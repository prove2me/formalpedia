-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0697
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:12:19.762632+00:00
-- url     : https://prove2.me/submissions/0b3d5643-287d-4c84-8c8a-5a108c2dd350

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 125179856 ≤ n < 125359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 125181106 1250 125179856 125179909
    0xf050307020a030b0a060b0306210f0607020a060b0301051608070302040e042102030708040e1308130e1806130f0b01060c03120203060f01140408030a05030612030702 73
    0x128114414854081d410208070400001006004601c1a12910032040c4c100b180d1a180e601c0d0b0501c1d0712080c1c503035580c0034a00701c000c100000712201242441d29404003c03103030f150b040300c0c483c5810700f4021201c001c00750308401d01207400d01503980035141a49000320001c10a5180410305908a084021a0340081000d03101c002580355006e9030445000c1c00c401d031210181441c091822003005400b1208a8096603000c6c0d041042003400041922030282d8440d500b542010f00f030190100c0c070800f0003020402100b801010343c90103c0c0c101c030010300c072a01c0c0c0c001c074107100c40e4144003895400502c061300580107546081c071640d50451000c02c2a5070482c145581500c810600b90402c00b06448a171180544501c4100300001180c0f0781120740c021490f807107901c58034500c140441d102d41c100c0c002111072030307002420b0020f03850880d132244102c003205086500c00c040c101500c2e5641541365030428041c0e000894000010310145190071110b00e0281c841c1c010041d8030f0400c0640c041030140e42280002d0345030b050b02d200e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 125182356 1250 125181106 125181113
    0x6050402040f06241b05030c070e011214010207060c03021306080106210e010c0f02070608150d030309050607020a0b010b18150c0d03051504051b0d090b040c060212160f 74
    0x1609120f1694a203030f140c107100d071700341811500c070340c04a51003039200c0c820203200044a52040c4003d604a50300201071000c04501520345c1203a1190062038410107540c20072262001510610a181e5083c11555005171134582034810034500940b103420030340510002e40010440b03ea0300c254652600006101c0f40e181240080c0000d4001d095640c28040710341d402c01000c58242d60307101c0b40343da0448506d6803c40d00129680d02c1d0503901d0100c155003038801c0d0402c50020414600b40080070f0707030394a0700ca403030001100a6140c90303081c281030003a01d0510058103e40003140c01e2086511080340074100300750b6098685040f402c08803010900440100e0300900b00d80091801003080e403030955030f0081484041d40c122110400e40200203103403c846004101e030080b08848440e0515126462260409800060910603840d0002d9096000032180000382500c83d05c003500022100b0b40114055407090703903103107060b60510b07001038142480381080205044040c420034125a0510301200d03031a0b60440c0100700600803909 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 125183606 1250 125182356 125182367
    0x30d0f0e0907081b0307120c0e0a0b03060f0603090601061b060507020106170a11061c020706050402011b050a030509060426010b0a05010c020f0402040f0306050402040f0624 76
    0x10001a400740c0c0460030403018941040341d15204150084c82c030800310b410500780c0002c501050301c8a1001500818225160031142c6e40250b2010207142018002520400002060282c01344c000305031000c8080103000382810214a88080500101c0306281035280c250011135803075105206500c1041800c1c0200030749014040394440d07201c0d4210307606122034a020f141c0607002e882b403485680390060350810000d080440120f03d4a070420b40c404440794407100ea5404100058005880182c0d0140101d00c4021103e45a0f200400388035120b00c00c045028a0036000140034101100461000341055051070f00015101041d05c000301c59240c240b01d504c0b034030128003045040c050754210304040010800000603001003540d0f8000c16000400080c420111110188031883d01179102d40790214000040050040c40c2241c011210607401600043c00c1507540c90001004441640c030a070384043c0d55200b80002d5080600408140510b40c2009214440c90041c0b01c2404042000f91a22484d88055412080c0d6100b05c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 125184856 1250 125183606 125183627
    0xa03031407111009060e09090a0605100b07111009030209010909030315081c050c03160206090414040b010801020702090a0b030a051b091006020604031d030d1d010e030d0f 75
    0xb408102c940c003c2c8540103003290070540100b5001c0340b901c80c240700852030041459440303100202c002d008030f490305607540809000041c010032014282c0a00100b5640c0005c8003604042d4042c1e491001d80520340b0050000c6c4004010a0004000f5128810300158840c514a581129170701280000e1420448c1400c50061220641d0010010032000b03000980070800540d0030822110030f02c1c801204a034030b580c1503e03284100100240c49810502900325000f844e542071150050010341450b142052003000a01125104000400016030620522042c00b28514089014003200c0000318030f0030815400290354404020300700c00b02152038040224072a2800d120b0055110740c040200c03030520050000104405035407600080c003840d11400080d0301040e084034042d0481d82e194014200316103c6480c01c8070070401d0b2080002c1c4d090040720114900351010448a40895100d94412481c40f085000342c292802e84100da29040140c2800548210f079404604100c1c5296030741000101c0301080d00d001d0325400d400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 125186106 1250 125184856 125184859
    0x9060403031110060b03072601091805010903051c0605300a0c05040f0501290c0d0905131401050609130221060d05070b0f0d0e07080106050a0303140711 67
    0xf0134400088142e07000000d035001c3e2a958444001e01d01e412040e2841c202e20b0034500704800000000104140100d41e40942a401c0c210b0040b00d00405a94840500b500c240300c400700e0002e0000590985881d490300b0035900c0c003608602d0b01340443c9260400042000d19511300d00da407a2004180c058080500d1000c5100351094401e0940d8407142c060708102004c11118401c00340158100f034641e4003082d0f014424641698540580b03580ca2134442181040040111240ca00c1a007008001c1400100400c001d42a80080555150259541804140b00a0008100c1600c601c64246001c912080004e01c82090566106441064490501c80c1c0010550b208010714055017a01c00501c2401ea044048140c200750308070400721480c1501d40a0030300181c600740e0300b80a00a42c000e4601808083c014000070000d0b46041182c2c281010342010301c0d6022222080100b9045a026070300c20050f0403800c0c06102c000303180c1258110105461514007500043ea48004018035580000318102000b0a204000b0301d521300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 125187356 1250 125186106 125186111
    0x3071a0a030e0f0f07140310020c03071505060109050a06120509031b030304060b0306100e0c0d060810110f18031c080a0b0d0f020409240c080c09060403031110 70
    0x504401d1503440e1070b0040300c4084a0b014640340403c1d02603413500306c5440e02030050010403c0181038140b00380250880f20034008140801c000660200e5025007038040c5c203a03059500040c05041981c00034280a0b01c0d644401d014121100e4100452038024240d80e0170b09440759004a0b440d9580100c8a040d44950848024901d8a0394604c440e0303d100000034501c40e6114000801005041d031003015620300080311011805280540f091143c400490300480d00003d806002c130781060390400984068a5203a001600154042c0d4034013140340186008004c020682010750500e052400c1210031510701c0303050903c2200c08480d02d00c804094400301309409084480c541e5400004418013030040000d02e0a0340c6040320181044444080d40ca88058000c4046074045128140307000c9560074400031f040c0002055070001101d003900d0b00c1401d90382c90542880d91464400003518a044034002e010483d01510110b80d00e64180301454154035140c0480d01626050b00380303000910040c404c92458841e00540d0100c6050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 125188606 1250 125187356 125187373
    0xc021002010b011215050105070f020409080720030616021e060613060f031103010b040507030e0f060114040926090405070309020d11010309021507020f03071a0a030e 73
    0x1036041d804142c507500309036560702c960420b00000c00c0039241c0b07000a40584100c4101d0400c41980075000500b03409100301c2e07801583c0b080341c0d00010300710f60b030a110554224100040001c10811351054003009038041d8044500422840341c00300e41d80306001021071148180801c17803825624000c01c01d5001c24440003201c000700246030100d46c0d842e540190b550030b0140c09040740849000100d4003850060b200c451510104262031911010b0324603c00010081d00365684102e0f915050f2180d01880f071082c4000d80b4041070720005290381600c0e1000032051808160002030050141000d81d0a4101341228225008180310b400348c100501c40c0f00071041810300a86602416040d00300c3d1090142c2200c0b101290100066514041c0a0302698030100300254080c100c180e000780000c4c000708499001c0351042c500001d070510690302054910260203042ca180880c007240d50411071400c2c4020580410b026000392084614150720490700c031031450318005089202141201c0158440c4c0d01002642410008480b0380c403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 125189856 1250 125188606 125188639
    0x80702041103091002030601120e0d0806010503040503030a020904110705070f08010207020f0f060c0a141513060905010204090c0503040c0504061206050603150c0c010e0102030903040501180b0f0c060105030105041a06010c02 98
    0x181072007010100330540180005082d507002d48207503449190403d0182d4590340e00c150400c4001d6010580140d4000d5030341e0072404a01001c0c45c050407440d80320328010043c0c2c80c01c2c58101039145119a0103a01c0d0740c1c3c0104500001600c4080036954281c90540b00c840d20803403110005007036402220500d6020317128400d03480081c001500314504403415010140c034039800b030050042184150440b1070b02140c003440681c3c1d20004440c1da020601040c09000010304140d02e4000400958801c90118800610b020003030105200f41d1100550060070125000c00071345243c448070400c40e002c14007001d003942d5070303a9002400c1601c050003c0100d6000c0e50405465a14040e61213540300d40188501d4046c9603c0d05028401411051003146d010340c001e5001107090070701e040c00459200798400b106800400010500081d4904181c0187c9030440041e070305141c96154411910b03161500580c484c0340709070b0501c0184000b0454900e0080351506c0710140000c00340e82c40c000162480c00c408003009400001412159045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 125191106 1250 125189856 125189863
    0x31312170c031c140f07020703150f0b040219080c0903070605030f060d0203100f0605030105040309060f0804110f040b10021b0a0509160207030c03080702041103091002030601120e 79
    0x4410b100b007083d80c11000c640c0c11010484510a14400c40b488010010030103d1400d41c10f03090f400000d03407045800b140c0d22691825040505100d19003101a150302118110110f41e001c2d080010300d041c1d4085085c28010b8038114801000407492509100100f00801c0f084120401110b1a008001e8102c0350201d64030140109103500c12507180c1546613440c2c0c0800d2481c0f500c1c0d00148100d5400400405140b126081203800415411482c2c4400650320000010661070a004032849140242c4580d0116454044007819001e084040711081008240410000a1005855400c83d503010f8404820107030b00c8601141c01042c4001c010780e40039411003070300d60172a540060740c50507000210814400c44011042800301004243c0100c2e07070710aa5010015080c2000095028820102413044600d129582e8643e1039860070139820980380c81c000016003d041d801c050107041c06058000403114a18504056095120301c0c2014448502d15000804141c69030302c181c43e031403c100720341e4a04204045520000783d54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 125192356 1250 125191106 125191117
    0x1205011206050108030a080109020a030603050a110a24050a03060302032b05040b092803060204090b0109050102100c120f1a030312040b040317190b03031312170c03 72
    0x44182c188000801d65510100a0b10118841c82d1580885079090191940181d0040300311001015030b0742d80008081041086450f0400313011b0030324422003120a405105602d41c264001d40041c03010020401c0094002c01707020080c64020f0300e040c9803501c002c0003084010300000da201941c07610401144400c1807006003204034454150381450f14400c1a09041070321180264402c06800304c0703040c000040582400810191801c10f070b607594107a001601d24800c2d103000201d810586070070b90b01290500c4034102a00c0b90b603c090400b42816003145207080300003543c480105400f0b55105448111001c81c1d5030007a164040c405028541c10b0154106002c0c070b1600403c02400b0742e104081700035240800c00c0c10003004075040101e02028907842e89e5100d072179002040001600407820010b00500d407013407068003000d080c3e001c0e103850748003169182e200010171700641300c4a000d4107109420400015140c4285103103080c0c2100c00b24140c0c7c078081d00e2581040010681000c1411b200c02c1e00000d00c000e08110040300501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 125193606 1250 125192356 125192363
    0xf0c0c0f080318031f0b1903150b041401181103012306091f02030d0903030b0316060f120b061201081908030705030606090a08060105010207080303101512050112 71
    0xf4118096020076503206100056035130000b02d80c01100c441d0b2000da8121803031942c80070b01154802c41020000854070500c5030310076038403019640c90009505080b0300503219030f80310880c1c0500504c42071041c4907407040c070706109107060499110b6442e5505107050b0080c1b1725017494044015180d41e92051301010a103401100d0615914125940c0e00e028504401590b00c40e58014101c07654101c280c11800d41c0c2418100010020f5100a000d00c28909050340600b10030b480c07190380c0204000401d041818501080d03c0441c2420030810b1405110107079001400c0070281d0b40b035280000d903641080006900500c03280d240650844c6001922a04100245140c0c81c100c41c481c2c4d00302c0e43d40003040c1e00188001c40c20600000d104070340c108003045402d4802c0c4007842d0001380003010b507440e0240b4040000d03000d8810b540484440d0b08850010401580c043c0300c1c1200400180028600c2c51078283d100d1070182045000e1518644a001454214241300c0d41c040c042d040340c81d1070108040c0d61a58000d0303d00111115007203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 125194856 1250 125193606 125193637
    0x8030a110f0405061303170702210d030f1103040605090f0a0309030312060506030a0e010b01110316030e0a060e0f06091f030e010f0603061404030f0c0c0f0803 70
    0x404004031a0400c441245054240c69414181014100216070748030075440d07583c04c600c549020001c20403900743c080c0c5151388000f007255039409a105102c0a4026060f0400001d81c0b14034040703c1902000c51841c1c1114054070b00044d1424406580000a00c10080481030600021082008000316039001034051481c040c111451380391420042a610038618074018005500004200b001074000c030420703d400c0c110b41c0400b088103501e400104185030400c440a1581ca0713255208005007420030320501587c01c6080c608018480101e1050951340d115480d03812070076004c0c0d04c100c8130034188110107041095400501a0040503034403000104454540003403280704002c1d96540c40036914006080320080d010141450f8040d9241840019001e040d04141000b07150304d5071030740d101c051000c3c4540c4c81c0358440c04900103159411030602c281280c4920100c0307040754041c07a09101c04a50030030800400b04c41c6a1034448075201c9186480030b40e01c10281e0010f12040b0160b440490b80d0000070015021502e10315890 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 125196106 1250 125194856 125194871
    0x6040f0606050a0503190507030c1106010605120c0c0f030c0f0c131d030f07060b0402030903030f04080c1504030e0a1401050915040803070b0a060303020c101b08030a 73
    0x410100d4409100c1c581c00310b0030800c549440b1a0040c0c01465002d000310400350308444440d016803040e1071003100e4410011b42d40c2c0081502035074225000300f0300c5c02400300003011300d90b040103005041d504ca03040010541000d10307800140014140022a58401c0e090429151034202100d0b005031b9940120700140880e014885d0740c40261240014420129640145a00c0040500120f00130003490815104c14850f04c0d40d00700b032901e00c04100010001000e0600c0010b50724622424404100c448000095104500410a05c590610000107403904050b07950011101c42e1944d151a0f6401e110b00d00c82807106000e01501c20f02040c10121090f8411800703610b40e60b041550300b4041240fa000140a01d081c2c1084166459050354400c102900b4072a0003c0e0600d000d4144000c00d149881d00131354040c03010703035000054035810030442146a40d00884800420300c0702c1c40c1580d8001c0e40741c10181c0081c9005265040079401050300c1905402d41321950904003801e24800c9060000155204850f040e80140c00c0458 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 125197356 1250 125196106 125196131
    0x1309060902131e021e0c0c0d030801090e07120605090313030f0209090c0102060414031b01020c0d020a030f08071e030e2401120204020705100f0b01030603050d0c0c080a05060604 78
    0x2117455a1405405400d03540401d400d0100765a0031016800c200b511171010345083d180c880c40400d001c080d000361522406585007256a8003544d124841c040b045404c200c13403c1040d81800f1003c0350b031850b4012004174299468080d01c030310314080c0140f03050303001c8441d0030004148003050881300f6040d8005c2d529199240c1d0f5800225541700c422044040c0140c0c402400100850341d0740c0c605a540108000c1501e107406a19445008000c43d48141c03150075960000300394842c0681044107950846150019140d250070a40703000d808a83c203220368000340060340b00000c191a01c24030840301004480c1c220a003034030088050080040044000c980710b02d02c150346100391003803040d0000c03503440c0a4074200190140c0c02c00e001d680300c9610030351080341c11540a008401c0050000d00080c40e42415160b000100e00b96211200c1041d2041080860305240c13501005202041000c01c010140f404d050400440e2410f0516062490189961080149003e044800000c01201150041c05001c04941c20701000001c0386 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 125198606 1250 125197356 125197361
    0x80c01090b190905030f010e150402030615030703150e01060f0b040303140702090f040512030c03060103021b030d02180a050102071701020c01050103080d05151309060902131e 77
    0x7921054203400d10054208202e2141d42c00308200c200d10340684031560307401c0400d00c0c114400811400c6139460380380301c030741000042203151070481142580440e81c2c00c10b500802e49034200a0a031441415200404042948080004e040203545c0000b01038004006015020006c00c901c7d01d1609081d42400000140b06c0b00841e04d42c4191850341000a02c0c0c14a0340d0713001c3e1202100030001c84007514091202c0f4000d60313104100a1310490500546800c94945807800608215400b13641c45400712040c0148420485130500360307a8070a0007800c005036200c1400c100703002d0214011b0f10100d103074800051400600703900c0b600075140407486510610442c500300030030080c0002d0180200b6005074406a01088551540078035180d01c09414400140303418003200c5c03403a00307603074098209460142000030200d490402611030254400000d602e41d0841040c0400050b100b030f045500e90b000d400d0345441c2c1c00e20500038154070101240d42d005002c90407440300c9480b450091304102e00d5201c01819081c03521400c8680c0360 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 125199856 1250 125198606 125198609
    0x71220010203040b07300f02010213140d06050103080d0e0109020d0b18030706060501120203060a0e071202131508130b1e04060911040c082d010609080c0109 69
    0x5030095820700f8144880301100b908905804d9403507000460f00301100b484084000604070403c51b07058495000b440402400380c08110001c0f074210380c4100614190040b04035904015104140ca85c82224443d13400016861303028084054280c43c5017030000810004004010310b200c44942005024403102d0305a403500300c0300b0311000a504044009030708000140200344030380d4011031381d0b00c1080a022120f605240356400800048620958544081c00340f0743e0089159949121400019465403900001003200001a4420000582c0400c4003080304903010f03070203002502d903052100710b407104004500c0348070201041c46220103800025510200c002c0c0b140d454544103040308640d05103022000d0341c500040010040c00100c401007840e10f0740114030025909240100d00a0001060043d02d90802d455207100c00e003030b5940315624151056a019420038100e581c00301c0100503a2850000e82007074040b0f401c203541882946110350702c00101c0e00d03e0300034040c0029660410308507115100500300545403400c06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 125201106 1250 125199856 125199859
    0x10c0203090307030803072a03030f1803030b040e0a0506040b010501030c020d0e1801060203070201080906160810030b0414010501080d0e040e1005010605090f04090f0b0414071220 79
    0xf010050000c14000c500440e00041140341007600d49484008041a04100d20482100240c0110281c0d0a05500d0b000304412001082c0042101d2075400c0f20082d408000003c0040a160f1070700b80301c0300701ea9207035417011540150395070a4a03040d076000c3c44c00640f1500116812180394804100102e071f2540709208405429969800800a0f80174115058074290040d015081d4050341d440071500e260b12444501c1030083c10300e030b0001c5881d0181071002410304000140750480c281e001c601040707602c900e81070810719115401e0501c00200e0300d0b030710349084440010b900050310349018041840308101c203050713441d07003241140d0008100b96602ca465283c0c48046203145000050002c2001000515051707225800e20082141220410003c04500d841516001d0703000c0c001241010501c00620f040007150b40620203000c41e81045a401c00e41d0307034510429040700015059200c401d00040c100803052580807141d4180008644030700d5501c201640c24003060039401c03a620b4540c98083c000814414803c0742c0311074070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 125202356 1250 125201106 125201113
    0x1060e150a03031d0a0b0301080c150901030b010309120c050f010216020108090109141b2b080f04030f030905010c02033004150f050406120b06090301050a0509010c02030903 76
    0x610f0b03c08075580c01060003850040c4014800c10003050b0341d84149500180b00340300343d0030703141e6142c03802040c14413558528580c003445807409135001000c0700904542e030000090a00080640300d00703004a00408100c4d0008080050340c080c41d04841b81c21080c410000c510400c00c0b54035081d0101c4040e400d130f0003407190411b502e41045550760010340c0030700c800b81c0e44000401e00024140d52107840e8110540a501c1c44d07515283c0000b9500701109403c02c5000001d039201b070fa0780e200074075142070000c002c0e41007003900303440005480c088000c1048500c01c211046459440003840e15551281004041c00c44840d40407000318202d000c00240c1035004600040015030010050095644c02115001c42105030071044226480c4002800c1d842c240303001d018001a004c040075a04040001c9075024044c51104601c04041c0304042c0010405154003000c1d0f0310203101c0060000c82c0310b010000126903035011b082c0c0f02c0c690550824040040702455984070600c14400580207011141c081841a622840b40a00a580541 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 125203606 1250 125202356 125202359
    0xb12061915030209090f040b0c070305091504050307080303011811070f0309050307060e09072a060204030c120203070504062d0b0a05040e0108011a01030c090504050901060e150a 78
    0x1014071410074001d642608025140950900014191450803508280806002001d020901480845440c0c1c000c040f0449107242c000c00e51406400740c081c107500b0902c02c40600c0d000e00100012041540c004001c05000c540c05951a144459104e4009018500400307019449041c0120410300601c510130214252292030510b141d1111420807444403025403c0c800650700000702a2801c201c16001044542d850034044881e8a042129891019000100b00320007034240303440001ea000e182004200e00c140080d07042101c0c0f8a0311001034003850344094920f0888100001e601061120b100700070394400c0341a1440d403a2524100004c4031214001c081c3c43c03000b007000c0c160f1906003103c000d00d860218401e03030707840c007a80e25206880d81d60f0213999000700041011400304404522129910f0243c42c80000a10200c1d05c2d15041c0c0e45290078029002d410151a2401c2c4400a03000c0c103665000761901600500480c94503202c10350207000180b24449100b81000000741041d006440160207850000f49105c8056 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 125204856 1250 125203606 125203619
    0x9062c10090f08100b1816032705190b01050d1403040801150f031101050f1225030908090f03100515090606070312051008070b120619 59
    0x100040140e000074040a54400710344050900400c0c401081d0401c0100404944040e400e0142c5003205000c50040c0018640c200099a0005801c0e601800140901c03c03011614030080b0301920030f10251a005440e441440340881170612002c1c41818045c030122401d205d60f07100419840b40107104050040d049542c014050f520302001d040300d0403802041d09030030200c001d1a0f124115841644500e140742e40d21070020b007000e20404003020050103d220360456552540d2192048180172403a20760400500143c401a04a07925040d15078520040307032100f00c1841e0003180c80203030100c1600c41e0100708030034031a4048140e00c01e0082c07101550f0310140480c149010031040c07120505180c400958580180702214a00b403125120740c3d07104462400e602d0400681201c18482031a40280240780610000c01c0b80d907004c0380c2c10182d00c852041c081030000580d80d843c000403081300b1086070003101c00e5016113040050007410910280101328061401c07440c0700c4d2180401c102c800c0b160300d08654580300e100c0e0f0040260 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 125206106 1250 125204856 125204869
    0xf06010807030b090903090a08060c09060d0e010c0f27031b030f0b0f010b0301120f1b03030201060f08010e0d030218090f070f050f0d050c07020307030309062c 70
    0x1001d181d08010030003292071400580100360440e00d00c1c0c0e8a900c0070622014514101c04000000c0c13880c40c0180045060141c1c8020721071168048240c01040005218044104c0640c0080140300c0c03502e008101076860a0002884120104518800644114940450942c8142940d03207211500c01c0d00c921220319550b01c40300d11180d074110b03554070501c2840000011546640c140c40d4411312401c18501c285c170b40504022100c40c41a0049241c5d60707000e2005000d01c1002d000c0f400030098118080c0180e814907803074560031001c1148107440c14406512400410140c0540000382903a00c01c0240e80c1405407210314190889068030041000c581c08000381c4141c1c103010360300500040a6451001c240b221151000c5201008180c4000004004040420401d01c2e440141c0c44a1103440e440c146140c0f80482c80200401d014401c00d11f20503591b0348012400029488003150021940075059441c00c6549080240c80714000b03204401c04104910107070320780c2004e000e9040d500481603030b00408102c0000400d1181 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 125207356 1250 125206106 125206111
    0x81012031202040812040609210b090f010c0c05150601020d050304030210021812060c0405130e0d08040c0b03010b040902030601051308210c06070804231b090f060108 73
    0x155650308003c0441c02c1c94003401105a030100d55850159500d1500200405030540d980c0202c440c5140158610040c1c0c0a101d462140c0c00d8008880003402e03241c0140341e038101503c44800c41010744c40c003105d0510a0341c200e000340341803074040c4042e1f542c05406403150701312a000845a513401130700065140041c1c14000c0001e5a04207019204403005400e0700100c0004a074030011140340c0c0c2e10000701c1c80084601d4103401c80c40655080d000580020f04141c84080d1180c010341c02041d118008501d00350582448079440001600a500101d6145001101e409400104181da003076400c00032032100401c03084080780840c0c1c101e6114040d110701d064034200d4000700071340000e0413070f41c10003408201c1c410680c007010310f00c0e202400b500d0001d0032424002c3c0595802d00c0074800000c2001c040c0c14003404904640228040d80e01c2015414200000d603107074500720051b00c0c83c00e07d11581d020804811620940400a60001c81c1042d1407142e60784001b07030b07504214101804558507524019140000390095114180103034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 125208606 1250 125207356 125207387
    0x180607030507051506100302090307091d030304080706061203020c01080402010e09240d0c0504020a14041509060c200604080a0305090301150303020d1416110108101203 74
    0x2401c207440d581da0181084040d125168541d00b038182444418501300751242904449821f0440c5400f14402c0401d40b10700491103054441da03130b102d89003102c1680140100ca1043d541d2030560f03a0f24603161030b10b0700e1103402c00c0406695080c588100880d020183c00d8101d80340b180c050b001081c0c002c41c13802c011105545c008104078104504d41703e85091588841524501400d041e8a684c1c221403401c0c00058400c20710040c143e44100130103480c3c80013256420418600707980381a2000341e5100c140c2e003403d8580c91300580d8079070401c09000400090141c5800041240c071032665440b40f65059498404a55840c0b2044001e0300301e180915180d40d861802c1942c25110440c0a0440340c20036598022560030700400c0541600420740000f0b030814a480c0c01e12070f0002c02080601c021008500310b4500a65504001500001b031105417100e003500c0e060305000341d44240d4190045592504c00a25102c40301d921301400c124041085100801d0398041c4802500041d038000c504c0008041d106500c003207414030043d40960 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 125209856 1250 125208606 125208617
    0x20f0310060e1302070609060911030105160e12030408030301080322050f040b0a0b1c0e06040c0303110106080d030b0108070806060a0507140106090903080f0f01121b03030306050406090218060703 86
    0x4038002850327030244484081c000e03401c0100c81110b8500745400d40e10003e20010310a010300040d40d06080e0403074040310f00c0d1441900d0001e00c5a4115182e01d1462080d500b25044a02c804400001c003903200000400369402c0c900090707c240401d0121003505441d16000303440d404030700d041c82c0040307900380355128104030300d00102000102c80c7d480800780e60b039500200c0281003144a00102c050790621600400201041307040061066107810340b145032502c05c0c10b010080811030301d46101a1201400d4000760094400241070754011043d0180190060020410700c902158400c40041d00c0d9a0281140620900700540354038941611032104a0360380c1e015040c21030780746040c018801c0d0404801d00c112000740400410020345003c0a007406800150000e1296698000c8001048a40705021012504540c04456940d44031440e514100802c0d44240d01103100d1604d05400000034117a06401480450f2003d40e410000c15465600500991248085001d040590490041d0550401100502c0482e003c0d2500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 125211106 1250 125209856 125209871
    0x6060301051c200a230118170d08012102120a080f0304060b060f0d051e070806040c020f0312060103060e16030b09060d020d02060c01020f0310060e13020706 69
    0x41208010400c000c2c0703107070040c1902c5003c882e403d00b450110003800241c5c0002e92021640c442d00650210740d4808070f8100a1104c003041901a00d41d82c030311000c1c00344140a0019452110741140d919900082c51000184024000117490380302c0c0d96240c114100d404101c003070207010503024080300d80b001c00700c80c0059200d1114840c001c907404038042c1030f4200300500000c1d640c0c1080c2c10501e042c0d643d04500a40315040421101100800c098201c031a100c031510004078980e500c1440c4002e080d6100c2494560b02d00803a010400e6150b4460002c86c1328001c103d80070056200750714003c0b42e41d40d070141c104070125030080215501d8200001070080d4000300502d0007060340354441d50020b40c2d000e4180d5414000000240041c0710003501401a103565030b6064860040601d0300c14000342c840d02c0300085c060b00480d00c5240d035000f50348500c0c048445c003068000c000d5540380018014058282e00458420244007120030020030003d1080000e600700f90002000ca5589016680d40c0304025404140300300c8984e80c0c0c2c0c010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 125212356 1250 125211106 125211113
    0x70509061602030c0402130905060105070b07050c0d020606210c030f0a03080121020904140102160c081219030902100302030609060d050706030c0903020916140306060301051c 77
    0x1088061a40000d03105407200910506141c0305801120900c01ca0040c024551010000310345101100c0303121402045903121403006858078800d9a0024203100f1501c01003022507504032005042e080d8059013120758201c1d803800204c0c0c41d208150f82844d4810aa180304200c4c0c2c81031060501040c501d6807083d200e10950b4180043d151900c0c644003000c003504501c51501c141500082d010340101604201080e105100c240c02a4540040820007485960b00502003014040c5e418008800d175807048000f19a00c045020301031503030b002c40920440301d064500d07034041803601d8042031603403500b100594260b0070701020013049103024490350740c00d0080640c0c4801d4100581d6601484000b5400103031401603403400d11400340420b013234005156600407a42e2310341820000e00d00061070002c80c1d44514000035441005401145d0a5402e5400030b584441c0700303024000014015000705004002640319820352400c46400c1110b1800202c1d206a405003040c0010841c0c1e0608848900c600b003680110110088099036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 125213606 1250 125212356 125212369
    0x207020f0d241103070c030f03050c121909140106170a02040902030f01050a050105010f020d080a020a09080f01061409090a0f021503090a030f1107050d1a0a020705011d1005070509 79
    0xc614600140032049100d041c5030b001134200b1448421480c05022510785002a00c0f01441845821031580300404000de005003602c19205070b0748000301d4004e0281d24461705084400000202c00c5030120351030b2030307800282c10032820034003c0d102d14090301804032004281c080000910a24105a8040c0901c1122042c035580c00c0c0700e094400d0342407403000103865040a00041c420003050080d1410f6501c004500d410254100800319444001100c0244e502d0446000881300d0201a41c040c5070144108544601c03c0101904040c0980f00a107203c41c03040706200e01000601282a07034155100c1c2c0202107003c02082009001210f000d00103403010a0200c0102c1210580b0792086640e1103203504264500000c05a200028000d4141c00f450f19400c4010034819540e1201d02c280f00f240c1c41003809401140410080040109000c01c071070a0000b02c40c5442613580c1c001e540181b40803551940307407081c202d00d00d030702480c0c803240400072902c0148610011181440000c0c00c0280c00101440004d0182081030707550031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 125214856 1250 125213606 125213611
    0x302030910020303040b0f07051b010b0406080105150105090a15020a080a080403020d03110d020d240905060a06050d020306030715020d02010f020406020303041b050d060207020f0d241103 82
    0x42d40155900e11302402e001d0394074070018054403940080b10050000c1c0305e5010f4103661045107007041d048420b030000010345004111003801d00d40c01c1414600300040c0c5000640c8494415010907482e844c040440d0401142c552080c60031184e8032540c040420b108405011340240440e0340c990048865884240d1603002040d04150040400140c0c0d41080004140c0d050220003150002420b042c0070240130340e01e01c0800e50140e045980561075003c9a0500c48904940107541072210b044843c2e40307545800225a40445880d000b049034860620011500c82c0c2041d00000003100c4140e40c1d020300307185822140c0000303548080c0540c0c0c3e15210f00320300820240a00a2100000b103c1600109110005594080c0c01d44519a40105441c0d01c10300003040710035008022a54040c2d130100c1d624212030503c00c00550490000d400076600040031601200820460ba0300400d5540c0c000c8469002e503c0220042248409000d00014502d80642d000d0189143c00107001108441800c030010440c8907a8251090041c0c008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 125216106 1250 125214856 125214889
    0x70f020d08071412031f0f080120090a030b0c0903011506020d0201182a06020105040606080a0203150c07050f0604030e09011202060d020c030c01060302030105010609061b03020309 79
    0x2e08002080118500300558401c0e0401501c01210091461201400002c041643e1205800c101080c000040220080900b440031343d07203001c41d92225180703802814505104c0d00780b240f54000320030049030008103480c0340400c001c01c0b844169080d5607580c0d0850b08058040c18049006004040543d40d080c05400e003860560404d04c20180e203000b200038035011000e490b2206692409a07a440a452010720074a01140c102c61019541c0c0700101d050150303011400e25001c610404175001003046036064010300e00907800380340305018450700c65922903207541140000960503405111061900c4090034145039000f078524154900f40389880d1103c0742807205c100c102007403a820641c200010960807640c244c1300c0b11000d40310496658104603c0c81c80d804d40d040c4000c0d204410110fa01e89000340300d40c044a40fa204840d00b0b80c0d03198a0078a583ea4040c01c014003049119500345400803d809208910b00000c2307035104d42e6911100501005003094044d5680019411404100f0000b00d02d41c0364201c1c4210038058 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 125217356 1250 125216106 125216123
    0xc0f060b04060906080601032603040f11012a03020304120b040204060f0302090a11090a0308070303050108030c03040308070807020301020a050310060c0b04060e1e010f05101a070f020d 81
    0xc203030040100701c5071250004099030749089400c1c0a01c1d600001c1c01410b681d07000d401c00300c805621680800000039400100b10104400200f0401008107022030700740c1e41c500c11009080382074098001519090781031901407107030a03090754140c0c0700310840341e610f000d41500a0060b40d142c0b540303c580000c0860712030401a18516030510038082103080c1407141c08024504441648900e5095900003541e809001e0440d9030740c503803100803010844441c00100d5150310802404c54140d1036991400404503040b03d1020740129261800024040c0000703c00c175a1111b20030380145280c1401d555503009250048041aa51214144102401614244020304240d1081d480e003c5d181d292039850320200100e0f60704100304224a1030521800508000a1503030400d51140002c9025502c0a12103032401500030510134142d06044152240000c040d40450040c90b600c0e0740500c000c0d83d030100c80c8100841140300e10000748105003403e40c0d04440d5503019240d914410310900d41d1180003034000950058958900760386545 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 125218606 1250 125217356 125217371
    0x41403070816030b0c0910090509090106030209010b0d02121f06090b0a030f18082d0304020603220c090515090a020c07030501050408090301060e040c03080a0c0f06 72
    0x5000c0101000424900009002481c0d0700d41c5a040b64600a20004041030b5403000811200c08036002696030014002d000103030503001c82e55000f80703940c100e480b5103800b991003030340466203a05043c015403003640c0e0003819041c030071b03460516800e801d80d1011800111003603080c0300381c44c41d00a4008016002d000d04070201040c004602c0d801c07584102c40f81d84440309111441c0002c02c9083e08c01030a4918a61507820001816081d60701d0381000380a0b101040391b10076450745018010840c42c0c2c2e022b400b00643cad4a41e0303610003290406031180b00390380b182d400300704021003800003c0051a0080045a2000c0e5075030702c1d0607a54085811040303a49040d240b08480603450301ca000d0040c414144140b90344a81e9148003415841c800102080710584068a110283d039000542404024810020ba00c02154000e00030009031074a42010302c181d0308450703003051195081c014000740c4521221816030240360031452a921a42c9503613140c880b564080740b104400d125107840c8010100d00e00e5000c9038819401808080b4000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 125219856 1250 125218606 125218609
    0x20f0303090303280c11010c14010c030603210c06050402210709050a0b01051c11040303080411060f0a030b04060506041205060105030f0a06020309120c0709061a03061c06020414 78
    0x1250744d04954010800c80d00140310104204420740f000403d400e080284c1030003c6801c28803144502556001c00d86d40c01c1ca43d0703240c880c59041e801041105e0140000e2410b0303c050308806000c0c40508035480300045c10740701303802d0080f0b505a4425038002d8030090860645401c50200034423558110152000b10b500804010000d100c0a400740b1903001101d41c00c100f107038040c5000081d0017805400c8040c82400e0035000b110200f81e006034001e0b0541200b07194030743d48483d0f0b0307450001e00340e000440d006c80c2c1c1050b0f8034487c00344a080c00c20a60b0b50710b00d140026641080c1071120120001c00a0303800d21a4099150a0001900e07142c460041c005421669905c1609150390704125107400780c1070344100e00030b910101c1082910240450161041c40d032020000d6503d88a03440311a15040d02c0c00c100d01001280014594400280001c0d20003c40709422414840b00f0742d039035541c00800d09159001030b4a0340d000c20024015107031840000548102c90b20546c1070101d070302d45580080346c100e500162460300030a04001540d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 125221106 1250 125219856 125219917
    0x807020d0305040b070e01171501200c06070c09050a0203070e0d0201080c0a0302090603011518030803041106071401150f0510050901020f0111030403080a021204020f0303090303 78
    0x800c045003400c2c403203420503a540602001d0018008410881c1041108072507a100c1c80c1d148240712640b4014003209d040c07980300c801846402c4c01c0c105000c113104028070100600b0f0119200d00c03509007180581031469000081c0626540030000880d01d50300d41c4040450f49031800c2c4100d501407008044010785030301d418840901125103103075295201c0d4183c1c803c0c000050fa44644065408800140c0c86611080c00c078105030040e0041c0c1a903181d05c0800032001150f01101c0081c5030b41d0804c000d40e58a900e00710090130b01049265240030250000a08000160103d070150303695404004014146502d080b596849403020071078140003000c0b20b0394691008100f1000180c050300c0141941104180750a0700e01400a40c0b0281c0c110300c02030508c070000ca10300145038000e00c141128610808000d0142d0025907440d1040390748122021408504d01d8000304100030460300c2038669407108524510840d48858003000002103240740c0d11903151000300a10b5055403020310181065100901105011034240c80d00c2095 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 125222356 1250 125221106 125221123
    0x212120106080604051b0f07020406030b07021c090519030b07030506040b0f0d060b1c060906110703050d0506040f1103010e09011104030b070903081c111305010503060f0405010303080702 82
    0x104500302401d000f140200f08603108000300c07406c08569a25205204041580d0040c084040c0d8001d180040000c1404009040248200c10720b0307090307807840c2056001a01c800b01e07041c0c1c2d845001500030007080c801e0341002014520340801034114518895500d64404505003c21141d41c40081d880b002441910f06050007404121074040711030303403080c916000c08070342e6800f1072210140c00e8940f185071804083c0c9880d1118000f5010301d90011240050071b09002d4050041c50030100d40c81c51a002703140c2c2d400c003250707400c0c2c1d4036413941540d84505c0c0910380d010010207001c001d49090742c4196503038a1000e020102d446994807911402500366100d625240000c40e44030b6004058a4580c1d0508140039407047c2c0001c01c49003a280e0140e00d0b115280c070381000c1110380c000180c0005255040004204201c003060394580100502010310610041002c02c40c5500c0320300454000b090361b4444410f062001d076000308095035000402134101002d40c0320000024094030400ea00035008144014140401b1941c140318044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 125223606 1250 125222356 125222359
    0x5070501020409051f0503190b060f150a0f02060c030601030c020705091e060f06190201090219050405070c05030d020c010209040f0209010801060507050a030c03051207030e3a02121201060806 84
    0x482c0f090343c0c8d608030201c0002c4400003460b012a240c002125580e40e0704031840d0301040500f400c0c021441903545e0b10702c5980201d603680c02054bc0f01130715090040c80050034521403280d0300c00290440c0c840b0700056000d0703c1d540b01004154014000b000c551342d102c415625200340c81d41c07020701c20303102c0ca030642c11050000050004e44c000c02595580c0c031520703100c02301140c11035004141048404030445030201d0042049140082d8819201440744000d41100c00340030013600e0084a0421240d00c41c00b03c107460410441c540205140c2084c0021018082c0c0d5902908503001c04030005441c00700b070940054222048003401c0940c0c01c0c6d010030b01107419603000c054140940b0060a0062501c0e4950315450f645642102000b404c221410341c002c81054440c1c0140e402601d00052240414140150b025001e010545054002071290140b0241010743c81d401c42291242220b2500410100340b0143c045151408030884081d0301c07030380b0541040030361000c00404541c11f0328505400c2d254102400204204406844603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 125224856 1250 125223606 125223613
    0x160b04080303070f1202040306061701200a0c0c0e0a0c080403020304150302070204020705100c050703080a05090c09010305030a020105071707030b0a1a07110307030c030305070501020409051f0503 86
    0x40c018000c0000c22642c010146003012000c14045401c00c1722603840900e410044140045000002c0054980180c026500c8401c6030545003810007203414200c0c0c2c0c3c1c80e5504134031000f0a4900c4603042113050002c01903403105203803c5201e409161200d1400b8035190b444541d4441d002d100308280b0383c42c20312444903007048620b0070309018207260301c0096a07030080d8015840d0038202d9845040803503010342e0448110903070161095450f2002410804c0d200c01c0c524041c050300c10309104100318440d1294044a0b00300f0380c19181c04445132150000340000f051700034103880362880f408120a1055450890b91402103101d40c00450b900d292401e002801e50310090514000e000f0b5015a290040075045141640007449280000d29400890002240c90059034402a8441a41d43d414813503890303107100901c00305010319282c040d0f1484640905035192810301c00501017400400c4d0030300c0001c3c42a401008040d0107680090700301a00c425901c001c035130050764401e0b000c89404080301b030907408140c800d100034003048014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 125226106 1250 125224856 125224859
    0x40605090c0918010f0e0309040e0c01050d0506040626150408073f18080304030b0c0f040e090606121b01030e0d0302130e010302150a20160b04 63
    0x200e619004083c001c903030b00e400d040340442901030003540501007a004500e0184000208600815200c0e88207454030f07030060b03041c808045030380c402c001082908a98180e4480345061120440400182809401d0301d0b032180e160b00300000c082041001030581801d43c03001c5444201007401c560703454600c030203810f00c8102c1c09407010040403d10100130f07107642d660480e600e43c2c00600104c014000004151910742400900104407555540c0302c008000c0c01c40308079485664042c0d5030035010220200140c441c0010380d80c0304200500025060041081d044036807000c6050800c00c450140302840c0e0815045440019010b500300480c80c4410010b103070b00000203440180c40002da46103456126030303120b2868650211500642d0179503910a5100205c0d244020341940c0d01b801c050b4400a010394410400564a00001c0c07001040e01801c1d84086412a1f6005129620701090351175481c09603001041c90300180194000b0010301810309941c80c040b180e020502403c503120b8118860400001e45401241d0b000304140700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 125227356 1250 125226106 125226109
    0x8010b0a030e0a02030d03061406090307061110020c03030402010306050111060a0e0c120705100906090e1b0a110607050705071802070507170c0607080d050c13060206040605090c 78
    0x12100401814507000ca100d00c02c18000c14901040303988003c1d094070540040c030700100e502d6801441655404d4000d884114252001c20540c0d0141c51101913068000c50410440203005808070f0100075040c0c816a4041d2fa00d500110301260401a014007040e00000100011036a05100e4503011308000d003007100c1c492120025903030b55030100510370607810ba507400304002c01c0300c001c20042c05803c0005100140c0c82451700205611b0b9907144c410580100c9281c0b900d4418640100d406000755180c503a16102164174194080c03018070300c0904000a5004400c621241030040c0000074402440e6076241c0154031082da0b01ca4034506040200346004001c02800a40000f031030102c0c00404840c40e01c204401c1108103011000c0092003a036200070304501c00e00d840041c03c0b0420b0903039080c04040b08020744103444064818003809200d06100245005000c1000b413002a8060b40f01d29040040321510310f05044950002101c1d8444540080e80540d00240c1040200000b5000b41640600c0c1d40018010b880031180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 125228606 1250 125227356 125227379
    0x21c1706151204150f020904060e04020105120709030602120907060908031209010f050f09070602160b1b031303020f0604140d0f0b0412020609010b130b01020f071e060801 75
    0x10580440180304201240a01810300100d13000140107007420401c1d0850421040000d520140203580121704200300041c1040303614928911854041e110309203441e0303006e403e245c9030800c0240184140301c20344c01d01101007062440600300702e0a4190008540d410501d1149180451031b42c000802c005401c00180501c0e803007c000d8076070649044843c0300c8941c42d01100784e405456000344c6010514502007c200340d10300346420300d5004070a0402950609900d07444c049896403e0030752015104e6441010030042407014000502000c514070507000703410050202c0641c2175601c0f15800d14250381001006000b5841c0c000c01b503c0203010210348082c5450700c0c003c2c0c07002001d1400d95542c0d2040507450150002d000e14a00b08603d070310f901c0510f16130a4601803400302001540401404014411080001d0201805105c0d011035004024440c40711150030f155400003508070030301200e0450054180781c2064402c100560b10181590303030f81005202183d242c06001458580c0c0c4441c3c1009180001004102d080c02c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 125229856 1250 125228606 125228617
    0x602250902090102100e03040e070806090105010c08280318020a050402071b0303080a0b0616080f040f0e0a0c02190605040812090a030806040608120a021c170615 71
    0xc980942c031000c05a005174240714500c215800f04501341900d0000038240800140306603401000c45041940b00c1e49401c03518041c04039422904003049000500c01c81d801130446035011842042c82d14909580291505c0b4079100c84901d142e00c051425400455054150041d00180c10084540441091351a00091034500261281c02d0041b54001401c0702400b10304400e0905001503060703805c0329255a03181c000c040074801c0702c9a120710340c07401c820140103180190442e0028480c6840701d6803906e600d500c1c4c50b0019407190800c0d46288108010020342c0c1c02020328001d00509a40003240750500d01700b1420f00c2505d0a080002d01150050840038400b8038240e0460705166400c6240000c540e6501d15103080c09100704025108406000c1040001d494000102d10b4130b440e120f40c1e90200746480c6d0100307000564042c2d005510490f04500f4401d44904901c00203000103c3c5544102c400700d110b201100304800134090b00850014030341000c0d072030401c1894000240c00100c2607a444041c00030002d405050303800b90 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 125231106 1250 125229856 125229869
    0x71403040b070207030203160504150302100f200105160302040f120303020d0e010203041103010515040e01090b010f030b0f0f04060209040e0d20030a0c0209100803070c060225 77
    0x4074030200310b00b140b08102c40c6000d140d01800f1200d204c4041c40421445c90b10511800348603c1c1000c801c000098007a400000460764094000070f2118841c3c0019909500356443c19006c010034068002002034621080b035004100e05000043c980c04c08512502c8003d035000c40c46418180104400c1244404c4c016001044179001c4071324484a24444c07500324040e204201d0f140300c1080c206401221101e4041d0300844c051846100c026501c2000c440516003a100e00f1105020240c02d03036070540303906080a40145000900e281c00004009035155071b5800b86002c281c010640d44100500188104001b01800c10342000142550040500c1d04a204c880a18801440200900c0d00800d5112180c1c039250420752407034203c0010381c0d08040b9802d07401052400c1100b41540940e100c0400014043c0e00807080b074001600696401c1191004d94003444503100000c0e0001448030882540000d2540c030a00141c480540f10f4100d1005a03460712000a00c0c200c0c1c2da0440540041c0b801d041384042c1c0840d0f92600d03007120348 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 125232356 1250 125231106 125231123
    0x14010e0c011407170901120606020606150d05010303020109021c0c050d020112050901020306240306120a050a15050915010315020f030a0605120703030806060f04081608010507140304 80
    0x106101007518500401c900240f421080742000368080f0004c6000d003035250710a0344c480c1e840181d0100000103441152240002582107800816840c0c200761140710260b030340c60141d461070f080f030301c002240448500368000d0f00140d5503000e101c801c41c5414001d141c0220031403a508000310103141c41b140103802d4188030b00c0c1d2140340511007040859000b480e03400d45186411408101c1c2d4030b40b51500d58040c5d4012240e040c07041800101c08184075940e040540c401403003021600d811581c0b03600501c17100c1c100c106a41d400034441c100150300011800c01c81c8824a61086503000c42d02c0111503005002d070b50019101e03540c030b0382280d0040540c1e102c0304181c3c0350450742c114220504c01001d0351600c4000f40f080b02d05000b64a500007080203409611500000c040740c4043c2da4021905000f00314040d2a1856404000c1c0041c801101040091070910050000440d1001686d45801e03541d5104910b0220440320703200c82031042c44d00c00c0040d0360b001c0c41550741c801030a06015007010401e06c0c60301024030000b00000c20540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 125233606 1250 125232356 125232377
    0x40b070614070c1209030503040b030a0e0a03030204050118060813080c010c09030c1401050a050901050d06031401050a0203090a060207050f06010b030103060b0f1e040f1814010e0c01 80
    0xd400c00640c000c072101e011a214141a03100800f0703240c0d040310543d802180c1951200a040c407075000403049a82040103541040d003480d0350801d255101400c01e600058449102c4800c00c0000c0c132900320540e205c1d440041e660b81c5004005002406050303945402150414420481160001c030165440f900000d019203941c07181c0c0c5401c1101d8000d100209113503619001440c12805e4128031410150381c02a0341d40c2c00c09564a00031036004201540303106002840a001ea20f80b86d07030088c2c02030195018141041400c002c2e401c901c4004903072540d4025601208140f07440c0d90125003c0c03082d02d401c21602d0105610f10f14003400400da94001c1210000e010070f500240720f8051100034050b040d0507a1640c4c080e2a495603480c11021a540c1082c082500d459151010902d510319080d41e00449240001d010014903503408030f43d800301141003013516030700140c4856814807000614840d40c401120100e0400654a00c2410000300400500304001000d0707240c1801d070300c80044000780c905120042440e05072903d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 125234856 1250 125233606 125233613
    0x2120307120f06060c020f040c1e0210110301090c03110915070803280e100c0516050f07050a050607060c020f060421021906020a210501060806090903040b07 69
    0x240514240700020a28200004c1440c5600040d00354680b402200d40c0001208124104001c45e0803036130049002c00e07039800c0000c0d0440107648000051038241d0060782c0710240d01504a074242c8002032060f03c400d9000200520251000344180d00e510b48041c902000351020401ca0040702d88200180c81c0c1c403400d8042c219a180700c034000c08460865910000c900d44a003040c90707800346a03030040990344000640d000e0024003c042ca034490800c40c0380658004100040c422400d4030000c1c44019450070030818104500c14401c401e842108480d0791040c401050f405044190a504107509a08000d2054001c60400c001541d5000180c0d41c031039800c424000307030b0042e24840c241e14100c114450308000340a01c0b020002031045141c04c0e0050035000b00c66010400c808424100d131a16181c0860314a2071045d03a00103404102e00c2e03070160100340c601d81000c400c0e40e03500d071310440e44001c25543d04000d06611880140b209540c8030035040c1e00400242c2d80c84541c5d0510924a540f41c2c00307030b03000342e181e803410219000d42030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 125236106 1250 125234856 125234861
    0x109050a0f060b030a06120c090b062712010b06030a0b0f0d0303020c010606030501050102030d0902031212160e06160609020d0803060a050306060d02240a0914010212030712 76
    0x14031041400030031803280d50f403500e24100d030000c85070410114a482d400141300070380f000c8002c0c1266804004013003154144041403001b401e40c07050641d00503d080c058901208500f15a00d584808c00304503000681403081d04025004c0e4800208540d03d906203656445542c0310003080d80d1f00105170340c0d8042501910705000c0391002c40e003d25507079400001c04035101c0c245038240e4020841c62800d00020f02800b0340b0f80d0801c1d82921003c0c480d56005910401000341d003e42c00b580200d041e64030080c1030341c9403000601e2003064540c009280702c2003526103601c244075a18291240c6d00d465440d40d030402140158041c1c0c00030761903015540c1601380c841da400c02034034200012903120a40481d03008200c0318040c86d09040c04002d5405c00c03543d040c01105800b10101d65854001001031040780000d0444982c40300303581c203010031180b01100c0c40d41c144005111050f03124190324040c0061400c15035030008c0382d80c07405400c00360040300c00748081e040d50051418030340c00480700000c40342e00002a0030114030340362924052000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 125237356 1250 125236106 125236121
    0x31b0d0c110402210106020c030c01090306020310030506010902090a050f060a23030403090e0f100510031d0c03061315050601180609061211090d03050c01090c18140109050a 76
    0x101e1000076a19004003c45044c50b13141640c00e29422107a18030901810325942c2c030001604580801d40d1198200006001500116809856506030048903507507592540d180604c00c0c1c00246100350046242400b90405420040090004581d6241200c0404c004240513200d000f80300420440e62410b880b40c1001c001c1340144901c5060036901e41c0c0ca1500b0300b03005040121038066680039440c03100214003080c02113000180501007001c21450110b142c04204654451200c610f013042c19140d5001321340c44c44200c13030100f0003051200044c01700c050341c181c20182025001021044045c0b4000b0108022a154403045d030725100341d070980010036850315001601c1070180c0070b1300580c2040b03580c00e0105030190300c0b140c003000b00c54454035444076242412059406846070710700a4030034103900744007111061410005542000740282801440c00a685078012b003540c0300c4003c2a6542403201c001000000d80d181601d116003996202c0400100145405e0944401d00612440c00850380300d002198950010b58040c20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 125238606 1250 125237356 125237377
    0x9010f030f1a04030519050316050a18120618030c061d0a12080c0901020a020d06060b040b1c05161d040e010b190302060708030c040b0c031b0d0c110402 67
    0x1401d0725161600402550100204618805840200c001094001d0041c2c5c2d01404c4440109c54000c4c92040342125aa003100c285003082100700240545241605400a005403240c0b41c03d250704801d0a00349103096030300c5501104c1400c0079a00405003c0303507000701070102c03003548400089410710810001d00380e40d0000d003407214010b0282c0360030303481008040f02c450364503d0b0342d07a1106005a500d602640d405d84c01540c00c0036001d41c00089500340185803023161712031600d20407000010803d0b103c07800354404e900107030031118050b040068410100d0b049510754029912030031406108524207030041c00303088855504030006001c0c0c0c4068000d21788500310b0341200d800c40d0141c4208091f1580a4803103004c0c04801c1c4543c2c0c0640d11020725a00042c0440e118542a2134010340464544159603485941d268001030000a0048042c4400304980703517110014180c58421000454894002c003500c450400080c4546041a512100d4005480c54000380400c00080e085140404000d4080011801034031440e18603e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 125239856 1250 125238606 125238653
    0xf0309070314031909081f02040e0717010801020403031d0d050d0c140a05150a02040f0303050405041a090601051b03030901320f070e1002060a0b09010f030f 69
    0x29203a20b03000001800d01090a098980c10801c3c0540c4282c0304c042541c0604e15107504404000e004803003030803600c500200300013800149840d94680000c0403002041c1c0d03c1d400001c1d03084014141028001c8170391030140070701c48001c600e094990759024040b200246c59050f0748041c240036001403551106100e11055030840190f402c035580c41200240744042c0c40400f1101810540c086c1088183c002644188442c1e002d001454041e0095140c0140f90800034040c2000760740130480400c0404030740210341c00640c0701c2d0304c0e0175454505044c108416908069001025240f1250703505110313549102255402000030b00385140d82d007080c00c030300c0341c410502202000a9440004280304c24401c0550240814600154906582c502c2e103469003404c0118101014000800e0600032840b5000301d90b2540c2e41104482c02c044200c0c2002001045502d14995400c9015803c01d80400940341d481c0c0c0601c0c01205021203039034100b503040c416800107001280c0009045034500590240c10400c200240c01c0d0941e5003020076 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 125241106 1250 125239856 125239883
    0xe0a020301060b0d06060908190c120f03080604020903070302060c0106050a0311120f0c011d04050a060603060b09091611120915091831021002070b0f03090703 70
    0x3412615444038140104c001d10f01100003031104d1082207580c0668003400060103d500750740703490401901e15280c05868110603441c1c00199225050103800059200c0ca598070b800036218200031b001c180c40281400e000d540104034130301456402146a01c20b1f43e0b41100e0050b1185001004d007401403150741c000c030703400c503060080110a02107a0381ca83c8004460448100043d2112132880540710b0003050500380f42c5a000603010829517005041e27450000f403032100d11081f11800c460014081c2c2c0c10540d000071025948500030b01000b541402500060803074004040c2c50b0200450104030002801018406900104100100c01038400d86c10030300f414024004a542c0d41c9103d48001000390b101c5105140701d0740200b00c1750b5990040203419a0780382c000c028001070701c0000d180010f1300c507118001c04c034040c1410041e242104a94181d00140f4564540320011003000314548144001d01613400001015580448010060b00850204981d0b40300000b14160741c480c0c544030080d070f2514102e5040240b1103601d403032a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 125242356 1250 125241106 125241119
    0xc0201180513140901060302060403080a050d050c0304050f0d020d031503021206070201060906120605070c0b13020f09010b030601050c0307050105071d090403020c0f0a05180106020d031803030e0a02030106 90
    0x91110034040e4101143c86480b0001618204c034901d2000a400c10303014002040419818070290400e04414100035141945014140c4d003150011203188048400100c20b220500400b0410060500210302c01802c009000702d402035902d19217169158200f603100e406211a001001c2410002035074058802191010b0040046031078140032280000150301e00079000550a01ea8000c1c1e0302107511403404030710360100c20780b620b8014003401840c610030301540d2480c80c40080e0141001030311a00c00e24080b00c42032142441000690887d21882c1c40c41800c07000f0040c8040740707458044070341040c402d0912542d40c600140d01541580240207000e46654a01010003440c1e80e000340c10300c440d01040000202034000c40d0010044c5406098601800603030000d64624041c3c00c007002c070030160240c018101a80640e40350b00188100b551200c0c2e0307891030179502d801003194640410202003141c402c0d060910000b950228800b1440c40c84c144007604043d140c18201740701c981c0502006809940140080c06010380302c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 125243606 1250 125242356 125242361
    0xa0306020c060f01031505091906020315031506120a150203010e06061207120e01182f090a1409160b04121712150a0e070c0201180513 59
    0x54035102a8080d4400140d42d481210f902d40b4140c903403224900c0000391002620100400c0c008204072518420143c801c001140407402c40303071100f40b05140143e580d20380b2014484182600e080b4880c000e5014182c41155480d04c1e24130035510210036600b0301021007159082c240350900406001d8030340c4414001002105299400850503140e10f40740701e6005803101401d00006201c0c150b403041c641f103031020210740203e1041d03410210b01048901c0c0821b810540c911072a007180c2e0b13044082d42c0800510f03c541d1040101c03090403414807552031940c00c820078401041e02801d0400900c00035214500001c0026242038043d4042040041c0d1054501d0151074110301550307442e55000d01450b4103550003800007070201c001404803829102140a20351800041d9074410929a407001441d00380b41314240102c0442c039502c0740d142e900c140400c80601c1072100d200400d024980000e50080340e1429400010882216040b8a010807029420b28002c2030f007100e401044a41e01e03006030405588090405c080c03020700003558 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 125244856 1250 125243606 125243617
    0x4051c0503040303060e0103150b12030c0a050d05090603010315090818010909020307051b03090319030801090204030809090402010201060807080a031805010804080a0c05060c0408100b0108060607110a030602 91
    0x2c0c3c804000094031001c86e5001154248801031201800361204102d150716034001c0084c2e03074805440d03122542e9039503007030790308603003190394590b51b0340e40400301039000e020040044508065042c14070b90318041546021038141c2c4014003026000c07500340d00310143c42035a103a111200407504540401d4841304821062070101c00c1280c1e8250006803524408900b0140602c05c03a4000d542d141c0303a07249010b60480141000000e0a004420b1034041840421803a85060140301300501d40b03000454102926890042c10380d01c03040c1c001c010710a01c14007041c40028452000c980c440034007202c0b17001881d078513480101e0140600ba00400000e0060403000a242440011596400c5200703803500b104039054505481c40441081c460700b0300140c040404103020400c0d000c01029940b58900d4080038144540d20b455280a000703403400841944006000c000350b2106004c0100b4100703554200380b2038881442c000034128040a071034181b0801d0300241443c1000580c0c0302c3c480c101c9001070300b4000d4440d40c0303003030a03030094000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 125246106 1250 125244856 125244863
    0x2040207080408010e063606010602010209210601050d020418030503060411090907350103120206040209060402030a02070f0b070e030a0f0303110906160302100c120504051c050304 79
    0x1c0071701a50f4161000700b0710b58420001c805014102c60043c0040901403200c1e5402c003850500d108030103000e507040a000440c041c160540016903510301e00310601400840711843c2c11a001c3c0020074100b0f45100100701141190000c450f414884101400000c00900e141071888041508081d0072400300360b040b10156100750710440e000c110645811310b03e20014482d107040d50754030240050010314028007480e0190b10305010205d4848902000d102422002011490718915481c038030401001002070243da100e444040510103045a801c00fa404a24907500c09460188074a80100c001604035025505850b06250425072619020800742024460440165603000c0003928030703a0f1452103401c0c002020805954002d034003150f100d40545007280104100c02141c03030100c004001071400d40e95008003421120281441003040e6002c0c2d480c0c06803a18039440740c4454400d085c0b514001c005900300c40101503072124420045096900c1d8508581000041d21342844805901c0e100074003819403041c0650f104611 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 125247356 1250 125246106 125246111
    0x70e150d0b010608060d0b01050603091c090305120c0d0f02100606030515040b09150f12060601020601080d020a0311031207080405070504060b0706020d1b0201090506060603060312070804030204020708040801 91
    0x1d848090201c840b0b00084082c018031f2100004005a0800034000e503482400c20043d6020308000f6803e04011658003d0301c00c000601c080b00c1031040c01820b00802c0c4100f100b800540346801a120f403085c0d100d501d0b0080030b605200c5d161501d65241402401a030003001c5155208001c44c80d21010f0260003000150395115210070300c0d025001813420711b8400d0140c410002840c400c07596a492070740f403c1034100310240da0b070090044146a201d40d19044072101603500b4190140c2020318116000918107074059004030b200e0341c40501682030303068020925a00c0c40c8d0301840c2401000e10b81d07440312440d620400c1241c82c0b10020442c2000105a0f1000d0100d0180f845075095a9189a03a0300401060ba8190300507010440c4003000700b240011050b50080462820007440412401a10002c1d10024040500c4138405070351540c26002c10040180b020540c884001c582d07c2d4114105803001c80c1c0d688580580c032000102c0d0006112060080c414203940046034028000c3d550342140d45880d42e056001845410704560 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 125248606 1250 125247356 125247361
    0x5040b2412090109021807030902030d090501030c0e100f05120a020424050406081e0702010f0c03091208040503040b07030507032a020609060d05040501060602070501080108070e150d0b010608 84
    0x4806005100c1314a4001305807a8003000b040da100f0040d448080c102c0014181c1c2c0318802d00060b1000e200385c01140c503032920f40301e4000d45440005800d643d01e62201c402002083e81d01c0c01560742d07603161000d8104100d45400c1c44050398200d4255050311034405060b0104800108125803500c0c1d540003481030342c00400000280c0868261010080d80c40c10641e000800c400384004d000c070320f100e9080030390f0004003010101648490b48014a1521105a41d10301c0180d456004221080c2c03001d008808500d031403450204440d660a0700c41840d8901c40c5401402004110000300b4103001c420403e45010f4404803881c5540c5080501e03014002d980500421030120350f40380164450202c1208103861405040742e0140071602965080103500d50003107409640c082c2c4140b00511441c0002e1094030301c9140301b100005501410200044d14000b04c6078009410000d82030b0041c03180740000b0075030342c0480d071415181c440b0680300c0112000a0100c0840044d030000c1e90a101d07002409a04418a412a101501c8440158 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 125249856 1250 125248606 125248621
    0xa0b04020a0e190507030b0d03020d081308070b070216080c090106080702100c1101021c060b0903120c071d150102060108150415060b04090b0d020a05040b2412 70
    0x1050880d4080c910711441d100c808003d42081e003103190311a50520300094540c681c200042c0b40e0f050401030079801030744105c20120400d038008002c250001000e40d40300096070280e5640003006d1182110050048400d4400f1400890082151031420001b010b1004501900e80440c203035030305449898148500c180c2030000400c54081d04200d4021005076000d000441400c031105030291110034402c4041040c0e441030b5602c071800030303c0a02040640001c0d01d1450040404409040d40c002d904110a0807008024000c19035500180d20b40e0441560302c951a1180f41a402490601405500c0398116003080c0002e40b03401900319100c24450100488000701400d05c0d0001244c1e01c143c00d00a0342443c1d0f020300c00e100200e280c000e440e2607101d84580180f40800d14104255829200c080e130041c0c8000802081c1848005064000c1802e401419101d8080504554001401c9400644108c60046940311b9000d0041d4070b0300c010917184606d28100c043c4600c0c40c074958101c025800b8118080301c04c0c0d107500c0454001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 125251106 1250 125249856 125249879
    0x4020d0b15070b1e0121080a05070c0f0b032806060f110f070b1308010f02070b09010203071d061b1c02030f0406030509100e0a0309050933030a0b04020a 67
    0xd00d4a4035044c00c101e13801c14a000030001c44280c0c030000c0c0c44244400d003d0010704440d000789003400c913a03558181c0350120b074504403448810340d0b00400030701145900103100592442d026698818840200a4402e40c04071400d801420501000c03118200d0900b00c2c0810410b030440c5d0b030284039122607680d4010540000c071a0b291198070303044041c1c00903040340508000700f0981130007804c3c00109080749045050f640303c0d1f0040c219911100002e48198000c605c44080c046401034041e40300030504000e62440c41d0420000300f01c00710400781d90f40351200003580e5020030345540c6c040c0da10710030403001046600000034500070b503030b10004001c500d41030b038000a545003d244040143c0d00e9041803003001d0f40c1400c2c06e2131030a81c00f802004020b17140d144523900301c240e032600c42c1d07010398250042c80340090000c0d00d031282402004403116420041c01a58100248000c3c40d8000d4030112104401380c8100a40f040c05500181400008184a6515110388440001448594804180102d02c2141e1075030740542e6500442c1d8a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 125252356 1250 125251106 125251141
    0x9010b0901140d031125030b16020c010f0306080d03090b06010e0d0605041a04120e0f060706090204020f07050c041a060a080405030d0203150f030c060904020d0b15070b 74
    0x822080560b24180040e002c0c0140c5c1844100c090143c03940819a440b10000d02c03444001e1004184200320020403d0221084040e0b0b0055a01e08401c03e100b1048400a540d40c0b84429095040100c021140843c86119520160252428000391002d040022100a0280c8505c0d1720030389072111100049041c40d03003c0d80083c0c403914006400540d0309032040c1c882a00404004009850480c05400c40903001384100c110184a00c1c454110a2201203038500014007003000130341d2050040d5008420740d61940e07035042c1690002a840000410782c40319510104019001d0244059414000071a6078010064003041e081802c103800e95040040380c48070101c40c0003940d041001980c028208010405d0741611609103140e20602500c03c42c0e103031004158001c1c00b20b9104547c0c404185450024040481c070b0200050001d00404500528071803400200080a40c410781d200944940da002940d541100302a0304950101000100603801c4400c2aa00e2622280c3c032118044940d4050b000014150020000054a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 125253606 1250 125252356 125252359
    0x1c1805040c020a0f0f080301030302100b01030504020604030f0302120f042409051314070302070b09120d180602040b04060909090804051203090907091412060606030414030309010b090114 82
    0x240b00d075a04e881e8850b03840c0b07100503602c100d1100360700008a200440114021481fa900800601c41041c010b4411160b02c0128113040504060520000d6076032001914103894004003107101c0f101d0546410792400c1c68100b5024075a4801140c031880001c500d4000c0d100711140a108851280c034092008100c1204407030810b008240800c03018400d0382040f1100d49003810500d0310005006421551006141204071501000260000384030b000b0011507220403038100d0440c0700240b032140485280750985016036000705404c81e69400414204e01d246081200c4500d0300300b103086507034503200d29481030355600500405d80450304201c400920501c00380300c2c8914890700305004500342401c180800802140015140041d44014800313106259a5082c0081c0611110f840300c110703007803525034403000010b220804a48280300344a50080038a80100703c05902c0502103440d81c3d902e80d258503001019144142c44500b1911020081018944056100f184440c3c0201d8101209aa80d5510000074503540d56809 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 125254856 1250 125253606 125253613
    0x612060f0b0d02090612010306021306081e0601170109090b160f0f09050612060f03030a0203190203041503020a0305240118050411030a0b0609010215091c1805040c02 73
    0x40c44102d5007036010f0040345074000c0c00d00380341400003801800d10b48020380044d20083e90020f246407044440c5000d42c401018581040070552601441c4102001c00041c1c8600c0001000030000e43c980c2e104180341c3c0a0260f01d2441c40c2c8003942c5400d00364005055800044401e00c0c40744000c10000d40d40c0541403045034180d40c0d143e0901c01103c51048803810f01001d140824004c016101180700d940b0140074203101c3c000b0300309440036850040c082048a40c050b0058034041c0d04100220360401e9070100898030400d643c5899800041f00c0c01d80201d14510841d40081442c008102074600215850780041170900300550f010700003030310b4200341000c0d00040700c2d030710344507802c1000700540180d401082d02c0c1042e65262102840786a41e80c40219055454a540c10b14030070b040041003220b0802d01c2d00c40d00640b0103050300c07124240055107002039954202440110503c4000b0780009100407000c0180401046502a0702c0340c01480100c80544601031000b403039064012142c0b008174143c20148101d815820781e59009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 125256106 1250 125254856 125254867
    0x506130b160201021303081903050c0d0b030f0114040c060206010b030703050a060801110406170915191b200d030905070305032a1603110d0506010612060f0b 69
    0x30030006403040c20010055540174401c00e5100000b071013a5a0046000703a90043d903031a50404500c10008030400c2071000d040c1350a0600c03c030406032178184c2d48152040000001c3c80100000081d1901d841c00d1440700c029070803d150780005d0201c942009000c1c9108000c03660005850b04002e03030b1501824050320903414410310014035203074803035000782c1d81003a210500050015202e0800c2c1e03094078140c2003810714689002404001090b0b204210590303460040b1003800c0030b0f0402020070790b00c942690b0061034032480b100c0c3c007041c880210780354600c0c03451801910030002d000042c03c100500d50f600350f40810102d240c500701c1d104000080c240c1009042882400342c610250204d00990040c404580251000e1044c260040b0000d0800c00c01041100c0804200e01c154041d1002e110030300704413041601d03045070045004e081091020450b2041039030750181043c03001910210101c5e54035101550301030810310907200000340d1103400001034800d80e54111414000350f40c581d03080c40c07114000342c860440c900d0410081c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 125257356 1250 125256106 125256121
    0xc090b06030c0d092307080106120201080727090c031503031809050405060a1803080103081b190605060303120402090a09150204050103060e060112050406020915070506130b 76
    0x8003c0070700e042d8400036103048240c85402c0002c10780c11030002d80d08081c0a50085202007007100e04001c115550007840854100444882041d40034034000f4140400e010101e03181e980034901c030000c0280754900241d01e400800e4502c02c04a03969110780c0d650107107859003d411552083c02500013405102c00f040f0076603032555904a405140b0000445404040f0728000301c0d4610742809550f0040b4003800051000781008600d4030121034900a6280c42c2d0b50820803410700203600310070700f00e044941101c0704580b251091054400905000820303480340d40600b41e41a034000700286002d0600900414041209648600605960380324012140900d1025040050018030305080c0080d80419047c0c00031030380141940d80c24502032038000950740e6158002c40d041c002c959040c85440004e141c0425003400d24184600080c15880400b06100c071826101e00001c0c0034840355804440d44510090700c5624413807542164840c83d43c200510840c1e20703005d5040802d114900b034070424615244c01400c000c0490711501c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 125258606 1250 125257356 125257381
    0xa05030f18011a030f030a0c03050a0504050a080616050c0714120a03080103050f0a0c06080612030c070302040e0d0206061e03010507080402030d170a0207020a0906030f0c090b0603 79
    0x420360710394000e00c0c00d08050708603000c0c0151140c103081050710030940c191010400d410302480101c81c50050f070003445005100359010380703100101601801c0a0b49d842c145110300b1603c40c42940c0086800011500000518403000192075100c0c601d060207804190713800800898147c41148210401c50b444080280702818840d40c00c0d2080c2a0020302c25815800c209842c0d50505100c050280c0100c0d60311001001408030611a0040e240c001034058409903585646004d082c3c0402c1c0540010048118001181902d400004640070803801084948132405241015926802400304a0196040103000d0b0b1070301c4400101590070040342e4014014558a03081844050034061803030400c0507180c074856030f641d034500380314003802441142c1c2d801d1618a054014140761000300d40e41d100420580c0c9880f00d905200a44005400c820341e48005642d51034a8000194070001940011a59514115001003080000e644024001c0c0c8508214000207607515203142c11210b84071110b60b044941040052042c1c0e1905 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 125259856 1250 125258606 125258611
    0x103060b04091e05043c17090405040c140301142a0c06010e150108010513061d060406080a050604080d0204030b1305010605040e03070b150d06140c0a05030f 69
    0x10304901103ea0321400050f1a01918241c0311a000b1001c1d0b01003000c691000149550324030343d0a034a070700491200c00c2900f10407110010b06442148000b100921b1022400c481d1a554010000e002c1c505290514000c0010f59200d17020031000107001521860030306014051186007450034140c0c00c0e59481190003200b041c288400e03c421071601070401040c041c007001425003460010002c00b0290305080c0c0249407404d0180c51b01041c840c2d00c80d0100031503030b4412407a505554040d244c0340c1c030003c540384080d4054803080d08662a008030300340b610592600c04241c00341c42200101da040c071005680c0d403000c903151103107154050030b2504443d001401041801004001d02c858141d00145025941e84802184a209444101e207002e0507035524824448240101405840129002c110100da602c20300d581d641300d184001031a9030b40c2c02000818058031000c01100103c0f0141045105500b00c0c504903008041812107809010000d40110b40b1900440d030a0314503d80700d44d19000e1840e2168030041c41d024400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 125261106 1250 125259856 125259881
    0xd020106141815030a080d060f06090b0304060e030d0204060e030c10051605070f090b0406050913021e04060303050a020105010b090d030509031024050f18040303060e040305180103060b0409 83
    0x2502d03a00750000c2e409100500b002d0fa5906400600d0f1409c204008000c4111540014200107107501c043c40040c0c0c20104490300940e0040002a9404101e13007010b013140104405404014804140001c4403034000d1030888850710304400740d50703581d5080c008000c102000882c080d40007940611a41740118074000001610380d01030030071184010ba5035102c0044846058104611450b2905460603190501c1c0c0910070190038100c1c1c0c20412440c069409443c0d8400210001c0d2040001a07101100c014004400d040d005034054002d0004a4030ad0801909681c0b00520041c015032803c0c1c000a55045050252101d41d50f004108600403501901c049a46803c41c002d202c0e414051045800410000c5100c1c80302e051ba050303d000d00c480d10700b00141c83d405410580c00603000381902160b411096130307410b110f961001103140845006445505040b00203000701d4102c0d0f074010040344284018190040054040000382e01c0502c041302150302c00460075035840c1e2140e0701e88443c050005200801140d003140400f1141c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 125262356 1250 125261106 125261113
    0x50315250504050316230625081201150806030c090603012405010207050f03060103061806020d09151a040234050105090303010608040816050d02010614181503 70
    0x44800010341402d4a0022046145405090800c15410401c644131801c03001342442100c121b0070000450210b01c501940c890344508141440c0c0c2c20801400d0040c4a809d801c549842d440c0c900b000d0805410707142c00c3c0210f41d141805415454030562190031228803e82000d409844010841c0c410700c0310442000c0d000d6580b554a500201420740400b000f08a4800f00d01711400e018280f501e40007900700340d0540c00107130090441020045003510000382d010304407980140c0c00501000d00805440100d5400300c00106541d0001940d0302d120a01034102c0000ca80c010352005260307004040c3c0040440c1e000780224400041d41c2da06011551400307a01030800e203844c04104403803e42c000280e2400c15102a16404a81100c0741c40c0e010500400344074a582c0302d0840c1006520350350500c1809428184001c1c0300510300100001c1c0c1119140341480c40000071540401218410205a00041d0280c0710502901440e048403811a481910380002010f0b0b2101070329580d89915190160b01c50a4070f80d0003110b5035098031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 125263606 1250 125262356 125262359
    0x206100326070f200d05030417010209190e0a09030c0201080702070f08030d0f0e1911060d02030f06010912060f060e0403020307050106061e08090c0402030c04050315250504 76
    0x152820b5048104901c5110080810b100c1c80e0842d8400c01c5044e48030074001c0e0048400803000440c00012101654940001c49000c00d131100700c41d0740a44161240d468202070b0280c5051b620002402c80c0000b41c03180b0f0381541c180c0d681c0740f1480e101100c49151000d40010301400c4881d01650003510042e07002109441540c1985171106100c0e480d4a41c15440801c0e01c1c0d00000c0e4014a0702110b00c035084610601a601b84407404110394141e80e40c0288200d14480c0e030400c6c0694004205041c010100003e2001e4040c0c0c1d1079980c1a00c500000b500221600003844410070300081c0a503201e030501d23506468200340e403091071540c0d03601c40c24001c10903c112801c6003503495101046d4800d41031086072003540310740d0003565225081e141c400d00f56907103603120f6010322000c06c480303a070101204620f5404014081c0b03840e81c40e0703598009100c0c0c42e2004108215810504c00014412161401e400900c00e07908268101c0d800d02030307510300f24030550700c04490b042c0c5c00305110340c0d0484015039201d000102c9040710f0703d046c50409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 125264856 1250 125263606 125263613
    0x315030b10150e120102090d1b0f090c032a05090d0b0c070519080417150a0204150c0206090409080c0607050d060e0f0c1c1407020610032607 62
    0x3210039160001244001d83c00c03108603d06034840d5006580610000c1d03090280c20380104021030180c034002413110550405c076141041120030100011306103103078a03051055643c20201e000384145619400080d007010f8000f9040031040342c0c003042c003034a0500714850002c40c888080710250041d0a150fa4450380a20505e804120600d004074050341100e2019585c0e8180c41c941703140360540040b0300d56030030711040c0c0c40003021410500a45044503a200d182007401203a246c0303414181034515540081c5000c100701800000c00d682d034068000da4407601c48070040154004820768400c80c104000030b6220030104955000c44c20542c01c0b8030400761040c09600d0600c1e0b00442d80e1414080300b252000009100407900f0803444030f080c041c000040c03a01804859140c20030651011000c00c0007400580b0004c0c0001e041441594484060180c825203c04100a54814031110409a80e01a00d10100500c03841e0045051820b50410180480e075101030440b1200506056110105210704181d004000d010701c08180172 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 125266106 1250 125264856 125264879
    0x402070c061106010e0a02090a120318090e0a110301060b030a05100b040533040803070b160c0b07030f11030906091c03200a05030f01060315030b10 65
    0x14144111500890380d070800300010a51010301c0c140301c1e0154000001000180d007080300c00350700031400c9000503945404a001252041809610503440c0350030141400042c990301032481288008444d9046000075559400d0340d0039034408002004083c0c0180304030f00002840400080b42585010300003040450703590303041d40c089810031944011174036295010003640c5244c000742030028004000e02e480c01d06c3d003044007041480c2901185035a100403441121401d03512480980b149000d0743c4820941c1e42d548800c2c0c07054480c2c001140844105c1100b80c00728104051070300d51480503040d03940d54280403c0564884145083c4090040030906030345640481606405020720f1212803809020030382e51741080d80d0a60301d84a801051030b6403e8000f070202070201281105035004041441c50f0208041c805d5100192021040204030011000c0010b08105603c1e04400550f11a030701c05844803100c0d03a618201038040d100e80e22640d40d40c94a100e80140005002000b010381c004258080c102c0788540c6500703540c2903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 125267356 1250 125266106 125266117
    0x6030f0106180c0c1104022b09021806030c090703020c03031611010c120b0103140a050f09030336070816091503060e1009030905010f02240702010b0402 67
    0x20b581c50802e08040315050078020300b1102621403802105000d41070b11140804541981362910035500001c0c44641b0300c2c2404215001544120300900000d1000140031008001c1034000702d0040040c2c0f840400014007054181d0f02c185405000303482c91022004c100410500e00900c2c46041c90360038410300039001010000345114070342250800b540703809032400c06050b036030342030b01d65034001c0e03040c10b165683c0303182c0c000d10740348200903a00c1022558150300401a03000d440d1191460b408101428200440c0300380c5a00b250b4012040700d94402d007141c4500c450a900e0f4030086134029505810220030300f00710340030b00025080e10015400ca00c2c1c1440402c071156414890107501c130074202d40c4040d0b000500c08203d506070324010122001d0801c82e646140480302418126448042c050036510700d010049200144011140020120000c211101c40303841e002d00703203c5d0140104d41c0040d00044600c00e00038000076103d40ca09504145c422461025040b440b03102da50014010340c119500c0e102c020385d25880750f001400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 125268606 1250 125267356 125267369
    0x2070203071d01091b0e1504030f23031602010507060b18041203060812030907170a0b060f01080a0b0604080a030801050f060a0c0305071a0115080f160806030f0106 72
    0x440652409107003005a444c48042d1001900f0013802e480c843e142c0194130300303018034829108011051000801d14445015980c0090304ae0140d80d0189002c00c40c1703001d0040c24040302080825940b022a55265649006001500c410341008100d50009507002c0c1c0c029150f50751182c0c001142182c450340c04035062a140501840c41d40c12030b40144002c03c200310000e1600305145140070410540360225495450b80140c41c1c8042804000010904042041c00800041c0140085441003111502c05103982d614001009440380082000403030151b20f00b0822880034124142d40382403003522030000250041007c0004258051410400003803407002c2440f0309490341c2c2c06030721070002d60361600041c00003200a00100f18407038901086030002080d00b0101040c5515010b16089444420a241104088065200c140103901d90000006007080c03244c40ca103082034080307585041e681d0300e481c6404404610141c8140c091200e501e0038420700f041c4900c412540c0980c0c010203e80440712821106400c5a4858000d031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 125269856 1250 125268606 125268659
    0x901030b0405030712030e1b0a0618080109050307050c0105031915170a050601080a0308010315060302150405100908100b03100603030f02070806040302060a020318060a0606110613060207020307 85
    0xd414058223200c207d032010100c8040729180c0b40b07241e0010f0340e104124000c0700300740300030303a802e000341c0d000b101c1d0130348000c2c2c10010020070500080d418520b503681c01010044500303108800440c401035101708280ca00900104441c00380c210800c040701c1002c1c20900300c0c009000300310b070300300058180c000603080c451180c4641d0280a40c1d421758107055080c808140c00c001c215601440c1c140c000251b010341d246044903041403d4901195140d5103a030042c000643c0042c1d0b118070b00034812082160300c030000f0011900300701c80d812500b85c00d840f002e4900c103183e0700c40c618160708250901003b507a60307508110301000004003651004015904294215503007504141c0c002041501900d4007c1d804021a4028001c000010301151030a070780d0003951840002c1004cd169600440410a03440b140c40811120440070307404da442614000c05100c2c002c044501c54100080c1c020f0780008111003010410134000c101c046142d8441502ca0785802c0040d60200108a03018440c858001a02040e0300004e03c44422401c1c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 125271106 1250 125269856 125269871
    0x60403050c0f010203041a060d080406050d0f05090a02040506010c0b0108010c02120c030301050d0c0e070e10110309090c070b0a06030210030b0f0d0320031e0301050901030b040503071203 82
    0x200d03260101a40540820f81e10410900001c81c0d002a1101240103205000b11a1a83d55401241c8170101c2c5880c01419143d0106d80402c80701c2c1c003c8090300208044c2c0404001c070740414440001175400603100c82420b60040d05488000d410644c00c00da81c0841c0604200c9481515541c2c1d106181708264440c8a41e6551805402a4150b0600c80c001d030384420b64690138100800e00c2d040c10384910041c0f003958454040c49211400304102a4445802420300718810001d0345005040078160000d03441860b44110358122004000c03074094038841e00941c41070382c01142000c0d407450034444407650143c040c50002c4c000f840018001070718000349074410100785101140891035031060086040540202c0014141442d5900201d5140c1c2001001440701c120351881c02200c89003420385020002c09a0410b04205684070b0100c602000801003114100032410028411400031900c001800f003801140c1c0d204520740010030120349401d84403504075000310b09482c034050840d0b4640c2101c0c0500c0700498042a1910172 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 125272356 1250 125271106 125271127
    0x301060902030103020a1205120d0518070b04450b0603060904150906020310050a0b0c0303010506031806011211090702030901120b030a030206040b0a0b1003110c06040305 75
    0x214801404480c00035411541941d000441c51050b90240c210b402c111000d1400500c41c040003d40c0c03110019680003559040c13a090120060201240c1c0a0101c2c1c1c0122107007009941c000032414120b0f40300d82c4071039040a0501801800c0444404504170203041428148850407146e5080c41601080c00e001a0011030481040310054401c403000f10762042c0c030140104a903d4450b120f9843d80030354041084607840752201241d0f00280390034040a420603102000708075101c0104100c010540c3e03401c03a82c0311501039076000d4490380c03486800c04000d0300d03030030070f000400003400c3c120b01541c0c0045480c954980c5403401c0242c8507107041c401740e001e034404060140c0c07800c050195464000707009800650b243c00c10781c80e0000000c1d41d07030b10988040f24100304800110102c0052154405454488010140c44801c030b45810000e6441200303030703000e944030300f91640861208ea8941c4070b8a81c041e41e001d801b01141003030901080c3d00808600f40c02c60034049040064450300710082c0b002d64400c40c03003500c919445601200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 125273606 1250 125272356 125272361
    0x10060812030903070b06010302071704080106300206190e0108061207060e1c0f06050903030f01030f0309030516140a0302010207050f060f040605070209311e0305090301 74
    0x40c0c200d140d01000708148080b41c0d5011003102c0f22030fa04402e804260f6112180101c0003486220b02c090702150401c18000c0c04c0400000043c4211040c1e42c009212068503000ca0044030850381d00006a825040b03010030b07207000701240f40405182d000404107420226200080040a100d0000050000d0800c4142c3c2d141ca41e000b22074139402c0b9030f065980742040c031407020242d0342d216424080d01082c0040c1d03144503112a5500e0140d100560f00341401208141c1b22031428586102003500304596060420000a8800d0000819207103d203038901c0710040103900c1c58881c1ca400d83e40e04030f019030070800805404030204a0400c640a5410142680381c44070760320342200300d4000300c500c0c0b145501c13690000d9002c001607a070002d098070540e8030807140200701e5000c1303400113191485128a841c2c6580008200065155042409410300c40e0090304d080042e650748095489600382001d07a8818040d0a904540401b09005804015032a01c0313076195441c86850116600e0708910b400700c3c11000910300190645440c103003030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 125274856 1250 125273606 125273623
    0xe0a06090509070e03030405040606081006110a030e040906020301081b04020a12020f09090f01061407170a0210050c27060702011803080d0207060e07050319060e100608 74
    0x1890300e44540e506240000c1d4410301c02800340303400c1148054001100c0e03034091007141c2c0208001030041050716038840d0098140341c8101e400f2600d98052250000760036001c1c4441c002c0040c1d5280107042d000310555800e48040404410050b081f035524401000081d030140300030b43c082c0c03402800900c00c0300500c0f20f20340c100003030b1005014043d5005100c0701c0f0b11550050720042000301269000358a50200e5404441140161801540d00c050004c003802041002100b00c41e05031002c650392441c880c3d0001070400402d21558030008e180101040140c0e47c84c001400142101c1000c62055402000c0c4481e000001d0300d0042ea044521003400140302d2400c10941d104201610400c01d03113540c03680c031815000610900a00001034144200e450b031400a1804142d410350140d6070100080e5103900d01c1a0a80000b90030501d400c0310103e10782107101d00f0500340010341404031800200181140f0840030945078104041542c2103a240d0345030181940c0307074041445100303c984400000010301038a090700e000e1034086003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 125276106 1250 125274856 125274869
    0x6020405041a0a090e0a020a03061508010606080105010503040807050a030801082b050c0f0111071208040c050f040f020c06040b10030809091e0406091217010e090f0d0e0a 75
    0xc450541c0f60001840103c90118000061200c0410707182400d0038a00301d4025401501290701004028080d407241d100b0320204501c05559580365490142280c0c1c441c02410007240c6402d00400141d8403031401503034040c3c41000342c20f0804400395a014601200b00034220080b8043c400140300320141049222034050813224500300803100d50f0f1041c03a841001d600d0420800000240349901040d04021846240a4200081040c2207400f020302035582c1001a080b030b8214900c0c040e00c13000e54072602000b8001c40d0880d60b92400c2910f8181085030a01c20195200c3d0040c4d10340165024084886c40501108811107029100310314203403402442c207610082401d0901a0100340074008243c0c00700503035007074940681e80080c02d030300e40d0390610480050300c014503c1c1601d00c0104000802585d5048420620310940443c640c08031612829282c116202d0810a01000c555004000141c0261109500000000c1c02d448128003459402400d05034200e1a60380840e040e500110910b041c000d00c0720303000b02070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 125277356 1250 125276106 125276141
    0xe15040213060f0b09030102090a08072105060a09030e041107020f0406030f060c020a0f03020c120705032a0303042301080403050a05070c0b03071205090111070201110c0a030602040504 81
    0x30301103d11942560f0380203200c14030002199402d00f54509504403001e50000801404000e41e0b100a4a0741e2144140501800c550b025a800340401d418841050800d0f641f2501034030043d5184c02d06c203001010032010603020486050660040c5842d01d10900503019501d440c1d041e6a0300da64014818521070f40040180a217113000820404030700e000d10f100003159031180d00816100040034040f03107000701e6018007804080b82c14600f102050740000e984161018182e42c518105641c05503030a07210000c2e44a542d42540250605280e00f200d001c4060381d0744e07003040040030038484042e03000c80d01d1500980c10400e41c900b4607005017198030b021102e5511030b40e5000d21382441d60703183c51b6030700616034041c08441801b070001c0480c10604000300070110402901240304099240d18003100300409a41c110200c01c40b415144c000401e05103003044c081d451409403090300389440c01c0c22607801141e40c0e000185c0d200100c0d008144002c861590382c4030b1307820001c601400e40580c49a060604220480c0c441d4580304208a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 125278606 1250 125277356 125277359
    0xb04060207050d0804030b0406020403020a060518040b01140c010f0f0605030f010903020a111804151a090f040804090507020a11062802070b0c0a0605060108011a0d0e1504021306 78
    0x2007504c41101d0503a07600610b00c098a45942c680340c80a03004540009501001c840c0d0003249099201015020100000c24002c00744500c1009100494188445490001e00d603011b18185882000009100e85900c1d10700005000750045203060807200108600c95285032981010099441c003000000094034514008020481d03507694065034481038001c0081040d0f8601d80c06001075a980000801c60352800c40d5000910710341440c200c0b50450003109080802072a020f06081c0007500b10440302d0040d40b002c0e195400503107a030307004240302450080003118214410080400d00050a000e42801030390345800801c0d07210840d00c0e0013100c40890004481c05854140401d41c4a20122045c201c403804006075012040c60000d4012030512249030030004034000c00066195642c240081c21902c00c1d40601c81c100104d8440740011543d45400780324284850315604892005904100700501003220443c4d000605101c41c03003621800c01e04030000010f41441c0c0c1c04200025070030064820312007000c1d940c50400403103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 125279856 1250 125278606 125278613
    0x106050406030507090509070306050a14010e090402030c0a0609090609020f0307030b0103020c0d0804060b03060f0f1f0b0717040f0b07060f051305010b01030b0607030f0c06060b04060207050d 84
    0xd0040784101010162580c1c0400c45484c010403040000c0c16003c0c01040780c40c43e06680c040e000c4c0409200e140c2c040e20786880700003064201180c01d0301d008001691071404811344401080003804000d00140ea06002d0f14007114030555406031100003d240c2e60315881c010701e14103141c1e00e0480d1090f51040200e280100002940c80d00d01c081241d03440700c994240090941d443c000100d0090060392204141882010040c407101030700700680c24411031240d80c00b4020355481105041c0c4070b4000350b0301c240580c180c9002088045a5a01c059580140103000502d01565959042d60b110780e60350740611143c1c1d40000d031a0b0207204120418640810a441d0403a103050326005039409401141e20804850715030201d601c00401038190070012031548028014489414040080c08441200910071034182d0720301103128005500a020b80c0d00240d60041000b0300304416514241e074040403032400c032410420041c00034000a80030384201e0001e0b29070020640d8845050200103841d1480580202e84980000c0d488500003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 125281106 1250 125279856 125279867
    0x10606080606030a0905010204120204060503030405030303130f0203070605120906010b1605030c03030709050a06080c04030f06090b04080a02010c080f0c0903070f090c0801060e0310020c0c04091202150106 90
    0x4803905495242d43e07503039088044401000e00280c0140740354000600010f14601044102e121140200d80420803a0b646a082541d684903d01c10190541c005000094507070444101490301c1900501691300100301982c0083d041412980214010500c0451401814160b1071859507101c0f01100081030b00d0350409400b020103010b00c9588807114610f4240000c10400c00740144da100306a82c200310f907140e08000d03030040c14412541c001c1c20700982d07640710002812845102b01c2401f4414072084a0f00d402d00315280c8001802c1e040000762265911440c12030002040401c5092140f03008080340790301c600a0a02c000d0950716a00d03007540800c5445024004040c2c000a0b807203400444000c00569580c482c100401d0520b011584080000840f02c07400055880c080d0700301c80402509542d03000020703a02c5072002d85013000c100c4401740e0182c1c0900b0f82c1c0107000080e50b00805941801808448028004000080a544403500102c1b04246407a440b8511b0980400010f184010b00880740c400c65810a04001e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 125282356 1250 125281106 125281111
    0x30206010311030a11100302070b040b01050108091204091104180609060b0a0e0609120307060f0617250515070b06101707090306050403020c130b01090e101508070e0301060608 77
    0x201d40d80306e9071a80c007401d000750704031492664442440e41151a003800c00c4031904500344201c50102d0341c003d000901c200c00120348024021401d915060600c4c3c10184200010440c010840031500000c000102d25404920b04030159000d032100c001c54582e041c200e24405545103035120201c844d03c01e0001070100c50300b01310009118081661a1500d41050704005401801e4070648450140000107200c01403111744c0d003102c124019192000e002e0b080e901c080c0201c5603582107880c410307990084449e0084039a6000c400d40d0100c40d0b0484a00e00c26a12031000031110303907401d00101d820240001d420300c10001c440c0702c0710307500050440d82c044024181c040d01a10311640360083d00313a115600d90001d22001d00403c0c11101440c1c00c551b08009c43d2a09150103503807041c19005003445900908148031070b4441074012042c0100d4181d490f4442d60b494010210590800540001c003c083c000c1808030340360b00b400f52155440d400360358496505040c400341c00340030b00c481412414042c2e4100042070001603001114240c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 125283606 1250 125282356 125282359
    0x11202030a090209011509081204120611160309050906150313050a030801051c150c0203071a0105241648031e0c0e0103030206010311030a11 62
    0x165a03598055000000300b0803040c000350302403900000460000b0980740214122550b0342ca400c00929211032991365140300e0f50601c000041c804001c02c0c4a0055a0840380b07259504c201800300c2c0c3c03802004170707504607500b0083c0d850b03100100010346c6100745648170207104001c10303066a10007481c0c1401400b0850f64800038100c941c0308880000401c01e204d1403508070094450700a8162111901d481c0303801082c5a034284116845411f0190f003d01804941c5600d00708410381c0b1005030385501ca0805414405840c010500d075065000c01e02091020500d170064200a0b00c0804440c0b441e1907040004006000d00903404040c990b90110700c0754544115804121264440d4908004805408601d8550b40e07903412404032083d100c420110b40314195550f40ba948869420300449205100503540d00a0040c90741884058481050007103000d400c00701c14444018094020b21442e12219210021801004070a9100320010781c8010010418080d10715032030070f0012002c501500c40101c460302d40f100d01000d030100c1035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 125284856 1250 125283606 125283611
    0x607021c080c0d2a0311010908070b0604140a0b040608240c03070203070201050f07140d09080d0801030f080f18030607053a1d16260a080301090b010f020c0112 70
    0x10018103021b0405410014101c00c000d0000d001d00c4d10308400c0315001100c3c115503080586020849a2805009981380301050380403006080c1e40700c200b90006000d0701d40e503c5400c156612408a103148050104040c01d5242094a01d520000d000c42000c20010051400151110034401e1040103503010049542c4942c0918025482d01d59041034061a84190303030005013045181c50700c6204861010030780440c000c0d13407600c402e6000c0ba6100081c0f902c4080790462080042c01c10070040c000034014102c513142c507601408460342010020043c5c1c240d143e2103440104800414498807080900d0200000c0740c3c000d2641c901a4200b03003280c0e007540d014041019980e02041d411401d510f2045a0340d1002c0d540340c01c40c0c0c60f000c0c00300d0074100039041141408a00b4a000747e00620350039644540c40344c884041100e00c892044a0320b030844032005140b40300004ca0824503030041c0c81404020481e03070806903003c3d250036100060100c01503070024058800795020740040d50000781104000f070307030443d01d4240e01c0c1c031050b03201 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 125286106 1250 125284856 125284937
    0x3c0a080c091003140a0c02070b2505010905070602030a05040315110a020a120905010903030509030c03100902040b041107030c080f2b05070824060c010c1205150607021c080c0d 77
    0xc14ac014868140c48440070f0210210000c1840015008020f1042c0030f40140c17071070661141001c907202e208200040d008500100020000125070103c3d52201042d00c1a0001d40f1701c244070013917107881d80030b0071019005900203460401800301d0065044401500360401100d95440c0100103002d16a00d88009001c3c0800441c42003041e880a1044141c0e00344c009082c2c070040601d0079416401414803103000e90146240101c6044541060310403503d65a41c5541142c0c02e0480c60b5404403920340d107081085a8807502400721000040080c00502440d080e240003442c214018007680c42c1080341001100c045580c10001440f030140e404c01304050300071000e8400801495a40da0420244c0f1303449107507450300054000303880c5040d1601940401d04200340350781c0c2c1e060710803402c10705c8600f900c5080c1c54024100f510101084080d15044005020b8184003402d1030420346c145090f80c07010070150000607112402c00144440b5408424400d491541c0d100703041461503603090303a400c124861801c1e8919414079090300c1e030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 125287356 1250 125286106 125286127
    0x70905150316030f0b030601031b05010804020d020405070c080412060b030a021008060604050a0801022203030206070c020409020d05071a040f0b0c03040305033c0a080c091003140a0c02070b 83
    0x1d05c01c010040c0880700701d96586d01d0540c0c0300440d1044c0c0c2401038040c003540403440c0d600c90900d0a01994008000125800494003003000422001e04100107100342459046c0c001060b5502410041c00440c0d001e0380380e00024109281036074040803d0500c40e0b0031a929040041e0766030841585600a03901e41508641e8964001c40c12510980d00250390140e03503031000141000054000384143c100c07400102111040c2c0445140d144d50340c030b000090241c3c000400107a54144600003200301c05000070008981d03003101d500460a080501d603819070b102d41000b08140300c400034413010100009069042d013460940b8210b5910388803415405141e6206100180c0d010100d80204140c40144d900201a260307902107203d0b03d0140c0c0701c1751072445040e0140d0803540300407924203000a1582c1d0f2030450380a40c90b00452890031108410020046a01400240020245600c035041220175060301503c0002b5200040303c40103882c0b0100801c07020400e410580d40c0440d80d540031410804881100020b2515610700340d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 125288606 1250 125287356 125287361
    0x61b23090409050a05070608070203030a02130302060705031e0414040b0d06150e0c0403080a051b06091006050f01051c02070b0f07110c0a05010509030a0803070905150316030f 77
    0x11880c6511509254103081800004110405854421401c0f0b030296581d90400340c2c0c020500f02d4030b2201680044c130002d21b40c441d194005000307002c16200480201c90300d03540050400c0c0c100b91420b071540e0f803010924082c850780d10b03000489000c41d844881c60030240b4040840340b0740c2c409504100d000744d0f1100c100150b60b840c1d9246c842c0305035034088030502c0400162aa69450a14103100e6020400755640c04100a007000c00119070959800c58040c520f800080c6400350740d19440980b000700051120702407524281010700c222806044050080c1142000a040705c4050300c0c05600900c7c45100107040501250ba0080202d84100e40c00452501c0000609260f01009011b150b0000c0c062400c000c003005000b0050102c03003840340c81d540e19485011014012450380d03d05c9140b41e00394004414172001e00c1a58001c50107484007070747c0101107603849011030340d4200140d00b00303072600c10200d0440b910034041841c09040b194a04004044204e00754030340340e0420f00520310400c1281d003d040c2e85440360600c250468 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 125289856 1250 125288606 125288617
    0x51509040e0105250f2a080306011206140f0d0501022107020105040203060c0c070306020417010b090f040b0a141503060108010b01020601350a061b23 66
    0x400070041d0111488015010f0031089844a080c103c00c1c4e44049014021104c041001c254241c2e02c041c2c0041904000b543d01780c00440089200c031098010441101d01280c5400322000d00c1002203036100d0a1240003d4640e407481e94440e0710940c1010400d202002d00005071a00c001000c954209040c2e104a011650701555198042d0165000092030b2001110100c0002e46ca41d0304064519100d594180f0101c0c01c07108103540c029490f42025000c40d040382c100340c024215050350f060680b400d19a80b0f40d42d00080b644140d21449458580740080c0303025032020711030071114130001d0755003000500e00382e1115801c0f1400200010310f402c541e100032a900118a40c03040442c1e000b20402c40d01c0074180340c5481c01170a5400580702d8030070302c501000881c284106010311a108441a0024805c1d42d003041600b41242c000341141000c0c0820049000d2680c4801c07902c4403102c0360141000d05555003031414600151400a040e183c0b010084044035a8420391014103443d002c0b254401a25820745844c40d064007030b2240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 125291106 1250 125289856 125289859
    0x3041205041203030b030c01050405060304031409270a0507080703090503091003020d1d0c130b0301050c03090d08010f06030b030a0501020d0f0e010501030b040b0a090c0f09050601090f051509 84
    0x101402c0404064040c0e01c40001940201e04460841c0c0284004559034416400b80301d4002030305001080c0068010141c00100e000a91100760034070f10002e022a55210b03082100c0104100448044044598030041c01500800004e0050040e490704450103840030740302908840c105030340c0e403404d0070a101c028000d85001400040c640086602c516070010040d41020540703a81d071a00d0056038041180344a14101d0841d20502e01900d40c6000000800105102c1b20355622607007500c0380b076103040310358003031084900c0342e035100420315101d091810113189001c0c085c078840300078064040c0040c08180040c50b100021201c0b42d180214041d8500c4021030700f09030011000030155800443c5449020040382c21080b41342032452000c00944001c107190500f682e4080c4070207060951083c000c240498814011a503100101c170401044000b1301c0e5403034030349000b02940100780402c1003540600c9250742a00460342c0001003440d20144240c1448032088408906108592240d036000501c65580c50301101950310301e280 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 125292356 1250 125291106 125291129
    0x1031b080d050a0305070c110d1502040b0703180807330e1806090f100f090902090901150501030f060506030a09050105010608040b01181107060c0809030f0304120504 73
    0x2035507000c1e100380c0044032901c1c0402e0425002403003951040300501c248035040391503c00907004032424450780003001309085d15000d10311440701c035510a07103000a2004200e6600c585a5900c5281401070100e90300324080c2e082e0030580d407000c00c120390740091920141c410ba601c0391803030203010780b80f10b1540d0079161030707044003202d0b0040040121b035070003804c0c0c094220000d0314805080c50100090010603801256010781c4004100d000c240c00c80020711506500400c080c2488074550348520344944150500e40c4100880b940b140385a204505040303500c1030300020500c4c024000c0040c070083c20100340701203011b075504141c0c0d80c0c1182d0421645c02c0c4c106500804024102a640e42049100b00014060102040d606507007824000181c243c840d84001d44115080703e4540c041c2c1e400d2816104010041021152070240c65188016180d41c0000041c07248900c502c0700082c401e81c3c401d0000e0b010f81030080099440d900107200001c800140c0310100d940c810f0b442554074406009419055405000f590000c240581 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 125293606 1250 125292356 125292373
    0x1110a030801050906010c20032b0e0901050303120903040f0f05030601060906080412030219030b210d180b030c040311040903050702130f0f060504050c030702030301031b08 76
    0x6070095461030507140c041d580503a00790786480064850404552000b0f0489400101c65003010114100c40407051500909030f40c0c00c5001e03030000005404040d161400e4003110540104070b07c542140c001a074a5800380c1e10044207614280c0000c0d181d011b00d07485400d0621201001440070302e002d008940c06806500c16400c003454071507001d02c220070784031300880c1c4c0a4494080049815070194202000710703200c641d034804080c1d4540d50796409101c0e1752250701080c99024802409a1a8030303c1060706035402c10350300011280313094400c11401140382d609500600c800a01003103001c0c0d40100e030f10b0580355006e0a1003190417047c628508049109a4420308280c030011051000200785100148101c90180c841c076940034507018204000c030744030703401d000700894002c00504005050400740c00d041082c1e801d0000901d6601001d02d0340954800400c40291650759041c2071000389094032440d500020f0540744182149071984000e5542d10041c00003505060341124140075410348040000d029002d0322090b43d0310301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 125294856 1250 125293606 125293613
    0xe010e0a0605130608060a0b030c0d05030d060603090218160e061c150602010c0c02010809010f050414100501030206040b13180203040314070309060e06090301021305040b0a0f09020901110a 83
    0x301341a0091001600501d004920054101c0c000c008480000401034080c19640004002e00c02c083d203d012283e50105010b00103182a03684207080040100e91004260200316204001000d445011109032903201d01c0184407000c07400000500d11854a030038603c10000c14040010050b010380c5071042020100141100141c075515003004681200301d021222039140c84039000c1c1c0c00e1f80c0000e0340321070000c0c480320300300f10140d8481c01c4542d402003507075800052403003425038001c006e86904440a441c40c400000b0821306091040112000e0a090500c1c100443c1d4116030010f5003030300c940e02c1070849100d030202c0c0f269200b0229200882c0101075100d14403503203c0c019000c00c4069041143c046e00400c64000e051002d0f04a20f104442155a066503034658041c100300c0140e880c11002e420380c4da040310301031002c403d498400344002d00000c9024203400c940540b4050410043c1c1e20700d012118011040100d08022041107a51003c0541c0c001030400b503151402d80d40100d40c60910720030b10040e40d2198a030f510090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 125296106 1250 125294856 125294861
    0x221060402070c091d120901050a11010c17071b2a12050c040209030d03050907080d0c060506010903120c030507020402041805010b0c030d18170a020f070e010e0a060513 74
    0x81c0e00d2901642d4024030900d0807160302c407240e0384046c00c0c500318100b048943c19840340c4010030343d140581c24a154125210450701d800c503041e03c1e00100c007140701000c518444801803250140c0c484141e181c4400c0381c030070100c894500900c8503030008160340c4206403925444a6090481c002200c02c1029043c109a40c41d180032036109504d0314181d500e0b000300550800e00d805c00703000b11142c404014006080c1c212010a0450050400a01c50029406059000b2a84490501162964903a00d64a5200105181c00e055003240da01805043c1807048000c0b0400c000341b00d00003c011540094101a80c5400c50b030b04065a0510504170000c0d80244009004a841121983d0010000e90030310b900301712a85e2a2842e8402900c100141042964001d100c00d240c030a40582003180211007080c009940e80000f0341d1481c0e6080e0f01c282051001e0400400c82c01009541004035000401180b402814003038941001c401442206004000c0c81c0e01400d0002504151240c01c610002d15024000308501400441c00400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 125297356 1250 125296106 125296121
    0x13020a0203070620040509040609060f1a0306040302120a1101060f0e0f01050a090b0a0302090a020405030f03090901090b04180804060e0114090d0f0602030106030b130221060402070c09 81
    0x8042c0d00e0711101d0410b1404c00310240010307104508610349080d04140401c950614014401c0342c025480344001c0c000296180a0841090850300340481c0c988050b68480350041082c01c0c150340681d0080c0c08210200340c0c005448861080b40305821070b65034020301c90444400d403010100081541c2410400140040c03c02c884104071003809030205201d44441095400200e420b01c605588500c86840c10b001c001c00541c050aa82d201c001d1002e4a0590340c1d60105804003030803241d4002c10703507010508108500302400031090503540322029614020003900016200c00040c003c2e101203e0342c40da010040d54980740d01400000f10140310303a040a202034a08829558020f00480b800600000c40500e0254018207481010804408941d424009208144031560940ca201580d051b000070f4600d40211b0b00601c0114040c0000365008103420b000b200c01c4c0003102420035900300442c0d204218000d601906e00008a09061180c0f510f0010345e203d036000900179000b40305014000d01c425400000700b45074030354030080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 125298606 1250 125297356 125297363
    0x21006120303230612010b3f1b040e0f1e0d0207030f0204090219030302060609040515090f01020d1e06060f0e2d03010b090709050d0213020a020307 65
    0x3c0308141c41c00901c000e00e6401e002e804030303140907000402c4461414010344403042c403008000080b480381c1e420010385a0520040f5985e401c003501040005000b080d0644817506581c0320441551360100140860b41da800d07104000104000b035200f906040d56100d40025055008a4080b00c009140c200b42c2c60361500302c1035004412a01200c0f000700044480400e081c5100e11a0360007030a640c502c0d42d100c0303c44941c01180d04991240d034035514140140c0e2000f00031117031020b0012620003c94114600a0319101d005802c2511030b030074907410040080c80001301031215010080c102045e6480c5c0e0040300c2c1c9401011600000f180d40007269a0701d80c440c65a120040c200e203452820346120703c400314040c0c2200c01a0094200250040d80e5030003080d40600d00352420740030040c0100401c5852170540070045002d0300034200700c01d80c0c621104001854240210b0b900c44004513101c034600c0c10000009842001a072045900550034041c2c450203669484402c40101098010159600c2d4810741d07009480341d2000c00100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 125299856 1250 125298606 125298611
    0x3090a0608060a09061a0f0f070c08060a06260106030203030c031e040e010e0c0d0c0c150506030c040e0a08120f01090203010e15030307140601060e03011407050a021006120303 77
    0x140c45a441c002c4070100d070b00d0024146c0b81a061041921040c0d0300083c0800c1d03002004100d84581655942c0c01404c040d802003410780303203103400c0c1712941f4280b03d8090100702c4818103110060040b0014601800101201c10b1460107205482034002070140c04654806035040c0408544040c10300008402800180103903078010444100d00d005100b928010744c014030115180b50001441000000d03a0b82075049843e51740410300302060401038030159542015840c00090740d513085401002810450401640c078405820703c8580341500201f0356401c07102c101c80344503c0c2c41c1e0071800c0760f180b02804000041e41d04001d006540300c0c041a44183d90300c00c25900c01b540244c0c414000a100d110078403c0c1c0341a101e0040390020f4070b4841c14605881c9100300c100d199814041001040e00146c180400c038902400018090b0885d5032400307038080d2988210034001402a4148000c0700e244111650000c0d80c00b1216007040c51715004110b0080380b03083c0c6050103600b403c600d40303800402c0c07950566007040f140030300c640d505 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 125301106 1250 125299856 125299859
    0x6032c1c030501050a0e010e070507020d0507030606140603061e010e1c05191104090309050315060411070302120f16141603021008180313051f020304090e03090a0608060a 75
    0x40074807800d1123103800a0f80344001003190580704100070b2120600042c810f207004121a12104d0400304941c0c41110810f0b6540d00c1001060803c0c10b0381500d0039001c440e042c0c114980400880d8a0a00c501040402c0c001100b011130480d03070082d400f0209000b0040d02e41d05440328440300c120641601c0900035203191080425240c0000000c07281904c400e9400300702d9150080c403050034840a400c1d0f0380310403424400605004a0151000c1240c03007620518000800c0403403d1000c284002c84024040c00d050005080000c400400d030001500d0130030740100b6505039039030b1031f15100c121000d02400c0455210310160b0000c1100b809680780784880010262070507104e8514081c3c0301d101c2c00900d42d00c0002c1d00f00320200380503403000b401001072950008041c0b0f4a10180d40072880b126043d40d0000550080102c440d01045c4054141030301e6407004030f04404403141c218000203001175602c4c061442811440f0f61140052280b00e0380c20700684030000790250002d0401a15120080d014850884805d4022400101c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 125302356 1250 125301106 125301119
    0x5010609150e09071a0a0509090906040620071b080f07060f170703020c0109020907020109030e0307081513021804030e0415060f170403050408060106032c1c030501050a 74
    0x1002021642c2005500a1841c505017030b42e103171038019031505824401c05011088264540361380d414490000000a44030601c1c3c10300d000002c40c0c085103188085122446000c0c581c40000c1411181c141b5003240701c0e960a03101c040350089610342079402c040c18900403214001c0c1030480000d60382050310340c2c54030f071070351020240f60341103847d04003813444134404010b0716001ca0001c0d4000d9004050000d0b6101c00810710b50f5503a0045200120151100710061703558460300ca080c9075005000180e154001c60183c02e82c140b4002c0c28590380c969a40311079003403c1d52000465001c011070034484070f602c1d9002e40072282c80c0c0040064200c18900444040c0c01040308030821240c949011312409480b144480500040070b801c040d0308a81c0c644403c080f210901403010003000e05242c03194850761246200f6642c15903590300f03200c0d105c0d08200069110301c090505002e0603141c4001196a0600c45000d020121034914500040c0903291030000e06420303245211a035011480c81d5410381150b81640c0341901d644210310364a22 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 125303606 1250 125302356 125302363
    0xa03080a0c02030409020d0b0901240309050304050f130c030c03050114031203070315030b310f030c081b010b0111030909040609080a110c0103090503031305010609150e09 75
    0x481c0401038004100901912165a010340f0b2107882881000820064100200f07109210a0300106010840412072103c081010140096400414901409404003da5aa66a9010b14050144981c44490310041c0e01e49800e6840880d1008031942403101040010f0007074010990701c101880040c0c03c03c0004138072040380700b00f00400c4a2001d0b00403c0d4161a2505684407500301800100405444a4030002928851045d44001d9030081441c11158180210740d540700028600032052840d4408101e800c030314440d458480000c940105120502901e1890308a9502285040051081201159044c10340d100c3c841801e010f07801d120020030032100d0103001581e29500418200034698410042010181010000107401c06d03c55180494210800d03540d10066400107505100001e00d81c00c05000b0300a000c015012610400b030070104070a8aa035140c00341c680c40000c102411090100c0c4250080101c2503001c4801406001c9041044501d05074400710035022511584007100501c401060500c0400f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 125304856 1250 125303606 125303621
    0x305070506070323090a030812010e040b070e1f020c0a081b01030b0a15050a090b040b0a08130506010b0d05090309030d0c061401030807060c0c03050d0e120a020a03080a 74
    0x11348842041c801c00341c01020b03000f050754802d00e256240a106503129500e41d02c420301c01661060b803280d0380b50107280351a0558840142c6c0320141c140c1600e010b210204030613403c0329400030100d2600704d0200e030340c0c0c034042350041d0741071030705055081101c900404185901080000035070b4802c5800807030165031110025a01c0c0c100480c4160030818850b4000455070095100390701050015292015079a5107007029050185880c0290010072000102d500100d640f01000340041c14000300110309050402034402505d002c1d490300308041c0031190307001c250150f1900302d4400d00a54070104039800b03907850300340403660340d0001d5000030902810320b004500704078004010f4030b140c440c000c1c00404080c0c2c5131340411203069500c90001d40f500d580c0c8640f0240084e1160036224040c500800c80e080d135880b60752400b07004890101919104001c0741144000c0041c3e40101112041d04185802148445030b441402c2d06080303c014515001002c00100d030640c454010072000c00741c3d4000d846402d841e5032545c01400175100c05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 125306106 1250 125304856 125304863
    0xe01080f010509060a0b120a230304080d051c050c0c0c09011211150310140d1104020c030c06090f072705040303021c0e010b010c030e040506032104030507050607 71
    0x40d800140c00c030869a0000e030404400420b94814144407c0150b810900b80329015a00c0143d07204c174140e414020b1030031059800780110000c0d880d0a10301a03046072512011b0031100704110300011000c152241c884c00303142d5082c050712420040c130304159103111902e6102c862882418014852809801e244c040700450480d0354104a113180300d2200c1c2d50700341d040340b00d8150b1340f90300c9100c100001d071407149044007452085290409100b00c0d40c0c1850b56001c030000f10403110b284617210740707601140050280b10300201c000d6400d4a02584510341c1c80b00c0355040d4007a51003083d040307110307803010028068000030310b0750851540181554542c5445008840c100d01c80d945035a5006100c0305403541040781c840d440294464040d01d001402c040000a0aa865990305402100310f66107a48004000640a1040c03c1810400342000c01c000581d5030b601409103a600101da03446141d0301c5001a13810340707060125500d9000c401c81920fa141c0ca200f103001c90a034100380025140c0b0303c50008041030900b0118111401141c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 125307356 1250 125306106 125306113
    0x609060f0c2503020c011d09090a08070302010504021305010b0a030c030209031002180a0503070311041b0206060103050109062d03080304152022030213020417010506010509061809010e01080f010509 87
    0x40c501f040c40100800a80108818856042407101145280000d0481148a40d00100340d6041c140100585140030389a005562840c090040165844450032a901315159080c0464a102c10000507802801550b4646400d40141078149181540a6005110300b0030240009a070354143e88080c0040295240110360705075202d1079050010402000400c0d8074444001c00c0805c050a0b65407416151006100c04000540d01070030502280c2c1da00f5010f964090400d2910401c070081c94580d00140c0f40b481e110702c0d0400c00c2003404240203203250001e11032000c0c5402c00c0502d80d880c00d0920b0003443c041c00d5030041c5241c13945810321078240030105603280c0540e2010100f51900704416200e8510280c1c40140c80c009610300c0100c00000181c03520f4660109036464010016141c3d07140410030907803000f460319402e807103900d4070007000142d07030300182600c042940a580750f54a030b040c080e045d1080b40652880c0940e1011800c00006903451603003c165058031004400e9450b0040d07040c044900707940c016260705541d500f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 125308606 1250 125307356 125307407
    0x6120302070303050f0f0d06050f091b07030513080c010f02070f06120902030f03030703150b030c0a11010912030c180302041e090f020907020609060f0c2503020c01 72
    0x13071003038000c0c040001811a22920b010580609041607078013417410342081c0f58071181c00b00300c0b6103403810801c2e044080a444441040c80c241d05001030060060140c200c8942e8045141810b0502c1041540e01003090301d03402c250710580b10500541d403802001d100c0c81c00a0040c000000b1014408101e100484668180400c4801c2c2024000d640620755548401c0410307030744500d104050b90b402c211805501c0329000207165a41030000d0000e0688012041001280141000070849010740f04100e951000c40221804d8031211071100803504800c402803081095800e00c18020103010403104044100400c90724100010382190000350341707030701006448902d03640080e641080542016042014409180c401070105006038212080844031103080642c3c0703680c0502403140450403d0003907030350004c5d1280001c065030302d8126005540e41030300034a1445101d50000108110740c0055055404640c858079030150903007103500411b9024100d1200c20340051054401104055000c1c0161450450000300b02d81c1214 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 125309856 1250 125308606 125308613
    0x140a0602030a0f050702060a0905010909140406020307030b030a0c05040c0e0603060d0501060915080d0201050c0315041b02030a1205060d03110c0a0f080c04020910031503140c04061203020703 84
    0x20350041da400c0f000d0081c00c100b11001696000700400c500c0445840301415542820001480300d182c581107402303294501030505016012050846501c207a10a1000d603403903450140c1203001e8045800c0b955014030580040300b0030059140554070076514182c0382000082040e5400329241f035510302245801010800100b000c608048040c80c650a009070b0020036407942d0b52025404480c10305815007008105071000340801c54091102c42e000d014184001d10150030841e003440860f10000d410b1699100b031241c114515525550414030500d41e540c400e5180710f4609140280d01c9901080c5010b0020f0071580f10007040002da0311400d405040003a011122014883d40d0544500c41101515095440384070094801a560041c000001d4261400205025494207036070b9032610140071074280c41540140001d0714161074013258580b00d442e203450040380241605d40b4007490001503070006031100c1c4582c0c00051a1a000050318404010705507030800400c2c0c2d4401c82d2004002e91010024010b810210080011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 125311106 1250 125309856 125309867
    0x4030f08091e0c01091409010b1b1209030d0305040b0a020a050409090305120a02031e071e090f06050313140708010c0305040209061e04021806030f01140a0602030a 72
    0x15060000c030b4114a15005090140600c00150308007154094100388120b564000e4004000b800000044801d0710300a0000811170181400b071180441c8004c01d101d400e001650315070501410b074400995000c0b40c201c0070310040a6201390a4603010384611180304203124424407505205541100d9201d03002c2c1c654100b00c1d000303540201c004004000c82408045018400c0d03205040c00144662980c45d503078200d503c05854001c0c0c0c0100065901c510520400410790900c245440341c450281000a07560742c0c811030240c0307207090700140d54a140b4070381e07013807000845800c001d81034192080e02d1142e00e9010b0380c8050894541c03108881068030b44600e1030f8510000b581e030340307a9105c0c851001402d5900f065264140300742144e090b4255000002e842d20240801d50070140ca1651300300c9002e4a01618480f18448070f00246044080654091580060440880f400321001011402001441c0316520b04054400d042015000c2c003c03103039040031701c020903107940c5400482c6100b19076072a00074608000d10441d0550b003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 125312356 1250 125311106 125311111
    0x10e091011090a1d0c0c0c0409030c0b0414100902011b020103060e040b0a06050105070320010209040204090504051002070b01030b060d080c1615020a0b1302030d020a0b060301020304030f08 83
    0x100501c28000c114540e074500c5240c0d80541400e41c03030940c03c112400c0040c0c6041001412000058a04003c800b44009010074400036080f02640c02103a90f03000d6150440b010354a01070050300000c0020240420854450b2401100400701e900710741041d0820804441100c20300940240801c0e1456126081d40d541d0752188440d4900505002501550f503000d144500d0314122800c6410405010810122504034400d0201034002842c0160070034016a90207001248010400e0402c001c82406450040500750111800440050029911103a03210141c401a140c103907007c0707845000d8810010800343e150320947c0c00c2c003504046080901d900c1d5450b6050310f50800350031150088030210f4140d020803040c80042a402900200920910140e40e959442101c441c0c2c01005910707158043c030400d9541e00103011468607422186008141e10f60b84080140420003180c003d405014220341c55190303940100f04824028010b2107011510303034490042500300d12080302c005004c02c1160100c03d58040c8100300d01507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 125313606 1250 125312356 125312381
    0x6040e1003051e1b0109090e01062106050901020a05090607050a1a010e090a0c06110a12050403230307030c02060705060f1b03010f12020a0e070e0108010e0910 70
    0x8014985a848081c01c00d081110440611a107252402103c16010405140c141c140c0c144c040d0300c40ca1085000800304117942c072420400301c0d241c2d1510002c1e42000e6020000500c900700c052010042c00c241010000d050082d001e80f040d5180c01e0000709440f10600854030400155610710385400a164200480c58000c1c000503103207442886502d400141e071450300034070304079840d055100c0075600d0701d8201403a03220020308020064010442a000041c413400d4514144d400da030801140800b0070114151504480d83c0010703062020b9040311401c0d20b0340000040c401e4a00030700d0071b4141c0d203841d40da000b0091000094403560030390040183d034011900c61b401d07102e28580300500f2180703054100e4840901d41003080d00c1c0c070380d10b44480000340300c541c10004a0070746800900341a0740781990302d4907605d07102680b0fa603c0b84010446d1402000d80031982c0d40d074251030181c4a00360f043e91081c1031044008003400031510300c06010405010000c644a00b080e00964400e1003107030700820302c6e242d15820b560043d109484511 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 125314856 1250 125313606 125313631
    0x6130503190e10020109030806010525120906090b0901080a0914070f0501020c061b0a0b3303030706090204020408010603052b0c0807030c0c060507030207060e06040e 73
    0x1ca000089515280080c5045565201042050842080310f0306000000c02c2066a14160b0028000707904014940c0e442030003400c00549440100c2c00400050018000d110030584010f0700c176a0800082d05c80107511140b00ba5541d11140d0b840b400107030b41c920300314010101c8050301808140003a41c45010b999031f12454203e4045a042d6450b41c0742c6003418041d8500810b1a00710000500203004241e990a00603d401d100500c610280750001c5126441a0700d414003003000b4242c00740206050030400c046540e035101c4000d00300da1800300300c0f4041002a442c015015a4014480340c201c0202c4103030402081c81c00140034602d881d2070ba95491005000ba44c034101c0c1c0264091200144c40b41c005e114040c0114040c0c4080c00301c9103030041800105620b0742082000c000044600e00785003070b07840f031148010150311803045a82d844c11401c003030f61083d807200c10040c89242402404900c2903070243c05080d42c1803090f02242c41d429252135041c4c0701e20300c140741001e811a805000030000307180b00441a581002d04418030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 125316106 1250 125314856 125314867
    0x18090e070b040b180a18090c0e19060e040b070509030a0203100209010810120209090f0616020d020601060e0d17040308041e030c0b03070e0a27050906130503 69
    0x5044076500240d00041c203269010801d06040743c90112412401202255410034035414207401c030030090b201443e900f8020341e07204000d000704403200e205d91000d043c0c01c0350543e000c0e1510340c11040c41c100000c8201c0d05c2c42c0f82411000103100c01c8800101d4000c0d50709c08000081580c80c030030101c4d80c0e03801c038101065051013901981c1015031014440b03c01484580d03c0c002d659402c0300760024150705400b815000d071028005004000040201c40c000044a074111001800360700c8400e6070926041a000f40340c070f807500580040c401d41c80c03400d2400d00d03000030141c3c00b81d401c0e030001181d05076101d160902ca10404103408440350700b15440e2900c064220035102e4000041c050505207440482c45c3c025400c116500400000c044c41420741d46002030040b0801000010314003400e55032122020041442100e07400d050100104010602980325004125070282502000c965140f0b01c40030400e81c0c0340031400c00020083c02d061041111800750b20b1007941800001d10158542c080210708107142188255030600003400b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 125317356 1250 125316106 125316119
    0x304110d14061609050a050d02060d14010f060507031e090902070b0603010e0304031e021305040c030201030e07080a1101031d0f07140102060402130f02070602130618090e07 76
    0xc1c000c08100d081c0d00030001c903d0504200781c0c0300210f4000750000e0040780c031000c01141c1c3e101c02085096407015940200031200500c0440c0c0c160107400f034000049402c001480e0824903003401c4c0305040324034112801c032640e5900c03481541c4500c15850040c000402c201d5084e0207480c1840031240725684240303004001e00e55a18098802ca0300110b03001c5403200c60500c10b210491900340034640f07209003280c020f1407900d4075564400000302c0e0703003040c6403000540c001184e8040d07580b4080000328130004030005000d5498585450610f10302e0b9800100e010074504829202c1858000580505a03200d440040c84010a01d85803408814512041c2604041d02c0d401902d05800521144600140c40348000313202c8121585c1e511802e00e011a00710f042000c079014520752691b80e0000e0115005034042d9100c1040c0da2130005074030081c102d20400152b0803400002d0020810074994014400040d26190041d802c64640d081151802c0c1c10b5082c1d2455814a2071003848860303007690204224039807500444083c00e9a412 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 125318606 1250 125317356 125317373
    0x7031704020d02190b070c03050705030f2815020c1506060403140c060c060114030102070c09020912060106170105090f061c02030a03050403050d08100611070503010f0605130209060304110d 83
    0x1072080f95242c1f01e4050410400008008900c060304088028291042a40400a54a0100c84a40b616060854505e40342c098003040d20034560075005011551034600403541d0340003962026a550445108403914152003030310003104035000380740080c82249428616100e401c403800140859046900911032031014940d908070090061100207805840f05600d0601d0710900d808120305020300a2740108401d90006e000d04003684251000750000603222100c10000c03407201040f48424155611403000046485508100681c22840c00c07030354408100ea80355802d00441c81d105a4144800b211101c0104605217040000c0903880b0301c01c210b4075407182e030b503a0300064030381048410148d01181c2e0003c1e0030300c141700050000310b10720002d508004805080c6800d4400c03110358144034800c10801c000c0050001d090091040070014000103000740100e094203128480144003c3c820300788601076081c0c0c00d200714072580c001e4401d44c910042c04070f425a84c8503140e0145000c2c0618820b07500100880d20200040c0500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 125319856 1250 125318606 125318617
    0x9121817150f0906010803030613090807020a0603020919081902120303040606150521070c060501090506040b01020d09050105031012120323161e0507031704020d02190b 74
    0x200c10380740b0b030910510243c103102c3c068005020366001041000b0990f02e600d444000041e00c20032002481103404c0c1403680150180040003035100b60f4000e00000d07450380c590040e2903c440c046139030b144083c4550b04481420402c034490402140c012509042e0a4461411004400340c0003030405800543e100e0019070441e4012102218055a0b40744d0602c03111803031036400d1344a00d2250a005182c420020b000031b00b550014841c01c0050220310b00000e40451040d4175001e8140e9008105000b156110344040c0c0281c40c0483e64540200d180854400701984000f03220803040c8100e8540000301400c240c0115100c0d400142000340744001200c001400c600c1e1008c400c1481801201c4048075200103110041c01d4400109011504090304a041d09a01800c4040f540d0010001ca4907003818180251003500e04058886981c0005210707410036804207a082402402d4151280c3c0e203520001c2c035031b40d04c40d0030490402e41d030182d085204821014014104059104585070540008824140d0b9810280380d059000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 125321106 1250 125319856 125319871
    0x1003080a02010c170103020f102f0c0303070803130f0803010312140f1c0f0501080d08010b0f070f0303060801020f070c080102040303050a0c170d0912181715 69
    0x466075200c40f05a40944000345900e24004001c4085d49141c0016855032580790301d240c400d541d1016940c56840c0298121461070703c1650140d41ea20010500b0078031840e10403250441c6d1409040c002020a00c5e02100304e4020f554809030403030458444a240600d81d881d451422901c0785007101441001ca40c5001c003860003075220fa4403c20012140c18801440c09031000c10811550000703000284082c03c00700169140c03000c01d5800103c0101d0201186c40140c4002c0802110091030240045800a80803d424000c40015101c00c2d1a0344d9848294400d5441401d0240e0103146041c4180e600003010185505409400307881c0102d41103480d00401c1e0b00b21b901074407041c1408a0700203a10001c200240c00c6010003030066000850603e40380d44c03000381451003040c00007420480441068010040c07102d03030341c03540d00941c00b8006d511503100001000040c8042a400e0fa400c0074002c5541c0c010600c5034011104018824454105152401e002110482d1900003a140e0720300440d1080b0302800301d42c034600e512401d46c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 125322356 1250 125321106 125321111
    0x302120318011a0609040f020d060905010302030f030301080c060903030706050106030615020a02030a0b09030d0204090f0605030d020c09070207080f010204030b010f1d0c0d0c0804020301240e1003080a0201 90
    0x14007200c460308444404848080032071407800c0d21a0103070f4500040d04c001602c180c1e000710b028103244030420020302c100c540c049140c904c0c191011139403460a600c80d9058900c01c0e03084034000341a4210f580c0c1e0746e0001b440b0b0b04809900400420140d0b0805202900d02034402a08980c01c10029640740015924240c0000b00000d642c2e050800c080500441c0c41300886a003400503200c000c000b40c012a8a40d4240c50028100c2440a070100e80d4020041045400b105075089086488540722460715014084407000c010105083ca00085003074a40458110318000d0a90001c140004a010611800d180e000300810291f01a00d1800a8015002d0000b24a80b0080500040c0da4a0541c40c0c8003c80700310607001280c1c0d510a0303850900c40d0241c4080c0c940e00e40413542013015050f80e61100110028461202c002220b0380c100408180085d4010f00b0b0180900d00c2140240104c1e404010005641d410001c690400107194810810500d005039510540000d4013440c0c400c0040c0d00d07904d4144d0164000c0f5007641c010303076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 125323606 1250 125322356 125322391
    0x13090c0507080a03152309060f060a020c010e040204180902030f010e150106021216050a0f0b04050105090f030703270608070305011a121f0803070308060d050a0f03021203 75
    0xa480c070714009408140310403180201d085034034404203620291b1030350181e0360034404510035a0303071a09201c60016008001d10b5a40d564907400a48900205010601060b042903828101d4506402540c0c1661040380400c20b0030b10010100e81c0242c541440c3c240e800d17004050400111010a014520102040c0b60003003c8421540302d80207c0b0920580c842d80442d0003c4d20030350342e6900b000045800a001000b950440342c021810314508100700c6010003410b419850031a1410844582105840340340200c008120543e01c207400c80c0c3d2180c01e10b40c601c41c2c00e0703082042903c0019002d100502da01e0700070070249451204045241e070201e110950410804203c2c680100b003242d5070b2500901e0b01411000074554104c07080b000701c1075682e0180030307000c888040c3c0342d0300054043d6000104a50001464203041c1206568824000ea201d510404c0305500240c0e4a030005031550070a076400000759680301c00100800b003044e880b40304045895070400ca085004881070a1040100a0080c41c0a000b0741d070f2140f00c0b0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 125324856 1250 125323606 125323631
    0x60307090e0a090c060507080d021209010e010516050c0c03010906021c0b0f100e0306012d03020f12101e0605101409010c0507090c030605010513090c0507080a03 71
    0x1c03401070510701c0560074460541c0028103407070344043c11100d95040c41c1d901c0d0300701745c40c080c0038502070107410400b110304c00300b001c1080002c29402d207400381014900030050640d007403180500740c0d0350403220464800c4002c0340816a051082d401000264480d500340c4500b8880b140c0044e0a441d00d84001b84c0f03c00e9004036002c40b011960388407280b4400d02c4034404000700140031b400300300c0d00702814040c0d80c40384482000d040000381c025100044c3c08400241130390215078482c9007910314102c15000890000001031051a2110224a42002960340044c000c1000c9180e600401406841059807000680120341d41700d4440b100c0d901a2101c08028800d806650b403419580c176108450350307580028882e90b01001d651250035000b00c2001440300003070607140c0e5071702d400800698000c0d400c07010003030952080c039500085000c180d500041c070b03801590780d041c0000d07540e035401120103010b2a903200c80b049100b035604114071000e661299003102c5060610906080098481d10321a0f088038040202080e264004400d50707 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 125326106 1250 125324856 125324879
    0x3191203180507090b0103090b04120207080304061209030c080a0c020310050c0d0b01110a0308091002130e042609030c060a0905040506030709020403080417070e06040f0b06030709 79
    0xa80710807880030841005907125a03a03600000d102d011340c0707107643e9800d88801da4400d0b00603103621130300841c80380c03002c0c1440c0c0342c40b249140340201c1c090014025800701003131780c800102c1181c01302c840998178000c420083e0780d031031001410300260407014441081c0340800054034800140c4000d5505896461042d040d60042c10308100d000030740b40b640103240c08204442c1c401100c0071755030440c2c040d40001507030307500d1500103803040c002403064400e5a00c6061817200030075500c02142d80c0f003000000140d500c0e1075400c010320300c00d0b030080f42c800060b8103844071010b00030820980c00b1642c0c0203000341d02686c803800c019248010070528040725982d44882c00503000c0c100c4d080400581e270818070305036081032800020700b07001403111005028040c86162070350040b504940c0c00300301e148098078110380304540c3c170365892034070000315800386c802c1d980c5259034107040c0b14110001064190882d42c0b40d10070300040399148e4013084014803414640d070002d190b40316810a9180c481c01c000d5440b88045813140740156042c03030301040c403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 125327356 1250 125326106 125326121
    0x5010b071103070b03130f06051906050307080316050304120c05011701030c090f02120a14090c01020607050325030b0307051203120903070f06050402090c2703191203 73
    0x181c2d0140d0b500700b0070148407130100d036406081120007107560600d81c50500031f11001300d440a040ca41c01c1005102107a589000903800358007207000f08101c05541c0d40245900c4082c41c0c0304250550300705118068001460202e100302451003541501c2c030309500d40c030f031b0005041d24980c0d05580110109809114a58201806500201c144190140d580d031450341c0b5448400c1183c0a1440d0701501d8184402001820f9010789503818007100c1101081e2408054040051880c0d055241040c0d061101140c8010f401041c1c84038001c4040e400f6101f41e540b8410266102e0340050509401c4402c2c0d04142005603012071120790301814195070100d101c2e0300040815140c01400d0b044984a1700da40c0340e000d0120a000012900680c940c0e0111400d2540d80318011411401410000390000c80707249140000c02c021540510b21032442110310071401c0e215000b03055030500550024110548640d0003000b013600c3c82110050000f0300060803079403000482180c41e0039400000008540e00d010812000c22040c0e09170181c0003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 125328606 1250 125327356 125327359
    0x314030a08091501090f14010308120c1e0a20010608060108011104030b070903080c0f060a09031d0609030d0203091302120c0a03090204060308120f0603120306060c0105010b0711 78
    0x40454a00b680f40109183c0c18420003051a950380b0010030321000c0c40d082203003060000400d425907503a6038208021503601c601c0813403d800b80c1c40301c00078591760386000a8900c580c51300c1d0241104a0440c0360010b01950040501c2010b211105541078981420728001d0f10b2200441000802c20038940380d002458240180c0200351180d04210703102e00c411810100350f5045039005451100c954403078410680784401103400c043e1075104001105102c04000040b0300c042c0c9080c580407101e4a943e85842c605c2203503456a001000640740c3c1a6000e8140f0300308048052540000b000107250005582c0001c1c648000c8041641c0980c1011070480d08614203280b40c40c403c0540d1803130940c0740c01d250704a20350000d080100300a00200010442c5400d55100b41d00500100f54068404c11900b40c4a080403021500f0188000540000c83c60008a4a103501d25489000e400060010071150008401044480c2c000801c600d40104c4144104903c1c000240503550080c000400c00a40e24042400c3c20300f031803903504908d103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 125329856 1250 125328606 125328613
    0xf0501140106120f0b030d0507111c060504150c020a030914061e04031a09160e060d021c0b0115020105010311011d040c030f0e0c090c030705040314030a0809 69
    0x1000300c9a00141c83c1c55031500c0c10000082d224045031141e1004008000d0700340d40510588007094a050f030804020198030b40113007103400c04000d0203001c01c1000d4246a40010603c003902006000040d01e07070300441e405c0340c402e0040c2c140d080e006403100400c9940003001c400c0140d100c120303040c00b0b150b0001c03e440060400580c000c0d4131240c45d6000b080d564031840b031201e0361540318450305861182d08082680c024507407042c22010b0070740f00c07455590401c00c81911003004030302a00981800004d48502c095040b0b07000c0341c0782c19240d65944000c0040050b00c5820a80e0866100e5840782240c4c1903d03039130b07000220310070b0394441c1c059410140c000d024407140c00161403e5a00d420014804540c8880015507050340903c1c025200e922f02c89100740d540b54101104030340250070813042281c2a074058000b103085501c2d85034100f02401e070405203682da0305030611090f80c1040d480404900001c0c1d512004607030004181c01c240349025503d035039420301180341380983e4460350404038100103040d50000c42d80d5045003803200203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 125331106 1250 125329856 125329859
    0xb0301140a230c071707050102043213150e040614190c05070602341113090203030c030403060b040e1b0118080f0c0103110301060513030c030f05011401 67
    0x3240b00c2c0064200d050700c04000c83c9071003c00640b0001c0c07072520310031007941507210b80d07940c90b0040c043c0d04079004400b03c9507021400c24001c01c290405581440c3c1413120510140d4083d541440b50701030044036250640341c2c980001ca0540a030900343c3e1002401400100f40591920f424218215502d56113030030341e4656403009108582049141000d601d00c1502c07000150400c145009840c14401c20000420190001c645455100751294409161000840114400c03403801d4401c00824503032220700900a21080c01c501e0951706010100a201001d0500001021903603900064a1900030070b40403501580001005c0c41008158010040c01d908169000d12a038041041c031147c88400c0780390015023042240e554a030460b803060310149240d00d0000055000c0a861300211a01c0301c0480b480048130344204e5503000320b0386d4828880c10480d26055103d00e802c40e402c0c8841182e160b88000080700c8011265000400410b0151100717500440c468444038144003203501d4600c0c00c2d1030201207825600b0740b403c0d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 125332356 1250 125331106 125331161
    0x20307050d0c170a0909050c070201091e0314010b030a0f1106070209060103020703122c0304060816030603051b01120b0306010b0d02040305010e07061101050601050901120b0301140a 80
    0x100c4000c0f0b1040c0d90326900d07451010301c2243c0c03103a40d40d4049214036041c9006c0c00b0300d006100005009070341c001c0e40ca00800e0f42d100c06503c04448440019402c2d02146110308001041d18102c0880322001c90720001f045602c0400002841c1484001d000d07a98602030508480c00c1000c2a03e004a0302041507036510300709840e5800180100340028100d9040c15000105801094440d0251950000e5000c0041000d018480c40c500c0e20b440303440745800300040902c040782e403000d50000160340840c2e4041e5a85002c958038903202408240c01103101070181500c03503901100161041c17042800c203011450004503085440c0d00014600d5425454a2310100d1401400d00d101ea14042411415181000d283c0c9988291450507003000b440b1b5680040c205520b006402c0400240106130f1904851040e40e481860b034840c928040d08079070044c1d402c1c07400b00381d04210b482400d50283e500b89220300c83c0000300207a40500c403400f207400d5070881491400000381c00703001c000302207100d4412500049611030540c10210038996 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 125333606 1250 125332356 125332373
    0xe06100807060e03070e040f0f080405011209020303041203020709020c06070905060702010e1c020301020c0f1203010608070e01030e0d08070f1b0b06030304030f060902130513060f02040510020307050d0c 89
    0x900c0c1b04a07441c910010342481103003180c883c0d08903480700d03000c0040b1030181000205070b002402400e000510200e00580dc0c07095078000d00e894503800502131841c7c01d00d040042d84021104a1084040d03000303001c070004103486c4d20300c0604414810040a8620f900c1c150070001d00c901a1500301c1c074402d41c0107000c60710150340c0c0b01340e02c1c9a0060082c0e928104c008a4506116903180740d03003400940c10b40c00040c1000d800e650104124807000c8488040707845c00700040d4080c0000380405d00071580002c001d103001489040c89050668040700060400145807410071913018189581e04560f01d0100342400180014150302c280002d125100302e1400072114122071044092100e240c11024019001c28404034065540c1801103c0c0159802958600d8500441c07600c440078251852060340300c0d00305070100401000f25809058452a60314410255060700d07a41c2c0c010040c0007030700700c103500b00340e0034003000c141600c0c0c66104114055407500259241c0d407003490700506e096100c554500c100114035201c40d00150107a03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 125334856 1250 125333606 125333609
    0x110d03050c0c030c0f061302030a060c030b0a0e06090f1b0903070918060501080706050406030c0c0209070e130b03032502040203010902040905060906060307030f0e06100807060e0307 80
    0x519000c00c035900c811082060a00031810540264000041d084229981c0060f00b0040c500311441900d0140c0d80b1242001481c1c5609040a50150060325100340041d03035030f50202c894000386050014000d203404000c03914503001508003098090294007403091901d000c000c2103a00219102d02a64180780c5000d4294584040881d07a001c0c0f030354046800c0c1c0e00c07030f607003440b8010140410000030083e0781985903e459074031100c150155412498000003107400d10b00441e0f224140c5225480b490b00c0e10b450300100710018940c120001040010841074840140e032900c80c2940500080da40340000c14444004200c801640c0080d1449401d00e0803c08100c55140481a0b038030f6070020f03100021001e491075589506095806800070b501510010020031280407560160003070301c02e10308081080350388207001d020034002e0981d20144d1000302800090106031082d00407941e402c0c1c4548020409502c01080c40380703007420640e403001117400f0050040c84805400c02040300145094034100c0001464000401c5c0c450100b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 125336106 1250 125334856 125334883
    0x905030d0b06070b090303010620150601180b030601020d080f040f0309090c081608040b01090b03101a0108130309060804033011070308060d03030b060a02010e07050111 74
    0x1250a001c40a41d5050141c0d4849038100034103200a00d010340380b064981d4400d02401f0040b414a501d082440c900008011001d001c0c0d00000b81f0080703201d021981400c007c000c4c20241003200d034040c9061480d850780b0014000384110b0007a81d0300c81c01c1000029060031030b580003e800f048440420000c0310311009070031517006500080c1c000f8203694141000c8400902c180c10914015081a001e1191103a000c18005c0c8611700c95134070149182c0408800300c2c0c03200001e64002d841e03000c1c510010321030001c07a6840b040407980003c00315102d0300da001050710160b40321284600308455400c40d650320700b560032182c02c2c0c1e440b0030141c0d90741c054615550b5021305034802c540104000c2000c0200024105070184a102e01403040d800d9400100e020707003c0500d514401008401744005003411460b1041051200c00e9035680d90781f5445540b078964070700c010f1144070002040c0c15820541c40308100303082034a07203c0050031114140d40c0045220b070300d10f012203881c0a8071580101d041040d00d07100b0800d409000301e010807403040e6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 125337356 1250 125336106 125336111
    0x30f030603030c0a0b0105031507020c280303030605090a0c0207030305030408041a03040c080708121e070b0405010501140d03030c180609080c030102160201140d060308090102010f0905030d 83
    0xe448020078610b0240d80f1040c9000e2040c18004c0702407000c0028a903040300d13001c9003202e009902058020890b2030050f103115000d1b0348017810041442ca0709154001c40c11030a0700c801481c01c03a0f200c1200c401c40c1e94680c4190007290740d904c002d020b1070070f001c080c080d130105483c03105100d540280c407402551007540d81300103010808044003003030411454504841c01064244a0340035010410080c894855000340c80c1229500715084000480240110303484003110121360250003140364102c49010b1951207805940461160304011256181b152005803403020b025501303c0b4024903061500c6030131598180c212122081003800040403540d5240301e00c10782c450f4140b4000c180c1042d41300d815544003901100c9400c00100c0e00001003407103544805c905048800910440b44201e044400f85401c034443c2013200b240d100040c010b40d1000d540240941d24254002210b00d03490240380040c82811614030350070480d01000c00144504956909010304040c43c46916010010403160744d076101d80e40d102c0c03421040001c0380c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 125338606 1250 125337356 125337361
    0x112110f030a0605040203010303200604030f120204170c0307210212010f050103060f0b012a030909020a1e020d0c02090a0f02220e010f0e060a08030a0e0f0103020903030f03 76
    0x80c2c41e0303007120004101c054010354407540c5070b15002e8181400314640c0c0703904802c05034401c40140b200041080c001c982680ba09410320024010485085810000201e400794082100140c6110b10303110494125032003a02800c2d202801d40200b5041001c5a0b1040c2c0107034201199002846c042030850703002d245e40c101d0301e203444102d07410b408501411040304c00528041c9000300010501c501500000c401b0140c5400800103100010015a1601512074152565841104080350074511011101513054013078280800d8139070361038000307a05903132110b40340c00c0002c0c40b446540682c2a50748a0011451038250007d4010914520002810039240c240040d20a84c0070101140d40b9071165441800ba10100100a6550b030629415051010920403141074a42c110382c00c0014590740603001d454144c0d030b0424002c1d08014900350320100140b8001d890140d11030000ca40c0020300140402c003d260500d2652516041201240100101095031515075414507004001d18031069501100f282e200701c8443c00010f4494 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 125339856 1250 125338606 125338621
    0x80601110d0302030411090901050f06061c092604051509010c1106040833040f0b04051504150b09070507030813080403050f010f11090f19140112110f03 67
    0xc6c0801504e090304130305e900c01070040c070315010b4102034419203404a65407100c1d01c8010610255204500680e10100300402050031419110b0b0458a0300e24001d150082120b20804070700082c141241141980f031040c0040d041096080c00305088401019000d501400c0061a60011705400226a00200320030074145415071241e8614080c1c40182c5400e40031108401d01410400c00038400c09008603108200e11411a48000301200c1050f1143d0b5000d03850085509141e5180c96101c40080c1044401d03005000c400c0120524841066110f00e006d220072222107841c0384191401c542c040799685004640100800c03c0c610f03008811100b81d59450310f4a0206941c909a000f01c100e600c01c200200444030010b030000c00d00c0000a41440c444c4030742d10081040700030070000c11089a540030038a0600c07031002d02c80c0e49035614003203a5013030380c42202a041d1032540c000d03d10b00d14250440754020941c1d25801200020055900c658a840a981c440e102001140e80b8462904900d00918420900141001001038102d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 125341106 1250 125339856 125339873
    0xf01020708070609080f0304050307121707060903030506040c0516110402030406020403021509010e04110903010c050d0b010810031212020d09062a0522090b01080601110d03020304 79
    0x200651402d98445640300c001c02414040d0034411240c5600c82c103007200e0594540481142c0480340c0040092600b01d140140ca024000d01c4201c0541c0c0801d1412000760340038504200510070140700b408001450005440d010303003240e0b030160079540101c1c0342201a440f09a08a012280501c2c0f03d400320802c901c400c0d160581c036040504d0441e54101e40044140810000f00e60060400d4070700c21140c0b80b8100204c0f50010949000f103001050005901508403c0035050079404900b45010704c0186920f8200400046802d4403c144065000617000055103142403240348a1a501010b00740382450090901450807a4009883c0c00003038081e115485214000c0341c000c0640003100800c103902551290500d14255005150050040d100141408010312141d04841000080380300ba40da483c40546d0a00c0d04210741b95004042c1c44a040242e0280c0e0b03900c41902e17008140001d08181c2000704900c0c040034001881c0500140450f03041c0b14a844c45061072040218001681c0d680901c0c005172259614142201e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 125342356 1250 125341106 125341109
    0x105030603071703030f0c0a090302060f040305060f0103060c020c090c0315030a03090f05060702030a0b100f0b042d0603230a05090d05040f030b0a02070605090609010f02090f0f010207 81
    0x10488074103c00c202c030000000c4080e6124001501010300256150017103200f02d44901c003110303000160311020500c0103150010240c51301030359400445003019160341c0c84a1624800341e45103e01c64240400420800a1a010f00c500340e0015101034116580000041100c40700064003c0c140c0a50210020703e01c059155a9000004c000404a83c44031805040250030003030540140c02140d0704402000c10710b17041607011100591780c00740c01040394410300c5c0c645550915025100040c0011808400078000d6000660702000c1d10b82c200c030007681c45103000b840c02c02100d1410700306a8440c2e80c9120402244a900c0040b10484009007001701c0c2c0030047c40c0b1403072900845030881030244c0000c0000e0100c50030300340d808184504103840c12034600c3c1e1911750050300d1501481c40360011041d00080c080c40000c0411040c0d03900700202c10809030034a0125501e0f80b0a4480c200d50f80b2019602410412182c410309000d4082c509031507103005c514040c60070700420303480c4150704009030103458903c80c40c0e6004c1c1d02c2081180e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 125343606 1250 125342356 125342369
    0x10906020a0c0312050c040509180f010608010b090705120405190c03120e10050f0f0c0d02160302090105010806030a0507090b1011030a03090f080a0810080d020c010503060307 77
    0x40d520004068042c1c5090002d8805500243d440b612803a00404980305803402001003c0c41325050500c1c01c0301f00440c6940040502445140501c2d50000032841004521318200420001281003400d000b8083d00b103c2c03405008520540d00e540510807480c1d001403c81384031034445104e11344681d486007442440c1c85801c8a80310300c007002c4050207605001454421100740c84c854807184543300c511150444201022640407a840b0f090140d5444425000d000101900d030808112a13003011a034001d198007a42164003c5041c1c2d401c420041c250300c03603040c0301e48803e0034a004045807000e8155004180311450501465051283c04008130340fa994082124014156100e4111550b4a8481c116540034040342003c09008001040c540c0038400e004018620700041880000e5040c000d6007030040f000f51411210969007848201c4000c808075011100030280c0441d5621354411601f00313403040c0395200f60154042c0500c0e030030107100f503c56180d01040403c07600c0b40910b0190340300e0b21540c0000b400c00a4170381c0000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 125344856 1250 125343606 125343611
    0x20307080f1207020303040b0f13020a0f0801050907080304140604120f110301020708030f0402011103130e0106030c0c170d09060504020f01050c1c020a0606060e03010f0b180405010906 81
    0x22480703002224018007404042c2c14109495855031101a40d59004c1900c00400c200010000102d10180710680c850740503548116017020500c564010450309002d40e0080140160300d140c050041c1c0e80240201a044085000141a1540340c084403039160b0065004d0f0318070014440c41d00d08403e41c1d440043c0c034013031300101301c43c0020722030185005641c00e00e03017910446001842c40c503d03440c1c600e018800d6814554100a20601d0340d44d50701e40c1c0c0c607501c001c010822814004040008280c60204002408039070b000114020400b60800d03d60850142c0140d101c0c80c00c05041100c0910700300e038080c2114500300c0c2e00005844881c2d1039007018800074081d6144000d0320528092070350090142c26007149006074020764400703c1500f000300044600d031180c514a0801a801070707001d20f04040381000804165141481912441c44540c0d036018291101503000e030001031742410030402c00b46030070b101e00b03816043c4140703040110f4188180411940c00402c503100100102450028003440344c03e400a060b42e590000e0304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 125346106 1250 125344856 125344867
    0x909030a050c1617010e07060c0807020d0515100f06050f1303050f010b0a090516051c0203040b160903051209040905010509070f0e07020a020f0103090203070e01090f060e1602030708 80
    0x1c80200001c08a030004c0641c00e14400301e61860000c101103080c0c031590390300d51001c1c1e0001d807190781455111a900326080098440c0d403001045042c4001c8090b24121308002034141849829001107401c0d681100c01c07249005102000400c0e0000121084940c0d860302140e21101c8070700940394a401242d00c084d1040c061002603010b86a81980550420042214004103954030703460b502040318030403541a20b12900c01202c140682c3c2c0901c024101c0d0505044c1180b00c11130755100403905a07002520210b61009126060140c540012b10038913401400c6840c3c09046a0f20b1741d12456a5a81c401c1120000800e000075002e40c15100d40d08800940b0381c01100901013824800c0c840ca1780c2e8180c51145c0e07801c01c50517400119010394001202400b50140d58001c060310119a020451482c20403035206051617514881c140041e2024883c55000341450744507050550301d00002c00098910340d0703140c00c03001c81c0b07001030911403400d205c03a502d90000e0010401d4644002d80c040c1c2a45588100c070340251003218003044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 125347356 1250 125346106 125346119
    0xb040e040209060d02420901030e030f0c03040306050105061206042715050c18010305151f020c03070302010c08160c0816050103050c0306090402040b060a0e0306060909030a050c16 79
    0x32001214003040341c02c81402c82a00405101002550f100210f1b401001560f000c1c0d88a50010940014148141c92401d6180450500503900008540bc0705070001700b01001403003800e1180d103006001c1910641c1c83d01400c00f80c50004c000004003040d1040d40e4030300700e055004042d8100302403103418400042e041c0049070b0a0040030020044c0030082c019041c14009928840800b00b034420b0030018504200400340e03000015030140c50001d01610100755201202200340d41c03480100303d0521551140300e080d208056030003c2c20018180c00e8507003e6413054000b040144d9110303e0031031120307800034001034503056040803050180303942110140012401060110352031401182858040d1315a114460050f42d45030010740c01e90304101c503030900840e400e01c0021140c0c148007203801d501900c01417000071040705850000d800c540005140c400042e00144d1075408a040412000d03401a1040320440120318107400745ea0b94901c0341c6040e510410a010034103c2c01c515040205090343e4020609590407aa19980c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 125348606 1250 125347356 125347399
    0x927010f061a0403051b0114071505061f031107142515080a0905030c070905060609101d15030601020d0e01120b0619050909010b040e040209060d02 65
    0x10608242c507414042106200101d0032a000c032a840b03000380c8000380c18945205040080b0903102818040d400c4030b04411001188000d0112600c40c08a03030f509259181660021660000c0c080d034010310002c005c080141c04410402550800e0f02c1c03034040741200c1c0c5540c1066040c021518002c15100980503100303200c00c000b003034100d0200f40304588051940c0f2041c00d15030003151903108220100b4410400ea0808034420100380f03034810070000d00480d8103121607940741e10710781c0407050100490700300e42c4091100b00f9144c00359031307000350f011a0198203040c00240007500824210840301e040c00245640c10716190954004850004401891659150180d50201c0066441103c08a0040c000c09909481c101c4c0140450700d4400c9041e074800343c2841d1512034aa0003041c0003070749079500c082c09025081440d010f480092561000f83d1b95941c1d16100304000b401032081d41078101c04034000c0c091000340a0041a22f00d40c40e0f205404580c14507007600e03204e01003030224985c01c002175086000d50b0703403040c2005e0b61007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 125349856 1250 125348606 125348609
    0x2316080d1407081006030c020a0b040804090e0c0a06050702011103030702030702090703050906041104110c0307110307060509090c0f27030a0215030703140a06230927010f06 76
    0x411180d038540d521003080f00c194104486010041180544c20f03c00e00380f290b8451b050500c000d0045035043c410a49403140b0b44170301194104c800da1300004041c004050720b0300405064803605001400722401c11000a80049541c1c05140100040032541100750380c81a0103682181507410b050341d07a83e0400c0300e0025180e03401403100703034098160040810380342c41c42445094440c404150240020351600e584015a0702e8260140b01da02c1600c40c0c01e407100100350706c001400401400d10095541c2c10755450406141011218030034408d8119050030440070340c22000722480141c0880328540a6510b5800020850007414000302d112500443c40782c0c803001d0100c1200b86440340950a02d1b80c00024032042554070001904000d4220216405045450b55504040e48c0c2055842c1400300702c00581061403803002c0c8041b00c220140c5a00d074402044003070898036065000401c44400d08000201c00e0300800c0d001000502440e60480c0c1090401d42c100345244080704060458000900055640307144803009001e45 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 125351106 1250 125349856 125349881
    0x1e010504020a0b0c0a021e060a1d0901030c09020723010504021207120602030402030304050409030203121e01030206070f06062d03030e06030709030b180d2316080d 72
    0x11050003103100407050b000e84a01e0013110006154010945e800d02041c800203190070f40100104801c07950803543c60300007501d800820350703130b505068503407641801244c660385080c0903018810440c010301c00314400d07803007801c180c610084025940707a06c20701d011024101940c20880507080d60081005503040d040d00300c0740c01785000716020404601c3c051f0800e42c5561051284804402a5606101c00a07800341c01850b445400181a02e0609070303a40041015550f0304041140181c10000b000381c1200f560380481c68100c4241040c101900c0c1940010f40c070b00010601001e071182c00d0124002e0201b10800c400055107681c08041404001d41e1483e080d89200c41402e05100400d29601c488080104107032442000c50b0b815645d085052117140f8184080c551001d4850390030007907100e00100c0401c4246030144d0040101d09131000268603e08a150f007003001400030b49040080e90780c84140d4083c2d00c1071000290007600d000385965003070690700c0086c030114130501c014281e240c0403901c6c140d010741c41c0e1300c1344009156 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 125352356 1250 125351106 125351119
    0x3120f090114070e010e0406080102190804030c141e01021815030604020304080c1c1205060a0b18130c020c030a08070615050415140d051507021e01050402 68
    0x11080456800d9034080802918504803140010383d50a00c5001031000f0080c06060000070010410007140591309141c01c14070349a0740014400c407402c021040c0702c0c241b940341490301c0441800c003541d0081c0011445a40603101242030403901d80480c8062100114180c05a001080c036850f200740164040c1d040303a8845d03c2d60001a00c1d01c850507040c00c0d20013140a20070300c40300b02e1030342d65203404001c000d40020b002076600b44014030075032074482030402c11400101f4a034000c140d809826040000c00c4004041e07200380c030f002e00f41018404907403110203107401550445420750351600400c103811801e00038036451041d40140703d03880800c0c03103c140f644070846d1188a0b50039102c800c0c00500c00e042c0d6075594040010940f080402c00480401c10381e42c0045510060100c500c44480e40e41c00000c1c0980b04a000380400c04455800c00b004165070070203101648080503150030114051545540fa280c01c10307003036001d007002d0340b010014005600c03e11883d80c00103620045070440104240120b8000c0c10126000c074081c0a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 125353606 1250 125352356 125352361
    0x24090506090d030c05390106091d10111912060f050901140109050d03180501020106120206070204110403030816020c0a150c0803150306011a0703180803120f 69
    0xe200307004603428000580c450a180092242c06d240054448500c8502d408041c81e100c117880c2514181c1c4030050100b5a4004a8031604014000c82124881400b9880980300d0350700e810841d14003c07401103070003e41040300140940501c414054907124008074040e041b80405200c1007030780d8202c2020380c4000b200d11000c100240d02d500c41000f1000280c02041c1c0c1c030401c5000100400e55100700d042d8500c10301231400000460741c1e40c0114030603030b00710300e4120081001240c1071020b2020403503148000f48001d10080c00894940000c0903101d001c00c12029004540015000c1e041d0b423100e80000090341e00c01140720781e0301c0d030352410001d203c240c080da0880d01044200321401c8483d4400200b10511240003000c5a26a03450315100a540c0c105103e00b4100f8010030080c604081000710b4003440c0304981211825105002082c101424079005801050000c000340700c0e01075543c1c2c134007015a8215545424216010001e840d41e02d86001c10075801205a807000183e40800315244060392409a05a00403442c1241c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 125354856 1250 125353606 125353633
    0x2b0903030b0f03250b0d020304120801031104020d150e0712050c0306060706181b05090c04090509070e0403121103240f0a030b0103051603050303042409050609 70
    0xe49006600c0c66065011044050700040d0035a06070b908003504c81e001000145d1380c2d901800c101e070400c00691190540c044204030611501d00c13070380d4000703554519100c3c0b115815951000c0d00d2081c0400030354051640400c05410420640c2c1c8606690350405003110101c698030440c0c040c0020086031114001414094a0300c404c214034020301d400b50103822080e0b4112341d20380e0b080c4500d035048001d041d1a402d40310118503a05803042c200790b0f12024080c542071582c100134640c1800b00d407004c80e40814040c5d4003c2c4108810100441c090f601912075400c00418070792107503e1410320702003494110508071040392040c0010586c210b0403440342444418028441245000c904181c0e030300044965094043c003801e02c8020714000362501c460381070402450f100c00202014049824203000b600200d4160380400d006205000082084034043c94403540fa0f031000c50f06641d1541e0f1a0300018000504d03116080743c0f590141d40300300321107c0341c0240f054001c10096516044c11070b5190001d892442071400740380124000c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 125356106 1250 125354856 125354869
    0x12041b0b07050613020406030b1302040507050a0e040c09030b072705211e070e060a08030a14040509130b0f060a0e090309091006110109020112022b0903030b 69
    0x500c1e411001400103075a800d41311030b00c1498140d43c200da009030381c0c5401000003082d00400b90b004880c90003c01c50303101c3e50f07072040c041282d402505d05400c1c400240032a030492680a43c2002d04036506480c0842c045d00045401e5680c80c40f15000207040c1d01e1080100304800307130311810685040c400301582c0c10b0f021842001e52003400b40c05019094019241d0241e1880044289006110103c0c082c2d04407440c4903142c101c200984010025540c80390f40040d03100b04040c81d115420700d41c002c0d8084400a02d5140fa02a03030990f203120f105403c005104643d446001c045070030006035001003202070500e04251a140600461a002c0401d00300c0c1c3c680c070b5000100b4010b40300f80321150301c510000b6201d080c0090420301d94405007000101010582d1200308501c10158440750100d90044407500482c8000a0a02401a19620700c5c041c21980300d038075000740c03000540c1e40308042c50707465400a40010b0781c5020800c1c060146803850003c2d2265040007400d650030000c0183d00c020b084074000d0343d04014445030042004003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 125357356 1250 125356106 125356117
    0x2107080406060519060e0315070216090608071e09150e0f01050a051c0f030305090d020c06030c0306131109030709090203072d1202010906050703021002030c12041b0b 73
    0x145507444000c1480521b004120300303a20790500a044502428000c1c0240c4d659407000c1300c01000680000c000315021941104803040070306001c45081c000b041c1030040755982c07844244210f80312000c0c0006103070ba03036550b203142c45030240040c910300b0f002c055004c4a40100c40602c03880760405480302500091440f401d902845416620b0040040d01d01900e460304110603506000d10301c1c01054101d805400000d2400b001c600600e51094801164503d04001c1450411400c520303c041990045c014109043e0f66803c22030303501140c0840f07516101d480b070304049442c2205100c5422010751070300c1403903018402044080d15400f0700840880f0009030b00e0748a2841601e03503842d4000c3d090703840a58144403103184a01e803071034a0310018130a86205003101786042031210450340080c4440c055849440c0035035074842d4030240580080c1c1061450043c466900950351048204940b603100d0b404004542800c00f0f18048902044a0740c0440c800b905050825500c4401c0b5400503254001c20242d00048001c5110700303458 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 125358606 1250 125357356 125357389
    0x8071d090f0d0e040f05010e0a0b010c08091311070507090b0f03070302060d02070f0b0406050a02070317040201091d01080601120b01060e1c0b06041104080703020621070804060605 79
    0x1500c00d880c888262803411610394904c0d84152110310107070b54003005200303150090880c0d00781340b0918281008000c04440c14400b1450410100180800200d2030403030403200001c07000d0722020305010f0400d490900800e1507128440b210f91000449200340140041c074001038411450042000c1c2e001a001c0200c100d40c0c440c460f94054000c10001c002624160001d0603d8804880c3c0c094609a084d0f1345d000ca014a513000120394011418061006000881c0715195124081003400c500d0042e1070784002d0100c4030313400449000e0000303404c001400c5900c80d54207903000b4400102c50300c2d19407108951740790744020240182c84040c414540001584140900c0c05c8032082d4000461181e070b6401e10b80111003080c40700600f942c00c50070301400004008140404e41380400d02841c1500401d04040c42004180c961000001803000b0041c0400c0c00603034404203954040b60380c1240c800d960b61248072094401e229400366503030302940302e200801100c19002107030f4501c12072048600b0000503031104200031a01040100c030301d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 125359712 1106 125358606 125358613
    0xc21010501120506060303040b03040b060f03060903120c030403051c060506040b0705010c140a110a02030f010912050403120305041b08031e190c03050408071d090f 72
    0x84e0b41006040f07001d103140a00c0e00c1180001c030702020788064280300b10880403c4141d41c2d8a6102001c102014041e64028a4900f038041d8a94106001c005c0503461207900180341301e0600340440388a540e1645810381000c101451200c400c2e070b0300c030440d91005075591901143c02e03940c41025200a10400c403031566200a103240080c2510801d114034814000c40b2000c182d0503500240c242c4090140034680b0700c1e200c20740084020300d0928601c4000c0e4250003045400081040190001c40415010760100400c200c41c40c0ca00700c80070301c84d501c0060140d1480ea042102050300c00d400442d009401200a2103040c042c0f0150f0030504455544500c480d6480010501e04a481c60f441803402c03403034440c40761420004070555003a0b030300c60400c40081c2009403032000d000401d0700850981d0044c20030f150444000035200c01c030b1031907410b030021000c214000d01600001c1544100250400801c08841c014 = true := by decide +kernel

theorem cover : BRFrame.Cov 125179856 125359712 := by
  have h0 := BRFrame.cov_init 125179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 125179856 ≤ n) (h2 : n < 125359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
