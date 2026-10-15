-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4211
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:53:36.084356+00:00
-- url     : https://prove2.me/submissions/bd012b9d-f303-4985-8c12-7302a8bd7c36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 757194244 ≤ n < 757374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 757195494 1250 757194244 757194257
    0x50918060f010612060b160f14070f08030306060712030905100b030615030c010f0207120f03111606050c01020d0e0705030712050c10020a0819110312010303030f0f020d05090607 78
    0x401c8028003e031900411f00113406a280591818001c4841003202009030031401e401c609109600c02c0000e00c0c00854146a0031000416075840c01c0c10349074082100c602e60004c00801c5842e0000b440500003000300078490400140300c051a4641d94070f42450310020086455441c003e455481c64208160342d0300c45034170600c0d000440134090210752101c640040d00b60520007024442e5000c0da00a00810b0060004045a954111807030300b03002c051611410404c0c1c01180e2088603200c00c0d41004114907074a0003403800c4040c8001c0c80c00b00c0446036503100b00100b980d503550070701551420740c59a0040b90b62007006c1000404504d030030002014209100c50340407500d080c09040c0a4000984042040b40c101101110032910103100090243c3c20268046002014507070000344410300200120b1a40d14022015600c400e415010090302c0d0b03641e40b240303d2400107486034000040001030b1081c0c004010000f1100c10108809458120203404e9070007104081032055114030800c506520100500c0c1d84c421030625042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 757196744 1250 757195494 757195499
    0x50a050628050f0d02031213060206100b0d1e0f0c052a0a020907080f060a06080a110c0330131e0212010903021015050918060f01061206 60
    0x6081070100c0d885034601401a00c0880742c80790b611080740302100307900039042c3d401d2000d40741003403511680a044490403043c03c07000c01203161440020300a21580e00f40080d42041d90401800b401c09030484c01118903500d48071142200c4002c070140840c1d001c040308041c003240c1d1042c010161010355601410100800c501071000c40405042445450402d6139000700000b040c0c0141c00c01d550038a003a52a0280d00a0040401d101604d58005002c620a19114217460000e4030f840040209200141c81000005940d610116030940300310b6000d9460f01440d02d51183c54a40c0d017400d90b609640000020004c0f100c0100f148034442620448400d8103038100501c004c2c101d280c51900034684500200018081c4050f031005040c0c00410310702c0b42d4403026002000100125480b2044d2406083d06c0c010803801405906030544240a181c014090810b02600d980d05d0180d0821003813145000c5c004006c4082c0c0304407800c00c000c4500c01031084a000e5408510b040e84036604104014200f11000c6100210b42840c00108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 757197994 1250 757196744 757196809
    0x20f0a08030a091a041202030a0204020f04030b010b0406050702040209031608030705060a020717070501020904021206010f020f2e0606090e1b03010b030432190b01050d080409050a0506 81
    0x446051b1404042c60120b40341e050300100341380128846000b500144001450081340c044007001d013044910881c00400b6030380c0c0700c0d40560514082e038410713a00411001c0c000c1c0300040c43e1039005001800e070b01400302c0d00c1d01800c0c001160703803000b010340c0040c0710f907040001c00005003e014401207500001e170b6041589485921b50707800d011450036032054440002c0c0442d070001003010a40448100500c0104150740314801c0350060440c290381030b10784c01e0208034036001b009c07078090010521844401c070380005000c0c944540d03081b01c0358000104c075000400d0340b2103100c06d900c1e444d0349100d190003030802542c5984503a4201260401c1c01035000d002c214652a42d698421281c0000c0b00032641941c3c0940e90850300c2e40c4982c0380c8200c0d5180c8099035044004014a00c003995400c03541203c4183c403d612081b03032244190bc0c0d81465020404d028080c1080e142800140194144943e10106407445854150f02c6e10b541c076001c400c02c448041c1e4101c5140c0f5100c0040c0a901c5c94a4690004119001030a82c4040e011a009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 757199244 1250 757197994 757197997
    0x509011d0306190c1805040504030915410d02120901020901080603070b0f18030d021c050702060d0c020a02030d080108150c1b070b0409150b0c100504020f0a08030a091a 74
    0x940c47c0700d143c980e0f001808041c0b1444c0660010008420a21440f00410780c024021601001c8210380142c14020000b4000e105600ca145245606450100820785403074120a415440158405c100c0d5808000701a10204200c2802e4440c4024030001611040718030001000c0c100040c0040d07100ba03015030020f000070f024200c100d4102c148074111059441c145440e801c003050950261190740b42c0a03403500c1201b080d07004110346441d24000000704950103c0d0303440595441c0904040030350080802e001111505a05501c51010b010a500440b034400d0150750004c0d2801201400990003d0030304d000400548200300110000307200b85084040f00c8d0b141c0f0242c60318550080103192943c50094443c0c0c40350801d014030048002d442c403203002541e555200c044210281002d42e050103d9103011000c005498500d4000340c801c2904900d0140c07018100f000c01180107418081c00603640802e280e000d020003540c1da40c0d6035000a0081038043c5440710901b00380949109155031207261140d0f00200c0d603050100c0c2050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 757200494 1250 757199244 757199249
    0x2090a09030c02090916080d1b050c151b0a02180402010c060c0302220b090918010c09050f03060105030613030210062402010204060509011d0306190c18 67
    0x8000080d21140380c2011100d0361607400010350813490090500080c1318001c0b030300d183d00b0710400710084c0031940c0c0d4400c41c81d40c1d440d64441240c0000e026188010f4074800d240b00103072105010b90115801c1b445c480d00020040342860440c0d0820083c002a02a01c44800c10424180083d007200501908480364000c1000c4800007661b0500250711034001908581c0a6410740c01d40719000312040203c41d82082003d4000d500024008000540d0035489000f02450491400162110040c0b4181054181400d1019446003e001c07006980700b4145c240080d02e0092113008a08405a510481098078040c01d0042d100c04401a86020350040c0b0300520403510005885500312541041001101c4182c1c00d08908080e000d002200f95982407074400114907500c1184280c0100c0001900c0e0210301920a0903400c0744207074440c80001c03410a1010030240d601a01584442545251440da101c021460009050280c112601c280058003440d80c41d100e0466440303004800c1c081410b010440b030f4606003000d840c100051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 757201744 1250 757200494 757200511
    0xc03040602070f05011d042a0e0604031505061302070b0a0b12060c1606050a140c030912030c0910032f0417150f061e0d02010f0513090504020a060503040209 69
    0xc80406150321f6580c02420304d0310301c0400400c4001c400164a4510b20b002500580c0016038201030b0f0313501c0d442d2042c216001c59502044050469070b0051140014040090015909c28103004130061054040d0004000d40d5100e0500f175000c03403a04400420031a0b00303d000050040c040a44002d2010070000341c11034001e01001011034840d860010340c50440f0740c042170010001030509092101720007690708a919490101050580396550381003e108503808110f4041c40c85034800c1c140340c3d0000c9600700007950441201c00080c0c3c54024407230082207200c0600840000005c0d61004403241c1244601901c004a5444002c1501c9051000c84210a640514021481074051000e02c00205942c00c122083c1602800d0020100a01d050b25142c40111000c40e05980558094144420342a04401c0c0b40e0002c014014052106040240c00448000a90801000500c402000091860380e03200403020010204440d000c030381e500d003510502960051917400701d01070200070f0041c00016650030f0320855114805 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 757202994 1250 757201744 757201787
    0x6170a020111010204170a0c090c05040e060102030706021c050a1802040b0f041e05060f1008060a081608010b09070c0308040615060305090c150405040e010e01020c03040602070f0501 80
    0x248803202d40288141e501402c0c111290003441e1510040101c0d4031441d99008548280d6550b9840e0b00c14015500b03110217020004208100034000c11021100b4039420901c18070490b414000c15030b8404049134840428450b030302c04444008282211140500395100d0540740041c003882d410703004c150303004c02043c00009201e00e8903580882e134a61120420ba045a00340104148000650b640c0d0030184807c0745d02c039184201c1d062900040f001d0504e214281310307009019001510b031090387c2108440003e809400c03554003264070380001400440c10802910300158900b000c000451074451190b0031200c0e0030f00307094010320901c005c00000640081048060a40500b0f0001c1d040da03a914240000300020b0070810603180780484041044c0e941980064421301300380c02100c070a00d883c2010414980540b80c0d608242e00000c002c10322142c03d20340c0020100503c090f0011809540c0341a0490036600501000441039102140800c01e00760304019a100034015401604c800b1420940000c0140c840c00009d01052480d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 757204244 1250 757202994 757203017
    0x90c010c0506190f1a13051603090201050903070611071706010618090e10060b070b220b0f044404120308060a050102010216060b01030905060109020d06170a0201 71
    0x2041d008a460369100030000c100c41610b25000700301100c16440700078051051803d80c1a440d154511609008c2c6030341d03043c0c0c000e83c000306110860103003050307003422810864248003008658030100180e401500075600c0307568040303501008051800c03d990748058510508400800f100480100312181500e04c24503001c40003000c00f140b040017114031035011401c824075180c0c0c100c101500205902a81160820061100c10b44e204018100d03401003007005040c051900c0080382021080c00b51000b15082c1c01700301501c15031941d40742c00540ca2001c4880c1510314030040e041108016038020a441160982440c0f09140240358403078404082c0056061840f418032405014400080c07079041d6401000e102110200d001e126240017172070300c40c05599007405030841031008101ca40c018000d440200080d251440300c810041d4a030f007409040c641250364185a950b054040104505010007800380c0700900015036501c040c13a18210071208680d01210900c203103d0103204034184040b070809012038091804078040c95 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 757205494 1250 757204244 757204291
    0x11505300318010c03020d030504020f0d060603060e280203030403080c0c041b0f05130801050103030809060702122d03010f03030201061e0506160515090c010c0506 72
    0x29121541084220000c0010452000000010009203203840c03080c40780152000011348034001c0070b0704000c025030400742620031080d11aa000c0e0354880d0008145c10800540240405d054161800098403884d845050a0051100a0046004041090000301201d1001c0c1d100c210808815070300c940c000d583d45c51000000e542d410000d8402464110000c42e40c0c2d8015007980c580c0d03c1340d2016200d400742d410300c140f00b906031042280355030300288141c541003080500008101c550341c0c00046000d240903810303240400c151100748212400381d4840d8070703035811508003510294505040240403c0441d44114031604d80c848909003902c4022005e042d1685489282090148950121091042041c1008400000c040e41c00713142d44800c80740170350001c01616442d9407044500e05203112440901000505003000f032403c000004002103610852410112a5142d940390704108045c0c038180c028429003028029440d10511038a0305011003402d04401300d0344641c0e10b1030303200e2000030080418000c40182010070707030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 757206744 1250 757205494 757205539
    0x1406030c0f030a091a010315021c0c0c03080a06060f08041a0f07091d0402101725020616031505190305060c13090203220b0117011505 59
    0x680c0540300c01c684038549100c04900401c2c00c40310580d0503080c0703142602e00c00e101c4041e50320b041e246c2024000c030070032100c12400c102135031145108001824a0114a1300b54021920414000c940140c2d6190f0429529081c001c0c5001c030064880480a403030144101b000903003003c01d14200740c0d41410071134141c1e9110b05054022803080c80903044208100c0b000c00050211900c0c000b80f0500c02500c4554059490701c4448010004011a540040181401180140c5801041401c4001a074608400d88188980003140c400c0c00c1901d4072074054815480c1070040203030104041c00ea8803200d01c01882e0500e4141d0300190304039104d004500c107055851820115082c484d02c131000280c1400707803c0492124001e030841e42d617500d080c8015201c5003d0040401c11101c0e055048480824148001451241c1000c40550095001500700049107000c400409600c2c5131454a4842240c083c6404406961520801d4502110442240041a454055080307041c400100c18441902c0d41500c0b0000c00034210001c00014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 757207994 1250 757206744 757206757
    0x10806120102070606081902011d0307170708190302150a0e010e1e010e0a08180a0b0c0601050109121b050315090c0d0213050901090210020c09060a1406030c 69
    0x341d50000500c44241300743c580100045507644002c440c0d4100303000300d02540601c0c0c1b9500c02400205401401c4e0000030b914111202e420100030f0607a0b50b41982d6178461042200d051028030880d4010181c20805140c051100c640d0080213489140c01e144c03138564000703498136450010041c001d41c00d07102003070901c00c0300d50060341d040c00090000c010605200004075529918590000030300342d0041204501500107010300880000c3d204010071030b40c580c030359883d0081d030801e00c0f900420f001c110040c2c680d95903903540404002c0207296620383d910b2105e841c0301d03400d10740c0503082281402400407042061481101620700c04940004c2682c0c0b4091349440c01d9100034156500440d031503c074860781000e041c04000b070201c0c060301c1590207d41d43c4165a03018851681d051034070113580040710000e400b04d03050854200542c0104138400000b02d1440c0755001803040c0c0d065203004001070740710b0209003915082040b0815003080f42201c5203107086140429407005d90746c51403500d50003900c0204c082054444908240c845 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 757209244 1250 757207994 757208029
    0x90308180c03030412021207060207030b0702030d06120204241203030f111b2a012607090b0f0d020a090e0406091104090c06030e21090f0618010806 65
    0x2940c81e507035414044a55032510741a032159107c9100c00b8100c4a0014901040715001c0d0090090720745141c440084980d0b005290784151302040002511104052207668054074a00030f9000c0300380024014030003125800254240d0820b0b04034508460301c200100c440c011160440c1c2500c68034030440c1b9046000e030425601e800304179400c20b00070700c6640704c4030005000700d0021241204c68000071403100540d0740d034421a61031203a0142c0b0700c1e00b06c07141e020b25000a00d03071003040c18855029180c40c058400a20f28000704502d900405500740803160342e00110503402006890070040c20b202004039191840d20039040d40e42d01859000420318919402400c1c51307401481402941d0150745010308241c00540101c5c10100c503031880e401a100d155181610800701d0f042e0304881014074039030134076009800400c03440c0d180352094070031080601002c50061801180303c0c02d403140e18685614100301417190450940131354a2140c1010711030b6001d041c1c3e44900d42c00f640c0030240380039407481d00c41102041c0340d0780c02075a5805 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 757210494 1250 757209244 757209247
    0xa0302041d280212011203031b0e060f04032406050a08070b070303110f0a030b04050705120a060803071115040b0706020313060c020a02090c03091b030c060a180801090308180c0303 79
    0x303000811102c6c61a00c00d4041e4406008404440200001011004900740c01080807102007e41e1400c0a1024105040311031035124602130f00d94440c6418111a5003544003d10895000010003280a004010080c841076440d180a1401c100103551a00300c0c034001c7c5950318102080850074540300e9000550800755034507110b99a040c481d19200041e60150fa070341c00110342040301c4400103081ca4803c185c82594a9500c1c503090a00e00b250a03420804082d098592040d2901c40c0465a44000d00040490303a2046403401540c6812006106002c01071654240c5400d806000802013880c0210031034005a40c08a001681c03644c40d07440744841d0350280701016006070320f0240744900c02c0d83c000580400150003102c0c3c0a001755110400b02d0410f01c0304407041030164010f051440b4442c151041c50120b44c03240201a500f1166801c4007040c040e0f048070321040002042544d03040680c240450f03503030024080c607100038004580d5645002c2d1590340060310110700070302e03c030100300c202202c1480000d5980c100241500e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 757211744 1250 757210494 757210499
    0xd060f030302030408010c0512041113050709030b0603070b0702010c05120301030605040b1b0a0c080f12010e180c120a0f050c0f1905060307140a0302041d28021201 72
    0x350343c3e07002402180e101e0f601e44004500507901441c00d4600010052580703c19591316952415020740803d0038083e040200c18111164801081c02035a01c1610070741ea4542c120351960070b11481e0b40402408440c002d404c01c071402d1200707108032800c131400c003602801c0002400a00d8913190349818403040e07951100e03c202000100802400d500960300450103048408a00e071584134503400c240b80e85942c04104040704000d41b410040c001d41e14541c02c0c50040c5607850a1401c0459071001551012450341110001da00043c81465403c924280c0c002003c4000d807880d40540980140d0344848400d020341c1320340c46100e1000e40c5c400c000c10509007000d030f0041816680c81058501103607500070783c1e108684254003114018650341040c5038000000300d100b101c0f05010b07501d0002403100d40e41c000342c00c1c0010400800d80301008802d041d0001c014a02c1c5560380166a280f40c080100c980e0342c141440d503482006100d0a0010f410880c101d0031071320f003a50700440140b03490741408a100a1080c12500b998260501c0b000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 757212994 1250 757211744 757211747
    0x2303090d03021b031c1415120c09040609020127030f14010c180b0a120203060f0a120506010b192708010b030c030109171c060e180706050702060d060f0303 68
    0x54900042d51004184050302c40c0c80e0b15100200c02c107e4004035241499180c0791b005217441c4560b159881c5c00c1805441035a200100404d000d0300040300c0980385a612950075404550348604d070a4102030700c030909192520405134840d8035a065620014010358821030100051250030b00d120009070f201038008019880f01400c5c0a849403404140c503004102482c040024031712a030000b1104c01c17100a0780d41c07000e44100d00130a80025040980b003d50002710709107911009468020310603014cc12440300d101140001840c0262820b81f0507006403e00480c2031203002c2d61030790014851001c40300141010b100e244280d9140c000344031414180c41000b942c8d90440090010b9042d072025403444002d5069540fa14091310034982600d00c10100101010746010700c094250b419480600740d15180d2192407452281c041c18440c0c00c3d586a034004c000b031034170800700b485031440c010340c1ea030720440c500710000d4412149040c01c060107a0144000183c081c9c030000511303401c0801e080c5e10040c043c0540c9088030601544a040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 757214244 1250 757212994 757213027
    0x212090a0906060320040501020d1227050706020c06090405060d02090a0603020a0b030907030314070c0b0a0305090703020a090b010509030307080a12060e060d08070b072303090d03021b03 82
    0x1004045c0120000c607003040900e0403003c40d0155407068008181050041c20304550b006442d8000038000d40d0364001029105041c40c4602c9413001002a28110010305800e00170704100302e6501040a55001940d090b40d0354841d6025642000400ca8002800da5100c10106103518500b000c000d40c81444075007000240b903860750104007a203000742d840b0b0303441c15254911340003640710558881c01d056200000810009200d00340c1c2c91818600d8040e803a0800d02e1903a12800311003030a0700070910003140400c581980992501c5206c2d4803290300001440b40d545150040b4100d501c0c1406001a01500d444520120b41d0285040301c0003044003508aa42e0381110342000c40b01c6401001c4040006444001c07240e60b00001c5018440a840022101d0303d0180c444404010f58201d0500089500a906002c003002003070b034241c00141310348441c0c0c65002018140c1010740000c03601400c80ba1000007c00d105110340c50b2000162201d14455030305006075202514410280000d00c8101c40307558030312002444030403981c442e44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 757215494 1250 757214244 757214261
    0x109050715020c0d2009060904171c051602032b112106091504181505150604030302030405090402010c020307030302070f0b270103060906031103120a0212090a09060603 74
    0x30f0040171005114080195a4100755403407544100b00d840070801103041041c5000d0480104003410345400701c0d6550940041d10365080301d000300780e40c41c0304111281d207188640e065202114400745240c45502100c402d0b12030a168024072600000e12829a4540110b62040441c2c202c04002c00e51a040381580c600d4503900c428099159814148000c6031050804803503080c02010002c0000c206407030040140001043c0480c1c1e29402503040086420200340004275044080a8280011817a0702d8000140b1003858542d001581c001c0400300301c00c10210351f011068038183c840031199986691502c1c001214030300b00300710001c1c3d41070240c9100003040640005204040700c01c402c500100c2203690702d1811105005030012030110410715038030451050601a100029102d0504000842d691603200d040225025a0000c07240c1202e15a410845481c041110036040c08491054500d01101507038001c0d00d80100c42c1310f00203851b2022800080d00d80d20001c404003c0c00706403c0030000580e45400003009800000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 757216744 1250 757215494 757215533
    0x1020f0f0f0f0c03120702041104171b130b0a03062f1e071b0b1803030306010c0b0a0e060c0a1d0634050d08090109050715020c0d 57
    0x1080a201480400f2809652102d8010040c081c03003090201980300c1603100c010201d038000c3e82c030b44420501450200140010300030035603981400644055005140105080b24100e0040c40111040307610b588003008081d00703c0e8880b801087c0c841c072450208a08081c0c41d04010102800c001760007203414030f40001c000d4115031098400c1c83c101c41d409080c490700d2080304440c641c4031241805c050300010b03040c0001c1041d01c1c0300301030104140c1440c184803072800328180c00c07035112500000b504000c01d07012060756080541d070032800b662560910344000b81c5111002c442c005c000c40401d80c000b07030740e02d01c0130751100b20703120049015030f02c680c0740c09540c0034100d074444c1552a02084020b24190344101c04031000703840102c80601142e03d046013481110310603a04d81c2c03958810080c02c0140088194103190612911648a00010f0105010491000d001c15200801c00452030703140c1445c5e14003007440003030000201d03145043d42c9654402d0000c0200c1c24503140d42e5013541c100e80112545e9041000a182d11842040034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 757217994 1250 757216744 757216753
    0x812070914010503011412150118020408070e04080c161a18060d0603051015050306040302060103031232160c06151203031e02090310090201020f0f0f 66
    0x11489404001600259071500141080c0014400b668203a980000000300003800e07a04d0700e81c90421201d02c0e114440c06984411603800d4010080e400141180c3d00d110b051004042d42041c1c149014136549100c20711030340d1204c0c480b42020405021443c411503128074501e5003a1094501160b1982c1c80d06d401e50b10682204505006030300743c3d1408040240d80401c540c80c0644410641810304001060b0040c400171a88035a40f080e00000241c010010620000b1603c0b17404511041031514414260300745078820b5010b904240c04100000303901050a50644e0f0b89410101d801c100b001c241d2100400000c1c0394900d01d82414452580c0e8080d140300702c000d000000c0b08101540350344040c403100851a0306a42e103008514580180000a40103800c040540c41d4110220310740b084d41c5010005820889000640120307035515044a05045401801d0b1803280b140f401c19417414440380c2c013003070340c40031070120207208aa41c5a444104580c824032410043c10a100c1c00c85001c0e000118034240c0b240350741204540716104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 757219244 1250 757217994 757217999
    0x405040816080421051914150901150308120c04030605070215181e010e03040f0f0e072a08030703140a0e062a0307031b090b09060a0c08120709 63
    0x11310110410195922002030008441500083c81e01c5080b200c60413210400e01c200d6001c00038004210300820714034402e040000e142040203590f0700311034144041038070240e510407091012079491012507408101d0b81c00881c02c0345e610070403104000d0143d5080101182d0900003800081c0d0703400110354900c2e24019120081c55112010010013011014600d03064a03000761208501d00d03101d4001032051103201c08004581c01e9801002c60f402c40c0d0064200191a149803141401400e2140407981c02828007480314a0311400e000802402d100e407036440030301407000400f540c5005501c0300d0b00c85c0b050580c0d00c400e085450341130410028003d0304004814a01103160f1000007003180c2a00d0103501c10f140c507044c02520307458484221481c0745800300303130200c500b540d400e4407001a508100c0c030040d44a2281590002100309501c8214104120349024000c104145020180815100f000440c3d00e5040304890b8995076611302c1c40142c41843c25480c0103010103002099940313a807e40f2521051007400103a40c0c101c100368 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 757220494 1250 757219244 757219289
    0x706050a090b06010f020a0503130602210d020c01140702100f0216020108040507210b0a050610030213050411070b22030806040905030a1d0406050f04050408160804 72
    0x416400c0040c2c031000501021480c20f5008250102c4101d1903481941c2204001e83c591030729503417040d03142c1541c2e030801020030840c16505000c48207440d03d4081c9007c0301c148040270b1540f06402069804009590700080380c05040b042580070b240b44001d66040e00d402440c080802035255a60781d4030500403241405040000141c440c400c5880140400c4120a4140840c1d0011a0804001081241c551181603c00706030b620300015011a008038180034900b0321280c0e07140200024101401401c82d0710f06080a2240940d179107800146000040d140040c1c6402005600030041c0c034156102e550400d00c0c102400403400500402400c40c2802041015407a450342c040440ca0880601074040300d1140c0640401c0001e4440e01c1d040f600980000c10101d11300fa2a521140d05590191480760045405c00c032400091010f4940c440314016170888041140c540ba20300400d0040716403008071403155584800103000c010180003549c84c00a000c107084100c5209a00c1c200101e9840b0b8042c484014050540107035200c0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 757221744 1250 757220494 757220501
    0xc050a080f04020414010308091813020d0804090609061e080601060c1a0106050d060602240415020f040303030612080d02090a08062d0402010215070509150706050a 72
    0x10911a40c03444510390740e0465250884801030000c80e8403988958100031100c0003400ca2031301031400390822607a00c0444c003080114030400d20580e21038060503c001c001d0303515910384c2c0004441c2d40690b294447c45075a4503121f81603210f1b5801c0301c8040c0e840d122000c205025194840001e8800c20280c420440e40b104500410312a154440c1c0c60190b4408801405403d12407070000c0c5000d44240ca0018020440003e0266444400d0b001080043d002103481e01011515000300402810140080c040c0751071482c601031407074110700c9000b01030000b407040400c01700044400403c2052003040000c44d00d0741c440d000b9100c0316074043d120941c0080d0074081c001c580100c0c043c030b500d07e01c1a4000a0203140606000d4604003039080105180d85c4070b05000d8000400000a001d054400d103040d00380200550101d060101c1100c0c0448544840400780904000050340c00141004030b00d21000c2c1c50021582d520f9104548601c113000400d81c1009400350388080000940e0040e0400782e104a0060201c1d5445c00d5100045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 757222994 1250 757221744 757221757
    0x60405040b19020403020604060c02010318121b061a1f0f11010212100503010c1d1c0c030c03121806120b21210307180302041a03010c05 60
    0xc900190340850b0103490b9110100c41c0c08140100050306041e62600080c1e025003040d44000701044248428104640e81842101400c1203000410301100455031078156100c1c609000d0002032040d402001e094214020703952500e87e6078003101c01d000901986040012011001c1400c6000d100a0490b445001440410070181501e042c0d640c007085181070041291000c40740c21000310341d035508001c6c883e00400818102449804c3c808480d00c59203260006140c21103400702502010441d502c4201e001c0000d15500e64881c0081c21075141c0c2d040714140324292150032540030020f15801c4040717400400c100040ba12070080b41d01603801c080d18180a400c080c4d03030000c1c3c0e881040b80c000c000d01d0418440e060143d00f1424283d11004400545400c1800100c0c00c1100019544004050940800a5105410040c102d0000c400c00d0690240e16024220038080740030107003556060240c1e01040180c42102040250015a0000c0c800c2c4402140c040e11803c14107840c1070054065402e2004914190340200200d448 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 757224244 1250 757222994 757223003
    0xf0304060e030a0b27100c14040b090607020a080307060903080a0612060f1503050a0228030f02060f0d05060406080607050409020c010e0f07090b0f0a050d1703100e06040504 76
    0x170394942c4c0c030460514080c1480c1c080c044107459100424541c0c00c10001c2240b01d400342c0d0004000745111006040c1145c20300e441010003504001c140103035021a410703905c007000c046c3c0305151505c00c2880020b00c00001074116003c90700c80030075003005000309070b040072005900a450f9940c45443c1c024010013628004e0040301c0b5401c416291800c0091207661064600c0095840b000074528031401c000032595403a40e00590303141c1e2100300300c2000e625000c4c0000030300c0e884400e101305d1311007039034010058024800d1002078a4102142050000d41d00c1d030341c00701c4d4288031a034000350395912000030351b00004140640300b19005610342500400c50100006429005040c2d03071b184c040c245450002c000c4080e42c0411030901c0155200c3d43e50208080e01000395000410a280141c0b0f0994106112001200c000c00300e41441501c0b600c0250840e501d4070465402600c0060300d80f01d0b01d9400300d0070b00207002035901c054840d02c070038000304000c100302202021f082551910b048807000b0f500c6040c00c21050312026203010f803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 757225494 1250 757224244 757224263
    0x40b2d0c09041b0917010b01020604020d05010e0105270105220f0b010b0301170303010b0d020c0c150c010b04050c090409031407060b012c01200f0304060e030a 70
    0x21000005000900000d24004102003100350205002c04440040000d00f080030455200003803290190322901e50f40c009070000b0007000340c4407190b00002c2d0b44a00103000a03000342419131800c814450203410100c0d40e0601e0703000a000d50704103a80031400d1000c803541c45071800310301085881c0a18006004241c000e40112002c0c0b912400380196506c0d410504484c1103e84031118140100040d00d9030801030b00802440a4560301c070340c0742c43e204821814450a4402c0710740c200300014001e0868050958210160010780180c5401030454107a02e0404e80802c01a4070a250704104079040d8081401092409071420081c07180c1c08100e428441558810354200e41202c1060040f50783e1790070310398440b80c0384500a240881d505445007803500040e0f0320480080c0d40c0240c48900300700e01541c0207c0c54000d01621010a810f200c1252210071024003170f85021981000101030b40c503000210140442501c5d2581c41c010382c0d001060f07a100c101c1d0707240d00603c100000300b46298919550fa140106012981a070040c0c45007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 757226744 1250 757225494 757225501
    0x120f070315090501060801020904061a04181e0b030c01030c171e10080618031209010204050418050c01030605090430020604051006080706050c01090506040b2d 70
    0x4019110201c6a100304156030342540000305070240102e030010310044c0001079540311070000340400c1d04d129400041240e0720201207035004003130007005c032030898110489802805c00154100303c042e04a03080e01003621040030072200103505160744410407803e4120122070a2041d040010f4040c1d990401204e808110b100c8215a01c091b440c06820b43e01810001500031600540400044012b0090360b0540c818003038008140310000c0100100c60b048903507507002020a80c51019184d07928803a0103941d12000740e8180208811312403d406a13006400004c1c01400070320381405070356441c0400f0b084107440c28803800c483d83c20a94040d01c5190151030f0b0141c25104941e46907140c0d002d25034014046001c000a1245241940c0d010142040c004030780305602a00c0c0e181407c1c14103500c2d004074851195445481c2050802401c0b0000440d041180e515080294503a1101c103011070050007405030140c914003640c001c0204010580706203a10844007a0880c40060380c002c180d100781e00c1c0c2440740d20302c1c0081108021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 757227994 1250 757226744 757226753
    0x1030501080106180f0f151403030418090c1a0a08060405041e0816080d05090d09120c230907020f0304050105030402301506030a26031005120f0703 65
    0x3103400410580d10121b801c40803c8540004c0340c034410b54108280c500b052050140c10480400940b11b020118011401c05051411071200281621100f030401c50f6a00001c0e0100125400480000d003d203560381c0152a4140c14200001e034001041180020301e858005502c80c80c0c06c0c41114001e54004800c02d00205890b40754003483c3c2c6003410b0595084a01740100082a184e074064418400d20520002d0384991003e120707001a26400b8195101e41d40101400030355040c0d2190200d02118132400503044190740508040c1c11406e0301c3e820a541c100001340284040070721070072810215034010b0b200301c400c17580e80c202c040340c0ba011446008581900100410400c41d03204001440d0060700042c848403581541280b207070055150440d080c04030b01d049008000d00f100041c00780b00c042d5034442110505600d08100000d484a01c07d91000344081c011840688403c11040b07404121801c2c0507110341c0d900d041003c50708012031041d02c200d9125295032003422040580101f40c1c010083c0d1000000e1031200e0031690b9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 757229244 1250 757227994 757228001
    0x31603110a120f0602032802090f04020702150a170405012007050307120e030a150506010507050c100c230d11030912010e03270a0302090703020307050403021e0103050108010618 78
    0x803942003800d07410511064444c01e0104003d42100c1f10001a6200c40c00c030180444281242d5516204da88140b020f140980c40e01e44095520301d2410000a0380c40c401098192030580501d041208080390000c01c00082000543c0300c000e10000b90024140302c40440410780300c03d0300c500100144190018086000090031a900c00410311180303080c8540d0300075079440803c2c500410f0300303800e50340075061b10501488240c1c1c2c1d01c03855030008020300e01145000300135101d09031b4039036800742028000d40c120319070410090701c07950440c3c49260b1300c10180403c5070f41484011041188280c4d040344a80103552010384424024043c1182c0b00070740c900650300f00700e80103082240d0141c0851406c407082d52980490303400c818081c0020011105c004080ca8440ca2004003103800150548000901900c4860005e1015940d0000100d521030128980076a6a82c0c03565003c1311a40520761009401001b500c3c1c1096844d07496400c5100c1508007a038003003015a81c1d40000c2400d0712903501c5498140e064803500c4003608412a007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 757230494 1250 757229244 757229251
    0x5010b0627041b120b01080709050d051908070507080307150903020703060c030c120c02030906070c030f0305030f07080610050d110a08010302010216030c050f031603110a120f060203 80
    0x41c800502c040c0e0024299900c03454280c60200010141c400089448001d40300c0c104e0030a40a00c7c001101c0c0c0f9240e440134040c52554003c080c818502c00e00c03401c0c02c1000401c01001d005400c0c0c400289003000c2d9190a283d1904074800440b4240145440490242c0c000803e4611700ca0700601452110244506480020141c2c1c24048c0c04500640102101040c61402840d00010555500040808102c540100b120b450040301407041410440d07000c0802c3d034000250344001000b25640d43c1c1c2c40ca4180707041c100300682c0b0340c0014480070314a8008014142c101000c2c500c14200d5649144040d5616039040740c106004413412580000b040c441c5806446c8a4000b41400c0441e030600042c1c0041d11611220898100582c0040015000c0c80103208550717041c40030706072400704140f0a000032402c56440c0301e401035950240c030303000701614208180c0307682d020010b00c1c000b100c82100c4144159128100310b6012504440342a02600e40b0103030000e200c0618170308000c0801c0c0c005e44050401d004a50745d8001039400074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 757231744 1250 757230494 757230499
    0x11030c090d020409080a0905030616030b0621041203051009051b0304292202040b0909072303060a091109090f010501240e030f07030f05010b0627 64
    0x7120000068440b0301c50304c00002c1c003c0301d841c0e407036080e9010f0040c440280c580125009400c14024440305030707220300ca151610111814049840d0407120701107120b60088060040d003001844441c800c00000580302c40d030096000702685103811f07045560550a0712003e407101403242c1c00c0706c40108200303044e581c001504042500000f2119070071200c0d0791358040d04183d405841c0303044031800b0b802d0074850034001c0c1d10841040003c02c0c103492802c3c0b1a0032406051890341000410383c3c1e00b035903c085503074540c4403510605005185007018149031b080d90f91344075218020801010b014a01030b180c05004c50003e2524080000c00801c85640d4080701e05c0c0192501c42d404803050b28881c04004c0c81a611583c0d10b074800d01980004096420110508500b03480040c1c1c0107580270501107010091354a42e40340741030080d05440c1071a0b0000c1c41143e01082c42d11544040c20f481d00d006801001c420800241000c10003903006a0090026522000030850144604100c0c0900266145400c04a01c40c01950f00c10000000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 757232994 1250 757231744 757231759
    0x90f0f030c110a080331080c030601080a0f11060912011505041107030c02060702150a02010c0f090e040201020f030f0912012706020d050112150902010e060d110c030703090911030c09 80
    0x45903c9aa01e4400c1b6400c69072003a00400c4140005042c2085140c0c010b0801800611080ca80c9403291030b4804200c01d005401e0040c80600303031a1948884040303074510b88028094085044030b54a0b800c3c000c101d09000450080d980000024061920340180c0d41072001c1d00c0c401703515000e00f555055400d00e51182c400c90b0450340510690000da6160b42540300d902c4500200140e4540901c1c200a00712000c3c003103000144281c0d2640000c000b41e000480c5401d41d141c0e0b114010392510b0b140010307840d012080400020900c8001303201750344054400060458814184c1d407008600c00803052884c26500c1c0082480c910300700e40074150b0700c000c2d0003240d60a040c0c0e00805005240c510107003a104181e40c000d0300035091143c07046209000300f0a003d03a1008401c00c600404010b0711096a00007420000300c55100d901c610030101e108084030865034041141e00e240e41c1e105996940c502c0c0c0000762290802c92041d800308001ca50001030520050141818005c0382d8103000346035a44201d0714a0444c2c0148131003a800410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 757234244 1250 757232994 757233067
    0x6010809071502010e07030303060f12050d08190501060207080d0914010804020d060905060403120203100b2a0d090b0408060103120e040f060e130312090f0f030c110a0803 75
    0x4180046e8001e035001b40c0d0045546802c1c2402e0700b440070440d0b48004c2420400c0e1035203e01103000811840058103041c0392002030707500c40300600d658482c5140c2c1050344003031504c0000903010383c00080d0780c8121440e0b601a40c481c100004010358982c40e15108400d40c10486050904240d8480c2040d180e20910003098058481510307100c04d02243d42c6680206d529500610500041c1340d00610040c105010f0a04194558a480420701e0101011480780003d040404240e4105a10101040f000704040e181d211640c45d401004480f0b9590911321300306000f00b06d8640003c030b4010304880490301030b01c0700c031001081c4603442e50340c40c00314440326008424208031074045405d4944d515406104d100040e0804003045050905c5a580c1c802c01010308181c61082c2c041004a0000380c01600310b0740d400250043c0003800b00c0302818455841c0300020742c000e054400c085800e104040e0084000e034070050054043e01c2c508020142030003040511801002d184d030b4000d10140080407141d09990f00076a5000340e000c0c0c01c100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 757235494 1250 757234244 757234271
    0xc01020f1e03161109010f06023013031101030207050714031507020a050d08130201030b0d02060a1709070f0510020c04022b02090105070816080d05010e0601080907150201 75
    0x10f41d0b0040460b800080d81c1d103da0954600302403094090b1641c0d8a04580031891b199000e9030f9015100704031140320131000aa4000f400c0d080d42c00191511003803c45a0355022105400c41c480d0709540000c0b0b8a070f4412056080e070b103504c0b910039500a5a8003500820055041103240c1410751250016141c4c14071446105501e1500381c9800c840c0507480c2c54009120340390751442d007a810403041e0700140003000101410000c80c429143c0c0790304007264080c00d0006214144401103519800045006904070b48006199141d00d64000794099080c21010a0a8101d40b00d00703030403d440d145580325540325803010410a200314600b0b051040d030f40c0081d44c0100d80402c03900350080390a036049020b4550304d25146040044174680c40801c400303d8001042c2d01185000c4110001030100e004190f80540018804541200c0008107081e0400d82c142c0c1144a460711400380c02c030300340003401f024010419021380d8640450b00715405610b1060240c003100b40030301340c40c3c1d080410700c030f15841389000200215034846400010780c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 757236744 1250 757235494 757235527
    0xc0301080606011d130e060a0c0503160903050607080708090604030207141201241a180d240c17192007030e010203040b0711040f0f060303020c01020f1e03 68
    0x60314039000f040b200c80405409003481802461503c3d00381c1850000e20800740e01c00107c9a00030cc544d20b074002a4100740800300c1e5521600e0704020003034840c0c001845401608201c0031441070540c0d0f40e40079940c0c0d81da041850f440b42d000351001009031f03000b80802e02c03104441c07403c1140f0f01031001c5c2420180b0701480c08190300303503145032000c001003400c003100521146070170180803c0074016200340783c0d1a2400242018105101e0060282e605880810340204030740d03600801c3c1c12400c1d400549844400d80304541007400e02c09015140580d444c17404100d015103a005000007810000303148110101690b4810901019041080081068540d01d08000702c00c00507400c0092114001d0340740e82615015280b42c007520201400307040c241990b02c144003c02645080390101c441d030642c0610b21680f000948004034002d448070094001e40681000c00450a00c1519800346003128003a82c210380d011040413005988444084040740c810340c200100540c1d180700e1a542204d01900c42074103c6c0c0c50541b0810040353340303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 757237994 1250 757236744 757236769
    0x17060a05070509090a1a061204080306120d0e040605090105033703051b07030237090c02060f1314030910081005060f030f072c04050c0301080606011d 66
    0x166540b01d8055072051412038071b42c441d44050300c25902d0110101c0964118000060009000c20303c000b00160254880c1c05170548601103110460300c00c244032020241c0040014448240141d140c102c0c00205860300f944440c0c12110302030003410040f90705c0f510308201d00861f01c4c460229a40c0030700c0c0c141c1110740f080f00308025440c080d07070750789481e90004100030901004085c1c0c01411917004140034000b5a0f81c051014210101503002140e038403c40003c140c020000c1500c0e005100c0c03100290001b010300c1c15410035a61007840f6802e54041d5a51503125109c0058107680198480c401c0c2c05c1d03000c0000e11030303050101c51201444122410070300345400107011401e40c2c1441c80c1c00108a00144641c0200402e259005010b0442d03c56041030805080541d42c2c0c00000c002d045049125008155840d010340c40091444c2054109030107040600c90b10030b02da8045a88517540204d24007000900c88400050689051300d1201000e00310603100c4034011148140c090000041d40400c1c1d5860f1030700c03641c440c443e0303114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 757239244 1250 757237994 757238011
    0x2904060509010e060309192109050102010e06010b1e0706050c07021306030302191406010b040f092a1205040c0e0901020918070e0406080f0717060a0507050909 70
    0x80e110700c118001411441001c00c4103004810500c1440700004000c90703a06401340950341d002e00c3d240f07103a00303004400c40745a680c0101d0741c5900c0e01b0500380b1142e0100036802a600280c0007802101d000d00c030703590b81d940424850b0211004083c850100540000d6850144440e141324071a4149078060700ca09088131070680703000e141500009421821414200c0700c08101c00130719141003100902c0c549019481c2c0428200302c11032640c010003031100b00602250401d2200a1400440d4615030312000740307103859405030280310459150710100041040c02c9004100c0c40e034180b0744400c81c082d002540d00d500181c81c18540c105c01d100700440006190580d501c03a41d8422806000e42140c1c01d480c241444224400c00ba02040e01c1d80d004100201180e120380b01c0384105a050650303140f840c1d54a40701c044400d2000c112000b648541020b800045075900010010b901550b9042a261007683c0e5100c030300500e190005410174241c00c500000349554440368085c80d8400800d05000389800d000c403000031102e280c102e61544 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 757240494 1250 757239244 757239247
    0x100c14030a1e0203030609060d080d0e0106050a0501120c030204080f03070c3005070504020a0801051804170c340906081b030c0402070f030e010503010b0429040605 72
    0x565140c1c80811503182c180448921035500c0b0107040020340b2848014062401200f0060110364141c9400100910054028490a481d880b00c9aa400d018001c01c404241c100d40c201180801c180c50b0108000007103410585800c0d90700840b08902e10040d101c0103440701d041c554240400140002c00f8881880038a0040303001d1a0b64000310b141600c443e00060f005080400c0340707400c0c0000b07201f88081501c241600e0100c0078501c00e08031445d00e9450002a80c204582150010880e81050307170300481440d041c1c0c0c204940182c81420400c1003041240d10848000e070003401030311220315061807510002c100308108541511b000c464412400030780302035003900d00120f400c600c22114400c1c1c424800d0040151016100901400e80f52850b51a43c803288100b07110344108081daa0089580c1c1c0401c418401418003400030b5480e05e0103400c0404c0b50780c0d00a6020340c08501c40c0103543d919903224200b20b906942c0791009140c2024201000b99010384c00c0702c03440070890412444e0041079000350030060001001b035960b481707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 757241744 1250 757240494 757240507
    0x1090c0f0614030a090f1e020f040203091e0c060f0a1209020a05060901030f050109050601090e190c020f0105090601060908010216061104150c02150a090302100c1403 73
    0x450415440381c0c081c00422520005403402142d401080720781228148030045a030140504040e9402d61010307100910451140002a1810b2001801c40d20b125000302e030050303515070400d818482a0301c801c036a416410380029600203011a00d80300d4803030540c2c2c4d0a4080741c050800581c0403c81e541e0005410030303e44800882c14022803a4003042e250116180034000b480001504c0d80440c40919440c055a4881c034404110a201644a85e01042406044800600895a594071800c000b068103451140c00500c4201011841c00784020f02c00780a1240c13080000e0021642d610702ca801002070509031000c50080010b0749050b904240036842c02080300c500941388030752401401410141c20359102c01d26503401404000303003d44524010a44841d00000080b9240d0038207028000984901d03046540180501000c2d106c61950040f03071480f100e0b200f81c2d61585407103100401c0d082070740141000c5000044503103d050006040a0700c1c51401c0c41d8031b40c20805011034040d0b9510031b501c2981c918940040e800415074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 757242994 1250 757241744 757241759
    0x5070e0108010f060819170f0304060b040b010f08162f0c1203070611071b0303081008030d0e010e010c08150901150f120c0818160e040c0801090c 64
    0x1600c0c005e00c094030050014403460f0020390240b0a00c5040641074006e2200781c0e8400006580482d0b405040c2038507615543d1401e0326111008149010000740100e1600c8580c1c0c4495008600c003040400c91342e11059615503070140862007010300030000c030042280c0c09180c02e201c0100b94048000c0b408501c4c0c2a8620380f50311581c0580b5200c1d681154911804160342c481042940c0481151045030700b20101140444c0c40c000d00403440c1c0302d4800000c0002c005090400b000c203040380800003e50b44070380e942c00c0c42a240c11422900c18119401140e134123420802c42c0c110320003a50750000f402c0b0302d9404004035440680e2090682180c0c0c2c198a104007083c0110200b0200805400c1280001d400488a2241e02c0d41001e180824461840b0012028084064034070420503000b080040201e50480c0750502000d000700384004c004007400d40341c1822082c002c0010400001c03010504032816000032a11508032440d2014030082c5100207030043d41c003201011004203201e4402c1c09403006941c01485140c0d0598940003d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 757244244 1250 757242994 757243001
    0xf0b0405010b1005250506040305030415020a090b090a0e16021009380a0b030c010905030c130f0c0201090209180a03050307031506030e0714090103020d05070e0108010f 74
    0x26903c80c3c801d418200c40243e8001d0151540b020100d100c0e00360f0f50243c10403448699000010217001485003000f08002c16902100079442203125810700c201007880543c03c0d9003603000c1c00003140045092820244640034040d005403140320001400c100361b2980e10040071060300c01c151043c42c0d01045442284c1030940c0c04016160b0701c01c400841c100303d00402612208401807410052041040b64044e90450071034038010040c00701c640118480b8000e04095555030300400c03110341c03170310300034059516a610b1560060b00400c3c12294094080c1c5080e0000a04000401c9a9000045260307a520325282002da00c0611460328551415000000c20b4000780c010040020300c01000c00b0490f40b03100c5104401d0050100d00c2520076989820308584a4861060a0707018140c2d01000103103810703205400252299040c1c10140400001c20150380505841d060300e00c4011124103003a0760880c0300840100014202040000c2500d0f00035415907419603141d01d90301c0c1c0c6e140020b9010a00503912802c01400c0c0220720f10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 757245494 1250 757244244 757244261
    0x1905060a0611031e1801021b1009081f06140a03030509041107060f060b030405210906070318050301020a020309060d020c0f03070309050f09040209041e0503070b1b0d0902010c0f0b040501 82
    0xb80444000c60720441913001d25110954009c0300001c2c40c1244441c01004010003400100c0d0030b031440b0640c90448000e00404100ea59820700f41021000502e10581c040c440c040340001400e107010703903070441c0c80a440c180d0010401035001543c2d0032441d20003079a40009400f903144121004117958151840a038191641074000c030402a00c200103100001303c3c00110004600d2100318900c408c2580000440310038018580c51580058001588904055020410301c1000c0d60485001040319207400a2508074042c8901640c09a80204481403003032520b100500010f0084030f10242c908001c1c00c1455080107480100c0358580c1d80080f07090410181c00250090280806070f0780c00520140c0034002a602860144c0040c2c001e03070b1510049001e01030000c260390a0814450024a1382102920341241d07690701020080d10a000881e01044042c800c50030f5524140b02403404186c2407070500544600240300400c0100d05018625a4603000116000d540030303805401121410064034047c24090300796203804 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 757246744 1250 757245494 757245497
    0x90c0a0605032e121509050a0c06020303100e180d0807030b0315240901080a030201050906040b0f0a0f0f0203060f0414010b07020f040e03031905060a0611031e1801 72
    0x1441d42d901210085411281104c42c5501104841441ca08014200105560048a006080004040500c440060440362052007024070300d010965460080fa1280070548900c110008074100800610811510035604150000a400307182c0c0303521361101d0305c0c199000c02d605003c101c844040000d001c1e00341c8100d8001d5001a4007400504241c0d00d5401c111400050100720008100031640803019003c1103014550b602c080c100b1152943c4412005e907591803169012001582000006079180f840402d040b070180707a2155a01c3c005840310f0340020051200144021030443e0b55048505120701c480c00b89050024a1030001139981c03c04609100c400303164030500600ad242007020440003031950461a6044841c0ea1040c1e5455010328800903110720090500f00b60301508000c40c00f10f04180200056015110441d0a22a0419070308050300c2a5503003120fa4a9002500c400d0030070030705000711808500503224000f034030b01d00502d20621526881c0c80c00c03206981110007180104c514084101410760b154800d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 757247994 1250 757246744 757246801
    0x11120703140d0b130203090d0306080a111206240301140a110d1b08060315010b0a17090a0201080108151b0c0303070507060c0f0e0405090c0a060503 65
    0x5645000c1e1181095926020341c103080014244032034203081d4043d04440784000e0010036410902c3e900350003e5002520f001807640510360030400319030300174441c15048400c10009803105071501d4440b56284000110100d030000d60a8081c9554441d0a000d0144038a0b22000c1402c0350008101096031113248401c2083e01981c980a1800d50701200c00c0b400e50741c032685a43c0c1c082003c1400c0c8a44840314007580543c2003049061140340103003a5044016440c0c2050281e41d84902d0382d5a0504055884401c0000251611083c03801480845070544c01040b200c046414400f45c0c0c000302c4110342c0e0203900101d614004c50740103180b0083c115a88905000d0040090b07034010320480c2648031320080c000802a1010804d4011484640c0402d03c4110540c0d02111880f030a403900d0349490607020344aa40204800c94400b494100b0030810603014450800714407640d551500044605d650034040140b1010300b001109200e0400080482d507601042c000c0645160342d203c6403a0b09204601c082d03010010740380940803105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 757249244 1250 757247994 757248007
    0x4081c03050f060d030e030d05040806060d0b0f0403090321120b031b0301240f061706221a0418050c19080613033f0b101112 55
    0x201c036036001e0f070086004c45071440b9000c203900c1e058500001c171040300e68140c00341115250f2120f82010240c4101c0700160203441c850354601c41000f10140c0417600051030b1803021404585400051058164003610908182c0012034507038882c10340300601041c08580d01c0681c1e030200d8054942c404c0a20040c0c3d0800d400c01d00141344070200180e2500301804070040034141403030311140c550b40d0035048078000d84070f06603000109a141e2003601c4e075544454001ca5250a0707080c680010740324482c0c1c401400300c1111681c03100f280c0d01c0b06000c0000c0c034091005460001d600c0303100e020034007484500c1402a0700180b080246008062201070006481e07450300702d40c2d14150201d00c000041180070500c01601d400440b202ca00035851041a900c44d07690982211059204a40c00c200486000a4206040034003a44644401040ca806542c54103a08950440e40304084d02000c00d525040b00e401c41c4011007001000460052100408a80c80701001d050810024481045850a0200030f00485c858050340c0d0140070b19001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 757250494 1250 757249244 757249261
    0xb0a05030d120209040c0201140c07030e010e041508061f0503030403120909060602030405041b02071701060308070c090b0105181c1b0608060409050a020d06020f04081c0305 76
    0x80c2421404080c402c0798815840c000e981e65040364a8000010000c2140180b40c040c02402801d0022403492603001c4400031515644204003928826a40740c0e451140a00c112001152890500e1401e40c0e042034407000441d6000001c000c284000d401c40c0d00081c5620301e414104007918006101e00c0f41050324803600240003507280441180c09072900460203080714041c0c0d00d001c8409100c1a03010f0a400c51034003078007041c5180d001c0010310864404490510840c0150a0f080600e0000d050007400541e00c015002c12039a42d0411000d540404040d000141e81a5280c07074140107980011002c03503a074070066200740070118151050400540007803030310320700f49020400810103400c0c2004c1028420032202400807031040948028081e1160f000624581c0c450340301449880044141c0503a0000c1010b0b1800151182018070600e00a46d1b00040200346490581e020f000e90700c41e207000c094803013036000c20500d02920f250000a000800c0305900611200c030300000320305019444440c02c43d0405040c90103100c03c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 757251744 1250 757250494 757250503
    0x1206091608010b0304020f0a03080c0c0a05090601121d010f0e0d0507060905070f030f05010e060c0912070902031003051606120c120c03060518040b071101020f0f0c010b0a0503 77
    0x100c02d50143c499580c2c0301e130700000707108111040016034000c1320707548080100b0a00a01411b09840c0c0304c0c00b280d1850500c1c00400c00820500d015070703a0003911180004002d988580d42c844040d0b1462072001403060070500c0800030f4104802c0710502986c4d110f01c8484100d511074801e00301094500750140512074011140103002c1d203d0640040c01494070344002c40705100c4140040c0d8000c11140880d112161340d030740380440e00c1c001c2c810390030741d41c1e03501c1c007104011020808031303019204082c0003480a1804114000304000584e0350034070f80005105000010031003500f50720081d400f80145552542c1071916510703046162034410042c200181d4204201040b50035002910141460170302e06000c24902601041112614506100521101d0030010342000d801d4240d44204240e50003a03500c80110112849446603a60302034800514500c40d00c400550312610803d48030451410010000d86403107903000900c0d1064100d03142d01d4845c0600013403100341030030b000d00c540d144055003540e134486518680b03000039895 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 757252994 1250 757251744 757251749
    0x31b030b070513051c1b03020f040911030109080316020102090d1520090a061713030216090501140d150b010509040908120916050d0309080102120609160801 69
    0x340400840c1c1002200030807294034014040103813614143d411780580c810040007007107500b9224110082c5c40d1135001e0800110507800d898028286d000c814500400340802401c010400342c1d030300c081040003644655400e00900c085103014140f801d4880c1428610f000c00094000c2e0100c8c1036a01c1046850015100c002d4142c1400d500800f12501c0600c101489001412080d8650100f00040444204841c01010044d00d0003034030603901154500c2d1501000c1d50a601c58190113a4014002400100420000d00f0b8040c5858440d00c103589460002e0300301103a401000e0340001340e40e69241c400501054906074440c002c682c1007103d00030200081520360300080c405244880c404686c43e1180b5400a0340106c080742c0b1568030207041081584a10b08007058182c1003141654280c542c01d0b0081010b40c040090000000c0b814810540c2c040703840c0c0030400440d042da080d0304405100058100152030a0300f80b0150030380e1102ca2041b0311140c90803504220b01100005c0c0000c0c80b90110703241d941748142e13200704240d05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 757254244 1250 757252994 757252997
    0x7030e0312063a080c01050a05011401110c041517060a0c081521030c1507030204180b0411030c0c0c12030f03090726070617060d020d1506031b030b07 66
    0x180d812440c00e2032004c6200345840c5400e550b0070003003400706481300c42d030041e812074840c942a400d0b6510118011100c0f80d103c0800c080c060b5015820700412490b040d8014465292600c840c41c1403241c0c0c90000441c0540a601080d60701d070052410014541654042c00043c00070901d400130a40c40c010b818035012076000491107008a40e4052030095065404030440844c020301c80c11a510341e00d809100603920142d0a03c01c0e58504071807000f1410050080c0240c4080c0c88040b2040d100140b40c01003541c00500c08903d00303980c0240c45042640101c49400021405103035840942e6070b442442101483c0b40c41082d9070158000c070001210115182c0002c07041e2401030103d011142c1d940c1d281d12045a10301801c0d0b410541821140c04103c808400704204441d0307545042e0004e80342001d50b5008103a601000c820b064403500d060002c0002d500349800b507000840e20784010a81c02304800141c0301c00c0c00320071010300169000d60f80e407542441448141a180c040000700c0a0304010041d0660303a58040c81700d0302400c50030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 757255494 1250 757254244 757254349
    0x30f03140906040329010803210105030c2404030f0b0f040213020a3c14160203210307030b04020315010e031005040b0a0c020a0201020a080307030e031206 68
    0xc100c02c58030180111000c000000d08046541c481070465140d030b10482041550003012089e48140d100402d1040b4105c0798010060300039240c0910501c078a6900d8110151007000036084010b40d40070a050291002e14014400303c0500d0340c00303151001081c1405800310010704c04090801c00180c0c1e41a002d605241000304002d40c4900c0b281c10255001480303204486120010117040c440c00304001c031040f250030300f03030150030b0605810044400e44440c81c5c58040241c07024400c12094000c4007001400444180c4050100d503400600c90746001400c0d86e40c800c2c041c40e00c2c8800800d00a00c0780e80b501990781e0808007107804502d581810b00460420856825015040c4241055010040e5409102c50106015000c50502041c230380b43c030f8903101c50f0108541d580d84040c0b4004021105071b10000d80f83c4102541038008240b10450fa88810078141c0004120400b0180c80710307a40804c140c001e03c0901404c0001440040050500030100b01005c115150400e070000813440203500d20040c4030f4490321310b00b291601c901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 757256744 1250 757255494 757255523
    0x330f03010b04020304150605010f0507020d1110020d110c1e0d02090a0906060b0f030a050c0d0906150b0906121b03070e030d03020309071a13030f031409060403 70
    0x240907090100070194050300c00b1041001788081302e2814404803400350800c02c03850740c40380015601e540079a01ca01000400c1440000c005003028022107041600408104141c2c030982e800254800440c84850070060300810303003030b4a5068001421140c0d40341e0701c5000e010700301401c01c00700b0092180d000c0ba1140c0070115400e42030240d260081085401500640741928500d400c0d041100503080c5c8402c11140d8910380140040c1c402c656a042d210710103042c000c584e2030760f00c602c1441005084080c1284c00f2001c020400300344140300602c0b880f0550391064401159120b00244c082c14201402c1c1d01a428071002001010015038641d0112031010211821051454450140000542c00d40c0d05054030340f40310000511004503003104000030380e24400c03800c640140c00060400c600341d010540d80d0766480c0c2d108000078022072041910010f00a023a107040750b41070610b02060103140c0d10243e8419682142d8002c030720386c00c1c1030380880242c00e00d04502807000c0c5171618440200d0b02c1072255103c060801c0da14420b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 757257994 1250 757256744 757256749
    0x2102061b070e010305070806010501050304020105030403030b1201060e0f09250b07141c091518030303020c1605010905040f09061104080f0109261e03330f 68
    0x4414901a0380c400311000940c940c500d018030200e00380020703a007a10480304005054980010020b0507180c0694809042d6100c0d50700640700781d00050021000e040d128007030b010313468546041d8849a40000030005c0350705460888a0b001c0d402000d06800a5100e02c0d408200050400113990350b0440c0c10f1144100480001030b0382c186205082d5041704d403880308001002d00074403403600c50030150001c54034142c030401e030191400460a0074482c410400030072248841000400c00505801070300c1504d42c00d09110910b62041a500040c40c80d03003040b4046a4080361030b0994600c108956141d03080740c0761004041c94240b0380060325101003841000d1240d2703140c44983c070450020360809102e065000c003080c40420820400e541d81c1e034100340140700b00c80c41403912500701000c050145410664002e071f64042c4010f8005158451100c1c1c404c120042d42c5020000e068140100c9100c1d00b0302108801c075940d8490403e8005640036142480b25400b509182c0d60103100d020342c0c006151b11340100221074406041c60003e01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 757259244 1250 757257994 757258027
    0xf0c210504150c02100c0c0302060d020d0216030807091a09013f090c0b0306040b030a05070305101a010e1c060501170106030f06051e070513210206 65
    0x700c00e1030002c07109481503159420103000d200c418400c0740e1180c0656070302d2a04843c040240d44018040d40c806d020100054204507006085040c14280050b2914440450242c140c0e480380403080c45842c00c0054250526a0108095401514500d40440214a0410700802c0150b050015106812000031040016070069040600905407000580b040914050501c80481c01d010f018668011918110b06400c4503070307100e80c42d80b2680c000c0044a100303040c01e12003ca82d4200510341500700b0703a6011180340a60b010414078403281c2c0f00318010104141940751040c01c000e04040e41c00d00701e40c02c1a1516240794803a6070020a407860038a401a0a013a1010000b840b1885031041011102d0b12882c03000c0c00c0c03010a4001034140c0b07840e10041c111900c2400b10150072948640b00242c60380e00c648480a00080c469006180c00a00c3c2e0000150a0f03164003400c080810002e45080001c1070000542d4032212115105886c02000701d014030418801440e10346a06410450500034401e403400038000d416202c0307280 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 757260494 1250 757259244 757259249
    0x3051c060f17060117030706020c010204050a03050318040234060606110606030a02060a0c082118010501030506070c05160801020a110c10110307020904120f0c210504 73
    0x680d21140c1d550b45102580342405520982c0341940500000862924139004c952090543c03e6001140307045150f03202e1038000d401c105030b00a0155002c100002c4e195403030403070b11009580981d001c0c0d03643d481c07030f10420031055030344a0301300e401140148003588040b03840265030300d00304620005181c4203090f1b0007400744c0142151603008000501c1c10002040d00d9030700040c400d2222140c8011200b072919460209a070740c80c0c01103c0294041010080305016a00c07901d401c5241030300c00c1d03c042e403c1000c4858005441a001824886180c0d2301608000c1e002e003081000d01c40c00c1100900801540d4116110140c9844d001070000d4240000304107403400704402000700d540c619104c0300d2580185521580381a02035800115000c00007003800100d822284400f14845800280040500616403038118094890f15441c40c5030000e2800180b1114000d40ca075100210301c1180704102e074042c440400b400c0941520b00b2518100c0401013000a0000010b52407404a24900c0c00802c4520701c00b0f64001045079a4030585c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 757261744 1250 757260494 757260509
    0x30901090f030e030c0a0b030705160c0b1903050f010b0f07080705010501051503090601180e01020a030b0a08010207030c0b061f020606150c100c05040f0612110703051c06 75
    0x31500e0103050b80020f002d200240d08a0644810024002c10031140c5410b034060328101c44410804904014001d0004240030f500300f00401e400c542c003a454407a100d030150f90004100100004244219035104042c039060792880f4142000541021104a5225141400b680707003007030000644500a40545e06c2512001c9038001c800503942e0b2003d00e00381e0b004e0301c02882800d004a01264450404500a8050360311035a4444002c0c0315a07840c0403009606d001e0001f1664030a42d56a0f0011704548000380003c0c25403400585010464048020034032038000115444460240d1050121100082c0c0c081440071a0b1a080001c1d811030361142000600c4c140f03041013440e0080740301c40074950407203034002c00c80d00d00c20b40045a010f0010000851804058480e80c2008030194001c407070880304000307243e8007028141455203000c0c0d06080c0ca40c850950300d090160080004641a0071550004120724000d03440125040000e0b142040d04a5501070844d0103140c0d00e00c402550100681d0310003000b00da1025000723042c503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 757262994 1250 757261744 757261763
    0x21203120601110d08091608070509060904020904170708040603020a0e041116110d2306070f0f030914011a040606091206092f030609030306010c030e040c390803090109 74
    0x960710490789e180000d00c241030103210ba41c030020356949032800c0414031441d009413000444d41e07a60b40d40c7c55025001c10011240050701400448046841c50019201410451f2001aa14000014064142c80003074160038816414812448039200c515402d03240301e41e030148018501050646800840c00814420158008511200f00000c0c07015030a4103180a140c00545400421141c0d6503160f00c0f10f4003201d800d008a03c564441a0306c1038400c0d0b00e424003050040ca000120490a5a0303001e0ba04100c420045070181e46401e1107100c00d4040f841c2074589640c045400304002450301c000500038500342c0c40b6202c030495400e8050340c10f00c00e01d6001810819400f420702200080506d603440d5112103c5000f06004074000303600e60740300742800500030b80110128001142141d844000445520356030710400c6040001003420600c0c3d64980c1d00501c60300038403030346800401d901d40700208040c4815181083c80c50300413404c2c485810220100e14407000e66002202c086e6642c1e40c400446015202403070300204000c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 757264244 1250 757262994 757262999
    0x507020909340506220f0f0e0705120114010f09150c05070b04080a0c0e061e0d021c14070f05131e0b09010807210609021203120601110d080916 63
    0x11145d5a01801c0c0802106042054880d006d2021000c42400740d5980b40524840a012000c0080d042d10f41c85079203403a040d40307040780b402c1c90851188001c0c2d0003d134031010100c100104968000e25050100c54685c913121016905d0007200070300c0845200006400c0c0400714034030400303011050122201812001c41034a6030349a0b9502e0303c42d5501084030040c0e034103400d81840410a0f1240e41a2640240001844004080709540343c140c00c5900b250303c843d0f44035540d8040c060050b120500d440d400d1084081100020311001d060103802035001200600361900b00d07000c01c3c42920350411b0381d1410798400360f4000480131300400010008040c08501c1d242c004031820301000c04403440307822680a2604c01c0d645402c0fa6607071099501c1c1d90b40000d00910a03c800c881d4001d8040d10600e401030210a0f025090203c0c40401540110b00e11812004c0800314a4200003041d802c6040700f80416a004202840c7c01a50403a00e04100d80e2038281c888041ca0400540c800030800d101010858041a0041042d4922031a036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 757265494 1250 757264244 757264267
    0x1806010806070311090d060b040f0606050c12090117070201020f040b030403020d0801050117041a01030b041109060f130615030609140708191404030507020909340506 73
    0x30007100c400b00060309150f00b800140b1411000c0c1c400d64400580303040c9110300150f5480014003222603030160421b995859100803980140240b5000702829111760b80d60b201c3e0040030605114040401c4054000c0400401e10940d070301c5400c5514000d04004e82e0b400702d498102003280640300f007581c400d0000b000490040f51104fd8900158001da01c04c2d000c072101c4910a01065864001c2480740a02280300c10005100401045018560051240400d44012881c03400b0710f1403444000e07041030f502d034144042007004000c00c000f20001078a07011944a442c601c1c203030f130000350f040e2202c101c154011040f0303003c4441c4e000e081c0d410140c00703070800a9800c251a00c1c2040c0060050581c0d1003502c0c40d40741031044040011502c150194005c0b07181c0c1d40c07504d0740f56503901100c11002c01041481c0c11402c0c0e031924001683c4800c412000d0099110f0f40c1d400365103d115004000d8460300140c40044c45402003440c90690039010041c2541c0c02025120110400c0160005031158401c0f0340d205581200c00058107100f071a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 757266744 1250 757265494 757265503
    0x9040f20030d11121312050705210c041e0c080702010c2321010315060503061e0a0e030d02070303060e010b1813090c0306050615040e18060108 63
    0x4403015001c55040e00d05500044a41c15001c40b00382030541c2003404c0c4c2500f4070381c2e2500144584403800d20111003255884e0320f030980410850f0342c2564503410443e0f090106103440c40040c8034a41c981841d5200a4215001180e00c40c5034050840e44203650b42d618403065071311040c400b00e424031802103040040e00000200549010300c101ca0240055282001c3e0300300c881d00401d0b811102032607207400401e014400040d801030f107910100002c200506178500000240b4079030004140651301c07440c250f80c200c1f800c10260700d05840310354000e5807081d0021401c10607070080c100044c03610402d051400482c0703034403048015401008a80d560300c555000010301e5034000da14503001046201c0c446d6504106055035103c98048400302030080301c0745198200810495822904000c0350012001030014000c001301702c41003005c5895446c0120356100102c0000c1080c409a48605070340908195a2034004000711a680801c0c0e00c204e0040c032100c0c42c0d507070000c95211403803010313103089011601085a0580d40c40360700c070690781c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 757267994 1250 757266744 757266803
    0x7050925020f0d0c0b15060c030d1b0503040201020c0d0606090207140d030e030313110d0f02040e160302060d06030b07110705060708071e170d0f0e0a0209040f 70
    0x25110f581ca42c104860722400c6550f0860b03401460340200f80d1140100c1c00c52441c1c000109507440300b410300080c60a04814070007003180000c81d0000189681d60248030100750400780b5410010701109000300070140c0d8001c02d035a10041e5040700c02d84020346503481c001e0001c2c80d858100250403840403519208110004040f404a000d00804854030b1101089080382500c400c5081c0c60705076082400401c1c0d03000315058040d441d40d80b2031801da12a24280c2d102080310f4040c5620140ca2000081c204042035007468441e0405041142e0302901c15407040c1441070700b01e600c0310300c0024084c010000301700441c030b2095400807003e140d00c140e8401c906e06009100070012011030416400710b00482100042e40c0c82c041c4221101254041040d80c00c05c1516100c100c3c0c1c0105401088282c281c65012400003e00100c81111124200700307259600c64803c1d40d0807100700e032041d00462001d245044014442d901c1d00042e40351403d1750444012040b543c5903d4401c902040d032100041c04c3c1c4010308602d000b56070482034580351 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 757269244 1250 757267994 757268023
    0xc0c08100516020705060703020307020306101503200c0307080d0b03060a020403242a020f06040503120601090911040306110a0f0e01050c06010314060106110705092502 74
    0x502c0e22080c000c0302ca2048281c500b280568000481082079003003c5010b0210ba5000703005690801809801203803c0880440d003a41956480307410a106050380f40c08050960000c0b480c007002141c90040143c1d1103141d9104d0140c0303d82c80c01090407840e040c4100304641c0f40b640d109407d42d032910385c40d241c130303034060400b840c4c00c0ca00c00c3c011100000d030036400c0d80c804c2d6021640c00c459843e0030003040c1e03444e8070b8101e0380301566211004c2c0c03a820902c040119982407803050000d40c904030f80030480070b00d0009050032603c0c202c80031190070031424440401e00c00800c0d10940260680e480c41581c60750001a5904202a48a0b40d0170ba41044256080320201c0d801500407a809a20306100240041c1000e0505200307100d6090040340c541350401c80000d20031108a40d060406040951400c50a4050703249001c100340d008a0755080c481c5840d01c0d10981c18402103004210301d0800090b4070780c5005146032540b849004490040281e24000f4010800f0180b19a0300c00305a174031108216030450800945a01102d9070091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 757270494 1250 757269244 757269251
    0x10020c070f1a180d080c3004090c02030405090a0e0105070503060619050c100501030c1703041e050612060a051f0c1401060f08060606040e0a05070c0c0810 68
    0x40c0c00094040501c1c1101d00349010180790401903403c0c18100f502162500f5004031105181500041580c13008041d104081d1004004800d40207041141d40382c80b828040d209401249069100e4181200c1501c080e58160300001c600711484000c02c0340b1718055984a254030140d50340030f000140140394400c8881f00d4035500284056640e07050709503218032041d903c007908407201b001110540440c9440e101c2c0078030032500e84107240c0442200c170b0342c2c42c0103c040c0c2051b0605542d400100104203401c80900000d00507030314002ca5025807440520740724002c0e84075100750840401095200c0c0903501d0124801b410004000c6a100d445102440303d49550454502d40100300d4120b0228a61a1010082522001c2201541040e1504001c2198543c0c503046084400003650042d805074100c0030f000d20390103480601c02090005181c030780c0c4d41d460400c3c05010280204c1c4100b20078403041d100384801c260720030402d10010402e40c41c0c1c08011200040e000d00701070304144840c100441c41d03d8005c210070a91440581d0f052 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 757271744 1250 757270494 757270499
    0x506030a05061e4602030106120b09040206250803070302030a0b09090705151b0d090603050609060f0f090c03071112091c0c15110a030e0108060310020c070f 69
    0x4007101c80c0b166226003c54240040552510060740f01000e61070f65000200342103207075100104d80598000f03802031400b15140001c0400e0510b89881003480e43c1100f1644406542020340110707800c0d2040100038003401c2c05c0215514914020094081a0b0316880120380f40c0d240b400030b40041c000d400c150342003040d5906103c0300e0b590302c1c648a19290300616165010309103442c540410000340c1c402d142c0900d480c0250920903095124084c12031224900200c5024120b80000154010252907194021805051500e070074442d807a12180411a4801410b958110052501e000001e00d0003044000e42c0c0d40c440c0103841049829982c1002440c0a030900387c4442000c081d90110940d210301c0d8240c034050005005000206151424822500001012688030041808243c80784140320680d5004104500210604c00d0701c40c07503101c583c8504402d0510081c151051107a903000348a41c411080c406d041181600204003959014401c81c40e2140d00080d0840d5030310303689054141c8031009481148450304040600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 757272994 1250 757271744 757271761
    0xc15010b03150d0c0b030718030f0b060901060518220912051c02030615042d05030d2f01051005010311030a0f0207020d03080f010906050a090506030a05061e 69
    0x3c0c0c50455a100110b072040c07905000d6007a0303003600001c04030342c100214500b040048044680c03010000d980104030111124455082c50641030b0006090300380550115401084441d921400b2f07618002c0d00c00158031070b40c0100303800191800e1003000d08200c11224040c00d060300d40109500280340d161141c07615010204a5000590f102d014201000800180c1a04082011a51036004540c42000144095102012035a0051041d0000e80180b4095225415408420302d00c41c100400b5856624168002c01400c1070b01081e00c6000040c1f01400340941500c1210f520700c00b4032401c075518401d911902c455800800301c414041c09054600500700c680310000031426520a008940e07840302c40590079880c507218907140c80024069507111003501c1ea4244103440040e03880510303140c4280e002e6502c000760f905004064104008040c0d0010300d2403442c0501c200910380714580c0800440b4050703030000601d03586800100707041040451000b496802407604000c101c1c00d448001d410300c50011080380302d0554907002d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 757274244 1250 757272994 757273009
    0x9110d2306040501051e1f020703032d030203040201020a1506031a0f040b04050724030b010e091b2215020706020c090c1b06070e01020703020d06020c15010b0315 71
    0x691501b040490b2104080c000106c410715031180700240c038800000c00709640b0b40d6402d0348004100001600418400c10a160344100c0b03030902c03525200303008445c01d401c244240e4201c2c101c08140c1c40c141500400010250ba000f0302c039815a041d0880d6a000004a00d013907000014005c83c08100d60180824644d00c08001212000522488440040003010f403110780b5000404000180221410300c204a404141401d01c01e1000580c1920040c40b20b10308003151201a041d02c501c6400c05040000740880910640e0b41d03184400c1c0c11003100c2d81ea421001c40314010840035881102c00d9113602c1c0c116039882000c0c080300201d002e811110074140303205600801900032078940d09603203d010300692021582c05100d05c0d14454203904020340a0030030386090100d0b50040c010f60b40c038024071001c036040074003000308035078028568180300107091002e000070b6420b6a0018848035000a800346c209540407070904c004400400030303114800c2e0802d00480d12507950b5403508829520440b001401d0100c5800e0700782303860410b600c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 757275494 1250 757274244 757274249
    0xd03020d11030103260c010c020c0a0b030421140f070512030f040b0c091903030f030c0210020304030c0f120e04091a0c0417061f06020709110d2306040501 68
    0x4003615104100b40c4c00100460ba03a440401701000e00402c14003503e4032091182c084c0041464001c3d10003101c01c50100f101260040c0e20041440030104200000614002d0340001d415000b2080320011300c4441c0340031a43d03c154503940a0b6680d90000300700040c1001d01000e000402d01c142c04503000c0c0518402c03240f20070301041d07034809600a000c8000c00c0000300f007019000e50003a00e20f200c280c14549601c0008a00048650341d0780c03200c03800400140141544611054400140360809000b40c0284503002541c3c0c147c4500c400381c40c941c0c0440483c0426114100c588401504040c0c0700b181d20b0071a04044c014005440036100c0480e03940e00b012112803e00c3d0040741400e0b0b4002c2c88001e00f034038681810311000840106880740301181007201081d00c0380c0d0811400441041c0030001c140c2880c04003142c0c2000b881c10301d1140204032940004000300d550008400f0184c5038480d2001c9914801031101c040280518000c1c9140c0c24102400042407000c580300e04800000e02c00c50f6403234140c0303502c0c0910045031400e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 757276744 1250 757275494 757275503
    0x50703030507141303420f2409020f0409110c01094407110a090603050105180d050c070f06050703020c0f090718090f0902270f04060e0d03020d11030103 67
    0x19251142c0090591b40e5503111181c90204101d250060a50126180b075086001d040b41c0d1070f10301d1000340500c460910080c1c841c2942c110700d08104200000128040e9208200c9495120006c0c1901a10a0425100060704020090240c429a032424900c0d00b1094002d61061950030703d20b564105080c0702c0b810003400328040384078540e8446e0041c854559801090181c500040c1520b01500c15202d80c10520000c007001c001c00981c40d070441c0307800790940da80034160082007803081d0742d00d405c00c0001085800500c54141401990707040d940d0031180c05e00385560f10040148440c2c10000030711300e82080013000c03070074480d40c2500c070030203441c1c82008114950810070607000b4a1400004004a0060004c001014003141d4102c5405555421010503143c204c002c10751142e4940301010110300302210004114036007074015004102442820b4802c2003c018040040c040f400000726091081da9401080500b03c2c96098400e44004035102030065804500c1031600c084c502084040201242d106581c181d81c1d10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 757277994 1250 757276744 757276823
    0xb0907060f1d030f01020309011a0a060804050f010e010b0a050904150c03090b09100516170c0c0f0c0a150801090c140d05101401050703030507141303 66
    0x426900300c44030542985040380c80007100b02c0040d400e682c100300d8507104503215400569a4501311001609454605243c0401c0000c0305810017025a94a000d46007a18180d18006003250340341c0c1011440c1030040a03410290707511344081203d030103d042d004400c0d060400c1d25401e0006039142c00344010000c04850250103542802031071042c486890300001442d00882ca0b000c11290082c2e01d44c00320002d0255a9049958049a4409040c0c1c3d6103000706a0f00241d40386072440b60008060024003202d601404501940000744001072003914110107850905056070101c850020300b4400440e500c104021880b80300b00400c1000081c007270004e0340003e5580c090f65580b0002a4688902540070380300d0006040c00780546a00c5080105104ca0040d1607804480d10007c11079042400c0c0084103c0782d1a080078500140023081c00c3e9880e600300080328000c0703a16180010b2580d4035000c0c2200d592000b515601526a000036400c031030007040000780c100b942e00451088150003100450451010308a4048402c4c0545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 757279244 1250 757277994 757278017
    0x1f08062410030c02030405030f060a0b0a0315090201180608061f02120903010f05071d01031a06031e0c070204150f060f1103031306050901060302090a0c020a0f0804030b090706 77
    0x40b81d0070800801c09940112801d160f26180081d0400030b440d0500c0710152b024104103c03440780755010342e4000040641e81034035102e007540c4408070b00302c40b80317112244820b4944007a40e0842e4131902908180303c4403442502100d0741c40b81d10082074050162181d80c81400078a44c808001e80d0098007070a00d2402c02d400401070800d110a0310000c58104650b065495582d5090400c020901402027a2284e00341c0e42d40d81e03c0ca107030120010348010390000f0707599040600c0c200d800640602c000403501c01108046688580320760320207602d010031183c112616810321600009002585007690050306100d4421241486540300058401852101e20b00c25100e00300107503002040301d18020b0003441c1c00340b0860b00e80000720050740c05503145141d1094a090b0300707030760301043c00307200b4400c8620641350000d200790000e1000310300d1a0000f41e000c40d000780c40007142a070350300c410320300190003004070700c888951000c912107030002d1030b0600c00c810b03411a120a4844650000c0005d40d0750001194407000e032207064a0f0441e10f0700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 757280494 1250 757279244 757279247
    0x6060825031109061801020d080708280908041403010b0f09040c030f1a0a180206090324090f060112080d2a110c0a0e1f08062410 57
    0x40b03902d145050300000b000500019100d46005241c109402c403203c9400700401c4000a01e400c005040503030401040806222078654440541500100721540d43e0401c681204401c91030040c00485400049281c00011000c0102001c090400c46024a2200d66a002c05400b0306084c0d400c1c42464a5100280310442086440c2c81540c060b00b00b4020b419440d030081d141c0e0745400d036840415000b0b5800080e40440304845100700d02845502003102c03081403024400c88455100444d0301044000e1103524041484041500e0401c54041c0d0307000303111000441031890020858178408151407400300d40c041e000c449001d46030009241812a807501780502070200090b00c82d0030b11a0401407125409540369480c007e1200360724403014007906055000645908801200900008141c2512514a03001402e04100e80e41c4e0f14040502101c4814141040941d40c42211440d4203401344000024000f070540040381c5070a00141d4035118020540e58560b07a4036459161018000306041d009a2001c100914860000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 757281744 1250 757280494 757280501
    0x60f04182009090601030b1005030c0f031c0809010c05070c033e010314060d030305091002072108010e010b1b100b150306060a1d03030a030606082503 66
    0x981c1c06458500e820103a010006203115030583c0e00304001c0e8010030051040c07110800a141d001003000e10801031941c5484082516001086e03032442c4140c4400070002c05940b0b0510003203511844a00082001d500c008802801c5440f040d240140a9840c25010284160050003150034294004442c0e617900362455646050b407500c185006107864107017100800b00c0540d4004002a11400c082e8600ba105000c2800102200c0c2444c85000041c060801440740544595841405280d05880c0c0032829035100c0485c0e5181c004020030039410a88001030b110144280d2512140300c02c503005c00ca0740d0140c11090400c503010a0207001342810b000710000100b10031012403001b400300c01c0128520300301e04140c0038886800c01c00044090300e0902c0e103807102101d06141051011511072000c000d224203500f0f0040200300315000d04c408041c2480608004209070581d02038900c0b4403008002c0c11244e40311130704a0000c0c080c00c00c0d481000c000c41c0b0401c0120341c22802114800c1d201c2c410020925209440090084019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 757282994 1250 757281744 757281773
    0x9060c010204080d0302040303080604060b1806040f0b120c04062f150105030d020102270d0b0405010c080a09050a060c14040e0717090705102006060f0418 68
    0x39036080200061140060007484c07440c9150352001a2980d140d818007400340c10000309250310413450540103102d450310320303401e4841440002e940300070092502404102c040c441c942104a03031500c0a04005400c42d1400c0040072000c0400740c1c01c1a60703450b40f04000309103005d640108130118007116059020002408103440305c0c2c1d001980702c40008000300309500d05220342a08e041e20940085030040c0a40d0800700000c1420010b1072000314030f012402409400d2407800e0051070707240301d4042c3e8203031500d50795180d41040391290000303501c42540c2460300e006ea000f0642c02d4400c40c04201c164000515481c0b1900c181d403511b50b0800c014108180869940a00511030380050000b4404245007080c002101d03080500040d046014030f5001c10301b0f00d04400ba02840003524140d5401c8a10810005002804200101110002d075190041d080c0030721410740340014004440c1100710030b00c0d810071200e02400910304d80075500695500030304050075810706c0266040e41000c00115020124098002158bd11b1843c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 757284244 1250 757282994 757283017
    0xd020a050c0d2906041b02030d051005030d020a02100815040f020d0609020c060f070914130221060105030907170a05010606020a03030b04090b07050c0a14011e060b0906 74
    0x2040142c003c1c101c01682c0e5628400601c5511420000c003818203104074040800703940301c0100d00e0704c0d0113000256244a040c0e0360450b059140c80203d03000e80700135184140940f01c001c0a81d880c5502c003903002035464480d1001644614072410710308218600460030140140ca141101102d0b02c0644420b0002130801400301c00d01081d800c1007440e03c0e241040c841c40d006800c1451000d0390b10000414402d1905202030480c2c40d51034001c030280328445400002c28800c50700301d4007804081d02c6805000428a06038020742c4102c0302e00000d50900321100032840344242640c2190000c41c0380e20b6030401100d107030104803010107059102543c00d01c52018002403146c0d10401103001c603802e40d001c50f5076a50075601e180c0d10040140e0b204181120415805001e41d445440007a10200320544113511a4510310707801403c0c120600c4800914628114020310041b0740407608542c1e0400300000b2008464001c00410030b40031840409a0b001c1d5641e0500b6005103000c03600c5242e6101d0814201104000040c0e000c500d4201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 757285494 1250 757284244 757284263
    0x30218070c2306011d041205090a240314070e0a2607060203032203170903030a0e011407030e070f03060b0f0103020a0c03050a0903050609010903020d020a050c0d 71
    0x18002a41001e80d1004000b00c1c540298440c0301041c811883e0000680000050708545c041701d10151a83e040050380c025040584d8500600a0f440c094400d03115110750150080c54440700800c003d10400001c5044450865003a1140c401c0903e08800b203595460075145400200c0011802c420700c2051002c0b583d00004125007807181d902c1c030318108001e12240e040070309140d600c14807404522040c008403008005a0005c2c4d071651824a0080c034807528207003801100390900409800c1414031a9100d94200071080c4070072120b6050a01050f5500e4000b29a50028103081c00a130842d05e1606010714101180b0309040c015190716800d00030f4001e440314400303107000c910420308006240300341035503040d0065001e041e000410720191000c0c0002d11406d42000790515004100c854202e0758450303903a21109405140c4261512643c1104803108030580d400604280302d404144110064103600480586100f1380032102c06501c0b1204c1aa00c400401c00c0c05001500b1500c0358103041e040c403040d4051003074440c40b8000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 757286744 1250 757285494 757285517
    0xf0906060405091801180308011806080102030a0b03280209070309051e010c05040e150a0f0f1e05060a0807030b040504030c0c05010302033c090607140403021807 71
    0x80c840d501c21100106032001004e14038009800c01c1c841c2070040200c81e80780e46601544d60318054000c000611070701c40c0020f4021007000700d003000d07580180042d08400c0000c3d5568140074201c28060001040c2080c401c1c013070720a0b00ca080d0340303107007241e9041c400728181c0c3c41e80c2004094080240040c00113041c5414184c172990406d00007802408282d00f9400c2c90848280f5045024107180d007115000b100c000e0902404220074031458080400031a400303070a071b44498407000c00c10b81c049142d071203055100c83c21443c002c44011522022941290b801d840081d400c03071351401c00315030555401500e244546a00b0040422001c000944140a425407102203820040748403041e0b04081012100b0407a0107400065160f150300040102000d1190300600d802d190550440c2803904626103041800052543c1200031510103c0300003044040718030f41c00c00c4010303d200007413070010195902d03107104440c1c20000038075800c0c4070a00c034000d2100b540e040c2c0c0d0f00a4240c004204001d00081c01c009030140c03000c000c2c072011040e007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 757287994 1250 757286744 757286749
    0x6030902040608190501060e0c0d020c0120070b220201270f0801050702150a0c020c04150e010801090c06050304080c1606120612021519090510030b0f0906060405 71
    0x450f809060841803544c090300d0b142001421a0031a401690303070320310220140700e0003245d14811703035421b02c2241e440142e6441c01184441d004250700c1d61140340c8550f1100012410f00f00072f5018040740380c003a0840410903956030a020a4000c7c10150940c80c2203540d00b0440e001d94810740c0380504c820f00e2525102002c2c7c000d8002400d1900c4594400154009041020b0040c07240c00e001d040c0d0081c3c480c3c001015a8008103010711040c80c00107004000042d03031404088d407000d00c00c03c482100b8020140c4100310050381c441c90f448038107040e80242110006240000200301e4414480c0c6410780350001442c6407810f042403803c4415600c060030981c0e1004091104003a614014448514090b2010b000c2903101403500302c018080481c00e00c4d956102c02c0c03030010100a4080c8002558074000e5045278142c4164491400b08a00c6005090350114240203541055010380d410004000507240200c40502d010300444008a0582d00750035407068100441907040d40d401d081c0701d1400b60308581d00402240c00c01d030b1240b02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 757289244 1250 757287994 757288003
    0x90102070f03350c071409040c05060d0209060304080702010f0c030c0b0721061a07080304060b010201151d011a090d08160f02120a0f0b0c04091109010f090f06030902040608 76
    0x516424035000407504000b4182c1000008600c000141c7d02441e441c030301034a49211541480c448c02e400f4420001e12010144413a50440d81d8042c070041c0056141d0030641048556900300c00d074100e000c2041c240030f038450701e40640d002c0690b966240c2d4407001c1d41c040035910140101006420340c82407001c40d5070303403078022a2200841800b41c0c56028001550364648440f00b81c40010380c80103481306170020045c00b00403914100c101c03a4440d0b0410400302e882c001643c0100d0050040448500000c1300c0800c3c046600860060740b00010140e560702501d040c0d803907002100c003c0a9100d024205403c0c2000100d4003402c02d14101a000d0b4010b46050741800288100302820102c0c10f10111281c3e980588944114039121100c4424103502d0341c02080507074007560b1111038404040d60041c10464442e03000800c0c1c01c50540403107014080d00b00782482a400741741400c0301e103a000981080c0c00300d02e01840440c4240e1049000f4400c54640034000c04600b450103d090f0000d000c450300a0341c00c980c8400303012030b13104030800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 757290494 1250 757289244 757289257
    0x20c2a0d03031e06062a02090f010e060f090708060d0c0b0408061609180f0f020c1005161206081c09150906050918010605090102070f0335 61
    0x3180803455074407912000f0301664140760000c40c401d160181c1800080e40c071480300541c8960706d288800320701d002c441100c1803418000300000e40c840111001c1049003003113080c2550490718502110311041d03c54004002e0340b03060005002e0b802003c644005010030344500441d5400580140c502d421121240d1500c01145070b2980104001d54030014080082c1101008082c1d400144e0346143d101c1c8400f82c410043c0240050321400c0c4c403c8508081015400800c0e80c40011000c2c0da51004114081c0c001d040c41c4007942000010000c00e000d9040c0d000e10142d19409180e220b0400803410644191483c0410782c0c07600404032002e2000360b42e400c070110321400d04001102c5410380d4404160071150a440e40203120340e01c1030b084010702403411038805420b01d402924100541e00a03040041e00e41c0401c50100324040410073702511054440800080d01d150403000a02101c04c0c213900392412581c0f51040c0c864403050500c0002c000e0203581d04d1809140c0106021100c002c850201600c40204032000e41403c41e40058 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 757291744 1250 757290494 757290497
    0x7030b04110c0d02120d1d0d0e0f0d020a0513020f0412141606030207140a0b0703060b180607020316180f060b0306010309020310020a030203061201020c2a0d03 70
    0x5200301000b800f000a80041d880e0361006081c42e0049102c001c01d01d000d0350400d4400703191206c1760060401904041c8180315032054089506100004c80010900159845210f000301d21070f0500c84450f08120f902e110005802034518141e252418040c0035801030420410380c50b0075801d03c6000b40800c1c1002c0100020115408141460300540c20410394040b125507062805502039401200c000041c890420200c0342d031400d0050302c406c61410700d409e400c10003200c201c01e40c3c09006490300801c10b5002a00e40581c0c0c15030ba0400000e40c0b01c90007640c00e486212261040c495142019059a1902c000100b817690b10240a40e035000028100130300084181ba000003290041d042c0b8800240c0c9000d208059040001c0c850501882d8176008101890f4400940342e80c2c101901c1d14140000c1d52010816210711501c01e010440d541c2d925800001c0c025003042d6004e1348107045140c407440610300140217680b041c0502c04003030700300c00001140d00c001c10981c0d40c2d0007031204001141d1440311035482c2400400c19600a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 757292994 1250 757291744 757291747
    0xb040f0219030b01021507140406021b03010b030729030c0c010e030a0f0f0c0b27010b0901051210020d0f0f0908030712140403030209010f0203030402090f07030b0411 73
    0xc0116401c0400000841c00e020140f50000a243c1a17078002190030144101c5910107403151581d25044810044c801c200768001d0740c0c0007400003079a40d0300040c0f1282840c0c0c098110301c1e2001d150010142038aa00505c4141c2c103600042c0144910503c0025040140d01c0d841c41c101b0042420058689481d0411500030440c0078010a1b4103000c01c4c070038041c6034052a55070014607d031070088240a8a081c00101c1154108001c0303160680800b8040c44c1d90403162a04850f01180d03d291a0000035a00c942100102244004200401c0c1d201007050050f48a1040c00500806150b8204814400d00ca04851440002c510a5200d4010250302c00d2000346582e01c10a034001c540501d1503002e0034240ca984014102101d0310344005035000c100090140c0b50010300a1030281907011021071403230003408640908600d8007140c4400d0004161701640105929071081e00d80c2c130b440700d40e1614180e8503408202c030040c1d004403204001030009502034000315030010342800d00050303a0344032401107021241800e0403c0500d480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 757294244 1250 757292994 757293007
    0xb030a050106151106010311030a050109230609030318070e01140a080d09060806030f01050906010509071b02010c0f1208060301051302060f0c1c1205010b0301050f130b040f02 77
    0x40c42c10f1114103c01c1401c02da80480d503850070540c0d64140500c0060802044410b00130301581d404d03c01018030a40ac900280544112400e000e40d40503a04140410140742c21118803102030f80100e00170303100d060414050350a551b50103000140c0c49800803402c3c9030034054550301003846a07400c0200d034060b042c5400310030851130340c000a0040e41449a0030218241e0312000f5003000c102c0d484401c04098800320310781648a0745629001ca403038a0808002c2980c25401c10040042180002809074100c9404949190306038803003503001d0307440c0780c0c03607000c0c0f8186000310741112409540160300c0f0030314041c4100c0201030303040c07181e88072181c040c030000c0524400102c201052010507d02405415040010105403003042140ca80c00641c80d40300700c1800750340004001c1039802d44c40c030701071052046044411070070200c444021100242041c0c1030b80840310342c00c0d1134000046085002e500c00e6034180c45018101c0c4a005298800700100852410f1f480d0040c10b8039100412202d807500c3c02003070583c454440c000360701c925 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 757295494 1250 757294244 757294259
    0x9070e09030a0f031103161107090f1d070e070203190c021008151c0b2e0311220204080703020307150905100509030102070b01050301140c0d0b040b030a050106 70
    0x100003410503400c00d8105580145490a00b400b00c1750031019050642483c4142a1f1060752984e8500c918070035240510b009c00600340c41907803c0a0036440070030700100300d01d104082c09014512004201000181e01c09201400511650040785803c0b0300a03004490400003200d54000c11914010f0300c1000140000c26010214102203141c100707888482d00b4400c2540c40d1419092056400c1ca248061140134081c0c403101061200003c02c4034526000340a5001d14500b000440e50300080c0e12a0500e524900300aa03524440b402e01080e82c1030b207030700191006402101ca0300704108020080d03a07619000c903103040d02c110140d9481c4000c0006105440107031604c2d9245004142c00d105181c0e000241e8000000700016031658084c8488098850890b42c0090884021500b100c00713015403034610750550b10000e030b540103101c58103001d94129101240203105805541910480f4041d05640746208403105214400403a4029000105040400341c000140340c031a075030000b854086080c1060780c1c1c0d40d545807424400034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 757296744 1250 757295494 757295507
    0x3080f0c06040624030816060b04060605280203031302192402031e130306020f070b131104020a180308280905060702061c06080601151709070e09030a 66
    0x621413201c041c83e20f141c03548030003403003840c4c00c60b0481001001d0a42c01c01c100c680c02060709240c090010000320b500c2c0c45d0060300644c001d1034202c840c11414146160800361a141030303080c00e245a4095400d580361041013100410401000301d03403281440241702034414464906400804c1d0050101c25100a00400d41012081c0b0540a80031074004120301d40840e00c0b4080710621003841100400d0f0742d43c110001d1591071401603040100894000946040d5041c5c45001810a02c3c0c001e51102e01c060b04d401415060317101d058040100307003d5071400401402e14099001e449543c0d0075050000c80494550700c024218413040c1c00131503401c900411000d024025903071030075051000e4214186e14001c03032900042d100c02ea0702d1003420701c200c000003448800c544406050f501d4003083c243e68900d40e6003444180030054813480c041c1501034440c11000040b41c1200d040840e42c14941e9440300d40504100080007582d025000b48050918403480c00005640515a80c6180c894510a0040c58a44081c00d0004100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 757297994 1250 757296744 757296791
    0x90b07121a0d020607050106180501030201090914130c05030a050604120926100612020f010905060f03060604030f0c06090617151210060801050f1003080f0c060406 72
    0xd41803102250881e51601000b000340260100d130140d480d803035185000b03405800a40c1080c0503500c21340c03080007106001034001134141d0b40700740c80d0b50120380c1d140c4d00c5000c02c480300c0c6500c1912405540303011940c3ca0060b01c01e020380d0a4040c0300040746868071500400d02c2d061408804a500358081c1c0c08006c00c0c08241c0803402d00d080c4151030843d406914200b0000303440300101c0300700c0070060a82c034864807082d6000c01070321f01610011346040c803603a56130710075150348000c40f80d00a80c010402821030171125031094001d101074490051030b4500700030740b0394603200310b90b00000e120340d81150701040040007065411000c401054411984801ca0740c0c02d21000400b0705100d64042000e102d0090010703142d0902c07010855601030b5850403804500002000044c0194034421081c14160003905901c00f00002d058200301d013a00c81f900e000307001c0f42e10b4400c0503c0207028115070b82009194401c20500020340307800003c10b00c3d09001c1c060103052280c00d02d2203a041c000c081d9070840320b00e07030341e8101c030796406040d070441602 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 757299244 1250 757297994 757298021
    0x803070f09081506091008060c0d050a1e09020d2307090b060a0305070e0d0507090c11070e09070306050c040f120f0b0c040f0314061303090b0d090b0712 67
    0x954503460040e882075010f02511309482a894400096180a0348445000c000c1802d44221201030611910100481d40440e48400d8134074101000101401514010300c0c04854040100c681d411000516500080c9080c1702e089a20120160b0300d030000c51140f18013880c02e9800b0031a100d0041e40100344407440e103000c17680412031540c20030340110070595588003a1411b8143c01d01b070100b0950b640200445800f4100007105a0220b121240002440000107079a801e69040c130f9010006584492030075506030781500c011100ca50b00410003802096629011242c204c0c0b8081e04407101c003520707940c94005403101150b141c01e10300c1c4007083c00c00c01e4030540102e00d8024207401c801d1030b900c13a00d15241c001c0d074a0720002e80038117106aa800072a490814540c01c071001048071081c0342d5030554881c980380d040e0503d080c0c003607100780c4605000f28880314030000c1d07001042c5074075031142482680341151450300d80c0c121408002ea0301d0342d103441900106042007031a0348620380c00d9840469192604000d402150100c021640 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 757300494 1250 757299244 757299253
    0x203010b21040302120304080f0c0d09060201090221010b0d05011e06030201122703020307120e060319020403140606100504120212011508070e16051b0a0803070f0908 73
    0x20210fa00031654410170044030311001d40ea0b41d61030a052555104600302c400140b40002030380c4102c2074010681c080c42104c240c3d90003803011351300c4800b2402d075411810040d5000104880e5004202c400300e0710900404410340c00450150b9050000502c01c29006405442d16510784440b881d00328940c001503440346252400400c40785040d0340000f03111302a8507d004109964802801074014568001414110300880c60a09241010b18009480b600600021254001560600c40107180558943c8080e00c0014000509640c2d5904181003140007203016101c0e529400c010200100b44415500001110700d000240045d0511740e060102c000c0311100c6080800c0001d001c10700100c40140816088160112085120801c00ca60a140100154a003808505110780300008000d02e0208041048600c841001c58103507894500d4492000e000c40402c00c0000c20822815644640562040e00990003002c1100e1012000d560307002c940354020380c1d000c40407a0000c0407010030103a001510710064100c00004e003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 757301744 1250 757300494 757300501
    0x4080d1b020f0f040c0e0306060402030610052206110d02060903221d0906071b0f1b03060e0d110a1e0615180504020a0303050912010203010b21 63
    0x1402205558000900c624000c8451209a03500d400c1d00a0fa00080100100912011901d020b003070704c3d14402c15039029001e8440007072030380d03d01842a207100c0c0002a107161580c5e000d46008941c81c1d40900d00c81004044c1b8440802030311407201c94040080c02721904e800c88229250500705241c100c182c0c0000702154030490070445200e0020050701e4000c16840f05692241c0721030030744c09030442a075402044600d44034200e04021109013541283c01446281e042e81c0068940b090111402e1840000702c0e441055000140384c005500101800f44003405001c0c0e0208c08207400d444d15548408d55801030350b40f103480340200014254103009050041d00182000d02c00c8012010096840304881035020f801c0e03c00086117080e9a9801d00e2400540d658401070800500c1028180c01d25000911300846142a00181c4c9480500c040c601c592801990000c007418401d078950b07070f401c41d42a4800d9803905d4100921020850080300c1c00d001031806060504540303601e9020680b03440460201003560f640c203110102003071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 757302994 1250 757301744 757301777
    0xc131d06091f150306080f010f0e0d05190318050610122301020906040602070f05220f02090a030c0317030403090b09060f0301030305030a0e12180a05100504080d 71
    0x303044890b28083c44407000c200760425401421940e110043c14041c8049107100c0c020b06600240da015030a140c200615040350711840d9490700d400d080040071400400880398142c95800c1d8044100c41185004103c010015981d09102c500034081110b099000c2000d129120700b178000444c01905040c59400100c141c07079200c00040003003900800c082c4c000301c2440d190784130381d0030b40440b5101c6c130010709146c2d42c41c2d9440303400039520205485000458010468040b409107840300034000b81038003500b0940d0307003000d06c1820030300100440c10b040205e1039401c0102c2d840c3354480c020000000d43c019494940380d54518101020481800c11a10186c03800410800c0b00083c0c0000a140036520704031900c03601c9a0010000ca45c540c41000044100714901000000400d980800154402c00102405004081240c2910b0b0313515105450405140c2d01c0c28421480e508480482e010152080100300e0404540c1c0c0b40049000da115080301d03240069000a801e00c08001d003080000003801051501c0014400d11014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 757304244 1250 757302994 757303051
    0x606140333150a0b1909030c0605210a140a050709060c051504060e1b03120f090a060e150406020d0804051005150f06030405060c131d0609 61
    0xd024a02140c4031002c152610a95209124882005420101070702d803031311102c01c05074201040e00c07040c130b42500c00c0a00225101e24200030441c3e9003c0096500e49084c0f41090b5880d8100c1f0441c103040b0700c209619414850303185140e15008506078080040e040344101a41a0140c0c40100710380e49050a1034180030303c103544048950b00f103c07100e01e4046601c0700c841c074280d402c0c2a0500c811044040c00902440103205980e44580d60b800c041c01e040315100d094240e004020038910044066140c4c100746101c3d1440d88486000308525101107090380d16142914000401090a88c0c10420014034588100c501904104004428021000340d0303850070b251a05c1c0c002175803003040c1c100000070400c2c0c6030041810030a003005800c4e88445c108100f8801880c003c003694480984d18542140315064202c0301c10a40d0904808070390240c0e80107000341c030325590389120403600c4e58007144000a01441082c0d00180d07a04096030580010a403042102020741010740c2048112440540419031501d40c0d45801e0494406852 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 757305494 1250 757304244 757304323
    0x6030c210902060c031c0b01020a020a0b030c090d1406010b0414060d090515061906080f09150406060603050a0b010509010e030106050d112b080f0706061403 69
    0xd000c0341d007107160720119006004200d50740851384004980c89842803804078550017030380000c4004001c00c01c0507800480e96081c0c4110003941041800d6004e11a54050600541d8001c0810710914540802da00c045404c4c06401202030300e50021044030541178182c00d0114030300405030700c4006801c2600740060007064010650301e01d881542c00080580d80300364a50044043e45410130f042c1c443c0c0c1c240004500141042c02c03a441071050f00400c4103000d4459107007500c40e05440b06c5a40e040003030342d64081402c0440c070001d010045a07105500e000d40081d541e04056511951240d003012078110b16045018050383c81c081c00c0c00b2081c6080c80304c028003e903448001d075440c0490910f003030714556000c00c000c20300409003074000c2c3e5041001c20354508180802c1c0d44411f4004c94041e0303464160985000140c003640d40c41c00e945120320ba0795558584d0041030706c0030f026021071000d1001107442c3c5125559400e04640e21644528003503004410b51407080c1c0346c2032040d942c100410400348107012000c5c2e00c2c0c0008054580 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 757306744 1250 757305494 757305557
    0x14010501180504020103060b03040506071202160318050307260a1101080612030a020d08060603100501050703030f0204090c03140c0a050c0c060301060305040c080d020601030f240606030c 82
    0x2007001030b0640e0302c01e1f0441e00090050f40c84181e46c905040c2070864644404882900201d808481c181d0001420ba100300c6042c11034020030700d4404103072239030211f41031a028003600001410703d01020900b503506207c030a0013010302d540c070340c8000c1311081d0359284036050000440722550400c0d04500042900c000d8400d40c0c2400034a01581c0982d02c1800085506020307032001840d511001c94dc5890311500055482c80380c5120b5210f1206035920b100c00c2066910003100c0700c0d00d074400d00c4082041554000c1d40501643d40c824100460801c0c8101c203d00100e80150388412038071074440b021059a00d40501c104030b00d0103800683d0310190315010401c0041403240740048002c0010008040c011100180601005509c008203466a40d50395604002c0281c502624161460017060400141540c000188203007801059000f40109a00c0c0d41c035100001909000140c07404444050120302d5002621440d440c0c0c00c0044c400001c02d0b80c00c0500040450fa8120303d124180a254400303000c1c2c0b41100079510b89a4240c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 757307994 1250 757306744 757306751
    0x70c030914040912031e150e060d05030c070e06120718020c0106090f1107050d210513030306060e012307051b031009080d0c020106211401050118 64
    0x1040206004202021001e8560071a50401c11a9240c1c503070840d051b5165012410344000503034208400031a01a5081160702503001d003010400401c402d6001588140c00505040302c255154540d07900f1544503001c00c080070b800250090202a020009042c3c000006032200301810200c542c0c0da50392000720303000e100c3c42d800703c06005000c45c40080d011181c5150b003090092010a58500030040038100200031001c50701d0911601c201c003046001e041d21502c541100040001100e50701054804a10188070b8114200c24004004034204160094070301801081d244a000c030003050400404680041c2c1145041043d440c50403100d036070344806860000c0598003450725001120408100c89803144010044c15405194440c0781d901d81e649039500d904000640a03500700c140d641b01044121518264000c0c0b80c070000b0300c0701005402003a4003039405040e0b24000001c100b9100c6a110108040180c0c0480300d0071003500c0c900041016110034046007204d081c000740030039414110400d41c0003034284017540031140d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 757309244 1250 757307994 757308029
    0x306011d0621030a090e06010f0f0c03091505071403031e06060c06070504140a06080103110406050307090b2805090c0d061202030d0c031b02040603080f12070c0309 72
    0xd005199031040098041203c2e550700d826071029225151a1103546d04001c140000140d26500403100303948066501d50310542c0c0c0f11900c51083e903004841e80b800707a0801c0f18a410116449603c0d11301141020f074991a11034461a07540380100301000c40307140e229110b400c24820310035054581d4940e134581003540a0201c7d840c2d540c00010400c503002e041404d501c80c0c406e01c400c0c4070f016604040204203482040300c0da0302c803407100c49007071081020ae284100000034801d0001000811031982e0300051500c030090011480750798079400249800e420703130407c940b000c4e0755008100726898071180369404d0124008095400c10003c0600c0026403140d8030a00d4050130f10000010056220300c400c40d4032800344480e081160300d4844168044241d91040704038060700c5002a03030072a1502450900e69002d500d55035011800c5c080d4a00c507203840c100c04008981041d04c501d004000590f0301e601504540da03d00584549900c40d41c0650102c6450240001044c801c90181e0078010940c0030241d9800d80c2c91110850074003c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 757310494 1250 757309244 757309279
    0x150c03110105100f060f0e09073f09050604060c180f0303031a0d03180302090c0304111c0204020a1713030e04060609030605040512030f01050306011d06 67
    0x102203030020259501e801c080014400c07500003504140c030300c11662889070039154075068620f46198082203000c50708072412014280341650410b03910602030305c0d243c43e0015000e2490080d404182d009044044101c0b00364030752404990312441090b01c000d250500043c006074503096111a405080502400e440d204a5401c95005041d100b4036103a0010800c450780b40d4030000c483ea0709020340011070010b030030300d507480044c00c3d80e0352060510030340020844200800242d80960301036054003420300c140035280c407002026941d0501d461380f1490038108290741d43d01e0645001c400304408140d54501c2514100240c582689002c1039420f60268141d0380141e554584020580715850640d00c0300740c2104c0d4000030040c50801324404050a54070a80394000242840002c01040e200c0f02c0c09040c0015500c08420804142d840d006150014000c20941d0414041190545040d900444205008141c07600c0104420304042008500504982410010260500000780a1540050050362003801e500c401e940012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 757311744 1250 757310494 757310507
    0x60e1902090a0806040302190221100c0e031606080103030809010b0d060b09010f08030901030518032a0a1a04030909020c0c012003030f070509060703030504050d0306150c03 76
    0x50300c02000212a01c0d41d54071255558981190120014042d01c3e0055401c02301102c1c00c0080e5540c018603606a11003100d50441d0040c00459100c0451702c51100c0584000009214120b00500150341d0513050501d410185850010280c40068801800313000c1003200c40d510514950540ba49840c200c186130b102d00e509a4090320b8810040c5038402e5004500b0420401c1c182c2c00540264810f88480c2c8580c2c0e80d442d001407105525100d1010307a90401c0000c0302032584240c0c0119440204174a90300302c100865600075145030000384d049031a05502c43d0581d100081101090180b070b1422200603d4a5050b03950341000d07a118540403200001414000310f030815002c2c002c040044c3c40403000441d100c3d0285144155100b118034810303804183c040c812088503940f1464091403144109004510f56115204000d40c2d40000600d03001c100501070001e12603035502d004c02050501d010355004166400c1034105182004102c20110060601d489001c11003200405020b520f0f420590030201800001c504013a5840c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 757312994 1250 757311744 757311757
    0xb151306080c131413091e030504081b0915060a030c050d0f0f1404120507020114120109180309031e0606080307142a0a03150f050901060e1902 63
    0x40f804450115094055003181c10340031034112001c01a40c402c02070024111100308102600600c0300180c000721040310101c0103031030540700c2d14141c0d10f001e80e07485105043c00000f100da048034909103d0840021b1801d140d0b60343c0c200b82c6c1400f0701c83c90800a1000030b91948900c0701d0304400d041d20b0341c038120142401034091391599004034105111031040614140001c044101d41c0b81880b0b40341082628140c2d04901c1828456944403007030002c2d6448101041e61a0f410141c2c00300e04006402c1c0101580201c0c02d00548200c1048804c040219410700041d14203807942c0103c0402d980010760601c1c804203502c071041d101226000440060340081c1d16130b1508010550f40406810603003054000103084000100900560303000350b041c162411a500c201c146ca840c00c814403055281010301040384ca5084010080400f06002010314640590742e80e9050310840340c1c1a091140c0603070762115003503e407919018072913021130201c008104503800c0280095040c000584016003501a0301c038200c0c00554241e044910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 757314244 1250 757312994 757313017
    0x210c07050105090a050d020a05030d0e030702030321070c240f090c050a0504060608010b0c070306050c0307020d0926070305010e0a1209140d150f0b151306080c 70
    0x199251600c81d9944d0380c070081104803031520460a551384461310118075096a150b01034003031890a030803420003501504180d011034880380003c000080050768100002e00c0c50642c80030310300031050104061000c000400030005800e00200e00705900c00141c0545c48401100c5504003558051a1040c52003c01040d2402403513040d617113401140c3c0280b040813407601d812280100d03030b000b440c81c3e01c601c10b00064440b030303104940100301c0080c0180701603140702e00500629039001c07040b00c40c1c890350380d1140d80984606a0314120207410010500118a50600c4a01104038050900c200e405103000442c43c15408100780d4801e030012201d050b2031600c0c40c10312a0304001c5801c600240481e181c41c21000307499980b035030411913500035003030303401c0040c03500920500b0100e41a04082e01d20680c007600c240101ca1031001030032947c0100c9001124001e01d480e22618030000401100003403c141030340305100c1c01c0310005002c1c48d0030b40c10912101d2440c3e01c0c0032012006a4480340b031704003429120316140c1101400340a43c040c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 757315494 1250 757314244 757314251
    0x60f1805030f210301182307200f0a020d060f1401050405070f051c15030b0718150507060b040f0f0c08090a021203190210182a030f050a17210c070501 66
    0xc1141c9d02c200c0c074602000040c000b042c1100d0071145440e40e01c152140850441f9042803c014003d803600c08000c1d600d403030082ca0041900440f0804003401c840d041c00b400000011280014000350819100c0e0329803050042c18180f14000b0700711000340460141512030400801041c4105401428903002103100d000d850010403085500c0345451107035074000321580000035003003011500d0080030b85003441044510450304907200e0410400110313a140e01c01350080d10415110310014910b61a0740c850316030403040c07440b800101c3c4c0a40c0c0c000401980d030604503140c2002000f20602041d42d0300030800301100742d070443c3c0c0c24010015220219042d030040c01d10b2440a0f400241c1d40107000703030300070620441150600310204121414214000b8040b14008400352000092001380541c0405501004007192104005020b256035641c2d140c1d80d40c1c4104030f404840300d070080d01205042101003503164880051290340141841c400d0020089101102036205405120340320209070070524050031030302c005070070070001d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 757316744 1250 757315494 757315501
    0xc07060219031b08160504050303030403020109110f06160c051009091104080a170d021b0601060504080607030915050403111204060f1805030f2103011823 68
    0x207191042059690000309040407078880a8510701c0890349018a581e80301c4807400d842d0003503100c10b60070485403040180700d810003010513507540803c0990312441c0300782d00204401500d0700e8010701c619040c0045900502940f00301c0c40c501d0fa1820162410750007030800d00c0c1807041072814000001c501035403045801080c030035800201a507202030100182d4450341014080482e449210031000e2003680b140241940240507400006070603d4400c8200c0340d03080c00030504185020480400300c0e408454500074003c0d21005c01c0078018400d101c01401007400b8109035040900c2c00c5612501c5102c000c040c1301c209961000b24804104010105200380180c00000300b10720702d4140b03000351203c0007038444607090740b041e510740400c001c40300012a02511407a607544603160420b01015911480c514116296050008074045a9034400b0082c4010f400c501300d0040070b00c083c400e042c18103005204100320300203140c2040180f01c080c0703c103420100000741c1000001050b600e10860000070b6450f554034a400740714900e060 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 757317994 1250 757316744 757316767
    0x2506021c0b090c07020402070303090506090141041718010206060f060a031806050c090108010b0c03070f020d1202060a0e16060806010c06021c0e21030c070602 70
    0x10441000000310041001103000810041c51810031514400c011000304082801400d2540203002c4052181c00e02180c40c210a640709070038014101c4841e206695185608240400f0f035000c075515640405182c8460b10102c40c0e0304074640e0010a0a10084514901c0818108205881258208030441c8035807030712001c1c40e1500c00d18901e001c107540e078014410b40c400308510303241c000001c00c0d0b034140007400e943c6003200b0444107402814510101401c2440110325010200360140629803040c9108080c4a070313140d20020003d082c032001031300070098240c0d0a002182020200000b10350803960428030764060707159244005080c107555048000c0084510b02c610018107a00011424007d2400d41414080c000c4c8403490f8659a84001c0341c500b00914024208006a41c000c401a54025506241c4550102c84a484100590703000c55071440003d510841080010380300ea02c10041c540359080040c10700d81d01c00c01410040484640a41d0480a0000000c5620418a80f08a440c2d15030321840640d00c0b00c007882c2c10b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 757319244 1250 757317994 757318027
    0x5071b080405040c08250e031006031a24040915060302010921170f0301120b18060619050a0303090e0604020301060207170106090603290606250602 65
    0x1070503026904001008444900441c400c41c466141400072050740943c019117a60310751b0301c0215000902260445804054400b071200020310050524040341140c41c600d4407608c3e91040110007100703052124180007070004440b0440c1d0000d07040c081d070411028000000180140700c0004002c1410304060b840300031824030350b00310b801140d000741c0b511100030307588050b44084603001550100c01d01e640400d1103c0050071042d840d5815420b078140841c102a52a5043c1c0030b0f5a10070b820503400000103841c4c07281000001030046901c580c1000d06540501040100070b542c458014042c54441d444800c02101204000c266041c01072800500c0b900c0d07600e41c0d906014204803401d0081198441181d80012054240790085034102c8071a54001c1440c1460030941600040741c0c000344900039502c4600002f0b0380e0b0828010350f40950b00525044032040c04810015407600c08981c90509030501e850304000c1a561060140c400000505000204213111400e107001c01294608004100e01c0c40841c0c8000078548021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 757320494 1250 757319244 757319249
    0x5010219020328120e0f0105030411190f1e170c1e0307080a24020d11030a0f05071d0310060e1617071d030106091a0f090a05071b0804 59
    0x5640c3d800c0c034003d01303500303d400c5401c14100607003010000a030401694071440085900a0017114000744001c5014009101422000404100401400303070230310890007148403410080403200420003403000c0d542c801801d400d03000d20070b07804c84690701d001001c400c800501c01d168902d08004c00a03002c100340300b003c008030200038000240c0170384249280480d00c0d94000a9640c005a0040705203007003800810328031011000442c507003010981d000c1c0580342c0035151034000c118410f50340303003251500da103000c15180040351840c20107180d0990408007805060761304008201107802c00b02606c440c060012a01091804c1c41d444d405036051441e00f20006038294004205900600d02d1342d4900384441c0c101da508aa8442070041116424006070020030303070040c01900e1101001c24007000d50404580302e00c00007800c4070920f0b40700481c010748515070130075590302d03548150038440f03011a62452a003034603001083e08204014444c00c50f4590340c1000c50a070700d02519030880381d038004e00b03034100c0c403d20303146045141e9410a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 757321744 1250 757320494 757320503
    0xf0301141006031d03122d04060f050f0105090a02070507080a0201021c02032b291c0f0201170c04051f081303142b0605010219020328 59
    0x3074102c0b60001d0381003120410b201e03202c00250704001501b140e0514030500604540d06400d03186501c031064403a0025812541307514a94690000d28150500c0002e507172501d8417902c0c03814600410000c011044030011815200c0558001c0c942e40e88031441800240b0a014001c1c1461180e0300c40014444800100d480c1018400e83c20390b8111a40c44c200400b25943e0800f4410158209110324407031041c2c05c41e180c28007000d68030b01d05041c0c01349030a4640103c5140c041c00100c14203c040125000400540000c901100f0658601d096409a50100c15071030507070b2038000b800d103210f1455410035a849074480708103c3c0700b200030040301d50504a203a21015403003441480e014800007103850610507002c90b124a1481c07516203640e440740c0d650344405108079405800490038804002940304504c541c034005000c02a090841c405401c0d011030b9051810320a0040110074420b0800704240030903640490200f20f280e01d210700b020b1003403503244002400d0202c018030425242d2800300300048140c0700612464000b6006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 757322994 1250 757321744 757321751
    0x509160f05131803140720031e1506190e18030a1706030a0c06020703020310063006020703030903110c0105040b0d06090f2a0e0f030114100603 63
    0x503410b42c1c080c1d50010902d00000d1458a04510100c0d010380c2d81c484411516040552908000340e9405030012070085140700102605090400ca134102003100c17203c1468a01074000030440e6015803035580346405a00c401c14240140701184050302d40c4031000300e46210f82458881090703103661140702001011100d0090300e003ea400200b088003c04000c896951089a139009148050460141c2e85c1d0340300684107a070103114400c40203000c103500000600281c101c41d4040c1880a2442c01010b02d043d604244564a41e4a06002048815208800791a178542c031954441c45c0f40441c5408003403007509803c000f42030710303000040c524201680b5501480000b0b10984800d8001003110940c2d070380d5051401030300341c08648104000e001001200010300281c0e82041000300b071041e04c49450f00113941100c6802c00080d51105540b00117401c1c00c000540070843d50001c400d0401d07011110040520300618625402001c030510101020345003900a418140300d040c900d41d9890406600052610f5041e01c07500e8006480c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 757324244 1250 757322994 757323019
    0x604090b27041e020901060309080702032e020c06010504050403090807141305060108010303050f1315081b0d02131e08010b010c052d06010e072a03030509160f05 71
    0x1820404a0541c1d50050500c1c5e01585c02c0900a9004106504007580e135440b05102e91b80060f40c0800004d4941c3d1888000c079009121200d402102070512440810801c1e0b0042c001c2c1202c41d140020003034111142102c0128035500c450600b030724400c256401085160260110105022850041000120000f590300e140303460b078094003260440300140c611a0008031207000400100344074201818180d12040c5a181c0742010014825500100c03681c880348404021280925042c0d0300404000e034410360b1180902c0c11048500c450020f02d01c03440e40050078040c0c0c045070443c0116140762210016159807246084c8440e600041d5022010980c03280714041d6081010400c120b51041092412081c1e0007001080400c01030400c0501c0c0b5480014400101c45100510b002010010131100d4000c082040101ea021705041500400450703601c0c54034a140c1d0300313900d5003001c00741513800743c40e034003982614001840f61102042141820000017070b8444182c0c0401e40441e400c401c3c4003200e411118204c0c0c40131342c0c40c1d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 757325494 1250 757324244 757324283
    0xa02040f06030c12110c030c06010e09011404140703141b0102010b010c2003071212020a0c290a09080c03011a150f072f0604090b2704 59
    0x10411040303035000903400c2e44c180ca441c10580d0091003108080091080c1040c481880642c1b5603000340b0302d08125540031800400602110a80c201e13000b14507d8002e02003040110314203181c0c1d0902a10080601070340c1040c00f0680401405030201039a8420456103010b00131000242c1e0321b1314804031301c0301485070f801d00b08103c035801403250358450401a11100400d81441c2c1740d004c0400c0c100e84140c03c02c0c0d0a4480c656070f460303501340000d6018110807450300304103013043e042070252108085a403134195401822072034045403295280710122074200d090710130b129090a10041e40c0041c60850141d50340408581da0680c0350300a1400000e8424a10444044244480c2054203850718402c07400100011031a605056082900200c00f9a2800e07407003d52402c0d840314040343c030a5216480036107024a165448141049814514010100000b140c0030000300440c00024070a00c05e61041403902d554440c03004d24691101c803010614140c0c5401d02040461084560525000f801c030b6085602040c403130714501004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 757326744 1250 757325494 757325501
    0x31104200c010e0d0c1a190b040b0406030503120a09110904030e0d0b06040c031104050427030c14010e1213030812040b16020c0f0604171c140702040c0e090a02040f0603 74
    0x8214250f207104503c2e4020251500500941d85122740058036820040444d450702c0c010f001c01907100b80025603070341421240e1904006001380c410807502d0b080182103004504c010902c0c15598800720303098401030301e6600e0b05071103142c16000460380001103030a841003804605910075201300301c1510140311035030503090114101c8161510040c42044144024000d60410f0f9001904004007101070f403014001c2c912180688024051045001910b50b05080b02044099030504c0300c01580d00d0005e0111080c6180030303984071105090002150080407582e40100b40c68400f034800155081001c49030780b05203401000c51002c9040350142c6960090502040c02c0401140490b200f003005c44e4040c20000030032a0411850800360100d00c2d0340420180000306100e210300100c0040701d15410018090303206100d03a10301030f05002c0007494091000814680413910790180480e07201c0c550445000480110309a000d8078140b40c00e42c4a150411080f400700f00035200c0070781c000c05c15107080c005103c2e461075071404214140c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 757327994 1250 757326744 757326751
    0xb07020a021c0303020c0717010c030504030507060e0715030b032503060f060e0c090406050603280912080f0f060d0b070c0813031104200c010e0d0c1a 66
    0x1c10088002050b980700d409100841e094480d260242c50941140240340c034004083c0c00c101c0200d801d00c500d00e80d1266007445131690340d40040c2000e00040c9056200a4030390301648034007905407038440d55403050000044c050b0501401c200800004140c0d5040701c010300800440c19510b0007446080382e0031981c1d0458919001c1300144403881c650301a8155035401d009001d1682c0c0d402d00890301d42d080480c58080010401d0310402d0b80702e02c8142c40e5007402d0200f006071401580014040d0307600f00b00784108284c0000040381c0885180111100c05001007400074001c12070258040c00c100f400c1c0729146001640414194019001c080044c0d02130389a140c010420b6a0301980d110b54086030400030300c00041c02c49421240d112509040800208050381c0b14003095600c8104024241c00c0a04403c0c000c01c2441710480050703007826641004060303405450034800d212001c2d0481c2d490384010030286078141e000d4101c481d2403001034054403c0b444000901404011010804490910704039801c200d11140c1ca640a511 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 757329244 1250 757327994 757327999
    0x20906040e1f020405150306031b0f271005030d02010c022d0a0311070803030921130f030311010e21040b03011d13081c14130b07020a02 60
    0x4920718503492400c001168121442d5496024400000c0513500c802012401100c40204070303076a86040001c043c14003c1010081c038009000814041d101c2c1c8500f02e00e004507031403c0e105a2081f00c2026030152400c280c5030554940c8079244400c200c3d20b4600383d05804c00701c6d6004d804440c000725580505070b0a0710f4061508a0060740301d802c046c01040e0305a250788620101d030101030050840c80481190030100740c0c0b80160046040c0c00620300649508022900003410881301a5066050403422141c840c04200480d65150004078954000107100c00101c60640340e08c207a040c01520380e13881c5001c0100110f480305501042c900b010b021400b81042c0510308011031501e0240c2083c2e01040020b07a2080303020386401c040d4000c1030001141e00c0791a54025406031050005540d00c4060b01c46e900541018000c01a003031081080340c0d0075000807141c400303841d11844c011101c52100c1b0b800a50410040030b9001d400c0791201d01d01d40a01000c440c42082c4401818000d50810603c0d0703461140c00c0c3e0340c0d1440004000e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 757330494 1250 757329244 757329253
    0x60e01080a03121e090b090c150c0f0706090503060c210907080d05190c0c23130b0f09090c0402070f021206010f060f0f05030a060b0f07020906040e 65
    0x30020b407007508000c42443d000b100c001540403500b0100703407140309a1400c0002c04d50b9200821014821a401104d6010411000412500b0386200104040411030310340b0036000d400120740000c044400380090801d450220003100d9001d60340b120010281401841742a01138000c52000c209020300711803c440c54001c100d102c904201000d4001a0f440d81d01c0186202401e0180460100c1c180d40b080c4403496411000b6900c01c3c1d21140500c0e81070054103601d0b14a03c00380104200040002007285800c10100c480404902c1c04103541c0c3d1444004258002c81c0d0180d103e149071190362501811503105518801007691042d800070007081c10302280e080140c0301c0d24140c0d84100d50802a81c03806070010704400d44030711008040d240702035021941020602c4031141042d0081001031010f400740c000c3e101c00500035071402a5030014400006440c0c0cbd0700305031010042040001c005207a81c40203800040080000c110000d540c0c0d0b00f000f00940641c1c00081d000c0f4401c50005001c81d074585400d000b01104070400364043e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 757331744 1250 757330494 757330513
    0x3140301060806191a0405120309030a0f06110a0c06050f0c27090a05220206040e1305060c041a1e071a01061706010305240409080d02090301060e0108 66
    0x24200900707121111040d204c881d02256000d6080307800548000000e02c043d80301d9041104005054a0305a84c5032900d61080c401c03008555800260b030000c10b50094006c1c0703110039290800c40e001c1c20301c1c00d02a00150000044400343d4560106481505038000c0b07404002035100d1010210b4010b0b020381d50f141c0c180005009048003880070115003205411200000d155040745000414034611040b142c0d400341c21348d03d108011310640d6095030459180481800c54513459036a1340094040c2c090340c0510244c001c1c9080004249624600721034045582180c1100d04031700d0708500c2c00b8401e51160180c1c0c11000700050070404661040c43c152481260240003404503403844041880e003c0d00002d4060350841204c1000c1c442c04182e4000060180050341d8400981c034156480104283e44042c00d41c82c10145401c08020b0b002e134542c1d04000a505540c018540300d0142c3e0800079001c4d00350008080c141c11400510345110b816664010f1411540a40c028080c907a980c621190300f106092040c400b541d04100b401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 757332994 1250 757331744 757331749
    0x120f031d07090e161d010608040803040b0c0d0e10060b0a080c0c01020f0706020309061302030c1011010c0314070203070c090510090e2b050a080a020702090f0403140301060806 77
    0x3d0584050500031503044103070030064940000900c0d44900034840c400d10f5001130200c0c40302c514901600803410000613505040c0d40d4071450388030003000035103000381c03040200e800010f4290072540d07020000b42c4103205031103c0402d019100c400c4000034014580c50014001340c1121518180c5104455945a4054507694090485641d511106090b07286550800c5400040c296a2000c1d185041c000c510050b101d00e41003d41610303045001c2d090401807aa40300408005a50008401d100ca00040e201800c42035141c00c0c065806020342c0080d446c507542070040700312409526520854048140020044542e00c94034006c0c2c4c1c480c40780e1003026200000c000b40c01e200b10802030700031a030060300c19485060301d165200481070880d020401e080f401c540110741030421480320000d81100700c0d09440400391280c40c404001401501c40d482d031250034807201c1000038803000c13010760540e0021500688050001d24244080302e10307980d1304990807800318007801c00c007802071100e034001d6034180e031410b4581d56038a8030340d0001c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 757334244 1250 757332994 757333001
    0x70201050705071401091e06150f030f020a0f0801020705061303020d0807050d06060815030c0105030a1d0d050301030210090815090f07060207051c0804091503120f031d0709 76
    0x790b40180c1e64842110800003080301c00300c1700310b000314108001f001c4940792414200b03403200305101c0d20800070000c00c01d10444107140c90b11030840340e205400181c0d0200c1803010510516441d40034909209101d100003031416011340040501c03910030740541707106a0303d6081c008045580c506001d00141d201c1c80b01040741c64062844039821030300c42d04200d42044001221101581c08135001540051680e0741440405020001d583d0b0702d00d0b0044000c1c200b0440d0000000b8100e0100030841c521654954900220b8101d065010081000e8008250384506c0174014015159a000303200807400b880c00606135010071445143d42e081a00c0141020707104175001c250700d900000130b0140ca242401d0007a50054210384a040007060010b154a40140074030501d0300c001c100700072003000c1e83c440c0c010f255401d0900c0040c840b28100e03000d46203803580c0041c90203401c0464041040941d00300604040c060101c10384020b03080824240400296070f024003006408914524140e00c25400240580d8450324040c000041c0c0c940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 757335494 1250 757334244 757334273
    0x1b1509080703080301120f061e06140102061612090c050906011e032003090106140307031505090c060a0e0405060d020d030806190b0c0709050c04060513050604031a07020105070507 79
    0x80320740c0247d0ba42510352400311058007000101004e0721400054222034580250002000042e001c5000034541900103505e0f820018074410a40d50032402e0318021070301034107030306600c503014040410040c03981d807070060354401090007418071409180c0c000a6996101d130b0102301541034584950240c2035865102500a0103202450f2241d0040032a40e401517184804041d43c41085170400101c2d2003454801c804040710000c4071144e000340c00902050010905d8080c1c071900c031030003d150020742c41c1c0d02c2c0c140340c50409a10a4915911041c00180b4030b02c034650101c00c0010385201164100060b0321000100034009c40d440700000d400442d036040e0303403010a00452100f5172118028000c0d4074072440b0b0320305038041c42c1c540d5080311180103000309100c0c842103000c0043d40003412000c5c208110a0501008281c110b00651080e04100840041e1035020500a0070190b0010301000c3d1843c1c0d10b9503100c0c42c05c007a066020010782c0e42c030180d411001800003841400341130f004440b540c440078a8004607840c2c0190208019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 757336744 1250 757335494 757335503
    0x7030507090506150c15091b0f1203040303080702190f020907120c020102040810020408060402150403150b24040605181002030901090e010b0301121b150908070308030112 75
    0x51403c480400c800e9802443c03117519580107001d07050846481d40d500c0b40b4020300b050031242e214103008105110051500c8038845021035401d036000901e80001112000b41d0102036106e030101080010425400c055071601616040c0c00342e0720300c110000c800340d0380c0c0c400a4801a188010b2100c040b000b509100800942042c0d03a441c0c031400100b91084204183c800d03c07441480182e50000c1c0400540c54107022481c042c05240c00d042d85400c0c6407520069030b403840500083c0c81646201d5040040161007800c41e00115880003240b5003048403100c0800003090a050b82d00c0c0290380031031020401c103400c2e035a00c21111511030340d11703400d083c2000c000b2aa6a00074410030b0100e69021a01c10206980707540201d02c9541882c0c0c021552511644001071031141c1c2036100700d01e94482c5e03000502449107180e0590341036621b42007991071400c24a082c09088800d02400080c1842c29885011891040c034205001c55481c032a1070b0441d40c0b681d118881c690302e01c1188030183c80c1840c280b00610050b58204042012503014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 757337994 1250 757336744 757336759
    0x4180609030e031c1e2706090e0408030604020306010521072d21021215061801032a0207030c0803090a150201060315051b0705060402010e030f1005010806060307030507090506 77
    0x10400d5a0310703140081360600b20418901c1b9080040300c1d8071510000c0500207403500754295003056521041c00c0d00014001034810b80e0084001440f9922442c00c1c0d0f603561031715041e489503100d007200c10540da460042e00e44000003040700c1c1480c107215020807041d1400314003440c02c0b0b001601c0300f103038201e803a01600012000c035580005d81c048013000c9180064804c10814214019060610386507468403e01c00b00202c1d800707001c01740040c0314082c2082c20740840da800203003400f0a085407502c46c411030740c1005071120b1081c940d14100036084540d0024000702a00c2c0700f0b51451001c60307183d200099507030084080059200c801032006101300d180200c15116107250a000100707000d516590355000581c401008240b089076180100305299148184029640c68040906403620b001c6840710780d191302e4002c0010f03040c400c0701d0364100c0c1652000c0001d201960159416504000740c18040200035050030320503d6118801d01c0085082484c3c0454070404a0354080300030261a0320348400d1502509005141d958030840c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 757339244 1250 757337994 757338017
    0x415090311010e0105100f03030f051e07030804020909010204120f05151906060f05090d050c0a080d0207080114041b0509070302070209150a0504180609030e031c1e 72
    0x9000e441440343c5840000710f110300c0c10f54505910402540d214011071000743d642080843d41001101d604084140380c4150f071080d101c898250500302d90254101021f400084880a25921052076402180300312440b5030180c5400f03000600744d0195000c1c100d9000e0305401440c0000302c070010200d16880c81802603511204468952080c03110342201d0b0348a6021500f003030004c40740e0203407140c040500114240040c0c0c60042d214002d2060180b070601030302030358050f403802088c00010131036219014401891040c07519110f20030603440d207442544190151054240105a411060185202218601d280d03c0d90940d220385502300440c8440101c00c0d42d01c001035002048503181c5d880034038401c00c8661005a0344003850701c14019458001401d940060311441e00f0700c2c26a0b968103040b41c0c00c4800441d40814450045803054546d0b40c114070300100a246081d03a21010140c0003908111a00001ca003510300520011b101d10040c85e000c0e00c0c869001403200e2070188654002516200b50f80341c0c5078580040100d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 757340494 1250 757339244 757339277
    0x1401200106060207030b0702030a1403040f061a040e0109080703031d010e0705090106020c031b01020c0d0b090601150e040c110607020f07140d0206071a0408120c0304150903 76
    0x750550000c00058011440c144141b00181c2c20383c036040a020b01c021071502001c1003000b0110b17a11a208100c00342400404202400000d91140b81840d4010b4400c03c1100b80c108000a802010114264002ca090031042c51002c072041c4a12071055401c640003c0c68a881340d0307821401460100072840c000b190243c100c0380b20001c244904200c3d144200b00501e4581d0400d8200034103110160300141c11907019550140182d01d0220749011411441c0140210803a01000107074184085014181d400034407030700024041c4020711000034060b0380d204058a0083c6d8880c54000031582c100905480030440102001e180303030400e980300004a07202407524410424500b2031581c2001d07070070f41d11000143c0c401c1b60a0121300c2c2c0144285001040310800160b203030207200001c40c080040d2100064842c00001c0341038410701170042401414820718080f035560740e180903d00b161013034010003a01c0ba040c100480001e900c0f0790464040700c1c09260019440d4801c501520302100c080e00f0814811000c0080703118010b1040b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 757341744 1250 757340494 757340501
    0xa0507050a030c050c0a05011d01112e0c140f0409050c0d1a0a05060d02041203050406021b0d060209040f020d0905012a05131d091614012001 62
    0x20744240d841080071083c0d03080c501d2500340042c000710711400400c001040f4980e003000e000b103202c88856403413550070300c01180180c40e00a04091110f060340600300d90846400001c451f00d0b111800700600040390008400c51100807200c00740310000114403180e110b0403002d1311000103083d4802003411120b01e00364580308404250381c2d01782d0341100203441c00300b03000340c000f4800d0081e90312400321480d03501c000410000002d91240c40340d10815014210014aa141e02d24460b012103001c1c05044280e4507030070750249402070056006105400040c0642e000d00d00c0b1581001d6000d260158000340048081c01d101c1d150780b8001d500004c0c0c42c1c0c1d4408c0d43d50b404d45041c0c00d0540080c0810b0844004001a03500050600d6404d5810707400c481c50982c0090400c0440e2462201c0c1c1c00300c42c4130b2091074200d0321203070007031002c60001d80280c00c810502005a8045c290140b20984d0b1140724110b068151001c0c3c0e13021600c01500c043d114050301c1d00d50510031031002041e52040800300b9080154010144082e039603599035a084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 757342994 1250 757341744 757341763
    0x1b07060506091503120a0309050d09060207090b010509011b020d030503090c0102030f1213050f0102031b0a140c10050901090314070803040609020d06020a02011b091a0a050705 77
    0x555269820801d40d03192110480354400d0340e4480c0030031200f250034002511802c01003034800480c5408604203085070b200e0f910500c4401e9011044403030035000c5402c003400f41078052040c0001071061800224183e5901d004040c50980180c542d070341014004001541d15400980603c003d21038412415400359582c8420010858000d48403290340e400d1090b84241041604885541594007c0040c26984a0040121500034650409440c401e480319036090107243e8402c903000c0c6c01b5105000340d541c000d01042d0300441c090017028040686854003002d4034001c5014120707001001ca400381e4841c40d0b841032004000c003044401c1c001905d54101d00001e000b41121425240c2c00c0850307542d4841c0b0010150850b038903c440d040c60f0320740c09041820b03580c1d038101c0600c401440109003944074042da02c00c40d211000d0135000035901803415515184030120090080c0040c04115080c03181e8030100c0d0b0250740c0101409400e4a00341665a580c841c079010741030340264030060414003000402c000540100f0002d004e034110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 757344244 1250 757342994 757343003
    0x8180d080a0609060e0c0918010e0901150311090a06050d0302030d060902270a090e01090302070f0b1b03250b06270405100510050901090203041a1b07 66
    0x4003420011407250845045030003c8012030710301003040c4100501c0700f4a982d8001c0e0f0000c00701760b80d10040f0f030110701d0300d00076145076000b03045030b030030012035004000c2581c40c1c4240d6941d40208083d8003544030181c11840c3c148405031240c0f12b40520801d19051504456900640d0f008011510700e41d96404100001540e200c160010307080800e0201d0102410701400b0010030441e8029810300000408014640b0300310303046846041d1641002256540b10031a03090f0060003400010002c0300300821116000e8182c1c40c0d421401030095542c0403c400c1d1400c4c49441c01c0d2008001c1d00b40c1000403003d00426004030800465500344428080c80d44140a0400c90105002d00e42e00301226138029031800490b80400680918031a1000c2c6084d4520641c203c3c8080445865440301040c1c1b079200c0342001410105601d44440038107040c80104088050603203000c4044907015506448141c5c0d036188500704038002542c004048203c1c5501c510000c02185040641081251100807500d402c103032401402c41d0b001e034900b100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 757345494 1250 757344244 757344257
    0x305090a1202211315020a08041d07020601080613031103041509090b0f011b021f12090c090e030c010507020c010e0f0d032001020d021803030a080708180d 68
    0x703403c4241c00c100340c40c264204400321420040042e5901481c080c40340500c2401d62503585c22405004e1003040300f0400103411001055586869005082210380541520101d403401400801c0800d48001651350490702540b000d051152107004250b0296080004242e0070025170489840950b031040c0010801800101b5060700350040c5990041e0154000381d206c000c900d4174001110354541c98a0b60342c0300c2014400d00c0c0c0b1003064a807041c0f41003200035200c10b01070f41180403c50311050f585503200d401640d114050f101c458000c468021040c0a442d00101c008001e4055142c08100440050300b04036940305560b01940d003442c0746036401d03608480049070140c006034020403840c0d985581000104080060a82e00986114a12804202c4c8031207480002420455903540201c4458a007480507194506c9860081d90358051816202c0080e40103284440300d01b8100803080e0074070340740000407503800c20981e44400c403080c0e46c4c0680948002d000101300c8007075004140160f50080c10148056401e42c090390710340c0d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 757346744 1250 757345494 757345513
    0x1110a08180901180606021203040b042f0a1e0b0f070b070e0f0d02030d0f0302041e0503060f01030203100b01020c04050a092609150f0c100e03120402010305090a1202 73
    0x4080e10146e521040554200001c0e500086071030000302c81d4041e821141d11000340d1500c0c506400800d00505041981080004012422a950b2003100000381d5040328a0412682c94500c24142c0f03400282c407510310300740248001c002402d0503202804152820b44056400c0000640700c001d41040200d4801c40051489807008a031071824603a070700c042603010796032801c0304041a404691b55070000c58096040c003100c1c40d160140140311790101c501614105803204070041c00918101500c0740d040c01140d1090056400080c00c4100c000c60281c101e0713400400134a11040c10086900040680c1c8040038114050490310480680fa04d015190041c44d41100025010000342440c02030034200042c4040150754004042c0f076408510810354070000d8044808540c5070415031802d42191180042ea240106070201d8600c40494000c90910001c800c0500140012030500490540b2882808001d1a0420030b04001c00d025501c40d0b03000c642e2110b2000c045600d501d050740c5501343d82d0404814000010791101400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 757347994 1250 757346744 757346789
    0xa050f150f220b0d0504020301061503091505070912030e0a030f110d0c090b1f02030c190203060412120e0601170a05060403050703170708060a0501110a08180901 71
    0x10261046110b001a8040e051400040d041c0c41850007542000e43c40d10045015580e082d84540010711225001c1c44900c0706114015000d8403036000241c520301001000005101d006000721482000780d0360380c00c00c0d01400c1542038280e01c03d0f038031025010002c0d840701c0000316885040502e00610f0080c3d101000144003880c08010f5800361407072040c010307030401108000140c58152840c0a0359049180880e04e0444c400214040d03032843c507513102003a01500318038440c0607004401840000765490a8440c1c022801140500320410710200039059409000040c01080400c040c103545540c0900d0820188045c0b400c2d1311080e40c03040310180049810540c010860085000c40e031741e2440c42080080e2030855080d44481d0b483c0c4000803c0901030000003c1c0d45420940b15032244080b052407001030340002e0030030600040c0311042c21920113000d03003c0d0301d0340410f0640c00354000801c943c041d80010b04040969a03502030f0305030801010070035a41012540c441555a0300c2c0003090180c4280c00743c02c403500c2c480100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 757349244 1250 757347994 757348027
    0x150c0708030403122f010f0906050601020d05033303010c031e060f0918020603090601050a1d0a0b03010f0c12050f100306020901090512030d0e0c0a050f150f 69
    0x43d10045c042006070101c5d14580d0766142c494203902d031005007105880400101c03405041080c1c0b03042e10079032901c0340c7c500c200304665002c036001d80801c1e030031928a032506a2061350a0b02c019140c0311340e035456074450042002d5403101480c038084201e0898051600c02c0d4004a800d55080c546008007080d240d0701d020718021008160780741c1030324018405024140c54250041480341c501c0c043e0380790341030300c8400782181d03401000e40c164041035026100ba6581e1401013107a40c2c4034502805124880c0714000e4000031100000d13140d48401c0e4071a5860b82c4450f0316202d8000c0002d08800709015055521881d88075151407071441105404419038032004200e41c2015039420071184020141d00c684088070040c000d1a0000c04107080541c0e5004c140180d8a50f102401a108050306e5804107600c01d4081c00980203105000c0301405c084101218188460b042c0320701d0160300c030204e1920494004081120801862800800f841d41030100a00340d80d120039038111301030b1140d0b400354800103404c6500158481140c8200c90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 757350494 1250 757349244 757349273
    0x50a24080709051c0b0f01080d03110405010806031e0f06060a080703080a090f0909060c090e16110601060c02101b060b210c010e0f0d02150c0708030403 67
    0x39000c401407030800700c0a0851070390342c0075150154041840c414003685110b41c102241c00d820400c0b0048601d40464014070800342402140e5140c003503540110b01980c000e01460001c404c5040413035003802d003000011212850300400055040c4139441d03080c81c0102c80001d204c1c07200f180d140081c080003041d0b0315007546420000fa00142c041c1d80e0391102005640c10110b06981940c0d8442c010642e28041100100c62210f05608203400701080400300103100502c0e580700c0f0b81d22500c5080d00380a03c2294103000d0f10501d207070784568000c1008a40001e00212401d1000b85803980e614141f4038140d4103249100d42c60490242c001c0808503008c3d01c001002e514024848800c5120a450020201d01080c8000400741906840091101e0384824010340c0075034411204000400040c4441c151a02000d2207003a0b41c0c500c2c01c1ca100f80800d4030890302064508100504441c240000340548070084525402d00100700510311780e00b00c0c604824003800b081c600302840810001d0000b00015622641541441f00c081c2c04c0c0712 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 757351744 1250 757350494 757350497
    0x160504020c1509031e1303030809030705100204051e0f012a0c0e060d030f0f05210406050a0c020a0f06020405090c070501110c06061012060b1305030c03030708090307050a24 76
    0x10300030409883c82004006d000d50780c2c0341c90300001030384030310440300c0c030b540030700c0c0340060681c01703020070840a0301c0446c4d014004442c2d0071a500a10007104075801c07035103003d4800003507400030924202c000741540075041c209036803800c61401c04680d054002c501407501188039001c42d40ba0b000c80b50208600c8808040e07160300401d08a42c2c0c4a0640103940c0d000c6e00c002400c2d004881440f0002580c41c07105400350041d141d0f41414111a9141161018440c2c0080c4078100d408039400d80c030b41030100d124100c145c030034009004190780007801c0c0c0d81080d44071240000c8007200110760440e003c000116481e06c968104074001d03d0b10103490b60f181c10040c1350603070950700000c010724042d100504c0752481c4503000085490b0002806c0d1900003404000d03a9084807603007800401801c4007804c0040000d24105c944c80200800b500c8282c40d91042d40d00c400406490b109000c584640c075074000c2c050440800c1602c40141f040c080000e08a501240d52880441c2c1125500c0c0c0c42403c40c0d0111295005108005a403400101c2145 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 757352994 1250 757351744 757351747
    0x2d1c050105010e031b01050706060b120a022d04090908300103231207020406140a0308030a230601030c020a03090909050c03010614030f160504020c1509031e 69
    0x200301103943c61245d110954007800d0340008a038400d9010320304a51071103030401400d112907a1208006e07030541d030107035402408a440b02000900c003204207100f81c0310390f0811032400000e80c0076814020781400c0d501a44001e001c240401000550303403502e1044035105886107210a495824119107007031f03502c2d101c1100c0004010808842c004034202c0400190550780d00c000d5994040d98202a140c0391010740c1440c1b000d052003011100456100700402904d89036108440c18000107480c4c003829590046498201d03600176000260900024400101541d845070705940001241c1003060b54005c2d00340a074050401c640b968000902c030281d603142c0281c5440b007101c0c0c0021b00780c045981d075000706541c02520441d500560344000180c20000240061054110014020b21045881d08100100c1e100d0218826110f0703ca03954032030035840000b0603203480140d50b42d02c44a103c94a8902400040e600450480c0c14074003e00c3c0104c82003616008007140909040030003541c4503808055084110300c800101940000300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 757354244 1250 757352994 757353017
    0x10f090908040e070201090c0807080c04020712080403050c060408040f0b090315070306030c0b130812030c211005030c040b03100f1b02030d0b0105030103082d1c05010501 75
    0x400804071402c40f203242c440c448541d510b80c0f80890040040d10b130014000714032680c00003851000050ba800544080406544c40380003582d0810040780300c3c4502c010141c00c40d1180010545000d0305076941c0c06030103030409601c0c1c00b01150004e81400c80440d42100d041d60003180910904a0040780c82c000b07424440c60341ca1400c080200020780d650240f55140269180300400111210722a41042000315482059013900c55282c400c00c2e00f00da004030b048594143c4003820002a0003c002580060404102803d10314648034000e0b202110b031310400385210700ca040e44501208810112202d41e100700c945030904541d5a0800c4c080500b411803c4c50210301c01d07401d00c140c05001381d401003074003403401703132150030004001d00402140c1002e400408106070110100c0d03030300b80340f186801000800b5603403561042003202001d0316006441a0100b8040035010b01d20901c05840c0350394520290340d0700014551752240008442540c1d00c0001d0f032028400607003100306020007501070401c50050b00d000d0002424800a10702 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 757355494 1250 757354244 757354253
    0x30c0b031f061b08040503010204030c09050906041a1b030705090f041b050d060b0705030705100516052113140703020f0607060b0d0b0108190305033705010f0909 71
    0xa48903c120002a81c801490007080103041c100c60043c2409002991169a80d080060b5508041c2c426800520b080400040010401083c43d52065030301c18020f28200154206105a0207002046400c0f0b00113a00358400b80c102038030015601c85c1032969100d50396900300300d042c0a05200008881401681046080e03d240c980203800070504400500c1c0964440d003c422500380903007445d03881250882c1c00080c0150600401200512000b80188216800c0e40d980001203800c03a00c1c10ac031110f010006006502c19034510a00040003280c4400703c5c0301816002c60340f00003c010a041c0c4484460103100540001000359111a228008407441d01600400e0f1440d00031400f90401481d0b881d201c0c000c001114420002103502402100001400300301042d165441c28000030071007030048106d14401d80b0310074400d0303030502d031411041d80d60b060b91001c1c10354603131a4a03107815009040b1142000d43c004030840064a4048040211030100d402d00450294504842e0702c8010445401c81e905541c24802c80c0000f14 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 757356744 1250 757355494 757355507
    0x20c040513031b0302030f0702010903020607050c0a0f0302010c020103110d050c0a030f0b060d0b01110a03030617060411010302180306040606060f1e080618130c0603090f0f02010504030c0b031f06 86
    0x1040b41f907880c60b0f40e42d80c043c0300490300c000070341d04002d5012602143d030b4024010b001420221151054604080701616400081c7e242441c6200082c0000c00f501415001540f00340c118a19a1803001c4403941001e000c00d051006480046840c03400309400490074080b01a40740c06031144245400c8410482115800003003615403140745001d0307040645440040d030407a40704810528007101900280d60480300b96250041c0a4210340c0300d000207051480e04400d000407408602140207540c001841456009940c0055011750000300c4400c1e000c0c00e0420036480a038406010140c070036071145070b00150690400038041c0040442985034010003000e030302c14020030045610140006105400e0820307040d550100000d440c0500c0900c0700100c20000c00c01d00080d036055610041c0080c0c490101c900105450366030071003c54034121000740c00181e035505a5008619500039010300340703006149c02c5180c07e841c0c6e11210000c3c09103032f20542c0c0c0410000101301280702c00c50040c0b801802e0041d10b00001514000000303098 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 757357994 1250 757356744 757356757
    0x40609030305340c0c06030515090108060411040f111c060503030f0d0b04091208070e15030a06030506070507110a1a03190c030c1428020c040513031b030203 69
    0xa8440765a80c1440719002e03c0500c0c2005a02c10b0700c00e0102070300c0d2a1b0003000b0300307810f6540a8502200b0701c00ba6191b8940b202d1070791306a6445500501507603071141c0714003c4a810b4081801d4005075130b030640d0140c105482c01a04000d10250114698840040b601e540125400f041d42d42200c03803a00c0e400f407000d5070703003c0700b29203010103001106601c520b0391a01c11402040e0820080d0b611615203034000c2e08010415140075450700c20358840d9030702652180400d4550b04c06d0122019400300c0140e121071256800403010b1504100d50250028000382c40356942840d0810942c0c00f500414030100b02082082402480d298805c0c40640f02a4649480d1064107001614440480c00c80008040006104402100c0074039840450301e4038248100190100060001c0600548500c0056950700c520340b00240000111015261000c012340b004001044591840f000c0744c401480440c003d8460b98032445e03849004160055a41070940d000c801007615025009001049145e600d0946041c41c000c0801c0e008410390b0302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 757359244 1250 757357994 757358071
    0xa020a110f0d170c0115150305060f06071113090b011d0601120e16140405010311010c02030703060e0c0f010c21090f0f0510020f070306150e040609030305 68
    0x1903203a030944083c440f0300070101c102900350310701640e0302801c40c0d000f00303c101165002c0c04030030310000304550210305580d011141942c100307910305003100342400c0140061882c10302a004072403000c0c4603880003541c1c1140c4810744446194035a200c6201f400901c428076401805040c8403800880601c4403188110078005040d00d050081d140070b0002004070b5508480c1b0106811420380e80030a0000306404041308541c01000004031078000c030203145040c1885824141c0760480c5940d00f1b040b00880045814102c441c10481c0c0600030b804000000441c075000d100c00c1404410050325400a0020501c001c0240348071150f070400800c02c410001041041c1880c40000e00c0310440c0c5100c5070b201050644445181d54040b911001070440000707000015280b850041e42c50032508a9814005038008a0b40d038100800780218a80184c0360400002d00303a5484610001c86c10395034007050941c0c0e104401c09070b02c802c84040e81d00540715a455801c051f4035110300ba5000c2d01c03401e0403d050010001c80440014023401031981d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 757360494 1250 757359244 757359263
    0x25020301060f030c290a21090b04080706180609150204050105030a0b04020c0f01051b0f0307080709090e0d0810181119170901020a050a030911060a020a110f0d 70
    0x150b84150711200d00c4040b00044070174680e1650940300091201c0c1a1000d07030880d000e10744d0441503103d00c035409100541500a0a001000c0e00c564840d800075a004200441e1801d81d14100d0f8615568010400840e240c05050300141d01040303401c25070140711502e24140d002e01c2c4100f106100981c0c200301502d4116508490008500480c80b005c41d0091248000c00c4683e481018802420301c541500100e00c280d014061040a044002e61010403a01505081400c60310007070000594181c458070b1240c0d88240c1c00e01d0000c01a9a80d25020070460354042c02080d000d810840304880f00a030012103158000023842c1e072112001d032800e02c202c20102200c03070880300207903100c40e03020f2600c0c50342c5c1055030300c40c2c240c4182c00002c10b840010013418001d90154201a10819613000a4880e40107100341c80621600c2d4440782d00d404107200046004140e0a0b204070f0b140c4403420a03440080d240c48024066180d1903070010100c01c8060b06207182d45241c1903100c940320b00c10781c212620050712400c0c2d01b0003140750301c0508030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 757361744 1250 757360494 757360529
    0xd0303180204020f0705070b0f0f130b12091e0d0c020310020f130911070f050f07030605090709180809130f0902090606090a0b0f25020301060f030c 65
    0x10059480c0311500654414000b240102541da140030041540b07611900c1244c0046e81d841412030414005c0d4596080807940512910303140d03001c1c01c4020800c001c7c0400c0015030300782d1035054a41c4141c214a252402008120040200c07071101008000c0c049401c03003954110201c0c183d180c90303a549086410140800c03103054424030854508014803042d5000704401552540c00001a0750780782d8010440e0503420058044000468101510512220344c170700324a06440d1003010303155141d2003021082d04842d240301d03e03025a0007003201400460302452103444003040506014038050b151503d150040340340180350894102c2502d144d08050240c4030350015009860b400c041e1b0000f10400301046042058508005031040440016401544480e01c200c4040082e61181ca0900031940660f001454100394003c1c820300010a03200d002c1d0100d9600c80010f10304d04981103506142c9445000ba1480c403a0585403618411481d0a005401c00340c504001d508040750301c3d644801d000a003880c450903100420030340b041c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 757362994 1250 757361744 757361771
    0xc020c0a17030c07140f09040f060c0504230a080c0d1205161203181208060f100207080c03030307050a050306270a1b02030702040519050c0c06150d0303 67
    0xd41c1c9890f0180000c0d00d0050380d43d0340310011100c0050750101d1107841c1040010040307240601405010f5504032042c01560802c0383d8807040144100d448500c244541408006640d1440164038131035101030010805c0307030000c280c05101d45602503400c040026001020003605944440c6210310007070703411203a00300000100c2101a180c40c0b085000214071034544404034800d001c50b02c00341f440c1d02d1203181e40821840b44000c0c19005034040c0c0300f0000305000003e407400f00c001d41c46001081d0308079400a2412111024800c006500c0941d8074500002581100c4801c01001d24140240c100c071940035005140303549004800101144900400e440a104020000c2021500d03142002100003140c0b40d1990030024590000150307a4104840400303449050501c0b01e4400c8043d07220840e05081103400070f6050809581c01c001c0130344402030010100c8003503001488020b5640340100c9000d2a0321030f0800d5a6200d01014282c10424002c102180c1c8441140c05829603071a901c0c04c1c508900e4140c5800180303111100070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 757364244 1250 757362994 757362997
    0xb16060213080613052a061c020415020f0d020616020705090c1206010315060309020402070b0a0c020d020c10121b03061401090b0315061902100c020c0a1703 69
    0x40715500f84a00010003840160300e03644034403d075001c1e4040304e00c0b406070700b080081d0203070100b000c02050a1030b41040000c40c2c1403d07009450528814130182c88001e0664028030221b030020b6101e0f50325450354000c2d041d403594061118456480030a0040c000b0215280310183d40c48401030100c018013281c0b0308007144d10b20710a1000d400900401404d8045509050130391001e80d070072041556041030303680c1021484660083c811030811901000d10084072520703100e402e070024551000241d0700207408002000018290005a81c4260740d40c010000c3c0b080c0d1110390083c50540703007100050566001d04640750444e5540354208040c5126464242465840b000708500940182c0c2e412055100e18092103100e0203415400c140152451034110180a1034034500460b464901440380b03482d1300e042000410740e4643d203200031403c00d20000d41014540031480002e080d441000304540401a000304984000007420f178010705540140d1072005004548200e4009408640640b00742c00c01c1d58159805060300050510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 757365494 1250 757364244 757364249
    0x111090d02030a060c0503060f09092808130602010605060f071509080a0305090606031f050702070b0d0204090b06090303030a0c0e180615040e0c09031f150b16060213 73
    0x420b0200491000018015070029aa528427a84580301180c049050550300d503403040321050020035101d010320301000042950310514403420b1501c00c01000100e00900c004003c0000110001e0311910f28016009085401c59008544160801c0144070000040720050b04d050036000800c11001c0c214484d0b00d00001c20013130030000e2440c2c3c00403c0c800700c0a5015070005120301c0700c074015603115070b46103001c2503181c0600e0600e1280c03c03280418082d410411541c080c41d44642c03240111070300303962501940000c980095419103013840e0001400d22184031640140b24a110058450f14101008040000d0700ca010040c03d10079919074031000565058403c00c10088054005007245507400c41030403c400d9002000c407074240c00f5622130b42201c41e01c1d40e10141114201d5205c0008403004d80c840e030011031082d610154025515100c0d903881c008100c0d148a8220703890000300c2c41e0008008069003140d116421459224140c020400c0c0300500020700098030000990b0744c422401a66440400f410141411864 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 757366744 1250 757365494 757365503
    0x30c0504030b1311120a0f1a090609010606180302060715020a0e04050603060105010903032118022806050f0d0c02060f090a12030c030209040f0f0e0111090d02030a 72
    0x10400d00c4040700c5800905540a40601100d445016032013003400102c0041c900c0805c070075402492590041150f85010340481e078468048150310010f20000c1c0c1d24203042c00d60301070155400900034080c4d0024240700321001040a81050359061400355580c5007015201e10019001c1c00d00051014100300c5040b1441c0e043c0a0340c864115111246000c00411219400c0d59080c040e030f2921010134440e02d00054114101e0340c0503510341981e50b06550341110b1203444240004101c0c00030f6049030481c61410b0141c2c10a4030021444d101160846004003c2000c00c81e00100204c07100301701e141498000b0240c20b10303040c2e5006003081a81c40b165800080c14500c558032003011030b14542a10000869070209001e0300512400c4045401c41c1c80e031034035094a03440d6100001705104010403001c04494044e401c06070600740c550900504125081340454295132f00c4000d020170f4240c0e0380740b480c01c0c0c4040300c1c403034100944104002002050302003202d10007584920030b40d039845144095000707400c55030100110319549510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 757367994 1250 757366744 757366763
    0xf06011718120306011814210d0c1203050403080105011d030a0f031106011d0a0e190303110a0801050f060702180f070309120c052d120702030a03030c050403 69
    0x40c0010745000d0f0401d035041e50000d22030840300d0094400b0560800d0030b54503010036843c540100181000303a004143e04041e07140c60600c0c1030441c40e1540501ca4180c40005c981c4a00c011403010340342c20100221041c5a400505d46008140030100303501003003440c190b070001e00302a000d008404a44200354654003620a07810710500d1509420001240203001206200b512204c42544200e0704090f1581002d0252200c04105681540040d51340402131a811440c2002c0000e4481c55004a03107051101c0044c0040801002500700e404240d49441869001c1ca070120b9418103100d150240148686030620900b480707101d0191021070342e65658022501004e07401086050070301c500c11404005004101e03201514000710000049400d402809a06103455128000900321024400103907800802410299014420081a030680454040d160306514200040c4a0205102100d5042c40c03c030740f21640e0080020180031900c0141ca00080101b02c1035418180820280c0b0708a000b01c40c40e02071684050281c03e807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 757369244 1250 757367994 757368013
    0x4050304090606110c01051c02031003020a0902270d1119150f05040e22050102031816050f060d020909010603090605060d02010815010905040207050309090f06011718 73
    0x810034094013100c0015021703603001072411001918a030040c800549003410310409100f0110107964000c592001010744809000c5440303802050303001c49079403c00642c0c80d6002502c0c248404945402d16070034603040d1205101c1d00ca01a010401c020303082c0c10020201000683c43c0190342e034845c80d1841c0502c20784560018216a81c1da26101401001000000802d0f031039496818024130540440d41520070340d000c0c03142503441e191402c100480d0b4400600d011a00000c07414000035800f07000840c01202d0484080c0d03d000e00903c802c42c185910a00c44440054449500b04202e0311000c55400e0000340c00ca03140c03078903160700c3d00055000c4e00c680103010f54400000c1c000401e0180d0140c0c04444440d005203c03c0106580d540180401106519400b82c007051642d0001085200c8140501484040605d0415002c50703450002ca0240c0e040810708a50a03000418140440d08041c10540c3d481404a4103004c03250a000b00081c01d5040300d40c0c5807100300c003220340018214144206805c0701000c1e4003c100c809480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 757370494 1250 757369244 757369247
    0x304030903140a0c051509030105071d04050907090b01020a0b0106091a120103021c06111b030a0c0204020d14040303050720070b0a03140a02180d120804050304090606 73
    0x80180c0000c89003521280e0700c12550031800506100f910b0f60041605a54604010400015100010014107801000c01581c040c9840c01e0203400d02070603598951884030741d031121290004012035444603014600d8842004800100069480c0803a4072002d40080d5040b4074800403418081c00400c00781191054000005090390700c0400081260380074031684003420a000c00c1c61200d4440c6481d03841d202d424100042c4050300d0810341915880781041ea14002c1c0760100e0795403c080d101100011021103502260250341c611200c1008100340c034400c03000e14035091400c00c0c050007000081c43e01900460b40440c180e4800c4140760300848422401000c45141c51802d4a4014041d00c012191000050b050348140103200702d02e401107156810303100020f410310604061b61051a074104492401c109503d4400ca030200d558490380050051000c902c0150740d400070b16800410030344031000664003030203804459802180c1c071000343da138601c00245462141500e540c1031151941c0140d03007181009a00e088000190b45 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 757371744 1250 757370494 757370507
    0x80409020d231e150108072606030f0102030103080301270207050c0109050109271d031201050102121c0605030f0a02010e0a12032007090f050a0902060901140d02030403 74
    0x1e12181000b0f1036084410340381e20404110980d41c440030007200803070400c680d600030358041d40e00500344e180004005100090300c000c61001002c2e500a03040f45142071001c0c1d13007010301c4054140c0c0c41c1d03200254910b516541d20140f040c0300c144500d280e01d10900702c15402903450415102d1030030301201025504c56415041160b2192502c141d914007003502040009510750040c410201101c40180450245a41008007402244040456200340360f03690305a8402d0511114002215252003000864031001a40340e80b0901e09810382140c1e056500a07002c180070b0104490841d0100d8038940d03d00c00301b625402030b98101030700c85038104e15450300031941070100400002a000721840e000b41d031902c40e2001ca02c4140401801580100030414804440c0c010200e80a0f402440c100c1c40c41d910f2080c102c03910265003504007000ba0300459483c94a40c59211480061801050740211340048200302c031074900d500041c0d15224400d05107040c000e00794005000b031400300050b01d100c80301004055550740392925000304103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 757372994 1250 757371744 757371751
    0x204060e0f0a05010f0e0f0a2603040f15172d0105100c170c1e010c020a062403050115061b17090d0627080409020d23 52
    0x14580c0e0300780d61242403401c01c0c421001c491040c0c60340b040e880c890403000c6824511120116811412814104d00c10303440f6020500002e00303441c02210660032041d00300d80032504000b54040e05507482400309010120561481008491071406100641f4199907020f440c0e04404150303030303d103000b0582e0400c04104040781c0b002c0c2d05042792001d1000c085450f810304d4050b07400c2c00e0081580280441401c94142d6004200300c92402d0700501c41403400040070181d1a08561015008032815084680414003007140c2c1008401c400b42420000c0c04402c0180400942d19440c051014124640340c0e0752100c502c0030b004013011f107400c060038811005a41c60b03041c4540601300e21440c102c00c2510791500002c1e401c0c4980034050524207500c50155540b11182c442a108405800c16102891300c2080149180ea460064400405214560100701d06041966002400e40c01c4c048845480d0740810702c180002d034100c0129019a462600016121009520704a00404e50f082020b04000b814400c407404080740180b1f094171 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 757374100 1106 757372994 757372999
    0x1030218090a18030e1c112107030804030b010605090127170c010f020303070207091d011104090b0f0f01211a0a120b18010f0204060e 59
    0x2a101001d0310102d0205c0c84045480c0e08500f44000c4c000c455030400c02484000c4070458481024100c807210034684211801c805000807400f0601c1c09140601c0200c0c200c942c2207449180408181e4020301094490040040000603910321a808403210034006944050480c04150310f4400285400d036040090310344104e42c041740605180c200140d1041122000703000a13280700d40050030043c440c03540b40b42150410002c004040c1c1d0002036610440301c1041c400181405215010a181107558020484550800111184807102e0b40050b201b0f40711a00000c100a13110407040254210340e000c1081d4100c2d41a180c0c8000c29802082203070700312034403000100000c4041404a5044800301d1020025180e56090304d00c240d41001d8201101801d05481100c440407203e490306000d40100501000950184a84225500c1c0e02900001107082951074195121900c502c0f000d000041301c2c510050 = true := by decide +kernel

theorem cover : BRFrame.Cov 757194244 757374100 := by
  have h0 := BRFrame.cov_init 757194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 757194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 757194244 ≤ n) (h2 : n < 757374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
