-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2621
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:15:24.883377+00:00
-- url     : https://prove2.me/submissions/596521a6-d5fa-4345-a88e-abee028d4f42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 471223021 ≤ n < 471402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 471224271 1250 471223021 471223031
    0x150c03150803161b0b030c09030115051c0507030b01060c02130b0d03030b06090a0b0d0c020f0304170304090603060b1f12020318030c0a0318030b190902040f 69
    0x440c0c00c45140a941c49082254000e01441a035800f0301c0b07050010082c2d01c0304605035104c102e030600021541c0c0ca58043c0030800e8000c8100030695042800070440f18404030020844110101c0300700c2000c1b986400b03050b8020221010b200442a1549000146580140b04a4550036902c2d591171381030714003d80085000030700200b03510b003c505100460315a0a038210405010031080034020594402c440c00c0c020b010140c880748001065100d00048494175200a8000740741d1307035103541029032139600c0406ca40c014145006a0707100041d1000c504140e9407654400910314192034300c1e100f03582058126054407903a0000f00000034101a8910030301006522030301000c0f408120b844100081c0601270340c0501d800d134030200a02c803421a130042035480c54203181d2000580380d8031a40003c042240103443c603100b0034800050011110b0354001101c620443c401d079606a4010f0780002d1070202d1030440d2000400c51604980400c0103141482e2030302548043d20800080c42c1256500081e090310310300c64400034113695030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 471225521 1250 471224271 471224291
    0xc120912020d0507031b021309050d08010b0406080a0515030a0c050103150b0912030408010c080406050a09030c0b07181d09060601020c01050d020f0c10050a1506030504150c03 77
    0x51042d121030380b40703608181c0d080540544014003250034481c042d40390403203041070b00c82c11507480d8520346001a6801004200040d818500075581e4042c4034651004500c1c0c49000144507403202c0121829544a940c4410b80c50700c40c0700c0a040500806000b081c1512081c403031b040610f0301c0400c08490301c680990300202d15640303000009030444400c03030055112264488404d2110b408850115007204100b56240e181402e001e007211811030203990050700c802c1d406c2100c1c00c51281c0d0703c6485036000d80e00441080141d03807100c0318000200c900326440200450044010324000c02c0e820a106640048a030614001e004c1003c191040c0c4440140c0003402744105a51890310b00c0d6801e649969031002c03804004001508040d40042d556805800c1d42c5410003000003542d20100c0c4c802d805482d6050200d1581d59180c2d0324144c0c0450b00c0d5100340300080041d80c90180058145d0405008400c1918948400c0448060030407004602822000b07000b0f40d04a448514038502c201103e03c00d00c802004196000a000301403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 471226771 1250 471225521 471225523
    0xb030f0303041a15102f0c060301081504080d050106050a080a0e03042d060f081e06060903010207050d0315053a06021305151801030c12091202 63
    0x15140301c01203400004001c000c41300030003290b002003100d8100e0701d8a0100b940b10604407081c003600c580c0350b04103151400e42001c40d502c4100540ea44100e1100507107101000300418445280400d00c03452031075070701040d490b43c80155090401c03904940610840c03031230840403076146170070344400383c2c48000091030009403050101d03800529540c010400e8031041c41018038800303c00780d5900990141c15200e100d400100c15000c00784c4c480f243c481481e16000c40c00025600c0710b015101200c080020b801040c08400091b0480350031051410a0034113001c035500d001d481b01010300105401c0b2080c0c290705990308100c80f102107402000f100031078064580d004195540c84003400840c0708116405140602c420381500d00520000384260680f19038142e00102c940c5518000d40e000701c0d000e601c00a0030341d41c80060114560032043c8031200c1551010b82e0340000030b41c00f0100240b110311400310394034140504010203c03095842034022200c08101880d2080c40c0d1026001d81000311400c000c41106e001d10a420320001d4150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 471228021 1250 471226771 471226793
    0xc030804121505090606090c0912030301050102011d0a08160624210b060102070509090114060d11010e01091806081516030b0303130303050333040207060b030f030304 73
    0x28642e400b4095810310f2113860b41c1e0351038081c0c1201d1091200600166514100d04161900032100404018000000b00c2c2caa40e107960080c019640154207250365070b804c01440c6031652400001c014010013001c150b94032801e040f038100e003074110b0800314064400c801089031801240d0014001022401450f040c5014112107010745500c510380201400040e00381d141e0704d24005800150b009140c080160383d42900403410442c598002650046190b000d1020000d0705500114815000d03c06604d115110102040319000c03045100515552034600300e11069403007904500950072060618540854654503110108a1105c8401100642d038410412814908020107400d503688002404080d04250b00810134541400c0d003982d09140d00c40c004003d0030713203040003281c1501c4840c00811101360b807207140080166006403117220b599140402c174083c1c1c2074180c540074110814401c4c00c50403a030080c4400d11019401450381a5072180d59807a207000183c60600041400c1c5c81c03048069682da00d400c0c40c02d107003404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 471229271 1250 471228021 471228053
    0x40f030c02061209032107050d090606120b1603060b030105060a021e0a0303060b040303050403120e030a0c03110a3609030207080d080f06040f0b19050f01020307080306010c0c03080412 81
    0x100c046c4c000d204696822108884010180060200341040f103402e001018205940c02800404030010030503043c02a108000ea028101450300001880600c0c10100d0035500380e802942640e4204000400140c540301e0024410311000303005651a8400e0911507010944020401600c0b58000000030000c1603418401d200107820140b40340c43c10b09040d40c400506600542c00000d20002c200d00140302c00d94040c24085004600040484165a00d10728041d8a01856444201c0c0d003250f205e2001e800519103200309005030307065074980088200202202038201c0300c2003a07d62840c0a00900403007001d02c05802003851701b5010303070020300c0b01602d80f1409501d0f15001444c10b2040028150501c0074192005454540101e01200c0214a0208030100c0c2e030700070004051041c0c1d00c00c12010f4902021803042c85800b0840c1e90031035444204140310001a42c881c4245640104080800c00c0000e07559800f40ca440040a03015800c0d00020f243c903aa00d180095100760422100405100750650400542c80076448000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 471230521 1250 471229271 471229327
    0x18330301080616140304030509040506030606010c110a030503040305030a0207060f020c010f09121124040e04110904030302040e010f1404110c0d0503010e070206040f030c0206120903 80
    0x5589030030041d54590b00c02820032a0405041041c40c002c0512030040e10508001244142e5030300c0c106403502800b0750b4000d0b18000c1c0580d040034000382030340c03030f010034060320411068461b02d101c4106940c94002c80f02c40e044802d54010442c007004400300300100040c1019502c01c4000790340e41e640312000a490905194414000c2040a907400d01a855020460300c0e4440400c2c200021203580d6000d094420b2044c0b900814580b55049440c0001d021861054400d6610207650519000c0e111000c501448003005060460074001008100480085045919400f90042504030070040c050000502c0e501d034143e0782940040e8000c1400d0044900315848503004000c141c13041c840e0035207481d03101e200c2c00c0151aa030510072560341541202c2002c80304101c4085100c4041542d0b4801a0000090101d0304280208a0080e480d00005036040d1300000b4454083e0780c003d91082151141540c080340d0b139280c010022600b0440a11203c3c4041d205440140d010350200c00280d51105420525402245002581d280300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 471231771 1250 471230521 471230527
    0x503030d241d09210a050415050a03061517190e070f05010206100915180c020114060a0b0c16090905240a0f02090a09020a090801020a0e0103021833 65
    0x4602400c8100f080c04c0120404801d49038034030520182c481e130040b41d0103085c4511020031041110b5034003100501d1000034580301007001c551100e81c201d040e0006001c1c05008980d18500c034210500d0640381d21036202403c440c105003090440c0603c00b0a0301c410740c003c200c0d0355102500600042a90307404100180c5400c0c40106900d142219003012080568869054140c0c0d4980c1e020020700c000c8204240a8903000c090302000c5400e400c812001032600c405100015440c014a0b07080242c41110308900030f0000070611980381e810108150803541c4200b1040083c0e10070008100301d0209034650381401070820080019420500f400c0c1541800044507801640c070490040b202c03080c8014000c0700340c0101ca141000100840f0f000c1d2454028490a414240c0c8591803c00000d02007201d81c00409001c20345031b4603108010340c0d5120460a0b802411610f030041115201c02e0f000c194442d0303024190900d641d8000a0342d4040110124038a512036001c240203030994003d80301018920317010095a08510b00403030364a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 471233021 1250 471231771 471231793
    0x61d070c05060c09040e060c0d0c1803060b030a0b2503020a091403150c1308070321030219020c01030b06121f0f060819060503030d241d09 61
    0xe110b40e8001c11074040c0110100310605580c8031548140305c5411100105c81c20340c03c4c02420101d06412001e0150b5286052028000000344241c200c452074041c88400b20b41001d05541d6114043d001c401251505440b03892151030120310a0f03032606005981c040426101c0c072010400785046002810302e030506040c0104181c01000f03030302c091410300701c0c3d14000c00b00c000740702c5503070010f42030446681c0300c00c03810301c62007051260001e6040004c103d46800d00050500c8107030f032072036505d81300e040e82c0c800a406221405a90000c001c885004a21120810315005107008007000320b50b03000341030b105074000044c0e0011807051441cad42c15201d40040800f084030113034103018034028a540c0d10b5000419040c100192200a0360740c1135140194003007e01400d000e440c1ca429241d080c0240a140100d5400007a086007082c6200a49214454030040d076001401551425a01054202c080e0000300c0d0807509800c5170a15251000720b85d02e41900c00703096006441d80d44200c05419a415000016000d501c00d90089039100e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 471234271 1250 471233021 471233023
    0xb07022d0c101b0305040b0d0203090f060405060c0a0c0804060c30050903330c1305101101150303030f0c09062109080403060f060f060e0d06061d070c05 67
    0x41c503c4007180d020500701c030186002c50355405a0341c08224450408500a2941c1615802940c41102071030200e8030000100741c0f8039580d0700c0c1c003590b0107490354009502040443c41c8150040c0781000f401d09000000c2031031390350394042983c0311358400c10029103581040e03001c12201014000c00307030070244400300121041c1c4246e900c85940072034403034050040004203819941c5081c0724200020404001032241c02965590074051440741d50b52400d4802000000500304081040540e580041020b000414150400091011645600384100300b840700c2941c901074550302c00d0141038107011000e2080045a07145207409016902d20f1211404c00b10f050402e842c9a481c0e101500b0012200549041c25035003c1182c11103042e6408010718002c018205840c1e9024003a0000013401101d00c01d0000f00318100100c149a030440b00107005000b9175041c0c2400404c1881d01c02c2d0740180081a00504841e955181c07a40d43d0b80464140e648484254842003420000070900d5a0f84907900c0301c00d03810035111600c02d5544071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 471235521 1250 471234271 471234287
    0x1150e180d020c011b15051801020a050414061c20071505060607080c0d08180705090615040f17030a02030a031508100920010206040b07022d0c10 64
    0x5410400c9001480e0f04400310000740513a170076008102c450107454a005d034400584821039619840480c41095117086e036005100701c030007071003560341c0b114100342c1080b1420f5911842a1001e56001c00140074541050181900381e602d441480140000e13903845080311076044495140b100c03203001d030302482142c0125003171320b5104ac0070b02400e080c0000c4590354000068058014110040c059140120700d41d0304103440010b800c4a001115144da0244ad070b00e01010b1030002130440031544040d000700e4020071441c1040384401360400c90090100d240801900380d02d140e5600070364841051010021810800d656114044540c00e2504402541c038008101101954a00c60300d5811070800d9500c0a600d1480d2050841200117001528140e848170442080707240042d04140c0e4080c1c0e40301c8110100701c6114401c07960304c4d40701c9072410b8024100c0ca69a5485a801a000c0201481c0a6000d5202800b00301c1034070001100030b1212151003040d0f200c5940c05241e2524000e007030014000c8201810380e8124a411080c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 471236771 1250 471235521 471235543
    0x201120e0111070812240409060b060705010b090717070c081603020105070315080a0b0405010605092505040f0302060a030e0106060306080c0307050906100201150e180d02 75
    0x1000c100c140822500c14014035195204041c1d5603400301e03402007000408402002042000480c1c81c01c1030b110702c2031032400c00c410140c0503100c002c0c074501180390303e05050f04451542e070b010301c03000107840101402089081c4d0190b0021501c85e590b881080d5043c1c2381041030f4a40000c09842c2a05021100744440c03100c0c460090304501c05e0060807003902041000d0746d404c03100913450303001c03007855007119a05c0c000e03018040584030040402d0400580071610708904c0c0c00d2500707c6102c1001003e00e1444e6481c0c1d8210250054820384095407541e1012074603841e03021115001e402e003401d14114481e0323400c003c9010a8039026143c0c040003410001040502d000c0c0c0800001d5a804a4440e5a510345900c4150000c043d41c0e8034040c0c00b5402d0240020b00c56405600440480b0101c03c16600554001c0d0201a1181114041c0e664010452404140c903030500201011699507213000003c1c1d1503403186903422098080f0b80c01154045000f804100328086400c068001c02c400784c10007810421580d81c4040d44400b0441c403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 471238021 1250 471236771 471236807
    0xa0207030b04050307060c05040501080a0e0d1d03031801110a23010e01060b03071413060e0d05010204091d060910021c0e010605030c0109030b0f0402041b02010f06050a030201 77
    0x100302440014402c461400d0340c8011b0401178510b1681c1e000d0682c0e080342c850240842d582d040011020719250259820441e142006400c0013500300c5011307200740402004881c00c0701c5501d03a54064944041004024000540301040240c0302c0440c00140040342e034011180361034000410703c40006071900031820002007129003007480307126118001401001c030061038000660801e00300040c1d0a000c40010350161076a03076110b9210342c504041d68032251046083d002070800d1070307030301c1042a80c0c800c07000d0740340307080c0c00422024a00007152551400da8110f0741000c1225036491203020200c074064018802c44240d00000341070f01d840c0000c0c1c41500e8030291031031040401c0d0006402203c40320402d140c84d4a000c003160781004501811034196009024501801f4040c1c45500001e40140d80100403030400c40342e00180e03801503075035800d208140980d0040c0c8201e802940701d4a59400c0c800c103101c800c240140e0395600000b040241d042800041c0d46c015800316002d888103160500150364000c0b014001c460201d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 471239271 1250 471238021 471238043
    0xd05100f09020301020310050906061c090503120a05010f0e0402060720030d020f010c030e06040312060504091a060103020f07022b0f120201050c04090e0c061b06010b0a020703 77
    0x40c00c00018011101009605510010400c81141000c451190642c0c90548810806980e45014440107101e00e04110b502c600074820a4480d0300b0f07664110110461090090340e0070500c00c2d040c20409507105540b42c1501c5910345005000403100d46080200800d1414072503041820180c01089061180403805400c8885843d4a041d2a400144c01301d850300f00064100c400c0c00c000644000c1d1101e64222003c51a5404d120084181602c46d009100c10750300000040e00b015201c07680c05030b0380d58601200004405485075400519035030341e840713102c0380d040c01414009203108141e40302100e21480281040c0c1450320500c550040144200240c8582e160306440c11440740e1900b034451482e50a15500c017a10003000c900c202800c01071403694804403907204000c8045402c3d80b0580a074241d502c00ca404144201061004204441c11500421f8040f804131003078910340320000000c12030719888101703900440c41100b645052903000c01c109040c01020180b00d0281442d442c01070081d1140c41034480a08591510 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 471240521 1250 471239271 471239291
    0x40204090c060309060510030203060622110301140a030314070c05090a02130e0411060d0b030f010213060e310c080f0c03040b0103170c0703050109050c0d0510 70
    0x3640308851254020381201a040e03079541008000c2c0142d0003080364040d003801d0101e14081d0340c0350300340e2064030303030041c05040c455450b00280003400d2203070b588003c2d2169101007490021111485440800c503200c4d4584c0d56a03606089e0780d003a00041032204640948071820040000c61741c40105007074401c0d80002c0c900c1d41c403811410400201080750700000c0d4001400010b0108520190340140040310741c03426100000d5640b03415440040038121030240640b1900010010342d0718101006241680000c1c0c2c00150510100001c00c0c90000202034841c0203a6002440c0d00314102040c0a0500800740c07840d24240794031074100450100111121a95030726880d115041c0e8010600d11001007140d00310040400401c0324031940200110026115484643c10003000304813000c0b80041224410f5412079034a590076403031580d58001c50102c5150400c0240024002c0c1003802d1414460400110700440000c1303000001814450700740550350312024401c0b140d0b80c00c1c2000107800072400c0003500d079080100142c4d410710 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 471241771 1250 471240521 471240529
    0x60f02070b0c0a02062101081504020105251101030f11070f0311030f0301050a0b0313030e01030e070306060e0a06060f0815040f0911030102030709030b0c070c2303240402 75
    0x2040d40000c0d80440041a60002071980c07a6100061140382c6c00e075207030f281e6030700d407582a103844041401407a554407000000300076502400080c5102e0444482c20511071010306103001c2c020007101003c6680c4211440980c482c0e6a1502490007640c84a0700b041103601846001d4103018400c04800501ca06200b02001041c1030054140f540386880c030303006499450385e03104420503440e07109025451152210310008101880c602040e00d20902d85031016600d0380c40d26403825035140342c0c40e090f0315040580f20011540c4940050041200941c81000d000c94a241412904120448010305ea991046d02d0600304221103503200d0355002044905007001030f8640ca45030166001d02d07800800c1990406e0514241c0c09a492103a40704d0040329028140c3d0140d010030080400d130903844140c500340b00040004006001280c5000712150300000b4015104e840c0020507030350009007080c658031003820304011840b8092806101ea170300171840c40c030840c05041c5240000342d02c00481422800c054080c0800540050300b1515 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 471243021 1250 471241771 471241783
    0x6060c110604030c080a03030c020a020f011d04021b07140306190e0105241009150915020d411605030310060503090a11030a08040906030b01060f02070b0c 68
    0x180000040b13010b81e48070000d955030381443e00c1040700003038030b8660071140c440e01c04681d03412074660051038985040c12080044880c14041c40d180c0c00021030110042c106a5160300c0140030080d0010500c00720014110941410440c1a51200001c09040c6e000d80045607008140c1c02d80c000120700340c81480c80c0310b002031403004101e0310f0040500340d860302c0180700c4c485c3c0c0a900817841c0c0903030866288030f220fa0300c20107200243d0b0052a00001181c00c040081c017a00d079544e00d001c03000d10741070300d0b244c07129558030808910b4505c40c510071140580c0103603d448241c4d0341d00000040e008560000900c0c50034182d172510001103002ca05811451002d114071540c00c1b40c0384d110489280d05845007004900c11100d041241e01d0340c4c81650465a00300f4410b1001449a0140054a2041d25103401610b03020400ba10f0341c0303100c0e640900c220b6606000e07a4110b2000190014040c101a0218480002d541425032400030700c100e1040e0041002e2024141c0381080b01c69000071040f040c2c80910350320700c0c2c4840248a280b868a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 471244271 1250 471243021 471243023
    0x7121202030d0612021e0d060f020915030108060903120601030c140331031205100308070c03020a050405160c0201090b0414040c050a022a1804060506030106060c11060403 75
    0x241080301c002424900440039103074590007294071080f50000b03e10701c0f00c3c406d41034030640340c0c1141502d001341e40400c00c02d500200d003e419036003000d03203400c600c4800105c00224141c08004046404801402102820412035503c048440d004500c0c0140c048200600c2c00e800805090405d61140303070514000d441025061980b00c01d91504075101c0c01c011801d00d0110b013009404000d035144070000444244072200c201d41c6a60780507184c10110152441620707010b084000d0407091200840c100000014200200030441c043c02980000f03005e90441c410040120059401544100e0414041c804440c00680e00e404851880d401c000322030081d00d03c01030f1004c00f42070f40f0070308004e03c0c0840c0001e003007401e40410710020304003140d0810441c900c2113030642d010f0251410600050f480000760303611070456040071000c0c3c0e070440c143c00300b09092003900044500340c14680c402887c2414009100401100c0e0007100e8100c3c00440003800800c2c01c00c5401480c044944101402803850203280c0d80307c6071208c0d01113402079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 471245521 1250 471244271 471244297
    0x4090b1504151409220609060b06040807080f121c060305010f0f060503030408070b03070219060b010305130b06011d060a0201050402010801080105041e08090d03020d030e0712120203 80
    0x14950b16140d07207083c219010b00c001d0164000348001555003900c0c0d04001c41c400030151803c4a0040a901c0d003030024844000102c4c0e040baa50f9507060780a9940da400b03031000f03207003e20040c8401c1c0e040c001c0080c100924a00c8078111984034030300d01d40e0340c81904000e40701c0940400700c2008007001c801c1c06031806001103900180c895442c20004100041c40e42e0004805182c190ba0244810355450341890b55034803a034807903c0c0d15600f01d4603080c08252011001590061a81e104a80000e9100703041c160281d054144200c7c1c040faa03c0608141558150146980c00020006008100007aa0700d43e628458001030255040040400307440b00c0186a450700d01e444040c0160015444d00317070030328002e4001c02c010b48059011a1880700002460300c014001c0b070748a80d6001c420031300303401303400e04040d00c100800690841300c03910240710780f400d142c444041201506000740d00030710ba0710840b590064200c0e05140c2c1e03c464242c004c00024070801041001c017248541c0d0010030308049490000c8100e0840c06036812880e03107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 471246771 1250 471245521 471245561
    0x50a0c0224031803090d02090402012001020d062309090304090603050f1207110906010504170606040507030b090c070f12050d0f05070c0b2502060a0b04090b1504 71
    0x15814080a14420a655030700f14142d1038100390790940d2406102d121940c0206080144c000500704040c0264000b031040c10700600d641c18020350100e0b046c00320811011140e601062964500b03046000c0d000041c0202c0745011600c00e0300100d039000079031060f07013141d010b8079200d804981d0f600d408004580051000c014204880307501c86c5881d903100c1d011043d116030030744110080c1203c6440840200c03445540d02c000c0e8110030036810820f0110b01040180b00382d040c1701c0c0600000a0070134030041d4242c13a844d288406486039180903020801110300240104080506d0000000c0c4140c075100700703054024440e840e2060b00d4609601d041c80340d141c42040700070044541514107150080c3c01101408502d00c03000028031118040284802c1221400c892041c0015050441c0b1404680407060040d0001c00d0b00f103541c240100008401d240008100c800300005910403410000088450300c100001d03440221001c0c840c49040392101b5202e448060300c110b0a0b403440c070a0310b00a0307603174640c0882c01c0c0310190284091 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 471248021 1250 471246771 471246829
    0x110c0303040617071b06110702090703020a180506070b090a121d010315030b07110303010f031e0c0b030c130e01030213050402011202070201030f1b0f020d050a0c02 72
    0x44407409071181c210444803d008141002d00a40c06054800c034031090241c021000d9446400103010082d9000784042810843c0c0400342c1c54201075140b25060507100035a030344003068801001215103e428009642d40107c003404142e40d00402c88200542215028055440700c032121410412103620040243c542d280001900a41006400c40880c5c099402d0040c140c01c0c07540150300369208650140300310404482c0c18400500341c0001039400000c0c0c1d26105c0f001c0c203245070049140da4000e070018a02c120498404208100381d6032848820745550102845003000b00d561004804120303405201d0b9107110100000c1e000d491310409444c1e450403040d40880509507500d4000d81540004c0c007007607001d091400e030b018105400314010035025590613900c0d9030350714160780b135900000e4220807012810540c540d81580840101e502942281109070300d1154520801003101278181240e210020080d900004108028141c001059445003003890030a04d000b24142c0c80025580421081148407107440c800c070340380d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 471249271 1250 471248021 471248027
    0x10b13151e0315060503070605030c090a09020d0e031309050402120703060b0f040c12020901140304080c0d021c140c0d02010b01030b1c06091103030a05090103180210110c03030406 79
    0x241c212800780000740c0c0c08103203042070b000c2999124003419030154041c1d00c013000034a100c0c2c0b000b154040007551059040a5101c0b0000b0b80c060900d60121002c9900421200805440e0f031092254080c480002980780103444c400c0c0c0c20000300d0034400d03c241c59036610002000d54072041140440d01c1c00c40010354518903200e1810710000d03c0c8a0002c240501c80e0144201c1e01410300340f013822610600c40d2031300a012140428100301030751115140d1070401c4540d48416190301404405113000f9489440c2d01c0381c071050382c1d00e6414500544900c2c4e8404643c02440c04441320300300803d0070005000c152038403448110160750035020314030bd59021241144544581c00600580c198000040b03000c09903030920840840400300a03000c280104010b1014228401c0c0c803000411540c8103100c1c4502c0f03918440ca004100748002821600402000e102203034000401134070070342e4184160190510a42c50842801e00a5000700d50100402103022090010340000e0009595081144004c00d030f0000f002c882d0b50310f0300d80c0002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 471250521 1250 471249271 471249329
    0xa05100212011509051206070f08010b19090f060e0306070509130f020f0c1b0a1401110a0804060f0306080601032001021e070603050a18030c14060c0318010b1315 71
    0x6400207278007101e22280b0141702d088501d040394079560795141050351900642c1c0c110854840c2201c1401024600040c1c4211140035100c020503142e01c420341c103d00d030003051600740349004080c401003140422007030f905961910303c0c2c2803941c80310860000e0341240d0b44070a58028416000c1e820100280420703101280100000d01080784004100d02c110717203003503450034003515000f58020f69107007900703d0b14491280d5102d400300703401403410341c400c0314010040b030b8690250a5000307401400c00201c1c3c1e031401450395034260240701d000f880d82d40d0040c00151b14507101c4c400c0b49411b1034000c24007010040d140c00100da100300034a1154002c64507031510707140c100781112596003a02e4800d0201003420320700001c00342080361103015022502c95400707000544140c2c0c3e080790650541c6108440d05808038612221910302004018828180d46c40d040f60b40c0d00700190034004c2130002c1c5c03e054481380e040409810003502c4602c000385103d01c0138200802c5001412106c090500965080389440c6a602d610020f031600030b07419a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 471251771 1250 471250521 471250531
    0xd0305070807171c0504031215030c030302071a040b0a0c020607170301050f030609150606070b07080a0f0c020a11030307060f2304080405010c0c09020a020a05100212011509051206 79
    0x42e4100c000c0e44031384aa00b41d9504480180110f0009000c44804200580084400c03400108000503400d850b941c84000501003900300340d0040c0d1007402c0070b11107043c0845022221209100700c45040501d000c00c185450310645895404001c580a4103100b19241c00b01940d4100f90b0000c81a241c401d010840111250000d2280c0392081c494800c0b000d005042c08030310280500c40d880d0161021020989003404400005041e468000100304403d9022951a00809004d0301c0700b030f550302229090000315542a035440000740103101c0d107410001c0301c819400048074140d856100c802e0f002d8102c05400040c1c01d40c0910744015190a04002000004040301d6008001140d035031003041d60032152015440032080002c40e002010000100028401c542c000d20810b085580b1503422443d00e0b0f91250b0542080c0c3c0c02c090000e0015a10030800e071b0301007241c180324507401340003d42001c500b80301170154480c0c01620188900c190801d10000b010092522900e6a02c1c058800a00003480c142c5a00c81e12907900c41c03007115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 471253021 1250 471251771 471251797
    0x50319170403080d09021f03051005012604020a0b04030507051203030105010503070e1c050f0f0102031003060f020d150e0708130210181d060303090d030507080717 72
    0x2803001031504140c0165016690080d102c0c0c0c0c1002e20300a5040c0060145800c160f0f0b00525801d038602a4481400000101001680d004134483c10800d5080d11a140c040c0c00141c18046440485c0440c3c1402040075207018002c40e28140040d03e0764000300d0043d000b80e800c0302401c0300b0001008000c0c050000394481c03c4070740950341b02d42c5224510074901d0f102d001c00e00840c0d001034805c001058500d8454207810003110001091580311032810703001400602c442d500304441790340000c7c440301500340d424031244000f244140000d600c0c0d45494041c017031207800c46000007446140c0e100c0843c10681e00903410703950345042c0c1c00340c01c21a803107415001e032191204a100c2e421200040700000303880303207108070300b014040c0c1200c1101c0c03958030300142c1c200300b654003890b404a400c000f0000303816a5010902c0d40720790f006000e11050741c1628010b034a072070103204034000e10040c080c0d841040b402481e83c440200d40501282c141c548292140d410b440e11120034468140041d1110142003e40705280013520014180701c3c9040c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 471254271 1250 471253021 471253043
    0x190f0807090e060402210313171605060c070902030f060a09090b0c03130f1112060103081911060c0a0e01030902130b0121020301060f110604110604050319 68
    0x315032a01658880702c4400c0c00c030f03000100410010300346128101d00301e10402d000c010400051040c4589190010002c01c01c8900451701c3c1000100b07040000341c40c00d03510343c0e00039041c00c1c055100301d80001005417103940e0042400040c00060080203101c500c019103030092065580341000e001d07640243c4010b030703905803023441403c400248800c0725100c0d041d04580e1122040f040342e940e4540301006500010580d50143ca60b440200c0c0c005a00c9103807240025120301c6c3d018040c0d0044000307021841e0800c400c0c3c08240d500641c014004242010240d803600903901d01c1031030003600d6580d01260f00e9600304002da102441608d052080c1c601400c0050501d100c03041c2d444001c1c418542e00110152006503038040d400c0684095142a154440e400040000c2410304207100c01c0c40c0c10302002900c2c0034401002c00125640840180300d21503100280921081035858504040541c00c0c43c071645501c1c021744010401000380307da9007280d0700d2703c40c16a002403000806443e09240340070a0301e80341c82c0d8440c004907940c1c0b100d2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 471255521 1250 471254271 471254279
    0x60c020c0321070807050d020106090b0406051327050a0201081e130528050f0309132d090303060501020d0e010e18040c06121e0506190f0807 62
    0x18092040c202c9045104000707042c6429441c0243e4400c0b002650341c80390030002c15011460402c00c001d001d0000703500005500d40b80c501c2c000d04a401d40e041d280d11950824030104403d0b03075412044072040050400c0000c0c14182c030240d4a850440c8041c1c54000b964503240380c0024400d0214212460a00070780701c68656680d804044d03403160403031500d41c1992800f10340101743c00b81d036400f200003a414400d504840c0b000720700c80800d0ba41400c000700c200910304200240c80d402c03c1070a0203011100d2500100850800310311100060042240103140314516550303800756020300e440401c1691000c14040d5a01c4c1c0c0802c0e20140c110041c040d010000c0d00801d040010004007035100086a0401e0103259a4088000b504d82d00115850111500440d030302c4808a21a080c00a2000040f0742c00385102d01403a4041505e8481d0141030111803020b6011190701c0d08144041c4107a40d40701c040c19216103444001941d540750000184134202400d950080d00e8222100801d94504c2e0217210010344060380101e9040d150b0f9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 471256771 1250 471255521 471255523
    0x10b0a0318020a120f05030d0608070e040f031805060706020a0e01210911060c010204031407050105070f050a0b1906080303190c020325030f0e030d05091c060c020c03 73
    0x4a01c50003500054040350030046002002080902144200e50380040410301d070315440c0c5135030800700614403203656900c02040709070001c000410040050045101e4540350580b00c0d4071035100703e44005803c3c030901e104058080c41801d0a810040c20740140300d00d465000d42e040c940c009400006a900c00f00318103034510807156010340b040c503044010b091021004043c180000801030103600804545401c2d880340e000c03165944003800f41c440120340500042c0c403113141d41020b00300750050740301250b01c035007080e0420b001a03617006003161419a000012034501009a14086262024102010380106403840510450305400c90000b5040d14040341c00b800403d403104480c54072840f0030380f08241d166024a9401a041c0c405400c525108540d03801501c3c101030b40da001d46908000414500018540d6502403c1d0815400071122004000d00e498214801c10b101c80100b0754452070201d005051140c0131806070440d50710100300744040140410034182c8610070b071901c134024051404822004d4010340441d0003207824 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 471258021 1250 471256771 471256811
    0x304170a020a03031110060e0412050a02030304030f09030503030a29031c02070e0910060b0f12060f1206041505042307050619030b060406020d140909010b0a03 70
    0x50000d1242c40590320f10340d800d42e00510f2180314450b03a8080c4010442000c00300303104e03c03c02461a40c0a2514919003460818a0342071103003448814090140f10b8681241e900000313403940079a2504103c6120000380500b41c0705512541c0c0020414480001000300084440d00403540d07100d5181e4028003605907584c038646051900c0c54046801d03601104400d07944101a4461030134000050050341c10041e100c464020200c0001ca841d40d05641c0402c642e00031350003462084000809140c80f03581e0510740d03101002c035428425440c0c81d03080402d505d00031402039507072200c4580c0b4400004118170111441010074079203403281190161a072014a091881083d5400d0150038405e0ba8418403c134a401c0c01824076084003400b07162240120b214581c0e012450392141c90080800c1c21403003508602c0b035000304c980282074415100d10280204414001001001d800040d066200441400c0070340301c5460b40107884115010381034031258403940721000042d10202c031000a02d61901e16503010b00030300c0d8521442c615211 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 471259271 1250 471258021 471258023
    0x3010f020337050f070f080103020913050c040c020f010b060702060318010f020d050a1b080705092202040e1014010e1f0906020c18181204080304170a 66
    0x6181d490301812101c6221140014550048410780c6002c03910114401241e80032501e060311804c55500740501c45421864451000c81a403810620310b42c156804a0121040508400e0141000c8201402006000e009645000300043d101304a118000710009544034441b41c0156800e520704081c5c0380c510300384101141e50503a00500924a55211904005225010303280403106039540ea04600e203000c095800201040b42858201181c1420000b032110116561244009010b00c4000c41e1410315070f8204024960290640c1401a12001001b01240d00ca61100c0c10003a040380c8514107014065000d0b5004d841940c01220b56241c16070b44043e25103400010031700941e840c0b14849254401d42d58482d00585c1c51400c000ba060315803588445c0d40e000911114441d118001c64001481840f0b515410840b5052883c000ca0b0011500b888010794400004006464011440c4040b4040f00a01900300101e0110b12280c0c40026540c942e1541d140717490342c0141c0540341c0010b0b01003001010040c40015807440c46 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 471260521 1250 471259271 471259291
    0x41503020408120f300a050f0a0f0b06040f030c0b13050910030803100e09010908030406110405120705010207091b0c06180302010618090f1410110903010f0203 70
    0xb003402540c06481d6003240d014800004010081c990401c4401c3c1d03030024070104180500d20b050500020140e1942030300500c5011b82915003401c00400060510041c1d070010000180058410b00442028000e8040000240c0e0041d030006000a911410070b000001202e003d02041d01c52a0b803902070410080c8030f4034a002502696100c0c0c140054a80200c0464000c1030b154070849003070303a480c1d89048454104640d000d0700c498510b0010072402d41004180750b805840c100003002190800d9070380c00401e003c0a48083c05590307072407500842d4484000200c0780500b10042c4042001c1c108507020701c2c2d070341c0c6040c0a4103005010760b000020b03030500c8901800c124004034110304a45181443c004582c01034a01e40d081d00d0580e1240c0441c200355000c107404075203240c02039001103003181c10b020300000400c0c001e41c02400c081d461f2070107000104010a541d8081075601c40c0c0c0c812050040c09070070034038080c1c060100b5692135240c2800481d0104000c0c0090986942c00e9000340800d0820001440480c04100e42e00001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 471261771 1250 471260521 471260533
    0x412030c0b06031c0f05120106020a02090906071209050c090903040f050117043504052d0d0f02030118020f01170a0f0608010c0c02121c051b12041503020408 69
    0xb0304d402044603181805081c50041c0c00c1c10b030f04042601e02c201c82a400800940c1200c2003480950504915160744000198001c0004d41401d40300144844507104d010b281c0d6540c0c50100804104061106038000d4a00a18600d011f040c400c0a450300d0742e01c5482a0110b08800030317400205540200800300d125104001c1004150765591500002d4858003014814034000300c03003211030308414081c8000d0180701c070a01d08075201c82c103060610944501c0c1540c0c5542c41200012003040c0c51068164400c14a9425101009130710510303d06072404c0e14482c58001d5155080c800740452506041d4413203d0814004c440f024141c11540b0010f46905000d2062080020300c00c0002414490303d6030807419000c07405a01c0000c1c069513079881a4211159589100002864107080b1020340c907016800c081000300103009840c8000407440c1246c40c2a00402510303041c4080400c4400080c0440802d0808180402c01a10500e0240980001e07a5522900807584004031307808041d04800d2084c4255001c5e956500003c0c88 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 471263021 1250 471261771 471261823
    0x50a0b16030903050906090d0c0f0602010b010203071205071b09020304200901031202120d0506091b04090b010306080a030c03080705070c12050328020d0c1109040501020412030c0b0603 81
    0x8103640c4071f16000d030707041440c0100200005189203802c0006245004908940ca0300b003810007400c6da44002c60150442d030043c011321005c81d021096100a5101e242030160781e54010f880c1c4241010318600f080d035a0840400c2001446402d99001944600e01c0384008500c142944c11060241601c85940740b60042d03481d200500018a05200741080300b2118011036602070118106286540d10805600552584a00c148400ca08001d4041500100088203445a0042800104c54207006610131038543c00d448990728502079020f03a000f030000d403900209a80b080051400c005d003502001000803000a41c9400026a0492260041d03520880c1c0c03007a8090368061800f000b01307090743d40407039003035442e80020003041c0900703030040d01003642c0e51100032686003009039030300006420500c20114030010300c8006107801000544901400003400700c11035040b9003544070740c245a402030080740c02801030051200c03070307207004d25400403100d0406600c00e283c030080a0782e0f07890074107803101a84006444608180c4041c15 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 471264271 1250 471263021 471263029
    0x706031404081c1b02070f060e03120315130b1e0607020f0609061201030b0603070303451a0c0a08030a090b070e031b03100c0309050a0b160309030509 66
    0x151900c007a0f070010a48020390109024810202812000581c0c0940c1003008164490310581008014908140c1c0c0140d00090120380c9a151510544032110030000004400c440609010444c00f18040d01c95030b030580d01050484010701d02c0203286440344c07103824684d80d24103501c00e8039500e40500240503503052007083d07030901000d06503c003801a440581449540c0094896101400d120381010400c1c001139407460800c01081d140c080c01c0640a600140400e002103034001403607418940c014440c41c0e0b00100b141030840884050070600c9a0103031414490410822100c0d041d000681e9210701d01051040c030204003000c813521070f003034604103c0e07000485050046004203001d980c1c001e240840c042141142540e452021b240704480c09008a440c464a1403850309041000c2d444646009120040c03181c1c061000a0b40e8855583c0141c84203921030304140d202900c2600300e000280e902408171551a82c1519240c030307204400312400100c0d141c03c10000940d45110b400341d440b481f40c05403184c03454031a40b03500380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 471265521 1250 471264271 471264307
    0x1003090501020904092105070201081513090533012105070b030109050601030b0306160c050105090607030e030301060504050108060a0e0708040b0106030c1b1403040602070603140408 80
    0x68403155400c0c0041d0100ea2118013450b981c652090904002883d09202e030018440c121000340307010450140702040050740c1120250340c201034402c0c0601c071200040b070005a15005095000410682801007440030048005208058409d82c060701c0b5818003a000b00c4400455000c11070b544c141030140b0010440c1030b14001c60440e460303c009507840d80b980d102e41c481c64a07010a03940071003044180080100981c44003442180e80100d001d10341400031550440000b90b0300c1c2800303800c034503a00035074640b00703012940603d5088009603880390091001c0c0ca8850041516104103d4090000c2410100030445410740402128140c5103e034440c01d041c01d09040c01100c2c0081c00821040c2c0009034080085240382c1030074800ca11405269070790b1a2140b40a1a0000c1c0c4c48006a204000341410100030104c2c01c0c0c2c0004140300b4a00c000754900b05216800d0900c0f103080c50b030f41000000c0c0d0740400a00411080ea0215010040d1041c070f407814005121038614228500f034040b58045e210301818050100d1250b042400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 471266771 1250 471265521 471265523
    0x1106010b0f0d20040e010303120516081503010c0908100c0909020a03021e210714180d0b010e090d200a020303220902280c0c0902040e0a0902100309 65
    0x284103e003100482120300150700c40d8101802940e94000104101035110340c031800e00c01c0001d2000d110605203080b0b0810300410008048041c84a024001041d41784440351b9130400200c02402482865007501010f05040103601580c1a1030090f1990200300a4141c05401d41c1c98080d5a103030600640741000e000c00941081c0949010980c08100300110240c007554030406e4841d1006250741c0c0e0360074030309100106140c034540c4003160202c0207003044182a00001c060714161660020241d407400792548032400d9208100099501c0143c2d00c1c507400034490741c00702c070605844c10b80d032021030300741c903070000c259034520000700000001150721080e5070701d09400c0c0000c445180c03d4901200d070140c0041d40000e04542100c80c00b40c48954140000c1040c0d4140010b0800090250210131490a0a614188220491454500c240008048a010755110701c141c005e4260b164103c480180340c0c540f12006e402c00f075401403040c2e015840524000c0740481c506c0c3c1c40f464007000da00401141025002e403030158060305c03110b64 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 471268021 1250 471266771 471266801
    0x1a0601020c0904081306030605011d09070513030503030705090907030515010e011818060501030e0303070c0c030503161505090d120b1210141509040204020403050a031106010b0f0d 79
    0x119504030660075013143c5c00034000545006c2412402c25000610445100d141031041d080f088403000c0325078a0740b55005800a05034504140c0d41d4901c0103e5040300c208070ba2000b0881d01c00041000074142d0f002000d81200314080320f0a0000752a004005c03001c0c0c840580c3c1640c600c21074010b280e031043d8051019107100c2d4a041c18504a61622a04021901c03e0694802d00640f03584050b0300721038840314402e020140c074007401e0030061a000070f140950399000c000c00030000d000d04010710b0b200b4441406c030198003c0d50701400b204d50b00d03681c5800081034281d402c1c00c00c90310f2110104107450704090a01400c2d11070410301000303061269000710300f00c400c1d60b1040c0301c03001d1069030780da1100115203c0d0420140d41e0215407004040c1a100a101c01046a05018040c145102140c003449a4400440001c0803546021600d40040751160700015000b8841c50344002c101d8428080c9690030150000c00800c4000b540c8815181240e03a1900980c00501c1011001c0c0d03030702201040100c030b410000d40c1c00750323042240704c2c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 471269271 1250 471268021 471268027
    0x1e14010903090e090a0314030901090c12031b0803073e070618031106040e070305090d0906020d050304050115030804090c09060e010c03140409091a0601020c090408 72
    0x102421200c01500c140c0014030800c20a00c0506401c0e2600c5810101070f400034810b11a050302e00810043c4400b02c1005404800000b082049001750440b91007a60080300150324941c0c1c940302c1d45009200550214041a0104441102c290304845403007880340e001b226043c955a04d44600702c801e4541d886c00b90744a42e070005000740115108038801d14405220010202001d016020058074100746603000e00c01300f2040f14004004c00b9281c5171040101c03a8081c2000d04c440d0a480d0008003e40125000058802c042e4000c0000301541500050301600d000410764005a140d40c804032081c02050080b04007503880b403074031045200d20070340c000c6038080e00038400010882d04400413004280e1941c0d1003914914404142400350200724400c00c3c0540304141040070780249000005095003424400d010b0500c03284035540c0081c103001d00181d43c4208035181c0e16940d15516410700c9002405d010000782c0c0e0036480360b140c42d0219001c0700401401100140c000b031090160040400103441402842110044414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 471270521 1250 471269271 471269303
    0x10504020a09091b17010f0b03041718180603120705030d060311030d020f0c10030f09060204080f070518071b082116050d1d0d03060b03041e 62
    0x140b084401312540303012412a0722481820040452180d001c0f58070304403031032030700410610306a00289001c0b6544100c0280d01c0c0c1d560350500c586082c216848618260200054000350041710040709240560b04640100202c0d401c007500008501f400c41d1040d1b0191300c4588800590025900605010b17480f503412249001028030041c4103680c003540c011181e4400004100501d842c0c00c0c005a4030700d00c036901c020180280500700ca650340b000ca464006020b03003503072612030b50006d20942011128503e402810301805005140040080d809440390404502030702505401c025000308050f400c60700020721441d1031080e444e0900340001e0300542008140400081032030950303448070510403030042c000c100062700d0303c040340100b401c0300c52170b04d04243c645000d050402c0741e45062555040c0302c0d4102c501e0b14640329242d40032020f000707121558003c03400000c45200745003207007400070740c00d45034464564091101703982d141001c0440d80026500200144008800400203601c4510503075421402424000540341344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 471271771 1250 471270521 471270539
    0x708060d020301020d0902091b030f04020105120f0402030d090b03190e06010b0702040b010903020d03030f4502031f0f0e060406050c090a030204050c0c011409010e1203010504020a09 80
    0x41c450b4031030317115110340141040d0314242048503031160320b440c00c60140c000840d40c4109613110040102d500801c0010118055900c40d00690301481a101044a03041c03d29441e54400b03040d044030124030a108250300b01c0f11043c0b1440340c3c10100c0302e44808260942d1503007100c0004000d9940c141507100d40da42e800d190500034040007842e0090002064440d41d03000d16006000a03280740110700ca040c840ea40804200584030011401000754061500040000d50701610502030089040040031158102e02904030181400700e100410441c026a03040030020300c0d180f5806003ca2001e00607505401440355141181c410184640c04001c8221002030300032103911620f4101d440c0d071860940917500020800003000300c24450356810000c0c8808040c140300352100041c58010642c00020b000d251158080f0710208070000540b050400090000d015258910307003921080c420898540b44070b5820700c0f07428584034401040b810401c1c4c2805210504e10b82c24201404041d510202100c01040120300d030012305598 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 471273021 1250 471271771 471271777
    0x191a1b030412060c030218010509210102090906040501030f08030a11072d2a080607052d0403030e0d240b12031603050708070c1505030f0708060d02030102 68
    0x1050591518030b241c42d41803140c101e908240c00f00042c18070400c6041500b240c3d6407141c2c4c00c1c400d001d103070642c1d80341d03001c40c0480c00600302d001c100d0074400c43d80125211041ca0640140400c504191031114046c4d44900406c02a90420310019151240d0a061080810103110095900600e10000030900744200450020298091038042d20303090400b00c95981020011030381c00d1210101c0041e84661200c580d1920310446c4c0c920005a0001c90709071400c01c1d20002e440e01110020004002a075056242c606405070880c0c0c080700410111119840070004c0c19a404503000800c09917105010b42003d040d5a010b644c1c03180c600d0a45944200d40002c907070009181210741210180c044140c0036035800c85c08000c40107491a00665501c9400d072510100c00410000054070f16682d00520034210f980514241074070148905500984807400026049003800500081c80088803807203102e504030340c148182c2c01c076218082030b100303002c03010070034004036400e144200c0800350043c00c001e200705640d400650019007268 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 471274271 1250 471273021 471273029
    0x272c0a1d1501063b010c0501021b0c03060708040f0c0305061015030c020316030512010b0403051005090c0d0804050a090f060506090d0312180302030702191a1b0304 72
    0x256940010f01a1584c4251580960486058444800581a000306025540d01003204002d01340c00041e11805a208140951503107404c84004c6655569801020388e0007074403501400520f20810058159a08001030700324841e0300580da07000540d40ba15515000f08441854041d1818028084c021010078428414180104a842e0007a40090700d00010080e082c030b002c1241005043c038000b0b21040d030f2500403048030704428039078080194400c207070301d015901703400350300018031084600400201e45c0c0381c0c2240007081074a0203401211400c3d010030108a042c2c83c021940a155600b110215064908046c1541c1c1d41443c4112841400c1545440110701f248200380c0c822220303551286e500c0d002040440c1300758005070a094503000d14010144000c103008020741c07400102001035200f0301c0307000c10110b030740180c40d42c54650710109840107507030500030b6494109550684c461032042ca2406491520002110201c41010800801107040d4070030404894103e8001ea0000000100340c00c14545000d000a0001e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 471275521 1250 471274271 471274303
    0x932040501141612050c34051f090c031203060506030a09030e0a0b030705030702160b0c01051008062701091b0b0a02061303272c0a1d 59
    0x103c030102e4001445201268600c1e10514a000280441030055174212007800180750340010180303a684402c00c402c070b4050340710b03564000005800c01040100101c2d204400d50585a06e1580711403a14017a802183c00f0307000003e00901c541a400c10000304070389554a4003421038100010a60341e40d002283d050f6008552000b4000d640300510410190012010342881300c00b40c3c1c0411650303041800300c031801d201c050310300d4003488400700c00105903e00c01c0010714100d001404001c1c24885e510f03540141c0d41d070850002403072513500342800101000500d0308507004880403000140081e468102042c1c0d219000b00c642810243c0c144202c0210240b024002c40e10040d00c5030005402112011100192141558020513541c000c00c01c10f56444a41c00159a60001d00d03166040780700c82c078a40380c00c0c1c1d043c03842e5200382c141c03880c50b81000e828550243e9600038115031144100740c11000f100c0c1c1148000300b20b40d100d40850341004202094800e001741d882003001d000c4816410000f400e54660252070300d90300760418845c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 471276771 1250 471275521 471275551
    0x190621091a09011404080901030e0f15010e07020a05070509060d14070501030e0d02030d1a130c030e0c03151f030b0402010e09040b1602011113093204050114 69
    0xb100c1024460382c0054407440700201140d040a42c3c1d180b41c18462503444504164996100c150001820701444004804140403039454110700952031410312024403c94039526890000290003c0c000318042c4c0d0013a40c00006800c089081000304a0a9840540100d4202207100d9503e0300092194150f4009900e001c4010410646400001015100303021000a0300b900110969410513030004141d94a16032410b401180070543c10300e00c0a07a0603800942154889404002104a60b425a01070100350760195014080c0306030301d03103010b40c0d603901c00744801d50150300a0810b800b019000000351034200c5940b2080d0f03c22203204102070004811144c000b514110104c0042c00119a08081d1100100c0c070f040e64440810301d01610f0b402c00c50800200b245100340010740d804940107200f0341c8480400c2514544160703e807d08440804001c890750b015440c200b0785803100d110036403500814019003406070603101d840d560300c0b40350020f0154407020b00704072090340d00e4010241038001100102c1d07218095165003121 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 471278021 1250 471276771 471276781
    0x306260613030801091a100809061b0a08100306150602061023010e06030a1a04020705060714040504090b06090f010f050f0102070906080c190621091a 66
    0x81031000241c009021030411000a0300042c0d085100382c0e0442d803c041340041c000445a008005840024098070b40c41019020702d2140c094001c2400c034001c0000000301d8107a9501c050614410b649846072030440d903c010300101110500c503182e2268400c00000074603800b40d070340790358038002d448518203280303c03092040e0070500610317030b040003500e900460b25040590000d280c0320380504108075151204070114104c000c2d01060740d019050070b000641d4090126071345c07413a1004045005001d84940c0c0c0c04100001d0500d042249441c0c001e0b42ca000b6000380103040e288c1c4555409403071101121140d0b5100c00000e01000825a880c0d02c41e0000c0c540c041d90440c1e4840c500b61080001e60701e0010f061080d8a8001070052100d10b9400b40e244060b64030503100703061140d00260043c0d19048140d4442e5664505000003c143ca102c0410031821440054841d0329600c00a07013020780c6030030400d00404001070600d17451203468244408001d14000300800000035891400e448100354411159103070b100203101013040c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 471279271 1250 471278021 471278023
    0x705090c03090d0302030106090b31090c080c0a0e130509010507030c0c0c0311120f07140109080d0807030e1603050c0d020112020d0204080f2524030626 67
    0xf4941461900c0d0441c55076051070805000c116213801000301910b070108a4007080d881441000d030041005080807440c614404500092110440c003914106604000c0580c3e606070050200c280100c02c40c005032030a108040d002102d080c5040c10b140c07580100049100c0c590340099228050050f180c007000441d06140402c1d02400356009143d401c010801d0351001c80c0c003c41d01558003481500e0f40b1038642050b0301c4451000511341000e0a0681400e400ba404100e0b561000004282007100d400540e400f0804080300010348440d003c91080c01d401d600041c1c0312901d40c42c03051602d19803014440c00c000a0308107003842e9091820390b00d1164a03003e00c01c024400e00031f100301040310b1071a418013101d0512034a205540028960039901503210308460700880d400e8070701d0506405450281c03005408541c8190b240c550007955078104240290303003450252506405448004140b039050b15210960004140703095081c04c180d42008540e02340816a80341c802160120300090a40b4105101201c018105100b20802c0d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 471280521 1250 471279271 471279283
    0x90b030c070b010509040b070e032505030c06030103020915010c06060303020a15020a090b2d040e060418031b0c060c0c08010c020616020a0f06022206050306120705090c0309 76
    0x5510401c11a000c100c00a807c150185512507a0362800c3d10b484102080860324001a60814071030248142c1c07003004c56507002081010440e50114211074101c400102800310510080c00065000301d540b00000b52450032804000301406410700d0803240d0300640f40c545008440d00f41d001200140c03c2043d000d010b11207040002480882c1108045241080c007240150105646205000e8004004200404003084400465110f011810441001040c0b21134070105d030f1b070b48540114026403942a007c62282d0030315215442c3c0d514404440c80380c0e118503039101501d82184240c51140058413a001d040005266026440c00409072a03e61101200300c130705d00401c42510a811510315a0b14140f02580c115500082040d0002d01c3c12035140558454501708a0030300104803001740008030b06c0300d400700403c14240c2c010020081070814610451107c1004001241014400c420000d1014004100540b506010001e4020f01d1030b402c03038608964032008903c08190440e03040d0513100c801f0041165040c1c081c014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 471281771 1250 471280521 471280529
    0x5041b110f1914010507030c091d0103231b040b0f0a060c0206040f06050d06060e031005131a09010b0d03050f030c090301050a091b050f0d0201090b030c070b01 70
    0x38015192503920740799038441d8195104074444802240341014420040c8110780c880c4110f50003840686440c1c900640901810f44501000a5034903400041f40c05800e034800b0005580c40c07054a956074a141c0701c003400ea880c101081c0d0300e0060752140007a404401004110b800e007002449011500441c00c0402084501c0c19121030b00a251500803804581d171031000120503107101c1d05146982554a002240460085802070564180d451801103811508000076200941d02c0520502c00b65031030f1001266403055a0200e6505070307120b04031140500f00250041640008000d0305c1000414071031711800d50f2110000203005002c103c05091189094081c020420100b00c01c0c0c880f4803034001656001080d13481a1307030410442d41008000300380c0707034601c61040b00c1c01c2c05001070091000d4241111000000d091440088901e00207602d0510b0803140b0100100c0d0480b0402403001c209800c148007801076484002404904015008801081410140028601643e42406510384501443c03030008109141a00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 471283021 1250 471281771 471281773
    0x905060f06010e03060402090703020f030103050f0607110c09090f070b030a0f051003030f03090b04080a080f090709020d06030606030c080c010512060618030f030a0201060b0a2705041b11 82
    0xf12141c1070744000078460780040e070503101130845a030346907401c4000b4000c51251303009200c0004000420f200c400900301510020b654280c914940380d80d2410f481380e080c1c3c0d0025200541180800700800d1903d019983d030302041201c00e80380b45207191881641040c01d81e401402c034881c801300610140040038400c048090ba8500c40c10000341c00d10100315803480c42030f4800102040301d161071908609100f0341260010581c05040e280e503a0a0610b0f04102642043d4800300008041c0070000e081c99450454150003584900042c084076030030048968041c0d40400d540d640c86c2030b115400080055075500ca42c100070340c0610f000b04400d60811f4903132818540c592410b1410404180480000d24540398281c07070700701c2c10072514aa91015842151a40e8014102c5191750600820740c6003c00c1c4400070000740400d480c10b038000c1105644a0313080100501401100030001280d143c0011000c040062411300f02a450010a00820f56550000350035102c011000c04040701050115446581d08040303002880c200141c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 471284271 1250 471283021 471283037
    0x7090605031906020906031611070609060f031407020d1d0907120e010609021c0e15072001020702010f03090f0206030c22050f0607030906051b010905060f0601 70
    0x2a98920040d40940903007801922502c0030490664121003240c83c0c083d10300d41c0c60380307462030b10110485118014400400c416003181000301c440440c1140035928503841c0c000b80e590807c2c0c0100e039080702103036107842410395610259200700c54268141c1d1040d411a030042c0b240102150004003c1600f1000080100400020303801d00c1e0b542d940c2145a02401a10300030000441c0c1d804820007401c810609926154603001020428820f40c0d0001d00c0d13100d4000010729038070305001d200141280c800f42002c10040d0440c1003000c03002800040d640d0f0f01701d203507480d012201c000d00c118145404845810705183c6694000352007821944c00001107241b1490703038141001710706200d885d401b4058941210081c4a503030008000391010502d0740c16205100891000205a4481403c04483c41e207154003e0511503548002201424030700780e001c40c1c000691547d070710f2f42c60b1494407605541c01d4100083c100c152403c0460b4000c2038000912898400d9070052000309a64240782e12080c40485000d0030303684c1000b0f006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 471285521 1250 471284271 471284279
    0x2a12011d0408090d08090405150a30061401080303010303030507030b030a0303090311100e0106050607050d0f020705102601050d080904060b070b0415020a0c060b0a0323070906 77
    0x403003956407015083d101075441548603c0d190100d8800c44001987c030500d1704007882248400c11800245407082540c4029285859040c030900f011240008001d40e01c40c1100174030a81144a00001001032080c00046404d00b000c21205074101026040880154808030041040c941c2c580038003900404681001c20400f080540130a8580c100d0240203018540c0fa00109010140304004180e0b90804903420366aa01010b003c10402602e14802e29800c40d41c20090080759500e4401c048901996100008201540200c01c00344e41c0707048560341440a41c020b2074000150781d10340c50303a940f4061805030781d070141c1c3c48160784042c00c00e00c42207001400d4840a9000602085e00d401e030b602c0d149103070820006520ba50400001401074030103038208510713094020599a04103c00c1c0b0701c1082c0205d214101c404003d112510006049001d6000c429002614900602001c9861036020820481c005820724500c5034490300c07280c1c40ca103d8843c804062f0209a4004a641d50081c0840f03000382081400c140030031031030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 471286771 1250 471285521 471285533
    0x50405010c0b100e0703020a0e100504120c0503030703050705060a050108030d11040f03140d050f030133050c19051209060c0109060f0b010806092a12011d04 69
    0x503050000c00d800061070202da0611400620f0b82e000705044a00c0d0b082070302d860b5900401941001c1040000b0410942400d0700c140391400d54080303c0d407400da441506103440c0c8070f01c0301c04903030300e41000f43c403403040c0105c0100d600e4405000520302c503070003a2200781c0c5e00d440d5440c00314a8240c004084004461405005010b806804011a4405680d9000200f0003096088070f001c128030460740183c43c8111021000020010a4440c0250511250055520313a140120040c0c629214120607101310380b0040005002c000f614000c0020004100c1c1c081d05007411540d440300e005942560501d00200d04003081e01d00395502c080000011080e19a607078246540542c0c4d4a2503a41e806400c0701d03407000c900106280425481d50f4065450340e0081c04001e002e040d40604004c0c0080c43c105403040302d000d06002d4079032420350054040754001c0a0207004c4881c5d075603500d140d004860103242d200c40645401030310051603200c1f440c0040d0049002460844100e0352400c14034680c1c403c02020429040760303181041101240c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 471288021 1250 471286771 471286787
    0x1030b0609060609100810050a14090124030f110d0e0706020a0203100207060b0a060c03080f0c07170f0c0318042a170a0e1e1f0204050d030f0f05040501 67
    0x31798104040d4648070204030f264240540c1d00305070b422041209c0300107240c029001649110030b50643d41a0000d90b203445c0060541c040c5414401c0d41e83c00148886425903200307500681410401602c00607a4541c20760b03114209a1264040c021080c0c1c5076050300b035045d4000c2c0440001001e60340001e052001460340425156070755000030300920f59002c83c03c1d60a01c20b507500704c0c4c45940c200800d00702495440e00e41c003502a21030760ba402c0d0005400840090448004034005a0007180814600c9042c080e4540d20340305a80c01d000ca2141c0c246c1400c1c0700c98040004024040e00d00c0d03c80b5100038648130302ca81050750710101200403c030340c03166061101f40c0d080c02260034451b82c2d1017000d420301c004003045040001d0b5400f0310100c1c0d0a4103074580c41030401c014102160700400c0200d80d14010350f016070407001c44991400000c00080c2d00071350000070104190f0114414a0002c030340c003481d809410035680c0c40c00591503141907107064000c42c0245603e200c65950020f488000c000450038480d04181c20940000c0480c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 471289271 1250 471288021 471288049
    0x10c020d080601270e040b070801060c0b0a0207060b061c0506061e070303021908041101020a0b011401030b0402130f0f0308030604051e071d04050c12130b01030b0609060609 76
    0x80341404c6003c16014000039060242c6892481c0e040903003003d107402d0a00500444040300042d21200010941c00c2c8200c04022500c3d070008150300c0c1079100e03030740004000e6010303c008698a5680d1801d40c180e40e1203c0c0050049250f4504110b145011018200b5090f500300400a502c6040b04101078241c0610580313444908070301040700c59444a203541703003d600900c101c4180303609041400c0b03401c41d00c0c81c0e40103021a00c03a0741b164490100f90079444006a99130018000001d20035207034800140002040100c6d82c2c440c0307041c149804220100c2d900c01041c01c0782c0c40003429034030f05884244140500340c1e031784c0d0811000341950700e40e0701003203031a40d29640200d003c00f4003410700c070b15101e0000c10303444034803c10b41e040038055030028103070b881c2003404000d0b191a00908a40d10004810181d00c05540341ca4406d15114547d006c141510700307007401c22840e40141c4000c04c00001507103c00100b4020030800404140070790700c0303400e800003d410440b040000c9400000c00c0c2d05e2040c84100700d860f40e5a220300c005081c040f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 471290521 1250 471289271 471289307
    0x170c0910020a32010e3f0301090c0e0112020a0c0b010f0f08060106021b04020d0f1a0103140109201b0721030f09090218040b0a1215021b010c020d080601 67
    0x1924100f100c20340b4512011548100c428806c481440c82c144a00000c42c1256035481042003c0700014106444018aa607001c1d4080b03107250242080c4200c1c240c0090101807400e01d010701d0803803100e0303542e1030340030800384c00240600650072000d104c3d22205160300c030b0103025200014007103503140410003951100c940000010031000c2035034200251300c03035070141c03982552004418000d004491070042d006190014642044200410380f0315095406480b84048034003030703131400c0a42a800c10319800c01510000b00c0400d01d1100c4131481001d1074140c070026114654502d40e4040c665401d807141d0920f0f080040d0041203100c0e81e0ba003103464100740c001e011100140e500d410a40d07029882050140c911040319441012031394000603080c031582c10b6581d00b810303a00300f08a0f000c2140599100a2190109050141c20700e88000d013950600450f01607104001408140c1c000035103081100d03071170300b4011244c010407419969150160b0045082d0188003903180c001c2c01c0d10740342089103040d400003401d4400d443c1e079880340c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 471291771 1250 471290521 471290563
    0x10b0a090b1606050123040b180c04090c081e0603010e0d050c191211030d15030218071b0201050d020c030307170c0910020a32010e 58
    0x11680603a51650041c180d052101c0d8540951169400c0c15000d40782049a01d98500340c000319200d0f0400c54114005c07000c440c114a0241c82503002c0c48010000030340c1c05d03940071a400074101170054000341040e1041d682140d0740380d16285081e4a1805644141d8032500034485800100074822851030101e5400c0b24007265200c010b501c0d0729003c01d0040402101d403085070301072142810b268542050041c00741c2c001440c2190510900541da4214140c1007440c02800f600120503808403051086d200c807400e5001100c1502d103490010032400041328981060759004c0402e8400800c154613200c4402c030000c0500c0a00c10040e80340c04a00140f03110040c907641d02d8401c030107440100039a4030403001d450311481e864008555036880854125683d4008844020004d11b54000d072a24204a4000d190302840c1240526420680b91000300100300543e00e0b00d060841c4035180505002c212a90503002c42c440b01c55410840881010101c04002182c0b55142e55150381440041c1021480016100c00d407a102c241c5616a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 471293021 1250 471291771 471291787
    0x20c130914060a0c020f07140603040c23010806030606181306020d061a070b062e0306031110090311040e03120106030f18021203090604030f060b010314010b 69
    0x4040c00c0c0200800030700e8403a0004000c2901150341c003a08100d8503d40132078410750903005009a40300111f000320303d5540100e080019040c02c0201c051034020748501c18036102030303031195400c0d01c203020038083c10700e2418020303100282c0c2960803500850700a0300a801405103480c00030b01184100b8008021042d940c482d440008400c1c3c04007544000c42e159020900b9540c0ea401e018140000e04641e006d03400c01e409102250f80750742640182114010b40e03204094840c244c1d1400200400003d0b12000c0350760035140916888148841c0c21006098441140c40000b250350442c100030074003580e81c10006000381800c9002c2650340e500801a0800c889e40400740070700c0407140c040464080c141414410b0114840800c50b0a03840a9541081d81a21281d0b80d0400c81100e6107440c4109131070790760703145a481070480164880541031140030090082d006d01c0c01c4900d01044103012507019805a8016180c007080d02101030b0410106018038040e42c0024a814091265406100c006011061084805046c80021001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 471294271 1250 471293021 471293033
    0x1302060408010e06061c0c270c03150906050a03061d060708150312040603020702030705030d1205010e060609101817010e011b050d140a0207050706020c1309 69
    0x280079142000080c40324007262043c8950320982520500d104444c0000740180e0b0b80ea414940100c040d41006800708042d1920001888480c1880b100c07110076a0300002ea052100001d016000c00f9124503a000282c08800903818410700b80140c00034465a03081030401c0005603a6126001c0589401003000901f20040b180011315180b280322029210f40110030400140c1600890213034450003c1042c3d03000781c0c0460104040d185c1501101c00c1200390000e0000703200e0a4401e0307000c3c0002d584060304a034102070b1210000703031a0048809107200090145c00d2549a0b16515003d102d00401c0d180200f5000da0518400086113801010040d034040c0300da01c110f42d203025214080722621050074000d1000401d448003000402840300800310b035003039030a080c0208410801440b07090403812440440686901212404480550200f1100d40d0155180c20010ba01c02c50380080c080d0080c8030950300141c0c1c42d58a8645503050280d198001c0003550003119010340d6a890b000044116150919000035400845203006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 471295521 1250 471294271 471294277
    0x21b15130b040501020d08240d0b0f01050307080a080406050913060303090302210c090702010f0f0c020c010207080606130e1903030b0a06050702061b0a060b01120207030503130206 79
    0x42a48010300c900090101403050080054500aa003610203c4040c600190751400b8203075142685041e030b000c400c00004c41d190ba107400d00001c004002c4520940030f03032212440002c0554070f0101c00003000700100719601d030800c02000204145d80113024004104d488a1020740160311400c414003400003450300756a6203c420030301d4408003d00302040070070f440e818002c1c002ea0072400101e0007418022180c00c1d9619100c090000c05038403000082c0128500c0100b8440c21203000f600c0c0409643d01c2d0fa041a0a90056026074402c4000342d850010f0b1006a070400240b0b408108185d16065420600701031003044000b00300c1c0b9030f0004040e01e280c2a04040c10302e2000c004c0420403160003c0b8043c21100381e402d1140ca0317440c40e06031400f968050080b10072640400c40400c2d0341e0721810b4089001007200d000181000006000081005141c22449043c0200c0060a084030030104558041da82c1a1580c203940c3c00007191501c1c06840d0f2070442c280021507078090054400070f810032014903060812030007155103540c11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 471296771 1250 471295521 471295537
    0x1806013f0f08120c1c1a040f09110406032604050621010b030601020309040f0207050a051f0c0e060d0b061b1005040503090111330601021b15 62
    0x51040d0100c1142000307190354100c00340320f070144074062000c11100545003050350000d1a143c01192101d00081c1020b00040c400b40c003940c11107041c2c1c1221800b19940c0c5105a540302d0400010101d404480c40c5808441000c000700c2e0076124a2518400f4004181c12102c4d0005405448a00109042007200c582c003007809a139002507440500000d00f1202d110501b4039603200a0100b60304007610742d0700da080d0580c49000c00c03100240182e0090204150030b00d0031707400810034503948040040c0783c880075884050401c2c001660584441d0b0014084141000c084400321807000e04d0301008100b0000c400100031304001c04461a02e02c9082c2c0801d5040e00d01d0310550040c0300626000303003907543e2480041070f40d000e0395400c11901e2801d030080384418400c1140a006641c425030f03002e00030b9031400c0b00c00c1005542c600d00c240c800001700d2042d200008800b06440c082c803d1800c00010304440003010740e007041800341800801803811500003100940316a50400030300d6000318011070704850000e260000e076040c02d00604072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 471298021 1250 471296771 471296783
    0x1012030507061a030c030a0b13030504030f06060512070602060c0306060d0609150803180103021c0903051801020a020109230604090b2b020d06090204051806013f 71
    0x100e194018100c2d0765960040b030b40c0650550b00c4224240d010140c58540f0b8120142c440c41c507423400224241a224501ca03503143c0b09040460801c5c0c1c0b29140c1ea6046442100b040715a40c0d510103042c0310b1031405a170b040d0026111303c2c0c0207008080c24094002c0d12404058082203070b085010002c80d066507034400c2507900d80c441f24141080003d584860070005080b01d007110102300701c0102c101181c11500030040b80c1c980310984c1d0103d9089460300c00110001e60003882e1040046107510500e0361001990b029600c0c5040c000d60350991100030201002c15500750056040d4155070003080c0d5100140d82001000040350200b40a1440c1c10081c40d00c5a00c03082c0f054a001e03036200130009404200c1840c80c0c4d000d5001c046098070301c0a420745081c2c24440c9564000902c184641702d48096030401885c00441101c0d031076220701da0200b200d4280703074042000d640c020b54003100f08869442120061b0741e41003040070300400a158150790720408000044c4002c5801c5500580441a4407444103020102d0400c80c61440c0c0e8481 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 471299271 1250 471298021 471298031
    0x12030b090a060f0b0c030f0309010e030c15060a050108070c0305250b070f0507060c022a0f010201051504020705010e060711010506090618040302101d010f05101203050706 75
    0x2121403008040714042c0700f0381d031a110040490180004810b540102c034080c0010f614240580305488183e4000521030085503413215620041208180042c1c040404510000c220200010f00500070150b0010011070156105800400c0260390002001b03070000071604180c045812903060031240c0d84190b548684044040b140b4040482e84003002c1c2800c1e15001e02d000161588540300100d0301d04500005840000b00c050003200003141036036020103001d41090040b00d011000096403030401c0c84403080c8042e0202030b960420850303802d000d010040b18190900c000c00c803030314041b90617480088040c00c031240142c0d07010400e442002004d40c401203e04c02d00070200c0d10b003460300030401007400303001100482c255403c1101050380c900300899440c0c00b451008040c4905098400c0c4000e5025500900c260114815001c1d40c2c100480c00e0300c240c18000c034290a54001c03035828407070100d0948044500921805180074100b200203102d113803000082c4c3d041c54120125150b06404c0c2102c6d580103010700903003800e02d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 471300521 1250 471299271 471299281
    0x41503060c090602060901060e071815050c010b10050412080c01020309010c170108060a0c0e12030d0605010504050f09131505100611060c13030c0906030303141312030b09 75
    0x400c510841c1e0084d400c40d078603070f961484e42c0b9080c0c4009200d031441c1c6503590030104507864010001c032840c0740c291a8009450550350003050301a415640403000c089400041d410704540828000e0000c40c482c213580f840840744082d40003c2091046204400c5104410000d031001c10000b8406c688442d920b00f80255100d00300a20854024001c0b610320a000c201c01c5020581050284d40025040340c8644010f0152036417550b00c04001707070035a04800e80400031401030011055440c02020100c0000f203200a607290b004e00c2e03100302d044030215040300c1d0502009200c00c1000c0e9442045072041c10380252515940b6807036000040307100700e440540c014050012481c55035000840744c2d1066116003c004800c008140d503452003580d511003107201c1d559194010340002101c0c180100010110010050b5120844c0c1e07035281c41d41c0051011540198092a07120941003040c983d0600035002001010b00c80f600c0d49040c041802e04588203031540c010501c507100250a10214000d900c07800c1440005809100c48bc03420b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 471301771 1250 471300521 471300527
    0xf030509031e03151008010b1303020d0507030204050903120105060a09150c0b0609060904111504030305040326070303051023010908010b030d0305060d0c030302030c0c060a0c02041503060c 83
    0x811142120b07850481000b1289030300c2d2144800f210800d05460f071044d5a400e01c41c0700c08c0c8507840803529201040c44a00004016120342d4200407405010380f002e0880f80e03040d48100801c1d11f201030715407043c44e4401c0c00303c05814900f84604c03c1c1120000c8403e0356846440800680e014881ca81c4000840c4038205402911141c00103010110340340704140382c20007503035408100000344505690494000000e8800100000c3c46403001a280b69001842c400d40021591a401001e9105800440004502250800801c180044800a5610001400c1d00c4c0081d0005c180645d5001e6143e028041503101c1c8086840700010032003903400f502d0a15801c56440030070710583c0385803502200807180021011600060b0b8420107205140c21410000c000d030800312007081c011009018081c04090340103016801d1000000e410704801c5000318802c1e0051900d9040d031001560900091803040c5000d0507041090445299112070f140001e00e80c11140060205413018041c20804a1a0002860140b901c45250741c0560 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 471303021 1250 471301771 471301777
    0x906060f0e0d030801030b04111f020c0a0b030f0a02040f0b0405010e180c0702010923030d0e0109060305130c030818241e04030c240f030509031e 64
    0x20060316a01c4149050105102824002d2000940064821401400000c14052505810038051000f589030401800000f40300301c03a000040a01c0107a0700110703500d90355010b010914000e4812079000310714918200c03a4041e10711000b881d40300c2141c806400110f00404950544019100c08900002e681d40c482101030840d50090041d140440c207503040d8001c40749400051489032002d02c0c40315648a84440c500030081d0742140c00128103100c900d1134041040e0744401c4d0500c1414440c1c1e040d40130600f410005050604142e1084141004001500c03a050392741c000c000c51003247c50520300054190341b002c1c1c2043d01d5400c401e500405698100030004284406080038007000a44080509190208202042038180c4040e10301e40390300e4060401800400c84280c0901900140c1048012412400444180031544507030002c07540e0205a1806209446c01b04926560352090358881a46145801d0000f5103c07410f042d00c1c010030140c6034000124090801d0003543c00c0045294401945034096000c2413074a90 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 471304271 1250 471303021 471303047
    0x50708071407181503061e0f1410061713140d120902030a200901090606030c0804080d090503090a030c080607050a0507080904090206030a0912030614060c07090606 72
    0x10040c90003210580c1c3c100c1c81024a0046082041200301d45140d407901c1c0a4101040da408001c040483c4021010f4201d000b4940300d915003000c0011200600c0100d4a82d40c00c02415000c00c138000843c092040399013106141d07010700301205a034221540da1080e0000c00c003901440007080700301d040034030700d08051000031400f03401e80d0141c50310b41e0b81942c400c1c06a0700b10b904c50400a50f040d80418000404640c01d0108400b01c1c8541c03106000014130920013041d000c520a0f84000c030110746c0c0b0751003044901c0c8d16204680c80e108070740c03030030409a04040e21012654000d1b0380b00d184255030344250900c00c1000030411250a82c6014140c1c02c8000da5038100b00455004c1071080028501031540011000b9100710110b6a00903060f071100b03424903039261500c81203034104d40b0740390350060354480040380580d640601641c41000d40c01c4020900241c0d078907201d030103c0a22590f1000741800e181050000c100401e1450a0b501c6065444503142c501a0560340c2c40c01c0056480307a03030481e140140c00b10f990f990020a07100c0407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 471305521 1250 471304271 471304289
    0x30a0c240506210a02040906020c0a050304030506090303070c081305150a080108030708031f050d0606061808031e070b31030806060307180b0a0905030111030403050708071407 77
    0x40c2c10032500310f00d080048450043c015800c584442d800501c1c05038403c115031801030400504010701403003150718200e0400405c0c0e406910110b0200104a400c00c003240d403052005010314114144490094520001520001d02d100b00229030410b101100060000041100078890f01000b82c14407442e54240c0c0c0a400300000040d0389400100e0800030010031154030550150120740382d44d640001100481c44400e10515480d0076024001400e039491152844c800e40c040c2c82c0c000741032854039102816181d602e402c01e4090700c1c410102040841800310075500c85822030034214005001a030400c80b6184203070030300180704128179010310000c0f080413084508810b000002d040e64041c0080800c00c41c0d48281c160080004400c900003400c2d504200f00696004801401e0520419110b00140401081580c00c40455001d0114102d19010342c0111224000c000c150003c1011050b0700348400214440208041e0521500003001410028800d0032106556045078500381122000c0c10031649130103c920130f003049 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 471306771 1250 471305521 471305539
    0x6020d1b0f290f04080c0f0f060114090601020706030f140c0a170f0a1503050a03170604060e01090207030e060a08010501021018020108072703050f070503030a0c240506 74
    0x42d011080c032000307025071602141d03030482d603507603a8400000382c0c004180e44d070050045030481ca04169040000100220151010300043d40c140012819000844860184540d1040c400d0261590b0007103041d8050711018607011406000b11962003028181c07200c503a9a181048008000ea001340e040040d04582003a69940800000d105400301a03210059603040d6001c44988040b802003a100e034802c40203e203ca184041040d41e50b0f440703031420017409840c00e07000b040e0100e0350485448407004295510610440d8100b02140c00c02c00c66800701041405603c070180d6000032003005150007000d811091010041030341d030b0b403401512002408120b0a01c0780038058404c410504102c2200f0740a0356159040750b850707520325114036030011540020040e0441c070501051411154103055840e00364103800c1d60700340c3c59800b41851131600c5407170610703200c68020442c1c2129506020780c0c0d401100300d0b080803413140380c440d1100340d01d410700d501915a10950020800c0f440d00c100c111540007900803c0c4200c10484040075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 471308021 1250 471306771 471306833
    0xe0127090b1c08040e2205030c0105010e010f0303080a0b06040b0d05150f1e0907030903110604110d03110102070b1906080c040e0309040606090503061006020d1b0f 72
    0x40c120001100503c16142808144030381928010b00c2c0303a00c80b518030f0f944050040d0b01e02400c1000b800c00001540d46400c00608031901c111b09002c0c840c01490001100710543d0b150042c8032200740c49a0000404200801001c100140200d0700440e241e59002081c859903590350740d681e0500e40e809250901c0116061000103860b215148030a00541030380a00400300b149000d2040040c50700444803041c03000c06c5001041940b585030810f0b418407078100c0351000101d451107820302406071004200c101e0950741c86101080006010050344800320081554020240007540c681541d61404075914010150701c045820030a00003a501194091560140c10148281200000d002511410f000e038242e25070100100510505107684601d142c40c42c01d038141d0f82040c5d00c3c5c20001d02510000d41c0320000207500e02000b805186014008240c0000003074000000ca580340400180d1100c0f50790340800107002c40100c0c603e00d0f1900c501355440041c1c0c5d1124954001c0f021516101e90994012512a45080c2401070020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 471309271 1250 471308021 471308059
    0x10180e1e060d020906060d0603260c0d080601020a08030f01060305010506210a0b03071401020d0504120b04030c1208070e01020705010801031707201e010e0127090b 72
    0x1030700458001c1d1400b996440a40c00f80b00b100ca90240405070440c03c1044408824038140c401e4401451050381c00c054040c0010500c2c90601c020110710044045081260030034140c800152a0000550760800c42e8150355500010703410b00308100030186c001e0f00c000040103a440f030218078840c180c8a040e10108040d0b43c171a070070701a542c0a01428100d074403080640d0f1000301c4c0702116411391b002c0c0110300041a02c18111001c2810300e01c040e031111501c00d01411401400d90780510031440c00088610304181000d1500301c2c0e180318a0b00d604c2000e0144109030740494203140c444e440d00540140c110694080c0825101e2000741040d004540080000b50f107664404501d600c085166021510140d5500143d81d0035621504501d41e01d0610041d4010010808080090318002d04100c14059210540d01444000b07030070704c00441d82c450042482c20790145010b441c0b5a07040520205c5061302031034890f400c482c1c0b80c00c11001c1030041c0000341e14141c42e00d9100084000854000c40d100f001d0581d03403d014645446195 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 471310521 1250 471309271 471309331
    0xf190503010b0711040b03031809071814010216060206070207060212250f080a090e01030f0809030a0501110702121501172e051b0910180e 61
    0x4000000070080c1e88041404d941d0004d60100c401132001520041d204001391441d0b1060024041e204414190030300740b807500d40005503100001e824683c2450103440c0304200c031a00e060140420761031082c1c2d4844030a034401c020a8403107440c2340e8401c1070000d07220303400a5a43d920494502c0014400c0314004a0582e1022510761904445c6c0101e10782800b01c1c041c2c01d025440c0c0f540300280c512160245800c800705215800c80c0405c0d50199504555400700030310b004045240c1a00002e400c150001c0040000503042000c080440d50065403250300c071013042d0f00103404c0c03c0c0c40070f00c05404c030740c20b1aa00800200100c402003001902c00c4034440140090042400c0d02c40b6940311000d10032a1aa0f401002007000003402212008007900646902c0c2030751540084180e44403102d10912010100d00040d21005107100711134000d0902c3c81443d020708001c0c46166002e2040e00011801081e5119034851001d0003280c0d104100c4012245d124101c035141e00c1c40780900704040322450f00c03109010004801c000030400c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 471311771 1250 471310521 471310529
    0x1b030618051e0312070f081b070201050d02120403021b0a030b0f07090308032502013c020c011b08040f301e02072709080f19050301 58
    0x6001541038490030902d500507202000e201ea404100480b00546070031052461089413103884480003024011401064000000c107048000040400010303070b2070300990700740c4110070b90900c0c000755100309152991b0041d000f10021900115009070621080640102c0c0540006142c000714510046c01e86041204815080c8000b03401124602d0216002250140406900c01c0390350802c4800d0913603a98a40c6004d5100f00c4203501c40d0a188210555010108102141c008035a480280420300c242c00131200d50300c0320955030b0340c9078150940440c10803d0742d020f40c4803001c0f061540d085480300c0001100a002e03242c0c07a000415045d40c0701e008841a14000d05405001e00e03000210342c0e40d041460303075034511100004040a207402150281450360300281203210710842a0f10703501d01342c22000b110216007400416a4191080d034001d41030600c14000302134600401d1084500c0c02c54551010000c0541c01042002005421048000340d00c0e400d5040365401450081034032035840c2c0900310700755821507a9000c2805 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 471313021 1250 471311771 471311773
    0x10e1305370f14010311010912080a0f0905130504020901080718050408070b0403050a02070e070c0f020a03020402270405190902011e031a060f07140a1b03061805 71
    0x58440d607111603225841c800d200c041c0005004000c000c80c2c0128200c241d1049516082090640034296070120f40c8000030200e84084010b04600c513966400680561644042044590080c50001c2813040806200404015140b121903101c092821406000200e40c16801030f41003100005111000195500489000c540b009291580781348241014280140064500348028000540811800721906016a200342c80d030341d9903021408030103070514085d6480840d014854104200d40d0ba5005400c1c238458683c02503120900010b5840011112940368001030b420500c08134004003c80c61078821100c1c0381e055034000c0c000c51040f0f001000140c0c0d40845600b841041144c1d00b00802442c20740102800d00d01c14101082c12105070b00c00b21400c441c03543c40c84000a6151400017420340428940c03050605000d036181c9190480c940c80d5074000e803140b288000d00003075004d039100c00224002d000402505500600c8254030380c0b0001076490080001e800151000751174030701c6a044100b40340ea00d40c0781260f4490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 471314271 1250 471313021 471313111
    0x30b01051908030301120614070e060c0106090e0106050a080f070b07051f020307030b030a0c030f031e0c020f030a0b0103060e03121305150c0d0b010e1305 68
    0x911200029404900341241c608030300200b4250030600107140a08854151001d1403a15410714006a0b080d80e005883e568907200140100d2652140b504261140c00baa0415654503001300b81600600c015440b6420091422a0703100907064190045070484000700c2d400d8030348907129070078151a0520264026a240c1c003000302001003100a901034454107000350280c07044036a081c500407400d082c0b121510803005600000700702c00d107034051044d035001e594260f00400316841a41d40d41e8008074010b01010781042c071160200c204251042c2c00101ca1181029015010b4030306415014012924800d0308920a84030041840348038240020320485c0750343c0101e8901401d91850300c9160041c040a110000035010420180c1d6441d110041c11a0150707180c8404a080c3d08414100355062948080001034600b041e0010700510341c52220541d403204402e0309000800ba00c0402c01070364030440300030040d07400a034603001212042c0e50302e0703000e035100381c0b15544480c204104500307144400d81a00c40e20352007401f44007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 471315521 1250 471314271 471314279
    0x1e06070806101b020a030609030818010204030314030a02161a160e040b1504030b0f0c0a0206040605070e10050c01060f0b0f16020d050a0309080c091f051504140604030b01 75
    0x2c00076000c03c5002412158200391070b07440e0181501d594100a4012500250600010010074210032038401c43e4030000710308150440d5402460212101b901031901100400490f5000020380d04940b5400e512918120f2015000e15146d0a24400803803442074035411100000d030289503e01070f107180300446658032501000310b00104001880228071007a003142031141c0c0800c042c0310801c002d1014601a002e06034032071034403043d00f182d6060001c0401285007018002c0726106038000408030f42265001501041c260f03501141204c082c0341c2040034076030081144c0740500d01c40f9007050080c940141848020710209440c0c84c2c02806440c824440d07440464020040c801840500602420100800c2c0c070440c440880d03181c0010f00a4502c014055a10b40c0101c070303c5070101504814218020301030321006d018860f90303040020708890030081c082142c1c031035005504000310f8000000b20000d040010f01e41c03d51701503205e40f0220305811502500304e0811403003106c80701030b00c6c3c0003042d9402c0720b500a00948950b820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 471316771 1250 471315521 471315557
    0x507090621060f091a0f2d030a080c0d081005061305030703030302042121110d02060105010e060712030e03071202010911040e1e1e0607080610 63
    0x78419103400e825500d02010a02c0701d459072450004010101c40844c0b8868a840c60224080d0440081d904c52462221000f445844e10082000c0e40040e515403c0703a00c40d000342c000d07442d406030019540c0d41406072801600400020002410141c141202103403503201e80f85070140c96112041d914021a0540d0141c100511300d0520018213501803090007081e403403a901c0c40482d140440d150003c40c0801e0300450f00b4450b024074490040d442c801c0030002100480e403281c8981480c8600f92010305420300c5040105d151040c01a820015008504130451f000c0054282d80203460325000e0207540e00150201454010307500c0e1030130654100540181030518800542c50040c0e008152407540442640414801900464000c40c0c80340c0240200350000f08071201d1918110b0b98401340b00d00100e104624140342e00c0c0d00315a0004041040d80d4a491180300e0621100c0070052a2865000a0480010210b4008100c164000c00c032a07004d29074035101c1b2080f580701c0c201005600e11a9410a40c0003841a02c804032003030301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 471318021 1250 471316771 471316817
    0x721050910060b1e030c09030a0b0105150301060905060a03060506181201020c1e0708030403060204030c0b030903071704090e10060611030d0c0504090c0201020310060207050f041d0105040f030305070906 89
    0x40788801caa00d07147d9807401190074480040020394561940e00010842410241c0d48070403c940000344162071581040800b404a2503d402024000caa010504900280c025409103010300340042c07000c1d8646c0c10f01c0c0c0790780681c180f04078031150040030785102144d0800414025a02c00710340820181041c2e0f070801c140c81d900e800c010640c1d0807042c8200300000801000600c010b10217940102e0016a89909506100c4801d10944d801480341410800c200094504c2c08400da540d0103520220707103403c9015819810703c950291b504502d820340c2c941078038a44a07000c0040d00220740007850768188925540e801007030320311000c641c48401054100704405080e4040c0c650080780c00d801c9508046080c1925803601d8421a1440e4400c00090f030350020a11031108203021010004006a00c018890729041c8004120b0b402c1d46401d841c1d021715181c5500440320000c1595900d0b141e40200000c006524050600d026950b0310208245e000c2f074601030200343c25600c03a1712100c080e1800c1d9143c0d034144014018098040e40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 471319271 1250 471318021 471318031
    0x9020f1e0915040e0a11030601060c060e120301060e130b01051207031e02030919050d1b060e0129060a110c031e1002040305060721050910060b1e03 65
    0x221064a6407100342c3e4603880b82c0c0c9042c0340700f80020008803013989403800b0400c010b040064400c0d1f0041c001000007942c00b400c00300d529076002d600414a1000c44a01c0b1b0b180c001902c209000c0c03144e012001144465003c2c40c6031540b0107080781c6140080740d04a122a085841c4006880e000400420668500e81014581a9040740b500d1070000b0b0540903281c07001080042030780c41109400e4000040c80318001003002841e110450a0100c0e00f01003c1a558040d6149d0111030040c041c0b00851208106400c040200b291004c0e4006070180186664080124000c0c00540013040426481500e00c4d28040c00400001001d9680130700003500d461a14074013500c0b41c0340c940d0695070441c8581100c803403c80d20b05200340440e4441c2e8030000500ca0580c88496810b001c5010202141c2610600042000c5000081d2090b00300f03800d07080050388030900d0081010800421680c2601c1d05007041d051009002001071a14403c24205204110741a20b54032440154440c51450a01060031149100c0016a08c04000c0d034200b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 471320521 1250 471319271 471319291
    0x1501020a0b04061401060e10030b040608030301081c02030307020a420b0d030507060e030423040c0504031110200a14060f0f040302011d0109020f1e09 66
    0x40042035460000c41c010459048a507162a804802c20404002c2c09080c050308160508000c0c000a030808180c42101c4003601e14201600d8141c2100e964403240e110740701410084055907070701d41c0c54110855540340e0910981c80c80e0920012180c512920100c1070303900412183d401b41c6200400f94440d0401100040300c0501c44e00c451119003880032101d642d104801c40080320309010b200e90140c0f099001c0307600d203980700c90040d44d400102c140026030140c104c0c0d45255000c1000180080c00048070791850003581c00c20003125900000c0c9000880c1c00410001001303100b01c0d010300c9a00410306080300e0b180034030310000702106003011003410b90b40351031850b80584000c185060900c112038000500362050074100d940009403c14108007041c00740300300310800e4180b001e600615075411310400441d240c0600402c0140000001c20200b0304051013900005504180c02c00001103001c103110001d4001c2c968284100d22a24072940840240d0505c90b01007100120004c0e9400400c40c44041800120308004205d0004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 471321771 1250 471320521 471320533
    0x9010f031707113c1315080307150e2b0324030b0105040e0a0816020a030b01060f02010c08070f03060b0f040f08030405030c0d06090501110307090f0509150102 70
    0x203c0d25400d84015040100b9001d400c0540013610070300240951010b078410000300d030001c146483d41c866203a0462094000e040024940c150001c03000b40400541d0010001d0b03000c00140c42c41030184100c80d0003095542d82004002d5032185e00f51031903032012800980d1256092040c00c50310b10045804814409903280d05003c14040c1005160900c10501030820200040c802c003414424000381c4c2c044240503002c29101001a259014601035030740000c103400038220302001441070240070032800038040d115409809211110345a1918040554017409018001a141c603500c0d000140305015000340c02203251900300d0030307488615080700c40500c84840d040a16031101c000140a00350b200040c02241900100552114101000c00400d44042da2082c0c40c294000e000038040703540e01064400304030f0b404450303c406850740b51400c440500f09249000d841540f03030007a52140d641d054030066120b4101c564a200c401c540310088440c034151980207442c2c001c858030001a40811370109404d2070890140103c0d12 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 471323021 1250 471321771 471321803
    0x9010219030b190611010b01140403020f13050f0a051f05190f09020301060e0111030406051b06090d0e010314010e0705040b13091103011232010b09010f031707 70
    0x141c03c8a6a00440000700401c181384c2d88014203214107203600c10709180c5440d002d8010540980b4078011800064490002200007403103a6507140c00b400b84140380c400050089140ca02c0c401c0707000300405c0b00c240501c40d05150004001220780c00e00d01d140f4024078a01400b480b4181402c3c0440c84c000300e00b190301c101006c2940401c40f6902c1c1c2d001c03400102011000541d4940c1003250040c00030f10741c2e150241c1802892440c01c41003903c044207440507250360f0b00e40700303444614503600d4521b4a100055902e280b401140140701d400240401e01c172849141396100c1c0710076900c51000440444200003407244030000440d00510001c0d008400081d0450300074071700a03040c103444480f090f456a00c4408884408540c044041111503190b000b02414400001300340e40c00d5600d0000d00d0480d071140100d0040030000180140200c4008400b100320020f11141420500e94020003980b5000b403540d41d040901c110445000085c58145110840c0240e1394407004007229014014160f0b41150000001210880f4601400b10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 471324271 1250 471323021 471323059
    0x3040f050102161119050a03200a060c0c1a120903091008040c05060f040504020304030903051002070c0f0501050702060304030512040809040c0f09290304060603020909010219030b 79
    0x7290321070207041181c031901c04840800101d490110010045e0a0000c0010071503540d07504a00170440e034012140001c098034003001c0c2d1206d6138072408141d60110340ca8170046100f99002281140703041c801c0140110640c1c90f8040c800041041c10300408a611080018003c0c0300503082445400c568100220307030406004000281f8003d44444840000420303010410080c85685560300340204800d40b000c901d400101501c041b401c1c402d0703029090040e03400001241c20180700b44c6509008540103019070380714203000151107000c2c0d840300d6016101201c8401c008a0f001515080c1c1c03600b11007050b1100c0d89803142c41d509100702a04001e20580c18040b082c45400c00d20045480c00da84a20310503400242d80f80c4210b000c10007150040045402000b807404074100c60035400100307040c16103008940c0440490103280409000d042121185803c180c400b0003440104001a0803450940703108940181c40c541e0380c00c000c903080703006010101502511950035412814000d07404160248000740c40c104601550301290 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 471325521 1250 471324271 471324307
    0x30b010305060f01170703031d0a0e090c1206010e040212030309031b030a021f0603050115092d050c0904050405061f0608012c07050a0206061503040f050102 69
    0x41e18290044402c120a1441d0800014054100c0004842c1800603d40303616603030f070b0210702000741480844c203d900c44841d2215806210144001e01c01e4401c643c60340a81c1100c1c80c0d050b83c2c2803d0070301c610f081c100303503900e440c4c3c007400c0120541030020100f41e0718209101003100c001500a81c1c1000d0031b13401d40c0b051000d0502c020361140413554000c5a94a04800800c01001c440d4a0380c1e42841d0014060580143c3d0301080000490381020a075586040a801c1407000601c01c0d5030008000707611b0403440402c1c03550b0140d40a4202c440041d030810103904500d6484c0303003c12180b0b41131404032054160700203012940341c0c010740c0c10103401030401d41003c4030000420122402920161003d92040c410170640c3c11000c11403500a40030901c40d0302d02e480c0340440282032020b0600510814240c40590f64400060740252442c2c1c07510990a214600c0c1040900079101e42c3c8010308110043c02075000059042c180000078118000309405018030355591a261409458ce8079002100d00b55000c00040d0242d03000ca05031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 471326771 1250 471325521 471325523
    0x10e0a0b072606010c081902160e07080601020c0a0e040507090522050a062f09060a080402131404030206010f0506190c0611210106080f090703050a0f050d09150c0804030b0103 77
    0x40c01011000b540000c1d240c29006030303141071141e0401d0414881c2c041803106480d00700c2f0300c1e420032421580300c13240140d041440da6062107070084601080081c0d01d422860240d4016406038007640d0416813568001401d44408a40b818035001f0051035184441d103800c44c030344a40c24000c006440780742c500e81c9c6d01d0200381d4600455215421803184908805411034480340c294100410090314030b03007803501020036040e00419200314140031810001030159102c0c8004002080f00300102003040480e003e1201c001c114054034260018840c042c000700b20100031000a9060705c50082007242800a9030400d08441c3c40e0740d14104040102424440000614034003803605030083c20903100d42c90b075404030055440825417003240420151803030010400b480d084068a60062144040b10000d42e0b1340b800094a40f940340d6200501c6845408c200c50301703000000c4a9070700074a105131f0170350f011b103c0720b03003001c0320b4100440c007410014401e95188020329a018002c80200984500611404d107071f502d8035072020010003640 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 471328021 1250 471326771 471326797
    0x301060305060406050a061416030309120302070209131b08010b010f0e090c1e070b0a05180c061809010b0c07081204180b03010e0a0b072606010c08 65
    0x5119158150040c10303889030043d642007000c580f80800244c20b0303454074420b11382444409000484012411401c64103500d0b102d030810a81803546240040003000340341026034001040008480100381310340201c4026a400505620003030700c0311622200940f214a10455140010280402c0070303101e10340720303c070090130150000203804007400009018150500252020018442048641ca0341e40780070302c540240820400350384619402c59400344201884074803441102000c101d03001009080d1a40134031807545840309101c103031100e084a41072805000102d200d26040b48070101d10a0900c5800b070079180420100da43d0701d0402801c0801c0c0441c10030307046042e1041c0001020b80209504211003030007440f000e4001d05080d8164064100280034a000e21311038a0090400c04100c40c1c0e00d604480f80d1080002d0080102401e12a803241c1c0c1c070021244215412410300303000524050044007401407003801002410302a8030040c01c84104100010505414080098851000700301d040780901440c3c0b1140c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 471329271 1250 471328021 471328027
    0xf01050603061e0f071b0602130e04030e0f0102070f080606120c0306010b090604030611030a15260f070305070602060115050a030e0a14010b040f0b0109031e050d05 72
    0xc0c942809402000f40b0244103000d4900b1034640222200c80d5400f050348501025a52102c0c00704840c0c0900c4070240d4801d14803a0042c0c8001d0120320350040c40b81f00000601d0a201e50742d10b00b40120542000c442c0500850702084007100325081942c06003000b01c20500c10b6407600350f2924034001c0841d12075080b540f9650302800802c8200e041c50290704158002031002080200d102c80c00190307440f08140200b041e9044c000c40c0140d019118207027901c003d913074056418080300c599110350001c59041282c0c441140c2782403e1107006ca120341100004190359681c0c0100c1c04059021146491152010b80c1010151140c0162103010503020300c5880042d5200d030000d0111a8a802002864040e041e0440341802218001d110718441e0400200c0340448000e00340414901680c50021342003981c071711005805400300f6240c80e5071501c410b40c400e0001000c21581007060802c60250201254401c5074002d0110300d21a0090010512134100c014152130389102c0c2c1942407456544942c14171000417418400b040d008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 471330521 1250 471329271 471329281
    0xc0807090b041103090604080a021002121f0302010509190b07050c100f0801050934170f041b1e060912050a0602031801110309070f1203030b040e0f0105 67
    0x2e40030780e00d4501d218007807403829400c00c00c10643d02c500303010f48000e1107601d00080c024000d40c024007803945000321402e030464903010807652620800d0421116401a90560300604003051140c0c50300c241503903010b0392100e0820a404080c0184007004500c0a010401039000000710343c92040002c0c184c070340c4204050511145190180301d4070042560b0041300780081c2c282214140b0307500c00440b60450b141114840305135141c480e45000100250840084041184a0301901006890b0b1046155050039603c14001c2c23a1743e544200401c43d001d4540401103566400417401044c071140c11640b0702d1078203001035940c40d590b490714112941100100c0700e61045100c08104011074004c1c00703e00050800304065810004985e0f07605807151285035004141e25400b001084a010702c003800008400b150070300030000d81c00d03400e070002e00b9600300715000c0701288680d580c0403800e074500e254007100721172550403055008500da540640c00741c111200c081da0015a00c50020b59030600070411071120080c61400055a8108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 471331771 1250 471330521 471330529
    0x9070314040f0c0b070503030a1a04050f0f01090c020c041119030504060501060302030f1602010b0a0b0c070f080a17091c0605060f010203090d08070f080c06011a12040c0807090b 78
    0x159032045071361000500002d804107402108070307035118065950005120300c94140f0300003030b00c2068907410f411134a07040420211410600743c49006440400003210769a9075802a0000d0b1443d800c884001130b0400c0c0750100c09801c040c2c2000c1181d60302030140508000e4861059501c2d240b80342c42d041c000948480a00050042d5403048a01425013071809600c4d600d00396110303020909029151140c0c4014030620b08000c80d100b03600400c00e65000416040b5480d58440c00c071503058005a020100900030304d480010742e204030a44100480c1c0c00c010290074102e0b0a43c5900c059241d10b24090b00c0c60160400c00364a03d540e961000c10000c03143d120090b03248001ca814400112000102154010071245500c60456a0008283e403401101241d5803030250303610740fa00081a006408004002c11115540701080200e05005006c9654000049488680c2d80c1d49500c0560901c680425034018000c2044558100391002c1d02c55100d0300500428190790b85e6820072518100440c0e110302d10707144d0744807856580c40c0340c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 471333021 1250 471331771 471331793
    0x9051018090201080c09041d0c0307120317070207050a03141c1d040b091312050f0715020c0a080405040f020f0a080403020a050102071a0604140609070314040f 70
    0x85240c03081200d48202c0d070020b040000050b0403c40c1c03801021500c45079590b2190050420402500402d1200720121001d0399600d81d19801c0b054404c0c09018030214420701c0c4440608091074259072000c00000004d0840613407004007a100344218007642c14086820345801e00424000c0d48070303866220f1080740070f520190414101c050310710b4104181040c400042c030f920407551000c6c5582c2d4002c20b0002007a90000400401075030048a0b0408080c8040100c40c05155107a04035207401102c0c5810b0090121004555520903186a400300c0003043c4001c001250100140e110303d1800302c18018079004004000300c0c0f60042c082c50440b0040000a018040f60405010b1200c0d14a484c039000e60030640c04054059190003076254200c10004040000740c00e1520803c0717032121441e04900210365504036400c001c124052606022414401c42c1305c00b066144c00e1920071040300002800540f056900c8001c108050703514082d200b40308250b00c40e14451318000740082c42d039000703501c40c03809045501524686000d15032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 471334271 1250 471333021 471333059
    0x20603041e150501060e030c0112020409090b010302031204030506360d090801180f060204180905070617150a08120309060604020c070603111c0504150b1005090604090510 75
    0x883e02d01b01000c01e45000822199500003401e00700300c0300c03820403000ca0090240345d01403820a402c1c0301e5520144024601c00ea07043c0d90003030702a5000038082d190b84014034030442c0f1000340141d02000014200c14050346101c2031800c0c00c1441c44da1400207000002125018100da09000c03078016162415607183c00c0a26030005100903402803065513001369500c000404491000342c9a5102510320500b040265412030b00a0f280d11041c110521002403020b500500c0c1d00c0d44122442e10030780d1408038a680c01040a82240ca0500310013061075520307600161480312a003140242c11444070200411151030600c030301e4008480300100309490b85040c9204a07d40000904100d016034810484034000f43d038041001c0d0300b03031030060402040c0c0403000c1c4080740311840703180c40090b0412149541c2010201240e0806405540500d03034200e0741f000c2c801030010444021520a030741c0b249216280120483c01180a80040d42c2c1c0184920305245d03442d1800700076914100e903a03054030107000c44280140c01159a07140c801c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 471335521 1250 471334271 471334277
    0xc10050904050610051c02040b22081209060c07080d0c0614012d1e0806060f0a171501030609120203131a130315061e03020603041e15050106 62
    0x280d0b945250240c1707644190038400050301c0e005402001c0081050301124010720413a8555551040849600c016142e001550714901113100000003403058000645001808c0203c440b851400c010001008080c0c0e11001040c58140200c04000445c0706080c000320b070030203040e41c03a07601e41c0740403501d0840215503000d20026a10640c840040c082c00303030b11080c60700300c0c2407185001000707890307101d02102c503481401d520a5015040c180d01d2441e8000707084030039000311010f0800310781050702c619081044030f2889800c0c01b078002c80c8415007042800b544c07441403000a540441036441100c03219840302c2180600742c006540054946094904000802080300e244003032910240d410300180e02055107a80300c0c14400c0400003201550001256a819011121942c100e990050402d6580b4503001e1043c4004100700703804946401c1c00000c203201d00038010045040303c00003424a1500350b41c00c1002d6504041c000742c9059038103d10540914120303818000030113000c2c1c03040841c230303c031203040010940710140c00c48810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 471336771 1250 471335521 471335539
    0xc0705060f0a1b1202011b0804111e040207050601030c12030903062304030f080a02070f02090a110c101a0f101413150201021e0304050c100509040506 66
    0x4022201d09664000e84140b50421a078001d0191401d001c0a51040150005000c3c0700300506060301503010b290050700031300c10380700d00e013000702c0041e9034039002101c02030f001c8040e40540d41038500c1c107072101c02110303900c03051155140c00185000c0740803a000324400300c4181d0b1100e40140140100860307200014494107110140f100e40c5990010701d800d0a92000030700340703500c58044c17021030408040340001d8800c00000e45201c600d071905005202d01528062507010800400202d29003105078001c80700d905400c05080f090103030036542400f0040900910418100740d83d804480303081030000c00101120002c500c010848402c3c2c1c040701d0300845030036050319040e10103039804143c41b585410080c2c080d0702200300c4200c8900d249181c0f080d61480840c1304043d00d003480c0000d01035003075070003110b08006640c02d801b04607800d4080d14809034200c0c4117020001711494ae00e1142207503551120001194480c0c0b084c401d460b03021a2000c0415084200075020b100410340c00700350301c4003a0426101e00342d4403c104440d2800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 471338021 1250 471336771 471336787
    0x50c0306010801020f25020d030503070f0504050307030b09070b071b061b060b031f060617150d030e060a0521040309050d030e09090c10030c02030901030f18080c070506 74
    0x1c5c14419200400c81c0c0303955080b50b6118100c8501d00580d034443d0082e240310071103100b03440c0007892070b400bc85800002c82c078000060141140302c4c03010380703040e1071018009082e000e01710f031a80c004410700180f03401454403581d400494828150000b52030201e00c216515644000c84124401c440308a03500301d84100441260700308030f00d6501d81c0010003050b822080c0040c8400700303180800d003000f6104180403100c0001c40c00140c81e192080d4020310481704c10303640d00c1c0e100901303040c43c2c40021801941c103541e40c240c0b03244894020740351207c0049000b9200e401c01d599001e8113503001c5221500b1088103040070031004600c041c0f04101198081070340c4003801100c170045142541d0060319270042c81c020030340942208103c41c020036004451303030b500d07a101c010a803144502d403550445030355189010045000e54084111402128000d00404080014903006142842070440c0110010000b8942c4400c2c03064031070708440e01252521521510050290306166500c2110010061070150030354030040c060001041011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 471339271 1250 471338021 471338047
    0x30507090b0c101401080d020604020303070b09151018090f030f050405060c0307030f05121302130218010230091527180a0504031803050c030601080102 67
    0xc181d070145001c841d100c0071031400725454040703c03030303c4600ca403403620740c030320741d040320300e080098126008407040715040340940f00d0807602d480c402c0e50003d401d64018040c94002401c1140c899a12030608011140c58061986c500f18170b90368183c131403000e442c4c8000b5050100c031003c0752a032034220400600c28481c4c05829a01c4088000e0030a0018082007031019240d20a00c0c49103040310004d0400400c6030340c440a806040341d840c2e50000204801144c00c112001c02c0550041c1e041c1c03802d00040c0c49007040c1c3c41da03070180c2550008812150403030344040301d08440f009190551002d44025090030f029248115011400a880d0030201c05050901d80c4c06501ca10149440c181c2c03074412110280046c464880089002156041c1c20300038590317040403400300d580040e981c4154252480710354000019a810303080e1130309016540344000b2244030340c05044e0000440c0a03116804c41030b0003034440d1509666819581c0c00d864111559504210350710b8201018003800b502d410050306000d01038000c021032038200941c41c18 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 471340521 1250 471339271 471339287
    0x61807030b1c12120b0d051b040905070905060607060c171b0a0e0d0b0c0711180619080d0f030515090103021c17030a0f0501030203301207020706030507 67
    0x340402c04c0b01c0b20440032501c6941c1046a42c0fa0740905041c0d0700226074a0000e84450300c1c1e8101e1282192541408201450036000e00c4079541c0c2c000d4040e100150801500030041c0200810750794001500300000000298a441904c610025035034521040c1040c605404100e02406400b0020f86811613402d04441580202242d0001c1442e0400011a010000125008204c8200c1c050b107500105020820b48941c2c5030014901f15224500304070f10204e0704401c000c4150f2807001e11151a52142d40001c606041004245024045000c0032401203035450031101e2421421820b124005504010349981a0b40c00d40521600042050b50200b000100f02c408940c0800c41407001901c80c4450942d1080301070100281640d803a6001254043c440001082034550f41d4000d40d00e02c01401c0c0361a880b04500d85403403048905072a8014090507188001c0d07081000c201ea0074020800c0380542c04c400c415406c2001c03d0041c2500380081c0300c0c505007440c14510107410300e480b47d440380060505100412000903804029 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 471341771 1250 471340521 471340553
    0x20a051306052d01410a0809190b0411120d05041a07171309060b0a0e03030c07050f0621040302070f0e07080a020409020c151308040509061807030b1c 66
    0x4411500e00d01030301164840b40c5c06244000c1e548070004070307008803551006013203101e070000108403240b00700790100b0820f01070240300c8017a00d0001d901000c94009641c255104c0908407008254034500d0068000880c1030035456101580807440000d020010501d400e00c24105444030302a0304c41c208a4203485148620b10700c031a8800c600d440c0011345800d0414a607848401900c0207010030001c0070b07251031341c00004d50311000500021804400d039400541c81e0000072103890484140203045114648014020600014511517610a2083c0500c182141100500700c2d10780d80c4600b50080e0608013070030044e003403c050340c01510100d01d4030003040c04006514249150000120304d8040596a00d080d0050700a0049030002c5002e20f000003801c980d4284002100c01c070108240e55002829180d0b0076607419103010040c8010503030801408100524a0702e52440343d804800a000030340c200c0c02c1070a01400c02071049820001007a81c0301c0320010f0f0350420090903005099801030784000f0968a444411204942c43c2c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 471343021 1250 471341771 471341837
    0x2d02090a0302042315151c0e0708010212150306070c11010e090f041a010f060e180f09060a0203222a0303140403020a051306052d01 58
    0x820070f40420340901c8204d044c0c001d040101d0726a00b4603030412950045030a0352136100300b000d2006985143e10031011201045c00242d2080308881704455070f0000341c1403092504402d4000c0c0171300040e81100a000030014081c0c000c5908000b8502548160354840b1030002c1c25000b640b024003041034160708940080c40603034100380070030b507041504c400403140e4050b9040f0341c13504680c0d0300003440314914103194041c0c090b510640c25008800e000000d0300038030107400d215100c01388414601c2000780b507000b00c510481c1050003402c2003926512941007112401d000b5106036501216180411541c140c060107126041848007005528504101c06065504c004408202034038140d02d41340041003008040320182403071802010030190020003002518040078a00c01070b030104000d01002d07040112900d08407000d49a009024202c8a402c03d000c0c000704a40300c00c15440c0455407000089050360300c1c00c900e44400c1c02011800d4005601e07125541908070300048645040c0410001d4074141d071441c1c00307102d80048004032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 471344271 1250 471343021 471343031
    0x70503150a0609050f18130f080408060720060c0f120f09151b030c04180b0406050d030c0b0702030f030a14090d0f0e040e012d02090a030204 62
    0x95102003009000d1594540c8440d48030000103049810003141022504220344034901404001c0a10101c010b030741c02d83c1000c0204281c006910264007058483c0101d014401178014859607035a41500341e13215400401165104078100000030742e000340e00000e1101c040c1000041d8140700034800303641c0ca101400c1c0c07615100003c680240018451010341c0c520661a1006242c9401c0007605c0407004101541d100c0c890f4000d201610468660703001c142800307130b0b001d15441010b00100311510a41d540000d083d0044081c41000001008811881c12040100d101c2d000002e840003c0710400044440c43d6109d640035060542c00d160209800000820400723402c001104016034450008074214800c040c0000205e220210501000c8103031076104030311610800c2c0108480740c842000b50382e40d81010808400003c0c030b0064840c00094072403c41c010210f034001e0700204100f030290032000c0c00e4030000600b1015050700c4400311035002601c88481c0d003413242214400c5140c070008101065140c440380c000a4011600c0d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 471345521 1250 471344271 471344281
    0x3010e04030c06050415060504021c02090a081b01030c2d0905180117060402100c0203010b0a0b1207051317160e0403020f010203060d0f0203071e170114070503 70
    0x30b6000100040d0b2142040000c0e103010316020840f584201e41d14119945412404910f90800e07108443c502000103074580c004075200500d0101070350028105680000000b6030008149100300000201c030101c5030b40f40103a600a24000404039101c150141007001005a4455600c070392201c0f00c0414020f00d40518828014120425515100c05a11040d0010284400b81d081c111114505a042c0c49001580000d2904030001c03c907a100e20640d406540a1a1807180b5050507003d801608903051001e000032921807008000a0600c040039800300c003804074005150f5400944207044140e0285503406c00c5414900400000704050384540100030040400b260141007900040000b0600c5614055600400031f07194102d1079840c0070243c9045016201ba6100e4401c03a40044c02600d00c06d03080075200f9a00100c80b40c0720b01c410041c41c07442c00c2c0d030140203840380464048172f003840e014a81d444001c1005000c1c0c1c0f801131018a0724082c2c8402d540d59902d4504514426065280020f4100b50186040d07500ea486d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 471346771 1250 471345521 471345527
    0x1204032a080304060309110f0315041a0103032f0d11010e0f030901080c041410050717040f060e130c090f06020d0e010503100302012016050f1503010e0403 68
    0x6400c44600c0b8440800c0018140d54550010050280710f0502140d5451810b01030010a0410710f055030340c10707040240d00880300794210000c50382c054000c01c004c2c100604070601d41240c095080e0000d5000580304442655144403c08040f401c04003400052171685561586440d110700102c0545e10070010307001d0144540f240250064280076501d2401d58484810f01c1f613216540307034440170925000c01c003840006038034804a01c080d28129401d04864500280c0c0e00300402160710b02c0010100b041c4a01031200c0c40104102804110071104c05c040165aa01e0422540415640190344000c0c100500d000c050003030ba45401c420b20480c41c4140d40081003c1d81c180c14165106c051640145880b9902101d0009215500180e01d00050b881604c9451101d41c0e0100111a01e1008a1310050807642c003000400055104048204142082200104106054038019400c008030f1405000b10300c4d0901e01d044c4103e01d40711200550082040741e03a603007a00c103843c0e44034219020500c103013580390680c10009024180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 471348021 1250 471346771 471346853
    0xa0201081e0a0e10140a0608030c0d0f0c05190b0c070206071b05222a08100b0403061e090b1303050f0a020105100501030e1b120106080f120403 63
    0x40400103106101c0071110240030618111079002e01b0138100080090700940200c01c8580b840720301c0000d00f03245100017030155000f43d0020910b0301044074510501000c41d0b000d103e40703440c07451140e08045401170642040240490090045c1d2184403003000706900603507507841110101903000c00c0c0d402c0050311644085500f102d180d80403980103660203040380e200c944a480541182070144008000c0010000340c0e0b940302e4158200385003041c42015111035425030150380070503441708001403075142c0d050b107615400000c0e4205a2040b07d095840e850180703c1004c81c4075403583c091300404420042507240f9264046258406401035440880041100f4140b62049003141c001e00c0761500385136600e07481610020300803c000c4528500b200411000460715604c80c1c064061226010f800030318581c103140d02c0701010701c1c0e40d6001c1603901140e002d41c40c16036142c1c280035013030040c02088040c24181e6a02030b01d050801d9060440c480031002c04000c00d20005949900c06004541c0c5015941001d81d031030840381d03043d88 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 471349271 1250 471348021 471348043
    0x90f0301020d050c0705070909080d051504020a020c01020f01050c070b0703111206040e0c010203181314100b1612050d06090b010f02060108060708091603050a0201081e0a0e 76
    0x742403104120304c0da10740030018501203218100b2103480c15a1620745008a401c040f0b4010031021080291002c06012900046d030410039400210fa0075030480b0740000c00320792003442c000e00035801c2035122001946e0140040740d48030354410002e20540c038003000300300d5040c814400000c00104081010400d01d0b80f09921203010107408229851350b909801e080130207030306000c89516101d80d041448408101c8008110b030398940070113070004c504100ca9a609021241c5500d000281c000e080459001c10451a41c01000090960381c80031808a05015686c2221002550030022000724100550304001c01e40800700204982c20901300000c40700c07020000c661620030f102880c1c0c0305c00d04241000c109803811360b11180302c030042600c548120048800c4182d8450200b40304400030b40c0c00660000f5a258000c01c0d001e980031400d1402d456803146204c46891000f0300c0782d001038031240c1c4144104400c40d41c000303880c0d40c1c20600240b080041507401000526091200400c00c12150340c64030264802d20804101d00c403115 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 471350521 1250 471349271 471349297
    0x10c050f0723010203400201082a070c050909151b07051e0a1e031404060806030c061c0c1206090f14040201020601060c08070c060c0323090f030102 65
    0x86c282600003503a5503010800b08101044001c000c80d1001150780014001c0300c6407038600d081d8200c5141c006607107003d0024003030014505c0c0d41e003007440303180201030014048141480887d9250329080c14603541c80103203608121f01071030500f0709000001000103070b104101200314118100d0350755100c0038280c05d0072003550040405540865100100100400d90712070181c0b0080d0f1861210303041d46070344c0d0350b5000103950243c403018000c22210000c45c0c032114403140c0c182c020b040270b8010f030a0701100541140c2c01a80460001041c007000d01ca19881e0a0146101c1000100d5040b402c0c60240308000140710054040304407080c0d501d40a4281003801030400362044580c0301c000f000003e44c1c2d4030f90003002c0d20b000d4168400c620300c1c1c40c2c501c03035034102e042507030901554042e40144580e84c20603105032495894603d080e15291001d010b05c90000fa240f100b08000b9001541c4c5969035612245800f0302803000340d280311081d000641c0080000310280c00b080d1092084121004c0c1c0ca07035818007003c01d00922810031141c1030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 471351771 1250 471350521 471350527
    0x6020705031308030c010506090c040b09041119170106080c09010917010b01080f040503030c0c0109062309010911240a020d171302090910140108010c050f07230102 72
    0x510034020014040d1340d0415002401f455941008000f0040011900d0b95004c1006103c01d101c600707000380c043d10080001410018038806003030000602030b049a5034003100080c4450a0066056002e820504004017005141019504201c0041c2c01d10600411030001c1460116440d15168030a440000081607107440a403d070401c01244140a020b002c0009404503000f403020520350103461804d2817060760444003450030340d02d58240010b000c0d0300c800d008100640d00c51031884041780680c4208603030110b002140001066020390341d4445c1282c014200900769241052020220f0115960644508400c94482c10a11160b840040d00708146000c0c0884c1d075507002c2560b404164000903040b500d031405840c0c26030503032500c91603900c0c056421506140c00a0003102800010300b40941340c1d41e081140c5500f0340740d8050a0300d54450461f400f52603502e107090782103001004090420300c148008290b082c030f0305500e0240711448401d054403803c14024500d849480e01402102d1224400d16806a403203002955 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 471353021 1250 471351771 471351779
    0xd0212030316050403080403060c020a06020c0312180c01080717091e030a170a02043305130e04020d120e210a0204090213090807140a030c060207050313 67
    0x3550303801c11102600120000c110000e1100d0107402a541102d510061491820382035a44840107010010503440945c41582c220100099041c0058088451000000c644031010020021040c0b000030305160792000c1828451070700700f1b1021810304120f03034003800c02c0740e01601c3e4440d084451761045608484060700780014018410004224608101c42c0071103809201480d1030346c0c041d200c1c4140c58668001c03070400040c1f1010a85143c000c01e900041c0c3c081c0c0103080a590304d420018001c100d16184007051481102e910500e280000404110211032524a050160003103480491003010700510044450b02030005003103694400d96102543e5002400041140e411280501010800401d0700c3c450035402a0015180810224914400b1000c0303005041403140e0350207001c0103000c010700c140d0b0400d00480300000d04016900520307004030301c505180382e40d0302114280410800c0309080216807076000842c5907804668400009400c00d40c001c82c0044e40c548440c5489032a40c490302c80c001d401d0382418a0b0008e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 471354271 1250 471353021 471353023
    0x9040510090b0f011a390606090c0c070509040618050f060703140f0a0b040606090306061a120c04030203061602010e0c03190c0b030406092d110d0212 66
    0x140224181d01c503600c040d0b43c8425005004d088054100840d00304207005100c1881c10a25102c0700a0481c1000c1034031040078041481e4603c0074020403a0360547c080380c2805601c0c2000030045070b101034959141420584181e4480352101b03132501c625881540b0f64004541400100e504c040d8011401d103442040490803071401a8860003025003400503401070400080016010b401404400180340c0b141c1c11043d82c80d94045c02c1001d1002d00401541035035100c0003134941d11a845080e0261103240c5442c142d1038658900706003610700703581201c420700c003103400f010030310030815015a00460400ca00c4244296201071180c00140215800a075040c070510f01400000c03501007d80c002a000c1c9540240b200c4580107812a90b00d0040300a107a406501c20100100c0e000e94203c042e0038410300c42c018841200d031307075541441c4141e003064805440880d0384042c0c3d542000824031715118881c0c09a5040b040448044200007901c07248114040e00950319203660a5881e966103001c0d91140c2d074014030000d15035581c02411 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 471355521 1250 471354271 471354293
    0x30d0609060303020f0a020102060708070c12020102090a08070e0f0408071b0311030d0f050f040e01090c030b010206010308040603020708040909061b02070305031c060e011e0f060c020904051009 85
    0xf0b80240c003450304100302d44000803036803a05041d0107800515042d11000700480b101c04004051708100103007800403000003410303458075918001950340003503204c44010f020065080800c0d4040c01059000300820803895100384540303540500c414003801d0700c96883d410059400d202d820300040c034001074000402c4000c0101d54007a41641c2c0607240300500014072400303065440058640030b0000c42d10200c06000e03181d05c0b84e801040c81024812071142400d50340c00400b04100804e030040c0340c42a0300c07900015643c6030b0501c01e080042c0002d1001703029951464846a020788994003e510030141c00117415030078002e04c081110010000c5c3d400c200140685424060004e0103004249440316121040b012981440004c449065a42000c040d5242c05120100302801d4107403207202500c0d0035140e0782e000a0141c0a01d40700381c000c1070302d06071a4004403205100c0d110302e4001d541001c84940000c1c0c0062056a502c0540d600c0c40710350658104015407910b00b095440e010200c508480035a040200d6001009a41008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 471356771 1250 471355521 471355523
    0x30103060c09080303060409150612120513120c12030e0a0504020913022104031206060219060b040e0714040f0e0604020108100e070f0f2a05030d06090603 68
    0xc1080400740c840d20844088040744a4104164404e0000c13903268501580300c00c0880c2d1007011402ca465040840c00e00948003142e000c0d040d03480001c3e0840013030224030480e45000070080e140c0030b40f500c00c0c441d11480b01d00c1ea090040702e4600034401800010041c412044902400d01d4241c0c82190000e945001007503603030028001e07802400c0d004c20014140c00e081c02525048440100205a08031114444500035009000d0b81d06614181440c400a059003000035540124003a0750f8104c034041c0b028514000f50ba0003584014210342c443c1d00b00c0a00801c003c03840717a80b91a881f50b408541d0740e0026002034064241c854002205004200002035011f4080c4840d101131402900e06010000d1200c45800484450810910301c2ea0002c42c00500198880c030705c4903900c60760449110804079110701c40d41c15951000c07140c14000c00c0b0703000c454020258024900010303500c06444c1410401019240041144010502da0310130200b100d00710a040140c14801d4034210b503282e040030850541d44003181c0004c0c180500c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 471358021 1250 471356771 471356783
    0x50f0601021603021302180a0e22020a03020603061801090213060c0f260a0206040b01140d1b050607050714090708010e100302041a1c0b1f08030708030103 68
    0x503a4a80302c800c080d924200326a0001c10940c0800000c4080c071021750700c058140d0091030041e00c071070200713556060410406800301080204007440d1221003017800c4a1030302545a0500540444c11006941c3c4800c07078400d4030b50580d0f0264503519250003194071038076004015031041d0040d800104458140c0c1e409064408080b03005000660381c1e980c4183d030104c078158006481040022100e5010507200050341d880c0c4202010644030503d0b1228076098260480007042d80143c105c0760a00c401c1c4101081c0042c003404410b411030301d00d00c580c1c40028a403145055001404601d25409600081414104020042002621039569840545407864a9107164003900c4403d200c0314500c2039060500d8030302107226842030b444010599080c050148940407000306001c9070501d03105c5020006841c1c5001e110b454070b003000207003551000c100f01044440c0c480350810444c0360f01e00b50041004905080025500503c82100c5034841c0484022010841402904080c1541c8000101c120402c02c40b00000c40c120380c0699 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 471359271 1250 471358021 471358033
    0x201020606060a050f0a0e13020d1b020d0e03010209041a122a0a0b07080d0b01020d020a02120a020a06110f2427070602010501140604210501050f060102 67
    0x7400700300c0103004201c502400204184119840070180400078046001e260528113000c41008001902c81a4080304ca100b42c5500410125400c031014001c43d8180b0307840b403900380d00b070400c507441c025a10302914054404100c4400d090710310a440030b504554131114050000d0110030390000c0f580080304d0500c1c400c0c1d402881d00c0c145a050015000c82c000c04003465501150401c0040403120030443d0514910080e804403126200194860b1031000034050548110b00c820f48030088507614000700d46421120a0540d0000c4e40c115801c1c0394041625500203504550f0400c0c52220340c441d0703516013088290b00079041028a40082a4260840039142c1c10040b000e00f2290220107015100e0f445801501800e0751100400314111452803040409503484805151458040c4410b401d810005c3d1400280d0300300700da00404c20511045034280503aa01401034441c0e11a100c0d07a141e40400d21904c6284150208040f000c00d020540441d1080f41058080e04540280300d076046c00d0507d054000003e54280b80540b242c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 471360521 1250 471359271 471359281
    0xc03020c0d120c061104150f0908030a030e010f020307051207020109020108070f0318081e0403020d020409141605091503070308220f0918050c0d02060708120402010206 74
    0x6612035100c1503620090302c40441c5092881a40c00908070302c000c0740d0454a556140820a04003c041e100034000c1c080f0050000c8100310703010782a890300140100401150040c1848010800400c96500c12041d140c00030701280d0607002240102002c102e61041140004180001280c0c04000340038000704034003e2100d0760f11461020381c00c0720380520000340411003040001340001d0041002e400550882d05003c04d00c07c0500500c0082c11142c4c1d4000c558282c0302180401c10f00011f107140c0310190050b2951703a4603160440e0009070b400d4441400c02440745441d00409403c10100c4070904400d0400c6404a070010b90072601954a06086405250701905002000446d454083d001800ca883d0014001c1d02c10f580c25900ca0213102d80c041d09110703001440c03200605404003c0040030b840203000087c2c11100f42810502ca003000c1c0c440c5e40e42c50f01c2e5900c48400d0310401003940400c0d501d103200ea04640340e203010035140c404070fa0903010b8400d01412207240841c841e250032300d040072610f10480c401d909403503160b665 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 471361771 1250 471360521 471360529
    0x60d0212100806010302061c15030b010602070e040822031410060303051c060f09050a1b02121303020603090619020a0516110d1202010609060e060621070c03020c 71
    0x1036114000283c1d00810042025041c140000c010041140d410b102058800d5010201594083e540485101030019420424000d00403100b5015040714800390005e1840e26814441c0024060f10103400f400001840c0401403060700e0300007000482c1d90001413031940d41c1e400d0168400d6000042d0440038040c28078040c0c1c0308050b9102c0c17907090381c1d403584800e07080c48a84203040c07125500f8020100b10580c1d542c4000310340126440001c10080400c2600460580340060040c02074403038124170005285060865031003410b4003c80c0f41518901c1401f2156120305500c9951090b4400310350001e9009a000014044138000105042e40324080a1850000c110319608141c412407143c8144440050000d1182d110b00c003c148844109180c0602508070b203003002ca0740018044100c9140c2100ea0480d40d210380f408168082c0111001440308002c1001105d00e09201454034400041c145880390400050389151042d02480c1c4803811034103c4001200d5282200020b84441c2d8500f40075030143c407843c089140700f458 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 471363021 1250 471361771 471361801
    0xa230f0a050c090c0403060f06030c120515040309060c0314030103031d011d060d0b030d020604021206011d060102010906090809150f07020103020304021215011404020c1b030a02060d0212 82
    0x601003000900e06840c40c1c40c0d010060014490310414a270315036000002283c0440d030024040c11801c02580400080c03403503e039181c10304000004620800e60800c010100b6004900b0008a0311242032048645045240441c0d50011600260403250400700000c4141580503824426140000109203a401032040c019242200c2403106a841e02006500240c030034103102c00540020b03440c2060100d403081c4101e001a042075000094600142d01800403c41540b402000400343c40106070007a050b1541060380001d401011324800f4030007840200c0200c0d2246c1d200b54080480140c02c558104098111031422800b170b83c1c44101d01c58868541d00d00d0469a918240080318400c0d206207072103916000441c6d00540180d0002041603070700c03200345e01d2484549503091001101c508003e001940556050a400d0320544400808041c0070754814071800d40506000034010040c8242c5101d40000c04061000080c03410305580b200035005039000c6109040100607030050710060684210400785950b420702807074200c003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 471364271 1250 471363021 471363031
    0x7030f0203030621070306110909010605040e072a0f03090603020c0a2901080708071d27030a0201060806061c030c020d02060708070b060907020a230f0a050c09 70
    0x102e461300c00c140c203c00400040c0b00381c201003130f029200c10341e681e07484030070850780c1e01c0304400ca0440d400100c10f20303645002807000c1e01511080c20b005040600303105007200900b000900c0c0d60248001d4644072148641c90f42e408901d40c1c101420040131410f01481d02d50083c0c00508800c40c04903a00ca180400ca480c028001e980048045ca0024500185192100400211501c01c45400550108400f0100000032044140600112802408040e00e0119041d01c5e1801b035901030001040c00d0003103140c1c1080d9003d14160401660b501c151031031a489249203c25051000030541c1e01d210006030300d001d003901034100c00122071243c403c0e12469900c02060140c4414101101c40d5144540035034180043c0c050b541c144107550014280045c40480d41c1d022440d08d034400c0e041a10402c9002c00c48208001755203802c44e610940c15203184190381080031001c0c0d070350041e15200a02641c00c200440d041c01c4203035411001c298018600f15144d039103590902c90f46401c2105829100350044402020b6a42400c4520038060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 471365521 1250 471364271 471364279
    0x3030c0e010c080f0f21060f01050405101202030a0606023a09050303040f180605031e01020c100c0f050c0304170c0a0305030315150d02031306090807030f02030306 72
    0x10350719543d1400300d140d105440909a410080c0900204030b000e0340c0103000b00140c150540f440c01e042420b095811410001d2001d8440c1031000c0d50a006c69a0000036903049071800d407800030b00d5441280382070310704011510050102c1440441003040124850b0420001c0360042e8084d02c13101060b10b1650b069404030198203444e022075500d650b200701041841c0b081b0b507158292a000381e1241c0c50780c2c002411580994881c44101410407400e025030312080b50b81711341d9170f04068402c0000d07525210100c0e840e003a0700b02051a0325912007c6c0c0080f0104203404550030303185a41d055a045003c0203402400910203664408001846485d40f908424002c904072410080010020750805191103482c000c8000c0130040c800c414003407801503150715252aa50300d000f43d4803a03405943c507490301e5101044a800703d5000d0074490f5401840500594451030202c500e011000380003d40d990f5120030307074803500410861303000b0b00700d92130a08138100b40025000034000651181d500e405186619000072030340d0b030000399011644 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 471366771 1250 471365521 471365537
    0x50f040608120705150702010c09060206061e030106030602030a0603050d020303150904031715010807090e0a0902010c051b040f061d071101020c010e07170604110f130903030c0e01 79
    0x1040301c2c4000b600e959813040742240d031403502c065955440c50a0954402d00540c0d1901505413a0a40091300c0f20054007262004109520304180011b0105461840c1c400c5680c50103254070b501502d080d081200039541041d410365890a0070400100200361a20003514640036040740ac2002074808021280901d030100c2d1300c0d092010404003044040b030f0000c0d01c02c900b40010a00046080030002d1070f003e206e11042050000740c0018000050110080100000208040c2000a02c02c0100300041b86800c160441d80c0054a20031510058400a030b10301005445446848030071005100040048400544203980520000d11289951401d40c0c01c14040c240703115240c610450310702c0c00010383d00d50b13000c41c079858200c1c1400b0211950608990010301a417005035100d180c184400001004680024030200c0c450f0b9030001344096140b500d03003e01820081c80b03040f05c2c05240c8481c0c0d6804080000118001341114144d00c11840c0901c018641c0c02011000300e81441c03280107103280145c0c009404014103842e6011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 471368021 1250 471366771 471366793
    0x230d050c0411120105090c1e09040f201e0c010b220c05040b1603030b12070e01120b06060d020d14010e161b020103090b07180e1302040b030307060f06050f040608 71
    0x1c00c824523000c0b8210080c00740003007115581c0300d01032803c4403d10b00c200040d0384400c05a01c00d00781d84580c501828010410002e0060381080c4001441c4800d45040305c058903046001c100c240540b0300c2580e110b42c440505d4054070b00030b03021220380f110000303500c41e020030809040c90801c0d107003801180714070800524180904889071030b204021500350b5100340b900040039084c0740b00240c0c482d11501403014640d03220355414440c00b280c0c5030a103805030007030b0104424900c916568042c00104000c3c03a8501540b00407854040b00c0906030142d601481820074240700002c0c2031021620005030902c9881800c010f820301240300381044400e010300c1c1c080d044c2d80d050003001510108401c00020904100d0405039118008408140b906c2c1007280240110f585c1c0000c2200000000480c0c580c140e00049001210081402055030a858410001a6060790003084980d10140024190b01407076101070480340c1000d02079a13031034545034410001d0b580c088480d001444004010701080b100e680c0156569035200d0700c0624 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 471369271 1250 471368021 471368047
    0x106180e0a03030c020312010305010501080d05090a05010e0a0b03040b0610030905073005011a19060c0303230a1112010519030206040303020f07230d050c0411120105090c 75
    0x43c48200c0c0500440e41744c4407c984410703801c503109074006d440340d954800c014869490305104901030b030486403401e2402c2403100b00015405140d64070510b814040c91000c980e407a03890303410505004006010000e5128038041c00e0288132131104441051040c103a6241d254496402882036041d540c0e0410000c0c0540e03801c0c811240e0740300905c0d808c1e0b101c0740e00d996420b584034114003942c0c8103e414800ea002048004c10050403a00080490702081d1103a54400d1343c400c1000d0340319001c0c00440710145041c5940c00c2c000d00b03044c4c0060944550945528207010548000803128101a41c010310a020040004110003000f0500031700515220f0314000803402c2c010840307071401da41050b6000c1220340000f441560340f680080c0407035010341c0c02100541c00051203030b414044280882e000400400d40150b03c140c50424081100c15032030010030b446241032445007c1800300801881c5e8508902520410071411007031442269a04840085081c40c200c5900119050074581c0c00744d4040d03606a0341250410300800615 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 471370521 1250 471369271 471369281
    0x7030e010e0d0201020408010c08061c1a090a0b011514030901020c15041505010b1606060f180e07050d1518030504181e0b0a0b040303020106180e0a0303 67
    0x40215034940052010000e0300b80700722900070505400050380da03071074448800c3c01d441c1702d01503c0081c04142002c03c00661107149000701109036688190149051a18085401007031100d848191400001c081020210000030118001800341c0d50f008400e07039840c01c01b0050001d107c000e41001582044402c91810100700c003a64024a100c070025082407004425a850981c0599461000705041002c1c00309020168181c2102510440000d001c59070404900152a10440101e0102c1d49a00b021101c10321450f58004c2000c2c0019051040714641d6821402f00910030803150900d40d50300d00303910120000c0740001c8400880b10b01421010700d16010303803031748181046a1a00808503d4403150b0b04c0c0901703014008242c20f0240701e515803546890405071220b84040003801aa003038140360982c40e8040c05082604102d02560204e000300314080d41a0100c0ca00500a9004080d45c01011802004054041d0031000030749039039842000190a01014400648a04400b103101c02d4004e0120300010074400e0f004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 471371771 1250 471370521 471370541
    0x905010f090b070809090a060b04120614010e01140102060f0c0a020a060203160e0603070c020f0a0308040308031e0403050904020a140a031d1212041a040305300703 72
    0x4000d1401d640c41c0c07610601540090001c031080c101c00111014249001c07040950880b04211342003100c07509140b080341c8513204a018601c45003502c0030104080210310303000700011070642400c09509503561401d800610100703018100025542c41c003422510b510005002c0d100300c26461100d045900c410301e01c0642a4000c160990440c06208100404140075000550107000c41e0361400d00f244d940000000c041400d40c407002d6200c0c071010010f1100c083d1f40282d040303403950307011151072400b6500440040c881d0581548020084070f03001c1000028410003402275440754145108111604072200d4601001e0001114000c001c62030a00c0362009074103195018000703a0015041000d0506011021540341e90000e00d24040065164191403a8890f054855179002c116410300903e045442c500c1024201c3c05442000780031840394000180500c082014541c1c0c601102d000c80407000d0409040040203540030103002c02c40d0465403450717852008400f190551210740c40c14807030290390304c60307050448c05000350b00f81c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 471373021 1250 471371771 471371777
    0x9060c03070f05070b031905070909061202040513030203030106080a0917340219031a151804061d120c2b0f0c060501090b090a0b010905010f 62
    0x10409598040400003000864010103076044003040d940782592810a1903080400da103802030080c40074034010f01080800f50303202d59001140320b90743e800c0105c44600581d48088041428508009900c030f0201c402248920b00944007032003698ac5034000c8002400c1e0324035000700103034000c02c01000400c0c03240c00b80c950030542c10600810340700180c1d210303040c81001410701d00c090280c00203003c03180114107924604a5030f4a1a401206840303038400380915040940c00e010b4041c00c400d07103917003004089400c0d1020246502480c4810380040708a80086400b000b01c40024501704d03c0b41040c001890700300300403410070400c07984d42c035116907469890b5400390111075504042400d401e822009400340c207001c80783c50801601c040c5a00c80c4e50548081d840c05210502c401c0c2d21341d80b000d041106a80c0d941c40d00b4a0100090304006406101c2180100d074041c2e08846c0180c095462300001240c42c0706187c20a03101090300300c2d4480d00d59282e00c1c10080c1200c0c1c2544205012400c00032080040d0b500480740c2c540a00740d242 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 471374271 1250 471373021 471373027
    0xd0c150905031c0b0d05120a02030d0c0509150903120c0a211d0d1202070e040303060501080601020c0a1514071b080a030f0e04020d0e0d0311090a09020906 68
    0x107918980780d90040c441c0840d2854501075607112040c001d01c100d40c99800c04130f440009505807629101c2d110040c0140d000c00002d40042c41d00b24003802002168121047d0030f60030402203400c4c040041803900314665141c80b80d5845017240c001c151103981610102c100040207070541d0034051a5000e00c0e83c1c0003c609202c01d0240341001008034103290b1441d50080c10041c01da04242181c5200123221140303800c0c3c0c07210fa50180c84040f020f85e4403519003401c8095400003d000064000c0b4105034a058800d0b8800d00346c4500c148200020594903070082c504581c42a00d501d0352075142e000042e40c40740451070000b03820480d0300c14200b00d1b909403401500c0c00400c10f0b0800043ca40340303c5a01c0400b81e488600c042e2268051115820700c4104060b00110082544002500740303840b003513500808440c0c42c2c03100d010800244003043c0503103654030b0381201c0c2c101c60000000c000601c40c1c80c0c052503d89502e54400c2000c80e1078003849000408a6504444100780002c085c1c101c000e0810403001c0084d00400c2d86c250300486d042c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 471375521 1250 471374271 471374273
    0x13060f020a0e1201090305160309121103060f01060e0d02010e0301180215030606191b0f03021b0303070204050405010902060c07140607030c030e0315010609170d0c1509 74
    0xd200404075400c4907034640c82c0b680804400c1c81000d052281200a903a898a00c0d9000801d6004090310341d0048a0481a10011101c0c02c0885114800e82c00c410310409004c4290000c024000c4c10340381d0340c1d11043d41aa0300710b46d03a0047d0b6144002091041c08003291154034004454500408000132151050402e001002e040310040b0342115024038132002ca6410004c04a029441d050a1140400c0342c00980180303589803400101c0c0c070900454901c8000c0104021150242d24010140080941c40007150500c210145040641217050858401e50160081d0301e9a0310440c0680d80310340d100010042c2c010751070002107500744002414020400c0e40c3e15582c4001c05001651503200410102003540b0041c582c1d075003456030590070409540556445031604008520010380c2182c00c0c101401d0b0942042404103410401080c00e0281c03a1000c0d102070240b00001040440d00140140d040d074541c410310442083e03140c00d901d580d54010342509030120740600e444d200001c038047c4c182e820311500c40d28041000301c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 471376771 1250 471375521 471375551
    0x303281e020a0e0604060e06070606050301110306010f0f0f050a12050405071a040509010905090309040c0207090b0f0303120702120408150a0b100831020a0e010b031306 74
    0xc0c0da1180c042900000e140032041e6000c610364014400840d10585080e1810002800c00144131440c24050349000c80d4074004d1003620340c002c00007840b000e1700038801c20309800101c000301e9004a8400340812071b03400000342418850003400d0580c0d81c0c0c40e02d5591b04100603800c2990207411160401003003040480c2d01c1440c0600e10300855000c0c602c64001080c140341441d594a194042e02620419003400511003004266140c4045c2030455400c002c2c0060542c90342c010103421803080c0e0802c40d8206040c0000d1003400d0b6800145d0008a0f640a08108003410f44031007001001d000889000e40c2c560b02c140000c24524a582105070b030003c6180c01243c3c40e1500c200c8050006400a512141c21500448000c2480301c1000450561048d40e00c20304101d05544440061805071035004100d00f00007404c2e0029542e044101c100741c0d540c400302034100034094102d91315641c001407a910101c0c003411001000050514110a4a0f4180c5010071842c90840d525a07001d9090002c81c10750913145503860700b940340200c0035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 471378021 1250 471376771 471376811
    0x12023007080607020d050c0a1b030602120f010b0408460506061002030a031a0a23090403120903020c150c0d0e030a081b190311030328 59
    0xd9041c0c0a00311a00d0301000180c14041001e41401c2071000c00c0280200000d4003081d400c2856030f00c40c8840f8002101141c030702c181801d00b030300021f00103440003410400d040b0000345124401c00e8440c0040140744c6c0c8a0f5070b000d02c24000c52184200c240d100f004907501c040c04e1105088007004c0700000c80e602624144105510a00904144200168195500c0c500f8018280721240d800384068440365003410000b030000b5680c0c030905115508255075100c28244800b602180540301403401061034800da034840c0032500348480d00c03031443c140d2200a5019030f01c96081c0500481d01c282e4064079a00c59240500c00c0580140061107011801c5014a1804106c10348c3e55000d1440207900940034540c9034802e000d80f542c642407512007002e05215840019240503500000c1c0c0c0c25103030b5800343c0b000e034072413070a407901040601c065980714580e8081d003001d0b844c140c404400210030040c007a83c0c0e5400f0300b40c0c181800d181c0724482510103180d5a000e03000130240c2c0102008600c0101c10b04410700080070004603901c000c000d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 471379271 1250 471378021 471378029
    0xa15080618041b05010903031b030e090903040815011a0307020709050a090501050717011505040510020a051501030c0e0c070209072106230d05030c0a0c12023007 71
    0x30200600010301110207050f40c0584000c1c01d01c1c000b15800c40c2c501034881c04900000c40c003000c0000d810320040610401d04040810070241c404601810000d4015499030050700810400d84542400c89955010f070828007812a024031071820300c03001107007640e1002544020504015440351140c00a03031202c49110740b0780f140e6401c8000040641e503a2601e913007500c40103840308080101880c0c0e403000d003840200d2054115607050500b207100303580e03810055070700c0c4c000c07640055405110001c40350b1780c46401068043e103071031080302612296644c44c80710602c408028080940110120340c1c1c01e1055883c00091240c009002070704460401e4540d41c00030300c01e070318103c6400001900021040c010304d05d03429a40d20440308000810311a00342000201402c81c0400030031446050034220390f8081c2d80d1a030101d2032500130b4005080d00d40d200707824154036030340314080b9104484040c0300400000e88013650f10f2a6440d50b542c000c0ca00b0180d0580782200511b01c0e402a03021400720508019804c05002040101e94018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 471380521 1250 471379271 471379283
    0x30f0703151103042f03060f2a0403020105070606050613050a05010c0f02090c12090d0806040e15041b0806010305010e0349020304110a1508061804 65
    0xa81c19076030142070b0341800b84101807510061040c0000900d041d01c1a2682541c80d612652141c0c5500034100015841e1100040c1c050181c0802e020400d00380b00900c40c0714000808c900b499021a410b00100d081c200543d08a02040092205000662040c13006042c414002c1d4000b00d10141c030b07000001c54551200c0c98803141e41520031010061401c1095515006000c24209580d22103d43c2e1170300311001e40c99840003841070358020b00046100003a107040c0c4040744042001a443c600c2c120711901d40d0341401003e0640451001400942540b50030301604543d6000c80003c1c5c452000d10340201428010040d00c11141d40050000c0c2c2e080c80350220899100600c08440140069407442c10158211001c04616082d00e070410031246031003c5103442a4034505e0505000c0e044074000c180700c0b28000ea40781500341544007900e40100040b40700c10350003a41c011805000514500e24034070007004209071031881502d02e50050034030004e2190b4042d41c102c80e4040c40207003094500c1401246040e0791090111030440d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 471381771 1250 471380521 471380543
    0x50f09042a1404060602011a04091415010e0f0c04030321021305011d0619110303040609030f03140a091a0901050f15030a0809030c03010603080a12110406030209030f0703 75
    0x40d43c41d1600600b0001c00742c0d40020014051201c1a583c0124121801c0d24051620340a180301040074082c0d0310040900000c094507100146003054003030105c02807040d104480b012402160000d020081254010140c400c20b1501d85840d603a01510200d441440242d010711060300d01c183c080c0e15a000900c1c1c2c0c2c1d000729146804680c180000545140070f49180c1586802c45a1400e11043d11000304541358101d00715420b1030422101d003000c4980d0302c00c820440c25180400720900003084413582042420034400c1d2030b4803400f00301c0c100c0110122500c00122600140e07640e0003007809079540d540002855805403901c1d1301600c0c10b6807256400700005446523a0b07260340d5081040400f403510717074800d40c2104004a00b0890181d0350350005c0d07582e041e904000f070500f881c00508040d69a40400060b41d072500b01800034808a039407420000e6094110040040100b001d050510ba90010346101d40d018810800c110681071505165044000f500811031268041c49070300806600312508024007401940700e5141400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 471383021 1250 471381771 471381809
    0xf2a25050d09260c060c1204121e020102060609130203071502010c0f0f0e0f130902040e01060e040b04020409140a02190308030a050a0231050f09042a 66
    0x200140c40340c0d501d400300405880c1c44414192010510341c43e03a032012a1710307a0304c1e20400c203101d0341130044140907103110718030004001488101c11064208424010116054084505111500c1c07c6181c540b009005801c00400107a0515203100c10f5a040700445085014040d0745601107850600250091246541d8041c0c0c0329607904e07824015400da82e14503140c03800103948a03100141511410082600901c228000c81d82ea00d900c9500940c542c42d0302c0145100440b90015846400410b00c030701d41640500d0034000581c882c08014059003084030200e00c00c03805181d0352a03d8074691058098000c0340d201da1941090000f1441c03000b03041c104040d110002c1c010b070002502c104010031400710500601c3e20f6907000c0400c042614841580d0307000c1c035112008502542e40741c1050009108021405512828404640d86180c8800d1004c80104040002042c0060340320002c02181030484296998040741e281c1c000b07400580500b0001a04003d15a003103072440d84041403103001c00e13000d0380040322206000c0091f04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 471384271 1250 471383021 471383039
    0x1c0302030f070f020f0604080703110310110702010e06041511160f0e0a0903090909030212040b04090b0303120601110a051e160b0f0c030906030f2a25050d09 69
    0x16150407001c90ba11b03880c00341703848900d82d103a0021f44000f0f85005100055000030f500c0078070513084881150b040130001c1d0920840d00c1d00d690380100308280d001401d045190001070401c0402c407020384401444131130800e605c40e60708542c200605d140921181c010b000d07403030302810303035100083d8013420032040500341140c108148901d0b00c04001301000c0891703080400240c0460341085410068900d1200042810310702d82c10282d280051109141c1241100040c001400710208009041901c103481001c2c00100342980402d039480c0100d80b080000e000d10a00030589960188100125012600341500c950701c3c6603484082c101070144c491720600b00b0100a03900041c840c113000f50078540d0241004a50140d052007a4002c46000311000701440c072100040c0301c038008038108140d5003480401081603071b50745007003150a003d6150503a006c6043c0030b075030002c505c01c24500424013038480d001c0070405402d02e80c17400d0360340c081d40300b0511000740e0150a601d014000300780c050102242a501c140c46000078189052255 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 471385521 1250 471384271 471384289
    0x10501080a050f0406050903070b0103050102030a0f020403171c1103150936060907090c2a110d12120e10050405011d010b1c021c0302030f070f02 64
    0x104902d84800c100c0203c018154454025412141c00613080d55044a0300c0d10710320a4510162485801e080000200301c0d05400651017a00c59840c00d111b041c00700031408050707010300e010003001c400340c0c25840c01034030380c41d100504207101c180ca0b08c0c0c14090140029000c1100d4081e44000d0182c40000101b00c00d98145d403001d003a07035080590301542c0ea0700d081c4042403000e001c8128240020103005018032880d49074841e15180c00707101c1301c041c0c80250508407020340d80c0d4145440307000b0441c1d041c6a0b50844c1d841c061a0444110345800702c01c0c8208040341074203400100007803d4112203494040d036003075400391180315842003154480c0c08103c2c0d000c120150003400841108030702101882c2001640d0f030200102142440140c0401200800d054440d8681503003d060b07080c200d142d45246c0c0d05080c03016412b054002c4800003074280c3d841c0c41c2c009203411060903c0d400c81c03070001c1d40084600c204590030080d041000c100c0c2c2406407054a050015184904e500c2d40c0c040801580c205a01c0c0d44007200307602c2c0480340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 471386771 1250 471385521 471385531
    0xe030a0c15060308040320010c1a1b04170609060f010e040213020307020102131703041e0306050702150a020406050417010f1e0e0120030403032004060f182d03080301050108 76
    0x290a01d00c075a5404250318ac40540c0d00034401d4405020802021100b1558080004070300384203911345441da8101c0b51503c0045200c80f0040c0b15140100320035010100301c15016001003032125803140c0c00e0212603245030340060012600440c42c0400114000400c0c8042e50144c069030f400540e1f16144522502d00b041e07038941003254076001480014019900010032901240c17a80014848076003a5500e40300c11100e901d0b40040d003c0c0b820842009001c0d68042034000514061070100c07642500c900c0241800c9000f18080c500c0402e04c208001d2000007402c28070240b00406280000c0b4441e0a814400b10a07510240748150481804200c40080652107001d9035210b03149120007003142484051032003901e043c2a10b000c1a000c0d000101040c1498440d070020035080e01c860301080038404e5407103640c0909034060b10488000612050302d0401c01e51085041040c030681c911814001141008169040d10049030001587c1c605148113003860380d0124075003140150b0141c4081c64881d85080c1c0003400c01398000344 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 471388021 1250 471386771 471386777
    0x606020c01031419090c0e061008043f0822050604030c080c01060e061e010e010807120911010206070804210509030a0b0a0e030a0c1506030804032001 66
    0x150040104020f1650641c0055551000705100c424034005030014200750750090a07100c0c1062002c0707000c9254000242c000d040c1a0b808034407204c1601130454058409680051107080340040c0300b8216040540c01d001220844075529201c004d05070341e640803082e10a6003100200d004001000131400c08152240a0702070310080001910809a5485488a03001070006003804041805101401440c2c41510040e640c404000c2011a440325110068240300b01d41e180d21510b50090340c07a00c0c40e5007280040c2e1280d00107031140307002441a480150b81344c000092410041040c1c0203400c1c4909030350b074083c0c28041c80c05114004594003403440020304040008250105000081d8240130000d4010b00040d041752000c460720001c00106528100c03528810000c1d070716414842d9032500001d001e8050380d15401402041010070864a0b00341031a5240c0c0614503501001c00c0800e580c2d0401301e40071240d242101d481006001070410344a81c1c1d07401c201c1d00a03070015554040c0400301c100301040c802c20329000900d000d007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 471389271 1250 471388021 471388031
    0xd0216060509060d111c051b0a0c080d061404050703050709090e01021c050a061401120f0b09131e0c06030e1501080a020a0b09010504121103030a030606020c0103 71
    0x20018046204070340e40709018420004d081c4070024003541c803c0076403101885c400c0d9903d10030840c15002602c04010340115040c13415001c11141c1e0b05042c0a24105e01042141c1810095490000e4903034414030f0100343c8844500f0400d0000c0104980b01e080b01a021404a101402d1904801c0c0030403124010308503028540f80906000460390401c100030101c5c1c840c0440071079020b4054440c40e001e4040c20310b89a9482ca002c44948900240c541c02c2603102d111079810802c121f60389c0782c0e51014000603001d62140402c1140f584444005401e4112103507440400002195580313140010440c0b0714821100b460b4a5010000700c08100f01612190010300d00c4c18140756007550126444002c984081481101705241d646d03141c1034422402401a070340780d03144465181c0440e40c1d4801602d61101d9191008a2040c0391502000c500071080205854407144180d607541d08260412440c8100810f0721541603642011758500d05010360b604000500d04138038941d80c04100580b03001d03c068501070f043d442c01414076081c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 471390521 1250 471389271 471389279
    0x20a021b0a0b210f04030f1d010513030503070302060405060112050304120302191b0504020412020607020a090e0106091d060c1309090b0702161d06010509030f0d0216 73
    0x100c00c0e01020703900000742443e03484803d05041c03481c0890aa0701129402e03800310411652007601d81c00e56120354001d89a02051742030201c0100c69031001d10b1816964564050940b0050b0f5101c2c01c05021840c403461428404103442e1346646180da0000c00e0100c006920805c104401c002050044600415a075440d0114002032561010f49900503400f6040650700050f04d4a024584200107003443e10344101c011250014041c200311242c064001c990701c11042c4814000981da0a052007141c0894245940b070100e04100c95080200b164021307402030f07910104c05040895000c0d206c0c400c441c02c90f101d440002a11500e40780c402c0c0c080d1070b59541c1c0342c3c1440d80f0f0711034241c41220f80401e07040e501c14001c14200395940d2102c04904c80c148800c1e0000c00020303242a00901c01c215034004100c0c019400c2d0303003c031401c9107104c001603400286103001e071621103800744003482030314000200d80d560070640c1410414241050140400d1400e1101403031040703a030f4891130b0300c1d00b45150144160f4201500843c0c1e0340e1030035424 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 471391771 1250 471390521 471390529
    0x9010b0a0503030406170703062c18060109090f12030209030d1b02010c03091703031e1e0912070f1103011b0e06071421040e01090c0908010f020a021b 66
    0x3d80c040021b414401d100028090a02c203038420710103801007900c80188004692140300b07901280501080c51118407101103401c00680407124440381040318020071140e0300301100c00019041c4940100d0705401c40b8842440095032001e10707642961180c0d5030040e01c130340a5130101498000d5080e1240280208611083c550010900748c0b1b0100711f0302030038010141d041510341104c0c103850316408800300040c00141c040340d084000c0003c41c0100f100c002801c50000c801c3c1940d032904101074a880b105500d1514a1042500001c2c0b51194003002c100147d0300d80f03c4800f5210f000b176030f011500458411217034001c0c800070410199107031a21840305134000c0001505040c41d40803a00c81c89941d00082c000428407217122030740c90b201140c40c100d510050385100d40e00d140100d207980f0200d04040f5403000f5a000305c54051240c00300c09403402c4600c0031391042c50716440d2440e0140240300310308a02042088041d404511014240981540d0b09a0a80e00607551820304e20000c0c140b6150503003100101c5e030040210b05241d61707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 471393021 1250 471391771 471391787
    0x71b020a050402130911090a080708030406081f0b040e280902060c1212130b07030e030910050c0c09010506040303111e0a151509110702040509010b0a0503030406 71
    0x100a50780169136131100c01c0e60b45004a00b035031020f8450b608001c1602a4010518054804214291800c1d2140e9440d014a00e84a40c1d03030f80540005036105100801c03903144214846600007035250300034000030b070700b03154070b8580c0f95115000b281c510030002070100401c2c0d0014400c0f59004802c2d0281540d104000c0f52100180501061041d0340c0075100c000c14070546d680ca100311607a0042a408803110b01d4100074a401d03051300026220701d00c40080400241103003000300c4a004006030701804140456980d0342c01540244481401c07012184000e0041403195160b200ea1008407a11507150551116903403580f06103400c020307170103050042070500d004000c0ca032110b078290380549034141008440c0383d03002c0b6041440c240121010300f02d803030082040c29130b078182c02080ea06038860045240914005101d1541d006943c181c289041000701d80c0c0301c08000c00049a03001d280e0786911041d03154540505500005c0680724152150410b40c1d544490203d480d1a04044000041030140c0240d8101481c2000107406a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 471394271 1250 471393021 471393029
    0x3190507080a1a0d0f0b0c070503031f031a04060b01030c02030711011b060c0206130b180c0301020d021210030b010312260906103c0608071b020a 64
    0x2500d45262004083c8000604454800d010f405034084100c00e0500c03441e204100d031010780e6040b52480200324030140038021120042d81140c011071464456414600504000e105151880150030b1004000901118002c0b00d15840700c1040000300c2c1810300341601222048078096050629120703008954540104c2650740d0140c011a07242c90f200e00c4200140c500c4030000310080c4101034640c410508002250344858108121903003107a10035aa000142c00b10010b8510029003c01d8480e000904d44038001002420803503410300a494046d411000440e0030b9800040e91100c1e0181c012418005200c0340b2510b8030703440b011540c420000140f5581b40e1142e00101808040e0840d14101ca042c00080d0048601210200039011035450b00c8001641030649820160fa0036103107400381c2c2e0045401c119021500105a44d010810710903460003800c4d11400c545070740d1390091000d04101045001500d451740150000700803588400403145001d00c0f008103040959000910310038040ca0388080540c54400c04038080e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 471395521 1250 471394271 471394291
    0x1d01110705061803030c0307050705010813060b0109180605040e0d082a040e0405010c090b0406120e012f070c0501030906020c0609030a0e0d0f060203071b080319050708 74
    0x50318005030900301c941960628184c1610002905082c045d400000804240e40210107503100c4130303119030046500380c1c800e403172080c0c40343c090805000100d6810342c03220101180504180d80f021f5034541050381d44001c0301024080441e40c0794420000c908050240b1904008400054000c100f03030b008010300140e001401141c0c2d40e16410740c1480586010014490346108808012501e842c0c1d01c112201c95044100c2d4200c03415400c0c00450352016024228100980f4000c042c0b80e070401b4103000040318100090f0900c00501621141c800d100e1101c203209050b111030312513884483e1815880140070540e15001040083e21303d00300f01c81d50102d501610110b01780d45091038003185000050802c01e0190190780803280340360140ca07060104001d40000100281c1c4980e841c0d2540c1d804212003084041d05100401510903666030748180e00042e243c3c0d00035640248207042c199002e250040c80303058006440300b0308680a51002007407100c0440003205040304408409030901203481c02d03160042c106080a4218800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 471396771 1250 471395521 471395527
    0x60f09020306031c02070819060b03030a1d0609040914010b030325030e060c07170d080406020f040f0f03020f0904021e060d0c0206160206060d1707121d0111070506 72
    0x20f10703101740041c20040c011f90040f685101c049110200807881d83c050300300c1e81285806480c10003800d011050702da4488480e00d0fa48101c488517035401180341d40e410b80f05030f4040e40c2081031080540d214451100d12500030001c5400302900901c1c2e031070843c1c0f140400765210742d0003800940d51140400c2c1003400c40030308412244041c00c6981c074054550203c002c001980c041808210301191400000380f00c001c4443e0005808000b402c1c4149058858240d803031004001015400020041400ca0700241410250b514841d840c1680e83d643c0104044625004029030704000f540030400d51503d030b5031840703507130400711845440d504156000078003000d901c981c002a0000c0002e5103099036a5004142c920801c0d003c0c4050150f030400c1c03400292900d008948005200c14522440170001340700084851041c030020701a0808031040c0d441d6211a111803000d03001c2e48400c100304540002d000c1c0340550700503004a03207409140e80c400340600841c05d80006181410441041040100240c000559404546095802c543d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 471398021 1250 471396771 471396823
    0x15030f040618140a05011b1413080a120e220b0d060501171608151003120c02130b030309010e04021306020a23060622050a060f0902030603 61
    0x14070020b03101c0024180c008640c0b0301040652000c03c2030080988200002c2001648018a5855003040d409207140095205044440e803d0140c50080038031444480300d07c0005136883c00010301c0c01d41142d104a5199181d5100d9501d40d5400410002484e2070440f06040303111342c2040c01d0717030100c0102c0c0c60103020980c40d40300480140d12080322040b03c00c0d800c498140000e6840e01c074500481c400d032a2080303115101c0d4880480c0204c1071003280106403048080a03001e4028418880e00d01000050962425201c1d402c0000000411110680c03650b4112a240e81c42d45403a2401040111800500c0201082c2d0410004220540d0040100e0b4000d0b0303001d003015101801c0000106009001e180d010203407490a0308000f00d607003a00000c04c03071081d5100745201140307001784105064205600807680c2c18240d021b4004a40c0d540b420317181c0e21b4a100c81010f000404240540c0650050f148150b40800000e50740302001d002481d401001d2102824440d0810362642c14604042a40c825820603501120005c0103c446 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 471399271 1250 471398021 471398051
    0x1021009030318060204080c03010203160f0219061a06090d1217010e1602030a140901121823030904020f0408030d0b03010b0f0906042a020106030215030f0406 70
    0x4500300212040305030703202031460701e80006d502c036000c3c110710341c42107031100c035054076050007124481e4820315412888540d001d4415030b0384000b0381380600298001d201d450a150983c038a00e03580251b000c1e65006c07640e13a9071601c0d04600303440490401d0f4001c0303800f004030051680b80c880c0e841d26059441001c10011b600c1c204400c48541c51400e011740786900080b00001041c0c1d500f0003032240903400301480a00180d0940c8402c0c2c1c0c2ea481505c401c10041200351070007240711400b40d400b0b0b00707004006050001104c0305862002c011500300015281c50507000724101c0d02440f401204004a840d2540303200101900580d2515a890194200c01c1c3d1195800003120842d40c0d00309816034000f04900021207480c0d28002c0020030250a082003680d00279803a00c100032804c1e02d0114012030203175802900e4800c180e01c0d9041800050a42c40c10006441d68070a4a0040c5490180c0a18120001180c0c00065000d04510400811801071500340c651041c040c1305010101003294a026041a4440c200068518101e8101c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 471400521 1250 471399271 471399281
    0x1216052106010e0301140f0112020a0e04060f0606021b03070602100b04020c03040602030a1124070e030f2103160c0507050d06020301050f0414060d060603020909070602060a0b010210090303 83
    0x1c2d015420110010801c103500c0c03084d40d020387d0300c450380c002c8140c0e00c8449003e01d5a40e1400065840b8403409020000e20180e1503880e9005800381d0f00101c2c020031075007174000556075550300c0a0f0059201c003005500c0101d0404c640c05001c0412400707801f40c0c2e8074005000b0344d07409039030400d0f0790308039521000c1c5196540d480d07046038050841740064a03100c40da9218041d44a812403581e220102d88128544010a0800300f6031030281c51002500b20300c0a803036000918101480144410144000c501e5510039550341001115500d405520003407110000310b01050843d00b82c0420f442d04280014420710a010845920440e40d0484620b440802050142012807074194590300c444e402c48540ca29400c10f000d210b0300254107881c02502d24640103540740303052000304c85031802040110b0400da40400c500386815024900388500400700415060745940000e003002005603510f0b40e40c0e9010800410859805000d03540d4042207604081240074280340c0041d484404510200700507503034a04800b420103009900c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 471401771 1250 471400521 471400547
    0x152401021614031603061d030405010f0507110a181409060106080c070c0b0a1403070f050d020d0f0f06120c050103020310080a06090309080d050409020f07020303121605210601 77
    0x2e404040c641d6402d080f40200303809003001001f840f0904200000740c0c0004101c50841d10f0680d03503c00316030104041183c040c0c01160342200c40b00c0e0840d01342c8260341d036000e10b4036001c0c0a1494900152450303c1c172030881200d910700341450380090300b03034100400c1c0c50000c20064115001030a0185042c3c3c0d944869003014411104028020030800c0da02203184808100035103407441040d11101c81c081c0200c1c2c005d07081c0c1d000032200c0030700003090071440c1d5151354852400f401041103412005424400f00d40024002e40e54019410009a5942d001610f040d05607401800c004184502c00010b0410141d210310341781e034006000c0c244c1070540000200d07040d1400394401c0c00090039403106842e00e060309840d180028240d14a030503800154a540003003020440800c81009522664690500d05441c01c29410003940112401129204043c8001c5016840601c01000040f4400320102003604e450712100c080c601240c0c84c900c00b003040901c2452000031035140e25017003440341102c0400e4140c0e981c00049030070030141c044c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 471402877 1106 471401771 471401803
    0x50c010804051c260a0506090408040b090a051c03091502031e250507060206070f030b030a02060d0c080609060d1415240102161403 58
    0x48080c403103419013000b01410201c04820b824141c2400d08500883c0003402c00c0001c09002c6104880d07100798100c070300000a0a050301c0d04c44c4a402a4080d642d952a80001c10703100076038a0340b0401c00100401441524850780c2040800313840c1c0d425000484c00700b02041e5011440c0d5501c101030442401300c0c0c0c0d00031814000d00a500ca0201070710001070000003103040000344128074405107400b400007800005103120344418640a894104254404001c40d000320050200391a03211041001940c200d1602044d500c0422002034100998040002d502400026803d00350020a4200c50900d00450320360311015612181400201c20088640341d9019901f010f0b1600002c8811b508034890a0b000c008490b00340c0c0c24241035580d105401e85a030109a10700c00102d06030f480c0e070903d144c10326078001c2c4098620000f00140141e548403260040380c4040e0030102610007503071810080d42c445030024207 = true := by decide +kernel

theorem cover : BRFrame.Cov 471223021 471402877 := by
  have h0 := BRFrame.cov_init 471223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 471223021 ≤ n) (h2 : n < 471402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
