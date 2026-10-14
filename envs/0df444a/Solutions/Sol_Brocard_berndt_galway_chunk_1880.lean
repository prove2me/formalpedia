-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1880
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:00:45.558152+00:00
-- url     : https://prove2.me/submissions/ccfd0e6c-c60a-46f1-8b32-2d6392202dc2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 337949640 ≤ n < 338129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 337950890 1250 337949640 337949653
    0x6070507151e05100312110106030507090920010909020c1f020d0b0d0203060a2007030924091e03021804050d39230706030e0c0603090a0b0f01050102 66
    0x40750450650301c1940d4100418a40410301d081b02210182c46540d82c00c0199584d9070f1012001402c244401130007440043c4011440301709038202100001040c1012002c120f54080c1c0d107803090b98100c0320b01c90072213201240044c1c8032044001d0950629003402c14410503244644800d002500055001d895600414403041028030358407002c0c003102d10201d0002a503d0780c400400540d200c1095000180c1701401d10048042210389440c10684541044504501040320b2400c1402540012007010040c42081201520010900203024206140c0c030700800070030060300c00d0001100c03100b140d961402107901410f115520001e205d80d0440e000001d0720202c40c44c0c00350204450803503224041e1008000719002e6812407094041e40030128450304480d807015030200502181010a413068401612680007101c10300c404c141043d201414071020b90021428540f81941e43c1609100000d4a105600425202c896907500e500e6107007403404001c44402030601180030200718040d0b080c00726941c100d030020307001c496030f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 337952140 1250 337950890 337950901
    0x9030504030206340c050409030e030a0c15050f07061104080a060b04140106140903010b1f030509010203070e01210624031802040902010903200108060303040806070507151e05 77
    0x3107801d200e400034010245401003800a89025400b08d200ca502c2401d05100e2900030303c01080c01d01041d21000d55030030440c0e80c802c01c01d80040f00345016800d4014600186000203240320100507004d540006040e41e036a85442152202207030049501504000044891011440c5400710252200120f894010780c04c018450321101c074055061410b8840c2900e580e4516051001c42d50015001691015855921540c88259507165150781c207a48680500c9113100c1841401d9011781030702c00150106407180c0c4100208004603a0007100094200000d2038815501d407492101c09003984d40304100042c54030302d05000042c410000c9003002002c4600346011512242550720240c0498008512448201190184200041c034003544803c0c002407050410440c070300d4403030f00e0b4009500b80c41e42e0010b0b0800c4049019041c3d40d0b8000010700d80c0010110000c5242c10705250a0300e48842c2c1c040c081e0303c1070000c04100d0000300009048260300084841ea01000000d07100d00303c11401184804250412520701404541c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 337953390 1250 337952140 337952227
    0x3060906080102091e01050909091504030804060e0a020603060103020f0409020301080703030815010816051207030e0705030f071710110a1b050715020127030f111009030504030206 79
    0x14400345c140c40d80d40c10000303810f0a012854100070030083d41401602d600a81d42a4800c8115006900988c0c829a44d89000c1ca05442200c50b16001d174600c56008950030001a500c4900b01caa00c05800c0c0790260311010701c5d90000800380941c0e041140c14a0001c0700125202d01c001034041e00301c0e4080d507220080ca8171070b40d0055944a011600b01400288200c0001e005902100030b854030030406894541c0c40c0089090003a040f003802600c2a00000380c035017003980b4032401c0800c6028060714084001e00724011000302040d40c0e8480620640980d00c1486031803100342c6109000c0070b41d88081d107907021b0042da0403402e50305625601c00d031000f101181200c0804c6008509083d119960380d80e0040003080403505009010030503c1a11000804640d00c850114600e0300100703000303a084065101ca00342d00e02099240103804000403075220000c1121041d00b4284690000505a040401228000a0042890a0031502480b66800107904400002844690194554014401c03134002c401a500041c00410b60038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 337954640 1250 337953390 337953439
    0xa0f0f290106141204030e03010f06080a020f011106010b07030807030c050a1112040f0504050109090b01030f02060d050903090310060501050f0319060b070b160813030306090608010209 81
    0x1a11190080380180302d89070041c41d914800046610b4241e05000400c40715126034401260120000b03158018070216500b024058240c0c3c1c11001c00081c003900d418219a6996040728107400382c030032207090181024076409889848a1224000d0581d400740d03031100e4a8804942c40264201c002804000c00211b00c40d11034880d05040c580720342c1c0c48901c0d00750784540846071903500088512086c051100c4640045201c40020401850811070202010f86845e003004119001640600c018a00b13141a40e0000390708443c0441c10340b0740c031100c03800c0100d0303441c008a480380c01070000050100c0d16000921540880c0003018040d0b003a002c60486070b182030410700800c151135152040740e010841c2448000b12103000e1b01d024581c0900c01c86204620302011100d018140c58056200d03501d115000280302084c4040f04ca40d0940c8140980c2c556003102c62401801004510014500040030101100b0304080610035000700c4014802008248035143d250380d5414001c1d07200408031485138016884140a009015051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 337955890 1250 337954640 337954703
    0x3030c19020c0907030e07150e01030f05061c03020f0d2a0201051c02090307090203100609050a06030507020f0a0c050a0f0f050103050601020a060c020313080303040b010b09030a0f0f 80
    0x100c81503440780c20f0306174040d0000d100c502c0c019009042d00403840c03201c01c41100f041c00d039039540d45603000100103001408540d6454040320241c7e0401d000c0041c4c1c1d489543c1441e0303903000c0d0300c04030311211740c0c89040807420114903a074400150300401780941c00140e800444030300310349680700204400c01080c00c0c01c0c0484180c07512009001c103009110718803070081080103840449012a00c058a840140c10001e800c0580b0f40d0026442e555000c070070302890000c01c1a1030360290886043c0b8401840c24400003402100c1d540c4503038410151a44005080a803081c0408805003071500101c442012840c5400c205901190041034001c0d840520b00044912180382d91800f1100000c410034000c83c00e000c0110b01810004000700c4c1984103a140c0400060391a1150502e80401c55029645541c480345142c4010003060f4844609540207000b840302280c04421042c0c11109601c01181d5a50741d1580403a00f01303000101d001d4080360340400003d092183d00c1505070031042c80342040544091030b42c4844144141117698 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 337957140 1250 337955890 337955899
    0x30607020c060d06030b010306020c07060503100b03070302041d15011b020409021c050304140d020906040c110102041d0604021611010917010c030c030204050d032003030c19020c 78
    0x580c00d03090002c02026080e03682500826400e440c0e0316044c001d00020303401110201d41c0000c81034064081448018023401803442c00500d941041302054070454043c2c082c250034010000003150169000343d0407200104800442c2c040e40b9603141102c0101510100c50451012910161510040d032080c6141181c1442d030071402c1e04181080d8081c00018551200c1c00c03a0440e1161449100750b1440d130f0101030f80b45118500455586003405c4d14120030320725040d10540110070500d011401a9241c0244a80c082015580042d0990000004903001c40f8035024110300741d440080d01040d43c1c0c0d407458048040304030544820b40541c071900144002c1784188000350607060f0b44102c120001030440607140e010060145080401203403035060240c1900310401401415a56071032010440b280c25000e5075038072201c541002c60520b0b00d40740129403846d06082e002003c110340d85c0c1820203031002100c0400c01981328501281e03100e25012005002c01d034010708012003100000c96500900510010301110104400781 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 337958390 1250 337957140 337957153
    0x50a0903060902210703030f050405010c0b2509061409060304150e01021314040c020c1003060b04030515160c0b1801050403020c1002010e031b120409140603060702 72
    0x71a110010460040c2c1243c0c80130091022001c0142d40400e000c4407499441e01402a5610398900176020182600f10803040c004144400c00c00341c0e03041240749007840d8011038109810360380d41072001035401e2460b41d080ca05160000042c041d031a800f00300351042e40d40644800300c0d0340310042040e1045000d20300c22140d101d6406c0000400044060003c8000c80f8880c02003c110181e0184c000c50a9802c10454880300c0da511100c00c2082071071200c101c0701c503a0410b03071f03007000381540c0b40340001c1d1031304200c142e01ca006981c0a14001301c154880c0e40144010011a06425110b903140d242071512808071b5072101c60031740c41a0303020541500d00c0300e440e181d802030395441d921031241307146d40d5031481c0380c0d001050a0f0b4084881541c0040d80382c02801191f00c21482039029129000c800b008110001c0300e01000d18045a25008410351000d6000040301e4907070050030181c418070a0000391051602d01060004020341ca000329002410f94916002015040f09552040b052360703486006141e136529003140c0c0030740140d00c0038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 337959640 1250 337958390 337958393
    0x18181e0a110114040b0a091512050c04080307140f0f0703020906010c15060602100c170c191e1d090a0e19020a0e0c04090f2a0906050a0903 61
    0x4126150150107052500c007034441c4070110f1000f900036500c03c04054000054401e0701030f40c440002c00c058951606c803945426031100c002018400c15100c0e1807402a690404141400d00e1041500e0040600308104c950326281c0e4036081074220702505910486100c0d00c455940c4004c00411044202c205400023071010b0342c695000c001007484007825050600035845003003808140441c00422211a07910b82c08909949400f5009150140e03425400c0910341c505915002101c3c0c0c00440d40e14000c81d40300130403245440e050000800785c41458030b2002010341ca140b903134000c0c581010784080440c40d01d5000210f401c1c40c6210540e002880c0c0420040050240b1408080519103900d0030381c0c010024503c000b4000000c007640c107180c038038080889001c030b820010a050451900f54243c40140200910000b210b050800012506005a008038001182c5500b0380199040081c1e1011401301c0c1000c032041105030091b001d480061500290000010b150101c0c01304086002e20100d86e003507005950b0350800035265 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 337960890 1250 337959640 337959653
    0x307080307050a1209200603100506030a140906041106030c12090703050105090a0209061507140a0f0c05090f10060f0306050307240201050609070e18181e0a 69
    0x20060f4005104071041c140003840454443c2400003880b80ca581030001c008a07140411280400a5984c41940c1c20410410101e114a06610845100f51140c40d140e48540e02d9440241620040080034440440200861a000080c450340034900951107400f5003000319080c4100342c80100c400c0000880104004d2040c01031aa9242d07034000170460a0750031480d22580d0f454291a81075400803842e9000010490551424450340394209800300e403006a100044d01c44030301d40e40501a4090292094810b46140d42c101c14031014400b44d6205251441ca40301e03503e4011440406402142e0185110800141503005d0b8500e1144c00340b003036043c0140d4904c0c17800b50215050801490400b080503213449000880d51000c008184c0606801c1c1c84040f44a441d8014400b4072641c80181036086a04003003d20200741c0302c18440a0f0003400c9031828010300301080c0b01240420b0003030000d9503170860080003040740b039030402c0580c1d440d11414103095415489291001e4140c807210010587c900e41c00c0292380200007001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 337962140 1250 337960890 337960897
    0xd080403140c0d03080c271c0f03080709090e0a03030b1c110d0b090d02190305030c090a23030d0c0201090b0a0e0a0828080d0903030b190f0602030708030705 69
    0x1081250715213820300e441100210b0b0501c1601c0c0e00d640c120b0080d144051450300e00d06a14082585040c03c140c8d00c0d0250b01d0740b42008600103406003c1c0010030340490461441070b0780c000c0141c12180818030024044103181550341c00ca00b501900041d02d021600480341c40c10f2f50542a60030110000f20b007040c1001c0e12100403031000c0b0101250b009150707103c01000a030103286a01d20560761100035010f5081750071b0700030341060101e906001042060111610010b5007100589401202c0c0c60280354660152402207440f03540c0d16000ba550070703800841e1000501d031129800e034203d285e0580c140c4240040e9180d09840c2c0b09035005009021410032102070013840240307800b400b544003c41c6401c02d112001480401c04440701d9401c545270302c4d0032091554040b11080ca0510b000d0041c0c0b1550034100358840d880b03d04050103803003456444640c5942c090400d1502c00c0d00200d0580c68002d102d00050100300080e01000c01c050b00c01d25001a2607600300003186400030064508030b94211074207500c0d47d680d140c0121850352 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 337963390 1250 337962140 337962151
    0xf030309170c0f01031e09020a0b0c030d0207081c020a030f020405010f03090f020d050d02010c0e01121e020d1406030705011b14030a05121014010e010c020d080403140c0d0308 77
    0x60b030f00c1c510b40505004071401c801b10350042a0b03000616049034014040240c40d5074001d0404034104006010b4441c0e40003040303e10340c05078030000507110784d00d500c0e0100b811b00c00e820302d1210640d1210540c82000882e9130003804c2100345524204007080c8482000d40c1640120301c1058003166900b20b440c803085000c2d81124501610030400980004a50750005581103a00e943c180c070b44d42e02601c400300c0301603024444d60482c7d440d41e080c911b4003206070a0002b4844800c8100842101d515030701070107100d00c00030402d040c80c00440c4c0d20541d10380540b001d2940003040b00d160101601413040010a400313060115940381039800c10380d07801c6c25a0200c40c4413250002d80100c0211f80c610441100713030010160170700c040c02141c00c00d80c2d0350f0340c3d0310074503000c0c8035040c2c4d54041c0031100174040c0000100501da8031940102d5181d00203090940c0140d040d040140c400809145002c0d410008440c0030004110444005109503845107c003185c6809141e04001e95440408500a420180311503080c0046400b0301505603000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 337964640 1250 337963390 337963397
    0x50f040b010207180f02030a270c18290f06090a0e0414030f0d0b01030b0102060105090702010f061701050106051e030402060c010e070314032a030906040f030309170c0f01 75
    0x600c1e02030700940890b4008ca40200380075555070212544c1c02203851081c1c1e1001c45032001c0301040044c075128884094000c0c443d0624a9061041d004111481900304900b404072020941c44902e24460800c1c41a510700d1000501c11140c07079204080c0c0e460044107544010b40f010701196041400c040300caa183d850064000da1301082c00d00b42c0c0390641c4408000921902601c109a41e440d030020010100a607a141c99600b4141801d09040400340e0360300240707107030444130104d90501441c2c581a006078010036420031007021650910b5004102a41408481081d89441382c000b045035a030b803078030103c4a6000388030280c01e403805100e11358200b0045a10195070854001011285401c40046020303003100e1008a00c2c4284d40c01c40e000400c01d1110a04c603022545991700c029600d808021020005c2c4209680b1880440780d84015084507410310410603903003101400381c8080d50300d82d1507802000c000c8001d8403044000070b948050103d80d41804035280450307465000c0040900480080802030596540800035040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 337965890 1250 337964640 337964651
    0x90b0111070609060305150d03030b04020d0c0521010b0316170a050603010e010e1e07031406010e070906090b0a0c080d06060206091207030c03020a02150301050f040b01020718 77
    0x5100140300da01d000301620707107034010041d1a1481c080c0c265607004000503208141a0b00c0c402468441d82d5101c490b10740d25107000100c00e052140020002d01841c00d44500380e6103440d0301c0851407078100004103000b806c40c081d040101d0003840c0b4400482d103c24064900610428004030361615078013807002d01e41114606240400089072003400d008400d0460700c01c0100c584980c1030245030708080c41188051004c1d107000b8003100c01c0b0b0b81040ca0769400d4000c4a011800d5846507108441041484034001441d0f1207503004e0f003007880350401150f0301d80007805490141c1411101041000340200004003c40d10765488520a00d450310f8840030140c7c0002c0714a509000964441d80d0004640c9001080313450360182000400505105009181680003400e0ba03c490b07000b10340050b40411000144c50f85a90b241c03a04001000d103078034089040c0030b4100c400079040980c0c1d0b606451031180c888055030503914240e804c0100c0302d40d00c1c010082070310352035503103940907170400c903c01d0054580301138516074070341c2e0081c902207031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 337967140 1250 337965890 337965917
    0x27010204060f0c240203011e210f050f0c031504150903020f07030804170111040306050907080f01060905060118060e060c10090b070c050c06072d030e01090807090b01 73
    0x4c0450240c241e0040031980000180304041e105175800401d0410400e6269807241002c0221b01c40400706015480c202c15a09000c00800c055100602c404591240a0781c0101c000b8400365a5580e40c0100c0c2d192083c068624446031218900440a2007035400003009442046000c003a80700074600320800340c0440c001c0d1010010070210410150005601c204c0149a80c0e82c42c04143c00f43c00001103030703070110603410040f507132a030501c4010942d003d49400c007100144c15200c13500c6851401007140c1c040701d42406009400b002c01541940322008441400724280200d0b65064011100d5144a0312a11500c035135a94061140d584210601c600910300505110f10b81b00c4e695103182d14188513050041c0200d42c8800d04042045503103407010b6000607481c02d0001c03c254480c0d44268840d90003854160081101007060310601405206043c0210311b400004040c854402480b6000c032100c20006901080c45142d684203554030035400c4a00b20380d905000303440c4032801c0003078030405050111000390400490f20180345 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 337968390 1250 337967140 337967183
    0x703050408061e01060306060507060b0f130501051512042d080c0f0d02070e0712060b07020102070b0310061404090e0607020f0a121206080627010204060f0c 69
    0x28040c40f0201076104010300d80d9483c075009914143c20007401c060034003c04000080d080415503241952203040401c0d11501d8001241b06104254003481e0303c80210081001040019840075060364000e48071204a14400d4000d070100384580c032406034100e2083d20000c0c000c038810500703031403080d1206280c14003040b46ca02c86a00b902c004001090300e806c0d10005a0344a40d820810a8003040078151015000204041102944980007445000600e681c8400062001c03407058007448007030811240104185500c0c1c48412196810103d0100d01601c103502c80410b8880841003034901c21895844c6034940c06042c0701044078020104442e800301ca50040c08007007648041401841950102c81000b014030b4a01108000d1801004000a009a81080d10603601090380000756500c1e0544608002c00201c0f00070301c0303000007090b0317540c403580c036501401040c42070144000909004851000005031100b920500d08a8202e10a601c80c88012030104a900e02c0c00500422180300c2007030244c00745601d041405035001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 337969640 1250 337968390 337968403
    0x81b01200c060124080406020906040612050609012904150206041703250c0f03020d14090a03170f0a020c0a061d01051303080f0304020a051c02060703050408 69
    0xe80d201040801c03041500340301040100e0041a485000d440c6288801c070a601030048109240c0c02044803100010f0300344541501110b0003281c011b080e0035a00c40c1c0c3c0346030080003246030180310308840d4109400310318540340c0f000505050302c0c00031450085000406200400b010200800d56038008400c2c400000c42c0140c49410080d00f408607000350489250914040013013178802d540c9072400364002c0c030a1140c1a000469201d04d280154582c8040d1040704640642e4200d079220340080c040581000c0d8801010703400b240c0102118800e44401c0100350071880d440c02940185215550000c540900400c04541c0001c41c1c52032880100e56494a418465528a59241d110303942140240c0c2c0803480184042c107010760030134004d00941c0f40010041d00c40d032804030046801c000301c2d54104030021850807440d000c2085c44c00b0055602881c2103668002c800403032446504112020391007078484143c0002c55040c5942d1403000303402420303019070140e00b032a070821050750004502642040418800804d1459081144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 337970890 1250 337969640 337969691
    0x10050a02030402040501081506010c0f0209070c050c0a2702070f050f07060c0203030a0e012124050603010909170406030504051e0c0603180111030411010c081b01 71
    0x56602c0ca4140180300a840c4117922800342139200800150001d468660525007001007440d0215070f000c803c0c101889a412075000203540024111300303100c0d000d50001c020070402442071042d10040b132a19010001d8045481c0f017200c84510390002c1848000c18190305824800344442d00c0107003840e0040e22070940c00906140d08441a6000c1c05c0380c030b50700b80070400410000300303a10319040007150101d5022940328001c0d0b654a20038040701064a0700103038040c50344a0050540002b034250700d00440781791400078007407100154940440c0328801480200c0340081c60004d031140600b04525507441e01d4640310082c422441c060382d2014070440d2015030300714040c006000130090303640c01040704d00307042c20103904188940b2495400c54006000b0280b643c68007140201885404691103600d03035482402d0564001e05440004245503e041d2024003010880400343d4041e078011400744008241f8040190b5550000410280083d0020300080210280c6143e03001e200c1005c0740c00101d00480d500c001074500b5035107685c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 337972140 1250 337970890 337970911
    0x1020c0a0311070909031403070c0b0712060e0c0f0307020f0a0c1805060a12060f050405010c0f02031806030606070501060906091a06031308070f08031006031416021005 74
    0x1041103100808024243c00b4006409080042007440c0e94081c010600c001052841d1080210008100502503a00410440d400c070f0000c403081d140c08140249440091013013100400d1400d4400f14103a0740c0010b00620403201d680d00c0501d407600e0f2140203d0103410042c00d4000b10300c20a00394003003002007403081010191040524a241c1404e0040c006600c1a110130304040241c41e110421460743e036440c10b400c0881e004030701448003501182c00c01e01c02818a8030390228505080c001880104601503005200101e01940c898000c8158200308a03241c0c440c8000f90421041d810311200b14901c1c12100540c2c01c10002804640ba000c219030300c550a44001da40000e90991340d4074030401c101c000c4c9000d03280002d07244054550380c4100100008485000140c2281c02602c0c03591505000c1003031401c112811160410710f00344640c0c03040e141000990f8412281203081e00c411000c0068ee80d4003a0240003400100e4140302d99890703503200107800142507000c034400c1c118490401d452100303440342d204013400b501943d90b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 337973390 1250 337972140 337972157
    0x13110a0b0d0501170c1f1407050f15090a2003012405030c0105040b0304030908030f030108010c030e06040318090c0e031902030a0f05030f0a0e04150f090e01020c0a03 73
    0x3110356680c15810075104e4098102e040600c103244c2d9640d00840014100c4500d101000b10042c01c100c5280142e00f0800c14400c0001803690203210002880ba10091161400c607200701c0600340303807001c1040060303507050055480b5841c1c1100045e4440561483c2c0c00042e0400c1d00c501c82d0b5840001c1c01d55030825164000b00d203d00c11a91444041c7c08949030242005400400207402140c2c00282240703c0d9220381f400d188400b00106080500c00d9509800803e090030840742c032240d00a043c000150720a1150f0000e0b0b61034103121a00141c0280a4503484090391030242c65250341da900c050b00ca01d0320a010402c00d05010a0011542208500c9884101e0034660b848a26140078402450320345400a80403d85030503600c001a40140e80014210b02ca0517880b00000450003e10318010745507025100003d1030310200840c1c1c81d0340f501d40c00705030740710068012141407190800c0c3c5082c1195600e0980a582c05801901e2018802d46080b03400801c201c0c15820b0006142040300340c0141c1c01d01c04041d2089000a401c0b8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 337974640 1250 337973390 337973399
    0x6110702090c030c0a050309030f0f1207030603020a03150902192108090d0f120e0f0406080601092c070609080d051b0313240813110a0b0d0501 63
    0x11040980d200b4922084140b55040045120146000e0003841c1c2042103c0000014240042807080e034000503008080c8035100c120510091807a9003010061084100030240040c4e203151217802541c00302c07500502410384080c2140c503507000f4406010858100107444014050050300c5407662081e1003002c0c9032440030301505251128003000082e844003160741e00c00302c0702c0e00f0210b50f15208451001c0c004860081c03580e0780500d4980c3e404440210040d1040400caa0690000ba800201920058804403500301d50101100c0c208412039110340215030881c1e101c00014044c80d400340e403144c940000160101040d40c0c00d0711841800321a1000114600c641103100100b000c20307000034a04003e040841e0181203490754280000300b603405001d4240c00032151403070140119490501c200d07584140308500d50809203844404468843c0e42104050000b900d0101c03059040038840d8040c5401010f90200c00740110740380c0e071102c4907011094058540c3c041140d050014130400000f0007821000300e0081d0210f020343c900b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 337975890 1250 337974640 337974649
    0x602030610020f1506150406090e0901090f0305090a0e0a021801170f0408071a01080d02010c020601140406050a23040c02060a110c010603030309060b030102040e0c0a050706110702 79
    0x3481c154015580075500780000e2140100c0e214038104130244071414551795140c0000c1d41203c01c034a000c00d24100021f8040f429a90056980050752109400d02d081c907141c10310b115003240e40444000d00300c032220704503000001c1c0c0701d8030003000c1c0b0700c02c001e107003520090302c1d044101d550200913140300203d0f99001031010405404000c0f410401c20013400c01451707240320030301006000b030030060000515400880014003007203861001d480c4129000142c070300b6106403000398880392400070b00558a40c2c3c46140394004042d441401014076103407142c4d0150404c0d03460300d000329000111803c1620350043d01c4060100315911038581c0d0300010b05100a2003028a4003040480c40340d0001020168003c5007082d840002c003d4000031701ca0340100c10044000b588075a14400e840700d601600301490029400c25000009040e4907402049106000303030001c00030248d410702010b080380311300e2003683c5014002c4c10015920040030000f034102d55503d804d00c0d515001c1d03039945180171150061101040d216010038a003065080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 337977140 1250 337975890 337975909
    0xb0612010e06060309060c030c1323030d020d051b030307050304111009050f030c1002211303020d140102040f08010c020d0503061917070806101505030a1806020306 72
    0x42070b43c141d031075400c0096031a034441e030006201c04a9104000302180702c003071b56082200c2441018400e8110780545840d5040c91000341101002070980c1a995680e00340c1c0313004290600884850b40040c590802c40b60815201500420b9003020000002c0034404c1c812101800210310840c0d86984465907807a0a00c1c14103100d1103038080342805645205540781045800034910b109a817411281071030040081c8001900c0c2544000320160000100072948100c1500080c400390f02d000040f0030500f0144030580c030583c00f8000c00c07100c0780900208403404c00250901c4031f035400400f80145500200440305050f1182079078066800907400040d401001c0003003507428490340702d040449101400c0c031000314140040081c000a4030307540c46154801e80341c1c203214104022050003003a803d6207100c14801800340242d1100145c0c4510400c901641000826400c601c000c12025202d14400110800d259003d00b103c507a000103003003600c0a030340d035101e040009980c0044090014031900d4003580c2c0c0e183c0103041c0000d410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 337978390 1250 337977140 337977151
    0x415020d03150905180a050715031808030705040807300b0c09060d06080f01151d19090c0906060912080307050729070f0f0f030b0612010e 61
    0x515000b5108200300842540303800b12422643c01145a0f20f031701ca96491640c00403041d036900c030f204440b605010000c0119100c0119070b24140d009e009900405000c0d81560203114070000c00b400030300182d01c000344010f070180d0342055086c03411394103140d2104182454000150013070103000a8103010340b010485100e000d07415402c283c21070040300d480d895403041c01e21310000e0f00d6031001181c085010040e54951000f1780d04001950359050003c2c3d0f07640e0b080c803500c40d100d4a002e0f12841d42400504500f140948011320201e40e00f040c290b00300d0320b490f820fa400441c3c01c080d105460340404910320040c9120980518807202d40a000c101c441c003488c02c00349008864070b680c06030060000d038050801c05803a2804c0342680b582d0704401b00da43e0700d558524003255940f080030b00052000c200c800c43c503107801a07e207221600c2d00155496014054850f000152200740c9280c09070070000e44c50340d9104001902c01c100343d080c5075646080118211a03c0000160036400100c2c00d403e008039920010000207403200e11040c0c010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 337979640 1250 337978390 337978397
    0x306090c031002180d110a03060902150a0210050c07060c050c1c0509011206050409080409110403081c0b0901090e1009030507021e0405010909051b131806020415020d 73
    0x1340c014510000ca01141010039118030600710320074090054007101c840ca00e006c0140380c3d0341d030540c4074035040009182c20103059000f08081c942c1207204070360a10460b03c00840940041860700c9803054030707101510006282c0c03100240305124010000304d03030780203e001c4d81229031144e5803200550306050b4600b071010300d0608501044086201a02030f0400d003105c40caa42c0a04e48030510201032000034025020907405150001c0c6440b50000901c18a40081c02c01e41e0701426041c8150205100d00c160701b030080b40070191800004004610b18001d2400c03084002d0340d042200400c14042d80e01c001078003424268019086640c84d071100e0840050705005e03103182403103080c0c410880032416031001001801030040080c010303080c1001e00008400b100012980c1a2030080050110f982c40342c0c0b9500280c800114121041e110304800a0a095242e048244410798040c105039060910488900302424110410444d000e149141359000b00b61640014005401c402c403a81c070006d2442400240b6001d19240000d040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 337980890 1250 337979640 337979647
    0x311030c011b29070f030c050d090519030503270c061b0a030c020109050907080a1107020433030308160918060e100e0f0c07020306090c031002 63
    0xaa800900041154901e155114241442898010081d500442c80c0e030100503016001c00c102107244204892240340e0342e5a4501111030750080a86c10348440e40c0040000c68024003010205502c281d100c9407000c1d026604844010420100310032055465041c1034000070b00c00401c00c02d1461040d4603802409401c0d8403188102c8004204450712442c01c02c913010700c0f075500014204460f07011918080e642800c00c4080d40c0b068115031a024103102c3e06400c049012880c4031a0000c0c00e40750001c201840b60419480b002d99075a60741c10f000e4018003280104c0c05c0190003d00c800000358503280b00310b0b00400101d20443c9100a004200f140c0c0c0294a0503d85200c004455024000694000600e540084100c40d035031818903c210020346a000280d0040d1a100d03900c82043c400b800600e4101001b2540b0607030341ca0701d44e07460300014058203030791500070740701e00000c4440403603401b003c00d0741c080d9030003041c003114a0f050541513030000341040d90a407042d04095110101c1261035140c20310458a8503480c03034808515 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 337982140 1250 337980890 337980913
    0x53d03051b1210030b10051311090d170f1215150901170a020d0c02030a0c031d0909060108060114210a0204020a0f021216021903080310031103 63
    0x5072181100510054440b480481e01d00301d0f5403150383d07000d15446030040c0b400d8a844988080b0844003031207014444d81c84582c0d503481032916403040d02041030140b80340f18502000e400c14016652120202210364120750301c0c0e0300038501440c9002d0b28450743d50504665039111040280c0c0359140c00034049140b80d0300248110b428507911071030100d01082c0110340c0691145006001070f0f500300040050b0064190078070003000041a0300341e00400c0c0034803645400300500107002c03a040fa41c900400000d000414811003003800030900a4881510408a403001d0148070a8010b0101b175142009442c884210303480a0300621480d901401514050720f001120074001209050001c0ca401e0146807144135001c0300381e8106203010030140048104203070058025541c500710a100104844441414900140282c13000b28050365083e108696285030100910720311016030f5000c03c0080300310304002610710505100000300182c8480007652280c281c0c10303c95407030b052035414064000803403c4c0d0708a11a400a400612 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 337983390 1250 337982140 337982191
    0x2010921021549090b07020a110d0c05192c06060a020a05010c0e010f09050a0911070501060602031908060a0e15031e070f0602030301053d0305 63
    0x200e143c03854844014010001c4801181d000119114418010203d0000c01d054030501d50484994144168444500340d1766500d01280c840c900340c080204004821401890700e480c1000f14404518000e09804504035507440003e04030101e82802c6040710440714408200d011700400f168600101c0d001622211001d03558040400d0707a000400c5503205039000700740708403418800c002c8161140e5200d03000b0031109445460180601520305003d9000580e40d0510401c0b16111b591008129040540080010760038800f54101810b503420044041e4181800010041042401000024549500515582c0c0d600d10440c4614080102c0d410007441a000203000041e1180d240e558200e0f60341c80f0b61040d0a40724100c0d0018840c3d41400415450303c90070b028518a194001c0701c01081d103c00342c007113812241e0342703841041c006030032481014050780040c001080182860190008070a002c0d540035940c01e50a044290400301c070002d00d0240071142c006d050044c950701845085d412941404000921500014800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 337984640 1250 337983390 337983427
    0x601030c0912061d0109030e041a060f0703020f07060804170708071b0902040306020c0106300809130c08090c030d0c08070210260f0402010c020109210215 68
    0xc1140b603555008107545201846002400704c8800024000c6031032600303000341100d03452071000c0d21451400900089400107490440b1400390050720381424481c403032108442030f42001d40207405500544210709442c200c00d005c241c028102c9611228810308080c10f0a040130720700d4482c248005042001000c0200e05403806482d0120352011b001c4100c210419100e4144a02ea684220f440900210300401008181c1d0082c21000c17200000070080555940840c0380942c0b05910b030f210441c0c0781d102c800c4844800481501900f070380929030391482d0459170000320310008642441c42075032a96854803610990743c40200070760815007210044c007100e400440001e4560392098102002e108041c0b1910003000240b0041e607504640042c43c00e04207601c080d0b40071b42008a180b00303911614008008120103a02401700c2d040c00b0b0030300c01c4520841e543d00c0d607005452190301c4e804140d06011202c000001d1516401d00c1624112a0b5100c024021000c0307481484510640b885550300749600c14091000907400400c2c18 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 337985890 1250 337984640 337984643
    0x20312011d040206031b0f220308030c0708160308090d110d0f0c0204091103070609180b010e09010305010b12030f03070e0d0602040e011a07150b03030417060601030c0912 75
    0x403160341340c544892105000c82d408945080704080031590b000075502d0740008e02045450448641c4003d070303104842c400e1183c2240030003408c010b0f0900202d511418128040d03c0403030311417410740c0e20301040310b0a62060141404012400250030303004002c00910144100803007241c0508101c064203080c0d0003815150b003120142007081046600044c0703c41031103a5008800250080c00402600f0401d08000003140050b04103039000c0e03c6041000900c551040182c0412180028104560750072075180140c040d0911041e11810861003401103416a48e40041c41e900841c0708400020740102400d05025a0402c101c0403440301d40c105000441401405004496009001e031800031110140000015107c141c41c40c4043c10561001c80c021030035090002425041c0c0d00c0940320380d0000580345082a1451080510041408481c00400c2c26140015004100c1050340101030302c0c14035445540724280c4041803000030300150304c45c4060049550705482441c2144a00380b500c002182d080101508501024100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 337987140 1250 337985890 337985899
    0x9020910030b0102070506130608011e0b090609040e06074112070201020301080705040905211b03070212010e060f0a090b070201020d0c0f09050405090a02060307020312011d0402 78
    0x340b05082e0b8428002007000d000d0040005440320300d42d088080b031160107070242e440810800e500103d841d41c0d0b8211034020074848900746180b49424507940180d079030032110059400040c18029140d803940c49020b90094207040c01d00030043c0749800c0c8001880503a0102e401032400101003202134508400c0c403484280b0421642c0c41c280f8405514001071020b00c034442012600070044c1c000e01480c1d643c19001103040750107103011144000d4840c2c0400c4219401e07044018030645c402e2100c0040149800070028603d10250b8803c1d003440032440c103d40c2c2c1da081801141c10309030000252681145007a1121040100800008000b1040301b03030100c079961400900484051408100011061034450300514415684020115800c0c1000034000e8040d4008100502905051500c5003462610941c202c0200ca1036a41c0d8a04442d4500780c1880010038001d04007140a000d00024040036131039080003076008007010b43c011a91090101b5a1012809040e0010f80040d22910800b9030103000e00c07800a900103804aa = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 337988390 1250 337987140 337987151
    0x10515090409050a050105090f070f1d0a0609020c01021e0c120f0f0d0501050108060102010c050a030209030a0c0b0a08010b070c05120114010f2313090213061404060902091003 77
    0x1c0c41c901d4084e9600d002496503007010f0401040010101c0c1000d85251001c04884030242c4892040b0345c00b0109024840007541300300490002c0d90038804c603103908118070103400101e05032a0340039002030f640020100c01060303400140b04120011040480c241000310788950f1801c0005040c03103207803111a050160304100b0004103c140d04611a041101c007580c5c1035050f82035440c81c0c4c942301c900140a09209417408036001c10001129540103000c0e41145e01c0751543e81e1071810404000540080d000b004d042500b5129804040b0300107034400d1401c0703001e841c007100c00c607880d41e4186800034100c5030140c00181d000c0d002031024400080585d0340703001c00e80b1400c48400013110110500140140100c044c0c807440b1403c00c030b0002a03600c45034418036041e51040342e105100320415145800e103105803030f4552074114100c0fa10803403c0226641c4400c42d0184000d028040310124503520385c0550b0810341150043c04481c8803070814520f440e01c1228000e0822031000d40c2840c148800040035041d102105005160305c0b031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 337989640 1250 337988390 337988393
    0xf23162301090e100609241110020d0218030a0c0e2809030315060e152a0c0a06120b040e0f030306100201050603060a0903170a090308010515090409 65
    0x1c00740c00c0301800101c042c4083c0703854428226403000301a8400c60012455204000c1122903d0702114116102048036603aa5410703124000c0b12081c0c001c401c002a0303400350311169000c814540c0014040a49014000750321002080750010743d4440401c546031007544110030440014000030620411604598012802941d030307100003005021a20071003039000c0030400c646111300d00c0b4075480320401c1800303554100f1001c0f034808401340450a5600920003c0b400301c0320310000e60325101c080500580714001c0c9050601c401902e4a401e5070140c1150300b07960034161102c2c0e800c605c0d404c0200c0784481108540c5225114604540038044000f520319007100c160712003405980c10744032078121000040c1c540045a92608050121545035002a60000d100f05e40f0f0140a88036603105008140c0100c0c0005c0143c819911140c46041c01070031400030850a101c00c2ca00130308032402c0094001d174400d1480a002142441c0d0390301d0003c2030040140c02c45481019002010500384114100790307400808240c40000c1c101c0c923607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 337990890 1250 337989640 337989647
    0x170a03091e031d060d050411040603050d08090d0f2601090b150c030313060b09010608060405180715170705190903020312070f23162301 60
    0x10180818007045010031064100700c04200708103010340d0352425400310118030b41203444001005280c0c05141845549003c089a51103a80c001c0d10030300c03903442000c0b034140c04075080d140d99500c107803120b0704038104084241d6088107aa503030000341c5201401144800200180c42d5000c102440c1c410040c10756a600c1607810081d07420020140c03844440442903079607003004400b606a40380124029a0708280e8000361548003015614220801e1002c0d5041d9920080000c0c000c124202040c0c0310151520a018403503100c01c0c101501805039640c640c400352828a0512042d60f0004d0308850004203000d8500144504c041001010759600940c103540b107481c00e403002c0303508000410301c803064204003000780503050750050003c0082d02d0302040008990215840180d85404140c0f10194050b000180103400c80e41c3d440e03008019441c0316401d5001c1c1c42d00941c88031003a01c200f00402880c181032801402e10014410040d01c8182000c88800010a80c10280445041c0303086004d484a50241c11680c00740f613a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 337992140 1250 337990890 337990901
    0x100f3b03030c190c05070f0f080304030c091104120f060c020c030d0503281d07080619020408030a082e030803040611030403030f0507050703170c0f280903170a03 71
    0x10170000300da1035192030f8031150200e0390f1588100810300140e00c1d00000e0040b40403080d20100d0303402c0b20b01550520310f40603085025200c00021442424802c03c0041642c0a081114042d064020342c0c0c000540c54a500d0034104590900d0214801c0d503201c4070121400e50340004110f900c0703100500c3c2a540381e46603681d40b803032220301444084a4050581c016400640340c19441012104034a4804400c0291413042d050f403211454018089141c124074002a0f042c08081c26402c502c2c01551130051500e580c0c2e100c00c9003107030040345d440f000003841c01d414010481502804110044200e04d40c0300c03d1000d045002e00180440ca20006180c848044006000c1c401c141c4d20104200000d00d188642c0c038645464004c00030281c81c410340010758600408140118800c8066405040d815101c0070310f104901820005040300040940405880400071580041c0031080504194000c07280c07500c81c801c10340300922003a900301d09508401c2244102c802c00209840007514031a041034119120790351040b0901c01c802420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 337993390 1250 337992140 337992143
    0x62303100f050402030601090203070207140607083105010207120501060806040305030403090b03010e15040908300c1903060b16050607030501030302100f3b03030c190c 74
    0xa01d032061003558034209400203403149200720305450060780c079038940c0740c120f00069030070400580c0480760510034030048540540f25050010a6182000c0444c1d48220107503012110351040341031080c1200c81d0180d8a40007055500c1d60920003400c8950802d03000070368071843d1344601d0004001c4090100181700003907200c44040c100c0030342515801c3c50142005086c41e0f0058404900003903810b4000900c0c2d070000c006890603101800e42c2c60400380c6a03900f0803039031705071010601503105079501100400600c4803401410410300380d90f24a00403078400c0c074031011b0000c2d02c1041403002d60440340420010100c2c000880705c4204401c81004144034043c08100c00610207a049a002c414000174002d80004810300e40806407881101250781035609c0c01e9007141903940c00c1c400140503a1060030b00050504954100c911010f00d0f251002070224901c515a56040000101c080190101507084a0711620400141d043d00c0680900a41c036504210080c1e008621485540120b418101390785456824403540301c560311203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 337994640 1250 337993390 337993423
    0x20a110102030c0415050c121b0d09050a0807261018151503171e12130b0f0a1e06091b080435090a09062303 48
    0x340350812000f0a5035215016128a042c0903038001c00016110348112a4010000c1c2e01034a9244512072003164035030000f0710003021040042d850b012600c0c2c030070448100f07080701550382d83c0c02052504c0d090010090b1160130021080e00038210074003c0c150802914041c80704405142020500d08107180c03401c220a911004a80e1810581901400c9070703003603a80541c442c043c0114813040550b0100030b108036941c8074046100b006041c4420004540004000d040040c180d482480c54800400110b8040a45251054020b010b01046e000c44001c0c483c400c403580700304100382d02001210f10380c55100e007082d0002d00c0420070b06c1180d4001a201d484640206000b42c46240c14690600030540800d800b4144500a001209290003449801d6a903040d40c6c3d5692038034035441c1c0780303265115500c89005040303440858054003200302d02c203100c01c01c12061610803040c002a03101c50715000366508200b0740c0110759115541060600f501405102c11010a541c07018801c5082600c07182e0590020030b061102c00c2c200007900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 337995890 1250 337994640 337994647
    0xd120911060a091805071d011b022b0506090f0a15020d0c05070212030306060703050d06030206031305070603200304020a0e011707051e100507020a09021206010c0312020a110102 78
    0x40c400d42005000d21030540b1880b0020700c410406031f00485101a1090014a0700c0d1280e41c000c201d440d420b074410500141081252500d1102d0720011085803102849416107202003003024040c05100141e04007039520068001044100e03041030b5240000c04018203c0d1110081c1145030114650454110380d210070340038003d04c1c2805002404940040394260300540380400100001e103008003c0f07a104910084c16113003014500c1d1000c94181d000540010842d5940e01800702c056a03c440c0614070651709075140b0881e1502d24035280b42051040e43c402010300d4100f80c04c20402c030340144110000c90001c00821034883c1d58500000740b0358040790303100d01080c049103400032508100d4a6503000507a0407403411030301c2c0c0356074910a1110780100c107000c40303040030454100c8a00d02d00c1c08000040507162146006404d1102c1500020038080b015030040c0b001036030000d14200c5008013990059030041003400e0a20108a26450107484007041c9804034070030076030000720400d6042c054081c81c1410102400210b48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 337997140 1250 337995890 337995929
    0xc0111070f241e1b0209010801230103080301030206030c090d05010c03060e0105090103020d03020708120d18210c0804030c030c0b130b0d0905030c0d120911060a09 72
    0x4414a00e00c0950051840e103070140d4201e507000b0a112410300443d480305400c01848035204a4621103201c0d48020710301c109440038009a83c481040e54040c0491a0000400c035920401c004035207800d91807800ca54046c404010804a0f400c00281c0e0f0440c2d4041c1d41702580c035580c0c0c042c425400e114071103119900c004402d00c1602030200551250752601a1030300c0400105480f9092580c070070400748600c690102201d401803005003403009150386054460700450700480d84a02d07401c1e0030481c48209101d0052004102a100c2207081e000c2d9074a00380d00109801516586034030780d001a0428280d90700d205020440c3c1c10a00e281c0300b0107400130220307007290f840c40c1c4443d103a00d0700804401d20bc2c0b0046c0c5d0200011000422042d12800882c3c0c03081f042030316856612440d260300e103e01030f0015078280c801a9512032403000454000c4c00140758004800014285007009440d018001e5140608140d00c0140350408420004d803a901c0188440348040740e82c5500c801d404c050441e000c030f4054106580c0c801d054810800f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 337998390 1250 337997140 337997159
    0x240d1a101527050d030e1509060d0e030c0a08070b060904030c200a08010203010306060b040f030b07020102042103030507031a1203070606030b07020d020d05040302010528110c0d02030c0111070f 85
    0x2406c1001110340007686070b01c40111101d1030040492a07079019404100c4410101c0342036000c0c0c0c400c030590b101540d0408001011150910150810680d0b00040004000c1d0401800c1e00c0c074184ccc000011565240c03682031a4500501e200074840e40104141d03035101b1401c0708003a80c1b1401310540c5800401d83c40c03102d84c13103084981c0030350028801150000d09005000c903040d103800d02a00c041c2d5089145401c0301c14a16103800d03010440282c05102517542c208004540c10714a181004145019403501820804103450010215480201080100f5141644075203000d840030f440c02182200850741b611290300201100750039881480802006246041e20000c00c1255246074140f14070501c2c1c080d207038841a00c590580c0c80304ca10018541c001442007000b4001503000ea0003502a907608080400c2440311050ba9059407a201d4686a6000c161685840100c917001000744650120082d01c540685500070750201365100280c0194a0500910356009501d01c1010803908008241950b031850743c00d41d0b030700c1e01403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 337999640 1250 337998390 337998407
    0x6020a030206060d170d06120c03030e09040206030a0b0a05090a060303020f190b07030e120c0d0c0b0c0913050a1b0206240d1a101527050d03 62
    0x31000350081d640012100c0c50300703040e8005810f0b00480244020b4507013410502031584000b601c2c5c4402940d984001c5051f003180e64544503c6071054018007803150443c00d0103400d0300b5012000a00c1405c8002c00c000068482c032701925040b044a40d0041f0707540e41000c00041c0316100680000e40c122001c02d0400007808019081403003201d000343c0a4404503981302003481c1e00c0701600784015001881c2440b414001a0382101c000340d0080c0c01740b50018440d120301900350f080c00c20700d00c05030242004c04648442c22190900101d103003100c01d400c045a080c613880d0f44000d09a8070003841120303030780c001040000c00354071400380c40c403200281d58508000d24038004071808020a94948440003c50f01b80c208a100140002148c5002c0c0515142e951182030440c0b01d810422940c04034100c0d0001c0d0513020b00d0000a140d042d1441c4844290820000c0320b05d820000d40000500580c00341041c00c4001802030022500720410141c21648491581c0060024041015040034654401a00303c00d05044072001e0540c00b610700e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 338000890 1250 337999640 337999643
    0x1505041e0516080f070c050a03030c1e0909050901090b0c030411010509130c1e050309061005060711044208070b03310c09021201060302031305010606020a 68
    0x421050311074244965640645410303140c00f0890f60404100c240132510ba595500c52000d1414441c1c828887e03540303505100b20318100f107000c603444103070442000703801c11843e08050f01c90805982c4402c8038054020010101885503100c85543e5102050350880290040c0607650b0708940c400d070345800e024001c441d60303900031102607800031304c000b911004d550310417412620b00384d00040250701c0441180c0040390003008008511014401190541c0320701a42107407400381300d4a210380320507440f807400c1c40c861428150014181c032504848070b00144025038070102610503854010805103900039541000c80d0003040307502e040e904000e07001401044901c10100094128060350801200c00486080a801004449009124003600030903402c1c04505d290b68042c641c001090001500d1758040700900c1c07000400d40040000031b5180030481c0a0600c003008080e10020584031b1411840e00900002c171a0f140d000c103000d11400c058001002c2003183c7c0031b0001c074526254005000708055030740e5035000b0f0345c1c03842803580 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 338002140 1250 338000890 338000951
    0x90a150b030f0d032003012112030b0111030702100809070906090902211216020a06020c030f0a0b061203090307090617061312050c0f0618031c150504 66
    0x214081c04049446040303c072a917a50185505603401c0ca5090381e4a18100129103070311000c6141100007041214510107072640352500e0000c2d02d9494180010200440c644800220358020415440183c03a0b103030740042034400601e0020305d0760311910f001d1401d02400b036014611244c108800840e411165038800b0000e00e108494582550400035804003186458141c11401e40d04031a0f135108500640100904843e0002c6103020007501c52a4001210b04020350040070040c1d00040c420b49032800d040102402050340c41008142d00c0c01150340d00c00310917100801c400c0c0a241c100c2e1243c0c000280800c140c40040c007005082e220f24a0b00d070740105000381030612801020841c40303203082c0103080001c1040b41c000d9158000c44296288a5101d1003141c1c0c018811220400104100407890150103000480400c90200090700e0f07141045101d9160000b540510003c054104100a2600d91b180400c0d00341600140304000c10003e101c0b4600000e40d0b111a4400f41e08142000600080300390398610194243c0a0030b0b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 338003390 1250 338002140 338002151
    0x40926040603240501081005120c0a0e13030315030602220902070201020c0436060b010f08070f0915030e0708010504050a06090c0906090f060e090a150b030f0d03 71
    0x5040c40501007200300c0d804031640c400f0001c0c09194458400d21340d210080e4040c001e160b6541d04049941070700380c1080c901d0a40c20003c0c1030001c1d0b19190045000804c008842551181080c00c2c00000143d4aa0001400d055a80e28210501003480382004015a0403a0045450f51482001c441400b00c91300c03000c0d04118080c40010850034001d109032118283c041e40184a103d806000344001000380c0303171440e800c0d40c5003a10310645528407400800c01d03900b01280341940c1d03e0b965141210941d2804503450f070511064100170048180e20241d040e52002031845c040380550300100060f6420005504032903000c40d4026501e1001e0354040d004802c043c504101100c0229964503c1c223401c854040c4c0b001001c0760014440e07080491f14541040310554000c0c100c6c82c802586d5840010119141c0741e008103840f584800000c03850580c10300c03580c030041a010a0b198081d1403c50f02141e00d0f940b1305000100540c03825419800800c000e50b0002800c004090b003203800d0407050710016545e07825280041300c002030510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 338004640 1250 338003390 338003411
    0x90a0f11010f02030406020307030810210c0b0403080304060f1d07030b090d0e0d0510090b0105090f04170a1211120907080d0f1112130902090906040926040603 70
    0x1003120100c0346c590b4090b5040913040e0b50b0071100341002400031182540d1324080800c0301084614640019181118000013040b1390380b40549450f091548640c1040405100400220f113005003140d40c05944544c001400b081c00c0c820000041802010034a00c041e02400c40500c00c040015110f400c0e00d0241888041c01e40e00c401505076642107901000300024241c100080d281d05000280a182d684100c0598034001c3d05203840c60121800040c043e5640d0b40b0f60320040149041801249807c22a41e9095035424600394545400c81070010030850758019001a04094091040d2110400030300070b220144400609211801c0d540d810a81100700c41d1807552000c1211201d001814000b05c1c2c5110014001d0301104500a4481401c07080d1800c1c140102d6004100d0321180a00980d10b2010030b88005a4a0702d04005888542c408241c010800340d510410400c0059520310720740d1548000115408a100b4220f49004040c0d0145003841c006095040e8071500a030b403c141e4064400c0e80c03500d9508120440c00b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 338005890 1250 338004640 338004643
    0x1c020417010213121713090b1e100c0204020409020306120a170904060e10030606080304080a02042004080c1816080901060b0d0204090b0303071505090a0f11010f02 72
    0x2507a1601c0102c03860300400f0010503d02c10042c0c802c1320b000301030202451600e1706030014140d100841c101c240202d035100600100c60036101d000d2200c6001c3c2d80c4160f40e814610404800500c803400a43d10505800d00d1602d81c49111350354442503250f000e001036441c1d9070f85800d98400394005031100780c810400102d8580000f04001000b4003e1600812903901c031070307446401070b001548000058be0701300303890300c5011070340c074220a40c900d0191565901100e0100e2840c2800c408a80c4640c0040700030f0303041044100f01d25100001e200602076011200024080d80c1c004400d51a41100c1e60034088941c000705000900d903c02044151040c142074850300221501100101206102181c01d425801e6109082c21344040c8112584d40d4410b04090000505688807107125042d41c00c948524003002e500000e0520200c00d4a01404100308400c0d0029400c042e641c0c1d545c040d00c00d0745607000344545540c0360300150600e901001076003145a0032a103080b07010740c150b041c011800103600c034100b80422000314032030411620 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 338007140 1250 338005890 338005897
    0xe0f03010905030304051915020703050d0e06163e07030f0303050c030402060d090203010e06130c0b0c0729030a02040e06120d0e030109021314071d060706021c0204170102 75
    0x2807007600403100300b88c0038501000a4200010a5040240c28006d07041e05401500c98482c05480b0341c0001c101c1d03450101200e81c22200c2288a0504020001c03011401c210206010400c1030810868500c0446071411070f240f4282c0c3c1503c42122040c8540f10000061020900112820038001d0f0ba0520550307540001c0030300580310546000b500311000b0000c0400c40b03555a800012a00e10083c0007088107803020304000c1c50120705852200044418401000400c400024080010011444440e0405d41680a0030303860b1846442010070b541840300703011030601d004800e1103802d841c604c2e1b0020f4480c01e00c003503044020b40141c0502451261a4004181186084483c00c124100b030b40c001440035103030445044900c000320030903a580543d20380092a00603614900300300e01007130540c41d0004150141d06000508004094031080600803500c150884040740982001e0801c90240c0d07007070f5610419460700030300a02c186869182510640f00158244403100e80042c0308603480c0d4402c50b4404903a55031058200e11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 338008390 1250 338007140 338007143
    0x807090902071e080c01050711010b01020114010b071514060f030102070b0402012102210709030c030f110904110307050604120210030e060a020a1706010804030e0f030109050303040519 81
    0xc0c0c0e40302c2030741c14204180003c8103961007805601d0902c400c4030303001401c0d11410307941000403c824002004040b8000d1044c009400c2d400d100900c0301d03c03003044108c20403c10601a0085c0c02c44001412800d0242c1041030380c0d0105002d0350204069440c0d407403182000442039405611807130702d0300e400c2d1031545014020b958009411880075602520f46c6c0c0c1c015600d0800d0481444130711282d50180000d10b41c05803004c1c0043d5a200710314120070f481d0041000c0740031440103002c1800e010030030747c0c2803010810345040c03482074a034464140354070b415541c1020f8406003070b950311865002e4044400c1000b00004d1450840390104160110784003984c881040200300d000e64000c581c103201c03103902d051001d41380c03503c01d090111031542800242c2d40b00081e003840c20020100c0300300080d07507000200110103540c05580c55120514003080040c090914000003000b011002d400941000300164580c006a52400d14041d1010b500800801c581007076440c100362a40c104940603696802402011104031f0310b410b00c80800d00c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 338009640 1250 338008390 338008403
    0x91e07050910081b03070b040303030902041b080114040207020904140717100b0d08031810020405060a05030721060905090a1208041a040804050f18070309020d12080709090207 77
    0x41c3e5255610082e04d0b0310303460095251103400c80c0018070081000050010314041d03500814151414014001036580c0110b44040103d0071a10503501ea503400816681980d00e0210305824400240c40020040d018070305001e90b1186916050108020100703651f0045400341000340c510581d600d1840b0114111718048078a166040150030081d203180d40d9108884a08000f80781c071444070000e8403056800e030400c82e848582c90744000c0c84165222000c00a00941c0035a0280941c41c1c50704000204844c0d004104010b0240b20020011034600d5001e4410076038180c02d9400503017080050400410040c0003244a481401ca18050214045aa0200d06a4805508000c102600c000719103402c0703982850081041e50810741c04620441520f040c125258003445c0603101302c9445074240b0341007080304001340c0e440604ca005ca070070951401066a41400303901c45000e0400081a00f06800410301109140d04001c240390410303013443c1c80c126041020399004600a640d100d0b0115140e1002c48228403030380201a004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 338010890 1250 338009640 338009653
    0x5070615080124050f04140a0903120204031106090f120606100e0a0e10080a0f020f0303030601171b130608071716031e050108010f021201030209091e0705091008 71
    0x9050904205d002d80c00c003c1c10000300d9000300509000c40c100c0917152001e0403600c5050146c207042c0c1c042c00d154410513815000314178040c07842c0d4903908410b6071206150300520010411689030b90341e42200c2c2032814805080440034401512801e611088115030081c414154811201c005901c00d41061818500184c044544242803d07001548160010a034071912455843c002c00c3c0d942c82401060441c610032102c00401441d0b620422928400704c40311302c0d010350f00510400840c1e0380c0c051420441001100c044040380d881d44410085803c244558040d004071001440103007541070350980008440c019035418200d6145c0c09000c40d00c14a100f1400b540401000c07001c40c1c5000c1001031a28881c00d12400c002828140848bc00f41001403000004240d8550b13603001000101d03428054451a03002c40d140447c41c1c024049114000c40c24180030203401600684009440100304020a40b503030502c122442203100045183c0b5680d4600500a85000d1820304010810f002c5001c2000c80030f46078040f016080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 338012140 1250 338010890 338010899
    0x30b1b07020616020a08100f0203092d070605040503010c030c0203180a0e07120506060a020a06320403021005190506010c080f0c0610030308041205070615080124 71
    0x16603801c4076641c81000c0300f0b01111200180e0310702d51003000030712402c80034089800e81d4401502c201c84145503e1080c150042007084241e100104030700340040090b003404486010000d64a00c81303913604842e803040c240316041001c0b9602d030300329003c0c00489800f20f00912800c1c062003c101e05862240c9034110140c1d0061042c809007240d0070410303072040e10020b048459901d03038407403130550049000d654100104a10594401601c501406440c0c0d1100060312490300e4480c1040f002035940902c48400b81401e55640101884c54070a030000c40d060185000e02504100528003100d600c1c0c40040c3c0d4110f01512400e28051001c552500642c0e00c18602550306580e11805842000042d003002071184c0d040020010060b40005c0384c90700a48840aa088411030301c0704442441a4038005010300854a0f00714840401c10000341d014112560156000d880402c000242803003c0c0c80078010303000010712046c14411448040c1800000384411039030480002e002c00031214104820f00e05003c904103c0f030041e0103000b0720 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 338013390 1250 338012140 338012149
    0x2011509022a0a06090609020f010c02060a050c0f030c0c0117010b0316020c092d090604060b0a080307120f030b0d030e01110a0b0402010810080705040f180507030b1b0702 75
    0x9844030b030807000e60f4503103812540c4560032100c3c44441101c03203d69501c031010545c148440071089c02507082c213100b2200306403a00000c2d418081c0f61100020088001810b131103800080c052026101348a0f811240c0701c0150082c016140c982804803070703000494007044400a010030345182d90489407149502071854072142d08480c480591a10040158840d041a101c441d4968004892080f007854001403d440c086156242000c00f00801d180304030304580050000d405004034009801c075501c58400a8020080b07008134803074002c3c41d4001c2c09203000109030031085c040c100d456145021140e50303400543d03449c0c0740d40176000c860350361142c7c540144103030712250300190040100c40c00301941418480f000350164400d041c03400d148440125400100300341404110f58103d024a40c0210403400802d40c0c035806c1240c0e0558850130361141d6840359807a16010f125040a5600038408a1822190400640e01d5030900c10341d00d130040d201c00c40d460421000001c038441d9803600f2000d14076080220061400d1130540810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 338014640 1250 338013390 338013457
    0x1030609030e0607061e020f160f0221010c0c05031c020d1e14060102061b19020d181a0d0b090f040b06030106030b07050d090804060201150902 63
    0x214180400d102c1c911520382c1d90100a440d13410320920010540192010a00024072280c401c21092180148111440b5081038001d48092414081c0d8103040c040c1a42010083c280390031f140030790407458040c02884c40100202c42001e401050740024028181c0c2c40008403803000c5511400360098000b8402d00300c0c1410340750020aa9005144405330501144500040843d002c18000c002400c031700c5442e002e0000000e00902c3e0f0500f1121104094614251b00042d44400005141000344131258501c0b4135034420141c1580d000e401c08c07a03046d51503400800c0e400f03075032101c0c04811f00000c41c041c00c1c0400240d001c910580d0080d54803445206101d20345065510490350001c40c1c08004594075440300781d409840300790311030344039440310ad101c003002d030510b41040c12084c20080e003a6030180e4103121092001c10800c038181c90700000b1074907000d5070f40c8424180e10001030940c1b034001080110300050000741582e054101441010340c04024003074069403520408124132500204040c0445800c0400c1903801070401d55 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 338015890 1250 338014640 338014643
    0x406020318030f070c15091512090305030708090f030414060c1002030417030f070509062a070803070c090b03150406022802060a050604020c011416140301030609 71
    0x9940805495200e0710b4250380210001c0380a0740c0b40402e510082c091101d002d40010010034004140324481c0600050080c170040c06201d181c252801300e500b500500c9149010340c0701e08880b01c2008030a16900c1c00400700d5000b034411000080c40e11011491241001c079403c00c40b00d140354015440d040c40d001e0301103c05281e8030f0045500000600c080ba0000000380409a00301090030700040c2d40c1e28051906140e032611035a181c1020a00c02e004110b07010106200b0660800d0f12410450384801c203003000076103075209001707800760b0b1103480b02000c50101000c000340c1c80f00440c2c090240c40005e6120901190749004045003d4801000c040080165030342581c080b080303207800501510080140c2851440c0d2840c0c0584040b11090350010b00c604c1c111801d00038030f256180c0c071404000d43c0c3e8020440c0c000e40d0f84201804d03c40f2419030314404191181d66640c110780750340301018000e00c0303214814854000c12241c111244441d03440c01e84180004148681b00010070b640194281c6d41c01c690030758035204000c1051510 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 338017140 1250 338015890 338015911
    0x1f050418030f02070b1207080c0307121503140a03020c0d2303090603040c06020d140d151701062301090605030408070b0c0d0e0303010612050a02191206050307050904060203 76
    0x400d005c511034004001c038000d10150211141007214004120080042420080090901c14051141c1d480a0018400c00720301d0300100c0c650022403001e82c0c000c0c2003a40028000b140756000300203000004201d1000641c0030340c080e01c000a86603010720002501003d0000c04008404a00000b4102c0301000208980d2030042128103040086000c04e8481e44181c40a5401184050040040c1c1d0f90400c280d50040c64540380c100c18440708040400a14090b442045110740d03141e140d145503824042c0c42035002020101c0391000c0d200b0000013494020300d032034041e45403100c803007a801c5442c0445c44002200c050f001a9990300c1001d2501a0449940e013002c0d1003110550400c12040020a0003416854042d44080340c00944d40c4180501c203030201c40022404051942080c0010048250048400c000b82c240e02d06022985507134822664000303200d01d10045500002800b800d2154a41c494490341000c00c2c3c00301c0400800c2d40780d800f095a903c034a4815a64842c0741c1c5000200000c031141c000d56005900302c00b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 338018390 1250 338017140 338017153
    0x60c06050a0f0504030903050105100f0603180206040f0e0f060306131406040b0601112b03090b070e01120e210d09080c011d1b0a08061f050418030f02 66
    0xa00c0b28207440b825101034001490b90700c018402d2110a2040705e41000391041100c122520304103981908220301c1c03241e202031507907036148020441c01d9280c852460a6000b007046a40703030748407442520324040901555140164500000318141d884203903603405440c005006000d241c2c0c0e000101010001c5103030301200c00d0300002e203045ca0403450412410b40954480c6104119a251540006000c961088620070250740011460300110000041c25040194110542d0303c0203a0b54a1003500540b040321002884d80302c40c001000900750f03120180c0c0c4000042640d0740c000c81c0c1c0c200c5030010182e42000d0f0358219643c0005000c0034070b242481c00030824a03c86928400e0800703056003248800c0301c60b1400c064541c1780f800140040c1c00c080030300c0b80d010b10903000e1000c901e0504541103019500c03500912240c040b205e015914421969528098000030b00c06207044038658a0841488082d2003181241c2d52162411100d010402d440c0c517003d4000b10038036a542071142c4140640381114040580c80d02030301507001c0c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 338019640 1250 338018390 338018411
    0x30f0709020f0d0e060105040e06040b01062609010f061505040501030515030a0501050708100806010b03040206130f060f0c02010813061e1416050d05090709020712020c030601060c06050a 82
    0x500030782c000100d04d070300501480c0d8508000d11068420150301d00e00260002c00c10040000c0000d55600e06440040c44d00042644200040001040040b148801030f011000100000351605403c5000d0000d0010b00501c8010350f02c21100050418064140001ca10300388030a112330351003039200070392041110b5090b40207500124042410403e82403016151039446608101813150012206030308115041d0f0070304c5103030781b03802c001c00d4a0745010b0142d0f8188900010101d03082d075032108280c07520101190120103d99546032a40f200012552060101096405500c4000c840c0558030030401e09030180c50320081559030152503401a1134503042190307659991220041c200e405407041072450a0200e00009490506040c0b02400724001001d1502080b1081800d0344c44c1d0303600c00145c8412a0080c07001090a403141d512190500426402005075144040303003803810f11500302e001e074180815940a4440b1410200d0a00d62159000d02a01010890420900000402e0b40d441a075100c0700c0d200001942c80c042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 338020890 1250 338019640 338019667
    0x8030c040f0b180a08030708090f0301061203020c040615030b01020f0105070504050a090e07030f050102160c17060708010b180d03091517040212010b0a0306050106020c030f0709020f 80
    0x590441440c0e05400f10704032050080075014442d20b510111014080d451501448955a00c1001001410715030041000700c8613072900d40a81d0a420390040003071020300d0300c1d0b65140c401901184401c0d801071082c00caa000640c00c1c64807505080d2401c14902d810b18000c40c51017540541510002d00741140b19101e20100d64a500b841124018059540d5050fa200d141c1000c02c00810301d29006028460716000c4802500c800020343d6004407a031101010b850b5401c5401c0c0a4024001c1e041540c6240b41466640030400100c1d518100958040041081c103840c8203281065882400703c82d450003244080005100c1b000c40c2c03c018114100c024007402d01d101c0c1c4148003042d061940303c0c030101e010074401c41c0706014075070f540540501e140c80d481c03900030401c000e00c00715002c4400d8040c2002e03010703807046400701d51816020b411050240300b010340040b8040b9682c0c60700d00000c0000340300e940018000c20040c03020520740030401031501c82c24400106809c40c28048a14025400310540740e45005040101141b02d400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 338022140 1250 338020890 338020919
    0x150a090c1206030332040302150c0d0306090c0c050c010e03010e0f03090102010c080c03220f0b0603061609150512010602010b03160302061c0e0109050a050c01020705090408030c04 79
    0x1c071707984840082c3e4082c2c001e4205500740444100700b400b11041c0d0b070720241445200380c5044a4040740e8a0f10007055a0f0981441d42c4101c290788515030040a0b072148074075806800007400ca8018180030004003221040803511480d6030400104541c000c551301c80c0c1a58801d0144020180c2c1c014000582101ca00e036041d40303005102219070910750000b0403803000541e0288100c00244900d0f045c1030700203103001c0c2e0300510310340310003040f80c2e8150b0b0b0302c0c0a510401030240c403090b5054980c04030003207111410a007081e01c003050085803100d209100f0310001452401d0401907548103041a911980c04207030602c2542c0e905503e08150060420105012545020f0241c460040c02042c0342d80000466034900030600d42004c00007241140f41d581c58410800041e114401150141403800071382c40403820000040703001900307126402240310341c2090006000d00401250300540140b040089550750039075500107a0721a8440c1c480c0a0b40002094001400300750014021944042d104001030b2a080d1208a03140d11a034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 338023390 1250 338022140 338022143
    0x61507021c080c072c070f05071b030302010f05010f0602070e09030c160303020f010c051c060f09021c0c081f0510080f070c020f04020c010603020901090212150a090c120603 76
    0x14004c0022008210410005c05000c0e68800c02d44102d0720b000d01e00a01250705024070f8404001d8002107080500c5107007070171100340222030b4484c200680d0b900e0500034007070a004034807c498203140400010701442422502c108807103458000e410f4040c6891014119420010051401804200100061143c041c0b0060701c41c103224002c04110340d41141030080c0b40c40342202070407071a030b03142010100040c0d4004050b200d80380400310490350094902d03c80200585410f030702c900084212401c020036140c800e03130003420410070120b02155805d00d40c0c0251000303843c42d200446001c0b2b4030040c0400d90b107140401840e14240f4480780c154550b00d40d02d4010501ca1a00000303141c000a40560a02201584101106030442d845142222070b0700403039000a00c0041c114444188500d600051540342c10000b90022070045400a02d0320200f036958600d1003004e0341c08120042a00269400000c07001e00305021110621500600303c0703150b01d402d04020b0310050030621001c80910041c2e403004040203030f8a009510196 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 338024640 1250 338023390 338023409
    0x908070806040318061713140d030c080610051b030309030a030c0e0a230d050312010b071104090f020402030a0b01030605150316110307030206061507021c080c07 71
    0x20302d071504004000c1407042100c8960320b6909001000f40c168413403160400051039040c50145919076204a147c10905030000602070300c03040d001448101404100078115840c1900d0602110200e41d00c1102d00603c21100250b00c10749402500383d007503100300007400c40304415941a0032a242c100c9181e030300d9604100c58441035a0303c00242c210049503d80600301d00242c4e18103001c4004518a40010002c2420b0f004035082039500003002004907042c84929540103201a10310030194046040c880d449034044034410054400c0000000707001203107101107540458125284014035010030b001c00001d00100b880075625038048020080160380e03148021801031580f01130020341c00d803c90300058166515940694070031506090f0340d440c0c1c01190000c40c0d6002940b041c140c1c10500a402040d01c03051902c2000344410310000c1410410036400081890040b0002c42d01084052007100b01030380355100d8420000d40000004404403130342c070a4050300c20781d46441209564144a0a2540070740352403455130000d01034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 338025890 1250 338024640 338024653
    0x7050303040201200a061515020a1209051509060d02031513020408030906070f08040b25020a0e06011419110604020603010509070513090e0c0a0501020606060a09080708 74
    0x110760308000c520a0f1902110f8110285040c0d49010585420176a10040c003802c1c1ca80d6400c003a4841f811240c28080d181075005d8044805080c50001c0d0b407800307003007800c580700000340301c0610103207029039400b00843d9070041c4405039492555081e101513070401c41e03205401100034002c4c00040b03080390000d1485441000030700c41440c08024208000405070050410286104000a22081e01d02004460301c01d08283d811039920005440e0450600c0a40140540000400308020641d0f41e1000d0041c101c54044170309400702031036650b42c040341c014460304d00290320652400d010405501960003003640020141810004100c00480740440c0354011409520780c3c1c41184c01105540340c01101d4548034401040041102d40340c03590121304148410301030640720300018400210014170880803145443c110080c5084201d40c0c1d40b01d03c034041d020024250b4064080d030600200d40d0f0074035600300b400300d4005034002e08007500c4181c00d00c2410303800b011384402040850400031802e61001c001d02801840c081008200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 338027140 1250 338025890 338025893
    0x60d031b0c170d030506090604090c030f0f0308070f1b03120606110f03120109020306060708130509010b0909011e1e0302041104030b0103021012050f01060f03020f1606110705030304 80
    0x14616515520303c181490b010921a103903c2d080401ca0703000d20191340010f9010341134241041e141d402c1d0b43c00206403800c1c42107410100902d0100e10400c8510a4030380840c281c0301c00390300756640b20103210000c00051500c0246100c8200c2040040c00603402400d109401c5003520024600396540354000602040f10303100684c5070903104218200100c3c3d102c9001e9420000a003a0b0a01400300c18420400e506801202041c0c499a50782c0480c2d0000e03078000c0303c0507074413114062414007a40c0240300e498481d80c141400050082c0540c0201c1d02c2d00180100101d00903802c0004044078456850044010511a42c41c086079130909517030980c000a004148814050b4030313502c10003098526805030451170400620003080003510f1100a181500d5040325203945100000070200e89a41c1c50004ca80780d011b00344014840300b1850305410360305942d110355440760b17031403030b000003e070103a00c50480302c030452001c1049402c82001c04890146000d503c1120080f88500750000f2114054003d0b800c2980e103900f00100f03120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 338028390 1250 338027140 338027143
    0x3050a0b061e011413080601060908011a0102030306090a0e0708150108010606120b0d1a04030807050f1b0f0303040b1009060b07020d110a06020a0614060d031b0c17 72
    0x24105503842c0305503981502440020999040711280c1031806001044038080000c44130407840c081c103098001c6448030b60391800e00a003140a903101720785482d40707450a030b00840c54554860703004025042e002545503440340d50910480f84401400803803259960305d8540c1580c407043c44000020300c010402842c549001a800119541c0d042e40710180680c50003800b0003d4a40254040f410104140c0000a5107180714005c140c1140110384018a030506101007410982c0744021240c2c022402556032640d10b582e6154144c03058030401e007060000c05c0d42840500c010f01c885a10f0b0b05050448041610313203880810071070525581041d1421250400c1036020000028155040c0b24010300255105100452030042d2500c070b64410444083c0c0034000805c01e50061042502c1c4075410040c010304403204660392120002d485401035041103446500b400c00e2031140b00304400d0b40c01c1c0582d8000f00400c16042c050340e000d45450038001894001d81200c3c805240c042030400c03500ca0300501049890303040c6d0300c1d410144075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 338029640 1250 338028390 338028409
    0x1080f1006030308042004051006021603170d0204150503180a0f171606061811090906120d030606110307030906081f080a0c05060301270603050a0b06 66
    0x800d005203403803410004254010303485500310f600300c1c0710542ca440350f40e00a080a5028031905681050418051001013100044103008403440e80e0b082d55084442e0301c0c014001d44103203107c05802041c0c0a00100140d445410040801c140070007030042c41e0513640c2c00c0a107aa1140802010013291000c4108070368a1580c2c10b075100d038844550702501030004030341e540008411100da8041c11012007004040340c81c0301c002d0110382c0504a2020241d500f40024540f6901926441c0541c40c003000f50b683c54002440380a02400102c80240d00106e81440c2c080d90a000b0449002000f00c2d9020003809481203030001c00f030003c101248800d5402040d5241060809071082c40d0841249102d540200005004264003401184c2904c025240024480e11615048207560201464607801111180000226050300141e0300d01035501c5050072405c229500d44c1004480c3c0000d20510740d118985d560751103441210019007a0709111864400600623071030391546850016407540c01c80b8180d001c4000c0c4015131901da0440c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 338030890 1250 338029640 338029663
    0x1b08061e0601021c03022a0a110102010902011d01020114010f030201081305031806130801061e05030a0f060207060603060902010e040c0e01050309010e030a02031801080f1302031501080f 82
    0xa002290000440969040c0f0b0184800201507000c50361507d44003d03a81ba4902503440c11880017010002131103000e4903089407400840d4004034540035203060f075006001d60031140b90140c41d048045800a4425207500c2403119009046558460b203100c5102c01c641c403154042c24840c441c6599990851001500b0900d01a2106d08444042081c101c0000c3e000005c0310025580070b0710310b058000704a004070381c0318042c2c24090400f41c40c40030408036194205600180480700804e00700403032000c0e04011043e9550131401140e4060700b150070000c0128201011154203140324070001840d208040c0c07600b0013241c44030f40007150081d499002c0d01c070541d03a0040d24800b9a40c0700303c6003081032414800018001303c5062110074140000800080e80c000000c0d4030205003003910b58156270b51042090b40c000e450340d010032420100c08501c1861440c0e5940b00c1c4281500c20105258007a00710b0311040300018803140c69030001c80e07162003151001d41e2800c7c2001c5040d8000c2a81000a11540340c041c8041d41c24041c034040c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 338032140 1250 338030890 338030893
    0x60c1615090e06220f110d0b06030603070b0307050d0c050405040f14070309150203090c090109110d02070602130b04140405041a040206040320010305070e0d1b08061e060102 76
    0x5004040d075400c0c40c0d032008141404803841d0881000382e00000a018006206854280741103d41b051030500000100f0315540102005c0154896440400240b4001590380580507480303014240000d4005000454101019041c007500341381c800a00e80c025101c0060401c400124041020025414580a035600020110005210b10b00c0c1c0503d000220780c4004224200b01902c0e5100346040c003d0180044030000c6070240195900d152440f0620f94a00402c5a0315004010300b1000080302101803050140b1000941e40141c5820700c20500d140194011520540d14550b081103907100c0030141c404180b000703201d40a04e450b2220300d814094402801c5c0c00e26a0341c051410030040000007501c0e24042103200c55410800a81916980041800340c0980d800c014030302d51120007142c0c503078020350340300c008080c0c426a800d206a5603220400ca81c401c990905181d0866108042e07400041c551580c203071402031616001080c0142e8688074189400b0003900c0025128401c0c1034406c220a0740b41c0e03040e0764810030070700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 338033390 1250 338032140 338032169
    0x2070b090607020c0108060f0a0f050f15044a15010203040315110310330e0103110a03061419060809071d07021507050702060c161509 59
    0x50041d491300590a1900d04025590700010000d40d6000c0282da840c3c80c028000b14038003a168242400340d91217501450f40309003030f0031500350030f41e1520448542156149014540c10305207440e078540c08008070102c03560082402c0c008582015400c8401f0340220280000030403042036020342c84c21420550107402e02c2048030566070141d9607030f40c000040f01c00f1280d10000e4440510541252040249040003a5441c80c00c5c0000c1400300d240071140d401000d680d03402c95100c04400d001c5401c1d20700c00300041c0750300d40050040d0700c0750402c0030f0040303043c00403454041c1800300d10002d11142040e1a80e03c030203120b60110b55a058103006d0380150704c00d5030340302000540314a41030350204440c044000d20544100d2042210400010b11440b406003c110010000392451224040d10404040c4400c0c104990b900010320406400d00c400c004194070b05070003074000d6241c89180506c0c075000c2c400168450700c4441160301c10455071188030210900d0b020000c01091045858030000401c1c003c003030711400d174004191030790b903407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 338034640 1250 338033390 338033401
    0x7030c14090a0315090807050f1005061c050f0d170c0307091a0702030a030504211104020c0f07082a0a050418060c030203010f0e0408070822080102070b0906 69
    0x20b80702c4003a070781c0014102606820800800c005400141001000410f0208041041240000380703505080b01c1c2505a901d662440c00240040340d074202c848a41c0721039078410340c411540c2c0c0340c09564201405a401c0d25010b20271324400340d20304200110703a640000d00800c92221200100f82c2c0c070a03002403411080700c0c511304040100405850083c0509202c00c02c80140b90519054101d0860340402e03400340c2503a980c3d600720704006d041a0001d00c240c18828074507200e80e00302e00640e814100855070f404038410703c000c60f5580034800250040c1e0f81000843c4903c00415104c01020001d510090094074002d0540030407a20348019100c0c1001c00b090121501800c02c0c8800ba5a01403a01c001d9071340030307200044c10980719907142e40540080180986401d280440003100c103680760300190b05880444901d80c00c45603072002d15030070041080318050080e103028003620740010280c8000701846d0100e40408500c041030080e00300409400d0f5880f91300543c0d800070300e0000b0441eaa0003003030351000900c0003400161810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 338035890 1250 338034640 338034649
    0x2030a030e01090f060509040c02031201030b10030f05210705060105010c0c1e060e0f0112020d06030b19050106030b0d0615090f0e251202060d0507030c1409 69
    0x20080040920000c0e6918030040d920031060003000b00105003ca20340c3c59980e140181140d4080306005000c0ca00b0070002c0c04d400c0d40008212940030480001e103100603031a6840d5031810300b0026119230300340030a9600002c046100d25039840c020718041e0740540061006440c0317020b10351010740039070000c09000340003c4003c40c3c8082600790440f8000e0900404c803c50340e02d40b4032072100b504c0e041108402d41d5461080304002404c4040010380c0c52544500000c8200401002840d00301c074018180007078040c1e10f898050540a8024100c468040715000c5569600c80e40e0b02c100461046500d14501d0070001d0200c0c801006c603001d401d0062405050401600000001041c0c14040c4d0041c003420507030300d03500d00c091041c02030303814800242202c1004210b05107400d6240d4000d80300a850000031031180a40d079100182f450503240000710065900112201e151005c040c00700d0058a800f40e074407103800e002200540a190203003502c290b0103030703400160030342090b00040d00100b24805034814a1505100c2500315484 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 338037140 1250 338035890 338035903
    0x6030311010f1104140105070f120f0504080318060702180f0c07021315030204061e170618010e0a0b010510030c0e010c0501090f030215070f120c020102160b06030f0a0203 75
    0x10b26582280305141c5d10011f880520501100400f4107003030185000910141c1141c61a4140080e0f4809080c5d540c0354004032140e004900450880e6001046010650819140c40220004000d801c060030000d00e40c0000c1c031050343c0540555259a604010000449184046d542d4000301c460107007400c0110b69004100c035128403400a02407150340d00180d008076076020ba5614000d50340203100b03114481e220101031100c8068040d284040034107220300412445e110145e90907030203440d070b001007850380d45038005000001500c200c00c1c4559543c801c0014400601417003410100c50040000c1880f9501d0705062014404c0c0446041c0c0805107410300320328113144d00c071042c150340001c00d00c0c00c1c03400c5045508001e070040101d000002c00c54006d602d081e4040540105403042c020407502ca5018547d81c3c2e0f0001903a029580140e283e0003d80407110881502c091075004200500e0288001810b00f034585482c12081c03440300e42c042d5424681c420402c0124501007109003001c998a1001e041d2200c01784c1e0210750b5400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 338038390 1250 338037140 338037149
    0xa110a0f030804150e010e150f04020d02010c120504030309060e030a03032d0f0606020a050d081503031803280f0303021207050c01062c0c0d06030311010f1104 70
    0x90480200e018415100340d80010200e51041c200100703c40607080600900341d59100b00c1031809a010201408030f0032348600b61140d072200380c6404440ea40c0d0b40c03c1180540c0c149000300d05100d00c014027a0302080e04007a018410184a450b10f6545070305505019040760042e84c046400c001016418506030784020481d81d89159050501040300d02c10302d401d00c01035002160156514181c00000b00b042e03040e19800c01c0303444c6405000d00700107150b00c901f812a22800001006030290f8004200401840c0c82040350300c0e80010304a05811400882400183c116409000031a01042c540c2c0e039000c1032460b0a02c98100ac0c0e200b0454081c24002040403994040303824010060b0070320001d0b600807414503009404540069040e10300080d41d9252243d000341c03050f001801040c0c40c1c3e41c609980414182c03070810307a044159440803031320050044414400d2140e210020010b03040b446c01409511302110003405007401071442902c4402084c60180740103407c6507012848000c084c0e040000d01c0c844400e4002c1200e0a54 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 338039640 1250 338038390 338038397
    0xf11030103060902190b3a06170a05030307110c10170108030309100207020604050d0f1a0408030f100509090a1110140708070f060b240415170901020a110a0f03 70
    0x4540c10518145c42c401800015400003507c0070b01c2e81c0003140c903505c1030065498030000310b601d4159142000723a461540c41c500500c65802000410b101600540e02100000324031801c407108950301c0c002090500c1c1010b1182004900340d05014120000c0156090f809421039030000c50071031401c00307142e658130000d10106d44807030b560005000056403510b00c2280d001c2c3c200600300e040e00b0810741c81d1501181103284010751319440c0300200012260f105001240c059a00600c8160440d1541e50301c05c0d0340510041d00340395136890100000a034686a030000c4038414140c0c500500202440c6003484440301e0903540d03a1034030812555818080c25500116030ba52440681441140c4441003403810754010700c2100009007540ca0040e80503001c1210a80040300806801e803213065070304403803050303006500e202d100580b03040030000d100c2030001d039580d402100c1340302060380340803000c161a44040070340701d0200307440100c0c661350001042070003a508074490102401d0818014428a01d6603119074051070103502004040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 338040890 1250 338039640 338039677
    0x308070f08061c020d1a01030317010e15040213031b0644100302040c031509020319020f0301050406080706170a0f0c0e09061207090f11030103060902190b 68
    0x19501d9030190030170f109501c00711700c0b10380010801190030541401d01c070440014404c044048103030546100c1e140d0484030300d0032014030140c07100c1003010040400c40142c96005a82404400700030400310090000035030040f0700381001074052015107110b00041c1e4219405214110f10804002030228032411079040d41100030401c0c50728044400f2429045805080544600c5002404610351414000104603031088404001a6801c00300640907036031581181401c0c4100000304100c0200150005c661002c0200540e0f461140b050b030030300e000c0303030002e003610104135401100601c00e609003803003400c001e00100c1000b000320741d180140c0184200a90280c01d004921304501183d48079245030080d840b2002c6440382030021050a0390000c100d0380401c981d840c480c0440401140442c01c00d040006114a40d1002421845080c0044c00d00a88616150201c560f039031401d130104050410310256020717610400012070b17401c038540104441c0c4645a549000405030180c4200201840381e03040b1078910302c001c0084040b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 338042140 1250 338040890 338040893
    0x50f0f040e0d020607120b1309051f05010906090212160207050916020d230c03070804150207060503161805030706031e060303051e0f070308070f08061c 67
    0x2038071a05a041400740708071526418140c0d0082a4507124215969400080985074240c000640d04600f0380780c0c1d0000441528450040fa56070080c4421501071f20441702c07003040407541221580540d42202075080c2ea50300041c0310410450013040008c0c04d4114003941400c0300300e05584290f01e0060040c448448000651142c0349000b400380700005c00c0014004011840d00b86850350003400040034150050140c4c00101808038062100c003c500c04c0d03a0000e00350392400c101c1069016500c2419898124032061280c20300003082c0c24010000750008100401100c8461500646401143d80090b41840414010018256000c4d2010f010a011901c5e01d1080303074064070712140d0f142081e5001590036000f035000125010340c142e04600c1e00807841d402005031a181c2c01413490110b03955404014009201001400048000e042d01c07000c20f10004040c803407034003c503030500c1e11055005060483c041900c8204100d081034101416500310340542c10f11450624100c00002c1503034513140540c4407011241d803504030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 338043390 1250 338042140 338042149
    0xc08010b0903120d1e0903141e030f041110080a0c03020c010914071d0402060711031005070f0c02152208010b0a14090c0c0a0206030906010f0b04030803132406030303050907050f0f 79
    0x43e8949048003296603410500c80bc0300c0059012241620081d00d42e00950115060659255624003555034071424142c0b00d008050307029003091914001055001d0004039480700c3d0a200f00b48c0c0080c4500d10000d1420320880c04103042602e50381c4119030000400b00300410301540780c40042c0e03000c0d50459400d42c1d40e06031440e0200c200007651001a8243c4109006200301859070b40c019401200d1944555006e00d4080c40211528401c411009400000c2c840701a4080440d00d4050003004030700c0b142000fa140400b01c1e0714503000741994401582a91100202081d03418022080d0307024010020424000300d5610f000f20302c5030382d8040c080b15099100001c46402c02e00080c0000d0811030b41c0100560f542e0b042180da800d5580d242805452941c0000443c0010805440d2044404899111460509694600c09181540142d207802034420030b8860b8551840e440d1513408410403080340d0440051803a0545c1401422100000c14850703040c0c1c400c840c140304d550b98080100704204821107003105c42c14914000b08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 338044640 1250 338043390 338043427
    0x3091005040b07060605150405030c090402040e0303040b0a0f02070f0f06021b03040504050604050415150302040e010e0c400903170702010c08010b0903120d1e090314 73
    0x1082c00400814400100300154100a003124011030300d41203408603500181204e4800d074490503501d41d024220700c05d00c3d81400382140c0d50040c0014000210745039606006070443d4001c0301c0072248a08244100300d480c005600c50030ba04070000200850526030199690355900312140800782c44c0540c40800701e001c0143d03a4046455004000c03404252000410000e01c2d640d41050117002e12640c2003a0000740342e800c00d481003d200d10342003a00c03d002e0b4410701c4c1020004043d14928840d0044004002101580300c03070041c0c2c1c113904c098000010b410306c4045001c0e07081010024405200f66032070b1a200f84000503c03400b5481e0182c10040c00700fa00700c54074203140080c2004100340b15030581001d48850903d0340042428241c00c80120740c1c1029640c585004078200c4049089010109021900600c0804090340240040110150881c2c0201c140560b1805149e0400240b468005880b5000300c0261916054135040c0a80200c0062004c1445503401805161503e486140440d1010810046040503841030f03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 338045890 1250 338044640 338044649
    0x18060206153312060904080f0a0e030d050a020105060f01050d0b1f02030702011205040b15030a0209090f0706050c0d0806010c08040602060717040b012601060f06090e090309100504 79
    0x14250320084000d403078559000607800390415060300d400a44c0d02d080c24800300d4400c0342c1c8081c0d628503021288180c2d0300150001e091010812540700c03072440094400300701c918421030b4141c0324151140342c0710302c00a0a54400034012030180d5004080c2046698021041c1c404000300380300c01080d00c40e00400070801d54130551800301404007502079894040d40d0040b00070894dd82c000c1c0d84000c452200c1ca420340c1c0545505450040c08507480c140000c20700e01c81c44044a822000003000e03100190f5940d00010340400080c2ca4102c10350b00f261024500440c01088504014902c1c0d041142c1020720241c0b0582e20342604810105c188401540040c0b2a13030b200352103001c1c0d03c1e0340c008803d507299500e403d402543c0d140304680c1340010402c89880208031a101d5200140300b50351001e02c9006903824001d50720756480d11902014042040004017211404081c082e0b900505003915080000070300c0c0c02402021081d40303a10100c03101401c10184041240040201d4401d000c00b0f4070034240c982c02c0c22a044602c0d1046500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 338047140 1250 338045890 338045959
    0xf0e03160b07180e060105211006030b0a140f030f280b06010c060605030703050a02030d030b03062a04090f060e0601091211040603031806020615 64
    0x104084a0500e000099a189001d951140d03001d60b00c10300c0c2034034440080701da525000c0b00811020008509203001c2c0552007401850a41d0500420101c3c80e030a94140c011107003045050b41c420001006c0e4000314203401811286000d001d04e40e0124049084414940902c3ea644000d4060780c0c0e01701d8482000000341702c0d6024007240c010400c040d200c01d40350b00003164000c090744001080c4142d48e0781800410003015030845200c0d4032544131000191111801610101c4089483c0c0100044540d02848820019070148001d02000d42c210310406003004507000548040c14078184610380701f601e000500c243d11035104d8415005180302e220380d001d0b05a81800c0008400c0c9400903001c1081036086d040406584c0041205106c015122010640034150484040d8006180c500080103100180d41c0847c0885020303880302d281082003034000c42c05495041e00240d01140b00515140e0345081041c180c41b0084c1032070310107031001307003400070150100301c0f58a001148101d6007211803040c2804151405130340700c121301d403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 338048390 1250 338047140 338047147
    0x30210050a020105060d080a11011b0909060e090a12120914060f040312021804140618070c06020901020f1c110105061011030f040b040905070e010c060f0e03 69
    0x1240202240d0201108070015420a40420340703e00340b000c00210041d03402400c060419031b1605045034040000100152550340701c01c4048041008202c101d0103042c20f035074035481c0c0d207810500701c0030540d4510b0f03009201c4041141c0810151040201c2c0c10151580c0c420380c5ca098601920740210303002030442082280c26460041301d0800c1142000c2e00e61b45140f1100c0c00c0e0341c5650360361000000008412a000b07070100d10307050143c1e01818046d07802001c59030891418201c1c41011030000c42c044900402c2c02ea40e03040310034010b00042d46000c0b0b41400d090803403421089540d10780400001c20307014080b8001080d468010441801c20780c000d110341803841c42e071a000c0b034605175074084114042d203409114001c007095200011060034001030041a104841c00742c0b04e43c2414031202c90072284203050900705000c170f00050140d2020660f44000800c0106054030074613880c0d6080124030021600040c0c102400e00032480f9040e100380e40c208070003441e00b40d044a00010f1982d42c10900d01301402100c19000712500000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 338049640 1250 338048390 338048419
    0x8070c060221181506010909020d0c030b152a0627010204050f090a140f04110405130b040206041511010608191b0f08010f0e0c060405090603070302 65
    0x50251401640b40210081042c1c407449104a0008001d007941c442541000b2604ca400d1668805002c2d080700041c540035240d00d0f621894617003207801501c0e168100d00d880da00900c440030303410b0080d507008403811141e880c00800841c2248075207104410f4241d07007004049218070b1034001ea05107044d04111044060310101e14207400f80d400c851458900c030a516540b942502450580e0510030b0f10180d0340003030150740c0702c100760804005411100034a00761240e91a1a0380170303005800c0a0055000e00b00070320742018542803500c8c2c05808800d9201285000b41d00c0e040800080c1130b80c1c0c85000d103582d5000250000f482d112800031403118411600700e15415951030800c516525400b00c2c90040700802c900081003a01e0700c40058641340c5a10400c60340b0660481d0f006003000c1001e283c0508a08ca030450800c030f0300036544400c0d001028126500a45a6964505c0c888030000b800d40280c40042c00d030140608001030700440000c826000340d01495025006000009845407000c002c0100610740041c1140103440c42e2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 338050890 1250 338049640 338049667
    0xe030f070e011403011d06060a14030c0105160f051b010f050d0504030e0303041d01140105040b030a0f050c040510030e060117010f020f091e0303121f0305060a0e070f0608070c0602 79
    0xa5070412700500042c0400a40b0316102d001400100078004c018241c1c10000c00011201074100f201610079512103510801d001543c10780001c04c0c4641301d4809000403002c1081c199108240d072a89150521800310900682079601270101c0c0c5000e038041d5400125910b450408441140d0b42a00c61609488000340100d080c40f03004041850241000107102d94583e00c807468016220707000040c13240402d005020610210300a03001641d4401040c2c10005061a01c40a00406881c0300341d802d0f21280c00001405d000c00d04150110400a51890400b4442c0ba400140c03542d41e241c1c030511035824424102403040c1c003000c000303400c185601d544450f070a5447d0040c2c001d045034181c4c800e0400302d01c00c0d171188200760004424020040e50100000f0041d50a000302240004403418004000c3c0c404000078510a810308410f1130050401743d801580206124502201e20310b081320a0311aa2079507581c40340e80104201c0c5051841c1c18144c030303600d241c1007500361903044003030f01ca4284404000305068000b0030800e200d00f00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 338052140 1250 338050890 338050903
    0xb0d06090f2411070807020d08190503160201090302070b0912100c090501180b031902030a09060501050d0b0105041505031002070204061203051909080a030e030f070e011403011d 78
    0x1900d010050301a282c6046070700341c414800c0081001c5c0c410b01000026103040c8546403c16409024401d281c40c081111980c1c80901c288120340200d87d0200a0205118800d40110400030b5540000c10000c40e56407006551070100340705d842c0000d0f00000780c14941d516100070502c0002404402c50364600c0e005d1482101400f440017005000a10440002030990f1040740d11015600c5250800d07000310341008402c0f013060748010880b0700c010801401c455a003074a0380c40158400c03540340800050a04030342c5080c5041c0c51041c1c0c44148030743e0480d501d0b42c022400e240e040904550342205d00164900e03070291860303080200d41c0d11042d03050090b41c0c1d03682c100380450f0b00204400f074400c49003000096290883d071944d40b11985809030000d04148608642c0d8210a0710050446502d41880c410866803072050071b04e410000201140000e079261002d10307503070404028103106444004040c0205d40e01380260200000d10504c60707500c0811003500c40f0001b80c2c5003035200000d1445810342d0072030030034140400c40d640d890 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 338053390 1250 338052140 338052203
    0x9040b22140c010c12120902060a05091329030709060e1b0322060b03011508122128021b010b1509010e120d0807030b0d06090f 56
    0x702e90030119658881c0c2d0302120080d40c018411585c9501210040700c0c81d0b0038041d1004901daa0b078041c81400740c0e0740c00d00030b08414100b50f60360303c1d5185038000910412a000c0b0f045002014203000e1b50039203100d00003403850121000040400005071803003001a20b0941c49510088a403898108041006000400c1c101e205000c40d2585941700c0f594190344030850301c8100d80c0012906427426080744134103203a4869580040c0544c0003c640f204605000900311003000c03607940907001010208000002040c010a00c00d8003004550301e003040190070700c0d1800380550044245d4801c581034001000f000499010459268841186050780381d04900ea1800a510581c070a841281840320040120a0140200c0b050340c54064054000940c0c00034080c2c003950099030759981403214034422900540c0b01e04180ca403404825800602000407280800b07070400c1005130281c01010304052201e02603448c0c0c000e840503800d90103000020100801e04160345801080e120040900441c400848140228200d0109840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 338054640 1250 338053390 338053393
    0xd0813031a0f060d0f06090c0b030601020d050c06012711090a080c010e040c0201021204050c0f0d03090320030f071a090919060510030c021b09040b2214 67
    0x50b11204280c1d24901d000b01c4410340c0c400e940001403800126094140c949542c03150b17001041d080726030380d2401c505144a0f004800c0884c00482080110b40e810410909004403508015143c01440402152220014000e040407480e00d1101c1908495425201c003050001103202049081c4d040140d2036003a62082241d244502503030704022801100c0480c011808500503150b403401624203005200182c00e0882e21b050a6540c2800b0304a4500003035039106200310320940160141017110b0b010070850381104486540104070300c20010700004d030096034079020f036900070505040401d502c2a0055441e11325196a40c1c0502031035594041e03100001a56000f0b8804180b4108016241454904d0050240484040d4000e8440c008149055805200c901f130109010070049030703547d01d8a002c9044041000c0c0b0341d60001e0799410104005640c18003040300a584214151a514076004001403440321002d40090104140c2401041008200a8400101134100300c10300306508200d080090b4003554601036458103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 338055890 1250 338054640 338054693
    0xf0715030f02040509150f0a0e090f0c010f0302070f08070f020f030105060d02061b0a0506070f0503071416060f020d111914040504060b0a030e0a110d081303 69
    0x1102a58003d0300d00380c601c003601c400c050303075940e0035400ca4003100400d5540c0c201c0c84901013071107940c46034801b4401620f081300c040401801c000e00824909480d804080c025500580c041407070340d85c0c1c40064024541c0b0b00c1e160140c1c030b07030a490505000002500ca8010f0a02c0000074011040080103907802c164140200d5025a91480c0b640626090322022980203030f0061901e1903850044c40c000015210710038407240d07144598000c00c0421850140500b2095501d03500c10b200b040826940701c582822001040d107040c0d4118203014402078804492200209206080450203440801b0813400c2d10345501e0708007c0a008100406099038000d512031a01d1030042404d141a914034000d1060485444105180d040611400006803ca602d9001d02c851003454034400c20001501c0d648600440f0064610001da8659405c0355410290480380040315945294102001060100d01c034420742507142c0c80150ad0900042441d850580c10b141b003011128500d070b58400601005111581003241e111904a9400c03142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 338057140 1250 338055890 338055911
    0x170a1415030c090105061e0c0a06050603160302030706050315041e06060206040803040b2e09060602061003080c0705040e010f11070503041214030a0e0102070f0e0105040b030f071503 80
    0x3c40d40c0240503c0d5007024040204900c980d0b04c0c800b8240302205000a61410030342450045030410003c050305851140c1c80702c051004914060143c4000c1c0b0f0088100300b032100d0f18543c0030a84900c0a07104900a010001c400601b160115010600750000011f1081004c2d0340c10841071440c6621140c00b1881c0c051510700013047c0f007400010081d0003190006409800c540e07031990b0300d40491030000c0072000046103c403504507030980013640301c1402164008580c201c440c00c1524480c103c88840d8011800c6520800520000391529481c0c0b0068036000300c00030740d5134071003100707041c0c5003a581e540030642007860002c0318003440c801940001c0038481202c4050011555030055004580141c3d0030113092074004000c00c001c5d40c2ca105001d05042441142e040e034202303034081c4865085070443c520b6100401c1046880304543e43e41480110080c207003490061151302c1c1404210032102e201405954019540c81c40301d1200c0344d400b00074030b0301c4a070030302e5080b00c10762910b50800d960f41d070740c07900c50340c50210741800550103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 338058390 1250 338057140 338057149
    0xf0308090f100b12060c1801050301060e0904051609021206010207060906050a03060b0301091a03060c0405010318050313180b010806010503101a0408061006170a1415030c 75
    0x205103004090042400034089104400100a0f982078283d214400e001d80c8080541d0034040d1301e2041004d421a5512401c1c81c0c00750404100001880303e041003c01c000510640380c202e02440d400381800d5922a0f4243e8a915049280c005c4065400780482c1c0700c035000146c00f403203540003884100e20303d01b0403400c00c0d202c003801a80d56140c94000d009c00b00c0e40143c420b0007440e01c40c1c00645011441490003140d120380e9900103600c254800c0e00f0901c1c109454050034400080c1d540e41641101c0c10075402890135151140c0900c0c13a0380030703500400d410142c80301c24020b00071490b085101e0103960401c007506d550b82001da030300308546c0c10715100f00504400084401400f00e60070b8468044c0250040c0c4808086944600c01143d1960000f40250340746007070b00c0d402003405810b4107520301e4a14580c000c800e90f038a06101015192190003041405042030740c10301480080d42c0b1003001c0d03014002d005900c4100f61030f281c101d1006041c41a250440000509003000f0031818000300f1191b03811416415608080300380c00c14070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 338059640 1250 338058390 338058403
    0xd0b03060c0a050a09091b0e0f1e01050408030d0b120a05030712053f0408070204050712090c05091f150e09040503030a051014100909090f030809 64
    0x50040c0207050050740c1915002c0d100410070074a461600d00307445c64030703800b20b40201da541c6658217404202c1c10403840b0003650010003501c0d60540403100c04481c0000c0800142c400c5d144c40000c0040c2100d6040c07040c0b52a40941e00756030240c104076007a07a0701c038440c0180b240c0081c60b032450710604c1403041710012000d420003c00d105000ea508403014625114980e02e955048090111400d000c00c0fa0070000803006051104c1d440d2486814202c0f07190b4403c01c4007141424040e0301e08411207003a54160184000180d8007405c448510754186c0d03010816a5450ba0305492009039001a00480350804500404015001e2452803e50b10204d03038072007981d01e0303081e03c0c081d081426003252000354001800600419801c00c05c1030401d07001528103032142040002c003180341c0788000e80d41210705034404400d01004a605004250b44101c5440000e6142d80c900014582c2c103100907440c49004000784541c00b4001442002100050503424009200d01101ca00c1c140300e14040d0075509500040c0407001045c540702000c00c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 338060890 1250 338059640 338059651
    0xc071701050f0408030f040f02030d02010c18050607060b0a050d0f1703060f040e100218040507050a02120702041413021318080903160e01061d01091403010e10020d0b0306 75
    0x2245c156600c0100d03401010b00003a00030b0300c002200d081103400603070701003042c5404421075038004511111841806020350181c4481010b010a0708181400345407122016640c2c400e4010300007044c03003600f46021030b0f25030580c0d400550700700f102810600c0901110014500300c80f8411000703000001d074a007a4100c0a4041540c18940c420140e40003041c00389401c0d049089480000f0701910441c0031030711464800ca911040d11103d000c0802d1020350324034500751141c2548104a42445440e04440c082d0080d1039084000c02e952507600701081060a5480c1d9500c13608001d100004200c08504108114107031a44040d10224803a0010015000a1a0f0300c0e004114801084019090558000d42c0d254151508020b06c2a5007520418048081000742c1d013034110000c1c801460a901c082d410510300804101c4a03148070000001038214032411664840c10b114100c0740c4806900410542c608002800341c0480d5403414100d10600707103070311904041c0350b00901c0c40030b44103c4204500c0051800340b54651703d04946 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 338062140 1250 338060890 338060903
    0x101401030930121404020409060e250f06200708070909230606010e030c09130203100614042408030306011112030105010c05030403060c05120705090f010f03020c071701050f04 77
    0x2c05e006003001d800001085125840c0400c25280e4070300780d5480e181500d20b4010710031b108003010540e1204c2210b9498064421182004402810500e0190040303c0794442c60b8500319520b07071a4420400c082c0861070103042c610056404250b07981200b9005400601d0040d43c64048209a4411985000003841355048050018210b2550351500564880c0c400918554142c0210202603001e96a03c0504510403c9201c0810003601d41c0ea0051600d88410700c80c40400b00da281c40d5050099003840c00140240c11001ca4010420401d405015804600c2c120712240f1902c4000202082564000c000b55120f0142030741d60000039180c070700103240d4900c0340440c22413510340200018007055104130780102d0390314045e50441c3e10749540c0e540c03600c08994070341c041c803c001200401c940c006400d004000e00d802500c43c4c038181e4104049a0b00007000741030700e950406d061001c2e00050050060194040d030b48003650343c0b02602c03003130750707588009000081403080c104107076500e0540003401503940d01c105540520381040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 338063390 1250 338062140 338062181
    0x8090c010c060b060d09080a02060f041505060105040305010c0908011116060b0d0813061421040623040203070b030709030803040507090204061710140103093012 71
    0x1100c0300000c3c80300c0303440140c01c024108007115a8001500070b24100d148a080c44503034540d6280c1000782408070280442108001c00c00a200c0450700c402c0c0c1248044d001c517400011640c80f001d0050311584103d500040c0725500700204200c4850308000044100d850302e03002030000000843e2003400c2e030304c10801c0c3d144141e40405040e00220b40d080c1c0c0003034000134000e082c142e41500c258803503403140e41080d030710404a051000b00501c100c0d0b034000240030102e5841c98201d400c01d60080b1101c1041c2400d43c0c600108000c2d000c000505006890f00412110140500403c40c80304a59000048082d030499080c0d000340f1880c0b07030000b141214882180d100f045c0e41d54801c5000c500316030b02c4100300c1c0c0c0041c0c02039403217104604002c10446100e1000300002c001b107465980d1b5107042100101190700c40203200e08600189500300300107480208440c101140c8017480d0004190302030b85030613980d0040d0040b07e1032703900ca600c0d036007071050004d183d00214440c04d003034880c0c503104515002c40a042e900d00c440e10010a00b40394 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 338064640 1250 338063390 338063393
    0x90d0308040c171f02040b07050d0306090204140603070c080d0b0f270a091a180703080306060706150605030612060108100b01032d06050405060d031b120302070308090c010c 76
    0x107503800c4440c4210f004c0140c5090740d40c80c03c8070566000b85005846540145100301c650a8261040e01c00900b4124820340c20070345015100b112030300c3d007062031b94007500c070000005840c2449141010240d80c2d010210b075440d645640059401002000704450040c00c2641d09046985800080070044140d03a52242040c4500054101e0f4501809405411b20710344480e90b6070b002405002040c00702404d0501c8126013450010140541c002c4040000c1c00260004030007400031481d502c04a9078420416641e440d9680c2140c40c140d002040e524100d081e008075600303000700c2d203030b9402001140146400c41c0d400f80c800100c0398102da200d10f02841421019031050072090041c0c810303500400c00900050500080c03454403d10050602c0317600805200d90711100c43e2200c603000d00c040c4540c00c0a0202613400308a903207011008102c5088280301e0103810b2041d400b4200010100b880622258680d0116640303c00f64074069000d00a0340100c0c6c012404940600c0000700d4500c2d00248004028805039680b0891715403a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 338065890 1250 338064640 338064673
    0x2d0103061116030203033c060109030c0f031110020a020108102103030e03040b040512010603080d020702030606010e0f0108070203300a0507080406020306030102090d0308040c17 78
    0x104038480341d03034402d0250b40144051540702c86a0b441c06900503658905d02400b19004400000c21440c0d5582c04413002c420342d98012040001048400b001c601803540c446500507100c0445543c001001c1111154000c00d4000c03032604854101c0b80b25132103803600200c104041090b11001c0030000da0041e441100e840015600c60700b4030b0b0350070010300c11000303d000e0b4035440c0c11081024400500440c2c0da01c0d003100201050f5240c40369030a0b41e4424800b550501d0b007014000f80aa104504c17605100300701001a004003c03d003940007000031980000415542d40c06002604080c0d0000102031f4441d00403040000c034954018207980d0782d00c22004040c034001249010054a40f04070180c029003c40c4010300211030760071030500a006d00c0708031030641004003001d40c115001c2c40f24002415492068140410b2101d4950852840d503000350f804080581c0301e0f920308010034024005c82c201135034820000d0760441c080c1500200494011406892000c0074240ca444030950401009031800c00c2c00d510400162500c000d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 338067140 1250 338065890 338065901
    0xf0603241b140d060608070809070602030412020411120433020d0e010e030d110405010906050c1515031e102a0504080d0c050a03111011032d010306 65
    0x209100100d05007502d40c0803d20803070326190080310200d2451014454130740c0d00b0800903a0b11005000c01040c149040480085d01c0c2d00803442030b990710280d20700c05402150707201d8201a01001e2065078085d2030b1000114a8201484251401c1d1180001c082403109543c50031107203280c05185490044007010002504400251f105c0c4902c0301c8103c0d5507031460141880c003070054070b2004910344010358036a40d41813a0503044070401e100000c0104000c00c0100302c02d0760440f40640803107a40703040954880c090a51a54104016142d0100201c00349800f0080b5191400441a48104059048414401d1100701c080c0800e802c1c25000c0c102c6e58402171518403c400c0540200740160740000e5041020030282140f511000f5003d6001408070700d0115052000b00000c20040c1070440d01458000403007000303900c1d96500e03100c050b40080c1c10080c001c1503144c4181e0303081021030719114480c0340c200030013404021041c14030740042e14641da60640502c20780c3c00e40300c0c80c0b1002c1c10703120702c0080800081d40d00e10f0703a40100500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 338068390 1250 338067140 338067167
    0x51c1404053001020903010c030501030203060105010e12030406080a0e01151e050409140c0a031104091703040c031203110f03250c0b010e0906190f0603241b 69
    0x150316030400e407004a842260104282c04900c00940c64400c07100415096401e2505210b082602d0300e801000981d400103100c5045640c20300b041307148404a0310100780071203410002914184000100000e1a030b81c001c0c100380c414810340388108811049210303100d080e07a054499200d07196003041018070804c41051040b4045c2c16030316501c100030750b41e00c00116042d266803ea050320804000c0c005103041d00303418418001d4030141140c09800d8141981e450301c0c020b0f003210668070f005e551342c0d0840d8001c001c003d200ca01035000c04407040684a01d82450181040310141c04125a0728605541e0080031500a02039600401c054405203400c0903c1d0070780d80e4100c1c0d000201100100c1d10700c01d42d0301c02910007041140c0f07040c80b1076580b003050740751041c00c249445c0b08040e48280c2c2168240b4040103000100032400c5034000a502e40c90300320140c00b8100c1c0f48081e00030720145483c0a491f000d000800c1240d03006c90524484c000c540b0102000800c845810b084404004005000039501110b10400c1d902c280b01030007406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 338069640 1250 338068390 338068429
    0x30c020102040906060801030c141c06090b01080a0311030a0c0f17210c03040305070605072a030e0402030c0403030507061119110a11151204051c140405 67
    0x9aa83c0000c6041d40c105602880c0030400f00d8005005003c008a4405d0260100b1038800c8502200d5801040d1410340c0829070050600720848007108000064000b169400e0b0001c60b0039001e541c41e455504e03201c1c05800b2045000c204003291207901b941e404020350360600c9803a00c0d9070724084819100c500900c1d00c03840048511a500c10f22401d45041600041c0c0202e0542103403200b6400d0307a00054043c00305010f0540c00510310203000f0800000e0b440011150032a510243c0445c040c1c40c0d103031095910080c1c0081c00710078081d802c045540c08142008855105034020350343d4040c1d413050402030000303d01c020740720403005280400c41480880e000d10001c2104904c83c04c2c0025014015600c0350305150040125070010740d6102202c07240c032035800700301d403514941d0490181c1a03949013039894101c003125002506010351080b044101544682c80113489107001c0491480d40e01c0e1400c0d20307040c1d4032801c81c00b0621500100400240704001c0c4180010051107600e8840c0c01d00c0c02d8208010000c51000c0300d000904036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 338070890 1250 338069640 338069647
    0xc0201020f030f040f0801020c070b0d1d010e010609090b010510020f0d170718090b0402040905040f05251a09060a030506040b060c03040302130207020d030c0b0c1801030c020102 78
    0x709002c100400c882c650410b8865241c0713003014100c50303420a9030351020748940e0060100f0841c04202244107422299501009960b503400207060380064600c46114608040a42045007000181900804044075501000b00081074641c581e06007100e0701b0840c00b13022003484500600040c28644a4610058803900440f10701c12151742c9030518280e44800040001070b05031031902250000ba010954005115040ca2420007000d0b08100720b503c1ea8621510301c5ca6a29000914410745903541114080d2604c40e206200070f1901e41007601180e0400c000c2200c4521800c03400e000800c080d0405800049280050300390400d01c2c01500c19401e040300e0500405101081181180954a0000510610707510340c030041000c0c94018100000c4522101d50302e40185003c1100070741c41d100110483c0c023920340c1104c1004007586901c400e18020301400c2c5009422a041c0c003071040c245a0420030140d8580d00c2164103030740035901c120110226000c0d80c8940340c5039811000c0022070035030080d0440b100d0035940c1d02c0010704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 338072140 1250 338070890 338070913
    0x304030b04051c0e010e0f0a12060e060112020d140c061209010507030507141e040305030c010605061602041e020d020c1207030f210504080301080d030605010f0c020102 74
    0xe031006440866840c3d12544620118025100c07000b4161641070500f88140d01900001034020308080b00d115220b0101d07206060300070740e40c940400024092640e40103441c44803e01d01800104400e441c407502a22640c000020041c3c40518100c003c0ca0740542205100d1801d9030b1010004e07640311030740b030307025025202c458459522050060003107c03001012044050800710100c0d421903502410400415043c07408208100d070b0058050401c0302e40076045c1655a6261000040d5100720805808010301300025001091050000107468181980c01c000c00c0705d10742e01ea040014502c681214062100c10140081000d8509a480a84107000760000585400030b640328190480e800601d010710301c15400710340d00c4800e0354100040042816510911031624049481c060f051068402c40042040500c12500da80b100740003400030441c516040050040d800c203460060144e0b0824040d115042c8a24603000c4004c500c41d008610494006855000660f01075140445041c104150264198810f0725400d20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 338073390 1250 338072140 338072153
    0xd0c05010b10050901030c0809030412080904020f0408060f1003020609061231022b08040f033f0c020a0f143705100e09010f0806150102030403 63
    0x1214890301c3e0391096030300e080c10000501281c2000f03001c0420081a007003004441c40d00002202c00b500d80b001340c051120503c2d86031608242c1b10b03500714207030000e0010680078840c1443e18042d1060303c000030151944ea030390300e02c0c5404d140c3d0812145d801400c03204100400241c1000d60041010400203802145005034600c0107040500b41511141814260b450034440d04004e00e4a01104420983c62001d8914000d50009000207a560045040000c40004101e029181c1412035440c00c2d0342c040603540e10742d5a10302c0064004c07685448195100c03c50b00300900302034a01e100e003403086009500f14003001011a28000d41004070300c1480c40051265000316180560785000e5008003d05904043d04e201d1410700300038900c5010034500603801510565820031072015103c900c041c240c400480003003207009003c6800f40080c2c610b076101a4110303900705400041c0640c0801301d1414030341d0035640408140d0b42d901d082c14190b417003403052030102c0e00201701195100b44020000c284409052046034109910f949528 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 338074640 1250 338073390 338073409
    0x6022107060920030c0d150203100806090a11041118190b0c19020904060e0309040f0b01030b01140d090c03020907050a0206100f1202010201090b07030b01020708010507020d0c05010b 80
    0x24841c0401a03c40c2030075500d401c00c005242c445040d20b282d0150b50407030baa6041d6000310019401c503108d401000059030340c0c1e00412210020005101100d4071420070810698854243d520f064900c0d0b0a41d91680701a42000e001c4c0000c10600031000e5450607900003580d0000d980711007942c0307501c14a0020b41c1720f00001904682130140403445462541c4064003102d00c4e1804075104c060006e5141c0f150742c0000560b032000c190303a5000d40c00200c04078200a0300142241540b0416101d0395206141c0480d00c07490b800b00364000480000281c8003048ac0182500043d5401c2d0103606450722a144100303d8842c0c10310040d040425018031841c50750140a07100d40c0080c0340000100e845500113000422113608a03681005500e800c51801034500e41441d0510600000268007030040e0b221907100401c00340110f910175032180072a00d4002c0303249111070903c40c0000b07000c1c1c422a0b04050042c410f2000115190030103104190141840d81c008158009c0310240c15200755809140640d120756841c40000700980304d10340311 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 338075890 1250 338074640 338074673
    0xe0d0806040e12040f0e0a090c0512030408060403080f0f0108031e040b0a02010b090a0204120320070306201908040311010504060207020103060e091b0f0316030309060221070609 78
    0x345c4410b81030401c42d2003e440001c040d04072040c00e001d410004520320884020a80700151a50070f0210004419245180b0075a4854215032207040d0030041819401807509009055031100c2d0070380350301d440c042c03420200400c0c000c048081e0400c0010f02d0304090000304a680300c036840001941440d54600003404590000b0789510090b0351500c0010400d454000c0806034030070030502086052a0030703d82022010000444010305204071401c0f0a079403050340c4c3c0d0700303882100400c004503144151039107000301c05014134ac041c4107004051026070715103290142c010b403503100843c4120101c1000030100106c45000010380164140701320401c01d001c4940c1d0a0141034440c42c010704c000b60740c4020510004040b2a015407008851801540a00100c0b95021902103001442100620710350f04246002441d0201d005001e60740c1882030499001043c0e032014a600c0840c0d00035101c1c00701c80c650700d107001d0341c4900400c0002001800300c2d400082562013914041e0040a0040e000060700c518540d642401d1480350a95 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 338077140 1250 338075890 338075909
    0x601020a0f050120030c0d021312061406010228021c141c020a02090612010f0603050f210c0111120a0c110703031b240e0d0806040e1204 60
    0x1548103140000c0c0251328210000214040c590b03d400d21a070701d902c0c041c0d101e0003840150009a10000d041720300e117100c4007801200361076050801291415034020000501c440c1c2c40007880070700140e51036001080310380f0b41c4d403480044003500e015081c82070034a03040981e0080f6841501c4482a400c15103035841540c1c403043c030030a00b01c0e258804546050b498011841030300f005d860024004280c0c000e50202e00105856810348540311981c84090000f0320041c80740c01036410b1586410002d401041e0340d900101c0449014000ba640d0040c0406142510b03441403c00030a845131007250415884e900400052820203188400084c0e48510114140c1b030b60742c0b00c40341d41030501d14a0030901034006424403a140b06181e2a041103c414940c550006449250611020f010300108507041110600340f40048070015a20a4016900c481c40203110507035030492005528032546441c5070b05a04690004282c0c0303031401951290540c540d200c1c01044040d200ca90300500040c0541108040200410805800500420070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 338078390 1250 338077140 338077151
    0x20d050a03020f0705030c010f1101060911040501080a050103050a120e030313140a08060106180305060702061f0b1207020a0605180d08010b03040210020703080f09090c1e030601020a0f0501 83
    0x7003c245020121340019209811802403644582e80100f1305200281c01404c00f00c800c400d0b488102c5005200315440b5411076410060701c15400c0c0c8404004000350342007622841a1921684105002c40e082404002d11641c840500d1002140700502d120721103e11600c2c00c26140100100883c0c1143c01075a00c4220044516905100043c0008801e00c110315043d44c03a500d80e9880d07c0340c641c3c1e8429043c4102820b004603603170300c1860362510601c01e001940c2c00c41e048a0503818480300c02035484c8011a901d00b41161081103815032007066121500440b51a6101d003803c051414050a0548801415102c1035201d001398820020700c45010720340c8148040f080c51074017040d00100007401e1002101c1c1110030040d400005000108440c1c3c00e0303a42080c0c054800d40406a0800d02c241e01d800d41a0b040541400030200b16001d198a03108003c0141d2282a80c84460756201c2d0203558805002d008440b850741d2001842450800780100003866000703105104503211a12940c132403240c40f061480c0c041e01e869464a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 338079640 1250 338078390 338078413
    0x507090912120b0109060311040f0f14030d210e010c1d0301090b040803040c030b0a051e0601081302130f0203090118021503100f060f110c011b020d050a0302 69
    0x1400701501d801d079010500840c1e10f1100000d01c030381722a004000c1419030703400142030440e90540039540a841440c9a540c801030300c803071040e03005010074030403404200b40031a0841140e00340420200c0c020201501d40c2c80d0f944003e000b0130150f030151100c0c40c00105036a0410100c1c00d110034051007826a40c1d580341c00004c00c0c10196121031042c511036040380213a05001d4410000341e01e54212aa10507045601680c45c0c1e180c500d00b0a2880d60710380e101078400641c42d01800811041640b000780901130a0400e03540c024022070240c400c0240031901a0b0100700d5401c0081c84050b601c03075246505610050004600107501d17120386007140c400020659055a01004006000d402441544100031980c01c1d1000184081c0c0c1c0010101d000710107030220010340200100c1c8000700ca03050910007a101811100301010b0700c8150041444521144c0b42002411080600e0b00300c48000c00c116403551410380d9242401c101c0d00500a0711511801c4080340c124aa180030007000c10000e001c500b401e0791280d406883e9901c0403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 338080890 1250 338079640 338079647
    0xa091406060c1e01021210062d03020304110303030a09020a080c03070302120c030a0f0320060a0c1218020a09050112140f070b03010f0915030f0507090912 68
    0x8103610701441d07041207201c00b00d5a000503040c500c0803407405064446610003400301d029000386105440d50700540000c0c0400b0002d04d0300914161211550b400d1405110103044898602c00da0482008502210050401d2a03201e50011680036001e03416504d00c600c801d40c08285180d1003100e045040540c1c8201d4081149041c0342c08100070147c0070000c0811000f1030300020b8848640e480000d105211008440b034203500c00340034061080e0401401c0e18009001810080c1a190346c0c88001c5000031910a001c0d80404107030b000c41c10010740d011000742940e40d1081c4182c0e004042036800e060134080c000703545e03444208aa00915000c0a40c0c210900c021144c14410300c9240c1c0c10346e8004210b4a4207003001403214100d09000520001d402100c00e40401e60b62122071810302c0301c030000380281c6000f004000b1418400d00c00045040361890103030030400c02d5542007800100c4030201680c004d01e40a03440200040340602301c00c100264040e04c1038032000307580c8040800403550701e0700013200d131340b25003444640900f0740 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 338082140 1250 338080890 338080931
    0xc010207090e0303270106030507050f09100509070207030b090f120403050a0320010e06070813030503180309270705040e1303030f090503090f06041802090d020a09 72
    0x5014014000c0b5201402c2d22404010140300381300a44c403c400d41300da4a4100403d1082c0303140402000003d44a0074116152040c60140c0303030050b41c0c0c610b0034100b80c1c00c00c3c0105c03074440d0442540344001e890908082000350080030b86000c0452060703400100c0410300488013a400741c8035030030041041c240246092030400c10940c0f82914914010b0000f0030103e480400c6401001e40d03d440d000412441065491055600400000303c2c7c6600e448079041074842c0025038940205001d48072652281d507507098424651140c0c030350040010b0000d00105070352800031282610086640000d03a401c040300400400d003001c03140c40e012034640c0d0009802e2810440c0c3d4040041d004100342c0341c002d203000d0070414405500c0300081c00c803200c07001ca95020300c4140b500c81c1c2d04c1500c1d20883c00c07101b400200700b6810881d940b40c001e00d041d42e22910b46e241d00e0780b1140c500101100c0c00c80b00c043c082080784040701c403030100080d00010904e94019084507035000050351220b0704400903184400c3c00150940000c50202001e10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 338083390 1250 338082140 338082149
    0x30c07050a0e0103080301060c02012a0b150f010c021f02060f010803190f020a05011109190302090f0901150b070501050f0402060906070501021303050102190212181f020c010207 78
    0xc02c40c200600109000300100c1b03064038801d0030300701d14048041c8012500b1406c031800690341020044401500100c3c0d01c10101e02310b41c028004045140c640c41343e0a003400401c0240340d54001c00769204098a94000d14001d10494002400884100285d22200e040000b40c400d6500058005208010741d551114a0036800340c14030384010360030591070312024000210482080c00900003020ba41858441c420400814000c0d0310400a04c001c15500d507041312030380c002040c680c5c86145940ca41c40d28021304035081c081181e8004040080545840c0e16400c0940c1001d007071001c81d9501c48844041c2c1c0d4070341c56190720080021000260313407040e03035041c55401c4400290002078555140420311000d6a1060269402c07040215002582c1e43e18511b044c2c0d0091042c05410348603d030030084008248001035016218041c101e440200381840d540c2000c0743c641300c580d1200401038009001401c41801c500e00d420706003d6010345480f10308050031004c148030621640c0d215005030300981d0022600d50b41803007084001c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 338084640 1250 338083390 338083409
    0x9051504050a02010e03160b181912020d1e03030506041b050a030213030c030501050919120918151203173304060b04050d0f020111030c07050a 63
    0x6003455501c0c16101c11036100040e040101c0e000c81006559024031201d0051500c82c204113840725034070052450280c02040e44042e040c415020040440d060140801180500c0c1d0580041c1590a01d02c0700c01c000c0d150580e040e604001501000000600d2201459100304042420056198003902e40107090f14002402d0900460521300c41000d03482c912448074a1318140c1e4100940c464402c420121f000340a201a00c022032180b8000000c1070207440e040440960703002704000d0240b551360301407880d40c48920f54443d8501490100042000c182841c1081d9100c54a03032a0286540d943d4002c03810000d4803007070740c00007016a204030280c90000380c020090b00401600851000300e44550b10050320b04800c014004051546110000301c0c0381d14038201d00d00e05d00c5c120b00c4001c60310407086e246821600c581c951047d4080c600d00080422858142c2042d10f0031280001c095070098451941c40034028140c0240032414022000c0c0d540710103020910103406114480c00045c02c030245400d08000000826501a0401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 338085890 1250 338084640 338084683
    0x50c0d030b0a21020d0303180b040203010f0b0306220204020f03150f10080405070506030103030801140a0b070201050a09170102090f060a090626010906092315010e03010e010905 78
    0x1280300c00d0f815800c4aa8044441c0909030650b81026009449015107088000681280820411545e00c90303a500560082c0c001f005401c070103280490880e200640300b03d0341a0b1101c1c00003000000c10562062844c3c8020102091440706640401d06a070040e881c120441ca00101c100005214640840c25003a00200c070307002c0525002e0000f040c0d00c4a0401520b804214100f80050140b0404001080c01084080c000540d80d6035a410010100103080c046d81e482500c031a061050785107010801c1314242c4549104081c5030418581c0155038661010080d02c0031f1101030310740040d13044402d12201071401d602030b00150b9120440010001e00c240b072164100e126403401e10540740c0c44c5901480000943c2c54600f0a02000f0000d07900d141014101c06000300d21180b5100d00104140381e66410480c100da41242042c4551400c8038002150900700c40000c1002015486c0040c1001d00154222071480c0d50604100102c1c0f2800c5002c00c0c255540c44a0348000382c3e4450780d110702006020454140c110300212805a02e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 338087140 1250 338085890 338085929
    0x301030302011a09150604030804030f05150c03010501050c161415070b06040203091c0f09050f0d030305060105040f0b030403020d2c121902030c04020a0e040903050c0d030b0a 77
    0x11202806004240001128145c18480f503c81b1422a005107420040c060349465907890712041c20880c6040403034540c0640700b420400d07000302681d001e00400c00c0b6020701d0305580c200001120903030001c0e200c1c0e120912a00c1210302c000403402d190080507140140254080c800c882e400e00040c03c0b22100049801082044200c001c80d4108111036044a011100540c2d070381c861074031291511150a10b90204080300001110034103030000034040c904181a11240c2c1f5265035081003210288013035071182d4014486070082000079205c1e41c0140d50010050410508042e00c0311103034240403125030069070050000105001c241a0100412071400540d458002209560052441070018011140c6030b40103000604011143d5522003016500d80c00b420108da11180c20400d111409142200007a03020303000707503c8071184034100350081341c4403645242c460038281c036661010701004040c0c41302c095040040030320800142600c1408a0000c0603056600460b004001070304000801030681d01c0b4408000c401c03030a525 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 338088390 1250 338087140 338087149
    0x30a05030105100c1203060f050105040503100507030e0f0307060b040e1e0a02120d030501170a020d17040b0a1d0a0b03070905030f010e1207171e0f0301030302011a 72
    0x2030558205a8104100201c83c690640ea00112428010010000c2c4507000d075a890b890341c011070448002c00003001041d96140d006407481c0c800c60250507090713004840d0000c0c0303c00040d00702e00d411143c3c1f4600040d194203c40c00c514103105c4018011102034200060220500846001c0c400414008440405c00750807115403499130349407413054109071842d201080000145c02030000ca82000d8015020381032500880c9481901c134294030b010000440c1c5054000310b03c03251540000c0350011034100080030350140030f130200f00454501c00c4084a416482e24200001d582c0480d020700b00a0039148420703620b985108c41c01600b11003a91500701c00c4410021000310b01c40d698100440101c076440e288080c1c1c0c0340c039800d104443c100d00c1e0380c100135010303c200c0040c511042c0b01540080e010151000550390007001d042060103c42c4508440078001190403080f13013081c904184000e004002c4c120071031004000e50036680e45d10315006440120b00b030400100041040c9502030042c0b08008002c42c640e040b4801d180d40005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 338089640 1250 338088390 338088397
    0x2101050f0d030c0606051f020f010903210b04241205060f070e10111603020f0603071b03021c0f020618010f0f060f1a030402010c02040914060414030a05 67
    0x7904210f40b039410b100901c04030b984200050200648102c1c950b0031410011080f039031141190b00014480c0440e40051884184101407500d44c2c19611400c4095040d0252404003403070400000750f0960750074540866584602c00c09441038082600e03c65082d08200910007030780711642c8840b040e400303028203c40004a001c00c230280d0158a041f1108030179281e80000329160351121502c5070300441180741c103d070950340160008104c3d030030482c1117030318804100c05d0542004041d0b120081d000082c0340b00d680d00c13602e048006190300c40c0d0300340b0300410841c212a8040c2010a0b0200e010fa025800811940c00380c49020094110b4008803828040f0f0350391802c0310002d680d03c038002c00d41600c000503034240d9010124213400c6403507000031900d4244203107134500d4100b100619041c41180103807800807000191000a10f40c010241000c08008035040d5030301ca40054415003642c00f03089038066a60712401001908011005240070b0703041c0c0c002e00c0300d85018a08600d00031002558100f080d8000d0145451203036100084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 338090890 1250 338089640 338089643
    0x70f0618031b061409010e01060506070309120602160f0507061b020108060a0503070b0c060a0e07030605130c0303020312092d0a050d0203072603040602070c08032101050f0d 76
    0x503280c9065942452401040042c44040c1c00140600c05c2c031071030031415003044403a50031200080110603520410420309101301240200840d680c5001005894044e21407030321901d003d08000342c42c0c1103040c3d801140c40c1c100e5040444400400040d00710078003400300305a40140031141013850004106040003016a50700920090400201c0000940f0036250750146800424002c0e0440e01c006480b0007500c03103160080c0156500750720034000054802c190743d000b04821f06015501400989007551030382400350800402e144034481d0006800c00c0040c00b48000d07500214003030b0340910346030344644070902000580075100320a1a0f11020b005110342c00b00c10440c80c0c0c1019400b400c0d884c0850040c00d00c6091450100001c1c00c40e00400910001640d0003000400c03c00b1721808401d41000c0104119400881c034001141412150604c0040c1c0090b410390700510f80b5900881020b400e01d65108081c0d8515480a07490740f032141078254089070300000840601e0701505080703d0f221000928100801c810001c840c20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 338092140 1250 338090890 338090927
    0x10e0102270904081b0f0607050c0105090c18071e1710080705010e0301140a090b1008030a0503130b04030e0a05030a02060a140c1501061416031404050402070f061803 73
    0x600741809481044071b628845a002c0581c0c40398500080050855044456a01000d50800000440c140008111140000c1000b8100744103400c900c407020700d41d8100104868244031500004001c204070882c105014900c40f642d460007600304ca03240350901c142c070140502c5404500c1241c103011030f8030042428003d4400c00c0c81c21210b00650100040d01400c8104003880d0303611001400c0c80410b40150f0806e40ba40703806086078000c1c503219412000044420380c4140b6210780c1007403020b55461842000116005541d000c5820300d0300d6410345554200138800e513011008541090f00c0005282001c14000d401030804070003070001841140c012510510030120090304001010000c0008001d0032010f80d12018519422505580144900828004401e000b803902180c14100e810f03a408402c5411610107124840c44000b04d8801d60b6416218280d00e205009845041070201050948840c4090110503005d00085002c5d030f425810302108484100340100d4508061611000c003003a0031400c00098034282c140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 338093390 1250 338092140 338092177
    0x161e05030f0d0e0d06050406050a0b0d03050a080408040905070e030d0c020102030f0328140c0403050a0f0804091401030c050d0201080c0c0a12050304061b0e0909010e010227090408 79
    0x4000404d600c02c1c11000509181c6404107100900007a82e110500c102074282080028801c403030100708030600f00100040c00104c04105400303446d8415508246c00500c1100d015003425254150700c020b0310070448107240064621042c444203841c040009a0960b02581494809a2400c0c1c00003501d0340318840c4c1c007640c1c004000000c10f082080324911414003002c42440e42409902140c92000130300036403140c1c0308500030781c607011031408080c44084030100ca0740040280294040c41e0307591202c500701018244c40c4a2402d1000003505e03110350160a509001241085d040c1c0c0d811464848030641d12508043d00a689003a10340d8010f0341c1003048a50800014142c031511107a0802c0011700c0e10b0300842c0002d0a9240d501b40010070741c0c2c0c0100245000324412035060004041c104031104000c8051609400020502500207a8508207074000e40d4008252400120301c4a00a20b0311609a074000c0e0301b03900c01d020b510321998885a4901800e000070180403109520b2274100790b103d8107420b002e61106400c0c0b244064 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 338094640 1250 338093390 338093417
    0x1302030c0405030106080a0c0b03100501030b040b131d0105150d0501090618031b0b0106030c0e0405090a02120d09210c0603060801110c10020c161e05030f0d 69
    0x40e036000b850300500900c0819203541c18152503402882080343c5141d104123001c5401b02e1302c4010b803489203c648a156240714070b040700450281c40940300c1d40d5005941c81101e0b0360162180425440414074401000c58104030405103031560050070003401207564074080a001d10001c410b5100ca490560403580301a6050850038658010300341740c40005c19061802d5400c0101c040c03518581c80201e4003a0310749400718101010341c0003e51203100d4009001880364801407285500990180d08090b4040c41e101c9001002640400c2c125041a24420042c0d4040741c070740002c524050ba031011800740d40a0140c500c0280320040604a01040d00038000010003400320160000180005006000d03005a142110141e840300081c004258500523050103501b02a03071002a404103e0445a000c005030000b403840c0c01c64802418025084288a035a2901035090f4001d01d84a00d122420041e00c94800c81c0506130f0b20503601032601d00f03039584c0020f020350041410380c034280340b0104044ca04214030342841c06141144 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 338095890 1250 338094640 338094661
    0x5120127080d1e05070c0309090f020405090f16020316170d050a061701150504020f09060c010e010501060f05070303050403090b040f08102904090b0f060f0609130203 73
    0x600b000490107503d00b001a40c0c071000306411000e0460380141003000540c072081e00c01c444844030b568000e00881c80050041001c2c0d80b06070f22000c040000380710014241912070300000c0074400107444442e2071343d010101f401444002013080c0d60903d101070008502c3c00e42e2241c103c44110004010103020055261461200310495000311001c1e040407401c100038501e084500300c00201000d0141005100058a028a582905100b0790f0303820342540c26268103107450441000007030342c011544001144000e003c4544280c8811000c1c162015041001080442d90711040c0750846005902c050100801d96910300704454008089968084e0980783c080f81940d04d500b001d40c0c0c14642d80e80824840c5800041c0048d4003203032131503042c0603a0403500c290350300c0c02d1900c0d000d5006c3c3d5122415070040e00402d100c28601c60481009030361080907000d0000304990343d4644401002d00030440740030004100060400c2542d10f07048003000086001161518100350020000c600c14940300110101029800404035461210 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 338097140 1250 338095890 338095897
    0x4030210052a1c1707020f030d18020301061d060d080a0c0f1b090e0312010b070609060606050309010b1203030a0b0f030a050a0309060804051005190509070512012708 73
    0x45080071244012229034001c010401d91201c40070700311521008918a54800301f11004403002c00d40040d42000105102c050040002c15110084504014104e20050300e0a018000080070ec030b0002c0001d500d00003085a100307440c018a501e10074a0f04001320f1300000d55180c1500c122100c01d103031401070004546003419900404ca4000303820108000c6084a40d404003001c00d106552402e2003e0009201034600340d9501d000d44000d105000303500b18014004690a80c000d06440e034061a00440c131503d960319010b00f251241d41014001407000410800480404d0042c401c1c060030940d000500c40000000007074036400080d10a0203100e4680c1c001d5201c0c1d9030307420030780e4000640040130754a000b000c0340381c51540e07050354003070031008200c1c0300c440000c2c07043c042d00d442840756801901070042c25840c40504002803400804144407504940210342c0713412114411203201c2e900700c1d0018801d032801c0c6000c00401d13286c4040220382c280c2c14031004151214851081c100d040090ba04015441c890600c3c01002602 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 338098390 1250 338097140 338097163
    0x801030b060d02040f05060f030615010e0a0f06090302011b050c13091e02040605030607050712140c0705280512030405090c03010603050708070503040b1b07060204030210052a 77
    0x1170824008115000e85039000e640194011220504200c0700c1005147d1118411200d014400d156034194000a5000d02e005602c0d0000051502d2061900c0704003028402d0354a0b007094000541c1313540180b086503040031250107000038034098001207400c0341c1d40b01640c403281c0d40c80131801007804007014000c000554000c03190903940548003044200c0b40100d20048004210011b0b4821030400000040702d081c0814000d0244040e5541d040ca40300c00307600d0b0000c9603141e44010340100280415246200607940e00981068401d403409041d003146000208035820382045400b04010001c5840c02e100b40364410010012140142e5000c00340500940c0d001d429070046500c450340205202041050b05100340c1c000b5811380703070607072401c1096858494044400040846024000c688100003250100f0000040c00d0380c00700407002801007040d140542d060b0180c000381001c9a0f0940c0200d010700440c0303400b10042c0c04d181c1c403a29003507041411a030a4132032101015080d8031007150040c01c44103000e01081c08a5804007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 338099640 1250 338098390 338098399
    0xf0f020403080d051806040303090503070b150a0f27020408060f0108010612020603040f0c031403070510090c0506130e150f12030a1404080a0b070906050a0801030b060d02 75
    0x4030740da820442ca4a60042c0b070025001c1c1c0c07512000680d55030500041d03062440c0310318001d100603501d96406030000c01b00840c0c20703501c5104c2401070310300007072800402a00c41e03010a1000c60100d20341c68140001c0c481d2540010070400848401802003005120926070302203070b40b01c03c251184600d842c0309002845a41c000540d24060f030b108201c4414000d800450407038215074003c00100c0e56501161045541890f002548040700300003050200f150054400b40560103041e07a00d001641e203543d0008a19600000c0520701d40010031180140a42401039075039640000030203000300d60059035075111741c90072409028804c2401040c0c1d01e07c4800036a440a0140c07201503020221801e0140c0710b5401583e2448034148504000b038501c078028101100058001e0004400440c20b040354494140c41d050130001e10048012820300000407007100802680f8419801503000391420309118400402140f40c03038122109101d01003042c0302e00c4035844410b050440b501303c4403d08440c2c039501c0028041d183d8410029510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 338100890 1250 338099640 338099647
    0x8030a05010816050d0201030e0114180c190b07140609030d0f0209010806060c010e160f240f030e010c0e0f0d050304030803040303020c0f07080709020c100f0f02 71
    0x2092040d40018142c9001d001100c0709241078290001011889001d843d41100c0001306040c0154040c0c0c029000d0400c80c0c20021400020711024a03003888004c842f04103862a030a144060340c001c080c842801c1c1001c0c2a110b0003601166050301d80c1111000d4450501c02c1c660000c1e41405011042d864881c40c0c0c140201610b800c3d050030840c055a940115000484851408516800e161900c0c42140c0700d452041e141c40e403141da22001001003540004004100075500c410707616510714805c0c0501c580e8000e292a1032030308a41044001424078040e900b0010b2903031000640c102d2250a098a0600c60020900c0c108540000c1c02d18100c024018003140e00c4001e60a0000070f000c040e0300b00c0030317044c1c0c0b540c02680e00750304002103041040450b40c04280f0140c00c5810801c02480402c49000040d94042d000341405840d0162500505140100b52020441140c00a600c18080b8460900105005010301c10065051145071500780307803a034078802c2490407a01e6440026082091140d000000c5c0c0107a0350108548 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 338102140 1250 338100890 338100901
    0xa0507060f0305161b080c030703080a050703050105060d0f1b030e0c01050301120303050a090c08060a0f090305030703090201140a110106090e03030408030705040f030f050c010806030d1b0803 84
    0x1d07007001c4a1441c00301e401c00c00040d4400310300400c800c40300e00c01980c4030074040303004403482c100c0c42154076415079082d482000801c1c1162010801000c0c0316100303544403003240c81e1004d010011640050524000c05040000400450356500d080c1c6d61250400c0d040040d090400d2660b2034010200b09008023200610042d1071b152072034242c2d00004010f0015415a0b400c0d01c446001110144024010755542e28100e4944101092090b8003090340328040e12400a040b08031307501c3d41100c0c0c02c02a400080c25a0001081041755000c600452082410240003444580001e68015069000040600c800c26503514180401e40e8499800d142c0c010145500450340c480d00c00360014110a6103021488082d03081000004a031201c41c4240800c202600004d1411a200c42c0d035001c0341540301406c41000c00505100100c0e02a0481c0300d100000c52140300141c230583c2e100e00e8120300b00021120690306011198007003000d01d840110300411112540d06d1b0000070400800c0503c60100d00d030580c0541000c07004400c110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 338103390 1250 338102140 338102147
    0x403030b130b090c07110a1401020d0203031905060402160521030f01090b1201061e1205060106080a1d0609071e0e06130c020a0b0105030c060f0306030a050706 70
    0x15081405440c005611140726400c002a500c40c46946900110040001007032101000d01034400d036403003a280b001d00c019062000444100403070700081d100c691200ca1604081d07804001490f43e040f0280040c43c15481c0c171400303001e0f13200404581c2081c2d15403030360000340881da80c5034103c1c0c08003442282486419010b0303080455483c83c080400141c400d015090014502003800d0039680300701e030044503a4280da030a03c1d6001c8090407030f035030946400581d041c0140603041d00a010708800b40a00b60000f0186540c5803034464600b207800c1e440070310000702d10401d65000c40e9000c21351a0545015042c109800c0d155104124001d00800140c00d005440505035135010100100e1524044c120700d008a41c1c1c103070340b240d06001105072428043c141404dc004400c0100080e6840880d42c0a03100030912601e94800d040d040c015640a044410010307001181d04c84104400a1500c902606c1d042e40100030308a0203201103945072042c107940310103041020000804a540800c0307813501007a4040141c40c846903507540c014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 338104640 1250 338103390 338103401
    0x50a09150305040b0c04140d0222020703022a013009020310051e04080d060e090610080c0f04060b0c07080607050310030807030c0506070c050106050f032a09040303 72
    0x4840b140c034004e010801d007020fa903055900340c441101004104565150400190050360312080303030003640442c4d40c122160056510145c1256001e031015940300e40030b14009003005001c0700101c0307400c5e00c45841c0569100c07042d903840040c210207003080202051140600a182401b00320882c403040426a00c4180030003150f00304c030761000d10980c21500020f184140207010b6a40459090412081e42c5600c0c03c0d07205100503074180c0140c05080220301d00351146441d4025600c840d009903132241c0e03031403040c0000c2a204100c841d5121071848000740100b82403508050301c0e0001c0044540c422110148000407960781e90b40004028081e000c0340c299105201c0031076a844072401d1056551500405000072070341406882280d01c01c1e0300c2080e601e000e541c150398441c0056000600c0a400300300c0d00c0f030a580001071041003a0381c060b007001c3e220a5880c03e41031500781d00355101c1d0f8120301e006034203591040b892901d0010303e041c4100c2c0c02c25482c901194410301c118411030700c8041ca195024401605000c285909075109 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 338105890 1250 338104640 338104643
    0x1d1207030e060405090c0304030918140702060c0a03020a0e100306031b03021c05030d1a0f0d05060f0c16060203060a0905060d02190f181d0607050a0915030504 70
    0xc11007002490750410075540514441c8640104110000480642c0c2000045912a10905290754599100c0c10104100705141d1403044140d90f50b05281840c5040c04045150b104440d172000304242d1800310700181c818010401030009140d00803501c100403074000c00455202c80c5014007001d0719115039480080151005100540303038403c845850030280701d20507003a5016203030041c101007002c4000101500e00740d84520400c0d0351601041c0704a042c16000b6010b2010501c1c4a019090050f42198003000f214203030b030945003441080803042d418002440807400c95480004540000140e6507000041c803030f01c0c0708600c0d01c55803141e4582d042c1c1c2c0401c00f2070703801385008100554010400341c1c0c5400c0d039203040b22025202240d201001c1001c0b1801440e01c010000300b0034100065201ca000c1c0d075407441c080405d8036900040191100401c5000424000c1d124400764001044142020045007100050b1200e80c00742181040080024101d90120b000c0e4441d13000822100448000283c0c0643d0001c008210a440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 338107140 1250 338105890 338105897
    0x141603080601050a020c09130206180103061706130302070e010f0906050103060e0a0506060c2b050a140f120115090905090c040b2b030807021506041d120703 69
    0x81070007544600152850402c4a07001808110204c2082040562000b0417880440c0c0415204100686524020740f803038207503e015090300011098000f4064501d5500080c100071504c8804014083e000980180c202c10480e400401c642c100f420202e052290907000315400e0310729003000041c0d0311030042001044820101c010001a9154001101030380c040d031003503d18520810b404a440b91a56038480354114400030400c0785404241e08803e402d04040e1511440564036188201304050400f0049104080f550300c0d119240c104014400381c201c0300310b90f0500031111400704850305403d00c05407c40303400005407200920076603035421006180352182801c401c0001c00c140e100040f43d1015001d03103030040d074414002c0c00313900803c04144001041c407581520740c4104031800d0402c441c0959030031800301406003100345410300038030309024110303486c06814041194040603a4101d0f08130340100d1540c101004032004566415254200c080c04168241c44800c0e03401506803031001c0d442e8070070007008010720944 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 338108390 1250 338107140 338107157
    0x2060a0608070b0406030509100c030902031002030105030d050f0d0614030d090f18060911040f1202090112050f070f05130509061b0f03040303020301170607021b01141603 75
    0x10141d80c442d032192080c0e484103007003440b06000007406178102552002c0481d0448000c000a0003241e01540c0c0a4a101c03400f1991f030303400302419403c0500c440c0b8610900d50100b03514551414020a0351a42c034410b10000704a00441d14010f04000f80c0201c80c3d20b89441c0d041480804d464210362070390004d012202d64400d01c115000d00581c140500390520440743c1e854001d01d40d0900d0844c1c04801402d540034050002580e4800103c4c8220301440341c00c0700d11566550850f00e0ba4105040b880913400140c01070001518965041030059480f440d0281c1586c00d04c400b103140040700ca28040b803031314141c0f0b00003440318000d03a10003041d881d182490074421114200d44000f400ea52807210300088850596460300540c2001001030321011001808504214040c60380034a45180c055803440c0ae90019541180041c0d0000010810b10004040c2ca45414400c2d8000e41740c1d034181104040c3d611100044200b106106044403801c02c0d03805020760105030f4010030b16141e83e0f82c0503281011144203550204501080c000c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 338109640 1250 338108390 338108399
    0x609050d0506040b100803030a0b10320f0c06090d0507030e1203070506010e04061109010e1e04140901050702060112080f090d0f0b0c09060d090606120302060a06 71
    0x180ca400000d4100015100c29121901c0351303001c040c0020041c3c84246188500080e0304402000118401c280b0400300140700041001001001071440e01c0c00820005040e4034007100300820382c0091000e6001c111542d503030070040450858540551005e03004030840204221040310300c046840c0303106144c01d0068400e400c44500007540d050042c014007400084482d28414850b0805203c036215140d0328401303d81c141105603990a180c90800d0b080310100d8007004040c44108112409100d40b0041c8908982c6d08020244000a0080c95a42820b921035500403c0140f40e034020381c5402521500050424402c04025a040c41d050000030fa400000340c1d031074100001c0c03200d4404075810f8103807800001c141c4117501d9070343c0301e2600c2500b0000e0888820390040000f505140d40d14075040e40c40314807525001102d01506c0c01c00e80079407400148000e080e82c908004040d000e0399440c04071400001d01c50700002d072055003030610000625580d0440c841c618126420102455000242c0d82d1107248038030401c5c0f0116444 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 338110890 1250 338109640 338109649
    0x622140d0f05040f0b1803030c1e07060e0607060605090c090127050105300105100e030309120a0b0a090209091b0d1b090c0e040504020d06200f04060905 67
    0x1103118898240020004c00e000342d060020041c8160700302d004031100020f1165001900b103910000d20702019501c10319000c81603250824035154808000b1020709009841c242000d02070409000065110b090002800001c000480c2e0114019090140c403030000d0b403800d0a00310b040390b840f00740014041060320350845c24200c041c22070111044000038143c1c804a15002c0152200d41001400798002c500294460480000c0140c610b40007030b189414501c055454401401800208404150b082240c028040e92842c1c500000301d0380030310000c0d5a469210145008141e052240440c40148010300e080184410f000341a00100a1140215018412620741016075a038800100a40ac1c0b1003c2042070500d81600e0b260010700ca01030b00400b11685018500417000034040fa040d00024905039a0f80c0490b00000e500c001c0e8801e00600554007045035080c540c000655190038070b10b0042449856109280c1441420b48203580041d1800810070380ba0803105004c1245034005000711000160800d40002e2540361 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 338112140 1250 338110890 338110897
    0x1e140c0a030804051011150103020103050a0e070b0a2d02010e0a0f020d1707030804050f010e0a32010c0810030209150102070510020105100608090622140d0f05 70
    0x1c1c8402c440b0300c1c00d0b00e40400e0049160300d003840101031041d40e803d80d10341800180003052502c1a00345426400d507055200140c1103800c05001507140d07c0c036003491417840040001e98403007654211a511911903007500c00072101402450542901e1104444c0f0491044102120303c05614001e03030000d01800343c101e81e01c540d0f0b48110b010080d213554012510341016052240303103062030500030001c3c80001d0002e05400e20035503100308003c6001400701c0c804c01052080900ca03202030125410000c3c080d5072405111140c0e60792041c4c1c0040c0c42080215100c40e0b0122586140c0141c0350140903d03031072000c24250015008203241d2484c4d5000c1804100014600e0f0035140210b802d92f61b008126001d1038a030702d803a40ca40f820304141040d065105085010031203940c0c40b80800c042003802c0e80003060134501944081500c21241e4040350500910314280401494082541544072041400d0605001c1c0c03601b10310000c900018001400890410741c0302e108201001c110070601180c0c58803000d14802020b0401c455a20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 338113390 1250 338112140 338112143
    0xc0608090d080c04050d03080a060801050c042606040c09141006260a0b130c0c08160206211503031602040212010923130f1e140c0a03 59
    0x402121a61800c0c0d40280751040e00600c10401003420180ca68006c14000d01b039481007038004c11303071a01c01c00466003218002d0034050031803c0024007160402900020442c007850250101c44000503010742c80d803100034038404400315104070490f002c6040c5401c1843c4800f41e02c2c000c1e80c2803c0d0808451200030503219070060302035000c900120b0545890108219000742e07808400c80b0075189042900c04145a0400e040c0d4020074494500007800c030302748000c10840243c1f41c1b8000701c40c00c0c103207501d803810300748c0024541c101c0c15046000c455848400c4034044046481005009500c003501050341c0c000c90100a1420358100e64980101c400c1ea200c00b000000e9103003080b0f02c3c0f6607044d8010072160026031500c1c240c030032125202400c058103041c6641850b02500c0001d801803552550366a600403111072003000e1354808102160003000341030a0544101c41211804000035081c101702d024081d0410150004450200000d840311911502440ca0100e40460380c1c041c0f614000e119008524960b4a000110340080f41d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 338114640 1250 338113390 338113393
    0x24020406020d0c02030a05370b041410020a03050601080106020a0209060402130e040501020d060b12010e0c0c16030209070e09040b1f03050604170c0307060f0b030d0c0c060809 77
    0x10305006022100e040705070f20101d03010300030004036000280d003c21456500b410356038521502e06d00240e41c0c00b00d03d1a00e03000c104882c00030704803120340800d01025000e81c000e034000221190020b04401d40a107001340a242c51444684005910503001da40343d48018081e81090781c1d4a40142d0380d85004a94071100044040d5009001001007801840e180d4000e2400c0c040001c0c03181203250790b0300d40484400100b1901603070565000203810701c190101e442583c0103410503101c624288941e0010103103000d11b0501407894010b5100000c1449101a442581d401041b50011180b072003001c0d00c9503603500e40c0c107480100d01580003c1c000c201c1b0075009414400d8000d001910100647c2c2d142d8450040d102006488200402c0d82040640001c002c011060305c05507000b01c00400144c1407500d407042c1c0d4500180120360318587d080c081c105074808080102c49049401803404200b0f01404040d2100901c00a540140e0520a001c0c4103a12140c0103181140c81502401c03203004503659540007138402130000c9071506050f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 338115890 1250 338114640 338114653
    0xc0703082701120b0f1005210708041502070c0303050d0f1b05070f0506090304030302060a09020a090f0605062a010e031e130b0301051c0201020712020402162402040602 74
    0x820b1150340b151901c44e00060005107960928404207058030f400f0358110300000c40005610229010220550100e8013038601400802e02e001d010003050840050402860380e00b461558010405168054a0b03180d508201c0da5010b00c3e81c1c2e0310700905030b54001c400103030f60b950800b03248141c034243da1b20560a54400c1c1c0240c5410b4201500c000302c580f6440040111001c01a02890b40007007841040304034032404000000310358035411808c1c041d10b03140e0b00400d018003150901600b0801038035010700d8a412511013540104860583d458154044c125a0b000942c0041001c2201d20b150002e046481d56a2131142001402c2c0d46446058030b4281c8020211102c00c0b94002c02203036900c04000b0400316a140c000c15001814802d035043d080529280c10b51041009201c040014015071801c070303d01e1034000503b07050700042540030740d00103919101c16106a100e040310540403607055466540403149500c00e42198602a006540360440003014900c1d03121a141c0c4d0501101c10691a130380c0f01b00c409a4026030024500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 338117140 1250 338115890 338115917
    0xd050a062d27060621090c06080a0b040504031d04020f03060906060c03030a20030f0403031a060d06030507050105340609060506132a03020c0703082701 67
    0xc1072008202420390015214440381180b10751482400080c00d096034510300101c41c5565629821084ea0901a03062890300d07500800180f20917100030101c2e1814242480240d41d03034280b02d0000c101c80d00c2c085410908181c00c100800d640070f50500b0005440080e1500b8003240c040500040707016100ca04020080204080740c030614100400c0e41d4080d000608442c50480d040004174110b03041a541c24900503161414960254059900d0352605509e8042c0c0d5411817401c10a00da032401405000a4241036072645862860036440f40f8a851074200070380700c2035a0348503408a0000520007440140d41c58040d2a03400f107099032055080341e140c150804142b0300c0c0102c1080f032403409104600c02c441d8a10110100401c0014640c0c055529040d018901c00a001d10706881800b425051190762001100c0c5403285000c4416001c2d00f003e840c200d0004280205808000c00c00d60007441100750021862044801c000200b104203001449055080c141103c400074038285820f202d1144400318a000c1000c2d500c40b0702c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 338118390 1250 338117140 338117159
    0x610120f050703051002030907060804020906010e040b03070b0d11040501050403241e2d050c070b101703070c060f090509011206050f0108060c0d020d050a062d 70
    0x21814041c40658410a9032541e9492400d01059031580450f9000300c20401050000e02c0100700038980c1c1d051000da02d1400c1da00003144514000e2026051100c4000c140b02c840e01c5a0f8000490114060201c2e1002a00d5007080003130790308080280064541000080e10004140b2003c0d102261010b07140d0710305003803d554031010030030391490404028286105070400406514019203002c54031440207605004a0040000c06440550001100c41c4030f41c0690042c20703800880f00101d681c0904440024152244520030040344289040540075240b940d0522a00281001f00b00c0c04942a0380d804118444c811208a034803405654806003c07408041700c02c101c41c9000c2e0030010658142131902000d101d482c2d000040c1a05001c3e00b001d219819280c982c0d001b00710f00e03440780703e4008200c41d0302c2c8a0f0b190301d4151506d030780c3d007401400641485030200700e10351103640035015281c0a0641041c140198a04a100d207401400e03d8440d40003191414006004075100c0000a4800c8004d50013a104a55052444e4071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 338119640 1250 338118390 338118413
    0x1314030c3007182f1c0903090302010305060a030308180f0a03030c080f0c0a030c12091101031d03091c0605070e1305042607020a080304090623090712090311061012 72
    0x4401000b90039103a02c1c0c1d035140502c80c80c1c2106d840b075110f0814450550000500301d60008004500401c030340d080c02c0c03000c41d07040045142d000c0d02c26200c0c1c0c0c2c4c604000540c00b5050018060f4400c0c000e00c2000603100400d80c140d000f2000c0352800342d0b1015000c1c0d1343c090344540c0c1d0310000d0784c220f0500003080000f00b02441c80b80d08101520300c01400c04241151a24030403030226906000242c4091196400201c069a894017500f42e00706000c40b452a00c0c00401d01d200c039140c4c45021380341ea00c990502c6541540c0c8003203004c20241030a0300308001304101d00e400070002c0c05c2c82d03014454882c4203002440510b0644902ca20503076018980042c0048030207007001a5452002900202410964509015032401a6030f010550006044000b000e9a11940307031a003d0030960f0a1074201480d40c100b1030000c40c4030030b12040c50146403d001120421503684070b40b203080d5a660003c5000340146800c0c10311003014180c100000b14038510012089440e43e50741e49618820700070b10b500590041c01e50f4003280e680410f41c00b00c85d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 338120890 1250 338119640 338119657
    0x10b0603011202040b2701060305060411041203021203010e0405010b060304201c03031d070e07030207030309080a0509010e0a05010c14121314030c3007182f 69
    0x218100c80346c92807000c04400802601d00a4030720440401480510f6060007a6500110300391014080006500c40410076409540200081c40d109065400140740c8208070900186100c9003810340d40e0358440501c0458010111303802d4034031350308203100c058460030500101c6e481076400c9400002c1c00d504044089025600700e280e429031016190302e1500d0700e001d442118140541c4240c500140000003030300c230212041c440c85445406030b0400c050400c54400c0355032a09612409918006948408034038082d0f000f000244000f0341120702c08911444140e8205005140c6040242c03240003560050b80f01b003108001c814010f0700e00103040225000c00080e143c2c0d9800c5440010402541c07000304807800400819080b03a55810710081c02c801c0100010301c04100701c074032000c4065014020380e145080100d80d62005900d101102032100c0c2d14004d40702540e207001060904080c8083d5040300b030351640d20385460a101c1d0483c400941c03071304014000d00a01c11560b840c0300c00180ba244c3e130441e40d2038841c1d00c0c03207a0001f0340c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 338122140 1250 338120890 338120899
    0xa09090f0e060a060303081303020a031b05030703030906140c040b0a020c0d052112060f04330527060105040f030f03030e151602010e0109080309010b0603011202040b 73
    0x8503009120414800c0b140318001180c4001400c80c40d40c10010203c0e580600508440021b1001c1c07200802c0e400b20740a0300c0350b030f0541000445c1c501d1801045002d000b03260805003580c04045003c0b03003090fa15402c0780304a0f50203a2020303c003400070084028002c04055070011384410b01000100000c94104015100815480c01990760004030348000c5202100861000c4449401c0044404134a128551254101c0c00380d07032442c5d074100029a803258540d4000a02482d01c00c96240d041d050080d41c40d0740041e980c0b20740303c90900d420310aa081c605011141c028440003c00720444102103520705000184503840200214006c00c0c0f030342010f0788481d203040701034641410040c08000100301da104d5503000c01d0055200e180210355909803414020115040c0c4841207105411040100302d82084600c183c60b046003011031081d41641ea9100300340d00500c0c6c2c41300b03801429401c0c0258103041c000400050b5100300174010080c82820302d0f0104114841c842400341c8a4031000300d051440260805a0183c000c041c0080c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 338123390 1250 338122140 338122151
    0xb0603030405150a021207120c0804230312090a0b07020103090206041205010f0209182d0108070b0a050d0207081c02070515060105040302150f03040c0f05060a09090f 73
    0x2c012411141c606080100e60320000103e0300c4c52581c0c1041003001c000754132080c081c1010510340e20b8214205034281c01d03e08100e9556010414000210101d0b80100302e614111800010f8200c05503c1c2c00d00d66940d014401d0151011195201e0b480c1d03c101d03002000010012404507042c40d05800454001c00c0301a810141d580114400580313170003005001510740340e1000e04405405251850a6420003150051407074018802da03881ca0311800c3c1e910080c4a58041c1701e041a64501e00011801c001d0202c0308807181000d54109180412500a1f15041e11102000d40b03d0060300d9980b41b901c0d904c502240d038000140b080000d0718507604180e0103005060300c07841c0d0303507442c008400c241c8100c1c4264602400710301d546d0006a0400b00030040208030501418044076040500d40100040e1090041d0f200203400317044e0440411800b064100d007210040003034007564586034242428a04110282801061103410507070402284910b000c1060380e034004915600ca8808030f0030600e0714005482c5144503a48801d4030352 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 338124640 1250 338123390 338123399
    0x2030c0c01061211010e09070309060e06270102040602060718030206030a1a040c0503190f0504050d02160f05100201020705100e0d0801081902011b0b100803160b06030304 75
    0x2802210003d22004011062524150070710f10381e6110f000e548039060002000079241540c0301c80d024150701c03000608000640614900304200540104c001d40042030160b001001300250300e500e00150b4521220403200b000310051400c103401c0303101d5030007074a0159011000080c09544100345454000c1015281c0f200080e0f039960204400b074000b51030315074800303440b02c50070760702c3d124405603c00c100342084409000942401b2009031461001a02e0480315502200d4030740d84548007608209480d40103000c0c00c002178941400d01644070070040e1618001405180c03d03500d00701c01003500304c034107554081003908001441c00c010020b41040c4d040c4540b06654003407102a0120b07401741b10045840340031182c01f0a00708a2000200c4c180304040b1404070a111504006002090000500c3c500d1040c504da0300c0b0ba811172150005a56139007000e0340510315002d90017418010040d490102d6802035841d41c000480940d100e1800750340303e015003800328007803040300e211203800700307204440c01ba8003c507000d010b883c03801d42c07603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 338125890 1250 338124640 338124643
    0x209091005040b071d0114030c120405030c1911010c03270311010c080f090a2c0f04080a08150301060303020102091318060b04111b0f0607050d02030c0c 67
    0x1110300f40e0300200480b0803c60075a07040300d01d0060207540d44140104201c0150700181101502094100b00c002c4003000003a00448410111021945450510541440e06180095499110f0a17090146004044107103184c0f00c01c0104075103543d544034402140c00f04241e00111042e01d5043d4041d010003988400b01c4003540c03070f0f0711a20300c0800403100004100d18110b06000c0480044400c0441c10007481c0e04003000854501420750b64080c02d00000b2660310b4000b00002031084110381c00414031030700401003010340c400800e04401c500940701200141d990741c9881e00180315001c100d80c0134200c035008114401a05100325503495100d455001407113911494080820308440140d0030440160b0340c0025841250300e41050600c604200e032003020b01102049601c070300408044014000d140702d885a80b85c400c140e036141c2018101114030b010440d201c40640c0e418131310380c1100400d03220f040c0c00303103c40d08a00c81d113012800307500c500300b1929020f18082d0030781e8040c00254001006100602d0b0b080c0400112100c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 338127140 1250 338125890 338125901
    0x9110f04081c02030c1203060d0503030106050703080a02090109090507021513031107240318150b0411090d02011103040f080721140a0b0406020c0c011b02090910 71
    0x2504010321049008580a02200c40ba480030b50040d9882485503220f04078002407541380c5001205075003910b0b92100310100d107003845d5100d07000741240004000404c440360b106000d0007409000b9518015662141000c1104074031a0440c1ca80c0003501410b801d219407405504070b580c01861520445548800442ca819101c01c425142c5008407203410300450181644201e00c0081c1145000180801c2894079801e030450410000381c86c440762510020700b030707100703030180d4441d5200c1c070348080e00d80410321324510f0101000d6039502c0c2080c000300e00d8205400100e052910a00803d03000c8000071a15119110007001141d54074100c0890401103000984c090454040c07000d00020080721552080403800e115001d030801c0c9640e003003511a4222aa040740c0c040010012442030705070000919030820307441e9131a03a801c0100c04200540b01d900c08406001c100080b60f4014408000c15009030f55031500c3c2c4400440b504024000420a03441125640b0300c05450b00000a0360402c1c001c1d400c075900f030022070003014290342 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 338128390 1250 338127140 338127149
    0x603030809010c02010501080d110a050102120601030c030507200307050109080901110a0302060109090305041e06030b010c0c170c0d0c0801110301050618030c030f0106050a0e1009110f04 82
    0x4000310300340040d0346401d0080c410702202c14002031040d581881c0901c0d603a0b0308141c0d149003c10a0300079140201c001c1c20710036a81082c0e0800b001755550210313001c0750360000303000b81c1d41c1d5400203250103800c000c440d2082c812107014640660301c100e55504c03c5080181d02d1042490500000d001c104520f600044e8244100b5414602c00d00700c0a440d00d030620300240c40040d014100401642014074404002075020480b81d065403000140000c2c001900c0c1000c40716800b49420100c01010101100e000c2038440360702d14030403a00b00d070341c09010030b1400d107004441d42504a00010100c0e8000c076000e003d0420201c10803055403003400c08940e0419243c20000c2d4600300c0105080c4c40394801c4440501c6400000c1c0642c2c6e09406c814844540f1f0340d4500350205941d482015414003040040498003003040d5030a110304c2607001c0001f01101c80855801c007049008081c544070320f80c880d40f8034600000f00001c0030398410b449070300703511000ca2005180c0464200501104444420703180810411009054881e9000e00f0141 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 338129496 1106 338128390 338128397
    0x103030c08070c081e010b130f11030f0411040603030507020609010c080d14010f030314030a020702061305030d0201090203030a1b0b01150906090302031c050d060303 73
    0x2d0098010060629107002c000045540b800520290b0340490301c0310700c1400c03654034080982200c001c1821f040c0c0100d4030f0301d00c000b0254615400000710b103150380b101007004640d4074503038001a0b100719121540350710300405110074000e005440c0c0b0300c4800c0540307040043c181991400740941c0540d00300240f05490006090000c1d0344035071200c880d6258042c110303984030800300e00ca100c09480b4110254601e05400400004c400c4601880b8108880d0503881d2003030200d44030a48049240d00003084480000c2d020051b0000603140c50b0014500c0f2891420f04060080c1403004060918400440c0c150440e810f081144015036000300c21101c134040d180c1004805003a0b4400c40500c2802810406041e0282c020000220058450307203941d148081a590300307103099241ca03070a030b4103204a4000079405500c050080105400e1540d01c2d03019215039800c119092070051510341003995100d80045000 = true := by decide +kernel

theorem cover : BRFrame.Cov 337949640 338129496 := by
  have h0 := BRFrame.cov_init 337949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 337949640 ≤ n) (h2 : n < 338129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
