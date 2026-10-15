-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5270
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:18:23.48539+00:00
-- url     : https://prove2.me/submissions/1d5efe8e-9ec3-4898-8190-a4265973358f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 947661870 ≤ n < 947841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 947663120 1250 947661870 947661899
    0x20703080f1612020f03250f021008060910030332040e0709060915120f0204060c0c0605030108060a09050c061603080c0301150309111f120501050a 65
    0x2000507020400d0906072029401200360345032040304003410b01059510024034120b2007020a80e240e8104002911501010300b103014204600304409403400081c0b810251845084400043e40128403844054065640100742512810040390f080c043c42d12600ba0302076004405000c0140424150f0484400c03401d40006c5400f20202e00824800c100450b24040d45402c0e00145c0c44078854011301814440740a070044282006070160b0702d4008109441c20044400e411200001c0b84140b01c1080f0741000c0c40140f50300200c20180c0303044c0096507515503a6900511480e903407041030312500c52480021a1040c4100b00300c07812078035140014106e07520b40c842d007840185007103281140c1074451800101c60303e4659901811680303101c80260b0f401380445007001740086000804003a0517800410060181d6071030805080c0700000c26140c0020749134100e00d4a070071520000c140b9154440140b03408034460000300310001d04284202c1d9510440b42400880b12030a0b144c1c28001d0650010100d10b003070040a44042d0003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 947664370 1250 947663120 947663137
    0x40605160c152001200c0c040e1b0f0a06180306110c0607020c011209081209010621120c150608010b12061605130b030108100f05060102070308 63
    0x55402665200305504000072000b48610100350324000c4145001c0009800e0388507401c0280007030010139001c00c44501185000d110443d040c0b4408502d0301e0010a040052210401015008020920291800d01c0c1e4503401e40580d034408010415140e5118100b040110703462400c040d22682e80607007400001d4402103d5911000301c160003031340b40040425410302590404c490304340b10499903080f03a00300c002e00f4444010065030640d80442c0c08100340380d034000c1424451028a900015500413a403810581501c10280c251980d56030303000038003004010640c4034038100c0340320780d1a180c842240341000051424182401400000029221442c414001c3c1840704500c1c1c4114140c4005414200240e0105d8203240c0100003562754651003071616007000e0300320751003030140c50740101640e1030103075640090001220600c200700240840e500017a1418604200041c140405502d80c4075a110900d940d0390710300d01c01e584080c243c2403880011204001c1d21442c0d01880040e070181c074080c0d0a580700c0034035580c40880c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 947665620 1250 947664370 947664383
    0x702060901050d180c1e15051309050603010c111c050909041a0a0e0309130e030f030a150e07030b01020c0a080303060a0e0f04121e030902031204060516 67
    0x14101202010300c10701e0030741344100c80e403201d00d05030606141d8030018064200d02903491840c20030141d0401034002c1d00080b9003102c4c00e2120000e1080e0030407101d5016a400c81030b103444502c44046103a644e680c00241c4100300940080002c140242e004488990313800c1602c034000e411500107030101880d00e040d2005040c7c41d90401c0d5140402c2100869104e4808032000e6400c0101818000c5048850b40c02d60ba030000103510741400000090401d80c0d0b100c0c411110b10702d1060001802d0030845003882d800805419201105980d01c4d440314003640803081e401210885c810b41d00c1c08940113030541c0c040381048141c1d024486032122f60780d01d181c81038000f000c05000790340c10340c812485408c0c0306a9900403440050104d0710051903ca007070203010b1200c2d840140c3c10403000e0410034020404981043c3c168a944241c10103440c40c2031842d44035080c0c1d01d0000b0f04d10144140c1100c0d20680d401c194041c3c22030480c82d80309030119000c044950304440c000b8000d078051100000c030100100004001c0c40590032412600504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 947666870 1250 947665620 947665627
    0x306010207031e1401020a09140d050304060f0e01031e0f09050d020d0e0307051c030c1a060f03010b03060a020f120f070206180c090c1902070f120206070206090105 72
    0x80f150700008100c04400040740d40e07100600c40070000c90200784005090300d0070080d418403c0c3c4982c050009540c901034019042c1d1000d21aa5440d940c9540c0850000d0b0450181d13661203403601d20050108030101d00401c04166198002a6154440d2091800b1114020403941d20920301a42c0403020f011040c0140304929202c8a111002c03c205002c006070301c000300c0e00204098003030070002402c0e001c2d85846241c4a6080316000308481c0e1100584c102c00143c1e9141c0107c10000b81d842c0035599036514402c05002c80901e800d4188000c00d00046880c01020121001145052400105803c1e201502c040c5501504a000450298040c0b07030060160b500b4002059403d1803501e54040654100c11501c00700b10080302001d0000302e507014451150001480607080c018450780c0c02d04550b88081080c4c031103028040203000289880f00160a66003280403001d0b1400c00c070240504001e5642c051405a41800d5078170500001710104105101a441517001e400756042030016000c011140d0412500b8605105040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 947668120 1250 947666870 947666873
    0x3090f060935010501080c1f05070201120906050105132c0c190306060f0e061005190f0207080d0207031e0210053018070f0e01080d0221030601020703 66
    0x50444400b020405400040e4540c5001201da240452a4a229000304d08000c504074400311045001c0e21140c485040035580e407506c0e84012a03000d02807000c12101940b4200b003060070010581c0007981200d10032608602c04010041140044400d0310180c40000303000c80da94443c0d42401001480441410034040e690480410801f0a55240800c4800c0c0d03240220804113204010692040700301130320103031300c04202c618104400c1d008401c20203000a0300c0b9000c41c80e002c140092190007142c41d81c951042d50004a00ea07c2c00005e400c4102e480c0301d410240c09070780c801107500c0100051403191400a0340c002c002c85465900c0c2c4041c925080009415844001d410000258644102c00340e5a51007036540c41c2c1d0b407034203820310110118403805400b0707090f441503041c80180480c0c5c4110f141e42180b0b00405140f800c0f01852071071440c0094651103640c20f148001800110500305440301342c100e41e1454140c88405903598022a00c0b04a12400b40329040b0f280400c89440412640207568090810b0044481140e00c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 947669370 1250 947668120 947668199
    0xc1b0311030a080603010e120406030b130218040b040506030d0c05070f0e01030c230105210711150702070303050d11070807051504030e040905010906110703090f0609 73
    0x903031500380420100024040d01e0f01713092007105801507421000e884903003d8881545428495445450101a10703000ca0300510342e210300c000003000d60001c80c110343c4c0340d60301102420800303031800b80d845c0318909d440642800f900303060080c54401c420080c0904281881e0490948501e00101403e65a0384101400407400301c0c800c0d489880508440451500d880d0315503d0118455030003500007040009907400500110712030b03a02d6900c0d01c24800d081050f1107448000710024001c0c056114450654621b40a000b995038109200784250801c0c002502c14456221581319203642c0b05451100040c2d0183c4410008240700d100170340074142c0c1d4013002192900c0f151214a969030007914080c1c4004c0c0000903014200002005034000d80c94850024450500e01901c002e45441c8400d544035005588030b924000c2000340030350043c014150f000001700000d0110f000032841940142d00100c000c604540d00c0801e803500d1814074581100c3c0c0683d1904031503410040c00c000d00b44c1840b241e003064890345901c084030140380d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 947670620 1250 947669370 947669377
    0xe0a05060f180102040815091c030c112b11060103050d030c08151e0a140a080a050309040903170f040c0501030c0203160c030b09061005040c1b031103 66
    0x1000c8015481e82442c01d0200d102400182d08505203078410841000700040c049507a005030b0300c440255480e1691516002414541d403031882410283e401c01c42203016542591024108206540d02c0c00b04000d99040714598ae400c00e5081c0807034921000e020718403a5080e084032602c1418007881c240319a1610b01111502d0700c082a0404c41d8075401c5240c0090132281d1612403e40c100e0040d203004009401d0654120304410382c2c00281901522250028050450481c90940303025800a0020b00300203a5030301048100c000b140e10704620802c0c4061000030809400120b8240c0c4a422001a605e0b06100000701b00041000080407403d001c6482e011409082c1e000b50781904c51150728401840924151600c2c80054280b41c000134145460641c481000a40c00420f5a8042481d010b1070624a41c4074104911b01c281b541d4001801f80e034548082000400c00440c0190203200394a20b02e0101e01d4903002040241c86420f100100003c29210107101c440d0340ca4140302104900030700b400c0035542c9003290210b065a1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 947671870 1250 947670620 947670631
    0x703140a0914040203012303030408070f080c0901080d111603060903080a05090304050904170307120c09050d110103110f070c120201021c02030c0a0b06040b010e090601030e0a0506 79
    0xa803003541c104200380650300b41c6010460100d90852031581088110f9204141d00400610804a001c42c6d90400c1c3d28104102c1c1c003d0030b81442100c0001d0703601d20300740994000c1170080070040e029040b0014a14180792071030905842000000e4510703604140801c443d829894404d94083c1e00c074200e440307541c460b10412104040c50055138045103003400e03410060081c0c3c1c8040c0503075840c145084200020800080240d070305441045500d0310940e01c6d0741c140294006510001c4486002c000401e03c000b15801207904180301d1240002800f40e046c9400c0c059401034070a10880303800c034102d071025000040324095082d0040c2c40506000440c51680031305201103400c18a070f0b0341009034000803080180603514039000c00800c1c034030081c800450040c2c1d000030b40f03401807020160b814440c1210080602c0f0700900a846050f1110400c403103101c103140c2403403d0040420703928140164500b01100c00c855224170101c103400340c0e000e4405105500c41d00c2c01103000701040e40a40d5000d003d84001c41c0000307481409940c1c01074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 947673120 1250 947671870 947671877
    0xf12010e0f09060103210207030209271218220b13110d020306120a030f0909020307020c13020f0301120b06090403090e0c040503010c031409210703140a 67
    0x207280440c00790024a6014082a030198060401003001400d88110782107881109052440001e00c4520113a1401201d0b4200960120031a81044203120412400c00c240c0100303050030518644100c202c064481c8070218019540c00000c0044078054202100841c3c49148041c0840c80070810699441600c1190360501c41d42d42070719440030748440c0c50700110f21035030880c000c8410003080302c0c1100e104407a0300c0b8818400814940104c0002c900360746100411600195090a90700c80740340701e01e00181415081d1600901080c4500c05c081160010303403081d82d12484d4517070002e040000c0d82408200000c410503902c04081c680811142c0700c88000403001c0e50091180702c50f0500c100003245000e54900344004d092901030b054010070000400d5201c18000c3c11106a040d41442d651100240366889102d260442601507090040300a00507606a00030302034020308201d5180705480c1e8010003500c86541000503090f80d100311040c240d600742c00d10005e00425203c2d09010110444141c6440169001044180b011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 947674370 1250 947673120 947673149
    0xc0813081f0c05040b160503120a0203071b081215130f050a05060d0f170a0203072022060510120c0c0803070807020a1b140604080c060f1201 62
    0x94028a0141c0100320590f424000e041505021384a1120301542280c880200084401001030010a0040340c02c140b14003202c0001c03d15040d80d41101950080d104200000c4014280711680903025103a02185940040e8603840d0414040641c1420701000d080305c10f000110000c110042c3d90b910a104402141e2020080350a01035181d4a0342280c000801d00d041180c145010040785598000010040c980d10104c0806a0a503c0c2400300008940355550444810000340180100d50000041c0100f644502c00304505840c01c40040c1c1400d01030b03100125007180071094003600202d1242e2241c801d400d0001d00018606658000103100d500e174800000002c2100b0b05140261f242e07a0b40680d401c0e040315820458071504996681c804144001800700c020000c400b40483c2c48184280b00c48181960001f822101e0704061704905800c204892140c1c458481e0003100e55022418480180c804071400103001d010011108020300c20150b0106243c04a041030420031070038240700780c620a1f8044d203001c2420054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 947675620 1250 947674370 947674423
    0x90c14090a081b030f280501020f03010909150b100c02010c0c0b1e070c12290105010f170105090405070306091506140a0306020f0706020c011407080103030c081308 72
    0x5054180c0c000d181d040d00302070f410203002c2407510380780ea501403040c101031800e0111b0780c20315a0082c040c0102001c00c4000c0000005000c0e443c94202c510740754018010044480c00052045d01101d00118219800c114401509405140a0b031a030b500e03201e00605040003007485682c0d0721500c003406034104444a100c00b00346040c0700000048506d2300c1c038900e171400754941501034a030740007842000e10508070600e20340e06e8800f04101202448180c2d080c2a40c1c01085d0003600b950000b108013000b402801e00060074002d4940c00140704804070326092040c10b5035402644d0900052151081005200b603e0610130000f00000089032403181a110390b001c0c400014517034800030303a00c90030340340d095000c1142e042c1c1d681d0a0712402e6582c03044080c210381e88850300507a03501128040e8041401a00c1001c2e2203e84042000c031030142044d0007900c558500c2c1d003103040107590b86a4081d40c20b188203005c050700080100d0b64140000e0030b860010200510b40c3c03070707401950300d075140c02c82c41c80c000d40b000c20508102d880e00c04002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 947676870 1250 947675620 947675623
    0x81503031c0b01020d02030405040c050d05070f1d010804020418120210050c0931020a020c090f1909051c0e030c011d0105070807050304060c0b01090c14090a081b03 72
    0x2d0420400348081d000321010a40001c1d039078000c40c0211071146948001120010b4003c004450310070074030003000d108502d801d0401900350180e001e40c2e6004501301082811755044640c00303621364024140c4070044662280d07024080100030507018088108012100c20780418484000380781006e0f5944e0003000d020f40b2903035001d0199000603285c06e10b185014400007001e5030310002d0000d0910041016050103400340e0703010840200c80c20707490900e1340d031001a500314460f0740495401d444034010794107003555460f42c1c03a00c51900b0358100c55000002c0080030260038160003e030042d14a00d80550100e880d560104010342c3e010010341100c0750701240700c0302c88002032402d0510005030f460f0801d007084100c0c0701001c6480075040b01c20620b40c0d8104040000c0030400c00041c4000c1c0c4245540140449884940b60030000d804030b048060f040e07034480c004000004140c0c409000e00c0b04881c000c1d955501046004640f03400a0350803050ba142d600c0f012080d004110100304100c040300801a882c2060300c141510010315 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 947678120 1250 947676870 947676881
    0xb06221d01030f0f06110d0207051b0607031202131502010f0b1018030f080306030709060f0308180d0602211b030903040e0906190e0d081503031c 64
    0xa114490103000400100c1ca5030018841041d420013504881d180581c13401c500200203d0a0341d69440d00e005c1384100c0b140e030065028102c018410811140c10445c40800c1040c2ca0b05282c2400b94010070800082000910401c038482c26001402e0015080c1110203034884400655a00590740603900c517200d003000c4941c240601074411041d0740d4104000034481e000301b007031580403861078818041d280c00c0d03010900203074503101c800440e001051003d030780000e4940a509503200b910b100e4401d102d000004a054001845008101c80302c0c6c1d542c0754456403440d03030b8800f40c3e074010403404140b29607050452003194480454458489116200059039800c00568146807404949010b41031174441004101d580343e05055215050480075058540325920b04011a14511440d004200c48450100074001d00362400145c55010310394910101003195484003074242181e41c0f454201c0f0f41a40030840c040a400d0042c1d00b4981c200200b0b00d40d10a4960440003c640346600c200f00c21100c0e482049915400480c00d441034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 947679370 1250 947678120 947678159
    0xf01062a1a13020d170d020309030d140f01090b0409060e010e1002040506120c09030d17070c030e120c03010c0206040215070b0c09040f061502061609090b0622 70
    0x2031180c0e08168000c164640e0b2202001009861700c2c0d00845401514401070307599490794280207659038505601c5460b242c2c0c00010321051400e003000e00f400380d4903041991062090002054096880c0e28110900000d840407603a071542181c0c1c0e607024800414518041c1031049415140085a428603001b9020324158000002e48a5644180004c0c040c0341d03a0901102c0b41080c50303591551301a1140b009946441c03140700041a0b246c4a00300c030245070346800658514112030b80501068141c0d4540d4010b5a40e861008801400100303130070390b412990300d030002081a1911414086400c0340c04000c0100b030849010004000240e4001810402103180000000000c403900c10b07096810302c0110b0380e8541d1203110241075000d20840c0031071000401d0f00c0d00c1c2e104a81d2864504070a000340355591569000d01c0c50382c901981e0040c0100d0001944500e07007114125840c04c044d07075a2141003803604c3d0f24000182000700400d68040300410018031a07a103034100341e0035104136500e80a18400c0c60010402130a8407038a44c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 947680620 1250 947679370 947679391
    0x12d050a170c04020a0e010e0301062103030c030b2b0c0b1201080a020109151b0c050306090a0b06010e0102030c10060f150503270f0f010609050f01062a1a 68
    0x102c901d046511038011b1050a8007820b00141082c0d522000901520082c0c1040d5403c81d40b95107001e4007202404206501c1c41d009032010444030f420300c04102e0940718285c0c8580d400c009800c072142c1032214200f11411464a401551040880d0f00b50340b900d00192042d40300b2550008040f881c00482420364625500611071030000b840781001650010b03101c4d840f00d00c51007850030a51180382d0641c07405040030643e07041d11121040400d201914241d00384903514000c1600912880c0006024003000017252025650002e0181b645590703001d004440380810801514114001030002c8c1c07001841c10040ca0301303110400c05003c41c445041007400e4020440c1940110900c40721410550344150708082142d0700940c0880c1218840103881c4481c059100e040462042603200d05441030740b4030400030802c00103070002e490091004903500c0d07000006480b0180c034407594880c1d045004021083c0111103143e1b5040000c0e9082444003404121440b1802401c002600d2803c142c0c141e10b5601251036039200d501040464 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 947681870 1250 947680620 947680627
    0x1020301060e011b1e0c0b030114121507022503020924011206080f15090a031d0a080a0b0601020d080108100c030b102303012d050a170c0402 62
    0x4603492414a013100036008002c800c0e480f1242c81c03852040003c0c1035800001803090380e0b40e1442c642c00c060b4024401d04051101c00407040d8154a4400010040444604000c2019030310031102001030300c2d0007074103040c1944240984441d00b001c1504050000b01e540d503100403041469401800711401c00103015080c0c0000d0400030980d10040744900f000c6582c0281303861045c00550b444250024000d641103141107220310840c0c406890400115407080362500181d8035440d0325028030086d96408088801004190103101e80b07100c905448400d001182802441e025209a843c4481400d045005100b601c01c1d80900b81001901e58042092180203011894490382941c50700c3c12240c0c40301010205d000d151619180c0e4005050310035003000f08401801010740c810340f8444140035008100d82d070443d10308101c1c1282c650b5074440c0e1380e40c02c0d07030304a60755204892024451741c0d0301070051460008440540b98800e2101150545420110001030034002012414103504d0780c800502c2c20850a510a00ca540100f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 947683120 1250 947681870 947681897
    0x90703020c031204020a0b03040b1015020c0904020f0901060807080c071a070c06020c010c0e0414040201050318190228060c240204060f090b07080d0212070201020301060e01 76
    0x100f2038a43c2c2510741190300c0f2503203562000a003984602d030300801d586600801404140809600c8007401201d50007400d0409990340c200000c080003c139010400960403032249281c25060600ca12540f181c8014080a04000414005800700a080e000900013415203810441c1c1c0b5600107c000742c2140320007000d1410614540d980740c2d0310030b00e8020b001820000d407202140445000b4808681c03040d030301110a6481e4440d0b00c12084c000e104c401c0e0b1a000050031006107040ca03041a203e41d654200c00d070380340410326a585400543e0b40c1c0e44050220380d10103503008504001441c0500100c000146000c16100030010304d401000040e407070301d811a804842c1c00c0810124004d49000f40784d81103a03110300782040b021056061075141030011105102280750b50109200d481d5101e42c2c000d2041e500291102064600301440460b04403078140202c1007040d40c1080301d40049402d00b4080e00c2c0021180c00007614001c001c42e40041583c1c030690344100540e4020005212083c1c10213020520035000b031078192150f8004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 947684370 1250 947683120 947683123
    0x9090b03030d180b01080c10030203010305150c4609051203220801051e07210903030905070815180f0601031202010605010e01021b0604050d11090703020c 68
    0x50080b072540a943d6690a280240003c00d40c1c103001c0e0f500401c05441669444590b00d89a2000d0405907100c4c1c4120030108014a0091003580d0503207401c00c00a203c48414105403002d141c4001d4103841c80880300b031101040c007241840141480c0010440400109410340c42c8006100d00746a504c914020b00c008095803600c1e60200e078042c12103108556041d0040ba26120301400c40c4144c0e504d0a41c0708651a208504c4019007100a5003114141002007203242d44940100f07010b28804001c00c1c41c40380005011403640e03803140708540b9140d07404090494104003002c06140407078446c0d440440110b41c407601d49000b070003c01c2c800d8100412420700a01646d03002d03030030b0b8003a040400825078145010030030000710360208104201103403c05181c08070748095860381004a034812190010304019801d0000110b0b03654444d01c0e9070604a00c041e0002c184202580418005016400d03c086030001418000068966113200c091011280600d03071242410349560148000100024049000d040c010040764403140b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 947685620 1250 947684370 947684377
    0x10c03082a0412020909031608090102010204170c0a0801050c0d0f091a09012405010305070e042c070501080609090109050a08030702010b030c091906120c0609090b0303 74
    0x411814240700c11107800e84200e00075100c1040c100621a0204000c505921844212018140200c0e00001d030350351181c3c038441d5a40308180101c9804070020306107400042c1d0b1755001d080e419030140000741c10f080c1ca49026100740a810f000e01001d551190320700c01c0c0c507803c6c02c2c9020805050004002d00251404441902c01c900c40d4144100b0610360f640441c0280090079442002c4182c0d100c03c210024481c50b44c20401805401d40d81a0b00651030450050b1010800c841400c1105800025801086240100543c0140301c001d0804d0103215003094110700b55500c61146603d07000c8188201040013400b03a540410b400c400c0c00c49403c0c00c2e40400d2081c4010383c3c00a1031294001021901000300d40c0d10b030741c4c1d41405031210020040c09071190f00c500d0b2003080301807005140300b2a816030003003041c0c149000030540c6e00e200e4100c0ca9030304121127001281104603501c0a0020307100e0108404980d2a0303031064001d20356800048281d50002840c2070612542d0340c8005040c000781855034051100160500009850340b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 947686870 1250 947685620 947685631
    0xb04090f15200c031c09140c1e04020c01110c071703070609020a0b030403030911030309010c031d150307030e06190c140705010c0306050103020c1009082214010c0308 73
    0x1404aa8203090f0007040044410724120302c0084014221400c00460152900400c11650f2050000061400744800a040818003c0040400305d402e03e100708086080c214000440c0d400903020130003410042c1c024019100040403114140c0e0759588201380642c100512500520041015032840002d01784002054640c0c5941190300012541d00c00c0c40019440000399000c40e08010000c010881410380540c00b00c000c045c084c1200c552900c8041c000c240d1a440741a0289010a40c4c4d0201480441e100fa603000006103400804250038440a40000303043d2001e14814820400001007008006981401495211200c1c0001000035051141c0700102040704105040310380c0e42d40d09070700c0415901c0781e144400e0722201d08021a42d94441404e00c103020300004001e09002c02e017050340c0000c90f07522074801c48010446500290070082d081c01c000c013019280c04c020a03202180305000201015600c1441500b0304901140148210342c50b000c0400080a5020b1f0b900e41884004415280880d03080082e01d40d010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 947688120 1250 947686870 947686931
    0x306031e200121201801050901120504060e0102040e0603010605010806060a0c0c050d0807060b03030f040902071a091509160e190c11010614060910030b04090f15 71
    0x8607010340c1c3e540300400d00b600c070310b51284418403600744402041340300800c00032540f448601d0800e04201c005449900c40d00041c60f00144121034000c3c1465415841140c04c1342c0b040310041f45040714464550b003039802540000d0110440801800824a400d200d80c40c002c080a080000007454420006503150140c486090140541c8000b40300c1040003640700d00d00540402010a00a410079041902a580002d80111500b510b007500e200e1191800005840311000c951080501e043e0401e41644040d4000440440d080e100202801da00011100b50725071189440a004145d1683d41040d05600144050640c12140d0008807490040c81e203006040010369920036a10803054440c441080f4145042c40045035945180840d64061298004419207941131101c0080c46040d44400c281809091251170103580140c0400c4050010704145800f00406081c0742800160450503102181c165805020100c940c0b03078401401e2020072410300c00e08490442c80300c0c01003140d44e460403c03200040c4280004800c45 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 947689370 1250 947688120 947688167
    0x108060913030503040c1508040b09010b03030d0f02070c060305090d05040303080c0307020f0a031e02070503030702090c070803091f0c0f11070503031201081c050f03070306031e2001 80
    0x40c402c070071b000c07240100400300d6842d80a4040c0c220080a402c81941e04680424101000c5022008d05000c0c520f0141c0c030080141d0b01d451020407204000b00580702403e04042e402340300c0e43c00845d03c44103281c8014699503c021900d03240000c2402d0030a000f40c869402800800e02040c404640d00509d21940010400449542e9071034400741645400d150010301111845151194400c265000005441ca03c07108003c20592024241c02662140c2480c09042d406500900c0400c0c0985010f4030043d4001200102441c500801034850380e00c070b0750007101d007101250720100310300e16410400d0340d000200c1c00c14035800b00711002c8420402000001e229078848100a1500c00c0c120004009202440041000600301d80e034500703821001640710718091103210801c1c0504403042890400d80030340000b00c070086a1710a440d01d2201e0561551710740001c3c0001041503610a000700000b81c25a03407502601881441289100b0400e10704030014041c1d030180d00b004083c0400101e4802d036003100c0050003c103240c02e041d103035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 947690620 1250 947689370 947689373
    0x90f0a0e0a05040807060207030c020307090608060c180603010602010608071505030a110f07060504110603010308040303051e0a03050a0c090f03030e06090406150e030604230109080a030b010806091303050304 91
    0x4d6500500c0c00141044c4d02c0001c55504042e0019a0030700a1032007601a144040e07a9a5024412102c1c14401c0034040c0c3c004000140c3c0d0019414001d100007060380a403052240605000301e01e081d0803d0f04a0030143c0e560342e005000c20501080700c10001c10544a850b00c0d4580040b00007045400042c0612160a8880380e6158103e2016010745150241c0740d0500c644800d903e0500030081c00007030b80d09488148000302e41a200e401c04604a07416250030140452415245a80c11501580b100341c0303242100f00390042444521840f200103100e003841c0d44c0d03070200d440d04060541d00200d4010002c42d00900c00e080a040141c3e505a0f2045000c6070b0b0181018980c0003a0003010980b14415035810307590003841d1210110b045a8a0a040c039801400e0365250500e0419840506690703441c1039030003500c0c910419403825034482298100008486c0c1610020840030030b00d40c0e504640d0b0f00241c0018000c00d80f0b80e81070700d0065a0206070181e01c41ca0071210119907040030407030386022101e0742d04080c0c03c001c40040040c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 947691870 1250 947690620 947690633
    0xc1005130f0f17071106070f1b1d09010b09060102070506070303060f0e01081005192408010b040f0603020a12031709070e0703020a020c0f03150903090f0a0e0a0504 72
    0x38100e41210303200c08000900c03880e031102540070300c104540e11712210035908000c0c100002a0340001e580683d1700642c075046502c3d4800040d02042e92900c03207550b19040400d03043e6864503c1030b0401c400c08035111607410075007202802d440030b0002641c05209290708000490b07a00107040b90440c1d03401da0b46c1c0c0390344280c44c2c101200502000e0b0001001080c0039600013601c0c3d106490703071a04072440c1c2015200c0c0c0391036250000742034620076a0310b54042c4607403000b0181c0001469120080d610030b41a070b4200c00c1d04412060f009840460f520120490b50350740c481d1180380c1810b0044100d8820059000c12a0314219800943c4800260066512401950300e500b4200340c05215012240c0781184280304440c90005505a603883c194000e800710130001d80080340c1218068000e0300d410f03100c2c3e5006050511010004c3c4248848440c1c0720550600c510040c1a05062811042a00603490301000d1507441c401801488070b13a092503516180180c4851908020034118410115000500100c02123916169410b040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 947693120 1250 947691870 947691893
    0x14131d0a1505190503030c070e060607211704060905060c040b031b04030c0b09010f0e090402040c1b0b1f0303120903050d11130e060a03080f1308030c1005130f 70
    0x40e03010704c0001f881d1400d90000048035011900504060a0b8568401c4140007203805865402401400507031180c0000f406811440f42100038180351262074140000b01d102584003040d141514001d0341c58001009111090044950001c0c4002540d0310b05444e01c01074603d13910008002840700b5040402100341c0411030003c5a00660b0800c20a02c1c48540b41d40444150368829440d050100d084102c9180b540b6001e9840880d450030b004008039010b80c2c694003400b02a01e081800b5034200006041550030180c2c81c156015006401250b600714145405034410502510411360703884982074501d400c000180d8421003106949008680100701040a89002d90784c034020043c05036a102d0600c880c0c0401886c0f0000070381032501c190f8101c4110540d03216001c8180d80d030151100c82e00a100c031041480420343d103400030400606510251860102010038a9800c0c1800c0d070000030700c6e17800000e148020748104100a0104809003442000079051503000c803a0360b908100e00081c0b6190b00c003003005051010b2003040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 947694370 1250 947693120 947693129
    0x604060302032a0f0616231005180a230604031101050601180b0f0706050c03070206072f010f0e07080f0f070614131d0a150519 56
    0x11200c000590100c3c0300002c02140d0404201100700599a800364a41400340641408003d00500d18254420a11180a9240305015035480007191f14180142552441c1c0c00240008030010f4003400755003512800a0350400b8111420600340302c0d80c03602261a01040030080103902084541244807411080059204180d50300308040c012401000309164000030415092242d0078020800c17940e400d0015203070858100940c080707103000b01c0c800784080004c00e00200340c40c2e10039100c52400c0a00700c3da5010309446045807052460100030041c4601980c04110440d0011f1071030510f000034040f100004a158045401d42070030041c0c4005500600e20420340c84000c44010a00e0140050603107041065a94212882044803900c519085101c00c0180812519030135040c0e4006002d10030b04d02401290424001d20041c2e000c0c000c204500080381d20508800c4000f84003480400254900701c07040603104c0c010062212500b141041842000303050034807400d2090358804c03100c0c1101c0a1980341c1000c0c0d400d000d0b412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 947695620 1250 947694370 947694373
    0x130e070e0a050109060806040b15131107030207061b0807020105071e140102040803030c0f162f03100f15080a020411040501080115030908161101030b010c0b060406030203 75
    0x5101c0000d00c16004641a184003210902c000b82e036541041395100c904480190500604e80c011030b0802c0030514202a8004000304041400c0815122000c2110241d40d485d5284103800502c000405405009500003007055040c19204a5034140c1c0d209044403580070010210a0005080000c4ae80190145c64404d500070076102008240021001010201c0d500166020303440040c0500d0020300500032102591150740103036003075403114911400320380c2010105040188007440b005c04402c45450300e03031503842d01600561107940c21050000d00d0501c0c0194010104416002501041f42c800054840890400600009030303082c03c040f4142c000d0000114160312070b1001d80c400540031000081d01484103000312400c015940180d10100000d1080d8801c180c0482c03401e8004100c05003c8001c01504100309c0d0401050b041c10595400201764004400e440c00f40800c0007901c420710034038004202c0c0841c002e08040241d1000d8400107010b070340d0410b030010324060310b48001039040d40325504024000c540c040e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 947696870 1250 947695620 947695649
    0x10110606120a2a0806180303060a05040908040503030f130515160c0812180901030b0408030c1207090918081c0e03070b060117010f03030809031e0c10020306130e07 72
    0x130034a440b000280d660040000000c0a200b0101c03002004076802018020600d4080c00d183c8000e00c405014003d0701512102018400082d0b6618144000d00c1091484503100c1e130750740806115004040c03002e802075400360440465401c0d6030f10b00e1500329000554800d041032509206407420703402c0d0010580000040c3d000381c0b04492030403100c20014120310505030a1849840d0031200070701c101c0620903c0702810700054003000c46d0114520718011a044101088098a0301030180034024001006880000005011a0007005120760078401c0100307035007001035040b0300301ca4607494010460150080200c0d00882140791a40700b90910b81c8a03030b0b0103005507010307291542100d00302504410400c40d0403d0104106001c0b00d08042a0081c1c540d050303034410784002c0308082c19a05c0c2216a80ea0040110003503210030000035042e101540b01c0c0400c080320041005540b4001ca088050906035801018642e1724014400c0c410141e8450015031280312407190f0010700c00c030403500301a1a20000d0303403002d0200c407202d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 947698120 1250 947696870 947696879
    0x50304270606030c030b0d020a0e07050f0a0e010e041a061b010e030901110601270b0d0b040507080d0903080903010902090f0402040b0901060c060f0b10110606120a2a 73
    0x68224142d00113240d201000310080c1c0704140a03224124040007540020003803014405c05107040b0150350460b120345822400c0c0202100c21000542c483d4007044e0105a040c01920b51542e8055042d120f1100e0549050002062000f0207078091038032464518490704000c18109443c104004201104602c02c0bc0240301504103004419100c0d0b008604560010b40010448510070380c001070214101c4811015119002c40c0d032040e202141c0c24803a8031090f001e030300d40b5402d60240c1d5450b08a281c4c0107000c1d01201681e810705160082c90b0240c16406031206400025107a070308540c00003960400c81c2d070418070f420395800c08840024014075405800940c00400641404407010240580c1d0b0300c01ca100750f40422818003040f0070030040f048244510000a084413400800003815a04180c1610f50140000b1030144555000625042c01c001c6032800000c4070704d0450111b085003000350380d030031405c10f403031500030007102010103529010a1880074200c480c94800e881481301c80c2e243c40710400d4425a0b500320031030741c58 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 947699370 1250 947698120 947698127
    0x6150d02031c020319110714180601050424021510060806211c020723040e0d030c030614060a08090309030d0504060210051909060e0303090106061407050304270606 72
    0x3406d040788164440c640d4007249910b0045680344003101c000f004030000c6080300451001e0424001c000d1410841c05000000b44005d01d4280508a544000c4030126008100d00c0000d10b005240002c2034601459001071000741083c0441040c1610030300d18201c001580e8480c08103100c04107418142c54442409030307004a80390400314100e0000300100740744032902d1141001c102d80d203d00c14011208160070000450603808146003401006440140020505d07940b40d001d0a0700305050911201c01081e00c1e06400716100380d0610a00000e40100e0b64580380b81209100850502d000e80c0d0034031002e0000d5140802c40142c8204152224800c1c018200c4003102c1907003c0040c00344d0000d02c07418015126009002d000702e01280140351080002a80c16412a52411851030142c058404113540f00c41d522050350030203400a1005521030180c020003c02c0513490300d41e00501c04403030302040000c10b00b8244041d100107000802110110780404a0b582000c0280c56aa654201e07e042c10040459191810000c1c08581 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 947700620 1250 947699370 947699387
    0x1021504060606171510020f2e060f06110712031e17041e050703060b09070815090406061206142a16080c06150d02031c020319 56
    0x1039544003060301e40030700801c401d00e04003034504003c01c13400500060414103003040d406c2214103032803045400b8200000c4030303d0300703142c0c0c100c1002d48607050400c25030b1090395150368800300301c81181100304006460034103060400266800380d48100000319030766000b803580c100540f0300541030f0503c00d0190380180b031034003800c4107958030500402000d904080f000030fa03000300420203440d2030b54141440340da0389a5558061828801510020f428450301804000c54001c00901024520841000a240c205d0404020340c0c1c54004042c0b00800a42030200212060a003a41800d448000e031041d0038107880c0c500c2d2002c05000250015910b00040c05140401c0c0403a94108500341c0e0801205050107494481080c0d132110010144500440c61310901000200c00081c002d2180903031907010400009072664032411203911100001007035170321030001e00c0340020f0007060900790300204954540309881c844d80465156240401d400c11070000103074601488034001d1080b074449400e944400d03000010300c0c4038054000032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 947701870 1250 947700620 947700629
    0x90507031a0f120715020313080105070f2a0f06150807050105030a0209030307080403050606060306011e0e2d090c1c06150305040b0f1603020702010215040606 70
    0xd007810900040410201003040c01141c0c040d1500c100c0c2d68004051000301403540700c80ea0828880d50400003450440f04040e040341c1e82c0746a0103107699401c00e055941814109400540003645058180840da540109100c5070030f00b40c90078040c04000c0707044529038404803820134180c4007040c00131603101001000a4521012032080f9800c1148840303c40480d02c41c24003602900003a0740c04054188490340c015809540d104181d55400f514210340c0d1301c04a070454000e00e60464040c44045414800c002007405070942c00780c000c0d1021030640c541600001c095000e98890500740301228550003018170321820505014800c040c0c080b11095140075840020718030700b07a4100a0490400e03c01020364070304064a14003498048118034141009811060f1080151041f10742c5400e6172540000740c01c0390f4400425003181e49940700041d5510300750908a800701030040c006031190b80341501300041003011a50540711a100c924006840d1141440141e290054400c1c18a82004248041008101c41b640141c425034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 947703120 1250 947701870 947701877
    0x80a0e01060902071a060604090b19030c0f0b130501050901110a0b19290a150f110a1a062d031203040302030a1b082106010c020105030f100f090507 65
    0x45d0041072a5100844d400c1d41e9841e4460b500300400c110b4500390740c000c202c070000b0060454542a50320f203200010000c16034412503140c800c1c03150400031040340c102100020000340d800240391a01c5807141509503061409094140030020a480060742d2240b001240c0c0303000c1c11001c0f01e540a0032400e00701c0b80490220b82d8101031205420b42640a24100d000320100c8864051048211031340040080c1d00d00320540303400d1900182d4000000620441c802207042803040705807918244000c0e03074000240544031081001c070007644110720741e40025440c101b1602c80c0d070398400190b40250301c0e1000000c1c805040e0103642d203030380c000c10860446410f8154403800e25443d42101160400d40200004400707600080303402a000d600300f40007100005000701001d034003180c03c15182259002640c2d9a6a6083d080038030b0320469191894900c0b100526240d0030182c100c1001d00b411400801941e000921a11004126503034035001c40c0c002c2040c00d5078505944d0083c11322840c0900c58140c0700c000380801400100c4429000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 947704370 1250 947703120 947703143
    0x308072901032303040e041b14010915080a05070201020c030408160503070e040609030c531b010e06040501200912100c0216050312030106080a0e0106090207 69
    0x100c1d043c0300707490001d150000b009107003010325100d00c80d0310f56000200180ca0000e9114502c074000381c82d03108510050a40106030005400e10b41d400100b04003171580080780444c090850083d8805c2c0c10104196015881c00004100741d82c94600803406806a000351404274880030902051080b0040340c4150840c072075040d00d0054554880806a481c40c5900c2031100c404120300104010407680c0e00030210a5020307050042d801201507540c960158444151890001c0c4ac0741400e4602c0256404201014619003400c9000c40616011900d0415043c8003400d0381018002111140b50110100280c3e400c5101c00c020040c0c5031000003c551900003c40d0304a4141d407074072081c0c003050f000342c0128090428080101c0750910b0300500600c01049050098100540b140b100b903036000c0303070050060110620780b07980940503020803c002c05015006c107401c0244a500b01c20f4403c088030400106413411100d1a150101c01c64540c00c800800410382400100e0155007400400700320003a00f6002005100d107d0b102800700d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 947705620 1250 947704370 947704403
    0xc01050a06050906280b120f25020a0512190206100302010f031e0f0f0203041505040c091b0905030c030a03030b1809010b1018030807290103 62
    0x1c072405402119440b60388003000c40c04900f01443e40c151041e42c200c1c2d1101c90055848903019030100158460401e20740000740312100b84a404001c00e810465504503d412402c242035982d210304401008a40a030005120f0510518401c0001140e60354112054818001207441094070691001c001002c4c840456890f211400344001b600700d00c56120f4850307460307116007035038011290b00b400184130104264031140c0c01700e000a401414501034205800e40010325030a2096042c1c00e43e031003e03903044081031052081001003078010385880d0100c540c02100040b56901c6140000348a10103410441c6481d10f403203004002d015010341c0004800440f40ca4103002a035a4a0402d99200c4840000f5a0150001c1c8001c030f000a0182c6c1081f808840000e02034400140c1c41541d140c920041124901401c1e9100d20840401e41403a0b10354003c0340c0590301e010109001c075403284590055080c4002040518000759000c14400798041c003424034424114001202c0140c8814824892000e00007600d00d4918040942c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 947706870 1250 947705620 947705641
    0x91f0e070503070807090f0f0507020c01080a18020607080403080c060609060907021b030f03070507180b0a2c0106030b0907050a09050409061409030d0e1609150302150c0105 76
    0xc003101d04d801c006088240c20f00b64103c0150501c8104200075548690035a60a6803450003074502c91442a4010308400000c100010030068000c0c00c681d181a183c4025141d24030211146c0c1c0300b02c2a0143e0b9090380d11300980c541464207204540c07024040c424007003810444840d01059090003180b049a0900d03058582c113013001003200c410341d40540581d2100c114640c0c4115121034070f0864460042c151500d001d0350342c4402d401c50707103c00e90494480d007006030203100003031055080741c40c51410004100002c00003034020603032000d5580140354000501c8000c40d0901e9442d81501a150012080844e0305543e440101a01800013800414850104140050130051140b0203580e03410a5560304d00044502d0a81400002c128039a0309464440d00d840b1004c060265040440e80a0007030103006554801c0e088800c04100c4040480e94003050700441e0301d2007040041391056509940c1c07070344400105401000d000010111860744000e400040c60350301c15000504a00107040c400800c03200a00107a84c4140011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 947708120 1250 947706870 947706883
    0x13060c140315040902100512010803040f05120705060d0203040201020606030624010212040b1b030415050a300e0105040b0106050f07061b12140609091f0e070503 71
    0x55000440920014401c42d0000100c030440d90b4018100041c2d40256030045544612000520b10100c0e00000e00c112407035a805050600505202000d1820300e42000c0303011801c085248207091003410410b5111084003001e0201c03038014000108004d554000c55a040006500129000c9e07000d0700841002130090f00307012408901c078030390460f60440211100541301a41100c01601141144601c001c3c200a55080400400180c50700c80b03a11a1100d2050001e0243c20807111803010720b640051104003c030b03c602000b500440d01072410059180e02c00f026044138003494000400f80410788031980507210b15110f803105094203c52b003000780b01d019154a401e6098401c1603c000b4070700602c040c0100040d80c802c0000c2e00e1000840d42c3d0700392804119032600c80c142c4039508035041c02501010396a2005a4008140d00b480c440c24141c2441b2840901c032609004d42d0300280602d000d4642240080c040d44418801d48415803890b840074083c0b01031108a03140101058079130381c0040c0c414818042058900000c91 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 947709370 1250 947708120 947708147
    0x61d0417040f06030e24090c040908120106050a0c15020c1b010806040603020607060c0507021002070608160f08090f010f020d0f060509070c0201170903070606060912060e030f0313060c 81
    0x805406d515000b0500303821090007008842035000e41c2081d04241c0d9550b004145d400e0703000b403003540c0c1c450700d621441180845c0c0c10fa0101091120800c0f51940301074222007140c40b80d81d000040f15401074120103124010f8232075501c007402c090041043e03080c101440445816840e50003a03807110b0856407101c4c144001c03102c0c60300010307622180c01e1001c1d20002d12260440b4105040d68a003241c18144c0b564045881054000419000742e00243d1003440250740c01700030158014400d10340700d40f02001d5880c010b0a2040001e41c9603081102c3d9000040074803104200306449002203030004c201c01350600598400030b400c459041c86201c0e0800d0725084c03001c000b601402d030998200400c0003115031a524000d40740d82d000c1c40070490500c50b9146021580d42d90f00c0f080c0520030200342e0003650369128185010400c1320f040341c00a00034040b045805004003410440041c090507803006002803842d65502c40c003807071400342e0020b8042524000080290700b0109070000e9680512640c000d00c80107807045400d40700728103070703451 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 947710620 1250 947709370 947709403
    0x6030c0815180a06050d050624010509090615040b1224011b051504060507030c0f110715022103060603190f0c1e03061d0417040f06030e 60
    0xb12001200031503001181c10182d030710310003d44030360380c0c0d00480da860040c0f0390251043d130007800410200d584405891254010401000e80701c0150810000c0c0c00c2e8020012810301a90342d010000f410381e00c5d1203070444500e0904610803501c803540ca02c2ca200d201e0380300d410f81103a0401d00300080794400003484000c01e049890351619a204501c041d00440701c0c0702c003031055170504002c110109800f05900780420405014145481c5c241860503003413200580b800905240c0c1010b1501081980f2079a000a001a162a0607e01161280700d1034103461310b0800d240d089100707000d04072820990201c0d0002030110700c084c105040110030074546030b40d0401e2408221642900b1900400014400966850b003140c2515413aa000040141c0e6100f000421185040d200741c01092241c04600036048001030001c1e4024940d14041c00024100783d10320a442c1401d07040f869000481a000c242000402c030402001410100d4407948c5031540e409240389580861b10841000ca45454040403a0a03000308032101c200d0114203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 947711870 1250 947710620 947710639
    0xa020d0203032a07080406171e0411060c060f040209100b0d0b04061d010603060503030703020c04021b0607080109050c04050f0d14070315050a090510050403021606030c0815 76
    0x10b07882250f441e034181c102482c0440c108100400180c11202400280006071f03910600b12981c56015441c6201c05030041040c268400342c07001c0c4c0308011b41c645541c8190f00107444860340600030302144090184e140c0c0c240c3349025900c10000c4c1c03004140c50341440745000700c80520b032a48414841b058820190f003c0d14150700010451002e181c1201e0b004442801d002900015002e591014101d0010203040851100b684000f0010050300358140200c00140908501651605541c2d9030069621074421030468062a00842d5054010607004042e03000c102e031a4060b12030910303164100402c1d40c4001d0117042c01e100d2030900800c00148461007541c060b07600c0600081c0c50501c14500700b0500015111044958142c01011b101000005000d44001144181002c4610803051185001035940003060300103c24a08110030002c00c200042c2c01400030b40e014000101503d550401700e081103802c1524034201d5140c5400001c4240d4035030310110320f0365034950302d1400030384407c44001d0100b00181452a0f0141856 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 947713120 1250 947711870 947711911
    0x111030705040e071701030308060312041409041103070305150906040201140d060803040915170a1509170726030a0f020c061005100c0206031918080a020d020303 71
    0x3d008144c103d841030030711040c40342d0304206030ba40c0300100360400c50015140700d081c00121301b03003048100134010703800c545141002d0038410920207410090510920801c4c8000c0410103201a85000d4829000040c068840141d220700b80b81d40da41000609140e4410380100c0014107455010480f00e00450b416540c402c210381e103400c40040300c2d8211452000105540321400035454000304010801858040c0010078098045034140c80d4160311036201c0541e17820000b900500c40800403452029480c0e00650b51030440c8000f803601c2008007000107001307240000550100b0003c03130701ca00203031844511a4441c80f5000078603030416032140c041402d581c0d00910b005e00119400d00c03810b0700045541502d00030010300f03014900c3c11903403034203074151440c0180401c3e003901446181090860a84080340310b0038280c6043d0600d60101d000c07840010809020b42c004080344000703540761a0031252042496105124010803a8106550700358000320f800c401510640400008442c004401e8070b1041c402e0548103600b16065 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 947714370 1250 947713120 947713139
    0x908070303050c100501090c120908030f090307080c0105060a1e0b0c0a1b030515130305070f020301362f15040608010608010305031b0c1c05011103070504 68
    0x7078841109004110304051350a40364402c1c98002c02d00048041040810b1240250090948644255010782085103034404550360300c0441e80c10004d00d103540d40c000d55030f04c4191803c0d03000d80040200410300000305140c010340305401c0a4055a012640c40c889aa942c18600b0807900181e031059005540d500c0c020480f400ba2240903114500614040d83c3c654a0307180c0d2003110400707141200e913a900b600003e0034014080f0801c102c9034585404000403005003482e200b12812500d203d41e0003020004005000c104100c0320040b41412242d0140091100251a00481136040d03e01d000c0380c0340345d01181040c015508003d2844d0030507650061031400c503051000756601c3d40c82281101300075000440c2c166140380343e1141410841c502c03803441a81c41e215814050010031a080c182c0c040703010004040d0043c40810004030859203483ca030400546170307102407045198184076040701e500f030340201c02e484164481d12400f8410030400b4440c00c02009459028840300ea81030206070340c4c41c00054414481484803414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 947715620 1250 947714370 947714377
    0x80705010912111f02012406090b0d140712111e074101050613091407080102070b06030a0b010e0a0902040903111506060a030b01050f0c030406020706090807030305 72
    0x1002c0c00d600b100b02030342068041c2c14401d4034140c20060f0740d51000c4242c1c1f034071032850320885c0c040c0802c50301050358541500100106154080c0c06000030300010300010307510060344240480b01c003c00c003100c031900c0c00346009440319503140300c041c03511030504410301540405801151001e400c60004080190461b620740300d800d4200c00307c101c42507411405a81c00348029110b26000c05070481107031201c100200c20055102000400c1c94603941e038108014001070787c1d28003089109429030004001a00c0629081144a40c01d52400c8014603006101c8041088441034004000c000e0081203c4c00381c81d115801499580d282d03030300c0040c1c5500c2075400140000400c10f00301a81183d5a03820110b01000d440c0c0018049466045046000c1484d0120f0210581801d00c00480000c020640b0005546020404075403248074010100741015503551680700d50b41c1c0110299140402d0022006466030840070b109585c982c403d00680c80548158100091031600c070302450000e942021020b8280c4500d10795094440740c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 947716870 1250 947715620 947715653
    0x3060a1515140d02070c210f02010e090411040c090e0c0705071a0315041a1c14030301030b060a0f030f0624090b030a03020a02120a0f030801080705010912 68
    0x622481202d5151800710003800070075143e41801680e5120510340f1910051040e4006040340e00111411040c000c0180704415955401c4407445230408500d100495035004184c1010360301c54808400c4c0001d104a00c8100c03030a1440588040001034414481a0345c003206c203100d60a11010082c0014850300b1600c806024201d228100b2030703408680300c0c1002c103d0300b440388111004030200401081040e140c900007280c4109002c0c0e900300007280120700000c3d031207082c84852a00603000e40b41700320300301c0c0c100c0808464000c0c1c12516180b0b8264a0350072107a00d95000380b10035100005c009011031103e15100307010307508076400f50503404040c0d03181d0794541140300700c00341d0240c40d000d9542004545518425014100b484143c01c00445101d00b81100b031000c880720b41c05558000c0c0e00c10000d0100090300010800d81c810b4048031840154650a6405480c2a51030781005024a449484207020113401400d42170595103003000740d5644940740c1f801110920050b00c5000e28592922049001040c1110b11445450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 947718120 1250 947716870 947716877
    0xb0114010302190203072f12190b27061305070504020301080d0f0306060c140a06020f190f08040b06120d121812261503060a1515 57
    0x4a01c8030202000048040341e55805a000000c001b420000c0740e80460b0f40c41a441030040d10040302c24119800c4003802d0310081d9004802e22980425103120411407030750264804444946410304a00d00111500340070b175500344007220070300303621940980300700e10305020240c880d001841182c6d02c00043c2107200328004e005407494080c001c80881e4944070350000718080c0c2100b10040c490903a01080007007141018031a803400309441c040041c0401d07a448554074913519003010810112003904002036040c034044540003081d90744001125000b410748a00548204441207c8064483e52514010380b035140207201f108000030042000580051002075911303030050000707030604056021101080e49092030f80d001a6001c200009400690000c480c01141c4200720f1103041400344100e03035600c480d00310401c501d40c8020303c43d1403030443d282c0181c54001640250720010000c16203003000b10f1980c0452050740202c501900400c3c0000751001c503103014010301c0c00d840500c1074a40038907000c5d030011171840000c02607042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 947719370 1250 947718120 947718127
    0xd021c090e04110102060714040504020a0306080a060b0307080106080303040b1807090e010b0303210601260a0509010c0e1e0d110109081f1d0115060809010204030b0114010302 77
    0x401244080e40784142c0c803c1d1101101580c102001a182c114010310500030400308030702c0e071011a4018029a4110350040d90050b0301e0ba00054800d4025100642005880c0c0c8503080100090104603008a030700142c040d01600e0005031075845850a0703410074007030382160354002c0010400040b44818450360100d03018445214171258ac02900e4181601c80d03010303041150b1141110045210203105034012114103d00951626205030380c04a80d45403802e0004d90ba0641201c0007640603401202c2d0120120034107502010206001c1d114941508800d03036122114520300000030340001c10512560914900f943c441d800000b1a14042040441400500b0800c1d480041c6581c07000740c0380c2500503480c142c480c101000c903400c00d00c2c00040c65182c03d43c0c009074039944a440c03d43c02642402040f2603a1a076114004510185008030f90022040e401c0c1c0e01c503003d9807034031001d01c0d0086802c480500c1070720995aa40200c1b52a141d80d01c50a0303008600002d07000d0720720707940101705501444040000b00700041c1000341c03c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 947720620 1250 947719370 947719379
    0x605040504230705030703080c010e100c0315030b1b040b0a110d02160b0f1b0c090106031a040b120105010e0412050712050c070b030108010f06080d021c09 68
    0x1503540548040b80d00808081078a03180c00340c1c508440b003482c60030a0080450f54500b0000130385c0c07683c0622015012580028048965042c06e404c101035680d80d04003100d0030990318848110082c03c07031104071030010b45071403411647c2a58840c1010112604100a510b0940f01c3c9110740c4840c0080c0041280d006100300000115800b4610203490400000c3c4c84201074031404499590602e1604882a0115000715206044030070420f5048400c0d1140c00d42c0094072095001460720591203034040c10701030751000d0352805095010024100c1c1d00c1000651b0081d2050340d90700310503020354400ca01d011070740082d00221082282051fa20040c0c031000c0081002400101c210001d5084440a07080600400001001c000501552100b80000b4002e035107000c3e80313414010b03100c49001d8180c4540c0c5001304030000820541c0c1e81c0003004190301800011045a5995940d17840940c02054401540d41000d0708005000030f5444001c20520252802174011300040b0201450190303040f000c1c2801c50042c0140301c40c0124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 947721870 1250 947720620 947720629
    0x1080402130e10060302040b0603040f12090f0902030910050705091018080102070209130c061b0c06030506210312060d0606030506010e06040b0a06140c0f030409060f0b070b0a0605 79
    0x2003104501c030800080d454114010720040e62148c61055004c0c480800c280000070b45000e14080c10103070444441c03100e425a045d01240c109000d54008d04448002c00b8011403010180d5000314014070b01501203805580d004026881590400c48000d00450310038030180440d81051710290b24000f0702468080070543c132403c2d1200407030480d500211440c1c0e5010540d0030450801002264100200107c50922454180e88441076031a490055004000c2e0800005140303050b100e404000c941e0740405043c904640301e400090041500300c512500c5041440781b106111000100c0c01c441010001e0055483e240c0907040d503490200020b012650000c001602e1031002c500306200307901c040c51140000d05110352500a640c0682c0760041c00d014400c03442c104c030024007543d40301100011140c40b82040100c6640010981965004081d00059103001d05244e142101c200403005100740c0d94000000c0044580740e0f140d1115202080c0240303840714900b0442c87c008900801c0380c90f036004c0051400030070110b45600204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 947723120 1250 947721870 947721883
    0x509060402040c140310080111130915030501022722050601020c150c060114060a0c0611040e090609060f01090504050106030f08090a08010b010e042c0307030306060e01080402130e 79
    0x21007850506d00c000740b00d00102070040312400003900840311304207040290b40340380d64030061142c1014140d03a001070b549988503400c9003000842d0840e00854481180000b05135140d01c1e180b118a030500c2038818090003526001011508200d90501a590000b100d5051b090007400090201410742c400c0c4040c0800c10b030740f215005c0400361505180c46480b4030045407044d20340241038100b072942038000501002035880d840c06a8000f0f080d03074034003071130928100e00b081c034020b007000348151850200c00180031403224120507100380181d0b0040c08aa805a8a083e84c490b2140e505a40c1c40100d030081d200100302588603034018070341141c02000002190740e0303aa038826180510060342203d80782d8020800c0c4941e8030f0500c0c410b00050010000070710448080d140028400c00805406900c00c40e983d4803d4007112040c482c81d00c600641400e110201961401080c030750320f0700165000c5002030708180c80428100d10034044a0b03405001a1200d0055440301d60800c04166106c000102029641d0b95203a01400c108101c103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 947724370 1250 947723120 947723131
    0xb04060908210106091a070201030609021902070b0304080910110106091d3904020301030b09120c0601060c0f1703010f0504050103081b0312041b05040509060402040c1403 75
    0x20b40c1c0b14422018004501c08030140e00c0340082c040310f6035080150740f40e10f5131b4a0194462080f591560364150380300603401000e150b048200c01c64404203401c181900c50130724150400f030300c0307400b202c442d20b544d00e003101c0d06803108850060107400c007404107484506042030800341c1c02215040c004038642680c0082d82c215007241e07202480c19600d030806415003150100204a418100d070f000f41003030b0910201c1d021101c40314138540e02042c45c80303c11014040004440c400d19a401c00510a42d9a540e481c01c10042e047d106490304e0785240a81489880003061482c11500c002074200090945607107003903015103c0c608101d40603207282140f0b102100000b0040e03042c1c1102142d04480755038984d41454180c110b040c1c410b0b04164021460480184041040c48060780c1d404a01100c0d80407000c45100700c46400c500841040301e4802c0c51030740500041010341c161501c0911441d041c5406100c2c0d4500800003a948203132070f40c1410350469804180541070070f800c003481c82440344c00d1080040a0715489115135038000c580 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 947725620 1250 947724370 947724397
    0x30203040605011205121c02040905010e0624071e0c030c0803040815090304030b0709060e0427060b0a1e060905010906050901021c050715180b04060908 67
    0x42108024031842643d0161081c00c0d208244640c0d607a071005c3d0703101c3d103c0c01c2c0c0b400120b2000c41c210303092501d0403201c008602d01450b0150344030f0707070785889007006040c00f070103120194802136001035158102006011620007020f080b00540c0c03e180002102c89a02c00003094540c820010052a034401d5810588219244149801d080b901d246090442c0c040919410840c0340c5e0700200003c00030b070000004c0150740c3c0000d109001c071403521943ea0040c41d501c11648010034034134000c1c081100054028250004407035850b01e41d041461003200c100400c6079850790700d07100c0303a00c011088480010707212040104800e104020004208481f100041c4569070183e1000d9804d01c400d10480c000314403664030140042c0083d0400c190110309010000c1c091023018041c2d081040300c04121541c80703038400c01002800d014403d1800c10009800d03040102580e10125094551280b940158032440349544640d440241050800030074101c502e9445132640c802c0a40301b0703154151204018404240d849005081038003c00c1c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 947726870 1250 947725620 947725627
    0x1218020a0311040f0e030405120709050705030702070807121b0905101805090a1b030c0b0702010e15250507060825050f0d1e020d060911040504020306060c0d0302 71
    0x800c11098030184e90148218608001c2080f82400c2c0c00003d660a6030800c907604819503403a041a5441d10480d640116646406c00d4188422690044004c5005007060350994815540b5400303100d81d5400719102e0320905910900c444030208044004d5900c80500f454540d000c4107565a2000c01079440a50b060052420b052a04000348458800028a802000340041c0400d01d013201940c1c0c0c6800c4401e02c0a840da841d4a03401900c0000707682c00800c09503030b2240c2500ea03080c0d1219040034282c1c118007001c0b804a102034948010900d000300f002c01c510729201081c549044146000400b40d6004c070b02c0e40c034010007485110340c80095414000700340034080b107a4aa68691600080080200740c40201d24241d2a5515620400242d800400c940da0806444501aa00c50804c120000200070f1113900500240848c00c19680452180c1c000304280c03441c0300c034113100300741c0c0350b003141c008903154240346600d1020204000c2200f414150040d551100c0010070007820700102d04206414503145424810001c0d9000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 947728120 1250 947726870 947726903
    0x5120403030b01111e191104050402010c050304081c0c120e04090203031c18030203030c07020d020d0317010b0c0c040c1107090b041803270f06020f0613031218020a03 73
    0xc00c4801e40d1406c3c004981855410070380c44000e165841e00390820301894a0384002405d590060700d05601759544002101c2c0c1c1e4a5582841c203840d07145112039a45141c6003440707207150092260b2080030b400b41d0407140c040d4403040c8801c0180c8915a40e40481608a500e4007203900c090b03581400a0500c941c80c040c0621700460f03410003414116811038105008001c62440e4a002103680002a60790041c0207403000b0361b4071906e900016030f1880030504020351002e01002a002055482884030a500c40300200d03504550740c0316a4404982e018058070303c0620740c8114800d01c440c2c942600661544202e60800140040c16641c10f2801c1c0201ca030080140540c41d0400c02c10311b030511b071081c8041880c5600700303902407800301c0d50010000003079581410300100a0b0fa02c01d01000c00b0100f1810020003000411003041540c500020f510340082c0342d1107070b040707014040004110195040c4460262640340d925903807407140070201c42000700b0442060700400c080040380d00005881d446c1d90300c00030b14080d072030010311480c0c0c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 947729370 1250 947728120 947728123
    0xb040512030a0219020a090501090f0506120c090a02070501020316020f06010e040b06030c042c06010f0e1806011205010c03060f0909051f090b0705120403030b01111e 73
    0x1150340c20641540200b215401c52540440d81c0c800320131141100b03421900b8030b40005410381060b9042601d00034a01400040ca05003107038000c016900c5c440000f4800c0d503a41d1030401c10446240b5445a070650805078162a9500e03001303d403254081c240301d00c01400d0554a0300e80900326001100c1e11700141c010000c0104031503404012100d034400490380100710540c1414020440c00f280980003c01103600301000ca005950240802c480d012400703801001900d80320303070602548070181ca0003e0456140201c504803210300200e00c9a040c0c07840c000100c141c240c03500b01a452078960050050280f80c548080c0d20b8090582031003064000c0c40c80c46140c280d8440541005400c50389103c10103070500d440d18500304002c211440c0010100c1e17002c2180052514051b0030b0103030400c41c812503c54004020b103680c81820307460f1588502c0400e40600d41c20503041d510301c00c1c00ea038580302c1d0040b1050a51003400000c2e001900c41d40069104217011301d80b003102d451080011038913000320b24001242c01a01508110f488030390 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 947730620 1250 947729370 947729389
    0x30921021e0604151a04140613050105061602130e0d110303060307031203090501110304110126040c15022a0d060b030c0a0906080717030d05100f0b0405 67
    0x1140c001501d42c0703003010307615042a040b00200c4120f4003034070748010755100c3e18142c18940c000c00c0050403d028800030a01018070642040700e01c00d10840803070341c80340c840c55114810681600c80141c0410324280c0800031040f8040d415410032a032101c47c504a04030040b0700f900440b482c409241c401006003c402e900090000650541c441d811a4810b004001141e64001440000c407600211030521860b20400118050007108070007070019030030f20100b000010184001544a24081c04035031001800d0240111101c00c85192104010038210520310401030003403810300c0e08507200c1c070100494030769541041c120500d80b41c2419400342c1c105111004c0c9100d10300a1000c55062205405000c40d5800000520784080c1350314081d20142e5902542c0701e0b0703038404001003a0030540041c031690bc0c8070741d11002030004e030030140610b40c1c4502030b009000403002c01d080d042c501c0c0d43d035100c809941000903035007940c8003c2000520501c10b00d0090b060002c0c2e640400800f0740302030112141c04654481c100000e100302c4031f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 947731870 1250 947730620 947730673
    0x6070f020a150603200405061e102304030507050108010f0e130c0909020f0f0d06200705030c0f0102031510030603060c030b12030306030312070905060d020406030c090302060a03092102 81
    0x1c140462780410501606241c3d0032002150591030701044038100700e404240d52000b0f903516000d40c0350100305034038000c006002124840e10496110a4507000111481c02c428030a001c2541410034080c40088141189640d00540c1c41d401b1101844094841312018100b80c0e1006100c2617940d0203030300c15030915008280c8118003c1e03800c01c800000c0d82012502001151002401256550403081005405540002c0c0b05840c4001100c0c2c40b50040d040c03240e1a0342c0304090000040c4100ca4424429400600a49104032115020f80740340c2e40320501401100180b178041582010740d03400e80030000416a109100204280760340c005503840030041070100440401c1c003041c00c16801803040085d00c0c0d400108071540c8810035010b12103151120030094400049603004960301200105404d0424801c0364040c1c03007207405982e0184000000e100e03061740c01110901020390060702c00c22010459a00036048030300710910810f0780d261011a001401d22010310644440340058010074201c0e03614018060b102030000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 947733120 1250 947731870 947731879
    0x212040605150d02030d05090103020d15051f1d040b280b0301150c02010c050a030f03060b090a0512121309230f040816050c010206070f020a15060320040506 69
    0xb0030f0507030000380e502d440c3c1082da2001c100c000548800240d00c40c2d0140c49440701829410b1050103001c07000400c1012403070107100e0141c40c101c4103039180c22001c131291100c20a015190950f401500001d059051240711042c0c40c3c003d030b1602d22803441500c4103500d80401d00b406c80a01e140b038040c034202e00305403070550b41e03c0707c011280284010300600a036803004144c10384d420b00702607611850360720041c0c0fa8001d4409002d8500d01544003510180354000c40303000310510007a074003003016a880d100030304039500619255940041154005101900f0144c02c580c1c80f03c0c00b03c43c210b5814800400e44804c2e0340d4440d404000c20a4400901005106040c0c0100c0406501307400d0040c03200c44a100600c40754200040c5044c400c036100101090034009224110390740080b60403002400300c021814903540d241030145011380140318410010368510b2003000304000200711980641150714264550301c0594111210760403a407a034440000000894000d9071043d00c807070300840a541c26104800b0042260340c02060b0a005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 947734370 1250 947733120 947733139
    0x604050d1403010513060f0b07031b03020c01120209030703060902040c030204180903051b011406030606061b0c280f150c2102011406061e0d021204060515 68
    0x3080d80c5078094a0640e002a60b1400b880c0002007201c2c8007400c0e075075200000038104140c0104032944a00b0061103245d01a813210380084404425040210b20024000340050300400d0f05c4003220740c425500325204890300e840250403c591500042d080c8460707036008840c8030780ea541c03106085060070b00500f0305801726802c086007060314280b4030400a183ca0110140990b940e2203040007014001c4007694104110707100d56192040d5098100c6c0c1c000c2a03101c1800c00600140c80020780746d45000039a051103080081e200b40e04129001208010a44070740407040102c0c0210700c20b81566455080702601c8000c203003c125400c10a180c04000d14001c071035084640b901e0000c007030900020f0a22074145880320050b1a24044c03880050070000c1901c60440040083d0001e4a41c034001300701d60540000c0d14006181c1410313200c41c3c6812003081400e10074040900c480c01094040520840022005806505004403001d80b0342485810743d46150b540c1110100d80b05a0350b482445201c0c1002428400103450550306601c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 947735620 1250 947734370 947734397
    0x5010c170c0405060a14040308040b070209091c0f09080a0501020a1e050a0c02061c200909040204110c1c0324230307030602030714040f03080f1b0604050d 68
    0x30701e4418241d0901c141b0407004100215440312000f00c40c000c640215951f512103880340d01005c00c40e070229100340c1c420341b01000400c4c440072010982d200401944100103500f010b602c80c00341c801460490f050010f10608010004100340140080c0913024820b400050307440c218880003808449007101d07d815201c4051520300080703600601140c4501c0c0c03907801d02e1b031080d42180c07000035058850401507100c50b281000b0800903499564000702d21a000c4002d44030f80710354840d1a018841d000e0504600d6003d104d10300418094209a84407000303c03000d4501061401d5500b01d0307240d20b01483c01041c40184490751110f520700c0c592511901310384000402d241c040c200b14910703c601c000e80441c00b8000d507400b060018580c800c1380c8a03c0078442d000019003541c2d2009d5036400c2c0307500250002c0f039001010510341500d0648500803501100d06846040d641d009039a41551100122504007082150000c002001491030070346030141c1010b0800c3c0e030b180080c0103d00d0180b81007030501040c8200c08081c4100c0403900213 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 947736870 1250 947735620 947735629
    0x50f060c07080f09030d031406010c08040b250c030c06080118050a0b0d0b0907050f0d0f05010906020414151e090d0f030203043f050a05010c170c0405 66
    0x4004035004111951200284481010a032140344030f0940d051041c80946c2c100d454168005182c21034035040444c0b01d5588820040d500e1481c94000106200360070001807000d00390001c082c0a45542510b494800b9900800c050000840030403001d6030304008070388003001041000d01c0440c0c00b42c0f07214645a040f030351409604e0410030000080e094280d60700c07140044e02000e450ba003e03040c0c02d400241142e50740c00090600d0680381200303507030549403801254000714260074140c83c2c5200b150405002e940c020a0103803949480b00b1000717401155195200e100580c0890464006403011b041da81080d228402c0c1610300f00210a1080800141300010074007045030b03500007050584180320003605901e9910810b001c0010301322480f07010700400141e5481044000d16034004003805c01e84102c40f9003655800c05013451582c80450b080d88114000d90008000f02e5201000209007101ca4428012581ea0700d501e6034a4a083d01c4100c07403064001b445041c0803181c01610202c410341c22680624a40c0d1904e4200400708 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 947738120 1250 947736870 947736877
    0xc020a03050d0b040b220b040e03190512010308090102011a31050109060f06020a0f240e061902120f1003081c0c05191803140109050f060c 61
    0x414003e90328a016002511507401c810280040208031003000c107103120300300080032641103004104030302d0050205002d0429100e031000c503001d170a0040d81401040084888286017429010b010014288140c0350f861002c00140f034080c622410481e92903034580c4000a0845908001c01708030407002031500902034851590544224501200002c80701501d018112030710802d01000c415064500800041d00201540c008810740e1402c0048903002513844004036500c484203c0e001c1c0810f00000c0e43e0200007011800e601a18028188503152100b210503005000c8420002c81514190480c0c020030000c5450500003015213a001002182043d0076035410785007003d002810041c6a020100c0030607202c0c0c400907540402568450342c100d68032414201240c00600045188032501d608002226108900070780580303000480d0380e6201c01d004004480100c5111181060106030030300c0110f00800800c841040c3c000ca400e01e4440042a404620301e080c6103456814524455660020b0f003e000c55542c200d41113 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 947739370 1250 947738120 947738137
    0x201031b090b13050d080304020f0d0302061918030801060201050112110906010215280c0e090705130e0619060801060c02060d09110915060403150f050c07060c020a0305 74
    0x182d515070340e044410391101c41598000c1039101c4c401d201a01d08121a0748001d40c030030392099950210b0010f00106004a02c00705200003005a0040390028174003e0104040c40e000900401c400316172400c0c220101507103103400b40c0003580011a03c2d801480096024024640100340502c035008c0030321182d850340e40205c113084100074402d01d070722808124168802c11041d076410215607441d843c5030901c000b10f0f01112070302c0140b42d01d5155450a160558419511517645100c80d0340e181e40039031102500800c030b0881d40003420b99052140c18400c0d450307122540c0f04d0140c0a40522a04201d0a0a01004100d121644440e069803111408401803201c1c1303a00005050450306a070401300c03002d240510001d40240201301e030340041075180954180500441c0201c00c00d1207182550740004079102d0b03d085500342c035800859250060f40411003040040d40c1040200301c00c400030040000c120007144801c10541e18142c6424421a50214030001401518400c0a0320802d443c0000c08464599580287c81030188190 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 947740620 1250 947739370 947739389
    0x4050d05040b0a122711030d0f230c0106080615180a021207080105120a03020c0d2405060a0f0e0403050f090d12021b09010b0703051606090201031b09 66
    0x1c1d5200d84c40341d01c0d00b000a0b00c2145d0703812998100c81d1a0000d02c040083c5420581e0148043d0400d02030508010a034400c5035032079580c6030610030075800c0055950012aa0240124180b0006c1035010340705540c002e040b440c0c810380d00105000b490000c0139460a000601081d05000b201806d12001d035590400031880d502045000202690f01e03008550001e0203440d803ca04610101e0080050f4a580301c200e550682c0c10485103400b003220815802965540c0d1030b500280540d000c1e914081d11441e1000c2c01100702442008142035280005114504101426418483c0759480c2c034140f02c1e0b54603202072240003800c0401490028140f034054003500d0080c0140001d0103003c00090100503481d8880100da41c04007010f1701c2400700c2c910b90304d00a411a20203446074001070140e1390341100b410009080001d0050402000d0101030390a203514901c0640c0000c40844c00d02c1001c2081040003c0285100c028050040074009003100c0175000140036240340440d950b100010000c80100b0868000005006503a032111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 947741870 1250 947740620 947740637
    0xf14030a03110a1205070606141503060d05150405070501140f070c0e100501030501050a06021b01020c0a0e06190b22090609050901140c0a030c021903050304050d05040b0a 75
    0xca8a04000030750501411548482c01c4608135140c1003001480e802e44540e104002c115960300800c3c420602050034198030440700c0ba0580d58005501c006150401c5004001c14554800d690310701e131503c0f00c1c802e508806c200c0383c0020001401000d00152001b08002c0c2050300500d4810800007840d40b2a140910b441102c012a1150901c440794001c1c0001e05890a0b000c0540e0030418100c0c0340f10f412603c0f82500080c04e000c004101c50038000c6e450012a005a001442c101480c9020310008030b40802c3c138a4114890424123504a58440c0c1c240c070010319003040415021304040040c4107070703a41d440c114040c01100d481c1e41000074181d504225441868800d94400340012600200d000040c407d0303104840d01c038104107012440d001950300184c01500403800030045010140d04d1581c00000c21030b0000c000c104184040e0250600a030171504030503159105407403103091b840705018028032000ba4250300160380032007000100700e810081030ba04a02d007401e02c035040515003c00f103045803280241d240304119120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 947743120 1250 947741870 947741897
    0x10f03090f0215030f07030608030706020304080903150a0f060e0711160b090a0807030b07052d0a12050408030613021939021c17040f14030a03 63
    0x8440c6851a95402442c009605025542d9141c0c04e4000f514181c00b42d4002401181401d4020310610f01125001c502039070414245072101002074000901c1990030000030059501c0d0765070180a600d03c941008642c0c0301c11400d040c1003a408850945c100100c4d464a4080144107250200014590110039450704441c03a000300324040781002c41550346600c02c0c0b2581c02001c5505c0d80c0701d002804040209032554102c1d5a0360f5503000303176a50214400580190a5180882c8142d03101c1d10041079422101905412515500081d070521541c0c2c030b04000c03d00c4480071441d845052390040d150755209172060024411400c0c40d0702c403207035907201c0034201d6441444c5800720a12141c0079601510003c000345120b04000300d0207290050807a05172602032210000e100036000030a02c2849582c2c6100c9903580c13524402068040d0f00344485041400f42000c41c803081c0035590070008100c20311a140300200c1d078502544540c034124107045420754a403c00c1c268614010507803080c580300016441d00e1035400d890002c080e960b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 947744370 1250 947743120 947743133
    0x305011805040510090b06030d0c080409050702031b2b0215060118031b1d0a0c090509042303070f1b0b12070206100503100e030d150801051302010f0309 67
    0xb80901000350701c0c10040818144144d0b000f1b03040c8501020f5081c2c5140c0003844000302d4055141e800000c1c1842018003050000d150940e110940c04402801101e18090700e00e030145074000c2d821b011404240c3d0206813070354102210a00c007004050a8500d090f855291190000780d22080c5a1903e9440d9041d81c0c400240540c2c86079000c0c0400003032580c0c003882d0341900c90501c8140051070f0411003406884821000035402c10300d030240d654442426a0000080d150111106c2c0a0448010140100565035501040c207541c0c4814050056100d10011020401000302d417040c0341941007480c002030381003440994042a10031400f0100d2982c007003510381e03992942243d95880d114080d0410343c8500301c0440c04001c000c07203c28200c0d000e5405034081b2071a50f50b6040c240c0424844601a0540580244260724240107498000c40340e0000310704140c03403c000c0c174041d980040302c9070451403600b8282400e4003040426001e02c91150880710504042c40c101d0714980001c0c000c0512000300c81c0c1090741e20707a043c8050012 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 947745620 1250 947744370 947744383
    0xa1703070b040246080a080904060e1303030b100516150504080310080d090504050702011b09030212060c0702060717070b0117070608070f0c0c0801020a02070603050118050405 77
    0x202d5131000d2810100c5240a0421a5407845001c42c99400307040000f0340701c4c6a10050012264060020003020380380f541e8410041d00000c0c0c6040e0080d0315840d012032030400b10341c81288500315008a40050030742ea4280101501d039495440e90140c641681c81c03803121640582182c0503d8015012140e0044441c03030070300030080448208004541c908018071041120f1007006500900c5c8244c03001c64142e8231881305603211700080c600200420f403003041c00c000a05064202540c061280d000001d0300e4114003103090b41500608582c000001c0c0a60018011440d1400f9024170b00340407100203003039500e44541c0c3c841c03061042010183c450400031400c40704121061900d4645011003c5450b81c480f0300503c4d0403010a107080c054904003901d6841d004d2154200060144102c0703400d80d81e001c88a85401900781d521014142801c000c004c07482422001280707601e865440281440d1000507916900c0201c001d00340710964100204060030013004000010a10805400c0341c20300310000070316901c4608e0118074000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 947746870 1250 947745620 947745649
    0x5090315010905100807050108012d0e0612011a04020c07120812060d0302061504060512070807081902010f2105010302091e010905040503070803010f050a1703070b0402 74
    0x10035a0010403040201d41006005015140e2000f040546612890b0b803252103a001d00ea0015021800400000d44809007405015110080e0459403691b0f01d4400498000150081d850005444c2c003803207103d080c000d11080f4a0800840204400d0200b0500e41c811070f104c00c42132500c03550b000b240d012034040c01409404014030119207545d0381d40350149841c20103034000304003014118001c030340050f095040004521025980c140d001d02200d6845030508a501c400305c0300343c40d4000303a4032400400e59848018482100040000007403a016140c940b5042c5040b10380e4115040d50740206117401071404040a1413007183c0c2d42420203550110300c0c0801183d480e000340054100c03207000c2e80203820780c03900b640d48118160b9000752000004c554494100c103802c80301d81190002600403040c01000a040164001c0743c100340704006407440c1c0020b6441e25400341c1c0083e045101070401c0240704000521700781a10000030080710314501c80e2004c901451545a000d400c070054104041003001508541e5150154007110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 947748120 1250 947746870 947746903
    0x31401021201060c030306050d0213110417150108070e04032706030c090602030f2224020c090601050315030f03130303020c1f140d05011202030d0f0906050903 70
    0x10b6a640100820a5144107820f034003003031400c00041114200129081c1c112500a00b444000c0c14034941d00400504000c040c0341c10f01c000c18040851000701d1440c1c448903800c0301d40b000b0001c0e0791114007903a0954806070b100e000103900607581001203603c00707040168041e41508085a080700360340c4103078a2000c52112408082c40c5d8040003c19038903015800841d02d05c0c5075543e04005d56403506003da90320b02c2959103c80c0920310501c0f0032101c4c18105d030b10008a051020a0b5425100e503900e9284901116095442009100d540d60a41140da070400040c00b4581d02143c44540f0350506070000381c624400a00340b0206041210700d105003944040090308282d401e00c200301d958440d0010341c1c243c210711160000320014020800952454a041c010801802d82131480f100150084420140c45e07682d074000429601020a020081d04c1c80350521440b402094080700c0f400045886104040c1452b180c103041c0380030321280c01e500c6002d450b8001e440c02c2c251205d034103006035070f07000020000385800001c95818548 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 947749370 1250 947748120 947748157
    0x50a090f030b0115030c0905240d021b0c150d0b0909060711030f0f090a0b0f0334110a020406031b050612040807060b030f150c1303140102 61
    0x300060741020b02d04031050b03d0301d1040c41c80d500c20400c4040e01c24040000002640d00c140c24000741c54200b40c1803010311014a9100501e2a21a220700002d4200110f90007245502145030001045542001c4104204420107000c01080c4040000c0440c08601e2041c1d4180d54082845040f4441646c02511302400c01000704403a454010202c40c1d68040443e40b034000900552204000310304000207440500501f03101071414600030200b454400c0d004540050303840102034100041450404c00281500c51141844039543c1c40e0030020a00410b07012195036045010403402d00445001180291280c520f40d4a850004062624146071400120100103940540751020003c2004a000c20402c1c168a4100c81074813440e5a03001005014020542404614981080050300040c000f0009000c0e440c0306100000b01c140b00b0a000c285428840058903460350b000e0340b11402c00340e80b1012120350101000601030b16041c0c41443e0406650514400100f0ba013041c0b404140c0b80d204290140c0704c40c0e101c00013007000c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 947750620 1250 947749370 947749373
    0x6170c010f02150c12190e0a0f021315080c0a050a0509060f030304150e03011b1d1c030201021812071a21070908030f030105120f0609011401140d03050a090f03 70
    0xe0300ca1803030342011455442e022500395401f0b03020442052281d0098001c20191806409000b5100d15458103616640d50b660320400403d401d9a00c92070242801c000140f2444d4200300c24081c0e10320454025a00c503901440b003c0201d9074860646960254059071400e041c2065000030920b50f02440c0c0001d10103242e0000702205c9913034000040380f401142107009008440c140920540d80d000312000040005d40c036070360202d407000c11004424884050180110105014070040c6003058092131404400507500043c4000c240000682d1814150008a50210101c00c90503007442c1c0e01c3c18244902c0c400540c2c24804800f240c0301030341c207503910381c0068901c600e0055000002c2c5644914100c61080101e18100b5000c5141c41d0300105440c0c422003410701a501e183d081134100000c08004940c80e4620307100c0c266040031401c0080c031070345024025400c0007141c2d120b226034801c0c080d114144c000044214851500203c556250b043ea1410b01350941040740e130310308041c0c408a0742c0c1c201d2030b00044400da600400000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 947751870 1250 947750620 947750641
    0xc0c0a051020030402101d150c010c030c0f0e0112020c03270924030f100606180303201605130924090606170c010f02150c12 55
    0x5200344074a00c82602c4071200c1c00d070420b0582c0010b0780c01a4200403040c00c82c1145500850684840040c0180c0c55201061520002100d18542c04c601000c0d0706008500b00501000900a0501100090a00717000340c440701100104000354100700703070b4200705101c0360003400c69009055642c02400c00c00e4007955100b41801115035685e00403488800900041c1c1ca004090001f41c071200a29150020170200c1c2c01c1d202c1540b0301044803c1c0b5200c0d8a204c004030320f068a0550b07401c000340c0c940d0b0700c4c200d4081d0005880c0400c1130012a1040e92001080c031520f0f445c480c500b03a0900084200b540d50600f85505580c00340d8560b02c82c0d80300540a01c40c4d0070b10841685105441c00031001d001220402c80b1030f01d011141d44d0b901c680a5690b074080040a100c81c50302c180456041b100c603040170f081101d00d00040c9894258a640c0706488841e4851907101c0d180804500721464148111402d001c020f0802c1ca03000c049090009503601a040c0c600d10868040308013092080c4d808100b100ca0580440c0c1c04440682451841038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 947753120 1250 947751870 947751881
    0x20115151e210221040305090907030f1a10170a020c0102040b07141b18091002040314071e180f14060f040608071703040f15090812030c0c0a0510 64
    0x800134000c2c40c07100300700c03100c441034201303100c1c80d8155199406d152071801808032448010344060309140d00d41200d00d1340808184107221094104580c0d030940a4017440521980c404107440f00000c00100030255040c4030002c04841c1d8021000140042e41c0c0c400841d401802405550086440c042d0005541018003003c580c1a05141e0b8440c42a1009515148008240c07101b801441e07e03088240e2000140484030391143c00c44d84071818009072044641c0c03c0181e00204d030302c1038200311425501100c0c2042103001c02c02808010701103100c507102d495244003000030107200c0c581c401c03c00d2804440311014883c060a41210840c10160a8103000001140c2da428841010840e402800350b48041410b61403440d15010701d070115a440381c05005d10900b080010b5034840342092800c805480704110000e1020000c00000f4000c101d502902d0340c00841c0544000d00141e125031051071036502000c410300d4560300d508126600b0030043d5401a503141d0000211608210307121402400c1d40c0190001d13089588003a800a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 947754370 1250 947753120 947753137
    0x20f030601120506060603070c0f0203150c07030311252603070305060409020a0501050d0b030706020705030d0c120804150c0e040c08010e04031107090c020115151e2102 74
    0x4e80784070f9034032a020b101e21400b088075400d0014030405140d002140010300d600c0f100d203001505940644c1c45a089140440400360b504025409000981e0005d044c1d25200303545000401c01c9241e4504850200c43e403490305418403010050442c01019001084400f102c00780e0440300c402c0742c500103111584143d00d0140c20403210800403c4c1028009a13403031500d403050b034100c01d9004000d07030071150030280115100d800642c0980d8001d599110391600701d6a08028803001064194000d210146c140b106040c14880c8080300b001c10b10170101710380000290340403000c4060000d90310707048555950360700f480310040c104030250190403403608040942c010b902c80c1301d02c2c80401c0180d81c24452201c92100454094000740f0078480000c0017603011800080c840c00e40c0060494400c421968000e07201c07400881120541003610b00541c0d520b01701c0c8140303540c11041010090100d41c4000305403005400b4080d14040745202901740039003c081e800e01c0c209014203660200d08194500180c0300f03840e1100c4201c001c1d80034162 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 947755620 1250 947754370 947754373
    0xc19050301260a060203060f060408030306040b0604030c050d0201031407020f0c220b180a02131410080a021b0c03060c0408071517040605101a0a0c020f0306011205 72
    0x35060b5011108600800d640c04040000d00030905980c50700b1000350405080d0079484003400c444503131719541301c1f40035002038521440595500e0610700c1c204000c8031110052640915030030b00c402c0010075000d030319403821283c5c1541d04400002c0385200403001802184142442d18918100f44031005500240582d217048a50046908034032080d410042201607010303440c6021800f0220f4a012140300d90006918010043c0850030b451010006001e40300404403507051920342d0200d04c08080000c006012001051003406054040400704007041000103070024520502c41c2c01008a01680070075030495040040c07a40d424201c04510148071a102c00c14141054864860344001c90300c1520b00c04220341c126066113006003202031405058a030012000060403062240745822a0880f2086081d50b40c80355106400000305882e100a880a14001e1a0807050034818030300c211000710342c0614225400d0a600c0d080401c6608654030000d95521003d0508541601403a0000608007424040003101e1074030510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 947756870 1250 947755620 947755649
    0x90b040b1b1e070b01030b07091a040501050a140c07050f0909060f1b0a11100e030a110708010e0f0d080702070905151504082505090c19050301 63
    0x18912400c105100701c902840c0c14100700c101848500400081c882502d0070520038100951900c485600000036070064510004070320030042d10036032190904015101d0080c100d600b052803854120064010f502900d410704c0310000b8160a65802090f01c0c2e8500c02403140795955410340c1210a503240d00c003e01c43c0c02e003c1c8402041c42c421510384885146d11440445009206a55560035401259000a0048245000180c0c0a05420050580145142d14407070310303049034a2004001640c0b4140c060302060091501d0310071440b10490b4040100c1d44248482d01d8100705111019083c5402d0641075400700c03046601e8030030a0f20f00e16034080360521a000180003030310f529941031360382601d400c20100c0d129070040e0084102400031541c140d02031908450a034680d50410040da00c00301341258400d1f641c141c010440801e040044103401c10400f20b40c1610041015004030352080d429000440c0c5001c1c1512800d10305000170708185281c01551041c0c800d00c44c1d01d219111390780c88090708a510030b00650701c0906889 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 947758120 1250 947756870 947756881
    0x17070b0c0a0201030b1206010914060402031006030f06051f091205070302090403030b041d0f19110d1709101409310501170f150903040504090b040b 65
    0x900540d40c5018115014000042807503004400a040c90300099a000d12403800c01481c3d6102080894043c107080c00c00080c003000c2c8039900c06050301000340711602c150300420401590f0f410005c0d150044411a040202d003111411030140043d000f29013185400205492001800e41c10b6481c500c4484020f0791101c08925882c2c00828240d1203038803070050314560003510204014184108996403183c00381c6000a032007080034001030140e4040107000310008001d9109528200f2041c00380c8903140d560300d0001c00c00801100201140b24140300005450f08074106d145800070348030040c01804495120400c083c614025840c8030425030811207a1340e0003102030300403000700d01e401400e03100064000b680030141010a404204211401d20720030110300c0b000303107213401c0841e00107104072103444003010780c000f08070b035814810078075400c000320841d001d01e5a100c84916000d42d0b0011421030702c1020104d9000c041039440e00c0d50b036440d501c51030b4407143c0c2003450240d041c410321611641642c021481013821442d0b58580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 947759370 1250 947758120 947758139
    0x10b0a0b040b041e050d050a030f0e010e130204171f05070801031b0302031c080610050306130e060a0c1704020619090503060702010207050609030309060403031805071707 75
    0x11401818003a035000c1000740302c105480c5001076401140b0609400344c0c15141c40100c1c049500c4507801b12460760000320100101134215668146c03a0b40c00749032010269003804002051a106002442d024400c0010070340700302041ca404640103024003900700404e05029010865031030582154030102d488062007446240c6500703008407801541c0555401040c0e900315100d020503508000c00703030954403e00c241e002005803010f0109098000c5444452032070001d2070031001d031030130701c0040409100b5446400440141a003040540e600305009642c5020040341b890480320062a000100d210b00e0300c221800c005182c40150090000e500c142e0b640e0307525003002c041c45032481d01403c1e0760086d1b02c03810920804201e0390395005c4c8001071104034903003111140d6542000c00c0c242031090326002d0060b500000c0e904144442003100e203800100e07920040d89189486e03d40c4d1500c0703050191000301010348a44a4a03115990030084065054101084d11003542d030350410000101184440b8100c3c2d4007030860005448040e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 947760620 1250 947759370 947759377
    0x81e0d18030f020615150d050106090f09060e0c0a020a0b0c03160f020d030b0303071712062205060a24080a0207020114090d0803040f1a0408120711030a02010b0a0b 72
    0xc05c110701c3c0003031140a00030420141045400b0a8403480188a07040c1310803114082c9500800c025110026000e00703090342d4a4901e0301c2a00031950003410402c08101d0b0405031003110b070740f01300d09511160720b035a6103a10403414201c403003030042c01d10007841050000d05d00c0c03190002c42c081c0504802d11a140c42c0260f200b81c1c0e208242090741d81c00758000b140d1034200790703000350850701c0c402d40700078141c0f46400120b0f40e500110b0b180405400c290250085094514200c1880b1074607003100b0111100c4040c0504045070b4124542ca08007514071040c3c8510210b42240ca40c2c01c2c0180c0a0440c0200808074011003a442e100d030b0f03017081c2481d840010054400f1445035400d5100711645aa0180e44a041403070030003c4080302c0e940420425500a81459040b82c0800c024001031809184140001880381350a800d014080c540c501c0c0948821441c040c0c180310019403c1000c840403602082c10350441ca9595040540c1d40604601c0e00c21424040040c1c0700c1c032031581c1940b00c8981d20000b1110b07001d106440e1100c0c61803500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 947761870 1250 947760620 947760631
    0x5010305151c0c0803130f0b27030102040e010902030403031427070906030c060201140f010302090403110d03090c0f15080907080114060f010804081e0d18030f0206 72
    0x190849460248181c80d20a5807220b81c000c5074481c075500d070366000c4036185038441ca801000790010100c01303100e40458042198010455561840d09009581c1d008607440d1a4118141446070040600740040d41c4083d01602c0040600e802004015a550160407010b9030080310304500092500c203021041090311000c03030340214203518250b1004207804d01c2c17080e070405540d900301d00b45104070840000c0b241101c0c05103102031807140c3d0317a01c400c2c240350480282c2036426042c1500305a4000034100401c00392104005070440750115954105a00e4508003034079103d883c3c03a0382c07005500444000c0f803100d58040d00b0010301d980c850f66144c1c1300250b40f03c4001d84d0b100001d00421400c4011981c41d600c100d0f2150b041c00c0d81060b420019103214581d280b0b00c0f0341c21200600403089a40181d80200112880c20104501c440003003800c0035042460b1035560804940b0528000e400d030021403005180a64500d0800d4407079440d00c80c0b8080000120110500075210710f9028200e0000304003850300b41c80700b48045005030242 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 947763120 1250 947761870 947761879
    0xb0703121d0c060a0302192001020406140f1204080301050f0f03030a08040c080604051b010f0f110c0603090f06011d01060309080906180109120c140f06030a060501030515 75
    0xb200c0c403504200d0701d42d00003841300701056000d000280c103051880d1807522000d1905c3e00c07a004480e26100903010445d4280311641c0f07181e407046c4401c000d0750b500322800d040c2e4041d031500d0140c3d4a15400d1445e202c18002c082602608038084020802005811002103040e160200d44a01c8098103000800c144a654070301010f40680003480724406032030040c82041e800c81c0c45100c3c03191150b602c0322040c52400504035820b03209580000e8650000084400350040c44560a28050003004481e0038090b10246070941c1807002c01c5030000c1508019803041c48100d1070480f000b800280c0d80d042402005030794001e0440707004c406000758400041c440000c02042da400d43d042142c1d0310303c0e581c0382030802c0d002021000b105882c07000e8200200180c0350380340e00080244c041c00c0120302c044881c60500041c20008150408a0140b40da10090404110aa4926411100103415a00c0c0086160004c54812031600d4804c507041032022044c4500031040350091400c0e200d086c0d8040126a980c41411000400c02c02443d5400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 947764370 1250 947763120 947763133
    0x2f04080a0206210f0f07030606211b02150702010207020a0e061f03020a09060906170c221d040b010b0915040f06080a02310b0703121d 59
    0x40c10141c003e41030201d14291403c20f882c031811050103003004200c584544600c05241040141c808881c0420703001080d03850708011940c00d0203006070131802202c42c041ca9000036105414045001d0390420050300e02c02d41e2061542c580071490195840140c0c804c0210364612140000742118414400c4d00c14407030f0000c00e40c40d2510301d041054143d090024042035041461003c02c455421400e0600c001d0083d42c5541c0107a54440c4900c0c020400c40c40390708104100b00842e102048500d6100c039038100849450079111500d503d034900810686e10840508110b00f215904618110780c20014086c42250003c01007462510500e1949034002c10007120024884c0945200600640c400b80000c0c01411002031b000321044051504c41c0041608180d0200001d10400001800200c0d4001405904402d2600301036080507803a20350301e114017200030075802c0718656203a0307288001c146a42c0d0500042141d49180d0b980da00301420001d0100001c20710319610305040c0106024405014406050f85616010107840b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 947765620 1250 947764370 947764373
    0x3030301060c030203040906120203150c0f0c190b041509030c12021603110a060507050703030e031f0c08090f0c0f040f05090303010317042d092f04080a 67
    0x28240b12580041d01148030602020401c50340c184110b81c003031b00c1408000c448000315441058a4011201e54003503070003c130b18003441403045188050311b48004011004039101c0755450303074051504459102d2042900c0012100000b40020901503070300175400340300c10115110b602011031082c1d80d8100402800140151601008981e60880d0303100740c208184142c030b006101c5211369090b80c51054105a4011307604d803146003440c0c0ba1400c1e0040c018603c504000303050660b15114582c603000940300c05030a012098072401600d079418401013848020030080907854071855103030740004001d04040303000890390034004544160400034022a281c00b0038002010a62a80e01c140454858807400d00c5800544966180e8041809405070f288104504401503841e90b26604080096086142044808000c00c200502009142402a402e8045404050343e640da040b0304850b01100c01e15800020302528081d0300c1d844545140f048508400701400300c2040c490903000c519801441903104030140c60380807004840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 947766870 1250 947765620 947765627
    0x8090103200919080f0c0f0f0105030c0901030204030b040b0402010216151206150c020315130b09030f040305160504020a050406030b0301090b0c0a11010204030201080403030e21040801060b090303030106 89
    0x241084070901c0b0200280f6510041c0501c0c10305d204040d9000e81e00250f2880e03944d03050491182c292204102e6080c80780c3e005480c0040d14600c009400910400d074001f420b0a01a4042d4048600a41d4405681c0e111803525007040d042c42c44003a502240103000703d00c48041e050100740380940541d0614002101d1610041c80c1c181c0c1c0301036a0000110300c7c55240c0c4400140c0302c1104c900d110f254040c6813600300d12200c5a104150901e4001418521001c2d0f6060910a04c0c0000801c82245260300040b407407001e40f545050580f641c014002d800d070742c03c1c100080c04810404041160030354a00d450307414080c02900c5a0410003a80644060403002620a000c00c012262103604a680c0307011014000013080740300703502c80c03c40c508001c9034000b0780c1040001c0c02c5101141e209c0f1510b0303103105416001f10700705411940000c10a10300900003034201621005804d5036100284001d1065249408040c90310040002d1000c009401c0303880382c0c03200f41d440c1c84400241d040c500801c8032400c21005010b5840c603030034a00c0c1903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 947768120 1250 947766870 947766889
    0x170702090a181b060305160203071e17040602010b090f07030b1801093306030506130e010b010e090105030a030f0908030f0306041b1d12010207080901032009 69
    0x4402e050b071100008400303d241e180e00b42440c07010035240d00d48402d0810f00050140d5202411200c90394684040f603043e419408000d903011254400e0180350140c41c401e0300c2e20a460010200982590601c2c0080350b401000bd03001001258080e030000e1010803400b00402200440480e00d00c0408840300b00010340301c0b031080c1d004504c9000010701ca0700c0c03003041820b061901c94000b41c02c4200b19aa03146c1500f40310600250085a20700c0100c025080200a0301d61a294003260501c00d02c03060548400104105549444040302c0d00b03104001c0c1003101c0030305c01000718080d0070020713407281c04039030301110100407414480c003054143d98015000704440016070f40d00721440740c02003807a04204000040007240c015400e1000340110b184000101c1e88900300b13001048201eaa80d0101009040da8101d042e02000d9048205140000d014040c8070740c000001201042c0c00c95504809080c881d44006a42010030402c04003030492168280d030108110a06051410110041c110344140303a00300c14071003440719203042581c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 947769370 1250 947768120 947768141
    0x170a020403060f05061203040b04062f07150504080304032006030403080403020c0103090b0708100b0a03151401020a081c0c050901032405040911061303170702090a 72
    0x1454a941c0361120400c50f88a4800c0b044000d407208103024540c54150300f0010300d0901400a54074013481d010003200c452089206078814044421880c0320780a1a0030032210f0404211495201000c5d02d105031562225094010401c2c1000d00305156590b07584100d00381d0b81600c4c110f0700254a09805c6031030724400e401081481e40784030704100003404900c1d01c03074002442c020351003505d800c2118101880c0c041c2c2025281400141010b20b842e00e5500440c0703c22403441d800c019941840ba200340c03901c203c10813680d08288c03c10304c02507900240c03000b02150f060b4410459015500e500138841ca480c0c07068804d500034281896070041e80810044c0d80410034030300081000301154240134045011036080c00040e558166001d501061021504c40072650b05070081182c2d06203482d8a5031800740c1070136224500c1d1580d5004040c007aa03915541d040411001d60340c3c0202d806801480c5a4462031140d128080d203412500003150f25900705006c0040c03008010050320355443d801001420702d03075a52180344004102d40700c1c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 947770620 1250 947769370 947769391
    0x90d0c030c0e0a060e04032a0206030106020c0a09090218130b0711150708011205241602010e0a02040f0207021e180105030a230d03020417010c17 64
    0x600000090080c88440001c2450a149420600c2c01c4843c0c04200c0340c2d103600c031168191880b4100000039600600c681e00e03825003244a024042c00d11180e4802c001d800b03000c025003080e030007c004140035400081c5140300b00d008945480402e610758582005850040c0c4009411500003d0717100042a22529882d43c0140b0012030700d4600f140a44904031741c0c0b10292406000700380030181404004400340a0849050440001d01320380341024034004291020501c1003000d06070400300b40138100801484885040c03104484180c038085a44a04c500075001d09803034440812400e003502030381c0d4a006000e07240040b8846c0f0050107105004e902403202a228940001ca0403a03420080348006030390781000541100703131607440000d00d0445402030050307600703204a41481c80440803004110603030b00001c14141440d4802c103c02481c02d8801e000460501c2c080002c0415801480300c20302e9925030544c083d00480342c00c6c002c21810200003680082c00c0300d0081d00007038001200051200e507480e5080c101380d42c00807400c80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 947771870 1250 947770620 947770643
    0xf030f0b09030d0c05030601091211011101111911070e01140f040f090b090c03060a020c1606020c0427020f15070f0b0708010b0d05100308070b0f0714090d 68
    0x50000f0460307403407503440c1001c62030100510042e96070110584e0301415603480c103070441c1031158464168110041d8052410400c42e8002d1001c01a0203400c13940c0b22205661044e502e45600074000d81160f83c50b03100c5000010548c0d40d55565001d00000c090382110400101d1485603400d00e01c01c80b5110300c00d0411140c004021541180321030700e40784a00440300086c0c1500180106035854502411440a4004441c5a000e1040d228041c0c0d008602e4036001360071000300595481c41d03160001e007444bd0880c110506a45a803400060441d008128121005400c80d020032400d440260f02583c0e04d60700c41e603804004180c0c3c400d00401410000f4510b001303944000e109071020300d0b101881c040e00c0e920800c02182c180144207410300800c28160b1010340c00440508041c4102d43c14030044144070300800313030340d0425030b82c5410100e50440a004001d0010b550410800b558468103828107029444050f210890f80c1e00b908000661428441c40d0f29140c42d0711034644041c50a040c2104001000420f520151881a440c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 947773120 1250 947771870 947771887
    0xc022a061c14010501050c0c210604050d0e1c240f0c141227030423010806060307050705070e070c0302060703050105010903080a03021b03040801060f030f0b0903 71
    0x80061002a00604001c501e54030000c69030300c003240b0b060f8071142c14408140702c0f80c01041c0d0080361601a020040e18074240d82e00100611207071075a02030040365000d001e00010300050081c0455031072081221a140d00040943c1c00043c00a484000c400c41303441104142001300004010b03141940c642c2c4074421429109601008000c0200d8000806502449942c2c0c24541012034012003000554040d00380b540c3c1c2400003103e2003a4000300d004000800014088000c29404850403428044051003802101d0300e0301d0b01c2da080001001d000d101c4003200d10725000c0901d0300640c0f04042085c4221005000141142c554501c1951281c10480080703c090040c8003020500c61030100a840c4600d8856454036113580e0903041c06404c2c440050041000c040c01c01006000e40c0c1d0301f011428040780e501c28001d680e01d08892a04400030b01888101031301318018007142d031341c0040000000e0400d5902c400300820850340d0752428807410002d2448010701c510a041c0ca5540490607134611541e0001000b000d891810409 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 947774370 1250 947773120 947773147
    0x60706050403120509210304120507170415140711101101110723030f0a032c010c032313051606020106060e010203070f02150706020301090c022a06 65
    0x880380c41d0f200d40d03ca102104051b540307500f881c0c40c030886002d040a14504051711030f104a2042c0d40c0e01d400034408005090002c20221103d6211104045101c0c29203840d164190030300342507411a5540c3c00245c80c0702e194903002414808881c4180d91201903c0d200003e10300920030b070022046030400c1801240c61400f094410b0a01902c00c0f12041c5000d40341c0c0d035498038508030380d6000c200603112000b030f40100340590140d1000021100109104a20b007600c80f1009541280a000d0307003100c0c041e40d030060a1000c038034850a0071080202029003c007d00c210f04018100724200d0b410103000307400178907216100e001ca4086000d0308680150121a141e240c81d06141c68a42ca070a5131194800710303500c00850104400755080c0b090310302405440c68a5007a038405000000d641e405001009008105c44080440455031a0224003005907146032080380c8501032810150020341003441154003050400002e42e40317941c4041442c00c0050000805c01102d0041d501c0c0080d4500200b00f041500b0590410928410346807 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 947775620 1250 947774370 947774381
    0x90503030706020c120c1e1f0203091506010f03021b01020c060a0609090c23092a07020612091914010c090e070f091d04020108010f030206070605040312 67
    0x1c1802581e5076101e5591139280520f500045606039101740080440d0b0040815480e49101e01022070240d03041004241d01e091180d1840c2c1044560a00c0c1c0c10344030310782566006180301d00080e10507035295111174415080c502800325083c90004003481d03001e41c090750007a80941010107144080000301c83c0016a41030884e0f21076001c0c00c8095104004200310310500f8000d49024000ba03400900520f5216504c1012800141c052198410044422103a00c6200101c1400709404000c02d404d0075410120003045010b11070800075915415202500c00048440504035092503074042d01d2240740040b2610703100d10030400504481c40d04d01900ba071180e0303c0350b034141290000a0040d503203054105d449a0201d400c440c0e20552840520601010401070502d01000c8960300414500304000089400c0c10100d80350a000c1c3c00500381806c7c030150301010481d9001803544910300c02c1e02c90050598a81c48000aa54810310000394043d0b0100070280c00901c0c0740d007146800500c241061001e80707088010982c161003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 947776870 1250 947775620 947775623
    0x1b0c0a0506100302150f03070e03010e0639040312090305010507030b0a08010e100506030a1b0603061e03121b120221071b120809010305160c030f0905030307 69
    0x40b44680180254505815402d08682ca003400b12407502d0141214440140002801c0704180b04040202800c261020740009000c51140c3c001d0b125146001c06a010800094505040c040c80c0490f4015070341c07611018402604113103001c0c00a040600c0d40c1d40350840c070249541e8030f0080006500c000800140240903060003105580c4000ca130848400050042d903c40c1035205081c141e0500004440d420408124010003250f20a4040345655844010038a00840030b08024403e03000507001c06941c2c02009496006d8034500c0d9130034400300d6074940c02d15200760001c0304e9121481214210400014000d00000350120b49507042004400344140c05170403023403804d40010796501c0b03014480010b107181c2c14020031800c43c1c116043c02509501403298504203005038400103180f1048003016400d60140001c0b01ca00908100000004c214420310f07220b206034000c0c0403010301081c14480801e44001241c611840c1c0005641e856070444100c54500311a520103800c0f034401070104010f00455181c40c280000c00303215 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 947778120 1250 947776870 947776891
    0x30b0c0f0c0c01181d04142505040c020316031b050d14040b04030807020d06050c07050d0c03080415060510020c18011d04110a141002061b0c0a0506 65
    0x2c01c0d290300140c910842c0d030502d168a84180c00c818042200300f01420f0001c0209039414030015601d03468694903010b41d921183e26980300380c1c54170003040740c880310070303c100f1805803112007d030296074a0600c003e48480030513800141e041400071214407121000380c0c480050003441c10a800001e2900001c05100704860142c80603002642780c1f100303a50b04220034200000c1c01c0e0364030624013031520030364140da4040e9010042106200280e220155507402e0000700c290307038001c8820842410401d02784040c1e58002c100464442c080c10020b403030b0240c022859240016019111420076548559481c40750203d0400b6490889664420100703240e200d240b4424000344080d001001011401d004014141e800038000a100080c90001031000c204540c030951040c100401108519460340c1c90a2210040800308140d008079081c40c00003460307a00014040510701c01a0740c40718151072241030490311004121080045501c18540107007042240d0740040413043e0a11007501e440c240559549800c1c508103584d640c004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 947779370 1250 947778120 947778133
    0x10b0603010e1f0f0905090715030e03120c0306031b01020606041d0a0b0106170c0a052d03060103110a17071709060f0c160204110904090506070210060f030b0c0f0c 72
    0x117800d2140c1a0402803070402041042c0c6071078540640401d41c4160341003007549503d8201300c091030420940f202007071150360040c41880c10740603851036074004892541c03091054904042034001240700c81c0002400c1a405807055586420074080545801d1440702e55044022034400d14007030050000e0400d1034481c01c00c603126940341c070000418440c04000c0c0e03541440b1031002805980c050101c216101c1484070700f440c0d0341310b842d1250814007080340034001d640010b9000c558083c544595000071071181800340c0b0304028001e01003ca00202e4005c486d540008588440000c8087e440c00038603090303024200c3d00e0840c407048480e03c00c045c0341314130a640350000d9601800c144000d03504444c42003580102c122135218107000115000d0b41094001132400b0340180d517110304a0308400d1240c0c04032409000060014042020a8a402965120100c1e0254010b00403c00382c200c080c64107020b050700310790324054803225650450320344000b465000b0b003a5900d402400c2008040d2050b4400c00f070b00b000c2e900d40b409000c6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 947780620 1250 947779370 947779379
    0x1e10020f011d031e0405030f0106060314060112090c09140912130e060102120f0304060b0f06180d020a06110c0916050703030e07120c08010b0603010e1f0f 68
    0x350341e401204030a0201d140b0310b401c90300d520000f0a541d0480d20f80101c91081e08a0300b1081256440ba0360412509070251a040e9507994905401410031243c80d81d608011541d500354440303803980c0341601c44a0001700c8034440a00c46544d00d800c802d021900809845113043e554600d44803c440c050b42001d100400e201040001f40042442810305444020804030b14101c90b0081c0180c03070307a030580a040034684044c004190141d10800c1501c80d01382c10080d10554890013044d0881c0c2c1904100c2d411100c480c102075140446040c0b80002606841c0b020301070310308085016102400c80714160038825040400c442091700581d40d00c104800090500ea101c02c00d25041840a40341480e042d070742c9807030180c883c00061112060841510b42c5540700c991501603100e0140c0c2c0f608902511080f52100f60038486d000c400306254401c040f01800c203038070501c014000d0a5a036400d01d420b0320402c2061540c800b00900041010514400200d030340312a000d206002001140100310070340c0503950b0803e10280500800c00e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 947781870 1250 947780620 947780623
    0x103030e04330b12070f020708030706020309060907030c0603020c030f16150b03061605090d030f1206120308130c060c1403031b0d09050118110d0b061e10020f 70
    0x5002c0c10158110718946120510325407803656010700380808000d0700d00d11b03d02c1c00ea882440079201500b450b00070f03030f581d841ca03e007080350194001b5901d0750800e00a26001c98070180c4001401011250f2241280a0103071803c00160003d40014409104502042040c40030042c0000020546400c0ca5401c81204000a003440309074603401c0d65888407054070b0005150240d42e40026015808403c001c401c0c10710104a07a400c23075203400303102400350304101a801700c5010103810140b01000c0549590f120381125150803c14000da03481c602c180d031508064660040f01013849010302070307400350340c101b0030809658169a0300e598580c50b42d8001400105141c6441d01040b02c01901c5015444c6e8910095003036042c145100d0300325118a59004070a040000b0760601c049960341c001d007980d203030000002c0040103141800c8100030030322064221505000405905030620303001d80e50b078100b41e4206c580b0086641e01d0105000c4040000c401c8403000308900d400c0032044c0d43d02c200071819003c0c072503070103094428030b03015006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 947783120 1250 947781870 947781971
    0x15080f010c021c0c0b13020301090b0402041a0a09020f0c0f0105040506010609150c03031d150603030a05041401140f1206030601080c04110d1b120507080103030e04 72
    0x69070383e803070f0403e010b41c0c88a0b8030003051200c3c00d40280e00c2c2c403050f4a070085031081101300410000d40650a1070a060140105412130318801d9001f62805d0004200c1020f1326040c450503c114554420706d40c18041c0f019000d00e6029045040408240c585084800088185483d203818281130881e91110100000c01c03005211042c010302c154148417450505080034800c1042d082100c03041000882500704041c503109801561180307800c2e10000320070b590801c0115807036400c0300341d207a07030b110000c032021400300e04000003194101d50300c954443d0b080c61308164103003081e02c2403540d10504002c500038609010580034001800220110245103030360300e1614203480600c43c80289040d01c00c0d08804010000c041020800c8540c00340111000240c140601528190502920040044c514030340001c4120000100d009245110034545665401e03004000000040d1074044500000180c0040c2c01080013034045c40d40600c02c072400030300201e00c03425032a40032005080302030380300001540c020030780081054100440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 947784370 1250 947783120 947783143
    0x1416081c090603020a090e100608010e04081e0c0714120706080a0f0204030602121e1e0a0f0f06060f08010503070317190201090212010b09070315080f010c02 69
    0x10308034915218103014120340450302c6418145600060b01c500344c41d1043c02030102421000c500c080d61410440100010369072680036413400705501c00700110303075807110001851149512200052502500c01140003072040c007200c05401c2d041c0d00307020800401c503082c403007000902061441040d04c54801030401070a00c002c0800d130304d059000003c0500405e64010304299120451fa04041494050f100000f4000d208551002d800c0034030100340da13405500c1002c0300f240100d4103803403034000d012000020401e6028066445d02120142d001c4111118040200c12a40c044460a0001070072030139040a6000c0d595000d004449242c2e9031f06c0148100d42c0c102c00e4200c08040f251800000d198103000c04603586080714040604420440d1521350b4a01210070200d407400c80320840144502280303810003901030700305c80404900c110004c2809007000362051142000703110740204071100716120f040d400e0b80100305403150b0081e908459400800c0f1040c0421100354000440c400000e8403960f060070003400c10308481d20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 947785620 1250 947784370 947784403
    0xb0f060907180603151701020432042d0c110d02070e04020f060a180b0f091203090d0312150f17070e040b0a05060108071407141608 58
    0x3040d04a021088002c04191503203400c000420a82c06070140c01c07105400da110410b44001d01007034401c440c0c010b401030302c203c400c5403034044848804210403c00e403030394000100003c0e6055501c08809440e00360401c0c1c04000d81210381100017800350301200780002404480d4040940c590305001e90581d4410410f260404881001c0c1c418030101100c025100c07007091044484a0041c200450107560343c0580100200000801a60307030f505056a0181404a43c2c1d012030040b1104010006204403001080307403501460701d10310615004458081190119440c0141101c41c0300c18010802c8684132440c09181c803d0207529000050032034036650340c0980340d0940c1e80003019031400d1410441046006021000d4400003402d509000f2032199030300d85004a43c1d404102d15010340c03030034041880b4000081c2800380d06603100134061541c0300d90040d40e98901c282c40200c0000d00b003030301003d40000b080024240844c41206900c681c85041100c02e8a0101d0001e206440c0e0341e0000700420090f542001030114943c40c004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 947786870 1250 947785620 947785637
    0x160302060919030315080303011508010911040b03040c230906030120030702120f04080c0111120c030705060903130f0b03040201080c091021060321020a0b0f060907 72
    0x740503280e0340c00350000281850b4451000c01030740d580175104e080140c4089000c030b07516582e4658200d0682501059100046080440003050358002400b4914540040038039061510f440c004a01c611540010703c2551220100a400b00300038454101d01c840741440700308622082d200043c01c0141011010b40703090f12070f0b0315003a42c40850101800c041100250503000584d225500d08000f41e050001034004845031103c001b65511400e80c00c031001d042070305c400030100e840d00340001005443d500882e14000362194012003251a04043c0000200801c10044003901e040c000740f80c0c3d03040d2078444180c030010305981020980c05090a8504041c000400601c1107954030685800c6001001d8400900040c1c1040340840010b8023500100085448145c00a13000c503048010f004002440c40b040c081d0a404074000105420440600314002c0d102540c3e0010380480441d45004080803004040004100a5004200118000c00c070261001841084140304ca090185409001c1110b4450000e024000744a400c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 947788120 1250 947786870 947786893
    0x30f14040f0506030414161701021c021c0e060a180b07050703030b1e01032003010b0a1806110105011d04021e1c0b07021903030513081603020609 64
    0x4421a8102c403020350306207035a80ca450800d1101d030030a01c41062224072803a000d800021404407120011030350000e8050041000000c0700030709074403603282c1307600d80412610210600381c0c01a900030300030510440c9101c042c0d00b00c059806010740c2c1445d0300d04500c0d5005801082440d5500c3d0007120100240c40070382c28040d0840d9591070130500d4003d0522810420042203203010140254401c03000810000d000c46048082d5280c0b46090b503410085490003c1d0074918844043c6408107511016034004096150a50382041c82c40303989d030b81100040400f0800090b2801c0d269400e4882c0030006403070340e9950102c0c880c40240e070300b0303003036540691148400581e4040076040010001140d2500306e13504480c40c1c24922130400804102c03410407069990311000030321a81d6a826020b20102010740c0c89003412100e42c1d03880081c140e0304c41d035651200c07444010b848800c0c10000b030720130b521031640950705190001508200e51900080390304000c0c0002c03440800f2400501c14507404000c4c40e0b034080382031030040901610306c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 947789370 1250 947788120 947788139
    0xf0503010c050304080f1314031524031c0203180d030e1c050615030c0307080703080d0e0303130b0f06150a03020f0c0c1002031e0a030e0a030f1404 65
    0x1440509031100104424800c1120340d01280c4091984030044900b590f00e6541503803601400105c0da502ca4403648000d11181d2414840e218429840c11100300c0700e00301d46803080f04806012050310ce0713040c001e02840211204811620108419107940210384070703051401176000c0d44a402426920502c1d941a8190010368000808220003138140c07400c0c211706401065443d880c42802c0d0703000b00103000c2d89041207007521202e00c5002c0c108038118100c44410500c00c1c03e16850304414051107a01d50407005090000c42c03440c030300501103c410140c000444c50988411182150000c0d0f03001c90810091625550903c0754603044030750082c0c8016004956414903400140d103000c00000f2140d10414041170030100b042c000d074180c072140d0801e480032aa960340b81c1c0201940f101c10011032981724004d00981125403d100105803802c04511a001c54000c640e034144036035071a08412040010141c5074601881010b03414005c16000c9031003034031540800d0340040e601030614115814071403006c030300500080004982 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 947790620 1250 947789370 947789377
    0x1410060f0510110a0602130b030c030109020a0c1a0103030914030c041a041a03121c05150d050610080c0d021509060c0c09150904060b010509120303010f0503010c05 72
    0x10101d600c0072003100c821505540300c0701401c0c182440c50281300120424410710f90020581e451559581d0454030340c95800b017410a00080d81c040c000f10406000500442c560b9034020682a4060300701041e0b8a10b080d0b86d003800e9446100a6412135030f0541d0010001c260300511180054180301032900516900700380800d07501c08050710618450b0340c55082c0a44208418404101c00c2100900184031442001320030760943c4072009070960291042c0c504511000783c001007038404500c90181c0050402c810200c0c1e0f4000750602800100706a107101c0c1e00c203252640c0f01c2010204003403044005c7c014a00d402020503007032400a9100c0c02070b94104400025481d91148031410200d0360440b40760080700032242154246006c0c5042c903036005000055490a84100042c0d5030326965000ca42c14041683c6105000700d880a54046030b5410043c400080340010b403058100703119001041c5030603410400703e800014103e10002c980190f80360000401405060410000c40000c2c000c260000d019610b07036100020450722 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 947791870 1250 947790620 947790629
    0x80d0c0c051c141216030905100b060f12060a0806010602150c0d0203010617011406091e04020d0b1e0d120e0a090c1205040c120602070503071410060f 66
    0x1c0c0801144003196026262203c070030307a450903041d900c548001030b02010400042ea00c01c03404281902c0030a0520388a4040c0c42d042d66886005482584c2d41c520142000d06140c50616a000d602403180c440030310902400f07003490501032001503607581460410b0140010b21904583c8261304054010b010403600003481d4410910701035200702c581e68408140f804140500e600c54801c031400040002851a800142c1327081c20103240c040c8008603680c60026000d504030030f01d0055017000c401c0c4040c0d100e0389440f810280f000d00810025450b01404000010120792002040c0c2c4115580d42c3c5000500c0d040c250501c0c0c4100c00b001344920708444d14100040c03036510036a04014011484d200400b000c01d403155420040e0160058070043c9070300c0e1160159030150050500741da00058880d089d280307411019002d5180070b140c00c44800710429080615408009003009402d4410f142c08200030320010308200000c04440d4011000c0d6900032070304042180c20150001c4503c81d006050160070720241c0c8511f40440200d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 947793120 1250 947791870 947791903
    0x11150405010c03020a06060806010e090d0f0f020c0301090303050a0f0b0303030606090d0b041a150d1415040c0314280c030602030f10290304020d0b04080d0c0c05 71
    0x2c08151a08078a0700c0c0610f000142914100040003500c04000111113041e070b08030047c0c480e4a6524080340c0d503910b526a0000800060200c050314503414026014400d0880c640d20640788a09403400c042400c1d03940f400800c8000954030400c020040f102807040480105020b9001d011130115440003d5581c0400750072544102400140428160350790080941c0555100300000400c1ca801d0400e07560705000c0b007080a400a5400c0006000b04c041c42802a20b20000107010028500031500c514103195000443e58450b40b1039421030203d001c1c0445241c600c180c1c4101610081c050440c505805030f03103210202d81c502640309050382440d07140c0d0000802141424980c0c42400c0e9407940c20010000d0340c01c2d610140805100200f8013940c080d0742c03c1c0301c900c0351280046190203103540da00a00c1181c0205071600003403071400391548210980c448021500315000402c4228012407030388400982030300c20b81e0110741d0040700282d50508174101e401654248642401d2100000c1440c0d100c0c2e030349442c04d02c160071890 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 947794370 1250 947793120 947793137
    0x110105130e0c12090303160e0321090d0602040302180609040f1e06050a0b01020c06070305030907080d050717040308040302040903030f0606030c0e030d1e0201110d02071115040501 79
    0x1550100c50036160200d0300c180450583c0d0400300d10550700c076801690601c214044281d00043c1450080d5010440c2600260041045c400303103110440b24070912505d04032042d40d040000e40819960001c071303101003078011345005a0f0f0b180345104205e503100c001140003402d9440f440420906650305002d0070341c132030341010782c44946100382e2030685003c5000e036044031000101084030300181300c0316500261007058242410400c8003102c3c00107a035251100314615900000400c491000244a2400f441d008180201110001601c40060508220310b0f90000f50026801050701414405a400b074103020024a201580c03074541142ca1f440400e00c01c41c00040c2c007607511030250f0404c0610230b41c88802d0b01110b05004000140e1100350040142100111510000311511300383d400914022842e510411000d440c1e10540da043c04203079003c03054130040385d8015035503113404184000785401c0092414100100005070b1b6403510703180081d42894507603441ca0041101040301c8030b40c032807110100c40a440003400c12251 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 947795620 1250 947794370 947794381
    0x60f1d07021e0c06040b0408010c03060e0c0a0c0203030c030c070b0c0a0f1b090e0c030312340203030a180308060108060a08030c03030105090c18060703030e0105070c110105130e 78
    0x1809964040343d603000000010b0004146140b0340c054401e40348064001e006825588008a0995145004100560000002050740041c850000709051121420180448050b903000a070079900725020f184031a4000240b00e50040f0828001c5078040e00d0f0391803029050a8042c43c005503554104007006003403000c800407103410302c001008903942400d0422400c42c005d688070755001003e040d021126650354070414030050003a1801000399041c000043e10403407603030340da1010601140500321003024015111002400d071010b1003904180d00d400d02071b400035a40d80c1054007a040c11611014403d8100c00f03641c015440010341e010005a4006600b440c000180e030b180d030400607141104640c05004203200004218100c244080301860403a50200c2d1000040e40e41e0902100b0548541e0344040d000d0b0510000403091482e0076006026254080d140018820708803600445c210380081d10383c1400f2035005001441001000301305048500c00a1802d01c2c00c240d2102016101214180550001000304000192 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 947796870 1250 947795620 947795623
    0x4050705010815040e0c040f091e080f07030305100b030c18030c0307030b01030203010b150703120920090c0f0418090f0b070908010b060d0507030609060f1d07021e 72
    0x550083c0100104070030300e40c1c07101700c2c0d907101000d86019008034205548003002c94958410449119002038072011950300c0c03503072202c40701c0005000490f010314060200702504200c00001e00080751003600c00003014145803002400c00415540403620392003041041040d0507100c40e090b105d14003074841c102400b48800100003400c0030580450140c05204980002060100030360100c0e04890080c2d008111820800043c088101c5075642e560203070410030070000000903c242c0c040b010f0345800f030200140f8802c5c0d9645a181c42c500302820000340408090001241c4d240100c40b10b0b811081c0180542e25103034001d9400c04241c0614801c014445813204104210303550306030483d03109580d02040083c2e064016160041102c481905c4600005030b18500c00f00d07142505104240d0a0200181031900780641080c541c7c1c041c0030018104401c25854460006815419004010203820a0f0254650050a00340020240001902071124002c0542e040c0300d0819008280340c651811420782c141809418100c145 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 947798120 1250 947796870 947796901
    0xe061c0c051c06050606071a090a150f050609040c120309050a08070e0703060e0a020d0b031b010f02011a0d020109030803100918030e12011808130806040507050108 72
    0x464000008415801803014402c1e0100d4115101d400300300400d031603c0c400d21515002c0c02d2002000489806014040b4841903d00c0507440f514070740458101c0140c43da101c0348103101d1807201441142c1c481c118030500004c64010141d00c0703101a141c074940303850103440300358003071285101e540c0c0408000e0090009152041c0305010180c007001e44040900340d5110380c825920301091007800c1c8003800840105d488e0900c02d0003140111140085415400d03242c0d040340d42e0095201e45022591503541d040c9017111501d00340180450031400100f2002202841380002d062852080c1d141c3c0d045924083c1110130b06020408044c0c03481d42c090b02c5d8202c020320035100695081e02186c0001d0550b07403001c003c1241501c0908100402c0e01c010100c01e02c44c060000f801c0d0f41034441200c000a0224600da00d0889082c20002c2d400340706104a0070020881c5007403000e00c1c0a5180d2002400c1e00d41403c0001c0c506080c1c5140c81100c1d001701010720003800030345050b480d41601c441c40341c0121410000390b90b0200707840301006d0050307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 947799370 1250 947798120 947798129
    0x903080a02032a01060e090a06020d061e0f2c15091f090908030a050402010504050d0b010302120d090e04110901060c05070f0b160204240f0e061c0c 65
    0xf056a02da2104841d00d0b10704001e181c4107080d5030a010700403445030701a40c84603005902450090403419610342d240070294105264181c0103030341e07030b0b10001058003110920214178000c2c00d05071000141006500241d0240980281400300421412800c1d00183c04084103c2860003842c0049a0781b600b0b02031411108800f299103a00411000034061501114010011a444d050b51944005903880d8030341005c2e10364a01000e021300700d044c00002c0d400c4002c0d820141e801807051400504e81520342c0c00155444859080943e0600324080040c000c44c2404280810084015001011043c072011001810541c41c1d002c1c8071024184e01000c0790030404410b80350051070a0041c6a260746603100c80b4014428031403090180c5071841030b40b500144581c101440c100c00d0340c0502e2440d078030b0b081e0034208aa03501400c4020490b00a0340d0b512903820103000b075150900f0115415140460f100b45042d1540d0040c40d96038120200d0710f201c01040c0034581e95610b0209008200c824844c3c19624000d040081030081540d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 947800620 1250 947799370 947799397
    0x10c0809041d190309060e010c050115080709061202010c21080402040f0e0d05090a0801060b0301050126010e0a18030810091e05101e03020f0f010903080a0203 70
    0x1a80044406019400b441d2a03250340807940c901e6075010183d420f08410342c001030f003c901c80010034440c080c4141d03c1800d40d0601030400ca4882856a9100d9007182c8154039a0591050540c0e000c6c8420803080c44404024078100301c0071302110b41485100584994034200084c18825003410071820820402c10210b400741d0222460004090781e203c1c003500320300040390101e21445c60b06498600c00d03041d9104403064202c1180c014078842d034480c00f0503140d90f4026031070709500004000c030005041009000d4803000e002c1e4254802d07141e500d0500098a0161030682c90055856240c007200c2039281d1501e4840c0c1100c0e80494000c07281d03200c55940c1030041c5450a6120642440e100080c4203064010707882900548241c19200895595500301d44125806030a0f2284410b188802170115561190401504403440e4039496041569440d202641d00b601100003115443d11900200294500340d250301d10410410b03540501080c1c201c40009045500030700008000d0100440c03000500c1f0303c01c0061783c400325452070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 947801870 1250 947800620 947800631
    0x304050618130f020a03050106030e0c13020c1e0f030f09010810180c110712020409030e10020706020d0f02031e0c030706050115020a0302030d0b0d0b0a0f0b030106050f010c080904 79
    0x201a03d000c0e520460200d404642071400028071207100e446906c04010205001d05262403110703080000c1894804002c100442e0280810170074001d05116420698000ca60450310b16000800d501e81070080070b00b40e440180e0414044043c00240c02c200316007526609180c203c2071540d91101c520320800c1d40d50402c0b00c026074080500c004031400f03607014240280d015225010340342c55080c1019039982e4240117440b49104010321034401402c00e13800c45100548203040c0400358060220114845284841c81c40300140d00580c4100030443d018061551600f40c00d00e40320503c1e0400041c0030790f9030312500000c4c0d1030038400d4141000c9031602280555858400d2402076039503415990510300e010703013400e009400f10006985401c0014500000c1e207140d100391305402560074004c4115401c00188000d08800381c1002141c1d0300c00d40002c040c1000284180b820b51760000351030600c0c6580b0313804c84100307040090290b031501400388015591402c0382d442d8001c007407800c900f400c03005184c0039440e400395040301a049810034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 947803120 1250 947801870 947801891
    0x30a11070b0f1314130908090d030503011e1208090d05010609020a03060b0705070b03180601030f03030c020c1c0318060f020f01050103020a0509090f16051002030405061813 76
    0x41c020020a41ca45400d1443e40d9140c2503c10309000e0f41e41c0326030f0b500680d100709855004006801c00036215010310000c81c14848540003048130b2040c0c0000450005000000500881d8492510340103d051261181002a400c0c5550302d07101d4600e900c005003527081c0200c0c05000582d0342100c0c48401940c840000c1c4041c503610000c02d0081e401928002002c6400c000021400030b0441003038910039600100203001c0945070928400a683c005048484a02c40c1100c4085942d4001c10801e4002c43c45809001c01908044c280103080350084514502150001e4011040c00e9540113a280016070900d031400d4242d40d954601940d07440760b64022070000c06905400001c4082d00015101c032141407d800f69241d8031707550341405007221001d00000303500138668003003400241048144590320240c400304442d0030508441c285440c0200c4d090300d21001c09a011000e00150800710b1120941802c1c5000640c2820300f44000211940030f5001c0c0162103c408a00c451000e039500000c0302c02e0501030000c1008441d114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 947804370 1250 947803120 947803147
    0x1505130f060605010e0111150417030f1e06150901110f0a0201090e0c22030f0b1f0305060c030424020309164406010302030c060c030a11070b 62
    0x81c0d10956022801100d50f1039100d50003481c0e0390120b0f8030f6403400741004926550117045081406441964480b200d0f4150350200310101000313300800a90300004002d180002c601c0714860b500040d9005407480083c2403002503118095070004240407150081d40b10302c00400101d400d1104115202003e22507500d02c02c1034210701003400c05a06000307030303241584c0607100c402c00b40d220070703050714200441d1200300030030001042c02d0304104414003c80000b10320001d40d00d8480d00c02c03045890600f03861019040c1c05210f004100502041e56540b10040d03c001524995210b8980701c0b0b5000713000c141c3e1000d000001404101f0b21006007160007040341e407040580d59010581000940080b503200042c1c2c030810101d12110140c0d8819401140c000035451a401c8151070700041200006490100d0381c18401424019841702032441400007020700300c010078203503145004140c9005108030b2414060700c800c100710f00c40400003200300c800c0803407117090101064491088641c074000c400d40c0b1410f03d4003004904006081803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 947805620 1250 947804370 947804381
    0x15060705061605130e0f070809150402010207030b150f0427060b1203072a1806052d06070c03080f0403080d09140606060307030c0219030f080705071505130f06 70
    0x403201d00156170387c176414190341c640c4c01583c2c259910b0344500d0b4101d62100c51181c40550192043c819241d8482e50f0790744400c0540400c1ea00c031034140310903521100d1309050401010454a100322000d2103000c0d050748000d44010b008143d45c03188100c81c0d041280500440742c001d094201006030180d803c2449a080d007680780e0300200c00c01c0b01d40c3d06a01d0505441c103800d1204290300820514400c3d10718624091980703044e00c00d00300103026600d40f240c0d4001401c1d5500c01d444034249403400f80c070650f40003005072035a08020707424071001c0c42814240324850229004507468010360381d01986a90b610141c0121075280ea0085600041a283c030000c4c09034036916490b00a50f4002d84909200565550001405a2038420440d800d9400440c10300000f007070f90344241c21070341c4680b041d8010b030781000c85510105049184c1860064020828040b203501001c1d1b0b0007845540c0c485800e05d446420402203036079252102d8031940100300b8071030300c440c045000d00c03059100949103681d100c1d140c03844c0d81e41b6514140000c1c24 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 947806870 1250 947805620 947805631
    0x240901090920030c0f010c0c081617061501020f190204060509040f08031b0318160f06230316020c031501091109030d03020315060705061605130e 64
    0xd444051441c445100760100700020b4a0040103004021114004c0c0005858008039083c100300707810310080c001c612004109001b5204000c003804181007880502c03111716045a003c01c41400201004803a44680030500300d8100c42d4442049000c100f110300102d01c0c008108850030101e0042c0b001d030b104400300302108081c14620a03501880300039510b004014034035800710f43c0504403c0f1a226603d00051000b8015030307202c08204e6481d0030100b8094030401e184d07042150108030301c00d507d031441c00580c80100f140b80d0a0040c0c0141029001d410b000709800b203640b07188104d905000f503000f006c000208051114102c00004c4e10745a40c0c90f460310355101142801c08c42c0070440540034800104400d8200030603004000e440443d404001d517480c05010400a0400c100070303040320ba80c280241802641d050080004080c0340795409030700c3e820121b0840302460b8440050b5442040100a22130000300f0209010380c0c0700145030480112807091100540361441060700b0441124201140440d4142da00c054890040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 947808120 1250 947806870 947806883
    0x20f0304050109031b21260307080417120a06090c020a060c2001020901030605100c2402270a0302100e01020a060e0304030302070f080a080f0d0c0806180408032409010909 75
    0x560504c00d150090307468006c40e61a1f0350750401c001072000307004022854106101c1c044c4000707042d048845142680d0480340000d259905da40c01030244034149030040f6409080c0c0d440303003005502c0004802075078400308180b006015a4864118580700d5002e00b5031901b550744100d00980d440e10880340c00c5c0d4002d6000046040c0840e150110215090030001084a0040c1c07598651000007103041c2c4546940c618440c6808072113042507134070354290a0460020b00f80280098a803110002d01c9035116141d01c0c4184950349000d242c0080741040940e8030003400c85080d2819041c082c10301135035000102d0500040044c007412060804014150131400003004004481c041d5007914401074075224040000381c254403d01400b0384c80301101d600410440320040045d1080060b020b481c20b012404144141da030406988004030b94150100300403810024140d0b00c00ca111000d080c0340915042d034500982d400050071030914070303281c2d90010102c111203524031050304100800d890165a0b507080904050708040e01c040b605c9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 947809370 1250 947808120 947808143
    0x303020d1416021c120207170301051206040b13020126010f0b0c030f1303060f060e160c060c0504180e010e0325060b1003060501020f0304050109031b21 67
    0x10f102190070503080c03075004840c00221424010480d401c07240070302ca00b007116a00b001b0398070015290b00001c14011054210958496140500b00801c2e8043c0d90340500ca42e410447c10480001d4804180d203501c803200c2c90340456442c1c3c0c2030004035034245071038860b1005c50034914048451040c00050700741c1260a13100700702551030788851400c0e481c2d02070079130342ca0807560050100f800000d0480010380700381d201c1108103407c1e40c0c0c1e8980f1603105641d244414200c0013076851006125801d501207009901050305843c6803464000d4600c018031070300c11000003400343c603136038182c1c0d60b94140b00e00e08480081c40c580d110980e003000b0f10500f0000070104900c00901642c60b01000f0b034000302000c407e454a4280c1c60100340382c5500840c001422100304030000316212565403084240a55072080c0300145500c20341c0e00050342c98102400a450074203490303021540780e03000b40010005603038058000820750fa81b00c02c115810050b070740b05400c60f04541d504030542180c00d6040040101c0c8075011010052400398016994 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 947810620 1250 947809370 947809411
    0x15040f0b0102060c0304081e121e150604080a0303060e06031903121803020a1a0603101109030a05060708070503010f05011b120215060901210303020d14 67
    0x840d040680d030310307001d40c00c070a00040107004054003865001d0b0044409925028a50540980045c00f11414004e1404013080c40c000030703210a24110350205413603c80d0127201070400c0b490400074200800da800c6115900039120300b95160b000c142d800070f0001c4006c5818892030341c900640903040b140030b03040102d00c0800000b0124500050681f815080041d008202c00c1525141150645000141a503401c0d031504104820403040714850405940284c0c05040c06501e01d14000752446e0004148001c9100508144015640c020031043c0c420071540b040003a000b0b00307010400405004191029500d0b000d410070103018040c01054281c4500625928038500da0703503181c002e41e260b000a006c0d600002e01080c1040c0b000f540501d40d40d282d00c038032f1501072a0402c14155581072001680c1d050322001a003200c4104250350f0305650307000350020340480700308503a9030402c1c04d0200c2160703500d40f0b4a0081001e6400c500141402541207507028901d121060090041c00c07121440c0da0305042d5202c50081da004400c440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 947811870 1250 947810620 947810651
    0x607020a1a07290c03430804050c01050a020a0204060306020a0801170d2a2619050714010212041707030e2107080607090b0c12130e1504 60
    0x901d486030f039900d41c0803521204503000117a04010b101d607880c002620040f11495030381c0b044210b018850100c0c1c1c1c011008000c00b45500c1600d50b0f000d02c4e42480320f04e2040c0320003e140450b21400020080c80c2190b182c03609a2400c0780742c40340c00311019402c10310300307100441848543d4000307055480c40b5032070312101d5036600d5020380c10180724000c40305291340180070f00700b00300b510958101207510340d03103c892680748900c000101070150300f248044402803154000801c0c0c0c2441c8013055103d2950f5400c1940c10405030140d40d07030303000c2c00284200c0304000c400680c880400500c5511501e0492821008540740d0b01c4206002440b11403d0314142d0781200d4203100300d126030321280101c80c400303035160351602c00401483c0244400d190418854140039101309402040c400e40800020000300304d12802854581068400a00324203230300e4001d001c0c0d60004104e0041c11050000300d0000050b4154100d82e5035115070b40c0c0900c140c00380d0b40c001e90072003880241440b05c14405d98400e106032f070408407001c01614101c0c04001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 947813120 1250 947811870 947811923
    0x60b07150b010f14030c0405030312180a03120e0115062111070b04080d0e0a11010801060203030c0904020910030f0b0406060c061d060f07031103150607020a1a07 71
    0x101c000b134040341880200a002c900a5600040c01c441d5030750400b81c564000900b5504180c504600c0994003000b0800303903c0c40c4401c0c00c480c01c07144e003019006440c25038900510603504410700e4581d840c1c4070a8026800c10003540000c80d40381d80c400d01d100c2c800d900da01006180f100300c184400701c00781e84c034040c240002026100390000000070800d0785141819a544802e1840c40041003507071a044144641001d40100d40254945202c003400507240014983c0f4282400c90040c0e042c141c1040031000040c001560008200ca070070140d22035485844203214070019002c0e1040300d00107904200058112244c050701900140300b6480d403040d0500c41040708000b444103c0e54240300d06000904190341b588046007896004190a104020741c20400c00000b04025260420941c0d482065483d04420071802992500c5000100c040c2d00c0806455070525404500c0300c0300e0304040003845108000b480e81d086541d1803e0000040c001c002c52a48015540c1a54040340c0d0091441921144082d02003105000d80803942c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 947814370 1250 947813120 947813147
    0x3031b09030b061908032701080612161401110f1c1e08071106090703081b101505011403130c030b01090c030c0c0b060112060b07150b01 60
    0x4050080d89181c840c9001200007030020760b0445400c181026440c16000749002c0a03006040c0210356540031444002c00e030300d1341c81e8807218800318084424080d80ea480600309400901c112500001101c0d0006140e00b008500982e120150603c4140082d041041032842034190809072505410390040b130080b00d0300c0301c0c40080906103a0300000002500764406110300c0000104078074000811100706501151a00901c00020740032800c51410000295488a5220072141c5001c0142956082100c8003550701c41300f600000b04005c3c0045a0291a1b04c98940210b203024030b40c030100c800d00306008640381c0041c40c008200c0d10b420651314201081c0365009860200c051030708001804d103542d894900b8000810300b0401e045480d00c513240400800f00f8840704e0414040c1045400c00205810320101c040c08503803c15403c4010f1115000700d500c041000500c02c02d90080003820810340104041490f40700401c1203800a9500d001c01150711014004e1800452800c0c0300100402c004015040c0010369450711807946 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 947815620 1250 947814370 947814377
    0xa15080601030c080618100306020d090c0522330f080109031e05090a0329060d02040c0302040f061223010b21150906041e180f080703031b 61
    0x406c011030381804800981d0000304d020f01d002589031280e4500060341c1c0700465030718074243c448051a042c0900b8092403030041000303c5020a0700920f416401d400d0340c040e8442601919518406403a1340d611105219001c0d4560a010206910007000800b180109a005c0d0701441d50080c2c001149064051250528082d01a203480246803070508046819004100542041100074401804241c0701d02a0502c080c1d4480e0402c050b0154510281d03450800d0140a42c80c04901044284800c1c0d480301032103810099010382d03001c02c00701d100c20780640103441103a000c00ca803911900345c0001c800d130380a0000120303200842e00a2002240c000407401c21150243c1026464060000041204903501c0009090004489070b40540d04004525110906d100494850620320400c0340c1c0ca203a20710700070300d08962000c4102c90410016030140340304410000d60403441507100d5550028614100034102404010b00e500c56500310464285142c0080540c00c400000c401003420611819403110300d1036005440c4aa05a1303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 947816870 1250 947815620 947815639
    0x40c090e03120f240a0b030106120509070509010b16080406020120310b0a05030601121a0f0307090f23040213240618080109150b0a15080601030c0806 66
    0x207000d44e4840c01c44041159002d5102c40c00080c1d0980e502014600a14950b12810a5008001100801e9603c010040003603904221005d00c226034441400c6030544844080044c0c48500051300003881c0710350002c019000540c0418001902a4150001d0781c01289035107042111000000d010801801201001d0400900110341200c078603502c0c44000f400c000c00c48180c4840a6924100919070768004030444001840000810450b0350f005004242c1000816104008180c0041421464489001100340c0706000f6a41500c042d503604000344006803234101c000f080f20320b076070040710300080603044002c1c50b02032401c2c807004200c2c1c1d00503215a84a40e802801d807841603114040a000100080101c0d0040c0f502000d10010295016520400c0078150603186c40c0d030040840e0401d0500055150301c00d0380c4a80c101811400041c8008200d00c07280c403190340300480c542104000080003d5081c0d040306617500c5842c0400803500ea445805180224404c0e04c00f0000d030b890214048483c01c2003110b9094010308002c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 947818120 1250 947816870 947816911
    0x10510050402030f01121e060912020303360f0105040303200406080c120f010801051b0904200d1b080601020604020d062705060112050d08040c090e03120f 68
    0x2c0b00d4201c5441003587d6007040c44400c0ea9001e9407a0f03140415101182c0c0c1d030a5060802520f0004000e80305502e000a50541c5841036030082043c411400e21b640305203040344020002d440b54100c1b8000d27600003805541e644042104414020001100c1c258002800e01c60080210a4503042526840031a03901e420701e05030400c901915140c9001e4139159020004002e45101d2550511101d0b00514101141d4038031945014805829030700043c2103840a100003544601000410311304848400e0015200842c0c25401c04034413014204545000c22158000016650111100e50b4052451918003590360015290700e04401c9400101c1103540b00d000d40d01000200303000d441c111010ac408603200d60004554a9030315110040c0300b9000038508900d00210f00350340c2e01044001d0124501510b40c600c2c4800120005450b05a61102e40740b07a03030401d00100324041011302001c0400e08002d8007890354140081542c844080d82c1d01c2d0b0000c5043d41d440719905012035505402d00b520180a00030550b8940044e0008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 947819370 1250 947818120 947818139
    0x512280912030c020a05091314070f050d02030f011b020f210d15090b01020f19080a020106080105010320040b061e09040e03070506011202010807050d1d010510050402030f01 76
    0x10f4600c10b030392022080500080d60703a81d2800240c070032161200325208002c51813905441c2480d0041c181046030704002c202b84030301c1044421840480d80c003101c503040c022219001003410280c20780404419542402241b00d5480c0303905a00300400c002a500b103844402003075081545030b200c412800080c0f0340100c00c0c2100f00008000141440e480014400600414440308419109049600c19004c854a1703202ca612550b030140407000d541d081c160050702144d858a02c207040d090000300b90003040d51602140d51080640b0075407009025010481c000c1143c0e585034100f103600d1801441c82c00c5440411180400c400d030a2038015140604400b505280c240500c900d0744e90f2080c901e04265402c0d009060001d9601940d076405000900300d03120000d1642c50a213400c1c0745007040d0058000000386007201701e030b00e00181d0380428103e50044061070942d885158101c01e10000d002c01c07001d0ba403400040c40c642d82000840c194019806000703402800840700c1c1d65802400203a02084075109098a4981e0042181d0f030302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 947820620 1250 947819370 947819387
    0x60b0904020306031603060f140103020603010e041401050702030316051e090f030105040602032d061318030906020601050f15030705070c09050a0c1b030c051228091203 74
    0x20050540e82a4002074a00d000c0c0103d21ba4400e465598552402c001200c000b031207100b400c100388102c615003644c11500810240c0c401032140d10607007080400010240319840c1a2081c60901150090003d8241810700070750340c1d001554200352245000c441c011101d0300030000c546102c0c842ea4104e8816010068003480c0c10f401242d0750176007051141d480c00800ba0760030710840c0e2040703100308070042e00c03400c269111090303a02483c1d20181502d00d03030400c804d920b00c2012038201d80c409811504492000314500007403001e040b0b1103c6da20300f040034101d42c2d4410075422454000c06c0c3c40e241e508440b80e40c0c1e81d5404008071952114040d6400c01803408100c402214490000c1d44c0c4440c0c0c6090803440d00d9180d031b4550214400170707030008410710381c0c4100344404034a140c000c1000d02852482c004000040450700f895100403041e40060600528808000821100303008200103807030507000c216154682c802c1100785c4915501040c055108810000301b04050280b4400b00565560f10001c1e40034425a03a0706403880c94 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 947821870 1250 947820620 947820631
    0xa0c0f080621120427020304032001020f07060b010f0201050c0d0e07172407200c1203040515040e0c0a050408030708041422200403030804050d03060b09040203 70
    0x140d01085100f00b11070740002c0008081138201c2c2e61004060110121524000e04102e02855004000380808242e01c0a541402d6507170b42e613813041ca100d85036508540284540710071421804408030302c0e8801d01c626a408907500c040d00b030321918542a44008101d0884200f201d150500100074002911003911a6101e403460540c41000c031007070307203407504140110103080e1101645254011a00310350080000d841d80b00071030792a213850820905004202400c18408818500c070a001d4249895080c031000f0002e001041d24064060703400e800c80b403614035489a1182c0140c500400c840045d83e400c000221040740c0c00c99100141885082c0c80d45d4840074580e50203d121001002404c1c0000b19940074203000400e01c0078030419989e55102c0c689500300051014042c4010301c0341000c00c440c00106020491080400100944000390010103041108108038100710800043c0300041004420160803150090141d4008d400b2600c1e0307280400d2080301a55014058541d1094081c0107045050405801860f0800b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 947823120 1250 947821870 947821873
    0x30a0c090c02010f060b071208060f0409021c03050301051e03100b03070315020a140910080a1512112d0f030604030315080a031d1203030a0c0f080621 66
    0x280132a00325030282c80c0241c01c8010b0f68140004c60404201c000030300c86d8045401c03420015894a02400041c01140d51183c0c0d540c010764460000030f04540d100703001d00d01825800c00c19400b140c030075810b008225402c24000c0310700440744140407410140303404180d40d0213444004c009245519001d4074100c003810f4211070f11901442545404800114040b908080c0c406096400584131110b160000f0252a00865482e520010801c218541c036191940a05612407660034901c107207850784a0084000d08007407a0b15408424a5400441e907102510100e442ca180a8440c07001110740c5102000326640100d120004088204c80013403480720a1040a00440c0038001c080e0480350085101084c100042120120006030341c80c0c0d40300a0410013502c5d06000341007040024600407880d55009801d118085095009a200400c07886d081c690f0368008400700d8032441c2041e641c032401c1070340828010b0030000d0021808528540f02c5040d034948500c014134850032008200c4d0003080094540104074501001c90344407503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 947824370 1250 947823120 947823131
    0x3150a15030525141003050411060c0102090301270b0406270303050f0705041e15091802092b020406060e180f24042306030a0c090c0201 60
    0x21075401d0042044610a1449804100c005204407102e00c1c1d08a0304200c0070b80c100561306110ba80c45260340101c801549003000609038070750741032540355480502019a8043c0c07001519109168064000e040c0b15081038000f44070b421a03880c0642050507803c2c00b41024040002c00480114600e1804190054001c1800055030320740c3c40e8001041d40d9481c440c40e00da60715907410013001c1581c140704803a48000d614840398118203001e5401051072245100307800d6168202140c621a08031842c0740ca00c0180344a040d074844415098401410301c0000b84a50b2562035a0002036000c1c609140c000c0350b444050080c0030102c001013522a022a4004039039280080c4000b515015004dc0c8170b40c80303124042c2c48951118480d04005104100009002c024202604030781d50381400180c06024050a40010a030305155040482c82902c42010402510380c0640c030609041c415499608078050808404210f000400050ba0300c2409050355001000c400a103100750751001080011290b5000200d00001440041407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 947825620 1250 947824370 947824373
    0x7050f060724060302030c010816030b0316060801170a030e010804030c20100201150317160804180b0a1a040f080606100f022503050d08070e03150a1503 67
    0x44082e01c81100c0322407182da800050066240c10085d14001c440240780800a91400d9898600200d250396921014507449103010445503609100224074004500e00c0e00020303944d1900024011902849010f1410700454464404c180780456410314540c0c05841c8d569606106800444888000402c1517042040d41e822810000b803003400095894148004084220b00b600010029400204803502c02960302d40941d0700d4a20b00c03144100300450341c00c4203000d001f080110002001d030717204940004505502c00711110007003291840140080da00580a0814007480500d0610704032800c1c01c2e2070650211580b0000c01c5140c91544003444003144e6020014280780d81d9540110044400380c010b0392194100904014050901c8020042400c1c0e10380303807085d00c1080700300d0080d403075030380320070004ca0340c0d60500041080381c40200c1d810a00865108044134140c00d60284000c1c0003d0064900a000034400850110b480c41c0001d20701a402e0000314089a8984030a00305d11700501c0312110103021044003e40000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 947826870 1250 947825620 947825663
    0x5030a050d180e090703060c02070e060609010e1906140a021f0f0f1b0306030b0112020d0c14090a0204080d050904150810060b07030503180a020307140103060807050f0607 75
    0x140624003a034010290070307007140742605c00d0310191500d6004540c0100340c00c0bc40644141c41d401e03040301080e02c9040e614110440101e400e18400d12650750480b8644d0190707824075008035884030442d45140d039250f0b05448911080d88a40c0300e4418182c00681c04803003800001c084400581200810242e8001840b001880c81da10540c1c0d107046480003556510500300280000c0c80d036401000c0401854108101421130341c80302e107407001c18000c4807089020b200071482191074004560a601c0c0d005500d08000320782c1c420844d9400c06240c149107008400610128a40104c50b00035101030b180940043d181e00c042400c0704454030b41200b0000c0d90700a0311030050f1001c1c1e4825452050107040c445000d00018401148410240c0b20582d1044402c02001c02020340429402419030303800080c1c2c00715400706440c88502062502441d440d01a601d03000b814000944690320404042d0140000e80b001e201d82540c2d040da858480c0994490203400080c80a0041c030640f130500010017695200782182e40d0303130441401288 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 947828120 1250 947826870 947826899
    0x901110106031424100b0d0609090b0a3b070b1206010807020a050a020d0f020901060e040b030105060d11060c010e0a03090506070c180209060304050307060605030a050d18 75
    0x20300700303810800300700c4104441c1100c8411320f01c003242d12099183c20040e0807901c0281480c86042115040415010004520790300000028140c04005100700d9100b400c000611490540b81094001d107801d801181f0346250880ba5130300d40340007480080005c07501902580e45440345068100503805041808620010417130098040c83d803d1100030301e000d10b009000900582000b800d820300b035511903030607107000550005402820340e9043e0303590f0250a4062511661424070404005c6d0300c8103140001180c1990301140249103110112030a002400c0b0560074903080b00d0b000c0d0340d440d802c217900011440105800b149041109007001e0704c1e40c1d180854a07540345007150450300011069030040340c003c505141e4440c0852000d0030080399543c0c034080f01580d40e0000b021051041440e8103907010540c1880d640d041e419108140b0015162540d280303071528005884e40d018250032035086141403000300f050f0500045400b49136511900500c50110301000c19105510384a4095542c100010000b003035010054402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 947829370 1250 947828120 947828153
    0x80a1112030403080106110d0f0e060a0c02091305070e040f15050609060603011d1f030b04060509010212010911040306110a03200406050c01110a0c0606080c0105090111010603 77
    0x981c0c40e4105850000c0402806920400802080c196460190800031600303800d07281550810208505991005072001138204181ea43d005002080e403000c07140d0440c04a0154500c01c0b40d4040351940d030031645000d080340c40d15018015500c83c1105110f8281c0c07100b100d5400078058039003080010b030706564001314100c0b0b95620203209030f241d900740710031814250412500300c00300301c9030b00b4159030608106100007144002d034126411820404034a42d0780405078520421807000d10050202916030500c0001e42d0383c1950200c80c1580b03008000365000406100341d5454032030490515a85e6480c00750440040c1c002c03250640c120020030030002001030954410f0800720740e00c82100070380b00c03055010040c003140e0601c0c1001403c89402c44049001c58110800c4030203541071403c000307844e5611804407034014086e42da20054202e20024a100d001500200602d941c1032044c1000c3c041c0b00d8840d0110fa8544129442290100b00c0902c2a00390307660044410343d0000080708000a0750300c0c1d50b078840300b8004080000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 947830620 1250 947829370 947829403
    0x9020c0d2610091b300e010c090f2108040504050f04030e0d11130e030a02071802191110092003011103131a100e07081003080a11 57
    0x308010240031070042d484e4071400340a01c0e00981e0940103002d8588007014000c0d1400a059028200a00e11020074114840558400030403860103d59071443c02002d081880d080480c002c1c01c00015480f04020483e01074452104903003401c09841107054441102d009021500702030140070104103038586200b000e214070400445401c450800d818060004290202520f0007000460039000100d20001c0b170a1b480000c090b500c002c4081c00341c820100c000c0010905581d680c2c000000e000d039501d030b400100c0c8001d85551800000c00074207852800000c0f44500c200c1c001550209400e14100c56008103080048a00306001380d0f000d580103844034a08503082c5400440c0d40700850b00000000c41c0d641301c00c1008420b0700303030002c000c1440300422038a40c5010040048481507001c00c402800c1001c85444002d00c2c401307405500d546410181111400345045000350f070084103160000484e941d214018042c0502c0100030480e28050940d01e45204d00d0b4088090a01441014881d14990204c100440440724007040c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 947831870 1250 947830620 947830651
    0x260a060509031e1c141603090807140c100206070302070206090603040b0f1605251a012309070c0201020c030d110d050a052515020a0909020c0d26 64
    0x41d903004a116264541801403885c202c242c000034040c00316400c0d040700c1e1954006180d4002c03050214007810a180c0000c1854601285070400c004007085c2071110301030340c501542c050744038070018001c9040d0025444001680494013248006009900134080d4a0001e03199070701d085d200704089007450380240ea007114540d10210800c01c001d48c200c2c6995400943c15210703242845401c1a00a196000320600b4906e0f620640c6410480e6501c1c400d02c00c1c04080d4492582d0501c1e403480c1d103d450740c804092003940e45450303034581503140d0810340e403102e100007907001820001c3c21340340c2650882d1420440b40c01207065209920212906a404010011800c40030b5955080340088100344d03a81006217107103001041c4102442094609a001030a69219010800c1205c50103107003540918031103030f0651005040b203008020126000384070f40c2c00900c0d00b03170038545030104001e030b9880e076a40c201c0c4a910f49044150f00110420910b061099524402c0200380c1c170ba100307680a428101c60030080000340c500007a158900d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 947833120 1250 947831870 947831887
    0x8040f0617010b0c0d180302040c08040b130f03120e0712021e010e0d2612160f03021c060902190305010e04020d140f07260a060509031e 60
    0x2211031601403c2081000ea00300400700342e010759140b00f070f10411420303c148036030716240c1803580c10314020055400800c20301c01009074120241c602642603506499522221002a408403e0400070708081a40110503241200e583e48044031451071150f0b84403019031b126004800c0800d0308000c8140903200d58440110160301c2881040040900c01d46c01110b42110714100c0f114583e0401030000d0704401c151041d00c0036a40500e081940c0c0501d080c91306000311087c800400680709020090b0603000d44001e00d6907000c1c0c0b01c00c00540410824500403c0015501c1c00d552021240700360042c0580c20750008400d207001250070740d00c50075030342e01d81c0048841a50118014900003050304643d0070020250030100880d5060007220340b40d03650300a2019000d91030800380380041001c43d554440040703401d40e05803100c4161191107161103020611600180c854800201012604a03088020740a010b40e8028400b100580d034070540034080040442c1c050340000d000701c1c04c10784462030148080200340312581c0d54402c100e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 947834370 1250 947833120 947833157
    0x30604090b01060315050a150c08040b0c0615060304170c07050a0b0a08071107270f0f0e010c020307060c140a020102040317180405060604050a080a0b0105010314070c08040f06 77
    0xa1b54041c034440da58244040060b105a462140110921481c01603225030440c2045800d500c902d90042c03202c81e200059510400901040c03045c0a844205c540d450106084000c0010f140410395001c0d01d25a000505540c1d5001403000810520b4008015201c0d195540d50000d00b104003668400880351000240005502d60700643c020380c051002e092001c00b0403401c4803000e540b0803082c011418160602140d403c0700d4440846c4066419819540034866110b87c0e0101c0700140075004013075400c0c981459040001c21106005806000d582c03540290f0030f1a0640d15070310041c185003a414001e02c40423007401c80c48142e4003401000342c18241d40001d40d8842c61450b210441040e8186003407410f1009110852000c0c04002d80c0c240703c0c503c210340100d05a154030001079014070456109590100800c84001003c010100760b88607810700603d414601c5a9858005400b602c03051154a8242c0d68240b00245034140220300410301c0038000c442140c1450b40b2142e04242100d615088000811002030fa4066034120303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 947835620 1250 947834370 947834411
    0xf0f140307030c03080c150106030b150f120c0d0507080414010c05071410020324060322080706020a0915230901020c06040311090c041802030604090b010603 69
    0x2a0010700c0325600c0d54864442d814800e0000030201c0c0e10005a5448003c020446403003890320200e401c0304c4a581d5040040d000380715143d8903500844041890002d40c540704401d66400300302c001406458141002100d007200c0304011b25100401006003d80021034030b291041c50b02c035149a40710310440303041c6410001c2000031504071000e8640c1c10004841d0480d54001c0a803504181c0c4500c9000d075040e500c800c01d50a0255034540b01011030b20100c200a030070410206145117450b000d0f03240d0313444000c64906010b950f1200b200d00312210a1500c904140040b401441c03c0741c0140598001801d010b00703603071000180e9111841071400103140078018494500d1070764240c101c08901c0c0c245041d007a1544c00c104c03031820051408002c07020700041389030a0664024007604440c407800411943e512908c078903207003004202800d0b5050259403c24002074106131504125019034034424a0441d507002d8804030b90010750320003010300e60065200c0300340c0c6000505080200e80078116644022501c4207441003000300c0c008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 947836870 1250 947835620 947835659
    0x613150203071e030b0916110f0304030f0f0c0303050d0b0916051e070f11010810030b0604090f0606090506040b0f0d030c0807050c0f0628090f0f 64
    0x910410901c038142e6001a01000b40360300319204150f07000014a001c3c0c000741024104603421407003803c10040c140d11340710140140e0178202d80b00e1100c0e4004100d8034560711450302810300c0480e4810003090002ca40e105200c200980e216648401d80185e040d035440d03264101a03801100841c80128010740340d10780034081c3c0c001e065420741e201030183c60300b10407480c1400c044540b86800e221b4009a001000d04d4001040e1402c242030f0400311380c2d140741a140050580701240b81c16140003142c1c8a0744190743d0b1241d9030300c078003420089201440680c00e548842d9404a000f03880035a02035524401040001c400d051591314450013500c1c00a01c1380e1070081d1500030707a0ba000708950321a40c500448919540d403480c88403058480309070798603c1c4804183c03a040d1802c004c00310001d84404008900390003009400515440b1202c801d81b440402c100700401440300b180146020b4107040d4000c809214170418180c0f402c510080040e1404140382940d03070005503170750009500060102220708009001c4074035509281c10400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 947838120 1250 947836870 947836913
    0x70c090e060a090809030d05070c080c03030301060f0e040513020a050a06200708120315090112321b0a0b09010f030209091005030d030908040b0d09050613 68
    0x11112086a503441d0314006089010003a50780e03003180d080c48080c00607555811006022910b51071450f10700501290480481101d5540f520840494403100c0070808a06612002c2c00850071a4201b03001500c240042c401c41c941042250601c0f2803140d903460046078040e0040b40d00c1e0511800150041c481141903980019000300040602048034541c010044c4920303070b405461b142020032800f958a804c00c03616601404c224410030043d02c03003e2a5420045005107558080c8041741000107060001e0340d4800d100c0c0708140c4060021560108108840c10a685081d82c0744003105880d0440303201520b000e014260408580c000b9410084078002c084880212440445001a03168a811000400c80c4960701003241081030380d0745540340c80b41c000d40680f1800c080060140310700e40f030f003004003003032080c1030303100e4a8401d11402e03070030540c0c01e4020703c0b40040658110000900d054144032183c078090b80031101805c40c0969420443c80416014014140696085808120781104500300300d44483c100100c0d92800d07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 947839370 1250 947838120 947838131
    0x50319060803030109020903030c241003170c010b090106111b100302090a090603050303061008060f1005090904082d1c020c011d160e06090402031c05070c09 69
    0x1d0a00006890459030100000750b9a9a0302c3c00c0428114090105a01640d1161400c0c02038130700c500c02800303105451a0300c00c000051341c0c6c00344a00711040043c4406081850840b100900c04400758000302020646030340040707004440f800101c1c84c0044241d0040000410001400544031400d000074625024440c081e41281e002c0000094150744c00a000c400034141c0c001380840e4076481301d0120000800c04810204140c1d5580d00701140c882c2d108645032407003240d14081040c0c0d00d03405008842e00400020b0590780c6070250103018070030303050b003c00806010b0141c1170103c85515a60280510712651141d0320315a00da00301402181c00300182455041c060030701081041141492020642d6100c03880d0300c400e007103400340501501000303201d41114200c50754201300c46107000610a000721011114258120307103124607601d00c81c80704075246000d42a0302d0366584000c030b90123103444400c00350420f00040c192807458211031359070301c078692252200034003150300070565405000c13400d00da5000600c1050030a104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 947840620 1250 947839370 947839379
    0x20c030c0a02090a111909080601080a1b0e0a09050f0a05010b100e0102031206040f0f021806030907060e120d02071d190c0309060c1d060405090105060c03160305031906 74
    0x2480d01030106240c2c0c1c000d502001161b485441106803100174082401076a66550712148030310b454000090041c1e5088071000500700090505242c494100c4a9500b8241b1036901c3e422101c0b4050105030a0640340e61245180341240448240200210540b299000003890030500090103420352000c4284405d01200c035001c095181d0300401110004044940d2075003490b910303000000c005061604800c01c00c14945041c03d03000705420b500a10410304294041643c0703c500a00f0004244401c5410240130f820241007044003c0c0a02380001c20300b1001000c010340402420710262414145507403250040e8000301d010810880781050912601c03401010f40049450840c1030102c0001181020705a0180d4031680006c1035840380c0d0016071110341c4010240511a207503880200101c0c0d641035100b0008009011201c0941f42140840e004c550010b000448a0f030b01e410104842030700030780340d401090b0004201e0054618440c0c2320055859101c0c0d100c0d2916400c1c64100c818085401104030021035160640900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 947841726 1106 947840620 947840651
    0x6011b05030304230106032a031416060c0503040509070507020301050f181f052a030403080609071e03061e150503011203080a020c030c0a02090a 64
    0x240907042c0304c0220f003220b600d444014115100046400c0e0842d02045245054211084484240760380c0d0703841e0441e01e02c890340c0e1181e00e01d4011841c4544803207481184900500392524012030740c00d506a0f1902c2d641c0c41030f40186c52250b000000001c6085100d4400c881d00568090004d0106080068014012070410349600c0250800c10109030304002e000600c4c6001e62440c1006001c105002150780c900034180030706441c400c5030800d404110320440301590000042c080d51744140da02c0c070300b60500070010040507002512981a10052001c000e0b8046e0500996440e42003841c481166a0f031400d81c0100860f900c07012038121100c903420038180008034910300700c0d003440350071603004209071108440a01c000d0107000b88070b0790403100050110340300d54425a44281c0c0050010303d80384482e03003241d10710380020300e03440100d910000080007142441000b40f07400040070321043c070040e92100002c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 947661870 947841726 := by
  have h0 := BRFrame.cov_init 947661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 947661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 947661870 ≤ n) (h2 : n < 947841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
