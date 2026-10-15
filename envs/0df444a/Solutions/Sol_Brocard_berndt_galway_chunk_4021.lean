-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:20:56.877989+00:00
-- url     : https://prove2.me/submissions/4a956c08-a0cc-44d0-9807-3b4287f5e4a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 723021582 ≤ n < 723201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 723022832 1250 723021582 723021599
    0x406050a18210816050c120406090314030310090e15040f02040e150c0f0d09060e1011040909020109080a05010c1806120e01060f0306240f210b0406090309 68
    0x11441800409130102040765000015103080d0400c403001007071030241c514410305090302d900c081c20041840ea561000d89901e5420140240410760352004072640003041082070342d100b00300103541200c040e43c0d0b00180c00b80f06070381e41302d0500031180d8002c50318501c6201880107100b9a0200b808541e070007120b04101d440c040486c2650f4500c800d07059000750b40c04001c006003140c0d0910000d800c04105800907640f0b40f0341440d5041c01124400b0780112401c80d914a40751441540c100a1802c02503213150080141c510f500c1c5030707088280102c0c46012205500c0342e10800c11039105001e140010800d40d812144404110310707105028105502061001482030034003110440c00404100086550603111341056803001d40240d80504480b144090709592690340028807a420b40c03880000840c06110001100c0301c030214225049031024a00242c00011441e06000c0500501e40300c40c01c81c3c5017003401840d5400481180c03400e08101c8900505a43e68020807c41449070941040410503c66034846034866114543c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 723024082 1250 723022832 723022847
    0x815030105060315040305041a0a030c140702121204060801080c04050124090e070203040f090e120c07030b01030c09050717220c0312021b090406050a1821 68
    0x102c0d03410340c0160401036110850490254005020f458030b24502500e41400c0031400c1001e42000e0300c80880005c0d1100340c264503214008510f0221700c1c15440800704c144030307804207009104001c0d1050806a24026079004104400304001c0c03003850301140c5a40e5a020040c142c0300e0240b00346d130032070b00a4503013100d45880c151085505a607803a8200a800b0104130300b25000c04103601c0c0300a02440030355480131030280c1c41105158801e1501e82c1c011940d860a2500c04030f40031381c541d400b891384681054168451380e10041146034a60f01304040e040e4850103132080307640c42d003c01d40e0b00192040645034004401d201300303501c468040ea06041c005001c561240f000c112441420300c100154094142800b144201845c4403507007895032000c002e0500012659102c03117218034101e62040300d09162580c1f0044000e9014000d1000740300201104030049203041000c58101c50780104010605941c90000841a00e480e81c4550525440c628010146030300c0c500c0c040811420410b554140950100c01c200201445045d9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 723025332 1250 723024082 723024091
    0x2011508030c0307110402162001030501030c17031b07030c05061602121e070608130b0c1303060903030c030501050a03050c060708070f0506061c12110c0604060815030105 75
    0x20343c5050855110b03001801711603d070355a03000b602046144c501064085148400c1409102d20b1460300f05400e01c0794222100750302916042c141040d0040001c95408903120003141d9445001702001354164089504521800f51007040603c035945c402240c8a00000f400307000d581c45003115070b10403901d17101000340310701800340c0500d00e0b2580d13800c044005080c2102e8041e1604040c40848020281c00c88401e02d0582c07001c00c0821030b0303502c007a2081100c668004000ea410103c808082c00d03000110b5150304c07a40b181d0040a9103c103040c0018a010001925100c58008603001101040303054614500100540405200200081d040c1340002c00c071482c0003075240080700d0740b00c1c004084c1004400c0034480c40c3e400030f12342582c82c0c210a01089000c035100c02010041c15100e42c01400042c07511400300055002e5a500c8c030980400210611800158800400e03903942c07610307042100e644440a5000f40c50400c0070525240c00000105001803016040071815004041e41420754888810007414903089880c1100c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 723026582 1250 723025332 723025357
    0x708120906090d03050c03361008072f060f070e040b0f06070f051b0a06080405071a0c06060d030903020105070305071707050f2d01060f060201150803 66
    0x30020482d07140c20020482c03c1842410140d04000148000c141035800c80c0840f124000b4136910058040a10b105854118103500318079000114603038400f140c0b07400a44007068060202140100300e071140503114500d43c9001c09812182c3c0034954045080c800c0d100c14541c5151440b80e03030045030301140c078003204034480c0005a844001224080c1c0401c00500000b81c4007941003040528089416107c503070060030040e016400030f19180c01649401f034034065400d80410202c1d00e0309100c540d52541c0e4012291300300c034444e10b000d03089a150f0b4100a4203180d1283d102480c040521035045c00000220700c013030602508100243e0385580e9902040c072030900700843c0c008001942000041c00158000c5014080c1c45009140503402d01d1580d903078000c01000341500d8030314800e00c041024002c0120801040340313544500000f41c0301074451b2403000c044d48861034440f0040010340d104401500e401c250b020b00014414900b100c1c1010761794020107802050315980881d00d002d4200e0011902d00800411a00c001d15100e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 723027832 1250 723026582 723026587
    0xe0d02030d1805030609030901090b1c0c0e090a050a0606050c060106111c020304151b060509010221090607180b03040303060905040614011409010b0903070509090708120906 76
    0x2544129154110300c1044079441a0b5a035000c950750b241005494031510320403000b0340d9140806800988100030030350014149a004100c41601c5030700140d40b41000c8522001d022415055080c8255401c0f500c0c10400d5401c00d030b9a07003c11200c0100b680003140120940d1030f0400409844280490b018401c00c100021981e00c0f0000401906102d140003464080010080c0c0e40c00402ca00c01082d406100001802e0040c0d10100f000d001702d000c401000c0300801440d0600481e8903422403071048840511420150202ea9240c0020701844402c1d01241c010150003420381c5c40c6011070140e030700700c5814141d404802e10300c01c40c800142c800340180b240d50350039403586005d403245901d429850215075000038421010507868100c0080c0e410460302a042c041c80c4143c0700402d641c0709020307007480d44e4041640404211031070091080050f480f0800218156800c4080c25903a801005000c28035240b610b50020b50400c0300ca408000e03040034080780c5c1c0e4080d1100b89044d188544940c0c0c0d001d1102e0300a05601e66031100c400c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 723029082 1250 723027832 723027853
    0x4060b0409170304060914011e0b0f0906131503050715390803090c041817040e0903040801050a1505060313080a0c060f1107150b100309030e0d0203 65
    0x1d46010310f60140c850070002c0790b5000c1b1a9a40b100700c18150401109981d101c044c1600c824009494405404001c54400c0010b00c1c800f1000442c1d03925041d0074140502080300c041000c2d521011090048182d010a062214100b003c070301441c0389101344001c0e07401e4000d44102084002c5a49034a4420003855074550b484d000305078080c0c0100c5e00c02180b01d901c1c2640c440a410aa81380e881d4150100f0f00d0294802c07a1700da241c56404a8100809680024420380c500110219404103900c9200602608403100040400e0100201c0c3d0951182d03400100c501c070380c64010407290709070000c0188151843e420080c4050744070684e030141618054446801046c900484c1480b207820b10310059030f0b100740c590f51103091640054545030556800894071200181d240c0c0b05001c00d000035030142042815a2200400140203000e41d240c58501440e84000c05180c03054825040340071a81e08a4141d0100003440640c400d130b0340350000f800a00c01040201c01240070113442079581d00e00410041540e84c0c000d0081c0161841 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 723030332 1250 723029082 723029123
    0x1501030b07030216030f1e080109020a020304120c180603020307090b030118060c0207080a260706050a140606120403050c03040f080a14030a0203090d1a07030504060b0409 75
    0x18000c10101c205a0f0030300c41c800c20440500740980030540280c9856080200c02c0702c00a010510f54196207205582d45066450455801a140c1d411111761180c01a02c0340d034404000c0381948030703a41c0004030b044240c2d0103400c280141541084101c44169094140004c1007122403000d8070264070020754036401c001c0e01081003420750780020108041c001d0002031018404405010f0700d43c44000c0c1079419aa407182904100380e0100001800317000302000078011380306c040d81e9407800700081800003030303090303520010741c5802d4140c0805460b412030380803c00340030360300d0548402c0c00101080c6c0c0c8204101c2840c030b40440e03281d05050040700d104c0703030329205d03090030555503514191a150b20000c030600c0c083c8410400001d4400c81180c4580c05001508003400116140742002c0c0203a0100383e0b0240c02d217800c02c001e0400b00640000490301d050005581c0c4d050700c2c00c0107043c21502e040609901c245542241030800c000154941d000a104910030b100811401c1d0705041484101c58605200515100032850340303912081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 723031582 1250 723030332 723030353
    0x503310504090c050909010f0c0e030c040c0221090415181a0312031902040e04031b0b0c0703140f180f0d030809011a2211040b120108150103 62
    0x90183d8401100d80340d46001280800300c084407800251b9540f020180c0080a550241000075412460007140c003900e0070000130740f00d41c0401c5101d481190b41c0c21101103003034020701908007420903600400c21041513181100034298000803040f48214a8800440c000303118481e004815a2a110500302c0014207800c010401066a8101c1c502c820700244e001034015279080041c040064046500b941c0c6905204441000940c2c070700c1c000c1d110703050040c041400743c46600300d0120740c0a601460503407190078811411480041401c0c0001e8440c064002c100720078183c101008150702ca219640c4c0340601c8001e40c0442d881d038000d8a179400c06a40341000305529184c8050700c4004408001002e004819180b5800101c49424603c01200403420350010401140c00078842e156103007d1108000b40c80303014000005015000a1001510705c010311424032000700116440710114002c00381c1c000303540385d84420044d1703807503040311340360825030704031000049615840030801e80100160050340c1c1d4a03e0342150343d045c40b8603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 723032832 1250 723031582 723031601
    0x50d030917150c0c0a0501060801020705010b0a03050d080c0d023702031806040803070b0f10060906110a1b0503101b03020c030f03010b0d050f2502070b04030503310504 74
    0x610446174450080f032020300c1401d0090050704001a40c482142c82c0c4075094a5103509424801d40c600102000400c030040b92084258695150000301660390120317880c40c5004808500703840b00c0c030124004040720403013003220b8441c100308591012078180d1002d818040050007102080160010b10070341c40b802c50401e481c4040c00400074041401c107911789810914540040c0c40035511200300300284401a6101400b0a400c403103041c074403c00c01400c0c1035014207400385502c01c0c1c404108d080200444130310414005c141c0b115602c0010342000c04102c1900c10308015107409040e20901904510614948440c8a01d00e0062101c803200da410f00d2203450150000e400c44044840f041c001045039205a50309034001394060600c1194040d1156601030380001203882c02401000038505500a2042e405100b01900390070304805a400308042056840c101e040c9074040d48100306995010801200b0043e0210161140d02c0100d80c60000000a40719580b8014035034500c0102d0b8403024003028000790401341c00c1818403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 723034082 1250 723032832 723032857
    0xa052511031611040c180b210a0b09060102030a080c0928080c060a0c1104020d090302570a0303020a0b06060307051c06050d030917150c 60
    0x41600500e581c1c8002d50040004075118607404030306201524240c0318500008440d03103030a10000b02c2c0e014002d03c02c2c065602404410200200e00362003600b0311601002070349042c140982c00b003810088000c1014101308501603109102c440d0010b1507651000090b01d0200301140c0d102e9025480724405074245900008480c0c2c1c100303156074826500003055460710304003d49a810060005840c04890b40d04049801909034480d2204204801c5000d80c003c10043e107541d0025030300542e214149000800031320409014964243c1000061820f00d038010402d01440034010700000f0400351408c4d950740b5007084110b502c01c03041800c0e2038040c005100784a0070040b2003860740b510f0b450110b1103500044000701c80780d1045005070310114a401c200070b045120550000d0084e42d03441e040d400d080d0405442c500400500b040c608091101d418000500758011000419014180b00d040c0015410014010000b50184c4158041c440740e01d0300012000144c422602c910004a40b81c454540d03400d902d106600c62060704a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 723035332 1250 723034082 723034087
    0x90203100329070807120c09270f02040609141008090a02220e0105071d0a0306020708030f011502060403110c0a0b210402030a02010c0c030f05060a05251103 69
    0x1032002c50403080728003c2c640b07a19445a00d01d1700700d03802041c10000b98a2005d03190304224058103041d801260b50130903102010b4041c84005400d4800c038049026070b1907110501e070304280707030700d1b24903c199030080054400550305da400f01c5450b41420005441d0410110740c03c20701035103900d0303e5030b0301c1807800c2d030b030040f00f11010344070074040d40c0e0009280e030020540c8611038030301115094400740c500c0d441840080501c0368000d100354501b1860241462004681100703550043c503187c011541d6540c400c030000341d60b0021045464545504040c44c2907002150740d11203a040c1c0c0400030460703003002d15681c8035000050b4010f04540da92a60122829a0070120448003445210100c40556a80900d18400350030303a8611151100000201c0225040c4282a20b60319230115009210250701c0c0440c045001d00c0d020300300855144c0c011300d000c5000b9410b680c0060400f000d0003440404100780440c0e0039020311006a020b2001b51107020f60920000800d900a4418a0f68042c803e0305550007007c95101130501c440a6a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 723036582 1250 723035332 723035393
    0x60307050706020d06090f05040c0b0a02030403060f1b1e1218030827060a0e34051017040302100e0f1203060a0603020d0603081809010902031003 64
    0x500f643c011a40f0842040d85690003440f0240c0030f407040440380955800280143d0500f5202e90f8003210361030140311a05c0e8400108401c019008000b214025580204100003081001860000401000000c605c0000c54441c00002003032240400c21201e003400501201384d43d1034140150354001d94244801031091b202c940c6040c0d00040c54500e521000d000703403191001454420100c8680c900940711804a0208800300000350701000940d00e80d1024481c0400615090400c03072440c60705840c3e2000200c1131902140076249002c0402241c0450413141210303880c02a2984104052203192201c030200090b9001e40105842c4600c0c4102c0390424040c1c010307100007030800c0a00e802910469550060950b00040305100e00d08010012160346182c10400d01d4210b00b0300c000001c4401900c0d101d52030030590003045809a42842c2d6014100543e807140c030642d503400c562500c02c141200070301c5079035109541c940000a0844102e000301d81c42a01540c0c0e10f1203403141035540e200b940c803c100c2e00720041d0090340042c45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 723037832 1250 723036582 723036593
    0x1170c120102070201030f060b070b09010f051f0605162307090e070b0f03060d110315010e1501020c060c150108160803071a0711070e090c030a0803060603070507 71
    0x40034051060340001da0341e80198000074050350760283c060101d0501c1c02108000c10039041c402d1703683c1c0943c4031f00304403416182c00d01c109014000c030f1000c0b102080e00c2d1205024540c0010f04c482503880a0302c00e4424100c69031800140c1e075a02501507086d4100b0001c203441c8001414503401900c2d51009e98400904604407001850718003105508040039a650300c01c9140006d040800044004020b081d03a6a490500450301c9074010340006800140915803881c2464108090f111030798001602c007508858208a000b841d041c1c100340c0c20720442c0010940340d0080380b14403030b0100504c211100103070020050542403906021040c0c0c80928601224000c10595580c2d01d2041c0101900030249240100a040502c0549124500c1943d0106085500170808400000d50880141065040070208600607035070b480c4040e6808ca11490042c1803601800c1e00c0856840d001c60059030191418104951460725640c003856511215030178094140e28060002401c03d140c84001598404918900141002e601e80c1c4d80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 723039082 1250 723037832 723037849
    0x3060103021b2103090a021c0506240102060432070f05010e1905190b071a0114090c0f0424080f33131a010201110301170c 54
    0x6640d402010030315a9180520404818104401e02d1084c03550508458042d503400c1c0410000340210f10f10b9120200c01d4180c0b11002c114290803000f42c50103850443c5031038280003880740040c01c0800c4090705554603540300196041c800c030303071060022540700301d076038590b0044c003030803481d02a0310010312a2024901c1c042880345200030804003006003034135030070000003500c003c00c9040701d18007075500100b0038031450a01045890880714141e40000300600e444004001c00e030300c10341080d640d0501c00100c00040142c42290141410804005194035907283c4424809640d5070000250740102600f01281303e641aa000401d120801001e2891825a0314030302a0f001a00310b4404c442d101c03802a42d2802e51036000000164400d80c0650550382c03d15004800800341d22218614007084200c10700c3c0e00360305024900c104185000000c0054400503010714040010307208500301001450705510074002254014000d43c0c4c0d018686c0a082e03400c51782000148180c0e800302c24030a41e40361141d404511110307141c420700c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 723040332 1250 723039082 723039127
    0xc03150909191104050a1e11070218160912030e030c030f03030a0e071a07050a060510030302010f020a082d180c010f021f060806010611060c040311060306010302 71
    0x549544003c0c818100703c22900c0091a40401c1c03400c01841c0c00c0d00140c1c00e055480400f4848800051112842c070541100f4002c070f00b03009401050106040b42c449024406d424030a4040c0b03e258220f182442204945030f158a100b000c40c240407502480307001074010541c00300360b5030000d001c8421864081000a181402c40038251106410000c24000f40051500030761001003a40401400100d1900c601d401000341c01c203290f100314200204181c400c101c001e0203410071060704007405011300d00f07080c4aa00d5400c2c0170b6200840241d8603003102889a00c1c43c40c02038072080300042c1c6464150350ba80d810f00d5442510010748460701c3c1c00100c0c9000000d210300b101d03000d008440700d00c18441c0815035482490703d401d41d0f100580e418482e80f4510080c810394009401d40702c0038014980900c01c030810064140c040c141c1500483c0745070244600200381035034070800b0808030f41c81d80821240319441e8245003101c2031103140405849a28000149401402e2910080d5017015041c900103150103a1200c0d090f50442d00d022 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 723041582 1250 723040332 723040343
    0x203010902190206060904231213090b091501020a080d0b01142d07081209070b070503030402101e0c1b061b05010b09040303050f0c0315090919 63
    0x154603500e00408444107010300620f00040c051401c00c039001803510364009000400c100c0c2d1600fa4580c0341084803a80b914040300708001c85441000c1041c00a2240c2c00c291600120f0303060303040d000994405a03028000c0b41e03c01c041d0282880343c585410301c03024902d900b62014194410fa08507240002c46220042c145d002c000c101c0000c041c415400010300c40c43c0048140070102e00103001352103082003081400002e0100b88060400300000b03049003142640a01c42001d001d8010200340000c01c0340c2030600540c89140790109542c00da546450f16001d840c01480310190956006200150040c100191411403c003502d0400e000740101c200700921000c0394120805000511000904040001c045490106021454003400c111400c002c802000817042580d548403892840a200c070a1040c01c4d40300061621000c2c1400400c0d00d428240903010303000907503c080034940c022000981150b040020f40307000d0140303030420840c1c9103030210401400300d82c0500300380082d0054080380906d80c0701080b0211002842403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 723042832 1250 723041582 723041587
    0x3150b12010b030106080a0b120d1101180503180a09020309010e0105010503030a0c0b040f06110c07060201020406050f0d0f0204080a03020613030e06030702030d1a1e060412150203010902 82
    0x1115020400d0310103a0002d10301c0740c0d09000502140707410100050b44201e040000164062004002030351200c1c50070030411190080e100181c4403144e01086c50400c10b03076094020f21078000807001007807006e4141c81c005002d42d0403d00200b51400e080d02c080b841c009800415403000d0940301c4400d04202e0f07206580703825440c1c1d0759003d4810180800e0140500400086024609210841d03801030004507041b48014880440240040c0c00c0020203520002c031250400350820105101c003541c098107511903610407105220703021002a10340e105000701e46c00d5907580e40c1d8460400c41e010b450440b0a4100403c400442c0742c90326071502200c10780d0300c09840200b01c0303d0700400258403035040c06030902d00040c000902200081d1502c4000c01d07040420b40070340000075101d40d0303625a50304100f02d00354040d2102420b4028100320b81400340c4581e5071090070842c40708032802c03c450721030703540c0740110594007a050f142c2014040c4002c0080a0040e011600541d004074102c0b594100d080046004a034026002625180d501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 723044082 1250 723042832 723042847
    0x405101403070e010e031b060d0f0f0903091e141c08092b03051c18150c0e040e030d150e010f0b040b0f0c01090c1e0e0103020d020103150b 61
    0x8a10070868003001d40107091b044a0280350b000a1a6481071200d0080234000390f0201c451096a00c22003e2244c89001003100590310f001c1600a0b206140e42540094070310354000c181c802810205171070282d02d402060742102d281c880b54102a64862420550101707000e0b81e11502d0380d1110400c0740515200b440020750740c1c10090200701c052484000c1c1c585104040d02c001c2e2018243c095807048c103143e00760410a4a44007091500b82110300d903440309a0005040c100311007004480002d070503400302c1c40359000264035101041264101c0d14500c481c1700018403030030001030a5051a5010843d03544c614402c2d80c0c903241c240d01c1520269540c0308400c3c2d6800f42155030802c1041521481140501648005055814541885081280101d02031120707654000a68000760b032440703c0c2102d80790810341000340303c1071440381031090f0030380038900c076034200206030080c80690460031034004020b95807180030084650f400c2d80c081c4600e107040c0c00822418595038051150219a080503214018030b880c13001e0690b210070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 723045332 1250 723044082 723044087
    0x31303030c0905030a020d05160e01031101030203060f0405092109030d030603020607080f1b0109120e01170604060e0906070e01020a080403140a020a140909070302060405101403070e01 81
    0x40c4070a41c0380c10862807080500c0140c0d404941c5100854046600380400841814068108100241c07501c0401080711000507000d44100c00460403240a42401780380c003008a030040d4160b1001b140c419510600040c070941691425510950308503002c80304644c805040c82101082074421085000001d031408180440d691038108202011400c2ea45002c3c45131600d1540420064028804001c2c0050004550003449600e4101614040c1100c80102d009121400d01c0171030003418047c409507540f400d152125642c0d14040c440b421042041030707554207890800055810440c00c0003400da250300076210b2000191a008100d5454080e0f03110b10043d09040c10004005000c1885601d407042c150f4000754640c402090b011801d03182242d0f040107040b61111071240842d0705214280710001d61040d84010301150b800540302c0e03140700c0300300c0c103071101810b41e159a100301e5034464403440029406101000141b29074104960b2030024955141005061003680c5504007080c1d4004940c814001400104000107a6a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 723046582 1250 723045332 723045341
    0xd0c060221101e0302010507122304030506070305040804060f030b0306010807170d0e0f0d1502031b04050a1e17100c080708010501050a050708070f0512190c0606080303130303 77
    0x2090f5190080c90303407440e80040d01500032558050848001944498881030081058004190526004943e9010301c02900f07410b0350001d000c203543ca8420b803800290568082d128250107039402070081c50a041c0307003240c200c640e28020b6003e04101074940303007000c83d5500c08010690180c081030010300201414143d00c0340c0003e11007103105200e03070312503e469480c41d500090307a20111031080c0d030203013100c00d5490040364044070b150200405a2120000281000400da40030f903002d4828800a0b1005140a42d1803851314001c5024855200d82c1420003003004403400011048030300e40d854684804556250344803031030b09440e00600700c000d410004003005003a205209142e95806241000842420f0036440103209007014000c242c1400f00001c4e400c01d0540c012001d0310b0805522209030f82c3d45000d10f140801c845104500211154441c086840d01184020016a805400a11200d500301c12411808951542c508101500c0e155076480010500c11400d00c02548685000d6100c00c8159145180050444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 723047832 1250 723046582 723046619
    0x10030602031303020c1e09100b0703120b06040608060d0f0b0f220308070c0c090c0c02030c18040f0f0f03051909080a0b04050312041208090d0c06022110 67
    0x41001d10070750181c0e40c1405d006c8803980901680c250ba2540d8074032158568800c0d82d50044588070a020890808250b8000303000740d5a680c02c1c0740107000000680c418446540111b008210115a001000030054104440501a0385004110048550301c56480d10411854103440c58000c4d24500d00410601181d0440ca411455140650440104100c0d0b1401012080060140000c1010b06180070b414031203200d9420f006429031100400ce40307080b03a00013900e544c2503a03070124041e0203900c0075550540b40240004424407c0d004910700150f49580d50a1b01c3c20b1003140088a031a10b0741c0c030500300400c03460100342240078481c2c0c1322540d0b641034040a107941e070101001600b04000003480305020920004c100080d240d0741c4120010000e8546103032490440c0544480400b41d0080740040000380000a159040680d055456500306134442c20303c04c0b91141501038050010401510b114000502c0580c020502025241d4003a921300d090300001c007004600a85e8064503880c83c0d821b090107401c2c03010304904102c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 723049082 1250 723047832 723047839
    0x2406090303030605010c110405090a0c150806040525090b0313060e0601051e01020307020d0b061212091e0409080405130b0d080310031208010303030f050601020c0910030602031303020c 81
    0x14103643da80320713002c4604068480323000725107807408078010b000b00300841200d03254480f600c3c001c616124682040b045450a526000140d62140803c1e101d007468443c0c01e00840d50721008080c00401064200e00b01251040711100b001800c0d400015944241c40c0070754010a421450000c06071140e080003400d0340c0c0307011120440c2d0b400ca03200420196842403090302c00311380741d901e08140301013800005038258090840301942001e0841071a0007081400034040c2d1080700b040f1400303164100c400c40784985d00c02400000303160214082202400318a02102401100060229440c0201d0a200c021405881c074000044031a5540030a081c80300d4505086880c034a0121944200440c2011030005000e880560401409440c00040440c6070000f00550700005150000510100d4160009006006031024402175000a01e810113100102606004090060354164010716042d4000000c0001a080c050503840744540181d034000b00150060000d10311400c2e5445011104035020304002e400c02c10720041041c070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 723050332 1250 723049082 723049097
    0x91203120a050604150902030402100c0c050f150c0106090c171503071214010c0f0807080a0b0a24030203040f0b0c0702150a02070e0603070603240609030303060501 72
    0x280c020240c0c0141d00c00400040451941c031250041401056030500102ea0f454801c0004030340316840d81c008500591080d00c6030071074005080c00841d20300c0020900100408010345007080507250980c003046440a00422440d070807180e824628800342c1c010000d850b40359444000412803000244141c1242d2403032410584039110030000c0c11103002c0e500074042c1160864201000249860801c2010003070210401959100c040703e040c000c0e0018404280303d45150b007041c0c0745c0704031180b06175050100240302d611011459144c801059590000013000d840601d980d901c80181141d817407104a200a00c2100ca074134182c000c645a50110502000b60341c4420300d401001440000381c6a641d01c0909250083c810b240103488905540d421881640c0000e548100904220460800080010030f50a9425001c581e050359403802c4071404801c04035421941601300700342c20401c5078041c2e00030b20045030300b0301180980071180d44200700480015401c49d00008078001824001c05805115140c080d01003402d0140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 723051582 1250 723050332 723050347
    0x3020d030507171003060908130906060c12030e060c0a03060e07020c060a0c02030313080105090d080a0207020a0f0909120c121103090406080d020c06030c22090e03091203 75
    0x420f81d1401034984000d58410f000000c9440142c04041005180c0c0190140300883c500d04000c1c00c1c80e0404088180e2001c0d0840d0001200c0c1e49034440c40c002c5075400c0d01c03a110442d12a4441010302e4000c0021242895120085800e40000510919100e440d45551b9140c503074600d140010100d941750381041108030114420b000080e0703000541303030200001c1110314a40c0e030640fa0300226100c082108000f5054800418145c0c0005603202400050703031040c0000304050343d40e9900c41607a4401140600010806d410003052090134103800503c401400588001462941e81103524680d02c410f5104100e00380c5d6411284040012280c0a00d200c6440d914040e1406a010f03141e000820515058407014080c201c10092000ca9090003039030a202c034024001c10229640728001510b1f40d0102140f80018081e226000701c20b490040242d0780644a013603001ea0608681400d40c0d615031908100c0d824040ba030810740000c1c08422401885134030b150040c081d58907030080d0400d010480b420046e2140039500140000b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 723052832 1250 723051582 723051587
    0x140307030914011a090114060a120608241b0c0c060711090f090d05070303060b0a120f0c0c0b060d05030313061104033302040f0f140d151104080a03020d030507 70
    0x8807140301c02120034580e201090101030321040840ac442c40d010500340f50300006c01e85c20100f41c1d8000381860911a820008000050040c40c0e541100c6407294a2044261403202c01c4101c00a07003401990031040701c2d0f100c4504c070b0009115030003642c400c49043c20741800c840f42c2410006542070300480166610407081c2042191243c846c60580e41d079070200480440d20b0703000c3c9403207600010001d01010010641d20f8060000080007541c60604503103025040ca4048050000f180c4511040a15255207102c541c1e00750b03650703a4810b01c0c000b500c4141c3c89042040007202255041c4001e40c020703410100c000c0c000603003d15100c4140c0d84486001c4290708410f0208002003140901c8030100b188445000f1015103044440010828400c0881c1945051001c140030802c040004242015144c059102c1c00c2990b9486002c4083d010b0003038034032074000208180388000112000c02030350b003440001101040502254510468a03007040c1c0c44152554000742543d030602d42c05201e043c80301c076820304e000e21181c41d018001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 723054082 1250 723052832 723052859
    0x10305070e0a0906060e07080c19110a050d082211040e010912031a0d02010504030201080a0204050409230f1b0f030105010e160f140307030914011a0901 67
    0x7480411200000050240701c0c0382d500802d00e8580c04601000802c0d12510790802c5840c048414001141c1070300041201c0d20300c0c038400d4800d003254086e002c12000b1001d481c0ac94001c24141c11000781d91044550400004009101c2310340c10782d11039690b0b804075150203100c084c803038200394800183e40c2d030b078402c900000700d40c0700e107914805000300350390104820002e061947d0040c850140060310200343c02a0400d4180e0b03044c4c120060000211311104105071400041002088208100a0210300100710810055000e20080e84e4005000d000040c2041e5139040400e040c0c1e00071840443c0c404120318245400b012088400c0d603001c0c0000c200420300c000718144950741d54007945074044212000150000407550380c01c1c04218100e0000750080c0080d50352a1106000d1a005883da0b114040110100011641c4a01580e0311401c1c16691194000f205030507107650294005001c1c1000c15032075030460700114180e0626902c0300100c2d00000030b005607000c480c0445402d400c14403144a06500f0004200f0005844503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 723055332 1250 723054082 723054089
    0xe0d0f081006032301080c0103060801140f040819201603082d0414190311010e030a0510200f0901021e0109020109060f080a15080f010b120601030507 66
    0x100084e904038100840d07642c4150b60001e034a4450301100011540103004984000c40c2c5038280c901780700703c0c0d884440c16401d0b41d02c4020000c01103810b20002034210600f801c0c400341c01c2806980090f00c3d2654841040e101e86c0c03001040c11000c20941e60004816240d0001a0720302048604054051040c15001c0383d2500405448054120f03070020840300d0500084203480640158840324011149003440010362036608a40306080881116042c40c0f00d841c1021840c1a1962202d031080c2840641981c1d540c58101580486840c100854900d01e00400d4500b0019400403c1c0990000d129440d00d00744081c040d0b03000d80900c1c5d284a58100b10000d40c05004e07500380d8100190404c0c9140e00c910032480102c0c03400c02a110440a9200c602c400124051010340c000410f0310700031707079403400642d44409056604880c0c46c10a10300103008180024603001040e405910500d043d0444040a43d03614107000f0703c0d10140d000c44000e03903513503850312038054586031103205e1500080c034018041c130f98519205c9a449100521 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 723056582 1250 723055332 723055337
    0x3070506010e150d020402041809170a0816020c0d0302150601030606120e1204030c17030702060304110a0509010b04090b2710091109101d0d14010e0d0f081006 70
    0x40c44e030465446806844c050100048081c1582c440d0001100140c00d075640b0907034a1148441d40248200b811500b101c0700c14000e510303104050707141c5012084007107240907901400c6000d1990f03110b0160742d0741c001081c02c0c940240d00500b000400080700e400e155801403c490f052500d03041c41044000c0d002081040c0d0116800340c000365400d00c000382d545c2001080507a480c044840000e0202c100034a03031100b04141c0b05008042c6d410207031100c40840d03a81c0310b04100070307500000601c001000690041220310303410700d014141d440d035587d40b480851105202038100c40304ca0314000c10188401d800911408410040441d032a0641d07034414031544660f0400c054140a2000724000003900c440c8480c1c0440005006205003006110459414100d20703401c035010040c45030440783d00c04050107215080450020419004400f02d0111900400c20003210748031045461000008500d680c801084c07194943c62113121000c6c04000303003402d000030040816140d2030824441c20005022246101110360740c195036050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 723057832 1250 723056582 723056599
    0x207081204060f0e07050621010b120c04030309050609032d0c0d02210f162c1503011509060e01060f17040606080a06060e0a02070803043203070506010e15 68
    0x400381c46030310705c08c0348a80c01101c0d018900005412403800c00144411558054808000d0f01c841c20301d00703850b00c650711000e030008441e81c20030301c298540340004290f4407100400f1100c074440001c8503031410b0703400c51041d5000320f44401040c050218092254002c40f07074044880784a4100203030b00080c14104e041f0103071020900c1c1c1d03003032a0b00004401c0103103041502e4200222040c202c0d8503000c0c01c440c3c110702d014080d8031980c914a01c0700b050040085d07103200f00c1080c42101d0602d0355105914003160740154002c0ba45592610621724640101200e501c01800141c0310101da5a030414003030100c011410b070b10103030800c4032900000c004154001c0e05041d000414080140c019185c5040c41c0002e00f0b000c0c0c004070781034080c00c0910000c1056a9101c1c07808c1740c2280e054880b05a550242003812801070001c0039025a404000042c0040c402c03001c1d141d800d07a08810141c03d200610303035400d00d07800c25880f0741d2001b591000920605110302008114010400d41c030740c25800f8908400c0e80788100c1d00b10b040c4940241a407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 723059082 1250 723057832 723057847
    0xc0f080705010e070803041e1d0403090b0409051501080601020a060c1403070806041a0307291201091a010c02060721020a15060605120a0207081204060f0e070506 71
    0x2074210701103a01e4081c0845031495251014962240c0c030601c100d02308200c882c2e0186400c01d02101d0f0b81c3c41100d80b0b4807603c4080700c0060500004624000384120b04024010030082150003402c00540f010f8050345500042500d002201d05c14003900070300710281408a8a0700f000301507a400100505020b50000d4040385211106c070b82270791865400109051081d002004210358594000c84c003500c120300c201ca0a0254016042d0301e001c445c45444116605904246028801d8030303000031240b00034040c0030b5804810031a1000300802c41d6040704002c4550310402c1801000a54207074054680c0541200840341c00d01c4e11800c002030007411402500034024140810710400703014040c400081400743d600d03001c40041100c03040003910b40442d1401201c10324a0070700c06003840c01c6184104d0701621041d03212586090013a0f100040c3c00c00c0c000300409001e1384c08000610000740740001074400500d00381041a02400c1600d0700e1015902d220402a55051a00b00c03441000d01c00040d428080316010741e083c5075200c68 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 723060332 1250 723059082 723059093
    0x71707110603040b0426180d0f05010603050d0809030912031201030c0f06020a050d08060d0501020f070201031a0915030c1f200c0f011106070c050c010c0f0807 70
    0x1100c111450780010080108000c0c0240201400c1c41140310304070100d500e14541440106031042102c5480319030506000c50b0080d252010b81c02c403418040180390100011556550002807898990101d03203694580a0400412004020010a410710342c2001c035006d00e00100c1083e6240542140e40b84038030705070051a00c5e20401070040301e814405c0400d40804640c3c40b818078112410b0345100c0c030f0b0b0b80b0030121900081c00c1840820a05542540b14001e4006103800a13012540181d0281000d0341c0074811400100016000f480101942d18071040110344441c070900002d000c0b54042100407528916812447d4003a6480b024440d40c0720303a00d0300104200d4000240481e10b03010580d24050740000304000110211850440d00260400c0c855880b101c407840d0a41c07000350340f1130a85034800301d0303580700103200c034044d1820202d0418454010701d400d030f006046a1030440c0ca041030646036100070036113820ba200c09201c41031050032440282800c00c0c01507000166074080030032981a4000d0141d40d0003044290130041e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 723061582 1250 723060332 723060353
    0x17120f28060b120105090a150e060f13060810063204140402130903142107080414120f07050a080c062401050d020307020717070812071707 61
    0x2002d00342c0782c0c4075154244002400d41081c041c8070f00c0b0b11008400110b40b14894025510441540c0c2c0c000c08c0f03502d10340396100e112246c014040c294881c139262100d0340c0c503841e00a9409203440c00e02c00d001c80d003c0c0c40d2850403420300c1c0c0c40803a07218040b800e07c0ca052004055581c0c0200c454046138580e019503007103100081070a020901007859100f0309241d8004076a02650048901840c02102d40d000e05007203188a4004541e006000100824a841a45c14000d40040058600710b4110300e00c04a0020421203001e036541011a0700e50042051001031100340440584407000030b520020003410f00c550a101c10048078000c48011084020000521404002041c0494620294002096502c4007c5811104c0c7c486208841d100f03001485c03410100e2039144910f452001d0b2110686441c0d24104e06140e0341006580003c000c001548250003002075040741c0c1130508140000c4400180800505000070b0724103080c030080392103021503070511040001c03440040e60802c02c10060180c0a580c1c400707a24120180c3c0703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 723062832 1250 723061582 723061589
    0x10608090f010c03020a080a090c060f020307020d0c080f06090304090c03021903050417070c0b0d02071b0510030213050d140105040f0605060303071101050901030917120f2806 77
    0x80d400c00c00382c22440d0760560090420710f44540c07241f0545555800c8200201d0b80000c401038400e90084c981049500c2c01003400306003030041d520599281024640201d401d01c0c0c1d51030310842d42079010100c104092041400701405a02000018210900f022006e0564900990084c542e2990343c610111030114000d9048a0030301360260f10b91500c1c204001400360050030100c405503145000d104402181100e4281101c107000d82c032040100141c0d04007507505143d5049080c00301c036050350820003800890950030200042a44a4420650081c03d01040c07003a040c0340001c601c1c0905005000001c10512a8802d0000f03413541502c00c0140d01e80d66040c20030000441100342c0d174240d440c0006100901c48000d404c20006c5010710804d010586038071080c141d0328452880003612903182c4d070030040b241e98407450041800540524020801c0340454894202c075100420808111441c0040c003914254100e0b2016a030141c503480d5000c00d1885d045401c03140210411142c10031004600707002c490300340c84a50064002c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 723064082 1250 723062832 723062863
    0x51215060f0a18051b0a0e0d0510092009010308030c04271505030d18091419060b120a1103130c0510140d0609020c07090501150801060809 61
    0x281d994000d020065002203208032060f0b81010700050303090142e100c1000d42140b00070f803c9440c102596500311641c040c0f291100f9488080900d515010403010021007181c0c1100e8071000984402d5860266121200c00c0c0380c5010701408102940f8050b581c50140504498010703d2050f030b00c0c0c0e500114641680300e144c01c21840f0306a5481c484002241d10a1103030240d080b40f00041184c030b49101446800f510b054841c140e4144e0080c10200040c03441149605d440d0366480d40c421401c00c0e241d244608c1070350701070070280c0d601e14014020020314640881582282c10605407040082a0400c05000306c3c5110f200d207020000842040071902c50b0441c1c0d070007056200300c0c10000703d4480c20203c00055108007281006c5d1510f181e070350000314003890301c07540711218030903140c47c0c1b079011484402185446401038036000502c2940c81d0780c006030301c02c902d000604001e507680010f41440c6050915240458a0680011194001708000a000b0700d401c0102035054421504010b205582e81001da5450441c004902c2d805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 723065332 1250 723064082 723064099
    0x30a0f0215070f0c1d060409020d0c1202010e040c020304030314040806010b030609091c110a0b070302031008010b1e1f02160603111803150405031201051215060f 71
    0x18043d8656019581a104200308a45155034800e00302060314004262018000100c02044281c80d01e07601000c1014030140502c0001d44180e214000390410307a510103170081c40659510b030308560348185504c07250901142c08104030001000000e640340502c0c000142030054502c0d030507585061440540f8020070b01042103680035030711440b061356250001c0c0c68290048440c2004a100e181d0045445c008690703195000e10b0f9240401801260001c94a820602c01030117485080004204c1401e0079622070384c510349016a581c2031440d4812600c62581c0d001c201164504203010446646440c0034480b920100070408905008000c005207400c0700b91058950b24150454468044980105100d00f1030908848443c1c0801c0c0e8400c8160196000400c0f08600500200901901d6a40d081010b2605103000b40c00c035000072981d4450040c80020645d003d481c1d40d0310204801038001c0120119601606083e52050300c4450829440e503500ca201464000d590070859000800a44401d9016150100010400030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 723066582 1250 723065332 723065347
    0x80d06060314040f030f03020c0303160e0114070f020a0b0d090201031d061605040b130305010b04022107030f18050601050114040902090f060703050306031506030a0f0215 75
    0x1008215900c40e0102180c14008545014121075a20718400c542003040e83d19169410340c1d04544c296070903176056041c9070307007880008015081000910f1191500059000310f40501400c0134200c5101c100109040201c590f2088084450460680307440c02e9014680200802131440000c0c40c00a46400012030200045a2030301004141d0704402c8213103000780c0f01000302c0c61070384a1601030720781d4500441242d030340400d02242014441c044022052900b0303141440c24541c80750428203103035002801450301c00340710320001d02c1480b200380b0440442080232201189044820503070210100f007142c0c6e000450400031000107080034040d4002e543c02c0121000100706e101444490f1003100b50312504152403c1c854640042119409042d206001d036540201c11403c0618280308076010354041460140c0007a500030108006032030708009060b80b54860344483d9101e203809414503127401c907021b40d5000240030310824001c40341c40114405010355000140114055564000703d0607249064001c010b100c1c3e400505607 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 723067832 1250 723066582 723066607
    0x10b0a050a17130c0e07210204030506010602030a030e01060510050c0c0303031e06090c250c060819050712090305040515030117030a171810020a0e010c1709010c08 72
    0xca4500c10b44c4101074982e1200040000000c0494594000c00c14640c80c1d000704100ca08a902603008a0306000341c0303002e03226920300d402e1030000e0380a074002d03900200d605806a50540140024400008000c01c1aa13103803070000307214084181601d109204d40080c0e060f030407e005201c0c0f80c1803040040d0880795070b0b0a208403010a4826000c3c046c41a060418004c207a00b40b03000302c8482d018035100c0000c5410400c540004c10742600740030304c038141d8503e58030607070500184129102c403009203c2ca80340d444d0a8a003001c0c6110102e940111204145c40c540340c2005034183d0000e22000350956690000100e0440501d41039486101d140c02099004051b903c0e0a420310740398600841c181e039404210201081080248150b0381c1c0152912440420b085108460404030750001e580d81c807078038000e01c0780c4184d2603415000341009018000800300d40e4000030905581900718181200d50300081c40d141c244d0341d00ca0b445041c2c8440e0020031100114800142030800c981c40340c4100e64540b0f402c480709690707820202101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 723069082 1250 723067832 723067861
    0x31201060f0f0206010e0708130512070c1202090103080307030e010e030d14220c0e0f070e1206180a02130605041a100f030f02120f0f010b0a050a17 65
    0x1c040000c0501180c150b5540c40440e109040751000c508118070354680c0e640c01c1d5190380004110103907207030030840184042501008095000382d0440c0c03070196201038904041e4030030155604042c024481d07030203060f001070f01c070303035000f00d044071b0b00b1100d0a9201d8441d81400c070050440d107400d4504640c00c00d0843c82080c0d101100034890b03071010380c10801125081104103d13003001d0032550000e041d851000100e68400340048003c10303040c032600b030800749941c42e45440d60b042c0d0020b46401c040c251410702008001e43d00402c0c42e01100d28202c95111640c5a462640e9550715001400b41d60a00e100030450942c008040044034540350340240112660f03280c0c422801b0041146200d2103100f10f00b07084071074101400701c1d20f00c8a0a454080d040001d0b0003070741c117400e42d841007140b039207102010307610701420040340d2a0f80701501500384020505402c508207150341142c2d510000c0e10620303444880e00d004011001a00003140c040d2011410102d8803507030101419190070a04a101100b00c80c03120040000080b03900030f8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 723070332 1250 723069082 723069107
    0x2040e07170705100e0907050a050904050a020c01060801111605150f04030305010501050403210c0c180b040c081609150801180e0c060d0b03010207060e0607020604111203120106 78
    0x941502d9918013080c1207402d080d5410320075800009400100c1c0a0910401c020900d507105403c1c01450060b0540105040b10821145072107841d6000c2480d07060a54203014010040400c24001c0c86041c5070586001698420980e02c0070b0420f806000d01020007000b40442d86c880e01116500c3d40c4181b4040e1b40f80b1081440407101100024030b070200226240d80100d0590342601d0308400e0052245644400d40341d40c0c03032905012001400b520440c503a002a0440d049440688407003240000410289000075090301c00c1c0c4000c007403140d4180344200386000d52080d80c80d51b0143c8200e03443c08490300c5001090b11b407540d0581003980d14072403140c2015040f9401060b20350480700780c260804001085001c108007107401d03050401c1d407150804403418140d41741c071001404141c100498005041080100000e08a0340701e458200c0300147c4800b4040400072040c04850b42c06001c90000e00894503180e40c58008103c4409040da10590078000c3c601814030040050310414101040500510758490350041c0070600c02d2035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 723071582 1250 723070332 723070339
    0x415150c02130501061b1a0a02090411091e1309030512160c321510081c0c02130911030a05123001091407020a02040e07170705 56
    0x5501c00b950070561249504844059542480702110200d01c007000c0081003800b0b13103e800030300300c1410003110035903540c074000c200500b00140d40380091420b10041d6105038400d14980e01081c02441d14075250206044000b2000400700300240311440700003202038408030640d00343c1518011090b010540c002c0002c0c44c4030108803014105956031082c1e41b040f5402c464841c54000b4040301c1d140e40016040d0884988a00c06009541c0b103c2c2500d041c80805c81c60100110f4036281e40098014440c1c0d10030000496007207080000311000d60f50528003041e5440385005d8014520074662104442c140b846244981419a0300070507000811061601c2a00a4204400c1c02d47e81034090645d02c045d240340020381c01d01600d52001c090550030384555070410b145e4100b460318112400b542681001c0f00c5050000f9001c00b00b8190360100e0180d4100802c810840b20015148442e00b60188148090a500081ca441c0455030444010804600c003205003801c14007642d111168141041c88240082c3c2c601146071b40030f594003134 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 723072832 1250 723071582 723071599
    0x305030a0612202106011401090819020f040906050402091f0302010c110d08340b1017011409010b0d080f1c0e16080c0415150c02 57
    0x1d500c03000742d81548140003004143c04005184081c0340f18407601d0b038600c03030041449900c2d28060b9a40391901070503444001e0640c01010040c01811080c8010b200024403c3c644001114104121607541c1da07559801d80030030403030814849045503540e0002503802700018205000504880c0341c600c01504c02521f04030300c41c0d814400040e200400d0b0a003044042c5030170040b100107241c0b440c3c0041d80e10381c0340d180e4280c030721001180d19460305450700140c44a080e880341d00d0071961155584000d00d4903620815075000c0001d4030303140000f40760082d141c900d402c1a4000c0100d18458861991804246503036920094201321030110180c008041940031802c0c1041000300c030040ca90310410a14221604200c0b000e130310034061064000820705240243c00c14886c2d13a44501d2800c9044040c400703004147e004d88075200c2d5140d425181c40d100090040c45000b1041d420205075160414410940320384a030300985000c1c0707544030407522008004030590300040101c071004010b042e40d038003c0106540e0102d40c003a8041c41d01e2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 723074082 1250 723072832 723072839
    0x2121e040b2808060f01120509030712050c030301060f020309041103100b07020901090507140d0b100201140c030604060f14120d02061b07050d120f0e030403230601030305030a06 78
    0x10b40e07402800d400400e03900c8400940c2c0d4101003020780000300e070b07800e41040340ca1541078400c0805072103018041c0c00c60600644c1c84801c0c602d0020703036080606c0d84900410070244041e01d08801d001003038905446560a00d000341c106542e60072841c0d4000c1c540050360040c03d18100d41c1c10681900010740c0205d40580b0141100350300d5030f00a00c014425010000d40000b814001004400b43d01d50009400c0303041842d04071500b851040a5400d03a4100b001409141580da0051482519000d9400c08111005000030310401101584030401c480000348a50b07a511000800212943d513a070340315402a2449512409665440d40603241105420926850040c3c0f100d841c008078071304002801c04440010755000700015910285900c0c58120344240010b46110148070a000144050041d00900c120035603d065030000015524825142000c00009203a803504014840e000008811101542d0308600c02d240d03601c020081c0b5001c00c03224608100f806000d140300100c105175001d001103000b841c24090a000640e103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 723075332 1250 723074082 723074137
    0x405120a140904060e0405060105030d0806010206040b0603030c01090303020c060c130303031a06030f07081006171801052d01053f0c040e010c02121e040b 68
    0x840c0c60303440100300741250344680c01d10035030000c2c107a4800103080400c1c401c1da201e09040e6005021b980c11030b0150010b900511460a042101511021407494602603e05050b00042d445510141002c0c2070003922000142c0c03261010000c0302e1101c2d041400821000d800340c10010000d410000e0601c00c180a5200800e001c070444200756510b104044407140181072139585c05500501083c0c2c00c83c00391200740499400141c0c2c0d404091440341c00c814200e500c143c50245001070403e44001d0084001c0d01c546001130100c0b980c003809031101d1140c0403030469003036114142820b945031810800c03480150f0030541088030350003104044a4140f0420940a41e45c0445c0304040d001c809024000d4680125144803480341083c1041e001c0c2400282404d6802e4140c40040e1000b902c9200c040d0089005034091070002598dc04c152080c02452209040200000b11202e0300003074803003003143da000b00702c14008650700101d184003110312905e8072160040c8a03620b5640b508064503580062402c4a411410580203820414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 723076582 1250 723075332 723075337
    0x21f120506240c070f0e09010b0a0305071401030b06040f03440c0109110126010b090a1203020601030605010e070e0103020c03070204060e041101050c1005060d0f0308040512 76
    0x182c0390007440350840c001400c1005900586072480c65031141d004001611100c0c680c60038060108680c1c90308891410070f6a5500392403949003030741d0182650f007104102069004c1000b02c242d501c1c803c1107040d0b1703862402c0104c1c054240c4024059108100103000261100580004030849208092518402c0844030036907001c4000c0c80d00b81c2c40d02030246a505005184401000442540d031740310001c1c100045518801e0841e0744690707007260300300740450b002d4615680005522011000e2074280325500000c40c954100041010b220300105000c01050014030750751910210760191001c1c14407003081110070308000390f61724020300c800d481e054900320000c0b440c4410301c1549485001a51523011800400d1703070045000350f0103000c000900c0d020901c0031030016138940c01101c0040680c0400b0030842c0c1410305090003400480c42c40103041c442c08000313448000383d0104204d403060360a400005200d40d5680b002ca44801113503c0700030303d00d09800002008050300032000501441c003402c111441c04512480300311061 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 723077832 1250 723076582 723076609
    0x41107080c0d03110a0f0309140615032808130b07060204061407030c0f060e01060b180103061d04020621330402030c1b0d030b0102150103060504021f120506 69
    0x14600900c904c6c0260300079000101e055110729040c00c5c500d6035520303695003401c3d010365030040844400200b01142d46400c1082c5160429a50420350f08044c1cbc03403945802100b80414010026400410021036441e1085000001801c2104400740d5451031490601d00070b50080c083c0c103001c14400503448425006010541e8000e5030b054a48078050142516a000d00f20804042140e82c280c55514850008a080c010480104007a020194440d0803c000703c0f83c5030f1f89040781c141d0406207000b40070009a40790000304180f0412020045413151194000304489100d40d00d07009113003d54483c0d412050178941886103201d00b040d41c040743d0314100500e246a4031821541c08041c1040e44804880c0c1451420f64011a04420182ca945142940c00d202905401d4014110075030795070412151149607581502510101a0092000d010712526603422002c1d00309060101400c61a51000020304540300d68008140808070501400700d00c2807851802015040c075030000c501d95a04040100c0d0b000c3c00c01ca011000349 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 723079082 1250 723077832 723077837
    0x10c111005040c0b0903100629070507210b07050711030a080a0e010e0409030c1506060818010f0f0501080f0309060901180b03010806270705041107080c0d03110a 71
    0xc0b03844c0080007100b503003103074a81c03d625019030b4240b901d0030305c4240b08400003001c21050004c009035104500a00801500f41264041c060030840440000e402040000a03201006106c17010700d00c0d4809800120104500c00030507c01812062049c0c0725000f00107828401c0c814050303603600b040030400b1b154641107000001410344038148103002c8407600800d000c03440c0700c006151010b40f90000720001400c0d600b10000a4010401480d1000103202644042e110100451001404901d203098801041801d008151500f6a03103100040d04090700c082d00029404000013101f400440c5a200c0120000c007428410a09107104101207180800004000d6400101000b015941048203020040d9400c0e00f42c480f40e2002601d428501143e82c0e50303030602450192005000a09262525200d0075016090f03080c14405201d101051303442031034400040031000c1e603000b81c0e000b0441d00e801702880780140c050190300602001d0086000440b41000080c0608641c50558091004034803400e030046031440f489581c3c400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 723080332 1250 723079082 723079103
    0x41104050921093d0c05072309090c10030f0507031b020a0c0e10080304060c1a060d0311010b06180a1418040221010207020102010506120307170705010c11100504 71
    0x151592105001903804070a03040c4400d171080319656081c20480f0f590030040c24401c0606044400c503010700c042c480c503c0d20688800c00d00c0c1c1072010f07200e42d480722641500da12890303852040b201c100d80700e0b4002d0000046c62101c14403480c00d2044010b00a401101c0c02e840c0250300300035458041920005034842c00b00c1e00040c006400d181445142c4d1a8010300031f110800d007050762100002d01a00400042c40100000d50304d003002000030b80f403c020f2001c088142095921481418802580d4030040c14402540e410b0420034000b0740003250140c050200060b03481e610100c04502803a80410300c1d1005414820101c1c0c0c0c030b4a00fa9110980004c460102001060b00310413a015201c1038514030380161703074100d40000e154400c2c1100034905940d200c1c0151007401096500403a021045507024000c054020604072039011074075107241d4aa560b68040d11002400c0e444841d8200c042c2081400c4c21100340c141c10800900110391081310190041845061080303041c0b2480c0c04040c2c0754407091240600565100c4681e24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 723081582 1250 723080332 723080419
    0x50c0a0f05040b0409080403050a031209030509090a06080706050702242a0313170601150c1406090102071203061d07020309120706020d020604110405092109 69
    0x70000c0001e03042d001340e134890401010811007000b03040207501c144010300141e000392500030115000454100127107801d2508200010382c2200035075119107030680e81102955038180310341000c5c110540c0104c989001d40480460600c3e80301c40242080343c026950414080754004079100e0464400200b07840043d02402030006442070241d2200c414000c510001035a620f0f0500518159032220541d15100210726004008043e10000b84041c031050040140c54150b240c040c84c00c200819801c00d1104102045c20500204480c44042041c0c6500907000c41e0050303d00a02c40e079000350311021099622070086000b01424611900402069655213540403001c08014484010005c03005003070501035002c244450f0606031070724601e2650f0b401090000340001454404081c0c181210704109400319042035082001040310010810350b28803040c0c0b400180795551074512401c041a00400030f01d04080800b00e405d10784032441c09007840b2401281c03142d03c400030354101c2038294119411424040c86403041030381d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 723082832 1250 723081582 723081589
    0x10080f01030b0c0712030519050613020f040e0405030a020f1c032703020a030f140f0f070f051005070503011d0a0b19080111040e2e0909050c0a0f05 65
    0x482d00300441c000f80c02e080c10000d941300c20f42c808002c000c5a0010390b5400410428940c2c00b040c80d040101c82040070051401c03c140840c0081446043c9621403680002e0b00c1983d0f0210201140c0052217080021240b908041c541b0329141d40c0302000c060014070890f4000941d854021072010150083d141e1407401c540520b40d010f50203000411800101001840d101840943c0d00300b45100d03482c0d00c65400360056942c280b070f028003400e143d8141d5004000032340016010b0000e83c803040394000340c8070305000340d2a620004411030580c483d19500500f03400ba01a4800200403001501440091614405101a68909200b22885d000074411705a203521141d81c00490908108a2103422842189000c1658194003021448030001c911007041800340b00d00c030411020b002807242d0b00484511080c0645854a03081c2802c0310350101406580c003170511400c62000040e01c3c4850750520500c655900c41a06540300109030040013011000d07120350107200070382450352601c00096029684c6450313208100c1402c11050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 723084082 1250 723082832 723082853
    0x9030306171204181b020a060e07060c06020c0c0a061e08060d020d020a0506160c080d0c02092e060e01081014030a0b16140901090902070f020d0b0610080f0103 70
    0xc2c6008076984170303585e00c140300e0203a000a0704140c81d074004110703030341c024907100b0100c0d045c0323000142e2146c2241c04144103040e4803a007640c804c41d400c44005a00e0303070b45800d145030a00c2500c6412941c4080040e200040054022501d0030b041140030b0144070400000300e1095408000441c1c0003503000b03002c1c1500c03100619105644a24850001d8104401c664694000c54079a86c0081003a454a010440c0d174002008401c0c40070501030320603400a090042255040030300081d800030f0000340303e0142000050305c903088000d103001840240e42c0110030b00096414a214500401d8041d450000301105030110865000d82542c50180c24260345507100a0314104c5010704910515850940c54001e0602d05800308481c0c50751a40580e41550f0035000141081c070000d04440300405512200220603c41101242c2e00b0a20000440e64040405a03a030800752a041009864110000b036010030030790315403407d001d0700604036440354000781c90b11004c500400c401511031840490303100504444c1040180005002d01c1007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 723085332 1250 723084082 723084119
    0xc0302060f13050a050c030f15013c0612050411060c0304030803040b0612060f0403030203151c0204050a0902091303140a080f010e010b0a0c1509030306171204 70
    0x540c40b400105640d6043c18244c021100fa00d1640c08111114554070b421312104450550000050821400d01100d6102d003003014804c01c45008042140c0402c0300340004510340808841c4204070801c41011006c0e000d03d100c45000f80c500203a899401c1c48440384003846014003980e002807103044041083d80070416941d00210408040f03000070300000002a1210300954011031103a000f801c86840c00d6014040c03600d003130b4010180260302c0396090110364031645862540060b0549005a41c0350780f101e002034601c1da0040e200a40100021a4540e44c0501008041c08400d2080360184016107443e50341c4c230f081e01d5010001a41c44000c4201084021110700d14150320305101e070400c050003d03d9001d61040a0f0400300303081c8003003844081007040501818280d0382c0034040142a010565040c16164200d0b80a0440079806001411140800b40640d8003c0801080520501404600712510740100a00214071440324030100800400e60804004901c3c650150280403d040c1054a440c1524922404450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 723086582 1250 723085332 723085351
    0x4030309152c0a0b0c1203010b0a0c0516060c032d0e0406051206100b070803070e0a0803030108010b030601080106032d170702030c0d030f050f04260d0c0302060f 71
    0x1d440b0301281c0301c0440c524000d02e0b2402500b0307260f148583c400d0303040414048044d501079400700b0060209410704e209460080503d0710780f01c441c02a162519902c0c00104801e80d00a903407006c600041d11641c40501c1000d024407070365503001a0482181d121030a820180240000141b0106031803000b0742c80303440a92100b03c0028808692a940d44021441080d2103404c00807041c0c00240410095540341c0072240010182107004510f002d80e56111004a4003001c1c041908111841220024030f944190003807014100000650780d0300c1d40d44050300d43c0203042c22002940240114000010228418420002101c2e00710107800d00714209106c0001c16400b0900d02d000e00041c40c0c00b00400400e443c0b0002c03811600440342c00d02e64480c03160042500e81a120002a03100703101c3c94200c01e0010750b20004107072150260381496071b2940003d03414014076000e513800403001c0706580b9112000b00421519981c00c2d140c510400d0b40c2e0072601860040314038400c111005400359011401040e21036007102180c9500c001d288 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 723087832 1250 723086582 723086657
    0x1b010612030201390e041104150503010b03040b0705090907120b030625090305101401090504052e0203100501110d0e06030402060405180f011d0112050c03070b0403030915 75
    0x2980000c0c100c50940c7c0d01d842c45104041014400c40b051001c03c440c1c08282406c1150440d890b000c040c4005d0710000b880180740d240c0c042e000c1a4086c0c0140e064910003003004111a1041ca00f03210014194001ca104032611941000d000385010300b400310342d032800303030700707030b038110203c032035074035503003008401d00380c01a05081200301040080030503c180506403001c40301500c04a420400c104661114803410b07005a00c07118500001d0000203480000e442c1414105003403810450f80000360b10106556404074001400750001040101c0d164003c041402529400d0300c0c3c4041e540843e062050380c40caa045804004100300781503203519460f00a001e113030321600c01480701c2d03c0d242c2c0314008240d4039083c182c4008507003144c48e0244660b85d40c00d1760700c070303809441414000d0203c4c4104408201e4280e0f410303c1202c02039107681c0804414480144600003d03c08060100c818050343d900340100c01d41d00c513205c03e6000609420b40400c0313143c140364000d180d205040ea00e541f00701007030b20103403844200c03074840b4200c801c1c00b807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 723089082 1250 723087832 723087857
    0x504061e0e100512100506091e060409090204050112020603010905130606090c111b0d060213120311030a0e1c0b0108030403110a0303090303051b01061203020139 71
    0x8001e5502c507180425901c254031416002150b840d00c41e0090150041000054400e00542c0c940e036007520000101180c2c6c000d81800810070020640401c510150382120001a01041c7c0c41e100e50007038a141407003610304018aaa803582d0703c0d02800500d100c020b50000302000100720041594001c180c00c50134042c1610000701c12030343e8030011500140d200f840315644a0103034880f165042020482d030300b140075010300b05030140c1a44500788048162039551142408500403001c1c0121541603c1c5589132014402044a4540b040c1c1d02c601f80315020214001801006d80ca8000b05001c02030381c0380c06030241c072200f540c2c50b0a032041028030680201ca600000822090000100c0c003200400c40c000c1400030003640c1d486003541055080c1d00d840c1c08007075018410784042000001d60010030f103030071240c25150480d03c4118a40f8090301801041040c00c0f110342c01e00d080800d00080c90a1810174040c0310f03030001c20407070000c0b0541188002048102801050401d40d0100c48420100304140340d11246184ca840794241c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 723090332 1250 723089082 723089089
    0x80a2111100903030b0d081903090606090b030d03060f050d05240610031b0315031505101509180e06130b0106020708030414150a110d0504061e0e 64
    0x29096400d001c1d072900701c0321007031540611601450003020703210f1074852a01078803881120302c070300fa46008141d01100c0f8107480b1284290f2180049541c001d00901c019079031a02d001004d0a9990200340c40780c018070482d5154940a03200b83c0303088640190300e1800c805d20b41010401d0f01c0d003141000b81c845004011411400105d03403248420100107580c0048181d040c16400e000c019005142c44200745450720986940315448070b2402c2096140170b18022801c48910740c00100c450030254001065802c141c4200545030003560403951280c0c000d210010419542c5050000000503984844c1001c0b841c9600c00380b0080051007603034400d01000040204a88022510032407400400301d403080f98000c40072070312508001c100808140100103d100030f1203000c0c1802d58681d104c3c0720320301c9103002c6510080300b41d19281e1208049000c0d004203140c1401d0325611810b2004d0881040031410071014001c410314060098010300580b82070f0380340c5a456854600d03070101f500c0081164047e00c1402d11041400d580700320798 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 723091582 1250 723090332 723090343
    0xd02070b1003060b01030209090a05070912030203030a050c1207030903110703080d0c2a020120010506010906110703020103090203100203041505060d33020a050a09080a2111 76
    0x301214120201e0364558105103048840d410005810075004219820603030380c0c0d040c0706940203012148006880e490780201580c6100b0644c0c000790318071080150f0b40c000d0640110141d4030903500b80308140b2295541000310341d0944200024060302c44140004074520324131aa0003454918882d0420000100030019540c1c0380100c60b5204071040180054031516000d0036000f00300402000f400d00c0d24000910400c040001c42001081c4010545c0a084a006580c820f08101815206642c0400c1c050b11250507454040c00b011111a4081940301e040007403258483e046641000700070b90054503c640c210360044000d08255002270382e2622030740e081c00b2040c495a10085006903c2100740c21001000f402c0c61400380d1b903004218a10030200203001101182c030056858080c09060401082071100c0038609500c1c600319070312018100c3d880450041c070210340100c0200350884203500d400c421540d6a202c0d5507941c041c2c0c85401807800603640f8003031502c03c03410310300c410401e10607041c5030f42c080c21040c0000e0700c1c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 723092832 1250 723091582 723091591
    0x1008160807050f0a0612020702100e1002120a050901020717062203020c0906120714152805121005090c031e18030705010f060e1003080d02070b 63
    0x108141a0400c80c298080203100c0060400f0350f1007040e11032020b8002410611640710312010700900440510707640340b07213604951145600821070380c02010f054100400c0303c03059484c0c1c175000d80000e001e00c400031400095100010445500c806c1c0c0381030241756040381d43e9001110824154840c020780410201d00500246189058007402804207280512208400f1041c0c50071801d124440c1d00b001801003a40402c0429406030195103e900075150b0341301040a10f10244480304050203180c40205000a00c045200c03140002200d203030354281105541d4030300034480c02c3d02c40900c0071100d18a20740d2281000c11070504800035414900d08000042c10200704044088404140e0a000d03860180030340d1912100460300108144816419460061603080e0b8511589aa489036840d0003400580f50010f07100400c0b11a01545041c0d9882d19621f240c043e02070803050a4008149040c000003290142000d03500d03511070b0304241c1e4880e6149165456908495000b0952103030742513001c21250b400318a2101c5840d008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 723094082 1250 723092832 723092863
    0x7200a050901240f080103080a2703030815011d121b0a06030606050702040b03030405031905060906060306010303031116050f0c060f090909010f052706010e0705031008 74
    0x151007504000b800400114640c4400b40f06003004e00710401a4404050350559a002c03072030a980c0e001c009004e803100c1d400d41407a03036001481001100000b00303c826011044900c030b80c40f206015200e00170f01c0c0503c440c1d48440c0500285051001c0c0002e0246049454003801c00a083c05180c0c00e10104441c2c10128001004040c0d0301c41c0003000f40d031506218080d40000c0c001440c0810203507042583c024480c2c402c40354040e1146840c1d141482d01982c06104403001418001c044514001d0308600d00b05545000210a0b10240101e0700010440d890105400e03104501c000c0140c030b22a800e42c1d505600911201d284110030b088240700032050304140070301e000003103801400240381d14442c2e0b03030900e0329100d101e000f01e038028803007800000d07403980141d0151061000100e030000000d50380e0065a40c01018180f001030000c6007480140a4580400d404060351068007651035078030130261008040c1da920080c828022034642c4000003e81c16071145000e5500100ba4150301000182d07154041850b0401d84203603c0304 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 723095332 1250 723094082 723094109
    0x40b27031501140406033809161d01050918160e1509070509030102090d0c0e0c0a0203030c28030f0e0a0f020103020903070f090504020a060507200a050901 68
    0x643c1001403030744410400481c0c06005050942da600004006102e40d00420300740c0103121601444151180890005002d10111080d80703006081580d4800202802d96032881c01c8500101e001021031658582d64003031800002400c2e40b803c000e2201c032200050050070380c03080b0113600c089a18824001109501c100b006420413450814038000c20181018000744406c0b8041c0100704081d454074036890b6030010700c03820095120062003004c030340139105030342d01564040d440c0c8026008000c1400949026034900d0011082d030350762036292103800303032248074901c9000d603105000040e4080240002840240152000909190404d100c2c0540c40c0e00d02061540100703844654041c0302c2507462040c400400b5907840207180204030344d115060710f10a025000303410160000780c00e10440d102007001c003005201c0003030741c03000460391508076000501c0140c404900c103080c441000280184904180c1d100180c011500120f58001140002c00c4510700d00c080c2c0d43c2200b4100c4002850340e46885019000f040305070b5841e227 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 723096582 1250 723095332 723095339
    0x60906070b07082409040210031508030304110a121704030b04050606120a21090b1b0c18130c051302030124080a0507051603110106060302040b27031501 67
    0x50031813002c100c0c1003142c40c1c401c0000a1590382c44103000c81e00f041d015039072a29018011032046003d0201c0000b08460741e800c043c000528160000b0007075100301d01601c840c110b5041d40340308125025643d4840e168110340c5c000c840c1400700321003480a00e0b45803480d2001c1c03440c0c2a0340b80c0e10f000c2d01e103908942c242d50742e0b00200f0400034182858030b60840900c8920025007083c1c0f401f540d81d9003546070300d0082d040f49114088506452b050040290300c000e0304031008426295040d44641030891029800704060a0045110780e070301c0750800f0713080e006041c00f5803500c00c0215551411920b003a503c4400e4261240100c000c0d001a80e5111082032560004d0707059001b40e5651305000310012a5042651403410110b68440301e1602c1c5a4814401c5411003080c94003c116034a44000468050140100100310074a03103078421820103401403103484004100c140280042eaa907641c0c181d08034080d500c9000740d40c204c2000345074074503c07500c055544801184882c6189c55805140824a031031b60a030071140a6145400050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 723097832 1250 723096582 723096601
    0xf03023603010209010212071401050f040c0b091e0d0b1f0503030304032f10020c0606120304141305130317060625021003200c03030402060906070b0708 67
    0x100400c0c0d001c1e4025850b0200704c0700003e545580b000f204180e01200452000108078001d05a940e102d90010001d1045090880341c51101543c00d4400300d4005100741c1c800540c20442c1008d44141c81d000500034241102143c641030444440805815444030480d40f60314001800c09141e58010b08000c060540b51441c03001d140c0050240c0d94210500c40d600074420000003950002e410b1050303207112000344480400d04039100541da68109040c0c1c03a9802206445018450240e024007011410300007200c1c1c1d07036103811042c0811480b20440e00038003508200000e01040001c44252007140030060301d2030069550500307008084540035222071640344450b6051800741640b002140014030b228010b0890a810018000341c064400c3c22090000001c010203031104110030b10b69850000d0f034001d46100801d03282081300400074002400e4807c0c0c2e900c1801030b150201044d030002c0d6500081d03490021403460300e85400308209a0000090258403010030080180043d07503500035a030048101c1d403651030090800d81c3c0c03130303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 723099082 1250 723097832 723097927
    0x3020d1401051009030215070c090f0221040b0402061b03041d0106171f03061503050105010807030b04080c030405060706061d090a06051b0c0a020a09090804060f0302 73
    0x58100000081c4c1400503980c0d80040c401e40f68070003101c01d03a0303c2c0380c1880e00c054043c605074080c008443c0740402900a009450700204059030708e0808007400030004100c0102e4100c1c082d9400b6100070600e400240040c20100010f03e07030b600d032455609007100c400d4440a0700d5603000760060800a00800030b04255840640c01e01809080c090506d115002d0782003441c1c45021600810389041401948454403031b442e40c10034910059034100f6018807102940c0d0f8a1410a03181c940300c2158150700e844d0002490310303004114581526800605c0c0a815200c41e110303204c603500301c2101404240400c020000b00e5075907403402840040e200c2d89022a5061078403400e141100b08013520304d101d2204c4682040844a000301c1ca40f045158040000103240d180c90184d03000c0b0300f40c804215045044005516400d0000008411252600c21a00304101985034690b2030243c0780c1401e0024001407041c030003445070a0052540c030700780000c103140c0142000c0d0014141810025040d0109100403002116403024440b290312 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 723100332 1250 723099082 723099109
    0x3030c0212070806071211041202190501020307020909010b1809010b0a0f030204230108031e09060909042108090c0f01020c040c09050907032310051003020d140105 72
    0x2e4503442c1e1400c0300290f02c0e1440144001c042054811443c0098034a66011003040c1074444c2007a038460352240030a4034001c01c108400d034891031040385d480c0540c0100901080c161030301a4040d50400f85a0342c2840b6032140003900302d0f48c86540b20040d511403074803071103071030503118400c80844005810146a400e00310390031607041c1401130711091410711004040003070100c2200d50544000a50004401c50101200c21070580c114202d4120400083c51580001c050300c42c11a440c00454034108a00310390860b1882044500f0350415010b00c000c021b5407a28000e41ca0384640a0124000100414101a81499052500b1601260700001488014a0100f20550b8000015251801ca4018030070001c0c1da6410150f00c8148200d0b2240c0c40504503902c25070303c0900078000038280c0086800c10200c0a005003e0303403000d422504200d244190507070003550840310b00444d51112915407150a002c10b01c4481c01000c5584c0042c96001c102c0821003809a1003440d1001316901030101041d410070b802c128424100a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 723101582 1250 723100332 723100369
    0x181b0216090b060406051b0d0504080c0303031003020909070801090c1508131205130e040b24040f111201360506030a0209010608060108061503060111100603030c02 72
    0x140e02c50103a01c4400440d000d0343c1d100d04045440d082007052189226205011310126400781c0704400c91074940001c00f42003640c00060a60300280724481c1419038034041111440c1c0481180c0404001600f040502160004190010348000e0ba8172840b4043c01c1d00e00c1d030703981210140d50b030400400c001a1210060940c2c03504614010030030381001009c1c10540c15000001509070b00c41612030300c0702a40a40c04444042140704500b80c2c50590343c11350007100c0700048405589004031030380000c2090190400c0b160340700c0030248103007082076688e0701031100514078643d284c092650765035003c03a80600e00c0400b504800e0894000b0001c0b40d8180505503030301e107c00c0b105504040e92502c1c4019844a003a40210f1214802c0c1d60000519940e0140000e10340343ca060750180d004001c03c00041841a0f11001c13280c0701e50002e07202e80250f510f40105011550484003000c0700041030a1010908540c031030040410070b546400215422803103d850001c003121b9040e03004801141d80710380b0503411824a0504604105102d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 723102832 1250 723101582 723101591
    0x1815060304020315070225150306030825060509100f15031103031905030a0b0105070b0103031805041a09130b04020919020d0b0102100b0a181b021609 66
    0x9501003642c3d003131300d2021182030390581c2001444c00c0c0d100300f080040b220303503480d03d4000e019a800940c84142d241800b412100410fa050f20480042c0240a140201c0c0c1c2e210061a1400c40641003403403c51000314120007512990080361001b14070940142800340c614640540703000c140882e0398508540804c012180030609080e862060f1003d000d44101c11241c211721041c001c12280c0e00003030305511414588139484407100400f039840e90b91107c080c504c41c500000d81041000107510041d612400307030280040403102e01e503005100207032003944005d006050095840501584400016041d42e4502e100c810440c0c101c01d4000b40b0914100d04c0311038100240d44145549042151140c031000c200042c0086d000300c0c1114041602c018024280d07100d80d013840c80c400c42d1101c0084511101078a10200c8407030041c49584010007000d407061290520505005210151051405c040364480040100000d0080c90303480000c1031103000000751112150380301c0da0240c4000c050083d40407036120400d0308000121441c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 723104082 1250 723102832 723102841
    0x601030201051c020d1505011d0a0303030b030a170307091703040b03180102040e011a120a1a1e0108010e1005010507021c03350415060518150603 64
    0x202d0200c0301e0082c0c440911a0140c0d950010b564064407035010030a100c00c0c039007001d00004002d41800b910030f4031426030300c059105000781d092048858050a10710350140c00824200002400381e4042126600090151141000c1c00d0b1a8143c52a88080514100740c0000003005001d0381d00600701006005d0b4480350000000e1445101692402680200c24102e100007021a09032480f00307a0760024200044c00075969075448200c0300c000d0030b44c21700c43c294035035902c0701103064008070107016202c01900b0004520700a03030341d002010b00900a43d4003802080e08141d404031085481d10144102507d0012058207038111a0b50001080d1100c16880454010540800d02010743c9084440a04840782440d01c9a1250102c1c000206840721500e0b8075a800c03104000e14004158020b502401d1001c066824521004d0160f21100104171400314800342100d801000140050f40e041c000c1c1200c0341060070005004c40d00d60010402d1500060b24986500f811242000161783d15620162001c0c201510490700718140b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 723105332 1250 723104082 723104087
    0x8010c05070b090c0919060909050a17192007061e05090a120203060601020c0a1206140c071412120603120d0b040506030105090304030210091e0e07020601030201 71
    0x1c1d88002000501d602d0302090300307000c1c100300c249420a0f00821552450400700c840103c030745046405600300c241050740014401e007440c4910700c866a0880301421004442d0303580e00320550010400180550028804034138143c5030341546103040070b4036850300022400c2e11250000c00c2908005c407000e080d8003042040c004030f0351010841110107031200c0c00313044504c2c0b201e100340e80f14081c1465690b00300c803c0d808002649142d41217030070070351030013074094503141e0f110800126210400c0d42601c641003000d07124104125841480902c04040c0101000966207004d0740c107602c03946800741d4110100c02c00100c1c1002c00e0000361a00501d2101c0740f07e0040041c0c07000d0545401c3e41d8050302c08002030715007070310000440e191828424802a20704e403040d041d07500d10301d03045400b008041c82400c45000e00d00c2d29001860310f0174144203150080d900074000f1400c29245600708092031a111100c1010068003e000003004158086c3c082503260503940340740c9559042244030111594014090710855010a00410140c0d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 723106582 1250 723105332 723105337
    0x2010e120307080a0c06151e081207050c0901080c03061303140918091f0608030f0a021e0703031409010e100302071502070605010e1905041703040303090c08010c05 72
    0xa030f00c40155500c40000140940d003020342c190300601070900700240d01301e4483c8401c1c941816504d440e80320850000c0b030484808108001c5000d0201282d10030300c1501703266030810000c0c151680c070880072156903840c030b00d000c0381211b0001c0e0f101185a5001013140301c46450305002c100e81c400111001122912450b0714002d0261442c9005039051400004800032240c4520004011240340f403281a8158100404103d669182105443c428500c0c120181c1003201018000c1c1012901d14100543c1060700380c0e98140c8050340034401280651190406e214071202103074026850fa1141d030406054201d1a40c100a007103a4001e8091550700b4030b080007051101da0304008254034a0409403170b0281410201c1c41c090b40284680170b0080c061180d20758061001410680041000300d104040a004690780c1e1150b034244102d0036111402c1d0340c40100800c604042c3d0315031149900034040ea00402100004240a16540d4016582540020b8a03082c0c0c0c3e0040c00b043c90446001820312034020000c085000c24014401d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 723107832 1250 723106582 723106597
    0x4030903020d080c011409011a0307090f0b1305070f030605030a1103070801023013030e0409080301030b04020a1406091e06040609170a030806060306010210020d0902010e1203 77
    0xc40580603000b00b80000c10303091310805210f00000b00100202102c0407010403030300f200c42c40190f40c2000d00e00c00030812201d04e49600c404021300108003460916a941014003e440c500f20540c55580303944c030706550b494601e008042034000c5000540d86c1042d110040040301c244d00350710141401c142c0100441c1e24000707640e10303407560003801c1b41100503800c00000c0c2c14005980e11081b1651b00100704540461680d444002c001d0200000e4082448283e0842c1c0d50410f0084440a0000c002d00c0083d40200c0e0140b2205041d10744003e10004228196030b40301c483e03d4000780c0050351120104000c0204608140340e007007010300004c03078200004080020000700300d4403401070050701070f1403858810b071081500004518914800184402e4413240c035040c000b01800301c9441104100704603030209003108003000c034101280c1074069948003541c1e542c800038490258401780040d8114480d07210700c81d00d280c04520113132001e80940c110101ba41c150500004080c0e0480e8244c0b2846260000301029070040c00008a4420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 723109082 1250 723107832 723107839
    0x60301050d050a0b090d320708070206030420041a040903020102040812030702070609050f010c031e03051006020f150618040605012d0303050f040504090b0402040b010203030403090302 81
    0x44401e49400d500384441030000411602c480001d0000307140c00031403c1070410350039940e104510000c800748032880c504480103a00c0c95000703046591189224020040c015240160512850700d01300e540420101e600071503060740d400c03c1c0d49445001d019007200014018460440b01444000072080c2c3c52484000c9044600703202e00d9440c0782c00e104240c000c3d01982c0061103100e069803020000c052100600364011a8131000500800f42c2c0407400c40c0c020216001038400c05410b8051401c000310064480d00c912400503001d11003c0e5500135540300d0ba40340b105201007403680d80400d440c20400400303a004540c1d80c00480564004540c8d0388110040001c00c1c8410720b400808000031a02c030f000204002031411201020441c1c0500100014000b0b290402ca048481d04403010341d21080400c0c210000c184002190511241c0048040010030b215601809000008140c01403a0650f03400008040366416007048800c030300343c241040190328203441b508141110a0015620707601c0d25a400404800c020f0000070720 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 723110332 1250 723109082 723109099
    0x207050d0e0f0406120201020c0d110f0d050d03061e0b0d0f06080a05030a0e010c0503030a0c0e0307080a0b1005150d020405060c0f061b0a03050c0c030f0c150606030105 74
    0xd5590b40e8080821011001e0f004100c955184d118846102418481c2a4054840c0c6403a69205050076450303402c8a40d0441c00202c0c01c280d44e04200480f40045060303090740000f138000d080c030100b081032101020700c01c40c68400103015442e2a04010902c0c549070525000d0084140c0d00700408800402182c0081c0340c1d50f0130000e14103621503070450007012070350003040c1031380324014a41080020001c018000101c00e6110300d511101490b00456801007040c400902c160018030105048246680040144200e20b061240c90101480042842d0030100d60142d54030750300481c0380c5024070680e8041540c00090500004035400c2c1403502198419802e04480c04840703100254942410b01643d06840c0944002001199981d518448259640d511850040b926010340d00c0032844502c8070000001060b4041801d080c00d2070308619040c2d00921000300800031142e02080000c6000b0b50600040c038145107000c6505469a0341e01c5082890700002440f00c1091070140707000c0c03007003030f03034850094a0450381c04451942 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 723111582 1250 723110332 723110357
    0x308010e220f0609050729090120060c0a03050c0306090c0c030f07110f120c040c031d03030f0703050106140d0b04050408090f01170703050603030c060702010b12010207050d 76
    0x80d00c0032090b0380581414900b541d920308101c4045401800c44004400340340004c0c1821920b00b14445003c80f4000c01c503401080b040419500524041c110759142e00b0380a070070050020071a50030003104a680b032a5624002601400d69909446529005505058464190301e08500420508a030140c828800c110b008590f031420008204112801d400188402640b03410240c030308001c419070003582d094403429003a01c580343d9605017524400026101c890007000d6601f450802c2c000104001d02030401015100c219035988002004030381c14405da000e1008681c7d0b403400c4c24080c1c0080d41c000d8011810982800e004001c0c4c55808250207070b15141d0201103680da90340c0b50704000001c01403414506e40181c14072080005228a2201509040c0400c0c1c1d00382c1038503840103004548c8040018074020714140c0580216203035901c01d6001942c050000780440346412103031558903181041c02c0f942100140e45607054100d603802c20a200e4890203001c60001d6041010542c0d6958440d8038116030801003040145030748 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 723112832 1250 723111582 723111593
    0x31b04090b010621143607030201030b09040203060a2301170f1c052a0c040f112a160f060c02130e070f0e04060c05070b070c080702040c0305040308010e22 68
    0x8040c50a00052081b51040b01490b0841d03d4111610090780840d1624208105605040c52070920840d40280a01111f5603124840001401a02c9401c07520074207550020040f044d56110300c43c040c0410705060003958003d1118681f4081d100c80d1101e401e0742003510001c03400d489a1900640015050422585544d0601c0c100c003080c900d4400e0103140c08990f1141c900c0803410200b00c54444403000e403010300240003540c0e20701060300c180985100409a040102d0b0308000d8004030900c800705070014114144c0944c20000e903151003100c084403801c2c4400c18204101c10316200582d20014075180c142060040c0717280d0009012028008201c05100d501c03000001d1041100703100490160220364601d000f015140c05030301c08074000403a01143c007540307859000c0d05903600075826030350000c2d4040c50440c0c00d81d0f03c0718403c56010b00c0c2e541c004c03034560701c0c18041540142c0d118001e1103031088150340d00044030f1405043c0240481c106a10003442101941c084c010030b00c051030207003039110640d0b01d002d030b980c000f070b52030031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 723114082 1250 723112832 723112891
    0x30203060d0606060f09090612140a0602030c0d0b0f0105030a0209120d11010f050103170705030d0212070e0d0521070506040819050405031b04090b01062114 69
    0x201110f1400b9004a080c54100ca20131407010701c0c6a403400080364440d508102114030900944030400f820780c0b080340001c0c40c0070440ca5a415500c0c400d9481806480d40c3da0003d0341c1082e28018518070000c078120030078414502c161080203008a8030703958002510b00000e489403002824484800e6000103444019450714080c8004100c2c0030310440d18140089080200009210b1141d81129401c002d0207000307064441c0949810b03650402591110054850480d030b6540d40410000c40e207500003401003220840451000e41000c24110009103e0751a00f15002000c00c0d500030311451103046000310741004214000303030750000c03d50082074002d00040b018111240900032a41d000701548a000c0410081020440213001e10308580040d407000307030103018400e45081c025070041503090f5010340040740701c1d4a240b00b8511030130040904006162341d4192070b181d080301c0b026006080403e441040012042d20704040b41c0703a021454070f01c1081b407080301c400340c0504824040c0254a0300c9040c406541c03014110240b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 723115332 1250 723114082 723114109
    0x2c0108130f03020123010e06191203090e060103180215041208041d1603021806070303090b1503030f0a020f070303030b011e1b0615030b0a06120201020a0303020306 72
    0x3007080c01d01c00c07454024041c0c00d822100c2d001070002d414022102070454441c03907069070485007080015698400902a070030104809400c0070040c60600011000e0b0f00888250059009a488001c1a400c246204c03144120180480707040500e8540300040d0286449154078031581c0c1141d49144000305000700340b0242c012a00045051024127442d5010080b04000400840d0000b00d002044104510f6411000310400c0740c1564503000500d50000ca5244207500a040380440f0340341c04400c00e090500402c0c4150410042140840d03030fa80c450200340880c0c0b080c9150320100e04030300ca407610700704640070035141d0144111043c180d0101040f46200c460091049005541c0d14078121900603980341401005400070b034070b125011a2820391032107804070380c034140e06442c1d240b15103c1401500ca40041540322041111003900d00c26030742d0903d4100d0444a40b140030080d4099500b811250400c940b010741159420f074131281c4260b03030010b1244010f0341c012661100041d00750a0050300d944d581004141d0f10407881c403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 723116582 1250 723115332 723115343
    0xb0a05040609090b07080118150e09011d030c0d051608130906080105100311010e12011a0613030803040c03080d05090f0d140f04080106080303072c010813 68
    0x45011500501543c09024110700440c0c603403001c1d0302c80c060706640841080c040d00b000241004041040d017003c07a08490b2100100000803c6002d60322031203051240400e0715101e065035141c43c40021030b07070400000314020040540c0910316080d44100115510079601f000c81c028000042950b407010000d01d243d001003d9081800030740d48542180ca0614140081d0183c403a41030b00c1c0140104203c5814442c4501c10490003161040d21800d64542c0d2000c1c038011f030040c078100010303c1211800c5880d5041c0e10707208169420004140103100c004e022010311440501a80108028418044000c1001d480141281d4007d00040e60701d0300e83e414003000e420815000034007001d10001c0d003a514084140d000510448464068840a14100201c1074a0b0801da40100000070f050203841c0c220a90030342c006010ad16030440040e0318182c2d841c00c000342520020350100c106a0004020400d00581148003504071300c004405448a0080300c550120008203011102410051440e0004074082428900c80e01845c2e00301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 723117832 1250 723116582 723116591
    0xe0904050102040305100b01210902130506010f140426010e0a0c17150c090307030f0302070b0f04150e030f0706140406020c06030a1d07060305280b0a0504 68
    0x20304100303010b94000d120403a014401d544010060b04801c1c4038028000e18140d4441075070405c0014a800b001002080b98022507556003903010040c0c0e100e40c610a200c00c8030342c1c0b0108492800e5030014124865442c0751500b4452052440a0320400139801ca8080c0d60400062803a001107030706000b100c0e2001f080041940d5881c011084101404c00100030b802d0314440e03480e02035440c1d20b41601e611062a0f4040f01e0800358440070713404002c94220310840e613002c040b1031080790a00384417100082c0b0f0020154003e64030708982c40342403001d1507418803a9101900000c003d9518081c00514060703000c0c411442113120790300c415200c01c9403c61080f14080301c80200101185c517038080610045841d28001d20810000c6100f01e507400d491001d09009440450307080343c001d04a000e800c1c00900407181e01c02050711103070360b90354152420510701c10b0018200284001004201240c00c081c000740c01c8031005032243e03000201c070600191501c480521664041c9003507203804907005604202140c0c4a5480784c104d2640241031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 723119082 1250 723117832 723117841
    0x270c15050726130e01051e0d06290424060e0d080a050a0806270c04121a0606070b1f0f17120c06010308130e0f040302060f070509040c0e09 61
    0x76552804141c1d1510701000c2900d0341c2c0e80b0300300449024800034107103901484101341811031408c5401c0803170b424002da9010851012504140031039260301d2486441c0030416000c8087c071400c080c81090000408035000c240c84110440c0f0180c2443c1d03891052200300040d040c05210f69884850386011150ba0100919807140f5141401420342d4004107585000036541c5000a0454940461102410144004c541180c0c0340320007140c4580d894014110314000c0d404100000d12050319101c1500014042c142142828080c483d1a01d0481c0000d40210710946040c011395011650103205540c03c6400c0c0b0450542c408580500d180d515101a4408010704040100c00290f1940180721810b0f81400ca4081d20403009d070701c41002c8100d008401c0d0a0406911000061000a400324000c0c620382c00390b020312440180c1d48542c4103100050845600000341d624201740420180c041003029041004004040c60034036003c20003c1c514010301e004a403007640c42e00854581c90b1302412504000e001c0181c81451240b90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 723120332 1250 723119082 723119107
    0x3030e13020f270907050a18030c0617010b0403080426010e1c110c150c0303090a11030619020a050c0a1b060f0807030b0103270c15050726 61
    0x30703c10a0904a00d2000c1041c0145107000342556205035481c2e15018288100e40b44101c408555101c440c1c04c8244900381c010001ca1400e43c0b1000061441d5a5000704510034008941c0c20b03181c040e07028000c0794005020078000140d003002034809840f00040340b02151100c2c0e4146001da6a05800c6c4030f2420b51070003000c08140007000c01c0318011604e00c07045c082c42c50780030084c0c1100d2000e1030050134107064221000c610700d0f0f413800611104254101c804e106082a40c040025801d43e4010344440d4119030100d1260410803420b14a1502000c40c12401b50803076280c80c89004079603c4108500c4101d2550000b0340111150180c01922070181000341201d0040382c00f460070000124402c1c0001d0400ea4281c04005000340c0300e03244125949445580d405070301d4540c41c500b40e0103000521945414103440310102c00d11080f2404101081c0c1500000203100802c060400350111040c6130803290001910788030b203400f0190030000b290000c2d548030304502c22042210600c6100c1c143c401c02e00400701700b800904080e1486 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 723121582 1250 723120332 723120367
    0x504050105070206060117010e0c0f0d0501150302040303080f040212070303021e03070f14120d0c0914060403080304060e0a0302030a09060c021008180601060c0302061003030e13020f 80
    0x82c425021030741d20380c90369001916901c0d4007005034011800d01c01e005000c01d4480d541c20039002400800902e040500c9140e000d0501e811519981e5049942c0b00b0042203035070203140c0721100036070082c20118901170564400402240004101d0040c5150010100d411511001001c201608291040d1004c0c0c9840746002511030385004c480190401994403082b510f11400300490340c840354409942c0c0c038000545d907100d88040d0a0811011080d008034031403000403018000050035208414040010054201c0101804020003034000c1c16480109504c0d03643c098903200c00b00ca0aa9400c100c500e0388039560780c44c240c0090b0903400103c1c5214069a50020200b5400201800d02a12a5100e400304139444000c2140d95018054020b5801071110b03094a08960141300e440d0340040010700e003041d008405910441c60000300382e0140001880d0381350044203166051000c250440084000c031100c45203191801000d01c0821039219214441c048851929406540d0407903c00004041e1982e44400e900b400101920 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 723122832 1250 723121582 723121591
    0x90c020a060c090614040521150717090a030228120306180902150a050910090504060602031e0f0c06010308030a0507050c0a0303150509010b2227020d0504050105 71
    0xc5d015104051070ba030102041c1e07000c1d150047c1c50b03130b4588403040b15058a540c0b29100b07400344500070710700390184680c0000001407182c085501c40d10003060504c1015151008000e29900860700807211450000390b01083c1ca009007804052450440010030540343c5141035214401020389211242c0e24000c240c01d5000041100c5450042c0b40c11155510141004e43c5d40341d030002980020070013000011141c941e40604040b0b61503140160a100b4240c02144002035221150004101050010081d034035241c091080640928400740d814105a00c001030300390003d10f044524406030101e0300c004444818819101540d4071603040300e44d2940e4034202038150341e10540d0020234242c09d100028610074020700c00c5411013100d00008001c1f20310191000c4008003c040c4540200030b1649600207042e0740d035400d055029180340c140300c3c3d69580140b030241c60f50b468044254120452220010400504440d80344907140b200640c90b07403050b000000e040402445481210002c8a180030f007408203000c4c0543c0300341d205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 723124082 1250 723122832 723122837
    0x807111905150610020a1b0b070b060f010306081906090c0f08070b160b0c2b1a060a0507030e040c030b030106050f0a03080c0715080a060b07020604090c020a060c0906 73
    0x25900c4000521002c9041900c0134005a88040201400100340c541c1100003044524000e40c4000e0301e910703e150b090390140c0816184e95080d03000740071544c5010b05100070261000d08007044484d20300707002503880b10b09031102c41e4030403801e00641c01c0600c5000d4116245040d4004e50041c89107455807401480c101007805480641d00c290b031004901c20b24107008a9248550048036009424141d80c2c981c41c4c41d081c014080d030f940e40400d0114185c60398180408035214840100c059030800c0f900d03c81c20041300d80200f1603840c2e04103003c1c1402c5e1300e43c465000300c0b034080d541ea02d013455403612207040c10707110101c9180085030010324185940043c5c0d81e04d90320110150500b00c0c024480390703564000300a404040d0901c1582e0000500300100002030f12a001006d1040341da409940d12182d458070044030039a20000d038003002c16204010429849042d206e81c07005460700180085c24220540c0203d447d80c041c5005282003d65504804031009000304442c0c2d643e10b0740040c0c14050680d40d03172002030101d200b61203180007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 723125332 1250 723124082 723124123
    0x1b0c0b070903080d020d061a09011106070905090a32160806120109050a0b06090a14070c0f02100f0e040b06090f0114030a0207031b030807111905 64
    0x880318400c1a40c0011a40c100054a081c40188a0610f00940c02100085040c503a84c0e480060342c3c11111142c00d045035048144203845140c44c00c0058201c9060110f6803905402507802c0050481d0000440e8090303810070f88050000c2e54070241610024030740106280c42070358480f0340342e5060800d82c0c407403250310a0f43c0072030907030382602d4000d04610361220b9030045c01c012480141c0018892304018014007207403090f040000c201e24003a038860500301008008161586009a801c00000703040040000e908801300903020000003500e01000c1072501c1c0080d08041c2008a51840d220a1058406051980075002400360b042203405800143c620890000640041500e044c584c681e503203818800d0141e0807002504044c80d00d80e0103c04c11228102100c40d9506100e1144099a011034405000c0d6204001d450001603440d01513041c050003104c248801d00a180514058460020f98032503c01d94210702d15080c100c000300301d03235040315003020095584a152103002d460362a0038044001a43d44000140380c05140c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 723126582 1250 723125332 723125341
    0x2010c200f030109200105131203031b0f140c06180d02150c0a0315060903060515010e0f0a05030a113d05040f171b0d030509041b0c0b 59
    0x5003a60003900d030181c8107403c0c0b03005d001c0c00e0035140600344600f0385052420a203001141d00300c11044003900d4100080c81c024005102d0101901445201c035030340450b900000c0c0e05000600020700080164032410304211300190b800344441703d0768003640c9040d03484806403141c91412800011085042420500c45031145403105042140003242211411a10002c0c2da116542d41e600441400d41c0720708030718010160740e200300e0407c061080900801070001d5603a0030b0906451800d109050b01d9015103d80700140d030900c0c0400e202e80c1c2100c0010807151054400c1c03c414414140020036082090380312580600940d941c410402070981170715004104116121251104050060100b040304030211600148580062100500361210041404010751401e00d19182d10b41052919400c080c2e4010980c00c5a014611240320070140509840b05000f150302e079211140c03035130008064400081c400f90601c00c00080c07020716030b19940c000310003a042c1c084891a60000303c400090901952107001d480006210f00802c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 723127832 1250 723126582 723126589
    0x30080a121a01050a0c0c0f08160b03061c03090e130611030702120d06080d171326070b1302030f0a08030a050c07050d030f0f1e02030402010c200f 64
    0x151841c00180d5400703080c548400c809030f45180494000b40c60f825101d1400141c07813044e00605c000074129401c0900050380111011520081d070640103e40002010300c2046000e442d07000600c50f040c0c0e070f0f05c0110585100d06050944151070241c0000e0092204070041005aa5a184105200605c504400c0110740700e00d00304100c0c1c0e400306440c03020046e00114640801e240e601d0020b4140320b04402e400150459442800d540703490035454009010640101040051511894009610440b02a403800300c1e1480740c0d035036981048010300000c410a055111326481c1c2c0d000701c000d81d18071070342c0005050b009041c60440c102d122201c90104038468441c01d4110b11001401140c4640760380e40c03040c00b081c01c5403640342010002d401e000700b101c42010001c0c8004d00202d0010000c80340b0016003500d001031140c01500c43e0318103603041c14140e980301070308004c40c0d0f103009140320140400700130441c034005849845520040361982000b2030047c00882000c00c0c0c5641d000005603502150303a1040b0b8403070002201c5c04051 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 723129082 1250 723127832 723127871
    0xb0102120306060301050f1c0b06040b0111150c0c0a050c030d0c0b012702030a0605030706090608042a06031b0305130f03020f0d0e0a06050430080a12 66
    0x10b1a0004014001000103041107007000440035001007400b040c501c103a07500038000c40c203000070660f0440011810300c00d450400b88100150644286803481e080144500103c1d610301c0d14404100c0e103d03603401e002400d000303000c005640c80c000d02d0307405681140a26040c869540c0d010300c0011840303809100b100040e0399015100340100c4135402106507000d82c1c41c0c0f200b480146800225018804003480a12014070045131004600c60403864000290300c500700b070f081c1407a007441500058184446c1340014030499070401e84586e802640021a09050819041c2c440360b104c14a442803600f55000c84804124940c00d03400543c18189060300e0804400d1210808a003503400a0318a100944812503810000c10180900966803034001d0049074110b100c2c01110034079045548000b0400111104a44549403078150b008000900d000c0c9819800c09080a074001000d0005801210480200c641d4140d841d04140031100c10494000385015142c038110071000c1d088a005000042c07050f490b110151414a140101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 723130332 1250 723129082 723129091
    0xc0703053301091505060a0c110108091b040e0312180a080904090323040501022a120a0203120d0e010c0e040b01030f0606050702090c070308071b0c090b01021203 71
    0x20486416441e02541800416180d02c2c2c1c0404c07907181c0139000c12103848030700040c10300114658031032102e1070150400e0360081203403104840c1003103200401d001c42d03504005143c10365005003d040c010725008080c0014020312440840c0c10b050301000c0341701744506281011542c80303409917903000c021248102035030315143e184804000304800c0050258001d1400d1603844420814442d040044d1031198000f100ca00d2056800e5040c2003201d80001d09010950f4103108039116545000c0b51a0480700c0c42800c0f2090744410500e03164003813807031a50031880600f010054800640d030054182c1d042444e103500054516030120b400000114202412014506014400d05102e00031b0759882d038103070000710403c12002c0d00006c4161030416032211031030300003140070b407050714000c107243d0b120780707a59015600c140070091074024424512600c003440100d0200c1c0c0c01c0411154000220714060b002c005181d10380c445050f1441d9000340810b50740e290301041c4070203540c0c02003051a00980031501c05d401042d0000203248030481c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 723131582 1250 723130332 723130423
    0x1090302030c06070801081002030703021303060204060908060f130519030203370503060d0804120605010506120112020d141b0d03020c0405040501060e0727080a0b0702030c070305 79
    0x94a003015041a41c041c603002030003447c000d03181104181c1c5180340c2418ee0f03001528001d5001070208811600048444020034011010300001d25081800d003040d010000d00407440320340c4107041142000003d00c0340d00c0c034095400000c4220000981002540c94204030091410b00650205001c0c0395030a05a1450205000fa681c0034801c0102400c00c807041e0b00064241900010003214001c0060341d050b0142000d01010305204503540c941d03041031400e655040c0c1c82107019900410007800400410b0890320305581c10340560003c0641d0b244041041c00240d92400780079001c1c034101c01c20118202040ea0000d000030740d09103603e006c7c2800c0c00c0001e00924003000601690100781900024107054010070f80c001e0244c1c1c000201c1c0342e510070068580080032600000055500354158580c07034a540b01c00c08d103c400e40800c010700340d401d00c2030041d072b2203c8484025001e50301b81c10010703071168420400c071105809444180c41c0b1843d42d900c0d26035500ea103241001c10701011407140425038440104581c40e664903811 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 723132832 1250 723131582 723131593
    0xf15260d0509040b010c0b04030c032a110f10052b0b090603010e150c071a010602100c0516170408030c06150a170a050304150f03060621060801090302030c0607080108 73
    0x580d010342c0e12071020001201443380808645a00c1c030760510f12244500303030091a51400f420f45181800198040900c260700c142c2034180070029680724060920511042d80c188182c0e510003040500c1d0100c8140444400c101810302891030004040d6040004154070036201140300f40c0301d030010142031700d0308002d00340141e600c580110101e03266002071607034002004807900b501d840302c180c80f120461480c00001c130342d22881000040092a030304010b10710462003070a00403c06242c0201004003184141032a0059600b07480c5042c6080c06802403006029001050701243d450780d441076440d0f03d0360000c904904080c0a848001414820b0b445071100350401e0043c50400c0450411403031990b012900e040c01c4215110b10412200065001c1004001074202c00c000041070241c40345000f01003690400001e000c250401c2010446039412441d0300340d5000b80d112041a101000e1940d00005101a42c0445170541c00c0c441201c052540200c0149105d00701a001e4038407075078030722034103540a400c20320844410f030703119 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 723134082 1250 723132832 723132841
    0x7030305070c2a09090303090b0117030301090506030c120606030c0105070210050a17240429011106010f0f0f3204090c050102010f15260d0509040b010c0b 68
    0x2000041c0305807143c85150074640d141c00104c0201d0b4400082140440d994031440020304c002c880c809401410ac100402c0c0d041500700a450391a4001031080c100980d4546010813091f607014414a4101d02010302801924191103400540e075034015198680070740102250070119512a50486200640140150140102c085400c843c0c56004403045d00420040450328885c3c0d0700301c2003000307000300407044030250000030040748894501c0c01001030741d11441c45c0c110482c070034001c80c820341c46001b407819107080c072444600307801a103608424040300002401440e0010032080c5580c0e140c002074482c032190000000d40c4800302144254914010811a1105124a080c5541d0200004840c050702c000f08100508588030118082e1901ca04d42141c0707100c140038007031142e540e092140c848081c2d10400e003400580d01600100701600c03c2401898680c1c41e030100c0e1103440ca02c0c54440c203080c0c0c4031000226080012846801400d54002d2445039104a042c5644c0c1040d661140b581d01d642c95030004d0185500361034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 723135332 1250 723134082 723134123
    0x2090d020607170705030c0c0603060906040903111e1b01080f0c090a0305060a050c04060c030c0f08030c03010306060801020a090b0c2803120e0c1905030d030207030305070c 76
    0x100c000219044034000700c10103ca420640d001c4c4c05070611450056440301c101990352402c00794416011400b4840134000c0108645d603c400b5a43c02800a80c1c0005a61600c0c0c2021210040c415844400030300c180b0500c181c01d85280307089000090f4080c010758000a829966402d148140c000d44140040e0b49400801d803c81c40030792455801c55103c06143e803509200d0710105910b8070081d4025101c1d0340100007001840c01c000d0080e142d01a2034004c8082c5490705001024107103844240d405820031400c114800b0800061074103070700041e50801d1200380c607840c0c0010810360a50090000300c80c183d050000016102c0014000c0c1e41d0700c44a29160b07103c500d400d114242103a504600940040ca1182d005001c10041d100482814905500720031220354620f03034180680682d140d03060343d0f88c0301c0307150000d000c4e014507020404290026044070003500c030b85a4029201560324640c1c00a96050080703042c04442590581d0041454070302c41c1d2014010fa959148064031070303d20804016040d0164265400310684 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 723136582 1250 723135332 723135337
    0x8010b03040c170106081603030216230d020a090912081509090a0b01090623030304170f07121a0610140d0203010e0f100b09010c0c0b0c01050a0e0102090d0206 70
    0xf110400059541d5035070201d00c0c0f400c803004401144503013034a1010b105240d41400f070007410a5651172190580c42c03410050300d0000c032142e4003403016600480c072011240e96032500c00301085900105254141030b1141c4e01c002c010310b40f00a02b11980c4444a400000403030080d101c0030710a4000710706d43c00e1001c44035001d201106200034004d8505000f1004420000341c441100c0e01c2c003801040000040480c100311208400034104201d001141601c00700350001507074008100c81c141c40c0340c41205620400501798080c0382244601a150245c0181c42c404220005640500c01d0b0950245e40c44400480038150744d0512044242c0e2541d4020f651240c401e101113004503135400e82500005052403a1400b40300ca01c41c102e8000707802c20310003280e0301c50a010310400c82d641400c0d00040c1d41c03030140c0609450150030742e8040c869451004e050001d8a000c88082c8915582488018404050140e941c1c91813000d10394001c1404468180341d25181c14544643e080701403082d1400c426029018100400440e003c000380c0b40c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 723137832 1250 723136582 723136619
    0x50a151b0519020a050405090f010c3207020d030509090c122e1e05120d0e0307051c032007090905100c26040b0f0406090b090c0108010b03040c 63
    0x154100130002d1192218464a44a820000e02a1448207002035410742901c0e03800c0072640c204195005024407407007403100c0402c402c036440c00e051040e17244207214500c441d0003500b074007950140104104006058100b0001e004640048401e000c0c45c1e51003c41180460190612141000c0310304ac0000f48a0a40151030001e09120207446c10070303480e0542e843d50340d00c00344d90704107014008001100c00b5008810010000142c10115036400e41000301c4400985e0703603d18002080b0400008040e12002e80d1404d001c100c2c090700d0301034800c1d550920401b14081d502aa10b480880010b95010940703400e101e07010110501d41c00b161000740005070301e41000000034045101c815134071401000d00c40300c1c03203030f0341c034851074081141d41d0320b696090700c600c501801c08895043c010000101c0a2400f08000900d0040440c1c4e40305c1901c0e40e550310a512542400380060116848c01016101514184002e0100009200406000981c0c480c506680c03030301030075060340c002074a00a00810140c081480a0385182d000840d46 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 723139082 1250 723137832 723137839
    0x6130f1d0c070317070e090c040b03060904060b06072a0e0604090305041d01031401050105100c03120606080a0b0f0904020d0317040c030309092f04050a151b051902 72
    0x80c80b03020041340342035030b2080e40c024000c1203e124070707520700e400c100b0b65160780038000003440e6003498603045000f0024130000700418031581078800000c003080855403000d0b070450b80c041c14480d10b403910741ca840d05120318550107111200b005c102804080d40c000620b903106680e1001480c5140791144000c1c4030103441040340c200c0900900344400700d5030042040d03230f00c030841075251689541540b45080900180c66443c2002c11164117100040c406500c5045a60059060900c1c2000000849003811501c4005100060180358100b44002400315880700d07000d401a01c0c6000100903031440c00c81081268103481040542190324800014094a80700b10014400341c041c1c1007140070505841890340c51514121411203040c1c0141c0420f000b4540d001c0240f4018188502003040382c0440e224900480000c051500d402070100100c2444404090b00252001040c0140549005a468150309499605070320440b00000f245507203404106000d104031143d4058105024000003408008035514000e1450010b981 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 723140332 1250 723139082 723139097
    0x180915101218110108130b0f0c04030501020a0e041d100b0f0a1502060709030201021009050709020a051806160b13080a030e0f0f03040b0c01060506130f1d0c0703 71
    0x20302c52440c144444140c03040552400d076250309070014103030f11809051718100c0420062130b200000d581c180ba0a4001e8012040b40803217603100341c034400f21881650002446540045100a0040d40180e510010400b0454003800321142ca4106074041d040d85c00d0003498035a10104140100803504d521103199218043d0040c4007031001c1101061041c511907005429107416400388902c580e506100283e00102140b030306400e410f01e0744d00000c0d5a4024205c104015135900e05501c0100182000105e00030101041c00390744458541c0c3c0064015000304000142221891021090a29241c0100c3d0203074519201800300c2402c40b0f480310f01c5440c400030490780e00d48884180220106602c01d020344000c1c2c2c8640e40106000c1c5c4c0a003125400d1103640400c0d4003aa034825a42e81304a22030210171384041d01c8007000c2290b1201d03894040311303025008603032066070400c10001703ea44000d46502c0998040d212100c144070385065035521070526448035040286030014803040880d40c041c801000a1420030300a03d41001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 723141582 1250 723140332 723140351
    0xf040506070804170a03090f050603040201081302030f07030c0f050d0816080d06080c01110d120b060406180b0c030901030504030203090a090e070b0c0d0c080d021809151012 76
    0x1155680408130141194002007403081015445840c0c140a0030710002d500e07940d1442c09000c500103020243c4000e040c48150000070780c6482e00d50645000c3c454005003207c91600f503000d005621303281e10b07000588405441d0107010442d03140c103c09610840d000075018440d01405612010711540010304c86510f65805181b20f000412482c80c00340c847c4c08203124001070107a2519908030b00e813500548425040c440d10b0088071a030141c010a030b00c07111400e24101192045c24110b2080018940e0128280d0b1104001c6808510140d11641000301c0a24411042c0c416945506a603001805040d00c00341d1258010007007100294429003116800a210340100c074200140300e4000303480300016811a0b04101c8ea50505e0904400c4108a604010000c4010b482c0c0b4210108140d0341d11440384d4901e1405111540184400b00b006540444100c001445401c5454400e9003001015003140148041c0c440d260b1000800e149142e80c0e24035513440710300180309041c20485020240c40d000c01c1400c0350900542e503040c0c5c60 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 723142832 1250 723141582 723141599
    0xc0f06070203240a140712050a02090402030a150e0405060420090406150b16060207030509030303040c080d080603030a0f050c033013080304080d1b11030f040506070804 74
    0x2e0032881e02024070104241341c85a07800b000c5031642c0740e03240710f0808200d0078090045d402120100c2c0c203001c0d00b0b43c0880d1699440800c0c00191007003140d09500140700204000100f0760f9a40034110100303000d038110b80210754840101007500c0c01510042d1640d0003400105000a0742d44d85100c1851421460200000e040300001400328101202c003696129100d0451400e0403201512044c080c20385050b51074146041108680c5070054a58402840300d0790016008081c5802102519000e040040840741d0341d00e801c2c0780c858500b81c4203110f000b034a1301c030300540d0307a0003a4001c80d8000d1162001034021420140c506108982c0c2d00c4d039800c0c0141c1846420424a00c58840c00d000a10b5980740d0807070780014041e0b10900860951070040030401030307420f12406206500e00000000b1140301e402081d090b449403034906101c010f41c400d0b50340140c200361130529046003250b0620b803600180051910303580070001200210075160b00c215508000007943c01c05c018402c0d89495000b9058540c06503000300e06140d20340c1040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 723144082 1250 723142832 723142873
    0xe0702250e04111203041211060702030601060903060513030c060207140d0f080c03040f2a03060b040b030c0112091a1810090f02040b122d0c0f06070203 67
    0x10782c3d596096804650682c1400c00b4450301000180b0300443c40c1603d4682000002d205644002380b480f901000f1880030b903a80c69007034a07003003900101514503950b5074200290490941d88411101c40f820040003641800401c51840d1426800d500c500844c04448d81d04c102c000c0d0700219007268074000342c142150400104001c0c4011602250300c42408042c0c2d0668041e241c844020141c50440070308004000005c1d00382c0c00c5040c0590b42c0a040045d10521618415800700c1412003000d01129482e42e0000911030590090301c08440c00f9102089020218814140c8078507041020754046042d150b40d40280d03440d00e5101501240c020741d0300040c51000d8036164060200700b5200e210030b50380e0044a4409007001032210101c210740520040011896640d80c10448005491001c1c0c400d6540c0c0420310915103034190415042c4a0010985819410045441503111294102481026148600010308040000b007081d0440002010f22080040c0241003104a51000000301c1e01405420310b819141e0020144 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 723145332 1250 723144082 723144091
    0xb030c030603011d160e0412050708250309120c1403010b030303040b0a0e39030a1208060f0a0e150a0e0105030c010f20190602070c0e0702250e 63
    0x1030541da0110038000c1d03100c0482d0386c0064950000d80c2c02440005030781c2c00285007800c1c043e400c0054492095041c85581400b8800740700000c4c41d503d10b04103074071150740401d1812403442074031000c1113291501f040900c44a2035450051040380c8068081c0b11100c015403a6507121480140080307500c0741c030600480d0a5130401d5404031035450303d80e03080c403a036200a40940452601101c00901c444560003c011410703507001e42031880c400680b481c0f500100c8181a02c01c0d01070081c007030700720b89950a891030140001a900e503007420005200402007980c0d0f1130700000d80e0540902c0182440d92081c20054004540c0c07a010f486110f01074418407140a540d01c41030f603814010817640805600070343c5010181802d1034640906941000305c0c1c42082520300c0d030812102c4c0204004417110202a15800784881e240c031400c224140c0100310310b20982c000b00082500241045440b84d50304581443d40c9400525013002e00303562403c00350b002601300841c41c0d5554080001c50304403102da500381c1079945003480384141c403007a90b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 723146582 1250 723145332 723145391
    0x13090602090a08010c020604060207050c120f060a020c07091e05012601020a0c110f04050108160f05010507020616060203040c050f181305011d0a030215010b030c03060301 75
    0x40700301c19440e21541d42001058488001d0240e10791501000f5254000100018800f683c00305880c42403100400003800520f402615500302c03d80480d00c3c880d80c0f00306030b9030f1107a40d0348603003800a401340000e0300a948900303c07582d00510703926040225440117070410003442c0c0042210340b0302403100c2d2680d6003d19030003801c0b5840106030030070308c00381c40c0c050b0048101c5031100300da030040004c00941c9a01c010000d00e0030303422083d012080404180010721211383c20001590240c24000003086510b8089030f00e20081c40040d62b11480720740d075100000072031060b80c032419012030000c1c41000d026040000080405103081c05c80c01a81c440785946520480c1c1041e0f80030356880e407000005100504041052103940c031002c80381803d41401c0070010603ca40c030020f1101c180d00940c4c00b81001000360941001100200020020480b0061300ea00a030751001800d400f50300512035213400d0300c14030020340c0d42d96042e40c40002c00c1038995a9504d07958003040e40054581e9405669861f451050744100070116208415140c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 723147832 1250 723146582 723146587
    0x40e120310080f0a020f1509030618160e0403031e020408030403030311090a21020d1209050607050d0503060a120b041b0810050406090215030a050a0b011d13090602 72
    0x2100a15010b408007100900394032182e46940540d55900c0c8a1b1188142204d04074502c0244d0310300b03081540038100d2101e030584101010700074050025a03094420030011421500b805240241c41c0c46441a40c3c4034960000301440081030119100380c01400100b407400f5500c24502100d5180030089a100750700c100302c0354002043c1401096414080c0e40b41c4808075070111400e001001000403445286403198000d030f002401181c0c0c00748400d10101c0c0b00d00c103800a020383c1d4810011306020700c109505420540000741e4580c1c002c522494034074140d521a0fa0010002e005111a11005580690001e0901d581c8540688000148849485102c0801c10302c1901030000c1820032749000c8642d14070340d002054101c2c403511700c10701c6800c40000e0810800305001c00c000c00c0342c0e111400c01c0001040b00040103900488801c80e80144103406400850250806410800181d654041c03000c003118041c5403028001260010481030480068910305494000200241c040c962055105012610780400854104d03401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 723149082 1250 723147832 723147839
    0x30604050312070f0e090714040806060f100903031b21030e1902040b0d020612010e060306010312050705010f1505040e070608011806030519020f030d0e040e120310 72
    0x80b0108560002c2450404800030048003c01034812446075641d1030240200c070700040c104501c01d21035469204001c10025580302d4131588070a841d00403c460a40c01400c0c0942541c000b4104180074082226040c1c0d184c0964034110343c0c003111302c84013800b141e1605117420801c001c00b0501d07846620181003200b00d0180d140040c0d141001d4140e40c01c031074bc0c040700c580007504038a00c401042034400d000142d048400180c5021040b0008840101140c00070350495008a1070551900b04000c480d81661846802c0c0c01842c0c0d01d182c10965600000d0200805058103001c20a8a0380d0044c80a804454856000418140d1100b0b09805c11034a181c5d1020360510b200c1c0704c1c1000a814140b05240b0b22074003400180801f541081000b40411806100b480408006d0a040b15030703901281c2e02c038901440c1d00c035040d112040c601010b80705880307403080b20603482401050074200c001d1034001070320000e04659840e052a5500ca4004000082ca81500790884500901c0341e00c0400c030940070002c600c0b0350185000070141506 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 723150332 1250 723149082 723149107
    0x15020a0306032303031f120b0603150c07120309050d0207150c0b070e0a030b0f07120b0901140d02090c0309010c090f0902090103020702042d11091306050306040503 72
    0x503001d020510389142c80c11464810f41000c0101c0ba0300459000301e403121401e900e04d8181684200d0341c0040301d04400e0600510070014082e003683d0080f641281216142d124154010b0385011007694000300c11082000340b040040d9000480345210310b0306080005200540307440e12070600440401100c01a00000c109015440c419600c02112000c41e10705540e10401540d0303041030901000d4064014001c407002d5240640d522901c2e10005164407545451a90508400002c0a40002c3d01c41c2c40100c5c82000c3c0060005125115000105900400b001426440c115255a402d0b841802503600a43d406a40c100941c84440049001d1500701c0c100c036640746007030303449a421141502c0c8500c0800003152000c2212200e5040c00f0012781d080007100590303407048040103070000c1c4280100290054206414403c401d0158008540903590070003203e484a200815510300701e811161000240c0c0d6010300000c441403c040003200c4403000a40c90000b00d068440d030000745000b000702ca048034258400144140c2c4242d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 723151582 1250 723150332 723150353
    0x5060103062619030e0904020a03170301060906140a0c14030a050702040b060a0f140d0e16150c14010204091e0b040603031b031e0507020f06070b0f0415020a030603 72
    0x1d29a28080070100f050f60b00400d170b40401d19056201303000d8800030801b5075550141490085600c4201d10400840d900c90501c80394009100d9500030515a100c0005e04078050600401e42c102c0482d00b01d40352516143e4150780040301d002007a940e09a0b02c10b000c03c18668100010400d01079152500e64541d01c0610401068491404009008100a101c03425079544c01603881c075606003540c00c180800c10310030380b901e0080d03004040142e0682070400e405041c10178000716440d00e2201c02440b440f40030380e8585681c2407880c4440e0301100300043e480c000500114a6001e07d0107001d407034400001d403910380d8070010b00b0305403030620030540601c0100d900c02c0c4017861128070503e03d0b00c50b0160b80500c105451a14041c040a841c65101051604c9140c959010148200c10078850464210301801131b1051100c0c0080040e0424035080340140070055159155260940640da64958424001001681c1c1c0c411103014043d0054000c40d101010280300280c801d819002520004441d681c00140300b51640c00c1c01032800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 723152832 1250 723151582 723151603
    0xa2d09020f040b090c0a050c06040f1a04080d1a0307090213090504170f0d05070504092a0c02120a081c020c1005060d0503030414010e120409050601030626 68
    0x140d00c0e001001d43d003502c601d50f041c0c1d80009034031109030301c80741000001d940e030348191040c17001d4a00450381000100038104640011503401800c2450743c00405a0700c0c400001000c4e40e0244c00840144400384400501c0d41100244480d401c2c030008022130300030b010030b24003695900518021130700403860300603e042d004402c0c4020061460f060043e8100f80d01c600c801d50f0758009080041500c0051004034a841140c1143d540000c3c00801300b10500c0d01d40401822034006000e00d801f4281085414021a00046040003a5440b110440c5586134624801070b1200c241c0250201e8000c440000200780c14041880003000860050100c195a028403d5480028262400745c02c0002407041c80002c004400c0040c1c4841d2140f0781550010b03103500c2e4034002900e100104500203000740f0001080008200310b90601d403070b0b0020050001c2c00b001a1082c8034070b4a540c0545840c02d01000140f00800c104c0c0443d030009034109806040001306545c665000800e80c02102140264803040c1a120489010040000c42480c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 723154082 1250 723152832 723152839
    0x3011505071205030a11070b04031101020406140d0e0322050a030b07120e1b090f0c072409110102070e060120010f020a020a05011803080a2d09020f 65
    0xc24001e070341d450441c0006040320400300680407000855008007903104500c20140100300342c1e11001e0070700d014038030403c0440e0100e0000d4421030741e40c081d5071814003d440c03d5990a1319800040038441f00000c0702d82c1c2100301000c0c207003622180f030066074090502c010326800081e010341140c800480003000070b030010f5603480030b0300a0182c144100701151501078180d07044031184c50012641004103c0d1100641401c902c0d4040710300030b40f162181c650403440c5443c4200401924440340076502c05210780c0700e40070101c40008c0d0100c010008000058170b5140d10460001074002214a8140c0340d0303541804a40c016038040b540c008071807072039600720368042005400a007400e150b02c440c40d14010b00001d15040e0f110460610108440410f0441407000303410650007402c20703a40454645003c6100290f0710100740348140c6a5503c1c0c805000507075040c0390b4620352102d8061725a00b5007512010800790080c0841c0280540810700d61a03210220640c2500d1010300b0b030150000420b840c08203004001e44a401c0040d2141b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 723155332 1250 723154082 723154087
    0x11d0a030908121b0106030b0a06140405070f0c141b130e100908040513021314010e120a021801080c030a1205030601230a030501090207051b010905090a0203011505 72
    0x1c3c1c40b02c2804490001029040d40d4580c0c03888941410702500b019040108222610b86c104003000c0482d07403000d402c071440d0f0b580b51000711500344144011a0800c0d1110b40004500b462107030320550080c558041d06e148941c4190216104d00100e41d400c00101c080d22080c00c2860074190140e5162188102d0f040d04216002000300d40811900d141e41da1a020540100c015110103c4030305105200054800504014042c1c0c070a0004491258000754031a0100e01c0d941c40a0744000700e0407050802e0120040d44060b1200c9011580c40400c00110a00d4008195220301c0b0b0750140b08010307180d0f0044021001c0e20035070400c1c1c00394101120241001541803143e4001e900c900b00c0750001c182c404501440c00c00c82410010317070b07070313183c2e030004951410004003010a882481c049c2c5030040b9080314001d02c1280050f6a00300003903600c2c3c2c4c94402c2a40309650340030303002d41c0c0040d540c01e81c003644080c3d0952209805041a1004513980d5003c81c610036011a441c0380780076030100c0100f042d5080741030701202406c0c43d442c1051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 723156582 1250 723155332 723155353
    0x60c060b0612060f060706020309070504060e070e01051e0c0d0206220f050c1c021c11040b060c0d02060a0b010905091504061703070c0608060f12011d0a030908 70
    0x25002c80340200101d106034651080030210351120b2080b1020250000c0044d952450a1503885a6a58061040c14040c1c0c1c0350002c000340b2041d9402286029660381d42e039180382d25900c00c00440b2190003031110101c040340b1008100440c41d40c002e004101c0c440550018018844801d54040d06012004000c10380060710701c10140c0d0650340b40c0302042e0003903a1012140050241600b000d40c035001203526496002981c0d1112407070303076002c104504a146482280e08001458100c920f1215105c84c5a0004080302d040050b041514a0290011103032880c003c2c0c0394a04010003401000d2802442078105070160300a20140b10314410706020303c0040340d070282000840d0354035141c00707c2d040c000c1c001c0102203603e1860124105030359690700f00300010264005500110400b01030800c0d1a5844000c0844806844100018510307000b6806a0b00c1840b009142c454113100c800c050000202d00c10349003080035544c4040c034401c2d00a0340d160700c2e116000702400420b280300491502400458541c0c00403100d0341c1c01600c510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 723157832 1250 723156582 723156607
    0x90e0702190c030b1008011a060a0c021f030e0105010506070803040b0a090503040320010e1c080f0c1501090e0601050d080c0d020319030b0a060f110304060c060b06 72
    0x80001d0841c40215011101ca50b0414110801568000402c01603107941070107401600c4042080640e14240d000300190707062030240740440340215031110f400c207a090242030f14003802410305d417041d40c0c00909807003481445034000400440f000b034190808260384640c00c1c0801982403048030302604060b80d105143c030000f604c91001c103010042c4018034508040d00002c00c14661a0404c0c01100c1c2c0c06011203448030f84a1a0400410015034121041ca0941c0c1e8014603071503100c0d80b1000030358140548120a004015070800101000014050b900702c0010000b00e088440d021001300b00108905014010390254244902e03103560b0180d0050b54654240400c2d555503c4002c40e1590445e4822a50000301e5100783c5402c0d800d9018070180c1140c9401103842e100552a004001000e005482178105299041c2c03010040e421101d4505581c0d0700942c03412021301460b4001d40a1007001205401d00242885020000c24034540c455040000080d00c840480c07401c2080500400d2101d107011154a070070088034a501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 723159082 1250 723157832 723157843
    0x10140a0c0320090d0501020a0c15150e07020c030a050c0f0102031c05040201030603050d03090b0702120409020f04150e2707030b04230609010509101503110703030507090e0702 77
    0x1486030000c000244004070740d440b011004c980590010095403995801030001d02295a0380030709841e140e429050099644950344580301070030741c4801c0348078010381c2001c3d080d002c00d0800825800c10741c4250341e41642c02d40c0d41040401107140c0314500518a01040c00300380258a00410b0300306042d5031060080b460684000b10350388620741070301e0f040080c0030f65503400101d02801160380060032a0291001110315a90703d81c0002c805140600130001c090f840b003a00c04c90b0383d18400c4404084106003803000703000e9404985c009162103580c01441504280d110400340c140d40a0b0000d01e28003140d5003600c890a43d080000071000c07134a050720310880c00310510a481288100c8020110020150f69903c801c03296039807548031000c2800b0f134100c80360f00c490400380010465a800d46e101449000c1c1c440000586285c1201c00c507100d03074481c1004007426403810104854502c0b0901c0340c1d1040c19100c403100c0790000c80d80006401c3e40c074081e43c1d0100f864200400040c00b440302c0b0340c22502c0005889809c014410760005103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 723160332 1250 723159082 723159131
    0x801080303150a091103090601080303010b180f0603010f1a0301050609040507031d071802030903070b070c050a120f0c02010206070f17010b03042001020d0f0210140a0c03 75
    0x9120903010b180e000508070481c19049050040c0c90403804485c081e0300c2c517000d107211f20003041c00c0740c802c2d9889210071030b03036404244606005034404104c1c0001500e03501c07001404441015041301d0200c0b50076400140cbc0c0b84c000345c108003440fa070200010080036200004105004810545061440d410320020818501c10328200900940d01c0f039000c9800244641d0201c4401401e0005842500d1400d580c4141c85072013a204920b80049615143d015038440c604c2141c1c003c00302e0130000d42c5070462994a41070030110080c0180c0c280708406e208400880d00034041e040e52184038a40c1d4900076003001d132005c1c04020b10071261030100300b0140131600051342c0018402d5000350040c14030814101c0031000c215107020340a4031480b9420041400021141000006940030301d2081f1041c0c4c0c3c502e280c81c6003000700d65420781c42c503138010fa00056900000340e008010542c2c3d404540c1c816603400c6c0c42008103080503503418001e42d002514029080003116401440303045000e48103450107001c4000c4c1500703001c1c8550400030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 723161582 1250 723160332 723160351
    0x1a031b0a06080916031101030c020118060903210c0f02030306010f050f090a180b190302091b120f09010e0c040c0201020c0d020a0c0f0518070203041706160801080303 73
    0x202151140d0f40030080c101c0d142d000094080c400c1912443d200002c07080801c0300350302003410008030100a900601403500480c0c031500b0a03001c41091602c911024040e0307003030240c0a0081d8039103d940001103282c840100000c84040c0460800c50001e0002c1011030710107a001d045410901c14008140e912100100d45c0c000b90b844c009448500041d500c1b8124440d1030011648030007100c40024002c0041d6020068250480000704043c03413000050044041d40341d071a8018140c60540d0500051516040c0560006083c84215685040c040d1115119500c62000561900300000400c001171034012100b0342e001002100a12070001412075055450707000207200c0b0b00c100d4440300070304016403007541910722803000d00c0102d4850f0410386c4006510386250140684056070418000301d00c0d50881c0000d24120742000d849006c0d0320f00c04000d8100780d000040c011b03000b180000c1000251311480c1594441180e80c60b1800341c5000d04000c840400840110181035050003005401000b05500200070780c0d82c00742e05003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 723162832 1250 723161582 723161597
    0x1b13050601090b120108060c2505010207081803070501050f0a030902030309060426160513060504060f090515011e11030d05040629010c151a031b0a06 66
    0x100141c4403840e450f00708030051080031401031164624010070170304031a030301015a00603031140d20301071445200300360325880b021880c07401038540c09040e900c0070040903003d4000141040850303525106a94441c0c000074650700007a4a00341102d1801b031005034020402400c00707070b1600c1c00c03e00307002003140140c82080040c51740c1c490465084d51410310407503000c01001840a40d813151580a0004245c0c0c06421419681c5419010308010420000300342414805c010010558185400304003c2d01410001400c80843e45401d400034160f1100d00a031000f5100c805504170f165420005c5100455100902a02032480368400780481660080017015080e840311240304582100c050056038540d507283e104a1030b0b407100280c5036480d001107038000b80c0160301c42d460500c5290b4143e41c5e41d00450480e101e4802c1d0513541c5040d0045e456000341d1a80031454483d0521000c50303042d1036804401c0f6080002028060070408021071000c0c0760500c4043c00354019038284168500c482c401080100d10580903410600012 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 723164082 1250 723162832 723162841
    0xc03090d14150124030e011409120a020a150b0a080d020d1b17130f03030908160918050a0f020f060c030702130906090510050115080406020a050f0a0c051b1305 70
    0xd4018454800d1200024443c3c02e0010b42c0c2e14039070f23500403a20110140904805052000024401c45d008030406600912260249403a80080c0d1180441c1752009030b0b680d1041440107842c0c0006e000020300610000d00740d8403454510281c144121001190200003080564078682c04030210303c5400240c0200b1701696140189140c103819214020600038540320304000020140c0100010400340ca01c41c3c3c0e148600550b44528603941c840360480a04a00d1403031802c240000d05895021a012611529940d0115401600c0e99130500c0600340003904d40b00840c0c611101942040301c5003040365602542c0079440c4c02400c0022070b0301c3e03000e4844001e214584201040403000300d6600103500310394001d001040454454500f01d95203080103d03c8500003400d001c0005281e02c446054540c00114503200c0410540d140d41c1c41800941c808060760040c08028060b003000c55107400c0c00f0740f45003002a2110000d8664034101103140c11100500b603410514440c84011550712907001c4020303100064140410f00d03886 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 723165332 1250 723164082 723164087
    0x60d0c0b0a180909050709020304030c021909020c15010b040e0a0525030c030e010c090b0c210406020c0604030c06030b1201050702010903081510050c03090d14150124 73
    0x240070b0540c0000401240e001c98002c103c0d40c00340325a18480d40132666650341d1841351400b603000441e80030740812512025a005401e041d403c202c24001750340c1f4034540716501c0c0c03100141281c2021041c80030701d5008402c0d2500302110a001140503120005000e41002c0c030740869a11483c1000b0700d03605c411519440400d5041030300c01d8051380501e0b14600d010b4001440d00d10020010310140e0074000c002421f00c040e02411340018410442241029541c2e0102d260400034000800d0303000d1080944035118030154403c440701c1400da010340101074408495074862070140300900e0700d070004c40100c3c81014100000c10005009840480032251b4030700380418a0b808890010398001c0708400412702550034241007010302c9030f0650014a4041c426103031000c031603c0e60504421000c47e00541181c001c00d03035081e4020080d00501c00381681c100d40b00201d03442d2603402c00201e024400708480450b03183c00c040a404250b10000e0001851a43d048106400d0543c0750280200729074001c8400900340b160740b07042c0071949a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 723166582 1250 723165332 723165347
    0x32301060513090501050f0606030703092126010e06040b01050c01051512030c0d03090206190f0908031201090c110a0b04020901150e01030c09080607020a030305060d0c0b0a 76
    0x1d00207003880e4181c6540424000a01041c00046a0b65440c000004242c0d50355580308500486010704500d0035680c0d0541c09030300500303600c1000d0b0b400f00c00c2512a5141040403400c030091107000c070740c3c51078071601c0305040000d000c010740d2050740009075400e0018005000d543c40890b0344660200c4001c104012005c0050301d052144500645580d42494200210b88183c20b00c450301c800f000f070341d0301807030030307410030b0fa041e45030301a080c1904400d8000b09403c3c2c0c2c804d880380c2c02002000d0300080880e4540f4078205a1050120200001e2201041031040c0740700a00c0e4112850100a01000002d18901703002c1341d4a07109965014003603004166a1140c40c40250f074480c0307030304010007200001101c5042c1c2003401c00000d510412a4106d03c01e48800c00040340042d03030110141c0d81e21015440319802c441c201d00066028140c0e1065801c1000480280003d9502040181c01e01820311500501817010a5083c024103070390005000c01d01400c040e0031280001380c2e9050400e4200d554021f15281c0f80d2522201c2180c054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 723167832 1250 723166582 723166589
    0x80408150708070c020f0d0b0a140a11040e0c0c160603180b04230d0c050c01030209180406090204111305040b0f01051e071a07090e06060a0e030f0d030b06030103230106 74
    0x21448c0420014200e40310b80c0120700c1c1d2080340140c80e0a6aa5035411042030702d19400340c1909001041c0402c000c08a0f4450b405900701c1c2502a405003895400020146003151071040a00180003800081040c0340c0c1510840307000c8156106910b440480715225200d441001420040000c084518411400d6444034500c070394040941c01560003000100e00000e00c5814401c3c403d9a0074018407000009070340c0648200e074011a40503160780600c01d1440003545982500030000c1c0c560b035481e80080f80041e90390344a00140c00c01c3d001a115150321a1011940540faa107801103401103103045005040344d07680ca43c10480100c024600300c2e6440004102c004c2071346a55504043e64103501113000c0c0100300790000385140c7c501c481c05200182d80d8030854210b848803218814120903151607804070b8160b0034038400400d68041e0509100183c0800329020a01c0c02f98a50840c0c1190780018034411641a4940990000d08a080f980c841c1194110349468000b04904015600e0701241003100310f151003000e40002004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 723169082 1250 723167832 723167843
    0xf0a120b0a080c01080108030304030e220615030b03060103150e03041706011802040b0313050f150a0b010806100503060a030f0302100e24060d080408150708070c020f0d 74
    0x24564601c071580e503c90a008000340442c03c002c0000c1505200081a07a11443d0140d035824825601c507414480050720800e000072540040348548070403854903004140c028252040c529408a02c0c2c038800a049640e410301c054030a400000041012510324003c00d8030350a81ca60f000036050100c4070105203184030766840200c0c0c0030299881c841a203a00850018100d500c8058840342802c11665000c0403446540540c80d0002e0051011441245050050804480c8200b00300c0b041c80c00300c0000b0034507005c00d8960307040d460039060081005050300c6000b81ca45c01002802c0609860808000082c51000103604100402101000049043d0f84150300c040c004d50b0020b042028103032150034005d46684868803a0b0300414202401181c00f030340000341745008490b12803510b0a109400d0090030851440c09000d0a0b4040c141101040c00b0074080b000620082000c03a0061010708403c02c030715401c504000303001c5400e02089004101c0265002600b1155541d8103d9044900c032011800080081030741c2d6801416 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 723170332 1250 723169082 723169099
    0x30a0507140901060206070c061e1e0c080112020406030f1407171c05130b0705010e011116050102070b090f0c061314040b030111130501050f0a120b 65
    0x184440825400151032100455034108403403501406052070003885044016403001c400900704900c079a040d000804c1c40b6003408070300301e0071054000c0c000c0510006108102076885000126284403003541144085811b1000e00c2000042040a0301110b0b0520030702c00d00c854406042011940e0b01d52001001d581e016050300c1d01d9040070708000038541083c554151141c400c03600003040109811900d2440d18894000405180c1c802c5003032410b6410030512203c09205050245a4480040320300c88805002c04004681c1c40d2001420050b00703552035641c0001159240492001c0304405070411100b1141d01c41c1a81181040c40d450940c2c02031045240250401000d4010b20200200120742c6c42c5201c1d00400c09c9500d40d5040b50200401340c4501c104200c0798076503950080140346501c560100b8000d0008100213560048440860b003900d090702001110780704001a01c3e0b83d0103001e2800007001c0c2000307107000c50400c03412381c2c401c46250ac2000c1650051202d01d408180688100740c0203000380d0003000d480c03240d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 723171582 1250 723170332 723170353
    0x80c040e01060e010b12221514010b1c0203010e0c07290f0f0114010c0f0506090a120804030507060207080d090809100206092d030301140a0803070510050c04030203 72
    0x66180c01c140501400501c1b0040031907078003421881000421a0310b807050401200071aa2a040c01c0201c40c0c40405050380c1701c44109103184102c0107541d008001501c905560f620b84610458600d84543d500da2031141c0c41400107204a07050808035540c4407403207494040d500c0c3c0c0f403804d00c00f00440498100d0030700702e1007800b035510200080c65034560066620749281c06482e11003902030000640300b402480c2c47c4111035210181c41e513224810342c0104038081d2410040c02c40d516100d00c0c0c10304070101c0300703140710b9448505c0d9001001600000d01e92a1409440c10b50700b5418140d0300205680700c1c0050244c8900c0d001b1403090140640380c0206c0d414450040300800c6420307141d01c0e00c5400c0307030410103016100d080b4024a042c8401e0010510500c900c0c100c4002c0c01100c1c070640840c180304850300342110900700101840711091001040194060482c007030800610103090020030100c55042c2d003000718150010f000901c0000c80c0007a600c0c14070380903d00042103503a00c0b898901228020780d4030184d80351140c5031714003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 723172832 1250 723171582 723171599
    0xb060102030d0501140a0503010203041109180a0f050601081b01080406020c2a040612080c0102070f0501090203060c1914160804082112060402130e1807080c040e01060e01 75
    0x481020000f5518807841c587e560041500302d0000319009403c1503078201c1805800d140c0a950f990b402001707050760044582466003214504140500704844400c280e801070703c00c2c00410044240140100301c01000c5070104606121440c00012203014140040c400100d001c1140380e03010388414042e0b1808450300c10303c6080745104c0020901109100140031600d6200380c0741030a020b52029280c074848c0d180e1000c4456510002e80390310041c4a075106560a00100002841d030080183e2124080c80003c2a1120035004041c100040030781200d51040003005803603070b00f5030340c1c86e0107429804090034441c0001400160701313581c500ca06400048030030900d101600801141d20080d0080c2d900d00022560041000040c00c05030300b921740e00351004d148050100e0448801d41a49041d03200300091301c0503061031034016400e0340440954018000c00c075440703420003841c812401c20704000d21401e400281f602c140381070350403510f03020210301c9180907035252040f081d00090300b5041040104503440c96aa969a582d0004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 723174082 1250 723172832 723172859
    0x70302012a030f020a1b02180c040314030909070c020109030503030a0c080105030309010e130f1802010f080f0601030b18090d02060a15140424080d0503090601030b060102030d0501 79
    0x1d003000c03a00e030031028002002c039442074600f482c5550312030302e968204003428081305850a2130200e0344040302e1121800c05070300807042d06000700c0c02e424200d40c8640c2185040e0000742c146502e4104140d20600c01c00c152076607003010160b042101e80c00e00d411a0036035400100c415406981000e0054400003044c840c03841800da120300000001c5035100c078072903600d44040545070710403030144074001010500489214604006000e440d0a070114000807207020103c0d042040c0c5070070852248425509200200c15560040100060144540382c59092441c0c0790006401c4810702418843c10140c1d9054005200e4580c210808441c03415510b05003124508011902d40e0740d01c0b1441c44d8001030158a0201c0d00919550140c090102c1c2003075120422181064003401c0b4140d2241042c0360720584900400c00707000498a00705210201c000740c903120160912480714070b0300007076030100c001f006000c01c20800c0d00d240c041a02410b60303a108082d07035603607200c00d00103d00d54001e900401c940185010000912032007503054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 723175332 1250 723174082 723174161
    0x90d0c0308180a050307090507120510030b0f190506010212030f04060c092304110a0e010305100503060c070f0c0e040b0a1e0b0613060228150207030201 67
    0x240400b03440020140004940300703200d0140c160340050010302111701d16412255202640307150010300c804014400c00191401981d2901512080040078000e114100c000d240d840400743d0f13015242c2c1d06008080c0d0210309544c0407440f0a01f0340d2440464090382c420701c1892884064680c074a80c90f4103140100c2408a5400d81d4101c0b07003a4a00034682c214240540611411143d282c0e09002d001000c00c80420441c103196407801d50310694429200300240c5010001d008a81e400342d40c3c950040e08094000b40440d80088c140350540c01c0c0d044000c00a0345d90008000394008001505e40d074075403c4a15142c01821004a002800c6200401010510000b0390f072626110702d0103004244240e481d98442842150b40e1a8842c03403031020080003658000788560005500840302504082c6003803404002d201c0502c506402401c0160021030720030342942c1d0306907180400c0200410301541141000d80e550034000400c00315442d009600071800700d0a042c003c0d44422501c1d407030f58446044495414006100f0311a03040d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 723176582 1250 723175332 723175357
    0x180b12070f2105150301140a020c070b041d0a0e03070611091519180302091806090c0301060b0906040302190b13150201060e1803210403020d11030a05090d0c0308 71
    0x2136024100d45414040e04501440c0307500040c1c091348800e030034000690700c14008010180704501c0d0001321204a80000e000400c0d6505016085c01d00c50411200080400fa040106282c18040145003038100402244c268130f51007000020308141900c1c1461180c0150f035000c5a126543d007030f1074880d21619100401a01c02240b0500d0400180510240c2d894020000e01133090069400709000600b403207500035410044c500000402c404002c066140340040840341d00d05643c12041074440700c3d003024003442d8007401524500030f0030108400085030703c1e4000c45c80060310650200d036120001041d00340b1988041c0c004010101d603110035010300c01070b07062524821440302c0002e6900c00001d0600c18854402510881546040e1036260070020f8012141c0d00460103446000400116090f552106900d108954081802500e81d2800b403c000e418004044c03034804c284034030540e4014030000b02100300c41c0710400320b0820a89520a20011a89810001030020003da0301c66001206000361100506000306142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 723177832 1250 723176582 723176611
    0x2d03060e10021305120109021f0224360105060a050d11041a0613030506060315070815040e01090215070804050d0f02030607180b12070f2105 62
    0x2045040032407060344091003940304580ca090046107400550b00c1d800c8211700700049408000e64000814100070740803080500c610b41d1071401c0140f9014403125042445402200040d460040480340038660000c000e240d0001c20101c004030702000c1c9403013916505140a01000d8562022505503000b00000d1f140070b07106140e840800101031400240c0720240607400010f091074021100284006000501e40c110907000c1221a0440607440d240c0c040c0c50b0741c51010050306200c61035410014100b50307024110a0285c0c009444020008990381025078008842e483d00920365550401400381c180c040425455100d03040801192801905400c504101c0e80222940441ca0038000800100c82c8584003000b046600309000400c81ca1405880c00d00d0698096003030820ba07030741e0a82c00241800821101003001c20380a104507800120828010300141c00080141441d00d0160728500c008038500401110800c0610741d03011812605ca0400010034a80c6402001052298690a940904421078181c0d2641015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 723179082 1250 723177832 723177853
    0x2070615060509010e03120c0309040506030c030318030304120501050708060a051c0c0503060c070b13170a11030d020406020f060106210b06030f0f07030509072d03060e 74
    0x5828200403901c0d5500c1d0301c2d2402424000540380080340c061415403601441880100401100d401420690b07140c80146544450110802c0211640502518040d5000c070310400410380b4000300300c8181c10341180c00c070262000c88500007841c520450300200c0554034058915001c0240c150095403fa00940d12001240c0d9101400e2001e104c00a01c51079912030245009002d40d40340803066001841c5c02650000e040f2521100820329041c4281c030112044000001c1d200c1c240013101c5001d0f81c00400f055001c000c0030481d912040042446503402d120880000162690201d0080118540d210114802d480d06c5542c543c0c0c0c00307002900706110302d4004d40510aa03040d118100400c00070b0580c0c00e50b0312820201c4602042c1115055025900481c0b110303915501c502190340e610001c1c620502881a03140b8181c9040b81a01c0503101001d8400820302d810300c1c0034071098003400310300281500d8170302c0100a9030007030220024940f01d9030000c41c0d07041002d4041012091003880e803c0040a009500c0403900440c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 723180332 1250 723179082 723179111
    0x6210302010c0e1e01090f030309060f110a03050306031c0827100b030f300310150210090c08070806070c1106040503011d120f030a0c09030b0901020706 67
    0x10703c0600903032200800c0c00314450100d110300524466a010b00d810344002d602c0c2e010a892401c8a6041a00800c0300c0b6441042066444017100b60081c4e441c0c6000c401e202e03442c1580c4c0da601c403000e20000702480320100c005015510100f003403180200b03420840350003101c4010000341004400760780d5182140d440d51540a003002c05203c1e0000350343c080d40000d140020340400b010740202a043c420a6142c041c90061001080741007180d8580c07c10f071380034500101c103140818a07203d201418115014520103104010411946044140071640c8071216020103034050001203003041245d0104040c00c2c1e140c2140b54084c040000c0e032507400c0d07640100803591000e403a441e1700c1e035507070408a4840340047e40d40240000004c1180b40000860000540000e0810b0703280d50010b401c0d00c1c403001440307803030306003041c1740100c41c460400480c06806844078481e80f4165905141e00e05500c4010b08059a803511580d20400c6d5911480b103420003940c00644400d0325003480a103950203503000c42000c0d6074440c02c105401c4103441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 723181582 1250 723180332 723180347
    0x102010e0307030e0405040201170906060109050a0302240c0109141509060c070807062a030203190b1207260c010504030f11090a060306050a02030606120a06210302010c 74
    0x2c0e0180c0304c04044500e40e00800000e010020000c034100312500c09640510740700b400240e0700484441028100d1442c103030000425610750355004503c0364005075030030400740c1c662800005901503141400f4000c841c0c04050000c4d68415406a0200c039847d080340390b0244401d450901c044500400700780e601d041c286c0612202000343c00c1e101d00305260010b10101d50200074140050903080e11400410b4100308640d00d234081200c6020f118507036040c84210898007c000c8500d5000203180184c2411821401c20103060802c4610380c050340d0006c07a41e982c91416165443c80c20940400b00075204496070180c440c00d450785503000d542c158002d080c15010307025451a202051103220325506960706800d082c5192104210380b0f900040c1621404015400002070b0307110482c042c0e200d620044ca02183d414510302c1e00c00c0803600f004103401d88481c411302c103002d036039995403086642901c94801c800381e6580712145250003e00e850b601c500ca000f80c041a0010040b42c0b520707406508503020341c0080000c00c0f04e241056a098 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 723182832 1250 723181582 723181597
    0xa051b010e060c07051026060f03150106030905070306050408040e1005011d0d1a060a080609030a030c0203040810090210080402030d0503132306010602120405010503191a0102010e03 80
    0xe411050092000341010b048852007829a85000500c40f59020790307c1d41c001c210040035011070103080e4100410b0307040026841c61003060503002413080052042d207851909030103000e075904040d120214a02030120400c0413101560304040d003000a800d00d403405c0d178519401403080c41d140000040004030071440c0503a0400480c1d1040c3c5841062040e604001c0c1d050451604050b42c0c884017980b100030119440c07890101083c400c0020461107030038250100f029150b92a40000d845902840030400c0184012080da03800703120324100032031a0101400107a0450040b0380004070705216a08403003114002302e42000740c24034000d03501e03c0a45051740781d0072943c043c1d0840e0041d4040d802812284002032290004540c03048000c074095506d00e480c1ea851440111602c281281150110400c038510356005010050042c03d2900003030000004d1104015079030b010f648038490621030040005a00309800c621140607114024501308030200103078040c5111481100c0071240150b180007400b8189103000400c90340f15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 723184082 1250 723182832 723182857
    0x50d05090622050312060409140f0115260703051504031d0105030f0405030c010c030e151306021c020406030207110604050a0e06040906051305012f0c0a051b010e06 72
    0x82c001c188124175007511020b4941604a0756550510740464210800303100d1b0380070102e000c0c00002e88603a40c2c00d42507400d1040715550080700c00b00c0800c050000000205505640543c0301000f8002440c0700500782080741d8000342207401806050012103100d4200b982c401c0e4401c0d281d03c1000c048107502e0002e5001d444000341d0200f1010808105c034800d01442070766009200e0022680303400b0103c40301600b910900034810020940b6028042c170b68040074007500f64031117048424440d1030310b07180000381951008800e0203020240e0004a81415100045029840440242c802e42d90703250317244001002580103d00543d12000031914000c210700d0301d02c084400704c401c010202c0071502d05003403502004180140c08964441e980b140840b000a0050003078920550b051140410030f113030356050181c00d544007801c0101001c4622100d50456203904401012003011700c0005548405401d120b075460300c0c80c0795502502c80e12844100540d446d04003600701402c14000c0ea0384482401c400014002d80e40142c1d1b01c1c9101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 723185332 1250 723184082 723184087
    0xd09120b070809010b040e0d080108010c0c0215070b251403071103070f0c0f0e16110c150310050634060609020310080f0a0210050d050906220503 64
    0x406110b502881d40080300c03000000f4805c848880000d040740c056241c140e40d181c01038150f620740180c20905c11401400c5000080c445208905002030141078603010080c4914161183c0e501050400004d554000d50b0000f200103980c28003d00c00c0a80b04a43e0845d01c1d041035600201c0300708036105220501440f14682000340c116201c1840039200000100c440304103d10050060501045c0b5124255696901410403c441d090920a0303000000301d158108030318590207207050282c5410240301082d801c513003d18154140c90648686581844e500d02003590f400801d01c00601000103015006501502c0c04009051100d541d84040c0040f034020803901804905840000c4c1844880311109801c020820091900c402c1d8081e0b564002240c2e000c2e08155191903000c0704124000344007100280c0540b0441c1c004040c1803614140c4150344800c0d2410080c01410304100c203130405d81c020300640e940300442c2c880a006500d044002d00d603403403004032596001015055180b014114220a1040301d0903081000f451 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 723186582 1250 723185332 723185341
    0x151b01020c07210f0210110111030106020c01140f160b0708180a05062a0a050409050714031b1917011401020318010207030812270714030307140d09120b 67
    0x182d10042c14110078284489031f42650507440c005e104001c5520600404140c40b0b5040140003440c0100e002915418411000040c0314458008010344140c41c07a98001642c0d10b54004140e0312003950162001410f00c4850700511250a40280d0014816501ea030481d030070154601c24055500c1c3c0021101a180d50021404610980c18134152000b50001c041c4020741c4401d08074030006010341c03045d40b8a01c0024800300c0d0501c40c1c0c0c1d00c0c80c001c82e030b0086000c2c40d140305010b40942e00766295200241800e003281c89070352004400070003010142c0303045501904889800d0030f55154090081018420103a03a158176503400810100c5c1c1280281107880f0069005500b4240720158240c01e43c50400c601034154455410000006000700004002030141840e50170a02d04100e03484505543c280c454091003250131540c0141c89a800082c1c410856110700c00310020130a889011030b045110f00c00014004404420000308104d900180709071a102e42c56446031806603491040d0403003080400001401c11400c2c40210703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 723187832 1250 723186582 723186589
    0x203010905330915030a1a1f140d020406060c1115030c13050a0603060602010c0228030e1302041a18091e04120e030705151b01020c07210f02 62
    0x140c1d809800d0130301506a000d41ca200207840c180001c1c01c1101c18078071540074100c40f41c1d440f0313449135045a46410307180c480e10040d90103040c6d6042c0300e00070b4244c1000355144003913080d40c0311105540603980151041040f5a00c5400052400320030607002d448094900340301002c10f0400c40b41311808028070304c21190858031000b9034411141d2240700041c0c0e0341d04004401007101d503204400680104010f44002403410b26011020b400c0d21580098941035412050603444500780d031004855a0b10404410318011040d689030555a002042e80703c03a40103204040981d40f00317002c0340c0c020700540d08001d802a8040070090382030042d030b109101800c0310075081c8540f203031302c035080020350301d03800c54814003007182010200c00c0351f1640c02104640640d03582c580084606212604100b409040c0c80094020300081c2d424880404c00301c1800c49501100d45070000b91500d61202003401c807000907900301c40290b6071000c00b0402a50b0760045e078001d1018500c96044141c0b084400c500300e101c1d006903c645c0541c40c841054080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 723189082 1250 723187832 723187849
    0x1504031502033d06170103030f20030d0510030804090f09080a020d09050102030408120f07050d080105030115080606130b12070f08070602190302070306020301090533 73
    0xd051100d240289958888000003211038164502400040703000c10318402c00f03c40e244696841041070117512204a004d0071308958505041d607400d0308150070403440180040f26140d50380500c0d070704552500305c00009403030004001044d80c3c50002d80240500d468070200306400f5202844002d01c00c9504010400c01ea400507081400780c41c105c3e1100182100c0c6a0f10f400402c4d070701c000410340050b0001c040d00c032030306274200382100007500c400e10080d81004d040c2010a40d46440d8018410b884800208400e02816003040807030b5050b07035100b019070310201e481c40300142115000703000319840780d42820031403500500d900d0300b082c0449003c00c00800705500c9030010f00501c11007454040b1082921001030743d62984a072108036451080e600022f21100d403034017028042640103a08840320b503420441d4200051a4000352603011101035181d8201a000c042c0340691920300b041d030009046500100c000901408164080f0b4841c011110040f8a280301d0070920020a80e24903c040e4080c070040600320f821410180e02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 723190332 1250 723189082 723189091
    0x4050307091e05070e03012016060b10050703030b090705090415170307020916020c011407330912030b010c0c080109030210140c0f0d05070e150403150203 68
    0x40d14000280d44030202400d80f58101c0302240030031000b00030400a41002d01c03c2d521408919030002d2802081c80d44030318680d01c40c00e5600c9040c046603000c001d05000007640140b200c802d0007002d0264219030054040d00d6034003c04e1040e0046840c2a12008030b600300010007610800d040ea803102d15110031401084002c08544001d2b0900128a442c04610803d0503400c1d01500000040116143d03080380c810801c000c00020b08074181313a075000454441c0690000388013200440700b42001c401c80400b091995055004081c0040d04169101d01500d0700c06800300e800f00e0f81c0d40781c070103080c100c10540c0301324200c10b0f21102040101401c2ca1001301d4144288a03520980030710605141c1001c03c0d85d81a1a034094007142604050400d0750341d20031070010540c04016078002c00c5001c55091012030344008070300751800401000e080c00d16a0018110050208020441da40015101c0c4104050700300814000d00305100003146500822008581c944e480741604140c0f8222030b44072000514100d580600346020350001351 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 723191582 1250 723190332 723190361
    0x9070e0d02040e0c0a060513140a0e07021c030615022406010309020d080c010c090810111b06010f120b0117010908040b0a09050a060c030e032d070b0405030709 70
    0xe80300421307030f551804280000d000b00c1d174469031244030f15071044a03551115800003a03903840d00d2480420030780300c502d90001240c1e421200840c1699510304240e080c0413034162281c41080d16010584203064040d03101c2c0058415458044980f4000c4102c180e98403c0c0b03001c2c0c031100b8035807011004580e040303c029000d0303030001c818500030606104c0381c0d0102d00405102d0310119800d040210b82103005401c240700e01c0c0500111032810b0004075250582d010f0f21044004144045144caa0854981da44610000c44180080740070814100c40c030402442a101c4400b0700445214444440c0c0001d80c0340d003240d6517880034582010211581d0b03443d10782040c040d141c00b182d03605155529100c00e04042501c7d5000340c8010708144401c0348d070710f888000780104052815084544030721658a003d121051740074040340340303807541400c004034031400e00d1001034641a014055072034044a5002c40300c584869000410a15448031300032240c0356a1241d4590529024600505030540c1c04031508111849840d04120854200c02 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 723192832 1250 723191582 723191593
    0x30b0f09040303180c030605060a050607080c150c0c060108060933190608010603030e1905040204061d04052e080d0804021002010504020310020c1203040f0209070e0d02040e 76
    0x40283d0140c1c00c4213000141c078402140030040080c420207004480d40700381c048400c041c455060100040c00c500801101402c442c0b00402e000c03031007400401540c0c405160011100c010f0345800030001c02c05038800c00c58126540204800011085000119030780584035080140550040c841c54941c45000356901d460010401d01891501d048402c009150140c0c1d0a40c0920b0148500d2007410020b449103030307000000c1c0da03140010800101c0c0d0b10000800c4c600001f101c413400c4054000c01d1007c0b640311070741c0000340c1c424400140003031310380c3c1c00c01408850b045807a40090007200b0401c081004990044400724004403a40c0c13440301a004032010217400300c4603410108a00c03a41c81d491298600301c14003007202d001c15110014042949000d1901500b00401403000b8007481c81c1c568042915460b580b02403c2100d6000301381807201007800e000c80c109100312000c0494880c601801c140d03909441940d402da00828030440483c500c944101803002d000c441c090702c5464118025400e100041004080d92450f03405035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 723194082 1250 723192832 723192851
    0x3060b0a02060412020c0a0e070c060e03210402100c03140712090b18100207031a06011404030f110a0306090308060a080304061d03010e160e0601030b0f09040303 71
    0x8000241000303000560040110780740916002102511801d1180d05540c0311540d07903145c90303603904007400a464041010041c20744803480d0549803400b01c50f6005040505001188040b0706000029122110301243c589404001c290160240382c81c0c02d0350083e400c52040d02c1086a864026074a650b0074a2003882c10f8404002d003d44079605503040310500705d90380d40000001000c01940000681c000c0c100d0010080e00d026048850290310070400d071026401140b24210007043c00e40213010f00c0c0c00940d000010300790003200b000ac10034186081207d403140421000440d080003c100d40701520306403540301c04d820111751320644440d16011360440342c0ca40e101e00c1488006c4002031043c0299244c2c64407036100c41046007010404c115014125802001699000b40400c005c0c55074005410561a4008101c0170803280b0b03001c02103405000a000580c0303880c0703e54400e40002940c0481030004039980c4d2502c4440580343d000044040e990b80c150015407205a201c01c0711820703e80070a071150007501c40e041c001030301c024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 723195332 1250 723194082 723194099
    0xc060207020d0c0f06030b100f11070510050d05010f1805062d0f040b031209060721090602070509010b21070c1a04020d0305070309050406031415071e0306 68
    0x65034001000d00d14860321304003c4d054040c018880b56042c211140c001c0c05111b103400601105c01c0103400400c00c0040584005150818480e28000d020081e0081d04411070404000c0d00356401115031184040c07a110000a182032802d900006840d4000c0e000141c3d2100041c4030005028007401465101c00f030806180030701c07005040081c40c2e001e5200c4a1008070080501000b031001d1080380d5030340c013450400321a00c030b0796540403c1507002030304c1403500e85454101510100d841401071400080030140b2813102030b21070081e0030b60782000d00d00c519654003031800d0b15981c0803a01d0f201c880c030402e600207000100502120b507285004d081003100000311850075003100365028400410694640c000300d0751070340d080c1c1c0a000e442c11f602d01c68501e01b41100310b5182016404100c7c801007021028013003143c0450036900701072258858900038070000304140203076502d03400e0100d140400740e03030040524841c02204e409044484105584a448140c4441049226100305000c0070100708210900b00340e03a40c0000b294194 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 723196582 1250 723195332 723195353
    0xf0c01020f18210d0309060b03010e0a05060109110306010c02030a0c060302090103060902030417280203090414060d1101091e0305010c050408061906170a050105060a060c060207020d 80
    0x581d0300c464100350000040501c5004821407260ba10043c8144003002e8129800041c4941940a240b40008840425090201c003c2010f03c3d0701603815420f0680c9022102c00c0003803581081400344094400e80d990361941e510446e00c000c01c6d200c107065828800940c40f0360145c140600001d0004e0207568010100390341e00702c0d0100302500200003103540856481d0300c9581c1440b40c84050b02a0300340c00c501d982042c0d220154a05048000350b0f1152000251032501e40c203102e81c01d440380700c4404006050010180c81c001e52a44c2065121900603850401250300e90805000c1050080320007074461500e41946444548103020a0015141401000300001a01c12414100440c98011424424003614214905a07081d0b550119040d41004418401030011003000b082942d042401007a04071035a60840c00b0080242c852940041e006000c2d08485841c5000c0100f84c1d08105032055000700403035540d183c104501c1d01d5803030148400051700c03030800c034000a481c7d42c000c000c0c3c02c3c00200505032050080e903554820b503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 723197832 1250 723196582 723196597
    0x1f1514032a1e0a030e150402030c0a06170c0c071205070902040303081f0f0e090c011d0105130801060602030a080708040b06220c03020901140703050f0c01020f 70
    0x14011091520010349040400d41e82815448040340c0c039100080b40d09800800040601c0c0c075481ca400503940c00d00c03d0081c1d02034958070309008165180da05102c802a460f24108a030180c0c0a400351030030b4580c06181a507120000d6401540320308e8200c60941080c41d40054005140f1040c10303004101600e4020010400007000700848615850811118902139050040c03d51203005150300500041c800a5001802d09038400d0034035282d11000e0032000c007200d001510940c00000030300c2c004c0f02c02044400d0900a000e00c030791200d500303c81024100c007004480204140b1040c03c0c1030800c52008504940c4107400804580b61102e2200402d08e480b00c11795821104c030381e8808009a84001150a80740360084e008540c000d146d41481d01c203900e810303141c043ea40d1900130b1100e44941c000303001039001405d0b01d1410660054038500c0400042590755006002035205c40903107804203584940e0306203054004011200d0203541a51000d04159000b030026045800006214035595000e00c404440307041008081e0510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 723199082 1250 723197832 723197851
    0xb0d02071a18160605120c0d05040f03031a0102031803070504060e0907080d080a092405010f1202062a030c010c0e04020306012312040b040204051f151403 68
    0x1c02810403800e43c580100740c0a080c11807400d038101001102e4002058903041c00030203422a4107560b58160126841c030031080d03011141403038101400705000b03144841ca101a031103514100107081800d150700ca9a075640014031401a0710410007440801c00e4545500d41000d0090100e030f41d00c81d07c0d140040e0030b488075504140140316100041209408040081000400348034014060543c0032200040182d98010f00070085640c8610700300d0b0410805541400391100c003582d500c828400c02041e4040030308001e116840d5402c00038000840d030580c91513101c008a90740140102d00c3d003401c495100103450018842c07800c0c400c0c0d0640401c4400c1c80203100070000a4486070000810300243c090107003802d44800d030707554043e606c14002c015070f50340c02a0040c00c2c003040b186015842c0c0034201d22000080e01c94019504240c04d021028082009000c440e0b15000c0c0d4803c50301030015946600c451020184d0390300c1d0468071003011000810800812410404c252641032030141c10036010140e007c20340d54800c0c4c0c0c0340c1c0300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 723200332 1250 723199082 723199111
    0x20904021c0f0507091d0c0d140105010e04060b070b0c04030c0608040c06091d0a020903030408100e0a03080c0a0c02060309030c0d020c0102070918170706150b0d02071a 74
    0x3441210703124982d448451405c0400906040143d00014041c411a40007404020f20005c1a400e501505c1501d0381c040040d0414031500360002d02c050301d101e2080c460b0a021801c600741d0484541780030300070070069810342c0a110b410007105840324030260102408003020001c080102001098002188001a042d10f890b4046c650038180303008030744a5020762106c000c104403103200b80036004801c040c02070081c400c40d44488607a15611b030540c00034410703942d000d9814400018002102440400e075403001020059040102e044001800d41d2140801c0c90020000340d2450002000090f1f0740700501038808451401c10f190400960106966034001c0d90f80e01581d41c4086003280d4145070401107581104047c2c40503081300007948001075034030541402042c9895486e810042411210700f0303440310882d074000100306da2018030300c1c5ca40701c5268400700041c1c0ea200d0408061400460860382c520080311406e4020b03510700000144002d00035005031008a40c0ca5030740044900c903190902c4401d034007c03660f4100c0486e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 723201438 1106 723200332 723200351
    0x7020a170c031920010e01050c0c0406060908190203100207060e2d010504030903031d0d05011d150708092a27040303020904021c 57
    0x1500b500c900d40c01000302c005080e1802d0440d6000301c40219102200c5070440c6895404440e030310b40815030342c1150b4030040d44104010014984140b0a60309485452030000c0e065500940c01200011048081808070681c203016080340030701c140b2054280703240c05901003502c5490308100348120650108240c0140702c8190402400c2000000a0350786403449076445218040440d10b007540080300e0480c40d0401000148102030280750140c4a40c8844c070701e1640d00f22160580d142c05003c410100400462540c0c558211013100588144c00100300307076403408100600260039034000b44050b401490000000d0391056996500580711345048112031761b640f41036629040742403007902c81010049460f02d0403242e105940c5c04103880c04540010403114040d1182c01c103d41151440c824804248000c900003a000c2d5004040840c4060009410308030201086444d10300c0c203224120000f51180f0103c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 723021582 723201438 := by
  have h0 := BRFrame.cov_init 723021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 723021582 ≤ n) (h2 : n < 723201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
