-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:23:51.774321+00:00
-- url     : https://prove2.me/submissions/7d884f6a-5321-4833-b242-c700afa764ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 541187050 ≤ n < 541366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 541188300 1250 541187050 541187113
    0x106020d2303151215010b031503060103060209130507050712050c100b0f0109060516030e040903030e0c1005040b0c030f13080d0311030103060e10020a030c0207091401050909 77
    0x568a00a0402c0741000300400c0c4d21324020241c071820260707240f0b4a140180078104400b04004007040940c04545e0756055540c0004064450305c0d6035a15209000b540035000e428001c1c00b072401100404503943c49001d2050080740c131142d1a02c40039a480d4580780c400818a03005000c0c00b07100c0c50428400401400c04450b41042c8001020164042008295a000d48100d07042024011091040c2a8000d06a81d13080001c4503900c1212202e80ca015a50382005a40b01d0360007034501181d070000d00d617060300000c2ba03401525059981c41c2609a0501c155900414040f00110394100410411040050b009040780941c003010b4905091a80c0029505c940c4584004502507030350340e005020040082c400401c1c0840c43e070908101004030394940702070a000506c00641160382e07402c1d0300280d100050100c04848545250215628030350303480f001d03004204400c010801889003100100e0455081e00c207207104e1410407960303900b00c0c1c0e2a1604120110000820380030780d901441c851919a2200d06d17094182e900311420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 541189550 1250 541188300 541188331
    0x80a020103050901020a14070c09231305030a120e10021309060302030a15140c0d1419050414030712031107020a0303030b0d05070f05180106020d2303 66
    0x4040c1c0b03401038101a0140d10420011a00a401415455909841c1100b1588034200ca041100804c2155400300d0741081c1089030303004504403803480f0100f05840d2a941d02c4031980b00c4224032064a0030f003550040c000d034003c110700d03048103016041881880c1c1d01c0d100c0118548082200e2541824408241000b80702d8000c40c005c080120510400f40c0a84810b0408100b43c500d55000241c1d24075400740c01804100007c0c400c0c3c003080c3da45410240c00e10b40140b03000301d21030400240200d0716510038540551003030701d400400751300080340300a0503004180c0110f100c07500c3c14661108100500d000780c01151200c0c264003683c07466400038400380289500540510700c0602c003900002c5c0c11b5074010070981008032020450140180c0c0d0721040c0314142c035014030b8002901c1c2e0850303001c160720a03485400604a03101d0540000340c000e000e484804103442041d1919203052500140c0440c05000a002d0040940c02013240e040c5482d101d250760381d428400b029031520305100f685c04001c1d215031042e40c40c020200c2c900b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 541190800 1250 541189550 541189553
    0x90a08070905180607090902030c0d05131217040b180d0210150303050a0e03070b0c0309040605060c0a06020f090909010902180106050a1b060e0312010909021804050f010501080a 78
    0x40c1050f07002d984410b010f01060700d071100005003100c0003030280d4546982c0c0440890b02600780002500c0b0f4406001e0410082420308252502902411082c21100154020303c1e0342009442804d81d030400c0b5464542c420f6540e11a9030b10302c035198000904003460340e0001c00484166400c1080200300104142d00541041d1403051402d5050701c079001440c040000000000708006544042111003641d4a441c05d440700842000000381402c0721980404ca09200104041007880c1c0d004c0010304607110203c0f070400080707507540b00f400414007954000c51142c0d04580c98500100c0c3c0039400a103040744c035009509260520550002d01d00d89002e071041f07403d5a40d500d001c0d90850521501014100726902d280740341c50742c03605e20014200e1080090681c1001540d000d851400e0314112038080d880755015205025802c50520103035030b03030740002d11440303210401140002107052062240c1c004440e00607249481c0c40c80320889000c07060743c0c06402141d1a00c240120070084074021310403207010300954030207071603140b01c1e0313 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 541192050 1250 541190800 541190821
    0x112106090411090a110c07141c0b04050102090d0b040308091606030b010c060204090b01120e030a08060d050d02060a0f0218011b0606080303011502010c080c090a08070905 75
    0x108154015140502840089104000040d90a1004907500310f0940e407000f41c0d80024103030a0318041054400030130081c008140100d0180c042d120240301c2c480590824104100f0600070340d1044101841100560401050581094130b41c054062400507150000d01808200314030403000c4143c0382000740b00284010507900080d1036400200300c02c0281500050803d5002c81100c883c410102070569600b400b4174107034080c03070022519503007000045440d656610705140240502c0b0030716500041c800d007140c251012041c41021030300c1411070000d5041200f00c450585100e00c000d0800c692214286640d80000741007081201d0084001c2c0e80502000c0c200140d8507015602d1002c091150396006014406c19170b1964040414031600c24603160600045500000010200390300380504401c2c20070301d001c038014500000075030490b0b404100c0140700f1415600201c0c201c0d5182a0703500006040980031540c1e5214a801400c2032100050000200a507100f541d07a10b0020540d00080c40b10352104208952140c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 541193300 1250 541192050 541192117
    0x408030702012c040510080f07051c03090306111b0106090605010c05030d11090306131b0806270d0c1b05150706090b130501050c0c070302060c0111 65
    0x92925642a40e103d8501c81049001d01c48003424021642e0f140001c00c0a90b000702d280300240040016189691342042609403981e60300d010705805440d40006442c800800e4010092841e07402d0340e91004c045055035240406400316a0b40f05070069024490008204c03500590400a1004440000ba4042c60805800700303079030351a44140d041c031046040001c040f49002c0f0031601c1e424071302000007880340c0c0c410038480340c180204460315030140304a10400c440c0a2484281507265402044079501e420700c005540843d80115014880726504803401041c0200000300d202c42694144000030f4046008220040d450203010440c1c07507000540f0084014140715070320542e580b000c4021601e02c407406040a010800c404c910445505402400060703640c103004d083d03070048954a521050300351503810703d00e01d001400e1800c10416250b075403070040460580b90810302140d0089a030200079103043d13481c50302000358582000c3c2d0246540d5480d001c500c40c403801e00074020040c2d80c4031203408003540c0c01d950b8261900c2d42c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 541194550 1250 541193300 541193327
    0xa0c0b0702070501090308091c0813050418060e0f030c2d06220804170f010b0328150510090204030803010e040816150c0c080f0307050f040803070201 66
    0x4000102c103009699101003a42c05503a00030650541d904040d001141e40281182d0a1281e800c0241544e074003082100402448030314070030000c2c00aa540c07103008010032240c0146010223500404501080000c03043c0e0800c40510b5425016502c009514600290031903104c100360089e280c11007100c40c0c040314900811800c1560780d40352403104900d002c07a05c10f03540c0c140280002e6840c0741e002400c0c50b07046c8103800c3c400041544c8040e15130f44640d079036401c110911500e000c620015000305114215500014440c0c0b5501f140c0007401402c0480c1d00d15814010700b203000004841c0c0d4003c0d000d4101c0807030309024000200b01c4200800203002d141208003000e07070358281d0300080c039118010842000402c0c401d2040c0d0b415250f007140c15800540301c6240c03800c5148240b0a111803190500c41d9040c0174042c12008140405100d00700900103460303080700454511524040060541d01e06121a800d840c1c660700140d07034888601e0914a1400403440c98820f690b42040c0c2c41840680d10010b26001103507401214184c128 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 541195800 1250 541194550 541194553
    0x70b160324090b060d0204090903032a050901032403020307050307230f0315060405010906051c05160e09012711060d09030504090b0603011d06030703080a0c0b0702 72
    0x2500d00310729040e6140188500400162100c140e50000c0e030b102401c449400d02d180100b19601e580d20a60b08014001440090780880c1c54483c0e403840c5603080310789021090070300f034540082c600c0400b60180d4140d00440002c0b410103990300c8010b0440c100c041e0344034640510300c0760043c800700d10b54030405241422641000f8001d0300150340c200000021003600c100310108581e4501c00d8461150042135880700f0003600240c0c140705074402038803210804051180140000d480a202c242e80b504c00d05404e4030143d110b22904910452150f00144c808040596010340c0301d00d06a84222160801c030325500170054000c409240103d505101001000340304a4881e00f0f0300701d02d1409824000307151f00d0102060303140017500680c40c0f07040c05295640c40c0700494140c184504000c0019525600340103125400c44c1c042e9602c01e03881d01d4000311051401c402500d049603111110010103030302c908101032010f14042c0a05401d40302e0643c012002940c0310300070f00260501992500f554009500f400e2130045406400c400c150b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 541197050 1250 541195800 541195841
    0x906020c0c030a081603360b040b070204020f091503071106040c140301060f0602030d150e040f050705060f030703180b06100905090a06030210080c0d0e03070b1603 72
    0x105404d040c0c2e425008545800000081e03a410305444ca103c00c00d845909031180324411503420304207454a000000711508201c2d40454451100000c00e11690050744c4081c0c0e028061400146003680040406100351100c03182840c0c44040495400b80903071000d510096004420010402ea02c1900c515a591845004103510304054407141c0c4031010701e0040807940b131200d1040c8003441e18250088001441095585001075980b0f42000307449420286070340304542e040c01c101c00d00c078490211039182542c01d140861146a100c56440e0325020030034840458041c000c0c03035070000ba281c3e1000d0141c10141003c511700c0d5568608820b0007400c884102c8031049140a9a1700c605022850110703c0d01d0b4081000e4810811a82203000c0036200d001d103552109a00c4141c000401032140c139141c00190850f4825543d1401e10407110405582c0d1101c111210034075071809100400900d0380680082141d803000f44256450222981c54000c10000112901444c0b11030a08001071800e905100e840c4070390000c084000750 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 541198300 1250 541197050 541197053
    0x2060603151605070614010f051005070b010b160515010f0e1014040b041113151e03091a0906090d08040f03110304080a05060a02090f130605040906020c0c030a 70
    0x10b40b62a0109280200407011030150100425580007411002003070440b46415a514070548013150340a004480c007070307480d400300480c50600807000c0d13865443d48044555410ba00f488112041030300301c4450004054882c816030004100248440390080c518401d2500681d030600a00f0440b002c0158020309000000c80e0800c1030070039a80003004203a621000401100d07c24580024006e415450500390340245050320300041c240b006030050114031176903004082a50b95800003124a2100401c0a00200303110b01401c0203548148850312442c8170b918100094031505e41d80300c405881d03524100d0700c89041c9150091056400007000b0f9180c1c0b00c21000020810022201c0f0b005041c5074011b4002070019500084c1320003018000c4103011200f509640840740c80e2656000f10983c0c49051040503144c600032913012078601020b5000700c490a401c0036000d0240d40340e12000f0300c18409481ca501b40007c41c1d80d0742c00071030540d030341e401466410343c05102c3c0581c0350080940240e080045801d101442540008a01030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 541199550 1250 541198300 541198321
    0x2011d0a0b040c1503050108011406010807110a06110a020c0406080a030e060c03030c0a080106260405011508030d0b04090b0c0c01020f07060504051905071509150206060315 76
    0x212126489000e10106480da45892403d08645401c0001030010101d04000380719819407080b0f040f1487c420003171101040009a080b004902519060f00060b900b074001825a0f0152501c0b201503402407040321610710b01500c800301181c030303241c40c0d0107403801001030f104800a0f03040021059500d02180d003004003510b400e00326956603107407000050a0000058041c000c03662050f0540786001c118000350707580c0b850810280c142952107130309000702040d00d090020540d64420002514440711070922558001901c00e00012240401001110300e90b4942c400c0d05a0b000b440801c20006000d41030086842da2100040282a00e500a07a00c3e0b0140d40382a036408003003a0f0607284682c10082940703800e039481102c1e12859019204403d42c84c0c00c00740300007030342c0030803c046075101511603406001074504003072401425804180c0303c01c4001d0500d81c404241800442102d015034118a1110304144c50031940d01e080088102c06a4406400903801540800c4071500b01844902d410b40411038024020740307050300421 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 541200800 1250 541199550 541199563
    0x7030b070c06022b050f0a09030903080403050109031101020c0c0d081b1e0f03030615130b03100605030708070f11060c0310060c030203040905060105040b07150b060c0c0409020d0f060c02011d 84
    0x6901460300c88234010305050113104403401440e00300c565180c0da40d8880c01c0c05400f174510910105e00007810b14407600c9099070b040c4250380981030158040c00c140340000040040f030030b0b103041c030076200c01008008120b40e001295545181c62a2280081c003520b002c005600c1852000b03500c004c03505504400440c90750147c02008a962003041110301c5803a42000324000c01c41d502414030316240703803585c002000c03520800385405984114a91450049540e40b150401c882c28002074417040c0215417113101240d0340b20300031920320078590700c145040300640f0505400540348c0704080c0c41d05148140d0000900081c614415000009048a42841100c8070309558000f0b58a10441c4101010036541c5c0011900c2c9a20a404460083c22424805915904c0e141040200c000c901c0814040e1945041d030580a9801d0042c240c441e8048168060700061001e00240300c040c24040c00c0403030f40300d02c0d40c8520f00300050700c071000d0200c0c50b8042d81001079459075a04002e0300310760094082000442c0281c1d5130201005001404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 541202050 1250 541200800 541200811
    0xf0b06040216080714070902030105130b0d03030b0f0618040e0c060a080703061a090906040606091a0706020f040806060a05060f0d0609021b0613020307030b070c06022b050f 76
    0x419540c4d1160b814207008555550b014141d0314025140b00041c100364540140d030590f1402c441e120a0b0075a0b28070040d007140d13500001c1e6604040761415840c04a8041e0f070250680359005003c80840300759078800196a41e01028001815080243c420789e0103041c103104540020500e01c00a02c000074803080014590b007e002028010404441c2c001543e072441390b0007440c001c00740b85010815440034000e083d030b01600b180003c01d02590300070001070103500d0680140b070125041034485130040c1e42856101d0603243c046149488041d00108051000184148000c0c0102a40707402541e880b1401c2804041c10154043d20031440303800c002c0f100b0301c45540c4800803188440105017281d03a0303070b04030710a103080030f00182d0784540f0705107102140340d2040004000f04008101204015560260ba60a6903034402c0c035912080031350194840b141c180001212101001d8100c612400d02e00c2d002c10840c0d0b0f48030141e0740a01c03c125210b401c01c0041192901d5800700c0304c1c410350800d0f61b05220500c1c00164002c84441d00508 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 541203300 1250 541202050 541202063
    0x203010e0402130b0d11011206050a09091407031a010920030a1b0f0306050d0c0506090a180c030e063c100501260601030903030f090f0b06040216 64
    0x3a00c641003d40794011162114040c01c9240f000788603090640e2840702c07990555004ca0070712611810896404c1c41106c094800003801c0112540c20268000c00401d0714440494035085c000c0e2040340921802c0003048000d501c03c01600400000c035090052600d4010b9006000385801c20100511903180c020710b40490425200c07955441c0c3d9209207401018044115894800c6100c0d03811075111241d02c40c0c60200c40e03501c16117050210940d544148920340340480d50207003075000c920005110925000b0010501c81400601400909446503000c01c1d42007159245100e00580e1400c02c140c1c41c3c4d4143c01040c503000211009001d0900e005441130325590301140c500714030300c19100d191284c100c10310940d00b101002e0f1412409014074000c04030002100325402035130b0114604e1030005032181a942e245510701c1041c1d0b03ca010b020f0701d952005501400c0c20340c0c0101c043c90f4540040d00d505000700c1c451850028042c00303843c1c0c0d002c81d290500020a80780540140c1c080d900401002c0820340080d040381d0221548030a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 541204550 1250 541203300 541203319
    0x409050115081b16021003050601030c0e090408070305090a090c02010605040c08060d05030f0a050301030c0b0405030d0809070302040906090323070201050915030f091603031b05010b030d02031305040203010e0402 93
    0x1540e84d142c0440d00c1c18002e40c0284e003103004804140c0c0c9540030900c9000d0a803410020114440c90540e01c02e103100d0b6100358868030801c001400500d101015285480c4282030060801d40c1a800058a03440d81342c0011409a83c1c80503040e001315824000e43c00101000e440810214030004002420381500408040c042d56803501e801080000c208125925494a2190103844002c8400001c040b0782c400e21060307403181a468008111560780c501181c0c105c41c2e00030300404110180d0341007900d50540c0184210005d00982500102580b030b14011300006901c00d000014011300c0514000d0014008000c0307100455020923400c0940b6603507041100d800f10780900f000b9840314050000070701d00009051041598100204c00d00483d040e00c24480d0303000300d14050640700b017410a5140c2258040c40c92002900141000350b112040302c11a00c1d061032814003c4002192120004000c2490041351110940050344001015119400c00075030b660701a10b000c40d01545107514140000c0d0301004040d201900c2425400e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 541205800 1250 541204550 541204567
    0x506090a05060d09050f0304240c0b0c0a02010e061911130305030714010e0a021c0b070f0e0d0803070e01350703050f04080309120409050115081b 64
    0x1a140341008040c01803400d80e60320000c0d5018405458000c00444041c8600680843c80c00c1c0040706580030ba501c00104030000301071a100000c21402d010340303088140b0030f00608990218000100b160320401020352844d5541d040c400000b0f085600808004070076400000c148044180d40c0305c00491070006001c1d0100351609012412a614800d085208100002c05900002000760110207407103604d0084010020000070000c0440c281d030001d00c0c0000c140d401c541d41ca4001494505404290003044d40002d407600c2c01c444e500c3c0384140b6000d56800b0042a620325039a4850f1b0752100004a0510307042c1c0710f030700803207080f642c071f113403040c000a0640414020f00b118903014a0348034031034080355400241c680380c4e509a111106034054490f02c3c406c1080d00b59034900000c0c142c9029000f40b0780507542039040e141866881d525159619000501805c075503010300b04002e0104441701004d80050041d5440000e01945001403c4a40f240302c9003441040c8402d0301c04115451703640da048114691496220075694907101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 541207050 1250 541205800 541205809
    0x608090705041509020c0703030f230703030b040905150c0901141818061011030a0c050c030a03110705040e0d03020d020405090f06010306080c031b0609030f030319050c0301050609 79
    0x44d4200f9420f4600c08111a9840e200019051085074003d4864184110040700300701c0c0c001516443c0007046408514a4180c0f41889000070321441d4003070700d800201100000001401d036404803406803000d03841001e00c4009030b07942038000d541020800c00c580b4508204c910028207015a0382d102c46201548c0030410324003078105580380c2d16608400601b05540c00b200880c0c800d501110070740e2250b008841010710b1088850183d00104142e45804d001075040441440040721907445e07481040300d090151019880c0303940c03401c11049240e03e10076105d103041c00051038180c528108040c1c0c09103214904101a203041518041118203600c101441c000d0381d5030090310101c074060f12880c2d10080e08403284504200d00c1c030122403c101d0180a00b42e8050280d0b40e640c0c4a92982c40d201b07071303400d141d264211666011301e030401105a042132140103058142000c56680000c0d08122440030140321382d0700000108030540d4800e64214014000d1460100080c0c01c2024050010340014040c00340641d00001d8001036507901d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 541208300 1250 541207050 541207091
    0x18120c1a0d380d0c030c0807062d091a120f1003170705060a0e010b011706040c0c050a03051902030304110d020d062f04081002130b030f0f01060809070504 68
    0x10052a0b0032881a9a1b183c5440014641d11a004d01c9018100c2c000c01c00d107128100c9104c804202c0c46072803807500440448403560034400340e02c07036050000380180043c403025000440e001c0740008000346916841c0310804104246c900401f003d098508120805c40c20400c0a90100107583e000300c0d2080c084000401207010300e20030008049c00d1442103100304407004003690070807519001404020321103805104015110780b21540410030019113110001800c070304055002001b00c0000c0d15042c0e040c103070561280c0381002d80020303050b80041e40000b40400000d68120101c130125009100851071468942c8407125903030301c80d00307196100700c0a0342820810b560310225901c202640083d81001100180d03095010615500ca41514030034442c003483c110940044015581200c2c2d00c880541005206000c4460081d403000c024001d10714946500803845501c1e0340050f510404148084c2d010034140003d00201001c0140c2c055001c02000404008a42e000851003c007110710945011a981c06080780545c884003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 541209550 1250 541208300 541208303
    0x1215010203160b0a0b0d03080a1a060c07030203060c03040f03051c181502180409021903060902130b0d0201030507091706011518120c1a0d380d 63
    0x199070b0306240c28031510210450046a40003000c002072a12030013070001605a0000c0039010440b4580016541c4074942c2141a40d02046038000883e0003a681c0050882c0e0021000407030b40c3d510a80003130045041c00c00c407854102802c200383c181141342c150b98003401441c80b00c0004003085004940c022403801600c44a500c203114040d81841030080e656844925174441d020182c8021013416000f091041251080b20102a6080446c07406410320806120142510100c2260003400c3d90007020008446084007a002e144122400310385a500d50040010350050001d48421562600c0e001d848950b40d400c0007800f00c00d60a080c089101c0e03454000a5030328000b00da0001d0000201c0307400c078508100d00815044c0c103a40613880c0c12868a40e0461084484400c80c0b410206034440d599801c1c4188142d0360b0390085401e00c10081030a445890301c1030f0880040c281d442c5444011408a900c902036403041c0038a81c182541c104243d103504a81d8010403031207036a040213805800714032001d0041c1d251128045603040c107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 541210800 1250 541209550 541209577
    0x80715020906190207150e01030b1c140601090b090a150504060b09090a020c0a080c070b16112407140102070305030403091e03021002010e0f0f010e031215010203 71
    0x140c1114140040f01401d01c050240180225407000c2003403100c2e40d0312002e030f1401903544d44c1410041c1c0720065008002091100d9031060703804507503034848880f403013900401c1c41c4110b407002180c600280815140c030006800c200c40503810900d1464860300c881c0c2a8a40c4240000004106241c035183c00f101039041c0781d04502e40082c10028046440c05941004180009080d0741070103103a520420410b04034040d100415003290000c201c0c2e14082590400600135500c119420f44d00c8444c1d44d4251790800e036014011082c5850041c90008052042c0702108007411681901d4040c000f443c180300c022400c181d001580f2450304d401040030300910071510a016242058800215520b0100e410054060340049904030b00060001c1c42c04142c0301c1d945090600034040e0180200d0095003503038208000080d408200c24115942e030244e86130f90f5002044141d5084102001070f04981c58030440090a40300f846050441682c8104000003a41030440c41060788140304000d240342094500004031304500c101070054071031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 541212050 1250 541210800 541210807
    0x12181c12060303091a0301150809030d090606050111060f0610020106030804081b03030a0e100507020913150b060d090302010e0d08161403070f110f06010f060804080715020906 77
    0x100368001c4007100541720911600780c1995161141120710b84030174025022125001d0300d0803140d42c0c0c01000b201e03400c0400202034900340180202410111074020009541d801d8503440704214550b08510300120110b403440180c4501d142000307440501001c05400a4003411068501d00c4036a4800c1d40b02001855002030003d030f8071503a50b407282d0360b030740c2e282c82c0343e401d400350880403002c3e0500e8000111815162140c882c010206415020011508004580c99050003800c00c80c04c40141d45801140d40314a80400c520310004078141072110f00703400348004481c5030619101e01d026a80d0749010544074000404403000c01c802c40c452030202c4c0540340b148a0707031243e0304c100562155850740000050f03100c2c1e145090040300e0022905811611501000400c4048003810004100003912074008203161805505190042074546001d40380380c03000401091a01e6000900148090590b10610308010314051401100ca41842d485442c00da00c940f00000b0007220001543c500160342d1901a05c080c400000e100703544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 541213300 1250 541212050 541212053
    0x606190e04141f050a03030507060b0d0609060b0406050d020d061b090303030e06040f0305070f0c091a04060302090f09161d060301090308190f050c12181c120603 71
    0x295040d501c8140c1c48050106000d0f0100c1011400000c4840003800708020303d2070340d10103551a0340b08003015925951100c0021041d0307180d56480000d814401d5500248030642c030b0400b1070443e40c00b90001441242032220030049903072800146511241c0454403120342004c5031401c140102900682071515040700030044408a07008520142124025203060026001d50942562a18800c907001454002e048420502091046020740b0103180300d40384114140e5003a807101d02c81d25115a00000c0107079102c00c03440e0784d40321060007003c1a5074801e840900c40b06003103a00007500703900010058048403000c1400030340b100008209140e82d200182c0c0c00840c1c100e403600a81d8408902e006081c044580c11100403682c90300301407149288007900740d034605c0342d1500c1c0c4882000004072498141c0901984880e800030390a21a4442c0500403503407223640301d50341e082044841c003100100400b896061400c08030104296030012440d80002c40410325a41420902400c0c20f560740120003424140141c41c0c010f0100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 541214550 1250 541213300 541213331
    0x150f03100501242003070c0b03180f0d0e031507090303090b18130906060902130608071403070917010603050c040903090e0c1c1e02030606190e04 64
    0x60507580b0811a025143d6a003125800004407820300c8200010118800080641540c40c1002c403040005001c2d00d281450341c4c1c943d101d03441070942003003058040010034040d01d45001c05c91644601840340240c607a080300b00340d046440304d13203580b07100017400b00d080a0300c2c059a40c1401211100c10030949202d0302d82c20903400c000d108801c140411000700e10b10141c08640c4511100c00c2c0c07000c69030082a08103040c000d1300140011048491900b40c4240d454811340400100280070715405132440c84001a25010b04054048071002a54850024000c0c0c400c203011149900110220a0301140c15030b1a07504d03214103000700c50903072840e0302c59403a4103a0358020b800180f07010740089040b40c4c01a012140c000000004100c2184c0340c10300024041610001c080001403c1060f00d00c5d404214054901d0506e450a0804114002c0c000385600d0040d650b455030003000c0ca880381c183c450280049004506614001000c18440d100b42c1036107014620100d0841280303548141c1042100d000c0160050003903909503030411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 541215800 1250 541214550 541214561
    0xc060207030308132001140a0305040c0605030408270a08030a020f01050c04120c0801092d020105030c09040e030c03130524030703020915040509070c0209150f0310 72
    0x84002a00320030118459000600401c601580c000c220b440d0824480c80c81c04010301c5017080c40505021440491044143d0828042c02100704951008030300f0b031800d0b240100d00c49129800050502c50700344288004100c005054480b003c2c44809590801e1540321002c0d208411804a529409840c43c00003041186010014010b4524550210307002c600e40d51018a0984504551000481c00305100c10401031402c3c0011011840c0075425018030103403610912800c0d2000c81d2400e0311101021000f214a03003200303500b94400e00308a0b045250000303605070700007400361001408080200300d011460714041e075150707440758031032405000441e82d031041050f052a880e41c102c1e114140c1424600540020b080c20080070020080440d031703100200c0303a950010100c00701e4001801d003004065080c001504030f926000d941004d044c800340c20440c1c841e441c003010880c140000620043c10840100100c10040c1c0b105405c0d5a001a040300f4484800d5500038046040b50b01c504c0c3c22103500d440780c624181f80e0300d116035108 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 541217050 1250 541215800 541215803
    0x30a090f050312160501020903120d2016060b18010609080c01020d0c1b03030305061e06190c14011512150b03150c040302150a17190e060906072105130c06020703 71
    0x502075602c440c49180b9040420106401090108100110b05681000601c00d00dc51050400141160082004c61260004400f03a207086501650051140c1134110084a0060001000815596916800003500c0341000907403213051149075010403042059511300400507140404c07480c3e07111035480c20010003a0409031141030040104c19010089915001395280003100054405850030406800f98240c0c43d24a00c000b104000d802041240000c0721b0148900d682c90080d00080340007120006194440c00c0141e0002c01026100220240016400b803481d907041c03030078030741c0008803141248017081c100070040984165004072082084017440d00180a042603c1c0203480c40c00d114019845e00712490b200e44507480e03020070072007000030000140d0603181652200240700c10b4040b452045c1440f0060783c016510411142c0c203c1010000c030380404100e015130002c0340307207480c48012544500040384c18619106c107194490319140059400c4090460388941964400a0700844036500d540c003c1d00c41505010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 541218300 1250 541217050 541217077
    0xd020c040e010b0d020f060412121b021f0e040204090f0606050703050d090501140a02030601110705101103161202010c08010f090f0905030a090f05031216050102090312 74
    0xd21203401c0c03014441c3d01d10a00300940004d200c18401e808105513100d800099a602000070040482d4000c544038102568502c6240030780c0c401c0400c403101402c45541c40709586d0020543c12003030b4000d40c2d18500744c02d1000c0315505400e103d4250005080b80c1600402400c1030b000b0b4000200012240c040e9480480c0d849007000d410070011f6165102103c0300c0c81040c0d00a00000e00c20700c11b9491002d096444120200c1c812400022007008001c038010f01890b040714030b00b11650b03000c000c200303003560056200010314005030041d0150b142048001425600031051010402801800140e00303140c04104440c2008011036072240551001e140c2000c01c008841c0c00c981c015428807108111a5026900c178a044c0d03800101094550b40c00d180c01100100f1400324410f203c0c1c1c0c0c1700c200d00d0020507014002814007080c00e0b82c5007042a414201e103541d59405030f40c480c071701a900980590159000e100e09464100090300c0030f114504695090080c007a0003000000340d898010046188809040d200041c00d00140448 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 541219550 1250 541218300 541218311
    0xc0e0c07051b030304030311010905070303030605030c0108060306070c0f0f06022203030c0f02180f180c0315251d030c0a03020415030b0a090314030103030f05030c07050d020c04 78
    0x1108032902c2c1c0050301c245600365109100602c0044d005801c865442100d0000000e00c2503400d0320b900d450074a10340e0056003c03d0b40c030b8106100a041c203000101c103c560030b090280d482c0c00c114002c02d503a20b00c010b080e08200b00c0c1e070085110400140144610401e5009550119001040c3c2410b10007507019800d10060070380c005040511001a084050003102c0d051307160301c25600001e448240d1400200a000c99125411144038400351201d05a414041c2030310900760441407600c1c5071600c100d00440d00801c2c015510494944080d0740d00081d840244403c802d90001c130644a0340030030720007c01440e240e0b00e0b900c29800e242150041d0321102c88402e2020030030080c0c40c26101202450307142e8490500030f0742c01c60f2a820080c000350500342c00940007603842c0e083d0380c098169291a141c01c0000305480c2107015980303d20313082d000e040e4482a11b400d11049404954615403441e030b800b4102001d4101a0340620001000141e1401040402d64003025040010350b00300c13007000c0c0300007911261594540c502c141d00c1e00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 541220800 1250 541219550 541219573
    0x161e08041d0f090604020423070c030305150f060702030c09150a060c21050d062d0b041a070f03031e020a0905040b06130807091103070e010305040c0e0c0705 69
    0x85850003010001c01600585c0c0300c540030301016006188281e4070301c00440d41c45180d610441e4401c28413880740b5541c1c62000c0c0d030240c038001381540c00141c110038499100b0030300104150745110640225240403503c096403030b03840380301003410b00f40612171050b8410068801c00c01840301d01007044244040c08c0307410040381e60302c5031000e8541402c43c410181030b0022090744414101c0d802d540c20310040c5040d042c82804c0c410b28002c15000d4942507045904500c16004686000e4103214482024480e4020021360400342484545042c0b80038601c01d460390b81c40107107584003090905001300c0e404190440c040803e010000c0c20b0160282585640c05c08412480b52907080c00d81c00740f4402c0e5041030680f40e45002240c0d18200c200000b41c41c8042c1c41c2540300c6402c03c12500040d01002c02d0b00010303c0b0742000303000c40c9454080140d0444598050f04082c1200c208104030840d0b500890004034143c3c2400c4c002640d4441781002c109202c0d664004450755100e0303009110030401003030041c00425100da0212140038088 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 541222050 1250 541220800 541220821
    0x30f10120809010518090705040305070b030403020d05071a010909020f0102010c020d030902031e06220309050d2303090316050f0108250513080102161e08041d 70
    0x300000d0245181441400072961090300100b0405500c02ca51a640482c0f890000d01c0c07000c1c06480c0398021880008013001084028020803000704030405444d07007149072503203000e52030302002140380303042010028410007041000380c1e044103105107591f4248510340c2c41e164907400031f0000980070380c03040442000c0788101d5032050081440b0b40c1447d6001c2c3c59640c0c0c4840c42600a03281c030fa90200c0c1e05004d0728040150304003200d0701400031340840070700a103145e06110a4840c54807480001c440f0b2078200210241d00400d8011031030350210380c0240c491689550a906156580080800d00100d1001c00101000c42424001000e0112002c04400740d6a1031564000d800c640b40b017107807040f9074002c24400d8808000358020401580d00050502110321454600851045200300340ca045902082d40441c030750b450440b030b00384030302c0203844060003c520b0a801000c1c0d0791a46d01d408840200312140250052040e03246090450ba402a4400740d51a1a1511400084040425825035840b401075840003da0f80b07104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 541223300 1250 541222050 541222079
    0x11205060114030a060b0f0403020a120f110a08030a2115090c0c2a0506030f2a04060509130203010617092d10150b071403030f10 57
    0x405031150036410700c21000d0850036400007003582c0301301030b40c031500011842600c1004005040c0c04208580d900d0b400e510402078034036050b40120902c0c03500302c6582d8001418103c10030412a07001690209840b00b2070f4000340e00d845203500180041c3c04007040c4408040c1c0c22092000040311001c02c0d100c0b0710100000b0070030171180c2030300b41c813002c0e0410343300200460405030b40302e04003c2c201407404403285074250312100013500d500c2c1c60068039406400f20415040195050301c40c007403c0200c81e00c40c40c50620b61003140c5242e4010b04003039440c00d02581c080d00c1c1e90315802c15440001450443d5192926a0b40001030000e801014407140110340c03115424411481c14400c03203040c6c0c1ea05440b00006400200c4a00804160051421410b0702c614044000180462909401c8083c1c980c0c02203802140b5054915003001c40500d0b02005050070007125201d4100703070f01c0014080e5400d100440380c4404142c04e02000c0041c1c514011f40140c04000248800007402042e403034400c0030610f8528101e1691038503000e03603206 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 541224550 1250 541223300 541223311
    0xc170c0102120f1608040e0919030c061a0405340c03080714040e0a0b011818020d0f0c110303060108040f050c030106081020040512070f030c0302011205 67
    0xb2040000440351440c08000e4103d07008440072140100c100d50703079601c1c06503003da040414103c4100301000840c0f00208001234404902801e0340c0700000c110f0ba4042c180e51580b100091945071658001000b0300c0f00841000388088008000340100e0920f64442c425050b09800d569921104050200d1110054491005c1c800002c56850340004040c0b074908555444001d1701d6030341008030754891591a503911201410240c4031261174000d40e4205540e14104641070106058103020b04050740341015a2544240011110500100d2034101c9114110078002c1c8900c42c00d90204500c0d20340904451700c11940108154640c9407110a07560100ca114150349010071030f0901d000459120001300080c483c041d801c0e501e00e21610031503410300540c80c0001d0035a001604001c821b03906c0440700c461402054054040004014410005990000888042644110b000b058000c4200b000c0740d542200c0100301c10720040000601c00c03103219450b441c2844240001c0e220a0717001a622040c0e084100c112807044134000c0c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 541225800 1250 541224550 541224583
    0xb0912030426040b040801061422020a0302090301050103110f011d061602090406090c0b04030203061b070b130c0605030606091302190917150f130c170c0102 69
    0x540044010940c065003062a0608896060100040135034482c009040a08403800c00481c04500700395420314a102e610302039604c2001166a2155024003012008048103c5000e026035100440380b0264043e00c100c410064140d0f1070100000140420040c00b800da2441c00c032203213906003000700c0c01150b900e000c804d42c24099143c2c0b41d500355030600e0010024842ea4503140300e140070b840304680014003004c001b158103031401c9440c1d00c2118100034000c035407040508180140c650409003550003280e650540102064a10881100b11455520651040d10851a03101c0500061480c2104c0184803000360480102c41800d00901d0200d0240d01170300650744140c5000c6c040c0c1c0e0030851203904000011a800c07000d21400c070303420003130580007030180c01414028004945409880701d00d00700d200c1345007604158036001e840d0820312030201662080c80050f80c0000c408070345a141d030380b165401e80e450300d0280403005003070340ca400c1400a030360034840e80520500301c840000d548542c07444600590b10344440c100842000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 541227050 1250 541225800 541225823
    0x5240109090318140f011112070204060f15080702030405090403050a11010606091d0907170c03100b1906050405011101020903030304060e07080109081818040b09120304 74
    0x100090340c000c03001d19009240a407a0012254000851000075030090a52018240207504603410544203140050900b0320704500c41022004880da19520040c00960402c03800183c80b0040d0b54031600f00001401c0140d6055104603660f070f49a6504455445622001c25071603800182d1250004c02561304440010300950140e0380c50340e900725940c0c0e21010f20b071014403c0c1003001130742c000024803880000d403203d0788a080b102401e0600340400320b800c182e00140030b9840001008110400841c03007600b199000740b0284000044002405d04010a46000039018800c0318420700420038590050703071000b40166880319a226116a441d40000e40902540000c43c204210400ca25407080d003e03041ca41c80000c00040c20403540d840000c1c150381c0240d80607900c0e0ba8907964416070552044c041a0000d1158400803c40015241d40d80d8004c4d0240c080c200f4404020440402000d4460a1122010700052421a0741500e0540750906201a040d034501d4440d10901c0d1480c00301e280c09a0889020f540c011220f5640d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 541228300 1250 541227050 541227059
    0x110d0309030c0f050d0207090e0304060e010903081206181b0901050d090b040506070f020d0e0a18051503030711061605030d0e1204060e0f01200604052401 68
    0x68004080110204400c014440b4046581100508a0b10744140080c060801070325000915100c5c0603048461603d00d003e000500c0c0d00030000807102154420300b00f1344400061100103a481071040d5101074460b074030000d00c019106202d1042d0601c580003c848030004482124000d428260003119030b4042089080300901c100462400600740224051508030320300b03c02d0359104002d40b04034180845031403540340c048c401040403c1c0030090740910300340707414030b50f8003150300c2d0080d55112240315000c00e002d404041241940c403201c24410143c100c0410389030401c81c200032070300c0050200304ca09a111a030003034184942c51a021045402250700b1802c065880200d030410024a54403109480c4904501907289000043c0c2c113001404144040e040c0c00184d02c000044c1c113606001e62900002d04010080105000c49a040f000c40004280c00b47c80521805082400595400c00025400140c020040356030714039000c2d00041c028410f40c4290140d82c0905400c003241c5100440c6410503200003003400c0c00521 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 541229550 1250 541228300 541228307
    0x9060f1f0f1e120f060b0d0b040c1b0c0e280203010506040614040e130c0602070b1611040f2a0c020607030c08210612060a1e0e07080607110d 62
    0x10702d80c072403d1100040c078400b81c8038000304861455004001001002c61006080c85d078600c01c1060004003614140624605040002c201c0403560008940300102005504144041020a2030213003007110800c41e110700f003018030084440c901c800407042c0740d101404c0641c076540d810b0007a64102da602810050030582855001c0d00c00d25035032800e00025031010301000409102c0c0d011030398060303d0444c0d0764940c409040e05200350803280300d400c01c40955002d00740030450042148126010344140300b00010900342140b4005854070150b180b49a409401c01c04020702e0600b1550002d01c4009002003c100301c41e4081c401c950400b5810b40c6101c0100e480c1b01002c1d03025040150042603182d203c0d142210000390140c0d40c5a003076411120980c2826000312000014000e500000d99800080444051842325558441c4a681b444010191010b003500d42c01c0120007002d9030880e54140e000c5015042c0240d4408503a400c0d40c0d20307107920035210f45120f48804036000302d000b8000608151503200280250f05481035055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 541230800 1250 541229550 541229567
    0xd0b19181e0b160210090605010f0e1006030515030a030509031e0d14161518020d02010e0102070f1d0708130206070f08161709060909060f1f0f1e 64
    0xe00b0b6003d05420400007017a20b2051a007440d114038000103e550500a004071002120b0b002011060780324028404980d15801150044502c0c0b8070700451a80e403001d00083c3c02103100301400e60113205100c03c220415820078003400c40c07208140c0440b48034900e06c0116000001d40034400740c90300e0304203080d0750291511900c001d0f04098803503041d8901c0d02c240103440d032403581c3c1514416140180e503066000044032141c003400c0e51980408410b8004404a900081c540000c0024001d061240b180d644000366402403058070004c01100b000e085105a40d181826445034440c3d00c4995101c0090300000c00791400350401314005c5024880d0780b5440032082d824010315901c10501500e400103100304800000300150010b140f00c1100c0b10034840b07205058030b070032202d0501c0d04017000348110007480681004e844070b100ba150307841011155010300352584008101e07614280781c580341c1c0101d285d02d40e942d5000d46001d007008005005070b0301c440f049000a4411200e415000c40000da2015400c3c80c0c0d002e800344640c100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 541232050 1250 541230800 541230841
    0xc06090448080f06180708101703120630010b031203010306020c03040e07170f06010e04050604180b070e01020c150901030b040c12060e060d0b19181e0b 67
    0xd90405c49421000e036800c0c034084508000084e102c804010301d01030035022080080401e85440801d607012500c44035203900814802103154160b00340002c503603076101590642d84126a200d22004c00e90078100d103940700c807034034403c41c03d6075800c000c2c51400e1400c0008442076078500d05d0010701d08590959a0b1240039500100ea04040d81c8030900c0049100d65040680c1801500305072140110200314960182d08604000c11220200c50000c00300001660400031083d80100100d4001520790340c2e030000100180041000192402940030384802045030f002c4510780212801c1d05d9a6517014010401266150240c0414580080c8003c030003000d01d2101001800d0f08420504000c1151b6044501040c21654200200e000049a0304c9100b2000141482003d018008004414000340349c00400700c0c11039641c84074000c2209a603500001c2400c50307a04c008012030303100034034207001503003c0803036149d00b901c050380c0141d60310904001d01d404031001c1c285803600c015174400b40c91b003070070368a03072400616500d541200d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 541233300 1250 541232050 541232059
    0x210d1103040c1203020f150106080702071a0904060305120c0f01020304150506040e0a06151211010c230703060c0305090c0f0105071b0603060510020c06090448080f06 73
    0xc51403030b1546c0034409882d03c8483c0e0403480709150b1600d00018035080300030704103034155000340100707018840da100c402420a41042c1d0003d655040c1a2011030f0040505900c094168040c88210300702c0030700c003c0010013643c6800b40840d051030340040c04030790803440b00b90307002040c2181ca0780050340d5454654000d1903205000520000e0110440200e1500786000940c2c1103405683d10160700742c030700300c5082e01c54015007584801c842c145410790350784400120210417150f06000b5107400100411031400840c00c448800000c00342100700049c888590f4480d180c0c0422541107091001c000f01041c802d01c1020704c40e803001720080521540880920210140010205042060400820003c500c018001c0a106000640007001c09803400070024100c2c0e140d0f8000314480d4091000040341c1503800652900c10310003c071406990f452481000500a1010040b02121a400d07028007091102d1041c9003516094840040003c000b040507440c0c1402000e001000c602299450010030300380071b811071080d54011030161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 541234550 1250 541233300 541233313
    0x50402060f12041b0b1614030705160e040f0204110d09030519050304151a0409080306092203030b130203010314070f0303090b0a02210d1103040c120302 67
    0x514804940e40300c0c5081192156100c003d101c10803100d81c801104c51800c0c0c1c920b0655040c140071080302c25105104080306220a00d00504040c0641d629900b590982c601040f6a03071040e0a1410f40c2c1c44469024070b94180300c6103010006116a40000e20354451075000b1056002030946900b0070004020381c500c10f0700342400501041c2c051014034840c006800307000e510340e41e840c1c1c0030442a400b55a82d0203a100010408140140702c0080c0c043d04007805560348504001c01c108a14641020712801c01204943e840b605110812051000c240c000318000c4030b05503171450160740d440d040030041440003559880031100204004000c05d10941c070a9000a00c01040b5507120004440c1850a0340c100b030b00141e84c1c8210400e11021160b1040041000070310440e030204004030b1654a015040d03402070301c40c1d5840e0141c0010a410300f030b8428032020340d0301d1703100d406001107242120311015041c0d0060300c640c4001c5803074484a855440303410300503a0710860340150066502814494211104070080c00704034294803c54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 541235800 1250 541234550 541234567
    0x1602120a031805160e0907050d031d06070b0403020d09080c06070809060c031c0b010f1b1208090c011403010911040b03150f060a020a02190b1308010b09010e0103030305040206 77
    0x38042c0400d1100d9807001d804105040081729528898040d00da840c0031740c00101c04004503101c9040c0c079140b4541500b0048002c0c000c0b01d01c190300c52a5814505588190005044800c1141003208070740214041d80c00c40300c0000340e0445c15074031081d140c02110300036886902c40d0384503454448001d01c43e0910602c80d050501c070b080d8010030038582000558a03503d81010030400c0c4002d030114803580c07450348004e0302481084465000680780a002c2c1008504018140440c20840c81e166600d2880f0380342c0c0300f12022402800424000c04030b0b48240d0b0f104a142c01641c84a901c990710810700803080c0c100a034091071459113032001000c02445524610b040802c02844000740d4482450003841c840c3c40c000795000340381e180c01c0040103100350b0741042d402d100e0f100c20300c1a040500d40c0003541403086035068807107400e104000c202e100b0b401101c1d58003400d03809400080b01c10300c1c42445070001080310103401c0244211311040e010024070102c24040c1c0d9401d07000c00b000410100e44650005d83c0c0043c0040d10781031401702c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 541237050 1250 541235800 541235803
    0x7300203010807080607090b030a2a0905190501050f13050612101d040f03110f01060f0e0c0307080705040b0a05030601090503010606050909060a0f0e1602120a031805 73
    0x241d20144054220020070080c80310b05200d007070341c48101b51a0815156081005c5d0800c0f5001c0900b040c2c1d000ca50751072019014042e8105400b255400400110003914031400300202141000d0050b00e000c0d40c0f10540c1c14034001d00850b000d0b025144140c413418144a65030303030211f60b1074020b100d521580300c50411000855480d102d00070201e00c050305130003500603c1d00000e0001c04e03c507950b01410030440100d103515444034400700040c5e0001d91180c1c6000c1100000c3c107081b20301344102032041c0d10302c1c02008a40e0107030110540c0803404072a41820300503002c03a0345801c44003c2c0c80c07044444c804030201c200001044c00348208a000d0b407200c81410101d007081d48a00c0c00403a50340141c00c2202c04500d001040c01540d60300700a2150080104400a000d51405c1240003007a502403260f82070f020ba107c000110300a540c0300342c20302c0d0241c6050401d0840055899214800d107a41c2030300c81d11460403540c1034270107629101284483c52420104286071520201e064214014000f200d136020302d51034140c401d080003480 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 541238300 1250 541237050 541237057
    0x2a18040305070c080604170703120510030302010605030a1101080414010c05220b180604030501050901020307120b03150405031c02030a0c05041508130b1f0e073002 72
    0x981d99039856600301e00d0721203040350141e0442c1200750301c00d10421001036140182c0075220074500b40c400b521030500d441c06981111170b8500800040d8188000c0040c000c19040d80032044902aa000340809581c85017410f072203450003080a0007040c0248038a51995000e100071a420034890599826240d07100c4070150b003190039601d040303070000f1070000310384841c00b1143c00e813680444076244107100314616005110040384142038041000c0b114034a400c4131076641e50025100119000002400b1038038042d80018002d502c1107500b500800d0a035031100307044e4440c0f44240e00e5490805002046049605485e482581d0001442110701c2c0c8410803003c1e6001c46500082c07110018800310150f228203080120406030b0304141080e9040000601040181d400c805d0301c03010200741541090005c50300d4185200702134007070095001d40b06582c1901440180d000d04151009072038211030242d4040c2d5261124090749a4007a40c400c0700003008005800340c07010320006101c04075442009070380c3c10b505220850710260303003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 541239550 1250 541238300 541238303
    0x71703030a050919120207080f010e011d07050108181902090c0c1209030703080406050706110921010b22060602032506020904050a0f0e2a1804 63
    0x400110900a10010038098540c202c940303000500313100650403000b0320025003101c00141075040300c1919559618001d0100901400c10441643e007007802ea5142c0314042e086032880c0070895803a00521b4003c00340641f004072105031050001c2c09a1910385401160419406081006800c0881c400858194402c0040410600c12140e03155012943e6004000c0c488000518980d4a084200040e0003122404a81c2060101c1e142051585642070701c804280380610a4000910203032000402048a540002c0038250b000d21544050041140c0080801020b008902000380c01c8080c0e00c0c05c01506c0404010010700b000340c203400020b544149407000804900e1070350781c446010aa00e0000c6100f001d003d0207141c0142c5a180021490a19215204180078156017500d0601907000d0550b602084000d0b012105201c034003c0050002c0d0904215136001010384c150651402d6180c840718880309030000c10700b00c0202e10b14000f488a643d410411542c04101400211503000b0341794070090401440b00e2000601a0307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 541240800 1250 541239550 541239553
    0xc0c38040c0602010b0102071a0405030d08091b2b050d0f020f060106080613060f1401030f090503090d020d0b0403080402100801050f130f05040321020301031e050717 73
    0x341032a00340356100c040140c11110071641420088030b0a660005151022540304240301c4070040072212704c0e000140103075040241d0600407912400a417507485003080707002d81342e2070701580c1c005010181a08440305007800c00075080000701150030100046020414844000c82c80d074504580c500784c2d20181060000302a1201280202074070561540d8100100213480c0000001824154103000b4060182100241a20700c185050110407000b082c081e08507600034000740c210305444503102c40f803080c454030803241201d0010386025240328410130a4060f540000360031401841c40c05450805202001070118004d076000000c0c1c0a465000480e1340404034800c030300035078a09840d401d0a1040100030800d11120004001c5103c006122959420b8900542c0f40400c9034076203034031a50990140007034040c40c82c0c1400114a0b1008000c00d050b00305070141c000034941120101c52101c2d160500049000030302000d0320307041001c0c0035001d0509a4904d0b00c0501409801110500c40c0d0702c182d80b5000d030f00c8090401009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 541242050 1250 541240800 541240913
    0xf020307030f05090a061e02070b01151806051602060f03060406051009150309020d0321020f03010b090d020a24050a0807030f1509020c070602010c0c 66
    0x4035414440c5010b42c4000309003c0c407035420048901c60361004040d1025145540c0c0f145840098480d80c03a55070224004031000b035481e505903007042c22400c6c000340305132100a150504540d54540c031800c03140c09004074200b80d03511103070305004046603117801a0300c4041488070450303141e1015035500030250140d0306250704a1030362072401e40300380000d44113280d015a0242c040348189403244c1b0b4005228000b502e1241a1240f04510540340850103407440d181d010750030120b1402c07054140340d405007000910700045001680410801c100100c00c03480b8024449404500030300050000c0704400e001002480002401c0d94000b2083c0d07000107040c1c5000794454517418245111113030b00c00c1450008580e83c108103003880d80c20300a04070300260039800c001f444607007019901c0c402000d9101e02940a40040c000100c490078440751103a8860b0300951051031003000c907224150002600e24414003071100406840d98071103450310440c2e601d238803040e210048051b10a456020308010218404150329444001c0707100940278 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 541243300 1250 541242050 541242061
    0x414030f0106060c080a0903060e06060f19030311010914030703020c040c09030f0f140c030f190209040c0e0403120b032b02030403291e0412050d0f0203 67
    0x9000d461038606540d0381d04108080080540042c00c00e921aa04151039594485200e5000c440340801c58000815081c81c118074403514201c00140c903845440242c03404050090320804108103c540d42064420b200551901840028400c008032107540f4006000418020115903c5110f403011541044842c3d600c04030300b002c2031541c100004040314400b980d0401c420302036104010040c00c02c07800003502c640c2d030203480001040803000b1007004040d005807124605d60f520b41090380d103503d000441107111b48121030010299500215000c80c0b01e50480c000f4804111050703007844100c01004005a44585840c0400540d01100103010b62044d0300c00d41d144030609440d50000c0085401c01c1d810540281c0c060f401100700c040d00b94590440508803244210300011a0702c0c400c074510700c50740c0c0004000e8a8808200b0403288544026500c3c803001d8800403100300e03600c940342c1200c041c5034a90b461340e40031203c9c0081170100304100c00c581048182450000d28086603850f001c0b007074405000c8110b682c960f00104012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 541244550 1250 541243300 541243303
    0x6030a051f0f09020c0a20011107050306130807060504051606051303150b06180306090a030f080a0e03120f06030102070804030602090604180501060e0909060f0c0d02041403 76
    0x580c14800e200e00221080c102120000a0b00d2540601c0152541c001000714102c1c20030000301c9030503940500482d1200745010300550f90b09040c83c005c64003103040d440000040c954042070000503500b02400818070f560301c0c80340c00c0c11150100b10054894250030019040440c01900a541c0310b103004000512060b20040e01d6841c0e40c40d400e50000c41040014442501c0103901220640200c03500420f403c07003210504442d0f0801030089040c41c55100030000396110300000a40200d006100c000c5055030705545d00c1d900c880c0e8560140d031800a0000340d040c0c8409942d00e0242168a8101d1810000012211078004e21107285510160300ca10030101e0b010100304201548501c09917015138160000d40c101205030361400c60f14003460100420098000c101c210a0b40c94940a0714001d02a41c105500103498404002d40140350078061007001030741d144000e0f10141040c81c417042c001c040c01d000501460346d42c40c070b40c0f40280c0c43c05052103071800030401100f01003034a03500241020f03084040c405800050001d0425 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 541245800 1250 541244550 541244581
    0x519080f0c030f04030818030d0e1002040513020d14010608040c051f0305041502040b0703021002070c050d020d051c020c0a031a090c15220810020c0a0206030a05 71
    0x1e5400d1001c02c2004424041100c1594006038541000c003156140c11010038290762104d24080b2192001043c10196081107410081c110048075003035a16440121070320100341d226a005541d0044403540002192a1440d40140401c02c0320b4440041d1110710b902450000400c02c0c0d2000c00007400361003c1c44148005040305000405086482882c40d80741046411100a01d402c0300e541450340da500010144800e81c002c800e45003c0e10750701155296201c0c800c20702c0c0c5030030020f800c0d4011702c5100c2600f6100c100c1882110342854100013401401842c003c2004418180124120303000b04c40c40600c100028020004500c203001c44822042020021500003842c00c0c0d501042c6600c06c01a064040001c10b40100c90005690550120b10256999021209103000c46c400300094010076075100d0301000601c00c10140c41000300401c502e04444007051f41c82400c98400340110800380d04420620b400c8800d5a43c014247d2600750001c1e1034840a041d00010980d4004071882498982c9910405c220307881d0700841c1e0f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 541247050 1250 541245800 541245811
    0x30402010314100603090515010609170c030c1c05120d0c03020313060b150a030c0f0e03100e07120b040b0f0c03060d03110102130e0a02090303190519080f 68
    0xc404540b43c41410340c1584200c510610003410340c1d440d0000c05001087c8090035106c0308809140c0300c01d50f5241001442d0f04007130311541c0248083c3e00081d4900c0c44001c40d12150b80300c4002c004064a10300181048008061140d90807106411007501100040b418031075122101c46203c0c10907152001401914107880c016034645042520400402116440c002c2140f25140d4002000092800d8aa8040f924044445a130b075908100081501d00095034550001e40400c01d2565841990224506044d02c0e0537000704031581e4150440c03101c0400b000010350118900300c91036400c461801c0d0703450f120740000c1c0d0f4428009039006031600041200b07000d007900446030410940ba4100c46240b500b011001c01078040501003611502200c000f807420705118810302e03c0048003c2008554a40b0101c01200e4940514482d09402001c40ac0004503084128401d0741c28148000d00030314600901c2c00788105002c440b04240e407003445010300103498088100d0765190b5040d4680c1e151081242010620001660001007d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 541248300 1250 541247050 541247081
    0x9010c0c020303160503071502030402030c0109060507030f05040b0a05340803060607020603150f010e0a0905060d0f08130e1302090402040e0105090c0a090212220f080304020103 78
    0x1032500058800204590640c001c520090190001d10304c0d110742580f003110000b416451100d00718007190001eaa0046006030b20031421219103058410040d60034810910994002c0340d004d102002c08a030094072032105103100303403900a00d0315444011540380c0e5042201e00030b0000d07d021400344d40400c030703606034a11810700d220b402e0f80f501c03940104540e0701e80307040c00f8009100c8000400030649513240c4605031030400d540100055107d1508034544100c0c0315041050621807100c3c0d011014055000e03415214004c40c0c09007501c40310904000214000d0800945101d4000c9442072a40c000300701011003991001d8030828000703968a02c9458120300e000140c2d00300e0040720103140c060050180300105207040303855040d1010360300c942e1a400068010803525270540b096500340b2041200590f00400c0388810400c0440e950500288c03503a002200701d0142d4071480d155041800003152060300202000082c95080e405e00d107040310800d58950311120000001120482000710902003103603010f000d60b2510300369000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 541249550 1250 541248300 541248317
    0x5060f0d0f180c0812031902070b01030b0f0a0504120f020a12030e070902030907060c1a04080a020d0816030e1014070e0f0109030209100b070503030403080601080f070818011409010c 80
    0x45d4100d0306101c080d003240c08845420084982d0205243c0542d8096500f03d400c058081d03950303042020380824129060000d0203c0f601c00640c2450551298500507500801c0f200441200808151142100f0081c0201940300b20000e90b1f00003110700c90309a10940c01c40c1e40106110040c407900d41d150401e15000201e00d60700500410017a41d50000f024001c41e6000d11b060786040c516410142c04442510f140300f103229006600b0001842500d40080580e00541c0c1d080741c80c074034050130b01110103442c03e49007050903504040411941920981244120000c0304003503425940110a0301001c40c3e005080c1040c001402004000e10300d82c200024101f80c0d44240d030040078060701d4400003041c01c2040d01001b403041c8510070126082410b04803250307000c0c1240321280c1da81d44509090039556908200c0d402c40028100200044007948201702c06030140d608600c0d005410b844280c000d07520008020580600070440c12500f4210f560b090254040c0e03441008154400c40c14502007890a644541c5c9894040c0600780 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 541250800 1250 541249550 541249573
    0x608010612061d0307080f0f0a0f09050a030312200313030201151503050903041707030c0504140406090809040203010e04260a030b150703090f09050105060f0d0f180c08 74
    0x4021075145651100718180c1d1587c0d60110b0b0110340c083c00948490412001c1400391007207400070240480c104403904e03840805a80d9508002d0080c01601004000580141c25964017141d0b50300008812440c030170301d1546c0c08503844c84800c3c2c5904229185524644007d0050381819028880c0e0034182c45880c080403600d50a001050a00c050080e01460415646400280c0c1c0c24a05100383c50103020100600c20a100c000164a9a94030703c500054403041d0f04000006081c0c40c180c03162140812420b240e0441640d80d03516448010a50740d00242c400740400c000703107010b991300c901c01540a009040d06a00c218102418412011004000d21395420b0114a40444100e03802c0030a44002891503d8081100000320000c9146400b402045244d00300010882d081055000714821040d500109148083d540c1d0301c035030340f1341035840038402e03550820300030440705d50900c4c841d40041c04251b21000c8040358113030085003940c0881e004a080b0440c00c038034550450080040032885980182038081c000e00204105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 541252050 1250 541250800 541250803
    0xf0105101d190f09050c07031b0212030c0606030601030c031e080301240c150e0f03030103051e0d0e0405150a0b1c0b1e0d150b18041a0a0608010612061d 67
    0x507d540034080c414046100c4c0c18007a08840201c00300c560140140410020507000d02d40d8035001580143c0482c003d9070300050550400103582c40c122a0422407004d0440d1940e11002c90030110303101c0c842402003888081c4000710304040c00850080882a499100304000300a081c103410525100c80810022000300b1b500c08154500040b1241e140304d8080000c0039022000d42034600407003561022418000800000203104d404951810701c00031000c45c1e9020840340920031a00e48040004150100d6580c0c3c5407a00d8038141070340119440b8040d42c0ca441c203040c0c00300c000500381a0059001034000304000814038100a0000510700318100826001c3c00454850fa00241d10400e0041c07070500518401000d009850b039496800c020303065003115001401c1e400860014000d416941207150140e81d8003156044a0319880340e00b68800d603008014084500f43c01c00170540a500064031071080540c9816000c141c8003800c1c401c801c004d14801c0a04001044c00e440e0113429241c40d0201d442c1026100c03541551030410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 541253300 1250 541252050 541252057
    0x50a08010b280e090901060f060f05030c160f052d101107020d0b0f0c070510050406020f0a0801090e0a170a200f060f0105101d190f09050c 61
    0x1900b0140c04035000d050400b200c0340100c2c0d61a0b180d0203d00c00c0144001300a043d40210241c50301040f1890300303583c440105641c503d01c030321041c1d03000880800020700414a03050140603440069000d10b031090344103845441c0220b001c07400035070700f54022509141d00c44a20b040035420440c1005040550448410412a140ca0902110042c195155140318140380c100c1d104441c00c0e154003e07c8104500c10130300b0000f09400b021036054845132502720101e5410030521054501888c1c1c03000040c40074104a81002000c1c042c003401c00c4940d00e400f8048250701883c45d601401c1050f0103a40c034200c40d90314002d002d1042d5070800d955000a40c000e120701d8804207503401c4058100031902d912041e44d4100e02c1c101141d500030413803004103c0590b04100f0b860100c001003008101803105800f100c0079a203900170740800e0100f00307200300c4c1d0b8002c2c025a001902940142e0000100e40080e04000c05600d503030801051036000718841e6142542c00c0c04074280109031a09071403a01914015a0070403d62800d02c0c8041c1c040e10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 541254550 1250 541253300 541253347
    0x60e07020c010e03070509130b01120206030411121e010f0e03040b071b0e091005070e0d0206120f010f060801050102060601030b03030724202a0607050a08010b 70
    0x40748807079080c034540b8100241c1004000240087c190341c5045a8084030711003105c5411507807000303d44000100d4840b401414554142c0081001e4603548413035031000c1c401c0310811401500714500142500401400340403210701c1c129802100e00340164504a03490031107141d1003c0d01803591401c0c988421078000003040d5070581d607800c07010319651420b078100303080c0703c810300f0351203004c10941c50101045207004459201d0280f000842112a8103500209071030a42d0011110000001c041e401480c0c1d0758901042015421070025000a00e010b042005084e1600c000302e034010b4011010720f0040000c0e04aa07543d6000400b410b140145140d410a00002c3d10742c3c2c0c2c00fa00c01070406480320841e02844d5800c1c41110031813644110607401d0748000207001c00e2440c0301c2c0080103105030700d0035400306940010550070311106008443c010b031030010500000da0b10202c403c0705125480010b02c5410382c8107a820482c0901030350282e1242070301c6e070030040002804040d05030000c0401d00b400780400700740221001c01014400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 541255800 1250 541254550 541254557
    0xe0a0503070b07030e0303070807200904051203060d02030601080109050f12041e05120a0c05040b0607080c190f0b01061407111f0c0507050a0803030c0306010207031a0a060e07020c01 80
    0x284090b85c0081d2850080000c090b000240000300e101c10460340a1b8075940481c0003019544001d101c0100304143d08a0484000d00349400c4188002240e0ba40c150040d41c0c0003a008180792803c12098000c01d00c6c2c00300903006951169543d21140080c850204200a4166a01d2000300325a26a190903a000d500841c4a0900300982400da842103c1703041d10641800ba14028018402602280106c19503500c4035120a48105902c0c14003c0b60b1030401e8000c50b2a80034004d4803482c40c001d60307940c0d80e24655001c0c5800354070074029900783e651200c86c0404044181400b4079001c0d0140c1c40181000b6003440e0301a809801030000515450f06140c13244000c0e5200369412003c0760854800c130f5004a4400f0460301d10941c6800c2a00c80c0c0c10000d81e4102007400965030060003100d2401c2d41f940c0522264080500604a40e5807044c0009841141c0c21402103503c1001841a50701681c2d8a40d81d4500c1c4207180c1050a211400c5441000140b450600c10070000301034141703406107030342424200691212016440507042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 541257050 1250 541255800 541255817
    0x50706050c0d020a020309040605033903030a021005060303160b280c02010e060408121026010c030c1209061401080307020114040e15030a050d0e0a0503070b0703 71
    0x10008079400c0c1c1d440c42003605003c0d903844141410003500c0758014034806214918002000c01c0f00d080c0000e000c540c200c075042000401c81c10580c40f0404403000003a11440c0d00c60014404101618180b000c0d04039403c140d0020b1800e0741c2c0d40c901410981c0c4004000f280a03600c1441200728406d440729600810b150418032410054035105401c078080041100760150031184141980341c00c114690081c0a0360215500800080e41c643c5a2651110400c4e100a8940d62040c450390340b007111070f070032f142e0742148500707860270307040c664442161002a83c0c2400000780030389039081a158540c000c3c05070030b00c224001d1908001c91546c82402070319007011046411041940d41c020242000300c6544211076014200d8030f03507031842d1b079183c01840c1e0325449004200c1c0000c000c0c007518501111213600365006c8d41c00200041069955444032103004480e0040f400c0d60504c1100031490103da01807108004050081d914614411800c00a1103181d030f206500240c000c1e849071a041000c0c201c800180c911940d0305282107400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 541258300 1250 541257050 541257061
    0x90203090d03020c1606110f01021927060507140d080c0f07050609030a14030f0601030f180b010503010b03070303050d0e010e0f010516030204051c03120f1a090705070605 75
    0x240046103004015441008080071031800d0700300c18011f9001400744200e40c0e000b4419620a801e1703008425008842c4006c4001086445000710807512805c03903501c84880034450007045020213010b040c0e01810214000080c25803c0c002000c0e0907021507500180100036000c0140f000a050b8200182101507901004c254107800d55202c4c0c0807a48a950800704856450400e01c6a00751a9440905403901103400300108003801c2c3c6040c0142c074860441e00b5110f01683d40d4000041d405407071480d45640e16035940d0402540003032078061031413110318040d0100d80d19960400d0103040c00c44805682441c4280d020f08420000654080c0856107409103000c0701288040d892801076005d4100d22007422120701408800f00c0f9004415481a8805c04555125200e46a4000302c00d80c200d00c5940580e070b802030f1a240141c1148003290720740101c51442840d01301c20400710001c04d48121101d580c0c18840203030300c0d40da003488a03a40001d0b820848140880d0303504860700784018064043c0c492818000c0c58251034200140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 541259550 1250 541258300 541258303
    0x9030a02091f030317090a02010906050310230f0909030a0507021f0507050606041406091015020304090b040b0604150207180501061106040201081503160915090203090d03020c 77
    0x802d00040c001d54800b9003500ca180241030b0100da4190480202021800154410344c002003025000f034042e1189502c86007404801c50f03403503000510a03400407614107800100e25002d6003400d060241810740500040308420100036502d40e002594031b12515005050004010011044a030803030101c0c24070035175500651000c41c165050954510344a084a6100c85540d250000001c1520512072810384034207903601000c02040f40c10300d002c10710140c0d012000044d250700b4221032094002000c50000e82c189556810b450345290b01c00340c50800107030030125081101802600503e0f5540b28103c805110a411a40224225005510541c8813000103c10129181030082c08400090410100d41038590021120054060002071142c0b0b00003410b940c40421480c1804160036020b2a41655204ca0f66210a18090210204039a00c40c0c0e03d800790300001c00400c010000b0207001420407050115a80c1c1e4141186c1d518003000c2d40c45a0a8207004008100c000c0344c5c00305c0d22045118180c04e0068951154200e0706 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 541260800 1250 541259550 541259581
    0x30d0b011101093207060513080106030b0106113a0503060f040c050f03010b0712020609060f0601170f04030809030711090403121e0606030b030309040e0f0a151109030a0209 76
    0x341136000c0c002d00802c269910400400007060b5403078603032103000e580d02c060760f0891b11980f00180104e44403500501c03402d4851100082c6d01c1444008482004010040d400c3e902180250441410301c040c10380c56480702480c1c0d44a0311411020706200703082d85000760120b021000c04030103a5114542d00d050a03203c1d280580d0994844c82c0300601c1c0143c803584c445550300c84990080d40151803d8192103c1456014400903ca41c802c40c00100601000e40704c0d0350030406101c1c000307071400e41805044151542e400300b0030801c60784217007041c4441d1000e03800c00e818050040c25024081e40c202d42c008003c5080420740180360009100e40c29a680034040d5140d0a040b075101c0381140c02c40d1300141c01e0110710034141031421283c00310846d030031703604215060742c8030300036000c51340102c0348660142c01c2403104174110b2420703500c1408119041025120112000c00d070306c500705030380d442c82285e5207003a0000001c4803075881e10444c100c190b24000d15a04d03006285002a07590b004565000348610008030006a81c1c060140740d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 541262050 1250 541260800 541260893
    0x9150312070303061802091509030309010c02040605060a120c020604080703050c0115080a0203010e0d2106030b090a0309060503040b1906170a020108060a1a1803030d0b01110109 78
    0xb4a155644600c0100043c0d4400c0b4591031244295041c40c12500340d8223411200401030040003940340a03080c1c0010b54614004c0002682d005642d0ba8001a0589848001300b81078a8030b580e035800c00039440d1525100f121381080385002107510802c20007001404404c2103905454041c2851602c48512080783c84c09403400441d0400030a040c083c0000341c8110025514200310b05c214001c1c0701401c1912039040d40e0714504c0901100250914030141c0e0b00e00d8149070321a43e901550711001c0782d1b20381c1b651243c001c9002d01f5506220143d004110b80d6081c03651200602c0c000d0190751403c1803460400e61114400141d028000b40c3c0c001003e0100e0810380420756000c1c034014158200da0300400034941341d5442d15114a04016070118500000182083c90401800000c0d20107141031448916104907005d421a000060140d40794001000303001c2e801e0f03500b00042c02d00510710302c0c0045511071000000400b28880244503d105a040050728000541c85601e060300c42c0802603000c601100c0940c80710a03045914112 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 541263300 1250 541262050 541262069
    0x8070c080d050306013c140f1315080402060a0201150807090b090c07060e1f020406030b010f09050f031009150e030703051905120708060915031207030306 68
    0x90700e05802c18040d41c45031000f41ca55060b0000e03104c40424441052244144c0d101c1c40156004040106900c4050075048040c50301e5503140c0800540e001d225031080f240381c1a00c49001c52000c60304a1403554420107400e08c035810000710503003018064960302c00908001e11a810100300f40740858403d50040020011422200c2900c035036a04440d0f454403a07900030f558605042400d40d524a082884c115030044510045991400a10362683d000900039505032080b54000c4011900c506580c050b80405841ca003080e0040c0c0e03131840c0c0640902159400e0361060f0501040039084c49119802500c11000c8440a4555100c11002200040d04124800120040c00e51a10b0003c03424490861240350742c046d0704440400c403000b03d40b01030542c2c034098008000c00103003042046e1018203411103c1101e04a0300d83c1052424100d509800d4040c0c8402100c02600103101c200030000c452908004c3c0c1c681202070121040c18420488010035204c18000000d0f0141040000f03800341014441c0d8001c000070415580e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 541264550 1250 541263300 541263313
    0x20f07020d06050609010609050906060a020309100906030507030513110f060a050304020907020703230a150e060f09100b03030f37170a0b2808070302010c08070c08 72
    0x241440043c40c042e41c51a008110f11000420318900a104517019220b000301f00100d280e80d101c0c01c000996011103100e20460109201064117900c0c5c420f01600402d0040d01c4148640303041038030040498000801c510205414203050007103c10303a0b40d07500c0b501660040d40d0820505800000300d031821714910541358000100040400302613602c100654001e07413080711044255203500c0300407a95010240800351001c080c10b00c24024590300b03400b80b114085949010b4070071285081d03d50000d8500604d0240c80c00c0b83d15990500c0d07550b0030500140d0340c0b00c4058a02d1548900704219265510f03030203c941039003150707503a0000c0d811a507010001c1d644484e0225031003641e258141542940c1c0510000601c0903041f1080d0143c6100900d442c5406419070b1b00f40e640c4d9201040c044080d075090860146c1034954299452500941c0c58464801d4501c0c038200d480d12140c0400282c41083d148031000e54821681c64100c82810b20060b030380041c6d403d64150300b1882c1d00f40ca82d011410704800c4080340740e0000741d4510802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 541265800 1250 541264550 541264553
    0x2100c02160504151806030b0108010605030312370b0a23031504110307080102070b060d0f0b012403060509040615080706020c010f080f0610030f060e040c0522020f07020d 75
    0x46d0032420a6078818000b12000c0e076641c030b0581d800d80e0021b0260031b6050b0130610803150500784041c06154401c403814552000e400c08280d200415400c540d2107a580e152250b4030009400116004200040d4000e07213203040036030b00d0648040702102181225249046003290480d40316602000031300380b1444802910a5242018504607003240c030a9900c2c3c6009015005001404c60010700c00e0b030340c50384e400500f007280c00d40e500c0c0300700701880000410454214040070310880104c1d001840310b42c00f82400d4541e08024802c1740d04c501c0c0009080c114030b1410942043c40c14000c7e9151540c460740c0150740020302040e0b21525052409504482c0c0d0000710340d0744500040003810310b07800650810202004c3e00d07903080300a00c1e00411182407108032005100805040041085818072002158a01c125403500160200d000f900c0d0360240c4020b80e0082244841180601c0244101108a103001b0903080314985441c0060180b140000c004141450740c5241d404a105084983d407402114030347d9a0040c614611501c05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 541267050 1250 541265800 541265849
    0x140a1502071a0c070b1309050403030f020a0905011b0224220e060901120213021603030b090115080115050d090605040b09061005060d0f05010602100c0216050415 71
    0x410510381e030b0f40c032030810001803c00c5100201e842980024401c1401e8030309290985010300030140c0110b003019070b00c140708207044030310740f01030b00c005002e40c1e8034000700d24540800140705014582d9030760003035400c01c081400140c2d00c2c400c05c1c1600f540303103880400e0700310080102c03e5244d007e02548890007074022003101d604440e00e24100c0040e1000300034103904945610090000d180c009004a4107480f49820318a005483c2c907601500d5045190800035141c29906850b84a20b07045c030f82d000710701098641c07104998526201034240c0c0500010004d1080f500d0050360010510030040c803400b250245144c2d0310404d000e110700110355a10f0310359071050246014a2900e07c0080c102114241c030f031603100b0408540725400100d0071500581e030488d6032551706030500e000c00403207901000c0b81e010231a030f80d070700603031148059401654024241600130303000360701143d040791003954031005540b42150024508000d041420780f6510080c0c88040c1d03800500314449050443c0c0390105500648070000d6014901e4031484c0c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 541268300 1250 541267050 541267057
    0xf0a2d0c06060909030c0311070b0c0114130503090d1712090c0f0307150e03010c020d11070e0c0f120108011d0606030d0305130804060315140a1502071a 67
    0x480c007010090569545500c60132a003403100000e0008401495803000710344101500c90b000000c84080c0d841095aa10000340300340d101c640d56184594603a11016030040400944540c40902e01da05000ca0b84070741c3d603070961288a08a40e007445404042d400600b03200d40701108480b180c41c0d0141e03503a60741d102c6841003100c50341c0c2211035111f14450100000300c00d0802520707001d09a18060014594141440207a001d0415841c5842040103c480c0f0118100d580900881c400c5420310740161504240081004094801005075180207610405040000d0440b400640f5842007003140039544a5034111072428140c4661403242038901c600500100e1601d01c1940b0013801210310340310384501300000d62611900c80d02d040342c00b00c4c0d041c1c225640030f1140e14000e420990344a4601d0f01c000e80808040d0341c42c038806400c0364002030700007640d850b80c5100f40c585480141019114580c528800c0a12842c0001d10243c214083c01c5405c2d15403040e2004641c2c0200a04009000b030b600c801c42c61801e61041c1c0c09030b1601f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 541269550 1250 541268300 541268303
    0x40902070f210f050c10060b0a0e01090b0306090406090503030405060108060a061a0d0209060c010c080f090d120f1815060515161e02030c060f0a2d0c 66
    0x21581441d0400502e06441240c0c584002a280c2000380d807069a0295015041108207001500408100c0141b03044075208580c05800c12031030442c0ca0342e1134450002c03c0307101000d007040d05204841030107200714403488064030b45c0700400704d4064036241d9a0b8034015000c0c01e000c1c800101680300100034001003100c049113507810780301280704807402903641158400950f003a92240c45110784411414000600c80300c402481d03580101d01d0701501c0c00c50303a0404641c040d4000d40008903503035540d80c09031805550050300da43d000704011020350450b040c003100f805e441c0c5030780780c12500c14000c0080c000e06031f07000c003600440303000d40b441102081900081010070a000200400481e403084580c0300c0c074010b070304843c0700d0482610f00252100c000c2c842642001492980180580c402c0b107003007580c0c0f41e00068401900104c400c0c15a662074030480c90740348181840c1c03068078604240b148000341700700d18600c070300300042e503108505d240b42c090b03800241201c00c2c0361008621204d885c0030240010001c00010380081182030200d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 541270800 1250 541269550 541269563
    0x1b03041a07050f0d050c0408030a0801060201050106050712030c0306081e0616091a1e0a2d05070c051507121b0b07051204051c050304020604030215040902070f 70
    0x5a503104412902e512400e030050000b80001e021400c041021544000d03030001281c0c14192030181c8681c04d06d032a40e08180300b900c0020708000014814583c0c280a8a0300401c51420042d051040558400e034244090300d140303004250340c0300c0010000900c00c0e048200208a40010380b8050950b01c03030445410000e010380800c2c4c900c00c01009c202540c0e0b011540c401d694107156100c019039810104007060803545040d8140404900b0320580c0244a95040c600305c074800400b00103035072a25100006080201c035800c0c258644001c020480d94900c0c41e20031010704208051604542d602a10b160000b24055507812403a084040c1c0b00b48001020702d11001000054040c8124500716510268202c916004010406c112801042c1d980c0740015a180351031b0b070b008042d43c1001c2d41004076281641030744e01da0485090300c441e07002d01071440c00d007114803041d15038a1704a80340c1a40b82d03180c10303004207035a4825448001c0c0113900a00c1e0b00c0e5150412601502c02414a5804c2503644a42906125100c3d001c8202c098441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 541272050 1250 541270800 541270853
    0x10c0818041a030c09040507050d05031b070e0f0403020d030f1d0109060509060103031e05071b03060c02030a08190e0307031e030204050d0605040606261506181b0304 73
    0x1031401701e0718144259441401090002e041c034050000e824100748041340c04d44001d0000383d8403924040c5ca41c21a000440340206142494544580c00b20b040240c0350010b03200b000014040441d40c08180ca005465031400c010420301c00146035000209103505280f04011004243d04e10040d00640000c0340039400354200707120030b4440c8582c450720340e0820722004010032024075000d80f02a803904c0700ca21442806040150925031162907001c03410300f0680350b094000c1242e074001c5c01084910712501c1c482c0c1c4030500c025801d24405003406010800058007440481c0c007101e450004d00b0b2100d0b00802c918440b03143c140d0b1384500503807074041c01003600d10121140742950080e83e007103450b121f0b100340d034115600100910300c2050a80c0340c0500030301c0094815903000b078403610040345040b000d007000c01c821494280c840b081140760152590900342a00000791040f00b104e010701606a45010810101d101584003a03d00ca40390403a4041c40d007003140c540c413154034101004001c148958032414105000e042d5840a03030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 541273300 1250 541272050 541272073
    0x50c0f1b04141306090803070302030403140a0918020d0e0d021b0603061c06051918021807090e0a0c030e21070c081005180606010c0818041a03 63
    0x29035080a903007502c003850600c00128003050741d14010460902800300000c00504030b0311640701e5030b4006c0328840e000c02d4001040c00b08069200c140d4800314500b903c1032600703101c0048801030944540e407041d026030031403000d07802c03400703640e942e044a0740e80c08400402c111207000702c1c00440e12681e20003e01c10150044200c40440001740c2001c030124500000c00142c40d60307540c4404c0100d01c100c074062586124007014010030009100741310702070149802d20300110b07101540d10f003264161080000c024614800d01a00300c001a01c9501d0708507100c1060488841f10b075580c0c80d00c21640818a81e011f001d007030460206004441c1c0b0070f41d01405003070007a41c0d4140300542400c1c08160344c9031044000b0f000c00c03500f14100e920010000201600c0e050b80b1460403185a582d4400c5098541409030010809080d50740092091211104810364482403500019084034540303000080c11141c000e810140c110580014007000761b0300d1419820412201c01001040291260400c26031042c054201e440d01a00c140101c2c0c94 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 541274550 1250 541273300 541273309
    0xb010807020715033219180f08070512120a0506030a02040f02090301092306040f02010c0f02030d0306030501290f03120706021206041a040c050c0f1b 66
    0x8083e11001c000300b45080c2900b0704118010440540070a00006296070320800400200b44c0310340c48510182c0341d40400d8240403802c807141c5002501c1440a1500d0042c0c210501480d0300070414115401051540d4918000d04004032130f4498010010001e0040000d950300d02e019007000b0740300100800c6040034076951050007007012920241d0b1110b626a000f9184a801440d190300310800f0034603191030241c144031034040070a0942c0c40b2450229105040d1004081d10100b480a001801c040000d00521407420252a42460041c0b130a40281c1044060810203003400000c11a56014560240c2122a0081d040000034010702031030000712081d5090045180b503164100428540502c2c900c503400c242c003144a0108644048000d00d0303641c05000750f800307103503441040c1400307002494041da102580d02c568182010300c24203402403000c0c1c429440c00b030300c2c0f181e154036209075508501802c3e0b0340001c00c188100010388050050b06c082118600c5200d0040e05600004101d8883c0c044580d42c0322004180c2030780800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 541275800 1250 541274550 541274563
    0x40b0a06081207200f100306150207050310020a0801090509011b0f03060e010b160c05120304030c0503070f1203090302030f01060f0e06010804150e01112106060301050d050c03010f0b01080702 84
    0x9552001e0424145d00c0d1500c0c0500307000c1112511030500250850742c07100d820b07d00c00b2182c4601c0c005a0000c007001c02441c181400200c03661300780c056003103203042c1e01500050210001801910700c620b039213100144000100b50301c2103490300c02d026440f40300e8092900d4020426101d807442c0d2400241041c50010b0007042044031079044e41c04000c205400c041d1a4165040f4402080d0003c2e11000400c600001c1c4a440d1003403035051142d4072034040c541e541d0031030401d0040c4110980c00540a035000503070402c800020380b9095400e0315001c900388650b01440f1709045404401c0c80c0c00103981800703420001c2020322070540c081001c41d118055003c80b640c0d921b08410398600303400c60300c0c10b020808800c00180090f2200290030004900c9002c00284a140081c1c041c1c2111a030390010b002032500012281c0a070624003080c450703018001c91f110400340c50241e000c62214003061180c280141c020901c414100901400500c0350b002000d070007001f0fa01c05001c41c54000d00400741c2102e000c51192004542d01c0d03031000c50b05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 541277050 1250 541275800 541275863
    0x1110304031e0509040e070905040302150c0405090114030c13021c061d28050103140f0703110402070812150108040b160903021f020d020a0b040b0a06081207 69
    0x345070500d400313001444064440d01a500000d8040c02901080613030712440350364011030095004003803082d607a20514000b10b001425501e203807032080c40104916034a0382441d9040d110110b8160005003e04000b00749025410000b4550160051074070065240d91342e400740c252951603405841000460200d5407040b182203010f0520403828941101c81a1000c180e50642c108231001c0302c0700b241c0000c500b20224200c203500c0f08a01c0c45a00c1d40010401e01255006400c1e48512020103000341690100031207541c0c280a00c00144203d0104198171110755a0750305075080030b500440b84a42d0744003400c0040505a4003214200d0140d0790350200c0d0300842d407150004c240716035072101403101d45840e040e00201c58441102e4280b4200000c07010044010707101d1143d15042c150103007189180e00c110400c00641450062070290003190302956289020804807000103404c29003103048503c40307844402c490000750070b00d0741043e00580f08501021200c81291402015114020040501c2480b04052800142d070302940700e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 541278300 1250 541277050 541277057
    0x3100902030a0b09030403050618010f050708070c11061606060b07021302090a1a0909070f12020904020421350a17071701050301142701110304031e 65
    0x20b060009003081c40c10f19084189041202d04090b5a69110341c9489002c4490b2540403141da450305241c040309028910b40c1d140c410784148240d04e4603201c001c00c1d9800c028992010807040c0c0d0b81c18024010a5a04103c0c050760203802c040c1d0b0354195596614003054102002c03222103250074000a0800c070903005503a06c0c650700500400341e04811204400c040e40160316041d50080350000f0000c1c20a00c51221071502220004401d5296402d107070400c224444010481c405000c02c00251401300c5521440d51a00d14100000042c1c0b1007003200d0204d0000d0045422080119441043c641003003c414866500c0346403040b0005240003800c0781c40075142d100300c2c0103031201c0d4090740201c02c1d61095a03400500650b50380c0345480030201480b02108620300c0f00c20784d0319174041180502c06414513160110154054241035009100f00d00d48003001081240000702084d4520050784080c034005221703c03a0302d25540d50000c0003400f0614264a640c0941e91040e06c0840104000c80140301416107035801e00902c0d0704217501c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 541279550 1250 541278300 541278313
    0xa2c06060a0f0e09010e090d080c090418080307020a12050f0405040915050c19030b0d02090712140609090d0c02060f1b01050108010c0503090a030c022d0310090203 72
    0x5400b50352030394200c00c0b80401d0004140d0001c0d00744e220651041d000b03000ba84550755407810001000707801e1802940342201001983d40420000e84443d13822100402020b403030015110810700c04421060302031103c000c00c480380010501c00240e50010390301d00c01c0c1d402655a0401001a0701d0199110300c645a40140040d400740020099881e01c1c1c0d101101250041030044070080c40e210344081101e00131a800310b0007000125444a07a00e0440b000100140040c3c00c040150306102000a07101c44c2642c1d200a01c100ea6901c002803000e03100d6264007401c80340140052040c1414062005440c2c0d400322005c600400308800041c0704000700180c002c1517940c0325169241068240d4007404441d40c840c11003404208010082d10341d1100380c1b0340d014007040d210a40001446d504024a03c1c0c00d44138142c80c0311042000a1003880524040440c03d88200c0c0e60600b880b8296020600c0810321425035a070100480115001444060100b5801c0b800344105044050b02d03490b94009012000b240d4641030060b4041e409071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 541280800 1250 541279550 541279567
    0xe0105161e0c12030b04090606030312231312030b0913080d0506040b100305010e01090b0907081b0c0a2a060c08072f06071119050a2c0606 61
    0x18030f1000010310315280100380200f0324804035050712517024040f1051550741004009155020711050014050720b601801001c0031015500aa0048031059240c8200582c0101d00341840c07450030320300c01c10340c0310b116000e40c5401803902400130b090551030103002d010314400103140031011507140d65101e60f11003c00c03800c1644101a61004080c0100081d40081ea034114010a541d41c0d040400545000c99130081001d60504440c1d000311081a44039a04480c2030040c84822555000c0c00140c2c00708451625803880d50304e072124a44501c41042c3d107030702d500d000007902e1648120042103013a030701800b55914501c1c0c0a40d4014041003410f5040d40c00d012440d0384003050109920030054040d655000e030001c181081500d072980007260b91504403003402c03c41011400c100c5410f10321a03060f00880116000c605044e0702d030301c80745c0d500000380142138451a1080c040c8802d0514038401700c80501000b0308080b41d5507859a0318040003a03402850102170840000f0704c003000070a99082a071003004003400050905055 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 541282050 1250 541280800 541280813
    0x81203012301141c0609020c12160215070302241501090e0a05010509010617011505120403080612030301120b0613020a030c110a0308040212010e0105161e0c 69
    0x5a001e850411603224024241040c0d0b100180040fa01c4111085280c0c20604c1010004c4a0090744903803021030044c400036004c0600407480c00075411200286030b90380c0280b03801d61001c4040d07980c0c001358000412030302028500e5040c00076217500c0e44250201c074045072003a10044000e079100050710403500b00903030006e0400340240d86404002d201c103040c03440d074554a8640c4041c05039001c0f5190320340365583e4801006180b41c0301c50360300d0040c0300d64240450005550424401c0c0302405000d45440710584607614801d1521070b10885000111081202c0311600b8a031500030001101910380a1050044c444500c1480d00c1c04411030781200d40d2028105501d545580e01c400c003450004205d10740c000c4440c17589861a501500041c8000c00c0da60b80c00007010310780c1c10f034082d01c0703030401030410a220b9001c1c9000c030002980103c440c9401c25011929403022000103080c080c0503100f00350250302c0c55401c2c18103024540010f404040308003415600c540c0c0c032000a042c03e0860745000c0c1712200d00040c04204844021401c2e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 541283300 1250 541282050 541282109
    0x5010c020d1112060405210c1c140d0e06060117270a240203040305161106041e05090f2202090c0703111c030b030703061508120301 58
    0x20302040e51490920b150b0300e0512404503406c1d91150001c000610003620000f02c2e042c100e4810902e0242890b5462010654485494404284000480384009550303030040804c02c00c2d5490101c4160381ea40b0400e0340000140200e001c00321607a02c0ba07200400c24644c007801030152000075590490404d41d840c4107240c803c0c821502e25074040040040a0002039102c00e00074040c030540135036181140301d07400317600403040310105641811314544140103100000368000100c0300001002c0c0c03070011001c64076080081c42d041d05200f006a010600180000300300c1e01039040b40e212102d07004480180281d40d5010301008181c11281405200d021100090386003074a102c180b808580d00745594102c80c8400d13030100d412440c098420070f20200740401c24400300f5511071044102c040e260380290020000889030030b00b031001e064001c13006143c1c8410f0b0302c0d01143c408000301c0c2c008507004642400400200943c051810743e56004824a80c000c0040d81154108440103d81c100c0304c50903120820301012800f203500454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 541284550 1250 541283300 541283333
    0x80a030c0602090918150412031505130c020c1002060f041e080301152a020d080a050304120507170d021c0c0f0e0901090c0512040c030c05010c020d 65
    0x90b424843c3e01e101d40c4941840c107114808155440a4018075010642e1034180c081e5200c003450f002d290104000100d10b802000007003420350401044050305031061481e07c00e020b400040d00b091a002c1d043e404030086400400810300d4603000c0e64151001e81090003a00c0428010303440140c0c0c0b100c0049519070303038080030b2264014011040c5900c2e04c5c1d0091941e086d0391030502ca081d50010340120060144c420b4050038485008003504144e06e01c24403101c40c4040e02d02040818111f05d2501810340030a64840c8080000c140358011041650744404110160640c0c00694064910240345030b90f40e00554003d02c11241c00301d400c02c0c2c0e9401016107088a014155024541d00b0303080310b40920560210843c1c032504e4002c80c00d03100f100881c2002080c0d4000b400490f03041080300401c4580d400310742103921514030302410350704038074004603040626480540d020302ca03594080144802c000200401d000c0d1940d02101a00e129025012080d80e6503401119405482e0401139030122080d0b0708600005c4152300260b1449 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 541285800 1250 541284550 541284563
    0x905010501090606080f070e0a0f0e01060305010e090c04050a0f14070f050c060a1d0607120f02040e0a090302030c07030c0312030b031902030705062107030903023003010909031107080a030c 83
    0x564032042c02b0200340106034401d020780c030b03100001070001c0d5405001d0107014010354a0a210140750a0388803942e5141c01c00d0115008540e507001003481c11142e40c112185c2e8040100c0305201c0410180700001c07400004868440009a1001905104503c00d134101c3c1d140868007002420f01c1e0301c60045420042c41c4428105001c0100c0e004000503007042406554410301640c2c40300c3c052800b007414414140e0f00120b0600c0e891510401041c01442020f03c131203034000301c041c480014480e100386420307482c1d4861040c02c2d104522a1000020401030701d00702c100107507445103a41a66140c8001070a4054501d2003800c135034541c0000d0342030b0500e0140720311160134060004084450f010798500c081140c6030301809481030b8240407000c4000704080204202504038400307180400240d0050b4400175111986010241880f5038100d8000f40400c130010600300384100c10042c02641d0b03594404041e801805002d504401194010941118443e00403850504503404034014140410032903900b02c444601d40802183e0704c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 541287050 1250 541285800 541285819
    0xf04030e010e12100b0f0307180e1c0212030708010e061906020f0c03060f0c13030203010518010c02151f080a050d171b1b010905010501090606080f070e 67
    0xa5a60300c181c00c4100c0520340c054440303100004400c60503070300c01d4945d2600030f03000241c41c08155240021a101102c00b14121000035081440a42019142e6140d0f44040c510a04902c40303206407010b0340940404201d5002c84103503160510b0300000c18001140ca010100e0103480c010040c40c20780e098201da11072001000c8a140051a800591400e50f00f034100700b005902c26001000800801c01842c01841c204400130146c520b0408004d04107402d00410709011154049091240302c5542c00b480400b465000b0002e01aa01e080803410304449842c0391a201a582030401a06181b8004118003180712000c60b2200b1040d038542a280381d81ca1284e40018500d4000d0b20342c0081c0c6501c2c203001c01d0b190349205902621030102c11480c0104401125841c0016107080b08042c042d00c40c0703021603c900702000142c1d00e079403035803400081d1701034030184c00c2004812542400c080d07108004042d4809410b80301012010841c0707580340c41d411034140408541480754165010040303000e080c010300c0d0406410314020b01c410171 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 541288300 1250 541287050 541287077
    0x18050d1212060f0618180c1205040303020307090b03070e01051303061107020a08070b0409320a050c0715020702040603021903050d0f05120705041d15010201050f04030e01 75
    0x40710300b6540302a1586591000500000364003c8010030007409000412180c182408600502c000d00d0280c88161556585130107064140940124160003203000000c11440c41d260802030084e5008031414000200c0c600d01c0415202118000c1d240504400d98030751081d0901c150054841f40d2000780380394901051181c0000014400d4026001e4881400c20800e840f202d051041c44540b58a9410041507074020010912920f6040c10a0300c0841e00c94501c00700e800c85004007485804a801d14a025170001e0030004c9641c0c0f6200c032600b160140100900800c1156104401000d00b0700410b40010049140724918226542c1c003074001e0140140000d00015280e0b80d0390b400142c000704000c1d010000b800040c0410420f000f07090110b502d075000c0e64100685603454240f07005145114582c00c3c140c071100d040000c50100d501c40c1081c3c901070820a041002c040c4145400d40040d01002c1780d41002c209901c8600190f07a520601410703000700c02d00300025200381c4455400380d0741d003a4070b13842b424100281050f0010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 541289550 1250 541288300 541288337
    0xc020c010f20030403060b030307050613020117070f0f030b060a0305061c2a0b22090c1d10210b0d030309021216090e0708070f0618050d12 61
    0x3108802c200009642d503920714642002a249040d40e4140310350024001c03800442d0000c2002980308240039103140d43c400c01c920042e1801c071100c0d202c11086108950821001c2500300c3c4898070641d000d9203032201d104200d4a0308038141c5e07a9040003250012400e000f03104a82c0e0003a00f000344c00140090070a2071800c4d90f6000348141c2d2105940c15540940a582c0021000362113041c0b0080030921031a00b61039240c01d103050b00300c1c148208106110034044500703407032988105100c400b40107007003582002d0007524010240100098a101078940c110400400f182d081494112481804a101c0d030700c54401c0c00404051030410070032500100140b044e00c0d06002821640d4100d00203803000c0c840d44000a2002c42030050040c084500c0c2d141c08055440041d40304442010056004110350100d00041020556824001e040440981c040200c03482401404940c05052685030000c0c0e4a031540d4130382e154540540c00c0305e01c031941803050303503003084030300f40f420002c00c4442c4900c841030b4555050481a82e410101c071403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 541290800 1250 541289550 541289597
    0x120714060c06040c030312060501020303010b03040f0c0305061e0610030207030212040f0905070305040203120c0c06030103060c110601030f06020d1d01050a0c050708040e3c0a0c020c010f 82
    0x71910451348110078000c1682141e00c0e00701042010508008441c00d001c00030b07550f84018040e40311254030200c0010100310004450200e032a600000da080380981d0b91034450303590042521440400410300c0500910441c1460b00c0038803c0d5401000e543c200202c070350042d8000d41c86090309504500403400c5015030811014018001415402040c49555190401c10070407200c001e4011020181400b0601c4003517035001034036030b12440c000646590355034214541c080c948042000200d805c000017100000c1401041d174020342d80c405854480d40c0a0300002c50750a600e41800340001401c85d200b500100300030a040e035018001364048000c000444048501c40c61100c200301c0c4a10300d803169110420000ca5250300e0285110703155081c141142405080c0e030b00e0360024016401041c200340d15640025147c220b05402401048003003914000c0c611a180ca82e00035000382c2100d150b56020030035000702c2e030464002d10400550901540c054101c2d4440d0400450381404001c1e1035508103c44e4101d880e1541d40d002164 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 541292050 1250 541290800 541290803
    0xc0d0501061e03110402070809011d1003050405010b01090f0314100608011d0c0a0302060c10020f0c010c090605030103081b07080309031608060105120a0b0a060311120714060c0604 79
    0x40754980f460341c540034032818000c848250046006101d903400051144040d94002c00c403d08000326000100005444070345001d0180d075512000f9440303a1040d00380c040d44040d0041d8001c00003846610039500066500100c3c1d032003424003010444000300089802c030038161404c1b511100a4401108101403010180c1d00c41c0d80003d5505c0c0d54445188001307504070101c501c9443e440c040609041003c1e80001000e04140b41700c040d01505000441c000054418070240c1c035000308054003152503a030801c51503407040e00700040303800e541e605c0c0244610085010700d0341542260381a1740c070070386141c0c216911201203400000b40c454001d00480029079440b0070a102500c0502020360055458103503107800c0514049100c02500051070f03000c00140500c181c00f0401034103540d000d4a203000c05800c8074160038540b4120074406411410000144021050b09401071310449020381e51428880c07000701c0410800c18841e20110302107501000040260120320720041d017142d43e006010345e06004c0c0044c911410000c00711030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 541293300 1250 541292050 541292099
    0x301060b030618060907030b01020f01110403020a06031107060209040b0a06110c0f030c040c1b050c18270f07180c02030c030f09060f16061803020c0d050106 69
    0x20400c0301e00344061522007406079004043c803d030a001000c10758001025012008041d04c852504002d82d00030400041a5038110000300440c104400b003051403600030b0b0008901c188104a000915140309020b10304100c20344d02c000c2c2d8600280c0d655004000c1d80207010050f0080c3c1c942300d02152955524140c070004210301e4030303078144280d000380400e801c00a080580300c0c42605d080307415201945002404161024090702c1c0040c0400c05540145c0303001007103507596003001c60110072a0040007008548d00103420000d03a040204280100c504c045000b00c01c44108a14400502d01040c80344200d088c00120b00c2c454009842d000d07020185842d003401c03680e4102c800036106141041000c03a00741e12500c41d0352101c5102860034400c00b03000300341d124440d540942041d40d0001c1150350840d5280e0040ba03075812203416215603200b07d00c005810494043d40c0c0141e034550b103801c4508c100085403a4503c9005139041c0c2c0980641c002c031104104102c0e140c9035041e81e8a6680f0b04021440400e88000d00e03510624120 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 541294550 1250 541293300 541293307
    0x3180d06020a1706040606320d0213060e0616020f0d03020f1207030203040b0c1615030f1b08040609023d0e10030b0901140a0b0c0c1e0301060b 63
    0x5040c0d441650003c0c4c03002e40960301c2d004040080300d0b0310420300081c0080860002030219000c14400c80f5000700ea51070240000000036190072003032050760040003841542299901d40c560f50b000705440d8200c17108060390f0080342c1042007807103100d40400c181202a20013070400003800b01c8800031542c0b00a200030201c01581c00b000000e00020010403149101401d03148000d80b0700107090b03030025100e02035403203240c43d101d0000c02ca0302c4500100b07204241e1030311480d034410400c050b911034514080c11480c40b040300202e441c0c40508401817501c2c8c012011450a2201043d184100303520b400c842c2510020029038080341c1c0d4110038401640c91038180071081c4411004c0c0b01e02c002d40844140800e030850b10b808502c08116200c2c1c02e0009030850100600010119080003455644000a9010740b41180c1070b2a44213007044c001103000d40c0300c00c02603070b003000081e5a19000035848004a80161050001502090b07021a518030b000d407400e00c100f0b106244c42000030742c50000640e0007003801c1d5803450b04404400702020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 541295800 1250 541294550 541294577
    0xf15020f070f050a09090f080a0905061204140a11010f0201020906040e04052a011409030105040b090106091112060d14030a03050f2724070215070203180d06020a 71
    0x13200580017a044000e0100001d036000d0784d44205003039042e40024030f8440e000c00c1c140e03416402009208020100034012650310708410800b00c5000078202c400b10348003003415107001848100090b514402950015445501d41d00e5100191a2440601581021036400304803001154036030401078401001e07400792441ca02d0034503260603414106100b200b2120010703007007107a061105800d03c028a0009084c20211030011000910b48454866031201940640c24a03040c0410050000c94061203258460020800c81d61207581d131201350341074001e0881101d0030074042c200420741c0e0ac01c0001d1b04010006e01141100d94240e0740c0b12003d501100c108076a60704049004558039406000e030305d41c0711006455035105441c00780042800c014040800b800800203410b01c22030112004c100b0b0002842c03640e051070b1803940545031144400030341203136424014050305e02240d180908403481d884c0a100d85402031401c0600d440e4010400c100c05102042c0d00160003180740b00414004c0c401041c4400c02565882e8400e07094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 541297050 1250 541295800 541295809
    0x7090615110a030e09181c0207050117010b0d1b0c0506090705060706181a01030204050601080903071226010f12050601140307030b070c060522020d0804051903050708070f15020f070f05 81
    0x14ac2c1c4914184a0080003405200d030902c50f159040d10008803c00e900c070201c1044803401002504903c1c80210130184054a0150b04807544551040c824400c039800c5555050740c960710f8107281c0c4902d9400550a0200304001945070f000040c090030011156070340d441d00b64542d600e01e50f81d800d500c0072120540c0c000520a50610380a0154888070070b00b00001076041080b40c0c10755074850303420098100d810411106105030303c980c103051480300009440180040c5089030319422540203102d054000e03c102d0400041c61400d0031301c4207140716005409450300368a4641052a101d40c4203180607410700a070742002c000952800c41041c090300003603441607103603200b40c50500c0407604094003220714221201c0308600321180b240c1300808110b50540e2400c985107418500b0500134055900031662210720302c03441050030450b001e400300449000d0822540b4065407600c265440d06502d000780100d000280a09010392541d0000d00080e6104910481b0341d29000f4a0904d8205441d0b5049140c13000340795031081206140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 541298300 1250 541297050 541297063
    0xd330b16301e21050405070302061305040f0e0303070f0909050403030c020c01020f0309010c11060c0120040f05010c05031309021b07050306060f0307090615110a030e09181c02 77
    0x141e800c19003c4044542c401c0107080080120081200f91034900007420042c0c280720020007194043e1070325456102140c3c2801c1031014900405014074549082c0c010b0503d018002c07502c1411065016514544502400b16541d420011600c800d1040d0080300240410192141c5440f2700d000382d40000d54404101802818030420300f00c06070441d44a030050446640380402110350001c0d09082807c2d004141e4905800f803001c00d106059031086e07001c44e61403c070320b006401c0820841303101440c0c840e980103803840710181e07070085001705107014050220030b04c56035000b41d6000c402507018804132400c062034805141d0020500340c0014919a4012030713000421000c8035002020b2205800242c81d00303601703190200341d072004010540c0b0720440303082c6180c4030700c1d440500c4884090110910140001500c80c00c000030300d940008100c400244203c0310100b10104080340002c002541a81c4124045074140c00304820300402501041c546001c0b290b0889404900708032244003003140c0d4943e44800c0380304c800040c0c213020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 541299550 1250 541298300 541298357
    0xf060c02060f070e152206050711040914060411030c01030204081b28061d030d030b120a03090305060a0203100b0d330b1630 55
    0x10302100510856141d0500941c0d4081080d10b86420090790a50000b24119075004205c5400b020028103540b00c0e11003503620b00e81c030f4001d40c04828100781d503d4800700c50300e1041d0400600755070f03a02d0401d030140e80b4081e000107040c2400740c101059010388600c4c1181c1000b00c103031011112070b120940d80207020304003031024900034103090a0450519250204050301d81750b5082c992070104149050b5010566640da20152820070b21100013280a4224540e0080c4a140c900500010981c5d400113901419241d500400584c1343c007401038180030102a20076006001041030711365110300c0203d408140010104051000300307000f5903030403480a19609069092201c050000d40c030350341c010003c2003460540100000b00702c5020244c01c4ea0741d00d82c00220345008291810800b00d1105150034008101e00403901c0344651050016094000280d5401211f1044e21031400400310741d1428850305008519040e80c400f486500c03054501b003540203c101d0030b900d040c018444140100c0e042c0b200c20702c64001411141c56801c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 541300800 1250 541299550 541299553
    0x60b0c010c0305151c080d0203040803100b040315020313020303030c0405011202070b1306150e04210e0d0f08040b0c07060f020618011806060816050618060c06040f060c02 75
    0x20744610701007865851048038100074020040c00c0101000714200450700d5030000587c08544909103890b1a4001d58030644001d58681800c0e2008140701d60b005040703c00b00c2e0f41c001c0c0205079038180301c0c0042c00607400040005400b071b142c02c0c030b031807004d41c50500095110710181a462070b0754906003030001d80103d440044000500d881031100350300040485030300d580c002100c00b1031420284102e18001000d49030b400c00800c482d030f240d0030000500010340c0511600480c841c2804007912521200070385035116030994a400010010501d545680c1441d14080803040c1c060005620170341e4264a50f41c02661003036200854080000441749403c00f028007500002d403145141000034044030f500c00070350b0307100040c2080034a02c41440d14a030b10704409600c000c04224821405800d41c2c1010f050010040200d8801d03080b96000b58803140c001142c8008100701500d80040c14030741031002c000e80080c0190300c0300044540007081080040046c800c200500b900c1030b4031403c1020340c1d4500c1880c2140549004060f0103056 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 541302050 1250 541300800 541300831
    0x2030f0d1701030804050607210e1203030712020f0f0309070321080601030b0d050a1406100f1518091b0903031706190303030e152701060b0c010c0305 66
    0x18594005c41d01296402c0303608a03207660341410801d0902c0303481000d120900c41103642021a41e07810081403100302c2011103010322804003284080352240310440e1000000b400d040030044003842540d02030151030410516603801c01807801170b0044c5035841a541c80d415035000c400200100311094004024090030170303803100c0994544c000003910100000e8002d80c103041d144d00040e5484c0c0c48102c10760b90302030f4201c411140704089074100060a43c0003818114002e00844000581c1c41441111680031078004011001c00d1310329044100845070b15640301441006407c00d0a050a2408040c02102615100b5000541400d1700f07544e417131079842813030341313420501c26040410000f0940201031303040f2000034070b000d101e02a41c1e03680001d060740c4482180d1088080d003a05003c41803542c940d018000300304c24802114582c900e800c1180d46600c01c11902d8414000c107440811423030140d510b00f048000b42d00348002098013602c03a204201683c02202000f171840c1e46d00c0000f00b0a15626001c1c05070001c2582d44030444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 541303300 1250 541302050 541302053
    0x708040e010b04030206041a070602030411030d020f1209040603051f0605010e090703020d14011202090a0902031c0e060d0c0e010c023a0b0601080f0f0109050c0702030f0d170103 78
    0x26602943c0f041447e10503521408d602419000340c1140c4406901280440d904d03d05450941c4000d0381401045019120b101001027600e40000b03414002d00003171500412003240d590f109841203a005448058000e51035070030000020341c0400007060b103080803003005096890103185030803c43d81c95600160411400448a0140361a00c0080303a0b000001e40c6005a5101820341003400030708018a41030000c60700540001514120a04002015601c220f6030141180c0b02c037240709081e0381c040c48010f54150480302074501c20044610100004003010f003440700c4004413020005025401c1f401d4240807090f100c0c1c01c0120b42c1e5a11407076844281c0c5090034000c02c00c00c2c0c10b80100d0880030340441005400001e01d040300303241180c03600c05175225070320340796400c0c100504038a03000b007803c20305403501030104d04804007007078000b140c00041c42d00c11042c5a100528a82c64484408040e120140107a000b01c1e1080203507002503201403018840e0300c000c15008203550841940b000b440311001d4002c0d400f107910000018030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 541304550 1250 541303300 541303309
    0xc01140c04061b03170a020306040b0a031e0c031b0510170c0a020307020d151404050a150608031611040c0504031203020f04090f0b010c03020c0405040302120708040e010b040302 78
    0x120f0248103140c034400b41e0140380c1035440502001d907980c0d07a61804020003080d013100f60020340c4140015102841402c40076428484103030701e5808018401c4040a04142c10030045c2c40721820340501404207a00309694944421103146881c204e07042c40300070115428000350900c001d05000008441ca411150304001c0050442303141e40c058444954000006000140b01d44200213880350b0a400510704a5084507078a132641d15106074200c05101d240c2170105214800b81062405403107a50080041d01300c1c1c2c00a6542c0c0d40415441001181d40300f5a56200031440c081c00308007407c4000b00c00013001004062506005c1502102800e50074030039400e1940005a4a61080545040380e40c06541e0490740b00310098158080d01903241072492032403003c81c00040794140e60700300e081505c5450b03c3c00c000003003418004681036144581e000d40581d0045100101900b40f40e070103254064000e2054800c401f0400c00384c8589603005c48002d8031040e002240c140200203501d02c09500510891014505d050302d5540401c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 541305800 1250 541304550 541304567
    0x314060f06010c0b0703020c1605030d050f07060207050312010e0403030f060b12090c040c0c0311030a050405090a062103110c030a0312060801061d06151c09080c01140c0406 76
    0xa04e0307040208085000a4000d0301942c00500c9030b141518140c1c604075141400700c519034410785200344184030b8220a000c1c0641e0444419003140034040d81b0b007002a80303405020350700054080300c1300d10080000c05800413080c02600e018014130041d032110346c00c042c1030003800d8078075114000d10014034220040009007400401c940001219000c00e20346039462080e4641844545022031380c11906120409481aa01a803000c3c1c00034840c0d1030380c01c80d08803039003880c656034005c030500b0b400400e504001c140124a00500038644c042d5000d50040303209030301c07402d12415402160040c3d0943c5c0100503080d008040c0c02c80301210484001e40000c022800000380040c0c2c0e03a04844501506102500f03000302d010400e250002400341c00d10340003c1c080d0650f00c0d4150301c05480c28900c406480d1444c0750100f020307850095450013181401030100b03404c0074110f40c000c2e2120300b40c04803903004c29942c4e69000000036180030090710687c4060000002c000c0c166564128050100420743c910302d02080000380300182e04414903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 541307050 1250 541305800 541305803
    0x1050f130c09110405011403090a030c02031c1d040b0d0b04020307031b060807020105070c0206210f1b0f16031209060509010e0706120b040b06040314060f06010c 71
    0x2062002a12414a960006010380080c00518100004042c00c3c400340c3c4003c00443e0401c3e85e41d0300d1544170301901720600c0d010507139156406421000040000c64032801c0c101c40030500040c1501d444600240c0465010b4882c0c0780741a011518943c12000c01489180707104032842e10a94060050452030800140700d00c0f0102c00c0100170109540118065440802c060b03070166511100c0b0300d640d81c4105c60f60941d03025040c407407840010300e204002840d4a1041c020703540a40784a440701d400c0486940c1c200121a00300325803d2206103044445960040000e41419001d00c0048020690a0034075054140031240900701c0380280c0b40081000c09011030711030f400c0391701c0014205c20045254500b031a0817130b028040c01d80300469036400d1071710407800e021075503111038000d81044000704641705082007802c1c1c48040c580301d6003020501c204841c41c1641426004600c014000520004240282c10001240c0350484c2d00243d40e00740b141610301c0181103003001219000001083c80c2d06071f03481c01500003440c00c88802d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 541308300 1250 541307050 541307071
    0xb010e0f0d08040b0c031201091406121906020c011803051801031805030c150105150d0e030c0715050702130e0a060f20070b0126010216110301050f 65
    0x207001400b910500b0744004d4422405510f0341c072400c001da615a00d421140215844000020000641c0603461088445101c1650320880a90f507810081000c03400340000c5022843c02061980c81140781004522101b8030303c034000044e00c900c0e1800159003150710300010361440601451488002c25007040c00d0303030f00c180b05007080301c00d80840000040300681640c03899040c800540d4540c1004004002c0b0240c840c41c8441000c5440c02e500d51042d00e00d007a04284102c941000e4100d40b000c04503001e000c001c01c7e80b200d1070718010442e40b0110714103914542c040303101250360707400c103030301c107020782e9190ba10100345451b0146849402d11843c1e80014000c1c6941c0310005600340e54850a03800d2110b41071002862060b045642048103d08607015070024204080408114400d1040b08488c685004002d580c030030341d08008508030b60707800c1c03801c400b500c90400c0d080070101d201078130420b6190b100240014011990f00c0e404180703415800d840e00d11449220651464800d074105000c101e0142d440b90032030b641c02121000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 541309550 1250 541308300 541308319
    0x41e1104140d0501091709030105102409030c09021902030f12041506091a01170a05040203100504030e2b02012304090c08071d0d06061509090b010e0f 66
    0x58114014245d803640104030008441c0c4540c01100d503000a016207400c240c0080c8074950b40c43d0f94905400750640152646403071802028003200c01043c00d48440115282025010140c4a841d500603031400c59008003985c0f90002240724486000c81640180001c41e80010f50824000c81e05114480c080d540781e22115100d940c3c0002c1c2840001000f42c00c440c02043c2c0e041090b0343d01c0d10000e1b009051120030900c400140011081400c0d481840034000000307118400c1c050035140c904030400940707006082640e040c030481c14100140031140c46010b00a6200e52102000c400010302407000c18600c0416210400f5060f41078081c0081c81c81c28002407483d0309180103244030440c48860b041300c0300e01107000d940111020501090050140d8801101c51616444200c0203980e01d0004540c41c910741644400342d480a6034403141e5500307001202d8810140314100228440341c65601403000080422981c40014007e00e904220a074454420000014420b29207800318012030b602080410f80380200c16402800d860 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 541310800 1250 541309550 541309553
    0x8031f08100f0f1d0106080d08010315060302060c07050103060611101e0204120b060f0d11031203090a0201080916050613094709060f041e1104140d 65
    0x542c8003040c200d081510400144c481410f16000e4614a444111069071034003101042c10301d00042c903545001066602c2852aa00307695520b071024802c132002c1c81500b40c941a0100c01aa5858080c002d9040850001e01a0341d04d44400101035032201d5104031f0030300c555400040c1320000c01040c5000214034111000c03034860100341e501001d45400e0390b46450310038404540440d00c8205e00c0d080350480c1307000b501e142c0c0362522040100700f4120403d22920f03908c1314600038448000348881c4c440e0f1413440d0004080d69450410008030076041da100312070780c4115403c00d1119108642e00003c6003608894190000c00f1103454641c2c0b540080d911b03a02440d84207010210700c0c0c07041703040c0c07250703180019009480d03007440038120080010a501400d004445030b0480c0407000c07201d2191201080c203028259518004008079003600c03c1c407075480c201400c8690025810703802e41341c860700c460084c8456240d0110140918104560690341210309807000400b000c04208001c0051000c81600b82c003c19000300c500007204843c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 541312050 1250 541310800 541310831
    0x610030903021e161e2c0a0b1810051c0203010e0d08070c05060c0d090f140c01050408070510020a05070807140612240d08031f0810 58
    0x45002810340e0b481e150b0b0304040482c2c4040384200003038182044c1200d04c1da40302e0040e035090201818840c07031031031078404080290710081c10040030250b502a581d010381e41c02071200c40d608800c003264428042c90b203c810541450030030100b600c01c0b41d030654030f2111041c18600300c013100c0080144103080c490454600e460303403101e54607c1c652400e254010300800c042200c01c00407645404130600303218040b40303400300081c65070f80c02031102d50003060b8848007030911542c1d0404060324a400880041d01d16030340d1801d00e000009c2c482078a80300600d02504004242c220203d007403918041402c02402c0c1003103401d104c10441400002203540503214211a04180790f102d440d400c0389040304540c4041d110780f14123440001c6c0721001081c55000e496100b4040c4041e00001402d02c080340c030850566140c500c0081c000101d9810f055000c1d01d13048040100b20080322801c0341c0c00206400c41e154801d5801d100c001090028040364100e154116072518802e1000c03a924016240303440e241160b4006151907224500080e14100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 541313300 1250 541312050 541312063
    0xe06040b010e3010230f070e06070c0e060409080301030611070206041502060a02040b031302120a0b180706020a1b0e0f040201030f0612140709140f010509061003090302 74
    0x4a02c1032a0181d40c280c84003641d0b0f080b503d0158080c51701d090010400842aa145481c54800018041020352902200c480c0c550500070080301c10880007800c0b042c8150307248801401141d003e5403201a0f5281829480164a0006050303076100c0c51030030300d40e4000181c4080c00d80c0d04481d0001d000048040c400c11880f42e55118501c0c0c0290711a40025001c1402031054601c0e20004074154200c92840d0b480c1c000000c100d109600810079001b105000042c004510785401e01c10891002e440c000a000c288100c44e07240008422044500849410801c1a00d10000412100a1100b0f01c020040145800b0001c1c2d20788101c0302c0090004441810300000400c0640038800080c0b41e0340700c1818641c60281d1100e8a28801503801f2030009050200c0b02200c505036000301d900399004040240304001240c0e5585014000014588a5500480000040d40c208500c42d140d8941c3c0389500341e02c018900300c1880090103805802151285040300c00b445016140e903c2421075413012420006850310441c10107900e001d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 541314550 1250 541313300 541313359
    0x140f1203070f0c0e0606031021170408060a151217070b090c0d0c06050c0f0102030702030717130303121b0e0310140f0415050a060e06040b010e 63
    0x442c1d9410742040200d94407041207461400c6000e003d41c80d12020001c0910055801e03040020301004140303c00116106d041c003404420880141d80c06030942e0b240030481026072a04445c0400110307007000242010300805501c40400d40d403c02840008100103c81c00c80203004090a0070000807061080001d180740700d4502c2071304134001c244c8a40f440d14110410400840f40100343d0700503860100e5050401412079445981d0080d50811102e01340781c0120b4403600401700c180c400d032180c0f201400000e9000e1000b58003034050b590146544100c2801c000c030070701e6102c044002100c0402c002c140301e20180e016445c0240eaa151620b0300548100c462142c0180c00010a25000144692501e115098001040700b01459003030381541c12060040e040c25040b608074660031800d20951380001000c070503a003041c2907809807140384140b0f28032070103a03102c1d000c03100300315540c10707a007179070f421040c0092880304010b66070001c4100d40030700811441d031000a00903413504880a00980d640405a00e00038190f10849054a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 541315800 1250 541314550 541314563
    0x51510090212040c120507051513090605090c07050601060e010909051f1a040308030907150c05070f141306050607301e031803020d0801140f120307 65
    0xd04088090b04240e0702d054900702c9400b0300d03805000a0070006102d0360300c0520f400c40050400c15203031006008034403c27400401c18044c4410003242500030604400c0782c024000c00800050f100781441c0a1140030b12003d03007640042542800030000040300061001c1c199002c41c60030180300c050344070041c0c403076942641290328900c5c1888204040c401003040d00031458074002080202d03041d915a101c0b001d5140070300c0d0510242608001c1840440d400500641d0000f5a0500b22500e50340d5440b44000180c07084a00b10000640c010403140c00d20008210032405000000d00c929802031408014441e4030383c9808040740038200c4450017083d09101a4007000081c10082d25150752506e20b0700c3c2c5a201007450080c1a64071902640f0800380d600281c202c0c541d0030300032a031560740b540c051258111040d41d5071929120101074a40c1c4075101c0150391401c2400100d03109030003c01400411a60103000090b050f00240703441c40c1d4a130115004d40c0daa01152038a482400c0c0ca4514854000c02040d5007076128207140501136 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 541317050 1250 541315800 541315807
    0x14030a11070b0723161b080f0706080c0909130f05120904061409061201021315030509060405060106050c160b1207090b07020411070f03120e0a0515100902 68
    0xc070b40d00503000c00ba0b0410264041090705004e140c035420b00303020f8100750028030000b0491110002e0040500c000005044486203049155102c1d40a4a44003403c2103060068001d000100801c941010031280c200480d52405418042060080750508000800e07500000d824070300e40c00c0520616205c80c0d15510782200590381c1c031140042c0b04c3c5039154007510485015620701030b000500f03e1020450711401e188014052003030350321140f00308a10069445a5204155800c1001c0310800c150918481e0003080640e1070001c170741c102d0140c054105c600043c03030205550002c004001c002500402c00c28155445030800c00d86861444d00d0f1a403a099440201d000300c0750150b8030100d00d8130203240243c0007044008400542c141d4400d041100e0081185c401c1c2104800144800d070014030b050340050242000c0d5903040303070920416450700c0d4084ca040c58826004100090940c10001000b0b02816048000300c1d002444c0c510380c1d40e07458540da4131100241482001c00c240200c1c03040c440345020740c0010200e0081c19500d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 541318300 1250 541317050 541317061
    0x51522030b0105010f03020309060a0c02070806090706270303031a0918121602040b0f1008310b040201170910200d090615091b14030a11070b 62
    0x39422003070040c01e01042080c05e50b426600d200e030089921890904010341041d031107802c1000080c01c403c3e5003a074150b000f050404104400301300302852260011200800486103860380180000c08980c0744a080c40c10042c1d04000b9041c0d40e101ea0300d00700d07541482e00180c0307804548060410023140541c1594040c0c2d080301400f0901c007901c41c0070100c00c8a02c6098640b2080c0e20289001540b284d055000b403503004400d034003009403415070f00414440501034040c00c12507100a000501000c840b000b8407001c94402d006010b034000e100907807008140782140600740e00c140c0940403001d2001d03408800820304000703c0006011a4400d41c1003980083e19060f20400500700090b0385903d400405c000a031043d46800f800301c44803000d800c582c1013105030344208603150181c030b01a0780c8007501c401c400039101c040d102c01081740c0164109203039030014202d032a800125170340045200092004242144402c000000d400101c1642034001101d400034012540020741c0420369605558501550350080c02c030145003c00c001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 541319550 1250 541318300 541318313
    0x6090d02131116060f0c02120309010624021614091305030a1e0305060d020d14120901142a01090b0c0306100f0207260307050f070f05152203 62
    0x30420303104d44c03028086003160b00c1641d0102c45082c070030040140d014041e45a00b41e112000110340140b201c0d00080380032034844a40d120000003114201c02a2a101e001d410002641405808040b0703401c03501d4101c1141c0303070100c0303842c0101d4800c8540c3e104056480100301030740641540c0400c620b6124007629250112848090032035941e104084045100b02034801d14094070a00c6034912803e0020410f8104510740d801340001404046000c0722544580041c5802c0c00408104501c4990301d10320340306664140000c0010403055420144000e40c1100f802a524a142c0010325a40d2b804016490703181c41340f83e65041c1501420038070601070b0500c018802070040d02203140c0d005610500d015555030703c02c10a1642c040b0741c4004541c01c0440142c0140710140000480074580014860328801b440c041500402c0e01c503411030740300a4048610b6441041c00205c0000d007400300078020320455001039041840d02c0b0101d02c0d4105100b80303030100100000f030f041141706001c0344c00005601c41e0000e0520199284d15041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 541320800 1250 541319550 541319587
    0xd020d1107120606170a050a0311160f050a061e0c33051513020a030e070801020310080a080717160b040201030f18020915090405071406090d021311 65
    0x324019015000642c450800206281d0487d4024000c00c1803514545044460342c20b80d042002c45402810000302485101d02c048201810080c0b580700301c03040c58402080003080b81030f8000b00038462103180e1050b00403100e55000e95044c00d2400c054011450a00d000c0e11600380b01c1d40c2090b8124024860710880e00c880c0b0b024000c010700303031580030003641e143c801d0860401c2d031003000e515600c62500c580c819845105a00540500c07205400c010520030402c40742176003800c03a29085113480340e5021041018841c0340c1210000284a003001038801d003007490b200e288251040d444050144d4221101d0b42503a0b9510008481c85d18804807098400500d01d482e00f0b1201c503c0550301a030009091040305540a032242c410700da4500f42174041102422803503401d01c10881402030040940d0303086071407840100e440703000909102d00d102d840030300465400d00517080105240c3d00703811401010240441c10107501c030031090000145d011110f800e880b540205044000d03014541546409000101e00f03000b10b026500c90030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 541322050 1250 541320800 541320809
    0x130b0703050402040605041b120e150402030105070c0b07031505120a0204052202041e050c19140d0e100c020a02010801090209061c0b0a0609080f0d020d1107120606 72
    0x21701c44143d0b11820401900d0a2000020043d400e01c0210030881d8001c01082030500012031000c952100a0110365080c0320b0504010052100c6d0202040211701d003e1051603404552800c000c01d0120864071241882e075001000142455600c203045646004a80d92101c02070800411500c5528982400706850346141d40d400c07401030f810140440c06100000c4c1a0101c45d0400300b41d400c5901a464007008003800e03a241200925003450002c0e90105040d40c0a04c51080e40f0901d0020f9640b9031403810721142104041c098130803c1055984071882030640000c8401c4941115004500400d046c0c00190908824901150b411464110120b0f411a000f041503036861b4001d0f242e10046a07030f5036402505030b205201017264407034020401070781c08500020003a851000f140d440061659070110105000b82c01340c5e0042d5010941243d0208800da0007007220018006403140909003061600202a6440100b0b192100034800042401a942c040c03c1140d800103000b0686c400e0b0180002d8204640205400d006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 541323300 1250 541322050 541322059
    0x6090303030510150e130203040b180c03100e01140a0614040905030406030c0507061404020f0f010c02120c030709050a0c0507470609060102070e01030803130b0703050402 75
    0x1946440000703d03600860300d4150440c084081107000031954059480d0516038070100d10b11303c0310b008072004e2000c1c43c030451051000743ca0b1402d044407a1003482c1903a1086c901294015503080101d41c40220b1600718a0041450101e100c40c41156458058600e05c80541751420043d4200320780f140a940080045841e0364004203032880120050005844848002500550040104101c07441c03082d40f0003003090b501454140e0a11803203075500d42c00e50300c410841d541b0300c240c00d01c02d200a519100d0040405030744100c460b4212030b03c4502c0044c140b10b42240c8040d2084101c01290300b1200d030184220096994014181c0b8085500c0b42201030042c40b00761204e680c50ba190a000c0c0e00090b01850407221007030b03001a41e58030000c500c40444111f04520f91604034030000d52940141400b111007642221030b500080103c100b901d096014405c1404008059604650007507604001e00ca0f00010341c0c43c1982c0e04003c515a0341d958000040c20010206600200b10603281e00c1040003299143e0310060190b4403c85 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 541324550 1250 541323300 541323311
    0x405010914070803070b09120d090312020721020c0301020d020711030723060904060e0a0507180e151206090705030607090603020307020c0a08010c030509010507020c090415060609030303 82
    0x201075030760b207582a01403040903501c01c209200c045564100080ea0110280d000c95510300c161184400c1e0300d411401c4002d0103240c685120b1020141c01c4001c400c0c14039070600d011418560b107a1074040d401c6401201060b1020079035080a1003052003805100038084c0042e009654070360041c216600290b021080c02d1307030f030504500c44044443c90007003590403c4450094004111a108080604a50031703448500e5a01603420025800d903a1500c4c00351000414140718400d02a00d0072803084400d80303000a090900f000700e4a22090010110032410308250350fa01000c2c402556903009010080502ca88007113540414000c6000340d00d2030002400303c0c07095510300c0580781e01e56079a0051581d994802d58143d800704240150a003ca135200754099a400407491049850b00c860000c0070030ba000c2042d4000740100d94507081300705106a09801030640090780300c0001c03c680e150407200217454005d81610203100741002d0b4081010b102e505c0003451700180c9d2103c0c1c108416a900c1e0000382090940d840f00f00c000c0390800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 541325800 1250 541324550 541324583
    0x11010f020328091106030a090506040c090c0c05030406050a0909020708131202060306010c0201120603050105060a21030e1203040603140603010227030102041707060201140112171204050109 83
    0x40c00340c200f20b0f81d442810000c00d0190a000c001d9550401041403400980e6040b4102c04940100203d6005500070b1b045a0102820141d0300c800307a1f0020900031051242038816000080c0c000030841e070840d5240e10744280c44210040301181c940ca400d5201241c040d00210744403043c842c1e010001c281a1a5003c0d920009940d5840343e5141030a0080d80131b5400181400018500d5010344107010300b0078414034004420180c1044054102d800540003a6030603903669041004500f0f061523180094144a402d00314201d50102c044d0840c2181d4201c010100540b00e651a4240c2e1213144644000442e0346040d070352a640c8440d8010004c0121500e0300162142800100c1c4880c1010720848102c6d407144682d0030410a124941382030141c00459000d9095035080100181030085150000400b850000140515501c1c041d0b000303080d240f407000b03450700ca180d00f040104008110080d51800d625404203230320307a052141100480c81c1d0301a00c0510800b17811413030200000c001040d0f00800540d0b100703411494680519 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 541327050 1250 541325800 541325881
    0xa0510030b060408030c0c0a060926011a010f1103030c0903120a080a1503082d07030206060a050108100e0402010c120302070b1807061407050d02030409060b090f0111010f0203 77
    0x2d100d685c0205100d5142405020bc00c0e5103070341c0a000704032000503103072030307800c0c0348075084913002c00e0480b450100b4102c5401140d80d00c1008100c070a00c0d1031600c4189a0290b40c6004d40760b12010309502d031718000000d080e060130748060100c0b1100c1c00040001170780708c0c10107031000b0f05003000454115400300d29101d102540c807a1418612025203400c00005030510303444516400080603103014200d10f0340c5d81180c0c800c20326441c4100801000d8841c0d4017412030b03030502c00d050101030a030f80d82000341403080181c03c1046900741410708000b00c601c4566a5100d584a0740010f807400381c028034020304003130051107030035110303940580062090504c2480c0c07406059a074140c92100c400c1003502c0901c0c50f90401401040464402c00d803400f51407100017851464030000f0354600b8540741c4001614005600007041c01c00c215102c5101c0c0600170030340d01e5841c500c2c01503000000740302003180c04512414480d4042d03803d08000d109510003644001c050398110754900303100700300e128002807503090708143e40d2280f400040b00700034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 541328300 1250 541327050 541327069
    0x360b091c0503100608090c1e130b03030a0c030c0f0b061c201206070c02100e0102120a050c100f0e0f121c14040c140a0510030b060408030c0c 62
    0x1500c96403610150a0a104413001174003d44001c0f0b06108089549245588541e0842d009400d144003e00c1404410f105000303010b890428003501241c03074900340091a8801000300c458105540c0341a4040301e01900d0f096440113401107001c2d000ca07000901c00b804020074901070601501080310303c08584100d0246d1800d442003100c1703004060a8400d404050013081c3c0ea007900c81c1011000b480a00c00c0e02d004000c0a2601c90201c0344c80c0001545c42d0310703020543c2090550003400200301d24202880183c0400041d5542c07211507400e01818500003000c1c088144940242c80380041103c3c01d4410303050781940d51030003a00c0e0b100c941400b01da00d0003022241d0001e0000f450501c51441e9070181c0707641c031400c80c6203610035000055104091030111006a41041c824401c1400400c41141c0340511401d0038200005052290b81006940140d08072740310340382c0c0d55044000303801c44004440d43c046568104c881100504200300015030450804900495480d0021002d03000d14590007040b9030a1003501c01c100183c004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 541329550 1250 541328300 541328311
    0x726030601020d050a0908010908120105010c050721021810081f020a0c0203070803040e010b1c0b04020d2c06060d030e043b01360b091c0503 62
    0x3e02c40f036002d6034924000e030060070780d1440780d0425994141d5502910703070950301c0c5464200c80500b000100303001e010426030602400b410007842c20981410b070a94401c0c0e91003216010f07000c08119070703189045402e185500030501c102e41c050400c0c120f40c0b40c9617600c092071203000e07914a0199040104045030440e00002c501040f00c01880c4010080710301c1c120b14400030740c045480042008164001d010160724100103400c0140101e100444c2c0d03551400f1070399074110381c06800400c10722a04014240780c102050001072000250f0036000a03c0020900014000788550f60b45091507e040c010035215804c0ca0220b01e0046030303906140b9000d03401011030740700d0f101e8604507503079a4000200310808000c20b210300b040782e040c41c0014000103005003400301e040035020900d200171281c0b40007042c909110180d040026a42803031480c3c0080c4448084904540300c845444c0c400c417a400c40c0d400c45a024044038134000529080d40092910b001804d0004415442da42d0710111862243d00441000d4040c910a00482c0d2059 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 541330800 1250 541329550 541329553
    0x603070b160308100f1d060a0b0403060203100801110406030e06040b01030f1b0902070302010b030f06010b2104110315010e0103031409091008070927080f072603060102 74
    0x701e201c1c1e4096540b424080d003940b000c1000d460b00414140c0c20030a11501619800c0309105840d00c000301c0306040b10f00024685406010b40c00010490280400c0607901507a45c00b9802580303030b40e18031303105800e01c07c05640480015802c0070103401d24108000000d0050320442d0390240400e01c0759220b0250344000036a030040c02d0012410040011031030705c981c00510075104910503015144240f1070001158419049400866800a810010103809128007130704a042036025240010000c0001c07915441c0c144158a0034060018000c1c0c40641c07910003105500c585d074642020f0506090070510000c0070a003869501901c01c40350040c1d0490428400c0342e048a0003201c1c0a1216070940da02110881e605842c50074500e0014050f0000aa41d4102c590b44504c0850403c05d456a20b050105031414426520002442c1d1401141086107031a501c8402016008592400c0d008003191920b00c0d502e103d4490261101030303001c10100d0070013447d140d90068500c00e0108001c1041000a240029480305a4149015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 541332050 1250 541330800 541330837
    0xe010f06080d0804210507060504290906010510030207080c010f0617031801050c1509120f090f06040305060403030e01060614090d031809060f0b03130609020310020c060603070b 78
    0x880d8160702005040c1c5d460410304040c103d075152001e84105030b508442800d0455840007100798501c80700c044030540f82c29422a40c0c03c045281d1500c40c44103004040c0200c201d002e403002c40c6030113901145e105a5018158594402900d494036001f4000c810000e580c00e801c090b000954100760504000c0c0c00c140d01405149003007152561140d1190a00421074180306080c040905800c90911100100c030700b21100e0000280b0348130103940e0820a407450300c104000403d21410405001c000c040e00c00c4514207440c5510080e80042c0015442c0c0503e071720080c00b91003514200b108042c0e1542080c0003084000d00244079503a00d6035401d50380c2076022402e1003403000052160401501d0046200071b03020b4040c4c10907002044001c002882c0d040e9031a084200d0890700c42104110207001201c401009001c0e0800d1103040d4100b0222440c00d15217010b50142c1484d865030203020555038184584070083d210454115a00c0649071142c0307442e0041100e200d482401800400030300001d54200700d4000c40c0b114000c41c0380 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 541333300 1250 541332050 541332083
    0x30f120127020702010306050907030b1305100302060d060902031f060801060507260a0f0e030a0c051215011202131406060a0905030f0a12020f060109020a02010e010f06080d0804 78
    0x3d40152209904041c0c5401c00040c00e81c4503803d43e00e004015540d0040b8100381c0c0a001d01009012581c0c40c0d9000518010400034075041ca100400244e990440302d4a075a070851a070700358083e09150b000000c1e5107100105103c14200b02d15103014200645049018000c1d82d10a001e0790388540900c00c4001150040190a00143c1509005600b014421080d000c2299030604210700b182c119821041c0810b002041a0300c2c04c5422048109908c40120018038482980342d07244e69008d005407142d140100e00510120001482c1400f400c0d110116030380d2903500a41e07485002d0084d0f22640c04081c1e0156402c12455030020505006604e0000c9801e2041c01568507001c0600c400c540c03201103c007042184601c00400c03640c1e0f041c0256100311880900408400c172140c141f031502442d00003089019540f00140400b5072100101e42c0c5811070700d03595030050702c039032410703800f607014040c805840001c0354070308442404480d20700d0b030004050b01d4410301283d50000300c408040e20118421b4030044c6c01e030107100c4031540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 541334550 1250 541333300 541333379
    0x806091e18100603030302090a0902070f0204090f1a062806050f04030f0b090c03070635040309030c0b0a05090420160506070305060f21030f1201 64
    0x481c0202060403588686200c0714410100c0c0d0407508210002500001c5007165860280c240d47c0c05070140c132508516002c00c0b5522010000d1019100900a07520303911210b06100a900c01840410f8000c406d0031a06440c2688800e4096000c99010784200604541d2650340e5100c404201130080d519284a0350190030301c00113032150341141591080e0600d04000100020b20300300c0034078000f50301ca401164290f05000030100c0c1490300c1c03098007a0107075005c2c0b98100143c40e0320100f4043c494458400d11381c004d510412410156076480d0100411459040c41400704050348840e190003180d00805803000160b4071440e01c10918890449001c0000d0b4040c0400551403406511004064400c81d0034100c40d01807107612001c0f2604081d8903c02950071403050754040c41000d001e030b9a40070101d850100310b1440c0c01c0c00000c4182c200c5400300c40c024900d07110031120980e0b880411521412486045989601c100c41440c55031760300c803100c21035914500741c00014200c120320758202d28854021400600101030b207241c25 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 541335800 1250 541334550 541334581
    0xa0f0e061314070b070507080c060d05091c021c0201051e0a02040f0602030a030e06070503040f140f0c030f0309010507080a0c02060708180f060921010c0806091e 71
    0x5460b140c0281218120b03049040000c2002020302c090000e45800c41c40c01c009041407010390044407950020f40d031240340d1b0f0756484110750b006461008000b84c0d0340c54100d00b6905c0c200010003401c10441054500c0060290002400501400050b82009000021041c120f00baa90309403800060b00b8101d0980e150780603055581d082e0310500c2c521006003015038446070502c0007403296000c9400358100041c000d02280d407501170340c01c4a520240003031406003042c003002012403000410180c20800c0c144805c20405c01001407403450983e1000803625600580b90b6081d49460001406512078443c501405c0c0f0503c401109550300b1041c143c580f18104480c0341c039101d038103500240d5040304021020048500603a6040041c0c98003602035100300c0e4603000724a99071641001c602080e1440790010f2207580860380da0b1001100d80b6854190f4889004e40704015501e002d403814181005880c1d402c0c040d04030034071a8000c01191094a04a4030481c00b5140d031441082418041000c0d500513031410340014051540d07200c000b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 541337050 1250 541335800 541335803
    0x908030604020a1215051003060b09010c060b0301150f17060f060d1202030a08070503040f1e02180714070c0e07200c0406060228060915050a0f0e0613 66
    0xc402c00c446032040704d0342202e101005560b290036000106005031704242c1300510b01e2083c0382c141080080d0910300c0311540da0142e1100103040000d9040f8000c100040d0360007400d2209000740080c000c0c2e48002505405841c1d6034021b03004041a0068005100c0000c198103100c2141654090201da0300c90405210807000010641c6421010180e155400108401c10b8201006c4c105e5001e151a0200340800900840c1c1c0642a0810030000740140404500480d8286514590249078102120355108100c01d540b03e07018800f03580078079824600f001c4940c00d40d12252142c881545c9107141254a03105000d003a0180d034101a0014440040511400c40010070407038026080f803d100018001d1121314003803480e2800705e044800c0e0009400241e4905040c0581d0005c0e020f1030002c0c08291001c80c51030300d048668412582004a1505818820321680d54071082c04076030024003008050f8050000200035060949020461a141c004d4110340048980310305c90303034012541c019210540304c98507083c6129111030b90 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 541338300 1250 541337050 541337057
    0x1e0b01030c201501090506010e0901050319110406140411130b0f16061d0d0203071704030f08030103031202030118020904110301090e070801060621090501060603021209010908030604020a 82
    0x2070180b0800c00742c81d00f043c0244001e6001103654900000010240704004211902803040c00300140080d6070080360144985041c045c4130000745200c0e00b0490300d1428040c1841d5000381c42e046000c1644040b000681c0403070001640d06020a240f4001c580d040d910400b11001e000f00440c08051001c024a00b0041c006499900526428007401040340f8032000000ca004699035640e80d0500c49240c50200e41c1c10400c19201e00103480f86050301c2d98043c0d184e109180c0300401840c10300046c1e58101c40342409440240d500308402441d07107101b038913102159a000380001d4012030604600b50075401c60368001c0324140c8070000c1c00e00400c01043c0078840c020790003441a040e805611080102e4080c941ea9014500815446c0d4000c9508180070144605041540c1c10092803039050038014840c0c2504004451304000c2d032a48030321a0181106500c200034941800c0080003942424000118264150094030f200194807a5440d01a22040c1406088480c0080000d0902c0e03010700004990b85001c0c2d01a0010300c81505 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 541339550 1250 541338300 541338313
    0x1104150305122d1c09110a1a0d0e060709081203240105070215090a05032b090b03070201060f150c0b130b100e130308010e06131e0b01030c20 62
    0xc2c901042c100c0c0240d1100304c5a640c0e0841c200f0f124000400107034444003a142130080c54100f0301c00345c40c00340c84054040f1502c8400180c0c85120426544407440c202420016a043c504003000000c00c000c401c0c2c03044880301d03c180080d05010603801c104981c041d015980682c0e8000503020b408044c02c40705207417450b0500c8021303c004030140c0c07582100309183c102041c0006980ea41100108814400160840f0b8007907400300409245078240c0c03821005000803410040000f0700c070800012a9008129003210020441c0401880501c540542000c1c2c2692400000980c0864881d01044080ca60500c2c4040000d240c450192010805000b80c0a0700540d541c1001d040e01001c603100c0090601043d9650720b618901e400e8100b1192015035000c40c3c110701c100030019407140c552f0f1001000b204040c0140042e404404000c50764694613030a881c11500d203182e1040c048442801000d002803107403480200c3d849030070040e80c894550720a10035200d00a100d521600305020031200c00d84003059200e403d4194512500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 541340800 1250 541339550 541339567
    0xa0216060c29150a1a0702090604090f06060f05090c03240d080c16030c15120e0d0905030f100b15030f0712020a090608041104150305122d 61
    0x90355010700c80d10a118414a1a801c080c080c048140306a45c400102da0501101010400010300225584c040d012100b5000a440304400a8014440c1c5400109054041401d1070204000303604104126040c5903000410140c2d6001070129102d022501102002c20802c00140c040140b1900103082500010482c1004030301d0b2408540c4490130008240c60f407500c040342c00c0c50714003800c000320f081e88801c0544840350700d071569407030141101c82c0380a00d03040201440b4401c002e003803140c10115000c8100090502c906101050740c40e4903100d0310781d420000070700c1640d404101e40c140011030b602d0004000c0028101400f6070140e001c01000c0c038580d110380c051080e40445d0100e00c0208040c501480b88000101900e040c40c1a0103000c0003c400e05121a044c0180f02c02492103411030800c0c8100d6215040031589580c540c0307080c4045079203400020b54858545103480218452034030700031040d41d00c81c400322480c1c464482000e20300c1c0e004081c0380070300c6480708240c07295850102d0307410480306d00403144e110742c10a0300c113 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 541342050 1250 541340800 541340873
    0x2060403084c090204080a0201050d1e0b0103050601080f071407060e0102040816060914010e03011103150402040e0c0a11010e03090f01080f0604110d050a020a0216060c 74
    0x41c81040b49030812505520b800716031911001402800601811480c1a20380811181c681031180000b905211001c64440d0282619811207500e007009040075640b49240140d00074000c1c8088500c2600003407070701002481c0d03940903852079401031060710030391a000d0faa4268121a1400020239103048044d0030302c0001c001131614045c81d010f0075590310015840c0c50425680d2450311000c003140454801e01c5500811515030030410300020b8542c1a10f10740b001c1920b00c0c1c01070300c4100303905002a40540c6410300440b0708400706e0000c0e5000d00307003000c00c11001c2600c100800082e8082ca005441e404000103000c01c1c13070041490000c0c5804407460030241c111064510006003101d040301a04c040ba1381000455801c80c3c42c3c45070140481500c00d00b070042c0f06003042c403025140c00c5d0005200c140140e0741d51206011a031a10026200b14000c040401d1040745424030b0358201940140c42420302521a000d041c003c00402c400081d82501c000d0b82c1c0b5041c0d030903403a844026851410220380c1c810f0b031000c0382500c2401c00c00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 541343300 1250 541342050 541342141
    0x7020712050d0806030d050d0203060103021612030c031a06072301050118092109080a0309030b09010e03030c0904061203050a021e070603020705030903030301030317070206040308 79
    0x14801070322400c040c1250142100f2001000944030390045d540800f60b0a4002050b90884100c08400580700d40e142001a0024811091203840382c0f03000442620401031003d403140c0744441a07039000e000c01400d40c0016410b584603405003011404c0c09001c03035200c1d0700708240a4010103002d840c594092a4501203100c00035aa100d403000416511980140f00d8000d41d10155030006558490030080c04240f91500000c06c11a607041103035652911028030300c6944507440303d07409011303100103840600001e031a0184c6114070070300c02110f0008a210001c0d107c3e070010311800c0200f80311840514999601d03440000f9056115240107130348580c0e074078800700742100c00b040b41c100f240f40b094454981d00d6181e0b11001e8030f06402e00001214400790300e40c60721110740f4041641000c0703410031b060140c0c60b03600d949459070540c02560354998052002100010a16500c00105407010030f00c20070300d44180d1514003003240c407400e0845020b0b01050b003050100380c6821340700c11450750f80b800c06100641c1002e042d2015031740f180d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 541344550 1250 541343300 541343303
    0x41205010b040501080d0f0e060a1b080409020c0f0c1507082209050609040201020d0c02041b0f0f1805120f0106081b2e110102030a0c0f02010209130507020712 70
    0x9206840c0c911425421411461f28201c06007040c100030f03040200011460f10400b881841080011061a00490542083c0126441c0d01454958427140c89001600080d0000c2c01d03440003500c201d9241d01c0451101286c45501c8042c0500030162006034803034000c825034095041220840c2080054131103409641c0382c2407995056104010450340d00c1c03d0107002c1950005040103104084040500c030050307070005290120194241003e030f080f1140b03400080d006001039900f0801c000c29250f040141190f0000c40b603032032044a6101da0104590b40c210840b550340401a007264941d0f03110030107020b2854004102c0c0b0202d1002d400b11807035038800c1c4502e182964034030340c0708100c10f5100a142740c0514001260300181c0304000d40f80303006c0d50035910105d149002001076003400031040380d4040b07558051141c080a04040303065002035640c0d007170001c4418002c10301d0740041c2c0f00040101340c40342c0750b44d032040c02110244400240f41030103d6402e01c00c803e00600014180806503ca50500080c0d130450492140d000d09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 541345800 1250 541344550 541344553
    0x1505220e010e010b1c18051e06090d1209060b271503070b09030a140a0b013c050a0e010f1505030a0b0d0b04060c020d080c041205010b04050108 63
    0x3945004040e4100c6070301a009841000d000744850f8a41c00b0a0000800440b107061902007641b1a40d51040f200c0307201c902402401e9405040140c1403e81c80404081440389107160403035000d6628981e10742c5d00e6441d0141c07a42c0000390010707000400400e580e00305200307040c001e44001880c400ba040001d8008204100502d00c10501e400f820201e0001020189601204d420b90300e0015105143c0003d45442040c02282c0301c40707501061a62154074200410001141e00144d90008901d40750a42661070720500302c03c48038038601d43c0012074005403010424078034150f004a04c000514007441031a1920928803500d0007003030951100081c0940d078015a1000800c5003031031640c3c003075040214103030300030100d034103c00c407600d0302c40800c0c0c203180342e0040459500c140141e00015034101c800740041c6c02d800341c161000d0440342c443d40a1009004a540c040c1e403480d8a180c00329000b9524519043d540307120100c4004502a400b800104a206080340c4400b40c003030703c100c000107030300c20b282000203081302d500381c20001d080e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 541347050 1250 541345800 541345829
    0x315130c0305070e0f180411040203040b04110d020108070804050a06061e09060308031b0409020a0503090f28080d05040f020108010902040f030602071104050a020d1104150522 77
    0x8080d04158500011441505e0214000745d03200d001c00d4844a8443d00c070b5030341d42070b8080000d080c8442c10407941c0c05000c00800941d13507410729082c03c0001c1242907400b62140414400741c000e4514040100c04c1085a068640b0303411035490700d4043d1003c01000748280c0b0b82e03001d4401010005146c034803c40700a032190100703904980070b65441512503000d640e042104120b03d854000d2000c914081d051b00d60121310525407480000c0320103240d450318090380c2e2210422600104414075620b802c03001662040042c1001c035a071110082560380d581d400000314104102c4602d506903100480748010040b8514081c0080c90b28040c14200300300e00312802101d0036140640f1001c4110110744e03001d41c030b450041482d541300350300f01400c00350f0311059124907120040215500103400c02c1000b200340240340d0b00050080040080340307429500580650f21403030003a150b051510020304000c00fa01010f803410f55030110a0158458640b83c010b072015400044030843c076008103440b03019410011041c4d00080c00d1000303e802d85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 541348300 1250 541347050 541347061
    0x2906151207081501020102040b03010b090a030c0602030a110a0201120e01090b0903041706010e070f0912031106061005092404080d0210020405100e0f0d06050f07020c01050315130c0305 81
    0x3c802d0301058028110390042008010b40003071401524151303940c1c40031031961280c20300300103541040f80e070b40010f1907400c504030b00103a4035801102402e0b030300d20180c59480010707080f51011a107aa0380044000c2c00314410501200002069502c03040462444000005200c00c00b40c0320701510010031038414416900004060020204000d01c41c820986c07000028012941482042074070705a00403c03a80030805032006112103c0e120b00c81e000002c00c2d1035901e000800c0b80c1810010305000e01d240005d0000e1088402103895814401900b0b01c20700041d603161410001c10104015040c07207078604200e00a0b110148512803000b81e00000d00c001d0009400078801e0020401c0d01a080c101094507484080b4418442000f9a440321744461f05e408039540f4006110783c000b440041c18002c0014103c035046001511110104401a409070b800703200e00581a40d0385a9521508036500c40355014114000754040c804a208550034056940e4580001001403ca4800c0c0c2c030300e0700040300d0318400c03060002030310f6006220303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 541349550 1250 541348300 541348321
    0x1103030c030d0e1504030c02030a0b1f060f0504050111070504140403030e0c06040905040302010608070602030a080f01030c050d0f050a060209010e100f0f0c050106030b0103290615120708 82
    0x460a00400001d80b415406644d0000000c440082c0301500b48a00020b004c4110f580600400e60708503440b0342e1114031824484000840082c3c5d1040d1401501da03d0000806d490f03025103000e0424400e41d035034561074582004011946c41d2450300c1c28010520610b440803800d0750751030043d0740140900c980960007925160230000c06440010110110513048254442241d8480000b2a81070b1402e0080100b000c7c1c965181c204d006203e16031010400d40210389011a0866000c0010840c540e1035540c0e0300041d0319441c1140d611980b00b03110040c0340400d030207020015400c001c400c40160a024036a03101d000d0500d034481c20704100c88040100d80707030369000450020942e0400c080c1040c2002c195469058442c0310f25000e0305141105404000344005060901c0310203111b10f10407892740364410001d0014a81d2131030b149403103404c00c3c001180e03000040b1610761041460f10140059240030040c0760042c0d40c4440c0140819094421341c4842c881904000f0501e050140c4003600780214110b6440014034581054600c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 541350800 1250 541349550 541349561
    0x509031507020a1502121524032d180f1b10170f06030705030a080301150c03050f0f09041e0e010207030804021219060209090a02251103030c030d 64
    0x81e40c0c2403040c41301c0c0c01d051115864071a07200c2281968040940220800140e19402c81c2321400d202841c21990b030485031205c0d8001d580118900405610300316140050400300f07860a107142141d103906000000c0114102d61120326031012088281c0304400c00075110b19082180e980c8020840c41280325111001d41801f800c40c1c00b4505880c64542c42d404507558034040e003c43c0280c120500075000b4404204556824402080140b10040880b80200181d1034070440c00d800034459800c480e41c9030054805094002d001644a845d030540c1d64500e00f88201200e50855001a07128640d49007052200b41b9042c1c48038403414200da20050905a0b1588000044000b42e4000082040c0e850b4014000400006d8110082d145c2040e41141c82140441a0300c42c040d1400720314a4040b42541c0e0218030032010300000d5402088100002d0703800c0040e6a50b0101c02109170320682c040b644950f01c0b51588155020b004108003090036114510001588504900203071440e0003400f0600c0340c5400020f2354940355066803254 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 541352050 1250 541350800 541350833
    0x82502030c0409110108040804120308040b060907050f0d0216050a05060a0c0905040216050118050f0705010504060e01020a060608030408010b0d050307020603070507081201330509031507020a 84
    0xf4400c2c1d048079a9501080703141206003905000024020800f00010b1605031805403102c100041000e2000b81401809620250360070340f00720401d00c01144490402c1040da611840c92512a54a0020542100c2030a6070000c0c00c21030009609004026003079007068458840d0074000e000400003035815081241c01d18902030030551031645840e40510005402080d0442103e2040760016200c1c0c0701c002c00c0c4d0b840844e0025000b4080d502e84007581502441c91010030034440c2c0182d08850600720003101466403002c160190324040350045c00704000103441400050202c0c001032047e02c19040c070f00d595120035101c00ba00510a81c0e040400c1c01d00c101d509c01d00c6199904402143e01d0420481d080d151144c80b40708116010307005030400000116401c0c042c00883c0d2542c0d82c400316096641c0000b4100d140001001c0c01030711203015070301280014070320800c041c0c2c4020445c0300342c1540312955040026502c0da4848803202c0d4040c041c001c03c04020401e01d00f20a803007105141c01038803c5600a18202040700c5041c01c9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 541353300 1250 541352050 541352059
    0xb0f011d070207031a16210b0406080d030e0d0905060d021602031e15040c0b25060603031b0c231302041a07050a0f031704060c02060907031707082502030c 68
    0x40c0030312102c0e01f00d0085440e0701d06402002602c103814001080240000383c00002c440e106407c00c00c07240720b0381a4001a14140d852003614402c1140c10f100f10b407a24840d2162541c080014010607080c0340c0985e00030860a16802030307854100010b94046030504040e50326080e16046826403030042042c0a1180e10003401b80034441003a80c0c58641d858402c154500d0041144e100d4000c2014110300b68041c0b00328a00103c0504d0000c010a0103142410117001103000c12800283c600303a0081085480b4120000043e5008042c0c4000c00d040400e14000190301c1c01d81920800d601d0001c0c58604d84505004a1505501c010096915420480f80c4644040421110b0602000800c06080071030000320f441040700354000b40d640c4050000c1c2c00c00715524441003440d002c00c4110310080c00708010555000c4646211950296115036842010b803a03100d002a20001d06501c0c00e8089580c1098008001080a04d2194bc4075500b000c120b07041040440d1101c0c1c4020051000d007080c410705601c1c0c02c00080c036400d031040710b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 541354550 1250 541353300 541353317
    0x141501081308070f050f0a060e1231180902030706020c0102030301170a080c0a02010210020316050714070f030b01090c090b0703030f05070504030b0f011d070207031a16 74
    0x19100b49072071046a502900822071204000c04100c0c0c1800745800c918a9801180c1d00d030b11140c10b100d07006052550303155415111f29040140310000e03410690b03002a000903000300d00341040c05404041c1d400e40f0394410044060a06001c110f4180c00d1840492850108030300103403195540c81414030740146904400155442000003482d60b80c1d00000300ca0551360740c040d4035070b8546200c1d41030300d2401c142d03900014014280400d410f1158000040e00c0c12851303000340d0840d051020b00a0140d001c038072003900c03c00ca0b240100885210294041c9000f001d065109420440c0015107948a02d0f0a000258100407000d14602d10204281315880e8925405000c049504110001103c3d5018102070200e10500300040c2012402d0022705000703a00c100d000c400c2c009818403440c0b501c220003e003681d10500003150820341d0000801e056001101880c1e041e5a00e8001044212098031641300c020302005215004500c0307a02c4022000920018018003c810300651078661810000c06904604820a04107000c026591 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 541355800 1250 541354550 541354553
    0x306060b070f030f0e0303040e09010b01110309040b03070e01030f120305060a050108091f020d1a03060703050c0d06060903110405060d08030603120c060603120a02030d020d1415010813 81
    0xb200c1900c42283c2c141401c03000c01c0c13448441540c030f4032889a03285500d400003050000e8000c850780310f0240320b40c005100070072203601c0000041d202d9404d0541408010390050011140504050b8028607007000014215550360795520f09440f40c0e500c091f042104c003460300c1e1201c1070400c2144e416550070002641000d02c110325000b4041100309845100d4141002116408242c84c08070500c480200109801060741c68000c0d2410441c010303502041004000d20302d4040041c0c03244414520182ca0130784010050b0502e62602e51046014010140400300100d8003008401909441c6104a81c0208196142c1003501071440c100a40c100703d940e180c60740103030b00f03000070400969114400007000075400b910060312612400082807a060804403050950240042c40130091040014414842d000460407155412100c1200c00880d0240c4843c85015900500c0309504499281d0054822000380e94800a00c11581100c91040c641082d64880440103c42c50300e210a9680081c595900100c000243c89100016 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 541357050 1250 541355800 541355813
    0x1a0c0718181505060d08030901090512070203060a0f0b060a110c1804200d030216061e0302030703020f12062826070e09011406010807210c090306060b07 67
    0x2e602002c84015620400680180e903690016201c42da002941c0640f2450503999a60003000c203203a05995910070070440d1041408801c0444d00481d5001d0050074540e115448144064031180310010505d40d02c4940e240341c140c807104080c2050011960790b501801c1000c404050414807540381007401902c0901541c0611948440d4564105505c081079a4100700044400080c50181ca0045030388440040031140916500064807417580d100c0745900900d1648c0d8900a4400d0000882e800045c807090400c0c48100900035030255920a44034103015103441510400050254420030a0701058040c036011f10085061079907841d400072421807805160f640c50210380d80600760b41403080198110105180341c40032900088410003e050b030200700c8181c151100810701c4803203011204510a50f18041d070105103442c0e0410307020b00846041e1920103494a404400319060803407060311020351031060106007464a82c0c0c1c801c00c019003c0340c1c0c1d41c01000f141503140c03603020b03241d141e4480400b81e2014050100800d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 541358300 1250 541357050 541357073
    0x803160c030c0209090703170d0501080c181302063910110c030705030703020f06070e27010b09100201020306060f03130b04082808011a0c071818 64
    0x101116030301c1c000e1345c40e650303940d01d4500d040d00000d240c03400740c3c003001c40301801d0000503025640300c00005000036071300d52a0040e13a506c2c10142e060b51021049500070500b18030729031001d0704031030303000070710940c01019801140c1280e01c178000071141c012180034a110380c5c1d6000400d8800245070708880f041d1030a0281d0055950702010b40c680942e45d9a2500001c0c594038003041128001036440f4180c3e034a500791824101e840ba08005001d80c00340c001d0882500d0001404944244030725019180d0b04d01100c0c00f0024032501c11207100c880b410205080e480d94061584111316a8024458002500d40d1410600c0034031203031101022508065a0040c410321048e82c0e654002e99421038040c140a545030350342d0351111010102c9034403029000e8201d400900003403002500051104c4042d00700104040072840b0f14034580303820350f8561040080c070034500510210028080d000500082320180074102070121014508050055200e040e000c55003207490510000240544064a0500400400d0f10341050322486081103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 541359550 1250 541358300 541358303
    0x91908010908130b091f0c061d0610180b0609040e01090309061106010b09031c03050a200702120715170c1219020f27100203070602180d0803160c030c 66
    0x34038540d1b10b8041d214000b4401441d4102c00140180150b581e0080f00c0702945212100240c06007800003482e41000902c0d05003250b6006801b00200d41c04402c0e41d100500428280551003101040051400d91701d5001c0d12101c910700100000d0140c4451402610345551648035400b070001894441054440c0451403504484484e2901c41c0d1741e0151500090414a90a01c548d0010600c640307600b42840d030640c81944a001554001c00ca0780c104c441d032502c1502020010500c203008204447d90060030040c1c20421022800404c5650141d101d81c603056801131060071060000b098042d000c1088120745960f15007150a0071000c0340340405c0c01002005844d401401302d070411a18011100c0e011001c0d40c11039004c00242c588003600c8403a43c40800c3c0d034151741019031781d09101c034030a480d002078903200252103200c0c03400d60015071400d000c5a80310300207500100c41003a0702041341d00141c05661182c40024880741d11a000c16039480c50704850011000d4002000c90040010524007213000076006461102c41340d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 541360800 1250 541359550 541359589
    0x21f08061c02221b030c02150703180204020a0309150612020d0302070807180b0102070f091a0a0602011422061e1d120708091908010908130b09 63
    0x30b4500e00d80200d002d450f600d02c01200b490201c503200c90444201500d00c40c0c8800b6901031000c840041400c9130741700340701d02d0810940d861800c08255214000d1780300c3c624030300520110044000494000030300300d0704142003283c0402e031980c2c3c0550405c41c02d8620251102c2ca01d00303040041d0350420b8050700c4035107111500240903440c0102c0c81c0c402d0500170801c010007420007a0455010341e840300f070f0741020880342181c0c0b00f0346a410411010301e00d6002103a140181c80803c42c0c0045240d1030001210080c054081c0c00800ba40d110702d0840840340c940b00c0420010702a0b0ba0004030f901c2010040790501280005d1040304401c407180c0088a18031080b00361b94892035080a4040f602d000c02030450003180c5c4106401005041c03074000c040d1028407610049002c01c0150f0410399802100750030b508911480b40040c010715820041200103010f18116010401d507a205605a83d005910b41990508607a6008c0c13056503c04801f1138080d100301e040302d640c0c401501413900580d00341103c4001044602c5044220f08600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 541362050 1250 541360800 541360819
    0x15140417030c06280905120d060801150501080c0c0705010f030612050d021b0a18060b0706050907090b18090c030706050c0f0703080d020702010507021f08061c02 71
    0x6030241001528102d01d159019241c660900c9054030524481c0803540214010b194440c001d0010124411001107981100181c0b440c80300b0204c10340d0503a440344a09115003583c812002c00d14101c24072644100a00c40f880010340c00781003400141011400030482810361000704a1420b641001095450441d402820502c00c80415068183e019201542007032007642403004182080c4000014441d44403420744e002d450103490038803000d4402440080c40c071a041600020208404441081100c00c810005040010015105c004d41c0301c46501c0a082035882c292100140441c5030b10501c540380044ca4200303010464400d0610101b940002d03101200c660200321100003c800360414003114028140c0201074807603568407104054401d4201e9a4042c0052140342c0d45003c01704070000700841620340041c055410305000c2000c220182d8400d85080341001020302c15400140c44110243c0c0c0308a241c811030350a0694802c20040c0f45400051500f071150030400d401c0060f02900c030030003550241e015103426030b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 541363300 1250 541362050 541362089
    0x618030a0507061b03140601081b0f071b0602150105150313060f09030215100302060a05040f030804030b060102010c1b02040605060a1815021209030f0a0606151404 72
    0x38144040f03000b801d07205209030304002130350546c4108802146030828026031385400004495000007103c801107a0700000100e4000c1e034000700054000e00c42d41c481d1030b501d00071095882680c049a81128000d20080d0700d881888020f40622820910841c2d1044a204542c58403000403001d00c020000803000721000000304180303c0704914508001508100300340302c818061034410001300000f410075001406141e6441640200002605001d1070b800c8202804417400c3d5000c00000b58850480001840010400081c80700903054224004500403911240c0b0b50303186050000e000d00e0010256411649440c0198401c2ca41020a105031212505a1014881c0d0303103102040090000c0d0704005d030b2040000c030791031007070325400411403a080141c0381500950a41c0e810103440c0c80c0c420300c0b41400c05038010030f4401c000c9800100203403404c501d000f4210750700034044000141c289114120b09580554490f1424410704260805800c03c2644924000340042d005402c4e045060159008441e01208003e08032117 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 541364550 1250 541363300 541363313
    0x90c0a050307032301080313090e03040306150305240705090d060b010e1c0203010c0c08030402061e0c0d08010b040621060302090a091a0c0d0c0212040311030618030a0507 75
    0x20780d0840f509080005561a041030036a0394010310440c240c05001414040f0b49c3e030680b0701440003504042401507041c05d007540d94400140c80b04801c2e509000a48102c00800304004001071480c10344441c0c012020120072003400000b220004004100b1f0120030030049038262114200714002d6900303e03500040c00360380000100c44019104685070381c001c11100d0301d0642203079002186460306108034020000504c6d00041941c80b04c03101140600909024000500941001c1c4000d003043d4500000445842e20104c0c000f03900340c0c01141b500307085940422580010702d600441c0c040e001d011000915800d09151130130060551030442d01e01c00e41100a50800d01005c03805401c0b10340516402000e240062915a2005006180e002026281050201c041c0e460860343c030510180105d2484041e1881c0030f001d04070700401340c0744001c251341c1184280200102e50403052809000510b10810283e85001d090b4402c01d031420b0000707003040c8101b1040500030304150100102302c4030300240d10300305262652007505028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 541365800 1250 541364550 541364591
    0xb06180403140c010606031512030f05071b03050606030601140a060c06020906030c220b040e040f02270108030f03040b0703090804030803010501021e0613060e1605090c0a05030703 79
    0xf10080d802c1c4403010480c0354058000e036420518200f02903840650782c41849401e08450400a00418490030806042c24803c0000b040940d02840121071040314100d4050b03400b0542d41e0042e16140c1101d030911400e45010700c80c4a0040c448481c0c85200d6080c0d00c000201040c13064031444080c405140e401d98104201a010344d0b0460391700804068482c9421003081241e54003a10407080400101d1800c2100c0c24070192076030044c0c03200c0e40b07034003801e190a02c0105070306c1c0500503009a80b001e07900034514006035078007050040200c0c400709101d03281054000309800305c03610603000801d80e0741003803161410341030a14007542c2d8055040740e540c0b070894030382410035002046052006404c040d0300080c04000d000c181c1c40110704031a82a400c07600d02038841618600520002107084c0015080440407400034000c10306030032030750340c010840000c0040b05516250324003102000851a650314241e0700700001c0c9014030010740d1110103103d001e0320304600040014041e102c0105001c050603a00c0140da44022400b1423003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 541366906 1106 541365800 541365817
    0x50c07030c050c030d03020405030106230f15210603011802100e130605010e030f060f1824070504030203211c02070b0618040314 57
    0x11210a0320700401507a080c0304080d00318071682d0741441400c604500548005039110f1420003414255606075000e100d50400121000c2c8075114060903102102e01e0403600c41160207203400c0041c101c0540b00071084111310011502c00074040300076461540f80380400c0700180e10740d0348000405080e10385100fa403074581c1340392107800001070500c200108429040d0b07061030080003a0800100e005610302569201d074141d200c650800681d60481400600740b8000d90142c049a403080300103030740d1a0005003020300416880800a030007203607410281803090000c0320030748650180f98010303030104107050340700b04c0760150306400481d80b0a0300034030440301200d9026000e44003000012030004001070201c00924040101041441c280c0c0c20414014013002d20600750058460704541481c02480b44001c10890150701c421b000c5080a40705011031075405549440d04e0901e080c2040b0060506001d200c15 = true := by decide +kernel

theorem cover : BRFrame.Cov 541187050 541366906 := by
  have h0 := BRFrame.cov_init 541187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 541187050 ≤ n) (h2 : n < 541366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
