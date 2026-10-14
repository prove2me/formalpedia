-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0406
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:39:22.286318+00:00
-- url     : https://prove2.me/submissions/91e14275-5acc-4383-96b4-c6f2af879e18

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 72841728 ≤ n < 73021584 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 72842978 1250 72841728 72841751
    0x601030222061706090604080406080417030403170106090605030f10150e010f1106041103070801020c0a0c06080609070318060504060e16060e0d02150301030b18030f040902030a 78
    0x79903060f40e124580d031800320040d1801c0c4050501040c5d50080b80d05015094924103540d800e2414000e5001d00c60810046d100000c042061401070041c1400488400315120f02d01450001c201c03040724408084000c0c40e030340000605d10b0290040c10160f40180c0c40702c9046076954400410f40400003000c0e070843d0244c10304005809148051590407080240e5612030244010300700150400d8106900c501c10004926101142d1141c00f085041c0c006a000c091001d86074881400030380303010440d801040c07840d40b00107241c0149280018560588900c44d51031601e56980d10384e000d079403d40084840301c0e00f191a24001800e114480c2d0b1000590071003110303060075022100c8d00c43c0ca0480b1004c44041318910307640d040390600d804080181042c2404c803100004090b5003041c2c00146250081181c1d40d014042e00c111050855880900007001c0c2c1e9580c1200d40d403a5a900d0a104000b00b0003900c07207549034040e100b241c540c814400301c212801c881a1045441c505440c0c520400029880100030421b0a541c44048000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 72844228 1250 72842978 72842981
    0x207170703090905010506040b0304120908070906030303060e09030a0c030315121406190b0112050a270309050f010c0f0605180304150f0c0602040e160507050601030222 74
    0x180d074000d541c1d038440310b41420180700c111030040e085203100f2401440108103403221102100e5010754842c410001d0800c0345c43e019522105260841c4c81d0300e020307610300880c024607940e00c0710007100c0c000d036400d00041d640c400000ea481c010a0703079103481f2a0020061701090701d004111140c8421b110780b80000c0d441c90101c1480c011241503812001c1390340b481543d0402032060070840c002d19a40c2a8024241900b0038400d90180d060ad118050507400d522002c03111b2481e0300a8a01e69901a81070760180102c3c130f80541350030003c4c9104050003420f80040300c80061182880d0802c801c0c0d45501d9100d04803494200002c0010600c050310b052810406203060010020b0600c0301d444110500c00d40c000715080c100820715600590404000e01d003540d2080c001085459603117644910590a00d0405000300084080c00320361030350291201401e05400060000740b00480c069841e8464122000341c0d5a400d601508101c0c0e19108605010705150f00050040c005460450302e44030501404003060780c10111140c05580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 72845478 1250 72844228 72844237
    0xf0f030605090c0307021002210702060609010510050408010905070302010f0f021005191a0330070515041109010e09100c03060801060803030114030304081b0a05090c030a0f0203010f0603020717 85
    0x584442d411949c3e0700c80303101d481a8140c01c00c84c28006481c403881c00f0008202e020b00144101880b60320082041501c2a0140b41260060700e0076000a0141d800c07076003000c0343d454003148000c074000382410404002d0380b0311031004250911515405440f4250750941c41402030304000d40b00421240381e840420709107080d00d1140c40b50541c0104103900d040c1080382c042600b45131042e8008002c10509501440c1030341980084003103000f200044140c4c4448050400c02e145c0000040044d40006040c0c0c180400d0018070750040c2c030b004400f05d900e0b02c000c0e83c079500f12042d004000c0c0c0b600754450703110030205100d141c105e0b002044000c15602c0c001810669680d0b00c1070075210070380e0140c1c5582d00004014401213000f102ea000b10040161b0086103404e01e0500025998503580200140f5a6aa1014600c00e0398501050b200144001000b03440f081c10020b40c25030450780252011a112172602d44000400400c600a403030480e0f10b60016891083d241c550254042d5000c00012500f1544044a0244596400c000b50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 72846728 1250 72845478 72845497
    0xb0f0304141903020d030b0405010f05060c031b100f020906040302010305061302031e0105030706020604171207030b01020c0103050411060a1404081f09020d060e0c0306070f0f030605090c0307021002 87
    0x3c01000440e041d01400301c4200500c135502a2741800b006010361644019034030200c4205803020b50f41e89007600c50603070a40c018644000301c0201e4400010002403400281d110460051002c208440c0150603400c038120302c00c801005421807c01c0c0800c1003d58081d901240c2d0019028104581e01044115254101ea10443d0030114a040ba00a40c07941440300308031a9001d400f041d401040c4ca90f00300b5001942c1ca06000704020079008100340c4003030210901c841070704e000c5c98540c140035180742060503001d40078001000070b82d80140b04818000c625503120313004450080e60081d400d4400c18110700c044c0b14440c6d01c6060324200f40040c9070310003a207024405008100805001c1c0c054103801152542c40d084070010340742d100c0e841d141130001600241e41d61400980500b43e104000140b403408500d601400c00c200c0c04040c42c0d040c050001080320454001c04070080e0191140d07079000d45610100c2054044640b24040e064228050100295401ea100801181c1007443c03030040700c98090903101070784260380c000e4000c0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 72847978 1250 72846728 72846733
    0x10816021507031b05090303040b090a08030a09030b0a180308070302160f050607110c0f0d0f0f06060b0a0507020d050f070305070501080c0406021b04020c0102040303030e070b0f030414190302 84
    0xc40400356134a200403080707854140703019803418000f00300080d80d078060784c002c0404030600056010607554481a1060003800e10303d041c2d0351100d1828001918200640c4000da4140142c080006c46040e40f9104111041d03011202c074a103e49103a4401b2901c16000400301c0082c0355080042101e0700c100d010b14004003030301c2080c1c0641c012103d880c01d903003480d601034401414411020030145605401244022401000b41c1e1442c2c1005d5120001407070035042c52030003510303002d204003454040c0900701c50122807540c040e80c400e11005a6800d6030300179501c11042d207100010014003035a001858410f208029850140040300c3c3e0104000c100c1c541070414946c000c9130325521140c2c04022550b0083d500c60b0780304c09204030550400c2d01c2c10001030f441c0c82020740c0501400800888202199440b50b05031586d1901c404000c548403600c918001d8018040000001e0325480307410f800103081e1100400700c030200282e0f810681d0a40d01d03117964443c80031000d80a424494080c041940417848400d0040082c0180217500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 72849228 1250 72847978 72847991
    0x7020705061b0709140106082502060f060f060702130204080102040e0411010201020306010e0d0303060801020f1c0204060e091008190312060605030c1c060f0602060901050601081602150703 83
    0xb08910300340156011240701c5081180200c00c41c0c001000d0701d41118010706043c0740350394542c41003910800705c1e40c00e06010082e1000422030000e60000b1841c0c45004110016191f0b510386908000c14806664070381544002c0800c076120040c1092301c103561818542120140c2459100e82c500b5003603801603049801a003124204010178052504013010391100280000c61560130308100007001a10200c05a40c05040039400500405110740c0c46000101280c1c0c0c0215210841410301e54050b074040480c601c00f26507061104103004145100b12011150107854000340c200405041c0b060f240c40040950b60481a0010300040030241800a4500155031210808054032646005410044842d800594040c40e1210074001c154101080f00e4100a040b2156621003025400e00314980d5405920702e00c50f41c3c1484000200200000b03d03200c00d0341d80c01d4090b10200c0d500d19085900700d8a04443c039078000f4000001048804400005a000c0e019071403054502035030304015241d808507002d6030340ca000139580c1e80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 72850478 1250 72849228 72849277
    0x203030415090f0b030c0306010e0349080601090e01060305060103050c16020105030a090215031b0a050a12090b042d020904060b030a0209070306030614040201020d03050702070506 79
    0x40c800090204000c0566006040142d0501c04e800000d1050307201c100f0010100b00241e0054a52000144004040b071b02c140341a01d042000481c04c882d007089031a10420900c0f10000c200e01018000140a82410300c1d6899062004847c80000500040d0510038040f0011907030320f4280034028040d001030b032000303d51401c00b08001001c0700c6008080c03d42542050102406505144024400c519024640642c83c0e499004000c00201540503000303501020340400181110f8126020714400c80d00e50b102c104410392040500c00d8180b082c0c0c038660001603420000d10040700d0048010b40c0e003c20030504002020b140c3d0f41e0320101114000ea0381a202200c04218407424200c40c45e9030380c41d40003000300c1e4246a491065020400e00030b4041c10041080341c0341c1300c034002c41e6101080101d0b04590018883c00140c240604041c0081405000a07235890382000d030050f40007080c51800c07034000c65060703004110800c481c1d00b040b001480094050001c40c0501100003401e65a80c6015062021400924a5220900c0b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 72851728 1250 72850478 72850487
    0x1002010e0d0f050703080a020903030d09021302090306070513090e030904111c110c19030905010816081503030406090f12030c121202030c030412090806010612090203030415 76
    0xc41d1050401036a00807541d002948041594101541800c00b1440c07521040c003614040e014a1045540522012841c00d03030719101c5411030000039009031070710090f0782c1030604c8035030691007440100740e019030040c0045107407241716100800841c004408408941501c442000095680840d0445031542c00422507521a14041c450082c5503020300c0380480c58150041828100e11802c00001240d155aa040d03200c6600d808404070ba005000c01300c01e550713100414214401401d01d08400960001e460303e00c02080e03030b50081032054051f40740301d509402940c41041003200c42100052100c000d6031804590303904540c81c200041d002030a0305443d0034102c9410001368103a00d01e03903940000070541050383c070180440d80200d1014071240e0405402071000d100140241c07201301507501c1304c017050341c4000100001c410811020f540990f114000844068114000846e0107415900070800327a6084600100300d814015024090b03d43c0345807a01180040c050740020f4155003007603003c0c000c200c0c0f91041280115501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 72852978 1250 72851728 72851743
    0x111305030c0d05070b07060609060b0307080a0203010302010905090a09050706050309250b070f08040f0f051228080309030705010e0712080f0d090c030b010b18040c09051002010e 78
    0x7540d01c6501c0b110940c60701580c8902c0c510404405c290009000e41c2849082d4200c0780c00381046c4501071001c540c2ea882c0942c280e620441e6440001484075010900c40f180d00d0085a04a9030140d440c5526036080c2002c028013050050255040159903410403c00140c0a01150b0018001a1036043c4c0303903d08032040e542440c002c00b20710403001d07901c82041022201040401020384030100c0400c1d494482138078000c81c5e16000072401800b501030100b40058401c01d450112000d80c1e2072010b4410989a071035046c01200707640d00c04090a2600700b00010012090308402d509002c0d040c010005034602d43e55221640c0c66801076419034141c1e040020f042d4180002401100c40107961803001700529460016800e0590315120f000401c0c0241c00a8150101d21102d070076140012001035042042c2549440c100000944600c41180d40e007500f8000003d482c42100141c0d0090075915030806c0c1c0d25035100341001b009115100d00c0d0814000f00400219050312124040610000640c000240380c005407c400c40c90b0450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 72854228 1250 72852978 72853003
    0x81501020a17030405151603060504050f040209060f060705010f0b09010807062d020109030201050f060a090906020f030702070f050609061c090516290901050d11130503 74
    0x21a00002e0070100350707005100e1000203040d180e440e2842c0450500070300120410400d0728180034000f403491031400e00d072041c5020b03881c1080469943c0080c0000c0d42d1084800f076894040d010700260240c2000c044d07244c4c1c441d00007403038540400c0c603150000c1c0185d0480c8006540d40d0399a180310042d0009a1b1181060141086454030065850082d000b99030b1107450181000b005112103400c03500150880031002c04c00306c1d48200340030120503200028000c101d02181075005600f4440490011800c028000740076038405011400110b05051040303001d0301844404480080e03081104000c4000510301450290030690702400e141e41c80c00504000103000c0c4d8201c903100340d8040010300c080c2d03901c00f82141c4000143ca000000400ca0050511000701441c8134060800d02130400d600c805810244054410f540c01040160f48208490780741081c0d030307100400c2003101403004110040407507010300054034800d0b40040010a0002144240c40030a401000000000c0c50b805601444103183c1070110000640 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 72855478 1250 72854228 72854233
    0x3110d15150501110a08030106051c05012c0606090d020307030204020f0705070b0405090a1802030709020a020f0c1c020303070c03060b01120c020d1b02030601170706110705010e0105040e0708150102 87
    0x170261074940182c4010300c03800041c040002450900404403252403080710520324010400396130360303100a5146106010007106220303410280303008038101a48149010f1000908100e0600c1c441c1070601c010907080020030399042c825000c0020040c0c0d01c9000030a8290110081113880d174002d450054508007090b044100c00c03071750500040c04180c0341c200300c0580c8000003480200c0c6145422000040b80d180294000e5058002c030400814048003d400604203400ba6a003110009400450200c0c0c03035117150341c21a80c2c040e0303000d1400381e42c40d0040c5c030440ea04d0600040550340342241d40c1c0c0d1002c001c001d469000719502915603803070114a40e001503042c10b220070094024410070307009100082d1144000c013110000c1c00300f0203070400080c01c112036401000d55070180c01c8407202e503102c261075144009031803c21011842008404501c543c46100c900c00c1014050b03000302106418200156121440040f02c41e040040c14400020b84080c607110300c9002d0b6103a629210690309003c0c0c2140d5410700900344071815503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 72856728 1250 72855478 72855493
    0x30705070f0b09040209060712170709080a06020f0903101b0e06070f0311010c030504060b0a030201020a110103021e03040203120c1002030a020d020406090e07020703110d1515050111 80
    0x341e5002c0121010f0260880e00184e0b15402907000500602664802604102108c41d00d121081d4001c95a00e9a210f0f01d0030000701c0c40d0f600d40408a0305100940603140032500107042100018030190064000c50628006003424484440c0c0030a180800409025090640b01d00030000c5064401690780c20f418103620707100784d58103c1c40021071503510603110018411115030007200c050502c901d082e40e0100035017400074458100d44500c010054141070700e050b20414174003120441640b42c0010300300308030ba40c10b801910144c043e548800344a1030544815905041e02000702569180b0041d016a9881469110843d107904080c010b051600f40c02c1240d0402d602000c0120948170b0302c1c0066403c0e00702a4400780565030b0343e60240707000040e01600451464250001c500440c0e40303034200302400d041d20034111685041e40e0700c402d0200c1e40c80c10707540f0000c0c10b00390b5040d481d4540380c00d03c0c2030802c803114090f00d60880c401000400c444216420b040b040706544100c0b8000f4070503507a002c4081c1d81003e0948005080c02c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 72857978 1250 72856728 72856739
    0x9100801062703030c0201020c033301030f03110c0315010303030509070b0d0b06040b0c07080f030a09060e010c0c0608010503010c020114280c03060e1614130e09030705070f 76
    0xb001c01c035010103000c1c002407040e40421603108000d11b0b84c2008014040d00c003009108508500b00c002c601101500443e070f4051010f17035800d00c00c3e0070113040743d412407d50000da01154405541ca400e02091406083c02a06405c040d903440c01c004010700d641800a942041d580b443c103004040300da014000d18903e03000a030080101c000034405035003c00d20407200001d003032614000050710798441c641c4801c06148000c10440c54442c0c000c9404000c440d00381040d500c3e14801100415100e102e007601480200e40542010b000c100c0c865200000c44138018141002e1004236500c0e641e0602506500c40d9000410103401844541028019804c40c658240000e000304203401d601c94403412001442c250140109440e0000c0c0001002c1c51180300a12409040101130b00804008015101c00c1c0559024112a10007003462191100c0707ca045d140156941e0489081418000c000140d00448072460f40410000c004640302d10030103411030040c034140004540e11111840e00b181007104540c0b0024202081000c100712 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 72859228 1250 72857978 72858047
    0x60501090b090a0f02040905010909020108010b070c030602070f080c0d0f0e0d061a100203090a06050c0c0904061506021c080f0a05071716080108010c0203070b0c0910080106 76
    0x800c4011031401061419440b00c1c080020700507030380071f02c03007003800c080002403003011550010050358001e9035130301d00aa0301c0b012001301e1031090b1000100401e0484000300081200340d40a0301c0c5507407041c0410b01c4d07884116200e1308100d410980700400103401140d0711400042e00190044c904c0d0b6000e0604064110f580d40008401900310b6a014003540c1d11a080304942002031305942e102800000c0894804120b007450003941c9400070030b0442e0042d1a40e00010884500071404d85140d004c80038010000340c8014801e01c00744600c0504105c50381512840c8000d01102d0918003040505041c0e8024004c0d48c40d005000c06000c0881c40103041402a00b0003070102c03080921140030740c8080249004991519810380c1200c081280310b03209041c0901902c103002404005486003089200c10341e4407642642d0701c4000460803242c249107941e02507481000004001225102c0e01a4040f0104010038100762482c804034003440104c1482200259807140140810340d080101d001e8443e04400102002c1d54600f2001d51 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 72860478 1250 72859228 72859231
    0xa0902030a05183003010b0c0607091212022823030304030c050c04060f080d0e030c010f0309051507020f150103020d02040e0f030301090c0e030607140403050a0f060501090b09 77
    0x813002188240881c2403407444c840d03c0b5810402425881d5620b6075039000b01d02d010740150b12240503600946010407030462084032103906584419804148c440c0b0966950441d5580b40d103008010b50240200c00006800d10481e4807807200341002000640752600e141604001c0c18054642c1d19240c2e034a940c1c0f1140110000960340c4c05581030803c0c00d503420071420103503c0c041c1e42a00d5035038400c3c20000c000c40c01808040c0000d01b00c0d222a003c0b40c60210214605550790b681c0da92142d034040d40100010f00443d8400c08044454481900b8009108050780d140d0a061a00c02d0b81c207482c51500350401d000001d581013000c6001305024001402554000c1c0c11040396800b810320010348174054116441301996225407210801000c1c410403100e50081051800c0d49a400034829100424a4020341d4800c09005080b28a58803400902900050f50b9a440640e6520076804042c0c43c44507080c400880000c0041000001340f40c0110204128404035107026415928141c000c8561a820089401c000340c648000c01d6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 72861728 1250 72860478 72860503
    0x3060f09020304110f01110a11120c1012020d060305010e16030f1527151104050d050a080d141e04060e0f1207050607051c09110a0902030a0518 63
    0x1402c1752205000489011400001c0300c10320b402016004010017150084142000e40b081d50a0b450003800d001120f40c661103810074094000d511090f1301c410440c850681040c003029071000c0107003080f4070002c0d044100c44158000300e885079500c0d00c2c900130040d020800303040024200803508150390b04543c0c03445034052461310f00510442103140003a034402200d4100303409141240070400101c446900b0100d4000303107181c00030303100086208035484e540304660189403116064120414907180c50201031040308442481c2c03d60b0240241d000003400075072040020619007028084c00f0481c01d5509628a5000d90094141d20480422407490600e0001c212007460b44075400070700c0040d20440c4802603e040c855944020102c0340204100021103110f500b0284c400d03175004008480c02035564520a07581d501c40c15032000d00c00c0701518001409500a600408801c80c400c601c9880301e0340c03001d4080b540780c19090b04105056900032007004032018171449880d601090200c4d05c4100b049894095039229240d14052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 72862978 1250 72861728 72861739
    0x192111060702062209180b0106050c0c0d020303070204021207030c02010213060c030c020604090204090b0d0c150909050708070e150306041a0d03020c090a11040611010e0a0303060f0902030411 84
    0x100031034850800d400340020322400c5418401ea4010240b43d4050810760300c0c041f20301074414000811018401d07000c2d15942442c0c24002c01440c2c40ba4010880801d6002c0000c0b40e05200401c50340340180c4460010f0b00000d40c650501c01203034104982d0280030b031100d00c036401046a2061048010942100340150100e0b440341c2004915040341d410210341c42c070981c0300d000e90800000240042d503500141c0c020811540451010800901c0b1072040044d8662907180241600240700d81c2440b80082c4034039032201e020903904040f03c0e01950358603041c040c0c0d80102e03540c4002c905000100010135070844110400d1100c12a2541031013585980c0b1080a4000a0003141c016682d80c4031030034241c0a40f54040080000c01440c1c2400581e052500079620307200306101601441122001c2281130415009104600d6402c4410358142800c0c01021140c0040810807001959241c0030440c088003001e201c1041c078140659004160343d414071031002d001c03d0140d8400040d46204104000100d0542c0c481d024018404655 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 72864228 1250 72862978 72863017
    0x2030609180a060e0c041406031b092706160806030105040b010b090105091305011e030f030806181501030c020d021c0c050d050d06060806060919211106070206 70
    0x240c10b217001c8160300c90765000780c0f4001700d00c0b072060301c44034060740326080403421150201c03655004490004044140f00c3e410503140300100314135080742104644120004200c1c180101109940e1501d000b9041c3e80e0700300c2401403400f91100701a4040400365004809034024441410039684080c00700e02c05100e008650340c008038051000384c0c402c00403030b04240b50051880d40140c1200c0e2240009250038801c940d200c419191540481d198642104000ca035089407111001e00702c1e585040c0d6040300300404240d480a01d4010002d41c1e102510346170390081c41c950804400c40d0340c3c0c00c0000f40448017400c851806642c051540d12101a50029250854614000540394402069041958207410360f0500a00c3c034007a03c010700d048c1d00e501c800501032269000ca420300c4025907550341540c040100f50b1baa141c0025081005180d00d003420b42c01310f00342c002c00c509540051561000d694151025050743c0c40c2030100c201d0901424480207502030710340e074041280e0030303880c141e642e0340042e1311403180d10300007428075640b00d9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 72865478 1250 72864228 72864251
    0x60504050c03030706060f1a0a050d09020a060309021003051003150e010e030a0e010503010608042406080d0315050603180705030307140d03050106121e0c0302030609180a06 76
    0x10561840d648082c044a855a1440c6010006000c3c01e0082c1c022881c00340100040c2040010481800690300801007860184090030484a40c1d01c001e6101100b281c84003003600041c0c94291100f0014a09551700141c030380b503140b0401413404414600481014100702c24800104641000a0106d03540840d0141400c0c1c0700e0301c800000342c400c8080182495103889801a021107012000b8005c2082c25503507010405501801503070940001c1c0a00c8001030410070020b0005207010319515108504a40e071295004100211102070394007a41141019070402c1002c0000740d82c140c0100302d050108865011002d900f01000b0070514000102004408141c005018080c0e040600c0742c1405401c02500b520343da8846428030711503c0c401c1f442c09000c1403095a041d10900742c483e1056038148c5000380e507906038510101840c070003d01401d00001c28082e001010032405c0b1b1025224045481800d03450158480c54810100000c008000b03014011110f9645c0007162161404645070400903484040001c4510004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 72866728 1250 72865478 72865483
    0x80904050604090b160c080301260604030e010c05030c06010f0f0504021204020906060c07080304030b01060e01140901090f0e090f060903070b0a0605060703021b0d0206120c0906070609060b010f0c06050405 90
    0x110405000302c2000000400c039010050026105401c141c404cac941c010380c40c04100c030ba885170103d07009000201020000c0c010f40d84180a0b1a5565004900300d9080c03d0320900c0890602c0406e0b40104515032115104200c450070f4606c0d00002400c007100c0450800001c840d082c2c001141c0104020f00c03a03103004002034a40d40d10403050b1407044500f50100c5811039220b0070301c19942e42c00b0780020384880f81018000a050751180012038158581079441e1501e0900350700110645400540030749060000094000c01c1c1d8200700c105040041c04d40b0701d104a01d1b070030040b0309035090402c61804540b1a810034820494800b000004a612141d031200c1c00035259921401014000c01c03958015a40c42440060039506045c0d00298040041a104c1c08004c84003081d441000840c100142c4000d400c04011700c582580000740d10141640320882a03210f40c68203520100140c501c0c0c2c024401103072102c0ea105821030910a8520405800344401e0038990111988900050a542c2e50b61100504603500c40d40000c0410609 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 72867978 1250 72866728 72866747
    0x21606020703051204240b0f010804020402190c14030906040e060319060c090807080c0607110405090f06011d04020402030405101506230406051305030703080904050604090b16 77
    0xc000f00032070741d06040c0303070600140306e0310040450603030a00d01d4104501d2145101c0c2181008005245030441460074005441ca100010010fa80c0a5030a11800042506400c0258500d198540d990050b000c442d01d030084942081c0a044246980140800c80d01e07912071078115401d840d006d0000c2e002a0f179031080002d00d0010300c00881c43c4691000c0b00f0800422520350042e0702074043c691036904205464104407540c464891080150780d50104401a8a81c10704a0090140724000c0252421860f00b64000c03500f070310420380d40740005034481800e81050305002d010541c0507100c00600799100460300d50804920420141010b0320541d40000868100031041000444800d00d007003040c40380381058880000300030f196109001c0481e10156044280080c40d081101d01e070b407078050040c0d0820f410714008580a8104072180c90000c81c0b040c1022a01d239404115010040d846601030580d00c442d1002400160340c005080319002e1402e00002c40e0001d14410f8645a00050070b4003860350f8100541402c5814044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 72869228 1250 72867978 72867997
    0x106180803160221070603020d0605031e1e060703020f070b070504090b0103050606160302190c06030e160e090307020a03060506010207050303030f0f1008100e010e0102160602070305 80
    0x1450b0040e08090b8400041c0076402200c2c010f0240d20040521030081e0780c016445102900100d05c18400d842c02940503040703102c110400001d00da512200402d203080c00011050041100030b4601420160040003c08a00780c4400c60284941600320403440d901c000262616041c1a000b00d9805070f00b42c0004240d0302d106400000003000c0c1c0c201010080c2c02d9a2050091b82851800d20207091640e5002e170040d070380038680140001d8608522110980c10b03a080600045003140104003074004d0080c00c1403d08118180a280140850707403624102034106c2d103604104d641030b90050031600000c9940500060100c400c80d0a200c140303a038072400300030b04601c01c502000758010b107501c0b0b02000340308050344000d10034082a000c03603202c0c40d2a201050b40c1d90104450f03040c15042d088000441c04040e0308502c6801024403803507411a2510354210b5810881d4405035218a51340e11f0340c40c512003040074010744d010440486d008510305541090411402031000c0300c043c00890300091114209803040c4125806803c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 72870478 1250 72869228 72869233
    0x302010f0c0510091103030c060604050c04030206030108030a02011b0503191b090305070f0b03130501090206031f0f050d080903242a0a08060409021011121201061808 73
    0x20f49045120000300802c0e03500380e420302400f00c071808090400200300c0e030f0350520800c02401c00e0342d103000c00c04c40900300003041200316103014040080141c490385c01035800b914490300595214400000004c0c02c54906c00030545003246002007041440d50030100312604080002513540c1468602680d0101030004c4000c502280c2c07070881141d0354000d0b44070340000d055900c24001c0c0d070603481e03a401e2680310081541c015800360307010410214094400a40d00b807907800344140004a06040d880d000221240c1045594118042070100740950a10000e06840c0107030008008042c5100c2c00c01010410020031500c0007000c480c1d00080a81030340d41c040187d84035401c000d90301c103008240342c00002d185900d015502c2130601e803e0303080740200c0c5a030540000c80f0107000e4001024182525000201e41101c03028101d1a0031654030311120000d41c860300192804801e0726141e0000701801522514600704040d0b03000c003101c81c2e0a00c4200d4070326860540c021704480780e80c68000c0780010502d629910008259101100c01d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 72871728 1250 72870478 72870493
    0xc03061e060315080606190e010909110406081905011407021c0e01050702100c0c14010e09040506060d140105250e0f0418060204030c09050907030c0302010f0c05 71
    0x203440420010180c590507542441180c0034580d000308042d8081c040d105103a003100e4005400740c2440319001d19110000c1c5065440c030f60f81d0b96100c0f60071704020703044640410749a450f000709014201d1304030749000f0300030740307081000d2850084541c2c0c80c0c0c071202410050340c410b26407011041c014250040c000780c0c0c03006031982803c0d0030415000f07543d84144108049912201a0000a600340206890154803806840301450081da0380e00700400c4080c1c0c0e00d510030a0001c010368650202d1030f0b9030502c1c400340107a040c04480608520001410f82c60000c0d003154400d8481c3c504010008802042068110005645107590800645420542c10300c0550b480c000a42c44c00d420001c0f00710b1055000b500c01c1d142485501c5031a40f141d6002c98001c83c15549642c2c0004603003c2c512594101544510450705481c04400600d400641c0c07242c1c1640d11551054460740902c0f00700b030000841a02c1401c1c0c0000e4800010705880749141c0c0c400e10049058070019042c407808890000c20f007070185691058042e1f002c0b05844d0709 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 72872978 1250 72871728 72871769
    0x1812010f050c0d05061512040309150c020405060a050109090504051c170705090108040b0a0e031309050f090d0c0206120a0507020c0a08120903030d050702030711040504030905040c0306 81
    0x1500f01e101540300f8030341004d001c00c40906140206142a0b8410007206190420110401c0c0d008500540104d00b0000490000191484104200c0034051001c0e698950601100c0c0100803c1e580c0240242d4420b2400f01410411a03801a0060003150740342a0045410754a038141142405604032003015081c03004403042c1c1504e0341c080381001035920030409183e0281c664031002c44403400750b030302801d010030345000128001c6100e0340d40c07455000700120000f040200222140744e09513001003809840c00049200244442d40c1940200c51344400cc3e01500b040614020701d50755940c02464141009005c06900c0d41c0055458034400c0b44d04e00380d50f0610340312450410300340e004010401242c90400500a02da00c1d9415485d0800054045540c0440140507000018603441400c1e800080060760600c02086240c88155490198600c901c000d9000365458441609000d0030005480141d544668075200c10000000d40200382041a1903040d14000ba0034101d0901c00d0740248129003050300b4800c216045540f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 72874228 1250 72872978 72873001
    0x60a05041d060d0813030c080f0f0102030c09061e030f010510020c03070603150e091507020a0807080f070f0c060314040c0317070b07090303030b061812010f05 70
    0x4803000801d0440900d1800c1a8528401c1400d607480c55012030069181804984000f0192001d0a5104000c2042d140d030303075490181d8074a19034004481c54010f864855084c400074001c1c0d0104985400c003d45c51b43c940000f0303000b00d520860381545c1c40f0709000b090880c12034054104448401c5824003c550382d07418448102009001b0900c0303039520442030b4440d10000d542c8007040a040c2c1d15405030051a4a0b41403080c10780c00390030307030303041e0091005c4c01800700245249070f00344502d0060400354050583c2c83c0740003e038406000d40017012001554040000c07400019040400c541c1d000d80c02c414800c0d2107c0110042850078400c000020700000c0440d101c1b4410722080080b0401100c41d2500c0c20400800d121914113050311080703030042c20390f145142c0304202003040c58210448104c5002e00c224a003400e141d40e5a803158070161f4080000494101e01070040541600c60004014800c8640a044c00d0151401041c2460154041030141034041d902d0b4500700025040143c00ca42c0740b100600c820f00e016001c011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 72875478 1250 72874228 72874237
    0x6080109060f02120c09040f0908120f130611040302030a030816030603051011190e0f01110303072109060b090a0b03060a0203070e0a0b071709100c11060a05 69
    0x1c405500d0036999511480345403007101d51010100d060440f80d0b80d03541d04d000b029600205030017a04030340c43d0ba20300d0070b8201c1c0600c120a17a030381c4a460078649448a040a0840c8650000e0040e06a078805605118460405080000c1d10540c0841c0200d002090713400402204c0c05190b000035014801c5444100825070002c905a01c100720a040c10001421900320807804d840141c032015009400491504612881540064050031480340c000d92406035800280301d4042690045803001540c4c000140c4202d00d804504614440400d20382050611542c0c1e0078141c49200c090804820b005002d5100001d41040c00c2c0c0d02c00300950018402c110400503810910054080100014840c0400c000018403a1569100300031442c000500103014030381d24041c6500003944094a28001d1200c00103910010f03961f203071a484041c0c0203090085403160468640030351032036508031038546400c0003400b25407403945a00501c0c4401d1966031920a00401c1142884031190741c060b41c281e03802c443c000070320080305508a0003d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 72876728 1250 72875478 72875483
    0x140702030c0d0905060714010605060c070f0905150d05100f02040e0a020c19080702030a060c1b0b06010f12240602010203160c02061303050105070f090503060f091006080109 76
    0x84a02d882c1003801258260118014154042001c0c00f01c500840c0302ca602c0702e20000b01d40000002c2d81030715500007511a400500450080c0d50251380c041c00101e90300c8503280d0040c84485000d201c2402c01903250f03c40a52003444c0c00d40125180c0b03503420b092106c208030030300c9102e100820030403217518210150000b07507110380038180072070a0b92030100e488105c4500c21600b0400c0120060f0010002001140180c100243c03400d40d650401803000301c02590303061100d503501f603104860005100442c0b100141085021160444c0c02601c0840c0c00c0340400d0000c0140d61f0302107006d103050800e948000300191010f004c500700502d4114903180024200b1410009500600d90700c401c0382d50000780d900c040490a03480100c8641912a42c402c1c180725680d8091a5041607a234070042500341400e84501507481900c0140e8026038180c3c2d118400d1280e030300d4119010441c1c012aa15054004070f0400000c00e0f034540016291000180710340700081d0801105001c92503404618200500110741d0300c0040501820442030b0a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 72877978 1250 72876728 72876733
    0x170907050f01090f0605160c0602100f0506030c09090f0a060c020c0a060e04020d020408030307080714131203020703021804020102070f05090a0e010b06072405010e160201140702030c 80
    0x1100d02903004284400803101c500394a24075141c10b140d011102504607002c2a03880c04552000c0400098408d10114054001980141610141c2031300707080989901110700050b00f8034080500c0529200401d0240e80c00c04142c130490031a45440031114900924460300345120700410043d0020401c26420107080c0303105980c03c03152183c0d030410420011168900c181404070718000030071403036070406801070300f903240721218010305003595040100d0540c1e000311030790780000d60420100300c1c00710b40110700940b60342c804020003810f0280c0c400642c20080110b0280840c010540c142100030940708120010295070301804004800c03410720180854954240c400320b02500031f404010400484c00480340c01110401029102680c840c140e005004040c00f00034190070b552505c84401d01c80d2105801414bc1b103216128000302c04000e1001484440150080c240469041c0801040144c90b9128103a400c01402071602c1454050094280d0040900c04004440c2184950800c0002c68011000d440d6440305c0109 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 72879228 1250 72877978 72877999
    0x302070914100e100e04050307080d021b031806030a02040306020a0504080105060301021303020d15062d0f030b090114040b07030c0e030d110111030c0703020d02010c0e1017090705 79
    0x10f003400c050702c01c0700d030381e4021801c42004004041158580070703001401075040e649022802d8490303405a900ca503265180c9030b500028101c014071112500301000c01400b40c06141400c000d803a0440c00036517100c06061066501001107205444240d04a82c000c0da030044045544258444d0007416540052242003415468500011020b003418002c40c0c4000101400d00c5407003c0c2107508004450b81c0142013030b1440a1002c0c001c8500e00c000d03100e000302821720050500c55146408000040b44500705d20f17030b0241c0c02c030100d104010b00c0701003540d042d06481c0d004900d41c40e80d660700c4031840c2c01091080350b448031a41080081c0800d0154151642c0d01a19250703405103d001122507050350340d007199211503500b56124a0002c0d940510804040c0c0b050001d40001040d401c07807844203407040d5041030310300895010b00000c12004060b010860311081820310f00003408000c000d0100a041150260701305402000c00c0c1c11080845442440480d06080ea07400f003c4c44141000340e0f105a540206001e01d902854848a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 72880478 1250 72879228 72879239
    0xe0a0306060e0a020403050a030c0f0b0a05010f0503030403050d0305071b08030604060b2704060e090d0f08070516060204030b0406090c0602010209030a1e0803040609060b01030902030316030207091410 88
    0xb1102587c0d00600140f44051440d641200ca0300600c6d0781c10342c0c00340c1c05007414000140d841011140102c0c00f0320008103070365040c5860480c1e104400c1d400140319034800c00c402c100040e00401c82030061100303428001061380d20103400342c0712410301741c0740d40500842c0e00010f80104410100038602503107065808201464031b600c601d030021300c20305814010101001c01d40c440580301d281404c0b51180c401610218002d9a01c05070140f500e002602c101d000e603040103034030912142d03105042400380019481c0c400c1050070008405031540c071920140e2000e107007400b01c4020038459960120350003107031f121400c5480361038142006e000410420404079148001d00400140c054414000d0780c000400080c0039103504901903481c151400a04051000c011203000d806a0103c0e030300b100a9440f480c00303a100890102c0003032030008100c0d480d41070201c0c103141c541003002003d6200041661080c10f000ca038906404c0e1001e080503443c0c070750558099442c40e8140040d40045180f241480741c0580b441e560032101307480d181c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 72881728 1250 72880478 72880481
    0x703060810110706110c01060602010504020906041503260301090c0201060803042607050d080c01060501090b03010e15060a02010209042f0d0906090812090607021b010e0a0306060e0a 80
    0x448030480b4090a002e0000480c05942c0007080300003031440340ea49000102007000b030954119911240c0540d43d01c000700819800c1404401d90b0100f0101c034100006002e45118161100b514003001d862030045481c41007549461100303a1100d1010b0710002d41c0c0300e40e1b580c43c40c4006000f60000400041d420312000142010000060b94241c034010003401c8550b018040741602c0ba2090580303c0c0c115841041d00000c0c1503114950320700c0c8501d00a0320825035401039039020900391000c90348102d0400000800c2040013821080030340b8191002c66418441c80e89460b032806481c08550014198081000154020202d0701540100b0340500140e406104031024521415180c0380003145030461240c1c000c000480340d0002d41c0003000310804060002800340e40d6902d9100441c3c40000044400a400150300200c41080070601948441058001c14481c50016402500c0e11150740070200c20402000f81030300306a02584120b4404400545640040f950b01d0138041c01802c16031040d521441160701c0172403000b5210703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 72882978 1250 72881728 72881741
    0x40201021011090402090a050a0605070c0b07020904060b03010e060106080a0e0312060105071b06030204050a0e33030f0a0b10140910090203090a021215010e07050f030703060810 78
    0x800b0240c900301106030040c0800b0350f00101c086a40321f039000401007075a070350f81c00003000505555a54262100b0f42454400041c0030341c2d800500903d51b01b440100c0041e501c0e50314050f1702c1580444c0c042541d04401c40441c0c00362015080303504081c090b901c0003140340390780064500d00c58101804180841c50041c10a10788900c6040c280aa1140112000402d81d5003e80001c100f0320b031042c00284030802108020154070301c03c94124200094001030300f0803a903d000001030700030702070b1602440003508000e08014404e511000b40204002000c050703c69400e0800341901d112140b000d0155941884003c400f240c4400408804a0350100000089000e400e000c920007426202200315410400503810200009104014581d1044144181c00801c0364103a500180d030080d1540c1c80109401411441003203115147e812158500b40c0c003100c0144111755820b4800350440f81d40d10807108081c1c852903c126814030592412000f0305800200340114640d244c1d220000310386401054071203030b0109903840b0064500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 72884228 1250 72882978 72883001
    0xc07020d110109081002040518060102030901030921030219030b0603070815060f0903120f09060c01060e0408040305071512020c0715030b0102011109090c0c12120402010210 76
    0x84594240d00145041c40c00aa46240504003494030a41c3c603d816403428000c0201c42400c00c1c1c01140401190401c0d00081c5001c0300b94610140300c0e803803c000001e5481c0620340d1010304050319498101c0c180b0110243d9050030042504029580f12030024020340613500a02e00a1801405564548401ea10038450f0407803449004120303d2454035900000c650b039101c040d00000305000200340d03283d52565544000c00d0368200b030140882e12042240c04050425190840c51041c003041085600c0008501000321075400004239640e548954034101802d0040c4400e8020b08021140b40d400d01080c0000e000c09042140d00c502c044802c480d40f2400401c041315000c00703c03400460f40030125800c400c02e140d0050074000c000e0608580c000c980d6240000c6601c200301c0a11008030340c0e5118140083c1d642801070000c0040410b441915000c1c002c40801d20300f54008000c074400c0d040200e6198002207041c842100e4454503181500e8030f0790400e0421000240702650101d0141c411440031400540c12400b940c008001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 72885478 1250 72884228 72884239
    0x207080a080a0e0a032c090105040e0f030d0516030612030806040905100203011508131412040b0d0c0e0102060411010917060703060609080607050a05040306090f0201080c0702 77
    0x1400100c26a8521000303881242901e4441407944600071041040f400003a000744d0391b030b4514101c0c001d07040056000c0d896000070180101d030300068031525241d0b115411200151717030024880c8204c038481420940c2d0385144c185e443c000000c01d00c01d00100d58002d00d005000040010500290480b410303004c482c503a102c0c6042e0442080c00d500c3c00702c0e0061407026404030000c2c001080450a6598035414404442404030340c455010006120f907800c611041c4500f2503050405c4005030829000d00f00c0380f600307424402002c1c7c64200540840e68403050100d00f100500020080707444135110308403011150840340701041020720b00105001d145106a00041606134181c02a01c200d44554aa2039181c41c030380e41c1c035141484410000082c4248600011941154591001d0555400e0281005098560507800381b020004000000d004620001c01c40da60011a241400c903a6a00d44090586690113a5480940318502d00a20380c41482154513050810910036a9500e201d5a203500000000d400368a0003e034104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 72886728 1250 72885478 72885487
    0x706020d0f0804151e0c030c05040306020706020c0601080a1a040b18030912150105090105060a050313060c0507030e060c0705010e061201060c0b090304030305120a060b030106021f020708 82
    0x89002e0080550020700410004940310501d12200040c1c0380c03c41074070200500740c0e60320001c00084034030681e40802041c0c42d00b030207000b54200e0010198042c074080074040650001d94942000001e50448a8048095081e0703074540d80d40e0004151100b60f00d010549030205001907511040c00d004140c60f11031380e0f00080341d820b02d88030851380d00710996412489100d01d12041001148039681c4042800c0c40c43c0c0d44070010246040c044059601d2580c060f440b071805401e008006002d941d441c18242d400101051070520b49a030b69442081560b10521a005400c207450300c0802e03650302d071303022008040c55406a160320348402d00350010300c61603202ea4020b00ca416045203200b8000d5601c2100c46800b008401460b89041c50507080e0149506070080e44640007055184080c403040003480c01c05507601440303240266080c146503407800b81042c40341c107180c1c1200000400001e00940034a40c00070340502102d01c2c000c0d13169038540380080d54414604991a00c01c1c0045243c9401d00001c6001b19001a644900400c0c01e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 72887978 1250 72886728 72886757
    0x8070501090902130902040b1c020304030507020d0c051c230d210e0102030405061f0509041a070e1c1e020109090c03020406080703020306150903030c06090703050706020d 75
    0x7908041305240304a07465480014401480380082d00240c090585034580da056483c0da4003c1f590181c03450401303981d005104201c00320343c00c10251100c2ea6010345207504005800d2405036185c0342eaa40205600c1444d6420142a81c2450f0180402880c800d40075105c0001a850341c00345400902c42c080a1698080034440504a10581c0c08031111a00401c588442030011109682038481160403881c4a80d0301104100074070004201081d0061444401c1c4401400802e0400d0180c4a0a01a00340600c81e010041070400c00d0340300601075048174080321620b15040581340203000303003000c400c2588100d03464100c2204c0c4555a01506a80507408044000c5100b098140c1001a074140703e4182d0506c00c50203c00240403403640510403807102c0c2e99900583d00d90034200c0c0078200c0d05000d003503141010320500030040d00d41c60b485158000100550611521200712400291035480f800b814400c940c004c140500540c04000500c45069034400c409a0341031688850007244d9404100c1461000100c498501103407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 72889228 1250 72887978 72887981
    0x8030a18050a031211040b0703140a0806040c09090c020703030e010e090f130c0303020a020a0e0606120405010e0d02061009020703020d0e030a06020a050a12060f1e0e180106080705010909 82
    0x812508160b80805d08000190b0000100d03003182c6d00483c404c0000140036030401d6404204820b82c1804600c0c8203007000d403120401001d00e070b0000d1034070340070701d945041045405e40035092440040c44803040031310500c4002c1d40005d4441c55203100442c08528065800b05c4650300810091a43d1070000d003651049941e024010540340038050644047c0b402d046100f1000300395000c02c50400f550182c2c00414050309144107200a404003a403003104400340520600c811603580b08211507202d80c81041c0200c1d9512541819801404505070b62070b0360b8031412040d8102150040342c0c541c4107128541500140c2913881d200181030788a0100000c0050304010890700300346018580c480810a40502252144a000e6844100b01e911840807070317010980210b448100c10307600181ca449580d02401042c4045171422201003180215801040105c0d840d2a1201d4110302844540344000c0c12000803d0247d801c002000c1000000b14501e0480554281030005c0b40c00880041c0314421124103940345900c40380703014078000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 72890478 1250 72889228 72889247
    0x6010503150423060115180501030207110402030a0603020307090506061e040b1809090a2d0501060e1f050a05060307180806090d030e030f0c03070f08030a18050a03 72
    0x380e41940c2d4064046503e50008180002c3e050090020001c40d41004408016800341820080400604100724449880d80101e90000c4032401c0c2000744c2c60720300b9072804070300c0c4803240020305410a02c040200071500f8510380013001164001d409a400194403510300c07009980b0110b40140d005081004100010428000944105450301e41c0b2a82041d13252105201e05a0041c05202c146580300c800d0300c0106c1c0b0b0300d1901349810110800003031103a218a6691800c4407a4000001c142c02009660711030150800c000103840c8a5600500800c960cc1e100e126040d40c0003015181c1d002c010341c031560000c14051440b03a8101c00e460009000c464418680810071826900c020312800400154a905070b498284139000c040c05820558007510142c581604524600200000380d00205170400001c180929804012070740c00c4940703900150780c1d503484450b07034078518850780030018001665000c0c24014000d8100c091802012421414492100d008048241034000d403607010301a5000314003400d0020380a22802d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 72891728 1250 72890478 72890483
    0x50402030f06220203091606020303161d0d05060906130803151201090f0b0907180e01020f031021030f030902030715090503070f0b04090b011809090b0702060105031504 74
    0x250440f4880034001050fa0001d68005c01280d2110320145104a8101615001752141c2e10003142140342c0452107000079070280122605002c0c008a100031003162030300401100c140d01070700c0201c04044030b15041e59664400c03900d0091500a00c0003041e000300f00b8100070b002690700005c0301425a00c07000d101400e1000c82401c9107604c950740d00c64184069000b80036001d01030b40601c900d6200500241020240a04000d020905980200300300f808001414500c1102c00404c4400c005410080d1069050091040e00000c0c15060004020442d50b10070004c03881060f04c0b0141030780030108900046a6448804011005003c03c1e81200d0350345003580b10764008107030701c1d000030200c8120319980c2034018801c61a40e030b0b17000000b6215400601041c10304206002c0107095070241c03070346035074500b181d0041d203409640980f41045803140c19088041c0c1c4544444002900c81848010003e9034030511480182001441192944646030001c3c100030300100c1c170a4100c4d08040d010f803006420158004061a00c020400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 72892978 1250 72891728 72891769
    0xa030302160209180c060a02150c0d090c14030a02010c060506150d0c1d100c0317010b09130501030302030a200f01020c070f0b07030f17090c010306050402030f06 71
    0x10000036950380b070701d49401480001c440c21303d52a00c400c3c0c0241094202d40c0400c0c0619810068a01a01c0e400140d100c45c0300c14030a101b1031280c0303800030001100d00c581c07a40480080e08003118001444910740301c1078200c1d441078900100b041a00400d0541343e080c121400790200e9548581580031440e16001140c2c4030300014075107450050b44500d10384094007d510a049559640c4402508a580000d540c0348100017001a1f04130000501c400a030100c000d550881c401c021008110f13030100340c082e8042c5559005104003003d00d643c0c64940c20403254101050103441130140704800117030003003d48030f001d0680c0e415078095071800402c40c0060b614428684001003440345010b00342c0340322940c284a1242601101000541c2e03030510040120310741503003030300301c0038a0342e6003090100001d0440000b110720866142c14140711000e80c05a00381c442c42c602c240c4208007001e198042208505002c0b07040c24541c4003d803800c000e616112000e001c100e0100b100e01c6548046044049500c0e40703060341e2000c0c00c0450b100308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 72894228 1250 72892978 72893017
    0x120a0509030c1f12060806041103031303050607090e07020d0e06040b120f0903042301030e1605030d020c0a17010e0a0b0a052202010e0a150518040606020a030302 71
    0x1c1a008039900d804081c059030b0f1070f4007114030b4641c0070300e0340f054101a402041c00131904002c41c80340c84000c00340004040060001030325007540c0b402c0c010385400c80300400c240d008070b235a40d05040342ca4620440d070380f20014902d80008120000300c80361180c0113410550051030000d00015080e50031094024640e42e001009200020311181300800030310319003003906039081044c24085400340207c20b02a14084403504180f205100d00c0ca42c1030715101c2d000401090358262000d021005800410440d0005400c6003d41c3d203101c0451180c080b5a50700f156010307012603002c80c18045040340c03181030440e600d0764006080c45040250120b003420b400041c545500000540d0045109158940702c038541e003c403400030140003000079084003885002e41c040c50f041c0550f0781c0354a88200c40f2040000c0600000d05011001d104044034ad1070380c542035405490305c682c41b00d214201c4020f0250181c0c202c034860880304000071045000c0e509080c020003080342c4485d0001d1418240c070341e40c281c0194001400350020200c1048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 72895478 1250 72894228 72894253
    0xf030e03010f1401050d0201080c03040606050a060206060f0103150e04060e07061e03020f03040605152701080a02092d0703020d150302010516060204030f03030e070602120a050903 79
    0x416401440d02100c0000b40c903803800f030525524420164010f9102e2602a049000943d80085d002607121715040c0c1001c1d900da23607514012000b0416600030f49d030003c908400105803283c0001d561401408215100034043d65008011419204094810003503402600404c11413000c5214100b170300035114000200d1104c1a0800042c549103255206c034002600420b030ba49441e458401142c0180b4a4601c4c05603e461540e000d80703c1c4920001c0c20042c40203940c0c2c400100a8004206405504040100210420f0407841516195222804454130031185403400004d0745040c002041d0702a958060480e0b00701e43d40f104680c50540440e030700d0000220410040c0800b89400c42c1000b0f5115640703c0d00c0058454480522030030840380d002400110f241c14120302800541c4c0c1040644240302c0d01041c00941203105450058081c2c000c2d90310040400c0c0078413000904041d09504002164031a032401c5502c0c03203542d000202d0f03039005443c0c00d006801c07008004062002d0701c1040144141d20300513003140c514001d82c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 72896728 1250 72895478 72895481
    0xa0b0f061614061608070509090408070516090f020702150c03070b040f0c08010b01080103110d050709020304110307030803060d060e031201030b0c0f0d0c090b070c0f1508040f030e0301 81
    0x50091154100100704a0402c14240f010a00301115103800100b500d1b2203680a4801e10425501c3c9208a07000400102002441d604035158141e00c0802e075680c1104400d00159080610700401d0785060030f000607003500b40d40620a85054603001081c81c2c140a52049040031035078007603e0358a403c0c2c0400c000d59004240b81c09000c038001d500c03404072040c2074415400e28903002407243d080003800e07134100201040c0680c0d1100f21241035940002001413801a40c0001990008280f82c2c01001d07070040b58800905180300b40e02551059006c1d040348076516419401700b5840e415a800001c0040c0c80a00101d400c40c205403030b503000e40c213100e01000103261540000b004e285810107100340e00242003040c014800c21000c102015000301c0c48032a0903040104803c1145414010703141c07400a00c44d940c1ca4168130b0f00344540c0d04c0100500c19030840c541d03154181d0800e00c00e421514011143d00502c0624000744022200107016060300040c1c1d20540d00351966034492100c0c10101c40c0540c104003640004000c02d580a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 72897978 1250 72896728 72896753
    0x51603020a030e01030204080c090702100c02010603020a060504080a061107021f0e03011e0509010f020325020703170702030708010c02010207021206010806010b0a021207030509090a0b0f0616 84
    0x25001000741c01d06070301e001009100d161550303904050060104016568002811900e0404201d5907c2e0741c9940d40c440807407401000c6401200c42c0e90900884045e03164041d4014001e5030300a840c0b16440c1c40c0c0f0703442c06136250b105601c1213008660182d034100c400300720302d40e006d4560340c035050300b10f140f03400d04a40015241050115050620110440305030410642041070454504026402481003030f034400f49240c2000212070101c080300f42c645001924011081d80300418940c2c0c00401152241815410300c1d203800c1d01ca0750b40101035040810201e41e00c500014246040740ea12584202c400c03507410a851082d50441f2004036054454050085000c2500f80a01d016001180c0e0006840715500d00400456841d038000066840e0484001400380381e00100b80300e0b040d11406400c2c80d55500c10319004a2400b00d0110114081e4440480c038a410036501000900001e00200d0740c408054440d03110660446200141c503603030250025040e00140c0c105040a0801001001180403154405480c0d820459a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 72899228 1250 72897978 72897983
    0x9060a03150b0d0f1a0111010b040629090a09091a04060b03010b09150907140406080f0c0a020a0615050a0816060809060103110a080312010906090c02030d05070516 72
    0x80204180030f01e0355a5104a081c00f8a184009000e1904851161600d0b00e81c880c0199041000e40321002c0340079082504017843c0300d1000703441000341698481c290405403601c14801c280114810320782035003c22040081c1e48045030b00400034100d40349480219801405c5d07541007103a800005255000c50402c143e6500c500c00e500407070340810b44420f2001017600f10348205c010a4031a4040d202840b030149040090354454050a49441c48a03884000382902e145813150144000c900c000240032501c1d0f0750041c1c44c580900070a842c44440c60305c9191035071602d8010000b200c3c00680c000c07452200820034940000c6c0d0062112050308446030f840e200803660b1407507203410441c0749a100d0700780307403c05201d41c442007030052400d89130090840c01c045006946a10341803201038a0f070700003040341507a00c0e03560214450043c45040e0840340d48071054204038005580034801d40d02d24600e440000210098030380a41c42c480c101c0d07580514600b07003600c44440001c20019010404002c0180404071405101c941c40c41042fa0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 72900478 1250 72899228 72899249
    0x60f0d2001020705061201050904020f0a140108070c0302100504030918020702030f0106030b01120203070b070b2e03081b03040e0108060112080d0513080409060302030c06070809060a0315 82
    0x8660388006840e00019501c580e000b01d608100380007091200401860640d441100d004102e03403a01e0000032903201c0e6207001190300ca01700000c009010f10030480000c030f0b09402a210701c0e10a0303580c50f50075a00094545070141c00360700460030103503040e481944050782c860300c40c2c10121621a01d40c030000c1441501c0f017a11400741980003d0383c00951404201020706142d29200030b128250565807403110002d8184108012190000d00c070704e0440d0f4042c013a04001d800203801244c1c84480909000e5000501a1030b008d100301d0440d50041c08160702c0a032011141d44070b0131010041c8c103140d591440010741c452101070142c026807001d02c10801d9402d1000f40004d2001e8840002d0a5040c190001d04060301a80041b503035500041e11440011441025201d0f0380704000d1000031560f940040d0b50042d00000300008041c90f0000501090014099200b84240c0380240c084690201703481c01400394a1043d0700c40985041010f0060081d46e24000c6c0c001e02000740c4501d40400c4480990b00000801c0d11280c00c614030b0309 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 72901728 1250 72900478 72900533
    0x30603051e120a021c0c021905040f0525021203070203040317091807051b060a060501030e06010306050702070b0f0904111801030b12030301080a0204050c03010e060f0d 74
    0x1500200b0004411416030302e926850310002c420060342c1c0c0c00100000f5840080348203442e81c0ca250181400130780d26a0003030454020781402512410000310940500d522491900c94450000c20840c03162602c59801c404100086a0003000248080c070812160001148540703e03c442c0d1102c102c2e40903502801031070300117544603415850242071400c00c6080c40020100140068003161b6904065a100062084004c0000c1c1d11440c0b000c640354840c44103a8a820202034200b032200560008801e88100e24910003001340c40e1719540110140c40a00c11000580d0380440c00510218803658000f60308950180100c0701c2c1c1030fa480141c030306c1a401c9090307050300c018400300e400411403c141c0240d210407100040070514000e801501c0b401c04082590381107040580c3c4140700d00039510b50301d0cd4031020154200c1100d44a603074500d0340c641c0d2280e40d01412805241460041036144100c00c0603039042e960380e10303100c1d44255502424040c072034a64a8003998440301100c1c1c1003011031641c0f1507841240c2050b030300ea0201c6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 72902978 1250 72901728 72901783
    0xb220207120f09180612030f02010e1912030b030a1101031a180703020408030705160609050306011502280308010501020d050f0304050106030611070c080601030b06010e0103060305 79
    0x1240041030340c100388002282090b14040d8040e0411068a2540c1c8144002007040380d550f01c01000701c1d0b00503105d144400c20f4440145030b0403480c0f111410a0030390003072180300c4052030f5554136403002d0812411200c00c6074069400103101000c0203030b0184094030b400036446401d2800646062101c01051b609068014030b440059685802503841030072810881c0950100400c0109241409044050302400c190301c01240c0d800b03200f034048800400140c0c1c101d1303403030345400c0c1026900c4401000c141c1146506003034001850b64010f40000d012298000c01404240c0c1c44d180a60000c006101c00c014210300500040040300742c00900249024100c3c5ca480c00215085032030054042101a040f0078103640c0203d402c0c004490380309049813068800480300d070303840c1e84a5141c43d60141c101500002c2071241800d0010180e20402c20140400c540200f64030320421395501182616418203000180140c0703015400a0400d5000d2510a040c494040c5000100d132562a02c80c0c80c1820a011441d86000c844c0031003050303e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 72904228 1250 72902978 72902993
    0x40f09080415020304120803180f15012103050d1e090303050603160510050405040e03190504030506060405150d080a020c0105040e061903150c120506130b220207 71
    0x100d400d1030004510700385c24009643c0049100706c50003008a88000002a0062044000100340d01d89400440d4007170020071400f1138607031000900f00038519103003000009940c0c0c0340340c00324005088101140d0100005645044031650301c105506140107444111a052081c40424a40401c025014001841030500d01d40241070f00c0000d040144260302c0603035814180000e0300d00c074108a4004480c080c1a49052443c195403c0c0681c1c1d0145178410b1401e01c1007440c170b1101000605011060b1019441403610560040c0c03082e0145000180c4240c0c01440000d10394201540072640100750019003815040b08600050808020200c0c112214107012a141c1e01d100d070100081c0800c4002420071a0601d42000e0706a20f0401c0000c2103d44905819524040b0240c0c07051507250145800001d0030040c99115804040540205980701e00002c0103400200c16242d42440b40d40e0241400034240c9500d407500500c000702a01603203038105d90004440d0000c080700d03104100140d115043c03145015803031341c025003070900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 72905478 1250 72904228 72904259
    0xf1303060603060f1a060c010b04050a0203040507120b01151b0606260a020609120607020a03021005010e07030c110d021e0a020d060e0a20090702010204060e0f040f090804 75
    0x911140c1001802c0d204010b0160071030501020039101e09031a14030891fa414050071040480340c1c1c21038a00802d001003850305400441c4118000c00c100d0741081c3e511442403a046003154000350520a54000610400c0900d4415a21a00d441d1130000e210034014449011454074211080324401c0d40c8010401c86801c0d00308000c448400b0300c1c5400d2950100c000c500c02c0d15080e42440084c884c100004030441960751303482c00c4080c801c0c229003c0320018601210082c2d0b0f1441480c406801500c540900040610002e00070b440c181c944c45000c403000351721202003d80203801d4410f1051f0074030140d1003000082440400ca143d6003610181e0007003507803654245005102d143e0411074a403003500304000ca0000741e10303850720300d1401c69403000d40005c4c03003c0540b862905004280700300600000c080c0c102c8c80768598402c04001d0084004031031000c16501c46d890164201c0c85076110305004202d07110307440115486c25a00130f84070b0f250f001c1d0012408030240e06090045500160f030440304904045000c0c0441440c105106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 72906728 1250 72905478 72905501
    0x80c010c0f1b020f130203012c060109050d03020a0212030912030405061903060801020a0e030c010305010e13060207060608010608070603200304050c030106080309030c0904170f130306060306 84
    0x85000d5850041c0581c09210b2007100603014134840002d0702c0f0192a0f42e0740c000c0d08083c101800319281d585401c4808032030814507014030b500d00b6600e20f180c2e01280700303804902d008100585400100615042c00d2100c281503601055080d8054000c8144c00f684503c07080310f660418100180d580c2c2c520040030800c0c02c8103401c01d242034a5005000c00e020030f403121800c07591120026040345002811a0790120040c00c1960001941540041040d0011a80040e00d0030100c010450903104a03035500d50046007214400d1103030b09844900000854501300f40114001245802231801511340012600c440e0300359002d50b800946d40c7d079500d6000700400c10080c410040a0702c40ca05d003d00141e5a03504146640d604000c2c6011081840000402c0c20003130100907110350440c000e0028041240e03a070f49813503240d4202844490181c091406124002e02e0074001040c89543d01c0090290000c0b03100410400a40100608800d108020000318403090032040003030008500c203d40100c0c04038258a042000e40c1c6a403100e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 72907978 1250 72906728 72906737
    0x204080111090604290a0518010503130303110c060f04022d041109030f06060406050406060203030a02030c0403050a05060403120507080601030e071503021b03040803030a0f0603080c010c0f 83
    0x22030300c01e0f5500070890b41195200707645800030701c0880000c8480d510b50f0145041030b01800203070368a50140c000e00605014948481500303090b105810055540e0306c4200c03003a00d0310100e40102c01e2300103030007603020640021a0716241800c01c4812034140389005800c0e05d2400c201001d0728104002c520345000c140701c000c402000246020f0005002410303107440039800080c411502c0380fa140cd142a03001c001d030382003072000800720748101024040c030340e031035040954070300f801182040008142401c0c40c1c064142161007950045181d903070f0b03603c00c0c003009400141c0000d400d00c40400002020030420400301c0c0b04980100e0240803641011301c4c0c0603010519035454424214180802c2007880c98000748a564855001e003404140c170b2885404090414000760080d88000e004910562200c40d8103034040c056a038400c0c503421001d80b80c0000781503941d0140c0d10074a03900354401c000003000c038482034102d002a5070030700f4008501148c60355035030303046a0000c08080306260347d00c444903074006610a542150040031801c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 72909228 1250 72907978 72907987
    0xa0806010819080a0e0105121f1401020c0d0212060c03010e06040501051c0501110a0e010e0f0a03021903050d030b190806011a040509040f1403090a030f0212010f0204080111 76
    0x2e8036645801340d195a40107100c4c03080c0d0480541c5e401201110300a05202c0d10003d214075004000c034602280844c0e0303400c4d0b603100749400824001c402c03140400c0b80903016001000305414410800c030394806000c00407a0404040c1030003200d180300820900b40500c2c503c1e418991698109803032811240002031406c2d00ca0760400c0010040c85d145c00040102503014840c1c1448501c8280c24400d014100ea0a5603285132000000c1307200200b9408622025010307000da80d042c035822030304800c00150085100241f5800308600800b000140b40c500341c0200403481020070140c86039900d0b00e8242c207050700040c0000201c0d84550485005162400c0001043c086400500010504000f9020f58038101400fa40d0705450300203902800012500d02510010840104074071100c0c030b403031b01c0d0981ca0884007983c21200f000620400d8031103404080240c1e92185000f0f40700d4111640745468402010004003001d0741c0144501488446d00c941c01e00805284559030740e40969514a006146800c58102c810015200581440b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 72910478 1250 72909228 72909233
    0x60e0a1404062307030606020d090e06010e03100f1a090f06010e0105121008060f0912180301021602030d02120d0b0103110301030506070e040c02100c0207050a0806010819 75
    0x8a00d80d4115800450000786006805281c000f00c190004030507101c9446103081203000c980c103070480c1c0c003614410f41c00d41d502c6520911042c1c0da007130803034000d400381e209110000542e99485a9179050000700020212000744c10281540001c0300e116016150030151200004030310000200940f14112000b0b540e8400d5070319001010224054000e0700d401e040085610403904144e102c5e6003614808824102c0e448000e0420030030060464029100d07100490045800003100038128101041c85000301c240a081725850001d190401c40c1d220012124184030046050013098038244040c20400494001c3d402c0d2412290040500d418800d03030f0040111f501c43b07401c10380315040c00416a041000d0103140401c0c61205080103078003502003d1440c2e410070310b02000000038418001207541c000c4c081c603102c8881100c3c0c604280402d1303c000022800242e0b020610b01d0780e00c04d440380d00044429000c4d1056400940c0c45d940003608480c07039035001d54804e03444100140b15111051143c0b960640c0030800c1106100a1607 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 72911728 1250 72910478 72910511
    0x8010b010e01080403140d02040603090b130f0f0204020d05090604050f1c0305060609040513031704020a05010807200a02010909090b010e10050d0311060f0105130e030708040603060e0a 81
    0x410041c1001b00c1c00562021450001c07040e0742d10410511410b549a40e22140b00030002c03c00c200d8152a585002404200d40405c024412551182c0203240d0b04500c0c801c81e2526400b08415002c1240c01a60801040002060301d100316401820f80102800c400d08140c1030051400c0e400c0039081405411000020700404103495014100e080305040c0800c00b5681c03280010081d00450008580080c10142009040742088802903d0a84252184c0d1141c82c5420800d2050303000403100203400c441e014406001940c014044950303c41a54640401c1c0003001120a1100c030280e819242000ea00c202030700c404540c1c0108012000d0b01d450003082142070480d8550890707125061060600800d500e030b0124410f0001c55280360058440500441040409494028840c0ea4251200000c500505021038807240c3c2210030a8101e0300010070142100c5400300d034801c000c00b144070031051a1701c800c100810000705a000036000030240e60300c0000c3d0061800b01d405200c104000c11503104280341c4148a082503550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 72912978 1250 72911728 72911731
    0x307061e02010605152502010818031e0a0f03140604020f0c03120f0a0b0d0b060f03150f010b0f0706020304020d020d05070f0503030f040306320108010b010e0108 71
    0x114014000e8445205080e401000150070180d0000c2c0c5080c0c28000900140004281d804000c000c101603080305450880480e4a00c460028005201c6501080030000c00c0384000c0004203d450607607107440000e0075405001e412510000c0303650200854481c2095070400101c6450703940a05041c000c0070080500d44607288001440c140c480d17603001ca0407441d040c0960041d540c0b089a041d0803a42d40d420003851144071200d045404042c210228070001f10b00541c03134094140d000780b000e00708003c20007483d82c41000c1404001d0030142c0000c189000e00c107280d40c081000804981d055624a00a4204400c0e014000e110581202c0b21518042008086540c01c00e001c5071301054015800580f00d442d1440001c10890700701001a40c450300500c0140140140401c00c0400c48986c0c0c681e0078503450b030320001d040c3caa01940d070b05040489004c4c001040411a240c1004891051055034980c40b0700c1121903030480390000d070005071030591030787d4014040270000b445207070489034007401c00b140440909000200400750 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 72914228 1250 72912978 72913007
    0x1080702070e0408070c030c080604020a090905031b030f0a0302070210030c020d050d0609020403060b040605041503110301090203010207050709180c0b2803022101030f0b130b0a0c020c030706 84
    0x10009017840c00d205204032146d0145900030300e42541c40f5640c1e900b06640b6a030a940c240c0c8551040309000410002c24070680768125807000c003440c1444826174010000542d003002c41c0d0601e0000b0000300252114800080501c600301da2001070300c2d0501401400410300c0c42100788001d052800308610701d016000284407206003450b2800e25038407030000c110400078023450f5000d0301480d4004640401000001e420031581441d0594040000c16640c000300000c0c0c2e600d0f00040c00c400394181500380046500c1242c8a80c1281d0080e00208005510758042422640b1015040d81c45811801060015900034001c4080225014014051141d00c0361100407d51603a03203d6042e08000004103003005489003007c0c01781f11030340340c8082c9800c2c0d05100000b13406580008210b228ad9800c5444030300002183c90342d20750580b90004620035180140360788a82c609000a080710a0f00b1020f07507040800101d442d501c1038070945a50002041001c041d2802900e018102820326100c3c0c0c001150030700c50382e58008100701c100032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 72915478 1250 72914228 72914243
    0x1002010f0f020a0816020109052b0e0a0506090a0e0c030603060106020c0f04020a030e10020a0908160506071509050c1302090f090c07020a09020a0908070b030f101205070501080702070e04 82
    0x4407001c5e0143d004101507000101503010b0809480d06100c001a10b400410301c03804840c28100c4003008044644440b400407156012081e18030074032190503d14007411a40b1409000743c0102500d44146401a90302110310200c042d1703001041002d01e08003404498010b00342400104601c0e9843c2c1d0020700000e02c0c20070a0b0340969070110300003010ba0b04c2500078204040003142503c01c10511200c1d400040e50040c6c07854400304569150001d0443c600041440800e51f0410019808030304190800c40b613075005c17060565210320400b44900c683d590520070110b40350303c50001031610401e5207062084091500c0b100c00300b031501c180440d1015456906a2102815044481109968030b042c0c3d8a0018002c155000c1d400046080000c1030f000ca86600030816041d260721000c441030ba0310104650f4551040c0103e04d015101400414074000701e00c001142c200615481d4031020700c2d11668000d64004034030341c00f65650752010b50200410750300198900e40042c2c1500c043d05645003040e00c19100c090020700002e013500c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 72916728 1250 72915478 72915511
    0xc0315080601141f11010c2307050c060a020705030c060405010e04200d0501090e0601060903080901050f19030f06050a17010b0301090c0303080601030911040203070e1002010f0f020a08 81
    0x141d607020591341c90014074816030441c0c1030030b500380103000608045068000c0d6103030040d03032521a030003414210b000224400290080401c4c01e1000711954004613400c58883c414481403900541c0c400c80503102c60030042e0700402e8401e15001c00c2500d007e005020343e034010712003000107024a0760720540c601c0c809002070300c002c2001c50740034910721445540020041e0303084a000ca05820304d54003e1708118100c4107485401d10100501c40c200c60703261002071180d40e0208407058800c000050801020341008441410403d0502c202c070844107030140d1000210103d24501c2d00c1e00f00c07415507003511800c0b40b000065041004194209401324651159600940760382c640c1101400302400d4094100c0f542c8104c010b0001d00c40d44005142001c8015200c0c081200481d801e0070009205520902c00c0100d41034200c10050401c4400b18103201c002e41c4050300031000c00c01003a00420b403580310941700c80c0111000b50700000d0130140c0304407104201c0b210301c5440c1d1191070040081c044a581d01107066600074106200c0300404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 72917978 1250 72916728 72916769
    0x1b0a0509010c0b0711060c040602030a0809120f0d05090f0c120a150603051e0714130903050c071a0405041503050a05010c20060c03280c0315080601 65
    0x41d5800c20b00a010101e440d0801200300da01a0101090707414040440e01151968248003c40340141d0180c0b0005038000c2c021601c880c0d1141c2205900203108000342d400224901620798200d44c0702b100241c0461000042c05c80340d10000707101e2681c0c80141000030744190441c1e42441511105a17010851060098080c81c1140f054240600056654080d180cd4500080b280502001e400284403c3d40c050103011840c3e0314204c504a260303880c84201c000505161410000d59034820310102c4109604580361684001280350302c0d100328003445000e5110f1035120181180c5007850000c01d41c1062803c402c0703131b40a030b0052031881c60503102a00c00458001c03074038911542c00001d074091240c2c0094003d2007813500c1c00c800d01806501c2100f400300c00c0d54507074030342d03140810100042e003034200310802d0280c0c0701c1000035102e8a450f5000c6d542220340000d03d801c000b0021140c0103030a1208582c10015a40d6130301c180c040c41ea0705445191880d8036000c42c0c5441151500029603142d1805102d860040e65030036048100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 72919228 1250 72917978 72917987
    0xb100f031d0a0501050702060c030a110415170c0720040e0a030c0203070501050301180e0c04020705240f010905091204060302030601090801060b0f09040905010e03030f1b0a050901 79
    0x10502071210741980360000e600301e041d0350b09003a01080e110f9501c0c2c200030a1046201240040c070440d919291240b4584881d031901004100450744480f02c008180804181c4030085400382c4542c0203603903600015044010a0313054200c20103005468402820401400015464110580081250241004460700c03031070224001e00071106c4142150f028100141042580000c4031110a074000ea040b604a980c9800041d200e91200f8055028442e804503c00100c0b4075480c0c001200c810a00c0c400e1b035008003240000308060740c006141c1201e05402c120502c942881d421003204d00c104080101304826801d0586504d0015803060003846402c545070000924000010003402c01e004c460346490380c1c0e03034690b41c444c000d00941040d1655400035004840000342002c0501070354045d201480c1600d403400c084510002c00ea64080b508942e0419103c8a00303c1c0842c40c28030030403803804902009155282381204010342c50303070001406c50222140004068002d40740000c11307250414541d00b88156038060060044c0c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 72920478 1250 72919228 72919241
    0x3030e0a060806010c15061502280f020906240a020f06060a060807020c0a030c090b04090201050a03020a120203010308071a13080d0e070807060f0804080304031b05030c0307030f02010b100f03 84
    0x140f0401300b0540d482229a001506018002042d0610b0711103104281c5504ad000102c45e1014007030030700f019407001c054509110915000100189070040507065941c2240c0300d46401d51060f03c144801143c4d9035030306a0140110840744086001800d101e00e01240021075000d050b02a54081000460000700110700802c81c4002110008000240d0300341e82e86007640142c510f6004008606040c8024030700d0f2810300e802404501035058582d40e0070028050801c030025041014440100716000300908400c03038242c03004501840c003480307205d5a03d00c2c8038148804102c01c2c80041c9010f0382120000c02440c80380407010000c500380d0029003940d6400c00b100302c96020300201ea80c04980350051000000d603001c000501841100c2e159200d04a404c02c42e20000d50798041f04440150281508000190010b071151817481160b01070202c00800b04082511600d1654205a840c108146d20000303c0d00e0a1503008a03401805203403920080c40450000008031b0740c003116242c1c0000a0107036140c0145622030003504240d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 72921728 1250 72920478 72920489
    0xc0e071103070b101205152e1a0f030703091a0f10050604030302060a0506010306170c19081903030605120a0620041a0708030103030e0a060806010c1506 67
    0x1d0741c40c1c46541c1080010320400f56070011500d644200005170400520344048101074100028009900c1c2409000c0c5280c040140543c8603c4100503200c245016588129242c0c02c51440b00361501c0c500f0802d81824100a19000003103080d028802d40080a51440460364019800d1401041007401032400300c042c4209440203280304001d03e0204109445991100342c442d441d4071505004480c2c0c0c40781482914891030002400503048400014415071180d0803042e0031030f9062600050711030360340014140b0b5610440660b142c03a000103403036880d00d03c0c2034072003020003400114908a8683c507001905503a60811042003070384114402840781418040e03805040241400f61512880c1811010311940f2601e41581c200c0300d1516000c1042803001101ca02091000701c4a16034510707040c10040c020300150306001c10741c00c580104000381ca0005104401850007140f00303880e00074400c000c00c010003041200b80e400c07003000c000600b020031000d6a40121480c03c1d440d000291120505400d8001d500940440d4015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 72922978 1250 72921728 72921733
    0x30f030204121a010905090d0309050a0501060f1404060501170a0902030f0c120c01090302091308040e060112110405010c0c0506030106020c011805030c060c0102190201020d06120c0e0711 82
    0x591003800284601900c0050f50085114016078845016a0449105441c032400540c011a031010503140254003000f070031405135007160381d10402c0c0d503117840c02d43c7d11542202c42c40d04959a0308000650114041da00c45003001c860a014042c00c040000340100780c0c00c24581e105400190101d558130085030307c00c08a55070003a041c2c130030000100794195607070300007a55818081d13840040346c181490b1000c501c01148075016034811041600d140c080242c040c1d8050314481024bc4021040400600d8250081c8024130300d440c03000c4854540480090141001d11110410b00c50501500c185150131440884d42624424206000300703242c0b40c1488100c058083d0010394115a0000c004030309241c00084100c94020240d984040c1141d00d101f00400700c030782a11030180c16500442150284e40350541c081c1280e19140c2000600b003050f403800c0001c03402141c805190260b5400a00700c44014034601948000d010032813403004519440740d40d003444120780792059203a0782a0030b01c08280614401c803030700e0040c07100c44000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 72924228 1250 72922978 72923009
    0x30f070f1803031107060c020d23010207050109020a0518012303030c010b151804020d02090301050f010303091406030a0b030c06030a0605090604060b0d0f1d010203160206060d030f030204 82
    0x8014007242151001a0700385d100d940c600050407485070a60107412540600340403848a0340d0341c0c502c4034420901c121203c00359640100c041c0554024809042c0c22400b802c000b080b102020b0043c00300d102d4560308120700500c3c480400c48a1403201e01c90700ea04407880107110000d4250b01c502c007200a01c09945015606000006148a003c0c0b0150403007400100101c5803c0b1051f254000c0f410003900c2603c10300c2402540c02c0150300d03042d00c0c0a0b130280044450304000545044c2d251400207085804c1264220020042000188285540088100c01604120f0401405602c10b031001a4060000400c045842d42e00c49002e888140c9050168a14400019040c15241d0030000c001c0d601a0002e405440d0040841e5800210145424010b0b5021110304411040c90b042d1400c40c81c001a00c50442c0001e44d043d141d10050340011002280e0b008812020b200040c0c0307905110347c000d50b604008111100442d4812001d0020680e211490031440650509152040601c0c6003001d50190165174007101382c1004900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 72925478 1250 72924228 72924233
    0x32215052d1c0f11090108040b070c0f0302010f050702240c0706060609031a07120902041d0a0506011a030127021305100206010608060f010509040207050708070b030f070f1803 77
    0x411014901103e824180b002c410080ca102c420380c042c214041d030009000c0c101140100d0140e00d506504100e140c645048444900d45550a41103544242140140c0d07441250904520030b5124a0390420f030148058000356031040c41d40c411601407221640009a0800d02180400d1400d004949003180c1c02201844226a2007001410a10743c620050b83d10490140746103002c101721a1100d40300308040c0e162010f07070070064111840107000070102203811580d1104c080380b103110112000040ca40d1210000d10741c401107440c0c4a8117103101030341300c1100c010540c00c903c20782d40c2c142c40580f410340e05143c54100200344031203c0240615a44051580355501c0002c00b02e600740600071454090f81c405658015080d03176000412a40c1c0c44007407040e2400940b80c00046a001d15200300142081c003414548141492034404c001360881c0d12039001250b20f640900000c1000c078406100b090b0080010412460461800b61a65451050b00a01600c100180c040c5001c05d2580112a10190b40e034041940380b07451074691 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 72926728 1250 72925478 72925481
    0x6040b2203050d052101080a120305010f06080406090b0405031b070e04030c081905130b0c1b0d05150a06060c03080a0906090f03090807050301020703140309032215052d1c 75
    0x4410a882780141d180746510018000e016141c102c030b00781040c102e15146807240031284118080e2045880700d4486100802050b07034403940034040d82c01030001c0c42d5503202e00c124004412141c1c0e042c1082582011904100c010203c42260790b001d50107050160a818040c80d04640354400e404d50341c040b900e00807280304600c40c0c0c09005480d041c140003200000380354076005085281d0080c06401186648600100e45801121403031401040c040500381d190302039661b235100707414130007040780da91045230002c020022075071100d0003282d0003418141803242c10b0249a840090001c0d50080c80061060340314030802d0108441640000240394001440182c82f00652500038600c54492045444501c911200130400345418800c0b200e034654982c5032401c13000c41402d05410940c100a01c84a2540424890540100d1b440052600a860500d4003091114182001044120b03c005800d204000d0305110310b51340d5516410410f1140122494001d4032050242100c0d08248106081c04030840c102d4441131181c0c0303246 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 72927978 1250 72926728 72926743
    0x303020604021e100e01050d0204060201050604060605070309030308040f060c020102030f0a06050d06090804080a0c06020f0a0312151502032808041202070506040b2203050d05210108 80
    0x2141d5540300f003810895810088003030f03011510350010b28004050241c600030710380340b400303500706041041c1001384d603808040072a0002c0d401000581d4603030040002c107103000c1c40ba101c064445410320504082854a0082c80324543d0f00000b400d004010001c0340c14031452071002c41109901801c14000d02c409610024042e4009071502030035110f400b004910301c2e912340c0c066101030b62405004001000d483d40c1380e40001d401003100a40b031ba410100804a00a04180481c900107809400700c0e004480c60204024500341554510b072a1603000850900002944480408001c510000c4085080100001e298910119a82c08185018030f8000080d0041e60040040d140407441400118002c0055a01c40c0740208504001000041c24800c00140002c440200304140b0340b940c0c0c030440b0100c5071a60040303401c650003500031045d14000801d0141d107218104d004403240c1d82100d4600c00b03001d891a035a5542d1062200361900501501007003092016031451300118040d0000b8212503007a5a40750101030b202c0a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 72929228 1250 72927978 72927983
    0xa060303030b09061c111002060103030212030712020a1209031d04020c0309011b05060709091b090e09010b040609050109060b07050a1205040e1806011a03010306050c04050a0303020604 81
    0x1401016400b600c0c0c0084414401c12000e02104c030b10740c040c000d601d114004050000c41d80c0c04a10700d842c0c98640c07a01c10b00d000450030140c00a100d01c1d411410064070f040c400000c1c03003249003802c2040110955205107032522041783c1000150312150210025682002c69211403940346107820291410301d40d0000442d850b050001c04080d503807030144406c0c0002d91113008a0000c039680108107446055108116841140b00e0745516140451001da544c542040c1094840d4400500420303003e200e036a01e14070446040c4428120f1030021003902e034001511f40b004501c1407040005824001801c0801b0a4110104080c401002002181c1d00ea80500c1d004003005c1c02030425242c5451004107401d0042d80488801c10380040c01007880d60300c1c541d6444419008103640004000007030000240504048019500514070340048910030408400440c1c54510141d0104440c181c8003c00115500840c004482c1900e41015010680e0b40da071085200c41c0380301c2d80d40420380285424600100781503010030101d00a030b2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 72930478 1250 72929228 72929231
    0x20d0c09080c09180f070b0307090f030b19110f072006030a0207060b040207140d081003140304080d0804060b0d020a0b0d090203030d0b03100c0f08070203040e0a06030303 75
    0x1d454903105640c4140b01800e041d0041c401d58041080150341692000000a2072011640c1c450500040c40e4181a0207910880f01d210010050040c040d8011521802402c180a001904a441c680b00c0c801d4042000e8a40c0c600401008140d85684004d5000680d140c109134001950302c04034104140180d40c022441500c1d0008503030791000810100d83c100f40c10754140108114110384070520306400070740c8045c0c011100e803584c60303040d042c0707640b51800500803a50240c8224841005011480c0e4101903c0f01041000c02c0308000030000300052500843c0142da4100740b440c04410f41800006142d44541c0e048030385940b0500b4400c44400d0360200c05036100340c1c0300786401c2c0b001030b2815061080301c4d40b4503000258440c060a400740300d0074052102401c402c12094402051102d01a00032a04661101406444450302e85910313841c5410704120b00b8403101000d1804004e40480903600500411a00081c1010040340c0c902241c81c141c800c00c03d48026001c24500c99400b400d01000c980d000b40318600c81140400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 72931728 1250 72930478 72930497
    0x90a0906060e130e0319090503011805060f0f0c090406050603010305060709080a0201020d0e0301090f05010e01061e0302040b01110114070908030a0e01030f0e0105040503121311012001020d0c 84
    0x1091400f5098001d010702e00154209001e006c0c4408a844c0348020038410460510400102070380c00f405032050030b0f90070107180c001c400701d642009400c142c4024030054010211b00f040c0324a0751940d05c00380e90302c09030818409442d01e10b184001806404140d100c42d17032190001c00040203110021980c1401a45181c07507903070006589000098642a0320b00c3d005e409a0080c1203061500c1d401001000d214010050002845601c00c1d42c544100c0040000f095840c0d039500d14170b00306d0301e4800744075440c080d002d82ca5400c0c140c104800350208181e0600d01000740519190031603101583d0050704200f01100b158802480208c02441d0740c01a6288101c50400008035103480000d28080d000c01280d80500c0d6235503038000318802003801540a0013082c42c00d100703400d94940040c42c28100038480c0d42c2c0a68481e101443d958108403015500c00d95010301801c040543c80b104210006042e0001d102e1720036000c0c2041065103a40305c8001c1d00c072050400c2d02120f1075000017070f50700a403403440e030000c405010f9a865043d0007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 72932978 1250 72931728 72931759
    0xa05030604060c030e06010803190e0918190b0406091403030c090906090601080a0b0a050409050c030706110624090114010f08220507030609030507032703020105090a0906060e 77
    0x30781d8808c3c800c41480381c108002441a81032107064038a6001c840e4204461000017030400300344081d900b01c4400c41d428000d51240801d40000f4002e1110b07403032030480380c41c50318031407600d411102003005800100240d507210051010010303242c03800e0380e0380389200054a85a01e091112002268883d1610921400100300020207e00e0004c5c4d004c1d001d8581a9034480c0b80c1d030303a40c400080003041191400d591000f8141e80018a80c1d07100d014010f14103104402805920155600f0f1519004076030300b015043c001c030514112511000051542d5000ca542c042150383c040c0c0e808030803902c4d401400703907540d0407103421400400c40000d956801c1000920a030f0715801c105086400031502d40c0001e4405a42901d4050075800d500c2d20707080710405070280640d00303484403590349640d810300b1940e01003000c0700030802c0880d90406040c3c0204003483e07020103203850781e0100e12040410341100c0a4a001c000e060100100380e81049480d03012246000c0d100000082100b40c0e103910001c0c04042d882c5110b07511410340c02888404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 72934228 1250 72932978 72932983
    0xb040b060103021c0509010603020a080123070519050f0409050415090804060e01020309091018060803041505070b040309170309090c0c0307052a010203090f0405060a05030604060c030e 81
    0x50038001c01c20202d41604c0902000b0150071301410001a940d00c0d6403001c00940d442c60071950060642c5800001e48400c60500a410b950b10a8004c124000403070040140c03864006088444461000110005000c072030310301903549000780c03031880da010b10003c100400c41507002d41c80140264001c000c00400301030380c28501d0041e905910402800e03040240010041c05000b080014281281401980d040184c12000b1503007484044461020f031181600c8108030785986205132908500d000740e800d02c8402e042c45031240da00d1050307101d00c2c0d00d030386150081c00740564454000e9511341e6502c56005941170030181001045a1014024030115038081c140798150418008101d900d221400b50a803805a0f440c482c0041c40c40d08642c802c0c90182c04100720080000307100344503481d600018503400c894195401650508000c0643d56003a041d07520801404209030360f8070300313554003c540031540403500b50790b06400729012100641c800307905440303902d09110420009401900141c00d440d13a08112103113401610b940d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 72935478 1250 72934228 72934237
    0x2128090201120203130501140412020f030a0806040204030210030504110d0b0112020103090218010612090b060f03010605060a1211120a0903030b1e0109080d0509061e070b040b06010302 81
    0x2400b00b0035112080961021640141d94070000f020804021a8050b4560380d095551800810480000c0c2504100411030b0810380d081c3e00c6500ba2000b0402c600000344420366030b1151461400c00e0292050021b07031240e480c1d40454002c0d5a0250281c40c6100d9040c3c000b9016080c1078030100c1d00942c034a4068142ca0600308204100075820204080d1603900e444c0c446082c2c400c075498160f041540711070380400941c80749a180e44004181e09840c140540c0f40c40c030b0082052508840403081c00e410301c1001c0c0c2c00b144030f0604054101030b0490303444080c940e403000064014216a8850303900040d010a803030754410b80090b01d19240403da40c0040c001c5000d000000c00b0240b0034040301000444464010505c000005c0d4046640280309041c0080c940c00d403000041c29040745800e01128041e01e01c00950754035684200d2200051094400800072030700390100180840c09011038841c00f4100101d08005581014004103420100d00340003182c0d541c2a40c101200b202000f113906035441c951020102d591075120348201c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 72936728 1250 72935478 72935483
    0x6080c07060203061503010b030f0109020f0d0c0e1207050109050a05010c0f0f060204030f05011803081807031406060a0f0b04032307091b0c0506060105212809 70
    0x500e4140349607100002074001a019540040c03d040d450035410005a00441c003801001d2050b03a1203140c0390310320140a01058225101182c0103200805640780000156030385088007040c00700714440302c1e14040703c3d800c1858903040d41c02009008000001d00000c41e0340419075a00380d881d00a4a921842480200e841d1845a40e00107003c841404010501810104007142d1041c05403580d0300d20140c9030041a40c105030429a0f0551a08180c60f0400c40240306a0a44284911060360743c45034949010b486284001c100d120380030000400091070213011702100f005140d024003000218107060300815a01c00d012940c043c042c40b05070801140388540810300c2c034110b450f40c45116140605603580c00408410b04046a10342c51207480060140c00b00c288908006008142000280103040d0717610301c84205508920007051040c2c0c407806002080c0086980c40c2d002100f820304c941d07280040780c1c4050307151884050170810445801c042c007908120f10140c020710040c040139118200410382c21040101c90404800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 72937978 1250 72936728 72936751
    0x10c021005031911030f06010804050d11030706020705060103141b060f041d041104020c15040f0b040c0e010e090c010e010516111005090d060b041e05100608 69
    0x98815244034100565005030084070080c22401212203c0d002e40e5900c10b260b4500309808030030003280807550b00c1860f52002c030910300741d60039040645034a511100d020320680100688102c144231400c0b02082110403080e44450704540e2543da42c00c04a0f104c440a0008654020b1a040000d0344200300044400507406000b040003292425001080b0550340680c0c44408000f009000c00034501400782421040d00d00d100c0c4500005250500d8200340907010034000c82c0c4a00e10600903100110b00001d40d644401611720500252070b103c3d810007840b040c50358000104102e201c0020001000401710701c2404031101b0385080100b50340c0b102c100e41e02c58503013100e0403445a4070402c02301d4880e620030055012900c006052540c81d00c04d005e074a861100c204250295148950038101c00b601e0b0034120200420344041f0b16110741031034886030000c1c00c003004948002d0b20454403804851800d80e641e902c14061850841c030030b9900c03035582e418440090001101e03055240e00780c0c0d201c0002c0740d9000700a814400d5401c29035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 72939228 1250 72937978 72937999
    0x90506150109061107090e060609060a060507080f07050a050304080c0301060e07080a0e0d0c1505010305060103020121022809030b0c0c010b03070803190201021303020d02010e190f05010c02 83
    0x1004c440045040c0114600c03845603070000141000640300e07980441e10040c029080a142c04006c2c054030700340181c1018000c6040440c20000241e011040e9680180d0022109550300419450080380b8003482d40068818044d0302001800c001000004004541040003944c600f100010300300b5080345c440f449201414140030001410041c4281ca2550340402408800100d068100140d180362040401801c0c0108040950b00d40c10300035000c00118446081f4541802150b046584540e00c030281848000c0c1402104184400d0801d2845140504000300d180f00b151240b454900000c41c050000e080714820303840da1001c003220039124141600c01d49401c81c0441318651210705042e15658130800350403100c0d5507a150600219036041c0f05100c01080542c00550300c6581d041c9001406091400032841560320400110004100c1d0031200000c5a4044517990284070721400140c2d00351000380c041c95841000800402c4103071503641c0f01304017a10040004012840e480310010f494071b100c7e02e0800ba6000c1807841 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 72940478 1250 72939228 72939239
    0x603180809011e030b01021009110904030909020a0302070b01050420030c091503060a0b0412120e0d030c06050105040c05030a02070c0506070602040e160c060b01051b01090506150109 80
    0x4000c1114000603d00041c4182c03c07407451100e80329919103600002610351302211455a410000000034640c200c00821846445550308030294680041050040e034194001505260103410000c000b400c0780b000c150754407013410000400a52005108030742c8250707120004141420306114900e12a2611410752400100070303c0c880714260402007803c0b2079400b04000456003074486104656081c100d0030070a9850342025004c0000c01c030030a40004a460400b40130800841001c3d02d0000c0c4226007060100515880e00364084070b15003030020f81c2503000707000001c0e980205a80b124030901c803240140e00030861030f601c910421040da00c035040d00e40c0000b5014000f040110b29140d005080b41c91240c403c00005503a504085042f54004510540350147e0210341048040c140d103403c0c90b440548005986c200c000030b03480160084081c808046e20041c1e0741d03040038502d6406141143c403804114000140341311200009640600f4040301c0844140c05030304042941e009200c00001254a4142c442201850904 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 72941728 1250 72940478 72940493
    0x80105190218090a0f0e010614040504120f0203040e0f04170f07031b0507030b0f010f051309030201140c0a031a09010302130603080a0c110901030b0a020d150602070f060318 76
    0x40d00d6520b0b03042d0303074810152620140d40305401c11b0200d80303000481c0d480e2900c40c0c2d00586010034142c02d8081ca0602e010000000d07440c40c8011040440790a1103401e400c1041d030100d1941c0511781010b4040a04c01060240426000d40f060b131203503100c1d00215010500751850100e0502840810401c554804d004e400d00190088c201200b044404580f0428095a140c554500c3c0c142c15601c2a1040b154070f0003802900b11003c2c001034003401c2401d0000c01c1c10791500d004505207201229a05a010303543d1420002010301c02e4000c458114a514164a86411b1201c8600c3d507503808203100300d01092610011070b2900020800c40030b00c412000308400350a030718540034005454201e50441c190255075810200c0007030845406012280c43c1c9550f84441c0200d03070701e0400f18103030245006e01c0c82115003c00400c0051007403c440c50b4130050311900540c98018076a0b50601401041d4902c1c00407a403800c0d00411921350000c1c014080b0390040c400b00c00c14503521b01064040f42d000c640701c140c80306040d070800008203405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 72942978 1250 72941728 72941731
    0xf070201090c12020d02030115051e010503010e0c1603111b06030403030b0607120503010e0603150406020c0f120304050c060705030702041104180b040e0d0806090402030c0a08010519021809 83
    0x5170824008441d01da0000703003107031409012006038003c40c10040c452420b102d1803564280e004051502034145810700082d206000c14443e5509010741d410000301c2c50b051260607900020000195544440c0e85807401420240500b204110b103032246103020709986c8a25420402e41c1c00002d441301d491912540c908034003604014a442d030300840f04000b41000100446e8018083d503400e503880c03a44950404d10030240128002d082903110354030190750b0f12482c401250180d80c0040d4000b40059031403540340080c6040c81008081e041203402043c01da041c140c80020010b40c4654490003c0c0c441c558001700401002e8040c0c0c80300586681e009006031801030500e5400b40e945004170005081c1850740d01d1107a1040c810011001c0c03c0c683e6210503418003603040501601001c6800107014041c80c800c40d604c0242000001000d1500c1983c41d400802c0540d00c2c103004407035031100e005d4441d4481c1a100c00044e40a45402d4940180d890a210921180c400c000e02c01d88090300185004880c8130130f00c0400304040c0500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 72944228 1250 72942978 72942983
    0x3180d050f0303100302150a080f061908060406050a05130609030302040f06030c0f030b010507020402030a0221160f0c080c0f1006091104030206031605070510050f070201090c12 78
    0x5040d071080407401c040028502c100e080d01070019030b01d410340c81030021802040b00c08200d009002d022440000b50042103903980500140c010800b196108800100740f01300072403c000300c45070410808a0940800f0521500c034a00401041c025616180170060840b0380c1210360041c060005a401400a51a500001134a038080d103000b600b095181c04105601c00f08642c41000429500d442030b41c03489400140c016004082030400700a11040600080c01c1031145c404021310a076030000000303603443c0a40c1d050b50340c000107030380542c81401c83c0ca072201207801e070083d5688104010400c085084007441401c0400c1043c1003580c0d402e070800e040f40e030703941c1c0d0980045402104a0040010f50311803600704000d0034018403410080401c0c201d1400400c0300441d0841118a4140300c1c003000140f000d81c0329203040344d0b001400124407900b0003c1c501001c50750340c02a10001403041c061226034844a005a40050b802400071101908490300c1c0c0d02c0051703003220000d1400400c1214031240800c001c00c00007481105260 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 72945478 1250 72944228 72944233
    0xa0e090304180f0515030105071409040f0e010c0305090f0601080d0302031503120d0c0801080d081e09060402040605010503090d320c010608032706160309050108070203180d05 77
    0x140f10100c1074055a4003124015101c001000c40501d091070700b4000c007608120741c0d00341000c10a03407503500002240700340b4130703042e000c1d603200e012240e032070100391b8061031105412500030032601c1d6400c02c00601604003a00c0703400062065200340e92078040302050280c12110068014010001c22403010b5010750001080070142100d000c8016401d43c1f0280705030701c8410140c1130059a07907500581014229180b024040d0704010120700107000007400095812824101e034103150481c2da540703000d00e14000d05007007101c0e000001c0500c00c0c01002a8005092802144201c50601565448400468450004464402555000354800c1410b03600902c80003060800c1d0114108000310450242d090b2900301e9a541c000328a00000c1032428a8400c3c440c03400542600340140d4901101ca50404155000007400c1d03108200229500011076980e0300c0131950544424144a04804814100602052418070909000c614000d0005001520200883e83c03601c90051207290181280002d00c80340086569007101c3e1803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 72946728 1250 72945478 72945491
    0x6060906070f0c080114010302090c160501021905070b19021605031902030f1227060405070f050d0303180602040305070f0f030804060c0309050603010902090a0e09030418 75
    0x9844040c014940c150140b030720489100070500c0c0c0020b038803010f0361090480da45083c4015104d5001184584c0c11650101c2310895644c603040440c22a41c4129200010840400c54480c420010190041c14005a80014031104640544416201c41c49181c0004010340d42d414006466040b80a12001038004840d2005050030a0b484800c03038150201c103000c1c1c50302e60001c9246034010f42c41004410030340455201540c20320041e10780d8008680107600302440400c07560030005541080e0140b42c04c20f010046051030320003251007003000c0c0d240c11064400b43d809010b86d800126045010845000031188060301060b5004425141207005003400e400c02030100043d400b0083c08504a0b001030000382d800341001d004141d14055141c6101c140f9603001c1600442e0649042012079520b134141c0b02190728600700541c1c524801e1504952000d515041140e0003600840049060036540e4007405a0040c04ea41852885840d5040803078055402c4405c01140d92041006000b101d00511280800d82d12015002c141d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 72947978 1250 72946728 72946747
    0xd090f02150d0e010b03030304030507060b0306070f08070809072c01030c080f010902030c010305130213050a2a0507080d0606030507080606030f0103240e0304050312040b040603050606 81
    0x1088499010520528030100d0484031240c50703440748141d03104403480200f000c05c4003000829182c0c00000c1c03001d41440804a81e071801e1045980004841d00740007006e5800e1450a807402030801958000914000341c80b038400540700c2c502440c3c1450243c00310000420f0118034000400e090040756481540350020718444003c000490310100502a5204442114180d418030300040d18011030030700c103000c09070305000054001d070324003003040b41c440b01d000c0c680801c05603190a40018401d200c000029080019078820202e440398035441140200b441c48400e00941005540c030f49155204809200d60f41041040c08038034072400342004100c1c0ca881181c249080424640c0c4032401c80d05c595001c0d0000c2929002000309960b4040b1505a1280080722214150306100000b803090100501004040f1002c10110554102c081000b40070751b000c103c1800e112082404200c00d4594119116050017403040e00d84407078103450450265400c0c4c98244e20308606140c82d0070702c200e001d040b015014641220040180b4030700d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 72949228 1250 72947978 72947989
    0x304080a0501020a18030c0b0703090512010b01030608070806191107080a020c060705100c02160620210a0e0409052a01020a02010518090f010806070201050c0d090f02 73
    0x140c9005000040e2904e808050250040c4049000354014521842c0240002a0401480410b85800e1000c0302e07100c03085031070117842c0300304150843c0d80d0240c40d4184140a00105401981c0c95420a82c1c081c80300315650030146940b4107250141c0c5803203030030950004508805a60240c08071500020300400c0e05100c041160342164041e4005603408240025480d130341503010030a43e038202e81c098542503d0004240c071101c0d01e50030b14038204101151600d0b010032503148200420780814850540790104d4a51790207010701444000302d100a0b040140501a8001110100700d10003001f0702c002000903d80544072050740d41786c0c001c03e190020301003150540c40440e199482a442d55900c034100620f0010754a08141034100c503070001256100705054108421a640894020702d110340c20709104d03032510b40c01e03d07120100c010040407040d0440c508508000b81e9110361075201e41240e900105540e000d4032810000c034280e4904603081c40250000f0801e00c004d800302c550005601500480b07240a1300200c3d03074009007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 72950478 1250 72949228 72949243
    0x190515100215010e070909181e0218090705090403020a0605070801090b040614010302090f0405070203071707030914030a060c022a10030506061303051506010f0207031202030408 78
    0x100142c0c09011144030702c101204809024045404052210f071400da44000c0800d211801400582d41e00c1c0d00c0c55140800b440c0b2020345690b50300220007000c2030241c43d040701900b0221501070348200d0400003c104003201040440e4000c80c500c0c4d0140075000c0c280801e000c100d40003d0011021403040d4120700000c40c1c424810180244004d58880050b545402500801e0351030400c0d2040c030441c6031810420100d10400300320383d510002800d000d40c0341d024610001e030b134010703003400c0258105040ca010484055408401810b249110781c1c1c1601c0c18440c2074040c28158001d44c00010003140c1c980605201ea65400085810b8090307008040306c2c608141039481e0010743c5c14000c01c04016074840c0070b02c007091040403482c48012001002d11540707a108550001844a038010780c202081c159240040361064681104652a00e4215000a60703110340d01d1030910786e01c0505500c1100c5821028000c615958814080c0742c003030f41c039568010031100e421601e0f60b010410000b04004207500c000c000010b00c0e00741c184400c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 72951728 1250 72950478 72950509
    0x10909051902090312220b0a08150d0f08030f0f010e010b0d0e0a060b01020d03020a140702010c050f0a02011704020f0907030e0a0b190204050303041202150409090c0b03190515 77
    0x14004011300c000704030121b00c5030f42c0015110314400d1015064017603000c940741c0c1c0e0017403d5107000104001c0c4440407031680c80c03c015010b09003109900c69203040c4580f0782c000718011490003200250302e0380c5003110340158504c20700440b03540007100401004058074600241c4210703809010005075074000e80d08124038003a5a002c0841d18a0703203402841241351f80612190005c14a941819072400c10501d50092841042c7c0d030036101c031140003280d00010769101d40c9000d260b0a41c005d013252141c4c503200800e5a43c8101110040b80020300c4282e4020100c21844070f414007a660103003004540440000801080c040000c151308101035554580b441c04441c20485288040d014500360007071400e02d9402842c1000501c01103182036070040100700003a807400001c44044a030b010800340d10f40f040500c00600b81d685600f604903240c01e0040ba0100b4484c016520007510148284100320303c0c19500d1540c42c0b11804119509074507a8120810286d80b400c054002c15480f0000007050782c1d00070310480000e818202e681049 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 72952978 1250 72951728 72951757
    0xe36070912060b041d10110c0c0405040f08030405061f0501080105060304062901030b19030b0703020403060c0302031e15010302070f020306040b040c06020a05030708071509060b010909051902090312 87
    0x440780d144400313106048401591130b1f45203250452010323010340d443d03c04c100840c0c0101e95440029080c4040c0c80240000700394002c410315603074245410030665400701502c0c036145640302040c2c1d0111015240294508903001a121003041d82c2c030b0101000300c51382008105030703002ca0711015800c420aa90b01418201c81c1e40c82e00b171054035125030310001401c44908183e000c0c000c003500300c0381c40290714000c4490001c40341c1c400b082d22419512028200c01900032a0300c014030f09424500c01454080d010f401a510500840e20080107501a0002281800e40d00b0343c1c42c50f45110200360900560b5102c0c0d0001c1c10154040c04050140361002d80c0400d141060888094442030281010303c4200056400380c10020061440106010400c40d29299142e10074412f00401100002030808100003403000000b0036800c54040401140141e0b0403c14080c140712032105000921311b50000c106000280f06980c0521440030285050002c00b1003010000e51011a400742d00d0f00c40c000d00d100300c1c3c0c60007800500350f21581000c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 72954228 1250 72952978 72952993
    0x16030302030a1404050c04021c150e090604031e03020f0d1508060f0708040f060509071a0a050f09150a2a0b04030e36070912060b041d 59
    0x1140b089412010100342d02d81d00e8202400080784000a041e09400030858006039155100c10766040d801600c031181d880c030300e4107000c001e0040801c19006276040310200d1030b03c0b5245d96039500700703161070381e0040703900801089613054860301189020b100d10b9030040440c01c00607d0000421101c4519400000340c0e0303803510382c032042e01c020b544844200c11402461154000c0c0020b08180081000e1000300078403500401001d0800501480195455003130300d83c0d000718013003143e030400030707030043d1512014050915060031060f040748581c3d0000048030048a0785540d40d40c1400c061014106080d80410580d5601500e03606000003410000c9000780404046510b8a083c0f44807010210100705c2041c00d0240e2140c000140c100340480c1500012580c456410f28010f11383c0d0440000140d4080c03a5085801900c0140d0825034420090941703220403100c00d400190755881c4c1e1000780c01c6801c4c0c051801200d201c2066041c1c40c0300090925084419101d0b4010004102c042801a0481d101261001854501ea01100703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 72955478 1250 72954228 72954241
    0x40201090b0c1006060f0507120c0b010e0f0610090e040203031e0a020d0c1523070203091e0a0e04050c130b010305090c0108130201020c0d030f0f09080d0f0201021603030203 76
    0x2103071304000e0041c0d0074000d5490010001c0500140504203010380140c1c241002000058800c0b050040f00c02e0b4080c00142081d61102c0140401e41d10486154003038509a40c00300e0518034040c0e01c941c1400e8016900c5c2c0344150306241c0e40e80c070703540e00150040382c1600c824407003090707074640f48805a28494034582400782c4074080484000e160541110518041c403040001804c0810070810b09001080c04048011070750000c01041407904d99a600300c4003108010180034404040d03408002015100002c0740c4201c0c01600c021805003042d601060000d5015500c40000c0011809040900c0c1c2c0c00342c0101c0136a070094903000003041c8001d14003400c00703440c2651809111840c0da014850305402501c050014604101c0702d1002803e09400500042e4540d078030513001c1411a8420040314541484c0a4980b0740454414036011b84159200d24295001c504100c1071003103018410148502101e4588009261400358200155068540c9003a0281155000c102111001c810700e0b130301c004503a2180d5001aa20715110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 72956728 1250 72955478 72955481
    0x3120f0106080405030940061e0317040305071401030f200903010f02040b1216050d0b1804150605030102070201020705060d02130308090306070c03050a08040201090b0c10 75
    0x141c00c41c00c180403111052102054001040c0d9a404c00b0541f442c0c42540440110100c90728603a410501809030344500160f00d1424605003007007440130801040c0466074640c44980300ca102c80403220010213501031410000708424002c82030080e06048203aa1a10303407a81c4840f0708002254004c182143c41c5042c8035111541e01d4812003070388003034940040084a04807101011007a1000b03009641d80503011604c0c4080e56000e501100c10301c22029030031980d40b6541d0341c50a00503044204403420038000200050b040b25403141401100303049542d116868181e02c0600c850092034201070340c507000704030307200000070382180c03900300c0390265001c0c88101d02c241c40c7e03040046c030a0b03d095401c218060b03401032200c280140d80010b001405e442e400c68401d62901c04201c2640000e003c4c18003500300f40042918004140103042000301012802070b41595007541d50014281d450003140e24006000a10400c00072549a01c1846a1904544145882100f06a44c0c100c1c9002d25000000204000d4000d102d039401e504215 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 72957978 1250 72956728 72956731
    0x307090501060206161b05071e080d05120c1c09030c020f0f060901050c100204030312050a090812040c08010f2a02070605031012080703030c030605030c010e030f03120f 74
    0x341405c4180f18120f4100c01414001c0c2c4805001011002c20040d404001040c80801c0c00f804090381c100071481c891001410310900548074003000390003030207600e0300600d114000700c503922070344600c45103100d8035151940090b5502080d40c0c15150626078519050340d924038012240600e000360b6949145890707500401121042400c1000e00c500c0d0390784c2d2528282d84801b82604e403050f00034205662140030240900382001d007061030b9007214500c0010080100341e0020082441c20004c1c0004000741c1d40c0784440d441c02c075040d83c1d40c05002a5070a101d40400e06516183c066440f5101e0303884c64500c190b4034002d45003034401411140c8040d58491a5a00300e101e900280700c0380c58000340003034101c070209a8402170344803020b90045104000c13001000a82c961803540c6407100070091075501c84503010203410010b070b10303421081040700024204403545517128400c3c02264103481005029010902052005403070140c030015401d84c02d401820040000c0c10020310140003081c003102102809441c108587d007100e10300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 72959228 1250 72957978 72957991
    0x501031208060406062309030f06040c09020307090b0a180623030c09010804050a0b0408040306050108031c0c14030c07210203030a0c110303070e03060601020a0f02040b0402090307090501060206 85
    0x1d040c40403c1070651081c11403862400350380032a01c4486d0f10704409021481052036494040c1b00ba00b030162180c6000043c11841350b801000d0031841035890344c000c03000341c0c481600c0d86000690103a00c20320150032002c000f49100c01840c1881004900b4059450023041d40303642c81440403440e1000b4803030350b443c4211a08586160341d6550145140362004401240307002d1080e120781004001c20000d020032404001d00c060064001d00c023122140b8162801040660084c00704841c1c19007010000a140040002950442060304c8110b00c0c0c80312044151200804280c2201300400ac03012043c0011100c90500560041c8200c0d442240e46028904250340954060382116004950f03952400c411540d010040d01d40003442440c0c00f28a0310b040b40b40448a0304180c48002e22140000824080c0d201c2d004400140301020560640e503d9680340001a611070918580c050b1000c1401c0310b07500014682603100035103d01d00200018100720400e030120b031070819503410030714042c0d58580060015940405c9059071200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 72960478 1250 72959228 72959231
    0xa0e10140604030305040915180e070e0106080403080405010b040c0c0605060a030305030a020f0715020d0501151d12070305030a091e0918080c0109021203030702060f040f0605010312080604 83
    0x3d1441c0d600420a10680c4550b0f0b075016a200901c2c8070402200d21204020708a2601c135000c8100d1100e40c0c0d10090518018000041c400c128002400850106085040b00c1490302c80300d910366601c2d101034030485001007045a80d0b5680e15101d032003507a0740d8400c1040ca040c1d00d0392042d240c202c035454018111f8001600882c401c0316280c83c20000070f9441002c5aa000c8004a0003688034406070044120f580075000c0300810b02007016004801c00743c41c4c1e03400f4004000142d0b1080c8849d903aa03002104810050805d00000202c610180a002c50f9481c0d2541c1900d01000e482801580c01c600881400c10046400c00c0300c4a400c000b9104501551001c0d842001e048691183c601c400070f07203030309420044098858580c100c1d40b14120031080c103014121414081d50040c0d02c8030758074104001d45c5070080245000492095400750425000e0103400000d4a1141e80150010880358449035481011064000c0c0308441c4102c81500c17540010b0294003969000b035102d80d007410380c400e89000000d451004028686800345 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 72961728 1250 72960478 72960487
    0x803030c030402060a030b03070605091e030c1216030302011d0c0f040c020a0605010b03181506090613020d0606141309051306150305060f0702070e060a0e101406 71
    0x200003021280c10070350480f00680d55080f24101500034114131014140d150081c40e0000440e00e411000a281802045580200f40b0000d050b00e000c2070020008040d803d58800a0b80f80b450303060140c11065500d1a550845034400005100048044070a400480040c0d4413490b460b0b28034440c0180b5200c805200402605825100c3c20210780000704410450b80b007651209040300300326009000d19445160064018040d541c1c5a80c0044183c0c1e0007911300d103510b41c9280c0d9070126281c0c00400d4510580080d1502805d658032403804000e2109400303001c040d80220382060b8507400d40d0360f91008041a5003107610103d519481c001c1c2c05440d5001021030039000c03c000b00712881511607614402d0094034096580020307503444a40c45411300d22710301c08000300071610340500c0300e005039a101d0041049030710407803c441c01903076100702206040c14191014805071380880400d00c100814081c906900c800041d0000025982d213400d43c00069200360b07482410401c45507001d0040c22403502c218070f000c503416074103236181c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 72962978 1250 72961728 72961741
    0xa110312030c0f04090e070f0803040e060d020604081006060806060306030d0f0e03070e01030b0106030902030d0c0807080a0807020d140906090a0512030a030b0f0916031401140307080303 82
    0xc610008012600710000020043e044659803401c0e900a80f40d802810040702c80f540c1c688580c1e1b0079150207403107079954250000040c0b203100081183d05503004407021091a403240400e0002000074031004907408901440040345152081103082008a00d1308004a034451030200c0c06418140081c00c90750142d202003041122030340300040d40b240c210a443c980544002003600040b1099080a4141c65150144210004032408078000e5181601d00910321402c0b00c4c2d917909170540032681030090080d0550040e00070801c1460180c00406506030003040050310b401d40e941d8540b0a15400404c10307a0109005100b40000f441d810130089a20052904060070451500d034080c04850091585031403068100113003200e41a10352515240040502401101085c0d5031083c1541c0c41c0d401014401340040e141507800d2009140c0300d1482c00088001904112182c0c490400c5032004032100d91100c0f050680300d84806c80f490902e08202402406030400705000800301004041c04c108a41c2c1c40004554818001d0081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 72964228 1250 72962978 72963013
    0x8120a02120402010804020a0e0a06030308090a050a140307060f0207110d0c090903020709050a020927070503180f030a030c020105010302100f090b040803070c05100e060f0c0f0a1103 80
    0x300030f60242801d506590381c4d440022a0310985400c0000080204c50912508000c1170f04040c055178841d4032010070668603a00034580da114554030180c07880d07214010f5000460034840d0081c0340032070b01209907031a150490300d81c4c00a66041f42c0141c28070550000c2d01d07a0510181d000c0d01d060010080fa44100b807105a9125031150079500c2c010340b002d50340d841c18540308040c001c11030380d0000d01c042403092145181c580415802900164281400b804200841c01d44040440110408400340d240b070022407600d07408030071941c6810051590507041071009000541c240204800300c80c94200d00019581c4039041600201a581c035180104107580c100720040c00169518041c680c00c904c01890f150030140305022044401040c00d500011b0f01150001d00030031001400300050042a0141001c41f282c181e40e00d040c8001240d213421034100040c18000c0300310b801d1421038003e100c01d0100030641420044903030b801500704000c02512840075030108001008126231030350070a624950860281603c05294240b000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 72965478 1250 72964228 72964231
    0x80d09090509160e070c020d06050702060f0c0a030203060423010f0b04030c05130212040606080c0a140f0102011d0106090b0904080d11071703041b060203090609030f010908120a0212 80
    0x4d40c0705414900185589105104141000350000c025081c0e0781d210b42000001041c1c2940e01c000140180e41c001682d0420807903000d8018445034840707603e0300405e035808500039000a060180c0c0282c451001c9081288042d01d42c403500c0425000342036013545040d8203280401c51a030b2004803190028081000480c0e424105402116815a52310f100c10b444145640000c0c46500c000c42e4102581c601800b041c80341c0350307204ed01034628400841e442c0c000c070f5404100c8284880c0c071402183c039035890010040c42c2412507600545036018000850405006445282c40000040c1d10190b41c1e95101000c102180c024005d143c800402551004981d09164a400c8050722409d0b01100c80d654503101d110443c503030745004640503981c000b1103004251155044010240d8404e44080e41e0390042d0700341d07014030800145035450444100360011440c0100e084180b00450700300740d11155050041411000d11034400f80505031501d44200d0201c0c0d51000c9040300c207a0510300c007070b00a4402c144140700c404581040003954a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 72966728 1250 72965478 72965489
    0x60106020709050417030112050705010203070206190e030601081011070f0308070c020910090c02010e1b0d1b0314070303020c040902061c0f061d040f0309080d0909050916 75
    0x10070355584d2802d001c078007244002d500036040c0d5000400022403106c80040d074402d1034400c0e000d8a005039640d0004a1b03413402080c101951080041208800c0d0b111501591a40c00582d418440c111022a01c00079081c420241d02014190b004840029201c044d02d1180c0007014803442d1009091250301d403039078440280d0b07542004041c0075000000c0384031240904402410207138028030340daa861030000603c160303425503485880c034003c1c2005a520304250040c000c441c441e00e440e00091003800c0455007008004502048840e4010107280940400310300f0f403800090f01d00c0c10320381c1a009e40c94074610f0008100800ca40080d0b0230360f04028030510001b580415610040c131800c9601054405003800068102d103c3c0c0b151a46200b81994402c2030003a100703421100600d002803a082005650f0703141c0000a505503089404109205200014001003aa12202642502074940400003a440700030440c0b902001588000104400b0b203802c003c0b40d5220b0240b1503101c01000301500c0310000c004002d9213441100e010f0f4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 72967978 1250 72966728 72966731
    0x1110c0714120703050706200a02010e06090603090106030c06050f1813090308042013050403090302030604080706051605160302030d06060e1f050f0d1b03050f09060106020709 77
    0x148040d6842e00070307486150302490300b956400303a0b5900d4000e5803080c0b03501c03900001c129611709000c0c10720030a0000b000c05400c68009083c0000040e4011a450f08600d1072050b441402403117008125203600018611448145000103020350650a100310405816440788013003210410030044c0300f91010381507546051500c12498400c2300030400080c5920700c00c07092070105901c1c000c81c1d035061543c0328540c0c501690003860359040a54092a582c2e01520580c0c20064015220b0616010003221f0755000325071050003864418a0706849900003807c040f4191420b891144003c20072005008084c445c0641004407000001c80403101d24401a0890041e5000d900a5651f00320740c1c0401d0600a004452800081c200108034903900c90801409175200740007801d014644840f64041c1113409580513001c065000d0300c0f40c908110340118040c4c110340c030425110042c2170301c034640c402259a01c0700c0150074505450b02c02148138500340c08140c200c1000181200b040364444401040056000300c6c000c010350716140c80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 72969228 1250 72967978 72968009
    0x13020319020d14010c0f02160b0f0405060c06010312030c09050105090409120504060e0609010905120106081b040e1f0c030e0f030a140403020a150e030a0308070201110c07 75
    0x5184101c1d4820150401040c03841e0450b1282c07040d80304004c070b45e03065155088131084d000300481ea22106088102440441d80d00180080c0204d031002e0f0440d48040000030f0303e80b9071101c011a0960300481d040c508075501c140011300c20003820124517942c125562a007001681c8400c000244041101d120751340c14003a00051000c1c0e01d80b5507400c062400b85c0c0003480b10f2620310580700010500d5200d480754900080241040780c142e4a001e40407117a1031101655040c0712241401c0c10480c501c5510404d41046643e94840014520010b002281182d03000300c40d040c000d100002e00b0b02c02610301080e81281c49401031001082c030342c2040030031100001d217031940000300be00030400182c2c0140502d0440e1a0f030751180c01000c0455240000080c010018a1341d900c0e600707604042d03038030542d601503400025031110f04203405001c1c41070b031040d03454940025032901500a00480c0080b0341441288103054001031014400c000326150240903400481d520388407040c0c945144020380d5502c41c80305003d002070003a191103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 72970478 1250 72969228 72969233
    0x130306090501021e0c060f1906080d14070c1517010f17030c060f07050405031b0414010b0d0b270610020304080a0f0f140a0506070c050d030c030609021803010513020319 74
    0x590014101c1c03040f0348e0800c4029212408559203180f410358280000b070f4644a41d1840c05605c0301980c20780c81d0f005070100c05007402c0107061621022030034924820001030031500380c102c05000303c0c154001c06042c0c4d900d00010b8140715489803000b0b80550100c416500030044140010b500003017450388014103034140b040d5901d0b0110300308e6043c0700303a500c1554140700c4d40780a140e96070240c0e0b0490031a00c0c01120200301030010480b40611a240c00d10520308078400510800c11082c003590450000220300500380c110705981e0a0b0800600c0c82440942c2007029100b0040294078100616880103c56641c001181000d14200040769220610b10000b00300113404001303031040003030b07595000201d26030007180015050030645040f5900e5401c1c1c1000c0d24140306000200300468003801601480d160484007601340444d00078001d402800c51a40c41004240c0d991000250344411403000e0042400c1c81c100000012440c03130209400d446020781603c000601041c070050059070006110300001c10328401c0c4129032641030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 72971728 1250 72970478 72970501
    0x6130b0a24030606080105090d0807051c14090f010608071202040b040e06040302010f090b010501081008010608010b0f090f01030b04050c0607060b09100503060c130306090501021e0c060f 82
    0x1810949081680600c0801040100e400104c180c40e09107008100030340d0f81740505940c5845541e07002012504406c04107140c1803181c002811044018804040d0566141d00f207c4102e90010305d0b8845254640000c2c410281003e0003e8a2141200c5000f4880541482280780e200d00140c882d129080c280108800219101c0340c000c2c903142c8100420402208290304800350319503c08036000c17030055107000303d400819401d074031403c3c403030b00d81059001040b40c0c20b100c0192542c20020300031014281c60941d0000d500c0b40300f40928006018107100214524444c801401114409146007038481e14101c801c01c084603032145190f904494003d50950081d4881e818540c0c00d1a480c40b56003a0003410008074602844503035080000c404c0410340d18054160350344440b001084010380201ca5054004902240c940140031001e0038141801c4c500390b45809503680c0da240c0481c1c0300510308a603140d4000c5200d2100100d80948501c0d901032030b15915180001e130b1820580c4452000340a02e456900ca4000b09031100c949 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 72972978 1250 72971728 72971771
    0x10609090914011503021206010b0403020609010c06110901031a031b01090e070819021606200d05010e090708071a0f130305011b08040b04030203071704050306130b0a 73
    0x10720000b04913a81c020902104a01085d0109a0140f00f442141c20744d074400c00586503040754a2a02124202400c541c00c01c2040c0c1d00c0300f00b000d03040120552108020410f1840f89002c608082d40503691b4408005001506a9011101c240450b201a0340d1030f00007500e0100700a404901c00e84000340354030b80c0d644010307a95280582c1003030000e0f00440003007000f81030308508200c1c02003020090400d140f24030f0028410507882000c4200c001c8401b03040202d40020f80b25003101d03c15204c8584c0d2099801d085030ba60b200184c01c6450b0321030010341c80e800100000090040b00d26002081c01c0c01800038139041140c1b00c0c0c0d4504030b5200d0300c001c9601e400ca0340d40f00343c60312009032108401d0b141e80c4a903036046520410b4000806901003640e05500e007403c800c10321000d24640600c100440d0715894859170300d580b900d407543c400052007a402d6000030451000081c0ca95821001c41105a04400752aa801d0138241841c040004000c20000e0014195035404038040b107100550084a00c000070030214100c56076101c0303980f43d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 72974228 1250 72972978 72973013
    0xa030b04050109140102030702010609050103050c0f0a08030c01290d0b0403030204090204090207140d0e15070501050c0301030c15050f0309121602090a0603170714101b080106090909 80
    0x2c5060004c2d40351031040d0015401020380364000c0c4509525000d6040c08c0303c0d400c0c4801041c0d54043c220300b81c0b0500b400c0c162600c000360001c20820440d5680d60340c09046921500d200400799540e40080c2c58140b5120f410301c40c01608484155400300c018074007003449807405480140c2242903000005041600c260112009416005425900c40b81c0c0c8401090203500658000c50700009a0902d00d440601c0003d411008a00180e0791442c0c0001d10005002000708404204003c06004100400101d9403d00071640114000c1c4d03c00c1d5640d42c550f0515081c5080c02d90440c07803018030130325101514650b1120179101050501c000c40b82d500c8d03c4009402d441e00d003c4d455440c0301440c000c16042a0301040c0c03c848003449009030341d424038031790fa07444810080301d03620301000f40710080411142c8030704900f1713102030242c8510a9110708440d0840c0d01c500c600d41044800101003660301c59081001c2d0001c540b200035400c4109040c0034500354102080078100700c940b402540382c159034903082c0109102c41da1209280040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 72975478 1250 72974228 72974243
    0xe1507020a03030e01120c0f030b0f063702031b0c0d03020607120204051c1a04050a030f020a0308150613140307060f0e040b010e090907140109050a030b04050109 71
    0x640d03902c1e0251135a00c5020720b0034086090807140e424401c90601405440803943c2ea00c00d501c66070014400d400130031840640c0303500701110a031900302680307409004084031100e02030f07400341500000380316081080c14000700035200911205420b282c9a000029111100710a024001601b0091060305207004040e0300e40e103500040c004110024181c0204545000b03185507070310160541491030049003130b4421480b83d182c000c0720419440e88034a24030f2841c0c502d01403085140142c1030b10401c0c2d000c0140201981e00340c407a45c10251903a810150010000c02146c6c807280040c048941181d100075040e440003d18004400c0151a501031980c1d40b050304840c1d41000c1481c4481d4941e40302c11824001a00702c2000c0b60080c855890040341c500d000351030389403843c60103684200308280e0344020b10000e0708d4200c40c0345e414401c140b5503c0c011960342c00c081d94800d0202a0017043e00d81c0ca85660700000e003820707102e0349040c03020009041c8481c6e12001181415244c100094113110307210b40c030b025401482ca00102030080b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 72976728 1250 72975478 72975499
    0x20d060e010c0309050c010906050301050907090b03040305180f09060409020a15050903060f01050d1101020316120201051b040902031308070b09101104052206080c1507030e150702 79
    0x1150554401340302c060269007100c00038480a001036440074400c0c000c5001040d0180010442c510300410100c1d0301584074500045084d40d15512003000e6003082d03400328003090002c01c1c20503402d05d40204a04d80340c0c404460845034001a0004140c803503001034100d90046849800550035500e4400d0540300511030640c2103040800da282004155030001041207229014220100e1044041141c9540c10f0380c2c001844400c940c2d11642c1e92055004580b0030b03440c1580000e00440803031561414211101c1070058025280606003000700a003141c0c401003210801c600150340318048001c0c500140c4090310140c01006030380c1c3d00c45215039020301108240007000c808001441800f0401200c0e41c1d5070103001303004e080340c43c20079500040c82c09440d02250120500700302413100b0051071905084511101034030141e5082300300d0b02d0203500001d846043c3c01c170760110350041e4140c41e080d0a02d0348000d60344036000011a4113107074140d03600130945101c00311400d1203601c1d562540e031015104d550455010030b42c002d2035005130 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 72977978 1250 72976728 72976751
    0x702060318060c040e091c030902040b0919060905070212070c05090406050106020f060c0a050d0603020d0615060c0503072301050f01060e040209030304050904030504080a050a03030516020c010503100b030901050a0b031504020d060e01 102
    0xe07007100300c449110f4503f03203840040c0700c03d040d0242500488158003d0004007007681c080c50f9403a040368409544170301360b0800c0041d594a5a0a0050003176000d0303400481c2942c1007074006032600b9200d600310072481d401801000014107440d400d540b0901d00341c0c60302690b034500789002074014001031b03040694031008001040341003003100d0b445050001244240789403001c1d82c80400b0340b221b00103050040c19640081101000040304082d00b001454140f04040900300901d00300c080c04c454084980d41f10540c2032500600002e03030000030601c04404110f0b82036151404007008207489005600c41c0a004401c0e400100b07007010701810503140600003080403100d5440c0d260403e0740e550b440003031090740881d1814000c6403008080c4a042d01c81c2140300c2d0001c4c01284410801103c05a100030903800b401c580d0400b01142c1c600e0840e0003035002ea20032200106040c01e10324600d404176001d94823024460361040004010042030040e1080d4080e40481d08007200c00780d142002d0010301581c1c00fa00446500e800282410f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 72979228 1250 72977978 72978001
    0x2100e09010f0303080601090e0a02030a0905011a040b03030a0507080a0201200405010e0a0b07030c020f040905070314030403031b02031002030115180b0702060318060c040e091c030902040b09 84
    0x490b4041e5170b560040d622003070300540303603e51180121007201024070001102080550000c58102a09a50000d4030408a4407650b0841d881044a4441070340c01c60300c0ea8500d0324150240c1140c104049000e1031401c80329040142c003c1c0305100d0001c00344000414000c280314003e5001000050400500007c0b110034050107a15680c0580901e5003ca088061000d0190070881160010395a015450525028454030b05880d0200c65040807139210a680140c6034281c0c5a81c01041c60592090b0000c003041410341c03401d0340028003038001c02e080540c4140030400120707070b1209102d00324090b0942242d41c00794081c00400d00704460011180703145800007000141e09500101c415010f41001d60300d0304001c503d8104056481640d070303c98505500e000344480c0c005441c00c24001c540000d241540301c044811400062401c00700c0440d003001a9640218041000501560850f640054090068592914803811945510000c2a90315040603030301c2400c4070071074807564131043e1114030041c80c105162403c11901d10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 72980478 1250 72979228 72979259
    0xc0c030b0c07060c1b0618020a0914010e0702060103031412070504080f07030b0705090a05030703060b030f0f1f14150a0503010203160311040b0d0504060513020d02100e0901 76
    0x100c05516000c103100d0034500c200003059003071071701d500c400454540e0303034071641c01034000c2c1059003403000d41c05090b65006030740c1c1503042001001201030214484c0c0381420251a0254140c1c4400803c40d10320f4104561503902050050540b80d00d4281030100d0550b003010324116029080304c4419042d80715080c88650303504140a8011141c803402284d40c2d00070030307295a50301c420300b030710009180d41440701c082042c0c50f01480103841c450700301420b046002c030b0781c84000130b140140c294000d507030f400e40d10304100c810350605206030680702d0208801881d280c002d12030300558900803419035807204401a44e80b4664000783e60005a4059003907000e003000b9040020307d250404111b81e4100f031040d1042c5000090381d05060094910640d40715542246440000304242c0142502c0690f0420130701c400c100204548864034007a1141074409400002d00e442c2c2403401004440024008100381804000090010384d500c102428100303a05071002d5050030b4940c501500d200e10054081c2d54040c40750400800c0c00c0d041d04034000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 72981728 1250 72980478 72980483
    0xd081c022106032103060103090606031a010609080a0b15060d06061101060e060f0a032a0b0c1f06090606180b13120309050603070806090a05160c0c030b0c07 69
    0x3100ba2120700802d5131300e09100e610165a030048100c1c3c206140c01c0c000c09103520000c10304000c544400d065840034200c402c581c00482d0720000c003810f010030807250403081c180501864200850604e00300f0003141c0c2d80d666142001003c002200001501c000d20a103895080101701801c4682c8030009100d02078040c1106000d094005209841c0e4074000038014060382e011140106410540361301c8020038040804c01d80b1200f039800c01d1200500000203542d406510001c0c022800040c0801e845c2e42c175071601104a5640302c1b46096005000c3c9800140300410005c00d622403034510141148800e080d00e802a0880d980310f4a40f080c600743e0005030451f041400b0150b0b03181d10203201c00c245903c44901c0c030007600584414248400600300280135200306401e2030600d02d030180c10030300502e41d6a8400208a5401202c1000006078000c4c2400184d050183d065600040c58038020b200c18600b4003d017001d2038040c0c040402c200306000801900f03101d01c1900f40000b45030800d0f102c408915142e84101c04c59803203440b08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 72982978 1250 72981728 72981787
    0x10b0711010503060f090405070815010807150f051b0303010b0a020624010807030e01060b0403060f05090c21150f090610030602070501020d0507030e0c030c0d081c02 73
    0x4003409601c10307000c40c2c0c03055200410503921045c074103090000d0b4610040c0211038034402c02030081901c6204200d49880c0d840203102c045c41ea90305160016003007002590001803c08040803007014142c1e001040229500310500d480ea865021000b0b02d819590841d07002a0013a0100000201d01c5018010003421440481d80803610309403208013503810890303101003590f025049514a00c90980d8483e012854100d44a03240101e5111508000142190f44990000d003148200040800c104415401612070044510310100a00e2500601080c2c603030303a107000524171400e09240040700c10b12003010a401548a003c003110a1804241022074030380300b0543d241882d264040c40003d030b840ca00003032103030b10507040c211107021810710350f0752240040c1d002120b003210507540904c24100e8449040c850248540701555021030003000e0304207001d040c54180b040d8039009400c01003070f1010704d4880c556038040f00d0b5030180c6481e40d12828240040c0500405500c0800f40500000c6d004044010071803c4501e8070310200034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 72984228 1250 72982978 72983003
    0x5070503011104080c01050c0a0c120312020304032304090501081005010f0305100908040510091a0c07031502040803030a02090a0605030610120e030c01050114101b020a0e010b07 78
    0x42d0349200340034501c0b400d03209500c01341103c1c1c629446200a00310b003042e4141100e008111903070b101d0002e4a201d0b00070004001e0f60300c1211b822b05621101d481214000c1440441c6181480e850050466484903000107032551201002190391100e20200c4000f000131000801c119615607a91544506c00c03805002811420000085031324860403400f2003c90754440000c011802400d010703100548a1500c0640307a1036024880020306071600e600320845c40a066480d9001d035400d00403024490092003020076607000e0b0a12210950100000e60801943d0f04403d2612140c400302c00800064881c1d0b41003121540808818041208074680152110401c1101e030b2034000c94480d03204030f81a000c1165850ba1010001d0003101000c0d0041c10340900302d2050000125500300c10030560761455000600c0900075a6540f80100101000c004110f510a2011600c0000307075140303114010700d411035444107100d80c4100c800482e01159120001e078802000009480c21103580c0d2800425904c0d0000e131002d5440f00c1d078009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 72985478 1250 72984228 72984251
    0xe0604060801021603080a060905040303050609090105070f270810110306010c020108130204050115021c090e07030b030a060b0301150303090909020d05162603040b0f090a030507050301 81
    0x240c070070340600004c030b09000c60320640f405c44040034083c0c003e903e00c941d01e210228510b03405018184c403a50113900c010545043c02010b100301c000300200011078591401c0207104130039501020b1500c50060340d00d403643c420220040055894010181c901d48010130074100000c0c03141010580040700008210100107002035802c6060040c482110000d0019640301495001580584061a0023418040004803560703910303404034003203d4017030b005458641c090b2030301920495810400b180e41300b1a04580000d5110030b00d00041c040003841d008070604080c4500c0095074180c481d9000d40403000700141120304d4075010781013200c010003442e02c10074000e500303040c086d01084084400f1003049035410b590301e00744246840020300080910344000ca0344100c0000c029008184100100301e0304021f00f04103c0009407030600d001d04045000310a11240074210050800e02d1b99000c8240c8040380c003940340c410344d00ca0301d09010000f80c0c456011040e0307110f5640703000813052220010f0100107031802030b0000c104541030341 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 72986728 1250 72985478 72985481
    0x50a06020319050f1921020c070501030e150103030807110f0607110c060d020315090c030a091103030d0603030f032a020c09090102090102100507170903040b040e0604060801 76
    0xa0b20289a140190a002076850f40f0800c01469210400c007075035420248106503011410007224901ca001444100074501c00d00c03440c01107103030200101c0208500e4080d812510b15110b182c40c1c45647d05140c0c0e118104c481c035010070f000d00d115904405d5080c0d8040d40c1c59150182c06840c3c00c0e01c81c0c3c000940030b2171040c0c600100c005000718180316010014255030f610280201e500d00b611074842c0b80c09000750a08403990f511102e0141000142c41e400c00750301ca1806203d0112030341c0041c1001d5100d040c044040c4000c0c281c0c1a0110f80e0490160100420800c020341012549007003150303100d81c4c041c4400200200e095000ba4014000d6911170b56400c510043c0110b0101d09075036403800119a4200c01c0c0459408000464102081541e0940141e50105901000041240c201219007400e00e9400041c03180c3c166038140480001212940c13410007590401540080c0381d4100b1186180508400401203050b82c1d074200181d40044c903490008981d030301d44840162010040c00d455160055042079008507404006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 72987978 1250 72986728 72986737
    0x4020903061303050f040806040501181218050d08070204050a0b01091e08070b1905070f02040506030a05030309030d0510080d050f040f032103050c0a0c05010b060301060801050a060203 81
    0x50041005484002c1034010000342e442e401c03001e0203400c01c1070064082804003d04010035005001d0441803400c0d040c000d0944070a140c0174003980038072600003000604a092020210401490410890030548442d000c4800e0750307410a42d0f1054694408008021448005002d040d10940b0107101a0310343c103d007941650404502c136400719201c20760078004a4601d99090000b41c4000740041110b5548079070302410066160400000c1110006900145d80041003203058001b0280ca0194500344294854000791111404007c0c8265122408288541d8041000c010401d4112040c0caa49080c001102d03a520b51200d0300c9041d0040c105800101d4400c10354000d00f0458a2001c0508007542c01130004071a15884569000202d07203003401b020405c2e501c165191000b41d4802d45d8170b00190014510544030f8100c41041c14400c05040ca0100254450407030160b494404036420410204525480c140e400f40c024034104e250802808800060100e6005c00401d0403190203450062419446442c200e07281e218 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 72989228 1250 72987978 72987997
    0x1031a0603030912011b020303090f030c0c01050d140f01290f0724021c09020109090203220c0e0106020a030503130c121110030b0108041502040e0403030507030b0402 73
    0x30a01049545040c10002c4c1502416004000250207003907001c0c80d01103005401032540180e0001c400c00c44208401c01c1032462643d0300e48002d605207180b00b036586903500700307082c1081c0c104000414400425a265008900c0500d080410b0954030300c0c0510386100340500034481c80007a1070b20b1000c40401441040d0241c3c1c600c0042d41401071a04040703040c0c009069022880c11103200402c0c050201c60030780c100c2202003460a41c1680560743c6c000c400f0000728900c20018000d41c01c2b0f860604e01d8801030b84c002200d041200c566040151300d9603250701000320922510b2502242105076510007104004801e50620140d4407494441360075070341c890b40103c2e40c1d039655182c0100441d8041001c20490640c500520000368807030880070480c50780f1007090303998025401c00300311621444250086210f28100300c241043c9402d918040180e510804002000030714007030000b42400c1c03c0f80c000c404402c82641c0484000c2c0002500c4041c56041c0343c50001c0060400300e40000010341340c000d86000318039090003101c0d00c024 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 72990478 1250 72989228 72989233
    0x2011202041d04021c1101030b010807080417090d0c03050105010801110d020906092206050319060b040207121101060b18100309050d0c020f03030f0406110709090b01031a0603 77
    0x500c0b81d00071480c0e03002410a90740001182511009070828104401441c0c0c403690203201107250800c0058107440d00844110b05200c5014200283c290344459590740c400d4210320102c028940502c0745604511422030706a8000d03021984103424041450580e4017244c1c42140208010313a03070740680740d080b00c1401700261080130f801c11080d00c0c041c107141c000d402d01b10001000c00303140c03600040c0000c108800030101081c0d114000c0a49401d003090510400005250036805419050456441000c203111400e80c014589681c0301c20384403090301c503035060b03d821f184e02c040e0f03c980841c501c00c2c0c00342a0030700b03407a4030405540c240300c00450344240e00410b8502c1965096000302805840400300600221101c925401b0140d41d0703c40080411020006c41002900c2912100034250207030041c0302a0140711918070740070f9403082140034800060f250456007241c0c420b01d4806035407502c02c0161410b240d107592125044034140f20804050211040c01241241c6c480d40500e24600741d25500e50100803011106158187c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 72991728 1250 72990478 72990509
    0xd0809060c070f030905030102040f03061a06090607170a0c05101b03020304051015050f010302180f01020708010c030c0306080a0308070815060d200309060103020f06040b160201120204 81
    0x241e80c4490000f40c4600c613042c035004450310b030740100c2d00b241c1181d03004006204055a080043c0300c2c1500c01c2410f00400e212000060130710748008524a846602c00c0d040c0503001c00500882841010380017040c50141203111190381d20340f1050010001c0d0014503003601d081c0903020b40480325486a1003095400c4409150405142002020940003034100078000e50311409101007070300009216200d10381814003c0e04000c8142030500e41030058035100c50f460345045c103204010002d043c01160b100901000411030350002c0c3c0a015100403401c11241d580f0040e142e6090914581c080d64058001644005403542d04012960b40c480001d641c07564000c0c2c001d400b01c1c5c1414041583d0354810512264000100000d0140011042e408141a5803001220502d5150313a46401050310154050700c0100701d010807403c03815030030080c100c00d84851043c84003d106261070303401d40c24139032180c500b501e0080c11507052060700c031200074086201c10240d886080340081c001c91149070380391300d2034403d982c00d48944580c1320036007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 72992978 1250 72991728 72991733
    0x11b02070b1c09061a1905060d0b1005030402010327060c02070f0308030906060405010b0d0c020c10170106031a0910051009180504030503070f0c02030f0d0809060c07 73
    0x740c0c48402c900740707072141001c40c12107004898000c0c600d400d44160f0001650740701811051091000c81d000c4d00340700f00c215000d50013282504403084d0044c0c94048800c00d0342c801483d00e407000103045140c051038022045270710a101c4242c02c10080d611a5000707880a0200f85444a0003a101c4282e1400070840001c100002d080400c95543c4401c1503245640100c0304101c1d1920700c1c0301244d8015500440301620000208000660107004a90300075100b65010702155051500480050040520420200e40e554501c000c04920801c003240329160301914003000e080030b80c0c2c1c004290790701483d00c1c1d2640b0510710000091030f610921030100b131005c1c40c095102050f0100002c005600c100545054030700003c5920124040da107030a00c06c26031071040d45901a03034516020389240c815004c2034500400703510b00010000426040300440703522400b145428407456102c14000d59506284401c00f079014443d00058004040c000901c10004c07404544500f80a0350710180902d544480032910001c08041c10b2011400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 72994228 1250 72992978 72992999
    0x1c0b250305040b0a0c09030c0b0a0207080c0a18060f0e0103050606030d0f0c020303040b040b030f01090606140f1b0303150603090c0f0d150504031b030e06030613110309011b0207 78
    0x21360701d442d14000c80265525148e8804411160300074060750240040c400081c07907010000d0500828400e030140c2004a03000d80000c4035900c491240110b51814802c3d040d0701c45250b076000750064401c080c1d0b20084a500c480c2c001041b1a02400215610b110351b80210b0000d10780000d01003424079495a0b260030340c18802030221a54042c04104980611041c0408144190000081d0015000c02103125407685416001e1180e04101a84a03084461410f4000c1c006c40343d104c856900904000403c079950740c1c0c905898021180308680d040416005041000c00c4070201c044021402180c9054a01c464440d46200700180391006130703015111640314400000300e0303043c4803444d0324044500404040c0c0131407160b1102c0c0122a8002600450b141d0307a4000c000806400840c13414a0342001c080110b0200500d50b40904650300b40046a81300c4c590200000b07100c0c1c0d696600946070490510410b02c109803401001108680042d10503600a508220400321070403400411404260b040d54020700744246464003218 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 72995478 1250 72994228 72994241
    0x30f15040608061312050a022e0e0706090b0c150403031503051c080103150b030102090a08030315060901050307110319050a02010606030506010203091c0b250305040b0a 74
    0x25041622207a00080b00a014401148a4802503180d001000d00600d4040c20301040840000180001071000c8102294001981ca0807840c0c410b01c03002c10184460340c5011007080c174000452540b0300381500e02e2214040480e5400440315076889108490b5120911201940200903c001c7e00e0792040742c0080d03030140150035481d04a406030030002602300220941c1c50000105c0c2c0c00aa5041e80112454504a5101d01d5500c4500042d403a14840b55419070b507a034801200788145c810f501c192074031110f5a01e60390a604540400c0c030300400f003100d020740d01d0300280c0d00c0ea041118204409201c540c3c4840141c10307c0821644009416900c0d640345176035904080c3c4040c1900222034000748010b00c00610303204c4000012140003401a12001c3d280c0f10701004c002d00391416500302c3d038100b509000c10f11909036000010341c2d950500407980958210201800700c2d00ba4035404002400f40d200501c07e2010000310444030344400c002080c0c051100c0803544009034103661042e42d0040082c400d50b80041d080201da544800b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 72996728 1250 72995478 72995521
    0xe070b03070c06090c031b0e0609070c03030903110d0210050c07030206060d0f060c030b03010c090302100f1403010b090102150402010206010e0606070204050103030509130b0a0302010f0212030c041703030f 90
    0xd005c0c0b60744030f4542a2003446044036840e0f040b81640c0b002d1214400f440a201e80c0101e08491442d442d2905250090204090900040903d92030302c060000701406001d0044607901d81c842210306002d0b002c41c00035030b104241034507001854900008100065450760460b400b0a0305500100b095880c4d503018009001c0c010402641c50100c11000c1d100007803e0340c05840c108042d5640c0116036400c4090401d400c503000009900d0900640b000108010b031170740e018141e87c03d0307450700384601c0c42c80c00c420040e50820321500d00c442c0101c000100203c1c0381603200c1d0140001d03000a03401c890260950940039581c444c01541c1c0030340580d1180004000080d03545030501d9000700043c0c1500c3c10602d00e58045025a0f1081e0411404100041044111400c00d868003401000900005000301c00050020801d0501c8900001c0c2c1080800d8001919550003048504002d48110048940da45031980c003151080c0c029000b001042d41c401c1c00403650300760700041507d000340070342d031403516040d26001281e0040000d02c101c070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 72997978 1250 72996728 72996743
    0x2041e051f020307141c0c020d0206160605010314250b0f09030d0201060311040c0e040203060102010213030b0402011205010b270301020409020d05010e01080d0e0f090702010e070b03070c0609 84
    0x131800042034419546852017540c0c00820506aa51007a502289420181030042000b00c4480c8005030f5184407401da82a0f40584130b85e581d036012444600700070410348001030640707414a40008104913010742316504c0b4080c85070903100b4a40104564401d809540711514010740181030052109035981c6000300004120070301800e00d4401007102080c200f4030038014100150359104030800a00c0001c00124901c0f05045404000350004000d018160312030b0042d2a6000d03941c08000960682d000358112090140300c04a480300c01030b620315080d142e81c14102d40c03c034001003640b00c10b841510403130b0051505036800044150b003480c6101464500b030390f200c00781d0310a003100c0c070710b5031300900b0f4400f880200003510613030320050780d00d003401c0f80ca1200355841a409a0703400c904803001085280d101059504e01c1030f0551902c1031600d90303031000091544124030610380d4013560803002e000682c1d405520003601d1070a12020384100640d10b0b411003041d800f003110400049940c1070b0040740002c1c0c444c0d0142d078a20313105500d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 72999228 1250 72997978 72997987
    0x9060305070c06050f090106060e03070b0702040605031f110301061d010c060c0f0e0a030201020303070c0501020705030f0c010c03090221011103040809090c090607120c0209090102041e051f0203 85
    0xa0700000d03203401741c0c1c54140c940030950520004a03001e014410160803035041c80b08060b0b0032200426601e00951142c00305000012038250110b50326070700402d0051030020f00b01d820b008203a003a000140b41c00103162500080c03600d40340d40c51150f80301c010381c0e040340e1603a140c5480702a146030900c25005040e407603090400c264240003400080041c0303d0b6409241c0642c0c4c42d010b81c07829144008c2c001f82e1a000c203e41c800c0c0900d03501040140e0b4000212980040780c1c3c40c044459802500d0007501a000d00c100040050101040901d040000000980700502544009005181101c03130203404036548a04042d40040b500d400c0081240604603810803601e0490000050f90240080d01003a1600140da00b1581c000340050070050030715119500e541c10071b00da0489249411040d400051203489541d00041418100c80310100032240500c0c0407014143d0083e01a06140c944005000d000b580140503040c0c1591400c5190090505c03200e01a4059610142c05205000640c220700560110780c040c416003140300820 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 73000478 1250 72999228 72999233
    0x4020121050709060212181908030a03020a03050105060307021b030f01090c0305060906090a170409050411041a1e03010e07060203070308060409020105071b051c02090708040309060305070c 83
    0x3160358402c08a69a076a0301250600c6002410180c45100030400c12500303100642d81c1c0c0c08608019140c1c1c080417610f2082d6a414100304003000c101d50742c000d00c0d01e0b00020130080e864a4144c0c00811005201e50b13010072140c0c2e00e07401001840e000580c1c0384001680450140c590b0301812103142d400c808001001c07542034103e1460200d094512280c411114212911030800800500304101d58005103902c000d00403515000e82190ba65001564002c0c0a405015119481407a40c41003128041d1407001801c1c016460b0078200803a09a0904007064004c610740b082924600f85880c0c55440e14006c001d2010b40031079814421590003108148000750315542e2008115120035040202c40001c05117a0060b64075080309040181c403042009014030b00607802c0500c41c10050f039000c000c07240050f43c014010101181c041c004100b00300c2c925045030380c10010358910894000100f070780d400c1c050f074803c40b607030406a56090400c403500c0b0b1055800402007144c0343c40c11f1203054001c1d000f050f842151440c00c04402200303078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 73001728 1250 73000478 73000481
    0x101202040921030207060e01020c0a0b13061a0310020309070324061203020d0816030f0b300a020f13020702030604080c011d301305030601060c020904020121 69
    0x442c1c1c00c0000c01d500050f00420001240100c84481003030400840c20450304468294460020400c010081000d4900040c481c8801e05090342c0c4294104070104a0406140003e912a000c0c2c1a4424487c0c894003071811a03004160084030b1090303400030b014000141c9195215449000e4200040324040c40880c2010401d01692040c00024022500e110f07521803c0ca040103420509008042c000300103000e000c1000c110301800140c4a20103480c540024080402d401080040608560165108101484070b0940c8c1211510b2102201e11111006490100f12201156500c014810080d0040c1d174000c0381d084645030000c4205684440780c0e0002d032411155030300281c00c1910864048800e140c01152140d0303100b000f403140c0040c0303c2d0700e07500c5141d08005020600c2e07500c0c5091f490f01e4034981c64800c414901126803550781010340e60f280100f243c41d0500100c1c554044001802000e001c1c0c07203000c1c000203010788244010303410181c000e0300c0002d69440d01c1e001100e1602c0003260321302410048019036420044203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 73002978 1250 73001728 73001783
    0x40e040303022d0a0c03051e040f062a020d0501180b090a02013905011a01050a14030a090206030906010302040b0402070b15150c01141012020409 64
    0xc0d0790016a03408246040c14650751052001c2211209403004422100c4100c40403200c25070041d0802e05c071007255a00c1e08551910070356250040c103c1c140c0d44220300140c094000b600a40c0d1301d0030260311125403904070450761802c01180102d11081c0f445103c1d10482c1440f40c0004400340090001d010340031550711a41d0940d841200700000d11a0300b08540401d2100030080700e608100c003e030143c00305698a400007400c000452882c0007941045000c03080311a05240e058a0080070f81e4007141c80e04180d1030402c10b0082203a410490720740c5082c1200c40c44603622400440f0503100b404e4880028080036102406801e420091000701e17115541d00080c00580c1c0c404025500c00c130113400040903690b0642c4140800c1d2201100d4180c080e0380140048000070b4400c0c0070640c0c0c4820602030540c520310360700d00041c60300106003c0300825005c0008003455040010741040b000c280440381540c1145d20382031821207482c4030300d00c00c1169a03903107100c1c4400145002e0308405407141c010044a0b070714492204040d4040d004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 73004228 1250 73002978 73002983
    0xa08070c08070e061906020a11060c0a0b04050f0c06040314070b071104140c070206070c0e040c03050d080f07120906020c03070516050303040e130507030c0608061002030a030b06040e04 81
    0x204040028074a017105840021107441504484a14035110003c0c1d03071401c491000800d07190400e01030144c192100020b07207080b00d8520045a0703503002c0a0500080446040d0760030b6610b07020f41c01c103030642c4c400e00140b0a080d140c0f01400321403820b4950f0300c6161440700800c1c1c2035029401000400900c0c0c0520402908a0174000d1614403ca510703240204012558000140c510420b203e00c200020380d5500c0d003d840c04550103031390700c42d911039491401c01440d4a50b0b400610218816400303200078441c400101c5415039203c4c3c401c40383c20400406043e22180d0080321001800205071001540d0640b1078152144808180400807841146c59650703a802c1e6003091a1600d2a0707400443c44030300b0300104000300d0b015140041c0903140742d6401c18021a84a1013207000d0b000e42c1d0701460b00840c1c0388883d10607209524642000c2a52602c2d9200d00e031041011425200b481e0000380210080307403881c98440f09089400001d81c008520304201c0c42010350280050b40e11aa034040b00920001039400039000c0325502c16407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 73005478 1250 73004228 73004249
    0x1308070b0c09100801300501020d091a060d110d020907050c0c0d17071a0103050d0e090708040b1005090a06060212070305180d060c09080c0103020703020a08070c0807 73
    0x9801d5051102c042a000d0a003410010b0704c0740104a214208040c00d41c00411945c0551460640082c400207001903060008110b5031000030080c01c800d07107a5002500c22445002b403140754809401c0f1142c020281510f98542c06003102c440c0c400011061040c11100440141259614166680000d0b840113022900c00003c03031400102c1d1004210f050204040c0c504003140c05041c400b034191103000070300c0b1940049400c80da40005102007030000040d00d500603640480090143c0303603141d1400ea522000f0650140010800c1c201c8ad83d4028605400307258817802003642d4160195035203898600040001601040e4140406800400e0a8035843c2e103440c4521001c000c0441d010745420802071403c0c4e8210740c18510f01c1c400744030100000b64400c04503142e10b851402c65000003c81880084c02c80c0b51071000003004e451414103c002141d41080000c0304a40400044d245045403141c01035099100c1c2c40c03401001a04040070301e00009280300d0103003540754010100814819261004541b41801c40e070003c40145 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 73006728 1250 73005478 73005487
    0x50606030606010906090504020c030f1606060506040e2802070308010f06020303010803040e090c100c031202040506040306050a0b030312040507050301060b030604052e0e0a02040b031308070b0c 85
    0x40c1000c00c50103030803490a280400f181c0c0d1904100074289541030203058800d0b80c00094800030321104100352450105501f40881e554105690004410145030804451042c01d0010000c0c092070400240e8003201d0750002e54040c1030380c80320b140c070000b45032010410020084003992404041c1d1688080c05c1c07514482c1c0c1701c1042079414544c0c102140c00940d03022408550040005000d80140401910708442d1520303540d403407641350b50310304909102e180403040c0d0300310742078800f01600c403a488100270201c18065150086200a5001e006040c1d1145000d09900104100810070004074a580aa80c0c04901c207a00014184161b03400281580d104445070000350311400140014800284910401010120000c0162a00e41507141200340401001207108981da01c0010b07a100340146844000d90340701011030311203684803500108500e44907001c0c42c4c01043c80000040c0c5150f0f00c920032078090b0703044078000340e01b075580d00154005528a01d801c2118100d406118040010319140c50582c003070350303111151546070f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 73007978 1250 73006728 73006741
    0xa06060f05150301031205030711030a03091a25030f050f010614092d0409080307090909050703080304030c0507090203160e011d0406350d05030106180306090506 71
    0x110006042c000190010001080021180750145042a507075081080d281e50f182c000070317144060564082800f5000002d8103041c000d41c50742c4212505d07481007a031003420b0103040b24484950b0001b151006198000e815000c2074000b801600700c10844014070300828032151150400080ea0400d8816500c1012443c0041c4825034010f01c00b4108504000b0103141045c01c1040040c04600950a04014846100110074014007604040c2c00c1d042401600c00e0200c40c0c103600d44001ea03980112248400a03072034210210301a85a405803d201c10380080c0188622801e40c2c49000196101500881c1801440c60400000a0341884048000c2c0107160005840f85844079403c2e4490030041048010080c05850300c2c0380680e017080c85054844c40c18a0340f5410361100c800840c2c0284403541003121040070b8200b140d03124024100c0603035410510341c6120503980d82c060000aa54189000d0b1100106005100601c02c540c422031103403511148440e0b50508059603a11520211b8115200646c4e85030442400c220b0f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 73009228 1250 73007978 73007989
    0xe090c04021b0708100c0215060d0305040504090c150507051c0917030a030b060c030a0305071202220509091c05041205030a0908160b1308160e010b0a080403030b01020a06060f05 78
    0x1035421b50010f0030a210308000c40b0811280010500c902c12107110803944103051041d07096502030700000e0400c05c070107151404c1030445e285607445059015002d00048240c0a480b800a941c4495808002444040750074600b40100006801d03280013040520744001500110460503400c900c044c40024540c1c3e9050503d008064805980040b405000e0401004101000000c04c885400541d89000070309902c070300008650624000340400b48060000c00c01d420014001540d0122801d00c080c04040d44980d140103100c0c1038a003c449c904569080100b0421a0540c28040500805001d2412900e0581c07103c01903032174600b0701d50003035881c0d600114801c0c2c1e800ba00720207400c1c06040d00c00c00502083c0071342c094440408040b4040c40c50b43e2100400d03d083c280030a000054054800141510000030b15601103180d140070714030a0312580c0308144000181071565508039002004269940100790f500d81c0c50660217400d000e100c0341c0c1144036056901c40401c42e544911405402075036010b500d003900d004100700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 73010478 1250 73009228 73009241
    0x100905060a03020f240415080105180105010c0c12060b13110901050d020f040b0307021509060403080402011e02010f0617030304110607060606020a06060e090c04021b070810 76
    0x900030780203203109001594443c103100c2c50403c41202c07000c0042044c40c04d40c40c5021054030800101c01400300d070105080301014402c50b24441075507501809030b80c1e50300401900502500004291501e6040140001d5100311000099030f80111070140085070354032408014402400c006881080e550080d140141c54200071170340c0b07980743c404810700402d0030200b81d0032202d00c10002360b039043c00000218095200c03c1501034030f07480c10502041ca0784a039503480c28040b46500441e800030041c0500d658281c522441d007a040e82c05000b5000080c106d1366a26681603490200241040e411300c01001c2d28030418940003085046090041ea0000c26007603280080c1106603040364114140b45000c001005030802000400e882c4e001d038110180e07400c5040c09002040b8540304151024007990305000000ca6210b400003440c0769894420f1000b086000d594000b00c0c0c102c03039030039074002506800c011080c0d045480c00b5000381c0020031050408965220043c10200d1911120ba0301891880e040190036150750f001c5485001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 73011728 1250 73010478 73010491
    0x7030b100f120c06050d061a091507050d0c0204020c0609010b09070215161103031608160e040b03010b0d030e0a0911040303050a021c030219020c030a061a0603100905 73
    0x400070400d40d6039483c40c100d40900481c02008070118048004091a401010003080714891548030385141b8040c110303069000c1d5074002d01501258010f481008803040071240044e0f00b140190544103090b020484032000201d4050381c0c801d4080c0010b04e40c07001d040c4020344c09001480c00001c1e01482003c180484900000d04200c15900b00485d0b0a903c241143d005a07030040d080145020740c10646070007540c6024905491007a40c1c40040301304411454581d40c1c040c160900c6450300c034515502d140307060200320b40c510700d02ea00080280150729024209034200d00700c0080000d0002c205d40070090041030300100c070b818003540041d5240021281c04e080c5052031387c000e8610a8410301235201c6d032101900c1c13144100c2c4002002c20070001450b40c0254400d0201e1081c5105079520542d041220200040181d003000d907034001c1d01200480703021400344c0006101108804058080c040c01c40ca140c65a070002c06890300c41c0d202c0360301901001546d5583c0e1b10015803081111001001e1030300c1c24207080c44111074009060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 73012978 1250 73011728 73011749
    0x10909030e0609060901030e0a0501051801111903050601090306050a0605041404050a0f060608030f19021501050d020d05012a0206040507091e09060f0c03060b1b07030b100f 76
    0x80c5a0b4035144c007204c010b14420700f8085400207240e20240d00d800305111020f07101c0d510f04418000030b00b1004401c05581d81004000340054001e01202444510a24840780d040d200740720a0ba40345280640c102c0b550280050512013851680d0740c075000d09445085801c0c0200503500c40050000d85000e01c1680140c055071002d030700c10f80c038290392150b0b40d90040640240120010081c4a020050170f900075038040c10084058a0300c6400c1c6200d013050384d4002c08017401d050a9220215008075100240c071801880c400302d0411426407803e810b205901301e032603000f40d0300f000980c0d5010012900c02d00640000340c0c0d620301c000407256040c03a080e900078080702004c070045412910601c000710305e00141c0041599803141c4001101501c4600f90801c5076010841c2d0030125040078120300610441c0c2c0e200111411103a542404140e602240c214203d4a007402051402c0d181403045202108845600e040c480030098121002141c40c0c1d00c9240f00748004a540c4014070034181e2040c415403c0320801c50700140f418004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 73014228 1250 73012978 73012987
    0x3160513060305030d0e120403062013090e030c150103140601030506070e040204030f0b0103050715020615030120190309020d0b07140705011a010e01051603030b040203010909030e06 80
    0x1940c0f91244105d03562400500c1c2c40e06001c8078038170401d01c00b41c2d00c6403031410001d0340d88035030746d00d0043c000c1d110550604003002484003500e407110900c8011500442c010312841c1841505141d0f41d1801407039840c0070103015100911425100e00802c1022030682c06510002c00c01541c91440e001c00ea01e02a170900d003050744c210038010400560000303881d50f000480c50038103015683c15000490003e0040d5070028210b042c05502c0c250500402c058242d042c2c070b0180c07003968034542e202c040110a008405c1c070342c200168003050000303803400c5858083c0c4c5e1204800034004901c9010706081c0c450800d00d00105400c03e0350300080c01d80300f00e003412450341e243c80300c250406100b51403030b0303400146c481c41480e0720190650507254001084144030382451080c9500c050070b2681c8800c11410114002c0c40800c0d003080c0e0380080000304c003c40d503002e200d4000141d10705035502450320110104050324280060030407428152501d415018554550001d14042c020041c2c000404a00e581001880c49150003100c6000d87c00400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 73015478 1250 73014228 73014233
    0x1b0303090e220b040204140112140d0e060d24090b0301110d0b040b04050a020c060f060901030f03020c0306240405011a070c120c0f0614030f060f031605130603 70
    0x8840c1280e10341140750301c210384d51280003140107030a40c20380400145403140300100351162000d240c1030246015442d003411082c180d40c40140c3e03c10a0003041804105010700448142c40c1c80c0d0010b250300301c0000030104842e0801c21405070600440c3d42c50107000d46500c1f50511138010184120318410004600900c46002240280e4600d88600703000c2d001c1341c40d11800303920503d071120307000311030000c070060000c018a28144103070400170342080102804502a59011400442c60412803501400000740400c0071a40b85598002c0b900101841c1101507004944450701d20b076400f408120b01c500c1154031400905004501407483e078a60b40d040444c07259117480018020080d40d4505180d0561842e0501642c440460500500110442d80a06400103680525000b00941100d11104640c000300d40b61200507200d20060324480f440882191401c6407d20004200491011516810200203003240594014400110303040600e0010001c402202039002048142800d8440030700300c18104d00100030450030365 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 73016728 1250 73015478 73015531
    0x10606080105040f09020d03080a0b06071101050c0f01050403020a0b09030309100e0a060204031b05060a08060402070314160c0609031509170c0f1209030a0f1b0303090e 74
    0x41c040c0030300450762650404000c20760340d4031050703400d9002040d0000f03801f8149001450b040d8101c505001d11410300c880140c032414000f00755a04598000400c02c00c52602900444a94010214808091040c0c000b001c0c004002807007154000da019501400015086007460340d103100015006038800c0c2d004000304542e00001140c40e041c00760148030082581554081d103149409404540a050342c0c1c070000d000010014800074855070703c030700348d4501180680d5400800c40d450042d6003048c030114001c100000e500303103055402003010501c60f0800f404d09150003244844241c100d03002203000c0391100300700c44084c4401c00321401c005150503e003888580e811640c40e200c1e07007040042c8445210340c440c00b9080410241e0000c990900000c900c80580724488262295511242d107051100076001d5151103a00300d591020844078056006402802d4129513662401c880c074010740c1c01078414240c3c55400c00c24020348e05000000560095651060071400c0400301b44140c0c40141002d071003641000ba4001102c1b40c071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 73017978 1250 73016728 73016731
    0x30303150e060907090f06030207140105010501080c0c01060306050c030a0f0c140d060b0a0c121805190801051003020405160207061b0611030901051003230c060c061801060608 77
    0x2030f01c2c60340c1030f0340303c0d5a0180c0b2078049a4004d0442c0721040500410015859405403016030300984d220458800d5800c6068201c4401380151800036040c100061040b0040400910038055250000100356640e42c03565402c551080e5180d2017140000003d00481c50083d0292800050050404200c0d600000b40023a06007100040c50303c82d60a0081105016500207500c070340c0007410703070104843d52940000e5008101d4460144103d07941c800043c2a00f640c3c5200d10598042a50b00c4140301d0440d900780400c00201402100d82898191030300c010120b014102030003424015403110303598100460551042005440000300641071a44d400d0190b6034086500040c000112501418a02414140c141c0780104240c0700307031005050507041400d0baa18000700e01000f54407a05c0754038001c20954455004074845a04135220103022050312207003040c00640034901ea401c80d10424011500007030504008113816070003003032501c9183d03000f450401c01310814505964405103441002080304134145100940400c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 73019228 1250 73017978 73017991
    0x40c0501182405070b13020a060513090b031603031206050105090f06070f0b010b0403030807080402010c150f06141005030f0a0506010e030102030a0507030b03010b0607021005040f0305010501030303150e 89
    0x15507180414402c0c3c003a200303c9510b0350300004090210b240c10205218102171442080340038042251001800b503114000f554501040603030b1a000f00e616002c0001302500c14400045d9141c00f0300b10036000503281c81c43c220030095101f9103403448601d81c5000f40d5001c544c1140d00c414103000d41082007940725601c10301d541940f10011a030107500c95a903410500f200404540d401004040040c0022801000000207081107910940d03c1c44019038a40e40125441c0c0c600341e41c02400b04140303245080001e08415808072104031000030000300c4000c4101c820090342e0103a80300700c2c4074044020350540b640c18420b0b403c1082000ea030030010300e10304294030f4085200a00411911031035594802280781c50b803040307606500842008000f503440703041844e4044028078003035910201007483c103140005942010b000c3c841c40000f0041030300307003030040c4c0341c0a00c5a1002d070381c62403804000d810000880e44842c0308001501960141c0700001c7c0960641c50050201c3c2d202024002803141e8102d0b0400c0300c0650990160f61181c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 73020478 1250 73019228 73019279
    0x20a020a1b0815040501051305033a0605041401030c0b07080403061a0102070f1a0915160303050a05010b0405010e13020a0c050c060f040509040309030605040c050118 73
    0x8540c440c9401c070380241c1e004125507001d609140c954010101440c18015030140c00200038580700d905203440142ea0001005095030010b1001158a0b080170082031110001080c0c014400da0140d04003896140c03c9903000440561b45010900003828244543c254005194194002c01c5d41592241ca071b04441c5407085003000344000449004118908050f20002e640c801804e209500040c0d071060101100301a1081c01840381c03110014016840304804021142400c88006140c10540c9590307056900034228242c112003001c4c104040454034100070314207400007120b01d5800d401e1510300102500d50180001c0e02e01d50510b401409820703220400c940441c8c0702420000141c0da040c202049000b080003011401003803001c0f80d074055894100c0c15001c0f03040e1161080d00c0c40c82404104129250040500c12030603040180014800f6003800092203401c80d00030b08220020941d642c2d581c0050740c03400c50707084846c2135402404104d40e50300001d00b4115441d4800c04031940d5403c210703a2a4402070746c00c44804410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 73021584 1106 73020478 73020503
    0x203070c120b0907060e01050c0c0307030305071407080705061c09110f06070b010e090a060204060f0815010e04020307030b06040308090f01090f060804150c020619020a020a 76
    0x1a0210381b41c20105100500044403036411841400c501403050070013001ca0b940d010441900191301c00d035510783d0780e101c8074505003600616410a52046602002c401d109515000c00e1a106655080d01c2c442d4036001c00e40940c0c514021810307103080da400d20300301c810814003403041c05c00030f5120429101c418825007a481030102074400d0300300c064031841c242c200510041130700d00300148d0440d03010012920394003041d031995022a480384c1d200d20042504031110131105900260350643c0040000308410400d0788080c0081d2894403078864881c4a5a0700000013510103000e50700000c189080581926107c58807460030440e240d104150f500c1c403951515945280e84d6204e000c0c400181c0d900384091440300d52410000381c0300400f02400465003181c624030110079440c43c5200751480b0a00e50344c001c206034101080d0301c06407805045021040c1d00d004020000030181c0029501d004075074089600c1500 = true := by decide +kernel

theorem cover : BRFrame.Cov 72841728 73021584 := by
  have h0 := BRFrame.cov_init 72841728
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72841728 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 72841728 ≤ n) (h2 : n < 73021584) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
