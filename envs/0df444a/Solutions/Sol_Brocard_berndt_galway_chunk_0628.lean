-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0628
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:49:04.008156+00:00
-- url     : https://prove2.me/submissions/07b641a9-658d-4683-a671-3eb4d83b8925

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 112769784 ≤ n < 112949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 112771034 1250 112769784 112769843
    0x2070b040e010b0c0703020a0303030b042304030806010201020d1112090304080a030c111804170c0a030302090d02060c15091902090601030f0f0b0301050a02070503031b09030109 78
    0x150204100500030251580481411140016800b6948050503a030150618103640e20082d00450401c00c08000c1540541100c12200010354040128881031232034071010f40c0e8900301003070768500d03d8004070300881e02c503070f0391681e0151042c000036150000e4140984100c500a40c00c080380100041451a89400c4031030289400410000c02103003407508100c01681c407081d05c002d0040520000320044010040210114005c5403002000503100b05032642d004004000101c80840c0c0b0070502d074108100c80103c18044d10070070018071004040f81740b15650282c00a51003000043c0c3d01c449009080001070b5200c4c00100301c01c2c4240b0380546152074200c20f001c403401601904420454111313581d904096030701682c148480907011034000005407615801600105008c08052651a0400a00d502252120b4101c0070007180198003c000643d1201808422805082c00007403c580081000c6810850240c0c40c6030950100e40e0f900d0b501d40010200001e0840301d0108007110012200c00303000700d440368a400100213 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 112772284 1250 112771034 112771049
    0x8030a03091a06180712050106050304060b03010509031605120412050709050606120406021204050102090a090204050901031103030d050a0c090b0901120c020c04090822030c0e04020402280207 84
    0x843c2807650009803801091802144649503510001d01d20a1141c41200d010316000c80c4204070558440c031000b4640da2003110141c45a50900c0248100d078101445128483d402c400080c41c01c024140d95088004460f0304400c4d5254450080c4041e01100e80c04c0090000f00501c0f6075404003001c0d28039000e42880030b80c2e0700c042c800c83d19100801005403903800c01c60b941d00655a409040954803031030315400070b00504155500c221079140410042107015801021814003c0310305070600d90781c40c00a041030340314a0003507680280740c034001000000c0c045000290f001c03130010140ca040c02d82280c03a04044803c21a160380100340c40300b50803401c041d003044401010380201c01d90b1501d06048200042c0600b03e1940c54980015a24840550021b1081c0080241c500c4018800d2000301024140040b0540054100603001201e20390b07000481320340002e4113070880781d0100031080110324090390940e400100078401c0c0d8000d81c01300700b40d000350003582d00080c850640c0c0c180140c01204650070000d252a03c20f800206 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 112773534 1250 112772284 112772333
    0x13030218040f030c1a0709062309060904060302100c020a06090e0f06150a0302040e01060f0c08070c031e060501060f0215101203020609060a0204051509010908030a0309 74
    0x40030030180c1a00e80c9205406040091030061280b40202c0312416280319042006842020f06c5101135001c10640200c5586689040c20f05507404d101c0c810603042e1b40b070101071565040296403180d003812000743c09003001c002d100183c803560780e801150914104104410000d8a0703c00c484045107000341100740035005620f081d80509042596594070748070090545480903000c03c00064250baa1780c1c410900c2844013628444e00e030340420401070041d410500508180d2101c40c0004940d0314403503100c4048540e000d076038000b180d08050701da8540d03d80c0401c03415103200400300303000b20126030b00c400d04500d42d0240703428602c10702d0000e09200c0101c5406030820001c02542030180d103640d40c4e0004000f400000d07004d1884007a52a1810002c00041c41039014207410844180c02c0c206258003ca13400e482032500c4000d803183c0d542c07052201c030120712450043c15841040601115540201000600b80b00103040c1030607020561181c599500d103400040140300003c1d191a8840d08000c1d514140c182e545d4094000f61 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 112774784 1250 112773534 112773541
    0x1401030b06010815060d0209010e100c1217041a06010212030c09060910030605120a03050d2d060602070e0907060806030a0602070c1a0a0905060c030d0213030218 71
    0x90040300301a002034100078500001c0b809100d00100b401601810042c6140c0daa8001e07100c415002c1d40110180074042a01d40344401d1440c200545403010680c165694003010011964818480c0144030311180208550701c0c070080ba191710402106030007036024140303c815403600902e42100240300184420704540004841420002c030440c00c2d41c0d0884c0116520948401d00f040104802d4000c24100b5503001070300790155a002c903055840401a59425107090b04207480382100d0503601c401c010300040c0099030800c0341c07003156038442e4015250001e25021812001c1060080701031a10401c14000304099517500c420415160100448401440410070040c803074a400c1d00141c3e214502c0e407191009101415001604555090001e980101ea00c41c4046403540401d00300303000355242d1802500b11a0400d08030b0700d017030104984291915050f1940e200c04070942048203015580e08458809010f0744418021510720280ca800580011a02c042c20301404602c1d60041000e1564100156501015004140b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 112776034 1250 112774784 112774793
    0xb090306010302010e01030b06070b100b0f030a0c031404060606030c020705030c060c010212150a092903070807230f10050a0c0c0602010c081f0618080d090603140103 73
    0x8481c1103a409007088890554141c006074050f18101c1040340e4050b000180c65010054115211030090060200440384c0544444410b5100c0c0302d50007600615020030700004000842c00d0b0407600f0326448518012a240d034000181c109000c01c1500c00301d030314684444041c011182e06100e1245c8450152005282c080e2800e0042515240c0500115000da4800a0f11400b250400d4049410b08200c50070314203194030f0210381008841060441780d9125002e074404c0002c1c074403c1401264054580300c100507250307400c601c1910f01500c56514409405004400700014113681c10b000d114020840100032070001510404100c1500c0e54400116102c0d000810b0311850540794415a0149020301e800c1aa90315144100113452441981400400780382d0200c0c0c0104006034107408c5070382c0b20425619403034140d0310358482103025031594400061a03011200b00802004c0d10440d03c20703c0100c031921247c855107840761b00e0746041c200c04622400210300400001c0143c60340c07500c00c0d20740d0880000c0d0140d03070f2541503548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 112777284 1250 112776034 112776043
    0xb090114150d0507080304031b05030d051b0c04050a020a021c0203040e0c04030c0f08010b1806060f070503040608010e0108010903020d030b1804060f06050d080a0305040f1212060b0903 81
    0xc01c0390144101040c480100f080030010070002d08409800c0725203d0f55a843c10030781c4131281d51078060050386040c0c0300245601340041c030a05a088140c541314107150121080c1500742d220340807541018455010021140c0e1100d110303441c01005402c1c809070b5030b420159000303460a00d000d44070082c0c2d84010f9002401301c640c08410b890560310f06845c4414680c648015545440c050354001412441c404000002d0b2014444000021100305100920103482c1490410a8002c109a0345404400d00e080008496107414402000d184405030200c3c1d08110040d201e5901d15001904850080b030016030040c40180c0250034140e00501c401002409034440b1650000d4881000520402c01c2c0754481e0240c0c251540e0700b08000d00265000b41c1c0c000751901d020701300740029012408129005500d0303e0308c040340e603041c0807040b548400e4000c40c00c50b10780b4101ca10101c00410700284241e80f070942c43c41055001580e6030107102e0001c1080e5075440c2201702c0040c071540441e03019600244c2010001c0080c150780342c90114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 112778534 1250 112777284 112777321
    0x100b030415090c0b0f0403030306060503101401120f02070209010e070210050c070210200a050316020402090a0b030f16172e08010c0206091e01020d06030b090114 71
    0x700c0101d040303000ea29005461103499000380340b500201203521201201c030301e0040c00c1103a01030340d02171040660320320303060350300c2d00c000c1e903038501c0300081d501c800d110401c1c160002190904040c581040003404025144040311044400c44174a90740000b410015458135a10070350240c1490a01c213001030a090001039568071183c2c080000c120f0300e03500050103441d9400241c0e1450764026200c0c1c4480a0455030050240c0500b070340411400c050341c0f580c940e00910005800404a6004009602d40300316a1648440300c91880400c0b0b80c0f041e02003141c00c0d0345403142800c82005040d5001e00503182d041109403926a07800003041075401d4130320f030843e640380164030402d000790304078500301d880405481d121078220060420790211604140d1242290113428806e0300d40302e00300c900d110000c200601030711008a855906c2503c4170356056000031441c6403410340d0111502503028844000519000728445e0610036101207900981e404541581040b050103428050f195910002c043c80101c1c600d440b1903401d400c00c0e0102d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 112779784 1250 112778534 112778573
    0x50619030b04020402040e0405010c091a0a05161406040b010603022113020a15020c1816020708060709051201091502070f0b010b09100504061d060706060e100b0304 72
    0x700118041d500d459044a01070120910b0b4510a40b80c0b60410b20b01800a10400c8000640003072070000300c041c030b82c084500314010b10919003460801d201c0002c803100e80104490544031541105400000342042d030b10310010062544c007401c0c0900e0642001089040140c0c005414036004000c50b1142c0c41c18410b040903d100c840e0092002e03074031000c040c0c000c3c0c04030006000f9013002c3c00134008180038061503405d80359402c4550894200711820310500c0741584103103081c0030040002d0004110798541d044450241105544101c1c4c0290f6a20380000f07182400c295201404107000040c2441103081605015001404140003032001c2004d65494502d900c2038002484034880d4003050560810100f03012050340690054242500c55071038541c01c3c040e649c012064184603070404a0203805d1180a901500c044401e580c40360b2084403210400101d00c0351162940c254409410402c090000d20580300723080103421201d80d1038080d450403061501d02503000d03403c100e000d0501482003000081200205140c0c1801c0d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 112781034 1250 112779784 112779803
    0x80c030d03020309010b040e030903280b040201051303080d182607020a0308030f16020a0b19051302030106050604050d08130e0a0203040c0e010506090103090302030d06060903050105061903 83
    0x2038091645c010504000001c0d4490309100c000310094100202038214000101c094542071150304000664500c00a05840c4004050f040c80741e022813a0f01c00322a60007030060405a00d81401c0c0d07a0b5400b030b1060702e43c10480e0741c098003081600080304e2910900d101c13505540c0001c204540741d52180d4003019014030448510940d15983c00c000020ac2400707560700c00e1b901030304564542c1d40b41c1c0303010591900100c50b40400075a580d40001c01d40ca64080005462400a402405100d40d480c0c40300301030100f0050514145100c45050466855918402c01384200c4404400d0f00ea0052244100350a642c1140e0295108032010720003803120383d84003142da01699900c01d00d8590350303a40854541028403121390100200c00c01c003104000c001d0000b50000c43c8914400e0803204152515081e1000c8414030030b014294200806003c00100355010764007681003540240126410400725035910b1090302e0064100e00b000468003039003002041424010075400c543d0031038030521031601903415080080c540e40b0015041400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 112782284 1250 112781034 112781041
    0xf0308060108010e0a110405100309050c010306050d0f02060712030506031005160c020d020301150e0f1e07020703120c050f060f040305071401020a0804050c0909190302070b070302010510080c030d030203 89
    0x1b80d0802c5400a010103409a00c50318841000078006104099041d101c6014110301c1c8002d5622a11405013900ca00802c0c03101c3d0490181c60760240404042402c907044a000c000e05800706110441e0080c85c480650707800f01309450030720b0505003442da01951244e9400e081c04140301e17442c0c003034059004001606181c07108542c0c070180000f40d00101100000380d055481c0801820784c5407110180300050b41c20000c140d0b40d154680c88105000c1c4101142c00c010004a003001c460780c5803648036403003500510940b04440100346c4940f00d9407400c00c0c1a540c40d9011030f1a040701d0508109090211001043c5288050500c0e80f80a0300d410422850042c001402c1050003d41881040080d0078800e0300c401c1900c000310740300c07602124007420f90081a90144d0b0140306041c503041c21840c0c140190361241010301e01800d4580c411006807408514201800c4043d07004032040400e0300d00c0c1e1000504691800b079800031030a410700e1040102c2c4011180c10002040d0089070300881c042d1400591024009241c0c900140c0d41c1d46c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 112783534 1250 112782284 112782311
    0x1120503040b030c0909072a02040e0d0f03180b070c020d05100b1c0c1806050603041b05120705091905190b01210203070512040f0308060108010e0a 65
    0x21440d0000e1245010120600032016134001c007070040140c0a46011388640c80e03851054442c04150561402c004100f88112001e020f100c50000100601c05003000c500901d05014850512520710000070010300000c00b0510050707414041c8185032001d070800c08801c02941d8540e42c5030070708002c1000c2d05000c210b0b03402e001151940c243c00000c030390b00a0160392a03020507079040c0e000b6124440440b4481e0440a90b49100d881520350070442c2543d101c0360501e100d42c40d0060100070703a80320103a4100b480340d0b0758070b001903245c5441000758420b40c41a03400c01c0728000c40702d00700d0804d41016000103025040b02c600d14901c96400040c40000d4030400c6a0b076010640d1194240140e90b4075001d030f1005141d08040910215001da10700c045074000c48070b41c0030f10100b003920004480a16510803c80943d484c1024101440c9425070700440e0031601500e0300e0f9207445c190030240e03100b443c0f040e101141c600600c042c240c0f0230700d98041026600704009181400c42949803520110903090b000e8981140315551758090120304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 112784784 1250 112783534 112783537
    0x20312030c0c03120f0f0f06090714040e0a2d0216020d030e120f0d140933030403080402040f060f09020c0c0d02010c03050a09120b0603150f01120503 66
    0x610208903581d030355024516110080050b02c10342040c0280c0001b05801e0b681020451344194200d00144581d9a501410042c954102501060034064103103423030959081e4041c010009803800341003202e50307401e0034408242103031045005121a840700180040105400c4040704e240750f011b0120150301c0303800d00c18120008001d601c4000b940903045501d00c504041d044200e0402c11002100d4603022240d0700b00c4c0090701c403001c407412000240c000700d004d50f404500507200c10340d41010301c1007110b05220751400803c66030300603100030510886003089000305a107402c000c0d4010501e000e0444900b141410b030b0f806412000301510003845952942ea040507540c066611007002024040b085104065075401c40c4d400941c03010b00501e07201e0190034440911820800c056481c0c499042c6e4440740f540120303403000c54094108004200400c06500c0c4005812001c4000c9084010b009090021050a1510803d45441013001400243c024044108034040c55002e140904407040c4124803000c1e00400d15219056 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 112786034 1250 112784784 112784797
    0x8030a060905010f0513060305071a07060c110d0f02030a030f0912030f0b0f060901180b031905060102160b0906040302090f100506030c0a1b02040903080402090105060403020312030c 80
    0x2041c41c2400000340036a10841510890310706640b007406c3c0140c2c10980360242c0d0f0841c000500b06902010b000c200303d0304010040905140318110031428015141c1d2000b0a43e40c802c0c0102c000203c071040b0041c402001440000759403030320b07410564a12021248081e4480c008c0d2100358003030650b10b040001b511442600410006680000c2c0915207001c0103001800070940034560403035007460f01280d01340c00c3c00c15484d0356560000c000c001c50304004e0590011110710003124512401c14688540c001001c02e4944051030061880340b40c000c40301c0310265400c40c00c80c0c0d80184903d0440d480034a903120301468104010741900c0140d40600c1e84e58801001203443c81c4100d5000035000310ba44030400441c0c01000325000d01403000c1030954540349a03200d04010302c0b400142d4107100717581000c0000710b070b03924000c4c0040743c1c4680a41c40a0b0b4440d2341603800040451340681016004034036580200f004603d860342d10140945001c658482c2414115000300e503650a00c0034407032a45100000203d01b501d41881e00780c429 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 112787284 1250 112786034 112786049
    0xf01091a0306010302120a1a0d020a0302040e0c09070c120e01080a09020301060503030721031103070f0e0904080a08060316120c0f030f0c05030105041518080a05040503060a0e030708030a06 83
    0x765047c91140040104040706400ca100385060745884101d00e07220b01d00c0c8100540040072500040e0550302008010520400c004880b480751070b92003085a16014100d912a070359907101c4c1190f9502c2030070402c2c81c00c40f0381c40403501005410b101d10354491f0f8004940c550809180074000840303482c0c0d403003c28010080c7c0d4000c00e83c18480030400c0c0f4108800d12070001c0845001c0c03040340794100100705058083d103c0ca2292262140350510002c0e420b40d01c24400c280003c810380c035201c801d520070007021070400300081c1e4081c2d41d40c0b08001090350b0515042012640c208105500600c0750680c9400480e090043c1801080d024480190107201030001906d10103024100c503a01803020540d407450417031901702d00d013002250015081100002d05d0b16040c0b02b01842990013240400c0481c5a04040030014110880d0010b1031560300d03140c903000300d0b90160141024800c242c03039060741c603414a030405140c004020040c041a608100300201054004000e460409a10102403130b22522880c1c8004080d01c840d03001602c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 112788534 1250 112787284 112787317
    0x90c08061f110102041502070803070c05010c0602040504051501031d0706030c050c0105091e01020304020112020a051603020102211603270b062b140c04050a0501050f01091a0306010302 81
    0xb50200c5c4010404d01c0011a9000c4235803a50f50f43e05c8098481c007a01e00040e00b0300112900400c00c5501030b1480010b0b003441520700501c0c0030345a00001c4e085030b400795400301c0700903506a010742403541c15214074401e1018106020f403210390701c10f4144e5910740d1580070310020103458103980d829a074050005d865807008002c00038080c9203030680803181d03100d00240c000050110316120740141520103100312409582c041c3d64015181044011900195021203510020031104000220800c941e80c0c40e08802580709a00159a0b401c6180c031103840301d2895948445000002d50500c040001421900032001e00c0f01d050116088924040104007040725210075143e4421904096080000141649100703240c01c5640d441142d41c001e40c007900f5480d071217001c4101005111641004100c01060520640c0710071411101465884000308090390002c1d2010a101621000144020f18108440212101c0c0a01c1d0000d8000d1410040521098140c5010203006500001064060748a601140d0100c3c050f0000750 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 112789784 1250 112788534 112788539
    0x1505060f04031e0605010e0106020a0201030c091d040b0709060c140109020a08070e100b12090c040f09050c01050f030a0e0c100518100c1514010807090c08061f11010204 74
    0x25008404410845084d4507080020544c07070b01d42410329050306c0b0b06500030200440c50340e00544c003c00c00d0001100a01940800001c1e441103075803c01d40b4071141034802401039051500e800034400e500904004288034940c1400c0c4250395100c1a040a1542c110f401c0610070b07088003003241e0040c010100040c0d001601800040340322170000841d8822162101c422002d15038454124820000c0341d4000e01c455124100030550580c0c40301141f03190040361001c1565400d680c0040060100d810301840100300b02c1d01d41c03043c80c00b4420305201820501d8001c2c2811440c0017120500403446200c000c002d502041e07075820090311020003c2000303200d5402d000e00031109404200f4805000e40d0085c0c0714003218080c1d01c01201184dc240151004242c1031940c58981200615590340d000c2c220304003114164841d6607420202c030811109030541e0080112901904a1340c0c2000d900000f40d03030070180c50700c0c00d000e000001c0c05000d88920310f14550140580550424250159104480c000c90200c44440190b0011502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 112791034 1250 112789784 112789823
    0x3020306010e0105090a0e16090603201c051e01090501032d020306040f0b060d0201080c160210030509060705030f0c070201020a020307081b030105010b030f04170408010203010311041505060f0403 86
    0x8c09028441d07640f110410180d8850048043e070740c24003040c14044030395000a074002200d00001e040b5144081c032980c07440768140010311040701d00c01c03550010000050310765010210440c008003400341c00c1d0344200307000a40c19a120600050040300c1d000000e10f401c444400300b02c2035240030441c400e5500a080d520a81440c0c10056058000c070242542c91400c003001103035003440d003901c4411803140d0603100d80f0803581d00d1407883c019a400007801c81141c03040701c00003400180da900c0b100007040082d544000880e410000001031070104001c0009090241c00c101303000450030040006540003050f51070b8260b07120b400d0701c0102e0501d0a4188003d400d8481d07040b022070104004a001d048607e0800b01c85159507030104101130a8034801c0c814200c80303480800c042030345000c0c0c1c0e91441c0e90290090391030124542c510701c440c050b26403080d4000c1520780d40c00320040c0700b0001000210102644129814080300141c408000700f50b02441c400c09120304000185030854118100c20341c0e00860708032007447c80a0290008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 112792284 1250 112791034 112791061
    0x150c07030503210105041b030209151303050c06040b09040f06170a140d0e040902120a05061009090b06010e0f1302042d170a0b0c071203020306010e0105090a0e 70
    0x80c0d5000481d43c4400101d01420300340b01d11040c043d03100000c0c011100c1c40f850141d000754004216079070000081503200c0402c0c01488010301808143d0074881c01441c0c9142846401c091610340c01500c07404080104025003102d030803e0f120080710441d00080c5528104403841c0c02081280e2119009040c000c10a00d40c3c4403021541c240402d00a802038500204859140b41e05c661591482c0b41c003242c1c0c05100c500301420990305c0202d4061020b0800c0e81c50b0519035411500c1c4c0024403000700c0707413584107404004240d01c031015a00700030000b10000340400c118698030300140d05401031200341003254240c3c0100c0b0b9aaa4400c20031010900508888400510850380030040d6010b80034469801c451054001d914210001c6905818140c1e4221100428201020100070f608020f6030b0400d40e1240d0403c201c013080c400c0881c07034040c03060044040e503541c5040c031b030aa01c00940002980149441402008641e98015801c60010582481c0465403076410f0b000003680107940d0741115020b200ba1008212a4207521039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 112793534 1250 112792284 112792327
    0x5190206120c190e0f0f01090b070f02061207030c05120415060302190311060f070201050d0e0d08160f0906110708030a0503061305091203090f0115050a0801020405150c07030503 78
    0x151811618517480041c420111121902c003400588080c400700040d141210242091034480e03140b01441080940005104e9000314003400c1c1e00314044070911078215010300caa090f65411500313015040c0691210410200d0030010405400b003500e00c3c0b110f92550940d175000700b001e07507801000302403031032a03200710322120010724041200d402a03c800f844c0a0307440c10000703954a0303280b0300d4486840c18104c0c2c2c0c01100d030bd4105030000f14100e41c444950007920764042c000c0740c0e590240d90b42c032800a85400102b000d28400090700c4181880943e80d00000c1030ba6100700c4c5881a04c00780d0070485401107100094603d4090035038070840d898003000c113084580d40d600c0750007140144000c4407464454900242200101c900545600e10542d0002e80859400310944006c0c641c001c101d44280c8030799501b000e65550039925a41a442401c03443d2010500481c48d000c1d05075030186c00e240b4003c504203401d110100340c00d034040708018020f0601c007181e90f003400d070003c1154001541c1c1c007200381c9071a01001076100b0440361600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 112794784 1250 112793534 112793539
    0x20c010c0201020306030d0c080d1a01030b0f01090312051201090510050117070c060e0d020a02031b090411040204030c06020706020709020f091e040c080405190206120c190e 76
    0x803054100e0392050007580c0c05000c0c0240a80001140400d055400c854400c00c200d038002c40078401e41001c15141d2182d29554807981e5240100c03c80002c00042c00c66043ea00c01e0352250040300d40c0d0200e0b60368040040e000f41c1b070340107845e1484440d140505444c9030060264085900c0721400000c501b140942c0c008a00802d1552242039000d601c540c0151122141c0c10703001c5140e041218009943c241c40b40b80402c0c841030040307400203000078034600da560034903131544034100140c0d100707040c44030444c2820050b000c40030b03c41e20585400c28009130300041d44c0d281c01600281100d8600d4840d0364250b80c984c5e0480e4000e642c041180c5086580e2100080d48940c0301e1b202e0280540580703980095104842d00840c0c11001d440d82041d481c1082c0e80f810031440b05040d4280036080c80000c540c41180ea110b40c8510800304c1015201d072562490540ba00516201c403410b12104640d4511b0450801070b1240c2c820384c0e40b61100c0100c0d44000e81c1d109d000c9201c0a0249207a00110411b00141610915070040140c29102005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 112796034 1250 112794784 112794791
    0xe0301020f07022403040312060506040305010509070e15010c140102030f0712050c040603020a021f0b0405090703050d0c1a011715010f0603021e070b061903030e090402030f06010801020c01 83
    0x2003a1135004a03903046080d0440e03038507080000a0002c2d1240466004400c2801e000282c0c5544913000301c0d407039420540044843c2c4e0b655600707000c06048104425001411032500090a5140030001030f5000c0000e540d0181c10b02c60514501f4003008a0304076548141c188482c021900c1e071424003000c825600e41545d151003c940034802241000110b030084030700c101010f0246900d02450444110029071103540000f0444c0a240314450b565800038244503036035250743d0700c0403c820301c411042000b200c5025060020560046404100040021070300b4080f040c261305140c000031642d030400c00404190000800500c0950b42c00100b00c16141400c1c814186c5060411103014180c00080c3ea011090f082c01440b1151601d9030080201c14400d4000301148070444600c40b078242c00003400d24000d03400c80d903022912010308000700900b07402c01000f054020899101742001051030350700c01078500d6040301410f41c05112050005801d40d00c1c00c2007210b282e50607141c212100d940e5644c1e8814000d41210035208107a509 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 112797284 1250 112796034 112796059
    0xf05010c080c09030705220c030f0b0123070c03061b030c05090306040209060a081c030b0108070c02150715150504060806060d110607110307120b04060504030e0301020f0702 76
    0x480c2c01c3e40d0600001030700030701501d03041c0400c000004040344941c0a01000000601075140c91074007034900140483c0c0c0380801d20342c4504078081c0c00e07162001051410800703289040044c030681714090f18035070b07400480ba1541e24105130821070541c4120340c10180c44141840550503c102c50740307000d8103c000d081d903000c103e400603044c1c00301e81030300c29021100e40c5a40201c02040c003500c1c010781c407943c1003040200600345017079484528a081191f0903000c0c01c410318808200c43c0c0c0300c94240c01086000c082c240b1b484202c0e4a4060006040d54003404006400340300040d040c8100c88035040100e4508a80152900b4441e0340c6c14060040684503191f044641001e4400c000649800d0500031003080d9030300000074181541ea40d03802d0000100d0303400420b03a4500880002c0b5003464031114002d0880314048e681c1001d100d904141410714204295108621107401801c50b070000c503201d800311036003082d803048001c0740540307582c2401c480504481b1004c41c0c0c154400109030b0f44002c4000014003405100fa10410071004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 112798534 1250 112797284 112797301
    0x40b010b0304112803060501050907080f07120b0a08061503010c21020729100f14010c0803070c022e080a0905030d06090e060606160309030f05010c08 66
    0x180c600404019106416091610b80100c1c0c40c200411400504d40c822281102c1480e6440e0150b4000d549440e940d400501c2030b414400311051307203e0440d0510211900340703081a002c1c400c80c01072000342040400f1a0600f55203071a50400e03010f4503001002c1145c255140d814185d00d4000c00c0d00c0c1c0903403009481062902c18101030044411031075003a02d40c81301100b007600080440c4a11001c49488040c0d007044501700144205581400030b807440c0c5603004108900944820920101034580c04880040603820443c2d034052001210a4a04d241400f000c0c0302c001c000185c480205040f4001e0400f1804420044880c2e07000360342030203480c02200e0502621503854860112501c004107101d0300500d6800c480c0040ca400740030150340044d03c07500005003c1c0915195242583c02c0b088a41d200a500c0365001c00001009004170505014440c0203049141407030b5001403500e208414110399403a003103403403960605d40207a0700c44004640100006551400c240742840c000c00c2518207282c045074084021413071a9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 112799784 1250 112798534 112798537
    0x1a030d0c02100507020406080d110f0102190c02220b040606050c06010905100f0e0709050907211107060207050d050a1205040212031803010608120301170a1703040b010b 74
    0x180d03006040c2491140d4040c9003190551301c200710503608a078984c6c000040c028010030500000d600303140d8410300c00344c115590441c01d15075a8202c249050303005019140403072984174021403183c11705003481010285180701007010704c0400e152081401006030500300c247c0c4100d400108040a08960801c0a19101d45003074481c2d0046003000b00e441d610101c010311041d28981e101d160080806603119000d540e5032000b004190406412800e90400341100780442e540e000240f8102602d0b048844490034034040798028004107095070200540002031014400004c500d5000310754441d0b00e120380a5899049003083c00c0698041e000440c0c117481061480d076102840341040d108a40c0f415610b6006403c0c403108150040d210140081c0e070300601100c074108014008200078558003641e891040c401064440801d42110707030b20381c001c105541221103641c0145280c01c003107034191040e100c103400c1c00b114400f1115140104101c401080948080794210b17003940c1344009507104034400c00c8000712503038894124600c1d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 112801034 1250 112799784 112799807
    0x501050a09112a1c0806040603050a1203020c0a080c0f0c06220923010503010501050f06032e0e01120201050403080913320402010e1e041a030d 63
    0x2541c0c1400400d00311007150340001c0f214004844070344209034a50080c5400c2403082c8003803001c1c99207800020040f8a801000b10f59101008a0b8104644e40c90b50700c030561124100c00000389007420706d10303e0b0012140607605540300317110100211a401000da00d44180c0e142e0180445030841c0c8980c015070451050300058010001d10003514071030819406086c1d280001c047c0f1441c1d403103803020b90741c1c0c0402c421000e880f440b285d001d40e404c41c0c1c1030a6420f030107000d8111107042c2c014a00990414005002903111300f8a0392003114002d4806131741e0790b82c50701c9030007051011098100c80140c80110355070404a1400b05404159000c0c0c8803000256641c80700c80020741711114600902240301400100041070248014180e6980050400c0f54007500f810216404c4441d004224007840310b50b490000c1c100c03054a0140c0c03e0101ca0382c01411145d00f0b094001a000323040c1c00521905c1000c05511440c0380c50400a844030700d2900c0036106001100321941e5a40d0301441410855009110b007441d01891a446803414026 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 112802284 1250 112801034 112801061
    0x5090303060a060804170a0f0e031b12100f0b0306071806050c2d0127021026060909061905092e0606110601090c120f0501050a09 57
    0x4940f4600714081c0d131500f034000c206591078801c0e881c070060b900070088010404544c465070351205402d07420501401241c00b030b0121034000c0d4017861205640d41c603040c45d500002c41d000c5400000750032141c2c60a503d0b000c0440c80920046081c49141c0406403000c3e08100303454401101074480d07541c1e82c0c0a0803122a403513508044c0403105001010480300d0f000b84000c08113040400305485620300300c0c0f0560100e040700c10340800407410103050501000710080c422243c0b0340c16604580304c001c1402400c0002280107000c006031003070000c60b4644400714080d641010101140d62102c44082012006602045104941c0d05000c0c0b656000002d59400700422050b2007011021403000310101d04200f808010100100820464403a19003900d4500e07201d0542d1705a4081142c52203000000c04041540c1914001c0d4040c0042c0408030005a50394000440c2c180cbc103541031301724002080e4011071400c85862400000c0280028a010721881c0990381c15040305040e03a00a0710200d101c25038820102085940081e044403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 112803534 1250 112802284 112802299
    0x60e0a050d030507051b0606100302131511060c0903060105060307121a03072309040206041202030102070209041511031003020108090309060307080115020304060f03052a0c010509030306 82
    0x2040740b400380d4019900400603162803810700798a85030311000314450b03a0000380740d540010100030b42c602e058031a81e54956864501541001200581d41744034140b0350003181858190b610140d40b40c1880380259611a41d4254111001d40c10300509440e6103a010104940c0280103042c004a45414140102c078083d0110b035650b150030408078240c210080a01c40b10a24203070f180f8040a044942d42000380c01701030601d143c1d40d82140d1620002a501200c0c00c58a441c0c050150700c0100405655a4401e5408940b070000035203120380b500b1b1002900a224160000350700181400500042c8881c82104103c0007805c544c0030450003c000d2201c120174081200c040c80000802142400107520600d00150418265000c8a0521419100041054000300d80320400165208010002010741041c0103555011b103001440c90035042c600000c0c600c0b08404d40b0001415107940c040345034411003018100207600c00c002d004400e502a0b04c801e5017143e003c0031301c0003181c1d828100403941e8054003000b1030b40110700c001c2012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 112804784 1250 112803534 112803553
    0x80c030408070f06050106050901030f1103040b0a06080706030c080a05190f0b090a020910080c0d05070507020409050303010501031a09040f03020f070f0f080615010e06130e04060e0a05 81
    0x1001903020460444040a50a0b0f01c600010000d0040f18082c0ca4030303441d86d17929585440c00040495810300c01610500d0704005850a00c5c0504104603600650400856081540e900781c001c3d0250807a6404584540310740c4100255242e4942d0145401c5503043c0d8a0b009070780c54850340c0b201528425194049841480100588851001d52100707444103c0d541011400b4000031340010503d000031034214082a80004032058145031800d51038000b03000340e0900303540794104140c4401450190480c05442c0b150307201e02040f001030150307040e5199250300410174000e1000500c1c02030f4890700207205a42c080b170b04000740d46c5c900c0d40500c5010000c04d070000d4800b0075a582c60780c640a807140c000c440c0a80c01d5004004030b00003440d0090060201034035800003909501031170400d1070020030b801036110180c290449810b20480d1000c410315800000d6003460014088000301b8006003032403062803548850103200e6080002e5840030541041c0c49140908010020b2400803014241c903a481c00500070b00076000750701b05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 112806034 1250 112804784 112804793
    0x115020c060c0c04050c0903010e03070809010503180d02150a06121209030f0b06090c09090a15090f200901020a03050f0f04060503180d020c01120e030a080412080c0304 74
    0x10741142d86102c0d0481d040048510082811030344240d5951003081d5000440c03c1c440c0c00c1c2406110352902c80480103500c1c01a8540703d070340071030182c01c41da01d0401a000011414031101004500039040410056400c58542c5042c041d640b00e001c0c844240504130381c2c000055000340c65102d40d80c00c581032030030076801e400300a0761307004240000d11020700305014103c4070220100f0301402c88070341002d2244000381042d0804c2c0c000c014513013a0088c42040703190001c0041612a880b241c2e409600139603541c5020469040c07065180c1c034024166044803128514002640300c119050b5004180c6080c03000381c01021041c0715001c01c0c04035101e010115405030380244c960b400081d00c918020b0441103009060039082030a12a140c00d46a44281d101400040b800f0083c840071580318003c080304000101c0060812441c2400080d4440b144008820705102c004000704418031602d8210403103660030b50003981e65802c15910050054002603070300303403040c0b81c8082814413854000d149190103508401036580c1185e846568 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 112807284 1250 112806034 112806037
    0x100207080c19080601230a031505040201031103101a09060307080c0705030a03020702010e1f030902010302091822030806040c0c0f1511040b0a14190f080115020c06 72
    0x812440d41c488105000883c2d24007840401c0c00b81c1000d1004504801d0000b00c07042c4415038001e800d0744200c0d400da84c104006001c2c2840310018a20f00c1c000810f21765601d000680c01024840d0f41c900104400104018204c0145401c040035507200300250305c003a107001c0e40c10f00828001c0001050300f0860800c0400c01160042d2013a0394403118461102d480c0c400d20b40d541c4c6003903401049002000caa00441ea150440d03800c15001c64000714262090701d80b00c1d0081504d034881300c14100d0f048043c141d44800c54004d5911039012a40030082c041c0c0f41c960003802210801e4003c0c042200d400460011751040c00c1c4400001380080140d468040d40c0d0045251100c1c0c0c02c000041600450740824001c00e01070002c005a1240d5807075001b1402120f0010b500b40203104010165020b880113000541000c1001340840175904050b2400c10741c051501014003000c05018141a00c1004007441074600149400c3c103025a1020f424061800345980700c00340d0782d0781c03001c403007034280220f40100b070250300150021802800c01d0340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 112808534 1250 112807284 112807309
    0x110f161707080a08130f0915050907021b030a02040908190c08040618090f0506011202040b0f0904020405090108010501060311090102250b0f0309010c170c031302041109100207080c 79
    0x125940c5010b9846c80c1c0b4480000c003c0c3d000913416901e4001609140d02c1601d0510010082611f4041c0c140c44d040000a44800d40000800500c41c0d420f858181d10303850030003404030b905502401c1041485024100248107421a00d0790400d1640d01241e0459014480c4448055081d446085142400d0a15030140e9105c00d0705500113104088100300050003c030240603c4503c00348801000481d41007003400140036080c1880740030080c9004100811841d0f03180c000301c813a500e03401c000f15915200110b0008000c1d2060754400b9a01071603050010070803000640c8050b0480c2c040742c07020070080c0307110f0703590480318090700e140e103800358000c01b88000a503858103a403491100c09400e201c2540303544845441566400c2164038500d8044040300308540088240f1030000e240d0140d0030000001d1a81a140c05409480101449036005011002c282020311540b0030104141c0e008100748551403201c002080340b0b80181c510703107104106d43d031800d03402d40c0e00119004082d1030120001e044100c6a80007401900004d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 112809784 1250 112808534 112808557
    0x30c0807061e020c0106140a170109211d06040b0a020c031e061e060118050307030308150a2303071d0106080a0c020d110f161707080a08 60
    0x5004502e100c440b01641220485490500107880d030130030f04e441d1801c40c3e0503a0800e051140320b075809180183c0c1c8002c1c605e0101e503a000e00130f50390b0f0300100344440d001d0164104002e00e82c0c4544600c0761120495030341c9420b501903480d0b48a118483e00d5002009a0341058030036960090800c21081c4098800d140c001c0803088030b1070040f503e6840400022901d03001102c500c0840da1139100c0d0b041c4c07038541814000d143d003000d00c042c00805d90201c0d038900000d80d2500588883c0c14841103004082c844154940954004e100003000e98400c540c3d0b13410302805aaa08480c803003508030140300032000b2403400c03404040c103031200c00b51480714800341c0705039140c0c01c0981a4105941442400d90025502049001103811500d5040901925515169001e8401d51000d008211b90740e007807100c90000b140d030004002c1d0240c803a5117070440f4240b0840005508105040b01c046145000385181c0564031482c0324042d17800c440180100994209415140a840300618020321845400c4a80081c2c085160078000d018803980c0b2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 112811034 1250 112809784 112809791
    0x180507020307140303010f080c0a0501110a240b03030703091811070c062604021c12031b2a06140106020f0106050103090305120a02040b040311041503030c080706 71
    0x66100c051401c0000c840f0040c03a40e20000040c4462204070506400400b01c1c500141040050500022009016401090304001000d107011100b42410000071980c00d03000031072080b028007420607403079000d01c641e600721410600308030054505007400000c031440d0980603a0340d405018205030b0f0b010161600229070302c100036200e403074885c0041800d900421032544104140707500c140c585400a451317162206051200d040c051804600d50028140e001503003d54100c844c4607403800c07081205070190245200141980810452650240e40c05600009901c40c02d82465580000c0400c0700301c550044805840d4000c0c5102d0410003100c44c5000014607051f4840c00000c1071503900c591800e011864260320400060b4004066003400c00c4080c814000941800c0c6024822551b00e510003370b2203445810810001c0d840c2c51000103040e010f00ba819078000d0003c1445ca030f41ea580e0f981c18100d50101118440520403803412200800c0c02001c800c03800103c0b40d042d101c00c3da815403075803a45525138000301415143c0c0b549 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 112812284 1250 112811034 112811047
    0x3170604060b04061706040501051e03031204050c0307090c05160503192309060301030b0a0b04051305010608010501080601151103040f0305011802031c090e090609060c041805070203 80
    0x1041d0040d00c06408195940b020540170040007080303a01010700030318050341c90400103000c5030700e500c0401c4400260118091045607060004646103101e580c509120055040c03040c4410040d0118241411a00440031615003035120400e680494084414038004a0300400c07a10407030006550459030b9141c0544207417410007000080d0f1010304174070031641c00c0000340c601110610a103035550280080f0030104103410304101d00c09010880c03a200600014000130924000240d44100f143c02c00402100c010b44123112500f030100d105028880f2100c0111820350801380d012541400c14441c80e81201d41400c000c04543c0d182c481d1450720082520384103820091180c0181418110410050004007009400c1d07046076840e500b0014219200b44550501c800c405480050240e90001a0f00641e011581150505c035104200c3c10780c2c44000fa940b0428103204854100b1001c6c04001c0f80e95407040348484142ea50b50b41e541c4048441c20b1096003d251492440b2207040401c180b203592203107520070030310b0044034980035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 112813534 1250 112812284 112812299
    0x40c0f0e0a050a091d0f070513150305030309190b07050309120f030114091e0603010b12010c0e09010303020d0507080d05040c03110102010606050301050609060f180a050d0317060406 80
    0x3003042d009850f0180d01d0780224050700a00c041c2c050701180c3c600e0086c0851141459025071a110240701342ca2180c020032904d440e0810040d0b00c401d44100e03410641500c4d8036902c1c9000c0b0384940045642000e1402800c1e841048001c6980400c101190304c1806d5403200c0d510313a40240c506810180816505200c2c0444050796550604011318881e000c081659890b507240481a100030381e00260100d0041c00003c00b4020811200000400303407840081085010755101c0003c030b40149200c10a08d81e10400b07112000803a0081944450307541c1041d82c0d5081c1500001c030084c0401c4c0c6c007007840000c005901c40c802c900103482c8100043c2c180c20344100d01c01807500200d8526082070f998103942c02d50b0740407018242002007000352000c020004a0a00091001a141800103400307400148666030040d0000a100305895441c0000c99030742a10800c002c1e07444d45801c0c00301103002e900071503e9034018400107002040a250042d1205a0140e05548500c2000322820be580a0a50060100358000340c99503008110507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 112814784 1250 112813534 112813549
    0xf0a0212090703050c062104031112070b0a020306060301060309030e210d0206190e0c150403060c03110d090c05120102120a0c0212071704090605040b040c0f0e0a05 72
    0x8000c01001001c1035411404c049090070818151075104200400c000c0449100003c604000003081044a000c20f58480c1410b41e01c42d503205000040a0050180c51140314081c0d8014000640c0519001e400301e94a2071250002c038401911200c0d88a04148010460701e4800e41160051600c42e00d08003020f0610600840c070049111050070030468048810200f44044c100149030f842d100b00d200411480c00d2041602e203030010a103038088101900d59401d00c81e110b808214000c1c6062002e04880b50800b00200d8103201038105000454049041a110a410301c1c8a07020b041010034500140900c1c01441004d008000c0c005004215410f2403c008001500c7c0c0d00c5d036003c0c641224102c000582e40fa440d811050250f980300070200800b9900d880381841016a001032183c8100c0c8680520558540443c18000c0000d0440100b10718660b07000030b0b001c00e81c407200da0807c2080b540141c0c2e0501103d4001c80412060b201c1004a080002e01c566001c031140f40d114034440000b4060190246026940f181c0c042102c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 112816034 1250 112814784 112814791
    0x50607060902120a020f01121b0201020304021003090c120f0203060903090307090905060412140d0c120c080c0904270b07080f04110a0b0a08071808060f0a0212 70
    0x420703600c00c008015810001512411143c4120140c070252085900241c074200183c22800d0421465807801001407040d980420090170031102c04043c41041480c000f8040d50044034100e000e000140c110004060007402001840e079400320f913465030340c3c0c20000026a1101014810307140300c01201c84c3d840140c0c80a002c628000c000c400050740e034410342c1d50306262902e80e01d075100c00ca07a40c0c0f13005c2e241d40201c0d02c0030540b1500705a0040410511000a813000c40726040003188480301d005002030900760301e4503680d00a210300e00c0070f9103444601c030b8221629030049030340c140d80400c04249101c00003002e1048036402840d40c0000144006800345204480039003408500d0000c0800603030146040b418810903090080c0d226806291003002c5140648002c0b51917400035000424800750700543e4409960740090070000707400c403d40300c6515802c1150008060b0101a521500441c8500114010140c10003051100340e03040d18005100c2c82c0c9604100000b070040003050001c42035424044500c1100401080500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 112817284 1250 112816034 112816043
    0x80c0f24031b0a0c140316020609040207050714042d09030912081312031209020103090819090816030f0206041703040806071b06050403020708010507050423011710050607 75
    0x40004c418a840c010071122100400b82c5548144500c0c400c9254180b0000d020341d90590301c841e140d100e440c010402071301440704010000d0060200c04540c1c60f00740d40c00041da4400032074040c4100c6111000c0c0e000120f41c4213600340b45000850084c48803e000c0c0b6001030012502c60f00d4040601590707034001319907000da40c0b40115000d03a0005905500300007003080a60203401340b200e200c0c954006956028085041070300c4c2d80c20200f0380719200c10003960700aa218201d032a4003e5603ca0b0350b60002100d401c00c1c0f003402c1085001091200b000410b0300000012603041102c0d070071689601c55030660302ca808076090083e034101ea12007020400403d1751228644460400d13486440210780721420b0645060030b03c840140ba0008102c48a18050349072110340402243c85a00b240002980380c0300d5040803030800c5010303084a5115801d010510600e01d900500801c1103505030300c400c0c4a0450741c4840d01c600840780003000c2d03000800c180c0000245800300c50103503070040b01100c1c80b040d12550340e002092440d0080403040d103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 112818534 1250 112817284 112817297
    0x5010b0406030e01050705030117012d0c030506101202041703040501110105040312020a02030d1e060e100e1017060609010506071a15030601080c0f24031b0a 69
    0x41d41d070701401102001c4400c000240f040e0f1900d420000d1080c00140b00b81c03560300000c003401c2d0820240c298406581c01021044141920104541c0301c40551701407981c04040c145044c0100e80a24803d1040742d0040c03c0050a4a480144400040300d02140481c402c40c015030f820000051141140000c00f82907003c40c801468071075140000142003000410703610040350741010104000280e002d4884041520104801a1102c1c2141000c070b196009034100c0e1103082c0d01e4142c0746400d036401c030854a0f108001103803050003134603241c8000190200003600c1e60305078042c1d506030034000900e69448496101801c04d20202d0040c0e940c003080381c820419004030441d150450b40a1120314248903484901610040d82c050f4504146561002e4402c840b522500c813102381c2c00700c04520714035104121400891300081c1110081d58681c030600f5140e2600f60180c5200b0000404800341504000d102d50001c1d603140c01d01111a144d80c120440400e6000038001c0c0090886180c0440051102d4400707003038012415542d01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 112819784 1250 112818534 112818539
    0x7030b120714031e03071506030602030a050612030f0d02030a09051024081c02011d0102032401080a09031202040602030c0610120221010501080a0605060405070e0f1305010b04 77
    0x150800304d001c84640500c4c000c000141505160000480346e13410390101302e20b04100700050307200000782825080107044600001c14000d0f400c000c1c0e042180941c50494500e0340444d6006c40095882c8a00f0382c03041c01030b05003440001c1d420400d5601841d488409510003117405003095a8490403d100031025200f503684c1c03440507820100850b5a030407000212054580d0321a82005034803944c0e4100e2070384800c03100c049002912800c2d1701c00c3d0407010600303401010b03403803034140c108a5041c0130750000c440c46203030030214034803041014071030317501e10340c002c480c103844e03000f4152901c00c074481c068a4980300030f400740400000031580400e19172000303200070000c0b0350140d522404154036442c1400c03000361030003480d0b1410b180d050080882c50003504001650440d400a01c9160311034010b03a400d02d42ca4401400d44d403030100002030294001c50b0702031001d8440d482c200001d5443c070080008a0304151400c1d00041c0c900c404c0d04c86242000e40501009450081c4800380000c00301e0540307415240241c100310901900031408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 112821034 1250 112819784 112819789
    0x402040f03150e01050c071407150f02100b06070b070306080a0b010501030c08060a090b1201020d0506030601060816080403030b0306040c05032b0302030c21060909030c0607030b120714 81
    0x340c000e00f0380c0e428002d00c41400e0003102410503001e031940180a00340c41c0c880308018100200090801000c0c0d40c0d2000301760500c203c4000c0c1c00f584640e40c0032400f5019810107090905030380d00c41d1540c090401003c0e03900b0309005854440d035640300103003100705050350f4480c00300701528100b083e2603005220303116012056040a000600f0756292011800c1800040f03018000306070360b020a20015282d00f0440000c01540600001c0d1460508500710031841d4400030383d8807902c09003900101d00c6034000340e0444181f641c0c0d82c07004464000d411103004413000b0304c1400740e40105104628240d0058000d15011504082850000e424504107590450f881c95012004000c0c0d800e003401010980002034461103940f078070300b088020000d4003050207201010350002c000341d80c0d0a11002654a0208030302105980d09542c4800d195040074151600e0b0b00c40c0aa45001960b50b03040001260b1014044902502094441c554281c0142011500855001030080500440c061003006120002c25403d0782c01600102000f06 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 112822284 1250 112821034 112821041
    0x131532130b030c130503060415021602090a060906050a1413090803100602010f090308130f0503120109050a0b060901032d050f060102060601021f0204030b09030703020705010801050d030e0402040f0315 88
    0xc140a40c1081f010040031403005519401d80d0b002c107c601594620403605401031710701e000c02d002580100004248510030078160710030019581c106104002c83c0d601d8204000b4880785520071645504240d44a6507018142110b229130031a03130020022a02c1c85084e9030b601c44030303002103410b000c034664032402c10001075070709000355015012203400400a0790392649004044460080c140803d00e4440c1084800708a5880544581150404c00741c9071580c0c80d07141d006c004920b00f84180041141400c01040b10750000c0c1c41072420b0a5801008207140c400364000540107401c046854920050410002e0b04544540700d0743d600c00521820000102d9251000407202000400350403541190300c00c1c010050030340d030002501320070b120400c10142c1016480a0b510350182c492034100414901c01802885000c5030004081c010892081c0c003a108690b07150401160080000d10595901c400301d058042c010038003580a030744c41414050710141c82c164840d50340c1014401981c6c400c84030f8600b5081040c0400d01941b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 112823534 1250 112822284 112822289
    0x501060302041409060d14150c0405061206040b041a01080a0207020a03140319030504030813031d0a03060e0c090c0309100e03131532130b030c13 64
    0x40850800742040d2020608440107030f03505008404440c04100700e43d964214800e413039544410011400300811241503158480c5800b20020080800c02150b4508020416602070300d001621540c10071081d5050240f000700054411604195100c6402c0f00304e0702c0e940145104500309080c10092040190001800407100500280416106016690059442c01032140c101d03074012610480307580000441038214810024131500c20410000c03000c24954154001d51b103d035010341c403052040d40d5401d060b80c980342c03c400b20007400201040c50001c201070a00d42002d00000e0041d10410203140c8a80d10381c030031686460301d1041b0a03400401c440c1100d207440d81d0031030703804001c0700d501c0ca0941c201044c1d001ea030b0340c4192035805031447c3c8a405081c201d12040050741d0009042228402089a54035103400b4003620318018100054042908100620780d10300c258001100314005001100c01c5c0044024107542040442044118003294000b40c5809041c0c003440c0a6a982d0358041c1d52034910842905a08046a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 112824784 1250 112823534 112823537
    0x60207060305090705040902011206080703020405060f0102060a150803280c0f060f0b030a0c080d18120201020f10050a14010323010b0a090504050606030115090c03060504090f020103050106 83
    0x1041001e01004ca1014101c4000383c4011074049041c0c80140c400c06140c9996144051a001c00001c0200000070541c2c1203038001d4400304000d803101c405104080c9000c0c40d260b4056841240450b03050411640000c0c0c3d0110b80b51582707003400b5110703c2c415085500401c02440c030040c00c140300f10542c10008811010b422181d0a0907050036410341d80340d400081504901500d00e5980d4541107001407a80d030050040c003240101a1101e01c501031030a0303036905c1c030b45000d215118420102000314a0703000d0b51454a003d9924808102400c0c6455808618690f40e000708904500910070081d81004c0c0810500403010781c0c101d400700d424546400314208481e6200c04c0900b14403213140c01003000c02c1114100c40b00d408018031300302c0a104100071003070f8003400c0c040521503045000d4080004801e4206c5c3c1c0220f008610840544200d500c9a10405081c3c0c5c2110f8010840c2e04c00540e0304202114581e400348407001000d080105c0c407965139100040440d60300e0001513802140c541e500c03070115a4035104841c01f51959 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 112826034 1250 112824784 112824791
    0x30b0316030b0f06040906020408100605010809121606020a020604110303030106050904050a06050907020a02090f2215112101081c02010e010609090c0602030a0503060409140d02070602070603 84
    0x1d40d20394101801024040e02c000c01052004600a03483c1c80d04207504aa03004603003956599982c8001035a141c8a081c0c11414403890200d000c01c1d1984a401224019402c6200070040e6903243e40f10390360b0540c840001440a0100014481c000610900151404440343d4000d4280c41c50142800c0000c448a84500c03480f9410810051103404d0b000400d40b03104d0742041e5000202a0b030740d40074100091600707400c0954010880c0f0108240141e0014000300c0caa40300781d6001e0f080d40c4410400501c0c020341078440c01c3c000551807206643c49480c5009107000d0314000e0700d281400017094500c010403a000c4843d070902502c4000b9034003040304102d0500c0c1c7c00141d02c10500031310329850308130840e454000c0303e0b1072a03200c050f400b041104840d101350800841514003800820206655010680090a1041c400c407140004a000082d5550012007610341454107511550b2071750b80c1d1340c001c01005002004049a1541c08646903240c1c0c0a000c200b240c01f080303000d8006042e0f043c104038000e440e00825500c9a8201401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 112827284 1250 112826034 112826039
    0xf09101506030518010f05150118210b13021f0804330605030c06040605070b0a02070803040506040309081204090218031006090f060e160519030b0316 66
    0x24403030108548081c030b00020180c81d040c0100e241d0401c020300b1182c10350b080080c00c1c03000c84242d6100501900041d000491450003031720040d038074192070640740c411000301d4000820490710010004840c4541c5030a001da2174031490740d10344041c2c034401c0c1d420000c81d840c0c040c5603004500300041d1854120f002450410f001c42d450318002821880001c10081111203001003000c01c44842d0341e948480ba4090b000b5a031200190780044500804180c030541c0e100b84100d84048402e800e01c0c404a4040c2c403210b60f90985444000e0312581c205c3c1c0c5002d080012420750170001070001c140300f003002c3d5001d90301c118080c0500341054203004080782c507250481240d507000101c07a038480f0f02c990001c607012108412030140e141d070900380d00038981c2400085201d406010750050030102d03040c03c0c1d109800303072044044204480a5882d5140c411502d40d8091681a031800c2d0010885108030b0485441f44044c1d04c0c90000d140004415400c004030204d602c400000c2600c41000b0841440e040c0601805001c0094640ba4400d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 112828534 1250 112827284 112827311
    0x2030a14090d020f01020309030d17060a030c0b090d0c060c06050a050105060a0e03030c0601030b01030506150a0506130807090204050411070201050901180e0103081902060106020c1002010b090f0910 87
    0x44242000707109184e1601c01c5020713a4003e0003504c203402002000daa403800650480174000301c403241714002c00003500c100058901e00c0c0c03046007081030b00e0300401031101490a0803100b0341a0740c40f00710540e5002084085450014460402010140c0034607030b107c0c07554160301d26103a000e494000d425500c030030741040010301c040d480f200305803000c6400d986460f190f040c140c040413034110300c141d80d1f1034141809110700200901c11a07000d003504803403003081111a980c0d506070410384042c82c8090b580e90b221031000420809407078000d01415411b203038041001b5896950305000c900e8109590b0000c03403410340101d4104410314203480744685258514000a140c6a003940c0024018400d0001090500440050f0b1011340503500b01080702404a00d41c032945256124101852180c1050040b0020500004003101c0c0b40c0d4804030f04a81210410740091591641e20f2040005a00e240940e040c1107650740c54071100075039980700c0741500800da0080303954a0b6080c0543d207541002d00310205020468203203010200303801c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 112829784 1250 112828534 112828549
    0x905090a141303050903010203010e0f07020601060c0212010e0d02010f0b03150105040510080d03050a0e0a0506070503090f0601150207150507060203040309030812010510090501080a0b030307080a02030a1409 91
    0x880b030000c40400580381c62400340e0707281c01455000e541540c808000404c200c00d107a01c540c1d0082400450410007030ba03030f250040341d43c0c100c00d00a07280007c03035101075080142005000e000c0c14418a01c001301d4490100c84106144c20b150380a00030060b910390b565a42205010700c60040740b079001350b001d010107454000280035156018456140a00e0356000004d1899000628040240c84c21405070380e50540803440040c094130042c0d070464142c620b00700101c03401240001e400120268808060501030780c580700260381c40d40000700007407170a020741c55460920b0f060520903035000e000701494000340300101d0a1300910f04075050304003404022803040410310894000007aa90455880b17403002da601d070381e10720381220081282e80c0010072100c0c02040184a0b0441c2d0800223043e40d5090b50f0600c421121a0001c45483c0d82e588a0a40412910000304080f40d01d00e0b0001c07803400c20060102c0c0e1502e001941c5010381640300b000c2580050f000803c44000240e030105036107460884243c20071b81801041c00008007031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 112831034 1250 112829784 112829791
    0x216050d0c0b070201030212010801050103020a1413110408121c0608030313020f0d06051902090114030411060a020303010311040204030c0504051017070509010e090604020904080f0a0905090a14 85
    0x181500880c3c9a011603200b50112000b1501100030016036503135511900e070103401c2c28041244210b21000340490031f58852290070b00c1600c401414110762072a81c0103004002c04501c45084400082003002144180c0c1c00c02c1400341c24004480c020365605008a61003403e42c40c52585005414240321003081207600002c04d40340c0060503107001070f5282110341300055240d07000610243e081039603665060280603460b8800ca100e40e801c0002c60740d440f50b80720121401c0348502d4001d0390204081280e418481c0780c0c400042e60b4458410040c05440050002c00038405800541030030006038400001803080280e440d202010022094909505040c01d60744d4030480302c2c0340381c091240190303515400150810036915483d00100860b5600c4005640a45101c68541c7da05003d0b1701c0c040c0000100014040004810f440d1140b030a40c1c01601c400c0e1200c0d4200b26200d0030207007080d51042814004250000e040c400182411f003419100d03695440e16004c01d11030508001440907500d145004864419503500c00b903120351 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 112832284 1250 112831034 112831049
    0x109060f020f12030a0c030b01050414031f09050f070e062701080709060501051201030f03050c0d03150b1e1309020d020702010206010b0f0909060f0409030216050d0c 73
    0x454580118049103441c1c490200c1241c14440c02d000107401a1032034000358000d4045e080305125110041c103040d410b49080080c02400183d042200f0020640c01e10700103a001c45008007175814440490060150920080f00300c4019540e072510608100b05081100c003022025800180c2001444c1c41c0e206401701030014032107400340c250383c444504000182c082c071000c1ca01050070414000c6d612a03006694909550055034211440c0c100c02041d42e600606c20765075801d10000580c42103a0841e43ca2403594110b41000700e09001041c003281c0c000c406d0a014010354025075507030004041425a400c01604038007030b07004090008040010082c02690740140404c03c03038a40c16015078811003100d100c0d44036400c5502c50403c5070b00c089076183d07007044540c0041103402c1c000d90882c0c5550341c0f2400103103003610034078050081c6c84404108482e0380341040c0884e243c2c03003400288400400040f0700040b03800d980040c04200c0c01a000700d0404242510700c0302d0341401500003610801442c20141c0c0e00c00b00c0c240c403e40140384 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 112833534 1250 112832284 112832297
    0x309140111070807171621050d0e03010f0e03040519080a0308090d0807020604020120120c0f0601080a0605060109180203060112150905041b0312020c03030a080a0b21032205010906 79
    0x1820300041d0f0940541030742c044101c449c60a18420014246071491195a200f5420181c0320340240c1b450b405007090815558001d545801d203801c0402511022079041e640780c6894400e4005002e1400f84800000613000352101d50300c6103044441c43d401c1003071080c00d0206114070042404010ba0b40010a258042d40c203003420300d241100c2c0c505c1003841e9010754048101610426a0301170b500d00811003e000d98000103022103c1100e018410310380c84120034000c80c00c003a40000350640200f1843d801403038002d141030400c3c01c04262112403010034000a21a06403800c1c0d000000e209865034420070b6079641120010303007085000c100c50b40040c469842846403072a425196008907041c440c81c8501c000009038040c00501c5400d5036407500b07035007920140c0940405401009201d525030305000c02260f6074130030300750384100307055450b020418020100f0004058200090065654038101c0113a110400a480c0400079a11040301c0c056081c620031401e48010001d4100110130411642c0014022041d02c0b018240319 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 112834784 1250 112833534 112833569
    0x90c0f0c07050405090d0216031208071209200a0608010504020c0c030a0302010c11030c030a050c030d060b0c240703020715020d06030b0703020703091401110708071716 74
    0x118a0301c0380310b03004107074000d103010305200c1c0c00f282c00100000307242815000e13200071002440c0b411550690921000e440c002482040280c40e078440c00c4010752028150900e41040d980807070b00b10049480c518001c954840780548070f61011104029900b2002004480300c03658207041003802000c0c0f00701881440d010325008a4a0340c100b150500600d03051480203401c46201c1d00903414000d02070050100b5590104040341a2640204030202c103d4031408a450000c5103000c0d280d0004031441e61024407044c003180010321405036544040e024890040c80c802c668952100c580240181c1004030340813000c5412036030505802c5004848011450f841240c9080060300d699560629150343c03400c121410708168070000d98550003104542c0100c1c1907038015240e070071140d5960364040c4c04038419103801070040b4219500c20020094040d005444004040c5003c18503404e62203d05803800c0b08a810404450f04600c40078006c242c03564484c404540180c400800b01c0c981208440d10030342c40240550941a4901541e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 112836034 1250 112834784 112834807
    0xf0509120a12020d050f0c0c0a030c110910060f030b030c04051302180f070e03030d0506011b050f100204061205060d150504050f0c0f06030a090b010b0414090c0f 71
    0x1928a1414102e0255940c80d0209203040080c002195101075412000c0c1c0801e695440101c240d40b584d20007000103044110441d14280d40908500c08112120450200002e0142d1584031502e4010856815410103090514002401101100701a0002c151521441c0300349603400140c1040c84943c00e403400100d82c1c881c0c0d0b48201c03a6803190000650880780a00c030070b403046003040c0601c038401c9203100804210f42d105e81008490140b101c049055040e070041c0700d80309806400c0e42c0065005072050400074038a02c00c130008107209405111060704c0c0780d0064a6000f941c5c2d14140f089904840180c001145081d0410402814800440c8030f06e003005544d031000200c9949883e000c0070003540d00052844c4080305580c4050018141c2160200c1d0140035003401b2552028001458011030b030001000e2400c0128000c0034001543c10091529030140e0f20398906501141c40d03a10103501038108213449555490510901c40d0020707070f08103e4a40114840000c000140c850642910f888a40301078540c4d54031a400d120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 112837284 1250 112836034 112836047
    0x231e060703080c1e0403050d09030305030103060c0306090c021b0609100807030e030f0c10050f0c0a020a08031e07020307032a060e010c0e06130605130f0303080106030f0509120a 78
    0x100700701c604011309049100d0b2104005042240d108000f1901d12042d201011904810180700c010080b400c244014000180380f6081541c00c5681460001429036070307a0843e0080e2901c400e044000345e00810540b40c80d0030006080e481c24940141e6003d40340c4940c100c08141c40785030210500040004440c04105407522030380204e08a5185402102e4440c0c83e0352130341010661204102c95030902c51555640c9004010340505071003031000c603840002e00d82e20051600000d1f8041b80a1004502448164000103400400034500803041105401440181c100714401d41046c040d005030300751350082c00303138030b001035070007a544c05c0e9840b0500f11440101c0360701c21029040c0350040f03d004100500f000f0406403011015401141d00c0c01a41d84c8a4038100b9050303080c82200d1080d214403865035001c0c42130911046000340c00824280320742c20102c280407030b550090300b0038500e8250005c80006800800400440c2c1e41401001301d07103200b01204001c1c3e030403c0075400396210098060440c164502284005105000d0038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 112838534 1250 112837284 112837297
    0x6070201030e24010f090e0c0402130506070803010f0e040c1a0d020a0f03150b030402040903140705010c0f08070c02010c020109090f0506040c08010810020c010204231e060703080c 79
    0xb4190000207400c545400000f4240100c1e41c80304050300740020414041c5c000c80810091640c0640303201e41c0c4a10034440a035101c0c0c204071404803203e030000600390322140d0090002c0d038041c007121900c950400c8444074005007164132441a12100e00144000f1408960725203049071405255545007524203040300d0a20700030344564964170f078404285642415084003900802c0d80e44c0380d404021164802400b143d56a90324014244400070900000300142016401401c3d01406400c0035a000c0711846954280c6621900b02281c403070b5110000508001d820000b04c1e10506100e00340500d00f440e01000050003604011070180c100042000090156405250000080d040b6000184040c06032405c0180c090170055074a580928030f41300c0c2c542c140030f02c2402e44a0681d100f610103401c102c0490342404c0041d420007a07842c407003035500b0000011064101d00c504c0445000c0039100b01c0005a4010070000c0c00a40780d2001c0d40c81005040c007100321a1b80700f00445524a40c1418440c0203500c0b0020000321901420 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 112839784 1250 112838534 112838563
    0x313060b0409050d0306170d0e0604050312130e06100e0103090212011a0d052e1406011206050906010507060608060403090302090106090e131e0309050f06070206070201030e 76
    0x414006100b0f0229024070055025202408010341c1ca1a489403260682d8031848203d411041d080d42205200d40b85801100e44018a007a04164030342c0006402c080000c0340350654480006541d007100102030400c58010540040007580d240b8212000c00e828000710085070040242419025003168000d038460815650052b01c0b13400e24500c0c20713000038000d005c81d1000c0c08286480701181c8520b40b90501c0c1a444099111020f0006400d441040c01d403401e081001035401000b90882402c1c01d10124407400c10314840d02c0c40890141c0c10682d00140c0313401454a400049103003461000d0001707031030f18481d10350004003c2c81d04541c0d0315620709007a0b00410301508400102c0c01010280400d141e401141c0c54140ca008503000a400d0b40d86510507220020184515550719404800040740752060480c0900e2160180c081018107440b180d10040541402e0103003200400c00b00b04040c04141000010340d5800c1000380d85051501e0340d15000200980151f0380c00a04051f1160924180070000740406441031008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 112841034 1250 112839784 112839791
    0x40206120c0a0e030313030219030b0906011401030c090b0306040e0105090303090c010c0f0f020402450307030807021503040602031f031a0c0415050904200313060b04 73
    0x510601d10315076112020801c001040703004890300074980032044070340c080c41c80303001071070031a00d544e09004101400c110100003680c2c0e80480000800c01c001403c0c3e1064a455010306015814045012040c2903030102141c109450f0044004003035401c0407025045d603d0b008501a01d90b070314080064040c1030050b0510045500300801e00c00c00d4032001018600500078181607414801c0c180e00111680b200b4410003030000307018500d40d0030205005002021300c19001500240ca404240c0e080362105d203508609003001c80010108018001041030070491030b40c2c00441103100d08010040000b41d5503d501c1c00080c00403c40000c288007199680014100c116210842c01901c0785041e0800c00d00a400807151000c080030110411b45080c031050400800b503a51000c4510601c40380e0b10144240802c0080a542c4400801c03c004038074a14101002140c041381b640e02c15030b0390520101030000341d51200032400030b10700366844120b130950081010350340d11034034548510407010801d044c00c8024001401d1655003242c85c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 112842284 1250 112841034 112841041
    0x40318121109061503010b07151406090a110d0f0204051207061e200a0b0c07050115050109061b120804060c0c030f030902010c050601150215060f04020304020612 71
    0x418101c0400403400c01c44601c00302d56903000a01044804030303a007000038010100014082540d110b80900003190250501c00482c1d00180d4444003240c13a40303150402d80c0802d1204000f401d161071400c00d076001d800c0020510808928481d008103601814202441a0307844460110040c04035070b0554000709070080c094105407070541c070100c0e15108240107280000d100c0c034002a0040f02c1e400d48000101000369035a84441c0009007804070b03008041d1440300350034011301c60002d0100d200700300d10900030365404000540e108500c2c42d00900310341100c0300c03450302440707018010080b40c1e802501300c90480310f10381801e00315656181542100880f481c84003d0040044c41e046c01d81c0d90354862200c038851791207002c007001081100182034a40c064101f00c001d00066185901c407030542d105e9008201250b10605110110201c00d60741d003810000241c00041ca54203031000741054090f4104070030114940d0b030701504907030f40c02c251010036200200405850300441e0000003242c11522680308440700310010004000e0b0390308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 112843534 1250 112842284 112842293
    0x60702040609020c0706090303050a0302030a150f170106050f15040e09030703110309090a021b0312040308160903060908090910050109050103110304060f0b120307020118080604031812 81
    0x404c82040c0300c01138410010080340d503d01540c28a0290b90305074440782d0401c56a40c1048000e0760000f080140c10b251a00d0703c0d00c98144500681030043e00c1c94018240b0018206102e00035840039014502032a40e0400001b00704a40702c41c424001c0b25881903401e0480b0f403031400700341005442107600c0b1000c1529800201700160704040050720016101e0780c0c955628034040440b90781d40b8001d603111544d200c403160010446402c52a40108640c1680510100383c29801d00344260464108441c61140010800308000070982d110a401e40d001014034441454010300c0200203201150310300008010702e80ea4003500007400220001e0b1003244100806035005403400303000c07002a0707440c0d07486441c1c0441d8403440c01081541c003901400791411442402241941d84548902001d00704076103006418545da03074030442c0644ca89424010980d14800d00a40c1c0c1c50781d40340b000500180f1600d025113030300100f9820900c41c0040100b0350a8015415140021040c007881c00030060a1003942e11002581841020200810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 112844784 1250 112843534 112843537
    0x1903020106140a03120c05240f0901020a05030f0901020415020f0f0c0d110f0d0c080c1014090a0807080f0708030a09031b050406030b040b09120d090206070204060902 73
    0x441c0c0369410404030300c040c50b06001140b507030303804024540070b00050b20b01c0c002807003080c0d6100340d14007600807078186071071107185040d01c00c2030b410211648402c1c1742d08010355244440070542d009203181000b1860070304070510050041c0000f4014104010035400400e800306025010703203014000400850155030200c2001960390303210940303280d48502525022268141c80840c1c00da06545020306148903102c00c0380d550240c590503a0b0030465000d1030040405480343c941d4000c14494611840d01081002c0c00e0181c010328110b80f920003248203c440f008843d0640d94016810f541c5030100782112501c0d1004100011580000b0703410240b00e03440ba0b208005100600000c0e036120381162103007503510b49500c90041f940c903845894402c9006c112400c00810024040700d40914401e0091041840303450303251030000c5c0981c6c1056006449801c0786806010600c003410744403e401000600043c4021460910704640074050100c038040c841d569400d060b410b640300c14085400c0d01c2c2d4010000c0000503110200b00009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 112846034 1250 112844784 112844789
    0x301020a050c06070e0306130303020f030f010518090a021e100e0f01180e09071203021506010e150904020c01020f04030314070f15020c01020c07151404030f02031903020106 76
    0x10b038841c0c100428013403402525055900341e4040c0181001d030b40c030004810203c03100440200e040550803c040e030300c410114406540154880e4501010651401d41003010156a982040704140030303400901c01031200015000d50b040d5070694403211554000c3d81442400700c000455283c210b03002c00d006040803940311101c954025001c481002032400103400440300040200c118000f545c40c07440c0305000d414041c1c0070340351303012503c0011103d0450b00c4400b078019007000c108003100036900401c01e074540d400c4403024299002c182842c24455101c2d40c02c0004001403a220b898180300302000800603d103880b950111a030282040d402503581e80740510380801168040d00c0241d0014400700002500b410030081254880c54110340700480c3c132810340e01e402401c0d11404100c421459401c10503000410310030f00103051450080000740071054540381050f40d0500c03400200714200000d0308034160301c610340c04003920140d03908501480e60f01031407807001c24a04041442d00c0c00c00708110f09010b2081550541205d4217 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 112847284 1250 112846034 112846057
    0x50d0f0c09020403030203030c07081e03060307060806011e02070801110309061303020d05030a0b130903081506041403030f040e010306060909112e02010608010e15130c050301020a05 80
    0xa80d641d94510320700481c0658000200160000c101041e038101c81240a014810b00400700c0c82d10f402e10030110800c890b17a440150380703c032410100800480d4542400b071f00c0010081810115903920f0810300003840b03440c034121218802e03090640c400c07414074070802480e005800040b008001030f016001c07200750560021100406c00d44034110009007414401c1505001d010b505400400681402403420303191a0401030440c900c041d52408128220390b21700b4040b0b11881b80b001000211b8140d182402406110020a4240c106c036000303030449007540311007080340c044822008c00030038034072000c1000030b00f10b10417044004492000401c0109401c0c1c0c1c6080c0e444e040700e106070f9003002060350f00c0754904c0a550741160042c0c8624040a000340d880e040540750004c000c0d0702500181600344083c07802c0b80ca04541c1240340c0006030340d41c136002c3c40651424811f03408003480d48001800009184008040c003500000d200200881a2a0b00002000082c1001c0805000014001d644900c04050300034602c0d017201d2080310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 112848534 1250 112847284 112847303
    0x51f0e04031218152c030c07090b01030c0c03080601120b19060801061809021605150106090e06060f0a02030c0109080d06120b07050f0f030a060e010f0f051009050d0f 73
    0x140c03d0b07085200b4207a5036103041d03460300780c2c1e8400071214800c0c1c90400d45c40745080780020046c2e0ba0252400380320004c044d2044c20b000240c060b190074001400c0710b04c5401ca41d024054202049000300e604850003540c030503000d1030030340007010840500002500c00c40d18035035080569040070190100e4844c90000685800b07942c0d140c856079844a046402403201880110440e0300011300b40401d918940060607070034811b6010303a840c2807041d40c030301c0d191407000c03036080340e0300d103600d034014420541d010041c6001031403209600c40450074a01c001503080d110f00030403401d16410020724420418002d0003901c400c81003800007005104128240360380035030300c00384c0c6001c511441e10700045041d4586d0400c0003a07440d045141c6070a15900e0312021b6800b80d010b511101e0301e40005021244002600c400110701c203e8820102007545071508840b8007a203941a00840c00c100031000c2d051101d000000303d0701086903011a06003403607068a00080d00c8020098010640140002a445040c04541c40c83c600340b4922500001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 112849784 1250 112848534 112848563
    0x90f01200406050d0b060a030603050607050f1b010e030418050a02030c0901080c0432030c011209080f07050c0111070612021c02190201051f0e04031218 67
    0x5140c00c0c0900554802840800d200900c1030700e102d41e000d03010814141c440000d020000380c2c002007a94002e080120000390729140103004014080c042c1c1500082c0a0800700e007030503060046100b042c081c13003552151a42d810440451410801d41054001e070200b03005907542d40380c48840081031001c0c3d0040109445007441c0c0032680034203441c4205c034401c005d003d01440c00c0c0148800119111000030b02140c8207404248804264168003c40c0d180300100009480b42e11260003040d00d0b0b001c108200c000c00d2194100039040403990b40c0003000300d100e0b050305801c0052040c00c07030300d02424076005c3c08104c2d9040d041e0200b12501005000a00c401610b4400d88035a0008212850155550217042c007804001400d06010390460002e02c0c1c000e010080701c501d42e995261103134018900c0c100c0e040200c020b100d5000d0054880000382d020b100c3c0c40d8028010a4003959038056094601514900c14400e00d940c44d42000002400e140c0b094900041c0d00c0c503122424802e10341a00c502c850f4141c00d044090f52809010001d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 112851034 1250 112849784 112849811
    0x405010602030307090e062d040501090b03070902070f020d0620220602030d0c14070309050a0e0105030307020108181b0a0905090616020a120507380703090b090f01 72
    0x6e1791140c14003c01b004c04040c440f29100c03681622005041c4156804a841001c5590f140d008640c082c03d114280054840700500c20503203000c400b0390001d20b050b441041201c01041803a0b00b4902d040303030117942c1c140c3c2c1c4e01c49910f000001072030850300d500c01070030582200b03c945051440c0104038000d90b250b4980c40c480a400c040c07040146081c0308040142e0700c1000100405051038020310f076110b505041c038003c079414508444090764800b41048001a0116005200e1840c00a6000020300060356211507558100b00c0801c0d50b070300c20018068144a016400600c42c00e0641c11071072540c95900081d14058424040d0608191440ca100b46100c0c02d80c440c3d006c154a9030901c1000e118030306a00080c010703912840100c80503825440c19240031401144040d1020441d1880840d0084802e07681d4981d9030340d0f8a04100111111001445104103200d41d10303002100810403402e101c40c8155800050030341c031006029801041d0801000b41000f0310a01008208039020600100003081c6030001e00044d0302d000308 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 112852284 1250 112851034 112851059
    0x14010903090f09140f060f180124020a08130302040e0703050606040e070302040b1c120201050604021c0f0204081014070f020a110d06140405100e030a0c020f040501060203030709 78
    0x103a004c40c0b036100c00080221000751207a50300544040d0240c00303114000b8002c14203061003412200403031a042c1e0b0040040b220110103100e2494102d02425115075100c40d0b00940310040c0300009040301401040d030b08079480d22036040000941d030040c0204115803c1c21078454854910707101c00c2d02c842c0214400180b150a017405291007003003514018002c040c0c1558204001458070114041d000090a0100c44d445039142900c16500e43c054500311184480201000b030079100d005003006d00660050184200108600e030000504000611011600d544005440c00c000c0c09964003542142c401e240601c1100451640181c03002c074000408148541d5404130282d4000ca000c010020042e803118000401041c03102076026104500104031407482e020f140c4556041c0d03204a40d80c034602c45800d009000401400300000307524a0038001e01803010004103040c2545034007030764080c80144028001e4410443d074076640076208681000303004003d2540c5423817000f543c94008a404c4030100f0544800031408050266 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 112853534 1250 112852284 112852301
    0x3050f0913090c0e0712050c040302060a0908010b0303090a030b060d12030c08060603060904032a0b0711010c02030d09060e011b090e040f0206090414090309011d03061314010903090f09 81
    0x841340d01b10700d10710000b11401008018079011544800b4000480140d85042c02414501705503960320000a003844074407400c44001101c0360303102e54801c0118a40e0f030f40f203000e00344003141e8100c8440b4405a8504020499246560170000c1c041e0840e0044070101c41e42540c012000b082c100d9862b0711090b40c906d01806118481990340715801518200001c0c006881500030400d40c0c42000c220002e007007075041d5020b0043c50a18021200e09407120200541d066004c03c0000980100100a109000340038800be9101c0c480d983c507540030716850303034400e4091012a41115924203000c40080140c1c0800e02d01c85030f4108107a10010380051003046001854610130b0f407045005d290400000d140010466082103100e621206c1c185420681f01c0d5070780c070511800502400c0c442c0d81c12002442e0350f130360080300040c00d400800150140a03210030030802c000b03450016509d0f910481c2503d200d1704880c4c0c02d041011400c94a03a01d48021503003030041c0c1c00308041c2c0c005c410350102c442410f8144032140e00c5450b008203450401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 112854784 1250 112853534 112853537
    0xe010c0f0309140a14090c0d09061b051908060f09011404050106090305060c0706060e090d0e0a030b0118090b0c07020f01090b070b06190b0304020a0f1203050f0913090c0e07 76
    0x160580350311b191812401da0403407a0592464a0201030480300c00c281d0f84000410355040e030390340000e4208074001080305034502045203041c038681300030500d07020702c2c00c66000d88080402200100061040c0c03500d6001d204003c600402d2500550380d40d40350701c40815414289640507034100000088c0607800b034120351041d13a0340803000e0f060782c0e40d80d40c084400a411007034007981c090303460701c02c00215802a00d452500076030b0a01c028103481101c405002e050740d004c20311302e18000c0f503820740104081101c5942050548100d484c50740c054043c0702d1440c5000e130840000c00ba0403007080c24140b0082100100c01441564400d07141040c2202c2007000645020b40f00748600380051100b000744c0c00008049410b01c43e40008020414140281408440c4880305025000a901601d0000503c41513190901c0c10500802c290710609000d5824076903100440d2014180040901501181baa600c01c0c1c0d20b24191500c140019000d0a201c020741106100030707100000c0705840c407080049000c2050445407a1a603c100181d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 112856034 1250 112854784 112854809
    0x1d010512030913020c030d06030f06050105150d020c10020c06040c080a08030126011518020708041703070609150e070e0601122310240e010c0f0309140a 67
    0x1c0d43d40406980000c102c0c00c4540000c00c21007801a40c00e04c604e102841c0203a80e4000e034043c00c4e1600804843c41a04010b00c607821080d030320301011400c1011070b02e0401d80c00a0142e1101603d01c2c041d0310f800104407011040074000305515500c84000a03000e4492409207401410301d994403100240c8842c901e06004c0c180050070401032000c2c20000c0c071404105500c1d113034403014038616258242d00b110319070032003502031654942040049814007104030151a440038021843d0001c10365820025110340d102da171084200089440303240f0101401035803000354101c4402d0002d28003d18113004001050312000340302d14a00300448060a4000480380c0035a0609110b1103d29254000151441c4521100e143c005607221060880041880304904010482c030020300c04030f50921070304220074071a85811038021054000c402d150309800860b0101032001c5107042080b0400c14020048510102202c00600010f50b943d240f0402c0542c0134412608840b2022448400300c205041000f120301c400f84194403d80b9807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 112857284 1250 112856034 112856059
    0x80f06031903020f01151418070309030c0b070804021219030e0d06020c0a02210601060e1c030804050105010602010911040e011806020c0d08060117101d0105120309 72
    0x41e40d100316200302c0c064011213852000c452001d43c00c1d0f904180702a06494180e0508001c00c00e541030303020310702010031a4609501c0e512102c001c00348100044c0140c0c10552134408400c02c1c9400303070108840301c0d50041858040c5191a980c094010241582c00b28011421900c0083c0c0203039001ca0b03c0511440b0210320b0340001c040c1d6440c00c8920f00040ca1140c1c0d032000742013410300700060a62000300540101c1d03402600a041c01401001540c02e141d0301250102c2801260600c003650300030a109054454a081a811410030b24000c030b9400b9010441c2c101c2d41c44440a401c100385600000c00310f2240b441040207108903a00c03050103d090781c0240078003c144e440e481c00d00011625103500000d180d4009400001001106400c0c449090f5940703041c15a81c0d154001101c69600c0c0050100c941400f4040c24030408a082010000300140e41c3c82c02c01d540b24a55903004641d200c490804c0000c0200402c0c0742154222070403482c0781000b82001e1141c00e1058945034400d000c3d0703207004801e40c1d041e10702c01401c000c810103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 112858534 1250 112857284 112857313
    0x1e060304020409020312070605160f1b0501060e091509011a011115010e0403030f0513020607111009080c090c0f0304030c0503030f0f060f032a060301080d080f0603 72
    0xd140036049030305d40103c440190071074141e04045c240701f900070080880c25041280c1c1010f0306004682d40c07007040002541c80240e440e07400900700e0369906006800114280f1140c180540100415003040c03000c1c441c011306001801c800020b1a401c280e2540d0310440c0e40c2d40f6251003a1f401c8a00a80556025209e020141c0120b58001e104080c449000e01082c0d910909900380440c2240d1400d0704020014441d01d0140304c145503061140c1c00c2c40500c124410403003400d1103106c0340700300300c40030304001d00c01c0c180090520b04002c4540001881c0590180510340c20004c03070003002e00385040d60300420105114441c241c20183c5480312046014080030891589042d400032500701042d40010320607400e001c80300c441140007503400c00046200781c0c3c1c0b01c5001c2d01d1b00d04107800080c0c405440500518420b410045140b034856a0200700c50340d02c40032020807034000e49a40e4000c403600b8000b05c141c0d41d0340210088000036020301e01054400d640d403000d42d18600c00b036030b9908200c1000c030015070303000d50103030310500a81e500c80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 112859784 1250 112858534 112858541
    0x210d050702041b0201050708090d08010b071506091e050f0414070b040311040b1206070807020c030f030702030c01090605090904020a03060c0e0a1505030a02031f0303020106051e0603040204 83
    0xe0002d007010038070140c00b41042d96006056521100141c1d99441040703106c1d0781c002c23641c2780c114001c034010303115100ba1608001d0201c04180036030b102c22540015810200a0651450902c0c0d100301d0809100c00c075540d500d540001c04074490b200c00360b075000016036443e41c0c540d44a86031142c1c2403140c1c400ca50352074035112081c4009512608402c1841107500110f621148100035000a500c548440c4c0d4105040724240801e860140c50030301e0040d91020841c604184000c1113480d4000078516140c586542c621004034500030002d4070381a0103014504c8200c44010000c4004e148490084e8200c44600140d140115403280c264894540010000d20a0400030b00e496002c0395006800240841c866a8a03501d4480c2110646111a008154032180c080ca140c103101010100400c0640d80c800d2007210406006021840b0080a94450560000002c1c41d00000310760340741000e00d076007011859059102d02d80a0300a2060780101d500c42c50410b040c44101086619084441c0600600b00a0540c1c99560901018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 112861034 1250 112859784 112859797
    0xa05040203070305030706201206040b04060914100b0c100c03020403120c17031302120a0c080d120b0d06020304051221010b0a170c0d050c0306210d05 66
    0x50301a0a00003c041102000545034290058800084981d003040e46043c8442c1c0c107c01d10100250144070071001858205c80072540103000751004201441c5200000c2e0040103a5003252800524100010780170502c1e1800ea03d1041e020492244500cbd501c0710110b0303d680c042e04107816102d600500d4444081c5000b9002011204c45a040242c2013a07282e82e80d021020f01c5a184c00e4000906840000c1c0500500556002205144000003841c41c01d104a00d2681400001006030080d4840707460f02c030620303d00704401381007903803c1900d0000d4a601c80c0d1129441d601d80e5851070000030340030350701d401681015110b408030b40c0c200103010540c1d0f12456502c0c10065000240140d60a0181815086800408500614407918074412450792030361510522000b440040e0010b5882c41428407211071010b40010106840d45488112581c40c0d0f42d0b8022010014460541018640d504240078405621840401765016070300c05c0b550380b001640ca09003402316010700c0310480c400ca035001c0d1804481481c0141c0c0140f12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 112862284 1250 112861034 112861039
    0x31209050613030e010c080d0908090402041202190602030a031e06060e0a06080c07020607050f0a050109060c0813060f0213081c090810020a050705060906090c0a06080a050402 77
    0x244000240c4616040040840d021510070206207200020103500c00c085404099090812003501c0d00e154440c044580500ca07041d103455541c0ba404081448030007010707903214000060040d90354a44544042e902d00c403403120f00300e01440d42140c8480105410031041d0342900c240d980194104034855074110050100003145400b102c3c0700300d41c810b44044460190740060501c9440c0e1484014060040c06245052644407404214050041c072033049a800104d0302020f80442e601da4a500450408904002480e00d00c501c4600c20468030314200101900510b0100740154030401c4103161000c42580d41400440d900040c2071800e154400005260740d006034001c1d0703080e082c01410004241000008040035401003000ca07481ba2404241840050303401040342281403600c0c00255107403c4405d40d0350f0016a070f400740c4580d008151100b1132442201612203541c2c100c0b04036446420302c8901581c03503030790990300c000c1c1c180508000041c150034500c0303401c0103c03940f66a440040350b40da944004010704001d40b0403a03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 112863534 1250 112862284 112862291
    0x308130506150d0b130203060106050405010509061b06010f1401050a020d030c03180602070507080102040b040303110c060d0914010c0914060904050c0d0507020c0a0e06040906020f0a0e0f0d0312 85
    0x2000c5031000981300c1c0306044108074130051040c4d03401010710304113050740701c50108102004140703c566802026103010300425580b55440c0d811450b43c0e80800d00d000e460984484c860000000703004994891644203d9070042a401c041141c04401101d2030300c40e2030310031409a40200c081c4040c0314400c2d441000f90140a1138001400c1c44007030680760004807100400c3d1007840d0041242402d012081c41118002c00001c0c00841c40c01c2e150002c140d2045c0514400501071080724580f50030005018001c90004110041a40303a88440000c2507000810010f2400d44a095045682c10502c2105100d0003143c0d0100c2e4039155486450691a0258090b1924196030480400e04c03001030316859a005480c01611004080d1340c40e5002010103404030f80000f80361800315400042d080c081c1d903d554502000780e40b900c00c40080e2230ba95040115000c1c010300c0200901713140c03000070410403c02c001c0f0050101c0c817000f9661440703007158603000c06c002846d030440b1250b40841000031501c00a402409242234a29503a500132 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 112864784 1250 112863534 112863559
    0x1b0a06050301210b0c0706060f1415040b031003120206011404020d0207060f020a080f0f071b170915030405070b0705120a09050a09050f0106030209210a030813050615 73
    0x2e0313400d88800c1d24400c3c0d081002160704400c025141c096000a03188040d91520254034180101d0000c1440b40c4109000750611100341c01c0c80c00c260030494000e44040f4899a990b41000115048a901c00303200070340e200403296400f0364060b40b0202d0700a040761286401050726441c8401000002d40c0850b03c0b041440ba400c1255100242d010300a001158400c1000142c41d95000d05001e881031200903c9030300002e4a840401035020394502c1155049070603803400300e44000568141e403484d50443c20019002c981a12040e40286158100611102409403030209888170740d81c1b000895804162402090340d04501801d002f00701e80180a420750034001c004a071300c1e64540c50220729156011020400c0050b070840c400b4081414010740b00c0d0020801c609041003180b400c3c2a400300c0c0100306001d0081015000904010156a0301a855281c2a41e00c41d400d1590a001111655504840a421404242c05500181e40314a0000b004420140c1010240440e65980c911411040f845540029031040360104031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 112866034 1250 112864784 112864793
    0x3031107061404050f0f030a08100b072d0305120709050d060b09010b03060f280e01090e0c01020307080706060b070b2e120609050f1b0a0605030121 65
    0x1e070000b144003100b07034504a043c2030030003608002d40301121034032030350140c40c2d0803540c10350000440c0e2104109290110280e02e8100c41d0015828666214019514001c40c03a00c00b0300c0700d2000c080743d0340c2c02c42c40c5046606032034071300e00e10420114444c0c014002ca04140840304555640c8580c856000c103407803a000b4013181d05c3c0c40c00030705a08010781c03066030303121f68a6810f5140d40c100585418050011440c61324210300c0d00070000307a0039007150144036000790281c66030141441e004056568404030150b60031125207445482c90700301e58200b4030481d01d11038104038000d5500071000c91040c14541d010390281d4074040d465100d5940b50790085c0012118035a440100195043c03c08003e444624030030219000682040b00c0c17419203440040d00a4013013900b0615542d41504c10a07889001110742031640510b07030040c03500700362000706400c6038094200e0180301810000703400e01040c80d0000e0032000707030105030a4415000303005843e5682e002d0100450404c10041c481042108003054240c0002401d03001214070075542c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 112867284 1250 112866034 112866041
    0xd090614041203061e09020d06050306190b0907050f030c09030d0503070e010905032d030a0c0b0903030115080c19050315030102030408030c0f0712090504050916030303110706 77
    0x107007034401c0b15115025800e05a0b1502403000100100600d028001a21244900c50070107540304090b606d5a00099845016095400010003403d0080c103442c0c0c00d02d0300801010188103504039540c40d251616000306817510385211458042c1190360b40309030911040580c006915440a0054040140244849038103950104082001e0003055543c0070380b0380c04c2c41c1d03101911748a03c0c180304505000c44842c0a00c07241d200090762102d6181c5020310108511500558442c00c003412580908080c0000114120070382d400400740701401e40b00d50006043e680d00c0d801c81c680c42e8007080c012400102d1040c3d0880c621507114690098003c421a12883d01d8440898180940103060f040702001103035000c000c010108814540702e500e001001d900070f5203149800c4d41c94640c5440700425003200c3c00004100c4028140140055459095000500f03640926040c20007402c1622248030700c52040d420000051703481c64010035402500d00c04080021065411542c0c180c2c050000d401a9806901040c030920010420500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 112868534 1250 112867284 112867291
    0xb03041e1b12060e010515060d060306020f04050a080607020a0b04141501090506030109030203160311030a08012103020d140d0c0908010b0103020712030f0603020a080f060f0c0d090614 81
    0x200c0d6140c030000c41d00d0b080c804d65080061156042e4980020811100407242d00f200011400b1150310b969a41402403400040c04581c2001e01214800706035420200700000c0200103440c3c0c119514129150348400e002d60b9090201c44100050700901c07444400244041c400c150000d02c20784080007a8100d410804d0b00d81030105580075a21195a8010446041244501508107006500a00603041c0f5514080c1d584d01c01c001500b41040740741100fa10a051080405c440c41003c076900b07480e13640d004440c009003580028014040803d000c85c0200f0002a5011180015554150081c04e940b4003c840140d03605404100e0301d121144c8100300c1c2920015942c2704150b010300e416114103481c0350600582c1c40c07c4884081016050610400044011588000b00881c2054880c540400c44036400a20b140281009070300094105e81c030410082882403000c00c000e402001c0d40011a00c2990307400c104858001c20a980c2c12141000130013078a420252503800084c2210700400010601058a000d00035590070102d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 112869784 1250 112868534 112868549
    0x7060509061602030406090314031902060f0a06230409060612030806030f1c030605041104031e03050405040c02030720100201061421100b0a0b03041e1b 67
    0x20420099920060041603103484803d1009500b0203040c50006020340e051804040c0071030003440000c6155000c1001100d59883c0c0c103c032a807032900712001000c0e50382d003003d0b20840048144280002d980c10003034460003044034101d200c1a03c182100c5d18a01c1559010f81080355001615540c002010800342d003c0c2400070310540c0c00401412031a800c00034140c24029015501c070341c00c4494050032000000541e00849455444c00a140318041202a002000c4940c0500d030810b05007403900380100e07124000b50045078011060821800c1c0e0394003040907668000030300200030580c184024811400c042d40080301030303656401181e02c0c01503030703885001e25070000305078110311000a20380c4500542400840d0140130b0700180000d124131400c029400341e502c500e03020482d0140021590300172007001014410143c0c98080e0099070721102445650324060301d40381d250280680b00001c00041c07107410318411070340319580084007400140b0031305001e408a11182c0c0707015504542c049260200d8910307421214802030051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 112871034 1250 112869784 112869793
    0x80903091509030c0102060f0417040305062418010329010b040303110303041109061f030609230105040f0b061207020c0a0302090402091b0f04141c0602090607060509 73
    0x1041c00f050700e007650040700c0c1c3e8110b40007203050207200d104030141150040e51180381c09038000b125500c3d801103402160701c0a062413088005100925101d100800c120391000020180d4072421602844030030240031100360745c50001c040040020400c10841031900c1c040001d403a0020498030798a40c480304000f82c014801c8542c00090800405400c03052490210f40618080c50440c40c054681d020401035461000e4012f018410000d825580c80314080300013882000f103954200098400010024442d078043c0c101c00c145041282142420360440300440c00004118101d80c5030b08010034000a42207446142e01c00300d89848003072000395a480081d0a04200703041401c80c15140101009181c4546510b080c1e010303ca42c2807003030015132100242c0f03592294055035050708944900d05e079403880080c44813120010351804205081800c503810018011582c0700c2c19030343d14031402e0300304104403020071a141600c44140308000c1c81c001407044d0007038500c00c8001007045080001e9038541c10142d03002100c4c4010035401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 112872284 1250 112871034 112871047
    0x3030503060f0d02031002070204022502030c030106150516060203040b10090c0815031011091e01090510030f14180c030d0c0c0b070803160c020a060809030915 70
    0xd00301a210b4000004548090102c0b40310b801180d244c0460507840001d07590001100019074580d82c0486d640c85910070341c103a8254071126222040c08004500c02c07031080c000c092759801d0901d014002d4205440c1d01805100000d600030030240d899500039401b05254060701d00030380740810780301d1015603c242d0048034440c195182500451000502e0398005007c45407074a031a103082c0c19440b40c6596400703010510404051081100003a240a00041008038410b00b4000307201b138074420b550050004408280c41e0042d03001060580040c140801c00030541c0041c2030604100510b140000f4410030710072182c00e00086800e1117003241d070b0513581340528603000b081c40d49080c05000e00c0c512900c2001d42c4804c04c080d1040030200300000b0748501d1000019402c000d00c41034500148621004000000c1516002d140c2d80c406081c60039801c586c00403540b074031100c02d90500c02d4903000e0042269072225a07006040302c55081c20610142d07044000a000c400952005010b40071107601d0380c800c1d45052031000070100c1d480c0d94 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 112873534 1250 112872284 112872289
    0x31501020f0709061703040602070b0a1101090c05031b0913150533030a03050c070902030a05090f060705070303021c020d0f050a0204141221030901060e060315090111040303050306 79
    0x5c03140c17070800c00341d02c2048200401c0b81d011407090165a51004119034500480310100c0781210503484c943d008c0c0d4070300300040c4100300346011100e08980d0107030241c0e0b1b5548001c01c0080c106020102c400c80e040450036000404004088a00b0320340240b140400c2c841400206903014111001266000584801b03035100d0700d85210942802c2c280201d032000182c6c03540c444040032a488018031f10000b000d0000c0803030440c15800040c0a240c0241108010454480c40e04444001c01391000b9a0800810301501182ca00000c00c00301c1c03120300c0390320a51102d07407402103940e4044000754424181c0038101d1400010764411040c41d40020f0a200c291604085180b41c1c0014940046079406070541016074810402000070005850381c3c11100c410072900c11104c2101e902810b4205003070808401003035050012040725012041e409180100f060b03400800c42207403906040040325006898565040c3d21113429002910402040c00f039101103440c0003c10194081400110036030040d40007180443c001008001d03590 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 112874784 1250 112873534 112873559
    0x304030306060212030903090d11030a08130801050708040f021c030c0b22060e070b0406081902070f0b04020102070f080f01050f0103111c020a0306020a1112031501020f070906 77
    0x844c02e2201d191440c03d10028141c0e072446050041d5029004080c00b03c800e0024110b14240d14480c0a81900c800d20000d1400d48455408072075801300390117442902184a000500c0f819110b20015150742c450394a2381d46580095621040080380e00401510010f030070034aa540729160030603c04d841b102c4d0903140c5450104440e0100900c3c08082e450369085c840c0c0c6502d0b907610358280281d044580040c421810401769070034146180c202141105000500055040d403204a0b50b102d10300c010f000000f2520f100c0301e41c01c16172040f140040c002031051000400490072041c90320b90045d20500441312104e41d40e180368141140c0d15030048150707400c5a040c0c105500402e000341c1c0e50200c0c1c40c06a40f0029130541ea100184014402c0e2250700989910501d02d0440b181c850080d09060b400400381946650399107010b1020303600286040e000100c0c101c01100b509140050140101005034000e075003141e17900303014181c2095031030380b510f03046102c2c1c030f084140003220900104003d09030583c000f05031942042d1003200c26 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 112876034 1250 112874784 112874803
    0x2040303092301141b03031807080705030606220615020d0e0603161205090c1c02010c120c021201060e010f0b0307030b062107180506040504090201031103040303060602 74
    0x6034051408034450b10303a400b11210003681c41c010300a40d100e038540c031001e0b2140050030b14901824800002807260303424900c2031402100740320104a49000762110039494550240d4070a20f078040e401080810403a184c0100480d4400c1c0301005442c40092100c0c0c15407081e607015038042600e0852240580c0002035060141c8284e05050341002c4800e46a441d002c40c0c0c1c6480010249084003850f040008002031049580503465050240c0038016400c1c01504642c03038040e0201c0b100d100340814032043c41402542c0c0c40c1030120b550140c6424a1590240d2940c0061000701c01103441000324420310040180d84140340241c24191500000620304e0426140300d00000c010b0f0070080550b422030307504115910840040365400700c131178680401d9480b041400701ea09401100031000540721040746461420007010303000d61240302c0d541da4101c480046c1001f4100045114010240c011f02704000c280403508090304038002c01803041c9000a018005243d40c80820f81050b0b80480000303881d040308011041c1e04001290301e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 112877284 1250 112876034 112876079
    0x60f0c0305060d0c0315090507030302060709060921110307060309140102030c070602070c050907110601060e03100e0a081b060603010b0105030a0b0d06060807050406140d0b0414010204030309 84
    0x7000d10750340d22410041302940c4401019152480700c2007104620035046000c0d1181e01008507900c1c0d58492402a40b01d14045903194001584c40340f001403d207114001c00c1d41140c03042030100c101c03441003020100303080c9403020080c2c40d028401e0706e6a40e6613403001c105000052105503030024039120b0034900501c450b00032000e10662a070052080c84003140314102240d9140354410801039813854580340c40e403440b040b258403883c0d04c440460100002150048948403e05240760300f5a1860b0381c8548064030242c5076440c03069056402020404080c04090703114019406454086488002c1c03140c0d00c0d030003598010201800c00c201e40c800e820746104403c121494100c1811130091003208400300000b46640802072042460a07201d9184501903102d068101440640001c018000f09803917580003992060301e407095a000c1c6140150010b0300217886581e503000074200902420150282d504d404a4000024006880c07500d4510844405080c09100a00c01148641c41d246986483d01c1c25103142c0d0b08048000c0007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 112878534 1250 112877284 112877299
    0x10e01060e07120f090303050f0a090b13050111030103030201021903020405060d0c0c0210020c03071a0a0f051c0b01080606070507050907201605010504060905010302030c07060f0c030506 82
    0x100c803400d400e0180b0b521207200d181c07401001c0510282000038180508644c14414505541c070810701d40e054200c0e03880f0f140740e03942c3d6a4a648458100c40201c2e074000c0c5001e010034410401280c1d2001700e021600306c5983c045c800200d0521140c40c0d078520583c1c02070b41b0460240c1c0d40015815040c0c01c1d03404000080c900142070442c242850700003c20003034802c2a6000d41d10a540303044400c0718a01030344070b0000c00c98000d060303032001d814084400785d5500b004203041d0740b10f8450814006441d80c42544407424039082e4101031070400b41281d00584086402103102000d00c0002e002c80e909410f4901c1111106468001000c43e00c420038a0001d8081b80010b8025800380300c0400504011039400982d403022280c05441c5083c290b900d44008036100c1d615094051251038a40460300d04204002070746000d0034807180d02d003101150760740c001940c80c3d10491184001144684208010a43c0254003840e0301020034500d103840c00c5025034a070b90488012015414244d42c1d01d0441010a6a05104180d0300017010395144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 112879784 1250 112878534 112878539
    0x3060c0406090308070c080109060522050a02090a06031e0b0109090515040201051e18010203090109120c0e090f0106050f0f0f0a0b0301240203090d020f0312040f0305010e0106 77
    0x1400700c0c10b00e02000c0c0104400080300303410400110340c45002048030500800c0200000e00e41500589019900340d00d511710040103003401000e44451429100b40d0181c010140c02e41c00d036080c03000c110b0001700b040d2609a44d503000080451040117a800c0e0382c58110281d903409910b00d14102d034a544042c1c1141b104035290201040014000054031000400d1503a00c120042e0f8840c40102c030b00d40300c1d1068042d03d4100b0b80d03200110b0782d11314901600120350146001440351034594012030352070048008140c00a0b071041c030100200e84071110380c024468011480f0340401616800180041e250682d66445541d120300c4450902e81c80a200e4940905402c8409030224007090002618105070388110302e12801c480364070030156540c1c42d0248002071041204650700c07580e50310742901ca940d03601b40c00381400c80c6d102d2945411851010040b65001ca10041c805126182190203000903080c542000c1030305031290801a030083e00002e00540003e11890341d111000030b0561a100c0e0940700d0a0803a01c0303c5038140b8009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 112881034 1250 112879784 112879787
    0x80a0b0601050717180a09180f0f080a0503040209100602060c1c060e0412050301081902040b0406080f0c0103020414060f0403120f110d14160507080c03060c0406 71
    0x155030030250074a007054031000d043c10101048454000d0020f00920700240d01005018400c18500e410982205c00a01c01c07030b03031800c840b42942c1941c00e1f0282680074004002d4005072842121101080c004c1000c032511034001c0d551201c1550001000303d0110f10302100304805c62510068456000100764001d4000e1460940c1c0650358140c040c0c070b150100d66000c11010070401c0c25080307504e03011b030b41d050041c82169680c603001901d101d425102911441d2401c010407000030b01520842c0d040303440d500b00401850b030a00100410701c10100310126031041c0c4441049500f0303a1503009201c098840400a0256002c0c001d031140e140810003011641810300500c000c20002c03803054420080e1700000d41c2d0b1959185030f10303030800c181407003a500300815034808510045052036000d441c64100703010684903090300310401640103a46d601c40b10350304c100003044076140e0410501200050302101c640307021205c0c0790355429981d032400d06000303030070049072503006103605283c17441d04000c49500b040e0603c0724180741a051800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 112882284 1250 112881034 112881053
    0xf0604090b0a0e0c03030310060930030302040e0a0f060503010902060711030c0607030f03061706190b030a03020f0d031506140403080406080601180b0d05040c0b070503030f01080a 79
    0x3801d95155075a80f9984041402888070341d0403548001e090300e86c0c13450102031002002e2594001c0d03a0000d1801032313020070a481c658410400c80381c00c8005404a46060351101e6807041c8204100300d04150b02441b0000f038840c1140c0005000d10501d502c0484c2840321071180c1021034085900c128407aa05101136980547c481c07204407030000b6000781d02104c0800001000c02e2504c5a0030540c1604684000b03128400d040e030105513000421800d036010b001660343c0c1c0d40580d08262183c40e000507181c0020300419030006250040c501c401410801c081162948400084e06007a074108082d80980c10800341a10078400c10702044884440a00741002103032902c06040100010500950301132041d5101c1e0022400040400e0b20025544443c01e40d0391140c070b0305401407201c6420745406000c81c0c88009442e240311803203100d080540b424000143d080a2103030401201a10703000d4401d5503204100103010030034850000c028070485024500071a600d08188609010680c01640054200c0e040b031892280021007500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 112883534 1250 112882284 112882291
    0x1a090f09101811070f0b070c0c06030507090308040803040602101401060f0c050a032a15020f0405040e0a0c0e060102070504050a140106090f08120a0c050f0303010b030f0604090b 78
    0x620110b00d070355405070420000d04050750040f10301c440204202c02000480b01024400b00e10448282244d902d46400644100201510040c00141100760034012a07200381d11070360303000f1110300e070500e240e507a01c0c2c031080b0099025811182c02030304000740510070940c04115289980068030410402a00b00d0b0f0705070380400006009050070003100d0200d480740940328040c205040340d08101683c1644005290247c11407045000e05015101040408040c4ca00412043d11341c064118103105490f0002250b110000c3d44007840c415000c00040c840420141c0725403244180480403000141044061420507406082507907111826a40303003403040090716607006c1051412940c007900c0119954940a18490140844014440e400d100720700000a441ea48008104211002c01c00280c0d0f58680303441501c2d1f00c4040405525004d100100b01c11240d01740316100d8160641e000d00107584650b2401224107085074400e0b4881c055511001c02403040c1981c1c060130382c0d90040d404403020020307400266218807010b0f0303004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 112884784 1250 112883534 112883549
    0xa1a100503041a09060f0105060306030703060c14030c0c011b0c060f090609060c0e010c03090312090806100302032b140d02120f100f0b0c071a090f0910 67
    0xc004942082191503041200800c0c0f540742c1e080c6403610501c1199245000c071440481d810b80200005603a080c071404036409524041c000e040e030715096807108009060105040010400d014a0390002d00050202a5000d0340e003402c0b010356940d88410b405801c0d1844004000890351044040868240c0c00440c855201e5600c0700010646981150030360005003902040580304904040101c020409a0340c82030600b1b222603290003480d820940c004481d65000d03080c0082c080340c42c4410500c0414400b040c142c3c460702d52450410302d06512030150790305003074040e242c012000040c01d6081c1704514082c844041c480d001a000c40390000f11240c1030320441244020840244907059018841c0c450400741151201d0380418001d6540d01c981401441c80c5030000c40c0e0102c3c1020441001c1101403000105484c102d683e840040200c0a0410f58070510300d038049540700d03180344503001001900010446914009844640c4c1180c0c807100e89505000b911040c00545502c0b8031512002c104122036450560340aa03180c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 112886034 1250 112884784 112884787
    0x8030304120e04020d02070b0f09030d091b08070311010c110d03090305030c1b0a08030a18030b041103010e010b01051c060509040b0412080c0a03020a1b06050a1a1005 73
    0x301c4040c0c0d0b0240340c1c103500700e411900018035801180101c1d0001c06043d171044041000c15503407404400700091003621801d6036504100040f005048035600400650303400307541d83c0403102d1801098440105140da0025030f40e0b8002420070810300400701506801c204080c00c011010b000140d03039514401da10011105e200705c1c0125a06028075201e110182c1c003540d030204c100ca03524400a00749568844041d0481c0300851410904104103082c0a0300c40003c0f5801c0700021400e108110740b0075a21000c220741c00c40803c0418420000204003a02e564038051806454013065070b106207428103095a500711110105a03040c5401c0c1c0301c3e40e0b640b280c02c4800c07461410551200142c0d0414442015241a6100550028001d414081481464610103005038404c003504240e141800400340c800c02d4040700c003e43c180200b8004006018001e4005082c2d1000318540079100c10245045044427154005054030320300c2e03131001000100841c03486920401d4040001c003043c4030f0905c0f000990001c600d120b05408103d070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 112887284 1250 112886034 112886063
    0x60a12020d0b130501140105030706020f060a022206030218010f170c0403051606020f06010b040b03060406050d06090c080a050a1712090102090f061227030f0c0d080108030304 77
    0x1219400c4101d01c03541300d4002e10600715280a90b02c8404003c0c010b5038806e01462130009482400000c20040c0b8004c544081d0016542e142072510083d04490000c1e48401040e4407040c04030509d207a5000090f1081f0344005840d800b11034583d400a4540440c110305001e00145100c00c5241c00c984a881c1580c081604d15460f0341c1c4080141955000d9540020702e03a225001700003603c1c000078051141501c40b658200c0c0c0300c005078101c000765911800c1c0b04140d00748508100601280480c94029503200d1005000418040c2e95500414000001c4400541d05250f0b550424401c001800b80b0300002810344070010f100105c1c994031190b0f15401d03009401040c040e0170045054050401c00c05441d0000c10b042d41c03c100c6440e0080d03109002c0d41c092501e00d885100b03080d40340e980c6481e041c2c1c10b8402c3c410384c1003501d4901c1d0f50789250642c250243c0d40341d000c012a912000314104090304000421301040706520f00c1c1d0b00c0700326080c5031624080010140a003030103007940041c8807824000040c0d1f54001d41000b40c0801044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 112888534 1250 112887284 112887301
    0x60906020c0d0815010207030c0e0406180302150c040602070603091401060b0406120203070c2a0b040509100605091e0306010306090302150601090501030902060f0c06060a12020d0b 79
    0x400e001d400080d81c026180a105510381104003c1d1199404000c960000d01104004903182c41040c000280a50060704081c41001c0140c130040b584180300e044c000888841400d01c034113142c0d01040040340164029101ca41c04624a00101e80e00b155060300d206051a04010000c2d490b449140140400c050b40c40c0e05070001d0204aa00d0b107d0f0040e9484020064281c640d0f01800313203a07000340035403c0410a550141c1508900910861788500c0c2e4aa42d240540300113a07545845203900c08100a817490b13550a52410b4405141800d8001814017034100d6030f48a01e01000d03c8050762005000461103484c06404020701c94110044600c0903904560a11078500c2c7c58000e45080c01011503480d41602c9050004130400a0075408140c06e14040d4007150905510701c1c00342ca250400840703405000503550b1700100201d5000381c00140d4514401080e250400c0c2004400240030b421507101001107a1150044c41080e04001d0341c18400342c1010700b043e07076007840b058000c5050b1001d813020052542007104002400003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 112889784 1250 112888534 112888537
    0x302040905070503090f06011a030a0f0e100c090302151303060c020d08090c0f04110906030a0f0b03070b07020d020d02031905010b06040e010b09030f0f010905010c1b06090602 77
    0x8003480322040045050680004203280c20403204e04515209001c0c0308264036100051050480741d900074040e40500b615405a800c681000d007610085d1a101c800080011855000d01c1d00c02080b00c500420100c41e10b8898001036030000d105140602030303122020310140e280e0010320502c0c03c0c68185001c0c0c0e1800502c0030540080c41c640e201811030340c0341c415041c40c0b803940030039107401c1e490725540d078440030f40c6403802031a845803085c540c0ca9a1080800e100d610550519800026a4180c541811820703d0325032004600386903c11140340b050203a41c1d209041d180d106038810708441e002c0076402420402c0c18070548041c030f8840c043e0064851210000030b001190703a44481c0c2036110b503000c0c0940f1000c4898842c159940d501d072140407146035080c80001c05460800105940484014a0b0300035031b1640391202c540850741c0002d00654041c011320310000c2880b041000b8104086410200025200f085420054212044503170071104000b4006141c8581c6181c1841d00200755401000c00500c2140c03514105009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 112891034 1250 112889784 112889789
    0x301090213180f0f06050f010f0210090302031c05060d150f02070303020c07090e0a0b06030109050619050a060f0b0a02010917130e040b010e07122901030b0310020703030204 76
    0x16071680669000a00305150041e4443e00200c800a022440012a20009561442c06426000060241c180e5a15840f41c0009911880f090050340e950344500c60711001603506141081d070141e84001181c981141400345454200142c0441c1004a070900c20001084203c0d10b42c009001240d4200c102284a000b41d0711840c0da818020004664840d180d03d0058040c0d003000c2503c000c01e00494900150911403800750078a0b1440010141c0080d8010780d03101e040400000c0c103240d40665844041c4400507008000540c0550500c0340d1020465420410000a03603c1c000c1c4a500d0090802d90108241003100307480005443c04c0c480340300e0701c50b460300d00d08a00601d40c501d8068644080a05120199100c00c0c00810508802c2c1100100460701c8002c0c8200c18003094038000c0064007030740010010040c50342d100c142c01180e1460843c1280d82c4192008003514a49420341c400008080e8954540011040c0c100307000d04000c1c20f0030b010503085140002e0f16a2a18075001640720f0300002c0041c01c141c440d504031000b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 112892284 1250 112891034 112891049
    0x30b09070815010503010b1801050d0809040c031b0e1c0809090c04060e0618150d020307030b041b1e030b03070b0c150907050f0112090b070e0105040b0301090213 71
    0x2056512501d6100d400340b0030303c04c89001e946800c80200c10ba05014150020081003441250071691814052100c03138116514142c03030201c02070080700c1c81595680640214203206903800f03e10681002e20283e10000d0413108801803200c104000708040d1101c1e02d203840c140c03103201040c6d1020070752418503107014442e004945078403116940030011101880300207001502c00340e070740b048182d201c10400c0c0240727032048000145071080f111546c054140780088404036015100d80c0da40d81417480340032545007039030016074014000c2038407850020780074107181c41602c450320b44c5040c1402601c00c51820180928440c561801010140c1162950749580aa000040840c40150441d1031403580c0c1d810810f5550030034064001c15000700c120515440c9540428180540d1000b4040e0807251b00d07080130804951811260b090502c26143e042420200862140500d200d0040c2003c080c0e0340340440b00105000348002c3c0b2181400000c1c0401e1100d42000000d49065480c000c1005039160451284480609050303480340d00f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 112893534 1250 112892284 112892293
    0x915030605033f040506130f12060c031a280b0706050c0f0a0507020301090221010b030111090f030703020904080a021212060103050a1104060203180405010e01030b090708 75
    0xb40c19840151912150b8040400d05800441c9410f108009030400103040c184900c50a1005200070b15007a002014500c624406040c1a56519500508415411b80c40803a40101c000404424019203009944c0144003500d0200810190180d40390200c1c0001c209844c0075200584107000070a00a9581010140448110010321a0307642c10000d580da0000307a048134070718101408100100044010340e00c2c00c010051aaa003001c499480c1151030780c00244013a64559200c1501401580b142d11030030504441c0e0801e6968044406400c56003541c0e80a800140a0f80c50081c0f0102c0708010303602510712441080702c103001d000100308002403424006402c081d5000d281001031000b08181d1a00500540030310b5000d94840c1e841c5a200d1080c1401011074041e100e060320750010ba003642c03080c0d118640c4200c41c90400542502c243c00a4100d580040e00854096800043c03440880800a25444000d010445050110b5810100100395200040c40010b09403500600070942418050280307202520a14041341c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 112894784 1250 112893534 112893553
    0xf060f090a1d0f06071d0a06050406020c03070e0613020d02030705030601080f0c0307080702030c0a05010f0b0604050607030f0203120901060608011508070503090a020402030103050606010305090d091503060503 92
    0x9900070315040d0410030700302402982d8100e5404001c2182004208000c024041655903080142e40422012034103081800a0b60451200c0da561000d01c2c1e000742174160b03a00f64550b804e08001920f030101c900316407442680418401c00c00c0c2c42c4032900c603a43c010000c0d60780707007080c040342d91301500640940340c00200b00c1c0740040108100554044081c2d4800c0700c01343d0b5511410f0f1181c2c8030000503c1c00680b542d81d00710030300b040003c96041c0250161034200f05144112450f1a1002080c14100000030408603140c3c0d44492400b1608641d41c00340058080c421a20300e45400e24200005100c0e220308000101401440c20521003403d00038004e50346140c841c0c03a000d00452800c00101402480d10f4041c0c03d021405e1780c400071420f405030148011550a0325228129603403507455081d603094000401d14035a40c411041d441c00181c440c0d0003e940214412070042c003090030100b00240075103000405400041c1d200c82403450260341e104000c582102c0001010140c1110742503022405801c081d00051342522071461107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 112896034 1250 112894784 112894801
    0x209060c0102030408070c0e0c12071119061a0a050d17030408120c090d0605180102070515070e1003200301080c04053303030d060602060412050301030b0f060f09 71
    0x181101b92107106007010f100d1310b58036801d89845098a0072002c071203040c4090011050007118198102c1d0007070614000e00e10040da101850f095445080c1c102c94500c00030703d48200103444c080e004030380e0302c404003001480c4d60500c00b241c1a0a0300c1d2260620035090581400140f20340301c107402228440e20700410341c6e20300d864145004641d10480c40c01c00e001c1c108100099200e400c000a489070b41000501e0061154628bc80380d001800d03003d40410750b460503043e08080c0848091008146179440b800140c08007ca02051031043c104004018405100c0e81c0301007889140e132804104540811207040000c0c1030b600003811a0b6080001e00c10595003144008004905200d000458030001d1008440910103640c401c40070f2008078448880700e01940c40003400d031580c480b2980c40e0785c0d84246e4000c6c040300d040c000300951310801e545113503000740d016030020b400b8013091004800c40b40361301d0165400c000f8a1545160f9602071081c0380248000041040100411890b6840004416070b1030001007000d8078070708240c1d06 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 112897284 1250 112896034 112896037
    0x22060503030a021c050a0507020d02010e09191506020601180204030f0f20030c0d03020a33020301030305040b070204090c06020d0905030a050715120e0c01080c0c060a0209060c0102030408 82
    0x4210b450b03184103138581610303d1154084644030304c0e080d40d92500303140c0e07554240201031402180803414041410552901a20f44002c0988281000300c8001081424620300d081250402c2150342d0303600c401c0303000503c0703001c4c0c000908504449209490901c22001d10201000031701980c0c0004181085014902c400d000c0300d230710381206140c0255011840c902c0c3c400c80c0340c4c00e07102203504c4164241c0c1189080c0d141907e0700e0110280114028010f49102180c903603149800300383c80d109404001200320080c68070080c2c181801068000d62100308610319410360310041c2850141c1d2280003000b08001a02c1021900e668000380c0440b076101c42107203000c80d10b6000c003a4036610311001010024281c803100103560702e00041e150300e0741c58114000d403100d01d06009510f030407800020806000c0c02460000c10304200342e80e00c0f814611008840c080c20291015031300040072150081e090806201082c0710301501c03000003050f402d400850295005a5445601c80403520a00500d8002d07101548048100424081c50f2070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 112898534 1250 112897284 112897303
    0x3030201022104030c0b0c07021201050103030e090c090925020c01080702011e02130e0903070b06090402030d0e2701261509011103190f0b22060503030a02 68
    0xc9409001d840301d8400c040c0b05070750846019000508208040d004200d211401d11303004240c03d03181c1450001c0f29000b183c07005905d11150b10715a991070004000b41540044610401d05044455202d40d05040745040440e02030401c2140c420704483d4080744a10301c00d01c03007641c403804140c00b041c80300316940b0038041c0d12001550b41c110f0108401c0300014100d280b0610030743c840004a9070010500050a41e034010094008449146039406c01100100d0203210851915110f505480d009581d5403000e441c0c4020701c1c050140c6102d00802d52a400c0c400141e0300130582168001d100d2810b89600740803100001c0102d86482015002090703002c0c0d102885014500c61b00d4140c6141d907041030f60702d14010154211141d40c20b0795110f52074010b84032416020072035460198001180100200f02c0c41d10901c4000002e40c81a01c03031f20b41e0000400f4003128020f00900842c4111034000800f081100040c0c00860055407444281982c4014a0412905034852039448407018180180449442c0c89020070060355441d50310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 112899784 1250 112898534 112898557
    0x7020307060614030d031a04061514030f0f041109010906050102070e040507050d05010608060a020d0b0a080705040f0e0111030612030a0c0f02030118030302040512070e0601051b070303020102 84
    0x1c000c103c1c0700c0481145092402c001c0c2c000c0800b0030b804101100200f40100c030700d1040017900407180446650354080c500203089804e003200f01030344040f80094200c0f80c40c07c0120510f05030520402c40d4080d41c0c108000d41c8040800e1000c0240d984070b1034030341c034403040807098a03a2003a01e0a00114080826600c003806880081e002c4030640c2e61111145846100100e900416542c4951000e000904061403004200c51082001043d01070720744910505080c000c80d8042d0f00c1c0303940070411b030507503541c00e02840d06003540039141c3e00486070502000703039114107072801518001d540310030b0744550b03100396a4000100d20305808000c02c00717100349110f030b00c048e54030564000c0d00c644d82c041800c40301d10724040300b01d07400000141ca6a802c29140f5036a400c002640039042070380e055584810056400346040059551184280d0700169654103113020030120140c0c91a040b0070759407214000713026400340403402c5034200f07200342000c541381e003440c403a448820100750303403a1141806039071400010960150040d00b42e0801a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 112901034 1250 112899784 112899791
    0x8010c050c030306010f020a060501060518010e010c0602130b0d050405010b060301140d080f1b010c030903020606040504020a0503070b030a050105010c0b070f0320130e0717060102150702030706 85
    0x9010115054000d040015450b90010808980d46600851816901e45950700560b050950640c40e10406c88609070b01c102c0114200040c0203038403030034404d0f15440032102401c20280403024400001e0650070103c0e401440c607a400500508a0390072640c880c0300910100c11455030b00c41c0c080380000054081590121060341c2000c0300d540080c900f14040e0381c182c0c0d1409401009107401503081081c6080381141c1606c20740d10400800302d25031000b03002070045075043e0b80d500b03003850901c0c4031403801c4900b070748182406c1500d01000b440000390301144d41500702c80221008100e5458a0000078400b482c681d000310f030b1511a01800044582e11080514850060345100f04450f0380e8440040d90325010710134004140010080000c2c088074098407500035040d030b0070b00d000101000303a0240c0303080707003502e100b8004824000803454072055010815888081e000101502204d4100254040c00d600103c90641003da02c0b02c100255159108000d200a02d2207005081013650400b5803001e91240d000342800d031102802d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 112902284 1250 112901034 112901051
    0x203070b06180f130c17070b0c1b2b06050a050621070509010b07060509030a021f0e031201030212010c050f130f0303021c1107060c08090406030c0801 66
    0x40500801003440042e45a42c440e559803c1c801c806104401001381403005240c2c004000883d11980c0300c180640889441076010807a4802410f18040986c0c1c00009002c0041080406211000c01d045040d2082e07150401e00307200102001400d1080c0092850801e42c003044020b1108130720f10090b80c010b280c0aa00d041040c1e1302d5010b9448140e079030441d5403a80240001d855004000c000401900c06030001c40241e0342041e44400c0020070482d001c1c4d20100440c000842e02c001840300034812950003d0100c801140707071029160001e0346550400041c4e2041c9004003030340c2c9047c503546402c240500c90f82201a29a221107144e0440d01d040d02c00e000c103900680300004480351804c0148141600c402c4241c036814189140342d950852103500c2901c042d0030203102071900080c403080c80c1071090055842500688525201c03d03492100364412103003541704205100c1e0210421100c0401c1e094156607240c540076802034000d003403448482c41000000303030300289840c03c00014041144425000d86000703d00034802c540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 112903534 1250 112902284 112902289
    0x3010f060f0503040308061f020706021006030209060f0a0f180b0301020c0615031603140c01081b0703140307030b120304050117040c150c020a0626060f0607030203070b06 75
    0x107440c40310100c0864001c10106000c01d0054040c0e075800000280180d0691180da000c10400351011030281d030160f408080180325260701400003140e8001c0880303042042c6031440d0009416114042c0c003171f6009452512090002e0b445e0200034102804500f4100d507040356a0b4454607100c10800801d00c4005803500c01e400b016460180210b461680c013000052009895151900716074402d0301c0042940b40c800c2441d40d80761840b0200ba09070081d40192090009280003914290030642c0049500f030402401c40c041058400b8401d922070300300f0760062031a985620091809490302c0c501800c01701c41d425800710800dc41c0c1580354100b04035103001a140d5010340e0111284440d96400745004050219040742d41b4402007007501c1d51815031080c082e9005010030b69852220a0681d000344442c5c500040503a01460309500b03161019100605491401800c1014185544802c000c04600030804078510300c2d0100e98980d44040c4018050b4000401e015980d07441440d01030358aa0100030308849180d50f81c0c00082c0e461 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 112904784 1250 112903534 112903547
    0x30c1a0c0307120605101206090212070c052b120b1e0d020a061e020d170403021606050d050606030106050a050f0d180201030e0a1e03050c0f010203010f06 68
    0x410300d098900342151980c090a40e281991201e5886459603918000a00c950310850312000001268481200320310380340103100c0c15100540c10810505004010401051494801e510784c0600145081d03544080d50307103005820f0008034000c64034886411408101c10081c3c4550061032107070152100520058400c100794152901a0f100c1640b000c1c0c5955401c00e641c100400c00142480300402c0258600499400900320f00c01c0e82e00a0030002c3e4054070b14083d0200c15081c5071405100c68001800e40c080c103484018080c1c419054081d000406031408501010300811a80c0c01114050700c0c103020306926007200030559009542c00c070003091300704400318480741030280460b4141d5400303558003850031542110545d259132040c40d802c05040700410071006981030502c2040d0001004407008100e14180340001000d1b00d403104a0700259821800d0080000703080f00c003620b40001d1a00f40c603036403444131500301994103008008083c0403e0061040700d42a0303000650046043c0c0c4d640385058016076888200445e1003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 112906034 1250 112904784 112904791
    0x15030604110d0302030c07080105040516050607021e040c030b0f04050c0301060c03120509010b121f11040506070b0105030d05040e010b031b0c15011406040e07140304030c1a 76
    0x3a8095920302464609000e0002c08190780240101c0c2e140c20b541614940c600801c0c2d910000481c0d54842c14001001814007500303061074011245810354a05013030010310603102c0c0e48070082c861a10700c002030007810129a400422120000c01c1045261035044015000d4070340c2c0803000b803090078903014910b01494680700b80e6024404045d6100c0c2168204172099510010002090341480149003100110b41d1050296074400d2243c0000840c804503c0401d10224240c00001e40544d60054034140325184981480001c0403400c285002c540c0c040034048101c00c9100316003005800610010350340050044401c00a8100c60040e82161000c031380c2d0300310480300c41c040d500402e40c1a101d9503004000e580e1201e0091078000e0003104a11880720b00c80d00002e91940d10400521140d41c210002c0c405054020000c00e900410021080d0601182140002600d43c80b0301c9c0203c00001044a000c04c00d118400c0d1281010040c0c0300b400c007507590901c1c0c10f024100c2d03001003004a81c03104585040013040405590791602 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 112907284 1250 112906034 112906043
    0x305011d040f0f0516061805030316020a12060203100b03130f0204060e0703240614030405010213030f060b1906031a0303040605040603050105030f0307030f050f0301060815030604 79
    0xe07894603502c0b2800c010b034401003519081581007480c400304009004402d16025204031403040289000390162907104c01d284000c0f9002c1140404000740d031804001c03102c04066414004041d52000d10001c1c4090506800425040f1340f02d075108402c00c401980254000c3e883d8144100e8256a202c20590440c8411901b010030b0924003265440020070038001050110f100500c0400d1064071101240c9484d201281c4900c002a12032480501e541401100014164032505401608500b802c0000d0004a840141003d05c482c0c0000058280202035041c0c0e850105410640f01c2c14680d40e06006181501002d800c4d40c24503d4000059480c0c5480d844e130f0125801095440d001e41d07860b00402b80c0041c2002d1035000c2180a4400c2c1c1c5805a0b9424001071014220640343ca544076810490020215001601310034040e910109100c44c040d00c000013952640c039030508c0c01e04c03407542030010122090700036240c001c0c160150100011404940110b0113900c1650201d01803850410600300300341c2d8034441543d0103072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 112908534 1250 112907284 112907339
    0x20c190201021509010920040f090308180f120a08090102040e01030b07030e06160f05030105031507110a0303060302150316030c02030c16031a070806040b0a030819030501 75
    0x3d0192400b064182d10030101000001c00902daa1030718100301d9142d074070a03c2c440500d2201000c0300c2c54180f1070840001c8821804001d14405c81ea806414800080c18140807106504190303c81c1e0001048003550134044941542c01d00c1ca1140009209900201d070300c900403c080b400090000301051099400b112a03159910086900c0c68564035001e1b00c0c0540707440c040503120b0200e4500d0003004c00006000300324035088418681500d1400038000c44091001d0f01c00c1100c00c200411084e500010504251034151a000b9019260040c007130302e8210b101740c0304642c1400782d140e0004c20305816502201c100d078000d440800c51001000d200c40d5071131104551100070b17007100d00d40000f4207904c43e501001d038683d01d0340100d0f80341584501c0c1241c503001c0c52000c51b54001c2102401881040387c40742149a0307001ca803101c2da400d14144004003501d00b40c80100f0080c09295200004000f0340e5070751060800a607048028150b84120408000305020314907141100428200000040c002d02c0c12003030306c0781a402521101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 112909784 1250 112908534 112908553
    0x1e0509180a1106091e12031e2b061a07020607060b03010b04022d0c150702150108030c06060105040812030a0209060a02030406020c011701060807170901020c19020102 73
    0x394152103100120340c010105114880c01510f4000f000718040607071020f813112034445c1c001000b0794080c3c03140c4611000e400a00c104c451240b0710782c6a0540440c1c03200c0c0400c0c3c850b00310701810b0601242040c54070f8440d4541e1003c120716240e540d4008019a10410307854400341072a0b10722030b03255101d003100094000000700484004200c0c035502200f10340000400200b06407040c600010240d030022040000c0c15540d03642c40e440410411400000c144021036909414280352220740c644030324212048105110885002402e0a403084c0548405264641001803440d612005046c1d500c0d0401c06499116108002c04607250790b0054083e202241d05039401480001e0803808140510b801c098103840e040da800f409926081d03544c1d40c0c050700342c5081540c000e584551030325000a240180400005051050045200740c4101c0b40d0001181500c400f4141f028450f2210302080310b03414080f03904140001d14290921410442c1034004000660f0750004480140e900082d0b5070009a10303207030009001d40d1041c92003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 112911034 1250 112909784 112909793
    0x506150a0507060f050c09010905030606150a0c0812090c031609151a0c070b040b04151b0302010c090603020c06010e04050708250b070f030302090402041e0509180a 72
    0x600b52a0720400300403030103141c0102001c050f142e050f0f9131914245004500c1d1081c0c0d5902c03005c05e0f80140011002400a410044040f03000c1810307040c181c400a00000405521040c018000e0105044d840011030756243d11b03234541d05d02685820790b12241d150081380d40c0228189030010741c0060841d0980032801c280d518000307416008000001480c9004014103000080d4030028541c52003240c80640c201c0c5039203103c81100d50b418803030160072001c552402480103000c1004c2c0c1c0c0381035409136044c1d100c680290030410b4000740c0d201e95090f00340401240d01c000d01031f401c01d0743c190043c44220300d15460b00c40403541c031203c05500341d0240c4a00c103407203540034030010804076a10104880e0028094025035000700e8907a02498107005d81ca0503400c2c001e00002590080d5480c000c00d03510003c000840080e41032001d50342e40c8104036420480007508264011508410791340e900ea040303c0c01001d14111460b040559141c5840000400703100700c2c2d100d00c0510000645500b03185100b0080c2081c054040c081c3c840243d0794 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 112912284 1250 112911034 112911037
    0x1416080d0e1b04051f0e09070f060c030f03020d0510030c12021305041a0103110a14060316090906080c03010c0c0507181d060406060f0501020309131814010506150a05 73
    0xc0003d03a07074071800385601c04000e03c0c5c18240030700031a255100b011725044010303d181006550003d440e54404003410000300d58407489103050305a261600d08100070780608100c010340a1850b01c1600545840103100d4030048001400301102d10030038401c906030303683d012014034000b60800040e42003401c0c0403505c01031111543c0300d158003921640b0160944402201440051700e0300341c1048030341c1900c3d04401c803c50f02c0d02c030080c4001817045001403280e01580e60301180142c080900310480860603018800d402c1c6000300d101d030f4098103200b070302040b2807a41c032207020b551154444c900d113000354649050a0380b170911034101080616001001005070f14648150007a99408400080000568800c410003005400402071054407202d0f0b40104076074240b90030003104542031640701c000b11014401d000c101598001c415104000c0d011991086407413168030246000d4035580784140100f00800c510b400820941c615984104400c82008002c0c69035158103000c0010903040039440301d6981403010003ea00c1c803540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 112913534 1250 112912284 112912291
    0xc071104090503030708100e040213050907080f0c012d140708190e031f0c02010b0a03060204170610030f21050c0d081005011416080d0e1b0405 63
    0x10310005018419444980c02c2d07810949401c0001100b060130711035401c0903450f00740042c00f584000740003182895800544501d0001e000301039003e4903080002c2c44028140f26100043c142c00c0c00359005100c44012260b1a4840c0414440c08140d05004c40c510071501085400803504100c0d00c800c030003500c104001e56400321407105001d1550420040d038000501c1810141c003084136aa40d01100d008043c4001034107003000441514002d03030111002d080b0b0b120500040388064032f00204001444004001c08031301521a1a407a2500200c000c1c000104008156005000710740c1038496900348070031450b0320a9129501541c00203000c049022040c008a601e0100002e9043d02c620340702042440d0400a4120a42c038000c410008640702140700d81310000700713100002e601c483c4d80c600f941c040e14116800703116580040c044c00d8100306030b088136460f4020420f82150580101d4400d203070f0303c0d03502038a081c02032031384000c40c0d42000504048074406070800000300440008032008d0081c100084c108148001800c004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 112914784 1250 112913534 112913539
    0x60115230f1c022b0c020a0209090705190f0501180501030b06090907031d0304060c1502040314010506150301051c0501060f090b180108100504060617010905060109050c0711 76
    0x107000b8a0490002c80c0f0040850b480542c9900c90480301c820200e00ea9101d400c6481c9205034100298540455404540313502c50585c100c0b0414240c0e220300031a00e02e41003c035080301c1c0d00000c52a0004a6407403800c00c29608591a081004074125100c0004464031002100f007060450728801c41031003150301942116407101b40240c01e40742460320074800640206030544e841000700b543d50703441506146401e20030311100031641d80218a0603160010003844a03042101c06008040000000301c0307100015012240155040003210b84449031000000f4020402616918819110300e59070108501184041e01e04a0700000c5c02500c030200c1c40d042e50b050110481c002100c195580e041c2c003260351110401050f001d09981c4100240f0103441c03400f408140c0c501c5c06a41400e84e040903004104441c0005280ca94101c010780c2c0100745a1100c0c504000503001c6904000d000324141d003036581140c20154041c50001e03014001300c4000340d07a142502c1d01201c9007620022400441045000f0206400e21085034039020301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 112916034 1250 112914784 112914817
    0x10e16020a030516060c0c030815030d03240609080705090c0904020703170709030c17030f0706020c0a03082d01060c0c120b04050d020714130b03060115230f 69
    0x959840742d040355903030b4546c240070410111440d024103500010180e4003000c0461201007801611001a5640e202692648101a00c0d82402c1c07000d50803601c003c4001e08400d41404c1105903c07400081c3c01c071603a6008586540c440c01200003a41d00d400c06072540501c118200e0103150103519014007010358019002541444100c1009111681d007107621244204583d0340c030144a942507161800c0d020100760b121492201c0c0c2481981d894900210403100d001100c0a00340d40d480c1039502e00000640243d0b2400b0285000e2080c41780281504006820b100c1c4280d0313a010358035140c0d04030301810303152001e040c100c1044034070310018440300b40240300c2c8803950b034041d403081903100c0e030780c1d0b030010801584540c000c48510742103500307000402c00c0801117201c403c006400074202c414100080100b1103880070306041d1082080c0408514140d807a940111310b20f0328040c081d60055030b1140c43e281d07c82c00b030184208000410020240300b45103c0311401c0c004083c8480b6a00c3e150210b0002d2001403070f0005910322464400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 112917284 1250 112916034 112916077
    0x31a0c07060e0c0d030305070e010302070b0601030207031e03060312082401050f1803010c2309040e010c030b010207090903090506030a1b0e19030807020910120506010e16020a0305 79
    0x503140c038100c4d800e41c07090343c000c40c0e1854402c0d401410640d03009086414540107005c2031001811028480381d10500030300c2c0c0143ca8180e10b0400b1100050202c50000407008807840101080340d0541200c401c0d64010112495519a590011214a54125406c9440308820044121500303201c09145120900500d0040e003042d0010307100e030706c060b801403903115500841c5822007805400c2c28042c500c07c8062034140740d0540404c20040c18180c4050103265485803500140e0030b5151780c5c45502190920800c040200045000a0005002072180050141c05131144400020311701020340104130205605541c3c14044900d44400d10141e5003001c1e0484500a4469804084a4180c1001c40102c2611562184140d560003400c1c408c48079490b00c49041c5801003a4802d00c0824243c0040b202c0e07495060301c9505556454581000381040c81c1c2e0401c20100304a0402c42061002c002810781c141c80310500008199103a403400800e244aa5916000c050780005000e10046805107014010114441321003104170103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 112918534 1250 112917284 112917289
    0xc0d2a02120f0106140a03030203040612020d02030f1b04060e0415030f050a03080109060506040512070801020d06081501140904050c09100602060f0903090d0203030d06030606031a0c07060e0c 84
    0x105500007150b00381e40d03d4000704400241014800c0e5665030958440d260709046840c020740741d1059004031801d01181011002e001101079048907100302030030700304545070300744400c10301c2d80361009844481400403420b40c042c02c010380c1700342101d0486105443d901b0200a8050900028281d0030103806104c107081d4000002143d10b00388280d5441d4030510242012029500d005484280e040e0085442580380c001c0078016034450b50116400c0e280c04030380b920400c0703840500940c42c0000300d03000400d40e940007003030028040310300c2d40126043d1400314007582c0052051600c40b014850092050301c2e01804165000401070900c103c0300c0750800d00840c295500010b4030408244840070070350f0036004000e603260342004426818050140c100d5090000d2503414108900c21a68074000e010340d1500c500304082c030f0394007156001c0048440c449060201845825500d0924034000d202d1032005560890920011054900400842c940b25514880304141045025200c0b000141207a4020607654803c00d100c40781d556 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 112919784 1250 112918534 112918543
    0x2252c04030306060206090109050a020d051c09140607050d03021309060e1602060402030607141e0915070b270a05060a060f030209040b061f050c0d2a0212 68
    0x641c000d03100850801d04c0c0800007031030b0070001042da6901c0d92408880400041d070210300801a90f404690f1040d80c101d890074841d0601a0060a000f400803560208200540d088038604044641c00342082c3c01540c8400140032042c41a401c00030990341109040200a5000754082e04215a0190301d042513941c9800064044680e03540103036004000882c04c00c02132203d13150310010102c20910207010307036044c030ba8082651210040d200e841403001c40c00d0786d15400081c501c103070b6412004801603100701d01c00000315140c056000300541801440081022280c0d13a000800315200140d00c00035880305e81d552020014071001d44a00c01e00302d440b51048155403001408c03c034074540b413401440504528101044980202c42c4a0f6001d0355038000f818001700701599a03000d82e02d9001e40c20400c034421076a11000050b216500000d0600071031034901c54100010381e4030a014202d0a00e141d000c589100c000104103449a12903100c1002484000e20110120303071906880000c103681c03001e009044070741300c40c0091300c0c1413 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 112921034 1250 112919784 112919791
    0x921170403030f0b10120902030c100c020a06020c01080103121e030b03060f0c0906070c0b1207030605030613140a17090102011116120504030804090501050102252c 72
    0x10303488051411160050307104d40410980101d0300d6103a100321030a400703000c0803002c00c8103000403555100c0c000150f403800c0c010285145001455810030f2070800c54050406c0f04290400d80c01201c4200340400e10500016050f125480b05840e0803105030300e16924032a010400c0c054240801004254081003030056844408646c001c0381c03070114a03918010103040c944103004250301c6071802803805001d110485a4101e503071500301600c1e5180d03240c2c42410f2100201000b54443d10001100103011144400ba80501a0040543e5902400603a03643c0c820165220001e44074103114191504a05000441104940e11030311906d409036045119a40c65000c0e08140020508406000c0003070700120540e07082c4140c12407480c0c1e0680c02410440769103610011500c6020000700340d0032154280c00c450501902c10f9800560344100d6540d56280c6584011001e48000e103c1d00e405403141440307482d40626203c080844003c2520012442545022201e040042000e403001c01c0303600750f1018141c14181c031402428070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 112922284 1250 112921034 112921037
    0xa060501091a03010603020a21080307021e060108060f07030e010e100608071202040e031b0304050a050306070f0e01050d060f0e0105090108030406210504030201090b0a0921170403 79
    0x90040d032024501800a0100d0082c600c2070349024014401130b42c030b9180400541d4240266807075800007501c81d4811121130290040c0012002100700078060350b002a4003a0646051000310002004c400251035481c3c41c02c1c00f40400a8000f14005a004105a0351183c4d000800f49000308500c00d55200890859010b582e00004036045180c00e00d65985050140798010700c1e44400072b2002c645030528035231099600c004000d1007030f0b8603103c00c43c0421504000351030541d844d40000c0352801000c16101a500ea01c50b100b00c031302400040b00c000906240100d0311520950341d585441e50420726410040300c4001c2465003040c144201071181804203001445680054003008801c240180e0800e60180036248050f884203120342c4192006103c040e8011040e24215443c90500d951280e403035841280220308060a6a5909480e101c200000e2550540210b510503001d09140350564444554a41c00d6500070034015120100004107000c02001503d400359091801b46401d082c04a4030000c114901d5600307990580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 112923534 1250 112922284 112922291
    0x605100903020321030604020a111b0907080903073203040317070804090e01061809020a050114041a040305120c070501090302090103060203041103030d020c100207031e020a06050109 80
    0x82103040030404124954070400021180c5401100031444512008045c640145c0e0040327110061140103840c000c90101490040e60001020388810190404080c1001c921403070201c0d01203404c2c240240d03daa40219080e0010310300c1e103000ca85902c03020048200d11a9042c0008010110b85d840404900c91012103001c40915516403540c00d201130403000e03040c41c1c0000d00c1c0341007040c100003030000001c580440d100303500c02141154142543c0c600421260380440c88101c1040320b011043d202542c000c21803035100302ca80300091921040111032107100e000a4801100d02000280101a00c0b01300350b600c000188452180313400e03100d945060415082a41c41201701c4404900d01e00315000c10301400016207801c0c0780490300d440c550f800241c0c0d03a81d0103202c0940070f69400030110381405041c1c003807042412006400c070303075413a80c0070b11545000390311848400d012405201050343c0c401c4d456000b00d413250741c0c0641c0d401d48410204004100c400d0405031307112042d40329003a8040001111802042e000b0005a05c000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 112924784 1250 112923534 112923539
    0x10c020318090f13050c09040c1805010506041e0815071e05070b06040b1905131a01030506191d012403200c0d260103080d06051009 58
    0xc040c1d5241200c140c4a981010108004405401601940100348201450540036942405401c04540005a036003081c80780040000b40a45000664100c030140c5401c0c0c1c05200782e29540360200c1da0203001d4268400010007003040a49c6102c0340c0c540240000012034042240e43d41c079102e00c3c0403c08403d980003d03072010200400b094200403050840340902d90110807414900e040280303940b15940300103000320351440109141c2c0c4c40340e40c0070003c00f15020f000b85c46c2c21100c4030350400c08000d04e880303101e02c0b031a000c21b03201590036618003c0e4024400046081d01d20030400e00015405810024400c1d0380005840e80b009032112000c07210342e001440e01e0203818000104200d08101c120805070000f440d4041508004442e6001400030301100c41d0540c50b00080840d00a070951800e501d0400615103c1400800d00154801c40441e880708062515203c0070440c641e45103104200c101d000fa0b000703403d0a4204010030105000c0e0008281c2090b031440009a0651a1000912507005a0818400049255009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 112926034 1250 112924784 112924807
    0x8060114030d0903050d0f0c050d020f0c0109140907030902060f0702040605011d0d0c080109080910020c13020307120207150b030c0d020d02060f03070210180201080703150503010c0203 81
    0x182d400d031140e14048002c1401c54a505556018484c89042040070b0704249459061180360710a5220354882c080e00c011846640000355100710580c1024068010300003032071615801840d90500302c030716070150314440000600400540c200300414900034117444100c0c0703500603621070300100410007454a00c00e40380e55003030061000325a05034000d80d06100100003561207402e540190076014440440b5154041c000700e19081d0100305e10341d0300442056081800c40010040b00c4000f4240340407042c2c4e10034030072802c030903412030740d5140c0841e4030303070308078600965400c07120843e038000350b0340866075091403103400da003815000d4203d0380108000ea070090000c0400c3d041245842c00780c808650001c80c0107081c603100090000c1c04101c04a80c0092142d20100130240454072118180c036031100408101a8492078600760183d01c0c0c14120400301102032410340341884a00844404a00c050740680d0f40310213903a111003064004007c4045110b40c40e110801002410b80e42c01d00640c400e844181c1c0c00b46803540c0d41001c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 112927284 1250 112926034 112926043
    0x9090118050903070b0f1003060218010e0a261c051c0b130905010b0402040807050a09020a02030306040b0d05060a020a0905040e060609040201051204052113030204020d060806011403 80
    0x10b5902d07a50070801040b00840c401a00f201e4010901d0b07040300345c450700ca0308410b120b25460303075200420060000c64018200d000021007a014000c0a07203a1003032880b499810422811043c0c010086c6052456015182480c0c41c400d504684c0002d00d8110340da409501042c038402c0380011071140380000c80c0096809075401c50304411412210361034005220100c1044001003c03400007a2040c56125500e000800600a00350003034044501d01920865075903403a141a103840b4001409a9400b46007581400034034000c1502c01c5032072086c5071764080c504546405080101602400803a00d40c03003444110603501190060142e079025800b80000140d072031001d40c102418111595202d184514580080e10784034074170102d601a4850002c6a045800c1d0780ca078801030b00c450190214001080d80658200030402c000000c40d44001c40d004800610040f81c0071024514038850003c8401c00b180b0355940800041c03d00c0e8010344242c420340a404075045850b070340000c3c60400260b120048400c0140b503118505d080911 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 112928534 1250 112927284 112927291
    0xa0f050f03030c04230a150504030f0c090509030c03030a090311030c070501080105040606140306060705070306050105011b020d0b0603030c010f050a060b0f040b0711120a02010f020c1c06020909011805 88
    0x14048000145e01400109112407603c944440c400c014039945107400c2c4a801114003440e48552410031201d454204020308502e075000e4401c1075880c0001003400e80b0303030000c183c03800f81244800640c80c40d07444098040141044410031014400d0898411007503080520161905040a0005248007441c082c001001303450103a0002c0c0c020744c581102400401c2d4006004203901a414555a40d26100c00d408034a076440f50395000307000381c001e03c0b04c040104030541e00002d040b1002640e809074110a402035a020716072440304002e502c001c80c28212030010b107050a846600210080940c0e04190042c054142542d10310000d160400ba40d405c00c00ca41d40c0001d100f01e9010f081040d0009013005042010240c09128500400005200100d001420001080b29a00455030050051000703031840705050350303440720b50500072030202d0700e2105403185041c0300143c80710800000803d0440ea096155952140d1700002010544407140c0801040d80c0a884500d4210300030b00c1060506504100301036041c400300c40024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 112929784 1250 112928534 112928579
    0x12020a0b0d0b090f0903070b060f100f03270f1407080f070b0703020705091b07030306061d03100c0203040801090503120702030f0304030e0d020312030a06060305090a0f050f03030c04 80
    0x40045c0100c02d40c0002c2665889503100c07000400d2a110200021452140245c440303900c00400d48a8641d8998808210310308904651814450400300f142450f406128a0340c081d001e1580c64030075400429040d0b5101d15505009108c01c1d4400c04007100c4842c107012503500704244c240c1c40303a590000c1380802000b03124010724186840505040039990300a44070796241c03040611039400d2070041200b01c0060b00c030303840300342c8920080c1c2c41e91a10f151401a0107091743d8415072002c210f00802d2119481c845401c200384000009000d04000e40d609441500200040c1440b030b021403205000201d0f600c80d09214820300b039400b640007541c031030b10f40301c42e460840340b00103200000b190814410031382d07051200c2c7c094a0304190305081100c420354050001c00c58242807042c02a5140c8903420340845185d01c1e0100840c040c41c81d00340c0c1848030580382c0340164242c1c0c000f070314a44286c3d030216000c100455140078641d10301c14895800d40e115031201014161a6070001c3e54002d124281c0040d0421080c44184801c0b041c502c0f01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 112931034 1250 112929784 112929811
    0x307080a142116110c09092407090b0901230903010213140109080a08030c19120b0607050c04181403220305030901300207051b0a12020a0b0d0b09 64
    0x4409000c1c0c0311650820b10501619500020950714801404600840c2c258903d54900e0544003000200ba20541178400c1408078007062b001060306001a421a002690103031200080c11100c0c605018243d02040c80300d82c1071036028400d84016680a0004258600083c601d130300c0070508080000c038a001c5d40000e120705000001008114485012030a42901900111215181e980d81802c0c0b8030307548100c0302d0808000500c10501502c0980000300c0c4840040035880812410032601c003805201d22074804c02038260340c4409115069481d00c0e8000703540d04203a015823560740710a40d0780c031a540c20310200031002e01a0400700b50b46041c1402192001c0c0408040301118040d1407440d243c0310749900c556800d150400010501c2c0040a41200f1a00b42c0e4070004080290204000303214408020342101008450500034070035030710110a0380d51641080c1000c010006091039240502180c4200d4003c04c00301d03040081c030000091028003480103420203d117049404249140704a040080d400001401d07030408519 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 112932284 1250 112931034 112931057
    0x3070b0a1508060103142b02060c040821070203120d23270607051b1507050c0114070e0301051608070e150712020f0307080a142116 58
    0x40050f035981180e030001d0001006d43e0f02d44030041d0134041d003030910000d40191158040108290707004074402402c903036803c0d100c0316100e0031110311141c403451007101d400c2d5000d00081007010440581480e0740c02d031854105071400500da03004c02d082c081c5100d40e8081080340403e060707100c100c079805601c5900c03034020704400d00402c41c1c0c0c072015441c0301c010f011076008025607030951300da00c0030264110545001c2c0d4000c85040d80392203180101b155200888880c03080c100c00608454440c0700003038038040c4048000302c904060340c1c0c20b04125559006030130100060b648a401000c01502d580c80710500500d90341d928003c26540c82c1c0d052509441c00640b0071001035084400043e00c559101a40c941c208906240012031a86900000b50f40c00c9512b100c3c000709560005183c408016150040520312460ae400703440898500161240d141c0c01a903201501c40e090410860181c5441034980c800d10182c0320003070074101840020350848207410280d50a01c46000c130700c107000111084091070040c1c104985860702d035015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 112933534 1250 112932284 112932299
    0x230a05070e0717010b22150f0203210106170f01170115090c020d0c0f0609060609020c07030302100b061605070e0f0103030f0c0218060102070803070b0a15 68
    0x184a1090114209108000c00c0c02a482540da641c0c070302c4804100320b5000c1d6142d900d17003005680203010302c240110b456480d012030352504d910214121000c006681c4090041858260b0b400004240100214001006410f2000c230f604600d51740c501d220070481d81029030400341c0240c100710b44650b448403985054000c00840082140d00c850543e07401019085182601c1010030f8090f02142c0710035400d4807002c0e50080b800c408190721038007841465900311003042c0c00804c41560101190a009400ca24807030f1808004583c6a1f0030500d0344501c030f40c3d40025841d69400c1e5040c2203800444c1158295004002b08006041e0b04001c0b8515640481d502001400041d41c005511031199203001540629294409014001d05129500060101903118201d510b000c0c00d01c803404900c240011004a00362410100c01a4811211003a00950250040d040311650341a14940d03008001e03e0203046104440000c90310160031300180c00094441c1d1044600390810380800c6054a04040b810310141c42107940810003003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 112934784 1250 112933534 112933543
    0x8100905010b09010f1211070c0b030108122208100e071401030f0209100c0c0b030106080406092102030d0b0405090a0f0c091a0102010c020a02210703060603230a05 72
    0x203e0090820340300c00000c01d40f043e00c40c400e04075550840a0328000008a40400f09402031452900c201e00100b405512005c280c0c00ca80802e014520240d0b20508510845100c8000244544407a6100072500c1c040e105814503046070003034000780e1080e0441c0c0744c4101010b01602911140806040140407003604000100810101e0341981604140c2c49094400200c1071650440d807420320080c140a15111039441c010300882d031070581c00c8601c45424480042d0007003040c1c00b500d0603510107545072a4252900c1e101e640280452560a60f109282c0500c031410640d2071018031001c0000c20f401442e1140504211034048803c19000580038074140410404603150115000c6c0c0301c180c2c4090108051480b40c100b070f4610440c1e913000000e103c2c0c60000c50515000030307801031301d84420b03099000f800004400b03001207840c0e100c2a40029044560941c0c2d5400c407507100040402041d11440848000a1313130f035202c17402660450340c01512410080e401020300c0c02ca80020400c08152058001c01c101c964659410344d48 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 112936034 1250 112934784 112934797
    0x1050714070606030804090c090f0303080423010c031a04060b0327010e010207060b030c0a0311010e030a110a0b03011208031308070605010503060106030905060a050601050702030d08100905010b 85
    0x146100241d04820007030707158440806180c2001c0d0322600d035901ca03110740006141c1c1c084818080740b00c0000004448060303c066070280c1c1d50660702c40000351a81c0d5914904a96201450401e074000b0703541c80c40441d4800d119809000710b8a58020a1486001c080c80e0b0a0394172040d00c49008a0a04101b440780b80260021203400058619103031201518000c0b1500e40d01001101c1113100d0b50801a000407000415005003240c0741c050360080242c2810380040540d1250344402058219034100f400300040340088081d01c0b00c051041c10103900408000001a0402000c0300701142c201540c0001003905080c920305450140c481d60b00e606246505114510859002d280b5000b40002400000a01d62030540d41c0001d03c050f81c440762094440350103103403410252000b4041e060080c03085c00c0c00040c40f14031038081c14584640100140002d5125000c2c15405010000c003400c0c1400b80401200006880403c44560403203403a40c1e60a445060076043d6811494080c2d128040140c10807005114850303290040310034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 112937284 1250 112936034 112936067
    0x21215060f1b07030c0e0708070e090711010b060a08100506030f040602070201020a02090901020a0f030203010b0f0315060c0d080106030212130c0305030a11100606080f0a110a09050111010507 84
    0xd01107000b11266140c000250801050980000e10000b0300c0685564168081d8000d80c86825066541c08405c940388004520540e500c4510900425065800b90980e094050400c074004112030841c0804a4490f503c1180c054000403003490401c400c0e241140900b030301a100403100d15140d0308010245541111000d00050201640000c000b0110780c000c10900900341d03405050030a0318a0401107043c001d420004801c00403130385a440d0440507511030b1003140c0c10303140050401824103010f1010213203540c000030300a0078000107d00800801c1e80d41c0700003800034050f00a0040864509443d0f008203001e506910130000d050042c0a00d40d8243d60f080d6005901c0f80c00c1c0f1280044141c0a0b00304407840707041a61020f0842d000000e541c9540e00c1c2d000c03210b04c0070701d081c180850b0a541411468882201c04a01c9404000750298000c103000c00d440f20f02079500070309444400b08003148417285480c901e610140b00d034408a16101d10030040d65070400b2035600f11080440003000302d031070070b007001034400c03000d800d072440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 112938534 1250 112937284 112937317
    0x1200703080c01141311030d1b060b040906020717030411040509010b1002030405030c0307050a06030b150a0905012d030e031c0e0f1209090406020706021215060f 71
    0x716448003d41c0411035030030241604450b9030629022401c5d403010848401c4e6134a5070300c40104a002c1c100060901091b041c60307920024034410143d4030484a242054048550b07e4640b5000d54007680c4a0140300c00c4180242d0006a0310303025454041c0d44082d181a105483d80300510401000c281f0034120190781c0041aa0040385c942d0300d500c09207005100817070a003075000b109804545a0203900001030b20640350190101d92113014020201541d60760a44940c030f42c0980c0c0312005001071403180e0071190b280c40025082d410030070005040860b0a030400740c070388400a1030340d1004002540c1d11240d50a4590044941c00780c00c028040500c4211115100c0c1d14002d141d03d23410100c0740c1240401c11952000d040c00b40d1154030081704a00304015280142d00b21649105031906003030211000300349071031100c41c0d000b603151801000320240007050000802c2503410b075a09004034008500a80010072407a2302002203041d0614000c90043d2200844410160044038144030403000cd104030021205030454414840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 112939784 1250 112938534 112938547
    0x6090b070804081509060114030604080d060f030803040605010b180d03140c060103050715020a031d150316030b0307060305060604080a050d0806030c1e0a030b13020120070308 77
    0x7801d8403450740116518440c42d92154410200705400030b0107006150140d030040d03665986002d110701411050181c1c941c00c2039001c100024112801084172016501010030901c4c3e50b46111000c41e03400764070694801400004000070000f040c820705014050b251070450820032060030401032549507050082c010100c00b8280b5082c980103102d83e8a1303e090f2001000d42d41c80a07850030341d484560030310040324140b045003804164680c0c044848582107603194014240020359440440c0c4d110102c102000000d0610807080c80d0720380318000f1829204600500140e664204400c034850441c001c0e50780107082500e0884c440103c2e035408604030080714007619000ca8240c44010000d18144a943c0c804038561107000c2284041020100c4c44071510061501d4a0b80550b40300c0702415100c100e40d1618540c03052217094801c035a14040302d00103503c01005070001001d25140c0d91000383d40e040607604a00203843c8401031808543e40031040440e903c200c3e0030505615015050340568030503141c04014803011010540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 112941034 1250 112939784 112939793
    0x114070204051f0b040e01051c080a170c040302030d08010f140f03010c08010315050c0708160b150a08030403080316020a0c0303050d0b0303120105091503060408090a06080106090b07 80
    0x8030580c407400140840290744da5150158895800b0340308104400b030a0000002c0c8500c0c0040a0f10070000240e003c40d40c485086690300b480e980e1229221805001c00d010b9060130018181214a00c0b44040d0b50700d49580b41d003580101807410070a40700d82401c01c4940341c01071200440e066071410458200c5000b144411565100040785000041401d40e0035605e46160080d01d141e00410643c101da004041d0241a20080c10300300003030b0340c0308540072040403500304110000206018018804140c15414180c00d103080e80d6194180c0b581c042d85d0b280d480503001e1400003030390300d00540742400800e503050082d45031074950741d1828010f010003000c0303141400c400400092254000d0104484559100b90045a002e0b145e15010f00280c00103403030041a90314010a001e03c5090000855007071851354641e0356001d0b0301e4103040004400d0010000711188094010b600c0c0380307450030401c4038000c0b80b0911030241c40c1c0000109211030b004055003c01c1c10415444010004590081c0c01e21099525034074030380340c1c0c0d8030307940c00d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 112942284 1250 112941034 112941061
    0x423060d02030a0f0308091c05071106190f0c02030c040b03120c011a0a0302030a0204050601050d0204080c04050a060609060c030306150c062004050f0f030105040b04060506011407020405 82
    0x20390180214111001009842c4044401d014400c0d00c070606180c40e00f10040d940d800c2346a40f511601120345000207440c0b8007074000381c5400d9100d000f801400da0175a0340465810342000050002014801c48044c0f82c0310b412000c0014000a03e1608084503005500000d54a00b87c66250902460b41c9500a15445c1c0b42406403664450429100c01d079240c0f12000c405000301403800304140e0602507000312079000c2c50031a22800440b40c0040051030414969001c000003024040c017114184403042004c03051080c0c8a0002d4001800d00c8006021090180000e10054a0703008064020040c81c103c0705010994110f00400f041c2d9003989460200d08100d450140c006042e150400d66400c000c850308032603e03680c400034503d02d0500c59982841080340a00001056142040344146440000d000500107410b02035105800501c0c010150001111880c01090845500b0350781a10041e60301420001805590300039680c0003a420704e058880030901c540c8150541c014054024480c0340c59802103003c080e800720 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 112943534 1250 112942284 112942309
    0xc12150b030702030c0106080a150c09030c060c030206010b0712050706090501062409150309020d0b09012a0f0f02150f09070e01151b0b0a090b06042306 67
    0x31a066407030600200c007a65a030421403a1031219820000041a00b01000c1200712081d035201e00c03542250420b41d20034202410030050141c00f0807080b5180000450120f1003900010000c0d4fc403441359011490400030305121058014080c0c48108000c0c070000031340300d400540c5040d505441c11549030201c81c5400701c06400501009000c560801c440410b84003000c042c140901300005540105540c0042800e98456541d40f2032030342d01c1c1136038100407141c841c060340100011a2006006602c11411980c5210701d01c0c0c400d8400603140ea5607890075070140703552010540020740800321240c0c0307030400004008152a410040c010100466602e0051980c0c1c020000c010010b4140380c00441ea07031a1400520034161001c5860030303114801c4540000c0c9010014403128140d980e001c080c1c81d205510500e080e1100444a0300503e40100742000c400b020420f81503070b040c040da040034408a1250a242800c648000d00600002d00c200e1070004400c00c102200030b1890002c6080020203185075079000000b8124500c00c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 112944784 1250 112943534 112943549
    0x13020325060203040312270e06010f080601082208030a0e010606050412030f0519080f06010903020d0b0403020f0d020705030705040501050d060e0705030703080912070608040f15020f0a02070503010c1215 89
    0x1f00070104030480104144e40c071524080c1d0f00c0c1a8144a501c40882c0c01c0d20058801c503004c1071a000114846031481c004496001c098003482802c0d80c141603075600306070f509c100c0d12000750941e540c11107030084034280070381002054280b0308582801e0800b100e944100422500040030301c4032000c10000040c1c011030903618080a589a15030307445080e08805170216108454202c009804140081c0071580148213900680f40c01801000351885696105001e4150142054080d03108035800d0700317140002003100c0c4286140b01e501806a6030b140000381407800c5070a4000c42c0c407690420740140b095071034904801450715080540860201c001200e034600f81050b0341c20080e050f010b0740c9004028030a100008040b443d4080d558200740c0145000300e2600c074100c034060741d00002d08801c0400d01162500c402c40c1101340c020340301282400c60801007601240d204540e200d1280c540450350001b0300f6014001c8000911054009104030f6003c0f01008082d02908003401010b41c1d80c89407090300301d41030900082c000c3c02c2e42 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 112946034 1250 112944784 112944857
    0xc06050a0318080702012a0605061207061e02010c17070e04020409140901050c090d110a0609080f16090e0307060906091e0f02040513020325060203040312 68
    0xc50030103d031554042c290980c00b0914001041c05107040202c5000760868000783c1441030f04200e075407100e0103070101030030030741d400001490300049074070341445400f00420306c0d600d03580101210101901c1c0480c038400041c1c2c0035a4540340d00c1901440d0424010259061040380c4403510390f560080035103503061900052a08035101150115034055941d209180c81c3c00d400060b01c00315941c030240c881c261082110f5129a10b00c062000c100c1508160a507914400d2060f04044035800710390010075034550441e401500090816142040b031002c0601c0901400b1080c4c10240451000383c0303511301080085403150302000303a518000507900d5007040c02628044ca81c031950600181044d800d0113006001610402e841c1d1040320f03100000c01c10a41c1d003106011943c04030550401c2d10003602000010b0100400002060714031126031070060390b0078840107903040c03d0314481e5211010049010010404207402802c195442008180041200c0e141c6641c0611481d203420110100e101c82100d8a10b102e032404561003168 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 112947284 1250 112946034 112946081
    0x20906130c0806031006180c05040b0f091005120609181b03010b0612060d020406050d120e0f152d0d1103010608041401020c0a1109070504030c06050a03 67
    0x2882507020f801514118102d540d0a024403030b043c4211402d910030369506030070600712074210b030255400907840a82c0e00e051250810360380350002852503110442d100c001100004003407800d80791803d41d2060280c850714085007071040d18201d80d002c98101a021500c0380203404001040780700410a00740700700c0c0008040c0d49802036424150340c000d07800f0301c0e8818030950030700002a00b82e04048060f00d200046a00000c040e51315540e00303007c01c4447c02e0505030b800039190317107010610ba100c0c00b1308550840d214042942555941c100002c0107a58803c055a120f60407100c1e940825907290394070058851108480e990f44ca02100d01c040c9030100b800e100034546007041000c0d00f20080004c4020b030200c0540141c0c02d01c40002101d80c2e40d4a11300c000d009074008680314202050200741c10b0054840444050400180341c1201d05107401c0c5001d10100c01210358110007010300d480c50030007400303203908217a26081090801c3e0070742d0384014204d0300c50b010310401c2080204d041e000861007078001d541c880f00c06014500c041714 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 112948534 1250 112947284 112947287
    0x90a0b120109020a050910090504030c12020a14030301050d020405060301060f17010516120b151605100b011715061c0b0a080705010c0201030f020d0203061e010507020906130c 77
    0x140c8040164404c01d400840000c0500b4140c03445072045484180450980d030400aa240003004054416000c01ca0314150120004d2520340b80c040a030709103600144010340983c0f03440c4403035415195031008150820b0004010a4882c4040c20f892264100da010400d0740e51100428010101c550000c82100000e01001441f045e207080805100c03201d2000078070881d6226610510fa071603c003028000003402101240d03c100c520742d8001c043c51030300140503050082c807180d0402d04680014071460680b5405115100c20042c00b0050300d651461000b4003448031000d408006800c214031010300c0300c2503229502c00180040e040300100d0415a400400168442400c165060381d238500881c008240c0701e00e8001c44c0398a0349001d00c80e08088484c440e004200882c180401190003040c41d94049040c1602c403888000785200900241600c4d0300d21030350050f242d181c0b0301d00f00182101034104010300003145051901441e40c2c0308040720040d40c0c0540d01040541c03a290003081040340c006441c3e1480c58900106074905a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 112949640 1106 112948534 112948541
    0x1204050d031b0c051c0504080f1c050c03040b03070804060507030506030a031202120103120e060f07020603060f0405070f0e18041101021f090204140c09090a0b1201 72
    0x10020220f03090181d07174820b05000301d00081400d01c880c00d070821070355180c541444014000b10084400c004180540c140d030880421500050301340c0d46417410800c840080c0b5030002c09030b41ea86070046000b041800143d030111407903030404001c200c071300e4401d000782030082400030050040d5540582c0c040d29001107541340c1080494007400059a811000401c80b4000c5001c1d0340304000c05040c4000003041c1a02410500e44645000c0c410450341010b40c0702610f50351a03060314607950384d445880001d80310300e030784500070b0382d12500b0201000300c0198040c00304000607034980c0755421150102d01c10411b10409134000c03100085d003a4000070b40452501d0500c001c0c03c08040c019280e500070508000d08000c0d088000b041c0300d494695100b1002c6003424400d8801000414450165500b03000400d2041c52140c55080e40c802c00b1043c000c5819840103901001e440c0e00020100700c1c07128600829107019 = true := by decide +kernel

theorem cover : BRFrame.Cov 112769784 112949640 := by
  have h0 := BRFrame.cov_init 112769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 112769784 ≤ n) (h2 : n < 112949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
