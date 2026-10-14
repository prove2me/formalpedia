-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3269
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:09:57.875421+00:00
-- url     : https://prove2.me/submissions/8fc98543-8886-4c50-a4d1-d479a65c7c80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 587769784 ≤ n < 587949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 587771034 1250 587769784 587769811
    0x4060b0a1206020c071e0f140a290f0a030e0c18070c0602120a05060a05030606060c0a140f0709140417070f0605191503140f01020f0a17 60
    0x1e603807081d010390040e4041d03503144c1c440c80b100001c080c041c4409211605001e2041c40310920b04201d40042404600e40000c03820041c29031100b81c4039101c5401640c101c0341c8503d41104110842e000d400d044807024008512415400305441c0382e00d0940200920184416840401c85446440b904070f44441c080740d0115070100181715031080c01040d007030000d40d1101c0380d2b10309110841169550503049801042d15200c0d0108010208000c0e42031b54400c890308440b04841400d00c3e9490000025600c4100a0001c1d00614020a411300709a00800041c80180c0c3d022003240a040c0e94244815036900030030710142c10611034640c0000e00e08405104425140b00d046c3c9183d16a6641c83e00c4d024212001032000d2002d6000c200801408501c800c0403064019104035004a0a0f082914080c040042c600f4501c284c0c182c41c240700c0344030066002c01c3c4801200d501006059080400c2c102c51401c0062503c505801c0354000140c80c6210414440240005501500d4070706c191f15102500121050b8211101d2590191 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 587772284 1250 587771034 587771069
    0x501090305060114030f01020c0c010f18180b1c1a01031502030606041e0e01081513031806050705060c161719030203060a08010b01140307030603080a0804060b0a 71
    0x4810102c0f800030700c40642140d800030001e03064542227900c08840b14211b0f03046114071032010340e84010005240c0c081e81c40c02d00414000d09081c0030007a0f40c1031142c1c804100a044004980b04d80c0e030381001c90822130041c00105141c0b202038030b882010010b1002240d990303034001000c5041074202c061b481d058a8015441d0040b114040a19500951000d44081d42c00601440001400480880c0742880b420b18550142d4569150040c003000490040e080784000d0382110614045d80d9401582041c0e01108054180a9005040c1025614128a01c40645801413407203004200349030080e0042990300d21810413600181c2c0c2d1a2030340e01c0e040c011400524004031117038040700003040c00d1702c42610250f009102001d26110345144003102080006200d100401c0d0040708004251600703036a14001000b22500a00110012000082050001c0e400401c8025400b00200e9035a40c03282d07020301c0103160311102c0c0a81c0c8648d000406842044111000c841c5503003407180846407070038140d8840c001c4440500d80d1186105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 587773534 1250 587772284 587772299
    0x8150d0b041a10030f02060d05010303031506050f180f0604080a1b050904020f011413180b090708040c080d0503090c010207061224031101080f010e01140d0f0c0f05010903050601 78
    0x2405645c240c0c0d000c081440103a4014a0301d2007414001c61280d180001d444280804d42d000407500e9520400a010701881a901081015400c42c0d1941c00c4030440008010740010010311203a0346501207d8025101081c0452080d100107410130780d00b8060981ca6490aa02c0c640c1a0100c4909001c1e10380c001591601050060400029664410030141030903412190182d6900206800c800340031020381d001410704000b2a00001100c01d04482100000c0c400c403c407540101d02d0611019205101304410103000600340702094005501504600d01541d9845c034154070300428075003083d11038201c940139030302c00b122082d800012000202d4180740c964540f031100201058000304514007042d40c4900c3d01171403c0654145680c0e80d00007a502c65030100186240c440e000400343c0d00010100d6991180180042c0080b4651034985811075116000c14800e0301010783c0451141107203400005d00001600804134208810342e12a1001c1d2880032003c480c001c2e82d0b80004440f88601440040c040e504100300620059 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 587774784 1250 587773534 587773553
    0x2106020f0a090b09060d020d0f15060f020609120702010908010e01020918070c060f0212180111030c030112080403050a03110c040b0f040b01110a080703090608011508150d0b041a1003 80
    0x15080e040001800c030010341446065030500c03480302e012b9040001d0280600ca4210485150070f464920040855241c036051180e03550f202074040c03515501010031382000710780c1305001e50005060380700020300c01e80302c1d50101e60b03000c0d400a0503071a02c6031442001850250102c903551921503802c030740d40c200c1040304640721400100403180072008060b40800040e210918650001406440d2008600c20010320815181e421075000407e00034640c1020024080d007010f8202c1520706540301c00d1110300c10001c1c01d140030541e51265034401020b600032000e007030342496009004003118800200076110116014010041140c80d40300e01594404090300e000c030098105540801c0030f01d40306040200c1003c0506294600e420320115080302c0c02c120004010301016800820340e4000c2c9000d0030010180c0d4101013407406e0681c2c40210040030040b4200c0081c44078034411320762031000d04002d0004107400d40141000d0f090315104031004d54881200441c0d13500500c0c80b00b100b05110303c0311680c4821401c0d08507038850a09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 587776034 1250 587774784 587774797
    0x9020303030f10050618030c01022a011707020609070e010b180f040e0303040615030c0e09120408030d05100f030b09070e070c0201031401030b012106020f0a090b09060d02 75
    0xf0005411000718850b114a0b0050598007802e030100c103200303401e05d0201460b0051403107125046411118806c400e01100e02c0003a8011103202404112040f90200100e54818140f0342023041c904a07001400215500490542d0044030458203540340241c55040122400c0020f21031007000b1030040125039840c11f4040c14074211050002c0000721200c4440002500f0385011107501c0a01da0000018002040403034071a503150030018840d000d0b485441c50700c452251928a01c2142d41220140c00041c3c1060420b1064042100030f0142840e2159111100c40350f403500508007000c0450301e0900420002d02a0307440c00002c0f902c40c03610400d800c904541e1100a0348502800d060303040d1180030f41c0410040c0004940034428901691501103050150000406407414522440b8000704020f0050000c40c1a0704001170640b10306411f000e000c14400c6204d00903001500764050710032031010035103a402000642c001c09030000c041d9941c003a2541c80fa03041002a1260140c9158044410450000040107035006001ca = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 587777284 1250 587776034 587776051
    0x10c0906030207410105070e090601020a020301060e090d02010623130501060302090a0b1e0a0c021203210106090306090c05043b060a0b190b0a1209020303030f 70
    0xe01250040daa00130482d410b0b0040307140c1003460038820020401c3c0f44000306103c40480c0284a64180800c1c09007494254600c003d015040c00400194640d008010071070b40c0369030240082040e1a0341d01603805030103205807481c108500440d401e10403014070500480050720250411080003010f070103482070140c0410788140b81c00c504a403003a80d161440c1485124000d0038151400750b0786d044000100018010941c205000304407042c0414140008a5414000303140b80c498081070f40c980b00c100081e28101c0c0e1400d0001d5001c0c4440031a0740c070300030f03010000d070100f602c2e200c0c0e0140218440f21043c01c502c9009000d201c0c00103400f4101040410030315040416898040c5881c0c1140302e03160b401103000d641188001c44507412842300074041c02c61800c40704264020031901c0d48014149421002c80d10740601a040045a80e05c400010146a07140015008415109641e103495135a54060f4014030b50000780c1240003040c2c01d01110442004140200034559500402444c50b55035205011100028050700154 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 587778534 1250 587777284 587777303
    0x903070506030703140c0c070e0c03190e0102040b0d05011a0f071b03080a0e0f010c020402090301240e0907060c03032c0f210f0a032c0c03010c0906030207 68
    0x105004030100c030711b40142c011101c41591480e44c100494644002584042c04d9401d280c004c01624041280989422611134450000000d84544c9001d0207840285141c01c0294070001d80001c003020820000c0102c0141050f00b805583e0b6600d540c01d8032842d10003a066810f02c1d0811540f0a8014440003d004a61144545094901010503c10380d140030359041201d18942c0081c5402c012504407400e088940e0045a0107aa28403d50b00001e00003101010000e025036004074260003030780c0e02900300c90000d0014403580508031405203440c1031130074807074458800110701034000714070140c60104e03800d01900c0040e12104500d5400390790481c0280303a000200d00380403440f10301070900035000d5503805802e803807840d00800c4200181d5006905202d42070140c481c12100c241d2400102c44000000e0312155500d200d0900d454030444417003a80a041119000da100e83c40c6200e508645c1851512034807140003488080340ca0900702401818204d403150004500400d118807010030500d4825001801c000303100d0751020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 587779784 1250 587778534 587778551
    0xb0415150602060a0501060509010c06021626160b061903051c0206010503100507051330051b0307030f050303220b0c09011418010e03030903070506030703 68
    0x10000c4918400640c95184206401042207a42c100150ba4000f410004104541d51502c0d5000d0024881c0301029414020a0005403040c014542e05642c5840b480c2000148103a10300d24015580310070b08170502a03015007201211400c8000d48003540c0000c0c48460801e2001d0704181c40d004400b04004085c150300c045425103118183e807011100400552041c0e00800b104051044415420301c0d298841004552141c17004001075074001601c00e2007080d46070000a2140c5440c601124030340f103100410321396046038a0000882c100e01810218507200031031074504025140700d050700b80302034090308003411a9005030104ca000e4025454035642100008049801a50b52075492141e0301c0c45003007003507840f41c002204000c00b641d511403401f82007889000e0f803590014420b80d982410644003804840d01450301054000c0710340d0203a040141105100f2084686a41c80d841126a01241d4078040f180010901688a5032a0070004140c0b0800380008028115032401c2800b48442500001d003004105600c0c3c242d503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 587781034 1250 587779784 587779823
    0xf0a06030609110a17100504210c0519020d12030b030a0c030c0602031c020f1315030b0f0d020909011401030b1b07030504150e1009140414040b04 64
    0x8032009580b003407001c040d01e400c00703c2c00c208000e050717a4000210651002e442c034140725400b250344901016203440000300c0d5100c905002d400d00f40c07190749240d8429041c0603580402500300520b840b056204100315079000c2641d0031080c0b000212040c009411106084407031000072003120f0792010074072040c54006000c94002000030719260360003100342d5051440d44d4042c0103206c1400702d402e015051a0000354a04054019042c44040503414403052850380407980503005200941103441c600d840d0201501c003d0380700d40140311a409206800d002081c502003030010036040142003040e02e00c80080a0b08010b4100c4d03003c2c004a54401003403886113550fa00c0c0103a081c112900d03031850182d40105120006480c0a0f90020b10113400700500a401c074a0034000300c40044d6020b02210192200d10400c044070082c140d105903181c0e030302d50142c20741c06404060500c58490788034201804503880d0508080f6050420300078081250803000f10035542e0424840020b0225013081c5805810501c15540c4100440390442c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 587782284 1250 587781034 587781041
    0x230402130905030a120501050306060616170d06080f01060303090b0c031312050d1b120507020d050327060d09080d0501080307060e0d020a17040803160303060b120f0a060306 76
    0x4c040000c200c0d907066203e1288510300c1014058070341a40200a14140040010418003901c5401420742110404c0b10042029802804444803105441a0340f100e0003c1d010101500450040665900c15015841034101d414011401169010307200d400546017400c480c09410390040d4081c448a02c401c201010030400b02c1140e05004014200303103500441c495103021030a204503132441c0410000b594101d418400600b11412001e10782c07207a070032001d1140d0541c00740c0f0035000d260b0020354090309507586502480800300c0140440d040030122012061032000350b0011200c0b00410007034110b0000e01652618060395801004124095203c4504002c0c404101c001910000d030012a581d0708003090040400030180900780c00101c11a02400c0c145896007802580d45142c401c0160040c80e040f0140300d5802c1504040f540900f1004082d2607580d18903003104e601624080320300700c0000307240c41400250001450260fa5000c2ca1801c1d007000380d5160b094a4403460300e00a007000e48066914040040041d00c10b20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 587783534 1250 587782284 587782297
    0x90a0902040f0806010b0f0304021f030b0415081506060403020607030905010e01140a23040608100f081e0304050a090b1305011203030f1803110123040213090503 71
    0x50015070740350308000b100341e114280c5a2118030158032200042c0120802c3d0303000d507841207940030f060f07130b0b125540e500000782544400c6182942a01c400c840d40d00035180d1603000304081e11400d032018000501605400c50100700c8501c80c222558000045008001d5400b0518a412400062040d0b00b015141e4000074003d5000410031000f003042d4420410803940c00c603112520030202400d0007520784004a00d1004148160244081044070707902052903009441c02c010400c0414100000ea01d07651030385800303062000291840000188400000510000015110810344002c48068506804e4056103113102e190311920801d00c0740014040450275031111118603009180040010500740c0f040e0041c0f0074814101c3c00b1807580385083c8001803089048408031001c40c3c82d0700d4640007030400c0508402000400c0c1030781441040007585051482455400a488004003c015000300700c1d005403409400e010602c20202c0703800f40408400003402516084c550702e45041603240012607a0080c941da56415944401e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 587784784 1250 587783534 587783549
    0xa0905041e1b1709011b021b0a0b0a03090c0e0a0b09090303070c032016140102010e06061c0203010f090b07050408070b22060201020c01060806090a080f0f030702030d1413030f05090a 80
    0x10b030088d50b840c07c203000c541c502d0030340c2e102a42600701048c80819201320304951040c140c40b0380b1250104a10f20f601c01c0020404502c4000c031070300300b07000f014010742001c0130028490041003000c00c1440d040841183c0c0140e039103460745518460a0b6070140d6808040c0304e801401e130b5010304244403110000b1702c401d101c600602c050780000341d402d144204d507915681ca42c00d18116071410001040c0c4d9400024551b802040c200c51090221042401d140e40011104130000d406500306643d03104212401c0d0050390801c0d1007002c0000c41642d4450045440b40924481c6100b5907002ca18100004002c180041c89082000ba041d041c6480b002541d140c58080e140d8404c0300107039400a4000e407141406c1c403486014049540140c0010b080c01c600fa50b07902e002541d8040c0c015800010381d81c10380c0f400c840403140c0b070799400c00031107131685000034010351240c00240300100c0242c1071811040446240070900e41c420750450a9200039182180c0381120009030b25105101400001c001444081d903408181d503008100e035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 587786034 1250 587784784 587784793
    0x4111c0503091804020907051b1209100c051c0c0209090d260c0c0f1c081e0f0a0f06030f060e01020a05030c0a0905041e1b1709011b02 59
    0x54200f841400101c10903222040f01c054001d120040e5120035056811a00b14a002c6445191140185000d01c0c8981c107040558031804030346c060031114103400340034000c008807020185d41c40740d80c0c4150f480c0c0e91050002040f0380c000145001c0d6840c0d070307007140950000351850264201710032030780441c0304802c0c1564495a6907021950503600e45a024405072040325561441d40f00034144981808030500c4040c0440c0c41c405008240c10210440810403000400000000c503403030040c5e080705c01c413008425407002c10f0008500c10300250101c01c0020031000c05101e042c101659940d6003602c030a04818014184402294642c80c104050030414024080510b02901c4003182e074050f02d00c2c0c0703d411200c440c05203d0f02640144018801f441d00102665030002c141118143e0310340c2d800c00e003100c955030603400c155406850008942e11300030440c0d0044c4c0c03540c0e2900c4010840281080e011100c8601051148400100803400079003800d44001d02550700011100004540407030400345070a00e000c80038a0700f9005922 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 587787284 1250 587786034 587786047
    0x70f080a1e06021e030f15210c10111911011b1407060e0d0302060c0d09080d050403120605130b0406090e0a0308100609030807081303030915140304111c0503 69
    0x1146c085a50044000c840103041e1460b6400480c441000c89484280a0074401c554031ba88210180002040880000c100c0b80c002c00c1201c81c050b14444680c00b03100303001d10684030602c0703c202c071040c2e078100d040d038220702a4150a0f00000044030300c020222400040d5942c00311690001440201e510034651421a000d4404242004d000030180b20840c00c21500c1404090b0b21480841d4004c45c140d83c0100761030f2081e5582d00140c0310144040d0610a8000304010000243d015550000d580310368000c0e84241c0d11104241c140c080010240d80c2a40540d83d400807c54040d01d0015100341d000004549024001107007096503001000100d5000c1000072100d500010082c5003056030007070a003907001e100100350072509802e0001c02040700080d03002c01040f01000160000030b11100da810b0300c03407454102414401550f160309d40205040401d2060107500c41d070030745250500710301445584440094030000b0f541559199220318901e80500081c0c150044d00b8009a44c041c0035116142620090080009660f142c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 587788534 1250 587787284 587787301
    0x4240c081b070803060f18070f091211091e0c0a030506330c0a0c090614130207030306080d05040806160e042c070f080a1e06021e03 58
    0x140c905140c0429807000b002220b000448010a0b203800c00741c240c3d80d00710800304143c00f1511040d0207100001008880008020b01160702500c0901e0311039450343d4100c02a95900305d404440074a940d40180403010708008a00c142c1000f1010f683d00c4650501192a2414401c2c414000340d04c055407204603080000845c604825018003a00350001d005848461248000c4810080140b5818084854000c056000c0740344c50014001920078260640c4165441c09030b0510f0900c075100218800c0441c941c2c204000024a852103800d4808940d4001d0035030543d002c4110b03007040c001e501c8004102d00b451703640e82011842e00c80400617145450f00e42c0d15181d540b107042160075441c20340c0041c5007100070140c1c6d111000481d0380c003174101240b440040d64003080c03000d0108204000c040c451195800d441681100b5001580c03400200c1c901224000308400c03150b1a1540c540300d4481000c040040c001100c44402e0f0024080034426800e0105d008900041c1040164041010010044036030003404441c04000c0c0a00c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 587789784 1250 587788534 587788561
    0x210090b07030801050a0b0c0307060504031716031506141b0105070c0302010b030303070e190e070c020a0e15010503150402031008011811040c09090906020703110606060304240c08 79
    0x10004003003a62300300003600d50f09a40c0c83c03240c600010403541c0c450000c00d04041c020001888803100400d032a0072a89012604029020181c40704400081e0804080010480400d44050300759003903a5215800060482c510248550105034510f41988608100c41e6080360280f065502402c070569a84402200500b002829100d4a2204074482d40080041c40011900610342089191060b81c009014800307201d494082d2030016402440c0b08039802d01040901355101d291055604d10840b130801c4001d4aa0703070380c800400021200d4006a0000300491405507014401655000c0f01303c400303040c2c04403d680045801d0780c1050f104900c01c0f4070540b405029400c400c2c000c0c030f01101c00885841103c0b0a250b00e07400d100c803c0c0050304034001c665401401d0b4000d40304242030f402a19186405211b400c5e45460644000c5d8060f01090b000a020342e240321500d2480414440c0c0030f800700801180c15912243c0f6090198480440c1c01e204140420800440700d040c28001c0715480304c07280c0c0b180302c5185480e07026007484 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 587791034 1250 587789784 587789789
    0x21509031c08011d07020c040c18090501090e120304060902030321040c081c0e0111060f060415030b550b06040b0306011b11030c0108070c0210090b07030801050a 71
    0x1350b004d10810000f0030381c0d00003103800c11084200c1e0b002c141c88170b0b98001900c40c0d95858540f9040d082c1c596a020921704003981056040700e950300420070208010250203034850b0501020111601030030070114000c1002d0f90001c500480c00142a03d1801400600d0842c10541650550319040400c0c2d04110070b001941106000411035032010786002c0c401519000481061180040c042c0014003a40e403800d40d2107070740c1070040b609020f07003100e03607070300b0700c407180d41181c8904803191032040c0e0500000d10540354110701c5990480740d00210703910450311000c0c1d64000e00f80f40100028039880980c0d039070402426000400c0341d15640c2d060390500c4c4461180b607048903900c0c034000580e01c08504041340700c1e4003034460b6011601100e034441e003000d490b611082c0040310f068004191041d51500702d00160b00030300666600341041d0300360450803200c0c6000102d0054035004802c491030f10200d100000f4060150411040c0c00c1101e283c1c0d031a160810540b1004005500e4000d4442900000ca00c040144864100340e81006d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 587792284 1250 587791034 587791079
    0x80d0b09190b010e0d24060b1308030f0318010b0904060506120f0c010c060b090702071503060b0f0c070b160524010b0f04090c0305090607030603021509031c0801 71
    0x11342c0e140442c040303404035501d1040100354007a0607241203410032088101841c0c1d400e0504080c0a0982d03224800c200940100030103001d0403011201c00140c4d40d20004c01c950071045010101c90641d500e04014010f220300b42c2c1c10004045d5200c600b070b0b1401ea9a036a0700706105605c9244001205d0034800103108030700702c03998000507855011108c00912f07154002605a02c2c400300b40ba0480307a010030b0740390890252403008a03554002d10080c2c2840000d89c0c000c16264260340c44003500d85a1a2070160084054440c18032681174103400820400c0e03280f1400500134480107552000315140c403650303481c2c8492994485002c038a482003c5405400410030140030f4900501440551580340c2185000303915074800041c4607e070000340001815422294000080e617000700368031002004408450300c0c014024010880b01c6850070b0065030001075109000740300d61000d40390081c1001c0d0903010310f154070104950111010035410306c20070440d44401518451002075100055030307044215403502e1030154014888024440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 587793534 1250 587792284 587792297
    0x203010e0a060506162303030103120f121113030303150b09030615120f06040b070201090309140d0609110a051e0108180a03020609160503030304080d0b09190b01 71
    0x200561354802a01c0c4408003540c10208030b06401d250450300080c100301c0300f031008075000e14405205039011018604a0380508d503482c80129490700100c1d04404608a02c5001c01c03070140b01c00c00783c4642540020101c0205440b40c9203842502540d401c150440b5030700c100c0c00240c452043ca0150010144844c00904240c200d6505007524000043c1d11030790f000b04503000d02010741001280503500d403d42e402d207281c0e0000030303200c650505e2000b41d61165011242551108030040100d0782c010b10510a2420340c5405544084005007441d161160301480520600c0c0e019103294943d0f03000c910300c4e10400103898807403400704a1074414602880034070441644220721501008010601000c41d40c00314114800b02440c1002c800d581d02d095034010b81010840a0300d0510aa48040f420150001800ca000c2d07030801044800700031540542142d031212a010700b50305608144041000941a100a088845040440490160300e41e4004c2200c0c03d00c116581c0341d9034500b007040541d4100e190310818590703440270310702034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 587794784 1250 587793534 587793539
    0xa060b120405070b07170327100c0912030f020f0d09140607020a03060b0109091d06090304082107050d0210050705160f0215130810061514070501020301090203010e0a06 74
    0x201c0c48046d51702c0d190407502000100142260b046a100d10951034840c240100584103501c100c55512041c2001030b280c40c0c0c1c60801780c415150300400b081c5007154105091100c20307540303942d01154480d04030004001503100d40c080b60030040c0b00078060030410091658841d12503d1802808285d4102000451800307104100200c0c009a1200039086013620381040c0c0c085180c2c0021001200c004046602085041c0e01c2c7c0469080000401d1b4091074044e05588100c40d441c0d116262101e8032403166104642c2680d0001d901d032443d030103983c0300e10184000303020300035410312803151580340c244001505814010b0300440c00a504000390b80c030915030032141503e4802c1c1000c0e03000801c8101250007140103015803409561000840d6542100101d0940340e2064803500d41c04100c5110065a0751070050199501981d00700340b10712410351003001e046034441524a2454800c1d03031820390725110f0650680461110821401c00465070900044d4000c20040900503925031504081c01540d0740064411258542400d004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 587796034 1250 587794784 587794793
    0x90a0e03031609120f02120c06180d0c06050c06010603092301090f0b1602030c190f05010207150e0313030b0a020405090a0c080609130b0a060b120405070b07 69
    0x90740d52100c842d00195074620090301050b2660701c0c055000010000400c411002000390b8904180f001920946840952007001038809880300c504106058000d0340038040c104e079405006104800c480000b5008010510280d121000b41c4071141d006280840c0c00010b00300410b0034104996401807050b854200070b801d205079114000024030b0700305035800d007950055240308021300390b004047d595409a4901c0c0c0c40c03400352a02072281c6208848110315a2131046e4001c4c4541d0000c0f086842c08000c607400362002d0124100c820043c442600026582e40344000e003c00c0000308240b005011441c0030b03003450928580c0e900c1488007038070701d264041826508284a0700c40034008010001003620707802109204241e40700c401080007070140b0352040b507200d244882440b070010b6440c1d00554078581030b0398524030140e4403841401000032040c0c4118071810070420f980c1c000f080300204883e420001018001c22401c1c2d8480310701740e50b0f03004440200b40300202241030108001081025a008202c1442d00b2424800d040d01c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 587797284 1250 587796034 587796037
    0x501020d020d03050c250b010816120606030b0c0d0b01050a170702010f0f0b04050a02070b04080c151510030501080c040f02090402072604031e060b03120702090a0e03 73
    0x20009064444000c1560750041c80280e901b03000ca42c19808601500595001c200c2d0326607402c003036542c0750a0000200312a8000b1a0302c103c10102c0070082a0b0040c50702c04c00207015586030341c065a0950342c07203401100107146104218002c0f02e4581c41141c5841101015a0481c1c2c10202040d0500200b04003024002c1d1304880410300c84613429000e20255900c0c06000c0e8090a8289a00302c0140e2030080c4814010301c407070f1320030644800c090300d04110655038045954128843c013240035041200d03500010b000542804000d0540c800090183c41d600300c03c07203444038400d49040c1d80301040c010b9601101809420100229462045c1c68a001e02c41d40d40760000b110b45a5a581c40e00e1805103031101c44140003032650750100c230800500a4411581e8205500300001c2e49503110200401c01061030140e020040d03003101c2624160798000103101703007100c021030390b83c2c0300800301c0c0100b16445900c440064003070795410311171190503c25880394681d0341c1000e4410083ca488005240510091900402d0400b0800000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 587798534 1250 587797284 587797303
    0xc1a012c06090c03072708010605040c09031403120c07050d020c0f04090807020a030c0f08010b0f010c03031503030305160201022701090e13061103040f11060d060e0f010501020d02 79
    0x210640d580c1e00d403d40e04607030f40b11103051100700c6c400c80c030308100210440b1901e180040380e41110080210320340301d4080100ba0784000091000007407a00340c090010512000c0400d5a0030201b60882e4500200c4078140050080304442c50b070404100418164107100c0c0c00d01c05403104140c14030160039107050b200300055810082c04000781c000c6035180b4203942007200c07405c110303424190014a0718401d144e0742d2400040141450080021012014000140301b00301409450b5030127a009002ea07100100b90401100d881c008800d040e020552500d4040e030b450b04602c4014006103010740c3d404500c034905003040220300b080c0301c40d19101b1a0300c10890302c5507003c282c10901503502034055901802141d2540100c070300703030400c0e00300100854240d018080c0508100d625800481d03c200400d1000302c022107580e0300e19001c21200682a607000c0b0034840d00060000041000c4090001e200a040c003d249900c00102c0d0419013064640000300014401400d41c035944160041109200420907042e00c0e1a00a40300c041d5107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 587799784 1250 587798534 587798551
    0x50a02040b0d23030417060405070e0c12060a05180a1d030f160b07031e02030702150903190201140a0213030f0201050702150d050f160c1a012c0609 65
    0x541c03c02d684440d0510403100200040700d03206c0782010103002043e03190681560220354900c0340420001f0341c081342c0c5a00302d2182c0078094040f41000415081181100d500600980d0f000034003980115180e501d0312003088014440e811515814648014030380c04860f01008056801074124005034000900082100d0060810f04545511900d45080485180d00400380041084014108000c4001c0d899844100c1300b0b843d46002010303041640c4402e408920080e1281e0005800109003541403145650701d49070845480c108803032502c0400d11802c0c2d0f0705070711051401c0050351036249884001c1d141e44c500c250401c1030387c8408c42c5090200401e03804640b801d407100408101100c0c0840f415a03002d5010b0350304587e00605030603a08138401c030010384294450386c030210341945400041000102060340a030b104410f190441c001e500100c060a03190081910001c81d940c84034214100300d0031906101460003401045a120150781010a402c1c61054548080014950703100041000c0c99413002c4a11380c201010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 587801034 1250 587799784 587799833
    0x3080f0c0405060c01060302040908070c090b30100209010816090302150f0a17070306151407050d090f060e031f090b0408030601110c0f2b050a02040b0d 67
    0xc044d165400350245030300207581703d4541030b8514203010001c4010042c080c460103a06150a07210300c03040c400c4585002e5842d41000e00b08117410030b20503000146a401000455014220400242c4801d2420540018111f141900400c03000040d58210880341d4004039101c1940302c030780c1c032900002480031045101c0603124034625044a0414282a000c490850402e2001c0640e1112195406404c261001e0701c48808080880e0028021034441c0c4602c0c41920704088040281e10042c40c000c4411811070301880407007000420503103000440801091840e4055522140582407030700303c4050140b0078a5010070140401410000c400355008144c09000080350603280d01007900f03103180740c0020106072030001c04081c00780c4107000c1409a16006148030b103400b6641d900c041c440d03a40800c0e8071080700000d0302e5001450140030b0f904500d40600300e810032003040030151110107115416105d890882e20000d40d52908182d1000c0103500b00342c0600c2000b40c1c400e440503e060002c1e6aaa100d000054004030842c1115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 587802284 1250 587801034 587801047
    0xa0203061c050d08070c020a151101060e06031203090d03020a05040e04030e09010503071802090f1906090902120714090a091e110f07020109180903080f0c040506 71
    0x1c8404041c000d6110256070084100a98504980d5034080e5401500101d1403510009080301d10404000e00a154090004c0718521704d000683c02540503032800c1c2c1c0f0b05214030345000340d0100b4800d2140b40011314018101e1500c0381060824142030070100b00a1502e4424200200304000c0000a00e00154040d81d00c0e00581d2088400b00450381805035400030010f5000300011301c000e144d4407a40700560341c0c404803245501660b0312402c242d5a1081c52203840322002d111000488641440e86c06401141c5018290200c3c18043c000060740311900103506096440600e002444010362010354600038085841046160540202052440300340c002d0144080020b03000c1207105400107501030b107904c1c042c0500740c08070068580b0601405842240c8121111920255402c984c0500c2402007980003411162079a142c0808c001258001d41d000307940580c14404007401c002064240450504000e84801100041c440507a280040c1003041c064203810b1300c40c501409000007524a40e08a40886070115595943c828 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 587803534 1250 587802284 587802289
    0x9060c0e0d0f1a0a0b01031104060f0c06020c010207080d0f020403020120101b11070303080123100309110109060f0c03090503010203100303090b04140f040e0d0e010215010506030a020306 82
    0xc2c10440f03419041010b00051011030790365a0031103804100700340c80c203011015038110f03000858082c500c0741000151808034888e50701c501400629a00358011003000d80340010b55640749099030300c1403070200d0382140d000542a044074500e11590300d0214a6010661805246800003824125100524810032080001a41d40072a081101d100607030031003c410320000b0407241d410045280390040110100740008c500e081e9100003c02e03c130080c0c80d40342c1c5840f002d81e400d00710301503c0340207030030401254500703543c010303c0710713a80d40c410411194512a138011401d170402d450f01c8180864404151414800429014080d0315003220040d194442c091409940061040c201151410740c20f600094140d48000b00f84202102e4402d4400141c03030007a1602107500740c0d00c940e00c0b801c1d84201d20030802d0031105075114040d03500c0c00e100c001e60044c10040001c1641800d6030703029410a0303020b00c02c0320301169000a410704a540c05100c844600401c0303200d00080ea600d40000b082d0180320080620007031503400000141a50f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 587804784 1250 587803534 587803553
    0x5090d0203060103110114070c121506090617011e0f09060501080a050706020f0303040201030f090605130b0705040b09210a0501020a170103021c05120d09060c0e0d0f 73
    0x80d00241241d00c19656414422450a00c10140d580043e401807401e50403580c002080b070751400e50014200707581504d411414080c3c038026010403205c22684210b0004011103501a03e009080c3c078440006849241c0b02482001159094110035141d04022110354103002807602194541d00b41d00c40031610718940607000d4010300a1880007800285040004a01100d001170741d00341c0c051080046907442c075201c40080e40e441d2517a8141112507402000054019440b030380000103c03990345400441c10005982e00c51054600403100c2d0074601052402c3c41b0103111a41c181250001c1107414680e2a190508407215500d00c00c1d1280d4074003c0d10a2842050386031422125000ca400b03001040c1d0307248030824600607011f50b01809072100001d140070716079514907480c4650703035048a90040074160030240004401d850410501c03410382c0c403405004070342c0d010b58600380010000e20240a80014003150a443e14804541108507400b00304a0108000001070b00c075001e1003501c25411002050341d18101d4540b00104c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 587806034 1250 587804784 587804809
    0x10050406061703181c08070f0b0f07020d081e061903033c031a0a08030c120307090b160501021c05150a0611010b0d08031b070c060509 59
    0xc07181403080315010502c01001808031040000c207903001500002c0b00704a00400c2c995032840d00c07070010001120001e6113400044c000c00e4070414a030410000c640d21141e40411086911595111140e000c1003515581030110301c00c40f0240d418010f10504044001c18164040c2e00e551400244800e4041400c5544011060380e44601c02d602401c2c0c419102e250040000850404ca04d08081043c0e000074240c4048c030031850543c01c04011510092401c240003180584100345209401c2c80c1400c500c0303804d6450b181c0401000c0d2900c100195070783c0f842070055a242c8520807403502c001c010b0074420710011a501c100b110086a9460340002e44550780b4841d09280c121483e60004c190358070008540d44458400050060347d490291030420980c2c0d0703804005402441c3c5840c0c01c40d4050400c1c0020f018240c0115401c804d5a20396600004242c01c03030380d0100e01c89928080043da0100408010004901c682c0c10800503407104031022181410340300d5881c180d03282c405020b20000d004010074481a16103884000c0800e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 587807284 1250 587806034 587806049
    0xa0206041e08070315020f12010f180506030c2202120a18030807031a0d0f060b01020d0c0807020f19030c0605090105191407050309030601090e1005040606 68
    0x1500e0740d0310014020400c40d6040c441900540141c1c000858038004500300080303030b801003d00b4000c4003a0007002c000030b50080c0d9514442c5402230100890780912050b40780d018000304c044086090b410100f110b4450b107180021100300d1401c2030100f20317041c2c0300412055070b00a000d58545032105040d0306e4a441e00384c000c20041c0c98451012030024252081100002c1c01411003103800c1214840790315520701323820010100500440ca4080c00714001c54480d5009080d0030200301d100394640717112507000030312142d0341c0c99003a501ca0288003610010310989100c6c42e0441c0c0c100340001c4c02004031291300640619100c0c28068860f800110341e01043d901c1b5010180120300000700700d11840c840007152141d82c070102c0c1c0400c0d2907800007040c02140c1a4050340445400940585465041c203010000080c0c5150240c6030440c00c00051038250001e5125150103061454410390140d42c441003008145444d08005a0100711580e007080d15041981c140401e0701040c010310008041200c1c2c0d55400c026000d006158885203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 587808534 1250 587807284 587807287
    0x1021018020f12030c071401111b0a150c02040f060806191808070b012117072108060108010b0304080a0e15220515071a010303110f150105060901020a0206 68
    0x165640d0740411000d0583e0842d1350007c56408190004648000e1007521040e03066012200c40f0854455012620a61074802846250090303144e07071580c66410140d14058010071a2080c0e100f046103440d0040050545a03010100501483e0840c82691703080042c08454040b0001040c103032104078150808424014450b41803c4420390b2850551110790003d602692161a28400442d00341c00c1a5882c4501103026000255901da803a281c0540d80280011581c1d05101c1c20000e580010b40e24a140d0840d400c2f402088005e0345c6082c40b406080380100400b194104018600107100c550b107c1000c0d681c0058101d00801e48440c160340d02510400015586183d0042d001220711103013400110080040c0c6a4514004100411080ca45214082c6da402066400701c003100e0306a00342c00ca88005441c002e40200c660107142d03602403c1c464640311080c2c2003500020702072400d580e08600e04022540b0300e501c0442c000d10642d84401c141003000f1006000317041c4200c10025034511076a1081086000c143d40003807445 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 587809784 1250 587808534 587808547
    0x1e030506040b01050102010510360c0309020306100b18040b0d0c09060506071104050415050f0106110606030a060509121c110a2109150b01021018020f1203 68
    0x70142d0000344070b41801036081800060220010303441c00021100780f01c2e00402404009040404041001001d42d1140d901305240400c0420071400342d900300e100d054600045041c40c50040c14100400200400e45603242c0500812296a5240403118019014001140b0400000d000030700034080700c1e24401d40c0803403140c0c100400e0141d202d04c0401102d283e5207042000c6035440007803000901911001030f00203c00a1141002420075030041d541c000e102e84c00d00c03807224500e5a264401c90328196944064004020014000c00303801c0b64207204043c51140c01814a458510b0020b580c4404941008007030a0f2600701181c081d40040240304140c000e1a010252507803031a0f651401c0d0ac01c00c1c2401940e900703082c0a10000190020812900401443d07600c41c80350104c03810040101110042c80329000e00e1756008003c020a41c4d498142c1ca000303100050216000002000080c40c09203010020f05034145411040c03075030200800d0a81d24500e506950b0803003181aa60b000880c1c0803010605103030680000a540c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 587811034 1250 587809784 587809793
    0xf02070210020c03061303020c120705060705030d0501050a030f02151e0721020616090510020a110a051305041b120b01060314011205010603080c15060303070c1e03050604 75
    0x1403003020f600c1a421254a80d840c80001a01512000360103400758004001056443c108624180d44400b5101c00320380b40c0079a102d001c11510351105000f6035a9801c0810325520f8080f19000d914010701040361036144203415900e40784008480c804000b80b140b400c2003403401e031009074a010340c0c0e0307183d00355800401d00710809118113016500c0f01404640210351081551980700c0348181e04c0c0d4644002d90b0040c1040e0f82c410810f4020420f40d00342104c1480003500d40003c0640d608080744820101641c058100c03081385c0c0c507082076200303040c091517449049516401d000e140c903400010b410a412007400440c142e1201e0400210f00440c0003a032554104500f40c0c0420410300c100c445207442489480c0450f2240c1ea5000c0444c102c601403401045040c04010040240901140c00130039142e014200000d8403036525038a0480301d60000f240c95425400c11510801d005002e045201e501c000f00f5000b451600140340d03180d40c060210750007107180140a9041d080101c082d203a0200001c0e60384041180c1d514200340c140f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 587812284 1250 587811034 587811043
    0x10f050112050f03031e0a0b06040902040e42150301080f120a032301090f0e070302030606011b0b01080102090f18010b03060102030c190606051504090f0207021002 72
    0x4003500e4500c12201e1003d1181d400000b26403040c200c26850554880b00307802c5001d02904007405106000381c586258000c1e80d5924001400141031803a1700596a170700e0130b4030203201c00d2002000814444295074007050010b0107881e07001e002c00800000d0985e1420340e07840f400640da20004440382c21008101c4100080c0c8041c200440c10303034042004507084c00450030b002c5552003d0310111024030b0301090001c0b222030b5002c1c1d00b1141e070907110885100402d40d01c8c001011003480090f030040019a4449030443c0b000406803090508800314400a80030240c00c5401090f0380d1200030300014104100410100100d9880c65181422550310626040c1d095035a002c245020b508160050741c480c544881100d40140b0307101c1c4002e601c200c5401e5640026030719201c035042e184e420023030505d270560108005000c11510203000080b0992000340040e50480c00c0b80c240307031080b164a90840c0f1f0140c030084030200c0042002c40d083d64201c03000d0640105002c144000c0b0180a03014440c3d00075044000c860710141111303000304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 587813534 1250 587812284 587812319
    0x3030e030d0245191d0402011103070f15021902030904050a0216060906020c0703050105041e081207030b0d030e12061005090c091008010303080c030f18010f0501 71
    0xb07050100d1180c00d00c0c0ca210b40c15110340307900c02c9426102d00d648a4a0705003081d0303040e815264441848902d50b541c0c9a50015900d03450b664000c0c0088040401c01192703000100c4094224044006604055032a030360032600304603608002d0070074030701d110081d10303d65100e404840c0056000c20f41405c2d10380200c50b000e5031b00c0d0401e01405224504100001d001c558085c402d49490200503d02d840c1c4290080d00d03500024905441d080e81d05540802c50126a01e908010381d0004612440c00040c00b80740505000c1c1601a4402200b01c208007c0d103d401d02069410099495403007020088020b25181d814050b0000c0c112204000e802131031103548001415007141490f020400113803030001d44200c0c6d9041a503110340741102c800c00d803e16065800d02090074840c11082c0d1140103482107501d4105410001540ca2008503201000600200c0042c02010b90002030785400c140c0080855007981020721410707400020003054125101c01e00481c2000a00c0c007504802c600000700c1030b0403c5070707503140d0004850682452 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 587814784 1250 587813534 587813587
    0x1b2401080601140d0609030e0603010807080f0d090e13020306070e040c0905011d19030c0303020f010603030219150c0509030c1807081305100b2b03030e030d02 70
    0x110000525009400060081203c002d250b24030181141da1800024804164150308020308400e610781180c03103440003103020b081d03540018140d06160450041c40e1a68000c1c0101c05a00322801e0104000e0b0400820810b5500c188068851035071a00150016085509000707585886240c0500030300940192900302100000c0e02d080c400080411025590704480d442014001142d0342406921030b00c03940c80d030f000d0301000103100c00752400010006001d0300b00c080e002502d90303411f944420420150104252145210468001e2085e00c3c0b854070040d4646000c5904464040340c1c4101074401c01c40d4120811070054640e00e42041303004000b0800404a4020360b0903507007e4072880070091320344c0c540341c1d00c410a40b105411800103c0e03907400d4004c950700741001c1c011003521400500d0320381c000748003406155110541070b0350008003e4411000c00c050f0302d441d85103401c600a010391303c0319002c0c0e0700e00241401da13030303010b040108110705111029031640c4207600b44401c06030300c0811881c9400d25030850903812818075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 587816034 1250 587814784 587814793
    0x1e03111516030e0a21030f020321072a0201080712020a090f05040e03160807020d050307150203150d11120a021207060207060e01091508061206010b1b240108 69
    0x89010500e001031410024005c1c913900300c111480040d10803180792410511070720541c1e08040b002d503252030703c0181d2407161000d54903648040180c426844911865003020081c001c41498600400c50180103c03820000303810042420009201d43d8015103018551b0800e0359821541c0e103000b100d0090940215024126082d00040800261480e19001c5e9100780441000a0b600e0000b07900000d861207600484203d604010910241c030140c0da850083c40111070056000d0750365000c3c0f41c601100c92115001e5081d1080d841030083c810101c066019440e00700c0710a031901290360450b130a012401d10044401540d00c100c1e42c100f41c40500d1404101200080e01c251415483ea09207121142d485403064010f40f00140c1c0070860420041d0310034a20340300403003010704041d0306075501c0714070303256000e19000c4001c4081401c8905212250411140700750000c0405009041103504141200c01c17544074000c07450700c00341c802d54502e00c00c0c40d90611401480e1032442e4000c00d200d017802121600c8030f540074450030441c3c0c0035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 587817284 1250 587816034 587816039
    0x5091c15020c030a0e0d02040c050a03050106050a09061209051b01140403020906010c1a0106031b0e1e030f0d03050613090201020618030c12041e03111516030e0a 71
    0x40d00a07035a18242030b4018504181102c5000c4030107070800d06102d0b50190851200c000582c840f4494009a1003003030f41c0320b0340d131440c400001405445040e8009010004100088056182d100c2c0c0110181c840380d03d0400944548500b42e40060039003d1000342482c06981b03519000c2d030800c0c95040107101d070300f80c0b1840c243c1841520561001d0280f80f0010b50040919000284258403800e071089044c0d04c44e03d480e040f0310040d48031046003c24244c0042d404070355100c1d204180f4084070070100c0307141602450904850440034011482024112030032504441503480d42450315030301031018202074000c000c11110307041801c0c0402405490140da0340340c000d00c40108101d0b103400c083e02a1480054043c0c00800860316189003c0c010810a1002064140020f1007504140b010601c5081928103981c82100d841703030305104000c00f6114a00c20340001c1c40320354440c104000b80010200d551680c0044a0000740003d025030501418880c540905018100c0002c4000400d82c008000e240c040d2405c1e500106d0301c58 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 587818534 1250 587817284 587817323
    0x1c09060f03060e01030f02030a05030d0b150a2012121b040602070e040c2408010602010e190c0509130c0f21051e030408010f02070201050f0a05091c 65
    0x3011401030800c60f1041c0380050021440c4c12030359110161014003100c29006c61600c849003181c02000e4040e40507515480a050607140006829843d04000c000b060b2600801220140c000c9220240c0c0c02d04448010b200c40702101001d04c1070680c0c21241010282e52aa01d060308810030050807500c8803141c0580b80407009207980c03800c080d681503410a07001004c0c1c450810f0308883e5040030040041b603916016603000300395000300c0c822141902c06c06043d01000380305003000c082e2914a05070003c2c0216850007440000f41e2100080b448070074164100000b5003004581031100034010580c2001d074101c144501440150201089001407041c099680c40501603150100005084102c0c4211810300070001d4102c2a044039208605010318801c40454640c0d24400d010035880e04c44001c407010700750700085000c210301142070042d092000341c01c80d0b00b103103010030542c00a401c6018242104d2005400495000b03401d07401041281d43d0b51500414000030405043c0c844100420240802c9891900000540d00c407e07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 587819784 1250 587818534 587818541
    0x16050406210b15040c0804060b030607020a080702060d0e06100806010f0b1803010f0b0939090d210306030308060f06040306050406090c1707171c09060f03 68
    0x508600d252690011076501e4400119030050040402d8602080c522071113035a032885010008046a00c45ca01c0c80d1901c0c2c204201142d00d40f11255011342c109800b04a9650b1740424980e0007194803007050780d12607645001080b200d0140c0420046d8491826440c01e034000c60024589114074952048040380035150ba0200380c0380c0c0028132507100840300c130000522076800c207240601018440c507100d69a2204581d8000307800d4a8400020004955440303d000c82c0c103040c5189602d41c848482e0345240384854007103c410203603000ca03c040c0104110704401c0c41042d0b401c2a0221506401c5c002c06c240c410052500f062115820007442e4160901c0c042c0300302e079210601034011401142e0b01602d5109044e5201e40a00284181401015621440c100004800220107201d068040d80c050180010000060300d0000d01200c8680c0040580d000c501a0b1030410000c0091030401390344208088000e00c081030007001d40341000c41386408503050250070f070103909070340d000b4400b02c01c4500300d56460f13f00e90211182138086 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 587821034 1250 587819784 587819819
    0x110901090c020c01030207060f0f021e07050303060d0203030705071509060e0f0f0406030203012306011b0201031a03030a0f1e090306090f0f06050a20030402040507050c16050406 78
    0x2681001d0007000c40d82d170195000c1c2080c0390041d030b008120110005070610858400b050f803007419a501143c80040c1c030055040380241c044403c1d44d0103140c2200d0340c403440d0b60f03400020f0404e442040200364500854a0510980f001681e01204445607503880340d44048800c2e6005003004001103d003040012000d03c07400400303201003000781140044007200310600508040c10a14590455296840000103071000d110360018481c64101c0f04c03082070001c00c2c00004003800949128100899881003e40200ca4210542e00071942420005161800700c4e00718076205900401e82580340c080030485a045607001410031401c06210f55403130415140b0b2600c8481c10a0100307081000080780044144006000c551241b200c0d9030041d02c000150319026511000200d0500b00202c1e040c0e5110740034000c19440700c0c0101405e610034229184820301e00c4e081050350131702000308040c0c851511000400e140502840c00c813080508100c050701c0090055408400030b428561003980c4c00303946090000244a10100101d50700e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 587822284 1250 587821034 587821037
    0x20f0103060e1501020f0d09080d02060601050d0b131a04140712050405010b060a170702010c0c0f2105091f08160e030d09140d0203070b2203110901090c 67
    0x50f52036140b409059074418080843c194456000f1a051070382003000615000700c1155541440c95050000b42418941c0e0300b400442035520220034424943c1e044000d03100d00400c4e0410000f5505c1c006000282d2a20b802031140203260b260201e0504020101c0d4440c40380d400c4103450501401c8000300d0f201c04104070031102d510001d044405001c0504030b16803c5643c100340144000f14800c0c80d41000148130717501009c41540032540d000300c00024a5040c100d003139480f0006000030804060741c6070003c2c00d002c11900303009220b51500140c09042210030090300c541103804108020b401e00b03c000b00a000c80e80010119403103086609281c540c0d90130401d2803001c3c0f04071103039680c80ca07a8171a54045042c071380e41c006c03030482480ed040071019140d4404208a04481080f40e03550340c5205e00d405400d2080c1003888034194000c06040711a900541c0380003c2c0c6e0310403905c1d51055039170f58103851000321724900e00d2080105418140d108001007801981d86040c0b02286040303403014140c0c0d0340c60092100720303040c5000240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 587823534 1250 587822284 587822309
    0x1a0102190602070b0114090714160203100501090213050f0d0809030f032b150308092b050d02150406150305060702010515030d17100e090109020f010306 67
    0x210300003100380da000c14091240700094245007103681c0d810000ca400360411961038900402d0303041e603440c100980b40d8002c1c029007054649100e884500c0b007454802c1541454881140d11604411510300b005004445801ca1408104030b5856603060b401a6020040516062121a0010480b03140c642143c82c2c0b48003004181c2d10b00c0c02070955400000390000c94034a541801080641802c01074144002c03c0d40072500022a00516051801035a008540302d00e005100e80c0742040110107040e40212400a980e0000f442c19100c850b070b1800501c0214a112031032804500380000c1c0c0464803e440015004241b040741a280000c600510032079450080e02d0101d4000f140f00c00104010660f1940019a075040520032002655160384440d0b00d0b0040c2502c900c0010703952001000806589418560310900040340500481c80d44124000c1103042078080e2940c04030005400300d14480301860a00c40107214041e041c421034500340b0752143c000d00c44801d00313901400c82c01400f40c40940c428400c01c42602e50980b40329 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 587824784 1250 587823534 587823553
    0x1b030b0f091f210c06030504030503130c0f14330c0109081c2d1a10020307150908030708071107090c09050303040e010e041b060c03031a0102 62
    0x4401c1c01d0040c0b10020305581840780071072036541c8001001c2c03040084410004079040720740f502240a00d41075200c0400c051a04081c0400240d215040380d0700515464590180c643c00360420b00c0240c0440e5011124024049100150f10202c9601418061600f100c9120f040d03010005c0050b00480011404002039908501e18140401e003200030308541d507102000041c0c4600706540f044680d52004e41c0b069803c0d044640f0180140c44180942c1c6841c05518045442d00414010200c03040e0360f1303001600c0c04054803941c0c400154075190300c640e00702440c01488506904040d003000394a942c40341e08140c0d2590000b030700c02a442e200c280a0040001e51140c0d10360b103541d85845c021588014003404400800000e49481712001c802084000b000d0030505400180c001c41801e8050a02c901c2a84024082e40050204000450b03030702d80d0541c11140020404e1883d0703500c9260150000780415130030084100303030800100d000f60b40001d02c500d4481c0304e900e08000c0107140b584541c2c1101000e02c0d42500503030110011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 587826034 1250 587824784 587824801
    0x1805091b130b15030108010b03010b0f12120304030801080601210807080d1e1406030604060c091e06120e0a03050a1803300804021c061b030b0f09 64
    0x1030300c5400c01d0200005008107911000505031501c000040b54944404001442211000c3c0701d01000c03000109c0082108ac1510740108070b251050b1a000c5114515a08025402c503000b03101d9030b0348008600714000c0c0c1c0c81c42d040c030300541b210400780100002849240000300383c80d480f0b001c46640d02d001c8089144a0705619941e404103a40c0072040c201c444400a01c0f49211010590241c4416008200a80200c0d5041600144116002c000d172210855041d5420f02c4400d4402241507508030303400a40104250003950000d8810010588c40b010454403000c1c1d042740c1c4002d0021014041e1107003503030b900018101c0103441c0411749441d0820b000c1290001d45034580081c1c0144014041004142041403000b42a481d039400319800301c2e403007600e0184075081400c610200c503480502d1203c2410382640070420f005034004048050003040240181000d6540070000c4a4000c140103e642d8010014014140c40c0101403c080324a103100c0004242440303200c86c0a89052071814a081e40d0103049520940e8500c2c06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 587827284 1250 587826034 587826049
    0x60e09070b0d02040b0703020a0212030f0405060a030b030303070c050615220e070308040e100315091b030501090c050301020a050a3212060d03201005011805091b 71
    0x10085102d642c200304c001250381c00d44002d4864580030b0f4001d04040e170804e0052210145d0421070481050300100501225034262034191402d0b600140c600d2074680b804c298095000f410903400b41070b40b41c4808420414080d42c130a61204a8034440c04c2542c5094440208000c90044580c03100d5a020141c105c03800355000341130080390410f00451078045500b91000441d90b060000782c0d04150307040100050305004052008442d10f40000e0701c0c003031414500d440c644407481902502e11210600681b100040800d0082001d4503100d981100410294550368a107051402424400c1003118101405540003c103442c0610a0b90030804a546a04e0702d840e000c031070304a80610700312180044200350f100c1540f03c0c003030021450540c60540c0740c5c8001e9552210500d2107240c03034801810b0a11070412904800d00080d400891000071b188100d1b1600c43c0340c00c410b20080d081c407040107020307200c1c940391400002d01c55102da03d011541050740c003420021a00e50300109521000c0150051071802d009408104030ba0408a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 587828534 1250 587827284 587827297
    0xc0a0e0a090320010e2104121a180d08040819021e21090a0b07030e030d0302190c050705090601050d0e0a0c0602012c1011070501060e09070b 62
    0x1800c060810062403195020325100000d40f4070702da5582811501074182003002881c0042c20740802e000c507000d1307004165000d200b540212941192149802410400f110090362481d0b20300304200d24039864009440641015842801c0c402489501124500d03d4000c9240501850b0003955003454807158003411080211040c208004511404c0d4101880081d034000070008a0301400c040c1101c94045a2001004000e0313104a5122140c05c000440d0a40d403090895011150000c00c215140e20460400792800d40d1080003854150280011591816034940c0c01001c500380320001991030403400c80021160f02c01610360080c00350340084420710040c6031001010b64007100501d80240741c401031248501c00d581c03a00d004004030764000c0300f02030100109203108401170075880c030081009a00c0b540b81e8801d400d14466240b9020010443e458003010000e21a0121031105031005000100c20111011080c2c1d012640590b113951a0040202c0d0381c28940050b58003c40e1884c0050451a0400d11203803440d51000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 587829784 1250 587828534 587828537
    0x120910080714031005150c0d02160e06060405040e0f1002070c090e1e0105040209010e04120c02010e100203030604050a0603080403110a0509090d030c030c05250b01170c0a0e0a0903 79
    0xba040040d0316034070301074040718000d409030b06c0f0740d21400080e40b168540408a10320000b0341d00700700b1100940d90942c0d001f201c111103400707034100c4c81a2640b001140d6036228a412068005050400c40d41032980006a4611074507014000c0340c142840c0754582c40100e0080e0000140307000c201309401c1103201c40c0380d080014051400c0d429900300d025144440454190310400d02c00c0d06035194020002945409040c0b0390040030402490015454582d030340d8818040d8003810780003404090019942507901c50200384889010103426100132608111000c0d503640c0049510601c901c4c1094002611104103000e0101104d03032007500a41480c0c199588e0301140f9400c101d04a40044540ca80007601c2d40c3d406617038501811113000504140b07248200002c0c01d407102c040a1105041c108030440311520740c01001c8510725642c0015000c2c50304140c501c4249280000760024000760f00d980000700308040c03c6010502d805010718111110a0800c0052044841c0c1c00e21a00c101c010f20b540000c1da40e4003440e007282104903c40d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 587831034 1250 587829784 587829811
    0x609060f09060c07080d031401120309030c32030c0d030302120c030103060b0109141002120325090807050d0503070506040b0a061409040f050f12091008071403 70
    0x600707020403403a07040203e07100c1c00c0f030340a11030400c0030b41414408100040d04e189814415594841d40114502c40180304e0840380e180780c7c003900014148641602805964030245c030b88011591518145500000400d040b00200c007200c00034690119052121043c0f00d20203000b402041c810301c010010880c40c540301c160185902081440d481d0040401031904c03c071804016a40c9a5045052100403070390a94201414419440340612104600c1d0b41130030a007403811a54a200e018080200b02e08090b2544034091070754402200f4813005190640300e403a00b00b041c0c0c0600020010003c42c080320015000d2090340a2504581c8050041c2d060456543d80480d0044007220f2034004156901c034a0400111400c1c3e41d101c1c00b02c0c007441b6810b64180641c42c02884c0d8071006207400c0e0020000194245000360004083c1d16080c050788040002c10700c4108416924001a41e040c401141c401c0301e22580254500c80c80303200b0407901001010301944110340034510643e03d8a000c0c4080d403000c06030551018144000400c2c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 587832284 1250 587831034 587831047
    0x60403180b07052118100c15051806040803010e040c0512061b0430140606010305071706040c0509130204090617030a1d0d06090b0106030b0609060f 65
    0x3518010061a0310807001801c2804c4100302c20b48100c40c89100d40c0f998030340c040001e0040801c0040c130740c1c6501308040310000701d405160303e000d8542d0584010300400c0d414144094024444031507001e6840344940c3e0000030b24180f040b070002602c0b620f0032500200000030500c018012212030b04002a4841c0c41810706500140e15040006c500264440f02600306074000410004080e0524000d4440e168064003094186030412601c0f01b548002c0711460020700078010010300d001c030034200e4001807480d00119081e42c7c4110540b0b006132255000c0350402d0210342440b011418161244410008001c02d00400600b5522198104030180103484108000c104080c070000307105540b8204400703081170503400d00684d503038500110b0700244da9440d40f00100c44811800880e250030404401c6440718007541c50124408403000c244a40b191116920340364001000c040c07001c0801840798000c0544500030200c1c4801680c0c3c40e0012001e5030580401c10750400d0091108007280e084c40c401516690032810445402d054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 587833534 1250 587832284 587832299
    0x130207080d0c0c20150a020d1d090c03160203070f020121110403050f0a0807020112020c03040b09010816020c100e101716090308030a0f15050a0b0301030506040318 72
    0x40500c10300510180300e448149135840c0400c80842d00703154504000b81481d464400103500c03040803100903c14012009560300702d280142c0c02d01c19811100511441203814521410291500708442c3d000300242a1500810304070300020698007503d50240c0352103c4081d459004444403400c1c038400405e05201d4004a000c9443c15009010340c110489445c95140d620314100356140403205080500150088a04200405c0b5120300300c03142d0503021f080030100503411365403600080c414240074403100e00000c20040f801245403001800120000d03611900130f9118a0401440c040005840c000540e01c0000c0d031240b28102032400042188490502c040000c01040200380f20561a40d0401b000460705c007e403281050f0400041c0750010054070641541c0494600301800003c1903000240c10345101000060030f2110303540000c0115001d0810611242c404440361014111243c09014032500e544000840c043c2503850559040b2500400103210549a40c0c405a4420394151031f20081042507000102d14070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 587834784 1250 587833534 587833553
    0x102010b090f101208090d020d06050c091e090106030c020f1504051c0e0607060e0114010503013803120415020705010906020c090a0f0f0902130207080d0c0c 69
    0x1a50b000756040321501d05948442d20407586904146141002d1510410220309002c00340e851502e03041e03c006034581624000a41d030100c0580004001d141000200003075841c1c0d034800f41a43d1241641c0042164168100b80c400e2140182101c40d0000e100380010081c035803003074009242c000784030f0050f1100707144004401c0f4100408041101000c3e05100e050000700074040021203000901e03100028003916a94000421056a0322000c6225000119038401400496481074a00721854002001808040c0902c1032a4030740921400744071703508e0811107861f00125141d00b0144180c0660741d607420040804c0c040c07200e00f00500c100c0c54041c81400440f004007106c1ca00103101514085c0c0c01c000d0100b00c961402458400a0b4010904101c00741e00e04002c0541c0018140380c2442044404059580d80c0410f00001484083c1c1ca14450505180324080007040590095820b14025219075940d481c6c80031040f0260b104100000f0a0321004100103031043c881c0d5881041028114504002031004075100c1500c0e2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 587836034 1250 587834784 587834791
    0x6060c0f01021903023c041202040b0312160f061e0b0301110a2d09090e0a0f0b04050a06020708030f1602030d0f0603061b120b0307140102010b09 64
    0x1180e41c0080d5015000080000780b80030030000380313401e40c5402e00c61101300303000400100e40a0480034000b4910003020304c412040785e0420301010006500c03196642c4512001001c40305099004a240c01512030709814081260382c60400c0d03c0380d0452500d104070140f0300e20310304244801e9451115000e141c1c80002c0440c010795619a664502003481240410101002c8a407904a0644607a1500e03402900e0188040280d03504501d0605110012902000038500b2600c207034084e840c802d44524608074200d64114400300140c0b00c0c0d5200c100994414140000d0351021410b0025140da5450310701c0c2ca0015020300d104561040c41182692001c094969500c42a81c1000a04a50211022040004040b03c00c02900d0384002038041504442c605058003071f45030302c0781c150100c02c50303900ca4090000c0310a03217402c0030006541c44a0100038410403860040c50014814200d180051881d80d111409905a070103404031541000300a040d07840e180c11500c0c4041d50072850303014103654a808041e91255a42000c1611 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 587837284 1250 587836034 587836063
    0x103050303070908030a09150507050d120c020304141009030c0e01030605060321031e010e0405010b060a120f0f0f09021c0507140a0b0406020c03191a06060c 69
    0x200c900703040002810f80051074200c01d0269109104110340b443d0310003651000c9680c00d14a141e00d104042008569621603000007810521880010f2018254401e40484165002e148104004207070010103d03220301c114410702444180d0701044904500d000f000060150074141052140c45980c1d98030004202c603a68460f03030003200741c01d0040003070064034041c1d0b03640010202d0290140c04051f40c1600e0f50b0380b10010b528100700c4000300000303150810342c0c40c04804000c030890705d1040a60b035544801e140c0c08000c440c01c0300d4039404c04401c541e240c2002d00c1907400707a94540d2a2000c0000041103994020b2420249442109494510411140185110384008040c1c801d40100302441c1900504c502a0711446800d880d40f01d950f500d08022440c0800c00c6010381c0c40a5400040900f4410b000941401c2290485140c5a400150010b4803d030002000003c003513065098a4180111030151018154034071000703400412000f03a614652150304041650201006000074200041481424034040c42d1107850803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 587838534 1250 587837284 587837287
    0x1150c05060910150518090705040f0f150e0a1e1b0f05030118051510091d070c0311121602090606031303050304031b2a030b070f030f020301030503 65
    0x401c914090060b0700013074a003800340c2d02c100c40c9071001060071841030303402c00f103207106055012504218003407141e4401490018020312207440c03a103800b400101041c265035030700e561408000307000c4541c401403440b04540040b030490b80d05a581000380c2024100c540101950380010b50481d615203c41c40c8524003a01401d42c0491a5004d000784019003140000360b0b241081c02030078001008211411031150140180c6c00c5c1c030105054071080d00000034841c3c001051540034031800800100e07254400c03101c500700c580084800d40f0442403c4210544d201c0156542d1002030712600c640004070380241c0c00303001d80002d440d04544054500614040c4260808a08400900004a00c070010f520304500403941040b0101c440d42d1440c100341503400c401d070b01c050310000c013030260110000e0145801401003010582c1c804e103420200d0395003868a8140311101c00d0b00c0e0f450042d0004a0380280c07240407042803007034a0740b204070780c10b660701e919100740d07220f4030070104d0780042545903c0b00c2401d45c410bd0019500843c8108000c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 587839784 1250 587838534 587838553
    0x209130f0f05060a061a0a020f06011403070e041208070e0d0318050102070b09091003140606120d0e011d0a23060f03040b0c04030f0b0a0e0309030601150c050609 71
    0x90f041c21001303030004031218202002441b480300d6140d00010401c100c2d0807a95510403d81718181e0034003900180c180c44c0360080d040000382d10a100c0c254803026110850540c0e0f00301e0b4594280812418080c1c0d8003902c480c0305943c0d62010980902c0703005402c0030729420400c5010051900165050090020031000240208424a58140c260190300c003c4c1c4424005000c482e030400000380c11a001d0068824410304500c00070942d1903000c45601d401850300000003000d644e2032a10803690300c90013a60a20300403c121000b2140340000803410901c0105180c1d03c1048114080004440f4082c0c480342501912041303051501140e60740c013145900811201d801075a0b000440c503041c00313920101c0e031102da02402041200000c0c01c003260003203d80c0680d10001040c49a15603003102101406150401050b1081140e40c010601024909180c0708000c81e42c42400141e000c220040d859016010347c0a415030300aa00522031010350481d5200c0702050741c03810101004440d2030300380c54a5815240c8080b5908800c0b900c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 587841034 1250 587839784 587839793
    0x10090212010c0c03260610030e03070503090a050d0206030f10050301180611030c03011e15030e100204230301020906130807060c0305040e0601031104090b0f0f0d0209130f0f 76
    0x50301d002c11031784d9003002c507100d050300c2d0022034000000c0501d0300c40c0030f240c5241c00496000341c0c409029001e40c141141c1d158107482c0340c0240d40c2d902141e20030380306144100700020549807580402410b0365000d0880c505644403c5015900381034080c2c040d0a2116a8070404a1a03840074403c5881809a045140704806c1c1c1e42d04180c0b00b11051460340d83d180a00c00c208100324203c0e60790841c1e0456072111038250105d403c84210142d0194140c0150242d5118501c00c0074482c0c3e45070f0003d40c9840c0d42e6100340c0c0c20920301c9600540480c8034620508481c8102082c0c01b401080f0702040382081348002800144c80c10850600203a01c60b44800c4124601d084465002e110004007080520b0241c11142898552031501d91400341080c003da20072440d80c021300000103006a44250403960f0110340209042e526281c949103c80c01503c859082180991711540c840c2c0750910b07155107040c1c80d0050103460242425229024080c40c900c00424a45040d5001114030001442c003c03031480c2e00a002e00c4802650519901c1e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 587842284 1250 587841034 587841047
    0x20316050a1203050a11070b030f0103031b02030c040905010204031406010f0909050c040506030316110312090a0603200301090c0e061305011101110f0301030c0608040510090212010c0c03 82
    0x1c0094005000c2c05030000180d08a811110940030500300840c45032880c519142c40e203900c40d00a034006c41400300900140314080900f841c140e074421345410484000c0c444002000c4012540040e5041c0c0c0b10405d07440c0d40b4106a441500202d000c1c0300050b2800d9120b07107464941245081c600c4500341e0002004000f0323000c00d490b038400540b9960b00d003842400b1603a203c1daa500c83c040c2248901c52551440031800c1540e04200310b4a40b03085404a283c0e451805d81862140c01c5406d10b0b4490180c050b0208003170810f030101c0115052600300038020741d0b0350741c01e10300c048000704000308070a9580800490003030b860b03505042c00b85008005006000c5411004860001d0000401100703440c01500203004044581c030a10011000780d60081c64030300b01092600c0700d001e02400c0302094600440c01c000841200c0c240c1104001d5068034001d40783e4411842e07440508649400080300d020303146c2d400803400b081e44285583c201d0141180000c1a25a07440200c076509802c55501c0400400801e01025244081580049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 587843534 1250 587842284 587842289
    0xc1b03040e01050108150f0409020904260f071205130b04091109060a08070e04090b160203070302070905060406410f06070c0e0f01060210051308070f020316050a 71
    0x64008145d0502c003902d01a810b0181b501a8401ca0350b8032180340950303c4581c000c03484141c0051581e00141080c0c1407180301616110f080b0400844c10040a00011010504940d0f45a000000c0107160040584484400c1c40920035418200b0804104107544016010b40d110090320011200b1641c851420325504111343c12100c02d00a4418284a428a150380300001d8541042070740c00c1c044079503592000122040038010340b0b0316500a181c940003e040c4416151818840c161001c1380f10f000058042d000d0341d6034010044000c005900564040c44512441d4220641000010b0800308026444200c8041c2001c10008000f00c0300e0b543c08582d4099001d07182007220311a001070498502400d038540405c40580e0031340c06030741c0940c0b400900e000c1040480c04c4590020321403070798811400d051443c4134400d0b01d03a00b84200001031040071151503c1891a00c1860b0060801007003c1c000d25030990b4a0100c640c02904059801503040001900561410711070301d540070241036441e030015070500c030401000b4101074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 587844784 1250 587843534 587843537
    0x106030b0a0603020310050a12020306152b0204060b0a02061b0f0f0f0706021b0304080a0b0601020a0506151008010806040803250302030a050106170a050c1b03040e010501 75
    0x156024a868640d207004500750b9020b4034000d641c0369180c902c80301211082e0350000340c100319031080000b0500e903d50340500d281d600c201d042d00c01e140c403410103892406481c5400c1c16809808202000d11111049a050881e203100c1810201d044507a0380010f003c4416a07070100c40f110390005000c21a5075410301545910079080e030000b242c03c1c1d0400381401018000d41d0f045460000b00015a041c0007841c101c2502c034400da610355a0360b40c41b02149082d60194102c03140646407061002d8031300c1030804000c400e99080c1c804080c0100010380e1182c4580300314030704c05890181580500e200d0200480d0042c448644181c445202c8020041d46060500c100c00e105104d4003010800c0a00060114650109040e90003030382141c0255100c0e202c0c608000c1280140011000c04505480c3e0316021142e05600914441c01a028080046a985070000d498200c809505004817802100006601500c07076404603170003000d1320800d142410000c284251522464102465990b400801c0c10820200e5400049000d844207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 587846034 1250 587844784 587844791
    0x405120c0618060f04150e0106150305071110091403031806010501022b0212070f0204110f070246080c01020a0f030e0a030f12030c02030904093008010603 68
    0x31041c0c0c213244c100190004142c0100b902203a081c1089507007003100440c8204008100350f9544815814406500307020000209080c0400121000d025240700c0c2c10924058000e132403c40015040c2c84028440403d08880342041c0b515425070340482000914031400d10101d00c100c01c8051000040d1500e90140c3c0f004c0e04642c000d0042c8041d200c8810030002400d00c1e809074100c0c00900040c0140d050104a2419040b41e0718080307441424400303207803071452030b441c000d40342044040c001d21501c40c101c0c030030028214420300003040030000504100841c001d001406450a0820300100d510783e101230301820b4045000d00700e444524100d0b10610446100082440500412005541c1c2e80040d40b40e51100740042c00048070044841c040c14080c68825800c40300092100741e45544a01d000007282d10400e0341034600446040d020f0807502c0c00f03841481941502c580046d42407480d40c000300001340541104c21242c120025401240050740f8009403009444500303802c0d03a080b001004003c10401c4141e0000082604 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 587847284 1250 587846034 587846041
    0x604050a1a0906130e1608120f13030203010c02010f0b0d03020c01051605030a030606030c0806010206130c0308040b1c050f04020d11280902120a02030405120c061806 73
    0x40180741001c0641c0d0903140a1460360b0340e00c0005000c50412520000d4031030420311783c154040004641401c618074805856541c2540352101c0554400d00c2c0c000a01c4449010803c001c0031540c2603018003c4814107410703d401c401c3e143e602113400d6a116001c40000340c6e4503010b004000510b50700800703c0f0285c1c00c2c5d61103401140f458800940e07855206401c0c41c1480400504a8842926044003042854002080340c3c0d4840c0c040d20300034000c0c9050f10446c0002880d010340c000da224443c0e0301107401080141d00401068a40c0c6e03110701c0d64441408400c030340d520b0716001c0010007e20508007a00040c6000c4054a86400503054118031140019800010003450b00d420000f40c0110b603013003941c1064059540c0383d840115441e0190454160f603410a5020300ca103854a00f60001c0701252000001002250001d1183d841da061400da026144100007400c010500003103210695601556100d405002110510700d0b805e0000c020783c0e803007040840c1568100c40100100e1010020702204d24190045c0100f4043c40c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 587848534 1250 587847284 587847311
    0x708070509221a07021b0d061e090c0f06110d030b0307050a080d0801150207030f080d14180d0509060d0902060f1e1206040b01022107060e010b030d05070602040b0705060604050a 78
    0xc0715010010140396907050000c910f07149d0594031030000c46240500300920700c1c450810712915541803156030080410402e000c10058810f03140130403d070a0410062078034141c2000b00341d010303241903c0700030f4040c8900180080e0340e40e81c03000b0341030040c010368020346028200c20301d0080041e01d058106012050003144070141d07103640000c40c801240c0e0030001c060b24039182840c11030038900c100c10072070303041ca03040c030242c542148004c1d00600d005a0106246240e04a00c1041c01ca80b50001c3d0b111030b4001c60800e100300507560030144c00a1000c40c64240c40066041c083d41d000821a811490600c1d0f46010049208501c000503116100d660705a030741e09490038040b0085020b032101c81c00800c001d010301d0311422401e4213a4020403816a0b8900582c9114910611410728400c56030010682515000d007130505189010340184586111014003401401c00c5401da0141994554400e100071202558200300000b44441d0050181515500c120003401541c2444000c00003610400341400c4001860720b019184500d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 587849784 1250 587848534 587848549
    0x1401050c060a02130506030403080a0e07060f11030c01140417070b061201060806181b06030402010f111002090907020111031603020d0504060e0708070509221a07021b 73
    0x140d0140b409a55407159500081482816500c0940c110201000384003c050304501c12902c9041c00b69001c01c858424010460b5550b00170388600c102103668000c07265880381c850b0b6910b9040c120f8840c100c07840c1c0760007101c0d01400c44400000c42104016071805010401ca6002c1e00320000008409a050030704549448030003042002400562140c0140d42c00141101d0003034100200400d4440d065801c01c0c5131120518007618419840f82220b4000c00203034443c04d034040c0c0030640c03001002400c06811640c40c0e078019a0480d44c100b00e00018413803102c03028240013404221172a6800f20417980940c1b100400c1c81030184480000d00b5503020769040507410070300c0302e10311030540380d01c00300c00c0d00c00c10383d1303461211000c0d4002c6c41800c0e0305da1005420300c802c000a00c20140c006590b101d02520490741d0a50b0f07220405c0d0385502d014050705500030032500100d207901350740d03501440b104010207401c11005082c903a1082210300c0701c1d8480400c0c15001c0c0b402c0200b01a0140668150050748640082440c081c5500140b49d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 587851034 1250 587849784 587849791
    0x50907031a042703030f0e0a080702040213030b270f0615042c120c120d060b0c060703060b0a021e150f0a050c0c06151302040e011401050c06 62
    0x1c2d0b6480d540048584041e1100c0040e14003c04180b4040030340c1401c0080180503518900d070241e0f824403042c3d115501c400035007441803035007000d051400d06440340c0c01c01c406980070003030042c880000d0384000310215003d074070a11f0140a200f0400001e0f1182c580c08084a06080d03840c9200e1a000401034555560b03010500e143c2c07018000301c00e42d40b10000c41e00010020141c95084801007404414031102c20b01a010181180300322000c00c03561007482915138481c80d40310790f01032259160031403c0c0d20240140032801030000303007070001d4001c03883e2502c800c03d00703034143c104a040c95243d6006e10180251150144a0030019040120200380740074501080650360300c5501c40c103c80722403009d204c0085190000c2c00000001d1000f180c8a10711804d000f2680180050107445401c4c0c1580b1f4800030458400c04041151012507824022b00890340c2d81842444140c41c46241580c0c00111441c2c90195811180c4000c1c000b03003070110300d024020350412000ca2048032205104e181442001c008901030380100080700e991 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 587852284 1250 587851034 587851039
    0x60209062d04212f0319050703030309060219120605090112080c070b030702150c04030b060607140d120513030804080a02012a08060d2001020a0516050907031a 70
    0x25107800a240138080000303010b00e28a152461058010354800c02c030603625204600460840c0c80ca860865640c0d0013031060618002c00580c841502040080d00030b4000410850080c0d070018202070100718618050000440c00700001240041904800310036803161402410050318130403015070509400d902102c1020001805055022030340020301101000800d0140c0071201c0469260300388950007a56034800d503040600030a894000241c045030101007582e04503500200c1d201002d80721401845459803280e102526401c5c0304c100b0b01100241d040001045468030f030741c0d4001051a0b0440b48100700c400280a1f0803108030421155000b00c5c0e8001c1c0324640094000c1060350b69404101c0d41607004080c007011815907041910803542c0e5003164550217440c1d41005441d0340e001030382c515042106440c0c1312071004044c0f0310480040d054211201c80a06201d040600454001e01c1e150b8507460303c2c0c101e49001022031501800800c0c080d90034444080c4d034100459007424410442101560342001102c49405070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 587853534 1250 587852284 587852339
    0x5010305060c1c18020312031605180406171005150118030f08040f060e030a08090105040302060d05090c15030610260f0c130909060209062d04 63
    0x1100c040c5801000301c0c0d0041201000c019082c04c2900e01100d01c0010382013680b00e0301510840161b40488a000c8a201d00d00a0411182510300c1000503100354015649011a9407070302c107200d010303540700da100381d0f00034001c0c2d110320108500c900f204084ca481c40c191074203a122030520f001c1c00400b60449024001082c02401c04942210326442c465141e070429a0002d400d4021705003442c014042c6810041003911124212499015210320065600301c80070308c1c1554140e440b195160011641c04800341c20b481005241c02e62426907a078000803000d810507242d490010399298248201008104554411444182d800c039040d1550040c1190305030200424080c080c0c100c1182907038001d40310b041c606451b0031042c3c2031803c0c2c42e401a0340c00881004103e5584a0440420011500c000ca00c0d20a1342d14000840c0c000ca0501c2e41401182000b03045412030032541c1c0790702072282c2c80d0b40d607540c1805441241003040320402c0050704004051907400d13060030179215101e0301704001e0086568442a022031190301040d200b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 587854784 1250 587853534 587853547
    0x5031b09090103030807030c0906020d12021905090f03070b0712090e090102070218060d1b152102040b0313020d1202070f080114160905091303080a05010305060c 71
    0x4109204000304030381d1019030310340040101030300008103034015601c40d07038104000c20b40381600b910b054042e809a0005a8400001f80640c00c0c070500d03802c8100c8030300207005818000c0070412002c1c0307044030000030408100040340300f4209040015107a0308038801100141350711890203c00424134495000060302413034500002c0f00500e4090008003000b48400000000e0a141c850340d0030b4002e410549089103d07800b13505c2c0303404030540c98200d02800b0f8440149526800b84296032600d03000c0c8000351000044031060311002540400381d1075040e0005007207440710007201072445046e4030120901c1942422161041c0030138022841104150b80c4d00203c070850001d1905203500004100c410b00c0c103402806075900400780c1d03c95583c0400c109007125048211030b664503413944d522074265614503500c440c1c2d03100b050001501400d1081d2800c85007183c0c07420031000164603400031426071941115500c07100d0b00310503800b40801d82c0c4540341551021220104101650444e030310700c0c0d121000074001031460000031691 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 587856034 1250 587854784 587854831
    0x4050709031a10171504060605090601030506130f09050d020618030712034802010b0303071b09020a05030105010908031e0901210e0f0615091008100e010f020a0503 72
    0x212100e05802259400140c0342c5880c0a0007d0408d600655008010110201d035440d4002d025243c080c40b0010540c16030484045811b500030015481d10384000c50301d03651142c011a00a004098118a455001d4605480c0c141c9402c02c011018080d440349540c4100724071000320f030441c800c031036240c07015140c04a01a4003406064408001c0310301201070302000b014800351405042e55207014032201100071b4082024a10005034201d4613050706258058004120490000703240f41440021441c0303411034442250384030301c0d605040760460400c00001c074034000018452507070410000d0004010200003113240c0005841b18426141828815035110000894060106c4c3e0090102416180c1c0310702c001c003240e109800080707024003046030b44000070780030301002c801c0801008100c4922a1500802250003260b1503424000e10200003811404100948180460001c01c1070001030701028007420b010070001c0d0380085d441c3c03c40c0c00071220030704030500c100030b0888840c0d08132041e268801646011a60090000280c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 587857284 1250 587856034 587856043
    0x1b020316030e131509020913020702061b010203060102070b04290405030a26040302090c030901090218071e1b0203070b030f0103031b0c0509130204050709031a1017 72
    0x10540c2c01070b1604080101c6148950202101c400d01c0c41100c4000743c1d4940d408012803003001c00c15034105c40b00401514486184d50001c003032050bc00342c040c0d0b242a501c8802080b01380d1180c00a0030482c0d4000081c4038056a040201300c0150044044081c6010319203100c12480507041015001c151184180f00c2d0002643c11060f01d0007408050291044024075142c40c81c0c44040035083d1442200140041c1d10300c10741c1d0002a10b05030ba501810002c043c0d100d4002c9204150001400c000e515900d0302210780050300c41900713418800510181041e414109498040c1c4032100c45001d01d200103220304401c41030190f010b4a513404c82000e03103036644090006400031900f84081e6070086204003000000b80b04000c0700030641a03040302d00a69401c64213042c281c450b441c01c0000717404050000e500700c090a014901d03106030055000000040d05d0040d103051035001c0740c1034440886600e404600da0090810902c030040b1000201c000e04095000340c00d162000c280c6e90002d189000303d550340c001b9106100450b280401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 587858534 1250 587857284 587857307
    0x306011805060d0c082104060203040e090705130c0f030504020f04090203070f0f050112060317030604150305060618060d08090d05011107021c03020601031407050a0b030a1b02031603 80
    0x140e100d00c030549845c01140d4070724040300000b100c0501254081c0390a103814069800741d0317180f80d01840c6814a03107188804000070160603024a0f01405900240e030f0707940d043e0101013101040d440411f41c418851340c050a1426130030b24100505041000300700069603102c0345585c5002045900152602050010901d03018054000c8034840510200c00f04466100d0880c100468009903100418461082240f50940e00d40e84030003132034022000c5102074000c06007005160b003c0400780c00080c48462151005a403d002c80c2d10a89460700300d02e052084900b85040045148104810b801e013003400d002010541c00e009401000d04584004244080c250355a4111002101e408c00c0080c0035200d0801c40400196100c004100c0c0b0604c1c419030501d507030040440701e0003a0a5016005401e1036846c40d110824103000c034120400172806050000714066840040c1f900c06003522800762512850508a050b040781c40d0311801a84090300c401c1d4003684180e001048451000c040d9440e0100b8814903c0c065603045a0907 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 587859784 1250 587858534 587858543
    0xf151002030c120c070816060503070c06020a1806210f140106020105090d1103030f180d030501030c080601080a110a120b041703060a3c03110306011805060d 69
    0x1014403800f500c8003500506441c0a03d5420b4801307003540d611009a039000c400c04804810724000358200080d6010380013a640c8004241841044070641d0b507110030483c0e01024803040030442800918441c070303500441070300c0500a14202910301d104101140402d11180302000c2074108d031581c40c0b08039581c0d0035800051420450400d00911035071a000082e0107410212101d80c5503100c0c1011450029200d40a5034070103406460141d861504c44004941248600921101e201c10450b01d280310102010003040c0d0700740701150340c00612541149408085d484180d48501c60591107000140300610020641039003442d403141020888003240004240700c80345a074003580032009007045100511400700001391145e0311941d4107400000020348120858003003502c80d00d0b00400c3c0303910706000300060350340c41203000303080f0710036000030300b81c1801d120000c600801d280d640d0764803000e403002c10802c01d400c0310400c000d45088001c0c1c80b42c0d40c1880c54240c0b24201031076055a180f0740710804035040713484407041c501c0c1c4240c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 587861034 1250 587859784 587859793
    0xf090602040f0612020306060a0f020a0b0a27020105040b0d140117010c0216050d05120c0304061205010b0706111204050d0f09031e1719080f151002030c 67
    0x1240c8102c49440c295108000204209410102c07260340d2510071a0b1041030020b0485052860a113812074403120b500c80381200754130540f1010310116407510302c880d205d0301c1d0982011604e114000c0e88003a03203003c0701c1d800c802ca030700b1103a01240050384c0040a0b00c0030340758140b00ca6501e40c0392294000010300394584c244041c0e280310f40004502e0100a1102c1100c0b40a920020701c40301c0f141c100200d0f81e981c50a8807209801c00455400c0c8a14134002d80040c2081d1b001e50220354108040d2420a080c03a4886110700000343d000040c10045507030000900e4940070609401086a03600d0a03440c04e0301c80c41440c100421440e07035503c1e20030703043c59883c050b600c010300601c9a1003203230f02d03243c41c1c032640d80c541584c0f922003c10740c2c84407060034240c07003914650305076640080a2000092580c1d103200b0a80d2a49200700d80c604001c6078001112f00440c000f83c00022402c0c0715104c841010310328040e029040203080f0010408004007049400c04a00b000016440c60136584100815145013040741940229050a00103004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 587862284 1250 587861034 587861039
    0x30d0806011b0f06060b0711060306030a061a030f0a0507090c0504030f03030b01110309011407110952050c071e050405040b041b0b1209010b0603070e040f09060204 72
    0x20f0852050b883c540c0b26840070851661a031001c1d00c0c3c1401103100040c0ba070b100c49030340c000b22400c18a01468002d280501120400300d46565517405486140c03850701000d2000440d821603d1801b04400340c1140c20441c042c0c00c0e1b04034140c8425840b4200c034041e4001140d101c0070080391240c810803c5600440e00040220138116540c0307001800b400c00741c9040380c0050f03607412844200c5000401241c41ca030348d050f100e401605070344c080c040045030082101030701e01d910701c8142401203403103240300c081c41420452000c4200b02449643c100520000381040c284000c21f0544001d411070098400e0b07645040013007103015840c01413031002c851500c988071103a50a40074074000010303030f4150400b0381c0c192803e404030002230250300e500c2803004849088030050421020301010401141c04860350780b031000c06180320408800d4503080c69071010b80c0b00d40d100003082c81c4060708114544000303200780b20109000308c1d0b04900d9401d041070f00800300c1e500602860300c1552b44081011421885074450006980e01c00d4083d5115075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 587863534 1250 587862284 587862293
    0x40801020a08010f051e0d12090626040201080603010f1109120d1713020324090c06030c25060c091401140a0e1810060e030d0806011b 59
    0x401c801841c10100386041c0000c80c004020181000c196a4040e00700310000185180c2001180b9000d200036400c00c40e440c40207000728401b42c002c000340c1a515112103183c0c23894410000d16000f0788041010303014000b2108580190400c800c202c1d006502460000d4058441c4000240100f1100c00c40800711031900540004203000c210150003108000c03641c0c0103070b6910f003180003520f80c2048407680c0c3c0000c1180800644801000c2c00e265042064095100551a603550110f8a13181c4886144001c0f03109a0082c1061644855280f550201c40d00c4050f0200749141e00100d1114040680101d50302c0001044c161000120303200180c51804a000d17860105010500303082000740500d081220014200b0000420800304c0015892905603040c8d59213070340c86417040c5070001c00740c00c1101600c0401420014000603541c4860444c1c00c40c0071180340c000001e04022101000200e466031003002400154070709210550790106071810001e046080c050405d955010048a03a01c94054a850601d000040448180b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 587864784 1250 587863534 587863537
    0x421170901060819110d14070e0f0a0b0a06050a030b0301140906070203180607020a03230c040902010806130b030303010f090605090c0a030e0712110406090e030703030c0203090604080102 82
    0xe03210142a515003801c01d40c0c0c4054100401440a400e90090351015400b501b00000e040c80410700035800304041180b484072803810800d15600054441d0400c0050090080d0744030016904101060404c0251000140204064609a10403002031040118000100301c3c040d0f004009110b5000300200600c507010904400820001d840c411110312071040003d0680e800081250001000c0141c0e610b80c1c91094003c10040d680301180032a08846200c0b0700000180d03000350710f200301c030403000b4030301d002c1800c03954484d4600f80003440c030b0314416801c0060780b00140c1d0300a000e0a030018010348200e030005541400d54000f41c01407071001d94062200100005074685a941c6200980b50b1082c030511071582c0d074404211046405031000009400c4c00c2080c900c15a0280e805035800d00c080c00d05641c0041d60f120211100002109000e94080c00480000d4006180a10842010744040c4400b040382412a400342035880c00345010080174103954144022850713000b001555821200140030903034a40e110b01486000c2d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 587866034 1250 587864784 587864789
    0x1120c1209030507140303070912022101020901030f020421051606082a030c0a110609070603050619170c2205070f0210020904020f0a090815042117090106 68
    0x60110702c00b1038034550407010080b02d00508d101d95a52034040d003400040c1192541e1044126805600c0c4512003551010303000c011200b1101060005031070317010f81030015080c0c440c8051904a09841000306111007107000f2602d2414119925104e001802180342c101c0c6800e0300c410a00009590b150000948141d01101180c840c02d075090404203800441100c1e50303040704100d20700e20391150081c40016134400601000d0603c0c61824074000703100900e0b02000600b060000d0365901c5680c1c0001340b09010003a00740c080c60390081801c0e81c0960981c2c14030820024400b2083c0074416204042c003d0f03090403203604200000d2003090040090114a41001e140b0713031006070020b1b030701182c9030800d170000b007031103000700094071040c0c0050f00607115402c03804000800035400015000d03800f41c0d080c000408200c80400152518035500d440e8280742c1401e09003518a442428800301c80302494200030040040c80c0d001241521034242c000004903203004001c1662503c0c002c1201401c114107000400440d404150000c004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 587867284 1250 587866034 587866043
    0x150f020a0f0809120109030504150c0c0806010f081207061e0c0314070203090f01270902040f0e0c07110418060c030f021809060a0329010b070201120c1209030507 71
    0x48084540801800c0e02c0041c04003601103441848100034ac099500c4c09800c1c03c0c002860000750f400302c1582d5414a81100d038100030705a50202c0f00500c55141010b224101400c61038006250707051000c10b1040140c840c824000300701e542c580c8011212403440320656252040c40d11030a115400714190003c00400c800a60380000701f01040209030a58004012103400200181000141c80054401901c0500300320120301c20320365040b0580324003c0760b80c0d0302007070103003442c54400344e9540d281004003054010150460034142d99200140201c1030082800c40d00d86c0303540003070500c0c000202d46000600505288082c0c0400c000110f02c404100b00003030780b0410901601d9142001310b10803a18254003203001d031800718074031012072084010b010b01d07000603031a0340018001c00c1180c00903101d9648480d2000a270101040c1e41d614603015a00c0c00385200380c06809407080074406410144543c0000f400f400c0b2200e0202c8142c1d950f889448071071072041c880c5406c020042e11b8140840d00f03940c0740080c0681e200020648 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 587868534 1250 587867284 587867299
    0x1021921060303080f0411040c08040c0504060f0e1902030a140f1e1b0a051810080406020a09050616020a05180f09010b101d0a150f020a0f0809 63
    0x1200306880d803040000b0790740c040c1ea440402d030356141c0800710200c00241082c1c3c0c0c0e2882c101c8035030041da9960700609440d0202c9542c0c05205050500d4040103065454002c41c1c0302c0d504194080c84440f40e041003403001c64101d00c2c80e91016494040c400301c0c49141109004140310300002c1003142804094211990850391070102d248295030f11111001c01c1d040c00d44010300c014246010314414003a18140c86604200d400f60201c11829080701a0000e5078401510318012070f40101c2d079000301000c2120b4041107514240c0d00388a6110008400500a82c0c0081c4014003c540c00305070480510722440e41c0e0005810040c20b8640d0701c0201040403120001ca005089108240011001c5801d08000707601c00c0d81100030042c02c1c28181c4840808ac195454000e1203485c40350360322507030805c0c01d99610030403850404481c3c403405459800c4106607810324103250f501e10b0041401d250100040b01010582c1e02503000ea17490031001c601103800b4120304211084502501c80c02c80b611920051000c010010703c0c0390203003203c1300c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 587869784 1250 587868534 587868587
    0x2030a08091011070b0d060509102301080c0307020a05060702070f0503010603020a0512100603080301170307200d060e06070219080d090807020603190f0207020f12010219 75
    0x220f58a8050321000540c503040380c2010007032100164094540840d13070010109540d42c4510106210840c01c64a44240d151500010050811081c00b2036412107100c00c84a09155081d00000c0d00d50400030704506495a000400a02c413240b00303002040c41e1503800015240c4030708207a08003d6603441139005000388284e00c0d0100190130710f0140b1603481105e0380941680201803a020800c15602c0c000e411400c014042d02003101e0300024548680405103200d0144e075500ea5042c02201c50075203c0000801e8a00e60041012802203065510126110a03150301540000d9190b400481e04c0b8801c8800c0c011b140a0a10700070030150040428018801c80ea65406c40c0c481030200c07241c0344900d00000c20003030160714080200110b00d18964010140310b41c0a4118246080b10f290302217080c6034011180c2c00350001c241c5400b03056116003800b034850000c0b284002036051880c6500081c55030300480c40c07601c2c0300303203401c4100740c440744401e405450102d04500c032013403401451103402500d0a240c607d0241c104182ca103425 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 587871034 1250 587869784 587869787
    0x3161e21031e0e070b0412150501050906040e0c0301022a0c01080103030e150d0506010306050906030d03020d0e030c070e1b0d0906090804081b0f030a02100c02030a080910 75
    0xc06000400550b0060900881c0c0109603000706820034204046005035803010a5903043c180042c0001c000100021403024010305103110000d807640804481a42007000410841e81c42003006500100c0448001a01465100c917480c40d090442810940650001c074040300301c85240050340c0c41c101840c03c0d41002e1a44800d00143c2c903000c01300c100301c0c0800c030b5050041c000307c0c2c410300741e541603e0000740000c0d03014038000b041401070342c00851145405a0321581080400c0d6414000c007001032906a8441001d4280390b0002900c03062040e00301020551302040301c0100442c00c0d003000c1c03084a680c3d401c0e25610502c1d4500f030b90701c0d01c4007405907455105441c00850b102d8400e4046500c61030445040e107031f06000c00b40880001510041c0e0003507070015240c084041c00b14042c480100020601c20001300843c2051651742d40f000728590f06030700d10451109400018a0300c000c0f91405420f80d040b9030703c00d5442210a02030f2404211680040c1d054030030f421601c020000d0580080440d50030403182410304031780700d031380 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 587872284 1250 587871034 587871041
    0x90108030405060a120e03030c07120804080a0e010c0b0c07120c02031011070506010602061b090303070305073305090d0c080d0906051501090f030503161e2103 70
    0x6880c2d00702c8002c0016130940340c4103603c0642e0103107200d4004240112000c0401c0e20315001a20030b82c0e21214006800303020403880c00644d01007a195400c0103800e40c07405440c3d0015a004482c03041061112052081c00c0a82c480c0c000481c04540c01071240c00c03035081c144c05518407030b001080100c5a00c03128a142200c203034010049004500c0c2e00030024001500203090aa0140038400b01d10020078405002010004409100b6a03000e808194020310311883e015a16448a001c14510500b818100700503c1041d62008011243c5240e054140559192014a0710f00304484403441e40d401c007500100c44c0890000880605030400d0340300b000040c0042d8440d0b2400b20385823280915100042800340303454000140c4140090700c0221b0201a000074541015122241911812598803403540c10007042a0015a0407414003030140c4003103151020305c641140d071050b54034400d110015400841414039002000710312496807100c271110150801d02030001e481d0a092010010f110a502e160b10781080e1030440d4409d22 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 587873534 1250 587872284 587872289
    0x20a1d031c053108010e03030f011208090414060301051303051e1c0204030303061d060904150204030f0203060a02040b0a14160506040c090e1209030721171603030e1f06050901080304 80
    0x81527070081c5d02e40b0380d030462208000c10040760f0840c4248819481ca0303449105503003080030000350392041841c01504160131140f000b0000044890015403403004a03074040c080d070713004803012148481002100507035940240240b41000a0524003072803180e900854940180007228401d4800b0304c061601ca20426500084802484852800d9a000644145042c03000341713800900800760051003c0310426038205030781c01504152988080e0341c08960460800300300f0154000c014480c110704050500c0841301d000d03c28075a40d030041103403d0040f050094416000c9400c0e0f10011901c0c01900003451800540716001240d041d10030030400040001d000110340181e444040108010b455010680300000c00c1d641c100c01445500b501c80c0d4000414900c22580c3d060003605080b07221607030b00e9112440c0c00c0b05140d1248510031859003041c046104084600c03407400301c10a9043c00e01107825151440c03207a2030301108804000700d540c00c400c2e0048004031300b94001000d8a03429550a09240c0e01d40c004580e4178031491 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 587874784 1250 587873534 587873551
    0xa1d0d0e0904032c09090a030e0d080304030807050405030a060c031b08060607030c0b1e071106062716030b0901030c050609030a06020a1d031c053108010e0303 70
    0xb1003122850342400440344404a07804400c0e022030b030710250086811709800306d85c4140c16030300c25802c0740c050680000712140032070b10444401002c1545551041090b000140006003030250120102d410140100190b40103804040c0440e29803420a0500b98040d0010141c082d020038500352212111840c3c0700400b202d07212103504d94030701e143c41e91028040154400b09064080140700203400f400140e0000d502400f842e400095920070854001202d11854806400041400a560100b80c0510000b160595018108841844c800c0b040c280c044a290310b111820801026240d030308200904084140072005242c5903581007103181200400c2c044c070108280405490902d5940b0200400e1600c040100750f0580040c1c00d8071061215a511881030380c110904a401040c07002d0081d2500c900560130b40d0000440840051010352000107038108111810703104c072000c1100000da0242481c1d00003803552115404652072020f81031020014407005420341c00343c40341550920008004d840000004d59004560b40e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 587876034 1250 587874784 587874797
    0x61103040c0e0a021c021e1207080a270b010807080c040b1f02100b040605090a09110a060503270d1b06060902031009020418050a1d0d0e090403 63
    0xb40b91440155600061819909940800001900058804c83c40000c80c1d083c44002d0f854460030403a47e080d041d904496090005020b00120015500405907141c01803a10304102d406511000818030242240305205280d0240b03c2520664411203004002e1250f400340501c40101e03600c640c8082e03241d0300c0501c00c16000768001c4e40b060481d803809070710100303103c00c00600300e040f02c0b1542c02c41c00c5200000a4020302c00b68101d07610005490004e030083c03108009080300c1c200122428840018003002c405003c6508081d624560030007000b120301d40d401e003d80c000500c3c00da002a40d5086c002e00b203a104407102806a2070720205804488244410a030902a000c4080c04c0302020084c02218511205041608004a00551407012070350074401c41019000b03040000d80d0742d01d070800f030b0389413003007075603846018900c0c410041003016160750300c80505c1005220303c002ca0580c4844450318040c010090200b208001000f880c0c01492200150310701085450351101120a892142000846c020444011700403509 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 587877284 1250 587876034 587876039
    0x60806070c140f0f0f01050601140a0305100504110408100203040201350a050108011b08060105090f03100c18180f15030602180316030f05070e0c0403061103040c 71
    0x2030b112001d03034041d0703040441c0d40d0300f400300e464640b4010f40119140400e8000d500d0341006000c1c20b000d01a031255007800c00d01d120100d42050070368140301d0300c1045000c1607030725000f10b00100030784030328000104001032092001c0175050700d200142e64020b2107106014407072040216045440cc4c002d6030720880e0141c40741c2d040080385200d030144007181810340d4510441c9000403550155648800d0073b01880e111500081c456040902d82401c58980000c103484003041400e51a44c440d502184180d4450000e04c2d00b15100c015a070041000c6a400800b01e075458040c200c01c0d58400d00d01540011a415502e40d2490000c035200c1e0f0185075103200b80e0003604104c070f1780700f0880c0555030420303008041c002c51300a2000950000080009a034014250000c40785a03400152042c401c00030164060f0208004501800d6080b540b5480c4040040b21440700500149030312180e0380a002d424020f402c010000a124843d251500300d03031400300b0354003500084401920342950021b102400c113098034896940700c1200748943d030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 587878534 1250 587877284 587877293
    0x3010509040212010e07030317160f110303040b0a14150616060516030606030b0a091503020303040b12010603051e1b070305031014030a0b100b07050a06060806070c 72
    0x600c000d00a980003410701c060041d02e140f09118000598503080040c1445d00d04500c1d0007030000c14580022004418440207001c204640408461a07861607410607000240c405441503804500c2d402002e0164003001c400c0005016084290b188180c9418108005188814603a41803002d0150386001080141d0380f00d000083c01d01200900c404517039191103407401e24050380e9000c1550012200780140046c1d464601890640600800016005a060600c2003c14010125200c911140b00e5000321036280c04030f080003080240080341c055070f00a010340c1d82d00d0781c81c0c0ca45030f40e01747e02c807003900c0502c000e25400020700e007442441824004d820140b50f0240124245808c0c40308002d02403e03d80303220581d04040c1c020032401d0b100620b4101d2098440310380300c1c90540500700d40d0030460f900501d030302f84941c0310303401140d80e01042c51394103154011100a800d48800c8031034003070b100b29600640300c100400101e0005002c40001d10018a500c180000d1103070645440006884900a482210114550088440005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 587879784 1250 587878534 587878549
    0x20f0d1113090c02060907080a0f08120f040309061b02061c0507030b0306011d070503040c05040221130c140409150c0f020601050d141c0302130e010b030105 69
    0x65400d03641600700340001d55040108503040c0d0219500c15039640140ca035240e014070006038400007500160041038074111a00d1f0329611040c000800000e404280b40040159000564049000448192505180c9154100180841680c042e408140d01c1100018007901c00c8510020041000404d403a03510303125420b10081c2c0d001300103030b03410783c06040c800d0317412035a4503100707041c0308109030794011401042c4e070381c14103003000d0041e007200031003000e01e808442c0c281d9242c2d00b90300d41085552800c9560390b981c42c28032a40d0440346410056000d4000901c0740700d0350200a8200c1c811024501c00d81e9580c0d00d410000705410310b00c0748001081c00f1048001082999410b0104114520000e000442da0180955401c1e01c3e042d034810072140c8150b610001d1040342030780301c040b058081c5410300040840354100000941400e0050340010100017180702c4020441c0802c1c40b142c402c07040b80144c1b0a6031000c1401010303000c2d402c0700307604c44456079108000154172440f00d03a0541c101c40303180310300034916404c0800780b0010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 587881034 1250 587879784 587879801
    0x1912050306010509090709180b060a0c0206070f0b04060e1c1b15090501110a0c0210090b0d0608060907050d150908030a0e0120031305100908030604050a020f0d 70
    0x148030051101d803004c2e8035041e100134459030b0300b50366504d0703081e0404884944510400c04840c140d141741041101c0e450b02d46404a591076421820000301d07009481c03000443c14440c0c0e901c001c00c82400d00b000c5408000034900c443d40a60b2044006015100c1382941007581c5800251010b01c00c03c059411350b00030340d8090804840180c00301c410341c0c41380348415100d190205004506060409598002d10414060284102e00018070901c0d4514940201604001d00212038201c029204444071640a180d280c003d00141001303008900086494040c003030814002040540300d100d000d8002c0c3c60004451000c0414564152a0014440c0c40c0c949010307102d14602e0306160240d121015030f40d4a080004c50440800745204100c0c2c1c01d008245c440e025640142500e00c0c1c018403542c2c1030700d800a4449859400c906480c3d00c80700c10020f060041e045070170550b00d03040854000c034000c6403500c0780001c00e02c04510000c0d4458401600c0500803600c40d40c1d0500203e12454100caa03030303041d017400200c0f02d0300301c20b0700b22001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 587882284 1250 587881034 587881037
    0x1a0c0606010c05071d060f0d0b0103111306080f010e060c120a0605060417070b031504091719090e0925090f0c120b0a050d1401090f020102191205030601 67
    0x4c400d5190596030721910318404207841c1804003202003044601e00b61096403007821081c0c40081c540403d03907940d804805018000284404c0e0034a165000a89030180200400c0044440c2884440d988618158803407200d40a448019420303d90181b110030310018181c2c1c0540b029405007440c19012800b11310200c0c90240690030669118540010596142000761015001484c08101e51005051401e03191240c00d07400003018580608c200035903088080010080424140c40224901c40540313490740c401c00e912424444e003881d0201d2614021b156050350880342d0340903500d4180c0616150048084c03035800494008600b9482500b00074101c20403030104103c0780d4102c010860103162030f201e07840c09588400d03c160420590741c40c81c0034581c0fa4800c0c4041c450880c041c8007080910100c0000c00c1d080c1106004040c0500c0900a0b0001000480c950400c03000701104002c010a01e103a00c1d0041f590160903005a006106101d442e58208003018a021100d82c1c0c41004850740c100b903410180c0c1c0c140c000408250 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 587883534 1250 587882284 587882293
    0x303110a080415090f0e0603060106090e041e0b010e0a0c050408030a1812050114060d110402210a090b16020307020415120311010c050403050606060904020415091a0c0606010c05 78
    0x45e8001c103400c2c4007014090021001072546030020a140c40c14038140c1c44030303040084c0382d14100110354001c1c0310683c01c9174000000c591800390310701c1c0b00c1d5004085028001c1c00303c0b600c40c000203201100d03100078500503c01c14000b80840380041108403082c1c0030300e0141d405650401c01c84611028058001070803610101d14802c04030b02c2d501c200c0718514000c22441513851313035100c0e00000f030f4071140c07040865800312040b107225080d0a06a03c1c0c11800c100c0d100c0d919401542c4c000365040940107849030558000c4143d24a00c5690300d0880b00c42e4026052000084510004160104245c42c00c201e04103801c00d4100e038011818200c5a40800015040760800300000440c40000441c098690011203c02d941c06a110b1a003800036a00d400380c00c6500100c00d030f0040100500042c400541c000c078030980c00c4030080302d2090311070040c0800200213108030383c815138405544081d60150642c200302420200c0700c0c880400d186041c200480201588600c651914254000341d000503010741c0951100207015001e50100d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 587884784 1250 587883534 587883539
    0xe0f06030118060f0525030e030c0106060c0b0a02030f420109080d020717030c031c0501060306030c0312030b04290d0b011203050c15010303110a08041509 68
    0x40d140520303200e42501c0c1540c40e041c0084d001c0c1d100707000702d580021080c07518078120441c0c081101103642880b02490101520b400c1e20400b1140c0400c240c0c1c0001d42900f008210a80e568070002c0c1c0b0f411180881200c400b0304050001c2c1107040d40d03200380ea1040845071141c8409a5520502040d003020406040b200e5051f485095503041003d200c106100840f020a00243d020085c8005032030291181c1c091005540300300900c071740e610303408541002160300c01803100280043c00e00c40b09045008441d00c00d10701c5d01c00410708924190f9080c171000242c0300088000c100503601c41c9011000c0c3e910300d00014001009403802000080c04c402900b0004020924001600541c1480003900b682c104000700310005003043c0322911102d0381c1c502d540e0100541140c04000f51328403661842415032051080301c070580c02c42c0f00355809042c0120215883c0509542c2071301d500142c583c100080381d84081c041070300021080703920090708420000fa8114455008141c03241482c0c5030140081071a07a00d02405000c004048a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 587886034 1250 587884784 587884811
    0x20d0c0b0304112d0d020d080c15152b0b0c09040b09040537030503010609090b0d061e050c120c2506091a18070e0f060301 54
    0x1440c0a43c0c810300d0450200070001d000c220f107400107000040e0383d8581d20700e1003400c84010008001101034099544a064800c24000201e50072a0381c1c2015280010000311403101c02c4c0d0201d04a000e6542005041c10a620b031180c0c07407440c01c205125441d4101003180e020f04400203802c0d80110342c0302c0800c0301052002c8150755030000c0c000d20a03122000d80b0301c404900420140380c5030207030a4541409407050229031406444890b41e07240c480d043d402c100c04071000154029a149511021482410000c2910340d207141e260017425079000b449030000080743e003030002c41c100c41c0b00c2c00307190301c02040240100c540d1011034171041c0003002410396008428003400d02c21214032805000b0544520002e40c0b072161240d6071103800c075095004c010710701e8411090030024071180d03004c008141a02280f0003030380814170300e41900c3c00341e0081100003000390201c1d01003443e081c3c081c0c502815035485820100c00340c0c08800c1010541990b61105030041801c03441c4101d00292602040c01840d07544080024008680c00c2c4042a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 587887284 1250 587886034 587886037
    0x1d0a0b0607050d080c0a0c0b0603010905030a08060a0f0b12091015140a0b03070c150f0903020c010f090501050d0219080711061003060e071502030409050c0406020307020d0c0b 77
    0x1040300c858003c3c030024001036800255080d03101c60b01860161506140400040c0f82104100b4000c140208207404140140c40c25480100c1c155844400c4035552020208042c4c40013030704072110340c85421009c2011800c0b80702c0850000c12903019091300381c105941000c01c20030b040c1009002c8034691250024a4403180203601445e01e2900d42e0a4221505c0c07400c028445540e054580d803440d002d81c0f20014200160341c01c250840307521028900d171460342e80846140c402c41c060314484400c00d04034241040350303024101551184007481e103c0d400b200e814a880300015140d4010080d150380100301000410866540514000c004011640b1001454001c10800040504000b1102a0001040401001200354012400241c0e0419980040c1444e1500d8105421040c80c9404001c04c0551070707100c0b001d82507174100440005000d181e10110917940c66207500030740c3c0e86c0281c415031049500f000049501155103004032820341c0e0241c3d010354a40740307068003802a550020501110109000b90700003a03004d2a480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 587888534 1250 587887284 587887297
    0x902121c0e03190308040c0b070605071706030709090212010f0618020f04150c2f04050f040f1a0a090c06020f0c01031109040608010203041b1d0a0b06 66
    0x1002401154a0408010103401c0c2126409002c1e5000c1c0d484003100b28010708480490560528200705035560f6880c2251488549600900c1c1001b00801c1000c2004002e42040d403041a10780d88481c414084160071140301082520016059000b0300c40a00017540b0075044610381a0000d498030081940b98039205084800b100441c91541340d071000240a002d03030701a02c2006140c1448819414000f00608e80701d031a20441c4078480c00c0062104d000307040380f4003d288103006244c0080301d810004001503540280360782602e12800044600354540c403064541849000d001c5c0c1850505e17007109503180c0e540d03144140b00d18801694a80318521042c011740301007c1c0c10902c500d114400109661070280380c00a00600c440d0444010754101d00488481d15000098103c66107809103004a1400c032035040c6002031b0f00c10091070540207420030b9070208000405400450103184035943c07540b28403c0e4800c0071140e80a690090b420700065508040d07c0a100800300a81c0250381500b00040c80301d810000a41103900c0390 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 587889784 1250 587888534 587888563
    0x90304170f01060519180905030a0908060c070f0b071404090b010e0402070b06040b010e040212040212010b09011e091b1706100521010e0a0b03071404090212 69
    0x9160045510741c00b0301070500140f0b4180c07110107282c00d126004071045419400342c446403101160a00c0c1040c040342c2c11100c141d035000020ba0f0b0340c036412440000c1c8084940e00640d22130788661030204401c54124011180c4803900600c19103041d4044e070380c510350003c80107800c031420000c8003175120071a03a80c103c1c000c2c0004c1201010010f19400c6a00000d0308201070758070680d04c5584140000004070f91190202da902c440e04a900084011481c801070b80d0b09042c0554141d0468030100352403800c9000325489502450080b150b08810417400300a45082e41c00c1c02d54800d40003030b0f141c001000484c080c03181d032505e01d49180310208005621101104100c400c5050409d500b0611215620443d0303030400103400003840c02c010241d074a490910045a4200c50609540c0b0407c42c00140302c040f0260345800d40c048409200f51141d0a03965140b00404840c20266800d104261801441404910340091300c14111488080301600040e400002c001c014910400241d070051200e40d031105a1660501c10f80e240c80310384 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 587891034 1250 587889784 587889793
    0x304060f140901051f33020c12010606140f0409140103031803030206010b1c0501082112060d110d05010c0201180215030c0c0d050a0f0e01090504020309030417 70
    0x2c4030b8090a40308058403103d080d10807034080c03161402c1040800415100100c41694111029440c664150340340c59030350070001d141c4a400390781c0e41580415030f410321140440d0b00180c1c5c651081e201038203c48861054030003161010803001c0c08510b51401421060b0540d145403410a90f030781401700c00395841910403e01203502d5000500c1016045004072068855185a40300014210380e00170355100c4040c010500000d4010036444480c0680c406544e604259500080c031a43d41e5030f01c0100e94502c0841e1068016650300c0c0c4a0001d050120b0381901c1d813803072070032040b0100364071a0000e211000300034003810baa0400707400d000004c40e80ca9135100079002500c80c03000002c201050302c070000d0849903d105150103120b1201043c00144c0c0e621441d0186d207080380703a4060344d20b071a4505810454481c0010030301c51406100065648960014050140d40001d525105816007941c441201c003201900318460119500d0700301031140e800c10360302a41c1d0080a0348112881e181c0c441c80d0010703445000ea131110716513502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 587892284 1250 587891034 587891041
    0x40b0a081b04091509050f0a020904020702061603020c01140d090201050918041407050a03080f04230a0605090913020406081603060614030a03080a1803050a030b01020d05040b0304060f14 82
    0x138140410000b8000c1410421450030312030000280894060b00d005807054010404051a50702c5034110b52000d45d00400095652020142180c0c12001240b0140d025010b502ca4545a40d4068020190420790b03804006280031130300041c0710000c010341c0300f0a80c100002070100202644801c40c518496480b0644000460f25103442d000e2002442d204078035120781c000304020000c2e61680104081980d6000c03100c10703120706842d03240350b55a000310b074046103000d404948010900030036104510100101606c1d4204a240c0380c4000b5a680e00c110701e41e15810002217000a20390608160240364201d20040c00464038542e1052158688050b101000704030003520002001001410701c83c140003441e203080c19148100c0c8231000a52123488219015040c003100000040075184103611451400e82d0003250800c4450842c1070003040c0d0382202102c00e0100340f4021003000c4542c0001070200e00300c0825500c8615041c100403a1a240741c202030021038034523031100303c0700314022454003403480d035400e07140485031140c038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 587893534 1250 587892284 587892311
    0x5040e1f08160605071e03170c0405090c070312020307020705031b0303251a04050f0703050c0d031106090a030f03061a03150405040308100506040b0a081b0409 70
    0x4180e00000081d444002581801a88007090404a8001c0d040c85912280141031040c24078490010341c284006c8400041810190003440580c040c500c00041c0e281e056072002c0c2010b5080c131807030103204e612840300000520200d080c540107045181c8240390034141516210390450a0740c00c19180640540c01400085c070441c24200401152200c8004810800e9083c1c0e2011135120711030349140002c11600e002c0b40107910103c14401c064650780c0044220408082442d402d022243d09917012911801002800c00004200081c0441503a40000240c020346225400300103402c00300b038000b103041c0410302401180c118010320004c5d100361000d074003030202c150a51070020b100b2085c11007003400745481d00d01c05129013203074040e40c001d01240c225a0f05c0d69036221098550160300ca83c00c0c00903030040c2071508010405600c000c5e1070380105a825206400151940c04202c0103014900640d4464a014044141c1d0f60303204500254124032250705400c008111010a041a54025044455115182c41181a013031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 587894784 1250 587893534 587893591
    0x1803140c030102030c040b13081005071b020a14190b0307020f03030705030718030206071b12030503040204020a2615040204050d06090222060806011707060f05040e 72
    0xd0404500851551428030b604410ba0f01490203072403216000070540c2d100d00b180c03005058001d48446801c4400011080c107248026040c1100c09000007200d01d4824484958644903007000c455000740140111814180824a0070003044407155200c1c8840c4d080040340010040b200001d8020224050360303d182010029240240d64400c906080d0310030001c001004d5440401c0c0c030b0700405c00d1b2501c41703c04050000076040c0103840d40c002a501601c002442410807170445121450070f550782060510303280c0d4404003148091515030000e00452030410000d401407520342c2c002e00c4882c2890801c4581e90951680481482242103110000d1000107004d01c260700e601e0800c40070076642c086400b0742c43c282c20316020880c1000151002080070340c61f110241e04541e26082c2400882d41d49542e010200c84466082c180582654469288a40130300b50000c68600858230710100800303240f0700140341d8286000c5046507015428034002040180610021496410402e0641c3c054503d02005100464000705005140c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 587896034 1250 587894784 587894803
    0x120c091401050d030804060f1814010204050307031403040b220e06061228020a0306080c0f0d050c0418020108090601060906050c07120b010807120206070b07180314 72
    0x11090400d00400ca140d407024031800c629603240c81d0000c540c3d2668580741001d4400e988a540100781421850a803103503c1e105401e000c54040d5000301c075080c1c0c030345002908034810342c010181c050b00701641c09d2010490709100c101d145c1703a1401c1100e203046e03500c00c0100d0307458110b00281e0605c1c520004195842d004002500e00103007805411000c40c1d800c004001510512a590307007241143e4482c00000c00074844018a50040c545034003210780c020702e4200c1420002c0d8000303040007000c00e14180010402800024800300c040700094001a01400b4580410460106094048880303114a000740041c58a590141c09a6a036040d160704d141d440c2c480c03002404661004040c2c00b115800040100007103680004180200c5085040143e03444290580c0d081c00c12103540c00000c5548070742c2c02c4030010041c95400241c1201c080b60306a80480382c59107d504a180428103020750b0101c0c0503ca0b09000c0380b104c168081e0414298140b40a40d40c4410441c5094501e941e8801e480c0000c0310510200e02c02c0080c0001c070031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 587897284 1250 587896034 587896061
    0xa030c0608090d0509101101060b04051201051605091207060c0c14010c0818030703080a0219120e01030b0d1202010b0301020a09030f0f08070803153304120c09 70
    0x140103c0d0780c0020142d0140c250014800d1710122034600f811401420340e0100312103110002c0c01047c0d02c41010003055407003441524011201440294005401846054000c2941a042d02d03202510050308554070340015046a52102d028101030480c11001c000c0440107100c00e44800395281c501e4142046015116800162069034450140302d00d80c0e0310000050416603c100c0b10f503119201420740d402120701240b00f441d054424101c010043c000798401600c1c82071030650880e070548819a1440b60012128038006001031040c0e03000204850041695008801040c90b00282205091001411188029100381c6001c800841e00f01c4d1003680c213009c5c01031a14415402585005280c180080c0ba59003c0d00c0083c000c81160074082c0108041d00406012207034208546e552510100d0420008550040e00e592141070760704143d00e801d03800c0c00e9079012040c100c03118065884511490074402081501300610310007907010030010542d960414401011140686a44420316042120144c00c1f80d919049001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 587898534 1250 587897284 587897293
    0x111b01061403030306011107091e0b030c150d140c0d05100f0302060313120203030106030e070506220b0f040602011107110d0302160603140601091a0c0a020a030c060809 74
    0x41c1070b03840c0001180d4000d0002e103807a01d109040f00901608180090700140001400c0c01c0501145444d149148402444080c40400401d54220105a940c8186504032038005400510000c0025540009040380f840402c40c040b5140850700360300f0504050880c0d01d80750404010400300012102d80c81032507803100300402c1152069040ca1103503642d4500c5441300030311440340000055035000c80c89010602455000700d03d10101c10940c50042e450750000d00070308001914000f40f581e1101c8000500504807203010b400d041c605a510031113600083d0103101440441c0140d6000003d8050003070000300b080c0c0d03074804034040e19039050000090a451945105c8401c41e503080c8541400f25064984504440c041180c1ca24042d0290745002da080c194885074000311451802d030300088058142c3c1010500100b90040b900155a8480055030f06850501030f0400d105996450354410420103c018401d04070b4401c11110121003942c002200079920b504211440a00600c040042a41102c060f44e00226000e0240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 587899784 1250 587898534 587898569
    0xf151027150f140a090302090117060a02160f06200a0e0306090316030221130801090308071107030b0c0d0605120d180b0d0b0102060a02250303111b0106 67
    0x14860806070001944805002030074441312030242c4140e100655010f00981c11961355480c0c01a529a00c480c0e9003500e90140c500080c02400b52031003190086008200e00d103074640703003076103680d14440c03000382088a0041c0e0340c05103007801c040300700038800d00380a00d511040d03602c000369040202001d50100c5100d012b640a0014481c0741c20000c000d441d505698245004191410f90034104d10f8010b0142c1054131200c81101076400c2100290000c00d403400386540701c0c0b10510f41c0c0d030b201e050880c2c44280d40035001544190119121034480c58240310284000421680f410791640c0b58110f01d884146d540f2240c1282c00507035442205518000c0038020001202c814410107840704002d51100c00401c07040e800c11200c488001d140d046038149407406403110303514507030f1500c900b108408000d03c44140401e0141c132800001401011690088607403a0b205004010702d00c80d500c00c0c3d2010354440c6014201c05054459a001c03569500000182480e001c0d1200703480700d0118110500c508495954200004854000c07507031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 587901034 1250 587899784 587899787
    0xe160f0c02060d0203100e090c0103060f03031706010908010e01151403060a0b03071203021b15090112020d090302070e07021212040f02030709020703080f151027150f 73
    0xe40d001d05900c280f001d0f030707240d903810080e280d130f481c081d00500c1003070f0b00010070b11850441c00076007017040d06000c0c2c0701044820745a2a0f00e01c081146c6110003400901100013288100c11003442e0740c0d40103072040c100300c44d8481c1c8412020707095580803603001c00d580e0764070740700d00c41c00d10102d08110000741403040c40411403c0d10003010036110300008010945464071055068150b44041000784010110703546218070b41019032500a440d180601c80b10410a8448480032600d40340160801071024041000c0c2440c00c1c401c41c1c01500c130454480c04e0b070068581d003440f0844d0105114068410041c4c8294040c214090900748145620b80c000b0700360781d04540c0b01d0240d102c811000f0108071030b2102881d80d07502c0c90a0ba0f540c68440d8204c1a4900002d40600426100107811607054025003010b40c4a901c9851155840b01004000c650085071008a0003034142803101040c00c01540c1c44001c151145001a0142c55481c0c0c1034155070f907025000d08902050340000c0000d403041884002c901401860040c0203038108040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 587902284 1250 587901034 587901037
    0x312031e0e0d0804030228060515031b01050d021210120203030d051f060504081207021e130507080105090604050f010e0c0c1c110604030c030302130e160f0c0206 71
    0xb500a2101070004142458001c1041d1407009040701c142001039603012810700c60b040c4c4001800ca8401c1e0903c00410345d03035000a0341014100c07074050000c0c004006403420701500ca43c410046141400410041b05142c9000c9000601c01c800c510902e48000b030034002c42100e000e600681c46107000c42d10440c1341400581c0d008c81103504500400c1004683da403216101c03c802d8052a071007200d2000c0f013518001540d16001805002100d66000547e148111840c200e0710700b51081800c001e41c40880b410608100403a01150010066000740a500140320081041d104480055075103d0200b00040010481c41c500110745551190081d00c081c815810410f18607540740a040c0241c03c1c070951040300041006c079195040d90f00f4200401d085400c030040108150010003800301100d00001c031918056040c0072400902c41d40610381c07541d2201b41106070303130310110000d41040341c81c0d6880c1510034000140e240010400e90340100d000190801683c07401040c040c01e14080c141d690000e215090801c100540e03035010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 587903534 1250 587902284 587902303
    0x7090b1812030f121b1207030b270a021b0601050301150332072d03030906030e0c0a0e07081005030709050402120d02030a08010803031006030e01060312031e0e 70
    0x90440301291154007041801c08a000602e222425001ca8110090540840b060740a4080798404103c05410a8140510ac5801205032555188402c0b10200000c10070302c85c0703551200b1402c1c401030404112645008000b45514220701c40e5621000040c0407500d02072044c0d0100ca540d212080341c0080c074503a201c1205045110b0030000161465010f90300c0240540d0034078044100361800e460300316031070340c46407a1030143c0c00311462402050102e00f03440e00c0c0391a10303d07441524ac1588800394960f00e440011406040c16004181c1c1900030b44000884031f40320f071070702e50001d07194556522851386080c031700c01480f42d0401820919803100c00c0004010640740441c2c00c4d000e0300c50b46031010496941d0307400442c000d6040c650814440344102c8420301c501c95408405000341003210343d01d0407543d0766511001941c030b020544e65a524442d4107042044010301035032007111440360280000ca501c5949443c6d60074101c602c1e0180c03802013038540c4085144481140c0800340116800e01d0304105101c2c20300c080664038042074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 587904784 1250 587903534 587903557
    0x201110301150f0c3e0a41010e010e091f080607020604150c0906051c050703022d070209061206070e0a080105091507090b1812030f 58
    0xd50f000c41c8980c40350207060b51903504403100310091000744130440c58012400400c2004410340c9203010383c0844c1e00003400768000c9002481d060740ca50800c142d9500c0074000b181d0103000c0804000340100c1c50310319200c03118450304002e11071344007100a00300050900c089900340c0e941080004101400240e8900c07880542000744104d80c503604c0f1180e2258030041590913000840f45104800400c008035a00081207407003180715840e524003114031034280e03e00380d554407509003000c10000c030b9045c00741d00d1190019215904060780312142040307502c0516403c651054800300000381d00007548102d200c80d01140c1070b10b070300301e0710b42108060254582c0c005002d0050381e00091180d22804082155a61b6481310380008040450903074986080001002c0c01030311822040c41d0040044078400509100103101b0030344103000d142d018150344030001e9508056040018101020301c03582d180f0114001c0c80702d40152800c2d034111496400305041e1041004440c44078013030f948596903c20480d150310b40641c40103950410b14030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 587906034 1250 587904784 587904797
    0x31d07031104020c0a0c1401090b0403060b010e2e0f0207051c0219090609020306030312040201051318060b0301050a06030917030a020d14060d0206070c0305030403050d020111030115 80
    0x80400250113446501c044035074a100d910314550078814540302100840d0013120001e1101104000151031203841481982c0030741c9420f20082011034201d070802503141005150036401d180c0d0080c0020450700c1035101c0140a00b000f880c000c0e031201c00c1c40041c9400e0000d28100340c502c504c04148025991010750248602400480048014464044500405c8941c0c002c009402d801e080203801800c41c050340c0728010107641010000101c100ca0b91084902074000500a18900400c10070340e6540c0d40c002810803810400c003002200100d81a42000c080602204840c09110541c04100d901c143c9001c0e801034202c04004000400040d03450302074210403030700903017804180c00405007403960030041111441c250815000003081141d40866005200c1a0142801000701c280f5034407005070400c0c02102c81c00c8d0000f44035402240949031010160031480c1c0301d10303605c40105869951b0700d0300b16080780d8003c0710f00382c1c00800047c658607028061080c20020700c0035a540ae6600d444c2600d1010405402d0388800d1098 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 587907284 1250 587906034 587906063
    0x7030516110a0606031a1b030f040213020a02071701050105100809071d010602011401060e0d140304030f2603060d05100501080f0d0503010b12060a090c05030106031d0703 75
    0x60002c405410b40120f030400089a070303030910401103a0f40d580320410000c0d4a100140b1088004544c2c1522030100c900250309590790032940c8000910094400d82c3c0c02802c603044124076105600040141508940c05025507a00d045144500d401589003802e02c281d0400006015540360103040800f6154540b810503070603202c0c0032030541003000541103030782500441403d1000f40342d000303500b0904072496640200300e081100200c007003c4810078040c9400003115a0030324001c92038039840a028040c0140040c903030440041c540c0c14a598804ea10442e0003022841c500350500407968081120882009005c801d1a122217070340d541c40b44401000b6910540c2d01c60b40440030b100040104030380d130b50a0315030704001550f10b0304003003552946060240c1c03446108594824480d1841001528100c4680132112401c00c0004289018410170007054030340c20615004001400d00fa9500030a860f0909030788405980303505110004041d00e50780d611011085481040c020058400040c114040307940080c0d55100100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 587908534 1250 587907284 587907317
    0x11090f010c0c12150515060c070e10031b031101050f0403020d03020f0616020a02042003071706150304030f0e060417150405100c0909050114030607030516 68
    0x240410090181800b2410106008030003094110340f0f140203140030b01500b100310304200290782e400c94010004a40e000700e000041d08004014051040004060720560758644013110205107040f00e80d05038202c8500700c2001440003610f0a000b403000e40e50300c0d00d0380583c15912411040c000a00020f410480006409010002c80009990285a000707010b03100c04959418020345d9081c0382840200e0a001300c60203c1c2c0790310500704500041c5002c5401401c2e6982d529002c1100802400c0030348001070210b40d12040e02c00c0c1000700203511410341900d841c082c01040c2420240c298000a0102e4040c81c05074110031180707001c210070380368096403525001821800d6180100c0784950488501c0b43c10040c045004038000d01760002c210924080242124611100c02e4400880b80106940c0075029030000000004409919007101450321310a00300702015035514212503044507026072001d5481031f02e006007908140342c01d0040e140c0010312480c00f80603034201030000d9103a00702c91395062030500c00840c070420340d1380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 587909784 1250 587908534 587908547
    0x9140d0206040324090503091801051005030402030f060c0c0c0301050c07080304050a05060a32010b0f040e040303090303050a0c0e130b03060a05040308070f08190b04060305070f0911090f01 83
    0xc480d00138044c0284a510b160540d41ca4100e0340d0041d208001030358101e8a00d900404c425412680014080d20801a10700400d90301030b1f001030010390301802030302a18049207070100421802100d1180440d0781c2c5000b014501d80c00c000d4034001143c030030b90411050103451091001550f44568200c030a4507560784561070308a241c5800410010094020582000100c0007181e201100c2840610740c4810f1a040c6030000361140c08881000b800d40d0307590200103003c070340d07144400360500004480c07070b0307910300340e1659003034544a9800c440440020352070b05491820113505016050300009100003e0003d00480c3c00c0c003034661480e844280b4080d00340c001104013880280d402800800b0b2000e030030f40e070660034100c0c6408054401214203a021403500c0d00402d0040b84035802c0c0307040c0c1c261036a960300e100742c844000c0c07920f030000301b00c40c528441600e1348985c5c8229030f16842800c0096101d54024444c01e8130300700c2240515280ca0b4800e48803070b0715111207100302075400f80c11504a08011601c21201c400c2020040c3e030385 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 587911034 1250 587909784 587909843
    0xb090c03150906220b190e0708071403190b0402040c0810090216060f0608070b040e061c02031f0e0106050315060a030b0f010f12110d0203120a09140d02060403 70
    0x5140d50315090143c200022910440c0301b101802c81030104881441895550b0550ba100d40006903101c100c0811604080c01c0003528100d000805a841c480441e2007820718541d0460400d60701074500d41c05000442c80c0501c07034410450420f050561062030000c000c0f02c4550014819010369580014007501b1581c03d80050034800c6500100c100b20754805681003600400f4103000d80f202d80e00c61182d000c64144140005d45080382c1104103082e5007691500e00380002d01d0000725140307900b500e8142440005a030f0034440003041c1110380c0d0010070310078100800c500942c0c0d031001218000764904442881551800b19000b07a4030900c2c10b8003113500d6115080820514a99540040c20007071056051004d09020724540c24121040c0780d861220560710307080304003900c001100c0300500c541c0c0d005ea032030b1010341058003c000301c5500040517204246c140780d00b94a0642c0c008051240040d4900106103d103010304001d2996000013030f0781ca00c681100c03950204110b0f124500000e030101030001c5124204a140303905203040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 587912284 1250 587911034 587911043
    0x31609140d15020c030306130213030602070203120d0c181d0405100e1c1d040f060e070203120117060106080c040f0e070f031e09020301090b090c0315090622 69
    0x554a00301109a030302d075041074030701c14890210180035010320000c8c0c0c004c1d101e030070381507206101c0240c1c9960369910096006c0081203800d406902c01c200741da03403002405400b24405400d80880d0b00c28501c03400030301c60031a1183c1020030b5614030100340000038044902200c1849404408070450f00e5a0920070300e8000f01c0f200400c6281c0c203000c1c10101e00c544c04540b8080c4650110964007020504143c29681c1c00d08902c2c5152301000d01c191070300002e24041e042885030000c203038030001300e090b29040c000501c02012200040580d00000303520003448118200940104103403410103001c11b1944c00825200c20040c8100310801c0b401c2404500c0707010800d021640100703800030740c0c09045075a440850502c2c10b01100c9a03404240d81c06e4081c0d407014040c2c065850020b8206080840060810380f80c80e006060202e0140d80542d62040c403030323000650003555a4020a005001000400e81c102c0805181119810b12540d0403240701090007105180000c4450b040380d401802c6444000c8903041d105222511741c00040d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 587913534 1250 587912284 587912287
    0x15030605070903141504030c02011101240b1204080a020f060405011a04150e0703021317060106050a020a02010e0d05012a09030305040909020609090c031609140d1502 73
    0xc400d0b0850100b5086922903c40003012000c0800c00300d80754138550351900800703020f820002e40080c1c440c031011000544141844508003902d060301d04c0c210f9900079a01c00129850144041b240b08400c0d0780d19000b8021604043d20b00703407d0790000c41000b88041d10003000c41d0340201d5500700306030090023001d00b41c4510108580c0b585c5814203010303000c1c101044800c41e284402540c64402d604090041035601e00e609000003070010b01d007007034090741d0030b1000300520200740e0f0038020101040707d04039070301d4000e1081031280038518040d00c10306801d088040e841041842020084044a19000b00f02041401d80900f88080728844200c0070941c0c0e9410303294020326a51815043d51260707401d07000e0642840070080100a484245031a040d100b9a903d0700020b0003250060104204d2030342e845c3c0100c00310707070b03c050701c110708005450002c01c00c1c441c07041d0780286107110017108100780401c6a6034010884c5000745404031080d403500b18001c0c030308034000d601180542130708117005060010401030540c04414140086 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 587914784 1250 587913534 587913541
    0x2060d0f0605091e160219060b0a080304080f0606010c0b0402130903020a111203040905130501020f0304051525110f0a03090b0301030308180f0a12080604060806070315030605 77
    0x20048400310350000c1a1090981d00442c050a00c0c083d0f124036243c10701e400602c000c102d8071f250241042540902240d2003603c80740382100c281c8820307600d10f006020310001103460b5030421804a08241c48011408020751000c406c01034540c4e03008071200a07640e00030444840701d45945c00030a44078000310401c1d040300381c2424200010107500042030310400b0f004501c116044c00c4000c0801c202144003001c440c400d6401400140409081c80d4001ea0b04091811003c0c0006100c0d5500c071400d83e004207800c0b03403d2510104c20801070000500480c035a201d1003850394192481c1c094070103981b042d0fa0405101c42d000a04000540c0c990085080e040c04000030811034106410340c1d130103070f43d9407031a0900c00c600207410b0020000f40c903e24001584d060326411348070461030380d40b003da0584074000c85034101d05841c810b0a02d40d0034041024402032400c0d44c000c030110300282c40c032600c0c0508240c4000d000c0030b00032841e003081049049408100c0503005036040c6008142e0040b80c100c024a0900e45410140210b454001031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 587916034 1250 587914784 587914801
    0x50f03070c051206010503061603090f0602070c0b190305090c0d0809010e030115121a0702010b101d040b04020f04080105010e0603031215060c010f052202060d0f060509 74
    0x501c1e00720340044800030101100022020749078203081c0300d229010b51001c0003084804aa4000c5220ba0895900e0000740c07018403a00e50201540307000e01c0a80707106038009a01000c1c0440d04940ba000360910800481c41e00c1d1071103000d11074071540e007003d04041564402c08501216014840c00c0c00c412070041000d0340c5030300141044900ea906c00c40c039050114001c10002910b606060040020700c056a0030300c00702c07651800c0700260400302c2440040b00c00340c081814250520124102d0603002c1e030f000340d000191036200c4e8002c0c0110441000300000c180180902c0c0d0354651001c1e50034040c4984c20540d0b01180c000340503004075000c4e0050f400c640314206400b040110305800c0551040341228015442c81ca09501ca01007416203e1103080c0c215000c5000c5d50001403c90314841100e001046005080706203001d00342c2d1311030350843e818210b8000184e5122010310000c3d03501d1038850624106000c40790308e42001103a001828030b11a400040030029124071a070b4a4500195121600401d009030500c012071902c401c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 587917284 1250 587916034 587916053
    0x30f060c09240306050d030c1203110c0a030807080903190917030309010c0305010b190513080d080108010c0f120213080a0303060815130525030212010b0a12050f0307 73
    0x2d03203500007481d000d40041c0c1440d0032407842c841c00360903440d115010300013070721481900310350783e0b50000516858011039842d2480701c20040c84440500381c003404031200c080c0340040400710060420320400990805010540c44088125074860700d04805003074504070034500a4810305171990000e1740300b40f030482040300b0303803240800118070540b001030003000390307814034401502240c00178010340c1c61450040c000d289241306c00c8260a4000c00482c01d003a401c0071822101201c07400c015030400d6099030482c01d01459441e410800460142904100902601d000c10070020210100d80120b502000810142545101c4003a03044442ca0300a001601d02a651210f01d07003a0f8a0844090490000b4a40200010b8140011842c45250219800854015200c0c000070792141d00040e1402d44041c05002c00c504605a16107108c01c0c00c05a02c13624240c0c1913072850040110080d10121485140e90411026242540d150b4a405066641c0191000d480d0013f13802d00601c0d04501d01c1c015507243c40001000d0062084402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 587918534 1250 587917284 587917349
    0x11409010e0c0d030e01140409020d1b08070203090d230f24190e011a03100612080a050f04080106050f04230a020f0f091207030f060c09 60
    0x210360241d002d45052054410340707400060006150108201a0703980714013107901d20480d0500e2100d00b45600c50402c4030803603101c00c0f000c2c0303581541d87d41c40f0f090741511f00120b43e0790b184583c20400040c0c5801c02029440f42300792500d01d442a141c4070748410800a090b0008400501282c41603010072031a0100984d461742a04c070544072a204803a0f0030704140c02940c040700712843e180450240350b9210b550b0b1081411012101500025440d4840030402c8102440b03003051000060030304040d00383c0b03190141410400031603880c031803c9050800070b00828442c90032404140303512028080c2c2e170700c408540403110f500a1444030410420700280014140d441504000e09545048a028201e522007104003c00c40e8000042ea8036102c62152025119201799204298800b20950002d4600550003040d81c1040d44402988040c10700d000c071307420b940c1f800c08130b100d55514140c400c010245107086444501c9001c444600050500d6180c01180c00c086200302c0310304c1c004100b509600450109803c0414640c030150a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 587919784 1250 587918534 587918561
    0x2a05031c05090f100515030331030f0f02180a0605030610060e1e130203100506070f080c0a020d0b1b090d03030b0f09040c0305010b0618060c01140901 66
    0x44082080d540001c5045485880034500501c524113a0400d100003408008000180300c1a2196070b28019480500050207951050120220403190b081c2c240c160b4044142413031815050110700500c000707801001c110340300a40180c402d8140d954548001000c1c01e100b429100c1c10002400c052041c400600e4003d9016a00e0403420b803001641c4a2040076003609031b61044000243c1c54890381c640500305003410040c0c40c2c0c0101e90980040f40c0d050301017003210980105804801d640002000308000d01c0150b200081c0c00201c8070207141203075a07114207035000c0c1e0a100180985c080050440c07020a010031444550030390150440c4804c0d46603040c0344140c5903044030000c001801c805c49400903a4070f0241128984034000340541203100c8a920220000c10704056400d40016036403a40c440c0c140d640ca26128411480b80ba008204a825450131609507000c00b1803260141748280001c00e990712000811201d00081650026158213242e104036001d000e2100b4070034020007c080034020b9052041d001410080c000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 587921034 1250 587919784 587919791
    0x513061a0c061e060d02191401082a0d0605180108061302010f0e010507061107020307060512013318080606100809030f03240405072a05031c 62
    0x10710700503401114007111669001681d0000241306450081402580240090101c0190004a0881c42400d99080e000344d921000c0c40e40a40d03540c3d6034066030703056003d001e004980f000c010300d201118418040c00d0101516810700800d00c40c08187d030361342c000401020010042c40400e14101e1454402540a0050419070b0180200040b01c00b035001864003681030b81a5205083d800d04030070100c503070f0009042203904101081042801040340e601800b500c9480040c0c0450350741d8030b03030320401d40b81040585c8140c05102040c41510038001140d0300b4541140d40c007800d104603840400318000c07140321401540052680c42c1185a0300240d1b8400d02403020039015884000c0748984504000d40e64840440d8410b40c0305d132024916118180c403034191190450a90301c02c82c3c4c10400d034004d5103500d42d003044602c060300348d61045074100781ca01c1003100c0410a040a0318100300c0d074100500d00920710f60001c4610b0265032402655540050145820440c5142d00201a240c0ba590030b0111170680e09810000990420f04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 587922284 1250 587921034 587921041
    0x316081804140103060b22050f070815060a030e06130204050c0903060a020a02071212020d050a1b02030c030706170109060513090f0c0e1017070513061a0c06 69
    0x40521400c03641842c002c1c00120241c0c40c540d42d2030b0240940000b680d0b04a40120304003480d01007004070350f07811403868520200f0507240c100883d0f006000001c0403030301000050b209110404d84c5124048078131040640d410ba0340e0300c52841082e4060031105d010030b070085c4202c4080042e040004010400841e208a406012a4892030305070211402000c1c0881c0d807540064003c030300c071101e05500070319200c0d0b45030042d1401140e5071000803003074900d450b00c1074920740105007911100c0780e03041c4150050901c8500300142004e42c04400280725444041a4622000c0322413609415940e0420a042e2030000c02812694000d0b1261002803d00c6d01c10b658400154008200105000070140640016030300081c1c00c1034200d0510803450005000220350035521815428804c0c400324130540b480c00054400b0380b1500f02d00d41441d41e000381d07079014240d018002c0c48880c0001c40c262000c0106044040b2441112070050028526840d00000c0055621400e05118081c01c041a8044103001810504000909964903681c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 587923534 1250 587922284 587922289
    0x15020d020318041503062d0513080a02010f0204080c0a050a1d041e140f16090c02031303050706120603080405090c09151e161403160818 60
    0x40460721150411940c2d0211403e05240d800300f00c611314102e40d8881c081d562903c03101c040700e665030159824815010128045025007403290303a071100e02c20030100300d540340142c0011130100484038000e1000c900041e080340802d00c02d40048480e041424000c564650b44d030b403000d40c0e490481c420030500803100c5c184001154a00310610701c040701d00600e03151086515a0403031f000e400030004e100700d030044007802658160701808000441039500c100304076010110a054101c0c0342804400c2405042c0c1d0183c00c8800c038031040031080d1010c85420450100d00c900305e10314160700b540110b0035045080d8400900000620030006404c2c8201c952640b100d10304a07100c0078509007501c00b1400090f00560082104000500f0510ac0045d0710001e0f010105081070420070004419800c00b0110b0818611b0110310160000c4048080718070011980c0e41d0a458019940700e011081000e6160190140f4001c500c2101803d07828001c4030303990700f01000078200310341c803900e000314490b00045410f400c190455402e642860 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 587924784 1250 587923534 587923537
    0xf0b01141306030504050a0b0907090501050301020c0c090c070212060f090d05160807080a03090c050a060c0209060a0302030a080a12020325120614090a0b0d1e080415020d0203 77
    0x30454469112001800c1c02e00590140a018008503a40c0c40f0700003040b00480c0780010340d1b5000d801044041c0c03440c02e2400c40101d09844041c0c01880c4a64410841100d50200029005200e0f40056882400c580d036204a0003200b8010604065008190201c10080c40350300440d031240708040403030188000c5c0e228804190b42c0d6060300c81100010420400010248400914040350203034032410350145032000130368400045d0382068541d50702182d103a944031010048a5a40a8060482074400c41a03140c07801a0051004c0004400a4003401100e004100141c48001c4007001864000c0d086030f200b85414034004120350321031071855000444480b5070014200c07032030003168003500c801020350540841c5032100f240c0b82c2000311413480a02100302c10203400303510f90f401014014a1a104020441d018104c1404842080140048209454400c0050540c3d56550b039a49441d40c100586041e0212038449014601e9446000a08024800725000880c021010900d0034084030603030175100184c006040a036a01e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 587926034 1250 587924784 587924797
    0x60a05061c0c0906080d020d02010e0304090f1b02030a020d0206040b07050d200c010f0b09010e19020f0c011d030a051317060615090f090a0f0f0b0114 66
    0x409031011510300c50300c15012000a00600035034041c02c050b5a224156400c41e0201c0e0b10080454001c89014013480e5010710074090061403a00083c002070742c050b00c082c3e031607108500547c410070390349000c00c0b041207803250f00c80388a4404062000a840705032030400f81d5a5001101c0403001480b50b204215649072002c6481401039511900c01e19054558070000c0c0d49603084450b044407881c0c3e5034000501105000f400c0003c6501c86000c502d641c1e0809181c59900b52018a1900400b40c1d080c41c1ea042940d40350300c4042c5044444101e00030106843c0c050340d0500c90388035074090708003490000c110405a51584801045600e0900000f00280d045403203c589415600043c4039400360014441c2d400711a001c1d030b004010401211a000c1441c54492050030403900d144902c5204503400303c0c0400109040c81146000c0307860381400994240801c0300001520002003c022034080c412440c0030507440741c041d03041100f118040f0078042c00360780071500c803000080a4004050780040d102c0c1d8000321102c1c4204045951 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 587927284 1250 587926034 587926039
    0x130e06041104090b0709090c170c07020a0e010e061008070f0f2105010e060109080c0609010e0418050712150c021608010e0705011d010f1b05030408060a0506 69
    0x19a1961600070307507400540e07a01a082900c1d03581c940005001c0000741c600c0340510703868034401d9908000e0316408540500d01c5500c140a50312050320750820302c03584035550040d28000f00035a51134180c80841c0d0550001d80c02080310100705400884c090a01c1c1c01c400e807060200382d9840c94804000b0b07004465004003a501c08000c1144225a00c88661240002c1020400305080010400b8a044284601040d210041142c0f40d5502d80040c440f426214030001d402003c2480c14010305030420800c00d0b01d903506914400e10929000580711480e9005840f013681f0300d14020401c00c0032011030301c682c41d060213034110700b01c60340d014031304000c5460582508100560754128200802c040390800c02c01005040c00820f100544c070504511101c08510420410080d1a40f0070000c10384042004c403151074480a5003109040c041c0710440160050710341050380c19480c0003480d1a1040b1843c00600f80c03515082c203108244000c100c5040d100a01c00c000000348221000c00044071900c1d5131740d1380280c00720ba03026501682d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 587928534 1250 587927284 587927293
    0x90708060114031002090f1509030a080705070603090c0b1c1d0f030a0e0904050708010908120f01050607121e23030c16060e0a20030a080319020720130e 67
    0x11245d050401c0c01e1642c2819600780d071881d06c0d050f00002b0345802c6031800100c91580000a0700d02c03c001080c01038200520300c0742402d0008180703d5a43c03c090030064010000399000c0411000301c00c0308509007400c41c0c0d1000c5c641c00c22010b000002c1c069403000c0c1d404074050b600e2090543d50700450400000b2945041510f43d13929500000200800011040c041d2080d03c4500ca1050b005c11400c000f803007902c4c8094410400580e4945410b030890742500002032491708410416001003201d51a440c3c1180d0705140e0051030020003107103500c01612000841d45007104009115210f9004880d00a1003003c1e10849591087c801d110074403c030ba0300284403c9132001c89030382e002e02445080c584080d1310f0180c818812040483c605a20540b100d1528100000079164018052241501403074140000d010212098000d0441c0880c5500c1e460042d1202401c904c100c44402682c00c43c40d82e01a0b0705844c0d03801e6005005540213a81410550007403a600200c492141d00a140c1100050465110b21280740441c0320180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 587929784 1250 587928534 587928559
    0x60307030f1a0111060f0a11071a1611060f041a0a0c0e06070c0b090607150507120903082809080306040b01050c06060616051617010b030a020909070806011403100209 73
    0x1d002c0c1c2200300d81d004d402413050000309e001030001c200e04641103030118502c00091820905480c071107011416008240081410690708003a40450f1080d8000f0303a5a1401c580c540300c4d803414141d83c440c0c0060b40031440880500b481082c1c0d100303800c04180c80f1019a24074600c0c440344020410b092040c068014021003104104000b40b0391002c010300000a00200307400d003414030944854035503407081c1c002e900d0001d69a03001c010906800024000c0d41e40710b8010200000c01150b0f5024040a6000c0d0040c0c00307581100700c4281e884404034100e10a2206481014041c07400c0d14540031110f41c0060f54120702c55428084121015441003017500c0240035468002c4c01b66443c0d0a0a0025070b50040f201400c281c0c2040820364040f5204001c0c0b0f400c602d445032004100d1502d05040c1400d8800010904491641081e1034524142d130f0008a1300130850301142d00c1205511038101c01071030440d056101d8410390042d9400050581c0c03507004041c0d400001901900c2c001c00014070110b08038401d24025551008a10f40603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 587931034 1250 587929784 587929801
    0x61801030f03030b030609030c01050f1e060a0816080d020d050304060b010504030206040b0307020c090105130b040b0306070f1e0f1b05011811040204030c05060307030f1a0111060f 79
    0x8020707850090800042400840011904000e4200e40383c03007159000246a00f40d0410034800e0b507a11460800c5014114100f1441d6100000401101291052200d801003003036995100007800092802d5401c0b9184210f01440c0d030201c0e02e059200b000c405010b0508040308003400030a40c400400f0559940b039145540d290360301c100038103003c0e40660400500340000f100588810000b000908105400c1e16124508404000d00e0a400c6a407464003031004840100315a46408017042d4103150581c40200d0014a0070010500510920341c041d54144502000e0040341504503a038003600840c60f0f80c3d116000d403411086072000c1000c0041c080b001600b547d04850071a0f124007840d0003215480342c0d580440c03110717589803142074650107241c0402c5864842d1103001080041c03001c0c901052010f81c2d06504051440e1603040c1d42e840284290340c0146d07000000112098807990040c04180543c140800500090310b49000c44a02d4042e00744d400b15000b003040c20301c101d000040341845079540b0a03400032580c0d5000507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 587932284 1250 587931034 587931053
    0x31005180f15041e08030c180a030816110607110a0602010b0102370b1f03080306040504140709092d1415090a0302150103030c030309170d1406180103 66
    0x158000070b003130829118000075045500460155561101d42625900c982c046846910004031020384181200541000000d10080c143c9224480b043c14800380701203542089503040015442c40c80e031044000038a01c0c1040345040c0d9a01e26440d0a444410b000c4d51904000d9003222001a4054050303408050102460118400d402420702444c607903a64010304207695014400003414011281084003030108034a41c0314001c2092000c913154200d414050380340d51912085031001500c0c41d8062a11600000c05000312496260041c0a0761021107400c0c076951002900185410304040310350a0013890030520b110a145240340f0110480c40310951a4046603884269501ca580c0144c001802024035484080b60a00032840c810300b03014028203010320852030001e090408100d04d020840c0c00d1100140080380e886030348e0380e4140da814100001e14030006c0c280141d16a0340058012990f00340041c000340f000a494118034245407500c00c81c0346042d29200100070720030440c0c0e49038540c0903000d6001040495445c3d01c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 587933534 1250 587932284 587932313
    0x1e062a0d0204032111190803060307030f050102030a1409100b150703031d21160804031a010f05010c0305030a15031b0b0f030106030b031005180f1504 66
    0x10018949682c03030384d0b003900a01c5541451a0003440c0c1401184000da003201030b001150340d41c8000b40074046000c14201c5071034500000b020b030450701c011000400c991810000c503406180c01100d00c400401d807926045010b0746c0211091a201418029225a0074112240707442c02044a50040d10701c865104c1501d500510b07001c410140c3c060605844440d04101c80780050400c54000d0b90302044102c1c07401c900c0e2082c4100ea102440240d40040040ca10000c19824280b4030301e00e17869807a60f56042115414514903085090280c0a50b1001a001003007100c4028060800b8009408007445aa0f07141e4280d00040083d10402c0d0201e0024001180000d229130000c1d640306002c0071001a131301c038440811014450541c2c0080f01c140030442c91000c055a503258680004000c0801e10794607100c103103c0c400000340418821101819103450440069a506010b01400c802c1c46c00d4007040549801400511a1581c82000c003d217030260100c03900040e100031600d4060340e61a2050306641d0f48a80ea00c00c0034222013030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 587934784 1250 587933534 587933557
    0xc031609051806220b090c2a0703020a061e09150e01110a0c0302031e0a02060a0c060f0203100501030b06160c08070806040210020a03020705130e1e062a 67
    0x21900b481040f80c160f04c00c005503088110009100c5010820f1100012014010003601c9078140240600c02c1203440141203045030b00d045602034105003494151a013115504000e600055160b00442d80e140d003c0c8a0003a082e80a03980c14000608030802519001280c1c050310900c07881e0070300200000e50040840104180041c906000c3c00907002411038208a00c0d003000302c4004583c1d082c100294907042000840c003000c003540044103240c40c4080c0c940d56000d600c60007400740382c021640c000c0d100d0044e0a400e51a0f0342144003448100c2c82c1120800007544101e401c1031401a403658013123515442803040030390548028252500e440d915134225601c0180c112400c40c0d007032801090101d4a190140f144000400500d0010207903400e003031042090411703401305004210750082d82c241e0042a0300041c131038200c8206440c40e010300820104000c01070105c0030004445480b45418000d9140c126444e0041d130322250380161a4580c075001129a104d44207040c0100d040c52196000d0750162510310000d00c40700303a45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 587936034 1250 587934784 587934799
    0x10b0a4103102319050301110c190204090609051c0f02151b07060203190504081219061202040e1c14090a0321021c110f060c031609051806 61
    0x2280010b5001c00005608a8104d1201c000c10042400c0074024400c1051100000a0610149481840c0d030740b280d50303d05604291034000784c1001d5441341c0e4000d94500340c00074010f20070700c82c090070710031b58504021182000110f104d8aa05c07042503c41d18400c6043c14895001d4001c3c3c541e19040074110b148050445095180a481d612800c1c0c400b8200038001c503482043d000d40c80b80341c45841c10304c1580711100070184450400b002c00c00011400400c807810f4040c241e8100c0361a84400301102d0a042000140303e10503454554042803080f5404024081d081c422101030254190030782d003007500c1c0c0b42d6880181282a200b868500b04140c001c4082d6100c4ca00000f0301541071201640018103903000300e500c251a80c200340c0c054a1002441c00721950000103003400103140c0001ca06081c1c1c02d180281044d10710412003032403042e0309052000c2c48155441e104001c112047d6040420034045258000c1d280206000c2a0816244559024010341c10803194020580e4400100c1c2200b5140c0b0030780d0092025500001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 587937284 1250 587936034 587936099
    0x6060c0a031d0301020703050910122306100f2d0503091e030f0d0f111b010e0c09070318030e011b020603010b0a410310 53
    0x2003001400c052500076036960b072000100c02c1e0501400303101d90100038040c0e40100808008660004100ca94240058508030311181c0c0d404800c856140103020100240c6060020343c4a40c0001c0040e1414980c01040d440d01260721440100954003400c20440e101207811152440700365400307980c00c2d400502201d600052005440000300341c03101001c01c0c503070380454804400c0c4041c0500820090300303181c0300803030850072964843c80c0032596400750008482000c3d500040d07d018602c1140c122040304002054184840f460024107801c4d1908441410403d50403800142c1c032000b2014060010740f481c010307002d00074071800541401a0880020040000c2c140c4070ba88101c1007003545190910428000c6c0d5a2140c2814441c0006000041c040804e04d280361201740380f000540d0301d0400b01d0341142d0480c2d02c030550703840d03055505035048945c81041e80c032600c1d41d100707840280e40c04119150144006529030030445400807031800391240015113800418490247c8c041c080500785209030711062000c00124001c011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 587938534 1250 587937284 587937307
    0x4080c010e030a06020a0305100510120c0e0411042c0f0a061707090f0e030412050f060f09060a11030613060b0714010612050d14040b070807050607260606 68
    0x1c0c00350611b800040c0d81c0d6030411501c0c40c54140c1100180000719542040107441400082401c107001103000e8040340d440190301d2792940102d040558044014009202e040d0003400240e029401c035100f805c484ea407680d181c003c0c0604c1c2d581c05070010503c1403100203c1a07292002042071303030240100003906c01c55540c000491200c18000940070385030315040042018506001c5c4001c141c0c2c1d94294510300c0310342042000e80800402006a4065a580d40c0600e4401503050800030b24140c40851421030074003030041402480c00300480800d101d03c5086084075084c0c1c5500429200b201c42940718030100a0741880071a00c117107000c0319406506100d01c0404104981c40b06005c0c0415440503404440c803041e04111701c0b00c4118207004130002041c2c80011114090702c652960764a03280740341d26500c1004205203070342940c83c0b581d0307040d1409003c1148401e43c0711419031501115a902114003a2201c0c8212000030350114402c40418019003506060081001080c0359004c00603e805410158000c00c207119407218070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 587939784 1250 587938534 587938537
    0x210206070c090902100806010c080d02040b040b0a170f040803060f1e01120b0303091513060e01030b0d081902030d0c0512151f0c0606030b0a1104080c010e030a0602 72
    0x501d202d003000103004011348104024034542988402c103100002e0704000e056a00001d003c40c8140e0022861941d40c4e1481030944001c1c41a604032180303001010802141e40015000504483d4203991103403410175139808641c24403020111045c00d26561b01500080000b0358040145030003003c0a005074a540100350b0010b041c0903178010780d507480c44070784480190407580c1c015900d0a0101044504000380c81c82140403a85034400d043d8030f03c0c062000c542d100325088094000700d40c000c3c1da01041001c002900d80c24000d18810003810542e0001e81040c8111440d4644940c403160f489512500f818502081c5071501c0d06608404842c000645c041840751340c3d021801401201c5000e07000303641d03482d61121008441070721440d0203804814101c1c04122141c9240d00d420320904e106503400c5403c80c290300150a0101c41c030035600303403005040d107040c8940002000b9004480501500316403006002d9581441d50311281c03405540701e400c8040c2d00c5801e14034465400344c419400140406002d80b00d11403140c2d12002d003607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 587941034 1250 587939784 587939789
    0xc0519080a1b0b07030b010c0c060c0303051608150d06060311040c050a0512101809060b01140d0e210403050615010c060b03100905031909210206070c 66
    0x45020008541101c15030007641ca00100c075000030702c180e182c405500c0f090b1002034010b103000c05150742e6041944150703004012141c0d42c1e0380d200c025003000c15140d0340020f1100300c1080c2c04401090400001c14100820070501c1c030394003010307650744e61070f9035868027070300180d81030302c50103240d08100f492000703c0c08502580248400703580600d03105004020480140000c42c0c0144209104000c810b2044480c200d5202c000c0b80c00109101c403c08220f5152061602c0041d00d083c4d01c08284107012000b5a0a410299000030140c01e01551042090180d80001520b02040c0b180f50941281000c001b004094009603100d454103c008000711b940160a52441200c3c400c4075039401c2d914030351301290400c1044410026940d1100071460f181100d204044000703013015030450380c018045a2a0001000030b910100920901d1740340c406014020550030741002038490b8059031070402025212440b0100280c041c2c1d803050100c91385000f00e200407060002001085101d0018103d0b03200c14100b0003007000c07034100c4005801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 587942284 1250 587941034 587941043
    0x3021c020711010215040602071703070201050f0f19090c090203180609010908030c0c011e020406030614031e010e1b0306071e0f0212040f061418010c0519 68
    0xd0707940d003904110082c0000064010b0440d403008141d1399540c070250307444c0d5030440e9100c100583c6603500b0f403404070000f103010090790300d00f8100807041240c82076054011034000d15828004d080e8985950340c0c00403000303038115204400383c810140b818880403619880352184600501031300070b1082d100c0442d4070599009560315606003400c585880e15044040c0b0030243c00081c6400200024681c0740c0e5511214000200305400c8a0b1021500c0c0038442d40a40160081020f545466840e00341100203220003508903001e06400685003400129846a040c0c01022503840e000f0020048007101c0700c0c04c601d520f480040f1100d4a03540b11400c603607002400b04504c81481107800190f03180481c0107414545800c1008103200204000c0710003014a142001e20220410304540c540310000700c0322082c00368500a20409200c0485034000350014400303100034900c1d010746c0c085036640b8810300580c43ca601c0d020301030350003201c03049903218a81d0309203580900e1072100c0c0b1b03620403402d81f450b080c0d00c0d8040c000240c144610503030b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 587943534 1250 587942284 587942287
    0xe0702060708100807180207150203010f050d0206070803041b080102031618061107030206030406090501061e09050709080303090c010e0a0807180e0610060e0108010e070f03021c02 79
    0xa041a00040032942c0710004a43c410340451030012215915626071056414440d84c203040542e560702c1c1c07034044600c0d103034115000d410700b030310021245c0c00294024803c0040b0044146070200c0c4c1403a02c030030a480c4c569001011681080c4a5442d641d0240e0b1010304220b400f403401120400130008182c4070f42d40180444000141c6a04c0c0038200c040890b0904080c3c407040040700482440744400030380ca00e60a171703040303490820320400b4501c0b01c2c180380202c5500082e50190010042004000482d0072840c602c0b48190b000340041d43d031310081c00c802e03807840c00b1030500304030b039103540600c10545641e000c144d001a0b0361928900883c0e99000650565105072064080fa4210107000642560020100d401c03d56064808122341c40c9008001621030420740600615400303219a60350030100c0c9504004080345c00601610030300c0c00e12040903003001600c0c0c82808080340840e00300050660050720a14101e80702920100e10643d5a00000c07201240b00e00010f0042c55800d000c542c80e80c0080030850380c081d030f01400006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 587944784 1250 587943534 587943541
    0x21e0703021e1e01060506040b2701080f070e04090614060f0d03030b030c0303160c1d01050904020d140a05060604020327032104210503011a040e070206 67
    0x3801c218080c909001106a462030104110782c00203251901c42a480d1980c18074035501e04031050141560341e10555000b0382c042404503a400311140180400180c420f18805825040300c860301e81d076015070074541d0101319980000b0f401d06101c200055801030172403801d81c44c0b064205000a0032265a0300055401c9603840800500d4044503d91141d00b00000f1202c00500d0203110000540e080c035010f0f0000e040549407000f008080e00c040100e000c808a009050b603860f140500b114400a0010720415116070940440000b01075420b0080d40700000741012002000e41e0070700e800d00039000340181c4104d03048414001004042580100355003240c201a80180c01c426200c5d040040c8ac000c0081c02c15071081d44108140035070280f5150b00b24298403444000202c180c0b01020315141140188540c2c0c0d461440240303800c1e0004194034402d2441a44614600500304038800054040004241e0414000c00e60400c010b02090681504a11f1140d01d087c100038600780e140d412002e4103280079225540035a01c0038090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 587946034 1250 587944784 587944787
    0xa062604080409142206091e0c0e010501050702040209010c1b060306091b030b130c050a090816060503060a0306020c0a140f0a030c06020c031303020a050303070b010b0d021e0703 78
    0x140790544030858142e1100b828601408400c0e01116950300c40a111000c0d05881049400e07041403082d5074000710300e01c074642042364580c0222080b4170301c03ca4041042040c040768800302c00310014140c03001a0740b420b086c50340c0d0b5400d2100030743c0403142180c14090012482000030744502d0000030b440e50305000c0081160315100000e410b40d001a000841c0160506d10020a507406016440c0c034046410300e004601c200f64900464501d011550144010a0514030b00c1c05d44250410006c01703030b41e079035542e80c090b0b440d0351020803136243c0c2c403803442441c103110442d4000c04c1400e1140000e1074016a0003003444034610340d60b036140d4080343d0003400400c0d4140c2054451105126590045624041816020b89142111580e81c5038542d0b0340b102c1d00409201c130456904081c8081035042e12207045684003120b0f5101388000a1464884803848100c4c4140c02d81700000c500350401009a07450503a10100c0c10000764280040c11440e50041200000078a03400d11050380d000100d0721003500c0f40da8604408035611480d5040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 587947284 1250 587946034 587946041
    0x19030606080a0f0602160b04050102040e07090806040b060a0512010b1009080304230a0603050f090706050a05090f030102030f040303140106051812010e0c031b0a062604080409 77
    0x300740690040c0c010070703011491801e2a00310440d480400143e80d15082c011b00141d000110b10040d010628a10801081100c154010800c0d1490105005010b07a105501105d8000040c064158107810440100700019001400c498111700010282c410594a40c000303c1e44e040c05143c0c0d202d81c1e50391503404604413810701c40707401a44694546440103540e030030b141109541c0d1140d441741d05030890381180780c08108401003034040401900140401242030355070400130090203050b290540943e01c1e8002040702e01c0c1001a00c0400c4514644480382031915103001607030303260000604613410601c6800716465075038013880290f200d403510441992007418036090081c21994a182c1d20499040780000611034140c018042c0c1c1d0705952149621141034801c0e40204110341c8120745508511b43c00c0c0121146c501a0104000d60b180d5800c0e000c4640c030168041038040801c603c6054070360002400001440b54500c0ba00c8040000440360a04c4101000e0340641550034000844003582d503620040380500c030f548810300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 587948534 1250 587947284 587947289
    0x204151b141b0607020f060a0c021302070b0f04031209080903060f07080903160f06020c010e10150e1503030f0a020d030f1a010315170604060b030f03091e19030606 72
    0xfa074490030204250301065a0000744440c1500c120804184480c1075445000455110f83d07001e01300e220014030751100314000e500103910481318038002c180000d28100e040c82d01c040c4207e41640d110124403100c1051000203000004042e07a000200300280d001e1900e08100700303801052800d0b288a09480c00310001400030001412010854004022803101c03c1c004203c10310103180c000501800d490303400c5c41c01d40003e00c106201107080754201510110350341004510050b00c01d07d01082806202c1c01055041220f41e41802003100002c240400f043ca4000106003103a141280034088078a0003d82c900d0101046c0c1200c043d440040c1e00c12921200c074641c0c5401140700c140b50a1000380215003902899a048250b1100243c0c1016038a5202043c5c220344018984020601300c0c2e00074040c139400603211038a13400c0466090781d4060420103d0140c50034000350411640b02050003031410309510108000c01034440c0d001907200c102003104503205a80d186400410307400400521048010b2451030400c090b503600741d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 587949640 1106 587948534 587948539
    0x211805060105031204030b16020109020d06091211060a0c0e040213140306090604110301061502060f0108280206040b1b100204151b141b 60
    0x400e0041c1681c5064080e160880f00b00f0a848005210b1444000c020b00c901400080c009413920004400302e002c00e1001043e48811600002c0d01007a102d013041c0d8060b55503038103000030001c2c8140c140801d180c076420720384a1030400c007051640b980402407500440503100c040c4902e84900c15140c0d02030300c1d100203008540b200da451804041d0b01840303011b000319582d0764043c24111864001840e40c41820250018040342d0b4890b9a00003141d03480c00e035525015902c83c030001c5090740340c01507402400b0701141e005004601d0b0000f40000d00000c1039010001d00d070000c4000e00802100c40c0b050b030443c4098020086007155961000c40e64507c46c03076204100749078000c00c11b11180c1b2110238401001c2a9604116600c580222111004034810f61144001c0034080f0000714120501540680d81140c1c1c3c0c04e01f18a8a042050300c2c2c0e1704070103041742072009454000d540f030300b0031036049202c5000b100c3c00d09 = true := by decide +kernel

theorem cover : BRFrame.Cov 587769784 587949640 := by
  have h0 := BRFrame.cov_init 587769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 587769784 ≤ n) (h2 : n < 587949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
