-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0203
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:25:32.961737+00:00
-- url     : https://prove2.me/submissions/08fa78c3-1867-4e4a-999e-305e8199b82c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 36330940 ≤ n < 36510796 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 36332190 1250 36330940 36330947
    0xe011704020f041b0203210105031905010e010504060906150302060f07080408030301060207240c0f02040f0504060506030c24090607080a0206061c11040e0a0b010e071103041410 78
    0x48800254900a0ba0005910030081d65a500142121420841400051106c034401c80100c034103036032014000d8002e110881cbc4500d04283c500c0d007022601e9540b80d001c40d1035600780900c12148100e009040101d4180424100307401107030b00006803201c00c024540380034009600d907030044070904c3c448800950703581c50182c00c0025290285400030a01e40c003000000113513940d800510001030f201d600325920400e0750300501004144080c00e241c80d010a100c2d0f0344103000309000c010362030070b0140080d20100348852000c00d0b20317044890440f41140c40c1c50740c0701c0c14024241000c101c00f4204100a4680d00e018100707110030307c94600c2c6102044440d1100010f11080107481384400e550b01198800c43c0d040c0c582225400203500c0700c20886d0341e64011441300b5a002042c900c9580e211046035006801c0344d220038400000d00015185801600c0198810312110400042007100054020300e02c202d0034070311604003010010404050215500c0203944184410b0002c072000c850000c41c0d0a01c120307520400c500404400b135 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 36333440 1250 36332190 36332201
    0x6070206161215030b0f1009150b030a050103060c020705030a0b0403030e0a03020604051204060507030c0c0b0c0105040203010f02030c03070f0207030b07030b040b0604060504050405100e01150e011704020f04 91
    0xd540070f05001103640a030300c4030441d040560780303e10120b200715510a00700f1541d44070201c0381c2030031000d10300300c0070002640c0aa20440d03911001d90038024100c0d03110000d2500d00d03803080d80d40d600010b5540c001003003480090300c9211148003152000d0a066841d042c0025900c8001c1d00c0090910810700000c10205802503011100c2c1045550960f84240700505002c2d40300c980454080d505409288241c0c2000c1d2182e10498045c0c1d1740b01d4071554140801a182114200f044034400c469207a4050303c0810b13102003441c050510400c1c0000007007018a401d1040c0350075148600d1420b40391a0043c0107011b190011502900c1d0f0003111850101000703501440207d103000074950014007404100428003503441d501d0f40141035241c4040d00c1c103200383c90218003403002a104502c585070000d04180310500c000d1400c3d8224a0300481110440301d1400e0700c40c403514040725020307888600100b01c6502c18091281d0000c203000c051003801d09204000301c110503080d1071024030041c4028400c000d0712035403002684e96076111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 36334690 1250 36333440 36333467
    0x60906030e0115081506030c010807030203100e0109060504060806130f03050702040c0518090702062403030f0309120405030601050907030207060e0106061101050c0a05030403090b071a090607020616 87
    0x803c43ca40d562160b01035110b404180074808219201d070b0005e031440c200010809507041d010303521035409617249001100250805040004d40680440300040c084040e4030006010300704141c80092f815203030004000c2211050f902940d02d90300072508110700301002c0b4100c2444141c2103082c400074240f440c5000c079518810020002d5002d807803d424220050b901102610302c80b1102c20305082c02000034410845c120701c00701c42d103000581c031200000d40b03194060100240c2d035840c20001600c03604203410000b825900804581080d1002c00f1042010402080015481841001042c80d1a2030304000102c0d0300c5a4050207004c4c003900340b800208822368400c0d412100c54980101c003c00101391a584000e002c1c000e1031054030006560611055618801841040c0c040c411501801e80303403170040b680039038981e007008000303030180001c1c4400002c8240e2184001e0240314420322855841d40d00a84100040381805481c003d210340c000740c2004020758001440725040440d41c440d1440b100c052120450740d0707001e1482d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 36335940 1250 36334690 36334721
    0xb10032007060510140306071107080304090212010f080a030f0905060d0902090105010e0901031e0b010815010605070803060108041106180f012a03091d0603070609060906030e01 78
    0x200c1c030707090000c02c3c0c0c00036015685900401507020f03035481d82902c0440f00003074a158103420403008544a1030054190b403041328a10001c0e140069a28045c090850308030340d0015071480e40020f5484200a144490980074042005800329001d05040d220f90f40c41010714402002e100e0820042068180903d5010004000080020f942c4003098107205001c0d043c40001240a000c001001040c2c1c3c1d80a40310450711148040c00200c0ea5a18548540c00c0c810140c04121031150071455507000400c1aa560184c040c1103400c0084c5041401429800710240c1c05034008002c01c00c0034072075140012284008c9a40118091810401a4a541c100007001607019403815500020000b9140d840c040b800309846c0004078102c1c4ca8551607600b15006564943c1d8071091080e000907413125202c8928481c18541c568a4000d141c04003144e070700c0d090700755043c1c8402d02000c0030052a500401c8401e24080060401800c8946489007280349403000180c541016409500145502c1d4141c040c503042c000d61080480c90060b58 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 36337190 1250 36335940 36335947
    0x91e0c0203040b18120c180406021608031e010302010c030e0307080d09060e06090306010e09010b1c050613150b0303220f0b070506010306050403020a0203070303081602010b100320 79
    0x121446a8804111540a00c0001e944034005a0380424022600040031f020348041342c1d280070325032640c180024001c403081079090007aa0b0301c1e00080d400c04c5203000d01c14601c583ea41d042041c500001c0c01140800441a144444014030060340d21142c901d0b01c0f1981403c281030424040400039003428460340095015202d041c50009030950310014910440d070854807640301125466040c00742d24442e0782600ca40640c1710f2401003100545102070103521900000c000554111002e0020b031400c0da82041c0c1030400d02d4902412003c1c4141440600e8104494980714030310003440b50340704d0300352141003040c40d02e1207079949045900c80c0e2014130403100c6001e00d42546042114200c00c00756140007003406240005031030110003054040c01c0500302c075503540d0070800130001a845c1d9601c90b0081d01004000324110b008100011005803001c00c40300001d18460b8540d0740480c5071007001f410261403580c0c02031046a040c0a100d154980310310202880c1d0780030f85d00c0c000c10f0481500b626901e405050800c80c0c42801d2000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 36338440 1250 36337190 36337207
    0xb0702040b041404061505040b060a0c080706020304080a1202030613050709030213051005030a0819140307081504180b0a1b0302070203010c1103030f0402030f0709021201091e0c0203040b 82
    0x551046c511441058200ca00315a180e0090104540122800d81e401c160204510701d110b500407900c500f003e03807080d003645141c16a20f13a20700301681c105541c203d031078800c0454400c16441d08100342c4401036911707901c00c50852a101000464036182c008804100f01c0e80c0e4004641c81c1d41c0b1507641d60b4061070f0050420b410764850405404010701d000c41e0002d201101d0030b00d01144910f4045401c11000b0380100c000b6007051403e2034416032021407880680b09000004511220507074404003e14812450340d203810700c141ca40040b041080e0bd80100c4510711513460401e240c000945908801070405400c0032000c0e81956a254510f00146036a0710034a02c05010149030880707803036043e0020000e00344254001d00466107225025030364140b40c00c0d82041d15420a10004081d00221038441d90310a00007001c448108208040580c101882504010201a0000360400603c005000603600408000004104e003100c080c4508940440417011000c511b47c590341403446061080040d20050010000c03116034a0108 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 36339690 1250 36338440 36338453
    0x304030c390311060301030309030809030304090e01020a020d030e210d020301030b160906091e0b0408010b041802030c010537030c02060c1801020f0a060902030708070b0702040b041404 81
    0x728030044515800880141d507490414a040da070490798180c42d581c001303a00710340d65440c05400c10640c043d0188410300000900c0351160054042c030007051000140d450a080000a043c400403202c020700385403c2850071403000700c000852a540d94a2084105107600884c0c0f00080d01303100d11960100c849001000100a00c01081801406012480000182c0d10460740702650301903407610070513021400300813040009801c4400b821480600101100d220f40c3c1d201c0e40b01c0050350300203800200d0340d69941c80800559082c02d00c42c0c1d840c2c2200b441c56840010322554000380d40d5445101510781005001300740f00403418035918080d1100e0b50860000d050885851549041c00b503146030003140002c0c1864410081940080307811402144018460b51a080c200364151001b5500c4a10307550451040510740061408203011050f1000e12518001c00c410116004040c9400010b8021034442d4020f50700400c07945554400f15004568151004a8401c40d01d100150040c002100710014080c200000c00041110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 36340940 1250 36339690 36339803
    0x70e010b0a0807021c08070203090d0501060602010b0414060d0201091a030f06040209180c04080f06070e180103060906110703020607022503080d0605100e0103060b0304030c 76
    0x801d5610b4003100c0e82d074481c0807070380e6008040740700b246071401d00805141c0782c0c401c0da492a440b80c0d050045900d492448808550440d1a202c0107807020f0f5510311051061550a00034100b08401c100d07000e004009403641c070104001d9014101c144280700c00214074045900400c0c00380001c20310410347c40c00c100c1008901148560040707911901c00020800096a40c0c6828403d45490360300c0508556480ea07008504c00c0c000c020080c5c01030680c20010b01000504420030040040b42c148103002500a078200380b040a070844044210843c419140150554070f04100561b0031030440e82c03c280080b8801d045418100300070000584410108040025503000707042e00001c01500400d107940c21030b00901640310090f480402c00000190b10090440c0c0f0800108150704080c0c601c003d111030707000620300d50300c00001718180c0442d420640413900382c603070050312981c1500c82c20b0003c02044803103619510706030b40c004204140044005080314502c0c40ea8800c0050b990402904142025241c0c2da408034440101800001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 36342190 1250 36340940 36340957
    0xc09020a09060302040e24191505070b07030f0b090c0304020a05040519020c0106050a1203090b04060509010c03090305070f080c03030403030507030f031e0e0628090203070e010b 78
    0xa0040900060382d5100c0d108440c1140c641c82d03000301a50301c40d0304071582014200c2c1201c0081b8440e060400c14107a852044004c5c1c0c6c00c0e4281030b03002481d440c2034080c5040d00d1a03210f23400c040c4401801a200030a9405017510f60003006840c000074030140014098000740142c40e035450308100f80c40204003010154400071350255000721000d0124541c0d4408220a584040b948a07030041120711600e01c4044964002d080007801d42000400c03620b845e000070404a81050f448034a407000614003460906800205100c00340c580000d940b40341c2424800050028428200ea00e410805501c0031241070505c0391a000307016550100035100240e40d2a980c1c458449c0c514000c1319414000e10194049510700007040318100c03545515541d00b85190f54405850003103400d18a4401c3c0f640341c04a04143c1d011080c4062201282c40d00002102042e4034040c9141c0301c4014a103400c0301000e001da525180c200c0140d002548641404041455483c6101007400c0010540c8440b911420100010580c44c06c6040502100c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 36343440 1250 36342190 36342197
    0x210c03020c010b040e0d0f050705010515010f08070207030201050d021b07080c12071e120503070b0a05070909021e0301140306060a03150506150d060f06050c06011503090c09020a 78
    0x70101e450400046544540917403c465012450400002e40a00c5c0c014200c05c0440c103050b82046211703110142942c40c04c94201e580300e4507410960b0803544e04481980206203140c0307000b41442c070348828060355501c22400003034140280842c0910446000342c04480d4811194a40046552241820719a80c0d0090b03000f03003005409030b8481c202039030178582071401c00c05400030024140c892030300c54500c0426850030b60007500d0f050104804140614400ca07181c0140c2d1244000316075640541c1004400008041d1203818502c0c201802d021585e42e000c10317070f00241d4542d01e00c0181d4841e04404a0341252900b07441c04900340e403012000140381c501190304014240300a4003500c2e1982d56030010841c404505000003842e003100890342800d6202c141d48031940c400c0340030317203441e00340720b00c5000d01440d40e00301ca401c500d4650703215081032000350081d13202080109054200582840d01c0c0400c3c40351960301c1401410300310840314010014280c460f80100c2c0c0c040e5002028003031349a840306900806035000d5103a89011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 36344690 1250 36343440 36343451
    0x91419020109050411090904031106040507060314060d060b0102010e160806070e01090311030a080f090a090519090203120301060c120513060e180a06030501110901050307210c03020c01 81
    0x114109801000b8465809480c900c0c034001b800000c1040d1580054400d030100013840301c4810700c001c0c00300149800b5a02542c02012458500503000b0142d5001910b40304030081039505000294582c1201044082d074480d101142084c04000100c2c01028654000443d6101d4071025003010051600c5181c00e494051080d14550b50320401c0644400ca9040d114a000450840042000c41d1202a50b4001e00d50010155021071200707803a400080d030010300307032542601c41c0010000018900100d2900082101e0307032060226103444080200d9100c2500b00f400f080c9600c0d5102901103503402d0206101e0031402e45081d580b656180d0500400510010804582d00300e40d080c0081a000e0188041c1c0d14030100ca8418100304904020088030b400c00f010b541140c10101c2d06030031400c3c6c00f80d601074451041c8410380001a4803455411f0242c20340308104924582c02c44104020541640d000040340d5020351103042c0300c05070000c100352140591025890003409039141c000c0034207941d58103070014007030107540704c009124 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 36345940 1250 36344690 36344699
    0x11060a090614030103050604020111070b0406030e010b010e030c0f04090602040806160306030c0506071103010608160b16140f03070f02040b0f0108070f0203040317030115090b0d091419020109 84
    0x410f03c42800064040c3c0d111038005030056100e540d10000000c00d040a032004e140d40c5414081c825005500002d000c82d03290300d15001d581b002440754140d05034091a06402d02c000d02408640c0340c910090748140030305500100c000844e2103036041410019804402103580350f680b280c0c07454440c60283c5000b0104010148448000da10a00400041d82d0300405022801c5141070100a0030b580806400c45107481c0c5005a400340e030f41e080c030543c0c0082a504014010fa6052a04107a12070009034001c0d4142d05414441c0448100740c82c03905d041c031158080e28010645010102680c508400050300704558071000443c20100b28540e5005020940b0075035081c003c03501404204110124240ca1540c005403009000942080c0300743ea03442c003d030340030380143e82c80c00e03869450741c9001c441180c40148003014008010002d1a0705100c0d00c01c00c41e490b6280420203a4100f281c030303411600c100c00d00300240b0354403401114144aa040780090602c8070040484100403202220b0348100445440300382d001c608035200015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 36347190 1250 36345940 36345977
    0xa0f06150f030207020d02040e0708100e030f090d0c090207170906090d020a120303060e0106020c0a0621050103060c090e0903070f0521030f070306030f03030911060a0906 75
    0x3800e0000c544a070920741c1e041c040120b00a4000040a9034030030ba08844510142e1164405c0c01e0301122020f003d44076840c10240002d140c601c8441d601c00c400c81c0b400303110124030300b40842070350090300c48554034070b5686a000e0005421810415005003810480c1c810019070410035600070102030380b06111000c1d480400310000342c000e000d203501c569000042080f14892925040703104964031072000740941c2c135a0b501c0e61031900803800004003c8001c2640c0c1d1006004001c8c107a110140140b03014030080c0102c01c2454041952110540714203020f007c403201942c1952000415225034901243c1010422907940341498405804002070390b4005c0360b042c00d80824208005904d03a0300c01d640020081d881c0000301ea890190580520406071158010303100407142c6165260701c2c010348030004505994807420300700203269072040040c00a0040c549401d100304005044890b89009081d00342c2800541da40860500c8080e0381c6021080c0e07a4800400545002c050b0703000f54906084d22410780c0d444002c2c0444c0c01480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 36348440 1250 36347190 36347219
    0xb0604030b041b03060e0f06060405060d08070501020f07060b011205060a1202040b090a0b030609030a0801060806010c020301060603020d06090203130206091306030b01051206040308150103020c060a0f06 89
    0x9400304101c1d0700000c020686940000342d01041c80340c142c99800d9070741c2d200c0c20704540c82403c940c280303500f1451030107814500800c5055004030088900b0842414413a0001d402d51300e8410000380120310203c1d85000b404000c2d4182c3d518512084415540d402003031414000410050361614045074a0030541101002c8901c40d003445080040c01c10b40301241042444400081c2060040364400e80fa03003454200e0352251700340c2038060f003045100458214143d0301014284000109000c07016401800144284c80e8401c5085045804505100d0030544500c00125801c1c2d400c02806034040d030030200c0026a40354960300804949446080400c15540c44081440aa01c015100000c0d204081003000001d450b01000a00100b00010841100c110500c13103c03500b0f036201a802a1942c4421000411a41c14903c40c00e1148040e0000905100e03e065903002c0d10170320303002d4150401c080d45040c070700d85c0b40d0b4003d60499524220150071203a080c43c041d001c01c0064034001400309002410480700042240614268 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 36349690 1250 36348440 36348443
    0x190801050916120e070315020c010501080f0307020118080f0f01110a090b0918090c010f03020c100c090503010e07150509130f02120a021801110d110f01020a0c060b060403 75
    0x5010030240050f0710701014000000e088030083c000e5110000c0040c3c0a8400c1c5003500780c100c940941c607060328800c043d08544050340721201c0307500601d811000201c03010040329000380d4242040c01c0513464028403c56104466003040c203551082d00e00d031500d940e0000030210628090400244141c0c41041d06a0009000b5011100c0204002d100203000c1000c551000e041c0510024141e0503131540c030900d0301030207108282c0304441e1540080781c40818030f503130242c80c448c0c2c3d00311241010b616001382041c41c10b658440721140286030a83c0c0d81c4140082900c6200040001c12000300203100d1103101011440d251f11003481881c1c80e050700c03c0d54502940d4003440599120000007404800f2000c03202c1540e1000e0902e0f10001262240d0820510503d40d1103450040d01841da81240140c95000060000403008070844511f410b00106100c1c600c40b4200010740f02c401c500350f03480e10155102260354160710b44945850140490750020600d910403503401038850144034060642132064000303107400d0209922a5000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 36350940 1250 36349690 36349697
    0xa050601050f0a33050c010b0a06090905101a121e040b130512120f0402030717031204030c031b03080a0c11070803031906050d060e03190801050916 65
    0x20204044d4440c48850141c0c4102c100c0b607503c0403490005507107010000c00d01030b14041a001309540d40c2100c4240700b82c0030500710070f4589070b0900b406e2820240503040c191047d40075003501c0e100000c2108a4014500380142158281d2004481124180301447c3d0030039113055444c0c0c0c2c07660002800140303810383d5030130903510340d081009113584a07600c4a04250800400c4081b240c5d114044030000030724200600c4440c2039601540d140c9a0042c0c580c40050104060308a041002c5414144402f6070f6010402e00c0c100c91601462050281c26442c07160b0941c017403580d282012013a010108010f00d50484c03141140c00d8820b5803494182440ca80d04034040c21071440300500040e04440004008652a40c400c0301054103501b0844e43c00b58402008034588600c5030408203103900b0200601ca081d400d1081e0094210b00d040d5000c0c001c0504150126000f0003081310040c242c141c0f00d0104500f07600c01030086a1200844003180b5400d0600c000010f0402c1c082849020b024040410018000c1c62001111a4040301d040d42c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 36352190 1250 36350940 36350959
    0x150503061c0203241009020c1b0301090206030a060905010509090604111305040302010c020705061c090303060f0305070503062401080414011d0f01020a050703080901021204050a050601050f 83
    0x903440c1e622440500e4220781500c2550621040c2802d0300303050800c10a020039180f103c0d880e1034a021460f1a000d0f43c07182144a0060105070480e000c003090452020312038803030f60401114000006405030040d1a006900b181000041c0501716416801000c280c03500309038244850b9036298207208201404450325000b582068000c2000540b10b01b441382c0380c070903000b1300c035440f4203004140c0c2e40e086510940b412070160b99500203d152403a0140325181c0241400c1b9401418540707001d00140002d42782802e5940702c03c0d41c2d1a890404c05029a0003c405004a80c5850840c50b4481c68540d40c2d400f660700030700703219100e030348001803075a81c6c0341140c140400d1048603612481c1c46240019508200301510498800c11101c6222410700402d20038144450882609442c018040407485814080340f01c40001d140d0340100500509903400000b01c0d1f280325030610344075004c0c0e520b0780005802070203080b5082071040044002e20080c401c1c00a41175035031b640524140d40603660383d5400c1210300101481100e0700701c640348 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 36353440 1250 36352190 36352219
    0x21f08010b03040f1a0406060e010605041413021209102703020109020301020c0a14030c21040306050a06060e090f0c0a0306051002070305070e0f130f051615050306 72
    0x1035000d1600a403203201c00d4410110203680c1c4280f205c110202038100488003804000c140b0034107018841c01060403044000c0c440d41408001449032065010344001c00030b0050724031410b9100d0550711014a102200115111401000d0296155030280c07020700d49841640921104c1140e50b118a01c4000f448581c80000b401d0034140c032008000c0c0700340090741036540c4c0700081d00150b1028002040710320610382c05002d10084502e01030107030b614030300310009441e1720610005030250800a64a5100c0704404100072201c11040300001c0c89200b0361300000c01c807034105010f0050713802580e04442c00751161601e840301138103241c605201c0e0840c000c945e8102420015000701e0804070180b4010844191117180c041045501d440205007001340700003680c1c0c01640410010024400107200d09800b17405c000408000c50b0034100049200c4690103040da01c2d144a0b410b000320704000b105a00454140d5101058407010310251441c0701a4821074400c00e0b0301d4012410800d60083d110b10308507881418010400b444c11a0130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 36354690 1250 36353440 36353459
    0x906010e160807020c13020a02070806090706031d010c09060e060702010c03080a09020a0b03060414010311060f0c100605010e03120301031403091806100309020d02091906060c021f0801 81
    0x28000a056001e030360804091611a00440c1b840605c4400000d84e5400c00d02000914010081c2e1000b11550494014020103201c04141d0780c080b10240d1502091441c0e0324500c0c03c480c0601490000000d6281c00d6030001050b4001813528111303174581d01d8100c040d034041c205000300d51052000c0280040c4001c0d00c07450001e8050031007660421900d00c000503c4220300d03804920000e0b2160050500202c0c040100715a038607180c09038400c20700138249131101c00c1d4559074902100c00ba0040f00e5a105100201d07911a40048507015184e0861002040b43c001aa07a00c500d0780c000e200c540500c9001034140f104600c41403c00044d0720408020090b800741c5183c0c0707103840307950501000c00802002400304100d02d10051b50b41003546652801d06056480c0345081102c200f140c911a40d00f1620b00f1305d0709240400001d40c2d00d00034450340072501030300c0c031103455504e440300e11880c01d01e40400511050318040000c03404a900c203e4084143d4401e850901c0e602d510340d03401c4c2d606e903003122211a000803101001400301035030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 36355940 1250 36354690 36354707
    0x70203060a050a06080a06090209100509070e030307061b020c150406030902060d0e0709060e0f0c03040303060801060b1309020301080a0f05030708070f0605070f020c010e0102070f09050906010e16 86
    0x8070f100c000488030f403288911420015018019038502da15003003404150700c2d0041c0c3c1d01e500041030700c410a503030903e01404503545010050058042c0041d0039071038801034800f801140c2c0000c0d480394003000201d01c91448510290035103010140144144c0640d5003150610794519200a40d04204107030401f4680740040303019050b103040c00c03a00030070180040c0320a4141402100b1441c1e42e08005451903504010307241045403c1a406071140d4041c0030705000c01d111b00e1000803a0000240c14001e03a4950325828190042d2110b940201c00c0f641c0f0b406800903004046002074000356624241505032141d5401c1000240c0c082800751340180e4100504030f4000800c05074028825510074001d480c01c0c441c26443e00b80e090340019800307441e265100c9041908010a510038a40d1080603820400210a49000029034660034414440d050228940c1000c801d41c2c02000144028020102d10001054450300c0580203480d054400e00604d220301e40c004508004aa4501442124070440b0041642081c006c01c031607214 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 36357190 1250 36355940 36355951
    0x2060405120a050d020105090f0a0b01090b0d0515010918020f06070c030501020301090605011101140103020603150409050102070201080f01140d0c08030735030c0f0f0c0c01080606070203060a05 85
    0x1c58207003150000f640c284419000d072501ca03000010f0728079003e90854207184480030038240d2508850b00b03603070000d10300340c4815066488807000040c41540c04008514908001c00000d4242c2c4a1001403900e030070850000d45058641d1030780b080c8422100c1e0114141c0403a000a0001d500407040c80e01070185081020140403403d000d1b4091003c0c8603969108e1608a900c282c000007821616480c0501146d40c1003400342941d010030300d00030002980e0603aa006844403040c04001d20034200000810f81c248408155001d5241c40107208002072140c1c1e2a0981c000d511502c400c81c0425045800698104070107202c5074100c0303a80b090101ca800003040c007004994400c1000071903142408002c0070a034204200054080c66105440b001001701100070301e4526014141c649070110800803030f071355440000d00750989802400c00007185840d010b00c41442c0044c1c1c040c510800510040c041601c1d10300c500d001840c101401000e03218044561030740c40600ac1e680c81070300c60194140c4e12490129803811071680c001503000c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 36358440 1250 36357190 36357193
    0x60d0b060f041d0c0c0d0309030201020d020d0f0b060307090b030a0212150a0801020405061804060b0f0409060905040816050a0b07050a030e030304050d0507110a030803041e0206040512 81
    0x100ea400040264000382c0000c0300b41c1d064911600202c2e100030754181e8001c8100ca82440c01c014002d600e6555030a2003000c401b04050b00c0d03160007020107000f5015600403080b46001992102106038203d00100081507a002e010f50910341c442c441800c1203c03c8901560407550382842c507604244161fa8076600203040906201c1d4208031a0741800c2c00d64540c240507030090841000c0128281d0100603407645150030aa42d01c0c0d10421080180ba0307031f12000c80e000100459050407071000c5074400640140031907400003542d00c4000489442080c3c172907008105480310f06004000003a1610742400880e40c0c122001841807004005202000503100c0c04440ca140c4140d086a48102240e5034120603154152400c5e030100c3c0e00401c503105802d415001d07496440700303030318019030440ca015107410783d803000c0e031000e0402403100014480b01484100c1100c40c0b030078072001d444800866524581000d00e644211010f4500c55620b038080d079000c140b00d03000d5003e100d0300205002c1c141402d240030048021002c4c1c41c40d030840e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 36359690 1250 36358440 36358447
    0x30d050711040c0e090f061f030f18120c08160f0510020307030c020c060306010c2a030b0105012c0a0302030f01020901020d050307090e0601090302060d05150d02060d0b06 75
    0x1550750ba401000e0b0040301c640e48503a07000c1000024070143e540080c00d1201900c02d100c08014172511140c64071241e10000d00d44250b503203030300b80105800a0054801018906041a0481c204140020401302805216207001407400345034140840b0f0010080c01c000380380d00004c00c02230100300c64280e04a0f0016001d070113801e1541c1c60360b544043c6000c0003c00e4015100d9000302c20000d4041d05449282085460790014029412000000400900c0000c1449050140142651007031041020001011410000d6510854103c00d00255446080da03c401c4500c1343c14100041800d52003039000e8100c4c81940422106e10000e6150504d03681c81000c0c502c280c20104818001001d6941042000c407000c080c00001030750307001424002401e180034804008103103c1c0030020300112a6005021a007265001141c00a0781c1e140c420040320109138a0740302962010020403059034ad01040c2c1d2055015040d04820790b544180d00c0001d00500204204001e54401c0c0d007800160704122190700000c401c024000c1c00c180c074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 36360940 1250 36359690 36359723
    0xa1101091805060411030901050403090503070501020303041202071214070603060b0306010e120102070f050606010f0f052104050f0708010b011704020a050d140d051303020415031502090102010f0209030d0507 91
    0x1700b0b90411100140960b440301d00340401d15403c590820081d01064000d890701c2c030308001c0080d59a11019000030013144003981c0d4100300510030320140b0064160346101e20788048941c1403480c0b144c04100e01e4200140100c820000d40a0301038428241203481104002e420365503003034010348010012a460035006070646400d142028020b100a00e03c452144958000039140d40c1041841e000c8004d0890741444500310301c00300c500da01315008500780c02e514a000d0740d8440c222800e4000040022412035001240750050004100e80851040214022102180e2110703941d4a81c082c241d038404454280802c2100c0000d0300940107052007039600a00141181500d00d0b901d5000c54085003070b0180565800003103c241a0360401d0900665950442600d0668103088109288010b10b03441031000912440e41c0300075002ca5203a80f400310200071138000c910084040542000c003070103940407525035070055107042c50f0300a502038107100f91501890041c00400c0381c82c0c1c2100d01510a0751003c01c042d2188007203c0003034030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 36362190 1250 36360940 36360971
    0xf011203081f090c030f0b010e1c0209010e040506060103050c0a0f0203040b0a020703050d1715010201090209100f0f030b150109080d0905090c0313060209120601080a11010918050604 80
    0x2001092180c3e40060300700d03c0400028200c59500380241c0ca0303a0700700105400c45a03413040c804003120f1000c440c55524003d0004504054510101e0002c1d00a80004000030303401665141c1c00e44034a0244c0180c0d901c0c2e0b07540100440882d6001c079070b400440398041c0418103806104240c120342001060045a10701031700c904056045030404260800141c1c030402007841000010700c140400b4080324246207844d011055190f015204000344003161040f840000740070b9607131003504003a60b2141c01070506201810b283c0760715071842d40c482c0595100c10f100e14a0010341500c55000003821240c00c118500c4168807089801c1e40d800340000c41d090704109404001065000080c0007600d01c603901500d03090301052034502400401c0700002e0503c0b19100c42802001050029a0b41845040e640448016501c00b070074000a00d1021440b90346c100b562003003100205484000007000320159026003100a141e0440030b0045603481d0040c05a004400601103811184e02d131750740c201a401c80c10061010494201590118 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 36363440 1250 36362190 36362251
    0xc0a05040e010e0412110d050d02190903020a0b0403080702090702070b040906090b010507050c0d0303021c0212010902030c16050304170105060111070b041e0e100e0f01120308 77
    0xa8094680c000902082080d400b0702d044208819092040c004180300310714649548160b020b020034400c00040300409009d1583c1140e00d00c1300d0002d103061a50841d054014401d03030643c0000c9002d00c2d940180800c2103031106040d10100ea6100700b00c2480c00c030315075007441041440035110a09601c160100441c1030050140a003016188840c4001481440c04100304142c92104441c58144a010440400810340200e4841010007090350850100e04591808400a10400c1a03500010f42c03400710041c0207480c150000c03d5603101c00c258207551030740c9481b1000128401a242e40040c1c00b8100b04100c420500c2118010415025406482c109952150740040c08028045441e0850b591001004003e603084200b04007a800740e940100300b11820300f03040100c40d01c0b0b640100c04940c450281c0c00201d12006a5424001d05007841c0c0303806031401c080400100350b4519002d18542c0711003100000e5910100000c40504071202200c0c0d800120103035031070695080d20080d10603407c24400800b0b4940c03207481d035a440c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 36364690 1250 36363440 36363449
    0x180403020d12060501050a081b0f041e05090115030204090c0801170703020604091a030106030323070c03020904020612100501020f0111030c0313050f010504020108090f060c0a05040e01 81
    0x24040c50708904074000c00803082c140501c40300d140b5112040c443c40e60701005803040c10380981002c6900d03803140901d4206849010300304d649041400541751a038209014050811038800e2040c0701c86403d140a818409070943d801040d401c034034080700412094481c074a15114400141c1401450306448001e8801915038000500001c513124a004114107035030401ea9680c0d840c4c00300050300030182581e0002da4a480b8502c40d030f0405948031a41030085102c0500c07681e00c40e04000340200541981d81ca006441c030f0110381c0404510107294844900d00d610a602183d020961041c401d02c019400c1da403c002106070301401c01c0e07130444814800e41101c1d035012040c25010750b40c20b05010b40b0640ca03150009103000301c41403d00081ea41040f21141142900d4800d40b80c0054070030760810b03240d0395000c20811707142070502d07000b8000b8414145050200743d8103501c0240240c0c000c0c2c1e1524510f80d140303022983c0c0c03a00350024410341c0d90300a00000c0e4900800d40040d0542078010b1401502e03050303841040b40c11480b000c2c1c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 36365940 1250 36364690 36364693
    0xa1b0606031514181f0c020105061e04020304110607060501030203010c0309030516080f0a09080105060a05030c15160606080c0409030f0c060f0e01020711030616030b18040302 77
    0x61050000c0a22014100c030b20720b200c00e00030a080c030194515a0305000e401c1e10b03014400844e9105100d84103010144040960f60419064030816240220281408040c6e03d005540313404041803d600742032174114101030300340300c111400820b04000d020003940010019551803030f04800d0085186c0d202001440800e000303000108440d41940105400c440da051540070501d45414099000260001d0959908040212074411180f205052641c240c1c030a090b04440c2c20f81c1d0002c0d05a101a800c0400041034403000c00080005a580c2c4051003001c00b11402110391640c000c290b0000140381039001c03c000c0ca00e4446030a410901025210301d56055481421a12242c4546090010b032204000455600108490604c0609200e45010304078810703030140c1204214204401e107007841950f0704140302042010340104050301e2505843c5000f50491384041b601184982220034441c60002010f6010f49a1414060400801030505070700034100a040150454440c05861a0800b40c00b80002e10560083c0c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 36367190 1250 36365940 36365951
    0x509010603091401021305150702030f100e0a151a0301061403010f0612140c030304030605010e060108010e0c091207120b160504030303050c090916110105090a02060a1b06 75
    0x26040790800c400b02410f034400d0380305001651851105008801c1221000d9488562131240309115040b81d200320100030350503104840f8620013400001890007501ca1103500104030b00e101c00160301d070316050b2201e00a07008101c82c1541c43d0450307074140d20a403115010100c0c41414840c1c060301080c20740d03d80b80d011234500308102d03035401502e042c28020101d43e10010002040f929040020743c28200c403415101900e5801d18480d213105005003000705200010300141121388499403440d1200162000b4002e4400400420002c86c4165026041c41416540034140803045c6035510506149250029141d082e807040d007203982215002e6040c040b80014151024940d5210b59040c104004c40220203040d0045031094070103070105196000d001d075410b49900d86008602500c44a101c0502c81c003801114981c042c1c01101070000c45603019400291011352504c9040c4440c1c0da01d01e031142224000c40ea007824540210a1000040c0b40400080242414a0400801d000364504501c110107503082030484000380c1c1c4c1e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 36368440 1250 36367190 36367193
    0x1180201050901020a0f050f16030c060507020315010305030307030b060304023109140706180605030a061809023f03040803040902130b071203090206091005300403050304030306050901060309 84
    0x140241042c0b280c2c1d0446010102b441d5550f00c0401782c4003072241400b00480401c1e03c0003103590602501556004a86450310706584900703101c3d44941c0107480f2200030929005010545040400c10743c1c4c81036400a001501004000b04041c4400030380091030f4000d1000315051007103900e5240300b8034005601074540000020300f03c1e8090385c034001c1640c211405121312002403011020301d480218081d0742451030311030b032241c0ba066030340d80280c0400e400c07410505403000c480d500015803541c0444445030080318506200b41d00e003e1002d0011b6020011400c44c140000c0030131710354040000c01c1c02c0039214404212032800d6a50003185013942c000d6004102401e80004240c100c6441c40c983c46006051503170340385498031321f050380d46400002d14a8403420515403180c0c1040c05550310700c4252580700c440541a24507c5500510040490b40080741103068600104074a80c0201005406000045080380e01030107a80c40b5910151400d8000900840c201516010007185640f01c0c120614000e2071981ca020030000ba45 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 36369690 1250 36368440 36368443
    0xd0201050f10030f1104060f0b071104020c0a1707020306010602060118020f040509100305010f0f050906010501090b0c0f07030c060f02060601080105040207030e03030301060804021201180201050901020a0f050f 92
    0xc2c145034204195804140049101202c0200c072240d40180030900035010480842e001d02400e074404118804400d00004490740c4d550014000f4500c0b5041d454034500b00402008224000c07403c0ca4041a400156080700080040300e10962000f580c003c41801c00d0032036400240381c00e00c00d03000100160400350040118001d061450702000b075000c0005c0d4207010761604414030900441c440c0503c610041c00200c1d5074500d80c405944007464111009001c2501386d134044501a187d2528002c46443c43c0a00086003d07001182c03141c1600d105075075040340340380b0b004094081600710b0070181030b16025121610161420420044000b503205120001c2442d01c1e00401814032620390340d00c1820754000004103c00c0b42e83c010780103030559000b102c0068a405603410204c0e5151a13109420b50140320001c0007051042d0000302d42c9129510072500055180b03502c0c4c03015401d81c2d031404007607884d5801c040700c41c00041d0b000b880a8140200e040c41114115040c0b51514001e91201440a81d1550001c008800030610b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 36370940 1250 36369690 36369721
    0x905071502030901080f04031806020606010e03010b1309080c070f050112020307020c150d05130606060c0308040b06040b030102030411010306080a021c08040506030c040f090504320d020105 83
    0x4031400036605003802e000002e084010300030300c00e280450350280000e00309030140c55202c0710448190071031b44240e51910342c040d5a07203000340c0b442404508580d5010741d4614050017103e415207005005068581c0f0400007584c042c1460070021a09214107211140200e981005084010281203009001d190b103403074009420543c90302002c0644500400400c014180c0010301c00c01224401c0c2c1d0074102d104c0e907031304030501c1600458032850041414541401a02d8048408051211b030240504010565a400c0300342d0749565102802008640503c0004000c80d0711101d800c0c2e8466005007000c204150580000ba08980c000c0790111814010b554140342103507414403843c40038107801c8000b40741000c165000210b940e01d11003002c40c65201c040103044e0400003030741c0c1960024000504003940703d040c00144026250410300500e02e091821440c0000c8141036402902e000d107410400c1e10100354514560402e8104038030460b03440c01100c60303501e40f0040b002003090304600d40031580002840c0c2041180300c802d500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 36372190 1250 36370940 36370979
    0x7020a050901050609090405030f130e06010309050d050913181110140306030a060501060207090509070b0904020a14180901050301050601020c060a03090f06090506070c03020c010c03020709090507 86
    0x44541d001805261940c104444a00604984401d142d035280d10300580f541c0325004240d0140c0c10080784450103d80310914007000c2d11209000c01455a89245c011070844504103c090101e40c03058110106290041c001021a540c02800c044280306510503600306842543d034595498400081100d1f062001404000203e01e50403900000440340e00350000744500e0011090400300705001000c070741c480e40c08000380d0f240703d980900b06003c25a5145406915014a881412007103402c0100080c4c5001001c11050261603000748124108800340052200a40048030340c0c2051006851010f90b800c2254405008060076603911500407601540a000e490401030344024001ea05140601c840d0780e0b000315480d002c5090a5038902e49800040c4011030107031194440140949002120030300c01c0c4049034200c010b00c68001c40407200d8035190020200c507958900a80030300103030001c2e418890700d5845040c94608407806131040b50041502d91032018120b849000307040f26194084d075801c006040b440c2040880e41d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 36373440 1250 36372190 36372199
    0x60d05240f0604141501050715020304120507050a140a051605040b03150403050f04030b01090c09080606031c09050603100807050303160204090314030906010e0c04080a12111207020a05 81
    0x91303641038607001c07a200015003807140e43c000c0031814441c1d0364416401e480060b41c02000507148201914400c40081d40140d4094440400e00684503da40b8014000c403170200f68484002c00c0310028a460382840708003c04503044440c0039140c428004110100320550022141c0003003145203910742020041103544403041a800f035006080310101e50360116000580c46034250a00c240d95001c29030200103144911f0300020700020f60301c800461b845110b40d000d070b0740a61503601d07461352141d00e51080c5a0f4842d001c071061541070307000f90144ca200300600320154914000310b06007000f00c2500c03600012040c0c0c00c1190b55410039410081d003003208110411010b0000d103002c1d000b451602c0358000c2024a80301e510040079000b59103c2c0e800108051080b092841c1503000143d4541c4c9034181a41c00d00d0b00c4040038030801224120700c102050780400c1540403601241d10080040110750348a648261941d00f086079a4401c1c40084a039581e88000140051132070300f0007055800380d03144c84e188100903c205c29070704440d018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 36374690 1250 36373440 36373451
    0xb0709080303270d110c0a0b0d090503040503060103060203010509010f0803072a030317100509130f0609030c110307180e0a0203030f0c1005190207060902060f04030b01050301090209060d05240f0604 87
    0x32190b841260041270915401050448070760078070501c0d500c82c5074050364040c032407a8000810b0003100d174040e5040e07038401ca0703040c00266031300c84450385848001e0180c4079041d0000c21020700026203070b1110788510100160301c454904510a00c40d92510450f81c01038000c2500641104490704443c0c0304d082d480b002a80c00b011802d0b0070300021a40080c001401c1800e68010400b8600602030701b0a48000d8684d1301a1041c03040380075a24008000018004c411200f0070760010006805180115824040c0e944611301448400c28141d00140500302c2800c0300e030018051441000d000d46c406100074200c64405600300ca948188007801985820301d200c1e05100c006143ca400e104601a00b210418100d42104501503120881410013238014007403003000035403040c400a04000d8521a40003c0c104490040c050380305030340c1e41c0c1c00c14182600c410402c02503002c10306000240e0145400e0091128050017401281c4080c05110340882122480e1070904100c072010b841003004041011030541e610520543c0c0c00e112 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 36375940 1250 36374690 36374699
    0xf04091401030c0e0a090c0906050f0409151503080706090308090d0804290103030e030c0102011401030f08160303060f060c022101090f06090b0709080303270d110c0a 73
    0x1d4520070f8080c084c001e520520100d49603881e036401060780035030001c14240c0c905546414a40c000c200e18814a4020f40c1d002417400a145403511a242d80c4640003110300c0f501480303211a6900030200c8500300300700d0b2490401c000c404110302601404c3c60710b100b150000b51044081c1009054480300030415a0b299004100074007885d503004415a4101d40c1c0454074100c0c0c01104440100d800c9580c0d002c160355119018000014142c1c010701c1043d6010b0f094043d180c4604a08004a0036685c00c0c950103a50541c2c544c1c010000224149070a040003405042c48500309400510b000100d5902100140d00280d260101408600481c90313201d401041c240c10612461518ad90126420460003544d4506400c0e0308007071000d220340c0a41201940e035a0011400e058a901480c01c28001d2110910945501040310006200103000351903203425100c0c10002541140c0d121020308980000d60007001e4609404104400380340d450030006004940c0c1c0725201d481c034640307070b060150b0300d00900080306500c0f5003840f090401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 36377190 1250 36375940 36375953
    0xe09030307021b010c0b07080f0a02090d020d0201030b0907030f11070203061503010b061c110405061215120109030f05090d02011107030804170708010207020a05090703110f0409140103 81
    0x4403540750102490f800c3e405400041c0d41d0b8000c0d5260140c00b001a10b42040f440d00d43c030401e15031284100003104151501c65402810807401080c0075903411000620004000d89088507014000910500d40071a0507500380300400c90b151410b0369100040b0742c4542108035150b01c1801a0308044c40c80625190408240303070006036581401601074190100c0d00100e0500c1d40d14290401c04410364060441aa641780c1c0c0c68580183c1c80041c1000c4c010035180c00704034048031083c40100d40071500000d0044d400d0400c8030f403d4503507103400941000d1103e07850401c1600036880d6902c0c145030402c40d01c4000107080005040c06400c21100c0010601000010801c800c0b0700d9030b8181c1c406401640a203440d02c51140d400c0015840c00c540b980024142503c0800d00185201481d0700d400894000201921801f90759502420b0a0340107031031000394801c041e203000380000c8c00e181d0b8219921903928907002c2600640b02007102103607031245032140d01c581800a000c1c40500514011280d900e44900c004102d00d61454403500d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 36378440 1250 36377190 36377203
    0x1401050f0103060509010605040203010605071b05010503040b0a021c0f14010b03180a0f0819050c07091e0608010221010e070503070216080c0918120a1808070e0903030702 75
    0xf042940d94401040106030254400780280002610456a1b0758484a018025400c4006c040713a1100004d0711144000440c622158119001a101d0703c0c00c50301c582d51a907481c4940101306140140e8280700044414462840e8041d042c07041060000748401d8021206081e03401401c039007800321000d00010402d0701010b40440764060300c403940340d8150301c1d01010388504000130140007828603408000404280a40700e0700802200c800d00096106112010b201980c13280142641d0002a03000302500700000454ad40160300514081e821015401d41d04517510400c44004d904460f00c1a94041110502d400e40352600019580c1e00059811a56240c0117940c000d00c00001c05810030440c0100c00f003030171103008000c80145580c0c000c0700e045004ea102d01c41141c5e103000800b00c46101d09400d4002c0b402200700c0800000710f02c0d1122000e072038001e07509285400950300c403058110401c4800380c005209084107041c460050800780740540095403501c01001c0c00c00310301070f10052440d0010001d03c002290005041d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 36379690 1250 36378440 36378443
    0xc0d050a09050301090c0e10060e0d060b10080f130c0902130b040801090209070807120e100e06090c03010605030607120906050c07031101020405010c020613080313031401050f0103 79
    0x140d40d0034881100301c86a04950748055055803e000301281000140280034040e101400f00705043d6540b24405050011500d2050740f020451130040e01500d401c112140002d05802107202042281c03650011404042d801c41d100e1001542c100305000c0e955462118483d0003192083c82c0d03112030150354454a0890056105410005600140a100182000f0307922401010364911141d02c981c2d0310070b883c601800070510204d124180e48400030300c00a00880820b80110110f98403510403000c0303001c4050041514100c0001c06200c0c0c2c0071108188103040c003c1003031849044d0054002d909008040c1e40c901000742844521a9043c030000780243e44000a800341e20140e1460400281d403c00e0000d08003c040366079000d031001741800104000c6d0891b40000342003051084d940c095003888450090390807070240780100c60001c1c22400c49a0090701d4072a01030035a81d001000e0b0380d90b820707030380f002c40e103256500c0100303803407000f421a8504000780070002c1821032003170805500030302032031600048030b005840c0305000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 36380940 1250 36379690 36379697
    0x2070602030a03020d0e0f030a1e0504090b0301060e0a020721021f0b030312010608060916050d0f020c0f0d02070e0a0903020a0f03020c0f030a0c0312120903091a0c0d 73
    0x410b80c1c00e4800321b410111003014194244c1c0c0940710002076003510b9500c107501d120041444107000e003500030a6458005080d2109a480a04143c10008030304084d01d814410706d60f00d5903c5002c0800c0c00a80c900800340601c20b80d2400603550a21494001d44180c41c1659001c42e003241401103464190b004106c000e40e0030040c004420f4500c03080302400c2d0040000c010026018440400d041800c80200808035060321180e449140540c0e452004200108800720307102c7e05442d00c0342204d070b9680d0340110050310844451250207d034144502c10154201d8001504c51052075100e660405101c0c003052010410100071440502122402c0c03004082d2801000f415081a581d0f07203440b4081403510901c0200105c6500005450b0951080d0600030342c0c0d482c140080a01c184080c4202000b103160000d00d031540c07503a10844045145186803940c510042000180c00c050101c050f100148220b04c520600c45014841d0300d44c0c60031903051204d61031018540792219201c40104101d20201e8103800030300742504294624 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 36382190 1250 36380940 36380947
    0x315050a0e060126040803011409100605032a04050f0607050714060705010e1c02010606021f0b0d05101103091902190603050a0e010203010b0f0d090c0e0601020105060102070602030a0302 82
    0x443c420321001820130f50041542007105020030040750a000307504031240101541c0c848a150020000e10640503120b146070121000810031009009001960307200643d83d291210305c451342903110f100040d000415501c01d0200107001d00462038582070226604006036a11810f18038680c4d2001e940324214001e620320b00022041c040320641e200b6003180d181c00e41c03002c000d010a21841d90f0b00c80e41c030b884a0000030a0501c1120118409600c140310314411100698001d2141007000d00104006469508018840715101c02000c011130311803c2c4400101880b9a00400001c0d0710114120f040340c2d10f0303401400c182c640820921403031071000540b1984035a03c0d51940d04103d0710502c005000744403161100031141032903030400100c1caa01907210340d00c2000881070a2100c1032034504540d00301c0c8401d0040d080c01060030300c10440640301d490003903c40b29044003000100c0501e42d840b040725a290550010359a58401400c00019590a0240940102c82070008041c0c460a050307000c3d4980c01082ca54204245c2d010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 36383440 1250 36382190 36382217
    0x4031103120d020d0c02120d02030a1b05030103051b0904021315090c0e030a0b0c0304030216180e0d0f0507081603050406020d05030c030a020706021201060315050a0e0601 75
    0xa11141d2400d404200c10150344100c50142e0001a401c115034403690586800001c0e0207060010804400c2c03280d2040340f462410004280c440001d4101030072500c000c9036980c41c241e0303c0b80d202c682c02800149664440e50748a40c910b140052504241201c41002401540b08041447c0c0302c000305681c200e0350441e0f8060b094010302e620360006110414034104484090031002a05007010340c041c01e000011541e44003078014002c4107056139004c0404005091840020000b007183c0851401740d80c10910070320543c2c80c8140340300d861949000341c03504004036071580c1c40c054404403a014826100030031908800f6007040125400b000d40281001c2e90207405000c00000c840041000c2c039000c6400c8001c2c0308008440714071650400510f590018014000984074011508020b50b0042096030311800c0031800fa14916074504a001c4069000b6100c111038940d000e014075501c8241400750b1038041c01c2c042e94009032000d002d13020800d030802598000c900a095003142400781e020b1015032254049400e0030079188034041d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 36384690 1250 36383440 36383443
    0x6240f0f0c1a09070b0306060306090402010908121201060c0201090902090105040b040b03040501051f290a111e070506090d050703030c050114010e04060510050307060e0301051302010504031103 85
    0x2480020510180480e141c070b0348204035851140038400e00e50850312800e48900303207a0854881510015400340302400010414582240d0b42c6912920626110715000c4c0d8400303405150402d1041c03003020782c141c04901e00d41d003140304012450040c4542d1902c407240c5041600040c14913050790003010040d23500054206860390007001220b0081030a40c94640d03072260340c6c0b0b46940d42608280e40807941542084086102032041e00b0034446502008100880000d03d090000d20314003909820102496944480b071552440e61321002c0c003100c2c030a5403a128014801d030510300c0d0401d0405401982c1c1c1c081c01a042d142c0c0c560001500005890007030740c0b070643d10f200000000ea800880802c00400c0d600c0390020100c00c05610400800c0c80c42d100d1002400180704454000301000750074000d010a01c54258005070201e94203800c01c0d608641c240751182c402a03140d1021a003000d8803a040880800c01d290020160f42c1824841d40d039115060201000c0e04500e2580001c01d1446684806021002020100545541c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 36385940 1250 36384690 36384707
    0x3051e04062403030512011d010e060301090602041202011205070e040e07030c06091a03070e0616060c090f08060903190e040603060b1011030d18020307030606240f0f 73
    0x40140800c466140c0d0b130b180c0105030381d0200f00c0c0b8001c030f8820100001801c91840c05511114400103128521a0303003400200340c0c40003001030045a040d0f40b01c81418011030000d1004001411000c40741c0d07c842c40c5940005460b1110001d81d409650b0b190070200000d2039400312000b402e4510440d004290f8406068026192030b81c02e40001d0510040f403580000d03e00d0700829170310111010015124103114080c107800c1c580b030000712000000b280c050381c41c40701c071032508000401001d101d480b00d2041c803c849440d104100c0f41581c1e00711001c41c030041c50500c00b060fa003c040c0c1d1300900c2ea89009000c0c5161182c0c5180d100d0007040d44000d500c1c01f000d58865005802004842880c10014204001041ea00d08016010700240d800d400e003d01c030501000c0e00700b94031a14000c0100c0001d84011031400c026021b29100400001b034070a1141441d114034440140d505002c2c43c0c0046000e40000310703d007418000c07090f042e4220f241e10440d10011032825445103a4204240e003000c0788050030551000400480181c90b15171 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 36387190 1250 36385940 36385991
    0x406031a09150109080d1e030b09040305070206070507141306081203041a07020604061a090c09030a020901080a020f03070e040201050f0c0102070606090608010207030e0d02010c0f0f0303051e0406 86
    0x1030b5200d840460f5501c0000c043d0f14100b08042500d1f00845410144c0440d04501001c640041c1803c0005020034010b800402c803251002d06994500811038442904000c4240c012611076600724001a040b4075117001c00b4019113005440070032603540fa00030704941c0c038030001c0040780f418000800001c013440000340f014030420320f002d50144900d00d00444000d443d0101100c0031901c0a141c040c1c3c0b0304071082948a620290b80c0040c002c4505d58594480c002c80319048042c4040d41841803410703120050703c9a92040d8000d00c174440003003002060600c1000b040d00304804e40786010346d0040070100100c0718a080036981050302030034856074030f2080041b0200da03486896142440b0303600000c0c00a0030403409500000031100050320070018117446612050a078814040040c1c00684840c40320103aa1030802a0031841e1841410308196103943d41d50785010f290340708003003900c250819026030000e044d00360149942c4175a00d05016100305d1950503544003035003009800946500c2c1d032145014015035500c401d800040c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 36388440 1250 36387190 36387193
    0xf0711010e19060f050307230d0608030d050a0b21010603061a04050109020414011b0606120506010902190305090c1309170c0a08070302031e0406031a0915010908 71
    0xb019510200280d01c8901c280c80000309840c615440691144054034000d840640d5900010701580358402280301c1c004543e070301120810000300800c44882d200c3e000042140c20302a54941a599405a0890308010030540041d410a800c928907640ca18201801540c0c40003031b83c16000c60040f01ca180101101d4000408040c03403e01c400d040320b444a100300c00004400c84090010380c1e25055140d040c0e02030341c441c1c2071206083e0b804903421f6601580340352509070540c000c0c5c5d62041090b074440409407012a4014648542c03409244020f01c070041c0005800342201d45019880c000d46079540e00321420400c070403401015075840c0812000e402c10f10217501d180713400074203031402c0c92100c0d0b11500007018603000c105e43c3d411000c50f940c50f22280800a175080300c0c1000700680720510540c0c807040050341c0205000c1301103000401451484442e8441580071a8880c0f8101300c0d2140e05101020b030454112900380c0c030a20024491401c0903554103c18194801e01003102d1105c0e8442c00740059600f40041d40000c1c0b140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 36389690 1250 36388440 36388459
    0x402070c23030706030603140109020919020d020a0306051507050705010509120604110f0301050907090518010603050a02040515130b010c08030901020c0105100806010303180909050a060605060f0711010e 89
    0x4251725402c00b5040d80e000d1010ba507145070307100000368200c0d0003400c0001e4004451100096034190003100c1d07003800c4200100054a01018070791018100c2e1300c43c62188001c00c0c1d4505081c00b95040c904014100c8520600586d86450000c2e1201682c1e62107501c504c0303040040005500310142c6400c2d041e004070702c010002b1920395042510b40300d0100c0d46482c8206000d902020b00400d00d0b482c050003158040c40c0c0e130030040c282290a200440002c1c02004201010704500038003001301d0044244654401140500b0280c0705001c80b620400040c1c510190043c100030101c0302c183e400950380d54175440726200a01a001a88420b8000166008031012034054000394000c07040112444d010b4009048903040d00700204001e903650350030410380c80d565000300e0580c0e0f8003140c010300001c5c0c0500ba1a15045c1640c0b0312080c0e281d0b940c1c61210303043d00d90094084556401c512941030070400b090003840003130a0300700c0381c2600348103120311210601e0091032070107440d02241e01400c041c280d000380d50ae600c010700e000c1c03c0300c8072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 36390940 1250 36389690 36389699
    0xa0b0d0605010806060f03150a03050601120506070503190e16120c0806011a0d1b0c1a07121e06030c0f1202010c030804050f03040609080105060402070c230307 70
    0x410891294038080f80010000401a1424004450781a1761034020301d415a2164048000c203084e04951082d0001800940800400c000700318aa00a100650701e1340700c142c3e007924000382400809403001d41444401e000381320301258060f440b0000244000c800090b1081e224ac00203141c00212400090800107034140440e206020400c6420340c103008084c1e11310364907525243c0640c0d0700c0d802d00c182c0800781070044006588140c0c000061190b81d00801e80410000001d00700c0c14680720881c941c1102048030308280c0f0301003100705450006158100c0342d441c0998504054080c01503600f80c1c4140c04215900c00603110000d480b17503034141a5499418080181c2c0b502c900e803d0003c1c030144d015140c0000030b00c0800041c0d000c00f980d080f800896040c0e450b61070120480e5415900316501800813201c03800ba00310036008181c0100090301c01800b840c0c1c0c401282601d4244180e003100c0001d442a40030320f00411150003c2844101040c0460f414071441e400d91291540c04002040e0002d15129850f0260100005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 36392190 1250 36390940 36390967
    0x51009030803130317060906061b0709020309010c17060d05010f090c0503070e010501140903030d050c0d0e07121403040f09090b06010815130b06030405071508040507090b0a0b 77
    0xb03500c40c0309455182211448a16200c00007100702e5811f81e0140482d40010402c5c01c1040c003078401c40da070941c104c40c00004001381d101d0406040e604035040311079000c410848140000d000365004140b090900e0f03482c8081400c81401a0700740180310038000d401c1980c00c6410860250701c030403480d1071840d40070450000c40b868920303100505481030501c20322480788003080c9944d40580c885d040340c50507181c0c071410040390a2018402d402025102c1d925000a01211543c41100d000e0f01e4800e5600403a42c941d11030060f07400e241207038102d0052440ca036206910610110b07009201b20264503400844c48802c8000f000b440c0744c9548603582000106015100f00041c258410780c0100d42094455006404503a8850f401190103d01c200c1d80120400084d04074014541064034035414045103016001c10b0043d5900041052540300f6a011501d03580500c1c400c010721145c40644c41803440781407401f0b20f014140346d2241da076103484902030b00000300d642d2042102166202c084c1e00b4000d240f10550191100c08143d00312 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 36393440 1250 36392190 36392221
    0x314031f0e0f010609080703120507051609050903162a06030f0b040b0d15060f0b1801020a03020318180103030305060a0911070f0c0506030c0a0201140103020109051009030803 77
    0xd00c40d151000b00200310140168505016101c15a0090243e6031868980903038034001e0741c003650306019041040da00030031400d10203c0c611149400d0140c20306440e00e03076104200e4100501030901900107210142c2c0c244005070402c00c40c00d4014003491100301d45000c038400c5480c1e0142070300c00c00211003040001c1a41e010781240c805107450301c500f001007107006030034001a2890182c5003981320b900d841d1494001030541d00c071030307401d0b19030450000303580c58942084903040c001642110980200203d844400030b0115a00710444403c21301c040c003100b03042981d020b03540c1d02441c00141c1780b405101c00300c2c65060b00d0380500414901841d400748800c030359403801c000d00104400c1e50300901906096034040781d100c0c101c1c01010041d804101d4001c3c5010761a0315000301d81200c10340100c1c0d5a4822040004080d515000518043c05142d920b050760742d003045e8000390860784143c01c50403101002d4401080540e8000e082030089590964010100525120044a100100d40c02c0107000003008800d2240318455407044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 36394690 1250 36393440 36393451
    0x20c060a09050d02030304090e0a030906020c06030c070501060506031317040617040602090904060f0509122710050307091e05060c0c0d030e01021e0c01030b06130b070308010e040314031f0e 83
    0xcd1805058070b030801280c5543c03410405c590400020004a841c0c0400c800051101a018a00019240c0c3e01c5000068041d4000d44440d031068824a41c00018081c03104021450115503001c020700d81841e1210103040c950041003480202c0c119400041c060000325012108881d000034110841486c061038500024034000011882d03e40c90030000800c024400079146c001e0124102c1d610b0300b0141e4151800e003501c81d421610718480000b812048940c3c2e1070b000b8242c541c2203180e840d656140c1c81c050750014034108599000d01100c0c030790041e003041d200c0d2000c0000401d035041540c4141d034800c00b8540907494000b0030f00f000c540010103107140c502411340c0000d0302042d54500f42d00740c0d0045a03c00070213603040a03040000b580e09403c1071000803070641c040c1e4044410309401030681410300b0a6240780400c11451540200070000700018001c0806030700c048024054520311481040900745030718010008506201c0108404600101251050030650030030046180350b0060b0b0509152502202c105140b005d40740d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 36395940 1250 36394690 36394697
    0x1609050a0e0307050606190506031e070801030c0b0304082511030d02060a090c0e01081507030c020d03090311010e0a02040e010605030a080901050f0d0c020c060a09050d02030304090e0a03 82
    0x8950841c1072010080b103945a800000030495900c17500d040208044d29110254800000d02d0700000f21078903480095445810064070680c1d5040c040b05000c00301800080c0705408121b1400c0c01840080c40c01e82c0d240064a00b50f401050b240d40d92032130b03c2602445410140070841c03078000c0102c0305204060040c480d005100c0e040c07a80c2c1050004061550700d001e10405a000751700043e00161500c0c800e0750220314031501460440103041c0d0b0710981c0510030704083e000700382184c00c00011a84805103414400f900150315140401c0500d601c803034000c2d100c450306031a07101095113840e8ce11041c580700b03015851080c6100c400030410813403056040d0f9900c850180f0128011400c1092281100406102e41b8085a03405805417a10449913540e400d95a4000800c403410720206002d032440c032a515102602e40e103000c1d0f030000070307156002c20f0000e0301e405d24032103509218410400c884c0c0549076000c0310200880f4404e5918801d080301d1032002a0541c001d075041b11740d2140c0f5002c0c851009240c00280a00c03054041d45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 36397190 1250 36395940 36395951
    0xb0402030a150f06120b0307171506030d09152d02160b03010608040602130303080612010c021209150a0201090c0e01030308040201050a020f0f0304090606050414060c1609050a 77
    0x20000f040e01d000d140704880c0852141c0741e000040340d40c1d503080141020300007003c2d0b8520548441d10704840e8405000034050341d80c07141000038030b841d0080c0851504207a00f10000c0c102c5082580b0000d06170031715401007a00101c100c0b04180700d05030064030000c854080e052076240f1580036696111007140c40d403507001d10051041c140900811140d03803100400b40c0d20a403008901d141e0034200c050350034200141007110001e40c2040000446401600c408003c4d51103540c03103c06a04200d0104034500d00c1c1801c40702c40a07450400360b885d6181d0009041e03c1400c0320001d00c1c80d1200ec0400006226604500100d5134681b40003c203000056410350000035407901c291352440406858003001c40e05a08240401408903000f08007180241d8055800f03030000200038070407215518168608141403481e000c2e40c8010780e90000c10180301d0361515004200c040c2003949420383c10503207061b00300100b0341d0318028000c2c003401c4001000c10300780d2018440c00150917041924181e16544c0d9402c0301c402000d08480c0d01ca8404e1a15 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 36398440 1250 36397190 36397199
    0x1020a021002030103122a05030a09080f0606040b011103041503050c1201090906090f030e03010f0b090103020d211107050f01021510090c02010e010b010c030c03050309010b0402030a15 81
    0x20702c01d80f410303243c10660108002844c1070741681d03410307041400020009400700f0781150b0380610f6a901613080b03110354055910351a12040140980249401c4080c10f90001c50078500707401c50009015500c2241210003040200a03840165524105030750441c80b140400240814103001140b61041c944d00142d40803c44e49d5501011046503004499051009452282c0100280c2e080c81c0c1004202034090440080c9a25180daa00c100d0901100c0c400c40114107110300707080a0307140c00e206204201280c1c01003441181980c000041c0c1f04001400000d105031448a10807090000000d40c40700800c01c00600d010700602092406000e14841320606c401d244280c0700081101d0602c4031400c0b0408606030000d11602c0b170112140503401c40014010411004142c100040d42242405901030b08903040e00009040507001010f182541d40660040b4140320301c040c0c1d070314002a44961140344907505031904e02e44a480c1c13a0f04160141c0a911a8030780d003d4004424081194419800340c1651f1500036240702c42e00b03944 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 36399690 1250 36398440 36398473
    0xd0f0c080d05120f0f010608060307050607060e15060a121e0f05120a05030606030a09060c0f031508070506070609061406030610060e04020901051c0b090708060609040207021206010801020a02 84
    0x80b60560030a0110500407c01c460080c4101c5802103c01000d44d4078494842e030201d42e07150030200085c1c4040b13854428811148400340300302c254450b00310040c61010303c1c01d4000708030820064803658400390352060b0320500388800c8440150a410b032920400384c3c1c503203035810140c030a0351096005403054040e082182014030b00716812a8107580f504d0300d80c0c1e42103031b550344200701311500002c0034404461f48802c0c222000407694824400340c2c2d8065102d0142070045000001d007103d0005100c0c0211000c065400d020038100020b10300704a85007200e0240e030355410b078a03141019062000c4010022410005000c00702d41c0124000e03845400c068003140c1c00f03550b86c144102c0c9034040a104410200754060181601820030340c005021160341030402c640f80c1400c41c1c86400f84c607060a01041c05c01b66035000b40d0b00d0f03d417810316007143e00812645040b10140c10aa80026000e202d407421032482554009120011900ca0300380c15221145504146c4880f9039582403842d000c6d40c08043d0500c0140031305072007622750011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 36400940 1250 36399690 36399721
    0x70512060415090f0501050c03070e0307180902010c0503041211030303160810031401020d0b0105120105270f0901050a0e070306020a030e030f0a0e0409020d0f0c080d0512 75
    0x81202d000c19242542c482000001c00310300030306641d40c12560b00c807840421000d01a29005031400c0030910380d00e1400400c010203008081200714407a03040300d1002c00c03900d0240c00b0404151400208000740d403142c0c9100594011810031f10060003800302040004001d40919081000140548042c0a142441c081056101d10007111b541141c101061032005400380304900c01940210702c81004080d413901e9449608195074114170700484c2d03a4001494004100c403d005190000c0420f082003410000820605030403030f0b01c1400b400e8001c500b800311501c1da00a03e08540286084c461109030b440b0b09200e40e01c460000001c40e0190419030074035010888128003413156009810028002c1d1092505660740c0074082e602c54035040d810107481c5c0004e0104100180020040c014107510b42e5070b60344a0b08440070b000e890450286502c0340b07144c92011030158680b41c0300d0450f400d500c0340c4907854200300c1d03243c4400034803400d030030403480d5208502d1201b450035048002040c0a1103034458148141da02c2169802c00100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 36402190 1250 36400940 36400943
    0x9021503060319020609030102040801091103070303020d080c040302090a1d03030903120a0e06090a030f08010b0708130e1003060b091513090b0f040b06030708031b0c04020c0705120604 81
    0x18843c9440750542d00051101c03c556900c0186018074103c07000002a003640c00640006000c0c3e5581d011f07001c100600308410070304212043d40900021403075500c010707481d440441c1e038280c28031100c81e00040c0310040d80c10464002e503600400c0c4000c030b03041079a041402025003011403155020700307402da01c205000c0001031741e02c10120380b4021803400d10403003442703075030303800082e0603082c2c92505d55108004a40061103000d02c6620014020828044a41070080808502031100360070f00860f207006202e510108400c0303c06c1c0a070040e180640d146034803041c0050f9250140d00c2040d0340445403086c440181008090305c5c0c21280640c00030300c01c16641e0002c100314044180c42d41038000341154001103144c10880c141c55101409001c0c00600f10b581901d42e9442000c1c00c0f5510f82002c00e08208000c00c0281c0101040d0f0000c2003a00108041800d21404694920407030010788281c1e0000e00031b5004800042003100c1480402900940d160b10030007041a964084601505105510b00000312110120016060b44501d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 36403440 1250 36402190 36402193
    0xb040816030512090f0301050708090d030203220f060e06090d031506110f0307240b0f1302040504090503070c08060f01051309080a1d03030913020c0109050f01090215030603 76
    0x304030f104054166640680d03035180d040003655054030b11a42c0c00713128507480307103a094852200d645407074a205070501c240344060200345441030080c00005290002c88104003001c41b0400d40c00444030f4140903c1d80200248020201c0f420204c2031940084003056403409080703603404503005035007280c5082d02035980c4101c1c640d1408020441c1000214841d01e42d03c0040d4485006484071031390080b41450447d40905030541d160742d81d640d0b03000e54800c450344c840508445507400c10080d8820410000d91084250030b455841200001d018040648007a41110014240104200186050781c5415526500710140540d50002e0143d00054010000320b00741c1d120b1350610a0344840d507030801c410031041a17001d100081000b0340e01c80589001884080050105010545904d0007082d0b031440f184000c82000090b05010380c00a00488509403140314080c20811926034015071a4000c0842e0345005010042d0080e0040c418081000c1c0031782c4066200c00c099600030b0302c44880315041c0d4804c0b10102c2c07006a0304d07079815 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 36404690 1250 36403440 36403453
    0x30f09062a02060408150403090e160c02040e0d11060f060901150207090908090405060301020412020d1e0c080606091b13091d0c150307080702070306060b0408160305 73
    0x800c25a0703400000c0c903480241a1130406464440c95460031101d0050b561020700b140081c0418580c015010300010046518842c1d614984a0080d6006c50070b04c4094109201949006108558554010886208002e400c841c1c0d83d598000004203214840304041c1d80d180101004980c07034103402034140744140c00c090081055179280918940c100b24942c40c02800314050000086407100e414090a5103690064801c9a2240100300c100004c940029200c40e01c41d0788101300c10402c01030171200340c0d13426a4044660740001e0410741804640c001c420490320104000f948000c50401c24140c600e8010f6462810480710030f0795a55090002110040d0781e0702a09403010080c4104100300100102030101c02c1303100000c40381d42d5540034007058845000f078801004401042c0d8050401040150008080b01200d03940c08510049065052911001d0902c00c104201400050003290081280c0c034011540700350100300843c1c0c4c2d12261161071b00580201041c034000c01c45480720010502d1216403c0d0394000c40035000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 36405940 1250 36404690 36404747
    0x60a050a08180a0b1003080d020301050f041a0105130504050c070c0806010b0702090403050d09050102090f151801020a0b04060204030b060303190e04060f080601030201080609040503030402010e0105090d030f0906 93
    0x7491009003510181e0b0100d03c0f0210011f800040a040c05050202c40540caa506150030032124880c1c180f07605004524007102d003403c00c1058002d010703250000b800c00c56a81c448140001d41461142e07085070350800e0506c0e00b230010856442005005032805441040c08030342e12502a25221142841402c840420912200340545081140c29801a100742099071501103081811800c0d548152001c0e00c41d42d6011030861f0090800403200a809841101c1000d00320380e66142040c06802a804540d081d00b40d0060050341c0d60b4000c01c060b5081540040d6170701914902464068080d42c068002200e0b000c2810700442e0b6103042c004103499688801c0701e5540403068401d0401c803803d040d851001075200d40c5412000916040800303a02020708840c0340905810360550002402450002d440709025080e89001c000c0400c5011066a4219609113007120103420f1060040b2518091009007640c8441d101320784e041010b0300607482c06040e00301c50b140c002c0b65075a00c01042d81d505501c0248401c003101b40415030b80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 36407190 1250 36405940 36405953
    0xd060503030c0307030f0309050d09050111070605030109020f070b0c0405030705010302040e0708060a12050f060c0403020a06050a0212181302090a0e1308031906050409022b02060a050a08180a 84
    0x4142441031a0028210308103448279481e02e9840b141d4500442d0322140280720742d59200301047e081c40511030080944500d0700c07400400600c0140b00e031000d855804640c0c41002c000740000c0322030490b0480481c005908101e91921b10503800752140900ca8450050002002d5000f0f0007030b42c007200c030400100d241c955900e40c800d95202100030040da074806043d44020071108a02c52000c10294001d41c001c044154101131002d02c0d2a40250581201d14814841000140e844585040580d422071030074545400891006901d4a400c03103040c0da0740208082501c04243d941c0152036003907a602200d5041409080301511401c074444c090810303030450725100c0107200b2400307000d92194201942215100c0c2c8044941c50340380094006642d510300070780045507940202e6400d401044c000d0801101c082040310040d90020718401550621880c3d2001080814043c107801c0000d5100720540140090741e0307403290828000c080340c0c04000048041401007000c17403840e0186c440b2030b16a01c1403500044c080c80e410760b101c55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 36408440 1250 36407190 36407207
    0xb010e0109090e0109120315050904050a03050f0f0301032901030b18030903030d0506030f1f0c0507060603080d0606030608060a0216140d0e030a03020601051e040509030d060503030c030703 83
    0x43c0b410364880480c1000070700d1160b40c1c0030b07a1208940d00081c0c1003c803001d1100300f5060741c2d8465403266014400b8800416004641c000c0311035894141945d0f541125407070300030207000783d1025a43d214070200001092121105c5a44042d000c80f400b00040c10081c1032809e94040b00030300004d8a050b500702c001803c62005a2161000764205e40122400c2c11041d0b0002441c5921010104401a483e10180040f60408020202c042d10034000034020b03019403444c07011458810002c0384401d00e502c40e14401c5200b4001d00494000c1a0403080c248a42504d03428190031503400300651100840ca002400110184a8480c09054664540c00f6090035118221680c1c065000446101c0d8015102e80d0420b000a4509a00001c0802c00e032000d089000084138001e0208a00282824020b8015001c083c0c00258081505815640d048910010240780c0c40900e00c122800078000c560040d20703180c11700141120000c040e02a01d03043d034406000c0503072540c00303041c2c490145150f00100760340148007407800280511080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 36409690 1250 36408440 36408461
    0x11d190c090902030c0705010c0906020a060902010e1801030b1b220b0c06010e01090507051e0c01020d0506040f0204050904080a0e06030403030c02010507090617040807140d030b010e010909 83
    0x507880764590b489141241e005403001c1d41c4003100090700000300302c2d007030181c50700844c0030b8149011104d1400d2806501c07003043c0e07807008019030740e19600716045a0080346850701030130024000c940c0c000811501921042421300042d1707100d082e404e000070f410b206110180c10f4805060000c440c28003400200818604204e441100d4051101e030310f01240d52041b0202808402039903178010030165152144641c06940306802c4007040d50f080c04100114103400c00100d030304108003c156100c012560741050041800754009409107940000f60080324004103402c034038050754040300c2c02c004e598141d0160f64100d11451003296040003411000401280303440018200c0031401d0b04044034044606000610254070454045001c241d0b030f018115800740d82440707101d038001032904200c07c8075400d02901418003420403ca04082000d032800050800012500740c800c02540311520b04410720250305079649403209806a40e0000345042600740d0258030407202003d10303850603140c4221342d905111842c0c1c05080680c03e07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 36410940 1250 36409690 36409697
    0xc1204060b060c03070b07050a051209010f1a010207080d08010b0d090f0602040810050408040506070503090d03020c011101060f061b0b04031d060309060609070c050d0503011d190c 79
    0x841c25400d0700e42a0051204083d42030113150b50310f14500e440c180b0340070058010420401c050040810b0340f03800208480c1261003138402e43c20b40e03940b90300840c0e000d4419810290b082d682460070001c0300c4103c403115012413141c26001d82d10319a4680c0503103540c070b003a86118500028400740042181c01c8c0104020030f4002c40602000c0348100464540f003201c1030070954125035680d8002800c101322035080c4411740041030001010701c06401e05031551059802035010b4580714030300001d5014204030f0200b0490f011900080d0000e41c00640703030300700a03451704140811140840c3e060540300b100c101d018411310b02943c0d01080d000d64207509050044501460050070b1aa00380c1c0d81c01204404250b061a045104034865941c2c082043c01c550040c1004804d8070700c0b01402050306200b44083e10700d003c07400e240d1100003500e545049039a11201114403008501002c1c0480c014403c032460701c0d0703134458010360588450003440000310407100350701c1d1058101240c10000098402c0d135175034481e41c8507400c0707008944858034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 36412190 1250 36410940 36410951
    0x307030305100b0a020a060509010c0e041e0f0501050102070806040f06090821011401090e0408030417030403030608010b060909070c03110d05041404050405100b0a12030e01020609060c120406 84
    0x40d0a5144d200d546002d016034000c9641000300030850040075803140a000003880102c2c0c100074050401c0041c0d901c3c061003a81c440c07180084100c02d481c01544403011450050090704a0110000d00902c000c1c00381d60700600540d4001301c0c130781e070740010468001c550000410640c404191911030041084502c1220301140401c0307104c0008041004201d61341c19002c0c450b80c050f51421145030904c0d044c080103a414846404c4c410054960310102c0b403030740319820141300c643c0d1b655070307103400010703104203c404510342c0354044188014550f1592001d010b60311144020441c1201000800c0b1450040128440d40040140c0c0011446841003022403c04c41c4a420846d10f8011020000d6041c49903040004c00085c0c000b1400700400c0344852607007400c5030000d42d01000507080c6a1116500c030031408214050050700c40c003034004c19440c1d01c120100144104d00c0015520502803070002c01e8441c401c2045070062107000c0203d0110311010840350f001e0410141220b10380030491168100030344000b03106941c2c5543e1034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 36413440 1250 36412190 36412199
    0x40213090809040903030e010608060c04180f1e060506040b0d0e0a02040216030e152b0501120605090706050a0f0509090403050309100b030a0f11040f2c030703030510 73
    0x140a004c005610a850104940e202c54501a0031140c00d544418407580c09081171004030b40402044405503481120600024084080c019001d800000300b00c8400310328190201d545104c0b11400084215594402070221035a91000c00c0107030302460150a1344408200081840d10405c1c0e80700b5110064098103a40744020036400050898022861841281c0c011340400b404240d480340f81c0c80e8030a601105c4880250000341002c5800d4000d003803200d441c03c000b505102c0c000605145a6048200d103a84003071107a580c440718240003150380041e044481500704000b0464205000c0344c4031003607801e40c1c0e81d842d041c44a180401c0380d1000720b214147c0c00f400b0041140303440760f03100e508840d88100d00a449803176507800d201c6402c6180c00d114640125066113490300c450b000d66004501d415503160068204448007143d4108450b423024200b262a900c5032811040fa2481344258001c0850090f0100d8001d843da418480b0b5040b00d80d5002081d48020340040000c2000070b802588215008041e10110215250702d8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 36414690 1250 36413440 36413449
    0x20c01030513150b010e060f1602030a0b040303061502031629040c05030c01020a031b06020f0a020c10030e100906090b07050c07090603110909010b03070909050114040213090809 78
    0x98211000070f0f02c0d1514140d095558010248102e030301420740f01d851400105880b804400d000310080440034140d5142600c06558041000241054100702d0340200d900386894080c000f0191442004581c200e0141c1220b04140003105403102e450f081a1800b15446d1142d9459149240e840610005102a40300220700341c90300c1c2ca801c0e03102c0d5101b0314074415802d080034201850310548040f9a4110b51010000f00002584150003040d0254505200d1700c4201451034980041d002e00340d22554852004507049c01036942c005415441c02d8802d0ba0740da0440206c0c0c5004500780d07190130078121045e6110220410b00f102c0700d0340c404005070340034240000d034000150341c8106d40d10b20241c641e03500144000c550100e61f00d20912407507008145509003000100d185990b40c51040c5031648a451142084e072000440c50f010a4020b000b00001c02030540300301c1520303002ca182c000d12504405030340941c8bc046008503004d00c4c0301421401244c005180319010820f100c5804043d198000f000c69030b8034024005107029843d03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 36415940 1250 36414690 36414713
    0x801081f0f0903050c0c06030105030d030b0429120325050c0301050f010e010b040513090204060f06020a20010816050c01110403050f01110f070311070801020a020d02030a020c01030513 81
    0x803940d2101c0e41d03481c411751130a14007800805000d1041e80b0400040220380d400142103600a01c03a81004208100e800700060f005103201c031981c030740c240c22040c0e120250401c07510b000a00c0e10811103070b6035a0302190380022552401205000300700308091a080703020b00c05408020600c4e02d03101c1e00c00c07983c1313509068001c2422f603441515110150303007001b001440100e0303400318003e002d048040025800c1515041c00942814141400c1d40500b42d681e921800c15512103030401c3c009841c0c0400d0300c03902035684550003542c900c500b100584c0d030000d400710400e041511030315015002aa05940303441e000c0d280c460642c1c1051410450500600c03070100702d504041c1c1402e0040740c2c0c0e1428029070158581d45182403c034100182d4011020142e498005002c6040902206540c01ca16026010341e40700e59040c40d0075507004200c0d16409965114600e0009138064054008100c0c07034810341c0c01d03103100303c1c0d910200380d86d2401623403e01c60150304003d2450899503c03036401140d01615882c203841e6040005d85070440c2040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 36417190 1250 36415940 36415943
    0xa02040c02030910031a04020a03021603092c0117030403170315030d0215130b0108100e1203060402070303110a120506061602040905030714060a0506010801081f0f09 73
    0xc0000c181c1e0f440600e00700045120400c00d80c00c05002910604002d00d03001c002c0346210078400c59001c141d44112030302c0703a41a04c0c00952030800e4082c1a111508002e080c4941e82d1181403000d40700840d500300d10888500d000c111a05400d241580700341d0821003580304680209903912424841880000701044042c01c81c0c0b00782156800d0303015904e06290700f0300000d0040151030346010b90b10114017131341056400030320304140c44690170b82503110307865100007c044007010040c041c00b90342c100400407500741400300d06004104094541081008166040640c441d8000b100e080b0b1648414400074801c1d0410b50000c15240d403007480e00040100494080c0c2d0003940100380c2c81000650003014443e20b1140910030309070891070072034206003451341c40202c82600d0060301c00020702039515030b4105001c110b000c006591240350b00203078011400c0d4060784072940d2014200e411000c0341c1c0c01d003404611103501900380e00341a00c5d150390160074022a584034000c0905045010310007519640c2c1d0200250581178803a01c050503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 36418440 1250 36417190 36417193
    0x705030a0c0201090902030c0a140d090602090f03010606080f090a0f1110140405120f031204200904020607020102070b040f0306050f011508040507030b2d04230a02040c02 75
    0x2901d850000400036000b81c1c00034140035104005129502d02c0d202c05454480150749421b401450050100c02000d000d07808011011500b4400008100300164024040c520307410703140808250900c42c10982640d0452140e9008901c1d80720200e582899142403181d8096280030846215582d65915210b40000c06002900c0101c0c0540503000070386040c40c1404542c01c00c0789040f202512034480f8a000754030692003001c1c85140428070f11114080140030780c440108500041ea03441303000440740c0d4201000c0485007140c204965040402000600d4226038140e62405058103131141d44030750901035294403c6505a066109141c00019100e4040c002840a80042c00c48903100502d14508801a164040e002c07206000c5600018000040e245600ea00d04101034500b01c40f940e04c50f4180a4180381681d0000ba101c00351220401120300c5440b0500c540a90b405140c170740e82e00c000400c16148405003500d0040400401010080e494103100d01c803548400d800340d080c2c60140c07282d0b41c0000d00b182c00e80a4a01c015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 36419690 1250 36418440 36418457
    0xc07030305252f0328080109022101090f0b040b0d06091a0a02130e07120b030106080f0604140a12080705071202060402040b06040b0d0504080705030a 66
    0x40561602a01d504140e80a030b582420218510354580c0c44a035402c503103000c01508241c40c0180d0b111200f190f42c0b8044001c032010b660304004100560f102c2c0e100080b45114424407680001a0418151160341c428480b566803e5032039091801080296100b40602c602684d5203030840030b07100b4564071002d0700901c4c60410000d00c0850a0320304a05960b8041211031080f40780807618241621001d0440407426070001340041c8040d007030302d441805013003605c3c4100303c0c40c80701344200104018180d00401070303030040c2d0404504607603035454104c1440d001140d004000603c1120800302d0000301d0340080840c2080100049041610340c4046460800000f40300302c4554800e41c01d001c01e000640c032124204e80c0c440c0001d08410000d03074407400c0d00502c1c0d0140f0035041000200000d02602c1c13064054900083d4030801c140e07920300b80c022000355104401e98041c2d228074034103804a00b00b481c1c02d0007250110703144030900d036050001c80032040c0018080107000340d03010300080080400260041c001440440c1441e26040003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 36420940 1250 36419690 36419693
    0x70905030d020c3606010201062105071505070f1104020f0403300507030e0904080d050f15040902060f040b0d180201050301050d030c020307080706110d1707030e060c07 74
    0x107050060b0395043c0d40f40703202000041020142400c189031307880040000c1051a880b140c1c0102d00401f0b43d544907030700c0c0e144441c18060042504030b00840c01640903008803589591070703141c102c0189075080c031001c1c0414020840a00011052501a00041e0140094800b030408020201d4140d0b0b00180003001034010010303043c030405c03845c0c8046a01c41813180c00703a40c414081854500020300f40c15440c400c10302001082081c1018440c40042c0c1e04283e000d0f10030200307410300d40f914003510303004034410081c8242880d001803841050300d401d05104540c11100ea01e0070800603014400100501003081c1c0e007103082002451b6060b16864020401400614039465540c800300e0943c00444848076030303100b80f001c4172400480150380d102d41a030341950401c0b2800c2c01040403518084c0d421003c912402501405070502c00141070350046515000c403201500c0350910040c03050b00e190380700d910140c101800301d1050f078184003400000a50195201c0c0071800c0024413010008540c61074900f00302c9580c6410800007802d0710 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 36422190 1250 36420940 36420949
    0xc0303060b07020d020915030a03050304060b01030915020a05090306041101080a02030103020f040f0b131a030c030a030806010903080c1b190501080c0904020c01060e0106081509070905030d020c 85
    0xa020006006081a40d41e5000812136031010704c010b407040313040d8070114003030b60501c404104020741e0041c00c0302d007005500c0c40c0c068003541003242e0503503c46151040c0008203500900480390090f42c0303c54207040044003481104000d410590402007040401d1125001d591420080d16000b240290000c0402d00c0d00d01c2c00041503004010014803403907005100400040e1a24074900d100c1c5a41101c0c08240008000070901c0202030302c00038240e104603140b952034240181d650000c103a100c044641d20800d50070101c145035031545038514140d0990700c246150804248254103040c6c0203d01450100903480d80d85d101d01c06260003010702c261941d000070170910034203004800400050346040d5815210100e03100d201d00c0c0804c035a40304241c14000c1501c002840f56072100c4c100d84200c04001c0046488001d003200c10350003030245010780c0c054200e2410021402c903002e000e8091040264103034280102080c41c00340b10400300e02030300390001d200c540c800108030f9540c14854a05481110340c0109156180c800410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 36423440 1250 36422190 36422201
    0x5010e03040828030c060209030102120103050601050102241803030c0d1505180a0b0a03050604050f0307050d0c0c12060b0906010e06040504021c0c0c030e010801061706040e0d0c0303 80
    0x4124030707420140000101d1000c03c28500381e4241c00d099804e0981d5060500192289020459055100080110f19003880703050f0b90741680d00a80440b442ca80c0c072100160780d80d442d05840d8541c9074000640460b105d50568817641e074010350070120316640560610060b443d541064540103c0358030042154895150948103171041440440842c20000345070074041124481c03030740401d81e2100c42130b2002131815105070b00260310444000c0d060300304440e500d040203a01c1e0001030320200c0369402045005104081c00100356030304960400003400740780e0b2040100f41e48241f014507048450190311072002072000140365801c6845409401c0124881052100f0090082e1000344020705000450502d81c84a860300c0d4207480a070340d401c0c1ca0050b546d0410301003800c045046038005040c4d050614a60750341442d0300c280d842140c1d911a0b00d850780c26000400042d541581c007402030070b0010b00d206880480c920305501c083d45d00b000020740b0004000c10181d14a60030084020191000309484541d108101503161090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 36424690 1250 36423440 36423463
    0x2060306150a020a050c180106050a0207080601060201060501120209010504050d0c09090605060916120b011407080403020a0902040b120414070f080c0103090b150604080604060c110114070f050705010e030408 91
    0x2145894001f00760603019206006210810001160002107a4000c00c0110041e250711021602c9030342e95500d00a004c0d0011f8094a8002100300042000c2440c9030f0080d550a034070141c5030749042900f02030500071300180c043d41c151004441180001541a694071903188420f0250030046224507020301882046000030344080049032804031240e025a500042c0081100703c41c0d500410505295030040382d2040342803803c80c01c500800514841001500801002182e01c250342c1c003000c243d0f941a00f20102c1c01544202d442c1840c0c204103491403943c1441520394401d02c40c1c40c0445200340300c200410f03e0311000c0c0d044821382640d06681030080c01740400c00880001e02c24078050004000b59030311114449000303400c000103414041d4441040d603481c042590041c040c1c1d00c084860914260a060020f000101c0c0100d022603842100d0031000d01040c003d44005060340003207981d10780c6134450300700c6183c12050111000c00030240220780005e4021f004801070001c401000315203c0b801c001000e400d00c2000d458 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 36425940 1250 36424690 36424699
    0xc02030f04090b0a050d12050a0201150e0406050916031205040306140406050a090f0605060319030207090c0504030b06010e04020405060c0f120a09030b0c040f08061801050601020a02060306150a020a050c 89
    0x80c1400059100300b0741f03e14001f454a071880d01c0f80300300d190a0340905406101c0e0000e40e00341000209004200c412124491030007080107000d5900c4186456460300740030304015008282089c17061010466000001c1c082903481e240c07462401f96030f600c4010840d4100f050000880c510501030000f4404d01d40a00d80d0070019480c02081418090341e0340e0003241c00c48803001804a81c94000003602030303400340402c034500700344c0a10100c100095454000e40b5840e860081c0c4480380e1601d034280707884074400d01c10348059030350007000c810319612241c0040d030314165170241e25035104d9004c002c08034050704c45c6d001501b2800100402020701e43c0380d0030300d0f990802e414901007003089003061018000f05540300c1c102c0001c42c6c1c1c008161100580f511400c50806102c0c60300101040c046480c0300140350140011401c0c0304a000d240240700c0d00b401200e5450a80da410b4415900607400700c811000507203400340c01550455401000c12407240800c050041c0c49410550459015820041d002e100344002489440c02c1c1703200864 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 36427190 1250 36425940 36425959
    0x5120c0a080903130504090c0506030c1b03040b030a18020310060f12020a0b07050a05190201020c0306010f0605160209070206012d17010207061a040f0204080a02040c02030f04090b0a05 81
    0x20304080d04d451492103100c2c8950780729100101407003154a90f61001d80009404a5a80e1a0002c0307210016030110700f0107425580401421072072103502000340c8094684c50100d0300d166845040d80000540803540403803001c42c14511011005a0f030404c14417000042e8824089021440c0c800c40b41f4200215510020101440c0c1c4070043c0180d54082210301a03540004034142c0780c4030b05080091500261a4004103680300d0052a000a4820506110a068801d03806c9488508080040c181c561900b1f2049100300801594107028060144d00907002040080d1b0052a0b1800c1c10380000e2450308098800c40f02607005840107010340607401c00a2040351610382e403110504d1a0519501d005103085225041c0074505415681e00d14001c29011900c40b540c01002c14018007140701214030000b00c0e20340c0824032840c0b80c9144d134244600c4900076602101c569801404902000350240000342609040000445c041006545a43c200e060040c0014000d51800061144884010301581240540080d4428540b40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 36428440 1250 36427190 36427207
    0x5070f110c01031e020313060b100206060103050601050c03040b0c0105070507030206040b190905100c0c030c170705070e07030f020405101d06161109010e0406020a05120c0a080903 79
    0x30801541c16080c80c1c00580780b5500304040c11070612810300049014000028400501a1141151758180c080c100402021045104000d4010004207140b8050303006480000c0103903001c0d5000560101c030604210303151070054001e417800d5a00903004004906000308189204140034426075900c02c21900f40149400d0703150720065a1810000e000501071464800080d0620152014071171000d220b1540034007240e622840e145c2e032140048001c0503189071030a200b1043d15441441c00d51211901900c59003000801c80d110124602001c4107112307621041048280001102000702038001e08121880c1e180c80e080a1000809980032540c0f80c0401500510060205a031142403003d0000d000e4240b2003007180b0741d2543c5001400d00308502980c0070a0100c1d400302d06014610f0b908881a205103412807200780c0b00810801124000e004555108100340c00080005489038004e143c02039841c10000e0038480c0181e0008403100b404c603580f104128001c105000c9098002080a81000f1180082d60418089 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 36429690 1250 36428440 36428443
    0x60102060c0d050606040f0b070515011202090a2703020f01090308070804030e030f010204171204050108150d030e030d08280b06030408040e0c07030203091216060305070f11 76
    0x34041a010003d540740b0105205580700c00c101c400034514280f54900ca00d94402d00c180b00741d00848002d4456004d00082c001040d4580413105043e283c1d800314070800307000c1c00d07024010300c02c100070305450350b1079910f9002a44500004400d02d21009000040c101c6211681c6002400e1034080c410240d92a070400c084e2000281c0c1048010390704c11283d141614566032241022a0700c1c040c462403441e094011041441c400c281e041d0005d00c00e0741d41c00391051104c01412a01d40e0380d50b01003245e800e05800c800380020f100641c03048401c3d68002c107078254060303034031359098001904030054102c048010440704065110181814001040c00c03008606003414145410282c001200d85a4400b100c4528030044015404520030317448107a8107000075010340d03202d03e001d2400358501d40c81350003810301483e40030001800c1030fa42c890403941d01d0b0b03605901031070a14500c1418000345004c54181002180503880140c400c0d00f8030b0480d000c2c02003d1a40e030118650404000180c980c0f003000340120100b107030805496141510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 36430940 1250 36429690 36429697
    0x11b03050304030e0609040e0c0a060e1c0c0e09060a0b03030310030b0c0705030309010911060403080909060d2109080c061b0312010f030b01061b12090b07030503040b060102060c 78
    0x10542030540c0d40c031911400117580b030f100381d0750f811ba8040e107801003800c41000002445621000180d8880c0c0700651100019100400406441030b4444807680e08502000408400d040645118241c058000d83c2c543e1940f501d0181c1c100c0c0c2c83c100c1c940c802c6d0200401003071140a0000880e00590145203142001e2641102101c0140005009000c070131012620840991080300c5152b07400400f5a42c0741d0070300803500d0b40600f039540d40990345121416044480b42c5000001c03113040b260300005091514528030240200b0030030050030b090384008045030700070126201788050310f01c5a084003881c0c10404400000905580301d41d41250000b0381c003544600e0b959484060840e0050b0700e100000e0486801040b91403465803041500522900703014800014548914441d2082941e1040c00960346503038a5a2040f03540704003400381c1010010217403400c480802c4a52041241c4070000e0b1070700d401304645840c01d0311200d501180782100001d00020410040c000c0f4a05a9504079209102820b07490034000001441c500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 36432190 1250 36430940 36430943
    0x6090d030807050d0606090302030f150a05060409021e1e01020a080702120d05040801060806070503270106170601050a0303081f0e0709080c01030e1009030306050402030f0402011b03050304 83
    0x14090040b03910540502d00303882030305081d84001d0101d90303200e000c014503035802440124040c1c030880040c0610f4031008294148a19844103500200d6529940164090a00034001c41e4200d569400b001005d42c440701d0b83e80c2024419801e60002201d4082e05010041d241070201c61003164082c1d826a10a0703034042110302c010381e004030f55141c079103950f8000102c0221151541c95014419607000a03000758118024004440c40765000b0008190b6407440c8507101c0c0000c40326180010001c100040c0c070002440b80103440308148a481844020841541c54210b5000b500001088401c03010300da412130a042000c0b501601c01581c1a80d8120300c4e503500070301100380140040c0740c0003140c118080d143c4d58118031094024050008000e1080c280514003600c03010707150043d5030142c010320013502c603154080d000314116200114010500304400060b544001d008030a0118105038403800009030350340d0340e80041d40c001c2c2e0382a05544003074140ba00c009881011012038841000c6050224180400e41180a995115 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 36433440 1250 36432190 36432197
    0x18060409080d05130b09070f030206030415050c040f06020f1e0f0106030b07110114040803100504020403150e0706050301031b090c080a0e150103060f09021e01020c06090d03 76
    0x8000340c58000410300074020a0061030b49820100100800c012044481140c041d01010700d580d00c489000585540c92400b52500f80240454100010305000d0300540d401401586500880d803110f003a0b520036030b80151230200242002007014442c0c0403101d12040002c21960009040b084040c000041e01c80c1803012459040d1002c81800d001c10345010f114068441d81b09034020002d107a1603240034090780c001070300c40c50001402c4004413030300102d0502c034200d170706240056849480c0e6580e07900d6042c2e60f84002c0000e0b400f402282d9002602d501d0781e00207403002e0340c0716029118070351248007282800c55004c1141000c19074048402000600d4002e401c42c1d0550380c02c40245c5154540040041c81420490340c8024a600c0c54015480001a4400c5500d8011ba10b5081c043c0060125144d00b41d6a4142c00c1d4a20300503c04010010400514140e0281c0010130020402251b201000d8000030b1202004170408079064803190f40b5104a5a410b0026003110350044804500380000c2c0000326064040341000103052 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 36434690 1250 36433440 36433451
    0x20a0e060a0306150203030f0604060302011b0501230619060c030309110a12050c060f1812030f04060813170703090512010204050103050c0903060708070e03060a0605010e180604 78
    0x34144603030071070f501501c0107003d404005110b24500079900c0c3e00c01c461032100c0341a4000402c25030314003801440101d0b50141d48031481e110700f1000074500e003000801c1c220350302e40d6034840d841404100382c00c00c5030814001e8108414546400700501201101c1c1d1031802100711a58002400710079004491300010301e816190020300c0c2105894003d03007856a1070b4031700d641f080c0c41c2500000c0c00c11004409180241c0b10340c0a55400021500c1405400c1c0100c9030070380010141401240e105540440c0c0034038a4071401803083c411725070318010507421a030008510012215002805109041d044500c40e03070000d00d182009080c021f26074860202e001ca401102880c03459000500105040c420051280501001080381e078055a1107140c46000707601a10856000c64106000550000104401e492002c907014000d00b00310b03626000c00304ea0103c40148442c0521010100b401c116850811082d80700d84440207000460703c0c1000300140c840d4800030001341c0704055035101c40b103c420611000903082402650081130 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 36435940 1250 36434690 36434707
    0x15030b090303010e0417040b040f05030f1606030f060b19020610080a03030e0c0307060504140d080405040c02030f070b0f010803030603070b1804180b0705030421050903010f0902010e04020a0e06 85
    0x7041e11450b8494100e223a070100b00454820321500e03280c03040f11030440c200d54a00824450b030b1900d0380340710f04803c0342c08100e0180c00c0084500940101862180c0700710300003000c680307400a03183c0d550041d80324010b0070125110101070741c0340c04011840d00728000c42c10347c122107031800d80d00c20b03034410078010010101501c0700d540c07000218003000300c548071001c0202610f0b080ea46030703100105146c1181c032401860362100d02481180d42444030003d076180d6003124800380b600d81072070b051202900d040c3c0103120440c803080101040014001002c1c0ca100c520450203070101d410a04201c411540e81a00915030039002082808030980d0001001d5089030f00c1c080a07103450701b0905400c611041540c40d00d041d0000d08110012448080c1138403c54a140d2007032212250035210344400705c465010440d00101508c425800001001104842e9111000d5561502529061301500031a003074a0710707054010900d030741b181503110440d80c0003410000810b03c25a821800c142803044e004120200844502d070080100049585 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 36437190 1250 36435940 36435983
    0xf0603130305090402160b040501050a1109120c0a0314100608030910020c0a06030e0d080106020d0813080f0903070b090f0405040c03020d0b010806010902070b0105010302090d050115030b090303010e04 88
    0x1403040040100321b45404c011410980a2545c08690440c0d240d440c090000c0c54400061007286003c40c00740511904100c43c0c40306005c620004001c10f44000e11495280301440d550380c2c04020040e6218041c500c3c81e661030030540d0791601090240d00c0c0300440c1001d4090200940000c00d469074040221081d0030150840c4038168188000c40d503809402c11040b42001c565142c0503000340011034003460454200340550882215058001e010344401a04606040790026104086440d002144c0f00751445028400d6659100035502c1010003401050010590030343e68601800400001c0980c885414980744000000408401591150900c61542d4a0204007842121408800a580d02800a15040c105814170350b000303400921030702045100d160000b00d0808680c0c001e540d05542d0219040001d6406c180042d0045e4203c0065142c208100a0781540854004d00900348004042d100c0c000c03042d411410000011301c00201040c400d580104010800c241c1041c02e0f069000c0e03000740501d01410821810103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 36438440 1250 36437190 36437197
    0x605030a1e0e0c1c081209030d090f11030105010501050319020c011802090c040305070b2209020309070f05030604060c020f030a0e09070c0b061909020705010b0f0603130305090402 79
    0x46007014076004500c01c081e080000c41c5512030200f00d481e5090b100d501c1d13040034405242036030014680301c01030003640300050444c0a400d80000408040e2800c19880c2d41214042760308008003681d41c2c1d1184440c2c1300c00c0c072000482c41858890142d0007440070358106000a4014480602a4251088580485c246010380d6078107481c1caa00440c5c00900035000d4203140348200c0e0f076100d10141e200c2c04800300400d144070b9500e001c890441e035004c4082c0240038a00780c5000c10a401001c403090f06642d00008021880e210a40d001c8041c0091442c016128140411010b2a10081b600810640b0794008814000c0341d400040060703000d648201c020459018444080381049080e82c0f404825200205d800100d4980040c6480c403904403e40d10790306503503924902140e660700c1d0200050b113044007460100f01d01d414003505002c030000c0543c004102c0941d6543c01c41c012a8400c1c035048da01d59540760700302c00ba6490309030034913042d1090842d50385086043c41010415540d40302d600c0107062000c00640b49401d9110364054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 36439690 1250 36438440 36438491
    0x1062f0307060f02070b06010203030420220e0601080109020a03170412050d020d0e01080402040b0a05060c07090507030e07060305060d0b011d09030a0f18030501060612060608010605030a 82
    0x1405905083c0c00d58601075000003d0031502c8610b514002a4154400010707a4440da07001856481c8080c0a80c0941803405541c080c1d02e50450501c0d070150b0410f400400004143c000350500005009010740001c1e400c00906802c102c01e0759060400d02d0300940c1d1494039800c01d80782c001010018101605e80c103009036100700e80c04602581200000f42040c090b0200d84100d07150650707000d461220003030840448038200c8000005021a10600104026050541c000c00c00b20382c026140000d130380d455000140e49500915440c1c44035034000b020500c4003210b940a05a04014071303050900c440444904c4907922200740d030184204140e582c00003c3e2050351420041e40365507412030052551561900840d400e4407141c0b201c050503086004000c9010a28000301315030010500d59560169040c909008035402e01d0b42605680b00c1d01d05410740840426420710400c0c0c0240a642c840000d9008840d80b01400c0d10b481e54000b10510441d20b00400400750804120f0380c1c003020046000032801801805600340c0341d103840c0d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 36440940 1250 36439690 36439703
    0x12030405030607120f020f07120c050609010903021207020a0b030a150609260d030c120509010e240105010509030a0512040504060503030702060d02070503070f05030406030501062f0307 81
    0x41c410103540082888904c03130b8552005114581400c0c550005910038805100c001c85410003c5c40041080110790401600d075626140110074181d072a0075180000030340b0160703850303507650300c1450415404120b5884c010392141065402e0000c80d4000960300400c51040164a04000000400000742544403100e01e402001d000103045440e6600180218802d006031010300002e100d40c0c40aa01100c80790001c003114402c000d22029140c00300440c090507400881c242488520203040c052180b03e07008040c4145580d5000059009410b0301540c9030a40e022509204268103001655858010000341810b4440030309182d82d03180641d4000c24540440d20f50701608a004e90001c03040c84905c154000c3c001c480003100c050103850784030020503031030788100c090082d0300000820080c440f07003000744c0203415994010000e80707051418136200c10f485004160340440d01e903000002e00380b2940303070948200390142116141c80f0104003580e52102a06507030078030034008050408a02c8444a100410441b0100c907031104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 36442190 1250 36440940 36440953
    0xd0801030f020d0f05060c0703090501020a2418120e15090114090d0b07020615060702090604150801051f030209070c06021b1c0302030f0711011b02030d0e070b04051203040503 77
    0x1d2202c0b01902300880460004048107000180c1d5880012110f46254010818820fa100f0190800c9110311400821100c1c032a00d9410204a400c40c800b1501103084c0075100e00c090f40c0c0340c4003000030301c0003800303281c1d03280301d10b07d4400c6101d030303150034203040d190343d90020f00f006180e0003922405001c0380d009658440e43e000a58032003003c100403245410320b01070000c030340854840352103000307907024501090400c403504160305100d03030f2000d442c10340b24207500070760040d0002174040c185042540140500b0b8014560580d1034400b8481400d644240081c074803100400d84c56099410b641c00912030450103040c81f020000313010341c40014013606604032111038000b00c100340c412001c5441c1440d2100208444c00b0250311510f05110400381c068001c03240320340c0200000301c51543d180001950f441d80108005078142d0350390b0994125042d42014519082074040d00216160000c5c116003e055541d4107000d400f083d00b0001d402c1004114150a80d41620400c5030b070201034072070b058100761070350103964045640351182c034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 36443440 1250 36442190 36442201
    0x4020f100309020109051507031d0a0e090d08040209010506030618070c02030708030f09060a091206140a1103010515070507060503041502090603010302060d09050115080d0801030f020d0f0506 84
    0x590140b01054802c1c0c8a0001d815031b94820890558540c0c000710181c00d40030804640040c0c450b03c000c1071072903903401c1c2072454480f40b5004580b5490803504013990401000046c040d080a0030051800000c41d2440c004046290641c04075411010600c101d5000344e6000c80896103680e10048e0f00a01006000201c1c1a50f15003c0401400044100c1d0300368001d019041c00400c060304040f0031a49000b5850191619012510040c04815070104a80d9403c022031150007207000808989001e003028000c802c0400d5108000300c80b8843c0d490081c101e0580d03545000006103810500b2001d580c111a0201d81c8413594540c0080454210300c503003c0024241c3c003c990b40030901070307002800355014500a46a5011f01c095524a1108070302c600b42c1242d80c0900c2c00c3c00100700514240c030040200c445003001c04901140c42c1d64800b401c3d60040394a0b00c02c03490382a04140101c1c007081203808071002036803801e0000e552660b22080c426540120019014840405141c018050641030000849910108a07442e40c9441d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 36444690 1250 36443440 36443447
    0x30d09081b060a0b030318010e0607050706050a0e0301020a2a020d0c060f050c070e1815061201110d020702120a060209090f011d090c0301022b05040b0103060504020f10 74
    0xc507400d280644c5030014014440c10b00009981111480c034542e0795441c14001e00554000e00605804c40c0d2000c1c040040c0c000007042401548010001130b05d5154441104490140c201c4400e024424020713841405086034042d88042030f0400400d0603505440c40f10b26a88584001840c00100a900003141d450f03803e04200001c075641c801c07181d40340d503451a90505000c0440e018460351a031000c0543c0840340901000c180c0c110000d82080c070b1080700760300c00c400101c05c0c2828040929008017a2030250402c100807810300500342ca21132240c3c2002000745507103d50a140031402100480d03d0a13941c0403d0800440d1203404210038042c1087c4100c0d0704d06010b0f890b01030040e500c00c000003401174041c82d011500c80c920000015041e41d940d40c0311000394015100026580c0039000745103042d2449034000c1002191400e1008120b040180303442d0006910501040c100d107078144208062080d45850b0402010403840407103641565807098000c0340548807400010025046c070500594002e18110450540940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 36445940 1250 36444690 36444703
    0x103020c0f03040905010905090303010e070c0b01030506040b070206220614090a03170c031315150306110a080606070c050a12060f090809040b0103061520030309030d09081b 76
    0x2a013402070050707a0300d0318500310a072082a200142940d0050005004120520704880d0344a28280391004105209454403483c0460a0b8401c1c1c0e81c41c0c004400f40300a00c807403540200c1d4062050f000411080c1030920504480c9101510b00c20303514000c142100040280a41105c01c0c0f4400c42d0900a006040900845c1d03112000220100c001c04c4600000891001c0311203d5688100c0521804506503035070940e01508014600508668612a07260309000c1840f2074400c504040c034038114141e080f00d05510b48503040300c1c0415440400b44409001010665a000c00c043c0c1c0d1240082c3ca126458030044c0c5040b40a40c25983c0081d9486a050fa00110700200060341000b040d80c000c0c2010700c4010b031a402280115a003030640a00010020041a041400c064008c0c241d80d200603d00003401642c0e444000360002c03280c02515000504410840d0020306c0c02c061030103079440125010b1403650525003103a81da42d1080c0209600c94070b13203600b0b00f40306109a440070398120f23410440c0d00104002d80c806115440d02c1c17 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 36447190 1250 36445940 36445949
    0x9030105091513020604060804080712080603011404050604020d020102070806010902090103110c06071404030b1501080106140a140f07030201090302070807050603040204020904020915040503010c050a05030a05060103020c0f0304 100
    0x1803548001a54405103120003c02c107a0081c0400e403500342000002c07100400e000f8030945105508011020009825903148a942070b5182c2d55590710341004020982520403004000648070301820901c008100701003111504154100c0701588400355620041c0d041243c0c0b41c1c41040d060007108000900b50066400915401109a904205140740c403440c03070010f4010401640c280d0361168000901d03d601406e01e440c00e00c0c08110304181029620f41d588583c40b102128000400c0c204200c2c0c0240c0c5503003004d240ca01404941c00c00d05c4142c40c80001451450103545496820005c0c2c025143da2841868004c03582c0400c075514011303644a1203410003038007030950164100d0061088103c0061403020100b041d40c26140020141d615588032502000069000ba008080c1d21039400c205450305603840017030f15107208100c40e50380c3e61154500004c250864085a20a20034008200910ba81c00b0f54841c0849034805080740340064032b038903843c004800038040c07140031030b00d04e00c070303070300b001c0000030000006003081b1f8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 36448440 1250 36447190 36447223
    0x7051606210203070e1002070b0a120f020918060103090606031b0801050601020304031403210a0c0203070f0803040c05130e01050a06060903030804030e0a090c3e030903010509 77
    0x90760340a40d150403440111944400100302c1d11070007140c0e1401c3d24465019522910459410b5a2214200586035010400c000c0100700c8490b00e41c43c008a950007044480100040210f08051166020511158404060310160303103a502c0015001ea000354800e10203181c01c40020000b41c1d81b249041344540002c190510000924030b1000079440d40140900c13481042c041e03001c0d50429107180d4450702c208028950300f01085c0428081d50403040301c0c800a00450400d591032900d0941400003101d000c40e83c00005400454008018103c04180000400c0d103819920501d582c2c0c0c4ca070345506280c49008000c0c0c000d9544640d007002c0031801d0442ca0781100e103007009071100800480c0c03103030711140b41111250f200d540d005c10041d14041011a000340b0846034400d0080c03c108505900310b600142000006070400f07480190341e50130003002036510030762094040c0710004092552070b480540000031314141d80c1a140e064240a421144c03c0c040510980341d813044060b0081c00347d82407400030780d51154421043c400f01c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 36449690 1250 36448440 36448487
    0x70f03050c011802030706180911130801050402010806011b1a0702070602071d07120606020a151505150c06041a13080a0e01030618090303050c071707051606 69
    0x1400c0180400d03e580e008005000701c034600b0000340c0b140d47c2e069035240031b80c1084c5000050407084a000b5002110031900c415070341e400e03481090300c00c103028580240720700340e251104000042c5d030801001d0f6044074090914002000004134000240035455200034000d0100140701c1c07217800912a02c1e00d00403007141d0240d903842c98448400b01c4e6544120301c554090114200e070400b41d140494000243c10110624040305081d030303102d55007030a952441d8020001a4072131a14101409410340c07105070300e516582421b00407150a01a0040030141d6401030034410160f500310880c20101d04021035100c2511001916803928250400b5155007040c001000c84540b000800101c02c0000000d507010800e500006170f81c28018413580454121902c042141e041c140c2c0c403240424211880041034000c21f4885c3e001103031048241c5001410b0319806003000d040c110701031065100107100710402390740140101c0d01c1030361075541d2818034901e0000302225568078608600401b0079074a40c0940201c1d0600b5180c15940e40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 36450940 1250 36449690 36449711
    0x80d09030c0b0901090506070203010b090c09190e070f0201062601140403050304120e09042411070605060f040501080304060305010b132114010b09060d08030403050708070f03050c01 80
    0x42c140b180c507154a00241541c1c1041c8000d1a01c0703005000054000707000020040c05074000300d088510142d82d011000038001c5034044991400c0840e2003100f82c035040041003040d24000900182c0c8001500210a02404082c0c040310103100f54407280041201303860084005000c0e040d0088000c0c50021404019401d200e81d0452040a2003120340c01aa03055681da49580d8030760f221895071080d4800d0300420040c41400c4c2d40e81658900307141c51700890152269441c103d009000301c0703150405480444042c40d007807000c000b072810604019609040e41050020901783d88120004851400000003e43d1252802d0004980c0d100c00001420641d5030303540302007200b66250b160174155401000f00c124414851142c060000c1d0492400c0080c03110180d4050804540c150794032103601c1c031000d108a100680d5501034821452604a0586400020660328400800c01644903a4a103210003840602485000034400381000f000328225140c80c0e812030f021804002203441c0042c82540041e4003490f540d820800c0212 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 36452190 1250 36450940 36450959
    0x70e012a0c09140408070c030501050c0a031401060203030117010e01021b0601090603020d020d0503070204091407060801080703080903030f180a0905240103181a011509060507020a080d09030c 84
    0x801d5640001c10001280d904c41e5036402c02984500c80456042001240000c005402401624000c44103140102c0e01d0b0100a60010101c4220001c20f0801c415901c0c0100005500401280d0669030b142d26100d403180722071f03980300b4054401100c01d5026980b002032515662101000d806039081c4003d800c2d6101e90766540b24070400d8440300d000283d0f1210040560784014941003003103400d081d11510503030b41028900d0b00003400300d4044d06401d81e54114402607e80e2501010700500307001d00041c1c00c20078400c1d410410442e035903200c0b50000030543e01d0005100420307940c00300152080100e40f5140d20fa500c0c54000510705c0e20340030001e0014000d03151140041590415801114414810104885940120802982100d015698900d81895610103c1d000b82048030700c60200b110b40545c40d0b00480207044040c440700044143d2295146001c2ca1540201140d4010b03001c80441e155407400e66200c5040b03000052000300c075640305c01c41c01d00c1111038006103907070480b0581b41140c3c010300c5890328080da101081d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 36453440 1250 36452190 36452201
    0x60f020c010323180106150e0603090106030507030303060801110a0e010f120603051b01050309100903090b120a150b040e0c07020d0b18010c08070e012a0c09 69
    0x15800c4030380d81000651103940042d02c588988501002c140f0102c81a40300c450001380c40703001e210b04011404ca10300d01400d014003802001520000c40c00700c002800c00030310b04403011400a00c204800000720321059402d402c40c101464210003a0b0b18071301d542c0d25016000b89031a00c00c50a9135400c00c0900344600e2440001c1d9580e01916855000094007203030011910021482400400d2000702c05003031110805a10a0750051071050008015000100c5100d2174000000c04295040140400410050f18004030b80e5800083d10250003142e5025140380c01e9480201c00e803c40301514102145400f11203000c0e20201e80100f43d6030004001e0f21206440001c0b2a0046026800520000b04030400c803903c0080d0b84035910100000078941004890390004500400c8100141c80d088a1032003402070f110002c80340302030451404002000308107007001000d03207200001485107044c0722a000120840d42d010302d0342c414001c001d0f03000074000d040f22424000d60210b0080801d4030711a4403400c0210b03e188541c07240303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 36454690 1250 36453440 36453467
    0x3090d030c17040615060507032a02090705070209070804030806030d05030c091c080901080a0509060601080403021006060305150301050108030d020c0703080c0304030204050a0902090a020906121303080106 90
    0x980000340c0020751003040c0000064002c41c0e2071a07651080f0700b42e00509184075805091b5a6031666558091401e0041191440c00c3d44600c03100180320211541c0c0d821000e82c3c917150b2f54103035224483d13540d60740426150380c00ba01d40c0c041c0d0400c6110003088a4254420036240c8200e00c65140c2000a072a0b580616940784110340071100861400c10114540070b8a500183c015644020120840c5040368003104401c885d0f6100d04030f807500c0022813082101d682102074168400000c01040100e85449c4080315902c15000e0000b03414001441c000c982454800d00807081d40610804081c03102e507aaa41000f0000c0800b01c410820541032060396094030b1406000d03980c100c40424000390306025886100000a40c010a81e007000b5214050300080010048006000c2c2028520091501d80b45503006010958000030400030340b140c9400d04100040e038807881c1c3c0c00c0d00240c0f040f80058440181e034002c9000c51080c1c2d2160400c11131038404125000110308890064a8869a41c0c42d4086e682e4203400e0383c08004c1101c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 36455940 1250 36454690 36454697
    0x30702060a05060f0d0501050106081609091e05190606030b010206041b05100801090f06150f05160507030203010c020309180423010c021509030a0318021503090d030c 73
    0x1c5901c074203403500300c00e0300554010300d4000140348800000e050050089000c8502d40d444000402600d80c200368140e60152101e010000820220040203144405074000ca0f111996543d81240d45044a4440170000113008101080603080417913850a4032204418028012802c2c00300c08146c680c420b015041b003401040c2c0003400e05071656503c0c4c640c42003041c020f485000d002e0284c00101580c0346650359542c02c0c00360720364540fa54144004030040d0341c249208004c00504000e0104440c03290381da58520030a03814a840e11428102c42012a00c91241000170320f00c0100c10441c1030180f00022412104030ba00c00c070003c010212131010166203074080d0341819a4408044031803100100d00000c0180e0b406417203041e154114801011180c80d40e9141c001006060360340d00c203204a41c0940400c164040ca00c5100313140c18042c0b6081460560700d111f81c000c1c60041645465070115900030007400d60318140d074010030720000385003081300410302a001281d030700342144160f030040107115010744540000700c40d044c2d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 36457190 1250 36455940 36455953
    0xa0b04060e060c0a080a08010e01060c0c03080a020106052d1c02060a050c07061e0207030c05060702150304080a140307021c0c05011b140c070519030b0403090509010b030702 76
    0x40c204991a00f28140000a07409060710300380000c1c0c082002051010082d0715441069414015182c080f2035058000d4002d209043c5801d1001c1042400340d1400c4a84c00301415542e09846c0c0740482c090800c03940401d0b00402c1c002c00d440016a29041c4e801c2c100104405030745881d070840001c03c0558092607003801403a41e482c1051102604050004102c46101400c02a1400b0721b05014149054102d900440000f418090441c40840c8040ca1341c10111100348010030403541951079901c042ca0140c803c0d5449848002440001c64881149414071504460365294a80c40d1906241900741c0c000502c0000080d5a02215000d0f00e00c0302003580d000d00e400754000c0c50144c00011060745c078050820000b00038440111480400107209002e5520350b00407a00c40d540c40101c0410028020070403040c10b0380d11703041050201881c20b16000450b03074112101161184c064002c40302ca030b072030b00144070303000500280d10500410088c11341081e00d45040303c0302a01c81507075580c3d0741c07907050322140001c1d11400e005030080d1b0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 36458440 1250 36457190 36457217
    0x40804090e0a0b010e010611010b18090f071403010c021603030f0c020303031006110312040209040303060803040f0513021204030c020307090e01090510180605100902040b07020a0b0406 81
    0x181c0c40108258081400c88500700d50680300c401610b00d090384240b00724101440103004040d40a0054142d400400000f88940c4540f600000c08040780701600d10701d00c00b40b0500003071032070340b04024440d0300003244816500e010707481c0d003154000380300340d203100d103010b503081c0704080344134a20004003070004414001110184509540c0d040380c170f8028105201041000b51400c42c1c016130b805000443c05285c1210810400324501b100c0a890352807036000c1d50390103400900c940700c21014280800740d070142d4119003c0c1c040c1d55413407509800a02c107d07040350480d448081008140322028052070410b8840881d0150380da4035aa038070324401d0344034811701c0e254540002e4012400190090000e220402e20050503260201d40310004c200899580042004550391a080901e0501c6018843c0c80401a1030250900c100e0341c04a011600107690900e0040001d5610000641050000c040c09405411030380010b40d0ba95a94031210852908140000c1c2d20580701400d00007441d0b00290210703012a65242c80e490306201c0c0d40e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 36459690 1250 36458440 36458459
    0x90b01170c030a0213060f09090b030d03051801090f031205010b041e09020a0f1b0506060112021204080c060702070812090103020405031212010b09090f040201020a0b0702010e0c010305040804 84
    0xc3c1c4140031580d02400881c4440d40074078094406401c40d036440c20a8000040d100500074001584403651940c0f402280581a40300030504060720100350502203540c0e00c03002c004001054280c41c812049500e0010782c20200102800460b110310b000c0e50710000d4a064202c050411a817081c4940007000c00200020401d174103000e00c14203410b42003001c91405507503032500c0c0c01301680d02c248070240c00264100d126840031900139070f507a0389011114010300c03d031071801d90b1203036600c9501404441c14044c020441d594044420b80403903141030010021800182031500c0d01c0d4080e504451840051790080d030000800c1544000f541e90219140360004160240320581040701652102c0761040c1016001c0101043c0d64808001006045e11001017940e603613401c1980381911840181c000c1d01d00e903401040102d85d10742c5c421031101d801903d004842e00090701c651006070f1078250702000043c01d02c01c0400410140c0c03030701035008010201c0341809894a8001d000011070803514125402441e0110074001400322851 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 36460940 1250 36459690 36459697
    0x302101b14150103150c02030c0303040303050606040b0a050a080708090c0105090a0801020301180606051806030a0e150601081f290c030711010305012103090902070606090b01170c 79
    0x250700c00e4840304425203000008020302600203444140b08403402100342000c0d845075265100d03641c4042c5041c40c800d058100d031a0700c4003800240c10992160041071250380c5002c11100100300e1410781c02d60325001128050318503000811004081480c0200040d00640507800c80c0d03116036401c3c2c014284610808006450716040229941d400990306032020400300b0091001794040c040007080003640040c541943c07400d513407050300581d08114080c040e42c1080c03070890546c8004207100701c4e003040e100d42d10456581c0007000584d844020313501c0f40d06403441c40c00c0e02208000d8052a0281d94500e01e581d2041003130005015022011840f4003004801003004d0f07220003806414014042640210780785820400d9500c80d00714881c00c100d0794100142e03190130000c4881c1c1200c182c550a00302400158507220720b04425094420544039400381d58180d80d420180300d04c20711000360100ca80304540b1482c4034100b020041c0120b0080076022407402032040d081c0c1d0300078400c0c45210600d0740d01c10030003581c940c455912030b0742 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 36462190 1250 36460940 36460973
    0x30703050c0c0f07180c0203030112062d0501090203060d020d050102040e0f0a1a0f120a05100603050601050a0b0304021002280303050f011a0a050409090605010302101b 74
    0x10001e01c40b21810035424001080c90004400081c12034a04040c0b00500080c8080300c08880d09292281808850781c010040d681110901414403075504610b04268000d0180c50f40c04801e620000964060005042c103040c11281e555040c081019a0300ea0074880e0880c030090704c141c3c1d8007041c0208031000502d44400780d2f004a0340b0550025050940d501081420f0460640b400503a80c900c11040003182c68951181601840c900c0d010b001c0c0304844200840c3e541d00c3c2010f41140110303101c51048000c0e0b20108075111030240e201d4200c0300142e1a1100d1076008114a020440c0c00c3d001d1000001400c2c94004640c03000c0c0c928042096145840d65405c00c1070104603101d04005500543c0740e00025000300b005400c40390130180007200c41c03070b40062030000d089850041074003080340c04985c010301803800001d22103610350751030b0b00206a4801c603410302a212405660300404c2d42600385500c1c1c004110007174000a04886c0709540902c01d0040340542504c41212604903400e03110b00d20041e050225003401d2a842070305 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 36463440 1250 36462190 36462211
    0xa06050301141f020604022806050703020f0d0f020f060c09010302070213020f12180a080c0c03010e030a03060501020a1e08070f120801080309090103060515031b090106031103070305 80
    0x40d44000b10001e1243c50f0604000c0540c005804201c154244001e040301030b0345000b0300a1501409505109107481c010740030790400c0081c08a20281007500030441d1500e5119800100c5180385d6103605d006184031851401e000060051b4245110440350004074075000b00740c010704182c205102d2400441c002d400c41001a680502c2d00130b22066120038910042084071103030400c0f40e60340e00c880c1e480d881300c00c03030b015003105510044c1881006a40c10b0220b0640c140b10343c80054a56030b01e107226001441c105074111192344c9541781108251312000000f0040c22001004d072014081965140d0040e0b0300d82c107050b0380283c0b5401011045510114242100c007002c10701c105001400c00d04c5c0b07078564000e909010081201d0045903a100c10b640c503a00228064014205180114908111100803804000c2e06201c000d040517256008201c55000031803800c0301e405009011138200020002c10005006090b480240c01601901c0001c80d8041c400d0081800c060b107142c00c190300c3c41e21020002c80003400c1c01003602094 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 36464690 1250 36463440 36463459
    0x102070315140f06030a15021b060108100b0303030705090112020a0305040c090b060702040f09120525020105071202120f0405090906090d0f0207050303030708150a0605030114 77
    0x91903031140c1000300901d040c0001115091007a50200c081006000d00b90f04511600421550340e6000130049880c40c0d00240c3e80b407050803001034200281c002d11140310804d180c0741c2481a2190400100f440c102c032201c00450720b080348808400c10880c0e800b100d002d50140c10070000603d1045c0a1802054a410185072802e0701c00c0700e007800c2808981040c00d2102c0065240e0040c0000d00042c003a80c100544101207042140108100002d0074610608400074040e40c3c89a000c011181c000394051550203402c00b03041c41044141403802000c5a00581681d00b2a4407410070f151400110280000c4559906840d49480d040c10b0b911290a151180000c0c8421032040c000d80003100202000586401040590304980341e60800b000c01092610040010a8591007082003140024000030708054840382402c0035160028290b8003241040c0c4182c01c45501403100100380464264402c03803007403060341424000080c90313046c1401c20101c1401480341c2c41c0018418001840401c100c0903100d00480e00081440b40d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 36465940 1250 36464690 36464693
    0x103020a062007060903030e01090f0612090503030f0610080c0307030207080d0c03150e0408090625030206040308130308070e030c040e01020408010b0a150e010302160507150302040609050d0201020703 88
    0x6400f405400ca034001641c610002c03c1010b4124504003807144003420042c034402e0a010b05000e80035a00e105402c2001180004158041031a5000140b1180c00130300f074039601d14000c800c0c03020490068424034010a45c8841d000796051180d000300c0e000759000e52071580f079034540d0035080340030303400408013907440c80300030810749403605c601c0d02c02c90150110545001c9294401e40d00642c4002501d9800b002060b0603040070440014484012642002400c0381c1443e101c6c80c240e41d000c0c0400c0301c185541268003400ba42e40b00d080c1500000e04a2280f071082d500d00e941c41da503074030b09880103508151300100481c21240110340c14034052000c82480b0040a802c560403440501c0010f000c0d180c3c1064440340741d035800641840b2032032081c010107006984c1903501c040c88924004032543da00c146140340070b04100e4540070740c10700380c0c1c0700b40c0444410803038810b050300681c1c1003800e185403506254407840c00d00d12010388104c8800b9004c0d00a81d401c13140540c5810182d14980024800c11042001c070890460240010210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 36467190 1250 36465940 36465943
    0x3030518040c110d020d0905100c0506010308030603100b030d08040501150308030405060705040302060f090d0b04060b010905040c09120c03051204080f0102120106030f0605120a050105060402030103020a0620 91
    0x122140241c2c0d450b0601858036080013400d10a0040012045412410045d0051508002e500f812680d041d20900c0c060401258111070980b150391000307155006001c000002e001000007d03602844080b01580c4d01c0a4004080408440300892500d80540040c80025429805401d01a610601400c008030b6840f80380f041d8140e44500d03a80049918050200510041c04000c1114070b501c1903407400c0480c074140c21600041d040303006205444140100004120016482e07045840c0c062950100e040421070401d450960042c15141803500e001890400c40018285002c3c01103188006107520340c034901c1400d061001e004404602da05440741d00c1e0344080000060307001c1001411002e0b103004165111030611010900f4641986a103a000c0c0e0300500c40148401b16800b00304c0d04490fa141800942c0c0030b1840045800703041103903c000d070b10503124483c09081410200c2c001a49a1107040200b2a175540c038001c10049007c03e02002c0c1d080300c4411414054507018140800712413200120ba0000290000d040300e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 36468440 1250 36467190 36467201
    0x1030b0d0212030a02070911091e040f14100501090b07050109080c030901080c04030804090c020f01110415080108060f0c0d020304061b030207030f051303080301031226010303051804 80
    0x40c401a0320000c4e04524031541441400050051400144400e00b0312101038085400f038614882e100d814510000100003401c41d40c4030300400e10141c4144441d445032919000246031000c0580d011180c0080007840c4803080100f11002e03241c058460000e2a03092151010b401e07045410229165903880cbc240d000401e1802c0064807015107000d0045644050720800108a120042e0403139882d40740501090000500107400c0c0d4040c0ca445490004840704001d00032032030320810485140f01c41d4a08201c2c29002d126890040040d208600420f50300c09420b80800c0b2091542489003400c1c9400c1700000c6200480c00400072038100307040003081424005841100c0d0104d1b0701c287c0b0206d50300c554130701e00032054a11b0b0040008072801d007030404605082c4240c41c00703030004401d10345030800c00c14000b40c1e00d41300c0c400c80b100f10400303590000305070f0745c4960f1a45010918040c0030b800542c0841d4042540010240e0703517a00c0010401c0c07040320315a049901e07683d000d8640d80c008500c1c06550121039500d80000b601c0d01d1240c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 36469690 1250 36468440 36468469
    0x7060905070e040b040201030203060a03120c0c06091a09210105010801110315120708101d010207050a03030510051f0305070806010207050d0212010507110c09041101030b0d02 77
    0x6000009141081c0303000010340c400c80402900700c0401011611402c2c200340d010382c080c02e001d40e89940d900001064030907290030050030050f01404104403694008a0800401d100b4410f40101a031100c4096440c0c01e03451045000b416284a01028000c40301c030007500c007251025100e0030410660302c074484c82c2c00360440108078040c2e540d800104640c03c824025104a51910031140b480c5051046000c2c5100d105c2e011900c0c0518000307032812a460300c0c10402d4038020221030040da4454060070800d00d019082d00c511210ba100c3c000d0310304e001d85403010320865500580c048000e1020000640e01540500002800740c1c020b4103841100045607150b054004002c85040005410f0702ca41c9640042c0c120340014200008210118003044241d0360009140c0f4240d51007103443c3d4103202083d20016690a00380d400c050940d50900090207113140d040240c4c80032049844054034580201c82e03041c0003c00c407003141d0141240700200d00050b9a940660b200c100d004078050580d002d105003540110300b100402c91507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 36470940 1250 36469690 36469703
    0x6102708100f050601050f1b1f05010b04060203040e15040c05070318030b180a080a02070602060705070308070c0510060b180306010509060418050f03040612050603060103060f060b07 80
    0x7072046040d4051044200e06000e0980411040c286280000d18038040d03650086500080000d04003e1115140100303400c8209820480f048004540145d1110440c0c0450218003076007000c0022800798800f00a0300e09591007a4015801d040c60860364007074441d001791544084201c603030381c01080c40d20389014005080100f6201c055448070702d890000c050356a40d40c100140b8180c10030081c00050003444805030841108804041c014407840d03155424994446001444800300003100411580c0110b4840c089034065020365000c2d40e51818192041e10825000600041c50480050380f8180980050103240e4010000c441c01c3c010008055801c40368550020780c006034022414040100b07100c403051341010004d40281410354540404136500d000081c217894802c03a00d0b00e20411140a62412004080341c0040446030022401e5024030748a80c0180075074400180c0710036004042c0300c01400b0300750240401500034a042d13861912008010041c0300320a417116521500006021107070a0b0151044d14040d64 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 36472190 1250 36470940 36470953
    0x803040b040b060d150506010210060311010e0108040b040b07050910081f06080c070f0209010906050102010f0c0f0f0210020d05100e07051b030d0603050a05010506040506102708 78
    0xa02800401e4000c0210b031107402c0d130440b0f680001c1d039110741806601070150b42c045503d417586401071b420270300500b040117004c83c900750b40001444a05401074800704000c3c0c8400e00742d8500b0200455003104215000351900800a020800017400d015110358000401d2600c4c0e8106440e10001840c150100d072090800104500d082c840ca44021006100364201d189000344004c03460248050321011004280240200000c60700d00280912034a014100c141d005100c0b00f95507840301648401080300d03003d9140190300c0d042c1c12100800340c5209949030400261166041e441c4901022541c1201d00150038003140651411503c0e108410700180610b2010303503201090390314007082e0420507021a988440f0105040c03009101940790803600f01c03410503034002c0542c1103552a5030300340d0b4a10311442140d8507206d46484400424080041041040d151151000f4070181d140c650030001a1007040d1802607106841c64051022107015108032000d08040041c0e00003480e0f0407030020120007100340c2c4441001d4000d103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 36473440 1250 36472190 36472193
    0x901020c150a02070f05031015090219020d03060e0f0601020c10030e06060a1d1513050604050603010902030d0c0311060106080108060c0a05040b09040213090e0f0303150402090d0803040b04 83
    0x40c01004c2c082c044240709111541e00d01070020396101d200c0b45004000903940c2180190740484003003850054220458155504c0811900c414542000b50f940c4d400180104d82036480c0d850300c00e014680c200c48180d590754400da20341501c03208909002130540c50562041e60f1072807102c2d403124080d6003a9041251030005805184a218a042c0040200707014850198010280305410011680300281c121041c600380c0740d0383e6502c0c040f4142c041c6040700b80d07074002016203124182d00f4003a04520310850b82035400740029103d80c014103080e100c607400c0c0203600da00110080b0192912548400314410300901d405e4031070b9000c00b035416003048404c0c1c0128000481e208010300281c10300704249600304040041181c64110b0007503004005000342c0c0614000301d40b0000b80c0c90400c1d038890b0103503407a05150004180c0041e41c1d440c0c40704014804e0b000b6801032405591100419503401000b0340384589000c8080400c0b500b4550108002548810155540f1003040002c2d20041103660002c2c41c0316520904070b412103410035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 36474690 1250 36473440 36473443
    0x2131415090a09050402030f0a210c030e1306050a08010506010206130515040f080a0f030606020f03030604090501020c150402010306090501030203030702040905030417010b1801050a03080901020c150a02 89
    0x30220380301441a420011062161501500b880c1201c407031440000e4580c40c1c42c4002414040500d01440c028450905902d090080c0104550480e01c0d50030700081458000580c103440d200c1071140050045501c0b20107100b85410004242d1418042c0040009025600c07400012000e85460300019034a80d51007042108958040104507000030000c0384403503084950b139a4441e1765100800c540e00c030701150080413404100703a101842c0c880642c000f402d19102c0c40780203001482520000760300400607052000000300700b80003060f49058050303103030041c600e1a0340380d0041c0800b51020003800ca682c0c1d07508203c1d400800d5400d03c030525051100c44d203526200c1c2058000107003918403640000022078a42801040103035070000403a40c050364180d9010039a90980d04055055004540c0185100840c823480c1c0008034606500c0161300003421101105005200756000001c01403d0140b00d030061551a024000b28a0544c041c000a80051049915106107440030800010401940b240040e00224218050307680 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 36475940 1250 36474690 36474709
    0x90204080622020904240912180f050111120a09031403190f0210060b0706051506030117010f0207230a03050d0213031407030507060201060303050a03050604021314 72
    0xc9030404540c03100302c0343e00064482540a0002884040e0107900000d840c00250103902003655220300400090b02c560034101c4031111405000c400048142e41c051700407920f1b409980050b1b81042d03200f05911800c000065541410000d0030000611511f450501d800d190716004143e500499039540380030b00e2541c580f614990303206c45516200ba0700288036500186070301d0036a00b0b07c50603e514040440c1c021480301641000e0310740c00009030740c0e82010b90220706103071820000e08a0521030007040025a6420b403164485860080030a6403201c0108010050500c240c038203101c1c0e1822100001640d0700d201d0100b0001c80c1d100c0c0a00329003400d401c0d105203200001036202d02c0950400c140150203084078542d0020454820f60050700d440c2c0750f010601558a10441c91890003465216022110f51020480711b50750b205c0e8036200c02c4503248954840425000d1040c01500100c81e0305072600b5040c056004403c0d03004c3c1000034052034005038240034000700350b40b01e03526600c020940f8188440200c1c40502c144000e409 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 36477190 1250 36475940 36475981
    0x90604080c15041406070201030905300301080705090903120a1b080f0a0509010b040204080a0c051206070c03030e03030703060302040c21090204060b03040602040f0614180303040902040806 83
    0x2c1e0038401040ba0000084800390001021240507669165910050b8018072410201519a00c0f406030300c2e080c1c500d0b044141640c1000e03460400c088400c074035086210244400d00400c0b241d604072030410001e0b41000961039400c1404541520704002c1100c144550075a42221145407860315610599144070501489078016012351605500c00e1621101c1c4045070040a41210341e4503513114001218105d00390703c034201601b401007003550340e9907440d64001c0c1c1d90024040c0983d60680c900e5400a000c0c07600c200e09490742e2304110f02400344c0d5034441030282c81c1c2c00c0d083c0c9000c0e4241038880448000100c000c1c8015480340c80c840d180026020b0441c010710040b1000c0c41070b01004e00546250200c01c64984104c03a50f90441304079400704980f8042d10100f4040c0c01d15500969141d01e010090200300040d5030086d106941c3c0744680c2070302003650340385c0454494036101c1c9103160281b0208152011183c00703401c18102500c019007128502592440b80394103e82c0541c0c03000701709411607802d204080412100c01140c83d07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 36478440 1250 36477190 36477229
    0xa020907082202010509060c061f0807090b0d06061508070905030307140a0503030705121605070209130210020307030e040e1504030309060515040e06040305090d020105090604080c 79
    0x107140900b502803000d0704008000d030a460011140b0011684201c081360f01012001e0703e16900e90101604990713880d101a81c20502d2120f1101800004001c00e42091080320035210042c603881c2d140000450003030524031420f0340c005412141240c0892218040c6000508540040382103100c49804014000f001c050214800c00c000c0403401c001356a07002060752021500164000c102240c402c180a1030010800d034024140c0c0004000c105020390001c001d4180307012040070300c03d02903444031a0300072001020766400b8085a01400700501504242d100d056019030742c0d004851003101c0b01e0700001d0080b4800f010150059000207264000c160344850019048003090300d040c489420506582c03612440c3d00720100e00e403081e0360800030701410b11940040110940001e801c00090905d50402d145e180721403462a80290305141e05d0242c407000000725140f05a0701651141e003080c50030b200700013841e501c541d8160b04000b01840101126601c242c000c01c000d10701c00c0001c04030000342e1760074040030000041186030035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 36479690 1250 36478440 36478457
    0x60103090201020d0e03011e0507020d0503010e0109051302030703080a02010e010b09010b0703050d0c0f08090a030e150903100207060e030301080601030303050c04030602070b0132060c010212090a020907 89
    0x180d0f00041c05055003802810100400102c42000c2801416024504640107a05185683e00c1d11020b911241c01104182d00b9030301d01d05141c40c001c0d80d91348400c0c0f1415a43c45110b0004109001e11981300582041c05005502d03410015078000903d0140c00d40c209842074580081d400301115024440d40e40c484400030300a00000d041c5200003000140140316410b0b801e0b4000800c0010140704104031800345100c0b00d410400c800d4003800c0104041c41d04181480030515507004100000000500151010360590b1071807244800581402241b90903a0186064000700740b003024415507084c4008501511505401a100c072050700305041501d07000340c84025203401c10001449040130115002c0d05603901802e0200c0e20f0b443c0c0c11031954a80c8180e900152080d44081914030402c9008900f247c12500e040f0304485006e040640038074070485241c2e03400340500702c1c0e100003030b0454146039015008004500c3c0c00103040900c0040c122408100c11600c80105400642c590f0307045252030203199400868501c3e11010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 36480940 1250 36479690 36479693
    0xf040603020d02040b010309020a12020103050a0b030c040f06152a03050d181401050901060801050c070311071707150509011713140d1202130e130c031a06010309 71
    0x1d900c400b04010b4041d03a100c0b0300d080307540d90094102101e583d502030714400b00703245d440d500180302d000c1c5141e04a000a0402020038107440207402a0302d44d00b18000c0240019041140c104030013000480300500c0d5064441c80001045040510300709040b03429625160069005240041d040003c0f105510265684000d00c84020a6101069604181c2941c00c001240d010043c000010800c2c0010b00038800780c41d41202d080f4000d03041d0807082c0103003d008028008581c681d154603091f110111a4103c00d21014029040070912071581c0c42d440148040540340702984030020400c1c409400800c0d4540d50380070034001c100c0b410210401156200c0d00345009814840721600003000320504501c1c502c0890b1305040804c0982c40c00700603041107258484040c5103101285544c20f6140d02d060007a40c80410094500f441d40b40046000f00c40c104411540728052003420702c454044014009406220482e00c40300040001030000542880958000c000b4124070a003c151748415130040101501d0401d41850807040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 36482190 1250 36480940 36480949
    0x9020a0f050f07050307060912030b01080a09170c010b09100501080c07240f11120103030f11010c0e0418050a0b1302130615110d120209030d09050f04060302 69
    0x103a80440d01e2030055641c9210b030a08441501558030058840c0c00300042d01720800c95668444100a44604201d04540b4200c140c1a0f0840303410312002800300d8107440002d04001c500d5440a0f06a91003034402c0100c011b00311500c0e0189411001000107169076904c0ba0102a00e001484030380d0020880e4461030b0950306140008052200151496600324008900002001100441841d0380d04560024601550144000c4809403004c0b00f1340180031403030944d008000b41d40c01e50440703004101a20742c02c8110307442d41d5801c6841c0058000d48000300300030030380058221103003809800411601540c901c0800580c140400045440c180d10000a0140b00c1c02c10b0b030300080d404140c40c0501038100301c51502c0e41d920941804000008054000d61213813a0015081100015a00410545465180144405001030420f6030217072407070b81c0c001c1030a034003075501180e049100301e50341c055201c0c85d1b85016060030b400c00d0201e46480c1d15000c011000c204205014000c0c0d04042007240c42c050011603041c482240303582c0104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 36483440 1250 36482190 36482207
    0x30a050a0509010905040203040606030209060a03110d020a1a130e090d0c080f07140601080109030c240204030503030702010b04020f1e04031e11090103031b020301110f070201020709020a 82
    0x1805110300032840d40016801103003014005d0002400c15540c0e845c0601c3d00c04000d1021b0300080741305403150030100d007050400e6180e000560381d1002501c10904d8030001007000504454004981c00016030101060f04a25158941c2849400d20703d02510b40d21213204041140c90240c00c501241c110700f0040003407844000800343c040303040c03078113154494a2841c00c00384924032980b0a1040e0061b030001e1005c04100800c180841807082d0201685c000380d888405d000d00380c030301030032015000030301d015510808502c1c410261b01d8003480000c203804e081c0f0f00c48000c3e1340c182c0c1c00c294000d89080d0008020004090303028003e003907460504660443ca80140464005841e024141d02a0345124095048100d461048000c82e405560007000e0328405c01d40780c80c7d440d114015a504103c0300c14055241c086564141803e605040c1c0340e1546070001c02c540e818460003440c2c1c8403a081030764590f40782c2c54050510f985010042020f00d004400c01c82d642d18507070002916081c4c0356440503940300e2041081001d0700f580312459 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 36484690 1250 36483440 36483457
    0x5040905070216080a031403010501050708130e040602070210080610031508010f0203071b110d050118110a0b040b12040212030406120b06090901060509010203040e010e0103060608030a05 82
    0x6010345070300e14101c0c40c04018143c00d06004003c0d6801242a05000407240441480703070341c030410682101c0394609110b0000f03225181c0400c0c002e1011a00141d0403501400c1580c04911900c142d259880b121580b00020a59090f0b402d9079000a60300294100110070074441e002504000303a60341451404204040b00c05500e130810140e840d80004a86015203a0202c000d01c0f80c40001e1280303510314a03c902c0258400d407559000300d451400c0c03801c0aa031700d0612119216400c007000c1c448a060300410b0090b614000381e01210555641d0b100500f0301009015890b030b0050040c0c0443c8104854601441850a05034008081d6240240010003a03030700d60300211007000c80c0302074106076035855502c049002c5031840d58103882070303000101d400304030954080020090780e400b22000780700380300d8900706100482c49400c140d2500211a1001849844d003d1001820741810610403a0b20300390355001d42100c283c20a170040c003180c49c2420010400d0001900840c0050500240554070b407050545c80908148102c0e0343c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 36485940 1250 36484690 36484709
    0x503090a11040902090a0c08010501020f0a150212090604050c040b24090604170105011205030702090705130b1209070806070c020102010917090307090b0307050609120a030f0f030504030504 83
    0x700c40410b5240ca400080203154003030201c0005003803264109000d428006810710000394000700000d211340c400528400b0b9010b00b40003800265416403144425a50030745041c2840f240c0030400d52400c20a041b010390302c02e45841c0080d0090342020b04c0c00b2030400031010344403445507050165600741544c1c0c04010000d80141c020b64a5080e50154690354246c0c011708143c1c0341c0c002e2001c0750002d40344104814144070403070300c0c1c0003c108507070301e030255888004c905040150082e8414030010005042031038040723400040c1400c0890500351a40303594084c1207641d4010018004d00411a0422249512b5001d5007020341078025001c0705081c0588a41c0d00d440080007a0100280384640000390390003980b01d00121600003080c80f200032019100b2140759400380a030940244580c04002814140d540f1412048010080150007460724260402083d90499450940d000c500d540c1c2e02c40e44144c007000080c14051007904c0f10036480c02d003400080c100340d0120584009041c14401000006035016044500f0780342000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 36487190 1250 36485940 36485963
    0x608071a0c1c0804030807080408070605060118140a1a0717090301090b1f03050706030209011206030302010b01140307050a0f020a0204060308130602010e0d0c0203150c18010503090a 80
    0x304640760422000c0690003480e00b0b500181e039980d038000d40d014401c501944900c420740c0c0b15144101c40e074810072680900201c10503c00784002a500e03811564008070705141c03820603000350500201040e1440d5100b1540a000c0301c00004450034034000200080680900190030700c07001c000b40040901c20940b0040000c61070716526501c4803903040c1556140000540204a500e241d4a0002e0149a0545050021024034000440d2008000c120441a00c0d441009441401c2c0b4220b010340194009120071070502062590b940c034100414444c2d400150b00907400803d2014a080c005030154142d80c3c2c21850300c400130010000c40a80000465000381513601d00b0b480710004100080741004030000d0000c0d405030500c035002003480182c00c0a000074a0141c80420340c813a6982500303900725160003688801c16003008440700070343d6015281201c0e11a0014059400303140c40040c036049581c400303d50b0031104960100e1011042c04415014468030312003030800d81e14508040c510307166244034040c0004c041c0410003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 36488440 1250 36487190 36487207
    0x20a02362208070602180a05060310090e07080303040803060a15020a03050d020c1b0103050709060e0f01090312080106090609051309150906020304120905060706051e04060902040608071a 82
    0x30084600a40c2c025200310348506c022503031109032205c50308809100380001c06001c601031034000c04581c014160880c0a440e003a192440d1a000741050340022a018050b800d00080d002c4818401503200740c0c410f02050340d4900c7c00c601000300c00c1c0c2d220b411082c11241108c0c1d40401d95030300000d61003040b54050400684903880c4452807000781c460045142c1490043c47e25604080581c0440070396505401d0300c051000b60744020007229038107654810013000843c0c020440c103140c10b10000c001c40344101031421030f41841e141e0311803a05184041d5081c0380015013a8004000d1590f108a4a4000e082c540c0313061449a0f2400d40051044003243c410544120f954800301c0d403c00520a180d43c1e212100d0500512900803c1e091440c001e400840c1c00f500c600710906004103041c2c2c4200c061409480c0010001b60a100c26034640d280208402414400113201c0141c6d260b815032052411715103d6403194102186003402807052100365041c6620a990b56800310409000303000680680f0340012203100003003038031043d42 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 36489690 1250 36488440 36488453
    0x709020c070314010e0d0503190f1409060906060a03211808030a1205010303080705070c05090408030a0c0305010501020304050609010912030305010e0702030903030306090403020a023622 82
    0x594001400109103c00d072200366001908030101d8600000180c600f8035011003401d403044c0c40308860380300307815450b100090840445a4060550341005080008607280c4020003410304070020b60765182c0302e0f0300001c2004812541008100d61203e81503403d0a4154555514103690f1002041c52805028140641c0c10360301d4440c42c0c0000c1081400000510700d00e43d24030115403207900160920000400f80202915020b0040c0906412030754180d507804170f55503603a0b104503016000410206c6200c070f40d10000107140d90707448031014021030007144d00c140e8a00300341c550802190030460381e00041c035042000422840ea000b00c1503804030303401076031030f19510440d00e001242d0348a11900405440001d004a203070030b15030b040c3d00c89816207c4180c260b008944409005a98900900c0d05090749a401000010180c0c10030498140d0028400c0c01116042011a400a02454900004540c81e1068114030021076070344012621400c80c0b400d040200c0341c2c2080c041148043c000701c88100d1810b0001c41442041009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 36490940 1250 36489690 36489703
    0x100f060b030a0510080c0a0e0c13060f02070b090a0308030414100507030b010e01020705090a02070b15010e060f161716030206060a0e0109022802070306060e0c031321030504021504080709020c 84
    0x140102c0cac20342c42c00c1d180d410140511a20b0760380c0340f0051045c901d0201d503030030380501200e102490051010400300e2440c1c0e100621980300400442c1c0b2803e4a1b500110403440c10402c4a082040d28000402c1c1490603400c010201c41c1500d035014100074a0414030295070341c0214400044da002900d5282c6150b0380c80700c91102034480c17100001d2020040001300403030032020784401d010b075801c00d13600c464080c08207004020745c5005209504419000810041d071411040070900c4d4a9180f10788104004210030400c0c05c0b0113900f024441d060b0061100312007a0030540e0620800342c0c4441c0844440700c1325800d101c080150503205018010141d0350000b4040f505102d01000c03800b0000e800e5030484410301c804070000b901c0350f1840c88215a1141000c6010480c00d201d20462489080c02c80e03050b82c1140d0305e1041c101c2d10304803001426034410780c50305a0040d4200355030510000e0765889441c089880d0410380305000c0c4010a5500c1c198041030107020a01002c400416483d0454045040250b121420303003040030306142 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 36492190 1250 36490940 36490957
    0xd02090603010b060a0806030c0628090b070f060f2705010222090e070e0403030c09030209010f14040203040206031305070e0106030509060604060305100f060b030a0510080c0a0e0c 79
    0x102c02182c05d00401d603000a0140c4220f00070f070140c030326410700f01c400c0c4509800740c5501201404000c0b0540e003481001c9440322a03901c0c0c11440c0a1620322f47c0c5610192440c0d00c440d00548817404000c0e0403205001700303070180e01c00d080b500700c03000c0260740e400c041d80c1c0f04030301b0b410b01842c01c10f8841c500c81001402402d4054a0340041c9223400c0000d0f00840c035840f601e0316003003407081c0e00c0300c282070510070601c44070041048002c4442c4144035101070745d13036544c04400911041c0042d0052000740700303001c40075840c4e500c0b500c0d0180403040800301301681009003c00088981c111414403c6004204101c010789821064a4001074541d0100384880510300d841070820b43c4c217412114191406800008446a0642204e8007a04403481500c0458440f00300388403e130303656800301600d6a440400009030001550380003000f141151980040c1c00c81e1a82240390003948207407501036026440c2c0e001e00c00301c44503000e0a04010400c0c00001d0452005060100300c02c20700e5840703020b1030303040c0c145c00203803c4801c40c404660605 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 36493440 1250 36492190 36492199
    0x109050301060815100602120901020a060e030a02100e03041215020304080904050106030e0a020118230306090a0b04020d020103110307090e060609010c0b0c07020d0c06020d030b0d02090603010b 85
    0x26501d81c036070156503542078000b04900d128004c0100340a1241106280160f078041e501410400721245c035034020a90019180504500c100441000032075898400c070052000032501540d550846488024030380342c0c90744511600f540c6402d5540d04803820000460741100c1040b00c9040c010384450509140b81030080100c10405400003040004000c02240248580c0e201150200556600c0c0d404c1102158100314400746283d01c45407120740558090700000b1000100c684114825035192200080d100d910429400f03691130b0b042c11020711519061000650159564005010038206c0c0d486800b0310300009000640a9007641c81a0015a440b942124410604d41104103640c0e04144000520041d5148a5203040204920114005c0e15080040702c0d41c000c0140d545d1140300c503441d00c4e030250f030090140041c0001c0300100400001a00c1d5481a80039243c00f0b02c018031172551600c800642400c600010a0040514100c2000c03c140e5541042c2000d9030340543c1c00854564444011900429180111a81c071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 36494690 1250 36493440 36493451
    0x305030d090b150f150c0a030507050f190f0305040509010e040b010602060c0702010e0f0a0b0c0c010503010b07030e031213050117060102070e04031710060e0a0312030b0109050301 79
    0x12591140c00001c0c4551042c1c0d446100395848810603841802600c0b91668403881440d809180381c604038045507500040041c81600e41341d45902c50b01e107085180c080440c0454004100441844810701c00d00c0d0407209040f01030000d2065061447d00011824800182074103078064408050500c1641550701034100504401c070a075842d0b59a4074001d10701142d003100c92410301d41c0049081d07440420107a004400803010941000c0d0158010340e542030750200c50540109142c814804195904903001004007500340e20365a40b501d240e20600d042440000b00d031814000200010055805403408a0f08542d42600c2c14079880003843c0c0c0020705004a080e40c0f0300e10a46c0104400120110000b10300c02102c500340c0310f041c841c1081c207419095003081240c0d40f41c050b130001d48003008940101041c0c1ca5010f0f200345482c2071480700342070000f20122800c5d1100f08101d1004503091040b04d800201030780e02c014044032a105100d00e03542e1080c52803079181850400f010380310281403880380d0144014001500c8018000e109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 36495940 1250 36494690 36494707
    0x30705030105120705011b060b0301020a030e0d02010c1b0809030a030306080c04050126030c0607080a1404050a06020a0203090301020c030d061a0f0a05090909061605180d02010207030503 82
    0x10350001c0c090248074403000302c0140d910080c0060b58808550040c0c640c26003003070300b180c007081414002400c16140d9644a2045040c1030340d01307200802c140762030754030001181d940b038900c842e24240f075191448055a25042d050880603400142a8244001d80800d0344018641480d283d140c0380501c050320380e00362140441070310805030960003580c01d0f520707901c08031180740005201300000d40300700388591444110004200c0c0300a0080500708001210001d04aa140000c10541c039460503104a5080300018241424041c4042e00c50260314500c1608071340000d050b0406441e06a1103000f24100200696800960000c1d118000e00070f031484048010021915204108404d5071241d00c88111004014035090303001c45c1c140c0b00e5040701010000d80042150920180504140040d441b105003041440800e00c060b2640356501d5503850b1140144d000600380300e081140320440146420003d010a004003401500e00007000301c1d40b02c400b1500c00302c80c0c0804800706400140e0801c6000d800140070380c040001c1656 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 36497190 1250 36495940 36495947
    0x11704050609010f1116082a0106050907050d15120303140a020a020a030305040c05060301080307050622030e180705030118060e010b0a03060b0d0603020f04090b011a0705030307 78
    0x5200342c00903402402042540318500044540580a203194148103008020b51150444d014100c0ca6101b006000d142810712411122012220320485088001000140303c2c075030401e0181c44010642525242011b0500d4000a0114000c68110004d020f03541c107500e0f84000300d00c03204100203040c1750300103422201f500d06004001c3c00c1400c0b0700d40391151800010a821414901c01c0728024019135001d0015800ca0b40d0b41180505009002540c020020ac40080713442d40d5624015802420024003e580d20030311840c00c22b081c01401005030304140c001c0c008000708201241e226449059041c41c0c100308040c1444000b03020281040101d1904003806010020b2041c4c10500a50588011464100203210700d202980700343d80f10b82c012107410701e1607400108000302f0520301a1111940c40e04000c2142510f44101440c940c00c261004107446450390320030002c1d4100394256183d0042d041d00c09000b460642d40350303a040e030001882010082e00044e044144c980d0342282c242c0d000c441d8043d0640b585c9040c0035a009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 36498440 1250 36497190 36497203
    0x70c050a0b0c06012103120b100908190803061201090b090a02090c030105031509010b10080a0f1404020108181501030c05010503040c17150910360201170405 69
    0x7480c80e0f209450002c01c80380a1054000c14444415001d600f1205456908841c001c074096494400c0755120400241603581d1520214085440f1b81e8860080c1c614026516240103440d910f03554030401c4840c6440c0c0421604c00071245e00a0741522410680304014411600419542001800f0880540144100c0b035030042205080303680216481452500c401c080ca5600344030a100c2d00342e0690044004100c0383d080b005d01c241d0711401d407000000708030360b4580c00304907080d092440100004258000f0441400d056101d43c000141d20200100b0801e45091002c0b01e21030f50250020341400348440009115014000c072562060407504103550a29a80c034141d00348250b028003046038000d450042c0411254414000d9910840e0450259004d2034909200f107103940300d5404040225015209420402c00042030001c0e0164405a0080c030400016034003200458000000b0004140d41c2c076840c40c01c07031100d10544070070f0020a801c0c2c101c3c10203081d4030050343d03120000342c2e002180d019004104401d000020400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 36499690 1250 36498440 36498457
    0x1103040906050315090607030c03060509270304030c0e100b0d0203040302060105060f03151906181205100f060e0f0703050c09101214010b070303060f0e0c070c050a0b 73
    0x12144083e0804e50010040c0d08125641403041d07001500140312140b0907004000d213000c50341000900c00792201c002c1001c03d40c0480c0c1c50104152405100d00102ea0380c1050180010000c4002e10704150a55882e030131005140e00c91240c0d41d5503405c011810300000d280b0a40010200382c50785698031a002c0d00c101006e500120303001c2d4051b0003842d000050b2818400c084458031a41c4841300c62543d6990649000c5044c98540d859800005803090349952002440b0010b015008544030f0114415002da2404003c04454200a204000b41284040004c6c4000707907507100c242c8c60010100b44507908401a400401007640f09c04407000e851030501618041038190a402941241c2d0144465a41c0030f841c11410300c5030039030498110303104401d08460544101e4203140c502d00780100114012a00c00140d100244082e005214007403400944081016054802e060082c125403903103050042ca0800d040001043c02070031085070080008904041103049145140544001495010b41646580394400755400c045403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 36500940 1250 36499690 36499693
    0x305010c050301030330050a0b030f030412120302091c1e080d020f070b180d0206090606130f0c0e01030b0d05030a0e03070306140403080708100308090111030409060503 74
    0x110089001d100301c040300d043c3c0e41c15072609582c00c482d115460441c1100f02c1005802c05010305034190940c9034600071180112801d00300031915043c00d0040605202d951881145554010402000a140720f813198000c0c031a0056074031286140781c413100b6400703132282040407640300441e040e440d10b003050650b01c0800124010204120009480320722841c0c0e00c0702d41c66002e80100b90074403840c400d0400303c2d0000e1800e15550002e040c1410120781e07490021f460292040480c8001c0d041c1e5a41da900390400c100c00d10600c0e00c1c40180018102204150b0312100d000d003010340550a0000300700d13400c5c039141d00320740b200d8240e000d410030808041000061582c07901c20003890029043c00d80003021480c0c1201c20803500358101c4051458120000f50a48481404488054141c0920303100040440d10910840c503408034501a01c0c0781340d01d072074540100040700043c900c0d01400b02d600c05000401c1c590703148400a8a900c4802107070b6800050700107884841080d03014039044c2c4000100452000901e401c40c07003c0711419070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 36502190 1250 36500940 36500951
    0x1e0d0e010605091807170102070c0806040f020f0307030c090c0806010f051204020d051f0b03030c100c03090503030108010f050703051611010e07120c060305040201050715110409140105100c03050d0b030102030709030501 96
    0x380cbc0c1e2200360a0380c004d041084c41c0c910300300240c901030142c44c142e220020b0486022640c0d036601c0410841e11944402042c0340d484a50b1144540c0049046901110918000340110030040303002e00103000703410420400c252000e0016045403581c004034458240c11004581c10742c26034180f11800900303e00762030702109092070314000c52414008140d912028920000c0c00421005559060041058811036070400da20352004c8408154240020f41c00384c10840300115411508045213000c0d1303580038042808041c0f80a0400820756070304880101c02100520700107010444007551a4050045041482100c0c0614440003070b0507a92040e00c5038400303108034803580000b5900c501c20380440e0402c44001c0d0120303a0802002c40059040012003984070000f040016105a44501c40d80c45500b007508090000c1ea40c42c2c0b41100d4030542c401c40280100001c03a6214109081c00c280104522191074004040c00801b003108408000700d500011441140a4000c54903850100001000b5039624801503622f54a8030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 36503440 1250 36502190 36502199
    0x21b0d0e01020a031d0a0f08070b04050d02040b0114040f050a0801110913090f060915050106050f160b0405070314010b0102030f0a02031e0d0e010605091807170102070c 74
    0x4040342012030105801030b01d0f84102d941c4054400981c1a081414803032030b082c0c0012444d070b5032450b241002d0844000c114000f5818414400c0c071b00382d0141c1140704240d2045c0010400d0b59a1044400002c50341681c0104003200081c00507a41000d07420060441010040350101e1201000ea044000700c4104840311800255110440d0b401c803003001c0c41100107400200481340d0340c0d0608409040f02201074003000120407045888000b42d000d040d01040302c241d9203819062003032003002844140d030704880d85400c00c095403601c40080c00b0340c41407004044680b80040351a28501000144400d002500807401000c140341c01d140175621041031340812500810341028150f200c510520540f0484041a0000c0d840e1404a2074904081d803c81913842045100070410309100e1181c1004002040300404051a00c0742003d40b40601a124540e1030329030300e60300d0b01008000075651640b5054229102c41c00303a2501e05482c060040c20301d15690002601024900320301002440154020141f060241c08101c0c80c05844 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 36504690 1250 36503440 36503447
    0x50601030b0d020303070605061309150606320904020d020304031403010621060308280323091c0203030702060f0103020f040510051512070f14030702030d021b0d 71
    0x1100b000307134140d80180078031000034080e9400b550304114000c052420650901c80c0c03150690700c011000310380700b1901c04407081e088040750080c1d02c080e00050800141031141c083c42d03a0760241503610088600c00f000c00c1e000101841082c1200c8954401400540d581c0f10b6144003180654810340e0210005840c01c0c0000c002007900c001568107807610f66444449019a500081e4810460b600d04410101d64854000000070f141100614804405030303510041d604601c02a0380442c0c1d0a50325840a040c00c103c151894900600e160113041c1a441a0242d2591141e009540c90140d241140300c41c0e6202148807181002c1c1c0020265104003101d90844501e6601c03458a18030400d420b01c0002d4000800400448941c03803c0e0700120351089414200c1d001e0340e555580014100031400020811100000410b0011500c0950055510031000d0070084800240c03504d004040b50b00380b8466490701079004c0f001c02d03800742c403c0c0304498043c81111001d5445440c81d200c10b400c41030900d03070302c40041d1040041e0a082c1600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 36505940 1250 36504690 36504709
    0x1119030e0303071d09010e06090c0a020d12060b040f0905010506041202010804050c19030209011706060d06181a070305010803160f02030a0506010f06020c0f060a03020904050a050601030b 82
    0x20014003550554440a1080c4d5085510b00010081c240d0b040040c050705494540c05e40b4020b050313480b8040110300b840c9062021b001c00140c06c2c2e0801c287c0070000c40c054582c00003100d2100c580360385864911f40c0a0310f84244020142608094406d180005001401420b0380200c5403d40e000e03404200b1040c0d1340c03081007240c18492803240304c850814400c403a00141d8000c05c00b20358000e00a00540d030584090700300140310511035917951a4140503181c4280154205900d07990701500c58400310b054040c40f111030007035440358014102c0e8410700440103450100140c41c0c0080c0b02003200740b0440030b0307104090702d02200201100c5021028198040b00011700e114481e000b040d040312041c1018624084014800b00e050f0310700114140c0f2075000d5413500d000161010091158502c0c040d00c0a0076941d4105056030418001540c403000840d44001015516599141c0d01140b600c001241c9241e5550a4064240c000e0300800d031200c0d41c007030315040803c504030902d42c20661150b4001d0341d04010b81e00000042011f00c44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 36507190 1250 36505940 36505961
    0x6081005030a0210031803020105071106060906150403080309030405100c0201080a0e010902030709021909030804050108070e0306090a0b0705130506030403090b0a050c0c010509180a02040801111903 87
    0x248011002d10140c1000307040810702001c07034134000c02c00c60301c1100240c0080d002440d0490041c2c6d502d90801c804c403644060540c411400e850041c10280c1011000104000000f800c2c075072042c140340542032100c2d51000c0403200107541c0b2960075900c901d41680050307101e80051255a00441c0c5014008100380c0c802c00141c00000d86c140c540075071548070b2000b03c42c0100b1040c0c07904240c0d9036030342c500103025a5042114034001d122801d0096a00c07a5030304d04200414865044000c24000841d03405e00c0058604130540d42921403e280182e00c90303580000440c1c1400340e0403060740d058020f8006002c02d5100104000207114000c80e15680c481e103c0b00d50490b12032080c220b164140d115600c2e0b081c4001d242100055070032600a03c1d1490381d8a840c0c59100e40c89501c005240000f007200021341000d0720308244503515a80800b420003504003107200022a0302c405080082050144c11400015126002603040c2c80140292100030840e000e00744280721203561180b00310440c240d00c0668540404c1d0712901a40000300c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 36508440 1250 36507190 36507193
    0x50d0f0516030201020f121005030610030807150507050a031103100513090c0e01030506010504020307120f11040f0f05030d0c0803070909050408030604180804120c0504020409060608100503 83
    0x3a88501d11211880030984080301155001c00c50f1154080301c00000e0a12180031040200c1c490505a1800c102c40c617981e0b004074060b400c0b1401308184c000a00884a048981000f0180d90b41e00580c078202141d40081d0b400c01d90700c0c0707150206010103103a2010151028007c1078908000003c01c071400525036000446602409004858050040b824050b5559109078071285020880700c040c0d64446640d52010b400000301209504010410b0003410080c1c01c1c010003042d1411031650400c140010102c0c5498600200c03100e48800040c0d040b03880c80d902024003400484402ca48464075120000800c041d103200c0c00180303520020010582e4600480c00c04030806140d2150761154502c0e83c0d850090f40c10051035202800980c4c0000a10399032580541c600c602d20a00003039580345031010801c005c45d940160764400c0314a080c094000054070303810807942501c3c29000e08405165103441c2080011440e0f030880d82c1c100c2d001080008006081e40c1014060311110f40f101426540c0d000c0c4e00005251280c401c41b82d16 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 36509690 1250 36508440 36508447
    0x509070c030201140106050a20121c0e01050601091d1303120203010b04030b010e04030e19090e060f060111070303050d020405060c0a0b1b07080313140a050d0f05 71
    0x14034051540421014442c1c0008520031030b0303d030103a0390b002000368490000300d44001401420f050307200f100c201e54034010307404010f035100e1800c100513a0380454001a48400c0b20000344640c4002c0c002416403880981110140a0800610001e074007800040d24514046109e0207004190201413200b4104901c50403038890400f590350700010404007600f00030a9091080305095089200707810300095002e8180a1100c55580340b441c608416030010503400344022814280500001a9005000071040d01c2d0464440e0034403480780e0164a40d524180c0d02035410035290070b400045c203040128540b482001c0d0a8949a41a03441500555900260012410098000f0041400040c0c02807001d000308442100380141807603103690124140354405080d01100782e010700301741c1d01001203101800e030b40142001074070324502c29540079031800d50180107801050010301000080501100802e0b000715030303030010b80b101114407902444c652150850002500c190158042400390a800703469071280c0c400c5241d9070302c0d14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 36510796 1106 36509690 36509701
    0x91c050604210819020c011409070801110f0711130203190b010504030308090a060204031a01060305041a0915010602030c010b032b050702090c04050111070509 70
    0x10305030024600021265881190243c01500e9040e501444d443c20781100f00c0a80100d211030f0256600e45200050b044402d0701007240a0709050003506c1c00d00380c84180301802c0c1c2d0440403081841329070030008001e031041c075000201040d0f070007020340101a5500000048002e00031305050a041030300072051014410b2200c0804280f00070350101001027480d440d0002e04103008901c000341c2800a4400040d8400c00c052080a45080c3e00c42011503807a5183e1034014040c0f01406050032001c03115400200f2058000d00c030711170042da0854030749449200e443d402c0d02003418006101152034041c0f248550b49139011703050b100e4083c29543e0040c589405901c030a65007101c0b10303110624801d0344900c00e100ba176085088104419480f07807580c2002880c40f2070030b0039152403140f00e00007900114440c0c00c00861005480c060000d484090b40c0e500000840300d4901965103200740103440c0c2c4800c50001080 = true := by decide +kernel

theorem cover : BRFrame.Cov 36330940 36510796 := by
  have h0 := BRFrame.cov_init 36330940
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36330940 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 36330940 ≤ n) (h2 : n < 36510796) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
