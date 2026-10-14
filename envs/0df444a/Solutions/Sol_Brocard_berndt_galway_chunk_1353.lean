-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1353
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:31:59.517009+00:00
-- url     : https://prove2.me/submissions/a7bc921e-6810-4e48-9a20-905a8716d610

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 243165467 ≤ n < 243345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 243166717 1250 243165467 243165469
    0xd03020711120c0a180b030f19020619021c0f0801090f0603080f0904050601050c031c0608031c051b070f050a1401050f0606090102060601030902060405030312061509 73
    0xc4050550501116a00041050220344a00780034140c3c007215030000300d08402003000c111030548442100d200c0c0e0700802401c4550000e150f645c103013440c03040300c082c2d2040d800702600042ca124002511480540128104689010a20004881d4002e68000740c3c10003080e1600c80c030074100c0c0e203862a901510340713007c0c1c00f00c16038405401864180640b1090300d0310340c400503602901c03d420440045502048069031040f40700c10049040c0c002000c600d124900b0000418850740c400c0c2c054600040c0e103800a1490079a02504442d12040200c00080d030f265294140042c6c40d48040c400380c92130320b4140100380a50305c0c0c407070580001c40348002c0c0107841250640c0100585402c912040c1d03016241d12000010030300030a403c0c098602100c0900062480c62400319484501034190050b5002c0d10909410b0b00d40c0740c6030315080000301c2c09482c0485005a001c03400140580d8403941054050074005400d04d40b6107034890000c00c0c119402042440c201103003140a00820b41030444d582c442455415001da41406200c0e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 243167967 1250 243166717 243166733
    0x1e07030605040522123b03060412080907032012010e0c0904150612030207060306030305071e0b0a0c090503070f150513030b0603060604050105030c12120a020f0d030207 74
    0xa0064240b80c2040009050740d4015241c00031b0402100c03d44174051100c0036044140184903000400791000c1083e4220820b0030005030b81809075030f000d1200c04242802c0081212a0b420041c5000d90a110390140000030803c4a500c1e801062116080c106200c0070620902c0303000503010541d418270382e03d41180803031415008a8000c0c280f0328102c0d0340070340c4ea0301d90b41840a1a901c5030082c00a040c1c0c603002001032001633a8544a074000d22907000c0c0c500440d55450141d0444110344005404a0010000240040c09010030300c0640c03001c110103103070140a039445114521804484c144059560b95402c0040290050f1202004003411030041c044103040504400500f40203100d0314041d44820382030951414019419150381c1111070442c0d801059172410071030031424081d070b11103000380540c00204620341894020300341602c0e4003800074000f00d4000800c0c03050039a09015454564010044540300d0300030244000d014041b941c0e030080801603c02c280c054100120079081c1e0f014503104001140c00201c4c1c04c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 243169217 1250 243167967 243168031
    0x260601030b0112050f15060a060302091021050414070905060607060203100b0309100b0409030f050f120a090302191a180f070f0b0a0e091e070306050405 67
    0x70219040c40c2e00062030113900d441a10306148000e409500c1c41c4071140606490340900c250006c40c3d20390140381da100e9003541248680c020031600150800e4440044d5406142e0104281c1074000c418082501203a00000441710242e4007201c4000c0b24281414420714200480c0700600403150040260382014800120303184034a9034010032072074000c40094030040540301ca10004148454140b552071601c1d015183d01d5900110034044901c1c0b80c000560303450708182c41180b042d25459240c2400d05407074a0300996a41c1c0000c455143c42c00d4003081500e41da2401060410700070034290030046886041c603d4081d05111440068925801041c9060300110760540a206141d04943d00400015100c0003800f400094105009003598440e01da400100110005000e2049419541001030100e0726101500494401c0d1040316000a4142100a146242000c00ca03600702c0b50130607007143d03440f0040312123445401d011035034000401c1d6a0f0303d00704540e0421f40541540403222554000141c1d10384070703075450000302c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 243170467 1250 243169217 243169229
    0x6092503060b0a0b07061e2310150c02040506040b011719050f0402030f0309010221040911120106090e180c03010f1a09091207110604260601030b01 65
    0x142c500000701a126400900058241c5020507a45e0b40124204031024245c01605907100e20a0010380e402d01e0710f014400d807401511b149560074161484c0e010103584419014051061600340a00c1c00103120b031000c4031944818845840b0410484481e004220854900900803030049041c80c00c01043c030f0703034042c034019000c4401003607541e03d076180c10444000c8070301f407070f00440260b528280c28800e0021030360344004c4c4510700c00c90842e01c48407220f410054483c0a44200b80c1c1c056440410030400e0082c0600a00d00c0100040240a0a10b03036644103076810344820003400c0a010710001951107a0808446195000d080b00341000e0f020385141c48038401c0c40d114001c010101500c41e080500034950300034030061440050050080c4001201001240020480420951f1090003404080c0c291801c045260b41e201c6c41d54403001d09a49100c0e6000064643d110300412070b410506030802c070802c2d03510080030300003078155030601c8401000b840f00030000083c1888810101070707100c58010000148844021750540302 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 243171717 1250 243170467 243170471
    0x10090e0c090f01051b0303040c030213060342090c06110d03021606050406020a0f1103090d1b03060b0a0b181302040f08060402010206070f0914150c0609250306 70
    0x5944074060b9542514017840304880c0000018082480b000c034246406890007155510203403450362002e113080340c0452000801070319101840310b00044c42c003a40403e40d82c00c010503031544a281005040403101c1c104041041407a07540405000740501940b142002d0802d40c03d28110341a04c0750b2440d903458001c0801710003011b4000449020703015005c484544660ba0100003808141024078140b0082d400480c1038000081100400714100340c851200000504507480285140c102104180524030b00c0d0054103a501101d0304140a000303844400302c40006500840c40041d40035410420484100d03100da002c4000448207000a9880740315030b44c24003082d0441180d000c08003c05640720301000c0e0003103510000e01e80e011400b001840120204009119610076820b0341e80960f24074170181c0d2a500d03a00345040c00a1000c00f8140140100c82005850480b0014000603a000e480500701c0f12036440000440a240c00c010140580c6d500d08000030401100c04c1402000384000c0078041c4a03606000b4440600401c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 243172967 1250 243171717 243171727
    0x30711030d08060d11040e0a05010510060c02100c020d080d05070c02031e0f070b0904051f1206021303050d020f0d1202030a0e070b1e0304031e0e10090e0c090f0105 72
    0x3e1721071442100f440050028420b42c00c40d403481944074009039900785c4a650820f4000352036400342420007010396683e9103c41e060102203800f44908002e6406c00442800307520021080582e880c003d2941406201c1d4402d140d43e00030341c0022500766400a4405000c0c05203c01c034040040e81c0c007107154450501025003a80c014000300844518025100444980500480a000c5070302180b00e03008001e410000e039020b000c039884900d28018070b52a88000c00c00851504130060000c00e9072002400d0815001d5500542410b0060290106030383e0319a208030356940c082c0a490000c0d070740501210100e000704034003505640704640805000450040c90001c6074960000004000300306584c000198600d07600112200d294a940120060354401d032002c41254004900700c901400003201182d101d6541541e80e0300c01c0a02001c2e4002c480b0300b0301a4144180b001c0b0806000050700ca03403850344407002180ea01c002e1180d01c4c1c00c4100c0308a11024040c0581ca03c1c080000302c6958648000e502070f658001c0c608590741d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 243174217 1250 243172967 243172973
    0x211104050c190903120c1b03080405060d02130b030106020d0f0206060f010917030903060c0705070b0304020607050d0f0f0207150f020a05060106080103060e01050601080a021e0408030711030d08060d 87
    0x40c43c035400c000c244c182d6064000009641c060242280755101d0b145504022820030040d650741586407000500c0748004010600440c10404081d040d406100300025050107840c0044110341071850304000e040407008001040929410804118010078070f0034411003c00071404025100e482c000e28490081e121400031400592183e0302a100034110048100501c014040010f5129800082c01901c01c0c400c800100301c0c0e1011540496106070b5100c030090008a02e400900742c0c4d00e800060041c0e0340402d0500074080401d41c1889900009652551a42080f00854002034080500381d1698000c6510060081c4030700c001d0000702c0f600444081c10034544112403010101e2130924601402403150091400025019070000d080e24140c0348200e006115030001503200c14201c40c4e0840340c150000c0d442401081703101013264000d0021204014030806030b12903207003d09150798002c0d405221140d100141107003c0c0680c0c0c030702110381a50110301404c03814220f18001840c99078050220307032081800c0c015400070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 243175467 1250 243174217 243174227
    0x30b151c0b060915090306010f1d1531060e010308160f11090c07050d0f110f150906060109030303020c01090f050a0c0b09010c030e0604211104050c19 66
    0x40000041a80d0381c4130a4010000d40a0380000c89118001d00c540300000c01e04a00c0202e980081c1c034422520342d00480a0310550317002503c1c024000e002991411442d9070025201c0d07001100300d400074540b0590082031541c0b6080e0040b44215414114945040720030b01c2003102d0102c000d81140d8100c842551103c20704800c0705500000294001c00d015000e02c580c47c200003508400b840c90323901c120f441654680d10711401d104148034840000301190805810011018016013a1140c007102d18a440040ca044008203185003c5909145030101c4d84081d080b4010161080741c0d0725800400c82001d080e407170030306000207404e60070340f40401005d05401044804d405402540109000c6800c41da01041080c92030503d6078960130400b00c00d0350281103100c2c0205240d40b0712030031903142d00410703075030310410442c07544040782d01e007400034001d5030711190401001800d00000c417103030a01c0c00d110701c0544031549034500c1c2c5403010050900e00e00d4016410700d006c102c052114102a60300f00380c5903c1c4c000340c07102140388040340c1c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 243176717 1250 243175467 243175477
    0x160302070c120b0103030807033308120c0708030405060a0f0c0614010626150d0803100f150c1104090c0602011a0312040b07170307030b151c0b06 64
    0x28020510348200b800e00080c11615130499029448200091319103000031030954501200d200c810008001010300b84880840a200000b00040d14800d0801c1d103c107805410b203004034500760440000816441c4560350180700550003003034501c004500c0d05190901040240c00f0b00343d5408240203251010350f4080740940d25060b2841e030f00c40c4042001c1e16244a407000361490a00484002891414081d4140c010101000100c076000d41407866507560f9110000c001c0c4034416030700c107400604038460070000800d05400b85010700400e9040d04c8203503040c620340d0100f0300820741c00583c680c003202d80007031030403034026032002c0c200c54001c51209044038010700410068400c07040000c00d086224500040c94540c10740c003030000d808030004200348100c0c0d120205507482c28488001514220200300400441064100a18101b4803c0c4007500415140f15011034030358104071044004203844075038059207480c0200d10220300300c842e030340b0351400d190035180824000b0401d00c480ca004150307112500c103040d6850005a030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 243177967 1250 243176717 243176729
    0x9060c03220509040b01051002030d060f08060705120106051b0a060519060503060115090302120d0909060e160e060f0c0f03070812220b0f0a0203160302070c 69
    0x6a40c4003021010003016140084000e120703445540701c0441c0502c3d020802d18004c035005200510a80d0070001040501070030125504290301c0100660100c44a0501a10004080c0782031181c00c0f1524250400e800c0080080c44801009000c20404070052242d50045040d52081d280c1a5101d0a84440024092460100310140352007004010003c00c4459040544940403c100066403120110b0345c21040e1691400340c140d05030070079001840f90310f201c000340c21000d542c9443e0040b091540e0383c000c5410b04002180c101c0361a0052840c01d2a410b810000711401004040780400600d898941000c03d507540190108003140340a502c03c00905200b406407001e40d00004295035034607900081500003d5000034502c00c01c1e40200d103084080c054020090714000b503008810b403890308400801103204d0910051003d4401e2103104890120a00315029035050103100701e150700040d090040da0f5070764020000384540c8820f801081007200c03401c03890009039009030403400c015071540c10904d000129400e05130441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 243179217 1250 243177967 243177973
    0xf06010c0f0f05030d090b1504020a050901180509010e0f07081b031b0d0605030f0a081b030403050a080307080f07230415031d070e130519050c0a12021509060c 70
    0x18070510a07117003003460291602a10a081308c600310070500059024541c4283e020030014084c0e480a94000c20010354a2066028908176054a0700c000075071192007a000035008880e04010002c103c1c9900000300c0d0011820f040203002c900c0c01c800702c5010410000c4038142c0114004c400700702035840e001c8001c0e2081126a0741c86480c3c1c164a03100348020300952145078440d100e8518003503402c1401240c1d41d8810760700460b00d50301d406141d03005440e02c3c02d007041004006200400c80000414828440341014600c1303450100d40d00d0809c0c18000300702d40b00141c90031040110b11410300120b260815020180d0908440e003101d802c00c50118001c030180940d5000081e05c0d0207400d2103100715981a44000422004001401c0e000300d01800b4182d5500e00c0390054010554099020910800c2607480c4203886500c594129020161055208050302c2000741c0210b600d5405a907035540c01d4500921008040c201c4000c0c691810300046d00002c0c0072001440c11301c0c079003100c00540e80002d80c0f1142d08a5000d03803019130072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 243180467 1250 243179217 243179231
    0x120f0d0f090f0b10091b1107090207050307230d030e0c040e030d050106080f191b03090233030403020c030610180219030c0e180f06010c0f0f05030d 65
    0x1c440e1114045544074605044c3d200c0c0850081584d2003543d0519403510070480e20006280800c4d5007030000c4003165101445840b900141350203080c00140282e0b445a405941c80701d01500e8081c000e00261000c00046441c2d058504000c017070006211480310f806840c01152a85900c00b5060030310b0007200420383c000b82010031001c500b04000004007508044810200310b50781c0c0e07842c42107031081002c0e03900040e80b5006101251140540a100400d0100c02d03600020b00302081d8500e9000f0403207040c8540000c0394498650800703620b480c0002007204090000300c0f0320003a044510725900e44000320b00b8504c41a0020000c41e060610810141d540c00b40081c0c101c901a003460068035084410340d02c13410444c071441c0403860034211040d0007074a01e4160059035030310900c0880f203800d4025042a4084c08100511158803d4490b5142c1e440b9903103a0014000c55026402c045442c108042c80003400c80e0305100c078041c5c441d000900001401e408498111201c1403002181e80740081c04d51044070b0369030102608000e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 243181717 1250 243180467 243180473
    0x5101a0306030c0d0f080c030d0507030b01020c1c080c07030209180712080301030210030b060a0306050301061d19090b07050d14040330020f0408120f0d0f090f 70
    0x29030080c00201c04441003007500c0f104000641d1120007009094481e01d13546180090490005851034410071000d50b4140301022440380200d076021501100020b4959008145a50301800b65180c1c0080540b40300b10360384248142d00a000074001c80c003e125450020b4420900e810030300c015000340d9401031800b80c40b801c0c58040703e0707244008020b0344040ca00815000041c043c021075141c28005500c02c9a241c1168a19001c02c4101d1000303010704d0040c540c880c0c941a0255803060014107040415840c0000c1280c2001c007410308561864200345c800c4030f01d16882e40c020744081c0c050300b036100d00703a11110950031401100d0b0704042d14000381c0c0140074084030024400c04c260010050400682004001c110100b04034204d290443c0c010780300034010586800203c80707400c25012035070030400d260743ca519000ba807000c070b82d00c0304a03800030001118103400410184802042400120f4540485071011030518a51703584000503032086a00c2015120f0765078503000c4010604da00034055103074101002501c00850381c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 243182967 1250 243181717 243181769
    0xf07030e120307020d0201030209040212010e18060c040506070309080109030503012301140c011107080301080f12090108070917010509070b1c0b010c050607090806060a060c060510 79
    0x4a1a10801d03071551030400340034001040c0c49106030000c0a0b080580c41c00e0f00150002d600075400c0603040340e001c100544980f000424007034000d20001d02d00d4205480c000817140f100d50190110314525800c40000d114080d110f420a540075134000701da0b00b650354000380c5025502018a5408072503603500341642882410380020266048901c2a00e81d10b0b100e00d01e50008504129128145a000c104008050810891007c002c0c2000c0d940000000504d408040b20083d0140c000040482d50402c001006000004090000c0c4018441d904010182c0091001420205000c0e082c51107041201240008041c1803041003000020010242c034521480300d24603200340a05400c0f604604544a2201d0000b8000424012649100c0001c1404004110425014409032072261301482c10004110001d1300450000d0200c01c0c01040181c0350b00e20302c1d5181c800d4043c1000401003005208a00882e401c00100da0040401c0c00760b554001400501e650382e030110707541d46061642100b41919428031400114603000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 243184217 1250 243182967 243182987
    0x10b090d0c0f15110d0c111c120806090406091109150a061404030213091205030108070b0405100f020f12090406050d0f120c0b100303080703050c03011503020f0703 72
    0x4041005070b007140c0f4080c1613a002602a8074400c95500848565404a104005442c50b0510034020002d14252078000a0080c4200050710006e00101002480400c00354681484c0180c441317003886102d500e454000178103400c600410140c03106440e0800441005001c4400761070030300004202071440d0400040341c2c4841c80681100034001e0b0512480030524a004481d1081c01e8810700c245680f030a07083d5030910207040000c1204005c440c1d250000c19001034240300d80344041d00d020b95105a103d6141403811403070030245074000300903408104801d116585030740d8004003d0014a0421408864241004078501031600d0108081c1c0d00400c2203030094225100018618054101c030240102e80e1624104001120492305c000c001841c1c44d14017030001b44c0c000f002a50b040840d41441400c01c585030300ca8481d024021100c03c8610444541c051080541005045411502c0d502e010051403a007050007030310922060060840c51500050121400da00c02d4040300ea514100f0b0031060344403002ca140c05800c4a0034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 243185467 1250 243184217 243184229
    0x103210201060506040b0f070611070b10060210240b0a0e032404020a0308070c180902030a020f0604030813050103060803070308060607020a09050f160c0b010b090d0c0f 74
    0x6282814446520500880041c0d030f0000704820314082c130b0450344402e40e91190b40d494030003242c1408200c0100328548509201c40880d1040c0513540d0100d03141112540b94018402411645065018004140c2c00104816040d402d1000040c0340c2c022105848a00004441c0616120b150302c0e00c042400004e4001406225960b40c503a1030254212104250310b944042d04580481c240307a080c0d200780301613911011500a400517005510307030b98036515500f000741e020101c103584084003200300304480398580c070550940d00150f200401003151141c2c00640c036420440d4029110b01c04454040b8a182d481e038040360300459111503459500c3c00310301a075076921841486130b640403074a000000100c07048080201c40145905a1301c4161560310b070403c002c5150030849040c3c0c1c000c034103584042910801c52003034134010962004404018641000a2031905085400c21170400107054100c0c0b00188000d0592415201c100c118a61180408404202d880c6a9103501405140c101e5000090340d44080390b9160698031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 243186717 1250 243185467 243185513
    0x60203070c12030b13091a091b091e090309060a09031a010b0409020a1b030203030f06060c0d03050a02070606120510021305060c010e0d120b0307080601170a020301050103 75
    0x8080403050b400c070f8a071010043d400417001007010080d01c0d490b6000f5103090344110130400085201418603020140f04a075603007100c0e807182413403203c0105101603a40024108407038031a86460301c0d0181c020a1003c0701001501160114040303650703500c05005031100359501810351500c1e01d220940013400341c03030640f1040d0340707007100e0390b1809844184001c0d426050f203582c001a689443e2608141000030352040b2800001c2004511070800c041c0450600082c0b07460281e40207540340c2c1481541400340c003902501c143d104480400c4009203a0002141034121120075082c009620340e1200c020401a204100c0002e1182d8075010340030603503a07a80038070b1030145030050046402018400200a00f28442c9040d50000d017240b220082244c1e00d4440010310000034034000100f0740c9611400344a107010400403036200410100c0c103020490020300d02c950300c20048128003d1004901d03103100d0544810301030040c81c81c04001103180410f1100c0030402d2022940c0c0c060020442c543c1d503820007010b84507130281d0b8018010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 243187967 1250 243186717 243186743
    0x100e09060d030e0d170d0203070f020703030f0f140301080a030207080609100507020a05070b0306010e010201091e03140c03041d040b160c060203190e1621060203070c 73
    0x10400103160032805074543c4440c00300107086802c001c8850050041100c084991441c117400410b41003015040c0507031050300158a0b410a07030000b4002c4c04114540720f08642c0b02d0b13401040800e46c001c03114a06034003513061202c40030404a2044410740a800c28412280e0300005c000247c45000003140c90300e480c026030a0b00c400c1d54444814588804055800c1181544003083d9200b20050030f034807031604605140100c5400495954825042a08a5100806e1083d02004000681d600204441c0d01000248020407108403d60f03209114002040261200000407100da0000c140c0a5040c24000540e00808240c8601c0e840208913507e90007406403000d80c0a80c01c51507458110381010b11405140d200580ca030455840c030b00c900c8140032240c40c2400410400741218070208405100541c040c040806585040100190300d1400b41d5440c0a0300c03898644c4414040307504404180d0011064440010400d5618460b0300a114944400700300042c18091000080c804200e41040c0c014000740e206502441880c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 243189217 1250 243187967 243187969
    0x120204061e0519050d0c03031103070209010e100506070609020a0f140405091002070b18070605030c18220501050411120a060e01030302030a11070f030f060902100e0906 74
    0x1052207452440d59000c4084030900c02072900924400c42000102d6005a140d551000020740042250314141c41408840505109050340440080c00300c84181009524119060340803451042c014419040180c00c4130020030101000e12040c00010000104026100c0c1c18a003007103001000107582c128410200440c001545100400b0100c0442d0b10f000310413402c1e100c41c18280000351800804002c0e941c020030900c400100c0a5102800b10319004000c85240e40c500001440405502d8907541002c55000131001c00038281e0041c12203a10048442d07489446807440c05024001c100c0c8004680da001c1d504176804041c0802c0080100071030641c3c00014407207a41e855003031104481c00c08095040d1030f5030402000e4444507800234091303006600c03943c002403103e030b0350f0b08142c0800748203800c210016000024104000e0758459040b200004010018244041c50110307041e02c1c0040e1f612004041c145100c08a005010003a07001040d1540c01074000b82142000d000020401100c0c01c40051140140320041a05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 243190467 1250 243189217 243189239
    0x702010513020f0409020406230a08060c030412090312030e0607030b0a0b09010c06050103080c0d0e011b02130f0609150305060402040b0d0501060308130815240a12020406 75
    0x1550054807100c407941a01c01444041d005d0020141d81054840d1000a00b0640002d0390380d5000c4c04459085c405215400d04100320b480c181e42c0503881c181d001c44107214814100ca81240d0f0030a41c03103100c0f00c040c507036282c9040c0c83d210807551014200b0200c06000380815074160b0094400682d0340380075140c0c00d0380c0c1d20340203504841c0f103082082c0c2c000d00c10807000d11900d400d500062180f514141041c42c0401481e13640e01d001d4490903001100c00d40c40200300524501801c0050f403941c00681c0c14209404031230300000034108010816071010807090b5566210544d15501100c903400f0100000070b02c8041259046000036140074442d04a000345000d9140402c800181c0070802900d52040251140751a25020407010307061905289a01031004001f150005000744140300c0114401c0140580710304100409038010102a0b000361003580040b5207401c00244541e0901e5800a1010640c80c42d1041c20016044046403144420f43c110100d0000814420700050560080910803202404016242c81100c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 243191717 1250 243190467 243190501
    0x10e010c1b030c0b2214010506061c0504030507140a030e220207030207050603040b0106030f11090d05010204171501240324120b060a05220902090f07020105 69
    0xc00a0900400c0303c0005200301215501302c1400300c80d42407808030001144101340b011400c201c80c40c0749100b040d00d143c00c0b005e02170b0b0341d0702000880e900f6061003001d41809464030b81c88180f1004c5295110005806c0502a906444409401050b40d00c01d01540c54000d6030303501d2000380c050300400c0e001e03025000c980c0390080031072074820b01b4002004858640307020b00b14081e4102200c11003c0d07000d255004a81929104040c510880c02034100c4a01949440c0303020303040714200c01e0051b40e03160a02c0491485020150102c4800c52010764002c0032009803420310710300a008603000043c000304404698103c075540018900d0305501d15031081085079030307200034041002414222210640081c009142d121600030350100510b8a12481070486031000c0d40c01c1e800c1d44d0b9419030000c202c440010740100e41880720701d803503444e4014070985280303031014102000200030144004044022a00440801c440c48200d5004118904d5002c3c1282c3c0781401c3c200c0c0c604080307a600320b81400041d880d00000850f40c01015111031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 243192967 1250 243191717 243191723
    0x90604110d1806021306090617040809010c063801140304050106030b010603091e0b1801060314061806011505030c0c07030302010e0d0e060306040507020f010e010c1b 73
    0x1450000004028070180810070000a59021100c0070940812458002401c1e441407144112004500b840760107000c11445801c000708100000c43c4003030b110103036003154640160300410754689a0380c0b03540040700c520104400c000e103030303d007800903000312051440543d20b03103040c0d07510842074003d9412400360b0505840341802c038006452541c000e510001c610b801550007902960011601589a0f100c296000c18282d0140e030010341c2d2103401100b0b00040d085076aa02d1420120660000d00c030640390410b00c800054040b00741611010f16001d120030095000300019680031000c2032140b0303801695076844020440e940030309000d003009112012100805c1c0386060f610b0f0041c00058080da0828212401c2d0002403070400e801ca001c000703098916400f00102c2004600c0b950000c030314003403984001e60800c41c580300c652041c005100c46580d026030341e00090381d038001820360b000a49942c491508a10700040b00c61502201d51030205503418148041d0030148011405480303e65244440b01c115842c0c5207506100a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 243194217 1250 243192967 243193001
    0x10c030c0509091501110105040302150717060906131104060809060106020348010e010c0905060906070f0c050a17030d0504170c010905011506090311040f05040809090604 75
    0x140003e4500300d81113411001850400d8406503040d54042c00c55009071025005a8800c1e0a0480500c0e010792460703038070007000d1801414010451108140a60b1302501d01480f44141800140c0c068540e400d00f04940c0411503030502586d055070804680c140c1c09070144c2000251074200140444c440080e01b0360484116600540c541001d12000742c03003200c1c01d900d00e00c411800d5081c42c42034503915801038900c080080d000041c02d0700101c0100e02d08440d100198024a6418001441721703094021210000300c55007900c1c0d45944558140000d000d910030b840c0020b05404003c1c05a0741031010b4840100e068600035030b0790100064482e01c01100c02c8017141240400e0b036104001801002d82c3c0c40d00505e801c580304010701403c00c1c071582000320481d0000314075500140c1d511900304080c03040034001c0114500c410460305007101c7c2803020040c8003840b20300001c7c101030b80441d800400350b20380b54000b015009901c0402c126505051912a11301d03840440c8251240480c0c80210300145003038414020040718403880 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 243195467 1250 243194217 243194221
    0x40902031b0402040e010b0a1706010c0f0f0c0e070f0c17090f120a0204060f060f05251a090111031807050d0605040b010b0307021f0902030708010c030c050909 70
    0x341040d01070600c0080c6400a03024031000488105a450090103007824402d100e4855030003ca0081400842c4150342c0400b0700d111040c022140d07017024030540b00c20f070001b003401c104043c0d90404250b00201640c0007400340003003120020b08055090301050241c28256101982c9102c011012603110114510142000300c00c640c2d81240c1c00d02020041c054544064894603103400081700060b404018217682154541055004104500d0248500000340840029000200d4146000109070500e5803401d03500380600000c0644a41d000f0707940344e5104c0d03000c0c4c071070401841c41d040c5403801009044150b0710407440b4402e004110300c1c4e901800b40001c0040813508050035541da0403180b42c41c11004481c10030300d9014101c00840d1a856103001b02c01800e028070008507807804c19142200101e24147d210780c50054090062001c41da0b804150054910b002c40b081115030030100e01090000e11000c44c000394144102c1e500000d1000040d0400301c5220510b440c1000300f800303540c1042e1580e20403044515440312100300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 243196717 1250 243195467 243195493
    0x109032606010305090c0909030301050111010912030509030403060606020307440403060f05011508150d061b0f0e2205130b01090207150e1e121308010b04090203 71
    0x44651780c8440c0d000c0031074070740341004030108041e07560646004d030540d040000144240c1d600b0480400d02000c2140080102400f1511440114031140140d1000c15495001094082e40e0400a90707000c0c44d04044200012a91403070042d5480e4401e010403550004102c1c001500d1841200896030445c44019484000b00c50344070030207100110f9000120440300090101001141e41c911918080740c2c11161300240325414000c1c0c09502a0f2040031103002c00c8824020010840c0c000e240d40c07101d5000582d06052011940d2400e000903207070026914412805940c0711900040c1c0c4003044cc0d00046807600d40500c01c10380c0c0001e001c00300b202c10540280c2d1046100141000050680c055a0b01a403415041d404502403552080c80d04082a0301401c20150041505000c0c8144422903401220710f9190801524075040c21050711400d154244211180c10701c04046020380061103810503117104441c46036070b1241a10520700505ca17403406160306944c40d09501b0101d40c181803203402d100340d4006004100400142da = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 243197967 1250 243196717 243196721
    0x1e06040911010e040e01020f0c070911070f02061920010509070513060b0301030309030b07090f0b2b06031e05070b0f1c02090103140412050a050c03070501090326060103 74
    0x3e1401904aa602c1d02c0c003041100e0284041c28200a400503900da07a9001170382c0e60f5148c001c0030341010b00c44529050f0004152103145048840c2154003e025112504507400000c026024101ca1030f026085041800c00809034001d0000c490340707254804078031386160b0007080c490807a8011100040c0c0703503210100c248400d113001c80d0004c81f410340c1c0303040100d411034403081404201e800071780c0110045070720b1b480184108180710920030f038408800d203000d089103858400407203041d415511800c08075140001e107000041044008080c94030007490449040e2481c0b22161400400035840240c0d0381c020910840b00350003064440080946400070000e000e05401e086440e5030b6a800b11100c83c0c442c0d007041160007245c644001c074000303003810f00041c01601c41d40590000740c02e4500055140c100003000f0403c0100040154401e5410040b25151213078030b410b05450306443c94803e5045c001c10301e200115200c800c2140541140301401d1081d603d000050140f510034081c0480040803104410221800190b140e502c0780d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 243199217 1250 243197967 243197987
    0x2011b020f040c051c0509030f0a03090203060f0a060803031302100903050f010c0e100903120c0b0408131d0703050c0d0905060601110f12070c08061e0604091101 71
    0x41c49005414200c2002074221542c4400e01804180085050070036851040c01005101050140600a9103015685c503a241c6c41550300c010031071130300400c6c00344000c2d00c00e600551000342d0180890326982890880c5003d909411580c0c00300560420307101081c00398000c42520301803084e685000b0f402d68120750070000001e4030b0303c078080200284802d000020400070040488040703080c8000040114400d4402056101c191030001c0c060200c0840c8140c3c09640a65513030b044981044103070050071034018040380e44c014080c0d405011a00d11005000500036010001c11001a807042004c2c3c00c560b44001500302d110754507224500a1003040d0004003254045c5d0001940007810040407032401720a01c100c801103501021041e5010761010007000b1311541c00120800d428030a001c000c210a5401c1071404e5034401c04240c0300145245c002c540503040241d00c604c1070000d0807c1c582614010315103840c10042456001c400e00c41400c0c0d4a030085041c500307151150030189238100c0034a103a02c2e91140e00545849c2e0782 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 243200467 1250 243199217 243199219
    0xc050f060d021b0a030c03030b01080f0f07031506020c030708070e190621050607090b041a0c0708030715020906040b03090a0213091403040b03063109020909070302011b02 75
    0x10810403c4042c1c009020701a00148a40c4440d08080000e0070014201c50072481864107000e1154144200049070401480e403000c0025064200399444140440182c0340d40c80b04115000c101c031001140c659004600c265020400703070100c408155440b0b115a98420703040c0b0850000142d40c10100382c421344650b54090403508085004568140e9031010034015030700c0d07400b480c8003d41c2024411002c204007480340a82112007032504074140d9042031100302240c4518880d403000a210001c016010300351050035208491403c0040c0d6903656502e2070b40c15103d600c5404122507890014103030113003146c0c980c401d4503504840a80440d0130141410a030341119170018083c500b851061000032070050703030748401a4500000203803020404034498a40204980c0094141010a0f00300f0320082c0080241a07050360b612520403105008010320b82c1030070202c3e9111030727005040d41000142844805488540007400c51910948064016a40d281029612000180070090005060800c0740c60700101c1c0c0c1462850080c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 243201717 1250 243200467 243200497
    0x2060c1e0c071d0105131e0b010201061a0309070b0307053009010b15030c090409150525030b031203100b0313050618060619030516030c050f060d02 65
    0x74561003800c1400b030200f424214200c0e0180b0040c416800d104100d00d00382c0341849010300000081d03001d40034500c14140042401700e07a84074000c140c2c0d41e06c01d400c002c00400c4940d65900c018402841701c03c810703602c1200c0940b154840c1280002e0011f10340e0b0110ad03c2a0041c0da500307800e000d420221807401402d500b1502440f0070940c0348030703403010b16069401703401080104000a0000300310414045021039010807071039070f107105104105101a028048640a02d800c440000f4081800d103880e000b410344103480a200c5900d0101086007029a4422100c4840100082458a1404544124261407551503c1170f0541c01c01e84103229090039200c042c5820494642c040b8020035201e2050340f800d904200c2d460300041c10351b050382000340001889a550071440701340240240c141460900c594480c009031209019500000240c41c0700003c000e1524051a80301d015a4014415403407202a40d0b0040d0005403440544801c0000e0245444401008010005005941080fa03c0481c800081d0004505074035400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 243202967 1250 243201717 243201719
    0x10b0a030204080607090f06020a110906060f07030201060e0f091e031b030d0c0c050a03050706090803040b070e0103051e04060605060a081509070806040509070f06020a0302060c1e0c07 81
    0x41001e000744c500c20788031551030080c0d00340713002501e0114442c19844482503400c82800000410510403188c100030406442142d00b40e103401021442c01e00c03640f130740304030507041c04200c501c1099419084882242c01d280105e030300b41c1c4c4a01e400741d080d00e0b805486140380c0e07521201343d001044101244400c803120004068034145644c0604560840c14601250107064100003001080c50660f0311544a0402c4030380b52090300d04a60b1b945d0281e68403100f0034081c0c148070011400204209180c4c00403810264060f074407071f031682000d1900d50107280c01070311040046450030200b025a54070901c5024400d002103404504d0640c2004820f10403014040e2055982c10340300c690108141d1586001042c22460f140d6070101c1c3c0e850f0141d40002002540c10340c65200740700303000034022240c1d0700c80b00958000300300300e80002c2c82e0b4550307901907803810308658014030825140d1100015082d4000c1444100c440c06034003038900303560b13420714500f40030700c81e96920900b0050340c0b00d244000c194049000e0440c54154004448190b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 243204217 1250 243202967 243202979
    0x31a03030301150810030203031605160b0403032007151b0b0708010f14040525020303010501180e0c0c0a06050f070e0108240f09090d020115030506010b0a030204 71
    0x1940240c20020441d103000070350080d0684c1c4000c090ba40461806203110102d415680026280e12402c41d46660840f0014204018854140018112405202d0916100980d58100304440707030014481580400c0e80000e07100b03106004460800c07002c0603881c0c09804c400d41030207040251402c40090a004102c030540d482d188441c12580c03454503442c01020300004a00e801c0724010950714058100d4045442207100400c186010403403d4043d4500c1243d02154960b03486001d50440030071010803204100301000000d044940110040d8141e54007a60341700901191109090042207032403003003000c4002000c3c0050528428000602000b0b20f501d41034800954003901c1c3e0307500f920810385118071001096014000c1c8260090f9281300c0011003800d00d0b0b00185804c81104900081c0c2c2e039042d41504001c085080815070b51187e500b100c04000a16010083c02c00301865507460b00911580d401541c07030040003001b81e041e2010045d049903030040081c5aa03038240fa4129000e500101c0c11001456006e100110711 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 243205467 1250 243204217 243204223
    0x907170c09030610030b1003050307030509130f141302060702061b10061d041101030903030b03030d1d011404080c0106170d0206011e09020c030408060103140c0103140601031a03 78
    0x1010300c8a034804045040d810f00556151b8042d115003000074242a00b040020300c044151100aa01070901c562290804408111520700c1032604902d00d0b4035005000c0880c508a900030384800c6222807949041e581c0715010f007000303100480e4001c3d61146081c4003090051030840c00410100c4d19220b0050300f00060b0420207454049191041c49009072120402d114040c5848680c40c0c0b9181e0601c1030044904094503160088641c07031460031b0415450745008030074075029801100c10420042e044950700c000207034400c0024425441425082140c1c0504044044014007602001e400e0604904080b0b444940d24080260300c9a0101001952108030020f08103403c2c4109800c58400d10001e4031255880001c003d0a221050704280301d0340460800c1d0002d0910074060310400e403140fa010041e0380d8102103503c1842c5001e16030001c00240300748000030003004040005d26041c1c80001c402c039449013103414015010744c1e01034200c4000084c0c00c00f000510a604c00d41008040259002d040c0c01030049200200341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 243206717 1250 243205467 243205471
    0x10020c0304090603050a06180308060f191d01080a0201020c01230f030103151b050a0c0602030711100509060c030a180305090a08010509060c03040c09060303020d0306050907170c090306 81
    0xc05406c0350001e0700034440b6070302440d28003210580424200d112139a6000c0c1401c10050006402078640d030514142c140c071000068066000ca160f4500c1d801d03a40c0700706005a00c0c1201105103c00c6c6400700001480c1d45001031014480c079416000b92030f07000001801143c190302c42051407001d08586100801c11451400300406a02c0c042c00074a60341ca6040d0308250b41a200d035006c003083c4040c50807050000c0f0025030740c42524903011a01d05941da8030011740040341e1110140703102609541c400020f108140d40c00141003001800d0840503101541540c0344020119007080b280d994240e004036000130708201c5444015a8821080100025502c0a12209545440e5290781c1100031606c000f66900491910109200003408448024420351422068040c1c031000041d010340234007000400801c04105540c908200a81040c5d20200300f41542c07800d00940e1005000b5072480440d2a00c84003040c03c0c10906052031141541d0344503070072101402a8920040392000301090307031151003840001d00306c1d60305001c414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 243207967 1250 243206717 243206723
    0x90a1e030807030c17070c031205131d071d04020f1207020a231e0a050f03070c1d16020111070807120219030806210604050c01050c10020c0304090603 66
    0x40c841c031075031400c04243ea2020060304015002403208500098003043c6010680c1d41c409d280701200743c56008142d810b4021802e4a1404403000280410348100e01d42c80003c808039440402c103c103440303003c0162180354500b0960703080f9500180241c6a0390a01d500200100702c201101e107072528903105900445000180d50420068111140100030700000c5044012051607100583c0c400152203205a41c0d282d4800708040b4a124020340002d10092042c800910502e0304002a04c540c0210b070f070030468036507001c2c3c0000c50350201d42003004510550050144402c480308200c250b4010344a03228081009800d0018034802c664903806030008031060407020b01400e91280322101c0e1240850b1034441f4280f40d1744004035085601500034507503401c00d0812504bd2003a09402c01070b01c030762102804559040d448801142c00c460b50200d1022008000107421031045011b44180d03102201c1801c0116940e208134403c1030100c0e40000606401c040c46075004111400f80101203a1400d0755880b5800281c80040d4025 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 243209217 1250 243207967 243207977
    0x170718091a0a05010509010c06060806010b0304060f0203040b071211040f051503060f01050d06030606180f090b1602010f0507020c1005040317030603010f1d070b090a1e03080703 78
    0x180c008003007154004001d00504a900444090906000801a01904c0d070001c2c10040c0100c6440240b10983c3e000c0c4021308211000c0d21519a142c451021295205940031605d46240c5203034500d90150910130307039001e03d074032401443c90380e140c043c400c6803201600703076020750100d03a1603491084003200c02006200400307a8003820006c552410080000c01004244c10b030145590410800c40b072035491100710003140009017812500c604402c00204003c0442d07401c018401450300f00045038054400c9046503485440d00c6080c04080c40300d64404c000d80d04400401400d107041030022a01150322905401d00c1c031030080c0b0001511680c0d080915040d944150340040160f040751951000b00e052688813040560035604040746001e18603950400a20b20240e01066420008004034510f0340c4d081d08968216802140c00b0311030015800d2000d15004548600c1300007a07c164003000410510500c140e80c03641d05d0050602e0310341490940014208a0030010000c16601c0c54035001c0009034807000544040ca0180d60340c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 243210467 1250 243209217 243209231
    0x40803090d03122c070812070c091a120d09090f0e150106080708090703030509011101090b06041d03030f0406090507060201060e0709080a2d08070b13020117071809 72
    0x244410302e6110b400129258101e05c0301488820750010f00180e0700344030040b2031983d4000c0b509040454080d260000f00b0200e0400d62074a04d070729005050b801d2219000c456a50b8202440e0100321380d183d003500e49000c04a0308201040080c0c007100d41c0014004110248041514206c04c0b91039400e020303107041b41440381144800140072095010b803a00fa4003030316a00f80518513040012420b540da8260384401000c010001840f807009900c203031403070303424040a40000d0000100900e0101802c003011140c15008a1500f82401d03140031004041e40713826400b40c0302075441d41d202c4411080242000070010340d40640c88000300000500f0401c20f017001804a03a00003d842410304518286100002d880f4908100b20f03d58240328102c0c0100700340d48181e42c003c0f1024140080048a0800c0031481e95108035061003041405052000000050040c20700c2601014140d40d5840d180040e03070000c1d1903001c4d0014005d80408502802c4000c0b035190844600c0c146400c410150101e00c201400313850708021051915a12 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 243211717 1250 243210467 243210521
    0x90606030b0f010608010b03070903080307021f1104030303050408040b03010b12011a0f030901110307030605030c09040f0209040302010b030610240f122a0212040803090d0312 77
    0x4881908080c1c1080982e00d1075141c088002c1031a1410b000300100210b000020668941c01403008070011580701048540701d16182e18040c2d1250703036048450022020111407402e208282e44074052201090700700b010705141c20768400b10001c1c903005008031000b44003044049a4040260b018500a1510710800e90743c40555090f030030b50120040e032015500c131281d030091821002a80068500300744c90300c1a0f1031740b2613a0b0f41c00001d015009900019500000010a010055616820840070341d502502195054041102405400082128007801c02c810352a141c40061030700a0009801902a00c00072036400180f41c002030030f080d010350b103d100c002c800d52401c01002c2c0c68031300c07a00141d800001d0b94007000e0030060805051a404600f43c84c081000304414031888100036406000300441c41c2180385d903011039200c140140550313100805400340c800c20307003546995220441200c01351404100039500300303103d400920003a00f00184d41181840110070304054404490300c255003140344540c07282c1124002080c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 243212967 1250 243211717 243211733
    0x703090803030402090a09082b0e061506070302151f0605070213020901030e100212010b04030c050d0f0206030907150507051e0307080a0906020714091311030109060603 74
    0x1600c03203009600144104409070382c034440700c00d5101541c0d05c00031a08000301e24203045c040c482c0e41000141e401503000aa4100c0074100c20f03101c08020180c208001c00c140514407190b1707408003100d807044025082501c828241c00c2a8000e4800d007846801200e503600b070380b40140c11400c01e00301d031868250030160b815540140c4480810030010309081c07c00600d003c200d90007060000300100140c002064001032440c055922980c1300700c41c50200a415540b01c1d0144c000140301a500007150340e00c105c0c02c82000840d403890b1001c00c440071284d000340b800380700e1480c1c80288024101042c209079040c00d0009a1000540c441100652090315904040d0120070704060301c1d221030605415000c41080070500402c1c00044000500f4050300b407041e10700030b48a00590808500d18855103a00510405002c00c1525040340c100d000d0501307403040c075000c0e10301940d100d08001392003000e5198a03650085041e0007103042c0802c400b44910205015100c040550280140401d0a403003031000220360655644004000344905c4d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 243214217 1250 243212967 243212969
    0x3070606150c020103090c120803041a16140f0408030901080c04050f060904020d090503120f06090103060b0d081813060f0b0a05070c0f0509130b01140f04020c03070309 74
    0x6a00041c0c641070000c0140746001d000c000905155a400110080c0158001c180d0000c0003560031a0b80003181a141101c520380054404950103a132268842014098000032684299074580c4800b203044100002210110142c481c0215010810401981c0d8030400c1e070000c0c00601621402541d840d04050001400300c0b4000b85207040c00e80007400280016540e0781d030113560b1444201c4e003154984200600142c003c1c42250201c0150380d10b442510000c110011015040c4005541000302ca10f035105036401c203034a00c044a0407503001603c0001440010b841c0d6000d00d400c80409001d42c2100c1803207969000e481d40c0180e0340c5507000e01c142010722002d03240c01d10021548025071101402a03528005c4025812192406003071181940400e210014034420020f0f60311040d08021000e4001da542c40700744200003d64010180111481070010342081c102d080c0d401c08030383d400340101e10540e02e400f0381041035040491751568445c3c0f034140c10300301c1551345d4009404904100c001030b680d0b40a01c1e150240c50442c03d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 243215467 1250 243214217 243214229
    0x70f03050603120c010b060a0c0b0a060e0a051e040308010906081902090c0d020f0720030c040e0708100501170f0601060507060207151406031902121e03070606 70
    0x1000d00304081a1008601460196400c8190310303100c8110f00725180c050444000a1750308040302050f442e004690018490f001c4d0350003007903082003584030480e400054501c6401043e020040410114001031050b5002ca50f003c800d02ca00b0394143da0b02203d0301c4000074410b55007600090410401403000440a200c1d1305c005100c1c0c85c0081040140034840754010130103510b4003078440c58441e40041e060700b142c2c60841d03003103443c0802c0c00c40d528281e25407810f01d580c200c81e030183d400300c0b40000200072044031007050440c0c0c120010700402c0382c18070300c500300000f806800d081c0041d02d000700400041e0005081001042c07540d1700000110341036040c5007041020901c1703c40c0608050380310f1076124801c10400718610f8152000d51401d20364811003810020040d22403400001c000140c01c03405007521040070740c000c1412104589898a213a26448201942d4000120720407030324400060100c0014500300e071000441c100c00d00d058400c81c08080301c01f1003004042080f200126000080e841c0f0401075544201030240c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 243216717 1250 243215467 243215471
    0x1406041d0901060f030f0b0a140103051b01050a05030f070915030207140a020907080703090c0b0a080117030f09030c03010615110703030e040e12031f14030c1003020403050d0503070f03 81
    0x110350348481b1000341088401070121086c06002c0380c10301031701d500003199201425060352115650b03464076a42c0c0d8010600c0307451030704003500741c60022903110344200e404c01d04140d40c4031411600d44191462220b5000f03000305051084480000540c2c20b008034030f05003500480d4600580300c40303007810b2a5802c031050080d1181e0a802400c64200140d40321000e043d08401c00d03140c288040d81c0d401d40f0540080c8210600038210030249000000c4a040c0c1500800c0342c01c00759620024280d9845030f40d101031014079804003d0640090200b240c2c464445d00240c800c00c44001c0c21541c1800313120011900b102c2c900c4d045010140100d003070058095030001c040e1012024620010043c03a0700d140c60081801d9180f48280384150b40320550741c0041b04c02080180d082c0c1c0f0b241d1741e05550301c0c03d01c500c44048000040440c03d4580340c0e101c600007100702c02005034006800d00500a010140914010040c0c03081c0f0740c03062031007819802d00000c00402e07820040c1510700f04442d100c87d50b6a00b009013010b401407900068a41c1058 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 243217967 1250 243216717 243216719
    0x1006050315010b1207090f0b030117060403050405061602150408060c0a0f1d040609061403150a051306020a02012702010f0509040617010f110309071406041d0901060f 73
    0x1c106000f11000c0381e9422000700416120703041c045540d805180d01c003951120030410045480f648e840d00540c101ea420f2441d1804007041c000d1392030b44400c4122405404200140400c1141d400c20700d0080982e14141d0b003a80303408007541e80c0000c9110001064104d2076107030201c0e052110f0700e41007161035084405015501d0804031044c0c0d00401030f62880c0d042404000140d203055005a541800540c407500c0020400c2c8205034452a04000800c82da210b20b082c040c61903078622015090101e808504044e00010001460f95000e2055000e40b10150a10400510181d0100007140c22480a8460305460380d0010904040da50031300c0300d40306406110250701451030152400180c0c0c02440c00d00d400d00040c1001a200e21110000400400c520751001a170040b0240c2603000010040d4007100e26040c408008001c542920450885580400c03038001c941603000200c10300002c207500d075404480e8072004201c2480c05031507034144003034890401282030054036880c0c24455064028003a4a0180924195103000c20b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 243219217 1250 243217967 243217979
    0x10b090a2f07020f060f030a0902030106050604030c0e09070b0406030b04050106030612121b030801030209091216171611030607050405040207060e010e03030103140304060903031b05100605031501 86
    0x14416988003d103d130156036a0b40d100c41d1510740980b2800100f2440040d2039180081d00e242c0601107021049120703500e01807000c03540b4a0880b00780c03001d0700d8000c0c400c0c1918909281041c1d5800602070f1540c000d910409100090340c14007040100081d0041da40c0208600410340240400d0b10701c180c1040e018542480000c0c8084052030850b01c1441340c11012403641d203c3c0c0c241058401c4040308600071203840d68140800c05064102a8035812a4401c0c0c9101c08665a0041110b860f00384100e2a045071641c104490f42d04541d103040860700007405499503180c43c9d05040d1010626a0240d00078103030519409031404d040c01200c2e00a0f40146c1d8040e4090802d52405070350043c030501c118000c5e40d10a13540407800006200c05540040c82d0178441200070010a1141000d072662a08248800c40d084118006030b409038201c00300036a822102e4540706c011400307040d82e4080e1005905c151803418090a0490b581c80814410400300d1a615582100043c0c110306103003c4c51305003c80c4091403080801910010000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 243220467 1250 243219217 243219311
    0x10b090c070b0c1e0d0f0e15010e0402060301050910052d010f020705061e0403031e02070602060708040602070b10140f06070308130b1609050409150e010b090a 70
    0xa040701341c0c00c0660342d54800070103440c01410052506c0c0600d40c034240d035052003414001212901d06210b091603035442c1c0e031790300d644c011220401c4500a4002609000411480c104041c041d40c00070560820b811900c1e454902155840800110304100a01c01d90401540c0c401d10003800444910286000325414840c46000395a500b80c6100e0907000e54800074640400c403030103403049080c40002a017000d0382c2e03d41d00d090052518800c8201d088645090403101140d507800015614100d5a454024000a5039551070640304990000d0040c0e80c0a0307000c1041d01e00040c001c1c01c0303440c41500100c140303855460034240050185925900d10a000b6400c0d0303082100b10390783d0641a14442680761030700705c0c2130307030f880c0c0090701550740c6070141c010401c940d034106214a010ba0700c0d44903051a5a00e58445410740c1d520010002586d014070009466000c104103c10448101600000069880c0030004509461070001117948031400f100e200e0490f96440700d900780c00941010441c031030341d001e4841c0c03403844c0b2000c0c4402c800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 243221717 1250 243220467 243220507
    0x90903090d080f0d09080a17150d020d02060d090b0601090b03130c080f03030f1b07140304120302030d0e0c01020d0e042009030d08090a02040905010b090c070b0c 71
    0x221102002c10301e0900c3e48400c100f1100041941802800429020300d449400d58000d05907540200706000180b85400030318004080c86100105828580524180b0074007001005c4404241e81040700b40c08582d0250312010020602e510030380c5030008a00f11581030240550788040c084504203d56642d0410082075454256600611a0b800e442140358803498485e00d840080c0d8000c0300b10f4000d210781d8180e982c1d80840035510920007000c501081d0350b141008000112030b100d0b600c42d203140040c062000850118000c4850342c030041400c4078602500d90b41e800301c009d111050102c0042e400080c0007200b42505d400b81c0c00c0d900c80502d008010088081002035100e00b1450410800c0200115007481d070341d590f40c1c10100c15112a02d10316100b506c1502d1300003a10381e00440100e8001d01c1503501c0e00302414492800e440c8038681c40c1c0d010306144d18481c0c1c02c00c405803070040001d4031550b4803195003000a68424400074025490349416968519103443d10f030034280c0c001004408106030600c944600b00612040e001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 243222967 1250 243221717 243221723
    0x27100813031404151d01030204030f03030c030905061005030f01020c0a0305030703021207030219020c090703021602121c030b0102060414390402040b0d09051905060105090903090d 79
    0x1c490320030503800800b4640101d034002000076216143e031260b540d07001614400c0c05101c8488505091545000540c1a4401c41c84000c0490200482e0800481d01c17991040341c09400c41d10307000c21000603070303201c1511b02a0251002000e407901c14a04000915081007101000c0c98001d00035428410041411512203081000140c02e000d4000001107006200354100c5d20b1312503034209601054102298014000d411507051080d840da0540101c3c0d9409000195014051a005103010a16520340e0400c81c040d4028078021102d40220f40c1595005a880c07a200d6400c0203000f4005005408007040c1c48440e5611222031901810300d05580e8100311b99001c900103612941000302216070340b020051144c0307000c10014141d80204004210640e4428182010030300004404c13252070b4a00c40d02108100892142d480ba0711503001042000c5131038150103800c0010a0b40c041d000769854140c001108009050b0080d00c100c07043c3d04044014815403602101c45908021070400071800e0500003408650049941c09000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 243224217 1250 243222967 243222977
    0x5010302030402011b03020c0f01170711010e01050108030a1b05060601080601110f0d0306091103012d0b0408070605031e100518010906060e01050a050a0201022710081303 75
    0x82d09590144640340308190051501c6114800d46003402900e811a00d00181c3c03060b220000b4100041d8841c0d9204502a4552500002c0d01d031620f44040d02c400b000c0d40c04c0c1c0c400654a0f0752181c108040288103483c0205050030103180d44030403036a40140404034082d80d0700d5280620b040c038040864400141240c4c4042c003824900721607190000141c42400390403450300503d20070902d510300c1c00080413070510360f410403503201840480d4680440710103407440003404617080c40044c0010440c1440d04219002490303c410400b8242000e004c50301d100d4071f03005402c0031412580c00a800c110f50401040070300f00600140c6003203030450900e950481c0030000c00c843d09131020384400c80882c010380d0100610760000c1c040203001007041c3c200340485803a084024030030010b00c02d00e03100c40060450f01408881c0c2c07a48030141d58082c5041c450200c01e42ea0b036000403007620110f42d0300b480a500482c0000da035103c0390f007013400300c00c680b1600d10000708810300341240d80074000c2105100902c40088070380300e0301c101101d52601340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 243225467 1250 243224217 243224221
    0x1306030b040b09010306202502060d020f0304030908011107030c020307050618011b080412151802030f1209040f09020405040b100b0f0d0f0213090b0a090b06040501030203 75
    0x10082c142c0395100560200524000208206803540b01074511540302c0da8600b40440392481042e0301d800b500d01b048003075007031605000b044000c00e600700c55513285c4000c10490a003a10a0020343c1241c1107040190741c60361000081c08141900048140010700e00400240440c043d0640a0700d058001ca120003802c0c4041000d00c2011542c09004440142001415042d19117400380c00d0384a180102d043c407280841d01c1940040c05100c50540e0200085801c0580b2614080c5052881802502344000c140c943c075201c1883c1962101e042c0c01820503410a2014178041700c448d0b8010142049414803513281c150303120800d000d200b08107030029a092041c2c00c0724006401c41c034001c2000c0c042c00d00c03460001d5010b0320b408100010401800020740c01000d9211100707800729102c45944c07040d80700d803010b1807e0721902440317800400380c0c07030f1340001a41c10050b90380541091500141ca1228410540020f0381c030781d440710f50701e03506800d000001c00010702c0121424010700b00520f0100320184a00d000d140e0408d500000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 243226717 1250 243225467 243225469
    0x122101080a141f021b0a150f0506030703030e06040e010f0e0c090a0312050c0307261c0b011403070f0201050705090607120314180111091f0e0307060815061306030b 72
    0x80040042e94241954084100d615101c480c10540701f410011141c80c0408070070f116113081c4078503480b5407c0a0b00815845007182c03810f55080c01b070f0301246980070a0030807021680c6410148020300034100751440d01e151a0802003c402c4640009154205480b402d00c002c0c400395449113440000c032904a00c1c0030520200018003142c00d84504516460706100c0000c18100700302c44a004000000d140c060100c0302400c003085e90340500d02c10035982140c0b00014945c00700d802500b0f64054248407c050402019030200e44100a41c0e60700200d8102c03002c1804284007141e10b50302801070752785c04051403030150f15040310000065001d01134107802400442c0256001d11500d030090f4001481403001500425480c075003001841c030781150107108a000c2e5402d044000860650410949416400080c0303140190070305401c5001500b0f40c04044042006034144441c41c0d1034806108007005043c4603030b10001c140ca07159043c20505807100b0b4540d070203500204000a0900846000ca90943d6280c0c5004201c882801d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 243227967 1250 243226717 243226747
    0x200303040906060c0c080105060105042d12060c0908030409020d0e0604052817090406150c020405011203022e11070203010b0a08122101080a141f02 65
    0x81c001514442c074004002c1009038200c0d40d040c06852080340c868002c1c90f00c8003c0c4c1800d03500103460440c007040090005000040f50b1625001070b00f01c49030b000607465910b001050450981e5540032044800608800c40709000c2c280c000c4d203a048110f803e210204901d000f010b5070b80c0c0c0c03040c1e00c2051012503002c41c10400f048000d403c00d14500d4842c508864441c10241071003a25000000c5191780c50124070052240b65141150514000301e0b008005c54404e240d41420790f400da5449414107940c001d07661540417544108403001c10102d04516034800c0005c2c5146d00c148002c03164180c1204807810001c20690300000e07400680c0791084c003003118402003860003e0400c400703000038400140034814100742c621042030001c240508110f070b000320002c0c0308504209060052040460050700c5441d00461007803107030710302c140e0000c0200618082e1200c40740c0007400d0350040c4060080c1c001101d540c10410040d03040c460000e50b074192144072a030241100b0610043d10460309110b03d007100c229103801040d0342b0501c120403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 243229217 1250 243227967 243227969
    0x3010b1c0812070e03211b1603211706060714060c070308010e100b0c070306020d0203060a050126040201050d0f0c031a0f0d021f050c0c0d20030304 65
    0xb5507210324182007071a405084030314400091402441074514000344e40e190301d40d00c2d0000d00800061a40f9000044840e01000d0f084a40f0000d064481c080100e80d820028580c03042c0214003900050304201c00f5651030550686000d2218010407022801c0c00d9041c0000310841d6400a00c1100d0071580c03403036140707081080070031007200015481c085c1c403003041030b0144204c0c005d04a00d840b03540c0b407600c01c1e0388902c00e82080102c02d4991460842655005100700c1c2d414000034200b0350303000c1c0121004265a543c5110599004581402c02d0325004000d00129040658451025000900300300c1c0307a20041d00c20040c400342c10201a4008040c080010030196400307901180d041c4101282c1c1809503d4a07115a00c014040301780c40c02c80040d1500b1034108030703030301500c003a00e003a9140101107542e80c42d00390040009e012108042a43d015807041c2600c410480e506800b00209041502c1e281c2e100c3c14101e50050404600d52016400b54002003800e80001d1b1a1001c1a0719510510611000400048002c2451030040e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 243230467 1250 243229217 243229237
    0x30c210e030406020a0c0f270b030115031103010b060d1e11030f07050301080a150204081c02010501050a050603010902030406090507060e0f100906050304060e030307030506010e03010b1c08 83
    0x80064081510f40c0e000ca80c0850172070090200701c050903a60411114034640a203e031108280c0201428140240541d05440c00003041d01000f066001c41c03440020708440d41d01d4040503071000202420010003030340a5004508102c00c6000300f1071010b117940800c00c20b11503e602c00720119500c0d801400740e5400b81c0e2248001d44c0c000c50040002c00c040c218101e520768003c2ea03c0c0c1040c583e221300000c0019100b10b00312416112450041e10681c403c0350f481a001642c1010500c107119020f0101140e101c50801c0350360704403011145010121000b9100103401c40784103800c82d0340903c445900520150311414200c0e0b0454034411401a03890f6543d081c0340008100301800208680280600000d0b69548a044a05800303811116400901c410703c2c100902c141182c511100451690101001142c2c080c0c005154428051200800c803070800c00071290a69104842e8200800d40e904103201281d644040b000030060801c2e070080040e8070070301c8001107042480401d01c4440030411422281000114400c3da80c51841d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 243231717 1250 243230467 243230473
    0x110102090603061c0f030305061926011107050105101202060702060703050915030105130b030a030c020105070f0c0f090c0e061602040906090b07020601240507052a01030c210e 77
    0x500b846c004001d80710a50700c0c280308000d48034070b1038081c0c000b40d844001281c1c28200c00b070707610404900e000034403150b912851094a55030380706181e4010103000010132086124800000d502e182c030241264911989801803020ce18011030390000680755441110400f50301114802d0f00c82d003503860204d40354402c0b241d8403900110808044010041c1c002c0c0918141e510444480c1c002c0f110598500c81116100c00045070f240d440000b40e2404a401080e401249a0041c900385143c140e0589401c800003441e1702e0100c1d555005880e040061101b015420000780a03010000e010580d07001000401d03018600800511428001840c000550501e5101101881c1c0c050801d11a1251030b080240084c111440141c0d1006803420000e24107504c0071032882d050740e00380852820101c0c500481500380b61950598401444002c0002a000c10f0040105490302c8540119440302c040401082207591044407443c0c606040c206440c0d03001c5607802100c1054894201441382204021040d80030b40504100003013482c4d140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 243232967 1250 243231717 243231743
    0x18120302070608010501030b010c0807020612250c02031005070302250c0b0408060a0f090b09060709080105010f06050c0a06020a0c260307031503060e030a110102090603061c 76
    0x1540125050080b10803984450007160790310001075060740c9061000c00d0000b04851001350000f80e000c000361903032074000740c807542c182010070081500008050f01d00403100e26096500e02c41408620960050104540c03030841c14044180c1d000c43e0740c50711101c211036100c5403a9400944468401d030f040c3e40070007903000c0420244005509035031106a8042c402903c841c1c0c00751001140c0924004100c41c216403800005008650b1400c000000074130703207a5080d601c40d81d22604c000d0085820406240c0c012103003000580740500f0f2500c0301400000031903003d44000c0c1d040400401180205640304002c40d42d5509125076500c002e40000c9080030300b01030004011603c04121a000b2640c080d243c3c1864a00c40e02039200c9021003070301038000000c840c0080c031482e10410000103405038440c0d0003400b640691170000c0030001e9140d175114020f4401001001500d035101161440e500340d8000f42007a0581c8044d00214680150b607000300d1003a200003410036019081c020700a485030a00a160768100c40e0b04070310415100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 243234217 1250 243232967 243232973
    0x11d4510020406090b031b0a14190e100503130201020f2b0903170f0705120d0c0903020306070f17070f14031303030e0a061b02011407020d1812 63
    0x80d0001c0c00381c10009130502c1008200c0354100000c413805800294a54100b2448901e400d0b03c0300e91048501004105200682e01085199103004d0404400b00d50103c148940403584010443c41c403c00480d072082a130030745403190503508072003200c4d00110309810240c8640306900050f0f00e0030b0100d418034280b17407064a4661280c0280e0f40303a80040c20301e4a02d11620b203410040d4080b5070005e107902024100c0461180040103005c10007005150720345c80745039031500341f0034592542420100003d000718240c840000340d00038a420742d8841c0c2e00c2c1106175410505605801c0d40c010076556040201040180150000300e0448640a8085000d02a5607103881c0c0740c251500307590007402111980b0200e004960803280015010340400e0540f03110742c0d12030351540e910380038030f40b4100c2c007030802140b54519600640c5d503a640410114010b500324208091071381e02e01298480e030000e0840381400441411042110284a078a030b40c04608a0826125881c0900070486000c500e000200c0c0755a00400204003008250b01c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 243235467 1250 243234217 243234221
    0x32e030506130501150e01060305060d080c101d0606090916060207031133040801090804030b0a020405010c0b060402040509190e030a050406050c070e011d4510 70
    0x10741403040c4000c0c080110641ca0018650595003d040008011b220050191500c40e60117984c0c0300c0c01c01000c0c20b205140588802c4034030350081c40d908846070416010840b041003207004038290980b01a400d80000014000e140c3d4452001a09080c464800780c408078100150800030318803500b64404004901c039980c0c52010b035071030321144070444981e1046204c0f0403451612030302c071200d900d9001d110340c1103002c01480742c3d0205424039010414202c20a10000c181c0350424070800e0305d40c9103e020920383d15411405c00b03c110b810001e0290303641e140100810710413668840c60840c1e185602682c040b8090711400f001034041e000390f0300620f03013003102e000070015030700740010010230b07a800203040c1008100d0034140e84544910a40c0414004114200400c0010f280302d5402000804208000d50784040e44902d0344c0c6d0580c82080c0e0054800c03840c0c01d5a01d160440342c1c844090b400c0446c1e410340c580120f016419149010095900b400034901900c05601d9000b0310040c00d400a40b44040c05807032404640502d2440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 243236717 1250 243235467 243235501
    0x200114180409060509031b12040e0915180f03090609010c0f0501180201110d0e010c0804090c030c0f0e09010603111309020a030605040501030c1a0c160e0705032e030506 74
    0x1f0240060b0311403900301e46d00415030f064020640001940f4150420101c40d01000c0007038000951482668902c910107255040c489004040452081da40d540901200700e250040d81c0328140415002000720340d60a603502c1c41221101d80c02803c0290707100d03c00b4107000d940d01100302070140195080c00104030b14944541c83d80c0007114403d80b01c8900c9110082d4043d5643d0b8184c004800200d060b0420319a0b40390301405204007140c2c40380a04619083d240e40f100700c1525564810fa074040fa813550b1000318110303000420030f001a880c0e8a0400d00042c3c8003000980c5884040c4140030074155101d081c08860360a010071500c80101c1480d01c0f030740310703556006007900940c007902d141c00c0000e00c1c0c0000841c81e85000d01489040300d8222000407031071790402080d40030030500031010305042107080120300700040051000640c1d02002100d4a0502c1e0720b401e04051a43c403001704070004100c410400c00c07000518102d6030000800e01c03d580354011082040310380039451800d0300082c020b4032951040161101101007501 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 243237967 1250 243236717 243236737
    0x1207050a150e06150409050102070b010623040e04060b040212070914010212030705040f0b0901080c0906030a09020604050a0b0310050405070f030b03010b0d20011418040906050903 79
    0x2145507036000d403500319801003407040020b800c440082a458148003d11043c1d003e0000d1000a0050469607003d0072a03004d640110b03004400000104400ba4000300724544100d41e1038580803942031108040c2d80caa2150340a407024054080000c01c0c24001c641d80000c0c234260019000315038a11041e18602c0360b2200032201e4000080f00600041400c62102c08040d01d40203040c7c00416a20560f41020038464100504420411106000c000b850388010b200d40e5000b04440050140e85601c0440014240e000c01086100c800c0c0c020844040c503911804101c03a40511100c400044580c55840064000e10507640445d13840800b04602140089640c8010740c0039a80c3d8404105041e03030b5540c180701c142c2e40b0896155000c200f540c0c01e9041c1d4a40281c01c485c2c00891300500000340704840fa4000341c2103030202001501c01544010b6800861140c4070312003041e181003424000c0704207404422010091103000c2d00c2c20705100040d40c1c41043d5031030f41d40105000b0740d4400418451840d18040c04c80d9070750030600d905 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 243239217 1250 243237967 243237983
    0x80706020a020f1c0e0f06120403080103210c0f0f0c080309210d05031801020a0c030e09010e010b1c09051501060c2102150a0b041406031506031207050a 67
    0x91003602000c946090111022622443e05c400782e03030410000c444d840c1e03075850f5400090400035044100d40022000e442039100340c036581150f50450501d0a02c030410002010030105480c146030081c660446c240c41040c1b035000c485460034181a1500404029910388001c2c400c001814012401c40c0700400038018029040c0c6104c0007448081040e813551030400750b0300c01c00d59001910022043c5106000440e480b401541c0c4141035080303500d16940c2280e11640e02c190001d501e1480c0c88081540c00401d00881120032206940c1c0c035410030605580301801031080181510000418902c41c007807202c1c1601030f040d200740b001c0003e14100d0800b5030329018a0080300809058490000c0b0343c4038000c100d01146240c07c00c4030302c4460340305d401403064807080c2045c150055104003540c50100c0910000307090b10440c1c03052130110ba40105c44084c0301c203075590b1b0034440c00752918600410107035440005100000101c82c1100c103030941c4900b00800c0c1030941d44090403113030100000740f43c4244072000074400c40b1613101e1056 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 243240467 1250 243239217 243239233
    0x60b1914190b131203030f0605060a120209030a0f0c050108071d011206080303130605150f09060114030705130e070f030c030b0607050105011d13030309080706020a020f 74
    0x1000140010808121940d1507071060900030780d2031030000b414010000d4502000001d8691500088458072228110006a1295400031291065005001c02420705540e00d03030600e000c00401038900000304e00c074154903950100b8680301c1542c3c1009002c2180b0b030050030b03485200041d0300300f8003903440341350188034045502100401c0324503109486403d101403101448281e003140c51130045070807041090a040b83d858540c0c20210381c2d00b200303000450043c2c080b4030344420458036528000b802d41d400240007818891605880e4081034031183c0d030071202d16404030341408060b616400166020400300142040c1c17103101004000090b030b0170400034240e605054400380710946e034030244d02d220003a0480f101c40000e02d207030401142060007600590ba440302035042c00302c1c50740045008100340750410320b41518103a440340010042c400d600c00c2403c0f03143c211002c0410300d500d4400c85c0e0701003a20b00100002d04140e07039411410b013400340b0071041d031b41402e50060040d985d8444600000359035081d0a41e06034140d01070001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 243241717 1250 243240467 243240469
    0x3270308090d0f020604080a090b0a020c0a06051602060d02040f0e07030f0b010516051c09060908030f0318010f02030408040e090c09190f0f020307120905060112060b1914 75
    0x2e10f482da14070f034550050800380d88558a13118a50050094841072092540010524800034005025401340540c01410b814004d00704000c0e0480c40c0c0d030320200c1401820001c1c011300000d030b50070250441341c059409594461004080e0030080c41076a00001c001a000034020a204599411140c01180260b800703001416680402c1001c9903030684c0d101d40031800c00c0000100250300b080070003200e140100c0940f0b20072840700c1e001003008110011628001138044009101d0a60007103510005080414000c40c100406e10303810003a540b0001c1d0080c807001310028010707074102c00250003003016400d02c4141507484e82001e182400c030a400900032105940d04090015440480008040c0c4441000800011054490b5410a4a1200790b49104011a6107480700c10b41246601d000e07104502d5400440160b0346d00d400301008002900f5805a424202e0502101501280d40022240c0c1174032188007101014a00d00e00d442c60091840818094001c000e44080f06030125801200c1400c0b60342c0403a61410641e03a607c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 243242967 1250 243241717 243241727
    0x8160b03010e070c060209030706050903010c0801150302090303130905010e06010c030e090603011d0a0c0510021b040207060e0a050705100215100b0d0209040b04060506070303270308090d 82
    0x4054218001e42000015002134400e0414610040c020b07030f00180340050b0075000c01d00745256070b04040f010038000140c04100341000d00c100c0d20a403e407841c0c566990350400031102111008024141c0400d60003040c250402c1d6401d00440d40c801195100d60007a013947c032005a800b81100340b040c082c414440a0014582d5401640c0751001140e01d1760b82c5d0b4840b281101c0800098100148c01c41e60150741e00ea030004001441d50b5012044204500020f211014103803400842000d01a0080c0b80903c60040c1e403040000e0300096641c8e01007640c041d42e1081c05410f4008100240108540a00300c1c60030050304504071900407a40d4801035010358282d0b0b10f036070b4883c024414070701c501c0b01c00000160310201ea00f040c020300b0508450b4114481800c1320010726900c1483c000d9a8000c0001189883c4c3d000505511078601342c03240d07458002040e50184401c0749017100003602800f4810000e410b242e100c090b081616680030080298801180c00300c4400f858080c20002c0201e0822500b0041c43d01c03517030b481214218066 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 243244217 1250 243242967 243242969
    0xa200102191e0e010f11010f0e15100302030a06090516140a050102011509050604090b09100501060c020a061101060503071203030b0415031202100f050402030606010801080606011112030108160b0301 87
    0x10717166043c4c034100080d82103540f108032040c5140c19545e54070031409041d4040c010060180c42000051145506078200300d0030141c0041d001c590724880c0100c04000507100814001078268120500150740601410603605014454081086e00d014082010451219411050996000640e40c0c1d0070341c0d40e10b540042e070072100300c03410850601007501000c02ca051030641225903c0140580041600d0b003096861030486241035400840c581c20141c84000804264071071a801480300703160a0346160459000315071032204d2405100304000101001c0c001040094005000800c400ba00719000c0c07683d00c4450044054540800b100081d06250040c0c1e19442e050285c41c1c0444c2e1401901c5000c1c5280d6521040d005041d000b0340c006600800510f080824003070700c9204904445071002091a240510401d414801d00525090601010400600c4807000c0022166800082820700350b40c0c03180381c0340c07145d454001200c0304070044003000400402ca0382c40100c0e80e0300d511181e10880c5064140c64003a03c0c000387c002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 243245467 1250 243244217 243244219
    0xa0c0e0109140402040305061005100201021908040201020a020d03050c0c030f030409020901140c0307060c0f08011e0f08030904050c040308030a0c0c05030706050117030a200102191e0e 81
    0x551400d02c5071604090310350000719401040149803d55a81c0da081c20003008803803d0700600d1503034204201a0800c000004280d40180c4000c500e40400e90300494540c1c1d00400815003080300f904005800c5900800405003034580041031b42151600360301e001442c952140d14040f1050169006501540c2000201410714205c1d51010310304050401c1011030007500f008200398100450604465900b405610080c9204107040002d50382e62070035800e0200a84001d907900c4801c12580c108a14110303548907200e2819145580940c4640740c0104035581d40c0b84902e50000569880c0d0411f001408020000003002100e02c2942d00b800103039100e44100361075004030303c00640048c004000207003c000140c0d002a450620a04003040c841e07030303d91100d510b91307001444101c401d0307580e9100500c0320b684000400e941407000140107500c1c0101524000b4444500c1107a045980c0d040d40094000545081d0140c4004840a00d1141039041820b14000c000310004008071000300f9a007107101481b079209800c024440c86c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 243246717 1250 243245467 243245477
    0x60806150a08071d0a1104030507090b0901030807110619030203010326030a0216141011031005061c0207050607080c07030509010f030e06090a1a01051807030917030a0c0e01 76
    0x1c030714022048998010101740c03940b99100a003010022a04010708042c501941c001c1c000741c0c0c01d180c2c01c241191716001c4c001d4403034604a00100001346004041700c0c2c41c0c0e688940a000940394a902013203460180d0721081c446000d142e40d55964040e4198007a6040b07a00484219050b242c0c448405051004441a95000b02004000040d09410720760010540c048101c201c1e0f8983e003500b902c59854440f180c02c8246a550840e280d46541c200060040f80025240003443d40d140d07044c4088000c1031701c202486024050940070441c4610f07242c0d1864004010324400714250742d1101c062409503154182100d0b0080400c80d401e0110301c0421108007603902150b0b00d81c84480c074043c821801918031404020ba13840c01c03d622400c4101c462030b0f040c06028000c0780c441d80145400541032408401c2005a440301e01118090a001000a5544c2410044000010350000c24054513180030450143c007c00f0005003031100c1702c140300d540000c0d0050040d445004071000401c207029442c00100d030754508000038540001c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 243247967 1250 243246717 243246749
    0x1107121b0506220503030a03020c06090606060901030b01021509010501051318020405150d11010906051e09010c080310031103010504050604080c07031e020102070b0301080718060806150a0807 84
    0x500b50081106078450f500d03c2c4040d441da95600020b00c1d65100014500000740c01044120384600200869900245190054440f500c1c3c020041901409098403440c10517031500e80000d40340c5d0091105914070500016949a6071500320301d0f0314040c00b07080c420240202944a00780100160074072408420880c5107060540030365042e000c01001e080301401071400752200018503440c5a0b2030b10095802d062140000c000280344400002d010b22050354418401d02008001810b1607551800d11f2904036071a0b0180d05480c0c00036500100d407500e018a000134004c91000040c8003254903100041c004a034420403080c1c581c0030103070b01030500342c0f10305480050140d885200070030000350028014180c810076203c1151300b050368a84070103485006d4400b91020032403460f0054410355a0500c211000b030400d041c140e900d1540340030041581c40c0028818249000d0001004591200d4581c0002c0010710011040301c1607810618141006541c1e6004490711810040200080680d004500c00007202d140ca485207a980d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 243249217 1250 243247967 243247987
    0x110f0712020f0a0c030609141603061b05220803073203070f0213020a170c040b0d0203070c0206040305030a1211040608090a0212060a0c020111090607031107121b0506 73
    0x601f004580840b000003104031914003411041040440c11351600328400c010600e181440b030221010141400c3c0b004c40301000042d0090b4100c8115a0401e0b1070010103d021134210401d00d444045035003110307080e400002424000e0103402c42000c07056403615034020081d50140200100c50303034014000205680c0082c0003040200d10b03e136100f50681c9002400d1002d10035000c4241c482203900800c1d0520200304004c42c15083c840c901d803000c03540810806101442e080c24921025451301441d0a080e0302a900000040c10340d0b4070404942d010507070b024050680b6182c5914007a5103940201c4400da0001d00d424920300d4181300d16016040303004404001151415081400840340d0f000d0080030440180b04107407200e80161294995980701a20741000703400710b410b05800c40ea060f10020004501103a0418182100d0385401d00e00710703001440c0445450307070b0341e0b60f030b0f407a00752955515001915441d0140c2c0100040480c040500c0403031007482200d60328000741c800884803110600310b015180d04180c09005450311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 243250467 1250 243249217 243249221
    0x11205070210060b070303060b0c280b010312022505010e0d201009150c030215010b030933040206040f0602030a030b010c1104110f0712020f0a0c0306 66
    0x440644103644014902d6800c003019a201076200e405030000c0054500141a40b62054802420009440a2424902d803500c00d0352224041d08080d071164214041000c8066414810420268441c45d201c0156941c1c1c00c20b00808208a0210b01c09409818010f2140304050740304108484d41d10181c006860303040000440c0d41c801d501d03201c242c000c0b0102c24140301042c8111418151f021510400e402010020401d12801c020200454828400c08603c2403241071498a4030345101e44661400d041c0c2400c080c181245000304541000081851540022462410080c0203610070011201200c032a2000150888504030140a030202e182000b150035403120180a10308580045c002064a4141925010750100548203a03000c0d0001d80e01c00a070f40100c45401d8003400b001e40c4024200990b11031a00c0d140c100800701c1094103248a6592207002c6254105032400355181024000006a181c070910700e000d0ba1921410360554015107d080341100250400055507412158440d551510043c910f942302c00c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 243251717 1250 243250467 243250471
    0x6050306250c0203100f0b090903030403120b13060f0803070515090304080f0102040303032702010f031b09050a0807230312070b0402040506040c17130203030307110607080402011205 80
    0x401c114440b080071000d6038003002450010307040d01d00002940301807510414226030b2000c00d2103024010301c1080082408002c02174a5200c2c3d00742c181003403c46034105a00b0014100c91390115800922030032084201c050a6100e4801d0b01d400380c00303402c08561503d42d800e5403030041a0300184ec80c0d101d030340c01150810441c0910b40e0804108401c490400da00c40319000d0400c908a400c3c80da6aa601103400c00a00d6854014014a411064a180c04852200c1d0715010503503d248006810f01c035a10b904142420305c241c0c00002c40e540070742c1c2141c00020100800400c140058480d05100d419903203000316162130b01149010846000403181c0c040e103a580072500f075019205050840e0b1501a43c1000000d00344500000c01615200c0d00f6403001e140740920420088807000351480d4000e510303203807a501c010364005068903500c020001040455076a044400c03060355486004c02905404040203001405400070fa1840c42000000c0c261801c542c1c030200210740c900c00c219000781c006000c1070009104841107a11440d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 243252967 1250 243251717 243251791
    0x1103040221030703140c010903021f150b18030706050c01051e010312020a05030d05090d0309050c0d020324040b090606060403082503020706020d0309113c0406050306 73
    0x83e046c8040703148140d08407240150154003513041001307d2581444516a003944070920550200031607511500c464284480c0340c05410f0104400081445941203100d104d0b003c03200d00241112605900c1d00340051550b0080c0050305981e609020200c2d40d03480c40e991858520010200d107068a5a00c0d40e00e0b04c64200002c00d5a440960040030040400b065040c4010022200202408109410301002c094500000e1b6500c0b10109840c248a0f080000c0011400c15890001194015900d00c41400028148075000903000940b82e9144040d00340b40d40004080c91080b070151000b50880c1d5124580140c440c01c0403500340341d10100030401440001d07444405402e1200c250f0306103c4405260b4241d24180103c014015800742e88a602c0030465154100410f0780d00001c03034982408041c009540c0e102104a51007255486042c1c0076454604035090080340c501d264601c0c500303035890354a40c00402100c004030041e00d01c4c0642d092080120349403e00003035203030107112418805442488104070205404880e05902 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 243254217 1250 243252967 243253007
    0xc2a02010e13090605070e040c090603051017061e13020105160609032115120201020a05031209010c09060818190c0e07020703050d08191103040221030703 68
    0x245580b00c1c20b034420102400d1040c00001404e050170f0324050501111035079110300c41c5092810039404294040440e00440380c09090114294860030800840070800f80c10001c5424044040c1c42c04170000010301c00c0c02018003103550100103c03404002e215a21080714801c80a2280d0007000d0019407080c0014003070101c40c00e9141d00c421002d07603540c4040d81d20001c020342c000303400f410110800c60312120301c0c0c01003248513240800c15000e0542c100c1e010440030384180c000601d059144401503900034010044c01c00e900c03105a981e61190b13841a0884070206072080c840c07542c1f0f4019010003c2c0d004414000c1500e4a941740c07550030f47d070ba81552175582d0000c8401d1400901812019030745005806803d40346251064101072201404c140050300c2d03009005040b0000c40d8800d041c1007000c15008510120625840d1420742c1e86c60740c07419101e101c090b8050152503440c6180c000805502450000550700451007200e60744409914800103d100070f10504031620250010044840001d001d6801100300043c08901 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 243255467 1250 243254217 243254239
    0x3090305040e0718061205060103020313030c0606030803090321060d06020d1e091406131b0503061302030d020a02150c010b0409050706140c030f0a0201090f060c2a02010e 75
    0x1102075070790040e902440200711b19140860001c1014010240d01107800e203821415454030701003802c244101c01e0b8000d8180460f500409045c411943c110300d02458015500c0c0e0754904140c00300d581c1d298060a9001840120750201110a52209081500030344004000190310900c1e5250ba070f00030b6111555011307210fa507820001d0002225506004101c10085000140042003070402d0840c124444c509404140c00c00c0d0308000071452545902594543c101d003840407015041541c0c9440c10742e25400040c0d142c4242000c0009410020540102d864426415980c1c0e500301c0c104140da56000e25039000b9030001c0c1619581c01c1c1494190301a103120a094000440c1841c00040481c04558610348281c5d02030308015400e00c502900900380e13504000e81045014a40341c80e0b0b4240381e84900407641046070380c0742e0006940500c1e5100350080440160400090b085590b42c0d403400000908509000d140400c1c40c1c6041c0c840b034461a22189828840c604000d00074000c030650045a8001c1c100108035404400014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 243256717 1250 243255467 243255497
    0xa020d09020904050607031104050d030305060a0e1611010c1e12051305061003030e0d0f0b0f07180f03140718020a080c091804021f03050a06050103090305040e07 71
    0x500076030140c0c4c041e00032404c012200074241c88000690f4645000100010085600c40c2c00d14003c8560305841c0005a40c4c5035480003403004180d176407002c03510102d0201440071918107a510700c0068a40c90b111000100600b00709942a694400017510108421341012580601c0c2c450240944032054609003240050249100c001c88406944480400d01900070890030050100021070300f01d00d1110442280307516594005000d80d031498005402900c002020008200701c040d43c2004041d0f00c2600c80d030b41c41c40e000525150310740c002c9903030714001140c052a030990042d1400ca85001c0d203840405c0141c410703081d9191005480d4be26441120303544030364000000d003410544240c61210100c84805a030300c00503010001c04440f0301a00540304075070101f10b802d00303ea80302d14841801900c20050300049540b80d00000b040241320703500f106482601c23a102504520f50543c407140c428840c01100b040401c0c0c440004508503200800300401141080109016400089820a9004001c0e103005022400c0c155 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 243257967 1250 243256717 243256729
    0x10215280501030c1d0103110406122f010905040e032b06140a05240a05040504110910180b07080a02100515040e030c0105011502240a020d0902 63
    0x1503544125681d40d503005004200721810003000801401d000407014480d1460000407441040c80000c092000050650109483d6600920018444240160440001da0800d104131300f40458a2325410310403064a00c0681000b4091710b54100c0d01a55042c5856007045c003400000c0840030b40a02a0344018004a80e00301c4200aa2031501301e490184c44215202c01003916082c0c6402c0d801042c148a281d50a500480d240c107604031007225400c6404d401d02c0c140601c02c030500d940482040d041142d0002039280801b40d044401841140c030103442c108900f400c48289103e55004201401c1d0380034960700150341d100ca108010340329a0005c1440300510481c0c0e40e42d100340e45030380401c02c1196081000b0818070119a010b008540344036001c4101440301c3e00d0062070305204407000c031920502c181e40c1d03510840d200640400a80d613090032a00001c00c015612041444400f99841507040018455204010fa02c05508000611036100c2030708840300c0b130b440301c060302400b94100407400c1c02500d0769a050840965124 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 243259217 1250 243257967 243258031
    0x14130804030506070c020111010e0c06070305120c03101d06090711160306060b13060318020a0e040b07020307050303042306041406010501090b0d090602070210020304060e010905010215 81
    0x39171114808140a0f10014040401842c0a1482e50f4900801d01241150106038046000b40486205603180002d14041e2100d000707030994a07142c02941000c0000a001900065001e0004040040c42856566442103015a40c0c410036080d03502541000c07402c50f0500e10482500644d05040c1440d2801800c40300500d0403d020b07500c2203841da9444030410900450b84509806094642d072070030302e00b0501002140c131141c450320039102010303501c0058011003803018261558240d40240260a9242c3e1441685c0c00c410041e181684e888543d180400c112a000004846901da4008040d50031661540c40c5c171402c419040300840d09441c2e5a82c14001040e00900819216500c00c0750007004000c04200110300e00001600600d042c810442000d1201114070b500365610403481c0f0704086880205072803d880603016901009400443c03901002e9420303900031000e081665119600d02104074208001118440041c0c0300e5070b0b025070041c3e60b403006900d0a10240f03c2c6e00c80080d42942000e0801100065150451 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 243260467 1250 243259217 243259231
    0x4050105040201180501050306092203020c030606040b01080411040212040b090f06010803040b0c03090d0507090c17070e03010e06010807210317040f020604090903110114130804030506 81
    0x1442042000b15a0000c1ea41c2c2c55402000424030700395414000003800354031014041a1061044c8000254100d002c6207185161420000c03600c00c1e64807240c940a5a40c82988001b20303c00d004079000905182000d1080b00580f541c140e65480080d126074a40801d0300c908203104a80040c0c00b0450302c0300300c80b12052100d004d00d02c82c0520a000d441d2400003642080003204050460f40c00800041060400000075034040d03c0c0d11600700c50707407800c110441d146503200300c0d0702807500040d0f0300203200107001c1c2c0884c0f440d088949500d41800441b001480032619201d11001c0079030b1180b81070b030100303900502c0340e401c803840e8850140c0009902d2090700320580c900030b030983c03140b1400d038001d039018440381c0301e268040a8031038200a03540c01c2c0c1484a0350080d00040806810000104002c0001001e00c15141ca9264800e6009010f4681c0d590711601a00301900b1426070076008606008092a241c940503c40e41e04034100800000869444087c0840c2d03824007580340a82d4861024040400424014041070780914a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 243261717 1250 243260467 243260471
    0xa05130605091e150c0a0f0303140c03060d0b0603100f0605010306060c0f03080603030f0c010b0a15020a020f04020904060b03010e0916061407080a02070603060b041a070206040e040501 81
    0x104608000c0ba50072200c100b820800c2e180725120701151602c1c0c44000d00490a48001a05d56109500b0300303240c25441500500b680144076030b100b041c0354259008140201000303500440c50395546690f60f1140c40141c4180d9002a030085c1c450300031032020420640c1100c0d005040da5003175000400404141e460080c9440d00041e43d41c1300400c115030301071260200074803407402c048000e030905840744920b40e5640000502804480710001c0c15556040c03080351100c01030106113684a004800c82c460080030b240e4082da001d00c03802440070a0240c00d0480080e246c1c030441e03004140c206071035030a03c030b14003a04a2105400c150240032026031583c07039000751005001a44a03464480d85450000c0c039030041d000d03003150190b03006240c08030b1450145428010940e000c0d818440c2902c400220400c000e40304400000e4802c2e1400f0801601c020745c0800e02100b04c4500d9074041c04001d444402030710451145210b4902840201c101c80820201c440026220407800240306904103903690502d8910300c2011903048400365 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 243262967 1250 243261717 243261727
    0x5101401080415051618231809010207120c081905090607150f05090a08070305070606030b0f090615120709060e1e01050a03031b060e0309010305010b0306030606060a05130605 77
    0x280c0e0146810a07400940241180103600d01051841d07488100c0c0412a0711f003681e02e00820030380d00c030452258244100340c42041158505150403d000b50004101143e240c0c0c88070a18014a0b0308c03a0800c0b21900c3d40200d6000e25242c1959a070240d0a080c1c1c030307460414000140b045540c5540c801d4050039407030740076250701e1031105060095071003101d444500740d568003450b1109000ca000f200007800d41d41640e00c5405650f0f200200c0c282503a0074042c0e0180186003904045012080200b83c01e0000e0240c9540b003645000341c0c644564098840c0300c211040d040800e1b02d20400596442e0516a40c0c5581e207072282960003091f151003500041e0380c0302d40c0284104003a00414003a80914002101014031011202c1c0e440342d504180c0050000c450500c40502000340c0d105603046041400c001802049502040800c04000a0076543c0e44a41050380e0135808246000c0000034040d131700000701ca10500008000d41210742d10700003008541e4001104505c01c001040c03020a0701c03d41848941d4000e0041a12215160 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 243264217 1250 243262967 243263011
    0x31c080604090f030507030207050a03060b03100c080a0b0a0f060509120304030b010501031d0a12110606100503070513090213050d020906121203010e07030510140108041505 76
    0x4510040c144038080ca251085007004034900c04034800d010ba80c103191050f41d0f20680c1c20124500100b0f9008a90300c180b003500e0010810006520034820703248250161340041c224054003a0403a4501801d0101007020100015080e016030350050001031001007500c1c0d4101d880f910151100d00c000c2d00800c000c10000640000240313030660001c4985283d42c0d0085280c141182d4490001c030106114590525484c0c003107a0810552002002c1500784841045941010603420035070b9503900c455615001040201034862102580030074140e03c110005414800d4102c803032007045400354801401081044424000100c032444848030700002041a07000250b02c60419030488811a000356221511494940b180c502c0140c40c0c181c030700c1c0c0c0c5c40301c4112021640484045816030800c0110043c19130750070000800421584ac1c0180c240340100103a0f0780030851a991150390b05400d02e8070b0b004207040b0321400c030150541580302d101d00540c064801e4400c001c11012200c425001c2d0303031007541c0400c41d40c01c00b400380040c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 243265467 1250 243264217 243264227
    0x170910020705060618011d0705040801091505100f030b0411030f0604020108180d0c051002070605010e010e07050d02250f02040e0619021e130321170a0b031c 69
    0x40c14400d040107039055458400c00260244640d203c100c7c11a03c10000100018012410399004014001c000d00031b9460500d803d540603030141071044e5202d4500004200d803626008ea18005491808148001d030504645a0800006004000311080000c2401103507032500d060002c9803080413000014102c42c06c1c1403001510302c00d4000c00620070380d10070111814841c6000036880e803000106061085e0014000c0c200b1906001001d4408620306000242d01d0b01000516071040b412614840700102c1540d8961082c0480150160b401d0303000a0020710188940100b0380d4020820380d601202c1c21f20608030b0f071400702521900d41c5003054401080540c07984042d401c01e4054280c03022008005000589030600c82c03184081030320020940550790102d501c2c8007103003900040c40d030300300401d10032f5a4440300700401c1440000c5950008541395100308510800380006d41070f00c400713880d1054840f01042400001d800c440420010850342c002505c0b4480c03c0640d803028001d61981c000c034100118a4283c074158040d00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 243266717 1250 243265467 243265489
    0x10507020102030408090f01020a020907020c0405060346031d0307030b1f0306020f1309050705180d0f12030c0e060406050705031b0d0909020304031709100207050606 73
    0xd59004004100015000c01c0484010180450341d461010b003842d40102e242c1824814001d403c01549028461020340002d0440c56904046a0502c100e6680300103243d1115001c7c10820707150090052150b00501680d20000307220400217400340040c900400e10885a0348002106a011920f000c8840040800c1c2034170b02c206030403064005003107103840d5a561200c0e000005180c0c00402014150742c80078902108401c0c402586c01800c190b42f112401c00011041da0700c404c81c403030503035004c46400260114040c002d1f14490700e100e80741c03207040040c007042043d10200300000c0b25502c40354540d200b01c0012040c450100200f801900c130480c61400a002c043e04587c0e401720316000740704501c005a04580d54030001c031001d807485441e080c0d03100d140030302c4c00c1803a500401c5a88440c080c03040030018501900000c40008518031980c5010f200c0e40d0760342c2c83c02c089210a64000c1c00107001c0111030300ac140400000e02d9084403800e4200c0d40601d516016a0089800070300c02159581c0260060101614184450389 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 243267967 1250 243266717 243266731
    0x4030809090f04260d021305031926220501030b0402040302030a02040f060e0717010b090306060f060d0c051b060f0a05060a0b0328020c030f09040b0406170105 70
    0x1c606092a86814940d100d039011003101d0000602c0c82030025510031384c103951000c07a004105549441e801e5810301c0700745031903000c0e40b40203225062445c42000d1000c244000220303000001e625179503000c500c1c0440400000394140442000403c44607200c3c146604002c000d05100c0100e0840f00c40c10240010240c0ba060214140b2490050005002595010552108066044500050451b042212600502840d91000513001d03042e5041100098000d5441260840c1d4408910702e2680c0b140c141ca40540949424541c05501c01d0001510034204034507180c80a00c0010285030800c81d00075441c00546d456031240c080010030115410744007011000807210402c4820028003c04e10300914400150340340100032410302c640b0b40c000304040d5100e01c2e02020140940070b4070580d03030b40340c141030106415640308150412102c0302c1c0e614007981c1d00d0901c240c45000b04441c0103140b81c0440a50703080000e40140301c0700340e0b004c1d540e8900081141e071544144070042840c49411280314511200c55400c580000b4296 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 243269217 1250 243267967 243267991
    0x130903020c101e02010b310c0203030403020606041415220903020708030a081b09090106031b020a02090c07140615030d030b011209030e03100b151201030303020f0c030403080909 78
    0x24143e1655910100308918100004005500d4400704080c070124041202d40d043d414646234001f54050307404001503108030300035002c9400640b142c03014407044074442941e410308407540c4030101d8003c010f8420482d1228038010302400c882d00310100f00010000415804d0004e06039907040001c10142c05100210041440720091400c1000a001c050164040242040c80031402e01101d0756484040605454111034003600d289095030f11000040d0080050303070303420340901d02145400303460039100084400380e482d07011300401055225124049030306e803c05a03080340c005a054a484030070f5101040700602c1181040030b0f20043c83c85a5003890305003000c3c0300c1d40608044c24111004130603600014002d0a070703504d250340002c040000e030404442d080801c1580b25490300460100c1c2070030361a03c0e007109600d0035044505a0703e41c9075060703941c03c90744200140c1044112007240100040381c0294061311030b00504d195400d25140d604690681140d120340c10458174044041424503150900011666010000d01c80c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 243270467 1250 243269217 243269231
    0x2151015110309010c02120d03051806042003010b031203160f02070b301909050c04150308030403020601030501140106120504020604050402120604050c09130903020c101e0201 77
    0x2500e5100e110700700f06681405034001c2e01e5000c40d150103141d505070040210640d02c40361010600100506400e42d0101e0000386000241c81d00d0420104580f40242d0384000c50101448c000c02c900c51400540a100396419507a609841036582c80900c14403000c1c03641c0b4012559646088000318105d14050341a9400b040b82040185081741e8000a0f00e006403804101031700c0c6c441c0c100420102d91104840e0b10881c0700020341c1d007894103200c81d00340c406020710340b200300b41501c0c8045d18280904560502c0e07030140c03041d440120960801d0501d80d1103026920031080c00c00360040e8030707615039600c50f9000395402c4006a0046004006204081c421100182c0c01150510043d5251104c010100c00c0141100000d556079030000c5401c660b1104200c1e00204800703002551500c9042c0d031680302900048604034080c5040100103110844001c0855009520081641c1c06801c2031110410003450304030070450a5200e4400c56070342d01c2d52401c1044030601d6083d5a0401d4401c0301510030002c22030510f2688055a0518078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 243271717 1250 243270467 243270497
    0xc0c12060405190611040e04060b0f06040909050a08120702011401120201270602030901030b030a030c080d06090f05061908071e0b0706020301030c12050c09060102151015 75
    0x22401e0716030b40d40340c049149400f8181000b00c01400051030f200c80190000070002211610040c03814400c90140c4030400400c0c0044043c030041c440070784000c99028800304030031b011408a270f42c00040b1441c014400c51b02c101107a9940c0c03035850390001e0102c40f0410149000c0146055090196503030003400c41140a0095242c505111001081400000d0610000c0440858100030400d02903160310500c1c0000301449690302d80103074481e80900c80c8940040e0400b10380103910304000a2500215030306a48105451f4065140c60441d81c0080d00c24101d01c6403100c3e00014206880e000d501900d60340d6034000500b9090840c03c00c0164014021b82c1c0c802d0f04440c400030008540f0104175101200d20300d910b000c01c03080098108110b000e009070803441030540d01148440500c585540a141600d10401654003c01d840b200110030340c000e8154020120380c00220010100e007080c5441980019060040300c00007070411481001c19541141c2540840d403c060f0100040c501421001c40480c146051200e034800c0100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 243272967 1250 243271717 243271723
    0x3010501050d14190c18051903050a0b10090506032505030609011d0715030c0309021f081b0702040e0a0213020c1b0d0b0604020f0c0c12060405 63
    0x44149414068040750326425080a50002d070900c681c8101d105045180207080c14600d0403c000001c810b9034a4008500c0307119004031021460044803001400c1c0380703850401000782d500d103020350074956100000400400101c080091154082c80350740705c10f417540b80000102200701d8440d848508a14100300500106403004605482100d2482d9880c4030b4214410007081100111a4410382c0c1501c2a0020860b1010040d40080c034030031003246540900c075109048103643c4503010f00034002d0f00c000c0248a0800305000303500008070041ca03030078049842013085d00004c03510642d6180c1701142070605903010b0a400da0160405a100d008085420350303840d00c8601c482000e010300c0400070b0241d50b80350500441c40b10100300381181c19a000b003001c1070755540703d80084041d41041d02c2131320300d6100709562090351075182e51a00c4407824010703100e10101d01d0349441b000281500a4552504103508222007000025903030300514101380c0c0c80700200903142c244002e216403018200350015490b00540c0600c40011404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 243274217 1250 243272967 243272969
    0x15020304120e0f090402030c06040305010905101b0c0c0b21101d10081f0e030406050f0315060a02030c15040b0105060315030601060e0306161209031101020c06040b01080708030301 79
    0xd54009126070307110710100b45001f1020b09231580c413100109000041080540249090354440d07400d4403000705d100030810060b40e12104204450b1030742190381404181c03052128902d224052116103000d0350351480c00c1c1da49a0321000403000c0e21540031450199418819a02681001010842144031460030004c420008040240300084502800c0800c50900d168202800604100c40649040b03000400040c400c41d01e082140654442c00c20480f500c8181e03010090303800b100c0722521014580081000450344503400200400000108424400300300c1d11210090861004950000c6a88403040380c1410314041440442e4a0b855102030304210004209150881c1110000e403030b901e40300c0d04c90181d01c820045138000c082c0d400d841618000a0765a83c04082003183d000164159103454035900c003801441c0c00c01e407591030701168190309148c1d0200d6050f0f000b042190300901d01040c2c44450f20b03405500366800010b103022035520007801c5c4001e002c3c540b08158014030001006182583c941415581c50b8081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 243275467 1250 243274217 243274219
    0x51f060c05010b0a0605040f1211090601020f070e310f0c2106050108011407080c070c1d06010c050a0602030c040509070801060305060103020a0c1e15020304120e0f 72
    0x14140303841045030940160120800c0100f41c1c0f08900d4844d60001c0040e00a0b229004141c0d0f039981002900329604100e000c010780e000041828003424050501c41341e180040c00311030451081c601c05a20b503950901104e0007400a64052200c0c1d41042c0d2900c2c090021030b0111003004003424000300d01c00c01e00c1d590070100c0544d03000c032400c05040303024104218400e0150784040400d042c58400c00185201000711486e410340b00b05010004da90720b40e03922501b2240900f01e06040d69501d5404200c14900442170a0392142c20b407404c242ca0122180c0e510000c2035800e502c80f4114120010b5412482c2004031741d074030b600c01020301c0e2500d03601e100c68aa8030303a5140c00d101c3c0035084560000120700048988000c0340d014100180408466040c2418002c10180c000d115180009107818042a920740c031038001c440005c5980d0385c1d6841041050348a44007039100d220300c11407400d00400703020000204d0711420703003e02c1c6044a2005840303182506102c08680f5460480302d003002a2003002080e00d03510004010f02441c0c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 243276717 1250 243275467 243275477
    0x2c07020c1f031d01020901030606080708040609080c16090506030c03100e010605100804050c010305011805060f0d03021b03031201170a08160c0b0304030905010c0303090606031203051f06 82
    0x12003010141e0080c0031183c0030400d2140e8074404040340500540040440f10300070f0b6002c00c0072950b9468100e50704d003c151840c400040400022038041030080d005483c8044c080c0a00f070b40f4010b07040103840c0c9040803042d402d000300060f02208110f0402e0b10f20039503603c80380940c0038046044007140000c2e210442c0c80021120b4507504c1d54858a044802d5000c00302410024013105141d054014016000ea03404603811100d6124001301d40449500ca40500d504850403c0b001c41c01100f6911120310145c140107101d0b80d007000da500310b8019113940c3e040080319001e01035009010681d081c0440205030340b40450140740607130b04c104030481018044102c000c0c1100c4501303d449100310348245000d4141007200c00301030710701d01e4003103401000c04288141c007000403841412001c96081d0365140c05412400700b11005004903c02400400c501c1d4025550035040c1d82c0300303260011f0a07103100c0ea0b540d01100e009400c00c0d540340c400c60301159441c1d60188a041d81120f55621201121540b602807480381150f180a0041009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 243277967 1250 243276717 243276769
    0x3050f150f070908030703030501180b01090b0901050d140609070806060d0e1f24080601030206070c0e070e1c0b0408090111100c031104140d08042c07020c 68
    0x40e118030b0800000d00341d0081517079a20300c0d050070000d0240a080c0100602076554050401152401c0d21a6418140c41030b1503812602e0b240002400c0203800c8144464140001000600744105c1c171881641c20104108015500904101c0207014420b0401018401801902420b00146580e540c0035a01c1002102902044041c0d01440f101e0603c0c1d00110495440300a502000300340300b00e60b81181d04000466001065640c54ed01161001700c003040c400c04800750041c20051015040c801c00401e2024040c00004142594403604125000d5040340c4500005042148649451508901b80090403081c0c1e1401a05209a52908041c021000c0c1c0001d190440004468030264018034016491007001c0094030402c200102c00c21019040301200c92002a241c10845940046508199010380740b0b10160303101100d0409040c010b0261007150b040c0e8a03010240070000303a4034100d00321032410005031003191585880a00c00c581110101a003031006642000701c0c40000f139281d400b80b5071180890101006400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 243279217 1250 243277967 243277981
    0x1080c0405060f0f0a080a0510120b0601270501080c28021606020a02030705060a12020d0603080a030b01030b03010e0a060510120317090c0904080702040b06031003050f150f 76
    0x10311950751300455005021030100c0c041c03500722604501c03c40a82e00280119502c91074251440c041c42d000e5901050942c002c4040410301641c00241d00030018100b2640e04140d0741c100c8140309484150344030203480c010109001a5034407058943e0421001400541095010740300c505030310307403115440c0d5205010010a100018402c100071046c4840941c441951130f6147e01c0000e481e85048078083c3c0c000c0c4210340c0e0000b81400e0010072580c47d43c80981c0e4405050000b107d07480041d600550350240000d0311001d0120104082e10700605941006880008200e15a04005400c1c2c600c40c0d81c12a109904d051008042c8450205044401d1a4084000121582d820705000045100341d0440d21042c40b03049000810035401c070404066140280c40d14443d25994560301b07640d144040c0e40147c1d0450319180201e000100d034074025042a5100034004604240c101d00440d1135504201c520501e2540c00300010014440140800d00081e05c550019008103986002c240740c04000260803c000c416001c4001162 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 243280467 1250 243279217 243279247
    0x120106030206160c0b0a0503061005040305011125080a030c09090507020a150605010c11040e0d02010204090c02070302060a0c0521271513120c030501050601080c040506 74
    0x6907600400054650208000544441da980300c000c40302c240711080302150b000c16080c15240c2c0c000c000e0740c0751855940d44005000750107404540b440300340031042c000480040c400b03000e0741c040700c003800020030b44a290826800f0783c0e141202000500c2345402ea44034101007040320707085950070045418003281144008a048618200c00c1e030007a50424989424019059404184810b40c14050007106140100c1002d90400302c410a1003000d01050100c40c41100041c001420303104c14440003000080c0301c0c20041d84860400c11648071820044c0d5000074107005816070340c800c1640700b00c11480208541c0f070840d80815054410400c0900610240172183c80401c102084110306081040306202e01001c40340c0c1d040843d9800003134002d003140c5038008400c0380030b140c0105124007141005002d141200b40d0485e00420640c0b000700000b50994050401240140c031920114148911500a50500c01c1c0745003032050071158080c20060402038a0001d120461204105650a94000f114919900d4059181001d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 243281717 1250 243280467 243280469
    0x706050708040b1b160c030b0c0c0304090c031d06090610031a0901020717070c0509160e0102030d110d0609020909010303050901021606050705060702190609060e070e0403090e15120106 81
    0xc81505c040d03900010440d00c84050340441b4031600020317069031224140101e0302d0049885440d0264070610003004901c08a4102d139104911070b040014507424040d2428008402e10b4440142c542d02600134000500b6080000607071250300c0d50070700050941555074007001c01c1400c0446d80026003d00002c035104040c00c1d41242d00302940480c0c4800c42c0780d0030a00d18501d82e08403a90070782d24a55a4900020141002c10a8a108030b9000202d013903840005941910f401c1c10750102c0d00c1c1140700030700005540c02220701c0b4060701d132601d450b001ca07100c0008840d15801e54681743c1195003840c2c014400e011076a03c540f07400a054a500d81412516a85c1504c0100d05d03000b4495071044125482d41c40003d0229040300003880024040c10560b2291354038001e0a0b0b03a0b4102e500070301286c01907558424000714000b6840201c2c2203204070b10100e1040b500c0c0d1221403400425030080b1428038010070510082581000e070400081c4951900c8161910f003c440140909002030381c81805140400c1c0341c240d2520003036100c60 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 243282967 1250 243281717 243281737
    0x10806120312220c060201060812040b03100b0d020c0c03010b0a0302010f051306030e0f070f170a080304230c0603070507080c1f0605061312050709050c0706050708040b1b 75
    0x204003a0741e504003102520f88170311810000d03500e0000c000c60501d501240144110450f4840203141078900b030220101944024111001c00314401000704138031450100a0003448001c03000542c40382c41c840c9c60b03242024018080c03503200380e2505620540c01e840382d42c01032080341c1d02400c01e08000c88031040c0680c0c81c0d110b0210701a40d9650109008141540c150344101503500000c401c986420007051600340e035418090060030402c41040004101030300e0281300c086401e58a8030281e41040402d5901c002980d0000d81c4e040b510b003a190b8545895a4070800d42c100110303080000240754184100c00820b88511001d0690010480002054020301c9110012a54549031881c1243d0f00d8280d808200c001c25070240041100050070000700003210325008040c0d980500501801181c1039181c5000308000740f0102078221043e000e41040003883d021a0f2203a544503043d50000c10f5030325005440d00070b00b1900000e206106200018080c0004942c01d898582d40c080e0341c1c22800f00740c3d50b4022510544030b0203030442c0c0c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 243284217 1250 243282967 243283021
    0x70909140f0d090608100b0a050702030105040c05150a0c0b040f140d080a0e061314060703051509070203030a0507231206010302090d06092f010806120312 68
    0x212405240015060040c810036920b00030550313210b00040303c2c0c04030103442040c03075041c184000344080d42c0f042000b003a210041d41072103480d14015070302007401d548003224140c4030703c50310100402150500c02e071442500040c80c070311940340c251032086c003501c96514200e016084031240000501009618101c10a101d50030400d80c0641c404401c055664400b004080300c00003034080b1011911070f0b0090f02465000c2000b1001400159440c012894029507d03c041981d5141c45501154603640040c0001350103800b01e80c0e004540e0389045070b84a08000421140f09005441580412540c20340c00300c00d40390451185040804c1c2915191400c440c1480c40d1a603c41c402c200f91110541d140d4100b0000b041c0b0701130a40c0300807146640d60700040d81240208610140c200c1e0b1205682e03800220b255100080c400c0c490792088402140c440038030140c1c0a031110254032840201c1c2c0c0c0032090f660b044031101c0e5102c00304130303a00350340c8032448109980c80b401180280c1410341004070103c4e4500b045001552907041d00f040310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 243285467 1250 243284217 243284233
    0x24090907050f071e140c100f02070314030403061508010e030906180d08042d0303080c070602130314010b0405101a070605070207170303060603010303080603010e1f0c03020c07090914 80
    0x805d5165014081c600c0d115441c5a9000400c8501071002804000c03815006403840b0b07850350f2644602940004183c1400c1d020400001c0000b54151080c6c61108400f01024040581401d00240c21111500807400142c1d006000400180d0340d904e048503019540f1050f0750346503010300008104800c8104000a02a100c00b050100b03000302d84a00710394260b0440071aa02500040d007a560305c401c8524000500010140000a600c200411004201d102d2145d20010304e03140c16003801d600259400c0e0021204080f04110765103490b50300740030300706150000725010003031802d0400130783d44a003006100e940142c0e48500014281c0705181010703280840e07004201030046127450f450003921001c55018500310541420820040f8090000c10f480c420140901090714603401c60b1020340e100d138402080c0c0c4c0d40c0f5640720707895942000f80500c6010a2201114441d445800410440d2402e07200d02d140c19404142c03040c4501c0400c1200010100100c80d0140c0d40080c01101300c0c00e004c1441c2c1d441c9202d0054920813500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 243286717 1250 243285467 243285503
    0x70c02030c0a0810110310090c0c1208010302090a0c090320040f05010305060c0316030207020f1306060906050c0c040c02010b060c0708070b07110f24090907050f071e 73
    0x51065141001000805c111001200030b8582400107407a400800801d007402400b60b907005911141c1d48070b10030f09000000d5101582e51a03076104072142034400281e0410010411410002d80c82e9410100e03425007405907031000c0700018007d6501c1d200140442e00d582c25040d410310107851203a0202c0a0143c42071100450b08121040585400e12048905208800000720030720380c2c1c7c0054901070810410306031560b121581088000e504601d009a070701c081c07a28100903035596081e10107010040c0406011030841d02d0280040c103003000f941c0c050350510504000c0300c6000c003c007184110f0b24020440d400249c0c1c486255080b80104180c01140c1d8201c000001d000450000020388030007121200000c0b0342040d0348a5084460700c1c040d207440204200c1c0e0f5490000324030f14228042044140028103800c40c0703c031402807154000801d52a040c00107560008203a280e40c1050030710141d1196990900703a1900034a00c004000ea803181440140984490a141e2603101024040d0450855005811a501d09107292 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 243287967 1250 243286717 243286723
    0x30409021308030a08011a0d020307020a050d2f161d0c070b0a0c0e03061501090e010305030717091801090b0a0b03160c1a061201060b03070c02030c0a08 67
    0x401c015055034a0050010b1945400001c941c9103d900c1c0e62850501d91038405c000c060072900b120110014501400042082c810600c041c510416142d0700a1101d41c11030306000d8180f103c00c0e0310007030400171124160206c2445000c0b13428001c0040080c03400307c0900e80c1741da403400c0c2a28600444940480300500290044401200e5400d01d602d40811031840d841d0408194841d00c12088000c0a0201c490005000680340742d10226000d115804d124214001c403c1c0003905041044510002040d1403410000f61540e10107554809000c11100d8400294155120241d40340a860750043c800121560701d140728840d0802500da0fa1000034042601c131500d580c40d5004115024022150300500d170a80316200741c0381607800031048409154209180d5101e040251800110454615060101d10508080041d10a110032001c0b501c0001d03103480c850802e01c04110706039070102c84042050b1304200e0305100100c480801c4a400c2407241c20102c40e2810941b0100342481e4040c49504d81c0100d01d0b0300300040300c500c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 243289217 1250 243287967 243287977
    0x19030c14041b080105030d0306230609030604150b12060a02090a0e040c03060f020901091a1204060608060912040e04020a08030d060503010c1d0d02040603050a0503090118060c150e03040902 83
    0x846c19120141c000120031011610710344a480c1c00200b8400e004004905d0b5820750440044e0081c01c400d29080030342c03011038500030081d00d00302d920030300200d00815803d0544c07261040e0008201c0d9564070100c401980d0954910000e086600c9060b400240c40c281541c2c3c0c40c8a140c02800c0b1031082d200c0c2c1d8900b60400203030114403444165030706803c02c1036012090b10703903108881c401c01050310396a40041c1402086080350000b01d54012000400b041490b95184400d50400d11992045502060013030034151000e04203070001e040030a46a1124001c0c010b8108001c05940030345030f2103103201c3d41d29aa00d00000f407060b01150b00144090000282d161004200d0360004016280700358001d01c016003024804036032403140d0070f2200c0002c50401a201006203480c105802d04076000034030201e5000d4480e100c407804c2606009040320190300004024402d035800c41780a4008018044900100500d8850003810b102c01e40000100440781c10342d0541c40d00499a400544802c007c1021207403507030b45039500c9070000d41c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 243290467 1250 243289217 243289219
    0xe030423010f11060a05040302190f0c06050301210c030816050705090601020307080306030c060f0c0610030210031e15060801080604050c060d09020402071119030c14041b080105 78
    0x120000552950280440f402e024600d000200126540c0402100c01081d02030700840440c003d1344810140b844400d070312400f1050180200720f0300c20300c0c940360118000d0580d612101c00d0200a1004010000b40310501e5030300351006080c502915002480c1074450300c080ca8000070941040800c1031100810035180811400d8030417406c407038200b9250020032114080440780140140e0040180d0707000581030801468101c00050b08407403035920030f403002410641000880e00501070000c2032079000703844208981c2c0e4005480c0d02403098194110740102d2040d00318a02c60406064490000d4601e403443c007a680340c0e03806240c40007040078411651800100d07865604c40c080004030840d001041c119001b207032540c040e640c000000c00701902d03400107110640e04401c0001d0351041d6a844500056103a0340010165a44244083d824400a0400700410b02e908600d500346451410801400010b05c0155240d040d0366209a031048170a0f050780000d0003800411044808902a03140071007216a0420b400c030f030598030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 243291717 1250 243290467 243290477
    0xc01060e101d04020f010c02121203041b060903062f04050a1406042c0115030e15060f0402070609080a080708130807060e030a0801030507080c03100e03042301 70
    0xb0303014a1000266810f55000e98040c81404500702a50300490782521300610140c078203801d101c9421400c1d8201925440c0524101400008010402144002800580503c010b40d8040b05080080090940001e4040102071954843d480610340e11010a00c0c2412042c52000b4040d103128030100e120f2030382003841040c0c003d6105180200c0d90440c40c2404540805001d4403141c2050b14280c4608481c12261620501000c08a00c840c100700280c0d0342d5450182c8110582d40301c1000c0182d600800320f07802d400b40c01e141500030171144102a5194072034950000e070102c40c0c1e9000a20302c0d200185c001c0c4550000100454038080140d8100949040035100e0000142c940d00e12580c0c0b003079030a845031303101200d10a100001980a030310020b00000c0c0034092035800b900d00040d04824051081c0d186500c8144101e0124a81d0401001000000c1000d4406844400080d04180c0c04060200341d4801c103010510a980c1d450710800480c20b0010001d403001031180c07508a03202c1040500c882901015580d00d9030780010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 243292967 1250 243291717 243291749
    0x711030c0d0f0807030905100c0302060c070807030e22050105030607031803030915051f0b0a02030f030a1803170a0603020603130201030e0d09050315090d050c01060e10 74
    0x11a0007140709440c10303000121020b00c00c0c0c480d650724145912144084040c40101540403e00b41c450915540c1d202e66652105200c605082c2806071030200c000f002c03003c0c007850800c041d9000581020a032480164107060982229009000107815403001d8510b00040d080d1100c0030014801c00d075044039049440550a5139003a4a9689040b802c0e1403201c000703c0390f69010b80c00e09500083c0709500c4004020300a402514540320140d0070340050320030513600ca070440e9a5400c040d007100314410410030300038007041049030326155560780d0294030780c01000204082a200480020442002900452500300c11101d0a0080c44901d00c1d0243c03080e550b10008000c0540b03c000001d0680d0504e11510040d690002d00c1a0304690b120441c405003124040070481c1015101c0304560950082044000d041c0e1101d620307284110340c2084203152404a510920400807c0c0300c0c001e0102d0f103040420804031840b187d1401c00c0d50b4240001144c1e0141c00c10340e0111039028030503000c10041542d8184ca000a03504244010f910308 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 243294217 1250 243292967 243292969
    0x18080f0a140d0203120406060504090b1504050f1501090801020307090608010603200703170403020d12020306280f0e161d0f12030301030f05070816060807050d020711030c 75
    0x3401c01c03842e0940150307000b04103200704001000300940d8818883c038008070fa00c0341c0f544081030a8503422a801c45126007400c0c18070200000050600f40f44100c00c0d5010842440c011000f2031310304c080900070100b410315a000d10310590340b1070141207000d04181c0b4000d65a030b0800031002040020304e8402d00b4000b070605400030882c50f12038004c5045100840401303002c550103d041c070310182e9100c43c2084041c40359030081c0500311107400c9000c621503030184d0050031112080c0a0041c00b007900c108514550b162040081080c80d07551140c0c04003800316590302e41c090148001da203a980d0917500d85c0040400f03a20004e4006000e14026101d03c2c45521208501c0046a039004025621015440548103010410040c0d034282c6003041350002c5007802d8002c10b07426410512200d2035065510a800c103580120300914164240441007088600504000c00140302c1038058080da00c040d00b09a00400080103000300204140601c074030706846a04500c1c0d64210b640b09800d1a22104030014941481e002c1e028800007110380d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 243295467 1250 243294217 243294223
    0x3040b060a060c120306080a030305071b1a15031905070e0f0a050a06120818030303100b0703050403020a0612050f07020a14030c07030b1509070c0318080f0a14 70
    0x100d0303402d41c42d01150380704030765a855011080c0c9800c200405a9506001134001d000b0000110154000c0d10001104c0c20250001440031040ca11500940c00d040d42c00c0c0340000c0c0384440d0082c00d0328440180380b07100d40c0354640c01d00b00b101e1025010691500c10702103450b2001c0d0b0040c541205680c800c0d002c403505180c1c1c4495050500300200c1d1081d401040cc0000681c039440c075600f041e40e000d01802c100103941c0d9244e400080300215000829942c0010118181900341440100304502d204100e00039411441c01d108088410015401441000080400c001c001c144c012419240035550081c11300b4403007501e8841c0103141205c0304c244405198180404900e42d440b4181030640122103030b074060820540c85803640d80003000040755158561004015200510b10305011250155103c0c0701254510b0030003502c50b480600e8400c4099115000c10000e015586401c030919410481d41414400c0f03051881012112402020327034440100c82c000d010880406620220303401c1c8100e80314030f020302c51803c1d041302050b076 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 243296717 1250 243295467 243295469
    0x210020f090424050d0b0a051b180405091b0d080c030d020a030c0f0f0e060c0706030c02150705040e040f0f120f02070308040b0c1e150112020d06110705060c03040b060a 74
    0x1104c0403c480200304024010340001d6030000d80545c00d0303000a1481c9100b54492b40c045540d0043c00b00d021140004140341c00d02400e504504e10900914080d80c1c0c10b0052100301d414688003510842d1035541442c200041d44064405590541c0150303034640589041c45800703544290074940000b480c00c5042024107004044c0403070421210b1742d42c5c0000d00c5094209480c0002c4a9402540c096401d1207010038964007000141e001c3c2c03140d03a0380800c10401c454408ac1c500310354800740d40c0706024100200709519600c5410741e0304503001c0c42d0a2010944940c14510030412040c1c1000e426141116000801d204501e07006143c07034903280d1307512070260355885812611401c160000030580b40702000204017428564001c3c10380450800295110703003a03505005410b0f0800703680e007140da5410030030b601c80b2a0030036070003400c1c014102d605110850207141e40c001484a5458071000300082e45e01c00c0c8074004041c02c8025112191751001c12500642001c8011450f03940084070105c40700011000081c0381c0d4101000c40f07030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 243297967 1250 243296717 243296723
    0x20405131803031814160e0403020309010c0c080a0c05090a0e0322050a140a0902030106021c030b13060e0a11071118010b1c0204060210020f090424050d 67
    0x28111109903021005082120340584003444110340c00800300e075416409080403407212000707007035016101e071b80c143e08030302140c1c8644000c40245040102203500401140c0c2002c0342440c00c0b034170400c50b514144488100f5a040b002c040e00c00c0159050030031000c0d041c0d82045d90403c403205001c550707525910000b901c01000081071a07410502401c035100500e04607400301111b07509007125070507481e40003007415110380f6807259854003c004a81e8100d41071042d1400040d00e90303004150b00d1503052860295540c2c03001c07804507545590b00340701c0b0b40200f4402d5004c01c0c90100020b0807007800503010400308014000c3c3d80109640300140300041404002c032072041880c0400307080403490400cbe00d280c0324050280400d1000326080014008116041d000e40342a05018140c820442030301c400180480300c014170000d0401035903403441003100340401500020980c3c5c145200f40c0004da611550490821004d01800000c150081d040c0080c00c1d000000300e600140c0c11800107042540e00d2175a070703003c1041030000c0d08806 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 243299217 1250 243297967 243298001
    0x10305031c1a06130302120624090f041a010807090e0106030b0f040c030218091501060905130b030616020f0705090f090114070906021b03032508040902040513 70
    0xa00d0b0303e08001c409000d1950041503829145566034011880c1c0705c0b00c0a1701e000b0103030088010000704902422610002030661008103141c0000c01000c07507040c00014100c01041c409240005e4200301060800c3c0021f0300c0548002115565180d95070341e6106036502a54500c0d500308100813070240307414880c540449e0342201d6036802ca6124404609135265010b0803d85100140300400300250315005295401003041c081d065600d858034503902801c1c407055000d02031000011900410801b0750143c500c0b41600d804a4200191481105180004100b01c1404c1d54141c00ba1400b080300100e421400508003507065000e0f03401c1d4a800a000e5074403a115801565880000c203408110000075600f101903111603840000601002c0041801c440744104450901c0001c690010034080580c1c1407102c00203c10054404012208000d03001a899001740405d202465081c0340d0b010020003401d00c4000c0303185801c4254155101c2e212050107001c0d52140c042c1600a8084242440b13481149210b400d00c141084480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 243300467 1250 243299217 243299261
    0xb090706031b080c43030215060303120f0702070803040e0703020a05040302030a0b01050a05010f0516050a021203070317090c040b03121314120a060c09030b010305031c 74
    0x200b0794483c94040d00071445800c0500c075610a0180c04024401c0c01001054034580c605000c8902da000c0007038140032a072800380c5004032480026000500d03112080e40c0382c1c0c824100c80d920320020074610301500e0002480c1c010380348103011241c032a0008460041819071300342d440c9103403240b1510740e41b44600d02c90303548101003450000748128030a5010303207001c03407551031302d18642a03407500042d00e0003490800548440342c030040100440d142449541c2c00903d001e01f000843e140c4400390280c80360054444411160100032020f004000c02800010359255008082c0c1c400d8000c940302c501d41c0d80d0040740045000c10340000410002c5031007503101901c2179940500514500c6096811301000d414034000b416014410215111050304204000e0b250344103920103d1004d072454070210b0b1950301207004109000b10300c00141440c1c1054082041040d4039000361020a10801d030070341c1101c41403500c0e407000d400386907980000b20800034080000e1020007070000d00c2d080140e81100d03541084804541290101c018441a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 243301717 1250 243300467 243300521
    0xb06070302150903070b01180e1b060c03092206050a260705090a020c060a020f04030b0709090c050702030c03060c0d0f06051306060f0302091309110d0b09070603 71
    0x80b0090780403440c00252401c21070790b90342e840f10b802401c1c0c000329021001c0700180c03583c0740034510a600d0460145001840404600c4a03507003140c544010341c0c2c40c01024000340882c13551710100120b504402019202c1c12882c4860817035030405201e0070183c40c60490038910000342c1840d0440c1413205545241c840c101009070030034560002c2900c3e4818032449800360300c400281300d56402d40c04900c2111b000d603001da80c451800400b0341c14003000034181e1525a01c140700749900014181c0644056950100b81414180c03240307001500c00420a03800f014125003040d030b00b110003503840409024218801d40440b078071070365040c04150701c40004488000286030103004c01210440c0c2900403602c0d10b80409400620507407218080390225603141909842581c03688010002141d10128003080700d145480c0460418404000086c04070680c94203402c142c0d038480030700500380100c0030003800400c0c0c40102043c900203054030740045045411600000b103030003114070000c0d883e070190040c0a071056400103070340780e0030001d01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 243302967 1250 243301717 243301753
    0x8070315020a1b230f060705070201051e0405100305041a0709030f050f0f191b1701050a0c020309010e100513080106080d2d0e0301021c0b06070302 65
    0x2c10b01004010540741c28003290626851140501402402211a01d01c01418109103d5008421100b8907078802403a0460303000c00403d045421408078600300b5616011400101c0f420302842d8440e804122942d43c00c1c034892400034006204a40040d18200304091140d2410707411138104a802410158102d1048080300061443c0c460b0702c0100d6050584006450f900c80c00300d005a869800c0701c065010780c0c0107000d00380d07040103421448600c01004000d44103481c003591425131400140240101c080b0140580c030380150580c9200580a1659450700c9001c046031000d0182209407807041c02d90f450900c20204091001c4222103c80606845010030300c0c82400a000e400d80015650608105007031001d12181411030460700700518901001003001030405051606240c0c0358011035041c801c05000e0342400138076800790210b4103a00c200a201c41e200c07840c0410350703102d00392441055155100007003c8003000c04094a440440e009081c0401560128609105407885500c5020303000d0381c0008050091140c1c0c0b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 243304217 1250 243302967 243302977
    0x70e0402040f030f0b1b1209070509040602070215181309050d12050121060e0c0a0b040603150e01151b0303090b090105010e01090b0307050a08160807031502 69
    0x6800146000c1d925111854818141c3d04100e85a0f105a0070740410f11440452460b0001405003030601da000180450305d54510900b00308244080305100000c04254040c4005c03001020301074540c030380900c1e251805c44029441038008a128107c0d04190414400c500e40c16210a041000c8500d40c00440040030440c2091040c4c3c41290300948031069840050014807100703021000c01d441d4145001e80c0e03040d44000b5208140c114070754040d56807103080702c012024040149520340041c00000c0986d4004440c90500020420550b048a20710f4400030f04240e2900c0184103c0b881c6a80c2000303400741610f00f002000b04940300c2c3c0340389212075030014090484e01040a44464040f802c0503c28803c105142d01c500c200e1412003900840e94400030070081c8031049404940c0300001c507008003c0c6606245c038008000e00b06000d820455951500f00070041c0c0c5040007408060300307000700f83c040c50304d558000c002d94070504905180c00d0707203009040000c1d400f0b10014455098940c406079000300c88040c8020b42000b5005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 243305467 1250 243304217 243304219
    0x6010e0402131a040e0c070308060f0f09100603150320011214041e020d030f052206110a08070201080a0f090c1502030a0212090307080304090b030c04090506070e 71
    0x2401d0009000f03036401442c0b19001a00000d8292a5403406403226103201000b03118040d8410104038800010303500080d50ba500110803140700c04a4080b003c04078401c0c89103100495000034200301400038101d0043d031044110b400542d02800710006210f40750b004c0004c00c1c0300c020000114602a8070a050311718550a140e0b40040c034100181119285400e4143d541d4003201c90b1111a9120500040c0031041c0b1603080e0011044400c029100080e5010a0700f4211a90000c0c00b000081e101d0f080e00f107840342c0111a0507a880d090a09030b00e111400c6900d61901c0e49100780700c0458000507000010034800b280088a56030001c8044e424504180c0056441c1c07003004040d260440d948103d1003000c524644190381c0c400f40544c040e074100c54107100448044000c0d03280121300350b502c18000004216800200c0c02003850380e0010450f02c13601408040384c82c03e42290410900c070f01003c14041008803e5901401214100f101180c070000a58030902c803c0b6080441c002c1c1c85034210a001424880c014460348482c108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 243306717 1250 243305467 243305497
    0x20607061e02070606060c020619030e0d020c0f01080108031804020d020c0f06010b03011404020705010b0603040323030c040b0901020a05030c010b090f060d021c0f080a02011406010e0402 82
    0x40c46030300400c1e451140202900c0a0b80d01107100401c0c0600c52080d00080c1c0b05505150f50f07041c43c1c0780c00050312400f450002080c1000700c1c4010100180c481e03000004d018001104032541d03403540702400307511245900703500d500034070000200419035031081356081d04940d0310a02552622583d4248030403280d1004003a079403c5a004c20240c40e001845d44001c1c81d034010304a002d080d0804c1d42141c854100f16040e400ba4100340c2e003d10050041407100311000030341d000c08560059079464240b0300540989038216030700da80007001108101c18103410107100c0d000850038030070384c03600300c0004040c0031201d000c1a1403c000c40c120502060040b01544001086400c0d0140116094103090703640311407544c2d10072461001c2c01d9441c0c594031603550402c00080c5e41c03c104c1083d042c291620700240070408076400488040c0c4181402c54111031141507584880d002981c00ca007000da1103900714241144103034003500255005600c2c211207503210800413540b1038046c4005945e00080e410720481000301075008908014a204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 243307967 1250 243306717 243306731
    0x609120f0d09230d020c0102070b1c06120309060201110904050c1216030606050c0d0818151527062b05010b10080403030908040509040b0603061308040302060706 71
    0xe01c04220f11410520705002000840b40000d200c6401c101c035455668042d58031103035000015a802140c02820f40b450503613030035280c00b40ca6031041c070003090300d6818998183c81e0070800f0448124042c03800e00001c1c041d40343c45280075900d110403070888610100e24440e402c4180035852181c03610350002034000703919020305030034047d0310240e8203208a010780d031054100c1c1c00447c1d649880b13501401114014011030402c28140104240e84940302e5a0702480704c801c010921700000d020000500e14107800440c00811190000c00c0080e0009040134261517000030003080d10343c100300e00d15005d46400c00801100b8040d0340c0d9002c00c4800e4149001e4050456580109080141c0c4001c0329815041d401c0700a10400710031800a103400e1050840728030901d22402800c003100701480080d0810502d80d0415490b1070001780404036418903900f24090307900815800f0021405100c01d00000070303010360098108800390341407500d82d03680d400030101d80c41c1e1004000050a11041015180c03100141c1803880c015000401c501c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 243309217 1250 243307967 243307973
    0x1050403060c0816050a12150f0e040b0c03040f0f0303020c15100602150705090d02040203070309141b0910030b09060f070e21011e09050609120f0d09 66
    0x5290792003040c0001a00060410501c144c4001d00c180d1a102c0d1170401e545080448040107040f5032500844a000c562901444403d542d50000744c14000d01409040d00c00903601ca08952400c0502620300352a099031240c01720f40603220b6402120f00542d030040300f0780d00084803940d030f2145000400d44180c0c14180c1c00c0c0460301c040d042c240640041c00d05030811404840c038040c1000000099140c00c940c045510414204990031418001c46800c105642450798032100c0c3c01000070326020320100020340260020080c0403070507404d600101c3c40d2620400f1105158407101d110b259841003403000320703030034400c3c0035640000a0809901c0729410040070250b10b44030310341765180c144010a0980b03100c0800e034019410010303284800c6505980003880380c030f0000f4203c1140760024101d5007012014030f038001c2c0d00d810312034441c007003d5101207641040101d10040380d141010010b4010800c0e503900342c07070501445c000140c02c42004540305c40301202001d00c00c3e0034040300559811464200c2200403402c80c2c0d80303c00003804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 243310467 1250 243309217 243309221
    0x60f04050a0c111603033c0206130503091003060b0f04050102150106020c091e07020c0a0f08031605120c4b0c0627031f09020105040306 60
    0x218148082002c94010702c4140024000c1c003e0781442c2d4001e0700034106686103840041d280300110381c2c01d49008001d40044100105002800510400a604581c50741d001d00051070103050700d035001d058003514840ea4428950203c4414640b134000c0241e0401c101c58000c2d464900341c0c2401c036625500c0d000960030b480e403800c0401039010b6080c5103080c800200d000c11403903904101c900e825111250b000c0425501d80301d00655500004010035229460345c40000f018000f81007110160f0320087c41801109050502e4040e48420f22403800714050703400d041000c1f402501c0c4d14540b40440c0e039110020341c41c00300c0c200b140e0015520008070403516405a580d4202c3d01e45500005005102043e201805810054901c3d125502e80448104849200c03103280c129290a111070755800710500050a111485400c41100b03800c040a10048503404a400f203034100403222403404215141c0170070351090810210310020540d8500303100c001200481000700514400082070781090301d6803803060521505050f00d075982c02d02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 243311717 1250 243310467 243310471
    0xa0e09060a0f0e0a0c0923010608040204140f040b01080a0302030316020a08070606060e0d080d15090606020304050328060903120c0806150a0507080315030f070806010603051608060f0405 82
    0xd00743c083c003c0f0500c446d5081c0d115100700b0000c7c401c4640c0d401000418070301c040c200144240c070148400b140025040d5107841e002402840d0a40d030350210a85040b200b072242c500c03c02e0703e06440c4481000004aa070900000d010f0780c607940c040e00218210303664a150a031031801068260000c6000f0032180c0c00000345c0001c0500035240c402e40ac0400e12601300003008090484d00314219103d0400c1c1ca0310200030811100c216a80084146008615100d0b80d02c00c03100c0041c020b0788409241842c0c035100094041d4040f000c1c00598500703c090300e011340d003105005902042c8100354400c5140c02e1082c680700140b00e035403000041500ca03040103420040001281c0ac00c8030030900242010410703c608004c12440c00a1541458100c0007130214140b02007001c1c020704602411100a045070400400315800d02544403240c0d0800400900311800d1015134078580340c45400c03500c00c880c400d12440c40003051440c0a030080512864000820a090180c0c4000c212000c500240c003079900a003c00054244544542c05098 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 243312967 1250 243311717 243311723
    0xa050301020c0f0105060319020f0114032d090c0108131b1e0825050a0801090308010909030e22110a0e03010207020d0212030c03030f01050a0e09060a0f0e0a 69
    0x440420f0b10107121909544000305142c0c805d030080c05c014030048403000032490010340c056072005003140704040169221a0100780946000302d0102c20400c3c0500040c00328032120911240c90051003800e52410702250605596800382e541052010715030a510401c42140d0004a04c1d206064005507602ca01005400f0b0600d4484803001c040c03010b018140d0200301217040c070081e00700c801942618129481780c8a420301512541d010680080d4001c14003c020032480180500400d200ca4455980001074002c05981c00b0807400b04400074000a2a003903940305414085403d91100a40d03540040100720920003400322001eaa02000030144044012510903401ca09200c20700c8107950b00c895040c00350000c160a0040c4c2c0c4a68010400c00005845814021741056815500710012203101d8004a041d805180280101840003000b0083c0021182000c2e5048500c00ea80c40c0300e10700e40b200500d0444400407501c940c0550300c001c0c0450121405076006000c0c07600d5000000420b02121300000d82005129034040d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 243314217 1250 243312967 243312973
    0x80f070f1208060904050d0809070f0e060411030f0a0b2b02130c05040308160b070c02090a05130b07110a06020d05061210020d090609080c120c1b0a050301020c 70
    0x50304040d04054403c3e00040b00f152100100d1030142c3e81d007507032504070a00038020040c00901158504604108a20203403003e44001d420351b0f9121064035825800460740303540705c0c60512207103446041d04d400844e4001d860701b00e2661450307580d006251010300303c20131103560410b1b040744d48031000681c0c00c0a0400420071995034000115101d004000004140412201103940703485c07580010b0341c0c1c000d0111001c60788e020060030740b02c09896280e0194100c04410203490403048004000c05030707a00c055444050780c801c8403c00d45c0d03070706d43c5220f40b1b03b225802c0700c40e40d000e200d2100d81840070410700284117522030085e01d480c0c00d004803480f12183c10020261000c55101e6000320302440030080d10302a031a40900e09844803c01c0c400103040c1180d590350783e00050346001d607001603c3d100610803600401b40503508045e00340111812403a20400c55888107401d0342d403a0140625001031240d40d101241c1c0070320201d400170816821801546140c4170000b583d001d03481401000e000a117a1000c1c000b404110700080b000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 243315467 1250 243314217 243314243
    0x504080702060d1b020106080a02010c06020705060c040305010c051608130b0414010908120703050f12041103010e010603030918060e2d01081c0c05011406031b0d080f070f 75
    0x92840c40e0201c8040d04c07000c1da41440b6007403000b6000000c04200d0385409107020711805000d42007010080c0300d40400501a40a170804119a000c4c144000f44200c034403480c001c0007145000c103c100c034203001e8454601c0c40781000034002c0c400b0542c42000fa00e40303c0c0240b640a90441e80d20491480c90340d0040d4000584a1f8800010080541c1c014914200404296019000340540b800c0c4a800611420760010140803020802809402400b001da400300800600288124207050170400500502810058400d609001e1224003030301060240b1400c81c0e9150311458491400c000400420499013181080342c0ca9882c540041c1c0141c030700c5215809440d001d8021b26030302440c441c180b02d03441800111030840384503282c0104560701c0b000400c48108000160341d00d03103004015208444446445402805540c2031454030300001e4401e000450064004034111403800b10002e040d4218401018072459101c000070400c2008980389600800180101a00480c5400301c0e60340c2d1400c0c58559494207403900021160 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 243316717 1250 243315467 243315491
    0x6090b01030f051b0307110d02100501061b231009060c091a0307260a0b01020703200f0607050c1503040807020121021c050c1c0504080702060d 63
    0xc40c400080c0311900007409940791500c001e03240c0542c04e030303601d031122000000028400761080005034080d081c0041a0750344c0c3c29100c840250395605001030307041c1052510300002007103400b44903030303520481080f45424441d90341a21401c0800511006c00041c0100034414a40039030070500401e01068107402000034804510b0800104451601c605281408400e110510051001185100780041d54010310381e40c0340e56003102203400008200300f10030502041c250803c800701c071084806104401e60802004030549280c0126030f180840d00c40609a01180344c4100844400040c40d599001006010b0040b10302c1800701060039a4000d450a865940218010b64a42c0ca0643d1032207071050a03046040741142481e44846165100380c0368020305100103a814000030001c49500307581c850010f280115140c00c600c166265100603503a0380002310303915010014280c110745100b5130b004159043d40d034031000b44071004444001c0801600540c1c5118040c880540160383d0b00e130040c0420024100003140d680c05181c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 243317967 1250 243316717 243316721
    0xf080601020a0f03180902040f14090f040606030f0807032c0603040519030906020d0201150b03100317040503070b0a0804150f15030308060a05130b060d050708040219060e0f1306090b0103 82
    0x4c0c01283c044c00740ad20341548181c2c0c2d0480c885030030510703800c3c55003a05c1d2600d00c0c10000030040d96000a10500a4565080a00c00c03050090520240651603404400140160180143c800031504c440380800c000100c00303050901c48040c680c018400c04c02c49020f11981049080304104030030b41200080c0203504180039680d4180301c801d6240000e40001d22044910560901d44007030180290b0310810030100008031003103c804200c2e001103070420041c800d5880d19400d281c6042d4054018940a48903034200015136003240c000f1520704811660320401c464030f403a0f903400c0103548000504000e50361204c1c2400e050310054423074401c0442030b016071040f00751315600c0c020300441e2009145078031840e074008007002a5202e9600c0c41442034040c8500040016411000a40c14006c604204c10f80d54940360402c02529041888140590b0084a01c60741550703070240a849051414020207000581035001c00d941414110500e0340c2c02e000042011410181c407480050440705140e010386002c9460341d46071600d558041c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 243319217 1250 243317967 243317969
    0x6080609030c1006140111010209130b030f061e041704080d030b030f0d12111c14070c0b1008060f0f090102040609050607060b0904050303070f080601020a0f03180902040f 75
    0x3c0541841181e24183d40421482c0b1550103142c1800191080742e1881c1a0030f5045034484c0d03c1c0107103000740124400c00b00c01d00401d0b08041301d40c06845000c0c101ca5500c4000640700e0311070f140d210324171410302c02070403403410400c0703009402112800c01010b9202d08002804003e407007e041200002c06200c03d40075402002e4035075050380c0360f0203900210b1600b0446040466880b100701e03918280902c882040000120041c200c055015440a0020405841800040101015403401d8980c103200c1054001120480c8040c00d84110002c602c0c4500001c0008819002159020151100840780329558000050808104a079817140d030102c0a801c001040402c070701c0441c0c020701d0702c4000b18101814600041c1000400b4000c4d503100f10704c0419001c0400829400114843ca8017030445101ea080c90f10301241d4980082d00c104000c6003403c03100389040b034411200588101c0c0140d0040041d2440c4da01c417800c840900c02408d4042003410606800e04a0b8004080c4006191400c0c006940d1407400e03180000011403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 243320467 1250 243319217 243319243
    0x6020a06060609050916050d060f1505120112050106050405092b050d0506060c010606020a290703020c011b020f0709050702030306010f110a0b0601030b0f061b0106080609030c 77
    0x1240301401582c0360b500c0c0306035102a00006c4031008000307000d01941da502550440c014040d041101c041000700141100301d080707500d070b03400e15030700c24040e0350050b00d5074068458a406541c800307800410106c00005c92460003240901d000140c003907181d0300410306864084a00301055800310320804010351041810540811903010340c1c017400703000004018403520070801c0ca0a0350341d44a00110b816640c03013404a1722220490f90081100b15500c0402a480307015124007a0381101041c200405000103e01c0d11565000380e80101d10185d50307901c0000d500940009909040a65a613081804000e6032030303280d881c0c0000c2c541c00414440511001c0d192030500150030020308181072409000c0041c1d0000252a042042420500c1d4407003422901142c08600031080d00059204641030003060140310741406003d14000c0e6400d000c03001140c03041c0700580184181d10780e0028401c00201c0b214102d03c841072980d90703002c01c002041507951a0f402a207003c03003d5594018680001074012141c9004111500c05020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 243321717 1250 243320467 243320477
    0x91c0e130b190602060a090302011103011d0901020702180411040911040e0a110108070516060501060e180c031003020a030c0924270e060105030c01030b060412020d0203030406020a060606 82
    0xc10304a0003512400050503140ba1b84d138440b1f1030b5108050013900114030620000301440e84940e56212144040c0c0301d00e181940c0103034290004600b620350107000f100c9085801038141c641441c07494100c030403854001881565280003050508240e603a40340100040c0358081d030b10394400c0d00301000422084030f00314035000415600480140c4001030880351442c90746030003400c0c502c240d42c3d40c0c55410f40342c83c810896984c0c602e0040104050410505501042c1a64800d664a41d0f910113503200b072042d584e80c4021140660300c840340014260400810003140e001640c0080c100f101d5a50340e000c545415216001183c4500c01b20000340414100c6101f2604590310f002a1400300f00102e01c0032a030710031228040c0b0146c0c0c01c101c5051003c620801c1c010f4401c01e145401e0b08101310b20307000c000980c4404080c002d0b40c0c800c4c054900c0b1403502d5846030140105003400104424030f01442d2085070241c0100d114000c03600a00c1c03244034038026030b40074000360004040580280902d000e291403e142196140d81041c81480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 243322967 1250 243321717 243321719
    0x30816080a090206120906010f0f1211040204051c0b0604060b0d0506030c0a060e0f040e0304060c0507150906030b0616030503041505010b071a091c0e130b19 69
    0x5a0003604250030104005000402405078004564240700d1030340c10320035859480090000341040005c4850485062043c440c4401c1d84035015180c3d0410769214100e6141104415040400c40070b40410348011030040c0014070b032668401c041040c0340d90008422003410386a00d10003003440300501c88140c1c00102111b080103500e05101414180740619400420290307590b00010396142c0381000104084100241522007556640c01c006101c0380c220180c1500034540342d07010805d207060500488070444083c0e000381d802e1504000301150035014149003512107108920b070001d0226501d040315480c624190303550040d06814028090b00751000c56001c2c81c0200c40410584003030700c20203a40c4155840e450324106980340c84904100b0000d042c1842035a211610300700000540750030000081402c40d1250303d00038005400031101c030344050011140c054050b0000c510003109201e07070318001c1540918600780401390402c8240481c4100d91155054440c040d60b503031410b1654905280c02a03058500d210a030a40d40e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 243324217 1250 243322967 243323011
    0x31815010b0a2d111501170d030506010806280602060f011e0e04060b090c0a1107050a03110d0503040807090e0a030f03050c090303070b1f080d081b160308 68
    0x800020950504002a00c1041903200b1402d1000021105c0406502400e55071070750380307603880007034001482c040d00d1080c01e06005685009002e098443e05058482284d255511130500c041c440c0390034404282020013800d1111504e09803002103029003800e900038032072841e0241c101c1201e4101a080f00d07040d0264034540016240b101c0400c0c1c4152414401c15a04a440e949410400350041c451042d40c800c912208004d600b00b6940090074418043c0d070361303a10b8281b1088130130340e8903034015010712500000c01040030301c00304201060303104090030041d005030303585c03c0c4640701c6c107040d40c0080d0080d42075608850000c00c40016240a60320181802101605482074613541c00b5004558001e40d6400b030580700c000240302c0120b030307405440000b14058180c076640d42c1c4074034041e4140441117a5056101280310200c20310300c0503142e240c100fa286020010a505082c001c2c06a8041d40003d1001600303900102880151036403050140480713081d009801e1b400c0da00586009002008014116480b50010fa112000c2e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 243325467 1250 243324217 243324287
    0x6030702240702120310261b03070b160204021e0d0b0102060a111602010e0406030605040204060806011a0705030405100c060c18050f060706060b0c01061a031815010b0a 74
    0x707c03401c00d100c44120412003480d45010714551860301985010320580c0f081c00c04060705a01000140c21025110308035120701c0f5a1045001d2507541c409041e1140e110040141010740c004d100440c0c00f1100b0783c840600040500720342c1d500c0070010140b00e0743c841e130f041c44032560100030440d0024010401805a5122030b005201103000c0c00304402000d50f1031a24000070f41e402584d1410007410f000d00207200c200e44900340000a0701040e14201e000d80d20f8440001034400020403843d040c0c51281e44080c0324003120000c0d201a98020503015500c0d8042000b00003200d82e81d6114122820955459a01d1010220f081007401c079a000c10019003030100d0703d58464041402c584c00c1d02c090718421030341e58100c0fa65000c007203441405203407c020701e0b05152071404500301d00e10001900001000c6c40c000c0c807803148c40b812482c500c8030303583c40c03824a51074041c808500024860580071100c482c08204684001106800311405c0d02c0f421307404031509040c00200210308507400030005039003141d0807030540c20003261000c608003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 243326717 1250 243325467 243325469
    0x20105071e09091a09060a14190b0406080a0c0804021012140c04170a120c051c0e01020d02071203180b07050d09140108010506030702240702120310 65
    0x1c0032411090300c0785414029034080c0b0207003061803000c00002c021076112182202468180c103120f11030001c006a0130703240c0354040c0c2090ba0007004000400410302420301c0320b01180713441c2c8a920364a03000700103e03017900380b0341c0900020402951a03103d40d017060f14031300301180e0001c0c00550400c0485000c02025883c0d0f1644c80c0040b5242d40303006240741d101014020018180d01c40102c1d41c2c80111810310000741082009041991001801200170782180010f003a5551404400100080e0840031146c0305140102410f40485000f90f0a64052440d4050401ca848020030406c501290548243c0400740d41d04011041144000e03000429803079040004c1062440046d100c02401c122614900c0000782410001c02030040c19490070f81a240e416500d000740d101c0d800001e0180004102c0b0100054200101d120f170710205406840701d501d26401c100c01d0240581c4024110001d6100d2040001142080309042c10420070b68103a0069050411400007424456590051006c0309000c1c01885003015622007120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 243327967 1250 243326717 243326747
    0x40b18040b06040207151505010807080105090a02070210090905100302090105040c0e030a0809040c0e09190e0a1a013303140a0c02070e070203090d05031b03070c0602010507 76
    0x1800c1e65072010009000381c411140001c2c40301c0d10080c0c100c0d1002840e0740050101071a00c07103040c0607a5484da00119103a1800b02ca51200085032900108014206803a01079040482000302514001c2260041900000704c0300c072800c00610010010002d0031031030f10a140d0012007415050303004e00c0c1f460300090100041802814031950782c0c0e1540300c00c50f40c014a590601154050180c88101c80d203410000c003103030031170b030003640c000c50070f01d00b02c03a00c000d01c00c088140420100500040103611110540041641c20818840f20966210ba0703030201b80d00c0801c03803144050300c1518400500c004418000c0c504841c103070b000503c0824410030000844c4200310100107071010200c503000450100f601c0c202c01600e001900d0564031744408040c088410415003064044445c15000c0b45c0d0a01e0b554884c0905810040f40c3c000c0068105124030307121480c0014a001645009130304807414580c0c1c403440002d8a40d9650780300c02d400d50000612104000301d03842c03a180180b4190000b006980382c420380240c0030440c603817501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 243329217 1250 243327967 243327983
    0x1142205040e0d1409030a26190f021e0703031e0905130f02031e0609060a05041505030f0706090e0403080c0702010c2102120403150b1c03020c040b1804 67
    0x1805010b8254130030340d104a0700c000c0031159440300c0c03400c181038403100d00d072407800d03070720380c01c085410301140f20a0111400d09901d1004900d0360f2000400440d87c0ca10184ca0f0b0904601800c1c8800b15010b004150214010b2180340c0585001c074910b00c5e000d480c46188003109003000f0440b040406c800d9401082180840d00301b41c0354241e4640c0c1a20640700200b0f14082700d0a411807001c400d1000301c2401d84503a600742800200491125119002007209000d42140c841c1c0e40300c88030100902035406d0940080311b02464404034181e0454995000074140580c7c8054010b641c0c0c84100c0810802d40d01881040041c02034800d50449810301c0d4174002c02c03c02004044001c805800603040003103901c01c2c17400250b40b503044001a03009803454546142c1d25120f080c44c440051180d4074410481c00f402100712002c499201da00040c0f4400f141240c2c0c005005108441a40300e1107540000340c55113480c2c4c01c0f00060170f100380e001d0000342a040c0d08020454000e20340780c1d07004210015040c08440200101190099000045 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 243330467 1250 243329217 243329237
    0x30510050103270b0402120105060d1203061d1f0828050d0801080d03020a050714010b0d03050d110c030a141303050a02030d080601020a0f0201142205040e0d 69
    0x45aa0120020303010485444140c6540c4028007441360b861034050703442150a0580c10007802c00040c01d03508140e5040da07020b40391034004030000300f06041320030012405003004542e00e0381e144800d00f500d84680001c000c0504c0e03244c04010740303010b11a1302c40e142c903107500070000b050314180042030303940f1003050908640b80c161401d0100710900d200c1c0050500d4a500070122024200800c074001c095100c04e2041c0c0300244500703d610080c01d03010b8000c1e10f1405039aa0703640790a001e5503131a40e007450034150303a251040c0e542c0e810701d80c146a00c0b0308079480e010900070384656582d0540360b4015011078040d012a03100f91002804514207039030020088400e1a10586803240e100710b60005d18240314411083c096020741c1c0e20744800000c00402041c1910240d008409482e02200e00c0030041d14030722011600980141c11101000e40050080c3c410104424018503105580266001c6110210b80c090040f480b80d03840c000d10401166922003080201501d0705950501c180704204070400c0e90b6200c0e01207a48103000880f10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 243331717 1250 243330467 243330491
    0x30c0f02031c03020a0e03120d051b070305031009050c070204020705010605090109090209060a05061902010230070c020306150301110412021014040324090b1006030510050103 77
    0x2c03140381d8681540000510b90a10000500203610040201c0e002c9451003110f541d0f43c1c43c0110b4140b6548460350003852505074051070040040100230110303141d0003010100005440744900c06803402a110361600c9690b81008034044181241c40e0b40075200300d81c1403d017044003880c001426110f1a80e8191400341c0c891440c0d1074601c0c05081035401058102c0d4160000180a9010390060f845060098904501c1c035281c200a0100b242c2003402082d402920401c5820076400f5010401d8811034480d100050810092182110403c0f564592141742e04c010414102e00b00035640003002c0d000311482c1002d040104c07044c0d0129031145802002103030040382c0b905032981700392020b400403024002040b108603a2140c07540501c403070300d01d50b580d800d034000c0b0f294401c4000042d0081d007507103e81003034448480c0c1c01c0610356607030103508071010342070120074481512a10000b08007030b0056110761032040c60704810901d4461402c006242090b4410800c140c10141840380e020340b648035010680c3c0c82864081010780c4410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 243332967 1250 243331717 243331723
    0xf0705250b150a080c09011a0409020a030504020a090504170a170405010e0708241b030a14150612040516030501020a0f030603081215100c1a0103030c0f0203 69
    0x502030407000302502084080d850300c940e50000610101c0d900050140c41e03036012951402407156054121400c1001400842c0300b01101418692100703417060728164460b103d0900341d81240f4813402c08681c442d810300c400c41c0f5000100310041e00c2000700c00c00c01e614007074890621404444000041c5440001102040c00e440356800e200d802c990288544d455080903e000c0c0d0007011050340d4a01c06000e52600454001c0f00450b074484291761000b00a0071035480303404818040d103409003c0821102c03101e07070305070410b11404010314400c0c402c80300006181d03290034103403244da84d100030070f48600300e129051030208a6590b18269113010070010860b01d034940d203600c0c0c9185052900b41d5190300101108000008210054000f80320000c00b55854090301080c81ea829003c0d18201d0100420241c01403080c841e04403408010598000ca1008281680f60381c201c1c0450819038a00c4481e00026190015900611100740c000442080c100705440c3c985604d5a180148080202e4000030103044402d511542503540070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 243334217 1250 243332967 243333037
    0xc09190510050d140c0102071d070302040e010b090a0503030a140304050a060516030b090708011806030c060c110d0203030301050907112a03010509190204060b130501080f0705 77
    0x98030000340000d40f410031000c400752400d81013240c2d100b0242218000c0d48042108011944803419003400054141e94202c00385d900100000200b503400c0c40006130501c04442d00500030320030b0008850381c2e0300c280c44c10710009a000350000750082d40200300c0000d407543d01c03584250b40c001010341d100d901c4c0e880d50302c3c0207420f04100510241083e82000c0034802e0b05070f45203841111b43d0403507450030807200164030b0600c489101c0031203056010520300b00040021160012003030103407800410300060196260b5581d240c1103d030340e03080180082c0c409845081001381c00f40b00070003c40780c200e980420138081a80000d0b42c9100502900d4003d404010108854a0207942c0100c950b130340300c4003a0740c410b03001e500d8007029600440000005092600c09a00c5403801d062196501405403500903154424544860b00341400d00306d00d08903084be03901d01001036070310758580103040c00e60f03030216030310f05180d10f03100005244440203031040c01b0903004c02041c4460706030008111786050000e071003000c44048414424103044049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 243335467 1250 243334217 243334219
    0xb0307110c040c05031801050f0609040615080708070501021f0c09181b0305150415050d11041104080d1202040302130f2715060b0a08090c0919051005 66
    0x41c0f058000f101c540040c0514400d10320312003010039019001d900c50342a10307419661494005541400b10b0341d103080030380407903900600900c0d01059940c107680200c2a101059440b00103c0d40103d5000d0046036401c0c0081c2001700b070240300900b07418540c1640005c00c2c1000240c3d140d00141d588488413500341c0100e02d06001041c0000d0310f4400d4081e144400000707800009403c0107601010350074075031850700902c030303c5005088011900200c540220300303203c020518180d00c03050240c0d010030000b40a81da142100c510003403150300d00703280c001c181348188000d40d02c0603005c1e4608110207000500c17501c040000c0504207201d241c9007111140d400014031074004d02c60b98002035080080c1e99030580d03a4800179003041d00c50702c5820004001000d03540500d0440048841b1841c1c4000e2100c042d51400304201d64100c1e06e01400300c2c903000031f28603660a005c4020b50301c1001e01c5030204402e40d04010716150140b0910041c204240c40d0080d051408c2075040582d01c81000d90789080e0f40e51280800c001c0341000b8a00000380c58 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 243336717 1250 243335467 243335471
    0x40e150a1a0904030207060201140705180604170f01050c0a020d140f070f0c14030d14091002161e1203030f02160b06030102040b0319020702040c090608100b0307110c04 74
    0x3884d0500030b40360034003406528050343c20011405101100d10008038030a9107569909030400e00100b00c1004400d288074402036126009010200742c0214191110480c041c03c00c00400083d07040500e8070307080d02d038010115084040281b00545109401180d5141b4440c0246000a14295029443c0c801400741a2456000c003d0101c4d01004000c0c0c4a050301c1074507805038080342d00541e41c480e00040c0480d881a05c5a8142d007042e000036101c00c0c010145008110b0690381c040c2d01b0320520001168060241c03440e00401030344020840f441c101c0c4815400c1000c0c241c20005842c504540109030401c0030024824441c088280014107028941320783d20500b01c0101c1da10342599030b00c0c1e00810501c003e02c185c10b02a00c080d40d42e000800c81e6131505100320b80403540368040050642e42d8050904401c040b88400348110170b502000080700503601d5200b00b4210440e031b615142201070414000401000c002400d07622007118a1100f031201000c01e50613a5032205031881c0c0303100c07403100e0032841604241114075441e070414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 243337967 1250 243336717 243336721
    0x6030403210207110907050d180807060504120309050c09071707080106110f060a051906031a06010e030a021009030c0b180108070504060c170705010b040e150a1a09 72
    0x7410340d0000c0c044a0301448501510411200c03c00407400c400f501e0030b00108804104400e149030741d03504078078050560060001009881510380b40001d41c031282b000c0b51099664020801080507524410820749200d00d0200044001c51b51401e58a000794488180320b41040c81c002080248548805404c603100b514415605d410041c0c800b40c1307010400c0c01024040381118482e0078070f422002030380c00500d04610300106550740314059200014074000d064096154900080f0301500300d0140103000041d4411080c3d0b950b4428001113400c170102003d0b003402e0400c050ba6040604940c8c0001d551007020b5012503010310300b074004810070380b909820380c0c1c00103115090f40400010079220080c0500140b001c0071001140703a200807401141c0500742168080c003c40d80900c02480300520403600c0c0030050303200d0440103259180a0341407050640240703100b250070341c0d114420641e850906003e03142d10902082c00800c0d10009a1004001c1c0302d04c0103060042da41c0e40c0703000303503100c030000825448209800646540480c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 243339217 1250 243337967 243338027
    0x1180303211e050109200706020a0c050f030403030f0816030b03011b03050103050c030304080d2303010e06120609070306231003060c1e050a110102031915030503070206030403 77
    0xe05405d02c950b00c00c03245011060f01007698502c1042180148010b0800d01d8000c490341d40000940080310707054104616844803100283d030800425400708480001180c0301e51640c81c0051440600034645420400004284844101000005120311005060200f82030307010070042401400540c60144548200107002c01d541da4142e440241a240280c090b1004d286034401450740d01e1086101b000280c2c2d11002c19510b90740c1c402c80150b10240c0e50802d160b03030b44c408015617400c0580c000303070448a59100c960041c01421b1900901c034101c499141c00190030689048000d50f034031001f00741300281415444040c20b0994101054060744c174078106401440c0141019044d007442202180404c50b0800c4c94031942e4888140510b008030403540e000c106064510030b00360001c4445820856284007400040b00da044d03d40f00c0c082c0059031140015008485078610801041d000b680d00e03445840d4214003020000344042200402194003503501070710025a85e45036444c044551110021009480c540542d01800203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 243340467 1250 243339217 243339221
    0xb0411040f0b090916091206021b0d091203030e0601060215090604020d030f11120a0905090603030714071203030b090124140c0111070201180303211e 66
    0x761500840c003403800c01d8a401504103584074031000349500c050b04000141044020030070448296403585402005184d403500090a00224a402128480d801041040198200500041e00c3e102110f008105107191000003500803041d038000c08529400200300c40003071500076040f8002c00d603e80c50480350191707134941d0002d4881120680d00030a10350340202040707034050001100c42c099038004040d600030700e0096800b90b4040b158001001e00348409021000ca26040600010174000c04810388941d81e900d4a204c0103190070040d8008600c1070030594144a507584000090b01d484940c030440103032818000d5458503280c074480b6841490000700c94081a41056810b412010022900b5200c029090340c80340700d040d0510b02140b00d004228110303d1003011405120b444419a0102e400514a281001c03900c0c0c1d96083d6240419001c083c0c3d0710003d00c0108550f400160300741c050084003401140030341143e400070014408c1d90041100c8a03445110034805501660043e4407007610b115036000320904946010700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 243341717 1250 243340467 243340469
    0x150512010b0306150c010b03070e04051203070c0609110906010203040806130606030f032a1115040504110909090705090411031005010e040606090501050102030919050307060503150103020f1602040b041104 90
    0x4003078040c030070000ac5c60960340806180160307444400745c407046e0368120040300d00303420042a010400a5030801000481c6041c40f5004425004414400c00202d0800c240700d0b104401a00ca1411523200300800c00c81210042036054010800c0100000d103101c40e814084080c0c0341503000a042c1043e03610000042681213001503440d541500d001602c0a40d0203007801e61800c0340014080d001c10491408403e0310f08d0514070107603401c00741c005040c0c00e058441b0041000c5600c0550103c00090303001800358914500a4081ca0b4000751000003401e90b10304000c04a030921402600040c484840800c20a81980e81400140d00600034100104481e6960f0031400c003254106440a41c0c24524040000c0b82e003080e140079490603a44180c0045141c01683c3c000d0048101d0380c030300303d030409800001002c101d03650240310250040c640c40d501d450301c0342040b1102440c20460032886905051040007500c54008403031080d00e80205225619221401250000c03070064a000c40c0030075800340c503010000c20012454070280c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 243342967 1250 243341717 243341719
    0x21906021f0b0609060d1104060201020a0e030f0c010f0c05061302130e030f0c070902070f0209070924050c070f1d060918100f0501150512010b0306150c010b 69
    0x40c014454820401d0101c0742400000e075000380080091404604080c801042407000399a000103104005030800d0f600d42d049604144010303500051101c010f80d0340b04a01789050304048024019250ba10034007203070b546122903141da050200301514040918001c08000c40342c180c105c0180d0f42c10307150114001090510f0304100301d1040100e20400200c0c4103240c4900c10381142480020b41c6005c42da036071004c8860308081008022807144200100300e540f0240003902209101d0081440c1c04681403040102003135000742072104014140c1d10411403034205000d41a018902c10050030701d00c10000320121501c2c880d050092403284505400000d1078840ca11002040325000041d1102d0108039030303c00425442c06503a0580c0c0241500302003840500c403020a00e0780b0462060407142140d0415a03281c050780c3c543c40c05286035595403401041000d04211002c40c0ea031410340b038041e161003c544038030300c94a001800351021250300070002a90f99250001d0701c00c8080031030304059072a481c2c11b00e80c040c0a0410981c40c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 243344217 1250 243342967 243343003
    0x31608060f16020c130207050a12080609040b0103080711102c0102120d020408070f0306050109020c0307030806120304030c180501060203120c040e0c0d06060809071202190602 77
    0x290209440a980c402c4942d680e809010184903400c10880000c19443d010102c1d168200a40c0c40000c00070040385110324802e45203180441c51880000d450340d40003c10250140303021004101c0003d900c1203107103054950200600703032110803504115440700700304071a40d0b40183ca413501d1410110b400c0320801c101c0d0b1440110482074608202900b2000c5580741c403100c1e015038010600030700c090f000c1d20b000d003803611003a150050902c1da90340d1205161450341d81c4861007844600100f8028440c040c00340f039001d4036004100750315100d20441e040d40c0c0d0348201000a420010a50007217481560f030440000b4401901804480e15030f5140c1c10009e407404801d101c0d41044a031040741c10141c0d420580200d034101d0386a900a541442c072440c50188070b00e080100042c0000030304000c00b0500002101c03895014850860490b038844c002140c0c8e240495080341c0103903052015220030001e9228000a4490580d444071400d0404400e0750300c04140c003040c0310303400484032202142021075401d80c0020031711180100004a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 243345323 1106 243344217 243344221
    0x61403131205031e010303080402010804020d170903070e01031713081603031112031f05040219090614031b090a0803030a0c050f040303030b031608060f 67
    0x705030041440401800000c074002a15001c80d81c16800c12200781d54159140034060f5240248028100841c5400103821900d550b03251800d41513100385150346401ca210501005034108081250080c400c1c040d00180c02028060326074100c03500701288140858100c60301030441c0c3d01c081e0404107100044200011a041c0c100006c904c200d4404020b100c01d40c3c00c40c50000c3c0016690500b1640c142d008205049640080c1021280c03c9403020304d007040e540c51020303224190003000d03901c01e0398403c0c80070410003200c041c0c0c20030840d48040c030b565410b2155901e0700c0d000e5940381429205e4000c1c400b41400000ea84c40260b400e407007a40032900c032006040ca111000091032566054101016540020040c00700340c0000d402200c4120455041550900110141407030071805148030103020141c80e46200d6109480c18030060401d40e40f021042c0580c5500c40924641e134510a5a40c0d205507031490300 = true := by decide +kernel

theorem cover : BRFrame.Cov 243165467 243345323 := by
  have h0 := BRFrame.cov_init 243165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 243165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 243165467 ≤ n) (h2 : n < 243345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
