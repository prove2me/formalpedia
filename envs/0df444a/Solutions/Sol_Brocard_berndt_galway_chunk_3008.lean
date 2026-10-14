-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:23:13.618829+00:00
-- url     : https://prove2.me/submissions/f7acbf84-4233-4d86-bfbe-496230141670

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 540827338 ≤ n < 541007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 540828588 1250 540827338 540827347
    0x1050405100b0d0b0c1b0d02070501050c07030b130501110910052809082a18040b04031214040c0803040b0906030a02160503090301051012030819060605070203060610080c090d08 78
    0x1086d62682c1118032414098007d4440004155000350b044074a085c900001070410681141e0740c103030800c03c0140c05c0b009100301d2020340000040091288000c28010011440e490f122100104940c95200e20b02d0b20302004002e008107205a091500b23035440b202c008001460480c1c074040001c44030100301d944140326a02c520380c40020304403890081c0d00100360501101003414480c1c4405e0040c2e024582c0380e86040281a80002000305220060241e0410700c24070f00207561300001014101510704038980c80080700145810700c0100409065180000c00145010354242468032914000310301500700d64a0141e14000002208459039504490103000c844001007a58150385c28a50380e82c1e0400c004850203503182502045030420005100c8086402c514613242403140e1603078048a22101c080c01c0c116550b0364031340c0e5044880d04103000d00c4d00603022541d5615216005c45c0101442c003c2c014103400e0154410303c12045100b540420b440d9800301c0034000f0b255a4031055004a80d45d00007220003d400c2c02404503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 540829838 1250 540828588 540828637
    0x209040204060e091506040605030a0b060a020c0108091f0504021216031103070b0910031b180b0a0509060a1416060e07051023030901050405100b0d0b0c 67
    0x5141403080d410660b13603015243d840300c0c1c01011048080703204036070000d010311080003028803442c01190311001d1484041107101051000c5111038002c15600e03000341e0800e4030b2007070072960b0251032654810458002842801101d80001001020801040208075110000501036465003680382c45200507400848069070610509817070307440494002103d1b503e202080c10300040c43c00056036000e403490042a01d140c44e00e41d4003000101500c0784469400d144d1a4000d803501d041e5250701d2103450746050b40721010908074400f90035484511642100750390107000e0114510b030f194800d09035000c1c040d0a0f1003103540c0c1c0610340c41c2505c2c6c0d00a6410384e007100f4480080ca0141c0d540e040c24200d5031403846100244180207545804988a21150180079013100045442200d218801c041d20881d000c1c222020408114036651164042d6104139054816a03440300184030400c1400c1011800b044001e050401961000c10000b4600d110600c138050a4010301d5408104280501010ac41e80da03180c0e18520701c03039481c004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 540831088 1250 540829838 540829847
    0x20102040503070b070b0604050406291018032405010b18012c0a0f15080106020715080717040609020307120b04060f0b1306080105220b0703020904020406 68
    0x18041c103800307406280307000141c854440050f02c281c1c6500032500c0145580b0401484020940100103440454540d0106820070b014401030380400300d4910710200072170700d4250a2021510f07070014444108031601c81845e0078500300310200c0e015668040d98640c255148031000454903401907405803643d625250001441c0300d5440000c04c1c1c0154425001d8460f95440700054400c4d40803000980000e03040082e120b55070a400c00c0c460300c49403600810389624581c81c1c40f481050860a600001114448106002c24123074021140790300408851000b42000360800d00328901c03030030f0054106401d1041000104400c0b0f40207a03001181c550300c2880082003450036082000207400e5613030040e80240108100414a0544c0d6001820051342010700b1290549456980c40d009142004417140016501c02c201c070080c0e914814161a0320b0000000480c030301d414002c0003804c650f07001c4e04420502081d03400d4110620300d4440c0a038245608916006107540d201c0300d064005e40b1a00da0325a901a00c006408100705400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 540832338 1250 540831088 540831097
    0x7020d0c09060f0f4203020306040501050a05130b01021c1e0504060507140102191112030601080708041703010b040303020f01091e0809040f0905060609070e011d060406020102 77
    0x4003c2403940e42507940000b20841100c2d405240d5004404582c0702c41441401110000410020380f010003043c8046800e20a03031600203042c0400180c0c000090008a117000d02485015040031a010070f2114500000256150b0710384c042c4c1c04001340c9680c0501410303802442303180e6855070b0030300c40c2081580f10b0440c02031603080102c451000c4810550650120319100d1416a0181c0b1080e4980b5481c0440b02e4549507035070341c40c1c145171070440c0d90200036454207441c0c505940341d00c524198a50600c3c1d1452a216141880240690804e03001018401c200030f5a07440328003203410030303d10b0500d010342c0d480d03504040c42e080034071149203180345000000010391242400e00920071640031b54240c5000140000e4103078282c9002e06405441208400b91481503900410714100b1414855480d0f03514004000700410166180c6448205006668000541c10303c101805186d900c8181140c4035039003458a0800a011640e101600b030741000b0400706c11508444481c2c3c81c03801601d40042190b512a0f640c3c55000327010b90300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 540833588 1250 540832338 540832349
    0x40e0a1404060b041503121107030c090605010f0c050a0b0405010902090103030807260c0f1b01020d060503011e2c0c0f0909100b01050714070e010b0c060a0207020d0c0906 75
    0x290044c0c43c1815402c001c017802c1079039840100405c10503103080c411201074404c07000c200e595016880e4004009003400300b1010003407048210120340d681c40e020000d0b011207005820441441318404071040051808100409810384c480c0c4040d000d13489034108070340101161f8030029000001d480c000300900da006168070f4414141580c2d0000703806000c43e03644000750b06c4100341001e0301d40300e000400c00d084481c0b00078103074623a8059001400c181060243d03403040c5031083d0780449640d60001e0400d400050038000e040103000c0a400a000a80c500c0510031750303207100100d00755240da90352052107003a00451450761041100319504040e40c006280b1015840740c03000c0980d2407090392081c003071440600b495050b0503c204e8040024040815642c1c0030a8050410304121034100042081041e0029541c8a035000e01d13110340c03000401d05503040003600805003806800c1503011003001d00610b003d014000800a0340304800c0c80015884902c80e101088008000b0800102400119140850a0b400c198800c408966 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 540834838 1250 540833588 540833591
    0x1090b06091303021b060909010b2223010207080a080c061b030a05040218010b0c1002090a05190b0f0705010606050f04060e010c05060c12150303040e0a1404060b04 72
    0x71108078500e00b441c0c03152400200960045405085d4405c16050001184107010300003d141030328100008580c0c2d0400d81054841d502c010400350f51800290380107041c0500320700802c03150941049800e030701640000640d0711207c1060a900056a4400d112502c000c100e8041256001c0b582c0786070445540c0c001514000f410301c504030015000100c1117040030000c003040000300d41b440d200c18001e0310243c00010410380e0010099044c03448005a2031800740e0091600040b8280c541415002c01401c00c110b203a5114002801030040d918181d8460350200c0855604442c4111542c0c00b141c022100c0040c60ba024410016010401414000c19400108903052091008014440c0c0301c600543d214011398240104415081c041840698000c4d20111803006050619514007180d0b56906841c0c00e00803242206c010030003040c0e4060792110444059017080c0c02c030900e1030500d102c4d20701080d0f49008511601c041d40b401c1e400030a9855226500c020300c60100042c85105038541818040083c041d10b41d80720303004a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 540836088 1250 540834838 540834841
    0x18060f050412120603080f03040303051305031c060506070812090303010e270a0c0518090a060c09150305100509131401021c050403081803090d080c01090b0609 70
    0x2041288a41031003640d1050102c00c2d800b280903000c48216140c1005030102a949080c007101080791480604052800006107690b2840c0c2480c0080c26507401800840c2071103d100080c0e00050030102c01d079410030342c2141c1303000036042d12003502e036000d0051988410b4001200050f04802e000d5600700078107800040488000c40c0e612009800383d0789110074400c0c00e43c1c3e0042203000c982e0001c04400d12411810040d0301500c100030300025141d09000000c0d004650030030311020100440d082000c418000c40d80c44120b601058a0406506900d503050f144009003465070758154800f030720b4000c000d090040e24024001d020389800740480580142001e81d424031032a0b000010008842c58441c80407032007800c0800210421510940c1c07400034540e46003541c0040d654080c003180c0018a21700034401010603502c0d82c00305080c2800c1c10090300801c1c028098401d49a03c1c40900c080c1020000100c890440c0159036003d1150058101040a0b0040b811046099401d00880105005009244034000c050072102d44641e03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 540837338 1250 540836088 540836111
    0xb0702071208070f061509050106051204020d020315010b040e15100e0103180b1b130e1003020402030a0c02010e031327021303060b0901060e061303061806 68
    0x21503816100e05002910308551007000504401d02400b0524815210410300c1c1c54240c1e16507082c0c55481900105c2038454000410060305540186c5004000740c0c01d041d40790104059003035401d41c0000344007078080c89010f10418119141041b01109200b0f803800150801c1d40c40780d0022400d9405803040c403000c843c524011403519809100564a0440003d105000486074000103840080d405811641416560074005046007814a800c001161040312101b0302c03032400c240350060341603d0307103026958084180800351400340c0302156201991001c0c0c0c0c006001da520240c9408049010fa00001e41250002c0f080c02030702407954105042240b0150028860399404052095586c091950200594100d204081000946558404543e03c604000740101a1000305605090343c0c003001001c11559001441001807080c60701c1402030742c40c412152124907525010004080b803d0070204684214000500344456001d80e42c842d10096500603014842601c9880d5071980c141c0c0240003d9501c181031000040c1c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 540838588 1250 540837338 540837343
    0x4120306050105040626070c0b010e0106090b0d0e032115090718050402040618230405070c061a010f0201200c070f080d110a050d03020d0f05010807030b0702 69
    0x684106a42e841c1c10b00349001422101e0700c0b40c020000848004010006c039480c0c404c412454400c5069440701c500d07111451801c03044031075059001c3c010400040005020322544582c60340e00704c0c2c0c0c0c1c0d005429160350740561090000d1203414000042880001401a00c5011b010b49010032120032040340b22141d902c200040011406192550780d00c40741b2100014040c07402907d01c1daa0039032030f400301c154000d41c5580c00f14049a00c81c2c4c004c0c001207071115086641a500741c10716031020b8550180032840702c03440f0980c9a03000810004441c0d01c1141c9031400112110710442c1081c8142d50480c070f0905c9081500031068008829180d2510b0005a840d446101030078014091406c4140081e00c540d08400c46d040b00000503500602c6035042075000b40d603070004140700c282107402c1c050002040601480d44070010007a0980d0051115104550000717a00e45004c00d002007000c048607408d6080141e40c85028188a000800c1a050041c000a180c40008282498001040d000340c92084c003640004c1d07120408180c1e03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 540839838 1250 540838588 540838601
    0x3040317090105190507020f030d022203120c030e131a04020a020a06090f0f08250b07030b0a05040204030f020f030c0904080702011e08090114060a090213050315041203 74
    0xb0b20613518407620080c50650342d0040341d11080520544200580344010345007194000301c10070442a801080c0a59078800e051402e1101c0c1c040040d44101007440c1d591a00b4180d50101620300610840c5800c0405040c00350401114240300208940310901c990040130008202901c20810a01d07032086016034107040900c00c403850720081d81c0013800e000e001503849201600c01944d003140c00c01503802c00000000c540303958166080b0302c02c910860300c4110140325403101000031400e80010a09005610b0080307041840c886812181c1c502d0081030444060010544600c2e042d40002d41080c0300246c00818003268080c2404854800c680504940e103081307003055500d032340c41107907554000c80354000b04000800c0300008184070762040c10032603d22041c2075529200340403010603401c0440c0da94800c10034205420b10840c1202c081c40c1071424580c1c20000c0c01f10782c464219001d446203c0d5070000380d0402c106043c10910008220003001c4400003109034021110000003a54129080810f00810204150103402a107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 540841088 1250 540839838 540839851
    0x1020a12021602150f07030c050d020601050a0605092d0f06090f0603040302010902060304140616020d0c03020a02030607030b01140306150d0e1506011215171203040317090105 77
    0x140b542d40781a400700148210b0101401d03030b074030a00700aa043c14015070000392007a14065202c591681019003082401c1c58280004001150855001888945c1d030b910b14402c1541c4992600c1c40d100c800d46408a00a000c080040c0d0764941c21482a13181303102131152411000d8001500d59110f03200c1c4c15400c0c8611409202001c6034894080c800005030780c20281c0c0a140c3c0540a403001041044030341e00416030b50740c000e82d03055541c000b08240c582c110780d404000d11034010142daa8100006071851900a40361070307c40e0080ca0400178440c00000a00d40f00b001740a04090b001801d031003a606090a0140040605c100c01c680454242e4007a14010080740003583d01c1040d0191080f02d440c445032040444030381c408007a40820b2551040f10403044d02d000c00c011150404800b02c580440d040c1540007415481035500300c640800d08208c502090800b0b105070007001c582c0300002c940040104a8416400d00715118201105030b00b02008202c1810b50103220b07600d05081c2080710003481d0b00c800026a09030bd10481e9031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 540842338 1250 540841088 540841117
    0x10c110115030b04030c0b010b180d050c1e0a15030b0303041d04081b01140c041a0703051c06090c2604021f0e120d020d081e010801020a1202 62
    0xb0008034204044a43c0e11a111b4540b008804195564410b21002c003a000940c85000c045000c400030003908100c05041c01003290168000e40c100d503585a540d11201201e030f0300440d06000d1126033003000031404c40544030018012610341c0c7d01d40d0440ca1030f4060026226001900b00650102d00d4240801100c0c10758040300c405550321200c810440858403000340048600714002c00c03007101d000700384410740808039408800104004900b4207074000d042e00d001d0040c20800e1001c1004000c201c81c00c091035a44c0c01c0000355096298052030030191340c603000c3e080348000355900003184100041d0642c1d10810036221210410440d490303441404035142c944402800740301c081404076200c03070b10303140402c62540184004c2580502d440c501c0c1d0140484000ca1140c42c0200303c100c5d20040716481c0c00000d00d0090340c600c0b4000c11130002c070b4210080d990008030041a00340003003440421108030041c0c988400308440c4004175501541e4451181b8005d40c002541140014000100200245418001c94440c070424018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 540843588 1250 540842338 540842381
    0x91d06040c0c05061602031e0304020906010905060d09080c151008120405011206180c0314040305040e0a090b040b0a14010e0c090109050a0909051c0f05090d14010c1101 74
    0x9505503541c50300d00c043c42940700500c0081d48c000e22002d0640c810400e40300307509131a410300d441070001115028090905104a0348800d00c900c5d166902030b00d940c1003d06002113070102e050300301500103100d0001e00b00281c0c0140c100c200a25042c50b03001c1d50085584040c01008640e50312011034880c42101c8441000a504001c00c01c9150310603107090300d900242c010002001035039042d01d524400310f482e0080400741d0302c840d810013002c0c0d010300c205052901d05e5190b900c15868550713401000d91046014010310315444102007500d0000701c0e4404580c40390f010107100a181458100103145040c01ca41960b4404c0c01d1421200d05400302c00e0006040f1480e160700b5904a84600c0c4e1018079541010440c0c2d03041180080c40042d081c1e5032a0390140052524010002d4140f80c40c1c00c04600701800f00310f62107103034640da151005601e54081c400c520001024585036444081070000a410329031b03240030292040f0a0450b0220f200700b4190300101080340c02d42c91f03803810480011911420f9441c030011980c2742d07004400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 540844838 1250 540843588 540843601
    0xc0d11192d230d031d0d1101181203020703121e0e0102031c060302151206011b1202010c12090b16031404050a020307050901050d020f01091d06040c0c0506 68
    0x900500c0c0c111100b07200b2140100e50381c00418440349107401c050740000d50001900c4043d608030f0030711a444a01c10f84803164140300584075880301409010005041200a00981c84101d42821400c80a407800d000341440c0380c0781a040c0256a10380a0105a5070103100c090720345030150141010700d40300b201100709002550007900f000e881d032001814a007419400108980b240401e80b565064040d904124000510a402c40c014001e03400c59003100344d1543c2c1004c20001c042c0c030512112096000d00300b4607101c000e100500b800010904202d000c01072184004905030010b10b6010f41091168503001e0351040b2100481c1c0301090709440112001070700481640e004203220750341c50001c2c1c905503401410085000400f0700510003a500302210141c803241c000d951010210716050001500601084406001c19410400040d411000032a4002c3c8681516100221540d009911340030013004444c020b0201100c00380c00c210501790741154402d200318500a000c901c042d020341a5a0100c507000402002c1e60341e02c90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 540846088 1250 540844838 540844859
    0xf041b0804060b1207291206030309060307050703180614070c12210e1507060902030601090603020307091103070f0e0d0303020c100c020c0d11192d 65
    0x80c0040d50055102d070707041c800507213402901403601c002c080c00502c4003500c2d111010300c03651024004031800300003102c2d02c42044003014056500b003503040f28075003256031a40000245103200d126041078000740c0110400c41e40c00e4000000d098164000d441d50a1803195010301c0b18880603860080401089200d16a0007a4440e51009008050b1049048040c0706407511003594902018030710844069440c0c0b8140343e0a4281168001c214001609080240071406000681101b986821481d940d140100e8100c0612160380c015105180d0081d041e80c0e07003941c54913800c6d401341400d03000c2a40203101d41c420000d0151858421580318611291f1084c1c115111544116603824400c0d501c0d000f04291101103012981d00c054998103a10b00c0790320010303500d5000e81182400c2c4100e40c409401b00604d461a041c002c83d801003400f814500044440c1e101c5a8454640001018900d4040d1600079000c07070802c05942c80c0c4001c03c0e10503142900c4100015598840502d0b603099a02c0b030901510146800c030400264088 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 540847338 1250 540846088 540846091
    0xe07030305190c02040e06041b0e070c080d05010620030f0304030503190f0b130b01020703032001020409061a07111c0510050403030c170c0a0516060603020f041b08 72
    0x15181c01c0f992040760360001001e840c90307104d001c11142c00407818881002981e407015820a1120701c400341c095440c1540074104403074014a0304081c4041c8a0070001000b820b00210707030f110088030504002c50b50312094024801c60320b82444001c074803800c05040b541d003075001003a1148100420101461941d442d60220b54541024284194407281c1d000041e4160740c00f0300a40b1803040c9500400a80d581c825002c0003446550001c4503a00d16150988540869034007164402c1500d4040c1440400c03e40c100c03044480074ac40402c0c0861065202003070210321050f40307410501c1110301100005640c500d140941e0304052007400f6008207010f00710504080907003081c1003281d041d4194120485c0307445415440b690b0a040c0804290301c50f06903a10204010560540f003180c00c01540c07440c3c4214112040240807680c00c5014091180740600810381c018030921a1040341c03a00350148210820803002072520342d01402a0740401c92207015580400c6103141450711464000306d401d109202d02407803429a00b0744e8203400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 540848588 1250 540847338 540847387
    0x60a0608060a1a03063402030307080606091809010e0712120c0b070503060316051309020418140709091a0703060902340b0105012d120e07030305 64
    0x40f51070210031540c1d0500c540b0303105060700328401c0980036010118411910f09034500c50f5400c104c0c1d0040d803810760783c000183c81e0f200d142d5081400703a42c2c560000241c654020450f020b5072109408c036070a2208110b16010038080c1004d44024000204030391050341e01c0723003c14007a80805e0b03000100e00c6008509007500a2054811505000d42c903003506803140d01d00070204580c0710300814400403d01201d03040421400c04d1a14006050342e41c550306002c0040c10013a002e203000b104445c1c07140d0b0311600390f6540390b110805034511321401315441c000038605500c4a82080100900c1d5000d801c80006140003079004825225034010f0101a4180f40080082c00d0380d80c1c050701039020581e544001080f09545440146040b1040d02c0f011000c1f0030101009078001c0d41c014041150700361030844003100180c000703805241920006d003007540083e000030390144290742e404000b00c0301003545900440300c1c20f504014412601404100c081c4580880281210364459482c030000f40000d00801c8407880086111600307503131510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 540849838 1250 540848588 540848621
    0x1602010f050c101d0106050a06050c070f090c02060901050402030715051e040906090612060b130c09090c050703091403030d020706020c062d06130c02010e060a0608060a 74
    0x1080c034045151601003880c01c501655202c48261807400040c2c1007140c013100c040001c1c02080c0c18140803800c550414803402003440004100040600b00c14070202015040d5111081559551240003601a18802e01c130031015003e4100410007440c0c060181030710407238024000706800d034a400c40e54140f01c00c0080502042040a00007441108000080400f550003074001c80e0f40c5a1b030074402d401048550962000d00d01e14540801002400e04a600d0880c410ba004200000c2d00703400310000c10244208042d8111840345080c110401d810307003040d0104240c0e07058040030001c10202e86825180e0340710b5000040e0100b11941401c00081d08080d4141b42030403c0681030724100007150003801c2c166000310f54200c5155401141d4941018410802c080d4411380524881a64503055401144410840d0700c1440401010b5000a030283d02c1c0e41c11440022a5080810010f0100301c12000b40204500d0916060320301442001c074420717070528002d100540d455040680801d4451985400c0101084a80601d408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 540851088 1250 540849838 540849847
    0xc030912031107080c0d02100318030903060f02030f060904051908071101050405150a1b06020d060905070e0f12060c04060e22051005060f04061101021602010f05 71
    0x44040382000052070300c02c0c0c80e91140c80c440b000d21103040c80c5144c1c01c00c4407185d000c04080b0500d83d4404c24441c0071300d0780540e00f03c0320100441c10109c1c050940c400f04003800100074442d10042540c060031880c00c8034011101000802c440070f201c1000d034070003030718528407142d07411010915501c1c0088506402a12030710880c1c000c0744000d2000204025001030075510140007060f0803041c802180400450700d1000d20f000303481c26080000050704419882c800e50340c100c1c13000c56420691070040241008070040d04002d5891540b4034070b0b0000c080e500074002004004d00740500002d1100c00741c040c0c54010300c06074844594050b0f9980038005410140484182d01810710f41800c0f841c90401d1051901648100071076980c0d07181809400340c81000c6050010340200c1800c0480610141000022080410030a502207640e4441c00c50390080c0030510b400c1294030000001d03601a1260000c80204102d460b16103400d40d144880d000d1b0a0700701c0c000d82010072012100420b41400540c4030723640a02d80b9034154103007503092 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 540852338 1250 540851088 540851099
    0xa051b0a12020a0201030f150b0307230414040b01090512150f0906071403041401020c0d050a090e0402090114130218090f07020d0e06120a140c07030804030c0309 71
    0xc0341c108045800141e00724443d4442035590500403086c030030034845c42c14030106642002088096111b403240034150580800403580c0c081c802c11a4801104000426042d5040000d495107078641c0303e413081484a1544083c001c255090600554155100503103401e0400c51500c01405152980c1000700b403030a00606400f0040c182038020518091042e00b04203c2041c50301415a40c82c8c140082d180d1014012109000d5429094000071039500070750105403007101c020a40ca0507806400340b4000d0914600400c40f4488900d43e02001810323011703402d0303a00e02000c142d503200040301c640350030380c0c0180d00b01c1498001401000b20800a910101102400e100c0a07101603d00c800304a810802100b212200d42500c14255480d2802405410880041a83d540c900f081d0f00c01a5031030112051801c00d0008030200e2001d25036a400030344a07401114103120076a45040064440141200d00402004402c000c02207640e1480c014190760701c480e4103462b02c40d05030b121910b06507202c90301848100c0070440099001304030f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 540853588 1250 540852338 540852353
    0x15120c0306050d0609020a051203031504060b0a0c2d14030403020901080705032118030c0307030b1014130515040c03050601030b0306060d0b060303070c15030608030a051b0a 76
    0x31034000c80c03001071800170741d00c10007803449503d1340414400d140741007040700f458401104032a0455460704c083d85004a400b00881c01030000f81c0c0c403414034a0808204094225000303005145000e200b002000315003401d42c6800c04a11181c1c1c2c3c0124010280d0540c280005200300b58541c0d4203071461021242065500e9000424040f0241c00c82e010782e42028208000c542001c10880307c0400e00c052460a8000131003540000074003c40b10541d4989004040790030882d1028099001205409800d648810340c030703800c010442c15130984030320018408000300001c6541003440b0840301920020640c288941c40c1002c0500500400f0b0000b203100103241c52136010f540e40c1d034420f1406680283d20302082c0c0b8a402000075040f41c6400766158000e401c083d08101403030f030320305422030030140c1d00429008454440d000801d140d800340000050081d507802c070340465081860040c05440c042266000e100f466100c0c4860354030b80c020410503801280b0140101d803002030304e4020a8a6843d507000c2100c100344280d850725a03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 540854838 1250 540853588 540853609
    0x4150b0f04091422020d06110a090b090102032b0c0e04200f0f0c010507090305060c0c03030f04051f0f0b0f061b100c0203030a0615120c030605 63
    0x60a8400014100310402c030500030120035102c024008840b43c58052444010f0f603010b1406440054100c3c9a46030455648030007170744003141c0000e001c000d003c42c9021416243c0d0712950210011030404040000c0405026088540d041e1040e40514109580307500d440c90b003080c0c1030346054481c02040c5081888040c03140b0580e06c80011603030f40c201ca03000e4148280320031101d200598802400081c420003003810042421943d00d0000e009805a80342e80480b2120070324000e04000030440d50030700c01408541c5510a0740c100659000b071f02a203105450340e001c1018580304a0007582440c1d0003c4c80043d40440c1d80c0c008003503201c0c0c000c600355030041c003c006140030f4081d011000304581942d03074071242d030001c0c05900c110482d45c0c1080d50f481d803c140c0303464002140e9000c0e04030100d10740c401038004642a40e0083c41000c6a42da0003100c06c0c003a1061503030010b500d0350400c4481103042464101b00140c000290311010303100d10011746501441e040e4881480300500001e41c004814540c88000008960f207c03400c01c003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 540856088 1250 540854838 540854857
    0x1091104150807021c031509020703090b0c010f0212060108090d020c04110d090b0106120b0d17040506040b031f05100f110f07051804020913051006030807020307090e0c04150b 77
    0x41d000d11003048810b041f80e4540c1100b199107105100a4000170381004400045d00c00314500240c44244803407405001d0440c0e01c0141e500c45001099151500214242c414044d61090b2550700196490030b208640d60390905481100581c4058142140b505265111a0885c0c1315501c0d02845e003004401410103564401000300d410810f103000411940c3d80c8503000c01c01070080103a050042c6120500003456000c1181030241c61500034403c040c83d5400c8040883d401090058074082e11583da030344040b0115042202e00d1012030b071200e0400e0368810300900d40c000c1507800c005d00c5143e01e12000345081300d0041480300403c0a10130f02e0081d0340c040200401118151205102c01420708a0038072050059854105080340c1c0d240c1501c0e0203100069a401000da68001540c0f400715921456604250745450720700c0000000032441c0940c040300b8043d000c0020708100d402070f000c69107c00d60320020b21084805080c0c41202903000894280b1040c90319030031880019000402c105c2c1103a0303d82141720220b90101511 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 540857338 1250 540856088 540856091
    0x3020d020a050d1b0507140c1207080c0612010e0a09050615030705490f030806030d02060a0f060302150304170c0d03091a010e01091104150807021c03 66
    0x1007070018031030050213002002000c140d00c5840500e2005400d03400f0f0924010481050809000c00700c1c841001100e480c11001012006c0300c0e1041d0340e401d5102c04250080581ca40116850b401c554148041121500c88410b40d10301482d0703107000d1404c26082000341c2410180c1c0d48454800020a030b0030040c2501411740440c000140c0390103841014501045a84000c0c020103240d4541c100c04504416007058210450b21000d00028030752200034200c2c1d620030700000040440c651003c082c0711581003640d644d284a9200c0c0655034030b581c0308066403581c064140d400168481c0b00040c03140344490300a40078440305600041401c0d600c2ea800106100c05206005001d00808420001403104044844240d000e000ca1a075142100c00c030310107601d500290b141c038402c0c1900c500c442010882245400380340801060891002961902450980d00e80c3c00e109075818141012550070041e01d495046400f00e4400040301480072344040c10644100d0801820b04065002e003003800000b9040c006032180031038503a0b5071b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 540858588 1250 540857338 540857347
    0x2041a040501091a0103150504150306090602090a0b3103060504120e090403090308030c0408010509010b03071e2c0f0403090f080327030a15060506030f010909020103020d020a05 78
    0x803282e00c1d000130380601c9810503042142980801c15a0a1000c040e04c0c1c050310045490300c241c9000382c801c60302d69400148020301c0c008101c030a0205c241d019042c46c0c942141c0003012199200a4442240110700d00c42803003410101c415031140000100114001c0c0d049060603400650300d0300c074601101e90450301502d215040307501c030a5006138009441c480c54001224220510f003495240105603444070b003c01000c1c10310000100c1d9a0319804010740d0020070180c0002c0c0f025250214040b8041c0111586a5001c0c0c480d1260200c1c928911016400c119800b400b20b0220385403424201355103116100c059900548904614400c0704102194032034815041c400d0810042d0429190051070a102a0702c40c50783d80200c07040902030034101004607400702c00078144404407000044003924000303401030401e644c141710f05d0a0b080200b201e482e02d22046000e07110310030010155200203000720340c4411218003480400c0c0c00011300c000c0c1450380c001c4c41c03c907006140040c205240408000308a85c000b48480c40828400311707 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 540859838 1250 540858588 540858611
    0x111c020606180103050619110408010b12012013030f0b01030b0a05040803071d0301060602100e060105010c0f080f040608060f0315150111030f03010f0f1202041a04050109 75
    0xc580c582c0d03080001c0140d403561554640e40c0d221382c0c003d420011019418a880c09120f003660300039489a030243c207802907550356655507550003000f2242c0514026594210304102c440410320a0b42c00c11440c103890400901d04002000b0708030760001035115030320702e4007081c0400461781c07085800c1107039423060020a429504508100c600180002c20014190b81801c0410002a200c5801e0381d400ca00c4505203c1c910401e02065808200d010b009402d41541c6003c40005411f64000307801c40c9981c3c8a44410451200010203080d01d402003402190b01045603900c00200241c03040c0000c03c0107501511185003002c0c0030041c07210040d440360b441000001c20010902c0f0380f0749041b002030800180d040300140400d0000c0401d5080791007005210361102d4818090b00c8020780d000da1900030782c558403072064942e80c240c40d104014154200380aaa8004071a0890115104080111900030b032100074a04d81100702040c0d0800020340703040c0b076403178a0700901202180c0f0291210f0080c607020307100910700400c000c000c88 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 540861088 1250 540859838 540859849
    0xa0b040803030f0a0c05040311061207120e0c180c07080a0c03031107020a0e09070504051303030b1c08070602090306090706120216081303021f020d0c030f111c020606 73
    0x113080100020702c1e003081e2078415a000300c11039044a40c0480041c2d0583c98180c00241c880c081c0350b0702c40a845594a040112a45d441031400c5884400e84034100103041500000075524004480090307008941903a1704089490851007107544000d004451501c0c106080d650601250003070010203003c603425500d07400402d07030180075602200f01d0040c0f441d4140b1020b07400055114030248505035080c840071002c500ba0070000c0c403820b000340c030b400b500038442402c000703410802c80345900300283d001928003403032110989041c00001c848400c1000c4040700d07071445c80c1c40e0880280c0c80040103d03011a420840010309490600c210b0348a1103085003d0100c142c6858000741885441c03d8080a00034410003a504a0b0f0403981402036400750045029500e076000d4440c00c0c10f10380c80c0781e00702942c880b0014506130b09a01d084000e03102008107945c29540402c1c413140065501000d03007000140400c100c13081c082d108922440149030403a5405c012601c40d0510071000142c6400c941a6213001600090104003160508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 540862338 1250 540861088 540861091
    0x120a02092d090f04150905030f0a170609010b0a03021606230a060b180f03032808010302010507060903210f06050603390310091802010e0f0a0b040803030f 68
    0x5100043d051807900d0740d15446a02c04204240c03100d650348481c42c0c4103100d0204160741e030241c0740c110b149664149a01010703004400d03450b90440500d0700007000a61a0810400550480e040300a60504003c544c40c001e40181d004880417046035441e00c0295408242c180c00b41c0524030300c440c40142e000c1200803040c1c121111008003641081d0b414118100640071400302103403104203c0200c0e40c504041c810000984141a4480d0340d6070510010400c45240c40c0c3c3d001e0822443c3c080000d50805980b1a07103016034184209100290101e0f03014060540410a203800c186001e61003032130040070400d192010041d801840e0036200c1d10031a44da06400604160a200d0f20014180450300e807405c2d8a00950a15100000028030425085e5400754440c4640c1d001c628003a081e409421010361289080e07409501500c1c4503100c0d40504904241c0404d00780c14091160000054060f07440b140301e4102c40302409400b812a048442e0810034101d0b0001d140b08119020784090080c0d280074595134141010f44c003a00300130 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 540863588 1250 540862338 540862351
    0x90203100c02061807060e04060801061418090a03031a0409050c042a2109050318241b06090601150f09030615090e010c02060a02120a02092d09 63
    0x400d07000071030314440c002105c00072500d16280c81c4200348241804140030303110300c1d0b000400369070802c2e0000c0703071001005180308281078098034240d40c20031411742c084070146003d6a15203e15040018010003203440394101d17201c002d54a07032204000750706140c00704080300c505590a580030782004500c24050f1800d03024240b191304a2a0030031980078040304940000d81c111114220501a5503030f00c4404a8114100040210501c0b050030042d0408038280310fa00ca0b0b0111400a45542500744604640d1a0081182400500400840701c28541c0d0788000c4410741c0c040341d041e200f92840784180c00b075000020803445e440b41040038050407035940752000d95410140c0000e01c04041c0510030755241140741d40700031004101c0b50041c03400301e0310308483c0e4049100300e44d81f40c00c5001100d04000131020342c40415001400e1450f03da508940316030740c84000020883c0540303440000c1041c4540c010a141c2c02e926000351001c0680200f6003140074804440e00c07001b0036801c50100c2c04810040c0d40c50b14152800f000c0c056407004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 540864838 1250 540863588 540863611
    0x1802040501050d020c07120b0106030c03020a051b070f0f031a0106050d05100506070f0515060325121506090c0921050f07090b1507080706090203100c0206 68
    0x142031000180c8107008846030b50741410ba01092000c0d900c00100203100040054603130000450200c0e0800201e180024020000824148810124a148240308468280c5810750703609061200603c05680c6a10003603500c0040e6100d40c41000c00e0010300c07600301c440180002050100ca540c40c500c0d0000c840d40c841d40000e4030390003441c4010400d15400c86d01711a504100b045000950f5561200c03a0b4880d980a0382209801c075101003410703001c1100010f8441e00e9640500300300c07001c010b044410305121001c2222000d0f00368110524000000e881078604014146280b200080701d240c5a03051405c02d451034946c2074035070122040f00000e1403103007440780c2c2003e024500b50a00c29001b0200303000d08207110074822082c00c080204c0c0305015046883c80038001b40f66000302a10141041e2841140c0d0783d40321130182011291034071040c41c0c1d051603d40003ca00440182d07010609080150300c46081642000509440c00c030b071504000001650f05025034204544941c100250416607000001e20303020008000a0418 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 540866088 1250 540864838 540864847
    0xa0602040906050a150906080903070b15030f0d051603030b090403020109021003050411060f1b030a0201061e0b1e040e040c0504050f151314070f05070b01050d1a09071802 75
    0x9130b41c0014000281c1f40e10307013016942602e902c0b882528500c80e1050140a4002c546e0500001d95010380c0b0030704665008504554440e0240e07201035882d003070301103407440202d60204800603481441c920400c4850340217040000e09140c001c0f011540d5004110340031001030355035070442c008500e00f41810181000c0c00d841c0800a6181558588a1100e0780010b03041c4a4940811f00c0304521414004450a410304402140d06003810704c410b10b40c0d00d403c54000031000d5400c10001081010b0311a0102000c0302e1218142d001092411050040d56804039902c1284010030708260210264081d000344010011403107207030000d240c0760604030752113401500f003c1e20450030201401151a0000070711030b007080030a010034029456140025101c0303a0041c1500791020300300740034082c2c2c108030010303154483d0969840d4a05804100803044400c1d20900e080248200c23080c10041c002800e106a4200d40e4030305c01c207020003105e40c04825414260030100e54980865025000602580c3d40120240c29545034690003035040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 540867338 1250 540866088 540866129
    0xe060f0306250f0206450f03070f1104060819030801210b060f120304050a0b0a050313031803060c03060801020c0c09041a0106110c030a0201081302030a0602040906050a 74
    0xd40002810a801d07807030307035809980100b50607040c000a188186d20343c160702548030f4020041407200e240c81a441c4600510702e41154811010080315910743d8808140451520313242e5800090509407030069070015521440420951800c104800703201003581808214507041c0d240050000708142c018031140340f100c031003515401c641d00601d503501c01d44c0201640321541c3c458020030801c1e9042004540d1205004601450f05003011005106846c0299050810241c40390014405480f40002e1400001c0040001800100007940d1103120700d4407038a0300d0442c0e044540003003440360075140c0058400d55070312440d01c1c9621382c0511441c8000c0410350300030340c2000c824120f40354070f814194009030700a010700c10000d010801c80001c1c04250b8100300c50340a105503111000284071903015080c1e10032512403e40009128a0001070f4030402c10f0f81696803804607a299280032038048102c01040fa014816481c0c10800141c1c1030024001500b82c1200002781d691415080090410f11580425140e03030002c22001304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 540868588 1250 540867338 540867343
    0x150603170d111603030b030307230a02030105041112071511101b0f0e031f0e0f1b0402030915060a0801020d0f0b04150e060f0306250f02 60
    0x40d442016941949a0950201800140c18121000c142c0c0220008030450141a9440720003500380c000d607400c00c0a4800c071418159684680740010380090940000100000901d052045641c14003900743c804a403401d501003401d49030292001c886099038130704120102d05158441285000f1003000900d0002c1c985441c1212161406429508101e4030408122855108221009911403200820424082c01211100c98084114200f030000313112058203000e0340b48a86035094114a0060103401c2c8105148481c194141a819500303503c1500d8440070722400c1000c1c09180301d1199032a0180221540c0701d40b400700c030b441d058541148140d1040c1b05100c80c081d4005101c4618503104081030a85803100c2d40083c61100d2140d00a0b0403a40c0001a5042c101c0e405411421059030b07819014040740003041e04100c00d4813003c0c8408050410948020407210301c0c030711a11900850301811288075240318001007402d04c107084441500608141c0d03403482114880b0310300b40c0140d00a0b03181c207003146442c8920094 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 540869838 1250 540868588 540868613
    0x1091406010507150b1c050601030b100803043005010c0801050316050f030f0723040e06070f090f03240c0c0f020423100e0702030d050c07060207050a150603 69
    0x10325580d0b122045c04c40c580300d07800c0101e800080309100590907480c80c50a181d54030400d000c210f40001c050800304190207072900c1c60505507010a0302441c102810404c0e00070410320107d404011080c240042c0d00d000d180404841080c1c18000c00020581e040c84131805080500181e0002c0d01a9104400da0072804443c0e45141060368411a00c01504282ea440000d1900003010144101c5018445000520b09030b088522600d243c100001ca01c0c041c2c4c90101040200c81182c00004200d40107080003d40c6140304144030002c0b2061810010202c1d5150907000794294810340040300c0f00c0c01400c21001d000340181d9101003040404610521a40c104420700600441c62030ba802081850345943d600115642c0c3e400000b07038482c140f021b0340c080d5426010301a606c088182c890000b4101401c00100b038100016a060f1320420307036130f0020341c03602100c41c1c00400184801000d1030913003281800034a00281850000b0454240a18000c10b4008090b0921107a0504001d50f0000302510b00340b410000121072214a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 540871088 1250 540869838 540869873
    0x131d0c060d090501110c0616050708032a0d02040801050a06050d0f05100203040c030308061002120c03091003140c070f03080403020a060606081e0f0109020906070b01091406010507 79
    0x2044120b1a460140d0240c414212403040c1e54801168104a030780c0c1c0090003612615192040403a0b020100d14184c1e6944213001c0043c00088003080002d41602244034412101d481c0342100107280c3c00c944802c44056000047c7c81c07030949400040411072158240aa103802045070741080001a1800303001030b4000c43d0080e4020200b039040e54900050250a0000c1c0c5028041e00405651f03a02d000d282500c145103090100300c010554002c0817800c64144540c000070326281d0b2350000c0607100003040d900162a08003c0c0d1a40b4544020404084a03031120003001440da171054501054501e986d200c100e850301c40080c0038800241044c422140440c0403a081c44425640500301031030140ca59080880c02c2107040e00d00a444070741030000000c1c8190f885404184211034227190718441c0c0301441040034104409a0f00d001e02d40400100501c200c0ca0140d00411503813000070125480d0442940c0c0d141c1c5001c0c000d91218520707075603860207604100005009658013060034a40170380f408040765101c600540700031100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 540872338 1250 540871088 540871091
    0x80c030a06050402061b0607030c0305151e0607080d0615021b060c240c04060c02060c01200430030309050106051c02030f1609020c0c131d0c060d 64
    0xf260664403000e0840340c107913013104042040141c800e143c2603900e00c004d0300c11500103842c0101d4110064428413505015940003800030401415800c2000000030107000780011070310780d003808000950390b42070007010300700e20540a0700e40307415070301a43c43c0c00c554407584458541030016500b05c01040c1c1c0072500c0844451142012024600d800002c14207074084e00400c10741d94031442c04254101c1e600c1500e110541000b0310808030169480300c0041d40c9a00451003074401081c2610300980040c507050b8050140018040d00000d072001c440c4a80003d1010100e280c201040d4000606014200f4848268520005900c08241c44a100d0b0300004250102450000d010550780740150301c200a0290040001407400a0880705105034141c2c0c45048050000d804078400d104a035040411000045414502900000544c0038883d103841d821001039440b907002c9541502890010010645e10281d03404c0803111815130006481c0241c030b0b20502d10034074075210400c050380b21002c40a1180d03200412149031402e0102c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 540873588 1250 540872338 540872341
    0x408030106050c0a0c121704080703020112140f010311030109200a0e09160f06090509151509180105101101060504050708090d08010302010c0803070e10080907080c030a0605 76
    0x94550138070420020044c8151079186000401c10f0706640750b0030410340a005900c00603a40803004039414480c034840d10846400540c0d041001d58062003240503842229079010683c05014100038003a13000c11100b40e02200c030300300010710512603d0311424801c0e6400794020042e0032000d44900c00008440300c030b0301070010701d00355080905844094006009100540d0f0841003820300e048201e4035180400103603c01c41000c0c050002e4016001300303280003119140d4460b8541c05040809119600c20002d0600400c1d04100b0302185140d200c0c980c80841180000c40119196403009040042a20030401c164016864103401400720781e0f035004558000c120704e418140d00c0050308400307890140607a5802203a01c540f40c0020132400d140c009079080d114841c0340301603a00d07103030740c580007a00c030040300b0f000190028411109030300000d030f4500d0095800c4441403c0203510381210703c0c0010400707500070104000007100d02007441101c210404c1217001800114020784000600c0801287d5240c02e24000034100303940361030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 540874838 1250 540873588 540873607
    0xf081311010e0409060b040c02120a0c140f07090e0f070608060109030515040c050307030c060c11090a0e070f0e0f0a140c0a0e0901060e0d031b06050f060306040803010605 75
    0x24220b61100d805401804141030a052102c01801040c040c02d01990030b2240f02503d651000c11404403296095030b1403410091001c20444443d40001803c41d05401108003a40030b804041052080b580c1441c40240301c0d150400054800340e500340720340f682140d8842007051348a10800b09540044c0d80c00780ca0100341c15038a0000494050b402c40c1e0000c0d0850250340c105105000b81c1c45d8481d8402c030f002c0c80b817851115686a0034140d4a15a910016220300410602448124450b9800080403409801004403103555800014a083c03000c1d5406000c040c0e6941c00125914018081c0382c1c010201e00c4c0340d10107460b24058101c5041c020007011006000305c40000102000820382c419080c42403031040c41803152419074420712040e4085000717500812042080403100d0700e05400343c24181c1c2c99030782d0381c00c803800d101c101401101e07100c2c00e0303044040c000900d121844440c0070404e5144081e0140c132011583e03040058a1041c0e401c40600850300a8109070200404285000c0c2100e04403299894116507404900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 540876088 1250 540874838 540874847
    0x605060304020d11060c012a140915040e240a09020c010f0c021e0d140c0a08030a060f12030c0f031806080114040606120f0609090b01060f08131101 65
    0xc01307800b603001c0004200041c0c10a0150321070100442d0702c820700301d202080c103507005100c80ca0f44100d0600040381083e0321300d00040d005001c0c0c104542c003e001d03c1070f00400407c2c0805030790440d402030160200c5030010813104015a41000196824900b4940d0700001110003155001ea402d026040407c1d800180001c0440c10940c049600713051000d00411070714100840003503c80c0d0341d500d00e00c1e0007000c220481101219010a100302c000c14240c41d505a2007041c0e48142c00c191304500191030540c05940349200110700040d005503c280d01e070490002c1e0071070601340307020a43c1200e5009a010b60f510382064000103070700020300e04002a0031200c003c4001809280071100c8070410642d45210b806040000103a15070002c6885040c5d4050074500f889031032041043c4811290b03d132258800040440b046114005100d0780004100b006641d800304010340c07074499070f000b82c0d030980e03008989030001d500040105951040220000035000d150442d030a040c200d07030452002541510143c15071313a006440442c280c1c000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 540877338 1250 540876088 540876113
    0xb0f071103010c020a020102062d0402010203070c291801050705030f18040c0201150b0a03020d09050a0203060f0c18010c050607080405011b12051003080c07180605060304020d 77
    0x40007400802e0b1403c030020b4507000030140c120b01501c48e41001c100e039191580c07021400060840c130550814040c50b003c01c178801c040904281d055000420030440401c4181c49000060706040d160581ea80a040c0031554101c18008400460ba09040c00804503003074008500e4040d448003403a00c5602c540c510f050807400d6101c0c1c50302003100702c0c500241c41222108003380c145004101110100a410a0000d0903403d950751410180388003103403440705005846201014015050b2980350041c101400c1d0000d0307500700c1e410101c1c20b035200d9020302e41c048110300d000c0085990102c00f03454242040d0401e00e03880b46441c05624520702c039400300081c007424583d201c1d809c50801d0542003c215800e5041c030500203005001d0681e4265515424099944d02c1c0c3c101010b11131008045a0760b88000c0d04089036142c03002080003404127813251002a2000000c2840c0c1d50140800c001c5040103801614a04804601d42c04e80030058510100c0c01d062003000305980f0082a01d0340301d501a01c601103840c03407518040026450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 540878588 1250 540877338 540877373
    0x402011103070b06041a221d0f120f0f18061810030b01200106030507030309080609010902101110051303110c1c171804050a060b0f07 59
    0x220b9a1814070a01401035402201c05071010401d407140f400944d1092440c0301c205039044011048014070450b540100c000c01860202d10010310307001a9589850b1028100954689942c4840644828850148114904140001031484c50496281c03015110b5004030b0069050500d4040f4100d9040c0d16107000d0f041e8006001090b0380d9960604c81400501070010041c0c1e0741c0659102486054040d00a105820507081d0503100d40e40750002224070b0280a801d0078181410a5484010000010b0010441c0340007031882512009442410002405e20703040b0010051011a0706200c4910b002d40c07201080c0d06505565483c01e4588080044902840e0154403c19030510754a0b146c200400701d04e551040780c101074400e94800482400c105551365a13031100700300c0c450f0b200382080d41c0e41c068000d64034400102948542a42d0000841403440820b4a0304000401c0302d5481c40f120f004110f034645840fa03d41d02148185c401c0005900f4070540d83c03424000c070340b10904c8410001800d10207201c005d64404020a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 540879838 1250 540878588 540878593
    0x40822060504091a0114130801020f09120705090133050405040e0a08030c3406110313111207090b100815061803011b090605120f04020111 61
    0x40d51140000e0050b4410300c50410510b1a12100e4400e03140003250300d00624105a64044d40c0f004600125007444c1d0200200c2c00408030303150000101ea54003800036100c00440411010f4480414074107000400850190580483d0801e203000e1180c1d640b5004090305450041d00001c01035104155141100c002ca00c56a0300c1016000d0314a142ca0360340200103100b03907001901c0502112144424290740c651406000400207a400d00009400d8401040940600c0510b800740c0c0403d03c8480690004050003401c00c0c00220a4002d03600c02840303000d00840308082000003a661075481d01882c100c402c807618000080c045000020114070356076800064000481c0d540d015500c840f69180c6146c001001401c020780e02034900012150880c0b400740c81d50b98440da0107942001c00b178481640030428240d00c00c400003014034226000c0752510741c5091040799001c1c080f09040300d107105403600380034000c4165079000c5803c001c41000302e04040800501c009421070364100303c2c649141c0b02e500c0140c408850030305a2800a1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 540881088 1250 540879838 540879907
    0x1080618040312140f07031b0c021504051903020307060903050c010e031e150a09030518030102130905101410030e03040306050903032e030803060f03010f0207110a0305060408 77
    0x445d1610340100501c0d142007141c02851000b64504c044000c0200c008200d030310030003001500f8a001c81103588554144d0301d902d080e0300c440c00542d0002c0d003c0080244009410010b00440c201081400007034404c03400c04601c02451076588a0303a90750300b410450704003c156164915a5181007124000d01c0c6451842483c0c1c0701e1100c1040355484200e4070741640811196000b1500b800b150f44210110640c16980300c1d80740400000c9920180300004040c2a0199400c00460030020741034040c01d4040d0162a07030110f201c0c245108541c107112000c1d000451000c0c03101132210560f80c0c07502160341c8000098100880c07014a10804107045000716400544614206400c00c8881c2c038021009621812514544440d200c4005680c1d00c012485000780900c0c1e0b1072460014000304107024081c5911040c0100701480342900c0b4130110b803e4030050507031008400c0c1c0100e0003408010000d4000fa103454800d0712800e44441c5980c9a9654500c2c000d803014181202c0060b80440c00c074481c4010200c03000c0039030b0701a00c29 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 540882338 1250 540881088 540881101
    0x301150602010f14060907110319030c11060c09040b040b09100321020304061409031006050a0b07020306060103020717040e010e070315090b030f16050108061804031214 74
    0x60720025042c9090180f801e0320440148000700f900034007a030805801e80d0074603687c44000307840c00500e04000c12440d100902035503d400205140c1c0e00015035143c2e802084910a07030030083d00b420960a130045040d00104100b000380114101aa20062012a070104483c241c400200c1d0041400d094001d4011008004021f00d0103080e115050032070f8811410070a04c619103003002d11212000705140d40044c5c0003007104100461080910044103203844035080c2c60200c0d1030002a140c050501140101d440e2204810060f07850001d0615004101041c52940b600041d0350009440f8807000705818103040c1e0105090060011050074030340001c0011074001d9903940c4944880c0c4455000744540c0024841c04000912043c0c407a0243c546c1a080315a0211646411703c134940c0060400a41c40701d8243c0325841842c2c00c42c80e410800d00500c1e1303610b685241c2445041100040a81d4030040c5482e000398608420340c00755811440e03600c1d0340680c00d45404601002c400b401000508044001e604d035100034141030206 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 540883588 1250 540882338 540882341
    0x60f0702030106030809100f0c08030703181202060a0c1e022d010b04020708090d021302180a05010e0603010b0307090e180d0e03150c070501020c1c0207180902030115060201 76
    0x103440710442d200f1514040a0f80c02300c071003468007007141000130440503810001510410141d90041014240480c0c100000d003d40c00c8070f2488550190742c0d10301a49010a520f50301441802d03042901e07004240425903140c4006060040744007403040020380e5003e407803105540b0034041c42c228070a178404250010281003005242e060100c000200055207019180002031a02d4803c590100b9802060f6504082110080090b1200840b034180d81141c0312030b108100c07007041c45c4020984401543c1c07141011030318800174410f4a01064101a05100903140e40540c1d55540c20242c03411541200340c4503549580f4580100d03001210760380501d00801c66902031210002d40307402c1d220081500c400c115850324031032031011640d121010782c5050701500031034a015422040c44103080d502032644000340345080c2c0d056589908a030301100800c0d8080d049160340b0f031008010320496030310f4020799100801d0b415042c0b016072080c0d210f80350307c07050003644c0d030b0760141003152800c0d004180b85035007038022444902c1e40d400700a030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 540884838 1250 540883588 540883597
    0xd0302070e01050306060d1203140703092a031e15230c0d0c0c0f060501061107150503060f1306090f15031e120203090109061d060f07020301060308 65
    0x1c0155084200120329030900007810362048100070f240c00c0c0c044074961580349080c107001394031004250301c0e543c40440e141190510704e40203070069500020b09402c0b609007103080e900728010005420055030804d0308022050041c0f0425280c1202e221049880c807035444140ca845641c0d030080c41164020074103c2d261500780d0081c12807668000301d03c1c200008101c1c0100154104442c0448034420030721600a0f5401d50b80d02000100700581045180c9600c2c03600c0e185046071218008a429585800040c00026030100c4c2400017203203000020000d2a05100c100c011810108550310100400400015940c2d681d43ca10b1202c003a0f8050898032007415440c402002030310443c040d400e62107007403400035100480580f00b03501500c00207001c024030315030440d07a5603080b007c143ca0000e05003100320644072012881c0b10392100d40300c8909400841c5d0710380320382e8005083c1015a0b0701034800d0084a000e9000c2e0151105001c641e89070046510039900c640005410b4254040d40002a401d586008004810010000000c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 540886088 1250 540884838 540884849
    0x90815040c142107030c12031115160c2901120c0911040503030a020304080d030e150603011d01061d07140904020d0504030f030c2604060b0d030207 65
    0xc200181c4031512140800c1d141401d403074100600e11500011400d03c2c15182d41e10780c0d03081d0700f5194041d80d29183c01c4210110344c0c02007041110140e001108041c2c100054500d0410144042c0031400051948030550700c030b00602d400410500d10f202418020300c50782d40c11660542c402c8042e4104801c3d00304000e006104019000400281c1c1b03400403d64150040344040840c0e0f11141040e81d071424240c450703010f00b000e00c0040c0c031203800911000c5040c1d5014030140c41500001e500035500d031403400340000e103882c603501c0c90b04092515000c1d440b28040b2011074190b01980082070000d110b42c40301c1c004640101002400100d40705941c1110780901407064000d05d040f07a5144806524800345005000c1242c40d0555220000c00c1045402c10081080b0b50090004204014401414103581041620075224215801c0300080c4120084092440c0c040c4645900c1350001e15102191031f00144440d06512440e00300c13548203440303410000301000031035042290040800390842c40f030031205d0328020392b330307241c007800b44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 540887338 1250 540886088 540886103
    0x516030c031701150302160203071710021306030e0f030a030606080c0c03221d19090b0a180218060109060203090112020c0c030a080c101e0c09081504 66
    0x30700c1d00c05103040b400034142c4040c40740e2001c00c2c10149034150700039403010f04503984010b228100744015035010712012000f800d40702c00609036003610744c480c9820201e1459840401074818003c0c241800c80b003150a1080c0d608600300042c040040d545081d10b0010b5215a20035548000035011586039410381055044850b1a26080d40640f160b0b4145a840d0060b2030900c2c0035a442400410720000449101c0d524030f4040659403600d260f1a039003041c82c103560340f4410b0803044e4282418041714040d00c802140c100007a04008128551243d03550f02c030814801303400400c0803030b103ea080d4194841000c14452026034000c00018130341001c000c3c9515603c8080b00c03014046074014500245080c0080700700e52161105949440400c07402482d102c00a41021502010074415248203202d161000c0042840d030700e0140168584505244071018030344a8000c0c40300303014608090441c00c0316444030a0110700c1032200c050104211558102c200c0b0400000c4d84482c1c114420710000c000802c02c07802805014901860b803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 540888588 1250 540887338 540887357
    0x31c0b01021506030319050d0e060708060d0f02060a0e060304060501031a0f130609050114060319050705060309240708070c0519050705130f05090a0209160516030c03 73
    0x542d290500400c9070150381607042000309241c0350308528680c09014515080ca00c1c02d10415608800488444082d1152964894002e020003c2e800c685601e510160072900255101e00079556030401000450317000380240c4020958528140c050420015521006007410344c803450281001c0010b803000f8030069034024145407049120040c0e134206544a040905d800b00401d444801a882c41c00c1203114082d104660b4860140e40003400a000340503443c07200041101d46400c251003090304103c029480c0e2080c4160000246002a501054850132a0000c642550300d95485000c03d50030314041012414032030300104040b1000541c80084540075040903a50100265110001924085a14000507250b0b070f02c62b030890b580d0302400000c003607507061258060b02c0700030b6590408100c594404281d840a140e403100c0d00180010303064820703d0361201101d401052105825004214020009802000d2209008000ca40a980103404403145540350310032400b21498241030041c040c004403241180060003018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 540889838 1250 540888588 540888613
    0xa140d02070305091003050c03240a030b07080705030702120c01090c08031803071d0a061e0302010314060607031803020a0603090203010f050108030f09150c0f1c0903020f03031c0b0102 81
    0x45074901c82c070020a0949d02c2c64a0710100c4c6c40031680064841c0743c892003188840b812540b04c040c501130007507200b03134280c40302424005005041d075000108003000300581070080200903a40064007542100404030010381d00d00c94040461b0140000312800b910016511000280707441c0c00100030321911007182420350700500480704050302c0e101d042c4103044140e11044030b80d05001d0520303410590085810840080d9050356420320078180700900880b20f40ba4440c49000704255600343c090034040c2c242c0c85020301050b00d0f2000c00603005004080c005410400e440300c410800c540c4e01d0000c8405150000c150b0180185e03588801000780283d160200d01030350a180a10710200c02c5c5020b0303c2c0c140c850b00e001450a14002413800b241ca0380112720b0041e84406001c0c4bc160903030048100038400343c03101c40c014111465040c49100c0c03a0a5058926442c80400d006d07211031500e43c81550310095075030464201d0a10041400064a103006209052034207501c5104521007080041d849250281802e80a855690391400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 540891088 1250 540889838 540889841
    0xd0c0e0307080a0506010303050a030f06030c05010f0206060307060c0f060e0a021512040b10050a080c03011b0806090a060509090a02010905060a050418140f040221030a140d02070305091003 83
    0xa0f100070300d240d0040c00148002400b510142030170402924000070148243e1030400217840352580300307403005482c40109008550b4802c900c0100300200d80001c0002d400c060012030f83d0340c04284544402c00c2000744940c000c100c03c001c40f4a14142c3c100505000222520b02021744540c01070604900c500c2c04038500e050461184800c6d6040d00440481403401e170364030741e20303000c46098000b494411070383e4a122000c1900d0751022503440242610b800185a98066402030502311a0055080b000006014603544c0c45c0b02c1c2c0c0003281caa408541668055007076240c0440b0000a003141d500079a502009185c100710030b124000600e4a4558000d03680d0789205a03459040c018503114580010f0000740302000240522144102c800041004a5100181c980884d00001071054000d94102e20f041c91003400348000e519140f420201c004080c185001c640800c6405c0007039407072040c59906e000f441755515103956406040010b4503891b80c003041d0259902c8030781c1c7c42c0c0140300d64002004944600c02403000c402d0014804d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 540892338 1250 540891088 540891103
    0x90303020c1005010f060f080f062209060e0313060309110d03170f01050f010509030f06010b040311030304060e0d02030a05070603021209010213030b0c070606090e1504020319080d0c0e030708 84
    0x4582340c40c001929001d00c03108407150000d0041c3d0f0010703c200c0c5c0d00c803400c014407002c0d488003802c1c5010008071300c2060f103403100a8540402070000316a000b40502031481c4008030303612048407014100040d42d480b01d031400000d1a01b40c004020340c01032900b1106018541c005607280241a112580e003030996075002100302d1402403c1c069207412650031600191107500a034000c000241c002003c5905403600c042d0850700d000c0c400d030030031074050001160070010048101113041c84107804502071828203007001c0b0003c160702000f10348030f0300c41d28011001c07134251340b018800c60403025000320690f24110f444900103000382d800f0341e00d0500c0d0441c2580018100180610a4410988205c680c1480c1c1741d24686510a10800c058000307841e041301005040300156180c45480010f01c842c200204111000d05c840c0390600c44100c0401604d00344a4041000580c1d002c0389844054245a510040110841c00d08086a02840e280002c5a03842c0020045600780c0003010b031505c16908900b00c07036049440310134650302c80c0300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 540893588 1250 540892338 540892367
    0x30406052706060d0f05070b0405210d03090f02031c0e1c03050a090906090f0b0105180907020304090f02030603120403051506040b0d110f060405090a090303020c1005010f06 76
    0x6004500705141004030308a20500176541da5010080d26180c0f13605016041d4010079160740002410445030800076091048503d40404000c107020400c0c2505480d02080b884850030503507603080342410001044800601150003404032084101000100102d21807129141c0c00466201c0030180220f281c0403109003e010a940c0b03543c0e80039101382d61b042d03400750003294418042c80310003c00417070f4001c03080c49280c0c000c1410500101d500e503900c504100403200247c01e414104003041040755160711001141c0c0c00d00e2241614030361079070356548004034110b01450b000008000d040003074015041566070040c0d800756004130b003600c0d500b8001504581c6a48100d100c000e10941111059110071072926504982c00a409400440d04240714030024800044808046130300450100303142a11b41031058500b6820001030b40c0d003914080c10407000810045000380110101c6440303100351000c141c8207405488540103a003044465400200220002601090003140118141448001400f80c422080e2405031074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 540894838 1250 540893588 540893593
    0x12070c031d150706240e0c0c03071112070b1206010c0201080f04050c0a080102030a06060306050105040902071505040b011a0304120e0a08031803070b13120f06020304060527 76
    0x9454040100c06600440b80c260795413a65100400d012a2150b0826800050f0551002c081c080c10a014203009000240400c40f800e07006004001c1d0403071001080390340d00c3d908079500a13122894bc200244500a510280e9012030043c800002010446040036014003102602040082e80d034880044401c8090110060b000560b0b0302c0c04100b66103000400650824052001e480414201e40041001c16442e540401441e80d030020800005002d031344100c902402c0d0620f400d022603850800000c029004038014980d005600041110810403c480a003125040c032540510140ca0035090854441c01c003445680c0f0410640040049031443e01303801c81b071040e50b00c801c21000302ea050310401c4861007607100e400c607000044050042160390701040600380d002c0c0f03000000c0b4902041e44003030500f0a040390780000c0d1446400c0c0490380081c904000d250702030b0340c006030120314900f010341442c80d060303915100c1c0600f4007440002130000b40602c0d5000203109a0b0724601d0b81c100d41d0142d80c9a00c01c881a64500c482094 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 540896088 1250 540894838 540894859
    0x60d05011b210209150304060603080711100309121202040e101a040612050c1b0303060a050604150813150c0305010b030402130515061308071a040902070812070c031d 73
    0x119180080d61f0000c1c012100000c00e66201d44d00c181d055405a00140c9903440d02050b00d2600e86041d40006604003194641801024821307500d0060308c1901d2640c0b02d05100c40780c40740300102001d690603a80200b01c8401d000e00d15040c55012402c40c10000d0240e21000c1c00440c01160003500c20000710703011074a80e5a02d080c0d410381000000402000080d081c030000741030401c00112086c035a032961508410904001d142e403030a0034810021034039502d0344003034000c41c41484100008003000041d0b520001040c05c2c1018a03644008512111140045000b4203820642c0d1404a5103046035100e11441902074038100426600d42c01c4400361800101c1d0003c2d032002c2607620300018200103422694210402041d00c5000d44542d02c005102500194000004088070b41402c10844400f000300780014282c20035003030b010b9200320940030014413650180012650300000c2450810985108070740d48503e00301425281070070000802013446840d42003d40001d24901c6000509000084109000e001c0c01024211071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 540897338 1250 540896088 540896119
    0x1081f020f0d0c180f08030f071b030305210c07030c06060b07051609093f170916090b04090b0412110c09060d05011b210209 55
    0xa0360000441400c4400d06120614039819a8064083c0fa5101c036100e00020520a4a0861500400350b000c41003411002c8020850f1400110480d0030202051240700c0d80c1e2050340c2402c0f840c00444010303084c071030003c415000042c143e0001c0a80145902c500b2101c030620f60850103180c189005468a00540400700f0aa000182c002c00480410b24030075000459501d640d6590360219800c03011040d075098024a00c090300d646041c0100001030301413500100680711803034807500c0000c850060390320030114842a007090224a1900e00d0701007480e20020400c5038070b114030fa005142d206c468501c03140341400300001c22808000070404003c0d00ca280f040d1607000d6890100700d4806028a000c040341c2055907003865502083e400103285204a00891451403040000f840c01442050348400114039600004903450540d40c0b05402907070052002ca460b020080d0032420014010041d90706810b0908521000000507580c1082904c04460194014540701c1c0002c450820140c0c071803a9901130f44070552030315500c0b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 540898588 1250 540897338 540897341
    0x80d08130302100f0608190803061504050d080903010b031c121e02130603050606030606030901180615051509280603270308010303050a020f060c1201081f 68
    0x4060080c8111441d004442550b441100c4403480a541d1183c0c03903030810f101951b01081107940800d0040101620415562034910b0380d404003515541c03041c0000401000510284010364000d444002c294044ca1011840d0040c07040d172150392194001d500f00010641b80c2d1401240020a9034100100c0c99104203a9000840b101d5008100c0d142a9641c0c50140c074401c14070300c0002039101c1c44180401031342c03401e01c00624074001c491030340144105400c0204000c11901d03814140c82e0441400d4a801e500c0b43c99102019014203000b46070725000c0c0d04880605018004d40d40c104407041020410640d50f079948034000d1040c52001211159006e100c20410011142420b5401090311405080d00c44642403000c1000d055140c1560700100009881d445101749441c485070f0a8004016625a214842a91950042c02c011030500c006410f121010502080742e038005d01c810b0350080050070559409192400c880c105c42d4100174200d010b881d8591002282070a000640011041d450601c240503001d17500708000c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 540899838 1250 540898588 540898621
    0x4230c040e01060317040311030f1f02090613090c0c021c030519030507020118020d0b06120708010e010e0606031902060f030a0509100c0c0f02060405031207050601080d08 75
    0x210650f507a5880000030841d034912040e00e00b030403241c507240d80324610700b00302c0d0381c0e040301c203400768400e41000001c1d40381042c00040c0f42c200030031019901c00c0c00d004400c058800074064a100d680d04017000081050401d202c1c0d105400541e100c45208003c2c13178a03034480403038141c55100310094001c01c00300703000c83e165100118980c1070300348130f0300d0001e2600c8142a400a0303515040342442012a80781c1d400d01132141e0f02802a0848100007584001180301550001058403041720b10283ca420307940700c0496040c0d200c03038020f0f85010182404480ca1f603a80d6404403030081002c140c007184035503e024611a0307440e0011078010702540c4001c005101c030800004883c801d500c03c00b80c04a03400801007000011070605031001e14443c0d03000300f10000c0d003840c1540e0341c9070500d440101c081e68440c0c6031007040f450a5821400140da015045428424141898404507019125a800055140c0700c1c41803c001c4d41e124200081000d2440340d03054503c1a40c7e00d0004564524240c251000480d080c0c400141828071001000c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 540901088 1250 540899838 540899861
    0x14090907051810090207050303070e031203010e0711012d02031005011b0b010f031b030803131403040e01031b03020120150705030a06060215060f03120a030504230c04 73
    0x50f215a42d5030074140003264801ca030101c170b84c0e030001700c1000707021b54200740f2480c12098140c01400c05d007a01101c1c1c0c80c070746200502804110024400104a030640310300312500c64907200e98002c000d101c460150252a2000038810700e852039002e2515070480d16428000d40340126410f42d81c0c5610343d8149001910601900001603003400d40340c0074240d000c102105040342c000c101242251000d14154108642d105034072031484040e07002c501d041000002c8040d000c03240d000580c42c15811419000307290075000302025408094451101080100e516010400098122031040d160f05010b040003d00264611041c2d01c400f90100c0c0c132a48441038050032445901000030755000c144c8000d02088120066260010342e220b20002e0004010022013078003034480c400182441d800108000d0035444c40384020800c0040c0300901541c0c41010046c5240c404001c0c40d201d2403480740c0443d0701c402d90010010003c05d0212030558a5a5030030602d510040d200d1008141c8000312800a004a42ca6940c24040604000300783d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 540902338 1250 540901088 540901111
    0x4030809010e131406010305090607080f0c0409110306010f0c0809010309060b0405190b010e1f021f02250302031623010207060b0a0819110406140909070518 69
    0x2e210f010056214200042070f01d22414240780c10540700040c00c40788010504262580710a0030f1000041e0071501107a400724412203060003030390f501c00c0305103224090740d0710102c48141030401010034010604050b42c423442082e0b85401807a2180c00c3d0840d280803803018040c000c0d600410a018482d4401d800c160021400344c10089540c001c0440490100c500840b01c1c1a000c1c40d0242200134014428040c404600f4070901c0c010380880c00030800101d408012a0595824927800045541d403035009211001c1c03034211021071002c0101d80340e180d0801a41c4000ca2480c2c2c0c007141c40703210a2009040407514154241c1581c0218280084448039520701c201c407010649410f13100d040300710340040d030b007114401c08a0481c10002d600c40c6142e107000b9054a80413011a807140c1c03c0d0b2601030101030f000003044003408a17043d81c01004070029041582d00300009041d5a6000b504101c2d010400c2c0d0900403c0008011b4260b5284145035136010b452030b201c10799802441e40c4580103c50f42903680c007030b40e41c2c01d94204a01059 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 540903588 1250 540902338 540902359
    0x114150a02030a02070b19051606061706060922020109180b0f03031e0a090807030f2003031e12010f050a0b0909070f0201180b090c030304030809010e 66
    0x40820690020506400142e10024080c900c3c035505000c0d1400809208000300c0c1841c5031005040d05200018500404111000c1411084444c81044508030a90042c0e02001556210541405c807000800340992640c810a004074903207003041c6069910450548001c11040200b4003140340403821100300682c1004148030011900314401004140c104402c110001001d44a040900c5a114014440c00d4401d810a0202000c020110322400c01e00c0d002c1c0b88038070b46d640c4500d00f80a40d121020303034000c01c0c0f1034072034200c011041101c0315107145040e5004484440f030310140f604448500b441e5820100340c050b00300b884909a5001014600c01130024101a080e08280d401021401c0001b000d03806100d40e14241c840400490500402b01c00140401c505250302c0c003243c0c48007142020314098009010828440302da0300f81b461003940205031aa80c12802d00e103040050341443c03004000c0030768400413140211191003442d4a8000b08450441c3d500841c05814070304100700541d03500e5010300c1c0c2d007904001981d9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 540904838 1250 540903588 540903619
    0x80f060607020a2907020f1014070f03141e09060d11180a06051c0f090b070f0e0108060d031704050106090605090403051c06091e05060a0b030114 64
    0x41c03040001c0c10f25540081c00c02c80000e40c41c9503a210b007500d6004c19510707040240e44090b86031545c480742900307010b80700301240403500344003140c00805040022501c040089540c02c10440034000385000349001740c0c0e0b4140c040c03a032005c07c00400d10880d01c8100240c081c00714000901110000602401d03500105140c0c103011181d495030055a00780c809150360001300082c2142054412000744040c10410b54000c9442814034034042c20742c3c4907803900030300e40261069010007591116049000c0e01c400013601440031511925042c001c2001c143d0300342c03010032054000c249807503115500c0035030319040580d241e081c940c49910600807001481c600c1070b0304110b01c0000618035000d103a540e5a02035403180000140003840c003007221080350885d40015202c1c54280302401301190348442500d81082ca02240000c00b8074041d048a8028042c40d40000c40040c2040000b0302c1d03100d01000103403040c0b02c00540600036541c0e070504100d002409800703104081ca00a10050154503105c50a080700150082e0040c1c107880a2035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 540906088 1250 540904838 540904849
    0x3050703110403030c05060f160e0609040c03140f19090219180c080709090e0106180e010e01020c0303070f020708160602100605010e040e07050612091c080f06060702 73
    0xd400c00d501142c442485d50003001810803c0076800000f540c014800703801d03c4804007991038010200c00d000c0000d1b0820210490b50343e101114001000100200300c41c6d05080d070041e025041503400340840c0e0f026200010422440e01c8104c0d4420307240303d9014a502591032003040010291b12000b40e8001c5d0440e610164030200500c0843c000d4580805140b0401020b2842e40c0140c92085a2000400c22858244058260020459819aa421000456007851201e241030050006a100c3e11a00da0640f600b22a4800c5a9003c1c400b81d4451000a000e20a060007259080c0e120307000120106520404c0084c4c4418492401d02400301110720503100c1c55580d07600840c2c903020340007441d03d000110340081004916010804a50107a0301101c0c00d03c4180d2420001070300c000c0001e20454003d5403070362041d030101e038000e21560010381001013103d41c850079400321410b0903510484100e150b07445001c01220203160303078600e0f40034400c2155450540c5a52003d00b030700400d860140400390454418410040140c4d2607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 540907338 1250 540906088 540906097
    0x31a100305011802090102060126060c0c01060e012130120506011205150307140405070c0819050705062a0c030d1a120604032c010305070311 62
    0x256500400d0075410408056101c3d041040c0003041d940c410002c41c1c60381d03600420729504680c00601c1102952007414154500d440c1c4c00921440c19008200c00c01c400c0081d468081c00d03da0f83c1c0b5100802806490707155400700031100380554940b000c00188000b0b1907004018005042910581840b40e114581e8151440189400c00041d200c0c2442000201c801c954404032180031503060304400c3c0b00c1420040c0000c1c0880c001c40c0250f215054175100019075040401d0007100651001804a035545680d80001048120b20000540e20503800e040c003060005104030f5031841c0040d00104000c0ca44042d1192808291a520144006003e800d0140001081003413003000e103d016002030080d007604800d4041d0b59644004c20a020740b0240c240a00038040c0c0c80041500e10b0225100c400081c45114074869250104680d0562a88403024420300c5000c90001309016014030b00c81c0d04c035500e0320b6a81460f03214401103aa1a40c1e0843d00d80b0f4903900351250300c030b0b40001d90003040301d00300001c001800300070003440c43d8003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 540908588 1250 540907338 540907369
    0xc020318040e03070f1a0601120f0b0d0c0e070e100e0301090803010e10061409091005030a05071406180405190e0a030909022515090b0109050901060e07031a 69
    0x3994501c0c046c400321100140004680800d091220b02d4000c0018015020034000200181e60726641c41041c0d908551082e40510f00040400f00c0417a007501d0000034125003030080030b484403002c1c00400c200f20f00400d40104c039400d005103541ca041c061300f8402c982d1580c026082983c11764031501000045000d04001b18041d00200c44001d01a15003004140c0c21041c0e15030103e4100280380300b0039094404800141c0384c5242044481042e56140ca55444400412940045925000d180d000c201000320001d11481100c0040c3c4403500036840e000d08002241c05210a40c500d244a20b10704414a458650b22280e031202241038030340b84110008283c40c0c01c507070350790850707101d90361102e0000e506160f0403104c00c00082081001c258903040031101140c0d40c1d51042000440101c14408c4010b0401c40e43c00001000c6604030b1400700b000510700d0602c01141a428443c5040c103e2411012525041041c055403003a038607400d100ca9081e44440c2401c40050500014903500c200203096000942c5c4d0b5035100c1500c0050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 540909838 1250 540908588 540908603
    0xc13020d02160218100513110a0e120a0b0402010324060905010e04090c050d1a090d1d0d08090406031406271209010c120908060601030c020318040e0307 67
    0x41042c4184001000901580c0301084c003201c0402032110340d07194806094807019502c0b0340c036a008603650346000e401001c0310000a40000301f00c080c003596100010180c02d0300c04031002d1000d0581218ac0715212040030401034502413010300014055406030300104140c01c0740c03660b0000c0c0c501c0719403081900c0e00100e801401c0041c00d588020001c56a0240c0742c4490544122420890048039079180740c0c00c40144c2c480d040c0100a404800018068400b0040140c030221086058803886c10f403100d90349415405184401080030120300400410603100e8980103088007401c4240c060150343c5980c1829001040780d903500c5521000003000040107100864049501c5800421150410016000b4185040882408060040d603840e011171400011880700002000c45c1540d038070503102d001202c00a10b040c0c1c0142104c50403640d031944841c1d11944100c01c030f0304001d0640f40a074030b400c40114140d0700424505401030707105004800c0b5412100c04582c1c940c1000a20006401e80003c003260300703541000b003082d140e030b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 540911088 1250 540909838 540909877
    0x518070801090204080303010312140d05040b010e07172706100e19020304020301060b031807061e0e03030403050a050f0606100f0302070c090f0207020f09090c13020d02 74
    0x2600204001d014101020040d81001c1c00c22100d10380d01c0c04144005403c10101501c12400c4900034214044808003128036259504454240d0001420303080e00c088074660303140000003130385070f180d00d0860307025404950701c004d00c20b00e070511041c20880b0003030020000145411496200c8142c0c4000f44400a10300002408203840c121070840b441c01c04541c00078036414840030805c0751240f10b80c0c0311f580300c000050b0030050f12611781d0700100c0c0c010300751900030309180540003043c00442c10142026192006056080707070170842c0c5030b400850302013423041603000c0401005001e41210030702582c0c5e4001255400b03000c490500365291a010318100e0240d034103036583d810102d0355184411007440783d654001000e440d107808526450f0300041c0b182d11402d4200b420036030f0104220b410020200c030308500810341c0550910540c1102c1541e180294010380d0100d2003105149111003c508110b0314441c80341c031644011300000c0c1c48810034003401222680000010780d40c2086000d012008520103884c244028007900e02c4203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 540912338 1250 540911088 540911101
    0x4080c07091b170903030c03041a0c19032c0c04020f040617010e270106080c041a09010b03060d06020403120f11121303080f250b041b0518 61
    0x603029405001d811914800c0004d40700000048a401600c0c20100698950b1a42001142c00c03407030f134290107000880300e0103000ca440b00d254060640744602018482c1030220401c02903048400d500300c0c045000c0620307540080c0c0750001a1810311000001030540d9a5a003020000070704a92004103c4481e428012906202c01940400b41c542e02841d2070342880b20a504041c9500707141800100808000e01c0b4088031144842001c4940c84107034218100280400e079126038102d0788400711026070301c0c06a442c0c241c45801811038021084042503014081c1109039003001d91141440d0300041076141c214111182803000a515440244000c6015400c816070540c0043c0c4010b00c7c140c03800c900b81c420060006200c8c21190804142441d886100465a503039078151a0401441364400341d0025000310004038403600305a6248004000c10b0022196460141800c494403d2004241100180003400c1a00018000504484844281ca01c3c220480e0510a954034009010704192003421340310380c907040c1c061010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 540913588 1250 540912338 540912347
    0x90d170706060e1b0f0702040c1b0f050f071206230108030309060a11090103090519110310060305030a080415060801021b06063601300b04080c07091b 66
    0x1d01c9a1201c5501d845c1803006151a240141d400291040350740b070007100e4444c1c1c02a031a152014540c46803001c0c801c1407a00b07141c0a801c0f8004810388250150100c80c0100050100700001507402103160055411840d4030748400402c090110300d13408070b41d030f24502d116040040c44528001d000c881f00455a038904024614200407001e0002072445003003100f148082ea01003415140303244000e10300054180b0090400da458010740c05681143d034030030390081c4014050041040078003030f5015000c540c4040c3d00f0030784810441c1d00e00d00c00508150000d005e03401c2c00c03510075441c080d0000d018a20b40003007401c20300003600880b200ca40c821240c50317500084a00360081c0c070b035103191910320210000d00107501c1c0280100384a611b032410309103004981000203104002e000b560651107250780e858000350660f15038500300d560303139100d803074082c4202641c075915840e44605203098050b242c1d00c600c40d10001d131215034881405c0d800c00740701100c2c14000c92a02003880b140d14401d091800b132035404460080c000441000c0c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 540914838 1250 540913588 540913621
    0x903060c0406020118030804020f040b0910030311060145050708070311041710090b09060901020f1c09061a1201060803030f1f03110114090d170706060e 67
    0x291748a84c03403259040485e0300140400d80c4540c0646061030160000c0000400610007a1103070f40e8044454810b2001c11a1614200740c143ca01c2a283d50b030407440040b03103a503a203800034403072008140041540709941e41d200c0c0013064142d980f01c0040810f10030185920b44180a8442a2000341c1030740c1d00100441150310060494202c0c01a040402c0345501c03c0c1c0b0211024032507401032000900c00c00d0070f40001200d04001090008259800400a480d40da02d0240548901569032840c01c4c840d040c00300d0500d407410300c201d900c0c4201a010301c0e45400c452403040414403001e4000c8004841d9601f0001c17001c500c03d40582d2180304500001d89103070300080300070404d040f20818a50700c102d0385044c009121461000040300d4001c00300501200169941221190039001c2c0081421822000500000100503070790002055800c42600d0b000b5803001407a000c0644c1c0d0141d2424541d01c101c0f0781c0131400100350f00903c204240c042c0c440c110f030702d03082e0303e61903100580302d06602034030346407800c00100038000c18040d00c0314 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 540916088 1250 540914838 540914861
    0xc070e01030f0606150c080903121305090f0f04170403050105180712031211130b0c1b0904020d0311070b031501030510031b0306060b0d06090e0d03110903060c04060201 74
    0x900c00c111450f05d000b40001500d0030014542d141c00a41d0403500da4041041e65100c0e1004a1899074525441440003181030042c0715440c0501c41c101d01151590061039801e03403207094034214081603a0b540361500003581d48903042c5280104400c00c0040301249080c01104d00c100f00038402c982c010b69100d000303685400000d6000f41c006140d0040c180307002036032060310302c002003000c000c004c83d1a01400c11a03201500c2003550810241003c0e540001e907001500c000b0345000c201c1e400a4485141e480b500c0300d1070424501003055807007810303100060014a06060b00075500c90017440c0c100d00c50b1020460711440c041c119088407030304000110030088000422500300d00c2c030110a2a05100030705103410380700515181408020200f22840b96050b40b5100749501060003542c0080c0705001c42642c0304108a010ba01c4030307800258490400700c000ca1000680d005801a02100000500c0e5007001d481040f002460800110105044100a280b040390341c1000014052003160300325564a52a05201a00b1200101c000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 540917338 1250 540916088 540916109
    0xb06030c030c15090f180708060a0308072a060c110a0e0105010c0312020f030f0a090c05060c0c03010603031716020303010b070819031a06120402060c070e01030f0606 73
    0x90b4081c6072150005030800400152080d40c031422240000b41c2c0340e05c1454900d58110300003403c000e600400b0f1a08480c0203c481e03444043c1d0640301c0320140300140c50507000240c80c170380081042100040380030b007014450007040c03074800c821142280d40030080e59401c6e9104100241c0304a44800a0007822007094680600442c1c07a502c0c0940b800c0300b0305001210510605042c88881c4442905060091002000c040302c0c03c40b0031540c5245481904c0f54540066071920010708004000070342c0311a00e40305000040d40c2040004000902d000b0410100798001d101802140c050300b102c0d01c4003030f1400d000c2c0c14040c4d482920707000d42e080d00300301c1a601c0d901001490101c8510010a1520706150084200ca05550b00c000e6940c0d030303c00c59400d22508074031501d448c281000c00c00c0c0c0f1a815419900d54020f01802204800340d25001c03403030008000490082418404d10184081c001c40c006190400c01408a02c0c880c6041d20480741e030307a03e041e0460317002c01d9005641d0f400042c05c981c02000228424207000d404030045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 540918588 1250 540917338 540917353
    0x603370e1606030905070b2106010302070312020a03020c100b010807020a0b1501050f0a0903050706020f07051e09091c080c1e090307060504030c2c0709030206070b06030c03 76
    0x407014a4019180700e01010b01d03503a40311210a0010500c100406010021011030707423504141d581c08400d1006400c40758046140c800410155071085c02120394440c4c06540e1400808801d66120000b035000300800c805140d400c01c4407024000302072240510580700041c0001c0c034101088000341c400c08005001e031045402603040400011600410250402c491013001e2010a1a050041c0d0f218891302c1158446080041010a070303a540c40298001540e00c684213440384d40f660740c4c100780d0703645046840180c0c068014400038010390400c99184030b10000d010310081da4024104010610601c02134440400e141c002041552a903816101c00300384c414058030b04040185423800c049403141c0901980f22180000300c0003403618044510b001e0741d20010000302981c3c5504d95803440500151301901c801c0351404d085840c0054005000c226481080c410985409007800e0846004902281c000b020a07060080600010000d82c80394005801e410340310760450070b500e06144041510700f81d00043c05601c40c0d4420003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 540919838 1250 540918588 540918613
    0x21c020405030d05090607140c01020c01051e1309060609060801051008010b07020a030501051306060b1306050a17070305010504150302030322080f031b0d0203090603370e 75
    0xb44400fa072140501d4040e0710341c0d44010005040344141040649031003290818001a00400b046450310341c0000d808031000c40f2844001951a40605a05074a9880c0c0c3e5144140e0b004403094000d14480a040e00304100454582c070310039040b11500d40101001520241c0300307000d207030340110801e40502000c030b0304081a1120a100209105014003034481d0640c4045000002c42d01c407018002c0145038000d00a1040e8980320094401c000d01500090782c22904050300043c00895030702c00c070b0300d2068000448801d850f0070123600340c0391540a00a98000c200c000000d4995400741c0311144c0f801020f1564001c03841c0e51400041109803282c0740e90b1001001c180450401c0140d03400012913000c09582161040f5400c1100383d1010525056440500325014082240c007550340c0c044003c2820701040800d240120314501e42c0c4e19952140c60010002691040003040c18a1412038059503203d01e44c1d80c0010800b171101c0043c0020310f00107048440900078100b25480032a140c501a0103a000d403040000d00a619506 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 540921088 1250 540919838 540919843
    0xc1210080619090b0702010506010f0c0b0402010804020307080d090314030306030705040e010e010f092109030f1509060c020f0313090c0c080c0c0102010b060301261e01021c02040503 80
    0x1800d0821038408202d00c0c0c4000d070000e5000f00c148150043c000e030810786400d841c00703800f90404071a0180001c40040380380410a000341c103145070301c0f600300d0315841f89541c556005503811078003c3d2050342d161044050018001808200721251813560750b8038a01464034600d49590030340c1c07055004a40c19042401040100d4070300048102c100d85003100c003c40c0c507928001586c3d0060903004c0d40350056500f0054001c03a6042c8603003107020700728419000204c0d00d120202d00241c42a03081c1404030001100904100041030070f603542c440d0114080c4800380d22440341106500201d401200045500070340351840c004501e03070180010850144500301840c41e1115015415032003012a000e14901142d503040528200d51007030044e034120540c02302c80259110f40030402e56554840b44d0070300f2030043d030034000304a00c1c2d8106130056038101c4490700010624010b0b00e03c1075444018111050f0340d0300d84540b40001c15540141c1c0b81c44000300350440001681c40c01c2e40f0030096400b184010607080c0c5030f40100410481e54500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 540922338 1250 540921088 540921091
    0x403050a0b13051b27041e0b07080403020312090f0d02030408030703031a090112170906160f021c0b220b04060b090c0d0f1506030b12060c12100806 65
    0x703101e103e8194070060001c2c81020151a0700c0b458035800750541c5448450245e480c0e80600d01074502d405103ca486000e01d08021b029040c004d001c01d03401c00c003050255000c4c04040e0f41080c482e0044c1c038141881590304d008031a10031a40741c8885d9204007001c2c0c1c5843e1003404842d4124003184003441c070701418118299924460107800500b016900c0b88000038162000b0004011050300600c4181156903904450984440d6400c1c1607038015030380b0f1030703e450300d11011086400c000c3c4090491418980c85150541c003044080200b40d8519200480000050303494404143c4082045610700803500c942d07040204441c50f00a09011940083c03c0012019064424000c1c603082d03486542402560b90341c1c03402d2070281070030000c1035401c1042c2d1030074800c490a104014164144040c00f0400540c54041d00820a445240f9141c80e00079031010400d000c2c4a00c40d410820703818070041d00c0200d607c1c921044103440c080f012948585404008241081c0c98000c03070443c00c0c0c00152a02601d00309601308075469441e01d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 540923588 1250 540922338 540922363
    0xf050f1e0703181a13330305130213140f0a06060315090c0917150f040c0513020912060a0c0f090b090f030a0303060503010c03090827060403050a0b1305 67
    0x400300381d1421002e080f40100006e014041020802c00c0c000c983c3c0b003596650901e20040544002e5030998800c64880d20074140320785602d02d0a00d50700221174081c000c5030314038010079483c09916101c3e054108c494000ca09406031002c52940d20013894000b02c0e0f001240d4458001d07804050400080c00000c03501c44000c0f070140c602403400004d1a00301d5200988000d601b81c0e111a20740e05000340240b0482e00e01080e1700120704513040411108e951803042c0b02400e2503080300d000340101180342d0140036070301f010244181191103909006240841c2c050000c1c5403c1e516401c541590340c841810020b10384000c4c064030400c2240341c01c1c4640c80030210000034001c841c0ea405600807041010403180400d5440c41500806100701406595035220b05040087c083c22150060354025803e2621110445100b4420703c0d44440e04540c0301c1c1e04099802c100352912110341d91416070450000400b000703180c0d8822000300000d40c0706100030642c0c1e850600c0c200c011210010704181c490f09511003408040b56002c2551820001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 540924838 1250 540923588 540923639
    0xd0b040b070e09040f0b10060507111527040506090c0a0216090207030201110c03161a1305010c05160303181704051509010f050f1e070318 61
    0xd55140c0101c401080d0700201c0c940c00300345841400240045c0c48074a0410b130b40642030100031036850702a80c0e000810750f84100400101c0c108503081c00f18031007800c034452011009200308002d0034030342040c6580742c009c8400c02c3c82c04201c5000c000302245415103140000c0381c0c10780d01407205d85040000a50721000040c10a0480e00000402c0f0380d4107403090240e011015400884c0c1042c40d6194422480250416502103001d9840d18400014150814044e524103810b00d50003945880c0c4241d40f04842d100c105241110307810840c4800c040090174043c0c5680c482e20080402c980140340b10b04049094072440d44440c41408010007952030821500b079807516030f030344e094100071402c0da0f901c03556007021405510000d0030000b800c100c0050808400c90080c021110200e480c0000b4400e14580e020191040d904074ae4041208039001c00403c0b40100701900101c00b801c0c041c00d04048030b042c202496450381000071540c00c10002244010150068450040e5401500500d60b0031800c0500c2c034a080919458002c0859 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 540926088 1250 540924838 540924841
    0x120501090203030d05060f030f030d1a0405040807030f08010506091005070611030a0b030c06071b18020403061413030509040e0106091406030f19030905090709050f0d0b040b 76
    0x1100350012222a80d0140032203903903005030f0141c00300500059660520403034000600b43e91601c0c000400d16115400240554030b010340103a0000d005088004c140c420014036202000c19036138580c41180d01c2103004601c01b95031003455203030007403407a01541c0c450340c18422500300500c615120b6505441022070103030398550201c43c0c0030343e080c3d916015100b80180031904084580c00c04103200009540224032a90051040742c900000b0940c60304000114241c0242c824003032a404980220000e03030692038824410a00795403160709100e50714074406403010079542c00160401c00c010041c4070310301e40fa4900380908d44207400c115203000800601002d0107400c001c40030800400e2551241c1c000d1004001d85c0008204141c3c1d1001444058842c99a140740150701100000c1d1803030602069002420580c54050300420f000a07081c02400f000e50b80c015001c002c4050000308494407031000b0207003e261262a00418a03150504004580e02d00b0030310780b40641d501c41c404200141c0c0c04a0f0443d00640e200040c40c246 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 540927338 1250 540926088 540926093
    0x70312180f05010c02120a03110f0102041a090a05033319090501020f0711041d060f1308032503271a040804091a090105060703120609020a02010f060b0412 68
    0x38141b00849049450081414000030160000f10b00d52a40c01c150742a5640b00d07084400c0f203803c0b405680301e04290090844411201107074000003c0c400b41c0030003424460802d4441000ca4501600c006000c21040e04d28243c2d0200b517104140b42c28042e4501070120703a01c500d0310f03107071030b41c0344008425440750000e80300d11203030741000400c0d010344802605d0351256a44520550912580c005168000d490160f0303e8222503d81c101607410303186601c44021002080c143d1140c465003401800003d219090042c1003000d03038000500000001c0d4082c128400400102c11602000740940c10300c207000c040309151900c0c0c403240c080d000d481103905580e4400c981413400c817040d42c1884102810040300084941518104100030062540060400d4503c0003400300100f8045c0c041d0b4a034221180700d0110360000c21940100102e00c1c21400505100703100703113405800c020300301d100030081c0c9889420080c4056004240d25200a034240f00380d00e00ca2031842000d01106190642005e014030590103403480104003104217805 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 540928588 1250 540927338 540927349
    0x30608010e1005060d020a0506030709080616030b012d090b070b013204050601032405010e150d020a050c03070302030a08130506010521070312180f05010c02 69
    0x1481514000d10a0122901d5100c0d180c4901107a0015181e1518010904909050b100c0c64490356019041c0c0e900c8a0400007040107641009010f84c0400c103c0003004a1125818072005014010b8551185803002c040f14014007564495490a410419650040725030301503440e100f82c44000040716150900072026000700c4200c1d02d10b800001a2290010703010041100014035281201c00680040800703029134420340c05c0e0580740803054a41e4048542901d02c0c903140650009400c003005041c0003881c180790f8441412060301d564050210725416140800040d40c0001400d00e80150488050708040b21000603000310b4000e482d00c01c060300c3c1e40460b80143d070600640840d46407100060441c1c0e280c0483d46030080d5203500000140f00001d9940c00882d0b601e050207003034a061194414003400b1180c0c207040c103125500c081d29030a4660141460404102c2500a200a1000c0c50044075580300304064944087e20242001880084081080e182041070240103414101555800d01e403071388045966000088 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 540929838 1250 540928588 540928601
    0x30607030b2404080d090605040e07030f0509010504021c03020a0b100b0c030a14070b060d0c0f080c1e01080708100b03131406090c0d05010213063b01030c03 69
    0x54100c032401e541a002e80c0301038002c0e000300c441550441382a843c00103021521100d4522811011a1f404d000505c03034501050080d90340482c02d85800a5008a0b0145007400d90700103031581000c03a551030050100f5400c20918101c070048903d0b050b50315540c49070750002c4da1004416800b80c010385801002c900d100e80c191503090001c103205030315681c03265607203840c07140c50b039000c0081311000c690300254450307090502e00180c80c0c00c6a00010a250259a15414002942c0103281d00326504010307030310042240210a000000a41021002403400003000c105010035103405102c8445201103d41c1060703070b1aa0301c180e0707145e030201291410280d81d84070742503031051610254122082c01c5c5008801c112040c0721858405c3c1c031860103818900140310345161541d8481d20103880381403203900500d001c14801c0c01c000e034080000c684102d00043c500354100c01010301a14450b0004000a44c208140c20000c040c141c10b81c040d00340d0107c00302c103050305c0d24044508810580b21000f0341130549859460000502aa01c83d6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 540931088 1250 540929838 540929869
    0x20d080601120518030a080f130201050a11010605031b010909050c091c020d0b0603061e060d1707080a140a0519050d0c020c01020d03060f0504090f061a0a14030607030b 74
    0x2a41c6400051402038406001100c0403c008180d090004271025240031040d107056806842c0c4e01c0c58000e0b08175044401c81e81d41001d02d002d40d92545c4000a09450410030700890f41a040140010b00070388000040680000d5880751007654101010b00010f03420140449500d030f1000c55160031141000311459440b0306e10300c0e0029512400201c1580c0c14040d0413006203110748001c40c1900c06a90380c03a56101c084032130003109458020440e0b000100781303090003108450a80e0140d12920000305440704021055440f18034105c0d428203001ca03600048030b42181503404504442c100d03240c1880030710303040200603004d00035203690025100d400c204540d50044040754003c41c070044041c40101d900070006903480584102c0240148280722035614010721903c40c1009603001401c140641c1c80c0703010200b0000d480101c01c1035441468415070f070800a90a03100d07404180c6060302d01611001c88210810480641d6940101c0900304c091803800707001d80d00848c060fa48080310341400aa4500c8400100300101029500d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 540932338 1250 540931088 540931093
    0x50103020c1f0f050f090703020906010e04020d0f0605060c0a060b01030f0903020c010f0908150405161806090c0509040504063308010e0d030c0e0619020d080601120518 74
    0x122407840550f508003000c402009007042c8881e858013412078100b154115201032441c1c100310024401460701e880c65540051052501e41021140500002c0403a031069050400d030640d2071500c0c004201150040c0c0300100021628181000d55091099446407840807000300425078a00040969a001e40e0094403854130008003040360484515001c0e541d0500e608215001c6101401c1e0451140d10030f40c1071000380c80000011300525804101c01100c0608050822105801504000c200c4400d400702e81c00e0007084100541d070450800d088506044030076070341124080c18100251001d400741c00c002250b1038104107940000b03c035911400c080c0003c04103451080c2000720b10b0068034895030400b848503500440d11403c0848042d40d5018114200c03410004040c01d15080400d0290005009500c04003c4501c07508000c00100e19440000303446503c55894440b0304480c22050008565040041c4500b10354542084c1e0007500301000003070401c87c085260001c6054648000640c12034544968a002c02014000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 540933588 1250 540932338 540932383
    0x304090c02010f0f09020411030c041a070b1e0108031e070c2c093909161206060816030b030703140f2116020d0b010618050307050103020c 61
    0xb41000500f22212051f8461803c00f0000000005801c084034001e03c20028420300d01481c0103541c1c1c0701443c2003a59404411410700c610000708545000c900d11900720340880204108642c20b000301c0500d0180c1140030594424130010243c024200c0d9140e084022111605071107000c0f600e00003003009074a81000001c441c540f0414540e80c6560b440761000e120550004404907620f45d00c6140d0f80e003185210743c41480d00c03440e42003c01c3c210075200c0c5044202c10000341e480c03c0c240f200301152562200b90748800c40031640340041c10b44540e014141801240f1007490500c449441e1440040038884090480000d60244080c40c110150081c4d001c012600400360507500740d40c0e568104030206481e000701d454018011803191052140d800f09990540d440c800160300d411682141e459a10364101d030500e021003903072a420301005661a035a016000c68440d01d1005180d40c10034000130004041e040c0c0d032030380405403114180308580e0b002c6130304c50540f602071030010b8036034440c2e010003841d01c200400b9825003091900c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 540934838 1250 540933588 540933611
    0x182a06050903070b28050c010207050709054c080a0203010b1210020315090f0a180b1b040b13053606030f0d0306030b010806040201020304090c02010f 66
    0x805819500d5040341601c602c16031300c0260540c507105280e620400c1c1d014481042240086140010945c3c2c680c5141450510b015121011708903400000c066405500201c0100a0b07004a4012076502c903280246008280600c0400c0c000e0f62042d500c012541e42403150380d0107000c45503005200c1700c50704030225003800c0c495803042c07516107a070b4020700143d0081d401d007030300d02e01241005003842415084000040910902030700c40d0000a4202510b010040004a51101e40f15907030642e0b00da0081c2e0404140b0b04d000d003010402107040b52000340e81e0080c0034031420540070120303640805081d0310020707220110304600c0550170108928452900700300c03008600030803500350b04481441458142d4100b82c81c9606a2441c44041c22800009100303001c02c586403031500c10854080074600e090300f241003e41160b40c040c5514a80ea0b041203111900240000d554010400503c006601e03918010500400038184504007500005d40300c0c0b00304c1c0200b4640d0303515040c0088a140c0f00f58040c00407183c40400400a044a04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 540936088 1250 540934838 540934847
    0x20f0d090305012901080615270a15050706060312030c081803120a1404030903050601060e0d0204020c1006180b10200f070906080607020111161502130315182a06 71
    0x2801303885902004081440c45402c10007580d4058400d0ba21400180c0401802f04681c60351109070101da0403610323030000100184054044941c044001e44001c01c6040c40701400a121200080941d9140d001e00c00c01c0848914010040b01e0641c0c8662042106da075407541c0742c04000d03104520b44000915136800c00c000502d03a1000c4800160b034402d00c1601c5659030fa841040f104240001d01d000d9000848940c501d0040c6000d500510b0400711040075601c0400360b00301c1c01c800311003003039000d5800691401011030011019215042c0c010b1800c8400da411841050070081404103451484550203c00a0680a508000300900c40b20710b01083d0880300941d440b081090060080d034820000240324240110341d5040c01801038202c40b8608882d00c5082100b51100328003144d50418081d503003119221001c1840b80c550340014400b030340e0480c281401440c91071800f01c2c4810500c50800c400f00d0300e0412060800c05e0101c08920056070800481054000010960300100140c41c0403040e0000400303100042d031035000b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 540937338 1250 540936088 540936127
    0x5040201021006150c0212010c09052b030c080714280f03081b0304080711060f040504020d0f0e070911070312020a020f0d090305012901080615 63
    0xc0e400d035404845584044801d442c0d01c0d018021404c1442d00749040c3c4584900c0b40903d0040c0020f244020007113900042030308480e134031401d600002d00b01440611207070802d0380d420709140b82e405000051644040c1d0158444a0104400804005c0600040c900340301750074050741c40c0d03660804006428038400d049015503641135100d002c001c80f0140c541882c2e1405444184045460f0000120503500b05280c1d001c8660400040228054490220107050010b01d220041c5104610900d1401c0c2d6071102410b100b044500d003d45180c2c402c94040200b80000348442051750700322001070b607001d80c8074000390114101070b00c0d065080c040c0f25850585907050700040083c0070411540031100170800306c0c0c130405a402e5244075440024000c108520124281000c5680c0180904d001520558480c00b01440216003822806181000080e543c3c4500f4018400300384a101c1408403114044442c000250904940c9028003403000380c144446a8000f0b82e60b6201e00702440c42d04200120155903400b511a800b030001d802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 540938588 1250 540937338 540937343
    0x40e0f04020a2103030f02130803040509090c0a090e03070605271b0f0d020a12050708030712030b0f090c07030206060d030c0b1e010306050a05100e0105310504 70
    0x2142c034000216980c00140c944048050764201400541207601d06502520199503801c074066030070000e010500403100480320150092402a40e0ba503032404082200070140030f4005030040d0859101c104c115a80c00004d01c0440b02e0001012078202c0c1c41c40083e0b070440c002d170722002c0d1200c0e060504204140490b1800403140800c034032400192000c4110b0b101e95515500007032600f1001aa0621141c0342c80e2a010010b0b0030350004005001c580c1c00b0380d0104030002d45643c0003500b4044811644400c0010030702886010f0402e890055051405070f84503103148412000881f01419070b01c11030151207031192a0041079a49002d0841916030400030049000d03944418010380c01070041102140c054030785101c50500c09034141e541c101446c42c0c161160380400101900010641c04899840440f00145003103050082d030140e900000c2d1490033006440655100a0200440300380c4a6418080e0090565149054a0007610500d6440958031003000c10341c80441d281c0d914400c00950303a0403003401d0b507412a501c103a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 540939838 1250 540938588 540938599
    0xa05120a0315050310020c01090515040201080f060a0504021b120a120605090433020a090b09090408090109030215090102070f0f0b0a0e0603040606031202030f120a02040e0f0402 78
    0x6903410750000b240c55150040c140e0541182e2488244000c1c50b8020300030741003000000040d402d0041c3c0d01c2514100280c44050740e00229070080006560f00001380c2c507030100800036803200b80d01e00700b000110703c924180101e600c07a59020800c0d00c105d0380c0c440c0ca8030307940500b8207003115050452464a00c00c00d40044e404c250000380d48254100c20000f0500030182200c0001c1c280300c4098445a80300481fa85c001129012460f0400d00c00d11524108840612a4400011001640c441c21650001d00900307450300482c00c180810070a88001d070f102c10f120144c0c0700e500041825159140080101c55115003540065401603441d03d200c03500403031b02401441200b809808941c01c0555503501198120f8640c42080c0f1456200c100801615050000901c0f40030420703e01111030b642c246000034040e810590301950b5455549100b4030401c0402c00007a1070482c224001103041c800c0d00400c2002d40d10405005904031546c03c2c0100c0c410000a805807800391034048070951640c6002e80c85458a4101207070300740c4c03255 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 540941088 1250 540939838 540939851
    0x80d14090601140607021003180c03150911120705030f030d0c230313020d0b0f0708090a02010c050705040509060a1104030b04020402070201120e010b0315070816020a05120a03 77
    0x1c50494800c1000c000f0141c40c49003440703c19020044440c0c0040c00b04002e01d9128075227000c000e041d400300c620040744100381d51480f060070740c1404d50031080003850b0441e50038503204034200400d565030f4520141032400c0311100d00842104200c0c43c02c02c503041d88030f40c0e0148100500996036020210241801d038030705d00c20812140c64945421500d00740741104203080114800040880c02e9102001954080d1008540d84d50b40e8516901150990701c04a1060710b048140300d00340118032001c4a440d6411600300e10381000342d030521423050364581c01117180090500480405100401038140240c6004201c014020011490441d001503152582180c5040e549494220500c184c01034103000c2c1c45c192900301c00352410980d01c1da1300303000003941300340380c164180038540078044001c400c00c0c0121010400302200108903044076100341468040c01440724240035210404001c500d40d80840e43c503500c1034504480c1d541c03044020754107909010318130038042d169004403008040e442540000418081c9030907681013210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 540942338 1250 540941088 540941099
    0xd020901120203010b04150e090c1e042009040c02071701020403030f051201060503090309030a030f120203040b0403030b121005040b0c07260412050601140d0816080d14090601 77
    0x2124020104480d003885405c2003444100b002300c400c00da0000e001021a8646000e01001450116644803d4910a080403425140c0d50525008d0300a240000054050405400030104145401100c54090240f0381d541000c1c01928420400000140429001d10048200e0840a103010398031030701007640814074004d44d54038041d118000300d452040a43c414030040342d080850860b0355500141c038014035440184006546640d00b03000c00b00081e40b017501d81c1702c00300c6000c840217000d0303600f00d8a0010034a44107000b048082003040d40c115034050b80c103246c009520f4010f06c0c0090000050401c0985c01445801011340944516900c228080c6004d043c00e15000d69520640001c0d038854107900030040d00e1b07407410b400c0b9003e894a801e1960410ba880242e1b00700303500c50040c0080e2502c0950151071b143d200d07100411442d500303140042d5a01c0001e48803103581e01032503101c1034802e10078024000d800951898040c024005180143c0e40c0424100302c0a000078052480d42081801041d13a10140500030100000344 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 540943588 1250 540942338 540942341
    0x4061d0c31050f091e100b13060e121b011701030c03230d0f0917070f080d08012304050a020a021020030402060d020a020a050706080708010902090d020901120203010b04 74
    0x1141000c4a020310107900140105c00c0061401340c0341d44520304060002240d01c070b03c402e0140540f0040d009052060600e40701000745440315a031022800b03200000000301d809207003c0341c3d0024124003032503410781142180004a40d40400e20540101c120f49480002c0200900380020004490243d00400714131030718081c50341940e0117511819885940907504031416039004205208881116061109009552b0058455508041020300c0e80c180c0000d03000740702c21040b00c401d00c0f02808038007008082c8250090f40c00f0300707001c1040c00341e04044c000300e030303c040791441d4404010041003038047c01c180000c0c18980d01c03100203034128480301c070058050a211070700c0744060f51042c644494846c6401846140c03215000d030120790320140c400d03604030904000341100c075400d500003003030409407070b5008001844040c103000e130030444250000070400915100f880000da900c1030b040c6065402941c1c4c01a510555100003071281140c04070025040501c000c0000b5152169640740064640207500910080c02d04404020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 540944838 1250 540943588 540943591
    0x108010b03060904020d0602030a02120c0f1c090c06030522051c051603020f120a09050105030601020a0c03060c0314090a03200105040803040204061d0c31050f09 71
    0x5121001c0c8001403941c40d01006140d005400500a442c4c03401ca10348035042a81e0048a10080081c0c001500713050380781d811650560300c0320300e500c00c036410080d50320b6180c0700b2481140074480d80740e5000184410f008403140d0282d40c0c2954000004c07581e003691501c1c09405000211340707400c40404000e94005622444480303100e03400e580a00503101604503004440041075140c0e1001c0d04100c801d000d00d2202c200f56940c0d03500103501980081c03040c0d900000915141408045201c00428000d200c1900d10340e81050750340043d0303042424801d460340d84800040b8600340c61720501808401500000006102c80340d841041d00d41c1c12940c0034000c0041101005440407002c0d40e40c0178041e8091001200424861018000528542090400c0348003503901c0c02070075102d00340c81c261030005001090004604e45445488000c1000709144400d4054141c8501000080101008025080000e644c170021020722000c042042c0641d2000700b50714601005401048682e00603d80a9201e14010350709a03c0d1001215 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 540946088 1250 540944838 540944849
    0x70f290913020c15011211010c030c0f1505040614060316092a030b09100312080403110322080604020d1b05060f03100614070807051c0c060b010801 65
    0x1052008001d0800030000d40c402c40024225000311441400044420010302c1d000703142d20480c4003150307820b60070b01c501080c00e1064814140441d2410200c00290000d5603084280d41101c2c1c20312214042e800c0c200412031100c002100c40610304401c11081200c141c0c0150071082a1014455041c0c5d1210181903448c08054420420140920b90400060f04141c00403508107007904000d44440e01d005001c400c1040b9020040c802003034464000e1f00850401150584c3e100c00411040000305195494039031001222031030031003c010040c000102454007505501d00340e1a540c808981da2440004468001c0d100d029404904205070010005070056002031710702e00964004001650701d4845955100c03520030a01031811841101d03030300005003a0380e0080a0300c10262000c1c0007580d07134500150201000083c07a0031440912030440e094540041c144400e0f01c2c841540003000b5176596100d400c0140c0360800c0d9543c03400001042e0b0760f59002055110940000300b9200340c0c410b0000416410040d20120b0090144 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 540947338 1250 540946088 540946099
    0x3014060609190f02090d21080c030c0304030e0603070c020118030b060d05010b031504060b030f060a0c0903020a0807030302120301061b02010c050604060203090c040e031b070f2909 79
    0x15941400d002d5840b10002c09252403005103803040c5813000c1929001c1d441d0041d503c096844031104500c6280300c800242c80c0d00107280c01d80c1e5a280c4026408038902001d030a404111741c0100001d0101801040e02a0000304000c1c4825100d00c0c00e800018a0052520030072030010345000c1070884140300c030002c440306417584810a461241e95400c28007841e90811907058820b5906c4010f030540a4502380304c00070514001d165108075a14007402c1000940303200d5072417503000e544034041d10600c81002007815034012190300030200e50f07903c07030500441c0d208500c2d800181d400110f2034000100c8540028032a01168030a0302903c00302c006940528405000920036400840c404d0800301c41030301d01007040f41210780c1c414104415401c400da11882d10b0b101003200d044480550000900c04050001c01c0200c0c14a20215024025162804c02d015260b000c1c1103015142ca0380541a18503c078001444030201611040300c172881a9a525225800703188130700285d009241061041c086890b00041c0115400003c02416 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 540948588 1250 540947338 540947371
    0x51005030438090d031811010e13020f040e07050c0c0f21010e1b0a0509061f0c06051501020a0f0501110f0408010c090f3014060609 58
    0x8007500701e103202c00094040e96600b651036005091180c103282c060510b00005001c0c0c903074403050240c1181e2180030405440d032080b60804000511740072484d00903040c203292031029900b00c40c010030f5548000c86219100c4d1030000c03810a69811501003d8811140301e60031608140c0c0301d08001365440d22542c034420910380c015090a0459003070107500c003000c40c3e00c080c0013030520807608031000c035150040c0064485640d444690450a20303900f0451840000041b0040080b0540d141c4001842080548205401042d05e280040d0a942e034000170507401011940403015401c00d0080c3c0108603805101044400a1514000c10407166801003a40c40002060b0010004080c0a07154980d400f6026203044884e5134940900290007600c82c0044c001031400b03e007480b6102c0e410048802c2c00c0da03040404200070420880740c200a128512811072084030800d003a00560303944243c20070101d640c50464040c001091490003c420001c2034800503400187d118103446058a580c03082100f40202a103017440700441509 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 540949838 1250 540948588 540948623
    0x1103190e03030f0c07120c020102100507021509010b0907020d1103070222240305010614150a050408160e1008100e010b0d120206131a070c0c08010203010510050304 72
    0x100c0d154200c3c0e00f90804c0c2d03040c600c069540840c1b000c100d441180018901c15450310865804100111584e55190402d203d030345010500259a5001850340c0740d13110b411000441e1000000303503c40001c80d0790142c0505101e203081e8002940d62090500c090000503107a075102110301c400841511200c903802840d6182203a02c6541d800b07500d03d844903404188035079501c04e041200d9a400003c40801d4260030203801941c1c95801d0440c2128035031b0780507840c40c00102c90101e00e40e42d07174204610350300481d2401c40c0341c43c2c2d20060070448541c0200e030040c66140c4240c50031885c4c10102c0219400850b0f03011010000c441e580e8801e4900f104d4030911801056030302100140343c1c04e50249e04640311040d41d41000250807040c003000158003900d154001d84420710b8241151140950501c155035101e0780d81c4464800b40703440d41e03032401d101c1400e950585034840d00220108012611031350390041c3c02c54104144a00c1d458031400390078000d620030b12407540b00300d03411802001514001d0007070349c0c442e40d0080b500210310601107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 540951088 1250 540949838 540949861
    0x4030308060f090106030c170f13080f0c07050f0d020f040522080706050f0108030f07110409060b100e0108150103021911011a0904170d1103190e0303 66
    0x140c010340c2d11a03100d6007030000c00d84802800078002c2800307603404101c2e00d85185014100c0300e00400d00300140030044c070401c80f1040c4070003141604403802414007065207130541401003070f50080b42d1400358042e0700041d101d5a00030000031a00d041d51000c68907551403c1c10310040010044520324020342000c034103a4034100c3d62400d5404554040131020503c01c40030800c41c0305440c0ca8018010071a01d01341c02041407400c1c401140b01d250b034000350361102020745504101405640340180540d82c0503069001038641b040202080c0091400800a4402c0c0329803080d0b481d00300013402c02c2e0b05015008030802c15029840c20b00c2034540c0b000ca8001a1141409500d40d040c000c0b01d21308952041c1c6040c10303000c0000c2600045807a0350035508540681d02e0740e00070b1000004950030344170030790890085c403000b154200d015aa0380d94111500f155001e568061903021034000d4403000c2c06021151510240703410150351001c0c80000003144a4008200800d5222013000b0110045075032601d100c0340c461b44280b0001c0e60481c0380 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 540952338 1250 540951088 540951091
    0xb06010809160e040605010b07050a0f151a040c030c09050d0c1d09070504060308030a02130b040f06110a031403090115090204050906010e090a0b0609090c13091104030308 75
    0x300340d4040c00d00800c5508442209035100c0f100b400c0901040000340b000620403e4007400200c80303030301d190014030b03122503543d9264a0300c09410300410300c000d0002c008001001026200020f48188241091010120312000d007a411460059080c01e400802e0980700344546040c0d10400c0c1c40382002e16003820140500754604c072000b161954460348002c104200701103807a28402131a0b00e080000d46c40c004103214101100c91b4050f41c043d0b420104140000384041c0150383d88440c0209005850340d40c108124500e4007100c1e8455031100200013008961210300340f81035400d441e0030342c90340c80d0781b209030520450b074520a5000140000746210081c6125014000c021030b0403180010012440b5441600d12400c280240c9d80712521041d4001717410441c6003021520240d100f007003428500c407840441004580c07040c0000700004e182c1036940c036204125550320415075050110282182d005840d02001d400f03590307030010f40040c2c00410214400180c000d0349000d1820380d50641464541042d2541e501503814050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 540953588 1250 540952338 540952351
    0x12140109030813061d010501051804110108041b03050f07170a0b0c0f04060f1205070c021201060911040503060906011203050a110f0601090605011112030601050f0d0b09130b060108 79
    0x7224105d44510589034007201c41d4020400d000040c00d54034100401101e0110f4052110032490200700300700c0454103440c508000e101080c24407100540e0b5625111070b6103c049030200c05052106240402844000510381d542b0052b41c8045400940e03c5c0e003896841320912125440040e0f11100c800c000254610710056007248001c0b110741c2c2054051545103669030401e4015100055091151000450740104d00360303d5114261020801070800240c01850b40419410280c040d411102c1c00524603030b000d5019400804c2200010001200d00f440d98040139801171080500c81d04c21140401d900402c0400e00c0340c1218044c00b02003c080b181580d050380c694000080d0782041c0b00fa940407c0101103000e000c50414821658094141d42d810402c2d580c0880700c158000c0d82c100001048180f8910310002524000701285c00b604d01d48980d113100040f1254800c40e2503401d200b09003c503510881400d280c0280f031303002c02c044800c08040d40e12103440c00b0400820500203000604078402054455000320181c681200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 540954838 1250 540953588 540953591
    0xa1202011707050a0f0f02190c0807090518150a0b04060b0403050609160b0901120906230105040504020d021210060b09011211031b04030b011214010903081306 70
    0x16a140d071407a501101118000081100004c0341c4242d65880100c40c0b503800071505080c41c0d0034043c02c0b4000d40c2d81160000b010b07500d160f04040001481151080103004140302c4048034007003515911007102421003612030b0311900c0c0c60040c45030303d41000814000c038420081441d0292079a0b400201e50081c1441c0c42406030072940e20a00406c1c03d1001000400145000358000c000c2414a0307001c6c14500560118100701c102444141840405400740450f0941102482c184404012902110000703203880c0781c0081640d480d00703900621901d040e811944d4084c8075100c54082582c0c0e036000340002d4600484009500100d0383e038070003006180140c04203030b407000d600c0c0c1210380b8030a0005083c0f04403455500032511250010a1484441d81e015441c519890390240e0240444922119940384600020704050461a03050308214142c2e0680380a8400468100c0d201090a580d21300c1501c0e41c01074103d8095806007203660140310080e105015200c02558103994078000c2d903850003003480b652403c1c50b6044038100d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 540956088 1250 540954838 540954857
    0x804020d0f0501020706020a0e09010506190306150314070516020d0816030203180607051203063c0d0209040b071419080601081b031902130918020a120201 68
    0x402c00d10141803075034410240140e840d010b00c08040c00c94010b2040c0c0510131194032005110640782c00043e00c0c514141d10801c1900080c000c9010b4019007615001b08900320f600c8881c1c4041c860385500b08082c603069045424003241c54141c0200c505100b44507a1620798403220740240010305000044c004090b0080c0d10031410664041d03003881c6c00c0c201c101025801640301007003490500200b1682c3c00c1044808071820751030070089a582e1070700c1d41c1c51005544450b00e40440018141d23140c03107191055981c10650131043d482c041c4c03500794030241d000400303044100c2c0a00c048050507040c10880c82c0f2415400030891012682c0759581c290920700018820010416820a501288104640a040741010000c0c4c0c6140003805040010400341004110307504114082d070502c0300c10752000f01c100d036144821102c0035071343c0d81e9602540751459900c41c40452080c0d1000071449000c03c08004003005903040d0031010302042d020390140c1e03000c05000890181d489403c510381001034800007420006903503c10b041010701c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 540957338 1250 540956088 540956093
    0x1b0803030f09070605071a090a020603070810141e030705060c010b0f01020102191409090906060307081f0510030803040b0a112107120507020106080f07060804020d0f 73
    0x658109503030088250300d846080c026849801d01c00c0c80e019204034a04103081001646a802c10300b42040001c6500d030380035101081c0355440c14480307120311640107402241d4038102100010131100e000c0700c201d500f005a03214046210004d1034111070b04064010582da0a00300b00001c9101d50f047e000f94844d034544507403200003456032110b4026082000314603000140a006100c103000300351412108031411644101708000c0c012000607400040c003049440c1595003400920f4001e85144600c4a0599200c000d050030401c0c0040000780d01481888240c06039a0039640c1c0740c0c12207a8420303014954503103141c603071b401e000c0c0e50340900d5100c1c0e0341c003081d080a181280c0d542ca1b02c80c10250342c0140c0d401c0d641c525030102080140155401440030401c1d0780710b0510301c0c0a81080c207003415856443c40012407140b512010901e00f602c6007002407284030303418100700201d04001c43d0203030081c040b5102e07075940b0713020300610400148800316004003298042d440e080c55a584641c02c1005500c1c060300221400611150800003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 540958588 1250 540957338 540957343
    0x9010603020a1206060e13091a090102040302090f0a1503050601141306060c0302120f040e130219060207080f0303010b0310120312060e16080a0e0105090d03061509031b08 75
    0x18016a04d801c068400b1050a010047c0d8118200094030b5003025105000100b18401d0115402c0c3c181c040c0c42005e031205190316019101c0e5501c060340c40a5a4000d00c070034840d0243d086801594000407c00c0b124110504900f68440d40d0300c8050525008000100a66603110544051034003006014041d0300303480c2d400060803101903070001030014003161010001c00d42c0420403030b801846091482030401003907020a50301803040d0f00482c00003044220200f9030440c2d80c403004081050380108a50941a00d501303440d09080c03418411f040040c420a01c00041c03a40010558505200e40400698690383c200306450b1080da0014102075465078030500000780081190320180e41640c4070741d0300d10701e1040600e151842515410b800c443c0580b0340314414072056401003035030803c0250044c00d005415075100f11603400180b08078a000207065092204000c0003040104d1a000c9684464504010503912224488e4a900001c0208008210441014404158180c0d020301c2d200c608101d003640d006840303208007030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 540959838 1250 540958588 540958601
    0x601030618090506060105031003021005071a06090a0c05030a0504050708070e090715020a02040507090f030803010503190c0b03060a0b0a020a03120e0703150608010203010305030309071409010603020a12 89
    0x4078195914a000d2040040510150350004400d00c1e2450850401b85240030030090f00d488002d214143c07400c4103039440c1c0d01030f409940c00540c204105140c2410f41740c407100c15085084501c14480c5515034005070850f4203908c5400b0030000160360b10f41c250740c4c400c90958000c0002400543d0907102e541d00028444908002d104003600d402074600040d4203041e0750b401e10307010050b00100005c82c801400301146580c0041c502c454141c04440200c0c1d1521580410f448040303550704a103650b02e8003c00b010050001d0480158100d030030540841d10310401d0600700001204850324000c0c82101200801c0007840c4000c8007461300918000c3ca03e0f01481c0e0355442d640c3c4d40e940105504005600b003003104009158000c2c1c4d0070350400c81684400c0c0000c050310403c040d12821036000040801c81540c003940c1c9018099400040a003810400841d904d50b124148165250000c442009281c413940310003241d4010705140e81c1ca12200b010f4011045642400780640c0a03410801200707040103407040c02034410160501412 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 540961088 1250 540959838 540959879
    0xc0d0902030a063608030a3314041803140c030a11060a0e120c0a0b0403022506080406020a110a2105030c0d0e0304081b1e0102120306010306 62
    0x500c80e1000c401010080426038407210a580ba40d0241624081030400b401c80744d01a08800c4006954007070f0707050074800410340c0c523240e0b501070704c81300360307444096582031840d01c20384503d842e1f142d0f480c0d1140c034200410369001038014041040d40744400c1c40064000d43d030504414040d41c5509080c180d00d1f03024286150000d03404600041e120510982c52010180440c40c1c0001c0c04560509c16450309010050380c803501d40c0c00c3d00f50030840001b1451200700c42401503503011640700c44040d15508040c03d00030750359071480c19a01c8420780513503e00e1781042d03540040d00e422141d107501c0d0903186603103689490b030094000500c0300c1d09010261114444040040c881000c840f4451400303904110a4985e06000a54400400ca414042c04100b4049000002c500380c4000006045e40450744074040c40200b030540c0255030220350769119040c40c8500400901d480c05070740003070694004003001d00d196182c015062800803140d015030490b541c2c00e018607940c00700442d4410410305000ca600ca9990040c46203899500810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 540962338 1250 540961088 540961121
    0x10020a0b090c0a06022b0e0414060a0f0f03021302121627260d020c0103150302130504022d3d020120090a08060c0d0902030a06 56
    0x840c141840e00f940c840c0c019081c01c1c0700800c2058044106505842c039420100980b0361281c0480028652017400e07810040c1d0301c007030410700030241d40c00001c004a61090b144540b043e00b215202080c2c01103504054400c0f911343c03001201680e861078003071110341002c0800950070582c007080011180100440c4d40c0e0300480390105480000000e0301d200401000c5440809056205040009070240d130740f0140840130b9440400d049445280025884007004550400703002660203079130080f50078a40c020442c2d00741588280c03030a100da1070201c01c2d001400851800000d503c400304403024460000590f0040e54841d1000d40072541d17071200201da9110200c0780c20310b441500782e81644501414201540d00783e0000c0c081c04850008544c2e0070040304004a9019004041404201c04001495100b5001300220f030302d41c13012446216281001e829990b42c444045d80b402007400001c00101004002080c0b4454401f41542c241003400070325148000e041c02003030070b07079140c0b040c030042c0f0000c42c00c1c0384030300002d01c21140780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 540963588 1250 540962338 540962353
    0xf0311010f080c040308091f26160f0c0203060a0c0e04020f040611030d1802010314010b040603091505100e07020109021c021807050a11190210020a0b09 67
    0x144040c14541e0003030100482c0a09001036911004151401e481c0d100c40c94540301c000c00c00104a5162080000c6a0307441c0424038040720241d0031404050011038580500b00115a000003001e80088050300c450391801c0940b0134084086105074810541000705161011249101e6000246860402c0c3e8042000585d60790340e16407985e40000302e4500f0709074140c40550410070020100340b140d018920035241071004800382d405010906004032000703002000010407105440740c64000a40c0c81040b4100c0c003107072800780b900b1010b0707011010240c121450f100c85640b17081d080c020101c2c090305144104a9160142441c4040d8a9035036000b41480713011569022200d13142390801406421802074013030000c1d6490716107514003513180c1152900313001c0710350110300b84941e82a00c0401c0c6001c0e1182000350248030460309200c01c26a00000410048071156940e00701e105000302d0300c1e07071181c45210b1483c861540504068005080402903c0b1035a42c207401946c06008040d1180707070403644c0440741074044c1d811410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 540964838 1250 540963588 540963623
    0x220c06030b030a08070308040206070b0a1a0108040507141801080d0f050a0203030109051305031b01150b0702120c0306010b0904060603050105011b0c080f0609060c030c0a0311040f03 80
    0x1c624040030a04400a101c070000030741300c14003140f0408401408201d000c02c00201035440e1103045811103503002050380d40900c0e001ca844401440c0d51007401c04041e0074000603c2040d03106444050207181c000006c0e05040349482c1e294484000c81a01682c0c1162000c0c600e036407040c0360480100e0082c80c07120080d01c00d01d0102d0900038080e125031010300f030030700c5002e00070f0100b646d50000a490641d03100400018558070344550000d040f40301c5840c010300318800024018035000500380c48010054080009100c000c180d01d054209010f110300410510400602a030809480c0840300780e0309240d820300a81c1d00c2c055680c004241480c070240c00c103100352400081c0d8a4000e007002e21941000f00018501003000707506110008204400b1504c41d40342e00000c0394000001d109d200319016004220b42011600030b154000301007030b01c601003102d00103aa070081754002802070250030120303482400ca01d00c00030310b0318000d0740083d001480d040904010701c00c8207200100c1e40003c601d102102640c01011112100035005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 540966088 1250 540964838 540964841
    0x40e010504020f0604060503160507080a020d09151b0c0f24090e07030e010b22060f1409040515010b03040b0702010b0f0d080f0d09020109120503030609220c0603 71
    0xf44550b0103034030b00300000c000c0c0c00d40c041c055a400c42e01d07000811041880c0d41e04115030314000c401010304901000035909007215000500a82d50019540310090742c0c5039035000f030711515044580020301103005280704100d05046015090b005500c42c44503c031038261201d405160b15503480e00f007008150303810301081518001d41c419001d00800d0790f180c049026800c0040b005c40d48280982501d0038181c84d0000076289000030341103a820800003410720749040207100d08501240c0080c900c03580d0082c0c40c0c40004900d040220418509413158580308181c1803110350305001440d00018410f542c1c0c0d010301c070040450030350f82d4090706000300142002e0b580c40c2d0400d402e001c441c110000c1d0211065a1400210780c101e601c400c3c1e803d0000d000c04851318441c0300d00c282090400382c03180070740070120303c50300041500c42022181d002019090003a61001d03551074031000d594811401802e005040c540c4103000142403440c240c0c4001d076204000300a10082214444c8862585211f801001c0324400d150001c01c1c03010340e616 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 540967338 1250 540966088 540966109
    0xa0c09080a050c12010b0f0108060409200a08060402062b110909090d020d2105090d17040c0b030a060512100c050406090e0c0c0a050a03020105062d040b040e01050402 73
    0xb03130000304050900ea100041001150040b218103010800c80040c0c440e0b070303641c0c0c00701004680195148010405c902c034240c1011170364081c5a403060242c1c01000c12941d00c0094240c1c072403a03011345200c0c5010704810711100c001201804400c0d205941e100c01c00d211001070f01942807500c0861000603104d2001408102180070f00811039802548120010542903900191030301d070120860820201000d000381d031446000d082101c444004d1030610050101c9501c2c001074885260b2050307a100f10740949400e02400040ca0207680c090007191a2400a0007003200250086030004107144002808541e0360002c5040410304d180030200316000500988a07034100d40c000c1e09900d54a5240191901c1d04004016080240c54007400003e958020000790014144500301c402500299003100d80008840c9000c03a99003c1d0028114015402c0102140103401c0c44080e0f0401c01f00d900c1c0b030700d000c041d1659104000c2660314400c0e03240d110f03443e20303200e00150711a4031604500c44034120021400d850b007801400040f100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 540968588 1250 540967338 540967369
    0xf09051005150a0609090f0501120813050a030f0c0f081024080a03120b0112050a090611090f0f031513050303012403060b030a0c09080a050c 62
    0x1004000400140041180040c0c406900c000003042d480d400c031042c500302e11007400b90343c10002540001c1200b03a0030299920846600745414013480c3c400c0300140003a280e0a201d0380d100c0301143c8034150001201c100c050707d0419020f005074205250344100284515050707502c240c498210700c0301040c090040407a08040548400c00b4a0390301c2a141001d01690382a23011035050000707075100041946004908400d0000705c031100c401180c01501c5941c420385480b02c111046000c40c04002c440341002310700707015000014405846c1d000c0b4100940850b01702500008044a515a1307440c61118001007940c8a00d103020201a004c4540703600c4050188810080300041d400c5c8960761000c03036a4525a00091030034032030704403225001c1c090b44031403040c10418100e26000815070301001c00046828160200445104268400c500c2c0d081c02c0034103820b80807105540101483c021742080003540140300c50300030501322a20b0b072034130410700c44d80e542c100c1d0709115a90100300c607650440881000d42d40740c4082148081c80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 540969838 1250 540968588 540968591
    0x120f0506180c160c030210110d0e0108010302150c0604110f0901030b06060c031c14070c0b010311032a090f0c09100e04050702010c08070c05300703030207060f 70
    0x4000810803254041d491102401e003c41d020100304100401d64510025580130b007841402c0c142c45500a8070034201103824002230300c640e40e0240740141c85511aa00d403070348181c4400c0c4290342035409011941c01c01f501f0a000302141003103042a100c00401506109078084c003180101d14240504004040548c8110540304800700c400500208d02182082600300d50100c4845a881649100e150306500814007040c42403100c0c0301d61951100300940042c0b90140c40c19003c2c00c0703d55500001980c0d650030120002d0300d9a141000180005941000078400c4a2802012110044103040e00942c00c00341c41ea48000c071900c407541100c0c4503420401c2c1d020b034100030a03c1d0401070714500092410080c0c0103603401d1b1072080301030707500e41c0e0038050107420b0303420b4940b5014002f0700003840c14190180c0030b44050307184400010710190000e01d62522a4207005129544480a0540304c001180f8030140c3c8a0140545403141340c0c0c0c07079054400c45a0721300060450601c65140540c480c800c9040c000c0464050092110404c2d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 540971088 1250 540969838 540969841
    0x20306010812040b090117043503041112030714010b010206130b060f09010b130b1306081b130608010f050105090603040c03050f0a1e0c0e0403120f050618 68
    0xc1040b0140c1c0c0a8801203040291a1209000121140c0c0c03290302030380742400c05a00c180820f01408040d800c40310441c0d80c4046d5602481d0074000a002009200c0c10380d88000c0505c0072800207182d401d4400401c020003056594084000f003922400d55010316801ca030717030104501c2421441802030080030484482400a0041407070112040d40385580d13000c00041104582200285e5903035580305600c1800e4902400c1a949503840e0a84042103520540840010480e84500000d198501e2000c507016203281e103c44d4540c141c45d00209407a900380141c400000b43d06008140e404030300b009006441054101d92055408919210000d06440c006811000f58030f401044140010b0b6008012110008400e640540da00ea0322170600407100440c50704000e0050040e48403145410200040c81d20740742d402104035104c00040701c00e00e403001c01030040f402484030342018400c00c030a041c129100b552160103030502440395018540a03004941c0e281c0700c1e0390b440954581c2408903a007000640c82c0c10f138000c581c6840800303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 540972338 1250 540971088 540971113
    0x51305120a050c01020316020c090103110d05010b030a110a0803030610080a09140718090209040807030c053003090606090601051623031303080702010504030f0f0203060108 76
    0x40d910010064031035800009200d1070700341e204000300d40390070034414003c42d26805c0c1f500f4041100c4d43c503d6a00001449131009400942c0b07064403000b81241d9020b16440104458203003442000e64941400f50343e80d540c6c0e2030300e2034240c0c0c401b4014074003503d11031001801e0300e1003000d040001c041c0d138a8011050a52050040007100e450303003801a42d8250250070b180d115641c80c5501c000103004241c10042445070f146d806041070b100000391a809071a040440d003031903d808184840c04039030510401a60082035480850045007d02c0000c00d840b5001c1d1600041d01e0800342c81c4d540c90504001c070b070301c0009504075241d2001d100b0701a0729002c0b110800380c0c04a281d801c005c00d4669607210301902d014481c140d0180456a0f40e8010340485400c001c01e021613610744a418100400810800d1004045801020403031080072100403040b1581e40c01c0341c0340b110b00001d0a64503800042d0304401800c0f81480390802000c0007055145415048943c41a0306904407413800384103050900006a2141a442e03000e001c46099 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 540973588 1250 540972338 540972343
    0x4090524040506121507030b0f01050702150f030421140909090f01060816080f1b06040b030f04060b01050c1b0307151e050414091302060319051305 65
    0x51040c1103070041015150000002c018110180d0400c03484d02c00c00015004000080b110a44100c1c0251000c0110200328011f0002441601c0740031800100200030500047c5060006e8409a1141010341801c201044140549560054605445c0d4040e1124030214103500c00c0e080c085000c045103411000111000c000468030300549000b40d01c10340180c8001551414100640f001a0098500038005c25540c0d0030520b440d507100e83e90560340b0140c001400f0680703600c006501e0078148200c2000f04585040c81010404600c01c41c0d06180c1e02100400c80002d2888103100654015001501d00c2020b5040c00e161038011204843c0220741445000e11650341200340120720b10020b24010140e1020007240c10323000a0030a00a500011400c2400da24058641948030325608031402c0304200312005000100b00036201805030b48101003500764803040300f100a04003645695001888100000c01c4800d0b240d00150181d0000c84d00c030207103603200340d102c0440038100e402a2500b2000502c098200e50405031102d0f40c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 540974838 1250 540973588 540973651
    0x9091505220f05010f02031503010b18070f0912060b0907080411010c240c0f0c08040b0a0201020c0a0b150a0e060405060d060606020304030b162307080f040905 70
    0x42c00303a800360700c1110600800303401001c1038551040f0115540c0c0342160f103a0640c0074580e40003a02940c03030188004514108040074244c1c0101c001440c0354265190102151f1181c41d800300d203000c009040000207071480da103903020505103204000200e0b500540e6414090082801490030040001500138040450302c2034410b410200000e1a20012031503040c10702105050030700d0074048014003045140005e186955012014018050b920703403e00d400034000031076a5400320a4082e0060f44108810070404410034000c02d804829800007506183d480721010741800b04082050b21f40310401d00401180c41c41031554500500f10840d0703400341c0d260400d450f07030030700b00d60050420340507a9480001c00c0c0036035a103104101d43c1030b07448030060008a4541500a440303402520040700ca40c0098030220302c2082d814041c0d0910401583c2e00c5403e211080d6032840100d010051410070400c10400424000c250041c0003010801100704405969501e003102d52011280000c00303003018407000712481c03e6075098820607117 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 540976088 1250 540974838 540974843
    0xb01090507081f060f03060b0316030b030f06010e040c09020304060e12070803062e0203180409030c1203020d02131403060702060103080918160207051906180909150522 74
    0x5c01300c5030100c5040e001800542c00690417001c0c04800c002083c10808010701072040306540600c122205070050550f54100e5a080445070b810020051000b1440030f40c00756407260103980c2c0300e0341280da40c0191100300d900544096541980310030381002402c0c4204a00b00403041c00c41555841c1210365100d128550101401d9540f2429210704506074100c030b00800c18100d0701c898a03500b0810404004042d50342d9000c0c0b6100b00110320111060f200702d103864854900d81c950903803583c1c10300100c20751b106a480d1503020441428580e0a1100c05a40034580c0b001c3c1c2000d001000c88412070b9400c1c600351007142041d548034548a540014200310301c081c0c3c0400c8080c1101d510482e03040e19580c0403400603005001c00e103a0408100114802c01c2002038601c2800d00c9140c02036002d8810254964040c0880c40e059001d5a842c3c210b88080f0410010303114000062448060960b450020f50302c070303440e10b81980c81054050700c052124400180e902d003030a101c1e00c1c1d00181e440c036030880880e0006000721030940011002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 540977338 1250 540976088 540976097
    0x120c050a1d10110f0d050315220c200705090610051c0f0c0c060b0a0b09010f050d0606020f0706080610030b042d0f0605030c1c0b01090507081f06 64
    0x141020b03c3c00300050b045209000c019030f40140850030008005820440d00714440c58103075a4001d03000c0c2000e400010b0703101c090007070014041c101c8403074a4026100c5211078a0820085030b038118640c407504980c3e850141c503250007400d9480d2801040002102c1c0c040d0041d40718080f215108120f058200301203071810200b0004699205200350107a000402e80340300101285401c0c100303410704483e070103400540100c4c482ca00400c0490b82a80034001c1064850103038034010107081010000d41d6004005c41101078440d843c10901d0104003071075001c11345030785a00140140c0e20a00140104042c00d01030040581068540380e00240f40c807000050b40172003009030103000e16580302250401500c650304481c1510107803008015043c6a1508003100d411030300000c0c01c0c14185081c6074040301c40c02030701541003103030300c000c00030015060f81404006031400c01c4181d0110751829400d0707000000302134001840c0208215100043ca524001031701501d01c1d50014a0a5070801c100b100f00c46010040355100700070340700036191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 540978588 1250 540977338 540977357
    0x310050f01050c0303270f0706050d0603050709090303051e150409051b04451a041509150e0106121103010606020c010816120c050a1d10 60
    0x41e9803d200d4555070712540d0100000304004800c1129038000c00740080d003d48400d20310740743ca00315120010300540c43c40070b4000480030000e0310b114101070042080849000a5a507641c2c3e61007074584103855001000d601e0b00c9a10000626405200302903021010003ea803012280c41c0d19444d80035080209035030303419409400c2208040e203540d070100036050b50050442c0c0e10b4581940340c0e03411000142c6178075440340e410300d41080503000e00e095010788440007082106d4514111040445010007089800c2e804014964411710089520070740007088281c07800c20110050309107401c00c00611028080010000c500b02501040000d40d0b03080b0765100e07180421000205c05100003040c138050070281c0c0c0901b42c2c2001034450201032240e44141e008440208038001c010b15035540a0598564512507250f901140113030001aa201d44e203c0e641100341c0c10f02e440c2080712030f43c5005109088403051952000055800f09060800d02d40102d4100401c540c003407010b901d50744403100083c62048100b0040400c2000210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 540979838 1250 540978588 540978619
    0x140405010b1b0c0414060a06110c0603041a040b0f060307180504020f041a1306080c06070c09020703051207031b0f09180c1b03020a06020c0c040509030406090b031005 73
    0x200c200780f2098020000d2102a820141e81c0380b5140080d1044e0748940503840c0005411802405050300300180b010281070320409040030040d180c1c10050081e038011980303900d01c02e2a0f501c2060800c3c880c0e80f0030b2400c0c12a90608107240d02c2030010003000e050003036212000c20f1048030720000d009011031a2000010845503210301c04569000303c0058200e400c5810180e000300e80000012081040501c140c8000c2140151b603000c0314103440c1144100c5026070058040e001e03103414500d0040403218062181c0001d0b440d40c1b40120b0341264407611054000a00104141e120b8109820215420007500c0c5814404004031500340c0d6000c50035601082c05004070910301c40310301750181125070010083ca10b07142002c100d220140030081e0000e04006800100c202d0580000c1c0303802c040e03000c100b0640607401001407100680e42d41c002544a43c0b8400c3c401d1094507400e0110f540e070b074010503124129040185403198501030010300a01c29580090b0280c250030310401c40303c0729045040c042101c07002c54072034a8100229 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 540981088 1250 540979838 540979843
    0xd06110705121b0a0b071b0c06030902040b010309030f081905090c0405071d060f0f0a0905120307030c120c050a030201020c0705090112030e040b0a0f140405010b1b 72
    0x3000052090250303a0a038040050550081c1c00003200c401c0d09101d5050032007901945903164642d00400d001600c00104204501c965104401d40d0b017013843c0e07544c0a0613580c07101c0311003d0469100c01c0010b5203465500307085080074091007001c00c00030b08007440030303d8041d80c01421902926582c0000c0043d400e000402d05c80b00500da000240344042401c01260900d03d4206403103180102485005509041c04240ca207072141c01c0c0300e030905000700c4011000b000c0c000b04001c455400305800d1088800c082c02000d0f11158040000e0404501d262030b0340110340e191a080c000025440040d01c081e07908280f01b500e0105c0d81225819816030752204616a40740102d040940783c549000e0b0024006216002c1c030340e003c15070150f0041841c041c007403044450340b507038507420000814000d000351003201c069007800000207070003040e01c20701c42140104003080302036804c404211407040590009401c00802e5a04000348015440d03c524000ba00741c07010310507513040012442280c403c5100899110000c00c04243c0a4030f800e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 540982338 1250 540981088 540981097
    0x2030307030e031b210403020603130f021f03050f061c0204110703051803032115130f06080f0c0d050c060403150f050601020c1002070510030203010f0605090d0611 72
    0x20900c94034000310300340c4d6406681c0e0880c50208015800140000c0001e41c4180b800d0300c080b280e00801d0245140d03500c1d000502c5034416030008461820001c1c80d0000160394100d4414185021801c0440d880100604000c054507000b03812106601240d10a004003030f00c400126516011621110031840031491006c10b0040048001d95024540e002c078900013010351200c010003441801c07556800b800001c0c07004041c0c0704e104005004480140e042443c0e49845c0641807410b52110040441c1083e28651801081100c0032511380e0840c19551f40c807005012a00c0c0788a0b03400035000d0100108074103d18500007503070324046002400c1c455000f11060b403003004000c00100071300c1303480a006283c943d5503a20f011010203410512080344a4180521148128a0707446060710400059004080c0e107070242003409090390719404d10303008602a0040108441e122008080d0b40a1040e40c0c005980750b1503c01001118810742d08203808200e004c20145000d941c44040c4040740c5c540090300001c01c44012405408030b4800e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 540983588 1250 540982338 540982357
    0x80102030c130e070819020c100b18010e0619090c03090c060f0c110f030a0507050a05030a05030a12020c010c08070e180c0f121f090c02030307030e03 66
    0x401c1100384040302014107035140c1c0240c61081101d44030321881c803001c0e40483c0c1c034a0029006800085d450719403100c000140c45501c8000619103200c2e410300600b05640c194548030b0490300c44800325403e0801d1351981e0525004c5112500709941040003907101c03d0405082140305e42d03c8207640301185c40664201000800c80c100d02044901e9030402c024000e8100300209070f45000030a2000140140110703111014089590756040d1594110358680341c03c0030010362040d40000c2113120400c4c40ea1020040d01d240c10f401400288442d91901040001d02c080e1500030501940120107140001400001658030551007030820480783c69415000c0c400901860590003255030928600f203e40540066100303000f80700b55990518814000d606010105807080110590142d810780021030b001808005004c200c0d1600d01014640400003001c03010004041c1d0b4209940707160a01040440070510710304800400e04150180300001d44505c0107501c9010060980003815110720314a0b820a07402e008aa040c40c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 540984838 1250 540983588 540983591
    0x1e12060c05040f060f02070b040e180c060720060a0f050306010e060a120b030111122a030f0601020d17060a030605011e1d220f080703020d0305010305190305040801 72
    0x4e40e44c3d00010160741004100030058001c11101180c03090140048400f5682840d040c04110344035903000000c0c0b10000350600760240a01d001b24203541d600c0390002e1010900458400b6028440083c2c0c0f44208000f000041380300716420010020850b4002e0041907000165050031034990703a4103030040e10301c1c2102000301a801100010599001ca40042801d408480c1344c0784200f01a0304804149400ca03088030030400c803400001e0081050f1020728402c141e178032100d80e80d0b0901803100500c100d4100d9200e03008036130007076043c08030400c48004c4421096581c001c40c00d100030812050000c101030880340d030035a2420854444100014001c0e01e601907040e00666110104110541c1d4444440c2468202048010103c0340c41d541d00198080b03c6a00440b6141780c100400003080e16146280040c0e03e080c51102154a10013651400c04628440414150280030341c17412961403240d442c0007400c3c060518102c005061a29006101184002900f402c900a503036200060b404542e00701175071325005640c032108403503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 540986088 1250 540984838 540984869
    0x1f060f0528030204090f0b0603071410170108011409010618050c070f0302011a03070b1b0a050d02071505031b03220507031406040809060901090315061e12060c0504 72
    0x108660f0b00e0000601075114054240c03500c0042640703e00751489043c55080107808020440d1411445030b16100c1ccd07950034512090701c61200407488110f0300343d00600300c07079640da514040800710305892140d00c4030004008016060610741c100403010400d4440d070141d1350740d070800502c2100c1440704640b07040707800c1010f01861510901c0c00a010308540c00c0d904841c24000b600c0c0c00e00301c2c00d000a51a06540070394840b90705204031102081e11311003401c2d071020321610800c200400400c0060102d81c940003087e502400c2607a083c00c0c4401c00b000e41ea981000d007009010000c00c50b00440121609908850955540d0b58130349920002c0007054a00d41c00410441140da100c100811100103090812207100320000559100b42e500d620780c598004403400f50503014104a000150b203801001400c2c81da0050401c000c049440e500c1301e0b144003504941001c50107684103018045090070305540e48040200c01190750005007001039a620700440300301c00420b1703d615001407000303060044060b40c01811500c1d128103000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 540987338 1250 540986088 540986093
    0x11120114030f0f030f13231002010b0d02040203040303060e010603050f0c07082209111215010801300302010b01020601050f060f07210917011a0907111f060f052803020409 75
    0xc92142c448420711480360318000c0b10143e4018083e044580100804c1ccd258070030345680921001e0760004008804040c0d4031940410104c0d2100c65a5002c0e1007260350000f510303d00000001d520000103400d14100740300a000104c00120007608032004c005110048840e0303080603c4207000e00d00c40d41e800001d02181092046802d48500e4000b07402d201e01c5010b43e10b01292500d071400e2000612407400305000070780750303401400b0310380c6000c1d2020502e107518545d40c00034080b5041400d10f03010009004500507511400010040e6134108441c83c00340000b101c458070940241c9001039028401e0801070508000041500c4051000205c03408242c00406d4014084010031900010300686240c0540342041c100c015904003410414850a20014447c0c0c548202c008400310400c0398100d001820901049044500d594654406001b5080c44514058881545900c4c40c1450810f4841d960813106c100f400d1810104400d0f0b5500342d02c5943e48140075080c1c002010380f400400321120315600040e400500f0301210340c08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 540988588 1250 540987338 540987389
    0xa0515040f0f051c110c090114210d090305160510030f0e030a170f1306090836041103071b170301090f0504050703030311120114030f0f030f13 63
    0x8507a005010340306c0c800510400c1118036402030040030521a003510301000c4a080c840034100c00c400351040c1d0480b2107501600880d2038034403102c2c0c000f8005100c103801007003048820428108180f600820a0003003e003003e011410305045084032004054032004481c46948041e0320003070302a0070b503600762035a0700c900724070140c12a5000c2c84176100034024580000c0202030402c24143c0121400302c01007905200c680c49020103000090006d03104440b04000310418080320104840709605442c446a0ba00c1071941c082610051892110300c0c000e5090124039400d4810ba481101e5000c1410b007070101d4604e09000c543d95440551442c01015050307511022080c0b0000c45010718121501e60740b00340a0441140c03d82e03000d4840589000302076910001082c00000e000e50005115072200e0407400707040641007040c0c05030300c04c02a8030640e450b03803000c0c0d00113a140c1018043c07182c0441610700209600310725001d9a0303030f4900c42c1143c1c90a482c072000c90031100200310302407810000c00e5070b036150600b440c0e522002c024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 540989838 1250 540988588 540988607
    0x8070e100806011503110405090a0c030e010b130c0c02030d0221070f032d0507020907081e06010207170f16080318040b060c0a0515040f0f051c 63
    0x4900410200005180300c0004045043e2100300320404d84c840c10780001030340544800049040715032401e00021886859240d8401d1141010b01c502003070300008a03801a0480c0c99680c01c000141e414258029407584038150109030130140c00800082c01c0740065070444000032030035002945070207544c60010000c0d50001c3c01c402201c0150315066040c00034403409002910a001c0001c10604a1a01d1200401d0090010390f41e230700c0031810504a07052650110803810741c0c0102d840c0c00440c6001c611030013907040414405030b2140880c242001a4201407004d1220300c000c0d443d0302c200522141c80001c0c1c0c0c030b903c02d20805008001010301c500c0103440b40e0400d181c6485540c5801840c51040c00c68045400b580d1240640845000c0d102451822125030351007900f0b6400542aa5041510b821048025840b828001c08918000c040544480003084c50b20700d0500c10392441c1c030b26142e200c0c1d40900002c203a411000284083e405060400d0070007a600d4454203195098a003000380c029820514510b00d50400c0118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 540991088 1250 540989838 540989851
    0x1009080d150e0c2a0304180b0906060a11060a05090c0d030509040b0d05070602010c1103030403021b01020c030105280e0705040c0c0506071d010c150203070908070e 72
    0x10300089541081840d4265103500ca10200b1080002c0400c0120000800030140075407020003060310401c00c21a8104107242948480f613459000180c01c00024140c50452803240340f89600501c14603a05400145106030003400706441581c00082e9501079070700541c3c41c40c80c1c0030081d005540d20f528040310020004d0100329131f44081e502640056030260b01e00003811760503241d45501c13014182603801080c0320040818145203a0480c0803245510007149041111100910140e40003180021104200429170004043d650349564014400c0c800000d402040348250385801c51198813004078080c004070700e072448800b0b406406510301070920001010419011612002c183c00300f203c103032680303586c5400310784191900c3e000c0c94225000c213100c01c0c40d05402ca01c160b001c046c030707000c3c0c01101103440e400d042044c103464132004944116103118020f180d01c80c241c0781c030f54024200500c0c55070745a00c45d0908a960709064148003540080000c2c1c1721409205101d000c0c2c0105403c88d84441d44a01c00d1900c0c100094482 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 540992338 1250 540991088 540991091
    0x2031303050a060e0609100509030706023108030d090c05122506020a020d0317161407020f120723030c030109030210020310090f0b04290f031009080d 66
    0x1d641000b40c00103031709402040864001c1090404420f1041d0050401504200007800100710040c0803400e14005011190440c81040c100c1094011984855180c4103000003481c10f20041c0c2004030400200981d016080d07510400308046a039071a00e458014200c2d00142c1e400752040542ca000c0c1c04000945a5078203001c00507040074040c8590580341021907510504006030b01000b5280b0050404c1c011420501b8440c2c14500415040c0c00310f501240881161185035000c298801c0b00030042e407040c190380242c0d0000904610b0120070344c001c00c152100704480039018100105046401c803104100c0e03d0010200a1554007211440c5014081c1401c030b00b1030901e00c80d01c540c2d12291041d14040c0b10300e00074654560010081d03180100003440103908002e001c190003a801d04800510300e24280039000314030029010003e20349a8003001c100444902e0144001c104901440806480c0000140340009000c111403000d15810900b0000c1c0c541291150340521160419001c0380030060240040c01225081007030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 540993588 1250 540992338 540992351
    0x40b0f1b0a021915210e0a120311121b0d060501090b091c0f0209070f030f0608031b031e040f08032107110a03090f050402031003060c02031303050a06 66
    0x141c00e0140c0f04940107098001660b034004020f41d81c019000d103890029400c034000b101088842c104811914031400f5528543c0100301601c0c204152100e01c0e8545100d00d00702004070b0f00040070101050b0041c0400120140300c03580100307144200c07900d503038041c2c0e058400c90300c0c1c0c3c1d40f051600c916018180b00c0c401c180c04680306a2004c2250b108070300903a0760b842005003080c1c032a028030180d6801c0c0043c1210050707404159860034030f009a11810044e501c1080d11382c41d02030b8503240703d42c4010110344000c0b1811071000d141c40014041920040121044a0f2098041000d01b24039101c0c858254804c861460300a0703074514440f0640056000c2c0a44110341c1403201004d121542c81050380c2d00c07881103070b60089084110b8081c5031100189980c20310b41144080c5010340705010001c20380d0789404103861007a00407a4844400300300401501d511200685400c0c0e4086d800d50a00000c070110100e0240002000f40d034841825102c20fa01c2001a284800a4100c45502550396800c0107500c50420000954102c0d04001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 540994838 1250 540993588 540993619
    0x6240303040302030307060b130501060c020f180402150c190c0e07090612110d090615050a090f0e060403030b1302160b06030c030a05030c0c010804020105040b0f1b0a02 74
    0x100703440c1140d802801070f42c50041a0b50f1504000c02c03080840d142c0c0404044c890b400e06000511505000e0320050311a80c1e9130011074010410500c1c3c030081c100348694455804445030408248000d41c00c140d040d50700d1155070b8a40344101d207a6000b004e40a4107584504208850310000c0603208407941c1c0c3c040c60a10103105d03120180a04480c100300c859002040c60040c0412007a44241072440a00b41d0340035000491141c0e0158491803a405004001c910030b445080d1001802001d100d4900502040100382c80d05d0385c83c1501080c013409a610400078965a110300c1a040440240c2050340d400342440251201d40c035103440c008d0001e21250381e00900601d036a000c10005044644211501c00c0725100103519405559602c078220b8800c002e01158241c000c02d83d9040c20f548040002d024814440c50156031140c0199460300d103407800c0c07203030840c0c10014501306200243c1d030403d00311821755031843c032400e9403540201f0310003010380708608400c91056955011340704090800309145a1081c42140e00081200740076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 540996088 1250 540994838 540994843
    0x180f020d02012015011d07050901140d0902010311190503041e03050301030303060b04121202072303010b180c0a020c06210619050402070204060504061e062a1103062403 74
    0x81650741b401d0003a280c042201140994040c0090701d10501d8806032100e200c02c0080388a40201e500803c1c4140c54480c260219a0503000d000c1041c0c146c50015402d2030814000758004281504080c401e0010000200741800034102082d010040c00c80c1d00e143c246070303080c500144254000d00c0140c0010389840350204610048100300c8080310050556001c44540584503003c13040d4940c141c060540c803c041700015104000b0003a100480036040040078203554000515083d51512004a48515903000707580010000c0c001195400650075500f107030311819511016072500d03007021103081d0f00c060045042c2c09030740e810070388218102e680281c203150039413211002d100c00c0024a62504141c141441008d000070300b410307806410302a00040011a0b2070743e030764010a00300e510340d0b0407515440e8000610b4070300010b01e5904403001032902c0c2c039003d00318590307600180054502c000055003034205040c034001d0520081e03403880811795400a06594442c00c5c916100d2254840c0c441040f0300d103490f800521115031601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 540997338 1250 540996088 540996119
    0x51905090306160c0b150109050307031a04150e0303160c12080a0209060d0c080c07030c021507080c06010e070f20070305030706050109180f020d0201201501 69
    0x14000301100e03141c40b2140748450141200300010000102c04c840e010500c04403049000384c00080102c1e6100d444140010010a01e40d00402d0080d400030b04100700194010f80401c90025000c0d1901415031a585001e1200703198162400800e0b500b0620004d2120002000440c014020600c0203110040e2202c41962a40a02840913010b0a80c0140d4900f225004030907403503000c145210014a05181c40380041c2d800d4010740200c0000607952103440002540004800d50007250b9400c020b400c04440b81d82c01404070001c84030080c05102280126025845044142c82c5e00c0740c1d0061b0000d4680894025440ea01d400c24443d1910006020b000b00d80810300464503410a02c81030703070b0b035a8000710444e0140541c1c180796107141e100c035129140001001c100c0900280c148544a12004a0f69514060b048410b59909401007041c1500146411000498540305691324640c1540c050390380c0b00ea103000588480c4a100c8440401142c2d42e9100341660f0004140390000368440640e505190340c0341c0144c1c2c5000c4c0b81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 540998588 1250 540997338 540997357
    0x71a120f09061f0f0303020f011a0904081806041221020c060325080403020d0f0c030c0201020c060412151401030b130c09020c011b0503010620060106051905 69
    0x45100428842e001050b543d0403802800701c894840144e07180c04a1445583c140d10070b400581100b5141411410207008905071040001c0410300101c0d0584000741480310060801001d00a000501c0d040100c00d071074590900c41310040c802c0c0d0b00c4643c0c904080700c0000c6e0904003280c15442c601380d445031069064040340c40440c0e142c0c1c024240c04480305d040c0702c1c40c4e6002030000907d10021485801c040b2000c0c0d002d500941e111075442c0c01d1135082500c4c020740340075412910101400209001c0c40403080c0e12042044660f41c240c40c02400c0c03000d41d070006038103112480d162290803640c005030103d03c1c2e407250382e01d40c12002c1c4906d04008072040c03000350b204101ca51412014000d000340c2c900420120314101d03a219001802800c038101041120341d9a04803101c03ca40c005c1400c10b03000303d0410b00c0040280705540150340d55107108400b041540700006e01a1005008040070b206054044040903840c2c0503500765001041c1c000c803000f81d40c5515026113260400390b13050381e007502001c50030722030720f48104140c801484 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 540999838 1250 540998588 540998593
    0xe03100501152a03030902091006050a0f030213080c030d0e060304060c0504080307031701060206131b080a0b041b03050a0308060609060d0b130606050f090102071a120f09 75
    0x440507004960081c0d543c1e0204640300701c440030340c3c02d640d00d403598181000c912a1314000366841c2d00e44148002084000c01010400140f170504001958110044030740756030241c504203280000c242d0059000340148d0301c14480c90307900d0010101c0d0b5202c0002c4d02c0908007504504440c0d001d0170405003151030f1208100d00980051040c07010800154142d08400c0b940d00c0da03401c1040c149900c0310318151079500900710540019540490f00882016a0700c15580034000034806400075141c455000122045030620080001c10340c45690126515900d04071409031041609458440800342440002a901542c1c207803150940c07004000b070b0f5400940080e4081326480005005515400c0d241542d0300c0d000100203a0b0020410401aa41e41e07a84100410b255030700102c1c002070100c01300341480406c40700c155010109502d40001400456000340c152000150071081d8195140b082100407400c3c41c074568491054601c0c031040006d0800004c5001e40080e03810720340c0b070940315034480340c02001030303802911107502380d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 541001088 1250 540999838 540999869
    0x6080115050d0533011401080f0403030b0a030f0c060801030302120a0e041112010503030901050915070c0e0118020909040609030c0c1d060d020f0d0c03050d0e03100501 74
    0x42c28442c2045081a003c0d0040e1150169a00b080e0034038881010140d0700303003044ca4446a81c10021002c0c107a0b01400d07000c0440000c4040480000e00132900c003814040007898504000340826100360001049090090800742103580e81e841c2502c400d0f141010200c60b500142070000c40c290f03100c0d80049040300d4040e4010700301140250003141da0350348204521020800185250031701611a4060703400d802346d424807078542d40c90501b12440e1202c030040e00001d10a8204201c0c0a40030780c0c0c844240e801181044401c1751070f15444211441c141c1c4a58000200780c003103c044002070441018032454122140c5201e480520618441807000301d03c914885c103544025030300701040c045030095101c06003a522909183c3e491403140d8464213440b8503181e0100002c0f500c9190288298a81420802d8000c1300c00d603200c0c03a4080303403580000c42d8a0074510302c0a0203070401c8400f03001800181c1170603100648d009015151404a00c1100a00d2400c21182c41d500070b10030540d4010740c0d02d0084c8600c0e8100c409488100040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 541002338 1250 541001088 541001099
    0x21807170a060801020403140c030d1d030a21020f031c05090c12010506030c1801270207230a1101030c020a020909010f0b0603090c010315230406080115 67
    0x106003014018003010307a91a6030200b42c6074001d01c000c101440c00b0303941003d02c03c01d050b5040c0c2d141c070100e40c003418066003203139040c0105990040d4940300070f00007429498019228003400f2914200600c0c20203000021141c0207201003801e072444070604011030380d083d00d507000420b0f59215a60322131081e03103d2500b1504485098000c0c02d5a124036008220103040e40d0640b501940020b402681189a500959650b1f80c01c3c0241c1789410020701a0441c0c040d00d24a804108000502d501c1290521444a07021a8500d2204e0004009407010003900000304045450300b240341040850750286080c0d000f46076003c003c10940092000071030515095200c1c0b038090552210a0044000d043c0010840e0290300c200d0500c07000607914003201510826852000003060000400c086080e1400703103840501800d020024403190001c04508000c140340c084c04d02003040c42e00303000300c4100e0080d16489880800c411a03014840040120a1502c91060441e000e003e00e54036070010078201c50104043c5901103040711410051f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 541003588 1250 541002338 541002377
    0x602060601030b010c140610080f070308131211090105061204060c020f030a0e0301060510050427050106050307030506040204060c02012d020d09061b020607060b0616021807 76
    0x1007400f410301d42542c00d80c2c0f583d5201812402e40d01c8110701a60454820020707291307502c0c07001d200144131120082007107401003081c442c0c6903001c0e8000907082045c00a41c120360441c24600b00e9000303000300d51581c89034405500b0800e5a0818110100c0d11510101c40000b6842c41c000701a20403144419410301c0da0354a85564041c02171181404000540c0622143d014044c041070014140341c00c100d48480040b11844c2041608481c1503070000d610035116882c0340e100c5980d0000946040d1240c00080c803080188401100150791403c00300282c0d0f481c1040004219a9401405980100455142808581c444400f00002da018500401e000a0035040204000d90705c11034001454200c4030302829100d81c98070444c1d00324503018000c50030143c0c3c8000081c480c0d80b0b9120301054010035181c030784403100c121500812880000e24410180c80b070180404e005d01449295804058122001004299110700c4100c482c25032203100c510aa00c00d0314011494415072110311b0100748513a20560b21586e404007450185070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 541004838 1250 541003588 541003601
    0x80105011b1122060e0c031603110f0909151509061b0106050111030f0a1409030d0917070305060f0405240109061706010501030e0f10020409060609060206060103 71
    0x840001101030150300c20703100c4071000003c00f400300241050042c403601c801030548826501100f003502148040240c6402c02c01c003501d070000424514903039404203000c002c8000c1d000110000611010001d82455401942c400900c6040b07015541800a03988144c0c2090980d07100b24001504207625041014807002010300902964000401c8242020300c2c51205049544511580b60003030381d90750320244015038100011207103540360240110310f8540344103200c2c2c4e0396019600010041c0040c40d100300204100c004c00b6901c848002038120380c0c200c80c040c40c00a01c5511544030341103c100030240350903000b1902046c2841980c1d0450010081b940351a008150400b40c02007055615020f400707800080d014004171801b1160052401c054029411f01c00702c042140c2c031552210040400301e00c100001c8401c042076090446509080c0040d5050b8491421400c0181d11410781e4400d0080c1070440720319000643c0688141c034800942000080d450b26000e0361100c000e800b0b58005039200100060301036110340c0182 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 541006088 1250 541004838 541004843
    0xc0f010e0102030706050a050603010605030a12030c050c150105010909020703080609040c0e0405010f0b0103060e060d150c1d010c02060304170f210702070f0603050c0408120c010b01080105011b 85
    0x200d04d89411a25003a045038429122886211f458200b80050303403900340990000780c00110042c00d41e1420300da840819040d076100c000c81c20300d512103625654490055080d5080868000165141c00c0040620000021024000c41e404525610008101c02c846d910039119480d038551950a51a00d64004100d9070741002481291103100c1c44602040d00c1d100b5202e02e5014a10650022400300d10343d0341020251480d804009041500e01002040411148141c05170044419200c13540d10000905080c04400001005048841c1c00d060045d4805540038038941b0303a40c0d0303032425180070a044000c011242001c2882000e903026200b0300202e40810b1905d020911031703081080f0b610341380c0618604400301c01e03044104050400301c6400d03482c1e190b000d0303003150007a070248240c40a08061030404192114446060107500c081650b41c10000780c42030945021034000c4c081036005c403100b502c8002c40707200c403503404660650003e50174002100703074550140d070125040e0344058641c0c1c4a120709000c12148403e078181d105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 541007194 1106 541006088 541006093
    0xd0206010e010b2b110318070b0c0d0f0c0c03061a0a0609090209040213030b04200a0303050d15031416080d0c1b15030c020c0f010e0102 60
    0x904540704102034050106007024200013000b8200e85004d0114034000205003c0032200c01030b074600c40120700c4030803038482d540c8884c01024140203401c121030a552040a6030b00c8414040d920900030180075280000c1d0aa900351540003445606070f01c180e4005a441d40d410441e580d841d03262907010070050700d041048602c0d042d4000d05840d090300c5200001e40d804218203190b035480d5012190010340c83c2c211903020036104d003083c800f2044243e84c01c41e80c1e8000100c0c2d414049d1a80400b2039242200104010320b9140703107840a54444e80907903101c41081da55051100219044030740d2030005180102c2c00651006010054146803a6140402c80070610342c0c00700400007545c0024420701400751a140c0040c0c1d00d0003900e0104020250f05c4e07213802581148100104030b0800103035100c0007000c0140e070309021742c07015080141c0e01c80000b13020454010802d0940f43c09194000c3c62003021083c4180304 = true := by decide +kernel

theorem cover : BRFrame.Cov 540827338 541007194 := by
  have h0 := BRFrame.cov_init 540827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 540827338 ≤ n) (h2 : n < 541007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
