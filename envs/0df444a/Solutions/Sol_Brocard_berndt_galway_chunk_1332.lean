-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1332
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:25:23.275965+00:00
-- url     : https://prove2.me/submissions/965f6779-8c3a-46a3-9121-78affe9ff991

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 239388489 ≤ n < 239568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 239389739 1250 239388489 239388491
    0xf130c0b180d030908100213050913060203070507030e0103020c210c0307080306040e0604050319090e090709060801060e06150403052406010c080315013006061106040b041109040303 80
    0x130a2200d02c40c00e1021090081d144c6008600d0b0545803403640e5015190742c4a480e00c1200c1c500d00140d000319909080c1003c055002c04115900e1925690107041ca8100201c10350004441407240740c030550092003240d000305040e1004004038018541d01d2061184040c0007805803110a000000c8015401c0010f0102c00740302d1490310b03403a403a00401344400c44a240d0418150313580300d102804003007507002c4200e4803844801d03c00c101c4404120f000507940110307681c1c000b0604400c81403c1100702540401c0000030ba40e0101024032820f41d850751f049090b5a0b0074013038241840740d07003004500507290004805200e504c0c07001e52603080c00d81e644c4906042c610f040d5400304058130801c400808080081e00e07501e40c0040b0909001c4000f02d00c43e01e0b19411f40c00020581c55503200c04030003155080e802042c10640408120280803100350710440d003140041500c141c41903115003420008a4400c0c09031a000c12141d000d100140010395468541480d02c600141080d55110780ca0043d864140d2100c040c0740d8891030003610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 239390989 1250 239389739 239389757
    0xb060d050a050c04120f02011803050a1b080c0409210815030303070e01050d06170706020f0d021213030b01090b030606010c08030112050309030601030b0f130c0b180d03 74
    0x100d000c160b0b64000c01c03030411030b10100020311841201801c0d070300c407843c0c00042c076200317598041c401610104401c413455030b09010049000010024005401000c0701d2189240c003001001c60b03210015000d4040c011341c003030350b00251410b07500790400307900c407850b002c7c0030b03c8008000d078008400043c04c0701c640203410780000c0d410104200c00d103140d803510000401f030140c0040d80755240801c8001c1810984002c02410404001407040c50b455940d00890058084018500441e48031070000e55990394840c800e04000d4081e0018220140201003058034041e0256000742003202d4403c5800c007641d42c4184c196140014071a200840841c0c040341069000e0706215100280300d8181c00c040600d403803030080c000342c1044658000c180005200384152411a044910301030301000c0745160a5056005011985415101d001c0000050017941881c4c20f004007241c40e20341e03106403a8001c2d80040000c41d480050583c604c4c40008220041a400040446103a40110075003200b40c503400107005030851003c182c2c00200008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 239392239 1250 239390989 239391001
    0x9021303140c09040b19050c27030a03270834090f060b0c0601060e0d05032203060c09030501050705090a120212070608011e0602100c030b060d05 64
    0x4603104601c02100401040200403110016841d0900280000c08407035046001c5102400c0c80740d8092000104403001348800d00c2c0c15114000260000c003506100c50342103a421424412108003417403010240500030f452007481c29207068070350000782d102c042c103280e0309000701515503c41100040080d1580b0006000c01c1c004010810340c00800000c3c030714a060704403411004100b1010400d0304121060b204003c146d0030b14508001000b89041c0e40400050400041c04982384000812401d050300c42c0b1740c0320480381d10b507180180a403525240b40002c04c2944100041050081c0b00186ea4030300c034200d901701190b915169954803080d50f14070b800080c040345200c182403080100030301617581d00c00020310f419810f00700c80c1c0c4002800741005101d4007050380e114140700c2065407220000c030381e03050100c801226040341d0b84900042c0b88144c00d00c18040e12410f206600d00080f202c1e40043c030100c500c6580104001e14142c4000300040000300c8100c41815a1205c0c500525101c24000e404041241013002482c1c2c5028 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 239393489 1250 239392239 239392253
    0x170a020d1b06030204051309030e18010504050c0306010203031906030f05010504110f03070308030604020d0e0d090602120306121e0313050a0305030a1404080a0b010321020d0e010909021303 83
    0x1a03001001414014170060016881d4010030544094010002154800b201d04059451440c0c45200c240c100a18203222502c0341030442515040b25000e0354200503c0d0b9480041030f900c2c1c001962500d005800400c04654011022075604050302c3c286100040c1c0a50740eaaa1410034a460801c05c452994680b41040240000705410580c610400e5551300030011421001030380303031112800b0052009501201044881e107032941aa2002c40c0001c60800510b0040910244c0e42c1d50316000c0200021702e09000032601c180b010910740d405914401000d41103031200310400802c00200d0740740c0d4a1b28842c0304041d00c12104101501e50250391808069680c49038008065500d00c2401d400103070048506000410009000004943c00301446180c01c00315801464400d61162040f030340580024411812182e00380003c4803030300da04a078401c100c4044600c0b048a410418000c00300301d107038090307000071100603260340c010455841c140340142b40c0820059103810070003089811408520b00c40050a010a004000e41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 239394739 1250 239393489 239393543
    0x90b01031404020102100e0312010308070b130309030204050421081e13030305071214071d0906010e0d0b0906060306100f0603021303050609010506190503030301170a020d 75
    0x70074030800301c980340980020303540d40c40044c2804400d90f40c0320650425481e080c000d50b00c0d12105e0409000980d40e40341401c41017034008490999509030f400000c00d00358284030f001190140c0d8962600518540b65801300300080c107004006580440c0e004126813042210407034244119065921003c0803410b100a08008100071450a0511049200144010f5100005c491400c060341407030041007996440c2800c4500d5510001d15030390250070720402c400d11407100420940305030b00e965120041e9041c41d2441c1c10030b426001207500d410106110100e40554480c6078030380c1d00d2540c0600341200070003003550754a9816404840c5041c2d150040e00900c18240f41c18001140c10a05581c00166103c0c1009240b07448240240300d0751060690000c3c01f101140702645640e002183c01c803080e04e14510f07241c0001c6010704402c41e00c1a200341c01646e01c03006440d40c125404410303110060000c1d03013142e0030002c3c1c6c41007400420000c041144905000307800166602c00980601d144614000399510034030a9a120103004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 239395989 1250 239394739 239394761
    0x30c06020705010210020a0314070801080d05270102011d0109050c09060901090e1002030705090f1210020d02040f230906181e130201020c030304060c0b040c090204090b0103 76
    0x8101c80c2084241c0c0e0000b5040100361a403007005a45100545003640100003100700e44020040803401c010140d40c008040a040703501840a43d2030030030a85000302c40303520800d601900300c05540a601d6070201d0b9806540c2622900c18000091071002140d0120700803902d001400d04241e46800306c0c402002f209000c80144220140d03603a80c814101000080d81d284814014070111554410508481c51420006944c0585d142c2100f1507680c1000140140300d40c1c40440302a0080c1e1400d4801030040c103108001202c2c80c000a80036220f41000018000c1c0a54025480880c010707070244070114099080f1440700300200700e0303200d4a41c5950103400a01c501c0c803100f003180510a0100f0700412106803540c0b16410741d84c0c42c0c1800000100c0d0b40f5411940b080300507008141924034442c108021411523050020700078203000340c00b00e070a031510003030405503079100d98000c440025102d110794500040494882c2d640007441032200e10460741c2ca4203412401c981103a400301542a460b960a0348031560544941d0040f85 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 239397239 1250 239395989 239395993
    0x3070c08010605060412050a080d050103060c210c120f02090306070813030503040204140103031d09040804120c0b030a05060406081b12030723010c05250303020f070c030c0602 77
    0x1460800051a030340290b10030034060070b1544070706e401003004c01d104103001503500009058a07141e1542041c00206130900003240d1891500c10040c10450151120201450050b035041c1281d0100b01c05a0002d08202075001041c001c00e20464424205540104015003124100043c0c4076164401014a440000b801c49024000b90742c1c20302a4502801002440d03140e00341c2841552601c0d80d1022600400b2280b0300382020009200000c400c0540c807500342042c41208481810ba183e00e40420810a00b030184d40007410f80d00204000c00601034400b00d400302c0b96004a11200e1529030b45e00c0c01c0d00702d5520407a107030568290f507241080054a800c4c4142000340401400904a1404440081519160390180030340725071403a503400400c0c07480800c00c132030309907901515030b00181444411614036020365000280c8203508110305444100e1183c4242d4008120094044a942c280c2e190281103040388000140e04140e000c100013400801c00304000d08109104200344c1c26024614140318003010401d4020b60115 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 239398489 1250 239397239 239397251
    0x7200303190507051306050a050409090b01092301031205072003010501090212060f1903050a060b030a1205070201052503020d1e0503060604030204060b0705190209011517010803070c0801 82
    0x2e49601705c441000d403111803c05998840f4059010366581c000d55103e8440f443c108603d8004100100c0c038010304841c1241000e00000700107440210603c250036034800ba203018583c00420208244054080c1d11010600700203140c0030301911001c46600c1220003144401040c0b11841429040911400b0300500e003102046003820407040c2c00c07803950080a8149417055000240402060741d0341c2e00117031198601c2c0f080c142c10041c1c0da803405d0741d2501c8480710241c41d981c2c9045101c1c0c50305c2c1000702d034851545078040d01130340581414031000e49054000180990410405000301030110070b0103103c03810005a658000140d81c4910320b0000c0c1b0b030050941080c0b0070002901400f035403c410200e8903642680060420039200d641ea4000b007549401154030183d4442e081643c00244c2d42072550091018500038001e5800d0300002044501c0008401040250008a5400100880c88070901d60b02c850710140c5c0340c103084050000a420418050a80150100b90400100c2a040040194400c1c0003008140024404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 239399739 1250 239398489 239398507
    0x309160b0d0b030c041802090c0301050616141501140d030e130209061914120103030f030f05151e0312090a03080a0c0c0e0603060720030319050705 65
    0x105004040c0d00079201d50b203481d40b101441d501840040c3c8040302c041c10030030226051401411100c46100401d900030700c00200840d11550000c0200da05036503014046500d0603c0e00e50011070039454510054034000481e040c081d15a007030a01c440c80e50344d445100300c0301c0d065040c079407004940400740f10500c2c0b0400706860130500090b00401d401d004010200d41682641d040c0041c1e00c40680b080082d01540140c0000b18650b40c03c0411031810314518490f542c002e441c9440c0c07205441e15102c1c1c0140c1001c1803107901e00400001e0302c80d422014007591203140200d640f0107402600ca0030f541003514442e0314003a0100c100c080b80c0c141102500e0241c1302d609000c80300d42c5410804282c40700705220302c0340e1200304005501d1200da1500407002004551105620b9035602c04900024641100c40380d0884140d85810b43c00111090180c14140c05164001d020f00310301d80f03a404040c1d89150100da0b42804500c01c1d40c40d00241d508040c40030394401c00c0d2011081d0108094003080c2021203000a2180701805003d0000704a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 239400989 1250 239399739 239399759
    0x230109091b0305060a0b0f19091206020f0405060304060b03010c0302120c030604110c030408150705270a0801140f0c032e080109050c010207061b140303070203030916 73
    0xc10034010781000941130302c030702010421000007070b009044010300005034002500c07030841c0100301900038074000c1100d500b0a6641200e200c01e86126a0800320040762011012500f00e600404c40804103500882c5055a0b400224103d174004860540f800c0399101c1c0e40d08020300b401e000c0d14a2241d43d034a401c500d40411036080300701404003d0901c400f5070f88003100203031254466034803200014405c4514180c958813941c40c4207540398000e0246600314010f000584042d0320300003030480d01a904e40d495103400c0404580c002050302c158440700039103000030003115a04503204c055034500900341031400030a0a00a41480740304603e80541005200c7e010f00c400c0160851941d02580c0d000540e01e1007a1405441480d26249a43d800a101c103c0400c10500005070801c01540304011691080065582d6104004010380c5c0b9a0150300c02d040c041880350701029807104200c0740c50b039201d0748a440e034034180081d0842801d142d9003085400b0f50160740004240032100c20104000854410f5000054150b5070170804100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 239402239 1250 239400989 239401031
    0x2215090203060a0902090402070804230103061d07030609060605130f031211030c01050c041d0f0117030c1e0f061501030902120d0302180114070b04080423010909 71
    0x640c1301c07a4003285d4034240e90750726011114070070f800caa000350f02da40d128407070b10090803083c503108125103444101649041d40640152022078445c1d00039107180b4406118100d411107002480b12040641d02c11020800348000c0c0315007000f400c0d00ea40d68035200d64085145407001c020642201c0c2e45103108903410000103020a14900e2981807501e403c2000c0d0a0b50384019185020300c1c3c070844069401d10301044089210240030f407040300d1125000d502600c25000c0d1607607130741c2426108002030010503001407041034401e094080a142e80b1358102ca02d441d06400d000c609045440d080a40302c00e101d440c4242e102901003190300d2250003414094100c506020400300600003404510a05040c1c0340c03d0414103544c2d8502d0410114000b00094600701c0801180090003980200c40c046d0000806c0030030710f205544180078015144005048051074021540c540300c981010042c0102c03410001084045102e88111380803020505105c002610120079000003d04042c040746c100300d02c060f203009080c10550303d0341c1040c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 239403489 1250 239402239 239402249
    0x7080108010b060c12160f080306090a020903120307050403061e0b010206070e0112020702040f05070906020a151a032505040b091f080a1401060501020c03070605092215090203060a 79
    0x2555281180c61b01603007001005006015021440700c4034090000140045100307820880c0c021805070340320b1001d18124025150002d4156000c1c01d610000c0c0710210000315086401424190b0806903207a5036a8240c48403d13000302d00c001c1c46005003408005181c000c01c0203901003400a0b2520303240c29030000300304d0004003119070304100500ca15a80065410390480d906160050020f0101c0c0c585403030000042d0100707503400300005881080c0061390500c08200100c801c0e03404034070546a842070664000240001d4008202186109107a001c0e59a40130800c5070440201007580694030400018003040808a07548018060b90074040c10100b15640c0c019869400880070903000c01d004880c0c0b20080ba840c80c0341d000303c040c0d403042c0c07182c2c2130038800b11074031032030001003880000c0c08080d458000484e01e400c2040c40d620f07055441800c00340039044c0244041c1c1090040681001004030955140f012013016000b1203000160742d030740c40c2c5c2c1d210305440b034440310203061600410340ca54102900446d02e1030701d070ba00c12 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 239404739 1250 239403489 239403523
    0x10c050307030f06090c020c010809120414060d23150607080d0902031b0301051003050c060c0a0203030d1409070308040b090409080c0c10031806090311010507080108010b060c 77
    0x2031030349400d0030b13480000034200703002c0704102a142e0804040e5840d01744048043c08035004070300041020800044078188081820300c5c0301d04003840c1180e00303010f4416940e540c41d48a203003403240c140300d22701c0c1d446101110145804054503000e0014020462804083d0a0081c4061103250b10390042e240c840407900101d0744020a00d0b6101c481043e544014014004c00940c54003e445d1040c0c010b0513030b4a980044501e0440081102d902e540e00c4407545082240310003047c80d0400140b43c20245804006009548408420b030f403445181c0b0780c0020b01316800b4401d0210f065039240404000d01945401c0745038408524002000050b0854076509014010384c42001c003d40c00001d09041503488a4012401e4035070310040d41912117420b603014940711140c443c1290300440c031203403c1c940100d209000c0d134164103060303004001e48000c0030345520000c3c0c61120b800750144604c0418200c1c03001d00c00d00c00d29102c0c00560781e07019015410945c405080d01c011071070b41885440184004100c004011540c0340244c080e03450 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 239405989 1250 239404739 239404751
    0x1502030a021c11070e10090216060902030a050a060c0912030905060309070812071406040b04020f041e061a0f1b0c0a06080109050f13020111100c03060314010c05030703 74
    0x80c121907402c000d1a40c10224084c0e25800035800f24400f110038002c4407040300c40c5070440d8030380040300c049008927194800c0c1c0080c1c1c2c1c42d90380c01150040e40040c84250000d801d4400020907600c4113481c080445d0700884d8a40c0c2d07108400c551895100000c0805043e552209a40c140326503100100030300300e00d000307040c07013060300001140a8503000c0000b1340c0104015015180b5804014640d81500e410200e006d8802e4009080c45442d19540442c0e030030310665002181300394940301e42d020310407103003c5905800d030015030301d80721080c800380c102e000d000e004440041c1c0401e01d0b5040c05505419a151002607250140090180f02801d016041c00e482c0c94140103200140b501903490042c1d444c1c004101016a080080c41901140ea540d0002c15241602c0d408081888070387c4074180f801c854840300701c82440800c8000ea60303c40c011741c4501d0080100d6041902118507600c224032190084400141e09a00820350f11401001003202d000c0c0c104007030642d20350080125030707a07107607028040380702c02055003003051380e118 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 239407239 1250 239405989 239406043
    0x7061508010603050f120a080a0c090902030c09181303180509090a060e030a0c02010315091b090e0402030307030f0c17030108161a0d0e010906061502030a02 69
    0x14800002410310100038020a0390301e040440c0c13a400b0746408520341d40a100c459001c0d02c0e5044044507005515a0741d82c10056403059140070013020040e540004000040070001040201130029501aa00a100e580e03034859560f030421842c0e412616142481b14900c9040181c01d490203032011540c1501407c140380212081c804081c03804025400466010030544280408000c000a08140c06031050b141003000c05600b0a0156a074001c43d114000090500c01010005522a801a007524801d802622903210f0700c616941003036600f143c03620f140c8001ca18440541c082c1c0c0c84050341c0700a01c910f21f5602182c2c1071503004641c481c8501c00000d07050054032080700b0125441542c0c4115482d4102c083c0e91703a0404070404140142c0d10a120702c80f4288541c0442003640340340703070301c51400700e0302007142d15010031900150f08901504040d0070144115600c00801a02440a011391084580b0070200043e82e40e0600020303280301c1022103c0f4130304650042c8204a98113400148648945d00b480040005070507002c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 239408489 1250 239407239 239407271
    0x105060f0909070c022803140102090d050c01021612020609011704050a111804030806030a05070f0305070617071d190f090207031b03020f070602060a0b0d05030706 72
    0x40c0540d582005402e010800d0706940510020f44c024400c4078007003034a05e00c00b4098441c001111685100380d0444c1007003040000c2c00c05070a448148541c00001d030034120403100050260540c400152055000900104490b681c10f004020115100d10703036014013603003800044c4100302070901001740540384c00941030303090741c1c05110700502e04c1010003072100c03651a042ca031968489a511004590701c4072040100c488920b0b103000d0200016036079943d011341c2ca554580b011600003501030b00b440d03098046d00c4501c0c800b20b107041c448000540032802c140451030340b56281103440d1031055440b11041242d5401750a6248141280c03164020500d4640300080500f0803011009a80400641c1640080910a80100c03104071440200450301c1101c00d5440706966181414203038807a9000040028010307440c031a132889a24004801034a00030f2040301c40e942d0f001d007640c501c2c2c42000d070400c4015900100801034050114001c41c1c0c1e548105541d8045048100d650311030f40d0b03020314000240700a8071000c0e400030351046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 239409739 1250 239408489 239408497
    0x1404140303041211150a08040605041e0c0f05012c0315010320030118020111071707080105061806091302100906030b03010911130609060905090c03150105060f 70
    0x72241e1216041d0707180b403a00146611a6048040c041c0d1452040400d0180d0305c0c0e020b40e01400b4498841c40c655940d90741c0d808000300001002102c43c0103070001c2d05c5410886c2d10040c1c9600c0340c402c4541e07050181c200090012000070b03d50104c0e04000c411101901c18000c1000d169507000d07050b800b00810301c102e200c00039081006907829194524690000002031090f1a040c0a420100c050b2070b25004040324400d040c240ea1520807440304900c59003c082e40154030646510940384509000d071162103455589190900000409005099020417000d1010060a00c5401e8002204135002111001c1c400c49007000c0c00c1006024600c110440750004101111580418034000d41c0103001d5400015000e2019041d007a15025040000749000600b086a003014401c034400c81c0e80080700c001403242c11000300320002c07c10410041100c0c1d11030301e00141448030b5000d440098581400046220b00c0c05440d5940743c004408011842544020007020105580c00c09940c1541e40564101e0360711620611202d4442c07003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 239410989 1250 239409739 239409749
    0xf13060e04120f030506150a121d070b04151d0a0b13090b061207120f050105010807020114060f0d0206040914061509040b0d0210020a050d140414030304 67
    0x403212042000300301600e0548142c00c103050300c3d00e00b40034440450482c1118130844000d45c01501da1298140103c07180780180007841c42d03524203803c0e0b11820310720100544070030000646580324940404a120b07203083c0700340c001409060301d61505040c50456610002d10904440200b40112a040b1001c40c6800107103440c0030220242446c0d4030b16544000c4c5003040d60086040200f4035604042c01b0900304440d0281404105006000a04150301d02e01050311090000d802c64080c00f00240c290800c04525014141840c3d45c60301c00010191325150024100d450003c00450469141c04680003502c02e529450541001060340d001801c04070b0310004c11411101a00e0195000ca00442e0010b00c156040d007040560043c0b0070811050741d2108014401d0304051900c0380c0c07040030300910400086080640c40700310441001440d40300c040da0150041030311300701d07003c48100c01a0040d600c0700d41400300070000e5107d54107280c42c1400310705514003034040550107603000c1c0c2c900da48010080110f05d940d0800070340b00940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 239412239 1250 239410989 239411009
    0xa08150d03020a05010b0d030c080c0a15060303030b0105160308090c060c100e0313090c030f050711060f10061413060801030c1a0706020d090c15030509010b0f1306 72
    0x400c950070041c0d52040500310480c1d41d9170030010081d409041808122003c203070716845140208010b55603100503030300001c03050a458803900d04507401150380a00082e45028180c10000b81e410304505008040d0740003160b545050180030005484c84085003203042d10104d800d4075010a8a03101c8000c0c050602103040c3c1c41d40c0c0c0c84540410000300c104004203140340d0081c40702e2010404074130644059920ba004040b198000c00c80c0417001005828a40d0f04aa400304080c2d1500203070448149818104496095502e0303000203002000c900d080c54000c01a440c0c1008500307038162028944602244490480b0303000300f108001c5002d601c00b44020b1100195204031150040c1c080361a511400000c00c1c0e00003d120030355441e03c031503500186030008a000d901e107a8003100b19040c030303003040c070b0311800081d5004008010150b03548031030203404140c1e80b1036003a015040680c101c6c442506c0c4040000c044d508003808080715a4501900740c07020341d41345500001688001d89010040c000c0c00d00340703540145141e9105000c2c2d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 239413489 1250 239412239 239412259
    0x60e01020f0a02010b09010509070807031e0c170f180a0209011d07080c121504050106030501060909060b1801050d0c0207090e0f0601060e040f0204030602040317030c0a0815 76
    0x440030078041e1034a6480d507402008003550000800c00d00c40300a101d40c51300100401c01154546d80f2454840380c1c08003080c20301207420f00741e03401d42d004500d00110b01580c9480d6127803d80003070300d50311500c0d00c40001b8108440c0d44ca2414a840c0c0020032010142c00b0083c07400c2c0100280305c1150341400b01c00e01003a00203000024560b0350300420144010081c41c1141e001966000141c042030040e0b5986000c1e100c1140418100411540d144840e0300002d0003943c1c0036106030901c1c084a9440c0d01605000e07140380d560215055150a0001e008560160885508070f42498001d00c0400c07031100540303003240c68000004201c0500640141d4a61280c0180c000c0081c0c203265103491410f40000380d01045801139402080721010b00f00840b03845146030b03c4c41044640041c00100310300751042c01203c02064005100003052021400308404a030710582c8100c9103250046030030002e0009142d04040610390000b080c500d10714050010304441c0c45840030311801d020351500403410040354030071049261800a0f140ca990 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 239414739 1250 239413489 239413507
    0x60307170a020a0f081e0c0d0201120911040b030111270306071e080f18012702031b010818030d06230307050f01031e0c09031502040b0d09060e0102 65
    0x44104c2034010740e5140d11601da0501c840040001c2c2071180c8421801c040d02041d0544400c00204804a420a0741040700c00740c04000740d0b06961041c004190304c180010b0200308504414403055a40c6880101d00c0f1f40d14000c50300410003085003c84032000002c140f81924100401c00c501c0340b540c110400c10703825104000810441e030360041c240c049a86004613448441641d0283c0455440c0c804541c2032012078140d2021540400b4581030020422501c8000801d40c80c3d82c813428051031121903070070300380000350041e44d00095080c284044c0d4a03900d04521103007554006080041c080c1c40001d00b9005805400704401c10200c1418800d0300c04c3c0501064060103000c1d0745018003420424041000d0350b101030614200383e15481c0000d013031811034501801c0105801c0907100194010010b103042140c0c1c0400d00074022050180d240325032007982640d034503090115419400c0840102c10040e010103e8a44108001d0103400010426036241c501d07840c0e004203500c90326103014400f40041550440030b5600110328a85 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 239415989 1250 239414739 239414759
    0x703060f111b010510051003020c0a051c0915090509090a05010c0804150b10030209030a0605040b04030f050a020705120a1221060e1f0e010b03040614060307170a020a 73
    0x40940c008100038401034030341c1700844085101c0341c813517681c1c820001c0032031040c0c0f03a002e50041d024450035801a58018046500d5507420010641c006c1800511885160030b80140c001088034054122070980040c2981b034440040d20452482c01010701c19441100003da03060001c100070300300f4542c014002d100701c03040042c2c080e03d500810748044441807034206070b03603020100900c44d5031380d07514004100000d00c5841410a8009502c00600c00340c042c00741e00041c0300481e82c2805101e019034410441e08683c0d141904000301200a4040403070308000c002c01400382c2e20741d80055000d050b1442200d421422003e1000c10700d2822042d154020480c502d454010201c0e5608030041c500c081604078082a40c180720300300d00004603013035400354000406801f0081030000b0410554600f14940d007000d2581d04903100c0a80149500090303121880521000003004100400b50240300344900b0800424403ca060003000240c407002c10340581d15540440310021340300280104403441d01c0c107802400c03014145442d045442 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 239417239 1250 239415989 239416027
    0xf010204091d0c0f13090b130302010c17060906010302070506090109030e030721080f03090a02010e15160618030c11153009150907080703060f11 64
    0x440b9801002c207031140c407500041030805120a004088070201456401008548800c2c50000c4401c195246001400641034142d550b00030f00201280c4e2a0800c42468000e003564150b504a070100440b4071030740c508501c40716421681000048441c0300306a510840101c0080c0900700300903240d07114460501c00e081c00107500103145107009581d070207495004117090654405092107a13050000c001c03820300b100441010180000d20b072143c80341c146804246801e0540c030750800c1e80c84009a40003400d800046603041112044002c005403402c921035890300b4000700c1c050264980c5690070b208690400410420154000c1c492802c400ea0407080c210200c2c0cd0080103220000d40840b0000f152035800e1450f46040c4144200d0311021703c0080c0d16101008056071030000728981e103902e00d520a601712100401e8041c43ea5407003083e40c0c100a0200c00404506000035035006040e40549402c02241800040340200d412000d503a000b00700807a451495060180c02441705600c3c150918601180d4a200170100310486 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 239418489 1250 239417239 239417261
    0x1911040f0e0d050c0c0d0f0204020c03040e0a0c0504030209060102010b0301110901080903040f120609051009120f0503070302070f021203070311060c120a0b120d090801020705100b030f01020409 85
    0x1103260b10800c401c29141840344e02a840040da01041100840d1301c0c0c424054902e0740d205000c404451241c650100c1c050b40c00c007483c0055590400b003028046182e101003030503401650700f5003c3c072001000c180003400922881c00007900032403008000544590003500407205c0355401400822880d00300d107060380000c0d00031441050020710340303902084101c1800410746040c0c03181b64400003c0c0c1454030607180742000c030b9120700b02d0740d5030b44500003500420360a00c41500c00301070428002c916910b15241c02c1c05000712404943c0140b00c03000c01044201a0b02805495105040d4200143e451201d800c0800621240c4040203512110313800f000000808044080c00b1407074072a4840c2c10070082052003280d110b140443d0583d070351100512058840d40d10546c1c4143d006444003400142d541c1029000c10300c1501c803038501a48540c4400c0b000444103a000c090b01d4010014800218203001f92950340903125030f03030010802c0b04c0b643c43c0c0d944104140d0b020320140720500b804000840d51141e580142e900134103058100c4c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 239419739 1250 239418489 239418493
    0x2030a15141215280e030702010e06120a050a090f080a08090a0b04080711130b1905010804020d061e06050a0510020303180f010c0201020421051911040f0e 68
    0x281403034003100040c120b031400124030b0402001d90b41d4544080c25400020031105940f4054008030091130024810f5601c60050340c00a19078604081c0005000b902910602a0040c035041240709042a41d48000c241c115003080400700301501d0340504c0b54042c0114400c0070340f00d006079a58160810900c00002c0c01c860005403642603460f0b1310070141c1901c40446070340150441e071040c000140020310180c01450050f1040001644006070100441e07215046000601e031450382e114111190b924011900d021040c0300c100d480021305060800003000084090b2000f405040d400509000b08500c82d0092002001c81c40c80b081603041c9941c00c444040c06940c414240110585c404c00b1802d400d025a030007060150f1500114034648910304040706140300b0380303402d02d0035010348802c00c1001c01082c0a150000442070f0b00140c0c0b00c03070505150502010f840c80107402d0005240040d6000120f010640503003000144900c8400106030381446480c10380d0110304540d02900e80000403074009455407048031110341c9003003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 239420989 1250 239419739 239419759
    0xf0b07020906060909040303090f0b0106020a03230a0c05120a08010e090109120c02010903080a180e01050109060f020304030803040b01060f03050601050915130303050408160501050d02030a1514 85
    0x7060254031300c28000c072079800c01001c00016000ca4000e400c9600345c28440c9000c0c400c0e16000d0303140c4d1000614207820020040c0c12051210040c0355028070842758084010402e050006c4034042c81d0402841041414014844814454400e200d014050240b090200704200c0da550a00003030000c0c8048003d001c1d0128200220000c0b42c50b821051281d0080d00c1da101e001c0058000c1c0102c1e007030b0303451400301c08228100b00322200c0202c0010704c04c40240030401480c3d241c0314811400321003015000c00c00e580200740800b074440010002c0d680d00c00700c42c900b15042814020030601107584100c0c158402c68002502c1e0751800000d20040060020116041791020358070141280c41400048041e581c064518034009031081c00410f8680c51300b031100441107460300c891301e0724018003013128001d880300b50b50003a00428401701d400c001e0038806000245d58080c2a1aa001c00c180c00d01c40060090300586154403220340d408000203600070b01c1d56100802c4e6140c881940100c40707a481d104c080000d040e8120b11801184202 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 239422239 1250 239420989 239421001
    0xb07020303041514010501080426030610030b061204030527040c050702090f060103182901080604080904020705011a03120903031c021306021b01090806070807090f0b070209 76
    0x2210305556241c0f034134150001c9900c2c2100440310700c00701a1003035038005030302809074030041c980c1a09108401c6001c4a150380303030314200c420044040d1743d0211036024103041003162406955001c04440c00c0400d480302c640c04944860038104c846001ea00340f08103c0039030a419204850b0800c1e403605104880c200c0c0e041c4184000c454084540707018200c2c1c020f41001c001c602003000402d140903402d07403208044c500080e0b40c000b5010b0f6074600c00c41c0c020080e40c0300032038410103481c82c0c68200810326685030004480c00310395141030240d582d250f01c0108041d00e19140400e40d1082d86c0d982d50102d680b540c2e0002d000340114540000c09103181e183c21551a44288180c40d10440c15070480800e44550301d9009000c2c6081004600450000d02c00b1006040c001d546d0810201e00c5841d200c04081c4050b1203940d0042141510317080c901114240c100318194180109280100000980042e9142d8082401d15064100d9260344400b075820604981102190f1003400394041340b600d030003202a1040c80d000b2203450341c60751a50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 239423489 1250 239422239 239422241
    0x4031520040503075604140102190f020f13050709050f10110a08120703050702030f04060e010c17180f030a03140d02040b03060f030d0e0f04090b070203030415 70
    0x74079034030b1101101030040d480707140002040394001c5517207a45000b44141e00074403958a0a510804c600ca034041c0200741800400d241d03c204001004080c00140b0700c014000c2d021100440c007100d40105500460200030b0110b440b4403a420442c941c1c054621044c00100c2c0390550081d00086a80200291500e0300006545c80c0c21481c0302c4c5014000f801c0c03044500c40340181200c0c00d40f481100d00344113110783e42e070100c0040c00c150010f0140c3c10903060084442c0c100300d0802000c1e00d0019296804540c001d02c0000610050202104c0840300117007488d0801c181340354010303207500104081c040c20040d07400d0300e01e0501a40e0342004000110a40c0d0304122101130200c108030300d03050b021220070340580c00f82101d600000e001c3d214101600604625441c2410400000700060360300c15040b505905002100340180c1d81445a1113040c3d4480440c05080021a021002040b02e00004821841006a002512160384072a401042040d8010a440364117103032020000c2d40c1c3c4d52040d00c080b11802c03e54000d9590710415 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 239424739 1250 239423489 239423519
    0x106081e060a05071e090b03130b0108120f0901021e010f0b010c08070605060607080a020705010e010509030c0f06070807060e060702030310092304060501050a080f030403152004050307 81
    0xc071343c454201142d0340c2c5c9103c0e140060030b013040d001442810389001c00d98124110140d481160801c4480022240d6468034a10a44d0183d0151500d0380c0308603141900940311000b5525540c000414031619000d0b0040100c0c40d222020f030242d940e4801c00040c2c007003004419003248001da400071130b091009075111401124401410940508484401d2000c140001d25940000e40c000000130011802c00302c01c1e45581d080759014100400140e031181d40b041103156005103485030821000d00305981441ca54101080e110801080c0940c483c00000704613200c1c2d983c8100030340d12015085941e583c3c031203a8920304040148035400010001e8820382c00000c5160341b001044034414101512440398880c07900e503125010302858500081c05541d2924204c44030802c45100c10b202e41c0c00f031a408207055140100707016501000340c00c400b84d103401c5052914000e500000031a01101d60055419aa03500080c131250014007443e01c40a00e40c1110884440000c140704002d841941d01c203d0540f46965a514240c0e03106000e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 239425989 1250 239424739 239424751
    0x60203070b06040e0703120f0e010305010b16032f060a0c0c060509030f072303180d0f02030312040b100509010509100b0c0a060b0f061b0106081e060a05 67
    0x941d0000119a03040035000b039419030140d0021901c0d01e41e16a81c075920003c0314482c1840004440045074000154001929200a8002c0c00c0c00c00041d4181142201c0b03a201e41c0e0f01b5424203100001d404030030980304400b200500f900c01e4840c0038200b0080d6010084401c1030324400c0380035100d99000703e506880b0500c40d1201440e00c1d51100b4640c0c44a0380c0d1b0b410007400000380000c0c0540420305c81e000f4240c4905004044551240200384408400700e090345224400e8100403240720343c401e01070038500c002120115032030101c00304c07031400c8100464a0710980440001c44001d400d40404140c0a50308440b2000c03ca002c0d901c2420800740540d2640c0c00590891028443c0c1c41c2e1004040f001001242020455a41c02c492842059040d10781c1f1500180d0781940050b100c500e20b64841800032040c442d6a10409520308000c9a0030300107031407040002240c81c00b6410100904242c580307200203000a003503000c4002032004005840840d05d40c12111040220011003040d098080c900c00104580c200e8442d11340304078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 239427239 1250 239425989 239426003
    0x20309070f120203060619030b09010e031305041515031d07060c1208040c0b030c0c0a03180503120315011b050102070303140f010902090a05030f0f15010b0307031e091b06020307 78
    0x1c0c0f03540c035501d00c0004080c00cad04a90303561b100c40b50001d125080c0300510300040a0081800710381c0c43d19090204460107056000d0030503a0681080c049140c03001042c01420740e0030f16012a40140c5203110b801006810f07140303110944252103002a88603045020344405a02a0a140041000c45001030359190402c59000703003040d10190040c0b20200001e4080c1d42c200407c4c43d861810300961030740071441c00140203011f4000c40c3c004050072036400c220001d040060801600504519500700c44120102c1c0006402080c0e1560035849a00160340708288411b81c101403010f400034020b1080c02c00c00e0003540003141c10780000307007031051240028400b10f03800742c02100c07022000001c3d03a217000f180740000e4010604c031540c0000c14400000b0340d43c3d810489080030499281c050107400401e01c01a40c50460000c21014403040c080340100b1020710860b00fa41d41c8181075003404243c0c0031510b4200c0c0b0ba400c0c61801c24218041c0380141e4503043c0400814000300681d500141d0400f0303e9166681a030342e038014408024000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 239428489 1250 239427239 239427289
    0x190b091618080d1202071e060b041a091503031306080711100b010905031005090c0a0f0324050901050402010e0402091003020c0705210c0a0f0603020309070f1202030606 74
    0x80d00c07800400805800d104e50050600c01c507aa038000c4c03281e080030b0100d00000400a040810310429110b09450b81c0d000701c4041052001d06410000280080c41d012417044a0510005141c0108600c901820041c010184c2e035540c881d445041c014542a8052140082c14900010b01c1c064020303c981c41c0500b5480c1c0041020454045801e03018140402c4c8981c100708200c00d000034261030030000030300c02c00d59a2034081401c1c075244415900d448000203400348200c07095a010024078416403041c800f03a81e007041090404100f807400903c1c0805488540c003549600d09010880e00f18419449140214401d0b40c6a02055803a50b0070042030340200030441c1c1d44184018511044240242e00802401c410b010079190156994000110041503d050781d03100505d011580902c65507081c0120025000121070780c400c070b2400d1106030181294140164418150b0020209800500412400000b840c00c8000701e07118507155002c03000141c0c01a90300301c1c040c5c407801c0042038452a008058a1040c644d0301101810703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 239429739 1250 239428489 239428513
    0x80103060513120306080c04060521030c07060905030c1009090914010c0302040f0f0b03010506030915090c0a080c03030708093d0e0306190b09161808 66
    0x2040c015000c00c0b000055185a9030000e41152032030300c9003c8040c0c070000341070703450134802d40c2c20143c040b40d0140c451441c00005000380d03907501c000c94881c203030b188812107104c030b903200c09c51807451140f40c0d5086003d03c50130070b0009031542c2c85100e61050b107905a068070407000540c0148946450580c0103a80410520202800303030407100d600031060300d4012008400d4400900003c1400c60307420b800c2110000750005030030300454100f06004801490301c4030410820914000e80c0309490302040c01004d1055400002046106004000c50411000d207a02c2c03900700c0f404c0148489607a1401e61703403c0c134000c510090700028801c00103d01d020b403012014015610b400300c0c40e965000a0f80c400c00c6003a034003207196001a8200d00c40e41c00c17500503040310800311142c0c4014051b0110400000780700c0c031000304803940c8090080c42c3c03008100250000720141d105455101003110320f42c0900154954541c201c482801003003a00b94a6000710702c425240b0b601d40805040250030104038041041c0522101c0754003400c81031074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 239430989 1250 239429739 239429741
    0x1e0d0b101e02032101080708190803060d1208150d0201021903020f060703020918160c14012c070501050f0a0203090a080a060608010c090504020f0403021f0f090608010306 75
    0x80c00314041c4152031924040c0074130944d40700c001c800b80000680d24100140304069041160a002d4191200140003201441d0f01c00855480c0c6c1e050000d054840110228411f40c42e068403580b5050f0340314040038007031240c0c00f00041c07c80c0c1c01129103003202e0350142402c0c0030601b0b01040e0456401d4060340504413582e0380c0d0550010000031709408804501c0f0f9028034006007607090000c02d010340400c0e580503a4441003c010000941c000340302800c0011682d40500142c00c60804040710300310700d203042082d1001d03a58180b07010109103981c1c135001154200250040c1481405141c0307100d44803003203d01c40c7d602061a0905075103215a0281c2c80c041081080000001107040340506003901071072048a213003500d03c03c04122507241c594010a1160302c079070101c1c410002d0a004010240230080d00801100d10744002c000e01c1c0c0c601e03511903d4001c80c0c1c0000c0405541c40da0200b20307005150003612072101401203804002002e0b14030301446c8006501c40d00b000140c1d5121f07211500c22164155185849a400e50702c941d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 239432239 1250 239430989 239431037
    0x612080906090316032f130b1012061203080606030408130f05041d06060d030207080105070512100b03060405060301140903041706090316081e0d0b10 66
    0x941c080400c0c054000c5541c0c0030010360509840c42d050b51080c491441c60601c5103000c0810203507550f0100111040f0601845410b941d46000003120080140100c02510600811110481d02c0d008118a1110381185811030035800c1c0821030101c04010541d0748185400d003010005200800244082c0c000c0747c810315141010b9074015000709a000c0c500029003041484d610300551280e1101d0310081005c10081c9480c1c030507201805460700030761b107a00da003080c04661200307001800140709036810390680d01494070820808020700600130080060f4105a10050904d800c42d07100d650010344910f001680b80010030410768101d80009402c1400c45e2145010040a400000d03d10b58166681c0e0394103600c22000d80e04003074003d10f03162016640d52820040c0c0e1a1040d41003170303591002c907030109051000700c0b0000403c40b6148484000c19003055021458070598902c610f2001d2004010b10a101c40c601e24443d1004144840c14901c0402601540303405000c82c80ba0b005e4440008901c0c1b120700c500440700d0350200300d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 239433489 1250 239432239 239432257
    0x120715080c0d050112020f0102060403020703021201110309031806040b090616050322090b06030c0a02070b0a03061409071b0203010b1002011d0616050a030b060a0804020f04061208 79
    0x1d5810300040020b0700d000c031a0240c0c03001e411203d40a00903019804c1221030308000d100b003840941a603260540740070b5a20152844001d00411481c1591085440c2c04c1d8424445e10030607a80071a920f003031090303100d0380c0c0750080f040c8034039404140c01a01d004c51800e401120116210400510b0511034408100031464226801052080c0d00c500b96802c00620180010308040b07101d1903000070103100300205c5590045003a003264000502c1e00303d0b0012180d82e5402669484042c070741c0303030719a6103506c0c28040b401d010550303002c0e0005540106e610441d03181c05804c00c0c1c080da041c000200c403051030107000300082820b06590303c1c00854119101e440c04481c046095080b994001f6001089060038100032500040480508100603551034504107903108107181003541841e400b1004180c2070502c0580741a51595080d83c0109014002078602c207040d000341c0120210f0075000348096142e0864400150211401306c8080b481000600f07061120b40c03174244030344000e440710881c10f501600c41540e1505c1440d4041030356 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 239434739 1250 239433489 239433511
    0x3020c10020408030a08090c03031e0c06040b040b07050a0804020415030510060306200f0a110a06020d0509160b07150e010903120203071b020d06060603050612071508 73
    0x2145580d50001e00080c07000b02009401980c0c2ca280340440101a428041c101c031f9003c0d00480d4030380b50f25580020995101c081d900c09151035103119190a8001c52141411400480c001c2d44204814070240031032403031040b030290314030301050b030f4402d00b0848080c07007607500440119803210302190150419034007a162074044614900303d00da0700d0b07440d03040c070f4100d105052180a5486010620400019004983c0480c030015204030160180100035510350198050051840da408130302300004601c00c004400c0408a140180c52641006060207000fa5010022080c3c0042c01c0801003215507200041d40a41e4003183d8814140c0141000e118603a603902c005002e60394881449044400890380703104405d1146c1d9a1400013400d16864900900845a021781d0246a940b042c0108058140c20156840300441010000080030003140f0000b1000e60002c0d00181034503140a1000c80c4803601079015600400b001c4500c00310007406500d0b0315590b581d1502a458914805042c52031095000d12500d0750000d4054113 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 239435989 1250 239434739 239434753
    0x6080702070f06210f021e0405030303150d060509031b0d0807110c04020f09100804030e040b010504031e1e03140c0106050310060f050d0f020f040b060a03090b0601091503020c 77
    0x4070003000c5c1c81c51404c1d1402000e50000b0808179462483e0310804120741060f003206c0c10b192624002a071240070091440c1d02d080001c0048940c1e69035035006520740564450300400c81420a40d501d80d0b0340742c204203031450802c000c03041c03590244500000e4079030810400c2e0340c0b03290031941d860804440708001c3c104200894454820742442d1540c4500240004000750740c166074a0f188404204040420341042d04014031104000b4040440d0307000d0154140e255007560086409030f0300c207004031400d200700c2e400603001000761034503401d40300528046802001e0060500d030403082c464002c1031000544810b07005000c41d00000c1c04000e050052005000701040a00c00061229614000b180c2404071402000701d503960360350401e00c0000c0380583c001c03001e030070141c424a1a484580e5102ca4003410380c0c800203407081301a84020320b92659507400c20741c0c0382540505407649841c3d80d2000038002e02800c601c2100d900c2c400300d0000307929510504490044840740502020b0110f0343c200b003038000754014491518503000c0d5035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 239437239 1250 239435989 239436047
    0x3030f020c0f0a1205030f130c0f09020315010e0d030c05010912020607020706090b071b0b0f0c06011a0306090717010b09090601031e0b01030e0604060606080702070f06 74
    0xc840c9288030800400901144400c0d46446008113029503c00c03c2804402d10610100d8072000420039404441900811a080706a007080070820b600c980c85448440e110703e0300414010031940246018800010340307100d40d154264015646c500301d41980942182140a040010038880c1040c3e5207007600035000001e0303864040d00c8520f200d100342c1c00d82c1c60159100200788110745604100c0d240081500b0310f08401124204088103060f4030400c180903065a14030480034102d8441120303045c00404005059565441035a04201e056800c8052480c420b4020b031030000501085161001c03850072801e185a40c9565100e00800c155640090079100401250900c0c1400800103210444c4c0030380010f246807902d500c0c6000c00c1040c8403a006244904240c01e04103c1082010760354542680d6288420000c81c02810800040b00200100b41f180e003543c0c400c110902040c405554045001e40d04265a5400300c2d6850540a0340d490910788038040000340400380420140c0e200702078840c4444003050b00948000e07008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 239438489 1250 239437239 239437243
    0xc060b10020f0613050a08220915090203010b0429030f04060c1110020a03270501270303050a0f050403020d020d02070e060402070609050601030501150e0103080703030f020c 76
    0x100c52500507038850100c000c0420010020b46500040102c0c40e0b50b0042c10340d03a955901c48104000092483d074022175880b1307110459120700c0b01c011030707560711496034181e5600801c80500307652044000c020800300808200440c260007200e058512803c0c140e81351521b00300088204440e82c98180c4065140407410b100004010b00042d409000800417031145800d0504210040b6058082e1440c01c1c44000601c0c5541c1d00c1000c145a001d40c00c2698006031101008602607010349024143e4180080489030040504ea5904488001650094000700400c41d005880c100c21007038607018400300441ca010103080040e2080d004281e200f010a400802c84a0b1640345001c2038a0007614100c0c050303000441d04c51800740d41006410070b03001c035074402001402c2c940101d003c503102c0701810560003181c00184180a00071036411090199611908561456039281002c0d40200f40c1d006801c944070440c0b03240060743c3d14481d40d0b0380e810f90360440e0b982c5150284c20342e400d038010864051150705d001c0d02404882c1c1c00c0c04003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 239439739 1250 239438489 239438509
    0x20309030601060801080d0e0d201c050120040308030402010302070b0f18240c040b0f1306090302100c02010908030f0a120225050a06020d0204080f010501060f0c060b 73
    0x84e2141082c5504040394642482c4469400e0020000e0b1840905400c0c0d89400450010300e030482282c0b650390315140c0d0701099080807a8500c5402001e46524400d955443d03a0124201c240602d00821000b1140c0d506540c0d100c000c9910b01407901402c6c001800444ea100340110f4000b44141801454080d8540d141000c0c14400c07200b84a02c903908004100e000c94852002940c1501100090079100b0703c2000903040e141d826034000001032408400065120022b07030204c41c003820384054020b48600d55500f020809a00c802e071408644003421000041281c095107840099070381c020070139a059480c0e8a400c4030f01d02c00c0c44c00241d04002007036000045ca030f8000c1c0010804031081c180c0c0b503503032284041c80103800311840000e240b40a6104110a0820030b01400316055524211062104a5251420114601074600708041c001320702c000f03403070411050107a0041c800c4401c1ea4007510440c0c007204010500f2901c0912840c0007003410300824154151103041b10904903485002c1c0004e000611078045040315003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 239440989 1250 239439739 239439749
    0x80601030210121b050a020609070e18010204093b0303040b0601020c0406060201020d110415080603030d0c020616180915090f0b010e0a0f0b0306060d140109052406070201020309030601 81
    0x940086c080d180541d05101569012502600070701030103240c40039440000500600b1090000902018100100c01c29011075006128070103013400030681c00e1b03410202500f100b1106982003074103400101c03400c1c03e540d403000c0d075000f88010145096030b9035034440b104c0c101c100916041c110b01410b841004113544506c1880050600f5600060700d504511500d803040310304102e40c114a0000600c000c11006d0582d074220031425805280500d800d0301e80002086c558043c1001c18165941810755114441d03a000840921411494807980c0d6615240481501e050302e050021120100007800140501781b0741d40c002ca9031841d22402e40e008080d03600d440c000708072010301c510b001c101d0b81c0303c102d958000d41c0e01c044130040d003030021565121058a00500817a1644045c823580b15582c001000051599440b0000d682c001051008240060705000c100c2c1100503000f40240c0180074503000110300140210701d5541d8100d03540011024201a0302404c00149804c1072808038111f00c42009050001d4030f081c400240241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 239442239 1250 239440989 239440997
    0xa030608010c09180c030b09040b0415020715090c050a0902520f030f120c09060e151308070603020a09060e1305070f0801080601030210121b 62
    0x142029805401e5442e000303465410010080003c0c01404440e016030403422402a0300015200d912140541c0039240a165060388540b0400800c030034040030b000a58801c911806100d00d10150600400040740541c90000d07110700314121038031041c56895881000324500543e01c4112155440001071002c1560782c0140e007205401189101c44246104084529001055484004140600e064040d203241038204005920040203500c541210284071140025401c0b01c10710324400114100601421714100216000400c015030760440440d5a00c41ca04c683c81c05075507400c00040c43e150003100d0383c0400b81e10079a0312103011b1160004644000b40240345a540e03580440f030031146810a01428914140c0c440805c1c18010031140c0e0b105544400d000c81a5203080c1030400b4200800400700756440d005051701c181c0e403442c1ca000d208201d60455109500203503103035a03070246681c03110425516202e082c88000d42000d212500340031014000d900c10b1640c002c000d040001c3d280c4000100080368460024450082 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 239443489 1250 239442239 239442251
    0x603020a0e011514160b07080f040203060c0d0b04091112010e060a0515091521030a0f02030c07060903020405090129060d0609050105040e06070f0c0204110a03 70
    0x508026240c4030050000c15122401985820b07048849101c03034104180400c541e15010441d01d201800960b0170f4950744080c0d101e40183d4601c0d080c040c41d84280c4411000c903c048001921a00300300200501c21039014000e072115444490f0405941d41154058060207900c0304c1c0001e0a60300c1d18411401c0b003d008640303200c1e0f1041070358140080c0c9400e8001481203a4142010700c964039400145150f048418038030009891354030288003441c204d50048030581d100850800f4800c02509801201000407812521420030140c9120b040035880c400c076600d6103154205000c0b101e02c1030301035020f0200044060050703e2814290307804031410321270340f904624041840e41a090055003000e1040e41d9210001c08000c0001d10040481042507103012142c185414003036184c6078800e0380304c0509842400d000b01d001805400e0f180c00b00c13000540f400340503460103945000143c2148210008280b03010ba4541c1d15600119043c0500482e5584070b42c00084e07030400e480e1024002c103d0300311402401444502d40e400504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 239444739 1250 239443489 239443493
    0x5010302010306061d220905070509011203170403030902030304091e0c020c090c1b0c03010e06010b120c120405010203180708030a030f0f18050d1701050f030f010e010603 75
    0x3100d14a800c0b44003000324448000c011111402c04525061400f1281011b0407003803182110b078080c203900c10301d5611134185244d000400100080341c2d03065034000c44414155030f80324490804601020b50001d400074007030a00ca078100c0220140718540080c064640402c1001041d008289150701070b501c6001c40729507a0482c48090446100410400244008180908860810000d43c1e902200000ca032007015000c005c15040440da404907052000082d440120113200d042d012078480071949401d502030b50a01d0054404042c004c94124183c501158400b800c001d0744d0040904910300041c001d01d500c070b00820005240c0d120201070144501d21410026960b454140031080050303103036502103800c81d07001507004e206400001c0181c400400180c6000218080010756400203444c00b682d086030710070314007d009610940c0044403090205c1c00341c400c450203501c21060451b511044038491801c1001440300610091600ea41d040420b400c004040f10803042400e901c203801c6400d80c800c2494240e41d0b608003002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 239445989 1250 239444739 239444741
    0x305010603050714040b060a030b190611150103030504060f03090b160e040b030304062f0a020a060206060d0609020609030d120b01020c1003091e0609110303190302131701050103020103 81
    0x50a0320143d03803e00000c41b0341000f041d100e008001800c81450b0312500c1034500b45d10b60311a405c00701e0080c002ca0800c40c554440010b000300c1d8460504a40b46e01482c0f2480389801c0341e64090604881e4940d41e0715242514003101254071094860b400c1040540b1083d648000c01c698020560285140da202648003425960024242c0400301d40018065801c1140c1801c3c281d5004c401e07039007121080c1c00c1074491041c2070328001100c00f2440d40e1140c015100005030b1007902c0300019140b282c0742d109690703041c0d407140c80340c406a035191406c60384a40d1104146801d50009a41030300441d01442c4094821810046d090000078180040707070b00caa000040c81407000826911325805117181d10b040031b00107400041404030200302c5058010800a0a250301ca003035041c100816841c034a40589244003020741d428101d071405c40054001104240c440b121110354000480c0b501004136284510300c0300103900065141601a0042e41000951945050801c200040c0b40207032115100700340c2e5480d500008140d815480058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 239447239 1250 239445989 239446019
    0x90405130c1509080d0905191703030906060109080d12092004060605070c0e0402030f0a0b062409040c050d0207050c10032708070f082701140309030403050106030507 73
    0x135030198840c0b402d180400d508418078100784c80c4250360441000140c01038416907400c50b03501226070b60104140069070400c01001071801f0322808000d441b220f4403100c0044504c00080c0c059100990009000f4800443c0540101405484050004282d0342c2ca2034480901d2040b00316240c0341b50080e0f5500c162058034240c032030380b4060700380f0b428414201a1541c6441040038402d0041440711808000030030207542c0c08100b0f0195145001003120004c5030145007142110b1000e03504940150b416070302c0340f40a58034008812450800114210741000002c4040001a007441d41642043c00410054503141040394001008018055402001e1902c030110034405001350081517141090301d0400400d20400103c44414050b0f040c43d46500b100306428140214548a10280100300741007928815081000403000303000503005c07201d01540400d03074031074a4035841701d50040c0b41400514260140402d0b8216000990742003040441207908158990b81c40a0858119400644181e401080f04000c500e600c89000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 239448489 1250 239447239 239447249
    0x21603080105150a050304051c0203120f01050d020609121b090c0a141321060506030a0302030a26010902041e1d060d0f08030703060506070206090405130c1509 70
    0x115480f40c60440c91980d450148030340b48401c000c000404101400020003504281c9601c4070340750030740910b03191401380d0740703070700140031002c082d804140007840c0c8032001009141203500181c001c10108800b5403c10000e03902625200343e01a071044c01c01c107448001040000f0802d0900d491620100507420304000815400412864414404101ca0314003543e1003040d21892640341083c1c0ea031079015017140803109004039088244c240001c0c0c004002c500d14104440d40425000e05010021a1511818507486d058071000c00f07005a8400c00005421074440c040e401d604a1282403589511640e000d007030b182030842070f80582142e41c0c01041c00e010814000202e0340c030000650074600c070b0b41450500000411802c0e41c2c901821503988400003442074561820f4282d00a600c8880c00b440b41400b40b501c0c41c0d40da0410354201002914060000c03695003400030440340f199070003d1083e0704048220003048042c1c080244a040000010028007001036030142c0400d025002401c0400650f52078081c000340080455848 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 239449739 1250 239448489 239448499
    0x32506050720010209100e01052205011209020306040212010e0709021209060103120815040e010f05090a020d0f03020a02060a090302030d090518100506041421030f030a0906021603080105 82
    0x17180c0941c1d140c03102001c0b10000c40c188000c0700c00d00000169620301941c45404c800c4091643c0141324a0340450b030840542d03000741c813a95044103a6023162821a034070150020741603400b1384003007405846e25810410000301000c0001c1070243d4410380c05400c0045951000b01c00c56004902858402401e841c442ea00240c00e8005211640c91034880300d03a02c00c0300011850034030541c680812001058820407084452025000b4424072070021103107402021003c850032221032414001c04d1180c2e1007c00c103541e107a81c0040a107050400c1035281d1800d24001090f08900758454180c0c5400143c80b0000900762200305070b140c0360940c2d45140113140c00e100004004104214074260184500d5849030005a02c505040c1c400c850741d952401032440e0301d6140740e000b45903c803601150001300550884400300b41000c040d2038000549200e2500e90740402d000070754044064005000112190403880090750703010800210120f03410a4549840003240d02004000c000814032100030810315422040380c072300401c0e042d22 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 239450989 1250 239449739 239449747
    0x302060f0a0e06040303180b0106171602101d06010608040519031b0201090b030117070b0a090501080709120b07022a0f010903020a0801020301060219050325060507200102 75
    0x600c0c58581a00800042c28075075112003a8880c0c0007c1d80c400e03000940d000307040900345c3d41c583c1005452100801040904070b003549000808184a20380041d1078548607070001d001c00c2e2884001c6101620f0410000b012005021a003001c40040410a1074020100c54035100c49606050030410308081000c418035400c100208000e800003540401d900b5524405c11000c034903a81c0917440100e0710005103912224030140d0100001c1418a48072044210040d01c003000c890702e840e514000351483e8041ea84c031001c0440d1000d101000b8650040c140e03654408c0035850501481ca8907030100742102d00180354280c0307401103a0301c20000c10640402c802e540c00d56040c284008400b0703420000c458035254043d0100e00404180340f1701c82580e40250626009580e00606849a03c0c1c0c80f103c0450013134009100d040300501c5003e1102c511b0700c0d6079602c02d001003500400503503d0803004200711000400d07191582050001000800400f140c0380c1e204a5001c4c4c0256550b000a05c00140c50085034424401104212071344100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 239452239 1250 239450989 239451011
    0x603050712020a050603190501060e0f09090c010503071101180b0708060d080f090d0b040c0f060c0b180307060501030314040b040e0c0c060114010206070305011d0402040b0a030302060f0a 82
    0x550002203031300840f18035030b90b90b80d030340e10581050800e00c200715012814003001141964121480885041083d10b02d03005117000c0c0700c20040c003044152400019600981c10f03194095100d40010341c1d11406508155101000c4512070341e003120060005060140310810b800e10802804000042e0030000514203c401c6c0d041910006010061652008200b880002031315a42c04043c034054551200b0700400522604030a03092040552104840c100c4450b40c1080000c034510115101440985e24903640c0e5860b400b02590324110b103240c020700000c02400b921480e540b020742080005020329403080f500810315525602d0040e0440100654001803280207102c284101d034000c10540e0210b40449400c7c9030140c035a0b194540f241c1c0b040041d00325140c02a0800440d5030240080608000c681c281e088030640c0e1342d41d40e070403412100300f805030204a0300d6040460a404a1451200790400c0c00204000303002160301d000980c026407a54411009600302d00f0402c14021200100d0a900c5040c050041c420740280c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 239453489 1250 239452239 239452249
    0x307021306050f120c04060611010e012d0b0a030807030801050303090f0103110714030403120215010e0702121c0b0301060b0a0c08040905010303090503061608270709060305071202 79
    0x3e014039000e000c94031081a000f2008000b000c1c2a02000f801c208a5143c0318440100305048100030441d043d070178400301e1a444841445510340d0030040c0d5102003059461101001c02c01c0711200c030071005d629107440880c001c650344c803001c65006503c2466059650340031442d000c2e01140c81688000c1c460b41082c0900743c0d030ba448411045000c0e605c00d10740000e110310540054141406503000203008504c1c0080080140d22000001f44196406001e61048030301100c2c0080b40e84424200c1e5694940c0c41d400300400c0344040015030a90051a00c0c01529040c0180204d001001c2c0c00c030140c0c41805048000040720300c140d043c0301b03446241105500a01803a03041855151082c0f1460030303844100800901002d05000b295001c2e05e000c0c02da8075500780041d59503400d0003402541e540c0a440d1082c000c0308085140c802e4440e584081c4600c2c2515250000c0da100032070340c1c1e5100b040e120b01c60750549a55108042005050101c24003070690350800044540c00d604081b45042075a400c040300008052180f900036a544e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 239454739 1250 239453489 239453509
    0x603050d03200c0c1302090105040b1c0e0d0905190b03060121050103060f020316120f05010306050106090f03052e050403020d080c09010c020907050c060702030702130605 75
    0x914100441c400d03001c0180064103a44040600d07481c0b28010680c01c02034240492180c440c00e40031500040312913641c2d110817040784a031078009408904208001c01580d001d05000d003d20000d2004145410440d1550380360a481e104890360341c140d000303d5002da20064001441c440030300f600b9030b1122182c104034107149082040501903002d440074040002800341e80304070301469200100e0640e01b180d409a0010820107400e081c0001c40d102410164000c081e0380c11882a02e100700b50248020345103600c0080b013a0340e4019151a10f0720b80e80e44070701900c0700d8a052401040d008500c64400003603a0740c50700c00014414145034215848014403c8010004500e0000c2d06610001c00001c440c1018044001d401500303c0f88103603051805800d02040000303064011403ca2520b10607500c82d41580e6840c05000c2032070340b103014413842c04920340805440150802c4503005a100031542061032414000228a43c54074204841c043c0042e4400141e8108605102040246040000501384645810700340040c2e68003035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 239455989 1250 239454739 239454763
    0xc080a09020f030706020105010f21030c02040f0612120201020c07031407120602030f060a21021203070c081501050108010302060307090b0c010c17070c080c0a0c0b030a0e01060305 79
    0x2454800c01401d6603a000080003003488014100d803113290b961030010f8040c010920901c086d0300c40c00500043d4a081d4810092040b0460100e159040b01640d40c6c10f030f80c1002402002c0c3e801ca0790380c981c60032030350030a4030031040644508602a90022100d16041d685079045d42d201000f16401441003106211001404000341d81c1d02122040301d45603244c04480c43c0039600d0344201e101c0042801c8103070600040c2c1c2d00550183e40c4041d0f404c0459550304050100c21040c51007080055902c440745840c00c142e0380149603080b903100801c0428500c040124013442c540001c07106a494000240f000c02c9801d00c1004210404603807014600d03000e43c0342c400082c051a50511010f03006000000014101320703c10000e940242040f601c54a80f14028089078034002d0640c01685030215420309100d119484100c0c210354850600c031303552851040050782e1003902c1a08403c0800816107d150b01407800964403010800c040d118040e622500da180201001059480d01d000b00c8410340d25208060000c10804076001107100c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 239457239 1250 239455989 239455991
    0x1103010b01051c02070501020d0204050f120d0f03060807080312070822030e032505121b130609020307120203040f02010807050d151a0414040b010905091017010c080a 73
    0x444401d040b50041d201d05c1200138480d520001e03001001964941c0a002600d40596140c00d410166401b4070002409104003c507180c0e00c01940d02e198184100c8066200314840d141c003155242d83c411303406150585a410000403a0804a100c01003001030110141d070140d00c51804001c14101b010600006c900d210b4410001c40c10000c4441060600840244603030324000380403107418180188800805c400d0410002803200600940050706190035000d4090300401000038000d03d460055041c0d105622028001c0d8002d1400c81610161085610a140051241441c0942da07858900001444a04103185ca14460b51040c002e01002c6203005003168640c95081c2806c0302252100032090380c940c000c0a01303002890782031125030061002400120700c00c0703407048001c0d64215030072000e4522450140c1d0140000800c41c1c0840000c1034a00342d04440304003d8103061203064141c0358001301c0c04403081191901c002c4420f600d4100a44000e04c86811024042d0600800c0302e110003c000070000100680444001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 239458489 1250 239457239 239457277
    0x5070303270605070201180b0a15030b0405030c01060b160314130807080c0307031e0206040e0718090c09030b060f0603070f260606070c050312071103010b0105 70
    0x100755a1100050310041040d61100800ca8a44000035100881d4160300550900040724031403c00d00c290322007180d501603c0c402d020364a00c210034009140001c0150304244107000e0010100b0402070919000d14001c0001c2c540c0c5d4008002c24a0946156900c40b0300b004504001803d00a0411000d090415601d0b2401c0c0000803c0e92039805100c0c000d40c1ca00501c10201100700158543e0f000610340204c0c2d00b0881a00c540a0007a8105929041e0f240b00c042c0c60b5024001100845011f000282d02e4107071310040c02c01e410180c0f41e424880c14104200c80020105d40020b41e00f51090b48802100c100801500c5c009111211a502000300a101c1d1484001c10125000c00400d10b19070f95641d82074140e80c4050301d11038032403501c035000602c1754500046100110351418112408881e6046410700140740b80d081c2289542c41d604140040c03540001010f540050120350301240b10340d818043d80c4a00b504200500e515001c4a0401c0c81074840300c0070700796209070300d08581800180d070003c066500f41c1e03410f40070610070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 239459739 1250 239458489 239458511
    0x30307231e0706031a0a060f020a05100e060615091207090c0801031401020405031e03090d0b07020d1106011703071203151d1f03080c0105010e0c0a05070303 69
    0xa0404030a0001c80c14000c2030585980319100010020101c882070351301401210502e684001240c0e10201c51160090380202c0280900e60042c48064101800b0b88100c1d900410b0b41d880d2242800714040160308a80c0d11501d40074125001000750701e0b00700703608841506004010b604c4d8503e1912038520013078003c0d21510385001901d48140504001404801c005215032001c9100003420700009000c21203c1c0d5801e4102c81410003014825101610700c060000d00c0c841c0d10b200601d01519041280d0800c1034841004480a292075010001c5086489040c07801100d00341090003a00b000c0c11407654070100080903107006040040020280d04450144d005204034030f035081c150904520a80341c024000d0748a04060020144d896030040c0c0006007203038503a0304900e448603050350051011228a0710754052480100c0c003682e003c4134418906903a025a01100140e60355141506600124029801c03651350340010001ea04207020480e034840715440740c1c0b52621007050b001910b0f43c0103a0300050101030f560703420046 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 239460989 1250 239459739 239459743
    0x6032702091e0a1b050f091309061d010f0b03060c03070320040302010e01081611010e01090b0a0b12120d020f030108101a010c0f0c0306051801060503030723 69
    0x50441c081034040c680701e15183c10010003500d4064282070441d10340d10401280980b0440c2034501210300054494a4101160204003a490207240e000315820381c1d80400724000350051049030340103035401d45000705040d0f13200c00d40e508581d20701c1042c1c1507142c107100785070075541d8000c1441588a03040144e2151251186c0c0c0c4201c0041c01014040310721140300568107000150284c0140003280c2c802d80c0d800740c1000112004450902c03040c4c8038443d0300c810003880902000e0248910480040a500c00050f01100c03680c0c0c605d00f5211004819030f08800c541d41880300e800c2850003a64003007001921500c2c01520030441840d42d4501590f40e4821008012902000602841d01200d10400e46c000c2d010340c4a58440100c0c6032075000d55480302461078a481c2c00a105e00f102c440e01031409481c161245240071000741c41d50412841a00c904031880e0002d45c40102c0001c46c07a214060140071071512031306084510040b450700315a050b80000e4429441403188000184221280c54140c161402e0100c6a000081410034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 239462239 1250 239460989 239461021
    0x6060706110c0d021c0504140405090f0106230301021813090c030809040c030b060406051e030c211303031d0f100c090f030201081f0308040603270209 66
    0x12603030b0700900110036040b99000403461000d507020645c00218807003010b000d40b86807055204c0c101c00e5480c000054030b128030f445e074040b9502c07082401c143c8213413194245049003111000d800540040c041e04080b0300a40c220310003c4c9030500c8045d0021854484030380724421082120f401c0c0288141008a0120041502c0c0d80082c54026072111303038880781589904e0010b0043d0030000045000d03a1074100c030403002a01c01e010b041005240500b010b03103070500302201182c0a074003103108003090f201c038000068207000102e0000e41c0300d109080622500c403000000403c070000c1e07411030b6102140807004144921064001685c400c4a03070f040c100082c100c024a000d07501141e407160700ca01d40781c0c0158240c1c3d50140f10042070300910355521940810483c40c10032400d507680b01c07841c069040202c410100c1840194080c046881c0c10001000319441a480300d001e2520102000f50011601002c01242c1081043d800d070059406035011260041c00a01e503200c6560903807043c040c00603224080b200e010401c60711843c0c0d910 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 239463489 1250 239462239 239462257
    0x40f0509060d151a0103020315010509011701150f3b0d0b06040b0d050c040e190809040f0221060105040815010806090a0f080a0203130602060a0506090606070611 71
    0x145140150703a00f034420080502030380280d001503001d135215509611071f1088910a1a0300c1b00045030404a410046405810060549041c0828403410300c50b075400d4429110300800c00b0b1110f20041d154580c400904001d2552100c1051220540b0000e287c00348810060128042c80c061450711040110034040020341c2118003650445407500c5040240041400194811013040d079090048914007802d2003d00c02403170101500c1600000e20303040c401d00e0603030000c880c24075a4108884a08002d85c0c03c1c820f92104102048802c2c40c00090840400d09080c02000c5c0d5550089104504044007607280003241c141c80700d0080e400074603c0000a440780e0040c5c040c0c2d000340040320111000c1c0c070b80100f803455800701c01380554800d9100748800904e407421b0014568401ca944900c0d918521903e6555040c0c3c1508200c03c1c280a600082c40341c440180f0001b51000000c00b11580200f0190401c0c0107850700301c0c0c0001d0001401640329004004181e103501040303420055112800040f8503104e038181d009240114662 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 239464739 1250 239463489 239463503
    0xb010c17090406080c061605160e04120302040b160204140a020702040f020a0e011211070c030b06092707031415070e03100903020c090a05070e06040f0509060d 70
    0x103615600008000640580c10007510b04100283d1070b400b00a5842800c66220f40c5d01c840100044001c0c2c0711002840254103100c0c10440710808c104041600c04080141c0116000780290f008200070300020300002c21500d1400d06085240c58103155102001c0c0c13080d03140350200404452440004c640b40c80d40016190b4561403041440307424070140d00806544942026441181400c4044402115500c201c4e0104512174840f16443c80500006607030203e654080b0f00841030b903c04005122802c542c008000242c07190754079007403a030300354075120400e02c4000c0c068034010281e0004001d00310a100609522480e003200e00303a00030031844d0f8451881e007c0140c20082440001c1046289010000540046086605440c03408103036100001114041c8500903050381c1075004000c03440201c40142d000310300703160103841a10211103c0c0c60200c2d48002003681c10000342980c071400c00403130340c3d4032900321070810710f0803a02c0c9807804e494445200500b42140c000c581c4143e480d5408100303035a8880c1d140886607540800303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 239465989 1250 239464739 239464763
    0x80901020a051f06080c0913260310060305150114090d1103060606160215070605040c0608010f0323031605150601030e0d0c03201f020708030106030b010c 68
    0x4a00760502c0d0303c40c0001c0492410042d000c1000980411000403581d400f620381d5855a8503d20308010400c681d01741500c1c050801c00b00d050480003900183c0c2040300388400d03400c4e505e04000c07010240500c400e03440340f400c041c9048180100280e00540c03003100b8078000d00e0314041c05485040242c1c2e42d4403402e064254801c052049040410a109014040340e0104400f960102e603100410700500d441940001c7c104200340141c1c1034018500041091800c40f40100f2030b0342801c48655a204c1107900a5a05617402c40c403c40c0700700402d542c080f40e20781c00b40002e05000750840d840c0d9601c000b00c126004070160154036540001d60340c102000c2060301c030143c88454004000b09010300b40907490321800440b140d10812041c0c00140203500a00a00414400000c02444c0b1a4036a0804440340c480c000d104804000c82560922865110340700b441c69016403100c09880400b219442110607400c40021645005006001d40c80c0410068001d42c0d04641c500d0502148079811100100c0b2605c980391801408126046 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 239467239 1250 239465989 239466013
    0x10f091d09070e01050603010909080f0d020c06070203210612070f0602071a0a0c0201020a0222051503061315050a05010611010e030a0e0a050901060809060c1303080901020a05 77
    0x1203605008500d00026240307096150750007010452824003410343c1126007000104515840c6901c03a1441138041e00752641000340e075050764012a405050441e04c51a00485ca880c0b041509005d8075030408084d000461910301040c019550080100e0203201c0101400000107035152103084032410038188550556240a84461094602a00b40d00550005100750400800e8000201c19502808031081c50303010300b031011210017180c208001d808202d0440c0140c10745500141c031b07031150030007100c0c441c440c040b545404c10854400032504010401c0387d000c102c00c0440003003520049055a00020803140b0000520142d0602c1c500c0b18001070b24a040c098a00340800406244560169058030002d5070388c445024180c5418500380d501514040e0400d410405c95400b5403409403400c030500c014060074018105580303600241f0001000d83c0000c0220744400c04000c401d1000b80007055000d881380b14964205151840414928255400f0081c4000c0300090084d144e0381c000c00c1922242503010040300c03074802c84a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 239468489 1250 239467239 239467289
    0x1110304150c120c0b0c0f0c010606030b040c0206060d021219050a020906060901080f07031e0917040f1206241403011e0203040c0305190b060a080606010f09 69
    0x500080d542c03140f281030342103000340c0710708440c04003280c0141d0085040d8503091a01c280325881180c5d101105041003040c2c20f144134082c0070342e600030f09950b140090030102c000240815201018217510464000d40708000301950740644072120b290701a00c9030741c00350702e103024440c1c03901c1681c81021125040d0404090b041140018003109420301c00d40e030034030158550009021107809080da1440c0404c01c140300084886030341542042c2d10a1551401282c02100307406404000014100c2c210340b207580341c0d80e1403400e108001031170700300e44600412014981450429000812002c50060319041300b450b401c20018070945400c04c15a1507202c01c842c2c2c1c0c0c5178001340c9034030481410a1041d032004020000102815240601c15820407041c80c00203103c10b60307600d2440310001e50005004a9003200c05450100c00310f6070070003c1d040000000f1600c04035841c100d00304007070001001008680b0809548005110f25000811003640021080c288000210b414110a44141d111600304400c0f03419124241282680c203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 239469739 1250 239468489 239468507
    0x1030b031207120c11040515060406020a05060603060412050d0902061b06060907020d031107050d2001060311190302061305040b06120c030c040e0f091603030e0111030415 75
    0x10400c2401c0f100c0c9860308060320400040782024010040d1400800051304098000c0e0703600070345001ca69903120401d9000912250000c1d048800181d121161002c100181004181e4000c803040b002040b607850316980380303064001182850010003c022400140b00111a0010001d0981c0249040c2d105d6205044940d051405941e45c10381900c0f540000c21100d050800d001030203000d1a41c05890301000d1083d056014101044100007180360802480d40880c04c1880b50382c0203051182d8654400d4003000c101580b030700c82c0b000701c40301d1280d25107001003000a2038142c20b03002d2501c040d190034072000007014488401d064079600280d0061000640d1030b224803580c110038001e46001b240c003001521010000d10040b402100590300782c607845030f000300390306110300000b55900c05d90010003e4640750300c1d0740c092040c214042d101c9001c20303a42001400452038040c4222034100c0b06420011000c0d5266440080942c0b0389009118103201d041004d46428110034812500a440009c140801d24200d80b0401040b03c07030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 239470989 1250 239469739 239469743
    0x5090307091b090612020f0d02030c1e04080a0b06130c0f090905040203060a02091203070c0f0503011b0e01030204030507030506010303080c0a050703030b13051801050703060b04120201030b031207 86
    0x210032501c000180039000001c244d401c295191500c0300402031114000794810f040c1141160780c00d200e03040c100c18080c00118850510b81e10070399110008512034032480d91000501600300724040c0010f00c0303103940010b180420160041c60914060320b4810110700002081d03c03d104603181020300304225243c02148034021150b0b41d64440c801e4540d500c44010498a0580700254141c0144000c581e42c03e1454003e4140114014000c580e0450700d14041032940d401201d0883e54401c0202d8200301c103114049912000745003d500a010352a01c1b80001104881a0301c540b9050120807049d50a0591282c1c1c15039014561110403520703080c0e120700780b250380c41c0000d101c1200041c1c26200017900c4002100c3c192080e4048540300c06041c0340e400d5409074040e1030340811081d00401500f18060705541c5a019040c0941d025805580008869088090039030340300038441e8060600702a010801c084446007160216041d4100415601f1040d20040303019000010303880c1d6041c403c8036000d07c268180080200301c2c0c0c3d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 239472239 1250 239470989 239471021
    0x82206090507090c0c0b2e1505030c03061002030c03070308180309011b020118030308090c1e06210f0709051503011e090c0f020c0307051f0509030709 66
    0x280d030b0b4240d554150f807060686403002405005081001612600c0f1050700910307414460201c03801003884145900c01f420008002c0a200000d080140801170b1807020060b079524a03116207107140645c00800b103880b015110078007804641c008039050398401c2c02602c9202030503000ba25650321090400901c0d1400c16180c19101c458a0030316030308905070001c1152014841030711b9448400428803100c000800c1041400da040c40004c4035255842081003182e00c000e548280c540340e00d00d0910300301e110b180c0902c40c000c25008051244600f18240543d04502901400443d02d035565080c000b0381d82031007210540244403080c01c3e108280441c40012540181c07261580b40c0d1002c411a41d21010004021684100e080c50b4440400c01802a074209078070140c204d01543c04070000803a41c40c2c1407281110140e1903010002001c0020b2a81d50300d0f414050b120715148200c000307003031036420400090203180d0354070700c001403201d460444c8030801c600030010350300380c41c20003010f5413285542c894680000e402d40c0c2000311100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 239473489 1250 239472239 239472253
    0x7080d0302070c050a080d050c010605030706030c031410050d0f0605151513050d0602310f03080a0804140d090312020d080a0209130501091401050a12030822060905 72
    0x181c24070058000c206d07040724000302050080a202590141d001c00b01e06080c0e9500c035940400c0d9620100140c1000f8051036030001009c450340d92004044446407100743e0308500c000c106104050a482c1c0303082054442c03c8400c2c0600c61000d1800c09001083c104009100c5800c000800c20316251503400c0f40142c000644140b1800d150005071080c05d840741c240a548104081d0405001c941052140000b41602ca440018600403104185025450400c03001518078140c1c2030b50205030b44608941c400081811b1100a60454190f0740e500020b8000c03841c00740d080080c03030000075041c03050000309441d00c1058030003651485e02114100400c81d8646001c143c41d10244050383e074111510008003031b4800ba5181e07485080640316160100c3c06540039085456114403601a03695580ca5644502802010405000038203881006118929010141e0020344603050012040123544d100500c0903109030360620300741d40b82d0b40e072f080400740300354071001241c0210080c410045010444a5808071100300e0103101100c00c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 239474739 1250 239473489 239473499
    0x4120b01080601080d05031b160b070e040b010e0f0622031a07020c0904210513060201020702060f07020301020f0d0e0105010906081504080c1906050a02090a030206030907080d0302070c 81
    0x9030740700d00750617200001e90030400205040003001b2404040528414840d14250510940600d1f210850b54280d960004c04070500030351542041a804022500b55000e220102d401c1c0006007200324690f0310f2900903280300403060344540c0c41c1800c454206002101c01d4a404420070078521012045001c21215026030858550000c498801010300c2101c20f94004c105030f03061030303013800110b001c054000c4582000000c00305e42510701e561a1007016814960350346858103c40880d591191205038000400d5910412440700907803039031011642002c89001560b5a65962440803900921540c0b5140140301c00110307603881c502545801c00c05c404d01544000313005607620343c010380d000c41e19180304494640c0c0c40420030310119134144a10a60017030003142c0c240d0a0090140c4c281d41030640301d0b15503a000213894560700d001c03c20588121600b1040c850300c1141006c02200c0032540c1110305002c060321424001c0005404588208400c0e80540051005e541411405140140c0607400a60003260a841e4440740850 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 239475989 1250 239474739 239474743
    0x271509030506130c03120c0b01080d090f060e060c070e0103032c0901120507030210080105011d060703110a2406080303060306060402031b0708030a0c0c03140c0304120b0108060108 79
    0x361150130030b0000303003460300d5681c8203507a14031501600003d0003c8040b088000c1582200154000d01410300641307980d400355075000300108205e07000061002e25500c030520120741d014000054401040d201e10380da4911130003042d8038015007540100c020080710310002c010140c0c00501110380e0b6080255106540040800d0a400b81c002014420f81080c01c03070707004010f03c0482e46c010715210350040e0140c030055601e94011506514120b422000440c074580d00400c05540c0c4800140001014040010300758298503000446500c80c001015040080b100150540060140454240141c0c0302d04034075018150084071140c004c01a025080c0668501600000c9081c000700450b4802c941c0100a40b0b43d40d40c03444100002500060903d004070081c207000781001403c80001014030500031a5096200d00e4103608090644142104541c101b00242d020800041e81080502800c1c0c84d807801c0d52515515030800c85032450041c2d0b4088491043c1041c800c80901c802d50041d80e043e05c1d9000d040e03442603030721130310001c5e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 239477239 1250 239475989 239476021
    0x1060614070308042301050a0504020906011d01260a0e120c1009050a0803010b070b100e0613020f04090207060506150f0a0e0d03020c03010c080601271509030506 71
    0x240100e442d5600140014400300309201c0b41d103240c030440183c00000005d5035030844204807038618042d547c078024803065107040101294482024649504160000002c4601c0f009690f10094103100300d40ca042c00c103024600040d03204540c1d042400d40d45601d0316101c80009418ac144024086000d2031810100e0401120211111001420028444016000040c5004091030320307040c0c410780070700040c1d107000075403440c001d500916440481c50348919090404420100014100c1c1c00299400e11040040148062801c0d9111800f03e418908102c200e02202c4040d11403410030404514000501150b0b920440c1e0103000618000c203010402c655540c024001c10094180044441140600203080f600200c90000c1100100519040032014580000301358085016201180517030441101c0307040c0c42c2000d00c10202505d11910b00004241808000680f0305c0804c92114003030b2000d0054540c0700c3c3e6030381c03100c2c0b80300515000032100058500800c4c010b05800c100d0004542c60301800d004100384284668070300c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 239478489 1250 239477239 239477243
    0xe0301110f070602090a030b220210180e1e150102070312020709020d05010305010c020c0f010c020d12180807140906040b131e0203090d0323090106061407 68
    0x103520304481080d90700c16036040a401100d00903020800754409842d80c407110f00086110318261005400d1000109100c503580a40e880100c281d40d407190805650340002440d51030605007000c10620010b0040000e030b40ba0f0030f4100c004103400040500440d41e4040c03da032843c00031031144503c010b4681807005051408200c030200d005a01070b01c0180003080d90741c41c041c1c3c1159458011a030703580e41d030f442444c4103a07044200f02c802480c0d5a0001001071003000e00031225402e4061019000818040e40006c854080070381000b81000102c000320804c40d201c1c48a090705043d0800310051000c41c007004001c0101e408009001140c003000c401c0082ca2010004200060340d41c100d80565502c0141004d0045c01400100342983c415112001c000c0c00303841308a6100c8400607400b101281034a106402e0040d11480248142c407143c1c4104200043c03440080307a144415030740b40c0740206941c3c00d0300145000241c0c0da1000440401c01c840d0a0083c0e0503815404141100ca15403203a681001c120310308503100d80210040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 239479739 1250 239478489 239478521
    0x11703040807031b090e0a0221070e0a060306020c030c0d0906050d02030a14070c050d0906170c07080a090e0f010302010c1103160b07020406090501050d060b011b030c030e0301 77
    0x81c000130b1a031040100c0310f42441136a51500c6551a0740030000d1352540c5541c090180c21030003021095003404000408401d02085062201c514203560059513100941b2504c0300ba03c0d0400f02103a03114240390010f80045030020019074491310742d001030b07617100da218030444c2003e841840d045c04200c5008405100031604d0310740340c081c01c0001e2032033780d0800b07580014400540704c0d070b580c1d0b000404420490030840c0030b110f01e540e030f29110030b41900c5d0541c545180e1000d28030500980300c00401c06254006010944030280408511140e00c401524040600940c0c60003000d0368000b20f540c5070724550000031101114a010080622502c445020205100c0b0a000180c002880051110f02042c4405403491250101401701d814003002100600c014038031540060204603000200d0500794903141c003e100290081d03020411440d494040011003c441002c8024911511000201c80aa000312203046541000d12403c6c0060640e919004007076402e021011408030f40204030310420750034144070303000421100c514 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 239480989 1250 239479739 239479753
    0xd052401150804060b090f0702060c03161805041103040c090b010c12020705091305060609070f120b0a0308030117120414031633050a050f0d0509060117030408 70
    0x81c0495003000c0061007030300c95544031200d051842e15070344034462141110105012250074000300c007d080000241c214207440d01d003401404002075400c190f0b4009828282031520100b035040c0c10408151a166024941c8103103407072109040f0b104020010740c800d03480390004050007600c521400d1300300c1d64a030010900080c0101c0461000400c00c20580f00207040350300403030f0001aaa034000030580c820860b41c6145101800203400104a020040e80d50003043c1150103607041d192468006090224034105042008041d507003848a50016900002240c036018260000903a182d05017203159900c28411840d100c4040092842e65010204140c030721000b002140350300c0c051420001c3c1040c0042c00180340d0345070107544246400e150640c04540d004011802c1001c250003045030b40a8250244035051008005c19100c5e80c5083c5540b05c4119901d171219400c00c140c40f50007083c0b41c40d1040c00f668200d460300518280912001610004003913048601d1900d040441c0e030542166203459005074401d600700765200030307 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 239482239 1250 239480989 239481029
    0x303130b1801050406020c0d03050417071a041b0801020915030c09130b0a080304030308011e031a040b0a090507141503071e030203090c040c030b0d052401 68
    0x402607900001e4503031414800c10100301090342101d50a58080700c0300e80d1b00042802c04200180115441803296080401042c42c0c075454010110010841130300d0038100004401c01007000030340324513507505021800e0502919151810760024400c5641e4500e440c60403080c00038000c1e805008a940c2c0748800ba0240040440c6038400c28103541014000329075400090201c004580c940d5404e06001c041082c1010846c0300815051110310b4140781c00c000c0490300200018004203030400c202ca811124510035807a101c803440701080c8400c01007500010441d43d8144d2030540c3d060710003210140164003039250443e01d91114840c00d02110701003e802489074100c05030822030903a1404031010102400b8043e480480281c003003106855000701c8000d400304018580421910310300d0042c01d0120910b60804514604000f006260750b800e42c0c1c42582e208030349500303034010054442d0700b14610011001d007403120304921a1a1554480b00c08103650198203a020a45928007040ca618050480e404c00390502d030300030421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 239483489 1250 239482239 239482253
    0x1403091903021c090e0606030405060c0c0a1a0a06060f0207050609040914070e0105011b0209060d020411120a0204031e080c1005090f010507090b0d2c0f030313 70
    0x124505600398020b1940780fa100280d840040c560048055540c00700090402065007070600001d000710f0300070781040c01048006000041c0340b9030424804001140c440940814841c541088054003c1041e00228048068900e11410442c00b0343d61004041c4500e6890351011070f035400c03003459a07000581c050030041005083c194018440da0102800200d00a80540c5810a201e140c80f442001258000c400402c58141d000e10030a0140c2400d19140d0019039500800311501046400081e110f4500000032076815603581c02d0007862a075000d44280810b841d001d15100a03a0071404c020301d000d1800000180004820344200c0f01034a9006600700860f070b0440c200000c416a4000c02140c040070100096243c00d0713010492510b68203075203840414039141448071a420300c0041d42a11800d030b8101414000110f401c0714007075054a6450303076a5515070000c080c81c003000e03041c036001c0c4240c0790f41030a5402001d00c00c5c0c01c00c0c0c0701d14580440110307220002c0740100b5550300e00c006c594008191074a044414001182 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 239484739 1250 239483489 239483533
    0x41a1e0a02011a09060d1a0c0a020f06130803061f0801050f0910061b05121305120a02040c030209060705060414030316050f0d0c03060609050a0518060109030f08040501140309 77
    0xf0822100c00c0400000787c0882d05005643c2640191070101d800c4083e00d03410008200003092641c060070080c02d1502001001c24090240101079140c048005045034640381030080d520203415002150302d45441c41c1c0588101000c0c05031a014914042c6840098202a10480d00910400c00300f03040c81c914040c03045a800d4000d811f008604565194000c011810030480c04220f0300080c0149c980c1c9126031113020900e209213500560144440186070b00415070302140344011240c040d180445e404d41505030440081c800c8003c1d1a42c80a000f0404006000c4005581c1d032107540b1174044800008101020690f07039010440c1c0b0aa040c00c01c039151000c1c0b00d8440c0028060403a4000c1c4e0032410900420a02001c2e60038010000c00001d81d1001c00700200350307104c4003444c001c04040e200300c1c2d0001d05110104a000d40341008484141800d03801086642e4441c1c01d41000640d048a011588003806161224146c0c0c018401d141c00103c21101c400304450a1500326406900038000805442030021404510410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 239485989 1250 239484739 239484743
    0x512060109050a0e0a050109061d060402160809030d0203191d1503060118060509010305060f040203010305100b010503013005010c02010204090e12041a1e0a02011a09060d 75
    0x41c40200001c0300c0d120340d0f84960113054620b072540e1843c0b8000142c6000c50300140d1181c10700505001d000c008250000b4481c2c3d846070031242d04500959070340c0e008140070744661005c00c50882e40b400948001e10000e60040e250050040382a200d010150aa04a03624000c00203284000f0810340003075004c040c001c007070060454190090380f1902e0741100001440490308480880144a0000100480d6680c410312149103200c0d420000b0b1109030414034020000e001c0e020000341495a5800803c8890b650b44c2412002110000c00c00c0d9600d603128502951941900f0b0780c0781c6c8030141080000e411940c05101680d06072a030092425000b2003540540d051040b8110840300c0407030751983d0000c3d010804c20700034403407942016000580d0b41d602e45130031802190358562181c0000e4102801600281ca02c0008580803140c003040c9181d0b007100c4034217480c0d8240c0f190908840c05c4490303019a421540e451103016280003c05034008000058810310405901c2552845040d80402c440001813076503e480000829114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 239487239 1250 239485989 239485997
    0x509130501020a0c0b1806010918050d020106060f030218040b0d150c0f020307320102030f04020a08061501030c2304030203071a161109040b0604050702010c05120601 73
    0x414035150242260700880110000601003403400301030202c0366071841c0e08200340641d000544005c81c42c0041d04c4081c18007410061640341c030307060b40300c680f03042d004c550301d40382c01009894a0703602030000070307000b001203100380000b04007103440d080d868a01030b10945138802c1302101380f1204200300ba01040010410382030495401285a140100481c401798200e07910300040e0380300041c80d83e1140f50090f2005507401d0002003150f00401c240c200003800c00d240e04000501202181204002c81c80d1441040c034900c900310710b850f603c0801004083c0038000e820502a60003074640750031080d11100d1150b2240d074126400005a01c40e6020043c00d94860760214460240c1441d216601494440c50f211a00050115034661440049424415443c041c05203c0080c15081c10b40700302c07034100100c441038a010300e5004907950f040504000c401d2040342082d031101800000d181b0116440d080c90580f085d090203649003400340e031504000404150052083d9500b10803151995820002d188000407020080180f10324100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 239488489 1250 239487239 239487271
    0xc0d03030f090c030311120714070b0d0b0405160c030f140406031b0512040807050304030605070503160806010207050909070902040320030c0a0302101110020c06060f0108010509 78
    0x800d0301c62103045180c512400c215840b151441c28000d201659a00300d5241c40d03080602c420301c0004030a0100c41c48a035001c1d003102400f94200e00d025041640e01d0340714811800e0f000071114035152f031591004442e00811202008a074461402e40e0381500f500c14050004116105e6101c03010a001e600020001d11403451711101030001c007005c0e091150071640c4001c0c04070780c0750119420b01c020240c021401c3c080340c9107005030410b52203c071613a6003080040c1018000030400203ca6051003000e000f1100603540000c3d0034002400c050f2001011948102c403490000205403104c901c5091050020b9800b07180144d00074801641018200219410007802100440c800c001d0300098045450018000450203000e5a410012400c41e51004041c440f45e210781c0b091704400c080329129074036070f200401540e230103481c500030721040d40c00f00351041d802014401b00544104848250390745855001064102c0640d015251036403102c0003072018442c8001c401d180400c0c00d200040c012402c10910341030748400800c00406c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 239489739 1250 239488489 239488511
    0x10e161d0c0c2109041a060a054602010c0206010506090609040e030a09140102061602011401030b07030c08090c240d050a0e030702090c0a0c050f0102030106110f0c0d0303 75
    0x24100038142d000500702c07004100c5104074030f0180301e0302003034103040c0002c03090003542c2000041c0c0610500c440c80b018488042450100c210000c40602000d80b12010b8510ad449a010140c148541d8001c51280e44080c1801e85560b8961060080038588140c0b0303001490240d00304400c12a03180c008040c01ca800603401c1c000c3c0b45240d03860703000303010301c1020860256660360345131000207002040a402c206c2504e03245010b000d900d640c1c0004e98070b41c429600c0b004c10000e041d1021040740034240c0306c8010302071079610200100c05d00407211802da000d20819142004541d81c031346000d84407244111130f04421a040301e00d00611030b00380041e080000700c0240080819110503a0301080080e0050550040f115580300304101c016a1035201d95031141c2c030341c1c200950412082c0d900040c5007100043c50109000e10205500700d0310f60064230703620b03070450388070048c0c030891400a032086000790424030a40000410100c0803080501022898a011001c5180507084082c01c1c24103220417000c00f80f404030105a550003840311 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 239490989 1250 239489739 239489773
    0x120b181b0f0316060207050612041b08100c080702070e04290106030c12110313051e1006090b010203030c0310090c050a11010c0e0f030f010e161d0c0c 66
    0x31820103c0b10b0701400903814410020314116454001034042c00c010000a0180301c0d40c0480194442d42c0002c0c64034040d407a8a41c10110b81c4481e50007a41e5510a40b0345440300310100d034110301000c0c95947c0d00c0748480d41d140d460482e5128801d00c01c5004160060021030045a60001c2002c050311413051003520040711103041c03c1c1c900500b42e01400000e9620380050400c41d50000442030030005a41040c400c01d030a4411094491001904c8011408507020f0f1540130072006010082d920303600c80074208a05c40d21023014540304c161907808001d00354900b030b00104a15126100c0d601aa0106078011400c503030700c4411511140e0700190121000d040c024000280b030781d00c00c1c0285460072540b40e641d1b50321100c0c0c108026121445024010f6502d174100240041c2e025404039200d07400c610b089a90346010408000401d0402000910500300e039424050160355006001545c08402005c1881030701605680b0440c00d9280c2c0320841039035203100c5da2800400c007002603020180441c541c200c8203984000d9070f00e114401d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 239492239 1250 239490989 239491003
    0x20f0c070f08010908270301051504050a050103080403020d0609020a03030504031a070f0302460f08040210031b030e070e040c0302060307120501120b181b0f03 70
    0x111584851024452226070504035401014404028040b8101d01d54400032103000710700c41000000c160030144282c0800030345101d601c2d00d8000e4001c128a082c08090301001203603c504650050382010b01080c9000f800d44111b60480780c00400c8242402d00310782c2004071140701c500050b1415a21349103124090f1341c0b0200e00c1001140b2079124030b43c5d180c1c50352801e15180510341e1002001340c0e8810041016294000c101d0070324000d03035481c0c0160303640400140441d0f4040241102c2c2c4007500103040e8100b8207019002042203000c2d21441c04454501c980504484041d03a2450881c0011072520209006042c25078048405404d41d060101e000070701001003152074013046421000090700c5414098099100b84480ca000d01a04c044410a0385011380795595454102d210007401032100000261881d4460312a105034481c840038240302d9545c3d14030403109117902410080e103050b8100390215078840c03101c0108100850884015047c480f6550140300c0000d80c407081003e070001d80c034100d83c041c10b0f07500b84202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 239493489 1250 239492239 239492257
    0x20c030301050f06031b03060307080105011502011413020d020d02030d0c0b06010c02030a021009050a06110c090f0f070302040b0a02060a0606020a05031903060b040902030613200904020f 82
    0x1903840e58904010808024a0b00115034041e075010070600c50400c04520351940114418a807042c0c2d2603c51101081c94115a170388158425481c040010075807200707048122404d0b03051a030090060002c0c02d400c50080c0359003030f140c0e0118800000c0325040141070182d42400b00c607000902007101d4101c03d8001c2801c00b59981400d01c0000c202007294000c0000860b0703e160030603821318014400c943c070396012075680c3d410071101911500ca600080341086114041d41c1001e88000b41c0007584181d038031302c1c1c0a040f0400c000c0100b2024040c04114030854200301c0c4001d407062142141c07011664540004592075180d014148204058080001003030311906100100704c9942c4a600130026850035403004001c660390354100904542180c44c940340814000001d0b10321603244211031170040c41901005500034002544405003100010a0008451000ea4041c5200b280e05640c4080c074100311030519800c440e031203c3d08070700d01828001d050100039000300180c280000003500c014503069134101c1d011306035000b80140c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 239494739 1250 239493489 239493493
    0x212041101080c03010501020a06020702031e030a02100b01050901030902010905191701090f0813030203070b03180105090316060207020a09020307120b0f010e01051908161407060b0a0306020c 84
    0x800d100d940d000c241c10758041480e00c4018215410000005e4880200348000740150781c000c10b51805558050159403110491a0b004070010007044c5a001e890307421848240d07015009100f1140d40300c1d0100d00460094400503511640362401c010010f600a0a4180040e41040488035000c00c3ca40c4030064503e000d841c800040503c1d45180228020000c070291015030322603418121800c0015002900c418411540443e00e2512812075038452401c2000c5c43c0c2c4060b5251103000c02c00580305281c1c2c0011402100e40ca81e200420201141d041420b0f200d043e903107008a0b03030042095030311640248201519261143c0c101502d40392003900000d6000a00d9003005103400e034004280039a15411a103000c1903100b03002424440454000005050a5098002ca60500c40b0503092020b880c0e10410803203444070708084001120b084030000007055036104071680c00021480c903c9918001e40945961000030389a0503500c0d14004a40d0ba85201a040d40b4003801d4002c40c403070401000280d4240041d01c200811900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 239495989 1250 239494739 239494763
    0x100c050d050a120e3a050717040b0a030e0604050a0308070201020c06040524010f0302131b0c020f01230903120703080402010801170c090603030d0204031b1502070e0604021204 77
    0xb07205c004075041500422041c0100030000c0d6201d007141c0c84031260140f52030070004d445410703505000c0c100340c03001507111070302810018000c210b00c0b004d034000d0700300072000307980401c141c00c41c8000040d5145000e42d0040d00742e07403002c500c040c00a8880e401c038a500150a1001604008082c0d09070740c500542583e0450b5a50000c411079103048800c6620b17a00200102600c400f015407403e2140c2861000500000e4010007a10000b030b0302c13801c00c81d006021910340c10344200104a03200d00c002000d40044160803842041c0b10b075521111507200703000c44072042c13400d130800181094640c502d041c801c1d0302c500d64158040c05106690308440214401503d00c2c18000d4035540b1041c42c0901c001800304070705800c820701154422002184004000407141d0342d0050030740326035140b900e0361310000c2d01e0b5000d60415692040d0001402100f0840040c081021460b603841600f0003040d202d000440000d06124815401030f03103c188100070485c1080c00e0280c004401601c014604400f0717078540502c00310101c0701542c11007070043e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 239497239 1250 239495989 239496013
    0xf030705060a050118090503090a14090606190302130f0303020d0215010b0a120908030a0903030615170c0d0c1e03140106181211100c050d050a120e 65
    0x111400d0b6001c0d410840070089036050003801d00b02c0352403480c009001a0344d60100c2d0070400808004132602640020300102e42a070385c400c02400c0300b86100504600078003001c2e020528500305031003643d05030b4402c03440301d0800003100f000880094124408030010f182151500091a880d0715101c1c002660280c0c1c0584100f00d61218086e161a00c0b401d00d49102d42401e100401800000c40f05031640d604442c80c1c040f002c100d940d00342034040c05c00c11402400240d07001051021300e95a40e4409400c541c805d85080c000e150b5500c140c0403c11420542010201c5d141c24880c1900002d48094150700c5a001c904141c100380d1820b804a045900041e5090b000c205a0710a60b107070030040c42200441d0320303450719080c8054012002003021808040c8901c60034002403121811400e00030002c140050305111880000511035410038003c3c44403494091030040240340701c00c0c000c091003040c0134241071f50004024240c00003100022a030301c0d440341d41554108800c5900007035203291035008038418103242c0300041450700d200d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 239498489 1250 239497239 239497243
    0x230405130203070e0105060405041e050115300903050c06070504030b01081f15090e0c091308040501050a0c020915010e010f1b0203150901061809030203030612010204080f030705 78
    0x150010007a0440e10344c01041a507440c0c4080320150360040e034011401c407440044403120501d10415564001d401e010022600c01842e00050104520a035140070b2041c0707401860203640c030003075407420307291800d500480c0103c50801d13040320020503c685409890803d003000420b042c51801e9074040c002a8000500f0000c2c0403280f043caa01422414001e86150322a0342d500d5144d1464031084402600c0c0c031642d11180003080404100000c201244042c403609040c021b89030b450b922030841709489000c1c0403010801030203008885801c940d52100e142071419042c24015035039a00011046010080c602e0313800300040e2151100940180720b44c0300146000101c00b000505050b0490f01d4980c100148102030750880c991256504c171118034540d00c560305803400c90001c82d090505030034110001c068034405121520005601030001c81d408080c0c0e03860208200e9a000060382c072640400b07001030b03009002058070391030901081201c0e080500c0005140680d1061303050b050030261400d0380106d801c00b081100505c002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 239499739 1250 239498489 239498503
    0xf0901050f060f010c0c080709090c0e0108100e071d070305011401170402060c150907060c0c050603270706031406100c06090503191209020a230405130203 68
    0xa030014480380c6008000f1458084211000034100580d5000140901c2180c045540150060724240e40000d03403910703000c40c00703801491401c4a40e0301c0c1c000400990005e440001a0681c2e82450291200c00a000d000714080d09490002c000d25010741d40002551159502900c2d0b40604a072888030054640300c7e00150403900141e000d69180c1c007080c03040001a071307030110b00242ca151000074549240c2d01c45001081c0c0500441ca4212154070a100c030307031144561001c441c00d1140320a60200d42240f0340307514007110762140c6060018515028014148524588003001d168451204400b980c410001400c12034110601c0c0d511002c2560403481060011075454068842118021440e0b0b07000c43c01d058001c26464035500b83d11408100c2070380300e40010130881c4d4200c0700315907400104403900d60096404070f2140702510b81c0328001162000500701c840c9580f0f4090b41d082203400618103174240346170078841d41e66130308a50384000030140a0343d145030282ea11803040b00d0003461030010b1040c403150544107062410301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 239500989 1250 239499739 239499751
    0xc03060b04060321110d1e02070510050a1206090509011802031005060105070f060b09010905100501081803030f101a22050306090607030c030c020319090e0f090105 72
    0x700b0400144085842c00c40031100001841c0030450b11907008400445581d9100c20801d00c1070700556221444290740101150349032088101c0d81c19613000c2d415816640c864461007035903048420680e0203041c1034052006000c8111a50601159221b500a1000708685040e0072507040c155495040c0701c0d10389024464080c100340244042c2580781456000070760388441403032010f10015107440000c0c1407648510300b9560011391100c6245078242c9503241c11005802240c0340c4600542c040d00002030144203900070f290040d460341051051050400c0011100c0c1100205078401d14085503080038400c0c40104011486803141c00391126807810456418082c4003565030120034800c89040c50710340031180090844428112440c0303806004a00551030407031846065028075414042c4c0820050080c20218004d0b10801440e03504100007540ea940030b400300c031248400100160b0042c4034000c9100015000440c104801d82840c21036980c1c0e507aa00c0445031011108400e0342d851800034404502c0d03090040c0341c1c100c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 239502239 1250 239500989 239500991
    0x1c230d2102090d1b0b0301091b030c0f0c17040306020c0c010207030506010b0d090c060e040f0501060c0b0405030c030406050a0e100c0204180506070e0f040b01020606011103090d0c03060b04 83
    0x1280c0ca00055003e001e0004064680306100b401050000a2a82000c00904451311466183d40e52040c60500921500230389501024490118440c1540300b4410040015029120401c2c0781c0941c400494503180300c4c582c116280c6016505000340c0c81c0510300523100441c400c44002da90340c025000d007203040c1030040e418641551711152040c4001103022038007e05648559603a55110740c09110f0034800340246403405422042c81440c0416800d9100310681801841542c0502ca2140d5048180b8200c4500344244000241003801010025400c0e00086401c180603008503800c0040010741c0c00d00f158403a61003c0003041000808451a0b0341218071a03158034021109102112919840138003000301402c00244115500c600c000071600007001c5510216800070f08403003039803a1182015104040a9810714812000110041d0036840c190240c12015401070b4050034090b10b501005650603016141c01160b280014800700010f901d40300b8034008003a01564421002a165050401c02c40303020200c207601803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 239503489 1250 239502239 239502247
    0x6041a06010e0334060503010e101509050108060a03020907111203090a1a1005060c0a05010e16090504020a030f0c0312080f22111302030a06050f1c230d2102 69
    0x15040010780741110114038410301143c1c1d400c500c1118412050b040441172f6001310318584070259000d60418142d940070b882e940e041e42c948408004044017180310003580881c3c001c00046161380b084428465810180003203496032890700c030488030540c208445000c100e038856259807044c13200780d85400e007104500c00d031000d003a414403829502ea0312002d0301a06002d0000000d014038104001c0244004c8990884000c12001042d002c1076502e800d0040b1800108100c1355101241c07800c450302c180d40c007440c0d004101e148450301d903584000e01440303291000c4e140d100e0f48103400030210301ca60400c0c0803116080d94907003095240c409466596400003070035220071040200105000d8903145000c41c0c006c6a08050b11a0348070752403070300048414095035501080300f8008424003270080e00c142c1221059034021142c0f001d507007500d00180019280c040740c1c140b1426500c03241c840003041203010172040f0414042070817200041c00b00c0080785400384140d07040000624040c1c2c039002c44200224112041c000700b203801c0d0300d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 239504739 1250 239503489 239503499
    0xb1305010b09040f0f02060f130f05032a04021e031e090a11060409020a050903070b091e0a0b04032405070c0206180907020d020601060206041a06010e0334 68
    0x908525000017080f10700314619000a40d5900c2c07040e00c8111181c515030903a150406006a1210703880b0f44a010550362901e18003040e80e140128000445104280f0b82a24529118105000c2d4109500116401075803c000c400d00c40105010b110740002180303034031141d4070709000c140c51181d04001d40002d03501c9030418040c018020350210748041e80f00c0d080000b000c0e5101c10040090594803c0b07038000d1030040e1001940c0c1c044a6003010151060020450075140c840c0e82c0c490840b000d901c82d94507055400481080d400f4504001c400d0000302c0510040c20b030709003803500c1d400031a20070390041c0c0060380c40340c54201d4041038003d4800b00450b42401d15110620050070129000740204418001c024451305c00445c64030b805040400c520030841500800c1170140c0c0c213182c800a13403114101180103005010300f000100b0304600005405010301d0b44400948484250000030700014038010301098104000384402d1041c1d03079001c109081081562902c0401003030405000008181490480c440d8481c0c0c0d00041042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 239505989 1250 239504739 239504753
    0x8010506030109020903010e0f01060e0901020c07050112060905010308070b10061b11030114040203070b0301060903030c0f020939030f09190b10230118030b1305010b0904 75
    0x10460f100c80c0702c0540c94001c2900081e014190f0b4070b160640e41e1181010015290405400030012650780c0513401c80f0750703100c0807201400e070b11510086c14030541c041c030310030407695100b000b807810070219524000540940315600f0505880003a4004c2c5d49000c004620403007485620400c1c160041401c178440501c2ca07103481000f03424140039a500c3c2340c0e50260a00c028003408840d000400b02e1441c001c0003001007440403c11080c4284041e1000e81c040e100314140415408080801c4034140d82164032480000392950764100c07502c052080c000c403130a0010704405001070f1a403030642c0340039480e40e452511906807402c0388950b110381048181d103407801141c8080860b44a841c8110383e00444280d24a000719074074610b406191503204080400000c0070007031180300f13000081c7d245500404500e684000e040f07694150b0502c40b150b4007100103001c0000441c885c0d09545c01001c1c40b9410603400c0800c40031081d034070307150010303004c00483d12858401c100c0d03203010081050a00c501740c006102142e591140d42050785a882c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 239507239 1250 239505989 239505991
    0xb0a050f090a021b06180f06040c0e07050403050d110c0307050904061a0303030114040b0f01050a0f090f0906090501080d080a090c17100c0809100506060c0d0c030207060801050603 79
    0x180500e42c009900002003582240d04041113400008481c518102105200f441d64900034062406018450312070208480220f11180504e03000b0204007000341c14003400510070b15000c1d0102c0d0510108000010000d007060003200000115922140039100b600450982005035500c03240c1d100780c00105040c019641c1c2d100c030140e08141c20810000790348449410740721040e203c04030925894440400001b48154010031203181c4810280c40a1240030b524006011048001051036404150107006045800340320300740c04070341400b59140c440d100e9503036080d041200d41c045400030300f602500d402e8103110711100750107101d00600c2890001c040d007401c40d003001081c1d41c90280070240d003140c540500d48180141411740c400580030941181201c42d9401003196074035030b140074041450710f0801d40d401905500605440d4032810401001d03050300b01d0307070312282002800000c1150354443ca081c06030010602040103141c51906841d22407038030b120450304002e80340400d960b07c079030100440000103010680301c0809503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 239508489 1250 239507239 239507251
    0x1020606010f170408090d05030307030b030102030c03010e0a090c12170406020a12030f052e0b0d150806040b040506010e010f050108070309020409060519020f0405010c0302070305100b0a050f09 85
    0x1001d10b4945181420f40c506c120b2511550116001040c3c0050042c0032008600a0400d5201006100d500340181800e03400204c94007085130800b48010080f000003131890030b600004640d00000c1240036a540c03446240107941025070845030514206003086802d010200311150030f030301c4150806180c0703240259103d62401b030041c02410002d030112101d6000380c0100301c100881020621035845d1803054007600c12001c54410301d0450082c070102c00000340d05406c0b00300b92034001c0a814038048480c20f0320006805403903800c1000c06040030002a6194017400424000ca02c2001d805ca003504290818510304401a00200190704108d0b00400c8035404101c0d00b201110000c0c2403142c0301d07968a2806400918102002030b41182c10546074008002c201e034040c1d407103040f00320402c103001030a0f03000410490241000c90300c88100e0401060040c1d60007818410100c600c28411110000d8032907a40c2401c155072625180101074580d40d96030803d00c2c0c01c001b0030015000a80340d04c013400da210000140015005405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 239509739 1250 239508489 239508527
    0x105071101050a02070807090b040605180408090d0804091b0f09030f1401180203061003020609090604021c06030605010501050705060420060a020c04050f060d030f0e040e0c01020606010f 82
    0x4030b850f03410700070301000c2c005014041c02c3d1003040d95a1610007020f04504400c0c10710892a0603400b08080c035090002c151000c0c03c084075404103640700c0d82c60348d42682c4000081c40e4860004a640c5001403041d00060010b0400c1020100d220140b611000324920700c0008100d0500c07480300c90284030030317510583c2d500407203801c0340380d032042a81c043c107100b00c59103102d08013581d49508011100e01d89034140605e01d0083d0748244c003103504036601d0302064844800700b40402540320804200c11441898403014441e0091002400149400300300d1404005942e80032207144207064072090f00b0828800540710340c40c010082806e2441c64881903555060720b1700070041c0005e04581c239101540388003c0340800200a03000b00548021b5664400800285d6500340c901e4415120ba406d0800003080e81d64401c14281c0100e00c081d02152622515981c10340311708c100a1038450812a5407003031140c1a43d02c50054180c1c004000000d00f581e2a022400241804801007180303050240c83c49243c942e10762702c40c2802d1000051a12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 239510989 1250 239509739 239509747
    0xc0607080307030b0a030305031f120f020a2d0803030c03070503070908061911040311060c010f02130302010f08070e01030b06280f0f02060a090614040804090b010507110105 76
    0x22055005111040c2003d40000105c00302004068000000758003c0c034030b1408071800c0b1b4403040b051000207081c40c024071406100302d030700da5000070f134009481034034041c4002c0032070600c0740e01c0d08082440d400c000049160b0404000300d07000000e0806205410141461130007031459450084120102840f016041e202041f40c00030026070441c0c0f141c14400c0c0640b41000994000342032120301c0c411000300210a1014903413038040341c00704040e00c2000710780490364012030b805070701c1c0c149a080004035084403d00b6013155480303020b00404003503544024280b200380c161103000e0300c44c05c4d8000104840c0811f000d85041c45150002e012840307800c07241600d00b1100034a40420000a0031021a2950098000a101510345410454500091103c00e400011130503510344850100e880740446030f07031001c3ca10748400350b08a8004544440e02e40c2d001101040d006100218000d010151222a03050f4121030544000101280501400c3d80301d001d0350040100c24a411420f1503625110300201404654900f07050010001d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 239512239 1250 239510989 239511001
    0xf060509030109051b0307050d0c06050c03040806310201090915050d0605070f2303070504031406100603110405120f0a03030e0d03020a021b0109150e120c06070803 72
    0x14005203c81540407069401d8410614406040021803952051007801800004a00350811403124000395410410b03021113140383c030340246c3e07140d8484041400306000800c0042200071040201d140100c408668208102c418402100303600181440c50303603400309800d021040581c1e4404060b20a960300d01d8000201141c050b400405601070f03036881681c01201c008030381d20901034141d0049218044d2525405a981c1660b002100d455a20030308000c0c00150310248103200495000246510140c00c0c14440d285c907499841c3c4c02c0305c041492041c180c80c0e501c44020030030b4008180c1650310080030141000d12010640000342d44d10b500950103094080d400084422600c44420880410740c400e0f420151152032885040c000e0181080942c800c0e814454550b00200c460300c02d1080366003032005035014201c80040307856409070040301511003a040064510010072200c0e2424602c030324620311034823100c1400100c039007808101e84030481c4400041e04500c0001e081c548460b02202c0005074004000707942c0340d46003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 239513489 1250 239512239 239512241
    0x10020a0e1504150c120302090d110a0b030a0c020d030204120b04052e050105030d0e190e1602120705030a050703030f02030a0e0c030f0d0c030221030106110303010f0605090301 77
    0x9900c8006031100c540c520044070764104d04268115802503107804100c96644d101507099210f00ca2903141c2010901400d400880c4c0811000c0b00c28001c004c1c0060100795660710746c4011038005a600780c0c58150340d5030b007100b1420b40412003408611828242035040034035084020042c91180340300075281c0e0018000190070854184010a5071101602d00100f05050600d40740c1d001c1d078401c00a0701c243c149400300208080c900020b80d07410380a440d907640c050b03c3c0c5c04070040c8260305020901600c50a01d41d030782c010654030001c0480034030030140e030b0000e46501c0d06560402071138001019006c2804800405c1b24102165012040700c0740c04015040caa9a82c2140e0b1400720001c0c0704400d42c1d4940c4501c08024031000b8a43d582001042d4554a4100c401c000038403410192241401d8800c500703590700c103100341c841e070702c0c02510700100c1a402401031f601d03101e007500b07002c46900168600c240200400000148000e030782000f2460181031401000f1805c45d810300c040040d495840d0b0203508103004000c101d1102554007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 239514739 1250 239513489 239513497
    0x7050c1606030e070b0702150a023f0403020927070e04021e18131b030b0c03090606010302030a06030503070c0e0a0209010509060a020106030203070e0910020a0e15 72
    0x101031030404400d941c0340300003401880c001c000044640580b103400a44161940141e80841e90002c01c5114030b64901507000c40b1550080c0040400d500075201550140803c5080381c0083c00360480c142840c40c80066448038050700c180c002c031480c05c0d00611090000d81c40f802c114aa00541c1201c95101c1c1070100ca404000390150060388451501c5014400b040080d01c20000b540030368800d03100294084050444140481c20602c0c42c143c0201c030102c2d09005082a0096454104848450081c00e1444c241c83d1901d140440840c0c0088249402d0f40400402011000c0c1030343c0011103101040c1542880c0c8511501c4010140c04141003680100100341b01503d5580007500840d800303801c880e0340b2092740c980401a000d052080700c055105840000e21140994000c0701c2002d4816540c20b850130722807004009541d00040745800456581d0b003c0840140c40420084000e410b52888109591174440d41540c9440821a4415a00b6005000003d40a50003440c180759803003013110441d00400c0828403101003401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 239515989 1250 239514739 239514763
    0x20a0c0602010e0111090f0405040c05120a11010f020706030903260a0b060901020a0602070618140d030204030b01181413020a0e01060212030417040303031e09020907050c 75
    0x88810005206901580500c500003043c0d4024404829a4003001805024400a10b03402c05d089040000135442d050303000680c80780c800c1c0407500806449102061100c040c410180761103600c66101c040500407250b90b40c4868100902e0440030142803088003d4640455105034400e06481e550030504160003041c0c1a51a0f4100449514600705017010041d82e500003554081811840c000c002100303828144112030200f00c040c0c004240e400ca00303075502e100175488040c059034000c0d43c0300c1c44071041c0c1c0c003417000d03c000c00c902418014407601410080c9078140b0148090390014944104801c00005003910303025411110307605c085817041d46110b400301c0302414100032145101d032201020040c09900c225461880f080c000e90b101e011050300c503c04049040f000703020310005a40101f55060000f40c101000b1507015100751109800e441d494202e85006401c01d0304210046178540081c009010706424a56181d034038181014407840c1040d03008078100000207000401081000241000081420402000024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 239517239 1250 239515989 239516003
    0x1503150204031b170a050d0e010210020705010b1306050d03031802030d030e0c090c1204030504180504021c1203050903091e031606020d0e01350106050a14030601020a 73
    0x4141c0c610590b002080e01030001190b0503184c89001c00340c000a6150311103030340031005080068400d0303410741e1415000042541188a4260702114800c00e81c00030300120742c440c00000c80c0c075001d464100001011031244602103985880400c0003280c3c1c0d18219109441d03050b080c00203042c0500200b94880101d001d002941600c5510701c411415035240d80810a0300081c00300303450340440c0b10b80402240c0384c4190b4884201321814000c0030600841c1440854016120f82045440c2c00c0d41c4c0c189c1d00e640403455002d4235005035519001c000541c2400a0600c06d4a80080c800c10345845003507549020b62240900c0a608040e5214000f400001d17080003101c500d0b24004161511811240600b0941ca4400c0c0c8815030003801707007101002d140d9024500500c1030f100d55030081c207061108040100ea01c0c07081c0754a264100580c81c021808070b0b01060ba01ea200d41d10b10305004800c1c5040322030719404411410385c0090104901000403850569108070b0700c044803071444420302d0b030380c0d203039000100c0c030f8000c41140c00380c050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 239518489 1250 239517239 239517263
    0x30a1208070c02120a02040f0b060409150510020106090c0507021804021203040306090203010f050907030f03050d0203090606030d1d01030518010c0c210f2016030309050301150315020403 82
    0x44c2e90000b02011841d1003160140b02054100c2022030071354002210041d0450014442031141e9155a0031100c80c2d1451845045641961400001e07003058001c840f48001d80d6584009110a208900460100428500307090b840d017026980411041601c907280800584e2040001c6801c659030250904124000340d0102ca8859843c0d050a8000302444c05003248030751300c2c02384800ca402845006a41c8211714440103000001c1c50350700e61081d0300c40038080c01c408001c003c01030b00801625600c051401203115030000c28140c034044003030600e04406140762505000304c89030002c03600c0003101010308200a00307180c003052035102c0307817003034101c000b04640802003039401d1240c0181c3d465030001c52044211302030b8440403994540d001e807540d1403685c08281400061801c07d014600307180620034004141404200038001e503911900c1150a104a01c1e540f1880554002001c105150380119610041d290440080006001c440145103298602784801400540b180352600160031044d4140d80046401070701000071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 239519739 1250 239518489 239518519
    0x1060e010219060f0b04020c010e070f12030c05010b03030301090b131406040c020f0d03051009201b011515020c03030306040e070306060b031b0a0c02040203060a030804090c0e030a1208070c02 84
    0x1806400ae81000288201e402c0040c140300910094002c582000f29166140062514100c4219041650a48103903481e600c41c005d094800b0801180240255400000c0c8500c4503410081c540664501e980c3d11a41400000d038803401c1c0b46508a50400021a800122200604400d07414104404500001030049082103159141c26410aa00c10003107042200801c5881d05004c4041300d0300c81180c2082607603038502e080c03801d0740c0444c014101e22001b40701c9007901c0d0020280003030a4410525003210815082c001c100700c000c14001c51401808460300141045441e80b4000c00e9882c04001d2440d48110388030040d035003001c2c0c020b1100c030740a150403800c280446038903004e032640c0360392081e1906c2c400344060003514410300d90340c1e1003554407075401c558401c482440c854080002a40026140a6211240074400400104c811005000425458401084003011040c01521001d002018176000360042c141590004486e41368022044a0a0500000c961a00300040380c4c6000c61240080d0054200801c1c0c0003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 239520989 1250 239519739 239519741
    0x180c24030c0405090105060a080106050f0c1e060a06080a02090a020f120919050604030c020616060f06080105071709070513090209013f051501060e010219060f0b04020c01 75
    0x183c480a54aa0510782d0380c6a0038000d062103410714010004105c1d200510010744118018212405050707000e500340743d0507016480c03c009a180e086051a40856503d1355041003d114180c0d0103000000d08002c1c407483c0001d0181c44000600009100340707a59400a400b03841181d043c7c030f44c00c590343c85120f502e5810a61001c3d2800d10256240c2025105082c030303428518a0108900484543c04000b41c4070fa41c8540d0340503100300d0000f11040f42c0c45441071110890020008401006040c000c0102041c600c070381d0500c150460308141c10042d000e904150400940980141d02d102d20807032100c02d10503466564620040c10b1039aa07401a5a010507443c1100c80344540c103030003100c0303600d0003141c4016842c2d0f84da003480c4050700703c0d20200c944540140c070420400340c128a40e668a07081c42d0040d41104410282d03441d039003492148029054a818090300510002d41e002d4040c1c42c0c601420700003440300000821440306c001e030403480020071164417406020703036115550300310b640c4e4250090000c2d52500e115407001d034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 239522239 1250 239520989 239520997
    0x60e01030c0e1b0319020a1814031c0504050d110306091513020a030215120901051b0304022103040602150103080a080903120108030a08180c24030c 65
    0x2441d01d020712040401c0718410025464018281010382e40c0003402d4900c40d001d202d400c02810000f8030300141700e0601101105000402c561034440c0d07100c620b8103d884518046c82038194026440c07400f0003500c1c00d805610f0000b64044003480002d0050b0740519031070005c80311482240c12068220125554080c00c0281d50f0400c3e8000c000d04400b070310031680e04d16009568a0b83d41c1d1a8a0131500ba861010403070042d0801c0803080c0c421700191030421141e4032a00895a5007058500d03001114800013080230321410700521468209007c840240030b40d0502a140d40e00c00039810241700d0307480c08000085400c41d503410041001280749080145462120058590b03165081803080c3c9002d409450048517100307400441c054141d0794000015800c1102e11034040742c50002c0180074203502c3c40100b1000c403003842d40c0d4009500911343c240c011a65030055010081007080d0107440241c1d0300e00001d0078404444404078004101c4036003554085507183c0788984801c4c0543c10070425669006000082c0500050224014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 239523489 1250 239522239 239522243
    0x20910090f1a040c020c2403090c0f1804020f060c01091203320c1c0204050a0506030f1501210209030609030c060103030302031f080a06050a180321060e0103 69
    0x4100b0704038030042800240c814410001c4016000410124540e103841d807000154000ca8130821418051100c441e12a10b0344181c0c0c210f952130380030444c072001e545071504103158845402d590341d80340200034455a484103200688000e00c607019900c18078030b017500c46000740e03406159004002d002e84096810405032086024a084000a00300403240d03100505145420b207080208441d141c00304c101c05d00c41680100310203401c1101c0d400c404c00c404608260103141200c0004003036000183daaa2800f4100b050071083c580c82179024050602c00c01805083c501c011a510000800b4085588800d00300101d410101a074601e044011602d095042c441025074041c194840058044034040c0e1aa1036160780d8078003601240e544154010300061001a03c01d0300a580c01501c8a400c0d01060b8213031501e91008101c643c3c209c418260b000d00d08a20506c00c1c40e005464101021070002c10a07550701451011102e00d91050290522841000380484a040803014810354003007c4410031003c0d8550700c2c00c100b000070a10003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 239524739 1250 239523489 239523521
    0xc02012a09050a0b07080306061216030e07050f040207050a020a23040203010e221a040b0f0c04150c1e02010215060102060a1a1807090b0c0a020910090f 67
    0xc08505400d02d025a83c0c2a00c40295443e0700b840180da03600d402e03a0740000c03e141e41000d0305210740318150491058150042c600008425194209064018106c4582c8500110b095020000801494481c0c075440c0c040190180e4002d0303982c12160901500d01000010003e4002d40020360010304003504c8200d101f10b60030400e1040e5280e44078602044240e00080c0600201818980045444a10080f5503080c01a19243c241440c0312860744486032103000a02d90140410500420042040101e00d0016031180d00c02134014040d050120040b101c0c3e02590096103a200000034100d506680100300307080c2080ea01c605040307141076101e4040390000e40c40c160220f01603c190014281500ea5008101d84202e9060380104240da031011180c0024114407200700e10514042010b2003610780315800c440c1c2c40c02030043c3d0304a17502c0c203007110000d184444a9100c001e80c3c110900c10700e408000f001c00e1985800780c048400f42c51131f8450030390f0100b03404050b0340441c00e140e29022002030112a10741141401506e0119 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 239525989 1250 239524739 239524757
    0x2010b03010608070308121003080d050f180c10030b0307090f0b06040303080f070c0b04110a060207050603040b10170d12020301140d030e030312190c020706030c02012a 74
    0x40042d90740301c1c4c6000041040c1d4040c0320150714200000c003560351140d0002100c411041c1c0da6105c0d10b003154004030201c04000d454030200000341d40c5c0100d5458000441c5100074203409584503032a41c581d0300208039948101245924000000d1080c1c0180c0d4258400800b5100340d10b81c2d88080c00020f158a880944915051800500407032070981e058400f12509900c0d034078900c3d81d0717000900d4081640144000c0078403160000a40c0071400511105214901c01c00c41d8841490090041190825480d4404011544050303020f02880d07c0f5401a42c0c0c1155006800b40c1d020f03110011112981a05901b01072000e01095200d04103000000411103003a40c1c03a520b803450402020003141081c0d01c805d000f02440301c402a0310342c0200307061405113640024041c0c0b41210741c21a00800282c21030f88030340700202081130f2010030f0102403283c40f25000d18403088964100107400190401944640c614413416040c1030b6241a05403920f8000c2d0081703a1009214070b4002c0900071240720b035880015078003440f500094034a90b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 239527239 1250 239525989 239525999
    0x601060509150f13030f02030c09010501050706021e1309060803070f14010f020d020702011106040b0112030c0c180506030f0c0613090612031b0f0b0a1b02010b030106 73
    0x401c8841900010b40180722034980c800321088a070303011203442601d4603410072011015200000300d900181d0700c40c481900749450180100340ca404240711540d80f04038134000040004c0d0ba00241112100342e8481000358651440030682d80c1880c2d00c21030106484500003a0720750070040081d81403c00c1d00d01184081018503120008141c0e28040c280e00103001d2038511a0050114500e03c0003a00c5040d82c540000c5405031030720041c101642c1000308002055900402c1d60821982c00000120702c40b41010020a01468181c6500c05c4590040c0f00700c590314414120b04400b4144030705223105a50342c1022040300e040391385844610511215800c2d103d070103407400b00404c546113030124400b503942894800401c2e416444104010590344662203008969660480024070100640509001044001c09058004034142400340c0031207050090103009020503040240003030007505103401d100b80c20005180281da50020803030b0082044c0d0304140b0340740c0c0c0400694088a54150000700e00300000760f00078808a9030710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 239528489 1250 239527239 239527247
    0x20030a0912030614042c03040602010c05160b060d0b090312010b03040f1103250e0601090803031506120a0504030f140d0506031203040c03030914031c022a03060106 72
    0x34024414032020f1200e504082c3d19042d040000051010185a810410071103501c86c07600c0342e60381c1000350300d402c0802c1c00c01c1402d40a1003890a583c166080142c50b08000700c09040390300c903024400502c0441c1c08008a4441e8551645004031071794004442140760a11104507680c982004051900c04aa10700001c50b003e020300082da40107a91201c00f050000345141c0d194940c4281c444080d87e010310601091049411a110a00ca502d40521010081c6141005e0035070080000040c03030035042c0103051038100b00840b030010807207034800c100002c02804d01000c140000d8452094004c0905c0e20050300c0d0a2020040c01648103c0c0558801c0d00c8517420b5032101001a43c44614810212007210070510504055800a8011541c04900203069540008141c0c8403400740b6001610103440d8021070800500400d90414858130207001040c40c8280c1000710400080d40e940750034003415001e41800d01040998030b000b00303c41070020410003440400300f51a80e11220300d00c5100c02c40b451003072042c2c40001541c00c0c02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 239529739 1250 239528489 239528501
    0x120f0b070c08030f040203011e09061107080a030e030714061905060f0d02030307050313090b0409080d1d0601090c1b0308070503090a05031603020d08060f0420030a091203 75
    0x2001c6090ba00715501e003641c8040401d40140f09030b17019502c800d5015016040846c240c00f422400400c0041c4540b40341c24144211200e00d41d0980d5046010006c1c2c2002c140b00c14180d6540070301d686030100d090031103843e0072800c5020724180100b13103001d0140c42585d039520201d041c52080030301d20000030010f1901d00c0b1080c15034105541e80d5420042544483e0014240f44640d0b030389003400581106e260030025501e180c60766102c409444001604650b05003c44101c0c3d01454000c00b0f0300b251309211864403512243c00711701c07940c041c0403401580d814091843e080c0107000811841311440c2601c0d440d40e901c00340c46020301207080e60306c4001039a003003140180082c078242c260304c000d13015601d2032145c1e500c12205503150307840905030450b584101100c5078001030080008188550708081000514030ba00c0c034000c1d00e0303c0400703012031060203c802c040090380d8548659a280700d0038101c501107524100403d0024010601d082a103040880020400020701303416046040703580d1082d90003250380700102100314201c1e09 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 239530989 1250 239529739 239529743
    0x40305010f0c1209110d03020f0f060f0f070c0507030804051311070609021201020a020109140303070f0e0609090c03010509090a03090501030b0f03160f0609120f030504120f0b070c 79
    0x80c03803c15a0f00c1101d81d8010700015200302e20b500c1d060711110300041c4080c41e45000c00c40040e880140e0f01a2203150500034141c602c16924010499420456180c0740c0d940c0005000403442500c030307030000744170318803440741840c4064100c41a03403c001d0b02c0c0e04101728180c1c00340c080e00d401070350f501c8081460105984a0b50203035012081c8064180003d0f603685030050b0501e4034060340d02004504817001c00c86028801484494203d8000080d200c040c0e19111003102100404401d01c0d4009008010800d50003100700b0080301d42628000640b02c01c2000015414005e174150990800d02c94000c205002c0341100003181a50400c99440301c06954500b02030703030350740301200e001000a040791208100c1035001e0780140900c0c1400070b026810241c070030000f2a14004080c0c1100050080b0354000b0807800c07103654500c6000e0180d91030444c41c1c90782030414100c21208049030081065055940b9031007458031a10944016203a00752074884100314500f0040c10384080c0741c0090704c070b132003100010410050044a043c4c4000e5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 239532239 1250 239530989 239530997
    0x220803040302150c1e13030b1029120c19081909020607150b060d020a0f020601061b0c0b03010608010807050108060a120203100e030d150f030f080f0301030305040305010f0c 76
    0x80809071040810b50055407000c2901c58501b05e0100c00a00e00e001040d1003118030140110b1060f103040b6420401c0c0c5e00005100c032100d00030f060b80c1030740c040c142c2040b100d03045800c2c180651247c03504c81c8109428414001100a5100340c05503014460360300c50000c0d4003460380ca0000c40096114400c554003120744004e40294880f038100518000158240241e00042e5211400041c00b280000041400f0742e001921010050790b00250700201e0641091403000000c1c0d151005010030740c1040310152080142100c4403045100c014201400c100102001501038000408459101c1d42d41d00e0300941402c100380600341080c040c0310800316803544604041449220300071310744641d0f030303140a0740807904185015080e0307018000d40082200314006801031a400c100c400c001950783e20544071215040390390720121188036540d51070381003084070400c1001d081540d8002160320754002035807030641084e01c40c905c810ba101c0d14002c0000403d1580020140040300d000340000d0103424003c0b000304c0c044881d01d00400004c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 239533489 1250 239532239 239532277
    0x30f06060504050f121c030e1603140c040f05011d060a0911070813030201261605070516051309050a060c02030705060f010f060e0d03110307021e041d06220803040302150c 75
    0x2007440c0100c0340c040c041005003560b681010504c00306058ec0c0d42d20391321601041c1c640004000c0781140400011703859000e0110380c1d50a003003880006002a400e449048011512000c072140100788600403036a0b12503002c101940d54a01025260359a0021440144d000c160081004030010b803cfd40300b4150b0314102c1d802481820740c0c6124220040751071840e082c5081110910030800004c0e000c00c00b0000d112241c2400e0201030385804101f240310a00b50001e040e01a00f4051036500003000000c0682d00c440c0c0c000400b141401040c0c800300d165000354a400303000c4d44142424010041540d80c2d215050f0350810041602d046d1300c45da0155500510360f003c0ca6040024003888001181c840d48101c0c9025084c0d20540c0d15112041d000181a810740320760203510003803149072601c4c030352038148030703c07190b090300d110790007103c024041d95503500d90000034030780150001c8a990303003021100e4031101861030941c00f0026940300d0070141002940c45030513071501008001030303c020481361010441503860544030f0055100076 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 239534739 1250 239533489 239533493
    0x40b0c060f2206090c080307030e03010501090c02150c0705100e1504051e010f020406080108190302150a020d02070305030406052202041d1903030f06060504050f121c030e1603 77
    0x180640c01d41079600c0d04d1584408038240e8018002000b00900a44d102b140194120301058210340303041c2d00005060f4070342210102c9103a0089940c0007051050100d86216541d11031a00e9594410240f00030600d0190000c040015001c682c483d1002010580c11a03950782c3c0c90710900d0000d0401610054220341c01000c003101481e01c048417046510030a03000104401c1090305520040ea0095040100032a050b04c0061208100420102010080b062900301220031285ca010f9298101c0d400705020403002c2c1d0000426580341d9404a072803038226981c1c00c6649407054140208150000d5400701c49050514001c1072681094140da10b031140b80b048404402c81c0000ea08010040c008080f10314400c1000000744031410b68240002040b1071004020300c070000e0010f10b4003c2c03c886148212003074041c81c01d4010301ca0940d109060b20107882d4140c0d10080a9508940003400e031203010141c110305e502c508000030b07401009032482c001c0003000e661410300c640300c00905515200c500c2c800794001110307901801000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 239535989 1250 239534739 239534741
    0x1051e0c0f070605191d1c061a1c0c120c080601030303091a0105101101090b09030a090603050c0304020607110306040c051905030303040210140f0403150b010c17040b0c060f2206 78
    0xc114000c8807c1500c0b241d0250b520700c3c0540d842d003a856000f8003070001e401511428091410b0b1448100700000c2003490030681d80d2241d80081e03e0145c1c041d424003940250082008000c001c2015003102000c5030019030352460020041c11140008480c0c10020302080d1034412a5148114142d400081884190180c11003040350118441c0014100941d00e5603030740400700c6e458091003030203031001402843da581d050303610144c00d00c2080e5000204062406d01000b540c0c402e0481520340040e13040b00e65556455060030f050041c0032002d101c5a62602600302440100045228800201c480c10355501d0900054044198210b0481c1d02c240784d017607001000007070014900f00408600c1c03115141842c0c1d4160038100401180c1e07400c0b4103007000381500c0014060060000101005004800c03030001445004c8000c000248049001c09009280401c0700d00400b200c0c8078054241d4029041c1d40030550b4071741c0829445180c0c0c0d803400b521070101d90440c00b8013080e59a0700040740491000300040401c1c525880304d0303031140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 239537239 1250 239535989 239536009
    0x1b0105030a0b0d0c060305060a0f0509072a020123030c0d1803080f100302030a020909010e101a040506091303091205030c070501051e0c0f070605191d 66
    0x101075a030342c9180001c9030750385503901c0e208454003d041e40400039050020290446001400d41481206029402c104124006144005035042601d0300c1c1140cde210600c007580c40001d080d440b000300140d444041d0000c608011240546a8000d90364510f0203070b40407a58510444080c00c1c291070524080001440300d465070300c0200140d40b4286400511589005550710005003a0002100051040020f1003420002101c010f500311030182129140c4d5403031a070000ba5a4948030b44000d00400c4010009499681e0a600400f009042401a591810b90f070605050080c602079a0044416041600410550400c1c2c42101e1003088040d045200d1500c801041c403e241001800032020480e00c0c80d0301051040c0219942d4a07150f100f200110340390103940d00356905182c0260411410004280400c0040340c951481c3d610750b4940445030b295423040e43e05001c504124458420122512503032100113401a448401080c0008038003070a0718032048000c60844d0700c0c090502701040c629541160301e60306450428081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 239538489 1250 239537239 239537251
    0xa05041e03121205060405150d060e0601060c15050903041a041d090105181209040b0307170708030f181804080a09080c0a0909030210060306021b1b010503 68
    0x1021032556951111050201480e114001821070483c441ca4000d041c0a61604004e04890521691404402c45462166019591807241200c0c12041c030a001c01036100c180c807258040c080c0c0d130721581c42e0380e405444d015003000c0880b0b40301c41e4031140d000c1964451160314040c01252002d50311303051a02d001e9201800c0c001c0c0f043c0501032020000000d003401d1014180341440d05e6800d0309069481c05421050031140000c254284010050703005c06030380b40c0041507100520607a8200c0e252106203804c00b0600601107440420780510900801041000074003140f040030303080d00c1080f520400d2725101655102d01501054101101081c4144802144504010301c42410003400c200126404414136118200e4252001d9074013010001c0d01040a80d441640d8001825520300100b01d600040f4003c02e060300800e1107004071095490700c8500030984240005000244411000d00c0780c0782c1c403401e01800a60001083c464020010140410030200105020100398000900c0c034035240b000c0401507035a68002012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 239539739 1250 239538489 239538539
    0xf040224040906062a080c07030f08090f01300b1905010e0406030201050d050a0912020304090c0906120b0402093601030c12020d060203011502120a0504 67
    0xc40c5400c0c10032a0301500c000c04001001141d09450030001408482100400c00c024525180e218801217030008802c8182c2940070542d29070307070140c1110490074410540c0008007620054107603d401c3c440d5420150010700c0c01210000d9944100c00700558a00c4e4002e0020b1071800c404080d41e0f03400802d080d80007041503c1e41d010200b13500c0a1540003902003090520000c9840041e075000b03103c0d950740300e5503118406c0000d41c0c2c1040030398110340001e05503004082e400982c141e25800051000c1980344c02c00f081090380000766070540481c11074042e482c0d07003041c082d26031558078099500c040644503000003012259680c554a40051004c03e81c680030f4070f400a007058119408000d41e4440c8c1d01c0c0c1100380c0d40001c07065101d4200c01c1d64502c06450b54410080c11000b82440c510b0010300124160320705d403604891461048800280303092010900031180c49201030101ca00c08400020b05100300032a4036510a0b45a00340c41c10100005070b0440ca0f4082c60803034030001902400103106029400506914044001d20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 239540989 1250 239539739 239539789
    0x60f0406030503030f152103090a03030908010e1f02072109031a0c09120106050604030c0302030606010c0506012d0305011d07080307030f110105090c100302030f0402 73
    0x10a06980d4150310440e415030000007040300c1440081100e80d0064481406000c01152010004018181c42003030b0788010303035000c914100740c41010022200c940c10003405000c05107907603040190101c10544240601e84d4249901e03154808008556004084041e4001c90110f0111005020094011010880e4441c1181e250380b0983d0322515001d03040c4000d50703580c40c0c0d40c0c1030943c41c1019020090403d1403001262910911a00f6000300d1309031600000d041da0102155040d0320740c8103025210310f03440250488030006d8048240a6540400c200307807802034003195801e480f65001140c012a01580242c041d40028006000513022031188105008108030202c65040b0380f21104180000310f5401151140c0d90307844040c803540841c12803444942580b43c09400d030286081006501c1c0d100c1c0101c02400c1002c5ca281e062442c45c081d840d00e48945039038030001c0215140040c91540d5a41d0052070084c4904264515034644902c240203c9110300c1c1c0550190700c5540755a803d200d08808240019140005248 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 239542239 1250 239540989 239541019
    0x2a0304031d032a01020a020906041116110414060a0b030907080f1b060a17070504080d11070b16110612100e01050108071704050313033f030506 63
    0x8900d1607060322141ea0342a0800042c60788540d0a40001483e41c1950041310090002d651022400ca40c8200f0985006c0b5030114003d0121115210300100c14102002d441c0400003442886441e040000100380d800700010007400d081d50102000485110381d11011451341030040398651000356812002580894100030b0311109420704144004008a401c0d0b80040c91080b440f0525821428081d48191134491610b10340b070000810544030420303802060038500000c102540d2181c0c2c229001040c0c402c0c00c0c0d90380500b0491004081c207000890840492007071f204c0118581807200212130765003605403045003043c02296901c080e5081c900702d81c15408001804001c81d580c0c558a505841094059218040d050034004100603041060b00f0060400c0390a0003000302c0315410626040107400103207014105540ca5103005032843c440d0000b2000050b9818038000108400d8020101c0e2940b02060103003040e0b039a50040703e0000c443e00e07008498071032880d01040242d5000307600441d0841400380c200c42d0842d1442e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 239543489 1250 239542239 239542243
    0x4020d0507120818060c0303070810030212010203071206050105120402040f02030c0a031b0504051c140304050a0510090501051b010204030c090e06040b07050c1006080102032a0304031d03 82
    0x14640c2960f071000000f503100007000c048040140494011910641800380a031411540d9000040c00310051250740e801007006a038504556100450f401003c0d43c80e840c01c902213244c080d400950340c29011a1480c10030490b1100140102415124182d480380d080150b20403203a550030001800580e0002e41d581003040d45540c2c4c81c00158801c1e055540740580c3e07019400d03002000c449100401c01d81e1480c041041c44031240d031100440d400c0f200704452b42c03d00c094041c180c600454280810041c40d8010403460410b8081c07011001e00115901111489400c694540520114002200c0b0003000514040d8061089600a40c05886281543c882c0b01d04200b601812042c03c990154109840014860804100c01040703400b4404c41d007284c80b806410941841d41d980c0000040c0500040c1c14814041950340b8620750070402030b2207480c04a00c041c00501d99480d0020b001754003e40d42403022403111080306105642e104c905c4440420a28000d80c84c680c1d035510102c441c00c1202d072041c08040700b01c0003000c0c003941c0d007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 239544739 1250 239543489 239543519
    0x409031404140913110f01021c1116050d170d1e0c031a0f0607200f0a0f1806090507030c0e040c05090f01050c1203070206010608090604020d0507 64
    0x160340d803046103030348030b9400704002c0400c024004d80d0552482001000090b804101c0f01505d032209403040c5600150410060f8101100c440f032400c04d410b40780380c40c03940d141d0b4006c00c070400c1d05000b8001d840c01070400c1c1c88800c91940a5024064000c40c03510b03034000009105003045001d0b400420704041c2003c1c50541c0309019a0300c2882c038103400346a440d1001c603218489201d170745c0c0269074034201000188125520b9188200e8031660070307031043c0000032002c20142c884030202e41503c2da0080d031212119000c0355070406c02101c00a006409001c092103490200e0800c1e01c601826146840682c062641c03030841c200c10034089602c0c25070451138480c440000d00c0c40d460b018103801540310380c50200b440c82400c0e400508500010303a441d40704905044500c20740301d40141c215000b101e4142c0d038082841710b03604016100b620408d03c0703944442c8600c401440000707181c00d0181d8040d035415030079101240d03a50402281c0144050342d0704a0780b504240045401071502e0803100c200e480c440c0c416980300742d0390340d11116803a00d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 239545989 1250 239544739 239544749
    0x22030b01080a0605010f03030c02010f18080109060b04111e160305091005092d030d110c1801121b090b040b03030c03030708090c0319031107140409031404 68
    0x700c8042c041c01008070b58003031319001d01960500d48800a256807030007042c81c01d072603a000e8140001c0e80f80144c045442a0141075003a04201c0002a40c26554000d903070003080c103031000355601850000070308003030300d014001c1c0304641594081d0340f4180744071204049980c10001003030845281d010002d6604000600340510501c5009480e1661645100b4003031203100311400c1c00d0301007045010040380a02d0b9603110122071940d910b204c2c1c2c001001a491040700c01d05a500d44445070f161142d10402c08507a644610520303240744660066690080e0340005019502d18110144241802ea00005005248540358030a03c0a80160807440c0c461a54910289a0240f107810410070942c0b60a660002820603005001e040a0260021440c0020101c806501da01000e04980d080101c504089441101c0c204a01110500000c00750b8022040491012034400c1590000f00e0104000110040c000c81003c651441182c00c0704040f85518406401004000e00715000300b2002c0c041441d1809a440c401000a080034003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 239547239 1250 239545989 239545993
    0x1218121b06020720060f0d02132403020c0a11040b10030b010f08150603040c03080f070b0604020a0206010b13080708100617030a03231003020405130822030b0108 71
    0x100c4141020b00c104e250b0314900465401d602085a015034503075004403070b030008010900540b9030603682c500d1400780c4110301c80030710f0a003060400490003441d010404981c0e8510b59110b071140000b059002d40c00d80c0640301c050202c0da00300182e200d01180080b4015042c200c8024000030700440341e00c001a0303152405481c003200195540f8000c03440d07942c12141d21821209282440e1805141408002092849a90043c1e0144801001040400004030351210256501c000344589504031010803000713503008803006036141c0c0403220124213a1b04152080310a40e03222580503010f1030b8280350010b01e50b41d101140c003400d04144c40f1000242070805001d81c001910160340a005188251204541592070542203800041910000402c100f500001191543e0b0004e08002c03640c2c080300803005054960041034072080ca9055402c10030702c1141c020b1a0030a50744219001c10040d281c800b000d150900c2072040080c8064000c1249440500000d00081d0441003811030b00a20141c59999030242d901d400e0388186000d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 239548489 1250 239547239 239547247
    0x81f02070317150102010e0111160305040e0c0c1e1504080c0a0302060f0f070903110a03061d0111030118050c090406060c0b0906070c02040509010b06030106020a031218121b0602 78
    0x19a82801420310094500c1c7c001e10a000c100b1442c03815030b00c110000b260b0310300c4d014031702c040406004105450003081b420a111030140350020403200340d035100c603c1020450003042c7c440e0f49000320a4160213101600c500050448000b6015070310720202014000b515081003e01482d5060401044542481840b81e805822030b0b09241c0c0d04460111700c0038102c000241001c03810001816030002400c01101c1c1c07c085440c10341090031010940151858101424050510f080d0790981002c20000074903180302c40008000c1202520b00b44009400203000348002c28109140d000c10050913500543d030000d1a1030221803400c141540010111001c3e039000c680419681890501070000800010350700a103400d001d0801c614107804010301c3d007644800300070710895659011503164402584603032108a80544540d0340c030f50312060040d5591040420481c00105c421100c11402c000c00d0007426000090344188544c404420742c2c542500c0302c2528088010040c0e1695020007490540780c0e5848410b00800c00107982d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 239549739 1250 239548489 239548531
    0x70201080a020708032e14090603071505090406050303130e0901020a09090504150c120609060e1b0c0304030807060b01051e0d14040615081f02070317 66
    0x311000100050350700ca106004a402142e100002c80ba400000407492840040b11912145261062040b04960700751600720b01241c14610b919081f40961000c44030a080c60f83c911042695481190240307102080382c03000f500c4001ca0188002c0d00c8804001000800c0781a12280402d103142c028691007040b4080e80c4000b046094442c865441c1c000038a42d009514003050048054281c604501c25801c1c0c03255100c0004060056080b4031906040000205200469401c3c5008045801002c1070342021850582c0c0002e12819038400c07401240c007041c1d000140b60313496841d494040e807001078040742c081804001280141c44144000d1020714440d00c2540c0d180c0b800c40c00e2107411070f1841203000e81030002c02c0144098403100c4031041e4031105a1150a20b0b642c00300f07442d004010b4400b1421107c08400200240410040b60303812030180c13000114000c08aa80d81c0302c0e407903503407503611451125803107844540c9a0b460141640040c07801034040d0034030107030100150080148480c0c003110034121003a0311856213a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 239550989 1250 239549739 239549747
    0x150e10051207030b0f2d0f060103060303090b0708070b0c07060c080603030304170c030c010e010f09031425061a06090f0409020f0306040c031a010f0e07140f070201 72
    0x4040421030041080c542513990700703001a440a0070301d460703a20400000a484968800300700140b940210803041924040040b0412926020383c0e2520050507071b88001791141d44240310310401c598141da03440d041189440b8030700300d6075802810309943e102004c00400011408540f045800b07140100100d69450189003030080480b24075000506c10031080c181848030030356000050369001070308005641c6105404851020640c0310345008052907000204107a07484c6a41036102c80a0b80744030358000c3c0044008060b064049480490000307000c5007600c40040a101c800d00b0240c00744112284903042d0b00100482109010401341c01c4c2100e450351160720321600130302c8050140c0c45c12801a41d046007040b407400009401041c0c4921020b000703580d1401505c0c255075031780e1641690700c240034060b21841e003828142101d450340c0a005c141d07002c4002c0e0032007520200151944904071043c0c1020451072a0905d44445e40c40d250180c444010030455020301c0c5c0100b020035004100031420618040e07034425042c80054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 239552239 1250 239550989 239551009
    0x506010603020a0f0503090715050d051807060809011812030c020c030c1309151d19020108041130010501120b0603100f0b0112090c0603150e1005 64
    0xc00705070040c4208542203800081640b031180c11824442d85075a16544c8007460b0044aa000605080409201442d0181c200005009d24009200c0070b001c295100595290100c5ca06810f2a40e80e9100314401c00030f50348500501904a0008000460284040a6911b282c0c42c030404089d80c0c0c2d004049001018550188919980300c0428000743c4080589080025101d02c00300382424018800301869032010840c543c03045201c96400000c4001c003800c1105001e0080c0791540c0d021554065070341c0d00400b0700c000056908440003c04511103020030340d03940119900c0b02d01400840341e0030b400d00700302d518942c3c030100cbc0a8069481038504000d500d20420100c10ba0075100d400705250b40c0d14250051040c00d16000409641d02e405c0080c14007151540c0c40424a0010440c5c800c0803810329001c44083d400080d0382100310b80e15400da880340011010580100700f1259030120040082043e05402c2150720f0094100c00300c1c0ba07100c621510901039403803160a8800108503003c0220000c419000d002c0b901e0145415 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 239553489 1250 239552239 239552249
    0x3050303190b01081b040b12040c05091306090206040320130902010929032517060d0602040b0c0303090106080c0303030c160212010b0109171203040f08070b04050601 73
    0x1e000d04280e210010f45100b802500089200c640c00002103c4074070640102d600402c00210b5030b550301d420308c0181c44000301003524110fa10251902c2c0010302440d01c2600a03001d15401035042c000800c0a65601c0c0080001030400ca07005502440b0000200314006108940d5031600800d10400c403034000b007005030200460751041d40d0a481c1c55180310141c1d81c03002c000000d0b141031807074203000001d4100d2688940c45404020310b0081c40e0010030403581c22022550301c00b01010b80c1060704034410f18032030709580100d000c11102c0068410800010b00a140100c26507007404c2c01858010f01e00b9444150707010b00d55000ca40d103801c4561000060096140302407007400c00400c0e803d400382001c0e80e01c5c80002900c0e440301502c0c40b0000d98001c90804082021003480c031813190b80c0100b008100c40040040d00780a001d82e00c40c3c540c046040e2150016030450b190040c6210b041040016200d46100c0d40d450710720541000d4815640341d10382a14020005003100000c150150081c13040212519051800e249002016001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 239554739 1250 239553489 239553491
    0x90203061c0b1f0f0513062d080c060703050a0c0b1008100912180e0106080f160207180b151207030b0109030b06030f070902030712020705210706060305030319 70
    0x1040b8040c80c02510300c0c25142c5c01c5428505a001041e0758002820044d0000d8500354041d40c103200000d03003c2e0001410004940c81c1070314545944141c410b40380d0300d0815401d500100c08211000000c0d200d8401008001910300345900d0240c1c0c1501d5000c030006044505061541a0030010b0000744420800442001c031f400200f440300100b03d076200c1401071017007031008050140312165031441c41c0e4201c10310406401c0e0340ca4000e010350f0355140028500e100a803480d601c10040107010500200c2c3c0a90304114480c0c05170010400a440c1503400e030180005000c1444c4d12542d5524290b11980c1e0f25900c20005000000c449511011644589078144002a00807800c2c14602111012113236041421301040b80d4011284443c980d40701000b00307081c20503119007004c1074018260b0214007184a40e01030b40c0924903c0da80c100c19424104c83c0300049110304440034040e68441403008260050070350800300100208339615091000f00e9032560103a0314541c00c11140e6070000710400052811144a4090000300590 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 239555989 1250 239554739 239554801
    0x21e030408070311031903030902010e01080402090612010609050a0f060e070903060b1201090b0a0c090515030603010902060705010204090b0f060d09021c110f1009090203061c0b 78
    0x40426601c44441c400101614101380080c0340c60354041c03140381541560044003900080c440d141c01801403100c00c1d4124003180d08181100309552003034500f10b10032580500710b01c04a403640001c101b1039001110b0214000c2d0341302c3c000072419170358a004003409502c03400004945043e00010f2101a05c50641000c082c19000e0020003807580d52068078041183d0700b040c2c0001316030f407445010449408100c1c007403010542c20040307070100b0403251800300d40c45181035000410a020000e00c0440c1c0c07200b40d510070254081e2148600541c0c9940000c000e54110354010000240704509902084540d0400a41950b141c3d60210341003212001e940156103085408991121000d0400c10000d95a40118880c0018103950385010a0854603000c00110f10102028407540850685150a44041c00c03000021405403805542080c81410404032812840d20161503200a560601e980c6a009400062440da0301c002580700c0314900c00403480c076145d150360288010207528605400d1082000b0102090f603515107510711 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 239557239 1250 239555989 239555999
    0x7080c010804080f070206031302190b1c150e01030c0501030204050d0b041a270f060106180306050a0c0e030d0e0f0609060307020c01020f01021201030b190c021e0304 73
    0x7401c01d0368425840350110b0b48440d1110102c141502805000a40200e400428030418807011520900c0310b0b842141c5002c0002c50480300b10011801c2803060403500ca90600108010302914520250120400d11001a076070004e95194141c44a031a0300994001c4076100c018814000b0526100c405040c085c2000d615007454600070031020802c103000500501100c6000c0303020403048400c404043c15200000d0b18040c00c0110b80341c441221100003210540c40c1c0100501c01e085004100802400034820290501d030f0700c1e001040d622640d02c007a51200081610201100044d59481007074000c1030308820000d5841c002c1c8101810304006524414441c4d80010107030340070542e00104603524450241c806480350a803600101e007160140083c890750003d000700820000e2680001e0441580c0800d9085810f40d901e00389001f4200c1c0b2a0000d024900d034013075001840030901801100760007e462400c20501410417035040c004a40c9c0c14441480183c000d41d900c44080e4140c1c060300e2000402040245180174500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 239558489 1250 239557239 239557247
    0x14130803011a0c070801020c0114040f060e12030c0403060b0f0a062f1c0801030b06010c022205090d180504090305090a0902030703050c0f030f060307052107080c01 72
    0x512038000248100c2600000500080d800d5504441020f400c0b201d14035100c40b0614084d410900a082d615807030320741448076000c9940680740c01280c005d003410610564035211440a41402d200ca0b40c03061003000064540a00790000451040c03107000003061300c0c1d07400d42c505482a5248003000303a10540034010400040d40e00c4d034100e02c08540c05da00b4480c2c10012915415100c00c03030070107105a2803442401a00c1c20320140880d064500c218a00e0089034070008d600801e42e80860f01780030107403165400d40c0001d00207501840705400c050f40024020080a41c80c1c110004c0c1c110101a2405845602d031410302074000003c000c0c004940c030050401c00e100141090001d040c80c10f8520469200760b03180c1c410901454041c5045580201303025041c50002c544504110010754420345041e00020328010001e06001c0990040e2520a49100c00d000e00c1c5803561404040b05010241c84140d05025030500000e0383e9443d00004028076007601d10f50100810900050b9040100ba544842003a0b0861010900d41ea0f0348 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 239559739 1250 239558489 239558491
    0x19020f01022d010c111f150801020c061617040816140f032113020d1a070c1106030403111c1d0306040b040f0c060503011e150c020f040f14130803 64
    0x303040c3d94402d06d10320700312400025040038181c21880841c440c2c408108810103400604911000c9003c4840e80d8541c42404694942c00c2101900018100c24100034118a601d8000da003080c0211003075400d1402d01942401d518020301c2d002c030351142c0c0b8074000310103c020a101c00c600c100b82a00180d400c00d4281980100a0700c030142d031103801c4e5501d840018850254a902e5031200380d4010741a018126014949500140754402d01050000203100001d603640e48582c00300c80791140c2c07010b0038a0721180003c00340007058001400c12414056100c04403d01c440c020059020013070f1102d14140442d507000e801c003030804041010f40e04100340c1100102e5590f0b44000400c950080d911507002c60309a52981004440c402002c0e82c020541486c1d0400012000d0380200550305072540c0c411100280d01c40c850203035259840d14070541c080301c46901000c440c1075000f0045511006d001904a8070501110400034007101d0429003000075280c4c1d2462000f40020002a58582c0310380112070360b840009150b203404456000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 239560989 1250 239559739 239559763
    0x905090d083108070b13051c0509031f0f052203020f010c0c1101030c080a020a0212070b0703060f06091202010504030212060f0919020f01022d010c11 66
    0x60740e01d1203454108901d4010a4014100c201d10002c501d03581e15102c0c02070f0f802080150380385004000801c415200011004903015400402880070001e01801c030381c1890713141090328041c0f180921113801181c80034400c002e1042c103810300140111200b540c3c55821a0607810110503441d262408018540780464603c40421950640b180642d80c2c252a0491401c44c0007000d02c0900e508100c0510300107504100300c111218860400500840440c1d4011801c5401074880340d000182d142000c0744000320350b13038014910300d21584141e0f078a890b40440009403035440504222035103941042000052035142c89104003a0800340c6213124000d1038024010005401ca00841d202c0001504064085a0295080360001c690103001002603071040406180c50b91000c0f202c15050050740e400203100150041101f102182072010361100c040183c1d020302c180100f8250301d00d4107600c10340c1027058544071510b21110700c00301000b007007080041c07842402509544020005806011042c0c0314a80c0c0344102080c0250411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 239562239 1250 239560989 239561011
    0x8120d020c07051c03020c0d031205060a050a060e090c0405030303010b09061b0307050c010504050a0e0604020c07080f0f06100302060c0a1203022703030307050705070b0406090905090d08 82
    0x1e01200c1c1060800d5481c0d0320441e4044586014080310070100700d4038540442c000c0d02541c481040302c0041c00081419a10020b0004012440c1d41d203c0754201d910060b0004005000745d11142d40b14130108981d54182c2d00400302049034402820820701e0800f422a501c0600b54050900342468980441c0c1c3e28003040c02000d800c50400b15102a268803001c085d0354074401d0138a03450070b03000c0c105a0410340340d0b84a868255034a0041160b801415400381044904642c0060803d424152400c401051301c41005803010360310540801500c20030303030000c0100c030000c0d1038040c014202d00451003281c03500d454000304401840e030b0090002c1000b60400f2012407011260192901540d81c400c480c1c04a040544100c001000076103288109801294140e001d08400b46c680802440a001400e05c40003100000340c01907941f50340100002030480e4490409400c41e035104500f26285070780c54400003049900103800190014400501c03c1008407003500842d0f030826465805441c0340c0d00d00900040ca2003c0040403003580f4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 239563489 1250 239562239 239562247
    0xc09091a010f20030a0305090d080c090d050c0405040303061e0e0112050f0a12110606060910120908030610211518050103060501050108010608040f1103030d0c030608120d02 76
    0x50907414a00c08403d403000401d40359160400f0b4000b40081605803070340a900d21900c08002180c1d802040c1c80c6010b0485c109031281001c280c3c00822881d04007088049036180160000c40c425900c403400b031507010b98403a88010580c035040c103c0a09240741450031003159191004030402010740c4800381d19040d207982801030810724006081031850400750521a000a102c0c80c103502090101c025582010641d150b0740c0c0c0c03415404820601c3d55030b1801a1071072540080e04118011141c600000000960000d07402c0114801c00f5003802841101c900000079035840200008101181c50508441c903080081030030650a5260461601003210341801045106191f84000d0101e030545045001401421034142c042600140001c07807202812080c84110b420030304100c00400c2300d40c024103103181603c9069440c0806603603a6250501c105810140503241001e010384500c4881e03c0038001001d41600d52500468001c00801c5c0003030880da025030090400703400c40a21650000300b41c0302111211450b40c0405078503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 239564739 1250 239563489 239563517
    0x302010c0f08032703041406070309080f03090315040302060f0703020f0a0507020a05010c03050307230a050714010c021509190c03150c080103081605010c09091a010f 73
    0x101c9046603002800300798003c410402e400040320420136034211034071800c0b07074601d41c4403c407507680e80224040c0100c21660300c0e000c04c03203d00f032070000f07404c1c00c5000e0702d0462002990341d40c40605044100e11050916000000e13004614103040007500315940700b00194810915044e10002e4654801404400c504c0c0c5a180c0498017403842901075440031803c04041642d2a0303245900070b0110340c072000c012070140301103501c00155580107400c03c610041d050380b240381c40c594541c042210031101c41c10b003050b0000440c08850030550b0055002e030100210640301c00c0d42d5464181030207100728041071900581c03a0306160540d150302c0d9010580340107030f03805422151620b403503600c003140c14082c003041510b240541e2100711509004040380100204c078021415408940d20840c20402038418403245140414044401080007812a00c010140d054140000009007255642ca50342508ca44c88400340004500b89414015080c03a2b20800b1044c5181c40d50b520500c54416001815202100c404a014401c09103406a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 239565989 1250 239564739 239564753
    0x1303030203070e0303030109061d011a03090a080d0605040506030706021c0c14030304020108090706080403050d0b19170c030a03030509070f0303020106060801080a050c040b030102071a1608100302010c 88
    0x60f0001006003a00d8070b03513840390407400050969100e170754407982c0c2c1103142c0e61807601d42c1002c440c161203070501c4410300e91080c100b4440695001600ca0166482004405400300b90500040c4c0900b0324800c1002c6201403070f08040100703551018040b18404c2d0000d02c0208501600000c109040d68003c180f00c0c551240d60b00400e45103440c940d074010b40a000c0c0006a902e0000c004002503101d40e01c00d880d0307400952503001c161641e802c2c5502a00c000700301200e000c907000c03070b00900151030300360075500010807040024404240308000708800348051200074174003032042c0d103181c2110700e850300444002440301441e00710020369520444040542810383ea40c000c21080c40b010301070440034141003076042c00c0243d03070391800a0080a4501c110380008001c040089046500820301c0d2140030380050040c07103240440030402005010010319258159420400340d4001428560103043c4070100d101452801c3c80c000715140c40050101c00030500308546c030400c02524089440100742034980a10b000541e04a00d494001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 239567239 1250 239565989 239566007
    0x2001030c0906230c0709051f0509180318100309110603091204060203091f0c140f070306060302040c052802030405061c1b050d150b070f030215130303020307 69
    0x30705003000000300a104103800040702c404446d0769071410003150342e50310350040140814030340d85025000c4881b800c0100345041401241c004500c8010803165003802d85101d45164002002d40c140b5403040c554001503403030640c25254803039560f41010310201c0190341d00d40c2c107400e1062004034440c0754040040750300e25000700801400c01c412540ca00740e69a8507060080d50300d0700715104191007907603512141c2e03920104c24600307483c0c1ca4000d83c85101c0e11a0300b03036480c401d980b05508070f91415841402da840d01c0321641041031100550003001c00107021404d60040c84192102c281c2010280401045020388168081e0b0303111550b4442d045035009076056180c012411403046a00ca1a0320810201e00f1080c500e078042c0e210504501c41ca9801c2001d030614540500d540e11498603000080345051042d05903141142c1c00140c00d5070038001c80301e2040f98440c0546480c9070400a000c0c3c800c011928040010142c04000c402c91801401e01c0d040401c0c904003403080041c1501e880020201600880810000c0380a04d40c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 239568345 1106 239567239 239567297
    0x61503081b011b120e0105090c010f090503030406201b0609040905060f0117010509070611010f0608030d0b1507020d0f0b042001030c0906 61
    0x800d4400d981c889039080c1a540f41d0041c50144112101159403019150701c880c1d40120907010070700112008000d0b0181140c0c0b6060070301c07075002400148207510b40c5092034144a40300092104a5031080154026901840003007404210160046201c425401c0c090080c40d0004650496207987e400d10111415240005031104058038148170b001406044005440410b01c50015510345241a108490651502e000613005104c0c04a1501844044600080003070003581082d003040c98481100d0f2044200740604c940340807007405029008050100078000781049169922000d05860b036000e5600100c40da4980328882c0006d250458004106103c146441402c00d807070341d400d0283c10300c4043c01c26205101050100700004000b0303000c0a20640c070504040c40c4101d100c0d4031842c010b076149002d10f81803501385a1003480407a40b0654100c01c0341d4182c54032128460080f00410840c044c40158 = true := by decide +kernel

theorem cover : BRFrame.Cov 239388489 239568345 := by
  have h0 := BRFrame.cov_init 239388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 239388489 ≤ n) (h2 : n < 239568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
