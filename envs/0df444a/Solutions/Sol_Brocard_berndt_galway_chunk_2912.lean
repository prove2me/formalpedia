-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2912
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:07:02.167609+00:00
-- url     : https://prove2.me/submissions/5b29c2cd-e148-4e72-b517-5deeda55cdd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 523561151 ≤ n < 523741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 523562401 1250 523561151 523561219
    0x1a090604030b092a010e0d0503030708010f09180f0f0c0b09090c040509012105071715071e03090213050f010e0105030c06030a0914070f061805 63
    0x1651240b0340560340301d0040302c07807000a10404000700c0703030540c851032040041607401840180d550f01030001151139110001150307802401200044000034010070045106030001d943d25022541040b90040801c095036000c174400a09040c4881d82c0014084101405036038800030307505291001c1c2c600201419a03241c070242c91507403103030b10014032480110000c1c030300c0c18000c503030b0844207541d800309804d00b50280c1d00400749c01c55160001840004030001180e00d081c05d80440030341c003190880d230702c5929013032094000d422400701c0c107000e00141c0c407010004990102c3e40704000d000d1a280c058002060702100200540716150708814200c40f980c00b9a1142c1039603900540700d611051000d804a1010340820348818208030250303000050a2010908a6030603900010060f201c000640000c100640d080a40301c07290f1903907540c0c880000203e680707000c0c090350301c0024040d2200da072400300c111800c000a51b22038024003c06500035584400c80018042c151036088420081c111010002c1c41000d0060a40b880c4036 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 523563651 1250 523562401 523562407
    0xf050d271206090219060f2c03120a0f0e120c04111e030708010602060702060103170904091a060d0308011511030d0e06060109060c0b0603160605120a020304020a1a0906 74
    0x80601002040c1c0c00e91b50a6224802150080305049a9500311003807002c8001003004c3c0e072a1114207001c00300000d000c00003400c90702000700100318003641d0f6100051180c00f02e07003a410300303070451504001100e214540846120280e04c07106504141c4402c83c1f104601d02c1180d0b1211844001d0062005684a9844051380004084180c00268800303510642d41d403408200007500000300309100284c4030340304401170360151140b6403855940c940b6040701e2800880c81007805100422803501e803845182c030103170700880040714903000143c25074034110030141205000d030002c42c1c011030100b600035090328111480a00084038a90028100302e45505020600b1b92090100056007081e003805908050b103c000c90f48103480c020b032683d00064403448810321071000801c0e41c0101d000f01040c03a0102441e44000003030161420b00141e410440d884504a400101c04a1804900c002401410174a6640e00400f140340c00c5185081c2600042c0c13206055110307240a810440050741c0641c800c0c0c0c002d407000940d02400082c0c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 523564901 1250 523563651 523563679
    0x611190320010204140406240323100e010b07391401030507081305150703090606080303010501021e01020d090c0e07181406070f050d2712060902 64
    0xb010f0340c4280700301800c01804c20949851850284182d80880b20170b80e100c84441e40418111a40d031502085040b81070541c0c4491034080c45040d180c2c008078040820705c901030646000b40c01d00d001d64403541c0201c0c022111510060045058000403903440540042c80390110403c500c2c4070640b440c101058600501c0d512002d20042e141d02080030000b40c50210301c40c0400146400011001c60348216050030015404901055040030b0003007010595a0044058540d503411960348000750304010f0f82c440b80000c2d5a1015002402114480d45005d805810099480d42d41b42600003961992400b86052441580c003018500211096048540000e2008402d000045841c00c000301294014480d1b40583e218110028000310701c00c440984501580e00340d40c11032641003c4100554042c0c08207600c1e04500d080000324049000810880c006600c180001c2c03a80c9941080000e21805900c40440d6060201e451820f03e003403c1b40c100320b03042d01c241044510a40c00e250074440c0191001d4800a50802c800c052801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 523566151 1250 523564901 523564903
    0xb1e2e060c170901080f062e020c1f030203091906090c05011b0605090709240b030103080708181315061d0d03020c0306070e0a0611190320 61
    0x61003180c015001610b4404640c040c10480d0300c2207004040c00201d1100c0010000510700708840e81090004d4a8055902600c1c0a058003844420b04560954080003450701c803000e80c100700c0d1950f803410581d882d8085081d4480300784c1c00540000040b0050640100c00503070401010000c6a80207000b4814125440d0014148400107200303006069039414035403840464294040d50800b40e0030703207080101130000c2d0029220030000b008080c02c003400c10b0058134400580c5c49414040e045940350445c0100d105042e0459004038004d1490b400750409000a200400215103050107880700359070002c88240d550013038007c10159010005254507441030801018900514440d03003c0f01d40b00e0304900c000154251519001c0e0780071120341d40111800864540c1c00c2d4814202003400c90515032280c0100c0d01c2881c0d00400083c146801111044e0014940e1a402001d51a20134500e500038000783c2000d0030850341d407581c0795460781030302c289070309500509000c2034042620030078510442c0c1844002845c503c5510f07184907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 523567401 1250 523566151 523566167
    0x219110103060603050903220f03150f0c05031503190602120105010302090d0204270f050d0512040605040f08030c04140a0506040501140f04090203040b1e2e06 70
    0xa80024541240841c48a01a225980c00340c40b1001c000d40c2841d2115484800c0c115a4029966114200c02d000041c080041c02c81c103000b45104503080e9610810300014442140d0704003c41156003414100705401058000d411281c1220b15041010030031100000400d1a02e104001c2906841c01d1801c4101c1c180682940a80f0761000c1220040c403850740d880c001102603009000715260f03c9a90541244018901684003c08090924004044040306014190021782e00c80100340c1e19402203900c0c41c010010207220748030701049142445800e15180701d94101030b40c41300900040090303641d2000b107400c3c0001581d820b11341030742c054015903032458a4510841c0381d070002e120300200082264422029460104252015035101a00803170801e4a003100441e4541c034001e0705000380c038408000e0321181c50590700090000d00031031100135a1307034145450300c0402d010300140011200301020030741c90a80b105840040303402c08182d81c00b040b41c2101c1541d811182003c000035400148044100024015400c40e0b10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 523568651 1250 523567401 523567433
    0x405210304060f120c0509040f060b040f03030f17010b0304030221040f0506190302090604090e0109030e0f0306061021090b0f0403050306130605100e0a0f0f12030219 73
    0x14040201c65220300c0d500507185c0110201c400b1480501c1880c00c0390a00b9404400511603034400401c0003035552185403060352268000c0100d4885032041481810380015102003900858901018119207a1101c0592080180140c0b0080320000000c03905152082080000c080074241d04402812120300180e113883d80030b403041456030014403800154a240100030b035186100a04030740c01c0f503102a0807046000f0752045482e0b5038400e00c140310100340300c88940306101540101d03c0c000101840c11b418050101d070540c107901c900c107138030841c420302454a01250240d000002515503502c009000381080c1d84248507116455072614004c254464055903540241a40b2406500509065200c07a014091240011076002d008288200041034560420300100f4024000301d03400092500d880303c000441ca0841c18131740310001211554800300d00c0c5400407080004200b1002080e40262506a9012000785180f08107500c0c1d4546009400c141402072119a028030b00782906000410307941d24265600c0b00d0300c80306d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 523569901 1250 523568651 523568657
    0x13050907050d08030606070c0e071d0d200310091b12030518030a082109010606170c130b0d05070305010303080c0351060405210304060f 60
    0x2805003440004401071030f0300803440310710b543c0c0c0e03440510403a0b80c0466002c40301c3c181203e00004501e2100b100d0ba60090003030750303948500e524103c8070060044a81c620640d20071000440f03042d00003110240f0710350700d0f031032403101e1800610349900010b0b0401c0301c076811a071615410102100c003003200080c100c0c1031203196103990907181606c46822030b1101c2205c1e10020003003202081070001d00301c180b002c104a4014001c0864002e0040340c0c0e16400180c000c1e1001c030740142d01942401d21001150fa01d040c0e8400e60450081003850300e4144001d242c2d164013040400c00c641d030400420340c0d10038000106c4410440f034902a848660703030717010b804042ea4410f2580c80065072404000c0b5038401e210303004850480303400da6074041154070344040c520b80c00c0e030028284030b072254060445601c6041c01c440482071211117111040c0500d0026800c803a1894032680d130301c441079502d1851f01403800d5460b04161000d0300e0042d180c00e125000303003088440e102c810030081079100e0301c00824009403031a4040303c83c0100107100d41e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 523571151 1250 523569901 523569913
    0xe121e03040b0408030a09020409150e0c1302090607080714150402030d050306030a06060608011403070b04060c02010912202202090414100608010b030114060a0c02130509 75
    0x501841203400161001082e20300b0342c0300481c002c29100c6003d107400c0203240ca00064008040d0340020300b11140d420f422500002441c02d0390011210a1091810b841c0180018000400550380000c812000520303402604e56800f10f1302d8822a12400103846015070f10603a80c5039074840c41d041a0042c10344544425449218850034502d04000c4c001c00c59018941c00f400a10440c00b40300d00a490b240c00043c5625054810704000402080c824018a40140300c1e648880f200d65041c02c0d08003500c000402d1865000c0e0303001c03400800104084400703c0d01104d11926022a0681d1217100490715051960b124400d5501840224030500030008d0308540e18140740750001d2442d1300844148482c094061074040002c00414184101c1c00d01ca40d002014000c00c02400004d0081210006190f009020b40d500c0c00600f8840c14140403150700582100d01501005000c2c500395850174030b070803611014031091030f4040c0300301058034044907001e00c41848160341e008003d041101041c180c820010002150314000c184a10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 523572401 1250 523571151 523571197
    0x1c02060304320a02100e06160507050301020f0409051b04080f37150207150e03090306160917061009050c091c02040c080a0b0f0a090509010e12 63
    0x121540340e4011044806003488400fa9020030510203240b020200601160b00c03a0140c1c1c50365503500801c10354809400005220800341012841e010050700300301c1c040c0c1e20400884030026074440c00e5a0031210848008507066441c4405c4400c54918211642c6c03c0c04000b01d000708510f5401704041100d0003000302141c80c1c0294080a00c92503d0303042c40401c100e442e03010000b2450888030316058111600a9807410f001541d070050500881c0e100900c251803104000b071450104a119011b81003050542500640c240154180040e4a504024000c5040c2c1d55000d04100da44034024400d0100510100480f410a012150039258546400311003c4c0707141c4005a401042010140c803640b801a6214801241081010400c1c01403210008a5845180e90745030501001680c0b140200248020340703648404040c00e05540300404e4403641c1901910440d598203144941d901da250244044031440d110200d80c60701e43c4030105004000d0805c10003968080c11000f0301c0d181100301d00506c2c071021404400c042410070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 523573651 1250 523572401 523572473
    0xb06030708041401060506040f0f0f03051203130606060f0e011409040f02070209070e01111906020a1e1e020606060921060f010e0112020f1c02060304 66
    0x4841450100e0041008900841d860f010310080d104004000050065103400020b41c02d500941e100b000144081c24040c465401c01d50940070003001e110200201d00d030700316036642d038580d0b10350603070200351040100026240c021562160300f402a0041c50403c449601d801004044070300c80581031001c6009030303040040c41d522501d02c0141104030481c3d41c0d13052184007070400001e440345074140700d00607400f4000c2d0f1025980b01528a4001c14081c2c581745c010780e218134000b400d483d07401829441c4035042038007000b2001722841d4124000782c0d4880070060391002040170540f0b0b26803512494580c00711410088480003600640701c82d40c0c14000c0603145e94103100d5940f0032aa50b5074101c1e00d1507081801400b52441a04001c003032207014201c481c080300c88001040c86001c1c5402021140680c101446000401002c400c84822078007406440c8094244001da54021603042c1c1603600429004020900d001c0c40e0b00300b4100ca0541c07070306500801847d038a0416060801108c84d00042c0c0d40c01341802c115040004801e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 523574901 1250 523573651 523573657
    0xd02060a141c051608061c1b140d0807030807050d020a0201091103070522140907051003020a020606010c1104020a08040605010906060f080702010209060403050d0201240504021b0609100b06 83
    0x8901e980f080c03141e90b125018401003103000d005101c1c0f1080d01d87d20f41000280c2c201041c840388103085030901c641514181d800300f8140507a9402c0d901565900d04040b0105402404803400d050b0182040d1300c003515146000c441c14480d0039032004543e403011506910455042d0014039230701380070b841640d81e1071103006d013051388450591044c183d000110340e2040308030090a061040d0b8201d146500011000022013038001d00180031254140030390407680041c08145403d80100030644c02c1860700f1410145d40c200040e582e4507001d8280340c148000c8a689904115820207002d661050150096445001d407100162900300b068504035a40ca08250011400c120f06105050445000d60358215860840240544e15008080e14500c1155020001281c180d140c02e0001e00c02188540000c204d5403107400b03002400c440d43d885600b40444071f04015200020313981040c80050354021580141c1e20501d5178050008400c9c2100b000c2d555014000400c00310344000310b5110440102c1c500c1c2408058000d10400c0b0641c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 523576151 1250 523574901 523574941
    0x1c050310050909010209040912080f0114010c061b0309061428060e0c07021003060501051b071d060901120503031618240e0d02060a141c05 61
    0xd89480c004001da840c09002e1150003240c2000018a06403988010406640b0840340030368608001051414240364005105036014001c40028081035060051030000703120ba000032181001950200c020900000d0f1b84a03040324010942c1e003d0219500000190181c0780081c02550414548181240300d401c0981ca0b482c494a40c05059400324480d9030f0036440004d501c1c4000c0e403649907880d0008143c0c01c050001d09806520002d00c0c441d141c455610400002500001d944000c25003456008c1100340d800405907000c480385210752041c40c90f000d26106160000560142640703003003101404048400319014036004800070307103161a80c2ea882e81130910180a8142d00144039900420005281d00ca06040602070003101d0329000d2401c1b00e2124a102156400381c01c44440c400401c014480300101d505600f009010944c00c000e085041701400180342e01a1212001e0301940340020400d01d00d601c9980300c0c1c00140c01400c56291219003880b128068030f072407031100a42c01450701c0c0208901070304c10f40092a0b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 523577401 1250 523576151 523576171
    0x90e15150a050d0b0406111201062d090302120a050709092310022104060e010506040b15070503280216051f1b03080402190308030708090a02040e1c0503 67
    0x4da1559520b140080a00401c0800501d0083c042070b1489060340310341a008018aa4880405141d15011100031107000d00444149525a84c64686580d030080007038001c4940481d0f200c150004e00740c03481801d0540044005201340038601010034a51604d40c400307071200d4002c43d0108040e03008084d060300801c190701103200d03251744084041d2561007103540052040f80034400031003090b102c440603030450088003505c0840c0c8950301e442d03c1d15402d150034810603500000440b0306100307170a055404a03507030007840c2c0c8451251000005281c801d0041c10000c5a03010400070502c0030b6008c0e0719174121000b0321036500d400001405048250020704075410280019550020001e0001c8041d0780007032412002140c1408041c03040030100304880c0040748001c3d5503024000c0e01c1e003c90700c1c03403d841000b6600400807a9a4844000600c052010440c004180da5100442c1e05024450b41c40d040102881c11802202c0254491f041c008294140100403501e1640754401281884000410318804d0315a400220303000e07148 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 523578651 1250 523577401 523577423
    0xb0c0f0724090b1501020a06020309030304140601050d0f05030c0d050a0909110d020a11100f150b12070e0a180507020a030e040908040f03060b0306090105070504090e15150a050d 78
    0x110f54160340d54400c1d01201401247e0b1500d2081d42d60074184e070021584010706400120801080c0008141030104c1e004a04000d441d456041000184a8041042d00581650b003070000724810494100116040040300b0380c12104038400d843c800504a80c44203c6810004002c087c00280361520340c0584400c6003420558141070040061002d4025001080b814040000c0e980c07110301143d00c00d2001c4919200458804141c014107241200e043da00007580304c1e0f140e000640c1d4108510b039032420544140d0001000c900f5081e44821000700d914840321944136902490100e000501d0040c400000000c1100d1818140a16603581000342d850b400240006804540704a02c41c1955241039402201c00a108036805030600341c445070306a8140e4000d400c12150240d49259442c19494100005940176802100034000352030308680043c894002c40c0b0907103020b82d86a09054000c0001845108909685002c01030118a4111040c0c0f50000481d40002d0007603074095030124407821f1680142c0041c507040203a0780c503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 523579901 1250 523578651 523578661
    0xe100513030507082a0d11132912070504050402030703080408100617070b0c07122603010311091b0a0c0c0f0506031b04050a060f02070b070f0b0c0f0724090b 69
    0xb00350b00160241343e6003d0020000d0b01c80c88c6900c0d05c1407c00d40c40410480400c8240800b4240c2c40569551914a20544140e0865150000b000078108183c030b4003503401003107039101c9202107441c02c00030740c0006000b041d01180104111500244203c10400091001e00c031007907984040c2454510301ca1000c46440e00420350501002402d640142100d010b804221111107903a40a503508040704000c0444c0e04006200c00d070b000c1c2010072000e0044401c03101010324990351442e51a50011608081024080c0081200160646c0054056110b03000d440c0c40c0704555030105840000c18001c1560b000b1146059148030201d0840340c2c0d80700b0401591400b07444585551600d410b80f080780d03081c001c1c1034171411340104004152500e0303c0f819170700100315a03280c0c2003040c02c0180019081001c0d0340c20040050100307010660106802003818041107410440b00d501c03540310403550340554495901004a410000600d08082220030740080302d0440c003124458084592594910040c2d41070b0841c00340c00b007001000412 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 523581151 1250 523579901 523579913
    0xa06050d050c0d0e0c10090e04030c050a02090a0f0f1a0d06060b16030207080d0e300d0e040903020304061b0b01170c010e100513030507082a0d 63
    0x40c2c105442c503070340078207041c2c1401d092000d4580381c2c82d051000c1e8001e0f0140c1109803c0c01d940f6084c50b00c000e428641c5002e81040310165601000500c064100102300100c04280072052105586161300a07000500c00d180c00c41000000e4054400c2ea0520540f0b40503a2608444962069145910024060f500040300d00f80c200950320b0350b541b0081e80e4a9940c1e40d0001100303194440203002c0d5952191407003041d40e03401d09019041500ba6401609507030480f0a0041c072181e072000b0f068000c1c0300200c1d40186406801840040c410520078505d141009060346403a40100c1d0000388440303480c0c0c156540294000110f41400180c40300d4020050150740b0501041c00754a00902030f039808007056a0840b40a8601500d401c1084082a403001c02c40d291014000307400304006001ca100c11450a0819404aa1f009004034070003410140101c0d0070010003050f1000c12000c080a01d000440e003100480d121142c95540481c1c440340c03200c8500c1c0303140f41031a09012000151800c00501d035500149040003400d030700d44580b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 523582401 1250 523581151 523581161
    0x3070807110d020d0c080f1206090106020c1c21053a0504050a1509032007060827030c071a0a030207030512070818160b0f0f07110f0a06050d 62
    0x80b18003940904c84514011f00042c007511481000031070300c0e0303818144101400100d55042e0840e40854005c8002c184c0d16450b42d03a580401980d540c0e040300c042e0b03100c0f4140380034550310b0b04a1141a40024403402c8101c664083c000c2c00c4040d0700312082141c034141c040c1c020155071603180850300c1031131000303030f44803110b42c00b1540080d0b4418002c00c1aa541100c1954a030a8900c03042c6143c1010b8907550b4245d4402c0c564000c2070b1200044200d054602c5144103141065a26442486010704001d611130005448002d070815040c10043d0a50385410b0340f00b00800d04a490381c002244001552003054000201109414081d0070380c002c0822202d0b282900380e041c114069801000250180102009100d2045480c0c2d4402c03807040d880c0d030740c80790360b5802e000d80b196462604441450007035501018108a11044500458044900019015546491042e91201a0b0096044040348200042460000d104c00c5443d03240381500101c1c1e0410125a0f414100107482c0003a006a8000070001d00c00030200480560007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 523583651 1250 523582401 523582403
    0xd0203040e0105210303250f0206060d23031804020a0f2a12030e060c090d0c030c261501031b030506151215070f09090203070807110d020d0c 62
    0x13464120f00040d070b0000d00c0d660007950080b492035202001d140c9030f030200c000300b51805500c1c3c0c900a2041000054001e42c0c44001420382441007000841803070400c4010010280800110480d034400841c0449217240c80350402d10503244001d00c62004030220f890300d8030890f00130500545482c0c3e050340c02010110f52809141c940c00c90148248416014440514458224100d10440c44a03020340960b0800070150781444513584c0440c0e101005101c1c01c0c1b0b003640192102c01c4001e5038010711880c080d0a040113840080da0001e429100d16010105039400885403100c21502a01c46000d00d01d0002d03100103588150a502c94401c141c414001800040d0001c6c46115911700480c070310492154503902c0b07140c240803068610410f8800c0404c074a90355800c1a1a40040c0f102030b80014000b40002003150004003003005101c01c003000541c00e401c80c25280600c010902400604104545a181c0118050a58002508c4050214210204416910348002403845e4000e095902030180074411a200750f81c00d8500000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 523584901 1250 523583651 523583689
    0x12050601170a0216111206040c050d111c0201021c020d0509031c05030a0b06041a1605030d1401090905070b031009090605010303080c0313030503060402070b090604050d0203040e0105 80
    0xb65080c0b000d1990481500c0d020300034a0176240003401c1081171440c1c00545c000581e401c25010000031800402405045800945101600c074200749403103540480708514180c0d10ad542e440c1022104005080709005480c401e0f000c403841030740c00071481e40b0b850255154000069003c1156020400d200320003500543d1800f604484030940668000c03c0301040340b0008100090010080041201c00c074018140e040c0019030340c6a1805081401440c8042080ca031103552003880000c0309003105903900400070314140c1100c03d070303900c03000c0c1c090001020303195440c1ea115050051400202d500c581e14460b40b1001c6910a0007414050b00d492500100358100400000c11581c108030002054030260180c500d0a902c16000000d81d5811841d002d0008030025050100d95081802003200850040703840346042e075010706003680c803941c8420001d00a4030034220000c00340c1c0550400e11103085800244180614841c801380c43d20500c01060490303803402140316051489101d0f4004111700e0030410145000104403003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 523586151 1250 523584901 523584907
    0x606040c0c0b04030c0b160e040207050a1703010e0a021914090a06080f010b04060906031802040906050f060103020c210c060c041706130618020907020a0312050601170a02 75
    0x140307840c070b0504000c9a050b4046414030014004001918412503403000c0c00d5080302071360301c5502c0b50080050101c001d0f4980650350010740d64040c0181008402c0c902680a90b8101000c8010502c00d88181c000f031003030000440c09400803c3e40c0c0c030f00714029900482040503044200b121600c90403941c419420215210704841084076001c030380c480c1849000580002e4036210710034104032103801000030050340240710348101884180035240d4092445000c851480c0707800319485000f02d028801c14a240d40c4025030041c9000952810803840c1c2e0402c920903000149a003c0c1e079a0358100540c2a032082c00c0a10185030450480b9055154907081000d101c00140c084c07180c00d040c01c4070720760b929004e001d4500b100c944001160802020384484062b500d01d540b0000071f0306190515400c0c01d40c20305450714009102c9034440120300140c00c541700c06074103c41e8000380302d0f00c8036003030421000e51201c072802003d4000407a402c00e5981d221219010b100e01504041e901c1140c80310741403407140f02500002e464140c0c0315400b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 523587401 1250 523586151 523586153
    0x6140603150402030c040509060d0b04140f15010501080a0b130c21050124021009050a0203010c0f090e01080a0807140601030305030609010905090604080d0608030f19020307050606040c0c 82
    0x83c406148242e441034032503a551424401082041d85008289a200b6080e00c07135054001012280c4213a001a485605810300380b144031115800c01c4544100c0b083c891107405d0045010021621005040300d0302038941c84080c1c0c89400e441c000b1b4400000c83c2c0350300b01da114250f03404044502e601003100f201d00c902e000c520040c1d0700010030b600281c0ca0804030080540702e0005000c460780d407040e42052103030300015103138840c5411040039445158085010306119550f00e1170b80140300090015001550b8028000c0000110001c4060720319004503130100c0024800714004524541810140d906a80c0100010b084c040704564a00a41d0380c0061340071910315401d040b40070792100e020403049018520a40f900c5480b03240042c144205036005074006901d280c204810b000c034008000c5102c1d074002c0e03002405203595441d5071000d8001b9000710b50002000d4480062400c0e4015000c801409002c46850340301014207001b0b0004a80c0d0303004a0001902c190082d401080140c50709134051b40001001381002c1408201c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 523588651 1250 523587401 523587409
    0x10080601050f13080c1c0209060105040302090a050a270f0201140408100b0a270213180f110a0810050d0f030201050105102c100f0e01030614060315 65
    0x100105650401c2500400c0c004c03504288010181100d0542e0700c0038a521601e06420303410f019a03070020b0700540a480108000340d1107003044401840d009402070666045c03525040000b00750440d42e0340741e8680b5040e180c8550282c3c01290246185152199218a03925911542d44800031684100e0501c804805100700010b60540030304024048030300035040000382942248207031540400a280b213000425014001c0d00000005d21084c0907a1002c041c0141100070807940007403150040010800481450020740c1003100740c0756103480c000d1990b040c072118500c60b00400941e400101d121020100901030b120b401c074880e4815a0b80056240c2e20501c241d5520804030f034a060a4240903500842024152024543c0902502707004020548846042c28500d403c000e044120020340282d07030629030030761a0884466410b0080c6864801001c03031810a107102d0703001d4100c200c81400340300419805800d60090350b000780300d00c504840e44c1e50039a40e8845454400c02195601c0102598802c0002444100319a00c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 523589901 1250 523588651 523588657
    0x406050d240e01031203020f040b031906080a1b03080a080a020d0906090219060e0d050102070b130302100605010504031104020c0a110a050909030a03090302070b13090507030b10080601050f 83
    0x34080b4001c1d1541141010062080500d640d5828940108804450707030f01c00c0300489044a080110103a101d4035080c032018421030700070342d2030b086860406201156001c000720709a04c04510408829007159000440900201040d11000c2c000c0e810601c600300c0a0f0707001390102540080403000c01483c06e04030403451070840d151604180c80741a0b03281042c40440c100003004151b0003402c01403580000349814001040024000050340c001d44540c0145020410250151782400d07510150f0f00c1c44501c2c2071100c548141692000650062048500c020304c108004e10840c42a5401a5101031405041d62128945032052100c2c05401540c01c0041d120301c0d080c207000c8807401030b00c9580c007001200b2412f410041405125001107205400150600050b0131000003254820701060401049040355818140d080803e56031280100d050000303917011220a0342140300c010740d0407240f010401a15403040c114125080140895040003d405000354518010581c041e4840c505140c0149441d4008412040c260 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 523591151 1250 523589901 523589909
    0x1a03062806170903090d02040b0406090e033606090109030b0a1d1203010905100f03050f07140d0311120f090306090102090904080702010c0f030c030f02030406050d24 73
    0xc2e040c003141d00d100d51107802d40c080e040001e0701e00641c100484000010120043c4910007032003160358080c6402c164465400460040c01c551408000c0c00160071440b40e12648130117680f6003203c041c0400030810faa12507820a02400c0381d1080070140c92407590130b02942c0d41c00f9140d0319040c025243c00001c0083c8000040354880c07031204ca00842e441d1101c25580c251081048041e1406810092030020410401c01c1524111561004040f40680314002e000f030240d08280c2100b034020f44950804802d10000180000b40c11626004980b007640d544c180048042c211070307069660107030200c02440c0101c1d2281003000019450b000650b03090341d03143c1c800c1850b00c0d442580e040c402c03240c02050b8060b2618003480100d0b80030f21410700a41c0b070000c1c03642c0054010038004000420008011902d84150f903c100440c02c105540200c4256030342c075440c100581207041407001140050401820710b030704140301009484c01c49200d6103441d400c0c000340010490103400200d6030100055210001c4104007485142c2c104002c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 523592401 1250 523591151 523591157
    0x90f0803040515060406150507080405090709030c050906060a120b0a120302011a01020a17090a030c1401170c0d09050d0809151504020327060a061a03062806 69
    0x2104403c00803507118800034401ea00c50781c07410908021700c650300c0c2c500b441549100d161040d52403101d442e110a00d405983c104035049140e8a0801030710640040148068034054900840d034203685100704910300030200c0d2180d8029509200c4100b4071401030407001c0c509001c003a0041070440f00e610100d24484000d9201580300d5462400389810300d50284a4805540c03002d0441480d011000701c0040e580343d0304c1c00d600410206048004010b40b160140503603c02241c002d01158102c0d50700d081494500000740a00c001400a10118205542c0129000c0f00c8180000300148800e595034040700341d1a80209002c18803481c0c40b2104a000030701e06020522240c00a03803200542d034241401c0f0b5a1424400f5140b10a0400042007130080182102c140d048070140122000741e80da58134603016202100004136903800d140088904078010510114106100f44022441001702e00d40d03c07480d08410215850b60f40a40890030000b1507594144132410382800e0a40b01c41e24412034015217410358130710259074861000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 523593651 1250 523592401 523592413
    0x907030804060c111f030c0e0a0e0601050d051f060206040302070e180105011701060e0f041205120901061e0f09020f091518180f0601020c060f03060a09050405030d090f08030405 78
    0xc050f80600c03034414500802c4c906204d00002c114003044c00c0d09d202d401071000750210140001d009a20035800c8414185c10501c0600040c01c003408038400e50512082c10034580d408440020414510008491340300d40e40550003044480c0c0f07866200741c0301c0d19000c0c2c103200c80261026000304100c0000d02440d0700030095447c40000d0f03001d0340000319084030340c25004074600010510900c64200c1d0721b03400345604140c12990410a446181d001610144078070400e0120001b4910204802a44194082e00807202100380740e1180d00c1c10040c1401c0031180c00e000340b400d80c2405e444280729040142d0f014182c546031013040c0d10704d00078240c00002c00c009103400d078900040500251912042e56049c900108080d005d5030030b02a04c0c0050b42741e40d03005010050945a6241500c80040e039240e108000711600c01c103001d804a0f0381d03801d8048e000e011030341c0111501030280002001c0015000c0c0c40740302e0a44147e0b040030145041200403050600900308032841a10000c20100c120808106140c0045010314801c070700500c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 523594901 1250 523593651 523593709
    0x3120b0619090e010801060e0103060c020309040c2304080a03050c0a1a01080f1c2304060201020a0e0f060702060a14030109050f070f09060c0f0c030b07080907030804060c11 76
    0xc510b10140c002c000d050741087d50170403400704c40302015410749900250105507100c20104c00c80c69130060810065100742090312001800d500211500b00b02c0030710083c02006080c04406085030341c4202e12035280345a11800740040407901c5900a0078031510441c05540c3c0c1031401791110610000010910030b88444110010040c030391041080e502a0960705c405001c0d07404220103101810160200c9880501100d840c00210114490074405011800040b0f41e5031182d40781c002c024000c2d0005022a008a1802024102c5c0d03071820700c41c1d41d101c03504001c21071850b2030741607402d001d080e0704100c0500c3d0501404440c480c50b800c4502e4041e601a00c428000080c2c14a0034040300300340450080e0003401444000d00d14440c00b242e22141e81c505580b66806e01c4901110549490110788502c01c40c082c1c0581040d4401000700045400d00c24018800c41e655120540c480d4a20962956018800240851002c11080100340d0048184c01603141c028a0255200d14180c00450784032000111103240c00b2400044400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 523596151 1250 523594901 523594919
    0x8071e0323300d090c060e1002060108100c1e02011413020d0b0c09030105041104060509100e180d0306030308131a0606070f141903120b061909 63
    0x151064040c0041070982d00d030301c20720000e070500d600c0340600e10703140c0000d9258a940401d40040d03015a82c4410620809941c3d8440100444445191180304074090b0850300071180c40014003074180e982a60103403d4103140d1f8003001c1c000740444604407043c000307180d18034880c1490642c42e425003108144c001080d0b1500d4240c4200680ba40101098004003051480700301584a0028100695070f11440f08440b64542030030402c2c01d8040c0e9a90750354950708017800c00007001003900e8083c06454041d14280f09250b241e80030441d9200045840041c0008110010072003031400c64840750b08030f401814070b0700300c2c01d5000aa4504001c0500f4005010030f858080030020141d00000306a80050380703044031a040c11040e030703d02070704c7d460380c500c0540c501c20160017180180e0340303100c1282c5030507501100d4000d01d4441868402c4040c030003e01250750300e01540724928010b00c040d0355010321a0b6419a40d08135401000b940c86001001d400c0041c50701300d00203001c40c0400b041011000c2d001c01072280c0f26000820b150510b06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 523597401 1250 523596151 523596163
    0x51020070e0c04080309010c0516140a050105070201120906140108060709090606090611120408070303030e06221b0803040906080a0803061005090406060f02010b010908071e0323 78
    0x207103480b004100400c00031504080251b941c03c0c03d0920b0645801c0c41d603410214903010250300c0180003101900f00000d40f0105001070504041006e070742843e882d541d01c0300152054002d10034083e0200303c5640e210744c47c07100c0725400300030796502c03841c000590041903101040700b0f50801d0b001803c0b030354016410310003815000140c04c8000c1c0406031090082ca400d214009002038440d00c242000d1200d42c5408210b030000130b200140c1c01c010381c2e030140790700da40d42d8031152a0345030000d2006070086442c10110708408503001ca94948100001c28010320000d148000c42508c0d0040190141d404411050700da030f240314072000400005005c920000c54682c0d0600c0340c03c104403103043d841f004103984554034050000e4070b48010b8a07885103088811a0301150080026941841804132403980240b0b0078078049045038001512400c03d5409038000c100d05581007005590200040c0038850281e0300c03541040102070032503d4203144540c0d045510b007a00c590350f03540d56042c0110582e40500c070782500e2540d0b080c01050070009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 523598651 1250 523597401 523597411
    0x1e0f0306040513260405060c070303090e0c1e0c010f0f0c0e03060a0b0a0306020c01050a0c110c10030207060e0a1e03050d02091c030305040b060d0804051020070e 71
    0x40c091008050313035511030511051180c0b074040c0f80c00f0701c0199159181c21034242c40c01040302403d403a1f0744074000d51101d500c07410140401c4021031807094000c04c54a15401d4800d01c07074032058030f2a0b032411303400140802d0a100c0d00d2000c024403200c00c00035036214410a001c0c200340c0c0061130754003140f20b006420650040e10140c20480040201e01060a51143d500007a2181c11034904500052480341c004040765902e00c5603040501100d000250405800034154051480360100c8101000300c003108401c111082401c0961004541d44009109190342c43c00340b444910490a5003001417070401e50340c0d105004d96001d44180c86068220244010910184001c440c0f50a00030003c104101402694007401c203002c2e460744d1191150b0702248002d10b54454000c44084001e41410482d83d035113003440d0003005020206c40440d5104042d40205aa900b0014034404d802940007450504150814040c0a0300481a61a0b102006483e003590030040443d0a070900e10752008078080c14005041c80603600b00143c020f44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 523599901 1250 523598651 523598671
    0x21b041112040b1e130f0b070903030306050f0f0f1c08090a0503030c0a0f02030712050c0301110c10150f150e090103030e0f0a08070810061202030a02061e0f03060405 73
    0x81e0001c100f681d44c2c155200e03005d510b4400908000703007440320f075154000800800e507000c1e6400b40030249402c801b4100450780320b07940a118a0391120305110400a00102c1542c1040624030061500d01d4802140d405600c2c3c080c5c40788500040581880d201c0a03a000c400340d4404d000080e40400c1c505019010700080c1405a00031460406c400b4501a07444036040c40c042c109200c100d06410855030103022020083c006412940750810b800d0600c2902d420765010042d01c030b0340ca417402428100e042402540d041c41c51520141c40503000030000704c0058100f40320b810b030180c5000c01d00481d600ca040b5400700701400039840e42011410100750701170041c1182c00b588500c6044000e004100096010701e400c200c400e0305840c1c0709082081c8002203060421250007005850084580100e000c00c03000a010300c0c149910320701800310350340d5404680400c0da4003d802a40503005014081c5c05401c3c908000c01c40341c14883c1e00400c11007918140b100784d1350056940008410400030500100e4541b81c0030307980d04804220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 523601151 1250 523599901 523599931
    0xb1507150609060503120301050121020910030b100f08160c02060c010e1b1c060b041407090608092e0513030314280b03010e0c04050c0307021b041112040b 68
    0x40010b030840e00e000c0c5007030bd6000c5030403d0944003842542c040d2030440d5400750001100e8000d416015002e03140510f9800c0c0524600d40e5040641886464400011086030329000a513440d030140c1d283c2405100200101170003594140305006803106401401340f1140709000084640c46069010308008241840c184644902c000c1081c40e9038503500742c00444241400a0124030229180070b0300549502c0c01d410341c1c1305241ca01850b51a200c1c0d941000c0c498403196888034034003515681e05441c1814180e032403842c55444100c2070140d50021000c0a680000103690829400c8008801002541d00460311700f00c03003a0040ca041020941c00d8000c0c001000a80145a0120f03c0c0c05000350380e00300851185945960305000c42182c454206e60300505a40d90060300901c10003040e20041303652941454a038501880c90000002d005083d0f2100b500e01900160f4041c0050020f80300d200381010100300a0300f03a0195442e1107118607180424002d046070f414160424010b071a06047c070124005005100030f51061840c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 523602401 1250 523601151 523601159
    0x2103040506161b1a040c052403011406070c0306140a0c050304020409020f0a0f03171908091c110106080102040605040603020c100e06100602010b1507150609060503120301 75
    0x3c54800c40400c4050071030070310024070a040c0350381580440c0c0c036980306a143c100180b00500070112568819a5025541c107064508110000b00d01d400180401c19501a414001484212071420010355039090040240b400d00a194035000030152031548111605c0b9641c84280b0b104e00515141564445000c40e01040040804980504140300080c4000e00ca00c0d542c0f0049000c5568a86485403d058054642d950003511039000380d6200a0500003900c1181e04c2603007078101800146c040324008143d4100080c441c0f044520165035140000d170a4414500648100800a031080d5000440c00c0c0516036074055a04c0c000000c0500711600342d0084070541c1d004200601c81c4039002021102120054940142e40c0d4003501c1100c0c3c20a03030380081c0c0c550782d68104843d58084040000307100d07016140d1b80c401c56040c581e494005030300725506850801d81141e4a60201c0540c509000040c0c455140900314840c0ca034401d69181400b01d82982e00046001982d4020030f10090504020681e141882580910310315418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 523603651 1250 523602401 523602407
    0xe0403050301091e020d0606090506211302030a030f2c0f13020403030203090108010f05130507200601081b032d030307080f060301021603030e210304050616 69
    0x500070040fa541e140c2160800712080c5540841c04100c601004640700e000072501d032405048188118400580d0385400415103250200881e6542181c195400c441e0300c01e0500183c0780118001c08030044c0d1034015045401688003441168419842513030360102004003400040d00c030101c0e8243c1d0016000344000f140f841d00d00c10f41680500148220b072044000030034800003d41c500c1c840c901410105001203000401c03d0f4001000e849012002d807501807150381c8400388001d000d1000e2198507841044030000791002c08060380000d4000000d07103802d019a10046003107000c14206c030b00f420000c951044004000e02c8d4010700c01d41c0d00701c0f840c120340110700704c0b040307000280c1c0d1310380ca203940f00c0c10050031202c0c42d03014040e009404d404080070700d0305070b9460b49003151014042e05400c4400320645254080002c140d441c06208807546418260300b0500704400b2920700701c0040000243c4007403d4401c0f80a540c094000d1200c07020900c01c4200c1c5402d50343d19052401c542424009003003001d44ca80d04041495080d50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 523604901 1250 523603651 523603657
    0xd050402181005011b020307030501060f17070302010302030606070219231509030a12051c09081e040503100f0c081009020322112b0b090109050111030a060e040305 72
    0x1c24603100f00407034017048100307000180c2204000c0d41881100000001c0103410341085088484101d00940d226555105944009203229600300490304107000c00e10043d0b0095020316005032000e03240c2402d00038141c3c0410402207284580c40002107141504105822000300c80301182612219050881000680462041440004070480c002d101044003051902c04000d040a06030b0060a008069944000068401c0e4441000048130300b80c0c0440100c15035015020b1030101540c08120389141540300c0e00c085e540080ca4550080c2640703000c0000041c282d80802c1441c0702c014014400203003402d1080303440c0c0101d0b141106d10b0014400c0a004104001101c0400001203c0c2c10420150380e0341d030b0f19050250091402d15400d4030040b4404404401c0c0311020701003204062064400075194030004d21030943c1d0806054645c2c42440e23100c0107030710004641665054100414a0000c40c610b101955980d09442003252444d100c00700101c10003082e005240102c400901c0784403d41c85e16800c094034002c0140c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 523606151 1250 523604901 523604909
    0x9021303021509030d08090f0703030f05030402030a060e07060909090812090304050406030b090d08150f06070b070c1b0608131e051b0301020c0a030e0d06020d0504021810 75
    0xe500502c803104021900d401ca035a000401070945e40c002c11a0310018100780d1003652a048180300315480340807107090010b01d06003900e030151075060f031018240744120345d5075100030000c036014000c00c0c00c2140040c0450044940740c01207407000c3e19500307040420041c000d02699020034840760130044d966022480d000119001e201280491484903901d1111039451482940c0c050764015140030400070a0026800c2c03518041c0000c80181c132501d0200c039208403104481950380c034144000c80f034a010070b0351a0090000e6000000070f131802e424201070340c6506504e84421594080840c05600c4003008100e07100c0d0048258140080300741040c14104000100310713800c01010001201c01c80100f00050006019040140382003040b01998106003e240907a11480c1c2c5000100440301c07841e030340d1415450b041c000e030b640301c44540d402001c14080b0703030710f045400c010a81e018a17041602e4410181c0172034450b00060002c2d6a000c900400c00d82032030b1050105120762030707401a01052840080c0180d0802c140008000c0f2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 523607401 1250 523606151 523606159
    0x80f030f0919031a07080c0a020d05130b0c0303010f0f140d0c080a03120b03011a0d030318120e01080c1e091c02090f0f0c1c0f02070c0902130302 64
    0xc101034000305003521000e608098840041c15030000d200045901c04c880c0316100c0d540d00c2d0412a225550104500d009118140d00544c00c1044890902449040034082401c202c1c0309003c0d01b240d0ba64001e0415500a141d6003500e6040080180445032920081000814010701300440051910304002041e52032106403500c1741c01c411075030009010759050600e019005040c26221400214500034013210b0b440080d10300f906003400031101891406200d0741c5d41d038048040d0341403482c200030410425009c818038412014190703070b21280120200001c2103800c01501c280061810b1181c0400040c00c0004009041c0b8100b0125504009884840c41c0681d25000c90003205031040c40e806c40c082c10301501440074030076001100f5124013055410002d2940d14054000e40300c04a07207843d09402081c6800088a84a134000d0f15540400da002011000500c0c0c2c020344100524a1015042680c00545100c0140c120043da000b040e16030070702c0341e03c800f9180104500003046160804020a41c0021716080c80041d100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 523608651 1250 523607401 523607419
    0x60f0d051b0c0a14061509042909060f010f030f03020106050301020a0302120a09120f020f03040e0f07020109020102070b0f090a031b060c0201051e07050703030504080f030f09 77
    0x10014414103031801040c0304403480c2d468800d03200c0d80c81e42d520320300d00068032a1454001e04007001c90010403154054204010050161003100050212086014004507166140740c03c00ca000d10350035180302c540d140e240c0c448a28090505010041c40c00c0005803410151104050040000700c2d0004112400c403a441300c402c6403e4400f50030281c0c010101e981c032080d0954000a860305201c2d6140c0e000702195042c1c00c4007480603403a80c5454074103c0341d036000c00401d003800101c01402254018a001c0540201e544100c0300c1440b440c0b02c070242560050740c00310340074201e580140076411203004650f69120020703200801169100340c0000b50394070928032030b40c001c1c00400a050401544403004032801242c1c05000c03000c07155500d00d00030044408241d100c03440d40c080040c0c0400d060303108004418896805a59580c1440300c0108250141c407141d5400c9014504104a04000220306014010066010351503860f2a40c1c500003166041610821002d0720b140c004110072041c2c800c07070031b05460b4489002c0c1c5200e12 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 523609901 1250 523608651 523608661
    0x15061804081201090c0909091502090a08010903021507021906020d020c0a08070b0c0a05120604020403050a06060f050102070e041713090f1508100f02210f06060f0d05 73
    0x30344500b1600580c6079100b100046010b03c0d1582106a0381c004990314880525a00d1a1134400c031000400020039074030981210f80720701c07000b0fa00a08000030f001840c00c10b0340c03595818813a08403080c940c022409070300194066000ca203000495103030701c00d4141c0050309d07001403d80c1040000546449000b000158040f42c1c00700000060b80c156031a0550320710455a0b00807050628004a8002c2e0701c040350300d10b00801c00503801001c07090940e138151446884c2c490a050102d041a503142c0001440c40303030003c0c1d0034040003020881c10080c0c90805030042c0c800140040c00c25110030151071064104c01d042d5030026108110724030031001c1c19584550080c154007030003402605207500910903850500d210141141e070108400556900403020300800d5070b002c200c00d4000aa1440001915104103119a00000300061800c056904540700910185000514140c0740c5a140802c203401044c4034241003148000700485501c1c1c0901803900581c1c2181c00604003040c20480840901c0350601d0f05000b1519900890 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 523611151 1250 523609901 523609913
    0x19060b060415030c02070815062704150b0a14090601020c030a1e12110106052706030a02130905060901050c031303050909180c040b0102190305040503030301030b01050315061804 78
    0x41d0a207101030b540e05c0c101443c25200c90340c03c16181c803807060300c0702e0348a4540810b03081d0005000d0060f41c00ad0403c65922a00c942810154000382c8081842d00d0b00018a101c1d6a1003047c1d001030454070203d0484c103a43d4400340540020002c3c411819540803401f501c449a0300081c1600c80700c1c1e0b003c43e08046540300c440d080f292003020030100074400107512800f034a50a0f0491511140030300e51900800600c0c1e40c2c0e0381045448441c102c0d5454590050a15210030180ca0150311544000c0180441e0030a440030741c08145000c0c94a031072009030556442c24001080303407c4c000c0c40c3d044030581d0000e01c140c1c1001541d0008510000e0601040103a507980c6010405000d60203413001702c0700084c900c075441d00c1c041403c0e10010b459600514010300665a245a85280134030505030040c4060340102191f62030b603064031001141180c4107805210041c0320008175030f41e0803c0114007171031050034580560352600c8141407410b41c841c003a0034240880d0208000c260348904050300120b10b040d5010019648880c1058 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 523612401 1250 523611151 523611163
    0xc120304090e0309100f09050922030203180d110405250305010302181003061e0207120305010b04080a1118070804050d09060504050f1219060b060415030c02 69
    0x2141e0060a0100e8070140301c10103c050700068800380c3e14481e90b41c03406102120b080400f0b00c098408500755840520050034040070b22580000e03810b418000c000030090403200c503101129070450040c3d00020fa010131200d01c40c1b0800301e801d1800d650351041003907996207141d82c42d0a16021706004503a2800028094480885604407031500c030300c0300121341c050240c2e0040143c1024001640101ca81001d002d18030039005107501d01c00c00c3c01f000c10903042410f50361504003070603d206010215868407014007140c680700b80300070840184218140f1200c00c0e19143c0103415103e05a0100200b08403d00042288101c08201d40d60b0710b5074032a404800d150000f070000303004600d0301c00d032814003112410b04001595411400ca40cac000d0b800785c4210745d441c1c0c00e070420440300005c030f0b8041d0a000480030300007040242444500081e14083c0101082d888804880c03003603241c100c008603041c011800350030280052094611642c040b05a06a6041d4640f50400d801984c8901c40710201108060780c402e1036250280c405c0c000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 523613651 1250 523612401 523612409
    0x1605150901090f091506050708070f0c1a04081006031e0204020d02030a0c0e0f030703030e060f0c060a06090c0503040219080709240f030807080d2903010b030c120304 73
    0x1101c40252142c6600000340145041c021751000942e8000c1000c502513815078a015034048040c40c50320702c0d15078656020420b010021980070501400101e280c003580340140100c42c2c03680c0552a00c0b1440c00c0d120f5440e041070f08403c1c00e605440c10071300707001081901c03005250007800305210304400c25142c8007160007446071004051030b1a102109001211055421000c0000d403695154040c0030f21030710400440030621221560b040d4480002000000d000e041e80003224030703004189034249035609004840e070754049960510300390070803404c22414404620590010b0301500c1400c1140300030b241e601401d18130001d0000307446081e5000000300c100c1e00501c26403002c0e0034120240c1d60840e90b0390800034007601960707506203041d2001d00f04c202310710740514082038100d41d00d141c107030f040061031a25070203510b61000300c042c0c0d1002c900b000140c8444171f044c000c601c03000d1840384c0e1010440c9203203601405a81c610800c101d2080e4109802e080c00c90740c2c00a03e80b0400c0d01c0c202c1d00500c1500c5d025103d10700e07621a540c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 523614901 1250 523613651 523613669
    0x60703050405060a09050f090105010813030e18010618062a02030f0313050d0206040302010509060c012a050a02100c030b031002040f0f0f03060c030b09090d02160515090109 76
    0xa030441c072440e4070171a038104554040e611040c6101c030b01401c1000303000c2c0c24050030f80080e42440000e8054008a4202400540a401c2aa5000d4480c402184103804103074802002881041c004100035684143c0018603001c00882d2020710034103014000b0070722151403420303114411100044444004105c143c602500b54010101c0b802d0b10348a0fa0304644982207e801d80b00410140080001c0c1403c2081e0513040c402d44c000c14240c5021304523401510300707801c405070854012005201c040d0380340609114100780c80140902640101c602e2061782860400c07041c040c2003c0013070501c440d45400f41c001074018a02c102c00c1c1004100526242c900700c0c020584d80c8a81945882000b0745460340c00d038103500800c1542d0003140000e03c170685070304440c0000c2000f0300c44c0c4112002d03e07080800204045500c082a00b081a103808501030304181c0010724028020350b42c00600b508020350500f00160100541503003140c6945e0b10109031807a120001d4481c80c5000940e40000345c000030001e111303a21900e210b0340a405401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 523616151 1250 523614901 523614907
    0x50606091e04140c0105070f060509070e1305061518190f051614032a0301140315011223060906010f06031407050706140c070201020712080906070305040506 69
    0x2040c03aa119209009169103a40204c42011860703520540440760051f400244d07001c0210066651038005100042510809004000010801103004641c4a02400c00e42d4182010481281409805e160707014207142d044140b00400d140060700d03001c60511005441806200d48d82d92049010103050503000503844403545060f040c58814601540142c0c02884110341ca40e00c040300c00c00b0180c6510031104031030002c007981400010b00c40350703841c19041d08442ea403c00004001d1414448800c05030000e8024002d1a112414540c1446c18200111181d81d07014403043c1130a540762001c10400a1f400c100c000d4003805010b904081c1140700e041d05104040d8082c021503000d403402b9141507448020078000c220010804d91070005000b40f0078000c1c0705402d80c5100c034030001911030b81000d030ba95610400c0e044907460b88403006190744a88090b5810300c55210310010b1a030b6840680300084c14032403141c00407030725000302c0380c4403001280c80c280075584201015501150b441d00141801ea039a802582d0120354059000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 523617401 1250 523616151 523616153
    0x109080f1b060108030f0d270510050c04050d1b06091d01030302030405041d0607020d090816060302031e192d0c03060302300307050606091e04 63
    0x64005001e10300000c406008541001e8440c075498030000e100d40499544103004085004903913600a2070011510000018400002030a2603c2c00148414040381c09540820711024010140480e0201c190307110030030081e51602c80040001c50151b4010107000f01602ca03120400c000310310207034140d40410000d070340e9112591841300401c50080340c00390701d01844048102041d82d02c3d5406005050340e0307260f009582441e041806000042c4a1200680010710b00b6a0307400d0701c071401c28481c450040c01d00e40e004e884805004000038100509903801410b550384000d42c01d8201c040c4178030009080c1e030381e68035025980c0d40f5004d0360303006100300b0880f84403000c0034506c09201141c00382c100040c402600041041c80072503114440700400004100d60140c104000c070110382c4000555521500901c002c505001030b9450f26a004035000058610440c9400c0c0e2070910554207070404602505e400c02582c500a501c0c040c1550744180d121f6201405290040c00780001003000b0500003152454103180510755a811441c113 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 523618651 1250 523617401 523617427
    0x3090c0b0309070b0304050703240533130c030608120702030c0607020904030e060c030d021e250f021c0c0503010b03030427090f150203101403010908 66
    0x4103030b400380c1461089100020701c40410000340d92040d50454007074800c03145191200b49a42c131104e074440f4440c0310141009080362a0034490f241c001d20b269144032966060903014503100c03800c0758450344031501e50342c20744020a558100c1180620300c00240c000c80c0502948409401509254005200a004901c50740ba4031090650103000414022822560481d80304404e00407103200341c2c0e402941090400c0300090209016681420210402a025529207285402c0103815500500b10000340e443e000503d401001040030150b4031142d000000b418071b440d00d0300c01d000a0304550f048201e80742c0c0038001841c609011100c45c842c10780540180c000d00b076148480340154030b00d100041e000c4801c40b44248020039281014881d2500440015006515007401c0001120011540e0485c0050b02e904100c0040714802250041d0617100c0c0c480c0c00190a02c40300ea1401da0300f003011050700300284a2040c400c100d644e40c11845240102d030000400080203454820110f4050b0101400241103050001008a64034003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 523619901 1250 523618651 523618657
    0x20010207051506150708070201021005090106060215010608010e04060f0f02030711070612020c0109120801060f0305090303070e01030e060403081006110c04020c07081615020109030f080703090c0b 86
    0x40c0b0500c078200d1030780d610f1081191030300e49025078144013003044c8010000a1a02402880c00c14014011500d84c00903008003c4240c5008407900c1a269440304010003055070104801440701c0114900402503605204000700f0070107052007410303103002d00800400c0500402d0341c044001c01d070208100344400b5040380007000181d4810780e018000544030b0a013015204602041400680e085556003c101a4600d09020080c1d000140055025540c540c6a000091010b000f101d8400d80f09803980c0f161985000f0024181004a400040c01c1c9401e103c20801484804400c4075841449428400294200b000048000301190084210944a204140010b00d40c00c0b0b82014451b05107202e260754070985039001180c2c8043d03407003401c0c034132a0700c400c0d51044103151580141c020b6040ca14115600b480da603203034452030006548641c0581071a080410700c0807580692003000d2002160000b405001d4040d54020301c7d51540100f0441081117540120b45541d100c0e41206400c55046101060010303154000030156038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 523621151 1250 523619901 523619923
    0x20705031b010209090402041a0a030c0e0f071b06020403230708010207020d0624090207060b0109081c02031303060b09010f06140304051f2f04062001020705 69
    0x2050792801c07055045414001c07114024000381440700c0d1501c4940c2408050045600c504414600e01600c0d100d10b62611091080118050754036a60a949002e0355000c04900c0507142113a0100b070402006030b655004040811400c1501c240003c2031000c90414000030b000d83e8000030070100001600a1140c1c129401d00708150507a203003039400c0d0507503800389035081f03100d4100001e4220580021590200d18251311500f41a29000d022080141d00045041914692038224010280c0c0c0881c480c01070044504c2210141282800d280c200c0d9410300364160b036254000307002400d00b00614a210140c2900c244242d415500504031071500c810740303e140c07510140035601c0501d4060382c070070000001d0811052000101702e5000d62a0120440b020009450443c1d000500a40b650303c42d034090243c250310001c80f110300500b040440020400b69505031190b581d000146500c4825001c40300019014a5580840302103481c0d5080c14000c03056908100860305605641601d050751001c0344039028008081101e01c1a4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 523622401 1250 523621151 523621177
    0x50f0d26180a0915140f0306040308040606050609090412111606141207120204050306010b09040e0109050c100e030f060708090601030f030c0f020405091e03250f050102070503 77
    0x20580310381030030f01183c224207000f4001c403503003800c100300e02c0350700e02550f68600030080c0c80185105081000301c0e10344001902c040f40040c28680c10802400a1071041d40d0117864100c492600c2d000c4001c1c0080c04400d07014101402d00402900050315860060f01061907185610043d81d10300e41a01040003072140882c030811001c102640e04081800000d20101d82e8aa2000110354415842d80300b030880e415042d40c0034400d0780d607508000118481c3c1e01080304034020300440804590f20f07a030800a01003074618041c1c0796000c580c14800010005075010451002c40c140075605100700820003d411254542e0381545c003609400f03a8034030380c0b43e8208003103005489060301e507c54203969150543d0003070b52000b003448007800311844c9030401c4001034480c418114025018140c0e1441d1640c0e141c0001d800c540c4250b5070200e050303020b0407489100c440c20105111100452034051803c18654400b810840d00c03000c40c502c001542c1d001000b8080020b01c403a0380c0011600300c0c000710748500c1c86280250f07807540942c90071069 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 523623651 1250 523622401 523622419
    0xa110607031a09010e0f040c0911030115181719060507080f0f040f0c0b130504050601090b03010513021b030903060f070f0f0221040e01050f0d2618 65
    0x250800d000780b941250100c0150051586e281003461404a02c042c104907445a00d1010001d520000750041020000322031001e940d4035403412003c0b501102d82c0c03e0442e414080380c0040b1248160302c80003200d0480d255030413064603040500d0f80c2d030760411410b03644600301041d4080650080c002213500c80d5200d1403494441c0101501c85c403209807142a4102c600250000d0040006000504c1e4072460458440c8100303d0383c80501e0301d074a00812f6903004a01525200c0c0c1c2003000030862454140507907500071100b8201800a1400c24487c0b04051205000d614040d190b182b4007129540290790440302110f030800400303179030303012403005168407584203a0a4a12078800c0300041070300e040454414500401d401d44a0052000810130140c41c80707440700f0003600c00d501403a5040700c0207000f18001c040c0a61a00e14265954600300307907485040c00c1e81a00b02600070089a202d01c229511262200340c02113803c60402071031b80c184280d0100c141203210b400d000304100c021071207803014210401c003280c040000f142e580031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 523624901 1250 523623651 523623701
    0x20a06050f0606071514040506040201090b1305010c1b0f03050f240a11041e0b07170d09150b03010c141806041517090705030a02060a11060703 63
    0x1c000c04056603042d0380468200b08100c0050040005000008180900451643d80310203480c400200c00320f40030341f0030340c0229007040210342e84002840c001d04601986507040030984019008011402d005e154140045000d1704000c0c00201d2111900130004001e0042d222600c07003a5501000e0010700c0100c85904c00c0340f0f034992104002007000d0a824102c07451410468400741040359044a002d4a0110b0959440e460b11141e603441000400c05050f484080f422580101114180e6450b8554080c10540d60705208000004850020b030742080d00c40b00200316281ca1203288103030024154414010940b440381c5c00d00c004d11a8660704024554102100200182d9448000a0725a45140c3c480000e011b03104104000404503000140c1003a100080c1150303040545401c4200c4004252004940c0032500c07940000f0034a220390b90000c1d90020308140a0710915180002003075481801000081c80382d00041100c0380d88a2040c1240e80b4400082011507074141041000a4018140d07503400050083c0d084000034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 523626151 1250 523624901 523624921
    0x31003150209130207110301060303030c12060308030726190f09030e0603150301090516080a03090e0a0209210606040e030708030a1107112e030b031c020a0605 70
    0x380045030180914120a00c18001c80f4000d6014030301c00c0f80d01768086407940400391001d124000165100342c40c00200c1c401c8080015122168038801c1030007030f03070401c0d41c14030000313030340d01d094980100b0181044202d6520000c03640030244c0004001001c0d01005408000401c01d40c0b0444442d000e08046080103142500d84400c02174800303056000d400324903801c4a03030800742041802541d0001905090301e13129481200007e0075a0500a0300390b401f40c0c0406803644c2d4040078511000020401d02004200f844000d0b03138040e0210f00715220303039401601d0010001d0b0140c034171a0121200102c008100300c942c2081a215480e900b90203c802e1002445444001074440c2414070400628102c450002c2d42003003884d0b900d249007640024000c80a49490704403e2100820803406032544c03522a5812a4440000c1e4042c443c0d007104250032040c1030000a424440d45c00c4400800421600043c035000c81e82480680200703240c210407449074a0500307196070b4400c0320b060f0301040d00c0c03002e284120028403180c3c032100098 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 523627401 1250 523626151 523626157
    0x904030e100801060e1e0d06090204061212030b0a0b0c06150405240604090e030a0806030c090609040c150504050108060a0b0a0f170f0105030625050903070b0310031502 74
    0x40104488445c0e1340b49615121200c0303100c1c1010403003c03903201c00c182d03004141950521802254030b143c440350700700c0441c5414050f42010301020900b98031000c1c0161038005e45c0f1580d5980a200b4035a40b410f221146032074801d0144080c0c14140d070f01c16038495101c0c2205941e00c800b03e6003103500b45240c12071501c06280c6030060b240611070010316041550034441180d00600700750000542d010f241017000092151036070260303103000e2440d4406192240340303c4001900c1404020812403181d040310281a15507038450801942000c0d05407a4911156211b00c0c04030040c100302e401004040c543d00c1100620580d200004006541c800e0741d03460042c0c0c4480701030000c050420b00600341e10380c1342030184103501880303110300d015009028070301481500c84c58140743d84500c000b610700036075440303404c401400f9600303041090f160020b45940202c0c100c2403001418200c1c00c0903091094080160001d0031456076502000280040c0420381c10907596070a040c1c00c1e5a020142900c012268030501e04c060210300305c513510035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 523628651 1250 523627401 523627409
    0x201090809120705100306080f150a0f0b040525140316020a0c1e0509091c0215101d040803070804080c030307030c1107050d1209050904030e100801 65
    0xc49814840e154040180741402420040220311070381a0001d0103545043d800004855903880000f030351801c0142e22424031401011401711036000311301d003007540c24900204e5a804501d280300020001c4e00d80b032440024000200495500030308140a200c0e50760318649940386c002c03284040000d50002003201c1500d034040752643c4025425800e00001c4c03501c40c2040110540e6a00600c10303264440c01a64480071031402603042055002c082d0451413149019803c01c050290108440d08105c1e440d080001c1c5030303586810000604546102180303040268020022a140481c40a00101a918000c0400c041102c4288551100756a01c00e458680702d4130a0151540100c0c1c000d84614515034400b2810b440404000c1c00455265200300420728500d182880a1400341d0241d0b9408074841c442d0300001080302c18441e0130745805800071101044595290618004031580c4003800a07080035004105440c1c921540d400309822000010810042690000c1307030110404044070300d541d512610381811603801000b405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 523629901 1250 523628651 523628663
    0x50d0204090f241104080d18170f1209010f080709030b0108030c070501030e100f15030c06031503020109050d060f1a21030306133207020109 62
    0x5400405400c103508103200d00e500865248030461400e5440850303900410900b07542c198040006481115182c4c0510f01008010b410303154186414480c3c900e071581c101e110a14184414914608401050b003c1c54600130420f001c0f1407581d00100e1840262545010810852070740160f0500d00e2209441c035040d941120b1042c0e40303000c4441903a44050396803c0c0302504030400d21081203800000616811419400f80211102854940d58080450780c508030803904800d0606081901035010041d0018001050400e20040401c401c0501c031207003401000c50b07159800d014030b50000b0101c280172a51805400701c82d10380c0c0d070400002d001003000c0146000140130090010b100010308110a24084c0d0b4205000c2c1c3c01070200007448194400018121092600c00f21240d0362861506402441d141c0b1441e4004002c0e114a00080100e61440c076403a444010302040c0328a202d0150215600e0850b440080701c0e86c140400c2c0e008468080e40203800d080f00001c4580c2603918968001560641b060040340a990740c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 523631151 1250 523629901 523629919
    0x312040f0e131502270301390c080f120a063f03030e0f031e070804030606030602120c0903060636040209011502060114010c05030d0b1002010605 64
    0x240d500483d0070044402407240f15000d0020000a07075209826200c01250b18000c1d5112004a00902d82550580a580c0d00c00355841c80d04484840002d16060204610a8042c001000c0824005480042030048050582030340405d80d084000e0000001345991034085400f18400c2d40c4003c0e4040a4610601810380d15a07008400303840c1e82d07078280260911041140300c5030f881c41340e4116001348816685110540010f070b12444019031080c01405207082442281000d98038050080e4503485680303840d0401603c0381c117000a4100c050046803815907000c0e50380044207001c002d03564100400a90424581d840400c0701400c04200042501002c0381c50340700380a40a0301d540e540c3c1e0002c005076102ca00e010840751600b194403801195041c040c0051180031560748840e4030381024014800b8060050704084008060b081407203101d190002043d80c110b030300102c0b17040b13152102400100c844c50300c0008010000d110114001105280640080342c9101040e5001e0600c000302d00c40c100c0c240e4406200302c0390808416 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 523632401 1250 523631151 523631153
    0x1060c0201080408090613030215160f0314130905010b091e01090510020703060f05060306011206090c0603021e0f0406030207051603050f0c0906010e0603040c050312040f0e13 77
    0x2e41042c9074424040d42c038190414071500c01003000742d8001000c4a41c2c2503c503500034411450003040d0498401240c50126042007510152070340041d241141c0542450a440c80324002c251041c5c891402215082d201c15807a000b00d415512142c05481c021400d545007000c001058440c811001d444004000401501d2211000007041600040c0c1d403622030304014440c54007190a0f02c40d55200903180c0f20030781c01071005625509108040305e00c40c134101603115041806010b0036a07400540a07040d2000d40c200300201480b6840c003540181440e8000902d0000700640001d00c0c1078050b1f0141100424900c030151410040144000031072007407222800d001c0b0018001809818802c2e400b506800348107074201c07a0300115800b41e110071a10507600c101d03807079400380c41e10303202d80e8405100b03450041c05c0503204052181003180c00a807012005007501342c02580c02000003001e20652300c0c420001000041d05880600c940b816007011036520130700940c07502e0040f400c80014942604030740c403481941c088485095038101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 523633651 1250 523632401 523632407
    0x7050d0f170a27020a0519030b150405100524030705090a050915011701240309060c02240f0604230a0504020f0603040209160228140601060c0201 64
    0x9041020425626044250700d90f0043d60614203c0220715210494441944100040103005400c454061408210380d01c002081c0c2e011582c5c240e036808a2a1503407681c1d400ca124060224548140340c0c07013800d00052100342d407125140602680c40541d00501015508500c0000901180e0a41d041144003040000c4c065480341001c2d00d4404401000d030055240d84c0c0001410083c000e44d2a024080d01e0717811244007940e040740d00040300404540d1a40004d603d03001e40d904203040d400d9030011024a0ac94440d40e140381c40ba43c0300c4015160300c88401c000c03946e150344009641300f1040c1c01c50061b81052213420320b40703020204800c901c05d1650b03c1301c44410350b940078103000c040c1244c01354000710010404074020003020340300b4800b8800c400100c000140b61901c0d00410149a815450a43c001e040400621000d43ca451038000d90206420030b0401840e08842710491400301e107214198050f5040c03000b9500d034054105242203615000b081403003d040a0b004225481c1c100030b21890010401e101da43d0401540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 523634901 1250 523633651 523633697
    0x9090a0c02070923091c03021b010c0c020405090c030a0f020d1e05070b03010b070303090809030703060e060901050c04060f050d06060201020703030509010c1b02030109021507050d0f 80
    0x14407803050301c4050b0b90720840c5800b650b0101c0864010a00709050b0194054a0000740d95131007100c84008000b13228500c0180719200b82110403820806400144001401a410b144540391441c1c050007080188071010b030040c0450400e0604034030581c2800e010465a00000a154544501c020064405d0f103030240d55007011786d200258100c0c1c100091078170502c045103442e4020407a02602c00b8080f22100c0442c1780080c00c116440d00000301c01c000c1800180041d00e586020b80d2040c95040c18001201d441c1410042481d024100c850b0b40d0601c58240c0c04000c01a0383d81140e0581d01c0d410301107440c0c5440d10510b2a080e100c085402134001803080c0001c016481c494142104003030280d04103140342c810011120002d49000380c00450140c0c1d00012085c0805a0510403680d0001058000300302d10010340200904a001d02c80080103480025030002003907503829440121143c0c1d004184104030540c1d41f820f0035854000b0340c8240d54500400300300c902034900540a07a03645400c1d175500d00c10705000b4840e900841e20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 523636151 1250 523634901 523634921
    0xa030302010c02151006081e100312050a0e040c0201060f1511030c1c03061a040e1008030a03110d090b01050a1710051e070306090b04060b1b241b09090a 67
    0x143ca0010201001516101541e004021107527500c16802c0c01d5003042071802c100d00c06c1400400000300000740c56264058130420b455242241c0114000c0c030000401c0740507040325040301640c1c0e1244800014444105060340880f210151074032500b01522020140e102d0168012090880d0420800440c040070010a40300c80aa41ca080000e0110340301c1171159000002e51403105140000000c050140ca03554040300d940c45110070024248550400c20407544a0003801814414140c495440c00205d10200041c0c030001c20034040d00b001182c00501380765401c0300d800e00c00e03140282c16080c2d02190980b409181e100340c200c50720006103180b108100c0240020300004200c9408245040d6124020b2202c499205020745444c0d0340224025003080302c154111000307030720341900c00c910b080c6042095005075400d50b4104000000150f100007030405c0100d04200c5e4214106110507a080c0044080104072942c4900482d80b40700000c03060a03c1400c101d9651250100c40c4e07a02c120200005205e0039100d402c52100d40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 523637401 1250 523636151 523636171
    0x10603080f0f071a041104020a0e1203040305010203090c10090305072102040e0c04061d06060f0c0304030606080601120f0b0406110a0509040509121e090a030302010c0215100608 78
    0xc005403600084d4140c1c4409050155540e5000c0c001800b580700358066041004460841c640400075102030207241c4000c15040c0102034031344007200002000e03c20342c0c009640100081d56a85001c1d140c04d5211100c105416114900052031820f41c00d10540c004002d4961140003803080b6420607200c1a0000c1408218002030080481030300e0058035035004006201074500020150042d4020030007054400b1500005404514040f5052404c9040c031680ca803c0348040e50070729911840b4a404810901c10b0b03045c2039106110005000042003c941d100344101c4240805a0b245a601d03058070a40c60120035802900e488445041000031400701503026400c58416040021400d0104500701e405810207880d038008181c011401814906042c01030603440080c40024004d61034604007c00d0083c06120b22141914001c500c007240504141011510b100c000207102c0360a40b9540d14000703003c3e01c04aa02d04c4c005010384001110000300110110340294142c480c0c085895040410031108034170024618080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 523638651 1250 523637401 523637407
    0x15050a150801060c08041d06040b1c0602031003060c090303020105090d0f1d030706090819020d0b1f0e041406040c12060b18060108090a120f120f1b02010603080f0f 72
    0x20008800040e400007031007c0e049161403030f0401c1041304440c4450030302030060402c141c0c00e0032010010984441807036071240c00183c07262502d00407031024000c190401480d407440c00190302e09564100700d450b01141d100e58024001c0396609108940c80301c40d01a0118040360407410b101b00603c2c090301d0540304010480c40902e044805001c002443c040321580100080f5440202c2032048000911001042246064203000200040d03030101f240076005c1c401c06086e1800717000100d03c0115448860b80c15510b2808079070066203850322a04150410b0130303581100d10001a02c030888044070b01203406407085030040c00b640c000b03a01e09103201803142c510641c210707040e5550342ca503030366180e03a200040c14820581d070b82d4030000e92030903000151aa03c07002d070404e15603503c082e0760200000e005801c50000c544040c40d180c25840324180064400101e2030700040344003402c04901c200c0000855100c0740d041d007248401c05074040d07403244040c0e089400c980005001d1640800140901e03500a00c02044070794035090341185 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 523639901 1250 523638651 523638659
    0x90602121c051005030c0904050d11031b031206010806131d06011e060503150d1103100504050d050705070e09120a0c0309050a0e0f06040f15050a150801060c0804 71
    0xb212003c85007100303500ba4081c0e0521250034204035011a1071015115060907090584905603101d0507040301004024000e810b030310040300300344140d4a81d0300312802c10464480d03202e00480e88076008104581c01d10201e8000150880d849046198064840502195410b802642d4102c01130041c40d41d801100d04c1d140c2100c80704200c01080070a00034001421960100b2101448031004150b895010500f00003061003480740c0c0c5d50303006002001224040b66130980d03400c018500119042000f005a035454040c0700700030300c0d02400b2604400d1149101c0c6042c0d40d12840c580300162894018180042d201ea405800c051180c0d003140022aa0012849811103d62500c00c0300e81403120340c40b1800200014500400380020580c001000a014210443d00104031906010700e0f000d03000801008006c181c10094040380803622103500503018516101000e01070900e06081120817a04c00d84211030165007581c078000b807181380c88101200250703806d648140090b460600200d036000c007000000d452188003000b0001d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 523641151 1250 523639901 523639957
    0x70f0e1207080c04050f010810200d02120c0a050706021308030301030305041401030612060207020d08030c07111c0212030d0c0f030f090b061003060f03061b09060212 73
    0x8001040c042d802030141d41070340030500080e01c10180541c0280311078034005000140c1c02040c2e80000d1b20701041c0009103240c42031014140300070105d50048402d00c0019401560705940d40060401c502d005c00701c0b210310b484100201c14180308d1404000300140041c803d1000142c1c450b00140614115040c8000d9100d8444403401c1c1103500aa004070040f82c0c7c0001e08001001e400d48001b000c15409003020402d044c83d0003141400340000c01c60041c0000c0d400242c1004540d6000e0300c2c8c001c880c1e000505a80c0320b207044100c070100e41d03105640c251420740c542c044409440ca00051140e620017010865560074480e16370038001c0c0c1340486030784540d4500007404004d042482c41c0c401c0c01b01e226556a14820324080e52103001e000c4507000000070140c075081c580000081500340c8c905a40051096840074004152030008400a04650708801e1801c0d9518a0010900003641c22a103c40c900100c480d041a0401d81b00c1590285014820400940c102d40340d03001031a000e01024003142426544070003200c2001c81504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 523642401 1250 523641151 523641163
    0xf0912030a05070c140a151b030e04060519140d08070804030c0b19080603120417012d091a0a0c08060312030112030504080d0c02010e09070f0e12 64
    0x4000180c004240c0f5002c1c400c218980600500084a10310060308000700880e07140d90060003660b000030760f07410748104014421402500852801d040c8460702072450310b0000c2000002d9401540705508080010942c0d01d8031103030310301d07029a81c02104140c0d0380c5803e1110050341e1047c070100341c0c00440000900b0104034541c1c01001920b03c6440140d0b500c5003540f8121148003401c1e04420800b02c2d00348102d1885041803102c41c0c0340381c003450914010a9440e40000b030706d02841500101d00c20800443e0020381c00110901c04100c86195000921901c1021085540701a08085d120042400126441c8aa0359680e82c4000440d6008004a0b0034644e9160a4014903140a540003004141e5500d250000540c1c0f221006400c00c4003100607007803942040c0240080d41c08107000303c0e0042c044d0185894209030084040f03c00a00048058805001c6640c0c009490044e1082050340450000221283c0b81c2ca45013001610550080e1101c0d504d0388505541110020595801d181c0c00c04544490b15004110420039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 523643651 1250 523642401 523642417
    0x3041407180f11090d390f080c0102030a0807030b0405130b0106031a09090a060e0706030b041e18051204090e0a0506190932120f091203 60
    0x40460000c0307885070b81d007040320050480d00100c0a014001d41686030341c1c480c0c0c182d03c1e25402088440100072080750300203650b50301241e151000074003002d6001c01d81c807001c00b580d0101c5008a10051205644140107600c403c01e118550380180c008003c0c1d00e81c1103000303244040d08110a403030002080d01020010600702c45040c1e8101c2c09190038100d80fa020000e405100d14094212850705000521440c00a51060071641c200740c0c0c0b0400f031a00000e9240c11041080401c0e494022000f808091100c04c0b0345911103106000300c00000c0d040030342c903200b0b509142c0580c1d14600c43d4410003c400780017031300f44c25006155048001d041203850358107050208030304014002201c2e014510840d551450b208454080b01d66020300c43c3c0140c0c11034503e580102e000850650b42c0300044201400b00b40049401c01002081e001d2070007055100c403010247c0170f40102d4200c4038400c80d6420b0070400e00c8100d000e40c103a5103401c2c0400180107503c0c10007101c103014a2031030242800040180c4081c0701c00100300042800c68104401c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 523644901 1250 523643651 523643699
    0x21c0e0405130308060409050f0604030503090f0a05060a1107060f02041e0509070302030c0f04081b0927010204080106092003010b0403021c02040c08090f1203041407 73
    0x41925180380c603105641d0030500440305007100102c555009030102600508032803156546810300e500340282800041c000805a4041d80d6061820785406040d0341c00648412030030740b2a1003000301048030002129520250802c0080c14030b40d0ba0450340601801c2658803144074460203000601c0010300502860a142e040ca034800740e1a5801c154511110fa203101010799441c6813820820400c5803211842d50f81c201c04940b03070169490740c2d0500c14130203606c20419214400b842c0003c3c00982c5003404180b1761846501c0c0d80e0080301d02091765042044112080d500300380c0b440000700020896070f2003000c0c03600310002c5407000541083d58585c1020700f11030240d400745002903110031240130050340b5401c0d082c0c0d00c8041e80d0580350440d410107806005a000d140802030083d899902d07501d00e0b90040303640000e03c0a17401841840250000b801c003c0c407662060301c103211790307100b100c028041e550f50106050100000740c0c103036181155550f40720712504128015110015002e103c0c0080341746c00700c0340022898110816 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 523646151 1250 523644901 523644917
    0x307140f18240102030711040504030c151e0c120b1216081219030207030302120103080a0216122337020a0506070510020c0a0b0a1401060c03021c 64
    0x391100104003044165811900304001010015804801d0308030005015a0b00189c00c0d0358601e01a56082c003054006010341c1c0003c0c0d9661106202604291b204e816003c00450385001200714003000e440780303201c522020500d1141d880e803160320381e90f21040510304020310009010040801c1c540c18000043e12401600c101028180859001041041c0201a2a4048620f8102000f98400e1640100e03170b165000c00d034001807040f050611a40540b1210100c0f4012101156074a28024180ba4400000040036020303103004140080d02c4608800b0071185981612042000140c0c0c40b90700c40e00c030040b13841403100e042c201c0e103000c84401004002501c040040004008920903040c80c411600f0008070390b200701013050405070040e100d4005140881d401982c4041c0c44003031700d00d4114101500703c07990788011403012542c00007017500014601f0720140500a802015140c010326102510b4442e50050b2032018503134010051a445840046a8036000b03106840b448155003e14051088040e020000000d100b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 523647401 1250 523646151 523646191
    0x140a020c0a17250b1207030510053001060807061b030909020d09050a0302070f05060403050c09070908060408030601090608100303261806060307140f18 67
    0xa5004405081001d0512480c8440140b00340c2d980e01280d0020262460700925a042e8102c070000c2100190528130003443e201c0100c2c60300098034100480d00500000c2c106800315407600b61502d495020b50b100a8400c0c400f40300fa088002000b45001d450b030501d101241c24200603031800a200d070b0805840785101804055140440062020000c0024410880e40450100c40043d0b000060703402224003e84002da00d0304c40c1b05002000410309100083e21170b0256421400c01c140c2e01151401c1910005111103100b80c0c1c940b400e0004501076800020f014bd40070b18070002807885e2807220580e02c01600d15200003055110305000d030034007405a030102c418100c0441404415a0418043c101810051500f500c036860702c07010b690a4020103120103014850034842c600c203a03940d000c1e50702c20028444040d400f158201281c4d158410f810320070030a5003500540c004101c6900d0045550001c4404084680d800313040c0302e8041189200716014017a03030100c0c0000d6010b00c2c1541820380c4502c102d01c40b00b0800c01426903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 523648651 1250 523647401 523647409
    0x60e06010c0308071803142a0f010c15060504061211061615062111130f1d010c0f09031e0f03111513030c0c0b22052205040201140a020c 60
    0x40300c0230900305c101c00b04444420f6010019004400b42d804446104101050350010380d9640000d08019010951084034003c0e102840d8114400300c0e98240c0741000701c02d44d1820354002c881840d1a00404000e4420240314561070094081e0101710034182d44020800442d64030100050000c0c0c0e0440c52558688004120301075840103000144981c2000d800103c181035603615158021b01940503100c1c00d907408101e0103035a550b5010580c560414032040200704d4120036004000c0c5440c2886d40c9a0b9802c10a0030000e062041c2400b49156085440f001517181c11030351420412500360341000b119901203285040440c000444805606020ba240c20384402d0207010810300b016406100d42414201090520040c15021900d44001540600d00381c050201580741804007005280d1108621a00100c1c003401868451105a26481c00800710403810654a02c2800703240c1d140e8100445e00c00402040c0030a6800890300310350740c803500c1458802c0305547e1000c400c1059030800f0902c0c40060740009004440c0b414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 523649901 1250 523648651 523648663
    0x40204151202030103021f1101020d0e12040f15031b050901031a0901090e0a0b0907050306090607020d0c050c0a0b1801050f07020d0302160810060e06010c030807180314 74
    0x40001d006620b50344c196000b188043c0740c0040d01500c81c4080c80d07408059a4422110000460403141c029540c41c0c2085010700040c003103180d100304a5024405401c541c0c1040325040f0b0b01180c0380002682e03200d5203000c085000c4a1400480403042c035444020010500e03038840681f054424181d02c0c1c40c0e481d10300280004003151003c4140740328020700e40608804650703981c0d4005044030201d541c08205852800e90081c248602c90b04024486c08910b820300c03c6c101c5c0040307841c070140c4505a044036a9640c40b04440c582d070b200e051312004050b0300304540050101c1d104540000b8a40c3c062011108400940008240c0362601c6038058001d109000c1183d0322003400003da8011449000d10348141001841030208034980310300f20000b441060744100e0ba03c10103000b030252074810320000502002050ba02c0011640303402c0c045a1094086180200c04988030316418a15401400181d56020a0b44150303030301626403200190240c814000c0d101d039032a0300300140381200c0001d90f1043c417640d50b220102e411010302d445 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 523651151 1250 523649901 523649927
    0x2030a0518070e0a1107051510060e060306040603050f0606030d030c0e19080601090207050706090b0d090809060f091e0904080d02040504050f040c1e0308090f04020415 74
    0x8421600c044580140028002007600d40b0303040403681c141c4551001d039000700b90b411140d0b1700e0000045038041c280080444c01c175100700000d1400c00007950b02c0091a500764191030080602180382d42600400c070303042020140d5401000600006010313a00ca84074140b4000c081b41550a01d41d00460800070b03682018400011250804c2c01d041c080c0e0124401c01825884035444001c0c021444000c04000301c1c0715150049004002210075141d039940c44c0d815901c040c0d40240b105441c0e0384144440064030600c103001c84d0b0216a03001d459a420311100314a00409809000c2056851800c10b000000403640c40c04000c040c420403880c022035480c44590107002c030303103401c00304400c070007c1603144900d200f610340440d0740342c0c8540d20000780e6580d00039252041d002030040360001600f1520b003108100542c4c1d520345801b8021801913644c40c10700790765120300200e002103203064003a50400043d0204001071800b03014001d501c01c010209210f85015901042c100c0c2c00542c4144144e544400043c8501e98111605602e81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 523652401 1250 523651151 523651171
    0xd03050d14091b09280b040504030914060301030f0312151d0c18012007060c1e02060f2d1209070f061202122d090c040e10020c0102030a05 61
    0x5890130081c5d42c01440d021103103082c8000b0f002011540200e4140d40104103000b0014810043d030700b0a0b08009001d01d0650040420709803c4a00c08141d625000040d2812680d2145c00b01c070041c41c55a03811110407540749590740b4000d441c0d030720049076480d0b41950781020b003500117500c11100d100413030519074840c80540f038840303964030401401000218010070f03001d20713142c01e08011508014111588201207030141c2d07070b0070580c0100722006c07440359805060000e001d40209401c0d007401803122000c3c3c078041e021450080d1300010800c0252288032809010701140440130342e074540544103558000d0070381a000b4006000c20580042d8103401b40b44665046a00003400702d0042c141039050441608006689002d01e0080c01840403544808090740e4044400b000403101040b00142000c0440155059594a508101c80f41680c40c180c03103901c01c05280c0303104007102801840070001e01d50a10000b400e200040700568010310f00c03400c440740d02600090007005000b07800181d07a45825061201103900141c050300d40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 523653651 1250 523652401 523652419
    0xd060e0a0b0109030c06050f1b010516080f0a0e010b06070b040210020a081c02041806050102010c030b060412020114120615070b070f02031303030908070608060d03050d14091b 77
    0x4c076070040040806d555160038015660202d00102882600070305509407807540651805c90580d034019000580226085c2d0320030440550044801d64052500300e40c0e00940c01250400202220701541081c0c00810080e00009000071094020580c1c07a40811030a43d00c4400c91018001141003400c00d0302d0460b00c4610140481d040f890761015a1352040c0c220b00c2500254136460310b4070352102d5504640061000c03c40714500c5c4029a007031200078181074030500b40076501c1c10705610720a40c004e00460100050052016141c1401c2c803540307070301105042c0002d074100111107040e1355040304150000c1c22180c1c54000000070b686454401c020308414500e000f540f0012040c040c82c2c00041c444030200c2e4000f20b89040c07c110020118504a01d9401010b04111445441c80000028550450f009400391508003042d40c3c1403540f00d40d01035500d240281c0d8020b070050003c0d8500030110b44140003400c0170341d40304030740800d0000d0b40390100c40640c4030543d0b0410b1550400d103400101581804410040e11806444c1c4c299 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 523654901 1250 523653651 523653653
    0x30b010806010f0e060f0a08100c030e07050111030904050c0d050c09010c0807020f090a02070507140f0607081315020c0111030a0c0f060c02030c063102060d060e0a0b010903 76
    0xb4115054801e40c200d84e5554400b041040d0381d01000c0703603003110001e050041d071196030b40143c9503214081042c4011841c42c24544c0610302e4824001c06031106e00f840010040f041c64040110740000c1e1508181359030340030600000e101d0b9510341c02141e0044004203107868441598544071000c80e14050041110600c00308080080c90f42c0011181d0401900115503d484110741d002050546500f84001948030004608105141460307501400304103004108442c10942c80721460313088441441c04299000e0031504500b50340d03192500c001e0a030a07102d10400350501040a031130f800d820700c0c02e4010040080c48021041511030317040090a2030324074240b0740f030044c0c0706114403081e80324400c400f2564100050403002a0500240121007c0881d5100100b040701485240c002520381e042054400d403d4007d00f000304050040e21000980d16a034900d2140408005001c074010401c080d44100f00c0e00700000b40034030000b00b0710318450480206600b0750314544500e04400180100d0301107400040c140092024148 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 523656151 1250 523654901 523654919
    0x9031203150918030e06160503030a150f0b2503030b010e04021e1303050307120e030f06010902090f1e042306060d3309020c03090907050c030a0801030b01080601 71
    0x20203255018140b83c001c0005c2c041c00315a0520030495000080f01c59500346c2c0c420014004001c62096280c0e001c00c100c040c0480c190020034180502ca00361061810300c1041c44146c0b40b0748000d11000360804c107002c400c5407009024072410303a00c0b83c03802c0d030110b640c82842c0d90640d40c004142174190070085408514080000c4206492040d007104084195540490741c041c04013801070a50029642000459032146183c0c5002d00d04450b928100e44009404969150320500700055103441d10004500034044581c00c2c2406400250801c8007030a603c00c0d482c0f01e1070b00c000e480f5160509900000580d41c150052807a80501c002c0c0d41020714880100c02c0e0303013000c040c0325800c002300482e0803400c115000e40d40c1d035001003000c1001d02101404140003c454000d60100342100001007003c029031821818002070b940d0b1200703022400360720a9246650030421000446241240e0029404442070400c107003090b900000b542c0c515023007800080e0204040c84010701c14000314002190042c6884e100501103581062114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 523657401 1250 523656151 523656191
    0x41208011211040b0a1e09020301081f1416090f05030c0d02030321100506120105040e0703051c021006080712030c02030d0c02013903090312031509 65
    0xc0c108058540161081d030fa203603000721100240081c8030f540b207a500d40651011211140710601c1c4440000500041c014456000340da040303a95007400b8214111001780c2e515040f1001e408513a08007503803110440c1b1550811200b0030b0060b007000350b14401001040302c01608240c001e802c00043d00300b076017404205c0c42d82d001800461111003900c164954009a1010034918021002d0061980813406528075140d409921b030180300390795160800e080c0d640c3ea0700030b2100c3c0344240351181c3d18404154006000c1414142c10101a040254007100c1301143d480d256603062815500784031000d03005c0700c3c201562813603041083c8429003684100401085150881c2942e84000511500800342402914131051600610701140e0260300507041d902c880150350760040003840d50302401c90102e09441c0c480341c103804480b1b10104034001e030900001c000010480301c61150140c1c800c1c3c201c0401002035004800606280c0d5520341034130710354801007544c1c2085032107036001038030f40d41050358100e16110012204902136100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 523658651 1250 523657401 523657403
    0x80a050a1b2402040f06031b0305101a0c01090308061912030f110a050102040501080f04051f0b03010603061401151706060403020301021201170c01171e010305060412080112 76
    0x442c00714904804001e0029014076480b403200c5100104001503141e806400030108424503801114a0041c600b406170100e42c800c1c3c802004031288008140f0600c2e040d52840900241540455810984103010f0913081d127550303040440000d1154000c1c0252402c00762000c0c3d000c42480c3d4141c1e40b406092400305070b50f28843c41302c09000c200010b81c44812040c0030f14412001444808140d600700082e07824074038080e41c031603c501400141080001103085203440c280b180210b81c014050301040c4a04800828584a00c201c050794040da00c0154192540d400d1184a00035407240001103a10b00300c200d040d118014059000c1514940d100302c02070b45180c3d01c040b010001042c0ca8503000e000792503510100300075004c3c58200075051f62001a10203500000b1400ca14100d81c0d0101541c00301c44c0321364040c0c0d80c4820181013924042a010424a09500300030a0503e511060283e500e180402e010250403059100a91040e281a00303c081840140300c0020390200102c52107040c244444c0d4508405200c1d80042311070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 523659901 1250 523658651 523658693
    0x1b0e1b0d02090103091e03120903050a0e03070f08011d0c090a0e0a02060a1d033d1811010810050d02010903050f031b0604050a0f050a080a050a1b 64
    0x102e46080b42c0c020760281069640007240100380221045003120a501c0c090025004a9401e5019030084c201c1802080241641aa509400c004400380700351a1800c8116a480e0b15010b90100402c00c0d10503001d01500030460400081b4200099101401000d6100c49145426802c0011800303c99103400030220f8200498200025400011443c0c2c1803d100601e00c1c001d51000f030005203641100e52081c90102a0b114511b000c51114001d541090794405002c4095040401409002140100350601d4800001000b014000141051b18a101c0880340360130b849405900e031001204091100b0750142242c40002070800000500b010308168108a241e0b11840d07210b084220300140869118030517203c000c41d4020b040307824030f107410440d00b503c1c0d420a0980c5199031f8030f00000c624010500007002030181e034100001e0702c4c0c0001d09807524055140c1c3c10170240c95901c02d4800c0c060015804100408010345107983c2c683d2121540e00000302038005000c00d80c900156034644143c08100208020480c41400781 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 523661151 1250 523659901 523659907
    0x50411030f040f02030607202b020a0f21050f042c160f05040b0d0e071e0905090c22060e0c0c06010819030e010c1b0e1b0d02 55
    0x3c40e0148207a0000f000080d054041c03c4103008100390090201110748122036104100345461140c81d65845151005081c40680c8201a041c0a181d400c0c800c1d0010351820300c141c3e83d4204450325246100090388108954820700808000c003d170f5a442014a40b540040c0b03003003450031001413100e6285000300d000306030659403441c19600c0355502840000b01313a899218036035000f03483d00301814540b4100107480030022905008010400e5841101143c0035940c00881c4181010060140d01c402805540c10010302442290030105002e5914031b20868001440c07490400020b042c05000d03825908042c002e202d00d6072040c040100140d40300c0b40d000c1102c5240035000342261488010883c00343c903083e0b200e2558000450700b032008591010005041d050703c5c18007110382a03640e404190f9036414450b03030381504c10401170100303c000a20602c804c5004070014034201008107400d80b1240010840e00f084451200315403803007001000741003003036140d100308075a042c51504422514100494802c814907144a40c0e800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 523662401 1250 523661151 523661153
    0x61112040e0c091909050a020705061b160606060207050f03100f110a05091c0201080106120906021b010e011104060e042703090503012304060f0e0304030c050411030f04 74
    0x18038241c8060000c01440743c1300f41581c1c080380c04485289030103001201da050000041000ca414000ca50040317600c04000c2c265036403841700950b030b02e00b4080c0784100005d400308201000341c2c2c0e50906001c01c80340036540007d800c07071400c103000c1c0c078200140c0e2200380a11447c03401030074103035000306610301420030108010416800d6442c00000a1502942d20303080010049140248207600c80083d01421340d055980c0200c950ba20044100e0000303101da8000c0c000f90900c0700506c0100e208101c480e000c0203802c4d90100c0d000c4496038600d03050b608802c402c0182c0b82140401c590102c0400d0142880544607403008014210f4a0000c681d6240300350301440c0300380103a500d01c0e403000e51030316840390400c56550b41c0b42d001015044142c0c0c100403045010142d000034000e1201040b20301c0c06110b29004980140c40c404080c40ba6629140041712004005642072590355980d075113a22a80d00a00514001c103602071a0380714110320f04504038000c07907005107024502e401e4180500d80d2640044a400060505500c0c18075521 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 523663651 1250 523662401 523662421
    0x10903030e030f1f200714100f2c0d0e130f020a09140a090f090b0106021609110306040b06070602040e011d0f0c0a0c020d0c061112040e 60
    0x21418480c0c054468020007490102254042401c500200b100c10712060341c10324005195007406a245c001c0c480030402c1400d0025071100c19a10b05081c4060030741c0c00200310784140740d0451369013484a0480c40d8480507420301003105103842c0c941c0050164103074140c2c2c200282d0529994846100f618080c4487e5506c130a15540d42c60941c0c05d941901640b050201034032a0781e041c0702079000006058089400f480002c503400620f20395000080c00041c25044c5100d1801d4000e82c00b1b014240c0c1000e003115518001e18001c200705130000c901802c03a9070000c01c0290704100117030000048683c8804202ca1800f60b214400004200480350020760448010a40018000020f42d0610403040300a03c542c0c4001070015092908180d030504860040c141e414500e4030841c040204010304a91885800d41c2d10320001d4072100218020744559030f014a4a081b20391740b10390105084c0401902d0640311400704140c1003218a5104401c0400702c040d54000c5c0001c280441e4400c0c000340101c0c01002c40d0f14030004001894042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 523664901 1250 523663651 523663663
    0x10911070807050706090f03080a0c03140a110607090321020f03270405061c0813081b030f0307260f07050610050a0306020904020d05090f150105010903030e03 70
    0xc0c01c5000300b5950030162501507a1a0510710408003c1180c00900282031400032a12038104c03908030748810700d02516405c0849480c0f4030114114103000406000040d01001c40000d4a0520005e4440707642003100034400c14500100100b206080000700d0406200003a12840880503503e51806c4061702c01104400c01d81c02c050980702003000320700c00416034002d5601c0c09600c00d403181002130341031212000108240400d5070811561141c01242051020007505224982c01d8542e80c01410b00605013040d0300c40c0584c09a02c69407102646502c1250900d02d1442a0130740741102c004100c1c014519846036130300c815142d0183c0340c00030382400000e9110b03d05c4107103800701042035151000e803002d59480500f90945c009400120303050b107007403280f040001d841c1002000000c05071080281143ca807246140d80d998081d60016681c960003a0702800f01c1070380341c1d26074080c00e17000d2400d00002d090034603541302c10345203004803440c0361350312894a001c01003002d643c1200c50340e416a60035242c001a51400d100119242ca0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 523666151 1250 523664901 523664903
    0x2130b160809030f06070c1a1023041802040f090201020a08210f0106080711060a09050c0d0809030613080d090317040507080706050c1902240d0501050904050601091107 74
    0x4040c5c18200840b55900c254285415403140910380c1c49290881031a10184804543c1d11011001100c000d100c1d49006440c005c82d500400d058466615140001150545094507000840b040c400e084040442c40d150203650415000514208403160050300001d60341d200c800350284c00e446002518400c1042c44404003400103001181144041c20400300700e0035800e41c01d11410000504040104180602c1401c000140c1d00520005000030b884059401c0c0041c211103008807150f110710f501480c03080e00e55441c420030860241054541361101c01003814107242c0014446440b603580020504001410340003520481e41810b100001d40311b045180075942e905001e80078038038a0f509502000b0422070001032080603280283d060b544841da0f100f10a88950007200948601c0b038100010b20015945054a070300c0507240000c00041010850071440c2210045902491350b1850380003034000c040640702e009076070042a060322910000e2a00361181c1380c50f070006010750f008842e15881400f00340d41480043c0d80d000707 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 523667401 1250 523666151 523666153
    0x80f120a0f05070f050a02121912091d0402010e011e03051801021801021c090314070b040906060212120a0c02120f04090506030a0b0c09010c060204060302130b160809030f 75
    0xc81d130608005640c1d918500341288903101e000500010240003107000c041581401042c400524800d179219035803040c0480f030540c20001074000010318410086880b0040900d020f80701c055609141c0001040c4406e40381304039050109280040911002c01c4250721401d260310f19002416444000d4844e074581007420719401d5641c004100180c0602c4800640e29035103c090b02242c2c06c2c450420000301490444044500c0407402c540020008a9105401755000c0507400007550816601c880c0c80014903040341c0c1000c4140ca96a030018030078076404000c5054801e0340072015a003810580d0b010b07010304210040225901c0d6441d00c2c09030302c68500810602d1541800d40c0c480c0b5444403080b031540551908640303d1a160341d41024003184103810082000d140d01034025030403001ca03640b05ea04026441e84117600c200d04001d518068000444e69600c058000b07005070756009039540c1d06164020480360510f40102c442c0c4a41040003510440d899018441d246a2100809488140c45000682040b41c1130b28403c0e11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 523668651 1250 523667401 523667423
    0xa081b0304060b04060e01050303040308070c080f060901140610030c1e050705010f020a080f090c0d1a0601080106050a030f0b090f04050d1805041a10030501080f120a0f0507 76
    0x401c441c42e080040541c3d0141c1d000c008160b92051648080c0c00d085c440d1035015002000144040740a40c0010020a8012030200600c9a9503150003844d103030851a0b002c4180d00b140d000d01402903020300480c40c0000189610510f5820302c80006196400300c2c911503c10b266a488111060901440c0c0d40b00b100318045001d0801d020300320707001800b581c0c401d02d001c84055180c580b0619480e44940b00b9180c001c04035644031002e65a584c14000c1060002800050091043c4040382c460741e40d600842c425071a101da11480c0c89134070160b18034580d0303c1001e031603181801082e00c014010070349d014080c0d0341805124500801c080e0041c18481c0000c3c4603400309503401002d00002c1000b104900540f890080384184211b90143e01901400c6401d98081100141c0d5401101810055864507070081146541401050703404c000c110800214080c03941520507001c00e4584004201d441d10030700c03541c9000c100300c40241401206018a524142c41a03071101c20901011070407511845200c3d44c03d84450325480b5000f804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 523669901 1250 523668651 523668653
    0x219090203090d0903050d1416050a02130c020c1905130c0e0303070c03081b01090302010b19030203060103150b060a110c0a030803130204150e1b0a02030a081b0304 72
    0x4040e50085440ba69148920030940850922455580c0304898006c0060900041d41d4481140d44c559981c0100d02c0c82c080034008802c03041c02c20490380c0d80c018440d4000b4030030035900e841406044215402c0315003000c6d18011a090245402141c0c1c107081500c11101401a83d0070b103140103441c4e07201601b080c0e070000c3c48481c41548424a0368410b42ca00c039095115010540a9682010741e00c1c4141d942c010810300c8040010400100240050020031843d5505102c4e840e000015a900b180c0300500c5c10303070050307440300d410b00d80c281015038013503205060a000c4d030308d4001e086401007591040c06120041551050070280c840e4607030164082c04051400401c1c480d520140280020a810110910300d5010300442c1036034841842c08480080480340d201e507516041d0358440c4c042c82c0030962003c00c240c5c1c1054840c81c41081002440c1c0b1180c01400c9259044038144c28107103580c004403a58001d09000c000e00401c80031810743d4000003900c0103400c0c50b00c5c00e800d06680300003160352421500720303003a41101d0021003400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 523671151 1250 523669901 523669919
    0x181d0103020406170d050904060b0a0c120302030702031b07030203031c0f050610081e010b0c0c030604020d0b07050c060c0408060610080a1d0a05010b011e1403040219 73
    0x150490340216002e10400c0d407182d100103850080e09020551540c4200b60310902a80038902504600e20300400020b00d00b40d80e07003941078081d48038004002c0000c01c12000e481c1004440341c0003904900f510314045046140406000c0d603644100980c41d02012800400407000d581c08003e00c038041e541c054192500d80c40c55079a42d96031701030403d41404c200d41c1000d400c2e0340081c91510620b4440c02d0010302046c40041c040c0030036207000d44003809143c107001c3c8005240303c40c400d800101900902c55080120f0740c68260355449414050341e820b00754425005101403001581e110329150b168241c11011a0450341c40c1c020080d00c40b885a0283d95107140204000c002023118204050320858408030103590032551004104091200341030994008210701c036001c81c911043c180c0c040c540032400e0440c1b03002c011307040f10b0f48546058154030084426139110028100b03d03503071144040c1d10300e011414407240c5642840710702819001d202c65108400a4010000a040d9a29003010310500385071900910703421900e03a101c034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 523672401 1250 523671151 523671209
    0x7060608030325020a030c0510060b1902031314130504050616020a020109060518030f062205060c070215070b100b1312020f1206040303110a080718 65
    0x51208800580b220354004940380c002008480550303130107011005416074007900d80d5103104006581c0762107200310990301d61141c0c0c4106d0000d88013080c8542e4603081c5030810f20140c045011410070464005100c1ca41c0f052080c0c00d21001900d9600700300d804590514400300e400440b6007241c41100c03500304403c4c0030a010300891418044d8516443c06a03080c0c901c07220aa0b40c441081038028001000c84004018180c42540a0421054021078111030310b120300000902c0c01c080920100d0181d004a01440b844850481c40381024205a121084e0b0004064a03065211034005044800d00c000c00500340045555141402890011103080341d0389030980b50810301d9101c84c0440f03010782107070b000e540c01050450b041000d40303000c1c0310811031202e041c0c0d04000c0305460507503000300e04a0300000454500381c05070f07840d503003d15500c1d02910024502403a043c01d0080540e11600c0021203038010030000c82d64a168091314650b80b090241c01c2802500d1b0300c4203e14a00058990b01c0b00000c1c0c01501000070f500790780c25100d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 523673651 1250 523672401 523672411
    0x151103041424190b12030d050912040e07050702040f020a020d0810060324080f01050a090c050405270a1505060315090a05031c0f0605061b03070606080303 68
    0x300d034040001480d182098030003150810504900090000720214103900b0110b0810710f50706404190f0009582c0802c4182590034005011504082074403403020b0b041b840f07020745c007000420041014880c40e4071401f090713200b1801307440e042001500c00180c110380203c0840300002d6001c0c00801c100b0300c040014030002d400540c02c00300140900602041f4541c800d005280c020301c2100f0b98203102501c1c250003900101090051041000d030f8407244c40c8040a403088880000300b8105000e0b15043c800c3c09403690840d040107011114807032400c681c8801040758000d004040e85d1003a01c1c0040c2c0c0e81c0780c1103410100c2d1440c464041403452501d03600304200e403a002ca803800b049441a00b0308a4491545090724054800448219805074400c07213190b140080b6804056801050303560030b8444100072502d400c0e065074484240c650620702c0c0c06800481c0514903118200c500014004208682401c04002400300d209141c60121400340503016111010380c1401200e0580c0e0344440100407041d0f8440c0001c1d1a0b41080ba1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 523674901 1250 523673651 523673653
    0x1060c120c02010801150201110d060620060c03060301090210030b041d060a050612030d0510122015131d040807080d0216030207090e03161511030414 66
    0x403482034018024404159030590503120001c2c1a0f0a081d00c25500380d010052810841d900c61410700820040c2d207000b00090701440101003040d50802102400ca00e207810000c21621151260305804c40303001040071350f003146d000b07080c40e84c2d01d40350301000030302410004901a42c002800c1ca0400f0025402d40d020040001c0d00703850500c0300801030340d0521f05c4240b140c00040320940002c1f0003d90b03005e415501c11588124002c1c80300021034a00c641161540d040703c00e0036000b9654030418048580024191100203007031320207030448503030190380e07905c030084001742c02500903c1700d5010091525a40c01081880394501d0b0003409850314800003d282d02c03071200d0700c00d0b1003103003040984100c001455040502d2007640c0003500c2524200c1c90780e80d0403071349900c618441e22145500b8481c49140c000001242890140254020003060f42020303d010308079404168100b00070390041004400304581c090b00341d1036094001030f59041c0c0a907014001405040380302d980039281d000000812013040115141a5040c0c11610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 523676151 1250 523674901 523674923
    0xb0d14070807090903090b030a060f081f0b0f010828051506040302010207030b060406050a06031a060405010e1903080406050d230a0509010f0221061915051201060c 72
    0x3c80700d04200e803070609003c0c0c0081c1205e4800d2004120716001181c11841e5520002002952075503015078400c9650003100d9150081c0350100041820951918202280f000c410498414001c0000d0305c1003048203581418880504005004251505084140300340d8809c003143c0700b0818015034100034002100d4051402c48010030300d8070703541010429542621b034181c0060000328107548680f61031210040c441035000d3b440303c0d0013182c1919203070b25440090500e40c801091103045000c000000c1a51080c00c24094001400f00b080260b0344119100305841003030f22600750240d489148a046e0309125000609a2200000c0002e10745a0003001404a080014010000c1c0404030350030741528103140c4000c03000c1e4081034002c1030152505a0180b60000090340000440740d0300d89101c0002d07600100124810070b0100843c0c42810f0011210302d80d4894030072038003031962038141d904185081025014051b00d81d4001034100012500030401c680c44810b08502c08215981d40c0d0320000c01814821504a400324214 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 523677401 1250 523676151 523676159
    0x309080d050c061e01230301020a0302090f04051501051605240106050a17070e033003061311070f0f02010306061d0616061103040c0e09060a0b0d14070807 68
    0xc4054003c80f0110b10740681103170740381200e08207400ba6000c81c0d240b018144589500480c0d9001d03c000c01d104200d075200075031142076410411001c0c040105c2c405000368101020401d807106000d201444c0c848003420700c9500c0b21206500c46130080d1401400400300e00c00d0a42c043c0b900034504013424034140c80c0c0011000d1f00d81e00c1c1d0308121024010803034800d02180003d99517810b00303901c645583c1e0380000c035440c15410100501c00003d2600942c0c0962581d9035281403003441c403041189440450101e03032806030514500302803001c590f0403a0f85042040031039955070780400311610f42c4012100680d030810029420880f45040c10b18403280d09400032400b003481e11400240031030150351040c000380f58a229901c551703102034041c484150b000c0756442ca61250030789064000911036120320034031640640303061501e13450946083d00c00c108264006070030000006003040011440003c030f09922500081022a50301100c0300030520810303550f00003c240008885210040c03c600003001411640300000321500e0a9407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 523678651 1250 523677401 523677421
    0x903200a0501021f090311010f1d0c03190206040308070606230f120127060605120304140a0b190305150105070f0507050301021303050610061205040309080d050c06 72
    0xe0300c43c00d29912106941130740441c00d540d4050b04810b80130b41480c000000e95900d1090840d4040720031121b42c1c554600e40344842d08265071068540c000d103600100004842d01d00040d41d44d40c0d1405088803040043e8001c0300c11903c940707003035800950780145401c0d00c801d03141c42c16030058a01ca018022020401c42d40c4640745460a400c00301951342c010301199005400103090152944106001404a6485003043e82911080c40400c41000c000703030589030002481e600e00f4030143d540303d900ca9031141c00003180072181104040b04075800c030382076904404420440d45020405024050788001c0000e500495441b110031000c5640100b0701ea010317a01004244da6030007582522030440000c05000607024000c450000d5a9503203075140b031070700a80c222014150b071040002d0983c1e0110700301c95030030f5034200c5040041050400c000e0b60007980d14066410510308199000302800100f108054460b900c58012605050141d5080e03c040c0811348141d5510501c4048007601c0c1c0d51011228a03034a11401c4005002004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 523679901 1250 523678651 523678663
    0xc0f03031e040206070b13080a0201090515010b040509041e0305041e030c060f030f05011418010506030a090201030f050a0209030706230307090b12070e09250903200a050102 76
    0xf9009003554102034403903d1b00d2a00302401020f012200010703004c100089088800078047d54002580041407030305081c5800c80c2040800070030200300a070078000502500d00e00d0020342d0300380c0d4400c0d00e00440c2641c0e5401d019140d050740c0c0c011114181c00a22001061560080c0144181c4501d40c82c1180c0003d150f850740c14000b002440080c1c82c16100c1d00c1300b40310251290115a444035402d01c1c000c1000105950b000c13046907800e901641c0d81d8002c000c6820744908085c01101203d4040c50480c400c1d0358900f001240040c80010031101c42c05030346d80780d02000c5a02a500006004451078003c000a28060a0300e40095000081084c4170781b040e02400200c2c2c510840b40034035a040c0c0003035003a145095078407c0c0401c82d000a401c05081c8441e950000c01c07018042e901500014000d400030361943e0400603000342c03581460520181c00360820100f089034816014520440c00d43d0342000340035100b854504c04803207000040c0c000400030701c444e102840c90080d00e4510450120300403074a000c2603594807c010380e0781384 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 523681151 1250 523679901 523679903
    0x512040605150105070c0902130b0309010b010e0102070f0510030e010f09030905031f020705031608180117070f051b0f010b0301230408120702010f1116170c0f03031e04 74
    0x2046c00e4105114030441c0f60083c1503000200700103450825229504205203800488100215a544021503603c540c4d02000907403498500780050310015003083e000707601b0b01105024190096905411046955200c1e0740324080c0103040e9402040f14403160038031007018011112042c0e0024030300ea58041002d180200d107080c00040385502c40884c8121410b0000060b400000090300e4a00050202c010322410030716582d0001842000b00c560340b81c5080d5800048105000412030412680340c4522100c02011503500e50410141c0c01e107004001400c10382144e003480780981e030b080e2465513103c1c40c00010500290301a401c441543c02840f11044580a241c01c0b140c1110244400c541d0207260211008082402d080e00103000e01c0880d072505001526003c800c000644040c001070790f6070120001507880b03031b00c1045200b0016003030fa030b407a004044649075880d244010b0064600307850080e004904a90a00c200d444848024041c0d42104840401d12502c030b420468484074a2120742e81c9040c0c040040b99481d6200d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 523682401 1250 523681151 523681163
    0x1a01080601230d02060309060106090b0708030103080903071e170111030714040503010207081b0106030209063d120606020706110c091603180b0601030507051204060515010507 77
    0x110440b00303010a001508035040b070300101e400701d06001586901004501c07400c50300c00200350a5142c1200104541c0003544803c028010500c6410f000500b480101c1e0704503500403070560b48502c01c441c0000d05104181d401480ca03006008100c800c4525040300c54012640d4031305103c00251581d200486c2600c800260500c481d80c000c00001e88050b00400944a01110f1003813018113003601c1d4008a03089030f22900d0243d41052000c9010f101c68441080001c0082e400a0001d10100b032655002ca10325042c05480301d84500b0302050845205092030705945e640b5410024424181c019611104480c601d032090b50f2800100102410050010140038480c00c540039039000b0400d09292400441e0700114141c540201402601507090481d501d004500d0b001341308020b0ba507040d0300303038540d8040d00721816001280e80b1004004040b20114441841041d0300034801c0c2800b1800760b170b07086801c440c907201d40103d048904880c2c5040c00148175603035014620407400300c1141c003106c0030036200640e810b0040302001881 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 523683651 1250 523682401 523682429
    0x41a0307050910030c3302100b040f02030f090d091409150603160305130c030b13050f0f010b09040f11011809150e09371a01080601 58
    0x1450400e0600c40d5805000e00882d032010725102e0352070401d020070a031702540c1e04140c4604105051b591808121074018014240c00707121600006002c0d48484511491849065441c810100952221340180d00000b120082c1195245007000485a2025080e02c00d009607208018001080600500142c8150750143c605203c1c01c1c0100401c10032000c6000b0603100720301c6124520b003851511400f002c0c43c09806054040da032403040f81d91004088a0008041c0100c0d010740084130004110b0a05801080d40e402849040e0b4540e903030340c0060190041054018000d00c17900d01110013500010604400fa10b0840009201940204040080380e400c25078010b455088060710200015460344400e05400b40181000f81740c07040f152a0118020f0b0305540b00e40354068441460385107000e940400c0d50051710401c01c0e88040c174100081c0281d6903080d6462a08071205820701c25186400c5c2c810809a03680b40c10042c0346003401001d02c0c0c40c4400616040c10b280c40143c0540004c99150300100721236060350303144650040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 523684901 1250 523683651 523683659
    0x1509060e090d1b02270402090a1e090602160c09060602031e031f08010c020613081903020d09060603140d02033903040513020f040b0f0d09030e041a0307 67
    0xb9411850740c8003203911100c4d00d8411121407059018030803c0f54031340381712440e45182c54014451100302c01400da02e02c540c0342800d01590800d50b5070703800c14160b829800014009001d854810024030170403420110a400d01103010040100c484820401e454044409100301035907290305076541d0040d101e10746001a0000711401c18200c050000d10ba201101c3c031808112003d102044101713202c034681182c1b41c203946803001c00b0304041c1c04000264100c1090007002c0c165503001d4a0b81051800383ca0462042108a580100c1446209405441d01e42156140c100602500c51030000028200c901c0200c9410303607500c4a8402482012903140400d05580d005140351481200704080143c6d8a00c8481807c45880c201c03034000c0c2c42031030201c045135600140007155030350704210801850100041600202030700410407000c440500c5010784044800c24241d207911400c0150f00c110b02802a078514141152600c0141e90a25601c200c007a201c070042030b40c04025030215425034000c846c0c004401c40b0f0301507102e1a4200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 523686151 1250 523684901 523684937
    0x40603020f09040912030b0909030717390a111c081b06340306030501090f0303180c05060309011b11070617070c061509060e090d 57
    0x2111540507100300e49890320003000681241e02d252019155034039203508102c4420781504c5511030441046a211a0038604504903030394074881d0500042c882410b10441c2140100c50400350742c00c1c100c680c680b1840504a0206420303414068282800e618102d04000b000e1030030020039011001e54000844602c401207440500824100c03c02c00c00c5107440c0c07004000004141070030040e000d0300b41c010108600341c010a88007039140c800058280280320201041c086007400b00d044489164800490a0316410500c0c05400e03001800380c0d40c4050015403d0002c00b000304440f4440c0c0d80366a5109403420007082c02441c98403101c007001000000c00c02083c2c0a4184810316144016561010110002040c0c034421468a908910b41124080b40415450f0303070074855007403060007071030b01400c42858421042c600d0324111a0700070398054050400d0103041d00da80c006021460300070300b4450380280704071080e040d607900c40c40c0014601c2e480b540000d03c1186000c105500f401045804c0384550701d0b96250807a00a40e0960 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 523687401 1250 523686151 523686157
    0xf0e09211605031306031a030f1c090b030f1f051e0622030c0b070201050d050907051002030a031802010804080315090a0b18071d0d06240807030804060302 68
    0x64070144024068004400f40c8902c40708083e0500340d034040f0b140c4100805048160015034002d6110789c012011101c101c1c0b80c0002c110004401f500c540383e04400240f6000d8440703219035007280603040f40c0001004a8034800042e10b0380218019024042d401c6401e01d9030310034000440c0245580b01c0020102c5110002d40e50405990502d070003003800d0302e44440200d44a41c0600700c2404c94040c0743d24810f080082c0282c0c18801e0b0001e10925012915100003940000c020384649070403491020b960b08081200c2000400501001c0c04001e420a403079811030641c00780d5270390410111580000e04080040110451103540203d8066040e11500c06c103443c0c0d99503002e49ca0708000c15411130341c900c54088868955901010714054902000f00156820a0302d051120740024031120040103c030a0041c01010755100d0f2114000420601960402c40203220000f40203544001010f0825401c0800721900145510b14040714044c4941c0181055a134862405468005902c0017070060401800200a00c9011b5002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 523688651 1250 523687401 523687403
    0x606011e110d020703050d0206040206070204050703092a0f030f260d0b0411070f02090702010212010e150904030e09060105090607240603050601140a0f0e092116 71
    0x40341c08603050035418075103040d400303081c0040140d100c41000c1060100c2400003900519891000c0c0c11146081e4000c00c40742c1c442d80c503001740101e41d01d40000703c80e14400d502040016500090281c1000da07a41c000c030101018040452101c4600c0c180c0000b0012168031070101204e5111070440303844040e544030302d00040208103203120340000c00130340d000104001e040140366591544070b0000d204407600c014031085486d5a020a03a011408002c02000f00d5090f108402c104d0f6412070f4807400e60703170320310604a0290103048044a201d00c6074900108890a042100a125101c003030144402072880208200c43d6160586020700440d01ca01200300c0c1a050512000703a0011043c10300500c1c0c00f080002084c06588078000070356401100c8001800c07811600c8d188402c000d40c00c000300707100c001d0468403030710745a84040c41081c1003018508114261b43c0c075000420001051200710301080306543d40c9888085040c01c60f03007419603000d42d07542421142884c61502800400003030742c0a082440852440e0f24000684d90 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 523689901 1250 523688651 523688657
    0x41107031706150f0d0c03020309250b040b040503010c03110d1815020d0e16060e040e0616023c0106030602030702030d113604051312020606011e 64
    0x807070a5150400c070f8006003841228045459a20b842c055940c404480703580821714109801001880b502c07003c0080c000703049404401620010040c1c40c1d107082d2460340954002444c03080301040000710701030400082d10450f039080d0002d0004d641c1c2e00b9021411150780340c0d5460904202032020119503606580038a5642c0003600b040c1e880d20341c1075250740d009600318084c0c101645800140001c4248098000d1031910800c107001441403003182040030b01079040a0107001c1c10000c44400503002076440b500800c503100c2d191750903030f034950600b0f40070300c040c8142110799000540729400321a01142d560490003042c810080003401c40b14402c0c001144008002004c8251a56498550210100b5002e100460040c0c0542c0c000b955901100400c800542d00100307140e03030140c002409002c0c221892086162409400744001280159490540824000980c00f61030307009403800040102110305240b154008030302800460300459030f03800d0100e039580c0044807a0307400605150103000610841314003a603803e5030981 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 523691151 1250 523689901 523689919
    0x3304030908100902010f1707180306110405010f090302060403151b030b120601152001050411090f06011403070207080f060f0f010b0405060901090b03040b0402041107031706 76
    0xc100c0d185002d20000400d1401996030240d50115038000f5001126940141041e542d40c05001841d0048280300901140a1001c0c01c03005d802444400001403001d15403000e810050080520208600d542141c00b4003404107203201e209001c41d5028555034070450341d005010700d10749800c5940b40840340b045c3c101829000c0782c4407603080c2009543d5050300c80302004035680024000105000300b02c4568203103c0040302d1600910010300a42c2040801000c200300b140c107065480c2010001c05010300b680890001c4165443c0005000400400100680090008480306211503e44410040c172410007a00ea09021130519040c5419a07840030000c2c591021450044c0c0d0103682e903508070b01e824088181c8004410f5003110302003016400301d90000e07641000302ea030300480c660760412015602c6031045002c0c41d8482c407808641d1480c40d81c03180340c4610242010746c50340342d01d030704007840d02e1a02242c2c1942c08034401e0341841e075407100174844201550a00c5070075907542c51407184820802d09100c98044c185c95000f510360 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 523692401 1250 523691151 523691159
    0x30a0903030b1c08090a331b110604051201050118020a020c01081503031c150312052a0d0e0102030903120d090c030506070201060503060f0619090c02010c0233040309 73
    0x42d140d0800d1049248085001c4418075042c6100305649514502e01409038890f032400303080714107000c20310a459009d2a2960001c00800005030f060181d640310b00c0c0e0002c4509400340e6068419000b00d4120350a4500719a4842c43c00341800080e405000c001500590010880c1c200c03543c80b5600075500442d203088000141224400802e0460b8001c81c102d4070791050024401d035084541e8440e060080606401550320281142c2d9000d074201e5003002c45c40704102010408549800420450220841204007041c600d0301940380c040791200300c0b000d02d0303070003281d444569640c43d940048111094008003c01a2403d1461300c00c498001740c0040e1941d034242c0f95112507800008103100b10342e90245000f00014007651030700520090075140301d60040d5004c0e0300082c0070f01100071010790700c0da80c204000f140d4144108110300c0d15070a01801d240e100d414000d0505848910752901035103d413075920b2003a400c2c1c0b42070703101a1403001c5a13014018854241a00846186000d0040c004c101c190001d110749070000c00740303583d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 523693651 1250 523692401 523692419
    0xe150d0215090f12060f071b24050403050a05160203070b030f011505030612013b03040506030a09050f12030f0609130201081506030a0903030b1c08090a 67
    0x100c800310007600c1600103072924603483c000180c02c0d0084412a0f241040403110314605031070b03c078050f060700814201c00001c81c1d00c147c051020000d0100d203501c54072890b42554207046000200e5001044041d0094440b5036028090a02409200360b030181c96a52408140040c201d83c142d000080a1b541c0e224510b21f41c41c0143c0c0d003800900300504803080c4080e04c0c1d0400c1c0c044142e4590044e4003000c0504500340d000e140f074642005c1501e40c0301100b144c4510200c920140898058925100d00c0b1111400724000111b400320140701c2105803444100d000c00c205580400903954038469409527651205c002e00008114048680241c0c011911890030343e00794800d40c9035050f103040d44504a48400c4400401006448503002d034203da4001d80880f007258031803d040001c100b480942d01c40c040c1c1013110850001340b10140e56500b00c0c0c54140064041d55803440d11500c4000101241481200002d0418044030800d10308010782d1008882c032110b8a401001a90341c1b80c41c643d5200c00b43c0640c00c40c4505a001403d103070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 523694901 1250 523693651 523693669
    0x6060403060207110405060a03050a080f0409140117190b0406060b0a0e010f050415080c2104150b060f1e0703030b03060a020f090d14340e150d02 64
    0x11184410100030644c09081000b0f4580041100e80602c5003540100081040002c4a80c0415040b60070583d0390540017034a40d01d14400d5030416420181424681e00016201c20b904030304a03400c1c249080c48101d1040700081d100d60706000ca400c2800e071910400c60201d20050519500688683c0000840c9541c408210340030b40c00080039032010840858645d189940c01c101d00b030100050300d11b440c034500b03401c2c0f0184030382100025070010708204403c800030700000e081c04210307841e0b0298034950401903452200704050f411360845044071803440308a140500da22043c000c20484203002852541800d803013160004183c0c00c00c2030000d4180e0307802642c0b00300013803001c401001901c1c001e03503000c076008a02e8030a0500c0c020014110f0140a48100119030f406c4811005440d07460404517071340038a00380745051081010401000400c068050203820f48503460b0342c5a100e80048004c0080004440c0c0b07045101c080d8001144100d445c1c07004004000741103410442c019044c440f0004091554a445640110388030701 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 523696151 1250 523694901 523694903
    0xd032309061008070f0b0714010203091b0901081510030209070905040c0215010504020702010507020621090307020d060b19060f02160f03121b06290d030806060403060207 75
    0x50005028001c4100031080b4400c0075140700002032035040d140603100c021054a42c03045214000c8042810400c014071b88041700404c901c908000d54803810459a07c546448044000c03102c07103004910b044425085c03007070815040b103c3c0c08001d44003500d1240300d4040c030010000c0c07810b41e101d5030240002c001079880380101030180e949a40c50381c40352802c013001e00c021600202d85400c03d40d032085920502c0412902c500310b0648006480150310307a9141d200680c2c60f405080c034000d5012901080c3c824100c0e800e000314414015034030541241c583c0710000c842ea16445004030280d0400d0042e249140814840d800000b5a04009041d48aa401c107541c00b200300000560440c90000715000f0800d240c043c2c0c100143e49018804407858404d0b02d241c0600030f452002d10f40700080c4000c00812140c0300703c4d03000e0403c0301040108407019004040030744c07800314001d1050501255415400d91040d00751207180c062108007850001c3d082d1401140107132000d842c3c40e1001444654418010807000c00021070f9400901005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 523697401 1250 523696151 523696153
    0x2220803270a05060a1206080a020102150903030112080c011803030605030d05031614030108070501030c030c0507060e07080a05010930050a030b040c18050406080d032309 75
    0x140d415140c4840c000d40c04a0007404003124080c064284503903607003103442c040b00c100b01e0702c135980c03100c0340315042d0b885d94652a0b54289141c540900012244808180380b070026100340d0a444a80911441c0a100c0ca54256031041f0141d00601c01402540d2042002504c402c0c0201086400d005070368404a0949881020f82c104401740348240380300f090b42600880000c0c00080b4040c1c0b2540003003450007071090000074280b020b101f140303441c040030640c0190f9143c03c0c403c0390031307403810307600d42c0c551004646d0380380c20388607160029140c024420b04145c40f0f441005000760641c1e84103803400f841912048090810800b55418501a4050004405004000c0084000e10440011130802098144540300354a07901110f0340d40b21294290045104e07914154140c80d019500780182c0314400d41004034000d00101c080f807a00640307000b0030414903607001411180003074200e041f0080b01e00d0300e40d020702003664098460318000e80d0040d101044040d0294001d094121500708011800c0e0554202107050000151464411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 523698651 1250 523697401 523697407
    0x4080d0e0c0f040b0d0f0c030515010e09070e16021c0c1103010507050a0507050c060a111b01021c26061002011503060c020c130615031b0302220803 65
    0x1d4200100b40c018420360454040040e8150340303002c220f1101c43c0c1c4600400a00742d5040309010420f8012160700610303080802c0341c41920300d542d14200043d000f070052080706080e490010365050070000e4170030243c500040d0f000030640c40d50f0480040b00b4220141c400c0541c003c207028810706e2003040030303001145001c40d074480c00000098102011030840ea01840c1d0300a90520301044100781d00301c01140c002444ae460056903c60407030420034100b00c080c0780b045602107030000d04900750030303400800590000e90082c1034500540c6c4c000ca504c81c50010301c1085a015070005500e800048071710101c41c02d031110342d9040480b0403010003218001c03200c95076031602d4121405c1005000440c203140c1c9a181480c84140000c02c807085c0c00c100c80001c41100d521009000303d4031500e170640103910900c03000340380034800342821651202c0302d86101e0140c0454054903006080040c0186480391180c0588003020310403a800552800d81401e00701e0195020902c0d03c02192901070b0140c450f403040c540c809c8003d029880c086d5403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 523699901 1250 523698651 523698673
    0x191505010b0406110d0906050f071b090e0703020a0501111203090606120606031f0213080106030c05061c11040509090a140c130203060d052b0e1305091c08180607140304080d0e 77
    0x4101c0d2940708a111b37981e40030318000d00041e111603c100e010399809003840302c003075181c10360f00340d02e03201040403465070409001c07003032002e0a08001042c600602c01180c2012002c90041841940d03054100c03052a850361002114860340e00c2400444001c0d000510405441c1400790140c11040440c5540300c0f01090395902001c00070301a40051a00150908640440c80c001c00917115007a0b115500032840c00c1c0d180d8600451508894500071a402808080c140f801c00e840c061112175140c1794203540503101c0c0c0d16648807105d040c9201081c0c5140240000f4409946041001d884200a400081075190404004211140810002c100b4000100c21410446130300028954550380001c0c1c11120f0f000c1401010751109c0c41a5a908100015659031030340002240c1e501d019856180030300901414851200c40480c503503200d94006010b174410081074031028800e4811007040c2d41e5505080300d8500005900c00c3c001346031020110b00454005005a04040c14603a0380220081128590f6400c0d00555009883e464 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 523701151 1250 523699901 523699919
    0x16030506011a041a04030b0a0f060b391903110d090905040609021302130b03220804030819020f010608191505010b0406110d0906050f071b 61
    0x64050701002c02c0200c0e100000c0765029000380107a018548030f005904901d01c0c41d02c400042640c00450700321229400a0402115180050030460080c0d03d074542040c00102c1d00300d20743c2040303507648003030070109070398820413500f0388004000a0250701e250f803090360007161032003841005081490aa5020070100c0c176000303407402501c150903c4418180e00d402a10240301c0143e0800a0303082154504100410690359a103403402c01408000d80083d0700509041d80c08000020703e6000e0544c1d6094449060b501e00e88034201511180001c0780c100c04040c5c01e484503a41d5030840b05035090141031148c40e216003025103a42c1c4100180c5c01c802111a540c03500281034100b100d0741002010994030040000b00412424a424143c44014910004c004007009041800800184d0350100c9030225000710208001d5840c0c04003162190310030320880002074a0103500035545030010480c0140131005413540c8801600e80a07040d21190040f0380081b11005050140a0101c0c41915002140c00fa0b400b609940460400c0460 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 523702401 1250 523701151 523701163
    0x5120f1b090112150e1504061d0c0d0611160f02280b030709080714010324090b040b0607050a0302060709140f0604030c06020d170613090501020408160305 68
    0x200342c0c0e8030302c14034501c400b04144d8901c003599820300400200c2c0342d000030f55043d460302c2a107801c00000120510100000d00c0200ea015280490003142c240340c038640310050465645100047e0300c4e520013000700c100400682c0c1c5030710600181d0300c00e110403401c02c044010f00440d0f0111500702035801108200700f0000b186841c00e00c0700880c220104101041e07200800a00d003294856005903120803200002003111980109407420003807820720215103034652102d00c0d14030040030903081d01340484c0c00c1420034104640703da90489050f08429000a1405143c040b00c1d00180030b0b14442c90f500655502000703500350b26500c0041031894000c00044c00c245805280c02850440014640002c01100a1042c00501d0002c40c5c0741720003610469205000d622440001401440345510007084204600c80014040b6004110680d2002c52034039600600240d4004442c4091000c81d0207541c0240d000d5003440340d4016540c44200c6a80c0100001810207840f18107082c9800e44102c08801c81003580c0d04c1c10000c1000030458 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 523703651 1250 523702401 523702409
    0x606230a020a021309110a060e04090219080319050901020a0611040302280801112a01020319150608010b03040611041202030105180a0b0403031515030f05040c05120f1b0901 76
    0x185803180c2c0d18121008104c42001442603100c0c90f15100cbd44e80c1503643c0c0317020b950030b0740b150354443c03003c07960395003002664940c021024a0300b0000690740140040307000e101910704400068014105110481ea0349a008285c0741d8030340328103420140408400750321143c90040c90303900c03414107000c50100c10b80b01c030441c07034112a48600c105a04240005074000110015a4818100025072250840b46003213a0101000754021980881d171000c0100410300340c402c1c1a181c00200340e60700070812100401046e01905c4228011000070034991401040306807091002140c4c42030082b4000110041c0210400410f94401c0d4040d40d4611419000b0320b06600c0c00780b00b81508900c10161580070b002d040e201761070321141300740c030090008200c080000c1c0c04d05009400c2860a00c405c010640001515801e170459481030104421000900c0e001e149070044083c0e1248a010b41d400802010190b494681001082c840c5d0350700c814447d000f400b036080e010140401449115007110b10545800c0300302c82c03042c0843c100c0c05a00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 523704901 1250 523703651 523703659
    0x3140f1207051902061c02070b0408090910030302060103080a020f0a060b010f03020405030a030c0f121806032009040f1803030e0a1113090f0311010606230a020a02130911 75
    0x10140e0f0059441104554a0b16180c0d01811407054008500c4002230281c55005400c00203002d003044200704d02440105504c1200300d0318500750340c86058050380002000e000042c05a8032003001032000c40c0c5400d0160203d00703000d104840030b8031050408182010740b5100d00b00d901c292140941862581c11020000d03607007a43c5c2c50b0441c202807821700001c0c2d64030260840074040c42258003042050182e0385c940e60241c50707000400d4403140ca40101b0014038000010851072102243c030000415201d1080c0545400301d0780600d26220301d5031005007106004e07402440d10719032080d9508000b0100b10101d02034164107150012484171200c8031810090700340c03a0780c1500c07082d483e003000c2400c800141803c03d011020080036034019110b003a40c410208001c01c0f01402c0035142c480320811107410103605c0000d5070f106441000091003190b030f90f00e80989142c44d0640b0460503100d041d50801ea151200c803400303010031540d24030494507040030b19004a00310205008080b0b12441e2103129240c1030214050311450703001c0b400c1d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 523706151 1250 523704901 523704943
    0x200319080307201005180f03160503090604080312010b120f071b03030b04200304082d07050f010606140c030d0c0c11010518090402040906020412140106060903140f120705 75
    0x441001d449200d40e900849d2040308800700300d02840001c200303a60880d00060a015581c54462030034030750365001110500d14440e01b860002c10404c80798003d407070004440d00d8407070010791152003e000e610f1740000e044c0030800c00d40981410003440540000c4100c00e000340c42c0040d1500076042400300390745601c0e80c031508109084410140322a41013046a131b0150300455810b4803400307080010040c0358030402d4940c450082045407a0304800303003030b0000c0001c907110b0002c5030340058002c4080c1d401c0c0e410a01c552400f00d00003030007034107213058240c000700507003d0b051082d83c5c0b41c03c01c5090207030103c40503c8008030000742d100b0440410807409000002540809081140c1400e1030700340c5a01084111603150390042c020743c8042411915030340c1001503650381c441c1c4299102c50b00d540306840c400508103030545e542c02c2c0400101fa8800010b00c501400d450555444025950454541c0c5610440001024083d07103d070020b112240783c020300154900621103070345e8a030307200c020b801c190340742255041507110030802907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 523707401 1250 523706151 523706173
    0x15010302010c080a050c03040e19060e0601030e120c0703030f0507201c03050d060911070f050304080106030809092215020720031908030720100518 65
    0xb0a6811500c1c03a4030001e05951140210350445450242c2140c0c1401403101080110701c41c5000700c601c1d841100b1056580400c0355404803554145c43c20780c030400d03501202c02c03008104154400d4001650051070341040381c5241c00d501091541980c4020b0645080740c0200030203004140d84054803086000c140d2505a081400e6510b034004c0e046401d0101c4844a4820303481c80c0d11035100c1a0740d0340003042e02114894060341c446d00b40a401e48d84040002e08001e450b043d000b24145640c0d20030a0308101d25484040c0c20044159a02901c0b1100440280d41d6444203100005d00f1010900495001d10711031601c1c140c980b03059200b408881c80c3d0203086000190360b11100c100e5800d0f070f0001d071900c4803504120024009801420460000e2003180e40c081c040305000d240100007010f03c0021710400c00416000c42e01e40a03600e05408168001d4800d008250600030004141d60910030356042c00301038100300c14040c851208400d410f16054040389035038001510b038420000c820208100441c4c2104504002d0103041a50b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 523708651 1250 523707401 523707407
    0x507080d150e04200d0f06090804031b0e06040501031101080604020f0a03021b010903080f04060b13051503010b0f1525110102010c08011206091b06021501030201 71
    0x24090520311581e621804450003079800c16124008051000010500e8141400c20718072011a12800103102c912401c001020f9041544c0f0b0314035403e4100064018642d2295624006406104002d8402e50740501010020541041c0c0392011045d40345907165034546410b103500e40040008020520a070703d04001000498003125100c100319000340303000c0c1042d030fa903440060024000c1410390f890788100410381c1c04039960503074010a14605555050108819941d8100b402e8603800c100050010792240c8c04180c0504180e842c05402c54070a0002290210590003c100e031804410200000b141e1a1010301007006c0810840c45c00e41d80003500203101c284071007004a085c0400491a940c002d000107410300015030b00d15000d42c1c2815540703a00240c0001d40325041d50441c50f040500641b2803214120180c00386600510401030900c800d5100d5400d43c1c2c0c0b030082c48060440104e2015500c041d11000c07400001143c2103c0c10244001000c004a0820b0074100003c0c43c014092103906100c1c61503800500150b070b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 523709901 1250 523708651 523708657
    0x90c03040201030c270501090b0c03040509040501023618070e0d32010227010c0c0306061427060d0b01060c110102060709030b1b190f050708 62
    0x5020b00f00840c1c040c03a60341040740c110142c0c4040f940e01d00c40c80c031a01085000150000c40c12100b0076621000c2c542c2e21501a40c81300e1080a80701030700c40c1e104000402c05420301400595006008400050a026000c0b0181c02c00451180380130468006110ba4040c0d941c44480920003b03600a40750b00c1150b480c41c0b0070902c043c1801808140901a03111151001960b400508000065000d44811500d82e800f1207206040e0300c0c980c403105c90071506541c201140003414401c0d81c00c075000200d4028402d031010500348008290300100c460400200110301030214500103401c0c0011b501c01c0070000340c05480c0ca82005c076440560940c5903c074040108444128020780040c03918032900e000c01d003441e03a4903400300150800a002e20000c0104110308000581300350042c82894000703024a4600801400080c01240c4901045a19101086d0032800610102e0490350b0305030780c00310001e409010341d040e1001c030b8101d8540219011148604100146103a1076070702ca000c141c80b48409080c1242042c1c080d07500d00d00030380 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 523711151 1250 523709901 523709903
    0x9010f080a0603050f0705040b01051905070c0b0c10110405010c1b051002010213060903030c0308090304082b0c0812090a021002100b120a110303191706090c0304 71
    0x62100860718000480e4480002564000102c40b00c50ba0600c1c2d0640d298030b030501c02c0a110b589000e184400b10b50103a401c0f1490703411900b1420180c09402d5105445030b0304610002d40b4240d0344070401083c8800044001c01c5150210b41c000c048006410028005803200c44502581c110f0b8240070800446c0d800c504000380319a03116050745007800e0551180d03000c2c01c00c81e50015501c8000d40a031405025010740c001c001d05002c82480342012502d07250309503120645440001d0003d4000c0f4401000300380700e83c8525420000c80400d403481c1c9951444081d180c2400034100489a0008421541c001d80a05a00c40c0341c1c000039042040c01458192103088441c000c042210014014035400500485400c1c420035501300c0d4000c0807118010054080255100c1c490200e10340320701e280c42c41000c2649040c400403000c1e018420028a8080300740c2e035800360a24500107500341c03d4481400704400601c20070f200864504501d590715003510712264003246164001400350b80c09804580c1c00e0291001001c0101c1c0c1d802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 523712401 1250 523711151 523711157
    0x2010e0d03020c03090907090e06150a050a0c0606080708060a050c030c0c010b03070e01050f01080c1b0a08033d0b0a02150a020307170f063313090209010f 68
    0x3c440c54404142184184084035034080141d0042000a50300038081c80e040d0384403103960030940d81d90b0038240b205a036100751801586000c107010ac208102d04c15402004802a41d180280c201c164079a5140f0640c4c41d1600407120540003903400380700c0c6140800c001070344885086001e001c01e007440604a01035100280401c0c001c3c0d1000a10007070204402d402c08ec03081100901110003181d5604800100c1c0344082c01150f04c54448118004c2c105d41c480c03030f482d90040c0c002c0c6e040c4a02d40443e0200704060b91044003001000d500410b82d40001040e11000a148140142203a20641038050020140e400b00420110010480c850b8001c1c540519880380e100d00340d0f419460f801d96147d14200c404d92400c00b094041440c01960441049030020040e0007650080c00e2a0300c2c0d5407e1140501601c200f0700d0012a24410384008900000b196071900c1655020680c010710859a5a800c1a240e003003100045100c8a024002d00040d007440011f40e51004800103042c0340340300710b003000003001c002051140004404020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 523713651 1250 523712401 523712407
    0x915120b090304081504150219181805071106040819050f180a08190b0606070209070c020109050913060c110102040306150e190507170108010b1002010e0d0302 70
    0x1d541001c208070f9000e829180100c40410500008110030031000715421694950382e00c0d18210000030304c1c02986d003034000440072a0717064600c00340c00315590704c0b4040c08000c1d040b5118500080742e03111100700e0881c80304c411034042a40d1901361006041d8001620020102c1c1d40300a0030000071403a030409440e04000d00c0c1c05010001e030b000301c9046556018181c00d061030040b001500f5100401c202021001c40c45083d150100c105030b0703502143d80c48940c09401c003483e80804000e2500014440030340140c3c03040c00106141c0c01c01d0955004124492411288200814440d003404010366800c400314034000d000445250840c0d240221410020821b075400040c8201c0d295010b5581c0d031800b4860340a01513031108003c54485a42c0e00708070019211468200c4030300015000e020030307111030400300c0600c269102140006101d0100420788003e10000344080100641030615403150441c1ea104e0781d0003052a500003080d106c54020800000d002260070000c1903a14000b1444941e90000c102c45440070203504005071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 523714901 1250 523713651 523713661
    0x918071505070b130210030218040207060f020406121512020409030e061909080c0a0b1c15030510090201020c2b23151b070506040c0915120b 62
    0x1120b0190340c074010101244881040b031500060003403042e00c14002c40306000110380c0740c030054040380706203104041b040b40141075400090509800802a06104080005900450b0038004c6c040341c001d50080b00004074031401c40f2a13519140c2c007c040407144c0a09601509900c2d01100e0106072500041c000e001d02d4941c2e41e880103140c01140c0c900f043c40800781c900340d510110114035403510000404003201041d60814007040d4040000340b80c10350b41e503018013030203101ea00f4414001026080f00c80c910b458903507035243c2d0301c100000c80d0095240298119039505481801c5140c01c604040b07081403582c3c03000e07260208450141c2c0e0f00007908036203a031081d54590903651180d00c150100080c400e00107011640e036000c0540410104400218454103802c0c200c0400d807100c1c0201e10380b03c0c0c8480c2440030005007810003042e030118141e200314800c0025003100a103061840c0c2d507020308280b001c603403c1c1c5000d00c2c20381c410042408207004104952014001d142d080d581000016054840c50000245ca01168203000030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 523716151 1250 523714901 523714907
    0x80402120307060606020f010f200f0409020c1605220509010e06040b07020d020706020307030f1e0c0605010f120803150603041212020f03181207050a0209180715 71
    0x240802d5001042800000d899a10207550750390032429000e56507290111106514040e032252781d9405000401f40b941c2403401d070014904035040790710900c1ca4100c1c01c0000082c2c51070a0300c0200740c00d40160001d440502c20b403206d424080a6140d010f14061810440500a5046259241c030401c0d1004000091680c0722036901d40d006100740c072005242c034814a03003407005100000b500c2d00e201d18a503600312003002404002c1240c0b2040f4a21450307025038810700100c00003034080c001d03000718922189403600e64a2a500e0340b10101c82240500c0d032003c103020076080d409001d154056075014084000b902c021003031404a0040c40600030360006003200c0004804210203c044039212502488001c00040c1c0b40e00305421b1480d6010001301c2c02501140d00381d142c0e82c02d10402070084e1540300c00d81612603425540c951800090341e01c074450098460780140842c5140020300c03403000d445501e001d031008141001951042c003800b642c0c0500109003903581e1880d600d2100f43c00040e00300035950050650508505c10700030a0f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 523717401 1250 523716151 523716157
    0x5070e0306060411090d030314010506120c390706020f03090405150904080a270e062805040b12121e031303030b09060a05010c02060706020c0f0d030c0804021203 71
    0x5d182c0c06000801400189940b6401c84409807024008045c16a40d13903004101d110b01c140224241d050600030300080d22482900064464038210440544107404601a010610840c80d010002c41ca418a40c0320a0143c200f000980040c02050000340395102150f074002d81da17030090340c00c131500c1552600300061056403409101410242c2c0035010b0716143c100f5290119007500300d040a540090740c4402040c0d04000c60402c403540d1212038001c1e03605c0d503174144801d0074207505004020701e03000050303800081400d90344248040030101115a0001c20710307003803000f000305641c0d401030810f118120708845110b0642d004111201d6540688141c0e40e07442c419404405022071002d035890140e000d0100070040350700300c04d074031890120b4480d945c20084030b0302080c00c2043c110b0003950f00707507004040001d040c411940100481d0403128001011182031041e10f81e1828182c0e409a0307800355164200d400d1780d02c183e0504010080c0070218134102486180c100c1a00140f034404010030191141c07408a0134604228004d00032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 523718651 1250 523717401 523717417
    0xe101101020408010e0609010c170601030e0d11010b01170c16050d02070603060504180311280308090303040b1501120e0a17070b0f0403030b03190605070e0306060411 73
    0x9540311941c3d0251a030080110030107074182c902030540015607800041c8181e501c0c01185444060704c0307205441c41410031020050600d81410b40c0c0342c0c418000c1510800c002d081c82090380d0703078820080c4880d040882c02d403502011a1030600222460480c0c803d92602c000303c0e4003400c42c80c40542c550080c00001c03031501e8002c4c41d0140c1180610b80039901000d03030105210040e80d410b42c4041c014266a9014001202c04031100d5205540c0c40050230030000303108003040c2081c4425501102c0c01021510203100000b000c1111244000343c140e0401c07010980c00240f45640300c00d030344000c3c500354509a1640b00f42668010119880003c00382c102c82421b0b03008031000144803400240401c00550007860f0641d840c0b1081c0310a07501d4260b800104202500c41004071040e0651054040080e501c8900c0c00110000d4046c204038145915240010442d860410000030360700d0040c0d02415149403141801011500b02030f101e14200000d40140c9442d0341c800180d12600020b05440c001001c1c41d98640b1411507014487c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 523719901 1250 523718651 523718653
    0x90308070c03050601050105071101031e0614040c0513030f05070e0108010203090105010b0406050a080c0f03040302031b0c0904110d0615181401120c0f03140d0806010e1011 76
    0xc105050100c03040010341524895011104681d8907840150394900031428010308903607001d418404c032940f103900005402100113424403892010100c90301d098034440e0b0040811540c06182ca04e14510380740c0280d20000302207061042c50b005400400f00400101400050201c80940c0034400c1000710811041008250b0b01841e900303556103409140b8041c1d0b00507500c4c2c243c1c03582400700203e00741c4901d00c120707402c40b44651182486c2c0781d110441500c81300c000821038070564809008495003101884002d6100f140322f42e01841d40d5441901303200d0007034600130400300c41640c0041e5999589480d080305090f00513400000443c0001400400229200300703140000700b54034207040008503c0c1d10303000d6510095031020846e45d9403452403002c0caa4110b8007544c0800064600001c0100000700b15180031800ea00d000f458208071058540d85115451b08403039004940080c0c1003881460f1101d0180442940441d41c0e1900c0d60503403c2040c0000d05503402c180c07086128040010700c2981c110f0191021060382c4030a04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 523721151 1250 523719901 523719907
    0x5040209091f12080a0f090f060e0f0d0302030405090a02090d06110c1c090504110409050903040b03040b040233090f18040b01060207180b010c06022a0d0816090308 72
    0x220340701c03da45d00b1401d114800324a100c10700348034070740c00740300c001044e621459882c55505280030b004036042d80403005840c0d0400a500b03100d101e1a19a641c2c104825400780e0029035032140b0701000d1140c81c08000341900205c2c1d1051000c0107503940c03000c00000625401c524086440d03a03072004420b81c584980041c03011188200481e207046401440d2a0b8011940c43c1c3d1290f16005680380288026181c150940c040f240301c0401080c00755050f11350150750400b0400d812a803e1a0b11500303c1c1c4c2465105580c1515180d001400308811450400d50b105581411b080c0c0101d040c0070583c29041c480d4085a10301c030400c0d5070104142900f61940d0101c106005e8004103102003052803100031b1101c1510580c0d080d1500000c2e540049000c500002c2c80e2070407150580d407000d540c8202d200d981402421441e00c0b150401c002c180c0c2440210307080c2e0024148a05c201600542c8020b804465481a904c20264000a540002248090641d000342c40582d00000000c4c805541d03401b803041c03c8880891607000144401404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 523722401 1250 523721151 523721153
    0x110f040203100f14090115020705060307020606030c1e130f110409111905031306141015021018020301050c0d0f090c05011d03060115080105040209091f12 68
    0x550320204450f0b103202100c8181303495480c080c090010400b015a0041c4140c00104608440e00100c1070450182c0d10648801a8443c000644958819210440182e02c0344040c06071600e0305200f136800071182101d02c2c52080104080440c250300e182e0b00158891480c61a0400c081c860076008102111000501003000e1032031080e5454035500b20b0f00802036050b10b400284c6504035581c0301214500039505503c852400c0c503a9000f100c00e0780c00180301d50903800074080b9500000340c05006182c10507103031031806840c0345400b450000014280e68010403499403100010b0422680105003410405044c10010a00090b2011240350a00812030300a4056107440104410b00e912000585520341685400344544098040110192030b03003d1009045c4807005101044903600071403641c080044155a41210300c10100001380c200300003644070564200382c0b81640030009501c00309050142100b100c0850070705c100f06020400101c5e00074150780c04001006851403d000c10900c40b00d0003448106064400c400c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 523723651 1250 523722401 523722421
    0x206130b180f070305060c13030212010225030e1008010b21040b040212060105060a21112a030d0e0703080f120f040f020402161704080c091003110f040203 68
    0xd04c81503030a4041c81010480d9008500c040b5100c51000c0c0c07005148580c21030f000c1004070012202c807031640d0342d8204404000b00c0c4992007050404c1d94055000322141e540340c1406404006019a941e200d0407050040c0d8020a0700281e400d030540b840081842c0c2c031503020043c01300000d501d850420301c46081c108200810050550041c0348114400d07100031030f8007090625125a10b01b802e0041c0da82c407480034082000c4407031284001c803c012844142e402070170009a0142412a04138000d42c10401c100012030180c0326445030142d54a8030519080b800001c071448c81690388a0043c08524400192203e284005460080050201031600003600329500c100420060003a42d101c02c903030031806001c1600242c1d10640200320380388541d03000450030800a245a01300402075106c0c000c501282d011011031000803c058071559400703c00201d03982552a414000c0c61840d1a1401180c18410421402040a121030003080d81c0f044076032108440c6031252030f40d80002d0041680400d825003041c4007000700700300019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 523724901 1250 523723651 523723663
    0x70803030a1505010c0f0f02010c020d0c061d0a05060327030c071d040308060301110c0105190c120203101809030e032a0301180f0b01060206130b180f 66
    0xd00360745400201d90765400651710104d502101601c0001c0b60191600406d080d0080c41e024944140b4042100825a60000d518624201003d99400650000912035190400030360400461540040604d1075501e0000444445030341c0142d500a140c0031000c1070071350010408100b01195a50002620001503410391a0340b50001c1300b4544c1c1034850b19100140741d42c05c21b07069254038400070b05001801d070380710707242a541d40c100074080b1505136689200054080e40e220f070103000003030041c100100700c5041c03007444440b0103e401070494401a01d0a0651050b89804c140c03290401d466032500540c07130340e8621131101440000ca5024520590300034100403140c85017036100218140c46900d0b0202e5851102050584e01e1084080780014041120b280400c040700880001c00e012a00030008541200408624400f00100c81c0c0101c8000f900841c0b91400c1184041d0b01d280036044034030040921703140006850000000402010b020403402030046104090326010f01e07007189800404840c88580f001c060340c2e0790b0b00c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 523726151 1250 523724901 523724921
    0x7150203041b050d0b13260d140601021c121a01200624040609052205032a060412031a10030519182d060b03070803030a 53
    0x1500c288003c41c3c1c900e4800f40800400307410800c40da000d680d41c0340c0385c0c0703140c0e021554050303c685058203d03a0541400d91019101c101105064080e100c04107102c40505468692180e09010030303070701081018603640060141c4000504080c01e8218181c0c610b010f8840c40c62104c1550113886c00e000b0800d400f8950000d12111100c02031f0b036499100551680c0503400a100c80060017101d4001c0c1001ca02c0e440003004242501d800a40c15031401c0400f03004c0011b0880b002544051140340e1900204518040426007460740c00400745810344502c0810307034910741c81c0d1098814440f92001141c48601000b0340c00079103616420104800c2320164182801c06079000461009440006030800e080300c40d0700c0c04581c060713410440c00680704400381c0018034405d802508004094803405401c0c58000050702d07069009002101d001c0f0030700c3c180d507101982081c0c2c6105100d03031a0800b108220388020300b614800c1800d12420a0f0708040002002c4a03940002803e050240c0d20846461001005001c003c2541d64400c1c2140c2d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 523727401 1250 523726151 523726193
    0x20325050306010c170c070906030201020f06010b030a0203040c080a050a0203010f06030c12031119020306061005030402040b0f2e021c03150308070311060a050118020715020304 78
    0xa945082003120148021214240002e00200941c00001c0340c0ca26509081514040654100543c80f05420f2030310b010740c1d001c070003815101c01c4108150b50f0107100036000d244d1454007031b0407950b05050702c681c19484040c0c9103541407640080040d0170310141000f0302c0c000e418000151140405e00382042c0e84e440c1841c0405074401d51924012141400302882420101c941c084a04400140380c1054120240c03e00e40c426414060300da0300341aa808024082e40f0b080c4007404213030442282c00760050601e08000200503074045c00845072404e40f05900602600d40c055811600030554000d03150100f01703000400022103800c002c0c545002407850421594a4046a10038859401030841142007260740d0340c1c110030708805440769401c2c007a504078485d40181c410450120303080c1e005250340c0c0c0d44036021544101010750000f16800d298048144090150342d4006070b00e1031042c0190350400065014085240d49500d032541ea0006d142401c00103107206552022080c40340c11522131a1a04003005c411000710101885 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 523728651 1250 523727401 523727461
    0x201020c0904050c0a17100e25090f060b042310050405030127080c19030302040303030506010201060609170a02090f04021201020c0d08090a061a0f0103020405240c010203 75
    0x4103a074181c0301940d1005d14600034002c0c4500010980010045000c0d101403e00891507030501d0140250704041e844800c1c0c520841e00a48ad10708d0950446942c07900c49a011400c1400c200070482040c01900c0c2910300c1c030242403000d2820140400e8849410020264021140d00c200003403054104028000f120020307002440a991007041042c0001e00444040e80341c0d0802c8440703000410000f038080c14040c00464221042d0203440500c134016214500c1084002a030009424400c01d030381030003480c1c0c0055082c0000d10056041040241071042d003401500b0106405102d003c20000c8100034034915a40c003c2c04466440c20300c006020b8240034216801c0c2c0c0605c003000c0710311070305600500c01c894003031215030b002d800d000100c00c200322494a8041c08040082c4500c042501c0894030340c0c400c051030349240c100741404544d03805092001e0204680080f0f0705140c4107100800243c0c0740c100742d182c140352480c0038110f0401302c40800d641e083e0150700020101c80d032000c000c0001d2510074100415907091401e0083d01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 523729901 1250 523728651 523728659
    0x1b0705031018031b0b0f0406140621030904020f0c0105090a0c12020d05061302090115051e0c0d0e0a05060309150a0216050c0901090204030305160201020c0904050c0a 73
    0x182c4519250b045200c072955400d001c042880703484005500c61a5035200240130340c05490b0002064015207076004d08200100038441082190310801c1d851681e001d10100c154a80000080c1e0300800e0300344035204407595202c0369a0318080c240105c42c0740d41c1c002482151960007440d440c007103c2c1c001c0f56080e001c944c42e040118120403c001400f1500c0f80c0d00418541400e400e0105008078144481000c07600411032840d000c0001e44244815480b641031f040780c0381100e0b106401084403620042e8000c83c41e1109079506400d0007540301007111905429a40e428204091240c1244418880c43c40207400c00d000701c0c404a48141d502c82c1c4220031084046800360307a13040c0c96408200d56844103443e81c00c41175120700541c1032a40c0c40f41810344c0c0d00c0112000300500342003805085141c48004044222120f4004440030320540c60140c01d981d0141040c20004c41c10075056030380182040c03140c004040240304004170f04034210fa02c2048200d407054005810200306040030320340955105104042c05100301c005e140e0120b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 523731151 1250 523729901 523729933
    0x6050a150b0409060807261c0c020315160c0203150c0a110111160201030605040608010b0a0b0304030c030c14150105091303050412110901030503040e0c131a1b070503 73
    0x50613507c4140b0000f1240d0080701c0842d03420501c1d0800341c506805034491402d00601c00b2034000400c500c41da00e6802c00340b060381c41058104215418111248070f111400d0010660905070101c0c800300141c1014410f0070010300001e45082d04402401403510300c0340e010040d104140c880030b04144000d94071000203414114040c43e003610f40151121020340c03c1030001c6005c0c0c0e51108c03180f1603040e00605001907055181c00101d01541c106410591160303440b80404a5070342041170402c001092000d14180c21070030140c0c0c0050014512410107400c100d003800d410030510000c03580c40d64900d282d0100322003501e140c904d8404a4010240b0070184500368100028451681c2c001c1120381240c2d01d40d4034071b80740600309140c0002c0b41c00207010544d0b0341d4410300a00041500e890328410301840c0580011510386141c1002c0c860520b00c02012403004060502c0301c1c070401c400020742c6406a0b40c0e500480d100700801050840880c1c000d4030400b401d02681d6180044020310041070000aa9806809603400c010104403c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 523732401 1250 523731151 523731163
    0x2160305060a0906151e050315040f0201090902030f251e0504120b01031e0804060e0f03010504030c1b06021510050907030f061202090406050a150b04090608 69
    0x1600303541084002618000c201d074040c5505922881c0c0000e001d03850b031050060414060303008030101c2c0c00d2030140048091401c1c0c46002c02800214001c000390107802c00200e0b41020043c000401307065207280c034401168000c100c4440034021401b011034407803810031030b0950030791400e03038074a56008030f1000c1060054016910001402c0b0003501c0c2d043c03011000316100f20b6049040b207400d0341085024800032845001c0580c0040d42e0502408a00b403113075046080108141038080039400b00c1d81c8803c1521000601080c00b0b86048624504080000c8110f03035002c51811943c1707034100c6601d9407070041004101500f14406600960081c0b8100d06000008020000c002c5c401d40502c201591140000920000c84440d03039139442074506a048034104c0c1d444000c240d6004055802001094580720003d0500d90107205000080940c014850245092900481c807808405000074006546400005164500a4114246000c00700004d85803850303840d00240d0300d0343c01501403442d0050400d640024660380029107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 523733651 1250 523732401 523732403
    0x418090c091802010807210501080c040c090e06010302071401290a030f32100c1d0d0506011203080f040c05090a110d0504060b09010803040b0c0a0c120201021603 71
    0x80c035450700032143c005558180004003280100606004078240260041c00c8540007000c1c0e05a01050300e505090989050424540096016501e00505102e406030301c0030000089030390084207401c1c181c5440004901038401c101000d00210b9041c800310f1b00c00030b0150311203050b800c113946009020400300302c0d07107a111910340c68405502000d02401031002c6600c05072170f2132403144160000c4012454020600e48499440304c01c0f0390a09020360b44a4482c3ca2040c4969911402003450400c0045c42442c009003148107071028007410381c10034403040c403055143c00c00ca018110f03400c2011100607685d15601604c2c0503a140108400280380400810700c070071419030350580196403049407528802d04220900139900002441c94100584400e8606241080d2800030200600014400306492819040c6441610229100e06d4061b0380c44400420600c8000300c2942c0c252a04950610b07070360108410349a00e41050ac40e00640204840c1ca0002548140b103404001503500c03e8007a141c1c03020742052404070060440c44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 523734901 1250 523733651 523733681
    0x100608060114041502210903070b0313110609031b0103110408060c07051002070b01170a0b0a02030c0d1406120703050604120923040e0d090b0d020418090c09 69
    0x402400003ca05405030501340690f441152000c3d0460201480da51460400c02044407000003058501d0f404e00b8480311015003425002c8034950304100501010b06a240000a0505010100c2c0d8019a607191b0003141c40040c1c005040f2080100c0c0d0350100c1038814600e00c030b0a4003003433510448400441e00c400c1564100d4840780b000d45866a0703038038501a1950b200140403220b03801282003440d0100079510143c2007882c05450104c4480d030405016159001342c56650800c0c0358002e18940f4000740e06080e03402da104160300382c0036031252a5902005a07901075401c4080c050707410002d40030b403604195000240724103002c607120a02d501d5400c50041c0c440b1020300016060750081000500403500e410b100446032080303407800e00b41c00c9958980300c5060803401c0500c0701244c180300100042c01d11303250003080c074420310f0f00c409800c525200107400b401d003c189200c4c102221030003183c20700100c10f03203a0550b0010862000d51410014805034100c00600d2082c1044820b440c450b10040349402180c131a000c05444020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 523736151 1250 523734901 523734907
    0x506030906091c120c09030b010308040305010c03050903090d030e0604081f0b130b01050d0509010e06070203250c1706010801110405090f041403271207030807110603100608060114 79
    0x6428007010349400c01e00c005c00c2c0b080292000000441c03500406009500500c00c9540311070551505a080d201489104000c140c2000180400ca06000c011500d00c4c040441307402075032490a25003a6514120080741c3c0d03900080104000609900106815000a01000030309524060300380301c2c0012500030030186a0403526a02c800300740305103aa40078014100050401c281014900d4201906944c000ca0b85801165180d90241daa0070b04100700c61508110180081c500b400002900e14400300000381034002c01355020048a81401840800d100c0500300c82240014940780003104503035590820700c02c840c4503600e800e0441c0c0d4904442c0007690282d400040000f109519402486280114090030a4030001c014038245c0311690000c00092581079200d00d80031013405c03400c2604c4542c0e00070400c4100d01500390b45c0e4100b044502c000c2038182c240c9900094898032001340b070425807045c8501070f200c03e410410000900000105610340c040898100e5592401e260b074803c40116011180e803410785054030824 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 523737401 1250 523736151 523736177
    0x130b07080a0204090908070506130b060f041b08061807120911040e210405090403080c0d0908030f090d0207170c0307030f0c0e0c030c0904060506030906091c 69
    0x4560940d000301d4014405400c240d1903c01010844418400445a40310009002c00c1005000e110b07250f03000314021507003412060603448070450b40c0c4d8018207180c4108424000c3c0400c55031142e1110500d60034104000414a0781003002802848066948501c80d01d68020004030b200358100070244160f48075550804d020704401000006440c4116040346d801001404540340c80d1198880c5110340300240004061103040e128081c1c882201c0310840c000307121000c00041c0710355141c014009821030352600c2c0080345566101580c045900441c408442201e0a2180c00340034880050040c502444802d8440c4000c0c2d25030f10862681c0c4d50360b490746400580c10481c2c0130480c4008104950101c41d580744196003e1f03400e10800079041c02410380044840d001c2d441c92000512020f1400e1a01401d03918000c980c0c0c0781020300040714a8000200b04501606c40040d41003803980343c50300004001c100c0604515240d0a1034104544c07600011a22100302c2c1c410742034004180103890070112030b00d071200d0312004081c84c01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 523738651 1250 523737401 523737407
    0x14160b0c0f0a0807030e01090215070f0f060c030b0405072012040f21050703060905101b030f051302010507060b0d051e1b090601020c1203040806130b07 67
    0xe003400491a41403120804440c1e8050050281c1e4000b40d840e107000345040f4201504446075004459443d030b00d080810001030300d035040c082c15049901421181c440200d4580501900d48115008000c0c0b01102c2611f01080300340e402018401c6c3d40d6483c1070281514400c180f00860300101d540000080c0b01d84c4010343c00180404c1001280c8040200307550403400d004d15903c009034402d50102442100415003040318080040e04209019081a4803014080c0c035038490a542e12120300010f03144556640407081085410070403a8000e01600c1d4051100005d15940d00d103441c82c80071041804642002100c40e100140e038800c2070b10500c04c102e540010306100c0d40045680b9000070a0417100d00e9501c000d408c0c81591100e200381903082c4940e0090441040003811001c0c1410b15110005044d40043d0800103050000c20b046040c0800c1655400007903503907400100e292404009a00c0d4102d440c5108480d05524040010f2081c1c0d0342c20800c840440d1603503150220550071801e40542592070020102e401e041c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 523739901 1250 523738651 523738673
    0x1c0b0601032904150f0807050a060905060a0c0c060806190602190206040e010f0611070e0105130923010b0108011202010c0203071d1006030912030209010228031416 72
    0x180500005020001600c0d600c2c1046419044a100358901100030080046c1c00c0100c00b0180400340c0c2d040140340c1c81c2400250009410340200d034851030010400c15102032052131641c0182d03130414241c4084036075902d4090400202a50341600880c1d0305481c055100c000c051008044640c5907000300741007540300040c501503045205040368456010440040d0100c201a2003e01900d50000c3c1100080c0c036005000d8003c02c0c0c5089504015045042c007001452020060541140c4082d0b070080d0441c06409180710003803800c60f0000709a15802081007542e00c00842600044551131802085028003a20054034000001d1144240c1f00c21010b140c140154450618121498400350485032000e440300c1041c0b4070003080342c22409845101340c04009c0e403103040e0b60001c0c000b0081410100041c0301c103a02c1d0881c141420038110b00905400140a241c241d00c20030000c105650840c0c000341c900e5203120001c5040c003000e07032001c0e00080e03400710502c251409410704070303007201c44003440c00f03552110b0b20354031000141 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 523741007 1106 523739901 523739981
    0x30f0702060906070c020d080324010201090b061c2f0409020303220522050604020306060313060906140f0924090c1c0b060103 56
    0x40105090b5004021032400400c4c505c8140003103444203259840060004a0000412428030b041018500c04655000c81e8041e40003903110049086c0d4400d81d0028000400388000705560f860001405100c02c1e080708908601d1281c0c075180c034103d14074454490301c9040b51200c08110140030a10303800c040080221820020186240c020964a0003207a144041030307030b00000c001c40d200329200d0741d1a0091500070102443d08030f100ba0741e000344010601d8041601030505000c00c0003403405009991103044058503940c00c61b43ca0a10809600079000025107680e540c0d01d108001040f406d0180340152400c00001030390703500301015000e542000c01441c014a607002820000b104041641004990925201015200389c50304604a41042030141003070742c0c8a0800c5400200c15a640c560034a481e41c024003030a059a0b89079401901036411240580302c0c1007192100c468000098022103d41507 = true := by decide +kernel

theorem cover : BRFrame.Cov 523561151 523741007 := by
  have h0 := BRFrame.cov_init 523561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 523561151 ≤ n) (h2 : n < 523741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
