-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1737
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:29:14.296521+00:00
-- url     : https://prove2.me/submissions/100a3d64-68c4-471c-a97f-45cddc0263de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 312230215 ≤ n < 312410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 312231465 1250 312230215 312230257
    0x50c0a14101715011205280b040204080607120501080d030908091003151208070f050f150601080601020c0d030302031810060e0709180f090b0a0501080606010c0503 72
    0x240c4200d5080c0e051407100b0260601000101d0040c6402102c060707400b41c9480040081031640b480540c1c40480700b204000780c892140c8480c01d80b4200e50700004c00303004040820240d00440105040741c019900940080c1c3c4440309020301d1523007122500000d01d01418046c0969810904002d80d0b40300c407005044101070303031050043d0a019540e0141e40f07030554002c01c03880e0a00304884004002c3c1050340d0f00c00748120428000002da218204000d40055036200e92240d040c00641d0312030581d002c403412000e070360324014031180745801f0034144401300780a00901100107260500c070000400d0075000500395419540f01c80c041819640c2d4032400a2310140c1d0510740942ea0b95921800e401810b44010003020f01441461142c1003a03141c141c00142c01d4402c205200c1e10305555402e005c944446592041600c20a0394030300354100342805070420301003030705003203400f01c0c0d070f07003c0c5070354010381107004039400403c2959485c0103205400d01842100e810940900e401840c01e500b82d211982c4a202d200800c0d00100d0f00f41c00702c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 312232715 1250 312231465 312231467
    0x5060706020d0c210209030604020f01020f0703030903050705010c0302060f1008030406050319020f220b12071202131e1a030a0c030c05070f020f06040b07050c0a1410 73
    0x440358480c000c00c50a10180c103080001804500c0d11307803820300640c1640c07406415050340c1d43c4265111a000180103182c4e0352259020f0003403000c1c1900c2d80604501440030300c0f4008940802503000158403a5807549206440e600340b00c1e041080c0794000c80d041110741da2813100481d80c0001d1840c3c000c00d0700c0e0154071240d01e420440a0811003142e02014460001044c000f500c0c581003c00b4610030840b00203500c03000800c08035a54100d105030410443d00d040c050101100b107403468a0030000001c1003050090b81a40c46280400c2141c0140c4210842540c0074004c020a0950000c80150704126002d030640c1401da0001036000729840601844a0424040407400351048640c68401d0080c0754000d01c3c24004420f1080c43e01031740c0d000704c82154210341081000000e0740c0c400e1141014948456503224144459652109081441500160707400041c000814115640d1900100010000d030300000395030b03800a140990074500e8101d16a4458200303180c0c2000702031003202400601c2c501c2295107505075086214 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 312233965 1250 312232715 312232717
    0x308060a030b1302091501050f0a210905010c03150510050d0207080406081302181f09020c0115140108090f0d020601030b0a0905070e060a08011a1801030308010506070602 75
    0x1101400341e503603940a000200f4149405020894000d48424a007581d41920f86d075400e81d10700e14150b001441c100722100220042030080d100310305c214a04000d0b440c4200d410b803401e210510348014901c1d680c80650b0300c20800241308480002c17000d0b050620180388038500f0510403c0252080c2d0380685000c4000d80f001612600449074001c030402d10842d02e074562410403045c5070708a07010b140046401500843c40c0520403c400d072003404d43c024141c0035900d20700c400d800030806010f4010741c4207d8404070141035200b0300a1a8401030104070030016100c0d8440096107003990380f6180403c0092603110800e004120041003007004c240002c0c20f00400f10744640d03103428680888482d06610601030401003000f81c5501060480c101c90040740b03100d1041c1c4034580c00e20100d480c42280280b06502c48101004841e01c1a9210759118400500f1954050b80d07824016094a002d0101c9020000306a003000d0f881e4508200144401412211590425030450782d010b40f443c0810b014843c85004040b0b610410020560 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 312235215 1250 312233965 312233969
    0x509270123090a0e0f070810090c15180605040b070b0402011b0609060b1e01180b121807030803070804021f05030402010f0e153916060c0308060a 64
    0x1030400d818503d441142030000744840440410b440c02a811805c4400ba400a100b40590300340384054801420784003140001085403a0084605c01d00308503001031002c2d1640700ea10007069080d242d80300c400603110503000404405801003018404148001c0c000b0300c81c002c05841c0c036107a00a1100309c1d0307902c9030300040e00c2e0200070176200f110f2103a180088a081000c05e0b000f24602d94820380040c412144000100f10340985124800410700500070b040c080c1542c401c065190010065440e4500030546483c6a15020350ac908050110050b105c400c3c844515605a40c619038841d01101074001941540d5840c01342d848064180c0b0200282413003c1415559107903075222501d40e101e0601c4103403885150014200d0f0b001200c0517800710b0140d031050704d45079000f1035910788501002081500e154100810513600d540000804800482c0602c078030070300c2529481050501d200c1000000c0307101754200c0030031500e44844060107100e5a10704030010060300e030b00213107401a03c42d45030624080079a146404103400840325 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 312236465 1250 312235215 312235219
    0x82214190504150305010b01030c05121510050a090506070209010b1c020a0f0806040b0616030309020d030e030706180501050d090209010905060a0803040518040f05010504030509270123 81
    0x1002c00f03103811140d405801c20859108030020710041c0d802e5001901292409442074020500c20400b5180708403000007001e6100d22039664030201c1119580c0850000202030b8849030201c1c00020f15070780000e81250a140041c03c0845000d031602300c031903001ca41c807080103105031070f005040070458483c52109456030390300c2420b1411046484290802000b4549145100440041595407010510394106130242c14007044015028616281e0b01c084407540307100303021034203804050342e80302d4010050741c85000c8511024040d580340991200d504040505020450313101e80144030700300b05a181d448246c0c4107081c00f100c0c1c1c00d00301642c82d140d0200070035014244001c0d0081d1b01c807200324004140030015521540c082d84c01a1201c985039038941a5891b604c0c4942d0194580c0990f4041c4031030a0f03d000c0c0742a4a5006210740d01450075404140c0d115400e5032002d42e41200810404036030101d184c10100d0680022500211010201d07242c04c07102e0001504045c0079070500710340d040504800c241056107414083d4100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 312237715 1250 312236465 312236471
    0x27011e0201090b07030506030a1203020708031014010f080601180305030d050108010c0306050a0909060e030307030f05100509060112242102010503010b0d06030f082214190504 77
    0x964000a00034401000d04849480344100401c9115100f0f2040c00d00c1890081e009089000351511080b4010100c1c82c081001c00d40c01b040040c000a8103030010314022000e80c4410022a0704040030368010440d0b062903181006490418106a20303400751206401440c00c1c00e00203450103030501c0e109881c80b680d4102400b284000149650903079010b074030482c101c0d01010020400c13400f0a100172020b543c0e552050a50200082c04288040e801550210f100303140304190000b1020300c286411070440d0011036212011a9681c08100d1401c4854061103501606440000500d5800c003030000d02c400b03101a0403281000300d40704080304149001c0d4010101c0b211078030001d08440c400340c290181c004042d4000c1d13003080110b00b29042013111880307180c100b8199058407143d0540e0301f00540c8078084e0704210b8007021129158100080407403081c45c00312030040e010303002c444d6603078071400c2c0500e4201c2040901d2507508041d07844104801526040c4804402c1001c44030a031080322154004042440719420a0f5403041c1703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 312238965 1250 312237715 312237767
    0x1e0504020708091e0a09111603020313062d0309080c250311011202070c0b040302010e0909030912030702090108030403120807020304140d0f0303050901060b2701 71
    0x44101c2c064003003024100d070300000c3d04580381000b850000790203d50603005058508203000303903050382c0c00c043c262000e540d4500b0304040c0c100d2a045900705400c0410307005600001181ba040c0e40c14841e00f58084c00c4c0350304014080116042055204002e401c0102d010203a406460080341846600921002c42d00b00d88215201c502d140f11940e1101c881d200ea810000c0d048100440e44080158450003c90b5080b100c40c480813543d03000150f481100d00780f44109111360030046400010700c1040400c006d09803c0054a85441c1944000351181e1a401c8205100d00418010032101c10f00010132601000c009075204a880707850a05440e256000d0302d40c00940c0005102c1c000b013031722036002002c0c0084074052001540004041e02068560110507150fa10058004100038805041c1980d850ba0541c00b002d003a121301065543c0740c880050440080480020b5107480a00101000034007411001d0000100740900d003088010f000c0c2c41441409807000c6d0791040200c601501d50380181844108402001481c2140032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 312240215 1250 312238965 312238973
    0x140702130906050a0b030a0f060e150f07030e030c071413140601031506020a0209190f0603150b01091a12040b09062203030e0f101506020307020603011e05040207 71
    0x40307000c49a0107502403421170040c0141ca400101e880985070811b80e01160b1244a807101806011078a01041c130034401d11400401c0e624a445002d84205003090440c10b803410f200e2001400c2c0c40d141c0030100c038554414068076000c0700f0040780200484d600004900404096000806d4070a80d0010100707142a1420310f0310943c10710801002480340400340c0e0100400e8503106000080b0300a54000c820069000008041c01070410100081d0084140c00a0160a914001d030450541d0100d21401d0768141c2c032030400b0000c001d044030102a480d0004081802900002c5000a00240d51440b91002c10001e00c44407a44404080048074180c0500e400e4444032440c042c14121010041a55508901e00c515000142d00318903580c005038070303071001c00700756a20950304d030b2007c4014010400c0c0d064640d0085a14100d00308400300241000d482050401242d40c50107070741070200590003584100e056402c10070070900141e0b03545045905585440300f030020340c1441c2e0111101070011503044590403e200142c00d5040c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 312241465 1250 312240215 312240221
    0x307030b240c06072a020d02100c0302070501030e030f1b060709031e021c0201021606090504050a060f050d08090409060509061302030606010c020d1728140702130906 73
    0x7064480b81211a41d4980307200458604000102e140c00d84c120303100f203144284601c1441c480080303000400034400c0590a07000103004150307905101b404102056801c004264050008400416090074200058030100d103449441c2d120f602204130640600140000000701e030440d0350100600302004481552510715400740000d0150b0100b601c4400012001322410b44444001404283d07028000311000e211030380410981c01e0038041c04a0540c0141d4801d044230015a4002000510203a40c49514681c90710041c0001c46001030010b110b06811f00f1403d1007010100c41c4800c0071144240c0301901c401607030381002039150041c800074560007030400e0941803d206046c0c00140c0200c1620040d5082601ca201c0e03000f2407041d00d91070080d05604800000341c1075602445a01040c58000390001a6020044c1c1d02d82510b2003046100b55030315440400c0d44000d940e00724070102986000040008080d441580d07007c0d000c3c0c54149a40310b05010006221411500c403d043e82214030301c4404140441e1025103009805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 312242715 1250 312241465 312241477
    0x906030c02160303020d1e3c031b02010204080c10110601260d0e0405090a1e0302010b01020a0b13080d09051c021f0f0e03031303020c0607080307030b24 67
    0x78100c112110407801e00403e4038841c00400340c85481c48103071720403118450200d00300310a40a6000120100b82305150001c21a42c842075169000209801c98100c0e8960b030080d08010141107a10512051251920020754894014421075140d00c0d4004018812a031309211050000c400f070113410000146041c18980701c810703c25005044048513560194150340d2500c001030304000161024141c005541087d034412604508128180c50011101d500c8588201d20003000715884000c0f07940016090603070a2080d0328040009102500002d021a1100c0c151034502411200d0784041130b044590800005c44200c40c00441d8821007030001c280c0500b4900c1e210702d5040c42108100e50041900b820742407010807100b03803404006540d0b0700c10300d916220440c01000c140d50000c2c003140d52070b860300c1d202c07880030400345110fa1380280c01090031002520300241081c05840d032250282c0301c24030a100c00103c03c5000e403540b0503041d1030001142c407c05400900d00001a4089506140c011144103044070480402884 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 312243965 1250 312242715 312242717
    0x9030f0c011e0f030b0a09020705060f0907030b15010e0406080618070b0a03021c0513060606030207080a030b04270b0f04030c020915061b0c010c02010906030c02160303020d 76
    0x9000c1000b18480004900c40800d84001410b40c0110f84215001c0ea201400280707000c0d0041202c10b40399020f240480c0e2140c07200b554154464410841381811403c207407540024100301400620f4550382d91030340f003440c01030010400c501d82e08010490301d034170605502484900023041408042c2d40d030007241f51585010b4a046c0308260b01410032400081c00080c950084903040c0c500c86103421907a00046000390080c040c4440380b800a020b00191400c0a40111406403d02d00c0003182640391600d8502c04482240e8459018140180168004030350003c041d507034080001e05002c00e615a01100081c001c202d240c0c80300b00481c1018290036030100c00d48904035440c2c0d01c0f803d0040c20756200c5101d0304001c007400320b90040002c1c10b40761043c0010704000100039002520a03400a641d10705040010322542c200c615404144070303190003c1c0074100420003000c100e120342800c202c042581e903600024a050858061300040c983c40d40d2140c640035208004454440300992040c14086889190003512030030b084aa0744 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 312245215 1250 312243965 312243977
    0x7080606060d0e2e06050109120c030b100501021b060412051501140117131719020d14070b060609010e0402030c030402030114070c060b0a0504020a0201050a1d060612010209030f0c01 80
    0x1880303844c098030402c01035520513104c51020b51300d4091041e042540c5000211504035200303c0010001c1c1a101842f4010600350405041490600c3c00081c5000850740c0c0c0c001800355103848045032a140d070400c1782c06480d0790001c4020b00203c42d0504a00d0208401c0e40d00080f030070b030703140001024a40d469010101c280d090b40c80081442c904500c0300b6907100f013075816410100b2003050980005040a225040410011803807038280480130710003030781e038804840c2808050303004400c03002c180e02d03440703015143e03214004030410b0b00300300313564580c48801000200100c1c0166000070b41310740a6070003507007890350211008005550b1391800f81219107950f00300f920103e0107582010412104004002e0386c040c0300c1c80541d9581c0101c040c1c16115500076000b42841c07150024001640480d0680b2540010488224260004240b9003069001c480845001788484614828104400e003108500802d0094208030102c6126100c00b02901d0043c4c028401c2c1200300d58984a81c10303131140359035408181840020303402d803104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 312246465 1250 312245215 312245293
    0x50d08150f0307051306150203030604050714160510020d020c060106030e15040c1a19030203060a05010503091912020f010c0507061a060c01060e010807080606060d0e 73
    0x311240010450031a9071541000b0700510040c1002d0305d45041a501407500420015580d07103040a000f1840085030005810000401005007054000c05802045e00e1415014941c0b80d8406102c141c041c0d40720388900c418452103040240b000410004650b2000344108541c0e41d40044000c03030003544202504100760080c00c000084040c000d10400c1c510700d50030805801601208400c030103010900500454140c0f5030b10030049070714007540f484541805400b001c282d41e030b03030040d007100d400918003441c0600c10580100308011840d1512044401128000e00380b81e9182c1e1104c1d0f0500c1d05010000e003448034002c6a460800702444a551409401e144040d000c2d01d4001d00803800c22426200e5504a072804144100801800500360341e0000346181030315030140b0323074014903440010f00350790100139440000da464000c28014480d9246009004080d0702008080c0c05103040b01c038584444004102a00c15100401d0080d01c6510940041c00011100e80030384099031082120003000140c03403030380340c1d03565122000340e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 312247715 1250 312246465 312246469
    0xa1502030703181208030406020f071103011a13020a020f011109010f031512030e03100605011d0a03080c0709020c0a030f03090b04021201110301030606060f0206040309051507050d0815 81
    0x1c402c20390b44c4030080c0e9041c803603090300d62003850381c4040c104a510540c20002250201c070070170040c2507401e102d04010902080710104060035203680791403c0c4c075800c00d090644078050b03a40304082c80d511050864003684812015000340e0500038022002d00745075081c400300c1004850060700030002d98900b43c90b81d600e07420780000110103d6103180d070009420030490380188259041c400e00001d8051180c61700180302481c00003c6400c2854400411072842e40390132040c401582c01c422400818101c0e428010401400000050030009040c44090100940010310b03805120050119002419191009540d03a210340d06500d03a40341e00c804030540000c2c000c4a20910542c0c0b00340030b40540580c002030301c4001503d86408011038400000b6440d0750a43d65001100d2091492801450095000f00342c001221841c019020300481c00b200300c0c80046402041c00c00c80001d8008450070180c0d50191603400360389040241c07d05882c031070b0101c003601612802e0080502c1f03542c080c801511410090380a80419646007007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 312248965 1250 312247715 312247757
    0xf101a121c080f0712060801140901060b07020105191b0503030915150405060109091805010c020f07031103120319270809040212070807030e030a09050f0a1502030703 73
    0x40c083c250751041c079011030100f80c4903020b40208451000000a0595601d4100358215000e203543da40104403603904200300c9a80a206410040c03080080d001d1506c4941e9000030302c107201c0d00d50700188a822480380c54541a201e00c9090a01c440346150a51401010382429030381c9400803902d4115503c00d03407903610381d642008840140212681c1281401421400702008041c103002000342d41085524000010301e22118000c01c058170300d1007880310b13540100b41e042041c00d440c7c13100c0389003040d98429a180f8407098800107080c01140c2c0c00081d4009010038410000341072180c0100301c001102c1001c014441540d812002005107000801800c10090b0741c0000380f85446400d481a840300b20502550490100360000c0007850301105c02000146800b201c0d00c460a05240c096500300000b40506003008038464040c030a40c8211700c210801141008894a0020310710030440c001c00e400f03200c0c012140340760354070b4080d4928050101080f07003c02d110241d02d0025502d40004400b5400241c81e1b03440c030f590a4444034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 312250215 1250 312248965 312248971
    0x30b01140f1309020a0c1518120e04050709080c0a030803060d061e0209031902060a0f030912030b13050103021f110a051c0914060c190b010302010e030f101a121c08 72
    0x7401c9821314000b5107850300f06495000c02441840ac03820304503c4e15a60318070510b44100e5450300c650b000242072441482c642681e8400c0345000b5a03a4004c144080b999030410b49500080880c1c10442001481c941800035180c4102444506034030b049452060002c160080c1101e0030054049038000365902114220881c0720920280d04460708119807401c4034403840601e801c400560801181552542d9100d40f158a00c000340d40740000c0d170741c50600c4000e282500c20380a1a810720744003031000c1c0d41150006031030010707400d0000e00c0d00c11001040c50380680c060340b40c40c84842001400d448201e01c1c1801d0132500c800c0441c00828100c0710700c2903020121802040504141d801d80185070b910b81c0110002c4c08050fa200803001103c0f84140c0180f99903103183d1007030912086200705000401d551462001400150300690f40d94425000b5288420010b840050315100020841d000800c0d40d80071808048c2401000c110010303008440d1440d0450141000180c4130801d100c3d54036400040d40e81110121580f02041d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 312251465 1250 312250215 312250241
    0x6050f01030b151f020f0a0b0a0b030303190b0d020927150f1f0f050301050c0f07020f1f0c0b0708061008040602040f06080403030b01140f1309020a0c15 67
    0x70018500301c8030a0280006084401303801100c00e508000c20310a0720340f00810300101e84104819080002e0040b460103a040310200030340045080d030074500303280c0d005004103040c0409000d60350b00900c03c2c2540d0f05004201e210390040e100d07401d913041032506039070103060800001e9640c54000402d0082c041c00041c1d1078400b404001214142c0c0c0d141d07160962809407000c1c100c207141c2c5802031804d4100702c0a024040d001003d0010791010140c0c504801e0500352035005083d145081c0c030500030b114202800f00c049a43d0030394125030b0103c1e0145c0c032600042201201c070310358081c0841c24101003030680390460402d41429016402600396580c400e17008850b0101c04441054000d000f8540b5141281d02910035035400c1841114054200741d101e104088840ca140c0c1d2001000810b01000d200078550123104031782c2100c90a1801401142c0b0081d010a442c0c03113185074080170708400181c84031150740c10705281d0014000c0079000b5592031140881c024200c12a03008159a804425900b40020f030309140f140c101c0c0401d02e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 312252715 1250 312251465 312251479
    0x3020a1a0c0d020d1d03030708010b0a081501090f12170403050715050d051005011704050c0d0213020d1d0c01080403031d151902090303040b090d06050f01030b15 71
    0x126804040c1d044030055070b0703e0f5902d5012100d20b02200c880b1703030348070082007400440c0c0f00c0c903281c0d00040c11080c0682c03000d00f10380d1007000084400b170f6200301460f078800c0c00c0c0880c984440340703480e0040b28503c6859225440d55042000c021801860080001c2809409900011200700b480b020420842c0324034800105103500c0303400c00b003100c56807580e4031a5100c251800d0090501100070080025a502115040c2c3e8031040010188955030300155115418041c00500d40c1c2c2520309559656900c3c80091066849079402052000841d1354514800100d2200c0d01002d549600000401001400111082c1d45080d1684600d1791600c400002c2d405011002c1692410b106803260b031070580041c4440340341294090b00055554040b82800c205044c01402111100c1c4020703d080b9100c101407904080024040350300400140c111030b600003080e5015a19001002c503a07441c0340300002264107800550040405e42003008220520210441080c104d9000700e0407903d040c1e480c41180d1b41c4090000c03420075480b030a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 312253965 1250 312252715 312252727
    0x2130501020123061810171603061802210606101b060906090309210b0f07030915050403145e05010e03030d020a0203120403020a1a0c 59
    0x1c04280300a4001304003404603000b454440302c0f081803200d000c403081500720200c044204000304180400040f2100c910740540301c1c0b590800d9a011081c0305900c805000341741c0740d00e00410040e0701c8082d44804a40d004115424a410f019030710350b0256041c49041415006170400990380d03041a00b2001084c030030540d43d1503504039456010300640030381004243c2d41c00303640e900c5e17900002e0054410b0041050207510744c901c8203032410228280a13030f44194100241d0920b40810700018401484030391b00401244290502070b030f6440000c80080502f900068690840400c10002030302e071591280d07010340d02950710703000042a4243c4100384d61084222520215580010004d98006a60b4100c2c203640c0c2c80715a01005408400c4d10380341d004115004000d44060440c60aa1070101c0c421091801004282056114081214006502da0240741c1034458103980019200029074400d008582c00b424400241c0381944c00d00d420000d40d03d0800d04021500b82140e4460303485103078059007545100c0c0a0f1910807601e891 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 312255215 1250 312253965 312254021
    0x603150c0a090f120512040b0403030e1206070f0e06040f090b04090213021c090b040807080919050909011a04090302100c052a03030402010302090f13021305010201 72
    0x544400704410402c00140c0c004030f40c03070626289080c02081039000380d4643c1c0c000f03405d140303040110070040c48860480c100820004100701303500381d900703c94050400c209402401004100100200303d1100b1745801000e00b00180d00d500600c100001e183d807903a4100b62143e80c0000d00005200e1405880f0785519072440c1000895400d4001c925031030400fa00c0428014080d9001c00c10800d85260603038402c50f000304034400c07103d40d860402c440152440c0c10602c4850226161240002005800a03005a0000485109001142c01141c0a4003c01b0701590700c0c5803e00c1e40024540b0110340103e81c4030b031403807402040400307105010b2000b21115110380c051407541076000700001441c9010701101540180c00c032144805659104181c0c84089a448169a6a101e0b204000041c0c2008010702e511020b009980c000c50040042505d50081d42800c4c0181e40345d910f640010400c100603410590310082c4194401c0d81c1c0c82183c4c01618500317258111a500081d02c46005a0a890291041d10000f4400344103407c425 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 312256465 1250 312255215 312255217
    0x2d0c070605030f1611011d010f020405100302090d050307050106091b0e12100f05100501110a0201030506060c01092d1e081201031a010927051f050a050603150c 70
    0x100220305041d0542c0445d840d1903400d42d110a80c4401854014481d0803d2401017070103114424040040704600e0301d1309020024003e0003988090340c041640c04222050310303444658a20b03e0380c6070090216600d0355286d2412601803c0240100400182010f1007101284400c0b0481c0704855100c0e1204415808408184070030710f61004818003c600c641c60b1025030002e01032088001d00d03c0300c400040344900c0d0541c0c0d00b8403c101e590303200b03504120034581c404c1130100c80070407004d85407036091a020502d61212000a1114000e005802ea82540707020303200c82c2027100c034540c8032a148041500c0f00c4030580d4011202922462035003805850740010500c60106054071b07115a60446104590440c1405001144030420034426002240d0b08000b001c101508141c03c09603c5d4018241d0030414071080d6142d4200707815034503008200070075500702d000c0d0080401c0300501c1120036020020443e1200d030704100003904007611096030b803111170030b04e4503021650a040c0480d003a00c11405140c8641e080b519106002612 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 312257715 1250 312256465 312256501
    0x1030509011503050114100b0301090507090f0b0318120708090303070507030b041b050f01030b181504060902030601020d0f090317120f09122d0c070605030f 69
    0x150355030b110114403144991481c0b100166001d0710001624002140844003010741c0501040c0a5104c034010420132594580c0459040da007078810301091a8540305004d0354040d100c3c0e00300c2031035908038601c003140011608010b9441180001044040d04c0304010384507407180700d44c80e20344001d01801c00030540415803000003012a258044e046038540340c41031300e80c3c0e8140f00c090380040ba0214074090510003800442040400d01404072090300c0b41045c0303404009101100440e103034078141134441c00402d40395690400c28102050102c1a01d980328a80f401c00301803074400b02d0302840e01c180d10305400424107800324800c0e2445880180c00074202e5846404069824400c1480881d00300200d45001000007104107081d1202c00d2100b0a50507203a205d90000c000f03509400030152040d000c181c0317041040e14200040c800060740500f08449640e900c0400d030750301d5a01c801510010700c40030b48500c2114040c449000520b0b1155281c2c003510380454035000202c500340320a0f210090326034020400300740021000c80300f0003c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 312258965 1250 312257715 312257731
    0xa0e011d0a1e080d09030b16021b01021f0c030e010b0f010305100803040909061a10031e110d05010812190504170c01091505040e0c09030f010504020f0909030702010305 74
    0xc090b903910401d6901e0071420600400004501d060304004120580200790303040401418146c00a03042488001c2d034429400d254520301000c0d9000015469000b0300800d41d40352181010000790080900480d0017611031f00d840c00001074034141d002185c000b010b108620210b04000c245c09107801c0014011405000080d10800c0b82d2103040c2400116a01c00708001c0004103006880483d40c10b1042c1807410444121200f1580c130b02c640501200340540d25048241d0301a911418005138000c441e24038041c06492170703002541643d01c1c0440020300109608050700648a000708141300c503a80b40d0701c0c6070303417940c0401c40c00d0045402c050003220603210710030800e02144001c030b01c0c04504050740c40202200c0c2c0a00c001001c01940c10060712400156400f0071000c0c00f80c02d00701151482e460101300d00800b123228921078896650001030201d850000c0d08401c48114045c000e044441c19824040720b00c3c020030054604030b105071000005549941004080b040c42515047c01540c100103142d001940500300c0203003241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 312260215 1250 312258965 312259019
    0x901020f16080c0a0501150905010803030a1e090305120c1c020711060d050a0c02011e02090d170d06141f090e130201090803030f13080f0a0e011d0a 65
    0x11002c00810014000d02c40e001e174001241c001d20b082d4085510040a42004c400541810010300c248200081103a0b00b0031620300300041c1c440e070032401c009034104402d00c45045950030480700a0a00d0340c0403001e031001a024040120280c1c03500381d5204801d1013054942195070b4001300c030305d25044019038050090280035810001c02d40c5007040c00104075038069500890001d03078900600040103183c1c0b059040441860001f00000c1c01c1008a4414090b084080400c020b50000780401c001d48405400301c0101d03078414050300748076540014214480e084201c600f214a4a4498002092140742d503a11f24908000303800b943c4425441c118500212220f00310700020701a422030001508101221690b00c592002c1030584c16540c2c4920004000c0e2131280d1100030107510034030510414641c0700101c641c00c401d0040080d0150f101d9454210303400e01030740921303850000000ca601611660000710140261809a03100d09804501160811410b201c0a1f02550408401031060003034014440f0102022041b800040b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 312261465 1250 312260215 312260227
    0x4150816030f080c2b031a03060a0906020706060e060102101e0e15070906020c0f06090603071106040f0605062409030c06040902091c050d0503060d0501091a0901020f1608 75
    0x400d905801041041100f0002d8078031540e05505111f40c021501c0003100c00c0461416050001f503a528010b040800c416a580c0320b450100001903041314070b580d9000a040c000c66981d0310b40407808040861742036001d4060001e000c039201029214290050f8100a03100348040b182c414168028912045140220300c03407110052800e4031407981c414802c00e42c1c1e9441d60400303800c200300281030803496040180203210b0041c0c0102159240016540030700000c4d15141d4599844001c11035400e0010f4610b80014040c1000380000c0c440d50244600a10303018190070700c0907450b0740b0280040b01003400c01d0a009001e09403104009160108020142003000404444e0448102c400284459100c0e5000006031540041e81f4011410402074070608190b100b004c6000b00709003900d622713884d44000e07a2000c04210b40000020115682c000856413460340000080100c20124584402140071a1012031043e441d000002010307940140202e0380c0d159010403649050400c0d0b0001401542109403086403100d0050040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 312262715 1250 312261465 312261493
    0x305060d0b04050c0109060f0c060c0201060b071505010605070210030c260406060e0405190302010f0516140c07060804050a05160e1003120e0d0204150816030f080c 72
    0x8440c2c0030318014005010b0074641c00700013601811303040c2c0c000800d201c120309214050320b402035540b40c1c2151b000800490807038a101c804a005000310f400181010f00c01003080341c107000303840d10208a07188416800700420b0341c0b2104146e51602600303100941c0702600304415004188290085444103825017000458051558050001040100302500301098606c0030801485244c2c062000149100d802441c61418142c55075500c403008031003401d0b8a10400c00000c01014402d5002145049148004001504101041c40403e8014002c0301d40058000c05080408020360400c54403030070300c900c000b04036403480c26a007502c1c042801030080c3ca460159884642c0450818030504218405450305000c100d401e00c81900c8041c240601240070071842542c0620010b1401007084070301c4201400c000c01c100d03008000280c40064a0000207410606104150001e0b08001100340c00b6038444a040e64180c003004903001c0210510740c84040c04481c0d00c2280d60000ca030140c0014600c14003000d0a44a50b01040c03d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 312263965 1250 312262715 312262733
    0x801020a02010b01120903091a0f04150f0e01050322051605010809150a0203060d0215031504150b090105071b140613090f060e0c04050a0b03040b01060305060d 70
    0x225810150f510707070542030001c0da880210400c288040c0b0b4410400320138244c0700140008021700034050211001d1180c00740d40824071003030703400c0d00c054407810580d00d64980025601c4e217291000d130b6070b0125480c200300c1a200360181488850168043e59070700d04540d10701b1161080b40c190200d18000b400b6908401c1004110b0900030340701c000440c0c000e1154010310f1304d0b0004107003034002401070340c01e608106001003106046021040d0001c2444a0150300c0f5251040014144220100e0084d8032104200804000004c0309000d9885010440703c0303510304a400c8410300040d04c038040043c4180324081c6100f40200b20001018145900381890110305206503035894400703290754840000080f440c240410032a1100c69105242d00c11400d40f00b10342001c2e580d0030083c07071444c0c06010750b020950301e0743e08514403422641d008030000c207902851400d040c2042e07041000301d1391060040b20301a400b020004550b1589000849008907400b91451040760302c0d003d01100142005031005610484415503103000c41e080d50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 312265215 1250 312263965 312263977
    0xe0f06091915080915220c0e06010e03030904050903130308030402040b04090203100b0627030c030f150415020301030305031e010f14030a06060f08010e01060506031f080102 76
    0x1c102039580c2d0500040b0610742006105020030024000c00f0800030460114400038892020070304001aa1100e50b03407962003480d100070010302002070300d10314801c0c00117034249a0119008030015041d6511904011152051400c625940541c030802c484601410650310482c0e0080503a0140c034200103044100c0c1c50302207400c1e03005035294038002c41404190328052188540c8100100c80c200030480f4250b000c00d8480070703034180b00840d007940c1c0c0e0f9050f040f5484801c11181901209082105011009103400c0040d031510b08606009204181d80c3e818107041c00038441032000e44050081c44100748010300c16405c94030046c002c58003042070303480315400e0060a001441c0a10300c80e44409441b45408901ca00d40361243c0c411803010300c015200100714011a0050301c0090b41d81300c454071002c1d07100350b102191900307006000c0104018902a000544044c084826209881e606d900030b0044009044089090b54268081c00d50f01403010408141e0028103030400402007d0301412007a2800c0c0e0350010142203070005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 312266465 1250 312265215 312265249
    0x120a050c0d020606091807080607020a0b010e010509041203020f1606050a051b091203070308090607030c0e0108090f06040303061a030f0f0c071e210e0f0609 69
    0x110360189249001c0c010010520030a100074210b07403070043d00140d49004003a00943d0b1640604004130304420040c86044041d10320340f0100c4020341041d42c0000e694581648050b08c108011400102d402500d480c2c4090407600c006045a04580f03075a258071100d81d800103c02c60a0544c20850046103940c484042c1081c2c502c0031040c00460012400e2107415078200601c150f411501c1c040400c4000e01c26442003107451140b07000e5045e00c1f00b01c00e0001c2a002511942407481c40c0c400800c0d4241015070040080344a4000101500c01a0b2549071054083c1d8401c00d2617200032400010000c0b003154841c15a04da8042c10510407600c5040010f9209420800140d070b0075400a40c4640007400344c54000101c8005074a61030707500b00c0c9103141420342c203845107401030102060460140c0229954030b5810090b103203044d401c001c810780003000500c2040400a0303c1d00046031b9030825403401d0301031240806000d0071100d00684880b0100a412020803075226005100c441d0300c01c6007400031071215262445090b08801d40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 312267715 1250 312266465 312266467
    0x108010609050903090a0627030503030603011b05030f10050d05010e010b010e06121b0c0304031101050712080405010e070810150f061202280908060720120a05 70
    0x182100708081c0c1d50024680d002d5544100007005ea40d4456008000468403140750614101c81c4030b60b591b001c004c5508200c0003405c11951004018090080001c50041900700c0c0200510800d00340c1c1c1001200c043c440d1100490420b0000410b2168000803440d0f12074403c0c04400300864503000001c81500905100395070581d518244464050001d100d02040001d00b400d001c002d14130b210b1f002629900c160381038018440109008941c0d88000e2448200c800d0b01421001c507114000300469a03a0f80d001440150b5105401c80b20301801c1c0c6d40100110b1303181c540c10144c140e10515118400340c13948031003d4000c480d150360317541201c0c034114410700241c00078020060140000110309007400c400d913011504817462180c00d10104100105910ba003200031510300d03007454103800010894450080c002c02d80c5041c500b01c0603500340711886c240040c00501c40c0301561103070210281c49040042d5503201c00ca4020010078640c1c001a804004080140901902d0304801c41c1e038000f081d01c644952036041980e8400110740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 312268965 1250 312267715 312267719
    0x4021803070b2b06030f0807030206131709120f150c03100515040506070305030609101514040f06050405010801150c241a0312030c03040b10030b01080106 68
    0xd018040c80005003146410780303040c0041e00b500501d90380031403580f1000d9002e50b00d0301e8010009950f00160000c5130820b40c0111a0300c1a0f0400701c076540d110080880c01400f03080001181118050784c0c14415075000390010382c1020400500506035070101c4606940100090f44c920742c41e100801c00582400c02e840080e10b0902c0c00c01a0182c0038110140048401da82c0a104015403008140200c0d000c030784003119060380c114045041c2a11038469600001d0304000700107155814903403c00000c5000348001e80315800c01d03a94051466100221078040c60002c3c1800441e0317041d00380e1094160f8086cac0d240d0711042ea407078980c2d20040010280f005034024000f254010404101942e003080340e0500400d0071070b20b896000040080f0082038001107400c01083c910746006003001c4a03142c07103006c0020481d550020403501c00c2d40d0748a6004842040080ca01c0391040c1781c4203003141400741d0141d038041e03021a82c560341103441d03d80d0307003424039000240300004003880184004013007400003541c103008012000000600c28 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 312270215 1250 312268965 312268969
    0x15090106090b180a090821010e06120a150e01090c080c030f07030b07030603121211070203060105060c0a020d0b1e010303050913020415051b280f02040218 68
    0x21141241d452040080030600001da195070101241e102001c4000000e51791158a016003450007441000710302c004d401305210182428008100c0e059582c601c0c181940c5a075658200005541c0d0241a079020350402aa4880029101c041e820401c0314000c20200c0c0d0b0144001c0c0c610b00719207101c0f1007030b600100754101c10054070b442404980e2004206501900f1541c1d22000d00c00c0d82c8118502c0300402840d11700380000c504e1440b07a4807050103598888109960b00c0c1ca980d1005100e0591442c0e0025900c3ca403140b440c1a140603842151034040e0b007e800b804042e8130741000c01042b07401c40c0708403594038016800a01c006030b8855a02c030316014801c40c40035106041107001003607103c0440290410101e607410061002c25007210544151800c02c03902d070407106820f40311100c00b900a81d0700200d4805070100c0b900441c9074200002e8101e048480c01014850014898040d44e43d00800c054404a03c07e1500a203200503040322441905500456621000c0c0c4071583c08202240d02c041c11150310f542c9130002c003003564 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 312271465 1250 312270215 312270221
    0x1110f060f0a0b06040b0f070b040303051b180d0f0507060c031b081804060504060b0714010b0a050114210105090702122a06010b1b01060305030405040e1509010609 72
    0x104000d99010482c115243d0701140581c403c50244189480d008202070080340c507800101ca445641c840140460340c242864050f001d0603003920188082c1c0e074203004250606021100390386819101c1100303201d441d0000d600f408503200030900188e0300c441c1041c000101180003000300500500c01903840c0d407001680b90030010710350a00400b442d546c2e00c0e0080c0d00040030400e00300540d0715202070300d00b45516111446000400600d0207901a941050410500107009441440a040d2550240c2d0540082440c0f0040c414200c03850744902e6584a400c0c1c003001e02a07540b04408140c8c100c040281020714100c5855402c040806d140f00a507405072002c840180001d0610a1a4581044050000b801d1404801c0d25040190041c4840d40718048507482402408a01441c0041d0108456a081e80c0c0d50f541c40300c0b43c0d075610b036104000000e01080310107a0002c19620501c01d41040b87d4022010f141824102000c102c0a410b450a001300d00e0300c0383c8110003520801d03130760885c0d0050090720700004500745080d00b03810035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 312272715 1250 312271465 312271471
    0xc0c030d020304050f0402180d0309060e1c030f270510021f1e0509032a030301032028080a02010e09061c03020304061e0c030e01110f060f 61
    0x1c542042c8030400540e2150288066009000c8802507242e0000da00101866481d1030302055215100c0c200710030038950040740440554900340c2c0c03503000c0c8441c140e040c41034410034104070000240f6440780c0d03500460f12800700b001881c2418504100d40110260500308680801c40d8a0aaa07081100040013246080c2403020f4071001e03280081d090800703c04061184907010030702c243c2d051544508001010000408100e0700c01c0c000984200100d04004c100907170341c0c0c0c1002e0390210884004c40007101043c1113001c00300c2040600d010040d40756a0865036491852043c50360302240300344001c01d40352015a41d0036007181b8050015030f00380d48000c038008401983c25071a0343c040c04c4d154000480c001d0250740c1c4100310717107103814041e80e4401440d1515404204005002c08a85812000c00071014040560220017030080b82c401350f854034481c100400300320b24404221030366040802c802d1402500024041d050001000405040c0680c0c1068080403c40c2451090403410701560802810441070002d1405641e0b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 312273965 1250 312272715 312272717
    0x10e010f05090d0305090301140a0e0a0807030e0a12031115060d11030f0307080403120e100804020109030c080a0501060e0601020c0111010f0911090619050111070b0c0c030d 76
    0x264540340350102070700034420980403d0281d80c81181031014035008000302c414601c030150007088800000d204c1e4078001401580d150f918a410540d52114810300002c0d001112900a0540b030301d040050381d402d031021100e284403150881d1150200080c0d0495420040d084030f070082c3c0300d46803201d150803005070505104002220000c0803d0b01401080e403a40403412035015030142080201500680009190414034100c041280c480021103104001032200540100ea204400140c4a41a0804e09031040c10745144d0b042c2d00301c005000180021446149480c5c0c00c240103041c03408001d901c94898610b10701240c0c100c8400f0341e005180040400c9030902c6407030018035a10b03080301c00a0829000007074550480c01c0200d410041d22844400700301e0020740c007041c0048191002000945110315202503c24207030603c15207d10030a800060186c20300140c40c4001070040074100c41584e060000640c0d41440300041d045043c81460004141d42e0582c80003008802c4964000b029140413010805181000d0400140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 312275215 1250 312273965 312273977
    0x100f09090b090129030703170408100203010e040b04140a110a060c0804030f140d030f05070309030e04020d020912060a150e160302090315010302090106030b09040b070c20010e01 78
    0x1113110920500d0245410b850328a804a20214040c006842c1c858a90006401c1d001020082c085001042004008540741c130380a4030500e0035507a00c4001280001d00c0b403c17118504240010380001c002c6145954080c2c03007092a480080a03c01d85140f501003100b80490b1600004d8805a241e0714110350020b000b0310003441c202c650700b00c8680d184a060700603403000074682002e905240e8100809100303121946202d5204642e4003801055000307000d0040c00c10760340107ca181102060b4944d1003405044132032901070b16000550740c01301d81404000e62040803081c045560074081041940e655020f140744482c0403000501e402d0510183c0c810880e030b45000f40b074842480c41881080b001e078220850507370011406242c4220285240c41c01c1d8060303c1814809640350081c0c40b0000e404444c034581c242c2c1030324020344580d80542c2e01d8030020b4088409842c00203502280301d100060000700c2d414405544808a860400404aa9641c0b0254010350000982d400006c404c8030025540d40d22016034001039909107004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 312276465 1250 312275215 312275231
    0x3060f1406060a0c06050a0e0a120305100806041101050d1104080f0706120207030e0a090213060f050d15031704090c030c08011e05090c0406080c040503060609100f09090b0901 77
    0x180800500700c1e0001c2c0305c0d07521180021004a0720754482d041c9004490140c0791200c00514203002d17204280d2200741c0100e49440c01040b0035858001402056500c1e4000030f00450322103450380d03d510100d01400504010302041079001040340d5000d101540c0503070b840c2d80c0d51107908010b071a41c1055000a0b401a03140c0c0b04410400c00b07250302c90403112403903552440050707564415040c1101c640c203580308080d800c5502c0c001c2c0022115038945c01450000540b800d0724030000d0b12140308540f12440d100c1c0480c0081c50a000c42500f01031640d00241e400c6010b192811042c1760342c5e076120100704101591316501403074003007410088103a041c040c1074042c0c1d1082c50100000203130302a018200040c18003401000300c400341010785510a260021710b006c2c0100500c0781e05180385c0f41100010b10713480f43c00341d9400114081c0c049012900240169402d03104c1c001c014107460b80e50b907030521404120042203601025403010380000d8240800d0030100140044842c045a02040e03402c1010f1010b00140042c00943c0c0340c4420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 312277715 1250 312276465 312276467
    0x60e03030408220905040b0a051003030509190f06050c0f0303010f090c021509011a010908030406051c1a09070509222a08060907050f031003060f1406060a 68
    0x803604500e8030502c040c01038042c00a441d1011a011360000c1c04100d14040521091143c118203842c032441102d0814401c0f0f81e180107030041485650b00c0024040384042c4040c0500b4a041c07846800040c075400368111040756180080071604005910007000300d8000980710395581e03c24060000000000c00080d49154901a0000b5050742207115414019031b440d040512001c0c404c2c845032107801220700102c07100d8200040504e0082c01001c85a144c01ca42141c524859940203009920454180002460030310f0314040003070310f0940c40b0301c007910510b52140002022071600351050251159114401400c094014400c1c4102101c0150101c020f0060510180780c243da50482400d42070140805100407082000c101c18003c5c180d41054150480b41c0d1191115420010100d069491482da40ea20810768032aa8180034140e1429500d400000d001044814080c1005000a58100340354028419529690b5181e450480e000144100c061680341d0074100300c070009030f0304100e410080c2158503510304403062030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 312278965 1250 312277715 312277717
    0xc030103170c07180609022b06030b04021201090203030a0210060b041410021f050a0f05040804030b060f0a08030a030605100507060f060e071e0c0b131401021303060e03030408 77
    0x110704d520503056107982d0b00159034550000701c01031103800d1040d034540b4800c20b42003108001708140301c141c0074080b006545114000e0300440040700e42005035140c4580315a003d2014083c8000c00e203000b55034948400e2030060b182000140101c045941c00380895003903500c40e180550f0615403000101c1c2e902844103101100c0071b072400c100942c0c002c4610002444c065281682000f550b8550051402c2d0032101c1c01c49400c00c184c010a1144412541c10002d11941c01c40d22030441e0020382d009801108240000d100044118032150f0700044002c14461043c19806c0000e1a9100785411007049030300302040f91007901e5014000c110281030100d0b4607085004c0c0c060390040a60141c190b0244c0a984c66052010012300c02d0703030049028000088186c0c846240250014101e04c88107101016030080303a4007030200c0188184803c440c016400705402d807298941c07565091165084031811b46044088280080c0801e13000d00c02400c068020201d00c801c0103145042c400120ba201102a03201030b0410001c00002170381e848 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 312280215 1250 312278965 312278969
    0x807030c020d05160c0f0902041707030f02120102042c0708370204060f14040f050f19090b010e04060b090d030c06050103060f18111e04050c030103170c07 68
    0x1509004c3c4003440d410440355050341580014060201e400010903500b000350010720503a8500129840ca4980c00b00078030f84d0301c03441448090001c2d45044184001441c0c070403d1205440b951100150801e81c036102810301c11501c510454018002078800306001c600040d282e00d9000c80c090030800700519148040028800c44500c0640602004d5508400d151000202410b0050000342045407501d4549001610340c0b05140e29080100308000c8500c8100804e42040300c0507500b8582c100e0720214900030510002c240b0300e4000e160b1040b8500d1454460300a1a007404008154400c030105510807070000140054074080d103454080c2d030503d502032042c4203401003124079900080d80c04040030361807410100d4450041000090000f400e01e0700000510070300e500318035000b02c2990801c014090a4100e54000c0003a00c0a004100711001c0b1058119407400c2c40d4003c404600c030343d41002036129100001400c981e002c8411285102c8044018001c1c4180b4a061403166603000ca841c503d04208035480503541e80e1a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 312281465 1250 312280215 312280237
    0x51f0b09150616050a0f0308010803070f030302070614041b0b0a020601030f02120322050409020108151f020304091503200307090e0102090102010c0207050d060e19030807030c020d05 80
    0x180c407528842d07580d0792038036030103420806480605c0e45604c4c0040b0180d0b1083e8040d8001160040041076010f000f104507140c85034000c02d003010750149550181c0203900117050035075005646240b001007450040380c40d14422440b452810342c004032516199003e0950503007005001c64014043e8001d60f54000403441d065030740064840310708280c1440001c56180507008400d11b54040419051840b10120401c184404141c842c1d852103191244c0038801180d0010001a0001e0140404203c0c43c1a038075180480c4280050b0009981028545c80030348181c858455290050344001401c118061182c03092000382180c0d49440481d0350301e581c84018490142d600003800c5540c90140c000031554041280c0c0d0001c1c0880c49060041955009002d8001c0d04565161070140d403c000c0050003035440400c28106644004211021150403600c620006096525000c2d64030300c40d48a03d16040c50144600400c0b8074865a11001e051038242401019201d22034016029944042040d02314950044140c4080a140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 312282715 1250 312281465 312281467
    0x30d0302130e060609040207150605030d05310b120a05131709211006060f0e01020c04050a02040f12050303010e0402030a0c0608060a08030c1b0d051f0b091506 70
    0xf800d000071824842c07660520ba00030720000d81c100030802d0301601180e160f180701c0300401085540b03600381070726161071483c80c000013a82004285000b41241c0c4c00b80818209003603c08a00005a102a041c900d880e6040500c0c102c0c40410145e03400b0b45100074080d44140c00090510090502c80b1050300c00e24004603005000d8030494041e580e000d0003210991301d0106c8001c11207619441c40ca40491460000700f42c584a907401840345d002081110b5000b00021a0310f103603190080040168422200c41c001207000904500820901103c04c4d6a0340c043c1c00d000c1c44400030700680e554a0022490042031440d440f00082d010301c060404040390340071047d42d0440700a0250805035030381d14030000c0d050440c0780b4001081f814401d01d0201e07002d0f5008800510845094428042c2584c4a01d04c0540e680224926081c141d400715421405903032800f89005c0007000f014225040003401503441a003022030b134410510044d41b07028840c5c11800514007410a00400c1581c00d00e041d801c00e40280710003030403804801401404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 312283965 1250 312282715 312282721
    0x303090f090e0d0c0215070605010914070e04050c070b010f050418030540080f0a02210a050607030b0103060e040201051e04080d08041101031503031d1c02030d0302130e 74
    0x1150303446e03184214050388003241c4d20086441c0140c014a4207000340e81c042468105001e10424a0181071401442162285103100998804010240030010034034620304006004040002d10b41d580351a0103060350910050300d40381800103010864070b1000d54512640c1c02c5058403c0030a03000400c688000fa0032401c4030200300c1e14010861a18080e1071000c0540440340514921020042a5040140c9540005840011110203811035481ea0f603114080d502c0400704803040e000070111540e60b000600b910094450070045510b42a00b0404201c8404001c02c1d03c0305040701c0e00d0340e454811003000e0312002c0c90202e0356091540008205016001d070355214807242c18401d10800c2c5040701514000e0481d80210b5074071010b001c100410000f0161421113220040c005000380a41c02405502c48094148801840040c55501e044618508207450012400b20754440d440181e00c0d48202520540380c3d4124100c282e8565105041c60546070600b02d50416106100103044501d4441a400440300c04440d40d00d80b580b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 312285215 1250 312283965 312283969
    0x326010b0d15050604031103010c03020c1207050a020303131a0f0d05040f0611070201030509030304030e06070c08120406110f2e09030806031207050a03050307180303090f090e0d0c02 80
    0xb06140d040b5076030202002c2400810084800380c203080c000000d500a102d0a1214901501640200c040d8110a078104006114800d00b150380940102400b0313030122484215544c0102c0e04544c0300390300b0558031192181c42440540c480504005444d03e0404c10b0310b00d01013580400400302e0003031010b12035a00b503d820110303080c02004450000180d0308140100080480e2034040c07241039001003003c1f0302007410507000408510002c01960704c40c41d010344581c00e100c1d0030142040b83d541d2188008881281005002040c20f03942002854003811508000b07658032810705002500c034258581c1e410110f540003240e001e00c0e40c5400f15809510440c1c209040c2400c3e080203420f00c0103a0020000700c020649006014010b142e0300c140c0142c082c40c0190207543c10201400c00200c1d99201d400c8000c1c040340e0200c1e82c01d1000900c118000c56214010f45070403600c1f804101d0031603030034851070761041d00000c003200c0d070611030700f10780480031401481d4880e800c00028200d0600701d80c45100e40000358090000303c0c2c0c1c450703081d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 312286465 1250 312285215 312285251
    0x5012919021606020f010c020106120326091f1802151b06010510080907060503150402180a05040902010c021021060905070305010303080f09190326010b0d 68
    0x3140c1c074880d540020f449402c0203564201000422255600306212544080d00602c00c40b000c0d501c00094040c2035010940b016100c0090b00d071200708000082d00040c1c0c5c100321503482c07a20b0207205048040d005030880c96030400c40307100c1030300c503044041460035078400f40221103480c1180c02103078107451440100789058605641e500682c4940e81d4403130b83c103c92810301d00714085405411790b00100e408800c102103a0401716141441220020400d60003114203010044c01400a154054524014491402c00d10000b04080e600040c684200d0302c3d000c03400c3f40c521807415500307080180105403420401810150002883c52484150281c0200030820341100c03002c0c401d00c001c002802a000c0300c61f0250818103403150080100e41b08510090b0f00d00404213604500c40e004a904894040c0d4074446a07441c0c5100700084400c018100d42c90381e104003000c0b0300c0c1080c26151003640490294940103503142904d100051140311192040070403042d40e10051082c00d14070020784c0d510a9410000060b40c1980445418007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 312287715 1250 312286465 312286483
    0x30601030525020106080d030e030a051317011a0f0604090f0615050c010501060503060d03050a120606180b0901080403050c150109060602010b100f210204090501291902 74
    0x40160507031a10b048540540101c02200c140d9070450740c289541f44c2044080f94680c08900710f050f00100b004c0d48086115a000c2e1800c48040340a00302250b42d0f40801c0c80c0302601450150019945500c034102c004444e41009403006c00c0207803070b804084800c980c0010618402c0d40540d0003540c1e0340f299041640304040c1c0c0583c004d49004011142805041c0d440a0001c0c2c01003841070007070358204400414000d2048040d240104000340c9a002c060316182d4050701d690b04006048070170003440090802c5000c000f800341030020401901c9601002c0105031070700300030200e1a00b041c0b015080810620300503980c003060b565441354151800685400d50303082e80740e04101c3c142c1604544e0030555000403400c0720180d80018100c03210340d0020800c01e143c0609110000d80c14010f03141c08564501c8801070070328050444840e91203a48141801d5003d031006a030f408a8119400404d2465a640014001d904601020030400c0c03c00b910700120007881010158003034801e54141c1e442000142c002494454000c000040d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 312288965 1250 312287715 312287761
    0xc0303090f26090a1203110732090a020c030403050a08090f040b01020606060309011103010306020904140c0409021b1c030b0f030a1101050c0a0c0303090501080c0306010305 76
    0x140107142000c075000c403080e59100d090480105800706001081c28101e805400000e80a0b200d101e203420a1784041001c03550b000d07814844610000004514140800c50141a030320150a601000540000002c2104406403901907462968000132942d00d000180380e10203000c24026a0311040b036402e841c294011940024018420860500204110344001d014a0039080c5c5803014403450b00700c1040300340c5151684450240e00148003103240703420024001c0d1f9210080000118290320b4184141c00983d100742d20030f5131016404500030160703203054040d006409207080d01c00b410900700100703910005d209034440c07000b1a0317500051400c60700b000b04041d801c2c00e9a0582c10348500040c0c1e080140b100d50202361200c2300180c9401200b4160b07241c0110140700705030000d00103000c001e5655603105800f0446044132414084148004804a00b007007200c00da080d441403064940a0f8914900581244160b030040307818044210304000d20f048000c002c2d0399201b0300c2441d02040589407591a14080c124a4148072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 312290215 1250 312288965 312288983
    0x1c090204111305130c0f0f05190804050114091f2702040b2d18270c1005030a11040b12150603040b040305040510030507020d09060f0c030309 62
    0x152640c0030500301000c41c3c6007581e01c4020800b10710001011a1281201800072840b004012504144182c0380f1605d24112414450f00e00300b41800070072501400700000100081220b000c100800400317004000072074850814a10a9040c40980c1a49550b000c0d04092000c0c280941003440d81c600c0c64100d0b4003805034101a41250700b51b08400c0341245010b4220a90050b070030803241649600f0400300b0510850030300d01c000c5545d2000c46961000d21003100c0c0c450b40d405180c20741a0310300c0c041d43c003400c1400341104103461251a50300d10700388054140b5041c0c107080c6940103804003c0b4241c850312407448210290b80341031640c07681c8043c11702c03000b000070300e40080d025140400c0200e8007000c0740d070090500340c2150540c0c0050781d4a005c031594030600c08102c0580c002d01c084c400b08001030124000250054030a04146044c65200c0012820840c1500e201400080c0c5480500510640502450102d4031040c030704100d2039410b10030701070305000781c51b5610002c0010a030018014544207a000c07403440c40c0d01a11038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 312291465 1250 312290215 312290227
    0x1403040c15090e0a0501031b0b030a0207110301050a0207022704290108010c02150c090603180a030309140a0c1a16050304030303050106050c070e150315040308010504021c09020411 79
    0x6003008020901007124680070341800312003880c0d0701d030150f0012038184427102861980d8504d1914041e401c05036040307034903e1079291900881d45c0c003030040780c0c40340490030b41c0144c4401d02c600400c000681c0a106111070400c0a88440501c40841d56100b030344190041c42d0303030910003910104510714a07890150340c07140d2203102d0004605d0001c10341241d4400d90003a8210f504005000060400c0e00005552040a0010401140c0030900302440510780c041c202144041806030030f0880c590038440301d400e003100025660f5001c60308100617215041c00d561800801484109007e640b254258203141c001da0700e40e511502c958032006c607900003c44444004161055000d0347c5036240c07480c3e83c2e8115020840100382071000210b00701c0d200d2000e64140828440c002c0c40b2840c42c16800d8145003d020f0550044242c10840020380c0352420447c1d0410740714040c00400035440c060030020300b04041a0000b5206600401008204403040c0003141e0854140180000d034240035403000a00a0443c00203101c41e4800110724 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 312292715 1250 312291465 312291481
    0x6150a0f0c0b0f010e100509130203120706050f10030510050a0605030a0c030c08010915020705030f070f020306090105072309090f0a050a1103130c241403040c15090e 73
    0xc03090484812091050b03054980c0c1c58281b5126071140526034119500100140122003641002e600b02800030f000c0d24000301c180c0c2903204d0f131644254000c2d80c1682e2248140070501280d8019198003101d12190503d17402d0460b81c64586554921001d4603040380c030f035400b0941e1400c099002c4002403100408440002190786010342c10701c2410f01c4291243e90311803100003082c10045c0a0310540039407103400c8080306562807085400039001f015068415220500c840204071500c80c0043c60300600484842480844a104051030102c4c01032004000380d0600301400707200c030380003020b0440c22300001c0040490300c071098281402c28010030011a901545450030710145d910030740c09881c052070565000f4007280d65400c07419003c4ea201100d15020000c01000000c0d014254038018031402c074820071161403035594070085101c0031251584521050f014040d64101e403950481c400110b1700b16540081420361910340c5030b000d6015064891030030541450302104044912564404001e04180c515501b10350601c2d0302 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 312293965 1250 312292715 312292741
    0x81e0c0f2103060f0901080d030e0105010b090105031f09060305100c05041401021005040b06150313390602010b01090e04140a0b0106020d0f03051501030209010912061406150a0f0c0b 80
    0x1400011900e400b810ae001c440041c082d06040e40c016032015403420030340c44011611a07000800d114640304045445880c3c111607001c4803c014000034a000c15101d05600b401c0d42001040c1d006502d07403924104041c100f0175081310550b000c0385d422140f0640420f00101c0180d00f0100940c0200d12044d25000821003084420804a409420300307840c50445a00c000311140c003203210544025a4003020015110b0005410244117203102410410101d0388442c00c01605030002910041c0400c03440090f2005c0c0020383d824400c0320648842481d191000318a05141c111281f40003410142007103500040800041c0380400c8402802980b026204c5c0d001c0d0396401d0000d4941c4680c02005000550041d802461503209026207801541c00d0310001c080144040019002540440441414442010f200040701d840440400c031050703000d0f0002162143e8550001c130f40326034004050500c6060350030760001d002c0000b03500b99800c501ea07504011590490361030068581c1c1e000001c0c000c0144101808100900301482 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 312295215 1250 312293965 312293983
    0x60903010212190c0207060806040f0b0d140d05041208030405071a040905010e0601021902150a0816020f1002070804050607030314060913080304081e0c0f2103060f090108 75
    0xe8001c000000413094220b0f100c2480b8418000061240c50100c0c4040c601a808414036020704140001c0302000c0d00701190b91840a032a0580304410a41da545800d09000d0001d412000464a001031802e802c000a080e50b0b030801c01e40260030389030040002030801c0001c01101e0060500c01220000d981031404c40302426501c036010b0222118107007000000c04041000f034513402120140c000d010075504084803824414101101640c1c04006030304201d02c1136a004005100d800e00d242d85600280c9410842e000d00d501101c101c0c10110340c00200c034040c104001160451180180c15400340c3d961a0504200040740a00e03000143e00090029403041095010b42c0988042c0d01c40e005040c0540e41c6180805c9420481162038080a0b4100e0002e8000070302950021030340a446603101c3c40c241450350404804040b140c100e0910030340800100011102c03401c10211890468110040171004012289040401c1d2100c0b41c05141074000320225640d9502c0320303e0b228807841c005d401d1022660355844881d588101d80f03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 312296465 1250 312295215 312295261
    0xf02040803040833040203010605090703020a030615090b03070909021209010b0d0c0504240e1b0a0e010c0614150a0b0304080702010c1a010e0a05180606060903010212 73
    0x90441c41c015510201c441c184c4106078000f4007101c526402280404511006004a905541e607120118959076050f07d001d010380502c3e84e0040e2034207511240034046807555086101b202c11840d4800c0d00003a40411307050107541c2d10800854407a29813502c143c42e0340113030740c0100c02480d0000c103051000702c0e4a55080c034400e1094030000d02000c3e03148024041040795100f030140412603521414003403410550804050000704500c01e510a9a90380d031401e541201c2900090710488814042c00107806140d2301c00d14070a401500c0382480c0070156400540035069020303809040c46510944030060080943c0140504c1207884079070801e40c86c0040d26031a81050246040e4480e40c2c41d0000400d00003440c405480c0300341d07407014690b450f101e520b40041d910303c1104003040340d100c0b5960003201180300385149000c0c003c04aa0112880b1130422071400019103100409184004900c0d02c400914035100007407243d0040c030300f034440030740d200500008079005e445417001e11040d60000f082400044a40710384d51990883c11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 312297715 1250 312296465 312296473
    0x110f0a0b01170d050901200d11060c0405010e010504030503130e0907060903020402070c050a0b0903100209030a02090a0f020c0a02030d110307060b04022514160b0d0f020408030408 79
    0xc2e0030140045807011010140c0980c4a03901c06040d9500480050002c42c9050415180301d48550a0a4082032a04c00d0001000e400000001100e0b6822800450355000018003070403403450031032010301d81c0740118850a810000d14000c00309050340101c2c129006180c2040580e0364594030351007030700c200d82a9441840020031a000000c2e400c000003058410558005545402603c0d25507000c2001039041010161010a012040018559180104400101081c0c410641c9442c000006c043c100400c4414120303180340100902500b5960115054404a904070380355952500d860407075400510003200e00720038403840040e1100001000040c0b0000c4507200314221005615121005c84890000f034800300280d03881400f16100182c81a00144100e0102810045c103000c1c12403008071f112284942000790140f022040071003408208042d420411890318001c140c0009a04179894502109115041d070541c40407400404101094018903c0014040c0066403917a40380c00c562501c81c1d00c544600c5110b841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 312298965 1250 312297715 312297719
    0x203060f04050405010c1d030a060e0c04020a02070609090603120c05010b030609010b0f15120a0b03030a031a03070f0b090a0f0e061e0105030411010e04050403051306030504051b01110f0a0b01 84
    0x4445205004c1281d030107806812409e4980c0c1d070310405003001442c22071003402035688201c0701e91900c7c07000e04541880c5900800246250000191014110b03420003031840742080024004152072080d0303030b80c50214501e840544040c07c1c1c10304c1c900401c10011000e506018050034802d11490542000309075000440300031a0b401e0301c4a04104030a08003103e5003c03905000c0c044c5c901c900e1459004c0d5944600402400300d1107400303400020b400c0d540a203040802090ba86c400e11001c4950712080c40a00650640c0140340c1c0c0741c00d00c1060307541e0320550303c2a4100e11000103a00170300c58880d25540c200030501c1030b04510320703151107000329602d040044405502030712034440b0500c003104d10704414080012040e1250b905c0e5407182c0d181d0305048860400200d05100421959030b0740e0fa1181c1c031906219901030303540c041c4c6445050f0502411403800340c1c80a001c1604120500020507004251800554a145003940c0700078001c0c8016640309e40000030345101e90142c0f69200d107403020085405ca00f034a2240300c1c404441c3c1e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 312300215 1250 312298965 312298997
    0x60b0406020c0913031b12030203190c0801051e03030403050d030545060703050610031e02130b040e07020d1707080403030b03070303230f07060203060f04050405010c 73
    0x1580440d04e141c840d1604440d002d010078041c503840014201e00041040d42d48603203450f040c020502188031000001d5001040240100ac2c06d00c400040c118011000e204a402c048002032807030006001e62031143d42003900308040303070700c00c80355408052002906580c1c98507628240036031a08041080c1e040400e08110024100900c40300d04442d0b0403801c1c1e00441c00031581034003000c15600b5011030000030180c04016103d4486001c0141d02c0c03082056560110700c618044052001340c0c40c1001c140011316050504000e0b04040b881d0410a1401c16080016124100c0d4407603189143d1990340f0010040c1000640480c0401111402610401d41e5030201c07414010303496401c4402c82c0d800405020703920070032004507a40d18800c1840b00d0b041070003483c02003540341200001a06014055008038003080c0c488103402444014020f41d8114140b00346801820001c13490a4401c07a0307c00d00c3d00c010320990b80000003800f25941e14400b00c001140281c01040f480c6402d1070101d0080c02108564400718a401b02261128 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 312301465 1250 312300215 312300229
    0xa060915050c0d0804020126101719050102130308030a0e030301050f060c0f0d0908120c0a1b031b1805060f0409170d02191805060903010f060b0406020c 67
    0xc500710b840200000318880c0001c81d0340710b01c0070700101d0411032104d104007011609442c111a018401125120442c1000c00480c030203103896501200341c0070250310506841d85004100c0a0724084403940f083e50302242d0f480c0c05402441003ca0840358200416808014800307502c000e94030452000d40e080214a061444a90381c0f40001d1003400e80c40b17040050041182e041103809030024141ca10111041010704a80c3e2500700007070cc0f02c0440005504d044100075406040108003c0086140e14003841c0c210088407460302c0301d4040710058070be007a2540c640c641c2c2007018031a0000441d04204505041d01c250881400c0c2804e0741d2250140a001c0d9009880668803607208150042800070582495000d8040030311000e011a8032050790741c158042140020094014000c0c4070540348100018bd456185252040703100ea28840c0e100100080e03001503481401c250781d80c0905440c1c0481c0c40d0b5441c1c0390f290000034050a14900c0241108d41014000a0b03c80c48610207130058444e26003e07608400ca454061201c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 312302715 1250 312301465 312301477
    0x106021203040f030507020307030b06011206083a09141903060b040204080f010506030d09150804170711090106050a080f0403090b0a0206010503011103160311090a06091505 76
    0x40000410115000540e0b01122810544c800d052a5003001400e0b00000d00308083c5500544080d0030202c01c1000c1507a000805030780e5a04044000c01150f4100f907a5240d0b00c8105410010810490403207451a9500302160701c2e18402c084400703810303488e680340d0004041e09590312502c411141e01d04040d600924107007114101c01c40c00e900003500c01501d1611610090149200c440360407030741c01c100100e0000000e003d4100139503050000480c0c0c40c1040418036103084074660854007084501305083c06003410a41000220010503d04003002d0f031191701f4101ca000b00c2a80140700b00401c0001c02c1c034100039040e100340c0d00b40c0900316001c40060b0380e9110f090303425204860405001034041c034001191601c0487c0c8440c0c0181c06403600e07107040f0780c17141d54007000c540c403c001c5280035a2007080104154a824010742081c501c403209014214104034088401031958072441e1800d05032928002c44c1901f240509550841c800101070456060340d4400141c03008500d80110591a01c05110901d01e85010b00d00f1102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 312303965 1250 312302715 312302743
    0x50c0d0303140606121501050d0212060a140603070302180915150f0d09050106030503040b1306090b091e090109020a0e04020a0c0b0a090204060b2106030304051c17040608010602 78
    0x30f995440c1b020512140c0d1007070220f5814000c0600111002e40c40b03c2c0301600c0080e002026011190412034208021115150301810213207003c1088800786847c0c074020359402c201c45043c00b40c0c40d00031000303030450180e0703000c001d254011704650208449040740e041c1c00c015898040e24101c3d150000d5245000243c42070405c042d10100003084003000c1d0f21441c0d80a1900c1a0040000240c01510f90b5951802d55115030b0200300ca0200125400b1484403900050000804440c03c2c14500d080c5080b40400c01e81c0900c0c1c0105120701040d0f600c444c5902d0120405202c103000082050916686901204000f5007086c5030407800111071843e4401a800d00340f00f00e66000d4402d845181800403266580100722070010f0003000c016440d00114001602d49000b01006001116040f64507008a54091101c0c130301c0c0c0b0100d560098075a10f003802603984011084505507407083d20201602100700c4505a01030707020000c000d15801180c0e902006400b20600680191501075507041201e9a070398400300e0b981c2c100f040c07100c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 312305215 1250 312303965 312303997
    0x8040b1302030c0112200417030310030201052107052a100207080d0603030e04050a02091809030c0f03040e10030c09020307091e03150908070f050c0d0303140606 71
    0x690350b6029105100c2101e1401001050701001d0302007a00c850581d03503035199081c6e00d0104041c05000200c2100c0018540368a00950442c9050340240f0320000503840301a0603c4070010b0728000200c0d104009038004151031580c2d000b10309004000802c00c1d449045990440010412101088a40501a15112800c0c007009200c049941c0f80800001d510005080355082c4040008100c03203681c601803180154000c7d00c031118100c800c081444282e54006180c1c0e00b0492041010300400d42d550b414082d003001c0d0003580901c2c1c55032840c1d0803074554800c0005100c40d91040c1d8035901010b4100100900a54125012107400c54a91074000d03086810346001c0206480c0080d4000d1102203810307405141d10400c54502040a40d507500c00b072250b0400320800d800c413107803043c503001e10610425408000100c8100716080140600f40c3d2102c10840c0111200207025058100000d02400310804c0603130602200100400f48100a03882e010f0020080100c107207092011200005440d0724040707041c0d40d2007064410b410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 312306465 1250 312305215 312305233
    0xe1209060f07020d0f0c0603062702130e0105040b0406060c030e0d020a1701050c040621020906030f0108010608010b0d1202100e070e091603201008040b130203 70
    0x20a094206080d103041e81c241c244250005607440610420200340a0350200783d800d055070400003210b00083e00524141030034a03808000c407401ca642c040c5959000529411788601c20410b0f01d1001c0e100c1c030261202110140100815085200b400e40360403131382c1c101c504108441030b000a0100b0f4404034400c810100380d09642100200c2d02400a143c200300000742400799010701a8001081802650003280c0024045515880c0c074110901c900c51f003003078080c4121420940380040041a042004c0c5161400507013204031552504c55540665440580c000d05464a900d007148507540341d01024800d071141c030740c20f20030002000d180600c42c4551144024040442016090303c6501d54645c1d0600050700318807640b00c1d022802c290500c41e034003c2d0003449010b401301d146808032850311542e002e0018a080e40148900b4014808901500021260b2020a58030346d002a0344041c000c00700403003208c1d034220750700f20510f141280c0d000d0f640c103120b00d205401c10703107803516091550381c80408020b90081d00345d84900e00d9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 312307715 1250 312306465 312306469
    0x102010b0f090712020409020406050703020d02070312210501120302390102030922111624061e06050309060c0c0a0501060909030908030c190807061506030e1209 71
    0x21020044001c4d0050b10b0990365422000403070384681d20030800250003244410426506000355154000c461004107402e03411070b05d41009030a401c54000083c003280702e85071049000504c2c41c030701510440c002d080101d581c3d6981076030507020008204174014090604041d00111a030141200404102028826024190b1482c084041081240c03281235210a1040968940d035255807650640b00c02d02c003007401401c5065070701c81618840c082c98007403a1414032641006c40c5803200c1c000080c41d0004400803101c0c468800c03048505074400400390481d41400d0300443c0502c04190040740f04881c8000280d156540c03007408490074082611904000c1c1c01c0700000c118001c5001c800381c8000c3c014002035495a043c140d4802e0308607601d030f44c4119070454540e0351200a240c0c1003004480101120b00c0918a001011100c007512214201e074000d0420300c14050740000e001c0844160740c0c00b580d021200b001074400b20641034210005902c02d210000b4109550444001408520f00c0c1916441104a6040c0440032003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 312308965 1250 312307715 312307727
    0x105040f1712070c11030a06060509060d0b040f0309031223160f1e050708070509061f0c12181e0306050c0d0c08010611010204060914012c0102010b0f0907 68
    0x8003034072203175940e0341000e900c4e0f5002d200c3c102003240700d5140054000d00e000c0c2480a28080200854450030b16611400c0100700024800d55119510258940d000700d410715003030391126104d420160090081440d00c000e29904001229140d80c2134021a0305006e421035081c00341e0f807041081c44505e1800040e030340301c000b43c00400100c140a00c910b1030f102030241e912800c20003894280380c050354240d10400040014910610500300605001d940400c1c540c17a00d030300892001360660b8000d41c5a010381c101040800d031320684060214683c419103115000c0e807058002044d4505030003030403a0702c2c14429000903a00c141c0d1814004424400d8032075004051442d100c090042034001c1074075001c4503041000c1040b400c40c510505054490035181c00317801e541000c03802444c040e0001c0241040fa0f1040000b0b000c2990041c41010031140500d84041b1000e0304c2c903004a4208204091040c3c4e0103007420481c407013a02c035074071811400c0c801c00e9008100190b0514100400d0994118600d9044600c41012030742051060b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 312310215 1250 312308965 312308987
    0x81207030f0213090b030d0822120c02010f020601061d010e060c032205030a020f120609250e1605040e07091a07020915040e0105040f171207 62
    0x414001590101e003000c0300140d070701c10007000103812400101441455540d21454000d0a82500144809888100c02400020001d4000d03c058a06407001d10719449003d0388054115034040344422808010413805406828803c000b2808a10312030b0410049920014006048038410781d9081c031895a40c0c074600f1030145501005034100101c00c0304516003512200c0090180403140401903580e40480b9080b84429044810b4102d214507a03440108402c0d0307000031307210680300e804850690700c0141c0030740003a81c2800310440030321030b40c06141c040040c0380324081500d684c02e195101509103c0303203074200c281d144a080d41c05402d9030099544081803a803203114546045000040c02d00d6450aa02d90580b100d80c110201c0301c10000078010b560502040120b00c008a0340400c0c004101c0e428520030340e0001c0c481e203000500c0c0503990860010b0300c18650b42d464210109070340a4000800850500c1c0c100100000c00072401580c50041645034050364580304021039010010004180c0c0d50341e1980402201d07000004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 312311465 1250 312310215 312310217
    0x50306010908060f0f06010f02150c07021c060b06070f0b0c04170106061d03100f0605040221070804031d03120a02030307090803031b130803030103150513081207 71
    0x354002c10b482808006290041c80503080145481c41d152a890700031802c02041241003281000c00c010340c081e0001744840408050000c2d00141d6611060a40b00d80d002e891030281d84141400365458800000d03042e0001042d004940500c551100781c4140585032280135402880d407102c1d401d810010035460406d09411000d8260124607183d40ca640c03443d94803c1c03510703005d036640e550351808104079508086d00411146003004481c40c20308254001940f581840d0000c402d80d5900c4500d2190103024907481440a0280100110f40b1003048401600204a00c880544001d418900103e042113025408092199a00d9030f11664070110811b10748000f0211000000d81511416405003200004800074203d242c019070f00440d101d14000c0e01c010080b01c107030382c007605264001304240501c5482034040003514481140c0060740c1c40c0d00c4020b19140d02d6485a01100b42400040b00100800400c3e504d00c0903600c440003020301c00e581b40c0041d0080040310b52100101048002c002c07001d01600d070441c19551014003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 312312715 1250 312311465 312311477
    0x509060d0b0c0a030c0f120515060406020c0307140d03050f120f2502031b030f0f040509090304080c0d050c03070602240c18150703031b110a0305030601 67
    0x515695125208020382d0002080c96011603c003112640c503200b9008a0344503440c041e00060040701001d0140c014641101c1e007121344032000184265240000c004007000090300c400ea0f6503540d1080203403a5076907280f08a110b40205040002d1116100c1489460840000d001c0164422241d400755140e51060f2202c0028103000e12101c21200301441c8178600c10505210f86840d030346405c004002e000f0f95031007174840d11140400c12260307041d079000007584c40703103158200480059590590350a01d140034602d15030851400014071480000100300140040311801d480d006c030746032105601d40c0d0f00c6c1d00907801002981d49c0801214500b0b45441c0c90a085040d010f0820ba4207003c011401190070001150025009640001c18010040590b241509101c0e00c00c0d000c09552410700d80300314a0310340314003400b803071040300d907450004403a91b645036204c982c640c101c5803400c2d59504145800f801919081c0e030380c2c44aa90f5800d200b84480b5000c0d82c01c8407940c0c01180041c0240010301e035825034842c4c0002d00b103e410010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 312313965 1250 312312715 312312739
    0x312070c0c0306050402040e0f0703120c140f010b060403240f020a0804050d0207060c020906060c0303010806160507151e0c0302131505041203210b030606040b0604050906 75
    0x5944048902550042a0200e13081c03a050040c481a81c04e4900040712607030012803107000c4114003166141c2940d60003140c51414040440c402c443c03016040c000a80140c001c100740f00d0304040002a5038542441c40e5000740700c520b0031201000443e0040f84070141c031800b24249684109a081e10403200760705400e23000001c800046142000c202d03080102081c0204003200180814000f0412981101040b01d20080c8100c030700f800c400070300070032800350002d00800c80b1401041c3d065540c0001d690310025550b0403640c5a41e541c850385650f8200c156021990049181d4000010314483d034100c600d034075001030382141a00141858000145060304031000394070f02c0d040c102650800710340500c0c9034001c00c95801685410302e08152031031481060b03112111003000074454075549500541034404644104128030f02480301818103403000d10580100c0300c9085944c000d500b41c801c599078005e45a800059080b10341c030340d4550003440110b5040180c5254082401e0000f0005883d2034a680384c0d000e000540340390030540b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 312315215 1250 312313965 312313973
    0x11701020d0c030b150414060c030702040905070e10030c0506031506130915060c030f030f0c200f07180e030304060e121810113304050312070c 63
    0xc0c490b0308a640c00aa1076003540e459620340303c146608101c403107411081c6007038680001c201054040c0201203016120104a00c0d030041003e00c01d0303541240c4c01070414007551a507032404c00e813243c10602070001c001c20301401150b818800c506c8031900750b03030b0b000b44e0f14070205040c03d007001407e401c003c1903121850301c0e000400019482d50800f4000382240900707050b01e0745050511a1095490402443c0b8181958500030045154880c001444107901070520301808480504103c0241c440d11a6414850b0300340003220074140d0740104450000e2800c4084000b07000744080c00b4a03211080508003c4180d84600070612815204c0a42407a0316805401c00096140e400034449040d07400c120740c1900c44555454004480c84024000390a003800384c00191450319070003468400803c0502405030f801010b024010b82c3c500b5005e0400030501641c0c038001c50307014403051307007040840d4800040d484805a042c48000794115020500050103188e010020b1800c2015111403541403020040a0a0800038880c1c41c074000300d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 312316465 1250 312315215 312315221
    0x90a0518010f0c03060909020a0509071101060b1e0c15130507080609070b0a0207090b0f130c0e0118050409111207030c150c020909030c01020c060919030503011701020d 74
    0x207810880e000f041d0300845400c09804c45025a105d008040d0602840e040169a42a443e5055880c200d0b503000c8240c5403c5012180f10450b14028101586008404100d486440c00940800e02e65041c494035240341d648810105806800480091984680c648001501c002c4c503038264091403444440030143c04a0b02c40618003003180c2e001038029080751b800c1c0201180300f0311001000e4500350ba8014600450305a00075600c1c1741d14030884405035994414103681b5034440f1802c1c005008000c000f4100a120402000b0080c0028039005c004038020940060482d402426504040f040400d06040034520340010f02c0302404200c0d030216241e081c2c0f5040761040d50745c1e0011403100591098024821503042d80303405440e0000e150020311016a001d41d03443c6469a0101a0140c942c1d4196483c290580310120710b42d02e18054170498004a50022400203580c0714002000d0303200da40e985045031100312031038403c000050408000600021010401480503009000400303a40108000c001171821112408030030403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 312317715 1250 312316465 312316481
    0x307110402310905010324060f060e010816021005150306130c081606030c2c030c0a08060f04240504150b0112090c0902040b040303080108030306090a051801 69
    0x2c2500541c4200104003003980030000b403e8008000c0240e541151030b000c0f02040c1120700d1007901a0304012658481540750420350052002c3c904005200e1b458400180c6642e181c500d0450020701c0341d00005035080c20351034142c0e0100549401030004c40c822642483c001d0040144403401640c0e018084118544042107903a1048038501442c00501d08249094502d00385203034800c140c1940321180c4030503280c95000000040b641275080c001052408003038242e5618888007903c00700d401d054001c1044408901d20b0000010034211700742d072684010340e01044010103450040785400d511100000d150050040a0640c10a0040c6001c1c02c10724907040745821345580230902d040c542a261000e03c410401d0400008240402c115420b02c00c20304a140001d00e00c0d8165500944020b45400c1000d040c016014600b50140480744030a641d6a5140e011007030041c0d01c18071007200000d2040c0c00028001001209481c05400000d0001c09241c981700300d40c0c009000003401c140c41c80038040310358910a072030912503c80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 312318965 1250 312317715 312317767
    0x41b12180b090d020f03190c05010e0d0f030e01020f040504092414090c090606130b04080a1214090f0a180501060207050d02060f0f04050d0b0103150e0307110402 71
    0x400d4070340d00100074200900440d0040f40c0d5802440100c9051800f820803001f0071840789807044508105081140c054981c0f0071016603280507070100300c18000c2e400000c0da4101c0381281c800381710b040407000d440b42c205e20843e400240517070030a01c01484a071034941c200fa054140541d02d44040107039241070020f1882c028803a4890890b540340b0141c0c1900002100390744c1d00000840260104541c1180030a88000d0000e0440e84659000103110281e20100c2c1000c02c060407091080645450301c0700e640707e035030343d007032000582d10500c0080640a995105001548501c0ca03607003c020300b80901e01c410300c040c02100b10b8441d41e1110f0b28440c00b003801d0054a803001d44040d00d444002c9000e504d442c40207030510843da000107014403800c030600c80168490300704944100036815a010356901750380303601c5034150045420241c1e0101134101d44d1814081a01182da043e207010308141d01c0300c2c814010b01201211090800200d540e003040c485200800c00706c52140020945c0980054034102c004101548415101d896008c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 312320215 1250 312318965 312318973
    0x60106030f110403030813021c0302031c06081009240f0b01020c0303180f120a030f05090d030305060d0204180309081b0904050723041b12180b09 64
    0x1512060250080b04084403422146618150661320002d120550013000c9070300840303090280f0800c64035840c0800500c00c591218250041c006480e000b5141e60150081403c108203129412524549520541045512100084c02502c04d54000780d000380c0f0317940c00281c6010708482e2048501c0101c83c80f800c0103031070018400140403901c0d41405400c42d1441542e16046511043d80c16840342c80000803605401d903800f41d00e1034868042030004003120b0440110b9908003200b80e0341190051000180418114032907241e1a000040c420300031211030003110380c0c1a0b4800c2010340643d020074004c0d0700c02c80d003182002d403480d8180e407002d4000c0790648182c885141908001304d10b4190030b165200c0c501e40e003d0680c9001410f02584021030782d818903010513410380e104000e2030300411700708001004036100602c0e04041c81c0c2c0c0c655111100079540c81404002c0c9a01480c1003400141031407403019010389203801d0035110350007402450f001700d00c0240720451144008607200103804000c20402c901151041000340020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 312321465 1250 312320215 312320231
    0x120315040f0603020114090f060703051b06071b060b10020d030c02010204180209012303060406050f0102060a0f02210703150b0706020a1214060a05060703080a1a0306010603 76
    0x40811a1848862001d1007840c08030305000503a884400b50960350280b01c840e50702c81460307800091101940c1d955881d0f103e0400140742d810550018041e0202c42521090506240070010740584ca0b100c040342c20350300152110a05950b00d148100e003248060740164800110034800f00301180425003c00c00329400342e80903c00348080654540180b090742510ba1000790704051502041940c041d206010b00b030452500454107240b580d100f80301149591030a614804005010f00f035554038103900c00e0f54080d00540c00e00c0d4000c0b8241c1400d01911843c80e0b0181d006203081d85c0d4000d240c200915051410700c000c29000c00c0104004049141d401540f4140c0c0036586d00e50742482c401c060200c900e0000c0b8109151100740c0304002c0c41040750f0907220810f42013140540e582e50040c004407000112000450060307468058a151006071a1000900c80c40050f19220307505500c0d4000c10403140904900100020300701d9000403484012504641c00410041114503860480040005e081c45002d801c5440000c2e954840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 312322715 1250 312321465 312321469
    0xb0310091d2b050a09210203100605150708070f060b0307080601090e06272e0524010c110a0e090c1c08130f060203091801060e0111120315 61
    0x100c250b4080c564207006140008030fa40c0900060401e01c1120050038070140488500349481c844101d040d42e005041d5158805801200e90040000d070151501507100000200c481c0c000c10307800c030380045410030001030600c9141d80da9a0b414107000300c001c860030740d202c0d0041c00564038100029005425008058240c56061681d80000c803121000c1c01403450340020103001008107030356440003040d600c8401d514264094241c0781454114401c424a204840e080f004412009050501c2c84070328008071002d01c129118206851001c09000b0221701409402aa0800c5c09601602e61080382c0d0303206946d150001d40d403045c0010030070a84e80e030040c00808040e404000084100f840036180e001d00484040c200b10507080d200c0c0c0982d02d580e0078000c041080c0002d81848400039290108000e01030085425403258544c00003d40740e4001442090068a100510840000d8120511410ba403116038600c07082411860045554071551441001680030b040d0400421501080046114006a4080507402045002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 312323965 1250 312322715 312322783
    0x2060301081e0606090103080c0c150a080a05040b150d0212030304020306180304140105070f08041e0803121e04030c020f180a0f0b04090606050a0b0310091d 69
    0x4460099003043e01004400d03501e0010312415a500000542d4031400301301c0313803545041030282603c1e502040078076010901c24030090040610074426500e005854541c04804801d07107000b5500246007103580c20000c0c4064003000d222188222004100796007003d03554010541c000305280001460303400000800095060410400381c2050301c5a00111140c4449074049449029500580800c2d4405400c40009688141c058500340c940001c1d8103c0114078500e0090700c0b940c0140310303142150030025840c0810001401020044074206d8029519094810b031408581880003410b0225003032003500c60640050004121a02c0b8a2003511901c3c65074a0600400c95001c2000305a02d12a68506180f40c0903c005e02400d1074000141c08008110b44600c501c40002038041c441c2250f030400e1510341c0040521200e80c00003421101d054031001c050707039120f10b80b10090b44070468903d03404410500041202800343d504c076036000100c040c3d00080c1030b03810701142c90825103c2c0c1c0d901920b0a6450740d1650305800702e0700c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 312325215 1250 312323965 312324013
    0x30b06030a0f0b100b030708010312050c070509040501061205031e07020f0d02270a0b0d0201320c010209040f05010f0b0d0207080a0f020d0302070206030c03040507030206030108 78
    0x9008140840a690b0340384560845400000c1c00300f5041400710f00c084007003a840c5000b6001e03403000c2c281c807441c0240000b000441d092005844000c0c04030704034950140610102c400156003000500003050038001407014020780900100c0f103d43d0799150004004c034a0003a415822445000134641c0ca030381110f220003004140e80f6000c05410000c00a41c0300580e1120394594a222041d1140740400a280c000100c1c452009103d1001840c841201d01d21080b0480300c400c1c6c410340e803903a010400e0b292000e042c44000408410002c2c086010300046200004040b030028440c0c0d03070b4031081c2040605401c1c03d18942508520002034040e074000c992217074103182c507001c1d1403000210b40008001c1580b6000040c8018091071040d40380102c4009000060b02c002070701115075803604103802a94912461000400d2010043c15601c0103015140320964a140300c1c0c001c580465070010001030450700c0c0c06980588591020348201c1d40e42c032404400000680368203010303500030004e0a0150101c914078940c0342c481d00e40c442d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 312326465 1250 312325215 312325219
    0x1030504141c09061b0609060b09100801060e0f010b0c0102070206130801141614071a01030b010603060f0b03071205040305031f12080f07060603050d030e0118020103020a1803080301030b06 83
    0x16000d15201c0003034446020061710b0300302e0000f08003601e050030001c0c0100200c03140650020000c030104000c14010711450401c0307421240007000720a90300c041514111005880c02480e0860402c0104140510391001d00030112840000500d058100d40c0020103691141d5014290451910401c00c041c14007885001040b580c3d000c0d881c00daa05d85400c0d03101c5c030003845800241c24405000352854407640a04250b03100c580d44040e1111481c10300400d201c070031080c244000c9840502110010400c0d41c480d0280703008494502080c1840c50b41000b1454030319802c01058402040340c40e0803000c02c203d100e4003803240254083c0c3c480742d680b81000010b40c082d8001e1601325540080044d4000c20009803d00c1b483c5031416001b03d000d980703c1a440381c00804e28410742002829583c01d15801106006010402c0c0b5020a40340d141041081c0059003038500b0707200501080810b8600720728109003d540260010f12064420385070010100b000c103e094503c2d44400c0c0c1059030401000710043c400c021159925540122007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 312327715 1250 312326465 312326477
    0xd0515011805160c080d15090209040501080d02060423061603050603010209060418090510050a05060a140f1504090b18090d030b040b0d05010c1d030304030201030504141c0906 77
    0x2078050060b040c0519804c00a00b1003500045411150440b5849003c07000c2c47c2850704c1842c0340e55450203e01a40101110314440c624082c000a48140300042c40d0031002e40365009040107607200d8540d61901c030b400d12016000b0645800300843c26420600c0051311a04210083d1030120304501c05c000c0071140c4c014529406a88100920611a0368210a84082f070752642d051816400384d0045200180001c028028103c1c4202088003030741b0111034200c40c0c03240040070410002641c9820401038a049148110345081c0c2c114002c05006041041681c0e00d05403018003180d01d070180342821001c165016a01005000c2d98524019080345044d44582543c2e0740081d00900603810902249610345222800c0c11082c1540d400101d0f030344c1d8886410900c080c6400500e502d84d00a86801c0550280c26481203401c0064642e03244208a101e95402c002803c890140003182058155801540203004c054410b84070301459100d0035884070000c0000c0b20b006484400c03c0c0000800407807014080c04881d801110501c46 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 312328965 1250 312327715 312327751
    0x9050d0207081525020706120915180c140a0e040b0610090503011b08090703050606060919060f020706021504120e04050411120a0206090d0515011805 66
    0x400003e0700140c07038540c8100c0c1d556a40b941d0203e065003000303181c100e6041c89002d1070b840b905140c01041e40011200c0d039031200b5103040c080320004000c6598102e4014941460000303d0400c28129502454003140c0b07841401801c100107841e400701181c100c1c0d00000b00c401c04407260444509100c03000900400d0495008611800c00c0d80e512a0b507400001e0145010b005180c041d04400b52098203d2401000701034001c00c0307900001811001c102e0708072070710f88010828060109103110070020740102281e8010340940800d4580380c0c204840c075032280401a5220030303a5090401c1c42d6511151140080240d5250014044e00c600c00181c100070301c940c441070039500000700c0203001c031a03800340f141c1e070081d0300038100d207030f400483d9406440800301c0c000c4040d001480c10080100708240040c09411100003103400300d9400c201e04d4101d590721609008000e4101206202c4902030341000203681500c140703d1000d40340100c0f403020711262442c400741c1c06030344a40b200c2e5440d2885414144103403070b0003503409120007075080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 312330215 1250 312328965 312328979
    0x50d09050306040203100c050f0a03150501112e02041701050907140f150307090503010b0f130f0b120607030b0a06050901200106090207060e060601080a200a0309050d0207 75
    0x240c2c2c0001c1b5411615120820482c45611030403c0f60140f0445842260720b0b4104620007c000346904818032000a400c2c03c408140d940c0034032000c030008941d05004148405203047c0c808000f203807010020302214840b85004407404002d001420142517600340305103140d100c3c0d0b5030340d90a484010b004038209801444040c800c401e06858940c42d101802d1380c04c8400c41c00c0900c08100c01c482a50f008042400300401171141136a403150041c0c04071502100248003d40c21070f001c105501506004003540308018103200c11b440f291980050545c4400f00400040310010303400070030f1020009030002d8803283c011204203c004c50b0148910751402e00c0a41d0718404103820080060400d10030501d03040d044c0310700e00e05032120040c0300407440f08203c0c42e031070000d00080742d9810703441d406500b04507011038940d800c00c1540d450540d000101e89105600c140e40741155512280c40a80042241513081071004403c1d0303680340c100c910110300500c03e60036259000180d03000c42e42030140c10040595046001c41d040010200921 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 312331465 1250 312330215 312330223
    0x1413020304120305221101020d03020a2001020c190c0e0606030103030e19080718020307020309011803050d110105061822020904030c1203050106090e040f0c03050d09050306040203 79
    0xb40d8a181000201502c0f0f12182c4481c04495444214185412159030410403010740403460342102e0030303001c45a25404064065007a801188082c81c009144200304031a04500d400444014960718000103141024401c485070805840540700c4010ba001204090208240620b60100070041024810000c1c00c10800040c030510041c0b1000e0108060940b21004d5030380c03517224903001c00c00440074801c0110307a910342c101d4481707030640706401c451009406480c60801540c004c80c1d01c00e11941c2d0155141401910046d40c8020034100e101769440146880071000800411505089619988070000341602440c002c909540e030003002d0901500c109040c2e90001050324505581011681d075103900481e820752a00c0d42c001c1680c01010394005044c6007030000380b58201508544460140382c00c480c1d80146120213805407082880385000042100200300305c054045129590481d12440051088921b0350711560041c4d600c90300709894582003c0c50500c0ad50342c0044003c00201010780c00f405a5107420780020b81c031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 312332715 1250 312331465 312331493
    0x21606080103031428030f06260307150b0a080c010206010311150304060504050712120c030905030a4b06060806070203090102012003041203151413020304 68
    0x5004800d000c0c80d90355510502510248202400b405d11815040040003002d01441e00760040801d1a20500101d542c0c1d0314010341d03094419405040c242c0c10303092406900d505141d40c02003003483c0014441080050300e0300c01200e101350041040418203000e02820410b2080709540a410141d01401c1e0007604c60760003003846070460b178001121001c409a005c011640c00b0b4028100b0850220002041204201c210340c0f2040c02140524210f51005813504d0084d16045807031a00a0941c900311032284540610401d2140100c91180c0361408106a0701c1c00460720381001d0301e13070460342c504510a418010303041c084680c0c01c282540b02e0300c01c8074a43c0b803e240f84030f80c4100c0e0488610110401c2445000340308054001310010542c3c2c0341100d0b418500800b000b5104d80050100b9070040d400d00c607010403020000d055141410041d56001071035a01c0741e03542c0c0011303a503a4990788803d26072170b07120000042c00e0302140e1a0081040100c8010600c40c202c0401500039a05520111150700c14414840421001e54042003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 312333965 1250 312332715 312332717
    0x6070c030219030305040c0b0a02150402060409110706050f010f140303370203270301150b0a02010b030703031416060f09150509190c080d020303010602160608010303 73
    0x540825824202d080c4880c6101c0c904041075410202d0040540c181d1045214a001c1c005640b080d0780c503001840030310f02c250a400700042c2e110f8200140000c15801c84560018030003030140d0303d0a1303a5842401d040c0c274900107071034261038000304400e000e100050040c20f501a008a034040e903e98140f13005518412810700422034240948409040700d030724104200c1d080100d40145403922030b01d075051405115030400103c1c540005426040d9078000b800023040d90300d00030903000c0c0042c0b00c944501e480d10b09402084400c0d0307455034a9407400718200079140c2040303018045d1058801e03a5440305c084042d09450078021407038003030b40c0405000c00102c1d030300644080e00e111403150207aa44820f4101c2c5e5428514100101030901403070f000d18000351030101d5200c21601803060450808141d1101c00d83c400319001210706006580042d0030ba800b400030841d0200701418030a100c415080b540f81e42d4101c0c0781554001420015074800001484140c0c2c04019951f202c0904040d000030050905000a002c1c890621000f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 312335215 1250 312333965 312333977
    0xf070e011121070c080d1101090312050c0904060602061608041a100e15090f040b01090c0201020d020c010903030e0303250e030d1229120a0b09150601110607 69
    0xa5180c80300d42c1180c9115420a103804041e5440f41281901d903078040c80741e500466004031094001c1e14042c0200c0901903007549038100e0390200400743c40d026000003071180384a2001080450a15507442c49080007a04480d4000d24841c9003c140c4040003d406035500000c0c0a004810040060803140e0080c0040040c44011199920f4000d10301200c5011604060100305451003007040b0415a040307000b0302c02c41d00b142c03c2c210a840d00000110030313010685000d44103075500d00c0103000001c000c1d00456806141840014503000c0d000c20311202b01c2c1c10000d092070407651100440400d050b0f140c05907400840d2004065442c0d801d02406034200380d4880541c182c0c80000c0c15104184030303405844500d121075009000d80b00c00f1080c07540001c1840c03d20210403c1d03110303e440401c9046980d05800c44d1689406000c280300702c0d0500030200840300700707084c01c000301e03d01c035405400c4c00141c0001a001d000d4001040281455203492072400808a00101130504000700e61841540300c0000107045a0000c209013009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 312336465 1250 312335215 312335263
    0x40b040b0c03131d0f01140411131205010605040c08042901120b090f0d0e150705030304150203070e040c0e03030c070e15030a080310030b0f070e0111 66
    0x141c214000d010144524440004000803d200b4070860080020b0044e900b00344195908051402010b00038002c40b800c0c0d005002d403803035041c202a030003603011080c0a4030f0141440800c02d0400701054564201d0007040d844880080200042402078034003070300c02110309007c1d450707662500a020010042000e8401007802d0740100d84c0c0c1d47d15070002000702c2201d081c000030310340e1220403181866842507400c0342c860075100c000403550f03c008a80e9002070082071016102001d420101214075006400000e0303072180c088a10159140100c40040584622801c081c54030703442c2c6800d140390070111507144c02d03540a004004000c00607500038401c140e000012600000c1c20011804101c43c403801c0c105495030148000541107048000c0090b0080c12103450b0010721400703507214900b0100c0c00000c0c4e000700d0780690120300350000003010b0202640c3cec80080c40e850000c184c0d60b26194414000f50903240050580356810070301a00300d52202411280c1242030800003445044140d155580d910b4001003800c080b001c00442d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 312337715 1250 312336465 312336487
    0x306150408010908070506100b19090f03030903150903050306150705011104230d11060c010c0507060b01050313020108070c0b090708150c0f090406080a0b010509010902040b040b 78
    0x584000d0701030340e8000c02400b2040d2600c104e5561207100103907480c3c444d4400040160000104050580f0315802c0044c0c14186000960103180b01841c00c40300070f10001360310100d030031048000c03200001d500039030360102c405c1d20310f007401c960705420460105a064104200d01c3d01180e000301c1100d8004400740c443c04203c60050400210300d01588200401650034540c00c48603141200c8050000c1d15800310320701c55400c0206c2c0d405d03000d08400d2042c080d003100740c12000c00085000e01100c0c00c2001000f9080c10302c0c2a0380522a207003160042d41c8544041000410100103128030352240c420003240a08005143d401c006500000349076200170020304005010f8001641c10344a4054001c2d602d07404108400b4a0425010250b1106610301500e600e500c00c180c02c4201e01c40c40903203400d000c1d602c0600c015103002030311540c661a82c1e00c4030064580050b12003400040c1e03c0420403a0141c45030240300c803450b1950500e020808510010b0b84100d214600602050145802240c1150122040c0103400e0b035403501d04000b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 312338965 1250 312337715 312337717
    0x807030c120e09090c010806060d090f080d060f0503031204031209050709050610050703081b120f010b090307180b10081602071511010f0f0b030c030a08030615 70
    0x40100079006180703500c07074510382003000c81c900c0303030310071640342c0741c950707a03055400d0750f11400d581203640080d0b4000041141030410300000e201500612401140301c405a4841914500200c00116001600041d5804070b10056119580150200d54508001680b41a00080d9280584800726480c40e12420100b8105800f83c1c203280c1404114030003d00400790a818034a48130740c40303072003a080c1d69424980043c4840c580030140b800040f1654640318106282904c3c11601058000c00000054131241e042491103030b95140508505102000046a030b49032044541440d000180e00400e140401401004000c2c0d5011411006440b0450100c5c502500000c612002034684041401d420449504140e40455405411140700c1c2074178200105125081040480c0e0724100d520418a20028816001a90500c12481941c1c503001050001c51185003405240080b120246500c104c03807641c66006c1c410384e040030f01c00e6000260044010b0108001c29441c1c040d42031100402c42c511943d00100d22994400e0020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 312340215 1250 312338965 312338987
    0x9061410020106180c080108120304120c06050c030402030c030601060807050c100f0902011b050607050a0c050d1107060206040809040902181003170712030f0f051512030a080103080703 81
    0xa030854144890f150131000100071400000001658140001c40d050f0b000148100b40e010000744054995a0313241c4810101114a103429804c0004805031403003ca40103000321405a2850709001b5901d0070300f48101841c0031920301c50180280c020100401645820042d010b41c404041c2c281103a440388109691404c12100d00001e41181c0d10303040e1020702d1107000313502012005100b80c90b90f0849405110b81042c0c01403154900500c0303540100d0018140d28807a1002c1e109060090900842410482e0349890801050401300c0d800070301d0703095482c00c12100401400340101018005840d81c1c0c10a0740b02d5500620440d08043c3c0110b89540014007151203040070311803030188007003210030f281c03d004d5403150f4a101588800e031540d4201c005e0b520301104406040f036a25607884a49080d1810400006030003a00c1103c00800c00280c0c5c07501e041d410201e0381c0c002c1a10503031804075a0221003019004010806610300c0710001c0d194400e1000c0b010b01c82d00401c806041d29040f610042c1ca0714030901e01180c00c24112 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 312341465 1250 312340215 312340229
    0x9151305030d0606022b0f03021233030a0611090306010807141806010804060e030f1207030b01020d0c02030111040810060602160302060f1912050109061410020106 72
    0x42c85019442160310440a40300aa03003541d1400015110b04642c400d01403041c0e4031781c400c03488488500e03103000740a008491211420094100080803001c207441d6a0121060201054000b0416501001c64418103180040301d044160382c10f05210082940c0b6902c0c0e5500034601c0c0e58410a0700350a241c07071002d588113908010f0031181190307110940940c44007468400c1c0680d40b6665075001d9030500c1c10642e0002e003040540703000c80e150f68601004507082c40010b0700c2503a240e035071074100d01d0326003400f80001e00802800f803003910350b1051022182081c6040040100e000c0501e40489854541e901141c817104034026450f040013140341c0c038000240103040542c4000b481c43d07400200000d9660700400e2614180034940c1d000c0200075070316102640c660b2030001210312418000c80c410300052030702c0c101401810603642007060804008900e000c10292400d2020740105903080210070800000380074003405007070401003d000d80c0349002c6c8902d075a0f0b000c0c00300c41481a88040703003100855200754020f100030150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 312342715 1250 312341465 312341467
    0x3040206040305120d1503200d060216110402071a07031407030b0f0108040b01060f03020d020426010605030a02040203070302070611130603020f04050f01021005071709060915130503 80
    0xd110700f00c0080d034801707150030401c141000c1c03441100211440e44003040369002100c0202050700300b0300c1d000141641d00882d950048445060360081070345407001c3c001007441e481c0340c2c2602018604156a2211441c0340c42c0e44240e00400070741000070b542150381c554500d00d40d40040130580300d4180640181c44044041c01c1d98403007403820001c0c11640740d004040004000e4176001c01c4002c40d44011201500222400313054800c030f4000410202d4800d29045011010929005050100c00c1c407400c8180c2c2e0081c0d201d08400d00c00d546a000c0600c01081c16000400075a40081110918040c080383d1105000345001c1c2c400d65000c000034280f107020b60101c0c1d42a0380c0c000d104005901419101544a4011100030003106180c41e00200b030540c0680300312861050501034850804d46000104a940008054100d0450140038011905030055000f0103004521a40301c4c004c41c2c800700032592040c098001d0031008280c0c09034042c404c088401140c410f1071015041c40180003540c4c2e400030715000c80c0313221800402500c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 312343965 1250 312342715 312342733
    0x10b061603080621060403090b16020f0a0f0f09060b0a02070e0c09040903030507020d050a08010e06030102070b1524030a0b1f030905060a0b0a17010f050106020f0c0a0605090603040206040305 84
    0x580405c88900c03980c80307a00d0700020181c491444030854051440c00a4081100d041c2407005454107403d8240f44410052000503215244d4445054001440d40710070030141c5055000e200d203c025005800c0500041c4034914140210198001e548240902c41c2d1722490665401003010180e01a00700c865410015005001c260440d190040c0201402c640300070042c012842100c00070ba203d241203918041041e030760484564240422582112005000607a06641c2000881d0002c1c10380148584a0036070311080343d004141c0c0000744280c10101c40c0b81018641c0b0310b0080c02e01700c0b4035008103480d0860810600080d01a2080d40891745013128201e140c1348003100b441607881c0d441d81c95045810b802d4451400c0d81d01544402e048042a02d480c105103e5200121150038000d0b0000c42c108600c41c0b07070081f4004164040b182030ba620845500707800410060b005044202d0b001d6004010044a400c000c1d145103045900d4490010a1400748100c2284a0ba800001040642d582c0f0004c1d02c000c0d50304541a074800784 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 312345215 1250 312343965 312344029
    0x20a03090602040e040c0f05030d1b0204150f050103150b07050c120709060b120f1e040b010608090d021f060911090306070801051507050f0d05030108010b0616030806 73
    0x10008417400c8803800098100401c0444510280204a5001400810080303600300d4095510310341d01078245810401d02075170304015956a0003101d011400080032003840605200031002d031402945c010a040c58205020072441940c850303203000803200000241902c40c040c40c81c001d410509240c0243d503001031810703a0040c90410201d02c8030112084d804041040070f039144c5540c0241e005e00000c0c80b441d07000c02c000003043d2007021108190b00c071201d00c59906c1a0300001c0e502c008408402d4034144c074080c10000c010300c04a5007005215401011700b10040a5200d1640002940d07903619400f0024619101c02d01e41407400400d400c82409008040300500101454000222584c0c21004a19101c0e2194002103260711b402070041da4180d91018215100050790f00e401c480103030f44120401c613124801d0325580030108409000b07101008529039a942d07580d515000e805425210289409481210308201581d451164144100081030b8942040300caa03036500400030f0b20b0310f40c61541c04044200303c0003c2400304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 312346465 1250 312345215 312345239
    0x903030a05040224092404030609140d0801050907111b0103090804081606080408032a0a120b010215160201140106020334060509030d090c031a040b0109020a0309060204 74
    0x112000c4d86c941005400c40040074500044030415110343d010100070900c080341c00764004408903405001031000b01c00307642240b2464010203003032100c0028031600c0148181e107000d41ca5140c120780caa1601c5018038825480554a80c121482c4552000b0741c9401001e030540d0003a0030401a0035003014031340d5115540c0b000e503191070750740c0b454404282c02d8a8802c081101c60003008540e0040345c101c0625410b6a0314451007030011040c9507148180200300c4a1a20421000038008010018032550351903d0314040744a101d0544034804a524190342080c807092411820360407165034070050444042c142201c00f980141d004102403051800d140342c06a001080b1035400000502120600303405290728210542ca0340040c91100d41103060505d81d40b0b20340180440d41540005412114500c1034a01e0290b051192804881c0300c0c403c1117600003030000c42001400003009030505809040e5240170b666161980d25810410b005001d06441c50364049000340c001303840782d4405c0075040e6002100315030702c584514840c040c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 312347715 1250 312346465 312346477
    0xf03071a0108160b03070c020405041208091902041d15100b0a082d0106030b0f030307030e010813080430110f04150b0a170903030a05040224 62
    0x84440400040c03214000602e41c10400c40ca100c03d400510300b0180d00340343c10f9101811150401800b008010702590b241e07c0751900840c418030021510b800c0b61030300a01440401842c580702504002000c2c00c2c000320108040c403200d581207030001049040c040120108000c81c42d1000c4661294002200080346510f51031070003251185c0c1810b050039512501da10f503522400030aa03001a0645010031034118496804811160a110320140c400e0842e14220010070800d80c03080001a850304407055003414014481148144150040d61820748681c03000b8110040010b48941000000d10004801200c1c0020301039420b80c0c030100756a03407140d440c1d41ca83c900c160602c03010000080d0082d503924401c58960328040c402c1d07501c90706c20f2441d000140d04001c00391140c406102d800070b403222905007100708004117a101034500314444585074041c80000a1070344000b8103114910451810134000c040800109036a405900800041941e035118800310310441c8046000c68a220341046890031044d07191805400e07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 312348965 1250 312347715 312347753
    0xc0409020d060f0b01120c0c021c12030507090501050408030711060c03070503030412021f021e04090f05091603060c050f0d0606030c050a0923180601080a0209031e0f0307 75
    0x50509882e040600459403404850804030b00c20800b04001030420311690114040f94ac159102102d0040c7c03920030145040d07a01120000350741c1c100300105290000c482d0360143c642842c1c402c1c149820102c045641e88602400a0429910800c40c4c0400b0740e195821501c460a400e0b0a4a4681520707181455490704166000c50b0b0070341321440c031005150301c006000035420350b0040d003030040a5a1140c04e00000e40c0700300f104412001102c0300401d40d5010080c01400101100366000800d41490407140307040341d001400d02041c0750000d95410502810060621003640e0304101c002441e04c00c410b100380c400e80b03c2d101101844600c00304034000000850ba00c80001c54149450a014071918544100c0b07442c820340819801245d107400042c402c6c1030b0300103001010b04003028810182c607402c681c000307000d13400407000038500451a042000a5941e00c118104d03004480d0620035400c00050000090711601001a22214121081c4c8420105641000240c821024040a495030391a083c10300040310801004690 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 312350215 1250 312348965 312348977
    0x30d180510050618040b060d060204090c020c04050114101202070609080c010c050c33041b080102030106140a170a32070c030903020a06050d1d0c0409020d060f0b01 72
    0x844200206148240b080b50700841c1141690740e048102301505a01803010345600741d003400081811601481002a0000700f90000c0c8020808a001c000544074160004c01c1d9603200000c5004540e116100006492015824902c2c0b503120800c1c1500001d015240010348400d04000d524410f00910170001d10f640600000288a400003440040d00c15101c1c441c9084440e034400d040380d50303140c02030181e240c040c600030b480003003c0f0340d40078003800c1300d43c0c0303002d41e0f01350b47d840380c0c020900c042e101c401c511101c01000030070025815585820005064180041d000d100103c000003501c2010710300c140011415181300d02541e02031410500300810051480b00e42040320400d644d102054050b90714040e4115600c1c10344e0401c07071981d581e510101c901c2488581c08409000310302d1400300059407021000d80c042c056542d1000d44030a115881441a9208004281312034941d0b040302d408510004141090801416200070400140b10700c00b1850f01c415060010304a113141003000350754080c0c1340c2c100799030320402641e883d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 312351465 1250 312350215 312350239
    0x115030f0e030d020702060f040e0f15090705071a04050f1002030609010302060a02120705061b0703021b030309220506010503090d0806060d0507020703030807050705030d1805100506 80
    0x10030403078061071100ca003558000d000003a24410369800400382c03035201130300fa1801c01c164030203041201d03000394200107000b00401e400c000c2200d4041c41e90704d5010603070000c01003440102c40046404903401501c048108080023907079800307001510b800c20111b80c0000090b69118500341c01c1240c0c40701590082e06203607001b401d11410700a21113000346ca004600040607100070f64079503420040300364007074000403056015019441004003250070103001510b0007000902a05e142c01000f0001c007100c48004a03042d120180084008294000b4280036142d9001c03000c066501000b400091840c01521003e5038400c0d6204100c921814905000503031024102400340103507143d20700150340600003241c120f0200e40c07242a000348450300c01c0c0e12580d003240300641810701d070460584041c01642c00803150307400980d01a6908100700356100142e1540030505141090030300900740e48540d100d208190f41d4844403901c034520b44002c007442084103907800d5132202c00c4035900c13190040e08501500b0201e030940d101e44819060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 312352715 1250 312351465 312351491
    0x20604060f0b01021209030a080f030a060b270118091d070501020d03090f0b0a05090d03150608060f030303070215100f030f0311031318021905160b011503 68
    0x2c0c055145205070054400202d0001082109400000311554544103040250780880c0c0284018007020011207003079039607071030100106015140ca5a001c800402d004005641488a00c0101000750800e08080040482c1c0440012180360580c18088940c041c00840001f601048030b500851860780c80340c002824000740d8100580e00c0e03c04501c00c141c00358101b41c5201d211144690f01c007000d1503202c0c0d040725564800039200c0c446850000c85640d00510358400a104001804119240170740005180a1200600c80751840394000094814a014400c02c84041800360f50354a0340d401368228090304580c7c907484c240c1b8001f03686083d18803042021441e20700c0071a581d0076503080c5000964000c0c10851040c245944c1e55079402c61000c031000e80070003018160104001105000030410010903c10040641d410030507801c14014500c40c0102c0680c0c0304000300c155400e5807864250440c0d80c079040140d01d0701c20000640b041d125808400030180e00c0da507400071603031a01e45444c0c5030450325a903504224040c1101d403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 312353965 1250 312352715 312352721
    0x50309011514010305010f050f01050a0203040e04030306030312061a090a0305190b1008030703050309010213030b190203010e01050d150c1e0216090b0a030803040b0a14010f09020d0b0d03020604060f 87
    0x2015000040527002121a501460007081821100e04c1281c1c41d142c0c0c1c035145000f00c0c607000d0381d04074002910340000f0028103a101c68078020010048208002e000c1c0303000000f130524149101064403508010070a004665070740c40034800116003140c142c903480c0c0040c03540c802107110400c0d01190451a5100802c9030007540505920540b00b11a00844c90b10030ba44d1015140d40c0c0006000d90070664082240c0c1882000f5010002c0080d07204040500190030100c125002050203220b4140d8404e10600c010014018001d80c1c10341103490079941910202140d042581c04480b8140c0045046800d10309a00a8203900006000c4404101e604046241d2001c1030101d860711107016000c00703a074251500c2882805210f034084d4006640c014a9800760994951325604ac9400455080c0c4000140300e08010002042d4001c04d201c41c2d20000180040e9070400480c485080301500408900ca540407440d078656041981c4152141c00000f09415119882890000d65a88046508407601030400c003081d0341e0112540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 312355215 1250 312353965 312353969
    0x319060e0307080a030b270a0e01090309030b0601020c09010b0a0e01050c0d0e1f0306092003010e0411041107060e19080705070f08030301080c1c0201050309011514010305010f 77
    0x14413490300e00480d4048002d0403226881c0c9500004818a41500200700c0c0c502401d0101c140c0c581c48506e2500800d28422500b407413085042a034105070423800000e9001c111740060300e0340821048000d48880004070b242514101c1016008000c0d00000b0078150300360809440e0b11001652000075581c0c2c694011140c03402088500011688081d0360b003400940104a803080703141000d0041c40b0b201781820034040c03c1141034200040403d950350428011b5082d43e004080c1800344602c160521442e403041984c1e1944014461045100a054007140822640c0304600001c0e000c003c0060203010703c4401d4600c1c441d401144111495803614040695600010801d02000917000360340d445404000e440d00c42c943c1d800b42ca02103e8500421901003154906820800040c01407440219140d41c1044203403482c0c42020300714a03100c4c090000c01414201d2180f0011124194280f8085880340c0754055000d014041e01010b10810003892140466011102108284080e5003681e007406070740d036a17080c0303081c152ba07a074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 312356465 1250 312355215 312355223
    0x1502040e0709211a090c0301020a09050405090303040b07081506280e090109020c0307080301090501082a010c03050d090803150411041202060408061e09010c09180b0319060e0307 78
    0x140f60030007402d5590320913036100d48800e055403c42c01b41c6100103822680809403400200700c41c000180124202032140ea6400400c020041d851410306480701031600c00000c0104d01000041c0001907440015010025412000030308100e4442d03101d01580418100c00c61401040882e1800e1240c0c1d40b9441445410080c000151a06240741d00300b01180c0082d502258a0058900c0100b020000040c2d82400640c024846a4400142c5504143e0914280740d540d6031080c2100510326252541038100c000481c2141009003480f412250852034250345a01170f404814619500c0c180300c240074842810300440c4200070303400c91140c808000320100f000310780c510052900020f0081c8010b01c0315070b1600d00c0f029210341c0001e001e641030682d1002414036060307048a403610081c40c01101841c24940c118005038102c10604001d001d82c0f201748500902022841c81030b40b629150700d8065000140341d40e8401944200040c05846040e0505001c8145480ca900000c030785030307442d110461000e0381000c0150703610f072580 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 312357715 1250 312356465 312356483
    0x10c080a02160308060604051914100203090108190203090606030c040905070b07020d12030e16030f0f1401111909061403091005070c02030601061404031502040e070921 74
    0x15440c1200c0881004203070030703044030080001007071650b241202c84027402201c0c8241c1054605001c0901d0503c000f0138442c038000e001107800c04c4c418130780102c142c0d03d1500c03003032034842466038618103000110400c07039040000d101d100101b400b08190010131024420601601242c0c1750040680030700081303400340c400140132504000c20a200042460006200d020b000130038110418255031101e07554403400f070002a002c070340c0d03e0705c5e6081c03403400500c0800040801c2207100b400701d03859a2030b0b00001106581000f0014500b004d500c40822000b11881c0c07030b0700d02000c00200654181d1428208155104400503000c2d20104009100039a204600440680b900e99440610342403a98000700481e4001401c801a28001e41c0383d8005501081c1c0300305031086007240d445800043c80d40c0103043c140201a08490104801307081c40400c02407051045504699020040d001c2040c840030305070000307008941022036040103132418000c405034403602da1400c0d1003c0c1100002041c080280800d0b070003d01c10cc00030011a5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 312358965 1250 312357715 312357757
    0x2040b152d0a120605030d09030c05060306091513060f0e0105030601061b03021c0c020f03070e06060a050903060405071703031b0d090215040f2306070302160305010c080a02 76
    0x84209000c183c1189045000b04a90f40c07540c001a0402901c0d09501000490713100f010418072104c03080400062500392151865400c0c1036012a09240b0002c100c4c1c4900001490f071958551101e80107244641d5071803034100310080c0c0b1042d42007046202c0b0b00c1a0310481c0c4a00001040320300e0041002c034126413594803510441210f101400c0e012045401c1c1c2902503000c2d0790104c0d070a1402842103005640840e5807000c1d003a02e5140304002a18100d0701e5034074041e6201490a0103071266200a654000c002100e4403a10307445000c2049445110307581c841900340c000c00c0103000400c8000200300c03040e0b400703004d8009446c1e0010b4185039680d02084809013405a0441c00712045440d0f410014074038207030400d0010909002507000308488400e90400b49551800000d010421100d09041e440302074018001b20450700d902c1180000700b484c000b001c40c80c1c811803002074850304050080021401d0341d0b2024200c103031000c0e904d081241c0202130034141c078270201e80a00005078040070144201e80040d00c908200d208008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 312360215 1250 312358965 312358967
    0x102120105040c0513031101090b0702030709051801090c21120f051209070f0503030c28020901090c031a01050a080723070c0501031e0902040b152d0a 66
    0x202403a05010f0500c001004940000c6054954840146005484030b030122000715000414801c49948045075544080c844440180d50105084c0c0c2116140c450200d5644c50b006049000d2080704140c6455035072030304024208119810002801b11034649606807036109240d0449a090421907500800d80750103205902d00070390168030b50202008280c41c00318148828043d6880311010107981031041a4400441003100c00d80f20103850020380026000746041c110189a034960315480c41070303d1607114440451401030200301400c60b10083d40c00a0400c119035a45141e420000c0202601d00c000190a100c0e0100045445000d40d10b00d041c1c060b03450a2601c07040f41000c41d02210040c1c0200100070004001340c00c0c04410104040800c20079405c1c40e507640403245450040d010f4198805418141480c2d1500c0c0c40307501e40304c08001e0504065602040401031480050020118005403640c0041c500c140510300d01041c2e005029030510480c1c108009102c20202c0360703489880c0c21030300340a0000800c42001c0c81 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 312361465 1250 312360215 312360221
    0xd0801180c0c0f05060402120718050a0b04020a0f03060f03020906090a06080d0e1306080703031d0d060209030606040b060a1101060305030c0f060c03041e03021e0d020c0102010212010504 82
    0x2030000d61400102c02c001940e96291200101e071000d6500d580b04800340025480e241000c201c031081e103e002003080d5407400400000000001121400c002e030383d08000386401e800d540240001c7c0302c00600c115900e0f0102c42000d09002c07844182e50001030300d4401c010800444101000081c1c3e0f40041007103820350344070801c20908590083c443d100950302e400c000038500504201041c88050252601c81510460b84107100512014840f04540035041072000c01103000b0104002081d60b07014917106c0e0b40c1032600e0b44027099030b043c06215aa005a0080002010312109a010b003003400c604500f564142e841d60710400c42661050254607030301c10010807501e0029405404628403600d4441c1c000300c0c3d0180e43c0c3d1105405c40d0080390307090307034590001b03103010901006c02c0c4a00c607172080c5030446280c11070416444042c0880c1c501d90710301100c200d01d00030b05000c1c14000c00c003410282c4e02c0c0010003501180c01c200199140c0b2448000c010241c40b80b5001400e080d070040c0251500250260004101a0f18100400c805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 312362715 1250 312361465 312361481
    0x304050f0414070f12050f040f03140a09090b04050603060c1b03040b0c07050307120b07051210050f0a050f040908120f01050a05060f031f1502010e0d080118 69
    0x71050742c030702040080c85498141d05104807460f4950718021946004045c009070b0455655915640c42e05007000b0b40c4da110003402d10340081d00702c100070503000043d284c280d5040b038900c1841101001d0128416030344503031007103501d000c2d101808010701c00840034805100a9580594105074903030810400941d1400c2d070038014204c0400301d5079026000110407000d0714150b6121340c0003055861400900030396508030401c08040107140903401405c1e000e04d01010400e9102004400606026801010480341c03441001640c90381499249200c0d031500b890110484400709500c04c40303026080d21008600140b824000406c11204040c2010070102d00c202d0402005100c0400100d415440520094115200c081c2001c0d1140c10503102c0c080855052400300701c0580f015034801c520544080000c400388441d0b9505603a0006d2a00e5100801c03104a11031914480880340c2000c0760814101e56007550495054000f40d1200da80c40301520a180c122072001c580700402401910300b00e914191031310301c03010025402080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 312363965 1250 312362715 312362719
    0x60305012412020c0a14030c0714061b030703020f030310121a100f090204120f0204060b1c06050a051005071121010b0103140601031a040504060e1209030304050f 71
    0x1c06001e0503807080b0300301d8101c41c2120180c1d40c441030301c0700104442080d80c44840d1007900d00944c02c2c5099a404290303600454012602c5100000140e8001c0d84c0700d20081e192044006803100c002c0c4030941c0071003550b039002208168010b1155070300d0480c4d91240401124090601c031280200541e04150b05c42a20032110441192095041040c1510204180303220a00a00384200c1451a4510b0a41202064589070708150b03403481c03041000300b0171400b15402c0110f24030f41c0802c0c1c04280846500024000308031a5100802e80580000e101024000c80c22140e17406410a40b01040195110300c14800000d1780c50240a802411910000c0816402078001c0c00c0e5070b0748500341c4468440c005102241078519070034503200044a02e0b07940c3d050749413021f01420302c85410a20b0308024101b0500b80c0458041c0300035040c0d5041c503a5800a185e2004d03d0304c103507015408005031042c051818149800030003031000b803420003000c1c01500e800d81d40200b4120100c40b0301c000010700440c2020300b03083c01c1100c8007400403007240d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 312365215 1250 312363965 312363977
    0x1005130b0c0a12170f0c09102f06040201180b0712030b010507030e04051003050f032a0304030605060604031a060910031e080906030a0b01090603050124 67
    0x104401144018006210300402604030244146880303141d4044000103c400d010500d585030515200c100c0c0001e6000c042d8a850912035110311032841c0280c804d46811075002000341a407159080e4200300c28602581800c60300340c501e1050402c401c404e0304115030105076203405c05004240958800c4a240310301d10091188200155650b006a000c2a408488212202204800041c5a0340d416100301c00000100307013000c0b1b10f0031f052550010b0001c455040e0852043c1d1b9904080b0744414031025106c0080d40e4084221030408890070a0726540e0380202e4032420216842480c5203018240e103503a4061032424490080d0704103415a9541809004020800b542090040c040000441d40d40d459481d403041900c0c0e425585403c100e001c1c0070b48908001d0142c55400c64900c01000000c6004403282d002d003802e02042d500c9031a8515000d40076200700003101d40e01803400300a10402421591198503101e4003601d40007103007540c03064142c060f603030f0034401c0704200380d03001108449507403240700c5005800e03507585450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 312366465 1250 312365215 312365219
    0x7170915161b0c050a0609210c1a07050601090615050a020c060a030e010501080d0f050c03070b0f011401021c0e01021507050c0f0705030703021e0306010905090c09010302100513 78
    0x40ca000803080002950b8030341540404021178103210f4030aa001d4180fa1800505c10b5050042d081c10804015100c0d80d0918540e070184424003400d0210f02d40030b0050100445421100c0564000e207541140a0541d4540510000003c8890235031140408440303d11817001d00001e401541070b203454110501417400c0d4003d411000e000f55868000909021aa0382c40005400c1d034010841c5007140d105070407218941e0310044406c6000d64000b041c10209405034540181d075400c01200e100e095016241008041c41400e03401e00c070352090003400e00350503185400e1000c181d10900d1801241d9861401001913502d070103018122032040d101d51305081407144103004a50301c40c10301d404000c9000e01d04403550400180c6c0032507007a680481c14061040c4d11300135640248a502d0400d0300103521040f4912000348106849420350024907400d80610010200c01001c1d02d18541e51492031601030302c000c8540300d82600440d1001152440e0903190181600d80181440c0035042e4216070a90391540403613641103e00b5a08e50340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 312367715 1250 312366465 312366497
    0x120106090507170f0903030c0a03060b0703050a020f010603080d0f090506151e03030f032a030708010e0f0c0d02120405010b09010503070e0703020f04050301050717091516 75
    0x40c18050a140e5582892042c01c0c0c403101500883c0280c0a220701c2800501401601c1e440041581d070455589440d65603690300c1500184c000340341a82c00b1070101200404d00d18203064009018122500403a02503c0780395a0818409089813480d000c020300380362003405248561056075004030002e00d000fa40001d000d1186495492401744202c40b444000d40380f103540701105003089da4405400f20203090f810000c2d0421040040c1d2240030300205444020030220000320350062000d00d000c44550b282e01d01c031342520080303a01940158801c4500c100803c5280000240300000c9082c9540700b40c14500b402c00c51900c8140c1d03080c840e41d000d02c004810b1950240100304110b52151500d6001e41d02c500300000304058000c1c144420395074141d124520030f070450f074810000e072810a19141d600c0302d01d910300103a0716032a0784a001c8d0300e4007854204c160198a4841001140c1e0b07005054050a143e24078041c00d880c2d0755240200f41d03204490f40c03000b40030551020101e03600751403441c108600d40056041c01500b905680c1c407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 312368965 1250 312367715 312367721
    0x110d0f030915021606200702130b06220b0301031112030409140f0a05040503040905130c1e05040c020a02010302160501090c0e0f070801150c060f0207060609050105030a0212010609 79
    0x20181314400c4c481382c820000c21545218100004411101c0c06070000a002d040550900030410081e005502c85689071595040c3c56000c41e50f491801402c0903211611000c00b410403000f120900803000071540008124407510f001628102c90707001c0e040c3e040b030a00403000e201c0d0600b01507624040500c0107000119102e403441c0221703020000c84025411031850901d100342c42c0e44901800c10080540740c00b041c08045000441102c080d6a0704000115642c4c6401d8000c0000b066020805029143c079001c0109880718004000908001c60709200010380d512041008100d030101140000541c0c01803803810010750080c0c02900c3e003c0105a1403001c0300d00b168503590300f9039616230b10840782e000700028180b141d0f510300030341c040d0011001b54021141d0301d48203801901540e4180120384180c0c59100300541014420314000c8001c0741e01260511480c000880d046001c0d4000d4002258410b05000d004a0070340034600c81c140c101c81005008003003100c40d03030b000d0009100c04030706021110b540303525000c80c881107180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 312370215 1250 312368965 312368977
    0x2120a0302071e0803160e03031303030305100b0315210309011205010b030c0d15080718022802030409090312050906040c05130b0306040b0403110d0f03091502 70
    0x103140036035101c0e0540b800022800c40e00c1051003405240c81c2034240410002e0081d02e5002c1850341145004660001055811200c4400c1c49a4180f1000551a060b070a048250318103c83c4652020b11094a540c013003d002440503015a46031000240005001241d000000041c043c41c06040402e03032244400703600f1528000711b0741c200e010f90f000045009940d644404c00f40c035013000e01c2c41c04000341e504014040302d2a10002e480c0319100040440c144140b020964800010324645034800c1000356030310a0700a07110840d51045241040a60b00d41c80d1003981d15008071071400070181071803400010308400d4418a0624a234158003188410b1001050008851084488407402500c6000402640440500c25110000c103080c405800160034000040c510702079032001d490040700d138500444003448407680107013000c1002030ba26201381d80900c01442110a0a280298080c0e9076040240100d411800e5480907000414070010310b0205459464a111b644a03402e0035102d60304211100da01001001c080c0e030414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 312371465 1250 312370215 312370217
    0x30b0a030b0109020c060714040603050a060902070c05030d03020a020319230c010501050103020a1b11030d051c060608010b220b0918090d110f010603050a0b01051c0602070302120a 79
    0x40c0717401c0b00070003041501d500001d140f5111002c4400058051403074003e52041d01c0c113168864010400390700c0310342c2201015040c545003c40d110103c900340003031446058482e05010340100d8080c41f140500c01e0084990200d0f00350021890010300b0403001100500e130740700c3c0c5010800f842d100d00003451050425030038140b8100d5503454a03000300e4841e540c2100d006031f1009040c14030400003001b005400008403103020507a0940f0a200701e490341031411901c900003050590600421200502c4140c1007000317800342e405280070f0400c0118282c035011045030120301078000414078145c010070080d0200e030002c05c24100c20202c04526112150740c4000980079540062009000204100119003080c10200b20120016041e040c40d03030070005003480e240d446242d044420055503400c02c00091b50204802410400018001c0007143d81d0307800d00c03944510340d42c001200c00c3d02c000d070300001e428070b44000c22222444003131a081f0041049070344d90038020f5024910441c103500400404c1d14400ca4442c0103841d0110319 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 312372715 1250 312371465 312371467
    0x506032e03050c0108040b07050901030f11040f05060909010b070624150f080109090f02300601060203030106050309100e0f0106083d0609060e010e070c0201030b0a030b010902 77
    0x110b2511605085142003181c0c1040840300801000c10010038449400c4820380c10201d60340e00f421380048000c0e0080084040e1210700b015401915251401e00803c125040040000790070354070703001006050b100303464100f1703070060605c0c0c014403020801034024500240b01d55000241c002c00101041b015042c0a510040c1d950b08020080041041c07400950406090306d15101850040049000d0702015041c010214120368840c04402007259417a00c0b0550a5002003480300d12440101c1c03c2d070320070150f00c1d5401c1803000c40c00344c0e4524007c2002844d00d05842454019605580c207001d400c07a020b8000a00b001450b11074841c417640d041c1c0c458032801d9202040c42c005000090201584682034903010350017040c9a40c080b14480d50050000d001100c00c41000c49400e0141800d85103082d812181c00500c0c050200b0314011002844080360350250089440d56540098541e80e00e1600781d104000880c0e20202046441c3c8484005600c00d900c5030819000042c00c02d03412a440382c8a0308e4440d4000d8100808090b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 312373965 1250 312372715 312372719
    0x5030712060b09010e010e130b0102120408060a0605031902150f031e06030a050c0603060105040305060106120c110618010213030b0a0e0c0105161106180a09050c040506032e 76
    0x41c3c41601c00c0301d00542030a14041d40710b00341001c135081126208c075100c2c8a075510340d0710402e140e1007400301025104604409680360394039030403001d8460205960280e03000341783c81400981420085128001c7d080e8071304890441d07800c55024011100003450407050305604c2084220300d52000c140c091405492a14440c0500d500d4482d843d400c51140a07121a02c00d41c40340f4203180004100207410031306100c06075007450301da0301d9030b000580781400b40b41c0000f00700e070090100204129520550f81d41440705003d809010b00301324044160303052984040703014296001400082d1110700030b8039400300c03030780246000103151801c00d00701456480707841c5c2c01c22503140c0b001c182408003001041c01a40000741004025003104c1c290301002804510038840e0200d640243c5011070014042d9030801120100006400130355918154081c00b44242c0b24040c01c1351184001f4440820540d119216a9110b40240c0c040c452401d17080108205503600001c0c0303042000b0f10000315117000820071014030711030b2511141003809481c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 312375215 1250 312373965 312373967
    0xa020f120907051509040b04020d050f090c01030911060313060204141203043b01060e03010e0c090a0906020c010906091e0201120504051903080a0f0504020f0105030712060b0901 78
    0x261640014842c24030b04c4041d8510003400f0049507500c1d0f004550004461941300003140c0a03008040f00f4190304c914040400101056626500348140d083c00c0503640042c0542c8010340444140d9034014058189607004070340582002801190072800d40013084e01e010505a0f104420b91740650000c940d0b0006940860119040c840b420a240030705c100050340c105400d04040000303920002038a040c0103000140600c48070042981101100484c18031089099030b102c20000d05810b040740c007014000e40c6061451441c001020403a207000800003001000e080e200c4003103800250540030010b4582c0c1d58200002c1452810911030640c8940c82002d000c111032049081098000d150040b40f2000101440c04030300041c0e0b80500d241100c8407510900080a8407241409850050100d0307040040311a030603400c0c428940c2040d21580301e01400034041c0324101c402d030a44415542c0580d00203411080282c40210b1640c000d1000e990300c68514984044181006240d0b213003038880e540c0c03146103400e0380001c40c00c0c115 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 312376465 1250 312375215 312375223
    0x1e1306120c05071502071401020a0e1e03070611011e0c091d010608040c21050601080a0803060607032307021806280b0f0d050106020705060d050a020f1209 68
    0x40c100c203080c80e5040009648900384142c010116074501380f94005114410842c00c450780a02015000b4003c544980d103207000074200c501203151140c8a510030441d4000000c03d09050046403001c054090400715180c03c400390750016120403000459521032005050400c0d0312554182140c0c0440380c082070f60303412454003030040c1e200c3ea00300b4407820100b13540680f8882030f13204504d811100946060409a522420078011040c00358204541141400003074020300444064821455409982555200c0e66540500d541c1d4000001006111060500004100e13180100141048a000c0e040100010070350181d81e4111190021100054400c041130031405c1d4100150580103041407902d103d60706080050004212a0094000e10124003030b1940100841000000c5c001c0205001100d00780c0b40e406016a00780d041c6c0018145110711854180001421440001d1100864001500c95840d0020386403001d030150400805d204100740c2c01f04001500e5420b880006e0010a401c69814200b50400c4c070301c42cac1c3c14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 312377715 1250 312376465 312376481
    0x3050c1b062a1c0f0906051005041802040f02070b10230607020d170f040e09120304030c030c0f030504170f1c0306050d11010f0c03051e130612 63
    0x3100d1044031a0b066088000e000329810005030002030b604002c00101d00c0005031070000300d507421075800e208078102040b140b6001a40034000000c4449552611a010321089030b04d81c0741f18084203d01408254090b003000d601600f5400c20aa070090310300041e07a00c96820000303080d10501c0030000402d001300300c0f8007100200b0040014043e89400da02101d0702c00041c2542c010700c075012344291440e030205000c002d6001c0c10208006183c0001d5034946040d0b0b60310506a0700584038000102078014005100c8a2012611090403601c10303824504540b143d440803106681d028000300d003030001642d02c50011606002c20411502d1107a90340541e03440c00d040001c180810300d0f0348020f001743d04c10b068000500001240c40e00c43e19000c40b101c0000e0050f02c19088024003002d034403642d0440140c0d0100024815801c80f03054412000f80c031480b0b81411b0303c280855402000c0d007006030000d801405000100e01030001d4401030780030b082c101c050a081641448010744003141e400600425011f5003464031900090040d816 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 312378965 1250 312377715 312377761
    0x31e07170316021c0e040f0f0c02150f0703110706240e04020102060f15040519110a0801180e0d0206040c0b040b04030602130b04090b010210050103020f0103050c1b06 73
    0x109034148011022451440d00204c082804400e404260141d210f0368040c444c0c92403629404c1c08000c090000840c01400c00c0e1410704018060074440d412860a000c0c1d00c5401824904061000c40d46e40c0e01c02140105141c0300b00920001c4100314400200e41a4000c00a03e5911549182800da98548401c1e10310b00e0300ba4071001c4400c80000421000d0303a00418295801000300c2845c20329036440d50340707190007003000810359507010b842c103400d00c180d241c605410400c03d0840e00b401046400240c01d0781e4021800342e42981e40c0003130354440050110302c1d01c68880e0702180c105d2503400700d041503140c0301080c00d01012080090040e4040c0c402c1005224007130040b03000801807204641e2a00e414184c04804511887c003003e44055000108400d82d4001c40d014080101004c00120381c50700d448064640c05404818040e0f0b00500c5045038a40704440144155070480c1e034014910340300c00404500540142074001c01c4914001024040c0c1030326480c2421a04031130052080190040b032074040300070380d6002d144006102c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 312380215 1250 312378965 312378973
    0x60b01171303030903020c0a03080408060702030405280b04061716020a060902030f030f0a020c0f0d020f0103060f120501051305032a0a060219030b03031e0717031602 73
    0x407039a1914969034809460705450042181d50090134280e04d040194124940c110740e440d507001082c403003d000608103540884054494540310760400300c0c1c0d280224020213a01c004d14103040c0086602c01d00304250118a210741500c038040e0b5a5222000341d40080d44410701081d080f58441101c413544090b810382c408520a01154003445990000355941d040b480001d00d5641d480020405540d0f00b0400c480c0580028000c5036070711140c9000c201e920340c01c04400f0102500c40d0043d140403c1c038110000300c005000103800704418002c02c0d020800c54282900b14141419030ba00000301c0c04000624182c0c001c1c1448103c1c3c10b40301203080c5402400c48000400a00228560703604030380001e0b00100854625000070340c02802c0d010200c641481c082d0307040c502d441c28a0300c42c0d100810200b0000340c01038400c00004240340d03c2e0041c40d890056040d140c0c1c101486616400412401c1500005504440740680380c070003c181c1054580c1d940c2d46000030f507100551610000220030800034150060401c07520742410302c003074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 312381465 1250 312380215 312380221
    0x306010b0405041109040903210506030d05030a0e01060f1e050d140304180501030606081507031a0d0501050906071809020d020c01180b070f17180307060b0117 70
    0x100000d40214000c80b031286445418040300d400c2d030f58013a203211060003042000300e6000da29000d44805400c89900e09003049542c1c451001c451213214031807058401034003604405144c00c404491683c002442210016070300c41c8203620b01d000912600c00502a80b01802c00001d0070480303030310b400407500044502d040701155010b0000d52142c2420184455000103c038040080c038130001c1d4203600a07a00314000e4071100200c610759401e15504080c4c101ca004002c204000c0e601d407080c280c0c07100d91841e40c040400c40100d01280c0440d11135401a40c5c08107518514014480e01800001c0032080c08030400d4820360346640521105000c14498280c00440c80d091200064206001080d9078401500c03441c421243e022852204918031601111456511803008000c850244500b0700e040604ca000d081d922003076024005003005024900c000c0310744001e0303191040100c440138a0709425000041035008055100d104003a840c2000300003030f0806070700c142e0020507100c0f6440001495410f010000300c150104150074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 312382715 1250 312381465 312381479
    0xc0f1a0720120c0a0803100e0c040b0306091f08011d0a0f0303020a03140a020c01050c09061204020a03050d111b0f010f0c0c0803090f060301064a0f030601 68
    0x6200b50700c0008800c02d80c80d1841c1100450810f150913401a00f00000007007000401a8225401d42c01c0c0c550741c41030b500d115229003840400a00441c06501c01d201002c20101d0f01c03e18001e0704090f480341101c81c0a241d11380ba1481407891305002e83c5d01640d52a03444544d035a50721131088801c071454a050000402d0600702039102c4030b20820307030181d02800781540001c0564400e4400c0d0424898200791800c50406824800d0b210b074000d40c8208080c1805502e010041042580c61000f164940540200940c1c10811603078540d1450030760103881285e120280e507100100081080c007041368545503540740c8000c1058445007070390400c04110070815140490000040700d0396034624200d2200c807000e02e00441e10410002c41990441e0f00007401030b0190590140009811400000074042c1b900b0a40300007072800480024094203000a000f4800071840050352600300000c80c05800d1103204150b65100d11100c1100300703440794014184125074008000d2452a401070030080c40120144805500030b01456243c050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 312383965 1250 312382715 312382723
    0x4091a1807050a0504050603130201020f0604080414030c09070509330307111002090a1e0501050903031b010c14131e08010f0b09010b070305030103030c0f1a0720 71
    0x3140d0750501101007100302125100320700340d4001e004094101560790801d0b1540300105007c00c08124010310914082d99881031000c86c04500440c0e02280d210704042c20070040036417034240300c98020b0700f500c5000b95895040d520400c4141c043e04498940950300c010030411f110320520034418941710764980d841781c100c0406886000d200034074141440e00d612510f60303603c102d0380403800400c1250076124072280c0d001c0c04000da90007081004021101070141c1642d4103540900c15141d4004104200315840080203d940568024194a04018140d0745000d02c2007007414102e0380419101c0220341c2d92401d500140940000001d03820b40c8941c0700a60901c10500d44200c810117282c041d5a40150541012030960f100400c00030b0302030305205000f403000194040e45031000f0b00005681610070601e08000140340e200c4101110f100d01c2d00740da0350394556801c645065820910b9400d085840f20a40c00320303403020481c000041a48102806241c2c1e0942c00d003400300606007041c039181680c20164202d44d684040c44001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 312385215 1250 312383965 312383971
    0x50703020309090a18060c1107060e040509030931050c0d0c11030711040507170a09150e06090c011107030f060912020304090c020c09060913050304091a18 68
    0x2906200141d41303210030000074041d2208418469403e035541642004442e41100000c0b00c2e1507503d100322040c200095954441d2144503441c085480c940d003a030000c0c207003500150303031000c440300440f49000e9419000c40c052011b815000d20715001880d0120440c50940344000c2e080360494401885541421003802c0c1c018416a19040641580d0342c10100104c0d000d900c42000f1852200252501d0315120700300b0200d0182e00c428203920030740c54000040c071140d00880458802c03840044425045a403902400d6000b40403605007551007443d00c0c04040030140d003500494142c80c1122029007030750f040401002e8034181501c0720340c40c1070000003c1076030586040090510b048a41140c80c4c5640715006052880c0280060351018000705440c04c0e400b50fa181d0000001d03c00c07a00c03032000800446140d90710498940601850305a444ad11801c041150351800620311a08800886440c10b55403e0a5403101c0c03450f80241e000981c440e45800c0c0808450000d510b0302c10f007200c070650394200560384849100100e84802 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 312386465 1250 312385215 312385219
    0x30605060f160f1403220e010e130c030c0e1e0604180b010905010501020609240a020d050106021b0a030f140f070e010906080c0d020609010c0f11090601050703020309 73
    0x101c0c2c0302009001d0070104803c0b2464100c60301034003040c007040d80103450341e0040c3c00c03e02082d140004400002689814048115400c24800b48441d07402c04100c0c0c002c1d00e6000d07180d104481e601d0101480030070840341e203650085102c0c064000c28207141074616503001c40c00510325070404c40d101380807101c107072210a4181c1c1d110404a0340081d840010340c081404288000c4006040c0d03020300030021a00a00c16405030303050b510240c007100c51a64983c079449540d002084012103410ba0f03080c0c04107840310907036002d00d60405010394003d41024503428607101290401d91296005030300c0141c480600500c40e03d114941d2000c2034481000d501c0c00c54480040b40a655000200401007503183c5200440c0c0030b0026404054032181941d400e0b0341d48081c0c1102c803250030b00692035400d29101d0000361002c00000c14451481000d003114400c0d091540820400760015801641400f070b807030407240001000180c50714005442120710000204d4400d00740202c0075401041d180c148101040746101094000058403600481 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 312387715 1250 312386465 312386497
    0x40321050103030908160b130b03040507050916020a0b06011e0f031b090509040201091d040302010507050a0e090c040f09051b0301180f11070605091b0f0409050313030f03030605060f 80
    0x80c0d480300c0da0b01d001c41279000f00c4110402005000030040c021400308110b0b03804540e0114a500c51b03a500c000300307845800980740564011807955000500c07900310340e40e22208c141442450b1032500c0002242c41e10081c007038000012110800c40d61020780520520307644189280c041c04003400810b4026142c031106006140c461080034000a0031a0311074114040a0046a503041809901844601c1740c0107805440c01c038095400d060019038804d22804c10b48030519401c0c3c1c2c0b00744961541800307000e0241d4000e8410010508104070204200188000f404000c0400310000556841d0021050480041d802c84441c902c101c1000104040a1910100c40c0560b5183c00c001503403001400010004103000c841c0d070400040049030702818040f00d43c0c0018443c80c1c000341502d10403550600180301c14200895425448884101c01c170a00d41000d034060007000e445441100d00c3d203d107080c3d10303000954071984100c90100211030384004040c5d00d4000c8000400341602c3d11030800103206911070860188184445007000b07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 312388965 1250 312387715 312387727
    0x5070f0c0318080f100b0f0d020607060b030f0f120309060705030c04030516030614091009030c2109090c0801050d020105090415090612050d08040321050103030908160b 74
    0x1504860b4640204040c80498089504060b0030355202c1c408024485009803800c9405042800d0071021010200001820b40650344160b500700107281c3c110040c16244a544c550071011151000c0000a80c42d814200081c0f020340e541712046031410004041040400605000b44034080b503000070181e0b0030480c03508119850b033b503496852500c079004a83c00640b15110b00c0c481c00d03c0520710b240d5400242d0b4010714052000d08611100180480f209480e200c1d2a60301005031414020020382c130032a070307903807003441c040c820380b00640c54007202143e50801d40b010066405550201403038110700144010008060f080c020a5501840540400340c1441564001d900d0340d019001107a00c00c20480f101080d0061040081c00c442107962404035400d4000c0e014803500d008804652078140001d82019a6800130003000103902c0340d10101e8010801030012014002c0c002c51007082648101301c00801e003003441000095075859818003c0c00c5004c542c0c05a1110707041982040300c0317015070003081002d654104066640c0c0342 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 312390215 1250 312388965 312388997
    0xa050411070f0303020306010f1d010e1201051008010b0a082e0c030c0e1c080d0213080303040c0905010b070311070504022d0310120309030f060203090105070f0c03 72
    0x1105074200242020241114001010340540c0554041d410a985408600c0306194007a101c1c01500c4840c45019510042d11202c998801d0101d41d81c5500f010b400c600085d18203100003030940310240c17a08500a05152001d01400c1070902c107070300c0c4010080700c00c103002610b0300d030016455819141c0c00030300c0320160b06d0007070845804030200140c040283c0e0340100301d07002d2002d00007801450b805400c00002a40c0880c4043c45141c0341480340f501510b01c0e58069001c600075550b03021981d2000c1c990096843d000e2103c814000c811068004c020305601c4090b69891030705180c07214070f459964200301921454400107000044244007598901a41400c1031104801a1011607180c040660f01c15a4401c1c00055031401c038030a000c04a0240e41c0001d0408110340601e50b90340c1d45603000485800d80004c9050004001002700b81c031880801500904105035025120349852000c444072001c1941c1081e00007060162600d024880e80b0b0380101c01d40f07031410300c0801d440801410500840307805410400c152000000c54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 312391465 1250 312390215 312390217
    0x203070b070e3d0806010908060c0a0e030f0601080304090b0a0f060c0309050a080f0105011424070519020f0102060103110d17030106111203010501020703020d0303090b2809020a050411 81
    0x83c41c0040d60542c40c902d05000003082030070700301d03020350000380341c5403000a10200019945015000350506641050000031302107034140ca441d10044d41c07511401c18201c4040c102070103428040c018400286513030b030b414803400e0403d0303070070500410f0f0040100c90410420f0007111a00d103003da441924040f629003450b410110354011041e080030340d110608400c0001da402c0001020b425070150031000380310350b81c2c1e11301d030500d0440021180160003440e140c409038034660a0741c0c804500300d894107440d40e08209050700c65515090f115941c3e0b1000e400364800080070752829600d01031606101b440102038035070540e500d034000fa071031062241d8040c40d04c407903200003004480a840310848488004850301ea6a6514005147e003100310755456060280e4818000e45512200440303060b070384c040c4c0051041a18550030301013610f456a40031740c20141d44403503a8000a0301c247c1c00901810703206200307988070007060f0300c000303840701d0001c44031491245488030398001030311020035081c215141101c0c0051007004a414548403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 312392715 1250 312391465 312391549
    0x1080402120f1f02040305070506090109030b0906040c12260702220b03060417030a0e010c0e01020616080a020903030c0a0804140d050a300203070b070e 67
    0x716009442c0d040e454024009040030842441d100700c03544000c00040c07407000701c1c400e03400058840d8001d12014052420403500520700e1607010316010000b65903030785540c3c81d3f621381924116815001130381448248803d40002d00d0250240b035008200d030401e250b07124240200384100d02d0356034036a100844000b10500740240d840090f005401d007401000740d60140f80034a8089260f401c130356441c2003a80080f509001422078482c035404000c4089000b000030700701900e500024201c0702c11585488102440c4102805034020849041d1030740c83342121444006400c090005201000203148032000a50749030384039011540140700801d006940712003c1d40843c0c2980b0440d24401104d1192800c9003040198200061080303e500503203035202d18005600700108401205006840d55002407501c0d004210f078400403205466040e15108803c02c80000030012007641d055010000d60400310703025003440300550f1010703803001140c508a90821039100000313540c40c0c43e141c50007020311801441d40150181c40d0030360340c43e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 312393965 1250 312392715 312392749
    0x70f2c21070608010f0f03021507020a0306141603180f02060403020409030903050c09010501050a030b1f0f02190515070c06140103050c010810061b02090403030509250501080402 78
    0x60000d49400b009080c2c00d00a224001a1061104000513036420085400090b81e48c0280322902c00d41d0366549400d0715400282d0113a0b800f074560350002000a0803803140400715051034140e84070a2610b610010046400c101c808814141481546ca18070090540c11005940c4c2c0038040c140c0201d01d40c00482c030f00780216000250403500d0036074102c050541194130708049a2281040700c00065820041c40303141c13542842980d010071021301c00181114003a41041441e00006403c56500802480c00080d100c0740c0c100400010070030a00c44c98006903070611012802035548824010346184030b80e00c19171b44540c01c01005800c4114100030469480c890b007a01c8401d40d03080482404034540f000d1840d804000c00380310403138051007400303e45404da5014500e076a105800d441c0c0c2204031245010b4082d1011070315540c502e40e00c105581240700c0140c0e144110180518000c0d0b400061034641072031010b2900100b15542c0b40000900c01c1c6a80e2110001c48260050322420b00e803460312600d0f0340c408510340070f030311503060a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 312395215 1250 312393965 312393973
    0x10e010e010e10020a120e0f010903050c240708100e070914040507081b121806010b070507180b28050d0f060c050909070f2c21 56
    0x4455203054108280e40c00c0e81d4010380e001c8071240d0400d603049100b504031900202d00840d00c440e00c3c0c554554420030103035200e04c00340c84c00d6070880c0480f10308441242008501180000c140081e40d004208080050711407000390b400540780490b03007143c4800708024541000c001c00907000840346060344072460000c05050150008600700381c0c001034800c0d045405080d002c040b030030a842d0040e151a000d0540a02c155440d00403540e20b070310701e1010741018085c40e01c1d9804036041052034164101c0245081c840d800030505000d5041c00312920506208040e40103507181e441c28010400441c0010404000303d40041c42481030303100000f8503000281040194559000c411022003004100b0600d402e031702d80000364104102300c0b0f9122000c00180709603c07070018041d02218000c00c40004c030284c1c45100090740e14241242031000c034000041402004403a1400051301d0040703180320b42c54000405040e00d013071284802840e0b032400802d0515041c1d41c401d08600c039032880c0004103801c681d0020411064840e2205072 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 312396465 1250 312395215 312395231
    0x4080409050a2a09081605040e030304030f080402010207120602120106020321060a0306090c0f0b030402010f1d0301020315120d020a020105030a0e06040c0e0a051611010e01 76
    0x1045160400d1140030102420301000407032000c41c602c5441911421451941564403851810025904048405109100d040100462200c90820900402403031000741085454142000d0001791a200c4250a210758014003c0c400000d4204d80c1d601c400180701d02c0d040300b1076030311800100c0c5050950f41c00880b440c1c813000030500500c05660000c1c1200201c8601c0c0c44e0660340c1e2403904980c0d81c13098002259044441c4600f888500151750f1031a40c05c890001c00080b449601d0782ca6100464040300c0d003c8402c241000e0703081001c040941e44010003010800300144c02d61406800203045242c8841318402001095080d43c2c0c114108880c003e0031108014000b15228070f00b1047c2108100e00d100b02c602d1240304c0386c1c2011fa41104000035915100c4206a000e40340c200280d600640301d07500003602e0030085580b241501d4501c80420441c1622560107810005046898a1603600104a0150034050603c1c182400c0010007034009084010588161034a004200d403180382490041c8012900002c03c1d500341810 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 312397715 1250 312396465 312396473
    0x902030a1407150804110901060801060c081b0127082a100e120f0d020a1110090605060105090d020f06130f030c080d080c031b031006090f0803040b03070c0b04 70
    0x10244100d06c0382a5007411005d5403810409031940912650002803001c01c010700071284511308004070144100c070100d00701047e00b02c2d8082e01c20303620b02000e840b0341c0d1354601d98905501203c0800040300402500140d6404258445025611a20044040600c0400440b10854103e00d000c0d0035205070078005d8824401e44000850060503008050095074030442d401c001c0140060411034103100b174200c54580c9011490030f030240182d00440048402c1c80000090307102613007400e00482013284803090002a00391035510703200003181c4000c0c3c102410400244006038154903036240c240502501100e00d52104814a0001038046c400e40ca104004100e08500c00160810050541c1e400d40b4400c1c945e041205440714101c60b41c410103485800d0001d0a0140811040d110100046070440d2240d40e04100e03441c25081d0384003460b4070a40d6800f2416211600c10040360354041300200207003584030760880869107030045103552400389018103400c180300000400c406c503004c0d0000020413584a40030075280e103000d0070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 312398965 1250 312397715 312397727
    0x8070f061b03061404090201020106050604120506181e010209060d14090c0303030a05070509040606050d1a0607082116170f0c09150d1e0902030a140715 67
    0x111140301040c2090856111800b034014001510307a19815010310b02c166a0400000e001e006a003a415950303200c40115442d04c0d291300501c09020100c17500c0c00303030003044c0c40c01906c0d0000c000d06580c207100303d90803d4054030a02160114180f00d0ba02003800000302c1b400148e40c0284038011a841e0301110014150001051640100c04101c0c200c03003080e04580d950407206511a00003a035202d5054004000151100009e0707404250000007510300a4101042c078000b04003203e07090b1304640f011030b00c0450201c480b98614000c1d0402d40d00030340b0842e1880e080c0c890128034640240781005000c85000706a0300e200901b032541802d81c180f905086059642013101350181c0b52401600304070002443d0750030894684d0b440510940c0103104003000040240d960300c0044c00300c0c0e04135024403035221184018074002720075540003415041c9801c2030000b600b41140c4002588410501380c0700e21107241011071400140e42c0102d0450103007900b04420200d501c5110200506080007600a24a046e01031800d00040c554002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 312400215 1250 312398965 312398981
    0x1407060525030b09010503011a10051909050301200d020a020f0102040303030c02060c03040f02010f02010f1d07060c0b0a1d0a030801091d0c1e0d0f0506010b0f0f0708070f06 76
    0x71394284400c3e41c880d4145401c0c0d1314000303202a0404520105500c4904002d040300c403151080c1d19126003450b240340b0461405c058006800350000302170050a200300c0c60f00303104d01c9017088042005804103e25441c0c80480310f0003135136414004203501042d007594880c028414046041c80700b000071540c568032032501400410324000b0321001442488002107005003d482224003c640214146d0480c14041d401151002ca030315000b2011552181007130180c0400900031883c0c80c011481015485a07030100300e440c61300606612800c00c111000d0a1400030450560101d034002c0d00803600440d050b03c0c548418401f40d40712000d0a806da01c5001e103428141607200751042e05039814030b88240700000d8800c004811441001f0300755000e0b038101b801c50300400d1901140e2140105021640c2c2031031401c3c0c290002c1e01a8402e00713420b540c11038500c0c00761001c0000c103010407405415050099801d04000d840c40f10390501541a0718514003034001511030600a9407010b0701d8503d640a80749240c41c05c414a45640600905 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 312401465 1250 312400215 312400219
    0x12060e060709030f0b07050906130905150d12021207060e070f1d1504090501050105150a020a121e0f030f020a020307020402030604391407060525030b 66
    0x40041100d480c40b81010a0499800040c481e240c0c80f0a0b8942021914000d0003000c02d204080081944548a1801520700f01c1042c0707441c0700c400c0349010b40140c1591303001042c00c0312503040d0400842c001c2c1c1d202c40e004080e01e500444001104514000c003640f5040a54031810030840e400b02d03030711082014a030001403c4c2000d07401503d00d42d1350340d010503e46d48601030080340030083c01031000100c0c01d0780501205034028a450120b200c11449080401c0454035248020390b016516071005000d181070000f507440300140614006882c204068400030b44450f04207400038a18602c1c0b51a80e15071500c5000c40e0b5032030030342860705004500d003101c2010348a50581424a0040b9082c040300c0901050140300380c8010000725009940340c1141503080000a50000f0901035004d641d480b040c059110841c0140080c903203052844215522440c04d078003460506040c1c07494200310142007114101500c03902601c01d0940d00520108603030701d42c4c4130101c0074480c1d41c900d00c003100091003480208031035150700245800402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 312402715 1250 312401465 312401473
    0x409052401060804030509190803130f030b01061d130507080a06030308270a060203071403060303070320010c0e12060c0708070203070308040f090e010c0206180712060e 74
    0x5220340c0800344080900c0341402164214001a01080c02000105240e080080c41110941c81c200e0303801e540c04159810900f5103a00102d5192010024441e4400242c1045008807014a20350341c0d40c1440311105006060821240006d9100c0c030051150700d1040828009007030f2480c4285180f01c18004080843e01d21000070f90b0603020a58540c0703948168826a0f805075560300986e03a8100f50301450210100240c800342c800d00010341c0115105000e80c1d03401503c220800f5aa07400c2c5a1002010340040c1003041d0300c2550104140b01c819a400002c6600050345410600556241c5112010082507104003400b0694203189644c01041d5000c00c0a111165040b900751020440940d103060780c9040403034119901c0c40d81000000c02081404001c0c5c0b03a01c91009044a107034680b01e903103021094100f54460400d00890729420b1000c040f1a008440341241194002c00007900301d070303500030741e521030140c40322a003c80110782c48070600a040c41540040d0011503841c0100180c20329294000b407294003c51521409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 312403965 1250 312402715 312402763
    0xb0f120a1b030b0117180a0501060626130206160501050f07030b0a03020d020d05100f1109010509130f02070f020906030a0305030123040504080c01060803030601200c040905 76
    0x202030301c40d6003c00c04041e5601d11030000015060504e20001070618011000d45440c182c100071020440c2d0f00c1c80621803c00030582c0d52600c4d202a06268080300e07001d84c64000b03000c003840e2607007030008803503440038004080301d4141060340040340e0140302d1224480844500e001e0b0b000f081c0041500054010b01d180640180d40c0e68554004130222650400007684c444a101c004002518111226640c40da000030241410310790140c0d1060301d450a000171105000c0d031101c1a540000e84107120f000039140400070f8203441c0aa200c80000c20720320070060494856201491440a030004a030b204c0002c0894202045513600c0150a0481c5910700460080748203844c10400079613942000700d80e8128095054441904507400c000e181000c04045140040c844019a00d601109903201e02649004038000c00c0b045507a4500c601140b0309607070700c0d6080100968001c10901c1410b0340d00c10781c007031240300e07800c182412414002b81d445410031240e0305107241c3c02420030345440c1c1404030100304644865458102d41c10b03058 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 312405215 1250 312403965 312403967
    0x60b071406061507021e030114090d0216090c02071a090a05033c01050f09010f0b010503070507020a09230702011e0b0d150614030105060a0b0f120a1b 66
    0x140210302215083c802842481c00508210009002901260040042100c089808242160a56480300c0102035001c0280f1402c00000d0080540c002410300c06005000e40c0040d080b94000c81d40c0c4182c8170050342d070f12142e00301603100303011282c0945000c400c0044041914030702040190071101c0314610800340711800103607a00d40018080c0c641f82600c80444016a180c044030071291001642d542800c03401020020a600380a10070b2600c1a070030051200c10900701079904a0849240c0084030211901d06602d840351a03070042c1c1680d43c00491458030320765403070551002c074040c035800c1d500c43c89400342480c83c040c2114a11031884000c1c0c440d41301144401e640d9403d022801e844025011525902c0c006a441c080712200390400c050520b005070480420400c0c664440a40e00c1001980c42586c83d03840e102848900103010350120062000c40091049080000c00640d0080c1148104003200720000b0b00c1d40c110090001c140c405407002041e204540d032030401c0d9040c0243c102d225105a047c20340d444d603c0c18132 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 312406465 1250 312405215 312405229
    0x30302180d02030d033912022811030309060411031203190912020d02070f030b0f0a0b060c0c04060603110711030106051002010905060c0a0f12060b07140606 69
    0x220b500100201010703160070205600402200e490b540d006896250001e561081d407901c010803c0c18805101c1e00d10048060b4000c10740011203040315040d034010821404200e05d51188100c80c500940200c2440640100054a01c0300d00380081c1a82d0b80000b00400800e5103000c10103511443c010030500500c2d1080d1020151103d18070080e41d500404107001140c844062000e140011410505c4000b4050110f03840307100e400394916500c070300183d0010810001c250707418001000104400900c001c249030071641c945680c00c1c802040d01031540055000984180025044032069030130240c075682d81c3c0c082c01414543c98080000d603403400385040c4200080d006210303105002e0902e001e84403680c00d0881c0d40d078901d000c2412010029905641380e8002003007907a80d42d02018000c850a4000160004c00d030702d810717810200000e08160801d842440b0800e84150024484420270303440380b812410888050003108014082ca1300702c03c03190a0045076460802104c41d803005010490003048034029a103000801c014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 312407715 1250 312406465 312406489
    0x24010e04151e0e130c0e130201120209030c011407060905030c0706020c1f030603020301021803070b180910080a08210106050901350712090503040e150d03030218 71
    0x500b518940009122038071304281e04003500c0c032540c02000207940d0b13001502100201a1030070380d200600002150219038000341224600d125508040d82054000d000081d203034072404461605100d00e4485000c50f00c0303c0706080f118042e40c014400c0140c06d80a04000348d0f01d030031000c1542d006100389200418050700009513040d0700080206002400105112444004080c908200c402d140c0c8501010006a40a0000e001c0c0c03140307200030681458901e4010549003450980c484044242c0810050078021408075910068207025180c0741142d4603140c1c1110709442045d070005140c0e014130440c0c1020051004010b29405030711166031013000c810600c08101070741081c400d15000c0f810401c260f01007035005100503440c8034403a0031080c03000600c001d203001036900c0c12003081100d401e202c1d00300b00d10307073340c00580c4401b21000034041002884440c0e62203643d03911a134000c1d04248440b560000b001828615031506440f81d0207000000c1c10001c03032030003402035089000f42c40c60b6141003003001c0145043c80d0a0200c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 312408965 1250 312407715 312407729
    0x304050a0320060705090d0c080607031a1e030f03030403050a1d0a062001020c0a02100525060207080a02060702060c07020a0905090a050d0801031101030524010e04151e 74
    0xc0c2c503244d041d000c0d10340398042840c0395008030b2900100001f0490f00280400100442d030302a04551504190042c03c447c4d480c010120308002c2d1003001051511007a141c201c40d6116803d07689086000b540000e8509400020f8001c81444000100810194080c018180e07031a995203c0300c001e06999130303400c0c07600c00503003a03515002108410100020342c440c8110322070541a060300042840510f0842e1170a9a001c000e0490300e076031003c00d102d000c504003440e4907007107100b442ca004c5082001c1c040301c1052001b000c900091003641080c180b0418419250f048595055000c0301603030b583d1603007800c0a51a120111070b56009406544001022601102c0c112051240d00420744614607050001d9100288406010340c0f0851040c5140d010002d9002c009140461000e0788800c0300d00d61542ca000a403030051702e100d1a040504010030f000d9041c0500f4185818007079010042e1012000360001241c107240002080c580c041c1c2000c1003140717440490a43c507010340700403034105010300c00a0316a030f0001c4d1000744940b035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 312410071 1106 312408965 312408973
    0x191e05030417010501051c050102040b120a0501050a0602030a08090a0b0906040b010f140d060f05010b040801050a02030903040614090303070309050108061816140304050a0320 77
    0x6102c2c1d8502c1d0380207105560411020440d0741e810281101d6901507090950300803c00b082d016030b4054086038400c07546500d1a510780180c900c10a60350032040c7e40ca41000401c0c54141003903058142d51a0b500190b14200380e401b02200c6800004220980b18080e81103404c0014a480f200140900004002849281890b0414001c1030380e0680c49038038000c00000b0208900081060604a028003c0f111500010202e090030409001103910300741441f0b14010001c0b82000c2028044c00607620303000004c02c034541e1480c440b0004c80c44256130016050340180010801d032481462003a042c014003030030040c01d0583d404040f03440d40d003101d0b004801047d0900e400b4451703964014489944010111040011000721020040c1035190191260145c241282000410306000d8254280d4161146c05c0d4280c0d2072805041003511009640e5007100040c0d01500325140091001402005202d05079000d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 312230215 312410071 := by
  have h0 := BRFrame.cov_init 312230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 312230215 ≤ n) (h2 : n < 312410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
