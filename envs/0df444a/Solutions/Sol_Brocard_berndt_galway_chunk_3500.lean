-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3500
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:50:26.986903+00:00
-- url     : https://prove2.me/submissions/5b1e4d55-1791-49a8-a234-7f7da383afb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 629316546 ≤ n < 629496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 629317796 1250 629316546 629316551
    0x11060907030f030324051318061d06040f0b013c08010e030c0118050705040207022206031401091a0c0c07121511090909160815150a090906 61
    0xc00c00c2003815501e03030b110661a00100c2400803c00b80c41c0c4070b11500d465011126082142c0005030090800a510094004009985500502003100384001d4a0f44a10040741cac2501c2442c41d180c03805150030040308400f2145902450004214159500710405080d074480250350f420303c030b50341040c2a0b400b61208140491080250010070301d24030030f0041070040c03150b181c011a1606440110942500c06018036000ca41c2100c0c0902004110b0000d002000c980c0e041e030f401030b40d4294500202c0c030540d844180000c1000328a0510156840e0b550784408101ca01900708410088151500142a200c0c4000050308203d150144c03d459146a40c0580d6006108622480d2030404500300e5181000c00b9a440f120146007825500740612027204a01c1542151a80c0300700306d6a5101c4280354418044c40c1c200b00c5c060342c00d42000450090f41008490f171103e0400120155603944c440d2800d5480c218001c52404d900916008107000212110100760365450003410101c01c203090240c2d280040103001402d40d03440740c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 629319046 1250 629317796 629317811
    0x603250807030302010e100b010f11031e0a0e06030c090f0d0c08060a0605060f0403030c0309081906110c06010611071505031e04051207080d020a02010b0111060907030f0303 76
    0x80303080009600a40c800d80020494000c680c441c1d60400120400c44404942042d121440582e80001582c602c905c0328100b00c0c40e1022502100d529501612003595038062030039407007041d1915064083e142d00710840c0d4a03020314040d198240b080600003a242d0310b0003254144000d07800c92411312201c044180340034290f105486599214520940426404a0900d80203402402000b403414082c01010f0107060710401d1038580c454aa03000141300c0c511000d810030070742d01840d408051150582034011b101603021107003e40480b00340c0096036040e200084400f940b0f030081d80d50502158405483e01900c41401034141c50f0b180540580b48803200141da2281030048120110b554040e04112a4090a156948607120314107070600541c8900071480c0070b940300c0c54410800000900025a140f02400e20124407078441c5403500d13244d0001d008030400552924000702d0300040e02c40d41540071800c180e030300f6a2090031401c1411a03e50315800255500081e9800500090011444182c058032520348280f40024410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 629320296 1250 629319046 629319059
    0x305121e012601091a0c0c0a0b09030d140a1d1c02030c0703030206060f010206090c04020c030403020303040e0a0513030804061802120d090f0b0414030a170310060305060325 76
    0x542420908648110b11007100030085c11414104c00d40c0405030801191400c161084ca843c3d0f92140b03d8002000c1c40f25000004254000a200b03940307130340c104008203000514200e11200d0310b01d202150034039042c51801c4404070b5604049441443c810f62403001828811400707a02a040101058550b5415803008200560468008000000066010b980a00f41904209d010086003401900c4018110751000703040c40f070003150100d0580c080200031280182d403000841c06207030035801a54006503040c0000304000079a0018516014410704200000b0001a41c412402e0b0300d541624420280c00185203c00103000200319911000702c5100003901303400f000d0601e03800501030540240c0c100042d604820107008035141c101103014003520800c40741810440c14148032603014007032031052400c60765008114028907101801000e507440d03000f040b00303503291051400d501e541d80e000f500c4540c00110300c0c13480010b900d40300c0d00c5100d0042078010090070011241c4401c103d07980000c1015942100b802c83d1000898 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 629321546 1250 629320296 629320301
    0x302060409090204051810270309080601080f060403120209150702011706010c030c06060f1e06090302010e0609180115030e0105040f150b0d0305121e012601 69
    0x201521440824003154030f00c103100950b80301600515100640d43c24005c50320f10046007000f032101040d080000d0b200d180c111003080c510f482e45c4000b142c12000e100d100091640c8400c40d142030300c0000d822103400741d998400340c0b130791012030311001c01080d0810404940041c3c8120403294070446030080260800c1f040b00d00191202034580040050040001074140455030003440b14050512500144059864a10000f8104d40f2043c000242044003112040c41000111781c00b0802410801b1030b264040c0340c4400d021014005164604e81c0d010100d07400020310140716425060a0380d5060303442e0106440d4600501025800003481d6aa0210540000101178600510001e00800c4a801c045c0c0d04140c800c00040c04a4503021900c881a9041004010104440b0404031040c250310610305408581b101600100805080c550141c0c0309100810090525038000060f101d840303008002d04141c3d03158404451034001504807180c0081c07061400401c18440041402d08019100700345d030300800312851039650b08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 629322796 1250 629321546 629321549
    0x80a081312030507030b010e03120a0507050a0f03200d120b040c020c24070201140c06090c04050115200307020301060e01090e06010e061324030501051f0b031003020604 74
    0xa07a61000c00c51350642c54090100310600c282004614032040501080c0c0395011540100d150303407030000382c3d1603103a8400c204450500b0382200550f98036901500d04299440342040b41a000547c004903410040710820326400c1d02d14400c1c1c8000d100101c058101a0303034504e0306241160f07200c0e030f41c0c2c0b003205015217541c020042106080e44c06080110303800b404100c01134804070008045401d0324013007408039440354022541e0551302409c1c5880d056000100304000c510031000e082d04a030043d81c007844000480002e41e5413001000b19418006070380c880d0050340c009081400c01134009141c0b00030302402c002c0700c000d805c1b20558417102902c0c64248160040b07400e4a9a40c3d01140b0306146500040289180303611518507484004009400a545050130402241c403019000d140314000d10a004540300f8401d0340f0150707441c803d2940d0700884110550b620141c2003658401601c2c81e50070300000076a10b9041d403281c2580d0b1544060030400007414030002c070b00d1641004040080d550041c1c0c1d00480580e0720036000c7c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 629324046 1250 629322796 629322833
    0x904020a031b0201090308010504020f04051302091806030a0f0204020d0e0a020a090e06040b0c041508180f070b070606051216090203012706032001110a080a0813 71
    0xb640c41c0e540c2d1074860590840c40c408200b10391402c0d03600400264003049150448804039400342e210101003c0b0700010f44255405103a01040c8403c528110310510303000b0b4940311004880203500311240c0c440d4004c01c20011507825074150007141900340020382e50b80c000099503001900040c01c1c068280004801c5844d1440d080706141e0101d2038140452806a004070080d0400040c103200c131015041e1241e903100800b80004100400103000285200d4840083ea030080c06007402244020440d4400580f40030404c1e206025102043c402824503840b0004900c00000c3c00c281c018402d03d41b629129000541048001b1508142c4503600080d0658800394481c081104027005040b180f00360782e03010940003103283e100740d0410380140f0041080324292081d140120004540404030800c0600806000780b005401c0106046c04c080d0320701c2000f504a2045010310301003070301c070380b0303000d900300003650b07540300220100101810070070030111900074442c0c01c0c0c240d08003e203000700742c02550107603481407022002003e001c0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 629325296 1250 629324046 629324051
    0x5011d0c0a0911040501080a2004232404032009090d080a09050c0406060302090307050f1f021603050312061e060f0d020f0405151606090201050904020a03 68
    0x864034a081110a4010007078108200f1441c180d801c5119424007992040718140400d00000441c0d50036241c103d14443c500a90200d10b18a07481300c1d0750541a0890b00880540d0740f02a003140001c6110701025001d0004010100c6048a043c0c030386c05180c05443d40c64403480c1500500c400030020710020080f111611590300d0550106202d01309010300b030300c402401c400440e80300c0108091070030340042130950405034600021030003d1145c100390f0701c0d002c040d14100b90401d03c0c03c440052240d0381540508002d030300072000d03103180071707956002c002d51040503844103907100c1131141ca01d40804c8000c0b05117141031400360041d200e80607540305820408100c0340d80706940d29000010383e01c20380f404040704541d100e036088408010b5000c80e103040c1c0000d0304030142083e00880c4c0001342030000e02001000e542c5200c0302c001040d55623211a0749289441d42051003024040c450b07000070148410100c0080d50042c2c85183c1440c0c005062a8544001511400000f80d0501404020300b0080d5112030004220740da00700d8802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 629326546 1250 629325296 629325313
    0x305030d06090e2406010306170c040b0604060e210a08032703091e04091407060302161223070b060105040503211909031b030b1305011d 60
    0x50342900c809910041c0141c100e00d0650521036a84901104c0c0c8496000d0070120307a541d0b080059004003d240c01110360390114002c2c041c3c85a000040a1248013800e81d002d02c558482c03001845958010340c0110130200342e8903240c11041d42800041d11002070040c1c0da041025009032a505400c00c511b55000365060140042080301c0c0340400c0301040d1a81a100050b501462848101c450300c80c050f181403e4444c0158881001d07007981c8100ba503a8078240010010004182a898103046028800300c007202d06000b5404001841402807090382d0400305460041425000c141c0d840c0c01008982848a1007806041a0382d6070500ca0903ca18250402181c40616a40d03031541c00c2107403030710030010072250410000700010b0003243c42c08030b0849040301c010301c0540c01d114450661520f160284d644a03d0b400710711111f645140c00c1d070001601003242d000300d51003052400b201d20f0340940900180800750101111002007a0340152050155000d1806040002901580f40f40946606943c0d020f5986155108108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 629327796 1250 629326546 629326559
    0xb01090e100512032b0b06120c0711030106061205180a0f03051201120b13120c020d0f050a0b0106020f03090603130c080129030c04050405030d06030614070c020102100b01090305030d06 81
    0x3d5142c6c500c41101c2e0117041c01c050303032102c001d22000146503d422880110b40a010852001142110408010020b20465440310340062515040380701d0304407118103000c041011014100c86030107003201a84094400240141c9500c01c0c500c05a01b000c40c1081810410640c0c92038030445114040e006105030f619807003000782040388036070340060202803a2004455101000890000c0c280405032202e060180100301a800001da19000000e806001c4020000c0c0900800901003808488113115000220050b6200c039000c80e560f42840054070201e900400100c40c03a49817210156034050000d0242085880300e03683d80010366400366003d0101a07440c0c600c0506102c4680480c207480750000d4440070b0081c0802c50000b543c0d881c0400b04a4060355a4030045001d102c400e001f01c038040c1c1d9146800340400e0b5940d24000c8002d08054a074140804805404144503138403e00000042540590080512049042a0303000418441482e1410b0103041e21001000070001c2c4085c000d1410172500c00903489203408e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 629329046 1250 629327796 629327801
    0xc0c0b0a0224100303180b0c0a060509070e271902010906030c0503041b030807030e090105011407060506030f01150305070902030402030d2304090b01090e100512032b 73
    0x350710000b021500b008005650224454240881e50586000d100c40c040441c3d80d190324802a400c0507007403080000315802c00c4003002500c9111944102c80070041e680d9541c080c2500c0341142c0c003450121619440204042c1c1103181c00b280e1201300c001c0611028a1000c0c0d488600d0b144240c07114400040751400b041e4159030b00421020020411800c0610544100c2c06004146200003800100546400c070b080841c1180400410800b541e40300c00c2080d50741d032181c2405040340186586140c803c0d01c001001103000e500c00d01891820300413452859080c1030349035580708068030b0000c02282d01482202010814000c0c24000c0f83c8050140900424180d030440c00c2c120300303104c0c05820002d01a4010024080142c50001d420284803845140040200943c2007512440707239001000804030120100d808501540b07503910011004030241c842109075036441302c40b00340c00c04049880303080c8404042c80070000f03420880c10720b5140d2510002601e207000868080d031a45d05000000c00c0d803400583c100341d0609009a031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 629330296 1250 629329046 629329093
    0xe04050f0f0a0b0a1205010e0d120f0c1707020a05070b270109030224070b071106040308070c172b09020609010507060e060c031504020310060c0c0b0a02 67
    0x200500c0541030700f40101c0c410742545d100d142c0000d01440c2c00d030404d0040a600501143e4801d03030640c0c56034140414000e00d031107003480b94020481d00d000c4180059403c2c61140702c0170240c59454007881107002440172080d03090010500807d42c006c219140700000c100b80b01107405007810412940d19800c1c81041004580703640d140d010155040300c41c0000d4140e1b0030254413411658119241c00443c0701100d0722a5502c4122240b01c00072600109242d010487ca246405100703140341d43e28003412038000d0104564514044e00d002e408241e6a4001c00e4619200e01494864240103018400506000e114040e00d00c1c5c0c03002840c5c0300b1410114282e04a00c0103426450203d1410300d410900c441e0b00581c0004625126600342281440720025604003002102e400041d40a00101c040e1020f5246c00502010349610407030714226144030302e44800c2040d18140c801d6a000340f9050001d1400c1c00d040880c151030009072208241c0d1007045020000418003401001040100d4503603001d803900c42806481d8804803c0e14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 629331546 1250 629330296 629330311
    0x915080703020d2d060c14070c05090a0e191101080c0d05072c0411040b070204020c011506020d090512030a08070302040f030b10051005040905070e04050f0f 69
    0x35401000965200a0107148440e0410500a00c114411200540c2e1009440d02121a0360740000d003802809034651000740728180d5600c030f88551820250008a062198050007000b450450b00d09100c41c0c02c00e0320303416600100c810b00005030a44401d500380d00d040440c1a62481c40100000e502e010450540c0741000030110a09058000d402c040401140340e010703400320303c0035907581c500018042d144990703859043c82d0081800311140001b208240c0b00380d0348109401900460400c0942d000c1c0713820300030840f0111644c3c4071400341032050b25420040694484200c2c080700350740b80e6a80c080070101e250802c10061015400074005407000e90400303852181aa030050344900683c49605204150110032602500114640030007147d644520540090090703030018491048200c5000c0100301c0c0702014103020310802d40740341e45855900c804000d0198096441c00740014030500042101c0318860708100d410803d80d01744404006041c602040031210b00301c1e0244d202c51110400d002d80ea80030310701c40b42d420950 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 629332796 1250 629331546 629331553
    0x6050105120a0302060a0c03091a070906020304050a050904050304090e0a052103060f22021201080d320a09030201110a0b0c130b0307050301051216180b030106091508 73
    0x20b81e44019403210390042c00d00704110345408811109503c254000800d00c0c3d4840010707a01880781021000d1003280855403c00405c0d00c90710081111800041605e00f251801045032103480d092400303014405070082e10072600c03440144004102c1800c035004040f0b145d0780c0800181101c007035908017513103451044102030504003114816440141c1c1c504046035802841581d10f070b04035121603030100356542040c0c000109800900310b40049800b400303400905d1422401c0c0250003559803507030041d64a600300d041a450103c1c07035454203100c0382e4900707200c16944820310240d00c6058054a074051111544003240d00400034030401003d00441da000001d45080c00e800c1c2004013140c410030b6807107641100001c4c01d80300c54141b01286203035003001c64041d01d4001c3c100d003005043d01c03824541c0001e0041e40003030040ca4441c5081d4410007070807480004000159500440c51000018509a0010785074680c4049000c101600e8082d0b000b03c949007400742c01e008043c111000520a4680c02941c00c108180340c01c0420380d42c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 629334046 1250 629332796 629332813
    0x120414060a06060e0904080c0a0804050a050621060d120f1215030305180a0806040c170c060708190807090b090a050415030b010e0f0a0228020c06070605010512 70
    0x1580008645441c4d981540c0d501840e4549040c140d0b40c50203000841601d51041000610411117503502600c1110303410703154040121303103540030000603001d0840c04c0c0d090003c1045015003215a034000b1581c0101002d80500800c4030180c4542c0e00981c020100500803442045c001d030341903039120034078009030344a081c0300300301c0c08844c003903840c0058166100240c1006000300f24007010000c001000c400008004243c031690760b82d103003480ca440301e40440301510f4491a8401c001000c261002100c1e24505880f006020031021082c02c000c03058000c0d07041911040014080680d1b00701c04050340d40c00849282c3c40703103021f03413034030441c0101018040d4000c0e46013090305000d803000c203881d02c0055800b906c40455006c80d201d0407080c0c182006400a5201030700304100b03440000340240d88641c000303004041c03040500c1e04a03540c4000181c1a482100d00f03090613254401403422500407180e6504800b00942c2c4145c1d12031005000003d9099013100d5007c2d209030750b0301d8004119601d411144054511013100c064003660 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 629335296 1250 629334046 629334059
    0x304060516052a0c06070b04060b09060a0e0910020c0c042703030914160e0c0304030e06071407080d021c050306010c170703030b0405060d020a0614120414060a06 71
    0x440d404402000c10700c24040503d500000140b01c81010310b84007501e201d494074a10b04184070543c10503178040e02d040d0301c1c15010242c107003440c441c0248116000340a80000900e403242c542030112000b0a44d0049010303c45a8030075181242c002043c030070381624020803500380c880703081204840c42c10101003402415901f00d038001902c201030500256400d0701f4001003030700e12030814500e4101070000c0c210b030328003880d030008141e003803003e40034000e50f52a40c00c2d0681940d01d40403100c0c5c00e0701c02a0f03000f5010428141b03094020b80352060041c03081034401c0940c02c540010754881c0d41d160608a40080209802800e40040d0050341040b507040e0447c6140090701500c0c00e048000b400c42d102c042c101604002402303ca000911201e10f00420b0b00720344100c134082da11310550400900600c45608040d20a41c14440441e4440c03508480c01c0300d03110b400805c85000145050000e03180054500407aa040d41c0060007040559520701d01100c2c0315a001e503000c80c2c9440e00f0b030b10506040403001082c27005140e2806c0c00c02e0001c1d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 629336546 1250 629335296 629335327
    0x10b090115030b03030708210703060f091a030d26040b0a0c0221041a0315041d070f0305061b0304030e04020408101a030a0209130303060506030406051605 68
    0x41c1e40d00c90030002a02079601010074254030074041c018003075040c00a1600b04d030009005400021500d035408220107510780305411815103035144560001a108823209008c8281c1a50000000f1207101d000071285810b110042400d0545401990021550b44040b20b0015905055144400e261282000c400c91030242d85001d001328020300b041c0a06691442c4491100b07008108226808030321030429000d28080f50b8061a103603021b4024000f15001051003008404543c0e07054070701850040740b2203400c2442ca0700601c002800410710942101c010741070300c0203080b80207000840203856138440e04103401d03080d802c14038179180c0050421280c004084401c581c0e09210081929042903140c82c20380b0034031610b10b001801902454001895a0007004503ca0074030b282071303110050703040d8091001c2d04412504010180c40720110600030750814017190004800c8000400a00c220501c079084c00131b03103151150f0220300142c02c2280c08a980f81e90f18003c0c0b0880700c4038240801c1681149181191900d1a0345605144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 629337796 1250 629336546 629336579
    0xf0f131d0a030c0605131a070f1b030c02130230070903080721020309010f02010b030307150615020f010608120f07111906111203010509092409010b0901 67
    0x203515500c5c0046205203242c0d42d00826a644c022000030201560f20551100030301c0c00b030311404045180304600d00d400c4c034010300708040030480b01c5211501140d0f01d500c040c1e4801305004012680496000d003050852a0244041c00240d41c042c0c1800074100c070782d81e11401084152440550f20710f21020200101c5540c44120a07003030720f034003401050b12155a0303d0201c120111807241c165031807410f02802c42c106a4000050301e80345100760780d00211907a40b400d0a078229582000700e590540c108000d03e6000c070300545aa4910b06541c4c25000901e580d8440a59030144100021440103800c680095982c1e00c03024001c0c10094003068021f041e4041d40360f1540c21451180e081102d21059000c0340e50000e01800501548800380054091901409203003440b11720882a40100d002041c015007145a8030900010782d403500002c10b100d240d00d16400c0800b046110800180200c005100e00c0506040c1d85402c5a440da00780c149000c206515410030011180c2520042095a405107140c080100b0a01e03000f41d501c030a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 629339046 1250 629337796 629337803
    0xc06030e0106090e0d120e06180606040c050f30040b0c1206040902060919090f020405090606090307090c05031e071205130b010b12091b0f0f131d0a030c 67
    0x41800a410b946e2001400ba640351501c041d00501080048a002e104506202009020181c603d1681e40030104000c40755002d2402c0002103052100f0500351807030314010070303800d14689005410005000144840e003208040d4414011440c00113001c108540c1d0000c40e038000070641c9990341812400080c0c0140385070000c0142d4820f80d00c0d0310226055440b91401c1f2450711201420504881052071000b000c4807640c1e202b40040d451170315000c042c07007848500c00d84041e201c0091540210313403944020400141c20031a5441d516024000000a10100c1441503000c8503440303442e41d54403440c0080d2035554441c822217081c52091800c6041042003030b8000c10700007140e4043e0900107515164820080b80100502c14007c1c03004e40d80d80000b00300c4540b03642c09001d103403c038131011a41341d9560740031907621001d0119401d060381c2c492807c04401480d003079905550300b4402419010f98400004005100c00311a110445c5040b0781e2200312076442c8640c2012200c0d030110000c010039254003150b800903c610040790014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 629340296 1250 629339046 629339057
    0x30f0305131b030b0c0901080621071509090626031902031207021603030819020d0f0506040501140616120518090106200a0c06030e0106090e0d 63
    0x40d6000808000301c50070180c000703a03068030803640b1600e5084404118001590600102c200191215840b40d0071600b4482c010383d2800b011344c54071400e02c030007461002c2400c040c418801c80c4201405801f04202c2c0014603140b0a0715105004100d4040c1c1120343c5600407002c0da6081c000184804c081c44402c01c1115aa5144041103006c000c141c51401c60140c0154460416010310000000c154004050400301440e0481c19100d51544003069940d90704050201c2e002c0400071a04001190003405550340c85824060340661425000e056007040340d03c05208410a169500c1c60280c11210138030030b4503805042030f10300700f07d694100030002d883c107451941d920b841850001a41c260749141ea83c2e83e070103c40d6005800b0640f12002c41801381c01c45c0c00c982030807100040c030604c10084600e0156000e034103ca409480320603626055881607501000c0f0a5203295952242d000f2550020780c4030021800280032076500050111034505200d401e403290707540b200d1501d034140072000d610407001240215003017113642020f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 629341546 1250 629340296 629340301
    0x70614160311030127050a200a02060718090615020f0c0a0510030b040914210d050702011401170709110f070312050f060f01050703091a041a091c030f0305 68
    0x140c0110741c6500c14000031751401c0c501400041c0071140c104020b004c82c0303103d00401d007494056540165015481020005a104801180b503480c024400b03420b040c1402e4140540c081e46410308882622034a80c00950046020403041c40800d5062100702003404407078000c0c2c0700324145440040e141075028020079216189016228030703d81d029034001c0c8490301000d4030034061740e2030604010460303403199583c1d90f559000300354044480c034a8583c01000402d00028045040244004007803000340001450b4100355076841003408032000300e082c040b6000f400500342c0c0300c000d000c00040c26820a01264044440c0e10308000b0310034a2000b0007001d031f40b41c110890b041c4540360f03082410206d170402050f40354401d806186c03405004800d050881c503184243d2090347d01e00844000140111414070a2910180009481c800c0034001da20300c040410f8441d00756400d11606050722500311209410300c1031031103400c1c2000001e0302445814055144400b029174629900c030886c600c5c0d200030f172580021014a100f01951b6400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 629342796 1250 629341546 629341589
    0xb0a03060f090e150405030301060311070218090706110a060504050c1c0309050f013c0503040c0803070201081902040f0612151809080706141603110301 67
    0x2030030003814600710008400d41e5500b10392004000c2420161098040c058104020542e41407103a4050396101004501d113a1130034070201c0c01082c00720a1a4092001006104007507501c0f02c900d00d081e040d032240702100bd8205005118a040100e0b40300c00c6c1070210b401200110750001141c60a003140d00000c0c0400d00f03680d6864034a0038445c1c0394075403d601c40301c00b040340d0403e10400c14030348000b07a2007600c0e08000d00d40c0750420011340064081c2e550f4005025440c41c01540c43d103070800c0b4070300406071081808403509640080c520007902070f00f01d9000030710040100418440050507210052850b5805180b400555800003010500d008110290b56100b8620240c2c0162407a41249e00401c042c07818258103580709c1c03034000e01404905900e000341b80e0801007042c0c0c0da100032030342e603d04445041404042e00808040d0f400702a10105c0c4042d142e00c40d007400020086141c030b0164403a01041038280c40420718003c80f00848104201098608242c070f030a4032640340d8070448080740d041d00c550050f480f0101d540c0f0300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 629344046 1250 629342796 629342801
    0x612061305010b0a11031201120f0503031e0f041a07090e1006030510050105220504050108030a0801091104030f050a0f030509030c03031603080709080105041101030c02060708010b0a03 81
    0x14900d0009601d000c0000603c4003800015109400003551113040c400702c003142041d07590050b10704000700b401c0103100402090307081010410b00e962007005001c18401076074842d40e0840d0000c95070f81c081502c134240e103010300060310003201e41c0c05a0603034015522400d044d110940b10103414042c2c0d50100c950b07580801c10f0580207094100c020181c40900300359900e420848520018540c0c400c2201090900000c00e4010b14200780410030ba0b001a5146420f100c031030010350321125256141c4600d03030440c2c20b5000c00ea90306c0754000c203070281175808025940c840040704018240e8105a10400042e40b410600d075040400340ca0845046a4220110300300025488c02e042d0300340306480300c0041200c96065111020960840042c24480c00704034142c0e0454074910f014942c49204152542c40c100b0300c00220540001d00034200e03550007201d1403805000482d294840c03142180e20a5074140c4051151420210b0250780c54046d0195404040c80500410b050403072020748021018024200c4600c4082188541940b095 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 629345296 1250 629344046 629344069
    0x30102180f031e0a0308060d240b040905010b0307150c111203070f0506100621020403020d0305031909020616080c15100608010e0708060f0a14040e010605061206 71
    0x851420b92840e0019084035070398100c135003048011941c2c0c04001402454108480d5443c280c100e290001c1c145c880b000128800070148080c1d001c0d583c0d40d1040186580c90728411142075900c03450000500391140401c2602e480d120380d002030880101e140900c4103176540310703400c0002c0079482601c0428401d4040700003842840c80d0000002c0074400818400c0501040c1a41180c07103500a60588043d501e603520315000e412800d005240c0880d14a10602480c040c64086c0c0711000712038000010b052a07125800903804900d9030a0603030000e4008401d10092851001a403000c8044041082201c0ca144c0c0d400b040c61030050621032241180c01e41c07852000e10440740102c0303e108102c141aa101c1c0c4115440b16105d18006850710b4003a5500e80750041005030140c10198140e541c4220751444070b035656042103a407084000d0115421062081200c2100d80768281c4440251041c1490840b28100c5c00062108035019405410b8990703041c10300820591701c800c02200c07901030007012000b01554818020a0460405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 629346546 1250 629345296 629345323
    0x7050a061b12050702040c03180803042109140108060d02040b010201090c180f02030c040e04031809050f1003021e010e0603010306060806091516201605030102180f03 73
    0x150300b00c14060355072010040003d03910840c1d04000594102d4021412a05404040040750900482c8240482c54400185501ca8499400d000c03405000e2121b0345074100c60701002c50040b4034030316400e00410410920f900c0a849003842d0521b2145098000600f683d420048040d018070ba80e00180c4007564400c0d040211f100d0b401819100092b680c1e94501c2c00310320341ea040241c01042c40c003819070201000070b00859004030b081c21031480c14a0300b445451120608054000c03000d000065a030b40b140801c0d101114001000c92600003c2c0340d07c0c0c42c80110707603541d900805150031540202000d100594400c15400e002c0741079404101c503ca026000181d03103c00f00c2401040c0d1201020000000300305481e0000380c03c0c4c51020060ba03000d503d80962566591068070b00308102c640310070b0300261020b040040250f20f260050300d8941d0b250400b1000844040104031000c036082d41001d001d100c580d540e0b4112000003484150003c500c3c10001e80c0d00c5913964000c0c01c501522174900b204e00ba0b400c5550821142428221 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 629347796 1250 629346546 629346563
    0x40c03151503050309040b04290a1518060806010f12060314060615031e0a1d06060f060408101a0307230607081605011b02060901060807050a061b 64
    0x71a0304015135217412010304148200e00300900c80c9028203060090400400240c004d0f20000030310007031440d440000202040750060340d2400d00090b2500c041c0c0700b4076800c203400c2e00c0b500511088042004e1364194240c0022041c8400c00c01405280d0b64002000d0942d4440303480e107500c41800c0d4141c00360140c1425070002e4001003500503840310620307004c5600c1c1c0c000c600c2114a40001c1d0075103400c0c2105400100c4103480700941428014103142059525650b0005802c000000c44c90540307c1d00c4009331401c20825116a4446410011281042500b6000001d800c41d0b0a6041a00e004011603842141110300100680c9804102d204200060195040c1000084c1070301d40c05500c4040c1c0900001c0b0101c1c2082554806100b28041401e1013422509210f401c103003064a050140b1051002080ea50350086810f5982c071000c4c00c40c0f1040b08941510b6000b469800f400790343c2041260a425900c990700800e100d40c211400c10461646ca44d91100200d034a141845c4100b01d8007540e85000180c24540064001c98 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 629349046 1250 629347796 629347799
    0x1090f080312090604030903060218040e030c012d0e0a2108071d040b01110d031a100207120606031502070213050c0301121b03050303100e040c031515 66
    0x80100c00340020b2958808403002603590103008540d92001514040d01003030040e0002d10104449030024a0139400ca4008403042c0502c200100e802c680c510b8224003020340004c00c0801220000780900012100f6001c51403c071851510207044011081d6520040219070b98280111407160502c400c00030550072510b0002e40711880b04a41e11064403070080000065626400103034207500a4102c50a040c8603820658040c41502c402e02004000781005e141c1800711800c00c5140701c0204002c0904e085130540c0d804200c04040710f0070714031100703420b074070107449018030003d0354001e15400503e400845042c0c11003901e240b6102e05180c2d00404039900080c21322038442e42d8840c0440581c2d0024401c6620a440c022485101420510201c54050320700700c1056208100400006022200b1f5402d058001c040404c400e40b0741d11001094000164011611074001004202003110b0403c0e000c0020b050107c0e80c0225458107a030b070000c0c100c5c41070000400c040510071070b84105130804e501444840c0c03e441311020703420f03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 629350296 1250 629349046 629349059
    0x80609011e03230d170f0603031902160b04180c0c05070f180911010509040e06010f05240706110c010905060609090f07090f020f18090606070b0703090201090f 70
    0x4400d86201c520184103543c106044544600480414060300e0042e017403880d202c0001030096402d01401c1c9980c184400d01c0325035031040e40c00310b02c21841c00c582d40061840c0405a10103455256a682c4400310584082c00104501d000e802c088181c168456500011140c103c440180c408501000700500306100b04940032414000300c101840965090310b400344013406103400464180c80745008003c0100b01480c956140c0c550007017000d80a18031004001043d040760056003d454042e00f640320110108204908026906103601d1034100100848244800b891808440c1300591003034400040006035a26840082c100d1185c09441c500741e244002802030242504203240d070b5240a9404920a903230703d0f030114901070000a0302c0d8984100d49405007040600d0000c0c100d0081c03040444007a1040d400f008180440000d81e002096460201c402120016401d038040c81050340b0014000d6005140810800d00494019100c0c154449107c0c6404102802c2e14070040b50390003030316441114900340140010810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 629351546 1250 629350296 629350343
    0x90216080c0304260c010e030709020f0306120d05040b0d090b07050304060c0e1023040f060e03150a0515031f0b09040305040303050705070e0109020c0c01080609011e03 74
    0xc0303411000204c191164445448100846507500c1c05920b680715680302c2040394040e40804c4000070004080e50121641c8200c403101740d900c52801c510300ca545c00030400100746000d035282c08220306048028500820070800c0a07049104030b00400310303010404170700903113040096003101040703640c000e02c840342c03508000b50003401030341081d90201c92140c01d2041400c84035100c2c407242c3c0b20750507008000c2642080c0ca030105517042103da2102444c0030540705c681010305042040208000e1000b00c1401c001c961500100420007541e03405900e00c20f400802904410190b403000c0c254019485010000f40c3d519582a40303c1a01c0191241c0d0350540542801c07110303002055190035944124214042c0f06586441082003072007141100d00601082041c0300501c0424843ca0240c16054800c0013201c61254846200002c030741c0f026448062051303000149050701076000d0003010a8074600303003440003c0b400c00344000342c0d40e49814081e42c40442a48000c003c9180100d944180003550440d81a84012481c103140e03150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 629352796 1250 629351546 629351549
    0x207030e040902060417030720090c070803010605030c09100e0117010305060406051f0b040501140c070515120c120f0106020c060d09080307020a110406030c090216080c0304 76
    0x4034005050240c90360074240210b03480b040e40205203920b00341c1003401250128000e1420355103130b41700c180003000c0041c1d01d20444180f22540c0c5543c0c04801c8070130b402000a40310008120410485043c4804000901982d06030b0b4195605810503646039075800c025414030f030090207001a444080701041c14481c5800c2221110154820390307819400746075407561650301000038072004111b41e20417000140444e5081c0e001c560800c050420f08401c502d036004401034568519049200d190100140c10411582c000c03103503018201d00500401e0602030907211090b160f01c5540301d400d0140d041031880091400400040b0b80d0a1115010918038504110203404525003004001880c071220000200b040d0004036010f107412108580d006011b910590428810f16030080341046c1000c1d42c0303031404400084c86207005184928103d07402010525002c0c103000f0150070240c1c03a0317580224a001800d00105007084400781c1a10344030000540e0b528852001041030a0807848082d02013440400d01450611001c0700800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 629354046 1250 629352796 629352803
    0x30f010e0108010621020d12050c0c1c0b0c0d020a0509040c11060a0b0d0c060f08060f06070314090616060506041a1905100903021c0b0f090a06020403060207 69
    0x22690781c8594206080b50703824090805ca01304540c40020442113031010104e07100b403000c1e102c40c250f229240e81c0c00d008111100410710100e90085034440084000700044800041d08031020145007110458980ca40b0440303800c0030b0320094509000510028070300d8211000408610011599011001e000034046d40005940c1813240e8200010001e5075407042441c405260091000f811545d124030400600600304d070300d01e9a40141140261001244084410740c0040c01551646104181e11400003480100002c064074440d5022000e2007140341c0b103080580702d100c1e51509244155205c1051554014001c100d070840d44400c0004020280725103006081048922548090110b501c0710070401083c1c84103406d0901c41d2502c2c21010582919080c065003120340d02002003a0100c5807100e000c10403803050001c0b00360226202103010011410018050030054641c240b00c00348501260740c4140d4402c6000d0a4421042c0d002000303d280754400b8041808040c0d4001411035680d40da80c5404070282d00628003c0c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 629355296 1250 629354046 629354069
    0x30203070e040b07050a020a0204020f0d0e120a0509010e04180b181011120106091d0f0601052208163c0e041a13030f0f0c08030f01 58
    0x191070041000001e0007150300c00300c800150b54a004085486401000301d80045108442d607030300258407144000d11a094a20189560300c2c0001c0701218243d0314140b003030902e0ba52000604e00c400e510324a042e1820030712146401599207007001c00480700300455000c0e85510610309800c02041502845417458402d204000c1e0100d00d50792100c582001c0741211b46010f0164000c150b1902d920345040d8000101031080010960078403201d12000314002200340c0090300894a041c400b4043c50610181c2c200140803220f48407142c40c60721740c80100042c0c02c06000b6506002c0046040d0706031034020b0013000b804080d0240c0369680c00c0c1d6550036903a0f40b80394114506001010301030003c1110903240056103d00703005400d00c0c40b80030590603170380c12014000400c40da0103c9510303200400d60b40c02c80c140740c43c040c0380249000134200241d0010720159402c0505075010300050200d126002070f0700f00c40310010000c400e0404080d02401140c2c1920f841c00c100b035005050041c00410091400c03203c5640134183d0341440741c030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 629356546 1250 629355296 629355299
    0x7030201050c03100b21150f03070501050d05040c12030c03090905040807020d1401061211090f0f0a2307091413020c1608030a0e0f091302010c081303020307 69
    0xa02c6900c0c8401e4600e01c40484250364140a110340f1900108582070340004180004440c200d03415040c00300903511081c00320850070030008240740500d4131300c910701000c401501e0340a10700700010b046c910031010501407041d12440014180400801440000c14a26814240c0b01c0d20a00e8010011100c4402c1180440c050407000b1800003002d1040c1441140c1c05140203160511a800f040380081c1d400000b182e01401040b00b4081c40002802420002c14042101000621a52600e81000c0c41c0d0110701d14028414802005802d100c00c47d0100e170000500f0581e1187c0c0d881c0d565641e40501189040d02204000513a421060441041e88040c854600e6503030381305020341c541280054030824405480e5112500710504084128980c0c01801e24110150481e0440c8046001d000c0e602e07a155807000e100c030380003c11a100103542000b1540501c000850f0f032810080501000580c100310003034840c0700c5404c004600d4404590042818080c0b0633000300b451501c6000050404d560b0000303a020407800390250010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 629357796 1250 629356546 629356561
    0xb1c0209040908040e01120c09020c2b08011e1a0403060c0809011805060c09030114090d0f020d05040303050d14161101090c060807090e24060a0f03050c1b030703020105 74
    0x1221303445a4400e54800225182441c90000f80d000040c0b400018080c0010341e000d03304001100705c02030114264400100d9210f5000540442c01c1648400d03400d9000040d400f40340310140c03042c501540c144030582100c1b4985840c031303414240101d0308001c000310b240822502d0081d811115081c4501e26010007804140f600d00c104014000e6420380040c041e034080c8001c50488108480900316980d4050000180030302e100c2c03085a840b02054801c480b130ba822256006600c281c0c0031480700c902d010603000600b142c10440100421911403440060300b0894042200d42c10042c1a800084a0030010511082a400c0003211100c04400d01c41d084d0011408007200c0c00f00041c018040c800c005034001c15000462850540c050b80d06010041016082050b481c102207501d0300b2018282d4007884d15400d1110802a440c810500c4c040c01500003248141400c0c094a07030383c1d5600c0b00444115610703034a030128032520780c0d00d002440c5018075140e084002c49242c01981440b040000070b0b09910340039500038400c0c0d485495 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 629359046 1250 629357796 629357819
    0x150d1a0a06020a0510050c2a010b010f020312070306090504050106060906020705060403080a110604060506011725091205010938041b0e19060b1c0209040908040e01 72
    0x3c40100240c10200c200540d42c02c00380e1110f58400703503400d16503181041c542c080021540614092003e4610520042c1c1c2c0c00300c009224944c1c0780c540a00300142c0b42c00c150700000e5568058400001580d00b02003000900141c4281c0144006000c444410b003e2030409191407400fa15250280100060019000144551000405604541c3e020348103d1a1070b045803220310040c1e00c600c11010500c0346051441203c900c04225961061780601000145030601c40d000400d03241000c4240ca14205000c414403202c3c41181c50b1450076060340741c62056052450000a0f60842e003107921158051400c40150001d00c5419003020360702c144102c420104840ca050120060341504690f100a124841c10004400894540c0550307001806041d003101040138100b9060343c1c0038036580048041120344010b03c04164280d1440c0300418800300781c140310707103030a00c6d440e80c030180102d02c0d00003480150710b81c80481080d815030460781c1400001d08144070440305814604031990061007840382a01b42e40b000086c2c82410032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 629360296 1250 629359046 629359063
    0x2a030f0712030e06160311010612210c02030601060302041a041a070501022703010b1f1d0307170d020c01022e0906050a0b01020109050c150d1a0a0602 66
    0x110100408001da03840031107003103600e41e819a4000008010700011a00310880049800e44070350f0b00c8a2003100420700c210b007035811f154814070941c0c1d20201c010001076411964801c003910610109401c080c104001180c078600315082c00380d0103000d40000030681a45c5a00280180c0c0c82991148124001d100310103101c0b07210300d2044450130300122001c003c2464110000f020b14500840c0090b041c0309411044001c180509450722500b81072071002079445080a0080f11060801215003000211300820b110300c06e03044495200b420000031a1000c08003140e841b91810a600000c0c080340d40040d150502000e082014060b42111889004050501c3c1d41c070000340074000d0841039010b0441500c0c042208400e58014648401c16941c0d026200341d0055070611601d041c450103900b0125060522618501c11103500c03158150441e410803201c1e801061000031a1205d0380305c15030b003001442003010407000d0203000d120040f1680a080c4001900d0700c0c0403152aa143c10101140c0b02a01d01d69500400d80ea00d0100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 629361546 1250 629360296 629360309
    0x50901080a08070302031b03070209130b041103150f070306050910030b07120e060126060f1806090705093403020c071d060f010c080702032a030f07 65
    0x1211420000380b105000341401e50320a0049a08044203111410b441a80000d0503851039440400c60300194a41503600035045a036014003900c10507441d44440c560f0f01c0707004001510044c80144071035a1600e042003207011084520720f402140e41041c0786801e01414045d2400030020f81401d00c086410b10b0200581800f41c00f0320041c45580034070303640e100f20640c0710040001d070a020100c036042c1c0c00c420303079409003c0c0c580000c2d00141203190b0402d01005401c07824000c28003102c1c8000103102d18550b0002070030f80c0d08501c004098000580c2c1e200c00c8800641d0000082c071170700740140014030000000c00100f80c000d036403048803242c00e2039907080300e44a000407249051f4081c9000f05138400c2c40101c58442d07034002d54800c3c0c0c940585000c001ca0340e01450145168400325041541d5020310402031604c0300090382040040f0707030a1340ca000c0c00070b000820200300c2590180c125200041c403072086507410024280c0030402e4512040c15444111080380e0401d5410f807135180a40280d284401d850840072030120b0503a0071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 629362796 1250 629361546 629361553
    0xe0601030b01021018080703020d09081b060c030d0216050c040b0d020405060d02041e060902090102060f130c0308030402010e042706150b030117030403050606010c060f0903120605090108 82
    0xc841d001d40000c2c0164090103080d0f03001a05e03448001c80c0c0e8100041248501940040c85802c0005100920143c1180e2007100c21b6004003582ca2044031141852101035082200d00a4480c810004040d00354480d040c02040110310000f9010300e00c2b19042c01910341940102d080d00c50011020041c0003d035018401003991010b1080c40302001450264441600800e000c0e0801304415084d5000c5401c0ba1082c8440343d032489800905904914581e004a002926183c00d081d07040845100010b503071248003404440c0205420307400500302c3da840a120703e5000360000301407002c0a90f60f003080b240355802900c050740001c412000c4045a810503000d080340c0b402e14024254540e1800500110310380303030008003ca8a1030344402c05420f00c141011702c214007818050318055030f84d5242000c4414044ca402d400502079030000d01c030401c04144003080303841d8080c07020708088684c10024601400203040b2071120105d5640741074145000c7c540d02c01900f000c1c0a1640310304000312500c807020010051002d1103011250750 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 629364046 1250 629362796 629362813
    0x3050d080c0d0f090b0c0301090e0f1c110709061401080402090708090a0506010e06010e09150907210b090108190f03090807030305120a0605130e12070c0e0601030b0102 74
    0x1041c42c0d101c0c0841150300701c000610031050350b0385c0c456042820740760140d01050100051181c0101d600c00c944810620b00700401035400c0c3c0c4003502d900d038284008015100081c110100daa1103004882c18000902c000b010744407584d0301d4000d008020001e80c040c00c4904040030310581070550040d400d49025a800500c004030540d0780000485810f48000c00340e41281c01178205090000e081008403034040d1481c1190000e2a00d003d000051800041d6a15640305480210a1000041c01c85003210200e210640e40c0c0801595548401e8074000840b42e00d004e28100001c2c2620950350b080d9103c0d10500508443c4404184d0b6201459036075080240c03000e44000b019a0145c400055081200c1140b0b20b100b802d003040c201c2d13980e003442810115950f04c00d80108100281220040c0d01c80d101c200d6100341708900c10002030741010017194041c489c15047c00009a03498140c0c44039620100054110400181c9001d0740e00c003140d1801da00ba220b1300f4404d040c90b40c0d25075004200150b0290056019003801a4001c01940 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 629365296 1250 629364046 629364067
    0x602060405162103050904150503060a02030705030f04080f0319050109020f0d0f0608030c0307060c0c1e15050c070302010b0f1513091d100b0603070c0c0503030d0603050d080c 77
    0x215010004900341300c030810115100740ca490080a5900d81000c0c2315030807030380c503240074107003482d400030010301d4007d104108000d1059048010741c1d801c03140160040c11241e850345040c2c5640e200b15201a00c00e00d1b404810010040c5425090b042a54a244402d00c002d0740d03070351000b601741e003c4c0d5280442079101c140304502411345590301c02c103a0903c822001161707181d5141ea9042c1198080d0001a0158000180d40d8003441072501406044103400c0c90007445a540302c0e00d034503c1c1980d10203483c8049009610b440c106024201d1080c1043c410815010400c0741030000b40b9881c507500202d002c4001d5401c107241402d147c6005405041c401d28050004c0400f09a0005030700b103168004020404110b05120300840e4012044c0304480d00246c10b07a00c7d5002e02440002c460740f40006003600040710b07a0a03c14a602180c940e40c0a030703034200d2110b041074003030084185080011071507190401c5030144408100c2600617070043c2c1058045902903003e40e0020b205050040311400c408940603454540300700581a0304c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 629366546 1250 629365296 629365349
    0x601140d060e0703020a14030a030e04090605151804050601060f14030424052404200d060e010f060e040605040c120606030b1c020a03020604060206040516 68
    0xa44800a00080c4004425078440080b11550400110154410300f420310071420000c000c00f010b05070000000302e2820502c0b000981d40c0d075803414000d00704040303a0180c1115843c3c0d40c00005106501910902c02e5240c000e81e40b04a4503090840b0501c00d403044502181010300110090340165008005400c0507802c0480c103841800084105000700018410100c01c58000c6c0c4c00031f5802244120403516580031581d035080f013501d2080c0d005182840c900414031050000365007200e104812103e908146000a50000600505141c1c244803940e8988114280603100044000d004441c40c0041c1042555101e10308000c80c40c0e001d0042503882c5100040500c24940900d010341d020f148018800300d00c1c40e8550b00428180d6013038078026030100724001e02022030b004076805414043e0409103410810003402100180751305404980585070010300d41c3d0035205645036031a000c0081d54000e8515036480d80e032210300a59a0804590580e2980600001d8200c0d443c1d4848814040f41d000b03203402d901c114001810900d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 629367796 1250 629366546 629366579
    0x1003020f07140c0310050703062c040305040504060e09010e0d0c2a09090606061b030518061c050f040f230f0a0203010e03040b0f030c070b190e070303020601 69
    0x740f040742d0280600396000c005c5100c40c80a0058007080e20309001d580502074443d150001e030011030090320301e0241c98120004c80041200303205021540c94686040a4031541708680180382c01908141c2e02003100d007100b1550b03e000b82e5647e030081005942da108460780b40c2c42c1c0000e8982c00a102080c14501180709120783c10100400d0400c1000c1000c9026100e84590040e070f03100400031512203030008140b0000c4e100e141c0050010f81040a0700ca020100c4142c00301c0c103100d800409020300412001c219402044450160f070700007408403565018440080c10b90b00084400b03400045082c02d0000b8004445044c58a005981c0908041e101d203081c0c5c1c3da07070344505541c041451080407803145400f481410810845a0320343c0000041c0443c2d03520750041c1404e542c1480c4000e600307a8010030081001290b588104d4030180308000895490752960003510126100e00c51024041ca14a04c0a00c014046040030301140040e440d04100300302d490030054140c50b480c40b44806005600a40c00412052803954100700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 629369046 1250 629367796 629367833
    0x1093602090303041202010f03060f060f050c01020705160b0f0d0203090307020432060d0204021b03040f150c020f01181707030507081f0902060d18021003020f07 71
    0x141018041c00c0440d2464100703a00600b4a001e800c455030040d540c02c4201410348404524080c401141462040100003809200c0c01042089101145604510983c244c0b0428503041e002555290312900b00369550301d074030f200c0d2407046001c41b290000d9180d031610200c1c5c1c40c0024098041d8100100000c140c002508020310b000c17228081080040b00680c1d40e441814602c02500340d401c49060300741d42c581004683c140b03c080604228690074050030b9a10b081d42500da581d8122005a5200c030808600c1d07030009041c0d40c1c018a44d01c404103012440200400303059080d1805004012159402c00c10101c03544d0450b0340c0c000c0e402180028101c080c2d940704d50400c0040c6500c0118030314030345644460040281c0c0c0c00342a04191908080001d008010f4107008520050015000a0020090711040107110305031020310402051b540f240402c0031901c4800543d089904880300030010301318902011140c441030302004030302c03031415281e00d4075240e8001d200380e403c240f6151011274201207541d580c01152207403110b2400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 629370296 1250 629369046 629369051
    0x3060b1201141807090602060c070507030f0204021b0a02010e0a0509060918070602060f011401080a02070c09090809040f051b0304020303040305060702030a11120f0a1202041202010936 81
    0x1e0143d4103c0360054041d040f241d444420042c904400207007024809008004102002c100000200e44001001c1d001d1325000544504424058400100248144106045a0280d03910b025041000126080070101d000380c96041c00004020f04101c1440200c0c01500d41c002d610718046010783c100680c7c0668013414081c4050380b05814408520300d803010b103034441310059022004101030768810b1580e450040140655060740005610000b80103000c00030320044205a001c00c004003031014000120000780070480e4100800003090501146a038403894030746000e181440c414051149641c41420302c18084400021002c070f4407509400020790010b00180da2510081c4808030100c2c2c001d1014034094a920740003140e6450603090007500540d0319204480042d04240c01c0c0d4901141e41000b01c0352109a02540700b99500c0c141c2d0b4003079503250102401b500c003480c4045004540c020020b400380e8041c5000f44c80d404111541c50720300e0000c0900c10649004101c41c00b00c95095694001c22481c0302075040000007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 629371546 1250 629370296 629370319
    0x3081e0f1602100e011a0306010b1e1312050123070c0203101119050913020a021608060912090a0909032a030809031216091d0703060b120114 62
    0x2072410380d0060f00c2004032596440709800c03c41d04506c140c650030810141c01070503ca624204070070b0b08601500c040300c00700565004000605902d05002c9554160100e182c024109072603100c1544001007200040b20b00351f103085420b01c00c2e06500d5a56a4200100103120250b95403070420465514103100d800b245c041c891b21200d03a03119210f500440403141c071001400703a185c6090840e88004c0d031070014411800e00c6001c001031281910754041c103a01c1d2181c807401c090b03a00c1101002c120319001080b03500300c90396081c456001c10843d0300801c05902805028003140d00c0345010100000d4981300d900d90701a8002c8962408000b030801c581c000034841d50090400a5003030545a4106c03041c028141000c5020000e4503085104140e042001c0701c0d000b140a00046003402d4a64110030114900a00000390072402024802d400781d11543c504000b401903070740512900c01000c030494a06407015604640468100a07010492104c0d1205540c3e08e0301521040c1c045d107904c0c26291000e800c24500c0c0c119004403000c1c3d507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 629372796 1250 629371546 629371573
    0xb03070b0c0a0506090a02030d0c050601051c0209070305040309060f080112110d0326131407090e0c10020c03060103060b013b04050108030a120b0d03081e0f1602 71
    0x904c510801444018040005d40c510416042100d01e030440780c10304c021030308400d0200d040002c3c60341c1942c005841980b01030140c2c4c507000b86110200072000358020201e03020450a1641504100e01942c403e880c0e0880490f100e042c1078610310341c0c0b080307c4c40001d54614010030649000c1380511100d41d0103081c4a446121101000c2220903a02202c00c1d40825080d100c4203a81880000c0e19402c1c8484500a0f008141852100b150111007003901c0a0101d002420a000c0215410b01c0580010941d10104000101400e04025140ca02008080344a00b400300080f025442c00400c4d0000200401405495aa801c6030f072840001c00410807030604104c15884123412488103001c51b0000c0c940b4020741200d07107140c05051100d90581040c400c5001c0c505050040207950f03000410b5800d80a00b41c00c19000080709600c1d0000102106203d0071380c445914410a0241500540032501500b107120045400883c0144505220350301903131544001c0f03c2a00000e00b495481c0c0c22407444402061040d107003a50145030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 629374046 1250 629372796 629372803
    0xb040506091c0c030b040312022a0c032d060f0f1b0418050a090507062102030c03040b09120301050d02010e0406030309090606030e03043c050907030b03070b0c0a05 72
    0x800444000b00040c050009248d009a00d0a0711049110800c6d0720f003441c124045045410110003061f98020180404107070004140020b42c85400d02030300b15018000803200782c0d982c000c16110f5018034800d211200c81041d81000c80c14a01c15458030340701540399140d002e01300400c203000501c110080d44d85d003d103c102c00b0f03000e500180010a50040789507084a04003a4000480e00041c2c00c044a80d880c050303905001810104d1060308a60860910080f0070060040740782c41a0807800e0b200305540c1c400420400084800702c00b0754021030007682d02014994902034496550f0307070342c400f00b11600b04051004000303900c1d01d03c6100b15154030600d44444110044c0c0046801e40d1282d800450215486c01c0050041007114400c070001040240b5013440000b071600d000c01d4692060f4010044419110820b00208910b90101c0065603c503154008203c503011814215498140340a003078454100400481e02d2a8424040c020f480040180a821454500005a80341d507000d81d0361150140590f012183c0071a8090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 629375296 1250 629374046 629374049
    0xc0807060e06060a08190b07030605091f05060a1d0d0b0a050103050d020d051c02040824010e0103050c040e010b04060603050103050c010930020603090c0a0b040506091c0c 75
    0x3400104142d00300f28080200c00c44450b003003022568020100c01c140d981d440c0c01c0c0070751501d030046d00b11211074994140031000741c2038940200381c12140308014010070010302d00380361001410280c206800345845900f00104d0b80310b02111500011215046910480c0c220007619800c604002e012940042980d51885441d02049a2600b11981e44070010010f0200038407440c40f245901e032001c0c1201c9800070101074068059442c0350a48680c2c040100c806d84036456044801505113401100d03018503000d107c2c0f0700c1c1048140605041846d140f000001c19200c3c42079000c2c140c2e07038490090000c1421030010b200040c198410582c807d5901c0348202903594490748124806010345650214944d07041d8141989000d05440120b81082611001000718004203145d004800340760040e0614990703c10040c60b05090302c410b030301075440140001401a14840000e1228800e1400da503000d078440c3e5540302c1380c031460084c1d108050300301c142080340c41128a0012003090800782e84140c0107880d91400e03150006480c16a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 629376546 1250 629375296 629375321
    0xf0815010309120509040f020306060f03040f0236070903060207110402030a06051c0305040515070803070504060810060f0c0602041823040519060f0c0207150201050f0402010c080706 80
    0x14445c000e800c1a014900700900c0c800820752441c00c080010a111340305601041d48070350400310100e020045180600391340d040d0002c06500185400d801c1d63b000e441c0119805d24500d0890345411402a81945a664461100c648030341c847c1ca890358896802a600c03940007114800304281c0390100544d11880030314003400c3c20610000300e180c180310034004801d01810102250b201c203000d42c400025072120841d02030365401ea4240c03440350b0040446a00f540500c11000f48001004800c04c20604e074023001a01c12903c0d29610078100e80c4a4080d03002c004259400340900040580613a090258003c1141c804002c1c070030f01d0018945a5220300540c40311680c0c0d042401d95035100c103c42010002411902c49902c81c4513414000070b410680d6032140e0352240c040307144a202c030303d42d80600300b030040a40c000500b03440c600d641840404902ea13030080d220041c901a004c50000c40c43d105a4030684144105885002c2d880c00c803075440d0300d40d900107680d030614141040ba80d128041202e00001150781c0100d400310100d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 629377796 1250 629376546 629376557
    0x5011b020d030f02030609011401050415030c0306050105120c1606090803011e1809080f0706151706010504050c0f0403030e01081303020604060507020325020901060f081501030912 79
    0xd0341c00d0300505540c80c004608445074014418030841b9964100010b044a0300d841030302d4181e100d4500183d170640107503032104400030088500b00300c003a034064100d042c506c042603804200090b00c0c3c1d4010f40b040e004150301c800c81e001d8484d00099100741b010300100241d10041d182c4910000203036031001d0039075082402c102c07101c200c084010010003501c81004811005903400110300c0c41d081c62000341100a10786400c40c2d5203520743c0d28a40a118004040700c032040d4691945940d201c0352030070101c010b8561810343d000c94100000c4001039140611100f00752840f9400c01401d061391038402004080d00028005410900c02003212161980e10b0741c00030320055100c2d031551654080d90030005006414010800d9040030b801c81c03c80d00000f640411a15031150380203400103016160100700f20700e18028401000c50008000c3c504500405848001340d43c01c500c215808480c507a02d881d421201c070200200780e1004280d60b2404294110006041042d907480189000076103000b4036120420420b0640c203580001c6072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 629379046 1250 629377796 629377813
    0x203072715051b010207020607060b0d060203090c091518090309030106320109090203070c14011d01020922091209081009030e041e14091902030c04050405011b02 71
    0x10803070141e03d01c035544010086050004540203d0301c941301d200c400902d010f40e180803500403a61b80c5038040070b131076410500854991600128142d550142206168400e00b003540000d140c1914280d841684204040e000c07000400c9402c484401c007820281001c00ea40c00207004140030342e1000d1049800610742d004203804488800c00e4810318401c80f04030ba00c0c1c0804410003403c0c5481c0d070014881403c54825040050f926550301000b201c022040e0f000041041c0b0a040780d4200c1f000054000e841601c042e2940701c00f000c0075181311503080388200318403e50414003510074a4881999680101030140b01e081010031012019510503245110303610010b00420022a0244140042000032001010010500300201116030310081e010b0044e21455503c100d46800241550040c0c0114017080001594410b10044030f4208015001360130485204000b03104954514800c0b5021500804c00300c1c1d0081d0180c240444c0310410701c0007800e00100142d4040d2b480d00188542c00491203034121144025038090020318 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 629380296 1250 629379046 629379067
    0x504050c10080408040e090a020301151a0c06040b061c03080f07020312010504111b072108030105010c030306150c02010f0e2d090a0212060103020307271505 69
    0x80059041c06003005200350070440000c43c180c0882c1c09031100020784150503550600030300d14003032500900a4040d401c1401c0e142000080700d5482c0f0558240c0c00504000128180038007400d4002c40300e1141056000b500800d011841070410581c0003040901454284c0c0d08000c030742c0c0c01c0401c3c1090102c0c0014440c00400c0003040710940c003682c11030080d1015620b031143d0042207448220341170150342d10440d40d448c070780101d5028050480d82d1401e00c824003c0d280d80a1040348035180c2449102c0c6580c0301b02c40700c1140820726070062614074565030042e0264156400d00d030045420140700d041c11810b041d0f44001c0400d411000700c5005801152903075908041d0346151000402d081600102d00b070901601e1110b180d61a611021341202d25494000140d888030a400020083c440c158805690064144014002a40c4454005080c0f40341158400d0410392a40f0004508900c070854025000450210900070645580c005615004040480100c02e140d2190944c0c130100201c856800e010840014206002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 629381546 1250 629380296 629380309
    0xa0b060417060c1207030b240d050604091707081b0c0117160509060415081b03010e07052101140f0a03050c130f0c030c0e040c0e0d06020702040504050c 67
    0x140202c03582003031401c01e84013401600160805d028940c4801400501d0b444500354606107242030b900700b4103068107800d0b140007140d000f080008141030500d00003031210300301070040d000125444040940030205281c00c5c5501c4e900000b83c04c03a0605010404c558030341000084450101b0190b002400c1860404070025080c11040d00d19580404000c2e0700f04401c04400264040755200c1c2401c100781c2c0e601d02c6000203491480349803c0358244040c1114407210950784180d19501c42c11ba00a00f01d080208444000d10450009109088055030400001422280700f1405080d00541c405201e071128003205034140c8251030260050045030003101000e41051601c00450f400616098400040003411900c6042c0c54001004c0e05602510072080c40c210300c120b4990058202c800540c01c100809210540c1c028083e200002e800c100140c41700c91080402e2a2500c610011a01c09480d4040c1280000c0b06000044083d90003c1e100729900b40600b0300540c94a0190b184075911480140c5840341281081203071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 629382796 1250 629381546 629381551
    0x5031c0b0d0203100209030a060e0a0c0803030c04060f3f060b0906090111010905070504060e1611070b03131403270a050d03030c020609030a0e06030a0b06041706 71
    0x208035070700000940982c40c00b158000d4144007045016035506000e01c0400d01d0000300c1d1200900d1649804402162050080351801c580c5200315040225542d82d002461340d0307400152401d00400c00100f00070049140030781f00d0318003280c1a60500741d0210035440440c0c150710000c03510300064090b02c030b030345000c010b2240c9041103c24000c040c401c2108030b04001c200390040c0543e50025010b030100103201000303a8059a4007200c1407030003030001e00c070031209032a00d2074130f0f0000ca101c0c3c540594246007002c19481c01d054091403040051204140c10207508120440300c000a0b100300819a00580c3c001290850845004510074400d0381140380e111202d6280a094404100c3d09031401e940060040105502092413100031096540040c2c903440407140d000079090b140246d10566001400c620380004040d090341145105007100d4003074078001d07503074421042d031031f03200301da182d0000540e102c2c040031110f245c040060368104a5401002661416035404111036900a8019238503e283c070b00324a0192490402400d0f6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 629384046 1250 629382796 629382799
    0x20c010c110a2f1306090f2f1b0105100f08030a0521180c03060105010c02042426030421030e03010c0c02090117121605031c0b 56
    0x141031140c1d40c0303582c210340c20266108070728001c55486907005146407502004507403000604d6a903031901c41c0c0c02c1200003851248580c81610b810264601b465070107500c9481a0402c407290440c0420350040082d0340b4200240891581106081c041d010340c1350049071141664840d07960002485040c45069010300c03c080758081e100752000d0142c14050a0000f00c140d0300d05019a00b805912140209080306104016025065030031034400b040020030382c0b00000d0680d41002c1e42c410380f000c8000074400c3c182c5170305003400b400b4007103009031560400506103a4402c1541c804101e80440413541420240344000b070955111419204d042352082c2c00940c080e0400c2c00c50028408020b524051400200c0042c140d40611348682041038001c041081c140a40345490082d10010020801031540840140042c209114240d005a141a00104140e594400040780011a0b00010f02d05c8960b0804440700381d600105070f013203900e12000c03c0d11000800c20801307800e0520642d140000d10181c1c010000e02120721050307489 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 629385296 1250 629384046 629384053
    0xc0c020a15050901050a02010609020d090b16020d1d0a08031b062211150301091518150e01090f0b041b05031e090607020706211509020c010c11 63
    0x481035600b110803900003d0003802c0c00c6032165040f0303100b42c1c0144540d610080c403d50000641c2c03002c545045c0c2c00242d04500c01d8411502a0719048644525030422400d41400359002d000f4140056028450b01081000400580107040e0318050100740e804010b58010440340d40b0108800080e0005051a205101c814200401c0c0701d05d009440c0310540b40f28605011083e42e111a105418440903090020448002a10a0303d6501c0040210b040941c4240709040386285441c0f103a40e40e5140c160100800c0f1080203040041210000c02188010f02151010394244600d0300c0c00014890509805a4000c007503640001800b0202e540105003910440141c1601c5146003441e4070300c0b80520000780c904010703142c1c50070725280d42e521500030410b5641c50880320740c80c000000c208203450034001242441380e0310640c00c1d01c5030643c0d51002030b51100c0ca01c0e5a00166001c0b03401602c1000d40780c5a1103000003034904100c0c5544c00b13940d904900300301d0340318480d0600d16945812038820525000002050041c0419009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 629386546 1250 629385296 629385329
    0x2622020d050304300f020402040905090a200108150f09090307060f0e031911030c0c0f030a0f060513020409060b0907020c031e120a0801060815090f0405100c0c020a 72
    0x6140820f042003030041c100e420711104170042d511981c0c10f44020740001c03002001141482106e4135610812540129041d40d404540400264440300c00c0f10520b240607140c901c05901c0e4004184455840350b0039058104400740c00c0c201e4181d640310f1001c0d000300c2c1008040c6913a00700c1804c110007034600c090702c0e03180d40d20305100b200e11003150004111011030134406100b0040311500b840440d840d820500d00c04509200102d400c2c0074800c00844c442d102d003001183d449514014180034140c403040b1040c00901061144614a00032441a0300840e502c00a40005440700d079842e80d000a04507600d03030000340e960540d0b84089041c142444032003a42c000015000400201645000003684c83c518019100030803901c0221511030440304001e0760000405500d42c0303c0d101c8805c290014441c440910542c4002010000440d805050b1805008184040541004403540c0c1d03d110811150030040c0c400c4407144145800406180101d00c283da00c004c0441e81c2d001d01108140c0100001d02d1203d03009041d900c0a00c042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 629387796 1250 629386546 629386619
    0x3010204050901060f030e0f0d080916030f03050f030a0203150109080c120a02180f010e0c04120516030b0a06060509030c1903050609010c2622020d050304 68
    0x40c10741184c081d89851120090b01c1d0358114060004429010740301d1240d1548000c0204001c07981c075402c05400da46010642d561104084e940b110740102401180640c07007400d002140ea0b0100640307145000c2c1c1031003484c08007113015000890f07008480c6800d21950100c00d2018803e038054007035003144130920345003030201d06140c80701b82c8034150445010301c201e00d0510780300c0d010340050001480b203580007004510380d2180c0762608202030b89d0884509400b807110b5000480d081d00c2200006000d00015807032242403c0c100b0245000d009803603031b41902c03d1f208440403030300c0300c2c620382110344084c42c415070002c1c0081c24422085820390341140c00c810240401801f0040258a00003a40c11149204542004038804c1002e4035540502c82c1c8d4002500d0790103510104481100c054100f9a4000c501e80d54a101c2d00303e40c00300c4400c503600882503548081407100046248440300303503189020b148111540005c1c00b9510b41c00941c070000c1e190030071515504089001c0100842e2422092410030b50f06568010b203000110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 629389046 1250 629387796 629387809
    0x1203121a06160c0306090506130302030405060f0d0f09020f101d010e0904060e120a1706030c0a0306060302190b07140a0b0a240f210209040b04030801050301020405 72
    0x9850060300c0109400c4954080410940c502d207800a19410f5800d440c0c2c102600034044d102d509650a1003110045407500e5051209812801c0d015400341d401c0038200307001c00c01d0692246203c070265403010700ca0591400b00070f205803641044d20041c001141c0650381f0601c071180c0fa40351341041c400c20103032608a07200e64000c1000e05c283c00034030030700100c0c1c4031120380107a6a048145002c1c9400079450810001009419444020b00240d0081100d04215020422110078407a0003403801c0001d54400b907402404c0301e1407140c03a030420030003010380c4c2c1c4032691140450301c88001503100750b0387c4a458078020015070078542c94000000c0440084051140c0c2031804181e614810010003e103559428070002d40c50100c00c0c440301d51410352001d6900380038180107100c00080d0510910000600c60194648400101e03503a040a048491000804440700d02e803255a2540e00840b220b0480c04d5001c1201001c0140c1d2801c1c200d40c40740d8880c0030788031100e00301424000e2070f04005801260190788104000c1c0496503518 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 629390296 1250 629389046 629389091
    0xc03010e0607210e0109200402070210030906240f05100203160c0f180e06040507051c0605040b3106050c13060f02160f0627120312 58
    0x190074030300d40c164201c044403008011008088200b0752078080c0100c108007c112240750300360036441c02c0403045400c100801040380700d07605000307500c408007440303000c5041d000b90030441d4a01d005210014800380760005511100100600303520424075250300030301c80487d00c2ea1802001e00750903a004c0c1040c00684002a40c0d0384103880a605040b20580713080420044001e55140180040c003411140d40f580d5070100000701540c40310000005420b05944143c5098002421480359400c10001c0c0001d918200500003400c82c44002d04025408000c0511b001c2910740c0599400f903841020300d10b40500c0c2030b104200c8001041e601c4100d50844d010102403005000d40c0c108481c80c0d0308490001041d8403030781c0382e00b0017503c03401005d100c5200c0301980c00220360f038005a480d6900a500e03000e42d10640340c407040e84071410340705000d444003220071040b06118043c46111080075070f00074001d6411421384250b2003154500155031001546003c080700040c201a0f00180881f81d80000d4001485400d014090089526102 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 629391546 1250 629390296 629390327
    0x305180601030812100b0f040504180b0f09031e0c0715170a09061e0b04110403110103021204050d0f05190c060b10020307060501051c0f02010905120c03010e0607 71
    0x20f00041200410860044001004011b801a56415082c11400100c3c0c02070710440713101e18a000340109400d038456601906480e400010380ca180d958242034002000750150450001c1e00c001c0c4600c407041041801e14184075580c046015464648100a107460803800303030048000c5855032980b101500307410107031807840e1019034044002e46030b40c1d20b518600108090000909001d003440c05002c0c03500c112001d4030045100c2c4c880180004108002440262400303110b8101c801f41c010002040410884445007001850514002d40781c5400b0b2500080302c1c00082d103080c0c405070098a55816090341020403480402d50a00b40b0130b042040050003022071041d00715020041c00200300301d47c002c00041381d1112280c0280100801c060310f0101c035000f580d0303410880e412186503207010000b10b020718000c00340c030509031741171170084d02c00020700d61b9804615180340c442241405030054010400fa9100500e11003035130118001030900514120802d400c0d80c50480c0c000c0c219800810600c5100307540b055085070b00d10f81 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 629392796 1250 629391546 629391577
    0xd140901200306181f05030d02072304110324010f0c051e0d021902030601061d31060608160519020a02011101050f040609050c090703051806010308 65
    0x644a01243c1c3c3d020684030b0941c44ea604000420515801c41800e0403c4280003521441000d41c4580605070340c1c0346e445c3d0900002d41c0c820082000041c4070030700884441e401520508820001071004902516071001c82624511340100c02c0002c102e1404a00d402902c60101c0800015050100040c1c43e41c203c4154603030170041c6064001c018040e08014509144444036281c00301012801d230f0950320703000c0e03407411003006000d06005410a04151005013a5880e00203014008607480c06a0644103e8140b1140384468410030a0400a9a071000c201018850074070791100460242c1200a007002c44980c802c500f480e82c0717403100a001c080e500004066001c000441c1c840c5060404000544140c060640c40000c000c645074240c4001c15408101ea204081c030030381b146440c10f04510185404c3c0c0d034048991980d8080220005404104550414140c041c000d4099a1381703d003460b400306a407100120b8410313000c0f03900e680610a6160181c801c0000071900e6002400c4c007541950342d481400d20510503414460313070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 629394046 1250 629392796 629392801
    0x506340308100f09230702060702010c0c0c0b1308030403050c0406170d050a0e06070f110108040519030c060c0207030b150a050d060212070206040c061b1203020d020d1409012003 78
    0x1720307040c00110048117030080c00c2d00e61812101c000c0d9200760480719a8019403c08088801c1c20b0301a080e103004480d40000301612031810f0950760103050308035060351100b4039003511001070fa005041c001080a14041c401804100b0b207004248400e0382d26660160201c00d1026200c1c0d24400e0003c0740c01c0c4180781f2103260090b0b1b21465510111600c3d003a060200781d0006001500344104002c030321036000c90301e1090760a01c2100c00c20200565a40a0865002d48160489100e03000b86403501181140d0151183c20310700c1c085500350322210103c440418203040580d0041e80227105100460000c03d40c0035981d00440301d000d070118004160214240c1c460740d4000c00803200800200059a0151211046241d54070615846c00c0031000f50f9a4409540a49010480036000b0400300d104240d0040350502360720402d41d00004d00c0e510f003d0424a0201810304050b030a0101510b0000680010455240c0c004000300d0089a2140070000000300a03003022080d030314260920441c002601410502254200e2080c0e8590b03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 629395296 1250 629394046 629394071
    0x708240f0109170102030105030f0307120e0315070503090705030d09090f0603080705060712050f07050a14040605041410140d0b040204180f050609010506340308100f09 74
    0x11100c0390484058154a001943c0e50144150701650498500700c1c22107004800c100c00c041d8591180a901030000500da41840000d20f0040c03154615801010723040310a207003500000540005001e0303030300d8000100000180040d81c05e0820401025000c04c401410f074901c00200c0280030302e81c19104642000b0f80360090300e8855105a0b210000070b54001421995805551401070b84540c1d0440310107001c5699214405803c24aa20403a84140940420030b03d143c0c907240419200354000d1240d5404001100c2c80f141c0450019601801c001d00071610b80503211824816244800265220528010702c0c49244038650187d0040c0d0860403000b9082026aa0391044c00200020380070a00c0c46035041400040c00160034202001000308066425008001d0700d807400c03824000f542c03829034405a00011a400511030b07840c00400909152900c0302000e400420340c7c01c40f90308400f0b031a122840451100340c03002400d16030855829a80034404424000406060018402d46602e00d4040c0d4010995a0700d500b8560 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 629396546 1250 629395296 629395307
    0x51204082a100b01021f02221a180d1115070804050103090f0f11150705070e0606210f0f0f0406020703050702090a27020d020904030e12060708240f01 66
    0x110f9002851042c3c1b0081301c0c01e41c0c1d02c042d5004690681d005040c0000210300b0f261140d01540640e901c182e0030700c400b103c0510b074110054200a072215580c50b0004900c0d9916528812032556440c490100b094564800c08204031091495410903d02a201000084001504241203505503082401d0006442c015400c2220f807000d0341c86d10081c103c464034036001003404580300e0000e0000000701c1e07003041c0141c681040240d1900558400403d0b9a2104a0920908c103c6140181e44810080e000742d080c01150300020100e0042c0501540c90006d64405101d140d0b01c0000b4070a0340720303680384a07040303d90a100c0c140a41012008001400182d40807524804051040b0708807a240c640003408040d040c03c040d9415030060240f00e540c0c50421454110080c0e00c00b02c4413065201e41500180015409200340d024003c000200070000c40401c14007603103901c0c0030741e03501505071100500c050050074185046070300035240c0701e005403079a03005910500441003940f045504a5200340e4050765800c0e40c50000d8001600c0303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 629397796 1250 629396546 629396563
    0x10510020f070303020c040b010f0210091707080c0c0a2d0b040e060406090e0d030b03120313120e0d02041a04050106020f071a0316051204082a100b0102 67
    0x11103000d8100000f0078580e00094116041c4811074041003031100e10740041d545640d03075401640240e04500b64a68000d00c0300c2c0d2054182c107000c1c982085e12956062214a0325502c01d1104a800e02804180301c500e100c010020060004010703a0780055050410541140c078212001251418040416240d81e5040c9030908583c0104094810540c94540700c01d84083c0c00c90702101d40c42e025034500040011042400d01034000b0081c0007074041c0c030b042d901072113040b000b4200d01704c450703070f0507100f03440700550042c00000045102d03a41805c100010720030503103001c0c419403204c0c2d1808400c022480c608003da0b9500d0f800203c03001030f4119400502541a070b040e15440000c807220a680c05443c04000250594002c1a1501800041404d4400e140c0c1c541c03152080514159010310310320b40c4248000f85208200103001043c40c006c0c0d00f44182060700000081501c014100c40071160801c010420710502e901d414840f9001c0c0729088002000c00c08440c4800741d030360540d210411242c0b51038500c0c0850300d034001d103c6a00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 629399046 1250 629397796 629397823
    0x161202070f0b0603120d0b0d02300c01090e130c0f06090b040e04110d0807063c0b010e0d0f050607090605040e06012007171501051002 59
    0x1500d40c505070500c6904000d03144000c2d41d0240d140d01c005100781c41e01290b101a59040109420304004071101380c5802031200d8400d45420080b5422440056928000c03000301c10b0a05820701c1400c4180210142e4811503c0042001d05503c4480c02150070b030b0f00b1043c038905030340701d401d65807401d0359503c0c007029568201c201028000e181d24000114800030151003400036100191500740e0f0759507031012215124801c601c5408132040c00500460002141494102c40e8078800a00c3c8800442080e2500320b01035101a0080780d1080d544c540644100401e038040c14041d0011850403101c850b50200580c403e00002e0940d206840c0e65680a400240c6c05418041c58107100640708032019546442d00001c5442c02280c00e42d206c3c070030580007404051003881800251210f95131418113251815582107004ca9015148a041c4500f4480100401007030340c1601d03058000200c010840c1c00d2900010001c41c8a0300321081d8490b070001c2c440f8480c201e4401a038241100c0b070640c0c0344485400c000c10200c0c20440d5a01161 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 629400296 1250 629399046 629399051
    0x1109040b0417070f08030604090803010902090307060306271b0215090606060d0e0c09160806091b0d0e0d0908010c0804150507030b040c02070e0f0f1612 67
    0x841840645048148290311034100c0711038042070040070185034094000000c112800b0000f02000048201000d15013000700034101041540c4c0a0b0744079a450f800c03d80012030100e0b40800c024503030b0300d410001c0c0e02c01014075050410815007403080005600301800354184820158400c89900350690340e00c000b8071080040070420324242e9a5a00a44403803800c5607141c91903031a1804510f440da80451694059000104110700d050030030901c4501038074024041044038040c07080c46c281140c5802c0d03017503481455181d40701418003503241c0c0e020306800700c00341585001d0b0f103074001040421b800a034507950513200c0030342c5019203035050081050058280c4034000311581c0030b1090316000071600200424140c4e80080001c0c058046038900468451070111406044120200101c0440e40740540c40550020024507011a0030880540414107440d00b401c10040140e0203400d0030091002480702e0150001c1210704400e0880c20710540f8009503c4014050340d8202c103680c040000400d011301c185440480c01f24409 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 629401546 1250 629400296 629400301
    0x705030106090b190e04240c050a030e07060806150412060914010c02030f030a0e06010803030106110715050c0a0b040b070e060a30110c07050307030803040f1109 71
    0x121028040c4905500d0241c0d40c0d40d81c61004c3d121a01c1020400c2e81c0c81c10b0040c10311039450341c41c5c031003880c082000c0c41d030202c0c800b0301c503982803112640c01111110720554407010764680304061b00508840c19600a1440b40d00501410700040750b11820054010001b1901201c01841400d444036980c400d42e802040080c68a40545c0100042500b20100d1140038500b5009400101c40351103007a2410741241031b0042e0030810110280480c1c0b90051900b200c042c03100040c204182d00307941441e201c001e8000000036403001c0010040c030b503800000344045003402e80280c030810b8035007101c44895030300560200044c0500422034044d541020014580e132280c20110790006800c06040003171103554281e0300d20300000c1d041701c100c001070f08080044813002202644c454410381402190000741d458085420100051a00302d03400d0619958050b03402001c0750a03120640c0c607038400310f02624009040d440a8005c1c0c0103445d040002c1040da1054950058111200c404420110701d8a05c10091a40726001e80c4041c06105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 629402796 1250 629401546 629401559
    0xa02060901260601020f0a0b07050d090204020d1413051203151e10080f0a0e01182a0308030103080c190b09060106080910020706021b061b0415030902030705030106 72
    0xb110750081e003080c1c084e80c201045c0110815154a8189000392102c883c51000c5686140300b04014492030f40300b100002084441c3e5800141a039025090703910019480e2035022000350910341c01c1c10f42180010050004c3c8561940d651611000d2071081000203160110004d089015000b40e1644c410381700401d4442068040b030a20030703240076904020340c090030440d500413a8050143c4244e9005a0303004040b03060719500e0382803400103010801040e9450355202d056415030424100440e00983d4400e040000e20015540d03901040c00008120604105885020410110b0b00042c1140c0c152500300031981d56420b030b2505240d01c1d001e000c18404174030101d020304200501c00c40c0c840313060182c0e000100b0b0310556661401c0440703080409540f40311060300011301440b04a4030590050104521810f005070824224440b074402e492161018000c1c140c20200401441042929050f00c5150396403105608040c1000c01d04001c889081c1c2d000340a0554902d240415550204078000040000600a100150301da04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 629404046 1250 629402796 629402867
    0x70204150915050603040f11061321230703020603010303030603260a0c020307050612010302090108010507080a0c12060b0a1812081b07060e150c0a02060901 69
    0x10407004018500442c0e03210140d20441410100c48000f000c06086403a261142204604042011110800100c60611454442001410422448024030014580307042c41818660046030102c0010380310b000c0c0750b1400250808011615220031818000e421150a141e80346400c00030340000c2d41c0700001000000406505070015000c3e2440781019400d41d10111a05029080c0c9552507005030401c203101d1132101c07500c608e40e0248441c1c002030480719080c0d178a03000f00c3c0390355104038101c0041551620040c0154180085000d0042400d10002c002910f41404010410f51021300000c480a489140450103188100c0c079410035502c99040401c851075551411103680c5d4842c503204400b1500e540d2201c01100d042c82100001c4507101030000002080655500f4000d904c02d991418155040c40e024400201d030400280000d0080b58944d440401080010030103950140302a9005401382040003000d000c1003c40c1310300e101ca5041d0b07090391b04c8120301001681e41c0c44100c4101c03003000c0509902e280c410306020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 629405296 1250 629404046 629404049
    0xc0a1403030a060e04020f010f030b0d06060e0c0a0503130c050301180201090b090603010915120b04032d0f030209042c0319050c01020d050c0901090510140c010207020415 75
    0x102c5080105035900c0e10000142041114080d501410403507442000b07500900039004007191070300e00004c1d85d5009a000965090310310300266010356444009228455101c1c0348030360446501c285507400c00c1740003040181944001084580820145403454003003040341030354100070b024003c00900420320b02c10180243c807062448107a0008820b2400000c17030038450011a03002c2c0002400540c590313804c040911001d4100c854021107000040d11000400d00804010361184500c60200004181040d007401010a1102045511807001d4031040601c500003c0400020740031035410028042c1903600c2d010f40090090b60f01d600e07006410f0a4040b40004680310000b40d101a88009551400c42d02800f181c2d6a809030402c041140a041400d0303180860007480a4098582e08a00141c034200030190210107481007607405c2e01c0c281d100454491040d60b00601148041e040c00d54040d101c003e21401c1c000c05610440e68041d01d021800500000c42913401e40446159035000b034820f2001c0c1016000160400015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 629406546 1250 629405296 629405311
    0x3140d0f05240d0b1e240f130b0f15070209010e1012151515030905100209191d0c0a0c02011b17040501120504021003020c0a140303 58
    0x1a80288040c0c20944903015522200901607180d070800980d130700c0a41c41c4010b414618940c000550742c440c0f07805c50065251181d070b22503520b00d204038000281c000116010514180c4174000f0303510211a192500c0701c0c07011100103500004103080382c4001c00b00e1440e00446414a4011a0429504154610060081507031034030035207035890f031a07990700256001c258042e1184050001c10100812405420280d020342540c05410b0b000d0b400c02c080c6415204481c900c0201098000b000311080100840c000d1440c42500c80328141800a40d901c0d658071901e5525840c0303a41942980070456880d681c0f10200d200720072031082c1b6031030b1007401e0315070f609000d5001c404440c400a140781d500000368560f50b035900f81d8400840c0754030f900d41c82000543c0150348500c4100420075104010049001c04203401c1070b05c0180c0100340d806003942d614140b07000100004044d010301e500a504000c20700006841d0102103d10080680c0380058403490111402030401e9010300300a4110319401c099007502410100081d8000c101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 629407796 1250 629406546 629406571
    0x1060b0a09090b090109020a171e060d0209070f0c23010501240c1a0414070503280204060b07050c090f091510050301060f081b0a0303140d0f05 63
    0x82d00c0d5603460a503030076000201d070010500030042120341c809401421010441d030420005456540950f80054141120032948035890700c05520520919500b0441c1c0010b001e40b0f0800080c107076600411a6048064811420820221500888140308040510380c05601403414222085249840d0051040f4202071a44039403030407000040042c5102d07409065410a801e04030380e14a000007003510107400b1941d0070390301c1800b40c4469400248003605544d01c0307035114400b00f802c00101120300030b1130040750340c100038000da0000002d0b01001c402014601c400400d10440749039201712510204000d040e8643c00400700d01c0c0c1c04283d0008106000c80c902001107015949a12039542d000c1c051548501c054540641c0782d009036004218032075680001cbc03a0321980503441148956640e80202e402c441090b80020306e049003040007402440400d114010440a04210f524504002000040c480d00c11621005003404a600c90001a51903404c040d60f03d0b02e81d0402c01004030b00c1c10021140301500d03045425400000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 629409046 1250 629407796 629407799
    0x62b180f0b090f1005060105120a050a05010e0709090e030933090a06051602030d0e12010603030e09071403010f0611010501142e0f090602070506030610030e01060b0a09 74
    0x1240001d5024030f030401030004042903421101c3c0700c402040090400380c104002009512001150b00f1401401103d07001c00005183c40c00c04402c03400c4800c10b802040c5660542c80a2140c1c0d568400010002d440b410400041c0b211441c00d0ba8503c0d61080c5004982c02200040880a0583c05246d203010f0100c00a0a400307104019041034a85070b10410320000da12841202c0300b404894855405441405540c0c01c01c198000b5041e00000d15080402c3e9003130000070b80300c00c4a0380719400d0030741c010640030419034004e016042c11560041c1504a00d140310502401c900c00000f50000d100b14050200d200c6568801ea580e07513186d040f03090800e80240210408610701c584100090b10051207158100d03404e40c0d01e0994054020801c001010101d801da0044070600c070b100da05594015440c000f80124201c2c2c44013000c02010500c0600b0007580e41c0c0c001e0007503410012080040e40c0b1a90112580040300b100d00407074102802c1c0d0705400030300c804103007440d4640c81d1a5000c510ba01001d4000c00e40c2d011680c482ea10f025 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 629410296 1250 629409046 629409061
    0x60e04080a11030a090e0702010e01240b09030d0f12020304110109080d1d0111030c0102040f08070815060a032118060933031505062b180f0b 62
    0xb442000d080100103604030307004020039004004907e030005c07440d01c00403445041c840116030964921400294003500002c1c200204c42100d4100e075001010041021400d083e0b840700020745444034421607405125130154100080351180f83d00650b120b115000464aa0805092100d08010007200140c049a140c8901003020080001d13100381c0030903551b80d420069020046d032440050480c000d190b05100b8a2840b00c0f0340320a0501c041d04003090300c0000143c42c1c915001507001c0350302043d4062010b54002ea00d040c07103040c002081d40d81796034420588000403074544102050446100d41d002a00d900c010f9400600140c00d880e0700b8a40c0941c081c2c0d034081081107041340034001c02c0d246100c0c00c1d001c241d42c51401c10546034026840e41c0c42420b800c2c900521341a503890340310b00241d12085160002681d410400342c0700020001072101410741a5250350a000c8130810b030300540f60348500001e20344030180a41441c440c46a0b00f0220a401150803030700c084004e9031801502c21481140704541c90003080340050f003038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 629411546 1250 629410296 629410303
    0xf03040804081e0a02040911030f060f1b07081c0203010806070f0f020d110f1905160b0403030809010e1e06062e020c06130608070e06030c090301060e04080a11 70
    0x707100140003030300c000134840d401c0000502d5008401c541c111500e2400c6020303a1f805200c0500d02c2c0c1a2503015142d54178014070046413403e401050800d01d001c0c01031803600c0c0001504e050b240c0e690390082002e0365a0f0000503121140d444480707011004c560001002195000300400d00d03074000d0030541c480c1c00b203100403440c06443d40e0b40302841c41c20040e031111142100d0703240305013044021070f240c40c0d05843e0b03450080c40d211340c00c2c228a2183d481c0342141c0c0c0d00f201801c10004210285020261110320b100700c5051500c90221071085200203010041c002c80442c008131003c3d030190342400324000845a1030f070355405002c4994000180030004e503000b510000781403400c000e0403140000e1b83d07001c031540d120801c040402160340314202c110ad0840c403030020040810b03280c2c0c4000b41a106000d08041610702d01d022030092503e00d00910582c00c002070600c0f00301c070075121407095075001348100c20440c0e107980031000428014071444d440210030b601d4210501091141c03500042001345407541d10b848a00111401c1070341d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 629412796 1250 629411546 629411593
    0x71704120c090c14180409210807020f060106032304060f0f0207020a03030311070512040e090309010e130b030316060501050303030403021b011403090601060933050f0304080408 78
    0x5244020481c5c09580600000356a03210b410051002031005072544810180b8001440c03032a0b860000b60803010281030300001e16640c000042c0c4010070620b404040c10a450701010320480050585480341614035990402c01200c1c2c1403140d000403240b9240c5400c00b54043d109840340c15250619200b0600c031607007002c2c001c40d40d006030080c110f046030b1459a03400320003c142c5a5140704440400f030100a000490034001d80da0a807040350102a2030b107090544c0507440d6600076001c41407940c000c010901c01d0f0303600000d280c0c400030000c070384400141c2c0384201c1c428090500100084d51500002404803200c015100703100c0440b03801414100641da8850003413640c0c9100944000d005a800fa04555290100c0710402110803034041c5011004a40f040d41502d8241c3c00c1030341c1c0c42d1855081031005101859014044d034000381442c0340000103002103491101642a2540340510f21034040c42c0106000a01601c01c4659000d11010040d07501d14240c10f01e440d03550014007a148441c098a807480c600c0d0412081e1014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 629414046 1250 629412796 629412827
    0x11010f14071b030f030507060c0903050c1207180e010b0105070213020c10020f0307111204170f0a0c030b1303091202120f030903010b03060705071704120c090c 70
    0x901c1e080c640c0c1c42c0d040b040000607201622540a0704004400a00c400c2d86030034502d8803075115251101854036046e000e8030350004540040101c1a0002c0000c90800125218101400c1d1040c0c40c800d0001c20780c141c28108503802c140c4026428244800b05500340f6070120520304a08070080080445100046446104000e0081c1d400280788090203201e0002c2e900500803200004c0440d00041c100c580d01c101a80c01c0202c0794004500c0100401c080c16030892445160090300c080688031498070440415001d000f00d000d60030406241014030b003d42c1d481006100d90321828141110078032051841e040da1003041900044804400340342c042500fa0910321003030008541d060f00c0303c1c81c0e040e00740a1401014460990300b0f992084138010702d410686018000401d501c045038019560303d0044009044c00d40e02080c1841c0c2c082c4d4011010000941d6020082c0c5007169404400b03844503240780742c0030322440c1c040c0d900189a5420303c21086000c00855640200444002a100340f103e03c10124041c0c2d400e0b1000c22115 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 629415296 1250 629414046 629414087
    0x4050106080718030f11010318033905061024050d020904060e01140a0e04060c020703050316120813060c090e090d0201320601170411010f 61
    0x140b040b40280803502800511650600b8841e540362aa0071000c8100442528a0007000011030844d503070500415142051030402c290403c00c1c250703401440c00c0a00b0401210080000002003521403403c04038000701400306401d0011f803c058104a6241c250035119054508860701000811040078101400b81c4e5020400c0b010314091000000e072a80c2c2d0201d100c041015138208940e000966030351080c0405800e107403074600b26075810424030402e01310341040154030981003042700700300e101c200c82c0180c0d900952200001c00d85507032203803090b468500150002880e600022030b1781e0000c00301c5e10b001c0099090084401400000c0220303410b40300c0c100305480a900f9040c4500a5101092840d0030400b40e515083c5000107102e952200c1c04500d900701928540f4841e000b002040d0040307503090184510200d41203d84900c9524940e40004408000d07100c2a01a40030482c00648a83c0c003800c1100c402c3c00381c0d0224a070280c81c203440d007444a86040250340e4049400503070700240b1248580f0b00180440c0c16500721 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 629416546 1250 629415296 629415301
    0x31211040314061f143d0e010e210a05030a050a08131a040c090606050405031203072309090702160f06020723181608060d02210304060c020f0405010608 67
    0x40c80070030188440043d98201c8403514a040c0084c20600800d942e01a0382070102261000324001071040b241d07401d00a041000c04500144103540d66038244500d5011002b910821075598411f2506001c1c543d0405040c900011401c0c0000300e82045c000c103454481981e030348120380e5540806454060507008d01410040c031981545010009040501e07410a004d0151001050365540c6070400740e80090704840001074010804021904040054420b4050000d44590551800c0c8400400c1c0b55060910b002c3e6071041012080019208507088520108019111a2883c6068100031f9624560746200070f01c580b004000020350b41d00611207c2c01551200d6002d00501490001407900c81403e00d80821888000100f0132410383c1c2d1000d80308100032070b5018240c980d41c541001e422120003841e500f14000d010303455081110b50b85d2281c02d2060400d5045400c003001d0074480280650180c0306058019051000040c04181180c202c5a942d44052003220b94a095008001c18442918000c1c0700300710106400902 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 629417796 1250 629416546 629416549
    0x11203080c25020120100501240c0f02030712050c03010605060a0f140301090c2d30050a1a0603010302010c29180307031211040314061f14 61
    0x15101440c2d8014900507103154058507021880c280c0e104550b4216a0010b6211482c1e8512400303418010b0101e44488200f00d1080c400031840e04054030290010802d10b0794214003080a41140510065006021610704e591241684044449405405c0d21940b14070061231001c0c1c907050046c40103030381010781101d0800c441180140c1e821500e10a255042c061000e600c8850360004001850081100d0032020420081317000020700490801501e07502c100e06082043c070712038500c5d19060418651a407070140403010441d00c1c948442403038040e0722080f5040340a049600210f580e0481409007840102c10042d64106615a080c803510b1004200d42020050004001541c003c4005540b020f021b8907448806203064000480c80c107080404141041c0c2440041c03241080361004950320815690f0b004524140240c1c072301a048020b0f200c07541910603140c200e451000780b109401d440003035600101d820b402c0101c08402507203a480c2260174a107040000540032103410b9101300b440084032070f80c03920503020085420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 629419046 1250 629417796 629417857
    0x30311160b10120503251101080c0c06041103061e040f060605060d0504060605010804032c040f0603060b060f1902151602120f2a0105011203080c 64
    0x1460400030741d01488002482c50480c1c514800f000b48681e02540c1d40307407001e50000e1259185c0401200243c608080304d00001149800c690501e07103803d0034a401e1a60b9040030050041c1b007503014a444038000d103002d0004104032007000048494045050b9920b644e1500c2da020403841c1300f4078007040f009200001140210303603c0210000468010200412015282c2010807441d41c04400702070f900f00c0d50b5200308424000c40e4803030305001c3c00091030100b080e42010f480080001c401e41e41d4a1070b1380c1170500c070350294045160082e00c04a00c800b070001c0c8102070700b140e001c500500036403105071000c81c00c148020b440c900d0070b0011520b2080c943c0018a040100103010580d10407030350f19230300c3c0039881185003640c1e0507100f0245581c07060095030000c415130703901d03584024200034000c1c841441113042840518211b600d24810b83c1c0000d0070081c51146103016442e0a915901744d20403840c0800e51a00c2c0c00450b2000403001c41c071084902a4075a01e01a41761460044c84610a2442e03103400c120950a00c40045220103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 629420296 1250 629419046 629419051
    0x30f0406210507080108240606032e090f0204080d12150e151e011107030c0801050f070504030b13030c060f0b012c060c120a0804030311160b 62
    0x100d100507800d44269000c0d4044070700648407840401c0100e00104a031000c1041940341c240b25100c0c0d002d09a002e6040d0800e005000581050321824011002031061000350001c91002000e540c80024081c0c540d040d4003080040500680001d00d052500c0145000c0040c000c880440700c000d8028480c548480c901150141000c02c012078500e0b403100d0044211095041c01c0401074105450f8070314a50800c00c0c6080b4490701c03403403409805552501c85404c2c800c07001003140803810394282403c5c0c0640c03c040207080d013400d0f003d401c0100140340340c100100318060154000c5104400d0041c10818513285c040083e01c1134041c0d40b000920309019200001c0071a08040040001548641840203680e0025601d080540d02a020700c100b1555803480c0503076566a22540000c180080b0b441855001c60080e1010b00c180c04110700013500902c00050b04603819002006007184000a4058890700c03208800b000030300c003210a44007600080e0804952441c00c422100c12601101d04511030354210550a5440145a8100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 629421546 1250 629420296 629420327
    0x103080715050a06050a15080a0209030a20030f150703020a0509031e010605040b030712020f0d03170c120a0506240337090606170c040e030f0406 64
    0x32540180840758041c0c18011990f4000106540d8248400c0c4021504e15601100c4e06520017902d40c01c1558001300099006a001c0d5400340c0d448001c5804079242903503095004025581c01005000c2c0c030313046c41010074000032084054400a80b00c014800c1d58442d000414814140040404540c403d4000c5d801003c40c8200c07030034038a082c92100310000e420050301445492105040d00c02400b040d000030710500b0050300c0101c2d4104580701062000c80d648920310700407000c4084025600c81c01390340d51016141d0310403400411403440745925240080114031681219008100442c0200d522224541c00751003540d42540c102440320342d941007400780540805044aa0040001c411084504035480e100c400c100603001180d41c0d0701d04110f01082d600b0502800d0081c10840b4003603000551b816503113900701521094000101d111011400c111000b00b0f00c640c000d0ba100c03144c1203800c0c9181d0f0800300d441034008400320340401c0885030f00c070381c121b40b24030400d4a0010300003410001030002a0088012043c031845 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 629422796 1250 629421546 629421563
    0x40506181804060504030807080c091e1f0e03030703120507090305010606020304080f0d081f0506030a0506010e01090f050118030602040807030519030206010315020903010f050610030501030b01030807 88
    0x600e41c400c11100c850030348003900c000d0740352810802496080650381c0d80001c03180c0782417815440d28050f054210701902c0c003076500c0341c40000078100954005140032584a6801826500b0b40b802d8a00e035450300081020060340403a4a0404404240c41c0200503680c031150142c503001e040200408404004190082010341400651103020011680c2403040c403001c1c0619400940d911820032600310314012140445840c180c2c094001d0300e0039241c0c4100e0b241c0d0890500221542c5070841d400b140c807000ca01c0c9400c013542103d0080308005410803242c1005024000a0300c41a80d40c00c0a00011940f80041d40204521850f0b464003c00681d48552038070000861610351049100707803266107002c242d80c820f40c00504180c0c050042482440000c1c0100a010881440c12000402c9075a401035100c0c10144400b40900d80948000140c10f42142c048a01c5040024020030070216146422802880d0540d1900d0003690880b4580003060b000b0300c0341d981641d40068010354261303c4c1d80c5e40d900c00b951151004480142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 629424046 1250 629422796 629422819
    0x60b030f010908090f091303032a0806041116140c0d0b010f06020f0706050d09080d1a030106050d060507200601030203013801210e0607020304050618 66
    0x800e1040c00c0e90300b48268012684e0b41000d8082010316802c140750701c1e00c62240802404803030400c2c142001c0442d0392508010441014040b50140c80c0a101841c01c0c4a000304004640d600c0e50f44000700034800c0f68120360410082090400d4601789018001d00c00340b050107110515408030b036180444045c00c0d03001034100d0303894118003c045a81a055018100c44844004006101079100001c440c00501607520080200c4045140b0241e0b68140c00e11030307103042c41000100100107046503084117544035009210700b81e0705c0040361100310080280e2500380d03211051059443c8154a01801503a08a903401004400c610b8040d440c0d1000411000e0644020700c1440c0b07003400004d086280d2030307600c0c0780001000f800b690b40c5940107041c00d4410003512104100208180c5c0382c00000540c810032a0350000d0082845110401001030b91401c0d070042d0124022a20041400803601c4107421403064411035209903020364403806400d83c0d0324003440c021907a1000060180034600d089100d01e159030b01000504020601 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 629425296 1250 629424046 629424073
    0x606050418091e0b06090901020310090e0715020d0e03030a09032010021f150e07020a0804141309020105041e1d0601080601020705010f032a09031703070903060b03 72
    0x124200c8070042d5080c1002504d140241b40d040d44102950000d41c80e5280c044124860103101d4000d08121035a541e42e22a1702c00070411104000e01801160000189104140603581c1c40750243c0355000220408415001e0b806e01100340c81c008500c541356019524250742c0c400001550b81c170545002c200c042e071001545561101002110b07119550050007038090104000d4984080c03900480d87c0042c103008004081d0248504074004031001040075552685440030101d040100c4144003404040000c280420032059032090408a0001114078901070005520104280c400c0310038046d010620510080068011180e500303c44003280500d04036500ea1113100c420b0011141e071b6847c1542411102c00c101d0381d56000003645400c001c0900003414218a0721000034210800c0000c0030041507180d08400511041c401c401408042d00c2a81c078032040354078254010085240c40c441520403044414400e1072464a010450780512095640c0310103440c21911043e0140a192801c030750948600d00014056 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 629426546 1250 629425296 629425343
    0x303090b0c030c0a0c080d05041d041b090c092c180a060b040614030706050c03120408070b1b0d0c110a060f05100509040f03111e01060605041809 64
    0x3205e00c1000055005e0381030010b11ba05c1d102c500f05006081c018100320521000403c1c0600468a092003641043d0507a640e151054070000c0900105140080284d00030400b03071000d0b042900c003855141d46445500d5500d141c0e202d02c5940c0c03440100c07100f101d9018006004009081c1c495440040c25000402d4000ba5100b060328002401070306580b01640d800e981c84903898540180c0000b014010410f003003183d2003500003034035104644105824028002440303e1484414000d8410b89031a0500c00360041c40d1505100c50264400c0d90304840b00384086000a03114a0940c1c0550f444100424001d801c00034500d003190002c201a00d1800700b440619444004424000c209212019204400c00b0440900e071600358815101d02a2020110038040107082c4002e448004072070b940a41c0080b80d152003000903003816620301059010401c103134041c40740500201801681e8000d025200350008201540d542c840440e082d000e01e014803090b00201020b07080700c0440079001070300b60320b020b440a4051280a4500b1204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 629427796 1250 629426546 629426563
    0xc020f030408010606090506040b03191506050705010f0e060103030c03051b0c18011401030506040f09080304110312030708090f0102031e09071a0a030603060504030e10090303090b0c030c 82
    0x20b06a450f03030f00a0140503800072020300184005d807442401d050030258504004c1c04000c0c10161000c000c8802040301c405a40c020008001c50141e50074601c2e526038000030059480582d080ea0310750300749080c84201a80300d114030b1081c0c102c500301078032059003141c0c0e00700c030080c41d0300905804001d407d20807103040c403c4284004628480f204001d08272007100d1003d00424030500300e450484800c00d0341c010400ca1181400341c0442a5003441c002a00c3d0303036150005070050290f04030710107003140741194050401c07044100071400769001d44499910034505c10300301075842142101c1c1e803412000038400719664034014805113811161040c141d42007581c18100141c00ca8100310b0340446100d1107180d4190b8004810806140c003c06100003501e0fa460400b0501d0040f01c82c2d100c4c1d52100c000c0c001036102c0040303100c0c1d0304c04c6c006103078460000d00c00e0307040c2414002e10403404540d0320b5204e0145a9914040369000750010403c0300d0381074650b122038918085020b120341d0490a05032815000402c41c0301080c1e9030502c070032034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 629429046 1250 629427796 629427809
    0x405060105153006030a0c1202180c030f010806010f03060b04020d09050309101701060c2f130b090711010e240c030c120c04050d1527060c020f0304 65
    0xa005100c0c003d280052040042e014034000d0704401c1d109008210429200340542c0c82c0060140c0320200c4034801311301c1e00c1582c01d00c031003036150403541840941e080002c020f500802e078a1400f4403450b41c0390341809445100030b00c07920403040034050701000000c4140c1c0000521380b0b002000142007440c5002e401e400e41e40e02d0141103901d0381001965611a2602201c8030051183c0c44c82e0800c0e030480309568850314018107010f210184142c07454200c0401006d10412a2609590002610a4007400881510718102590814808c504c41e0321020401140b0f0721620402000040003001251691030007900c503020500a02401d95403610b42810b245403040014103c0340907242e81896011602074500d03165904040c19041c0000000c105020f0103070030640940b914181c040c030404019440d58401500680715561225400c28055003010f014803080e501da10388107a088850905c03516032001512092064050001d01684d4082411800131880507842504044110700466480d4903030551301078903680059005070b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 629430296 1250 629429046 629429107
    0x20106090c050c0a1b080f03040510030207020f091b0a08040501050106030504020904080d0209220e0106050117180102070b04031707080a050718121a040506010515 72
    0x100540803891003101855185842c02605180b03ca40d82c0c16140d007101074000e00300350490f464482d0504204030341c000051841100311003861407911002c50300c83c0c00510409110312003094900307180b580a80201c8514030b07401020220403801c07000401100342c030701910032824000f14048640c0404c00010080103944125117445485160030326199083d0390050b0001c400b01401d14040c000141c0380c04126035007065102428686403c4079140301c00082c010a521140d10a4403281038100040c003150003894801f00c0c40c60240468601003030010b082c0e40f064850b050001d080400d8224220403c01c4c00d858102001c01c890427044845481c000e402ea801201003910580722a4084c40100f54104042d4090303003080b1001c9520500c0c05000141c1108002001450700d80e849100080c80c41e0700c142c664003072aa0080822004468030381c400088165079007072041b2a00310001400e1084040809200d40c800caa000d0001c2441e40c0c2880d0034070010400e0740c2804a0424000d0080c01071014a23446818203412a01a02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 629431546 1250 629430296 629430299
    0x7080613060b0d170307020a0b102405030c090301020d0603060b09182802030604060519050408040614071509021302090f21030c07080606030d2a05010507020106 71
    0x901200e5402c49203610802c4948820b90000d01000c10608425080c80ca600791241c2d41e03180b0a9040944000004106468030020490394078400000101074800012030184910706215502d0300b00c0312014401d00100b0002c0c000036a41140030001000c0b810070290001d801c0400428800c0e0603140982c004a900c2138441c040740030503090028050fa44841ca68025840346102104243d496030b9038044081d100c1407524aa004840703410600f2048038a6000c0d04a815034070b05410440e0090105a034203400340761490210107607001c054020203000b1504405c0c214a00740c40d08801755901b01044c00ba241965100f40115000700c0c400842c40400381c1c0c07884070f0209006149104001e41240c440441c5a6005c1c814005d5003400d49940140111207071050f5041d0580f00c0409901c4501d82d049000c3d501130328400001c0343c2e030404001040784030807640300e00c0444003280c80c1c1800305512900c4401e0785400080485094950059861900220350500388101d005c20441380d41740c041c2514000c031350500250303444034030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 629432796 1250 629431546 629431553
    0x81305150a0e0d06021c09050c0d020603132409050c01030911040c0504120507050a0506040b070b060402040b07050a050d030209060405090408090406030b1b040b09010c030207080613 80
    0x2444103404080c00d0145440c854007006848081c107500b0050250070108826401c10149904460844140750100b11100c0d00d07485220014200340c1030b0032a090700440204269904000010300d0400354001c0400e402c0d0380e2190308003021072030944801e8601c1c0e40109420180707240c050210f4500314075042c50102d16407055040c050300e42289010a03504261800004001080103031145440d0018125004a01c00c142c0c400f0403101802990880580d0f01200a42c0f0403c0000c0002c0389000c403901074881c8100705030368100b00107881c0140d1203080e41030101000160002445030300c006a020800a0006003060f44031000c2d8003c580003074900b102e00d584060751031400d108040000403091500c5140551500707010402048040c00341d8401d082c0145030040203d070800c01c084080c0c42100c1e00141013008502da1364205580380d400d082d5a448001d14100d01081102e1507244c0450b000d03079080d401c2c024a04000240111380100e01d03001d00340c0850090300e10200380c90401344400c2d0f01460070341e01b691000c4406400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 629434046 1250 629432796 629432809
    0xd180308010f1a0304030c060e120c010506040204050603040206070f0f0c180c020c0607050a02040f0b0a14030303160e0409030324030507060323071e0237081305 71
    0xb0025142102d03010000c00e0b1003c1c028084941c00f590510304081000158a814000b07894000300d11f0f007150181c030000003e007108040282c502c2c6810000280015103070300061104030710a9000b2107802400c01c100040160800c2c4000344030981c800c80050310111016151081000710948007141c2c80c10b041e0404002c0c08800c200c075280000c001440401881d101250003958a03c0c3c0482c200303009040200d00b14061101c140306200403240c02410a001daa03038442c034040018910b03481e42505c0340c25050404070380181071303408005580f032011b0b00940c0345407141e101401401290650900c10040103441601e81d584840c040c2924291103906c01217055034101c1d050324400040402c08030415950240200041400010340800300ca030381d42000034a019407100716801d111840740d100c0c800d52082c001400a072036031015a411019038400c40901d00341d01100c4080343c450101c00c841c0c440248440c581044640d201302100c1d0f45815506010000940c1c40390380d899459000030740074825080f0102e030200030608022 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 629435296 1250 629434046 629434049
    0x3020316020f0a0311010b04020d090b071704021e030f010902040e0307020114032d0402011b1101111c03060e100e011205070902030103050604020411040602030f0d180308010f 77
    0x6002618602c8010360032103640d00c1d5241000fa0401020851003030440d202948071070740703016010f0401d643d1112010001005804400d00c101e860781e202400040001c0c0c419a003400300f055080040c03500503100c03502044120208001040e0306240010720320f4016070750800c8110010b036a45400030980001500412040b999041c0c02030b103261300300b08002c1c030040c4c1c0d0010b0200b03030303128014110300d40366161603400b1800d4000c0d840010000d2030040e0b081b0418041d80d04149413066100340d0341c0350205d150324400d69804403c2480001d01080c1c4070a4124505d60103548243c01501007a01101e0185d01407401c0703803090046400d20390000c41d5030b03400c080c40700701c01d80110320ba403000a070181004030ba071a144090409090510503144141c2e1204005420081c05018040041001e00415900c035612410b100340c0f18507081d00c0480c0714600e8041200d0304400003070b00740e604503101500030303506001d6030703146112480d0700840444c1600741c0c0c0c03817980d242c10240404008000074003a5440000c1e40d03062021161003008113 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 629436546 1250 629435296 629435341
    0x105070203041d0901061208071106160204200301090e0f03070b01031e0f110f0109030503041404021605031b0303091e010207051b1e060901030e100c030203 69
    0x802040c40840103c40c00d00768203c0c41810150300715a220750001d801085160403202c440b851141c120000c0c40f88500242010300d001d042810b558406d00700030000e480c03040e903581a80301c02c1c2c10400480545803640c0b103920300c0e14a020b0605580340c000010010070303a00076004147d1140c3d444800300180c80d82007060314411006030004614180d800d0700d4101040b10148801006110300e0341c900480d804880c6004106164407003c0419030415502d4111400800d003c180c0e030007860108d00c2200a98820114101204d411001175840e003401d140740950401c00602c905608142c003000054850764540c0c150402c0306025001650711424511645041a03001c2d0001c25120350007801444940f400101d016030010032100900404400c03c4001070340a0b005520703018001d40903562040c2c9820748441482a03456800f200d6440d0303601114402c100b14041c458509603000b80e01031241c60a02e501950050841d04616400c581560341007001100540b4064840c1c8070009401000344040804501c5076070000554 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 629437796 1250 629436546 629436553
    0xa09050307180c0504091112090606090406050604091a04060617061311060c01051909111905120c2704062a1808070b04090207062c01050702 62
    0x35210600711556000d03140610925543c442051a46002d20100c1d401041c4c4a4800e1100040031150204075411a80e641104820300c58002040381c04041000c84c4134641c010f04200a81d01d8030f8440c18002c00009100c90380250362031103000701044010039603c00449004021744100e18040c5442c40558240e03a03c04002d5031410640e0841035000071031000d0f805140700000b20490320701418849040c0110881c25a00300c0c0000811024642041d04200d20030350b8208120310042034042d03802c42c1107030580788010348200301c402c0201c0f00b1860b003540c00814500c1d0280141e0991364991000405944002c0c10340b54003984441401d40705405c2010400c11016041121210312840700c058864414200802c01400d203030b9981d00d842640841b40480c403404484561080700101e10007900580905000d018a0741040003410340014004030006480c0300342d40124005505240c44c10301c3c46806034004540446025442d0413181182c10a00811010072404c1041d42c100d0400340a5416421200081c01c100110340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 629439046 1250 629437796 629437799
    0x519080f0d050403110102030f03190605010806030d2303090714060702010e01050304020123251106030703020c030a080105040c030c0207260d030c121503030302071b0b0a09050307 79
    0x64004096604894011705020360000c007010040341940315401c0720030316081c004010321400300c9400c0b5030044500044842046404c0d151b4005403082e603403c4400d10744c5503204031400c0c0302030b5119040b2691000580d01c203140c40f0b22503401d08045e194004070713030140c1c40b0342c4030310320404c5880e02203001807107890781c25207602e443c2c1146a00000c12541240d003034203040c0500007010808691103a040003202110b03142c45480c201104072120045070380182d00e0058500e0b00001c5070f4140d60308640d02101102c0e4009920b6184d40b00038424800705410003440309050603800e00010301d00796000c0c8001d00c0440746070303030f0f03550324941c1040108000c99500000040406103801003150019800065680c00d0310301a000300c08541040d4104404d466034200e8038044280140c14049074960b0701038000758000800c94036950505d0040480341ea040b911490505845180d0714203040020038002d5000b003440ca8018007139480d501c0c0072900b812160103c542e2261190340c400090036a92540e0041c40503001c1c2c6000c8014000301c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 629440296 1250 629439046 629439073
    0x513051f0b04152319050408031204020d050f070f091407031e0e030703030b0d0b0703050a0b0910050108070512040213060510030902130501080618070519080f 70
    0x3030040340540e01c41401c640a2040046004d40c61070480d100008003004c11814114451100c15045803801c10700c5c2152690302d03070002c10b0054043d00c09036140ca900640c204038906001012221019109030b030081066600c9101052051080311000c0080b08024035040d4501203410301841c0b4240e04c290304003490081c0c00780c0b500c0c00510001d80c00142d117160200f02c00034801d0b00090f901151894008070540340042d441e81e0100084040c01084d0f010752810481e00b91a001841100c03800014001c4c8414540e90008040c94041c1d0300241d00140301705800a80701220b1408102e01c8541903561000410030301e0b00400096a02c04112a0300c40100c0c42c045007000018111f10f6480301300604000c0c41459031407039041241c001640401d0041c40005e0050784c0305034400c1000b500070018103406030300402e034401104040000750301415048480381c800421342543c95965840802c0005062010a40a100000981542e07100d112504004031180112020707458000d9541c900002d031010781166070402012496003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 629441546 1250 629440296 629440319
    0xe0105030720070506040f0503070609030201050a0819090609150615230f032203050703080a2c070806010501020303040308100b0f07030e0411031303090513051f 71
    0x11100d01200803201c0c11509a0201d0424030144c00160304440e02280014a41c0c910b201000c04032401030701a5052030352140d0089a03050060b001c00383c003240b41004104202c0381b20b8a00d00b58880040c814091002c2001c0c082d070704c15035402c1e501c10f032070380c58858000300e043c03025040342000314040010b000c2014624040c91306585100c8031489106204000381e0308201c04420749401c1410008400d6001d941c2c00d403103c0456881e403c15111100b01c1341d43d05403000d245807001c1c462000e0175134260f00c529040039083d517030444103a0b5004001d10302850b2941c01136004d01b04800200700580c0c04050340310200d04c60541001c4d14102c0140d11071506a80010010043c60360007008594002d0b404d0300d00400180e079941501c2c001e601d2668401e1a0240d000154400c034103c00001030000e0328400d035035480303520002d0000c00c801c0e1148812540000c00e010404121900403400c2c0651045119003000c3d013010340c0d00c100142c10001921740f00000a51500700f008088402a20b04550078901141446511810060790b0b404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 629442796 1250 629441546 629441567
    0x180901050a090e0f0f0a0312020a090b03060301020d0c0504090e121b0322031a15060c10090f020307120b0601050702040e0f1006050a06021011070f060c0e01050307 72
    0x14150f40c2d8420000c441d0383c082c0614140c0c40740c190304642070201038040c803980e90b152005081c0e00103002c0c440811302c0c0010b64000c4481980310303036603090006d908190a5000d158000b5010a5056608211810580196000f18451128a0344405486034a001c0b1144250f64503083d00d400741d5000915172417402d20301002907a440250200282c10b2601e010210140385100e807201c40c030705031494158481c084000034682a01601c1c403c0841c90300100b1440d0b400b011080d41580c1003800304960344002826402d10502030005103da0f40112002542982d05100845025090660b003183e030358402802503003010004a80206034100c560720482e1071360388488071510b101520b0720741040380014681055545641041c104000d0101c159000180b55000c1640e0321a51561a141000c1c14480009961b01d00040b182d400c441d030310380141452454685101c070003010800103030340e83c42c2400e00003440422480d801b504021441030360000b03411400307044090803604a00300c200781045400c1040240b41c5a01610119 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 629444046 1250 629442796 629442809
    0x1b050109050d181818020904120e0d02091305030f04120c05060301030203150a1d0a110307080c01030e011407050a0e030a020f121515010806091017030906040308180901050a 76
    0x1400604494100445c1640443d0180d8004c0160081c4414803650812a0035010016100d003541c9555003010301c4400122054060b50020728040001c03200c40380b0100f120b403481e00c1001030720300e48054000ca2000c2500183c00c40c0707000310001c00045040000b07a90406000d804c04807401d60031503145038002941c030f10150001400b60074030031011481c10042d40c2c10107061204801d040a120240c00351b04d0303590b542d41c040b0050764601c640d1018010223007008030300c00083e02c80031005810f045030708400640280602103070030142990703a0295854451042e9280d240945241c0c0d17500da42e968a1400000c007840b491000052007038200039200b1b801690350083e04014110160382c0100d1105420b03410130b04000c110801845000410401c120118a10780c80104501201340c81d0015291944428050b00d4042103c0000c510a1450028809103000b86107204041c4242c2081300d01c5e007110701021070180e41103a80101c0d240d40000c210540c0c2d4903447c90502040c00c00a0710000c10b81e40c582400a03080c1403e502c00da5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 629445296 1250 629444046 629444051
    0x40503040b070f050607170f010506090d0804121b0602030a0f14070c0f08100e0d0e0328060f1a010f0203090a29030c03071b050109050d1818 62
    0x140d08000c2000c480d02401c0313130010b05484d994502035030050030016020000726203044a4000195144107081c00b228140c900c080d0426040516a005000ca1910f250b00c007503443c1c203001c0c400020008000502110854400ca400c42a450f03804810202c1d85401a040841075400c01d000355054164040b013248480011403a011101046115000b001e908c60100080c00b40801500003040010741d004044080701e00c08000c6491108408004600321001003210340b040750828508446e05522411400c061035000500b42e5000c440c090b990315005059007007050001c10a440307100c40c1446070310300c41e40384202d2500f041800b8260351541741c0240e01d030300001840c1c140000f107940311010134403c000b030342c40640e8050400da0040c2e480f51494092000c1090100ca0a0306600004540c5070030340d8000c1e01d0040d0119103045045803a03842090f91440050f40e07061025107554030250000c15024000c41c49401d0280d000391030690224000103111504801089440b4240120704200c000b0b88004014807050041340300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 629446546 1250 629445296 629445307
    0x126040b1003082a0c0603010b09060c0303040308060a0603140604090501110d020408010f060f03080702060f03130b01050a06170603030c0114070306051e09070c20030601050405040503040b 83
    0x81c044a02019000a810f0301c3d4041244880d01c00c504a54038000a90300c181c03940200e8044801c03542d40c0303545010041e0002c50a00041002c1c10314000640600c8000030710741402d0401160b010b031721310303081110b0070b40c00031391040144016420008182d0001d4555440c0501c41d0518241001c9901100a8402d901407a568a001402d1220039403201228441c0c0a00341a9907410141c01000a504035001e503503050352074105c07501c12409103442034608170703580303d41e00c01e41c82e9107580c444030102d40040c101680c01a500700103950454812900861240c14001001e62003444c1c40d042c55081010140c201900400b0002e40a0044e0b50708000c40f40320311505005000d415686820101e420740c06041c8040325598242006c035041c0001001413184202e0140c0d8041004070b075a2004c10102000d40000000a49242c19400d0001c1c105201d6090f44009581448402c00750140e8640c42422030002c10078882d103260180c80809441d0520078940181011a4140054103054961a07102d200fa07214441124600051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 629447796 1250 629446546 629446561
    0x2060f0a081e0123030f1011090114070f0b18010b01020c130c030e0d080103030f0f0c0b1e04050c1305090616021e031309020703020d030b0d140a020126040b 69
    0x8414000135000307030580e11700d1240c3c641e000da80e80340050a6105003a05110310710a803410007105440c110041655111089034103c03540d40c2190b072101300d0a5451020a18140d070108040d00c171605c5c052020785500c640d280100804603030842c0c0c02d410281d8119001705250800307aa8400d00401145004490300181140f054a801d400401039403251100f41c0c0141c0002c400e401d9004885941228080d8441140080c5612070490701c1064031000e81020681c074402500c0131941054880354401160100e413040200c51244052842e80f0495088a07954004454003441d41448100c032100e450b0105c1b000d112906003032045a8985c5401064100d44800d5140d007a03121074400c016480b55000c1e012180c40034036060f80c1c46030703440b6404a46107858200b840c000014003a40ea038421200c40640503400b4100141d841c00048000d003411030042e5078003035140258031004c9200f5146003d05501d21000030100d804503880054045110510f01504051b801e03011450403030461046240c1c0705502400e061160b640d00c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 629449046 1250 629447796 629447849
    0x13021c0c05040f18060506011e0203030a0203100915060f0e0604050d0204090b0412080606090915011e0c021314010603020307021009142b180302060f0a081e01 70
    0x10004d034000c0d0700103a95820700c0303030940c4441d009040030383e02d0b0b0011341a09091218040000402031005900400025102d84d41030360155400030001080d10b441e5954522102d0291010102036400844661000300301e0290424020341800e40203040582145000030001141c90046104081c0950655903c810031551554488031100c1da012003e0f00f2070f800c15042c00d18a20441c118100042022100800e0f02031800c402514401032000f094070499594401500c03007521326152000b4103205145458203400a100c07010394400c0702070f0743d445100008040c01040350002029100e032505624155100c164002c04a01a0f0306494090502582ea0f0321007402c100d2600003012100c0c0d418030703c0c18482c401042105c1c00310300050341e41c1100f100c8001407044182c5d080090030980c000001031801071000031240c0582c085803121705000210040107507490300800e10359484440016561400040c200c40a5508103405540160007051aa0042c912038042c140346a4018082d20006030080400c40b00b0102512 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 629450296 1250 629449046 629449061
    0x3051b090f030703021c05010e03040e071209050d11060f01060c0f0302190b0702011b050405040903022506080c040f0504050402040b031501141903030e01140313021c0c05040f 77
    0x240071140c041c3c101820406e8151102601201e4550130052081c500c2e400000030380b402c0e00e41052840c88aa200c210080c0c0715020300b41381c0d81200765140c403c580c2c042542804a01c4411446440d000d050981003e5580d05210700180a42502001c000052151503070000020104c0c540c04821045420400d050a13454961028034030619080102c152104102c03450002a0040c00580c000784000491098581e09882d03140391403000040c020b0004101c1c03480c00b030b00705a81660280c010f035036842d003910303841915252030389007080042036555a003009034642c0300401c80d500c0111100c0d0141480e080407968400000e452183c244100d44031004503003950b407280d002800310b07000241103404900c10955414501e000901c91182d04142661111545090005020944000e03030350800746161f04544d42601e5080004218504000c81d06015040302e034004d80055008888941520010f01c9032441000040f03140080e00003032901d0070412000c0015180c0c03180308144c41044030003003006450840c50700020441c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 629451546 1250 629450296 629450299
    0x1507060504170309030409111204080319290a03030522180504020a06050f0f0703020c060c0a0b0c0a020d27120213050105031903020a021f03051b090f03070302 70
    0x301340424850000010421070700e030800240031482c0e005848060500811040543c64000c41000900280c07400c0010760748901c450703601c1c11500003584030101c204e9030304d448089040750005d2000601661911000c050b542c0c0d0840d0713801c084505594005003d806041c000c480903100300310150481c44604941d800103000080d181800031800200c880000d024142c07400d0b40260340440012509605c104100e420582d11344002d1494030f50079003170217030540d40240d1056085020b4a810000c41e83d80e090000c2248908210040003010402c0c1018001c070b0310003411200c4844001c2001410403a00803030b40308223030501c0b410651050b041e40c0c107419201c040c50100000e0050009000851b007070446101c0c420140e03000755804604440302d0041c101c11900280102030389030340840c607045c43e400130703550f66007207602d11038030640d031000100d5404035004114005040d01300c0308030407080480c1c640e0f061260302d41c00801940442400c9071801c0031002c0a2007100050341c09111031481075403442e2001c01040009560 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 629452796 1250 629451546 629451593
    0x2070f02120114160e0f150c0a1101180e06030f0708030d1503030c0f08130b030609070306300b010609050307061d04050604090512090f1507060504 65
    0xe195007000d00800c07100c181c682c0c04110240c045030f04440c481e0b40e101214946a1030fa4801c500025040007903e41c2c0b07003408280c2c031a800201280c4060459005040520500c0c0020035a08501c1d141c14510075580007181c0e8100911240783d11002c42084079001c0c00c60350030f4140c51829455020100b070803c0040c2120b0f00b494030079201e00040d0250000014880d0500ca000d0402a182d810079204090500741d12003d00003070100d4021102080700d036402248143d11495160f40b9016034140301000107880b40d40b0032002c500c000b108009860800520303a50340607005141c20409c0908005407590303000b440e08000e185224034803e00c843c0d20964071b58406c41982d00840200b04648e0354881c000c3c4401168012075001c0c0c041c220700001c0751400b40801042d08800d06d9030f41000008201e05100080000504031a80251504648000f28400307010016007120701c040c0c0d04c1c1e92120344105201a5040d005000c50054201680c410b060301c00d0401925a40c55010f140801c0780d03103603400c00141c1d126100380c604a070001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 629454046 1250 629452796 629452819
    0x30a0902031e100606080c030a0506030a0f0507060905060903100c21060f05011e1b0b040b0f011a1b03040f0e040302120406021c110a030e0a0803071502070f02 70
    0x2c0005149404020b561400d01081c0e8441200b1221000f00307641130901c0c1c0c0420303c041a0146010b0f0403896109d00007070f0031282c5038455922030003290b00d8034103825503968000c61001d01155078440400300c01f0345000d84400345040342113808039039030b41c23280401c102c0e801d135813207244c000060701c40c03080c1c030300b0b410601d5602a41800000b808400204841e03c44d103118200c0c925800078855005440701d0344030300c641814002e42c18410040641d143c2100412450344a04880030100010b280301c051140240e0050020078458502a03184082d00441170300041020802d03107100c10305c114030400484010341c1a0103800c0030010842c4910501c0c6014580000300c540800719000304d40421004440c0380303d20300135400c4901202821103a501c852080f401881c005030050358125070303d002502d040c0d41b15544130b40391228001000d0319850741001c1407900300300c001942c0c42c801c1680c03610784121040c01030081c584c05585440000d544600040d0200c1a8840710540c0101c2d68205001e1812602ea84250b0064020b4103c00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 629455296 1250 629454046 629454103
    0x150a150807021608030301080c04140a0b030a150b09091222030c2405072a09020a030b01021005060604050d06020d06060809010e210d02040504060b1914030a090203 72
    0x90304240201205031094004214080c5024010340c000f00c0c2f018140b40103141c54002d02d070000ba10110300015098032480140500041c1c04070410324400010b1240000c6850f14541040b140c3c00028158036196070021407a8071140c070000003240e40d082443c2140c8403030046107a00309480d05040f9440134203c1c18501c640050102507414940c152a00c054811031900b001003001513600e4000c1910107815070300300c00031400300c0162411500190f003403100d10500f05650f80d0000402a60f1048428900007900c2c3c009250007035804020640d14082d00803001d008a1801c1000b0421038042c920806106500310442c0e00c0a2101c41d60442c3c0c219040355005008680d12620090501071082e00c01c00444d620349940388101e080c0109022900c40025460303420701400e1a003103500a038004490102c01c0b00c0c0e0801c40061a42d48034030500c402440402d05070790300c1d41e95080c0f00d0103500c1282c9840710b042c460701d030000101d891003032800c580d48264140c200090307051650011030302c2d040c607003140d8016551180d440042e20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 629456546 1250 629455296 629455303
    0xa1a1f020f0f030a0f0c050d0c030203090d2003010911090403050d02040e0103140d0206010911220e18100f1b080402040b010e01051b1c08150a150807021608 69
    0x40704c152141000110429012500a003a002015003030b500801c9000d00518402d01103000c0d071500910440b41000c0100c00010380c3c410f00014111018042c8140c00c0030324070413401954110715000c900130072500146443c0c280f031845070590698404c0f1028800a0700b010300078401e807040040030840443d1070b03640391040707a82c03602000e0206455400f004040c1d40300189001a07503142185080d405440e2036468560110007605185012402100c81030020300d2542c11079081401c014168130742c0b0719584a00d0300142c0110803102421042c298070f941440500b0000f0005141000d1011501f0000b0384509084020b200402e400d19010a180b40c03500f4412014a5001d000a4041c41c022102080340716100c00040d42c071040315103178041c04650280104500c00348005401401c20044400340c0d0142495000c3c29813011800f80f4408020440702014440c1031102c42c0244035402e542594403158050402200921130301c40b03001c21408200302c500c00900f01501c203000350810514140d10004405485541705500c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 629457796 1250 629456546 629456557
    0x301060e100c110105040503030c070e161b080708030a020a110609070b0310090c050a120c120e0c0303031603050c13030209071707080a1a1f020f0f03 66
    0x18260100c909501c0c41c100711048010640d585565500020315074940d01c03409a8444540d0500905200c0000c99480501c0241001880304001d0000c0703d0528800459011001e410300c012181c0c00c00d40200e80c01d400001c01d100f0703001d0307414080100340c02503e00a4002c0c4110a00201a40c4011052100c544d0164015000304125a01d607080c0445802c061140c1d284812604004ca56001c490100811400040159000400301d04c2050300e140d211210b040c1038400b0804020009540041e81864580d480003004054100d0100180410544058003d11248072051840d5031103640d03d42081c0c0081c8100144108440007400381c940f41d28250045a0841003003494440c0401c0c24007002801d08a0718008940a10444020014801e0700715000d004640c50010840e109000e0b1502508252001c9441c003d0310a403900da680e28070320300e4a0f5800500780c400b0903007481040006e46400300072039502c0e9004050b800785d403c0003000c002201e0a108030b2070030208000c440c201d0302905048aa00100100c000c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 629459046 1250 629457796 629457809
    0x3060105031b0430080301170a0204060303080f010e06150306031504031e082401020a17180612061c0b01080d141908040f081803010501050103020a0c020d0c080a080301 74
    0x10701c0e4039103144d0030590541c0040d4000c103040c00030001400712907640b03140000c00070280011140b0856556012500b115510381054010503650410462440c981c203049a0240a01c0d1071200c240303040c01808101c405490341c03100c2012071408000907040b6142040700b100301255154a00b1007505183c140038064030802200084800c406900400300e450040345014043c1e46e50880c11002d0112600b9001030b4086a11210350450140344810b2002c106000c140e00c024509a4219654603101c685103901402540c15599000e8642840310503c640001c402d4150b002005a030031070800c2da4550003212030050030f0031004102d85031820001c244100700042c0301d0380340741c001e480301e80604161078409074540c011814040c041010412820325201c0c800c1d4002500244903c8123000e41c3d117400d07594001d81e9005044100340403030712004525440e00e0300b4092035004040a0804515040f14600d0003850000c20701700c040e014100e0031101c141084510803c62008060240a88a208441d864400c01c1d941c428440d58 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 629460296 1250 629459046 629459099
    0x40b030a030c201e0411030106080106020c1e01030b030f070602030c010509120a0c1e1b0f061205130203060f04030212121f030204020c0c030106091103060105031b04 73
    0x283d82008490000c014072500a100d42d004660440c0082c001031403409406030001d84a540d2080032181c0e542c0514080c0180f40c894070303401d604100c1c0092030b040c8d1807044140304008a906082d10140c3c8c2c1c0141d028491000e2074081a00103001d0042840d0286135111426a441030b0f04000455070f0b80440584215403d100007480b90b031f184c0c09a10341d03850b414450301902c180020004080d120f4043d6141120311031142c050520040380a2080300100441c115054424200341c1d940014141100c808a10140c41c001980f9103e907428048000c01d21000d50010507034a0356200e010650708a05400f010f0f004d540d0041c101d03089898554103605810728151401c60141c0b250494003001991050103a9554404450607640c059803540d030f0580031141000104048015011008005a04c580c0010700440610302c0c018101012000103140c00c44545901c1107440324940307540440c003010080c5c2200d420043c00d2800940720748034410310714585500032860044001c0700180010b076154944d00c07005c201c984440b190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 629461546 1250 629460296 629460323
    0x31e0705122d09100f030e06010e040308090609030313020a03080a0c15020403050607030f0e0d050c071e140a170a0611030609220c0801050a06081f0b040b030a030c 72
    0x65003068020b00f11001d43c024000c96100c40d889104542c0041c00da442480d000c1016042c0e00c00301818030000b0307005510b0030b083c00000c000c141030300012800e400240020007080e17185480509113403240400b82030105041000f100030001e5640b42d00b05107000c0c41d081042150750358a5810040c00d4004101421680d002c42408004084c1045200340d604681c0c0100242880c2e0343c64100c114018000d54158000c0e07075030380c0d80440d140f03203508012040744107006441d081ea8030010540d4161420502c0e51014940d402101c41d490340340002d07503910300110f4070780d0501700082c1001c0300005000300b15a03411002c0200f401104141d180d5000044500c40d0900a040403c0310810022020305a84001c440d6207400035040e80100f01d684c0d4030144269028041075207c286081c81302d550307156040015038400b0800c2c2c0c0d117800501481010a1098000a16034240182002600d228001c40300200354007030703407441d555103c2e00c1010a880b07540024540440080a54030030080360716000e440884600815120000003542 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 629462796 1250 629461546 629461627
    0x60501050c0a03052b09050f0d09090c1e2a110d03020f161502160e060109090207030518040510051c0507080a03020c03031e070512 58
    0x211007203009018060009010107071801d80700e642c09004880b070100c090501001d0f49181c0c0150600d11300042e10f00125900f015400c2071032030711038450030103c090f030007100100601d9500205a01c3c01c070342d541280030a03001d030042c8050390518001d1840d0034481c0d14010440607250ba118203c5031152101c0a80940c00340d486401c0c0118810086c0c4004240841d4214184170501d8068100c0341e000c1e1003841181c1c090031070381800b1410301003c200c641100d0740c080b01040c0030f2200403a86070150381220348003c02e4903607203044c0c0ba400c44641c140f20740d80600d044c07600480c031940d10070b0b00c2c01030103450300070420765079048907140013401d030342c021400b0703d0b0483e8440c100080c1c10701d0240100c40c060580300c1c0807148928100804c02030175003402030790510745400155204000034814406c038401000f030030700604020300a5060180c00c0001805000b40f103a0000c01001a8885880b01c070704119000298015481c3d0f0351070b2800f146003004c8540440102d00000c80e90381c44408411200903128040c0510a45007102c1802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 629464046 1250 629462796 629462807
    0x50f071d0708070507060e1c050c06060907020312150307060f1706150a03090b0a02031905060d031d03011b0306061103190507061a0f18010b0310030b010e0109060501 73
    0x10340f50700002d5410450b000209100350080c03543ca8020300709865202c03146413000107603525000c245401184000c1085440c2400c1884a140c2c0860180c505120503d420b40001351a4400d502c0b0140440c1c0800003c02d0240148407920060002c4c0502210039441d00c540b0040c0c00d25040c0d407040b400045d150a00082d00019100c125170181c000a480104c02d80701c01d503810101500b0008416040656030752100740403580805500e4000c50070300030016503e040408951103884900481c1100c024204810b111440d103d0305030501d001e58151800000c2070103041d112540c9048091100b641c1503007440c603420507504065040314503444194908028082e5109415168032071140b1507402c65400034400000a003100e4415080e120215107031481c41c250269880e001110740e070329190782c94003108003105900c41c1020803050250401c11a800d441c2d81c901000c10b540c03001c005001c0c0401c501d0010000c03c8101c018200c010b0b02466000103800748540c0c45880c00c1110000074401c110700c1f03c0c00c12100264a50140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 629465296 1250 629464046 629464051
    0x30406180507061d0d080a03050105090f04240905010f050601020a030203040b09010c02120106060206010f14040c0210180b0c04080613111e09100b070f050f071d0708 73
    0x3802800e290741c82c00d4419134112485000c440c018031004003244007580d6070200e004003a02e21030f048140d19280f8800f0010304039441600301078000c83c00e510038400440004510280c0c070039800001e421b074501c02506960103404406900010740360070f0820442c20000107401500308001361140410590b0344010049a6444407504042c0c09031300f007040240421001c55000307005141d01030504030940101030303003c1141803198007051216650350f00070600c1110f50601045004100038450000b802c0d0400c100000f10300400340030305124954509442d40160300a0000d8805070b000078208000340c0c1c8807103000c81c403400c0e0000000c40c1e2520f1444001015041240d05640549000b4001861295100d8001e1480c4922050003075032800c0d82e130b01c031b2444107607a41002207500c1d11504501400302d4200c2c80c1400b1a002c0e010300f90036107185c4210409d002c00356030317601524091500118440144085401d0080c100f0312904500c0881d40280400411061041c0344090503429180d401020360f0b940d080005c03603080d84d05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 629466546 1250 629465296 629465303
    0x303050a0b0604051806040617031e040f0b0a0201090b16091e03024b01030c0f0e130207080319090f0f0320011b2a0c0e01090203040618 60
    0x16851301d1040d100c5085c0000d9100c400980001512500c41c06948111801000f441c50aa400000c4541044199010151240c4c0500036003d0030301d03040c0f41c09000705050300d004800e41080080743c1d0311182c2c0e10035000348110301e4105441940d1402c1c02c030354511151200c2117001e0041a10280c00080245000042c904558240c100303641e03c880c1541e08008079018030b000c0c0754183c03040030070110604012450300c2032059290801d8162180c4244495207070003a00e003441c1941030510700102d800d000c41d081003044922160074502014075400d10300000c2ca0ba40306006d00120070b60b1001c0b50580c1000302020040d8054a0302c002a101202c04560076142a29903110340200491020607a02001541000403a0100d600c6030070300d031041034103801984402032111004140700369100d0362110402c8111041c10040d1900d036142036281c55403261a10018400d0260703000084581d52804039007804941c00c2801c1c00307049400c450b9035841d40d4509581e0302071b40050780c05880461600721520891200e106084010329417 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 629467796 1250 629466546 629466559
    0x10306051504140d1e06050f06030d031d19031803080a0c060b030d09030b1e060d1a010312030b0406140915030a03050c010c02010c02030d0e03040e040303050a0b060405 74
    0x1068102c40403103a03114652074004132101500d0b40003e816205140e4100148001c650345040c0030705103242030700c0d000392420780e50902074000e201c0f85840204009444460300e040110320800380100c091040610700b400d4281c4c0740070301800e03190240c11809481c030010f4020f0f0741e0903121205580300d00d69044194070004001100400000c1c3c005401901d0a8031424010180020120001b101290038400712002e03d40011300154030a004001c16450025040200c64840901100c03011680028031000034000610400e03c4252050800c12040104154401c80051034202c559480c078082c05900359004548010070b0421100f50900d040c02c3c8120012138107041c0b90720b14209260340602107120000b4200e824421840507046442c0d460401110405501c65a04c4c079a0304ea44ca44031a90031074260000c542e04690604103000721380d681c00025144403a1100400040d06982c8040440c41c40c0301c0c030360180172a96280310402040c10341581c0703c0b80c464207407280e00f488403009d03000401c0356920850003483e03072080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 629469046 1250 629467796 629467799
    0x60a02090a18021c1b02031914070204020c030318010b010e010302130314030715090c1a042103020f0c09010603090c0b0d0905071403150a1404060b010306051504 71
    0x36464205032007000301600d0040c40d0450800e40f25141811113501206443d881c0d00348100861000301c50240181d2161020714102001800b5501401c00d803110000200500d64504d000701c0078000085880e01c0327a00600448d525100c520410f5180d070800c1b1003c440192070000c1c0b91201070018000c0740c112900503594400005144130048d802500f12040710f04002d5003032000072000078a240e80300c0d000d040492005648440c41c9160101550340301c034020702c000c1810703ca06000000c10507900c030001d0722880d4060b0941c0024140030100305004e590b2003003100d003110a02d100d10500045c0044841d1500903800d80c0c19010f810306400d030707075078100d1619140c112040381e004000708c43c80f940c0a148014410a00398a0490f600c6a10303a915130040d243c8440d03001d41c0c030303100ca5040003800c124101c000c28100110030800c0480314002030315400100031001d00e80c0c1d4400000b50f020307030041c0c1c0113407041100c0031044611800c0a013480401004040c8001e40030a1400070040346030f15100018209603541c03100d110b40b406 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 629470296 1250 629469046 629469059
    0x70f18050702030c120405100e0603040803040f06230601030c0e0108060a0905010f050901051801030602090f031516180306090f020303030a022104050a030c0c0f090509060a02090a 79
    0x10300006181c40118081441602d00401060208415607030143c5501925036060008011240841c40c0800d014000a080d0360151034540f182681d51184e0880003230350310b036a07e07410030010702c1c0c485000c010700a514048040c3c2d4144607138003803081400014500303082150f030340c100194100c0e141e86100c00080b82c064004000158813036651660312080103070408880300e5a0740e425101760355003a0002504807000701814040390070040c4800b030052200312174004510080701080201c04c841804050011034000800040c40d85403581e1200110f1b40c098100c2d01c83c0891400c2440c4041e10903a007000208030355100c418060f9200d010a0380b00800d40c01e441e40030071032459880d5402131aa00f0350894000b28015200c6001d650705101652180040120260340d4042c403440b00c0e458070300c601e1425440802144240401718200003010403000368036080c040f2090666041ca22156203503640902c4a2010103800480c01c41160307000305000d140284100c89282c0c44040c4130b4000d0340141103c03a50003030072a80040200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 629471546 1250 629470296 629470301
    0x61204020d080c03040b0405040515100302030a020910110f1b0105070c0f06090f080303011220100e041b020c1302091c0209060409080904201209070f18 67
    0x100e481030701068500b0407030100060135604194803c0500300ca02003810082824180241780e800180305540c003000030f410f175000415200039400c690b420180d01000080004a2a0741241c0ca2040020300078070740050906030041c001c0001c00e000308a240070f1100c24000030103002a00903031000604d02815406c18807400111081e40000070240c0720b2184000340018034405601121000e0843c540d90303035076498200020418840540e5001080992041004000140c0e0748039071541a503500c540708004662100510900c0d034440004c900b64000040039403030250030741180549602c80c606070340510200c05c490b1415000c40d0301764444000540c000992415140c82e000c2180038080700c54280040c20700c60307a80089240c205c0140b5141030507100c203030207690640c5808a112503210200310f4046c0903803191640c4581650103040b04c0203010303d0311600c14030000030032441505050303540010441c0d21540c0f056079520a4082c140d070601441c0c002e180c0041200300d40c24842605450415030940750744c0e40710f0b4490000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 629472796 1250 629471546 629471569
    0x306070f030914010b0108010e01060e0418020a0b0301061b0b1b0c0a03080708090615040c021221060108010605030c07020a0e130506011e030212011103090601030b0606120402 77
    0x30141d4500d0042d0000340b0040910310fa01c40c100000041031408200003421000040c1c00c4400c0c042c1050004005003a480359900310024011340e4041001e01c0044100480c190201030000d40c812240c410109e0105152805141240c11555480a001d02c14041c05608400d50b01800b610002411001504e040310b510a81d800d4048080401464400980803090030843e480200b200000d4000041c8000e85a104403002e03003055949015040034102182c480350851910700945001e9074882c0803030b250b064024170480b0000d41c1038107865991504030890540b103c0071424108000452800041401541706d2200c1c5416103027143c9407149107171900c90b1030742d54582111008aa0041c120303440465404005c4091078007901c488090903102848500c0c005090081c1600070200705c510890507849108640c3c901c1604032601984e41020540c0c01048982c0982402c1d951680e890b4000400d000d442000056010304a901030440c1d81102d455010400030740d0710941080d04a4145104082070151070002032045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 629474046 1250 629472796 629472827
    0x6120206070c080f010b010f050313030c030908011508010e0a080f180a08031315090302121203070504150c0f0b1015020109060b15030117070b0f091806030607 70
    0x145502d03600d808040c0780407003004108404d82d46464a10040f56042010801d0080c01d504007182107151840540c6440702c8500c001a003000704203644032003494015801035014110a400074000f10384c1d44200d0442e807840300d00c07452000390b2814128141c09580807444500c40380d400541d0300d03e04211240c08040c10b401c0b80e81101501c132078926000c0034959a00e03074590010034858014588803101518501e081d1130003079005902c841c02100104041c0d40d480750400c000e60b6811038480c0801d01c0003460b45440d04180c213102c0c06424000109005800350003402410403150020203420a6007404002141c2000400350700821034101145001c0008008008960380f20100b9501d12114990b1040b000005d4550042007001603503440b074140c0705015481c0904000c1c0e100a440b0042011180e40040b80b09100500c22002100c40c9282c3d2000410010b101700c034000c03e424940b00e9201c81401c00c11000f80c2e407000100a10031109089030b40e91222003402d48500c40c0c540140034120b0f6a840c400709403a5041100d2094 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 629475296 1250 629474046 629474063
    0x1a0907030605030114070e1219030c0b040c18140c21040606080d020a11210604060f1803020d03050703180c091125240e100612020607 59
    0xb18094801740b140c440900420a011201d608141401074644207102c110341e4050321907846a103801c0c000014205440340665a9007040c001800d003030460746805c07010300c000c1006030400144418400011038103001c0d00c4032507107841070312240500d0310030895242441101140c540c410025003a100700c03074081d04a80d0100101e9140305c0e900320f4001c000601049500b100e086545440c14440801e04000155529030384d40020141c00d541919041c107400205032590303228290f070714021581a40308201445900068804949103400c05150820103451600c5043c00c040e40f610916170503c8909030701c0d000c0250340540103440c0102452034110080c00d40140240245034807020641c04a040282d0140f1032940510301d95191141071807229820750b034418030441c3c05c0030020b000121140c0c207400115594140c60004a041c61a600d28007042c240341450107046c0c08402c0d07150003c1806801c0d4108614041d4030030180c0d100810104888821100d407801030195201c032440c0c0c0385005050100040541502941c05ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 629476546 1250 629475296 629475299
    0x11b08060d1a0f10080304050102060c0313050714090a09081c021611030d0c0b0f22051e060106021f020d090510050a0204030206190c050d020a151a09070306 69
    0x241002e8880555005034114440d60130000410580442c1c40301400c6500040c40c501403800000179903c92015004018003000040400e6003003c0c04560f5412146c0d0080680341c20039034403030007486242c0e10100114080e0032800e00141104140e4410f4050b0164030403070315130804041d50b4a110b0003514100c40081016805c00404041d50310120301c14200c14815010765100108100c01d05040c0805560040e0601c450241e20348009811161520343c4015141c01c00e083c180e4540d500b070b400c0e1849a05441c80440010300c0c07000240000401c181094040503d0b48001244a103401d013952124248100c10040c2c01071304106086071410994001100140000075003080340b03041409045603000ca0b803c4803280e0002000c4180080c05000e501da210201050443c00d0610b5900030401e0342c46504070f082c0c02c00c540c06c0d008280c4580503d495401c51034102040f501180490000a50760b45109041a6000c01220382c008802d6065805103640c0d00740e0718402c1c0c045000e1024180700b40444082c0c180c0c024035880d95030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 629477796 1250 629476546 629476583
    0xc020f07150909062601020f0f091207060f0309021f0503040302100204030807060e3c0f0a060c11011109010e121209120601090509011b08060d 63
    0x2030032014003410308001da041e1010940260441110354040d0000d0350411008000314001c600381d104d0340c03008040f80881c42d0841c40d0301050081c482d44150290038800461a081c0510f05040076248041c0142e40000090641c680440d40d10384040c800d00300021a06c805403c0340c81d2103500103000307407440a42003c00804c500c069400d00c8400c0d9417000c80001ea000f2082005241e0f0400c4046003651140d40114a810300f075496003020392040307540207032405071103417182078030b0502c20000c4038100514220154445581540340400107c2189810300b803248812380f440e0307000135000c1241c040b45a008401414507415640d501c1014091182c80c880c14002c80f0b400c0881a604280550042096a01903441d90b49071002e001401040003c24094010550348a9203915000009048030f42c800014000c941c1b0343c4084800100d2001c11800204240d0040b20000191040150070041c000c00c01ca200a015111114207089040a40b001c801e100140480002c41c00505001e18162042401150307140071a121400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 629479046 1250 629477796 629477803
    0x604021c0216060507080408031b1c06030213060f03020405060303090303070507061e0c0b0901020c030703030911011407110409022e020d02150618040c0303032307030c020f 76
    0x1500c26801d107481000103070403c110707803159650281050525101078100b41d2920f0b101800000c142c00d008004170400c9080c0d21403050240c0e454480d00c1c02c403101611024410b4440608001c0c48224090050003942a80c0c6903040d01440081e641d64402d00400d8a1950b000c0102500002c0c040540602040000c8840c9071400d000904000c0c1c01400103000c418603000c40140004014085907203800070a440d254a071a5100000304195034004008050300e882e0300e0901070082c0b0441c26808480e11000801c0340405415420a280c803d018074403501181d0203000040d2000c0300c1c4104600c801c80c0040080d0000904201840070321410058000118000c0e40c1d404a1402601c818001c284005c80d80780030044181d40302c02e031309140035076440606050000d40c07a02070f40c0e1f080b00020900074541c00c0000038825480d9019003118482003005201c40b1380c105801c3c07503d45203049000a40c0041c0c240780e00206c9405500408800074440038095064030b0742ca81900320020010712143e4801c6000c0c04016244006040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 629480296 1250 629479046 629479057
    0x12070819020d050a0f12080103081218163002120106030606090e010b010327031125062105041a0f0106030e010504050607080603031c06030c0e040b0604021c02 70
    0x74840b07001003424900304003c0200d011b40b05002042038003001840001c04020560304451144004062a900c900824155207000c09204003180e02c01c3d40c80f0401c413445160803002c02c440381c0302e07134007007600c10801000000c525910f0400f20307001c4c10140d000f00c01410000a40001d6880000c00002c03600d840740d90398820754010740c0c40103102e980c035516a01d194900030f1240c2000094242010071425001c1c000c0c444c090030074807a4504074501c001c2c04040915002d000c2e002c0c0b200d403c2e802a1505511560000d480d00440d009900e40c8d2120134070303004590702e4061805842c00c00c075190a8809640742481d00f01d409800020812604006907905059442001c00a02d50080f00740c1c005030495581403402c010201d130507500b800841030b0304084c00c0c4000306030042541600300c030480ca490311aa40c0c0d0040403038030f07500c06d9041e20031004401514500354002168001029644144110110030b80d03109225030b011002554090704640805010590524066000b404800707188038040c0c10403014041c2c02d0b000c0740c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 629481546 1250 629480296 629480303
    0x30d0c03020d180b0627040c09060b041a0a1412040215040e010302060c0f0604050615040c170a061206050a0609020403150c02031e0912070819020d050a 67
    0x201e0b00c051a03803183d005002815442c4090224003a40c9502d0707101c44100040c2042e8041c81104151140b2036441010356041900c40302c4410380030341003d1400b2205100684128030b840b514004011a48813a410111030840c2c400442a5181d030125800b85071143e40083c020505104103807a40031f04544900d8017404050580d120040e40341e191134010700000441c060200c00380c2e800f0030482484075440c4000d82a0540e030301695016104d800081005241c01000e03550b86c0d400784220f0b0100f00c1008000034080384240c0002204200000c400d109000a2f90000004d41e00401c2c1d000009000810701c12030701d242d00544080020511a07501c60060000701c2d80d1840c20340780d81d601c4608114000e01d03030340195001010342c0f0f8401c51526103141c171400d81c48a48000c002c40f00980703d8054503a01442041507414100c0600741c02000101c101040005a80c02007480d140140700c9c0ca00d04254180b03011900c0022036440a02806031020100d205d511a400d003040c040307034442102d01480c1c003c100304203d6240300a21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 629482796 1250 629481546 629481551
    0xc090d0b011d011e06051c021b1b0a090b010215070f03051e0402060703111b031006080d050a0908100b1c051e1c0509102a05030d0c03 59
    0x8400038000e02d128140c015605819030a4a1051145142d00394030f802c54106180147e03c0310300c21505210400c9041504201803030003c06c00010114541040c00d10b50544e42003141d00d01c4028040036100d842e031341d40c010307503120080070810003682480340c014030312145051040c0d5590045844120302c442c101030382c00c8000180113412224615415128150b004504a41e4a40603020b4032012030b003003020014002406038001180c100209401107050540c400300f40019070700c150288481c3c4003074210708000ea140c0300388160611120440e9451041c0b40039140d0302c0c80640b640c82e000071019980d590181088000f0040d44010000d00300009122815100420302004506603411500b0030690840415114005881075843c450000d2000034001e040d052020081c1107207195841d412508011044450780c00b00c0f0b0300c030718500105990080c001d11068000302d0b80480000d441200807a041401203035a184c1003c0c042840381d1030382142c00107941c076140c414412280b41c007140d102003205a403440040400030a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 629484046 1250 629482796 629482829
    0x303051b210301080d02060105030a1b080d0c0c091b260a05010f0e15090711030a020a060f06030803040206090f1002060a0606141903060519050a150203030c090d0b01 73
    0x2201804501907441c071506c010950382d410300d40040d8840c540500006e003405500d61000d000d025803600701c40018590314043d1802c140180401030144824a4000ca814440407107011503400f50070700c9001d4200c4010082d458030001c099505a0302048181c441501d40040700b5843c0131010070710003210f03108515400c8089900d514101c400154080e05403c17020480c5080000c01003410001c0c075403030082041c12540328038107849020046d20010034100314060b5038000082e210000c00c2e00000c1e1285054031440381080441c0180a105040300d8180c00010580c00d01000072501603d0404080c0c000201c3c000d0010b46000103c0c000152048541d518290250704803200f008140143c0384141c0001b0803540c284091895144c040c0000184203d60109940d01d800505000c000d03842fa0740681d025002c050305440100a24958403510b038520340c0711f200d100d00007551003c944031460201002d6481d595800850868a44001d4480c180d0000e062681e04819104020004600c1c6040c05030300034101485041ca031079 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 629485296 1250 629484046 629484059
    0x90905101a1c051b030312061801090c090b0a09090f020903030415120b1005030a09050d0207091b020703080304050f1e010e010b01090501030e010b0a060e01020d02070303051b210301 80
    0x1d0b04410b000b04c010f58015642207090340340071044031103601c040c0c0710300e504560b29076000a1440c100b98150001c440040c2c400455000103550001d141e506158965610090381d03481031213218862018504005080d1143c1003240b04059044410380340105200981007119100c0828a903030000d80c0034255852040300d51040c01c0c1e030000c8a00e40001c0903090140001c00054010800215614203650108080000040c540803402c0d445032034000d510200340e40b4010307045a8025540d0219003d0303090143c0c030340a50072a40000318030811304084850303000703085114030b95102c46066420003802550613024052188400035800c1c002000709181e00b04c03055000c2c0101c03404003030071160701300c0c0741600d103a1410106074181d84e00501c002084800920300400c580f51000070060260001d401d040c3d4105075880000304140e6040742410606090a80c01c0701c141001070700040f69141250f21015000c20020130401980c01070700c10f420f0000c00ca0010440d075504144c02c80341d54902c0e040d441e2066230f00d01d003c001845035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 629486546 1250 629485296 629485303
    0x20a020606100e100c02030307021810060203072a0810020a09050f0d20091005032109041104030b040309030c08072d0f030506070801090905101a1c05 66
    0x86020b40e2904501c074042c48404101c2c21540e81181c00c0c240700401241c1c10455808000300c03528258040c01904545070608001062654240c172000c1511400c5500410a24030000a440c0003c2d0005c408051864115081590540101c00201c0300c0492288002c00d801030200407110148418010042c2d0318002400000c0c0740c24201e4100c01c0c4104041420241296079000881603650781105e5504641e08030340640580080032204041d80128081c1c04000480f4080900d4408884043d01655890040c0e8200e8081803031903082c109440070300522140c3d01034181540b0109510011920849c90700d80c4071345404018020803541100051242c8901f4001c008158800100601c0740100030b001541c1844021181c079483c401c901c03d5550704018010f0909104603040400034143c45031042d0000e0349038201030381c9401044411901080404d000000c200c0d08a00c00c1e0303c5240d42060141403240d500342d00e0031002d0960b00b01c14980d240482e801d081100d80d0b82c4005030440303891140c0030341801c000b40c8c50b0807402d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 629487796 1250 629486546 629486569
    0x30c08060105060f03060f040f09200a05030a08031e09010b0f0105040f030f020307030b01150206090601030807080a03110f0a02060f0f0c0a03060b0304080304060b03070303092304020a020606 84
    0x40d20044c400020f481e046a03003660740240e01115121040b400c99000b103002880d140c03100701c0b8500d00f0014920240804803110b013044910001601e02e000c440c940c14040060903900c1519015070144002c02c0c0480c1e5071501642e009403291075040700380b4910100109400c601a00c650440d0307595010040e85030f2406503220281c512023800c295080a10f001c140c0f009045052201900202c00f94104200710351f024001c0201171940000980541e503103844481d075030b202510f0b962101502c1b9490200718061400a001070480760f00c003810614040c2c0b00e03035030844240c1040444c201410b440d011149080b21000015050954a20307801c1c03070300c5d86440e01009203490f0300907000320090012032081c0001040c282821036441a818825665210136180c401c80c0102104e80c80001743d0007000c0180010050b03048000c40c00b0320b000d00c80c2844000641020161200c0152100401041c4110030801101d00100d01d202d4503603080c440e004000b440650042400d90344081010030043e003202041106900e841003e002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 629489046 1250 629487796 629487799
    0xa020604033002030d0903020111070b1902190f0e1503091b03060103230703150605030d1d030a0f05030c06091c1805120a05060c0703080a090516030c08060105 70
    0x400300c002c4408082d4680c8121000b103e0400c0e00c0705114400c3c98000d4220460074604a910715035504100d061160b20710308180d5000700c1858848540e09500180c6000f95404640c0d10b01c0c902140c008601d400341c03180d5500e12107510070701604100d0034440381c1e070f25004014408408880103130759141c562102400c1086443c0007100d90040400309411b0342d240020301c40d054a5128512441041c01910b00790728064440aa66280d0f10030084040700b0030404103010340c00040315120603c03696455100305a100d480340d1191000050011060840f072146480c040c80d8a00009002e039402030100ba241c9840700000c1c0c1c10141c8465100007a0320155820420056070710031401d81c00303040b11304103c00b80f0030b08844025180300100600207445412010100b06203078000c0c407008101c5240d8a00b002405a00c5000c002020b807018003803e0002139580140c10100c5d4032660b8107558154150303994030296401401910340558052290820000c1c5178104000d030080a140104190014103151485080c0743c203c0581005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 629490296 1250 629489046 629489123
    0xf161d040b0d1203360303020415050706060501030605011706121002130f1a0d021b0f060a060b120417070803010f1409180a050d0c03030510150c050a02060403 70
    0x30b4800000e01d030900400307a07a40030041a1200c42c5ca0400310064051608600000200205c4120f41150800000c280c22403160320305200196403140103404403410341c0b0030b0700e01184400910b04452486451031541c0500c0041411984428032640d03075181c190551a010034065000608030b500301e080622100041080e80303420010a81071140707944400555245d00700c00380001180511864100b0740580c3c6c1449400f0410203140000d50060030b07668402070005081d20b0007800041b90f9540c141d0b001d8103040d1403030400c0c0700c0c0c81c00d05041c84400162900130001d990002d90185000f4203100740701c0c01024000c5c0907c207680e03100d505040d507010741d052040c0e10118607410342c2c0c81001d1458032881089503000d140217105803600c4206598482c20080c2401005025010300421a204150011000c5820b64040d903420407803a52602a008542c200601503404080c480703400f800007592043c500742408070b200390180c0c0d071a0038a9070f01003000b64005800c120342c1401d801c154890300230b1441c810204c1d0410101c03043c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 629491546 1250 629490296 629490341
    0x170a09060b060c0c090a091703190615110703050610030212010c0e040c1803140c01030216080c03070602040f05180402010c030e0307031a0f161d040b0d1203 69
    0x103050707440780d030b094045001702d00f175000098a2042d6540401d1815401a8001c52401c00000d14460b0640c0300725050340079840030038688403840754548545402e50b8004050980c00d4200d00c1019541101000c10814040c0708070032000c00095003e010050040e180822407003981c90940c41000240c805420769840144e14040c1e5855500d43e00c09684203c2c20400e4a000035075040312801182c490003215030121444284035000010008084480215861082c043e100a108000011001d91040f60000728101994900c4000807460150041100211030802c2364030b010603998511701a42c00903805982c211940c1d10041001342403138080c0b500e90303d40b1609411200d00e025400030b0701c1001c0200b0043c0820100b01007819007500c1c10071010700a9a0040c2c5500c02c00b4013480b04040c0c1c0d4800442e000710300440b9010102d4444030040048540746103140d120042c0920b6200485c80130759000304c0c0e440d0b500680340d40400c4150f84900380f00c61000350040c1c8490124046949004c1c06450080700d0003078800e500b1001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 629492796 1250 629491546 629491567
    0xe0c03011b0c260a020c12120d05090325050106052d0102031b030702030c010207440102090f09100501030e030c010e15060102070b0405040507170a09060b06 69
    0x1140340c60b690310090b28030341046409540d614010740110001000800051100c50345038001944041a00003100c2c2400c0c05144c00c0f04054558070050000c611200c818015101c03000c88540003e1380c17290001040303c2c1458035001d00340e58018001c483c03850070600062000303024880d0038017800010b448180c901d904c10000d000740555000d0f46a841c407080584600d83c162905038400d10846802ca4109900c06000c00030384910113450f80d00980c001c0f4400d01c140d0300380c0c401c107500109202d01292550290010300e645003013038901c029200d50380b8201c1e01694440c5548001e060411122200500007000140c8440404051101524004401e10320440e01b03a010044071486039880b0005035503083c40e0205050188020b09851070240a080c2c2003c0c2d400c02039522070b200c0c0700040d0240001c000c0c90b00762803203454400c016600d079002d41c000c5095000702000240407a0519400c1160001c0481c5000111099075200c400d030821000d598210360503403985c00300070a0148a0185a01c00c0b141140c074241f0f8840c800380d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 629494046 1250 629492796 629492807
    0x702070e0c0d1a0301052d090d050a03110a110c010903050c040902040204030204020c06160804030c17071a07020c030c1f09120302010902130e0c010e060d0e0c03011b 73
    0xb098180080d0701d83d0002e10703c101e4181e582d940c480e07501500034029410034850b0752000094401078028604800d4960340e5080c00d0030103119008100c0040500800c400c502d4007102c5a42c07040312a6424542c0317490100c5c00b8035036078800170702005005136118503c0c0b1400d062100d0410040d491054100040c030081030010900100d08601c804900305c0f0000b400401c0361001c5400780c066a8800380d803151010481489008010400d640b1401c1d007070b0b0308248071109001080c1d42c080000d4a0107070000781008440e40025114601840c074172085010440d0801c032282c0c1c1c8441d10865420b10000380840c810060200164041107541c400b81c004078060006d15200c0008180904d03041c801200d440c0c0b91001d80020080e000e840313000054178501141220204c0c5e9804e0290182940c0f00f4124080c0c4d07480100c0c151118500d2041d0440307144040302804044218000464101c8805c4000540c45081001074034501885449480311401e400c801030080c1000403420142103030541c403040070200c800c140a0607180f642c000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 629495296 1250 629494046 629494057
    0xf1101030b1f27080a11030d0c06020f12180105100303081b070c0617150609011101020d0f060e07090b0d020d02090a0602060f0c0c03040308030426030702070e0c 71
    0x1480c101900c2000b241102001c00c540c542da10650500f8040f01080400001c81c0d42c5540d0fa003c0c01c0c05001c0402c9840c1413656034140740c840480082e040002e135200140c03684e002841344e01d81e0499240d080c07400303094500d00300c0307241a40c454500700002680b6011030076003030003071070b52013030b01c62916541c03551075502d02030402d4400070031707808001a1843c1d6101d45c50740080e003a543d42d82c3c0c103c2c01c4400b80e00e4903070360007070880040d41e4071820b840303142c00b070025058018111a42d00111030260500b03003408410340040d2040d46404c280807000d55002d00c40c0b03c0400209202c0c0c44402c82d042400400e1031440d04011003000030303015140f44108240032006000c061300b004121500010f9504005030398041007640c0000902400c42c140da480346a00c2000038030690300041840c0203031864603100d00740d80c4541186585da03204100004415030818071040000c02c0000024682c054010310a006071b0880f0301020501030b04000c117000100103000700c04e10032402d038100241406002c004000104509201c4524445030040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 629496402 1106 629495296 629495359
    0x330c01060503010b10083103090b0702061219020a0305010512010b0a060e04110316021510151107060206060f04050c070f0f0f1101030b 60
    0x44c4540300795400d001700b20808016481c8400c3d0f4401034024952203600392440e901c41c040103520325421000b820f00c0c04c0d070307440c002c0e580307250241000e40550060000c03e0000e20800005884042c03c80c1c2c03040312182001440d0356507241524142c020180c1c251003c050021401d41556a0150480b505941c0100c81200401402c440c28a00300d82102d80103030383c8824030f40c504101d020b01844050010b400e01500110b1020502c090003401c80c2c0c4203480062402c40c141c04034410349a814405420400800000d45090b42011810006521000d0240d4101c110a1000039004940284001c00c2c0c00c507440000d948180c0d80d00c16019403640c4007124100e0144488828648a6282520030584980180c42060341400c105455808808a040314101c80180c44643c0c501c0100385d84003668090548101c0c03000101d0f202c40c0000405651440000c1030060a240e0748000c8425421204c0a8456a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 629316546 629496402 := by
  have h0 := BRFrame.cov_init 629316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 629316546 ≤ n) (h2 : n < 629496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
