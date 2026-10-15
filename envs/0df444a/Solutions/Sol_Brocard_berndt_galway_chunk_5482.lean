-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5482
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:00:24.967611+00:00
-- url     : https://prove2.me/submissions/2e916488-f8d6-4eac-9ffe-f09f5cbdd0c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 985791366 ≤ n < 985971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 985792616 1250 985791366 985791371
    0xb01110709110d09030203190c02030604081c06060801081203040b070507050a050f062508041416030b040b1e0a0b1c0b25050711031e010608070501090b090103 70
    0x42c002580c403401c881e80700d207080d901407040240a00700039544c2e03800800b82c0c04046014080382001280300781142000a98000d000e4845a100da40f15040300d5000303e002d00c01140ca180715503003110040c900c02d41d0000d14240e00e40701c01940c9400003450500c5088001124012400c0081100081825590f01e40c0054103050a903200c0406060180c5004e070188402026441619103e40c80c03800b001441c1485441d00d404290a034407805441c00c40d1800ba0821040e0202ea11030011a000801080d100910a0344c13040480d00c0da0241c070702c0301e00c411001a80c008d0f10003031404000d120034090082449980040f00c00c00d0032280d60503022100505d060000c0048a03040d6031490300c10042c0d6503096514000b192070040ca01400b5500e400c0c00c0b88200340c19140001413185441c410b5414280c040314440f030b52a5540c0303c0740c0c141091074036070f0002e41100a50243d4540a00c1411485901e080b080c1c083c403910306400001815030404030101c0c94100940c1000b070500103428820440c5032010f000319040e000c030030300e0007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 985793866 1250 985792616 985792631
    0x170f060a0801020a171305060c040e070f1e0e030106061110020901020a0f08120f0702071a0d0b030106080619140118152c01120317040f06050f0a0b01110709 69
    0x201c070340516103e000030054040e8005100c94100c000006cae1040d0381e200040e0000f25141d410302a0b600505405444000c650100350302e0103801c09a40001d124040c1500b801d4920088030000203003100d056404c46404136045e2143c914001d6400c002001d0440d00e0744a003145440c1018002070754581c902c070300051108800c0850b40301046501d105444071003000c442124201d04100301c610111080c21240c0134014131036601d000900d11112812101c2d0315a840f80c0c8145422640720401014002d1400d256800d0b40d21030000090b018802c0001510415010100d80c2a220071a01024181c03510f100f03444892070351101c018011008003400300d4100c0c2c29000c00008070505a80c1480c052240241c0c80140e41c07107441c18600310340c1510640e8014500c0c4e12155240720340d81e00c40d02101c19850004c4000b500080101201c110b4030368080e0f1482d50864014050300e0340d8070f0724950700e15090320811102405004200414040142d066000e42c640d0070500f400e01224000611104c81e54036001842801c1e49140c840e1305 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 985795116 1250 985793866 985793881
    0x10b04020403111527010f02070303200102090a030c050a1205030d0e0a0501150501140c031b0f101b260736080a050c06030403170f060a0801020a17 65
    0xc07070724912030504001c001d50b17450354450300340701709101000fa000c100201500d610b2a807000c00d08105481c1c1c941c5403000e01c051607615410180340201c0812802d59130800c90540a6580d201c210f40003144038070b044104103801d107024040e40000c0b42d84880034042084c0040b400240002c000c0d90003401c080e403c00180d0920076820240391050662021f0100e52800e0600e0700c030203003420462010340d182a00c8458106182c503801d43c1c2644104403c03200203400502c80982c8040a91003ca1100414101101c8940400034501400d1008103c0b0050000d0303540d019400e2142e8481c4442021401d807030401c9001100000d2780051858442d4008158082d1504000782c03465008500c1000407068854019008108111129282c2ca0380c03030b00b0741210f1b4089a100082d0203040007600c1c001081d03125018102a40c3c0240602c0060381019104809000d80d082c540d62281542200ca140b003001d42c60301c1813450f401c0071014032100351f840f41c02c1650141d0040140031107854010070000710501d12801c1401e02c40e9110907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 985796366 1250 985795116 985795159
    0xc11100c03090204020d0b1e0d080306061c0603020f0d20120a050a060b1c030f0509100e0109150c0b040206040e04050706270b0309010f1b02010b0402040311 69
    0x1c070025800b03032000c11481b031030354040c0d445421500c40940d5a4000001d01c0f01185a940b6601d00301503a01050f4441c40000103178669000d541c10200140189003030007104040503074a50070903024000a1aa501c41c1001903262884d1085405c03442500c0c03015030002151150705682e1a150542d410040144090400c203031901290070780303801c0d0b040045e5120f00d0b000340380c01c58a5a10761942954000d0510106180910b00900d810188120030914203000d9001c0341e405036842c070250585181482810b00c8540d070a81c8031214013503040c0c2d603540d4a213180c400303403200003514480e4241c109008949100c46100c00c02c0360001c0926a0032504802c5010140c0e4692000504601c10746d0050002c1e101004140420400d00041c514203603591501c505610280c1c201c010140441a04446c0c800d041d9200402c02040d00d140b001541c01c40c0c40613001054003844401440161412001c0c903191070500400500b4010754280714503c0140000c4a040d454141b842d02c035910011010601148620205114007103400c2450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 985797616 1250 985796366 985796381
    0x312150a03030905042003071d0306070e0d030207051503070314060112020d1b0c0c06080f04020103330603060611030d051e0c071110020604120e060c01050603010c11100c03 76
    0x185074587d50b80760544000305644121040640301c2c840f078500340c0d80d1a140100d04a41b043c0c1c00740c0e88604070008034604101c0c80781c1c0010310550540c02200c0c80890251030390306203040301580c0e45000300e40c1c03410414402400c6601e140350501e41000040c06100d141c0c1e80c0607400300c9101d00343d900007589a075003000201c0c3c01800b803040c0c00c0f4801801882e01a56550f0040780c0684100d000b10a20f003141ea6507110700b0f646d16401101c41c0c4120b00710400005006600a1340701404400072154140246800ca9030f980840d911080101c21786841c10f00385c01c1020941c50300502c80076000740d28186540c090f05040d801c3e0b0724000e40e6006292039844600180480b08104100c5080804c8491000341d1030816014940d2241d0200000f034a84003031300d007681700c403a0801c0090304568180c994024141655a600c0c1c9800700700034904031800304280d6a240d182151b031210080c00a4990001c0000313200e00b048020103084075002c00c240e10038400c03c807004d040d40c400040f03a2995800b540410104469200500407401072940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 985798866 1250 985797616 985797671
    0x90e190f0c11030703020303011a191701050301140f15100e0406060e090612030f0a020105160f02150a0906020a0c060507030203130818030312150a0303090504 70
    0x80400226504480c0e800200c0070740c00d162100e0521604551003951207204002d00a000341e807040004000300c02200800080119410100740d080003803840c40643c029076403116030000255076440b0000c002d0481c01d005801803c045000304040e811041c041030035150010311f48001040c2450018144a03401703030b4070600c500342c0200b80b02c1745048140c0e070142c14104031411071401a071400401148590040c4210140c0c65001040e030700c040d648420402110702c02030b112480c00340c00b0500c181c1100d400104060318000030310f03800101d102d1500304d4070070035015108a2040c003080b01051117080e030b07141c01051010641001c0f445042e003d90360313001e80c1740103480820341c02465980300160190440358004c2c03003040c6c3e5904ca000c00b0b1080b500c40035000c0701680000d80f6444110750100d442d11000034455801425500e41e0744076402903010b1510002415a003080d004403c1d07034000c0d803040124031711070310f0000035280b00300300c40c61100c65045071001011030103180240c2c0e00841d912141c884044a5040700d940b40fa541 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 985800116 1250 985798866 985798871
    0xf0601030c090501090b09040f05010e060a091709060f0d061a07031704020a050d1104060f0e090a0b0601031802030d03151a09040b0607050604030507110f01090e19 72
    0xc0d00d2070032410919a0344a041141e80c03602e40003085002c441e00640042c401b005003416034580b100d440c0c0c4070100702207000c2181c5566170b070f010280c2c00780c9080c040070344101d02c0801c00090b401d485040400b14007a6902224403489400c001038800c550b1030000341d0303c4850026000760349074034440342650018016600204040c0b0a40155426411003100042c001e09219a540740c3e00c54810b50b400d0311000001b610000c3d03200c0d038001024011410882182410f02e801400d10146280c89503000c142124071390707000410304d91103600d014400c48016002030754210303061400414900142d911001c3c181c030b50152a00c0d04054440220344070f07801c03102035050034582d0000d00760340c0d4850421f0350140050400c80108011003400a50002e906103120042a08448038020094a01074030b5004010041074800c515036813140e4184440c0740070440810266226030303ca078503400d94424281c02c0090249911a1400f03118001c082e00000190b640090806c0071071b40111080d40c01074640c182e18030541040e0380c5103c0112031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 985801366 1250 985800116 985800119
    0xb0a03050a12092c091009150b03071d040c09020c0a1b0302090a020d06030c0e1f030f0f14250803040e0c070804030210030207110a0609030b04050f0601 67
    0x2d41c03003400e003000c0b140301c3e154030780303240e50b5841c2110b00080c401d41690b02d8074041044419010384c6460010340d00c94080d000f65100d8071807100b2413904503030040c54180c504900000341540700f0001442200d840c15021001049501d11308110000c01c040700e100d10039200d0781a44040b6003006243c96500c4050181c0d0383d402e54407100009445a075070300c01c5000545e16503414107400d00b00e55a01400b8182501d40180041600741d80b143d103418083d5001004c0300111a55901e40003001c25510484080a880c00303d007480360034203001503841900b20101e8420b0817a0602c1500400000b107001c00000c0e00c1a41c0890350101d03000e0305007481ca0020001605420180c0140700f10b081d0780d00d50b401960110580206418500551520441c0d41c1d00d010701d01810408420010120b900700410402414040340f02c1c1d10300a03e001e44070340c046a428807816107004080394002c101e0004020341030b848200700910135101c551015142c40001000203416100c05000e086c500310206003030117000e0080c0c1a540034407104484155 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 985802616 1250 985801366 985801373
    0xb19120b01061110110910120b011d301e010b10030f090605090a020a08060c0702092d06240412020f090717150a15020f010e010516020a150b0a03050a 66
    0x7a52804a43c0d0f246403070304001279160760103030746031908110003042420342603200300c0d043c05018040c24500451401402d000741c0311200b90700c141501020403003005408421403661240d0303110040d060340240c1c02e90405101040a4446080100d82d49503d4500480c1125951902c0001042406001b91000d130400d030401c650340300c000604001443c402d542406072203689000c469101d44090380e0250844408100c6c101c0586040410300d41c1000700940040104075400c0e00e079401e074000d0f540081d003035071903220100080f516249450003851141200030009108900700203210500c55401051078940c043c18004065440e10f21034412503800240401d4080d00b04410013a0a0305000c880010844035110300041319407903071005a00c0e0724140980750340000c0782050344440d82c13032031078000c5401140f10325444840030120034001d80010310060800010b032414155102205155140f502000b03541c024122074000071140305011006506c80440064990140e40c00103016601650000c1c0443c400c00d0a11b0060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 985803866 1250 985802616 985802627
    0x225050d0f02010506060304061d030a0207031e03080f090c061b0d2105150405150a06052b1503050c010905090103080901030b19120b01061110110910 66
    0x659829141c0819219901208078241d0307800711032194000e0414004540058820382100b1101c241da20900401641c0c40c00074180f541e0414a004001070340160410000d0100c044102040412624906894400d140d02c003d40b002e8009018000c0480e140303400100307140000e000e29440c59a000341480e6540800060f52017400c6c0c24000f016080340540c4a40382d82c1c1d00d02615208040844140b00c0e00010954103101c00300520000301900e2010043c45010981c540c0d4038411503128000540d402c1601400e070809004082240750000c00078850700300800300000150988503440850340207000d00310b4000919128010700001011064980521907022040020126048042c4030081e030fa60390304259154100b0800003028070000d0950700c010008159903500c40d401808010101030b082444034401d40c5080501e03411151b10510f40210440842c8041004101c10140180f1207483d00790900302030706c034126440b15002200d14820700c1e95030b814a040354a8960541d0091607008141c40540c500c0440b01415 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 985805116 1250 985803866 985803883
    0x3151f03080309010c1809050403200307050d0f021905070306090c090b040b0904020409030c2f0a060f120f020d050a0f05010b0301170c1302090306091f022505 70
    0x11942000c17400710038035114a45071580b03800c1d5a881440d4540c90005010020100904103500300103140f039003042210401c548440c00c14510500a50791820142440e509040c1e9100081040080b5614111821540080e03460721204002c07801242013101d5241c403034513000007a40b006000c18286844e12040c08854240070080f2410f80b241440340d99102410042140c0600302c2c41503209480002040c054100f9900001110307100742000b51141819803036080d0039500c1c210b115056038144050f864205d444c40a40c2148401c410303103031401c0d80c5051110150840791080d101608105240090b110740c00340c0d85e0040e2444242c1103c04641d2990b903914802d000c4c01046030307207100741800c000b011b40b901512481054100d4080464440c116401c04000ca0030120308480f0206040c0710340d980810450b40c4505800c40d0364042c5010050350303009040241420254003c8c61451290009281202075801503070a002ca6640d8200700181ea07800044000040016081e020743c903c00b402c10442d2040180c0000c0d181d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 985806366 1250 985805116 985805131
    0xc091d011d041a07020c04290d020d06110f040e04020108090d080714130902040509060a230627041a01020c0d0303060b0a050301091401030203151f030803 68
    0x30040190014104403a07601550b005195403150590300e0954400f40d6440f941205540c41615600c0140c0c0002500b9a441800b041c0a02111050b481c90850621a0311411401041e01c8100a221140d00020b41030309501202420300da848071010801040c045044585104682d001c05403580d80b60141d440d00064101c0d02280070030303003ca01180040c40d0002d96aa015180d40d9211481c03640d440320300300c40072047c0e000034826080c0c080c8120707002004545203020180000c48c40060700e840c981820000d141501610301401013100807800c0c0015072034542c80c19072403254040940400075a20000c50101c0c030518600c48140d0b41c4c1d401d50101c4003490030040c0d4084034411102440a0586211204044000b07007071018050ba00140e0265400c0c01d0034038410340107a00a090010328146e4516802d107940e80050340e1ba50001c1d1000006024807002c920411500b8113082c40c05800b20740c1941c0c0441e07070369010100034042403007601c00010034048841c40e05081c003035400c1004600f0940d03071b450b00f1b1005803c20388454 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 985807616 1250 985806366 985806389
    0xa0509060703140718080a0501020c0c1906030b01050403020d0b0618060a06140403082209050c1c11040914161e11120a11011e0c091d01 60
    0x7840c564401d000d0692000310f44004040d0b66100c0c104103480c1103404000c4400216032003070000815031414802075800380c0c090000580c1ea0007000c01880d042900f0a0304085c41580702d000920f0006401c0c3e032004094070580d00b0000381412490700103071240c0c003e80e80700075405820801c5000c100442d512105002c1c00c3d0542e0594114800c81d4004141400101c420642003082240d04120a500c25280182c690881842e09850305840c3d071505101984440b00f108200d0803069080c104032007119600340020425404100104e05040201c0401803245040401e0301c6a610015058580c04640c8a2126000a2a2030300e40d2556980f0701a00a04258141603038044000030000d200d0b05240e50b0105444045640c0380d00c41c0a10012032012224a090f14084c01c200aa88038200c003408100003413010301c0e82030845551902c640484c0108101021800608241d0420314106041940d52202890311100785e000440c0c0e140768440201c0e41d02c0c3c41548140c0b5071080140c1c901114a1140703d000d0705130303090b60140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 985808866 1250 985807616 985807621
    0x31107060e190203030a20060f04120201140a0f15060f030b06040503070e33040c030b011e170406150e070c1b080609060f13021e0604030b0a050906 65
    0x102c5800b1001c9030002c0c2d0184c0042000304a001e01c9551000c1b18000c02d0585514448107065800307141030002c4801100d6401004184000d001510b10540c038a521517100a00c8008607410000d030000001400540e80c03542c071820103614251494001031140d0710300c1d4507032601c891350320b01c0d006101d1003070318600d4000710345444200c084505003039003185c080d1000500105001d1703241003845005100010030b00c4c280308520600d1b0030700f001e030840050309484180000b012400c1c82d0300e4081004440c40003034000241440c00d03500c0251079070407644880d54002100844882100d000d14140d4405039911034110200316507000b0041000308942c005000b81c181400c02c842000d44a078610403000009640980c0030410044500c0d000aa0070140317120b070380070503c902c00070ba5550b50350041d20b4598162007148650300004100f052401e034201ca0168060300e81c45408813150126000b04000c0d0170100e810200d44441c410a060380354a501c1c00300d03001140c0c4013024000381c7c42c0010180005040c103448292103030190601 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 985810116 1250 985808866 985808893
    0x10605090a090f2a030501020a020606010804031d0604090c05041509030201200309060301150f0e15030912070819020c13020702010c12020a020301060e0c030412031107060e 76
    0x18000c40140d0004112480140c00e40341c003003400b031039601c0c070341c07a0308600320341c004c2c0601d610180d080300440c8514005a1180c0406402034103101008081d50704000c0c80710304000110394481d07014041001110089048081340e4004036840340301d02d803c2080105e0911283c13494895000008008071456007440b0f01d00745142880c1190000c0301403101034001240000f50040b00030084400d80c150301c98503802c032850f19400001041468000764045080c7c0080580b4103510b07140c000c51404660380c120716041946c904c03a0000105075042d1410301c0442d0380c80100c00500f5a4108100840c401c42e849000345840700c12510308050254864140071060754100c03007403c2e001380e00000b508503000f0b030002d1490301c1c4d00051807030300c500035000703020141e040010100c1c0c0307600800c0c081c20282c09203580650180c6a10401401891709440e8250706c0074002918110811440000348020b0f20f400590141020052241c8800c04030f014010f01c4501c0000e035240007804e1402c00007150321400d1503483c103100f034640b101107914 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 985811366 1250 985810116 985810121
    0xf0f050409081b0709090305210f0c0c0a0f1b09141305010213030c170309030d081b0406091a07030c14070b0304051011160620030702010605090a 64
    0x1e0060042606008000c190f40c15072543c0d03480002002c0858804135641c0303100030141c0d028203105401080000039280d402c11004584240100103078032044105040200004020b0300340107003c620503417400300d9103000e46a0107210742c0c01c00c0c40e000002c0c1d1580c0d40c80f5003407080c0480b0600f4607070041d047c08803c00065030300d0300e0300504000244a40e650441541d0b903041d2026140c0c00c1010803a1195400c001349041d440c14005604080c5001e01c1c0c1340c000c4503041c02036a0059000d500034a0040c1e40c41408032090681d000140c445640009180c04030107a260312038401d5910440b0050b81c0006035000c6008145075070300202d0041120038009007003010f5039a21102d860144240c10300074002070075118400010800840d110744040340088211111582e44440010305500240c50446c4c0541000d0701001d103441940c02001d075211182c50115182110f090044d080302805510000e1655032103181e201c0320503216a0100c0d000d40b03d80441580c2d00c1c0b0701f6400c028002c20460203032903c81c000c41c3c1c1c00304e80b00b00000e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 985812616 1250 985811366 985811381
    0x1505062d12240f01051c060918050604020d050705030714040b090601020627030403150605040c1e03140c091f02030a05030a090602070c1508130f110a0f0f0504 70
    0x22030341c0e802d030260600900c207201d4500481241031040c100201c2c550418001a6aa02d00340200350002c0c149080c02d40900c2650f05000440c444088040115030103c0c0d40402d0680e046541111814050001e52401034102665640110380c5805000c4e00001c80e0703e4a208148aa06002c5508210102c44c9408124100005544080c0107a028034002580c60030403250b02103046096070440b0b840340424542140c07445d88550001c856490704001070340e035000c180303018100240200f02c2d8248988000c1e103d000744000c40b8902c86102c019924010407103000c0c06540480002c1c002403080d00c80300c2c504400c0e817826030307803000c400d842c00f0389000c50394081c5000b0f180844480420141c1d0155261032001142102d483c1c03c09810030800f282e40d00711800005074544000c01e1610310405060005d140f9040722164021581100340007841140b604104103540c0d10348241820079809424914a81914180f00034103034802003285820015960010480381119032103902201e403003e08624040c4d48410500c01580c0c0e81 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 985813866 1250 985812616 985812661
    0x6120b0607030c0f020112060f0512033c0d0e191203091109010602070e0906060121150b180102030f0a030c1103030c030f0a1505062d12 60
    0x24408040020b000f406807404c1d40e0740149041d001800206c95060304440590b440b50700c0c1d882ca00e101c10001c604284943c65291250b04020f182071494101c412031a850b402c01c01c004a40b00e80c180d00710000c401e0362106c1d20f40c6500b00c0b407180303441d11076aa64140003000300801c850181e01c1501c510340104c02e502d1848010035030b0300c9400c0408006005009401816007413804944a40b0f14488002a54a41e8150386000300201e40c02801c2e0f0f02c0c50b142624500d4140a0118400ca0300301c60100304079139821020442e0100e03541090700740301d00ea45881a07401050644040c41400141c1280010740403d440040c0601e15110316207403141c0c0d0044401a6a0382c03140d94804440c041c001d00c0540045406a031110114903c170303003405480800144000c40c11584103d903001d214140100a000c80c0d0851a00269440060744000700f003180064102c0d120300002c6442428480e0400154210500c11060884410154200506140c1c0c14410707403100119080300042c1d4000007900b10014104880000080741240308 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 985815116 1250 985813866 985813877
    0x16061b090e190e0106080102030c070c1203020c0108191a03010b010201022a01140a0c080f0c1902030c030d20090603011202030a0b0703090c0905013c06120b060703 72
    0x524422600580004460f1200e40c0d580ca4a000598190a0005501c0380c264240c11959540b0351746400c0801460942020802c0240704400700c0000b60002403000c0e00e0707002401c001c0034030b80c1d03101d401c042142c0c074116644124a0505521071414061075144074102c684c1100280301c08920040124202e014004000b0304186042410710100320001c5120203074402880b00101341c02d201003103d0342a0781411340300440169031311009405440d81c0031560315008180491f6080c200d041507040e152640c040d000d82c2c940100607070f407500c03801c05001b0401c88840300d60300400e5030346179402da0510300010480407225420148540c541c4120b00d04051041354002a0002c1c0568156420f010030621000c0c00010308980500c41c045002d070114a0540925200316060b5a0206902c0781d076103007034031b05c0e146242e011a0b812410600103001c02000c9034001000740c24103504000380302c03004030020300c2c41c0c14100041184440c27100b40c000c074600c0c0d80310440140d140012402448040c040c8000d009040c800e8180c050002032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 985816366 1250 985815116 985815151
    0x613060617242211030a05010509010515160215130b0a0207120606051c120314060d0f142b05041512050c0405040f06051516061b090e 59
    0x509910411020442498280c0c168514030300d41004a135440b281890340746001104000e01007204e0302a10380549004d40d41c0040d40d501d02808242024144982c245190401103607405008210f44009150181c000f0010600f00059409904003544403400c00d2540c2c40a01d100840d0460450b411115100341035802840013500c0d216024a503400ba80c00c0c00ca4541341c640000080c1961015840100c0d0301400444c841960981c2c40c021403410440e141180502d4108400c0050500d2104681903101e042550100d41e00f00309403801c2d0841d0707800c44000601007960080c040c0c0302c054000840409c1507248a00390300c2640b079030181e0644c0b4426800140c40015504010500110350b0500c10102c1c10070160900e80c0a4000034150701d01901e0b0308588140803041c0101e0208050301d401c0c00f0b080400300840381c0402c50681007801040c000c00c00d04140100507140001c001c4000e0b0054402d40103440d8007c0410003616001c3c1520340191103102100f003000a0b42d92001080460025100c9070041c071040c0c40402d80724 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 985817616 1250 985816366 985816369
    0x311010807090f0f05040b0907121808031e0c1306030c030902060703020d140c070302061b100504050606040c1d0a0b0a09030c0f03030512061306061724 67
    0x20400145007008100501c980000c0407404002c0d007102030704e50300081002c2e19041409000c00c03504c500760018070521504041c8918681c0005252000754a102d02c0031814000d03200c080580680c48440c0180400d4001081114404200c84107040d00c1d10410440c1403a074032502c08025a41c0690080c004000c003501e03108000321070007a130203560580b41e030303090206581d055038000a4864124a80039005604819950380f600c07a0300c0312a00c01440c0025000038140030540300040e6649110b800000d00a2000149061501c50303d4101400d03002e0140707046030035111010401c600548001d80341210755200c1c48010604a20b07180c0240e15800060741d60344040f94400182e411410740c814a10349030403c0c072240c00891200355071001407050740c60544481030110300e1441c080c0d100c100160b107d6a00071100130001e1000a40c490f0032518443c042c0b51500e841511018001600e94071803414800708289454400075134250411405644c42001910b40c0f0712681d19095420381c400110303014100304a00c0c02c009004207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 985818866 1250 985817616 985817627
    0x210a11092809061812030e030c0a030c060b060c1507020102361306140406081906020409020307090302011e2a150603050d020f0705060304060e060a020309010e07031101 74
    0x30b95015203404144900441000aa45481400300365001d40c03004e25031a04442e0036025042c40504c0c20b20041d0b28280701110019203d4484d42c400404000d88551801e0601c15103410103a07603850300038115541d034a140e6480580e00d400454203000d80718142e10000d1180350062082c0d416540020040c0c401800256403070300500d26900d92840c070304034100d0403110000d48490150040c00d4040000010386c0505051f10110243d0000c003040b881241856014441c038040842c04104850740341034050b080601d00d1030070b50301901070394120038803413440442002110b5034041080d0086178000e8859010a0000354880d840940c054a801008548030008680f102600c01c0c1101c1c41c0061920355201544015682e0542c4500c804035107150390706d403202c4080c014417030144003528060410380000c050408a500009441d951070740300700d500c5175002100084c01c0c0700741508511089050707041510240d242403031414000350001e58400207158030f000d411070941c010024611040ea034018402d44407075480a001101d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 985820116 1250 985818866 985818881
    0xa02060a0606050d0c212415110f0a20010e030c01080c120a150807150f031d060a0b030a0c0b0306010302090d142406210a110928 57
    0x20411401c003115072548080e1422140407422040100d081d84104011f01c00c0d48010f02c4009145604c8440c0c100a885610890400c460185052410f10000102205400d140f03e4100101d014021110007070100038a0b030300807140c2e82041f4540385080c00300d9000115050141000d106030554030490907000c00f517008010b169400300d4000e0100345400244100804e0418007034920800c01c0741c440c1c10700741c6c56074507480e8204082c040c410010400705150000c00c0061000604680301844040b5000060b0640703e1b130002a03901d5000d8130b22108a1030340e14600b41c2c0e11141100c2c9100750614160f280d0f44185004965519941d403c141d035030300300904110304110254006000365040c56800c008100139a140d880d6040840c5010319004c8003d111510340c01c0d810819210405440c0681c220341107440f03002c400003040e03003100d07050f030b900c00402c4000796550350f030066500e0710220746e403050b13a40603000c02070b2850b00c3d00315070725094428517110740f200d022000445510140489083c42d044076550700d081e105502414 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 985821366 1250 985820116 985820141
    0x3050903160c0e0612030403030305061305010303020f12090d0b180d0207091803090b0318030c0c010210050f0123041b0f0804051e0709110a02060a0606050d 69
    0x285003000c1007030401024100350104481d00014040104400120303005a25440441907540042045038105510386902c00d501008082c55523880102e60700d41c80b101c9941c14090304040041000d541c503070a01966840e40c0f10f04042d440d200d84c55080c4445202c5e10180c6144c40006801541d500d4900e80e02d220705100018082034512082c0150340010340d01c10054801d81d42c3c103540141c8900d50600f43c040081d1265604107200c5c116121030920000790780504003d044441c0488600d031a501c1c1d03030f40d25580802a01082d400988130221700d546d000340c404145220414000d800f01c5041c90160024041034030001c030b5848400c4075020004201921041c10109180780088000749408844540001d0031500911000d0300040c4d40c03000344440c4642c00080b0100d0810250406a005140135a51140d4a031442240c4100d48007041e41844031070001000b181d00984016001172005052498425800c0c1e080600d99800510404011819080d840d11802c4250ba175a03990344c2c1e140070510303e8070401400c040c80824 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 985822616 1250 985821366 985821373
    0xc020a061b0804031a01090203010e0a020c0c120d11120d0b0102070f0602010203070914130f0f0908130f140613030203190c141305180312040605070f020d030509 71
    0x1c002540074401000514071500040c602c01805400981c4c0c1c1c01c80503040340380141c0c030404c010b124910204c16403070740c40320403080f0150751000c400750500e0410981c00116a008520703d208108018400310b0100117940b0039642c0c56400721010b621055031269413031340c002d064150420000c1889a010b410420036414103004641c81140d4600c3d4003449031840da0b00203030060f5800b005102410742c2c0154030000909016a180c25021005000680345241c1804552111982c880c400104034030260070400758a090b10b1070400c18a40a0b04050740300f64890881410444010f107008125044410074000a65845200d030b00d880742448020b22510780e00c141381002608030140c00000043c0d9041080014050b80307801051024006443c0c0080e17200080e03003202d105242d881c156490542c0751035940980b0ba403101c0c5404903294403228010580c100103104a4101800001552941540108a1240910701c20364042140f0750707030090115186100c00140384010f0f00300a9000486c030b07119030801c071307006804002038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 985823866 1250 985822616 985822667
    0xd05180f09040501020a09050f01170703061505071a010e010b1e040b0d06090b030c19030605040b07090e0402060301050d060b0a060c0201080f071b080708070818010c020a06 76
    0x141c02500d04880880f00c2d6900000c810200030f511101040c01804140c9041c0c9a4000c028006010943d00c03085580c594400c1100041d47c052190304110010244099803060100014400400d568001d0350142d030202c031120001d801c0b030a001d0554030f040710111a0760881310790070b10f055002198801030340c0440801c4601002d42140c0c01580051000b8400034803503503642d6034a100558260382c0341d98400c089507072403d10720881e030341c8000c1216512004111040e2090300740911070012254032603003015208a20300b10402040207444009240944a01d41f01c040c103541c1ea03200c00c0c84c900c003411103009400400501c0100064180110405545480303010080385801e241004284420529409000046c610800711802d65030010481c0e41c00041006903101e039440d00c4007000e000c01c20080c044016a82c8a04001c0307081c050340380c0a0f1031401d940000d81c1030b03480d001e41c2003200154102c0006901340018000d0f18401075030140e24081c2ea03181e0701400f2b0351100d6191140c180c6400c84805000d00c104580c0d0303501c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 985825116 1250 985823866 985823869
    0x403060b09090a380403020c011d0f180723040302100c0204181506060206250c0f060b0f031f0e0109172d16020a0509090606120d05180f 60
    0x124007130480c9a00d140458240750604009140010101305a4188552a9035043c000d22121180c000109000e45170a04544047c00110b0001c0321546820705078409102c0c103214a8036071200380805031200444815422a406454451091190703200095101040001000300240100180d050300390004000040803441030011800001c200c04084981d82200360103482c00210030702c1150007400d9184002c010030f281111500112001081054192102c2481c1c881c00c1c0c140320b1225000425481203011018490342d1400401500c004c12890784a4040d0412080b11400d0014024100c0c86a05540c90307001d0002240740c1c0001d00000c01c004415540312088040800d011070b440c0304800c401c181916039221150300007540c0300c14040c1c05500780c3d0500e18903100d00c480d070b07030409543d141c16856506001e8200584009100c00c00b0b031307901443d08036524a0400440300303000304043d407240070261002c6400d008d11580885c0c0b1441400580d901040c024026036010b03425980c10340c4240c041c05840307000400940070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 985826366 1250 985825116 985825193
    0x8040209270a060f060f05130603050d08071d0105221a03061003060f1509050907020307050706020327030a08190f0806060403030f0905150403060b09090a 68
    0x1c400035002c2c0c0c092900741c1c04001072807040e080d1120070b00204205050916124001600f80751080b03a22600480c100500480ea142e8000350056910030200c81198030a014041d284c2c0d030040b138030701001c0346000c40c070f000d9036070a034034016210351105948440c904914940303181030842c0c6000707101162124095002c41c100028014030050101c08054a90322031400004020320404201c172110205400d04004105120b00f1550740d0040d20002c281c6828104180141103440000d2603121952001a01d01030200c5c0741d40100080c80c1c02d5000d00d0640d03110a403114016070b41c034030a01c0ca05400042c50070f80494205006201100c1c01c034003009069070781c0e03442c944d00ca0a50b242c00540101525030820806502080d811403c8089200c440381041a0b1314030381400000e00c0385c011444081d0900110790f9032610914030502c0c0d150050b00004141102c03540d1240b2480401d900940070840b842c0c1e00d49141c8010915040c000d2a21941600009001500c61035071352010a4400910081c403180c100151000740c43c00d0302 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 985827616 1250 985826366 985826431
    0xc1c140703301509150e061201090c030b07080a0e060601050a0c060f050f16081302030a05070314210702040213030818130c0804140c0307031101030606050a08040209 73
    0x41641031213070620202c00101c0d0b010000c103a11420710800300300220703200011044d86c01703141114240821022400906d0140c403445100500e00000c050003c010026521102401203540d41c2d00d003203071651200c0c1c901c012141e1a80f03c814950388640d00048044d07201f0802054080c880d89000920700b4060740e14001902c2e009020403000319140e6081080d034030306802c0c24940c05100042c085441c0300004001600240e0080d1110741480d008100c903801b5510f00304241c0707280a6010007201c05c0c07a6a40c0c01c1c801d4400b10040e203802c030a8080c1310b15013410504070441c40348000c0c440080381440c00040340c0c01c00c0f00a603c810010400c0440c94032000000c500100b010704111909990b5000d0301c0c031851420000c4003900d01800d6800d591420141901081c0e2144416521660185071000f2140c441c1152628007000940c0107a8144079480001c0200120f001604580c40400e0320180b1016403194019111405400720010014500100060251820300d02203a0007003903118401a29150b994560343c0850007a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 985828866 1250 985827616 985827641
    0x1150b0306030f0313080c100c0f02120d020f010b03010c0e0909011509020903011523060d0c0e03010605060c0a12050702060408010911061c020f0c1c14070330 70
    0x1c0c0385007004446d0301401502c407045800c440000000000c010041e00500b20004040c0c041810706450b0000c54480c117051804480c00c98003150b20458490400a640c0d00c250013007580a5403c022060300181014000c82c18284040c0d00c1d20b0178100300c032005004400c0b000420307196070b40d92504041d4001c3c0d400c1d2001c0c1d9026241494000d69250008407d15007980c0ac000c1d002d405040c101c2400f0050340301e90201c0c00d18040b004402044030080b220300015403501a1500c84021389141105501d90103400a1541c8407091050b40203011769a5613130100001ca00402c05003110603005483d5800000e180480d107543c0e40708082c101642064090b030081003454010350425071440c1c0d507400b07010050002c2e4220541c0d01c060202e8082d1729191040190f60745040c0352002d50548544c020072980721024821098404140d02141224040344990480c01d801e94030818134180072840c0e194071b10980030040c030201e07000c15415844405194400c14007521041780c9840118041c0010380c07400c0b482c40b42d0382d4043c90f01d0440e030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 985830116 1250 985828866 985828897
    0x160e152e0c050f060705071b030b01090603110d0305090d030212031003110f10050c070909050d120c08011428090b0d0b011e0306090302011d01150b0306030f03 70
    0x81c0c1e2404a02d04200381e1506102580b001080000c0264003c040340d02c01c96010030560000c09400c460684050860b4200900c0d090346d603000826841555402102100d000e4880104400c40100034000452180100580001c1d8100400001d40c107054011062080c42841110151076900d0200703444c0e60010f460400d008110903400b0400d210061000301c00c4120103c0d00320307480f08114800196001f00345407210081c4074000c80d42840f582c03c1132180d80c000b401b4844050192760861b240c41c0b5100c1d5031000b503080c0400d006c03085c9002c0844d040d20501d440d200c5140c5030b034003050342090271011102c00c00c41500c5900c62000101078049204904140103280085400c050625042c84c1e990000c0c2d074001c0f000c9034003845010010301c021600c41014141100d440045010421401040ea1b955a00c40d507040074009604001c001010590b056000409001805440c070b07451610b80d00540d03080e05d07285000c0d1107114050350000d21092068400451b040074000302200c4461502846040c2190401c2507613824011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 985831366 1250 985830116 985830137
    0x7080717030f1e0a1d01090f12021504080f07060905061512070902091504060f09060e0f1513060306030b011703040915030c08160e152e 60
    0x4080d0034000b900301c00d03000d4103a80088900909000741403c001c0480410503225024410000c10380c00c100030b0ba5401e06002030003240308a0400d01c08440b440c08084500789004681c1043d12031010401002504610003aa611500c40e5200c02010342c000c12044200c0031000c00c4004000340c850712420140700e00c25809040c2e2450481404181c3c804000320043c0180303008a90352140307440100381481a58055400161a0b41c00d0b41d020900c0142613002242c0744001c005070114400340c101407009003001c201e5454141e2161210301c01c0300d8550202149a40061070540080e02600e0401050511a0705580060b400d10358503c505280f44c58155000001003030b40e8cc0400d1061044075144503000d051811584003103510805c80e4582c0e60301c01c0d481041c1246960b10310b280c05841403945807800454005901807140c40e225080316850301c0f81c0361000c02112101c4040003e10030440c09110f813041941c400d00c2b492041103c414000220078041051072a81031406101e030045048440901080c000c0795180240c89 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 985832616 1250 985831366 985831381
    0x60f12020313060b01050412060504110a06090e1f060305040627110f030303180c03030d0e010b030a03050d02070311060f061c11151902010c031505150708071703 71
    0x2a200100c1c045e04105041100340030b040c500d000d010310a280d01290010b961b40c0c0e1801e184924070b40380300c07c060b80000344030000525158041d22081c20303600f444806181e0f580305c0440c14011f03c94420800c940c039042001081102c28042e50040ba80b25028171008034460501c0031001201001c034031a06000666801021414444540c00300000b10f0b40c10340d038000c10940004000382d40c07800001c1c0001400c003200e411802c000c2000740014007030410050116a290118896590080c1c41c02d81984440d540c80c2c0381c2d1460300d42c03400003500f8076203d406403162403514403215103400c060b611000041d0180011412803000000d01001054890401c58907019402e040c40400c10540e0503a50b02888078401149105101007403c5102e590a1344030f040b142d0380855032600510b0042401307180d0820a034880b814180840c45501034012800000c2c0940d0708001d800c528a60481c1500d03c1402919003151400c00c1c0c3c0038001140b00c0051000c280200101400d142d007641c2d40c0c0e0425000c0c50494200043c0100034420f10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 985833866 1250 985832616 985832621
    0x41109041b120f080a11030304030323040c09150b070501050604241503091b06081305120a02030f030a06032303070f020a150c1a01050a060f1202031306 67
    0x2d40101c00310252000010b407941d010080c1203200c00303086840c00160842d4400d0064040050b842050805e803030300d914003400c028001341a05001500002d0040040d141401c1054103410321a039071202e03805040b607082c203400000424046110740f880b0343c014040420804060380c00b920131580306000120781b61810409000980e40e00003e6091132003140b5203240d1407802c115100c40103440d100000407000c9405110224040c1070301c184064031400ca5984548000402c8420340816100c05071076000c0140c541030140c8842c00c2d400b500150650700201c0c00d450405004030014a9200c00c5071044a040c035070b078211800b803070f40d109940c500c003100c4e96804108104110705505000079090700900030362104000310744580724400c079807000300b649400907031150455640d48015800f404410760030100c0c090a100c40508000c4e1003450580302e0f40750050140d40702c41150101541a120060010340c1041e25001d001d641030000c400001051261002030494400100d101841c031500004e94101c070300c0011424070104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 985835116 1250 985833866 985833869
    0x132705011d0a0c06050a03060306060806041a10030b06190b0414040603020a0e3301110f0a031101091506030312330b040b0309240f041109041b 63
    0x141900b1168a240c00b00d003c400b00700702102c0d51410042e0360390700f50102c120001c081a0300b0040103540b5124020581c0500000c446209a214400084e00130035485640307590094110f824054010241340140000303440c140c2400e4016401910368540d04a041d0f05001111485030030204001c4008a01041016644031100082d00019030b030801289045030040f072100c0b402d50040b00031004941000c540c0d02045000100c00c0c5180c04482d060107040000f0401904e02c4c1c002c2102400110311180c0790441c0c00340424040a000e40c0c040c0180a40b4070303640d41c15035800d00d0044c06003aa6544e259500404140d01c0b42e540000d4240300880000d03c0d605503d405400d03141030101a81c22685407016140d1810880d008101e2544420610076107045050049162404904d4000a20034032000c034001680c41046009540503441d0002690b0001e06000c01e9800d4819504280c0180384507100e01044848008810050300030b030080913400d48443c0c011021901400e070641c0c0456030f40390103521140d540c00480c0c08040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 985836366 1250 985835116 985835171
    0x50a02061006091406070203120301140603010f060806031018021f202806050f0403020c0112020702030109031707050a1d030705030615030d050913270501 68
    0x11070190800c18001d282840d10700648001d4014045452103507540ca00a035140d080d8020110740d201c1e40c2d10700364507034540c00c28071510001040803a4505a185007140640c2e0607500c00c20502c100c003901e0007000310b49000000e4411034050040d21414144421540680c0c00700b164400d903510300090051046c000d4408504a010b0034414059442c0d1030002e6000307642408246805c075503150355102c114416801d00c245c0c5204c41084440c05203411945d041810141041103000341002c000b141c1c0d50041102d01d103003040b100240142c0005043c4801580100c0004004d603804040c01030904045034007007400c44915810640c0800d140c1d00c52171007150ba40311011640f00300b0501d0a1820040300c80000740c010361005c07018503641d000e011a802e8664078100700300da009000050807a1000c0c28401c40d074140750700d10318021030b001c2d001c1c0c500071008490040f4100c5007121405412480007021410740040140542c100110002c1c200500c00d40b41d81c001145c100c41c40901030000000ca46020b5254118203040c09020322 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 985837616 1250 985836366 985836391
    0x9010905150403170702030d0207050f0d0c020a06210203010305010504050c06090d08070f170307110304050105030c0309010b040c1101060e01030b1b120c1c0b0f0d02030715050a0206 80
    0x384c4e01480346584403e0314a4602410b07180c0b10416400c50040303405024100d84089615001d0200000b0380c4481c00368803109031004030720300d08022184180540340280d00001e50003803c20025100325903204550a002001669241110000900b44c2e482a40261390b1603441c0d009200c14054103204900008800707c0b0700e01d180c41c2c09036020910002480030050024100402c81f0814013203110000e580007503002190b88590707135501c003c5d112030350001e403991400600400c070021060680001110251a8141c44680c2980c1ea5400014155071000781405072554075001455082d0300c0b175019201048189450f1445400c924015150031a0201d520103c0d00f809118010008039a050180642242894140602d40d20b60300c00c00101c079101c2c0400b0600c07208010410403000c181401c029000d9605c0740c0560080070782c0003c60030403d031000048071035804015046200c43c5403408401807a000d40c400b0301658061070b92030f08003c802c0b0040701910b4022940000e40c0d0840b0030350500905074005c010901e01e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 985838866 1250 985837616 985837621
    0x207031805031002070f05060115080a2d02071208180601120204020a09030506040b072006011707180b0a05010c0f020103050a060b160c050102070b1c11030901090515 73
    0xf940c0f081d4078400714080c20360000701d003024480c80785203020015400c00c04032085941e40d035403002481d03080701d060f03180000e8821020030700720f004034007588500030300c4030303000e0080c00d110140d240100441520390154850750030040c800c00580d17a0250581c0581850304d444540340341000c0190420309081c0003110303040c2c0003400113218099031000100e91550b01520011b807110304040058031000501d0f000a00389114620400c4100100101101d10440301c1e540d690001e454516809400688000d2881c10181c10160042c020703541c46500240d8081410021a03c900e40e444030519124100f500020802c1c1e500c2e814000c1882c1448100c1d200100420718000d41106480d4850314419202070750002c0c1019210303008100b1016403500064043d058425400d81e65802c03100604450069482c0c007201e0384090688002103541c00891040100d461030200c26180c803100105d5403800c800c4691090200590340c020000460141c80091803003030440740c000245100e007904020f0316000081c2814829608503508 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 985840116 1250 985838866 985838869
    0x621150613090c050715021c0501030209150420030105030106270f0902042a030c0f080a0e061f0b070c0b09040609050c070c0503031e031008030406030207031805 71
    0x14100d0868907807200001e42200090f000701d400d80b241c0940030f0100750342206502c4055846500400c0444d44500041740c0b000c403080f0088064410900c00030b5404806000002c200c0c6072901c44041003642c00078030008045045c003980c900b0703c1c0c49900c004c140840004c0010701281c2130921860f0090300b40380e40c0c0f40901240b00b081d020707955040c030b01219507200c0c1c9071010000c407164180c00009020358020401e224840030700c1c0c03a03441140d82c0c80038100c49030311519480707a03456030103445040c0d8050581d030f07140b00030b499485d2819912044050825642036a80c1d054002d07156a0034010103000c1d02400202e40111002c5510000c491000da802c403018402041101100040ccd030942e1450403289583e480365140c02e01800058000c0103194428004141400300300104c100312040280080e510910380341c40e0890b00c920034580c0c1c078001c9984400002c1003681c011112585080301460780085440d000c0100140c031440d042e03095402c00d6001c140442d0f00403840e4010190400004a0010000100c41140d2442c100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 985841366 1250 985840116 985840147
    0x31a0301140105060a03020c0105011d1008060109092303130905070f0f1707080a0c0813022b0c060f030207150c0203160b34080606211506 61
    0x109a41c13141c5000075403810460b0190f01650299a4004000c000540c1c0d92200c40c0c2c10300300b070003e0803a6104d080c0c9002400715200200a00c0549041030024209030382072041c050000c044494069580814a141c403a02c05201c1c8080c26070b0058004000d1078079040700408035051b00030940c120580c0d5504100810a83c1580001c5a200020a0740b402810002c00b4080076280f905a031386007404c1d00d0000d4170800c100c42d07400200040c020b040c003040c100101e40c04911704031000d10f015501d10901c8842e800c807071009441e00a41d090b07400c0e0181e1101e2804800c0c0200b04059243e83c001c0201c644160801081060981146403006184518141980340185c1d40d0307100c1000c4100028889240703a076074824002518030030010340e1300f0070030701007282c0d40c800b00c1321300b00045603d000312100507078510340d2001e070400d04e005032080150903040e280760b4110203546604143c6030460000c01441c1c001c04140b00c0b0300c0481400c0c510b00d1800c0c0402c4000e480302400c01d500304013100c10080f010b050041004001c0d051201f019207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 985842616 1250 985841366 985841369
    0x1407050a1704080d0e0604031107181113030b1f0312080414010f09050c030d0804060506060910030f0c020313170109080a020304090506040b1e0d050d031a03011401 72
    0x840310080a0b648525005100b4001d46401504540ca00050304007103007030005546020341e00035114034011742100419981d0300c0f0000d00540006607500c40d48008a02c01507007002802d000e03440d2800341040034900d0250f40c0c003031032544191200c00a14050058800e041d08100d20031075400c0c0a21301109003180c882414a00350451203100308800a00002c041c003000708030110810040d40000d1120031035111421000d4044200b080d0740c80c0c007443c48004c03480e241c00100308980d501952903807034079a81d03140c4820f801000002d141c550084010481e00900da0344410540c040360500740c6000a5031801d100360074044036003680814040d036108014000080d043d40c3d5010342103c4512500c080d02280b04420740d8050000340740010403000000c40d280304403a4000c0701a10958845040401c80d581c2c0d54020001a1140300400c41e0300400001206500141032800c600361003107002d0035451114000c0d50707c141c90111182124400070340d0752180000c4000f80e510780c441c07000e981103000380001c003124007007503a425106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 985843866 1250 985842616 985842647
    0xc050f15040c1409070c141b150c06040201050a0c0804122f0d0c05180f0903090f010c1b03120f0327051603030e0906011106060f0a0e0a1407050a 64
    0x840110000c00000c0c510f01c04040785403070181c03410300840c0e08d01c1e6481c0180405005200d1102d409401d4400b1000c80300f80d0b42a80c0b4040c000300b45c507444030380041d00d4640c00000402c040149241a442c0459040e100500007400704480c2d81003030b03903424204101807801c42980404040f000300880f0012612011f440d9003070750000c442003003000c15540b4101021a9203a404160014510091620003101c0d468080d4030814181d462018140d0300c0c8141c45403288220018244c1c0650225240480395215070703181c0c003449109520324890105900c001030400c0300c5a9004072140601f40c124030300c4141c2e01290f1004054110700f028404544840400d48180058401e40825003502046040a0000c10051004400c1003c40f03608501500c81c180200b05907002d5400e680580005004120031354400d0007000e1001c0000300150030704e0388a5908020200013600322042d031102c020140401d845208104240c0111302803400002c0590710345021000f4410300a000c1030620a0034010f401000340c205d0302c000408081d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 985845116 1250 985843866 985843877
    0x90608102301050120070b0a090509010b120712090c031b03080306040b06071a07140c03030f1533040f2907061d01050c0a0c050f15040c140907 63
    0x45d040a1082440383c02443c03480e083c0300d11070000681c0c0c3d00580042c800b41c9602da450110840d128418881c8808080c810800054000c2100c0d02201e1141d90b01c0c0b903040842841c0a40081880d9601e010642e400c0000964212400780c0c02002002541d4203040704840c0c0381c1c0c0144108070b2039603c48201502004101602464440cce140748947d50f5074904844005c3d038419240e070300e00364450b6074a0b080360108540c81404986e03081c4003124005001800c0d0f485901405000b1807131990313820034032b00913480041c048007420030215801200315a0390328142160185580444040c4141e03205a01c004042c001c104105042e00400081c403503c00001e480900340d0300c00e007000c1c0d40000005490401e040810313088001d000f6001080700010061603410450007540b5480d0b001400c041d0b030803052030888900707507602070041d00200045070106000342444101c40d8082e0702510030f1052828030752410207a10030b100c4a041c8040c40100800c0000007090320024058500c070450240307882c2000300e00791900c0a000301040c405c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 985846366 1250 985845116 985845137
    0x30506160e24040302030307031e0503010513020a090b160b0f071422090608060f16110f0a14060703020f04060e130614030c060c0c0d0c0906081023010501 68
    0x10100c2c000c540c0110380c080c0031665111407c2c10014051035450300d00781030380c42c40d400d500b46146101e40240c2e8140c5030300500c0020007030010040e040c001e40c005941c00c001c0c4082088001503420814014000c1034480d03e030010042c0e8014600f0081c41c000007840164488408401e00c1007030741c0d0200150075020b1606070201d68464072039021103e401c013080903072010448080000701d828040390b00300c1c01c01c8856190440710345480710307146540c40c040c2c101c070243c5040401008207145039100340206401485890166011481000e40312401c12020301010346800c0c44814010040380410040c1d517501c0303000c038941103041c581c000a40700d09a100d1071046908020b40a0303149141741d641d1000751450101032030000c0100b01c3d0b6422030a0302c0d00d01151613561003070064400c01801800d0440480e40352203003100c050400700350300c0e000f00302154205280950703410b5182600801c0c080369034810140503104138030050810325100c0c10000182c074010402c045c08946e00d0358941a070500b00c071034442d066a409082c01680721 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 985847616 1250 985846366 985846429
    0x1005012109150213060305070503072f03030f0f09030c1f061d04051002181002010e1911060c0c0103052806180b03030a0c02040207020a030506160e 65
    0x100b0040094414480c40090100360400300706418800721261524207014555440f44290741501040b5200d401140100f20401e480d8074400c0f0405c3c190080c40c030302421580c084065420703e150030071100d040c00f03010000240080d04c1440980365a11010b50b000640c6008107864086807180c8d0b2807401b408840d20b1004040d14688110b802003000349c05990070102040150703444c0f856151200380c0d801e950602841140507a814041d000b202ca600c82ca001d04034800e409000140b01c1d52000400260302107550b912005007030071006005d5001c1c444001e4565011018160508094010725001240d22840e010403a402e881e03400491094a21002424001002d80e02c000c058510035842c800409040b0014100d0401c02094680c029000c0c0c50765268040c1e00c2e00d504000142c00c6070140c91354194594070610094007440d105001c60102c00b0720240025042050350350125400784a1a0400c0300c481d0010002c00050706c0c041078220f40da141603880c142340d542c0c10b60004920712100c0c019010036000e44031680c94520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 985848866 1250 985847616 985847633
    0x30f0d02090f0603250e06070206220b04031202010c09030b0403090306021c05060d020d0210050f0d0f0f05010501200f0304060309140a0507090b12010c05031005012109 74
    0x2c41000d05081d41d41d01c1c2034a0b0150f07140710100c1a903284882e03c0c00110f40d00902c10065480c0d000d802404c0b50f1328016080d001c02185402c100344100c0c2c02030000d40381f0225100b2180300c5070001c1603909081d588036811031902c0310300f407070303e01c1c000c00210383c54020061500c2d6031041d503ea04490700300f01d0001894070f803402d00700d41d48880e60704084c081e01c0c0001080b900300799810500f1131074200303220340c1000940c40f01010024012141400a50701c400d074020b50710051b00c0c001c18090f03400380c0c842c00c20a00d810000481401c0d84d0704100400c0e80e12075580c0c4086000b0205034000c05129081200c010480c40d81404c00180c401407611000c04840d0f0a1940c00c10005881007166070b400d1040d460481c0c3d280c0e1303030300d20005014201005040701c0503140510443c00e514000038407584059484409055524189103240c0010642e810708540c0c0010103001d2840c20f254203200c1ca214240c3c155880c281c1d00d01c0c1805080351050100e07444141001444d510012400503183c58940c3c5000c081240402e200d5030740e0402000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 985850116 1250 985848866 985848889
    0x20c090708090f060c0a08070c15050a05220b060102010b1c020a120507060503070c020904150b0a0501051909051f02070f0b1603050d0903031d030f0d0209 68
    0x204610400144980e9503007108500b441034250600b154090303d0114582900e5070410b4070a00000101408030080550041207065444030303c514252240902da51105800881d05030041288580e4030028051f407034415010b4564410700021890b0346218445001c610701401c041000752240b52440e021542c141e10039080b008440c3e0703004140150711030b4002c00c03410207034049500483c0b20304040c800004205c010514081101d40d00b003005807041e280b81110a0300e41c1c0c0d00080111003009a10010540103a941404030b5010300c0c007510f0302840c0280e8022800d070441d800101524460b9040c240c042080342c5c3e019080310b0b02e40240280c580000c0d0101c8000b1f6403040019007060758050850044840156500b0040b00d40660b1a6821a02c07619590b501400600c07100340114a0507101c1003011a05000302e41881d200d6036886071070520301e0002c441c0340e10012a004407208400080d00c90501c840c82e002c5058086401c20ba03010061894000d0914642c1c10034072601e803000781d040b60049140d101ca0307600c6040414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 985851366 1250 985850116 985850119
    0x71212060b03090706030c02030a0f0e040608060a0515060702010c0f14031e03270a0606090903020c0f0108130809060d0504030315030507120501060b0f04080f010b1f020c 75
    0x441d88400c0c0310101508220380344486407140d80b00014a1a11070f025261040905801440c0b80c03491822044800c2c508191101d020300c00c0500d02c100e0030382c441d44540001046e43d0005000e446c00c00101c0c40d070550350f025290421146124840300003607130300c40f404c5130384507542402d01445590652528444402050a01400310303482c0c002c18517400302c000300041c00412000d03000f14811510003130380b10b000c42c0404d4404041c5002c41011401d40d5809258010102c8504801203030039580240c1d031104140e5425070416108151108045010542c04001c102c880e0902200c0c1c03407040d0816207000038014a401084141540306070303610310051003a200f04654851a018140742d6503150002c41e030001900c001c4e1030481c0001d1610120340707520b201215640081d603900602911406240082c104501806e011050300c0c00c1d50390350000034210302c81000030b1202e100103c84070b945036458001841e04111f00d050503006542d050070648400c82d035403001410007860034403031004204403102d1b40c224908a10b44102c01d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 985852616 1250 985851366 985851371
    0x1a1f031e0612020112141302030c0d030f0908030414060a09091815090f0303020f0909010e0402030114010e13061b0305010e011a03040f02010309150f051506071212 72
    0x81115110402c02c1c032440c40c000e0725000b100b880e524121034215542026140e07101e446650100b51a000c003403415100f614001003c540d1301c0026440012085110102c04038003003040c00440c4085a60012413610040441d00c02039410207142c01c1c1062103140189040a1103800700140340a1503500070007080d0090b040e014400c11050328801015090b04158020607200d41b284016640340117107590003840480c0350b010101000001d02e55800354083e4000d02c1d81045003000c10710800c01503456517032110b40206048120400c0c90705150050500319500700b4105102d180c5600b006224490b200c0e00140d8010901452800300590942080002801e00c0000480465000a900d41c0b1103075058000e98140d035900c080711040c40e66070703e04500c1d940b204a50260310700d00007400000d0100f0007514002e140f1600605000c40d11b8144e030356511a03041c00b84611483c12030790702c201d03015544440d842075079030000c004c69400078151034490004406016250004247d4003001480c03e0700e15110310b684040340115070409 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 985853866 1250 985852616 985852619
    0x6111506150a0302090120031e04082d06040c181104092009010210020306030f01020a080406141528060203040627050910050d03031a1f031e06 63
    0xf0040d40c4001070350b41c00502d000b05840507008411450018101081008520340242c900050380d082c03500c11882203901d1360601c000146440e0622642002d050b00e0b00c6880030900801100a1614266000440d9035900030800c100000d1140080b4006030ba5011880120954004440c0f2000c1c10302d032a641c09d164080400c0010721002c090708130a440c0a04c81d603401e01280703005281c0d0340d401d005042b0b90500690201259060b064403d80c02190041000745c01c2e665100311516407a42a0380c020402c0c100080e40c80c20070070051060f28030844072168040300d142e200c1c9041ca441910500340b4036503616403080e0090f20b200700444500c0c0340142c460700741480a030740701e0380d81d90400a0344980280c45404042400d51031205020100e61484d00402c0d0120100a00c086040c9018800300c02e10085c9060601d003452103010540c1e6031030703068640c041442543c000c58408501c181d04000c030143e949100340070302a00445081c130016215420b2050495519000400b5944079455081d00c2166103600e844440ca401d20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 985855116 1250 985853866 985853887
    0x304050123070806030607090506090f030604080a20150903070b280501080d2a06021b0c010e01030f150b0703020d0c1104050a0b120706090611150615 66
    0x8650710511031602d5410140c0e0711314060517141c0c40c003298010006140300909000324070308000545200280503000320040100040072a20b0300000781d030280c070506804500d0203d000d602182d9190364440e01f01840c0501315403501c5071965200b02c1708814018405590001345030080800c203840c0741613007102030000310b42404888031840801001200403074a54038404402020914029103040721901f000a081d89508200101e905001d5119641c001038480b6844000082e8400341c1700c2d242074080d0000503601c0701078503000060105c08001e98a0190030800c141c8a40c0c4c0e030441110410044207080106046480f07003a940c00511000f264100c500400c10000300b144a484405412440c2c413030303022260449441e04c0c040e51142c0c560380c8001c10011160202e0461414280c101c690080ba840b5004074030fa42011002400741020900320051561150030100700d40b50f800b10034034000b0041c606128a284010a180b5074940649560300381400d035008011a0311511140100e40480c003800b030455846941454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 985856366 1250 985855116 985855181
    0x312031612091a0c0a0c0209060a261615081b0d1d010e0d140d05090307030f08130602071a040302160f0e1504060504060902250b010b03040501 63
    0x31450107090180b50006001036501320308803206014161182d80070803555900300584510020a800c0d0040d00e454000614042c2558114801800c0e42803491800c40c0040e01c034502c4e09002585d6901c2c4240000c1c0108000c4028203104410100785103440007013a0340b41c2e05100440244042a6448003034001042800150345521003100c040c0c107002e40c1c820490444c0855800e960710a80d281c445600080c0719034006078040e40b0064584605419110b080005c1c203924881112405c0340c07080c2050b040001d0303003410160706c10326451100c2c4042c180101217007082540604103080403c402055664001828000e100c0e60700d10000e003150f004210100e81e868540350003922036003610415605124006800b05140d07000d09005c00c00d4135442d60304610b079a03940003400100c164041e00401d406ca030750346001040300e481d01d018101c081c10031000c0c00f60f81e072810048240c0f1501400c68044000148405000300022111200ba90448080d8011943c80c1c0d200c41c20074600502541d80c207000c90282ca9514154201c1042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 985857616 1250 985856366 985856393
    0x150a21030c12030914120901110a0b01060903060507030c05030109021b03031e0705070b06011d090103060c0f0201050c07020607031b0c0515070224070c180605031203161209 76
    0x11410001d03074045180fa6241d5540308600b4425420400b480507d010754414a8030002e00045031307003102c400c520540c507001401c401c03e07002000010743c892801c0c400c1c82890f0054640064151a0400035610401c01c010114041070041c0000c590700040c00040000003c0401a00c1e81640d0307064a035a414000e1800b0400b03262066003d443d40d5191001444190189040c0d5a0481c0c11440302c00c40744d912007004507190500011560b100080301c40d01d02d41980c0725070310170300e01861007900005940b554010020381269915035501e42160706082c20030519210a1003a0781460741d0641340c25495000610b41511410540000c04088030b00c4814507405101045400d4030132104241c448035101a2200c0c0f42605901c0b03040400781d000340c1303580d14406610103d03150340e4042d27090050009080490a5036407060141d00e5230301002c15110048000c0507015100e2058a000342070850080c005488101d01070b200d0350000821120024000000248071107000b0354400d90710702d0314880c007001420041c0c07a01c0c08544040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 985858866 1250 985857616 985857623
    0x17030106020d020a05060708040c03080a0f0206060316030b07030b03121909050918010b0d0c030b0903072003010618020310050a0b0d0e030702040c08150a21030c120309 74
    0x442c00310190712800807072030f80d071250342000181040d5620007e041d80c0020025008440c01c205408000011a20441c054031f43c008056039442144040d24400030701d400000b4000354400d801c40c41c81d980c1100c622000c00b0040700c2d032140c80060240d50718582540140310074604039415000304034225440300380701030003080c5400000c4402041103030400f0044030000804d01480d03801900c1a40854200340ca103030b0741c942e003110080001107007801440c004510704901d072080c11245628280400c0c030401c0b10704403070396900445070302c019410040c0c15204c002501e014400b078200ca443c5880b801c3d0710300340c42c00e400100c003500a280340b0032000f40c86030f10040000d60048440010460802001082d189048000c00080b40c3c8000c000504016410010302c000703102075601120b10744800c00c86440140c42d40e020300001030404e500c404034549084103210004086441d1810711400d00c030700050190140f814601242c103900901c0610701c1102d80c0c030701510000c1d00340001030040259800107508cc2540740d042200500e21 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 985860116 1250 985858866 985858873
    0x30103060e070f0b1e1303020f030d1b050f0d11010b0d11010e0f0a08010207170a020d0e03101103161707052d03040b070c030905011b1703010602 64
    0x1c49441d031034640c1e21501a001c91403c505030100440e500c402c002c2c0440c5070784503840982d495022104040d1940c03040c50111451220100100300390325042d0818408400140e01415581200790700c010401c061140b4001100d01e8032041c0340c000d0101c05c004140caa422044201e5140c006104e00203400607200c070f088980958207141d02c1c28824105a400300c0d002130307404000b1882d004440401036074010034412419400803101c0482d200944c0d6100149401007840100040e90396406080202000c492400c550300c9044080005c2403103540d0000b0281103c0c040c40c9408031307913030324030000103801c182c44188241078181c02c4c880900c4686e28181c0003140940d40e64940034030050700003c01030354846242c100c1c0001d4103252100294405019000a001c144c450540d203c1d1014a02e0f10780105400c3c0b034600c8105034000101c1004204502d80011b1074000320541088003101c000351360000e00f0101f80e07014072810070102d4003408040d9036000034007000c0980d00540b0024101c03864202d032145034009209200041c030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 985861366 1250 985860116 985860131
    0x3130b130906180c020c0a03023d0201050601090b1206150310080f120d020901031b0207080c01051204020f031204030308040b0606030103200f060406080a1a0f01080c09100503010306 80
    0x60000880d11001200a007080c48501d10310b4003045488060303211502b010720480013010b0110090440074020780c0700d0000001e803489110020003401c4810042040d8103102801900344442c0c01194240c03480143c0c2040d01192558901003c644408403011240085240100510585181516141003a20f01080c2240c085207040c4540c241d50312001d80101c82d03022820000c0200030041500100640e03138060402090b0b02c034420007101403418000c0f41c1640181c0010009010041e03086c0036441071041c003460304a041080c0380702a40181140984001d1050b0400350038810300d6101800141c4407100f4001005407543d99070304000d02000c02c111012078034030051600185551034120149c0341a42d0b003000411a80e00455940c082201184280c643d42c03007004090ba006169072060b005002406482e501c85500381040e4a41d5000e44071196680985c02c80d10030701030388031a104e03554085400d8200340381001060310f81618081440c402c280009401488440d1941640d682210040d03040702d104810130005017 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 985862616 1250 985861366 985861391
    0x2c0409032d0507060e011103090303100b0304030f1b17070303060801091115040509011401030b040903020c130609020a020a12081e0702100f0b040e03130b13090618 72
    0x40c00c03250001d00c0031800501800d030125099030310000d600c000c00000000e074580000e500001c0c40e04101d410940a0b80000100b0802001d19a421380c010b100e140f070500d0441c20b01c0d56000d891104541600420030202030200c260700101c1d5000c400f2038a420805141080803102c44489050b4011b03002580800e040100004030030005200b00c4c2c1103107400c440e151807100c0c00c60080020a150103107418005180500c4041070560350040907a000703244008885140c81d115600160646901c0c02e42144150f01c1c1481c0900801e03004a209440740340304407400842000b00ba81e4180050859030824218288041101459030380c0009a102506004048040c18500540c03c22200031300e080307801004041580114050310580b500c6466001407440c0162040116420100c000311007400d03420b00c810545031008030280342042d228070010194954007562500b03140a25900e05030aa40c410f40900d188006800219414070141071400340c5030100d4188000c0350703603c1ca005e82d100002250051424034010358501070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 985863866 1250 985862616 985862687
    0x92313020a0201141b2109070e2d060a030c030501090b100b040b0a0c0b0f07120e15040221010b0901050f0904060b0303130611060a06062c040903 64
    0xe40c2d42c54641143d0004480d49550603078001c046461b0f200c3c1c0b0602400201c1c01041b20f026031168076104010142180303400064841180040c0400030a030aa4100541c00c03441c0c04221800350550068103a146034540d1408140741000035880513006800440b404400c200040d0802d07101c09002c4d1502c1101034580100c11005d13040584030300c100020040000f0001d408044c0007905030b540c020b0404280c4080944c441d052480340440710144c03024100410007039a203810003030403550790201c40010419070450320f601554411120950640303405c0b2010005003103650310700c00300355018065244018064803c0c8510381c0079200d12802c09120742c240302c00100381414240741d032205220000f17000d803406840b5038440ca00181030070104150940002c000b0b119610110050003801040c050792018092500c0c004043e082c80702c040c2214446c1d5003031174004c015007540105030010036a5a594040302050380c2034020f04640348000c2e20700e0740040c18845114107045d0041d07820284910141c4002c03c400d0034011103100c1c0e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 985865116 1250 985863866 985863871
    0x5071a0304120207060906030c0210060803070c1a0a080402030f01091202010b010c020a03291008061006090e0901060f0e01060f030912050f04330e01092313020a020114 74
    0x280001d030041062074030a800122403040b0f03074015240300d00e0300d80401004cc0c62007900300100c0ea41c0001962000c0141c03d24414004114201860010403081000f42c1c0c05845a01d0301d40d01004003201c0401c2c150350f81403141c0c0c0e000c1400d1000801400c045864602400c039200d00364280076520340760420480c0e5000f41954484903500504868200303055686101c0d40c0c03141c4c1c1ca000e4480c908244085200381c40800d1035540901c0000c80040711091612040030b1400c00010400d0344018072610b020844a03401c4450801612003094020600340d0791036250740d004103100d030f002d00c1001403044000114445001041c42c143d07a06541d03070804180d40400c058050356550b00c0d0051040300349017580e4042cac038403d001a00aa40700c0d108042d152a950fa0705840d10b02902142c199980040a220446008180c054042e8110010b0911900010303440c40003900c2203e0500c0b0340c50290400c0501d24001c542c82119070042c0b80300c014142caa01e04004800700300207400c1030300c0b180d01540c40c03c00b0188640e040d102c1c1061 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 985866366 1250 985865116 985865129
    0x3040b0711060c312304020c070501030504021f03140f09060601080912040816050d0803010b0711030633031e010e061315050702060703050405071a0304120207 70
    0x601e0200d9040280000c803220b203400c071400e580898051408501c10f102658000d081268144010380d10b440c0100400b0070380c13085117a01c1284100480c802070074000c84c841044403400d00780000c1396561400450508658164041009860002040c42560b015404050200c05944043c100b81d40c80716001ca10300306082e80c070145c40341c2c404000154250320481c2c526500a4000707054403681961403062100c250000c1e00203902581008007a20303a24680a82d40d0801840102d0758904041155150b43e0200d10040c010031142050006445042c401b410420100800e00030b01110b000c1d203448180d00e403a58000c0d1245590020a039905040440d0900c102514424802006070040303030001400388101c401070441c0001c00355280c0c00075948404c0305001951090000003403501260f07501d0b18100780d9103010755403040c203010328110900070a6039000950740d5100c441e609001a482e1030303a040047c81d1010540c408403031003021104c503103196034134180039600540c07045d4158014800b1001c0c3c00d98541d01d181c042d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 985867616 1250 985866366 985866391
    0x304050d0b1522110d02040303081807030215160f05030d05100609050108100305011e11070f020d02031e010b010806030c010503191107062a0e040b120303040b071106 73
    0x3d95100010741d105255070340c0403210441c41d00301544165001c0e03810582c8190045065142081030400c0d00000c2030040046900240c02440d0070760f400214820240c451070300800d40b01003450040e00303498041012072641c2001034000c40c01113a00d0095074a91080c00c0544c100c41c02d1502056140110000d1174054501540350158098201300044a2070880140001001c146c03c1070b002010030000e10881083d2003d2000e80040361b0550401c0000b40c0d020004900c622900800c0104c0c0807034040c8a44406560341100d24080244003800000d140c441348024880718102001044043c441c4c0544c040464607200b82c0352955555205000c040d1101149040140030450030800120b101c03d825002d03081841d06800c00280c001d840c400403030f20940003200e04a40095541c9003014542c003c0c8940d480f000c940c1d4a15020401501c19401441d0407a40050203005030380710719003a402c0340c0d50004c00303c00241303c02c8112038030380c502418110809041599010041000d0082490f028000450601d101d1380750a03041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 985868866 1250 985867616 985867669
    0x2401170c0307030f03170f0c07061d21070302060112020118060503070e061303020f0a03050a0c09060905060a0501050d0207201f050a1b0803070f03240b07050304050d0b15 75
    0x2a4601544890130403904180c1cbe6130020489515102c03101c0c1d0845501e04014807403419215511805180c4a000b104284201800f120000907800112241551103058104405450310310050b40c070341c070b0444184c51034206106004214103502402440c861050744e0b407088c080103840014071440703111f004c0314062000c2ca940018000342c102022982100c51000d0040061980c0d02d444082c00d100700583c0c200e43c1a403140004100c40c101c0c03030140c80041c10541108100c40c0c14a0400501004ca49104090502c01c02207104402021680d041c1c60100360402c14440c0180d04418100201100071042c042c421011150f02d6800c014000c030303ca4000c0040c54031131503d8a444006c0603900d081c0c1004040b0514800c00540d000010001c8000d50f025812030f84840a0319a00c0d84405000c0c0c8030f8107100c02e0703a402c0c02c002d00076008040705d582980c1124512804207a481c0e4581c01d00e24150303ca560080d68001c0142d2803802d0401003002c641380e124120340c44654442901c00c01c10002c5401711ba604c0d20402c0d40702c0552 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 985870116 1250 985868866 985868881
    0x10509010b0a1d1b0c010b0108070e030d0c0213060b03100e0c03070e0406030c1707081b0108100e01180b0603040b0c0a121104082401170c0307030f03170f 68
    0x2550f0422428503500407014255460320611754480c0d1200c81701651074a0002500b540c00000e101d030400c59a0800d0003601403401b01099642060100c208200500c07110858159110900c8464071b05100e403409001e40c5032a00c0c5282160740c025500b00341d00c011071803000500143d2412181c0d00600e4100581481c40c2c80d142c604940c43c0480c0c0b40102e51250703695400000003811540204c0040242d4001e805d14041a803210604040041c0c0c4032540d284c0012180400d82004403540a0081d07000f400e088403541c8500c04036824449881d004008114410360002c42c003100c0306000035821000050382400409000f1090001c6404113950003410000804041545852404040d1640c1013032403a00d41681f00c010400241682d00352000b407101500001414400b0030360500c4007442030143c0800c018548010030400c1e200703400051142d007031f22490094482c1c01081c400d02800845150003421a04216141d00b4403600150016804a000c500841c00040b450b0300608002440340d01c2d41c034403000300744e9105030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 985871366 1250 985870116 985870169
    0x20070e0c09030a0c060806030c0a060f030209040c0503040507060923060c061f050a0315050402031207051c1d09070c06181703040f031d12010509010b0a 67
    0x140110119001445049040d072003c20030784200900035804041030324a0040302910003c000b0300943c1c002d0f001445099140d444400c608404c941140c41c201c40540d003d00d00c210001c0c081e107182994807a080060800760030b035101c8061401a40140c00390b81c030903aa5420151821245885411481700f20600c0889525108003000c0303c10304c001803e41c0d0716000301d40c5192400c0c110101c1d00c603c880086000900082c980e0b0225aa01800c01030351f0840d00d89085071a8000c5c070117101110f91000329101d00c0000d08544040c002101e00015007121a92100c001e80b400544403024204214000c020744591210300c503115003000c905c0d07041141102140c600c164020f01a440500403d41010700071240040c4001900c0342c07007507242c140c21504082c1000045880d041b510b0312003008058040410a0040c00b0109070b1441001e4000d80d810306142d4481c00440c0c10281c1c4400d00c0e41d0845074419018500040003d106401540c40307042002c0081205052490412a06600c24040c2c4034070800b072040e4108925000b038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 985872616 1250 985871366 985871371
    0x15050309150709240f0e0315090705150901032d0905031c090c0608040206030115020a020603070806040506061c110c0106060906020c24030a1b0207050120070e 70
    0x345041072140c0e8844098000c0d00c07002c42407040700c001801e82e1302c0b2415544400403801e581e0540c83c124102d41020320000c1e81e520100503080f1a084041e5000c0380c0c041104220010003004080c1c800710016030400312101c1035421108103540440d00302000e40c1711800410800c1d0700004003480303900b800e104812212000030a1034010484007480100110307500f003028180540c6040d01070340c01c08218041185403241c101401a4800e0003405041802d00c001607070742a0a07039066804c2c10741070201281050758124504818400040c1d0081000000d0066055200d205144100002d542c2445a5294482070180c28419200c5003041401c02a4a8170b030b244030035401601c0c400070340c40b10140c00c140312000310300d0840307070300c4c0e4495800328140780010070415806102c43d280404046400c4414207201c50604000e003158443c0000c000348000001502030030280c0e104990080404252404140300030300d01030340d95003083c05030780d0101e0540c25242c2000d03408002500d6040c42c000c00904245483c0903150781020170b02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 985873866 1250 985872616 985872631
    0x13080313020913061b090302120709090f20011202090301110a020106030b1f090203090307060f050714250312050a0c030e0c030a020906011103030901061505030915 72
    0x1500c04100903a0301c0140c00c500544181c020002c60320110718140c002c480750320001c0060001d51724844010507401000c19001c40360140c600613082ea0b4210b55103030405009802460619282010b000c003401100c001030503040348901c007040c1500000d0b104c000a00300c0c054164900040b010f0130040102942d0390080c0846440180003c2900c010301c56640b60140c000101070340050795190380030414030400082d2160464440c007107101d82a41844001d01c00d41c02c65004a042c1c60f900000800c0706004200100d404050304034504026908078101c005c000b404042c1c0d80c0400050701000c1601182010408550000711100180241c008590081c00145011104198103101002d0780c2c441e031154190107210b108201020300054103600000d0040d040790501c5039414001c0d8042000100240c400080704a0007640449040d000b03030791400012241c540824940e40c00c00e0001005100321810150840d5060303504265142d090710022003002c41d01800100c0d82d00241d68024054001c2e02c1c404c0c5840c5c1c42d007220701c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 985875116 1250 985873866 985873891
    0x6030624170115090f0c0c08040605130e0a0905060105040204050d142a0306010b090904141009080d060506130e090a080703080f07090b0906160606080a1505130803 72
    0x80011021405045a03030003004c12545414440861845a12a01280d8841d034200820354400940324204540914007410062020000d5045147e040504d219001440c0c401400400742c030341103000d18080e200b0394404580c1c510901e000481c8501d080e0080c1e605844024168800d41c0111b41c9a503642d011107007038042e0b030703902428096010528521440b20b100e501005e003003a1070f0419800a051500c1d50582c02580d2000040c4803e40346962200c1e1001d0700302c1d421868102d41000a05107da041c01e6650113081e90703040c54680ca9404211524002e005094070f10704003008015501c900b072103002c0c0703d142641c0d6803407c031401d018401429204241600300511208480b01440c5c641d4031541650b01a02096011412020070008102c00403c0340b07581c4901e8a1900c0102145414183d8145004802c0c500f40b05680120b0142d9075544040b0043d01e060b60815400d0000a0391400055205c1920a40c19140001c41640e42528070459000f40c90281212401b01c0c82d5034462500c03003092a41024100035003008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 985876366 1250 985875116 985875131
    0x1a041104050a030b090709061401050a030b03030a12111612090306020403060b09160203041205160609080706021203040605070e18160206040f0210021e01060306241701 74
    0x212660303140c0703028504c50403040380541841c9061601c0e00f450b9078801d5115600b090000c0c4000c44058824145504003820025203e1001620541c00340c1900e4028a400d8400810302d0f0002d2030b440444000c51080c4a034080082404403000b4641a1240c8951041030105450300d01e0006008201c08000da00000c0c50204a6592203507510b00503030f88594003d40d00c46440310b00017025880c201d0a42c6400c501c0844c124409202c1c0c00f41c01070349030300940c0b050240e1404e61351026030034442c0c01c1c001201c50b1815a42d081500b2a00c40320094602440307806108254462410049001030000400a04880d00b40130100d06640d01c41e070700c06010381802000785040111010865016480324510142d481c41c3c02100303a82c043c608902c0071070018003400720340d500f190303c4201440042024900c044800c150140c03081100031400e040141e04d070100c0d1011030314915842000600b2815410750203c0190703881088103100b03004001540f088118841d05540b0365480c0ca035a420002920400c0180c50401103100000ca62030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 985877616 1250 985876366 985876369
    0xd03050c0a080d0c0f14090402040905040b04050105180703170c0a030f02061302060714030c06100312032d0605030321010b031303110a170c07091a04110405 69
    0xc0c0d106001210780c0480890203d107444418000c20f0380202035071401002c51180e82500520120510b1185200a0b500059034031058445804807005440320400510080c1040d240074008283c0448041d100c80d481d100204a800491030308007406071804000400086007581c6411b1554041d0419059041c070081200e0b104280d010300807851002e00a48801100741000c1c14083d0408000814503001d20700b61620080c0140e40d04800e07030390210382040c07a182c0c000d4420b05900b80f4504c2802c154101703512880c0c0401100c2c000840c1c19005581c4180d003211011119904242c0035101c90703074101d030300c1a0b00c00101041490020400a800741c113403407002045990340d401c08681541c0c00321036080c014640c4461407030400200841014010094045c001e407071454000c80c0b00c10202e90503100201008601200310305003050030045540300030f800c4800080340302d14202001d140760b404260000705ca80209080012108068410301014650400c2000c8402d42c0103001c100080060020800113031030300f8480400c2c07030b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 985878866 1250 985877616 985877623
    0xf07030b19080f0c0910060c0602090a0807031a0f01050d02150f121303020c24190305150a170a05030d0509210a03022b0f0f0612020d03050c 62
    0x80401002401540c44003803c0503042c401c8410503580288803850500c0a98207604000300c04448907460111008503003840c0040c00b03031080070901c0d58050064003004c0344081c00800c0e0041140d01c03540703103a8280c4c0c0d80caa4108406100c11107580403e454541c1c0104001c4c1007084c01c00c8107203440140a100c01d000d6900b11025940c0200e10031101c0100c0c08038920002004680d40303180c100b02001800c07803c000c0b01381d40080d907980703554203c2d80c012b4806540d01a807418000708e40c441d100007a07988141d25501118000000708203540821701c0003d0820f030102d04084d40140700044824006410810b08604020301c803d4007000204184106100b10249040850000c1c005005500c01da04c00205460514072001450109941c04d814034061004641d07103c81719846003100c2900c00c0301c0c1009a00e83e1075055103d00b410106030b40441501c415071002495841c000c1e072196a980300b03d04010040340c24a5103103001250940d0144181c4d20014072441000b600d00084c40082d600c0c8680b804500c0c011607240100d08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 985880116 1250 985878866 985878869
    0x201090611130e04050a170f0408012304050d031a0307080609070614030a0c0c021c030305090a110d111903050d0f0519022406180f07030b19 62
    0x50154001c60058009410710a42d0001494848800051410702d038461a444144000c00207102e0a035800e903c0c001100d0401c2a03403000140d1a04003a215691107001c00d02070080584c004031502000c42038142c031595045480c50107160000010300480c40c01e134074158010301c03c1001d165080010071309100b100d69410028072014002c084090450307030824282803071402611380c00150074050044500c0421024040c1179075808540000b010610000c0041c06480407162040040c0d0846059a862040c015007140720320300e010311a541c00c0006da0b5910009070740b21031964600400e404440c0405540c2c901c2c015102d40900ba000351b1540720b0411001c0c000a25a5400200f01249103241000030014400c0600c8003907800c0125007040f00030302200c014014610f201d1000040a8502e141d654001c2840c0308011300c0c01503c0956090402d05d558200300e007410031204448641c8551b0503171040608090b00140c400e40500310000061045441e50f00c4150080c0c1280c001c02600102e100c0c401640202c0032610410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 985881366 1250 985880116 985880141
    0xf1b051c0f02040305011e020c190201050918150102030a0f0e0609040513050f010b0901171002030a060f0f0b030c03180a030c021309030221131707060305060f090702010906 76
    0x60b1f00360541d02e800a02d0201c0c03400c0d4100e282c8140601c0320300d42000301f960900300c01c0411144044407030038801aa081c3c028696603580112524030b0501e081043c400920b4080d544541010416403070044c0126030781c1c0705501440c00003c1d500c407091440503004142000f044040141840d040003401c1c0046002c031001164280e000c45250070b00301d01480000c1c000c0700065414400280b1420b8945000708030301070810f100f1040901b12008030f9500e000407c1c4050060181d03283e50540d5241080c2da08003024100174029205000b8010400041c10410b01c0c0c0c0754001c4941440d43c05003035558905030345840e034000900010712070701080d031080e0b80c034517050061076141440f9858030740440302203006204005228488032407410349003804610210b90000341241a009805010300079402c01c40c02201000c0c0540701c5030703010081411001003008081c4010302002401880c00f00c41440c1d0f90303940300305c060385c1081e64410341082102800b0211801d0903280306038080c50038000480c0c6a40b180d601c5001301d50100e4a1030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 985882616 1250 985881366 985881371
    0x90c030312020f0301121a01080d0e121203090307080d05220510051503120a020609071401050a0e0904030309050706020f1209030114010602010f1b051c0f0204030501 73
    0x24010503070414030046060300141421030403e100c084240580c1d10040c0941c4112040b200e6400b02040340300c8031a0912800134607601c911559540c08010b645684116502010800848841c0c0b228103216444e0b05020300601c000f88410234240b2240702c07050b44094203c51842c0030400c80800480d071b550004080002c2082c900060629060205c0001c280103017504c410044441d070003110100300f001130300350b0928051510001d0030381c0320070170005c9408509070801d41d014000d80d040350483c03640520182c6000402074080ea0310309d03600c45400c00d440380b11501940f203441040c0036800b0400c0d441500600031030040c6d81090004200c40c900010f0041d03d04803811400281c5404400041100900801d4014101070000b00801001c080c040c94842400142c0041010f4001c00c41017081d580940000c0700ca03151643c944d9200d541c503000c0090180a0600d0102800341c00c1c80d100f2840e203105800d804500c600242d55007820301c2c58610105840d10703d0043c510241c03603210b401c035480e80c100a1000348019031180303000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 985883866 1250 985882616 985882619
    0x140312040b071e020a021315030506060f060a0207140d06021b0106080304151d04110a0f0c11060304052e0501090b0d1704150305070e1f11010f090c 65
    0x402c0c031044004001d503070f207955072003e4200d590000741d04c5180640c1110400204030781c2c03820b10f2006000c1d9000a041300c09540d08000b007030100204a6034061042070712018030242030320301401807070722498541000590080c0c10402420000f0302402280d01c2c3c00608035612220652205000c0c5c1e08049503040c60480c022402004008091050100400c2c03a40003645c1860725090480100c4500036911001f4426115020b031022072403c5e03507207080184000c00411812181c4c0e100c1841d250801c940010128002001c0d228026000d240c1940c10a039021100300084d00d0b0810a01c071803900050801c65003031080605089482840340724450704c00a1507540460100040d800807800e4070f2041c0d000b038001c1450a580380c40c07191200481e44198a0704021180d6009030045030811640c81540c0c4003038540000c01100c607108940c990030484c040e0005984036a0100c03440404c01244a160780c0c0c1e43d20070382c5406141c030303440780d4001e6009600445c17203000002400880d00c20100d0585c2c0c22601d084030f648407803440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 985885116 1250 985883866 985883881
    0x20f01060e1e07090902160f030f12021c1d06090c040c2c15160b010902090117090f070b0406080906040512180d1b060e0d140312040b 59
    0x400781c410910b4841c0032154205940060425140c50040c0c44c1c036290001031070410743e03210103402c1c091103a0012100702e100c407203800c0080c240c660886865000490b210f0026030340400d14001d80d201d02103071440d445450240c18206030010a000304100381d00b08050445581410002c2c081035200c0c4a00f24090800d68a44004010496050040c80000d1182078240d502615400e0900b10300c0308100c106109601e2008040025554240c00e112070940440001d030f0448210004480140302d03512840b900c441e030780d0300d800b584e00a0b03002e92400c090000d10310b4582c041c08002440780c070a410400d80010742d5101c12041141c10700f0810207400860056000203010030100c0ea000d048903500c42c40040c0500500c0c00c0981d101500c40c0e000b4a1000c01403070001c80c0000e100228030380115240c081c010012909030482d46800080380700300c001d09001e860b003200000036440c1d00a00d008900b40c403000b0440500101c25648251020006600c66446403005000b0164608904e0805074007079806085040c445190410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 985886366 1250 985885116 985885141
    0x23070c1101091412070e09071a1602040515030102180f0103050f160504050901080f06070f0c080310031a01151b112809050606120105060703020f01060e 67
    0x103100904016240900f00048400400030f51107444040356540f16600003000c3c0750381351101d6a00200210300c031030418040b0000000131084121111444a5010500b40040710505400b41a10103081a0441d100c054011704e025070103503a000f00840c000280034020071010901b207800c140a05035603500d005c01942200e1030007400104180c0401d282c14001864500980b0b0321454001c0c00380011021400d04840c02540200140c80c00b0b0800034000c01e02c0356a45410080c1d890000140303508050280070701055800f88a803101c6498400c0f10307110025061030b03642d243d0301580d1009081040ea011326a90100006020000f001c100c401c400240442d0355040114030300140300013404820521120010014216a25501002540c1d40100c4581d8046c006200814500050780c0e00c501001d031500c441a04001c0c14004100094405030441040b8035600c41c810322a0500c1880c108620030200400100324500d001c1d001440d94074443d02c180d803045038149a0a0b401d41c0d429170090881d1510740010032030540c3d21035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 985887616 1250 985886366 985886393
    0x30703090b01120c230301050c091201051519030204060e0603100603020108060603130b010314070504110d150b18100203090d14070b0c010c1b030e0423070c 69
    0x56880c020300a01c0744c0d44d9600d001c42512030105d0700381c03007081a00071507112001d03c4101204050000e0119140c0b080040d41940d20280195108403920b1260100907a41441550b00c1140c4c14950380d14074040c003008015200d04c01000440f4004e412080c00b03c016259401400001c107003200070b5401d6420031074200b40c1464000e0703180c580c01e149405003c20150380c1c0015650740091064860030b58903100d03580300e0252052120b2000d40300c0c2c2c05400c0000b04005070310f800207000c0002602544d0345552590200400e40e12445c05004011600b0b105205020000c2d80c4098a01a200300c3c40c03011942d90380c40481001e41000450056241140712640d90311b0900550148041ca0684003440c50260f6000001d000c282c0c4011014044d0024120500c1e00d046081001c48041c0102040380c0c0e40302e1518030241c60207003a10360000d100103022107006030510202e02c80031003001c43d072503100c251242940c44184402090749151120310b04000c810020122400300314601d020354841e41d0b802c1010520f030b0130440c0300011074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 985888866 1250 985887616 985887629
    0xa09060906051f0c0602091804110a14090a020d060807060c0b060a0b180102100f0515030d0f03020c1c0c03031d0a140a080c15330103060902030703090b01 68
    0xb024900c8000941c07059100a04d0380e03006000507244e94100c00824401c3c40a0704801d12002c682800b40010710640c20b80c540c401c21401c98400035640d850310710007504a008105195040b003110000700d88180221740181a103440007080001c0c20341c1e81d40040d54500007003130340501c0c081044440d08006000e030b25003005910170403d070b40d00060146011a80c1042d40704541c600100e00c40d0320804409968401d02c07888841d1142c801d0140710609941110400400d800c0c0c6d40d00d4004d2004205c0400e181c2030205171284815240d0b00c4040224a6401d8207034080d41c444040494240520402d01114000c00300d1784003234802550355100c0d524041381c9400f600300c3e04c901e4200c1c5070b02c3c031529010340c00a0b50300250850a965100341000120550030404603d005c4000c00300600034180407078a03850300c0100140704141c2481820001c20b85460f03074031190380d40802103030800d81403021500c075141906150440700302c5c1c484d9041c90300140d0580d550503030030100e03041074805800103925034070102e0074001458074460150a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 985890116 1250 985888866 985888909
    0x304060c1d0d1b230405010302010c0f030201180309180614100525150b010c03081e0108060126030a0e1c0309033008060a0906090605 59
    0x2024030791180808111003501c100c00c805504020414030501c44820a01654000440140c131816a86021a060090711201500d13104044c046840d05000b513a048a03010385031070b1000b01240d114040400c20013030080e019992512816035046040c00c503610303c0700c2e01a41d80c2150060030841542044d108480306d04c1119410044184041d0410104030300c0c1054044030152803185241e6803d07134083c01120950b0101c003511050302d0181d10201d15402e501144a6050322150030700c0c03000d40c0421558203103080c900280007459007000090152110760b8004046a103c1100150441041100348200b40c0180380c1a801050042202d174036658268142e42c520401001000000c82030302d9543c0e40101b5940e001002030724000d642c10b50300c1d142c0e07512440481440b00006c9205003418040c1004010344801c683c0842410301000001070708070768078407500010013010b018440301d034002296116000b0708180d40c40849010000341d01100751013200c0040040400c049916840c041c100400910020600d121404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 985891366 1250 985890116 985890137
    0x420030709021b01020f12100f180b0306071707020a0201140a030b030d020633040f1e0b0a08161a0d05070e0f0a050f010c050102120c0304060c 63
    0x560214841080c1c03010400c0040c3c4400981102d03018800240d00c0c0c0307000b01e510025811031045203000c010b020000c0600d0040c0810340b0b40d1400c4034007500e020700c90090180030801c010b0200d1002e010100d120304e0700c2c0700740109603801810b0001b414880706541343d03c0071644982e0b1030b5035542481d6503416802070541c000340c9a10f5003aa00040c14442e8031103191842c0010008270781884078080c0d0300030028400701408445004240c207401950307038042912a14900380d0f864484914601d1030740740303a03121512504890024805448180009820703019030364202c1544424a44145860008140844007c0300d200441c0360940e680501640c0803c83d00220442d400c5910304d44400d0800c2803068045810701c01c03c01a0f8002a0035144490b03000c0c074410001000e00b06010301a030540d0001d040090742e4800c441e90b40c801d0021401b00100382d1355030b200c0e00707401c9a0840240d90556002d6610110301c10b01803030000d8544803609a545120007001c51b1000030448000c8248414022135100351410312400382031210084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 985892616 1250 985891366 985891369
    0x1005070c06030c050912280b0627040302120c0d0e04051509070e0d03120e010608060c0906040302100f020f07050a0506072301020408010b0d0803010303030b060708070303050420 78
    0x511844480500500311030305103000e0014100320701c01000b08800104080d0001461010003607c00c43d80c4262a04041c51010500c00d00e0540051482180110700e1030044207604c03007107651120802001501507000c0c48140c418001d00741e2000b05200c400c11800750005255072500941500700c401d003036601440c6000100704038010054400b500e40c500440345030301c1c65590b468080324101c1c0000800d58101d000013180074201508043d410440301e80c000024070030640006901d030300301c500030f104000055000d50041440345011200a007203a84e0080c182d50301c0d0589a402240d0500d44e65090300000443d003919400840754141b09161000c00c503240600109481c11001031018a81c50099501c03c1c6000210501080449072140038245201e0f4409158070302c0c2a55024000d40140c41800a10350900401c0b03045807402103440b0445075400101c1608690a40e1011402009800b42058124404118900101d20460040d012061080d6404919490945880085084c4a1000000d460280029114503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 985893866 1250 985892616 985892627
    0x2408040b0f06130e0a031b0b041101110f0703060c110718090501050f010806070201091a06041404060c0315120f03031803020c100e0307140d021005070c06030c 70
    0x200e6101082070159032290340016014455010482c01401d02d8500012103602c004650b902c5880c1c0641c0307074006078415200c402c640300500444010400d64804000400103440040c19a604440614100b900c0009804020b4a07050400c0062100750b07210500800400103140920348a2041ca0310b0414070720900c1c1c0040e595180c1a50040800101f03030008184150705c09035004541407508080244141d06201c00f54400580c0203014082c002c0c054a400030f60520f005000d40b20b0250b07408020760416680b05000781c100210b01401e00c2c0e600c50b48400c00b61610051421144d401a80510342c001403140416801800b201c0c28039054940035400a5806c012110385450180303038a60300412031100c50151854214000d0072280d91030751000098104010a25500064421000e00140d907201d80c030044810003038510b52641344103207905a10007207080c441c800b000a01d0358a8410042c2c00a0b40c009402c0d4006501300c09100c000100140340814060300f4804980328540c02030440d41010440700c058000300500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 985895116 1250 985893866 985893871
    0x3140d051908130b1e06040b010c060b12060f0f01090b0607060915060b0d050a2c1f0c030b0103090206091e100c0311070803120702162408040b 63
    0x5010310346001450200c421076183e030390250f00040c0b0300d880c0d10340f54644c0d044808a4202c800072030399009002804a0525100c1e1809586d016140d1a00c588210381c0c03500e0180990440c41604074608601841c203046003007003980e02840ca2502c52600314074110601d5a0710100c140e100c1c000407030a1412104c3e50b0b0702c3e00c0c000c940c1045d800c4000401c14200d141002d0500e0144030004088491170301c180082e044201f400a400890100e10090086e038a501200106491000401d0007132074a0f01d00c0308400e064241207480c0711508001040d40c10dc0c162018204c0000440d19102c0503985440e0000d01d8500c9605200302c002c84402404d04001846898002c1005030090491280c0030b04640090076103a001d4801400c1005038004201c060005a900f2000303103941c81501703044000c0b82c03550061403443d485c08135a010940c0c40c3c0000950070600300c0260101d210f2000b42c40a000c0d4011200510000e0003448041006015041c00300c5801a085002c8188900a0704615604204290062100041c1c070403140e1034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 985896366 1250 985895116 985895167
    0x170f03150402070f0804051c11010c02010219060605090603060f070305070c08130504111c0b0a080f07080622110f091801270303050a1503140d05 64
    0x50300c04044040350091107041e07009005098240c041c8010015104000e0003a10030540f01b8164111618801030002c202c55034008002e208501010070300d55120741400019180148100c50503620108080404001203010030f481064503254140b0060a0900640360800e0b0240c000b03140740e00d41001421002030000e0900010140c80d03102050485109004000d9641d41003000f05540c2c1d195400803c080301444e20845008034100203d0101503581d10b02512205000030054140c0b076906001d141d40245480600d00d41d00c540303505404500c0e03002c1040035042d28030811000b00a16818142c11900e859802440b030b0540000351104408904a40429424000e030301c00150b000b00d042041c00101041080c000098000481d4000c200400050442022007010720300000c0140c50f106120b440101d0307400b00c1020002c03402c0c001c0d4100002e446913200c20341c003020071540001e540c03c0c1c110030310802c03000e05c0d4004e85a50300f0b0b8600a1011990500542082c90610b061162031300180f00c040c0c41220700510f141302d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 985897616 1250 985896366 985896391
    0x72309010c03140f030105040e03040303210216060c0e191701020f030c183106031401020903010f0605090408030901200d1b210e06070903170f03 64
    0x10010140207490b41050700300c640302c40c3c5031503c1d02003035100302c0d68100340301c0d4031300c2103007012450747c0100c2d0301008850540360142e0310101213072a601c0e0b02d4804541d0350031281180c1d940c01c210241c01c1c909010030340c43c10035101b0100030408645005004115044814059100e04940f050f03400710261000071210448007014a000c4440e2420224680240104454888006c1e0000200b140c0040e25000801c0580b40c6103901c3c2c41181c04078002d0100c04850b882079a5681c0d100850301c12503050802082c01c2450901000c003007806034a0395181400300200c5000b000c19a03402160410f0145000c1c0078041364919a064104582c41c0f402c00003480e04d1501070405088000001b0100703440840a41000742c11022502c4807040c444000071030314a0390341c00040401200c80c9491010280d64010415518a201c8150780f41c0c4101542294541124064820030119555844586c86107104041c408513100701c4407131f19041d06880c07031400c2616030400c1c00c0c1c403428041d0904124081c02c1d244540c06172a003000c40980a13 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 985898866 1250 985897616 985897637
    0xc090f0402070204050916090905060604110c0106060923030304060f1704080306181006050a1718070806040f082a0105040c09060303020a120509090f07230901 70
    0x1150082c0704405010350458200805c0000b94040001c8900310208217241100d9140c0d41c0c0c0000400b26005603000401d141c10100215019251a400600301c0246000103545044140420305084a11542c05400414002e5030100200480710a144c462200c0481c82000c4940c0b40d0000652280305600990003441000c1500038211f91082c10303d0040111a1720aa003118101030070011442c2e0030440c6d005206005c0450745403601d181c80400240511611a02e800c0240d00303121041d0f607503411074071441081001241d000d0503409050f140c6603000d007000d4604000700c0b040f0340621500781000c1d504080d805038009403d020004802000c1102465000749241d40c84d01e0000c03a440502c00c1c4000080105175084401044540b9010341c80390b4011882640700041140e85e0f0010300c41034442521015016801051141010500c0d031010507004440c240303407803843c0016080003d1204c03001550410f034600c3d0000700304100035400c90180100c42e000304200c07200d056084100c005543c800d004545041080c504032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 985900116 1250 985898866 985898869
    0x108160e070c0c090501150c0302060f0403051e130b0408031602031509010b0a15020a0305031905040503040305160b04090c03270201080115080c0c0c1003021801080c090f 75
    0x10140c00740c0c2e485458032907a2681c2d8407010005c0c11080c09502031030b5601c00098030345140245104a040d5905030041c11190380c488110682642c801030043c1e050082c20000030010300d01441d1a0005a03000f042050380ba40600448030b20f0741c007019001888000c01c00c010a218256000040e1019460041c3d8071000715421440802d040c1866001c04844a01e0390344103101d03c0c480c040d00311810b401c0e000d850300c08034542c0d951480390031560903444a0700503800ca20501008a07214800079640090302c2c2e41400380c806c480c110b90a040701c10032101510281c0000c60180100b080c107022200e00e072404010202092407d042c055140380c403481c8500096a0390702c4030171941d03c83c00303904501851000100014042c0018505980f4000040d21080380050b8200001040c2c40c0e6400e816009452055915000966101404600e15600c103d190310401d1055072480b41e0310340e4950840c1002c9250650300903803962140402d081400d4505005241809409810815a8032801040c1d84d20004100e07051355401c1c02140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 985901366 1250 985900116 985900127
    0xb0a020f091903050303040c031506050603060111150705130806010b030703021602130b1003050c0f090a08060a14010b0315043801080609040f0b100b0a02150108160e07 74
    0x340002c0880c00b01000300003c0c0805801281c2c2142d00a0540e045c00300349140c05030044802033302603903034410010310210b600ad500c41c0c00501e440c60862000c440181c60b09003e018060141120188005400004c01c5103400030103450a00050105800514080d411700e41c408829010080400c01010750100b60b1046002d00083c20b106050340142c0070800250b590041e00001e4640c00c0c3d00396000d4260300304291183c52003441814818803441c580349007403040221020301d40f03620201e181540980d2140f00400e0703400042c409a03006551030320001924030516002c0c440031000503800600220130074402c01c200a5403611034100d217500308640c0002c0440c41c0c1c100c002000c84503840003108500071a815420380c002d410781700c4c41d032901e0b0076242d210340c42d0340c3c6c0030800601413801c40d0010700304030040c5120b42c0068640c2c9102500620007003540c3e0f903920380703420b0b01181c940c12090392000181c0c001e45175200d441c081504803038050080340c4003606c41c444000d0085542c0a0031071040c0b880240c10a00041c036582d00c13a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 985902616 1250 985901366 985901369
    0x1703010f06210e10150501050d05060d0c06030b010306050d0203101d0d020106081506130b0f1008040605060a05061b030702060f04080d031b081b0a0c0b0a020f0919 72
    0x480c04002c0303c281c4848060b034901540801c44299842d00301c2d510fa00200c2c8182c0e800480e0170503034a191400303642840b0071010b000702501082c1c11030318440d00b403000a40d005000c41c01510040e80c0c002094242d1600050613101c0903031205028a84021892000d80c4010a40d00034010020202041d850f10a4400000450003a030307107601c1134050100481c0a80f58107400c01030498510354103c0d080c04c802142c5c0804902d40c25902036500600200c12003100406941241030f4560000307100f1502422200049282218120090000108514100410402c141c400c09421260640e00d0105050412011074000e08c0b0340103026007c0100b00b04030541450007081150101fa42c06003515843d003540c0603842e046500a4002c02103d4082d403e040203901e0722030300c900d64802c824010f0608404039581c10a0714503102c040c0100b502000c130b21070b00007842d406140060019824560754220309003000c0c00e040705000301c0600050480b600401c01010340c1100074060704c2c06250b085910001883e500620407052140070f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 985903866 1250 985902616 985902677
    0x114152206020a06140126070e180d0c1e1e0615060503070203090906061e2a0c040e0a0b0901021803010c0801030b13020604090203041703010f06 64
    0x21840400d250b0303408244044090320608050106900510310190081d409005040c0320b0109141402408600e5051307070001c4030b840c1816213801546510000028090842c3c1100281100d0101351651100400c600301550302a841d115403c7e031540d694540340d0a800780051a000c2c080c50110340706005010842400b14250440c07107500b40c0b4154500342e00035040040d104458800c1400c00050340c1d60145084070b220700b1050780076602d8001d550003045040c078800707410107801000510006440d00f8490781109514001e4202c00c079103d8246111502d62800b00d10241d100000325014403034001800007550b20244136081b40e005c145d4600c0340e032801d45002d41d02c08010741000d03252424410780101c198014250b02a2003001d81c4107000c0c1d1113040c5800d035069294600c0c009004c841c01040415180700440d500065000c82d00520203a00d50001a07840e041900328a0286078004188010400b03488034000b9800340c1c0c02c442605642c54506401d10700300c240c0c4204070522618900d80c8895a1702000d850496404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 985905116 1250 985903866 985903927
    0x18090b0106200109061d12030a020706061509090f2a020c030a140606060306011e0221042c01170a080d14060a080706030f090807080a08011415 63
    0x1850030030b00007505007507000e21b11302c494104004000c0800451f24481c15101c4024080c91a155442c05400940c050001511079580d80c42d400b00c0d003081d00440e01101c000b4241e81e6400e0160034940e4100c03c440010b210382100e42d00e800100000080b0640d603c5031140461074903158a071b21503a0301a0304200c4920605541130140544043c10091130304038060803484241c0440c1c1c961b544420a2003c14441039030310901080e01d2114004200481210500d0034411a1040c0e07181c54081108440b981384103858003000c8401e000c5810f0141c0c0c03072103c202c00c616411110541c07a60381e150000c0c2c520080c1042c0a03050082a5a94030301207814810007904443e59404036200c0d40c0d4140c010b9100009058884400100f183d40502040403854400b282d08155120000234001e804d151400540c01081c2c1c0020f006402c0b41c40b84d03d044007154085000e030030316600a821050391a22039090040440c00160003400459030b21182d8000310340c0340e42d0450001001350903940ba40d214802200241031100c1d1403005440000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 985906366 1250 985905116 985905131
    0x20406091419061701080d0503040204091a1806090105040809010c0f150504030e040c020d44090f1f0207020a030309230d110a0801050f0118090b01062001 68
    0x5030710014820040c2c1c1207900c410340c9039880318a06c40c0ca419000d941e420005806201003009850700c2c0d48030300903c51160a52601c260410784440003140030458040001c4080543c402c11ba01c1c0003400103d40c400c2101000304460315295843c000781e40102001c0a04000c40042554204800a04180c40c41a040a0903a015041e80310864020f01000c1320228001003403d00c0405460502d0b0081d00300c2c010740c5030060000e03049105000c84800d82c140b010051704002404060a9240c3c8078052610159110400081001030082c102e0085010141603000681e01181c080030000101180042c0b41d1080760b0a60500600c10b0304201c00a802a154060352080415900200700f50f04a5201030407560380c02298030500c00d107030042c00c55131074a1084d0b883d00003206407110b0000821500801050020062240800355202d159990844004070f40c503031460040f0400500c4418007080210440700400d10007444004402d075201c00403078806221703100070701025405a03a4a0040b0040c8034014038040c3e0002c02003503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 985907616 1250 985906366 985906379
    0x181615140d0603121d040f090f080706050c042304020405031501062601152f121801030e010f18170705120d09120e0a09020406091419 59
    0x289410710007102c2510b10204c0411a240c01500d00a88138401071480b41c100903919011b000150006080a1460aa5804003d800240a00078001c5024090780315951a00800e203030090444801070119500c1000c144801c100c408901c0c0180380c00303c002d51241214101c0c2030f90108000c0e02564000d2030f0705000d5403909030700c40c801060f41e46040303032560340c0e6840310031116000c4400d00c3c80c0402802c2103004c0c0048010f1100402c0c82c0d080d40e400500ca440c025a01e500c80c004444c3c0900301c0c4040700b000d00081d0344561410140200962001000c4400b2218500128101c0103914502280750131414143c5905210308031000a602800910000a41c2030040400c0080708090202d1030380e40403230302c00d840640c500c600d151003902a2042c865203c4c0c001c1040780e100c0d4426218a8010710401e20780076440d841c2c95000a40c20000c0100428065226031070812018002c01900704c1c0c140d00456000341c41070104201c044d40c402d82090894480c8141a103000d001c00010a500054010103010307111406880010304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 985908866 1250 985907616 985907621
    0x90a0b0a0201051b0309030a05071511070b0c2502010c080c030904110a02121608120f0a1b0e010201092010030504020307030618140105181615140d 65
    0x2003410100080710308120400034140c4e80030980d9894071541c0184840002c00f80503000a00344036018100039080704004000e4a01a42c1104814171012800031801100700801d0074555600100454502c909200001c8a03488030007801d544c40c018808541d00340003095900540060001d55080811f190741e9075807204910355280d019900043c012483c2c00e03445900307031590b0000e841c0ca889850703019050f20200214411242d8100d00b0307000140c202440c0c6400c0001c0d401078000c1401002542c2c1c545081c0c078124180c608084e1004028903070040c1070260b14002c000c980f081a01704501c0710706003aa03000015a0040380105801c000042100d542c403202d402c4100554003011042d11000c032406034203c241c84200700c040c0ca00c207882c000e405501888050001036582d40000704c1003510344811070990206520790040b0305903480104c01c01c40c5d5441080c040341004d82400c10020a14080c0240790348074450100700d104104c588500e00b46111505401d60a11b44a4405d8032141218800310a80f00c40405005100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 985910116 1250 985908866 985908871
    0x309050d03050907050a0f06031e151d0f04061a041a09130305041202060d0507091701020408070e0601050c061501120501060507120207090c0903051b030a08090a0b0a020105 76
    0x6242c862400700241c18901155000b05035843d078101f0059180c900641038020308002e41c11240c10501035001c0c030280300140d1140c0c840402641850061240c03034181900780d6900c02941c01040006207904001ea0340f031208124a030460313480080080d070392010302030214191043c2200b031640642070040581c000c3c0061116400310840c03c07208188282c80751425000141180200200400c4091004200c440200b00480d4415170001e024149040180c070b0703004044480468030303080414440c950601003148031140503074013040c405000318601811320110541d00c0c401d62150b02c001103440b100044650340718809482040c0031840442c2c289003006500d0500100300040e98070300103000c0310401012a4484c2c0166412103d40740c03585403804000380c542c503281d016104d5904003903100744100010650302c2c51080310800441e030303a55180707000c1c1145001e070704005a6002c1c0c105440551316500c006a0f6001c01c0865031180c0c010100d0f0707074034101400841d0201055520000f908007012445100054040d04200e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 985911366 1250 985910116 985910131
    0x30d30020309120c060a090c030204050c1306050c10020f09030d020319031404080c010626070902090a060525030c02010807080114010f0201110703030213060504050f0904030309050d0305 82
    0x1e101d0344000c3c0e16a500c038010b0340400f0f941540300c280032589814131944070300d440ca130140c0c5134100360f1070f200d0700403909031075060381c2c4054119400541c1c10828408a00035901600b841c3ca00607280001d503189980c0d07101c5600d0b4440c083c9584c0000d0350505460050100c0d0354120001d02a5031203500720003406516500f00b15801044a070b405840c840c031291080c4144500b5039000380d00c02d452521075884041164110483c1652150b5880b000860a235019425201c540c058034002c0c5035038030005410203410603d0342d6101e1503a43e40103101c640c0050b95052860001e903078940c54007a44844480b40103203034001100c15144400401d00300720005043e8000f03121f07507045000780c8070321180d44caa02d101252024024454171040030921400902c60358440c47d6550240711403032002159003d86001051410b90102d10202c003c680d000615000e80f4200d51040c100515450414a08080c036102c04244800c1c07070040520703c1a0a800c00040402d03000c5da00c655002d0390000b007100d404039a00b28002d8010001503c014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 985912616 1250 985911366 985911373
    0xf090c0e1005041d0103050a12020a140d02150f0c090d06060603020904180b01141216091b020304062318090603010b06070f02010912150c0e030d30020309 68
    0x100606002504d00c41c1200d520800400c0495200e45412482e8404040c00e003007103004444002010a2107038074228510049540608811040e011010780350601407041d08150f04409030411049c801c18203d40733948107001019450307882000500240d01c560b8405030080c0304924083c40441d00d00d5060303001d0030300321905480400c5580030401440072030f1401098010244d844c0030b001488180c1008500030464500034065156070b580d003030069801c01800600c01c448001e800481004803140501602c4a0202e0300740785141c1031110488003c0d01c9201342d01956040c030200801144211512030032071800e144000a4407921a02010004200b014541d83d42c0361017148083c001c00c50a18042c41180c0d40c04a000300801d18060b00c595030461103600969061f0b05014484c0400070700e43c250624070840052080000760000240c0b0b10a05089070f501055203020016140d0f00c1800545001079011240c95560400c07100b907010740001039180e5a040308a0000705d1100001800705003030b0507000345000d120220b056 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 985913866 1250 985912616 985912649
    0x2d0915052d0a032f040c02010e01050f01030f11060f040b13091e1d01090308090d0c02012709061806080a3c0305180a0f090c0e100504 59
    0x30089880c025000150640d1000854506134911821032540142d02e0b2410540006103c040080c0c200c0e68a080400050307512080d140f110a1000e01c0b0340743d4003078440840c0421950642d10780f03003550124081c0c020401d41000010000c01d03a03407242602c8641c508a412030755219100c075403a2140d5008098100c00d5014002004070740b080340c40c0141126504182da03050882e1880903040c001030074001c007091f403c00301c140280f403010300400c0c041e035813880d0700945540d5035600300b12503c1344c5440c2d0400780e4001005059000180140c1c0e000f039040e80c0420304910440840c980304040c3c020300140d180e0110381520701d42a00000c03030034128600c0100da1505c176078041081c182d465401ca920344800c4c04004200080b05031800e5203955020b49050030000e00e0380b11a100c4a507208038540000000c201040d00801c02c042802c00c3c101c101c10078080d800c0b24041c1c1d1402c0d10035103000012002e030701c254010300c18140d8079403205001842c865910076528070401001910400b80d581400351142e406402a000c10035038840d007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 985915116 1250 985913866 985913869
    0x328030608030a0c080c060903070308010e0c0403030e2d3a0c08060415050106050a021c02010902090a0c08010e190908120f012d0915052d 61
    0x6030108507058040a14a0441d9400d01180e412a540804995882d414004244210f4003046120f118a03045c030029a61032607142000b90002105034080d0031a20001004c20050105201c1620110303541418502c05110905000641003102d5a000c00207206c4160850418600140151108000d0990303846404a4001400c400b500c034900c00d91040304115140b5207484610b500900e2048540a085802e0350544c681c1d48281c1000740966082c0c0b0800ea880c00c501040481911889004080a0034940d1500340c154001940b076000740d28601c4020840d0882940180c1d000390482800c803a07000306040041d1401c4820b46004002e8001285d000510740c00020030200c14000390300e030040082142c103060382d9031610109406052441c800702c5089900b1b010380c010199910b180540241d04072004d0f4442d541c1001c5060344081c02601460b40840c2c8102e94000c1c10b60700c040e200c00300750380c140a008202520074190040f0740755400d0740080c1d04110b0303a1813100c0d0b10380c001884c54000d86110a0a50102c80c803040c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 985916366 1250 985915116 985915121
    0x10f090303020c0909011b02210901020606010e0609220e0a05031207021006030609020f030102130b07080c0a150608241305120c0111031b0309010b03032803 69
    0x30040c00b50f44080000f40c541d152049026a21000342c170700228150403078003454400303000740b91406009a48165660741d090401503111054100021980604295407900001e50314000034008074140294000c881c03180e902d0b003100320354102c440980428140d8069081c0d446d4840c14002c04e403c401391418000da80c6114000ca0901c90b07490b00301c0011420000c12483c90555808090800010740c424500c40f030301c1070005ca0048000a40c094000001c21180e20300610249241c14000c0511a910400030742154210480d41e010a0b92070840e80c80d07486040c580361001807480381140b00d0419116003051f51042141302c080b060602c1040c1c0c82c042c0066a6600301540d503071600d002c01545680540d072240355125048040895004200000e0f9054520f001c1d03e50310300340f401420a5020b10400085c0040d40180709004124180c2400303c52a0301c0c500c0d040101c9511106807200803334940f0b41c000041201000c1c00d4001c07800e0100000c081d20382e91464100c00e8001c0700041468030300c0341e08625a03183d100e0340c001d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 985917616 1250 985916366 985916369
    0x160516151101150e0c040e07080105120f07091d0102031503121204080a1b080a030e16090203061306090515030f0c12101d2b03050a0204090905060402010f09 69
    0x10b0f05062055402d01e110b40c0e20034040200f031542c801e0000d0200051134444205058007407803031034540080f03650500e0b045c046a500110300c034141a60041a41140000d4001000011200e43c000d00003109103082c1011368a4034400d601c040b100390b0022090090440088505420f802404c408880d89051540d035003843c4c41c051a40d02da41032680080c002400b05416400400b0104180d1802c291005080c0e40340000041c6a0030003078a0700384001c0342500e04c03103030035115507602c030b0014100815801d100c1650034039482129000b4000559004030204595448150030304510f1645030005014640d10b402040c8000d0608803071906140c06020310024880c100401c40c9402401140c1c06402d680010809116010042c1d207c000000d1068103400d11082d0050b1003990010780140008827030108000c1e122034981071020035190201d1076110b10108070910b44540c02040400c0134100810070f60b44407402d1030000d000d5a484010214103000c400c4d0b04201010642c90301c664401d88035040840481c41048a464216 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 985918866 1250 985917616 985917641
    0x2e05090c0a0e0f0403080c070206121f260c12030a030c050313060c120f0506090108151915060201020a031d0d0e030c030d1106011505160516151101 65
    0x107450104e408244034559081d401024001c00c14505140c84d03000c94101d6000c1700618900040d1201404450410310fa050710b98042e040c02d00781086414841080804150100150307155010640c421034070030000e000f142c0140d0782c014510b0f1240d1480d400500e032a03600c0107456000103480c00101000c614040d5041e00e0041500f0315003011034000742d5803004000c01c4107102c40800c5c000b16030b41c0903107003d03080e00410a0f103050004020030b05003005002d00011600603003000322141c110304240380c030740100450b03000d0b480001098048001601e41703200d04028020500c000085d5143c40401048040d015001400b07844140e41e82000405a4400c841c0000c20380a50308000c1a0401aa005000e911504134640c03030b80d01c010180c52a01c0c2102000a241c080c0d10003541021036411201202280030502c4003a004000404401d00650303142c210040c61885a03200e4402030b100b084030f010040c44030403c6004011565100500c2d80740d1744458000110000c484900c42c0060300c21940b030412058180110010f0270710 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 985920116 1250 985918866 985918891
    0x8010501051303060f0603110f010c03260103060501080615100c080f071a0702030c19141506190b1608070c030c170309032e05090c0a0e 60
    0x241001100c09500c03040d44100c41d49604480440400d800e8400e00b2150802d000001900034a1071400d1020b40c607030b0081c0b252240119503c1001145d1300111103607000755140c581203842e04075005000190410856140d0300ca58034060001c020482c1c5540014180c8903500c0032103082d41e4655500840e90844501d545400c819244903085006000b816010300d01d611909445080c16200d80300300b05a80c0210506640f0501c81e0200c04800442d800c00c00c50300089284091440c0c040907a0801da0342d0b04546110074807080140704c40106008200484481d441c070700c1c3e02521103407070041000150111059450510920180c04620b01da071503a100f01000700c0c0d243c0180c0303600300301807441500c80109041030251001c9030204a0600024107420048014500c501c0c80d043c00c8a0078000c100b840514104044102c59104001c1c0003010395000400d1800000c500151141c82010188907440070070111024409941c141000d000c1c0c500c0012807140c00104050703840c160160f6030b8a00c051349860040ea00b000d02ea80c0f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 985921366 1250 985920116 985920119
    0x33303030f09051e01080702060c040302090a06051903140d1227050f2103131401090302060f06090c041e030b040506251403040f06110a0201060b0a0801 67
    0x24081c210708100403115041225446a5800200e42c82c0c80403e440c90150034201c24000300a580c01c46c09480e000303400d5100409880c41c1c5a603008040703100341d0001912521104001032606003054120001815000e414280c44003440c09020b040000240070489040c2485000c080c0d500c80d00141902c1d002c0030a599083c8200085001310000340881451414041052594101000f0441c0f4111aa041c030840041465412681c1d000d41061400440740e013000c0d10f501c42c00703016540d100302a41d82041e0303a840c004096008500d07100040c0d811807111040254204031020043c1038000c51054496204000d80c071030b86a455604000c101c0108554054140c20309000501c0803485000c1020b0300d144120742030403200e50b180e44521111400403034080740c40e64084010028a0012000e042400d100104090000b09140c010094802c0c6200c100c691609003021000070188a0002d000d1006503402100c20440300d045e41d0503d05607603201e007190001560900400142001b85c01c0102c50003002c0b01d907118090380c7d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 985922616 1250 985921366 985921373
    0x50609031e011b0518031c0318020a14010e100804030f0528030e0109020a0501030902150d0b030f0703050c091f060203090a05030f0a0803040807080a033303 69
    0x111144031001c42950360311640154444181007808248054030307240d46440d003141c9010540302d130031100121402074119a40041e00440b008040340003c03060750a01140000250090240e2a1481344c8080e501549000c0c0009512460b1040002944820390314065640303180814001c07810882000d0311300117040100005c0c0801d109104460703e28a00d071410900c1c01140c001c0d101d0030300454109550351103035114101030506e601845040076001390540207000100d425000252800c81910a807818140c542c440b5204560720400e40d0820f041c483c0b10300356240c24103c0083c100400f80462200e020348522110203625020020301c402c100ca900c82c1c0208290121070042c00f4220b04040c049402814030340101041c2c0c06011800d81c006891541c0c003d58458000341c0030000c0c0b00800f0750049020b40c21031074070303c846480e02003007610311560000300f00d0f640da895070703d8104d89a00c20100e002e0503000000c035100e1822545900f002c40c034000e100b030381c001c2c2c2d41103002d500c903682c0507940d00340800c840050700041002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 985923866 1250 985922616 985922653
    0xb0303040f0308090a1805060108011508040305221203230f18030a14100e15070e180601140c1b040b121606020106060c17090a0308070c05060903 64
    0x1140094210178080d84d868290740d0008000640d0045c1e80d40d114020803000b540e03c000e0b0140142008086489044040c3c840038010650180c8040c1c104500028050078442c1c00405030610f124855048008884e9908400e00410720340030340450029001500305000250316140c2d8400001680056a03d8184000b080301d410f0703440f0a02a00c0c003c00340064480c4079541c248001c0b0059401002000c140c407800b0070816080810100d0314405a500e40303400d40c15940780004011810200d921054101910f0b00401500c102c1000250642c2c40104d006411402418a212042c08be0000381ca950380c443c11110411140c0340582003600788264042d4150003030400c1001c568501440f000b4000040c0d8201e81c202003800d145c40400b2060883d44420030342c0d40c0e00901205880000c1c50103200070407503d410004010301d14102d595014080302c1c241c800d00e079800c045120840321102c1004004035040c5030f4a2521300c2c41c40c5c100c410150b5069051101c001003d0404034116400000000d000d0030409046007001d070780c0f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 985925116 1250 985923866 985923877
    0x106090b03041b081501080d0906180906060f09051f230f091503040f1202030f0301060e270604090c1805060a0f030f0201110f070b040503010b0303040f0308 69
    0x180808004091412003030008016400b07440340713078003030010250303641400d00e040401030380b140d03d00c2e80c4441c40341000d642d4801580d000741c503410728008046c1e20f0381c261810034603e51340c0c2002c0070341e5141480014805401c04000e0400030304d02e4036140350313641c1e807007003002141c3c25007007400c069070180a600c903040180b0840c0719101402203415200007580e4256403099050700302c2c00c911452503600107001d40c000c1c07808071510003a809840e4901c0d442c6160968604401c0d03484034030003c0c081214186850f120358020b009944c901a400428581c8030341c1e456100070000e0280c4108640503592a41240c0204036502d0703c440c0c002e103815a0008029180c0c83c080c4402021030001c1552124240c0001141c0c54a443c003504480c00340f44803011580d824960f04201c00442c030360703208984150500c80304000040403803c1030a03a00c1d0302401d1000d80b101700d075400e480c101603200f1850301030340c084d405020907003072a00005001900c50650007003040c15996030600d56640329038000c42515005a900c20000615168020507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 985926366 1250 985925116 985925123
    0x30c1b0307180e0f0d030b04110f1b0a03080f130b0c0901050903031207080105030f0a030f0e1008090f010c0c1509021e09060604260c0a09091202060106090b0304 71
    0x80e20895001c0078604011020020318581c0d0400103c401c5d0266142c0204c2000800813a4100070004100b00e000712244145070440c00964400b040c20952031062008466010400b001034450015007032a00400091040711031024518001021507010103880302c83c0355201e41d20038000f6500740c494981ca00400c1e0080e21001e0b040010030050400952002c1c805882c04003801320950b090345c00c0c52500a002040305800003070182d4044500d180101c9000910a20304a8040c10046040c008150040703400f107917155651a042048840d100c0e150650101c2000d22912a00080e02c001c080ea0740182420380703011a845200290301002e11001040060448060350b1541540029000d1455400304d44000da4028a051848003c900e5074112410320150b5140e110307104581541c545801c000710b8a8414948680c805418080300c40a2180e20310104244a12454010100503085030346811500280840e6102200d48007a4255120b000c1400050303240c1c1610040c1d151076154908100501c02a80c20090064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 985927616 1250 985926366 985926371
    0x317120a0e0705030f0c041a03030403110d020603090c01020607110c06030606120f15030a1e06060504181b050a171011250201050405061606020c030c1b030718 70
    0x2407544d8080200e00c1601e030051003e00062134000c001c00044074a612203800205100b821004050303503020017294142c952280100c004c0c1610400841c22800c3d18800c004c0d0044400804e000c21038600041085204409908403a00346d55030074000c032007518001e19484602c6d0700c2440010142e00c1c10001550f84640058880e82c00c200e2a980032901c081c00c1070320400c032175005d00c0e022311080a02c0640307002c0140c031081e001042e00c1348686d034a11124400000c0880044840706408000f0080c083d0009002081c0051007401005808110b025070094128811111589c07042c04c2101c0001841d000981200c10003407011007070516100717540d0804011030407890990b0003290b00c00d10410016100e800385d40500310048644a500c540d4049401070740704601c03a058090a0307804200140e80c4001160250f07141510140c0d295803068101c1c0c0010100342c40d004220f60700210b1080c0142d50000060612070038044204d401e0031940480c8031441d044510002901a0030082007440104c1d03503141000904004d06000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 985928866 1250 985927616 985927619
    0x1c02090405010609150503010e0c07110d06060603141005040b01025508180406031514071409120307060f110901050d11040b070c0317120a0e07 63
    0x40865209030001d402044c0d00f4030302031203a03540d009449110603601c0e08220340303154100300301c1e0900d0070401010039039145000582c1108000102c50400c09110003d82400701031b20051902c100540380602420000078a0645032201542000780c1540c02240c210324140703002420081408090400403c085c0d0540c45034032143c80c2c070001804511454030040010722030a64003148540e0101104c81106000d510800701d4031860000415590765507034945c00001c0c29503811440c8402200094403240c0039a000380341070742c008140000c0311160004084008800c00408500080d41c806203c81621040d00103801064502d80c1588014000e0a0000d4010071070380040c110388082c0c620715071054408845068a0341a0f6406055482c001c120780b0b848900a154202071b00341e070008000340203142c454050182ca4962a0302401c044e141120058a46442072554458840c10041030b0044503100c101c1e20117540107010700b0044000f406440d500402000310900f1900c80758042c034090601410340c400e030303801140740 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 985930116 1250 985928866 985928869
    0x220e030c030a02060c03091b1908030705150108300a05180a060c0f470103020f040b0a0b0318010e0f0a1202010207150e0c0a0503031c0209 61
    0x38203000c900c060001c541c0e860001d140242000c1e009442d5000042c020701c107012048101050750042c8405990f00380c03180c4600300c40007a030700d0301191000448140c0d0210000c54640800300003401200c0c003d00845400e1070240d604406050024820046a6000079a41c60744241680d034a0304510409a03c0e818689004c212045915520503103e81d0041400025080b2103c0050881d00c00c80c08821101032200c14030301035005e0700302200c1c003c00401100004884038100110301d021314803610381000804800c0e4015030301440e480101e03d6200d03105200d00c0c00090744804548a03c880c182c07903001d8400c460203000c480c00e01014044000340079034440295503010581d400003001540c403c00c0c580c0c0c0d25000384000c140040e030031140c916011040c0c0750000c00c840c03800e030503001540d110740650103019540301040440040340280540303580180003040420788071207003410940101c2c407800c101005440e403000c02502001232004423441019010340060000358142136000700704403008640f4900140c54a0403400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 985931366 1250 985930116 985930123
    0x9090c090a09060501080a060f060c020112060308040e1f0b0f190e1915080915040615050316060e03010b1201090b1f0e070e131e020405220e 62
    0x40240c081c2c43d075118010002980e11008558100c4651034080050038202111005070903080d000300d03020300c91a00521011a4032511005150f901f081c0b408200d2151280352000c03044e031241c456800300c282c903440402c0c1c030258100c0030828181140305c1c501c12810319101585845d608444d0140418a0061280740381d0740361148100c958140445d520407100094903001c1181d00440407508003031a0050090074401100808141d20448032035051421185c1c3d50a46c040e460451a20611014107070150140010400345800407003480c1300c80004104421b0301c4105241c2c0d141c01d0403030480d4505061090420400f40201e000580c206e00180004c40c00c2c000360800f181142402415582e00c40c3c3d505e5041400b4001c0e010011600149406100000403186510f810f8038410340780102d03140300420340b020a21450044c03000e81d0f03082902800030301e041340f0398582e102d0003480250000d42042e0600781c0c1c0c01004080600c02c071821384030000c0589950040707070710b054260412141c0345600c0080e0354100d194403480080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 985932616 1250 985931366 985931369
    0x1d1b0d0503120610030b030a0803060409050a1a1605070f08040807061106010603021314060d0f050405160b0f130807030f030311070c090b040f0c0314061509090c090a 73
    0x701006619042c200f0911010342c921203000e000705842c1401402c00c030b640109060140300d030003580b11b540f2500c480002400130b01140c24000c0c4984540c2c0c44520400c926590344041c5500210100074281d035404603014040100380c81d0440000d40100b07d00e100240d1480c4550341503601600140b420541c4841c0141d103007600c03541142c00407070b00130341c000c0400b62404c01956014025901e030940c1401c074070945ca600b03a6803c030300407040c0b02181504138404070744881041e00ca10807640b40b81481034070403140d01c40004090956041e1894061010401c1c1e065000c2c030000d404035000502c1031403910b00e2000c0b0740105d40d0800e511031006985000b40001e40d904003003142201940c003e500c0064003600c6450302034100c80c0c01c420700c803140b46414400d860110307030040d5040d4111603045002081001800e00050f0080541c0040c150b5941e10b46203140400942c10360060101940710340311896692145010040001d510200887d40400c08100e0781c415801c00c03501c055045180444018180511300c2c0018000a025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 985933866 1250 985932616 985932637
    0x1506041707031b2c070c032109210522030b0403021f050903040e070203090a080d030e03070b070c02030f0f010f051303080a0c091e0305011d1b0d0503 66
    0x41d500c0038889041d003103081141480c0c10703c4d50000322500c0f6607414040340750018510000e20070a000c03034006150051802096980030700300540d980b0000032017840000c1030a240c050b105e08503a0b07407600542c220241540e2040010700c0c3c6a1038200b910300034007030403980074885810144050001c030000005d4804441540034510136009019040d6500854000c008016907005841c14107040c10300c03881c440040111010340b8003403107480c07d43d960381210580c0745226000c403007508640c2c0b44000045020001c2011220f040306581e06000d0048550040d540d20700a0302c1010f000707840d45a010601c824056404800003500c0501624502081250401e041131070044106002da5100d60443c048441c1c1c92091560202c00c0031400c0e20b82810649004101c400010000400c1c160340301102c500382402145560000c007980400ca407107541006201040e03000851204440310b40c00d0004000510803500e41e0a480107200c0001414403804c0070180741260006c1140c9903070021015656040480d0042c4010300c0340010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 985935116 1250 985933866 985933913
    0x6061201030f050c0d0b1303051c151d061c0516150f02100f061809050709110a0e01140309010506010807090b0406031508060f010905150604170703 65
    0x9050510f1420602d41c81400c510400b00413810320b001034180600245c001e0341417280401d02032124034007600d8500ca2026003030089400c0030010755600d0300a03000040c044041c107620f903154503030724500318071007040d00c615902c00e98140100098a5040440d00500f02101c4400042c40d407400c039803505400d0040041069081145403041488030041c40701010507900f03141d18003207078801c0c50076100a40780c007a4034003003217a443c0c0c681c402c94204001c1e03038202e00042c1006d6020444000c01200508004200201c0c00701d800f03000c0c56000007201c0125205080c8024200c01d00c01c0d00d130950111701150602800702100303051101c0151200721442d2040050b51107503000d0800050359007030102c009405007600804000400980e040144580f000c48401d6400b1540e003828045011414021041305288868015801611a00c001c000c4080b400104450488040402c104103548954000c02c00c405801c018480e00070b003040000300240130b40750340341c2078200b0785032825151990f460755214058101c1011580d0030004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 985936366 1250 985935116 985935143
    0x1203010b0d0b01210c0c02130e1b030c011b15060801050609060604060e060702130506121603120e03100203091b0d170c03032a090d0b0606120103 64
    0x50a00c14075449480c2400c0040302d0020741c0c1034405100d0565040341c1191038441e8445000740d40140c40701b500c0107034010040c840707904018404100030300304100780c080184601d6002625000103a003500301c08142c040c0c041e000100c0040c005490040136880b520110381451307074000012604103081000f0783c4e4481c450100f01c09107440d005900707507070025080e144990114000d011076a6917420892742203801034280324280c404030000080c0640124803019400411001d0a0802600f0907032020f031141c0002c440303a045166030a25004d555101410082c3e081c0030b41e5202c1840420175034a240c03550819180380c0200792240e641c2c0800e06103000d00104810b042d8000c400d01c07101010074030529904006401072031108a04010000c0c007000c4251101504401000c08054030078040d1008991032403400c0011681e49050a4110103407984840c1c0401a01c1e501d80000c49000c2c000040071114081d40050400d02090680d44070511100c0e4003506584d03000348204240c60355809d0302d0400324001c5004511544001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 985937616 1250 985936366 985936387
    0x2d02030d09050a11181801110c060f01060c0804031b08030c0a1101032d090f0b0907060924091a0d230708090109170915180607051203010b 61
    0x50249130400703200e110007510312440803011580859206c511280f26660b18000500e00d28010542901181241e070030000b184035451100151003805421080c24410341613917141800c650208003c1e5004055071020001040880c082110b000c03103c12040302c40c20549952107222600d558030100711510301d508095040c030240035400241c101745010038201404040000340381c13400d400074940f180042c1d4000003010103c1d08551a484040707801d034004c007804041d40040c2044100d58204590300780d018429400007062182c4100e05807030440d9005859908110300c1d0032007407a40307203d20102080401c1b03a8644002030300e0743c00c001014070349004010160756a20340241400155500800710180070000047c420244c0e4010000c2549e0000983c03600d052140c03140851540907013410328005e00102e0351650b0402c130783c6141c08000c1c02595011544e283c0f0807251480c1e44881c0d0b01904000364a40740702c4c8814610b403030038002d0040c50902d209105070340c100c403201d1040c01039a810a802201608401107140000d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 985938866 1250 985937616 985937633
    0x181707060206060a06140906070f330914030a05040509010902070507150e1306060f0906092d090504120908031b0109121e2d02030d09050a 61
    0x50000ca201400461610601198034030300c0910410007008940380704e2800000e0f99500f17940000000401d01581e4a2050604045a66003484247c2c1d1040d6154001041c0c003124001a030020390304002d0b9203115201c0078200310018100c409041c0c8030340e01140403011000304280010000d030322054890700d407541e00b0003007880000c490580054042610400003e404500c00041e0007080b140007440050940204203412038848924559168005841d94014403021a6980016040c0c030003603601c1c215101c3d20310608035070807402e9100d03540c0403d0b9280e034148203400c580000401801c1e030404100f4082c0886190a2041000301c0d80201c03c03c0396580180020000720f4201c01a01900da8503003106401d0030701c0c075010303268807845103507100c040800418041006000c1d0810101d403504190000e00182e842c1c04013514030300c00b107101d11030300c21500700c03a000e8103030700410203501b8031240320220007980394659116050795a1100103000c103512040c001d0603100e105a00032a40481d00c00c0d070281c10130307030041d2600d0440d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 985940116 1250 985938866 985938869
    0x20c032e0e0f01152d170f10020301060e0402031006080c09030a05060f0c0309120d0b040c030605040e0d050f0d0b03070f0303030c030c020a022101061e0906030510050601181707 78
    0x50600000080941c2c1a9130106035400c2d2500c0d40100301c4520540c2e00790f5450b05000001c3c48400e8040c8c143c044044c81907540c007440c12258149c6581594090000070801203100441c0c0e051030b5010b0046040c04007511688200380d02a06420000e1318140300c220009141c00d00c041021125036225008100c120403949101c2904408010911402c5042040245458444902e01540301240200fa808906072254001e254440c1001c0d1080200440c00304009020344924019035000d1030504202e41c0740c540380000c43e03c11049059039914180f4112440d0402c0ca60300c25003018032030545504038000c2c203940520103c03008001000003041c5540c550f16016054685100c4507409040c900800300a815401192042c01594101c8410f9481545e901c10402190045107402200d076290000100307000d42c0810805a42201d00316100d016545d84086000543c0c4403800010716580200a003106c813030311260407582c1c004005040c8448201c2c0c03240e0110383c00001070361003c80418140b80040e601070703000740550720 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 985941366 1250 985940116 985940159
    0x41820040507050d050c04030f0506090c01090803040b030a02040b030c030f0c03060a12150204081b04020c1f09050625030605090c0f041203020c032e0e0f0115 70
    0x210702d1030101409403c500402c41da6000a580300c8000400052010b0101d60140d0341c814070081088840e801c00955941c002c660f81c509905c9105114000c031b41c0101640421204030f01c000f14134041c02c0c50140da485070009000d0a007100d4080c0004039070001031a01862007050b1078154a900c920b4400c54400710410b005e030840124680400600450740c5038003a0140641300d03181d241c0c802140c824640310034002404415a1403d03403000c5004106000c011480c0b00d00c000802c0d80ba00c2c0000c1c460f8003000102d2140c0101150746a00c903d43c2c5d100704a0b019503680584201603c00010f6841490b03c80b00e0408200b162280f807051000101d51640c210386490b0500080390b1071404004031824a408140145e80190002c4145a00030942c039103ca080e00e030488000e440050a60080c1c0740240c5806540c54401c207100d1072003030181001d504cc0303955140c20110320700a00040110b40091104100900038030041c03451049601403941d0034400320200740680154a103050f40c0e400100d0f441c001076180004031100101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 985942616 1250 985941366 985941371
    0x1506090112080f0c0c030106080705100504080c040b011707030c080f040320070f0b07030314090604291302030c0f090a18020909070602063304182004 66
    0x220045410b1106403050140005000b960b602d409071800c070302d010800d0030003941c10360800c040858002808070b850307000c564040d107681c1400300ac0f150003030350503000781e008070b0145034410840c2c1c0559240030740101c80b000f08103041c92103802004001500041d0821a58400030a45072221110030300d92003042681d1060380c0c000e0503203090406a800800c417134204d0440c4280007001207840e6240d28001d0010034000c10b0ba18440b0402d03103594081c1840030f41c00c0b4440950101c0e00e000965a1416680e4900d42d100d42c00450103000c07640d481c0e035141c10701d0503030004107110111244d00184905128407007885016403d0754250b000752061a10415207041e810b070300003a00580560807804941e0321139070300c12500816400004241d4046c05080184544130343e080195212030b14805000c01c58002042003c00c0e144550b007920700c240e4a003440d0341e51408181d108040345507043c0d017001c040520003030f80c2d01c034074041c0007000401c001c1d800544090b4000400e03203080d281c203070070442007060f0310400e20321096200005803000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 985943866 1250 985942616 985942649
    0x8040b1215061c0507050d06030c03150204060c03052a161401020714120109030522050d02060a110102040f09061421010e060a0c030e0c150901090815060901 69
    0xa400300d03c050740781c100c1d14103441c0e0004c00c91960041d400e9402e0f000e0800c5081108603a07a00f0700150601c400d00c01a1100b02a1007541800342d001e0740212030030740700a40c990b002861403903a13044509a20019140c40382014044004007114400319421080c81e9541004000080e03d00d40c0c01e103882480d0303501620b6400003c0d062011540d80104000c0c3c221190007002080b5820703014049005071a004504410a52914201000701900000900740902140c0113071101200b210b03ca18075145800c6c01510b9100d01407442f0341c1c00500c0c00600a1800424600c1d000707034115040601039080e40c000e500030809007000c0a0041c0f242403080d10800d80205142049007450314004000f2494451160507461029030b00b80e003d8224900d000d40020752142002c8048405510308021602c0003401c80d84642000a4141703a00b0b0300c1003d900140440710301400a01500c2c90700c0d0b0354010301540d44c1c005440c190512658a6001441940c28807201c01d5000f10348a03891414a844010040c02110507000140302c512940403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 985945116 1250 985943866 985943887
    0x209060109080d03020c15010b1201120c0512010207050f0709150e041b0b0304080d050c0c150a1103010e0403110a030e060a0912050d020c0d03120908040b121506 71
    0x41051040b0720f581001a920245600d0480c1040d95201100d50401e07685000018403c084000509602404442c0c4c800c4992722804101c0b0b07100c1350254050035402441d0000e0001d0716100c10700c500307080903c90005127072481c80c1e2741c1c00342090b401c400400c41135000782400b00001045402690110000c0c0c15101c0e5030142009000c802c0080040e2018005281d40200300e051440c244c0c0008020346030014486403030b4506440c186909034096140e8252580c00c20020409440c40f040a48861412640140c9400342c0e19808280c2c084c075005005907101603d4810380c10f120030503480114087d0942031041102494075040151003400000700b5401d0680c0842c0340076001c03c0e4042d00009000780300b26400d81d40c450801c0d20494526040f904042c402c4035604050304100180001d0b0040c2c41206070702950080c01c1c0400070070a1600f069038020703022404032900c0e10f1840485a200b09051440b581800d42081d07200d02000900c1e4004028112040c1c0b0307240140101d511086071505209a400c44a040c60000c41c001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 985946366 1250 985945116 985945123
    0x13020f010f09140105070b0f040303060501050406020a17040b0a0203090a060e0a030f150509010e060a0605010e04021c09080301030c0f0f0b13270b0405040f031d130603020906010908 80
    0x4030340d00b0b0f030034481121000142e2150f81200c11254019061819504040d005400103200644048000c0391410303400142a50080701510102c1e00c060300038103c1e1a07005c2e1201c1a035400c22203012118440308000100304904a54058220701c0e0050b4000d507100c1d174100c2c0501280c09845d41205091007042c00d0b0395501c51b40c50441030070a41e580005240e940005c00d15119808422100b02c20071814244000c0011041c015444450b400400d00c0484280342c940b00b14503011280c0740e001e101e00240554041358124101600103060342c2c000341c01c0c0c0e00d00c000410208242160702e00042101c9000000004000340a42461100043c1c00d9540302c00340c140349071481201203a140b0344a4ad507061800800d0316048a00c813185040000d00500d0710214960f200442d480041142004d9942d004928000c407903c8203017000d01c9407604c180d6109860034011007aa40f020360b03d1155038050f14602221440c4c010505480d0a80d105250000e2008041031070760440c4100031006034001e04081c10410301c1c3c4007c02c020038001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 985947616 1250 985946366 985946369
    0x203010e0711010608120705010f11030c0f07020604091b0207060203030402010f0201150f18090503160816080a080106030216021509030102030c0a02121606050a09050613020f010f09 80
    0x41c140006500c28060300b0a015148a40c880421800340c031071740000f9180040000c0c5125071140b4020400308240e10303076850440701030f4508070310103807070920020b418130b15402c00410b6043c0c80440c43d54241070003036001501c185d100d81c00c4050b10648070b000c121380e408110074170009089424000360501c0d90400070000d685c2e01000b080a410000c3c10346c1d800081310300030350205001011a0701b408405a85400c03038103400210600c0b03900b030f4400b5002030801c00d10440744210318010754480701031460008480410b15021548502c140c901c4107081280c1c52052401d1580d02c200c2c0c2d03100b58106604d03010003c03c0501105016440b8105041c010004d641c0e880d0000b050400f409a4100c07004041c0c0150f400001e0b0040c000c20410a0709503200005001a18180b5000307440e5134017155003240c090304540d40c2c4000c0b540c0510041702c0c1d1094550404403000172802c2e04950391001c008140002c0c858801c1c2c4640b45040000d941c24011031a61007000000c0d4280024000072510082c2000540d01056510040425105 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 985948866 1250 985947616 985947631
    0x106080c0d060506031f06020d02060a0c09180c080f01030803040b0a021b2107030903080f07060606030b033304020f06042304050705032e0609090f0203010e 69
    0x40241c0740000980c8040050300d00944601c3e101d24050280d2014904a0002c2c0c003e40d03000d4420000b5481d00c00034900d813541c202e69019254035103030300e07402c0f8016144d000707034403010301c0791015000c641c0000c0e456581c0c250010800d404035541c0070a90000d420315001611004030f07100c41e840180007207401c0500b142c1d04558840800d04e155515060014000d01910800c4c000514001c41210600710002500007001241005010316400442a0080701c40c80313013140c01030200d400c2c01c0301000401e00ea42c014055612040c9070592801c03440f41e07141c004641c500d07040040403942c2ea00144e50755040c00c00132010310480601d032554000550344a8440401220010303000d0100502e0005421901c3d003440750040e032800508465101d17074441000b030f2789592210b07a0181d120b521410742000249003502849006845548489165440d90030103003c00391034002042c010800501060440c0305441070420b802410720395241c0c400c4c0c07810300c0194820b540c40c4182003c0440d00500040c494405140011174000d8203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 985950116 1250 985948866 985948891
    0x1c05030708161107090603021503060d0f0f050303010e090607020c150c0c0406090501170604120c05166c03030506120303040f032709020406020d08010608 68
    0x82c008003180d150840d07106402040c0150540041c2040032034000c6019a03108440d520b106200420300004030f40411100b80b45c1c40500525000003081d009a46002c140303004d500c50742c1100e6415140c00346103a0081e4480d0900c0000803040280501003030003900c3d0414014805860184030050010710070411100560408020005129210300070400005941501c050028005607079510301034802480d09100d80a482c140700d8540040035100860340300d2180760f02513941c400300d03000d01c1000c50751505245402c1b1003c2c8039454070bd5a6900e1042e140700010700d18001e0b08250103140841001c0d4094040030090a54007800d032101b00e03020f43c9028140e00c0c10b040700d8071061507180801e6000c2141440811031401c0b4103100680001030582c50b400140c42103400381e03484185280780840540d0360344070845015010180d0304058000003482099030103844000704c101d9403901019150001003d420303a6000348000b550016081200c030b60107200c2d4080080395428040002d601d0150050b003004001080241d1010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 985951366 1250 985950116 985950151
    0x306050a060906120c080307030915050906030f2202150906040f0924260313060804050d0915081012240506030a0303050c070f051c05030708 62
    0x1a4960300000040c50801410f01c03809544005028032060b0108040e61501c1510070049448480001252016541035581194480c0b80103050a00c404400c04441d00300076042010098079903884000e103005114400c4082500d090040030303002081380b01c00340e00b170071509614081d00140c2e440350b040c541a5150345440f9913031032669400040c254800c98200c2c0c0362540141a011070400290384c40703845410300c40d40134121348500d9042d0180014145104e40c0b44008064007009680c6161142012401c038141401c403410036411070f030169540762a507000307000082d002c0700400050200400c004c0c0c149140c1d900340100200d0801000405031400751400300e00b440741540204201c0560803010f040144810105510400c800b4540035108004895a0503024410f205080c9611180d81c480c2c14040d40004000b48508140ca03642a405440300a1106000240034060b02e0017203401c02c0480485240728901070401190643c18000b1000c0108410004014042c4104295240c11584454212401c1602d55050f003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 985952616 1250 985951366 985951381
    0xc06290307082410080a0302030408010c0e0d0f0c0321030605041a19090f050105211b01121d0d050a020703030e0d0501110406110a020607020d2f090906040507030605 73
    0x206290780c0031021764070803c82d41c20207060340030001d00b003903408150090150a4100c0400c66412000d804000c1d0b000c8250013500300050710052512200c01d108001c1c00c20950380e6900d070307000403060b50a1503001ca41420102c04a09503810700c2140d014000440301044508001200f0503060a0000499402010b4403611007641c4224002080010000c030b1405014100342d09200740050007007031040340e0091003020840c511040011184020b034000d004c00410411030070049a0340c1140481c08164140b18032040d600d440c140303280c003a034500503010301e0049411800da000d20525042184250008124080c0107090070254041049011290035141410a00e1070800011300c42c204517920042c0f040d0703c1d005122404014180181003200e001d03403581c141500e50002c13016198403407244001c0d80074104202200061400c0e00160851074010100002132201481ca01c2c1d0002e04075885c850302c620340300700040601d032a12901e01303980a46200c0c0903008a042590b0307542c0d51b07000540402400325072030b00b0005990 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 985953866 1250 985952616 985952641
    0x9170307120f0605090610080a0209040b0d050105150616080f0c0312040b0601051e0c1204080601090b0604030b0402010804110a0e041704050108070c062903070824 72
    0x104600e0004206502c000c40d141c2009240c036120703640c052981c00c400038203140fa01c154030300c142c4445904c81054666030044044025030128181c15441642d4019911040d156018001c1c1524840c1c400020345e400d1201d0302403070215003c040c10b403065a041140c242024140c26882c2d04895026034501d8844c0750242551139540103a01e68a0414407010aaa000321125a1110350050303024284040045c0c4a0f0001160035125090841c0b0000106403d010f546807031a800400d040d5580c1c10a0b0b60842d2035003403200742181e0080d0700c0000c4030340c0f10030014003d625045c41060007848007200d045160503d1581c2d4280040b900038400790600903000c1c0003c2c10b0041d180c0c444891241c00501c0c6801c05921200400c00d0580c3c00d540c180c0e0f840c2c1081c8443c902d017200740000c50b015a00141c482d100c1690700c0032030450b040900c12000300d80c85030301c03081e16103002155083c0061320b0700d80c40703600c1c03c0000031008103040c60100594401070301c603070100002c3d00003080744095588044140c6035800c006e90391144020000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 985955116 1250 985953866 985953887
    0x705160f0b0f040606060e03150408070f03111c14031003020604060f08222a0b07060b0904080a0e031c081f08060601030f180303020d06050409170307 66
    0x203000308107020000c061400340c2c0b59610540c0304130b1081000383d88482e021141200c00868050305603120030a60314462100c85a038550062103140861310b4011655110184861010011400b0070202a541101c200c810720034051114048070100305c201240c0c0c03d00400c0b4000c0b42443d40c0ca800c40010119208024642488003e5500a08a43d640340e50701c190041441c804843c034140024004130204070701c1441c010b080c00341d074a00000401c5445060352550880c842240207440c2d01d0301491013000551fa0490403000d002030203140c00303242c0c85030300900308081540c0b265440548110018020000040d4000c000d40d0070301c01d5603140036565100003c01007450040d500c9240009a001c4d0541c5620203035202c4070b0342c1d1290462200c41810100301090703011600304140128100d603040000051000e503c00d07440400f402c4088040465940030f15200049039031502d410560000350006415400d4444034001d0030020b00c6c064608009400f01c0d525010441d011040d045c500350300000000c01e9440b403042c01c0811 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 985956366 1250 985955116 985955123
    0xe0c0a09030308060409050d180902040308033d05011215061404050916090b130e060109030b0f010e010f0f030602071406070305010503120a080402090a06080d0203030910050705160f 80
    0x4801045a2340d000e001c114511418030f80865031080041441c411500954048075803029141d82591642c001031140580e000000320000c00e2000c0442d00340c0340c80d06d425000b820040340041360800381030100044c044060b800510050500307042d460810000d402e002002207030464604400c4101e401081210341d0302c2113500041d40310700c1020a00c0810b04000e604503009906540740c41c000141e848a45003400d0081e41d105680399400c1c03800070400c1370722051036103038809014944030107200d480b42c0d2441130448090300c034070300449007282c018411485440c604a02400c00c01d012a405581350400c00348044110b07020061049801241d000208051190f80e505006403c8081e15154645110010024102481801d02c24400c0c1c3c02e1714004400a2000c84000c8501035440340351a503607540030b00c41183c001403c100c0640d80d40e80e00018104006001c5e40101c807000b640a0b5070f0b41d04000c41c4103490860340c032240c1000341c0e10f480144020950814210346aa20183d00182c9120105007842d040c215045c41015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 985957616 1250 985956366 985956373
    0x203071202071508010905060a080303071214042009060a0b0c0715020d020c182403030f0a08090601080c090406020c06010314011a09010b1617040e0c0a0903030806040905 75
    0x181c2c5444d00050310314140c9a03540b00c10022035071040204207040310700d4412024160020000304003041d110b1901b15120b0710381c1c0304003c030f00c7d148070040d407030389402c0121420746129140c00d8500c281d0f1b00b44000c682400c1802201e049044d42007090000c2c010303d05e6031151244011000501406505043c40004020103c0c1c140140245204a00c0a5150780b00000c00304014002d990243d41d41745070041140c80d85140605864400d0741d0ba080c0c40c0d80940203259a008022001e1025240075a0340400041603020315202c040380d00c40580510107404000041c014020341d0700050f005000d000c10004504c042a04226030781541074540d0b0400600a109282d500a05d40c002c6d03400102c20300c2541c085c4001e41041500081000c141d00d102c003101c05600c850107559102140d0001008000d800300060545201c0c0340c8184404d00d0f2480d512042d40042c0c0c491a60480300001c181085078800f01d44007154800c0e507204041e840c0c41d00f802c100820080701404003c091003607a0003c2107654442e0b41c000c405a6070700c00100d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 985958866 1250 985957616 985957649
    0x30c030607081602120307210c180801050108060f1003060501030f0210050901081602011401030c05100206090a030804060b060d0614040207081903150e25020307120207 74
    0x1090b90b10222008aa40c203803c0c160b9000d07040c400202000c01d055500d402038215110798904070f5250b1210f04001142100702c2d070441c3c0031002244a2943d02c024240c84240b0034100c0d10a0003000e508641c0d0242c40d081e4508001001400c13400b10381160704c072600905543c1c0e070366100d15140d03600241581024000c60702d010000305c100104210b20480040c02241e100c0c240c8146950112400e10a0713029450006650901166030047c41603140b02511106000100320801d0188003651129400d038800d80e010f81c1649001c1015041011800400c0100c0b0300c050300329890304030382c40c640e600c1c0801801410400e40310001020f0000650000c03801e104010161a0340700380c01c03451000601118003884104c034040b1500d4085a20b054402c850f0000d5108424504004002c082d4017080b420010404080c1030303c8042d0002103070071010700c0401030043d510300c4010908220320a007002840303811907074001e4100d240c01c01000e42d4000040c1d07280c0039400b613244120000202000c90810049a0080304c001c4040c820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 985960116 1250 985958866 985958881
    0x18090503040e0a15060c0f0c1a041a040807030f1505281a0d051009050a0b060d080702090714030903041e05103204050f0f03030414030c0306 62
    0x119280250421034040c0f04c03070882030145207864480c0303120300c0000c203400360b1200d800901c0350310075560508d009012880020355941d2800519401c80301c25042c01290000c0c0500401001501040d82041d9803066a82843d05000d09640e6594940c00003802c85001000803004100d003d8a45001c45100c1500c203000d030f0700303100c1814240704c242c110071f90b101f100c4940c2e284103000030b140c82180900007a0b0100c0744000c1c2803007820b010982e50580c605840741c0c010306036802d01d940041d000c0c0501c03c91250700280303500d021904065840500180c00c462044801da170403180814445e506503030721203070102c0d034401031515024070a4a400401950070707520880d000c01009040c48001c0054000c555020b102034105015841140c40e20f0001c90150742e900c110106086401c5910500c1c3c00100a50350380b900d40c003940740690840303040c49840e80b8183c034500d0300010b00780402c1c208003014a100007020398000d100100203000080e2a4021409183d4038400d42c1c840e82e001c40c0da401c000407250490043d003078400d036091112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 985961366 1250 985960116 985960139
    0x1e0503040515040e06030a11010323041a1b07030e01050904051008010e1504060e070e09100c0e0a06080601020a2301180507030201030b13050709080601080a05071809050304 76
    0x30940c24005002800543c5c01e060100342c03000729560010b400703c8418241001507000f440f1600c54854002e0114180140c1001c001443c20b0149010781c401c284e03006090f08051281d4200106000180142c40c11102007010f5002c095801103541824072812100078840100c41e9401017000c450b9000d0b08080a002030302d5440c100d5042074448a00092040301910300d185aa40e100c1900c9420705142000e00040101d03c15610804281c1c840c6010b8814559803903038142e000e1070080e5a02034568002c1881214200041c0c4100414246a401c10b000d00035510000903203000000d01c40c1d07074148101000001e10301da10a01c10345810b158011000d580e180f1303101201c807070402009100d400e100e601c0c0001c4100b02c3c0450032010048144e005000740340300c41c2554011006402510f84541e000b4500c594040e0b10200ca40c0203041c841c18890b90703514442c0749004102803808a041c1d1101c0d0060308075200038000b0070004502304055407490040c2206000c07413521500000c0c181080003620070300001c500402c4601c01039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 985962616 1250 985961366 985961369
    0x150905010f0e0712030e06090a0308030109020a03050f060d03110142240504050d0b04030e01080c040b03091002040b070303060f0b0a08060103151d0f041e050304051504 74
    0xa011100d9180d00c40c1c4038070b03181400f290130243c082200240e40d10f10518000b0300038140c070310002d0259541d080e41c0c0c1e5074075071940c3c000f80c10001a03582c005c114482401c0d0b00d07100e0f4550106428800c81128209000481e00c00b4240410117400c1210000c1c408480c410250814003203044510f80e40d902000761201510520f2095080d045a101c40594019604564500a00045c0d806001c03107594821b0b89000d50550700c0641c00142820f00a0138440040c8980ea01200181e1031030094003066100d10782403800604928001b040241441111010301c100006d50340300343c03010344105d1010555a6215140b1240c5448010920f46801030f00003e070114590303c41001510499100e1344040c01032a869440c00300c000c0c07165000c0c1c030035480001c1c00b55202081c4210012070700400d042c180003c00c504000c0828041404a810010b40e028512606401c070300860170306650300c920845408400c03801d00da980d010072180e0448034104144215106941805014400c0302c3c01840c00502c41c00395003000f800d5500d51908903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 985963866 1250 985962616 985962641
    0x60309030327020405340c021804060e070b0a0c020f03030a030e060901020711040527031e0c0309040b0a0f030c0608010b0c070b0a0504080a0b150109030b04150905010f 74
    0x20030000c20442040c1441e42031209001600b4004801c00c0d10031b0448070038049800302003c1240a038403140140e11032040188036104084000344040c80c0600300b41c801d4403060625803045a1103404100b102c090f10009917001448907103003012019441e40001105440d095000e140c0c1408000340c00361a04c0d425078003080c140e514170000d882142c0d8651480a08034000c0c40320103002a0101039509459142c00d60041e6403101e00070210341924840e0009941c0e184080d4522a04503601c0061441d103620a0310a518509580000c446854010150900c0e6164010a600d072800f80b519800c43c22195079580d280c11002d17040708100f104286a59092480c4a02d03031074440d00c8003180c50340001140580800c0d04481340c01030400001d0020714030b0644080b00342d900c01420502002010304c4040b8a2050a01980b210303d4007440d4641c01905000e550125018500c42240e414032030792200400018442c2032483d136005801c52207560200500340c00402c05040c00030f074024004d5113003002240040c046d50b0b100100f000314 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 985965116 1250 985963866 985963871
    0x3080408150f0702060a23090a050105100506040e0403030b101d062109101a0307090e0a080c01090b040f03020d02060c0405130905030a05040611160603090303270204 73
    0xb01c1c0941d84020900c280c50020050700010300141010340c0b903070008a031958000031381d00b50042c181c0440d980303112000c0d0744807104c9400062a000c148407090044580000315582d525940364030388800504181b10b140f14685603200b0701030020f07041c1070207507015680c1c944000e4812007103162a04401000c04403180580400c007500d03280706030000c1c18010242c40c828401804001d00182080c1000144801c0081407920380740700e03100032070020314000d000d00c07141034611000c110801d42c002020142400c146802000d0040e24241231101c00c0f403000100032110035000300245984006090885015140080c070151210084e8011b00c000c01c00708040c080b031000c3c000d9094448a00300c03840202d88405094800000c02901070100f0b124624024082440c41d4243c26000600c40d90365a9401c0c0c10343d00520074800100d0008038003000901d800412041c0c1018920001c0c140c80c55100c0130070754070021240070b84410142d40700441c4081500a40c00110034a40d001c2610803402c0703050f48441c50003803000703604900490 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 985966366 1250 985965116 985965121
    0x1091a0a05010506030f1f0b0d180c06080a240501030513050c19090c27061706040906051501030c1d0904030210051f050d050a08130308040815 63
    0x49503100751810f0f502c000f44042c1c0756460340c1400c0c0c185e2841c09440700b00d8071400308102d0310602464a5080b0000d00700080b600f070321514035401c114222034074001e500300c1c000030307038121000080e4a0303040c540180c40003800c01130005c0d191a5040e50060018148803150300e044031483e81c03850389400e1111022240240d8042c8102d90300c0041460014071082030040c6950b114200300401c07480c040701ca8521440900e040c107001c00c7c0ea01c0c04014251080c41f14020041182071040c2002840a140301c0351002d06071039030010625140800c020b003c41010700b4408403d8034800049034080e602da8101e01b000e00d4000405000c581449001404601c0755204400e0105e403900c02c170080e010380960000e948042c40581042c482403161018441d0580000300110700714003d42030302c0c5006580900c201d40c0600d42c034540b81c42503002c0032202001502c3c41a004203100e40401c818550000d9400642102c15607401800c86847d020810110b41c002c1d0050f4000401c07041010a000c84c06402c001802c070380c0c40034200e0503800141c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 985967616 1250 985966366 985966381
    0x51c060905062d010e040207060606030c08090d051804020d0608250b07020607020a0305060603102a090911250b0106050715060305030c060c1305040f06030501091a 72
    0xf42001d420b03101c3c40d00e0781c00d04444075245450325031041900d0706044c0400d69040b00310000d42241d000d19003c07241aaaa080306212581d450700c03d10b03142c61184c1c100ba8220b0304060701d8188c0d82e80a03068401040003000580c600020100020310181c407440544255200e000c01ca5045010306201e004c1c64507940b140115031000c201c03900700c8480e81c1c0358000d01000306907401c11590508680c0840c00503604003030204038400058548c800c0351001140030f0300c05002c443c10400101400d009022801c82c040c41d040c2a00254006000d5015400c8000c200c200b148400c9240c0c0c200355a0710130303d03903c100191490030790319035000c800c2c01009140000c18480d1001e80740510082c09040b155002c98081c0c4034140b00c1c0014408a40214024144d8502800c00c035483c00404418013029100c05800886280d0808603210300856420401141c0154215503520300706015908040200e61580c03150a03c0340b0340712a0600c003040c01070780c03202c0041d68200009100032240c604014647d1040046150000755000c030000c1d00b01d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 985968866 1250 985967616 985967629
    0x50c150907050a3807020111032206030c02030315010e0a0e070302040612180f030507120509040506010207030b13080c01110903070b0301050d150e060a0e0d0c0f0f03051c06090506 79
    0x403a41002c0e281041817a030011107d95050000c410300d140300401604140007005204800040414003a00d500305081c03000040c240d40401000005540c001d10a10005100c0040d01c010145800e10b4516241c843ea8000542c030320181d6442000c00481600c24040c5699240d002003096881035107800c038038110b180341c458007160322944070380f10344507000083d00e00000c00c41c1d22540041d50080c5032490900f0401d444503036003074500d00c14010210b44005800342d00c0d03041500034190301c041c0c24009841c40034a551a0700300c0030400103080c400c200b0802c904010820151405440c032480100008004024004400e80c0e43c0768000c00c0510311030b01c0b070a100040e0f080c2811080b2416504050104203840c0701a950f003660007403017802d542c4603090b2145424603011804000d011b118160450020540c00c4010407450300f0000c0c2c400c40c6030304009440c000d00011070064004422032640c0495050314008550400b00c806002d005044405140b2452901c1d820118035044101a41c004c0582006551640c104000d0f4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 985970116 1250 985968866 985968959
    0xb150906071b03080f03221101032c060f010e150112020f0c01050a0501090204030b0117010b031509010c0518040b04180609060b01050c150907050a 65
    0x244aa020451400010200700740402c002080310324403046a41c980d510b1080d5500b11034101da0040030003001304030f00e42e104800e104112200030341441d440ea9090f6215041003510a20509041c1500d803810704a000c08450328007500782c200826002442041c00308048d0300c2d401d0076550340003101200e40020401f0080000800d0003000f20510b4000141900d900565019940419a1130529824850f10251104441c003c00e030b4401b04800016551910490b014100c542c1a0440c0307184901c180007d02c00691145912415a02c60800140040e01061226405008001d030400d0305401246810010851640031007805007482d03500a00201982000440d2140110901c09801c08020015070500d8100703580b004207002c40290011403201c01005604084800503c1d0840e1410707502c0014400344002d5225030f41040c442403030002d00c0c0004a00c50503a54105040b05801c0c600d0b4204c011407000b1004100103c010080584510b90707650741c804403200b100c018060380f08503540d0300301c034101c0c01100301444282 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 985971223 1107 985970116 985970119
    0x504180f1118061f0903060f021312060c0c0c0501050a0c0b150102070b12010b031911030412020703050316050f100c12020306010921021002010b1509 66
    0x80060701100c407410031113401860761100d08aa01207808021690001d102181d16108544440f000744601a1040012008040e0003d4a1642e2700b4803422068000c100c02c00c050349039040280e44040300d051000300000602c000900c40ba41c01840504a180c4071480e01c03468408a56039901c249100580d1280b41550420912195641c3d0400c0040e01800d40c0d5110a4140580307070b101ba180d10712040c040c0101094002c0005000b002c0c7d01026005601c55101c02403214508040b2041e501c0c1d80b0596065483c0001e00500c154081d00003e13500342100d41c8131000b145400c091049040d0103001500c02203595004035500c04400403020001100c0c07030a5103603000103129507231042c040c08001c0d80c2080b20305400e005004000072030f0380096a80c0215901b000342c02810480380c155071040711500d804025405600c0c203410f00e0030f0f00d42c1548000c1c0e40510a9030505a02140c0d081000c4180c0070706040c00c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 985791366 985971223 := by
  have h0 := BRFrame.cov_init 985791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 985791366 ≤ n) (h2 : n < 985971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
