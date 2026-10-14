-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0617
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:45:24.40752+00:00
-- url     : https://prove2.me/submissions/978fd43e-1c64-4202-b4ec-80e97434d846

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 110791366 ≤ n < 110971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 110792616 1250 110791366 110791379
    0x1c060902180f3f070501020601171203040c0e0a0b0a0504020d02070203190201110303010303081506090d2001050f0f0705190c15051c05060d060f02090918030304020402070c170604050601 82
    0xc901340c2c450b1a0040e4401001040100081010b0042041c48442a65400600c4e0b58a031441648140ca013103c00052540b8100400c0c048080700a80080110a05004a07184840040c40e42c000c54000c1910440d400110b002c0b04044650446403142c0c0c0c06015112208200c526038600111060300603404030b404840d60090652010040302d045e242e164071511007a4039000c004013190f40c1500359081d0481000c00c598030256484004030030605218880e6041c04020015200741d41d104002000b5041c03203014071094400509540540d203d19401c0c0000f140c0390921810164509100c3c0002c80114180c15100502842116200c81003a55076111040d00d0401e5010740440301072007480d04605072000c0120040c0413203091600178541000c0010015806203085440300310854951650300b4130566400103100c05a030612900c010f5000000031030003a004000138212607100d10000b072000744215400a003030410000040007803005444030400e04c80402181d8110703079507100300986e01a15a44600c0c000003554 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 110793866 1250 110792616 110792623
    0xd061208072306070c06270c06020a020105070f0201030b060f03010905130b060d02060c03041e0902040b0703050901140703020d14031513060b1c060902180f3f 70
    0xc2d042c0b940b005204540c0c810a080780d010005090441d0800d403942a00040400007000e1a801e00e900e2210081b01d00b5a58588080b0011150b88072806540003400c030a80507030f8110017a900c8940c0c203c644411103060907c0124020100c000c0b03110351005000c210601c040702040c01031410b03a08168010003040d2199861000b401505890060500c5107017000034400d0b04101040ea070f103052028160303d040c0102d0038246c078210303081600881119030001d0303604001020b24000c02401060021021450a070400321030800701c1c82107160207818403100141d030400d541d220340160403501001c4e0074060f4a805540c58000c0d10394030740061510006440420028440440c0c5003217078082d0140e420070141301d105a0b01484a00740c038401000c034505940341c20000b811180f0350010001545d503003140240e001141da002404889858000206461050010a140c106140580c6104400c01c407501c500d4041480001515581c0c00415009800d00004202c41c0c0d41180d0380c0325600d00903441d03000b1a41c21100c140000d64 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 110795116 1250 110793866 110793923
    0x8100605090c070c0506031f0e070504150c0501020a0306081b030d11010f02070605070215040305040b03180a0b070e090c0a0302070507030b07050405040c030c0806060d06120807 78
    0x1031164603803001c26100d1503244010f14800344a0f02c41e0f51599a078840c0003030304982003180e07058802c1d100010890410000d9054000140424401c0c600450400480c02042401280101c0f00c40021005404003594000c1a078002c4180d4404000c0d56203180c0b2501c005d000c0c0520344a4094280706042d5141c0f81440e01c450303101105540a401440080400c040072500700c01500d10b0b41810395070b140c1003103041031018001030a00c41e005071008681da0510f04402841c001854030130080ac080418184000607921500301d8007118400281c01d502c0780c40f114440446500c030100315080901ca0526a207081062130741c4020b1184c0525128004d0300034134201403001c4004201c0c3ea46a8048041100b000094001d0703001c0c05c0701501481c12201300300c3c0c482d5940b02040209454050119601140c01c00c2245482d02901c84001580e1600b4030000050010290540304040c00c030303034400e403404a410240b101251380704170001d104044124003101080e0400c64440d6004000688a4214100d1541140c0400c142c5118 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 110796366 1250 110795116 110795119
    0x2031f02360f060405090c091203030f040605040201050d020a0207060212070b011e050a09060806101508250519080610081302090405010515040b0d031809020a02030408100605 77
    0x1100700202040005210700c2d0304000b40e000000b400040b40b1900d0720400184991621f0003011b0b5a40200e00c10070194070f400807030640c4c55900410402080079007000c40d03da04280d01c100c0100c1e4a403034510040c0d459005966813501c103d4404a46140389550010300f034011107106400b1345403207110404108030f0a100354800904040e603204010016510440e002c10100c0507804c00140d1902e480d071002500251199000038005a1a02070600c403a000c103200540d00607084c0840000041d107020403880051000c12000400d1084100c001a2028090800e0159104144220188940e8802c20140603030704210303c0d007a00017580e800c1412582d4050300780f06016a80c010801d46203030440181c1200c5015005202e40c1040c600c031403940e00180c4440d0405030113280305600110301c0e450310302c401414050000140c50311a5091141c0d00142d5241d0034141c15800d900b503d046c0c2410180c1c5048010307582c40ca54460460180b0010b007000080303601001500503155103200391245407140d10068819502c4901405 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 110797616 1250 110796366 110796457
    0x105030d14030c130816091a0409050a0506180606060301030305041502030c030d020a080f06151305030a08190503060306010b0a0e0901030b090106120510020702031f02 74
    0x781c0400800501859200403607503601e83c81c0020384420309106521382d0344070194560040c02540e480140080c94038001d400f010804010301114000d0f0b10809040c00c010240c003039692031500005000b814030040410700d4200049900c0b03800d124034810984104072058100ca4040c65011480c1444c01c0701c2100d049070781541d1407900742410a41d80d5040d10b0b01c00e401810661100700701c460403904050015100d080024100103880e5410707924043c0c840c0200502022102c0b09500800240351f98011007411900ba041c02060f844840d001c1c0b00d86110744854000507414030a5000c0102017140000040080c00c411011101d0030310f11450050f10710f400b0960300c0503850b40001005010b4285000e024200d038800c5451704048824050002c21151882a0802d45025041c00304012134040c090007500003e0070041c00b46006a201900c0c2d9a0300d524211100d400350b40c1e00001d80c0d13404d41d5000c120a018894410320166682d44034400039000962050301c0c13001c00040700da40130202c045414070840d007802c100c91250 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 110798866 1250 110797616 110797637
    0x10608010920031c05040e06040b1003050612030409050402030d230306010909020d0c020d0f080c0903070b030f070e01090509040f060f0e03070501060509010317030a061205150105030d 81
    0x70350700082c82d510742960903208030014620041c3c42e426071400f0101c0315455a6a9175030408102002801008000600880c1480031405054680803020034201c40c2510380001c1c1500c562002811021401c0515075040c403010a0125220072194003050085100310b00b11503c14a0801007074a2100344001031030300031040c0c00b41400c00d4030410001990301100500d001280035403102c4a0000b281c2200d00c1d466405540c420071b0004d0385404000c441802d50b200d0400410200705100c001786811401018425200d4010610000e261410020700029101c92800c82c1c2c0c0300c2c0b901161b1803071020412038415000032141400d0303140c294040d144000135a80040d299044968650716a400ca49280c40380c00c82e03080e82d8940061918070360314032480e0600070a86025541c0d410041c00c105080d41c6064200c80d00c506440001000001d100b4080a10200740b840805d41d100d1f40c3d070200040040c200b681c485041440c6024030390b0704119010801007107074011010500b0203640c854041c03559500303540b01450046200c1852 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 110800116 1250 110798866 110798903
    0xb060406120f060e10051212071403160c0b03040f1e05010e070f080d21060b1209011514120c0310020a08090a0f020105160c080303090106080109 64
    0x2105403a84105000403604095810408007240c3c00e40d8028038840c166502070109004825800f6030042c40304a400c021010310021800d919103412002840841300001030240400103800046030a92032004103072500c8400c01c001c4e41d035000d07a002e107003103440c0340c511071000c2000c02203407040e03a000b19003001c0403600410660751030104100c0319018140c601038030101d10400041e424026802011a600050302c105807030020b01c02001440c03600080d510380c1203560981030701a0300c030f400048241c00c1c40042c900154021081407004001170b401c0700710301c3c4600003101c402d05403002060038003604404000f017141c2044240e04000300359290080107110b89202c1c10680c120b2400d82c000403880d00255080d20811150b0100103440e007038a0f001c0029204d500410035032113440d040f44056510081d1000a019841c503266900e00c413110b21000000e0600c0008a86ea0303040541c4c400078200b44540c0501002038103a207031044940c0ea41c1007107600d140790398200030f4041014034040c007400f08059800742040d56105040704 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 110801366 1250 110800116 110800127
    0x19031407030e040603030905010f080912090a030506101a09280e0a05040620030708270709050c04050a030807030302071502090103050714030a050603030c0703060b090105040b060406 80
    0x120240d04004a800c1042c150740c0d00c91089500840c030030781701c406c0350314544400549000300d000c290344240070400040018004000c540d00585800d0700c00d026a41e1440c2c80005100d1410a80011700507100d094100310002225039800c10540d0085858240002903815100015104110405d90030010070407a040c005400ca5400103803040e0044100c46100d031b207652a91564541c1180c00c400c0154650050105105961240c81400c15150b03454403000c207085016021140300140c412810010700c100010148544219003082601c4417000015001c9054602140c1d284c80c0ba02409649500e4040414401045001100e04441028151025040c6540c0701c9414a4000b1030064051580801c8840006090308a41121001d9141c000680780c13110080010b04035a801040c500c1442002044c0a09291900054a038002000d201c0400c0c16504c01e800305c0e04500440042e044188107902d1301204000d5560000501c20070185c415020320307aa0f5100300400d0380d03c8540d100b5007001c002c1000b407141c1445403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 110802616 1250 110801366 110801377
    0x60907050a083c0c09011d061b06042a050607060207080403030c0c0b0313080304020409080c03041a03010b070f03171806060f0a050d0f02060a030b03190314 69
    0x144200d80218000902100ca094180c402c496036144140707841d243d20841980409811280f0708000c1814039203d14006030805c084604a4074074000c581306003d1403550b1319011241b0403a898072030740086c0c00c83c40d1191903450400f0b40b001c80b07104800e07614010030b08100c910355851103440108540300b00352410f0148005503004000907035a0a808000c10400305004000030002180310303035144088403c2d0f41c10091071001c0daa400148095004005102c110103000340964031080d00600302c540d81c1d4a03144001070051041c0000282102d00c0403800c14441440032000d04102c42c40303030b4015082c0786d904d041070805d5803000740551a0b17104014072024022420940c1203101c03051103810300702d42440001c4865480701c2012140102001d510610210300142d040c08034541000c001c3ea10700044281802c001015030840307000700d03030065500c1100031041c0270082046040840c0c001d80701d41d81c0ea8640c010014098a800e140380c84c0032303205115200e00d50058101c0d560f10301d1601585d648103007500a40030700480f584907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 110803866 1250 110802616 110802631
    0x2010b03120c011409070312050a0f080903070605040b16081902030403230403020a050910030b06010c02090901062108030c0f0912060601090f030b0f130b0901060509060907050a08 79
    0x2900040000c40f0704c400c030850701444c2c0e880000d00082e071443c549400d1080280c02080c040100601801203162f4100d0341604000c146820181c4855a80d40c0d0405d28500071280c014080034181010b00051100001c58035005d5106581900d0107491600015205520180da0800518a003404141c5200c0c1e40c2d50b015541041c4289402400c0550128002d07030400030705409500740340d80001d01007003189058a42c45000740000e1702d810405140843c0c1c80140c003d09480080d202c0ba4600700005c40c01ea10864444986960040c9521158204001c0140c02410031703003d00c0c0d815458081c0201e544841c0ca80700780c510140e01251045c0307113aa170a101d41d50320713400202c820b0f2940c507420302074049660344101da41e07401d54440000800e80351511600041c0101c07565400f4029030f00b101c44043c0046030f2403101f4154802c85101c99008242c94184802002c0100a400a08029296030034032041030019080002180e1301114410710a0701c0d10410000380c0303581036500101203041080810001400b610240c3d038810350 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 110805116 1250 110803866 110803871
    0x210051003050f07050a09110a0309051204030309031106070f0f0606030b1e0c090604030f0f060204080d030e1203010905060f210f0a0c0501180b070c0305060702010b03120c01 77
    0x58942c2e8661611030b50080400f92034020081c14801350038071700310a0004040d400c405001810300411021910311661040004050312102e00400380002008004d9040a120715140e5443d5540c3c2070060030410a400204d54603a00244100c3e01e40c900038040d80c42494214048800122640c0d8500c002c07800d940104444558a079032001012401e0040c040c0c0c42588401410b202e04003070110300c4010402c00800e21602904280f00c1c4028030f40300c10b8140c170292a40540540c503d418642400e00402d1080c2c400203104500002d0040317070408000c0b4100503080c11301e443c01d0044107900981c031170b180c00380e04039000e14466050004120220380c43c0c0009812107070103407400508081c6000032a2010012042c606004a00302400040241e801c0003120b00c0f20300b0803005028601c44558401c01b542c3c655106480c1001500707001010084040708810380201030200c41c00d6500c0720517281c003241c080440c0c40240e0b140d000c0c030000145454010b02440081070401809002d4810308006410130503009480055015076 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 110806366 1250 110805116 110805119
    0x411062101031a13050d050d0204050402070302030405120c010519030e010c030203060a06210c050d021201030204050711060402130207020406031b060f080f131a1801060602100510 79
    0x14000d0008502039801085509240c03021100403202c41c01c4007811444403805200000c40204074040350782c002041c600c1c64416914001f50b001da00203070149410042e8021b1002950004041d00000248110368064800d468191000c220140e11040041400c0703000c94010041c55542040c1481008200f99060030001056003200e1a11801c403a108900710700400e034000b041c0502c5103424440400203003081c0c60010400203020700e050b0706c01800403000a0a66403952011306140c4d00410980d041c1c0309807044210b460f21180d041003c3c02c03e01c20320080c1d001c1c41c500004103031221710401110049480c0f0b030f0000d04480e00c690342403080303560b03a100c40200b25a90030b100300d500507602d500a0074003c5001c0e01071000802d21000047c00011304075401f503001e02c08442030f00f0014541000c4a1540302601da400031610741d46031742500c00e51000c2c03018001c11030b202c0e0b8007000038011050390f800d60050031840500001c504030004111300b00c8a450013043d02581c04110001504119a0001c50f070080203c0034458103507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 110807616 1250 110806366 110806417
    0xc1203120118090b0a0f0f0209060f070507080604211d1927050f060d110102030f070302010203070809070f0b030606070605040302030d1b09060e01021f0603020f0306041106 76
    0x2070209482440309180c903142c0c070200c00d00c00c60087c4031140c1e800c54030841ca8100c09500003600c0344200440c10800201c04148001800f80c04c3c8120b2006010040a84259141501c4d0078800042040040e0b0000c0c000320f448211290722440c00c1d2001003541075490500c0690100070014518180c400100c020074001c0400318036110b0541107260345400c1e0307d0f2003c0d440761607400c41000799140103002c1124994401c04110071696031a140b914200d410110810342c9500800040b0700b144100c0380c48002184000440400b0980e05600642c850041c030351781c41342241c403080451521307200103201d5500f8030801d11009000c0490a03200850308040010b103184e15200c040ea80d0303202030340d104841c150050f170000705032a592940f47d8000c4040403d10940e40c2149902e0041f03010b001140603025650070403c016214900302e174020032150229440d848420b0010050b401201c0000e812030b07010803400f840903154140a50308000a04500459001c03518413038140080f010702c442d035003102d5501c900c00890020800d844 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 110808866 1250 110807616 110807633
    0x50a080102090f030606150a03060e040b06042d0c0302070f0b07120b1509030a020307091d07031e0c090216230c041a120c120312011809 60
    0x204105800561076180d40d00412007514105207003980640c000008210241da0b41e81e4035811244402200584c42d22813402040b00141481e07040301c080d0b61044c5003800b0900c82c90420b500e1140c1412142031040c83e2000c9456203658800384506244000500040c155a960f0781e0440c0070310020b07510b001414244962215481e2000c8072038191141048a400c0c451070300d83c4030440492110700010f00f40150b201c150302007180120003401c3d004480b07002040305949642c3c1446040b03411a001000c0780c12503921000000010070a047c0c107001d01144120610785103070b0010541c0310442e41c12451b610210700006c98070149000b16500110b400165000010075190340034809030642031540303d00350f20980c01902d0030721480c00544107502d02c202d44141f05515080070020f104100c0c507105440202e00804c0d00700001503040c022000059011440103162980d001c0002021900710004503003000a050b1910301958a9205540000648031040380040c081918101c1c0c1141852441c0c045c000b91001007901e03440030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 110810116 1250 110808866 110808869
    0x10e0123030703060b0301080c0f0127080c0f0901091104120b090d0507050a150e030d050910092d0c0b07020406050f0a03030c0f02090108031b060f1f050a 68
    0xc0d00004014464402c0d414810500a004208003192655042c0391510ba520b50103040041c0c031a0840c0071164620341d01c110302e1070a1f00c00c0782a100c41c09113000d40408401d80c5889000303190007403144000d0503101e4138010b58409903046003d002c1c205241d003420200c00240c000c0000c0103450325010800083c4003802004d00120395401407201d11190f040c001045414000400300346410403400b801064081800818001802c0f58003051100703006807004100c0c4090304000c003071070115020104d900003045060b03400952180151101f0384116a81910100084401c0840003400700107000d110340e01c2d40344c1e1181c4e02120070034140c01140d240c1662035a407081481c490782c02c841e10410020444100310700305401031201401c8101c1c1c914164000a0000c50360f0546544800307020029040b0021080c00840e10f004806580c010b403100c10590385444240e5a6a801002d080c05c01c9880741c41c001401da200402c9d158080e0b103d00c1806112621582100e22441c0b030840030192030080f036007400007029070300e1462410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 110811366 1250 110810116 110810177
    0x1e13021002100c020a0b07050a110f0c040b09010b03160311030a0e100504031d06040305030403030c0213090c060302031e040b07020d021b0d17030a0906050123010e01 73
    0x12801091200c6403ea070740d280286403e40d407180a0f504001400c030380d46240e1288151401a840e00e000f841300b100e07010748952a4540038010848620214403005c550000009415a0280514101c0c401400b01900c801d1041c2c070b1a81c241840400e00c1b91103441c400c0c038444c006030728000c1040c01d491611a84a94005d0340c8541412740d1795601004080d2080c070008844489221040002e80303841e4401502e4030368030201856505000f810108a00d550b4030050360701640d004022241c0700c03526403070050300c070b84132810041e07208280d51084c03085510b00c5405001c04641c0d10404079030215203420000d40c080c0d003000c4c05c0d6007141c4071409400d40106250501035482035000d03603180d424604107045d004e070400d0669a102002c54008442400154200d035040c017410340e0381900c00c3c84400029080103410304941011545800740000706000900c14a50001e43e2054098081004940d91f00c0840b445d600301d040401843c80c0c501c0000080041d8003613081280150b00c10f0400000141b1090404ca00b040141c41d51103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 110812616 1250 110811366 110811373
    0x927060105100e0306060909150a050703061e0506030c0c0604050606011103040f0b0a11030406050903120a021f0608010609020d05060a120f03050f0a120507081e13021002 75
    0x401991802c0c0388141e05002c0030781815800340319404007091325200014000c501503500c2da400308081150410040d00084c11445136101281003c8000700301400d010303505400000c3c01c100c004a00001a650b240f5990039000840d240100e01e001c3c01e22030301d41c1000381142c2d484003050100c4001c0e10020b001c81449580f1610140510b03290100014041c900210841c02c025802031200303010511440381c1403001e50700c0b43c0da40a610b41056260441d010040c203a55450301c0d0002007400920790f0303000700180c00f044000720191040c003000c0b01d01d454001d000e4400e00710011b074858012180340703a8920003c1e03443c0302c01407140420226241c6000c0c2d825510750381d00c050341e000d6002952076001721136031103032581045046811514191138225207041c080c40c01c800140c80701411488100826006000315082000c40c0c00c00c284c0c440100071000740c100080300e04109145404d09000810091141d02078921405805c1d19070040042035900b42008500d0080005004000055030080580d580010170f540c501801d41c000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 110813866 1250 110812616 110812619
    0x8270109061419020304080c030406080405060a020711091005040e031b01050f010b13030b070509040c0f080a021e03010b030910060503030706091e03050309010b0105160209270601 79
    0x381c044070140884204000240c4062083c00c0c0c00300c141a43c0301c200c21100142c1c594890341080f82540c89141c8100e40c9511001800080258000f140c0910680c007640035038215503506a41075042c5e00c201078000307140900444480100e40b4003402c440784c01c600e01e40c5c0b2800c1c0e1b103512000400d0444101460540f1607500c085022001e01c410b99030448401c248010082c0943d00300000c500d0414007047c092100980008548215420180058940155006500c00a46040410014000c0e9100007080f600a40c1000385807040c01e40951781450060b140d07070b5a0f46a91b0f9507569255802508508650558085118404039440620314003440c064002c0b06880d40da6030a0000e815403500c180120f00034511410710f031003080310360307000700659860540108001c00c542da0315140007005141ea00601400c48010400c005040c10b0b4480065071103400d070000200504a18140150f40c580550011001d114208009540050409090ba80c1c1c03c103d803851003403036080c20101d0030341c0281c5120845d110b055104100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 110815116 1250 110813866 110813873
    0x60f06080d03091e0213020a08010905181506040e06150a0e070504030b0606090d140c030c030717070b04170c0a06050912210d1d0d08270109 62
    0x101e000742042070300703007041015080d550300402004801c08441c50aa001c001070015511048406011202c54510465407140707040b00241550300c4c02c2c01403252082c6030000250780c410f05455014030700701000d00101003404440101c41e00054004140507001a22500d01f2103800c2000c2140601070640c107440e42035140b184c001404804102c0e540701b58566040c60045c8200385820101701c509a9421104400b41f55485c040070030354600c112000143c0142d40ca000b240306001402100242c04003c179019102c034401d00c0d00c1050303030b9040070040303507907042d08261130400c46848003a9403000120800d20aa40380316503035034002e0308039403c0342e8040c03a09a070703a440b403611168805101c190464078007120100407581c00c000004000b8020860643e0003941028920a20240704012210502003124643c10001c10b1180c02c0e9107040e000040c02d0b100190510010011001800030b1001242d080c42008000b02c07808200111281480900710f8a4401c1c220001c2c3d2404816440300100125211030012408801e10318 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 110816366 1250 110815116 110815123
    0xf0c03040b0a0b0a090504050c06040f0605030a02090d0305130b03060627040e030304030f0203120604020d0605030118062313030e030d09150e01050f0f09090901060e0906090606100c060f0608 84
    0x81c6a0ad100304003c21084c040540c40400c0c0303c05580d580d1402075260341e640e5054000034412141c500d40d00070910a1080c040551200040c15944540001021502d50b1760f42000c649010a40751198008418440d40d070b540300d03040e1001005030521305412000068984042001c444403181240034070340001003000241500501880c0780428284011031600d440310440d40c50503100504241d10450700000c0114036010180c1005002c0e1000a008201a0340300c40480201d511640f02c04071011404c1c034400e00361100004c4010703407030b00c540020340308610380c0d904805007030303000e05280c00f00c0074014100d048280c2d5490410001c44d60600e162660110f05040201d00060864049410410080714a08c1401c40c1c4e60720400381ca0003660344601c06c80e00c07025610503a220714003c041055402040100821030400341c1500440102c50414460304001d44031303180040e498260448004075540c0c080404585175091894405140142034074041d0304d07402c00360351070009640c0214858410700d031b181d90003404080f00a2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 110817616 1250 110816366 110816383
    0x30405100503010302030606121e031c0b0f041503051002090f040c0c06050903040503010509070e0907030b0114210106060212070201081504020408070905040b0f0c03040b0a0b0a09050405 82
    0x3070034828155072550380002e0307070303040e0080c9141d01880c4040b51032025124104403000c5801d900c403016a58519104080550380d401408241170305000420004c82d11944503c18140010780160080394054001070a1001a000c2c2c42d081403000d401d414800400325005008004104901e80f10141e5606055030030004100750040c0418810391900b8a9030708041d421104c41c00345c103a4031403000326069444031015401c6020300d40c04240c140d4289810085410781c0420700e40164dd000d003401d00c402c0d480710054150358080f18080100a4151361005105204078120b0028110400030901800f0b402d00c0c40b009415111064043c0710103a459080502240da018801411107940b0541c0281c2002c4844e00020a51400906603000310007076080300c0c01071070322550100c6015007a50f43c100c0303006d1f6648201181c01030500302e07402d585400421f0082046410784400050040c00c0004996040d0b8565465100c61440c2c090303c403d600954034a141ea5013511000780400c0140b071181c9c80003901e440c4c5820054102502d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 110818866 1250 110817616 110817649
    0x20a050d08070303110f0702010c1b120b0106030501260127020907030b06070221030f13050102030a050a0f17090a1406131b0503120c010c0306060e0105090103060e09030405 76
    0x910186d019004504180e65507240c0902c0d02c403540c02c0290070007076802d008102107002c1c80600e4030004134640300e10001e044ac03078601c211081c520580e660348044080318802c0c00354000000050a4a200014001c00d41444c180a410000541c8106440c814429410345145840b01c11140c102c0c2c10041d441d0400702541d00c404281800c0c4003046202d4005000d40c441e656009209006422101c181d0004072040b10314103c00f600d08680d0394084888000c4c0781504003041407c03d0340c0a185010401d94800701c15500020010388440e0b050030741004040ea4154100d0340e2420402101e0000c0b408820b0032080c20b540070381d00d880c02401401e4081c2c14107504200064103544590350040e0300744001202080ca1010314a500072880b0669041c03076000aa124105550006a25200300c0e10013029802c1c5140007411540d020000820503104a00400d0307080c2c8149124140200300011480e400319400b600041801c00070525000440399201c060441c114841030f00e41440720340c0045010310140c11720078140d40b46600e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 110820116 1250 110818866 110818901
    0x1080c1314130614060c0c0901030b0405160302010203090103110d09141209060301050d050f010207150b03060405060109150f0b03091e0309211c0e121504020a050d08070303 76
    0x80c070303038181d0741100d9010099001702c000082170a29044180310006142c03800404000e85541c2d203049c491000c3c40203881c26100c42c042d2403281c6c12082d00e8105c108044035810f030059410005060700550080c00b6504050581740420000c0c08040702c86071244201d1244282d070814200455002e54901d03103199004d001210043c1000100c0c401d60300c0c2010303a4111081203c0080390361059242560829904040d120113541c0046510001c02950303c013491080c00c181d09040203002c1201c0109a40c48509441c040d003290040e000500208030281c010091030b0b02e05484003141256154081d542800045d4407683d5031b800040709100c20400180182c0001c84910341e900c403903d002c02269a03880c3d1087c4044944120358920010700344101006407926403c00600c2134540b540c06008440a1060790154520f000541030b0325800741e10b245c41a294000500034400407d1100140400100c403041c01810980c3c0c0010541c2d0000781540c0c510008940c030522486000c0c0d11100e00d0700e0058250b40c030340c070344450f078010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 110821366 1250 110820116 110820119
    0x702040c11010609020424020102040f0f03020312030103030804032d050711030a120e240307030b030f0c01031503060504080c1002040b0f0d0f021603021006030c0501080c13141306 79
    0x70503002840390032100b480b14547c8070700d94044182d00910440d8003c6400c0b5044640000301022480c1c00902203038000e030142c4000100400b000c0156210902004001c00c4440010401080c420b10b4080a8200c048420708200c041e40a5a52242030080000c0000034000044039001c00203003100420510b18141d0040250703060a075154994103060000c0d2a040102c1980088015941c200309252888200003503034022105107218032035590710884150340442e092000f059414280020943c1680c801c1401a18007074107441c1c01180940a00312030302d00380b02044003021010540611030a230103103100e000c8050380d9081039509541044250140b01c001e41c3d04c180410000300301e1a40c1195640703c210300c01980daa6100c0712480008120710b40101d00450300c0810640400c60101e80004010b038025000c0760180401407122400752410703408010604004008108180d501450300741c0d41100b4080302c000c0c00d00100c40c0840c030300e002e0a039119040c0d540c0c0780203140c1880d08124041c08900440300100b440b805 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 110822616 1250 110821366 110821379
    0x1309060317030c0d020414040e0c06030610020a05030c060108160305030301210609051b0603010b040302010f0c0615030b181c03060308040e061206040b04170702040c110106090204 79
    0x1400c000016074182980003000903c000f241504480c804442000215240c40d07e1380402d142c0300c1d00e500780e0f850282c0d180054424035020001400c480c4180014042c2d8656a2041c081c0045802e0955001c1c056205404c40c000001d00107201a0000e4581007008000715850400410700c0c15220064211180d05100428000f081d4044101e80c10341d0200420350900318141c808001c0700d00000400035000c540340001c8901089008104040c403d00d0080c909804000d00408000c01c40c8002c0c40b1388800d4031030801c01080107500a5100120700042410049407000f0181c0391142580c0103981040b0307042d4031390003090003005050900320707800c46c1c0700068407141403000420f00e0350340d65050181a42a54034808403105054440c0c2c01001c0510390054030180c50715074811000308844401c0d00d100344114a440d040b90900400022590311650300b020924500782c42d685c42d020000d001c8101180c120308820044200941c545001d4010081025500c191031002c100b4001400c444045d080f800700726004000c02c1101703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 110823866 1250 110822616 110822633
    0x60604031713030803100609171e01090804090f0c0e01020d180506070b010905150603150d08031306050601091202090a090606060c0c080703031407060603050105010b13090603 77
    0x9000c0641d96103550b0b03070868074030700007440300e40d51004052040010070010610400c00307084048842d26122005100d03166007484c1070941c101100700328950700c8120b1080c40d110405003182d407800c103004c000003140c3c0c525450b0501c103076006421074402c02e80c4415452140315141e00c1504440142d0b40342001500f80707180d0000f5111201800e00e6810083d00a8901c800042e610000100910009210700d90b40c124614019154a10920801c003d1516007070000e800303041803070054440e8500060101d0315560300c200044c8400d4105d86511038105071059003540008070144015406640f40724810800d0f41090701d0440240e5100814241c100414010104806141d904c282c1d0260703035040300c10081a540341e00c885402054500d5010b403480d410410005056070304008413002180c02040c0e03100d84c0075143e040c02a66203485100040005200400c20015159484c001c0c2031501c1c4909004941107a0b25240c803070a4420a07000350360080000983c14201c240400c506800a21151740e0a004141c40c6441d548607 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 110825116 1250 110823866 110823893
    0x3130c141f0e03030d0b010201050903043c0e01150c050706030207030e19050112060308090607050c0a0e0720060105010e0a090908030714030f01170703020a12020906060403 76
    0x26060141050284060042e084185a100094220707030b2100346480c0303c017015201c6042507901651810010911041003c01101c0680700d0042c65107081d1400318581e10340349140301d188000303040302000d107110022601541c02c900034000c016070f8221550404200b00c2880b0a21603100c828030400c41500350000d500800e001003160f9142c24010307124809418152045682c15003507952040d228414036014040e4140d0b40c2040d10001c0e80c8003140c03220301c02010001c4805901003d030079401e044c0300d0b25429207002c00051103482d10860643d10b1803038183e0041000003120350880b1140c0c40404040024495101c0810140c2403080c01c8202040c0640d00055130b100c0006004042c10403030002c083d074074a0b80b520714102004001c104010001d0b0b182c18103000c0c6403034100303a504800052200c606000035940d08000c0c2c0740542516000c1e400c1ca07910705100c801d00da0314001050a883e000321800007000d83d80c0d400300f8034020021001c072008906810b104001200600401061051500740014404503c05e00c05510 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 110826366 1250 110825116 110825149
    0x14061f0201090206030c040602010c020f0a0b130b040c090c0311070807030903050d0507060c090518040311030a02030705010609020c0a0f020a05060406030c02070e0105030a0602030a020f03130c14 86
    0x45002542804a0152502e4580690012000170031700c400c800b80c4100810849126074001c0100040c0504200d84410301c0440903c140d50103405e41d50041811400181d0b0040072003008840303400c0c01590740f540c48900440b400d40700035403980340c10005c0c032006018104003000d45150400011103407511141ca076000300d4002401000003c552007003050300860601c405150400103d4500c4111490300030415848960300b11131041c2002074190105014000c2842a540c0050003504c9544610b0b0f50308100b800d00a205a081001104d0844d4003903405100400a402c8954095aa10b844604009080d204e031540189083c0b4810002c920f5100008200004800d600c41344400d031031a11400000d181031103e80240b94040310000e00092200c0e050360245d80300e2002a02034440381c0742c0e01e040021b61030030b0134440c0300d4044d041040c00e140022030b658020740d844456514010b0500078400580360150300111021120500505112018031507200355090090035181000c0c0401004140032030a034042489588 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 110827616 1250 110826366 110826409
    0x80f0d0e0a0528060b040906090f110103021c180b0a06080609060f0601050d0603020301020a031e050103051b0301061a030601080a05070516020d1205090a0b1819030b0a0903031406 79
    0x110790941c3c9a81021f401a43c0111007400140d0342402c00c0b0307200c0f400603007045490006641e541c0032294041d000b61000801d0384800f51910075103141c1000003908000030f100b0440c090700c051900018161038071440c094582544005051030a005000346807400141204480764000010044d00020b034404181e480442072901580781c20000203e1009855982c0000f5410750001c1a01c8140c1d55043e407000e01c0d00c110800001e28030740a4100c18a04070f541c280405000d64001c03004e003051111210b0820f42e981200640001131040d0f83d0300030048141d42110080c0a0740344000144001d9603484a065070300407550b18400c000c14144031402510743c1c032501c0110302d00225004003078001d55480400c0030b440150820004100c04e084807000030910340c00646041e04c40d0101c40e102280e980310940540700041091201e5101e002d88241c1040704030300140d0880700b038126000d2004400104038480240c0648106103001c500d10354185409030940c0c1440744001c07d03224008042140c0340d6950415030002d00e044400c0c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 110828866 1250 110827616 110827631
    0x60b18060f0403030e060417060f070f020607030b130906050906071b0b072c041a030601210507030503070201020c0d03050901080907051e0a0602060705030103080f0d0e0a052806 78
    0x1b00c2c5003070041e640f08000184121210000f51800800d1061107040c103c12007000c16a10300c00140c401000e450344500040e8484c40005030001c0c000c1d440900ca541000b02002e4030154a161904181c80ca0310741c08840d21600d030410301042c030700100315894001b899814034002922441180c1a084031a44501801a54580d8086805140155007400c00440450403141002590300105001c0d080da20208a00a80c50002c222420194100300c180c3d0b0914018041c100b56482c240690400040480d0100000d0740444003c1d030002d81e041140300000d6206901843e220701c441d000181c185030424a445000f541c80304001d000103a403280455175501c1c82420041807a480d03548030b661401180d50403080d000350880c1c1444181d41c000381c0c050030030240211000119640c880d20100d844242c00c0d201c0d0004100184018000502e1080140c440e8890b00c0c1c00850900b20121900c10588605a40140140c1c02010609050080c28007140d05103070200481003004202c03d14500241d500c0c000005055155108103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 110830116 1250 110828866 110828869
    0x210209060706050103050d09060f02100e07090e0d031802011709010e060108070f0b0906040b0c0a05070f140f030613020d0227070c020607060c050706060b18060f0403030e 75
    0x19181d1a5030410300c20000c0d50b8480c41c0c0550b1f211300340034209010660154001888901c240845d8141c00e000d6405000140001503048010f807007100b0703281e8805e0040740800b04450000f4400c01b0128410750000f003000c4010190050211500d1030780f03009041d401110b0f42009170341c011000c41661f62a007100140d09641d5030f800305004000300e10181003103000300703400080c494100245120075681c0140444510031303a00c60a04545102d5000800e41103035090001700100d104150181a00c0b44c0c1200a440d00c8603003507035509082c100140c0200b8210300c2e150805210f280500c0c90003964040003514a09056024600000c0d81d440d401012201ca41181106600c210340340c9450308621150301508508210b0302c1c0fa40001407462090704101c0d8103c1004001440840c0720342c0412082d02d80107890b0078a807110940300d40000d000e0650343e0800b4000104252400210107103c1c0b10000c00b82144056124203010b00c00c840d503070703280c015a02e101d0301062102c907521030140760031242125818200360f50300d14148070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 110831366 1250 110830116 110830129
    0xa0e030403081b061501030b011d1c08040e0118090515090304030804080105062704020d060b0d05010b04060605040303090e130206030f0a150e270304030501020c0d210209 75
    0x201d4540b00f9004400511040404140140503680c030262010b01603121510011690059400c2d00a085480aa44070711034504180b928603400f1b4090081c4105401881c2c0c540e42050707800b17039100240d804201c0b070040201c1e05000402c1030349428003180c10f210440342a220749903550005100d01400031032050224820a1007041100c004650005170540c9440c0e407204494001c1c1412642c090049061441c40c0c441c58010b41d0b034000051851803010f01d2548c50b01d400b40803c60889a000302c844540d201d220402c51f1b070311181424425840380d030021503a03c03c0c003030902042e54540d40c00134041c06010310050002076000102e0409940b1720044042d8196140e01f030300d01d600c006800003c0d4105200100740445013000050303d41c0308dc410444180818800e030080c405840c0454030940908600c202d01180040040648203c03503041c4100c00b08a190400300c2081e420350b40a070380203e803103a50015070300c12003207024050910404010300701000c0c04000b03034110503030034180c515030f000c05c1e1075000606a0580d0303180c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 110832616 1250 110831366 110831407
    0xc03031b270411040806070f0201090f150606030e070605070819080f010f0302010c320109031404030302070302010804060207060906090201030b0d080901030b130f060e0a0e03040308 80
    0x1040c00c50010616500c1007580021051410740214280a01c40504104601c101c60440b11710400030012030b5100041125a02d0184c1c098030300f155294464000400c1c0d5221120342c03101d00501c0d502107000d04040c0908101e030180e50189041c1030824201602e020070100d03001c000c592103800c0c1103596041c0c62070500120322803231b80810350360110305d40661400c96000e010b02c0c1c4607440741c02c29950642d80b90a83c90110f0240751000a000840c020040720008401d1071030b084190400c40c100054a4190800c0072a5808019216540c13582d50340183c041410380c440c035408541e101e2000741030328207821520000e4843c2d18902001c1e06000b81c42c80441d040042c10360445031000d407c000c040150042524107040541060203081e80001d08003034030402c072803400911f10784003158011151458840303180015800b8241c00b294581c0d000c802a41e024510030f0b100d000d2110507108060002844500384a0860541d0343c1c0a0004d910b000e152644240d00c0d550000229400d0365000344245441d00f4045951103a1442c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 110833866 1250 110832616 110832637
    0x5070204090503030a091a040b010308090414150a0f0302030705040207051903051801020303070804063c15032d02040f14010506090d020f12060405070810020c03031b 73
    0x30054103901c030380e00071521144143e031040e290b15844000c5d01d01484061703c01401a1027171400410001c0c60351350041030180c00c00740c030100302103e41000c04108080c044450800764646110540039900c0c1003210080504a40d048921a05045030003290fa40d090340c1c000c8501641c3e00080d90024042c080003e0100220b202c09603560822013403400602c50381103001c1203120381d0000c1c0c0003000c580d80044280c0b07110303003640e984a83c8540d40f20744820010b0080b44d40c0124001c2c40407500444907000900342074103012aa201440e684000c042d101500701d640720902c42ca000c0d0b05000080c00024810680e1001c0803903880c40102c4401c00d9285104000c43c4447d100a40c0986031407858000602650004192901c0110080140303030380c0c0702d090181c00e109000a9650011043c440c0e440145055000d508141d1005001c003011038018403800d51919400796420389e00c0b82d03c418401c016a020400c480c0c0c04e81d400e950b0080d8248051011815624003018022202407140c091120f07100e5070380741007522103a0381d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 110835116 1250 110833866 110833873
    0x4030207030c0807030213060b180109180204031208130f02040605060307030509010b0a05030d050c010221150f0901030b180706120605060c030301030206070305091003020334050702040905 83
    0x703039119510344e1141e031072204038041d2940c0c4d841002206850700c50402200d000d1160b503131420a820030070221074000b0154013414828440302c04259901400505640000100e0006a40754110305140d108100f4046812041102c01001c100000801c9a0b10000b0103500c110071900000b014400580600202e030455500054040100034080e585600711602500c00c00c002042418548001d00c0079201960244540507800075004032102841203006000c1d50240a000504000c044602142d004008080604d031019081007030060461b4543c20700302c51000220b898000071038080f030100700c100f90144006010000d4010010b80001e44a82c2c1e03940c0303007821140c103480c0c20586590001d0070b60032450f2850350300140760000100c1c00742065000c60304082c602000440c01e41e80f8690800500f64031a590807405c07c1014411045552201c030f000c2c110380d8207907442c091384034a48031300d0b0452a58004290706002761203061503003074204c0610590501c08645803030501d940303407801e001260103002c4081d03000b0041d21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 110836366 1250 110835116 110835119
    0x1c09050a06050a0f0e07060f02010b0909030c06011d01090203041a0709083009060c010908180409200f1201050411060c0c0d0303110a090603050109180b04030207030c 73
    0x40d0540c07000d440f0340503020080242100000040f13013207501c848904801d50303100c0f64050103918082c114054005941e4800451070340694004518468810390f51110154804511645003000a102d0540501700360ba0349140703441404e1500b603141b500b041c8521404681d002000c9000d010703029125009104c803a0084212600b4903001c01040358181d13109850f018000d01c004c103c4001c01c80d964446039007001c0c4140010742e0015221041c0e242d400103c0c1b02c4e91007002040342100040c1c00707000e6034180346d000e0080a503c41c3c0e02c40b0b2054201810541c8110300c02ea2900050701c0003d0344a2072038441c20300a03944003c0a1913211008180000805184254800c044803440114800f054001c203211350b20482c4040300f034000c20010321010b401400044010b80e0004d0315414941d050101040554034000c0c980401c0c0c03420303821100580c91340064414400120300c05c8051080e141c0600560f0b0040c00c072410108a800090f030348914071040c0410000348250502800700341814403c0100704003668001c41c00901b802d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 110837616 1250 110836366 110836373
    0x150c030a0e0111031c0f0207021f030e0a03050c100605130506220501080c0d020102100c0203070b0103052a0105070f1704080303011406030f010308070609060204170708010903051c09050a 82
    0x203012091103105c070a4103009100506020b0340c0207488a165016100d051000c000c0c03105081842c040100e5442015038424155484800c03c002000d07906019855050303a90900003003c5003007a050b18015410241040c0c010080c54803100c00c2030321500641000000c0c15142d00c0000303040320b202403540000100190030390914500b1181c1c0054121002502202c40c002d00300c8041c0100b0308040a0041c0c0135821140c0b07901f4072915181c00400c5c400c40244166840e1a1090b552902c1100742a00306030740c1d551200c0142c03c1e01c621a40f042000e40307481030060310011140c20000034510321a482d00109031340c004c84c44810803c0301d080c06200b038203440110303402d03292034036007212903501c0d0400d1088160fa1824100d1110080c14440c0459018581e82d071800180783c2e08503102c0180d264000300044848554030725904000c91228400382014200340320009031940c8541e070100c0d140220b81d801c890740301d914040080740000c1d080030895811840402c0144810b11110078680010031200c180a0024080e040255040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 110838866 1250 110837616 110837647
    0x90a140c180901030309030f1106070b040605060307150f05041d040302120708070204051e040506011e14010311070606082a010905060310120c05150c030a0e011103 72
    0x444020041c4003900c0c18000007000010207003880090081030000e681480420f120320f03200280c040c010302d2400200189000400d58a41c407020043e10307594210000c1c041000399074011603810401c00c800138400c441c20240c0d0880c0511109100c28144044203841c091018003a2040d0b800400d5540d8154244840700185002c022300201d030114014082d02800d055010080b105a0b04100e4000c0d8490b8241002c0381d080c40028800600100f00e041b894040d0b0201880314403540c1c602c224821000350555514040350580c50000540300d5032265250500d00b0702407408400100080150240b03404185024070445185081c810301001400042c14000e02160301e07140020800f07090809400107440c0040c11102c050071084403002464002030845000f0811480c1c1071001d1600320342d008902c1120103680301c50f00c0d6107101c00b40340e0071100280030030010011480d010004000c51078903c0384040c074145400613810b80780d12556082409202810751000035a902ca200d03080c2010017800112591046801d410641 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 110840116 1250 110838866 110838877
    0xa020c060106090b0403030e040609052401031413020d0803070905030d030236101706030309010f05030a091707050c0301020c120c10060e090106060e010e090a140c 72
    0x121031158100014050f4030414410007100c5070103600c941001e0440ea1b088940c50b04d580b08041d40a034272514041080e640500c18640540081460b40c3d401d0b0003a2429452121200c041950501d0310340341d91080001c1c0700c07502d0258840f070240008070714008036100282690310b0740000a003141001100700800d25402c049400b050f51000c034222a11159007080813400ea00c40c7c5070720400d5403a00c503054800040340444502ca40c2c03410140402104580304e40100d01e64104802404c0c000903880000b04000907400a0411f4008000b038010354a0019000000303007009d80440800c10400400200282101701e0030f0f402110100c1d030181c10520b16103c0020385032002e4106460595050051103041c2400e480c0c14800c84101c24206805410b0500100002441c2900840d401d00000d004010f40b81046003098820320025154008040381c0500f000160342e42110003541201052010101000720180e81140d881c10003288101c60b9400656079030752104001e0b200c2c500c2049242c0104c00244020050024064103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 110841366 1250 110840116 110840137
    0x2120102071b1401120b0a0b0a032009090c0a0c05030316020f06091209011209060203100b0708250f05070501020f01051302010c030908060408040f0510021b0a030b0a02 74
    0xe059203485070003c03c07003203992480d80400d00b049042c1050a1564109940c1454014040c035240c0c0e540c4e12041c00e5960010296070006651047d1003441c0c441803c400350584004e42041c02d007400c40f1080402c0710307214080e18420038000d002c506090201c0c407406907170701c003154032800340d03902e9003007600d5070b80011903d00303d000c8058041e040e0b448116840c001503251064480710000d03c40f02c803c07101001070301c0d4403c0aa41e81007080300020342c1c0340ca400c6400340c680d5440c07060400507a2890103100312000e034021500100103116007000f03008041042c40050751100750245a0304d030410124508030381201005850000c14860704100080140440498074800303c45081c4c003130703503400c000d4880382d45e080ba40115488004803486800100c0036502ca0202001454070904240340410740700c174139081c60b14204450843d6030001c0080c060000b06001c000782401000c0c251603d01c00c1041658010b512940014000f000480b10080c040c81d455492503c0b42c80150342020714400d8070f00301180481d010354000f000c0310 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 110842616 1250 110841366 110841413
    0x1205070c0b160b090a0c05010f020c2101050c0a08071b020301090b070810080613050a20010e0411030a0b040b060d02191103120a15120b01080106061b0212010207 71
    0x40842c1000300e2000012136201d03134400305c801d04280c0151007422027040924114401e1405660554844003034080600142c650300305003106ca00e103505400e56000130a540660b8005001840030705400031501078006003103040050741d1301464400240e05040d104400b0750705601300300d218020b109103020303864000d1007103035910710442e51074102c4140c4043c103c0c419480f80c1c4d031100b40041c10140114a1100345e03603105505032111802c65481c4c6402e4140c059410022496600340d0a0216682140491110038000d940a2040d040c114000bc0340030b010050100d090aa2a5002e010803569681e110364144400206050788400141800c0d4000f07401548080380419a0241c031607440b180a103401030401c90703000c0003c0d03181084070318003501078100c090076120b00307980c44100714490070807200c50b018081c10341e560710301c07401c0f0707402d41410345070840c043e4409042d592500324140041640038218600c000a81885001107040c2e910204103a08603031501a5065403000c154081000000210b5144400381140380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 110843866 1250 110842616 110842621
    0x2070b10050307091107081306020601060f09210b0c0904050603120313060608060103121d0a06050901050c03120103050d020d0507060506010c1b060906020106031205070c0b160b 78
    0x16815035116a001e8194150b200c01c404001403d0940c200f42404580340c6070150405859980da980b0300e402215400c1100030741400203100080c0c0c1082018010b0007070f0b15040301c0400074100003420014403800340480c010190b00d2038004009031782c01c8100c20158028a0302c00705107800c0b24582103640000240900c51810200405c50900d030008041f07481c20240f6075204c0c5561190402c0c0840001c1c000c00c1158102e8655000140c00402880b41e14020350041e125568007440d5481d0052501400500c80f1406100c0c81d40c81d44c05035241d0211500030b031405420300c91f070786009101c0143c5550240002c109620b2100040e0304200d0388084440a048901c500110380550007204030071780c0c45580e001c0c10040050410302140c800300d00701d60015600a003040c1401d0740c0402d0309444840c20710fa281010068102c00c010030800c012507004031540010b0100f0f10080001030f04542d1588440c0c050071460404022020404100348200c010842004001c00c01032a41d9507170341c40940b04041002541c042c0c84070303641d5800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 110845116 1250 110843866 110843881
    0x915030603080a030507140c0a1a091b030f030408160b0c0604020f0d021002010b030f0705030601090c050c0a0c03150606170a0204080a050604060c09050114090607021302070b 77
    0x14000c180c99200c00b0380e0f414800b400104a00400004008a081115040020129098440003000240c0d02180a0030b1040707420b0a10544011040e22032011520403075007000800e09000c54910702900030b070840841360303c40c07020009240a80e00144601140070005000424400c000385040030070220031060403030550744400d01313203c0303009124002520303030401030007d001458030a00307080b003903c13000380503004022030350b0045861a09181030b04000361303540c1ea202603418a07007000392410228141008200181c1428082510341d4018418102001d40f02c480b003c1d522805003040d200500721480031100707010b8039400c20403410380b11488103448111860000001c0d030b00f20f03030068a054078180e4940440049030f400039400c000307100410003041550b09000c0030843c00b0090001e2400d90380504010002400c05080c428100d0302c04405110500c0000342c0c0c20032103640c0000000c2101c83c0c0a071a1107480d90344400100300a823041c8900254442d1030a034101c50800c0c050f41c00b400d1303030f14001d0100d04919600c116 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 110846366 1250 110845116 110845121
    0xf01020d091a1e0901060906060507060b06040f12060209030115030303060e0708070509130f062c06090921190c200d080c01020306090a020a0c032d091503 68
    0x482010011503501640f400282d4006000d607003100642e8000500d050392681070508485c1c4a40006001a1000401005003d00c0b80034401003000102d603071510701840d0088010203000c46100d924a03100c0740b088031005000266043d00c15420000d80203010008a00400340040318543c00100c02007440c002020481c081040c400d0340c8a070031280c4403a4915191141e09840e20380001e0945035000c2c0041700070501c10320082c02098900c80a00202081c07190610800340e400d2281e2152500100c5902c0e0750f5241d0362100019a1504403a055807214001d80728110024181107010038103046030b40500040340000310481004110080041c94000041e0950000c200c41448036094040d00402590403043c0c8814030110341c04082c800b004101c80d211183d682d0b50721949800808040300980d501004200c0b0790306101400b1a40300d01c000f1011450818031040151622a40c69800303420080148441a448001d020280c412082600c1800c07480c0f00f40c41c00006c008a80d50300031000c00034024080511101c0c020b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 110847616 1250 110846366 110846371
    0x307030f0f1704150608030306101404061107031205070c050d020d021201020405040f060503060906040f080304060f020c01090219081209030309060d0605030c0619030507020f01020d091a 82
    0x42e6981018400d1564501030071203400341050f07035254141000440800e650740b00c0c02008241d03000142d5101e140202c01c009209074202c0c0380c0c4051284030010600c10040c2d9200f1242030318018201921045201c802040c608296900014000214580c641803119004000f038421544210740701048161100c00740700c110310b0049002034220080340d03009401071074003180e1102c0ca0240c2c40001402c080d50f0f10000703825070f25a840c1c45100d8030398401d000c0c03002d41400c1c00250b80c84200d0304c0003881542829680c1818060340010050120040403000c0f408222032038001603110110568150340f2042ca005000c4e00804845d0707403c911600210b0005101560030250410031110660060151154103c02e801e4050780800344c60390f4140000c02c411419503072120060241403114010009215040070f01741807810340720048240c8100710600c461b45001d0004204108100260301d004603068685040c04e80c40c00003136410304000ba5001040b40405004c4581c000c3c8600c03406201058000610810b1001a0a809 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 110848866 1250 110847616 110847647
    0xb04062102010327030905030f0610090f0b04020a030f050115050a1211040e010f06030b220b04110903060a020f040509041506030b0114031f110702060304050307030f 73
    0x150050310090340c0a80e000c070280707a688507002d01c40303810400ca140e03003c440701c18011000318081d5401441141820080c80b8503a841e00030040c11030b4140074041c03002c01a5644100e0150799119882421000080e0300141d1020380058800e40d1140c1400d000a800f5214000880404602d00b0300009410000c0c161884a0049242c841601d03103400031408807409032128803482c0d2030380d460b40501c1010f000214001e000804034020f810802d035041c01c001c1c0d9614400c03175114404241c14038424003d107589800141b04600700d41c000607040d1541151801e4040c10326283c901e98020701c0c1151482d10403100400034060b07200210150f0340e003691019480401c0740102036110b00700c3d10040c003040c881410314400302e5401a01130741e4018440c40031034080d038054400039041140d404c040ca500400c07440710084400111000700700c001c0d08803a41d5144814032065000000f44600c59110144807410300e52940c215841d240d009800d01e6660701e4142400c0796070794050f00e03044000902165039100304500c20704403030103c0d840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 110850116 1250 110848866 110848919
    0x12040e16020a021011030906032d06100525033f0518060c04030c08150f0a06120b090c0603010f05010c03110a03090303081008062a04090b0406 63
    0x4540b08445240380045174040c10b200401000d03e04c1d80e00c030381c0a5441036215600c120801543d60012108003480007a013082810140b00903c1403940d55500418055811441e2a5444204020351210203d43d2039500712548200410b0810034143d000c21588142210403100c00a0314510b80d0001140090701c5203e030004034603154241381421025044160001c1c0d281224145920322005070702d0801c8000c4d15a4440701c900002e0400402018a010320700a00d406030140c840c001920179048144c2c140103003c414001c0700c1400240180d0f40ba0343c0890007601164440c0307120f41105281284c181c000544201c40340344925001e00005141410031039059400c8200715070070441c41e20f070064030799107580309045090224244601d030603030404000111996010f5543c05402d58510309018128070006041d003440029040824001c15800088032030300035162442c0358607000111008101000010f80000210710400240000d001c2442d0308601507900040b0340401c051665205060100d03090310050318a08030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 110851366 1250 110850116 110850139
    0x14071a13090c051306050301090b0105030105030a060b01020106210c170a12020c060d0f0c0305070c0f020609040c120b010504050a06120905030a02070303120209030a08070512040e16020a02 83
    0x104a5005928200b40d1420304600704480051a22100c5a140e0481d90001c4d1004c00108802102e5010305400301600b801c00c40c1c034550400c004662142151100078100da40c0b02c801240081e4400d500c07110091481b0b800203c40d0002c4e118440d07000a20021054a882910b074a02160804101880355084503c00b0010401030503660384817100122030001ca84158015070848152a40b11000200460412084002038075249450094115241e4110380c504162905040102c510f030003412043c1040c3c0c02050881154a2030301c0003c10070b104203800c1e10b402ca400c1c51800d08000d50410b0319024110741044040c0a00c0c59024011685070141c0d100d120b0340b10129190801c01a800741100101d816603001010600d0729454540f54510b500400145005030700c184420003e055104040c0303058050401021761402c5404000640e9820a004020f06076a00000b810303400c010b810050032100643d10b0300c0b505c0c0c0301c640c3c3d4a1030b8483c006044440030075114001a005001901c04100d0f6071071151300604030403019 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 110852616 1250 110851366 110851379
    0x60c050c090f39090102010c09060e1201090818091e0703050a02070507061e080c040608130b01140a09020c12031305060903090a08030304050709050a0914071a13 71
    0x70030a0801e01c20306244542552031121403c69060030301d11000050355a030400b032000900b161003260a08040180040c07050003115403082c80601c0645045503680010040f1414160040121407401042d440001074090b030b848080388054041504120b40040032a034481e200018100380b01c2c100c102942000340d00017000c1501070390210f500014a0000103080040555800c0e103094007540081c00403980000c0c00326880c1c9250080200708140c0d030714158440d401d0a2955100314000da0040000744200d400024014a080c4040380d9209608101da628495071341d203210310400d01c0900041e500400c5611030114040c030700780c0211003110307180000504650031030f00804d0415802c060f1520309854003203041c813400700740c0c00c20040340104178280c06150340d00c030307020200021229107901c00c6903d0b41080c81040007007900420940111980445d020400c2d540c2c0c41000802032030895402084034204080e80440c0150015402c026031b1054401000d0102001400c0c020754000d28a4240503d4080d0100b400003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 110853866 1250 110852616 110852641
    0x1060b040b0f0a030605030a0309090f020a0e061608070b01030308010911091002071505040f0501020c13020702011b1211010b0a060c080c01020a0f0e0904030c0f1b060c050c090f 78
    0x80243c40c1c03a000030754a13202c0c000030382030821079002640044e4910304140f281c0302140c880e400e50307071a1004045140c002200300192040002860491085e41c003c00c0c090b100100301003c0301c00303a591240c5019a2990181381c03510124401380015400205604004681c1c0d0216100385000803d001c2e000354203000b070381c20400c0200e860079901041140500c42c0300041c580f10008680c0b0300005191500b0b62514100383c00c480d2812020790000341150b0203407121051b9610303424070703100303208982c1c40c805a600c414600060310398043c50340c000001181228021404d1120980c2040116486580d5501125447c0f40d00903090b203070709030507407940121111000c0040b58000d801503162244103504d140d08044140c1c40003422a0010560580420004014102c0c1d8584c0084480001d0074100d506072000e081549000385000400d84004001001da1006c410070f21488903400084944403410344401b058540f04000c0c100b150601e030032162403081400c042050301d030040c01944640c1c1c00d840944019078894480880 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 110855116 1250 110853866 110853877
    0x5040f020f04110c0307021839040e040210082814090601030210051801110307050609070617061810030624060516080904020d0906090501060b040b0f 66
    0x10b0050360780b007034500d064000c10003902c03103000c0c50806984c485450303006009920000d1010002c000000074108400b03030b8000121100401da056001c1700c02030a04010409601c3c409049140440c8408a800600005014940d40c0700314403d440640030001c6046040d1203400c07041e1040000c143e1110130007240d51503110602440b6000c841b0b0040b50074280900341e1601d1080a5905410030b40001c1c0c014019400d01070414807940c0c125251440c94035006201c0c035091074100c00782c42810003102c0881c411141c030b0304206581c212908642039500c14101501c0b0070755501c1c4507215410104002e00c111105002d041c0901074841e40c00680305c000a04240018010b0040c801081411000100780300030002c40d0352481b85c49190341c02d0002c160a4041c031a500c08803904805c0d84528100002008120041150f4040d0300304220b038400351280c2c41d40700358400500640108a111400c0324601009c080c20300080e50000f0030303518080c9008000700c41c0c0315500c00300c061240340500510010100211090390517250005c1c078 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 110856366 1250 110855116 110855119
    0x409061e0b250503030603010506060c101824050106020d05030a021e04060c1104051e0a0f0c09090f050f010320060307030516020601060e01080a0605150c01050601020105040f020f 79
    0x700e41040742600d14155030b007280300392641ea002108200c104c1c103092041c04c0d0401000c840b801d0a000c01003008a65810031603a078000c045480f900c203894012082488240c040380d104a0301042c01104250550411281d800071048040c00c0030000a03c01d40081103107806128182e55651030b5540d07481800000c1e500c8a550352074142c00c41e030010211590350078050300242c1629540c0070003140950411004210003803044511a40c41c203801d101d0312403a0443c98599a080720102c040c1c0540d110419280140b0702804010440790501e00b100041c80e5011151000b55480050204615014403906c0341c111041210081068201c9100500c0894a10409000c080c1c0e41130310344031400d000d9a0082001d9820036903050000c0381c0c9076010301010084402c144035455000388003d001541c0341c1200107100b140e030a801c85042c420359070080b8003208441d0308240007816000d4000b44042c0440c44088601d03030710040e402c050652900007ca0039075841030203598001c541210184082007010b40810040c1c58061240a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 110857616 1250 110856366 110856397
    0x9050a080a081b070305030a03051b030a0e0a08040618090e1203090a05030d0504031b050706030b03160e060102120313030e0402091513050d12180f0b0409061e0b 71
    0x100f8881e03020400720010f0f5120350055038480e10181e0703000d01034403006040103401c00640324041c1c0130b50244000750707503000002d050045182c6144403103240c1400340b0400040c00504001402060107034000c68202000452480711421569850b00e00307000700d402c03451210042e50000c0030b007400804d07441c070091900800785070150f03100f50303815640c2d051035a48050f07100400305448008201c00e154025649002c0294400601c3c00106850355805407200d071a4042e040900d03a60328481e0304903460030071030081d0121140b405a058152559040001410b0459107039005100c3c800c0704100050488056034016008540507441c0d4840743d503429101000038003c51a0030030b40c20b11034800c6d0717a40da91412000e18901c2040c4103568916403108091001c00d103400450050203191081070000340c0b018220300e0511010325181c41e5060740d01c012500e140406070700103101e03400310703285c0030840108020007081180d84090f001c103c0f4540c1d4103800584e1010b40302d504030300c2400010080000006e00340061608075950040c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 110858866 1250 110857616 110857657
    0xb030a020108100b071506050d0302060103020616060204030b0105033f220302040b0d080d0207060b03060c0307080610020c0d080d020a050408010609110412050a0f060b0109050a080a08 81
    0x2484c1c5590060300013a6400f6a060201449107006403060700c004d0801039030391504104a0f0380b0082e50b40d00341848001c0c00b034240090b002a444003903280b011049a88044103656035540c03401c0c4150489000e0058521038003610780000b103d445103060101602484450268143c42030301e9000b00d40300e8040e140080074110401660700c42d0700710707014007900d583d06400c07860b5460380c1180148012104044105401030f0402c4400b0340c0400c0401064440e42401c4034000360782ca100503c1c00c24003800c0b5078808990144519814040286080b00c0034511901c165074400c00503644803030401100020041c410300258101d02c420604030300345003040c90640c07400f40714031514045811222a0480c1e20522107000002c1001c01c0c14401210280a032200078022020113001200003103800240b984186e11980100001e890150420401d0a000301c440481c1c002e0091169600d040c10040d0140095030100380c001611028042030034601300003d4029268150004c20314207102d030707032014901e500941c41404200c015190 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 110860116 1250 110858866 110858879
    0x2010e040e06040b07050301060e0621010e15030a021509041b181e170f060f150405070807110a0b0a0207051603050c01050a032a02100b030a02010810 66
    0xc0d2250300ea0418024036240c90107041003613500d10301800340410030200b0070041144030791141c1000f5811104071501c0388d450f01c182c590740101c01001d03801028645018000060090400e04910344103110396100c100204444900b010380320341d8403800c02580180404001c428070004080584901003010304009028415480944990f04204c100c950000b00385504000300030840210810080044940310b613051400c2400100039142d0502424190301c0c2c0203015650b10007010081040a50103401c20ba418504100f109042c44c40811511001000c98070803180606003020300c10035100d0305683c1e45601c01c907210900d045803c0a81171081507d144100907021022510400e6424000c1884110059076a4101e151103800e2008541e2198001c0e2502074013040859804500600e40580c2440c04c15503580d04200150000c10304e0021200c10201d1700b081c1d560b00e0007090030703500522880c1031f02241e80202d0f400c0300c0d5005a03028290f10981681200005600550207418856080342c4a0100022241c3c0c4400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 110861366 1250 110860116 110860121
    0x907180518100b01030e0a0512090a0e0c04090608160b03060303090a090f0b0d0b0106050a14161104020703050702151605030901030c08132003070b070204181e02010e04 74
    0x350b240285940e0741c100f540302d60f0580303d0444070310036080c003803c0c083c090394952603181d2481e1083e800f40c035600020750060941e569001c0d500504044035800ca05414014410300b80354109003c1c0941191900e0408140c41e10005410044114800040098035081054054882c0c1018008940610050120380c14694821000e00064002e0000001c2da4440c054441c000303959405001c6400390303450780000c0c0081150640d071300b415206141021581e0382c280301421580e0864001000303000340d40200c0c89584221640703c402820b140520010001040da034010030040307116600004012860801c2184014245800c5a5041c405407480072400c20307a032401d440141c6401100126101d0300005a42c3c0107541c1c042c881c0d00c40302c100f01e20b000c409602c2c214440030307090400301c540900b007010001085910528048004031400202400303a422030765842c403425a154220303140c2284a1800d00c1d40c820701030790041d2700803101e0581180001003540b02d140080a002c0060200690411010001401041d03ca50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 110862616 1250 110861366 110861383
    0x6090207060209090c0901020703030f020c0a030b0405010509030a051e07020301020307180f0b22030512041403033109050f010302010f030e0303060f01020717150907180518 76
    0x140800b507603d1050b43d040006500006000c0c459101090100000c0c60b640012181d0660f581800d003241d10310034011091386014160f0304055406155541c01108000d0305880c0d40c0c0c001d40c400ca009003c6a1141d0402c80e03144d0107103103241400a601840140c01d00010748d601e000032101220b8056180041c0e80c6c01190a90340222880340102c0d55041d10000c6010318800000c004041c104980001181803900740855481006111034400b0703482ca8801a0508501610f04021070f400004c80350030000381584200c6a410508c540c0d80b60019500030106d071400c012003115070800d810140000050f00500303544650040c80241c4140040a4a001280e01c036074510801d400781c030220348034620941c51071000401e860001c0f80e8030400c02d4203004a5030030f01c0c1130000503030382c00400850321030206880ea000100e01d8811a58440d250300c10351400c00d80d4281102143c418a10400c07d10001c01c0c590701e0300010f40d598800307880748031000b035001e600f007008034403640d4081c0d9000300001150300750007a90003000c140b9041c0b08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 110863866 1250 110862616 110862623
    0x10f0e01140d0207150914010203070801090f0b040c0f090e040b07030e1903021507020a02090c0f09090c030108070512150712150513060b07080f0702060409060509060a03051c020106090207 83
    0x503940104103111a288011071407e20802c025451440d00e9000108402011700c00c0c03d02213601c030b08507111054940c0d04810403685001d0000c0201185141009117151101184980445ca0090b07010441d0314040800521542d00103a079503906454650341200201601e180e982101e010362403101c070f84010402e000b54520341c003e60040424054240c141140d00d40080e00c400107644c007026441c2c0040c0c541c1d040345548041c40620241d11801c01e10a40740207885801c0f1441d074849480c0e0100320000d0030810185060721070802c225458643c0350401d01183c00c50410544c50303160300a03509400c0d081c50a206050f4060080d1500081d180b400d010001d00b81c0d071902c048904104440c100600c52400c11106802c1d0380070b060b94041c04454540310200e00b5500c641c2e10050100c00c4d00042c081406440c01d011030b0b81481d4040c0441e83d4030761782d800e0072200a12150080714414200e5402056480c601040807205413500034001c0c4c00100c0c00000c2602d0b02c19110070f2198199521020001400c05480c8041c1407031030301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 110865116 1250 110863866 110863871
    0x1020c1207050d090810090203190b01090e06010e040f11120a0317060a030308040c0b03100801060b0f1b0a05030d0f0501080d0906121e020702010f0e01140d020715 72
    0x582e103405810310759460b1030003040002e480c104101396540001c5d082e80d8500c04d82400222a402c500210f41070007042c0401c1c0300240d04958010b010049014440350403141d0754130f020003881c90300d41d0300e45882d07040038420000704a28080203e000700e101e0b468045445440b640c1e100c0340d0300c850880424842850b002907007081d42c20100a4a05250b000300d450020051070040407046850204009a288401404003a003001040c000040801500d210356601910407072011a44074648600b0703010410005018031075141d428000c0008445041c4400d8404401d050300d40241081c0e080d1802d208103c40004249200c1e01c201041140490003c1c00140520409000f02081550100d0023a1060310010b900a50650340006802c6d2000740e4015810001d44045146c034401c0082d604c0000380190010740840991410b603450328280c1895640d0081052030b100781c0b2800c1c0395020800c810b4400c8042540003030b020032141d42000403a04e00d01001402c0c000001000182050055150103032001c00304c0c40e0749a609075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 110866366 1250 110865116 110865127
    0x90a050105071d040e0304091e050405030a090605040b03010308030a0f05091b030601080a060203190c03051b070c150203070609110316030305120a0f020c070927020f0301020c12 78
    0x40389402a070f21220f1090f68140088400008034555a102d02c0c031170a4070070395035404100055290900e60000c2101d00c080300740036600301800e00b00e4681d403041c060300021500500c0001509401a0203440440b23a40c3c2e02c0840c02c5a10b940c44052560f4030041020b035034036907500c030005c40c000d030140329242c061160f00005004815400d100c2481000d214111a44203600807001009403041c00a00999913917845503016840e900c48407080c4800003503c840e480000c904080302031070030980c5a80024803403000f8061000c3d02c1d1820700c02e50142c41c4281980602042c001c1c820074480c800449036202104d400702e20450b49410320b00e4449408807803150750b04407152070241074680c02c1490200b0140200080300e03050300d110185503680c068040d100d810980f058140b0400001500d0848951104420005102055507903882c0713501c0d0107403030b400f05001e161307085403602108802a10007554034240e07100589074500d0b421141c1c1e40030002d40e01003100c0c20703e40c159020440c17a01106000d00030100c0c98034084d50001d8685 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 110867616 1250 110866366 110866397
    0xa0903050105090304180c0e100201021201090b010e0d03020c0a0b07020a0e09060f06032a040c030605030c04050a020417030406030e011406010f03090b071805030705010e0603090a05010507 83
    0x541000e4081030f06a48140010f119014280308001c410b002041c00014500703981401c1940c000a8841c8100e9010ba450b0712075042854041d002424400128506040160b0b00da1003c01c00310740710b25000500003a2041c4005149017441055a40d649020b801140c014200240c00102400c80ca600305400785000401e41d0f0382142080d20129000c4c22091240c00c10b503141902c7d100e540c0306002441c0005900302c580c0071507226102170001c580324212101007101c542d011103e44400010030b07603032918003c900c1c1c042600061842480b501042d42c80c020040c01c28042c03000200006443c0142400b0505070303081100240c0d0b1007103041e141107002c03600c00c00703540c4071342c50b100001c0c003140d01910000d0440d0741007040e42e506c164041101154000d000f42809803048045240071002015903000003000d61020000788500c003a0020745810800c00c0031402c44079540d8481060507143c0500b031258502003044c2c4001c0c40610300c0c080001e9039101c9500700c100c5110100c5503d03030a09681d002c0d00c176200420004040001301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 110868866 1250 110867616 110867621
    0x40608100302150703110102030c0403050c01021f0c0509030d110d0c020303070f05010207141b06120a0c17010303030f0b03030a090302090c0c060f0702060f070f0e0a09020a09030501 80
    0x4a041045152000c9180d80c000c2043c00c2000b40c1150480030300011070707034101400780000d01440e03205000210b4481c03400d150b217881c00354402e0009581c2c0b03106a2820759204d61001400ac0700c440910320011401d41d4072144010050800701000308107011081c400503005032410000c1d40d045552030ba84154101c0342e00b000302820080340d4520780c020000d0b1058a0805030300c00008440107035910800d1326020b9031960074014024080e4010003007103400200c10707200c030000c00081c0c0c004602e50007108916089888104220080c4900381110b00f504a18100017181c070380f5a948685d0800d90a0706003240c1c00040c0094052900009800840100340d4841609843c0030180c0705051300e249050b401145450404c01d0301404040d0700e888000e202e82010b42c000380b065040c00094504064291003120382034100004c0000145074201c903541c00621031440010400320b800c00385c4a00400440d1905402c002a1034012605100b500c0d50150300329801d05400240480d10340300500c1c08040c0343c3d458003406401d6161203801d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 110870116 1250 110868866 110868871
    0x50f01150510050f07020f1e040c0f0e27040503030a050c0909040f030908031206040b01020d091203050712030209040c03020c0705220612120201060b0f0a14030c040608 74
    0xb41070342d0000c8001094001044864002401d840e80307486200500c0001c0308004e100701c0150300301010040001c01400411003003569078900315404c1c072040c0c206140c2103940300c80d810ba645001980300c1c60781003035509008100d07058030345104d0460034580a2202142c030f1b4000090b602111241e00020800086070315501c610f58010b00401c10b001d141414000010344005400340c400360414841c50075240415014000941c0100f174074070190303900d0f6014107004c071001140427100700740583d00b031000ca0422913101007108889030005450307864219040c44000c940a00e10164100c0600c5401c00070036012034034000c06003089065076500940e82f0305400090005407000c48074104241801441403240040300450b804c0c0980e40103680d90710121114850030b44481c80c1456520441d24900b281c00f0980c40010360442403114012403549040e015296002c90880f0345500c11046005014002600c0045030f01d0024444100c0070f29180140d80d100c4070803950350740d100380e41d403101400000a0400c002604106480d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 110871366 1250 110870116 110870119
    0x507020a080f030a06050a0f060801050f0a211a04050c09070f0516021504030209090307050616110106062001050c07020f190609050405090c10030b0409050f011505 72
    0x103965946a215000c1c41c01a440100808000910300c003446500503401414000c0440c41d05554604000c0c016000c180120400114020700200d2681403050031590060300c060407000141d031801512068090070f2424a01031864849203140200d0202d0903250030079072007030305010801d00b8145840d610340154414110f028200e00e40410581540020401c002400d00d8205960b80b900d40000445650f0064880294040c244d040a4818002404080e00651f403098425255036203910b030b14a50386c0e01030030748010a2944148000380241411001c01084070b12a424038000c5104850b00d4142900d0042c0c1100c00000e807503028460002c038014060f01c80c0f08000300d00030000f80c02d0610007000188203001000c2d001d1035013112501c909072100c0c20030410707170640e284101c42403540344c07100145022118810700b80300d01e06020100d07442c0d400205140c40c40303110007020b1104a4600c92415006810f00e03010f5141d225582c0c400080108a00344441d1802e02980400041c0e1690385a019640d004103d40026 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 110872616 1250 110871366 110871373
    0x9080912010e060a0c0e060403110a060504030b0601050d0b120d080a09051c02031e0307030c030b090a0906060b07060b12060606160503040f1202010e03030901050d050c0c011806050702 81
    0x140b02048001c5015034005030121000b1440c600101400d80d200da840b503c105400580000b000820310102c2c600b0304141c40700850701144502d54490040f10540510f010180440e241400825200d40c002c1f40200b030107801d031640204022401c500020100189200c1503002c503017150600d20082030b4400f001c0d5a0080040c201040001003544640390381e02c0d0700d4000400c4d208a1f4030716208826008109441407c00a2102c04084a0300f480042401c2c2e001030347c0c414013081c1001c0b0002d84082c041d00428141603000f0b4032a070321581e610020000a041143d0055a880d40d44020110324400384000078a915409200042030b03164001c402e0048074070004c0040b0206030049001d100351070750b071001281d00400c0705004080c3c0740c0415061450951181d40d20072076140344d4850001851668007000d01604900036200e01c1c414000150600d900c03842021000e0340003039400c11191000403034507403083d6008804090380e40d0600d04804002401c48030020f0801d41c03142a40404141000194055035502c4221803014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 110873866 1250 110872616 110872631
    0x1a0103060b0702040b040f0c02070312090303050a03020d0609050108070e1803030c0f040503150f100501020c01050d090213020c071203120203130c090f0b040911150d0908091201 78
    0x350800c0d0b010b80c01000f0300c10707a2034688840c41651a030b040404e00f801800000c2104020140000e550307000c03a0704c8111039603002d00b00b083c40f6550040301114200d80c0c064960915064030034008500a5010700882280e85540313040100e2026001d124603806040d55000500c1c0a6041410031840c10800410108124241030048540f6080200c140c075000310030f89540c00d0700d8070011076800d0201c0c080e64001c0c1d50548510884219040114080345000c0c1b0303941c2000c0c1031641c40e1008210540300700341c050507000d64880d400c1d20441d94450302c020180400c482c00c001071100c00c1c40c5c2c00600c41c0c6d00d4080c0444166074010921306805403003404100e008003001e241c0003000b52629503000c1d08002000702c80794040341c3e0110000d07140d0480e0b50a4251140e501454100d06103403101a49070052480409003400103182500346140b0341018401c2084a40e08203143c4101c045085042010103c90520b072030040311000c0c01007801c3c0e499203002e001c0617148612102a1240900b07010b021040c41307008111040d50381410341c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 110875116 1250 110873866 110873879
    0x507110c0a030308060a090f02031819080d06090516021203070f0c14010c0c0507050d030509040c020c03030406090302041808070f020102030903150906070206040c0e060d0606091a010306 82
    0x881c0100c96141c140010195034000001d00e0424103944240713286801d004a43c3d20401095006500c503000c503906901e050200092866612006a0603400d829050710608002040d61031026041c40a0104000b0581c50380f00d00b49041501c009480c40d10901000d1646442180d405005984540c55070700406425450501c2c40104620042c1000d40144005118240107126504164a01700f20484000340304210040c000203000f2503601c5025103171406030680210712480c1c04424280d0203a0559503113420b100b100410003004040e21b1200600307512072401c4130b02603528244040c000030005921491030613403460044c0401c2d0b4203a0708180e2a50203e02e4240000a50140b091300c242c12b0f00b03d11158079407001c601c0141c1c9144100b801440d8075228003a83c00b9481d5000024080c800d003881e0081e40c180361a0301c541a6070b51002034134020180c4038031007424008054542c1d00c2c158818401000300b12004208d4555004940301600100b09064a5142c0040d002005c1340ca0990820400c0c641004030514150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 110876366 1250 110875116 110875129
    0x30d050304150905010b0a03080901080901111b0a1a0f0106021501060f0c17041706010302010804260f180f1e0d06020c070312020c0603010e04080c0d030507110c 71
    0x18820540540c3c403c1c0c51424080258442c6003055400b81020940948a0400c240240c00c02da50841c002070a440c0025030030384040c019000d2908484c1d00d49810052300b0304a2681c02c100c0d189d00907846108004560300070400c411003461b84110780d11410700c210b0510141c0f1045496058101400350350240c0c8412074980000301000d811600140780c003081d17202030900111500d00c5a880c01505121854455000313518a610050040350b1078942e403a5003840001103400e40300c440034032002e03000c42c600b070001801040c25100c5000301d082e03002c400b5002c00903601171440c02e182c0040402c00d40301c8601140311030405505400c40400400d00301c61524902d4022000140000540904039030b014a1040400c030041d1100441c0e11229079200406544a52503103071aa80e666026120545900441003810f0142d1340c004191710888180c00740030245140c1c00c09040380100180907208540000003041910510b0700c3c20f00400318015015600401c544c2001c0100518141c20500c807481e480c0c004041e1040140d0b6042c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 110877616 1250 110876366 110876393
    0x10e0a021303030e06120c030a0c020c180603160303030c09050d020a03120203090312070501050f04031704030c020d0c06180503031803240a270f02060d020d0902030d050304 76
    0x145025140881d0307004c04110305004000c1c450005c3c25194003070140c500b44a0000d50b00c20032244038200080c082c0d210040342da8445003854181c00c519044405070010784846141c90b408a00901140c6010300441c00c00d41d440f40d41d5620035800640d403843e071b00d0800c7c3e9015403c0001410110760300140d0159540005280400d2440000c1201841e00120380d111030090007502c0785c0c680300405a0724010030810520120364001041107549510f0040000d104042c1c42c4100380c042d5405030341b444103203015034000c00c5501602400540600079024100c070016030f01d80a4031007a59100f20440c010240c41d01d5005403183e00c100491100d064142c507014001034400001380c880c1758048110b070b044001e810201003418043c8142491244902c5041000c00d90f10a42486500621181108101c490020ba066840c0900c0714603402981e03400261040c80400d03000c0001d03995880c0000e111a142c041c500300d01408176408030316560329841d221004c010a500d002e008200030303500c550034210303d145880c1e81c541d031480600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 110878866 1250 110877616 110877623
    0x30b04141302030705270c120106050f040f0303050910030e0a03030f0b0307080a05060f040f020603150402030907090608190f080f1812010c0509010318020315010e0a021303 76
    0x1100c803800e06643d003c1125a00500b00a00082c2120074160b94408228501d402c1d101c10008012000c10003006030001114034410345080f44d0f841907424401d003200d0a0b4404105408510018040410f842030807030078102c0210f1103912869500c11480082c446641400900030041c0340c43c083c0c55030f05c107202c042040d01c80f40f9407624001600e241c4d04264070004144050740c054141c880c0100120301c0490008420035042e002e40304482841d500c00c012060300c40d004580080800700e400c6210801810f08034083d41e0020214450042291f100d280031408a80046407130020303550010310101b142d49064841c84010b07140010103003402c25044442c0b2410403003060f800a02228055880d00f0501c0000740075264400340200741c030381c1d0f01c50383c224a9482c400381c640c403124801d40d0354140301c031141d6605200300b02160039682c481c1c50030044002c0040d801440350080c0025002c0c481a40350b40140d605124440d540c80613219003130700c554104244403a40e41c0005014080b0340388100510140000302203401400c8962 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 110880116 1250 110878866 110878891
    0xa0501021015080d020102070507090605180423071e0518040c0905150f0d0c03030f0201090c09020a080105061602040f09020603070c030206130b0604020901021509010606030b0414 79
    0x1003004076040005942e400190711340545a00800455419002440e4040c021f001311400c040d1070312400402c2712194841c440c1d020302c100c5141a60f040061550550050242104a140003554040e1035210821011442015000000709000040c0c0030050b5021700040c6208000b041810300300425607203031202c190300c00b16030004000681001240c4041e0300141c05480018020750410302d400c40c00d800c0724554560b00c20180f207045035105003810184608142e8000340340011003031071a101981c80d042e4140380c0000719501c500315140442c910b40500002004400070043c0d9031000701070000c0c4001010b0b0402c61140c0810803100c415004001c0c085400a6012500000c072000900465001003106020082d04810044208425103811010140c42640aa0280c40341c0d40c0d6080d9031081c0d4250540c0c401001001820b02140c400c0c2010350107403140d9030060040300c9410348458009850044201c60368081c41c0e441c1c000510241d0303414020011403900940c1c0034400400090241c07034034200000e01d9a101c100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 110881366 1250 110880116 110880131
    0x606060702060c10062c0f040215040e0a05010b04120314070b0c030f0f06030a0f050709060305030c01180209070c0c050a1d0f09060f0403022109010e0a05010210 71
    0x640c0c40c0119140007000704100c8440580c880f02410203005103100fa86d030101021020a4061150a40c144814180e00001d07100e583e928000c1d40b43d80340401070002ea030820820302402066100000040c8050000448800b5041c68800c050509442d41604400516803050004000461810211011050303040c1003020710000c4011202506025084002e40340c00407590601182018400c003e6000e4814020711f0400d5035500e5003817001004054640039011307408070103200701240f003000040c1c810502c10415101c280350398a06000981c0d149400c1580e07660400100464088000d2241200ca060310032401180108181c00290450a00601030410b1200c1b120f820300812940030720071005400020004000207031120301e0a222071115004121842c8600c0c00440d84c0982220101481805048020040380d43c40c605200400d20010b04100d00f54810398208a040c41107019164001002001c009503c80120b0000140720030000d0b00128002c1d0a0f100702481184d90200341c01c50411034006006c40c0c0c41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 110882616 1250 110881366 110881369
    0x11101104060c0615170d0320090609030604030306050918070303030203060f0301060303030501091a030307080708160b041a07080a05070210020c0d081b0403030f090312080103051e0606060702 84
    0x4001800c00d500201c244c2d01c20216040300b00d40c1c010007016030a03004a8000b083ca1020607400c413503826110311017840b12824600111142d0000516400f6070150100c0d0074000a0408030b454024292421000309440d40c50501c95401c095442c0d40e404548501242002e03201072800c2c42e103074502d0340406010141c00000041407070320303281c0740404140e0b006002008115564100280184401c0c01181c60142c01d00c01d03041d141802015071000c031041c004000c3c5280c003910f030361442d40d154408141102d018009003c10300c9008180610703001654000c0c10803004500c1d0a24228900d640210204c0c0b07a0401d548003400100340c1c4c4450280c5e4400500040014180c03183c1100340d2415004003e01c2e4030440c0005000030110002003404110051780b9142c05446403a8883c5496812040341402a04403100744401c002007031065034055115501400c02c0c451007034036511410a072580c029880000300c0c5ca0320004004000c0e0400a0120255210881d054103047d140301503a00c443e0090070140c442c810101c1c00d0303001d6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 110883866 1250 110882616 110882621
    0x90703031b02040e06090d0219020a09020d0b06030c0c10090302060610050c0102130510050403080a08040303060b04140922031206081903170c070605040f060c11101104060c06 77
    0x3070f500b8100f02c5181d40b801e402181c1e40d80107c0941e030001402110318001d09010780202c184406076006123a141c805090018002c001e4000c50440c42089840f682d404078030b42c45010007580961000d840350f0b551181c1e078000d81c5151015102415500c41e24104034000030981c08510950040d6080390001c24902d81054101e0303050103603070340c19285d5520000c1c2c03c0c1500c0c010034039650700302c44003514512000f81890100b07540b036002d1b07072201520302c483c00c100c24440b19104088440d802886410006820364a2b584074504541040d00440003080da40265420705140c649402544806103100d00c000200360072080f150000c0b0400f2004061214203400401c141050b41c02403409042080c0840d407032104452924140f2030b502c80c0040e0040340c0001d0782c105c003002c10114810b00c140c4200c41b5003407904034150750714801000c0c010300039101c13847d10039014000075002f03000d5080e003941e8654034141c40018400e0781c43e0900da8490044240c0030f1504102400300090b610a940880d0554100b0313000c01101030814101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 110885116 1250 110883866 110883881
    0x180a02030d05040503011b081b040305010c050a1209021e0301020f030f040b0109140115050d060801020417010605030604030e011106040b040b01090c08180f0a0b0f090703031b0204 79
    0x515004401c541806941d00001600440300704800a114002042106e800491880c408101c002104c5200003045102280003d11840c1540c54005240c035035291183c60840d41ca003099080010000200014840e48c0261005c040682400080200c11210740c0080d01d089406030442c14808050310540c0125642907041e41c84480c21010116135903c3d20841e001c088040450702105d620170041e0000ca05007034180f0905182d045405403505003a42042035a154445c1d040b0508030422208001c490510707800c0703000360401481030900140e216420001d0700031664003001c032010300d142e241034020815550b0000c1c0c05500b10303416060094900100c400121030608201104081a1042ca420b2001308040180c18a2266000f40304210362641c0354006142550550180c0c1400103111601050129250440000d04031801c50203d4010b0a0500720190030000c0c0500240c07a4568404208080c07850030b8240e9035440000c00014000ca10f003182e0340640414521401d040050000c0352064045481e150710286 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 110886366 1250 110885116 110885119
    0x10e030709050a0c02150f0406090804031203060602070b0901020304090c09080303040f020f09070f111c080901060f0501090e1e0408070219081207231b090103020108180a02 76
    0x40301d880c3c003451900241c01200c1c0200010711907100b22031003003202c1c0341c1b040740244440c1c042d030030f180d0b03c5946920024165564041da030340c00007008000001107180b101c290742592582c90116526141503000ba080001d030b076000a007580401c01031030031540c2c1d010081b40c0541d80200c07000a08904e04800c221580348494100c1502444000248410b003d094101d41c1c18181c400c03145c5405042c07000c0d041c021500b00a580180c00b01e860500050302c4580940040c104428411044400580c01074006240038046a6602c1c0046101c00052201303c0c3d20a001d00409040301a0700c20032001d20300000203003190014404d1164441035100400c0c038820b0355505410291011036091182400e060034844015807000c0400c0740b003404004c0b040b4002080089541c412100c0304405000340301e0071440c1060072544280c4c400c55401100351510b99600342100031903000603d5820081c0f800200c5a0711004090140070313226845801c80d07000400040c1c1e801001030780d211200d01c0100040304c000100c000d1922004100c001e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 110887616 1250 110886366 110886371
    0x9030403150603140f07090b0f09180d0e090105030604170f0708030a050105120115090c020c1008040b180a02040b01030915150506040b0334200c0a0302010e030709 72
    0x2940000700007448041245c451815165840ea50340f00c0f8008440010400c0350f04004049070034501464601c28040d80607192012423030403003400c00ca44609008010000401141c2410754100d182d04088544034054001600101400d04143c0c445880743d00ba200d82310740910f00c0000e0640c3c0044250b4064822082d0701c80281a00ea0038048400409480709025241c010010b0180c8400c0e00c00d4140a540581211012070390641814256000090b00b880740c812410b5104020428a8a46039000340c042d254a040d07803018014207040c607101540c280c0c09816140f0049900028021014000c40c10381405541101e00040309495000164094403a500000d04042c429540060040344260003c0300101c4601e120711082c1c43d110803c200b803a006900818a81e50010b0002420125021444402204200d00c2c400c0b403481c001d400d02e40060a44502800002e080320014420604522500e000d22040c51070280003604000c0020455005071448003904000f10805488955181400081d01034400c00209 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 110888866 1250 110887616 110887643
    0x605031f05180d0203030a0f090b0412180b04060305070c0302070509070c05010c11240a090812090a0c0609033207060507020f180c070201020c0d03030b03070e09030403150603 77
    0x40c2d100d4008543c001da4948c107101014007040d1262082c00040d03944100512225110364482c10f010410130300441c0207100b035900c1c440c00f80d0040e0201680040c00c2c01c641480e6180d0800c0030040644002406100c00e004040040400198002c103000742910800e4410700e0f03050303030340b004100e400101a4102900952801c184005500d920240c11041a0480400c640799000c01e04610041500c0c0c4581d507080b01c0400d0b101190042803035402c00c101c002c0c001e900302c9090030040e0051441023041903860703980561000c03c565041002a031282002041a07091540e0040d2440d210302106d0144143c0a000f52013452003103140031080b52000c060090342c80003c0303500c030a0315802d015015900584080e441401d8022040d4214509000a100e00e101e00c0c804550301c50721112440c50340c40d001000200c0c1580209260700c92191620002062200d01039034000c00c0b2551003009160a142e01500021441c980c031a0402c0707035a480000442d0110390340280802031070301c0c4070b1185000174006a00014003a03900da420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 110890116 1250 110888866 110888893
    0x14010b0a111e0d0807050408031b010f0507050301030c080606090105090702010f1503060f0203060a060c0507082a01080c031501090302030a0c0f0806060d080a0e0406090204090605031f0518 83
    0x681d0446400d0303a86134100380b61520301040da460f005611421641d0b500c100648020822203005401c0e08100000001c18454841c1640b0410303610304a4a450010341d020004005100b036030b80892004040c41d0010f000d03a42018404100418014003a1318011540b647c082030010780b00354404000c5002c06141000f03d410741404061103650144000d407032060901c07004030304803c0548201d90040400400181e00ba40c42d01c142543d205017140d0741070303400e03000d0003038001001c503810b210240c90340c00007000084c01409100004a01e034807031903039440c2c10085158104451503d0b21030491380c100035004c1948c68a0244600100c4550080350070003505402840b078003208000040e1000700660f544071078904111900c8103265550b400d411a40d05900c030312802044000320322a08000c0c81d1540e074034034122a46008150100303040e1111503001c0740c241c40c0e0028040001203035501c595000b5190840192001c24840070400d00da9500d0b100c42240c1c0103a4801c0480c9519120403601803c4a186c0c4050b40c000171240714 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 110891366 1250 110890116 110890123
    0x23180103050c0f040e15040f12030c09171b040e1f05010503061b0a05090607050c150708040e0901180305070c14031b0114040807050414010b0a111e 65
    0x1041402290403d5040c1c409240c0350060b0984c41e10078400412405010820620800784040c00039505002c01105440c0420140c114061400c05070751004240400c4070300c0c0c0103080825a40c000754140c0040e003d41d2a45900c0883c03030059050325240070b20600c0d00e07243c00190040c410040f44107068848c051064645080fa41008843c00c801040c0c2000141ea0750014181c81c1c03203044850070044d8000c51111000481c94102030501101c1602c4c01d41e040c1849400424542d0f804100b09540b960711a203070040d114076240441c03059071080500b5450506002d03aa0b003060728001c41c000c2d501c002220b18001121290254004160a040c8291818140801c1c0c203002d000381d40410820f0310075002080d03010440810302224924520405402000c2e110580c180b040c00e4400740700f10550400030104c0d41201041640030250002c1c0503950090401c2602e0b26007080100c03410820701a82c81d0410100400c800c0b100002500d181140d94103010424480c1c0001050400c0c440515200000a080080120105001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 110892616 1250 110891366 110891383
    0x80412061d1603060203070c0f14010e0d1d0301020f0f0d05010f1d0601020f0715020105060a06050703050c16090b0f0d02030309120708342318010305 66
    0xd1007008182a0440990761215103100851041c0a442d5008000003141130340115801840f03441e0003445c41d0070303135500c0100c4806105416507850710184840118a030f401c1c442d031205030705c1100c018625910f2a036009081e40d5035080b42200b42c07800c0780c116003c0c940c9081d0101e580240510a40f40ea40311160440802e1a400909556020310729003400400c0d80d4440b4403a88040d03800e50f0b40403401602c1d51768000781d10303e000100f483c0c2c1103000e0400c140201210420404000d044500f988407801001d8190081c00c48900070b00f12440764800fa0310400c41c0a40180c00c803003e8640515103140d681c2d6444502614081c2103804c2d03a600c9912000002a41c40d074680c4c014036400c0c1040b81c18003444a44541007100300040c19401035891707001005021746600d0440d0308541da030060a02a100c4050340d8241c221305244518505c281c0701302c9102c0d2001048404a051240920303017800742e0440c041d04014252000d05400445041a21038203229040c031039032218200c842c101e419200c4c058183da100e150203616907841 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 110893866 1250 110892616 110892641
    0x50102040b0a110c0a090902040b030616031406090105010c080408030307020a02010f020114010b0c1f0b010215090d08070302040302030d090302040b01170f0403140304030c0c0504091e08041206 85
    0x203261019043c040401c000300704100080c02540d015040ca1007604c020403c0d440c04030780c003a6440364442415102444080d2140380120760544034510b074200e0190948074004550b04903a0701c103804014035640c403a0001c4d07055230b4081c40c1101d182045450019580d10031504803410501c03020003002005c0d640007500346001c6100b030342d4840c02c04440380c00603426640b45070110407003103150310010700c0003020740000342020750b10702402c8441c1b9500054203001d151201c201e500704503603144c09000c5c10340c2d42c042080d54406a6031422181c094500601140d490f0513407400030301e007042006004555028400c0d01610017843e0001d00b643d880815072a000703899040c2e2444100d01960501c9040c21941d03005106400c2100381c980000c642d030ba51500b03241c0c2446400280100c080c800f050040380c41031501c40b00903520952080d2228907170381545041501c80e207000ea51215108e10b0030084100d0001c0c48061013068061800342c2041401c40e004d2400080d1800707942c100201c075400344c204401c20b201c41500002c08c030820 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 110895116 1250 110893866 110893877
    0xc12010b03181b10110309040b01020705060f030610090602030f070c03020a1d01090510050936060c030c0403060b0a03020301050a1a0d0308061005040302040203010b030708151c0203010603050102040b0a 89
    0x161294151613010005c10541d465800500203504141425001245110030510580720040c0d140c41c005185a00100082180c10a000c0100903c41c10032000385503080c0700c0d5041241c030151070140025a0b074403401c500c0445243c0080303108800c001007006880003a6a006002c0d6851645035002080c001c200726410614000f0004000203e486141c0718250180c0e82c441280c03042c40b81440203002c4403030406031584800805490001c0941000c21700e043c45004c7d07008100301403907100b1151640c80e224018111141c0d8040400a0001c403505000c01c07141180d9202c00c02262882440b80003e030758044550010b9019400c08003000300410090740310f41962400d40480c2d400740845c4000b4042400e21140000b0040f59011020901030300d013480d0f0840002103c0d1070020315040d140c1c2e0100d4280d030000e902819030400044103004460f600b00751120b07803107103000044940022103d4001403002409081e02135090354919410003c0d07403002c0d0424000307903402c08000d41d80e482c0d0700c00648000d036020101c400b00050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 110896366 1250 110895116 110895139
    0x60b090703050c090103021b01021911070501080a090f02030f01020c150f0106031e0212100608040f02090c0c070f1502030403080405010e0d14070e0c12010b03181b 72
    0x10700034800d80e070150902000305428008600019002940692500070400d103008010400c3c06409000a00140148034004001c20481c40000340580d21441000c8a054200100601060b64484500e40e0b0140c1c014a01245074009401c052482418001000e5050f0142c80d4201440040c150020f0030305404040880312407803c3c84c24100e40000007036440491a00004004121141c481e40200035502190910945100000c500a000320791040c00b0b40d03001000d13803600700444403461494400040c101800d0200c1c8620385980c5250f82c100c440301000b48540016404540105075802c10707109031101010448030302c0c2d07440303c4a58640b01003511511b00046030341d000d4008110301c00f209540480303031701168003170070300e400c08006403040d010415003290442c21113819640810555112524034215500151034458184440500c4a4100400701c05011304c00300544401c0c00718100c2030368111140f01000c16220b4071014141d803001002601400100d125014400301056a0140c0c540e207001400c450200140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 110897616 1250 110896366 110896381
    0x11d0d110906010504030201050904050916030c0e0105010305190f02040906080f0c03030c06010312140a030f050105010513030b060f1012050f0f070f090e070f021002070f02060d18060b09 82
    0x85c451400001c1c0091003d00c0480002d05290b00140d822066a405480040d85107506076000210346601c103070b5410b034a08008200d44102c071002035014020030300e01800940340c080050140c5091101c28000d03010740c4d41080210310042c650545019000c00310f400e004c1c040c0da13400300e69a01c0c01000038804803401450152100c1e440d0000c211013030741c480c0340090b1155038a10b8840c10b12255110880314144035407000a0780010b0300784802803010090360303180000c0404c0c0c0d20800108942c0141c010505101c0c0401000900d1009101f1000460340c3c0f10b00031715400e5a1700740100e42500036400342980c1011801819444068200400701c0503005110303000c1025544041c178900a036a03007940d507910640d042c2408600150321440100c1c003034510904000d0116030740e0f6232a100311420221103540004680500c1d500c1400d606115081e001c0d200680d003941010b00303513202ca0214500c502d1000b8414400052061000001d035003142c1a82e0880f18011401d295103802c0110160403c032441d1403140c2d020701c0014008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 110898866 1250 110897616 110897627
    0xc06070f150e100e1b060a140313050606030a03022d0109030c022b0204020318100b1314130c080105040f1703100b090f03010509030a1106090c011d0d11090601 70
    0x603c0d20358248030001e16920070071b0115560208038800104403412a00921490740e540c01940286020001a84481541e003031050410001901042c440c1d0000d60301c401c0829800501c250030480b0182240c603082c85030052845802000c030641030300e80d501703000596007403517003001c03001d03034031600942d110301c5400700540718101c00c42c01400240000c0c03581c018504002d801c1981c003030365114000c652040b80d01c4c0d803406001407403c1007074224040c01c540c940030000280d0918401e8160800c9a0f2201441888130160039406c01110040a40302400b00b100220720070f004941c3d6200b801001c00304020040340c18141410562142e2145003580c58455552072004058415401c80b4880e405440c0c40100541c14100729201c640d02c00d400c01640490101101c440c0d0703540038498140111481c8008560b1541c08030000351040c0702550382074449410003400c012401c8008500f800740c0f0f4600740382c00410054146074a5400e1700140c1011504036035070b0645181045940405030308500021a880d40c1c96a0300c4c9801100d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 110900116 1250 110898866 110898883
    0x3020307120501200409021602090f0a06060c0804030204050601020c10051305010e0108070806040209030708010b04050a05010609030b07050d0e0105060a050303040f03030c051903050703110c06070f150e100e 91
    0x4c072407080000b08000b450a41c0680141801140a6a203000d41d940025802e24010b8607e485514503600a00c1060382440c41508020802c0381824016050b6036100c481070b60080340b101a00460321840020709580c402e0203c1c0e14200c0008280f06141009480000c0194005080324442c6500d400380102d40d81d8040d94040b54081c0059482422030b81d1510802c464100001c1c0410f50000c1d001d122140300350742c09201c20030251203007030000691980c030401040140c4102030000e0705ca0311324040040c880c055202c0c0042c0c05480d00604000220386030000e086441d0f1140208818110b0b14003503994031100c4040d004103000f00411100075448544900030541c90f44118454200007030fa1102d0f01f040040d008a008d000c005004001341c07584211241482211700c2e1500c0403c80016a0000d040005c040d0885801d13801d1114000080c01101d0001020038007a1280c0400a01041040c1c2c1031501000001748201e0703405850803e090120540e0a06081c0d9204400048000d1441c200300040c110f04c0700000c0d5603c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 110901366 1250 110900116 110900171
    0x717030304080f0a0207032f0f030d05031503031317120406140903010f06030b0a020901020615040e0d0e030d0212040311060705011109040609051b031003020307120501 74
    0x34940b00351200c81c2c445644c082c2c8210420b5005448001010440300c1c0c0004070555229842c0343c4402500401c2c0c0b8803440c0400100358415074402d1240c15088d103000130107105801150030029600d4031103042050440300d03d07907042075044c44009406180d001d04006460100d030005101c403d000b00300050402d444601d5a4110325010701d0030700040107410b00c601c4803c006502c65220480c81c01c1c4a44001c24255040d100200c1207807030f02c2cac09007041008141d400086d405070a800d03003142410507010000307442d41d0000e00b1246240040c0d2807102525503c41d4091481d03100f8044c2140c0c0043d841e4500900808256607009220340a002103442105001164017018404a01da240386031504550302d04a590b1400705980350080c00038050314000480034445d0b034010408290407180c444045a0810050b20800d270040b0841078107000c203203d407940d00c450f40100c8844107614256142da540c60000c1400450aa00280d41840b42140000d03060700e1400244003641e0284000f4402c60703600d0751120250f41c3c102c100701c070f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 110902616 1250 110901366 110901383
    0xb06090426040902070602121311060a140307030e060601021b1002031312050c010c0b04020103110f07080316090602060f0901110a0e010305010519090f0204090207050717030304 78
    0x11001c960550040c000d00c12244607405007460789405900040360001c00301202d009500041c005480078005024a40c4817030031040c1032a4884a0303a42e0381c240052009407a6000b940d000ca10440054000d58004178085107030f03180542c80740340c2050010007800940381d140c801c0c1e00403800411300d40e51010850781c1c2c9401c072650060f00b4107090700c5c00340800094121599400c501050011000003030140703510070010709074410145906407070340c1007490900e54040c902074107200301c030040c9100044a20120541c065024200001c43c0d4003c2c0259544a1044030080b08807110001917410400040c00003442c01140102421510b034040c0203030580d4901080c0c05402c02581c4020b000400101a6415841c0d000c1c20050020610851401b0340340c050307400000280c80403c13034a030600803442d41d148c8141401041c048500c0e5524215002c40c40e04180780900410341d10030340355507900c0e00b80c244a8040710000c20f00000700710b6441e825410040d49802c141d0148580c40c42030064065180240041540e0195030424180c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 110903866 1250 110902616 110902643
    0x30d05010609120b060d020604060807270905090a0204050c040609090605030715020124030209150f2106041a0f190207020d050d120b0a0803070f030207030b010807030b060904 77
    0x80e105a09001420b846d80310680d11038401c01030b00d4042c040c1c8000c3c0035545569945051020003d000002c80954070450a290030404004070100d9001030021100703002c00c002081d45800d1141810701c03269031301c0a90018180024000107005070801031080307079103030350b9044900b60315450f844080e0b44041c4140c1da410f610014090201644c1c14240c0400306043e0300001070b44a000700d1404543d502084003815004400000400030360a203016503035401600090754030342500c2c0420000346000c034208a80d501a9601d031142044038010740c40c40c159010450401c550061400780f03080201080021004000040c80700c0214401054003100da501400144411150490303e010840c0d0080d040b50b03c059901918260840011501c00d000000da400125070720002c5d010100104035055840e6000f8203402021403442c10402c001d404019032301069880075541c801d80841e81800c0f480c0080b01e03000600328500c00380c00007410309030005940c030840e0f00c030b03e031500c90550ba07540c2041b000d010111070143c0010503000c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 110905116 1250 110903866 110903873
    0x60f030c09060621040818030307050d05030910020301080a0611070b1515071a06030f060c07080c060106050d050c0306010c111c050102040e10031a07020717030d0501060912 76
    0x589181d001141300b0b80340c01031030550204441c0c08161801e0b512101c0004030310740c007500d041090700301000d4164019490281ea07a0340c4c090b81e650480004008010010020070107146e01400a0030904601c2842991603586410b8180d0311a070703001900329681d5190490480e07031440303510190380d40301c0d4001d02502c0d0745949140303116030f50201c0c14110340e600602d6004005a090f140710042c040b660f000d00f40d14444214091030f40c10800c0c80c00341410348654050070290400c0180052425884008080c40035140c111904e8a44a50f008200800940d401440004201d050b80080a40000b000b00c05040c000d5460300c0e401540144000d40d84c140c0000c0c940d00418000c101c100704441000072010f0040040c148906101a8003000310300021070340c90b50001410040c01d18145411758008003040c2e01205081e2845c0d448105001a4140e10712000c44410000341c80382d80280b2124004010071401c03c1c1c606140c24840741c0c0c41c0e90040100203001c2e03141c03900200d007552140d410070042e11007817040c001d0401c2c59602c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 110906366 1250 110905116 110905129
    0xe03012c0f0d0302090a03150902040e010501120609020402040306050403180f120206090a03080d0204051806101101241805091b210303010e011e03020d11030a030503060f030c0906 79
    0x10780e2940010150000100055201440b04023030442038100003030112003841000262003a60300056950b0381000014032440d600002d102c40d030b50740c0c80480094042c20b43e1010601a01840e440540001c7c508005c101c14150011011401056011036420980340c4034110b0502e458040d01401c141032402840c0a40182040401400d280c0d00c000c1205820a94035526540e0950009e031710a40f040303801282c00c00c07547c01c211a07295410040410002002d20b00100881d6504210700028410020804500643c850702940030088250003500100604031030080e401c4013480300d500c640d190700916206400b107903095500c2100e004140701000380c0941b00c12203200c91a01d20346031460960000c44524801c61141155205005030712240d005144c50790716000c022048a00305a00c01488410841d0a48555484103400d0406896040b69041e9103840c0ca4107244030026920101d064051041c0c600303010905400c42d001c1c502c150002c070384051000c4100800d054460562600182d00440810041046407a041c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 110907616 1250 110906366 110906377
    0x17011202060313120e0102010c0219030305060d050607020607090501020606030c012003070609060c0503131b050310050906060f0d1101030209100302090a050a0e04120e03012c0f0d0302 81
    0xc0039880c52803401900c804c01c000700c0c900c42071070216205a1122441e03580a0103089951079803070000c0c218070000e15100803401d5146400080030150344800040342c40e51401e829050958220084802c03510301104040d650f01400d54031700e0045907003440f00090641c400280f081c8141c1000d13001d01a400302c94001507500d03004c405480c1d50003107850145121604405c0029062090040c00041201c3c010b9003460011254503921401c1089410000c1000100003215460700c0c1c0c90b44902020402051064036a12080c140d0b0030540c0d050040358040800c5010b180c20241c054442482640c1a5483c2c3c81c1c00c100d80384040010442d000000200b107007011600c05020404000d8045c1809490702d0b00b078100181c61905140491400f080d80402e03495510304010a00e0302c05444103580090005007448030006010600038801021b034208151040c0d41d03281b01d401500035030b00d0080c000340000c4415010503142481c921000d03d07840b5000c03100d10010027800080c1d0400080702301029001d007641304102140a036000e3f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 110908866 1250 110907616 110907631
    0x90d0c0c08010915050108010506030604080f0d020d09060606080912160203030c0a140102160f03030b13270b16020a170a03150b0409150e0a020406170112020603 71
    0x114480040d03000070030b0048940613403040d0b00c0141d1464a14652030204d40040c0c00014003a803404040003180c1d140000e140ba0850780208820362030b04006031100c1050b00c281a0101c1c50351380080b94101d03600718075401000c9198031415082c0a415201d1a04540045040301c1c9111241c2c4900300103046040201c0082c41460404002e0300c540d040e058012901c5c50340301d80070707e040316800090b8005c00c1c4400c24a54074003201940c80290300e4130785c1003a007207188841001406041078841400d050200750003548030000404018161990856407801d5250060519882d020103814510814445481c0e065085120460b07120904941c40e071a03495070503084c03654804040781940b099030504804a003100d00143c1010064034600c50361764071351030001030944511242840c0900f131069024400c00c4029010b65007a980c0c82030001456001d0011000b08000b515401106030702c1c0c00f0000d014881d250354000b0b006546c2661106032641c04841e0302c040403036100b40b1800c080410420781e83d1005242c108015500600e6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 110910116 1250 110908866 110908883
    0x4060c0c030c0803030708100605070803150d05011a0102060c0f0c0a08030c03271203100306090b06010806150906070204020904140f0c040303090909081603080a14090d0c 75
    0x21660345028100010f80c00c0f100596001108000005611620f010360009501d018080d080e4a444009482c41c0170f8440001c0c44c1d00c1e4080001351308154810300b0506444c80003042c071034207842c5509015000300040f448040080000350391100455000045841c007404445201c54540b02c0c0c100000c0384036030001103500049014028807034000c11080c03006113005040c1042200d950b0300341210b0251113003610225503040b6400762146031403d4030000c01d2301180c10131a180c2c4959a9500d007045030031480d02c2604001c100602c1c112484c0c060055500e402403240f102a21015142d403078a01c00c0250125110140340c0d0050300030440e01005040000144c01c10b9031000c0c0001d801c000d482000901612440319400310246481810000d0401582d240c81d50080600b4030002d140c9803c0d514014040302d814020038840c3d545980c0e1103010801c03000c013100c40306602006c01e5888101540b42c001d00040c0c042e80d000e000d2034140321100ea90344059802040c000e1412900a0210328821030b010b0b81d000101e14002d60f00e0302d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 110911366 1250 110910116 110910119
    0x1202030c0303060d0609050a1b0905060d0b0907121b050109051012020405060c010903030c110c010c02240307030b06040f050f04151d0f090d051605011503030e0d020604060c0c 77
    0x40c010804030540714480c07007100301c00c40344505095840b01c005a01c84207401e810140cd0020303d88032019441056a000414031119513642d401140c541542ca50100342901806650741003404558194441c0c440a81100311001c0c075a250011207004015001352039008200d200f1102145001d010801c1041400441c050f007003a80d51800501150421514a41d0366511808000109075141c461001800d80c1410010540011001e507030766076805081410381401805805101503640303086420050782036020183d1f5031012410743d140301da60002d4516001081c03c1c07101d1003c003894441c05840030f076003181e0b403600545131816041251385801924410f8200359503000d0140c0c021066900000504100c900c600001504103604812004000341a403040103203002c203000100d4000720341c8128500345464016102c00d08608100c000781c90715030f0024025860301404401c0881107407401c604072802602c0da490359405070341c02c0c00042840024003d50141c41000144a220301402c1030001c81c500580e074034002d06 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 110912616 1250 110911366 110911373
    0x50405030f0a17161101050c09060a110303040812130209150112090b06010210020f030c03090f010c0c0c0905071e050c0307200a0609050105071109131202030c0303060d0609 76
    0x50740141c1302c00000310305a0b001d42c400c180d0042c507000e07040112140200254580080300c0010783c06000b40c0d5074460000020140d120512078540201036050000c2a00e50345e042c0361901c4445540400f168040300004880090300c080d00014407030300016005054014140d80c0d0b80d20780780300c6203020544e8030305000c4505080c00f1200b0b000d10803091b01c03521403018801c003820942c001900d002c40d2529407603542c500400c820340300c903d0740c1003c0d80d41061840c040c2c9d980f00d40b2071107681c0d4103164511030361100b550318000c090280039a110004040c52400341c1c078410042c0740c42d410000140c940031109070000c00c0c0142034017809208030008045024607249044c0d81800c00403108a030665118981c140e844900240b00a0401c2044040300754000400301c1e160344140f860007002400140e400c0c403400c0d05006021604d130050140e50ba50f18801d40030300600d044030520b840841c0515000707407170000703646c000300940c481610b090001040380c104c040002d00650a541c4c40508119822100c0901143c41a4540c840324000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 110913866 1250 110912616 110912657
    0x30b18040b0901060b0a12050901060b071101030b10020607080403020709060b0c0111130b0d090c06110c031614120d050711040c090603021602060c010f0609050405030f0a 75
    0x994401d081e66401d0b400e04000352400d5464641112290280030031020304020303040640c50016002009004c01c0ea03559101c3c206006101c0c41d07100e0000148005440e00030458030a0b03190b0344011007600d041001c0d5030314009020300380300c4480909000d6030125000c2441d203400b50410f254401c0c030a204907502c01d52503c60890036a09198000e031000740010812001508083c0606802c00d41d60b000500e0500b0f403100103103408500365100d440005200040c1410351000180c01a660701d80c0c11100c103d01040d95031000400c150300741280e0202e14001d1012117000c0f450082125520091100c40c82d0041c14240060260b001480c03043c46644581d007600080e400500901c000084910b6a450300c6880356190f0070300c104014262418544590300c5c0c44040060305d07170056025019200e01c3d140040c0c6940305520704c413010540429002c1e60201020861140c40348c0150030207550030311b0341c5606100701139a82013014240e843c2a94000c280380c205202250007015184080c0c034004186190070745940086a102842 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 110915116 1250 110913866 110913871
    0x90f06020c0c1237030f05070503130e070804021003020c1005150a0b040602030a110307151a0405150906062503080c090a090b06040503010203010b0c060106020706020d030b18 77
    0x42078000369089078100c041d00030502c4c20050300b40200b8820101c1850741075010403c0341401420701c500c0346200d10407184100d003607984c613a07446000c8a598a514126013001040c440c130840c42425407180005460501c03d03c04140147e6003d02003021150348804160060741001035000e0072882034180e5440007180318080c80b40182c3c80ea006140c03182c0b004506000b1420340e0b9070099000b0401c10801001803d0b40081290310901c40c5281c8003000445071601e2504611400c0c1c00640152011803c201507414140e222140000c046180c0989444100c414001038480880e420800002c0851010025042104150b0b6216400600c0720b4580b400814501011040401e0345801081c2900202d104164100340308541180541c0f40d0907042c2491000003d1f1180020b0050424581e150000b1030481e40300c030020356015010040c000d54a03980c480420200c1c541203004841550301c00c940000482900206191007030324189e9000d4948403080030400d0b80505480d5100680040d07504502e03801088808203941d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 110916366 1250 110915116 110915149
    0xf0f2a11040513080d0506060706020304150606020703030215060a0510030912080609060d080408030406020c030706090501050d0e030702061b0c04050c07030c050f0a0c06080a090f06020c0c 83
    0xa0005034802408101d4400410954022444980800101d001042500d80d800c091620100316580c0382004a0750342c1c01055030040082d400401408104601344a104210701070340607080190503940d90040740c0d10f413924880500549c01810b080304014a80c006e0700c03944400081c080c4a00540d4510206200c034244001e0b907070020399200845020080c1e19040d81d803030f21100380381000300d030300340700c400204c0d44000600b0051140c0708030544042003000c1e44094a004040d80308c2070300d07115070740c80ea00603460740304104607070b4401e0240390400300e00d00e030150034a20705844044e51000d040481ca000454001c090342550a00181b0003881003800683e40c00b0018034080d022000e101080352020400d07145030503070700d400351417055003044204041010401c040da01c8850701b500e02254043d065007000ca0401d012945e185e02d83c0d0044131764a038113010303018035241c003100d61594414103907030b0b210f540b802c080310303403822000b0901000150b0300c0001c14880d4000d060825041c4007607501c03030300c115400941c10321140c6da00003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 110917616 1250 110916366 110916383
    0x30070f2a08030103030e0612061002010f0c090e0906220302030c030708180307150c03050403060c0905030f03040834030b0105030705040b0f040c090b0a0206160f0f2a 73
    0x1841055801403001281b000240c0307584d800c00654609006422500801003800740d0700c41035801510b68130035081617200f076511160030400740700d03120401054140f15020304803000c415400170034040d41c00015618442c5500c000c00c08804520340c180e00c0d20007040c00d5816407c40c4814410f07aa130030481840108440d9105150b01559032607428542440c0d81d2140902c00d1003a00110f07010040400b469002045003e1039180800203440d0364981501c49008541001e05000d00c0c10f006100c00c140c1010840301540d4040b021a00350140c4098400e5480c480c034011007019801202c1510300050101c152400b64800c01803030602c2950f2209139601d48060f5651098800c0e50348030f401008141828050f050180c141030303501303010900c1d0f008045a40b64801140081c002c0d0799402ca2800428031a03407016004d00010b2606075590514003c00a44c0e032023060b00c1139031602c000d000140076602d00560301c10740e80d10401e03110036040c0c08800109541e050104111605240a8864481e0031803407a002030071807552140111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 110918866 1250 110917616 110917619
    0xc0108060d02010e100c150504140613020906150a031a030106030203071701060329070f0f03050a0b030d030f0608030307051602130230070f2a080301 66
    0x140019400350155005988103000d00700542d03804074180c01c8408042e160005000043d07142215048149440a4080702456200300b074000060b412090141e802422042040c0d412250303040d4076140195505604641c00c013020364014203000551541c0910000c040c004969495060b02c0003541c03016810800007591800a256903062079807000700d4401c820303402082801e05550101e581c560803070007940d0b0a4803444405404044013508080040d6a020042c405d00a400c0503251800d1f000c02d8200000b800300160010340c4040c480e40030f203103c0b0100751759003805004c0c0500040d8000e100103805510150b0b181e19074911540c42c2000424800142075400041d5201c14501d41d1085411a400c50070f40341e00100f0a00c040a580001503402c6040031a00580210026100040c0b45285060b0301e600860700101d00c0e01a44540085540a200c1d8603c2c150100603800540300310203a00100c5001000c50001c4400620080c4074002132044055038611a10f00c00403c0c185d5000580c003d6142158480d400100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 110920116 1250 110918866 110918869
    0x10060801090c0609060905150d0c1205060409080414010905030106060203090a0b090109170708010515040e0a020102030322020a080703121e080c0909010b090f0303030f0601080702030f04080c 84
    0xc403000070019813409400807420800000c080110603c112440703001b8101c1d401403400f065900301c48096a1141e4100002612804040c04116001c1002d000c140d20f0880051110b040500030741c8081c59100b4000d901c1c05081070082210320200454141c104101d800021a088d10244500400342c18a600159201c206000c10805207001540240301080d20a03c4040500d076042580082620740c1464152002175103803d00c00d02d00340c0340d039000344500d40c00c003028401d0514148072607465921041e41e007402010444040c1c0c03503907101c5411000380144c1c13003080007400a0040311003c03021503e03460702c0c0040305071160300001c412095582240000e500301c0c41c010800c1061002c6042850101400c0039490442208070b851034101c03c000203082803050703142c0052030703110581c0300700c9402c241d008041c000c440d61103004e078140540182a00c103020b0b682100503040300c0e01d000030550b403080c0b08100e16142c00365503000046441c25070107022041036100500135514074141d1400a007015200107002070800c00d1a020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 110921366 1250 110920116 110920133
    0x408040512010213050d03180b040510051204020121020d052a04090c09090213030c08011a0d0201110604120318020303072010020f07060504050916021006080109 71
    0x210818001e078410070a850078401380c454010111041211065208003142c01d09680c1e05030341c0400900009824000400c1d4051040060000e031007013035503401c188064015069545104024082d000348005200142c0150701c16403241d01c0c903605031074030401004a451702030030590300403044200409895904016080808c80754040312210050000007c0c6440b07240c070154070f071007213014000d192a20340221450700c078000c00103100200a080e508540e155021501114040c4580c00226924241d032107000030715040500400b481701c000001c2d0001130013041810001c003911644c03401c9041c00b5210310710a20701c0d41c0510907288100d014803411401c00500407401012030b08004080450200c03003d000d01c001d40c4000040e907140c41e5100f0360700e0b01d00c02c80f6820140758044880b105c180d807110b01d000443c943e2a502041c62240c0c40140011103114984501042d0b9850040c0d0082540002c0041c00040d0f8685201d90305880182d80c50040e161034080c00002c1d80142c8a40f90440107803a0344515420003000311a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 110922616 1250 110921366 110921389
    0x120809150f03130501090c030f02100e0307061b1e0510090b040b0601020708120a200c090c07020a0306020a020f0f30120f010b070c05100c0b04080405 66
    0xa080901d4001c100c0001249030001902c0444040040350303480082040943c030000100c1d4108440959032a500d1400540840c107100080780a01d425440403201580030755000300310b6100080c043d118881c1044400c5415180204084c0210700b09188640301051b1180065001082a0000000e0349000c50902038500402e00c0f521f02140c0f0308e4480b0078004102e003410700503006503000c041c400403038880c0c01c0100d01d890b101340c20003040c0e030184814519443e400a0014039103819079443e0a61030803650403a00030815130300ca41d55101a080b0030802401464985a0f042d406580040410b0418000d50042000e45465402c2102c21950020b443d090881c6c040040d00b2440080780b0060520803d41d421143d00d0301d07046a008042d100c0e11489004041940c560145604101c1000c6c0f2a03c8080c900410519414203682c0cbd004240580e40002c619424168201c079103643d00000c140ba101ea07e844240142c06041c0c048003006c100d4032140900004100a801078086c40c01004184e0302e9505100410101e40f101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 110923866 1250 110922616 110922649
    0x1902010905070602030702180a0f14060307090509030d110f0a030603020913240209090906060405011505190903120c0b130f0204090f0203030a0810090c020309040507020106120809 79
    0x1b40010001695649070f001c07140c0450400039001c41d01c170410100040d02c030224410510900302504103122060303000b02c6501ca89000c504030381c091a62420700d80111602030350502e032160001c00070851210095002710140c1c580c0101802e00e8510402c002d1304035900640b10010029860350000c209620b001c52000f80c00a000c100701006500c034690f00c0c0c40700081e001185401380b40420108011100c4079034140c540c440c0d070180400800f031074205010f54450004560151080b8941000429503464101031440104034984801d1310700114001c09040c4441c4120785035003000784050000c40003400c0b80d2800c0389418560f80b1248242079051500300c40a1100400d0205140c0c0410140c50100301c4520500b58450b03019940003a11070300d070f410650741040070044043d41500c40081c50a4000303502c4561284039034904280b940d01c2c07580390a0a5000d89000b84110703030060f40144070340c403024607265002640100312800001a0a55140910f2400307025004044d2007811002c100c000c1c2c203080c81c01d000c40ca840c44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 110925116 1250 110923866 110923873
    0xf0705030702060a0e010b060f09090c030103050a062705010509070509070c080702280603050606030f012d08010606090b040602060403050f1204060603030f0c05061302061902010905070602 83
    0x800c00750095071090010701e41e40c1c0240c0c444c0c02c0c80b140e550f8203502542d4441c8000d44220b5031042410540c0f001c40e0710640c0102e00071400400024840e12084003a00d06991f802000303440810855240c0d14060032210b9600c0c0501c2c42c0c40101c8050320102080500c451611910001c602442c0c40e940c02c604003a0316500040c003892031a020030041c15880003a80780c8060340007400c0d686071799003030002c9031741c40c14001d40d00100800c4159116154100700c0c00c4c076600702d0b40c00b0754041c005070791062b06204240c0416070781950040502001400a44050858104e0841c4c25000d10000045043e401c042c2c460070030f501481e8180d41d84d02c400e101540e40620701002418801e11300529207450410008d580310030081000d0f04010f4041600542d8030001c004481b040c128003c41c4035003d00300360030024014038951000301c000c01c034040c64000845019804600304150460007504030b654418982041d07100d06650200d90014040010426003100da415031582c80c503160340002a8150503103401e41c5011070b26000441590f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 110926366 1250 110925116 110925121
    0x6010905090c240c0106090911030f0102070b1315150603060e060a030303020a0210020406050406030b04050f0a0b01020a080c151b0a03090303020d020703022d060a0203040f0c0e0f070503 82
    0x124402d40c502c9224040d0f0203055502d0201080c002d004020a80141e4030300ca003000b18440911810a0071030b40300010440c162404010040441401c0348205140140314038032032400503c44807010300494400d01d0080c07e0b0081d8050034080c2d0f0400311036008803544c45020040d1400e000300b0782e01d4070501001d0302e06280c044c040d0781050400101a401030f0320008080680010b00007040301c3c801e11202d03074000c210550941d2140e403140300190803508540902400203191407032103002c074901801818015060540208040c0e10364003081c01c0500710003a48a419486401000b00004200d1b0000b884070400c004060a0468503c07440c7e800510302c0a8050149141e550300082895190a4200c6022401900f000039800c0c4081c60190040c0c01000c2040c0c1c0100c0c8041103c0081c1600031410a0400490075003240240b440100b1000103841400c0b9aa07a041e4000702c0002d80d040c04c154025900140661103440d0360043d20707920784d4448802900511841880c410510000f07500304000140c1154003170510b40d0851 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 110927616 1250 110926366 110926399
    0x605090d030207170d060509010605070b0a0902010f030e24040c060309021810030b07080f0718060e0a0e0106050a0f0305070c020d02011202031305070e0c030112060e06010905090c 79
    0x82c03a085134800121003000822000e07030f004c541d00c0200104400381c0301440a43c0d655602602ea5005080d0076614400b0a0300002c1c25540503124000c1e115034161944011880c491104800621082e036000c1c03041d00c500f40e03050158018400c1034044400d901d00c01d05050f482c0030b1404545a010720303407006041c91304250502d401030b61440c10080c0381d400480103114480d43d41c889009446449607001501c04120642880405580b100009110703415001c1d1f903003110b849660080306d001c0c1d144034450020b0132071402c090050b1803143d000c1030520200104200d03212900d40580c007101c680c00fa445a0f0110303500080013524160082e40c0d0703103014809401c04000c58640000c000d403066070f60b0b0900a124000c424100d408680c0945103640260340403800c11512480c0c8480542d20b0040310900a03075081c82a80000242c10b40744e0070095111320381899003141980d10382810100c019003104070846080303845e409110701c0800700b000150300901c801c07000840c49e4108a2034042c1440c0c1d464011b00d0058003c282c0441c4007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 110928866 1250 110927616 110927633
    0x90e06010e0c070c0308070c0e060312030106140f040603020301060f03090206040b25141e071505070503030f0f0a09030906110106050d110405240607080409090605090d030207 77
    0x20000c031405a0b52483c3c1c41c500b9468020f1960002844540045500c20a0000c0e4040000a4581950f010620740e2100020141d5070740c078207184004100410001808058424020310048500c03030000181008189101a00242c01c25000341e80000d038080010002c2e542d200c0202000d0ba0100c2c10308020600054001c180d9503c06d0780205c080099000460301c80d0300e400780780d0608002c20f001411b1f007404851407601001101d03100c214400c0501c225403030b1400e0108990b0084440a180300b00030440d0a1404101c2d0502110300e210b01c1040c40810711410f40454800e10046108204e198009180c81c0703010340304141d82240142141134000d02c0c00f2542e000080d041202d81c015202c40742002446d840c0380c914800d0142072540c02803904200401110020040411000c8038100030403941840256980d80f880c01a100311581d8440c0002d211440e9101582070100c001d0807800d0040f4041481e0a0719150504240c415018040b90159600d000f0091008401e12080c00c410030316160651401085490300c051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 110930116 1250 110928866 110928871
    0x5041b1212090b0310080106060f0801151e05041806180911040f02030a050f0601020a1509120203070507090209030a0b1812130602061b0c0c0306010b04090e06010e 72
    0x49207400c0c012104000d025400250040c84881c84a03684c030f00e0882d4011640c41315a20445020b98200032012429602039070056007945078a5a5440c030a078a8803589280e01850040100c003800101c0d5907006141070814043e182016190301d07025034440ca07000d4161800c1e4004c69085064601d05503082c0f00780445000310b030100c02c5c220342c0e003c2500b12081c100300e040070201c030100e1a8018a4118030560034216a00614441c41c0820300810803603941b40301580d00407000b1140680141c0281401c00002040c9000200c00c00024010003d40c084155031580202d8507081040000342e4400305800c01007000030030024002e05915101542016101c5010954407150600018440c000203000200b6142c040500d0048402c0a241110044c50346294000d07441d44c852a44620b03031640001c0040340070360000134a140940752988225410040b2030410380f206421500301d4092034098000101e81300c0d40c04202e0320340a00300000038150340e94603020900040350404403111405801001c010403c3e10300003545280d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 110931366 1250 110930116 110930123
    0x140304060804033b0103050a060311011d0910051c05070501140c0d0c0201120b0d0f020f10020709063f050d0513080118150e0307050105041b12 63
    0x288550390141c00c00f0200c51505000c552000a41c40c0800c600842c001150700042c21b0300e040105854804620040d15402c2c0030240c05183e0262016107194480d003103014941010202540b6a04880400201c00c1081036640015800411005010702c3c50140c4204964001242065292160300e5031140d03100c003010301c655410b020004400c60503050145088441010200c0c0a4412241c401c0350060040000c0d1501039001410744221f810442c070f4903128080c6180e100414100c02c2103860b5544410420702054200d82200e080041711a4544038900d10308140052038014118950400c155541102d04541c444088102121200082c004850030384451b0b450b0717804180340c0800c0c40b0080c41010302000c200d0041484c400c0c031001468286c3d001010302120924001421040c50b41c070b440790fa081c4c0d1809940308a41070311125200000641482c3c00358110300303116401250a03490b01c18060704540084000307481e540d44a004100420554004140008000b181c000c0d404600f031a01c0c2e204440302c1d540006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 110932616 1250 110931366 110931377
    0x6120102032a0c070f06020609121905041e0302010f0e0108060904020a0e0c04090b010302040b0901030905010e010f05040204050907060c141204120201090503030307210f0c090314030406080403 85
    0x3550340d403540508840c40c1c0c2250b1400c80d50f04c140e407901c410300e0b6030707646109160040c020074000c40c80000d40407400440d602c00122583d8104465401075182a0301d00c26031400920400700400107104404000941d0740456a00c22035400354038500025203c0e40348440f600d420021900c3c80c40fa8641e0f0072201c40f036007000064608050340d030b982e131021a1810000c0c0c0c20aa6a44144004100c15403e02ca402401a181508400c0c010900c5210066080e03014501903120046001d010a0076a94840d40c403251000303004400100d00001c41014550845641103000b01c030098480b010001942020700515800c4081d000007861840e150120040451140c0781c0d0041c900c10b1400c5061321900010007910010815407500e1075035036982c0c0c80c0d40d2000003c01e24400c0707011915080300010145404801c0c0ca1184285403240b1580034680c41c0700c40740c010342c4851304c600499035403c10b9900c0020944100c000c1c614080d1581003a8500390b041200c58403c2c3c48012600c070780c0c0104024011194050b203150741050b41750030304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 110933866 1250 110932616 110932681
    0x3040b09040b090115111f0f1b05180603011518150e04050a0b01051803010e150f0a020403020f010e220501150306051c0510140612010203 61
    0xa40680a800c0b0416805a035101c00810280c44110012071500b00b1303900d82c01030005145102584408030183c60f405100107143e0004c10b030340240e400c100314541050500240c0d09030000540d40a40046d8095080000c20110385104204540f411200400408581e501d00750f61402420200c2440300107116001c0102c210484105000f8000c034540182051742001d60082c3c20f50303a0014a0001c01981132880780c2e0405001c1107000301140310b103d40310709040c0d48076450000360740d00c00110320042e000820340566907034807440040711050003041584802c4252409103810641503504200101800d0341c200507104100800059407461400d84a078102800e0047c1c6081f0550000b41a0904d401120700781c03200300d01c0a0b12400380d45680841c2c103954141c0c0480180303c58400c401c504075901030051940002648002e80350020b1005400940c3d14270410443d4520401c2c44201800d9410203046103100d10200024049030340380011100703154003540e400850942c600442d4000d0210720b4140307404800c804000e0b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 110935116 1250 110933866 110933869
    0x50c09240f060919120f0b0703020c070308090303070b010e0601020c100807120204030206070f02040509190b0c0c0f01020702032e0507091502060402090c040b0f0903010204090c0203191103040b09 86
    0x2891302c010a01d4580d1114504410b0521080c19800848111880980321000a00940c000c1c400d0b0361ba01d50241000740051419035407241402d80c00034411a91500c0144610300016060402040c043c141e01e60075040c503428000006031400315100110741c4101d0b0001000d250007903100036040c1c1e0105051030041d850f0103031203040e20002e10403a00081d40040d80010700e00f0030b106011018a01a500c00d40d810480c80d80d43c1042c243d2100d003541c581d003000750b503c2d460080c04640c200c00d0054001100c403403050300d8402d070403420034585116110802e041e42d4001c181d00c000c0d45414040800501036042c000307510480060410700440300e4407102070b4030403640c070400308070000e1142a0381d0000e01100d11070254000d010410103540c0d080c044070120300c5110000006007080c420070040d00c04441c225400b541c01d011121525960b1350708042e8843e41c042d036003800006208d6000303020346030902c00d041d00a1a03680064400b1030a400c0a080c00701424001c0c042c25003036101000000300c500300c0c0d0003101e02946a01000c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 110936366 1250 110935116 110935159
    0xd030c030f0507230c0703110a0503010509070305010e01110a0f02011b031401080a02090f1e040804080f0c010509120304090207060b010906020a1e050c09240f0609 72
    0x51400082c1c03401c800c002405800c2a8000c08242c441c000803505110903400c4c2021600c184600624030790402d800820010f400c50080903c02c8500500c43d945207611640401d003120402c4444103e10784c8000c07002c006008082c800c03e14801003100c000d01910700c5a01030300840b445032000d82e60401040b0781911191510030f40c031000c0c0c0040320090400540405c840c0c0103001c0d01c00f003446194450a400c0c00005d40390000201007040c142e024081c8403031562010701801d054440144030080501041d036021003103209608c8220b10491040b40c3e001d0b12507080440076443e2286009803038003545c0c84180720300400d0780c100041c2c1d0b0b4815400c0b00c100116601440702c5e142103002d140d01c031011003400030450741c00b044002e8100340061700081c0e0f0f841c5481a07845000300d1b620180700e44007500001c2d03030054100c0c101c0d0b071f61b07080c440446004a040304d400c00c210314045654500200c07540226808105501c2c0d10507550307201002201c1104980703180301421440001501c9100e050001c2e440380d050716280891040000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 110937616 1250 110936366 110936381
    0x170903060f0403021507020c03160f0e060d0501180c05010c0c0e070e0a03080d1103041502070606030b04110102060105030d270807030503070b011706040303200c210c0d030c03 77
    0x402c21782e00241016400a5901d10f03882155504ca0300900d590040d0095045040710102c0340c00707210142c111490150201d030b01000c00f41900e908050b103c001c410104809015114100000200c0c04502d20220b042004951207103401c0141000400048500460a004070075020380740351180840654481e00c009a805020060750980c22209030000001030101d032502421492801c1201404004209401d00f4568881294001c0c1810000c001c0c40000642c1d6070b0107010400c2c07060100180140e05c98440c80c400b01e000705e408560706000c0515486030365074140311843c01804250020900c0901d200750103031032400362540d42028400c00d035403c4203911201d1001c901c01441d003881691101c03502e80c24000d40720f60041c1800d981141300d8600004144001c08012020030390204041d040c55201c60741c00302c02500340400b00c0b01d12040b002c3c80402c0001844002043e4821042e4010900c200b40310b440b00c26128101c0c00c01620212050180750060440402d0b0070320f101e0150f250014401c802c45030203400a1412 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 110938866 1250 110937616 110937643
    0x150b0f0301060314092d070803040815010e041209050604170d03020f0f07020d0c1206140403050901030b0307050a08210c030301150c060c08090c120705100905030607080103170903060f040302 84
    0x310b031f8000680d980040000c105562900d4251050b4150360720310318038100d00a118500c0201c100d08001008a10064016408800e0b245008a40c490350b4070001059a0403d400004040202c100480c1103d0401c100b0200c5010250400398200101c4004c0c0780428010000d4201800b2000180001199a4001c91028241d4009800e00d840340d111403045440d03c005803811034005141c100e03045d1000d0b03602281903210b0759065440c04d144c1003001c8011000345c0701c004401501031013910000b141c0ba40c1e80001305006442072074000c106010a070b04452104500c42140d00300104810883e5404160012044905550502e40c01c0e82c034400160301d0440d5800c4074014060903080c6441c81030712002e40e0002820707004504071b81c00c4a4213400d50104022809070007520814590f4805a0204010b042101505902948500340030300300c180d84501207424030340d00310380a00005100500520802c44180d04035401c001c010002141005140310210755500000f410301e682c0407004a000a04141c400c00c00030960090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 110940116 1250 110938866 110938873
    0x140103111c020325140f010309081219060b030408040311010915051905030f0403030e010b21190b0a0f2403170f0409150b0f0301060314092d 62
    0x105520440180040700d0780f14607010203290002441c81e290869105d4252001407004136070100840c0150300825a0720003c50301003200b801721760b03a1080b62000b501c1c803070200c804074120340c1c00c2281981821204503401030003440c1c205000b8000070640c3d070b0050780d090b00e0340f1046522030f0060510068400e41d015a00c02c100d00b6418200c440303641d591000c09807600503880703a80441c08211400e829a120700045540e01e0303038150100001000f0900c03a402c101007241c2003a000240401d40c01000c5054441603074211201e09403030070b4801d100c80604005d56809501d104051a00ca41029a907200708081c001d0103400071544c43e0100700c51107440603404030322102600304070040c04a00c1420b45082c000e4084c1700039264a00a00040ca141d10000403c0701e900441088809107414280b0000f9801445400241d0300540c940a50120f011005c80c001001007000116186407258075090000f81600c1d115240b0303031900e0801d2402e0001180000034031415180d011140c18040130340c82200188410f00380c2c034013500c1610 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 110941366 1250 110940116 110940133
    0x403080d0b010302040302090a15080703060204080d0302070c0e0a1e05090c040b010c0f0804030209010807090b040c050901030c30050a0507080f070311031603140103111c0203 77
    0x104801030100c45801001400100356a000541c102c2c069803001a40288007500043c030207003500c0e4030099413000001d101c2070b07506403510038181c904501c035001140d059034005014800301c401005009000021490103624107403480da901086501700d44154802c0c180010046000307255503410845034131407000345000c40300d62031035040800341405a4483c42640200841d10341d01d41400d0084840403541030315484901140d44e03a0328142c034000131109a581c07441c240300100069039a40030150007042482c006081c0d140c1082e02c00c1c400c0311460141680f185240c64404c030b803220780102c1503c0019900742800590f038140e801065030200915605800f001040c464840540d40d0480d886841c106000b410402c100d41d01e0940401c1110b0003030301e40001050f050000180c0911803030161aa04c8010b80c070b401310b000e06070011380c0d494540069880c1d40314580c8081c0c80400940e4548144c5031011910890380546514649810030140500a02c141c05030002c03070b05401e0b022100d50004035007190301404480b01d41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 110942616 1250 110941366 110941373
    0x1c06060509041a070c17070501020c0102070f0c1212050315030d02060717090a080a17040c061421090102040b0309010605040b030d140901031830050301030602070501060b0403 77
    0x4a03591101d150400e00d00d030012400340351245d030304409910382c80002a00a400300950b2a0455000b428040b5410341d0208030118003441d080c0040c1500612804011581107018030344a2441d801c2d40e00580b01c2c3d1040c450200003c1880d0704403070481c03421a81842c0e540e946038504da03d9026904501000e03094880d0050304851960b000400130b00c02d504a6030b8401d09140360101202d0f080e5030075589059294000c0b078843d4045200b1000802d082c07400c90900641030042007680b09030f900c0088609469009002e0802c01403160050000444000c81c000d40902c1d000b202c4501641d0b425034021144020846000000c1d9406002d504403009080405205516880c0003030000d40a4113160042c54015428001c00340803506000031001c1210304241c54a00011070700c0031040130950001640e240c1050340f05c0e546085003505410491103000d0041295650306004d02206003084040c0080741c044c2c40d014242c1761109698403409072815a64800b00140c0d4400c42070030030750b01400c0b442e0440300c01c1e100d0014001040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 110943866 1250 110942616 110942633
    0x409020f1225030c18020912061005010503042307081b040612020303120601050706110702040b09100b03090f0d020f0d0c11040207020406030b01060e040501080c1c0606050904 77
    0x51030710000c182c1d8415691800100740c02c14081c8001081c880c06194140300d01c40b0241400e03080007420180040c00c0802e01c100040b0804040c10081000d500a501800f00304614107100c0702c003600003030030302c01e14600301540c40c81e0642c052101010341d0700103c0444101181e0050014800030030003481185d02d95000030521095001034100701e80e1285181030030004260b4400c01c142840c0d103030000c000c2d50420140b4002c010388100010700c20383c104a401c100010000300c1c00c1c411400007041121013142c841c46c861043c80110354118003124820a05601000500f004003034105050310107000d070454a03500c2e4288064902842621081854090250a640426400034508803910541b00440d020030060f81400d4503040c1207503c0c050006e0380d40150070320305800c042d002049560b1000d00001101030381d07a102c1a50700802a000800000d03d1030100d100326291901581c0d0145c011400504100801c20380000c003948541111018081110440c490500100303500840080c400908586110302d85071418580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 110945116 1250 110943866 110943883
    0x7110d060e030c0f0712080d0204030c03030c06140402030712020310060e0915160e01020c040f05060406080610030f020a080d0207061706090712020903010228020d0203090409020f12 80
    0x10f280310300b00142c2a01d120014509084540c2c03500030141d60b000e81d4458001d150f00401d61078440d15000c01c000000140141c140900542c082c1d928408600c1b842e00e0301c401550502521000b05650440a000c056513020500134100c1d05050f05103009110b0034808241080000180320046501c1c24100084080590740c241e071003800b001068440c00a40d4012503140c145041e1101101c0c000850301d40c5060901a40408512070720500461720030340b952800050a490400d01c06030f0010f902d890a0141c5402c10707029003400340031100c010705114502810a818056440c0c400035080c1d108500118056480d80d40d11003010b040c81000313561055400c11400381d503c0105103d200002984103000070180c0b50104103160044000030030004030b5440b805021100305800d4014205415400c00ca05110791b6000d10080400c95030b160910482d0050a01102d40301c0c408201c007000039500b11080c0b00c034000d07502008442c1c00841c112400501c0e08254008101545070509030681c005e0b4501d106000d221000207034041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 110946366 1250 110945116 110945137
    0xc070f0b070c081209090606090907030c0806030d0e040209271506190c0503040b0d0e010f021201090e070e0702030306030d0e100305250518040603030507110d060e03 73
    0x1880b031940d801e001641c48028010401012070306210340da07030034078104068540040380200010304060031400000c9a2840594015000c01c0e030722080030510540120056900010403000741c84800c82054000d88004806055240b082c0e500041c60041c65595414403811400b1427415444910406865039000440945194241902d50001c4400310b1074a0003c0300c940c08008010141140040b034019101e9003180303101103a15010501000c40c1c055000000740c4824110410085003d40b02c0360700d080e0071111101102c01c54240100329030341ca41c0030300d003990504540202c14000b40401e4100e1500d410005560008038154403200d0900800c00e40c0000690b0060000b01c05503001c2d109169000d40b00140150001138102c80359006808445000ba030104c0d40c401c094406165901a2042c1d80c4081305280c810000b02003113012a010080100d00d040340d4015040c2a2004c104050a40d10090035900511000419031505503180c00c985441c0c0a0807480e8003a40048207204d02a549011540c50341c00020410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 110947616 1250 110946366 110946383
    0x9030c01110720060d05060d140a03090e04031b050c03070603050406150f1203270e0a151203020a0213020c010f06180e0a0f060504230706050c070f0b07 67
    0x201603c0c1082d041c42814240c0080c052840c010502110380e014140007419903511010040071100490003400302401e074080b030300c00034000f000081c1c50050101002c1d504500c088090a00422000039045207200983c0e088440504080c4c50051400e10b10f000c226200700c68050050400005409800d85c011070300452240e10280f00011484e00040b140e200c451060224280f901e41e41001281460001414000d010380b4108000341503046e008181e000044610000b0b20404c02c00c00c10200706038091540d0071104051003484020700c407002c80914040039015010720f03a96540d00900c201402080003640d19980500800b5202c0c568491a1000f500607800c0e15000e5401c1035402c0e009005980f01c3d82007a98440a001541d0b0b0b00444200ca008181440d540c240b207103d840c21003404500103a840840c4644942d0340480c29150130b151240e01c000042140101d0500b0700141e404412401051010a85040b840c0c0191038442c0f80e03600b20710b0403c8651080c4000401e0704c1020904202d00b000a1000c140195102c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 110948866 1250 110947616 110947643
    0x130807061d010e280b0906060315010e0c1c1815020703140904020702130b0307140d0201080a06090905100b060f120a0605090f06010e01080115050309030c011107 71
    0x1918240c64916070030b00b2a54004429041040d400311010400004c2c00c49044060120566601c00c02c3c4481910654840d0703100c1c2c810041e503450b0421103104400404c003a03000c40c1c2e51408a5464403d01c0c054420300c521100843c2c03108a403802450803d1282840c410240603518581d103800c0c181c0307044003000f6910b4014142d81040183e0580c001c41d803900d5490f9640c4890700d0700322001142c46401203040c0c0c0c0e83c49a0200031070405640c407200020301e0591103801c00142d0106d440100351403e00360f40c2c40840c1034100f1203102c2c01072355223a41d01c000d0450380a00b05400d241c4d4941000c200101216000b44842e81d10f45074040041c8000003a190300148040385c0c04204940c260700810500c6e000b08c1c032128080c903100304003030001940b07030000d42038028035070080c0032900a45880024942440458040e0908052182004040e40c0e009009111600081c28191665410306901d90009000352050348103008001011030220f030b40400881e45440701c0600200310a100410082007260b114100655110400000303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 110950116 1250 110948866 110948921
    0xe1c0203190807140309150417070804090515060d0c20160b0c0703030516080f0c10061410140c07060f0f12180204060801050601021005040f02040513080706 69
    0x2142e0281945e24010a482c1c3c1c0843e03904061f000e4014022910f0301c1d1080701266140520401500d15144a031169580300d41c1050010811908000e004c18000e5920f054003500c00e442d81c10807640e1560070a0004141c81003d1001038a6680420407540803a1084180d079810350400420303c064a4084000790030b00450f560310034940b550281c0011245903801850003000081d00580041000c0c0040c1c1480b509040c413141ca0b00305d04c2d6080040140807400c40014000580002803240303001c4640d130f43d40c04100042c1400040000021001e40b41401201e110b440f040465010b05030f1400d8182c1242d80ca160384142050301c940d142c01280c42084003055038400200c900341d0144407c4100f000311035460060950310000382502a02e42c921103500c0340400e4588030000b507142d5000382009410400b001041d5407c10800081c038000c8110b00050415242000340030000746540251200a50119001304050b152403280d2910342401e044010014200002e00c0810448107030800150281b80d420010031001080e030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 110951366 1250 110950116 110950157
    0x3010209030616140c06041103010e1e010605030a0515070c1101140405040c0201140105150702131107060e06010f08031209010b030307030201090606090e1c0203190807 74
    0x12456410342115001408103118610040e03c0360345249001c04035903041e03aa8244907540461300001d4590001d904202c1030012141c80203480417001c2d80200600c560800c4450307241c81e0300d0241910940b1003600150b000080c2500032901420004080d100301c01c3c0d142ca801030703440031411041b580e0000d031500040c0040d070045020150054000300e2915000c4004001120344030146c84510b00c80c403000307003c0800e00c0d031608e20400e03459540e40c0e000041c00e0368011400c4218100140d106c00d01c42d2034240d00c414500030301403060701c0c22207505958100340d400300001d003070b0301500e612859121824030100304081031004941003800828081c205864207a41c9407003400e82d1400c4e4500032090107900030020114904007101c401688245084000034651160600090440d441148190300603911140d551040c0504c51044c18003e01c0d00c038008000f00c541c43d11107a91250703a11901c1903242a80d220300046080d0080c8119100c0903c1c107030540380360140c0744002911411050314003000007410b01a0041d9040344a1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 110952616 1250 110951366 110951377
    0x1e180601050d0f1b02030d06080c060a1b05010c08040c0603050610050702030a1b090506190501050f070b0115110622020102150403170703020909010b07110310020d0b030102 76
    0x6a540718603201c890440040948243c003401c41e00c0c01c0e9500c10400c012416020030050103a031642c06169600b5a2081c0343d0706031030054020010641182d0b101c0e00c0580c1e9003800b12000340bc4503003455000e50b40403840c00290341c691403801400325400c1c604801100b41c1d20240c141d21440c402d09c80505070b9500c8000481c1168011503505030002c0c0301b0101180c889003d07001411020344020203c550944942d541e00f52907034540c0c2007003940c005501c041400700c010315005031a440b04050300d03a040c011119440b0000c127505144a80d80c18000d0000c0c0480001c3c10003000c440c03e09400c41f41d040c107036503503c00c4084000840380d8501c5002540c100030a0411100c0851000e00800940d11501d80910b043c2c200c041c3d2000c48050120305602c00c83d0304a0140c0611f0380710082c4190f000343c40b41c04410030320b02400c0700d01c0c40b030003071400b0105841084201e8071039079200080d505443d103698143e0b456922625004080c602410480c0d0360501c5840700000c0c083c07a240e002040002c030561014046101d807841414280e000d80d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 110953866 1250 110952616 110952619
    0xf0602060709060c05011d0c011d06070311070803180a05041505090601022506090501110a080a12091b2106050421030b031c05120601020304051e1806 66
    0x100c2c9001c1040e580700c0c843c031103441d42c010070001590034074a0784042c5202c82c240c140140ca0790005180c000d241d41e004008040c43d8502080100c0320b014540c0c00248461050100040a00080300d820705c8148001300190005000e8401c1240e42c0e84481c902e02c081130201c4498545c0c400c8410b16008211030404d40039480e0840c0309000d4080b0351605040c1007140460000784081d046106003554210200e4840d28962440c9100c080018070203405d01d54018059519038016505100d6161107251110074005041c00f03807140c001c0f220316107500621704119510001e81c80d41c003c0e01403c11458200f40107885240400035845d800b49902140e6030790052040c0950681450b4482c00c08500b1840089002600403550003807103100e18030041c012801d0b04803002c00031150008002030b50760000030420f0404000d0680c02c01c44615403030f88055100907000304280300340d40750014842403070000326409074020004e40d8090040140300915440b4142001901171003100501c0b88a002d514101a07140f80c04540d415015110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 110955116 1250 110953866 110953877
    0x1e0512070e010c0f03030b03070905060a0806010e0c0d140106022401050f011112070506011409160e01020a0503222102100507060207060b1201060e07141309060f06020607 75
    0x40e15192070013114408007042d400e040d164110b45001e5a014440e03070f80504000d03000083c2c1e0341000402e0004050072a00048601e42c051001440014101080f6640c49010800c03c00e03a6030100c94103580207003c809e25981c10b0356025a00104800d5000f003038455011030b804290400c140c00c580d180c62041c5200307203d46508401c50b42c9074440c143d445001c00700c11090402049912004c15a800d80d0401d9110040907109038206e41e005116016441c0c5004851a108540001090408402d208040110b4203008024010035004d1480264003d04c84003c5a03a0440d00b81c0751580020031844014502c141e9120034000d00125000c118244a441e0541131010302448416003a00319900b4068a8140001140e0920001f4041c5a000a0207030000706440c9120b074a0205400121005124040d010b40002c2c20b62070341400001d1184100591602d41e006030701d03160240103a032151560080383d101d002c40b50001080c81b1100070600301e05580100089880440140d060256595002c98032002c051303840c17400048 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 110956366 1250 110955116 110955137
    0x5180414010603020a05160f050f0607050d020c1905010203150303190e0105040807240c0b06040507051b010501050315102903040606061101060b03010302101e0512070e01 75
    0x140f00b07038050071410320ba5040407071419420101144201000f0301c1c00700d550200e00e82c1c040e0100310b030500c41040b41c40d020034010b000c14240300501621502178039410001c2294007017000c04c0000c0b400c000744170480f00d41c408401c0d0841c21ba801c2c410f0203075000303e409481c0645120082c0f210f50900108940c100050035202000002e000202162130700c19501400d81007090034480480c000b0000c1c8101d90042569400342115040c804041039203004040440b4400d2180c880500c0c2d003c254400d802d158045003c0703d00081f103664120381174a0500803490b8003400801e104280c0c159481055208030305840c0124200c0f0604404000001000501111301224184101c001044107241d00a454043e5925200302141e1520074030303a451656400845054a0702c0c0e484080401410350042403040411401e60007d0012030f05000c500641884180300081c0682000c1e04203403006031007038000440701800c000f56114460b010030001410342d0484504400c24001c040b0100f070619020318030703030f0380108030686503401c644 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 110957616 1250 110956366 110956379
    0x308160e090c1602060a09061409010f1103041715060609010518032a0a1e05150f0a261e060d06020409060602010e0c06030103020d0501060909030518041401 69
    0x2a00f01003941900400120303003480040e910300b030281050400940e0340c0c00301c00e4070f0110020f04048014940094084042216605c01e07684007450352101c001901706190a5219007040c5441c510440d400f070140c0034201008141140c8010402234440040004a031500703841d081e04000543c882c0d40c11075400718400708006c036040c21101d0301d40b8031400402803c0e10311032140c00400750013400e192643d040388503480c8010302d24a85400760715403000d403072101c01000c805080031080ba442030085010b194070440e200b606082c3d01d10540d000b2904c0051080e4030007a1982c03021b00000d0300310640200b210900383c1c6000f100654100e4904103036481103408110b001c903d40d0b4020494920408064950741c6c00c47c00c00d1105201003147d9000400081850300c02c00941a4940100203003151141c190200030341e00303c5015000199603c6044d03d042d03c1d011110f0440b5542140341440c01071820790b00040c0c0311810720303070307808181074011000c0c0805081e81000d009808082c1e80c10082222440105481c04084083c01417008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 110958866 1250 110957616 110957641
    0xc040521010b03010507050d0c0c080f09060f0403050303101a0301050607060212010303020c10030e030a11030c06130b06040c0207030312020405040e0303011d0702060402040f020d090308160e09 85
    0x200d10054000140507201840464203482c02151130002040700000c54442007080d44c0b007500c044c0070503440c0144844409981d000a203214400e1091f1070741c540801c180ea80daa6446040b00d003000c030002d1166664580d01d1a0040c0c881c0c10880301d1301c4507414103d1000450070038000100d425420201d840c1469a07003001b0802c0102d41015000ba0f81c566401d0101264440c001d080550207140203400501c012200c0008220501e20b0b03a20000c400c06041401e240280d0400005031020040c00342009800c0c6003980b01da1034618050b90060100510402c0140899183d42421302c001701800b43c4080d044660302c010502041d85c03c9040014010703401040c04001083c840d002c0001c44c0c000400000d032078107a84200003000d0700d002e0502d008554000000411250002441101000100b211001c00c1441d29140c080d446040042001e8010381c0c45c0c131210300503404144e0488000e160080c07804c00400040c0d0500802c100c50490b2120651507800d03c501c481076015804081c0501d10051036856940e8030a4481e081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 110960116 1250 110958866 110958919
    0x1104030f06090c180603020406080d0e091e0109020d11040e0a09060f0606030204080606010c0f0b091513020a0e22050102130e0f060a0e01030201050703110d090e0c0405 74
    0x4001c00320003004a12200c4d118035005030000031103c04a00c160440c01040211012540b014020f5480228035034030311600004c8185580c0c03803c95005039941e0700d8001008111032a101e0351740c04c904c81c480001c41d541c0c020754083c044511003074204200180caa421030560ba8071039801803081503c030102c0012042d0400d03401420080b0b102e19408244580c3d424031000c00e45500c0d40050010903000b080c141b0003410100112907110750709291010043c030003915410344d132004850740540b44003d01d50000f10152020040d440d10f560912600e50384600d00070519060007130f0808070803881042820300001e0702080a130852800f0300c03d00c050000d07440c012155203840c0b0400924040310655001d201d50074006448010ac01c005002d51026041c80d882d15036400790106200038400b40c415480d509080c0a015a03c004090541f9820b085c0240d4401c81400c050350200441c003107580343c0d84548020f0f00f11080d8000291402c031050743d1101080c50700c2c1d06003c0108c5004500031581c104164403401c000f8800c40904001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 110961366 1250 110960116 110960123
    0x403090e071215060315050a0e040303110409060501020c0a260703020604030308010509090a1e140a080903070806090a020f180a1a060304020906010e0103111209011104030f0609 78
    0x2003a100702c0c0d03403030580308080c01c400c2102c5001d010400080341c140c081c03074101c401d81c4410810202e04200021382107516074040d880c0046400b90008003018060b0303105240d40c900c400c805030349480d41c0f480030b04080c00584c02002e0040c007400c809030f10300341007070441e810a0714a890303407031181607001d01c0d034420304418100c20000c0ca038450744100102680f03400300184080d6009540e030b840c4640c1403c05014180c90090008840e81c2d1003c0c0603540450703003c281c4103c1c443c408502e03104030003403241403620002445008040b0640503404407402049000d00003044070040940c00e840b03c0d51341e10b60909840340011243c0c000d46400c080818801854100f080780502e4070000c01c1103c81400c8034010f40d415103021580b2081c2c02d0381da05c1c030748644442021421584104121181c500e035103450340c04184080f102070003003410703c60f5040c0c400c0641d80c06a04901c00b000104c0020320344941e4266490301c0d0f14142a1a616542e51030702183e4031040000500312070640c1d40080d0041c107841e200b655060020603c2c9a000d0303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 110962616 1250 110961366 110961377
    0x601020a021512010806090106060903030e01050702010e030118050607031515030905100b01030b090412080c091503041a040308040308091203090c100801050f1e03030a020703030806090403090e07 86
    0x2c03440f076542c0080d224043c00032400140140c0c0380c0b00c90403030308483c0e05400c0901408442841040080c0e405a01203280402c2843c100e03071201ca043c801600c0b0f40c1e40030400f40da81035081c00410210560403a100a88050041c82114003d450f040c0080d02124800308550b4a4400e00120601405003203050b44035264400e840c1c0014040307204c0d01c540307041c031640743c1d1100185503c0d090401c000e1340c1d01d8081d01504c00703011078004007241425a10040000e0b8209240000e02c9441c40c0060030740000310050340c1400344082c1105455000119a00d00684d0040f98115080c0444c1001505015400801d89108551540f1800702c503850310b440944011400900c3c0c0320322031140800d00e03040e45035140095409001d400000301030500804042103002c2c0302d401429000c00c036001004004035504c268681d80740841c10f8462500070780c5807291490408071010212a00340c480040d03d200c0c91640000c900044a01035500c500b03007a1102010080807001c2520050002100e01c40c0038810350000c29031190b080221820700303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 110963866 1250 110962616 110962627
    0x609240f03030c010905160b0301060512060316120c080a0302070b0c07050316081c081b130b030415020a02030904050a15090218040908070303050c040b0d230601020a0215 75
    0x301c3c0c0c2510310711002183c07140c10400410f1921b81c02c40c0c0c003c001801c400c10380541150304298004115001c3c170001c01341c05034000001f050f81500c051080e102c800b1a0070700c0c0e400c02540c0f60500c002e03014048080c102c2c0c401144120000300ba000220703941008039856030140a0182c505200300c0b2094004580e812160300601d000020789603001c000c100c0e4100622820701d05001d1600e10a94284510780c0c21601103820403110f0b4040c4260f0203045e55911110030184094050506642000603010740508203502650711031001c241c48000b00d0145200303d00c14603403588051080c4034244180c1c0103010703155015030b0050000788414501500015800b50144000044950150800318a01c01c0d0b40c0d4011b03101c0c10783c00201e8240303041117160803003402c3c0700030380c0e061040c02565514401c1900c504140542010b0362100462001004001150020146e0f80252600d868404070140010020140d41103800001003541580e150708440b0041d00c02c00058004d4481020b20f0340910080c186120039030104080304004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 110965116 1250 110963866 110963887
    0x8090a080d080a0f0b01091a04091103010f080708030703080c090306041109010801270515090d170f0604051909060203090f06060a1503060f0e0609240f0303 69
    0x300c1c15801d8a140e8a8034a00d0508050701c8084038a440000400182000800c3c0c4c004e076004031002d03049440c065a9050803482e0501040c00038055900102c10030390403c0d25014042c842d603030103181619000040204004e0303030758040540d1aa00d0b441149282d81003400081d000c28099028903911203281607010745051a0a00041d042801c2114211020005042c010380c1d1400c020161138054290300c0020040180c6a01f20b80d4500034890000b012000000c0d40c5000c1080301c140010300a1002003180c4801501301050b8054484269030641c000081c80016880d640b501c5c10521140a0031040b650382c4000e031a05014070014100061260751654490307100c0d91941c0145205400741e4a0107440f0040e00c030300f801080345080c40d13045142c440c442d0344484184000c03940d0f2011030104503100300224030560220304400ba409440700b0751060440116407000021429054980f587c400d89040701e1110543d0754007a400803c00e10400317100003060b900918060084d04000b9070280032800002c0c201d90a0052800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 110966366 1250 110965116 110965123
    0x61707080705040e090a06110f0d0509070305010527031206120705091905060d080306060304030c0206040b0703020c0102062203021518060c09060d09081b06060a0501050f030408090a08 81
    0x41701001c55601c0000400c00380091440384240d4128000742e450310704000d03445d00c400c69000728070880c2d05660350340c030201d40c0800c0100001001147c0c4a40240542c2c58011041d003156140c0030341c40220b01c01c0500500342281c9010003100c0f40b110403001e0361001a01c032602404100241c014200751136204800012400350740313110f20355100d07034203810b40d2554000400e6000d405842014003141c0c000c0590503000c82c005401c04040e6a440700701502d0854880d41c0e80e0070200d0703481c205c01402a40004001401003aa08406002011501e0094085030f2039449c051004a0765860100c44800071810709100400500c8501c1c1c101c651020301030710480e80101c83c422241c4008040c191001a2046008007060465010522403942c0c400c3d00384410a00346034218002c588144a481c0d0072030b0b6500d03039500541c401c12217080c0943e0f01044445a0300100810f081c00c6240c4d0300c00060725800d21654020600144a600c1001104c5c15800e038401d605041d0b4440f580d40c01070982100d5003499001c486100040342c02081003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 110967616 1250 110966366 110966371
    0x60c0201121d0d020f07030206030903120a0b1c0308061e031009030305010f0e0a0504080c0d0801060e030a02030703060b06091002010504020f0409110f04110a0306080601061707080705040e 83
    0x10b50b011404011072650700ea18100f41a0a1082036401c50508103842c5940400c0d9101101e406441850750ba54445501c5411841045547d245c01c60303005080c002c070355419502009584002340c131036856010cc1c078010700708510803180f40100024900e800003115410591880d110300d00d100d8003048107003140c41d40044d0401d140819040d50b8075584009080a16a15020302070041904011490580c1d007401006145040000c040000c030544802c003203420408048100d4100451007030a44106140e92a40180900c800303210342d2001641c060040a440e180c0490b02c4c44005600500405a60340b465441c3c2d00034000340a2155032005041c0703c0c5c1c0c0510344643c914601c2142c80341c1c0c000207442c501031040100b400114400680207a2070081034800046100803100a1442c1c116582840e8014920008000d090301d514a988550000314442c100ca40e01604817009640e052015070300301e41c1c0c0b168002c5400607410303220325440c16180d82c040741c2d819008141007a08800c44e45411840d107512402c2018121200707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 110968866 1250 110967616 110967641
    0x14090402040f0e0106180510060206040303090c150c0b090c0303180f03030f1b01020f04031506050411040e0c0901080f0912040315050a0c0e040b0a0e0112030f0305010f060c020112 79
    0x105004807007880a4070039954423580d0003101e0329201d030408070002c0d5590720041008090564074058081403107000d0151000034003e4404000c010941401d00600d00710280c04211418220013010500c8220302154080741501c016004508000425131001c0076400d00c40271740c1c0c0d004a03d080340b100d242c2d02d05100030440200d5440513036a91f00c440540c1c401c07048482e524142c0d01644188581c4240e000c5d8001100c044a802c02000301051009004190080584c2d42c00694030600c1c2c4201e090080f40080050021110a90180d100e603076502000c403003080c450019194001400700d8001030390080d03076a106942005d0454216031000700c02d50340b0392080c0d40c09a0400e480c48000042140010314081c01102e6106074607d006100c0c1508440c0c0140c0200d90041105110319259511043c154076180710010080407028a1001d1035690340039403207840050224150009003852207010203c80c0a40651412203041c1d02a80c503a983c80c21104441c5c11096003004c07410002d82d200303002e0480046004082ca03d210 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 110970116 1250 110968866 110968889
    0x201050a0509181501020d030501030b010603110c010e102004030b07050c0a0b011a12070503070c0203010207110901051c08030711010203150102070503010e06130503040305070b1314090402040f0e0106 88
    0x41e102c0060701c0e082001584a023014140b00c01032000504000030681158114240130804001150b00c0d80e099000b0111035403503031340ca05140c41d250440009065910b41605050070000f0b0403c614600b4800c0324019400c2503d400100000c0000a0300102c00541c02a014600301c0d00b400c0c1c41c429420f051903810001a186a24a000140f04405030843c848480d10352421350140303452051290b40940050050400d4144000880020401d500035041e21848590080003195140c01c00d1818041c02d03c00d0340c600a0080500750004201ca00b42503070042d1000341c4000e00000f12041c103550752641035100510b888104004240000f4008209001460090081d403c00f0000641c428000a180c000527920030381c4241c0c106a100481c0b010041f85050300110400300070f10080c80d4030b086c050729511890384010481d00c1121000903107448040054201e96441420150001d65551a00d441d814074144030750741c3c00460b11000ca001840c0c168041c0b4000e0607604c00c0442c2a00b15920042d08480440d4881e1040c0c94 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 110971223 1107 110970116 110970151
    0x1051c030e0303070b0a050601020705030703060c0201020f0301080102070b0a230916060203040608010906030b060105071a01091e050103030221040e07030902040f090201050a050918 80
    0x780c0103022a90750303002520305509150001c90315086a585407a01240d0030390b10206041088520040c002c10065041d81c03140401001000c4007001550750801c101b90712640707414041d40c001e1460400040c2c65407500d0600d68400c440090042c00001e1801100808019680c0e0100500c030b004503030002243e5031129030083c5407445403030150f214020444000038042d45d00000a10568841d80c0d11201140d81c1c81e85618281d0752203000040418588400041c029403198028000c95805015205004040c1400c43d1581100c00e8000c1103a490700c4180c1f43c01c5404110464000d0300600c1c140c00c010b29803542e00c0081d10303504104011800c01818072032403401004c403a419170300a072451031001501d0b400e2080f40a0024201034808900450070f00c149581542482d100d0814603e4060310b50038648406160100d8040c3d00c19000c05510502081301c800f62584150301d00340c80780031a0300204a948 = true := by decide +kernel

theorem cover : BRFrame.Cov 110791366 110971223 := by
  have h0 := BRFrame.cov_init 110791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 110791366 ≤ n) (h2 : n < 110971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
