-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2517
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:56:32.37809+00:00
-- url     : https://prove2.me/submissions/a452afd5-2d1e-4183-af9d-05c622e19518

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 452517985 ≤ n < 452697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 452519235 1250 452517985 452517997
    0x15010e01030f14100e010807180c1b151a15031509090f07091118040b0a03050c040b010503040305070b1009050403081602030a0e0103020d0e07030c0911041a 69
    0x22290300d40c8a103510300d0944a0180f07000309031084d0740c09031090074071884101044040c2e00881c1142d2200400700074540411030340017042200c1050201307110380000d408460541c08185007405407401d01d070580741041103a41076500c0000700402c0502c801a0031b0240300c440080e000b0642c44e00040c0031100c01c8003150400d4000d650007003c0c000c0400d42c1800c0080450b000c41c404544035101c40d4482250380c1e500340010000302c0018448000d09106260f000181711410340250161600d01004400d081c1a8590312500240b00f5103001403d154100d65072414125952820015842d0240d45408007001c1503520440481780700384d406845691411119959228940b8402094690007415803400821074440b10700856000d51f00954440100e4104082e05101014040000d01c003923510810252540e150400c124501107002400c0040e112003019034200098402c5c5418101c0078061880f0100401407007032880e105540c81e40504112403649070035070000a12030303806540b0613043e04100500003e95941c0003002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 452520485 1250 452519235 452519261
    0x626070f03110f070b0f01080c06040501030c1103192613060e0a14190c0b090103090c0b0304170717160203010c03061401030204030c060e0a170c0915010e0103 70
    0x21501407048030221051300303d81c804850b180400028802c500d030528110502400c92900039007080b084000c00a01c042c45a4401c02c1c0c14192201c2200c0c042034021240c2000c0503002c40c056a684400f001000000381c01c800000728040b401811000c41c0c1842c06100030300c0d00600d0881c3c60745040d102c0d4088200749400340401161b6a50b01e4000388000c0c44000c0c40b201c2ca02a2182425020104040403240d0030006086080310000440c29a010041004540d42d1070498642510341a6903d0f01b0f07000403000781101d49005018154112000550002840002c51081c0e000d0030640c808252030030700006039032144c0e08000e010301940459440c800180300c00200300c100240001407641c4800b550100b82582e00107860038012a6941c0c0b41004114025131a00541c840c09280861401d802c40d614218640c0c80c501860040000c401501d030202c3c2c0b21030300350001a103540061069402c0164880595a4903400076042c09038a00b8008101d5943d01243c1031020041f05855030441980300d440110300170708103202a42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 452521735 1250 452520485 452520487
    0x90106170c0d0c030c03030c20091602070305060f0a051006140a032406270306180512091e100c0305091c110105040e010e0705070b010626070f0311 65
    0x100090017941030400840c03091300d80030004a02410318070384548424146460456810101e100c1c0750f038039800340c83d91107002842c0c00142218015412031030032405420003021881014140200c0c60644180c1d1449080a1602804140d80f0211031300c51003441885964085035002402040c1d00111102030603889500380307030000e5090f1080911110305010302c3c1c640101000c4019090200c10340c03100002105841d510001c84030000c0e1411a8003403014944005003502d961411816070b1480040a20b92807950058100c41c1480500c40d00274825500204020f845400e48004032007990003c91107850800400400c100c0a4030045c0d0010744045e42085011420404100451401c41c0c5d02d086034011100c03440d20020042072018a0201c401000c80d18141c2d0511605210800c00581c503504121b05640080711240071f1500d40c0c0b04281c070030f4000c0c0c0383d0050240c1b403120000b02d0310660101308002400c188800c0d60b0209180c00e131000030140000d0740c001c0c00003080c150000803018001d402400d081e5024245207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 452522985 1250 452521735 452521739
    0xa0308031b04030809030d0905061803071a04170c0105071209150e030c0a081e010b09070e100306060203180f03010509061e0606030105100c050d08090106170c0d0c 72
    0x5421990094104907844c1a0100b400156030504001080950046042c0405503038140b00c000b400314025084104008a204e884800071503e0500c60540180070502d0440c1311210840c101c60304a420a014120440c0c5500b0000400c4400001d420886408180c548170f1030103044bd281c265a44000403085014070003003200000e0750700c0700390080d65129a0715680d54410805c112040504001c4030300080c0340308a080c80700900c190040807c66006500590105405c560089a6440c0c090020008066801042841000780031034020a081c000e402c0704883c01e8103c507001400640031181540a00030050b40f040c00903107031122681140c02160300c00101585d50140c0b00300d00003406c0d030301c04a4603924560000402d00034600c100402481118089051000051a088011503079600052046034803480002004284080c01500200080c907005020303900f10601c0c3d07040241081d401500c40d04159840d2440000754a440450f8042c1002004400303031020180320030030000b01c0803065805440c00100b81c080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 452524235 1250 452522985 452523031
    0x2090409150e100b1e0307030b0c0403030f1806030c020f24070c121b0204020d091709010e060912030406020703060b060301182a0507120309020a030803 67
    0x441544008900720400319166070411501d82c3c1c0525030181094120003641c0c0e1844069590000310080003185840710030300080ca408000e07403003d01541550030911482d54103a02c000c0090342d002c1d45031000500f5806404440103025000d81c40d1304c9582c3c496080c42030500c20340150201e40c6541c8110740780000f02208080c200545480800300032200c90030104240ca4410f8641c40d07003c400385c20804180c840c940c9640c9c203440c101c009011308100d034101455520082d80711f80019800e80240086403100368054108000f400d280400f03607001051081402c00e440c040c0f10485501d40c0040e07650301829403031139042c0800c1e0380056280c540c0c48030b1a0841040c21000400241c80201103a50040c4507962441c14854101c840c0d07185058040c0104100500026003c0721400e5103908801d140041e000c5503268a0381500146602c2c80a80141e101d4200004180d000d40600340340f034042c03503404101403481142503044440000000f50070400080040000ca0b41e032038050343d4040d14000f5a00015803003200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 452525485 1250 452524235 452524253
    0x190906050d0b041b030506030d090312210204120309050a05060d02070206070204091b05030307120e010908010618050a0225050a021503090f0708060105040b0102071a091201020a1202090409 83
    0x41040005c5d95a0302040000c1c9001c1080c44024032032800e007040a03600f9501c8081502c013080d6498001e00a00117000e105403281d00b00c0e0641000c1440381300310745179500d0308011101040325aa00390001040301d00082042d2070714800c03d104031340000305070034a094142d0030100040d420205003664021414450b55002d0303261b0340104658240b01d9003480403c03040040750039103010703441d0304481c0c0254020720040d00080d4030001e000307106100505201014040b246c0048030a00c03420780000702d595003048000681e12030060100f03002d00c0100c800600c0165a030b000c03030404a028080c0c0120300560f1845c007000200f4a040b08058080d40110103403048a51550081110b510840d0000046084000200310114800780a00c40c1d00240c4400a810300710701c0c01e0206540d449060182d83d100d56560044080c0a0703008102002c014002946680c2a8003041d110480c11604160341182c00360210700403013034100c10b043c42100c2380c080d05511400d00039540b0a0950b0000e404c0f201d0041e400a0f5640c0b42e04001c922204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 452526735 1250 452525485 452525531
    0x101404090c0e0c0405030f1b010806030307061409010f090b0c1e03010e1524030a0e010e0a210807120609090506070207080c030309060a030b09090102190906050d0b04 73
    0x81d540c3d59946203840249454200300d040d6050705a000624460144c0002101401e0103038400d1802c42581d854a5000030300b0340c4100b420060035149013503400b00c2e202851543c05d900c65042c12000300302401a0aa05200ba80c001000003041032002c40c0c00210004a00c0000d010080469042011384083c400c01082855100703800402d0030b03c000c40100709101c9041c114081d103040303007035441e060403100d48852110070051880c7d412040a0001c40000c0d02c0212940c010780790061940002c2c0003290503c0c00740e035102c054003542511090806c1c07100e0004000c808120a01d80708040d66031000303075075980c44202c40510301e9203400c01520351200d80004101031180500611035018101034107140c00c201d4000781c40c002d8141d114035800c0c3c000e02401004c640c0e0110035651001e4040e1000d5a803041c0301d2408400510020b00c11035408035503c41030100c5c5600541c054010b8804556030000d1042a690054490403e40d1007040c001500404c50400702440c0c80d08004048200504041510ba481c1400c10401d51001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 452527985 1250 452526735 452526751
    0x3021810030519050d0509100c030216090504020f0907080a05060105072a0f050105121905010b040626010312170109200a0c030507050705030a0804030506101404090c0e 74
    0x3c952a405102c1d0500c00e80f5103480c0e15082151074103000c000811040c500e0501c00c2c0003030081da045081d041c9802444040000d0320b03120360b8045490303140c940c0d0300c000b80802e4505174042c0c0441d42e0f50100c02d0600e400319602801e12038a80c0041a80d40341051409400010aa6030400900384202d400044403070103501c4c81e0042c15007001244610418421508640e01d5101c10480b44440c10100183d0360401d040b0340e0002c00207009846241c3e00c04009100744140c3c602d81c031a085141034000200300000901810a50f000b41d0f031042c0e000c080640409882c04000300c02c2c11302d100006001000050004a81c458461069080007207144103103000c6114041401d9001a005580750110120880600b1280408070894a01d510b4202151548020401824090018148000060342c6030034814100503c6008010041c1100c000d080310317140000c04c41e0000d100854452160320041510074001280a001b0380b4014843c4004440006003040040e040d4960103480250a8003404914001d00484d424803c03544 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 452529235 1250 452527985 452528023
    0x907080d051815040b0d0608161505040f050d062901021905100203222003190312060b0d140f1909110306070e0a0609030218100305 58
    0x1002e00c0303a12202e11031841071103044030744030310910490303440141d9064031701003a4a25100c00032080c0090092002d81c1200c81544612400800c5440c030655840c020344605030342101d101101d080c015903040c02140a403441d030340e140240034042420294401000980210004602041540d1803250581103014a2281038030320201e034068903580400061501051030010b6004000e0396443e46520380344d941040040e4a030700000403407440c0d000c610001c0442e05402c002000100014079010541c0300b1500c82c2c201b801440401051464a4040f940b04981c0b00103494014105a090390308881003640072689024003a56007030049505081c1c003001d060a54051507000600355240e48842d41a500c0c014a0790500702f9008042048040780d0240210800000b00303030115801402c1d2a100c9036005140d0521605407041c20300304807a0300c0e0f1008180e0341d03403113003a22411603168958200701d447c401c103800040d410541030140032a45401b0000340a07800b02600d0b142401882d104d039600c0781421768007180c210007009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 452530485 1250 452529235 452529247
    0xb0a2d0c0f120c140d02061302010e09010602071d1e091903020c030105101203051612171005060708090f06042306160303020703090e181002120402090907080d05 71
    0xc603140b0910090441c413008040c08400300b90000e542d208000e20550402501c0c402c04c004590050041641031030004090807050f6841d654008d40d940317075030b116415210880782e0640c0d033211a40008107000300882008600728429a103c03140700a24041d0040c0158402c1d82c05030704141045d8480c0c0c10300c05209901409520818008050079201d016000500380c1103d0718082203013108207850089444d80c107082454442c28000e02c4c805c0306441c20700f000341012110914070720446910116680d01c00c00d949588907a1a282e414510640341401e0040719000f010801044000c01d00f9840500349014000701940100607031040400c80075001507012aa1500c0f00e00c40455030340d80b08580502003020244c4102e8140f24101e81d4842040c0d03407042e40941455800900380c030505100d030001401030304130380c0030006803810404810208228000d00522072030007440b00907180c2d00242c0c000c480780903080c0c14848040d501c3e103400704009018090510b2660340309603000050068010321000c52400035503202c05888174 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 452531735 1250 452530485 452530493
    0x40e1e19050916060f12020a111506091504090203030714060916170c030d091e0506072d0308060a0806040c03080d0b06040b0a2d0c0f120c 61
    0x9000038000e5480c581111080f007841d6411030f10480100d41e1585882103400c10700f080b080e0fa400030360003244442e00340000f402000840d0010811881002060704036552030350440c1c00c0703142038030081c0c4651790300c5450754002c15020b100642581c00150070040000030080c3c810f0780000e28540c0807001c04c90300444003004013200e42c003040c0002c5a00200c640094008041c8691410b86102c8850140080181c1841d00809141d8820409142c000c01d01404480142080c0e24000c0c001c0c140764425002d248100800031100a9040441d281c21a2005400341c1c1c100002c65a50304100d101818101030072610b0754459981c0030201381d5059280e50702980350184181080000d026400105400040300b95000c1c805006c001040446103904480e0080540c6850300c83c0c1c42002c0b005801e003119034962000c800300d030100701c03400720b00020851442c003622200507042081e03c1d20038411315148003030401c82042c00c02030b0780d9803801540050f11007803041d100c1203184980e5031b071568a5640c107681c5101c0054201c1300341500300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 452532985 1250 452531735 452531741
    0x1c0b0606090a05190e1f0e040f120804020910050a090c050c060f010302151216090503030f13050f010203160c0f08030d0f020f0a03090c08030309060a0b010504030206040e1e19 77
    0xf03c00c5102c071000d484c5110500c000401c0c401b0380326008042c1125000241401b013501c0705103903401d6220142c5502e00c0e0b000c41d0000c209110a9805074450100c02c0c0101d1084035090440c0e0303003154030140001d0522440c012000008282c4810042d0601038100001001c240062011030b100d51070304240004070b54154014040054050040192486020424026517202e0303104002d46c000c00220200020a2082c00100c0e070000c0756034401c5805110225505610840d120050f1510403d0600a00707001c0ea5a0010000d4940741e6903445800343c0c00c20050f0701822000415682d2a46009464024040d545d5802501c01e41025034031058183d000460b00d58032456450103120212240602c0550804007000d1040c0d10741d03ca02e007100b40501d030356000403000b004040342d541c1e40100451001daa13103d1805225058658800300c030f10fa0041460100035241303660250060309c080d660090100781c2000d0900c0c400c0100104080c02005078041c003021020044d102c1c0031406d80c031400c0ca001d50540d2568a01c1014016 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 452534235 1250 452532985 452532991
    0x212030c0d1d0306072c0429031902010c030e090a061409010e0a0b031516020d050a0c080a0309050a0c080c01030b060a050901050d18021c0b0606090a05190e 69
    0x82a00020240040d0662111014103880b6100c81c3d0741808a19502c0c10100700711001411365041810302032a10311002303d0300044094000b03030307070ba86549550200d4101070322038822152030464480060142c00255114010003400f0a100f8101101d0444444000403030000048078500324a9840d608148981e415034a800580d00c04151803a89040d41006038010712040c0003030606c400295034003140046642d041229900c0052800c1c6c090016003003d4141d1000c0a403a040b10102511030841a1444280301e103040300c010496075601c0d42c0801c0840e03039070800c0581c842c0403141c04250726a0f0110000c031b00f0a00503508041c0c800d03031680a07006e161440e16410a440010042c0c181880c00807144202e4070b8001c104e13128103480381b811680c1c5240074030041e20307a03024040e1035080042c1344c0140c00c01141424523514205500841d4220030b620040d010b14074289248400003402407103460080340c081d0030710780c0c003500941c80c0042c0041859515400411244040780c120304030402003c06041188440c62400160 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 452535485 1250 452534235 452534239
    0xa03090e0708041e0204020f04050306060d0f111503070306030606050109060903060e1204082d0a0b071110020409060f03120507061d0d0e0105160212030c0d1d 70
    0x68a0003080181520707800a01c0078020b0100c000e0390443c4e661605040c0503c49900400454544144c20045a6150003a000d564080e00c5484007107040d9203052210800940e500443e400f00d6a803080d40d441c200c8002d45041d4581040341c00c070707500c0510b0b0154005036126005941d4001000d40c0b96003040c0c0d003030740c4859206c10305009010361306010080d031045216080e07030f402c8517020444014003d546458822030007061031050002041c04104105c021800000c0d0200e0f41b0402010052145062010700354050700082e410350000c1b40350800550b00c5031006610000c58101031000d0310b66100c5580c149446101d100880d11f03400202401402000d10520000c0c1030340f01000758a4500317543c0e404100c0c0412203486001d01501056000070032000d070700190b50246000000b65415098000300590360f006140c80100070038407422903820254811010b40b080c002c07803e4500c0d00ea0307002540074800070001a1398200514081040040c01480c400c201d1202d40071444e0345d800c42c20050582c040c500000c40b0044140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 452536735 1250 452535485 452535509
    0x9090709080a0314040b0307050c100b061b010e010f0c0207080c030307150f0603030302210c030a020705010902040203090a1b030305030a0b03030d0906021e04050604061b140a0309 79
    0x4000e080001030400320080d80f40c14590880d9074004a180e0b00c03030042d5440f01c4c03116070b0000200180141c0c040080d14661252030b04483c2e590550301d210300b003070343d4410500343e4104805100c00314a095800150020900d403a6000040044a4040c01c0e0709680410903800445071b103070841e42000c2541000840018090240038010b01050800044e84a00c06c0c0e0001400d5a40051030703200080c4925485000340b40d0264800f0403140f6039903c0e002d000382d002515410b40300c0c41000000700c05400c0b25858544034002d8044518070759500c503a400380094001c0207040d2515941e8016640058440d4030046010b2080c010080600c10340d2480d041e050340c402c1e540d03a0b4018000750034003000001e802c807050741d402030502400803940030b80110101c0d00e1401010302c401e405500b46400030003804100c2c1d0091001c00d0050f120940701030000101c2c00c0b0184a248201908940b04110804c00340384540c1c03000d210b005031440d072101a90110b1311030300b034000d4598205c1e56203500014104400c140d080031020340180388040d021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 452537985 1250 452536735 452536739
    0xb1c0b0a26030c1504020325030624150c0606080102090a08030f09010c210905030d0306060207141c05030301300210050d110c15090d051804050c09090709 68
    0x31641304c01c45418130014440c640740c080f40031540d0901c410905840306098040c0340c07c000070b54000210403a880141e5101e89404a50781081100b42c01100c2c0c1c580c1e10480045040b0302d44220426004010f5184d0410004040c42e1580010800e0045400a000721800562150303e05e41c1008086002a4418002035104000e45550543c0d01d40650b92410002d080030300036160700342000244501c8080301e03402c444010400b00034065400075a082d054920603000c43d094805048026821140240100c501503070001c0010000001864400040340c076014004801402d003014140891540940d42240d0366080440184802c00201a03101d2501103001400300d201030641c0016040030308e00d540064001d10241a10592450003101101d800071011041007203035040c5510745c1c011a42004010203032501518803031010004030719508a0107076220704041c040d203000360041581c1641c0141d01002203c4400c2c08101d10541e507034420203100d40c403c41c2c0c51541d603510f080100850190014100400d211100c101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 452539235 1250 452537985 452538007
    0x10e040201080a0c3507020606030a0611040305030c0303070e060403080a0c0201030905190311010c1704030311030f06010e09161103040312180602070b1c0b0a2603 72
    0x40b15000415050005582245000c0840d0480c81e600044510b080e504001083c40020003400c070f07036040f441a071810046440d81e04080341c4801054404540c545c0c0540702c4030000c20030360340c80b440314100850300071494a0359030f5641c00e00f50b0304000ca0514158202004010046070000b101015100048440f14500740c10740c0d230b480c0060f00410321303141c0420031108900400c69019a01000c0010780000840e485160b480b01c0c900ca4440e46642d04600140a0060130070b03110310140105070313100c00e032768079191591b4140420603040b1b010014025001c050315100384118800300000194000d40c2000700d200450316201c0009072074681d03246889402500c12000708469005940780c1041c003040c50340307010241d0641150301d603481c5010720b42002d080c0f550444010826282c10140318000d03207590280e00007806981d4007059032205124410302d54882e40070060441c98142a441800480d0b40180340014078804201c0415425a0a82c200d071082003103007042d00d40d1034000000881e43c0c20102c60019071504c494111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 452540485 1250 452539235 452539247
    0x30c11060610050f090a08010e070603020f0316090e04050304150c0b010302190e150415030b06090613050708091b060f070503041208120f0606120a0e01090f020405010e040201 77
    0x24040c1c0030803001081a4164401320f20440c3c4200c54020f103401e6443d40c840250a00a041c6142e40300c10f14400d403480060740c0d138041c0c001d032011072400e0703078142e030030355542201c2443d203c0c01801c00c0f00104101c0d55404100d80540c0b03c0400c1c052406003004540b140d0822030403180410307941d51080180b00319000403800203440a030303445040d070781d040e10740000440c0c00c001044031040040d0021407040340d648003085440b8440300e5084600e1003007200c0c2840b410016201007103520305c003800040c0101d2008000210319042804446070005e401130140029110840420340072240d0545040b4000f032030031002c2c0306100c5001c018942148500c505041001940c031b40020700359106441c1c610384455004140d020600405009590081c20858881c070b54108151070501c0e29035101d2034646414200c3e50000c900c54030380d464000c621800b0041c04251501000b000c082081440c000d2001c000c0603118085184186428040c4031070542c4600911400040e1910401040c1c450507004004032000e00002c000150781d00407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 452541735 1250 452540485 452540509
    0x414070b0403022101020d091104060b0c0a0b070c1217010f0f090f0e0109080a090816090b130e1e0c03120706090812010311030c061b0a0c0303030c110606 68
    0x112441e40d2080e16104ca150285c040c1071800e002d030034504449442402140407401d070b040346045034200620340d15070015059a0281e145013140e00e074801c04104002076030703e0002c0ca401680a003082410000e80e6a94101880c0d8a181260005440300d03410040710310145a0f13440c0501904003c0e1012603080c800d008000c1d2500d0301c2440041900c40c031140c1b80350f00480d07010f80d00e40c54081c4000d229014181c10f00344055448102000009041140d0000750f1000200d9207000328000c1258a00d80b00c1e2030608200c01420725551515440301c050306440f07020b000c0a00c201e44078481d00c14060000c0e040180302503082050001c60443c00ca40005180b10746035a004500c0b1481a1400042d4540340d00440c00c20760014888808000c021880001d1410044041d102080e412648a505800410300307000050688800d83d90f00340d250058014004002c4250034024403441d81d05203102142d6151842d41c64480b02d4074203d90081d030119175030701400034500fa0b05c03241010310110010700034003da00f0407001040c1c80b81442 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 452542985 1250 452541735 452541769
    0x9090c0403021c0506071d0a080114011707060309020402091201061401021b0d080d02030a1a060c1b0303070b0a020d0c09271b120c1416030302120414070b040302 71
    0x1d1f40348110401075a80303c0c8104101c0a00803038169512600400d00070094031485944a0308000000141c10f2114100c00d890104200080c203800c5240032802d6010f405004401c0342d200e42c0a000214007900c4500300031040c40458000405c5091400c2030a1703158907107842039141103411688212895446945083d1442642074403050301c040c606040c8200c1034082c031510f08a43d50f00010900101c20410f800409003049104d40c0f00700d02d8000c44042003030a108403040c480c404c0d00709000b010080625118088180700c805003d40c0d140000594a403555000101c982440b402e42c0441c640f20103070428420501c401c206400c0c00c095407800c00504010002503010030340c481c2241c0e80340c44074566110750001c400045004142d030800c1109601c014004110031810000240c0c50900401c0380584507840003205040002c5c0024646a0086003404541c6075440d015800c1c19001c01100306200c0ba52005903224038020600d200158806000c21410042554441125240c05200c1880503940d2241c0c0c0e82a03010340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 452544235 1250 452542985 452542997
    0x20030c090a1b02010e1e060609040602040b0403060204140a0b0414010201060302090114090f010501200109021c11010309080315040b130207030e09040503090d0809090c0403021c050607 81
    0x30000000c0192280c1a8000c9280882c52206044960150002c446030f0070a5419140b0782120180440500030a50210300c040341c0c85840450f41d1070524450007038103e405088007526003900c940300e403000c0390b1103644206c806a1f8002003c01c01d1100d5a40c00d103031a40700c1192840e060616049140d010350049014076a038080d03103c60500510ba000f5440300005541c0540742c1200d56a48901400500710780701200d501900c040c0f00022401d103882000141a82c0e016100c2110894102070410001e02c00c0704c24003c0290742e84c50a90026a48221500c003040301400c400c00550300580c98252503a02a03021388605260038030100c40000b400c0541603990003540302c1c1030300b01102503020004010700045541075411203140301103030501041300d40003043c0050107078aa81e4050503043c414041c1c00d50040750050141c4d0424002080e4625160a42ca20300300e000f12203140c1840781c0007000564204040e200f036040244002000c00840c1400b01002d0349031103441100e032100e40c1654507450744480c0d00074001010044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 452545485 1250 452544235 452544241
    0x12030703090b0403030f05060409480302031e100e0a2a121e05030c100b0405130c1505041e030501151a13090c03060320030c09 56
    0xc440e9000503041e5410001141c02e505203420090000d050b600b0020b8000ca0806d00003680c40c2c00c0c42e020f051403a56011441440d5602600c480c00c004000c21601c1c440b0580d0800000400f140184107005504102c03456002d010074610300c100351902442c40103441c9460040a40010b040d032000c43c0c4850986075030b4a010480848180c000380c10400b10810080034900c41c8902c0741112a030f4003140710700c2280790701f081250180d19480d14031a40113030040020444038030700b00d000718224002da1713903150941c0c41a030440742015071500002c1d0400d90090906203959540d01941c40c45440c141c001e09411001107160000000c4e0031707803105030a042a1740144298805110500b0a030f840c03103042250002d20f2400c41e038120621010741e030600001c0d0203210a030351a600341240405004600d402c1c2500300c0300007405564065501441d41700540d000038054001030000701800180620341800b43c0c9406190035a0005859411480c02000c44588a40c44c00b070b01144140b01c6032860344002540b1070710400101e0f98070150f0780d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 452546735 1250 452545485 452545487
    0x20a050705030c07320d05012901030501151b0302030906041206060801020a02031b1507030c02010c030605130506040b0a0f080705010509010f08150a06020709060801020a02120307 79
    0x21203000d10003401c0b44030000b062443c54201240341416921082078410b610504401080e140c070b04650ba40f45070380a80003401c481207142c0341c552a20a24400c0001141c40e46504001d0329408454811070103101040640d00400c561341485200e02400000c1c1c408446040e00d000300404006448a241040704405148201810300800580e84988401401c01d503031a511229410b00e040103278082280c0b541d0170000c01142900d4180290342150046900950510015400d04e02c0f80301c0207072000340414000c0480e5410404910b050a510544668601044885008100908490208a10608152030701c0003e00041d910031490442c0031180c2140455a500c415000500521a41840b540d21058804d40090406129000c500840d6800410ba650045c0e4460054a03070380b24000f0050300080103210300741606030003001d865400804a8450039031102034000401c11543d6280c03c080301582c002c00c0c080281540c580281400703821128000c1d400c0c0b401d488000303595071030042100c1d000310b440400010005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 452547985 1250 452546735 452546737
    0x40b060a03080d0c09080c090c031317071104050c0d1a09040c0503070e19090f170c0d050c060403110f07060509010f0c0c1a0f07050607020d02060108030301050103020a05 75
    0xd541c2044160780d40d10740d0a09100c3c020410f0340303908008613409002c006015400070075800790921010701400501d0741d61400401031648020940d10b100315012002c1400310b554561041080041e1580307a40d56110242450103c400c03124100b548100d007000704102d00b814005040c0c1c0c0c40503110120114000703030110b01c6e4000400441081c6500103140b401008140448004034404a0303500781d06659803e0f03151800ca45100e0070803035240c8204030313001030840282c202d283d00151459000c4d0000700d400d98015a10060b0200c2d88141c42c8003007800c01700b200742501d44103002c0b060002c111820180e10b00a40280301548442004001030240302003030061407200c40040c0207400c154800c2c001074528041d01ca00000d001500103040032400518100c0280445600a406040800d41c1144c0440e01980c901180c0b84595072044094480b0b490040c00880805002a0302078001d182c0f041c0c1c05082c03186801440240350109001c19541194010b40c010014060048112410340d002840c4c09130b9107001160b000d8400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 452549235 1250 452547985 452547989
    0x9050a06081609050c030c041a211909031202030702070b0f0403060b0604060c32060109050f0420010504050a18050601031104061b1202060f090312040b060a 69
    0x1d500800312606080304800b00c0900c1620111031081140d900c0f6401071804901040312550030444081006000300b410032046548e000c1e2074001d4240c500388105289400c02c8107200c0c540f0150389004014031042c02000c00c2080d80c5164aa2070404c06404983c5000b800c901e0401d02605450b0f60000103d00260b20a03c2400098444030054654500c22059600c01c542c0c040d12090700c42c1454540511040c2c0b0707004045034112419a614041a000c1603128907a00ca01480c0041e1300d80c2c21100d80c0d004c11003011104645076402040083c0c0000d40c50b2081440c25140c1c018000e112245289041000040e060003078103100c0c01c60301d50544412940700d401a034151113141c01140d03000c50388034400103013203900c440e031a00003400000e02800103441e2a8010750503502c01540740000002c00744403d00001c0d2150612100c8440003810003190402d09407503141e8483e03254110400140c000b0800c0049181c80903100c241c2090004005601d4040a0001c126181c680500300074101c0e00c400011602c02e6a42c1e1080f000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 452550485 1250 452549235 452549249
    0x30d15090c020a03090e1b0c0f0d020313211b3222020a02070b0a020307230c04182112050906060108040f05011503060501150909050a06 60
    0x440021a4a03000e951650383e0701c000c5000503d124004265a10040c59490140e14a40400340b840c03180006540ca050f00b061854138000d1068102c04d0301151010050040c42c80d2054000d10382c0c4034103ca02d0042d101d07110340c00c481c030b001000708000d059050500900b410b517986c01c60301200351030402c1a90b59100ca602940a0000a82038040060818080c0c001da40301d1031404520044185649900384200401104407102c105049150340c40c4145103c1c1c1c00510b40c1d17411070710640d00801d85955400d42980c0107803078010016400810840100540040072080810b00a8400800303007840c4e071521036442041d2188140195119145100c0102481155544882d8040c9003280082c56690f603500d41c800b0582c1c12000054001103c2041c171800c1c1d8130a05d0300450140d000b4244a60b1400c3c01950121000390003241d00ea494008041c0120b0420321a08003040c011000400c030342c40c03440c2050000e0320340680200c001a00381040c81f0b1a844d401140c800c045078611400400d680d6104010b680007007205030f10941c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 452551735 1250 452550485 452550491
    0xd090b0a050f0c010f050a0b04090201080c1e031003050705031c18170a03121112071106070905271b0405030a050c0301110408121c0e0d031d030d1509 66
    0x40705c1c4070712079000684203010440c07040100b1036030b480802040d1410610080d0215800c54003096a500200c1c0041c88403171030810310342002c049488000d41040d031003210f541071122490071042c01040070a000100c010700d011030040500d0b04043d9000c03603008030055020360902c652100d0130207030f41c1e01001580f002840074901e00e04140780022092a00e81780c14440031000140c01c02001c460030103051160064120b42094600d003460100d00c0048030300c85000d0260000d0100400540c150a0401c00c2400e1046001d03a880082d41450102404a00e001c0449206044000c04d543c0c00f0740d00c0380d1a00029404000c184800c0d50340f0880c0d0280e10100d12032500070301e80600403049130400307020300050306c20742a06040e0002c01440506e44604250f03405940200101034200311044030003603900802030280c0130b000351501e2580042c0066804200c41c1074428074040f5070452180c5075916500342c81400d91004c8072003400c941a04c800c8405c6922442110007410846607180150210401c00380d84800162402d07034410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 452552985 1250 452551735 452551751
    0x51309052109121603060f020c030313060605030a081210050307060c1505010f052b030806030d020d140d02070209070903021f08040602090303130312020d090b0a050f0c01 75
    0x210000b41d210281c09405503006003040b000c058000582c11220503c01060740d22113074119591200541030b1429600d540310303003e100d01126030400380000d40c003580000c1600781554180d2321303002e0181c1d4440e0344414465001040c800010030240803c442120401d141019284d91320400d00305050100c84d04415014410008040345540e00265802d51940c000d9005100c1340c03421800600030382e5024000c281d1074400d4144200f059040258105403064000a640c048450754440500b045007012141034000606100c244101070400f84540ca455081520240441410000f8098006505811800103140002449004220140d81651040c3e1340c01002c0b450a82005031005002e01c070107010030b81c4200008014444991141c02102100b50038940f152181b595071600c8200094200895082d014001000400641101c0e50710400203144030380d1307681040d0b49805000919115141040d0b2061100d000020b0000000041c29155050041d25080d61384404502d824546801f0f00145580c69600f04040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 452554235 1250 452552985 452553043
    0x1f1b032003070c140115080303010302061206130207060b100f021510030c0b030106080601090602100506182503060806010b0c250303020d1b230f0a020f0a05130905 72
    0x101701b034401c0f1082030703a200c50f1140d4206840c1e120a10000b9880306081102e41205c04060011640c0a03000410b00708580700b101900d0401da82c4040c40803196540c0c1c0306d010310210f02d80b000781c01840a00f10315120558118982c0b01a69486c0b2024040b0040c1c04120300084040b068020440042c50307000a001d03d6450b610014828140c00030b001b0341c00816400c4000500c19403040d142c040441d001c42c0e006100088030003940340010308001e400700b40c1149110662022444183e11800d00030201d413a10860700da07031001c41c5820155118004002018140361042042020010b23400741550b0b0160320103582c1e5000c014a142c900071508012150030f083d815034000792540710004000440f4040d40075035603e00d8078444c0490f068140e2424a0080200d403203e482d001c98080c4c0c61900c141660003464402c0e070314117000e01c14030340001802e441d01c1c10f6210411944c01c40c02d04034170a01c0d50000030b5823181c040b541484002105a000100d04000041d503c00d034201c14130070200701c0030031030007822020090013241e0300c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 452555485 1250 452554235 452554241
    0x10605090105030f0d03020f0d0903020a02130509070e190501080715020106060503010603050711060901060501090e060d02102a061d06060609031f1b032003070c1401 73
    0x41454458040203000154900340400c104c035520101e0005860500f4101c44240d0080d0043d105089502105200d16040d080d81c44c41003030001c1340a42c0007015284081c0c8100201c000100c3d8100503203609040500c540c1240c00200441a60040c4d400c1400503507814540418144043e004048958244800020381c014007003928000d6a80d00c44181c21034200c44d810030380c00e80b110740c810100042e0b010001004894840c1d0311494101d101854a081034491f134209807407400c0d40c00d444001142c0d540b1072040019680080409009140750f40341801c4910b00500000c908108079a0003901410091072003485251240742c421107a071084000700c0030060f507102c88610007844d844104035402460325060311507586006120f074035201012001000c0541d250000d01500b82c00c400f9171607401d0b11079680c4c501401212090b0122600c00ca08200103000d0800c1d02c0b601d50594030201e080c1e0207242c070345403040443c41d6030054180248000115065502d403600002100c0000300c0a102070a01d02c0010f4803060f0462040d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 452556735 1250 452555485 452555489
    0x2030a021306080405100e0a060f020409150806010603020703091805010303080c130b1b0601090504060c0516030507170d150501090f0e070e0d050321220203070510020106 75
    0x5a44005030b4407140b003610080e2080d02d000d40294003021390b104074125140c00204003540590140d400d03004c0f1994074201075840030302c01640816004182840503a031503100712002954904c1a0811f8070b440d05116035115441801030208050300020040180350045000c02c0042010300710052038203042d0008500100020701040300003c000354042070901f0000e400340e07a1518010390307001013014039040206469900440300d005442000184509002d034040c08028004d2002c4800072a451810f03180200840e40002c0340241403000074071402002089070302000c0c1c030403507150a026a6030300190801c2c610340091603a841c5111400051040c0785020a90071400a0303e200450b5603a029490381f0040d00c0e04006401a42070390804440100b02084c42404d446400c810542005641d4400b8100810300c004404c0c24150b40701e41c00020010ba17903641000c00b40302c01840341090303a0b04500381440c51982c0f6025150100040c000440c4480d001d41d6400e01580000381001482100d6184100001a001c1d110078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 452557985 1250 452556735 452556757
    0xe071509081204053a0302060f16080a0c030902100e150901050921010908030907090b1f112d0c011e023a020c010e040902030c0402030a02 61
    0x40001e4a000704506000c0ea4280ca00c011700b40800007010746010a1361030b00c0001c0541100e000f802030a040c0042d403a203210300507401ba60150400385800300e02c41000043c080e100c070107600600d0040e121141d0f4030461180d0810110000401d241500c83d0080b07010b800d8462020350b00c0080200880540350300000c7e010103440040c0c0d5081000f801003a1424158000e0306880e5011031401c0140450900c3c2c03040b600d000769403012400c455a074243d0f4044d613017115045d41c0202c415071400811b21039003600400916000300b000c0b103c107000038040c0101282440100116512400702c0e07082d20f14407240d02402d8200038200c0c43c3c0341250312a990030588034210002c4101040c03290784601504109100c0f001c500fa803044001a114801403210340c0c04d40c89564500740b00c030241103000d041c074111007843e04001081e4000c0e01c0c554103280c0d82043c0f60740302541d40c1014801c3c01d00359804803c000210307903048420840c5016045400140300082c0f400408c0c00d0608802100341c3c002e00c000104425600b80f40d0203090f0030024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 452559235 1250 452557985 452557993
    0x30903031b060a09030912030311040b04031a04050d0807020a12090614030c0306060c03120a09060f0c080705130906030f0c050117130c0e0a050103061107150e07150908 74
    0x8020381e5a003241e030711504c040c000411706034050004400742c40c0b02e02101c0e81304e842c0000d03e07500c442c048d0b00070581203500582802c3c030700010200705008000d5410f003075000340350f05845e0b2941055910603640f0707080c0144007401d0002950010707000c00c1c000e102c0c2020207170f00854100a400345890005100d80410b000c1c0c0000b00f10040f920041601031002070b00d20070f80904d00d007d0b141d80c40e540100241a0001c03524500c4074070080184c2c0b00d40a500d2281140a2005440003203403e00180c0303042000c1e10003031242c50044524100c00711680c03540c8905400d03003004003802c3c02e580c0e40b83c4012001d0b00b002c100d60008881d43d400e11800100300300a0031403848a03540140c5804030110f40b910300460705403a624002c07400a040000c0070400140c06100940700113445541c3e070641040e56051110305002c811a0201c4605035524010010700000380180300701140220f041918010039079440c41071034050105100e448560710140300d04100e404201c88005840c1c05c5007150445e64011400620310310301070085242ca1f0203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 452560485 1250 452559235 452559241
    0xa0b0c1b062217030414120f0a0609060515100e01030608120919080706050d02040e0f160f120209181810330905010915080f1e030903031b06 62
    0x404010b50741034030300ca00fa003880c4451401d403c07c403071004d031902d41c0d10b880c2c0500c51701e1800c542010080210302510403180440c101445082c40c008403100106682c0e14419945401c44807540c03000c0622004070f0450900035010081400100c000304600d4000f0001803084214421051884101030a10010201c80540b041c091980a0f41d000c86024402c00d0016403040d0030070b01c100e42c000e001404d56081006c800500b025030340c400070b035152802600c0342c500405032842881001c00340341c00c0c0c552000205013044012035200c87ca00402c9602d40d00040d102580d8040380f2038900e651160540000302018400d64000c40c1881c241031240b00c260706101422500c01d00c148103a014443d4019083d05418051000d400e100703d8280d0700050500300000700d0451902e0003004540d0250500ca128044c1ca450080002c1c5034009030b446e1191180e103600611020b920072445c50b000b00d58002120a904400c050000e40d01d51203840000c1d20310700074551241e40c18000030800742c400c0c0303460100980e10040902c1c211000c0351 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 452561735 1250 452560485 452560529
    0x3040816050a06050304030c0b0f1603050f01060c060b030d03051f031e080d050106110106080705240409020a020303240112020318030d0b0a0b0c1b0622 67
    0x6a86200d0301c0d401808500040009a00840141d64064002d08111030700415958406d894000122220f84170721a08005010041d0b441000701d01c0b800329142010002410444e1005d41031f802d05214040401240c018008108945074009820004025085036840a00050054090242114442061046454042e504e12003d941072800c982c1c004056040300c90140c0c40b8803030712041c86942070350381c1002080716101910103449881e009088982d00c900c2c49210144030b50f030965480b5407100c10158090a02400b0740d03580e00f00004541c02e4502e050381d6054581190340300c070340d004030b6111080241c4085500c00724950048010351080340c00c66072003120b209a841c442c135034141105072594009000b406110b6100d00c5254010740e0410005a16840c000904042442c0366500c26070401500981314020542c8900301210280702402d241c036007103400e1400c0050b00b181c0e180440200e10700c103450400804442a2180f80480f61003840701018803480e1422192141e810a490b48200d5002d01c0700b107956280da007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 452562985 1250 452561735 452561773
    0x403231605060a110a0909020d02190905011116090e011b0905040c03050106080708070219030201020c0c0105040602150606040f0b090f061314130c08090c040b0a0303050d090c0602030408 82
    0x820b0700c50306c4240c060341c14010190000d4000f2501ca81d00e550f802c00c002c2e941d0400411884150000036a0703588030703190809000600c4031480209001460f444640c40101507030f840400d4030196540c0300800038407240103101d0a0301510001d0320402c2c059076005031115605600c0406201503600a544c01d1001c6031100300214111030091141100240b002004a45868880d40106411600610403200c0e034458072652004810b072050f00481c0507039800030b01c54240450500001c80742c0002420194242460028041c0d2543c00c0d150542c001c030480c00c00001c0c0581d640e1401c0c0d030302070aa04007400c03007140e840311080e0000760700050072548541c10302189110a883d02d83e04484180c40501d458813071480c0350001e443d600424410506501c403000c00c0544008024a100d0186c082c202e80e03907824114200984558140414401540e00035810035140410a480c1d1254480489602d482c049903500200b05641006062516004000c0702045030001002d680c0040500300356110b40c1c00b550100300300d40381c040d194 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 452564235 1250 452562985 452562997
    0x309031b060f0406090219080a03021501081504141606030b2d06070605130308010e010b030411010309140d090b0304020f0906120a030903030905090403231605060a11 73
    0x8042c00c0703103000400051894000031075003480a85501c0c105881c0a48141e890149508030144503070090400340c007499030402820702c4148810310b8414095040061045d00c404c6140031540d003804020002c40c080011280400344034004280c00d4400c05008807201150b940054031403800000d060491001c22850b1804a01204803008200050710309400c0a180000701d410f0450554490317000e00840011818030b014107840b0360014018944480c0c0c040c50040c08120303060b000a901c1c800d5510050044000c002d003180d030819000b4001e5180c0d40120380040340600881c9000404400181e540400026000a0038402010094480c40d061989a0480d07045130701040394042d610004c020003000700341c1400f821160700204050a40d40042da038a0340ca00749842c10083d021000540800000c1081c503070300000300406890100e40910280c103168400420001c9440c0700000450360511502800f58210310440d00d500045c2d101003150078a6a0420300d480b500c08072240c48020b4149440e00c032000c12090110781c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 452565485 1250 452564235 452564251
    0x604300b0403171006110c09040605061c170904180b180d0e0907020c06431b05150405040b0406060813030e0409080715022a120309031b06 61
    0x6413003480e054048840550301c6d510a80b280c06401119200354035254115407195000c1c07000814903003040c405010100310480030a81c05194001c2d14040010b8000e80600b2021504800c65601c908016001500a240642e40c4a0600080714058402c2100361020302d440b0310080b14290071102d00c0402e41544038103041c0004000a01c0c05008031100d0710b0f0110442da0020b47c544121030400a201c2c000c244290300c50166104401145154409282c10f81c071805240d0080003032002c6445406140401000302c6540c1c0001c02c0c140f0001d20385901001a03640d49801414001c0070340101000e1150100c540340d000780915170145040040010723860401e40107200842d08540c0e80c4c140c031507440b02d82202184480e0b1000700c0800450000010961741c4500031000304a0107956119900d43d583d1410203004000c20001d0000c0724014400c142c61106078560600d40da00d9404103280075007030b985038168184010341001d4000310300080140b0520460020107449600c174000741041c2401040c0740015960310044540300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 452566735 1250 452565485 452565511
    0x836010c0846033e040f2301090e0a0e010b2101060f030b0f250e0405100807170a1b061101090b01050409051c050a140403020604300b040317 62
    0x2250003000d02505220781e504c04080da504064540342d440d5034070f0165511084801212035682e041c0128039503a00b1100c82003d003426000c59103001c005006001c001048401090b658000e64204a01c0a40100141d01401801102d62200050b100440700c903644103000090340c0ba03d44041001c030f00082c802e40c1507030b40121039041155103015148004400050120000654051408142c02601c5440f41e40d00215605c071268000d600b007082c00300702c2c4c4004188a201c1810b500080103c2400800d51a00f560200402c02c004507185910151030224082c8001740800a0b88100d0420000e00c110781c0c02c01e403580b555aa581460f4903032070860a0320700083c809440da00d10000100890302d410ba20828820340300300291007410f140e5001105840384003c400a021400004180e5102ca600003000c40410600748001400c007415500850400d002c0c2d40a050701048400700c20b4812074841c0600b0380e507c4a5024000410130f2014074200f00f105409a030100c0c042102d8102c481c0703850150102141c40340015038034030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 452567985 1250 452566735 452566811
    0x309010c0804050627070f030b130c060e03010b0a0b07060b0306071d12030c0d02060108030c100f0b06030103030207090b04060503190836010c084603 66
    0x71500c3c02c10154160301c1c00d1000165081030030f0b106001704401401c901c17101c0300c7c6e0347d0700c7d5007808003040c1d01c020104403203514101303d607000003100c60703400d101602c005180c030358001000c8501103030041140c2d54400c0e0f4031024100c1d000550451410003040c4642c4107a4007440251200020305903610000c0e60044046210250701e24a100000c040c40c0d0840358000340b00c001e11f494030030001402c59001690f12801500451300c400101030301003081900400d940402540f400c0220120f8a444895000409111a4a400b500703041d1390501c1d00940c0907540020b020550b696035a02d80659502260b100f002e0040d820080b01d1040c40c9045c0c03142400300c2e60058068200040701c280d00001d03003000044119406d040034002c0c11504036160700310402c031101052031446403241c500c00c1d2034074104680c0799444c100701102c6880e200003040c3c017003540da20f0020611501c03220115848900c10280c0d2580d000c07170b190071200840d600300c030441550706031109403a80c81c2042204510000051200c06908000760721944075040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 452569235 1250 452567985 452568001
    0x120f070603061206052a03240607080903030405190806070c02090c0319020a0f02070b0a05040608091002030a020d05060a0302060f0f0c06090c0a09021c020a0c02040606050309010c08040506 83
    0x80325501604020610029114210000e600f0075140d506032100061b0200410840303c0515013110b0500c0e0304400410703003490803140002c44510900d2801480b000010075040c4540e2810002e55002d440000c0480340c034802c071041d468045582034410004503220b01070214559034025610128000d4028040001039910603405102a0f803001c2c00303504140d101c1e9044040517032890320182100411540d507000c840d2590380c1d0000d1510b0b10315081203000c0c02d402c00c031030190590000201c80c11110b89051504082da528207000303092010311230500c07081600020400007030321030590050044a415101c03c00440c0c03107440030301c0080801401300a400000c104610203d00400e8009400c200c555081a245840781000445040010544101d000c0d07600940101c4a1494182e10000180218580460501680865191700c4030132002100307220a90001c3d02600c40f46c81081807105064001e0014001140d892170300501940c0200c0307075140254030b4500d0784107c143c800d021180c0503d4002c030007040141c4801d46 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 452570485 1250 452569235 452569241
    0x1e040b030d112a1c0b0a0b0127171005010b0456040e04030206060d11010f0c080a020d09060f0e0f0a050d0b1504050702030703030e010b120f070603061206 68
    0xc84944e1480840c441c11000a140500d01803040301300820100f02c00039984005400d00280354400389004110516016050407a459034000305c440c0303805082c04410325888814280810079492120050500001091082040000f401103a03900a0b1140325411090380b0080204a101440c0c0740c0000084e140310300a4406901c8036000840100102c2c00081e88101000c0d03eaa000d030b800171811405580406c0149a01404469404031054410035008225640c4e03040b031805000d40c805050040500b00d0a102c42e100710003000c2c105500a020b00d03503411040701c000c0e6890010700398100c0010103181d00030a0640c0b2442050b440c1f841962145101000848200505103641001d00e80d0000e09e00a00042c0a6450f00140200b06000740c012490f581052103c058004450003400c60082e8245014044203560010446d24003a40502d40011602286410580908000d01c4e03a0747d880020400149010480031411090300300c61a0b04440c421581ca41d01034050320840c3c490075111070b030151a540e0100348950 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 452571735 1250 452570485 452570509
    0x512070c05121c0504090c0806030d090b120a140108060f0c0a050a03021b01020301060504060e0301050f011203020a0b28200c12030a0e0c0a051e040b030d112a 70
    0x13040007030030030fa1190340480807503000c180d54500044021040c0512400c082c0108603c1056514045401c50309150003491b891048003181c00050725074400184008101d5803003610326107003032906003c07070b560b40c0c1414a540361030a407150040d5441c2c1d00081299444030404039840e0860f82d8441c1400d08010f500150f000750006043d0815002c1205a480f414410178401540038049584400751201c5c280b400003080b4a120a8603039000368034000600c5135060038042c090741102c0f1403502c2c04c580e807030403480c9c102d040c103000c56002442149284203001d80854452070200200103103000c8000e03414002600b240070740d42a02c0c400108030042e4022207860b04440c100409403080303440d01701d400c141048003025519620460707074505c500c0e03030fa05182100f102e01803140e91560102220b94156031414000012150540da042c45425685843c81203003054589800141c0300349002825036481e42081034020b403c061264104040300e0207a00d281c1c3c4802201c05808a0f002064010112400030894051243c8413000b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 452572985 1250 452571735 452571737
    0xe031905030d0615090f0e221703070e010206060a12050703050304060504230108011e090614091b0405060d0b040c031b090e0c070f0512070c05121c 65
    0x4020004802c0390354002d5038010500418840140040b0540007490303818950032020f510540780c8400c20500200b022055048003008507004400e01310030103205104402d480c07006006040c0c40c9102e088103606100618490b43c85c60b25080c4e854050103004a882c0e5000310707009644005d01003020301640c3c41180341c1041062098040300c00c0b1644984420345960015408880002c3c0b0000b0107214a503041400703001102e81c0d1000b2080f1a144200000e0907222050189907407500000140d40419041c07d6110710040c40724410811249407600883c10905a9410a5500840541011415410750b2000302090505030b00c0801e81068200420441076a00c4081c2d9a400c95441d218100319603030361485521030640d04d5490001e046c250084200e03440710603a900c601d05003c102ca80411489010b103491aa010781e40c04002d03a0f035074501c0d1401e401000c82030400640180314044c0d0030380003400c1d00001000d429000d0451000707003544c0e64041041c481082ea940c803c49812115032410030b001c444158217819407032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 452574235 1250 452572985 452572987
    0x10203090303041403070b0a020d14090d061d03040f030623010e1006020d1d15070b1807060c03050307090302060a03020406170c070b09070306050408030603010c0e03190503 76
    0x1100c00002c1c65a04181c110002c82000d40d60b003081c0c5403a04200b2070000b020385102050904001d4200a500c400110b8010002c1c0f00040011010021140084401ea00401400400031a07001c0c1000d00050106400254a10102001c00c00700b14000000340e80072a9241561071400900710b54600c4098858122280c00d400c000e00d40700800401008541341c0a000c0c00b40c100126440c0909480080100c3c592140f01550072024024518940c009281c1e00d61140666803040c410408801203041345000d03074074442d540780c408206881008001200c0c103010303010784120405a2081c2d80d445607154041c070301c61038012030341c0b40c42c10400181c0180c1c09103030304c0310305030801507000756a03034001c590554401003a1900003540000c0a000082c1c012161042c1050010b501c411503181c4050080c1042c070030000c000d0002221440001d40f4810104201009154003130340a001c107052500d800c0040790001e0368094400d5013814224000305105031108010000000c0082c1901e681651a0200c00d4190b41800ea4442c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 452575485 1250 452574235 452574247
    0x801020d0b152b0f0504051504030801060507080c071e091b081503010e01150f0305060106031d0f010204172e09051606081b07200d0f15020c070311010203 68
    0xb035500c1040c00c2e040805102090b54601461f1080c03c144d0201c4044448451840c00d21001c02c0d0700c141414107592075401d00565581e041e00b44584d090007000211751451090110116020b007074412201304603200034030040b558070713281c41c01c0c0000da889901c08480c0c402c501e10414406913110f2841550040c2440c078100010f405c641010a0035203a401000c00204ea444603c00f50a040079108145d00400c9c0b00d040c007043d240d0541d5110b988960041c0300c6c000c01c05481b61003442e01000090540c1d0031901c0c42c50101d0b881100c6140d02a8080d4106110762030280d4504110240000e90105044802100700541c008018056158140d082445c0c60894401d980e41c883c404d8000580411094003128041040403009500e0018000d00c4444010160310310880e035082c4107100c0000c2242901c48440e4414004c4500d8140400b42440942c060386110380d229203075000364014400000f48502c1110700402001c240c41e034a0107281e1080e442003420040003030703000000030000b160440c010b18062800510549282c54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 452576735 1250 452575485 452575567
    0x302070809041a151e0f09120f060a02040e07120f140402090723070f080714070b030c07031412040c0f091b0c0507050306010801020d0b15 61
    0x51101c2012074030f503d08034404200e203103080701011640741c1000403458901916400d400b03418040c2090002d82c5d0000100341c4000341c002030804c0c1e411307048001d4000400c00000e05a02e91b5950400c1c0c540521b580900b2011500010090003180d0658401503020141601c3c0c522044810a549550140d1503581d1408000d18001b00c80c013405992174401e40065201d824180104045000050004010f002a40c1300308004000c4101c001d0110116032621a900c5120710700780344654039006040141301d604001001d000300001180d18020a015440844101589508032510584026a44418458414020034001a205100800e0880360315003040d800c020049040c0301d01c404054908131401c0e60007000a0100701c07080900c1500600c14114180304404d00b0540340e02c03515169201120402074500c21010034003400f044040c0040802074101c2d42d20b580e43e114128000c1d0440b05540090713904203242d018462401c214203139680a2400300c501d16107419031000600e0880401c1c844101e015111142c44040f03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 452577985 1250 452576735 452576741
    0xf140118120501110306010c0b04080f04090c020f0c0108010b0f0c030d0b1002060c040504270507080c092511030a0504030204060b1206040506040f02130e060102031207030207080904 80
    0x82000e1a42102101103629142c0e0a640e80c0c00a5411103400c14070400125a92012042a0558100c0c8031142c450300d640c18007072018425242c03d00000d0b4000940050392a4081c3d0100c040e4000e20b44c00c0c1d41c040900c014025443d030307080000050010364494014800d500c28800100030001c01c0c3c0032064584003020b0903207030440e001880818501540c40c114120303103092160121a07200038900c0a80710500d0000e01000d030714000c41c000c00c0c0c0110350324146050351246070442084c1c03040c0304020075903100140d840c08030758695060182034071a010f01403462155007000c40c0a60b0141ca0b0740071541c1c1820085604c038160702e40f85c540c00481000100c85030305d1040b0400b030004050340440c80d0382c3c10369614110300601041d140503920001140c07e0030400c482c901000074000680180c4211000324840d2580c03400100985850155410307014400694130f060340126003801f404446021030241c00603170ba000010382c1c6034020128506900001d01c00014a1503110341e0080804604c01c0c2c00386420716200c40086422 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 452579235 1250 452577985 452577989
    0x3110d0209090a02030f030301080a060c0e030613140309010509091506071a100b09010f030b060c060a0e0a020d240f0e01060b0a020c0d02060403021008010306050a060f140118 77
    0x150f4214442030801c0d81028401c6500d5008890011480c55140003141a41e8030103400c0058180783d95103082d800003520903c0118114030004048503410b0610303401c0c218555045507401c8401c60301c41c6598965815002c0182c940010050b1601401d2010746001d216903e00b00412115a0300c030000b400e440c1c99504e00e40607002c240d0203288075190541e14144405c08404004d800c020400160744401c01c01400072800720351180d0b03c20310341000040d580756426400b03003181c2d400103544002c01107004484191300080703140c4510001c41e000e00c141c90300c504502d40c4804500f400a900195001074041c04101e101d0101c00702090354011075040c0c2d002c2c45605d2030446181c0c04043da003071074a0300c0850502035424082d001c0a00001c200852901c0d0005c4c038060751720800c44c50178030702841c01100d01d001550f03a1542a540159000342405c070b104000c401e401844107100340821500c1c0c61400000c02d02d0f00001c1d1040006071100503d41c2203100b0304000500444480c50005541080212203000524411403600100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 452580485 1250 452579235 452579251
    0x40b03100503030f12010801060f0b13050307090b040f0510030206070f080a0e011e0206070f0306030615052d011b0501060e09070e0f0708090f03030c1c020307020703110d0209 77
    0xb866050175105800c002a060b481070f00d00c3c0e814210140407041d60429000c0c200d0348590700c00c41d0f03901c000400350179031481c0e00d902c115450b02900360005690a8a6000b44070b0b0700c030084408000846000d47c01c0004c4541c2940c14146400c09800d0500050a145d0001e1000c41c1c0542c0c0c00665034100e696079010aa40403d83c0d650001e0840001400035507080348802000705010044c0e1070342c1c034640d030360000d55840c0005c0c03840c0300300500c540c10510528000d51000c070140d5007200c03003844001c0103d0984103142c0c401d81308190080102042150700c454030600d151419a00d04000000e0755860440111001d0203c0f1120003241d824402507080082d800340f1a03503004080000c071050f200c1c4ae1441416090a465512540c20009000200455102006009503229404d1304240c00c103034440040f01d0f880c20880150301e1650780f0000090008840302c0401801d550501c8560540c50042d0090050003680800e840c05405070740508000c0c4005014551b0b070242d4903201828861008105800150003074200b0343d4061 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 452581735 1250 452580485 452580487
    0xd1503082701052118061006020715090605070309180920030c040507140301031b06050703020a0209150303070b0f0603030301060f05070510051504060e0c040b03100503030f 76
    0xc40441040c1d2035115652000342001c6040c0007010302e01e510000c81002880d44801031001c0007401075102d04100ea00310700384c070300e0803a40b480c0f91401111000000e68010280548550240003514003e40d0407101440c4640f03070766420004e840c040050f50540c214a01c1241880500940441c80391081c659050740130f54481c2001c10650000d051007846001a00d180380441150803d00300c200313071000602d100105406650020b00c0d50b0760b501c1c0c103d4101c20240307000b58200000100000030b000c00d02a00400702c0c10310150400d031003507803454140c03030510507140300401580048a419000d8038100320620b0388412402000c0b10900b145e64002411a4402c1200303c51150b206000d001c0f6141c41103110680c4075100754000e500c0c65041c4500903145080c81e1086004200000501c00d0801c141445070200c01c001c400030a10144c01c190444034464455103044a000ba0320f4850300140000070b404205000d458840e40440ca4141881c0c0711041d9a44006d0142509006c3c1803c0003540e51400c000070309854203003040c42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 452582985 1250 452581735 452581777
    0x12030a080a02030c0405190b07080d2f090d0204020c01020406020c0a030215030403020114040b07080a090b0c130302130221090309010f03090605070f02210d150308 72
    0x1802854001c0c10440c05544148104907004910750200d9080c3d5600303d881034030f0414009007d01040a01d41c1041203090408110202008940c2024141042c604c84060081601c0016540c41c10b030b001c040d01c0412460075954004041190f00e001303224131320000d00051113685694004c01d003681c0c031842c80c64419a60002e002c001d41075040c4844641c0c003404460b1038103910f00d142c0000d00603420400140e20881400400310702054000d5000c820342d502c809142500c2450070342041c100b032203011200007002c00ca0075000100c1d05409885a02101e9031b001910704c00d0390b1940c0c4c540094580004010106508038400040301507600d4010702c17200007400d4880982d5480060900c188101488030044007290b03211020b1100030b24001c4180c0d070b407051080ca010103103908030003011005485d07d190094405440c0c2414494802d51000c400700486895408541400d402e291a40380c5100d042045088445c8050114040b0700d43d080d0003a1a851b61007c07480c2d8019a2240c584480d941e015101451001e052140340c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 452584235 1250 452582985 452582987
    0x20703110f06090705040b0a090203100f180e06040b01090b010908010608010617120d0b060405090a0b15070f020609010203120903070203070e06010806040f110a0c20100804050c12030a 81
    0x140000785c00240e506104880c091000700301951814002c00b4491a00440051103104012001c103008150003a0f0303c841c469520300d1007554400000031710302c00740c6050401c0e41d010700c44001242400340f54000c0c100d90035680f0301100380780201705104100341001494030300021100c00c04d005200142069000004280b45031041202d4001c1003894622019081701070892a840c61904c00e9800001e204000864201011000075120380300e50303004239a01a03100810300000304041d0f8001c210320790060324103d100b0900c103040c583c0b041c040c0b10b000402c1d065100c108840107092000140100c00c8043c01100e040c032040485100810004407104910307544007140d040306607c1c0820025000b840d500b8007100650130302d4400240b903100018100b50155171a000000d02041c0c4540c13058501002c80050f013503c0340e681b07000060201c0c0d4014000e513a00d01212000242d0f1038078090001003035050041c5180b114003078884041d95107000c024026036050180c001603020702c1d1540d00d5102e40e4045040042c5680e8081c4501c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 452585485 1250 452584235 452584243
    0x21050d020a02061006090b0307030b030c04090602090a06051801110f06040f15060b121f060e0a210209040303020d0c091d0712020f1908040b090a0b0406020703110f0609 74
    0x4001d170100b010100003002804040d40413030360003640c0ad01e030215001c1040c10100e840e1500c904d1403550020701d003007480810300c2500e80c09828800e508540381f1007507a9070341e4070458060186542200b0400c2c150349841c445580110700c503c45803400380f8255050948100051820010111820303904580500441e104120080b01003595680401100300400707400d0541110311790061101a01d0301c2c50444010031460403840d40c145d11001c15000b540716035191900001000810511051401030b0003442c804148410021a01c5040d0305e5401cac0c036125440c8036078003002a030f800050015030904d5030170040000040d002d40608400d095807a110442c0b04c500d0240048100704030111200c01c42c035080d4044c454019408440250b589a06403000340e100c04e41d500e051031180c4248000049020f4030701420342c1803a50440843d501c40d0b4060000c1d036500d50303121080387d0785501d691800140741c108140009000030f002e0b9030103412183d000b8680400c0340001006131a2a2010794105c00e000b5902c100104200c0e404200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 452586735 1250 452585485 452585489
    0x3040915120c2c01060318050628181212020c06070e0103020a020a0b0604150f0f080303040503040501080a021213051c02151e010f06140721050d020a020610 69
    0x350155680d100c0030900d0381c40703c0c5018014201055115040714800d200b1000600020a0b001000d0703617078900b40145214600540c100c2c3c0381c08100c50140014900c0c05c000e1080751000084502c24140c0c03860660b0342c185001e18111002c2044c0300c941e01894040c00c0d0f451000d0290b01c280d039002030000f410a581d026110703034040d0840c581010300410080d5001a40812140380080e0703c030882542c1500e54000240103448842c5804006501d07540000a0700080c841c10801211362080142e0f07442600c074041c417900c2e448201c0340980550b208100401140d4422140c0a601404c0250014141000020440111203060b0f58140349400c2208058007480700610541e00b00075a10050f02c40c9075020500b001e500c50310202c0c1104010b06400c0001303010f0502c49903c60495000450302800c00e5030315180d01a018107494001c18000a0328015030541ca01c42407400c41e40c24075000102e116003001c0c0a280413030715000480403c4100300c07003031208000700e05083c0050000d000c0c10390058841403600091450f4284819 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 452587985 1250 452586735 452586779
    0x31406010c030909020d06080d0f170103051b0120011401080a0c3503120901060f03020904080c01060b0301030b0c0a050414040b0402040b040503011811010807021207030807080708070203040915120c 87
    0x110bc0100700081b00025418140168040b412005010700001652034134000c4003044040e1060318003c0412100640c00b103044000d14800c00300342c03a40c80e0001c0c01d54800c105a4010940c0150180c10b1000700ea65004a00084200c501a0070321a100b03103600004111042401103699480459030740005040385144541c0704d440b0000800c4294682540d81208044600c8068000c0181501103010f014034042160030104004000780403c03544c0381a1041217038030901c000c0d6445050000070422070b070340110032034039541c08550b40c003800d060400401090075005103681c50b034001d544040039503094440d030000c0c00082000550440d10b0320302d41014942511241050048240880600d00c030005003230102488165008cc60130016a60f10880268541004003e6040c003000c07000c140842019841651588074005960f40c0c00e01648880b41d0a0740c7d01c40f402c1d80c400c0056001400280488801075200f4101d4a4102a240b82655540c030944c0440882d000e0082d90b9022038100c1c18042c01c2149054409a401c2c0c1d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 452589235 1250 452587985 452588027
    0xf07030b0906010c06110325020105010302010206014b050d150b0604030b0a0c0e040c0807050c030f07050c01080f0f1b19031406010c030909020d06080d0f 68
    0x1040010302008004280b207042c0704074900000d081c021940e00240030400d401c5641c90342c0f401d040c4601640505050f00c0c0d691041c40a001d071368050351040c0035850480b581a0010004da07402d209a10781d041000c150350030a80b1000c12100286101482e078803102c400b100040c000350071003001e54441850303141900818040c40c6502d081c040080c0d296264100032060314000006c10010b0360703000403024030039544003611000e2440144003443c40542e001d03405100c80c03629220203010448042c8030640341d82004c444040750b05800054000760080700148040741401c41070782e00d0818881e202400380e41001e074050720380d40e111512013074055810404841d080200300790513440c14a0660a0944080c03001014180c002c49800313400e0b4001504041070b41c502e4410048680c1c09025000d0317000b40103203600d19480081a04940215085500485002d07004c0b07901070340c8425080342410070440107540729038011070456075680d00c00603092005000705003003503c4540c1c42c090280c1d605000281018104140c42e145010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 452590485 1250 452589235 452589251
    0x6160e01090303080f040c030b01081b0d050d1d0406060e10030531150902030d0302160602030612060c030108010b06040b04180f11040303090e090c010809120d02030f0703 75
    0x500420f44980c082000f03040141181d45528207e10322055950009144102131400855000d0300800c842e40f801005040006e440c104407000c014000718034110140c82d64005048010b02148202010590b20b543c0458079440c42a000c000314040b201141d1042d400070340f160058012a01d0301d58100751144005140510280c2445424200071401c11840f6400c03004041500e0300e0004000715802e031820341c2107200c0794088505101c030034001d0070301088200e20a02801200d034400c41e00078803c1e900d24034001d050703107400802c403586c0e40b80c005d40c0041c00340303a405182d0b51042c4c01c6441080103098440c110700c1c8441500e03940340003110350070750b05000d80c501e01c24002440140070181c0e8180654044400b603294403081e9001c3c0c1305c41c3c40c0c002d00003e206a040542032602c01c2c0c3c0455000001001100d00c40d64034a03441c1ca0b9242d246d402924019140d210080d003203907460a8440d84110b0348140c00a41d80400d403261402020044c3c80305a01c40c00883c0b51154022080100c030090b1001d401d1751003e2a400e06001140e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 452591735 1250 452590485 452590487
    0x1801050a0b010927060605180316140d05060423070b03040602070602191116030803010e0c160b040308070c0b040b090307081c06120c030303020d0e06160e01090303 72
    0xf02c180a44008200c8a40d030744100e412081d280c01d032407040100000c200d01c035140c8030001d0850384015441200a884842601f80c1400d0004444840e0760205582a00040c00c01540341202d01c1032030030144d800000c5855500c0801d0081c0a032602031440341e44910f2001d55101d0040c14080c040c0540f00110f500300303110400451140c01c1c00c50340e01952142d001a580c00043c82c00303800a014038494410414400d01000403115040008215040d0704582140c2d01032500005003001c00d01c05000c010301a90f0184010000248140659a08030b011a040b0504003845140300c0012481c5440341500ca041c0c3ca034042c4805c0c160000d9209400914501e404100881c0715107400303420860160006001c01400d1b400100c4080c03003030080d503a0031544851403994402d5500700200f2061500480303500045d06d8480c00140b0301c0c101a890211a541c0041585215451034406070020340100802c000b00c2ca48641d494000f0102c01d02800c8d2103490305801100c150110038000421342c0d0a4000e90b1414002d40311800d00c082 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 452592985 1250 452591735 452591747
    0xa0525111210021317060105120c011e0311030c030a18080a080405071815050d020d03120b1f09050306130f0206070b16110c01090302010305040f0b1801050a0b01 71
    0x1035500c140b40076079142d0760403e0003054102d1136030014900c46410300c0c04099404010a12038121001120389291702e40392000c2c581d45440080f03d0301c0b1301144945590391400c091104c840b640100d114140010002800c030859603443d17108881010340e0030f038000100410030403507200ea211402408180003820051541c2d030b0801920035500c0074018002c110001504000040140c5d001410700395890440c100c1d06490720401820460700c040312003940c44c100205584c02c0403401180303542d400030540110030380036480583d00b80480b0002c08215646580303b142c01034072000d000003032445c1c0c20480084012018032000b0814403403908450300c0383d0440782c28403450466140441e8440380e00400205034103005840010420304c90800020b2201c5140420048440a20004e0f54a0310000d41c8448050700b88071170382103403552a002c4420f40810500a810310242d440f079800207601a03c100304180c400016625101c0910000300c403e4180300e40306110340c4007036100030300886801c128601018401c0f01d03141000a041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 452594235 1250 452592985 452593003
    0x90c020304150509040906112703031b0102271804031d0d02030105040501020a0807020607050304110f0406090f0f0b060708031b1801090e040c0b0a05251112 69
    0x20081c3c04240c82c41c203607440e9070142084503804a000c001130401507142e40d20a8000310580010217081030000002500d8000105070b134200b00070091442d201d00c0c0700d4801000c0c51101c5407001d1940d400e1044896094000c1c4aa0a5461000316001c41502186080120300500342c00000441070f030320f400313100000b41c0010415184203010540144544403c102007100c010030448040d5042d0f08060600050002c10b5004105a42c4655110a12035540c02401d036601c0105640c424004ec50800003e404a5585951001c9400005151140084c42d4200103000d03203038560011194151390341c51a4042c131405100743c0a621004039000c2c4621840d640000c4c0c100d01640c400030b0500f00300000060030318a00d0030300104110000e09036560301c1e000747c2c00c42fa20351000312404d21030115003800c0f804203241005411a82c41f8a501001d10030b94181031600d62142500145904000c0c0304051102600f001c100c0300340900302c82d000b021f65000550341c030300b00000c039a5516004a8000c83c038640203545084e8001c290417030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 452595485 1250 452594235 452594237
    0x180806090633150906131502030703120510170115050a080c090a2a1b11040e0c031b040f200a180e040506060a06021504080d02030709090c02030415 65
    0x55880c01024400150f40304500404c0d61090001440188802c203401c0b141c8281c0b01010350501c650004541c080e41c1d05d22400e0b8000e00850442418512000c90a80149902c1010698481030b01c9a030f0300994031103501081c1401c4001d945850b22840c400480c0d171034039001040c2c104c40301e050131803410000684902c001111035006024610000c1d8083c02c00307030000e00c81f00120010081d60f1152548020400ba1000030b11600007480703010500a145942e1945c05100307640016400c039140c10703a40100720041819482030360150007150070302d01880e40c040c840124405d12007921a48580c810b481008100d07880100d004c0c1310315103004016958020650110000303c98035401c455620880100300782d400d0000b002c6071060401186078086020004030002e50300443c4039808580c3c03691503240400c105105c081c040e00d001613100c0900031100142454480740c01500868000c1e20344868041c1140c20b80c0d00c03c42d40e00001ca84059070801c9210414410250880c485201941c00e0130305244e0200c8901c000c0c090050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 452596735 1250 452595485 452595499
    0x30c010915140c03030408130602030901120b01270f0e090307080f09060d0c0305150303030613090f0c05031006080606060a030f050a0c031a10180806090633 69
    0x1420100700e00c01141d580f038061400712516480d00d0f2901d00c1140d0f1000b011003121034854000000d5050000007541c2200c030050b100d1080c42c200e15a000402000c084160b1410002c90004c1201c0c0c10414a42c00d04d00781398007810309209541800d0325440c1c410f669910140c1414181410850400404400c0d6460755500003002552055491003007001c0c6d0050044840c0d22141c000381800c081001a44011201c850725107060143d81d6401d039400c030301c5501c102c4986406420401c0007460300d190142c01c800014003c1d040c0041c04180688401c1080f1482030012036120324001824082c80ca000c0000c3c0c0d0b0059030031941403100031308001081f9222540640142c1c001d4030045000089240a504007a6480020030030400251415040b40000f901240c542e80003c07900e04005003c500442511038441c0350740103000744030f014602d03190072258542c17a4241351300034203400320011a800106100c40d0380034040c5500141003c1c01d00c51403014803608000103003a01285c00d10703c0320070b601340b660807036010424044442c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 452597985 1250 452596735 452596757
    0xe12030103082d041211030a0f120201020723070e04050703030c02150307030b040b0a051509040e0607080121030f0e031002160c0503031e070c15030209030c010915 72
    0x20303450000f8140d002485140200e0080398082c40704130040006070040d52000c0403400a08145501e42243e00000317013111b003607581502e0110b05c0d0034a549010548602c0010f01d8110980c407002440780ca1100309100c806190419450503d030304101d01c0e0090311100f8100e09081c1440d80e140c90342e5802603c0004c0c140000407000368107541e10540e090fa81c591003000910307928602014020700518a82035058030403440d110403076249040c0302e602403046d41c0000c0c251102c4007540b4206640c0030f82101440950040d21003008419145c0184407107401100c454584030459410b100100c007101501c2c1e0740c9102c680c41121a1800801d50080c1000703e025003e0808051480020011030308280c10502c00e0182c1d01d0000504070b400c1c11004810403038080c05803400c070003e5500c840806840340310340c0004080031001c003035030742240e620014010044607103c0c001d859140d03942c801710004401170303460480c40840c0d400701e0103800d00c1c2030904c043c00d0003440901e01001c2190900349401103800d2a1104441000f01040c44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 452599235 1250 452597985 452598037
    0xb090d08010e340807080601020a150f06030b070305010e060d020136031703040b0705160b130308090705100c0f02040e070f1e061d040c030e1203010308 67
    0x4400c8030300d00704040e03105540120030650500452106680d00159010002030001c034401c0c1009409500164061310140c01cac0ca80307610f4801104e1140a41d20184d860000301114003180c4510001148102c007602c0c0e0320f18041001408a500580c0b00322017103a036100c20031065946421074403901543c2420030740c0444414642e450b0034044000c08282413481e040c0c010030410030002c800302c02181d10901d11703404c00000e034040c00c2d03000d400155001400d4103040004600414080c00c00340004a2145100c0e41c0055159160320a62080c01d4600401c1d107003400013a002419444011990302411207c0105070403450704011542c2182c490a000c1c003002009001c00701040550001401100e030014824400902040001e58031440380b0f100d04024100c0e20400040c1014858041c14078a00803803260302403003480c02100340c45000070303000704060525541c02101641d039198402c43d602102c00e0b580c002200c00107242814500b00d0042c2e41c40114001c240010000a020700007194004503890203030515003a22924 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 452600485 1250 452599235 452599261
    0x6170705071a01170309060405040e1005190b03010209180c07060509030d0c1715040e010203090a11030c06030114030102071a04050118151e0603050106030b090d08010e 74
    0x40091501c91070500b0521108401924541038034084000703041080102208299603201794802182c01c02001d01040015107090b07802200310002510640f1100500c0740c007024100d13101160380d681741034000482903074011024880d003c10240190021031514001e00006101d80075080d203001d4000c0d11030710000741d1000c20030094a20a84c0d01c03400c01d000c5800e02c1111503440381c02200742c001416140c6043c144210b48a82c00891141c0824007000c680b60700c0d10f55661050500700c04440d5041911003101c3c0c10940780902c011442546920301428052001c2d14000b1089221400d205103c1d80c4032082401c010341c1d0310000c40f0b0448502070f250450b04010140482d019002e020000741090459060246c0305201c40000203200c0c45c80340c0003c2100c000e090007ea426003282c10f02c040c2504201140040c01c841956010385243c1d100d0702c0c0100700c40d0500c2d4020000740c0b8015003044420380d466010070410084240803d07074115050b4000340c0200c00c03c00c00014258503051181244070414240401e202c085024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 452601735 1250 452600485 452600497
    0x103031d030709140a0c08010b03010308030603010b0a0603050411031f020d0e030708070326060d210c15020328020d020d1e0506010e060d0e250b0406170705 69
    0x40000e01540d00240013550240f0001ca84428450b42044000d030170151003a141a81070320011442c0905513401d41c2c5a003c040d8100803c1b00ea0190350341c1d80c41801c1760742c601c0c0b1520010070081e035000c2158909442c1810180003442c40a902940c0401e00520381c1c0700120307114500c0070380501001a16000500d402d035002d004100d400c40002c1c000000c0500501840e0750040203864026100d5440c610806106800c4050760000750365054504140490b0f22450305400c0c02020318003d000e14544100011500c40384611803445100105a50b402e010003044000c00c0351003001031180c03004500398079200425091850b9010701c5404103800c1c0041c3c40d8510035465060703a00340c03c84400115241c02c240c403000e40090800104510010744080400f000d46c40d07060140600c68070040c1c1d100c44030035064000344501504482c1d540c240c460748411441000f607001b080071909800d02c0040c1c0740f0160803c940103007a0003030309410941e0308035020002404159000050110742505455245280742e90703035042119140220 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 452602985 1250 452601735 452601749
    0x20f030406021b1524122b050304080a0c0c0e0603010f0207050a020f0105130905010302010905030c2d1e01030e060702300c0a02040e071202060306010e031516080103031d0307 77
    0x2a00d49610076070400a030500840030280e03000d02c0d0907e05201400d034110210440840091810000940043c03074403806070004410740c5c1000c04080503195512058042580c000d180442801400c115140c502406250a0b100e40030b0f0085103440080c0d2991500c0c0e0441c3c660280c000c0301d143c200b01c240340c1d200c0e0302100c2e42c031044404412540b9443e2000107010f00000c1c0b000380e0000d02c41041c082010300d0b02041e00714000600404140e15080100305404d00c02d00c0b0707180c507000c840a000303030006000d0b02c540b04c40141250018181082450000c00098101c410540c0c886540c2c2c0c4c04041003101071034000940c59051001504103060011501c0c6ca10803020b804a0803a030000328010590000301d0200084000c0701c9403003200d0a1000a02000b0655994800d40c45510301c0d5001401d90903026040c0704004507085001850851500d165410200b40b42070b40c0701802400c012120310400c107800b81820555007640c41d00f464062010351442e00e00070402c8031100c01454982003001803500d000c2d5001c10480e0b00038440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 452604235 1250 452602985 452602999
    0x105010b0c0c21060a0b0916020606040c200102030a0609090203060a020c030d0614150a390b1009050103030507120e031e0c0d020d0f06020f030406021b1524 69
    0x410042d6000d441b0f0140c80d2800350302d04201060f0b146013580d83c1e401703c1020550040407265180c00400c0090320412004005016001d800504a81c3c007000460144038065400982c1e64202844c0150444070958003d03507416152440c0c40006030f401246030340c0c100c06030500150729030700b211764518114400c8551550500d480c01d40005903416078138550406200d0b0440d84118600090b0b0a01d030380a1080d500c05d40009a0342d180048541654030085008083c5406184d484c401400c800c9481e0400c40a1020754541c050306003005001c548000c0c00d0800303000c902070203105a500d10798000c0c02500607524003c108100011010030300304c0c0b245145000c24480141214880c20a00c0309540e0b40c0681014134424074041c29030002014200030008106090b40500154030858242d1a01188040d143e1011526160200411480025891702a6006038058400142c0d0b5190016000f01d883c258140e180c0069004200d0f058015003c05010b07503400320039220700c0040c0301c1000d03102c2c0c1010408140041d6216034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 452605485 1250 452604235 452604241
    0xf0e13080c030d0f1b0f050a1e0806030d05090d03030906140103030810051c0209090f10021b15010504050603010f1d1e0706031a030318030105010b0c0c2106 69
    0x180c0c0c20201c441861340c407081000c00c00a0300703110344038100d161614022a003104414855035200307a004044090491500103500c1c44480c075404291030490032020001104002406584d1034240000d03000180703e400c1c040d280500b1400450384803818504041d080c5640c5080300d5040c8021034201501c0c020700500381260968482c60003030401c02c0d0a07503104100742895440455282800010713040014001c03034083ca071582aa07030070001442c000402030304280c081c02041e0b01d14120100f00701403108201000158807000b405c0440c0014004403032045103150f01070007241105c2c440608440381503490641c0c000c1125516480402e0150000440c021500c0780340001140803039a0f541003080701100c48405684da0040100350041016000c0200403007a41c01c4014108005406540440c5603159090003078200444868002415034029001c078485003012400d240070340b40740a200e80b501600c980c105541c140130000000b96610805801070b0f0b8010b000741c0b005502500048060644003440e83d004840c4146 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 452606735 1250 452605485 452605507
    0x60702060709050f031c05630307051c02040501050102060c220b030a0e070b0a0504170304210b090c0906040c0e0402030c040f0f0e13080c03 62
    0x4104544510004a01000214962800e019800c181d40c10040090083e00d44514038803212054054148003400810802030107140100400d000500d10052a400507245c810990a05000c6040e2540f24900305a00340300a0818200901c50400c8c400e8880b01e42100702d00f020100e4074040b01508a02d91040f0749842c201c940e1544084002c0d40603101f91000d0000c0d0341d80b88010382c0e481c0000e8031900941e4006004600e2031090800e5410416800301804010090f40d44500c40300b41e51090320310042d21031300d0342e4040468a03c20040300000f0024082c0541c0740c04030000c1c0c024110302503401801201c04d013003c1d210a80710800c205440190056403084943c10210403445406124120b00856444502c04002000310700041512610399002031300308210f44c0d950300708000040000000d0f440500106071001000f90300c8510145105080307500c1c100ba500c0b401c0c1103142c860540c080d0703c172911911000e5010700c0b661728a0040c42e90001c02ea412500303000103403840c1c085180c1c0103019401089100c0403550891003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 452607985 1250 452606735 452606743
    0x1003150c02160b0406050d0b150a02011b090506070c0503390f0607050102071209080f0606151303050a0503070c0504051003030f030b0307080a0b09030a090612020705060702 76
    0x4022640842e005090320200354000d1891030b201e05981e84005100070400c403405a001001400480000001c03caa03266000514000309081e0102441801240311842d16809101c0c0c540c10501032065540341201c0184010f000e200309018182c007415020415600300064a03c1140151200500b40c0309001460000c0750154848445d0b80214426541540640b580d203144015604c59030160a20307050300c0182060203050351140070200c46945d8200301c41800b160040c0710450b0303106e00940d140d40c029840c04107410318199400c542090321750440c0c0140456a0340d0f08030254442012180752988840c0c00052441c64410150f0000c0d200780220048442040000b0000300340092042c0040d50419448200303010440e1011208040340141090040c80030034001d0000b082440014500450000c07002e00200e0300340a01ca521502043c7c1c04003c81c3d0040000300c9401d00c0c4c1c04031002d001542000d08035800103000c10100d10526042c00400900d68401203010f404513081103400004484003410030400080d92 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 452609235 1250 452607985 452608001
    0x102102091504050f010e04032d080f0108010c080a0509071203080a05070903030c03031e0f06090501091e05060102100203070f08061203042d12050d05090117100315 72
    0x4241e24003c00200e501442080850680b1030a820000b050354540e41c00303407440001d41002c00056040300801c1c5c18002c034046e2819503098882d50350786180b410030303400a00124206030031005003a41015031400a1a5209110580c0300e1201c01002c1071a0700d03100c40081c284020f68100583c9101c4884c0c0074002d01d508070791301e94000d150541c410051a0b890010803030310784580d8000203001503427001907000401e101c1e410080280305003184540404202d5404003003100d56201041c1d19058445804210f000418420b280c0100741d040c1c0103200d40034141281c5100e802c4a100130070080344d81c410206006034420480000b650101c84000c5599040c558000390410130300c91885800246054002503580c18010301e00e000044843d8015410981401800303070300c802800c080903c4075484903103214400c5480b00d01a50090802c0c07203e0018800341d5060950810407012072420600c02c00700007000d2142d90000c460050156039501040907504e034100a0402d81d11154006024200c0c2d44081c10b8440c2c4883d889812 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 452610485 1250 452609235 452609239
    0x7020616051005270c040f0f0e0105010e0408070c03020913060e12250503131805091905010b030d030e0f0a17030603031c0b04141021020915 62
    0x2c50044401c0c1400b500c00c22034107034081a11040c085000310480c03a400c90545489401600c99681800b000304003140c200c8041c1902c5103480da40d48a80b12811440788448415141c0c1c001d101d15070500381004284a80580001d1a521001824031309024a4940078405140c3c010b207044440e04095195660710340000c041917580c1c5182503200380c0e04104c0020182e50288210107a1410300c44003400c070400340400c18101207440b940e45110880007038014001400155060900728040c40d0070924040b11035258680130b142da0600c2c2005100108000040b40f0142031441c0f030303410314403455501e8070354090900c03035020a8144c810b2201c4e130744003281c164014840466000e0101da0400c4966892181c1da0907000300098010004014503403052035800005540c041c00c050700300d2b0f180c8107034000c914000302d16000d0822070140e684c0c04240202d18190240d00405044401c412042c1e040ca00c2035000008814400c00880450251501990410b1041c1c0310044a4009103c441c9520b007030340b2110040c107041d415881c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 452611735 1250 452610485 452610493
    0x70306140a0c0f050315090109020c0706020d140a0c08070b0601020c04090206270910060f0c020f240a0e1011060f040503041a09010306050a080a030e060702061605 72
    0x500841107510811440b50300e280c0e6885040108440140c0d000c1d440500045c0808000e4407107429075495001e8030038004e005403900180e07a99826007000781407107202e0700300358115009001482c1d04282d0184140949003800d50009688000c4602d080d0b07a0340e164500010900038012507240240300e10211041c3c80340c0d000b80c09660081502d00d082008440c01404000c1d4000c00134070101e03220f0302113201d901a0074803900340410b068010000005628003412a40c03610315000c5844184006584064100c00d25611424403441c00c01140d400200002c04c80b80b42103001d814800505c62082031000509606000700f43d00d130ba0b517103100c8140000c0c24036010034a00c9028941c01d4100802c2c0314030450700000c3d41e20556000d030100340c890072260a20301c07a0140044d10188014040403c440940a80749000650410714241e5036040c0b5100240940740c1c0d6a20580c0f00d055804410403205001013404d4101c0c507814600b01c0000420f1900060340c0d4041c154004e0340000c0c01081039401d000e000300028204d180034004503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 452612985 1250 452611735 452611741
    0xd06060c0c080d17091e03030a0605180c09010c150905070509010806070f020c0a0609050f04050f061201020f0307020706120911131d060711070b04060f020304030507030614 76
    0x3696940620750f5408000801d82c00c0c99030562031000c4400d60304a085034060700d13074880305e103606101d58980c040d10510b0303e0b42000060020490907445403e00401b4252040080110038110107100e050008141e21500319001490200580c0319039418404940e00c0f0300d81c0411200d6480d00d48004024441007211140301d900c4000ca11071a10b00d0005040300c400400528056903645c2007102d440c15505000300030f610074040442e965540311f4040f0000352174103941d02d40045140070704204111038002400c502891800f02840a9040441001e550141081d140607803505a400c44890080c440c2c10581d641070030000c400d1007400c560106284040700d4159503040c03800c0e0100b80c0b8150840e4180f04005201c1002819102c850741400001c561071441d082500003414103020040d0a0f1500c2c14410b18003051708050100880c99400c00c41d084204003400c002071840300d080411080303251003a8001c54061014101d001000107108204440165034807005a03010182d49280c01000b910100c14100c101514540c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 452614235 1250 452612985 452612999
    0xd0c020102130605090a03060e0a150504150c050d140f10080309040f0209100c030315050315091c090302030d26061c08030906070c02150f0d06060c0c 66
    0x80d42d40044a0b1080301c8510343c500b99040c0c07510391205640a401101031100007011800e1407140d010000220f0700581144110307480c20300c0c06031001c40e0805808510341070500010610004a0b8800b958203a00c0c0082d0554065005403060300074181e4100e106420400c81040c00701e0b0030000382d400b074400050108850f4980c034840380540c00c01170107820303400d03032041c441d4940b03d207040c2d0022560350303501410045c9810320450102c0d0380f4054401c881c10100c0c0e01036458004040e410300c100548400ca081d001451030b0309200000340c8902d81d0b03000d41ca1102841001050b0100f0382485243c0706601c204814244103070488802500d199020310003648240645a15001c00e18086c54842011030603507003100c802100c801801720b403685000790009401a91900031003020b901ca005400156a0046800ba41ca03840c0095400d4540b0b1802000001001030b00c009040c0183c50302c1d010005007001001046844040e0081105007901440c406101110700b070550010f0f032507411441c41c43c90280644861001e00d510b40740 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 452615485 1250 452614235 452614237
    0x3191d0a0501080705030712110306150301080706030207110402030403092405120417030a0b0a0503210d02070f080a030c03061a0a0e090f010e090706021902030109170d0c020102 78
    0x324042c0881c12020000700c81603c510700541d8047c106040c040301010002c0383e0841141c510400740c0e00b040c5000000c2c0852454030034450b0f84070001082c815403543d0f0400483e01e41300c0032544a59400c1c982c021401004200c01818201c2c540e440c098411900c900c1c16040090071041c96100d694000c061008140f6841e03610511b20b10100d1038152106885c0000940e5002800c20b0014000d0b91a2a0782c80c1d4090140f03006580158003c0000d1040410031880410030050188a1944100c1c0b00b540103840c002103a0405c074042006410144655a88640c0001c10381d0b800703840b5002006001aa20980100c10419144040c0001480d0740c0c1d41001a001c041c00250101d906c54051110010000500f81810501103c0103040b55512850002c0070011000007103800c543c401e40c0c0d0072060181304401844545182d04041d0340c806106c0300242031407464801c1c0617444034480c0044c1e110010403001c21405640b800d4001c601c0407503208a42c902c11071040f041155041c1c04c4004442811418200002c120500c140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 452616735 1250 452615485 452615489
    0x60b1206011106060a15020f060403180f1503020304021801030c0608061c230106080109060b0d030c030c0804081c080907061b2307060207091e0c0203191d0a 69
    0x54017000c1142e0909004845203224094900218882c81c0b022030001a0144070240c015407094580900101c140b044401150580350844100522005002c202c040c000d00c0900d01c007c020f5003001a502c4c0c84600100e4a40a550300c0e001382c60703080f013600000420000340165801c0390340d10342e07e0402c183c458000300602c0340c0558000c03140134500c9000303410110f4210503c02ca500d0451001c00c100217442d481c1c21a007510055440300c9002c1c1d66030140e4509000d002c0c0100d0745007803400c59102e100060540d4024000a812000180410007000200400c0042040c12100580200130440784a240800003204201c5054841d60300041c0ca22400b040c1e0511b40043e050090310b01d1a00c4194002d5028210383c0d8020f000c6881c241e5410a02c2c0041c4264891440300c580e4081c1c9000001d040c00504114000e031034002250701c62101d0520313210184000400e0024003407041d501480d0041061000302d0001c074070f5801001503105841c080e8900d01c81c0781c190012055007250340342c403103d000206038502c20000403440c28 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 452617985 1250 452616735 452616739
    0xb010302090606211f0806012103021b0105040906180e0601120605060301090f0309060f02060c1b0a050d0512010e07140d15061214070e040f060b120601110606 70
    0x11600e184c481c5101c00c0507a9400381c0c0180030703020f0714210b6481896500e4500e901074510f81c1c00880050140c003940c50500c8000445410024200d406943c0d0002d65400413106900212244a640740c901603200e101120b0040014010900805840b06241c180030b102030b0394114030b0285481d2407c1080320b00428080d040343d09001d4101581d12054a550020304001028a64155130311180c0400080002000109050080d40c43e060528104900900580d01451202081d90b000008001558440e141142e100c0b1110f107003080d80c15850701081600d420036101c00282503004009402410907404405841046200d5a204500b6642e031003003e0080102901e0080c0024007a0b40609803c81c0800018180012030007c0010320140b41c00f10004450a541c20584c000791000712001310580b110b002d81e5901288a825541040c10440e81c0a061800340b109814051620b03540c1c14502d19142c2d5000b1001030484410040d81c038100c0d80f21888120b0000c80c1d0f0140403030001c0d405000c80320000182c030f520503080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 452619235 1250 452617985 452618017
    0x9050606010513030b15121615031b020c0f01030203010803070204050c04031203020a0f031a091008030c03070201091a0d11090d0609140a0309170a020d0b010302090606 74
    0x5140300444140d440705110f800b003c04800070020000310360501042c854828840d60007001307141403003041320b50b803031610501c2180d43c007007552460715242841d07103803040350841c07801100c2404005000343e0180140c40c00005484481c140e8540107a0340124010080440448015085200da030005404a0000f8015002d0551092142c1d000605042c0c5c400c0ea001207001c4501820030350b40742c0d80c0300c00e60403c0a61a1001940101d00202800e402000b45103070285141024000745604983c00408500a02c0c0d5061141c080c0c100400c0040344608405000341c82d0080c00e8a5580c0c45411050781e0301c1e881070030102e0002e0702900c07000881000496205141304041c040390792410540c17910960140002020049020408000c280340035512400f0341745600c2e116010228448030182084003072382e4078401c0c0305a0b40b5000f0b1048500040c0c0c0c031480078030075a01a48405440c104000340040d00e44401550005e411010035920181030001a009060403603100b203070640c4890369200705200700d40c09031455030380940c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 452620485 1250 452619235 452619241
    0x20d110a09090b011401110304140a0509070f0e04060510050301031406060a1208090d030305041a0c1c0b15040306050106090f051e091504180201170c19050a08070201090506 76
    0x301202821740c03903803014901410071b401c03c03104a40c00e580c80782d442a4200c001c1d0946805080c1850f00f6820010681240c1c0408145080c4c6800b4000402c070582d00820403040c01034926455845a0102000c1d00002c2c01c22084048040d50140107644280000d442e155800c5e006040d40040008105114003000780454241c28a0040b81c508030181c5060201d45c518030500c25100a42c41d07600006600e33600994001c1454105800c1c01e40b6011441c901117659a40d44c03104102c010b41e580d2048580e802943e816400c01600149007200081a422180940c400d00010001e0100808400a80b00b600d0041c01c0c201702d45e0341d070b4600907240a40903100e000e1280c403124808001e03a207482c0601d900200528021441040f0315400003508050088a02008040d08016111064140b62041c5501e02c0041e0480c183e80310803680010f442c0d200040501011003001d0400540c41e5040041590981001d10841c10440c0f0402e21024080d50040802d050005241000060b9800d1050042040b2181c2000140816403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 452621735 1250 452620485 452620499
    0x3110906030712030302120f1509010602031b07050d061508060f0c0d140a020a030b010c1119030b04030228170c010204080307150b011e0305040f020d110a09090b01 72
    0x40e00e00707505405042e400c0c808010100c038031f2040b0368480c640050400c403040c07401d01101e6400710207560089012b200c1480c0180091034000045404c0040b41403014441d8a4060b5001450180c241d0010703038109007440c01c0c880400005805c682c198000d10200c1c10355407030300c0d402e0b86556200300300d075002000001a03012480030109d190040801611035513000c00c640e034110306d40d050942416160a80c55a83c0001c0ba8200268103108401d010300c02445d03c8204056161100c02016501c0d5aa040c45044416882c0031100040e0340785200456010300c900e0b415180500b806034a030b0b1603103054052520001c030448203402144213655075901c3d6112041c0d480001150320301c000c054002203006602c45d9801c0101040b0b001081003d80041c034441c40b03030b41206c0e451010048050b240c06800c00e40c1030006e242d501301d2810712030b920902003200081c0750004242c0c0d1982040850054640340c080d4120081000040500c0740b04444084104c2041c2c912108086c0d41c0c60419044601407d8090310310041140140025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 452622985 1250 452621735 452621759
    0xb0915090c21040b090c0904080a021c030e0706080105030a060f0e120304061406010f0c170309030d06150203042102061215010e0a0312031b09031109060307 69
    0x100401264081c00e00c0b906907030350100c0314507094104a80550440402041141e503851013a4061507a4018000070f680c0328000c18001c106c0980b00a117074410100d61640014800c200c40d040324600001c04861540314254040c00074160303003078400740340d001e080c0c8089038440c0528503460481e50040c0c02012a403040f40c0390540185844e0300205501c0d903c64482e00c4141c241001403101c001000c00c1c8031580c0303003081d01d842700440d64080d40d00100e60056204010940ea00b007045680c140466042416007001070b0701e40400c004100241c2042003540c040207002000390008082c103c100e01c217540411607103481c0c146494103600d40540c84801a401048180451400820242241c1264042e074501240e020350001d206500000280a00c0c1b010100800074000c140e514082c00356002820841418810040400c03070007901c034000940f41201004040208030300c0303907002c00180f01000400c00c140e840c2100d0020000c0c1101d00c0203a45a101040043c48a490110000c50061400030700801d483e03494001c0341002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 452624235 1250 452622985 452622991
    0x301060c02120601060216050d020a06081e0a0605120703080f090301200307180609060e030f0f010b0a1a0901110f071d07050a1205060d0c03060b040b091509 69
    0x1c0d60040d001076052003c2240300c0c041d285c9500904183c60340354000c400032000c1940064885c500d20261000542c80340709412050b0f500c9868020515a2407002941d42c010600c1c050b41d120804c400100005a6103079405102943c10855003841c04045201b0000da68412a002c003a003510b0b41006800c0030210254000c0c08030000180000c174400301382c06818000c0d01e040f0442c080001c000041004501540900ca885441038244a40c44496007410001401d025190050a0034007040d80042c25071a6810092018048820390442c2c114106e4500041d0180400d2014940a2a4502004500b802d050f402c0282030000a6080c1c5080c001c00f41d00440780aa009918004d95028400c82072180410510400700034002a150495142041c00513548900b180103204008001050107031041841d0b002040381c40c0c44080c0800414a921401c0008000910005004050740e0b00301c4800010443c81d500100800c4e20225001c1107200048000e0205a00003203545200c68807010407030340c00c00c0c40c05684640e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 452625485 1250 452624235 452624239
    0x24061602040212041110020d0c03170702070816120803071803121b0b1506040503030a02010509010501050301150e0a0b041416020c1005160605070906170c0301060c02 73
    0x125000054010400b00e90200011107802911030042005104202c0c0d561016070740c042c0c808241c0d19a207a5002511020f60b0102c074020024a5005041070520891800240103410b040c1c0030007a06042c0400703543d841d054030070b05c1c640b40913001c0c181c80e624000c6030410b03003120b8050154006035107459036010115800100000188810008038546082454408901039407060001c07207030040c078400c400352101c0b0343d139032a5824a10b90303080300400140391012140d0f004410b0702c40c00900c0b10748010019265004940000307805100102d841003040b9815044039005054060003004070f079803500289400d03609030aa02034005074421800308503c41f02c80082c44c1d4851610354000880808500c005010349021145000181072000c092003c02b44200741690000750550004010551598021a800706000340c085028440c0c041680d0345150414490400450740c01700c8100050b00e801e80c0050f025981c1d80c0a104002500305400031034440c860030489000384821604281581c1c80c0010480b48a080c00c2d200300d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 452626735 1250 452625485 452625517
    0xf0c0204230103030f1403010b0d0b0a0e070509010822080307021606050403020112090c050f12060403020601030b1308090909010b12011e061401050c07030c0e07082406 74
    0x1403003800d60354070114082e5109989041078200c410384000c0445208000407a0341c1d4404100400c04032445208032180790a250401040e16000d11000402e40101540700c0d0318400d291000b08140c1e2540f101c0142200882620388160710703110690011120b40c0b041c088200c55505c4884564081f541500145900c038031a841102d03801c141c0a0600c10980c50a940170b400402c0011074144110f607085001d40707001070001f100800c0303100003035190201901c0e00c80c03003030368000c884102030754074661207940b030003004259100c04075151410302d0701d402940c2e40407d11060780c2e516400004940041020109002e0389504034580a040240740070800c41030203c09040c1c1c400c3e0f59a10807180c2c06d940c036001c0c925810b00c030041707000054141ca59068617090124086900f0344041c908401400b007203424401c0c07a01e06802c00e180c0542c5805401c00740d58030340082c0d40c1025005030343c05807000500814000301c41c1d05c201e47c0d540d150340f40d070746410001c12120b1428074011004107174000e0302d00110b41048000340007503540d142401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 452627985 1250 452626735 452626781
    0x9070c17070302070f1502120f13170601060512160e220c0504030c12030908030304050106080c1206070804061508210f0a030f1508030d0605010f0c0204 67
    0x422199224850480240c4c100c1c2c00200041c440841100d00109031600c2e400c2c0e0224003c0900a45034410030b00351507030b0074202096a8080200880695002c000c00c0e20450085c6a2103541964400c01008102c8a03903104180020403014492002c0d209408a02440120582c54060038110140e600d08050010066929140700c526601c0e810364960074040c1c2c40d4200d00c0503c1440d1010240d5444074054000e01c0002c00040000581c03120903d02160405100104003403e0b61600301e4004e084c592007a9000d11000c414041402819400b001c1110b25030000c4906a0403c3c0d01840b0308210079040380403a54000000042005000f6011540e10900c101d07030003d8983e144050460384420f050300400e020364444013203e40428201512007030845900e28101d414445084040c21203445072200540c1095110050000c018000741c100742d070208036000050394502e0b15425400d03039035084a946070000a080c40000282d0794050380385417419104564030540710301c4041d001d00024205084151250003050512 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 452629235 1250 452627985 452628023
    0x271e0c180406090204021204050114010b0d020f0c010e030a0e180c0c0a050124050901140d060f09060902091503030d090c080105101701021911031204060f0e060609070c 74
    0x1810700d191508070322a0b87c0e0500707080c4a405c480f2582403211110300c4000060120110f80401c1e00c402540e07441c805030380c4500c03200001205003d00c021b03007880d960a0509003603a4040100280072040040e41d03441e811035229108000781440c400000a441d02005000304039104550801458400c10700e00c222000111279607034250071142d00080e010f1103114210b40c0e0460340500c1354803110082c04120f80c406d02c1d40d410110307101d00802658003880d22841c60780c6445000c103d13294114090700c0780e04040c2080014600e0808501810700003804074428041017000500d071004c50103500500d00d0f80a001141880003c0c100c1c0d8008140320707201920944110071002030782d50004d00030746129201100c15615039907e0301c900c2100d081c128030f800c80e40d44d9005000011b640d80140410b0b402140fa0f13881c0441c1c0d0700807854000d0381188100943e1920041c0c64504010a10a05412005483d0300d015810080d0b045140300540d00c5407000d5030302d00c0d404091440480c803032920811414503070314020100d0300f102c0c103c00341e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 452630485 1250 452629235 452629237
    0xd0303021c0e19120e030a0b01030303060e0702150f0a06030b04060209090907080d0503060109090f050106021905060c1803030406180e01050f09271e0c18040609020402 74
    0x5200307011140c0701c2810344100c00050100c3d4450b101a00e241c02101d50b81130392481e00201c203200381e08040000c40b8981940c0c99030b00700100440d0b0342d04148101441e50712420021302a0426020b84d400d0451000b0108100510000d01408001200c00e900042601d5804000545190140c130240b600c5442e40c402001060f03907603d001d0f0160344139200040e62065254241f2030300403402014100c0c0c0b038000147c10406102c000c54405645a07a510302255641e03619001610340c5c8501d5005500058039040076100480032035804241624000c3d0200d074007106d104001003c2c001c820450081440d045480803030144004c10b07000d07020300044402c0c0d840007203150a002c00d146400c41e512500008080e0007052040c3d04014103003201804100a2111103507052034082840381054121050041920b0303400101d4207002c9050a030074100c1450040700c03524400318400341e070704c00420b4800d0000c6a898803c0d000749000000d2801c04600c40504400a41c0c03a60007050704861a000b40241c5a06850700c013001d0050707403184 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 452631735 1250 452630485 452630527
    0x7081b0c12030c01050a0608100f0f0e0d140f16020604030515010f050402180d0f020307124d0a030602030f0702070e06100212030901270f020d030302 66
    0x9801183c49141107103a860942c0e07000780c20810100d14104041c030180c0004240440c0e504401c0e40081a2260400b50000007050b2160010101d14502480d12012000100f50055030601980d5084a200b17000c84558556120740d02e03455120b038004001800c0500c1d80303940c1820b0000d000421141c240b9a032621580d003081d0710748c0b40b05802980c001c801440b040c50b01c017100ba4083e0805450841c00c2602c0d6040708903d540102c103000e03100f03c41c0c03182c244c001c004800030100e0072158042c0a4420700f95030b07031088a01610242404980358460b04000c006d2102c003003009142010380000f0384a2088103045d003e0080c41e050000d0790b40c2d540013440705104490712548081c1000b50710502c00143c0d00d140c40d009151080e0000350001003190481c0344100140301e2005400ca8100c48201c9505065051481d4164603000409041540340c0f44040b08009034060194440b9040c00d21059084e02403902c13410f80820070f2040c007440201080b80300580c501c0503040440262046900c6802c0052401380c040d058110000c000c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 452632985 1250 452631735 452631769
    0x3030706110316030b0d080304210e0301180507050613031b0501030c08060922170a110d0210020a140c011d1b06181002010c031107081b0c 61
    0x3c0c82800c1880500c150301500303191804100d01d040b15030020300c00b91003402e4042c20400011001c501406021170900241082421241080075002100500115001d1400354840d520304000e4041868002014512542d0702c0300142c4041410001000715070740004a8184524100b01000b000040c2100b0310f044000b010712006101080c82c0100040907101c9048402c01000814400d0022607110090000c0d00000c0c013100a20305c1c01302c14050f4402c1c8441030640275000c490303030140b60300030141d00800509009072190b03a01c0c0690080034401039a1035184001200042e070001c28248403040441d4041c08640b88180740000c800003264545c102984c002c8401c070b000c81e954500c1800604445103111032180d07001e8502904500e15840c0c0442444404d45c403805000c0c82c0009202403074010708010144d4803800040c40c2e00c8421151020081c0280740c00540500428a00081c1c010120071860a80300d4040e48454440e10b1b0115207204008d400c0045410035403542f00e00e2485031200d550706520305010900d9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 452634235 1250 452632985 452632987
    0x80d0501050f060a051b010b060a0302090a05040513080f070b190509011107030c060f091b050f060304080a0201060e0106050c1605010e0108073f0c1209020303070611 73
    0x1014108604900c8061145220fa4810000140c4d40c9802a003a503920164039010040e0410400b603d050140054417590b551003c00010140d00c0f6980541c09045015810364500b40d0564840007448115001540c04a09909904002c00000781e0004000d0a04889034696181801400d41c0e0307032240458241c406447c8120480480303200c03414180303c0c44c1d90100070100280071040c000a4400410700c600c0b1006001c0007401000441409101c1d000726207043d500981c100f0001d105400c10043d03104840c0b80001d94015528800a054035000a107100326207001000d5501c2c40d29a03603150405a40015031250a42d500d4520000c0c0403070900c81c106000340500c0e150a13030f65007241405a810155600005007010300c142c3c00600c546d9170b000354087c00307104c420309080c125903ca103203064510480c0c4503002c1082448680220103400c01c1c0060400841c000c613044402c0c8100c080300b40800792808110040f0005d101e280d441e03110501140c008120690000d01943d141051684500e000d41e4103150000b036042c0c41c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 452635485 1250 452634235 452634239
    0x60619180c0e09100611031228050103121b0b0108010209030d080f07110f1f050f041718130204080c1207060f0302090414010503072702070807080d0501 67
    0xa044803040b4140502151210703514601400043c0440f0b400380120800c01803503410522084c0410011122040c0c1803400e40c24041c58522054095131030143c21101c503010146c501c6003403800281c05511f0690b0342c0701813080b440c415256401c6586805400400c124120950745020109103a0f4464034081d100c1400056a10b10164050500d421080c8811800700012541040044540d255030b443c1c010322640b07003941c00101c43c009420300c0c0002428002190b401030340c89005404003228100c40c120800e0180c18041542c0340b0002c41c070003c00458010b805d01d040500e0845540100340014481c03e03201c1c1c0007910700c1d0407103000890000c4031111500d40410354001400d004810041050f0b10400c1021141e1018000d49002d00680711180b600c04c0400384400c03140e04446040c003a0701524000000079004119070144180111f00c1e0002c00c0c49502d02030b0064560100300740c1748401110890b242b00307001400c41000760f001d045000b544020700c20b5480409c10301c0014000b60300c403401003025203020140030a50354 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 452636735 1250 452635485 452635487
    0x21909050a0b0405030c060c01020408120a090603020901020a0f0309080d0c0203060a06120602071a04300906181e0801050703140411122e020903060619180c 69
    0x445030b074005008101c0207100c100025540010f0342114140f080d902241c81d20740b0300180b98064065a04841c440740294603000c0d03840718920b005480000090769584100c0741d5150001d400701e200b5019140c1c0142c00c51140e0601140540000b181401d119280c0403e4807070b0788040303c60070015218041000550ba650790070081d45410000781e50002402902040109d1900c035180d0503000300d091009007082c0d000b1801ca410700940d007207110184040c48000c00f8480c5031501d08003656510700809078030f81d09a1090082540c1410710003081d40b0f03000ca40c4400074000d040a109585c00000300e070300303424449411040403818440028410320608039038001c01c0601800e04103c036003543c078020441020580342214540320300c07003a0341031079400580082015100b0f000300008a518102d81c1078a88030940f00c2c2d1075100c400c0010604209000c0c0c4203046031070194800500024090b48030703140603258958840004036056103000890010040b10303a20002c8041503451800328441d151500180149a5031103080e900c1039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 452637985 1250 452636735 452636749
    0x9060f0f18140a050a050f011103090a090f0e1c03270812010803070b011a0d0509030a030e0f251505030406050705090904080c0102160c080c030610051302190905 71
    0x3e45002c17035180c0740240c10034001c14082c101d4101020704200c81c00c1040300c1c6659003442207030070200740a00a03a55080d107410303088000d0690080b0b8407000f2850300849000c22000801c0c2450032a1400718001384484041d8030842c090000f0755541e0743d00c0309085d9688060083e14040c9540094850b000154549642004010010105034000f800c1a00104090b4001031080c52407107040d61420b0703003898040548995140c810b80180c0e840005203a2901040c0080c07030a002000c0c04c141c41e441e030340034491640311402c401c0d151400e00c100304c441e40d80508a0b51140e040c2a1900a840c1c0340b080302104504c07655051003114244469020402269001051000780226800f40683c04400d5062142c5403000403030100d02920380040c409000e40a001c2020f0041c030500390100c840f510709000d420115801c1c0c07801c0541103d25148074007249440758103034000240c01c01050143c2301d800c100e182041214903000a000182c03240b40700132010303540d08102280c44d440505000700d224001e2599196a01800c00b8180292 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 452639235 1250 452637985 452637989
    0x30e010e07122609040f3c0204140405130506130b071409042018040506040b03031b0307080a03050a0c020c060d090602040e0f0702010b0109060f0f18140a 68
    0x401915640f5010f102086107007240c50188043e500014540200650706006041b152040800d58010001440440401c1c0717010132128081703054481007244940c8007100c00c038480c501c0b81548090b20b81e00c83c50700c1c51038241d03c2180e12925550380311224440968401e0305201007101c61810442051400c0428014103250482d801425070a00381c11130140c405088045008240ca600e11030f6885074800c4242e40401d215140b48181200c03490307a00c8600c00c0c2146216900c1c0507d80600403490800081c50510b058007410761400c50160145251520080a008200d81d400006501c10702c401c200e91000501603070b0051410050f140ea00248500f042c2000205854480d400c200c210f40c8540307807084066544070101c68000440301000a500304c1c3c0ca203004406400740364040c4021003010301c100a400b52200b82c17181e00c54030195008000c0d1203c07100040d02c42c20320364000c490000c0e801c880c84041c0c0b58003a10911001300c40e6401e00c10100c9141407004568213005411000c1d0038002c04605410f6420f00480b2840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 452640485 1250 452639235 452639273
    0x103080a12050c04030b0417040603020d05150609150c030d0b0418210908010f09020306070302030c030114041401030c05010207050312090d1401060303050304031106040210030e010e0712 82
    0x500f0000f0411480e03010b07074000913040480e024082420002d12501c07103201a0211980d01d900c89950781c2c8050000e410609103140064108000120025190f050303103020315400030401c604004491003840b040d00380301002207510540c1046407400b5007000f0000f42c51600b0100d00045400c00c0e20b64107110550f0307079400c000044003003d03c9140000500c10640140c102d01201e140c01900310319104101d4080c261b41e40610354a500e401202c446001c02c2c2c0d0001c000e40d80c02a4111040390303c41d400100c00301d1208584080140d0401c0c1300611010301e4642c13984980100041c00858a00d00c0c1141d8200c42c0300c0280c0c022122054075410070800340d40c06000a200402c402c50103407144c1140751041d0152880b401c2500c07842075950151075001c124144240300c0400103404001c1101c66220300c2c02810070761041e40c0540108500c60b01000d645100080d8003889907034040d005c640c2458005e0000d4001e40340b0480303013103059500c42000d1040c1580c204600030003484c00740300f882c0c240d1040d8200301003c065003d810711 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 452641735 1250 452640485 452640491
    0x70b0105120303040210030b0a0b07060e15090a020105030411040e060105131a0f0d140d080a0905031614010c050405120d020a080d0f14090706110a0b0a140103080a12 73
    0x1300140ea030f600f024105032070883c00c010911050703442c0007400d01c190641001401c4000850240240401540a086061044d40484400151740e07591003031100c00840da4105540e00081c12000127502c55005160080d1007000300c0605030b144a80094140d440c22011500d06a200e607004000300c1c80c100305c1c4450b03008076030103040120b40c0c9000d01440c01000001541c81c020b089511042280b1344402c0d800c01040ca03045055040d0141c020340302d1300d0700c51300b5802c00c1c440060700c030034040b030707c052060710034000000d5100000f51316061a00c50026024542c103441a00c0708810300441e0700318050f0a00425855000b2540c44941e1242000308000800403075004e6150b840d44880d0385071000c0364001400d9201c00e40c0210025450b0451100448007070240e02040c02c1c5111b0400440c42e501189900b4054080d00640017520141511000115900140038082e01c005511225518021908206805402140501c00850003089a10526180c540c0a0740308840d81c607400100c4c111900d52000301c41da03006420280078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 452642985 1250 452641735 452641741
    0x1112032a0301050f150f0c16062f0708030f0703080a050103020d0212100f0c1704080a0c05070509010f0317030f072a11040c03021e0915070b0105120303 67
    0x100f413943d00e501c07200c10300424003c0604c51190300300c44140c5041402404010f0365412101100c01d441d180d400025003d00100355201140302401441220380903407142c18060240610300d5904107002580030442a02d6004101011402e100c040c402001c03130610000000d961224240303030060000c0c4001380100c0d45507103004014001680d940e420b15a845070121160100000280d2032142030044184100c2c1d80c551138804c00d5640224680c110300d1510351030b40c485595940052a6910741040216001402c54404100110400c0d01503864020031901420807960116107800200302505801e0b0480e440340350810204000700300550200306c4041da50003c0181c15801e000ba050a070511010344034800b40241a20078000390401c0c4c140800440a500e5540359042000e0b092241c030b030f2001406150301485c140185040301c24001e0084402d1401905031034480140d002100b01660740000008a51014520744543c1c0f015a900024200c098041c0c0241e8034154909070410000c11510014100d0640081c010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 452644235 1250 452642985 452642989
    0x30203100b03120c06070809010b03061b0d020319050714040b09010c0f12110102090f0f01090f0608060a05010807080f0c130303020604050d0c02030601061112032a030105 75
    0x9920800da01580c4041981041500000d00340042c0d40b2440c0e05042c004911003d01800028001b80a5101134540e22155103848034414281c61950034003071703019032046000c0344603500c04100084140440309042400c00c50183d0300e520030f07a401581c903580030044110308451101c91703910070260815014108198111490315a1190bc0c0c0114401c0c020907502c0401c0441180c0d00400c0c0b008034036980300340d016001c5910342c980980ca102844070940001510b0000d5144011014403c440103000000c01122098090074204880003021100b12410091113203400544203000c6c0420070302401c6141c0701d8a0039860a44180450074070183c0c08a41003100c44428440721540000b00caa800c1040c1c2008440340b80d03a8400080068410b0031103211004c2c2003400d00001b4980c0c04512240140d205106a61650300024130498400d86400130180d85a0007200040108a024682c900c40a034000815604500b1640304124600c0e002100e880e80c1c1594842900b84031000712100d603010080041800398215410140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 452645485 1250 452644235 452644243
    0x1b042706120f1103010b060d380d2d05060c03160c02010c050d0c060b0301060308160f0f0c090f0e060a0c090503242d041b0f06090906030203 62
    0x1e010f24405044001c4a610b0a4000142161020303200747da46000c94240c0301300814188200000c8c003203d0401070005548032070344020021030f6201e1401040c2c0f2a02c020400b40d4410b11004868000e45c001c0400c0c0700c05c0c001c1240240d00080342e88441180c224170f0600508002c4001e1180068220070001c000005041692403045084e007442c101c5110041803005030340342007503003402408074820f0b264903084550340544c0110085118410511480d1120405c0c142038030784c04d01006001031800c0c00706401c088502c01201d0301d41802030811541444e05922040f000e03003418001900c48181c075a10520400c0c1ba03a01424280410b904030811049962111441d150b2801601c6030302455111405440b41e1841003015401900001b07050f168101c0c01c60000c0c1041c0419a0440350b000d401c500c0c0042c050745002a0108841da80404075140d43d00b40455a21400c0c00f070040080703c5405528048600002003401001c019041e054000580c007410030001038100d9a49500080009040280600042c0c034041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 452646735 1250 452645485 452645513
    0x30d030911030610050432040213020301090203060405070804020d080a03060e09030304050d05190c151406030105010909020307150e0d1101080615031b04270612 71
    0x125000901199078a08100204080ca41465151107900700b842408612410440112002100c0c00c00c080e84402c1c4007000f07001a80c00801c680c1c100b10307000b100e00c3c0154440d00d056000e8402000405000900d201c0c2c0c1003241c0080c0c020720709065012040150505081c070565410441030700b040505403074154000f4200300c2002c3c81c001d091950110f06011440e00940002e0041c1080e940d06102c941b810f01102543c0750000c440035501440780c2d8200b003421a0050b030865100c15401d0100c03418505018505448002c80050b00b222018071380b000a01d19848544a484d24841d28804203442c0e900307018040500395003040e0080881140340c1603108c001a80c001030034900b22802541060a0304030382e08801c1e00c40007043d6055580140d1038070001380412840c04c805280340c131300c01d0325600c0168662109205c00071541585142c1c00003001c002003034402c3c0f0010002c0100410040380180f819131205c009200803901040714543c06103050146000360b160501648000d08400540c04415110541300c6c100400014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 452647985 1250 452646735 452646737
    0x2091c121b0f030e150d0b032e0b0d0f0501090b101d0612060c0d060e010f0303030e07050301020406090f0b032206090206070f030206070309020a05040b010522060914030d 75
    0x103000002d940d25030309150007514954126051b1034071041c5070b80001500c2d01700491440b83c090009003654004240c00d41ea004003030102d0112400103070b510981c2c0020200400340517800316080d01c0a90024040903050050f50344124000704912405107080390f8024800380a4080ca03914599050040b0500c241c1241c040c6110303110401030070345680c004210b07840703854034081100d40035003000c10501c02d0011000340700c0700302e0b000c82c1003000c0b583d01d964120007000d080c062000403540c040e500f000841d00c01e401c44212840b200c410303620309940e1440041c0c226070280c0c0c0720901042c02200100800c03a1101200e10052180d040c64030b00d10310781880b0f07007405002904007900c40c501e03d4000c03c00911a907580201100e507030250403256039505600b1b11400340c00080000310014030440c40000d1b0301ea0b01c207008842000d940078010381c00312400d14081001500305070700c03050304220040c408001d401c0781c20301800d2072000110120440707450829130001d044d0f024a8018425006c1e01c0d00d20011292000115a200d001c41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 452649235 1250 452647985 452647997
    0x8070e0f03030a020718151502030d060e0603010605030f03070206030405031611040c021b1212070804030c0503070b03010b1c02120124020303040602091c121b0f03 72
    0x104800600d1180051000c560140b0001c82da140d816600010510117850a6000d612141020450958141c844000d10301d60813401c4040100800101080c500b007103145107006032410311070310291000c201d0b0701a62208a441082d00d0601c4101d04080c400e140140c1401e40c050302041c030f500c420484c2d5a10031188002c7c01424000000340a004080c07052340d50080400440c0981414541449015500100000d82c41245004004041203000051034216130747e01407824401e0009050801134102c645040c080c0f00b07800740000440b190000303040148140b41c4284011521107046041402d40003032182c00140c066804035405110b04a00c04090724116414107600503a00e502a01264600300252260f071174005002043d50444529141c24842c1a00c54011120340b030384900c00096080780019019900268100300702180104103180c000304441c0348058442d001c1ea1800c8000700d2030441c2c6603001a10a9500d1a40d281100c030f90141e030040c81000f040030100300300d003616214104625100c1c2e100400f8490 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 452650485 1250 452649235 452649257
    0x6031b060f0f031513060303020613050715080109060b0c03030c0d0902060301090506090907050f27091b0108060f011107180f0e0604050a030c030504030b0c09031605010807 76
    0x182001211141075078074000907200d0808840394426040070350340061051000302e224410845c02d51058900300c079095801006c0c55200e000020300404100c22040d24103000d07250001c145c4620058100c10145210f42c1d0f40402d03503260161003400c80f0040c0e0030091030700c0000c00858040600c00400e8035080091241d0655640002c803e0000c028524060005d401c008040000600035665512152180c18241ca981c0b0160f42c5200c0169191095030043c154891a01108035003241050300d2141450718084c000c0c0e0a000b0010b51000d0790806003140c01801952007440d0b10942e10074402d0f04500c1d582c40a0130208a14109100004c1e07180d558014041e04015800103a000d96880c2007209000800094005189181c039002c85000a0425104181c84441c10105031090b40b09000401500c111703080b2000d0803102066036005c0b143c04607402410b0b800c0040c00d0002001040c0000e0050340150134100c5403a6803203107204207042c2003000380c1020100022403000c041040f66000145d940d0f0040c0c0c1d0b89040c806000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 452651735 1250 452650485 452650507
    0x607140403050616030b04060e0c07081c020307020d170c0a0302130b04060215041a0c070b13110f01080f0a090f0b0a05010b0c070b070f0503030906070806031b06 71
    0x1000d81e6001514511498050000302034540e0107100c0b0740c411650f01404982810ba00780030680b1040c2c8035034079500070034000103a0001d0110000c0c103070003449a0030540c0740013442c02d14030398045103a0241c030501581c000140300e0050713010000761101001e103040030ac0107000003060810011400a2001b0b241000000e2141100c0b48207904907124100c01070f02d40030fa420b84882c403100454206008500c0944a8030103800341241c180700c8018800c1d0b40c010f203d10401d06034003510300200c18000d00410502d9800740b1240e00060743e15502d4900c40c940101490400c1035940c01d10221442507401064046c514240184881c0d03648140d981d80e0012684200030307419102e4820800041c1102840030f00881082003500081200c0c60008501507600c0c03550501c9107903202c42150f2041e01c205a04041030754004c0ca0700701304015284000d0569907000f10007540c420015a16010300703551045504002c1c0c1d030000070030845c140c0d4124900a40042c4154010300da5002e07088525020002070020041c846c49001c14025074003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 452652985 1250 452651735 452651737
    0x10302011b06051f06020f030d0f0b1809060c07020d0b040c0b07080c060f09030d0b03030f07151b02072d0608010608011208030c130504021305090a020705060714 71
    0x110b5403050003000329140c8030a004e03a800c00d0041984951404060000a266100140801200034140d01071031401d11091031380402000083d5102d1035450b1540d10300501581d904540340340b80114645c0403189d51030109030843c00d18400800e2090255403c3c4034507805626151034110503303a0000760400d01e5104c5042203042c5007215072003040a2440020700300100042c443c0900300d2481181c1c2140c0702a10362408a0000c0c050844150b0103561052000781d541645a8005c45408030b000340640e0300c1c048425010b00303480e6004c0801651101c5000b074404000019502c2a103500301c85c1400200812004041c0003925511107100d00c0ca406c038580041200310010b003c10701ca0344a14040c4260413096541d0368040d0080c8401d20480011a907600000103400e40c414038110100359100500900c3c55a507401d01d1001c6400c402c40d00ca00c54100c41d1004075032174407184010120000111000780900345400b040100c07049000b404a90342600500050300041c0c4000b80082d04501c140c00c0a000c42400403455041e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 452654235 1250 452652985 452653037
    0x80315130c0c030e0901241803200a032a080a0311060c0705030316030b0d050319090b091c2f100e010e030f030304060c0813080301030201 61
    0x409151601c25160319030800d5001412030301c603454914070480c0280030011880b4003445202c43c817601109a0040e00c0d00100100c8035020010f05260000340c50b2524513403003200c0703940c000b1034189811345240142c52104040c00406a20110388509144e07045035200004550a403080704003020140307000e014403000c1c0005850180c2000812600e80b03001505005001140002c90036050340101d202040901c548032040f52840c6800c0001545140c0b1510310b03a0501c403548a807a9020545d80d400a20015914080344242182c0598001c5841e0005a00c0d40300060100f81044000d00881c80810003000720320b01c05030b803000002140c00c05d070304a0290000c0e0800d0f420000700180301d00e0300c21040407040c10070100e07500484860f01c081080c1009a040c01e000340807016500e82c02c003280c800001a04590311071325205a400c0400307001d036a4081a031404851850300151030855082d9141c101044805902c5100e40ba485500001040f01b0300301c20345c6508a05100c103020207030401802841760820b844918580c00c0c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 452655485 1250 452654235 452654269
    0x140f07022205010f0303081311090a0e0c060c10020c030702060705010f0501090b0108041202120406050429030106030507030b091509070305060a12060e0106080304090f050103080315 80
    0xa4207001c01c01200c00050040212a80c40e2480e1400214901441840780010390b1751589074061035071503550000d8400030340e1007000c90700c2d048600115585074030351500e4540920201c02000c5a40c51221406500740842d0b1041240105030900003c4004100010070401c2c501a020006a0b6254002c1d07809003984552400a03402520014143e010450154003c502c0d40c901240708001a076200c10b02c0009681c2a00101c030b00103080706001c00c02296a00c2c60019103922240100c0e000e2088401c034242e040c0e0090781c4054046100840c042121a1922840820600b000041d00c807444450702d0b0100401e0006015100803d03540c3d00004061900070748c066102d82200030a50702003032810090f95100038200b900d02d5401a000400441c107940c2c041d0085a000740c00003080310901c45d04000070310040c00031088055034465100c54403d035400d80c0a2003800d000d81101005141c2d83c90811242c0803e446d21420703182441494040104040303080b0009903504a86203004d955190302010000030024010040240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 452656735 1250 452655485 452655499
    0xe01020c030d05150f04020c070911070b06100f0807020a151a0906150c010b090a090c0611070911120c130806040203060c0c1e0a0b09030901140f0702 66
    0x18411030000260020500b1202c0034000c50313480000303004100e07800001c403581000386040c2442c12854607401030248031001004940e01c040c2d903128840306542c0017100c4070003e03c0e03000130260103009040320016403158003902d200c00c1c000040c01c0c00520195034240b840d020000c401003c106030758828488070039900e0700701b5075901010440304841710060038000320420719995801d000c0440d5050506a40d4411300000b0014800300c02c14480710900c95100e00f460007081d56071030140d028596030780400d180c00f8196003103000038010f809151503001a840340d0400c4050002c3c0d40c8200b07600440001d1068107561100d00302060021038100f00404034011503242c541842c0d551402c01c1241ca9020014020803e1004008020580d0b240c00094688005490103034042d0440c40004040190800c014180c00c0200000c513605510040c6455045d00004120741c1410b41110488400f407082c025074643e0480360703000c0174515080305900060410800031081d040b4141000c00c8050001c1a01030580e1981e0b60003900c11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 452657985 1250 452656735 452656747
    0x4020109270507020109020a0512100203240d0c030f0c051206150d0206040b130f08030403030e0406210c090218040f09020d0f05100615090801111c0e0102 68
    0x30640507103a04500310700d000e181c000022012441400340064041d0082c2020110f01d0908061050820704600e219110380300c0c01c891100c841182e48000c52140031841d440300b0b01c800660b01440889211001102d1003080c1460b010340114900c082560200e0b640304a074101c00b6021481c0c510780c0c0d5883d52b03220b00d900a66441091a0a18010a48921558016064280c540360036810440d4030401118045e40020301440240070751440341d070090140e100c032200218446540e4414503422030900c0e401030b07056900046000c008040c2c00008003081d14500321800c2c04590b0a04084010208804080d02ca0001008212100340044084414042d01d1201429076a4075941c14110030203504202c074090207189800170020300c0d01510711441038540c0e4000c000c0c1d42d50312074070b0700c401c0d082910700541a2001c0c0510030740400d56040b03a1061500910241d01e101c6000b03002e50402910400e002d510060899043c6990841050280c1040300d40780758041480001980e60039540c84010009070100c07071403030741c800100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 452659235 1250 452657985 452658029
    0x4020304050c0102061f17010219050d05010605072127290f0f041e0e1b04180609050906060a3f0b071805010305090a03050304020109 59
    0xa03480340d1030020713000c481260b22100941402034480c60380c514100320f02400c0501c85550b60300120042030481c2000541000c000341d01080741600c14100c1a03005c01c10001e488070000e407540c000c0f60300400f290705200382480d401e51100c544003402d081e11054000c00200501010341d001e450300c0324841002108081300c2c112510641d800c0106280151540180100e180100c4143c018485516a0303902005050034661020440351041e00901d1b6a4001941c2c1030001250004070500c00440e1201903402c00000c42e03190051262a0711405045580345181000c0d01d000140c012004607030031680105034003081d18144108540040c003040e00800c0d4210309050900800c101c0004100c0d000b03000841d200003115503220401c0101d054954103030303d0708403240707200c240408055061400c648000500c035511a03103500d40c3c500d280b001d0b003210307800c02048d5800c0030f194220704060508005403600382000c000a0074504000c0d81d41e014445001000c11900200207821a445815000001e00103a4404d02c40580c2e1148 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 452660485 1250 452659235 452659243
    0x5010f15091113172410170c10091e05010e0612010e040f05061306060617010302060c030c19053309011d0a110d1a06010e0402030405 59
    0x116040701c040c2000402c0c84072154880031118510444100b52a44a00c0c05001c000990032041c607501ea070703005590002c0045110006031070102c0004c01c0c50180503242080c58409a12850b030080e041002c07010940b0318203020b00044544507000c00301d40d03450014811281c110b4802c0b02d540c20060a180000d401e044806854071600010385030b090700d03003800d8400c08901348107960042c0040301000717445040040100501c403001d8140c01c5402480380300503141051321014a09041624022004888801030790240919482804007900d5945401301880c1801841c101a0315010301001c1d100300d200090003200114100700312282d0711100c0056501442e4080c2960b1256034800d07505460b24000c204c14900a41442c074800c80c41400481c1804003400c03490403001c1f800101c0144040029940e074502c1d910305002014901500741590801011041054503080c11820300906050f03006400806131400001c0240c4001c0060103003012680303134550740d048012030344040b090070071a400c5403000082c4814008042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 452661735 1250 452660485 452660489
    0x3070303030b0f1f030c031b0f02070b041401050306120703031206080c0a0905190e0309180105060f160804120b0f0402010518030f121e070f030c05010f15 68
    0x26114004030203c40d00b48030100101113034006003812031000c00348545020794003501200180346400200b00342400310f018514078800c0550030104095004441d034082d8100a5100506010441241003500c7e0943c40407603da8010000b50501c600400000c0b1f4503110000d40d4080441e0301403c0700e00780d0741d0f2814094041c0c4130515a03091003904207000498846170000d82400d641d0b90241c00000b07030500d8110703820001e0501030302c40564000c131800240300c40750480c062001c40c0140400a569142c1e0341000b044000c26140c10800103005c0480300400c027a94901042c1d42e4010f4001509543d5650504c1402c04618803214008104001c080f03408914020848144500310f48104642c400c02d031145131103c0704814003110000e0005808018400c1d10825881c004104200080c003214043e4068814403800c01107100b4100c48140340102c0d2990314845034000000f00c29905403c0907180489540f2503040060313481c4000740501180d40c1c1c142041000035071152540d035006e00030402440000c59280b018540c514 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 452662985 1250 452661735 452661739
    0x7090e070504060c022b0803180a0f1707080d0c0e03060906220c0909030e0a0605070b1905090c01020601061403160903150b031e0318040b03070303030b 67
    0x240000c8580d8000c908039025038805480e103600c44004c135400c0226000001094000d06810700c98848495000005401d401c1485092490b4480c0b416404d911b0802e00340813040d94095101069410206101c030b0141030850fa04500b000b08008440d0035140d20741e00c11903c0080c06c44400069844024400e03511400c0c20621b40c0d5203442165040c6003c00d9920070003a200300029170080d80105101604030310545201c11001c0241d05044962500c4e0480b0440403a4081400311b9165a510002c06500000510710200110b9001d055181801c000038840d0081d80030090400301e102c8081444a0404552840d18460750082405135141ca841c41c0d80d00e9800b078008503405032080c44008148640940600407400b00001009411961026030071082c51056031210404c1c0006000c012000c20402d6070139a2030f40d0003140f00410100013100034586005103d04060802c407040783c00b9459000f02c00320840e2022840c82880c0d060388042d000019008081d4916415811310410500204068054009080021007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 452664235 1250 452662985 452663009
    0x304050106060e0a0b1903150e0a0e01020f0403121b050a0210030203090c15090405040f1b1d1e07031d010213061b081303050f010b0616080f030709 65
    0x1443c0140207806005000301c81a00c941884450000d00303540c0944031359020345250100d0819411080102020600e80142c1d0030741c03c022040003481d22081c018001d001e24020021450403020503041c41c3c841c060313408028401c5020b01d0035100854030850030071965101d01ca54030940a069031401756031710500c09800300c0c062044001030302074090003032094a1144030315601070701000310640c007005118000008200e1303582c05d05110400c841d032135920a042c803640c0301c0c80b03288206001c0c1c0c1c2001c880002ca11082c1d02030b2000154000c2c000c0c1612018142c1c0e010003060701843c500d4480c00b00541d25100c84400801e205010003040105403a4103410100704c00007041c4030b1402c040440700d103640c00d074410b1590014140d51160420441640306102c01d0145900340300032100c0708402030742d40f404240d004450200c1072240fa42400d00501000344000401905080000c102000b454000b1a0042c022207a00c0010450000c4400d41407141d05400c85a40c00751a905d015541c1c1f43c4044058802c0355980100a141e200c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 452665485 1250 452664235 452664257
    0x7020c010c02031216060515180108030901110a02030d0e040f060806161b230a0b0f0a09020303121e0f010e07110115150e0d0f02060f030405010606 65
    0x40511070020700320b6000340141060790843c151034072003680090f1845001c404040d108201150740c0344995806807113649261105008994100801c0a0401c0c1c5150200f0b025003004101016000003121000c820a007400900e00f02c0500c0014141001003101075018014091101c003800d0348646c0501440800f19010020031a0640c82c02d000c442c140c0c0541c0b0611b07441030011900e0310b061044245040324042ca45400000b0901055004c000502c90b01281c01616480020083c0030700301c0c01c40a454040c5c01c0042002c0001c1e45c54004100780054408100040400041015087c66030482d10607550080d0860307980e002d034140c148105440c22a90001d440569022050455068800703190041d00790030b10f4611140d00700081d0540d4480c0152001052002d018001c0700a4039080c003a02c610000f59900079140305d0b141600032146503d0108003101004620382030610306640704001e000380f03160015215201c03442c1034404508a8410030b4032042601002000300420082d054000320283c0740941d680c090141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 452666735 1250 452665485 452665487
    0xb031605132d0e0f07030201030c17040f1401020a050d0b100c0311070f03061e06060203040b071b0f03060c1b1b0306020a0215101d0c040305010c0807020c01 69
    0x84070300307003107402004040018440c1504120800b0080311498100060f00081c0404400c0c9080100380c002c5130140c204440030410b645e010700c2038804c980c060b0b052003004504c0d60b01480400e00d900a10090a4104446044080c081e090300112104000d0400031591403624070b0300504030350043c7d0340c400c089a0070405d40a20034102441746c41f551500c6070312000d107002c000359400d44108448072451102c62050750350003e5a210143c03084001540a41400546100c00d90110454115070004141c02c440c10458200032007903000040310110740344081059119042490700d0076204c4481030200424071520000411480142001881100d03c0b0380400c2068142d900c1050300c00e02549046030380041d01c424160404030300d002d05aa0b92224140406440c1c0c180c5a56581080380c000030000301c016408240d1411040403c4c040058000402281540c901032801c81c66008bc62194441d41e40b45000d03040204003a0080071064802441d030020003808440941d82c801810300004681d0f03800148690320b01c58a0719 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 452667985 1250 452666735 452666741
    0x3070c0204110a050f1617070311062a0f0f040f060c151802040c080901060f0302060304061805010c03020a09050402030906071103160c030c050111060601080a0b03160513 75
    0x1d202e141d101c4500b4507074585240300322a007244407065042000b04407000002141301480c1d0000d0060007190503188d00e01400d000386404030703040041c44c841d13218000788240c02e0b04103456805002050359601400c5c0100d5034551070140a0407401107800403002c5800701b0031040c1503018200751011460b007002c0056468408851085001c100030b0100d00b40c1102d0900340382c003180c0280b00e6000d20b0300401e404500c40b690219040b91900d140b040d0000d0280014480960401c0c05450001c05a0f0000ca644590858002030303010720018000803d440c0c0d89411050404d16055291000542c100008110301c0702d039103502801175840f0294440020300a034501284c64540740c030179a80902c501c100103201035a20120160b44010241c000c2800da803005000c04046030309031801a11949110700b590009d03c03459450030580700f402e2070300050b05000b690b00070070744e410f00d0008245a00c41400d10f082c420039120049010000c1c505101d840b41c06020301e007005420032201d0f07898142221000d6030401344c40c00e1202029421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 452669235 1250 452667985 452667997
    0x120c06021204140f0d0f0303050906070914120a0516092d0b010201020904021c0f231e0c09010f020c03030409090c0807060807020c0f100c150203070c020411 69
    0x40000007400f84107250801d207160280c084005130076003a1500e456141d0301c20089410b0301c01c0340020f449808120888800f40141c6400501e07030b06140304100d0070050120500c01104a0407801055140504031391042e0070844810360540103805c2d60050300361518400481d8450b4041d680800d4282084114030700794001070045054040345000c2c0c0a40c08031200400a401b150500c035045640a110902c000d540381d200428803142d002000305045070f0740c43c07405819107440c20828020700b40b90400440d480031740440c4c0b030111499084032412040c1e40e4802e01078030032920401c0800d0040442001c11003558001401000450002d8032809514906004126541c040d42c0381030715010740084c842042141d070305800183c035191180c20302666071070f01e401a5a01d450619808074000440400c24805020740501410880c10000c1ea00c003442e1a80c2d00d4040740004034074950410801011040700c07401d0240f480c400d5035580c1d920340c10a41da24140514010444a200b0311b060341702e1480d10804511644141c821100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 452670485 1250 452669235 452669249
    0x30306062a03030b091005011b2a0b030a0902010810150f0e030a05030301051503010b0909180708010c0f09030c0605030c041a120916090b0a120c06021204 68
    0xc0558000020700706400c440400440034191031390002416a90f800940300c0c401c40301504489285d40c40c100c001007820035140301040580c07030030035580c2c00400c07094005804148074090384010358054402050100082591021034084004814401226080d400102c0824000d99407201c80d5200c41170a400400780c1c41c894090746400d1140b1142d00107000303030044810a100390900f1402e4800102c0880d0074241c040c0c400b00c070a40c10001c0140000d140a0b4401405211210745113030440d814940d84107000e01c03502c0a510301c0b5820800000d5403c40f00303401c070326040d1041101600c00050b689c0507280d01a01004c014900403c07a41e000c00c0c0c0995109010141c201e1343c00007407080da07440c0303002c00a5a05510241c04032500c1c030703006c002c081a21400002484050f8959010042e41c40505650090b02c003000542040d213150001100030070b8a12000745204261030701142c00003040c0d1941c034006070503003106a100008a81100b0158070a2040f400e003004101c4100d5029181102031005103420203200b1401542 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 452671735 1250 452670485 452670527
    0x90c020d080a0c0315080706030501080a03050d0f2d0f0b1e0607050d02070807050a181e09030c050c030a021008040516081b03160b0d0207020603040f03030606 70
    0x10340b0100c0d01c1d40001040040038180041d4140844608590104541e00040e060f98010541000030f0f50f81481910300400b0000c0c041d040002031076500a10364441c050280b01c8040d142c00003d85c04001982c44400400051202d45400104108034090f21849000c07500c81a90f262103803d820440c1c0e24040c04e10303100f41c0100303100d243d0701c4216610380140c030940c01c815130072503000e000c00d00024404010380b40c1d036429035800404c0100d01d4101c04d545044c0c60b42d00302c40d005282c0c5200401810001410222440d421100042400f61240034403c0702d0350b10903400303124400e0030a0202804d0627042261b5400c0d00e4043c0c820760310b1402c2020b0a055469a005100a400c8080109445417003032082c04ac244d00300c3d111704203440c0550316045003082400c5041d000030f042e9820450840b11406950300b501494500190094101c5989440003d100b880c420f201e5800308000001d00e1160704842d0390304a49096900a044030780f241068208114003600910b0200c000c60318000d008103181e405401094516280c0302604 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 452672985 1250 452671735 452671741
    0x605010c06200a090305060903130b0307181509210b0c0c030a0305090c150d09020613142805131b020303061813080a05070b040b01090c020d08 63
    0x20400810016000c00c070545402d29580d040801600001c10000030710303580c1c8656290550a200e0300744200a00320413a1a0300401005110704148807400e0215214000e0041d140e6a401e0826035611a484030001c017401d01a003c08623210090890241000c0d100b07584190a05407164400d03003c90b002d01b800c410707851b40c034202e100d400581807403c5164040c0700c12410a0802400c0c50041d40b55070001408503011948507005c00403da081001400c1069408998400182d16841d100000f940300e06a00404001d440d1407100c1d0640d12041d0440b10030403140340c03c0c603004c03954941420940c600c144000340d2080c40310382d201c282c807a9450255032030722340c0e010f12075030b00924981000c020045555190341d040603034881c80704c1246071800120018005895030041e5960f403400c5000c0182c00407854040070b1100e0f49031403d102100303007240079649e11203130300192581c0d039180d28180589075409140e60042219085004020412020340000c0e4103c0d4003d000134040c0e981613070300598640510184510001c5d1800c000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 452674235 1250 452672985 452672993
    0xb03030f0a0504030b130b070512060f0321030916080d1d0405070e041104030302060c1b070605130b04030b070305060a0f0303051911060c0c07150e0f01030605010c 72
    0x709031901d51414658642030740c1341d40d0f10a0f1884216512074421101660038400d000b0700840c0c0945c0103035240341603498851011160868020050000c5014640050409010b80c4040007100100304103800d0400a10b03202c1d42e6180c03010740c41250101003c0c06442004107154450210391419225001d014000d01d002c510001c461400c51201d100c0d011007d20b201102d07003a02c40e445074034087c0ba2199521440d01c00b00c002400150b418107020f03001c99640400013040801e5000c0748050300140300d241219950700b01c041112a0049903203001000500580500051103500100201510b03801c811442903002c4d6600c00ca44082c2c050b61001500e070040c0040001d12440c46070307209550000c001044007000d141c5550803d0000c51054000300d0221b41c0c00120311134141c01c0d4041018403c1d41d18980910581c49084040f84c03103000250811014030030100380800986d40c2401900d0107400481c50714a00007000c2d16005140e403000c0c1d00d0113401140c40b40ca036031500354400d00030305c1705441040c0c43d0120305655650f6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 452675485 1250 452674235 452674237
    0x203070501052d07061811091009110f0307020d08091209060c0f0609011e06082119120f0c020d110f06040305090a0602060f040f02190b0d06090b03030f 67
    0x403070b00e100082c101300d100001503241c410440d185c907030b1031165007034508180b070608500300c491000747e0300c240b45a0040101c100101030f040d40940700c07491008140d00b81c200318081014003503007240030316072034010007000300d00c0c0e43c0000c8108a21032075a0300c42105885208240e80c43d4120001e100806031400c010313803401c83c01c100340100440703e01003084801c612100c40e805410403500b80c440e102d6994440c2c0900c10b54608410001d80100c3c038030081041168a010401c030742d5030080a81801e031106a2215416901c4c603060305640c448003008c02400ca904e0605c4500a0807401800c8104410528110075001d15041d80d20030074594400513001400c40900340c80003130f103a545a6040000303c912844000c8407900c101880014020b038400d0316603544400b100010030004140540161045501c80010804d4485000c1006070b007080e0040e140c2d0100c80030701e0000c1103040100e1741b90442e03640b038156400904c0f60142d100400203074407409420888180c0300c00084007983c100c1506c4943c180c2c0240450001144908 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 452676735 1250 452675485 452675557
    0x903020705040c11100b0f120705091902040620010c0f050f070c090204060e0315011802040801050708090705270c09101707090b03161b080304020307050105 69
    0xc284031a00c164004440e61811700700040307201402c3d440d00d011855505104160001040080703800f0000984160741d16503803000188a614803c00c40c4401048542446007010f01041c110036106566a40c0c542d00060607402824030034080d4403412141c0c2400e012418460300344030706480c0c6d0310310f00da100c0281c2d8201e0342c5030443c10802800182c108401c070b000500304031a0000412035501c001d81c44620300400507010301405074019009800c03c000d83c03024a04104656815199185000904c052803240118000d00540d08030030350961a0105010440360802c60709446201d82e8001c8801c41621501880301e00704201d0400b55440c40203040c00b40d00309655142d8664410403180351141003d10803000208421901e81078400400c1200c0100c2e01c80502c9071400701e6001080c3e0401d603aa0350b06c1c006c61401544401000f003000a0700150401d00d0342c62042061411780c092031540021440102d040c2000c3c4d55200751001c0744244500c030000034480d4011400e41d001c5114400900c48000120448211906554 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 452677985 1250 452676735 452676737
    0x161d12010209040213050f01050307270f080a0209150109030b0402132a0e0105040603020705010b0901090e0c0f030604080318030d091a01030206040902090109030c030b090601090903020705040c 85
    0xa102c4400070ba101c070710140243c4840016001501031030702050007120800342c9110703810403000300304011495421003060140c01000c81c00e000300d540c2209204004c071075044d4004a50705407444500048607030000410703460890003101c00c100e0ac1d441700e65590400508196409000c1041c00008001240403a04556400b900240c08076800405040b807550450b240f61800c0d01013003c003240824a9074810003002955084281041c0100240d00b40001c0d286009038460641019000511282000400c4d001060541c00107868001d95585074061071011b0702001d0703000043c602c141d00207245286003003800e080d9942806406003905848135243d46c0c00700d900042c00d2541d480d521001561650004000600c81403030000000200707401541760100b2031003039243c090f291030901d071001840076a40d050700b180c0440b0002e81300140d40345d0001d001600c0c903504c40e61010b003018019080010601540407030051245a501007551166a2142006800c450212602030300590250001348100d05040d441003152802c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 452679235 1250 452677985 452677987
    0x14070e010c0507090c02100501030b010302130207050f01270206030112140703150501090504152c03040906060507111309021f09050a03150c1412161d120102 69
    0x944800c0c1c42d100f09540003001c115581c03042d02400b01e9043c02550102c40200100780040e51554940640a010600001c1d1088648041408120480341c2c112003d0942c0034064903031b0081c41c5040c00d030007008002228104101421420040d420710000301e0444140c0c0140440d0442cad0030813001c88490003c4ca04121042c5d111000c0c5900d03400010009a8000c40c85004560300490004040005441060388034045044c00c1070306000020f046000b2075910502e400e64002184c1003452181480410f2400f03003000c61565900310000240c2e0301000610540b45804420700c010b694905040b01c4074400c0360f43c0503050810300445840b03240f918100c07200902c0100000400c5a42c455000100c8030031501424104442c02c910242c4041500705a407038000300401c540c400050391950312800101c0d4584561646e034035584002800e0300a001d070030401e00e84140d07030121135280c0310451003500e2448001d460001104100c42044141c030b81c0f19801201d88100a088043d6002c850a81842881c2104040703c800c1950 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 452680485 1250 452679235 452679257
    0x80c030406061a0a0320030a090c1509030b09190f08040e0f040204050a020a0c0303021b03040305150a0c0e09090a06022b1103010510020709050c0910020114070e01 72
    0x5031960034495034000304480c0e135203d400c014060212400162000c46a00745594194004800c2005596000d60202d8000c42c04080782c0c902480c1e10b5210360007000440c4543c5a50320395050b0311800b150f058901c03c5405101c2030f103c0c90314032651014400a13001d2004820407200b0b000503004002c2c0202548100d0341d45042984461903121000c42c00c550f15501c074100b0004020551030076005558101c1d103403810031407502d001244002c001c40807110340034080c5900021000d0700c2c224a1400009690b0021050f0398540b80c480c500b03991110400c00300340600440718800714a100d6078130700c255a0185916107070007010040700303418889000001020300000d8007d4401010101e5110300007000040e495590100245900c0214500342512401b48001190b180010400c203d2100c4002c681c191881140c50541522026408030706c1c14aa41e00071403281c500f4402802003000101c8007800c000b403011540c48100e40f203452000c0b4201c51000f180050b440b4040004555014060300c4640c035000b50614000c00303c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 452681735 1250 452680485 452680499
    0x9050622140f0102032d041509051203070c050706080c030f092b0f0201110921030708030103020f010e010c06050a06090e0304060315030b040b0c070f06060501080115080c03040606 79
    0x5c0c0007129802c201030070b240040004500440c0c000d074000180e040c0e8844282c105030326401403024a16400401a5a075299094184032040040c1c400780764810404507681d2400703400c01011100c1c041c0c0125018466000b0110b00035005031040c2d403150000303000c62030441d500c44c6800d20445e10054a0740c0f5090080a0004041503016050b08800b503d00344402103882000400050500800f5800b40086904d132a1541e01424601d0085613105a0202c9540c625401820000064120440c004100c68400042d49078104400800650f040b0303802282e140c80030042420056482000c10b06405000950061a80700059120782c000c54014100e105e001581548602101c41110a082c0d010300d4107600102d0100302896240c0200f02056441169210446240d55a5540255800b51000b42442c2d590400a501845070800f43e410064008041c20000b11041c1032810003130040b4060740d40007840400000c501e074100380c0305046060340c8a1751840d00554405800b4846134001400443d041c603140c00000941c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 452682985 1250 452681735 452681737
    0x60a020d0e0406120309060f0905220b061c110301080c0d03142802070302030d120b0a0b0d0507110a0303050903040b031e0a090308060d150c0309050622140f0102 71
    0x144c3d101e40c07140405070b0709010005c0c0c00e05180ca00c80200b000b1000c1d0302400240c5950362005107000310500c04210464403048650003405400c4403058215101040140310541c04c1105200000d0940408020801e01c610111034244400d001c0c075003841e03001d900000340c1414582d208100d0346000f480c08802c0e20344030890090480d070001240b80d24054a0031140b0b11102c0100c400000030052500041100c80d141da4042501d800903101d03c0c0050100344140c090940d92580c2015000303220045c14903803a942c0302d080800c010782040454001d918a00740016040900170003480f0070b4649824001c0c80140f0030707664124054800144411400d000520000a83d8078048000e540aa15029045490058075113a01000304000070b0020103e541020900d070302003508100120b800a10544501c0c108216508080d0b940300400c0c6004003509d49000340030070704503605a2242e40f82c2c0c0d00c0380c4190f4816454148102202510880c0c4105910000700f1240c030016a955030300a81420b00d0100f80c0e85005013902d019822 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 452684235 1250 452682985 452683019
    0xc060406030c080105090402090420030109081803150a090f020301150602150f01030b13020d06060810060302130c1e0815041a01120b040501080a020a05060a020d0e0406 74
    0x442d0300d44401e10b04258000340e80c1409808143c0d80701c0308501c0e0503000502c3d020005040600700c0c42c401d0290a1440e80e040700b0604100f1006802071104646031300d00b5291a920020a07a11440441d40300e107001c0c2e14022443c0c9480122100c030390f420ba500d6106104000382000d034000c0fa041404512420016202800b07801451289000480700c1180f600324068145110030702e6414480b0040420440102e2960b05100d05503500958185684d658400088845a00100f0040d502810100702c207030401c5140c5d081007058620f5141611100d240b00c0013183c0a03910a800000d60006101078450080002948141e000303500c20300d0085040320b0b4023000c11100b2010009d01c8e9001400240800107003454021038107a00302010740d020031014000310031920407040c00440d07142c10841c25080c40c400e030300003542007102d540c03900030000c2045594032030f41c0079555100800100d0040004000004403840c2c034400f542c480f030125402500700690b41200c200c451f2000104450361143e511803002c61803007014428400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 452685485 1250 452684235 452684237
    0x3050a050706050c0d060605120a05100503030313060c14040302040513141605010f1e2c04050723090121020c0f0303090a0f141c090503070f030b090c060406 69
    0x2550307405941c1070320300f46d035459000f04007440310800c24034000d0104850090703403101002c2000030301c5407100400601041090340c02594584008030500c01c030b0401d401c40e070312012441400e0030403280c485e2070760075103013900b800d816043c1d006004d1100300098101a04a1a807045903030b0038402d06c50045940c0e40c28407042c034140810782c2d81e100441c0e171240220400c0801010703150909004420a004107030081654007038001208201c1300304541480807902401c1480c5483d031800da58904140b0701e6160300f50000b85140344091103542000e000c110054003541c2000000d00c510002c816004174440070b00511540500d80c045d04010f0f03016102c0400340c2e80c080c880c6004840c480c60160741d842c0960f03060380c5006071402d0f00d40a81e030004c1003032100042002540d445155404030000b01142410b08201354101990301d01d8601c18050700d692544100d100c00404203c505c80d1791562002c01b0b44a02c2030564a44003406080340d941e0a041050000c43e900039482640440400111101001c044005c00c0554109911000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 452686735 1250 452685485 452685487
    0x501090513112d040f090e12030a0209150310060503150402040e1501110c0f040912030c1205010e07050d020c0d09090f0e030702041107051606030c030b09010303050a050706050c 78
    0x5000510307440d9060a03000c60300700d4181c201820708245d0400e0303845500c19809000c0d9940d0a03080c07400010702441c00d00c9407040d03410a80300c0c0380c001c0c4200041c1d440721413814072400d070b030542d00403030030220703005480c060141da400d10b20856081080c1a5000c5c1e0018110b4810050580c005048680d51400200094004014114018285a40241000d584034840141849074180a4001006002038480b14148040314408164480040800c00500c82c00101621118411121520b200e40582003814402c0e80c0307554100c1d48080d03104004048503421301568003140500f9004c076683c81c0c4502c1c0038114040c0262030061801c0c603c000040e02d05001d03003145001180417540104104071842c49074102d10441c0c0c4509215529854480c40d80380e00c11524002d03c60750361805850ac3d00340c0c280041c1c5664542c02821103010b005000000c411141581c480d0100003414944d005c14018802d00404807407503c040c0103107207541d00715031f000d60300b0342c20910040080000501226001c100c1602900d8040c10481000f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 452687985 1250 452686735 452686777
    0x207170403051501150e041a060d020702030712030e01080c0408101d12030c161a0a0b060a1706040f0f1d0319180e010602011e06050109051311 63
    0xd090740f001c2c16800b05024502e40390b01050a140c0102d14001a007100710780c0040c01c518030007000f862907212003045a0300400c0105403004042c46c00d40c0100080c500842c101d816060f6103110b17400309280c20f102d009001a0040714040c5d032079402450416040721003a034410382800d8481c040b0a180003070f0429403e0701c0a8070303a46001c40000c0b031031036000590013038440504181d003920020101c49100181034403400e440001040c08419000740404000203502548172514411004a8407080020999444003924a042080c24071032410000319541d10045840b42100d565070142c1541c00010028000d640083d100c41190324052068070810b0001c0c0d101c0c4200080402c03071925052507210384049404483e601c200004030307211007400ca80000000c0d40307241200c00e4450001e0700540e1051035500c0488501d00c0800045402f6806400000c400c20403550301031840c0140c160000e00b9580c55114203408205200d009015a0074907038100320f600c141d01e11300403a0f003618103062009103a00a4000c481101480148 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 452689235 1250 452687985 452688013
    0xf08070f1703010b04030305090a032108012304050402042c1204030503030f040f02100f0810050a0b0a0e0a06090302130e0304090c0c0501060f090b030703080d020717040305 76
    0x200701c1211002103070490566050826501d13041c4981d02007d0144400400d054074030343c0d289615400a10340c400300c003118940c0d424020440306003046a01501040520002040240f00e005c1a0700d105d2400140e0228513440e0001440002d00018000782e0f00940c071000454903280071a41d141c0302800d161407955180400d00d02105040080143c40050369000801040003caa400000d4a03080340c00004886100d07103c0340b42100409001b5003000b0b400c40c1c81d08010441c4160004212418a5084d03207c0c0a41c4d641c40d0500c5c0c600000c8607004117548507075900003c0c0302800401005d440100c0050501d442180c040400107507440302103600034000581d4400003031045040c010f044c41c5410308010014480424140701c001d0301d13070003540a240d011a030f81d1082005020300c0740c41c801c4a080d070484020410a5101c1c8040c1c105030406000300c40c0c0c4103003041800111030400003164000c8a4000f40910704141c00508e129001c1c0d405201706541403444404079040507803411008000551103880100087c6401c514 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 452690485 1250 452689235 452689253
    0xb070302070c091121012c272a180a050a02040506030108060916060804150908030a09021002030c0a0b280b030d110c10180f0e010b0304021c0f08070f 66
    0x102c202007010700d114200c039145005c20225130000032008d05009915540340c031011201c1030500c000d45843c440c40c90720318a014074402100c00d01072030800115424450035018020201d205c03400703510aa80445002604101c81540603c2c0c12200c1c0c21009454140d0313450009040386c0084c0c0100326680c108000b4007080310020080040c14045d84030805040501c0d001c0c0141c0724042c0240081d1150030220321351042c0704041e43c0101d0030580c0c0071003e961241440b40b80c0300c0040c408200228002d810261650700c59500020a9a82040c840402440c400d6100d64403140c102070007401d10501c00d40304000003200a40d91035000341c00f9540a0350006144c0d036080080501e04074a1800d100306111a03148100300280c0085003104042d802900d20403207502120700c085682d20401458080c0101225034046a40c0284140d01011123005a902c01c6441e601c1c0c0f5454481440280c030001d6106040c0c1100030f001140c1840741e19410360260312902049122600e416071194421801260700810004160040180082d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 452691735 1250 452690485 452690519
    0x20f040e0f0412030b06160b1005120d0507050f0a03050a0305060d030923030f0705030609031614030c0714040507090302010f0c0203010b0d030c0b070302070c09112101 74
    0x5080c0001d030400d40c0301e00000515681461041544844039400c0ca9100d034000c8494841d80c600c3c0700030003542da600f0400080c01003500d24950322090044005031502d410580e0065000b01c0c01d0141542c0c6a5120050710141e2001108950700d00800600c0041c0040c20710518241a000340c1340c42d9035858014200400321000148140d114840d072007140750121380d10452100941d13040180c1d01580d00030803c183c40e803003181910120740c540711304201840990008911201294015001c032006a1a4965401d4a074050b2a400b44098081400f5100c00b00b147c041d00e84450181c1c1c0c0d4140d0746002841c1c0c0140d400c10368581c000e00e40300f00c080035040b0500d05091050603844503007842c10b02c50150541e40000d0150394503442400811081d40301910556a0039409a41e10781001492911411140d18014001c41c155040540b0b910003110300180741d840c06070007280c2016900c0140d020226082c00c5038417001b4502d1b08104080000d0601040c8030652010b2503070f1400114200005c0251361400300560703100400d007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 452692985 1250 452691735 452691751
    0x70807030908030c03041e1110080603060c070206040b0408030406090801050601020d0e03070e0a1b020a0503220909030e12071a0d2304020922150609020f040e 70
    0x20a4071000c100031900ba00d8100240c80e143c0d56680d2a45c3c1005000301030206801c808100424400d90208001000d07600c01013501070742d00b00314800d41d481065841c003600302c504a4060700b114000900d0044000018105184002d200d00c0c00c05861301407010441c1c000e904007501035800000c0520445800040e180010503032a802401540341a1000030b4890041c03e05840600c83d2034000c0303d2180e501404000c0c040e00c0140b44104a80c80c1040c41031300600345c4c144118002400c0007801080c038901c00b05070325511941000046150260050b070488a100c0458461480e4000d41c410108010703d060051814881c02940d80c1802000c5c801d00700020480718508010132540400010010601d21080c10451210741544070b035110904500f404002d0222522038030307216900081c00c0d100c44103020681e140258000d03182518160366800c594980d495442280e100f600088040307100000d6a4080c2d55109040081000308a003035543c0554416a0014004201007240114042c004441441007080c0c0c05441 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 452694235 1250 452692985 452692991
    0x280902010207091e050c1c15050a060203120c090a030803040501060905011a0c070923090607081503011407050c060c090d0f060207231b0303041203120903020607080703 74
    0x1139030309a1410f401e462212140242e4907100041c62803402d207402d8500711000d850b1000c03600220324803080000c02d1490402e583e042440c410200707560510078001c0095980c580c0065261080707424600c4640d0000a1035040301003820007580d006500d801030054011740c4111111501d03070034a4a400e030300b0340d0001e0b0804400c0524020040100840308194104201104c0c003070720b40c2e10040710359024244403240e004080e032541010000c0e8400b100c02e540e0002c8500394500a040551180f401e200e4840c002030350040300090040020882900d000c561903010175130000c00004d05c0d80b074641c0c04041e1040f13040b40c041c0040b902c082031800c5074190600106911268425a0b80c1c54181e038180003c015000c0c1d4000a000d141c5001c00100c1002a0760b411a41305035041a000c04003802401440d03081910081e0f981c0d10180107298003154100703400c80408242c0301005002d54101401c1c443c6095158620000039010020003580d10340380000d05d0720403400110b0095002d0943d03441c00c854082d2080802920b2401018a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 452695485 1250 452694235 452694251
    0x100e010515010815010908060106200303070c08180a0305013e1e0c010903030e01020304020d12030f150518160503151809101104030b28090201020709 66
    0x70388080c56640c1301001982d0003124250f49001214421030750703005125544600f40000c00c00581105201214219180000104000300c001054480c04252801d0011840340000c00e00000c000b0700c040e0014074007619803a030548064000203002d0001d591703c15940e41e59684045449100022080e201c2e40c0c00d800241091001c0041004c0100c1d000081c096100c1103001c1600110354000510014034016030b80401074481043d00c150b14000c1507814001c41c0400e01d00004001088070600030703a4800d40d001090f02032194619220588214041501c1204040c0d0702d010f041c0520fa11841050381403680f41c05403000042c105814010f802c1c04852074000041001030070001c6020026201645000561603c46c1d01c98990b00d0100003000342c0b4042c980d9222400c0759411602108038179449120304440c00850350b840704200f1184044074070300303100486900020082170011604c00c51039160840c0c00314081613083c0590f600000100c40c401c80b014140240ca9001000556904100c40070103042c511008208d019 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 452696735 1250 452695485 452695487
    0x3030405030c0405090109021801060f08070804031206120609230d0c05070f0b130b0a0507020d020312030c0301090c140901210f15080708030406140408100e01051501 73
    0x180142c0051440b4944982c00910318407000e401c03005440d80d02501030b016000d54002c00d4230811209016000000d1041050303068149c2c80b50f060140110540d45508416803201d0b10100c1325003000114405100307450304000036000024020262049024a000080c10000e900d000800c00c2c0c5003a040f428282c1000780d01c500300607004200e1508507182802c05600c1d03901e0601e4581d0400545034004c04840b1040ca01c0040d440100c0d50086c01143c5201904121003071302c90030701104034007590340e4403400208203010a00050038603600e4a107155000904035000e0b0300c00292800c1680d402141c0780da440c00400300040007a080540140303e15010342c1c1c144120400321420722240280104c0311f4181c10000094140140440d0810002c1d501c0d03480d00c4014440150581e40d01c1d00504550244103010070101240020b023008003051040551302c00c070010714902494a4401c03921040b03c907203080c0306400c003000001420a0200701c4050f01d8541c0410102e40061145003160031120010440b440900b0808980402a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 452697841 1106 452696735 452696743
    0xb07050111030f041506290c03030403030b030f0c1305070c15051605030105061e0409091115090f13090204091a2a1b0d0f09050303040503 61
    0x9513505c640e41c4403c403042c602c0f9601e146011803400941d40840e1401182038000158156810107401d803688a0841e407003514110040f0b45c0c0ea2030405542d0071305106c0300c0d4032030107a1400b034520700c1550030200d2207044102c0c8280060540d21720000e441d076400f0303184404001c1d07040030201102d0451000d0110092a0a59100101701034050f84188420b11900803281a680007902050900102c0c59374100f1010000306c440320b01c0310080c0000303c1da103a80d5200d1481070030300810000f0201000903007804240c0b880d841c48640c80c0502008501140c0e190200c0c8018041e0050340e440be41c5040c080400c0d0014410024025440303401e241c0820180084254a500c3c90b080300c5200088580700c2006016180d21603149295902007900405200c401106018251001106031020707081000f107400c180c1800100643d450120300b0144106242581c4450303084040e0805500035803402c4d05041c0000c2c0c1d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 452517985 452697841 := by
  have h0 := BRFrame.cov_init 452517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 452517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 452517985 ≤ n) (h2 : n < 452697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
