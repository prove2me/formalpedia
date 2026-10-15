-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5198
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:04:15.88806+00:00
-- url     : https://prove2.me/submissions/364b300b-ab2d-4608-9081-11fb05a346c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 934712230 ≤ n < 934892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 934713480 1250 934712230 934712237
    0x1a190b180d050607080a0606050702030604060c020a021c050c101421090703050d05130e1806010b0a030b0d033903030b03060a02030702060106080c07060c051903020910 74
    0x424180c0004018541c8203100600300d00410084c0840b9a4201e0316143c080c4020304014448241c07039040c11070f114040d40c60041d505911940c04180424101c0e44280303106202c51054404d09056500400e915138007101c1c4d14540c510403401b01c8000c0c840140030741208017504036034a80d05054280d000030840c1c0d04551100404640000e809030540d0030030220188000287c8031b0a050b580303801440c20b5100c1400f031205035075502890780601302c0d25100380c04070740c003445c2403454000c031280c140012028400c44c018684450a040e030344440a0448081211600134061050455a107215a200040070b42e409000414000e00040f03a0000010384c120342407080c805070041782e04251000400d0150701440b1031010305030550300d0807104501815030507003044000107401d508858003520350100d01c20403480219030400040c2c01050050080c14440c0d0702c455000000c5080f11404c1514070389505044415003951040446c034000b0301c10310824400c14003007410300b0f40b50030110b003881610300105101000703000c101000c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 934714730 1250 934713480 934713517
    0x8030403060c1205094611211605130b04150b270d02010c030203071e05060f07091401030e03030a020405091008120c030d1a190b 57
    0x400f8401c1103046400480342c40b050105082118040307441e1221280d9240301c200e56604007141e03000f00c1c60031541d600340501038121006d442403402215103080ca100200c640e0f4000003000c203901d6480210200b144000c24800794241c0174200007441c80c1140c0d840308800400c0421104110a0744d44410b0080c141c6403183d000301d003248245001a00520050440040040d048540858421044005040d46c2d4a61440c20318041c0d0220344807624680c40209807136401407450000c000154819030300305001510900440b400c0080350780e1a00c2c00c03032032903501109801310408010403d01c01c0030003202d90460500d100d013038000d06006100410009050040220310040d44c01402410b9129501100ca0400c1c00019240c42c0d0a2000c3c1081c040c0d4014407465200d4103241011445a10070740440100b1100058010507400c40c040441800d56000f8401804007030005200103151100c00e030040c9820100028001040c0c003458504016a2440010206451007a11a4140b16030f14400c0c0494107242e941301501c1c031a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 934715980 1250 934714730 934714751
    0x40f0e06240f01110d261b070804090204030807031d031b060409050f06010f18050108040614071707091a030c1b011b14071103070f0b071109010803040306 68
    0x8503a01c2c1512420114811740740c01d01d5109900211050748880642512904011741c0b0740380400008065907140504540e8241000b21401c00100a2440c180f042190501342560b83d440d92040f0f0304103602c10743e80d03090b0008a407000c1641c4020398a0742d03804d021440d030240c00c0c4010082551040f00c0820138503243c0000d14443d0752580c615099800901e12a2028085841d05011090b070201082c2c40320303400f04030500810400740b405102d44440c545041c60f84c640002d803400700110350703181d80507200b611032540d2000c1c0d11505545641a07644030314030030380b500450400d14a044c51a0f6120080c981c00c1040481c00060100d82840c03d4810f003c002c000c03501036100e440d0201025003912030403028003411030502460700d401d01c00c1900030703907025801c2c0c0c04107212658220710203071245042078421a10001d4200140d03400a0300c80617810300c001401900b00e6813901d032564052040003d00f0740010075101e0020036a102000303000c400710145c0c0201558a0045945821003a5a990040740070080806442e51080c02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 934717230 1250 934715980 934715987
    0x40b04020409080f1810090506072d050a0b0c090612090f030304030f181802030406110408070906080a03090302010807020a1e1505010f090b0f040f0e06240f01 70
    0x282e03038113800755029945108400b4040510320072810224014008a80e021920038090540312044800c050080ca20f004a1a41d03203045600c4698144220603421054100c4540315401c00480c0b260702c2500103015100c210304280b09810b0000303001d40420442003290b01d2983c1c850700c040e9143c183d000e0382c02900c00e484210f0712504101d00c8210300c1c000c5100100c20170090542c0000d884000c01015220100451601105c58425142a0060103112143c1c4071341030180071030aa008640c8503004510000700c0d40344d00040280e460b402035100c1c0d641039001880a000c4003005100b89001040860000c0292000e80d603405089801140b03c0a0b062007080d030001042c01c0d0081c4170120b070031980b002c03060034030558803038407408500c80c00c000588200a00e0701510030794040a00c240c1f0b050b80c4c400710342d0381c01c0780380f038200c049000d45840f4902c9900b090042d90180302e203882d14044d500c00c0980f10b01011030a0400190710920704100100b240414102e400d5852811038204c641c85d445007041541c81c02c9400e001d910050703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 934718480 1250 934717230 934717237
    0xf0201090f0b041203020702060301121103060108060a0c03061d0c07060c020d030b0306360708060115050a1d0a1d09010c0311090d0501110c0109060b09040b0402040908 74
    0x180034075480d41e03190000c20a1080b20184030b50700c6550011011400003004500300e0168140094021a003040180004400d20039055003562040000d60703600000d02d00840d090050a80c0700d103100d640301d1014045100802c0c05111451030300c0385410005640b46c07140c1d82030060b02c1c0c00d0045000c548480046040d00e8401001c5411060700080d06110881c10b41600039035131030845c041c2c1070010b1310308491182d161401040b0710780a0000441c1d035114401030040f000a0840e11081e942da03403e08048a030320200c030020b04c07805009180403405440c0c1585059800790f8100c00012401007001800c00c140880039401080c810a0a615141050201070164001c80c0c40240d060300021003000b202000c00c20805000324115124080f508024012031450003801c3d01a00c061000d8940440c005000512041c10442004125103000380e002094002c50604a040c1a80c03212034031900ca030b5110080c40c004c0c007403180030301c126030b48041d01c4070502d61500383c50f80903032443d010300700030321403600c440ca00030901c034000007034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 934719730 1250 934718480 934718483
    0xc060209040902060f0c190f030807022406030d02030a020327040e01020717090a3c0312020705010906200d09030606093b07030b0708091c0f020109 65
    0x5a07a840925255100c429081406c186400780f0942c007503d03000c02c51940400d01002d034400e0340203440685c5130b0340541d6100e500a101c041140b083d0100c00a07000d221a9100c1c1c00e448000010700c3e610300700382d420b260034802ea458030842135600802c08058490707400000c075010808050030500e001d50996a060010521000c0744d04ea002c1c0c10034400084050041d401001a5442003030b1000c000071014640344024041e00046551022203000104003851002c5a0100c05100060b044034442e041d800034801d90804815800700ca00d02039407024810442140d20076105411580001e00c2d5039890040024150303403680c0220410041d00c0e03507a55920508500c441c03106000c00001b981c00c000c02185000309500d006110a80d00340d0b08000c000200103c203445001c551060710b50210000c02d00c0b00407081d42c03035030359070303006420180e4402551810b224061255001440c0b08004c400890309182400038688403010b4504036840d0005030a102000a000c2c40c0c01000b01703405e040544078a50004d00603401030041800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 934720980 1250 934719730 934719739
    0x30326060915040c090503060601031b0f05070501050106020703140105012103052107030c0e0a050919090b1e06010906270807050a0b271f0c020913030c060209040902 73
    0x189212207410000941c20369030247c1c100c2d03e00350340c2c080046081d80d00200344c2d522030700c2c0c1c500c18640400d4826100c3c041c4840c49802c200785440c4040c0c0c3e80c90b007101c101741e1010005130030102c400d00c2085582c034030a100910120000340314650400068400c0d102d802c08010f542007401903c020704060080781921683c61442603103c2d16910280c0c280c07250f102e411035501c80040d14150500203090700071002d1004614015003155501400d040030f000c007043d805040c80788212440c5400300c030140e0141c0148022640300d1a1000740c035040c412010990012031000d1201d01c41c100f68100261a607000d20b03240b08403000c6103030402c00c0482c1c070302c050341124402403e1403c000300d032000301007021000000d0140454005880305001da56440c5100c0010340a1000400403004441e42c00355110703102d1419003500c040000f00151100042c41c444440c1c5060401a0703200801c548801440c154500004402d42c800c84002001d64882c0c1c040d6001000d00042c4a8000d01c0c5c10380c040f9500c100e43d02c45a11426900e0360141 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 934722230 1250 934720980 934720991
    0x902060307030519091106030601031806090303060518061e150403050d0207061e020c090106110111040b220b040e01090b0a0501120c03140a020403032606091504 71
    0x5500801604089801c0b022840c01e0465640001e10140304241c0b0203038101c1540b0710340c400346c241004902d910242a4070704041d11080b00c049902d0465003103021152190314001075a1050786405000d40d1103541c045481004138200080d01e0711031100d51242c4c888400c81d02004900030010001a08081070180310b40c20017030300c0562002130070811000f001500d0080342100d503003400f280d0040382d84020300d00030500000c144107542044c81d030440307010001030503950058072a00d040100100d004008240c1c44140001d4698620041001c03007031051402c84490520000c0c68a81001011000e41c07003055400441e0b0b014400040340f0507285100080c0140c002c168106030380b00c0d0b8800000702d98001c280a082c81c031a180103452445840c110407100121001a1503010040244d05001c80003000000c0504081c0340e11f030120940000245042140310b00d442c0d0600517212425400c00901002c00203400030b03980002245018004070400380c2541c0d2054044a4000c1c85a81301042c010003410400c2d43c4680050400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 934723480 1250 934722230 934722241
    0x30e12041806150c0c270b03060723040314030316080907030609061b050406031a13050c0705010c020309120c01080a020a020102070f06052707060302030a09020603 72
    0x100014030898010108503400140d8119100040b03820324880e00d81e22520710580040c00b2030069103800006801021041c4007255241c19281e09001c010ba0b11808418070400811110500c520400c06a40d0040e0020b20251404c1c400241a0b058083c2166140c10007825241c1b00c809914000c94001d16409014148115008540580c0e03e40055500c01e0030840c1c049170f83c0c0c003054401e09502e4030410002001380720359071035074403450b00518004800b40d410b540c4800d010f82d07050140c0d101e0f20148022613554141d540d071a02000404455900460409021210080210a40e40c800700d40e0b551044141d030010b0151510440d0104500c41c041c4020415400c100c2a500a03c0c1c012010300f605840c15502006540103005105842d00744a02001d40454004c00229000d207a042d800741c01032030010f000043c5003080329181c80c3c41000b07511600712000c40c0c41c0d00c200800c0888841302e501c0c1c45003441d035007070100800004a103521707041a40501c04c101540480085c1b1842110780000410b590040e1807203a032400c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 934724730 1250 934723480 934723513
    0x1060803030a1404050304030b07030b030114180c0a0b0a0e03060403120c090b07110102120c0a1401090507120309050402040e07081b070201080c09061914070f03030903030e 76
    0x101e8200c80000e16200300311012a03e080301c1d05104582c40380c0907614060551752298181040680715804041d900ca0b0700101c103403024030940400803103030560005c45280c0314a459040d414a502030443d107400109604805440c0d01503207001703aa03d41c118982d2101c1c2e81010840b031044d504d490241e4503119503000d000030726821003542d5520807080c40091084c90448071082c3d4402c0c200340300d140c042000070032090010810308414203030719000510680c0c144071740c12540300016800c1507200c510329411144020b820001d198900c0c1000e0b001c01002400a40c000352940750b2610381a1040c8101351449601078810944500c0e81c440c00351000510864590340c1300d02c0100b001c1c86003180c094020640000208110380700300d040c668481641c5122051914846070b0046a1700303030001d8090000803505210b01841940e500001c0e04200c3c0e400c140408000340004401081040e0f5980340c010380d00301c100901d00c0411040c844140c94980c043c1130100e1035041901e03048004010001000d140350151805410400d0704 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 934725980 1250 934724730 934724737
    0x80a02060903012c1c050f031003020307090e01052409100902030a0c0f021b0f1c120914150c0a020a08030a0311090d060b0d060203042409120302091201060803 70
    0x44e42040b6890b02e0030340c4a100100b007102c40d0310100403070014052142c03401d40010056501ca02400c2e022041c03286d90b603000ca0b18180958010361902d42d26a42c2e10703c21000244551640801c08066085034001080e901e0100002d0400255006000000002e9500d2050a01c11001031001040440d80c91406451550003440500e1501000a500a41e42a0f4040c400101800b2005000c6e060781c0d80c012118003004120074201e0001c5400500300d040c14402e4019000304181e009004a150000c0071070042c40c01480d0000c0c1d500a0f000c0039503444400c81c00d985405846c00c8030506058042a41c40424800c814030f400550b040096111940f140e001c1a44100800030b803d0144035a2030900842c48411805440741c018440041e0300240d00c0e0110102151140e0080b03114200060481c2131252850348540d0f040ea4021101036881c1d040c102141076001846244e12032861300b40c1d420803c02c0da5000e9491101584801e8030510130160003041c24020ba0b40e840d034140c142104001c00800a50b950b61103015201e81 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 934727230 1250 934725980 934726061
    0xd1d0604030c0c15080c16020d080717030f06041d1006060210020403080d0506010c020a14090a020a02030307111e060f01050604031716300306080a0206090301 70
    0x1510903400240d05120704202c3c400744c3c100c0c0d8940155984d030360411700782d00e90811070183d2090184075100c8000b50315029030750060140110a200d40e50025400d1451040d150301e0762084c0c3c22002041081510703640a89000e030001000c850203d580080450300400b070201201c00c500050055030071404040d00c040d40242e00f203600980a8034200404034000030124000c40c032020341141800c100004100032035500c0f4980c0030105041c000c112010580100f080a040c035004003400013082d14030329441c0d01e45080010740c0b1224a410540c50007113140402512800090301d41424004805200c0340043c105020b80342d0120440b01c0340d554101980804181e0303c200c01d560f440a0700021500100e41d60404400b103d09580e002210020404203043c00400994040851a84030031240c0c2c0c551400590300000c0784107000401042001e400303550103030b042858040011414281440c3c1402044042000300f0100c201d6901280c0d5252940032038404603016240700103003e0420485460001c240c801202140c41c0e111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 934728480 1250 934727230 934727243
    0xa050615180405101a070c0e01060c0c0506030105062a0f0312060312041502010e070b0a0314100603090609050601030b010e0705120a0b0105070c03080421080d1d0604030c 75
    0x5813200c0042071200403550041143e184070350a0a160342d5039040380107001080c0304602100032150f6804440c050b410003a0803200004d03c0a200c0303441404000351554014010072506585994035100005100b446107c143c0000b200c5c9e046081010140314075003821810030038805030b51103000c4030706e00746842c1d501080d81c10b0b1a01c2000c0001c640b031070030300140c2c0480081d40e01343d40d140b41c5410305050710011280d106210b0119902d8900c1560740000501003000240038611314252030760b5801ca0090182c8140051001410b0280404c200c003181c040b842c0324088503094200052103282c6400c1c050007400080030082d0561090000000412103100c41d4903040303c00d1005000c049803145e1320220743d140300f0595084011035181000c509410019409505001c0050500c513142604c0340c1d031812484000c0390700c1a20000301c085420002c940c41704080030751192251100d0028425140d0b0b500c001ca002d400d1f901402c2513514034000b121000050b404500012505d012a90180344c68680182140750074801190f10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 934729730 1250 934728480 934728491
    0x5030907080f0a02090916230d260708130603050106050c151008010504150c05040e01150903050307060203010503010b01052a030f040b19020f060a0506151804 70
    0x10610210304038014905082c06000c140031070307030200040d211025091040328061100000c400c1d0b1085403c00c001000022800068080142c882801840101241a00070045110104002080301c4440c1c0c10140c00540031040400385140b6a2409014428005106103400a2072008a40c1c50710383c68011200b1640d01881180e0726000215014081e00000c0c1c2050707480421100d104c05882141203910140d050014489255070b40181825203000751019900c803043c02e680c00351540070034042d40c20034200c1c9042c2186014682880202d08050500c90042c40219048400c1025481007100000171500401144d40700d0701b03903051260081d4001c1c0b2030300c0d01c0b0b90b00c0c00c08442d960b540103d00b501c10074070044a80c0b04201020f01201c0d070b04202221600d0305580400c100c0c000e00b04075508017070b00290003c802c01da034581041c04951001d0011a14024083d940f00b51402103501e40002107195003d0307a40000860383e80c503001c0104e000581c4440700c40b03914a401160592122042e1910b0107a41142241e09011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 934730980 1250 934729730 934729739
    0xc080d110c03240c0f0d020a020c0f0a1a0f0a18120b041220010606090902250c05040f0f0524040915060312021606020a0201140c010c05030907 63
    0x1520480e440011800f02402c501d040184142076640740e40c4a4030000002c0d1804010070b034107201c540d00c11583c0c40c01055001c00c498038255410844002010403d4074052644100080015400d000368851041071b0261800b00317808910320b54060750740c14050b010031301d6100d0854200c040c1008a00c0d40c4020441c0b900c4442c0090320151140948e0802500002d480040da01d464403051146050321440070140000061143c500244038000600511050b000001d681410701c0780c0145000031035400780c41c54078010320044404480c140356045c52071340344001402032a0307041d01d00750781d0715030f51507014641c03091a15807084210440e5030400964401c451901704990b82e120398440b00d1003500d00c0b202080305044015031154038207090780007480b03c40c02902c48481c54094038030300805071082500101c4070101101103084ea60b940402c80c6000303600e00b0500301c0900783c1c144a0002c0d5250b10055000c1d0412020303861950418510300c0803130705100c1c061002404141d101c0c03e030140550740240d0720000144141c410004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 934732230 1250 934730980 934730983
    0x2003070e06210d0f1e051602012303060114072001140c01151e05041109040f0b0316080c0d020105071506030c141305040804120f0c06080403050904090c080d110c03 72
    0xa82404942e01c0b41c508100b12901901d100d0720800c1d4049040c014203462031084841080160040441e8ad03c0d0066a40e240504c0010800d4042c0c800308258044e043c401e0302e000a0040000c00100b01d184103000d10b10f9584280103c1e840581503100400040000032002500201074105400e0328001031115070121756202d858904507002083c12003892482102c0a00c0a4034198100030f80700400010f10909010410f00001c00729151140d2144c0595602d20510a9030b00317061000200710744140300350701050351a002904e030f15140048021842481d8030481c5000b10780c05102a1841035070405d4941c0d038000d82c03000c4c03010000c103060b000650344005001c0f0005a9042012445204408082d00d0a24080e070302007803120107088098021a00c0c80400d05c4041000e10007440422126030080200910701c9906061626040f0b20310b40204040100810801010035040412124000016140000d15402508010302441519001502c0d50300440b040300383e5141d44220000351501104050b01d08408001c410035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 934733480 1250 934732230 934732277
    0x3280b070f0819060f0b03040b180604060506060d060905092a01030b0301060b0a08011a1213020109030b1603051f0b0d06122003070e06210d0f 63
    0x101c001003281000410a8190500d4404003400c42100840c020361110f80100146a6031342100c401500003104002c10701004030040c1780c2012081380310942c101026162940c07502d2004201500c00c5860b1004038020382c541d20210b6040302805601003111546504034000900026503140c1400e106a100800f4100309900b070003841c41c40300031408440301d007440005502601c1c16409040e49551307a08000105000c400005150741ca646d41c1c1c1d52840d81d818982c21a0b02e000a80d0300d051407000d41403003100b9803680c00c2800c060b0810f1201d6000c0f40590f1541c030040390b007031034140c00041010383d0010030300403155940400403d034402d1702d840c10f000359580c020384280c01440e1f000a01c00340c805290360030031412100360b008166a0240d02c001040445d140c01c1c1c504404650350031700300e07000361109008000504c1000f6418860400c220050980140303080d41d0381107039250103000f682c840c0d907103240300b00f40d110040c480890040b40c1800c03e0b101d5802c08440c5c080c0405512607406030124201d042c0e04d00c00c1c20707440ba141703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 934734730 1250 934733480 934733507
    0x90b040c0e030d030902030a12030c091401170a0e0d080601030c08041208090a060501080604510e0307020a0e09070e0c0409090f02040b100e040b03280b07 68
    0x528400e403c00204134003500c01030038241d0b0140a0f022190012030302c1e500c460a00008039440219813407500c3d04c0e00916216540e406580c445444126080e0340b80c0c0d100c0d000d0850000c0502d0700500d02c0c0c442200e00300040c0901d145001d4a4410600810b9000d5000000c1e42c6c8540400d803400c02402546010603900c0f03200494004001e6008401c0342c2c9103250040450340d400c581401c04580c110003142d580d14085a03004c1e0800e0045a00990400007007000b00d1031000c00058455007904174018800046100c902100101410305203220039404641c00c0700015000c1c1003d40d80c207418449110712180030764403581320007820f03401140880d10110300076030b0256101d030003114004010840c0710301d8221442c03180b00003d000070004000c100000111f40b1a0342c0a8120007a00848050145010780e00c108000c4440d0241294084c00303c034001c0c00452a048902d150016505480104001e03265000190505860000904840fa034013000c03445401d0000c40c1d12104248203000e04401c0b41c96520003959054000101d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 934735980 1250 934734730 934734733
    0x408060610020f030a170106030e150402043308030915070c03020a0e07090621111e0c01230c090a0b0a230a0903030c0516090b040c0e03 60
    0x454003600300030448180710009403050301c442040030b401007030543d0f001d04400400214070704284400e0020386510240100402c1c2000c010305640e1032600c680b150320740d051040f901944080024150340340c9820002c4080066410465800b441c0f600c658040c0c1c4e030008104040300502c41000c074190a0001c21102102c0c0c000300b1340c501d078400900944606a1010500b01c030600f0140b030b000401a11030603a080090080580d842d00c00d40b81c1010000d2103074050b540110704000c028103400e5149243c81c105407c241d60301c071301f0205085180c102c50210b68492850606a1003004a81c030417010003403003000e004207803c02c10084c80110514095100864003024041c65141041c81c0401d01040114008140c41c5201811600c00e150b5100c4c02d14070b250701301101d032602060014580b00340d50350025901c080804130403109503003407402c0a00007d010741c0d11070000900b400300e40380100040c81003c01144500f08191a201041c1e151900e502c0c101a2429040c0c3c02e01031400c007001d0700d00e400d0017002002c444d0390002c1c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 934737230 1250 934735980 934735993
    0x1209060304150902060307123c110c03210601021e0a1a06030d081e1015030b011103030f0411130914061806010306020a120e160b0408 59
    0x1c0742c25050010756001071004070340d100010001611390030091031044507241c803215141025458103400790b130f800604c50b200f6010ba040a41c851003400e5400c00b00c01d69610040102280c000031050383c014144800d103410381c41c0010a20541120000004042403001e2915104089245070b00c1408001400c0e2000b50258211641d40040401c0d2014140c061141801c201c900040301074807282d039060b103812011b10100d44c0030010403a01d400d04128065181c10203145c0b219942c5024440031110103024040c0c0d655401d01400461590248481b41d880901342d5200210300140070640701400800038650f0150101d004400d049804410100980c1e100b08051043c45085070b0f0b03a540c551440d600c0030409991702c803043d00c80704c5c50302d040f01d8400c0c100a948203c440c1d250380d107040b10340741c1e03d0400c0081c1148030400d0000d4890782050000301d006411241d000001607266041d18005840580119600c20503080c40e204200f00c04440c002204801c0c1c00e00d820f413000c100b6454812076030181c450f60164101c03652081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 934738480 1250 934737230 934737233
    0x130f0e0709152007060318020603040b060315070c02030d0e030307060b01050f040608100e090a112704060f0605060406080a0b0d050a0510020310090b0f0405181209060304 75
    0xc4010071a0001d14000c03d0802d0981c0310112160006282641c60381c0c4828020b2002542510440c500380416203e88a10302e203855000030740c580301c0140300070186100e580104000d82c808010340c0e40d01d407a46101c400700d54034000341c0040c0003810b408800ea20a1141010302d000090250f6103129040308041d0141d4a004266103c010152069845140c100b2004010034902e00c0d07800340140024046950b41c0c1c80703046c2800c01a11842080381c0d00b101a0b0148000c2c11701400070400201866101d50010071410203140c2d40001501c4400c1c0c0309020340281041e4443c00000d10000d4075014420780c801d07901000112501c026090440740103006841d0410310401c0103200250242243c2e9500401001c801315001a00501060b038090380f00da4119403da00c9921500b0400500b03102e00f9100c41980300c4114114030b441520b100452045128400905944c0c03400034245480d0003070b082c50401e42c0a0b1040c040d9040174a80110190250783c0c0e001d6580c00b84043c20400042000102e800420004091b5419912617 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 934739730 1250 934738480 934738499
    0xb2d0603161421070909050901020c0f010b0603011e05210610060503190e1c090b16110105090910060905010203040e01140d200901060e0307031202010e03130f0e0709 73
    0x1e0131303240c24464910400030390782c0200c0c01002d1040c10400c5c0051388540314142402c0c640204070011000716414410031066a0304d960051b00d0455290840085d0318000b85c4441910314992a000290040341c0c90079940c41910220b040a144141d405c5d040b207110340d0710700e5081000c1055038054540001c90820115219058070300039540c8000803458001031100c4200001c41c80d05c0716541600c01d03111070701d41480c5001500256030b08002c1c401e09110510b0402001d18468015989403801003080030102072050483c5d200c0c800360b0b091404050311002207810940c180611501c0302d48903610015403141400710700c0307510100c2aa42118040c3c0c60002d82c903400c0003890349030454200c504a420901c420900b1010948102d0300b080c40540c10000c5e4024009040180011048140c01c61014014000d5000040da18001480b4044941240080342c0329400d1000072030140c010418034240e20b10001c038a110405541c0e8600c0d5040355540c40c00354070301581e01c950703052130840115116800f00d544030508001043c813 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 934740980 1250 934739730 934739797
    0x40507141305090f01050907090e070513030b04030c02040e07060c021c0f0602040f060801050f0f0307050618040b0d0201120c17070302030702010e010b2d06031614 72
    0x101c14220034a6161400301e0049201180c2a030f26556071040104218207101c0d200e1504135143d46840c07540d45061090403442d0800240888041010005984c05ea54001e008001c014541c0000b00402a0031329081c0103007c45000030080c0d00c19480d04000c240c2d5500000780074811100c06481e00c034407030f01d03040d02040701c0c01160b100c00d0402e041e0780340d654030000b880c9045060a060b105000050b1143d05103615030105c00001e41120042c840303600014040b940d505508140203a03421a440c00b4403940c5000400e04001c1680e201907080080030a013008114085501204c04040c10b503410456208001d003000718608a14002902080c0070941c46400002c0580000d200d003000c50400b141c0e20343c9020b00800980700c088440e040043d6000c801d00550650a0140e600c0c09450440240301d4295540000340008410016604000c0020514001c1003a03580d03e5210749010b00821480d22880c2c1910350084540a0041d01c00010707103071071080c452181d20f190a0300d410307100841d22034000780c40c00042c1c81c017000d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 934742230 1250 934740980 934740997
    0x30c05031216080a0b061b0c0603090a0201030f090b0606030a020f3004150c1803060b030d050c0c0f030f0132010b0d02130807030605070e04050714 65
    0x420051500c118080c80c418001d541080b0325040c82c1109507401081c41501a244582c44c03418540c1c3c1d904e60b0b036200c5054800c4e60308142140c0d40e001e00f116110320f00d8200f815071525007042000c02080b2440e0b80201d13100650500030f803030507c000d04a204040040312083c44009144c083e440d408110b480c18084051984a035840340e0040c0382c10790b1070b0251a09900903658100c0e102422802102d4118441c840343e410500b541509032629041070b55407070760400450300160f10340558500524928501c5078065407801100003030916000b41e01c070306109000d0300b00c003e0f000b4040e2150810035080c451290080b500b1215000019004110071203040100450300c0a804a606120b003460f560b403407810a100e4410400c0300e600300d401031401e030760148501502811100050088000700100321003c244800c80e0300402862707200603540c80c0030304000441d486498100380528403501c400070040044550200380191142d03261590241a040100001e0b5a0100d8041d0001039020703515030105e0702c0c804040c0401c807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 934743480 1250 934742230 934742233
    0x150c060103120207270e01020a140310051804050f03030403170a0207081b0f0a0b060d02220204060905040c020d03090303111606050604090c031205040e090102070302010605090112030c05 82
    0x6503440c130044917100e0340d50607500820049682240d900100d58480c00509003241e400a41c1070504113500506248018218914500320000c002070040070540b40c540082c0400502080d580b8032070340710840f400b2404640c110b135280302d031000102d1485000019644070f10351507a505100e0041040c0901c6101d04003602500351b03913400b80700e0710001442002c081d114124130307200506441e199040382d4520703080b40350161076200e0301f00340c40e4013020030502103a05901003801e40c3d40c0002c00d0480d20120b211000c5c10ad104c2600107000c10640e1505829640007070040718481d03582c40b04a80c0d115070801040307660800705100945c0c803082d80c00540c0741c000d4103c004080e000e8100060310908001c4000503550040e1403405210060301c0d9100d0170804d02d44503c036000310090310108075a03c0d20380e94a0001200900010b85943c00020a4000243c4a00111800b0788a0041007142d9401c20280c0c032800f0b500000c03011000740d42807000108450506da2616030484407103014912500d48aa02c4c2035a22504404055846 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 934744730 1250 934743480 934743493
    0x1202061606020d0207200103021c0207050f1e0105100e0f060d02041107030201111207081f030b2205030d020912150f0a020a080a02090607050106030c05150c0601031202 74
    0x3e1645101030704100d0301424481a800300354425a42c940140d0001030350506206100c4040702c0309044000060b00c0c4840c101c01079030792900382800c500c3c100718000030b400144940c84a001e5844020b020044c0708000b1040280145e4464581b00e40000540f07005400ca60310001001407030415061848a800c20130241039824958100e070045005e440742d202d101601c1d4500002c070401003650900c034036040341107900781c850b040c400118100c440210000c0c0bc00402c00000c040030a240e03145210032081c9581c0e00c81c2c411084c2c60307680e28102201080c2101c00070384442003040400012120540313101030141d40310000d07507d030084240300b0310000d401411040f03030040f2000c0c4040c841002c0812503050413000d2040741c4402d910704900c0f1000040f9009000030303006401800400e05580d0860061504800025400368941104c0c102081c00f90144840c046c4c42582003140010a104e1928010b4040d0f80090b80d0088003850001248902d81c030a0b00d1049905900510041012850f000201100c081c940d1042d03610 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 934745980 1250 934744730 934744747
    0x30c090b011715090403081e0903040b07080f070f150b0d120e0612012c04080d18200a03050a0210051207020102040f061704060f0f0e01020d06120206160602 69
    0x2030b440805c680480c00310300e803842400718140c04070307140c00b60803681c0c418420360500d00304425545034002c501c1105490200424008108140d15003500c20b029401c0f111180c0321101808d10380d01e03024070b0410580f01c00c500c61000c964640070a010390f61407080041c204140c03080380c541e24140000695604101008443c605c010020754892000700000c480049407411554101480003280303064280c81e08080c029445610f0724542204058564400d420050f070030b80b100c1145140101070b00503207036907461591660f0500720030010901c2d0712011451011801501a002e4142400807008803400080c0480d446000703d0001032910182c140e1020402d4544039080010941428a00c003009603003110140c0d40214080c0580b01c01520740c1c0b801400310b450701ca003c0c8040e4070444101880080c001400c0c080d102c00b086001001e10303070010520140e090104100ba0058400c04600070b4102440440c01c03281000c03400110000c1c20041c026031160020100ba180901402030912800140350342180d62940a01c6041ba = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 934747230 1250 934745980 934745989
    0x81302040b040e0c0414160807020a060e010203101a090d0614040f1e1e0f0803070c02090901020a17150312091206100603090204060905010f030c090b011715 69
    0x83d1814002e00051026803440302c104015141d9035404261041144810444440703101a602540482c81d82000e110f2a01c8004040782004090a0090800e030b0804c03848100ba540154000e41c4240c02c00340101c402292155440100102e00052521201006000e00f800d54604002c2917490b45202e0b4000042d46880762030b0f41107262a04540589032411400032410910101820800c2080c450071111604c0b42d071140c0e1089002c4e2008071485803910b0101c00e5a8003000b0418031030a91a940050300e00d030b100e2a19032802000340c40e03c014202c0c010030540001c0f540c01641402620400b003615114a070951040c030740c007045d0840c1d00030480c0c00d41c070b115603003810341588007030110745407002c05501040c2c0d07034180350740c00c0c4855006c801c400340032564400342c00c0103001c0c0d448801c0c680990344103280214000903d070000034090140c0740c00641005140900004100000d0680002100d10480e159050b143d80c03011040100c4503034840795070100346401604a0b0b12480c1c082d1441d4042040001001442c40800204 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 934748480 1250 934747230 934747241
    0x3020c0f0d0f05010b01110a151d010f05010f050a030803011a0403060906021819032a09020a0908030a121d1c020f010b0109030f060e12041503020a081302040b04 71
    0x142d4180e552500800c15959116405010226204004084480c03807031741da0090074040649c40028031956049082040e400340003041030118440e42c000d0100030506401e0780010142842400d84241c5000e100181a00b80303440c181040780d82040f0101e04503841d10502c49001042210901c2d515101040040300140080c031602e0101c60123500010384400400b502244078850314150244035242c1c43d003031320840d1116000781a003501c2d0b12803013401c085502103519036040038a4889450203810740100206201032503a01a100d610800d944215074070b03aa0303500709a12842542c644200144c44000e140c400d0a01580021906924000d0061420001c07030b40c100b424084900c0c503c0b840f000702100314060a0350304102c09034841c078460b030080020810440011b4840880d512004021585803c80c0d13900f8010140d110340c3d1754200341426540d81020855200056503c1070081d038031002c0309103401c1c00045200f8425240e2080d01c0391510010342c0c9071450301c20103040004404a03403154640c0d1440c0c8803a00c0c0c50291 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 934749730 1250 934748480 934748483
    0x31506170a020301050f101b0b0411060c070902160c061205060a0807090906060509102c0a0f0e100605180402030a0b070219200d03020c0f0d0f 63
    0x180c800504a032032940d200480003821644000d0300503c010f021586d01c00c0301c09426207004403040e560fa10106c00058076601150122089060754894503041031001b5080030342d114500c18000c0c0441104074108200c42030082c1c40c40304400b980842d80501caa9403256006101075034041e03401400c6180c99945501c0204102c2d0030240c0040c2c3d4074026030000c80094054203400a4084802030348441c10322215951ba02040e119852202d070700d401141b41401890b030301481c090304c005400e41c800b034504a0b2a2090030f030814404d8200c012107140303040e030b0a0b54030b00c0008001621340310703502030b0a0f407110402c042c0509528540740418640d10940341c00c804900b0410049010031001000c07070828580070412841c0201051810a09400b25041100590f0045075051100f40d10071490205526030100c103d24001040d100324440490b40031601d814041e6501d80444400e6005071405034081c0c82101780403181c5d44c0c809004001d0f03400000910b4031071800001c00c0301848800703004041e810180b615803070090581ea980 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 934750980 1250 934749730 934749737
    0x40327090f022205031b0a0902030709210203071202010234060503060303070602210103030e040c0c020a060f020c09011205060108060c0f0702130509070510090f15031506 75
    0xf82030b2500d0b4905100c8141c65220045103400075840d100109403a1100c9180c05142105907400c1d80210380d03181900c6401903c41910215120718040348040d100756950b00602d410002c29440802038034102c10752000100f46c0c00b40c05008a0f0f4136000200c40015080ea000b241507010300f0f1300100001208480d80301c150b00c0c0d042000208500c0401c03e0040d0940075801400401408100700403168400004440c4d5141c2d011500580d0b5424070044140e035080512181c5030004128000002890b80c81900100840c0d0700312401c012664002a056500540e0110000e4014401107000c0000c3d42c01a00c0d0008401024010303900c8058102d000a0b10117a0f00341c128044821500880340c080c064108403890151410b100100940d040400c02840a40035600c401101c84400103010b40440d11040e82c488200c0301e0700309050246040c140349083d141c040c0360040750f02a01c550065407400c11301c1807680e03c04441c4170f000240025403d1403441160342003006034100070305444030141000041d0700f00350600108100d68 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 934752230 1250 934750980 934750987
    0xf1f06260a0b120339030f0301051801061b060216080304050709050c04150903020d0b090f07061b0515100305010e1b01030f14150109050405040327090f02 68
    0xc0403c146110f00c5941119180e2042c0400c0d165a05071110710005120410713800c0e03218501603c141103405070083d010310654000170480700c088802c8040a0350580d1822650260300301c038180454003280c1401d1040d580010520411a01d0090190361980c0d50a4090f40c00580742a0700306080c24811040741000316410310b4004200801c1c0042440230348050b04d0307040b00901460806042d00c00c4d441c0554001e080200c4a000d0a103071120380100d40001c02580d000e01000c1d41c62905040c00d01c0d122500f00c60ba68442d020300b040c0d0341d41840e000728018059035070f2602c07030a04051205a0701d00e81005055012507461180d810088001c04c140d2840a1017801080b40c40d810366801c6207849800e42ea9180b5500d2000d42c4600907580e01d403501d010601107541401c0c6000103241c0903040744a4090078000c181140d0414091041c00608074600160f41003440f400c0e21620180c60750b60062208451b0101e801078000f0308031030a0b0160602200a891441c0d0305d05410b401440d98984202e1401c0326aa10030000b1000d5000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 934753480 1250 934752230 934752251
    0x7141603110c0d1b0801060e1f03031d0d02040f090212010506100c051509010f0605060f0d05131b03020a080d021b01091208030f1f06260a 61
    0xc0c1d0025101c0c1c41020b4030a040142002c10300c1c208154200401070540790980c43c04041051006000801064000f8003d9990700c5141c00340400e401d5508d0456010072550500305001810500b10441b541039542800c21800012540130650042e19440c1d400b65905880d000035039a00d0140c22800b4091000c0000c15094520400581741c071100000081d070390510040100036550301303d02d2030ba060080d040075022103607030380b5050307042003250302460510346c00080601015660550010441400b2034504010a641382d0040101c80c0c040c194030b940d5081d5041054055202040d084030350800000d4100040d400000e5450036001295000d0f1400107907420702c41042940f40c010301303440040030010060100708014110084d00e8010300034800c10b000c20070b1800c1c58156403280070070354002c00a05483d84200c0800d80303404801d9510982e002c024000c0d025021480c80d41712940b0b07003010289045c5080040034581001a110b0f0101c8001c403604108a815505e140102d9030460b0b240320316400580090070b010706 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 934754730 1250 934753480 934753487
    0xc0109050d0908160312030b04050f06150c031c1503031205070305010b030f07110d03021206030c0321070204060e1902212e0f0602010c0507080307141603 68
    0x2181e00120f1180c1c412001c205200402280880943c5d8000b0401c016040400d00160b0150203a40d494981091800080207013940c842064203019202c220303031032102203c251643c203405000e01680c00b44650010040d1801c0113003200f182c1d0503048004000070440c4440d14100320700a003220307071041e00800d0071414800c60440c103600c181d9038030240c1405c040200d54100a6500b1050000403e400300e03403150a00490002c2c2c1c001c9003280c02400b0040101c8107480f1407854001d02a4104075092420710400c0e4001c02c25038900411401318495000c0d004003440160241140102104680c1c040104842040803002507101d50180c08043e1031001c41d0b1003410b01704490540071108450320102141ea00c1401b0070310700c501d104120101c04850942c190005900c400c0c1321001984800c5014002200d5034a00d40c0030308103c80d245010884400440d0b104549546081c140e080e03811412440c400540200071560000e0880409160402054581f482190f1500c04c111405540038000001e00d10b00321107a48400c1561 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 934755980 1250 934754730 934754747
    0xd05041419050609031005011d090c031f1404081b07031106090a0b0c0d200d110c04060326160204020705190f1e17030603030c0109050d 60
    0x60695640c4030716008030300031106040e038034042c40344642400150b041e0075503070401c0850080d0710000020080c7d943d503128170f044661a01e1a41540c4250040700160704214007195005030035102501410703182e0304808a0345080b08105442180507a60b5820f44100c94509922451186110381007032959038802e80c05c41100001c1036402c43c081548036540c1440060094540e0f907002c41c07801d5500b00c0d19900e4510000303002c1106034020700010403011941f22030b04d5400180030f0b0f0030800da944910001d41d0350722080b03441c03030700c20841c1c0101c00382d210840c40c103a180d114506101054038140c0c151031504a403880090145c0c0c841d50320a49001042ca01c042d0700e45002c803242c4071521440d02c501a031400b11a461800004240340707a01134170441e4081030384810711038140030091188165860035020045940b034200f01210726028207480145482d030403000d000c072aa0207104061070b0400500390141640c45074a692a0f41300620b481d4041c002442602c0e841c160900495500314804e001502d40501600030042c200070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 934757230 1250 934755980 934756019
    0x5251a040f0b03061e01020304030501140a110f070221150f01090207030c020f0307120c06030c0e3d030b0f010e1e0f0628030e07060c02030f0d0504 65
    0x820014070205580300f45c018000788201c85110081c5501c0140180d0071401642d0000e0465420400da91194103c51107401d0320a40304650200500740c44c10710310701c0c0310b0b008011007a0240720007013100c1005883c0c5403508025103413070a156001c1901e51800098101051148404204400803013031010700701501070b00301d01603c3d102e14214180a082d49008041a040780d6003c1c2c007a0703002e0101c2000c1c80c1c0b018090780e0b0240c4005460a031301d24045c2d01d4140028111480b80000091420102c0fa20541c40784020290b18100103100354440802041e200d0700300c190002004d4030310401d5031002d42c88075000c1401c1c01590ba806403000600f00b440d10b400e002d124103400350340c40d04025006800154503030300c9460342d8070303030301c2d4032202c80420340410f0340120311440505002c45900c1710021900640050b00d2140380e100072810304c0c0c0d460050046082055064072802c03920000d01e40c1101d1014820188690401c810b1680024100d42e1106001e0f22503505201044905034009000040c0600c06888030096221449 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 934758480 1250 934757230 934757249
    0x3180c10050306090702190312060806100303080a0917090109030501050c040e011415030a18080a261909020402070b091e150c0c010e071a0705251a040f 67
    0x40030a00d008030244000307c0c401020320004603010290032070319502c0075020340240000c55180d4144134428000ca04003512080b40014141340003e10041c09034050654500d038482c005540808030340011041c1c0ba000f00c045181007007500c50001000c203209008550088114280141c0c0d20707401d01c107101204000503004242007000e5054901d216854044001443d0006828030507202d0f26a2443d0348040c0c10301c40c803025909043e142201c130a0204200003000e005180381c488105200101c0c00100c482c4c100b5010301e26044240100003400c904054403070110a4071004400074030002c10358002000c076004458103641c1d207080c2004100300d1180400ca130304d0b9000031303a6054400b0003d0701040d10fa0303500003a0100d850354031290070115100701200400c1e240e0100f428002440094001005203540e0041d03841624806441c0c1001085407051040c219004190070401500300078921802d16140c40b08640700d02140c3ea10389001c0064541789071030181c0324110030350301ca4642d600c2c42d14100c403100c4100340c2c102981c2d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 934759730 1250 934758480 934758493
    0x7080a02030a020607290106080108011e110409140411031614010e120f10140c031015030212071b0201110f010c0201020c0d020c01020303180c10050306090702 70
    0x250780d0008030484843d50441c2c07516983c044c1c2d440e0150540340e1074500d4007507a848039580700100050300c5204c0f90580d6820344d070341074035030713907034050b058203a50042e8003824a21465008814180c1c0c000d401803004045c0740900030b846c0c25901c443d8002100d8002c1d002d8a07100c012541400100110030100d4005003004070300401003024210107245000c2c1c02480b17141d040712442c00d51186582d0181d044580c031100c0c000c00314440c06021f171801035180e4207c4003506100f402110800d20080050740318000300c900910a5071545940ca4001c1d02c503c0340c2c406000e5001c00180450001216194802c94840a0a0039a070150b150500100800c2c02e0b81d2025043c103081c000c110144402000d0000050460b158091810302482c5403112072480c20688100c1000700c455007880c10904005070150000c01c08141c1c2a421134560fa11210000c80c0c03645940070645006800030400701d030300722400d11940b10303d02d212001600c15205001307001500e402c0065100c080481c0001c01046103900d445400c0942c0709810f4000f5000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 934760980 1250 934759730 934759733
    0x7030908160e0a0e1c0804030e061e0306061303080d05011406092e020106080f011515110109061e0605060a1103090306010305070f090b10030e032a07080a 68
    0x950b00060112200c540c4d1550000c0c4110820012130b41416980068420651381014000b0440c0740200c4041d030105640540740f41d440c0c14038000b104d44400018001085d904420200780e03409170710140c00d440d40190148001806035102a44480041d071050000d9640c540c00d52003d1015642c0503804100c92049818a2140a8488000f00c2d0260307401141c007155080088107007200b0300010030b107860400c508100b04c880302e059015403104003a1800c1c50102e5501030348407000380f400d89828000d40b034080ca03c0c140c420001d00240ca02d0140420440f400c2460483c2095440a402c44420b000c2c1030303031040d40f18481d504003800c0b050300c3e16082180e803060900c042420400443d160f8450201c46208111151800c0c490070780d41481519034030007004065074110351303490038001d03a1416107024102c4020112070b0001118421403040c1400c6000141c06041141d017181c0080d0014a10b08214078028001000040ca440b1000c20f450210261017000c00c030709100540e880d203890044290041003041c0e1080d4030070f00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 934762230 1250 934760980 934760999
    0x61a0c030706050a02070605090c03100b030a060b030a120207060801120c1802090a0b0306041104030f020f010c140f0f0c030304120c030b04140d0801031a15060703090816 75
    0x64000d5084200411141c03902403034003001b4030030068060807a91400b4140504c554001c51042e0038804214201c6050041d907001a50403070340006455279256100009510015508d9003152081200c02015034030b400080303859280010321660306110050704188400c3c090300390000d504901604d03c04032082c5007014280e542101c450918002c444280790440300100d1021808d0b0102c480411018100f010010ba482d184410913030030035281c092107a0b0601e524550440c031000161022640c0000d0342409201d031a03000c0c000c006911000039030400c090b0100320404122541d1003000100c96103001000040800780d412418070301c0c0b0105074001c0e50448512854256800420381c1c042e9050000000d0341002d0a02c0c1c65902c224803039200508503000c07030003044107220b069550352108140c10700c03e40c0c0c88200365440850700440300b4000200101c0080800c003030590341c512a0300d640502d404601d910b55100030070000743c8641103001e0272000241101c1080c41314600038080300403508100c144588006040c5010300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 934763480 1250 934762230 934762237
    0x41e0503030a11030c0a0b0405071413020a1b14070b1317070503060705030f090c0117040609021f110102090108070c0f0606090501090e0601080d052b061a0c03 70
    0x400c10030f100018001d41c031024011903c54040340030840c0d41c02540d0307180200070310030216000e40d03682c0224000042c107d000038070f520101700d400070410340719158100392040082d00300d40481c4c020401d000858000f40c0581c03038000080079003e003614049003400180743c54a03003159504603182c914000e100704503070380c1c4c044003824040e200c01038241004045506001c42c80c10780207902641e8540700d20340c01e100031a90040000d40c041d09d50741641500c0707962945007840e540c444940d090350006501c0c141c0800030962031a07020f49c10070f12034440440d00d14101e40002d001004000e48a40c0c44514000981811b41d422a05080a07018000000d40c20419807100203000d83c100102800b0a0113a04001c0c2010083d040c41c00c8049194880700801400384c4806070000200360900540114520f4844001190307030000501c14101c9640400505800a44000840303540d00010640304401281d44640d04415028071000d08207034840e40400940a850b1090211244680221410f405807003007085c40e42c0d4102c08000c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 934764730 1250 934763480 934763497
    0x3303011803082a0a0e030d14030a0c0c140d11060417071412040f060e0a0611032a1c0507020103150b1c0b010e1e0402160503041e050303 60
    0x40342064901c2e040c0001c0f1840d481c0c6200701580200140c0d0f144240c0c3c0001481095000550403118000c3d00f522041e901d65120310b401e28035140c0c0a00009007907580075009407841d65801c4c90031909003459076882568050484000c160329802c020452400c05a2040803091803020400042110b41455200d110034407100505103015480001001d209000028140d1002140700750101d0b403140502400c4d44190740c025008110090952034030002d00903105150034050510700405514075030313140500c269101808465600d100303002c280061010381e400c46114005600415030b030401c1d2084001c50703460400364094000d1514040044003101c500d0703400780070f07513445a44c203003000980c50b000d1103000380f10400c00f50312500b003a100003da48294070034110003215103000840000d0080c2481007005480140484c0390054010041c3c40e8100300300c02d40b407907680701c610b04040c1c80140b50840c002460031040383c5844081e52207900000e010460a00f1800d203c4000c0c120180600d0500e03400d04000a4403481084103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 934765980 1250 934764730 934764751
    0x140103200c031303060b01020606091509041509050a11061606050a06170a0201020d111f24080d0e0603070804050115080123010815330301180308 64
    0x81c0401800320030000c540001403d0580e4118055481c50400c3c05402454400c500500504012440c0c0d418150131041c061071501000e03c04003448501440003403a8000c0c0165807050300d880c0c0c0c682541c81540b044000c00340c06a0003a290002450409041c00303030302c08440900410040011001d5802d0354800001142d074002004980c0343c8424410101500705a00301e40c1f8140c2140d44c0b90340500000144615109200f81c0a48003403103407890f0b00b528040e81020f0008060341040002503c1f400c50751404c0120228800800035081c03003102905e0807156090100c8081560804800303025002003000741000024044c038003c007000c90504041079007400b020b00442c0c240030407030000c01c08115080d044096105c40d6910043c860b203582d400034a010f48094680c102240038001c1c22500d80c81c880100c6e05050307030030380401040f00d105071602103400c01c04003d1001841e907013800c1e2590b500801901100842c5c038000f0001c40c0702421520101421078154032001c0700c1d9880c44200b501d00090700404010341c0706030304d00f1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 934767230 1250 934765980 934765987
    0xa020a061808060c07050d02010510150507080c0106030507092313060528150303200a06021201060e090109050a0b2821080f0403120914010320 63
    0x91011071008580211a150050310100000c4654490103056898004c00856803900c04008040c2c0c01c82c0c506440888401c0380c8403005001c1024030742d00c03044c9030380510700d0401d00e802c03910b489100315a0403e00010b04143d44542080061140030405a000b600d000380040003d613a00c0c24174900c00090750a42085008120000a140720361480802d101140d0000014400c07407500c408400000c8032030b03400760301009011140e880c1c42c4140d54402c501000b034072904200506421070f2070545500303030f0864002c0046074140f00001c200b81e4080c4090040184120805a1514600c6842260544c0144c0048007086002c00a025455441031420f50459507903000000752519101801800340400c0c0340300b550094555402c290003240e1404c503031800c141031342d80ba4192541d1610315a400c0351310741d141d40301c0a01c500c003481d500108403989e0041002c00c5040001614103a56540c8150700707003070801c051a0120740000c0007040f00d40c41c0114600e04041007440c2c2000030201c0c00c1002c5040349012801c1040000021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 934768480 1250 934767230 934767257
    0x906060f010e13050a0f090c03020607020f150408100c050a03110d02040b040815010501120b0a0f0803032703180f061b011413060b0321040f05030a020a06 68
    0x800d02e210381014007510004203915440e5068026043c10359919040e1840c0c0102c8190800b1280b240e40300b220b500106002d91946160208880c40e0400d40082c3c3c0d10140c0f00e083e1840c05d51726194000030446480702c20f180c44504c0c04550600b01004012003080207801c003c500c4202c10b0f880f001b2104411000d007030001d901260360f105003205019010f450800e240c4000f401040009520000d0411541802c086402514024902c1840f0342c501780714613030108003168840307409610141c11405001d607000d0626a001a610320600d20000074907401050640c1000040c0700c4540c580705a9010780c1d5a800d10080311440d21421456580d2042900c0b03a901040406804071065603403211800509900a01442d10340100150640c048000c1180c4149290b1034a100c10700c1c0800d0036411140314041d031141880e040718507078030340b5000303005a00d80650303140c0144030f8000400c00b960070803002c0001c1901c0c0302a8556007490149501c0108640080c1c0c800d030301c0504000c0060740d442c003001c0d041e103440c0e180407107850205 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 934769730 1250 934768480 934768487
    0x31b0e010f141605010f090302280609120e0306010e0606180603090715020a03051803010e0d0e2403040305301909050a140f160e0108060906060f01 65
    0x486001e40c0c44030b00001103004030100b01c0030300480602e00480c020000b4600314102c901c12180b0861008015030400c00355620480000a10a070380c2040d1311410046c241140e40e10702c1c0480b404c00808440c44424000d8801c081a4001005008088103900400055042944a24a140e0010b00c0d540c461000041d519503c0950a0141c4900110250070f10752a400e10140c0341e5114962030146034054001003200300c041900c00240d00034095010307180c0701d00d080b10071080304918510804460750550340300d140011983c0d81c1040303050711105803171795503455059048041080750540881d01300c840140f2401000e120b10400c0c81104c2d0001d505050050740c1d8040505402d004a140c5504482c070311000048640e842d00b0300c0b082892040101500750810f00300e507a0254401c0710414440901242d0114210a000400030000c100c0030320440401ca0303c583c01403900540c030b00784880303a0100e00381268040c100704031201010840e02404415010380105d10707003548001d03500c138801001da501c26114650016a580d01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 934770980 1250 934769730 934769747
    0x1090e010b03010e0c12060c030a0902060408060403210c120b0d0b010f09050601050a0e01080703180c140609102303090102030f01063f140403031b0e010f 68
    0x8000e0004c3c4a680c0f40180482e4075040f076185903500902100d2401c44900402003000e0b803140742056141f90464584d00b0264000305040c0200304d800c501e041101041050302004418412840303503540c0c03008a44003d00704044a41074040c91184c140c10510000c0080e90491003400443d40d240e00c000071414851000103240e0703c52540060500d03241e1200129401d0030181801e415290300c1c140500039511514011a00b41c0700e050740d05000961000c1400c0201d41c0304e281e4180d000012450040b660414400c103100646c0d03903000d0105c4c0e0101400d102080306a0701c5030b01040c82518105c0c0c0d054180b0400c04003144101c0b00c070158150400a0002d00c842401a0307035101812a010480001616440d089807958000d600179166100702924950002501c54070604180c0d0300644030b81446c40c0a40010b00d0185400820301502c122510880c51556010074000d1040c00d503e805101906500390420b0704020b4200d03826000403003000555460546501e542100101d01c001c0000c0c6890645407140590481d140764 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 934772230 1250 934770980 934771001
    0x140a0f0204140402090307090903111c081311030303130507090b01050306100512040b250210021c020a02060103021005040b0f09060c07080c1003060305120708120703020307111501090e01 82
    0x901e048140c50a01d1350281316025081c08bc00101ca010780d00441e00741040c01c02d1803070b000f80010b0614000a9500f0304803d0f03201c040c0c51244c0c604610610110340000c6c1150012102c147c6401d41c8541d10105101301007204400a140d8004100181900900020302d03912006082c240034408072144c000d4030a01c590b0450f01d822120025551040c1882e15040a40380010344a1086200041c0444003917142104101144034490781c0003000c2c0340c84d0007446000603405c241b91007092815080c00b045078070f09080c0020200c81300c460f400703001e5039811441005280c180b868074540070014284801d1215110010844004102e56600c440d21110500000340203031003201000c81c1280640b80001405160005d0a10031961080340c07061100151441c0c100e0498106120141255101004403220a0030450080400c68007964140e464040041001c14030400143d9104002980c00400c0290540c1d00443c005540030180c4003070401c1846254802602440c107025854001c0d0340d0b12140c840b142c0c82503001803610b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 934773480 1250 934772230 934772249
    0x3020901111501140402090904120e060c06010911040b090409081b0106030201020d14160f080f031005010c111917030316090501170a0f140a0f0204140402090307 71
    0x2c0e0102c0003036101c0c4010078442c0c0398030000322821580d000d00c1c0078026150006006441c50545680f00d0b11000c0000003d000309109203c0759400c848296101d90009203155001c1000801c01d6500d0490700000300c4a020315a4414000140000c0c01002d44040881da107808d42100d0108980b80681480d149a11890503400100c21056062802e801410341081d030849000340c0a030390407044a000d0607240214283c0b040c4120000070090140b03c42903c01b0a0341d0710301c1c02203594a4070820035641d540c681e6413020286030b50ba84004130800442407119100000601002e19040201007100e980d6000c6120b6050340032403040002c01c2e141441b410030314802000074003600034400c1c41c4520661829859a1003035a03210150840d00c417110386c031140180c040008449041c0e4a100003400300c2d200c100d00250f40035004c1003c3c2c5803600e840b0000222240907014082c544090240b940d424900410001c94011251118400e801840204005130040c01405402842641c01507610396a02c40024103041032a004840d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 934774730 1250 934773480 934773493
    0x3061509020c0f01060b09060702090903160b0f060a031212091b0602060c03060a12031e11060601110d0c0602070b0a0203010f0b07050d0c0204183903030302090111 72
    0x2d280c0000e0700d00072414000380200801d54441205000b24070074018140e4120b142000808010b003003003018198401c0201d030030340c1d08002c1e50b18107207182e072441c40d83c003500d80800321020301c02d400c1500c1c0384954114401301c2d4004699413460b65000807010108404405100003c4001c1c0b10380049d90300103855003a40100d01c1d0b4a88c100d111500d01c001a030b24054100103100314400204400c0e0b41008403802501c0081590708102d1600b08003402401d4040d104400700000c010f01c50140c8082500c1501d007400181d114261150010300c409494040c00500b1b450400c0b410b206560b01c61000411196044042440d0039850340d0b68509068019202e0048001d104d0743c3d08904000c0a145140d029506070340390304102d01c207042d50300c001a450902a5603030181c00c1d50001d8116800d00e900030400c150f055032002e040461007041d0607240138185019402d0a85407800b0104031340660a00700b0314800306c0d00c240700079021490518a0f2601c0500040e40c00001d06150380083d01441c943c0c0074041070941e051440003119403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 934775980 1250 934774730 934774747
    0xc0f071a03062404090b090c0f07030504090f0506040c0206060a0608150a0e06100c0309050f0a0305010e010c141e0307202103040f03081513090b010f0f0306150902 72
    0x7103038010305c10340c5040b600d4240710005170315042c0c041c02d0044035090059414800802c0d50014551300410046007440810400011030b06034500079500c0101c0260760028061800c10180001c1c3c0380070100b20070454200004211955413000c008009940241c034010100e981c841c0603040701200d4481030aa409080c070b0303000044607070702880c0d4a407060400340c1c0c0701100760340c403a031007650344103060013001b004038440700f00c203224234241100c82943d55a8001c00c020201c660342e48800f400c541040f0341a01c0d40c1e94607030701000d90158020f8180c1d0b2980c6154030046140130f4800040c20b0384102d10701003110403158000f000c280260320541040703403000c440120302500401543e41ca15687c006c10400c103c030b08000e90040380c15410040d030560703206a400444015110f180b65800b2200303500014021085805082203e40c010b0311800349100c10800a400c1c0020218014101a002c0040580c414041c01e00c09440502070720b03a4210042084a40c094008100960160180c92600c4016000103200d0352010426a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 934777230 1250 934775980 934776049
    0xb011110050103061401050123130e040215090f0402090d060c0206040b07050f030114030a0c06090e06030601260316030801050103051e07050912030703050c0f071a0306 74
    0x90480c1d210341001c00c061694908031110424092241d12301045000003c0780c40181e904641540b448654603c051800300c102c904040656403942060300303660003c1003000304508200000f140c46a110301005410812080000344100200c1c0304014040d507004250410304e41c6515400c0054154050020b019074803541000030350f80c00d07003107070107890007100440840d0f10a03000301c04131241c1c610294622403850382814154100c8015105146405118144086004c903804030030100151840c2d0751010f4800703103440701401c500740c0c1c0684807070f04c660084801000740c400710413004072140f0b043c5038100e000c0e0f0440008860941c01100700f80d050f20402d0b44404001c251f800380d401c5050b940300345c804100c1610b0381038601040000340d03a14408050034407400f2600041c000c5001d0a0b2003c0001c04c601814440c240301c1d0b5066400500b0200d0100b03901042e2144541400d10007044031010795401452010b103080580c660b1540d8043c59030302041e41c0000032581d181c0342d440440142d01d1844401c520503110f48922a0f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 934778480 1250 934777230 934777241
    0xc090108010b100c080301060f021f06060e1807140c010c0f030f140c03280630030806040b09040f020f0f060702040e07051903050c0f0d060b011110 65
    0x1035200300800035207400584d000b0000b00105542040986056a0800341d055500010078800f150a40c8640c1000c8240c802c041c66804841c41d140543c0441c119140410180a20001506041c410100300407038a07154000b2140d003070b40c490b4040c6000e0012002c0c0c40c0d8007010502c6400b00c1c208071542803240702c80c0361582186c01a2200c88440c0c0c0c0802c4240c207800c200504841e124407004040a94010104298800000c051608031001005030403041e01012107004d2044520030089074100c0d00d6000403c0441450350207018804440620381d00c140940c0070b0b068600b445561401420f020b4003034041081511036a000e010b240f030000c0d0841e1020f06090410041c0d42401140492288008102014850a26070324401802e900a00a613050501d03581c02c0002030280315044400c030f80b0522a0000702d0341c0c1c91442d01c0b03182c0c007c038100f910740d06401c504143d030910703d07014001805113030414050380007a00c60007418901c158004034009180c140750310049030b00f60b15160440c3c80ea07215407001c8907002c42c95540107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 934779730 1250 934778480 934778501
    0xd080601021504080a03110c03180a090615030c1403040803061908030a0e0f0a0314010c0f090b31050a080f060601080901110310170f0d0f020c09010801 67
    0x1c03285014400c1e8142040b9140c11600206026810f1010410b418001e07000080300702c4941185a041c0603030309080a1440c0c218243c801c5244030f081c800706d07a1034100b03007911001070903901d00c0500070799040942204940e1940c1d03031424100740d81d441c1c001d030199100c1c0c4404601100c5a5680310355901b0581001a581d800c1030710440e120760a1501252103400ca4540e18204461040c0c01031401c200800f442907801d01c00d200401c641210400c1c402200d1943c41c6181100950f01c100a80410803031004070136402c4803401c0b103c0c0805d202000c09001c8043d41c2080502d8111401201e4181d030b03c43c1c000125510001d6804a856103090310307056503003942c0d51412a050b041c0c880a5500386641c690b508052680c507101000e00000c56085040441c8503544140d0940358048030b800000f0412401c01c01a0240c5540201c90240746011110014810301409154554800000350018044105800310051b2a00b0001140406008900d40c100d80f0a83c024070001c1442c0c40000c05101d2030391381d180c131001d01a183c0c03d80c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 934780980 1250 934779730 934779733
    0x31305070504090b2401020c010f0e1203071712010b030c070c0b03011a04030f0209091e0c0a050103090308010b0c10061203030c050f2205040c030b040501050f011d120d08060102 78
    0xc0c0b10038600007608503151032005c16402080710820308030055403403800f910040003c200030800050807035140d1002a00c0300c250f600c0700550b0f41d07a40c05d06006800885111181c8001d03041009901140c00040881074150781e45001d01070b54a44070216003510034403030040001c000310201200001c0d03d0004401550481c0c054880d40c42006e06064510a482d100342d0100401004880f8810005070401036161070380040c004007242c400031440c400003864840a100314100c2c5920040410b01303581420000c0b40d00910382030905000d0101c00d07a4010384a02014060f0000e46030f000304040420040c2084010100d990002c8104403150300c54401b01d4100401d98815404241031107100c560740b070300c210700300d03280901c0c02e8031618104069588011200c40c0342780747c098114079030240701090580e901d22135112000841d4400040e20014841440152107050b480301d40b244911040c04140f603608140308a1800b0001208041d01d40703c04000680103100408102115100d0b01005541c030350380000606015034400d80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 934782230 1250 934780980 934781011
    0x507050a030f0f0207080616020102091e010e0d0206030a110d06060503450307061d120f1b070b04080a03021002040f03080304050c090a09060e0a020105031305070504090b 75
    0x1603076038102606c0b402a03258002c00006003203400840305900b040d0076a100141c034209084000035140741024074002061010301045402a60b04091070b013035411819985250100110340008015000c001c215056407500d07458180140010031085601400081400b0441c1e01d465000c010300b43d400886034201e060750501c40d92180624200c6a4144054080d2210420341889090701c01310354604031510b0303180b0300c41400b0110016405000d03540f0486130710402207813903602d950070862802080c05840413070107070100281803800c002c06088454580380c1d003100c2c10a55020007200c40c98541035903c10500d59002045c0860002004030b04001c440b4025404c0f02c004d8603241070b180003244114850b54010269000d01040003070041c5000c4c60f07005025806a40ad51214800401d9541108450a07526143e6071a01c03042000344500c034940320400f2402c020f006503d51640043c0181c40090300d00150b495076058a60300300a41040380e440903281c090000d00c0340d00e8462500300d83c401c2007641c2d052400790010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 934783480 1250 934782230 934782257
    0xe0411030711010f14010b0f0c1b130b010f1b05010c020604150b0f09090319050c070909020d1e06090602070b01080303040309090b040e0a0f0c0f03210507050a030f 72
    0x500407103000d07040d003000c905c4007a40b82466006e6590b00507408015659414401244681c80520284520042662005c0300b0079000c0d204200310310a20a0040b40b40301d2030824241d94590f40320403448000e00f000e0611420000d104180f042c031503010315100130255824104126036437036010a0480c041ea01c501420713a980c2d010030b44490103071861030f0912900400310b410031408038540f10303040d2508405510241c0f0f1070602c1182c2d0480c2d142c0b21002401010400014210500400401040300200419001008542c81f503500103a01c40c91100c4001d40b440e1403c490b4041001c41064592891070343c4188100b10300b92541c0f4200d0060340004906071032446540c400040d900c1d80100440e4465903040e91074084050070803250034000c0a0240c02c00d0341003940c85d82c00040300101008404a402d004085c000d50500c03003841c003260441d00c20b40100e11b04044c19034080000a50b4031408510803030f00d4a02818416501800445036405010006012031103038a20110525400c104464603440507540d600c100300000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 934784730 1250 934783480 934783511
    0x1207051018030e041d011a150a1209020316030605100509010e043903051c0c08030402011809090b0109021801030902060903121206100905010e041103071101 69
    0x1254406404a2032280150b4891301c0d00781d111910f012000145c00b10f5007101c0030310752402c5900386007804454104410440d0b000380b4005403c60300c0d180150800c2c3d4a040000c100c0240508002c2d000259171584841800381195803d100a000300c130316616541c1c2801e03551b800c1146c0602803e07100c01009010ba940c0109060511114003811b0b9140050800055111551101c0c40e850203080703203068102c040c00241038140d0525490004c07402414442e403c0f03144c114105035040c40f207200407451404a050410381c94158000f00401c02907500803101a4680d541d80c001130f105103e000c0c6551513006403000700443c0010f6640e0201000500494000c402e0703a80301e803041c02c201d126902421130098040d0070000351070361181c0c1124008030310123040c07903007854101800b00345400301c04283e5480035000807890b84a4150034001c056486641110842481e110703103000a4404940c41c00780780d0403c0009107082010b42c031550041e8000540c0451029560b140011004040d100b03500c001240650800030030a80c03107002c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 934785980 1250 934784730 934784771
    0xd0b0906010e1c06020f09030114130b040309090f0f0c080c0d021305060d1d0706050a0f0c1a090c0d0c050d05120408010605010906170a020a0212070510 67
    0xe040e11012440c04045003001003110000034000c40000a90300e07048002845400944040c441d200e620984414a0604041c03d61306242c00003e00503190300100501404200002c50406401c4100500142c171740d414222000b1080307800c1245050b0a01c0c01c8200e4100180d8807840031003150715800c01042506000840d8a101c081d280c811928406012911030000c15034003c01032072081d40c0b03086002698030300100e03c0e150070181d00f40d00901c4c0d80e6034251b580001441e020800801070403000c0c116a40c201913014025002d403011000412002e1800701002d64011003440502c150025115484520070316016554840100e03001d180c2401140300c100c405082001400c0c0025a010b4011034145003004180495004000f5003076855103d0301109a40602a0400030806410400000300703542d800e1400242c0300b841b15a001c2c2c41040f000102d858141c4802850458100c20b00703080c00f580e030341100e910481c54803034001c0043e142e070140020b00c0c10030820001181c10001040d070341c4c10f000b42e60041d00411040303075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 934787230 1250 934785980 934785991
    0x80708070303320c071d0a050603030406080c09012601030318030f0206070609140a0506181009020121020405040515011b1e06020717030112110a1a0d0b09 68
    0x4014101e80950350f41c0d00041c1c1150004d480031107501541d107031214046280e15007503200090300e49200340004854076005072927010304d00750001c5160030f18000c8001e01400c0010100680850041035002c0144c0c4209030180e1030703608501c0c03a00a4041080b482ca105010f081c0310440120309101d0ba44401c1d40760015071a03080f80d405c1080c0c0b41c1100b20310340a000a41e44404411100d09942c2d05868000910483d403d441c018070507001044100824684a49080341c0984480d4004107001000e01800d4400540c4c0d1400103601000807a01160300d100584031b19400f41d50b070014030540d103810418035003040da001d0304c102e40c0c0403a030a1005407180c1d02123803000c0e5155409540000e03500e110008145072031212590350240719107d001c0182032610310018036007240d542c0496082c3c0d000160340040c800c03903601170280d03004c240740078510f95490701d602004210325001000b0003900d00c001417141c42d680c0f013040e5030001b401c6442001000c204a10042004ca0380040d107558401c034a4031342c0304000c5080c580d81c071903c0355 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 934788480 1250 934787230 934787297
    0x91109030c122d1c0306060c021f090801020f0706050610050a05030903090d1103060f1501030f020c0303041b08160501080a0f0f0204050a0801020705070b03040804080708070303 78
    0x41c0070326180c6181d02c0c0c1d078210820300360940140c011100303010400c008480c1d00ca03880100032000f034a801303008050306d1140d8011720401c41141b0160016a40b06900c6504079048285498200c01c40c0901c107031051410395200812552020400c420060700c91030041c8151032003644200819690720013086001164005614000394040c01042c4110340110020341e0070000c1541220f06001003207000444119030080700301e0f02e800c0c1c0115600c1281c14100980750300f00218103410a860f2030b0440b0424000e5000300c00b000d04258442d0505c071070040c205c1e0304951080101c1000d907590391400d4100000f8040d81400c840c0405c03d07040c200020788201c041441303e501001030b107411030401e107090700445015402070300d541c071040c0c4e8403034840b010301d0498841d6440c160a201005a102c4e4600f03410040000c0042d4131006140c1d00410140c1d000410100e16002500c01c0032450684035205c0c1e0a00c2411401560403101142c4164900851021000560502140d100384e8031a6409004806035201001041080ca1090b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 934789730 1250 934788480 934788493
    0x150914100e151b040906030c14011403070e0d111005030c0717040b0c1e0a0b0105040f02040b0301090516030c08070e041b03150b0705070b03060a091109030c12 70
    0x341c00c81d05100030b8000c03640600d040310a040070404402144d009901005030030799034a40c10420040700c00c41e000000e03d401610400c445190710700180c010858941d5804408400200003010180910f1410340c1c0d490b4042e00c0707000c80c80b4072841c2140c041003910b0141c610418001046000080c8a0300c22a8800c2414414031410180c003655100f004282c2c410080d019040c1c2840301045c42c5004801404d603101d04a001841c6e0300b00f04805c8284054031484990b605508441c03d1403000c11a10350344141140d009480000d080196809008028021600491400c440000c0005191401500218020301c4c496611400c120000031040e01241c0700e800061010900110000d1440e034083c00020000c2000030304046132400442d02c0009000519260b4400400da45500100001c48000c00c92000f034002d9501780ca281c0031440e10341598030043d5210b50424900000000344007a1149250b14006089810050050206c1501d0f40f022540210600500074802e6004660407450514442e034100a10a03001e00745 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 934790980 1250 934789730 934789753
    0x301061a1b03070204050903030f070e060a08090a020a120c09180204050612011811040905030f0a0512040b0f060f09130305070506090f061501050a0c150914100e 71
    0x81c5039030480d06106a5020501464025844900405e4400c6082c3d20240d5582e281040651030a85000380010007000215030260b00c254403000100c4000e078107181081c45981d561010880e241c00782090000b5000301d200040021000b1400809404051040320041d00540d1181e9130f0313604685034407850140c2003810317200105c05820964032854022030042c20300c2c4000301c5008400ba007500e100c16004450740f41c10141c44418080c2c0c510f108034100c04129014411039400b922529501d01542c10715540340400007032480d100e18041d00171a05130303c5900840e8801343c0343c00d00b0702010920085401c6a000640040010744615214804886151009080280c162206004005005403c250840c18040108500320101e401003201030b02c00e400c0c040003801e03402c014100c15404c1c034134003a00161440780d840030424400da13000010365840c41c88900d003004107060030742455074148865207140c0c9015868200708606012503590038101080003102240e65450508640404139140780450060a420441d090340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 934792230 1250 934790980 934791007
    0x6030a02011101141f0e090604062301080d0e0409021014040504020706020301080f06070f0509013e0705031e0f030d05041b060f080a180f020301061a 66
    0x54440c204000901c0064001324040c514609540016002241c5000d601052400f554494050904910b900c0030318207110000c0c0d0b5903500e0241c0001c06480d01d8140d0b02c41e5a145040e031481c802500201b0a0650396034a02c1d100791500701c420610000200b44003501151802e00d4011003242c0303503014050314000c43d8034080840c3d01c2041d01d401c940200a0400002a1650f1607002400005001b6503005030340703514001c10980351412107920303103100740c000c5c004110010740c1240d030204142c8040d061a0303981d14400700040741c0346000c44a500c1441032500c6203403440b0300704106803240803c205040c004118840c0d0039044e0f6590b900762042c542d0580c05043c03800c0c4101c0304001d8110180441d071b800c813280541080d03c0c2c541075400501744170440940d5682000188031070200030444044101e050603903082d0520340024000401e20005005116800c0045038541030103510951400b00c0c400c1205040241034541800c1c0c000000005a01c81d42c280740e408166000030945001d00000001c502c90320342008030701003c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 934793480 1250 934792230 934792247
    0x90d110a050301060801051906050d0f020607020414040c0b0301180e01091707060b06210601021513020a0f3803101d0402030c0409050a020d0309060f030506030a0201 73
    0x454000299150000700350b2001d00410b800780c980b403000407900f40381c58020071040d14008041d003038215040402c10002c9850381c215042545800003420344048003d400407440350702c00c3d0709000b500540b405020450100006c09e03040d024a00c5080d01d40401ea0340d407048007035140401c0c0940412440114a0700f50451100da00981402000788004100007100d610341a4644041c0110b40c8901400050300e50b01700141d0b845880e50105040340e84a040030281d06601c4035000d00100c200c00e41c0543c01010980680c02000b41c007403403402015928003035103400f06036a0101d40041c14100c0c0100100800441c0c00c100340030702c1c041038031440c07426071403c024106d50010303130700e2000d1140c0e00d0018078428540c2e2040002a000f1132186881c0c0150304c0c8a149810003250f41c81c421200c0d01f200059070701c0d050000507a0b000ca40115180402c850204d800c001c1c03410140c0c207240303103807100035800444ca4007080c00300f540100e0007000b02e8050762101441c04d49030540a4080c1c603030803180e03568503800200540380190700a2005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 934794730 1250 934793480 934793513
    0x140316061d1e09132f090403020d140306030606010810030b01061806020102090306040b0604150e0906010e09060601030c092c06040212060d030309020330090d 70
    0x245416030301c01a0200d5080d5070038103403400c62010002016965410282d01d07041d042581220600507070fa03803a840d04460902c40400300103942c40e420705880c0301d45403030070070411005000403c1d15200d41003503d80659a50080030468010504030b405581d1314403820819240326a0000c2c0c05403126a45000044a02c60401803119050395680e01000c404240212a210b000c4d0060340c980201e85c20659407020f10703040140d0f1200085a00400481c0c81688000c2050b68000e944036902101d584c5400b40003c0140c410321320f1400010404030f00c000303a1010b41c3c15185004010070010b890a03a600c582001a03a0300d01120a41215440000424180e51181d4424080d1080341d103000c060079601c1d441c08403004c4407440000c50354000c4c40b40e00f106004c1c0802800e0351300403004450440c0303028070b10340403241e0260300101718502c2805000720601c1454040c0d08400480780d401000e8030000c42414203034a084107000071f0612a10b00c145011054162000300071290b810100a1181004165903546d041f01d20454468 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 934795980 1250 934794730 934794767
    0x507210c0c120305040312020705030d150512100f0507140a03021b0c040f0b031905030903030301030c0305010b03030723070807080d02060c032701140a0614031606 72
    0x14001159a0204030604080b45640118603811310b401c1c01441541d01d04080e80105204110030b6000540c0082114400007414402181c0c1101000c0e090807100041c0d8080c581021038545041007040000c908580c40d00c0588508004d00d1440d03090074030403101c0c11241180802c1c924608102e00030320703020160026040710310f405850283c02c2201c202c00c083e18411156080e138088103419116141c6405014100021003004001c446451400607603640c0c40b0b00c0c0b02d548080d43c1c0080384020301000780300715410408090704aa80c0ca503034a00e000030b0903099500c003d903500d52800c2160240d506d000f0085130340c1c04e504074035605025806810b04068820700c11404020620a8800014000f0301c2400240e0003040140040c04261820500c06410301d00014400591980100204042401c4180c110606000307141002c24880c1c0d0f90a0b4003500400442d900300e01c601020713604025407010b69802000984044480041407002c3c440c081c50f580e1900144a1081c420f00c0d1401400198403484207000444c58028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 934797230 1250 934795980 934795997
    0x1202090604060302031611060c0c10180c0605032404090f0302100b040b100c080f0f070c050103050712051b21100f0311150d0501090507210c 62
    0x40012415442684888003180e004070402c440405070f20314000346c00300c040c1001c400c00d150300700034691142001080541c1a51022034240488002040520b41d420501d110421003d05004031000505a0f100d1049a00307145012011401c20300c641d041c1da00403200009000b042070f440e09008800b807110b0512880d0802c0d035a0b18010017103074449040b0b9141901980103080d111071646c501c5016214041500c0b030080d41483d401840f142c6503914005419003071403420013200201031078419014407600081c0c6401000200c0e0882081d4080002000301d107209140128803990ba031401034040e42c0701201c0b4900481e01003503850a48011580059a20001d01c0c030094484818000e802c0005170002c08010011090510310b003280030030340c000b80719040340005030b4004180f440c041c0b840541844c40e010081259201c1207540030b40e912070343c3c407410070380c4a05150300b5140d00c1c842d10a80000d00d024411424503604103404104c103140110041343d4820101e00001c5607280c0005c9680002d0848920080100060700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 934798480 1250 934797230 934797247
    0x10b09010b13120f0827030102040b0f0703050415020c0108100b2a072303010b03060703021e0705150a0606050a08420118030b180601090608011d0d1202 67
    0x840041c0703441c440616981c601c0b111040c1c46c22410b000701510080c040c2e07104000c00c1c403010310f903007094401045a40709800d0703030780665140840f0140500d40c0084039643d0a00c0e00b0513070254010854001c80f02c0207076140e04241d0f03210502c0e001c10007858401c154120a0800c500048030380c070358018400300506c018100307240d00c416084051034500707550f0003000c0614005d84c40801c0c01034209051405000300f10000d020480c0c002e00001c0c1c0300c05000d0003802c00c2c9a800202d081d80c0c0d848100741503c125041300361540e20782040c1d040541e142c034045100752500c0f006260002b908451a4880d00c002d84410f03940f61824003c8040d015940000050306084e10886c01008500762011246110b50b2100c54000010324604080340314100e02910340d0b02d0640c184455a8411b1041c07800d6004002c00300d81c2c00006a40c61501da1540960041c802181c054a66010704000403c080d03005811000172504950020425070315854200000d084413070100c99040d80000c54154400761240d45a1001440c01400051501740308 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 934799730 1250 934798480 934798493
    0x120111030c070303200a1d03030a030509010509120d1d010e010b0a0f240c02030f06220210051308010603030e0f0d051509031308010b09010b13120f 65
    0x100d03440031849600041207020598075008400c62108030310028604003801d03411750b0080703004d0110590300300004107000e111505c0d90030919410390300c0041c09807a5a191000700040150104036203011181d0b00f0580402c500c0240002c90b0702030584a002d00b142401d40e00b0004201810410107141644100c41950f40c0d001c420038422603410b0700b80d0300000a048950907060110448495125460680e4a00001c00c044900095410022000241052190550340301d05850169000704044c0d007600c1a0f0011a4840000140d00c82c0071b418280c1c0d0a455100300704040c149610244031000790008224500b5211180c0618090200103400320840341803582c403044c2441c2100d0090f0700940000359021440a1a420002c480204a89003690301250511040e1103084c1e58600310351a51405072088000200050300038006c4d00c0102e00402c082240341940c0e21082c60203081d403481171501c608141c2c1c0c000200c0040d244102c0e8802c1004041c0100524a0140c0d40c01910404500580d4501080c861480000e40c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 934800980 1250 934799730 934799737
    0x3020306090a020a0e070905040f0f0203041a0a11090d0201111c0914011e120f0203010f080f250b03040b07020d0207050105120402060717070312090c0302120111 71
    0x469100500c41c00e80c00c0e0042013050f05030b60340400d0701c10b0092070034400035030b51100400003a582c00340c1c1e01043c01c240e03440d41c140041483d86610b00000d0700c04002c1c80100460903030f1082007903400c00a0740b0740388d4903010900000c440ea9004850741180041001150605180701600401c0d40141025110003d528501c0342c2031900b42505040da0010b0100c004160300d8100c08103801400312024000f0611514000107486009041c10301428100365049038000d40d032055940510110320b01c2401c0c4100c200303c001420180d04280240e4a003d0303809080840c01c02400111801c42180c840c1c020a02c2580b0480c51018416080c0701800081901240128101c891013008600544c8120007090441c030380620028207200151402da800c64100030010001e582e07002c01511615450f10200100c940c0355840041e0040c800c0c104010000907090a030b074600d80e8502005800018003075124560040075800200040b1007030100010446110f0400900c05814400d85c0c1d003141030401c3d400000d100304400c004a02540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 934802230 1250 934800980 934800991
    0xe061218030403030f090e01120204020c0c0301020f0a0305090109030c02100c020d032a03051806040f0305010506180c2b1b0e0d0503030f07020a08040801150e060d061503020306 78
    0x20075216000e61040c1e8043c1b0150014039000c890700d0180e50414181d201e2031030840d42c01a20503034000c610801156424000c0d2030300090018021507695111180050180e0401a00040800c0c07034000001d02c804010300441003503550613510f81401c1390b034980c200900c81c40801c8c40b4004000d4004415030040c1c0300d41842c2d150b01d034081d46414152450304407241c1c40c03501581c1104c49150742500f4561000a41010549294038800300211184507003510105d8050f01a50b4401585446600800014004190f200e20f020b41001c3d01d17084105202d50580006400b010360700c020380c0b03480800c400351010001c50300b8000d800c41c80c1c1c03c21911000348040c0c10303010341e00e03c0300c510680498042102c42d072050700000381c0744002c102650410100345484d2206626800000c002c04c04ca1040000010b1034144284004164203500400b0b03541c5464689100c203009240c1c01c0911540d02e00c0070100031400c41148000f451050fa0001d108070340f0281c05949140261000c0310320b24a0760000c200001c401a1b40a2000d1071054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 934803480 1250 934802230 934802237
    0x14010204030f0b070201021207050d090804090501260c0405071b0605061002011a09070e0a03050c13060b0711120f1c030b010f0c240218010e06121803040303 69
    0x40c2450705102d1404070001c0c04c01c0f03095a2041054203800c0c104640722030f41c849040d0820b41e84420000d14101e0280050040090007402d001502082c404055440581603800e8a0107180d0000190f142d181c48420800c1c007580d0450f482203842c8026840c054011a60003a12031030140700710744600c200d04112304c04410302116265107410400c800342c18458403502e8180d070503100034420200b928a101c0c0d200d1179000102c40c00380c200301d40041e02d1030740101e080f24140c000181c0308103d40d0b1f5890418684640ea01c001d1a80f00e00c10301d1344050000011b600440d0706441c0d01407009403130030344a5a525055240c0905507560460083c41c40b0b02000c40003440040c48412910000e010442c40400c00b215158a940090500307042c5410440c10890341d00103540341d540c905c24144400003048904008105072440c4285000142a91100390011440368021b000d0003810307e100050800000e200540e11819003002e01e5401400600c0440106143c0f41c0c0400c1d04000365007100d419000c002100075017158429082a40803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 934804730 1250 934803480 934803503
    0x7090c02030c0c0a05060d180f05070e060904032a02040c02240906280c0e24180604030204020703050a181a0a110a23030c060c071401020403 62
    0x342c4805118083d41c460b0100c038048122402c2c0710000340207018615084011541d584003800c00a100402e244244680004000e00d8040316481c00039540c0c511400740003000d600c0718002c11850705040704030600070355154640c68840d0011000b450454035078901007850b5030780203804c28400f503100c510581c0c0d4020142c0d80600079007000240200285000455200d00c00040c11081154010020840b680c104201c0d070301121200100c401c24221003c400d0940040e81d910f454101100c42da00807640608000060f64040b110a00000440c0525841c980340c1d40d1040030200702c00395000c12141070031041640020811030030981ca80d000310f4102e800141048000c80c10000302140c2c0c041c1c00c4801c80303521441c802d40010340d40b8280072095541002465000d82d000c8404140502814010001811014640703401c0303503007000c3c49041004800841700b200e11112032941801d007039450303408800c0303a0024059070001c0c0442e465144007610716034402c0405a40080081c8140c0e4220302080c0001c0000b10b0140d1440c003030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 934805980 1250 934804730 934804747
    0x70806180a1b080402060f07080d020d09120518010819060e010503070515091504081903030e0703050a0f0c0e010602010f0c05030f04020f0402040b07030c14010e1e07090c0203 77
    0x3003039500c10200b002031244440c02c10005070364400031184100108282d05445844c1441c0541d001e002d285010351803280041841c88403106541d22081c5a240036540d014901c1440d14030903900303840b40c0945200c0403a8407a4110806500444503281c00002541d01e40c89207590452140003218101d40260381d6030a5200d004011510701000001c01416007101c04140074069500c0d0441c151250f140070320b000e00300032480e44407c0c3c000034041d54003c1c842c24041c1c0d031100003081c0e005050405119021404079181680e9544030590000b03c817002c0d241d01070003c0c9070050854940e08000f506207401121011f46400000c04c0c400c014400050081165070000310300e440d04024401c0541e282080890104a018010040050b10b2461600e0b0895016680300054843c0000420b019100e16040701c03081400004c2c81d80c042580c0000301703403070940c0240044508040f08200030381c20f0307416002d0074500a90114004001c91805c40310018900c03c0d180c0d0444145650f9030b010355040d52011080000580c0000c00c4000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 934807230 1250 934805980 934806011
    0xf0801050f091915030605060609101103071406070f05040f17120c0604030206010b1921020a050711060315091e13060e010b01050313031404260f06070806180a 70
    0x9401003809c54002c0d08112551002c58482414400b152080200b10071100304145011300454030840d40014000615072949003d46665550a50700e0341c000401d10105001c0f0715101f02c058600780c0d0101e03c000306801d07103001c0541c2001c0c4010b0307100880c5ca000b50b1120210781407442c0f00800302d400c1c01001402e02c900d0941400383c14a0b030140c0c0b0050303010f0801c00c44442407005c6d1201d001401c220034100203003400541000c04800800d40619100068400220607883c9074010740074200f554450240d600202044d00240321081c04260307000c0c050001070805085007850704641035540304c041c104000019481280c110896000140c23080705225101c01e04441c28020b8034083cbc200141905c07402801804c01160008005100c010f0503586c0b1602035100c0881010700c1a45500310204031182c00503291902c07021080302c081d07a5050094071025104c01c001d905c004010032260500361040000e0700f01039036808410340b441c2d6401481c2c43c2e8800e01c26007011040d40c0e90a94941d00802200c81c0c0040c568900380b6125 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 934808480 1250 934807230 934807241
    0x3040f0b070302070812070c050106140a08071d060d0f0602040311012c010908060906011e0b0a18120b160c0c09200c0c010f0801050f0919150306 64
    0x101c1014010849074012035111000c403801c1400300744480d0820740c0ca04074100c40300c4104203001009542061000201d068225100311200401152524582c96941446907940c0d00d05100b8480c80f19000b084402c00c040103c1c1b40c095208601a10745085c2095503640c0c48030400e20a101154925404a014010b0112110040c084c5000038280784001d81e1000894400354504040c02d54102a00b8a60368a156445030201d20000c1407000121803107403c0a0900e00e848000134084c400d83c4042080240e000e2029510003102110700b10004145070049809088400b00c4e02940300200740341e03848000103540c1101c4480e0707101450003001116582d0401100780844000301c0d298940401000c101c58502060b007202d00e11003100d00d040000901c041109501c40c0ca42d10030031100c640c1035034010403250785003100822101c900420036038594a05002c08081607908140030b005503074221190000e8000c3e54205050840e802c468140481d003241262881094140c420112548008034501c03001002005101d0085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 934809730 1250 934808480 934808491
    0xb0d060c021e03032e0303080f0c210a060e040b040201030509060115031e240806070912050a020a0b0c0c04060608040210090509070f0f0f120e070b03040f0b 69
    0x99404542500c042990340c4c003000e0480742001c3c00b5401c00c14005041d80401300043c014000d180f4160a0362402c01411000c012203d16041600d0b01c00040c0203090795000325188000f083c41d1003801190700520072241808020000481c2685e540c038085603456008030b01c0c6200b00d200354000d003030364030305403000506454002d2b05091301c43c2d0042c1c006104266014842c007400040c549400540341c841440441c070b0580c01d0f0041c1084140c40c02107011001c8040501034001104144800c6070000d13590750400d6621304044445100207481c81d0310a0104070401803504606030702038811100302c0300054002a40c280c06a80c4110b038082c2001a400001402c284088021108100d40800c201d034600f2202600d5104002d0000f8821142020000c010324018010900900b002803c80c03440f51a0281001d0000d0049030070040104207500100e4000600c651354140300c000c1e1580e55aa00c050403851064050300c1502c1d00d500c11b83c0140440410000d982001541c8075030b0003105101c4840d0440d091500011102030308 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 934810980 1250 934809730 934809763
    0xa0b0102011505040c1707020303010e1602060f0c1e0d0c08040f1403070501050903070b0f13122307020a0e010f0b0d0f1b0201050105010f081602010b0d060c02 70
    0x101a07004a0342d500300c1c0003c807103050f0380101c3c080000d07100c1161010700c00c0f9082d40340c3c1c1407684180704002d0350004c007840c140d444041d80104076840d40800601c20381c0c443c08038000140c1c05000095900c040c11807a0315045072000208030308040d45044482e00c001070030f1001c01c80340007011884850701c0c0782c280100c0b40128018186944030f4140317512400f981e8403c050b4042c00702c01c03030f901c0710300e207071744820001c81d101103802000801a500707002004580703030f178468401604d400c003580c03021503070b12102041700d01d003d00f507202c001168181c51a40d0302418120582c00440c1800080482e64100020550091142e880d00720b2816503035a21a02c104400d04d401c07a00301103209010840140b050740803502c0d1a42c10340720144c50340d0b625690701c00403100103480480c2540d8061804c01c02c29200c2c1e03051b104860009250700390006d04c1142e8943c8011250a803840454500140c01003021400410300c48400030b1004550744004650007084901290500c68800d90440d07041d0741c5d81282e440714660500a02c8500b0740c4091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 934812230 1250 934810980 934810991
    0xf05280b0a1104050a0b1c060e0a050910091121030714030405040207062f070b2205030307081501091e0512010c091203022d01050f0a0b010201 63
    0x465a41500c0c400520030422280c1e00c0201c80320115440095070001c1000924600001e41c80e22140407058005191060721003405010a5290703031400c0c06a5070940b44c000032201043c1d900e00c034054014080c06040880a400780505a141002d1180100c03141203000b42c04181006400d03005000c0200601c005440495003130005600600202008603400b154200d03c5c9051240743c482d0300141944510380c000ea40c0607200042520030004150840c907500e2010742013a01030101d030095241206000071242000700c0c00100030041c001400b40803050b0f04507664442c1135a1218960304041c519002407807050314143e00200820040c0740e881008668461800d11024248400c52000604050158051301036a05034030721030341c83c150408890041c01400b0040882c1d901d80c0103883c0300e60003855100c03984800941c10708004035402d410580d0005042d540741e4020016807035600600412010070b030040c1c10f107200080c403501c0d0307070b4407000d0007003a0140141124140050038240080000c03540b4901d0311505690605 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 934813480 1250 934812230 934812233
    0x10f05121617120d0507030b03150c0d02091008040b150109050907022a0a270b010c1208070905180a0f020d02040f030201020607050705100b0d0f0528 66
    0x22141c030480d48a080400042800c4040385414100d10140c01d0700c500f100465038510001694001c00d0048045c1d0702c0801907080050141910742d20703102c2103903030700840d4100841e446c0074001000b0008110b1400c4c0041c14012000300061221941410710b000084281c07090005002c502c24036150409280965000b00004800000c0c004c0e641317034441d8501c10350324040016000d07030080c800c1441d640030500b084d01340465000c04080c0b140c030030090400d008441c0ca000c041581a41081b00c00b10030a000031400321034820700420035001d014090070b0241001070601480000591190009402d500561143c00c003030320701a8401070a2a0265100c1c51060103c0e41c0e00910b510305445095410050381b030300100391030303080726030030406442411481c60391280300050008000d0100001e000c01d8910036801c0d03030130a4513a00360407200c1d0b008145015000341c20104012540684660006c2000b4038058501a002d02151f01c5022800243c010152004d4000100001001402c52500000c1152a8034035046480c990b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 934814730 1250 934813480 934813513
    0x150b130b030c0c011503030224310c15080f04140106081002030a0f02130b0a0306030827031f15050d031215031a130b010f0512 56
    0x5109005024034000003050782e41c2d510004a541580c8200000d10070002d60030702c11800d05503103100c180c00601903a116000100d4401c9a0f241e04d400303e01002051a881d05070801e00640040758427061045030300c82c203071a28a441442a002020300480d45500e80c5031815050206502e0003c2e90300e8100402c800421200c01c0700c08040c3ca0b04a600000c1602c0e156005042c0d13580101941d400109451046894281c501c1a1580045d44600244001803120000e490020010b9006814025240c1e0031001d00500c0440c1e0024041e2000801c41e00c0c022400315925103665030258040340c80d07001800480604641600043c0100443710141503000b0000c44030744100300d60044405410315080f113500c0e94031030204107154030103042c080e11004000e00e000383d1341480c001d81070b001d40381c6441e0086c60030500c40440d0804c0b242c02c1d2000316900000842c0f28024405044048800c00130003421605088020341008a004035400394042c01e10b8103e0152902d00300010451070310425100503d0342c0d4000d4110040c5400b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 934815980 1250 934814730 934814767
    0xf0d0b06030307050706090f0e0f070302181f030e010b03030301181e0f0c0212040522020c1c02070b0d270804081207021f1b05010506010809030a0f2105040501150b 72
    0x2021714cc01a01e4801c440e85049081e05207000359640016100c3d54250181c100301210700f203030005074030100310880402250783d00780d42c0c00951042d81600b0500c01008503070f0740e41201202c14a0360a800207a441c2c00c2440c64000c50360310700501c2070015a24403120f038030105248103a01643d10540010481003d0442c820501c0d403140f80500f40c0641c114882180191008850605904d0b0200c00d003552a04101c207269940c550800002007284c642c08070614005900100d20b032404e44500c05440c07481c080c0d4025000018004500740350740740144011803000c400301c040940c01c1099200780200f958462600e910645842c89520710021514001c03c417410040c1d07110100407200c0c0c0c00e0034840c0c0481071080d03038098980015404040010583d201d44c40c10030081c043d8032140c0319001c02d0301c03155600d844981550742c0c0e074040c100400cc0071a071101c000c0d0352058000c0c03152034a5044515880b107041c200500c11803081e40e0003a40c040b03600780e454043d03a0300964034620300007019000302c0c6040c0d410480d000340404104030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 934817230 1250 934815980 934815991
    0x62d0f010302040c090e190507050a02060c030411030312010f0b090303040320060715050f06061602121e010516090e070e060c06150f0d0b06030307050706090f0e0f 72
    0x5580d01c041d240158003644400c8002c00c420401ca80847c50406103552040f113042c04088503007450400011103880c003400a07504100c05950040c0760036a03c840213144035510181c004e9a000c0040d212503003095508000030303c541c51550018014552404440e850118040e82041564140074410422075840000541d82140d401011000a00184850034075410148160f600e800040009800c01489000b0700480045013204c0801c10450b03580c031003042c50007041540c056521540400c040c04690100001c00c0f10610300040c440c1030070305071110301d4500d4004201801044030200546451451200388903a0381d200466038000000352114183c0140051014068014003c00e040003268034140b080e42c05d444820001703002c40355150007084100740c5e2000c08641a0780ea003021208810181d0910140300e02c074881010f410552005804d42e103846458800814283d01071106001080200318100f042400921854483c000c2d0142055260643e43c641c2c1e0b04402070100e0404140403809001500007a07008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 934818480 1250 934817230 934817239
    0x5070201081b04030f0c0806010509130c080f01060501180b190201271e230129010801170309131d030d0b0306010f0620062d0f010302 59
    0x10741d03540350b00000704403404803038003900c4801060201c10441c40c40b2000c2039841c014910281001d90304e00543d07550300024040e168000340b410703010911040d40760300c1042d10984280200c80c5031340c0c0c44105141c500030014900b00700c070369190781c0100620758000300121400d464080e6003411480c101140190030f8800c4401e400c55039241c502d90b514402c0d100b0751050f01d444800302c418083d40300c03400555591500e10f0581c141c950b0028850301084541c040d0011541d015402003095290041483c1c0c100f48044000c0441d103c01c3d500c84680c800c1c000c0303440d41c09041ea500070280c543c004c204034800042550780140c019000640c2c0300140503210000010a44000c0c40c0200e03070528100103142c0203c2d024080740c401381400f0b058546a10440b00c0008800b0b0400c000d41c000c0100020200202055074554080c4114064070892040a200342c500c135100300c05000c5001c05000119080001c1d0903860b201f01110a030690f9500048001c07a0b4168030121200d0440c2180040041802d01d2800840302d00c2e410b101c0240308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 934819730 1250 934818480 934818497
    0x228090b09060127061d01082e050d0807030f051303021c2102061003020a090203060a0e07020607020c2b020307091401082407081509010303050a0f090605070201 71
    0x304c02104442d01c1c0301c101410381500c030566442c1005014980008618220f1301061540e60603075511030320703603148070300d801450702c9012914030401c03010301038140d41c13015040c0d5100460101343e6482d90071035105090300c02c01d4060769808090900070885c51703001c800141040b00800405031a1212003150b034040e22340443d14a441100c050700080240302c000c15005040081c0d2541c5002d01c2144c652401e104005280c007a1100d580d900e0300210b811080c18000250f20010140060000a205502840c1d20110182500030303042e448024142624108407100801030b4440030801440941c103000c0300d0740c010b0003550710b10b2040241800b40f080151204160140221001c40c0003429950204600d400074080d2000801062405440801c8601e009014404503807150300184404900c0000819221807030450044a440c1c40300901103911400280000d80200d1031031203445100d599860066001b1807098507616614640e2600280000e086081c0840901c00e0310344c0c0c100b0007940c002d0101da0b4400e030b091809041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 934820980 1250 934819730 934819757
    0xf0d05070c0f0302010b040c0503100618050d15140609152b02010e0613050909070302040f02120a1a0402070302161e080f1b0303070228090b090601 65
    0x805003100c031000782108010b0781c1c800b030601d0b4040d40a5000501c080e1020311411101482c04c0d6a40d100a440040c500003040c0d03400c0000e107214003440001d107042c0d2480103c005030b40b4000a10701c0e00448500b40d07800301c00038400e540c0181c241d00c1486103e1070510143e29140c6042800121044c40040c100c8440c8a00d040700c687e81550f554071031401c403908801b0101c1e44a40b602042c844450010903049011a040c03105214003482c00406849107502c604080e00300d584c0c10002409804003010b00824064410314070044016540c0e4003800540d10303212003006071501184145d00f441218003500c001300461a101ea106451881390003012080c5000b80da01581e1098503180480c0380c009800c0070010404c0c0c4685003c2000070400b00c04182c007850902a661110707441b01c585a44420586203400c0f19a40f060185480c500006e083d08401c0080040607a42030a080c3e03000325800c402b403005180c4c203403d54441440540e02040380e4090181021120802503582d841d80441d00c69803016003c24140a4603006031074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 934822230 1250 934820980 934820987
    0xb10120302071802070c0b031614070222050c0306010e01030911040c090e100312020303090c0d0312020c0a022d060c1f0504200102100f0e0f030d0509030f0d0507 71
    0x86106034000346400126658240c01c207c15002035506d1607030311812102d004102441480040f804242c2384140c3ca19050041c2e003040182c0040780c8001f4440072050849851641c414031803248125050644e8554030710303102000400c190583c00c07004e0306051401d800b039404141508422110410207440020f05e0144d100c0c8141c075121f01d02c0d881000c05181000030440f0b0844030880080c00c481c0b181610100404d901d1105a8a07800102c441070020350204800e0030603441c0581140003510b0103030621407441c401441c1d0b02c406a91210850003903070342c000c0102d1011030601c003042400401403401d6161680c3c004a9a40300000e10340c0c05058450180803d071504002c0040c040b00c0c20306408800400d03040700c41c0c6217032480540f40c215026074100e54080c456100300301641c1c0d0074181c3e41005a020300010806403098400400740c10010813052650b82d01d003442100c00c100107010303030b8880c058015a200c0100060b2078050b600c0080c03000d65250006d00803c558802d2000648500c207160000103e25680c1d2020200d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 934823480 1250 934822230 934822237
    0xa0309051c060528090c0e040b160311040e09060601030e03040905060604150c111008060d1a0903040f08010612080c033609010303050d090201140301030b10120302071802 75
    0x55040010b141000604c10440d90080420901c00c0301c204014540d00c0d2100310f0000001c071805003030700090350006280400404007030710b9a0821400c001443c0250100c8044007508550071228007450243e050103207241d070030009154003074070900e414084001016182c1d501c03070286118420880362240702042c82e80d07030b82e2800d85001d405140c0c4201041043d001c1c1c001d1039000002d005a1702c900180c01120f065003800746071220610319640f07a0840c180c89200600940500218040d40d54103080c0c0c0800c1a07944d8070400c664081c070030b00e100840d00d450078202c0038000019154003115640c0c0c90000b00300300540400c003e07400344035003000180303441d290100c040b41e0640c0b08210051180b12000d2100c0050703210010f4002c10400080400540e007030a6050a00599030803e000140c0441c0c000e10901d0000811600200c2d119032041c90907108100e206540f90b4403d4000780c0088940d01d04900070882842e0314000c0d08001084801a142c1800340c80f501c000c1d44030a1035001d000d451050b00154042014104c1e0101c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 934824730 1250 934823480 934823521
    0xf1d0c120a061b1d100f200607031a0a030f03140c011d0c0a090203060f090f0403020118030516080c060406060504060503210703021207050a0309051c0605 68
    0x24440b0010f03a243d0690b030559a4180180400e4414580762500c0c05107546110b08004042c000b060a400010303420354040045c44581e40411840703005416000c8050001c40241c121003100612990810074005815904500700840d00c0c04110034201e030356607450307215000469400912401482c0d0b00e80c20112022081c0394070107152404002031a4050003815440f510912922141400140702d50043d01c40d10380b85200401a404850300c00144118503035540112342002001f801400009003110103d141307070200700d400b1240c121070002000b041c95020301940300d1012100b070b14612a041655005005030052800c207016207100c1890300b10400c08104101c0716407103400002c490301c5117028035045d000382846025044c00f4a0400e09c0001f00c40c05c00190302e90440c02c9e000001200c00c201c2944900454100f06410f0702144120500c03100d0b10030010000300301c0c1c217000304054401003c490502500300600e950005001380160ba4103420320004090700d804c00070354003d501148540314104000e88071512401e5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 934825980 1250 934824730 934824743
    0x2060f0306041d0a11011e110304180b040f020304080406080901330608060d110d0206120117030a140307090b03090d41040f03060f1d0c120a 62
    0xd03d0403429000013480d801007480b803c4e8582c81c1c00d030200011101c11015504c2100d42d20400301d1010364460040d01240719500c0d0344000c03a41000d60b5038815070070140100d103030344048541d680c0e041901c60800d4020082c91240310340042d499405c0940c1c43d2241d43c0b10703a100e80010015040c0110380000307400e400100d050519402d501480300519000312003c070b07030010800700c1c0307010190500148090061401e5441344000500c4c0005050036500d88016450403a80d40c3d541c000768105100f130041c0c0d60314010b40000b04030f00c00c40b222190f0606910700c1ca01ca1882c0328501441c1d00a01403010040e40c080b9000e1011000140318544035210f015050b9210051a00700101c0b400300402088503c0d000001c2500128005694904545007542c02a050908031080750005c0c08103030710b050341e00d8019450024404115174840461909964001d0485c0b600026002120800d494900c84a000c400074010404561801001c0d80034984400d111a0354556482c0903131801060348504403076101206000718051030344c0040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 934827230 1250 934825980 934826021
    0xc06020f040b0c16031e0602070b0112140c090606090d0c0905160c05030301092a0f0815210120030106080702030408070e0a06080d03151202060f030604 67
    0x2c0d402c2046801501c91020180f140d2000c11440035001c40d800000c6a4014203000200a020034003104002d10100c01500d035950200034800003d020a0380c0e50f402040d0200350401940840d00d881e018513071303c098084905602c8104402c1066884004543d0088001ca03030850b540d80c2264046200d44c0b50024020b0141803005000141c0c1c010701d50400f501c80c0d29036880c4048061078a90084c0e40c0c1550211014000e5402880140039000c10b681c4095000b030404103405440c50a50354801a240072400a404000390b07050600c0c005090b001035990383c0242081405a9000c010f41000c20200c0d0382001180c0315203e49201100300342e0b6801c3d8003114003500e141032910030007250b540c2200410392007031040750000390b6024002030307580f0301c04410368003950400006005103030318014000d448600c015000c3d04915507120710000c2c4000c0100300c0d071680c181c0d0b10780340807401c0407214004003605d0002d039000880f82201004510010b80e28401102c041031418072010340c13079454941c00b0074014400751110740c00700548003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 934828480 1250 934827230 934827239
    0x13050c0906040f0203040f060605190306020a09030c0611010f0b0f0d020a1a04050f040e0d180b0d0c080105030f071206231b07020a150c1b0f09020414010c06020f04 72
    0x20503a107147c80c041c140920015a071101441410100c4e08100d04028030740c10001d000003296500201922a114507261800301c6d140c2c3c84034031240703c0c03d50000010a40c010500c020803d405c0c06024540311b55510104442c0101c10042522600001002ca2040450061140c11541e038800711002030104000f6809124140e40c2003c901a4002d00400c1d1250590b080c82400030300c0c0c40c0c0103601450500e0740c0517040e0600c04100a4032030081d04003000c007040c4c43c42080452032010000c098071000b010220007003803011071104042c1580d2b4041e0841c80c06900f018010f2405900005121400c46c0c26142401011114504000004008420303405040c6164101c04000711b0301d9035905180174035420f1054880c00c030a102114138540c4503207200290050180c900420101c503100031081c007480220b0400080c078004998888240103540212116a8024050b0034020000c0044002d005814a0442140b03031a04184141803070903100a002c504028407948500d080103502d8050725072683c03c005005885641380d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 934829730 1250 934828480 934828493
    0x41104080a02010210061a0c0703080a0509100809120f0415020114070305040c0308030703140702061602070f031e17180103021c0513050f0c0913050c0906040f020304 73
    0x7100380990040c8200b00504041c4000f44c492a41192202d411514002d401c5100e05007907034114500360800307070154420010119200100400154a0075034405542e981483c0030056000f041c840c403202007003647d4040001500700018045030980382101c205844000341590710003a4421500308031440d02105070b82d1241070382c05404c0000300b007122100c9103100e660f60b80b508604662045601401e010a480409c001080300300004580100c480e241c080b0710003032421202c0e03840c1201551517800590011041050901c1c1c0d2182200f00e421542c8054070501c1c1c40c20300f0040005109000143c00c00c50060602c0d842060040c040b00905a8860000f00100c1f1503c0e0340d40300f06030090281c611710800c845c03da0309030b59803080c0308940b440003a00c00038810f003005043c007203c0180401000820746408040040d40400e41c01c0000c0700c00c15042400900818103000140008054090310302d00305a8008a040000254041040c55844c1d0041e40c0c0003046580710740016018248107032000703100c0d91001040c0400d1003203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 934830980 1250 934829730 934829743
    0x10207210305244c020a050606040203130c060c03020705090103021e0105160605061201090f14150c0307021e10020f042705060a1202090604110408 65
    0x540c9040040d07070381d4443c90001c5040140301c0034165100d103450340b003481d2900d131160b0300c03002090f81d8030780003911030340e0350115000c200c004143e40100c44d44c2d002d80f0700c441c00c540010340b80f0704681e407025040b00540381d503585580340c1c0050300c0305100315004000503204044140e941c010803a08200645404c5035038050281c09402c0c21320080c0c005001d003940108a0b030078929900790403a60702801d80c10380e81d0003001b81142021b00310f40345076040007010400c0c401d07184056614000941d024440000301c0382822020407658602d41c0003440d0440e414601e1800110b880072110202481d0801c905000c0c5008400b1154103000300c513004034119104160910801c0140140514800d803034039000c59500d60070285036000d0110008170381240550207840c00d10004d60468018040e20000940010b0a154030b41c107503160302d09542c21030399590244208a501c4060780798003901c0e1f004642642c0072a0010b0920304484400082c240b0003902503651440481d145450300d500150726007000301c0c203254032907031107000311501e481 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 934832230 1250 934830980 934831043
    0xc0f120d06080604110d03032a0e04060e04140c03030a08010608100b03160e03100519050411060906070c0303020f0d03050118110f0309070501030f0b03120c010207 72
    0x14503000c070108000c240028940c0c052038010280c0380c0d1076188102004400411081c049017010389400a459624003020394424000d0300802c0207402d0024450342c01400040c0c2800e480d8801d42c01c0c22420030960714050b085e581c0003a0465032085855640c488824a42242c1802080d01880001380d1140d03100d82c401c42c40d60695a07555103220080e15202c009031440f03440c5001c0c04a0f080d1007000030409441c14800308d400d20026504103544900c2403a00000d0800600004030345c1901d840380c0401003a40100c41c55083d0604801741d0810090030592503004039959192090f37030140500061103d8143c2d502e03070654640382c2c5d00ca030b0080001e944134076001351940c5d82c5400350b0140d0303c1036000d481080d80c024011103060ba141c803d024024211100c060307001501100003e1100c03140e04004401d164981c0714011882500c08130010f085203031624000400301c0c0c0c00d00020526880c50000031421f280e40100301c264039041c840c909142c8603400034840500a22070740fa0018810100e680d440072804101c10040c20601 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 934833480 1250 934832230 934832257
    0x103060b01020c01020c130e1e0d0f090303080717100e010b070b2a040b03010f06050408030909040c0b0a0c0b10060c080a030213080c0f03010606140c0f12 68
    0x1803425100682c3e0b520090350445000d6000104841d0443c10100e000d4040401c3d030340c00c0803425a20007008a42088640c0c0040e0306822094071101082e110200860074a0b038007585001034000c1c0d140c800c0201554102d00008007000a48408922018420000402201101242d0742154101100000c0001e4081d01c41c0f8100000704500020f03400c000201680e0101da00301e401105140d8074400c02c01c0d280d81125451040601a14403e1954404c442c0040d101506c401c0e501c0d03950320350400c01e268248900c1580020f04000082005208188001c4140c44601c5000d50715500d007510303540f8101d0280d07449a040802e0130100880c0a0314142c0d4400140d0b204c960251240c25500d0301c0f0458440160304903401800045901e158481000800041c010200c5017054600182001c89180070b101c004020743d801280f03c0e034081901c5600514201510389542c2d54214000c1010718034140010b4010041c002500030314020104000c7c5850000b0300c12810000a0ba400f0303900c0003c405403241c00260402007409005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 934834730 1250 934833480 934833491
    0x20c01090b0a0e0607020a090929010b0a0e12030d0c0815030a03050307022a0f030106031101050a020f070801060609080703080306060309100516020f030f160c120803010306 76
    0x801d00380c4411600c0c68020740e074440003010214404d01c10140e10805040360001c0044a0000701c5014074807904209502c0b40e0410110200d9002d4200c000d0f2482c480d41c68908548900100f103a582440c0031184040401c1c1091824504800001204140c0411940406002c00034055401038000d6105401c040401c1e00da0001c01e403a18090030b401040050040781d00f42d48411018800303c0d0042d00990391020b40d0b4030441e4000d90328032003801140410b0100c200300b42c61950344039400500e090440e0307440c050020342c0208203d038a90f48802405a40e8009a141440340c005820f0214500c24007400b141d2131880c00854140e02da848100500070a5a4407580f1300040c030018000c6000d40c400301da002c085036009408682983c9420f0100a03c80d400989000395500c100c0c10b00da034140b02030380900c0d4451b54400d007421110280c24480641000c21454883ca001c4d042041110b000340900025116420616601c015001c400c42c41c0881842078150442101d5211004034041001381c008019416280b12303200c24440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 934835980 1250 934834730 934834739
    0x6060302030402130509030f04120204060b1206010e0307090207081317100c0504051009030b0c0c150a0e030d05070e0a081504051606020c0405061507060e03090907020c0109 76
    0x201c0c0420344000b944090003035000300000340907030406500140c40e0010b807032418404044500c0c1c0c079402640800304a03600f280b840000e61a1500c2488000c4c480807100c546000001d078204824000700901e080e0500c070340141c1040300c5460800240b009003496660442d51954103041000044d0481ca00000315109400303030125518203404410402c24140000400075640c1850b1207101070404992444d0801800b884005040e43e0703840303800c0010203e15101d0044075030450503c05280b10005040031004041048620030810001843c9004909007080c0113520b80c8901c004940070f021818804c80046c4000304460f000082641d11040c0034903156200d102810041f10184040010345100c0c10107150030409011518541c80c0401503801445101600c922450302c9054401d4010703507800a60040e4010603603084242001d1084d644c00410403103a054904070b110807210a2403045100040184d51107500c401c0c400d51081064030b46d101c00003040d00e0715a00d0b106100039034800195030602d0005c0d109100001d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 934837230 1250 934835980 934835987
    0x2112090302030a0602030a0b0d0b07020c01050414120316051c0206010e0703020c15070507020f0604030b04020111010207050106150815151b07030b1e061e0f031f0606 73
    0x31258042c015290456154862000075000105003031001038850b140c41c11641e448841d103515a51040c041003090341061032000b850b2030700401c1401e040c01400c000c184801283c0c1c1d0411040c041045561321083c0580034001415805540c0d824803c01c0062a40c03070b07040010218030702a01d806600800d054505280104070b0344c9079800c1c820008030404d100301051121f07100b50000c01e500e41d400d00842d80306010f41c0281001e06241102c83c1c0001032008181c00c41103160100c56105a030320111001400c0504544602125890107030000303050007603444220340c2d0100290141c1d5810b80c0c010008002807030340c800d4070f080c020045200b41e00c002078520300001c40e403044090400da035600e40a00900c040a6141080b5803c1d64803c90020f40c2d45151000c20b09090001040040046e62250701c446425041c1031605a41b6080052050740745d18600c00200700c40e523100c1d810400601c404071241c08200d6041080410383c42d40da42c544994140c003c1000d08400c8100d5400c0380040040140810040c01e43c0d10b00c2c089 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 934838480 1250 934837230 934837247
    0x6061e0c06050c0c060106020c282108130509130f0209100e1302180415091502033d03020d060e030d06080c040525092112 54
    0x24085000103a008010070069400039903c0051040114500510900290324080003648440c0059015034002d22070341c180341d494100290804c11100b810b0003030084440e45100a1402030034141668050034602d0036548511204145070841c003041d81d18404c03401030014080b820301403603010b81c02d118082140102d2001d40d810085030072207510f0b40364031519820490710341000361000010196042001c10301c20607003100d1074028a4030b46401340b0f5411145c41031190014000c002040d4941c100c604000201d80c0f42100d9000e00b007648500003d10164031320709002070b5404800c40703e0510303202104110241c04030110b60318800048003142e83e0b116548620310384081c100030480031b13005a9402e10030001030506da4810000d0714030070400410070000b2541c1741859078003d14442c4042d079031200c07410441e08030300340141c15680c201924240120300d41443e02925442c01d5101c000e43c00c10811100c1011a441207030700d04090b26035990034480800b1480d0904c0080c82c0700d10000d54407200c3c907070614102180500c186 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 934839730 1250 934838480 934838537
    0x12060b0f032a180a0603020a120906090f050303040b010b180108100302180421091e15120e01050601080f090a080706141503030405041e020d0606 64
    0x4580c0340d59200022074038181030007036165110300700c80a440e0366103070303051009041c0514a0703140c120342c400c81040030800303201c40c02e6100b02c040c075104129032610b02794050021146140b41407001304101050713141c1040104041d40700549a40b54072084e4004014001c00110700440c021030340038880780d8844071034400c10311500c0a802e02c1c010602108030019409045525402018990308004940c0c0e01c0e008116244909005082c0c8801020100001c01400c000880d81003808410076111805a180000d081c1c041c80c0e00804841c0304940211a01ea00711030710701c542c013400107180c110480c0540741304060040d00ba0007031f00004003400c3c03104c003080300c000520030703144110b105139141c0744035413107041b160295441c01401e140700302c0c0911100000032400000003012a144036640004540462000181050720083e1040039110301e49808a0343e1640c000081d44d040c0c034001c680005d18101c2002448020025418150309800c0c004140d207240a074040d03001b9011a0480d44604020b4201501804d100b40004d504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 934840980 1250 934839730 934839757
    0x100c0504142209020109030203011401080f062422050105010219020a0e0603070e0f060f04051003170d0e0102091503040312090303180c080d0f0c08031f030312060b 72
    0x80001c0c0b00219400c0b071000d042c01070405070942500d03900401e0035514203252070034a50203080010401c8600030050503100d8594003001e802c25051121083c0c00100790f00d81c00503460030604140380c103196180c002c03500032100309036480000d09900c00c0e5044e010300424841e00d8054003c2d850403a040d6200b44410641e01540102445112410036560803801d032030203000c141c2c15202c0c5a1002c22480f00560166001d03038225048000d052074081c0800c1a80e5010800c543d010f84d003048203000241c182c100800c1d059aa0090201002c0a000c0b1103042c1903028050109140d01c0c140340c18084100c0d07040d401010102021b0300c0c0180811101c0d0818a0144405d8600800241d403011003544000d045070300903201c181c840d1174041200c0313000c0d03203c03034601543d205800e80b00d82c40b80403000c111181c4104a0410300b9005800c007000c034888088005814910212001741c155040000080c13858030013010440d00b010000e003410301c3c0c1a5164140101248030017060020003501d000c0c40414022400016039070f4103100000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 934842230 1250 934840980 934841029
    0x11509110405090406020f030a0207231902060c070f033c030e0603151908030703050c1e060a0b0105130302040c030914010b01120203040b041202100c050414 69
    0x30030300c000420f0060040d43c500380e0138003170442041e2140300218050aa0150301585400071070074042182c40030300c1340c07401c40e15003c10303400c01f0407030340124034210940300440c10403a2200d068004182c5031720545c6c0c5c1d0581c0500a00002090106030f805151040e20b000e1005049450b01040c0201c200040300c10842c0e4040c032002c118414224140060301ca203140c4a4a40020100014404119550800c1ea44111307134a20b0411100f51508250029829189030082101e80c014030344110191240300d0701401408000380014081c00c141020080e210714518501d001c00c50340d40348440c40e9a12140241c4004080504100e120f52443d072054003550092203000e80e01c0000c40d841c0d94200304c0103001a81c201c600f4141c8801c0c80c1d034045041180003001c2122850001304031120420001802003843d6802090860304c18003c4c00b01051f01201c0e025481507100c0c41c04082040c074554164605440008031582090800030b154074481e03849006031046408001200c000b0740584010440c800250302d06200240c588003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 934843480 1250 934842230 934842239
    0x6060d121101140405152214100c09080708030d0f0f1d071a07020f0303160c030b070806010f0e040209030f16061403010501030b04021b0115091104 65
    0x1506811000c500d41032010524a150341060309440402c07000051190184082106110060202040c0f090900d03404a0f01850701010705122280c4409114000303585080503c4104030317000103c54504a083d400300e642103940d40c010b01000d804201d0b0a2000601c122030001440d0400113040c2080e0f0b4000d001840c00d081152888100070641d200c9420300e001c4e2034511340e02d1070b0442031007043c200d80c6001d0b015007148100f0350100c503d0300c0b02961008001864080b0b0700704000d00c148044d00c0d020365040f580c449000c1c006c9000249075008050740603029000c8030441208008841000c00c0440380b0413920940241c6c1c5110054035416005c55981c3d01042c100c4024a40f181d1082039100c145c201c00030001400d06546078003103850110a17100440a40d80a2210042c028070188210300007845145001e64004090b00101d01386e030b02040c031400e41819141d10282e0b0556880ea0140c0b11502190160407145214102c40980a00300c418800f44064907080800300e00d5403c180200035454603200724171362500d0b140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 934844730 1250 934843480 934843493
    0x809010323060d0c0909030206040203010c0908070b0918180c0d02010215041b0608010e060303130608100e1f15050a08060a1508010f1d0114010306050a0b04080f06060d 74
    0x11050704840a0310310a2000c2445c1c80903100d00790010b0b005c0d5005001038940352050600b100d084182c1c560900642403403c0161402c002280020394001c580095280ca40d00c13004143c090f0a0a942150001554810040c500981c0009608414425421140501c100406001c0c6200c0301450190068100d16403000b80700c03000d0302082ea007152080c050598101083c0c04c04140042d400d0b002080014048001041403441c1c3c48842500500d044014516001c1c2425400c0c0d0035141c584208414041c0100000710f1a82550f050302e00105059448120705190203100700050350401c031480c4900b1306620802140da0210a06940c802d103209840300c1e0728040b8030190039030f070320407004203860381c42852807001065540465448200d2109141c03030303d00c000d505000c0c9460b5885e8080d0001d00800c03440000c94048905541c0e0f5190445600b00d081c0340365200e6840c012805803040d9002242c0207a2035038400520021041c0050044607500c4055820120690f50a079444030020b8410340d034881d0107103071070a010820 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 934845980 1250 934844730 934844749
    0x1509060d0b07050703030f0e150a0f020301030804060f02210903030403021314010632091f031802060d0509030c060f16050a080f061c080901032306 65
    0x80c6522048011070366031901107a0225100800501c01042140416070140a040c18840c00104280111214200f0080d0f0382c1c1400302d028140d0703a0021000c608500c0146c0e0000304400b0602c5407d643e60349c1c40f400c1c07551103944144078200c0081d011040c1401683d1021071084003610244241400041c10110050015009914020340c103000401c400401603032440c045c1c00d40d02e0a00300c000705021210f003031a00c16000050384058144800b01c4503101c094030600d0843c846070841454004030380d8007000701006c503e026010503e900805500102c00084900030b2040d012000035a40c24000d1074004541c030307000800c400e103000b504000144034007138910446411903580b0000d0401103034109802d001c062440c2140030341e009030080c003040c0e09002a00c1040503503c2012030306401c05506e42141d40000901540004040303a00da00307458400320305c0340d54441c29a401654410701c40900b0300d010314204201b841d07002601c4640468078200d9015240d01c0c03800350010074505410b1106030155644c0e41070141000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 934847230 1250 934845980 934845991
    0x706050c030903030d0615050703080f040f050a05060a0c020109020a09050a09150504031209050303070c05030c070308090a060c020904030e01030902120619180f14030424081509 78
    0x1042c01818150384080010b0050600c180724003190300d520f07140030302031542c1019008008016040140802107a0404041c0e83c1021070003409a81d603540b142842c0c0140351403100010007500440240c0320034440002022405440b601d1420820f100c0303110b20036401c940c07650700003d4002545032002c00030b00130207a0201d40d0042c2c3c1d126010541c0c5400e07036250200403624141080c0d615130b0302e0741031100b895405404904441c0340100100038500650b203034642d0720b0000510501c10402445022010030100f0300c180c0b216080543c0840d0b0707096450b842c109480d07801030f44800f8010102000c0015819200700da0008140c0e401900403200d030780340c645007101c070550f0102949040c9501c40241c100141c9481c0445040c442c40e03080903005c1414080700445400c00f222040d100c11b40d007070946600d10881c42080010703840364050343c450700a0076289000c041003803401c204022180008107000450b80c151808031500d00d0204103081e254a2100e6009443c2807005541d20b900302940018507403180d05080180c2504078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 934848480 1250 934847230 934847233
    0x10806010f0827030c060f04020109140a05060a030c140a0c0b0705070203071518030b0a0e10140601090f0b03060f01020f0607020705180c0904180501180209180706050c 74
    0x3000000340c2c0c070307590403d00400c4001a620000b040280803900348541900065000c42c0307100c090030560002000780c403a80c0101a012400c40c1145065a0b640318a203100a20014202544a2125540c003900500800080001003000c400d8a080181000f008592400303010352511015540c16840d400004000201100188603082180c0c0016a404200e0a00103003004c00c1840c040030100c5070300601d100f0350980e0b11303580005800b40910000e00b0140007a0b520407a8108002500d2014031140c0d80350004140e582640180352904440a03942c002c02c0480c4030303450a03200c405c0c102d50f4941e0052010160b6100d02c49802c41c0c207101044140c68034014240c0e103010148100d52048440b12405410080140c6445026a12000041150307062620080c044042203402c85030107403601d481c2c01101840790804031481240c0d61030b03250040c00104889a140382e604203008010b42c40e844800c403040c0b07180d900c1d401d911400700080014842580c112408002640d824041c0801c40d207458410348403a00000f4003080345 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 934849730 1250 934848480 934848511
    0x6190b01180f090b030f15060a030807050601030b010501050f0a140705030c01060e090d050712090305060a0c08060904020d032d2c0303070b101205010515010806010f08 74
    0x1081c44190103001d0000e08010590961a0180ea1011107030a1300119000f074001d600682044440800c040c0e02281d141d0340440c255035503000005142d8451900300420a04020800c0001c1c0b080002e0700f54180c912400e00c41c1c8d080d903240c1c070041d04e09019040380030002c088204410802a80308131003208019441a2101e81000d1496403480c0c11900030181c000717000e80d0740e014200b15030030312299803c2d044810900039011030700841d140207013103100d1000040c01d222800356103d81d4452141c0709280046400c403040d103245090008101d00504500310701c140c00a0302e1100420150b180403610360f405994006d060713100030102d03130343c080e00d0b4035510001d0101b5400d14588022003650500f2051148600e80e41d0700d4007949403491000004142c2007802c90000310f200046000c1980d1000021220a05d0300122003100d1540c07a03449940c50090741e900071040c216200240360b810420b0540000d80214084d12a5414a03200781c401160292001c450b81c1b800150001c1d5580011400340d074040d0f80000040b80f903082c1c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 934850980 1250 934849730 934849757
    0xa020a02030706050703150b2d070204060e1e011d0411031c0801170624180601230409090c030b040b010602120408100b220501090b0306190b01 63
    0x704c03075044400c9408251581180c803080090448004d006c1c110780100390341010611501000c4158401d4503441e9800d441441c05d80701c491130302040e10b0719a580284140042511244a0010f914050390000f26640d00702491200c1c0d50240840b180c140c90044070b6090380c00415074001da55a04010740143d07000c0d0906090114152414002209000c6c010760500d00309031003115005148000c142e0081c80501e11072510b01480000100f0300c10703000084054001d401146201c1e41c0401410b264002c180c1c807025111f640180040c051081c0d034400c907000d88a240c40c000c00d1400050307900b00600300044030150104800d21001c0c996034000704606000c0c1d08218016602d943d40d402240c00c0941c1c0c02e07107c040801c00100501e03681003020320242540c0c2e540c800e0803d07107810180c0d941c81040c40403120700c02d62070381c001003103548030706041036615407100c01203003c46454540707007000404080c01551001e5003031248065080c2000214a4001c0144142000e10300c012480700d8402001a482001c1c10800d09071070864 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 934852230 1250 934850980 934850993
    0x50d0e06090405041e060501051806030a02090603100903210b0a03030f0507050703060b12030403202209050c010c08070b040809101e09050904060e030c0307080c100b090a020a020307 80
    0x50920303c41c210014865041208108855039120a0500b010200c20300700702f82d5860201b20185482da054801001589500d40081c0c14281b00040e03407410540b900c0f050b03005240d844440c444440030000f10501600b040c606034041a641d0400b099600005c80d070000f080068401c24016082d8501481c040382014401c0d51800d040001c0c591041c0c401c00d442d03814266141c80d0914041ca4400c0c1c202d0011450301c1d18594840f448094440d141036691078403103984140b42d88544546024010f00c0d280d0341014052280b490b9030082081c080c0c165510321400a030010254002c62940900b1a00034180300d04250540e540c0a0550100410031580103500740311788081d80d03c900d6001d82500d401510703000118500080d480b40f00303003a040744003030400c40070450800040e201c90b0300c1c281d0001c0e0031680c0403e05200301003c281c134520074005c11044600c00012138400b80034601000c0c04000c81c211003a034444403002d42c00c0340305981d004a4919442002c501c0401c807110940e9000740740030754842c01030340e00300340487d203d0f04c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 934853480 1250 934852230 934852283
    0x120f12110301050901060c02030703080a0c02040e01141807120f0203160306051317030720071a0a0f05130e190b010f020c0607030306150507050d0e0609040504 70
    0x540c00c0040c044014040b610748650400d02408042c0341820324015107800107580d45100740b1005c0d01c10f100015541c0040da11030b5420480c10b50f009481401180c1c0c5101e0418001c00c4100300110b0711100600c0441d000724200c40366607510f180c4660007010716504001703d0b0076040c814a0380c01c40751005075003052001030f1024044150302e05030700794801600e1442e500b000401e8540c000c0912580c04c0f100d0030f04800150210004c240640d450451054a030398810500f0340b45030702078200f85400502080d098040f0001c00203500c00c10303900c2c1210003500070504168030f04428040d11402c1300201d0051400300380518070820107002c1e4403960100318800980ea6a81303c0403a048160755011018143c010314079445001401080f810f60000c2c41c0010800800082c025215400303011010b100300d000050f46001e042c480e0700181c000d0403050350380a070003212108001d003007035008050448460141403900c0070528021182ca110340080500f015191140740f00800c802450018800c0b140d5140840d841014550441d510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 934854730 1250 934853480 934853501
    0x110d0e1906051008070f0308030606120109061503020408060411011e051b1902061e04081005070c08030a0207031205070f03061a090d11060711150304120f12 69
    0x14076410020740343c0c03030800761079080a507055114000c1001a10294880501125000080f65440b6242c4c480003818a02c6403c59a07540d0581580020a0780d45855028004a17030701e40b03107035030302d11010200d0a03000e90140d44500c01c1e03260000400500410a01e10600d404107105241c031142d0001c0c80d6000078080e072155040c1d800002c40c086180440f40c001c0e070882d10b2004400900034040000c0100d509100c5e03417501d00e4001d000340c00124007900031100d0720404c2c054055000a465854544910010741e0b1004001807041c1010b0a02011400e11409024010032486d000389119103159950070051029502841048040100341c4440b401140d0062040b240240010758803801c44954440006041d2001c5800c5508004609c1400552214032202100c1c043e40050341c3c54081c104607402e01e00b40301c00b0308810b42c1d44c00c03060001d205801c001b904584954042003c48030440200002e0030051300710f002c2101c0041061854120044149018400480c800740d210310309120042c841c0c003070075811390300c55002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 934855980 1250 934854730 934854743
    0x1504050a0c0f0e06010305090d0e060d0c0201290a0b0f0d091b09181713030c030c0b0a120209030a1b170c1c080d050c030601080a110d0e19 61
    0xc1c1800f8078604009a070380c2100c02481c09014500380303000c0380e41c1c4800d9030001e442d050100c1e031022440c21352205d42c01c0e81c504d030019a104000f030707207200328000c0d01802c0010f189981c180759141d81d000090721400d440c12080740c8080e10030001d203400c044030700d0040e512092203034025450178415140400424010b0000c0b0301d01c5481e465080b003058506500d0f464035190030071007140f030500d0b04080f44140703207a030303400f801940010190043c550003a14001c260700c10301132480304036050070300301001f80f1690003c00b40899100e07110400442e0382e11302c0784120070b000e0300060f00f001490565080311a080c25401810402c4001010740d460305000f541d407440d08180d0300410070103011681030b04001c01e40050040b0402c0c0940c01d40646410380c0d000700050030721000034001c00c5101d59070416110c180011881030301e05030344440d00c5c108a03504200008038440d0304100d410030b0004900380c0c0000c0350040d40703010300c00404962518003403c006c811400c250103440d44840c1002c5910608440d0b01e18060544a9660054002d61 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 934857230 1250 934855980 934856009
    0x3f030703020c06160516080f0d350903040614040602061801020d0f24050a03140f0307150506190b0a360e010b0f03061203070501050906181504050a0c 66
    0x5850307230074083c0d08600120703180c00004c00c0d10342e2160000404a000c8000704107422190705070078401c0000b854a52414210303c00071008011207443e0000040094944d141c41e101d1158482200d0811030303100e240a450010380040010841005614800700642450b42e000542410500b089038821105841040c0d010703903807a200400c02c0d99004c49050003045400488041c039032414240444c0742d840700723840028540006c8000300c20782c07000180111034440b8000c0040d2980c0e9035490410600303a1030003050704094180740c10049180c9184c646119880305d0a104490512640707000b0807048250400c940e05001e014030781098081014640120540401c00d6021408401c081014203006000c0c1640040c403020b2902001480100c0300c080544195112a075107080c2e89640380c2001c01c10800e100e600001b010704c00818000208001900054030920185040700e01039074030703030f1310140c4030001c544120201030f0001347c80001d015501da400b996000b80980c0848014040b6651410380d002d0040e03002d086400c4412 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 934858480 1250 934857230 934857239
    0x4030c03090503120315061315120e0616091802030a2d0e210c06072a0c0518090105010815153f030703020c06160516 52
    0x107081d19001d4a02600106941c643e001c450300102d21010340900c40046041405252079640c40c0111401c140b040c1020800c82c3d035641101c0b1840107178a1200501117001c2c2114100120524072400107803218000c0141406c0d103810b00d80302c0408100c00c441d0001c0001c82c21020a00510b4202603441c0505040001607492516054580403900a48421441c00c0d0301020840010002c1000c005070015002000140348a6401201d070302d4846e01d182d040d104405401c01034070700e10700c031540034004a1300e40200b80c50580d80c480307400301d8052403007003500100700d041081a225124800c2403a40425842440901c40c142e403980c00150386180448400c12201130f104082081030075081c007406005004560091410518a1105050b4000300900c0350142225007050042203607164030104984040c458120305c0c000385507504801c4581d40e45000a20b82410321041c03003014150000413900f1a940503800380441045d00410011241c1c40400c0c015140b010798030f00e44c00469020300c40c0c0d503040c5210b188a411094540f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 934859730 1250 934858480 934858487
    0x3050703020f0f161505030c1803070e0603010c020d0f050a17010b04050a0b090a150e130c0e030a0b0c131701021809040f080c1501090614030703110105070c030b04030c03 75
    0x160806117900300e6214489465540100907203404c1080740f0035194036001135100c448c1d602c803420191075a052148181c009128012400d0081c010385080d0000d10110118420503690f43c4100540c1c3c400048500c0940e4414503c07600281c9000d500a02e04040d841e10440c02064500d4401e0b0008442d107030001404101e90318085144000400e9038a81503410251101c0020326020040c0c4540c10403041e0b480981c1c19010300c11140e00a412000130900200e50010758400300003400c0910845000c03807401030800c0300714600010240c14065014a0006880c0e032030844180142c0c028490f01079510b01000c0000c240749281c000b940041c640c654000589925500407040a6000b6600318207010b48a46014071000c00e40e1140401050354118860700d990f800c1070030721300303140804081c001e1000040000002c640f10300c068115604940101c0707442c500c124802d00415449009a100080401410428200c070550280c0d0181c4005e50103a00b100202a40d29110090455421102140066000d07900001007580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 934860980 1250 934859730 934859773
    0x2030402031515150408151501030f0b03010c090807061d04020c070305030309030310090b130b150c0a0c150518211f1503030302090406030507030c150203130303050703020f0f 77
    0x1e0084640c1c0384d0900b440c8d50210524641a020304050720f403801429214840d401510700c8030382c00b8000b0003082d010300c10001d00c455013034042c51250780038910002561910940c55401011403c203c3c00a04020200c1040029030050594903c03078002d0000000c04698140091481400c012001d99543c5ca010f9480c111011002d4116500040ca049030b0800a030301d5051006020300004000040c41191180c0010b44e408004058580420000508422080404151840010f10992144d595103450304915640c84902804060019400b070028030311014051001e103a0141000e03108001401c1042c0303400e040b0b42a41c0240300c0169200d004450845a00c0b11000c9503d80342d1882d0810845905200140031400c00388005400c154002c295005181c1d1983e010340b00540c2c2c03040440d00d455660707140184000701c0740d11030000d40c00c41c0d6010314451240084100c0e500300b001e01d03440c814050b085542c142d440e070704004801d82c1103202d107070403030701d42408108828110680b800c402002034200b0200c003036801c0345 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 934862230 1250 934860980 934861003
    0x251707030f032c07050a06050c0120091009150806090708190b030709060807050913120807031524020f0c10170a0c030e0102030402031515150408 64
    0x5103802c1c80000c12602410b8800840103280403c030f020000403200051030401c20b03400c541c0d440800800001803540c0c20a004068a852060080c0f054003020002000031007102d2500c1c018502040009101314505000054911900c60800388855500c51003103001c3c84000c003611002140002040c01042c0c81d0130284580d00045920f001c0c405864610003d05e40c5884e07100071480c01541f034044240a43e5418001c0c9005441e50410421842d030341d503480c503541c400741c1c1e109240c01085114089100a070341d10408101c034507000040d891414070207410440c2c403500000c6c104010190740381c00401c1410003030a00c01c4014440a1050000552031140303d40788101152400c0b82594814074581e144c21001044844580c00e08440d20051024501d5007900da800b03600d609010007074001c2003008151481503100101e00f4142d65810040c80180f00ba0003400c0307100540e0045e43c164810803a50f0004132010031469481465044400c1c20703010408040b034a0b00c440101d1000314000e0106041c8031100c2c04102d0902c841 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 934863480 1250 934862230 934862237
    0x9060b04091b02100b0f0603041b0608070207031b0b031006020d021b0f061204030206070e0a03031b1e0317090106030f0803040203010213080c0a1a251707030f 70
    0x122180b50000c0d40e64135440180208090702c3c3c040303604c50740c1d40e542a502083d49000e0101075492500745020907001e03a134001d0f406d240c01900400032a1241c403804950707100703d00c10780080213442d045440305201074180d03100c000090203404a01092070099040654068070000d502e450406007008000380c18446aa4845011503203c550500040c282c6024091100c107001c0c0c400d134698018440100700c4a1150074141500c1d00807480a100c10940d0005289200d026a84d4030f45a1080600d01003040c50040d620002c0c000400d814400b1201c0c203070b00c10780000c246103d20518003c91001100040f140c0489240503004901096005100c4100b100c011541c001c170380200170452541140c0e510300304a150316001801d043c07030110014046460235411216504410b030312201c1080d54423412155588841c80d002070142e6540b800010703910325440200c0c0b007284c889262141c1048428113021422041d8452808038661609680d4008152507284c9440c40d910781c0b0b0f2a4070f9035000703581009090120070101d40d0041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 934864730 1250 934863480 934863521
    0x3091c0e040b0f010c08070f1e060b01050406080c03091c02070602070b160807111e010f03051605070302070506161b050303070b04030e150a11160501140409060b0409 73
    0x3141c0c1c1c0000b2035200705c0d500c00b80440d25083e15080c40181c81102071001040183c10842c4200e00001c0c4050030558184509410300c0303510404001125240110320811001c240d0f0b0a010842d42025100070350b920403607010032106500c0070110005074078803c803e15000543c010407410300845a0601181d8040c02c41044840d1030182c10741c81901aa1004000281c040d49010420700100a24004038904040d40140b05070000d01c0048841d80c0540380001140380400c4042c1103c28220b8080c0c00750601ca40d1984000b0010f00c40403040070b40d0315602511045045000c0d000340170500d0794519024060b6a02c0c1d030101e0b40070104c1207240030001d0040b02c60940b99880f6100508000d1994000112641541d00c100005051340700c524007a00c1e000303105412194064100e220b480300100c008400780c0840c42003541c2e02ca924280c0c5501e0142c550034000c00f0214045040d02e01446194050b810125002c0c0c1e80c030030f01310324040c3d560300c03110700b2200150040b42850600150400a104c15402100492649400100311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 934865980 1250 934864730 934864759
    0x16020d080a0e1219080d0e06060405092d07090510050a050118180207060c1116050f370311180a1a0d03200a0c030803091c0e040b 57
    0x70b40d011300064808403c40414480401c03c05000c0649452503401c0030b0038000c0c18920701c521903c03a0000c481c914052803400001509078140013503610b210081c00300a00d0100d03031802c400408004655a400031851055100014640400b8458103101d040c0340000c8903000ca00b42010400300380e505500590402450a00da400845544000c042c11102024100c15107241d4503407210019024110002c0d201070b1608250001941d00002c18120742d5400c0c0056039060141c1c1c2422500c0c41d0744600495401015501d6107100c24245a241c00b0302c041d40303045007865918091040310700704d402803e6506801c580e103140b0030410000740e05020341d0756210490303802503154002ea0b61300810b03900003080160b0303030358581141070307010a0f42d2504c0000d07004026000f450182410304014000384103440340c07800c41e605c40d03161040580b840440d02012850340140c11200b031302d284d43c0b0344004541000c3c068800600407101881c141c94010519402c40c00426220001083c0042c810001180c0a038088940115031442d40d040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 934867230 1250 934865980 934865983
    0x209061824030f130c03061509020f0d1d2b0203071110090f120b0901020306010c0305030a0609060f23011b0303020c0a060b0a0909031416020d080a0e12 67
    0xf9885190305406507181d80e21100010200c0c401880080c004105100b40070050240702d400585c82c01420300c2802c3c00d4256a0a02101288250075210341074100900510b00c0b10041600840c46002541070703c4080582c45203030345414007030308012002445078400103a1400000e4400f140c0e4082d00d060010f1410f1100b41d884100b4024662a4001c0c440c1001018181e42c4a0156020b01c028041000707d1215007512000920400c012810080d18800342080c00294007000c1402120f02c5540180e40e5120800c4460707400761b07000e4002170507014049443e0f03030020510706805e1140784000c0c05403540243c4038920700750381602d54890030701e01c0c03400c450583d81040b0b202d81d80121010b010081b442c1e090b0b900084d0917060440013030040711560a018010f60f000001440410307013015408000442e24910b48a50310100d038411204e200c3c078010041400141516140400310000d0708401c41c28001070398042c1c0c8540d00155500d40d80083c1101e00b901d01148101e01594001c03040b24a00d10182e0704c800384c460981e086503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 934868480 1250 934867230 934867237
    0x200304060e120d0509010311130e07050724230601050d1103011701060e0112030e060403080304050a260403080f1306050403060507080f040b07030209061824 69
    0x5406104010080081a031500061000c0c154411400e482841c03c100900401d558448201d540c002070070980480350001003401240d40544070550f020b20745c103192044110186100400784414800c00380700540205a0401c4282804908011840d2246071505442c02c101c440345801d51001062940806070702ca40110049074208a0900b801d645510320410040e0140821051a0070751040c040000220001d035000071500c00a0300000074407001d91286081108039609100d22030208600305040800b00b40500c240341c03d94007002e800f491915071030b07494004040d070060728210350542c00b6078030280c2404090502c400190408a550342c04211800300030b41c03140d00541c04094907400c00041e8000c00d030727003e800440781d20b000090704190009a448002503c0c6400500c41a00c0003400e003c00140958801e01480e0322980c4440c0788458107858036100c480544034024001404d2607030801412209582d40c0c0050070400b20011160007910403d54184202040703048913045c01c110803644103001d02071410065 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 934869730 1250 934868480 934868489
    0x130b12130809040519020c060118050702030313081204032303061305060402120103050604030816050403030e0d0b1311150a0c03021c090305011415010c0c1e0501200304 74
    0xb00d100e0b00d540c05c030b0200303182d940c190000710944009100358907150046142d504070340e110104421540c46443c2c09005440c3c0c200d5031600140c004000280340a0003900803041968003d08020b4288511034004c603051800c19203041e008114034024413015200483c119081010304201d60b242142081c2005c90b081c5002d00e580d00e40590f03280e00000d0760301e490f281d058a09580f004a01d01010756500d09000b038807400c00360f40640004000c1c400242003181d07210001030003101565556440d00d0702e96201200e026400c1282554030040d08420300003ca02040b0001e0b01803000000c40700341000907840c12141180301e4200c90b50107200c0c080b040c0c00b12031040d8400c2e80c081c80401d003040c95841c2410324007241881e0074a107050001200070000c591070304d035101e0741080550340708000070000004602c141d2025200304a88543c0d4682c102d81c00300d9600d521940c0f502115920850420324041d8640d100c580042810014039000810301240c20016980e200143d4a400200c1d01c00d01e100e1802c45002c1691a48624050f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 934870980 1250 934869730 934869739
    0x2e0501120b010302070204090605060910051e18090102090109060806031e070806010602010c030c020615010f1b064104110904030801090e07050a0e0903130b12130809 73
    0x8084070746900a030111444164028800c2105100b0b40c54600000d0000f0b44142c1d0140800ba8001500d071007840c0306250680710010518000c1c00d02103540340103000640d90005820180e000107600541c803001c01924040c1083d04005603c484440c80010402c81042d030056040000c44424003813aa140031403440b1308040303d04402c0401d80b04030200180b510f08568419001ba202d514000146554198840741000e10030741d8027408424a103074401ca139540000c0c0c40b26203150003102d110000d00e60044001c070b000d540080c00c0000700e00480e0303540380038001c00584050b15400d80f200000e0808024509602c007507003031a0207200ba0200d400614041d80b0142442d5560085800800407805204c110b0a80300c170b0b02e201c010035030311040c0f80c07514000f00745a10030310880c030301241072130201e031540c002c04152881030b170310046c00c0d10a0b6140f41c01c0317101004503409400840c250100700a542d0344400400540406440f4050a0540c0e4115080000d10030020040c6042211344400490348005505001280c002c88011075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 934872230 1250 934870980 934870991
    0x6031a07030e0a080a0318020907110f1e010c030e070b070201170c090a0b18040906140106170603030901050a0305061908012703020606011b08032e050112 68
    0x30300781c00404280a882025201e0340c03011408005110000b4003c800160340c06000c80e10034800c4040c0542c00c0424001e51041080f40001e115502c0f940680085040003001c60762000d00a801e1039042015410000d5100003401c8070549503c0004d014001c01c880300780ca010000c090020f04020b440740c400d8040c14440900004801d41503a116500c4401c10101c0082001c1d95400c01854060b0f4581c8503207206406110301c1030000034070002003005d4030064403281c0022801c50409008200041c4854141191060b690300b00c610319441c1d0b490501400382c0300c40c1c1c41f01d400d40118141910030401c002440e40d4460340c01001441c0a60340d01c001501c980f00058200800d182c0c655000065003001c216000c9100a01002c00c001400f49054000006614117001c1458241e1101c0b0385000814659800150140c0c0c01440800c3e4903503c18480c02444200c2e039120401c1b88442a81c6036549580282c41c000104200203031940004000c8901001032021013048280405142c600040d1a80442486880c842c550710b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 934873480 1250 934872230 934872241
    0xe1003260d02031305010f1a041805011d1009030906031d0109061a01020312011205071e030201090b0a0f05251a1e04080d020c0114090d0306031a 64
    0x14241e41010100450039034581c980103102c4000d10a1340b681c203507415070800d035214101000505c11040c070751440602c1d9100002c848020301c00500407075103001d81046030030f40c28400480c070284902ca40125260700303049601c003441c07a40d051030608080c00f400700043ca070400301c00009820868443c2207502d0b5050104411170903401107071490b222044c046032079500340f0542a08012841d40700c2c501d0391511101c4003069040311001246d0324011552052104901e010050200e024908181d07a2000d05c2501200c41454403a000d8581500540080322844c1c2100d12082c82103607000075554019101c40c00100d07040c00e144034801401c0e910181c1034a41800000030710440c20410a40c201c2d20182c50203011503e52924134940b080c402c0aa818140d840c1b00042d00216070500159060f0341d54041c00203905041070b45030354541b414903920078040340110303945c200700c4600c0205080c040c0c802c03040d0a0580c191600c2c54030b008070a041502c0c40d07001908240c0b81c2001480009c09650b44072841c181900340d10720050f42e41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 934874730 1250 934873480 934873553
    0x30b01030e160e0108010b1c02120d1706152d1611040203070207090c1b11010201060803190e06131e060306030f08090a050402030109060e1003 63
    0x70351502050a0140390a0600c00c85004085141101c802d080c0b9280641e83e83d8220b00c6c201c441120500d50b21040042100d08500c0c1c1c948400f03803845000802803c6219080202c051409404090101c041f456200d2054000108a4071580e40038005a03003010000840c4420300405100314021ba012007101c10000465180c03010500c5080f18030502e8200d07a40c0d9800940c049042c101c10f131011600c2c10040494404c1e542424000d590140c40503800420707200b07081c046680080c0001c00c140e0310820480702c0c05490341095200e01c610076a03010b5140b8410910b00c0741e000a013074500c9074009407140d500c100b00348805640400505140c00d1400d2502c058440401e03800658a40300300d44882d500e1036010310020404503518488454440321800c03002c03200726900c0b10705405440192101915892401040c074003c280031a0041c00d94140081004588076100d00000d0200e8000f81c01c880c041c039550340000e1140c5401e1418158000c0d20302169200f40d01e145a80b50100c07182d41f1301000b10500080e00301205140301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 934875980 1250 934874730 934874741
    0x30b060613030b0705070b010f0302090c07030e06071515030c05121f29031c1b080306010215010803090d1403190e060a02100203090c03012405031c030b0103 69
    0x7881280010f207410b2259004045401080d0301341c800c2084c0c040000340c4070705105400c03412a80d0150014000380c1e61101c018410350072110301079080c0460301c100c85106554110040000c684111920042103842c2c0c8a050211086588241450b40c100e60041c03010078882100e84088074411207203522281d00044070513046c501c00c100f030420720180c10a84a119043c10740c01074036060b42545280003500c5480088140100c10f00180e0079016040042c01e4903000c01a111900c45558641c2408424001a009000c100e40104441030b1800d240100c00e0080d107607410710410100340405192161194102859941c907072041e03159140c0f0400e9400180c0007007000c50b040d0311148980c0396082c0c984031101c044c40d500d84280034507600f0b030004645283c0002d452901500380c507900c21300c5034020100c1c1c0011030302c10360003540040c1c600540352003400d07102d5010341c0d000d00810b43c2d03030385c90050604100e492160141442007025001180f0035000080101141c9000d9401e6103001c41e8545008100b0502d150011390040c107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 934877230 1250 934875980 934875983
    0x40209010e0901030b0609063c03060406050702010e031e03060a18151a12060a26060606310f0e0402090c09030a081e0a1116030b06061303 61
    0x100c80b6000003042c0402180414415101a203101800f03075100810010410308001003442c00029103102030100d5129010341c44018500b02c0794613100c0c07040030300c006494940201c41c111032a07a11107003003101080c3d081c007030000341c040c80038011800c02022601929425103a001a5044010040001403603943c9465444004040110411b141c1620081040c005044203003415510030340001da0002d88403c4071031804050f081c036800702d070742002d00513054a2130031b82c005099107500421400001c140100080c0200d0540c81003580c4940d42c1c0c003c01a29141003510060103240b09810901020250300000b0504040d801d40152034014510318003902c00f084c25206800220340c02c0c0040101052403085071094600460085440304015035580f480350101c3d1180030140794054000b9904038000030f540308041c0c4195603056000207600c0140c003220840c5030304080c980310001008446000039001041c0140000b00808103032080300c0500b15110004070341c074042c0ca81c0e80601000202448180c1c241c500103405103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 934878480 1250 934877230 934877239
    0x10509010c06061707031703040c030210020109060c0309030905030c09070f0504031b050316080c0f0409150b010915080c0901031d070906050909120f04150512010e070c02040209010e 80
    0x42e0040c4c2c0a99590417440c0422250560040e00c0725044034114029a8485e5502600d4290a1070960b03003440a000b0300000b081d0b080d592541542000101a13000700c1d411140507540001e158041400c000717181d082180d00481c00398005c41100403164603504d20940c0d00031000d05240d0400748019808981501c05c0e0f0344050f041c11003000c803004400540030755181c100c4500714211031440c103030901445c0c1c2c00c034298401c1c4400381e0b000c0807080d407560919100180f00e03c500140001451002c644811120f41c005156802a080d9034020030703845983c1203803240006d840d904505042c1c0303c81e44e07100604078a00103441918103c40106851403940c0c0700790010300011900180568034a604201070340c2e90340400e806400c90081c240301021919040100c482449850b80d54014110012001840385072a0f1009100300e50310601000b000c24030305035646032a031070103841e59201540c40c00c142800c0740c1c00f4203040c2c00955002110358240810258844489900d00c1c1e01150b006981d2080080161100000114840c2e0807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 934879730 1250 934878480 934878509
    0x20f0703050d081807060f02030405040501031a0f04050a0215270405151e0a03080f3f07090810240b0a0c060b04020301080c011d010509010c0606 64
    0x40001c08200003140d24110380702c54109440c1c510700f036060035240521120f200d500c4050b08000700c501c521003003103c8a1060040e6440c041e1034501140948900360402c1c2c6800c01d9081c5605000c00d221550260300c002c0d5899441118105603030740710b481d08909880a1302c556500d003034608081c803245d0121141d0896562036000100c1503800768921904690820a20551400c800280548680f541c0c1c2c3c150060024454040c1000352400c00344070481042126401400701c00c404000940c85900600b61342c11400f905989481c3d880c0d11010043d11082041c2581042d800c0c101c49c0d507218038008004541e61440624101d40c1c2d180081120681c44a91044506125620b01c43c0c0c0c22000300c0d400700644800450421481401d0340d0940c0c80c4050302441180342c100303010007916242078403a64142c4201d9100300d0011842040410014041c0e800c00c5c0c200e08850f80000720b04003243d6030004108034155030b03074409804030152032000282903405104400380c18000c3c1c1cac000130030402c032940e4071410282108510380b400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 934880980 1250 934879730 934879733
    0xa0909020703080403020c030606240417101a0a060305061206150f09071e090801111c050c0d09020a080a080a081f060c0f0221160b0712020f0703 64
    0x6181c0c2c1944e080c0c002d40140a4021124100403071400d00c5100041c2c0303041d294001d9001c1c8074420811034080500006410300001c210710105100c5c4021081402c002801104d81840ca41011124a030350484002303074610007000043e449190b0010100d44903414002103554460012420403000e440c0c555500e4000c08007081301441148484c410201000c0d196015500c45120903c58140c0c0140c1c3c8001c04101c2241001113407c10b0403408140307030009454280c118640d5040007600707584e95019000700c0c0030310104400d489409002c624502110b2401c100340000e0514080e040d0052050340e000011494031140c0c00f44c2507484681110004102d20412640c0349000c0c0d04014100d50803405038103000170036020202c1d50079005180c1400c00007014132004048240f401c40e06a51540740aa8225801d8004020940160b03480650710066140c0c00c403803805100d07004007040d5040480c00c0c02e00d0201500c0c50703070040c814484403100fa1801e86a002c0141c010004960700b0980c500300040c0008034541c41040000300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 934882230 1250 934880980 934880987
    0xf06030503041401020105090a062007050d032301060e0409080c030304110102060103120c0c15110709150e100806040303091101030b03101d0a061d01020f0f0a0909020703 75
    0x2110b07a201c54026142d240f4000482c242d50741079400c215240e00c9690400c010541540c440700c0c041442c4200107105160301c202e0000301e60000441520160040d18104400907054000c400a184c45200459514141440c948040b4001801a0030402080110111468032a0707401400441c0d046982c0a846480a10350582c0d2035108a070b0807102800d80f2540321029500005405040c1c0c0c0c0d00c080740c2840c4480c03407001100c1c551044481600c07602003014001901075108034003a40c40c0905a0f0352007180c07614502e0312034900025580100d800030314080d1448c00f07401d40842a0000e50b240000300d641e41c2c0c0c940b03040091414040da04010701c1402500140001c05405500994916129101007060b0096402c01501111600c402d0305416030040603107a45003c82c43e51103003480880c1c561041342d404c4002c060ba145410a0072000f207858036501c00c0c244001c00001c1c0c078004801c0807010025441c25034102c08400041c081c810340b110015802052802d030340b41c082d020060190070109001c6403140b00c0d030b00380203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 934883480 1250 934882230 934882237
    0x71401060f030c0918050d210e01090218011d041103070e100f0501120203070c140f12160318122103050601020c13090f0c151e0809010f06030503 64
    0x4400b05032400d15400c004010304442201003c2d040700140c0f01d0103810036400d03600003440b0320030311230040131907115460a0402c80c8140c0c415928450000621030302c20b44180f003c2d1081c21100300c000d80d408100104083c03103084040d4410580107150494094595281c40c0200e41c0c00d0300450b13603160103440c0c2c0c0400c07050096207240344505c0072007041c054044d43e2002407091244103402030300d0000d014016544607002240d0021500689245080ca1240c0d001e501d5000c0001040184031402c3d411805207110030030780420000742054150f010b007a15040818141c03000052240000a051000410a41d08d0042c02e0301205070040c000c8032a1035050050615040c6906518401a1440c0100198054003018823030300c140c6201c1c010607002007020050440c2080505103540c1844038145444400a4000407d5001501c842620a0b10f92504160501500001e92001c0303604500800207175144500030003404000074110718809040c080386940315220340f64050007078824403000050030072034000304202c0000f000b0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 934884730 1250 934883480 934883489
    0xc090106111b0a030f1e0b0603010c03050121050f1b010f0206040312110c01060b0309010b0913080304060f02210a110324090a0212060a0803071401060f030c 69
    0x56405420b002c2c40100205800388840d00e4108408042c180b00140850a08114450041c00b00056020002880790b002104544049a4a843d804180080ba00b07090203824101c24071130805009560400021540040039041a4013170090041c640c0004d100d800e11080d08852041d03c187c030040087c400c0444070500c035081d507440c001080e0700101a11584041060b901070340c2d05a80c7d078440010b400c41c0c100d0240000312101c0804203001c00030120704440910075a0010101080c6484c0c50345000b0075040d08541d1101d4000c0d00031110a800c000c6480c86941000c2c2800b07500c011120307240c0d00c590404a00403c0c2841c3c101d0640c0d03100041c2c114900892203150454030101c01100f2403640d0320b00c0d4800c0f00f910506900840e4190041c40410402c01e80405040b441d088800650040b0314180d50000703640310025924000e0301030b130024860301500031540c040750780404190b4038115070a1401d50400d80c0c07880f42c0e20014100320301e000c2094071780400a42101d8010014000751000e020744074100030340d2440d8540328 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 934885980 1250 934884730 934884733
    0x50705221401111c050904060e0406060503010903020319052104060e073602040b040801050604110703030f060503160e060a0f05090c04470a030e0c09010611 69
    0xc00115079031141e040c00726510030200191058000c4846024021540d60004c60103001c4103000350409900c851103050b004080703160120181d4101814460301710340c52500698000d0341004404d03c0442d8000040382c42000c802c1e845d440448107840400c0701c02e4012008003c0c2d10601184030340c03490b402802c11030780c09a4064601040345240f000c5007d0758036412886460650300500e9500540d14650b0a030511070101c00d14070403690356004401407012680141c000072224607000c5070a011000f024880c69500c00000e40e810084420780803002200ca0080310310041c10541c442541402c0c18126030040001060054110790081040901046404945000340340c440145500012030518000380900c00b19031800b5039010103241000c06010030540000d1484864140400c0300090400804222403507e2251482d074ae0f4807049401c5501c0216900448040c100b00c030340d608040d003401c0c0c0359800c5030880d80f02d904001501e1481d0b0700d1880e0502104c0d811240d07008400b00c00011300c0907004006104070103400750 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 934887230 1250 934885980 934886009
    0x70807030c1407020414102103050f0d0e100b120619020708040f0f0e07030507200703020301090c0501020f15070e010c0602180f0d0b0a05070522 64
    0x1202141d10404400300011024003558201d20040c8008002e03035030001d131020480720250914552044000d071071030b803500040c180041081002d8030140c81841075641d03c500c4000c1550f514020094001d2414a0b08281000074100c0d54600269102408600d88941901c10220b03518542c4130050511603043e0b0b0080d2080d800c5844003c0d00415064894450143d8002c01d2848207000c41c4000c0d08075081c02c45900904100114005803000e40040041c51210591074020381001e000019201001c1c1408081c942000180700381c4540090104500380c12001d1403000074203080b4001c03450000c07030fa40065055440c02e10034005002d840804201039034002c0e0212070001c00c030015900d076940540507444920400703150101e02017030b206840295405c41c05150010843c84161111001ca900859050b072026248410840b11800c211388143c030a90022a202a1513150a80700c650308844000d005201e41c5684100040c802e5015200b960921100308a00b9120b0880f00e020101c00c081da5400340201c2d04a204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 934888480 1250 934887230 934887241
    0x150907030917040f03080a0203370302030705160222020d3c140c07031e0c03051e030c070b0f060a090903120c090f0812040303260c030708 61
    0xa401c40d0200c0e0407080d45245840d103162540d5580b600616041000c6000410115101554008007100b80402c002035684ac0810314008200c0c404025120030024180180200140c1c140c1000644200350703120721881005032524400180f03481008040515101100c0c1030000512070140e000c3d26048114903400c000c020414107401410480c04540d54003804d10310954280b402d00d0508420301104001000030a129000000005d43d8440490702400c2e40741001c540301c01410b500400100f0b900d95884a040685030080c1e00092855030540c10103400d10000140400780310645180800c8400f1700c0c0000503489041ca140440104d903c520000d40e0700d48011404078100c10400104680503120003031204c440b061600820300040c012101003134081c041d4001f11a019826035002c0c010040341d81d580d510118a040c240c2290b210409500403c002d5403281801c1d4460314040b4040301d06898240c101000b09545116000d5070340103401d070412413a0500b02051004c0c0b2118038011b94014840c80d1100401c90751071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 934889730 1250 934888480 934888523
    0x1030f06051c08130306050402030c09040c0b210106051c05072c19170c0604090e0307060e0706091d15040b06130f06050415081509070309 61
    0xe00460740d0007103464204480300c0680c1d4120b260250311076103e0394208440213190368007040702076200b80d41c0350b5154020481189030501010511140882d1076500c00d041903100c054400c40c40f030142d28004c920010301e4061604178a64183c3c1c02604410307050070990b840304c070014400c0e0008440c83c3c3c025000f1a5100e424282c2e6400b8003803058481c1d54403102e2100101e00b0020101c14610080c0c035109485944c2e10025880c2d40a00e44070030b81e640784a00c1c22082c0303003800e8860513100d003801c01c1f5490f03000080c08024641d201c600300e40031200340100200300b007854000c51030304500c030b0040000d0040d4500310029005810210390801200d480da10b80300c0c0d0f46ca940300d408005540c1100e02006401615100040c52180c3c141c1e0410385a8201810006181d41c1c188045200c4c1c1e4800c50001c0c450781031845007008440340502d0040c0c0503103680d140c001d0615142c131150790701541403981240e00b07004128001032a101d00075151450b40303040090211070241031800000d4000c2c40f100c00195442d04030346840780e4a200d407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 934890980 1250 934889730 934889741
    0x30708150606091c03030e060a0b0105220f0905090d1b03210f0605031c0f031e0903030b0405061504060c06060e09030c160510200303070e01030f 64
    0x4003034a00800030703620700007000b10661040050340da01408800319490080356000c10310700103920980f070001d10300982d07135040c9151007001481c01d007120b41088e82550807a60b200d402d07220305418582c40160054100c00c1103200c6001e41d60001c42000386410000100e0418540046008254940c25140c6a1080010842c0c1c50200400d05c000c00000d21411580080e2007070304440141b68080b10090102804003029038141c07088040c1040000740c680b00213200c145014850064040303108400800028190040940701c0100d40d0008c500341550b902d5910304842603121040d10012440804001c0a240d030300d8080d009055514200b4099890003000070300b1810113410766940140301030203031401c1c149440f4044945103080201200c4dc1a03d03080d000401614202c8524040c0c0b00c100301658030360400c02d20041c9401103e648440d4648240002080b084d10303124014007a4010501e0a1200141e140741080c0c2030445100b00c640d85444000204554140d01403a61120050241e905200c006c070380959030410f0301e5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 934892086 1106 934890980 934891003
    0x504090b04050f0f0709030503031015021f15050411040618180b040e0616260127060906030b011d0103020f030102041a09030708 57
    0x641901030a03225090541d03003000686080d200000803104050b0100000c80c00031004a2201d610a0780d00c8005180c002d8216a40e900f00042c03050f03521070103442020401c2c00484400030380d02c1e2002c1107401d40b01c0c0456440007000b05c1d000c0c050000170a0182000c0f00360800550001941d500ca40c0185508422030060349600c5e1441d18170007902d007000d001c05800706005003500902c031980200e281c01140d00311064000032031503c10400715000f000c01c840d0803a2540305000401040310707010b0380304480c1040b6580d115014003d986c0200040ba8038040072018100030140014007030b1070400d0009024541d41294900c101c08089444402102c0140e04040001e64988109005100e102c030071044c010030710f803210000d250b0490340680c41a03032018040240305406c00040c24000d41e400f501030740c024241440010113402400b45d48106c981d40886c850700c1c000d00a10740b000400d040701280c40e02440 = true := by decide +kernel

theorem cover : BRFrame.Cov 934712230 934892086 := by
  have h0 := BRFrame.cov_init 934712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 934712230 ≤ n) (h2 : n < 934892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
