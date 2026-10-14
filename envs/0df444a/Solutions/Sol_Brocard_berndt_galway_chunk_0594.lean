-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0594
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:38:23.752494+00:00
-- url     : https://prove2.me/submissions/610f4d43-f20b-494b-ab2b-070fb9177c99

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 106654676 ≤ n < 106834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 106655926 1250 106654676 106654699
    0x6031a070c06020d200310060c1407030312050105100512070e03190209010801140115020c06040e090d020604080f07020a0b12040c0b090d02060702010507061e060503011104050f 78
    0x440d00c2c8004d10800080800009203010501201401d18019914014400005000780302c21411505d000c40304541103402c0040800d030b0a40307050ac810308420040c1ea6444d007e030341c00001c18075800145541c440d0502180420080e82c85004000440304220740031000070700240321000e18005805001600001e40b820030b82e41704001c2d0800240b80c002e88010304606129284020350442c28074604090242441000034088250184605400a20148100858048010043c1280301e00031f0012103143c50014104641d201d44850518074884025640042d09208029659a42a202180340c0f40145d5016000d2850321041c0b0070321280c00d1304a9403007640e2100b0140c00000d181c0984d0030081c001c0d0003901e11209098a018140742c1d50400c0c05900802112008010000c0340f9980d0320043d0065036411a18203132641540c0c00104e03054050f04030020704851508160502d808001d81032070300c840069802c203120a680303c3c1c0500d030030f0b142c0e103240d101c405150601c014483d6103001c264200170b0b080082d24404006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 106657176 1250 106655926 106655933
    0x501050307030e060405010b040e030414010e0117070e010e060306090a02030c0405031f060503070807120303060b13170d05031602010e0604110f010c030c12120c0206090c0406031a070c 81
    0x28040c0d804890301d0b0f41d078010090035805c0500440007004a03083c091330030b06140ca454281c102c0305070740c9694100450112140c8090b07000d10050811409020030341140c40c0351183c80038104c2c000e40b2000c02c0c007045180c600724030140740480450344103400161004441c0d0f1200a0740310081e41002e0403000c4861810f00002c034a945040145611850240c0c0b0081a40c00b41010b86604550503074024030701030b8100c2203003482001c40020740c40085808441040d0781e007030120305040b001409a5000741c50301c100d0001e188401201c000d0030643c2540c503016a0141d88040482e016a550351013405a80003088051000400d80500910b229001c1122400003092600d1404c0d1024201901120200c8210a10310002185400d06041c5803a03024000e00389a1405202c6850107441000500401000b0344000c0a2004211388240130702c60070003015041c02d0041080d200c0b0003039143c15044600006903c141440c820480c134107030245038101e07900400d4042801e001540c1007030641100a1043c0d060001054246000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 106658426 1250 106657176 106657183
    0x303020d02070c050f0406030f0803040203030403140d02070e010f0302040b031903050d0c051c050a0b150c0c0409170d090803010f0602060601020c03030904150f030b010509010b040e010501050307030e 88
    0x5980710f42c6110807410f0400d03003040024100e101c104c1c1d00841c0f804c001030000507a1541f2a40c0290b81000300710f0345954440c40000c2c03840c0302d40c0c0c10081084070120300d40914003100251071035110300a502a83c07001900c6410310490104240b0942c0c41d50040d2020410150901c4d501c20142d0f140301505841da1507020b2000700c10307440d01ca0072003280003503800108109105c045218030502c0010f540703000b600c0c1c00c5400500018580342030a0080d0069683c90105500c268190303c00345100b01c01801280c10120001100071158111001d035201038061301621169510302481090460b690060024a8894184060312002c1e040f203914490700070340d126241d1002c2040c0001850003003200380c6000380003909000c002414608090704907810b550183d41c2202e8207560100684041c080c082c1c6001400c45604c0c80175005120b260344c00381000c000a040040184040c00302181d040e12000e0f00d02003810390341c44c55542210b01c214800d5501954181c401400190b2080008580040b15498041400780b48000708030709 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 106659676 1250 106658426 106658437
    0x40215070203070b0f130803030105090f060d0b040302010f1401050a03030c170711010e03010506090412031d01050a0c0809030d0b040e030d0902041a0a0905060118080f2a0d0303020d02 81
    0x580d40e4040751b0000644e841c09014409814000051400c55141002207642c64101038129142122008001202c0c0c0d206c41c001d4206150700700c100944a41881c2c10040d000b40143d4000507501030900c0c0c0d10400c286400041a812200058800d0b0442490350714212016594100d0440b01c502d402c404500b1140704a030060700c08030f40945010b17500c00603004005844003c800e40c449021742d050000700113042e0b482d64501584103070401d00c50820641604070440c002c0c100641d06244040146110134894081540030900c0341c0d00c481e104101420103580c09582001040700e001348240d008000344801c0001540205040d83c00241c80030440c1c40c044403600d401c40e005030a4400c440e0742c2d101941000e5242c139004034441204500a0303206140d08c481d0200381406018040e036601c03e0780380d00225074543d01c83c440c40481100140600300540c0c3d02d8120b810b455910500c0c03242124440c00d0440c00b11480142c850541220b6980130719005403a54200f404a0503814040c142e042c0750f800e0000420440300ca000908 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 106660926 1250 106659676 106659697
    0x20a03061509080d0815010c0602160c0906080303090303160207051804060b1002070b091c0803040302011b0509090711060c120109060b16111306050f0108040215070203070b 76
    0x31035042010044c5052000d00a100c00c0001040504c0180070b40c071080d6451941003868201540c00c4a42401800fa100b07c014210500000c01c03040390a00101148000070340320110401d01c0840d0f6140e078040c1c5c0c5c0380800d03109a03045030000c002198008001e1800c00b500e54240780191210340d5904e800056030107a10755503260361404581e0401013080890320624420007070460340105c0107912040029501c40c2c660180c0c40c04a8000034030b81e0120b64440c1c00344004a510040170724440001880e210700160026141100550b007082c01c61048040003045000c4500c89a0f92510b0400030100b0801040e40000381100301844044181d10144a0301400410305c1041e0340d54020359900410795410448a105a000d191a0340c5800000e01c19100004210345030b01034503042d001c99260850424803e06405810300c21382c000304030700c2d203000d4001d581c1e00030f84100c420442c2d50148884c125401540e110710215002540b00020242030195420800058000d40e40042c04481c5041e4582061181303683c0403034081e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 106662176 1250 106660926 106660937
    0xc1a07030f080103030801090e030c06010306092009041e050d1112030408071b0f06020601140f0306040303051906090b0906121209040908030420040e0a06020a030615 73
    0x10040c96004082200e001800d403520700c10300c1d071544c2c400400c00c42d018080c800e0304a80b14000b00c01404003c005641c5a800c4581c2500d250b940d407481c00200030706003002c048503031941e511450304100f86e0301c10341001d4002c0060200003030b40e070b2903641e14820300f40000320348818a1000800031000c200108008556240c1c2a00c0d59044c04cc0c0c0014038030300e80030b440154819240d00410810000034001ea0a40d07040c158003008580041815240340004002250400d104400e480100080c0a44e40091011704952400c0d010941c0110090184441c0707041440c41c445d007651007500810f0001c0d100c0c0d801182c2c48064030b5491140c0f07000002e031711760948800360300541016031121280c03166803504480715908500111284000c2440c120707249610340c0c2100801c8a1040c07070220301c900260b1504c0d04450041a03002885075030300c2c605440c201c0350f1030100e4414011510f08103010258142441c2c81000c101000210007051034444503034a01010358043d04c502070401d601c40800203007007003001d1102c00810745076403142d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 106663426 1250 106662176 106662187
    0x31403040f020f06180f03010b03060f04061d0a030828052e0603090309030c1502060108010b180402040902031f05070503060a05090603070e0109060f0b030108030a0c0c1a 75
    0x400c091000500f000d14802c4404025a601e030020300c100c1c2e851201d0081d82c60211601178600060300621041c402a60107016410070010045403000c40f50b4411442400b007004280d441c01241c004051501030301d08019400641e07080046070190000740d03030280b607405284060070350681c400120100300346201e1014988582c1803082c2d6040003405c00c40700e2896180000228100c1c10724041001000d40b04010a00d03954855000038140700e046000c0103103410442030410141d482d00c01c0400403080f011110014001e1200106510f4418050b10701601002806042c007844104545051640c0c064012684036030303500300c4440140c9040c00b8400000c0c03d041046032055040031062000d4400c01814242081400c0080085039075440720581c06441060f906408903603290300110346010b1442c1c02004079042000e00003d91107440d03800ca4019940005a0081250780c0c81c1642a4680000e026242c5983c1060020550b0103228014540710a0700940000d507816503145100391401c80c3d21030f50140f002100096 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 106664676 1250 106663426 106663429
    0x90c110705030c0919020409110c0c012c030a14030a0215011d1f0312020c060304050319140705030a03180308180709110d05010b040e04030309031403040f02 69
    0x24100c000e04058020f88691038440001407648040100b0300c01440401c1c400d046104801c0364199005407800710003c0240407a601d001d501d0940203402081a14070610036201c569500c0340300c2c4180030300f00d02c80c04000780e0903440f2101080440c2000e01c2c1070300752240c4440320003c54180d40302e080a03804d46c070020716607030703213044a0013800d007008040b101100b130865600401c001e0f00700401854068003820396054540d11040601900c0c10031354400f01344229a00c12021050002074088203295a00f180c00303c0710080492014450280012140038116400a0000f50380010001c40c682e01400584d140c00807000300c5a500103181070300326103001d4407103034800b1601d2540140c0512461160255070404a4250344c40c50354024207001d40200381c83e03e01440505e9010364000b00700480c9015280040080c42204280c1d60b480000c0d40000f0340790030b40d0b64101400003540085000c12101600c0402000002c0b0313a6807610241c000d8030600f402103040102d0103141116101210340614000c510500022956450500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 106665926 1250 106664676 106664683
    0x30c030a0b0603010f1814040c0923010e0402010c0213060e0a0603020607060b040b061c05060d0507031106040e09010504141b1e06030720070b040618090c11 69
    0x44802e006020400c0144041d0700c21608450403661000800145000344020b401d0182c05e540da0201c000b80822010302040007000d00b50070301a02e180c0d19040042c150320341d05100000107404459007880c1308110043c40100d5003c401264090b0043c101030044008030b03804a020002170030307a1101d1481da9101e003400428080c030a4140c22502d2624240a92800c50700020761500c60840c00404140e52000c01c0030840e15145c0158010303800c01400c803511341ca1b184040501c603100f14002104020b00e0305000a01d0b624000b52a0803070190414018141c150455440d4003411040c814a01da01240c180400142c201001221a01c240880400440c260030285051041e0700124100d44030385811400c05400c1c0c07251102818081401c0403140d2502c0c0c4000c5465a4081c40a40c409098000c9800420081070b43d07045844c00300d001c440d100070b00342d140c2401821286c891202d0b002d620f01e11a401c00040095510640014800703000383c1c001224801e41e14800c0e142150701c4c911920020175070a0310340f2160040e090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 106667176 1250 106665926 106665941
    0x509040302030a170403050f0d0e0718050f010b0703110c090a060e1305190f02030607080415060e0103030509040f0606020d090803090d0f0516090f05060102030702210a08030c030a 79
    0x207000d04d40309030400e42e4001d080d0340989440c1b08d1825101148403540602d0941040e032484041c2002e03034042c2c81c0c591078100c03030800e081e003100b0b600c20b4104800314074603440745240750b4100c46000c0070041c01c0c41003540d4202c408045525142132903114400e030106d041c2e950683e00c42c0c010150f40800290880c0f0f0a000d0040c0b58500426070310030588041030610110390081110b5501034804507400030300504906d0108490300c65900c000e034043c82107100b0016607942004d00c90340158010740021071044420140c1000383e0700103001c1c081202d606c140041000070b00820261401d0130004101107161009441c40504031070065000707a005a0240c050100030750341046c881800b070603440d0051403a28440c0c1d0082200e89541a0004111075850341044043c4101804404000400d151603505001c1e41c6840c8038000d0b181d101c070f034204414039200c0450700b15030000088500d0998042d14100201d0844600006241841c0030180514025004198002042c0e00b009521070140744040b10345038100382d19480b007210000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 106668426 1250 106667176 106667207
    0x2040f06020115090513060510080c1c080706020c0a0c03120509030703080d020712050406030f050402010e090402150d0e06060d020607061e0c03230106140c070509040302030a 77
    0x103100c0903e00c00e141d408120401c0d142c1d004030100c1c20b510784140c90303641030b50202005042c0b203141c441401600000d201c844012034504600702c0300e103071407683c0030050310608a1074040920850010ac20f000100040054141d81e40286401401e02c0342d2103104038104240481e0407202c19481c00000d108100082c0d00041600055140c52410032249501195403504540030281190a001c51303034018103415501200d5403142d0107030700941c0d501840c1c0030150441c4c1045c0a00c00109003000907031108403070244141841035070140c0d5004080107240b820b100452101800070b9810138a07601e0810000c142d83c4004181c401018440020280c045405d01401c0c404007402041c426501c0030307100000342e13583c802614110340d0404800665001c80340b0360b40804007500107007a281c00c1d081964000c2190b806900c034900780110030085c000f4104000c1000b0804000c240070350700201343e40e150140000040d45020709a43d20b8140e0445134170a0329840050401e08003101c0480040c3d10000b00d0f402e00d540e00c0b0740e002081d1800d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 106669676 1250 106668426 106668431
    0xc0806060a0c06090c0e0709062307060f050903070201090b0a020c0909030c0601060c05010e010c0f03020c010608070e01030510020c1005040516030302060106020d0905061204020a0b0c0102040f060201 88
    0x244980014614450451a8410810250100400d004031980102c0711241d2041e0f21030020369030b5241c0242000f01c200d5468005c076200c014000307041e9000310000300015502007030218160800c4000c1c05503a4010078001e65080d6610808a080211188a83d60081041d04001c6844a10380c4c40014251f04035a008804980e10901520715a5500082c02d010581801c513800c00b6603907500440c80b4998007a0340c42950851250200019038039410003460040103000c0c400a00c400c2600c2103242c1e003603441040e42440001d403004103217144644a60302a24404c42c01400108503255a03c08461911000d500a4001c42c0007078001001001020850b100f0a120004001d500f0050700f40f0504d03071074440d12042110440e03118800501004010320862404841c0000e004003143c0d01c90400a580e61002d0103030b08050721601a81070072190090b080003088500090015251900c0f400240c0400034019200f2600700c00124000702d40d070f110243c003501c40f0b03010315000107803101d06c1c000c0384d041c006125901040030b592 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 106670926 1250 106669676 106669681
    0x100306050a05060a260a0e0a031e051e19020d1b020d1e03120b0a0519080607020a03030c03060506030604050c09040f0204031b060f0305090309060408010c02010c08 72
    0x721440105011203408440003a04c0300344601042d910382c0b4a81d103401203450203c50f520904101c44580702c5010b2240c4c000100040c0c40c40301d4400d40e03071b500c2070382d00500400d18114205446401502d80350700c40a000780f03840303070034040d1300d0300b24078102002500d50300170010000c03c016403200d82c030243c2003908094920003082d140340c01340c60180103c180e050000c1240c012818048040d511503280c0208101e038804141c0c0c40210300c03a00d01c040307a99107a2104034002190039180c038448120a001d01040d030380c001402442d00d20705d0300c1c0811400000c0c280d10707070318410030041e4002082e90301805130034820032184d0060264441c44d890024111360100c05c149041c035150a40a00030794460705e00784ca0b07209409580028194403001a190958051010402c0d4443e05000203c0140703042a0081c201b260700c503171441825590500802854038000d1f00603900040e10280a409a040c42600195042403800c0c05403440c1c5907604020604582c001c2d0480c0c05280c1d151580050003d60903c150010854a4500034140b030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 106672176 1250 106670926 106670929
    0x40c1119120c0503040e0c0304060b030102091509030a1a180714040c090b0f0d0f020a020312041b030b180708030405010f2606100503090a0204050c0d06090b10030605 73
    0x54050320340440800c40307100e40304410443c04008403400b400e1886900110b929101d0340c081d002d40d004030340865010b0708129600c80a41414020f50300200002002040e4421282040307107407540082400a03410710030029204003080d60100701800071144034821034518078081c00a1f5880200780c00c00c00100750302000c800c1145040f030400c8071140e80350171140880c0e012805003085803081c040e5007040d6405600068031640c000c000400030852251008030030b0003040b4183c02840102d000f80a11140903800c1000100e110081000107180d119200307450980c80f24102000248070f2203c80d810403190118120705200302c015082d141d120b000c0c11443c009244050a00415684030b010764807505040c071a0b820b50780240075029102c0700d4081c81d0400004139900190382000c1c2c00b025010781d03030b06014050078850309411502c1402205d10522100008100480ca07d6007404028500180307034407540d01081c80010348164150003004001d111145012504404040c00c03c0035081401118000707061404404203d20b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 106673426 1250 106672176 106672193
    0x20d0f08160507050a0b190f051302120708010204060309140105090c0625050a020906030a0b0f041a070807030509030403020a090203070219030302130501050c0303040f030e040c1119 80
    0x206896441c025840303040f1840d003546094402d100040c805103003002004003017a596646040d5070010355205005c3c9495000300c5000305c41c001d580c0711400990307a20611000d402c0086126108030048421075250070b648600c074508a0b00260040c3c00020313192490907050201e21440d840c040c0341c410000300002c0c00c001380c189a070340c08003648090041c480400e40010354020200d841124481e20309d4071036010310903881d00c940c662030300723020481c8a6401d600c045566030800290071200964058108503c1c1c0e00c40440c0307040782c024014001c40741c1300c03555982868607644100000b4005c8116407503240c2c407420b10010103400e13140003c0003c44241c0c070501003003002d03039960b110260440e164080d00513503035298100d049040840c030740190340c45211080003840415074954001d05407024007a2651a1281d20340004507030b40d00c606c1d20711000c50361080c0040f602180c0f80707900302e0082d0340c4642055884416180040380503200c1e100910404950200140100301405001401d4280d0850041e11911400750b512941c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 106674676 1250 106673426 106673461
    0x15050f0f0109091802040e01021c020c01020f0a08040b011406070201080a0b0603011211030a030903030e0409020a0f0f08010c020303070c0f08070605071209050613020a05040507020d0f08 82
    0x204900d80e1000c192164000d074207840140005000c284907016540d2400e00362025a000100e004503e090216500614184280c0d810300c4c0908455901d101000c0300078034040c0d08410443c0916560070000c4207010401c00d0300810001d809610b4030307081890982000201d00c40140e20500704026440d94441c030960303803441224059a82400c101c1d000e519404981c0004020218605820072400000840e404c1c46050b83c90b40c40034854607041c039483c848d0b034090544400380c4080c02404203103104800c1c000079001e201c2450004001620001743c04805400140c07102d649640302d40340140c0c19010030312040b00c0d001c0d145c20140020f0702c02401600d00c0c48100039581e01c03000300600200900c4060060410400303882c003824280d001004240c45004a041142c01800152484000b08424010824800d03049004854625400c98003600c01d41d42c80407044030702224580c0c41240d00c00304041d400718080da12441524003c00f1240d00601081c28031160103001a00241c5003541070004010400c00107003580d04a031407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 106675926 1250 106674676 106674679
    0xc0e0120060a1802040e0f061f1a1603030b01020c0102070b030a2c0102120f06010804080906040801020c03040e0609100302010e0105090607060b0907030c09120309050303070b060415050f 82
    0x2074442c080072482114407001d0307034000c1d4018140980d00141500c0011001080c0ea8951f05a0300c1e81c0c1c4070901c103d0060504085614100c2c20b000d4001c000c10000001078284005402c0340552801240c11007901849424190890110f50390380310310341140d41c0c1001a00341010081c00107100b00f504054544115001c0108254199a140c0007003140351101600714010359102c1415004040c0c000214180c045d401144420300d0620403000027420010980e00050302440049e102c80c90705450b180c503445a940e20451089401050400c40012004070910003080d84001880145846504001400b5a00000503010034410071002e000d028000199805000840fa42420081c0c1c00d150480b0060f00c1c203000381c441080e800103011448009000303281d0450641c1c010200c0e20340416a030f0b6034200b80e04941191000d40002030064005014210078404150504c60181c00c02c00a45950340740003c0c9190300150080716010001350a00450382410b01038a0310300444209490301d41e0f41841c001c40d48410042c007015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 106677176 1250 106675926 106675931
    0x302061611120717040f08010b04020f0a200708011a0904050d12090803040b072a021203040f0609080c1806010807031b020a0302060606030f01060807120c0e0120060a 73
    0xc42000754903264800084c1c01400380c031381c6a0742e5a81442a4800281c401c84455509282904c1100e2034070748215121500c400300c400d0301b440300c6a330007210002d07030303000c41085800e411009110f1460b4082124100501201d4000325050051081025101210b8103801d07002d14540403d020001d400842c445c2000f001c40d00d001c400c580071042d0410054407007130201401c1000d0000a000034441341c000807a00c990816100c1a0000c55501c40d41c000388802d4054407080c0301c4a82202d0b200515000c108107101ca07802008a9041a44070b85980501d5a01d50b804074001c12803a02c010002c280050001c0031450320101c0740000d9074203202a4a006074080108514100445000054000c0340aa03204400b0b0143c04041000d0801d07040201960f51819000241d015100304000500e9070725020044078440c00c00300030303030b19850b904e40a000d9401c507402030710705e030180412900c01c0600f08410380720315038150606654104ca80550140090120325840d01021015480290010381e0342c0c000240d130035000110001c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 106678426 1250 106677176 106677187
    0xf030f03140c07050d08040c05061b01050a0c02160509010e0a09060e03030118020c03070209090a08030f06090703051501110705131d0d020d12090f030206161112 71
    0x32801071100303080d4141111009010310090751080000761074100d108200300d074030b00e100d07000c0c0641c1c060300102c4006001061501051100d410190040e05400036044d0740c91011107a0030704501c2c02d41d04119401c1d00419910300001c00a10303410400701c1c401031001c5249490f550f0401000c40e8241105004100b854064400800c0039a99035600031481c05810400411424512180003034480e88284900c19032309601a11240d41600755100b11081800d8060003503203003203010350901c044e52000401c43c8009005070f4010300046405140258032655400e406980310f03241400402501d0b0401a080d141010b14160801c4289018030300319a00c808407d0070300700c3c5561218420146002d0580d001182c002c08a084212440300064105000307500412800c51340c06442c85c0d03400b43c0d131003400448640050b40070303030080303140c541c041c1800c09044002c11402040ea0605501c4510381d0011079981240164062001c01080c44102c00c0d25008451840c0740c54060902140c2d005560781084002d0f443c03008400080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 106679676 1250 106678426 106678457
    0xe150d03080412090b070c08010b0103021c09020d02120a0201120203070e0f130609060e0601030e0604080d090804121b0f03171209030d0c0c020603150f0a1806120f03 73
    0x4058010402c880701700750b4035400c1c0d1600b024290100d1058a40035824141c042030658001d00a6032840f040c881c22089041903030b2150341003d01040001a07070410901c030900c5004d038030b40903501010100c100c4000c100503900d49c170004040c18201c004040c0000c0c81801844521544103100c11700281d000c540c0148030842d800300141d0100400441607110750324203000041c6041e41f94209404460403c1035000705c070b90b550b50040d01603074100040481c003034000c480002c0c0060000b0010b441c0c00d2100710313030005460b941c9035900d904030382c41904611500e11900b44c805080102d0721240c4c1c008100e00310308144826192014075040b502c06404010070510311101d4408102e11180309030303070750844003c018071042d060081029440303900091038082840c2c1042c101c04d609901460040381b0301580940303c3c0386103070358044001000c04001140140d0101c8000c8001c070b42652901c900e0300140100380358040c441842c42642600f1103000d540b0481440c1d82000c0103102140071610044000c6800d0308020380f141c0070890 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 106680926 1250 106679676 106679687
    0x1030533030609010b030f1203010e0709150306030b061801090207050f03040f050a1707050d051906020a030605040506060706050402060d0603030504060305221104020903070e150d03080412 83
    0x88120740c041c424407040000c001c50540154100071803e4060310200c4a00c8100181c0b104204640c4102c1c10b1010401005003020089407140d01c8a8240f074600303180307516610640001c14440c402000006c0c0c03109024014030000307040f096006203044510313182081c003a44e03a04c4c040c01c0e814444c0806059001c83d140d010300c4001e03c2041c202620403020344e0355441d1640480340141c071048c02000e00884040c1c0010030f40b100c050342e8250044400d08020031030240350404101c4203161050044500c1c1c02031030482e0201682c3e2040200c00b00384100b01c0943c03035041c1808000e04031060350340a24404c5007000d050100341d845400898101c035130440d1011405139036030700200f80d480c80380561089080e454454000305056020004d8802d80d00c00341d809000b141c0b18541c14124240e005100003550103440c0e47d40d13000061030003070045a0918068000b40c1040e007281c0020b81045140da014209071004041000300c00504c00c0360400c1c4854040310a29007044840e00c0c000d00346000204010120070700341c5d150001c141d0044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 106682176 1250 106680926 106681021
    0x1b1103010204170d200c0d02012006070305060609010c0b040c05100201020702010e0a2103090b1b0d020109030210020d2d060e330a0605040311010305 66
    0x1038150644141050107895654224084c00c040058104840034103071001200c800c0c1443d640384070003000c040040008014003070341c0d0000105e05020340340c06011641c0d031800441201b41d0b0096809031149160000c00502902c10003400300d4031504041101d542541c1e04041e10441044d0045000512961075281140901406401c82a81b000c01140c007006103a03415002419114400c2c2d031990803080861003030100d1100030b80a0940c11200b10200b0300b050392011002540701500034540100e0b015078403c021b2602e603000100038001e00896000c25a850402003104030012880d03440208101004c0c0c3c1c60003901d401e810341440c00c42c2600046c2c012200302c10340d04401040ca110803000100700e02488104418034960110301050309082c008006591545005010b209044507900d10307412000700310640c200800304100c2d10300b211421080c18007030754840140c1c107000303031045e91189960b032810f50400d80741c0d40010b000040d0400d4100300030020081c0103110100c084625140358601480c048504282051408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 106683426 1250 106682176 106682189
    0x9020f090a080304060e0904020d0204021c020408010606020c12120304030c1514090606010207060c050709090c080f0c130209030a050d2604080702010507030c0b04031805011b1103010204 82
    0x40400100c2e4240c000300003002241c2007500e0303901101141c4803e009545000300d130040e60103925a40e200f40581841d8004291290001d4001d06445009842403022600b050f00407964a84d500c900030b0101540400c80042d0102040b134488000c406000803007503a900d0b441000010040000c8041410540204096040e440d8003080e52501c5a802038886802403040840d1207003c2004100030640107000421028004d041c180d014101490400a05482e030384107400e0104d41500c00c2c0d050014006100744603455030944102c07210301296240003441442c155226440c02c401d9040710200d41c041c5e51311200c0c0c60741445070907440980c44142075070000b803d250800c18094200e0003020884010713140c1c0004402040564000e4141050312410040c88418070104c800400c400c0b000c0008030003660160001d0000c4610a161160700d5543e1503407010004903044c0c8080300420403800c210303682c011810101320041c15080c0b8103201d421b941c0103c0b1040009030f40328041d1103401c03002c014003490348003901140d028200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 106684676 1250 106683426 106683439
    0xb06040b040801020a0807210b010c06140103060b030708060f10080613030f0f02030f0c0304030f0308090c0f0d0b04031b1401050601030b0a171f0f06170709020f09 72
    0x342e4810982c080e600480c01100003509150015100500506903160420300780708079550402c15540c0050000c0c1491410300341400f400403840400170f1214005c03ca00d2858216425007036515614141094074641c11803e8401c0d085408280302c51309001603d1544409500c0c0b401c00c440c0c803400d00c44101001c05402c0040c580c004c42d8200980300c80e41d41a100c00d0244a81e454055510b41c9203002c0703500054100528005800c100140d00f80040e6000183c41c1e480300c4181501c2c81e007a580d80da106500401854200d0120760b0040401031080c03024040c2c0c070b8494809030f5030b2003241020180042e03081d42035001c004050fa2030000105040c1407191046801030001c1d5004400342c60090300b8a00001000c4600c50740066080000003074003544240100c1c018805d001c1c10700d0300c2d004e050411f0214146a001381d0313103505205010000851011580c11412640c0c050100000c508034002c240905036101d0f41c00c4a0102d0704507890340c3d00d5038a40016000c048602010700162240403035200310300c045c440c0d44440380d8440c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 106685926 1250 106684676 106684679
    0x141306051804180f030c080a032003190e070807180f0207120503102d0f14061e0a0c060f060806070f0c020d05060f101802030a0b0a0306050114041e0b06040b04 70
    0x1074068ac0a580501a280c60500100d10744c0014410340f8070044600d0148500081e003880e0410026402c81c0a940e60700030155031100e0f0300c2e000b0151400750740758058226011118032040a8049921801449010703419040d8540550364032061207203038030154494100180080080c0ba0503c0d60b00401e000713000714524903e40740302900d01e0303035840000c0007204100b40e00011100150300041d502d148012070342c514408120b1700e40540c0401c42c05401c540514049070808054407540c1c2c0500328000e0041fa034098a030202d1100389403e055040311842000001030a203408414408a6000a25694407202c0f82c6015244000e032104100d54151408100a4000c503201180404000c00030079024481d44848444420030740e62019511032014843c401d2580d400e070070f01303001185106540c0003940e000c454440302140107018600424031255460340103541361aa241c006100344508003072001c0140380d00b103401b4040701004990040001441000124175141d4800c404400d94803003006403401428a01d14594035207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 106687176 1250 106685926 106685947
    0x60303030c02120c060105011b05030a022103070903020f04020f0c011b0f0f080c040806070e31091e05070608060619141306051804180f030c08 63
    0x1c050103207501c409405626032510800d16080c050b507801d420010000c1100b646448019188400f40c034015150440054010201140c001c0004180c0700d09542d00400d1782c8126071480e41d0aa00e118640007440840410034400001c0e404100b00c41030b0b0790102d032801c6512034103000050082c032072500c00c0f0084200100360821400d5041d0b00c803600011043c1103020079902c86020441e414299406e400000c5150200859000340c4074007581ca501c12100b031092031501d6103401440380b070080110f405000044903500032841c9814040c0a1078000751014600d903010909401080e33641e5049000d003511001d55800e8244284000c048180c1c034091040e90307002c15240c009003865911110240500c101060a88000c03402c5030500030200c44501144041920215005000072900e80c103903141c12041c00ea0040c401c8849540d03100c00144018159610340c40e07512014000d02c40048a408101c440c815898104a0303050701c985594040d040d660301c1007030350540c5081450240d44948074100080e00302c400c0403940c035000c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 106688426 1250 106687176 106687181
    0x5091206040c0504020307050315040b1c0c0e15040b03030d0203040b040b061c110d02150a120605010c140111030f0406050a050603071a0409150e01080307030e012106030303 76
    0x15030300510180c0102c1d620b41062100b07900c01030350100c1c00141d0400000e5a14030b0189a4118415401000810907090541c0016a0b03140b5000154030980b1505403840c04000040c01586c0051050031210505442e02c004d804009000091099026984500d140d600568084c01100d1640416040440d102c0c10320303081c50700d0415001c0703d007102c4408552000c980320785032007460010840340310899200d41448a996000380704012802e800d03040400c4180c048010f03951440001c440c00307803481d501c5484141d1080d00030181c0782c4a0180d01c00c1989019014001ca991015100869542100010f808601401560742c01000614182e82d11101d000c030030720111541005a00d402540600c405102031f0b101c201840c011200c0a54209926070311800c420040d59003690f841a000030099a001400e2560320380d440d005807001ca0b14803a14000e6084800d000e507460070512140901003502c0114100324560360302400481c40c501115040c4070701c000c3c21550300705c2c000e2003e6881418054003481819501d140240c003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 106689676 1250 106688426 106688431
    0x3070201020702010f110d030b0d020a09050a06140303030c0c03040e01080319020313150201110f0d060b031003150603052a040905060610030209060406022b0f0f05091206 75
    0x10300303a6240e02081c144920010f0715061301c82405410484066502a0000c01c50b1394525038010483c4511500533945148052008015613007001c210b038544090003004642d11a0030084240c41400d02e10205a200003013661790121034503421035a104091025107245004030f82c4598039510a000c00070540341c10203c0503103c068810790002582000141c01aa104d01804111003881c1420300800c009000004180e54a01440e9000002d0080344064104c20b00343d22102c0352012041c03001440343e0007843d440c89100c0c014000854a04d0a42c00d105008801c1c0ca1414030029081d080c0070700081e86c0c015101cbd8091700045a005044540f1140c0340c402640f10301c44243e224100d0200908070030401c0d410280214900151700802a013200d64410041118400c11515820205a0300340005200e54031104000c201924039074005058104403090210590380c244801c0745042420b4110031040181c00040c00000e0025604010840c4100c030401140c0900820302a00d40c030611520300d204228a01041450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 106690926 1250 106689676 106689679
    0x2a05040e15030a02010e01051c0b0f0604060f050309011803020a110303040605070803131a1005040c0c23071403010f0204052d091005010809010c1e020109050303070201020702 77
    0x910966031560240881c0344a45040c50305900034001c1c0000562003510603110710501410725505104080d116441030011681d5181c10041c0d855040180e2403420040100d45540d04603103052034281801401005801c0b00020b80d8180000803020558541c3c00390800780c01c0048000750306104000c1c5080003990382d00201801d03588980255040c02c91420f001c0100c6003560015140c091410740d00395110803032584024041c528010070340d07120303000041c03240022840104500c000f182d42400c00f10154051034005621103482580303004c6110b29001c0e0080c1c1d91503065900800f000300d042002d8000000500259034082045001d600c0300424003000c2c07811107141d00403040e0020800200040d04801c101d21403409442e9200000007520803c0481d140b000180c89504030800e4481c0c05034903400304e080c031142a105698492040c0805200c0f0f0350f40000d195901c054540001c2c0100380c26040054034440807441010a40d8002101c42c0308858000d4100081555114040307981d00e203440c1600074000c0d004150304a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 106692176 1250 106690926 106690949
    0x30406050601080906061302120103051608010504021309020607021005040f05010806030604060b010918060311040207171e03040501060e0f0106080712060b0307030c0305010801090b01092a0504 85
    0x7800e00d51045402612502a00000340015203c0701d041000380b49115038003011454080000401031042d00030800c1c007c4d0700c940300925200039600703c4280f0541a64000d8946c687c9080e0820000d40e0310000f070f0140c0c0401c1c41100060000050010940f06d1054101c0a500a9104000c00c040c40e035120005004a400301c0400c00700341601e980045407201020788486070b040d4030440118020440c6a270154a1625050400c6c02e1416581e100b039241000c3c1000b00c0c00101982c0c3c000801c2884000c580620a182044030210b00c1d1100700d0351408003c88801201880b901c3c00801c4c0c0104010010340d4022103481403060a40e260b280510342503001e048140a1030b024031803c14042084101c0c10000c16050300e40b144c458040e5559805021540003450290009029071241c030b0000c0c1c2803503030f10011409030100b564003180344c005100000c1d00b0703039106a009040703d078942000c0b4004103030001d1080341911131890000c5030044e050032084880090152075410742c5104540c0114005030020018001c55602c4840b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 106693426 1250 106692176 106692181
    0x7062303061e0415031b060c060b0a170303010609050406080d0804061806020702040b10200a02040e010e12190c0c0305060108030c01050702160e18060a02040602070920030901060305011103040605 86
    0x60005490b00ca02c947c90225482220010000b19182c101140e841009010940302d5a42d442d41d820702c0807002c03100b2022540000005004903548010210054034068a09203da54904082a540da0186503208810010307a040483c0030010507400841c0b001081c8081e83e0410784150038920000c0d0300c0034600320312840c94024054910704048071041c0c1d0710f0600d03403101b021280d44040004140c110910748035945010745000340f030040e0b440d4824907092411b041c000042900600450394640b1080000350b108400080c4207035a288000349100c10211301e807600e407694600d5845e00c2c2c00b440001c4603410007421401080004100c03100c000000e00100c0c1d10400003480261542c0e00b0a82e119407003040b00d10599412014148182c551180426030402050743e500d580344100c141c13a00f070400780309507403040300e203a000107003000340d940e040001d07a000d09410b001c2040030b020203205040d088485a030342c903158200040009a4105000c0d0b100100540e0040c0007400210840b800321800ca42c012101280c40a103001c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 106694676 1250 106693426 106693463
    0x6050d020105040b1b12030405060f06060a030c0207050d111504050d14030702030a06150803030f070806060c070e0403120c09050103020f1b07062303061e041503 71
    0x2000058041c1c460740c2c80d0504180f030360318003540081c100d042d400c5149a0080c24a0b117080040c1e504036019a4032086e1207061500d410360820802400d0300c210011100103100c595600c1104645a001160900180c2401201400e0f4240205984016072054024640800b4454038141801003488102c805c030318005148007011540d0302481c06201c0e00410095400c0b0001b03100050b50301049010441220304001c1c482e80000d01d802d81014040302ca15803120700011210303d00300b54010140241e880554118038000c50021840c0d00010500001c00082100ac1003071510740304116003500e1050300a907084503490b0301c4200011581903904a00055903440d0892007a00300d44251a0569000c3da5603180e610310b071100440280d00540310310555007400708600b5240c52080c00c032806d110407204002d03240310742c6401c0010305080110f0200815428040701218070340b8540008881e80301d081220f4083d91644060145903090b00b4250b0351903000707881c00d00ca9923401c907552000035003100e02c602224a81c4424007030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 106695926 1250 106694676 106694689
    0x1e2901091a24030907060212040303120510170d020705030c130c0c05060a0218060a02030a031d0706020601140307060915090905070c0c08011a01031d0601060c0318050109060302030403020c030615040605 89
    0x84041d00040c14400710001c1c0c502d243e00107a4000c940050763b00800f6441d41822044015440c0c40300e1003d902240e54000c2031030301800000003c00084001e005a1010200418042172450030000c2e08145c4e51003a1402841c043c0c0307041c000858003d01103401d00e152084800d40203510545131000380700ca40ca034440c1614580681141c1e140051a030155003048181c0710140d0103400c0944440390301c404105429548007508110641c014141a4020500c5526001c41d0000070030f222004207010381c005178800d02804c2e030480e454100329041444032020a5a2115044800e00369642020090a0400c0c007400f4030642d101c3c90020025004d00c421030b100981d5140014202c41804016059804100402e00c5056010b98002500d450020b203170f558240c1d540b100c0326400e260003600903801054142d4021024150702c00c4012201842811a8051160400002074201110362040303504042d00007000070708240c4207214540880002500f21921400c1810384590201d87d1040c0d0301c3e01451800c0340c0041c280c940b00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 106697176 1250 106695926 106695929
    0x509060f06061e030a060b0d0f0b0613170111030103060e0d020d091a07060204120b0112030e04020c030c0d20070e041e2901091a2403090706021204 65
    0x4000c5540e0143e1038040041c1d40d400051150b0341e095070781c11000074480d100c540203220501000b04000754804224222504880c1700b680f8013405502c0511040e89008a0118900280c0d4020301664003408610b24a4601508000340003403540c0360080000020480c041e00710a0b04102c4000039500e520310b55a100702e03039401d03d0b9680303600003500544040010f01c8000c0001041c925040e003204e8904032007a11580c003071760301a9015500c200c59480c4400280308151034401d01401c19003041407442c00b410388004201c24200c80c001032049500042c0d0300c034426001c00480702d44144440c2500c0c00c000c80c01c540640400d1401025100f02d41da4034a001c095120041003800c01d40320020070032040c81d200c6466050000001c00e001004690001000c2340209001c6078282d000354504001815072440c8030750800441b4481a4041c2030b1482c28041101c00c00340740e01002c100702540640c0c1a00883c01107606c640042c2c0c05106980a807142c00000303100f482c3c040810003070113072038454013141d68003000705d070342c0215500c00d0703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 106698426 1250 106697176 106697197
    0x71403090a06030b010c02090f090c100921151406120a151d01050a0b0108060907111c0e120606060f030a110a0e010e040c0507020603060d060509060f0606 68
    0x80781401d0002c1c074081d60120200c00c0040c540181c02003807540c08914a41415107a009182480074100002c0e04001c1020050f000c400780d030100c0d03641c4040d582c041d01c17007407442c000c480881c40e2003950060040814039140614903040010445c418110350608002000c02008460b8041e1480001581c0382c200b40000c01c440b02c94081c0203001060050704d9000d60807080c00c8607161030311340f0b8040300802408101c041c4031250f05c1e0500002504d04114071640b089072070103011103040c03102c014208411aa5034501030b503400040741c01c0020603000300c020100e0900c4400c500e100300d41a0300300181d00010360b00c01140041c800058403144420f0f8079503001c4d1a43d449007100c2ca02c0c1d0222081107480e040b4903000c2c0140d500501c2490300441c100404028140350385e000340744104006210700141c0340d840d43e807003ca9801501010707901042481c2e030340d00d401000d5100300078000c1d019000000200d61591601c8104e10940da4002100b0002410008042074071030307500b640c0c2e030001403c169000c00d525180040c22200303080d00b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 106699676 1250 106698426 106698439
    0xf020a03050a02090a12020612040b0907060207060f0c050703061a040f0509030901110c180a051506030a020f09040609200f030609043002010606020f030a03020919030807140309 78
    0xd1b2545010b17a0800840c0101d80040052006400c44140340d0f02d200d02551107140c060420f4500303464124a0700b60a40e100c5030866101540401070a074001c04403000d0707859240703001c0110384120f050091401d105603000504040c0790454411003c0d424452005194400700c0d420b000660502c0c0030001541c42c2a6004030f140d03002000404030030740c060317843e0b00c520701e101d001a00c1d040d88403000024072960b021801201c00900c0a03042000c644030b00d21900e5031201e00c10300c05030b440100301008202240402814880f940758001640c0f145040414141c4608920040050181980724035803603002e8007007400c0070581c100302103206a01d1203203040d003030b681c080f40500c0c1890b00b985d803094200164064068130580f000c01065443d030b071103c0d0000c03500210701201514028492924444001d084072410ba0000c421504242541440d4001c04800c80c1c40c40705a171318000d030711204258006151761388501d24100100d00c92079400010031891202921800740244400b0240190442d03e00e6124828002032503070062 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 106700926 1250 106699676 106699679
    0x605040912030c0909060320010f0804080904090b1006090b04080604150207140f071a03181906060503070609060503041506090903051209031e0d0f0f020a03050a02090a 74
    0x82c402d80c0081484402490220900741d0346030a01411201250000e8810200080341000c0c0711100c5035136410a002c081c0791118181d115100e005004101c050002040e03080300040c3c1605655440c0c00c034101580d00140d00c02c9560418050f0b04e500282284a4940480c446441c00211440208150f404885480002d080c0c10703515955078556030745005940084103035081c030407031000c90140400d20300480040d00040c0950b101c4407039441c4c44d020441c0c1c031001c2d500f001c0341e00b141c45a80c039001c1540d030401d00810300c255442005111150400795811180b641c5d04404203a544103008031034024204841c0c05505840c0c41070b0310390720100d134880f02502070003001c18010404a000030740c52105505e40002c801c140001c080c0d45442105050f107180741300640c0014004200712400841440e1100c1e0000040e400440c03030400d101f00000c0403180400c90b600310018020480824242c46034100e0600030a000e00200140c0020034180002900210044000070b07180100050441505108840c20724000074081d10445 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 106702176 1250 106700926 106700963
    0xf0b0d020d060e01060c0209090f030a0e0301140709090606020c09010512121c05010821030a1401090207060b0306010503101a0a0b0301180908031506090a080705030106050409 77
    0x1d6000800c40308903150382c0c490005007884a12403c501800a9560700c80070302c00a0b00411606060103088946030b50070001c00440b146000000b11071440d80325041c2407200c0f4081d0300000e40108140340d035442828040700104402941c0c8402000c082e66a8482c0410030701e03447d0361040380e440b5a03801205400403076840041c450b82c50f1600d180f1801090f128116a4200e1070750307552044582007c0100c0644000d000345060800c0ba1900409001d0503a1000510072030f03c8510b0000c04018a520000e141003900001003001003202d90001c41501c000010006859691041e40c00b009601c00502555074500c2c0c00b402160b6840c001c01d2043c102e85d401030040c018049616032003401003080d003200c18060582d41c0f41010040c0c1b00c0105800c01024000e100c0d907240d42c03520101c08070004041a0b41500d0f185400e0305240001d0b07050007541e40200080c10950302d503103030105c0400c41c42d20a041c480381c2e1000d1594000281a400003130f40301c0a855050b0003e105c4580e548003408155040044001c00207510480b41c2c0004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 106703426 1250 106702176 106702181
    0x30f040803091e101d060103021908120d0c020a0c060302130807030f0c080307150209040212130c0b0408030f09030a1502030f010b0405060306151c05040506010f0b0d 73
    0x141c1c0380020f644101050214450060311000040b0f07980c0e0700b188007581d441010921400c1e8882c9603c4600e642e20000510403d5100d40050100a02c079814443c0301c134101034182c07041c2c10003401419044900d100d041e040401a03981040c42038004036070600c2d401c400260b10108424004540c8049401c07a45410719006030082d40000c0c5144c1c680c440c42c45000503041008010550040d40140d8a000d140300b92400c00c0ca5002c0860303084192154020444403000804241c041c01074910455801a29070142c1e10000300680f20700e1070790494000c4010140484c0e1080860802c00c041e102e1741e04106d85503910031020301c1900543c403e14865810500c003c032104600200100070002004095501d925103070b83e940d108160b050303540005455400720400c42900070a41c9000c0c09010b024040701d0820b4540030010301d45210044c440382c01000c580c0340b01d00b0b03220f080c40c0644a4602c0c2243c2e01a10100b1032601d4400101012501030340e840c45003400000d00031005545050a1f41c00e40f082d418681030400c0c15500c013 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 106704676 1250 106703426 106703431
    0x903050304060506040e1207050d051c0c0239030105090a03030203060d020607080a021002040f090b01021227090709030b0411031608010b040c09090f02070203031206010f0302030f040803 82
    0x708240c075211b0200c2d24010512180d00e0440808402e01c2d114130036414002d00d0101c6040001003400342c10030040600301000c0d0044096100c100101081101c5101f0089080c0108042a40300d05940c3c3c0d110681521044820510741d50304844159005100d420109401d94005580007100e94100c1004000400e1280d001181d0bc07000182c400288a00d450f40407070380b142d202410950360340e00c0100c3d400500aa042c0314032501600b07248815407c0a0902180901025075849007441040d55040181c0d0164004d00001450900c8a45001c1e140c20303003810b0320082080d030107520420705a680034403400c6d14076100c1078480c05607a03166182883c03241076685000c1d60719005030003940e502410051030300d12a6001c0100d000710850b60780d00070b40b00d2403901c02554290788504101d28440c3d42030140c0302018a5010584000b1221003c50119100c2c156402c41b0009106103840039415000c0042d01810040041420b01e000d00d40a07079070300320b1111182030101d00700d00040e291010f00c0414807001c00c007c83c0000002e1074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 106705926 1250 106704676 106704679
    0x50306011b0213050601180503031606140103030e010e030313090c02030f0a030c030b10020d0315030206040306150e04080a21240f2714010e01090b040903050304060506 74
    0x291407510a0300020181060380500304401501d580c100111546d024124111500e043e1074144006420000081d40b00d01034103001007030640e0b0701d918103400d01ca4582c01101e2107107411188680d00f5616810020b103001c2003a588a808076000844142d04d900f07000080300c004e100081c400d070403280d041c1425400940b980c002c4580841c842441401190080e04d002000e034002d40791000958008000c2e001340c1a2030304410b040e4440c4118240c209549900806d2044010340d891500213038165204180c1c5c40c101400342c001039001500403902208010340c99004202040c841f048007007545540328402c0076040b80c110f0b8010400740701072080d482154004c110f665400d5090b00c520059040c0c04032000000c45d030340d0841c1c07000c03400c00d181c41c05448084102c00380c9010b04800000409418101048400d5403002165400300120700b42001e0f0428074116840103180701406803440382c255079122801d5074100f4007801560403c500d4119840054a050321a4440e03540d810f845040c01c6170f449444203001050010510b9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 106707176 1250 106705926 106705967
    0x12030c020a141c0302030f030c030604060605090306040f02040e070e040b0c040303052209020f032a04050108090f0a050609010b01031a0f010c051c1107030c030215040e01060903110301090305030601 87
    0x9290048030140514810100f005603150ac030311303100040205a034016402101440300c1040591850b4901183c1e1950082d001139101c40b00b09610701c007080040c5030140d550002b500078400302080c418070b03003221302d8010740c06a021040e242d1a00e0441c03500b2403250303210040101d8420400f20f544140e9101410b401352401c0500c1c80407080e941c88050040e640400851b400b01140002040340602c1c0c83d00044904204c40041038040c0c260307003034044100384140e000329410300043d00c000440d600020000064446050020740e200b40c0700a01c0d006039560300c00e840d030b500554200302900c01154800d210302c01c030b29802c0100f483c91000300c030014080f5104a604000781007204116299021a100300700d2402051110707a0300381c944455040005281d82e0340c10103a81c1e032a0300605800c00120b0314480c03a0340150b170f070121071105d415400440207e840340b00d41e038404102c1c1840f1500000708039801c1103c400840340210929098200040201401c0300c1140c01d006021503014008281c0c954810201c0c510084c280d030581 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 106708426 1250 106707176 106707187
    0xc0815031c110712030315061209170708121f090b1f0806010e0109080304030b1314011d010920030f0604060203070e030a08030f040c12030c020a141c030203 69
    0x140ea0500030f80e60842401d252075819038100301581481074100f0702c2c80c01c2084501c058108500106400541281103101c6505d84244070103020808020010b2240c00124071943c9036102e240c505030a801840c81c0002641344040020188403100300080000e80c1e0308011100d04038244503069004080d0f000615400c060f01c00d00314012b10030107a40c102c85000341078031401d0061034110001014402c11002c0c0342d0400c0714170340c4100850200081554240d0f5403142080084c0e55844591a00094a15001500e800f504480080000c03a0651051541030500c8440c0c2e0341620f0795100b10380c02d9640c45040103040d544410603000e4408590420340740400c0b40141920104805071618501d800010785041d80c4203580001403110454100d504126000c00590150500d440d49854003041404014100880740b02640c00140c02c10403800f1902018082c0030240d4404a00315040c0200b4100091030201d0040c00c0714000442e0855039200c00d0714150328005e0000e241001c86002003903440e21000000c44c190b1009224 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 106709676 1250 106708426 106708457
    0x7031d130509061005030a0f0611030a050402030601050405130b04050705040603140c1c0314130e1602010e0c0f04060b0a110c04050606040b0319020d0c0815031c 71
    0x511041445424022900d0b042481c5030500340407010302070729880e0040d07180822854501080011703a00750881316400b1040c2043c10028003600c0658103403280070b40004108189000300d40e01413070090b4001c0d0101d030503603a220011b01046440507604104480c208041c6200003900440a140e4040d04c11010b41c0c010542d1000801d06441290b04103d8240c5801006040000030804c101c00e4804811184407410300310034501d0740c5600c0c64a520280030480807001e0012200c00704e508440312120804802044144c3e58081d2801c070120640f1044603100220313881c40103030b520501a5840d40344401e0064080c420004007080410b2001300300b0190080e44501c80021008080406080010400d4503020075030724a5108103402e1440303840e5448d10991500c7d090200685524007074909503030342c0b82e08884d41c9841e0408001c20044175107050301205400010f07400c07080c50103604500e10392050380d2034402d2982c80da200709100306c161145003140c16610641400340304c034901c034022001846041c00e0a13a410b000005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 106710926 1250 106709676 106709689
    0x2010e0603090f1606050301231504052716030b030106060309020117070914060909010303031505330d090302030415030b030604021e0d060f0b0108040807031d 70
    0x700c002001d600310718500b0040f41014480e19125040000c90074501c1800c010001d0906c2c0018000c008410000c51030200004e42003108a0311401401000c0081131203800389000300d55401401000d009044540d4802130320803048403019102440c4818a03580e43c6d55403c1e00100c8104a8a0804200b5407112460340340d685083c41001c015100741e40d0046a40205400003404404080d404000310002030030800c0004d540c008410400d50743c0544582003945004400164a03018030001a0750214050000004058040d404408004000100304220716524410048500d8507494512030b410740c480900012440543e02c005011001c0844990900420750901011600c0000c021000b5910028052001074901091041f01c520b00c0e103010310042c14034030302194a40c10083c2009004120000000c040001c68803400f00880c100640050b000348071909101000c0c1c10422010410715191040410482d44200c0d0800c0c412030301b001c1031070700c0c2909680e01150b00e0000c1000700042c0b04490310340080a6500c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 106712176 1250 106710926 106710931
    0x150702100912020d08040c21050f0d08011d010b0a0908070902040602060c041d06012304091104030305040e190e06060f0a080706140f0c1e0a0309030b0402010e0603 72
    0x46140407816141e040003e0316000b0168125024000640200000140c00344004ca0980302081c0c203191682c004001d00402c540b1422030020b04a000d480d15002503440c00145d2407160000300d80e130b2403407d660384040c1c0d58040032049040c20200040c0d0401405013130460001016032110519041c03003000c1c2c1d540d01c0c180c104400798001c00041d40d000a010070005504011203a080040c401846250901e402c01c03e02184295924005c43d0301c112000140d103036030040c0b201300003070003c010482400011061024426034014011501d0341850700c1ca80200b150010002c0e10309403541a190782c2d25250604801c0c04248030020b160818842e244503030604495201c1c060022520710b01002404c6505000080001c4034000c400301c50b00800401104020700e103400120641154482d080040d40ca0700c8506445609101da01000c103c0740f4030004100148650000310220909103641030901c2c0034078034120032500c1d000d44240140008500c1c000c01e0004c0346010700300a0b046841410140c00e0691010003044003074108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 106713426 1250 106712176 106712183
    0xd08060d0812043c0f020a0609080601080601211401140628090f0f0507020d08160c03030b030f15010f0605031920070b1603020c1507021009 62
    0x42c006110800c4691025601d550b0b5080e500311124480340d0b2450104103200da00348880003000e590040c42070040304294407038100d8001d03000754091902c8035005410b807149841407003034078812800001010400416080d05071214200480030304808200c0d4030141c00c070004415a4964000c00c102070005100740300d0301d9070480f022904030960303103003000030441414000c60b00c0c50010144660740d2110490524040750947d0000381001070054400c0030b0003c01028869240000f0624050502c07940b150000740340c21600c01d4682e5220a9951500789040340c5483c40311003000130850044c5000d00003400b94004450040003c1c04460710070f44138002091501080000380510311032900018015068140440409416039088c0705203141001c031071603400000d42605000d80143e48880050224030b804950200c101850310055840b1215070034078a05020081d100d0040d041d841c1040d00b181203004e070003039509002c1c42c040980000720529a08110080004281c0004c6000e444807400c00d01c00c651269180d514007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 106714676 1250 106713426 106713457
    0x103110408060114010e0d030806060a0302040f090209092a0901141812010b010518030f0a0501020a020705010807050324060409091203020702060d020d110c06040b0606030105030d08060d08 83
    0x1310b030005010b00f8100084030f80035900d100e031402c001c01d400c5102aa04054150781043e6030f010201000c42c000e01a0b0741016040c1d841c42c11001910201d0fa80180c0203010040381d00780d1050703e82d44100140d40a200700c6401e507030080d040143d402012548040c1400034410306141c0d074110078818040440390b0000d06d460341c1540310045002111308100c520484212611402082060403410020305603002d5124140c075502c4405807842c9180d1414010030880c50706010444013400e80354504a80070f03412403084000180300e09240010551303c075900c4c05025858540365a45143c80d40d10707500f0400304e002d5411070038001140c076454180b03889030741c0284000c00340e04600040501013881c0c010701403a101d45607403041600512008015940703142c01c4560030b1485003070060b40c1b403e05e038614001410104021084030440440e03101401030021802c0d40c800c40c845c80d04e01075a42d85020030010380b80828010740350103078801480000002c2c020004290004802400c2a460070580c0c2d65001075a070001c03810701640310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 106715926 1250 106714676 106714709
    0xe01030225110402040f0b030a060b04030c1406072102160b07050f010501050a0b0c0c060a05070b0a060803093a050d0f0c02011b0204050405030306031902060901031104080601 77
    0x42e040c2c020260112002c0d480c203840c00c2600710fa000701c2c0e03000304940c00300c2c00000320307000100780d6018000030040c2c0d140080c1c845540c1d0903d040705070714521851856481c031b550380440c1480c00030111012168418805010b1103d04e00448004c0580e00b4907500540c418030384008440140c440c031802c020601000b04503a105c190349440c42c200b4040c000d03011840e030f05040052080c0d40d03501081d00c00f600c8011002603182c1f00314240c110f140200b441a5150441800602c0d60a80c0340d004004000d1240907044d203403090703100d03a0031100c111703009841814090f41080c09032a00390710300b19501089040c05e1005000e80800d0805036500d07401c40c0703985207920003104502c15208100c4241708104c00d0f4102400c2c401100c5011500140114450181c002d0400401c4109101c5004a0003802458035401400801591500d460403543d05d9205840c114428030981d684800301c0c84600711541c25569000d00010305101e0980d0064018064040b00c40d124500180301c0130520b5001040040d0092075106d60050741d07007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 106717176 1250 106715926 106715933
    0x30f1e04081903020c0a0b04020a030615050a060e10030b030f030309010c030b1008060103090303060909150b0303043503030703060f05060301051008091e01050105090105011e0e01030225 82
    0x20103202d800c03501454018000a0002140824041115a0010103002d882c2e950352000580b941c00513000107111924200c07600c000d02072091440c10070b848003a64401080c039100c141c16561003501e04012503004040d40034891806120f500718503e550701c090100d426180e0f044040780e040d81c1045411149076995540090407195141c0640b20700c2c0d0307100f030341c042c0c10300c02c0480c0004010581c010102c42c18103465640c940100351007607201ca0000c0040f14010484200390789802c0c2c2d10001c03081c0714188081d060000c1705080b468040102c0c1c0072655005402e0880140e08030007845807100540e03141d0314002e10115010030012050000b103210b41a1990001800c030308003049030700080d289070443c500400083c00140055201c15110100d000c4803030030400030030351741c84c86040d2400c080c1800c2181c145514528101c9002c40541296050760b100302c40910140c0c4c0ca030801114043c5520120030b2114054403101c4890310b0058171042105c42d030600d405031030083c602e54002d0070074220700c01030b04118907403c4041007070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 106718426 1250 106717176 106717207
    0x80a0c0902130303210e0a020117060a0512010204080604080705060f0105090402010e190f092004230d15050702060903090423070207081908030f1e0408 67
    0x16040000342141415218007485942c030800d03010007000e003d411910b0300b50221000c2510080f850042c14240f1210760804102a102d0080c218202e0108405010008140d403032059510b00c80e01028040c4d04500d840d00c410003500c002448400e800a5608000104d8100020300803e80f00718094906030b0750fa405140b5040d498458000d00351400c0559080061005075148901c05801c940c09180110304500f80000184000d0292065503140c0e181010f000914401500c40d00822109907950030081d0030b0b00c03600741841f007807140b02028040701c500700010300c08403041c400010144560f0741c0d045001c8085031008141d8447d6900000d440b007041c404042d6914400314080c80750f0113001d601c003a02403410041400d907624020755941034032075615041e00403510500540c40d0420861902280d0030607050212020b51902c01500030122180903c4441c0102810137804042c402a0300943e25440c641c3c0c0c04c140400700702806000e003110559001d04034845440c03006c020600550190710140d6a412290014940c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 106719676 1250 106718426 106718429
    0x4030c080c0117040b071d040923160303050f1204060603021516060b040b030102070c050405010e19021303150608010c0309050604110d0506010905090606150306010e0316080a0c 78
    0xca45003401080001039038079440c1c1b80c006c0d00f18100801041c2d078489480304140d454601c8a6001482d03d425207060010000f0b001038041000600c50324540b000408040e2600d65800c03203034610b142c400c1000c00009209078010044441d084480c6800e01e5802184000c142001ba58290f48041d00c94a080c8103500c1c0024120900c2c4218200310b42c40c0c150105e0242441d1203103032070050816680e0780c400d440f141d180c50304010350302c12004008541d24001d514090b2401003550041034080c9103094008503117644880e1900340150303c9440d2090402c440c03002c201010b51f03c03001c1e4a10080046080020018a01c20028640b4601d40c80700440d0342401c008400c0e0031507040804031360405051400c00742c049003010034071070342107904210808901061000880c1c00c0e00010702000700301e440341000000b83c81d86c00f0b40c002030007030000030b05941d034544031141000203010340106000445001003020901642c064004143e1b040e2010f002d07070745601d041a1083c00412456880b200607034201e120000b00308450462000d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 106720926 1250 106719676 106719707
    0xc0810060b19030c11010c08010305010b0102030a05030c030702071802030a0b011d0112110c100e0d1b0c0312030605040f18020d0807050718050603010501050102120f04030c080c01 79
    0x2c0c01c12120070b1034901c4070311400089600703159468005841d09407040961070142107201d0024001058200c00007403007400244016500c6510300150394201d9840401290300301c01090344e505055031109180000c0903400a0094000d51040000000345100c100302003444d000d201d1100140c47c0d02e01f201265043d070701c102d042c1d2810070800d054100b030085c242c40101c030180002860a80004103038031810100030980001c04c644500000f06504051000000e1200302e80210b84005120700000098820b91f10114525000089401801c52200341104110080300c41d80c0500c90410036a60750740c8821440f10350800030900041d4941d1018403c5080c240904561440a41030402c078099094107401038201e00b0345c00003807240851005a0040c00103201c1a0358019400000382c07400f46540746283c03101d074400200f610f480036040c600060010303d01032240904a031010f8014040103c4c1c1400b50500c29032140e60078441c004818080072000c52010300207400030b000500020814144410009010311b50710315a0a07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 106722176 1250 106720926 106720949
    0x30f0702010c050301270e1606050901080105040506041e1d0a0b04080c240f06010e0a1802300115020d0c030306050414150d0305070f0f0c081006 64
    0x140c0b20b099011040707904550480c0e1040701030800500143c81d110442811051200d4201996003812000100b00d80200882e4010510b806980d502c80035a91800340c083c25501180d81c42004002506007604003a502ca400100300082d2054040c0180c0d03405130f4860070740c9900c0d50b9071300020b0340b8540c00b01044584240e040c00047c4005556603072520010300780100020803600d0041403280b409034007000060115403558504001a4404080079031034880222140060000c800c00403030031a50150500281c490000390000742890b082c00c45260703c00c0c01c208503400c1c01d45d9003000303240c0c8400c80c202c5041c0354002400110000348035031060151040b900c1a000b8141e004840c9216860a90300010b10340080da90b142442c1e1100c6646080907001420640d00007508141000c0240c2c81070140c441e02c040c03045040c203201e83d002200d200c05016488425140003408200f0401001c0c0c0801c1807541d540800034801e11500440c40c00c660703500d62a98201f54450f80459202032030782d010031011401050060300900062 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 106723426 1250 106722176 106722191
    0x50702030c12070c0f03060905060606071e0804090f0e0105060108060607170f030114040507050c0705060318010908180607120507030903050f0d020708010606090303210c0302030f070201 82
    0x9869141d001d100c0412503800207965001c00c40c8892000340102801181c13405034617a0b070b0902c040038104641017107030503014a00000e0300a14181380dd43d44e8080d006800c59640350740403e0505d07481c2802200540d00750b8000c1c080010140c4a40c02032030002161030f14040341c031042401d0b1540c02e40d030020f0443c46c10b01c02d4080410a00ba19007400352100c0300d4100451500281c0842c101103080d00c07034900c519026480c000000320744080c003071220010f40c05056408011aa0b11007030200c405006201c0004403540240c0c00400c01c03403030458061a0840d1510707004542480346c0703c40c55421542d000f80f045549800c00728207006c0f40601030801781801c040503076180d4500318142d941c00c8070383c908481d4048140540824034000740741c42101d5940265038020304440301411a0b0901c20380d2501e07032002c07030b00051285404c0072401b503106000e580300715121912003900d140d040d607400352112150500700103142c0c2860880c0d4041402280603148078100ba81e10700503901e0402410082200c00005d01d501e01350380c1010710 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 106724676 1250 106723426 106723447
    0xf0c03010630050d050c0c030601030302062701061415030c0909040302150a0621050d050705030c06010f09050a09050705040507030f0e1006081513170a09050405070203 74
    0x4084400140c40c4810b041c0c0302242000210118030008050050303c2910f041e032103660707084001440c50441103000c0791408894074040650b90303142408000d0068004001180c44040780c2c078030518400036103244030f581d078807000c4040d9400c4070b0040c0d100c08139458504e2030405003424441210744203c40644041c62540c6041c003120400c030704c2a0000f0b40c0c09028518000303414144240004012001c1c41d502403070302410442e00b64800b030040c42c0035084282200c80e05a07800041c1c5000604040c0783d018001c0c2680740104441a039080c0c02c0703440c00340e900d400100a0b030b40e031045050101d03d0103801c05070704100301e0504064401c412103038000c0c401010301c0e1600022401040d00029500b0131203404507008116030340c411100700c003e1300c2e510fa903040c2d540d42848000d40c0c032210f0200302038021560300c241c20002140e030b41010322f40da070000000101c50311032900045842240042d41c49451107004d61003034010b809007126501160b600102c218000039007142070a1006151038001d00e07400040620013141407948400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 106725926 1250 106724676 106724699
    0xb0105100203070f1e06091103030c10150b0409050106030c05161104020c010f06081b18060301060b0c03090a0b0301060e0111070308070813350c060a020f0c030106 72
    0x26005082c10800360018420841742003a18010044800c0041060380c07158130f814005000e440100f01c90220f650b121140103800c00100307031054a103012004100f0a02e40200c0040282104000c0300340c4080b280b4008141c84404d5002400140140040040d807580745c5100203003125030119440c02085010404402003c1200648030301490300a20b0207038040451400050003880b03101d140284035400c01c100c040b105909030780110119404072055842c824888055041343c01c2294004a42c00341004000003001e06840300c189a000d007025000081ca01c1d15040e0600b92900076030000c0d0005e40c00090000110304000040e04c0040c40d205281c10b00350b50400e80c0c05060a01c03801001810000c40c080003441e0b0b46c070200607600003160044245990b60a075420b000045074400800c03541480201503000441001060f0901e09080a500c80116102c0d201d03205180c04240383c41c5000300714480c440408230036540300c00c007c00da001c0c51034000301400c01c004031005082c40c0c00820003d100b0703494240200030710741224 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 106727176 1250 106725926 106725937
    0x80c040f1401180603021305090907060c03050906071202190503030c070302030f0301090b090907181d0f10141303051e030403090e0906040f1506050303160b0105100203 74
    0xda0302a000c81924004940a1100c1c0594004103c400d81c0d000410380e40541c0104001d03085244098215500c4109220401005560303a00159100c41020071141744600200420035202e85086072900e070710304000034159041020140c40030301ea61200e14886076010401c3c0d5540b907140041041d444a11511502e4507408001c1c000400200b000550b0070402d4401d1040703d0301d80c4c2c0c050b8841500ea5071580542001040c032188030318040d02042012a254410010395641100d000c0c0c10f2240c942011110044094400d8120301e0403074442c660b602c821001414800301624000040c0200500c561011280d0151040d44060321180c150003820301880b10800440b90280941501b4165541d60324680c008403011741e1440c1e070f240000d0b0080305100805038001c60358030480c2d03029011510951141061f0303588410040c2d40041020610824240001e051288800306c4460800c200250055a800102c1d04507030120050f001c40f4403141103c01d0402400d429480c0c0500015903040d4445091078074040d58078400d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 106728426 1250 106727176 106727189
    0x3042d06110a08030103061b0215060402090f0303071412041d041a13050d030c0507110a0f09020306040501080106080604080d020405061908070302130306090c050d030f080c040f 78
    0x9801c000c0c884500401140700e20990007152140da0303607980e0600c1002480b10302180c4440039003800c44002101d1001980801003500d0020154264903041c04100080d400443c0c030a400018402010b409913801344044d152031402120341202180c0300544050070054001d8030100e48010030b0000740640c201c403905004090300c1454102aa503162414020710b03074203504180d14103900c103410070030038100306499101d00b5652041d000c44428000d6860300342d0984800484405c0002c40500c0383c40301203443c50b24601070039580903020032043c03511006480d04c1e420440d008074420740d40000510910341490302c61039006008400007001034605100c6240e40b11070f005803019107403010209090140b20b207036504a4000780b8004140d159642008592001c42d1440510345001041041c0001181e140c040c0c001c45504614107500e90800a09541d0350300010210003100ba0b410480c5201c0c04035544d101d00e03000500c030a00076103d44030a14070b04980100240c1c0028006110000248000c1001000500103202600da0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 106729676 1250 106728426 106728437
    0x703080a0e0304080a110105030115050a0e12030405090a06061709070918030206090d051c09080403210c1104050601020c03070906092405060f070c0803042d06 70
    0xc421500401030a259080c0c0d8216000010740000c006000082e0283c88611845d031040071014401d00569940c08244038094001002104002a19200310b0041c00420a9400c02080080810000c519090301200c4401d403148d20000f001e0040b45071110409522003800f5205000f07242c00c080c00109188a2403228140c501885000301d1113030201400804003900d42c0720000c110012005545003d0f2080301c00382a40940101008511200d01c04119581c01c10100e486061600c10540320351a43c1a0311a9541101a42e0341c0b181680002e81000081000b1802908004180c07141480417040103c1741c0420340c400d10492031440d00001d000703008503540700d04048400040c0d0340e50f1100141d0402c5000d22440ea03140c002c044011400030030300c0e445681562042c01082003119403c0100805561110740c0c008100003030f89100f0811780c030740390008100340703100041c0981c2084501c0d40c1c0d032a441c040a0700302030421b2304085000c0c46544004800140280011003c504c04c3c030300b150703100305a41416402548108034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 106730926 1250 106729676 106729681
    0x100b03030c0c01030b12030a02070510020105040f0b09120c010b03011b02072102090f0708070309020f1314040c030201081501210b15040e0106020a151802040c020c04110f070308 78
    0x40d50031124070782c41b03440841541e50b505034030400203444520302c2c00303020321030f141d05c80803841418030510544e8419039010400d0380001c01c0c0d07a11000d4880c40001c141e1a00340c420360441501030902a405024404e102d20008034049052004150135038892039503070640054600d150682c0e52340d00003003080c200e50a2032305d00c140b002d038440c5101c08103010858008e90000d030101c0034041c00300da141460601c02c4030150395a00385074440c01e40840550b0160300c4080c0d8000c0058400c1e00c80c51030700d20100410000211000900104085c00c90881034004460039101e20301c241e0020400d5580207110184d100d41d5580e840b0840059150000c3c00c40641ca00c404c070081445035025000c008078a520443d90344000400c1103c002c060a0305441e0140d100d8040c4989900c1c54a00001310140001021540c80b03604c40508a6401002ca607008001d0080c00069601140d04141220240e01c5520916040300e1803035002d00003080c008010b000546e80a0b0700c0075589801704101d0443c0e503803288030542d070220f41d2501d012005078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 106732176 1250 106730926 106730929
    0x2150901110316180b0406050309070e0106050307140a1b020a051e04060909020319030c0b07110f0c130207050c04061e090203070c0609080c010509100b03030c0c01030b 74
    0x14411508000c04100d400410711415841c020314401c0783e40e06599400e01e522260407000030980940b0310440180d02e90502c024081180614042c60380112030808403081981e441c0e480d03c0e0190400e070300140200b03d00006000e211984410b0024a9254000b601c6240019108008204901c80c2d48440924151007005404642d143c0721460002c24006220010806044440c01a101285500103208502d088000170340d8811078060090540e400030b01800c401006120108441d500504007202002000038001c0000340c40d8189a0380644100d545101e04c000c1070356191468501800e038800980d0744a010700010b2039480c041c2e081d0380000813607000758462003036107001c0386416403246c1d8180c0c0c014208480418000808030202c404101e03500142584941d07240b51032002c910041e90f020002401d00a401408501a07800822070f0601c102d500782e00d810340128980d801c4500a82d90109550031507030920710b41d10554001e20148032802c9020314a071809640602d036403204c000d86120b06150300c5070b038110030301d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 106733426 1250 106732176 106732181
    0xe06060705010501060815030106030b040809031e15010503061006050f090d060e0114070c02040b0d0609110f0114030f06120313060f0914010309060b0301090302072402150901 77
    0x1503120000b40851350b1203041c06046081c0403141c1e54144290111441003d107014000c11003201d07001410720456844a440d402929802103a0642d01445401032007010b40b41010ba03014184101400905441e451880000c00030801c107900c442e22aa11003010310820401240c80c003030403200301c2e090441d6a4100481208124010088402c2e8080200c030550781c240710f4280c003c0300b621861840200003040c450440c034a0403105c1510300c0000118081d20352801030501d80e120303488080f401040c5a50a080603565101955100441122480e50407105601c29040040c0820111482420b000e410458036130103803041e500004094a00c2078001502140d440e444007800703144441c40c074605803030340c82d40c24030300201c2e0310318480c0b090200007050b00d5031542e0038903c240e900c0010b5600342507036082d964000100440c042c0030720704001e690325aa40e68120100d507800344900c0039002d10a40140005030314001e8241402180302078065040a4140c50441d983e55001c0b81c2880c2071403030200191400c1d1200f9104500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 106734676 1250 106733426 106733437
    0x302060d0b0111070b0304050f0304080304120201020106030f03050d06050105091815120a1104020313030309111e0306061008041707060903031a03010603020a0501030c1803081b15010e0606 83
    0xf60707006040003c10500540c10013107210301c0c011000c8800c104592040f00c1d54905c114440c00501c2e030001d100c01e0117000c8042442090403401407002050301c0d40c4948070b100d002c0c0c03508101180414030026401d0b1110a20f0702484006080c01d003446800c04441071b000c100501019200b2002c807100b0a00041c0c0c501c4020311076140c0610024054000c0c4a10314210175a03a0710740440140e4140401d040c00c0c000b10301e0640201c030b2091306110507001c0c8040140e50160041d00b19a407040716007100326049441c040d1100052602c14606494150004125060034541030030b601400f0a4002c0200c0945c0e015043d8020b03aa0a8001e42d014644014a040303a0403214075500504400600840c1030030300c00418181d040c2c0000d00d212850b90105014881c10500b014200d60180c88001d4000000b1001040301c0d6020750301c001ca1100c2e06050140c000400c0301030303d441109440d0030482e104900400d070340c035006440c0ca41981030140100010120070241a000c0402d01a05101e4610016440000100f45d510f13900140d45 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 106735926 1250 106734676 106734707
    0x3050309040b03070924090b06120424021b0606090c0304030c17030a060e0f0114010c020a170c060408070909030e0316080c0114090d031b08030a11040302060d0b01 72
    0x2028903000311080c98112011403410390b034601c14200c0412031f401c2910407a03103802c0f80284080c1c98201d81ca1400745070580700500541340101d001400c0040c80440c600300303580c41d100300740c001030b683d01e851801010325500360344a440c5030b54014400c002003510341c4902d490700701e0400c02c0160780f00e513210b140444030040b000c80010404c46110003803d118025400246006120749a001d001c0140c035050100d5048004484030356140000388010020a002e1410541030180e041c900f000203182c2540105003081c40035801880040c0044202e680b51910a100c1d403071450404907007561070140740c02c07149a40c07141540600b10302c483d511006842018041c004658113080007505a941c1d13011100d203071710140c1009109083c03d42c00b03205a108130035031042c2090488051a9940356042260707080501c290005410b00407024840c542802c1002c0c0f10812045800c02c1d44558086680d9183c00c030180000c0d10b0681b20b05600f40c032070030301c0140700698501056071a203404070280080e0003001140101c808a45003500300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 106737176 1250 106735926 106735931
    0x10815011d06040b0703050c01141e092107050601090b0114090105131503240e0c040f080d0f050f04050103090614090703060e15010b0a030e100615080103050309040b030709 76
    0x300c00701a001f4000d000325500c0c10000b08030911782129004100541210104142491602c7c0120740030f02c1100d8458200c80350500311846c1151598a44080886482c00d00702144000300d601410080c0800441d80541210352041c003201030404000703040c1e40f1080c1714203600650049520084c5901c108142d40000000310f84650b011642c800c91408010a03010b03400000a06140d80f01401c801840c9000400010f162018507400780380001da5031088001500d403100860040200080d4058a80540c901915100e00645420660b110014104900d1705005105000d000c0c0000e080040d0740c4820344085420a00f00444c8030f4105240400051070901c51156500ea101028421041d80c00500b28050343c0c4144410403a21902c440c3c003942d100c00c44102d000080480c030005100b802258030260015102d03a040200d40b002c441080a801c2403002c0807466890384e9140000c003c20245019a03030140c850038100800c0701d5046880d4a5140d00c0303a90070050196032190304611f0b181d101046460000c00204104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 106738426 1250 106737176 106737187
    0x9090103061406040b0f0607020402070b090706110f0a03030b040e010905070501030606030515040c020a0f03021c03050907090c0207080a052410050906121506010815011d06040b 78
    0x680010115000002d800d152800b0000b107042c2441d2050702d200007002032002c014090413808010b9658003000040380c2260b000d1161500003450043e00c20701400f13800b0090013215081c1b0301c0c000c0c0381001544084020b0391000a044120207808038540100640501e0003080219101c004503020317001c0403514120035071030000200b05205c0f0129119054402c241e8003440784903601c0500714150790303080d1141c90fa81d4800050800c604d1506900c00000408607005070b525911054843c3c9001a05560065000d40c10078244025030038075510449450024a0400300110709158a000e82c0c0c0b410103000354000075070380c0d00025801034000c01110b0000c248034400c03164800c46600e0501c3d1208112900124000d101020801100440400d500d1256490780c0d01100c04514010802c0603c6002501c41038000c0200c09894a0b041d04c180f1004500b140014060350306030522400040650100419000364030600c40c007000000c0c2c2e40141c0c10300205030095030780201c003800301c000a1101d1151764005400d42c480001c0307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 106739676 1250 106738426 106738433
    0x13080c060709060905011b020103060308040902070c1d04030f020c040903030209030610030209041b0e01031a060103020c0c13140f0403030c170f1803040b07050c030f031e09090103 79
    0x518510407072450b0b440119496a442040d50414224051309010425480074004c00711580c074401e846450052402103401c95032030300d9000c51a88982c01001d072094000842d41300b0301c40c0d03160007076000f01b0810400300c4032203401107064141460003030070040070444107001001c0d44600c200402800c25900034010802407070b1914001c0d00a5004002040c040e0203200e0005003000c80c0c01c4102c504072038019050482d40d55807a03031800c16140302114502c4d0f61042e44000410012107220304030b130295200c2d03240c0c51080c200322054000d91440c0100482e04260041126406006001c10811500c04040d620b04400c42092814100605000214500940c5000302081170400000d003405000700d001e03071020804031401500c100c0d24110740d4500c201610003048049075002c4800e500d02e0343d1104500c00c00305180d00007080d15038115440795000c1c10507200b010411600b400b5051000700c0c1003590071401002d400c951040c0858590042c5800b0040c40d00a015100c0f800050410443c0e88580e0000c2c610142c1c1c0d1703103d14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 106740926 1250 106739676 106739683
    0xc08180a08120903070b03010b1207030219030b090609100b1b011506170403051c0b040c050405120312010902371706010207030213020d021602040b01022413080c 71
    0x110304604c20700c45c10100140030142c80c0e048a05861a604065103010359016001d8460030002e4103000805908001002a070405120310340022004ca581c041810408036041155501e0043c0030a441485940c091000c1c3d4040303024482c040b10303c0000000c4c0c81d11850380750200019038000d5006125401e00f096404200c1c103642c0240e041c0ca0341500ca06040750f040b070b0a088103641b001c403001000705400300065444003101101490b40113042c51008102c0305812404182034446401580380803c00114080c041450604a42400003d29000442c100300d03075481c07400070006041c82032400180d170000e6501030343c4200d4480440910168074015121650281c5051800302c1c2035044500050a914040450480410041401042d059008081103400c6400300b0826803c1c41c072000000e0f96003045620409806400036200ca4109803449507607002007801440107444117801a00d0441d0402c170b100003440c0c04040c0b50030034642c240d080c10407040c2d6228819440000b8403040003a040e10000b28000384c0000000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 106742176 1250 106740926 106740937
    0x3021201030f03140c0606010305042316060e030c1c0c0e040b130201020c19150507050d0201050108030a080402030115080a05010605010806060a08091204060c060c0c08180a0812 78
    0x30740c4c907020b5440080d02030302c90ba40204006441c00350801800314803258403e4114540250246240c0341d260344c01d40c0312006807030300c586694801d035811440c4001700400b001da098400410b00d505240d00100c0d8210002a1100c0d58144694400c03000c4952113041440d0341c0d8111140d15030302c0806403422a4950841c0064100116422694540041c00040440210304495801194103030000c02c0882182010819800c2d014036080d49000301940000030003054500351a45c000c10740d80ca43d10740d1512107003409030910342140c16000a41e8109001044210400401c85140c9100b6140540d1a81c8543c0700003800340108a0043c0c080020020011541c200e001c03407440c1c4c09030310440080001c00d56400043da210b100813100140d01450034043d8000d030b035024840040d0b000c940002502c110380b10450107800300f90442c2c2c100c6000610010030740c01c204121407040099220f12410124004c0b24169101c040d80e11800070b10b15085825299180f5460700c89035440405031603080141c1343c141c2458104210640c011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 106743426 1250 106742176 106742183
    0x1107060c0c0506011208030403030209030a060c090305060901050103230c0603010303030524030303071b120905012703140a0609081c060506120612070b0d060b030601090e0703021201030f 82
    0x328000040c42c1c5c82d80301c24009001e648030400303034203564a0b510241c000350410314455816001312480780300044ca5622404101c002a62200401141141415480c08100a01500540e85020018030108021035820343e41141c0441040703901083c10824030781800240d541940d00207901000200c10550150006403141118221028409030400190a08600c102c10401d815401c10000700303c2e0a40303c4c56145500014108050406000b541e6490103005807503600240003504c412010300c4690790154030b4002e2815240781d0707407080c2500710304d95a051400c540b100621044215100c0c0803e402c051001c00c007040d8200d141000340458600303190300b00c1d50210b07251480c11290071030341000c030345614840c060546070050045424461800700500000101502e510b038402c80601d481e82d68120200b001c5005006195116521944505251000e6600270f07007103101d803050140308211541e64010800707012646200304908090b1030302c0c1700540007071045105600040c0600e10000c0b050007404030034240d0641c031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 106744676 1250 106743426 106743433
    0x10516030e04110a0e0f0f0303130305011b090506030403090e090703030306050319060b0d05100e060112021c0804090e0319020102030f0a0c0207090c120b0102070f091107060c0c05 79
    0x505104192592140e8056240450203d568000c50360401880d400501500600b60b0720400f8100400203186403c048000f0b8080f0300020000d000f0080d00703004180c0c40c20720a949043b24044000006850210180100c5000d18400310015080c103110b00680c4004111303801045180c1d041018059443d0341d81c601050740880d0811740001014200041c842c03282201145404040d0301c042da881030054110320198590202c946240b91012030418031080f00074243d054000503005038104034807400d10805074840300c400d00903604020056100d0a003036020a1002c51042140b0300703da4035204009024a8001e40181403030501d8141941030b0000080040c20f052084203480b032410360380c00301d0a178031040342c0389000c401c8510007003880c00340315801c4003994018500549041503114a483c00840c1e04010170a0000b5040c1c0d802243c09411512030280c1000080c405445007500702056006030604500c10100a81d60b910001c1c2c034400c1d001c2c3e0940344005c1c2e0021043c0114621b00400602e02c0311041c0c800d440902 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 106745926 1250 106744676 106744691
    0x1c0b040e0a020a0e1603360312050103080708070302070812070b010b0c0a020d060e01020307120507030605010f1d060a091701061211040f060b0d14090714010516030e04 74
    0xb02200d504d680301303520303c0b02d2400120075503a0040f0082c1c8141f9041082503076030b00d6210190007402400340741c54540d2081c500c807403580c61410002c110000c00d1200c00000e07442d040c014004500d0b201c044520141d00042c01e90355410a600d400c0b440d041c1c82c6d42c01415070b401100e421030418801b402c020703c02503014002e910504d98031481d4421071803085c0190043c2d01e40c01801c4820041c20101602480d80b4091400001c000c0304841425003a030740100e0340200040e18000d045184451203204203604541980313000c1060904140000c4d044403200c1c0d40034824071420b5409103c417400240070185034400058280f686402e240e5a0103130241c869070181c41a5541421840108000148105000c48801000a030120901615555564403800003125003044e04e4640c80d20b5500c01a0103200c1c014030001c40d80c00d03955400d1034804ae045038100c00f823403501c0700e41560074002c062000080510554030040c04800504007110016a138900c40c801c0080d034004105130154041c1a003042c114411220103032414401c2d80c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 106747176 1250 106745926 106745939
    0xe03010516030f0e07050111100501080601061407030225030c0b030405060108160b0a120920010903030905040b040e0f031e07030f0f0306120b0613060503031c0b040e0a020a 76
    0x7100d81340e10255659102020400c025032041101140561600094840c6402101da4800594009801245071588140010401d070f070340c849030f0440d030700c68110718031400c01b003556070000d486240e41300700c401400307882000302ca85518040c03604000440d4006598071105544581e9101c090300200e400340c3c3c480c00f920000044081011915100c003000c0340c1100f108840c100b070a004d46c0b54025131a000c1c100b264036562a0100481c9100b0000043d01400305030b40c00c55544074001c0440c0103401182070400201000420029070441069000c1e0f910442d008210600a04041401441e04039100c4d40d03140f0410751025501003020008104e0846c0b54180416440290078820401303108484004002403402074440c02d0051007108051035680c02460301291044d6500d4000e501d0070642c1d4403d0b51080201c6041c8182442c00752031076101e001414805010f01c070300d420002034403401a44082e141d050102c045588940d82140e01603540070100800404c00602c1d2011100d84d9240344000407401110318403004100d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 106748426 1250 106747176 106747181
    0x27060b0306011e0509090114030715020c0402070501091b080d030204051f030617030406092309070c020d06020309010b180a0b01050702030709020306030706030c020601060806010e03010516030f 85
    0x240c201a1503209028030204601c50314103c00b1986042080001d01990300740340d45045145000704801c824403d060102d0b42d042506160141d80255401d0391400b2102250035000b0400310807401c021100181c03180c2c0d00f070524602401015000034000381354850319070080e80c14030301d1749003c1e5582c0c041100c0032401e0303681d426000c03882135015296000a0b130412900c0e004e9038468000380b030901d580c036003ca169950b4641c6a5962083c0c4004000981c00100703061202651020503a0020f054030700340c0e0a016609584c8061825000003200b9001e070441d80d0004100341d0250070701510f0320354098401d0001c1d800070b05042009410a9812042e00e508000341a001442c1c4a016086160044141d4000a4540c1947c0c02c000300284c01351981485400d00c0200302603941405400c005120030400541d0700e2404804250030a1001e03004082410304d42903a0502950f4000b40302410369105040560316a12482c005070f4849880f459000d50541c20101000410152401c1e1400d07150b106071010310044c441081400103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 106749676 1250 106748426 106748431
    0x928050d0203250b040f0609050f0615040614010507081902100e1b04020c0c0d050c040c0203030106022e0227010516150209030a060507181d06010927060b03 69
    0x104013158000c5804034040200200025124040008500485680b400d060096201000203190842410007022100d640c1d4000350500b03003100c0c1001501e051001d000802110062101d04010000c030f00a170800c02c921044500322161180c48140b41c0c000218000d40d10007051444411680c204920000c8140002a0b6452072645014a0302c40a035002402d2000a40103035000110700d21400c84104d4407a21030301e00d507681103809600039081c000703449400d200a940254804404550040004000055000c100d0358002c607041034140e0710004080d103a03928070241105105108602c0007640c20003440001c7c1c51460948176150600c0c45a04088006640c1400ba10000356000f4000d11055000142d104000485664022900508103100d003004640382800c1a10112203240d9508184451326030402084e400d040c20800c5050300040c00c002d000d403403051440c0301c0c04070302007d80c90108140340e001d40800c0c00900b2072400d000e40c1440324504201031882e1000849108149030079004100904110304891 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 106750926 1250 106749676 106749683
    0x60f020307031404050d03050301170d050703030e160e0f0a0b220917070b06040c0c020409140d05090a0b0a050412080702060d02090102060703050928050d020325 71
    0x1810040c00c0c0e181610310150188480d0110001000042403951b41d070071201144038080c0d030b20305480750304001400315022802c1905c0071281c2e001900803900d56a102c012500701c0c561624001c00e075000c3c1c0100952626031054106c0040c074444400214908960803069841340c509005509010f45504581c0002c8610b030000c5550410b1440310451060002001248984481c204000a000389281c030384044505006403500050b09002540109000c0500c000380c0e044041250200140b103031b204005171030070b250118024092074565008906004020308010f9045a4a8090710708012021600500591143c80c006114403a14400410b4440003241920006d46642d100c0520306410100300a04c4c06443c0300085800883c00c00661005840f01006441c540c50f403103a01613140c0780064006400d00c10000c00100400d4031f014100030300101d001402c642e160308000165080249044084400e031040d9410250a0344a10256003402d03540c000020690740c460700d80008400c2c004402e208848518441300035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 106752176 1250 106750926 106750933
    0xe07031e0501211a040f030212040b19020a051e19020303030408030603120403110a060516021e090f100e010806010e060111011e0608010b060304080726090109060f02 73
    0x400103440880400c070150181341c901d94101001c401110701d0007403c0f01c080b11071720380515403201010b80410060061880242e002070405040904481640c010000301524009550300040303d5103000748075600c80e8a801c0400d403070389800098804121458484032500f0310344103122a003040381b030545c02c80100440d0300401840c516200d685820296810180446a042c01b800412104202e081002080114031800d0306105c201d14500400c0100341c0c80340d10401c1071140401000b4200172050800d80b1000c2e034115686108802c3c180084900da012007025a5000000c500511901c0681004224030642d40310502a1641d601c030b20b040c0c104054207106e4868250300c0040148242c1841d4450350764052010714014100d118000c50711405d48241c0c02242c3d580c045600c5140d070310000300340140406408050000c1c000390881c00d0119406100040000d0640700000c01c0c10020046c40030600d03c2c12402c1c581d0303c00c466808642c1510040d5120341c0160380420065000095041d0040c00c80c01e144c0841070b00903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 106753426 1250 106752176 106752209
    0x6050904141f0906050a4208030d0e0d021504080d060e100801020901020d1206090203041208060901050f0118080d0507030e060403020a06180e07031e0501 68
    0x9400208034180c1d61030800b40103445815540044850100c071003001c0c044008107022060b410054100c035009071028954908014900d2151200c0d100d507203c2c01011050400d4600300500941300210600100c1180c240e40403000000b0728440010140a806841520810820b02901074803955521805000b50140e00041a980d040031011a80301d070340a170143d044146000403100429045411070340080d1003140040c418000781c2c07902400c0040c0a031081d90021460180c003407001030b5484010113220740802c42808450481c00c11580c010740b0052010060070364030390901c0e01d45496207d51245009000445031000107429280c580340e0f040c1210300c0079002c40c6080390308400442d25414100d420901a484007500011054010004500d13500882d5035515150609442d00800b90030480310803038032031a010300042c0056070b00d0450b20001c07501c25080031486c400c042d101071004200142c2c801498540c86800300b1080035055000b8500a210a1200003245a4401034003c1120000e01900b850040602d01c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 106754676 1250 106753426 106753433
    0xa0204030317100302031002120709060210020c0c1f17040b010501030b06160c080706020a1205130315060509060d240e010504080921030304030c140303181006050904 73
    0x8015400500410f880f81595490340c020901d4080c45018149803543d00217100c0c811041c0c000c0040d5040f030024900842120b1518800a560300307442803803200d1342ca9000591180810b4100000e18056802070408190541203213007155503145004092000b050742101504003200841649511a40e481000011142d0030000110000c204448000c0d070440000c20490408054140c03820982c83c2c800e03400808440d04103180c0c0d0b404d01186521500a550082280390b001908003840c03900078840c0361130b1040e10303540d0b0340c240c0860380e1001e6403002d01651003040c034101c01010300d80c000c001a00e0044d5890705007502c443d02844104141024090076442c88a04d0003c40d071220b40d2261303200d014520314046008509080c0003800c5a0003030740c0440b243c490015194841e800c00c0107906d44840a03543c2242400084d0f004080d840f484000c1009040003181c20b03050041105110041282c0702e102c030100c80d1030380350a0f100400b41c8c10342501e00c00002c0c45050044580a8203e0180c6401c3d01c40140803448603445031354 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 106755926 1250 106754676 106754717
    0x30b010b07032106030609110a0602032d160c0915050d060506040e0327030a050601061b17070c050301020315010507020a080a0305070b060d020a050907141305090a02040303 76
    0x2c01c07030f0126031610301c0000403c40e02d0080d21603041c0654a000300035000f110400c00c00b50700d940c0c010760541d0024030804650b40f18080700e56103444040c40f210560a0003090841400740704500d43c01c1c407050066040711041c8840302c1c00c501c0580e041c1305002c00500d403041c0e444400f04042c1d44252680083c1c4191fa820001d107950704182e8004070041c0c008599115a021907905581094107803942c602e40e41451865a020303410075101a0003815005403005170b031580c850940701c00381400340e00203014600c4001824008202c210320b4403d508501b802c1c0038800034032200480350780301c900103548003107a10401050504d810300c00c9901502c0d03000c4400e214002008015035050304425810303a03003c916108001903400d010f10401442d18031950f03c07241d403480303189040315141d00050460750144200a507840b0042c7c9030b21084209803003040b5008041c0380e5441c00112440700305544d000c5401000840c6001c5003011707090380031098400c2100d80d070105594032003d43c412405030744009000224486098162100c2d03c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 106757176 1250 106755926 106755977
    0xe04060b01120617010f0608121c06030f12020f1c03060b0d091b030201050a080405010b12030d060602030f0a0e0d08040b0306150307020c190519030b010b0703 70
    0x181480000c050448082e101140d031a64402c8495115060f010010a4820310907107448000e050720400503907061040d91940d43d00310ba071885c0040140007905207070a0102000f4581184100c0710284000e90701c91400d050146082ca4049a80c1429400c200d00c11a001081d042c81000c1624020200d0b44106041d0303402d0320030b480c403144061540d100c0010942c491214002d15040520f000c02044185503403034500298074000f18600401802414148010303a03100c411142c04043c21700d4910000c1c0c80c1e505009005050389045c40d0303030000d00350f01e108440d51004000f520404030781d90401c004586d554102aa200d01c105414200c7c4207004000c8030300802e01400c0c204d148190003034600c1054408a503200c01d420f61140e0000180064041f080041516100c0720b50b440400c2c0e01a160750075400c0000c40a5039582004d5103440c40740300285e42030341400001c2c00c0703440c00a050060111785803140f0800c0b24003c0c01350030302040d5584e005403000803544138403030011101313401d0341551581d00300140b1591054040300034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 106758426 1250 106757176 106757179
    0x203090306060f0609090a050714160f06021b0705030d03061d04050f070b0904112508160807060b010c080a03050a02120705090109090519050c0702210c09010e04060b 73
    0x3444001440c4c0c0b106c10500740310359840000040c05091010001d00131812080b420384040313104202080c03160b0b032061801005954022840e1213104102e1500401070300030071040c03054507141a1402800c2d600005425801c5840035019125494102d4400f00c080d00c19601480e02000c54440d1038110400002040b5a80180108140c071410034800c4400c4e400d102036a4400c803680d01011986c50752915180c0b003a034030404c200d811001d107480c4e24045001c500c40110031180c40100001010b04081c42081c2d4110ba120400701741a5450019451820790310f88e8000b0315003038480720300d4051003050725400b43c050154004c0d00705070351070304003800110101e0142c08020a01c1e036070140c00340211403030400c90080160203a401e41e2a002c5d124004800010840c18480d40071721106800c010500406014071942c400b406154914003203580d95588111071600d20640d48000e4210705240002e440a04107803403500e0780c2400420a079002a00a44100f04d80c0d00401e0062030400700241d03000c100010b0b04d03a40320070b00c041c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 106759676 1250 106758426 106758439
    0x2130510121731140f0d1203020706141b0315101110060b030109021e03070801030b010e07021504260a090905040804062102070f0309060203090306060f 67
    0x82459088101d500710010701c80309481c0b124010f1980700320315041400f90030050400b00c0e0403e441c0c0035200d16580f42c3d00c1c50990040c1200d95805025484030341a28001c10741002d004615400d94403001030007035001103000d6500502c0d05d1326001c400a5080c2c5400e0040c104810614040e22648480742925800030b08518051103041100070003a03200c0200003400030307001c0e8640240a0b81384085080c10b01c07003007840144070603140c0f038010f000c009085401d0740d06460f0841030060710f42c016199550400004400030707091603c1b002c002c01500395404101c95050b00d10031a000400742c2d03030b2200d403480c0b00c5c2000e8071804091781007482d040c100b11041c1ca1031650b10074050420740c044140e80414000f01f200d103480d41c100c018000012140001070308001803070024215040200720310305d415201e1b13585a000d5402583d0402c0f800401c00c01982401804848060580301011960341110f40303050b031202a0000e60840c0031510080c40001c2482c004026101003036400b80c06407880c2e60303a80781044010f080700b009040e030108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 106760926 1250 106759676 106759703
    0x31208130b0103050102270a140a03050102040f06020f030414010507020406090504031d010c0b0c1803030a020307020a0f06050d0914010c0206040614010308120603030d180213051012 80
    0x801c1060310a0085004100042e62200d150314041540512544544515000d02184032216100e6100c0c1c1c00480d01d19003240f400494141000405807410703684007600540c0041000f01d070b88141409401e00710341e220340032a24201390384c48210b078981c082d40c4030705142e8290300d215064040d40218010201c0720b06c001c20004140382c0707035030f907080c102c400c260b40680009555101d5103500e4007480c1094503240000b404c0c8181d00340ea06030b46400444100801800a049d00892514100d64124064046c9040000d082e60f84480c0c2c0d020009541b0380021200364802d01c0c0e41480050314200c4540c0c000113441d900e9846d1841c040c10b4034621006414011000c4031003a81c3ca81c07500c0e81910b0280b041c0e2960020036400750006007407a0411031b050344c644141d0031062590343c0004000096400040ba8851908d4101940c10f580c0c407000002d0450040c84081840581484031610461401009900c06107100300e0703822001e10031080f5108200d91080b03075045400e841348203051200c800c2c003d910444543c4201954010003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 106762176 1250 106760926 106760933
    0x405040c0c0209150d03030209120a030f02120909040f050f070f0905010b0c0a0f0f05060c03190603052509060e0f01060e010e0103051e0108030306030c030703120813 73
    0x641003800c003100014440703003a8200710710704114001c0e00306002481502035160050001010485113050003424580d000400c405940c840201e403038465000e950656100320182d05014200d000343d0000000180903090259014801c0c1c035050f181c9170b10340607240248641d240c0e540c1001c1d60620720801d0318140b19a810b8140a014200100c4000d409021321302006e032440c0c044000c05490041e0002c119010b414040c0c42c049083c0043c4035a00d01d504010b51400c2c0c5017140c00d210b007110b5003612002d06076016032401c1250030720000d8000c5010310880c06803054080552b05a000894880c1c0c04028003035041803d0360303001d0083d0743c0300710301c0004124051015080d560b07040400440f00c0a502800645135010104000d00c007a803100c00c0c0c010f1040342412511010081c00082c2075240b81c0034140d05041d65003001c10320b1840b116a4100c8003280d1084904500d5850b241402e80d02d13001258510f100780320724410a070f500c2c14041648800c40f41c2c0094106a05e4403188001d840c41080106220080d1005038400e2022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 106763426 1250 106762176 106762181
    0xf220f1503090b040b0601230a0f030b031b0a090e01090c0e090705040e0c04091214160b07030b03030703020f0105150603040602090102010b0d0c0311010c08090405041401090303051503010504080a0e06040504 91
    0x814007602c1b1440c5d664040d03c00c0150014ae202d98038842458a800159042c07524086103160340d008401d003080350200b0b045000504160080e4106c110f210345400c034001912041503010b2400d50703026207a48100c03c0d41d6070550300e0981c002110901130903001104100035500b40758206120440300c1500740c40c0f504407401c000c2400c540462030240c5500d048581040d20454001c9550b452801d85410035501c0c10030507446041c1d800c045000b004194111050014482038803d03400002e0a40700101660b0361010f081c20001c0d540c0f00c0040b00441e0039440d202c0480c0c42140c0c0040711104c0f040014141a0450b034454403014025001203024a05554a4108205180e600c600c1100802032058038842c5501d030440c00c00c1c1805100600d1154140024014044089510322007920106e800494020450380c0e07552400044010384440103400540c24076040008268258100a120b1410a180c050254882008150a950303095074094010001000240c0c89a031080307000ca40d2041c40684001c0c540ba0340d410200d0308 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 106764676 1250 106763426 106763477
    0x103050a06080d0206041a0108031c020706020a0c061104050d020d0f020d05030c0d020303130803040302100e03070303140708011e030c0b0a030f0902060f220f1503090b040b0601 78
    0x50b000042084100800034051f14040051030f080031b4020342c10240c1c0c150381c0e0700c501c00ba5144100818203002284507043c1d01140c0341c099002109545514600720041c213000c04100081720392600300803140c1c035901e40c00d1081d18111074005160110300b4100342c0a1011040c03000d4025501001c02000c4040541c44030b01c584000117118500440da20100c0703a2030541041d42c140403440c00c6400c10420b21a0760840601c40f5160f40c1e030014000c075030701d889030f00d02039140c04c0352140740c00140307410244413094030b40021015000c1c0705c0c00380e28103028074136008050f600358000454103000811050001800700c080f005440c00352003841e90140100c0c09813240c03039159410130143c1c08245c00f03000c001b600c07214a0740e25001c2c9640c4502040c1060250700040d900007000750240c1c89681c1c000b80030104c0c00784014a000072a105402c06094450071107162180007010261605000d01c04e141d01c0f0b20305500c681c0303520a03c10205540c0d00076110104644507542d803441c54000c007601036410004004040130240784248401c43c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 106765926 1250 106764676 106764703
    0x4020609120a0b0106200106080a02130b090916060512041403070b09011a06030f0114060702040f0606021603050d0503070c020405070e090a06030b0c130312030b04060b07050c0103050a0608 83
    0x503100f05400c86c2081c804d170414407040100364144001000300010008412145550469401c1854104000e48800030003036402c03980d605c2104038090200600c000309000900c44041040807041c02d84514040c3c0300381c46462019982c00c1c850000140110321003522800f10014a041964a002850745607041c0c086002d58124400c1c5c0d54544134000301c0200240c03604100300741550000c1c250300d404c90030086143c10510031200c12800d0207802030141c0e03031400304542425a000f0020004041c1c1122464010070081c05610054424118110059252900400126a4080000e0900e02520300c030403115500054544000e0102400c44440145d64a0041078840d00702c65a408410491180c00c1051107080a40031002d110301d012418800b01d1005405a940203210035401651502e0a01030741e42e10000307541c00070307044040850b000903c107940340c0c005400f050404c45050246544a40c0089000d2061300002049644065003400c10b03075000e03402c2181e00040420f000034102e99030b14402800c0011040095 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 106767176 1250 106765926 106765937
    0xe0904080405180601020c01030e0123011401020a08040909020109051206040507060e010914030c03121801020c091609090e030702121903111204061d0904020609120a0b0106 76
    0x140300c40d0a2400f0603003607103000c07000280f44600b0500000303134803680d83c500c41c181015120a0100148a003d400200c1e01c05c4484212404000303550056021b520028020502440c0520080c00065031000418005454010400c81d25192421303a11100400031080224140150b00034005626901c040310b41140e07003941005440c191515251a504241ca540c000303500b030012000c0d0058503644c3c003a15880944540d00a000e082d810348000107468090016442039151091010039003401b4100340141000b01c04494103a00c1c0b460f4070070010381e290f407010034100b80c01805950001305800d8400255440881c07440c14001034064846251038256594503000300e04035800011554114185500f9041ca00c1c020800903200d080c4072415554601c0b01d140b140601001403040d0b41c2c400290044c402c014040745403078181580c40b179842c070014002c94440d0008081c0c2c01c21820206a05082034028544182d0303000b0072241c034181e00c060411101200c814880c0c5094811201c41600003070051000d01d01805458481d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 106768426 1250 106767176 106767179
    0x50904030917070303140a0201090605040501020901020d1b03200a0501061802040302090105060318030703090f290c0109050a050115080d08160c020306040f0c08011103160e09040804 80
    0x107040320910002c0c0a400e003a4050807003007010950040440c0d15902d200ea5010756902c64214040b405044484809401503140030140410004150b00800e148182130b000c1d520030307500000050700c0001020041d0000c0d0124800440c0019100e9035100340103001d0601d00ca2107243c602c410443c505a01ca540840f80781e9518401841039100320000781507401d0401c001503280c1411035000c00c0845506114880c014013001c0302042d200340b4110510303c085035440c01103030b840700032509004015280783c1c81601e02c010780c45540841e90b5105101041900c0c004082c051220b60a1115100520f62145200300c40d10f5681e081e030180050b509102201d00035014000110741c8030200d084240522a4960062003958004c1441c0710a003174006901c0c55005000042c11300c40723400040820b91301e286250388000e5040c0500c4040104018120440d070200500031108110120f4a80607418200d980c81e901c82e203890300f000c1c8001160006200344071844018036251540c0e1448401010584614003034404449858002c0340 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 106769676 1250 106768426 106768439
    0x31112040605130c09180209100e061519090b0f09040501080c0d06090201050d020d1e02031003020d06020d02040e0117010516050c1e0d170702030306190509040309 72
    0x3400c2d410100180541d1003c3c40240d0710581012054824460030944501e00310420308658200c0164164000e042c8400794030301001c984030440584d004020030b0308031520201c1c04504240d611501c800301c41c04501898504400650344004841d5103021040210021000c03230a01c0c1960080d065603036440a18130380719682c1e48100001e80d50140c02c02100303640100d80c581003e40d034503490700f0301c2d1a030020800200c071401400100c40034490200b10f03003c072500005800301c41031000c0e444040e00a10006040560f1b0303821500c40700c140e12045d40e604016030b040040c2440985040d00610f060700d0b01c10b4a00614140f1404c540c00103a070090750102a800464500400c089100440c00342000d00ca207200030001498100000001d43d4000d404803020030a0104a410004804021081041289504200003106240d2415658107989075001d00002c990104550344000c00c001d60b14015111900a181503070781302418041180001400c1d0360700a54278210001d800d4898201180c0214040c2d90748008117818240c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 106770926 1250 106769676 106769681
    0x50406030b090405070612020403080a080601022b050c031b0a0201090603090308010b0c03070b0109051005030a0b0106030509071a04030b010602152e0b09030c06040e0403080402010311120406 84
    0xd10940a14015020880001d0000c2003032030a4a1ba241030518031041c0f028036200081c001c90304010140c943c005030962140e900408501d214240076030840e55200180c0d1207180d00d6084a240030001c01c079074200d00d01e0f1030794041c0010b40704080b540400c40e400c001101103010a190f10150029009400591300042996440740c0c1450107801142018403c808143e80c000742002e1051040f43c01e58031002c1003404410350280100d0714041d8120480d4802c55841e400d1230001030006680c00c11003800c50090000c4c40d0b060100b44156519008039a1101c82d0786041015000740600821120b854041d13508003040b03003410002c401201c144480f101303a4585055143c0b00480108c1038101c4c01c00e5620650007188030040012445030700c10000c54801003086c00084031411900301000706542440a5036801055108180300a0700500a0490440c1d004c001041c1c1880154802e40c09603122140980000801103809010030f0782d0068410302d000202c804032600b00d80460f8108a84415003ca862001c2c01300340111030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 106772176 1250 106770926 106770941
    0x121606060323030a09060305040c0e0403020c090615040911070c060203030105030c090f040f06150603020c0705010c0201020d030e0327010206010611250b030c070b0a05010e0c1b030a05040603 84
    0x42c0021440c113044440042c0802c03102d88150b004043d1550001802c1042c40301261b8020000c2503c0d80c0032900b440e10b4041d4407506100c0e02036006130388410018045103080c060080d00380f10840c85280c039003401d20f1030640c05401c110008501103c2c0c00c21000b070003c0c10414000000701200d5000d5034480d414170081605111401035103a108400a50510001021080c0515000f5511501d0010301c84980c4c94401c000c0c0071803001c0a040210800c90004d061500754006040703118141d070036071f24401d4440c0d00644a00403440b50190041e4020a01541424005c0c0e11604100824104072800d02600700c0d00e02c0030307400c201e40895030b403040d000980e0348543d6010000203000d00428240b805c010050040310f1541d9601814400b103412001c0e403040d0038083d40c941c02020180c0218240307240c4d240341c81100e21074258031100e401c98006941d00b001420b001040d10031780e81a00e1441c0b85014058903007131300303030003151b040104080340e00d020305040042d80000402c005c00e81000d4548a084c2c0f80d61a2407005421607119 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 106773426 1250 106772176 106772243
    0xd060603021c020901031508010b0f04091a190219111c0c030315080604050601060503061005090f0406030308150409110108070918020414030a051216060603 69
    0x14862505102d8860707403903401d0084103400c0140c0310020000120054415000f4000b11140c1d82900410901419081541d03020015200701580303407142e81c03d0104556180d032003d011184511071100000300381c14078403504440c0c0840304800702c10310840741004030380c4502d07103540303c3d04002d0019140184e0060000c0240c070041a01805444e003400312980441c00c0144142030810450301e02850400d40668030081000d0040034480017644d40703401c0c5043c1d45400c26641507a1500c6808000107005116500b120300c9030760090004507007605580300544054010b046915400044406e040c2a10b071181d2040340c00950282c2e036440d815080c8085c0200c40846540c00d910302580c01c100d00b1901050204540300c3c1031043c01e1034060440c0e55543c82c201d4891038503822098820a40c01101c01c640318160b0058015039508d0050707590316000e440101940c0f4083c030840249190800017455807107000d15006044a07040280140380c50b00c44a80e2004100c0d0b909810231516607078120442d80c409000d11003507503900d440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 106774676 1250 106773426 106773431
    0xf101a0d1d0a06020306060c030309010e0115080c060a030e1506011d060702060c07030b040609030906090e060409140d02070806070801030213050c09040203040f03030c0503010515031f0602030d060603 88
    0x359081d541c2e44885070042c0140645800001180a43d21400c00315002203000d9000c8c0d03030300d03400d010b00024080c021020f81c2c080c4640c02c10030100860700b4000200d000702d415a10080c692a80090305000c502d41011240605040d514a070341049030a0602080500151008200440d40380c00c03c009442c0300000225201a001c0442a444203034507000c003101c0c040c82d01110107a48404050034954035003000b03504028101a4040144020030a41e074206902c842e2094554031007541d200c090444212695125100d500d41d0b220700441e280342010f5002140860258070086030748003101d03d5492808110145a4005900800d010003480b1411701c099a000b40b5175203014440c81d45190002061408950141500c403035a42000c9a4010300910444010040250065443e4682800c00d05400d13001003400ba400709080924440081e48101700703d0781a00c4004044820714070303403404a064039810080241d0002602a184018050000d02e0a0401019154000c69603508000f40c16015211603600101c00d050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 106775926 1250 106774676 106774721
    0x1e05040201081f2105010606050403031101050402060f0c2a041104060905130e010c080402121f020c0708070902220302030304050607060221060109080c0303030f101a0d 74
    0x1024154081211341d0710214007001e0942403844980c05a40f003000500546ca42000002e460390040017400c00c80b8026190031034440360303402199080c0e5004540003580044100201603c0c000b1040250488092520031220040c0d41604008402d10b00e07220001c08482c011030b02006203203003a00804d4404821450810b050501e80100070b400d01100d801454401c002c0011846040c9a199000e0084451038100a1100846914000d08201d006603016400b803d062a290352003e0400101404100c0d14549a42d18200d030b564603950003034014950760903c601030024002000340c420420080034110f00c3d4401a90742c3d42702d0140e03811550502080c403a03c2e01ca214400c00240c2d0b0040240e9088600690700181e84521620b0301100034498102d20401d588800000c8a00e07101413800e140788541c0c2e00f0388880c1401a110f00c030407640c8025008406515900c1040010018840000001c0c0c000d03054104004c2030a80303403d42081e8041c0c00010f40030304400007040244402c0103e008811004cc0e041d480420400d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 106777176 1250 106775926 106775971
    0x60a021813020c34260a0803070e010306082d010b03030d0e0f0d0509040c0908031602030f0106240e10080708010605030f04060507021603033c030c031e0504020108 72
    0xc0f00c5e10074a2000c0407801481c00c94021000d202c1c45109603030140240741d5a150051001c0c12203503020902038002890054003083c80040010580d101a1b181100400410381e040301614403a00d03014001401c6548031040f450040d01c0420141c00c1300da408910100d501114004003138540601c503140c021b15a80601c281c124803541100449a02034001e840114680c410b204d400d43c0c05040541c4409040d00c000202041c1070707200011a00c568520807820346540c400c0d40c00115081e613480b030107254a142c8042c044092042d910901c8004864503e0904a50500e0314074001103070440b0810307218011441040400280325402950940500300d2424058118117091381c181d031821400070070003000155514003042030036008003d90542c2c06032240c41c4258050304d030315000b811502029800c0100c3d00b003181e0850a00c0d1309000b440c400f00307099443c0782c1c0060f84070042c045020700b1011a020003070554959030b050100000d2010140354074281c00021509041c030f4400108008002440a01d1b01e81e452075100d41c84 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 106778426 1250 106777176 106777199
    0x2210c04030803130629090c0915091c14070603140a090606030215120a0e0c091b16120f020c0d050c030d030e060a021813020c34 57
    0x1141c070381c4c101048a040d4501d01a4020910503542c001500c00c03d620110b0840030851305007424107403e90f940c1c40c00d0b803075401c00c0c0240ca01558410a5105016101042c0c03820304181c05002d4801000301284070092845004e0f00a9520000007500c4500b244c1c1c54038000010104040e40c000e10981c50704001103c5551a0400b000002418100000381c4900c0c004060040b5a0088806907400500b801d0209403503518010856200b0502160007181000020300110700900c24656248204405050366003614403c02401d0b003070082c54801c001c05410340c0c181030030003103030050481c40317680400716030500d580f906010b44000000c04102c010400482000c241c81036022400e411040e10236500c50b1518034062034001c0c10023801005454143c410610303544106903041c0c0003a020921a80300780e422980368940d070786050b0311074442c4001d40c2840600d1a409141849440898400c000303c2006091400045003942050347e01009845601210089840300ea5400c00720002d59002030305140104500d00141842d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 106779676 1250 106778426 106778431
    0xf060b030403020f03180f030109050d0809011425050408070609030218100e060307170c0111070b041e090905010c1b0b0402090402060f160b0106090806060f0f030102210c04030803 79
    0x4898406182c00d40d40c0b0b02b5040100c250b0307803150603603152460f000790007040d001048500040c19070910040001d84001c00707080e40d014840c94010900d450050303442594605030506c8040d02009420440010701500900001c00604881d0743d501d4801865401000038891210191070405203400041c0206030404804000407218141000d41e40c40da2110002402c01005a004a820025542c4003401800c40458107000041c405d03201c0c1ca800304c80c80c8114690b035612600489900311801c22062050310540c03124000051440390156841d10780f1601241d06441c00004103c2d60350391101c0a11b07840c590064544e0b25045081c0c508080c154840d6111f00382d00d0080039201900074000d1300c0c003040035903c42608880440d4003c2c03034626a192500100b100c081000d2100a0f110710b5116800421014400d9201d0400c880b4084010326542c1c0701d040802040c80032071819158403860310690b049080e2000c0c0050007200d03001d10380d0880705415841d0b4444403d240104105c940c82000c00c400d000040382c000546e0f4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 106780926 1250 106779676 106779679
    0x1050a0612020d0201050c030d02190509060a030b042705060a0c090614040302060c0607170609150a081222060906050a03060e040c05180105030c0f01030f060b030403020f0318 77
    0x168180740f500060b80d03a40f040c0e800c2110580000038402c0c035500d0040d001890010013107945424282136103441111540038401c1c08540c0100c0030046801050301c2500040029840240005284202ca00ca0f0039120300b61203958000030031000c000c400038400103003c0e1a0344034440710814010015800b40042030189a40030304c40034000e040140701e114402480696024590240546a842c10000b40265580508032100c13400601d1f000e690484d000078200c03c060145901818080d40d940328960804225240c4600b01d5400200c0e000d40051080420020212020080003502ea91041c0304d20086c403e00340448a100f2100311100420800395901181e5001150035525142e07868020303200003100544110b51050b141050a50240400e00030010400b80440c0c50854201c4c242008551600ca68080d0074462a0703456000750f183c0e0b0300281440864642c0401381450005040d61820b051030007182c80d1504502120752000c0301304010160108140034084c4000760003142082c42c1e00521000b04c3d42403c0c0401d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 106782176 1250 106780926 106780939
    0x80a0605041208060a05210102040b09120a170d0b031b030d0801050d0b06060c010c050d0c03051512010e0601171515010518040212061318060902010c1202060901050a061202 76
    0x629443d0f040401e9108800c03420303802550f0351a0f41c0e154004bd21b400452019210740100030141503240780005480c013550381c4c4100e0500c1c80100031140c0720116000085048502c40d180e01c01d944543d41d040c00340c40340c180814541d40c1d45007810343c030905107010040072440052069180050000e80e64019042d41c00750341c4241515800d5981c000071030b4150154070b03003161503582000681600c090b04400a0280e00d40003843c10400240f408030110b00352541a102a102c082c8050458221070500000c0e4089042a46001107204040741d11610b2412000341c0c4080091400015020789a14007844140340106010300f0013035280c01d181d014207031903241031030788181484000030b126020803008a14501e80100c0041045440700a000d250702245081146c08030310900d40c40c44c030044104164494000104034206580d080c600d490f43d5000010321501d10242d06006001d03210100140bd003900d4540c0d4054958050000c0341001c480890950340c0140c0b10043d51410001c040c40314400c5803641500058049518 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 106783426 1250 106782176 106782199
    0x1505100c2009040c0e06040506010c1419050105010f0518070e011704080c012a081005120a1202010b010c080a030f05011401020f0f06010b0d06080a0605041208060a05 73
    0x80e0352148041011050304190b110007007000348013910401404403482903417980045d070358513820030040300c40459129000c11507803001000130070702403e41c2103d806d038404111440c1070210f08160b8445400b0358422103a5079110401070010308c0210741e100009000607075100304016103080c1410385402e001490b076000c01c6075144031401207a200c0c108501512001141380f00d0f95081c5810450000d600400d03c00d4043c0d030a007901c56540d6511100c3e0111803d041d11521031911600780c0c2d08403090070004e0204520903254000210703055546000305401e80990030010400401540303000712029101480d601d007964981744603d0380c640d801c110f4408405a01c0b07181140e85102034041079005100d1888418242440d0000200e5039555140340c0180c40e480c00d800b1158456a10345141e540c603107207022008255004400100b0403403210901808004030954030200d1020b446920aa1910341d8010382034030b415807168144803d0107070b56048441c207160286030200480c44c2c02c8010401100d10780c442c90b4020104c6105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 106784676 1250 106783426 106783463
    0x903130b0f1b120d0c02010c08010b0a0f110d020105040c0e010b030a0f0e10061a0c100b0a080f0c090a020703021203090a0605041a0c0406020703080d0e101505100c 72
    0x1c1c4900030410100f45512103800d1030425000300350b05951400558600001c1d4030180d80540d00702c80c101ea50020420745010381c80305085403c00f5240c01c04406000135104001d42810091010800d862150b40c00003a03640b13032506002403030308003503484129246942c00040c4400e0b950700c001c6943c0003c0100011070122080b00d807038070081036045421020703409070380c1010075039006c03e800200880b02c03032024600c1403001220608a00c0d01c80d03503428406a9001c81804451564190042818200e004040c1480309a82e400c50034144542140010702ca50081003031440a031400c02d540230b1304062112800c5040101c1c90754040d56030301319280c1110980f4008400140e8601c020408030400f5507200d0001d11441c00d0034a05101d007038a80b01c03084031000c100d520000c2e99210102d0266001c480b0154024002a461a20755014541c000c401d0007407030030b844440d132290000c41001080300f80940708500007084221516010b010360781581102d4415841d241c81c80e11890303030144031042c94507000040c4041340600b112 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 106785926 1250 106784676 106784683
    0x60c1a040222060f06050909010302040e0c030a05030405090109060605120a060f0602061b2503051b030c07150509281205070f060c03050a090b030903130b0f1b 70
    0x805400100400c142e10304800300a41c100c001107515041e5040440ca40b20102640c59000e41c2c040d2541004600b80100050b18180e003100c03080c3c074802ea0654440b0a80b01340807034108001d0500a86e65540009070400081c1482c1c820540145400a030402071541450401003031841034422649a110b00b41c0c02080351501640e100100500003d440b841103103503501806503c0d0801114103d1300d042c103a28402000108030700c1201ea03445444101d02d1215001d0b2420b40b0500c1c00d4402040e4100001404181508456402d00748442d0a0400095444483c80c0007038130720340250f0303810204459072140030000d0100d0b0400c041e80c41140d821100c3c0619804021002c6160745201c500d40b9400d07810702900001e10500b0318030540ca03054040c4099880040d01e0742e144400040e140c0c1b0411000a044060070404244200003601701a403503840c20a00480c0d0300c0501d108590000e03034404005400004034060b00c801c0e0103640324010804400401d0a04072007060301c1d000c6006141100b4505801b07020740c082540d1061 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 106787176 1250 106785926 106785949
    0x51503010609090623061e060412110d0c050f040e120406080f04050c01050a0e0901080309030d0e030c060715110d050601031b0e0a03050f030c07060c1a0402 69
    0x180081041a5407400c0310005000d6144058840920b0100b90000765850100c0c210300004040407002036503110281405840c0d60704c0d18001080c0c45020190700017a81c3d40300c000344014400003410a020b000e445c1800720088d840003684520508000100c40300240d001600c036021114100e402c08110705403000420040d00013008400094090166600054074a15024000391250350351aa42540c0e103c00c280c4040303150a4070040c20940c801c035402c640310340c0700e480107020912151030210302d000320450100711022070a030010000c4e03400101d50070030141170802000414481078504100300040210129465408180b0603501500001961005201c0c0940405c0640007444800b0007011030202076420064101c15903484285040034042a440d43c4070307010342c182010030320411149030401c40c032060300e164240c90320041d00042d00d42c0000001c22424414000018803030005542c3c0c5140c21505281800d009410038014443e540c0c450742c02150303401503403da039490b05200203813043c1c45e00e0000036200380a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 106788426 1250 106787176 106787179
    0x2030c060405060106080106020a0f0f020a0b0a0206070e0102010209090402090a1e050105030d08090d20030708070507090507021e0304120302010f050708071211040510090303020c060a0f030515 85
    0x104028402003040020b0f065048440da980d403500e02d41d8036804200c1c3c403014420700c0078060010254120340420041c044503801c00344002c00c401c1c0c01c4c035982c1c58030401c1030700030040700d2025030050802c2028803a080201c02225810902c02103250003d4580040c0244c0d40142001c0d00a528800010b104100b490348226880603001c2d804c0065086a40b8014014080034060079000e400b41e0b04000c2c44003409003000710701800c0c210740581680c000680c4103d41a401305103140107175007a070b944800180d0710180001d00019028034461341e03843c0c2041c105185041d0441e44414141e0340307404e04019016074081000c150740001184404070030130230b443e00c861540c0500d40040510407810581102003540542c42810307c940400740c14489540c1e040f400742e43d4401c08032380b4040880c003e0740a03c922038145500480b256031440405a0400707072200081103000c004600004081004000b0a006054042169080e04041114007030f05e003000b030079001419401c00601d10014580c076940803600041702c010b11074003000390 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 106789676 1250 106788426 106788433
    0x350102120906010f0602120405010c110616170304021804030c0219152d0311070308040c090204060c0b130f03080a0c0804081e040e0f0a1404050d0f02030c 68
    0x240201c20030340b200b0081c89000111225680002078490022504204100101300400d08103841c110043d41c00e01c0c41c008080350303401800c49813040150b84c1c81000e0907401c0a43c1d601c0003610072007481c0c480410f214540640040c60010310810005981d4401d0302c540c0c8406940d10302110b500da5190586540c105c0070740c001d6100c20002006820900c203018010120303070960340000380010007090280c407040d50300000316424002542209540488415100e021a6050710340003500300c05040c41900943c00c10b4008400041c0d540c01070105002020860b440074010010086141c00d01e001c1000d4442103c00800030f064100304000031380840704400040d407126810001c000c6180c806450b004011580c1180c0e0b4000c600d01d015103020116200796036051246038051101c0e1300d00540e142c81000011549000541800000c10000c10300d0880c24a20501030364060340c091140e420800d04080549407803010781e10301000c540c020403010520001d000c00605a403414081c1c081001c21104034214416a507100c100b512 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 106790926 1250 106789676 106789681
    0xb030703050a14100e10080304080a0c0e011508040218191a06030c0f09030a110a0506070f02120715111b0108010306110d0603030c02040635010212 65
    0x360540c01c814490041c010703040150050382e200703110103e14203a07558080e0310707036502c000e00031903090060b45504041d149000b001d0141e91001100d20b50750281e044112940c121950050801602400f02c3c0f01400c0a80d614003c55070500410000d90410b030f1142004003c807503004141035450700101054254401c0701807444628003642d408000c2100f04c54505000c40c50805141e0b019030b09420ba043e5220030007000702e407442d2100281440250054045014071110030081103c4940d4200105030100380f0583c18034401c00c40710000c102c140c1034568001c40c02690b04001100014401c01641c89090345e04075180082d07002c00040f400d2505e001c03a00140014014180c100700b4454000c4604100c512800c0100c400042c0c1009c00701f030301105074050403808142080018000154240c114407d54004142d00c54103122500c003052003610100d80c000e402240380d551081742941868090742019000b448520a440c01c2d9520100584400404100200505108040444030001e4044444440b41b6210315490750 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 106792176 1250 106790926 106790941
    0x70803070c110a06020a0803060a09090507090c090b0703030c0210060f0305060612301314030f0c01030b040213030c05090108060610110c030a12022404030f090b03 72
    0x3050565016a4807041d115060740b85480c0885001d030a4400da94003400ca000c1e034554500e039054101a10080e0b108855120114050400788140d0041034041c0005282580c58680d11030b003156001070b1560104801c403d8244904140101110311840e8145000505200c044c8000c070b0a001c8c000e801300828034249640010184584856601a40e0184c400d943c81358071400b040002101402e803d00c59643c01c1844252000147d1303910b0300c942880c400341c0300720112104925450a650290036615200c08010109200d124480a001006001c0c103400400c0800390b840c00780350352002710101c65410561110100c0b240e40d2980d80645486510560ba00d0528540f646031000c1d01c25003034056140101185400042c52150001d2501d002e54030190180700003054407c3c0c1124010a4000304141ca44100644007803aa107042100600480c020895114034208200e4008d0800001d80400c925842c01000043e41905d11902d03241c0d002a8141090303518800d01940654900c0d4032540310300c230103c101008221f440d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 106793426 1250 106792176 106792187
    0x19150b0315190302040203060604030624061d04020c2802091006080402060f07022707090807151103160b0604140a0908090a08211903090807080307 65
    0x203030058140c1d0310300c030701d044018050a02e054800290751464403400030409400e00340d00070740d00250094a42c40c6030070f8807500c42d07000381c2d504104103812000c0e44200d601c1424061940f0140500118a001c43c2c0300c2d494103115510150801000034411a8000f807070703510000d0f0170410020000129140142207200300c00750401000716103e0b0582c000d401315000580b18082d070000103810707281c0702d84444d84580c0b11502880491340100703150f40c0b82802c040010802603a82c071100080c4000d58811004251200d61080a001754409007030341c0c0901600031070601c0701340d13000b01d80c04090310941880e1043d944034000e0100c5030710180310f00e010b849001c0021180803210910310540d1117030b0f0142c4070900660305e07240d050000f2142d0104240458105071000315a207200260807440364240920b15450520f0032040020b5801100ba91001200da800307205071140900c41d080300c030501c82d00a01380c01e07800c124518426814420044101c0420075039074005050070411920181c0305003c2d000701102c1d440f0301e00420003606 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 106794676 1250 106793426 106793431
    0x70807200a1403030603030a03020a0207050901180b03120d0203040501200705010b0102070f09050406090b15120309010e0d050708010603030908010b100518061b031c1419150b03 78
    0x2c807aa580500000910740010443c0c1c040c42c8080c004614190040038120025045458420114000d10b08001400d41d640300c4000e01a00c07060710035515074081e40c002c5c4011504030f1852a4002d0f0802c1400c41802a0204150741c0f001c01d0840c0090307a82d9403907103801801041c0510b140d07011924528241d0a440352103401402c000b42c4200009c10003a820003005999070f81c01485003050340310241d001404010b0090704120380291180c84089aa031400341e444900307200084a013101380c0101e0051400d403501e8003e584003a99807800e00610301d00800c100008040e1004060054094000d0030395503020050700b001020000c6c031040f402023003030a4491400600e41001840384004039805c000c2010a586814030403411410099280c151500e042d00c65201d00e00f00c60701102702d900c0001449194004482a0300341e0108101c0c1c000615540e660303640303100c03840f100001072035584d02d45001020f020600340303100002d40002140548207a0200740303020f44009010030f003241c0c50b0444034440000074400e0503071000e1070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 106795926 1250 106794676 106794683
    0x2030903070c12020f0d150504110a050913080715110d06050f090412030603051609050c0c03160807051006060e030a0507090903050c060709050a0b0a0206070807200a 73
    0x8000f955141c010021003d1060065030004c05c003801c0d141340349840c00f8500c000303a11074031402060003804480c981c210760040343c058550179402c292060b5180f80250342c02000e88021210140a400c0c400c40c0f6408a1034452001840004000b0b6488280b02d5401811001005040d000348148500210040c04a4020f4840700d00c9090a1560129143c03408070070030311012001801301801d40d90355446010054642031302600515035035000c00320100d00d003400380c1440426036000040100b40380c20020002c80e0001041d00c2c611040c10310000080c04000720849105a0020000815807140c0d800c01c9503841c85440c60080135440f03003201c0d007514994190070034002c07103516880c1d2418204c5401c0916032a81031504001341a034018110611003c40203034080308449000385451400c00c01054105417a1480542d068404620410000c0106140000c0d102d0081d0640303000d0179081c411841c4029660301000b610300000c2c0984000041d16041c8501c0300342003070f054440c030f8a1440c50303500ba604a4907020b403ca0b065 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 106797176 1250 106795926 106795943
    0x2160b1c05070f12110708040e0601030207031e0203160605060907030c090e090c040501030312110901090306050a110d021b0a030206040206030711070e061003050105031018060203090307 82
    0x304415191480307071070b108560a84603901d080d2948a412102c07440703032002420040d942c8100c6654829440b1020b00081c038401d441e002c0e41c650405903a40d080000061130241090b00401450001942c010b1591221800c419100c500034035540600340d0450003811600c10b144114000f0400500003560003050044006035048102a00c0d034020480503103c100500c0c5010400a000c01c00c0507018094806900500c180c050740c4259150303a000030181d510a0307000381c00040300c0303281c1224a4040c0c5d00c03c13181d000d40d40d64401482d14012100180c0706d07204030300c07002c0c0101d0342d218005055025950080b9040384c44143c10155a00581ea00d00342c02034100202c1c00d841880d0112810118490002d407000c00550160018841030340c4540c02c100e0540c0c001007081e420403da0442402a0500421808005d0301807214820b07883d20b00001444203107091a14a0ba042500b03101c010070040d00c01103042d0701a20000600400d003020118502511003100c4000101418400002c00c0002d81001c000760100c0340c07050404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 106798426 1250 106797176 106797217
    0x80901030f0606140f0712020a0309140108190b030a080406021515040203091603030e09070503040b070e0d05030f03150a0b031f05120a0201020f15060409020102160b 73
    0x4011121207006030800700341034034015100010444040d001ca0b07603017000346a107070690302c3d501c00566030035688548000d607100c804110704047e00b140320a0f0107403020324540c00321072019000081c040e0700d000d45085d01800b009688a00c0284d020b0304181313a1441c01508a6021000f1444e1100b019802442030700014055100c51160200031480c403c1d0144101ca040300e04a4800007082100940c4080c11898031072042c40f543d20001c43c40d0039081d0000314004c0d200e100308600354005021017031a000b081c1c042009004c100b0400001d0b00400c440703030054654944241010000f0001c94001640e02070050420f10001c40c1074074a50720420700840c80f5900421050401e00204014000c030f043c40e034080e080500c10706100013008806d034080d152501e0f402e0100c0c4a07440c1e40d541c07404144030181120807070807940c00494a00c1d065503010080d082c1d01010501c000c00c42c8e0820840b00703a1980c1e0018056602c60f540b01c0c8050800e40e0701c00c110290300003285000c81080d03140c1e9401d16107040c2c3c4c0300001509400c0c50203d03a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 106799676 1250 106798426 106798451
    0x60b12090d020f0703060b1c0602090f0933060708030a0c030605030604060207020d0213020306090903090a030314120106110c0103050601050a0e131a090901150303050c0f0a08090103 80
    0x1941d095030b50f986001014024115541d040141c02c0c0000c10703e0b0021a003d24003c1552030070341d048036815015000c010383e140d04d680c082c0900301e44a00b500c0c41c0611889028042c0d5001c0192041c1c0b42c91900540070340d40814084144400780021a2159a00c600046081c03030a2201d0240194000e64040200b00325000c2c5040381030b0152038a40c40396680c9500803c1c002008110142c000300481c9100602c5810440c041d58002220b4520011f841c08003541d02004122540c04c012038840c1c0c011400c10700a609001e01400000e20080b4036010050402400655408052007800d00340c507003405141c000c400c491345c1c540134001c05000200450000500c41c05e5030200141d4041c3c030441e80210700c103079980707460041d01004c03d807640031208d40c0c815040001c03403c1c511503546441c07252101600070f40d81c910505030b104c03e0402c105440b028041d585d25034075064501494181296030300085940c9428030301e4030792400d0b560682c109400840d691405000d5003040b5410040b5010080039500006d8130100640802c806 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 106800926 1250 106799676 106799683
    0x30e070e040308040b31060c0e031f14010603090210050414010806010c0f03021b030c060d0b0112090b01030c06080603060105010302180409080301080706081b0d060b12090d02 77
    0x76005004a01e40501040100b0300c0007920581c07180c80d07002d00d030800d00d00b075407000c1c203040c4c0403403070045d417640c05400c19481041106d004e90014514039160111250343c040300026281c5c0c119040500009484080c070340035214481d0090700c0c030701039a040c0100040d80d480e84084c0107402c10003400c9100e0040c0011804829002f08140c40503642c241111410f10b411010041d01c0e0700c4805041c070ba060144a180750780018100c00840b00789035200340c2c0a00004035400316a51034411044000078130039080301d241c0450700c0d01e800b0241d0301000c50400e800302c1c26025100050391809070510400c40e805040011b13140030312140400640c102c0344125400351001e0707034851049400d80c01c1503803120351581112004000b19846900908100e20342c07820780d1001c54036948009021195444011500c0080c08401082201070520000e0020040360510241c00e18040300608214900c20400400e4050081905540e064440e031158001e8808016403940e9440008240c040c1c0000c1203070304541a12405107001c640c10b2010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 106802176 1250 106800926 106800931
    0x5060d0b13030f0203032401050f0c010b0a0501030209060d0506060909160f0c0f12180e010f170a030c05010b060301180522080d0f33140f0f10030e070e 67
    0x91041d02c4290707c0241c42d1881110494aa070400c40300380201c0009690b004020240050010000907000d00c8030424443c0c81c050b00e03484507043c94418030000e03210340c80fa40e04440a105514400264545c0c51400207101c6010f034000701a0041044400c00c04c0c03080c48000c821902c1c1c00240ca03a0a46100481e60846003c004418001d004182e1038110704002015640c00c2c400740f251500349a4011900c2c1081404800d4480e130020800290360801004400b50703001030a00039240802d000403c000304001615901c03102504c0003000c20a0344ea0009003800b90070360124280c110003c00459a039655006558070141c03140310106031481c0b4117004150441035510140206100d882007403c9040490b446520182d040302c0c103080e91040d20342c0c0080c2c003511500d20421190f05007181b555022131803496400840f00041c04e262008032480341c4002d004505400c01001201d1604490034402d60b2052000710382682c440c0141e55400017a03210b600140c40d030b00341d000b80b00030000c40c004030b0380190741d0380090760f210000a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 106803426 1250 106802176 106802191
    0x708070906150e0111060a0c09120803010b070c0f030c180b1507081b0604030f02060c0d1d0109150c05030402060d090c031e2a05010305060d0b13030f020303 69
    0x158860b0426030b402443c011055000504000e0008945507545604042048a00301065507861503568400d5802c460030030302420700c0e101e403502e030400300e41e43c2e4400510043c000c40015880200300902000901c005200207410b1f01c800b034011440c0c0d00c0c0b0b001482c014480c080c114001103032101d00d00c180034041c458140f00100c004d0076460440540000240e4581c000f42043d95202020080c0380d508100d90a01074803052070403001840c044c0b516003402441296180d0112045402807400d0080342031070740085d540200f07049800010204040d40c0401c0140502204031005942020328106c18032480c240e00f00c1c2880400041801441c0c0c20403822501480201d800070b60180040c024100400155440b010540d0311030541c80d441151680c0f22025441c8448450640c10320b00d031003003c810004450040203c4100b07d42800d00040b80a41a0100250142c02038504160b41c910020308107070380d00c0d104802300c0382e040440c0380b0280c107003100308c003c0c40c1c00d20700c03130580215052846181e44a840001120300c6030030b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 106804676 1250 106803426 106803449
    0x60105040e160302011809020403121704200619021b0f010504030f230307052a1002010615020703020306011d04060c0306170a0203070e0c07140109060c020708070906 73
    0xf1070340155412030500c4089403103003d03468008180d0400b03c1c4002c1c8081e502a40c0c4100d10161003600081030300d41c1c6500d0740e440d105610014440090180000c42080c001c4c8041d500c0c40c507020386008107090f4010b001100c003000c001c9041d004e08580d00807d10b4000c550000300c1d4040b00d00751a4040c4040f56a89514142c00100204010800b2034000d00c0103d80312441a030107040030210a03240341d48010000440041c8980000400c1000c21500b00a4522071185600e228458105c1c40707458a1140702c8035140c0c85024800451030101502d10070b60090300500030784102c0b441c8284100b04025610006404124000d00c256400403032580884092440307a00392110f50b4007500ea4542d604c030350160046130403c0c0705240d1500008210400c8001c40e001400c00d400005005500340b0340100b61510360103502400803803000c20240720890320701c00c04440010390069585a10070440b00c0541c2d004020340e0b90003030b10351450107586211403030b40414442c007290040c004a404494480d024101243e1141c41014610700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 106805926 1250 106804676 106804679
    0x6030c050d0504061b020d2a020906030109060608030406030f02040b0415020304080a03030b040c080c0306011b0506010603050117010506010c0605090309090c0c0708150609130606030302060105040e16 88
    0x241d400070343d4000d221382008030340880d4291100c0a00c0901840341c8000d80c014410880681d41d02c41034034045031502a1200d08980d80041c1c1c40b01001b0320f0341c24041d01440c69000000c103951003d402012a49038856010842d01e55556202e80d1250014000c1e500040d0420382c405040c0364640c000d49d016a005400f07110301d401e280106140500005030080e4081d800207100c0001c0b0b0303103414031501e1440c80c041d4402040340c60b08141040300300c4403032501480c1400400030038408000c07d0082504d81c007400070708140041c006503450190031800c9254000704076202d0700300045030865154222074100c03040c0341080c81070606c800031030714243d5100f1581c00c0c0c00104182d0b81640440d0454200360b402c42038100640c0e1500d066070b4007280c0281c40807102044040310020382005c48030303010814100281148405408030790184000c0b4030070707100f018111510400152000c100f80d5103150303a00742180d940c844800c1044550320300c1e000e510b42009200d413a2040303107006401d208040c400f1502e9503d10040444820006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 106807176 1250 106805926 106805947
    0x405030d0516080406020c0103111819050d060b040605030a0b0a020703050c06070f110c0109050d0611070f2009070f0201020c070306090b01120c170c100f0906030c05 73
    0x2504140c41012002d031003030203010040341c2d8000c014000382c28160302401a5032003134030026040e00c24901080b000c8502c1041850981d007440c0c02c0303d00b801281118188e00c1001d000c201c00c0d0600800d80c002c01d92000c18041e40b00d00300004d13940b0000c408607050301c05010003661181003548496100380083c1c095046040080c010a441b41e0041850318840c4c10081e04098180e107035149003502c21902c0c1804600100065032440c0e40101042c484561072100030f211084100000030040140c03482040e0043d03c6480d1100300700660358000c400296582c0310415128425800c11035000c0d0000c9205848901a50502e121030014030600c50710038000180070302c041030b2114402110320f5142a40c010045540c2448078074804031003800440003d60060002241000c503e041c1012481810b81c00442c201122290042c0040c030b00041e14000ca9042140026403101c62442072424501c0314140d142d0302c0400140c6029084e50070920007000c100c0740f0344c0c8099105494503000e40446802c481070344081241030050317038000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 106808426 1250 106807176 106807187
    0x304060206040611130b1209070f03150f020a051803060f0402010e0d140109051002030103050a03080406020d0908030403031a03030414150a0306051306050a0612020702090a02030910020405030d 85
    0x615818480b0680b4200c150005c02d031149407950469581e400000401c1a0700c3c0b820f03e0310b825003240f10300c0044c000c032902d4502840c04d4000c0503c80184034040489004480e804550320202d0001c0c404d4406554881d8100d10007445a48150002481c0100060b01204107040014140e44550300c028100c024680b1070fa001540c5165042404983c0115080c0f1100c00280c5210381900c896032046002041c1000030346429824014120400060184103000404c0410000201074007960303054209009207859908201c13000c0c0c40381000c0c40e0200c50074000d054040101ea003005500c11130180e51b00b0090340b9544080c560740c05048014060f4143d0040c401030048007402c02000484010081c90190f840400c9070300c2c0201600002885008a991540304000e50306000c4480704042c10b00c2c9000300041ca042a0004008410720f02035101001341c1480e02044203400c81d410ad489040d0000c0c11600a494050340c000041d42c01228440c9c10740c080c3c0c0942e00c2666480d4001c2d00c040e90401000b4100b40c01115a0440b03d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 106809676 1250 106808426 106808441
    0x10302011d030c031c0905030a08040303180e10030b0c031009050603100509010209040c020d0c030806040207020d0507090b01050c030403110f0604060810050a03030215070e03031206040b0303040602060406 90
    0x18140910140380e003c0382c0c1e042049090643d444200c4050180c80181c024202c5c951951085001e60801ca20b0344001074000f5003141d050300d0341400c14081c0b4040d801c10303249820015030801c08000e264101404100c00c1f030b442d002d20880c0c0c82403800d0a050b9590303c80000c00d03130109032480020b4074058401030250312440d402155101f80041c0c12504281d6240380d141b42030b501c09840c8543c03a03950004051469042c1400b0f020071120050004250591a205004002c1c40755800c016040142e04000b0070029520f6404452900c1c1c0c00610f5070140d0556420083c0d120281803149103c1d0780d2814110321210b50240b01501c4074121003402131030800d132a5464180000c85a03001c00c5030700c1911503040360601d030759510240c0083c5c0482d036035510040c94540d03c8512180002d030030451180743c10100030400030742d0010f80900d8043c80c14038040c0c07298a40d904140c414254005000340d25000c049000d4845106131640300748243c1040300c0c140181c06500040c1900c0e80f189016050040c0c115200040116400303800000703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 106810926 1250 106809676 106809679
    0x9060b0d0e030d060e09060c07020102060a0b010c0804090e0610060e010c0606050d0f030806150315131b0e04110906180a0e04051b1e040e03180a0b03010302011d 71
    0x3c0c50264403001401c204c420a40040401410440070f00ca0944001c104103a84400d412900c1845d03d401500042e40d501d0000b42000d03491620b8400c4501d482c0d01c51008051786030351026403551600e40790b50b200d0f0041c01001c83c90b8210741c862a0000b50104080c8200581143da0319160401440c070300c03000444541502c01b1094030803580315003001415880c1c00341203c003c00c1c042c495071800c804036450002c03c00c51029107075501c500c55010110242001c1103084a400001303280c0f403010160085004990f40320301c2242450880b40c070300041d801d000707499010a94074017080da684070225422a54200400c8a14000f078220851805106040e4503013441c5000380b0040015420b0100300d14a10783c00191240c0c8690050103502590106020400004007d14180d28207541e2013140e500e29150042001c80c010304036085880c400c0b000c0240140c7c1c886600c203019010340c50341980d9170788405111340000300710921283e50040c07554000000e503440750842901d058036416900c041c4220307030f43d40d40d420790002d900c032056 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 106812176 1250 106810926 106810933
    0x9050a060c0311030409021b0622020102010906050c03070201060e010b040e060a0b0a050901030c0c051002090d05010e010506030d0207080d03050a110a03050a060b040602031e1908090709060b0d0e 86
    0x100f8101c0810000390004007a45440560b42c0d4520210814603201c40d080103d001d03901080c1400050180c015083d20b4040e034010a148640c402400102d0150214100c041c01e4580381030240708050380d900e0015442000140c00030b10055035940050340800710244165049602d062200744480240c04e076141782c01503402002c01c00c80e951500346509440e4030850a0f04041a400a10800c0a58150088018982d024203040f00c0355a0140c41301d60716130301802c1d540c000003a4001130201165842050f5078448a81040003008801036072080c0070b00030a03041d544103100740b00b2141300e84220703840020f251046e0fa07600c4003d40108001c2840c190041d06001e000700c080c087d280c0040c4003402800b00c1c040e0107981d5003542c0125050034241c403010100e402c290080540707180100f00038024241c0000442e01049071a280720b2025007034070380608a441c041e41d24800d101c182150807040034075070703c210058014240359050710030703841d6512902c40032112a84220a8034036414045500741752401e0740031030504284001035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 106813426 1250 106812176 106812197
    0xe0d171317071b030203030d0905070b121806040201050a0f050409020d0c0801050604080a08160c03080c06060f011d0d0b0703090302100c05070f080702030d050705010c09050a060c03 80
    0x8500e5070303030740e101c0c00c04203003210100e0305a05100c0108a00c15045844045071016641103402203074480c032074402c10103101515403520f80304122040005000a04e044089140c83e02000324401c6140301060351044055886032040101c0c420300895640c1c061907050f150945071021000d416248100081613410a008040c04005060651400200740000305040c000070211401c007405451440d041c0c000354050700c824042402484000a600d0044540007414182c42c0c00210701340718007070b075000b150050804070740c900300004010b440000b4255115256007034a52540e205400d00c951101220580750020350406200000d110f015107248911040141c0745e0013102a035503c2d83d1002045c180d4020b00001c0c0e50f00555018141d05100110380b080001074280440300c0e10340b5004185000e0b441d0041c0821080950394010030800008407911558082d06488124080640c0a1b08a40210000740c60f036508040034040d45500c1901c0b120143c503001030100b136000b030518404441c40e0182c1c08040b024002034103032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 106814676 1250 106813426 106813433
    0x9020d0203010e1303080c16081305090a0b09010e040302010207060c0f1101020f04060f090f0803030612010c0207090f0e01060f050a0803030c0a0f0c020915040e0d1713 74
    0x105422205450050790365494035410620200c802803c072920044001360130b200080c0d00c00026900016043c0074140c448804400c1ca003140211741e9401030407004009030003840f01c0307000b00410084600886400201e5590601c0c81002d8800c00c01d541948864110010b001d4052107484042c0c02501902c00141405c1c10f951340c04c41200c1d005814078001c60814409220706c243c1c00140c428180280c1d400950420b0035022041d5024015805000d0601003400c8038003001d81d124821101c018003013058042000f95840c0826500c907030043c0c4440740201c90701114251149030501442d03000c603903d580206289850301404000070102d40525074840b40c0c5801d039003403140d0070074000c2501610280d82d8100b20145810104060854940d2110b01690400c1c000c00560703107040c1e070030384400320940d0505511a19803404120b50128401000a40c0285040b05002c0c0d001442d140c10074003040192000c12183c030344500740329a190315a0000b480001c0740c04400044d03844400b564103800c8007500c41c0b10070031540940d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 106815926 1250 106814676 106814681
    0x20304030c021c060501050402131202060f130503071d160e0607050c04050907050108010e0912270415060507110315090c0a261219081605030402091009 67
    0xf1910301e164014001c60000d1011030b100d00c1d801044222801c61070302e01c8a1072035012076040c504c0741810510050b1f03290400e41d1180c0c3d00326401c410070401d0581d03462103001c0d040c1c0d00400039801407600a1240179004204074990880d03c10300d1008942c144a055036402481031141c1c05006645010030042242040703458071808041c0c10103d100d01c002d0714026103124140811150018200702e80d07030b400200100810f0360461852815a078030008910b442e559483c0b42c00785061000b800b41c400c10740b4001540481c2c0f084c21034107011080343c1070740400314007950181000190f031001245c1c0740d851207040d9410444940101d004100c00c074421504882c001e0100030000303041840f00d6a01d00c4010000d5030401400101c28400080b40c210200c881072100350038a44002d8050f1040320351140403500700711040c40381a40400c0f100b40300e8041d00b03000c03550b1030700d5643d021140c4a8408660b800460f800d0b4001c039030384865101c00d28011050b103075211421a90b1720703009c0104282001e01420854041900701047e05010750 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 106817176 1250 106815926 106815949
    0xe0c03151207030303050a140c0a0201180b070f020111160c09050703140f072307020306100602010c03051303050a090905010b04171507080603070e0405010c140307050d020304030c02 80
    0x200042e1650518606000c0e05407100101140c19040c90b001c5034140d10480282c6042e0090794030304450b501e4205070001a40149145c00d0407541111010b00c252041191540708a0700c54802a919804400c0c0141d005900741c0c0c5514034405158201807003104054514a41d8200545010f490312507a070359515240c01c012110195407907000a505c4540d402000c01600d00380680140784800c2d0340c002c40c031f041c0c000104038480c0000a6600c1c5011074011106d44000d540c00d0340c00103034004040e5540380c1000e1030440981041489414099400c01c52401240b078024868684501e6500e1400320381380341d15560480701c0e540007140400901c034840d080840c034180c5621500e03010309069540e41c3c3e1b0780d5007084072031090300f08070311a814410360240036040f0243d025002095049440c2d410f21908980b1a03c00280c1070081c5030b040845041156020401446015005507086503540c1d25a6012480d004000800621003180c0050108600704180100c2614a40c010f5a1007400791401c10404000c0f5030011310003e81e507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 106818426 1250 106817176 106817209
    0x606071401060911070305090f060c010f0504200a03080304051203010b090f060408030a0806040209040903021e010522060b06030a0b010e09010612200a08010f050108010e0c0315 78
    0x40b000c003803010840314442c00041d0608007814070308110f950b0750018110300c035800126000305070701030303010f41d154941e0000e031101c48480c3c80090100300040c15600c40109001ca83c2510742c2d03d0003081003641c4815503442050300c450080e085100040c10b5480d00c0d0798913030001c1d004130f4103845584101d80707541403040e02031806040c001801a565454940c101b0000003200e02c070141c42007800300003c00c0101d400008840d0004200d05000416645440c0014003d01481405a4006082407006000c141c3d020500c402c008010b42140710065100c9640d041c00c9940481e1002c01c1c01e505201d01c01261080340110300c25040c0301d4000030070104500c4000c035405801c00d649500c1040c1d2101480512503070004010803100c242907034030290562404034000c04010484030707125502e552f42d5455010341b0301040701c00d0310403405003843c80396070b00c59003100141003c009209100003801096808502ca610171f24500f03040307071111401100d9a459010509040340d20203040754420504200202c101130b20f62240000d091644c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 106819676 1250 106818426 106818431
    0x1e0902030a0b010e09060912030f040c031b06030f0203040203150a150312030c0f0206010b090105090a030804030203100207080a030c110a03020313050411070305030c040f08010b040c0c0209040303050606071401 92
    0x90040075940b421b5005003851240307411604036807a000c401c070380689034005000c00a1000d180c032a410300116802c401c1c0c0000c0c1220010b0100d00054654080e0301c80304540b12070313034104822002142c0c69002c9010541380250300d504440041e00c0380042c5846016005004000b0005100300c00c01c0202d240107289900448050344506058500c180e050300c02c3e10300741541400c003141d000d8002e510007501ca2105000352820a10041810740c003d074801d00c16107e000c038014242c02d040a480b401d046407550080d10049100e44035007008203c1541e498000e0342d8529910070304c0e07a81421400b00301600504040540b00c0d00304407814804030b104000c10841d82c440a40260003450fa15400110003101c075400c030707030011130159062082404900c0100002c8401e0181c0500c0e1807038480c4c03a44000d6400501c03640d88403c490002c41c2102190f85041944081d228010440381041142c000c1401038841d14541c2c00065400900200000c010034000d4000c7d07541700c40003c0c03526207450342c0c9030b80c2c0c0440d18005007c05034540c1c0d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 106820926 1250 106819676 106819681
    0x7060b01300b030f06061504170a1202030406050f03131a060906010207050109090e0c12033f090106120c0311031501090b0a05060a050901030f1e0902030a0b010e 71
    0x7000c41c0b150040b50030064014113181c2650f2030450b030f61400d01908030f5004100e18002c041160300c0002c00d440c0540b040b070728503a10700d0040d1303148990b6032148040145e8000001c07843e0b410059000000301d80c2151007989440d0704002c1601d2005409400052403200c2c5038044000700b8000030003101224542d1140070030a80f00c50308000c1c0070301c080c142009080303505650002a05120030b80c0c0140c0180b04941400d8004a0454626444e0341e040000b0420441d4001c5552403e54800d02030100c0130307009680c140c1110b004510b2a4100920410035000c010580c040d08030825020110300c0140740782c0d8044158000401c8607036486403480038150700240140d85040380d0303140174410000e44000c05501e0080850044c13840b10201700c52040c2580043c4a03c048041d80e4200a4041d519202451b0008002c014901c0d501c45d800071310043d00f154040324140c0c1c0040e240c1404c031640c610142c40b504070041502c000703d0111881c1e41c0000d60050510503016a4581b08009840c8001107080c032030306000e407032101003501050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 106822176 1250 106820926 106821017
    0x1030b0a0b03010612060213090c170a0213032303030c07050601050a031e0f0506010b04092019050f0309010209030d0813020d1506060f0f020106050607060b01 70
    0x280c0361800c5491183e4100041009164a41c1c2000300120b81c00c0040144e590000602ca1080310340c4e01ea020184060500070f6140401d40c100d942c041450700e60541e071444664540d0707429412072003010507085d81d162042409101043d01c04203078040018140314000c0900d46444411071464104881140003243c0024101040200c14405a40109003d80d01c181ca00d130b0030b503036414000104a0351340015207030038020802c0c02e1051460401c0c1145800c40241e03106541c4480b410b091030752090003240038050078101081d031802d0410369442c6000b0000018141000c0000040320301c01c00101c07140e6410003109008031066030b0081c0009500a20011000503617840000083c14246503490880d0824020890100036141c0d4803090100d000a034101c9141402042505d04010700c4001103502010b2189003803404a00c1c0743e04810300000407d4162220310315100749190817400d07160f580c0034160704036070709124032800070700c16401124004105040054810b11030b0216903510311a5180210b8140c48541c2d54039040f03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 106823426 1250 106822176 106822181
    0x50a05010305060901030f0812071d030a03120e1203010b04080624060a1704050109050f030a0c060203070c021207050114120402090c13170c04021c050c1201030b0a 72
    0x2010203007002d1005240440c00654405014400074080d04140c030700c0349040050350b04c2124405449a40d00c51100c0c240140c00400640990321111980d40d51100d4900d19840c0000786021144d074076550f819490558020020301508503ca03d800c014807806070a0f00e40c005100d0090360181c00c050645a881c2e03407070040c07094034044016101b0700f50303509408549854401c0c0389550031000c1e142074030300e680d60b046411001c48208030611190420062254180300410106400085100303000da030032544000540e41d019a16403203403e500c0400704052100450018525402031940038425080480c0d05c0b81c0300d500440c0d590300750b003c03a070310702a00421740900182d030b0401c04180341c0540c83c1210900b8201185006e0802c40c03000b81c0064464482640001d0105035840219940c10940903c1c0c80302d016510b030030380d2817207030100f000b03c8519000e988001c0003d800c01d4425660440c2e0b80800a000c00343d02c1c1040c00e401003c006d000500104020800840503510240c4058021441400e00d4030b01842c10f45e444808 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 106824676 1250 106823426 106823429
    0x9090c050c010f0b06250f0f021306080c09041106040303050c0601080607140705120c0706170702030306120a080a05030f070c1212060801050408030402121501150309140106050a 78
    0x1821890314000c0792a64617060251071184080c448078501c2d1708030100781c2e040d81c2c0009920082c449150500340004004614035000b40b12482511030785c42c80c000751003000080d04c02500414240f070780f2180e8a0311091501c031081f1b40e080743c014000812049000340c04640c4d56030203500240d02180f00051010030f0780c50200701e65401044107801604050030600340c001d00c0c0c4001001c3c441c02c1524080303804018003005000f064a501000144ca941d40c00310045450f031903906501c01c41000c240c803401580081e20203609264441c0c20300b54051455681d42004100f501403450000c12460310a9003660320014144034024102c0c030840d525002c1e124940303038a11640f01e11004008504200031541600c00184042e00c00ca04a65901d0502001c0c04013005051070003402681d21204096080038240710034811004000c1d4002e50094801c0480315102425041e510f110b130460030f180300c1680302c00400080c00c4040f0329891185891902040d203580541300c9494100403614400c400d42d644000400440c94030908500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 106825926 1250 106824676 106824701
    0x60506040b131d040602070503121602010e0a0b0117030d090b1605070201080a020307021204090504030206130b07050a0e040203090106140111120310030f03030c1b0f021009090c050c01 81
    0x2c094025191280603c2c1c5030240c4001c091580104281040040520546601d54040c140300ca21500e08141c1d0541100007000d0641c000d5480c05d1651070000c28080b5103001c0e03041e004440208a64a440843c031200020951542c0c2580014011100c000440b4020290040e0003049400541d0405100c181841400c4541490511204000721030040c1d810405496100d02044001612a0f41c0c444040c0e04056688854014183c40082c002c101500c0c5540050f019502aa08451203a130324a05105660082c0c0280980009c5612001800481c450070080820b1449842e02d203941c000e161002c24166017040d160361285035180c3d10103004502100d521000c44100901e0604002600580880e441300818038000040144c000700140c2640d0032005047c0c01941d1201780842c905009080c014010240f9101c00c2000803c2604404c0302007002c0008500000c0d0040080d118009142d4200003c0344407000610b010302149002c005204100c42c4124000502c140d11a40d0b952010341e149a421102d403003070642d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 106827176 1250 106825926 106825949
    0x2070512031b090904060504030e0d030302130e09030f07110604090506030f12160c15051207020a110402090f1207051c030e060705010207060501090b03010b0f0121060506040b13 78
    0x301103d503103650f41c132500903030824000a0700c0e0703c079802c0440c1c102c100443c480380c0203040c800c81c0340105541030340200b0360380201401c45c3c4002c94582c1c00d008a078060640b81440503600610002c81525440001044103522940c80c102d0300c01e0205c004603059812640c0202003c6a5a400b001905e017024000c00c490240603002502d2900700c0e058460405000e2054194216008103d0800401081d042088007a10050459120500c82220020890f40c0180650b004198042000c54203c82c00001c007007d00a60107040c5000e094800400d01009401c411080c962100c1402d50b0048151030b129892852000c01d031002d03007016410700c414811050060b00001e82850480a608030100380d00c010b03044c0c118101120303015a1440241070450181c0281c402c06004c05140200004400c85a80e000030382400c0190000d001c200c0a010800c444040d03a1034580f408a2580e03100d241007035400152040000003102000600c00341c81e4404981d03150095002650000800a00c89460f424480140342c010810321908 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 106828426 1250 106827176 106827187
    0x20d06030c08010c09060518030c0d260f07080306010302090a0311012d030c0c06020309061e04150e010608061509090316020409020f040e06010905010f080705120102070512031b 78
    0x510b1407081c2c0c001808c164203003c0c032030203007950144084500202c0007424441c04901078200864500004d1841c11440c0c10204400c4494004030011354259500f0000c6050a01d40300d038a82c1c80c0c41b036100920a504160742003000c0306290350303030300546006180517207880701c0d250000900141040c1400c41400b20174002070000740780c9102000001c1c440502d214607010410044081054030403281ca1800100341034000320402060350400102d551081152091030700c0301403403044200007110b80903500a00110760040a05011101c940c011480c0c0c0f60841c40001032080d9103403035407424464241d83c20454045181a422407614091043c5500484a034010b11300d031950b0243c1c1d00604c1300304800000c5c010f40e155400c0805650f82c182a2081c2e070703240a8400c0c84940c2000340c1c0c158a46000340a107041042c603110001c583c424500b284001a5180417005203401410402042a03500300d0448010035590200b020303400140040c4802011440d41d8481503441e0705102c0083c10100c40140e0f00004102d100748030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 106829676 1250 106828426 106828439
    0x3020f070503070b0409090609020a090f0c1103030708150d06140702030c19230102071211120d0213081f090308040326090a020906040903170a020d06030c08010c09 72
    0x71503040b241300131b03070005915445c1e180400c043c141c1d08201a600c05207826001800000541001d9034640341c1c450108101c540c40c0106446e10709007590011202d0340148000303800c085c00f0780c440782c3d0000c8810300c466141e07601d80000107100c20140542207414684640641204000c00c480d0700c1d4119a0300d002450802d10301c0c0030600e9070741410070000ba8082101c0444a411310441c0801c0e40c12110354480a00e1b42e00c90301c540300c0750103980180340072604603d00090340d40e9043c0c420300036003044504520250000325040b543e055401d81040036080c1d021a42003150120b05000080071100620303040c80588103000d5850807940e429010000d02d809198103080e56007001035442017030305030f106500d814a048503003150b1b00c402c1c2c8030b502130b2a00506040c004000b4003202100001e170202d810b9100300d440c0c401d5a03848405005c2a40c0101d18000c010a40111001d1001c03a05070701c81c0d580c04261003000500f00034541d14070105130790885d130013941c420690480610201c1d4007805484a2940e1078206084640c0c0b5210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 106830926 1250 106829676 106829699
    0x31a0303070321020a05090310150b0702060904020703020a020102060901020f0301090203040f02090103240911060c0a050a0807060f0b0a090e123001061407020f03060403020f07050307 81
    0x40107007088201200080b1280004489043c48011188110745448482002030195884112214842e210311013086110345418001c1d01c070030514141014810500d001080b25540d080000c0407139100d03c00b4810b030307151030302c0e0762005c1e00d4654000c3d801043c005600c1c6c00064103100005d0034002d5180d004000380400344110a00302c038111000c0d00d0340180d9940e00c03405c0090400e01c2d8a0002540040709400010031f2210380c284e90703880b19902c0c00761320f40d0015902ca118011246042d8004050524280003400640740400260103882a09000c0e20101d100e95a68035091940244c40bca40f2500d01180c2d040070702030180324884541108020400050f6040d0001034800d40d0310b845800d0050343c4400008201c00014000302007180348038003404d601c5600300c0884400000c0300c0c4030f000c5514610031000740200b10601c202d150403200c9549540d544040210080c107140c3e801001c007680c0100c402e809a811750b460810101d442180264068001000403203101424034101c3c1d03005911940c4241070500c6041ca504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 106832176 1250 106830926 106830937
    0xa110a0503070e01050702041d0f010b010813020a0b03040303020315180402090403050408030f1b010203010614070503071a1501031b1d040213030b090604350a0c03031a0303 76
    0x9003004040040d940004850500c02c0341b0b4029017180c1450002c003262a00788000404480d42c840a652071404011111801c9541d0501200c2c0041c2c003290200703800036a40400d0085007400641a5208680c969030114402d500580c0c04400082d13000080080003c20520580b9a8034030407141c501105080001c0001149001b42c0702a02c65400c3c0c80108042600880c02c8074001c2082c0410399403180b6103c01300600341e800802c114203e90800101030750b840b0754103108803030681e6050788881d90074180003109405150080070040300c0d584000c0101d2008903a944c18850800700d00c0c06040b004c185019449251020000d00c0001d0500d0f042418600700030751548005514411140b4107a42103450100f24900d0400103800c02581051001400a129100d08440c85003568000c051100c210340766914100d59907441254084c107001c003099140040d00c002c11501c4804e48040345014a80b85241e5034940101d944840149000320f11520008420103416000c0c8002030141c400d0304101d1187d220700441d0312403141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 106833426 1250 106832176 106832191
    0x10e0a0203090f0f01090302060c12070810030215042408130804030212060f070f05030118020d0501090605040b06070206121f03050106060806031605040b031f050a110a0503 76
    0x44005055510b08001480b45841100c048800014669007000d0017031910901c00d50050107601c0029140e1506841110140310180744400907076130304d90740c0840b400d9001410050b003601c1b0408001006d40d80e0007202d00d8007080d0305001203a5071480c00d111158461281e00003486425110b80d82c04926a400c0341405902400b5074070b045800c01c5091400494901c10750308020f610410200d40c4050850000800c64800d903115031a00f1044c2d211000141c2c2d20039004032100c1f0006000b000188004141059210002001d0030310250400c1c008850090564200360003003a9850307610002001030346414000c6e0214080c09a03005460f00d045500440e41500c110501000e5100d010808580042c829000880c81c0c0c2c0308820f50550f4281d00d03480c001e8040c4c0b004e40304080000b41584042380d4285004038105075698415a480d1078818544020b0002800000c0c140e10f0345402050250b0266000301c4d0b0450080d1000d1050020b40c2e0302d08484004121205c03003410102c0e16100b4840880d0194210040340d401024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 106834532 1106 106833426 106833431
    0x50d05030f01060e01110105090c010909060b2205030601080a0b010905010608181f060806150604030813180b010807050c0a03030f0b0409200108010e0a 67
    0xe540201c01c098440004100341ca010f00341d80218044103041c541440800c00c84a14211502290254455048581007001c0c540c7d0050112019100e264000c1008a05102032045203006821205032000f441c1c90318440c824110041400041400400703ca1840d0303141c20b03880b034948903840c100311608a003580011072045524000c01c2e0507960560758bc0c5080f603507140801c440c0d4441d500300060b4a400f0b0003941c00888200c601352896074001115001c220300707181400c0d540c0b03803804c0103040c0a07612050710181d4075540c0c0d808084504981c1c11803a15a00c90f000200c4080c0508040d41c000406e505d14101c071190032900c10b8101c1885100d09032214101c640d06c2c004140d440380b041d5000d521064001d03000100000c0d000768011140d031a120000005c0da40c002c00c0204080311031a8406031074414080b0601c040700d28508110034a4541c0030720b00300741c00303505d0103148602c60030000d02001401038 = true := by decide +kernel

theorem cover : BRFrame.Cov 106654676 106834532 := by
  have h0 := BRFrame.cov_init 106654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 106654676 ≤ n) (h2 : n < 106834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
