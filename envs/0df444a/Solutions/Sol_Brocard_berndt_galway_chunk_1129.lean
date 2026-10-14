-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1129
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:22:14.993677+00:00
-- url     : https://prove2.me/submissions/bd45c3d0-4545-4a8e-b253-76536ec02c17

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 202877697 ≤ n < 203057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 202878947 1250 202877697 202877699
    0x1503040503180105040602072304060e0108063303010f181a100618090c05070618030f030e01020c06070e1e060915090910080f06010f060e06070507 65
    0xc0140c5aa015502e141d096060304880c0400070360003a0165001d4522550081014900b1711203250008212880d001040c0301c50484c00584655950081c10054034401c502c124085d40b4142c002491304c0000b80150354120550080040c00380780d1380401117810019809070070161b246260209004003104440120380c541400803c04080480500070303400a40300b15042403010920340c0040070018402d0310303000f9003c3c060000401c0018454980760003018021100a0781c00ca5a403086542101c040b41548d0010403008640304c4103100700d52158810719000d2900d041840449035400801510b00700d42044281940c462f05409036800035810340f295403220004881e0f0a00740713240c018208640d0b01d10114400d0200504902c0c002c2c40010980300c4801003c3e041d9400d2000d03d80400a40e440303081014048080c09016904081d51003044881c00b481c00c04120000c918200720020b401c20001c070304101e4a80d4422001002101840c0c0070a90440c0c00c58070341000c0c2c0d010a580002c4603845910300242407803242c214 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 202880197 1250 202878947 202878953
    0x30b13082215030608070b030903190206041e02010c08130f030b04021207060203090105070303140a050103110d02010c02040504050109080703020f1b0d120306090e030903010612020303030411150304 87
    0x80650b5003184007240c1100c1001c03022020383d10740740501c1035140c2203200200580c680e0440078540012005050f64101403d0404500100c640e29100d607005030300072800d00040c03241c41813401d07404910800b004844119103800103041d0900c0e80750018424240000c0c182c0089060000e010040c0030880c4807030000039501e0070302c001e07100801e8178180e101b82601c582c101d12001e80001c07030340211021600514105942c440056030391f03421001c1c0c19010b0584800d00c08035007401c00254980704141b0301f640020f942d41181001624040c01308103450040d95401074080160381c0040030400318550490700854142c1d12071038118090841c40100410000010507040101500402d80c0f200070a0203100702ca400b81250035196219044411080e60030189507144540406c81c242d0120307085070300303506021a01e41d0307580042d0022a9100c0b103028515400100702c010613450203008001c01414404114049400c040d00043e407284400b4000400307128117550a80c00507180d150903180a09c40c0e08680507280e240c581 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 202881447 1250 202880197 202880257
    0x6030303020d0b0a060906050309030f0c010507110d0e09040f050604120806030106030c0e090c031002041409010303140a0c0f060b18040b07050921150a06030b1308 72
    0x702c0161038060801102903150304000b645602110210313914011024a8a20140c03166403018044000a00040006c4a28150140700500c035125403a07000040703514010304010840d0a641410b0401600285243d400c00795022020030000d5404623864407141d200d03440e0210b01c2c4d03007104c40c0080080c0240802c200030700802010f03c491004040d06d4020055945508240c02c80d0017070f000c0188003c402c0c040a200d03140c181102907078058080d00c2143d4906021200092903c004c40c6421031080340c00081c14032040c0301602d04104403a01c25165403000d07504543d409485c82080c0d0192114107680401e01880c0c4c0c5111f4080c41c020960030410f032a8500754982003c0d4054082440c515010b024141c0c810040002c0000440e071049402481205040d1240d000480c0d25a10284840340e00201240b10420030890358200070300555000b400030880500e01000344143c0d181e0003800071820f5880c2550070404110b4245160354000626400c2c2203039401c15261030261401a0311a103505801030f41e1200301966017903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 202882697 1250 202881447 202881457
    0xe01170a060e0c01090815040605132001030606020616110a06060612050610080a02090307082512030c080a121b0210091509050a051005010501181508041103010603030302 75
    0xa0761928003454039404419501c01010000c0c1c5504001031f00060b01050140d440980c10105060b503840d04924643c4a210120074841301038080315120212428203980c1620070a002001540050b00e845d00e07010030003041403e9a82c0b0710406011800011046c0c002d410b0210ba010964480320420046071100d600400310f46404d2100710f4014548404107003285031400360010384440c0d5507203000300380c0d031802141c1c4040d402c4204541c5d0148076000b000300d0101804c1c800310b113000020321903066a03600001d110708115038240c0c0c010f041f0b03c058500c414001c0707a488a482c040d0660800c112941e250191202207510658644c1400380e41032400141d0108450003131690400d42840b80d00300c07541d654900702007104448829000600e24070140c3c059081140b4182c107c07804c3d260180054460a2807140c4500382821500c9400c1d07600c3c240d031000140f01c20b6800000c88400c00b21f1800302d07001c0c0c0f2400c2890f050601103980b080395080c8201000043c04102400724120500d600141c02807041e150359140c00360181d040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 202883947 1250 202882697 202882699
    0x510180b0d0c050309031b030d1a0405060a0303050412150204060215010b0f0403060506030f060408031014010504090509010902060d020c011103060a05061e0403030f02060f010e01170a060e0c 84
    0x4081c0040203840c801c90599002e1740d400740155143c8290381c2030011642d200c90f8a1085c00e4002841142203428040c81110005441d00c1000c01d200d4801804100c1211400bc107a07900c10840e8000500c082a48001075400340c48000300c6004801c0180d0030f1045030016100f880e401c5c501d00000d40410520390200e0a080f1404103007044c8906c50740c8070008a4480d006803c102c00000109110410120b00c094000c5500100054183d030000c1502e15101c9050030000c540035030b080c0e540041030044400b2040396130740080c2074562850038000c00d1040000c10501c2507204002c8444e0701c540100300200300c00c0d401a0340c59680140380390340c0e0301101c00d000760180d0081b800466403946054080c41d90702d28000202d030f124410040015500f20304002c10484950040c1c4d07054000c030408445000c0718041c140d4011300c01755000751550b821607888490001e2804000402801c2c0d01210000100070302d04440145605403603004103031600d02551800014502500042c001d00400d0400c9441f450b2030308045050768800034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 202885197 1250 202883947 202883951
    0x115080c12150315130c05060a0f0819111902072916030504030512030c030411011808060a0606020604110d0515010e060406061b0308060f0303040905010e0907121e02040218040b190510180b0d 84
    0xc5480a80e110d081ca840354080b49101503450900f130388922414544c0000c1c4142143e420305903016245c01c0e80f0540c03907808a011803000101442845410003412961203c1990064038524201d8400282408040d10050010f441c003070b01211260302071042d0103090982d1038401c2040941d18408030b9a80c4000782e0340095003600d0f1042c040740152020400c0c1d48034a0b000700c220380320b440e10007080c000c44800d810320544903405504901072102400d03c445038001c00009103510054100f54003007000300d035480c0d40300c4414092090602e0003521a10303100350f0143c9800d4100b250095460402090008100c086074a5141c04002400302e22070344c0e50751000d8141c4480f206003044039600c01c94005d40d03511003400b4540c0d02c1c40c001001c031000100c1c54102920340402d03001e4140b24002c05640800c0690700148110002080709180104072402c0a101c1e59080b00d404650711044940c1c2c4039640150030350540140c0780a01e005082a10001c5c4c06500d80401000385810044907069444c0c5114050343c1100255801c402c2c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 202886447 1250 202885197 202885237
    0x5030a03151202090103080711030307050a0618020f0d0201140a120b0904052a0604030308040302060c031501030506030102070503030115080c12150315130c05060a0f081911 76
    0x11000001c0b05540c0359004d010b500c4185d095449500081e0485001105c02100744900d21166840600242c11210305c0f450040200c0b0b44039150400540d0f0701a084c0640350342d500950790000d0395641e140e0106c07130700d02958880c280c103400b070004850450301c41e43d900103400720001e250700c42103500ca4800004941c104800b0070641d183c0900f000034421081e00c01034031982c4000c0390410764510040b0441c070350454101c01c1c40c501c60000300100d211034005900035400319902c030003004103040e01031241d140c2c4a1250800c1c80e00d185040384000c54a0914003403900d0402d50344200040e00c82c1c40950449051035001030850b612582e48052160041d04100d04d408001081c240100303880100500984501002d1500c0d900465951815400b00e44441010705580c148100f00b500c1911000800c801c2c4d0084074013902140107400a41404082506c2c0b80e802079020b903d0810001d80000d5205030788480807020f610b0140d01e2074541c40c442c1906440140b280e5100726281150b00b00001540c02c1c0180f00070001b485000c0244 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 202887697 1250 202886447 202886459
    0x100513060b0303090603190605210c01080103120c0c18061d100608091e0607030b010c0f0204050c0c06070807110a0515060d05010608030d110a141605030a0315 70
    0x3e40144a1101d40080044c000324044a40038030f00400c685540103030000b880359969001600389900c00c0d02c0300c5814022510b1100064406201b8000c1c500e00c2070a284d1202e500d169500340a907c0f00e442d070f0208101c140e81d030b54020440004001001010182c4005401c4001140c48600a18a070310034484441c81815140e04403180010480740b02d116080c2c803090001e482d02c1029601420700a298400d9400b0324240381c1440309842030701c40310307100301c180007000309161414011342244c0c580c260341070501c810040c981c2c0014043c00b5510070300590603600800e481d00ea00700001070038043c40d01464140d0007004d0401c26203562006000344104c00968460003c00e00274881e01e40c580d2900301002e041e80c4c22820038076412484c0b270700c0b00d160007034005050032620962548030142140c105800c00303444c03600000740b0301c0c040390428025015200a5601020318090803030001424200700c0700d2214242600c003240380c01094100506c1c48141c1608a404d903a80c44000d68802401012030503400919000d00390303408512 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 202888947 1250 202887697 202887703
    0x10506030a030c0b0402010c080a020a0b06061e0d020903030d0e0618030a030e030c0304090e060603120a0c03180902071419030c021f120c0f1202090102100513060b03 73
    0x21242c050316104503018258a550f0b89452006100340e05200310b900c00070001810f4000180702c1485c2960160110341308038540012101d5010346030701d109100501900f40c1d08212010101d021420110801d44c3d03446c2e904039503030084e004102d0f0840c0c0c10301021460141c091111380103294070001903402d441c0325942c3c0d91944039151200d00e2124005900038020700304414041c2c0d0000405a4041c421039003040c00070708450b40303164401e4110840d0180c07110440c250f44401044442d8100008030094a58420888290052800350180100400c0700b40e10340c550626018010850111100703d500310640385d00c0349441006035200100403070b005902c0703003c440090380c808158020150500603500c030301e1116644003102c5030302c40007100303980c0f22a1024855000440328000c98201555a072600080d0b2601c400104040ba021800690b041c40791071202c0480d0b1981c0084c4110311030340860801a29500c9000040f4a0b00c0c00740b1240c400503c0c54a014480d20304110200c2200e11445110103004455860091580b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 202890197 1250 202888947 202888963
    0x70e0604110403060b040f11040609090c0503041b08060c030712060305120703050c070f03031b170d0f050708060307090b090a05040503070602070f03110a020904170d0213060201050603 81
    0x7504803414442440010b91075000107400716070040007c00c07007206045090b42214418a00f501006200140c00c024454000c01c0000050040001c02c000c0d8104410001d0072520000b0f1004003080141c0410000441040740540098081c0710304035480e07450568240d0400d540240c5502c004202001d41c2c2070011003880c082c0360142c070340c800080c14031440c010080309407613001505c1c01c03001e009082c401ca002040040041100400c1c0c01e140c1c00c001e4600c1c41c2005400345c1c46600c80450032150400f49040481c9089a200c0c0c1190462080941d403a0711003007050009040d0890000da02504150500085a40c00f45d000e80c01504100c06071125140d44980b640212281004d40c01d40019a000004090706515400307240c0c00340c014030030b072071402e8042d94441040303921015080700c0040041c00d5000c145940007060205030300c2c03140f00801c114030280c0c0006803e6880208002c041c0003441000100c4032000e441913601003400f20800350745070030040e104218150300318080c1c030006610f42400141070307290000c0d40c50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 202891447 1250 202890197 202890221
    0x804210f0e01030b040e010203101a03040b0a0b0d0605060a0611070b07020604030c0806041502070503030a0510150e27010b0906160b0405060a061802071a0108070e0604 74
    0x20122440c56801991418080d10800c0d0506642d1560f1003c107031074500506c3d40083c00b9600041c0d81e40b0300305c10540d4a1102681045003c4a61590031031041e80a400c01c89400942000300d04405035a0801004058006030301c50701d030010035003d4020200400c0d0340006006000484100b800141c444208907045c69540607a0040365010040400901018030b000381081170001e0300d45460203860740c55102000c013145d40700464541c0468208818482c001c604109507014a0382c0c10b5103000a503031503040d81c03800050101005540e980e8003040000c038020040300018000e00035400e40b041142c85015140f0394a180700d050250b0080c0100f9803007020b28141c130300c01811151201341c1d000d07428034810301103070b4000011a640200341000744104199045075000103d600c142e00a1820745450f2402c5810300202030400401181003010910411a00c2603427040b00c0d05541100580324840d0f030608100540703902002440400f100b0780003080403080416080c007138441201c1602c0950300d0751801e110440349610030203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 202892697 1250 202891447 202891457
    0x1c0623070509011b08040e071206180b181504140603251802041716060e030c12010e0d08090a02040c020c03100c021005060f04110c030703080421 64
    0x4462103601408001c0540700050a600313401d84c25542d210300c00740d40310340c101c282038400700300821000e241e001c0c4034a131000110b41070a01000d0f103800101c41070060480311603042e0f1038851503200c035207485000c1d01040d42d41040c44400c60504001910f00c421741088818540114100100011004101c200d03c80c01400040c00911f90a1002c1c60801d109128440003501c280308001400510640c1010402d06001c0301c0701401641d46103804200d401c0311086400341d1490740c025003484810070041c18000070407200030341048810350156900103401e1a001020082d032000c3c18005c2c0c0101000c05521003520501c000d0200d40e0000c00300e160a840303c8a0894116066501c0b00c100e0400600b01500702e1080101d003401154000c0c24000c00090512070031360442282d080d680d20465a566a041124850001da020003c003d42c0c244031000c10303091002c01507200e000300d0b19503c1982010000804503042c0c46100c0d01600e4072034200f80303401001c092060750700341c5401800203100c3d8000c1c8140406407550344890380b90 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 202893947 1250 202892697 202892707
    0xc010c080301050f01051606060f15020606040b0402070c0306060603110711010f0c140a0506150904021504030503031510030605091314070305030c060c040302100309021c06230705 79
    0x401c8644100b13000c08038100802845402d406185602c8240c90b41703481010046035043c18202d041c0042d60450748030b0b02d181040306040f604140d80208495801ca40c080c0ca022500300041c4010a0182c801c4110003010012043c8001060020700e0340910103950081e039062240400600c0d02d841c1600842501600c0c801e0110708580c9a1740c011f0a41501d0041c1c581003420302000c80d030300e403007200700c00e00e102805da00c0e002000f284c9c080003801d0040036882441e604100c4a65510200441c25411009000a0054802c1469908440c9981c4141c60085034440704032a81e9103001e004181520618140c80c41c02080c5c1d0606061149000340a180141d0718050005546a0b92f034442410340411142c4d825503510810302c60748851860148401c45c0594002c6004507644c07440a13049a2400030300811070014100280070a0005a80741041e90782554450314008c99400618000580c1c0c050704001c403140e0810a01210000300030f003d8100c441203403040c4040c848090f480b108181074407641151180005002000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 202895197 1250 202893947 202893949
    0x5071b05150c0c121c030b060703030f050606040815090307080313050f0106030803040b04111e030c040504050a0f0809030a030309110d0c1a07120302030612030a09270606030606020c010c08030105 86
    0x1c444800c0111b4034020541c3c158180105601d540701c4034080e00001d44594002c42007040d98010b183c0c00417001d9602c20725191a107510941c603105900300350500d05898002003100c1940400903aa9215088501c055590500354000c50303410030a5042190399008103034000e0302d0081c040c404c0710212900440c0d010318540c1d032a0f86003401010014411100c59041c1039480d080f03900c920001c540903481c2910144450180503042614100c1c059032058819410001008002100801c04590161f804459082d65625914000c0c503c0d0088005044d054411070881800f032642c03542205100340d00074501c81c071800d48280d00780005d40040325009030103d05008020000c11540034060140d40c0a05100c4a00301f050079a2030351001e102d1078800306e0000e074010080c40402e1810300c1c03906108040300b030000c1d450110800000307400c0300603d1081060190b07070b4014844520204101104d00d61000103010000c682e1030311405001000c150040c02c1c010700c6001d4031542c682d40910074020816030000c04460850780303854 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 202896447 1250 202895197 202895233
    0x602030315010f021e100612050a0204020702060d050915071e0e060903120408060106020f0a1b03140709151215020f040e0702060f04020105071b05150c0c12 69
    0x85800e0852188802c02d80300c03907160303030521310182e52a64040c00080100031807050940eaa1504420003009008e05520002000000e0000c01558161800b58803081c1500020f10070b801114104180d07241407100300082c808003c00c2c3d840d110710705c45441c45415200c1001c00ca5015111150403100c55844944284c42e89004150454003060024541464124400f004c2420141c5040300c0c0201c4500125043c00195000d004550240c9032510080c05c0c51480d0300121903480705040c0c0c019100c92009040f0b10b0160682a110700061504402c40440e84068221626034401451181005441c078100f0380e04011641010964201ca071680d030307254060700300c0785c40d01d4809444050342c2c194042e50802644040545200c00750000b0815071015400318070740300201034144080208803900d055989820000143c0c0c00c203054a503440d40100d54000310303031a400d0046480780f0954100c207078001c000044285030640000010b00403210b9120654900048800c14015080103910804009411050312418036600355 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 202897697 1250 202896447 202896467
    0x1021e070b0f0a1508030913090201080f0c07060608030c0106090c0c0b090f0106080d0f02150103080309010e01020d0228080f19090803061e090a090305250c060203031501 75
    0x41c41c40090031416528550790584c005510a50464001060031807a6103000c1c125180120b024007001e21a03d649a40005d10351400108a0748000c2c5c02440450b052a03002c4050303504603503202008100494454004594a030010b0640280b0340d8204800880d1403e20350048842034202c0c0e840e803440d1002280c0d02c0310681600207080d280c2510904506035141c501c240210b0000300300ca600503180b1450405001440c1040410b1500c003550b120140c070040e192071910f04607044a412114040d02e0b03448407284513001d071051b010b240459600110f8407004500d4103070700a040900005005142130180e00d9103098164250185c0700010542c6403000441d00210800d14a901161842a00070940c03402100d01e81241c42c2d001c41035039100400b00c20400305041c001c40b40f440024021034818000d5060400048030b1110081016007200d0315001b01404050082e0281d4580444020b0800c8580341a038134150b07910b11008005580f050003090300000e0713060000c0110b0740660000d030a14070034030045c0001502c1508034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 202898947 1250 202897697 202897711
    0x2010e010e041401260f0c120102090d030905210a1101021c0903030e06031b130b04030f03080c072001090e04060507030c0f0c0b041e030201021e070b0f 67
    0xc9183d03401402110b00411400b8140080100495000b040c1e0404240030035175814402c0d0350f118410104000300c0004421801c101e08588080e18000c80c89216406400341c241c1460700000039484000405410030104000e50b0415111004021501401c03092840b8010301c0c54240c6030480c010407130101d40083d074110b00c1d520041c0100c1da040f031651015040d5503032035140101c1c0091340c140403d20805520118070b041c4940b040700c03103e0031401d2104040340a0b43c2040074407121031000056030b00c1c9101a120038000103214a401c104c0c1c8941d03032030038406040c00805004400041030100098030032901c61050b580310a8218210807100340a40440b00c400c1140000064140401d0220008079a9800b4100510540c072a0a000c11141030441015059035058013030f100c00e2290f003410500d016513100040f1028260480c0e00311040b40c5944c100907a140541d00030540c142e10440650205041d01500100302903a8100f2121181c0b09001c3d50a112501800c6c000030300c00d04074a400700b0000c0d03411060301c1341c000071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 202900197 1250 202898947 202898951
    0xc0d031211040e040809010206060a03030219050106081f0b03210d06030b0a1a0303030105010c030e0a0b120106170c0d0c0e130c090f0b0406120603020303030f01140d02010e010e04 79
    0x307143e03580094030f49411502150041340020b08041c595a06102c4c4940105080c1d42a030125400d5aa01940758000e00340030030708030b0a03c403a0460502000350010f5004003182070680d1000c00e00200c046001d14440c0c4264900e41d41441c985510310300300003a6035402d204070034a034035100c036500000d01002a400000c86100b81c03501c070070021000c125103111690090100000c00034102904c0d03136207004020a514040e500c01d030024801000584d82004114903600c1d410315105070030b010148001a0740d42c1681d0048070007011702044180d028144099010b059415907122040200c16441000c039204070203d90345d0030000c40901240e8103501044d00041c032070340300b1810034121401d07100d0042100001480003004030652030350070010781c95802c210444080c0510074103200000d07040a46a075103d104610600e810000c2d251080c4018201070703030100c00a50b9005058a5503410010a6114103100c00e0045924074030140e10360110915010520200c0580c0c180c40b4610a03120b04001903458600b003c06141e0000c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 202901447 1250 202900197 202900199
    0x121006021f0b04050c0d0b0102070b0f090a0b0a2a030e0603042a050a050103090203031b10021207140c070b0d09020303030406090326060d080408030a110c0d03121104 73
    0x3d03403980540b80c402c4c1c40c544e01003a1650321184989060351102025103045d0f410030001031210142b0141101c004c20b940c0a48156540e030040082910b8100031b45c4030070840030000c212499015840321201c414082010010605107203c0e6803c1b540320081150010702040b441040c10041d41030807030180d80d101380284a40121060044080000c4141c641070000c440a003c003002d00040c5016103040000c1c0c0300a1038100700c40c60550340440c0da42d105508000070091103401421103214000c01c004015000307100382c290344407403000e246500003002c25078802c030100e08602100400e44418100b0b5070401c00e407500081050030f203001c003091a00c0e400010714103c0310f916400b1000c09078030108001e5024074800c07a0002650710181c100103203400500880381c60b00703014060814002d00c20618806030408400c603040d65458441d0710b800a00c07445a98040314041c0004600b0361019a04074440203112101c0324150307001644000100310340068080300040c04241280c11003a140b051907400042d84c01d4541d02d40d90b00d02 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 202902697 1250 202901447 202901449
    0x70516140f010b0301050c13050906030109021908071401020307111207031a0105090f04060b0102150a0b010809030a050f0711220f050c0301090b030a020411121006021f0b 75
    0x246402100c107290b0b4503900c0d603070020b00b0309201d51540444d03450440ba081506030001c03401c240d0003d05c50148100500c1020804d5039a0a41c8550840d541c020f0840c003154a80110300702c0d503581684100703080c80c000e645002409002185070701201e480305a010318a8001d40756034118020039002806030f044204810141300b480380402900001c0c40c000c54140a22142d992040900c180c0140c0003180aa5044018012107203146404c4640003a44008081402c0050000413460a84548082461641300000b4441c5004480d48440780d40082aa2403d007036544403508640d0380d108480f4018009030042080c0c841e0904000c007c2c191940c458854810f904104c10002640000c041c8c20501500c11020360410729606503118008071900703110001d02c51032801c10f1000da4a0f000c1445940c00213522002448855502800080403466008104100200481c071410410b0b4208040780c2030000021804949079400c80040c40d0101e602c0da90003060040c0741104400340380301c000170079040a15103c50b114041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 202903947 1250 202902697 202902703
    0x110907030204030501061205071a090d110f0108060907030b1908060f0702120901051b0607080a0b010503010807290c0309040605040e0c040e1e0c1807051614 69
    0x14105540c0e0168407a811402c045007114101d9100c41c141c031841002c941c0003e61b000c5060012100e07800d00c00e034110b002c038020015107845000c100a50180750140500d0400c8480c150020007100e05480050300c0024034001503d03140000c1d2006507000c000100024003503482504090300c0503401900c5440c0740c00a2489004000400d038000011542060303041004200f0300715400e0350b1007507080c8020301e140c004801091559210395610681007100010f01c1c0c000302e02080c10b8101f0070f480d0a40803606546403d660003012014196003c86840f81400c2d011340603584900d082da81a1000240541081807604010405042e5010301d03100c251390032004500088003c0c080035140b81c80044002d0769480e0291010001110b409401144c0704074504107240014100014400c00f5111040c0ea0005201d046008007a240802031440700ca0315000c03140c1080003017100480d469400e0441981c059030012002c0c03000340c0b508a822030340c18001800901444c02800000840d4490780c81c007600c449180d0040c80e22501c2d003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 202905197 1250 202903947 202903951
    0x2071122150503340308181f0c0c120203100c0c0b0a0b0a050904051e120f18040b0603040b04020a050a080f1507050708093001050a051b071109 63
    0x1134040201c1ca100000c1c0800c0d0881200e030800c81c4242503040900b140c0c0c1346e80c000d0240400c0000c0c0d0360280804070305581c6503a0040c081c2c05042e02d010350b0310804c506c0401402448d540d10122038440b07a0b0070000540e98002281006150750040c050907618407042010402400107000340e40030030003c41034a1010403a444561406030a0303208012640b41e00f24024055003200c117500540c042c2c945c6c0b82c100310100d0001318014294420003800526140c42112100f840e18012509050824000250003015400010000c1003417101d500c0351520440112005c01007221009000c01d034000204000160005902c4500346500c01d01c0240001000b41c1ca5001142c105c071640d404c107503115803200d1026058400108881ca41580120038200b03003502d802d030310013030090041c80c40c0101040e42c00b01d003c0081c0c0c0d42e904405460710803601c03034807521084585c854003011400c04803c41c00755441c3c80003150144c0454003805214000d50036800c00c028101041a440d541d002c110192030048206000700d44565588401c94 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 202906447 1250 202905197 202905223
    0x20d020d02071505070513090507090b0a0905030f010b03031606060902030f01051216060528090302100e010c0206070f06110306010908010b090609090304170102071122150503 77
    0x3100c40c3d9550042e1030844002030f0a8600340403003442200541c020043c280019100315550200b62511070002c140c40100315500700c000c500802090300040264022808400c4800480803a500d01c0a118401d5088411210380540c040d00100800482406900340010710b0511650000420b155920b501804a80042e07481054020038100100480e10700712180c01a50041034024205ca4080540b80c40c8204106104a40c1030200115103140c0003486c2403010010903104a8500c40c1040c1e800038018029030280c002244600c95040074010028456441050886410b0316414050b9410381c0030010580c005006c11501c24503943c56010014005008441c07442c0d00061007542c0324184400058012400c50b041400da9030302d0401c8150584c1e4900e40320710380160b020740340204142c4980c0c010908510558201c241034041d08400c281e40c0c0d100560080109500605100c0d8122500303400704100e5190302c46c410743d084125554885209542a0b109c01c4464210800b600351141c0d651b4013080c281800025030b2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 202907697 1250 202906447 202906463
    0xf0f1e1206050a050f091b01030f0e0618070f050103020f04030203030c060a060801020f0306100c0b09060406060b0f1b0f2a03070303080a090c0515180303090307050103020d020d0207 80
    0x100c4903e0001d8010950855007258284e9201d1414080e4255105061209a1000303020180d61054a901980c0701d80e041f440c4810701403180f002650b21290b03443c0700a03507040e62002d42100c11004003480114010040c1d0300183c103404441c1d0b280000442c003030b4102c00740d14400e4910400c0f0000050ba130801c020100039801034054080c61034000b007880d003182c1066114040c3c07030340100003c48600ca001000c890348480219014825031101082c100c030125407110b801820b110f0400203010400f040040d40300c0c4500d2061500740310300d41d100e1541c17981901a140d2004101c00c0c0500014902c5848041030401040221044a20541e941c01c00549818240a401d180074525890300b40703110782c41c451a40c003003010154014001d40d4a145c2c0d00606150009284440196890040f01c041100c010b840d00d0040000420b412804c0317840c0075260a484c1d0011040c100c800c005014407100c03500700403003a134a42c03d800401a199041c03502006601070340c803034401d0100c12075003008410f251020718800742003014011008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 202908947 1250 202907697 202907701
    0x30c041b030501170a1e0c030f060506010f201513110a030b1801110a0e032109060705070e151c1110030f090602130f0f1e120605 57
    0x1d0300301c8030181c01090004064000c58240c040000500f80d0030f00d81e00c078041c8020345800e0851008214040380300205079501d590f80010074400701502c03240c4032a014060403c11901d0f490015104200c2e0346a1000c0420307081c0c541080d0030b99441078001000580e120650300340c0e54608070202da540c10200c404442007119403503190301344151100e100b59120002da522081c2503045480c0c1203a42400205801003880d40c004d014841c0340001c0d041050b0048008030f140b80c82c1d8000160203007901c10141c1459000b03204810454030410149905010719900030048540340406007800c0c008030f50703c030490541c1d15110b88500003c030368640b0104540300e800d0790310060105003005800c00228410000c1030749484d032000803c5801081d4501003440004030f080740d01040d45000a03c05901810710711703644041d03281c42d1207405010302c030032900207050020b80031540000041d2543d04171500c2c91000d00403400351030b028038402d02c81c0c941d8000340c07110444908013070803010981e85c883e800031503001783c0801c840690329070781 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 202910197 1250 202908947 202909001
    0x20c09160e040212130c0803070f20010c0308100e0103110a0b0a051903090204180215072001091203030f06050906010c060b01050904020c0a170306010504060e030c04 73
    0x140540c88280c04603025890013041042c019110740010301503800c80403400301150200844c00c0c285c6401400c05005580d199851170401c1b43c0c2d0f402c00000d003a502540c142250a40c1506c0202030f90302070800503191b000e0501141e490446900200400714141303280503c502007640001070340054000d62092840c0c22502c1a018188418000f03030b544450111603041c082118056040400d0f103038480384005455a820f0032242c0101c0240400b624041c1d00f00d86403481c030101c17484959101428240c02a0f802e096003c64280b1458a40e1040c040050642e40300200003107141e80c41d149960410074014982054510780317500c003094088000310390850100c3c0e070315040f09114030164012480101002c50b0301e420140b91000010380041050751005244550303c07860b00506078050800c0d80d4044d280a4011034942128000050303032420002c009413070074442e0708100c1c03458000c0c510850f4410441030b9109400c262500303c054451040394219079505014901d03521046840354804e100d00844126030a8440d001c401c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 202911447 1250 202910197 202910207
    0x30509061201170c0306150415060f0216060e1909020a020a03090e060f2404080a06060e040f08030c090303071a100e071211120106090b07020d12020c0916 68
    0x100364035041341c1202001481aa8012801c50350082020500103285414100003d000700010440e48290312803004001c40d00c1a4410507a84e4150b4403a02280d20150322111810410109880b0300d400080c0c0803003c08850381004109074551410901c04c010700c042c4c07a2821507080ea04080e0740000180e10560022040c1030b8025443c1000b0502d1001751103a5040c10000302d420901c004132054002e0b0140c0041504283c0e4110203800159191007a0030784494440c409142c940000010075a0110f003000d501060904902d4540ca00840e40a50380742a020b080d540c982c0f010b034000500300d4007074442c14480b00c0d4540c0c60a00042107541e2040c0c0d42140628400041403c0080c00501004566142560700740440c2c562004550303084200c1d0700342001c1c000100c0d4801400340040c0c2c3e0840c40344032070100e0001d034120002c1c3c1c0d00905036241030304c48107401c84e25035945003101d00030514082d6009a4020044001c2040944107000400e40c910554441da012100440e40c82c040035950400c00e0400c00c5902c0404a901c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 202912697 1250 202911447 202911479
    0x80a020c13021603050c030c070e09010e070b1b0f0d0302190c0b15240403052b0503071209050c10030c0e090601020309030a03030f0510030201051204030509061201 72
    0xc00442c03c100c2240c210350510120164000d09000780003070442910442081a00c040b0b55080080340d034000d441d10000c030314840c3c041d52591429800d007070032808400b90203d0311000741c4141d0001c65040c4100d1800501800d0303007600401c4120f000d003112000c01000b043c09803400c030380c030300352030150359001140705824140f0f10b20b080031010080700341000b5001801c0202140d0300b00003098003400f007469020340040e05a542025201703907070740c00c1405580c0c40b1102a001501c101d80c02002038900e00840c4004e40b403030a030110302600d0504a003140c000c0460a00a001a6070010b050b0b00d010300c61600031280390012580003400c1520b560b48540c010366103510300103280c405007181a10b82072005405c10103020301500544215603209818540000d03805034820025121802002011104c49142da0b08016005009001e10302400e2800e0a0000c3d045030803043d2040120799040e5034141c034046c01106804120340001d4402c07802c1060401c00b0011030380c0d8074400b411074520000f0504103907500d020a40c00c418550 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 202913947 1250 202912697 202912729
    0x30504260714091f12030e03210406050703090e09010f060501020c130509031204140106050306070503011806150509090109060b16060b03070303031a01080108190f080a020c 76
    0x82c0980101034640c01c0d00340790410b21001010103240343c1c01501802c8800f04d0340207401c0b00700081c0244c2007031680c0003080016240041c0c0c15960340584002030441f12203031100c0003c0401e80c041004100e40c0b8410340080007898020f10340302c1041525403220040030075041ea5010240da468210802c41070015200c0e03400145800d0000780360303446815010496042404990805240d0707144001405010140125410040c5610002c00c951070685407031400c240d01da04d0a140c256113460004213190a0008849004010300d850345801d6a00e071810384619451a4040c1d4050a42c4400000640c043c40d0f2548205042d0300d130721225220481c11301401640c001c16400201c07500e003003c0040061007044800c84d040e074038800100a291400702d0400c0c2c0d0140201e48106509403140707110020625525601100c030580c0c03440c0e0070a01c0303034034004011183e81c10280112070703140d0000d0000c144110007003100c00070719174801c8503000c01e5502103846000c0c403600080800c8000d0b8011043c01422864034401d49991904 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 202915197 1250 202913947 202913969
    0x1605041d06010b0a170f091c0c02090702012c0d0504120f02010917160501021501150e090412021204080a0f030e19061b050c0d0305042607 61
    0x240e0521565540106200e80d00409070000b8806072118411001c1e0751070640c5402c800d00380d500f4030700004000d081301100c481c2c0c0c683c09106c00a0100c0070400d42d03c2900e03040c00d9560100c08005980800844020140444055668910780348004444000c40703408028030759845c5a51449890b00420305240329010244d017080130411040c002d400b41c0d041300d801015042494406841801d20041e101c40700c45401c0350f9001e00d9050401c000c0c2c0c00d000961008a1f44041d8070401180f0713620001a40e940380c1144a041c8040102030040c80f40c0da0900d0300b2202c0c510b540d494600e0350a0380e8040402c0b040b50b4243c40c2945c401c2c100d8900c6402d01e0ba0100140003000041b0550315103003918110303110b0b8640340600d1006000e5814107125900b418401e40402440c20b07001050710070088140300241c000e605641c0700e2a0081400c2485a112020b6070320442c2c2600c9410401a00355a151401004001405030100300c0c2401000e00010275890543c50b806008403500c1501d840c84841040c0085c0d241114540c00b000500d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 202916447 1250 202915197 202915241
    0x30e0a05030a080a031103090106091a060904110d02070b01050a05030d090621060602060402130b0d06020904111605060901020703090504020a110d0201061706100513020705160504 79
    0x703100040d10990640d08141c83d2a1500c028003c201c014000601c1c45a501100110601101032419400341c01101ca00d02400c00913080702c50007242a0300b614801e038540c00041802080814140b64201900d84e10240d0381007844c160500502d079003260085081554a004d080d00188454200a2816406018100d004200c04498010700038009000b5018103030402c030000707a9650001084081580c6203890303d000502c2110745980b8000d503206001c0b94103a109404258110040700c51a1041d0040745402a045000d91071844e00c80c21b020b076102180310b9401507a00c4501024001d40351b40500b107040709003e0040d10140c19400d00030b00d084000780c4a0801070748104110000a41c012000c03c0403510203450140e21084501801d4071001600d410781b54881c01031078a28032110b641940306105a0300300c4d11418107802c43c1550700c00c0c0d50340411074280051007000380c41401580f601d070b03071b0804032400c000b18050f2501d24a5680c05050030700210b5409070110311644203010a00c0d250103071650b41600c4010000d110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 202917697 1250 202916447 202916449
    0x71d0631120b180d1101140a0f0c030b0f010e060d0f0903081b040501140702030703081c0b0603011e0803041202040507020303040302151308040b04090c14070206030c0909070804030e0a05 82
    0x220201210401070000460360501141829008030300f082050001550f02458020640809041e09e020681143d52420000d134003214020b102c1c0c02d001d144040c08040020580c60015104c0003400c4480c650f00400034092040f0741a4a40280850102c80380008101c58100e8500035005001c0078000f100b0310740e81004000703044191036003510201d41c02440d040c2e000109800070003445118182000e501802040c401000f408400001850b4600058000440c42c0c200c491402007100c11140c42030b6030141003007004021b041544450304c41e025035080b00d000c012541c0c81001d1850b540c001d51082144000541ca844150b261520805a01012a0001d503203149041c3d0b600035103d174503a40030001522624804200c03803e280407a184083c0e60301a4002d507603562a100c040c3d050360032500c5204103107403c01c160310610b03d03c5440300002c0c04e03441c0641c80b810000554200102500018844807140da01400900b19503a50701231400d0141d40360f6207510b407503406c09040013001042440455409000005800c000c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 202918947 1250 202917697 202917703
    0x2070f0605030a11070f0f0209060a081b01050903030705010e0d030e0c1e1003090b0a1e02070f06020301062706020c040905070905070206071d0631120b18 68
    0x80720f8245600081c1c3c100700c40b03446055a0007003041c050321209070001c0c04420401d00028082d45113001701c601d0200c2c1c2d60744800300b00c2c07080c03064050249142c001161081000e06551152a11a80141005403d1085450201c1d00d0358000c2141601c0e42d030744800041e0050300d0140411600002a450203010700d90100080301d0381d075260380ba401030080d51814070301d40f004900301204203070f281c800816511540c00400c030000d0107413084c00800e03100c0f0001603010494103101c511603112900c3c0d00114450340042804d55190094224040c00e890801c3c0b96006680050580c3c40154060010760310383d0485041140c1401444400031503200c0f06011600320203004007600010b6100b50800c044401068100c00c1e071400750304107081d580c0010145820481807100550b00410070750b1007907200d50b0b0f0385480c06401a60030350005800b02c1c121a04160300304041c5c811b4050018202003200e41042440c90501402d0350160080b4140754801001b20003d03c000004000c03204640a802c00c00a42400c6660000c0840040c1c0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 202920197 1250 202918947 202918951
    0x1090f05040201141e0324090f040f0311010609020d0b0a03021e0f0d0609120f0c0807050f101b02030909011403070b0a030902210604120306081204050102070f060503 73
    0x40d01050101c1c00308210b40320140032030340d013075007880c45ea80e03c03070400c8188103030300004210840b500000300703501d14003945c24454501403040c00c00e01d180510907160b6881e07035141024040303400c1d010040c0001203504500024020840201100c0e400160707540700c249801401c444117503601e944240d6070ba03c02080580e40380540d00400d80d0164540c1b204c54801c0300d000405018664400c50741080004031103005000b81607203d241d15500030765401c000c1c0416078000300c600c100060b04c25404120107885440c0400c5080014140c42032050045520b00705403440c500b80303400c1c00043e9451a26848020441000d81800c030940840151400154185540c9a002071f40480b41402140d4552489202052050b44d08008841c01490014103907907032203114003001030141034194800e81c000c0702d8000034076840c0220140018031000c0c3d03a4001c0c15058540707a503100130248100311000101610b40001150328502448182c8003110380714502a9140d2412001900344040760344094210000c3c000c0c200600d5420808880d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 202921447 1250 202920197 202920227
    0x1b0b0c0d030c030b0301090605060f06192010050907050a1811071704050f0d0503030402040923071707050a18110a0c06110c0c0d020d0b070801090f05040201 69
    0x1c03402c4084408228000c0c0807881c0d286505609140010701404419803000307015810546801d40b0310030540051104e07030701c114040202098050803064400754811001414003ca0301e200321130f44408648031041c40c040081d2840d10070240c4d80c01c14050741920401403007000f0001512100084e514169081481c5100e9241c28075071a034641c56159404031814040b520f000ea840018a07000200402d60a04150024081c0c5409650401c5003036100e0b181044000801d298020001c0d8510b5440d41c2c24000504404081107503512202c1c0070880c1d1040d525101100e09501e494028800e261400081d0140c1d03241e42c40c1e00246642041c6024450fa4541c8032241c0180d0b04610111079602c42881c643c44002d10800460403150710b000300381c1550b17040d801032400c042c043c056001444216540b500d070360700501c42c13401c007a0600c0d48642c10310b121070b003171800104200a00041504503d94820b44031158890b004907207880000c1d02000c010300c4407a4003886400b801710640c0c0000c21240c50184d00203404074101c54080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 202922697 1250 202921447 202921451
    0x8121c02030c0c0705010f05121312020304060207060201180201030b040623030105100302011e140315120114060f03160803030f0a091e080d09080a12051b251b0b0c0d03 74
    0x5400440ae0380601000c10381c3c07003408680380b050034810003500c03a0094000d000041c058100c0000d90707507205008110340d51031070002d511003454460b801074004142c480315064015803078241c0090030301346544c451085240001d80000b1030032100000c250031100700a00d4414102c8500e00b00f480543d81c014880d450009024201001421100c102a1440002c1c04041d070251200082089a5911441e1031000501030555520428030503050482d070a80c1e81c9650550181004100007075110318004114844031000a4192440000c1c028030451210f140c0e50000300c2298000018031a40400c20810300b0b40c03280712081c0420055150f82d4400100340359110651180d06a140c1002043c0001c0300d04407500038190440400c59204149003903a1960403102485012822507010256040c0a50096510480a038002031030901c02d15400118290003403400d18450143c4100c500c0300311a00040d1410500340078505404400c9003000143d60f0300c003000d40004400c1203091246000700e0b400080c410b40141094200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 202923947 1250 202922697 202922701
    0xc0f052502031002030126010e0d050d0e1006030b06120601051e041b020105010b0f0405060d11040603060312110616020c1504031b08121c02030c0c0705010f0512 71
    0x280340c400035089600c3c240e03100000005800c0449058491641070710703042d9807010820740e0b0b61207080780c0e040d440d400d480717800c40d42c079900081d03114500a03e1040000c9100054200c0e030075081e00c0c54540d00030004441c5039030b540707401d005005c2000340703c1d07500107801c49420201015402d0700c2071311a0410300c181402505490b1080f282c014011103225000d500c0984100101410452490300300741001c012714000d0b518240010402d04031500c2224040300003062218902441c1505000840e8054826030313086640c0e940000b124075400340300600080c8540c1d5800304010b4114140500c001604112640074065803942142204d000807170386540c040845000b042c1e1424500300d0517420300340100c03400c1c0e134040b4208551050b44120440544256030103840b041c0001c0300301d00450741296866000b00c804030360101100070703080200340c80142080c0c088004641c038044500680d407801d13038000f615802c01b001c8010404485507882000355800401091030001d29040011034054000e04c58080c00b40351007100400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 202925197 1250 202923947 202923949
    0x50a02040e0c09010e01020304080a0b0c0c1f24060c0f0210120e010603030512070e0907030905061506030105062a070f0f06052514010c0f052502 64
    0x1054030020140c0e01142000352802848034003031944203080c0d043c041900380e903050390300794800010b0307505a074a40c400400514185444403070a500d8001c00c0420300c1701080141480b03c8074280b1048040e85200441c03110403041c111412029035031000c1014115404002580701a1411300201d441240c800b410400c2c20021507081c4500d01c040c140d900650410382400f6101000c0368008000c030922628400b042158003000c01d243d9090300d110784409400280140440a0000d49a01c0e0f11a0440c00c80c1c20203600301c3c230403040400c803601c80403548840801c0e0703200012014031000b804020340c0075881504403034070001000c000802901043c041e4030b00a040c0880e5184591210444240e900400031300c82042c200c002d158640c0d0303a050079018240383c1c0b04943c080091a107600071000801c1d0390b003d48549041c4510b01d001e189450784002c8004180000e040600070114900c00084840c151404001041c6941c0d079260151420103a40c00103410403504003c082c54201a0700303c8245501d142c03141102c10705003680 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 202926447 1250 202925197 202925201
    0x109051e010b030a1d060408090612070507020a0801140103081b03071b060f020c041503020909012403020a17071d040201030605010509011704080d060303080a0f0b060d050a 76
    0x201410340e4880440300003140030b01403400618420140302c0d205000f110b0000e0582c2d244a1242450b03c01e5a511000c0810005040e1401410b1610f10141a42c0d092810035080d50703030300c01d0040d91041c000c0b40000030140c2c20b50030320852100c003a0820704002e000d4070341d0075540c01285090501c4081c15140000c03565180720207000c00000c0600d4080b00440f42c6494040c01e20390603480c45001d035100591600100000c80f18040c0030604403115058000d0203c1c124004140005400290b80c0c0c0285440810700100c01a40c5080e0342c0307400b80ca5100c00008100185c00040154006043d0f01802c08100058003040147c1d5030001800c2034407003079010019181c2c480985149840881e40010007610b22000441c0781c074510f5400c5192046000340d0b0140080c0e50342e50015100e500c40ca602a0780055034401c45107098020309420150402c0c41011220314000c8107003190b030101e90302c070307081103000402d81c2c4180981b908242c02810846c1140d442c1c1042034081e044005501c5105d00000403440d182c1366000508615055 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 202927697 1250 202926447 202926481
    0x90c0f1d0a0f060908010f0b010503010e0a020d06090c0806030c060403030c050c030609030a021203010e0c0711060307020c04060b2812060e040b07170a1107020a0312080703050906010905 82
    0x48004403041900e5003c068070015881c002c0c020700c2d61800c50301208822090060b40000001130719a10300d140d00b03040301c4040d103200c0108081141a020059041da01c4054401d940082c9906000022010060080108a60030240c20148203501180c4134960755901c0004440c11a640760400000c04d022070302d04281441c1d00500500e602d07029810030441c43d0310000c001404088116070a80300302c0b40594800741c0d0240030038011100c42881000005081280403001400101d0055152510410802001400c240e10072034240c070050b0406905400c060405014010150008944d0700381407151854455118035005005401c0020741d0112205400b0700901c6145000300000b5001d0200940b40c4040c0d600d86042901c003102c2221142e40091041c1d0702c036142444004034145080750550700c450b11402d004d880301004010f01c40300b04001e14001030703540c034000b070b001144a8400301d0944e00107114040c100b144010240000d050400c41044802c210110310075040d03820f01140010300d91105140110000b4403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 202928947 1250 202927697 202927709
    0xf12060e0109050304080706030e0705010c0501022b060914060105031003050f030304150b03120901200706090e090303072f0609060a060f140d020604030c090c0f1d0a 73
    0x1c1c00b4180700502c071011000b0810340d0340104c2102c40c40c5075510740441c102c4403a00414031080c1c1201c00d050001390b01c1006a00d580500a100160038806400942d4009810141020036083c500114080b040c3c280d50090b84001c080055080102e41d5000d40c5040d020100200240d0410100000083d040780340c440c90320001d103400c002102e5101d020465126580e0b0310176039065a400090703185024459031240201800300c035000e000b4001418070f080e03407060a03412190030141400f40600509140001d060001c07000c501d640c0e00100300b60b80c50b2410243c8110126040645c00248000400801b00000011a500840503140c0700102200b0101c2446014024111200072040c0e1900760703814004000a081d4058420081a6000c58440c04181030884a03103102d16407141004090400100343c4680041d2003905001e0304072411101968005940740e4415001110301c2c004191060003904020700c00c40441402a0a02252003d10a40e015003202441c0300340204405940a05a5940d10303412840c000600c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 202930197 1250 202928947 202928951
    0x9090516060201050603011d2e020d021305030111071104090b0705122a03060607050a08040905011d130614090c030f010207080405010c03090e1e09070f12060e01 71
    0x3480e0031000b406000d040e560980706e503007094018142c05081e004e03d2445495401d004042c03c00d2846032494800d28107518598031030030b1030301c032280316862540010001c54120640050355050740303a5a008460f079454020340e000b0303850050b6000b1503824a0307040310442c0b5000071071201c0c04504140000c01801a442c1c0091000e0085030a0041d000d4004000c0d1109207103001034103407aa9100d5840070f5070000c0c440c43c004442c860080c10b0045412105004541000300075003c14501403442c0ca5044c6407031050b01d4120b52603a400281003000b10868810203014002010720601d01c80c1d055600c003022004040d00d0002012181007000003041345603031004400e540c07030402110452405007001a103e25480c100c1901074000c880103032240d06018400c07200507540c0000a1030900303042a00450741011a1042103090160024001c50381c0d800f000c0c841071054071040801c0a200085c0076503502d8012019240c00c00551203400140301e22850103600c84142c881607101d02500c80801d082680190101d491f014803954 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 202931447 1250 202930197 202930199
    0x210309011d040f0e01230c0a030b060a0f02150907091a091f051504060c021206090606040b01023702060f0405010201231306020f0d0c110708030409090516 68
    0x2100f903007044800340d902c0c400030845084000a078807040c00c0c0224840c1b4418a80f200051550902c486c05481404064600001d105258101003603269024101c14000710700319605122241c1c0e410465480d510300a54400d030b040c0d040801005650707074010300401800d40e441c0d01140c1020481c0101101e44c07003900801240c0c10b0b040c150b40202d02c00400c0c085000b180b914104001ca614204184103002c003420661100d0f15141c0f0380300c0202c03005004460201e030720003061141c502141d1070800c2103e002c2c03c03003140030b002d8038140a02000304441903442443e041d0341103003429040b140750032140c03881e03480103481803d541c49401700c083c6034400c8a82500294171180108103071050481d070750050400e55500f80c0081241c030440701040a100340104126400825403880014408040004e81c14447d621956000d420455481344032034498018048442d0100d5035804c02c1c05185500c400c5103102050400040d01c0118240b0345603680303c2c0b245020310801e0a4590b101c08c401c026080100ea240101d00a20b2510b010b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 202932697 1250 202931447 202931471
    0x2012105190c0203040302010e040203040602090d03030b0102160503150c0d0216020301061406030412020102070605010e10050103060b09120f0f0601030c050f01050a11100e0705210309011d04 84
    0x320807040d24903031003107140603a0351081c6030000040b50107a80c0c0503103804020310f11030303010080070b948010012510a0380911090559480e40348111038007500c01c1c2c40100c0d4a1000d1000249459900c88104100c051286000c1000d40c44c0440c00c1c50f038244201d90120007540c1c2c7c0038a0300c8168419035002a4146100140d00d103001820480d01d148800d10071002801015070700e444520a0b0440300d400a40c1c03051003080480e000580ca9840742c0f000180d0740c0005800c001060300d83c0d10895000b6440340344010400000c2103644469291407031b015007070900f800c0100c0d07400c0510a0029001e03200c0c0050207105410f52400190f081008200071103503401c01107842230341e103500b11541c490000380f000321242189524041241d1420410388126494103945060a060441c01c0072922282c0b29000090350340110690380b6014036050003002180140c0400810030580340605128680c03806504800000708000303102d002441010045414803103003442d080c40f1111b043c0d0030b12140315103d2101c00d0303401803801c040701c405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 202933947 1250 202932697 202932721
    0x102160201050d0e031b0709110909041a0c090405070c031211220806090f0c06031e0106080702250510051909030c0506031504020c0f0601240212040302012105 70
    0x903464906d800d40e861596035088010903607404000c00040480140600007160912240d00d5912500808102c0e05103141c004008516110550f842d60307250790000f44611445c10b2074020140c00c07281620700325034043c0c0d10741c500402c03001f45000180c00107074440610440b040c01c440f06035424540b0901442e010a0550140c41445108130f00c5940c905000c1c0200103241020041030380d101c1c500e0268044e0410b1402ca904011407580000c0c102902440070f02c9001d0300300301e070352201c0d40e010f02503d4441014500742900c000e8548140710313410b079481d00b1540ca03004160301f010001186c1158801d903891a804100c80c0402e0310305024003841c10350714000980030200c102c0e0f0b00120250803640110301c043e808503102c0c4140074031484200c545011038800301200304444e080640c0101901c0c0802d5058510001001c14554182002039011540003034281e910400700100d090100460a9a0f60009043d040560781c0480c046005910000c1d040c0001c58800310740c0e164484100c68510700440b5000c001ca46401400b58031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 202935197 1250 202933947 202933987
    0x21002031c050901060f081b0103060b0c070302091815040f05060412081303020616090504140a050105060301080d050904150303050c060c0301081b0d080a110f0102160201050d0e03 79
    0x1640d44c01c09000003406003c2043c108140c9207c400900400d00d200042c410b02200380c9030f411410141d503440001141e05524000c2c01d40551080090310200717186004000c3d00c101c0c0685500d01540f6640c051141c0040b0000c0c0c5500ea82e140d002a070002c80d0383e00e051030103c00e101c0d0200600a8000c42081104101d041076059480321036a80701d1038080d484013802620b1420580034000c025901401c08510645c2c0344c0001c0b80c0b200a05441e001030310580310b8000c10140c0f031001c0900b1804003002002d005050f916406114003410098a0450075989003807039a0350758000e070518001c03d00c0310010b20780a250325590005031100c40000c0741c10074400d5403072a001381107901001180c1000d02855001c41d14100d110b4003202d0403140107200500e40300240f07054074106100c3e8860142e0307000e1011003500c00021440b40c0508182e1807651a50503a12031500c070200e0401341981d0341c900c1c041c0d05c10020303d081898043d80701c8200c40d80a2030b05031f48800e0f40c5c800320740051500d4001c03031040340310106650720039203018100e40b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 202936447 1250 202935197 202935211
    0xb0408030406030c0e0603040b04020d050318040f0b1f03090f03050d0e0114070f11060f061207060203070b1806010305060a0b03150105040e0304090e0d0908030a0c021002031c05 78
    0x401e420000c00c017201c071301c106a050b4580c000000c1000c10007045030507800580090004003a0224a882c0e0b607117051450784800c0c810b180e03040110240d42c0c943e00d014807850903101c49910041c0040c0221000240400040c1c2d1703601428000d110512010291084d40458045903008032880e42c010b4640c02c028001da004020300f2468241825544035500c0302c18020304060f164144000c08183c0c0b180c84065904004c40f45a1100b0002c0c02d01c152405e10101704100c90180e001303403465042c1c0d400e01c0d10604c10503003035041901c040d07540415810004940e0000480d145c031504003a40c1c001d04e80b904180d28600800c0c4064800207442040004410701502141c400d02440b0401410050110480c042c140c488150b0545000a040c20100420840c10180c003d800c003090720009a9140c10340b15400700c011540c040c0343d00580d60f0320400f00e6900098025402a01078850705004504102c0000700050822186e014001d02074140c00c5501d41c1554003c0050b143c40c2100400320400ca099085041401004116240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 202937697 1250 202936447 202936451
    0xb040b130f030806030c04020706060503120408030405041503050f0d1d0603040825051614092e1715011d060d0b07120c0905030c09100b040803040603 66
    0x810034500d50351015490180e4090034420150049450559508200805080e094001d00d090f0242e140c0d124401000c00d140300d2072000034030790300b00001d05141ca080b0702ca501520316001c010074060181d001003624112070080b600462115070039442210051003580c0f005049116142210303183d40d0010400504a0085560b0307000c901e0140100c00c01000b0307002d960140c0050382080424003040014000f081400c8615801018482d806280c5040d20f19503e20292900c0d00f0009042c4040920303030360780c0002000d600300000b5203640e2000004442e498040e1101042c800058031800c1c80582145503424040703401d440074898540d0380c41c8200451103003413014203014004c1d80b120100003400340314a00e060f50554203980601160844400c8000407002d48080da000f20032801150010308403041c45c41c03140ca80369581c6000c00e641103041d00261442d141000090054940087c441510001042090038101720b4200d82c00f0b0710f03038202034003030075002d604040c194400014001c1000007000006104440c559501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 202938947 1250 202937697 202937701
    0x709050a052a0403060914030a0c0302120301030209011202130c030b01020f03160f2f0f0306070212130b0406030b011205071b03020c03011505010906021903050f070c030b040b 77
    0x41c0b05025030342e1101a40d0040d8107010030301c0403034443d6102c80f408a108008500c051008210000c0c0b0f50b400002000300041c0494100a0416505200700b0002c01920b0107802c0c1154116800548804070500602d241c80c0811400c000540d696024516880040084104165a1402c40041c042d20080d04041e01600c260400e84600c8a0000b040702c11080f48504064100c10455842a4250101a00c1901d1030901c590380120304501c0f900150080050410014240100c203038203000881c44146055031182d04040c040241ca15004228040c0c02d0350088501c1d982c40c032010046101030070703568001520340140803501148654041c1e100c80d00d2420241c075000344900c0034400c05420341c0c00c1291950000f0300b00d0100044090072442c0b0800c4058840e0054900200d20200402c2c2110f504041c0b4561182050342c0030042542c1020b0b914024003190701c00391903104014030a14001c000d40302e10003400c02400094206240e424142a9a0180c0d805030051041d03650b241040a0000400d071410340742c28400c500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 202940197 1250 202938947 202938991
    0x20910030615080f071107030c0b04180e150a060f030b0f0f07020c040b010309050307031e14030c0309010b03070b0a0212030106120f0216050105160305090703140709050a05 76
    0x3000d62140c07110300000c41352591010b030b049400204291169900d4402c42c0c102000048001034250050320412261540ba14075010085251141c808180031301c071442c12080c0f1074042804038851516202c1c111108070680c0381c602242d00100f00d940d0158041c5400b1990120411044052040c01075901c941015440e031607101c01c41c60034070f000761070100c090b900540c0002018103050b004195800c205060018110065031a030f142180d108850880c009062042800d81c038400840345603841072280c1c074003081417400c075070304020140c03102801909032044040002001070fa8250410b00e034031070015050350740051b07944071503c4c4160403e003604005400b030350f92042d10600018054904881c8507648030f00c01d220920410100501e01009507600107074080020020000101014540f1030784684000940361078580e0111002502d0244102c04140c1031000f4441c020000050184c1580c2e08011416591210704841a00c0c101c0f103580301512681c04c10701000080b01d43e40e8041c9104030903400c600400d002a4203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 202941447 1250 202940197 202940207
    0x301050c0901230d0e0c011e0c020d05010204080304031202190c0501030e1c120e03210a0f0f02090f0a241112040824040f0204020910030615 62
    0x41c40745002490700d4000a04042000c0503070400c1221040c501c03441c0140425002c01a1454400320468903440415070b00300e01c3d40d0000341108420003402c000141074500400080090300c5d40e43c4080e100300c51a4007884280103081d411100102071600489603941e590f8030745002d9031502419450b001d4000d000412030b2050802030040c042c1948641c2c1d8042040c1018010340c0102441c1b14007018506c038031940a0390107a401c50071020051443d0315011204803286840c0d10544640c69402c60440e00309020001c603940c1440c0a60369202890032442c08079954004044000700001110002041d0a06128032076180c032179401440c42040c282d03007240d01c488007401440416040382c8501204171500c00c05043e8801056070804014030428a003010110084018103440c1c2614100007500103c0c2c0041c0030405140200034851403140c100131011000410814407540004c001003014160748000c0c0146c804665495040350700350600200145001c11607103034003e00a1601d8010444001c404082c80300c0100e01807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 202942697 1250 202941447 202941457
    0x302090c0703020601030f1b0803030a0f0b030706030902010c060c030203010306110304051b0a0b191701060504090903090e090606010801080316061d150a05100302010519050d02040b0403020301050c 87
    0x5070000e10290340796548802c00f2201c087c0054846407502e80302014610440d00314040189103200043d0744908010b10010202c031150b40240700507a2030100c0041c0c46840205841d01150366078280040c149820b0700059a5400c60303504001e1800f483d1400d90140e13560190f0207103040e21b0192404101c00390603520712088500c03064a01410790340c000c07a000c0c070000301001e4030400414030140100d02c8103583c80035203000c070b5002030680140003a01c11242c0c034000c0f5440102e6a8200300000c070740020030351410f01c0c05842840b0711700482259a88850821084c1806403200c0c1c0d0042410030504406442c00503e101c0e1261020340700c2c540007171070b03000000842307000c00000d80c0e180d040c6402c0c02c81c900f05055500c44c5c004080c80c42d25894209409032994407501001d00c410014044e0040601042c1d14144041e5011200001c0c800c4049400214051026036440b00994682c0502840e003440c3d4800b0b4010305075007500800d0441100d460000601103103441c21a005401224406e0340248001d44514a40391054022 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 202943947 1250 202942697 202942703
    0xa0207050d03050922020c01051e0720070b0307020d030f111209070b070f0b0702070f0e190c12060f050f0616020d0b09060a11090402070c08160302090c07 68
    0x105000c2c2c01d54a240c2802d01d0110000e8001070b21204a0f401d001d000147d822480c4210369907555101001711003480c0c9054080700d88409840b048039854104805400018041c1c3e002c820102c40001151a45400b085043c000d03244110074292a86010040207543e03003008a084c00010741804200070718444240a084014120941c800f405d140804202111808004098402612880000040d120185402402c290340520b07642c550070341c09801c104882e40b101409140031035200c007030300300b1000f44180190710645d450360412510545500ca1070201c00b0115246803809940b07004a043c80740758010031140300040340b000052044c3c2e0350303996204008894520440760081d002c041d9111803450008010014804001c0a03100714000c1a0081040083c100c07108803205818001400074006007040410b07405030481c1400d001e0314000312002d04150165a5460b8000c580203c6e0500c04c0042c0c810980010700307060003c0710002c0c1c800d141d007103894640c0d600c0184d000d031168002040310792113041c044a01c52a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 202945197 1250 202943947 202943957
    0xe06031006180c050405060d0e15010608060d0f0b01080f0c030c061902030d09050717011b031508060a02121f0303080a0f020c010606120603051513080309030a0207050d03 75
    0x2101091030003d8005409a0020080c04000c04512941c0c1e100c0904101c1e0340c1c0202c0019013088510070140b4004102c007080d0492182c1030010840e00e44e001c507c413940b090041e01c00181c6c580741843c04800b50080300100500b004080000401c0386a4009804c008480c6200304a50541e1918002d054444610608550b00000204455426940c25149008420b00144100ca181c80c0502424004558040100b200d454010900800c000d5281c00da080882504c5480200072565101c3c490301c0030050640c000c0c0c2c0905494800c040c0001e8a0015440000c0c00c2480540d03840f842d00e094150002e41c080720325498031841f080d0114103031015025500824000513955282c1040c01d6441c01e40c0e4408000b031a001d002512107015244680d41800a04a040044000414000d00301040507007184d5001c1d480c00c01030340c54520b0410129400050704440e907542841c0315240da445291402c0c02d940380e04040a070200e00000309002e10154008010181e103903442d406e030382c040c585a40800006181d11000540014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 202946447 1250 202945197 202945229
    0x180a050d0b04021e0d0812070f12150503010e0303010806011d071202042d0605030c090402070212011506090f0612150f080109020a140603010e0c07020a0e06031006 72
    0x10426401d040703844134901c3e8032014990310f0180012000721070071008440032034020404804094000c5480703900510a420314030081042160000c081c04d007a04490f1082030b8689250702c201e0051a070b100b101814028009000850460300042d41d03941c803c1c402c07400c0c64400d910002440d0400a088550541e0080140408030b80350201c00300c90740c043c040580e5080940c02c00000400e13145a07498540000071010350440303510240361034007426040340d81c019403d2000070810010054840340454485003401c807001a01d841d00da00124a510845501445580d8030744400c1160380b60401d103030700b4102c0d203440d0365585100b5200d403140301c07120065200301302c00b00300e41880000c6007084eaa0002d20f51011030200080e071440c0d54400e0128519410ba0209480340d55401000b0198107241c0a003202a05004030050001946c0c0000702d000c0348814810500103001102c00300d01c004a030f40c2308696020740c00600044420381c440c82ca60801400a4402d0b52091003a0f02091a5401903030042c101103421001c402c003280f1f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 202947697 1250 202946447 202946449
    0x30a051507020f03030a0e0d08060109060f0909061212050a020606040518120406030c0302040e040f030908010912030f140408030c2203020103110309060606070804030206180a050d0b0402 82
    0x5500007514001c2940110321501029180400c040c5100c0c1d02c48103408100b80e0f0041d03105905200012075000208500c003c104081642c00261030412610b1510f00b400c44070032a0700c802c070740c1e40300e95400500b0303210b08100001071038031020607555503454026920482c05200140701996284100304240c00903800001c0011450319041c0d000c1a40182028000705400c6540f0640701d0621080001d800c414a401140c1403180300c3e03240c480c00c6a11085400c0462920381400c0041c071071a00002c0c002040341c0b6919400f4010184191406801440040700078080d00c03c141ca0b282c0410281d11034454001b034074100e1000031103045c6010707002d03001c40d510b84000f66030b44403610791117601d1388010148030301800c1c10010000900424004030700644072549400c2078081c00e62000400b070740e16085141780c10032018010322241140c0460300c540c0012040311389aa442d012464a200180a00e90010313621900118400310007038065035800404030000ca0f5420411790702c1c0c404010071080f0081001e4402030900d0000703001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 202948947 1250 202947697 202947733
    0x209010e071706121009061d0a152003040303050609281503050f2509020307030902040c0c030e0a06050901030b0a05090103150c02030a080c090a0506030109020414030a05 75
    0x40c80980f1100a50030008810b07881c200c01170000001c0c07683d841c500e020621000d1f01c2407400b074400503100c2c2403030440810041ca554449290020b0100c42c07120081815629071507108070b00180d000c03444250000b28400800e0303100d8004441c15804170b42040c000910360315207000ba05100300e5001c0c801d2580f0340e25030f18100d000d0410007440f4408003030303598030314240d481a0380c000c180083d4401d01c0209980112440544d0409402003509e4100811a00c518a04841c610114500b902c0b844580140c4070f40c0c03002421400b8002c2c070140a508540b07040100311203258080c4044100d50b00070f44604c0c0140411100b880300b40780e5075100300300c00541d0500c410070b401d611035081112460001002d01d4907007500c03400094010036080c0e008980812800c0042c2c0f01000c840c1c00340d03100485541c0003640c244401d940003d0200d0500900007213000000181502030b80d5100c0d02000e02402e400343c6000d46a41c0c5801503d40203600500682c40b0180081c14200750350301c0d00152850001e98814041c0c042c6500601d85145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 202950197 1250 202948947 202948951
    0x1061214162105090304080c040506211213091b08130c030204050f0403180e0610120e030318010209060a030203040c082505011707050c0f060901090209010e0717 71
    0x142010034071460a004001500890b4050708000c0c000d155201d25041d2240c1c40e01c003200403503502271070814040110300c0d5108000b900640802205c500211003211110f1030510407245000301c82c900c0c1c0820124080400b018000c001c0d1500e2803020000d00d000300205001d140409101440000d181500152080360200c0003210182d21840b400490940c5036800113042c0c40046514059115a0208100526600c182000c511200d80142c01c8400c50510f44d1f0060240c0006206074040c04d40c00361194500c502c1042501c603800d15011040007000c89400310103403a640169140c01c224004035017000c40400d4107200b2181c0c0103000a2070303149002d0304898150065080200f007500c801d42114400961000280a504145502c1080d500841040c0340300900312041d10780c016904012509003000120800ca074440d603041100b50402e6511441c0a0781c4051802e020059884024001c40c8140704480303105402c88281c9074401c0f6108900c0340e80728840008410b00071603580002800c1c0200d0502c010301a0a00d0725 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 202951447 1250 202950197 202950227
    0x2b030302160204110304060b0114030103020f010c05060708060a0504600e06090a0e24190c09151206060e1f020a15140106121416 57
    0x1079603610300d030005400c40c0e200320b40105010b4000001c002c10080f0034812501000800d00b03050b114140520021305140c001400000d0040b110300c0101c0d0300c5030b800f078161481056171003022141d03a843c20300401081e0000540d000ca02462002d9804200d03481e03d170049200011030b1104649a407100815a0860300025031a030b5052600403103801c42a0f1516124040a0003a00d102d1000c03e08000d9180310380c032000680d0102e07101168060503c6400e1f51007949103500700580250118000c0f645510181c00c2000186003d60302002ca00390700000381c6c048559061007650801000d403032035060f0401501c04daa910b900d9220001d403040d4070174008400c03482c44004400d1001c0c60f1048410000c042440f040300e280d0713084a00480c244480385481d601d022410030706a0400c01d60038030440291b6600203559900060002041d01500b94045805c2410907485441c641e00075104d42807082d46d60f10000b9180010140310025083d041406090820030400c01d00ca00034052008002008000d229040f144003004d0081c0e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 202952697 1250 202951447 202951477
    0xe0303310812010e01050105090a03031805060316020609070510300605040c09060e01050d111909080a0f150e0106061e08010b0403120912050c2b030302 67
    0x8140451112070241240c440054410030340c65040c000c2408400340140d000e903041103000c1180311026200c00241d40300b100e916081c0840c4181495240c040291541c1e0040b40e00301a010007003140e110180201c502c1342e00d00d5602030300c00c103840700800f040c0c95402c03900415400c01c00c0020182c0301c2d54801c90b501c209400b00300b541040c21214035010304458114001d44134600300c2d2507800a00c551f24103441031341e0881000d8248440f00f01d103086c502070940280d03070008905116000c070340381d00200703076a8000240074022642c0235684c0b00c0a6000403109010011019800101e24130800302e0410000159908040c1c3c0114000001c8801650340f10301e804103c0140d404aa034540041281c21002402a403019044603111500d6016200c810742e180c4a25041440042084030401045805000c90854045d80e40010854400a40700310781658110080d501804802085903505424032001203007602101000321a2002d021a00b61168140382000700042030001a501c085103001034000d41c0140307559004036040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 202953947 1250 202952697 202952791
    0x4140103081602220b010e030307050c040c14030c0301061707021207030306050405040b0a0e0d09090209040902090c18040209180a0605130e0d050f12150402070f020102010e0303 78
    0x6903e0340d00c081e1441a04916101c0d1803502040d03030001f2071040400d80650041d42070640d1629081c1d40c80c401100d4260280350740d8850300c0c2401d44140f0074405144050440c0541d242003070640301c036a0f94070901c074005c006404407540d1a01a5400702c0d800d802108103a000f0400d860010340f950580760300580c400c400341982c51000240540b20741c080d80340f0490080601004520300074404c14143c4598036211050f5402c0b841c0003001c16070304049440e00703658040e8001616251038030085001090881006503100c030344035041103040b0551302c004100c4140300c3c003000c01d010f0ba4614180020781c040c03240c0c0f036a80410213510400b107a020340c0811550100300f061340071400968030300100e0060402d601c0e0200c00035407141500544803104002e10000038a807840c0080c0742800d401c2c0c80b0380180c002c05140d0300d90584c45401060407a0444641c1803030000004004540e18405071801250f003000041c8124099401c0c00c0103c1218200441664440c034104201c403c108100c02034400000d68401c1000240d01c8681d000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 202955197 1250 202953947 202953979
    0x70e0405011202100f02300f040f05010906170901090b150a08150412020309030304090219030b0f040b04090506040812010e040201021513051b04140103081602 70
    0x611402841c01141d0600c041c2c20500600071001411800302042c040c135000352109036580006c90641500342080c20360500c08001e030500a000f402000700041100011030300900d4004642d0050007280c080740104450b950350f8030010341c0c10754501e1041310042140c2118000b01c040030012160391040128000185101e0741e40d841e802c0c0002c00751060041d942415261380c6050401c00301d5003001e40003c0c4010920840d03075900101d542040204001c00030000c4000300d49400d4020000d489078410001c0c160303a1910345818500c00250050055480e01c11070825128403500d000e40306800b070b20038015017a030b001511403800b408040c100c4401001d80040d502e044090220383c050003628002c030300c07944600d644c4e1150074071007a43e00b080603089038450442c2001070100503a0005140a41178002e6501400076540e19510400268033381d080c060164003c09541c0441202d400103a03407410230b421101040030340c84045294444a009010040075403500300420005590091060f201c1c2d544000c01107002003001c05 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 202956447 1250 202955197 202955201
    0x1e0603330f050301020f0406050f190c0317060904080a050708160b09030c0c090406181b0621050c1b0105042907140c010903050d0b060c0601030b070e04 67
    0x6000005080c90421040c40340c01d450016140040c00118025400d00d010401d9201140c440c070b114901c14003000046684d480403084050703030000c002440080c00124100c460207040d06d0282017048000130500c03048048481e00c4c48800c0760140c6006810058a5074440d681c507900d550066550105200b014056070002074100ca0007040000f40180111030b4005d80f901c1e00c4802004043d140d000c441e0070510840d0b0101c8800182c00e030440c0400c40b200030a986440c20440300401c4241803240c0c44000004e80301c420301c950810740c1c0300da0201c1a040c5084413541e034070040b1460304558403034115200c04854007107000d1065030489600f00c1506c18a961070484201e5204102d502424605072059442390100014001c00440300007143d4405128100c030b03001c07220b03603138031800500a00e09424442207494800070700d030b00481035901c0260341e040200071490307030b07414003820319080750b00424041030501141c5482800c0c84400c0e2540e4100110040c0304503401c6540c0e4489080c00104040108000c0d2414510655914 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 202957697 1250 202956447 202956521
    0x201140a0e03070602030304030203070615030803010e06030f0d050a0305100f080a0506010b090f06031306330608241f0f080f0109090201050c010504030206010f1e0603 74
    0x19464108407801e07100c003494149003803680302e401903420070710400000c203030040112500b441e03110b20300183e000a503014001894400da040a455010040000700740d1000c0000c07282e000d900d044044a50560395100115030f0742041000c1d07440000c500b40700d1144140e000b0b40000d90880d261810042c0980c1d01ca950005245440780c0c80001daa80c4118900c0042c0001840304902401010412074074000f0580c012078000d00c14112610302884000002030303541d41d07003a010159100c0d4001024448089512100c0d001c1224490300c956460302800d0480214803030003241c3c001101c400fa00d4000c856036444010000400e038001e02400c2580103506c030348916a4600c0e03112003000c400c1407251801a04042d80003000950080288803e210504080c0141941a100200c0c11541041c1d004510014a0300c0102d030940100344404005608010a1000b01500030840300d0507680900c5900641c030b66201c5940002d00003290042c601e24102035024850944a078000451006844c6281121045030500e108031020326 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 202958947 1250 202957697 202957717
    0x5030a08130b03070507030c02190621050f130203191a09010213090c030906180b090604080403030c020609030a0507050405010909020603011521140a090f030c020114 73
    0x212048112000d01c006405040101c0c0201d00f1460b00b003001400500c11013001509026004100c00d0840d030fa544034901e060100e403482c95440503540d09018000310f11039040405450045441034801c4203403803113003500c02e2003441805840c42d1070704258071000c2c00980109a801d80503194509028000d03003120004031078030070034049902402006403044030302000f4002c9a046d0340104444a107505244807400e040d6401c4200004006240340e10540083c55031140043c00365003841403544082c415083c01d040800d006585030103940e620714100544800080b40d005000103400d000c1440400c5c0b295255614072480984010b01d020030b8100028540110110b0031682644452018040b604050040500600d4104000d00001da0103a001952030300050060751800070484001f40da0031403056403000550b202c0340080e50902018800c0301000b401040c44076000090358680800c1d10821fa0f88a82c2c403c080d000000407402030b00c80da404550303900040c03808be0b041002282141d41c084042c01300420f000c41c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 202960197 1250 202958947 202958963
    0x3010902121b0915090919060b10080705041809151a030d14090a0506070b011e120b0702010b100f0206131a070201140109061d0105060406051305030a 66
    0x40d40d0010b82214100041c5940140014824060009803c001802560004491480081e45d401e680704c0d203800074122005040941c541c61420074800c40c0e82c41454100f85c280d41407190701e40084400d42d1031020a58a050020384104410810440155a0140e9140c1703480000b0400f00d01e107850b2410741d580c421350542815a564030303600742c6448010707003852240304096014240c191507d0b0b501030560014400241050076000a5402223076461040f180b016040c001d040903210191403c00c07a0103203000f40500c007180418858440e9402503455040021942031002201130311b1416a0f8140d140721019104009564840041c07c90315501c5245103101403050b81d545c0645035150400081c90020701034295045580c4110203e80803488015071308148a9918501015a0301e075207004074014824030101c680070010344000070949203025040034049520345040b403c450514034141c0d0485003001e116059200344100410494140224064403403d40c00f10300007001d0307540d60000b080c01e06a010004541d044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 202961447 1250 202960197 202960213
    0xe03030114040e010e1209030f10020a1211040b1606060b0a1202031005090c070b0c0405041b020d140c01021630140c030c010507110c031b0301090212 66
    0x400c01d8803c0e224202e1056000780108400541c944e07803a03052024401c49250340004004207161010403001950200d80c0c82114207861002001e03c0094010019a0002490405a0b10400102c601413004000d0407940307810718081c90505601d91076401240c45014201c0e08151500200d4203030b126a100034500d246203e03964040c509002000d42003941c1107000081d20500a01140c62031082c2920305543e01610600e8041d158803403079580b135000d158001400390030142e0411942068010291084070342c242c4051110901c2d00040300001410647c0541c010b9105902800300180b003400ca14030b5043d41c14000754548112494120f081e81c0c01a603580e0100c0c0c00b0101024104400d012076001c2e00344410300f182d181d858082c140390040002d125110703420411102c1c3c108028070248811581a4070042080380e544141003040d05002e854111809804640c100c249940401c00116108448900007005080310f040d071144683c8200382501c0741250190750310200728005882c1c10143c1b03c2800300c0100206201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 202962697 1250 202961447 202961449
    0x130303030501050409200301090f0302100501120308040303053112080f010b03040203030f07110108010506040609180f05040506010e0901090804030303330503070e0609070c060e03030114 82
    0x41c8006070f0081e8007840c45d145611010580c0071b08601d081e9848903030602d4240c02c04000003405010941000345c0740d024154100420541c000540e0300940c80e00940c28081a80d0321044411221081640500401c4c02c81001070002886517000c8c035404801211020340c2c209080301c00000f080500510fa03c0361003040714210080c031583e0400a002c21000d8504803c42d072900814114100d03a040c4541400c080010010604564003403055510b0003074441501603d950703c60520b1405403904c0452180810f101c003001140074102002220180c43d074544940385d160340381050024011100ca405400310700d076a210075001a050b280a064000c600500c010031095041c55884600d502014003800307600c0c0e00d05400c1b140000c100720152000c503034041c00c000515011001c100e400c0f00054100d050301ca002440113400c40c4c035070f03940301110945c0c130182c04640c5115210707142d424908209540259008200e40006402180314400c420f0405200746004200460450011855600280c2040000d80c800c900c008810b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 202963947 1250 202962697 202962701
    0x30109150f0b0406080705090406060306092003061512070308030106110d02030406120b180106030e0d0e0307140607121d011d01050c010e100212061806040f0e0313030303 75
    0x94041c0484081144d1440d012001342d840d00c2c54410280241d804c20000b40610403e40c1c001e40040d508048107001a405515207110a449180700c1141042c0e1380c0318884501c0d04000682c284074048009030035005200101c2080b000c1a4540290403451169030408030003c1c1038030380030358001c110356200c03440011004074480e81003c100110510440d4828401007103d564011106490b9140c0c8000001e040a1004003247d503141a01c01d0720030198030b909000003916a8543d016204c500d83d10b00c1902c100300c406000031540320b1682009c4541c140d21130034051182e110b5410340c808044400511440c074128840d9a0101103403d100405004140354007100c0c1c4030031244841110300c151003480c1100c40c04111000e2100401d04030f00c00c0604001011601035516030003540803054100403801221a070212001d5594040c0d0b2084014140b2035003c0780c003041d52810410b4450748901081c0c000d80d4402d648060a210081c01200000300c5201d0700e8003201600c0f40000d20007024566407003104400242e00b5402c010f01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 202965197 1250 202963947 202963961
    0x1090b0a06050607030f14090402180901140d02062101080114070311030a0b04180503041703041a16140d02010501060e15090a0f0e0411090411040209030109150f 71
    0x102906007001300c400003903400030b0110321412850400705014541c0651001050040c480c03400d030014400103184814609488142481d55803c4500f00042c3c0c3c1c0300e035015081d50240d00d1105400c408400a4400140781c02009030007080040786400260403290030306159060700030303403000806075503a241c80000340c2c5402c041d45a1007200e6042c2405050502c02d00c0b85440c1c400100000e0005079990340905156a964000f00142e02e00c1079030b041e00c40340887c10402d071643d1151203500080d0311441001c46020401105030f83c1240d08410800200307420362a9246199400242c4007099540158903641c001080f54402202c40c0340071000404a00072034017000b908591060b04072005000e032035071160400e55114110900d88000303001c1425190020745001c103001008540100300101411140402c403402054a00352140f03002d403100c09580700e140001e01c51511070517a005482814100b032000c0185c2856001082002e0303002d80000b520554075180c000c2c0e80000c44140642d125107440720b4098402c26401412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 202966447 1250 202965197 202965199
    0x42f0309191203090f150209091302010f05030c0c010f090b18211905090114030601080a091104050109020a021b030604030315330c11040b060c01090b0a0605 69
    0x32914120703500c580300c90000c007030480800c151311509603508220340c10030308511595015194031005c0406000c900040d4012040180c000c21550000a82007464143c6650a26806071a0070080c03207a03040c012142948000d1520906200400a0303c0c80d0700000d2040b0480c1c86814200001e0495182c83c0c100342e81c1c500138002c03200340303031805c8180000303140081070001c070f03882031883c044901c0d000e14581640305024103091144501c03107880441c0c1c64a03803c54002e0410500982e6000b800c02c00301d1700d40c02c0060006848560006010340001002c2091a50005900c54010450082c00d88112030014060f00c0e400d800c0340710b440ba000704142010540401101d081c00d01001c040c001d4003440300003c0781d52840020000790400d5150070f604049600130714540720150000c440d400c905600a001d001041d540d801401c207590101c00300c50000030501c1a0002d0f185654400c40c00c001032a14441080042c000d0882940d5105504000340c8001d24803d2180030b42e1140310f46c1080b00c941c03901d03c00c42021030303200d60302c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 202967697 1250 202966447 202966483
    0xf0405040f0b0f060c010e010f09031808030306090a020706180c05030703020f09040f0506040c05011d010c1407081912110a060c0c08120a05090304050d02042f0309 72
    0xb02d003907584030941c0b112608019503a40e03840d94400740c441405880210f440e1724080d460081031103d4000c02da0400001c0740d00a464018a91840c2055040351035a03d01c40d0858603001400460250310f0114820364200d071501801504010303807901d074a8112498660555a8010030300000000c000d9000740e41c070000d24007100501001441c41d004a10740604400555200783e04a174001030400c000d50490610302c50700300040750107519091400b4134013003049004007404031340b080c0c543e01c132000f00c1031080038003206041e501d10381031611b5540d0350340310b04035182c024100a0241344000301d1301312010401500c030a0700400481c20107200e1420880501c00c0503410901c100291181d980008500024039a1032869004d003001030b034000307150011540b0055445c0d009200000c0001c0c0500ba2b180082c244030b0144820000400076031300c410030310301c0d900c2c42280704003508449403070312081c05441c29512003940c0c5010214200e041d20340c0c0064890b4a884088a0020700120100500580302810084044003103020000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 202968947 1250 202967697 202967711
    0xf060105040e0d21020304050307110402090a031509150b12030301050607030c32010b030f121b013303020f09190c020706020c0108011d07020f030f0405040f 69
    0x550380c40303c03507081002060003101410100364440c540704100300f03422030890440d00e905080c508540c40c7e5001c00320545141d5001044030b001840c00344211240b01800800d85640d0a14595852400c0b03048048410881d0b5511800c0c4004640b0541d0300780710350301b00c600d00041e4109800c420000408515040001580d0040c001446192a02011070f28000e4250400c40c030010324914080074401d034494245c0710385010106554010340b100d02004000c00c09080c00070b1060428620500d030340c516855a100d00243d02c4034401c01e513032100b501c0060a1010b03103000001107941e40076010a00356078132240012200a0420034501d45200d181d030308032f0400c9074500c0690703c0350342c80d540005443d43c940d80314840c0715503040340101d08400204068104444801ca00500071030f0007410020b916038821717118041c0540181c42c2c256a0700e600c10310050303041c3c803116003000001d189000b1041d5810780e001041681076101319001380400410070005070900350809103203690f4640c103000c148010341d00c45d00002c01c195420005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 202970197 1250 202968947 202968971
    0x50702120415110319031a0910051e0904110405090d0804230d08010e011a031303110709050403020c0a080d11010f1a03010b010507030903140715020f06010504 70
    0x240d9a08042075a2403c9008690241a51400c500c00d031203c4003154901c1c0d0300708000b1940c05400090600d4a40c14100c250b2a024409220343c0f0b40048414a039100700103901440240b600120080c00c3c2009029078414511010000c241c20789010703034041c2c488400e4480fa034030741b5103040d000d150341c400c007444050207184213019000742c900b0f10042d000071f12010000c2440c1114540c85954805001c06e10011030fa44400f0328407000d800c61001b8041d6181c1c81303080c08004a00030b01810406040c01d2000c3ca07519244d0355500d10940344034441c03508228204404182070301080b80003000300b0005400c0030040002c03941000e00d07010b454640c0c00c000090060088c018100700d043c4011030080e070014080e0501c50707594001c00072003c0c01408009041c0300c2031440c0136801da28600508070800004802039000300b240020000043d5005d002d40f0600500040c00c0c00403c1c0005458101050240e44401c8100e030450f64844900030ad981d400c0b440e1250050b80201030042d1921400c110007401004192010030a40c10284 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 202971447 1250 202970197 202970219
    0x2040e0f070504050922080426120d0b0411040803030a060f05180915070504030303050a0b06031303050f1801021c120e031b010e0d051207030b01020115090507021204 73
    0x30186c5104285003036003602c5000280c44100c619035400701c5a0741c1e681d80c0720329405075990f075490320480600c14180200003461100081481d005000407650341d04040b802d004841c040c0c90101000794000b5100e011005c5400301281c0034101a10364280611303200c0c5009181c032003c03940503074041030001011034001c10035901d44c20500c040403a072101a02c2120390740c5055088c608142d1040b40d00500800c070081101003907100c40a002502d10a0342d080c4016115206050f0564400c0700d4441d6006004102040c00307901c42e4404400001d220f070400509000003100700c44d0030f9410001d41034202c0070407414520480d690511aa6030041700f034111240d030741d12620400038070101c0f0049107160240d030303141d076100343c000020001d031441011000d44048440321003540c1e42e8060215492a4401c0344600c03683c6000c0680140292108002a2806900d03103a40e0f203801100a0181c030390a06065550b604071851380a000b02006130060856002c0c0420181040b1000038500548001703d1001d4800174841480199104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 202972697 1250 202971447 202971451
    0x305030714010603020f1201021201030309062606042a120606112503080c0d02010c081b030402010c0f0f0309060203070c1a0405131b0e030c011206050402040e0f0705040509 76
    0x47d00c22100811840c00d0702802480b0b0000031030b0210034030b90000420194044140300c26140e0658514a22204050103d020914003400d081c0000d503403200002c0c500c1c00e2039030004070070000a0f03d50341c0a0003c44080703407100f81560f4000200080c03101c907641030240c030b1a00070007006100c49c0c5001d608030b074840320900740c4030f044540a02a20310f0842440c424105000d40030781000d5600942c0325503a40040d452050b030341e001110003030390165082c02e45001707603a4019159540320700001d8100b2140d8a00d17841e0340d4222a400140b040381480070000000d80403500cc2282c4003403640c0f055140e400380f8a8142030142400301c095014030215801007041400045900803500101c0e03641d07409602642c4003406440e00b030f60042c3c0d0002500644151100c004a00c095001162003040042a05610010030401200c400903504296501360b40080c0d0410360951203002e607118904821400081d13521384940004041c1d230311076840b82003880030542c00d00081030042c003202900722005040280ca0a854003020503805000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 202973947 1250 202972697 202972699
    0x5010612111203090a061d040e070b0706180f0615050a1404020903010e0a030e0607020604060e0a050a0b0a080a05130b0705070f0b040317071d04020403020a0305030714010603020f 79
    0x1c224a0b85000c000c000361040d9110007071130801240d460b1140180080600710091500704070703480e2401110704213481503880a210310b00c0a44589805c29110152940c08030300e080301d0b2a40c1e60b249201261503030b203030250000ca10440d0b00200c800b03001d04103c410f41c5d4071a20000c03207611044c081003040390394140fa03a400b202c440158661504100e000000c000307021700014290103500301048034440070808203c18a204ac8291642065000c020003400710034040c4400003900400308210601c2114012005102502d400609064400e82c49034045032042e002c075800615000d83c08111040c1054101985982c00600030b4410401468115281a000d6840c10340141043c0da9420119102d20f104104403004590004c0740c1c0c078103002c0c10b4902044150012103041c0c00084080200d0000a1b0381c0036101809142c0c83e03600c2e10844c04096900c0c143c1409060130b52640190308100010040e103808420038000d50240700070750b44074015804c084c645071540c00c220030707220f9140450510060340c4891041c80ce00f00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 202975197 1250 202973947 202973959
    0x260d23060409050106050306010b030103020a0605040b030c0304060e121309050c0d09020118080304090b10080103021c0f0503030610050c100504020d08030a060303020d0201020909010314030f0c01090501061211 92
    0x12203410f1680c01056030b43c102c150140180d40003c103000c82100c00950403288280d46144400d03030303034140442d0035001d94055507100c40b0080020418000c2600040c50b08a4000d000019041070800d040c40e2422101c0b60503900c02d8680442c0c41c17005403c3c1460709500928090000f400b1b0351a088a02c100035119007001f00cd50340c2d40d21884c0c2801d5904c0740900c0000c0c0b056116000c0d0210362210803441d5203402c28450703113000504050024001c0d0400c003034910010300180d2503007031070781e4219420007402c565940421120a00b0054003100464a082c0c0400b8840d80600040c40e601c0c180300c0d05105921442c03101000c10701804220903000e61500040b80c02e001c882d011000641921544002804200070100280598902009000140040380d200000312882a001c5404100e02c221050f4242e0061609855011092100410100706c6000340850b0a80408007038a2526800c106001c00707a8020a070101c0e1750b07a56400382042084002d05c2510046c0290603c8518501925500c104003c0409150607000322 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 202976447 1250 202975197 202975211
    0x160b1f0b04090e010b06070c14062b02190c0506010509090303070503070e04020406030e010c0908070e061f08010e0109050114060a020c090a0b130e06060d260d230604 73
    0xf160a40c005030703200100410b03880d034030b00640c1030090041c13425003e0001c3d011440d070108086880c1c000c0c02c0703450204016151401c000249407a0b02011980342a0400d26030f81c0810099040c0c8030045403030004251241c45024450003103007000da00d0250141c0185000d045000248596141d001050340d40c00070382c0d8500a40e4980d00e03104100c500e0030400f60950b070031a0003c07501099654050b0410781640c0710707440c000c00108440480c21500000503114102507a00403400c00d0101d0142070180e95882200034050501c00880c1c00c1d100003d020001c9034403c00507100f200144100507450b5205401009134040034481d43d41001203210308004144a4140308020014440031b403540244110f5140280003002c9a0a030728002da40140503110070b81502c0c0c85944010b10081c22030b41e040c460382c041c0350140340040403556119400c0c081c08018030b00050315034520300050401304101b180c0341903882010a00c2078a440da42c0520600055400e0440815400760b04a0074800030000780d143c0140c2d011004481c0841c0c0d0f4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 202977697 1250 202976447 202976471
    0xc0b04030306050901030309060815060a0f090506030f091e033004050606030106230108041b03032303061008190213050a080a11010c08160b1f0b0409 66
    0x189a16405203400280f0303e0000007e00d030f000110392045079981e40703440d602540c801d0710796202c1003840e2101c0c41c1e10550510000018500c0341c88007045408550505104240d103803070020712150000c40301e0b81c1421110380e00704440b6280a07c0076800f413410090902c4580662f07074000700e443c0d0041412402c103600043e10202c00707005031103072980d401d0100c41c3e04420050400d4148162240300c12510b150107982440b40000d01c1005c1d01030b800103000000c400d94034000c002c080045a90300c10103003043c0d915420701c91203100c0303645600c0b1000d4025440390b12482e1444016211001050706980b42c0c0c1441142c045c01000380c2034031046008001c1100500c0c0030f00c1c443e664120358001c0f42000040040d011840400c0180002e8407000840302501c00403200407003010754a098107681e41c200118010724809841b00f03a660154040c840f494075280c85032082d60f0421000603031760141319848410680c1d221528000b4400d1500003902c0c0600c0f050100c00308403c4030307400c182c51103609108500c00d9080303165607410f10540d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 202978947 1250 202977697 202977701
    0xe03040f140103061d01081e120d0204080d020a051005060306040b0405121305090921090310050a02030403090506031e060307050d03181d06060703090801050703090c0503030a0c0b040303 82
    0x2034110512514484020002149245d200901540a141c402c01c403038119082e10740803504883c4201c0d076004100543d25900c224065801c01800207001075024803010414100c1405000a41103030307070b8003e1400c802242441d624200038200c0d0540b0040c90001400b0681e200401c00b594000d130011581e018689985c584a46403548603a18100c0900c07000c1014200c1c00f03030010590701240d0040303942103038940b0b80540765901c954007030010144ad170540780b06182c0d141c10120041c1442580c010140e5488580c0c0300c80714402e440d0211506120315034004100420550044c0d030100180805680303550461030300c1005800f00c60280705601000c11200c6000440a50302000011302030400907150850700e060528004d01241c02180254405e2803544801007a039400c0c0060440341c2d800c0490240100b51a504203000c45a40882400c0d02000145080070502c410240034550040c450740d90005508185d43c03e040c0341000541d040320784260000c02640c501c01d40c0c8a1010003459422000b5007005444500e01540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 202980197 1250 202978947 202978949
    0x120507020a0906171e0c0d050319030209010318050606060f0408031b0d0f0c02060f070b011403010c03020c06010b090a080703031701080a030c08030a0609021803010e03040f14010306 80
    0x1e0030b5042200206a000c806018551000455801c49003010403e040300c041100a4034800d012585c8580c13141d0305035180101c056030b801d07401101034034680f4042d0203240c284040c00140c188040b9030001004641542d0502c00c00e6181001c2400da420f912015903030700ca4a4881c041c1c0710b02e21a1001181d8454459005011a0004c010b0581129580c04500d4040c1001c101042162883ca0060035241d207041402000a2401a00030750b035104c000e48201e5081003000e802c0070210803c4013406100f04400207141c402802e020f086803024188989403d141010309542501c0441d42c00c040c01480390020340100010080e040d5290200016114503440b80401d195000550010040e441a039070000306040c0c0083c41d90744804500d0103a1010350780c0b227003807140c0e4403041c103c0e004000502c103804110108440304003441e0810300041c00442ca407907980074180309982043c000783c6c0069241c2c102d800c0342450240715403010a040e00018600b0280b03424485260b100552080c403203d9004001111202da01c030b030340818 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 202981447 1250 202980197 202980209
    0xb090d030809031b013c1107051b0a052706190b030f010e0402010507030309080c24011d01060f02011103040b19020405060d090f0503040303020d080c07120507020a 72
    0x13a80f02034545038890b01034400300040f80c5646105904a01c2c8181c0304450704045040090140050381440304010002070080c2c8107030800104083c41850002403013400803144058400f101d60703c204020504020100ca01d83c2d100700e2144000100081c110380d4841114882e948140210078050342c0d4001c00306140080c2407594064602c0c04110218031b102c2c140018602400040c0c80900481c0c0e240c07015840e0741c0c1700550300a404203405000c4440024400d402100400f441000e00324144040d4801c45441e02e207004140c8443d01c413500b680703250040c0702e00c04018018580342c1c0d0701c0305650040c0c0075111400310040c05605c0802088081100c3c03031038000d4004940e903d0310100d10035500c0c40c00d410603071a41003090f00e219007525100d400c125094880c038020b680c15074a000f48907038034108072a02000010b240c2c0c0b44080322005182d06255002c00d005101402c0214005d0700035010880319090f00414406000300800201903050043c20003040844150003141141030030b01c0360740c983c030b50700000d04582d2041c0e0001d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 202982697 1250 202981447 202981477
    0x40803093912010e0d0201050c04030b01050607150e07060e10140c16171b15090a0306050f072d03090819020f07080a15050612010f090308010b090d03080903 69
    0x1018060000100d480c4005031713560003005103445501d0141424811444041c2510f03080a0040c401407500e0300c010f28046100380c1648041c51142d40d94407082e20400c5000303110355000f414081115640100383d401010714111402080000e510344c020b401001c014800c1d00b41707031201090030003014804020f030300d14600d0700380800103690303503903080c0b0155120307170400155014028403500304031352083c051880310b54480083c0350340300429428080c1c0c045600320524042c0e2003800d01e403000010075820312544e4040c5080c110100200d2600380c1000d8103208030340701c04821039801c00294410b41c0001d000b05210440c01c510740841c01030f103641840340f16401010040a403080c0756110000c0066000914800c82d403a201040c0d407280c603940c0d0b204646031503010390082c0072458180304410000a031a031189501c0300004044680d09000101c09508580e6003030f8052020039903a014880505030060b40300c0c0d004004440c002da14000e080c1e0041140c0c03118401b00182400350007008241c41c42010300640307074004411400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 202983947 1250 202982697 202982711
    0x418021e0d06090b0414060403090509070507020405012306070818060405040c09080f12030114011710240f031a06070521030108031204051504080309391201 69
    0x405480e1810b503000c0700e1b500307104400903815081c049140c074070503a0107407203084e142898001446040740303000308060b04000c410412040140d0381ca1080724081d159001e0882240020360003c90048a080c140b007512070030091003207000181c90300d8201c8101c00070540a2a1031181503d010528901036504142da0150800003040760300d561240c1d01000322100b01d4100e41e8412042094162035413400c0c0b0000ca103484003000180404016545800300955040c5880203a0b40c0d00d440c10110a00026590b4004c3c00e0a081e604002400010000c20043c0c041c2501c152001d0440d1740d80507000004910140044c181c44400e2812081c850409240c401034015010941e608090315000d9265501c0280742c0c0742011034104001003181d80c903030030703a4181c0f400d0000440c500b03c5c0090502c070402c00700403c11203d51007400c103105400403c2d400068000d0384128103940d00c9080401c092801c0c0000c4845032080904042c40c918004c418401c003041c440417000700038503035007030500b400b09804130310501500303000d9803d06e03113 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 202985197 1250 202983947 202983953
    0x4180503070605060f15070c0308030c0a0e1906030e010e0f0109140c01050403030815130209010e15090d06110c030301031406010302182806050418021e0d0609 70
    0x180781240c4140c00c1000030380e076503400f0400c00032405240240c018045501d020b10084c807210040100030f000e0815a084169243d072003888075442110100300600001c01c240890a400c406856100c1c80c0c11100c4071010315004010201801241c8150b070101a01d915600180c0780c03013075020382201c82e200300c1a80c00b03a100706035020380a44180b900803202d0000070502041c1905000c00d0929600034140d584500c0c05240d51802c42e8890f4004e00b00860440e410351200c0c04079a03942244038000c1c106000050303100c40e810b000251210803040d011a0146880c4001882e44001c508200d5049143c102e643c00d8410649080c120020621a070240c45105000100c1c500c0441000010354120383c45008280e9a0a580800503a102c0d075081c40029040200c0c04804144413100220450340080d100c15064001c3c00304425905012190f01e020400a546d5140c042c060380c1030034010400c841c03c584000394242941540422000c0300b504020445200c0080c00c0c050681e503616810390161a080388040c400310829007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 202986447 1250 202985197 202985203
    0xa0e07030b06011d18060a0905071e0314011a07020402031014060415030f0e0d11010b010f021c17040b01060306061b030c03051e0415050f0d0902041805 67
    0x582c01502007012001403200140c2258401d03110540043d1045c03603214074101035822100409460310f03a02c5840c80c1c01c040740c0400759204491003030002d941c421480340c041c01c0d1100e00110306d20071a00c04041c01c0c001060a80c024413007510303046410210780320400404240c00c0080038022040d000b90b0281c000800c1c0035400303031011652001c0d10250302c08160b82c81101d5040190f584243c0c0304a0300741050908404000318084c0c0c0c0400e0440b08886404902d40e0054450f6908151802c611000419000d070030b807103103c403000d1080c0c140e03602c5c3c282005e5866005140d0040e58500c0920b0881d284030601c103042001c5d00d03104072141101c0705074800558050741498607010074640800d01071600040d10b8618001240351240e911006411100c0c0d041d0b58911483e910112440c0800790340030707400d0160420000d9101c02e20340242c20141c45070340c2140f5481d01e04000086180152001080081001c04e000c0320720b10504c298202c030040d40030300d00002042c013158800b10717003e007100c6c1c0701c130b07000c0c0742c54190301c0f8000c3c0107001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 202987697 1250 202986447 202986451
    0x24050c0106082107030906030e01020904020a03091104050c1225020d020c030304030b040615051005040609150206160207080a03030219090e06130f02030405070305100e030906030a0e07030b 83
    0x980d580c50b0383c01070b504640d4032244c000e181004d0001b90303c200c410030843c1e000360304c6014941e440350009450f01200c4000304003680e1000c00c09a000a0340c400a82d407d00c01014400d80390850222414045814540e800d07401c24020b1511405800d03a110b4040b50205002e0702d8000d42078100c2d82c2320f0b60182807800c28065110940c48040d0b002600901e03405c8000d614000c0101d030b003540e034450f42060300ca4031180c43d0a0000c010a0a84a00b11410304030045595902c0651942100700c980d40c8448d600da080034001003140040c0e50003694900d018030003207501c444c1c011030100d51203441c6c21074000c486403000304205c3c5044107a601401e80d502a001c000000e265140c1c005040d50b81605034030340d9400c0b5401070100e90100c200d218460203ca200004145a850410300c460300070303141c0d603c2c080b440000301c840c08001c0303902c2920200c4981e80101e800b0820443d09124441d22410400c0c0100301564034964103648030f22806031224480c500c008005460100240d02086180200c24100d558441c0c60f440d010401d42e0302 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 202988947 1250 202987697 202987723
    0xe060c0d170a0c0804110301090b040c090c030908030601081f030f0309060e010c08033612030c0405011b050d030608060112030e09041a0f010504050606030124050c010608 75
    0x1d4000100400994042c8072030760401c07540c941e0015525511040600f01c414a0243d90654840940ba030105540310742007409140180e040c440407515212002d0111a550044401810b0420b50003c003c101c4050039a40d221600b82005580360395070080100d03040c03e018103401406d8011802c0802842032003040c02c00564802d41714003600d0382e251042564104800c1128900003082400d1510009041c1c0340a56000009440300314059009107541445864030540340d03100c1001c40e24044036540d4400c100c4914035241c4611700a24604056101807030901c2180949410b00c0314a4040355000031842d50072004c1280c1080c10f48003034800591008001d8110ae11a0b4115445400b0003c61201c4d0541044a0080e5140d126600c428010350148142000e0041099030800c000644200c01c174003050440520480c4080211072480d030428041108a0b1009800d042c0204400d10041c007a401566142514420fa206080d4014020302e0078111054070803240c802c46d955080407400142c0307210019081d030008503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 202990197 1250 202988947 202988987
    0x50a0605090408190504080f15010e010515130b0a0f1e12050a021e0418091104050a0908040815010815180c0301110702010e040501030809010e060c0d 66
    0xe40c82080140c50481034801801a6008002d550b08090a071542c240b4007800600f03203141000c0d030704d1460600f007402030080d4181a80001c0702d080591401c2c0400d5074050004803d04200340e504000c04140c8404000381446d0b100c1d00c0c006032210700c00e80007130b101a00074228111425910a00e1210051454007121140804250f07200343d601d040000100707140ca83c0c80d50590f512000075404040d071002070f0002620069002d6401c200c0d1043d03a03481420803686410850f040b02d91344914204804480ca400c0e00008041180391002002c00100003c240010750b0300101c5001c40c1c141c486400840c0141900d9400410740100000c0c001100e03500881c8002d52182c6c0e28480780d01c0307030380c0c0c80605540f205030341c0e0300a00c0c0a18001e00016561283c40582520448210003120942045140030a086030480c2e01207003048580030603070008540e0f01400c3c000a80ca02907071300b40625451580e8031445801070680690502c2403034005000c5070307103684080e42c415491400031103a5412032001c014000c402501c030100c1c0e60803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 202991447 1250 202990197 202990199
    0x406090231090204090506040b040b01080c06040e09012d0e010e03070b04030c140105060f010c03020a03085b0308030627010512010606020c060d0603050a0303050a06 73
    0x740e0051521001c11000381c580038024056041d00600820303a400741268019130f9614180041001003117201d01c6a40b0400042d542c50920b0b0800700e110f800140d101174043d9024140040541d10f551080d1000c403042c1940603e107a845195102d8003501a40c0e0b0444050309031800d4a401d0703504015000c03c0c85140c0807800f0802e01d07100245442c00d80d2140d44850780e25a00410000c0000798034050301d02e03131103030092407c0207801d1816507d141c03501d5201c50011040369120001d01c4100d1404940204007003100342040c42034407030340d55800794a03580150740150901410341d00158440d000b02815800020701c3c50000c42e0440091f40d00f4404610340718054401241c50744000200541421074001600d8a1903c4011805480c4d41e940c1e01e0941d0004200f5a04a40d040706419007030b02501d000002c0d00300102c4000300042d0f05220a1000e0044009840261030b030600d2020880a500480c0b400c81c0d0010542d1140d65854228140720301910195100070580d1040d49140d20905603d40d101e01c0c082c00031403205103d0300d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 202992697 1250 202991447 202991479
    0x316050a0b0a08011a070533041a07140c06090105010506040f0e0915070c02030d02010c1b020409020a06120b100f050309070f060c15020301080309060a1704060902 72
    0x241c0607680582010610f40401403005050f406800305000c84203040d5a0300d001c0166a660741071906068410ba00410ba4501103c000561a42c1c000b04d4465151074071006881e10f81ca6007040b2400d4001c007480303170700b044a01217511144502c07440a0707080e20741d4000c0c0740d1b1803030700105c00390b5614412038a81071103505c0c1c50004100c503e040070072070f01120701c045c40d008800350a100000c481403034050310400c814400c40018160303015030501c50511070b0711203441d51816141c02c2c0c0103250a01342141d40040443e49810615880300f50841c00010210043c0d001100340204640301007402003410360400382d84812000c02c00601d10b648004c240078031458070b00041c04902600c0090004401c41c01e1101000700b2608039081c0c404034801c401460340140b1480485004907a156161300b0b40d48816042072000078a56030b00c000500021a0104d02038608685086145602d0320205548078007034508940d1056000251415000b4410646d51001480d494040c00039801c0c82d1905000810344590304034050000c0d00801c40007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 202993947 1250 202992697 202992719
    0xc03070c080138090a0e060a050702032d0d0204050310090f120e0a030605070323010e040f05060a09060e0a15020d02070609050d02160305030f0708090316050a 70
    0x1c0940e86140b91071a0000c8200c1c200d40843c01607540e1410600300301c05204243e48082c461409100300f0729001891014486009041a00c010f02450005040c00b050044407580042210b1444001d020845981c2d0031503a004015a010111703100150030021070724030060b4040d54000c104440045040f5000803900094490980c4c1c540d810141100c06046a0314001c030b2019680050042e00c1807504803a140b441030002014135045030400da035000e0303035803007000303011601403162886401100c0c140c02c41c000080100f01901071790500400c3c403030030410070100e820080680c3c4045241ca600105440080c5083d407441c4004002d200030698006090180e00385980801244840e503ca1b0080081e41d03480c2001544007020350300c40403100304029802c10003200484c80501c210310740c40e0302c01c0000d44020040c0f100024030b0b214119181241d41403034408100700051001085540c030151780030000d901c0d0a6642410364441c0034034225a03406015032a00c090000344104d07000401e8272011644e2003400d0f0344842280354 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 202995197 1250 202993947 202993961
    0x206070f051206060405060c0f16120f05010902121f09120e06041a1c050c1206010216030b06091005030c010c060906020703090806010b09010c03080612030c03070c0801 74
    0x1c01c804008091140e090605010740c002c90140940e0b140c075a541c004a00c0d140e00041001285400501440351000018000d0489210210049040c603900f082c0c6090000625050002d114074491000c1508014003034104450030740c0c0080000220f013a140b44560785a061658200c004001d04040310914030610341303d2028003541144c03610720524000a0103640d407003001a6500e5014a0a00c0001568200441001855000940d0060700e0b0121181300c2180000c0e01d8860300302450402c002c20141220380b40507124615440c0b032101178140c84050050b810a51001030382c1c007690000e202e020082c4403072601110302a940545118001e5074900130321b501c108c280c80c01510f0345a00a9206040b066104100003003e45005410001d0301104550310325041b64415003040780403e4210310100300120781130201301d0040140002c181d1070901d03110002800d21203900c2c002001e1004210104203281c540200304620360701a0409c507542c03120b68003006a56074000d40c10407100301c5001140800c1542c41801121 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 202996447 1250 202995197 202995227
    0xf110712033305150904050a0908090d0303021903050405060601030e06070e030106090e06010f060503040c0b0c030d09030315090608070e0c0c0601150e062d0d0f050106020607 77
    0x4507906507030b600d80319988110342e10518a0245403070808140e80d525200a0640615020001c030381e075030380c80e00511090741c400408201c801850701c656100447c501804440403010116108180780e401807034150000e002c0d600b0404d04940d40701c084165030700d405070b00140c0107500807811103400f0390f28140118160340c000c190000e40f1f90803483c04a48203034055a03030444503200050021035aa0345581c0c21703004850044201050030b5000d4401003041d010840f00010103001b10349055880e618250b103480001d541c0b5407003001c1d01d00d140040e90800e13404050055840034080000140411201420006c1c0038254688403200700c41e15494000803014480d00c101c01c2114940030280003440d1a021000c180400c0050091440250410038030355406000e102190107021074990700c1d9a15009900020102c3c00319919043c0200f030200500750141c5c2c440e482c141d03020750143c0c200c251080c52541e0008280d0141540303c07110281801c40040b1070748a5500040d0580b500e80d401c071070f0a40c0e101a01151101e0001d4803078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 202997697 1250 202996447 202996481
    0x1f06030309090b0d030509010c0605042306040314030a090b10031104020405031504030302071a0a110301060c0f11100e0306130213051e0a020a1202030c1204060f11071203 75
    0x244c00064007a00140a0791401414000380041407500c4850a862003280c2c12141e00200c03642e05146590102a03184600c882070006096924095034081e059115111641c00d032100f002c400114001e113981c03c0038809079800b18424031035042591940192402034001100d484180c81801c1c0700d0303420580b0a440c22144003d0042181a801403c0d0142000003c0c209508068080004d2800700d124132003010940b000c00b81c504240c80c0340c1428800100d5860303a8001ca01590200010048030350b1240003044401d80080340c00c0c1140da5030303180011012141c010303266040681d0f05922101032f07820250050280740e040e07043e145950344000308000c40366000a0000e6100300a40c035500c48200b955400700b40c2c800308502c1040311044110f14080a03030035080710001d160301e4001541850166010450b1039041c10b84045c01c1d421420401c1d603804060060071800807010300c00b000020203014203a0021444003c503810304100f8122500c0c01c3d4005540292400c2d02e090307124001240074503103c5c0c0701b0300c16103612000300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 202998947 1250 202997697 202997719
    0x30c0d05090a030503070b010305011802010e1002010e0d0906030b0a032303090a090f0f0605150d0209041805160e01030b040305090915010e0316171f06030309090b 72
    0x3924140c029405907a0040710780c41d00440020340420040410750300904030850950716600e412425500640a15240c2d115105400c01c0140d030044402003500341d0840e00c0403028612150120b0040c03170040c0c040c100511403442c00f1588160030800b000c041d180595030501822034108148012003005100082124502021100700010500032401146030b00c0c2c02542d02d001c80350800900c451180b5000460b0711582c0d0320b00d07018103104500c1041840b41d190502030168615103000030b5210701c80d6000034820036400050820b050500c5504030385080c1e0004004020b03203010f400090a5840c0360403812200340c441c11100f81c2c450700d0f40a9040342182c0255002502c40c2e03096540310150311303002400840a0000501c0401517075560080c4091040720b9248409091010345c1000511081c00090f00724040e40100780c80803c0040d00400c21030603980005001828072440c4000185081001c010a2080305a040310010710f51045401c00d40841e402941c0380b50580f40c846400da02100c0740a40215407226034454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 203000197 1250 202998947 202998973
    0x40809040c14040605030a050a1e0203100e0f100608010b0306060d1b031b0e011d01020c1c03081803070308040602090604090e07150210090f020d12030e030c 69
    0x701c48405a12440d15050321103155001c620b85411a80004001c9500401041400401c0d03204260344481545030500c0342c0882c45c1a1050000c940d80114001350ba000400035144242d2221100020010400c0f20a001d103019600002d510506913010403e1042e441c40002d0b801d4450541581070341c820020381807031030319020100400796110f0003030f0f40300310343d00c4011a02592040e6419804003080356200400c03d2406214902090405009800103110f007804101d003440e42c0c0131840c90310500c0c5960304459200074070300c0140d1030726030703804005544a455852450000c840550070b00b00864803e84603600f644d160094400b41041c030518083d0032545c824400031001ca80306416254000b40194001881c121a05021400e00c0d0700a03000100c0703441c0c440c406024840c40c02c224400c006d048002d45000d81420b4070000940310007020155000b00c989480211040c40040328162503ea940200404403c584c1440c0820035210001d0901e400320b45010034100340c2100c04022a45d00004d100050401141070349 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 203001447 1250 203000197 203000201
    0xc0301060f08040512030a090311010c0e042403050a38041b08070302031b09060d1403031e0f01050108070f030e0a0602120106090305030409020d18030801050a050102030304080904 79
    0x1032042c0c44c00d10403c04005426200c2000441c00366170168404541c0c0c034940d040143c0540f400300156041c80c1e00d0a01488880341c0d015000721030301b02c4115000f2a0a007698001919941000040e90081c2151010008200600000e00f00c401d180300d006400c665031100090384802d1036007030307105111411202c81016042007414120607401031149510006801c43c40d84100c182d40c05c1904440031701d1b0b00840045c0f0039480c08109154800c40c1803480314164010000101c0c8015201130080b83c082c48115502c0420480c40143c980c04050101080b0380e1030349042c075081c0c0781c108480c400364040040c103400800ca44070074084110b4182e50068490200359103170380c4001c82d4221a00782c1c1802c10155181d49034451071005200101c0b600e40030328000360300d403914080249044035040e0b100074140091014100001080031069a0032130f03050246c0140c60703100e441c8101000c0d08000c5d8114228000c00c0204004054103c810941690000c1d6003005070151502c006907074910040c0e401400c030000512000401745815 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 203002697 1250 203001447 203001451
    0xa260f0a02160b0709081b0402090307080d0e09010512120c150c0301060e0324060f1c061b050409091407030b0108060601030c0f270608040204050c0301060f08 70
    0x34200061900344858422440054082001c540320140c1005000040c0e51101c1244d0181620b20b01401d0304200d402240e04103400e0749207802d401960003040303094065609004c604014901c0c00241d50401c408040c00603d105080d100e414407440144002160b5070030000f9419120a07801001001a019000d8425900f908003100c0d124940c442da8980c00f0020900300302e094000e1050300344440d01c9505100014101d28001d4204074001d50242c01c810003101001210303140307483c11050b510022622218003040c0c200312280c0d40310342c001081d1059404140c1c50f81502168140c0900010800c0c681c11095a81689600520110014105101c20300c41064168801c4208911620f010f040d10548150b071542005055030023955480074800042020782c0701400015030080c400d01e0704110407070341658090318480900b0b6602041084640c52500f8051910031400c030140034110500710220340d100002410322004490480c0980d08280100f4214860b0105a9058608a450701415101c998400b00c40150f80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 203003947 1250 203002697 203002711
    0x30315030f0f02130c0305040203070e0c0f030910020a0e0307050915060c032803050601080115030b01020c0a0909060b0904050316030507020402070c260712020d05030a02030a260f 79
    0x240194828403003502d8400c852100181c0e480c04a0107142c23a0040504005055010000384840081040001c410f0308040300d40103a403c0b0380300c41d1a9120041010720300801d0059021280740b000801000e807a802120120700b004044040b40c1c600358603882840944601618412808550b5030505901c0385444030107003545200302e0048a040c00d94445640340c080c02ea041c0c40c2d4900001c403010031410305506000310741d80401b003030a00d01e40c035525008044e194031b8104c0c2c4c0074008142d40e644421885a2092140c0b14107900020030000c00d40391101c1d1000e004000400046862900d0402001c0c1c0d1400d160345103030720961b0801c0103541060540042c0807507110110351b00f202088000c02502c1c00503074903803010300002e5004007410002103060503c0c0d04041202c164241541540b2003800b00360300c2900007807107001c0c0da01c0c000c01c21003034240c00c2c03010840200f6800b00003019800042a6000c000354000003400c1c2500c180d984d8801e0400071500c0955107142d401c3c0c1200c0c0002c01e8030002404030114a5132280c1c1141c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 203005197 1250 203003947 203003959
    0x7020102030c010507170a1a04020702030a0b0907060f140a030509160305011a120c0f010c02130b0406060c17070305122701060503060112140609030304030315030f0f02 74
    0xc40b600c0c0003801c4540444040010910780160905c207003640071021548020b5101c1d007003214180e6500f0240c406651000c16038030458000070401c00310f450500016640540c44414000d160810100e043d440e15070720f000d854001020110ba12961921980324142c410300101502031800500b0a012030280000521340a594451071400c1c4040744803d0700304100071030140c2e00012301c145406903000c180302002007009109016602103042004c0c00480e01644101084445200c1c4007054401601c01d9018908081d43c4800002d00040300c403c520380081440b15011903042001c19118042074454038203eaa000e040c5420150b03000801d649404010065030b8001d083c1541091800c5000c1e540e100800c0326110300c2c40c10000c0020280c0e04c0f05081a59100994000a109041c00c0c0700120b0f40e84e0380140300e941c000210070520b000912506650240b8005074135000d40d040e40c82c00c510401e50b01d500c142c1e000c40c0040c2c58407209407400110402090b060302e40c45007003000341d40e1581e1604c03a00e0b402c0710300c01603034001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 203006447 1250 203005197 203005207
    0x207080f010204051801180b010908100b030d05070305030a0c2a15020c0c15090301020c07080c010f08010501031d010e010609050c0304030816051611041b080c0702010203 75
    0x842000301065804100c030001da911428003080c8403c0944203480000c00304034560051007240400e4640c085814104080000e40005c0c4030012210305101e50b000b49114003480911503c0007103160000c4038000b50640480300103070752000c002c4442d07128940000c1c00003602440410f40704145508600000803da1070a04120000c41c40703001c03219010340180c40101d01d140c81041040000c825410401004a4401103081040079803149850f20b8808011520038100c002e00c0811240310082030b1130090310058002c644546040350015a41c20031070251201d140326044c2a210f4561181c004400301e051079540b9059685d10b004010360150541d81c1440444c42040c00003045484401d10410030100300580002c40d09a01c4e048102d4111000500718000700700e0100100404030f900700020b160044403401503600c1207482d00302c046805008108105040001402e0060180800b4100a01214008490801c0940c1c42901c82c42e51394a40304107090007140e01400000d00503101040601003107801030041d24640 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 203007697 1250 203006447 203006459
    0x80a1805060313110a0501050f130e0414101a1509030115060e03031602190b03101a1e0903010e010f090c0501050301060210050a09050d1e0309080306060a0207 70
    0xe800c120f8620201c0c0802840040900000c92003e19955901361002c0d0582420301e0002000c80c403c03011182c2d01204005040c2d00c0c03608825502c40001c0c840a4480c81c1181014a4130181103a074040041043e4490b802000c80d04050a100d046490b41c4c503001c00101414a600c2408001004040e0440205501740000a8541c90a020724800e9012120300c01006d01d04112001e4440c050444502d03001e988288222400248503071007407500641c04a600310b484004d04110400f40140c5a00b2080c405100482400b0001080d40e00072002e4800b0102984800f12a20513080e4043c014400301540101c807100c40e08504841405c011710315500b0180000c1031030010804241d003561500c9511140a41d03a030500c032014098110701c0b81c4040d00003441c202d8519458050025610901e8a00583c0302a590f0710110f21107420a9000703441d01039008069540303a03d08000060880040e0b0056041202c19050200c8404c0e846485181c0042e5803200d8450300f036446103c04c0c480d840c0c11050b244401d510440c4404959 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 203008947 1250 203007697 203007709
    0xe0a030c02120d0206040809031e01022515090203240105090108010e0303010b0c070f0306051e060d0f08040e182404120905060f0408060f04080a1805 66
    0x5014065100c0a605400030310511060100c9080b50841d641c10911500304003039404540c00e50401d401481c0385e5115282000003074108000e040d5940f00f880c104207a50240701c40c040d00642000130040c0b0300c85002e4410407007544803181c0840c000421104611981e220701a1490303100300000c034005012100c9076501ca031803500680c0480904403c514209000407c100d20b444501d143c050325024000340b16945034080899585e004c18000c2c4a040d030030100d10080001c10400c0020002d007007481c0345000721a901e050810081100b591200d00d010080503040d1540d1a02407552409280050a240e0355884640c032070f003980200b0014211030180c07040200068519020030514001e84100c0d2120840340000c2d1041840c014003100b103055418610fa410840d130440c2050140d40c06508540d00034283c40c608082150245a250000d5a212070003044000c0c1c4000302c01c024005407241c20088403c9910781d90302210b004001181c1c001c1c0b20034020490b00c00458031440040492043e0b04414a10103134440340003443c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 203010197 1250 203008947 203008963
    0x20d15060b0f0702030105010803070c061b020405010b040602060610050a0e06090618010f111b0409050d030c181203030e160308180d12081e0405010c08280f0e 70
    0x1c0003030400f00b60741007585020b10031325006000240095242a55a13555250f90034428400c000074004203450300c075000707070300306118604159005008000941c0c603225041250b821500a010040c482d80d40024042d0900241881780003046842e21400c002107014101d441000022400750041d400f44000c03c5642c0315840505204100c40c1c420150070000000010400703140700c0080400c21024540c0d9900140010400c0c58103151020200d103203030038440000c1000741418240051151080b204a0012030f603060f880070b080544503583c2c0e03030364211511034094894507040c0540304025182c9480708000038001c1e03000c42c042c04454800c1d00c40007660f0560340e0401c0034140d40140c2d1100c1001500b404890364148240c014000201d814912180c91038554041d50311602c5d09000034403681601264200b031000e09444e400c42c10311115620f6601d0640381060107070445484030408110130001082400038548603042c00101c0703084000554144202046016054034600302d11040d40c0c84031082024101441210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 203011447 1250 203010197 203010217
    0x703090501060f061407121d280602030403111003060305030f0307201c0e030a030908060a02090303220902040b0909090309210708070816050409020d15060b 69
    0x421214501345001d801003407411003403203a40340304014a90000d4840c0035004200c0c0400d14204030064442c0d08014070802d0350281d000ea0000c0035802407102014251100300111002009201c00555261400d998a01550100518184402d401d5040a04118894441803541881c010031400c1c0d80c0c0d203130035045604c81a000d640d15a000006c200c142c0e81c0091500322180882041c000d164040d081c28242c4a11120100b02880018800141130303061140c0100310809030020103888a4040900d009000e44026200b0304045004d01c00004e00d82e00c10500c281d80300140080c018601c1c10050101079480c1100c680759050300d0944800e404102c41d40148058005401c04105d56943c965a080401803030300340050070214550701c10016009161640080300300031145020340805989204038506040242d2a08032000d41d1040078000106050001880f2001d0200309400400054507807090200380c8902c0c1e04d0185d0810a05138101300000c0f081d915280d00181e04c0d920001d9941d0f152109c01e00e0b182d00148440d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 203012697 1250 203011447 203011469
    0x90307120216050a05062502040204230d0c0e04050312180f01050910110d1a010807030b0306040201050d02120a150501020a0c0312020f0105070503240109030803070309050106 77
    0x192248040c40b81d018090841c0c0c2004a6407404c00041c1461080c1800d07030781a1120661404141c0c000000780207040c0d80e0040040d516240c03550b11181100e0b42d480070529185101020640950a01c0040300e1217850f000420990780304c0c2000314034540a10054404c031800e2000300310501c40d80c0411800613004400c1c103100c860500394828222460405007500c2860281d251009000194800040e081b481c8449242c2c081941c07040042800c000e400341082c1c0510b21030500f405062010142c04c2c0c40035085000340c0b24583c02e515040400c070119a40c0181c100c4e0180d02180126003d580a0340103095000e204410152900c560000c140740504410344502d0704041c0c40300340e03500114010380396540203000d00b840200a089040d48ae8140800c0c0540b2016164202403107600000703510078040e2031820086207000340b1050402d014010a254811600d2215882c035061445401c80c400c02c00d54082d00e0030507500c44050300d040d62104040342e0b00c0600300d202495640c0e022140001c800303005a6000b003010000c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 203013947 1250 203012697 203012713
    0x80c0105100b0309060a110f030f060411070818060c010903020c01030c030b0102100b01050906040f0302090a1109040b030c15120a0507050d050601051e03060a0501110a02090903071202 81
    0x3100140c10789600080308200c01481000200140000c56561001c451940441c58445402c0b00041900c0307040540d10751000f0000800200d1480c6005007070084030159810050078240302800501c03801000303002010a2410880303109000c03201e44800e1090500108450325148401d600c45085903180c1303070210056086401e0012403907030140305100c910301503400c0500c48c4440c84030000791210341a152280382666201c0c141d4115911540640d0070140000c0d10080d65561074070010081c80d017951104a10840705c103800550140601e000c2ca0b20408209032100c0d090880b45410000500706c60107503143c051103600b804c500d090740c0d402c1d43d0382e80748541c888240d0341d00c10a511580f603420000401e004180b5003807800344000c45920000700d4444202c070b480300288503122580103d40e0303807060b9046507074510f1444416000c00140c05004601805c421100d2030702e000c0c0d542e00192030b0172070341c3c591124494101520000160034007145165101d403040702581c0c541011543c481302248a0940468016801005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 203015197 1250 203013947 203013961
    0x90b07061d0a0b1609030b0c1306050d06150e060705101107030306050d020312030a0e030310180b1c060219090501020706021c030209030c0411090103150e180307080c0105 75
    0x4a5070826800113099071152201c18019041d00f41760710004105c0100c0c01d0002c0c58a00c1602e0590342105e580741e4207a03803060b5980c0c90040450300030002e8461203034580880021440c902d01200000600300341c5485880c481031100704241030700840c1c010b5035180500000354000450500c1451916104440015107940c0e060a0040c22075140c0e40002d400f6035108610100540e40000c9c281c007001c50a0300446650f642c5001c4100041d00042c8040b0010f4840802400000c92061408409981c844400c0d0501440e2008080055034990441b464000100103104c0d603c007880741c000491440e018580161403e18220f40e220307540886e501d03034100004c202400c140215a03050000000811a0348014800b021000c040024245040c680e010249940011940510344051000401c0404000c0c0f04128800d24171b8000f60044d80f1240855001034a01051b0800402420780d5001c01d40d813041c2c3c18401c00f65074030400000341c0300600442ca0150b210604c500000240810000e00ba010200400404c560401c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 203016447 1250 203015197 203015213
    0x806070e0901030b0a020313050a0f021302090906060a030e070e0612071805041a0f0106030522080310030803100807090b0105090103050601090b0403060e0c0d03090b07061d0a 77
    0x5058580700e12046401000890f18030403420b50010202c00d00144c1e282c98041c05d900d803180c03602034001c000c1d0007104600400e1202c520311400b040d500035074292004103001480c039004c81c42207092039503014800901246003400e1010141178038444508000682400782d42d401481c05403d81c1c0543d1148182d98200001c90410513020048001090000d10080d4103140f40281c0e2403000c1c0b2a07003204c00746d440c40000c0c02c0c010108a580741039109001074101c04c5c2040c46016104100034040c80000c24140f001042c80e10000869078030310000c485140308280380003503445800c035510281c22994040c1c200b2802202107468500250701407203800c14059401417502030a1410a00564041c003030f520700d000d220340010390b0010102c444900007444c0000d0165110740040c1d40d0940503401c01031628001140200c00c1160940c8040001014441141c43c07685e80e001c20003134070030f605040c0100050501601040074800810107048a14455000854401c02c07188040b030308182d440117103005a038411400030052061352 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 203017697 1250 203016447 203016467
    0x30c0115030c0803030412180302091303020115050d0611121e0c0909061215070c03030b090106051218030d060617090706050705100609060501020f0a39080607 70
    0xf00003560940c0b50a454030546820420000024013801204100414003d010090040d5500400c60403076030a201d0140c03500710002c2001100590310b40b002480e8001c10401c00c21080721001448180c010200ea0341d55030103488042c43c2d800311508140310f0b20400740d58a110040c8942e6000704121441030102034001c0080c400a082c0750b00c01740f03003007001c03091944540603102d40c00b900039280b2242c07101001001d6807a02411030324a01d882c21900003408681d540c0544030070503183c0030b41d40070b10490a5010030055016070a12814000c603a04201e229080101030404584c00605403140301390320041c140380507003035607c400d0384100740f01d50350b590500000e84c010b02c1e4903006c00e0000396803924a10b48410025603070a224020202808404540c02040240801c81d08810885d4400140002a50b5246210180c40e803070098601601903c03a10701e10020b030024080310b29940000402a462200200713025203003050040030404d0b807041c0400510748108170128040100030a0004042900c0c5c0040010510303858 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 203018947 1250 203017697 203017709
    0x71203120606020304050f1215091501050609190b071506292d0909010605070b0109090804050306070f0f03060506041a07020909070513090308150102030c0115030c 72
    0x10309072061040e9030740002603900365541945c0342c03003403015810001654074002a0820000e0320428001810040c41007241501030181c0d4400c541c007850b20f9074003404540d01c09000c1c05030080320a000042c241d02e803070340b64410a500030510400c02d003a110740700640c0c598086101640c003c000d91706081c0312990b907440350900428400d10b4004952104082001c9100e01400718403c812101140d403500440f4009040d06420644050303003401d45803201d0320390303040d40c1000b0070700c2d031042c40320303100005610f07014804841c17881d43e111140480b113a00300040b0390b0041c903a100094501c5075042c1310100e460745040240601800c842e40f15103440c500d20801c000d226040307002d810801c05060031800c00480c0c440d2002c1e241618010150300700380e400231841400d0a4054408042c1d841100c6009100d10b15001040c04001d80d1410743d0f105181e4103440d500002501d00150000b0b00103803880001070f81c6010b1104403080c8540051050741c0c9070800c0c0d4000d103401c2d0384500c0b2000340910708200c801c0003006110a83c0c8001402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 203020197 1250 203018947 203018951
    0x50103060305191506090603060605090105210a080703021b03120a140906120a060608040c141810170a112731020a06030f0e07120312 59
    0x105542d900d50301c40c000145410710401071001e2803010031040c28030760001c4025030381040101c4d0390384030302d944007406c0c442c44292801407070440040340500382030180741c1c182d41010304030012002a2807039032000744040b004408001c0c064038106d50300040702440103001c440c0c00b070b80c0102901c00c61905a901ea440c01c050406100358810400302c008201c1880559107c0b07070081c00c107030002c00c0741c2c510410072500c05e01141552003240028507000141c84411076500030415500304100e9251a00019503030800c06a4010b894100c2c1081d04100000f0212103450914074054501c0c6410390420002c0320390a0b405031080600e00300e08000034001c60034041d4100030054160001441c142140c1c0e244e00c1800302e084101c0b02e001e00d600d81d00417411000f801000c40d80bc0343c0c030711020b4030b05480d144030306039003417850a4030996010024400c0c4881c0e141a82c1c0c0500d0740f1980091608001900c2c10b102500140802226020500d44810301d50040841c140031500013440c0309909149049c1280c9401040201c001e04140b496034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 203021447 1250 203020197 203020199
    0x80904051312051b03041d0a0b0a15030b09010803030a18020f01031503080f120601020109020f04050a090501150503010e0613030c060e031c0b0301020918040804051c030905010306 79
    0x1600c51402e04612a4103810070f0755071303649408608190980c04d00e07040d2459210009000030320707114000d2400381c0714545020f010500d40b1025000c0b13080d50300d52800d10381e100003981c2c01406411000b4040294043c0c25003800074044400c0004200165000d034000d25607500084104603800240c1e002d181c50107810302d49403070741c031000b507034001055440c80704109410150741c2d11003d00d0710040072003104060f54000290303070344940c401d00745411164441e031040d601c1607544001007180f03540140904039036245d004058000c0f0340f051314184001040010480c026031520750340750308007081003807040c0b03101c948a1401d5000c0300d42c200002d01d07003540d41c1c10b544504c031f55100e00c0401c50721141d08251140003d9140c41d09600c46603003420024007424080308903000714000054601c4480780205075102404170110001d0102198507001c05080340a260020f6410540501c50810301d000d65180301607100e03102d2000241003946403404201c0b00808000782e10000401940541e0902d80c02c507401200415003403805200741 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 203022697 1250 203021447 203021453
    0x12010c03151a03070c1a06010207061b060c031104090506030601050f0a060e030a0b0a0506030d1e08040515070f030614010507080918090304031a0c0915040b03040809040513 76
    0xb48a404482c84200800840400d001605c00c1825080707054201020070143c8075510554000706038269842d0f40580314024000407100c0c0200e02d070001076408c04120311a4a244c5803114030151501da003501c410503a407214400c1c0084502d802a20103003244050000713680c50301c00b00381890840e060700a80d11a80f4416980c020565451a908098400c0c500e0420703103805d4003d01091600b029508000c00c0b40e001c3d02d08001c07150341c86911452184104a0440b29082050041580c441c424101041d402d03055819600c0c41e005c0c0904c01058202d480f03441211140b540080c21136600e02400c4d2203001c0010140b030451050268580a00c10140c40e40200300d8210a0004001030000d00c50580300403d00ca60120b08010b5680d10080c0030703840001c05030b0820f40c0d6840c2a8541c3c075101e80c00703030008403000004070700f00b2084095170f080300c43d20520110090514100050003001400c503805089920346032020031000c079030045001c0245004601c5110f009458050100800060f1100280400f1300340440305240804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 203023947 1250 203022697 203022719
    0x321010e09030a050703020709060330020c10050c060702030c280b070e0907020c03010e031e070203100f09030e010c0c061407060e100b01020d0503040b100512010c0315 74
    0x500071144c2409a500c200300d00e400d80c240342d00c65100012041c41c0071800000d10891122007105e4000c550146c294102c0105a4400503800c910f111400692000e000e00100d82480c0d144c10b00d11050505003e0708012405415614258040740e00000581001c12101080341b0100441720016403402c1240c0c0b142d401109092407108580080505201c0350300010428490050b40d078240c0b0321101070126121454424800f0390340e01b001c0c80500307019600e003c6070f10850300d81c0442a5800340a0324038088050f401414451074082d045000282d80c035004800c0f00d0b080810452080c000306880c0800c004c55410028240908142c140c20ba2003030500500c164036000085180010000340d17031260078000c00170341c80701c1e4081c5002d00840030000e0820380703404d04000c0340d0710700064031244032040e4000601080007503000498950403480e200202056080c40480c00244c0c0105c6031550101d81180c0d48800c6507a64000241c1112412001d84056599040040c0340c5592502070f2176085089054004200ca01d400d03940f6003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 203025197 1250 203023947 203023957
    0x303020d050a0306080114041514040f081b0106030c0504021c150504060b120c0a02060403111515100203030108100213050306070915020606100804140321010e0903 72
    0x100540000d07402c5030280a9807040015124800080240084603110490242030503541a40c80740300b030a05e96140c0411600451802c0b6000f001013140039103865440d00d843c901c10100c215040340d814000751700c0003403010345103c01c00c405200012a246246041013295181182c00c2140100c1c0100715048107029a101d602d803240246420016010100315410810703030501d9000141e12504010002501c00102406400e54003102207960503203403190340c826003c038401d1901c1700000d40c10020004010900460380c446441800006a42030b40b2890140710480e510100c90303001014548100078502d500b00010b800d4150803032800150300e9541442c1c6225a28000400028030080e000501a42c0099245152030005c0c90041c1c21201a4100104c0103056070701c3c10b0041d051102020390004840500c002219405104042c1125140f2424148119480d0600038000c0d94034030014850900440410001403060303015214aa0f03d8220340386440342d2440c1c0d01a401900310702900c80902815000c0841214 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 203026447 1250 203025197 203025223
    0x5030d0b0306270a0c1d0c09030d080a0905060103060c020d0908071e0b0d0222030b0606090303130602010e1009083a020910080403080c0f07020d060e1204030302 71
    0xb020b80d444a5880f0307180c124004002400c0215031180020400c21140d00180d980400c1030450100e80c0c0c810403043c40318044e9003400750303244e48089458400c60340034900c0c40313420005411020404120301c0d22050714000080e8021100941e0ba0080400402e505000c1c20543c13020350701d0300103000c078030740500c030342e525646400b5100d0343d041c0854800032010051201840142282c82d02c4646610344108108000c0d040140f105926842803124030300510f06454100c002d0b603030b0200000c0190b442e42c80602c900fa4100c03140d419018401000f01c10440500c0c03100e0800107040a500208900d07110321496402c1514004d8520306d4542004140300004020205485480010030303291014084241269981c10441e2401c0e01e050b1140342c20181c81c03004154004068459082d00c00180b04400064203c031400e60449024001a0528011a81c40c1a600c4003c2001a0032560405d040c1030f100d80002c0c100388000c80301101e6880e41c40c0c08402c07612a060015044030500c00c031003507052900c3c51710081d4031910241004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 203027697 1250 203026447 203026501
    0x6070e040902030604050a14030703120b012d0e0409030207030209040303060e0c07060c080105010f030905010e03160501060509060105121314030d050c1303170403060905030d0b0306 80
    0x2101140c03a194030000403650020308483d09400d05080054440c00c8104042e91000703403200c1c80300c0000a00008490344035603d5a03d02404c0c4d040d0b142c6003c0200040b01b0658104642c94040c000202c095080c920a444882130684020302c10220005d88454041c0b9550b5008605201558000c01d0300401c03594100d0b034044c1e4083c240d079991490201e00400c42c2e60400f40c400b4180d64280703c800c8032100040d0103554031640d8104007044d00701d4000d0780c2c20f034400d104290000303e03492544c0c4d822074842c3e0480740140c1c2c030400c0041840c90800c01090b0968000b04c112000742d810f42c00044052140c04d004017401088140d40c0407074941031441c002881445607003401c0100c05803140c08200d1101079202c0703100e160b5400550300020810913030051a160341c000317440e140425083c40c0c085a201c4400c2805c0740c81c0000319542c5001c4091950780c88082444819041c0c41c1c2c444010700000011070064010711180030701c140d0140d9512400e40144008076000c440c81c0324000d9004c0003c0024944240e1003546417100301c6502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 203028947 1250 203027697 203027717
    0x3061211040f09050303010311030604020a05121515031501052b0803010b03060405070e01050415090512030406080f01123809010b1c260c0c01031103090607 69
    0x71030080c041203460840706500d08042c10050202c0800550306a0388245520800c0310000d50070140d8504040d94065808042d00204009918080c0303400701d031500c0c2010584002400e98220300005203802c80d04e110004d160410511141d02d42030000c83c681101004e03c030741c100d5050030b011410326285440c07108102000e07829110302c8512070891748640e03d83c0c01070405a0302d41c2c4400f40541150001e40300e9a0146007010041000b49000e8040700c40c00c0d20069503103604051030050340a045110b504200e10038400807000110342e9444d15100040c0404803c402956654680000200b960100411a10170302002e00c00501840c0205034020a1181c2c1003001c070348090325001414008400204107088c0c80030b80414000001c000b00a83c001d05c10b03805070300204210141d4106111110307442d00300c84000d038845034800e078001500c4200780d01042d9400d100419040840c81c80d01004c15400a101c2828941c09101000001d41e45401035180d1001c6141e4842c1c210700b041545907541e5a00503005034140f081e0445 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 203030197 1250 203028947 203028949
    0x106080705120a0c120204050a050601410a09080d02030403030f0311030f15241602030a06021c0b01021c0318240e061618060e1003061211 61
    0x80108515080004880754a6442c080711030f090099170341c03c074041d5003441c0000b001448a4400e13140f0404041c0c6030420480d8078100103240d123400d18041030482240c0c18012000300c54040201000f0395a0b8009034540c2e0301c08000300030740006103603071003264a0b40c0070022040d0816404800c0d90100c80d8181001610443d0b1044158081c1008950076980e80c64040104440108040312450091248440e101c0713003a0050014001d407003030401c50401003003203100c1c40248910607540040c814807900c3c1040100210302d560010b402d221074242c054400a40102d03c00b06c01c01c3c88000c441d002c020685000708051595403002030b407650803400100c051040000b003c0c0c00c42c0e074001d412080794000071900e048030807141441c107035a01444000c12402a09500d0407064001403291050060301882d40d0000c2032640d84545400701c21100d109000700400c078000300d0b14213034a802e103d00c1710040c1140e5182c0010010444003031010480000700c002c820941400030070042c240407442c1c406040c68000c100101d64201e00c030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 203031447 1250 203030197 203030203
    0x901180308130803090d030f06050a0b030402120a1208070c0308010603021c061502070b130b03150405040c0e06010c02102d050403290c07060e0709050106020c0102010608070512 78
    0x604083c01c3c2407000010001c04030300118514079110442c0d2410003002c40c940c0c0c12003049035010b00801d40c1040781a0800d2140551060240d94483d2004203c40204651201041e080c46002a001c650f014040000d02e840c0035048000680d0001e060701d03101607a10401c3c0c80c01040c7c06010b12890040c198001741508180b21040c1001c1c0a441014001303104a41e900d039408200da80040f04000b0040c001c400000c60b507000324004031181c100400349607480c500c0c00c083e080441c0303034406050008401d90454480079180c03218046c0c1c030300c2603004114459809107880c180050050b0005e041e9410040304610020050361424401e42070010781349099155544c10300200c2c01d800001c450000c1080050300c01100e02194000000c2003940e12659500c65484407081d25801e60009011180e41400303130440000708500390020252910900440700460446044800c0504001c03254201880003501e9000521800d50100308080e249002071008100242c5404e41e241d454600038001c003881540410626890302400b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 203032697 1250 203031447 203031481
    0x405090112030504060e0d0b0702030903010e010203090a170c0105010609140103090510150803120405010b010801030525031e02040513110f01021e06010e010b040b09010f050f0c010905060901180308 87
    0x2000d48d80541d4200242c01039035a402c103624582c42503080c4511100164818029a801001940c008000c8512a65035141c1586104036410a00503406c4c0801c4840b12001d0040030700800058850f0320026003000c2c5107040501442045e5030600d4101000392000500004150100748240300000a8001c5113200c80440c0d00151b03440350440c0e100208000b02d40070040740c1c1d07103405144100020880304580000640d4422024400581207800144c1d440800f1500a6140a0025158051040b00941306e65079400d007516103140e044c1c2c000c608404032004505140c40340b00d800138050742c204003803401c050340c80f804800000a1180c3c003541d810b9040c507035181d0080040103880310a4010781d4000e4150004410fa46100920803400d00c08031400002980d003868000b180d0540d0b00d45450f41e40b50816460041d2052168482003400300202048920010398a500150214108103800810080640e0408500d890800742680580ea45015005520401429025104250b1504001c4030503a60010104844918 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 203033947 1250 203032697 203032703
    0x603110402270a08030c0f060f09060c0c15010303110607080c0706020f19111606120c0908030432180a15030f021008010b1b210405090112030504060e0d 67
    0x300386c000310048003142c80718506418508a9803590360b030002c000c011150540d070151080d0401e80110b0307503034608480101108202c00c4115032110700e884a081d5440013099005130009148136540d13010007072007400056000f02032483c000040d401c0600e643d040500c150000240008d500281321480c0141500a45105064401c100c40b0765100310400a40b0303500a20700c454825004084140041000d4100c08100f0b644035aa110301c8841d0760390703054200503d406101039040c031141c2407000a0034a0100000d0015041c40170600e0070058118100049500a10990b4403255007580c0300b42100b512400744040c0c040007a194611080d8807903982140082007944595002c1c000c070302502000780900380340744089582c0700b52002c5008102a2104450444c02805580389004040116042038034141082030100c2c8288800c0c0d80031483e1241450190100000425a000038049820801894a0325405d0300409400c107492a0b07100c95660001c11030311981c050700c02440b42d500030040054032910ba2030204654 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 203035197 1250 203033947 203033953
    0x1030c0e0d0b0f0106080c030f070e0d14010c05091302070f0b0a0b010f2105060a0e0f06030c010c05150a0e0f0709050705040503070506090102120d0603110402270a08 73
    0x4242d0801d156410800c0b501d02168800070000011003901c039041a520501d142c040e02401c44c0c071041c03081010494040c003904100100e550500d130f01c07075451a0308107c449100d640b0080c40c80307038002d03415030a40c0c00c02a442d60621105000291240d03e4001c4621a1101c50100050766020146040784211000b11009002072030f100f410880b001c00350307602861245000342c940600b024070325581100d11409039500e9615100c4250300010030601c051700000d4000700d0080c0b0b11042039407601502c1400080407130703140d2100c001c03510a005582c00c1c1031144051203a0b0a18120122000b5a03c986942d501940e41c604030510840e00054004945903201c0800e00c000350701501c20030740c1c4803542e46075100b685009484c69149410f0109039524060b101300c0b01211070140140c4001854a0308024441e004850894150b019050300310800a803c50300404020300031010000b00300d03013903041c08000300b20400030440c0101d104000003446034401c2095851070690024181841d9444031000c2080040182d03c4081248 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 203036447 1250 203035197 203035219
    0x911270702030915091804170a02100b190308030c1b0a06061410120212010f0303020c0303070b130f06020d1a0901150f0e18040326010501030c0e 64
    0x5940400142544281122030301d44c0c0f0b050b00d42c01a50b580c820340956541c0301302c0164117201e211424125440d8080c1c0603107a4002d0101c0a1000e103101980601d030b80c20f0040c0c100f07242544107141c8620074118484801d41c0c4841d4150703028509110b51100c0c0340005040300302c02100250003c05210708494491003101c0d104040c42d0503c00b84699a08100300d07048a2660800c000840c1034140750403000e49201c40201825200c02442d0400c3e610300c0045250144460b030200f000c100342031107800285009003200103010742d0035455820020709003181540041e01c00c0d04200043c001192400800c0e90300a000580019500603a03071900040c0a45036039002044540080360b114540b034000d0380182030000c03034485050660300c020790401c001071b807090080040c4c00580c81200d05850b0722030420380400159034209003200035080e000081031642d008184e20741201088081204040d800600507510001745424450510010480c0d400e40000500841d41059550b4620214180c403526a00300c580c0030151000d0003030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 203037697 1250 203036447 203036461
    0x40201120b030a0c030b060301090804050d02010909020f070b010608160815040501090c020c060705030412020a21021c020a031103010603060e0708070503060708040602090604090e010f0f091127 85
    0x30b01c0c2d13a44010789240341c646000468030b08041c0100396219a1002400d460113080908110058007988001e904000505c080130803168000e00c0186412001d42d02c01c9910365650f45043c070300210050b000314040010107000c0c001241b104040c480070f80d012134100403100d17a80c3c1c1d048800000c0460b0010340e900c94108000044c04040d130340e00c4100428001e1b400e4411342e02c230321400e02c401071044031402001580304010810100c503601d411b070304a00384003c102146d0341d42d851180e2213400701c0d2941004003820103100034200714038000c1c01e044d820b00698581034071070a030950001425081c1d00d2002410540c803d20122440e95030139403000018580c4010b042000501da054141c1c7e503185e40303000c1c6032607500c01da01003c10740386000200c4a01c91000d507969284c01d0360311641c420000c0c2d00911106d07500300c44144004614101c0d640580402d507050f100001075402008030039101a10038100d0060b80d132070300c1c00b054000400c4001071042d20402065420452000034400c0d6401068400c110b0328188031050400e2181d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 203038947 1250 203037697 203037713
    0x81302180f0106030b010203092d030f0c01080f090606090c191d0901180b15120f0c13030b1801060e07020610060c030c1703070306050301050c040e040201120b030a 72
    0x58070f025940c1004544060001a40c1d03e1284130091540708915000c840b280f0000c0d1210b140298402010381071300300d0321a102191a040d410f0b40b005880b074000c1d2072006120759124242c00e03441801410900302504208840700c1c0ca0300405001180a9901507002428011f0040304440542400118260380e40403d0080141100e0a0900391000380c00210001c02c100d1801401450583c2d0300798490040b004032401006000304065141070343c011140510000d124604e40014010300210754101007220b150014188800102c01050030400340b0051100740c1542e0540e68164040e03c5d405220340101d40c441c41c01c28080900500c051901940c00e24401050070105106060300130701c519021905e05031550207088590004038000c16001581c41890280440d20640e501c900490040000c0c00034600b8204400384194400c85103d00400d464150400060400b4030459a028070714401241c14242002c0342c0024040d00500040e0401c4125402114105d1039a0320080310460002c080700d1000300b01e8586111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 203040197 1250 203038947 203038949
    0xf0c030e190f0b0705060f10090f020c101b050a0c0c03050a03021002030103052e0c050301140a030c0501141303050a0308070e010c0312020405030a05100c020706081302180f01 77
    0x460b1407100000030707003182074410348a005510002908046e680c0786c0c1e0014590030b008142a10010082000041110a603c01e04c4007603521030704d02580d02d12451101c0e131b00c0e0921814860b1030003450500e8104004601c0300c18640b103c00c1a14115950350381990044481c00c1000c00081c10407540c4200001c1003240000320450000d01c25001d03981c10102800302e45080740424880034103d40c1003103212940e04200c000b40c0040401c51000ca820360400d2407003d20007202d149000d10700100784000018000c000c50408401030a02040f511110024110b60710440100f072144500c0e41401501000d12806083c494260b507085902080c120b514660340707003843ea6803480e4840c02a40441c18040c04129a1b610031107a09a5520068480039400881643c048a02501d01040000183d600b40300108840c0d500344060913119000d20003d2100943e42d08a0b48200d4118904500965105102c10446190044417159210260021120440b421400424100e50716080e00380b001c02d150354100a10900a010300c54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 203041447 1250 203040197 203040209
    0x30601111e16030507050f0111010f060509010506040308090607060b1f034212050303010302090f060904031101020d0c03020711010302090f0f1206090304031103010c0f0c030e19 78
    0x440c02560000301030b4081c280c90001a1242c0c00800c0240540d0130f1a050206000b48180f41c011070102c443e000040c02c60750301c014031104594540d1001c112038902100c80c10301500d0b013210350300e2130b151960350782406620650660358014400454140140092944000740740b40029000c150b12120880321644049000032094021901d0540034100b003210b450080010740e2141c51502d8107403007824080c550780c5003000e408800a11440c5070041292800c009005569600c502d005580303075410740c8100403c91900810090a144181081001e56074518001c0c0790403a40500381902c0381c18002c1100d40c06441071204c010406801c02d0140d0103000e625078001c11310240600042c08000928000440c00e80c41401c00c440d81c0f05201c0b04031850305103030610b0300201c0c0d443e0040091400e92103c0700032604100d011a00207040350004281003040c001280c10340e00301c6070812002040070b028402d8001d401c031705036601a5010480c0001246003090300030a0345110949004000700031011607801a4100049180920f03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 203042697 1250 203041447 203041453
    0x509040c0f060504060801140a03211b0c15030207050d050a020c03060105030d120609050403170919030c031106010311040b06070209151305040c0608090610030305030601111e 77
    0x55000e10410545040c2d1318656100306c0182d10300707001c1c02c50f81119203050302e078030032000b00c8000700103000e643d1000c80071400141d9003441410350b85005055004088842d251241052840e10001295a480b000540301020004682c207841324504074024021060700404502c141d60480d00c500784c0100c0074003400c0360681d00721560503656209054483c0820700c5001d80507840b050410350068020031030301140e0440d07100001a41d0f5a50b8642030141c44c4191400d41c0825690000070b80c0003510818060342c84940c010003004528800746441d204d05031248030103002c10540c242c1a10401d449009842c242443d990210780c00303542c4a04180d003613100100c040714440c41c80c084a240842c01c000040d035903815002415054aa80d503d0700d9a1940058034042590000916040703900b0750002c0d21550340a0340c01080c5040a583c141040a0030204000c0d214113040e510003805c01099002010f850b00640740c0c1407906c01d4903074480d0401a940c0310b55400d2503881a0003107402d0016806850000035044414160403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 203043947 1250 203042697 203042699
    0xa0501051e01060309150506010509042301050a0b0313021215060901080d0e190f0e0613090203060415061a031b0307050d021602041a010e030c03190203070509040c0f 73
    0x416805c80d0300040005111900c603461910303801e80c407980500c3d405041810700c1480c06400c1c2d03000404544241e100080041490401c003070503a0000c9060740c4c007410741074a5910244d8240203101f003031404010010142038520820aa045440d08101301e080202e02404949000582a00002c582c241c00c032000c500403881e4400004002d840050002c00110440d01c51003490341032034061050244000d010056500c1222600103041240c49000d5401000710301e0408415003800400c1040e00d56405498080c440d080508401c05a50b02082c4a500640e000c2d100310f003c1c2c4404507448024181d15402440b034281805c03042e000c3d1203040c0740118411100c014101050350f10b03801c0f5031003050009884d1200090b2041c81000c07114401c82c0c5c000d0a90340c41c6407001e004e18442c01d90004095850303188565080d207492980f080c0c0c0550f0803558070b080000e03088000d0a584000f00c4040382d138455141c0c03d001d40300032150030040b00707644007800000e000c1c1c000648502044d1505040880403e030152141104411485074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 203045197 1250 203043947 203043959
    0x9041a060103020a1d04060f080f120304020a05060c0a0209090c1305040308010303081b0f07120804112b0605040308090303010e0403080c090a0e010515040b0904020307020a0501051e01 81
    0x3007140c1c41a40e07141c440748080c04982d0100007049900e480c5c80e0b41c129a03070300f00114072249050002e500406a0500038540e80c1241c2151a080442070445600420400e00602c80103030748980c60b030301c15201c0a447e0142c4996024401901d000701784c90010703400c40f665005005502c90007240c40c0091010a6445401114960401e00b02b102c3c011200900052008001400040e03c40c5c00300035004090030845601e13150a40781036045c0c030b621500440c0440e410000c2c908080103888900700c000c4083c5401c11105620b00f0307071201c4040c82c1c206480036114010140310741c1c1b240060361040300300500d02a200251915114580306005003800e85095000c5401c8200050003040c000080301d05039155030008107a1078482d40c0d01983d4006001c0c0c003540202d0014445080395440d40b964a400401c0f002e0050a029403410061214482400d40340055908080000b408000543e10840d030a602c2c0965005a89030b0301c21b40100e0038510203040080c0254200424451800000c0c980041c0c0c2c0080600c0700005a41c0c0d0b99 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 203046447 1250 203045197 203045201
    0x12090521030306060702010504091104050108090f060115030618020304050606150a0e180405010906050907080a120225030b07030b091303271514070b041109041a060103 74
    0x8000300c0d0640d204200040d2142842e0001e00403062041c101181803a840380c08810139289090708503038120002041c00c1100c1d40e4049045500b007044030f0b01400d00000b0004040e44c4a038414041e221460000d10300d0008441c0c0b1a07884600140000c100355055502080032503c007030b51040c1c41c01d4500784260000f1a15624100c410741e244560602c007941e281403443c24080e1024559052015842180c90103907540d020140c0c1141031040388100000079005150346000011980042d02e1000d5030f900c102828400b928001422118080c0c101412494440785441d00300e01c2c040002964244110602c4000518480101e01482c04e89100d040d5090855032100300480c100c0e0b01d644407141c8c0c07150794032021580c0112043c0304603d406d4081c1c688601d0b20011807038500148621a140e1200c034800102d010044e00f990540c440c2951580c600d0301003201d4451040180d40e41c020010058400400c69010400300011f14000380c002e0a00501788600c1454141041c41074441b02c0303c60346090401840005003598464 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 203047697 1250 203046447 203046499
    0x605030d05040614041203020f0d0801060203070b0901020c010c0c0b0c070c210b100e0c0702060f160501110d0b090603030409090f02041a0a0611060a0507020a120905 73
    0x1507a609007014030b844403c407604d001404c81054104020080030070f1007480f40b01c003545114000d0b00205041035a0390b40b001d01d0180486160b108120620740140100d580c00b000303c0d401150000c0c02881142c982107082030091046100307000e03296282c11480404103800078405e07148180034100da0380056580070303004079030361040a40c014410310000005101d40031a41c03000c00b14920000200c089940015500c80748040c030280d6410700711120041041161038040800301d41d1101d1041308090500c407581d80880e8842c007803084521000100441c1c02040305400c008140d104982103c001c1c0041d9001c180100c40c20340c0502c00120446003008120381c61800c04071581da0146401400944c40c01e45081560001069910360407502c2c0107100207603001590340c50054540700c00342466183e041010381010444030068a0344140188641c003080c1058103840483c400750b01a000c540c000c0f415640f10103040b4201444044024100084035840c121135035071240d8103c060705c0080c2c5102c052030410f200d1003c80c84d441 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 203048947 1250 203047697 203047723
    0xd020d0801090e0a0204060b04080c0301020f0a080618010b040905070509030a060c020c09040c091808030406180212010608060c1314010c02090106020102210906070c0c0b0a0305010801060503 84
    0x403030010800c480c2e15501a406a280103000d5a50f0b00c08241e000906440c0303a81d12080070f6050214050215450600001c00312440442c000c5180103c800040902030082d102000c050016039000500d40d502ca00501200b26107140604185940e102c1c03000e900c803a04140200103000c0d180c82d00143d04030f030160084030b0700310500800600800030983c1c0c5000c0a8a5140c00581c114041d200c907a1806444084029010302e11030407807904881d0030880c1d08800ca59a2003005601d46e05009240b9010459520480b90040e811000201c0e0380130ba91580c08400e035061000003900110452086484200d0651100301940c2a14040e04e846da12011013645007400380030304400311250000383c104052030200c4800306801030f046c10030041040c8641c00040c1900026840300700940d40000301c4c8400a1181440701850b04541081041141000b07a00079945110007404203080c000803824907000d01002c14803a10050007512019a59040100c1d8018058502840390124960a2810215842c50045003000701222 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 203050197 1250 203048947 203048957
    0x6050d05060a1104050a0b0c010c020606010c0b0c04050d060203040b0c0901050406030e10140702060a140604091106160201110109080a08450d1202090109170a0201020d020d 76
    0x120000001c000b002c4120059444100401000459807103110f4410b00620800544a403101d40ca88c41080c04c1d40c0040910f44c0440d0401c50800c141c03a078203c54003c2d0740d0b98000040028a50318030300c204456126a810681d809116104c0445c20494190001c0d4400d5124900c46a030607280c140440c0400c0c0202905e10307012400502c000c0c40000d100358400b01c4041c0b401070881e01460300c1d0344d010500302e03409110442081480300c000c0001d2950108866904005001810020042e0b00303c0c680c041480043d0480b80b0854580300b240043c00358281100840c1e040050006603110600c180140052291407001c070b0108524a01c1e02010900c180f15003200d190300034100340e103003245244044803039040061084204400b84414000404480c42c0795064054490381c1c00d040c4c0000e01440c1c0c01c107105072020f034901594812920401e045600083c450884015002c0141e15603503810010398805181ea0412030703103030000e07083c0180d808000290070a1505e0007038013035406c00e4440650898503924254000380c0426 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 203051447 1250 203050197 203050201
    0x3150c030902060f1e0d2c030a030f1409030c0717030a1103130b1c0b01140a120e15070504120b0a060305191b062102041203030203070306050d0506 65
    0x2841d454010700c009160805002c41c00820171007400700030707000340341801c00711950741c0c03080c039029210760303030000c0d5015000420508446c001c0c0701110307542e100f60103d0382d0806454203c002850810794000e0b1404440010b103070959450556103041d034940140d442c1018030300c01e0500000d1000d98034684000000c80150103145003540700f800685081402c2e0a40c00e01a10042250910210b1300d64003400c05002c203060301c1580c0d1002503410380c01900c00c0640012040c2d01e8151024040e0783c00c1030310103211501c0e00711032030349800304c1c010309482c481c0842ca0800d07046400c005400c01c0d60400444d01c032281c01e1200c07240100945580a080700e45001342e002c6c01040450382100240032411a80409031300c5604918085001c68030303035076000e08000045004040940d6245916030030808c90400010400e544a862214214604000201041300070b80c00c04020842d01c1e460055440e00c0740e0105c41c040e100b05280c2404e80c003001c1c036004009600c201c6800d0002403602c4001700e250324041d1040c8020541000060280d9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 203052697 1250 203051447 203051467
    0xd020d02120421110909071505091f020309030709020405040f090f1502281106220f0503030f010306050906071e0c1b030c0e0108070b0c0a050703150c03090206 70
    0x3803002c694184c40302d604440c0c81109940d44c490940e48181d22032009480e000d458246902c1040c81c4040304038050083c14004080320303885a41810049074a8100c04820300b03120701d10182d0541c480c2110725905402004408150108076030020812103030300361b13002c0005d660001400b504035500351400600b2110260802e00204803900c661084040490100524085030041e207103001c83d945911a40b03d40c0c030100a400d4940f600701c0c0c2d000c00c0080c800c9000c1c000710f04d88440300c1510384000c40e20944208400240c203c5c2403203c00c80d0b021842c1a8004116943c03410201e41085508000b4882118400d05003400208100d00c0400e80b0780c050611900d401c1e80380c131080107810690501c40d500c9401041031540540010422406100514240c480340b04001241507042246d1050102d0300310390825810480100310701d980c00034689080b0340f10f806183d0b4903401e5010f1011b0810202c1c5002409038824640c020040c400241c40051042e030003541d041100440380503065040da041640c002e548800b00340110159 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 203053947 1250 203052697 203052749
    0xa0e13150501080a08130b1201050127061103040b0703021f0c020a021507060528050f06060702060d11030709080c03060109110c060a02180a0311060d0e0d020d021204 73
    0x5140d0078481408000b541f5050340188507040b1000b070018084900d0b0040281d540c101001c5002028200e48041c48078010040360071000d10b81c0d11445007000040292000c400d803007841510043e14102d002e403a92140641402503403446002d540069a040d50180108c84044900c02c0003540045070700034240f11a1103408200d4064200b0a0010b165001001454000780d42403051920400d440d840342c40c51034684141300d85c0359404032024440b006203800140180b80c8001120998000c40031101c3d40c2c2c5d10034080c4003003031290040200c0350b86010700308640002d56110a0f27001e148107200660310b07d030f5a680d903407066035030b01c1c400e000301ca0380c143d000400103110400c56a0482c01118200c101560718002c20410161f160040445210010942c0801c1254119003100c0f01c54402400071248510700700d00b10348401040c0a00c110100d40f2410002407100c47d406002c0c0c2190754402080015250340355907003c070103921164400800c60050050880219800842d407054900f907803440c4800c408900714403090305036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 203055197 1250 203053947 203053957
    0x60106020d0305100305340b0f0c0102070b01030b2a0307030e071505120a09030807210501030503190f090308070501020d15150f0e06090a0e13150501080a08 69
    0x4c0ca080e1885000b0010403010880300380744003620b10b6080c043e5a0b9103840c80d5101032411610300c6280c0e452445c01c000604007803060329404c1003060340d40c9650b03c1400300b00071700903c294040141008101c40c00042880456010640314540079070260360301c071900c690058281c5000306001d0090701014000b094140d8803d5100100e05c0080008940d00700e07840341d1065002108001c144c2d400206c1c0004c0450345c81c044201110380000100106201107212503802420752034000b801b203410455030401c80807212007014008064028454030411095841e03061031500c0313610454000301510214031003800014800d804035104400980d840c141c00340d0641d0398180c04c80e400504259483c2d03400b8080c0b03000c0c8061503c03480031609007400c080c088803464122010f140d2030034903054405009a01160755810303900040110741e010b804580050ba10030540300040c901c06240d0b0400c1088030585000c104540d4440c2051a075010302514911180c150880540b03410b80d0b070240560231050f00105981d000003600000601 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 203056447 1250 203055197 203055211
    0x60304020a1401170a1505061204150b060a03050a0e2805010e010f05010510080106050703080c12010e090f06040c050d03140c0a0b0a0b0a05060a03110705010e0c03060106020d0305 79
    0x1540750031380e0104404084050314142040c40c1e84400702d00700d5010900002d4005c040076258981000207410000601042c01040030b80240d107204540c80562400f40c1c000111042c00608142e01d03245c481c00000e00625045a103591b8041c03500500f00f40b04e1000107050b9580386100c482c1c001540740c480c10000d204000285e02146d040d0b4a41c1d40010300c0520a0052480c210f4070f040c3c0000700340d8900380400c1000e540c20a002030920480000521101d40d00104480c540e07074050070101000d8503071504880c101d2082c5046c3e150350380240350010445109115030640524658411030315121914a081034507040300351401044403464800070030403400c3c516810300c0b03004d029080c4400f0080c012445000c06600803000740069411900303038081000183c2c0c828541124158800304501007440c00851507082050044c240301d0703c000b280c0f66030154400d4101030000d507030340b142c21a01e0b200c1703034030300103018015071741801d08640212821030629080002d400f074100c400c3d660041c81c420b0440441a802840003030300c20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 203057553 1106 203056447 203056457
    0x6051b0304050613020d050a1b090b0108011a0421030927110408070323011413030c020a060215010504020f0406030b06070615060e060304020a1401 65
    0x491341c0a0501641d000da01c4000340000784410b255420300a03c1c9224100a020401c0036584012a62003072440c8102da0701502c505148040d940a024814001042ca4004209684d28150b0500c1c105501c001c07424541034485000e10b1001c0300c01c001225003103038038103100030425a100c844a002020342e42d84001ea0b11104440d240700b030743c0c00c101807040714a44481d00c040280000c101107800400c042070484003016903910300002003401103071085c04401d00a03003101c000c9840c180039840140c1440d403c9007500d5030700d5170448401c920040304c0c20740c20444051403110050b00d8101402010346035a800402079413612551200c8940c7c01608824001c0c0d00502c0000c411540340070036101030343e1700c40c01c011030240d04903400300b2490b02440030040c002e103081c01d5003842002e4161450302c00b601c49568403c000072494000380619407205075402500f0901c101410481120f0750140b42c00b0f608414501 = true := by decide +kernel

theorem cover : BRFrame.Cov 202877697 203057553 := by
  have h0 := BRFrame.cov_init 202877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 202877697 ≤ n) (h2 : n < 203057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
