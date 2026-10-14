-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:52.0014+00:00
-- url     : https://prove2.me/submissions/d4a21876-75c4-4464-9a7b-88ff51be7307

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 542266187 ≤ n < 542446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 542267437 1250 542266187 542266211
    0x1f03020415050304030c0b07030b09100302030d020a081206210d03053d05100f0212031e07030e1203010305070e0c04090905070e13030f1b0f050316080d 67
    0xc50b4004ca600d566079032191102034a4502d52000b0142040003015120b000e07600259551990303441c064407080d01a140000d2540c4101803a1030240c03221002590080c3c01101e000c101e405003030320303000c0329142c031390304929038900001400c10461498100c80c01940400004000c1d140010050309500d4292070410640d107503406282c480d01000c440c890b1039540075660354240004483c4459100d00e084410034200301d5103a400080324583c00390141c074001018010300001c200e0b4100141d48480c10b1140c2000d2460500758022030001d2085418445c400d115500070858032480b0303a02250b2368031000c906442414280800c140360303c1e402884140c5444c4242400031840380f5000100502543c02d910070075251501e011000c1c1c0190034050002d0b00c0a000d4030b0000100420b0030303041e0750300c5081c0041003011039003114070713000e44001c29045e0f01404001d8107808203007030340e000c05041041c0d0603006a0b88054190403403070118a503101d90380f44503030450043c0e40c4c1c807401c020314480a080d5079850b0300c0c814048450201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 542268687 1250 542267437 542267447
    0x51e090316050a0306020c011d1f0603080406050702121c0806090f01051003180305210603060c070809030106031a0a0c0503071b02031b0a090204030206030c091f03020415 75
    0x700602e540404415010030000d1100e600600c0d4012418002081c08441048040f0701404d40311030305561500a40c0442c5500b050355002d540c1c02e0459200c041081d181103444520040c0600c8c00f48409000c000a081c40942d5240790305955859110011a000b05111202094050071451480303000702d60400082009032601020441c803030314681001180603840c00041011141c121948003050660324405c8080f02000c1401d60304840d400f9442c1c1c2c075550286035103104601d030840860445480801c10503c1200e513400b00c0c000d9080315142c0c0d5042e859010341d040814180c419560340640c50f61070320000000b0040703100104440f01e0b2600c0c03c2041a40d445170004415210800d159000113801000020300e018029640981c103204503400340380ca02c082c0c5601081c81e181b5640107040c803d005078600b2100360b02e002d41381103026005c02d020035420b0034030b035134042071041c040a86002c0888030042020303403041d1110350520320148410200c0c0301d2a4402440007600079401805071500017100300c101e05811034019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 542269937 1250 542268687 542268689
    0x6021b10110c0a1e0b0f15041a01080a240305060702030705070618090c0e040b0a060c02120c09070e1906021c05221422020a051e090316 60
    0x40015103c03070b80c45652a502e08200e0f40a010064410b0700111074045400e08540c5441001d11150050980c1030581d8007031980071002d0384107441a0305041400204c01c070008040100030000307090040c01c0e619034240000103403201800da07404004039210841c10428651582c01d04807801482a92040d8541000890f101e124800c8040c0240d40080010000f60b407143e04401c1e0f005224410700300c081c1d030b107402c2c86105461800f038981c400910f01446801741032501d8440c061440c42d003240c415172518035000026245120442c00a413151501040c6503c8500d0207100041103510018144042841c0c68200a00918140242c2da4000c40b02e1a80340311240d6241075007003060b9540ca80080603911a8411001404d28001c0d00620070003c09001c41f28070650f0303400d0b018589201400e04424000d051030b07005602c0e01d03c1d214030f0740d124401c107600d69806195052600030190030000d6015980340204041590980f09044103054499202d04800840c1c0203503070007034110040300300c00303540e040300c10407411201924003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 542271187 1250 542269937 542269957
    0x703060e070509042315010f090611011808071e0807140c0a0609061e140708090307063513050c15070b09011503080706021b1011 57
    0x14000890000342c003850240c80800e100800201e03140300c00c0300590010344401c0d00c3c48041141c081c000e0088420f00c003030403006c0604003840c00591030414440010300c03012181c461031003440701881c00a13070050029000040d108020b803038103d0300403c69180010260b8041e20013641c0c2c032061003002e05140303005144c03408559a005040c050034580291103061042694a070701000728468207000100380c0d1101c4682d4002800075468004c2c1d02c501d00388020b450038070700303220304403025441c0300c2c006404982041c0329065920908603010b490744c1040c80d00b00340d00e20a0902c403079854421031400203180c40c0d010000854071165900030440008034500c0c4d00c0e088403200c1442c04801002c0c4000030320041d20100910300c0a42c02801103030281c03005030020035040038070000407108441c000a030b00d00078000c0c401c16031600402c181c03008103c1d014905d6001c40510105000040c0020f500046100a020940d01070b06e0010560400a9005413203000c00c541d900e2144052400794182044140307100050040705a81c05880 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 542272437 1250 542271187 542271209
    0x6070f0207031104090f0c080d05070f0b040804030501020c0c0a0909050714030c0d060c0f14030a0c0509030d020703060b06040b030c1b06130201020c100512060604090f090b070306 79
    0x1045a41d00403c07601d030781e07810300e42280d80c8404140104003450041e000b114000d0ba207220105040409181c10203e1903080790060003007c111080004ac0d010707101546450f000306100c0c1e0325031518909240a445183e00181c441e600109140324844000718440400400864440081c0c070b5813040314209075030700440080c2480c1c20101d0100650341958020020520000381900c800102240c00145c44c068030f280d0540e410ad0352814406039007500840e1050444030307942802800c1503c1641120464440102080106503e5801c00c0c120300d03011340d003542c40c041001015500c0581c00034000955030a42d512042d2001c2d4104619010a03041c9001242c066500040d5020300e142d541041e603040d40e900202c850115048400c40030061300300180802c03401a08150380880302c045260000901e0f00c200d414500f4072500c00b04505840050b080704c11504d810032050443c3c18aa42c5502c0062101d001e150f00c29602c4500307200c594296900c0d182d0044440c14450301d030810440e25641030480c2180c029006040b1000c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 542273687 1250 542272437 542272439
    0x50d3b0d050c040606020c1206040b0c2104050f120301050f0f0604120309140a060f0804050a12171003020102030915090d080901030e0f03181215070206070f0207 71
    0x10a00540c04a40c0e94021000c40d14030072008004602155000c2d4424401a0450307401e0307180b507140c241d2003204001d100d44010300c61801d0503114a10260009000400054000a80700b5400322009006d0802c0d00c42d401040241c0703242c54142980c450300e0304440741d00d41d800b0340b00042000240c24400d41c0c1c10790f14050b001c1a151090102401405d50b400390b443c50303121906000001301440c03c2601c3c1d0088502c0f0356203075030540d4540381c0e1140d00304145009841c421030621505111483d444100240131070b480380f500f01440c0d1250b044c0315003004141c0c0005000107500005890300680c01509107542d40c0b0340b00f5840511a9540500801c0c40d40321800000d0040e042003001260710310300003402a0703104000c0c1c50701610308144100043d941f10304207501191680c00c01b0480e946a580c05201e050952100b14000d401c01c2e4440302c520359200d106a24801c5424072034004100c030b01747c43c1c8240d03600c9806424022916200c40070140c1c50113104080352141c0c0140316503000220b100348100d07503404425281d60004c006403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 542274937 1250 542273687 542273689
    0x102071a0a18091b08150d080d060b180409020a05042a1e020321090a050a1506080d05030417071209080c120709050402010309050d3b 59
    0xa500031074401c02000140d2001800307405403440e821000342083e032400107096070218001c13201c00406070110b03030511503040c080100803140c10030b1000e0103d104072856880a009490300103c14004c2881584d00345180c0000807950140d90402403410320070901d040c1c01d000005200b000203448612100035040103c0950402c000c0c2403079001729070340703012120087e01c420b54844510605102030128060008401c0100858a0301840740318034400303640e07480134520741600c1252506030240245400045422103070006840d640c8148203050846611001303540c50480d03241841c4c4100703030900403445000340c0351040008501c0c01c00074014142ca02207032552819680c3e00c2d15100c411342100e03100c03440b80f40002c210f50b2002403140107104000b82c1d265100c9a21060030002000c0c03520391850001c03800b482c10600210316045000510314120391018038041178a590b1480103d024100216006206100c7c03400c0751201e440e085032145612a0300c030102801e11030b503107034480c0d0412541608141e804180d105500b44503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 542276187 1250 542274937 542274989
    0x90201120b0a1211090a0e0c010c17120a05010504020307120507021e1e030436021b0c0108041119080f0708010e031312151811010207 59
    0x4050300041040840320f56030980211400e04220303040b100c0c044000192800381c5040043d058200c951301c2020044601281078050f62000c15240a50521184001e600200b02401c003944140603003080e203040d15a03203004034040d00c041082d01c01121103801d2000210302c0f42018402e9034410200f41e0358940d822211801010000c02c00544480c3c118060305020100c41c2c40313000f92030303044a01c03524010301c0a1540d2071411417500c20710003413031480f6030009c2208100c1906184605004541c0401e1002d440c0401c0209140740080102001d00d0902d00209142c1d6000700000d800c503842d074008a098400741c036010001110504800c0320f00400c9410081011034260410216003171042001c144212501a1102c0342586014400c40690007660b12256091040c40c0080c001c101e01c000042005509000403904003030110011070156001440f074003902c020600002100901c558540410200b01e5080110024014444c1500055448600380030040e165035100040c844100e60600180200c0b0006800706801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 542277437 1250 542276187 542276201
    0x902040608030f0919030639051c060906150206070810030b060d14010507090e01050604030b090316030503041205031009020c0a061b0e06070305030c0d0603080307090501090909020112 81
    0xa020005c4000300c0080c00b14440c030211103041300e0520304049110804288080204c0c0144101402c400c21402281d81d00203042c0e801c5856428803c154a41003ca031030303402001c0750750000b80103509207503000400b400c00c025080415501e03682a5030b00c960701c2e03000aa0302000190307101042d021100c03000b00301042c04030001c80d4110000808010300300031162240070aa40c0381320740350503031a59640140802c00740c001e01000e00420b24808000701d10f62614000038481c3c0254880a004400c1704800210258010300480350300400461072198029000d0800408035082107404a41c2c10105c5844200400c0c080c0302901d100303040c06203c010603503013804201406900300e098002003921851030540001031107070150000c1041c071141d4a4145494140e0001c1c400228000e0070760054904210071b50101754080200c80d8000c940c03940880c0d4900d0741329040300042a05074400b07081c181002c01071041044d40b0505110403107034240d860718905a21815560211252514001d000c2200c290300480780728990b8002c01d07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 542278687 1250 542277437 542277469
    0x15010207061403010504020714011d0f1212090a0209100929010309050c040e0a06050105120601030b090a0210030c03050c0405031f241503052403120d0902040608030f09 74
    0x9e407101d01544031176003500c0a41c111040704540c6000c0389035200a0420960903500304030310042034140c00c04101d0b05814491008110a210079610006040000030004011410fa000c0c00384c40c09890301a0707180d1542c1c4090f02507403041c1824101400e07940045610500503803014407400c06e100941100040d00180070000d0b00b120980038601c0b1200300741d5520300c102c2500411203009008200f00c10700c0c000c004c599050b0040d0b8030a001d004502c0841b01d500007043c5040d45c0e0300507240130340c0d0385444100341d143c0b80031604000e5100316048034a0503410380c940c0103184482a03a031400e104d95241c814080115000d00d00415130194803e4000302001c0f40310903003442d1100d50401e00042c917400d60081110101c0800e5071181d144a2070b0403001c0000101c0c1c15049201ca000500e02040b5509014000104050b00b00703001c03038910044d01ca16100581d405200e03124208041400045e0b692040445450140036024800da201d80c0c90014002180c1c0c82c003000716030301100c141c944a071401c01801d0800600c0600c12a00d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 542279937 1250 542278687 542278703
    0x20a0b30010e1918060501080114041410020706060e060f1e0a080f0114070c02030d0c021804060b03070b040317031e010e0604060909170901110105150102070614030105040207 77
    0x42868a07441e03c18148501809480120402e40600b000f05c1a110107a11000c100d07854400d808c0314150543c0140c68201e0350080c143e41e14104405981445c0c444e880040b43c006520003c3c816080204c0396002074200d62a03410100710664412041292041030701043d40c2e0040344c0702c0c16000c074001158030070140c030100080861a60719101c0084d54038100800c501d2100d10382d500d440525000c40c01074a901d51145503843c0100803100b4170340c04a9161219146404240480907200c441150354201c03902d0803c1c0b0300d803c81030503903103094100b4801402c440900745019010302070b00411602e42c0e42c0d0403201036070741080310211003090201c541e42c00c2d54030050004082c6102e2002c005442c00b848003ca074000c000c1078901c08040c1c1800303020002111036a510070052289486103910000c1c9240601c0c2c0200b8860303210307003509d64803041f0045c0c815861641030b00c0c015520300700c104004020150b002400c283e0080e4203e5406545480042d00c200c0c0c698a440040d030314041c0010085440c00f9001040c40e1441540d034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 542281187 1250 542279937 542279971
    0x190b01200105040b060303070305090f0105090d1b1203020307020d051504050c04150806060f011b0506010305011401030c0b0a091a09150f07060b0d020a0b30010e 71
    0x500c5000140d00040c094050351101d00340024001d080040513005041200503501d0000e043e50040c2c11442805c0c0024015041c00f00743c0c00e1503a0140c01511110240986032403218125440c0c00c00701c10f0302041d00c0401c640304d080e8004c40e03e000441e0108543c0c590580081d45081c44580130031001210ba104121000d2003042069007503c0c1d103910071a4000c1d8401c100404552400c041040140d6159811045218440800c01c01540400145240c0c1041c0107942010080b00f604004a0b15070301ea022400b02c0450301d034414a4104500014201c0c101c0c0e0241e4001c014a50b102440c04540038800e1201a06442014105100c1c8180c00002000d41701110f050030b6620035035940104440c405101e1640c6240c240214537402c8604215801c08407520040e0405480c201e07802881d10706034000c1650180800d9a01c0e0241480fa44421220031071058004052a0302c41e503482d406107040e68400c5410070007940056210380b40c0b07140b440c1102c50751404a000742c943c07980c0c240320521940c42001000e0f00764141000103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 542282437 1250 542281187 542281217
    0xb060705030c07060f050703050307121506050403030305150d0b0c120f0114151b0106050604091e060803090906040207020414100e15060702010903120c0218190b01 72
    0x401810b8040c0d5241c0505030b2030780b900c18080e0106514001d02c8040c000c00704850000298080112a800000b030b0030152840785050329644010880b10b0051000c0800315800816000d8020b00600110381c0f213a6400c3c0003594076054007502a03540d0103801600070102e403400d0000102079440b1264000c16055001e420714103c01014445480140da071290032190510050101c501c032000640c541c000190b50390001003183c2d034400b0903507124200036070346a9410a03101400c1c03801c0079008400182002001c5903210f50f20ba40800004000707462940380c0c51000c61484c00c90031006402504129034052014604022441e4240001740d00020f06c45584590300700300e0a00140d07903070303c14003600d107200c26000441da10f480c0c810300c030007690381c1e4108010352030a8004001d02242c108105141601040d20780c541c8640f0300b44010b85102d40d175500300030403003100504a2424103a20421121000b40211200821543c00c6901461555000d6a0443c40c041058803c984500280d800901490b1010b1500c1d811035500b0003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 542283687 1250 542282437 542282443
    0x21914130b040302090c0705210d110a0f14090907030204080d1119112403090a051b03150408090a03150c090f0e1f03030309021305010f090b060705 65
    0x1d0003252071004046420300c294100080070651041031041403c0c44c0101a0320f8290341d03034107004044803929044204521400d48404142c80120b140c01c441170000b203450391420280d5411003c503510001e4001101101d50510454041004005030080149888901d009020400800a1803001895000c1100140442c03017007203000b0b94640b05a03107070403100c00d10400b2142401c51450904040c055503280080220340943c0c802001c001c411104400040741422113103030020117500e20314160007004410050090b00105900032540d11400903600c5039021040800031006402412940550007c108480c11000e00903040d50014011240d990074000f00c2000207100e64141d4204032285c070500d04a03d10a0400340c090a03841940e10704107988800d05140441201c043ca901c18848400031000110f020300403a044003850708041450600341c229268100a0302814894008070300400005501103400c1b20355100b6103041e5041c0442c2d16503894504400c1c20080c00d454a441c507407021b010483c80b030010f0420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 542284937 1250 542283687 542283689
    0x1030618170a090b0c030d0e25030c050303030f010e1504230a0b0d03080c0d0c111c0206180c060a0329090415090f21020102191413 58
    0x152955002100340c010700c80719403513000603440f9000b800310360f0314403102000f55010b44207122000113111304a02c0381b903450001c11130917031501860701007007a458103481d08101c50190781c002c1074104c40266490b004d140d9288811620074041080000045c0710813264041c129401020a60380b0066400211000070704688034094406526000030070348142c00303c0b40d0b000c20f551004824100f04841c51180011601021450b1001000c004041c0002850f9500d01d106481d628000414200104201800050118070301e000c000c217228800c062042d04030103441c41142100881d668041c2c20503856040e801a0100c011a0744045203000d600801c0d005600e80d040a400507a481d941d0105910300008000d40085000c40110003020142c4c1c802079596455014480742c119070b10005407002c1180343c0fa016002070885400c0104440800c403000310074004000b0340c401600c5170101c5072290034400b044040c1e00300c3c407400c0040c4600d052004181c4025600a91001c41d071102401d012074031301500d169aa0000c1406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 542286187 1250 542284937 542284973
    0x16140d05030a1104080a06091b0e04150509070509070507140318100e01080606040918020a06090f121403040807140d0201051215030a05010501050f0108040b01030618 73
    0x101004001c02d0744000e0142121080c545014149050304000400780c440070103020243c0480d484207440c1c010003402e05007500e62100424080700446031a40c0a01052080c00e80d800c2e111002001d217182c01284032072040a009816500003443c1c0c00d480c0509000f5036041c02401a8144031083c40214003040040020040d17121408018640c1e503440729030344542e0f4194606145000e4149410010803da8001c440c00410b00b0f000d080404aa035110000205a0301c0b0302e40040e00c00a0a00c03541c1d240d11a61104000c040e02c2c401c031001491039888003402c480340144e81c481c103032940d904100100242c54000710700005050007042d80c40c44203c520072805207954482c0e40203001903400300008120141500081a2110740d044505e113104202540000301700340921743c407403001411180c3c00700b80c9001a03050034240294000c2c080c1c072900a550709145000742006d108050240106a02c90b800300d41c42890741921662340203100c02d4699085441c1c12005201c481c0201d491140003883d01c034081103251521000e2112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 542287437 1250 542286187 542286197
    0xc010501080706080f0a050c130326030615030903131205060702150105280b2502010c0308090a05070b0301240e120a020a0b040e010608090316140d 65
    0x115065105182c2595540200100320600003407221500301c6066485c0c001c00210004910350b11210412038041c1300700441c0c0d07040511003500c000204045000d8040c842140000a01021038803034882004510040352200d074060500b070200c91307083e8280e00c05150442003100849061112403d0080c11806040c0c02815180c100d03803102d070b01000b600f040000d5125550384054000030b4000b03c01402c0c543c2c8103015152140c86114480800340078841c641000c00c2c00300c02158100a642e4840c4048154080c10b46c110031a002c01542c01403032960000581600c030b5060391840500c420b0f6403421550040043c0464006000fa081000f012510400001001c0c061600386540d44c0e5144c04c00c58908541c919150001c0500580101000a0380204591385010000d49902c0e0948141e01ea0403030074510f1050000350700c044a0000441d40100302406001a82c1f104402e44820780d0b20350800f5075542d0310856041c45254800c011190500701640843d17902c1900c288070f04640101078a0f00300b4249501040c5c4c03400003031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 542288687 1250 542287437 542287439
    0x8100203090d0306140d020103090611130603051003081b07150816120e01020d020f040e06010801030f020d030908100e060105100c08091f03090203161401030902150c010501 76
    0x5500348070b4a566101103040030441d01d481c00c20050340d0003a81412035481101048505019039000350042c1c00b4103035220382c0c00c001810020a01205035000313844c1e000b184115400c03003c80c2d081e0113071140c00e010380241340380400f02502d1540c0302c41c1103a20101e080d0400c41041c49810055100c104074200181042c140c0541c12006084002001c944000380012510710b014400d55500c40d0300700c154501120301018011400d01c0c2d07002001c50180c810a1215041e00d4030015218001c42542d03001b030800d42d201841044040d0322038400441c5c0844080c003000d0480280960386000624110903e5950f8030300c641010284255241e09590600f64000030b080c4105407111036071030600005020007405803008944440d030000e24020300500400e946071000306441c10000300542076680d09a040d4100003000d04072070090420801004015151f4250120700078030403011101046080314040000741c034441c00d0341c2400d8005600045000d01070700c150a98108161f40056042d20320880003c0c0000c030804800440c241d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 542289937 1250 542288687 542288701
    0x703050c01030f11120603240f070f02060c0a0c08160c05060a0e090a06051c05010c0309030c0201030c0c2f040905030306010c0804050a23031605011808100203 70
    0x40d07424000d001c443c1d5403500710b0f50303d207040c0120f050b1014403590311464440ba6880c900824984046c22001c1c1c0181e08400c40c1802600c4515a2414441c01017507110711440c1e00c60b10070944010a0386003a04015802c408006241090a280503018880d0b0a00d400011013425882c0e4030466800011100452050070001c0c1c018000c07420f50910062505a500519102d041a80208032003403181c82d5610813603000c000301e060000d85030088000740200406c0c1401440740c001940c5107070203580800312515401c140c111400140a03100b0540110b825441d890340a00440e40118001d002c800401024850360002000124100308500c80d0440e2010013054154100d0401d100c01501d1a280d4a1344104d041100c002c00192000c401d490308454207080c0b0f9080d1003601d2400d0f50080c0076940126800091600001426052110001000c0b005000b1043c034080002c4c070515845504103070304020102100f80b0100401c1d42b08803074811071203200921502c02c298980000c0c500303042d02800c003584800d4001c024002c007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 542291187 1250 542289937 542289941
    0x2040605030a140f0a090203010605060d0902120a030509090c161101170103200307090c030203010e070e2b05010e0102073309140604201806060d0b030703050c0103 72
    0x94100e06040200c100d14120b03c0b50050b48500401d290540c41d2a206d60100310744094010601038840103216075200c0b1a9015404000d206444041e4410303a0050895001c1590204d04602c141e82c0580e03550349000000000d00411b500302404070010504104044600320010218400070240305244a2441202840004000070103503041040c0301d044240041002070f4601d84001036203414581d50b6802800030308006824030500707078003011415081c540020051645680250706841d800040786001380c032101800c44085041000b06c940103507984a0b1160060001c000007005400000341c0c24400c0f0146030385142c299403221790b60455030fa40129105d01000712014810740c4481c44a40c1030901e00601d810007104000703802035202002680c400000c410701a2461a00e030701c0058240440b070b00c508040c6000b0b000c0e104842495511204e40040c194044d1170501110000401c000c20b581c1040d894880c100301c02e45d4000c002c0c01030043d5a6140c046c0d0540c40a0080030000c50050000c0d000740d00c11742001500b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 542292437 1250 542291187 542291201
    0x10c0f0206180a1205070b251b0f02032104080601050906010f0c020f220501050f0607061505100807080a0605010f2f030406021516050f0d02040605030a 67
    0x1221000e0340002804800000da48601c40d801c010043d0440da4188010303141c40c411b51101922800d001c4040250215824011012a0400010340802040c030b2490881300220f40b40f040050a039203048048020446110352007140341c0c0010141c5c0c000003101c40410307050440c88442c0550200c0040390421181c0400d201c218010101503403088080d1a00d0000203092241b12003500080c05400103401041d900c82980c18002190302416030040007281c201c01c5010500c0c0c4240c40d0000c1810000080795504000e01803002c03200c400341c00541031182650340c41000d024290b4444130320300e425190000e4141c0d20609507201008103525070403210b0800840003480150010111802d0074241041001981d90180c5068001c40151808030341c2411008100c1c0150414600102e100740c1004400c2e0360034100100081c0110f8119408a8000581c007080d000e0240d08112240d21102c2c030901056203841d40900010640c401d20404041e180800000003d400c030b0b007094014000013107011040103600d40b8540700b000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 542293687 1250 542292437 542292451
    0x1615050c03240a09140709030c2304021204020a060f0c061a030a14011a10050c030c07080d11150a021605010204181506020304051011010c0f0206 64
    0x2220518151100811510001e000c0346141881c03a400002441d1100c0041100300c2001001050020780d1000d6a070094204003041c5003114514002094a440c0164031900407283c1c044250310620380b0701000a0b0010740070120100b140c1e00684210700540d5030f20320040000c0d000d04800b03d1402c5c201801840900b032919041107080c031510510784000143c0003450382400e00d0384000c0c081110058103080403034007603089078601d07014444d000030801000310392440040d806078118001c00450b03100164400c0f03100b01105003690440d050809103007001744260010110141c44808591030a00001901880e00066a10844007030300000070700300181d640199026110090500104409102c000c4140d404a002404080c02554001a44440503030400040ba81a5800900854495580b1002c0040880d8171010340c0d40c80e20700e440c05c4480c4401c0c01c0141d00003581d24690056080c18240000e00c40c10a83d5010000240101c12144800e0f582c406d001d8900c4102c0184d541c000321801d00c0002031b150007006020b803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 542294937 1250 542293687 542293691
    0x60409021213050c0f040b090403080702012009060c03040b04030c030b06010309080d2c0705030c04181104020f0408100f1802090a060b280206061005031504021615 72
    0xb59000c0340000a141e10365400c222003260a00e440707500014001c2001956080d0801c505c40200014185c10800c1d491154170560020f0000124440700060352909040207072080382c05c18407203e009414a03202034074030400004210313468180c548407001c8079508075a04c1124003010912040c0100f0086a1116801080c203007418400741404da551800540074114092881c9507407207000f001c48211100409109640441c5081d00740080130301129154102802043e00031f205400700c0e4011414540310781825601d40c00e0070074840d00032030350711011b05180649065500ca81c0a116284100d030100d00140300a00ea03200c000c0124241d42d110b4003007621b16a581d894091031610004502c0c6020014036802030360f504503410301c082d65440e9400002010190808032001002081e010072080c075042200e0842d64104407601c0b101c405c154004c90740c814007200c00c0c541241008000744042405107014507080194000988141d043c4040420100d0300100c6803170324003410072548242400300d0a20001c161103120001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 542296187 1250 542294937 542294971
    0xd0b030a0b0c160210030e1509060f13050318040c0c051b060d02040303030e0f060702030a0c1109090c040b04230403051306080412030b10050a0e0604090212 69
    0x10741144128000c1c4250001c940006100f41c16640002800c0610b80d4000c101800c00340290704000c009215503a403401c0140303e021030b0f40d025101e140c2e422a214502150003003601c1c2d036680b005c028000c8000b601e01e400110b642d03080380000400600180c040b907603021413000c03c905e0f655400c01c01690201d50101041c00300300107113400440c01c04107042c18280540003100701001c00340b40100e5828401c0200d8030040c1407000c0f80103c1050b0341504550030700b00711541202ca8000c51500e140d03031078440036650311015a008000c540b8500340600100c1181d240100c0c038000c59824088003182030900100c90058243c0c01005080550b131070b0601c01c1400041c000d58003006000c0b500c0b2041107095081038840b04510144200142c2058802c0c000c4509a0784006100b121041e51158090904001507030122282c0011000080445100303102d00c01e4254001000b141c0382c8400f0080c2611282e224121100c10009814003800050315440020070007130101402c0107030b41d0941b903002c2580340d00d0003400340c800c0e51281041e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 542297437 1250 542296187 542296193
    0x80321090a030521041a06101713060c030c02010e01090203060c090d02030f0d0e06070201021b06040b0a050d0f0615030e0109060e100501090501051804050111030c0d0b030a 76
    0x14404004541c10b08146a84099082c040d801d410840c0c1c501003140081c5130200010040c6858503c44411080b01a400681d100d907000c1011700d42c4101840c50024003030316404a03003401007091443d04901030100d003140c8070580342c0712042620b1880f94214040303511000d144445a40c244038030400700e108e08000f00141076850340028ac03582c00180c07102d6500840802d4040d610382d82c40f052211010740c002d0441d6213200c0794034641d0351909034080d15800494440c40940c545400c140c01100c160fa54140d001d440c0c41e0f43c50604803080208035010b15504082c0c01e02000c01d5010101c4018001448140c071026128001d181540d02910002c1121103c080d061400070000707a10f80c0000000409001c1c00c001c100301c002034100d41d004080300031001d48002d00302602040210700c0440c0c88011000004014022683c803000340354180e400078443c540e00b0050812650902800c0b00b90265040380c801c6002180c0c0d10221040c2c0c0d21150000c1c0c1e9400c1221100180380e1000900d03510072100103c40c00d4020302201000c940b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 542298687 1250 542297437 542297443
    0x1090f050d0b0604111201030c120b0a05041407170705151b0c1005070201030b0901060212071a0405251802090d06050a06080106080705060a031808030108032109 71
    0x400010081d15412010615603604c9030481d640c0c00142c1070720282c80b21112042640c15107420301c8103a52010301c40c4000b180f001c110341e200240c910b07040410894161661029a0010b18008009403a007802c4030542d80c00d01002072151900030b0006803c0c0d480c405c52220803d9040110703e9100e030f071141401d00c1d2641e0240480a040d6508901e034a5070000005c0740324034074142030150070860164405040442d1040d211b410001a0110702c1c002c0e601001641011814040e040d0002c3c041c41000d6800b0046801d903a00c1c1080c0104a0785e8440d0358070509560325480e410100310380540f0704603203a40000368010310902c0500000309500700000c0c00f000c0490320b030020540141c0b038080c0703448003547d40004040d007d540300d5109441d991a0f001e0010481890200214001001f80c0d0003103842c01c3d402c0c9080001c00301d070009500340c25504020710691a041030b0240640040c6100d40b110300c1e41e10b105000701e102044443c0c01460003440034001455035200d04000704070700109140c1d40c03071007220b002030144103040c6000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 542299937 1250 542298687 542298709
    0x303030411090c040902070b0106080109020a02060a0c0e0a0f0e0906150d14031303050706031103010509130b1806071103030f040302010612050c0907020c240405040c050901090f05 79
    0x50b039064185894141c2c20b103810b8403c030741124022500001e00801040725030040241228445d50380e404143e62202641d0040e4170400c4080401030748000081038002c4e6055004812800c2c2d90b04002c42c50607c1a404a20740c6445540705460021400780c041215083c84107031158000e030402e01130030a514003254904501c6508142490050f40115104410051161308903c48010000c0880303441d810214000d500302c890b140800c541902038800f00080340307070083c020140a106440a420305581c01c01d8184010b07110010102d4180156042c02074001c5503a0b105541e020b040c998400c3c0704010381c1b82c40031602d0904050b00c1c400803c4159000710b15560b102006580d0802d110301440e03140d98995083c00c078054000b0f6084820a07050102d40740b0304000c40081c14011004040d6034401080da074040050f612000c0d0350b0440741c0c10a0116000300d074210000155041c42c021085507140c01c04da101d5001c1412510410310b0900846c6002a1420003503070041e254000610000c62040062400e1102141da00c3c410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 542301187 1250 542299937 542299939
    0x50312090402120405061f1505090d0606030507030c0f0e0c13050a15021b03061801090b0c0c0c0d050c0607030c1424071e0522140303030411 62
    0x40419a100140e07a03a03011650140540c454449441c206424650344503981031b2071449080c0c101411b01009000d40302d41031002c50301e003543c6810080383c00b20401ea60a81c00504190360110703d007851100001c02c11310420015601590060090a04501d0844141460760300050800b80d280c000401c54014100c87d07584c0e01006510009882c0d0710412650000d515054101c180c1c000300c0072a000c0ba101c03085007070310170641255171300300d501c1b01c0b001d00c0b4404480008860301030741503045100080c02ea40c034541030000c90462003000000d0031045544554001460641d0180541500025a08a480810000720340203050880e0003c210640320360740c886e500d00500124030b005120105000c0c0030302d4014804c66200b142c200018103080c01c01141030f65202c004590281e00c603100046400d49188503041c04680c031410070750725410314181e90086400f609010040342d100c06c1010400491840004002c121109400401004071005041c0020b0b28002100040140d00a510903c208000315018420700b10034800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 542302437 1250 542301187 542301223
    0x12030106200a0c1701090c0b0f0c064b1806070509120d08240a0b09190e1f09150302041b140304110d05030a0201112a0c0a0b040312090503 61
    0x1c270307600d10702c49038041c20b00c06810760b024400403c2000c60f40000c2d010440140a000136070b8180c50941c0e03c0003076a91008031141079216008155401c950314010705070b04102484400c0b14400e00811586140c4070701120404001603010038154254104004540c0301442400054204111555001408034038024194441000000c003494000c003902d0038911a8207030041c00500909468107064078003603003c03180381c40c0690b40700c0070700e02d01200e05824580d0a03070303003d03186298a5880d407117282c440702e03003038410590344251985100003a070035454883d8040001c0c014500004031883c500401c0100c9180105140c0c0228850980f042c4040d44104404008034005c0380c05501c80d115800e00c0d0007001c442c20b203440c0c0c20080c802600e0003840340c000301421240c101d950080c400d0b411100403100c410b000350310144105404450034681ea2221203180d00803410340c001c00300c1d8a101d50369000240c8924050340880c80f44100040c0c240300380802c0d00021402c004960420502551030040403030b664684e890016580341d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 542303687 1250 542302437 542302447
    0x3120507090b0a052104050a06020d0623010305010b0a050702011412310b040f0f0206030a090b01050f03030f0c0109060f0e010e12030106200a0c1701090c0b 69
    0x58000d014200242981c2d0401c1e43e150762016030302406507400075140d54030002c0c2d8001c0a9201d01581c0050a116940c024041d140c0901e20350303510000ba41140c0316466815461707020100786568034010144480444464a00c01c0040c0c0000240403a0f8060b00100480e4900308600c400e02c64104044615455081ca4081105a0b444987d55090f0280829a4516201030814006d03140c091101c50101545018030030541c1a5030b01c604032558402500c0c00a007059840302c005008a10410a0031480358040c03406004440715a600103441070348201c406240345a52251210207200c10040e130b450242c0f40645203011280b64000010b41c2e80d0140412101400c040003c01982c081c40a421a0000d9548080284400707030343c407100000074000c280b481e40c0d8958a011086920300200041d905030b1541c5410409285900348030701203540c0d02e281c0c401c15205003005004010b010324108001100c50b406a94040903080c00c0c109000c05d10524420304008503030618030144041120049500300301c42c8900070490f500c23 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 542304937 1250 542303687 542303701
    0x7080423100204090203100b0a171305070e07090509090a080307090801090302100b01051806131d011703040b120a09081b070902120a050a02131401020c0a03031205 72
    0x101c140c0c0180820000e001007800113651280d500a14013a914440d64400c0c240d4980c80c4034600c0d405190041000614010070f0228020000c011a0303030444800254010105100c0c1c407210725000c3d260b44480034404071602000b20150380001c460015044c11508003545062641e081541c800c8039050140035a20b000002c04d5045004036a520000c01840c0001d20120708203087c080c0d180c5201807905900c242c18064001040c2d8400c004075038a6010640d14a0986005d4005202090300000c6e4184804030258001190244a500c80120003c0c0d0b040894030a5604262145035058540c041d11038003a80180000c0c00081c4640c0c0c190780600e087e1a0f5100302d00c0c0d4070801584090000c0300005415048001800c102098550003848074484551088404403641c4603510700491007440010550300545001152400c041e9400042e0854030400025040c880e441c070742030b11504c5140c1c0c844548880300ca60b5032625560180702c107005601c0d040300c504103801e185440140004c0c46050340e440629076184005651 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 542306187 1250 542304937 542304943
    0x5160f06120c020312160914100f05090d06020c070b030903070803100e0f040b0609191e06080303040b0a0510290f0c06391c0605040507080423 63
    0x17603100818080d455030705120703e040b00000750204034200000c1c540d4401180c404000f041d03501d8030480180000603100c0c1020021500103030380218034401c00c80708015240440d0f490481c90aa07450013150700595030101044600d00e00b2085038041450341c0d200703100f0801112004820744030000d4004044907600d03130321044902e1000304150060340840240009000c00e4540c0325030364600c81c1e131248a0305625a203400f42000aa000c08803980c82117030304604c034840c41c4010107070000301895403034490795140c0e0340d0081c002c82c0a0700e01603003250240e640040200030a00c101c02c42c01d0340e04003d808004004c9800c00c1e01c20f0101450300c0f4081e1590305215800d800c089040804c0115944a0b00e600c0c915403500380d01c010740030300c1e41e111010300030503403003054042100b8924500860528140c459041902c0d0210504118040f1800c014031400625083c8032a000804040f0480e00e480000078800040044c101400c00040303a1000d05400100003a40d01000f0010307408941d60074840451040d120724100c41c5071401d43c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 542307437 1250 542306187 542306197
    0x36010b0f1509190b12041a04080f0d0b0a1d0a0203061302070f060f061a0903030301090c021f05040c060e0d0201030e0a020d0b04120c0b0f100504050405160f06120c0203 74
    0x10004d4000514028464601e80510b004611590342107003d1224101051444031007694041d004e141c08000d44061050100024030811407030a0002c1125026036000410f603500c0c83d480301000340d2509145414400407041c05070f0f44600048411421414007002181040f00d01e003500d00c80c81ca500090f85000c0c480100742101c1d45607440201480900d4030b103030000c00540301ea403140b10b041c90700b40541d607061a01407005071405401c01a00a500303580ca88503813500035001c035104404c2907006840c0c40c2a1a40b0900300346155840e440308010032103003068075100075461207540c400e100b000031035080c0155503611414966001c0ea02480e010070b4607000c0400709820440c101c40002d5001c0c42c110204030400142507081d61203603001d04000b000c02001d404080c3c0b02150b4100c40140410740c040e00056115810804094010b11003402003052942c6850100301144e109507016079103544600c0140a0070540c076202c081c0a0400801080ca01a180920162810b800030051400c450344818030310a00c0e42c800c03c1915 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 542308687 1250 542307437 542307449
    0x105060f071b2909040504061b080907060507020f0f0114040314060a05040201120e0c0a17060703023c0a050c011a010836010b0f150919 60
    0x10340c440142d250410750319100e4426191840002600803c100343c0c440040b800141002d0740261410a6440402c4000d010040048464950302e584545642c981c800b14100000243e8030707017000b2401c12030032581c50020f483d4000f4040000401c0302c5401a21001c04000c50081e050b1200c0010080c400b0050b81c451810442003940300c9400314002040c842501d44d00180c0c500031100359011703034603140300120079038008a03400303804180e071040f8503d482c1e001548a48450400f50094840c0000c0950014070b2601c01580000c0c5002800c01e40c1900300d6606100ba290040c03018102140790440c01007045020b034039048070400004102d0644104841030f0600d400468030142c100242c1e40381d074400740242a0703030410030780054590719008801c85c04240c500102d4803441c0050311099400d0f6180d900d03184041d818086210040c0500c081081c80c1d0070851100140803000080021501d41010000d1010710b40f0b002d11624803900701032109110705007081c070490b0800c0c0401c5d16806650025854040043c5241e41d00c54 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 542309937 1250 542308687 542308703
    0x901180f0b09070e01180b04030b0417030a0506010e30101119030e07050603090309120105060f0604031a090f0304080c0111010504020a140102010f11040303090812030105060f07 78
    0x4843d50350b00086407080715100b43c82d401c0c4080b48004031444d008205d4082d02c41050343c01c100600c041034110418940c410f205000ca04902d0000c00448a20b6030000e03504104041d03110010b0061568020311051601e210030f5030200c0e20400c0007640c00150300b03060011001c03251145901046003135414012034000c0300d451401806142c04030b0310134002030391115100c40c0070840f0b240c05811351244203001d41404024600010b00c919070804d0308000090f4005000306500b0300c003c10002060342c85440307051401c560074600001c0e041c60451705200000080a15084c800c00d0100014400140c08a24141605094040c00f890b1580d4010381c0525101050f14030780d800b131201203000282d4610001d081031038800e00313036036071940c4080c103d50882c20f0700d605540081d4005010107047c481344400ca441090300d05014800802d40c241c24a0481d4111081002680c3c401900082d041c814150003820f110002e00c50400100466120b0120103100382c0018010140701c7c0134009240a014040d40c001d07210159004694 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 542311187 1250 542309937 542309941
    0x60a080307080703021c1e0309020d120f0323090705150a020d050a12202a070608010b0904020d0e010c1d1c0213090f110901180f0b09 59
    0x3200202e500300b410100c0051040261580783c08026860000c0c0c03001e02616014202d891641d424800700f08140038042c10035030b882d04280e026995646c4800c8405003d1300480b00402d08203038000300310014459070340c0189410031000160011101c1d000b20740c3c01000c0c19074400e560310ba6040e001c0c03c1c6001588603d82c0403600d03091888040b200c080003400c401c2c80390380072030b02100482001940c0368001c134901e4401040180c005c0c019011907030341010181040c2c0c1b21202c030a488031856a508584c03c180510384c6001c40006200b030340704035030781035000c1586404001070942600d01000185440014010003a903d0001721315061162101c1d0151603103a13040e21414440f0203408842c0a00078450640030200080c15901c3c0b004940ac04020904188500600b070014088038543d4040c2d0705240300d6a089070001e00d1700c1c25031b92100d0f44510402c48005d20030b10107161403e0144c02c00400213094001b03039a101b11000c00041040c901a0a40c9101840c1ca4500108a55802c0312240e0002c14000c0c2e0301503088950002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 542312437 1250 542311187 542311193
    0x1205100c09061818021308012f030424021303141603120f0918150801060501081302010c020a0e060a1406070311031c052418060a080307 60
    0x694040d9032090392090710242c00a0f060800070b80e100d224030180050b51404020031403440e03400400800d1500508011003d40d00c40c0300c9800c594810581e040030000340d0041807442d040b0000d521000040e64800682181026101c005c0e545148440d241c414481822000ca050a03403a011f41e0b03201005c41c150320021944c3c1c0d00b0201c1120030300821001141c0140586481c0101a08002c40b0542e50800b52403040f50180700c0042c0e17640d50100b070603101030000c85500003405403070311742e43c040d155416110003050b44005203a542056038096001103403580d040080520050341e01c28803c940c0007281865543c400601d40c001a103001001000103500082d81140209503460390740345003401f400069070f80600301a60350840030038070703507800222982c8181d0411100c0d02183c41815820303048100d00b0140d9280c00c405a05403a058050070340c03581c05864644007000080c1240c0a0301e9040740020300b5600010704640400500c10501d002d1030301d0038a0005c00302007111501c41d40d910304042c01070401140d0b52440c03642 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 542313687 1250 542312437 542312447
    0x102120c010204051c0f110a05040509010204050f15190302090d05060103110d03020a02091f1202011706031e03040902040b030a0e0c010207121a0c090a05030303060a1205100c 77
    0x1004d11401040d1300000064545c640e071a40c102c1c41500403081154550690391070200109441c1800c583c405101c2c10040360654481c0b18082c05001164001a55a40344c20b0610075a4611400918811040f11300d00344c2e04100d40d1403c840000c81c91482820300c81150101c160000c0c0110800280c01003441c0003010100303e40080c485050b240a040351040d459074050400c0905a010f150007401600488848001800c0072664141c0000c031100390360b580d071108082c5992400c84542c1c0b0030544068111840015540c12180100400070f59908481c464607002d40483d070385142d00480c0c1904801550035007007020310706106881c0608000306041d9a0381e42d039a00c054020350425208400d180b07241200708540d580c00002c40110030001030b00540340b860b1901c0350381c0058030205801901c40d00002c40307003020311103102608a481a00310b40c1d00c036600c5903000800e02001302030719004240290300810501c4810b6a504110008858090300d00103280c4100d464a141000300300e88881c2c02081c200700c21188078603080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 542314937 1250 542313687 542313689
    0x9021902012406110a060c08040311241e070f11010905060601050c100c09090f1e0b06070f060501030b07050a210e0d0305070207050901080705010e0102120c010204 72
    0x9500034400302c114001d144080550032203580755580300100080040342c0c024201280401d41e1003084e10080c0b00e00b52180382c1598185c0080c60001803402c0b0402c02007580008804d40c40c11005001011500302d039840c080300540080841c0794810031410005034903a060b1101e804e0707030101004944a49418200c00144c51072080000c44004079461003020914080c0501c40c5e113481540001c000c14440c0c913001c5c015a5582d004503006021030085c05009402c2588902424000d1005580c40100f0140751280758821542011103500656090000c00301d80e02c0440c03c010142e018007000006212219440002c6035403041400091050b4450098402031009550040c0c1c1260701800d2031824035940c850301101c691141c08800c401040e00011040f90100e00703c0445042c0308811040000c0c40300352040d44130714064140383c018001a446200300300450340d051101070014034003900c54209a504002c129030322806c040c06000d04210800e82c1c542d03410380c4208000d140c0c00c0e610952055850a00d544124043c0d442 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 542316187 1250 542314937 542314987
    0x3080402010c052a31180c0f06080c070f02060306061c02040302030c180403140912011a181f0b07030513151b06020c010c08090601060905010c03180902 67
    0x1200813542d1540360311000000201c0d07220084810302060b051781c0b80d802003900c600c2501041000719441130001d61000400e0001c3c2602d801c144000600c0c0820017000204000c00c45900850140115800251001780c0c40f810241d048030080e071241c0d6000c0106a2034042d803214110b03100c440d40c82000c0345a407268010020b0324001e0b0300340c4421220704810301c29855800b0200c41e40041d00e25001601013485074404081109039000c11341e10704003100000445103205a0700500e2165560362a034200e162200d06901601441507400c09140c210031861003031a01001442070320401c15141c04208003a6181c02c0407409400682c2d182074565090b03080062a1350010b0404080c40c2845040c0401c282203011107911503524541d40f40008045900c00e913803003207440d0b01c6048074900e400384204000c4500a0165118219040d51400b034180351901301c2520306003046e1f100f202030100600b010301441e64003078580c001b405e1705070505540c0c80c4168000746440842c01d40c88581018404610000442c070319003039200f03490304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 542317437 1250 542316187 542316199
    0x2240d0501081005091b040216050105061306050f0108060301060906080a141c030c030b1309051e0d0804051504080d0b04110414040f020309010c02060f0403080402010c052a 76
    0x1414015045500c1076686441c6031b84201b15068914131107001c1030036042c8010b4005800c14030001000c80c10003981e56400c5400781d440d00100300050810129611001070700e460240105440c140104000c00070f150001c0e0304010b0488001500380d2025080318004060300c42042100541d6040d450341c40346600030048404840003505020154070000d20704c42a100751030001d5203070f8014042d0541c01814002c000f90181a1030b22014070040d80e0384882c4140f03610401a01198810451400c1414103000e0080c084085021524039001190001903103034002c0e050b03060144039501e90742400341c9462400a20f1400c00c3e51244208010000b8900140c03009211380c200600c89e51490004220a440301282960f0340b0a00c141704c10045c0c65940a8103180d1500003038400150f190300c030f0700d21030140d910890302c00440740c0d140cbc4200d40c040c5904114080d44044845c072654000e00300360340d000745000005080681000403e40d403040070f10405000040e4001c1030700c4d205083d51028494040340003e031041420748501c0e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 542318687 1250 542317437 542317453
    0x302030615180105090c09181812030903070f0f050303010b19080618070e0402042402070b1c0b06030702061f0308121302030f0601140f0d02240d050108 67
    0x4607204031410f042e070f00010000e0f45185c4d500003800c1c000e40c122440d07095100e2103c0446240001100580134004d100b881c2c42c08485005512070f1502d00480001e5071200c1c030740b007001044007812002c002c2c0c60b01d080d440f0f030703008082c000c1504204a2040c0310f494040e290340030003c000100240d0890003424080c80704500501d81e0078400f0301c02c0d40c094600f00e8040703401c200301d20018014000c00c040015413007540360910a541c9109000803c0881e0444d030404801d410401c81c40c03d010403208442c5581c269101d2008041e52401d224054800d400341c0035480c0c4d841500c00c104414041080c1d00035840d00310001e0210b5445c0e00c5c03d800000e5407000140c60741002d1406000641e04500e544e250102c1c1a01d4000024130301d00b114800003084400c20080040228107141341102006907028040748102c2c0800300000e1620394103004000307019442d000e442134454540c6101d5a422503c0310002e610314150121183e08520800065843c002500080343d440010b40018002100e0304440d0700c0750f8140c138605002c0780c000c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 542319937 1250 542318687 542318719
    0x2301308030c0c0901051c0f062003010504150b0a0507030203040b0f0904050105040e0a0201050918010b04030b0601020c010f0c1b0b0d0e0c0922050709050906090109020609040b0105040302030615 86
    0x90040f031000b41001d911142803101048d80700c000700740c000c3d103d4180068240d052486e802520440c01c803096142410000042006c1c1c501b60155036034024402c1c1e1024503152a1406c503494600c580845201842000b10309142814000d2003520010003124482903984c0c8a0010003080960245c1420341c03080b481c000020440b820f00c1d105140307003000480d00508504403180c0066407207802c50310803658048844c0341d069031030b01e81d0003034400e000b4001c03604000d0b1039505501d8078805965000784803c0c1154408010101103a074041c60f00c48070b201660030034500080e4241026580e000400d00171581c580300c1e0002c0041c3c40c501e440c0081840000d08a810401c000c504d000c55a1501c05072803496034807690700300100ba081d0750186882c41d4101180b511014060b11680d0703070942000032a5100150140c2d48404100103401c0600000307a204200304020412400d103580050700d640505000c40380210341d50110380510fa40200d041703c02440d001000c0b180b451416102480600e00a03070300d050300618940e4422402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 542321187 1250 542319937 542319949
    0x60e04060c0c02060a0509030c04020c010c0807020a0c03030f02031b071706040213021308060702013918030218060f011112030c07061503020102301308030c0c090105 73
    0x240c643c01494a482c14035041c00894494000184865040c09600d07110290790b50b0350b2009105101004c000890805a01440501100d400800d44415500416603540004224910701d2082d170368103007480c00303c260155004a00d54010418048820314042e00c1c5400c008100081c010211601d40c06001a040c8114a40c551039400540c1c00a4204083e140100800180e5401401100c802c00c41110112580c50401a18050094800e0030250b5904c2c0c00e02151180c005045529105c16400b26492180c0148071002c01121540070540c20411710b036032414281040154844015a00141a40001c4d0881100d00042c0c06007a144c40d480b40b424104050b1a5500801c03808204d101142d024000310304c0f10b8102820140d0009201c01d00c0c8200412031200003960905ca80030b180c41c02c8844d2002c40b40c0c00e620029180002102e01194520022003051204094030740244000c050303844a40d58940c1c02c1c4c1d01c030300e110300c0c0d4a03500444042d00010401c00600a000a81c5041400e4103d4000ca8681d07600d40034052 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 542322437 1250 542321187 542321207
    0x3120306080303011202030c03030703030b10030513060903030e07062d020304030b130b010b09030f0309061e130e09070f0b030703051015050a030e150708070c06060e04060c 76
    0x708981051004110007840d00130300040560001d801c1d40ca56100c0c0d407001a0650b8094281240400d80c0c0310161100e5042c0f00c1018140d500d01c50070b0030465030070f101140451140c65064000c00c000d440c0c91182c0101803094001894990b10031040302c00e810345528000c1c01007281059806040d584610940c602c120000380302d12030119103038021b0b52400342136882e1075040300402050280c00c101007030302904c000362404804c5030007005e0151440380c03184060000c050928100081b50581a8414485208aa82da01040341e1501c2c030700001d8001e40c00024500d40c0a50300075000032484072020900c00103505280180b0291041c0c440c10b05a5491545455882c032100c07015008200303021a0500003d43e015000342d0040b07030000c00d00308043c8003c6e43e5076070000145800340c264810025a01141c0410b2f4550113014031600d01032450301511041c1b01001440f44500c3c0c0081082c4104250a000700f11382d40c4c020004820296007001040c480907440d1000180c010700150740445101c2c0c40c24940c031126078419040b0303039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 542323687 1250 542322437 542322449
    0x90b0a0e0c09132013021b06040b010b070201021f06030512030f041515180f051302061c0e0601050f030a0b0f060f18060a081b061c1503120306 63
    0x100f68980c60f0315040861001c10821852008600c0305840240e5101509041240021000541d90b51544003d803e0407041e103100069090740410709020000d5100824281508e244e513042c503458903082d000407442c114181142e117015114160848401c550203030081e00582c2c0c010402ca5440c4110314480d41114481203810300425036160020500103106003141e6a8880c10003000460388090141140301c2c65040c6510003201c2444100d2240d058103100d0088240940000d8010030651030b00d90725020a4000c280c000070f12039a000504030308a81c40144000c44c0cac04c540c0040412000b2000c9a1003a902c03c000e01540344510f08540030010320340340000d4030a030030f03030752110300d002c110b4558601107030200350f000e03001c180c2c0542c00d40450406500c0d2890b42c90203e118003000d01106d4145881813280702c440c0b680054425400c104c0c0c00030a02107142102c04964002601d1143c2c0da0030442c04050488910316042006190500c0d601400f03404640c41d000040e42c0c0a80007030b43e46c0d40003a0301c0c00c0e030440e15107111320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 542324937 1250 542323687 542323711
    0x5010e031612030608030c0607180501141e040806100510020312060a080a1a01051f0509010c060e0a06050a06080a0b0a06260c09040f020f04090b0a0e0c09 68
    0x5400022202c8140442c031a40368200414a0b607100c0c0d030b4282c1150001c041059483c0e00400820400c030b6403040c80086030a600c070f5201ca000900b0400001c140036407032240140c02850010303082801002d40140c007840b54100e41c0d01c00b6142d41d2143c5003607448803c11f0b00e90303030104610408003090301e2038031000403011800c2d96001580307807840003080307240c49100040c2199401a1b9181d00010801014010548598822014134001000c1100f000c4880c2c08103800250003002000601807100018416a041065580c103145856000c8240100c40d180301c0000024601030800c01070384412200000c2c10b504180c070885007444240d8078141c000d8126540707841041416441034039030402140e45029040e4100380d070300d84081181500c0d040b0384000c02144011101541b031500d40c0b00700e0814014059601105002c0f243c00c4040d0078603494501c011924440b01900c92410414682159a41e1780e11600079540c3c030080b03011191400c082c0da0001410f1400d00c0840a0043c40303110102441d040d40a80c0c07141001c0d0400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 542326187 1250 542324937 542324977
    0x105040209130b0411030c04052806050f070507030c080613020a12060b040203090c0102100905030a0e0f090a020d0609110304082d0306150a2c0901030f05010e03 71
    0xa890043c00b8107803100c980003035aa801404170664800000d40c031940c2c0d1541c115a8403881d0405204241951588406005202030b812642207084201004201d4050b0b1500903104c8030210311079600361140c000010100e1054103c0081040f4449000b5000c490749501654815541c9900000324071940441c000e42c07005005006200241d200320000c400c01d4058900090411180000315040360701c10780d0454080d91250852050642c0e0420080100d01340c40ca00034004e26640d56912030b5640902074580003440703801c80002403d43c9800007401e4003100c000700300c10319500302001c0c2c80000794010b0404441581c2441c0380400e46040b40d000760300398052a104c46c2e91441e9280e4558090940110300410805a00740411442c4043d001c1c44d01c202d440000c04204ce540d003403141c01c0050009080c1d0f42590b800c081031200703207040d80e0889a1841c1c0305690b00360f0f04482c0300c2407240e039809040000c81515882202c0340001710601240d03211744071909109500801250406082e03e0fa42c03400303000c2c01c5650340340c0c190b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 542327437 1250 542326187 542326219
    0x17040506150d030e040213090510091b020304151205100608010b0c12160515070305130209070e0103150b0306040b01050f0f07020a0e07030b01020c090108121c091a0105040209 77
    0x10040400001c002c1c000c18689880c0c608c078100341d803001d0761488c11180b0b41c04000c0c40201c0651140d1081d01103100e00e1040110f0105102a4a80c0034503c44c80242003620200d45076600d0081c110094080400281007100746402d00c0d0a0481101078020900054400c50000c00d001d80382100f150325400c00a001080e0414100c5101e607403503800102c0248000103034202d8100026030820030000f44062940f03080d0003038a860b80d001004c41c1c0703004140102d040055000e0902580f900b00304e05400c5243ca14140302042c0d15000140d010341589420507003020814000060f9040011014501809080310305001d0743d400600111001e0051903030342940448104490950621030038000d0030601d00c090500c0c842c0b195900c00100c04000110780f103c0c040b03600e800d101c1d07096603414000c0e030460035000c4400405550600350807a0b41c0e6100f280d110803503a48d0000360301100f989500000800c440e000041888130501d146400241508c0710f0000c0c9900030b0a480000c21213103070500a6078001a000750080001d00840f00f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 542328687 1250 542327437 542327441
    0xe070f0803370f020c0913030c02010e030f0106050a170c10030e06010f03110a06020303010909020604080a03050c0f030427090506070513060305090a1217040506150d030e04 76
    0x58a014a001441ea00c4011040c02c08105024812440d4803405414802248041c0c10036019100181c412074202c0c0400070144103401d11440e12503003516005d03540fa60385100581d0400c8103505c20070380c148600d41102c2009001500700b5804c0e600295070301c0061554900c203400e6902407503683c81d140e580103c4012520750030300d05440307140d242c01480d0210300c0400d082119410218283c002140c00303268010140180b0000c502403840550082c0ca0170341e026450654025241e000602540c0800d03911601440f00703540e81c800c03e0f500034003154405d40d12860703142e1801421039403180d0001e803c0c82c0100c0300c01c0904414080245d9080720302820545050f651500d10012204d400303007101c000d41c1a9030300c5d054070114204018092240742c2c5070322096035841101404550150003a40070808040c205420090011000703c2c2c241485584100c20000c0d500d000c013400e445c104000c1d0000e07481486450300f080b0501900242c62130255484c040c81c2140c6900c4c0d002480204820728a002c0d021400c0d92a580340700e41026 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 542329937 1250 542328687 542328727
    0x501141804050417030702010506010e1c08030a0e0303010b0c06130308070c0303020d050a0b0a1e0e25260c070b1b071a07080105090f1306020a02010e070f0803 70
    0x240d034464400c0101c401c8044441d0020b1b9402070050790356070200300203940c1000303840c4c40070303841240c0034042480405c03042d28507802150030003003400300044003082c0d40101a82105001003841d0068070740340d685031011195690003541e9003064a105410201c0c450740c204d00d0b0866900d54042d48c81510550750324000355031410380002c0c00c8080544c204440c4030b2403042d0b8450749000e10200707480803600001e06010000c01c1c5800c2c0d0440746100700404030396600701c405121181c04840851514003001d13034030100030301a400343c40300a0012681d00341800e509120351128901d4091050b000406014031b00321402c090350054100c03000c85000d80108411000b0130503400686501c1000362203012542520780314401c00a0304180c0c011101d442d00c215284d40901c3e20003030b80f254070403014540100950300d490b00143d1013101c058400354104000401050f002410050000f4a481d0030010656440d0429103009000303080088600215008101001c00c2581041c0c0070341c000c0700c1820005501706034800303070162040303854 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 542331187 1250 542329937 542329943
    0x60910060309020d0b0f040b0a15090b0307050414190204051e120d02030705061e0612010f0c1d09161101090c060c0b07030c17040206130f05011418040504 68
    0x4815007038000340d41550100d104003e000c800000905041c98503c040070030140c0102d8595042200cad2618848481c0b011808032014910082980b428500102e420200c00303400c02d54100d801c140764041100002111240608505014006586600c0c0e200303800f240514041c05a00140b0b03030380400c0503200c003842c42c0710600c039008103425804d24080c03202625003000048284007580010483d103040c0302c4c0034012035600c178540d0844c4000b0030001c5c1c9d00410321404000c118520941984080c00b8070f144096004a1508801082c2041b9451012002611000094895600003104010582480e040c4070741018080d0b1200d0000440305400b03458299224503280c0b194801d290341e1039251344041540d00f88280c0c000e081681741c10100c0381881c282000400401800340c17092504150300400001c0d800b0716560f4510342024001c4520303407158400030f070a03840f60800d80c0307200380c1c1d00241c0428882c05002d07404089502c241c07116150030410443c001824020800b014580042e5040100524106501f15543c443c1c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 542332437 1250 542331187 542331199
    0x20304030e031509010f0e0705060304030c081204121706040f0e01020403061b081303050d0b03010c09140d02010503040b0402030c120115170604060e030d020c031206091006030902 79
    0x11041c00402c0c41c1c075410300320300f4414200301c90038450390310400c1c8900c020700030b81c400040c042042d0760901107640b08014415280500790010024013850700c07420844888950294869640c0d04004c0b02d150b640d171038155000d0b90f48032000d90300f0408482c000d82a82e03404205440070011903556140412006002030004500f1042c0c45408071091032000384000c102845c030a20300050044000311440d48a0104210700c1c0041c026104180a0031b03034411030260b001c41e60306150065450084041c08000344c09260092a09580bd107405c1107640e175000621001510b400d110503030070b0310400104204c640044e40704041c2c04038400300045030214948108150b8802c1c009801c580c000b0301880003080500d51409151314450359900c0d183c1410b40808c0c003c510041010040000b50303801d4010180d902e6002c0a07000400680e40e400011420000610986031403894100c4210340381d004c400d49064a9a010750b4910035041990000104146410100a4040c500d4494100305407410403c2c182d00404990b04280c0e4826 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 542333687 1250 542332437 542332457
    0x180f0604090f020301090b0307030209150303070f1202013804110a050315031b120a140106140901030c031e08040306020d051e06010e120304030305090307230402030403 74
    0x7140e5014158041c1014500181e4942c5044180340854201026603880703030700050f0080025989050403c1d410400303103400b003529131400000207843c600c42e0000041c1075152081c452401c2c0710340140501c14040307035500203021540d5200d00c0346450407240001c0c1c101401d000e21140d0480741c029101049200c6014000196801c110003d40b2010340100740f1010011b1400810842640b47d944840c0b072030250160010300c84c1a0b100015120b480c1040c281403406240c039421010142001000104d903500d80240a0210315064208218068007090049034190350703140300508010b040903022035040380e4110358800b0680b070031903450085401c89140751003074925640e1b10b9400401d404d04020402103104280040e80d490000c0144005d641004007040583d034502c21107000d11a16121304030707610050902c0d1203082c518401c0c0004400818401101030180300115001c400c054005004200c440307011001c03500c68036910102c20346480109102800c80d064010540002c81c10160040c41d0050b01c01c0c2003000e00c507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 542334937 1250 542333687 542333699
    0xa0c0b072402090a1707060804021801140a08060c030109050c1306050a080c16150609090f1a011212051605010c08011a120901090f06050f01060302180f0604 69
    0x91600180300c81507039400034446040b45405148000100346031a000b540014060f26140c5d2101441c6c41004e0070312204500090455540000b400601070504614100c1543c4540d10829004040311416005030303020320f000b00740d0010000321940708020a001051444c0c0c2428006406040080c01c1c545d4124401e00c14030708011407000010010302070f20307603859842c0c0140d01802800540e01034800e054030601000358886403903520364094015a080b0327444c0fa1210f41d41e0300e03600300200402d03030080c0c580030b00d0043d4039401c00c00d0031040044002c2c090760982c940644002d00c0d4540d141001c1c441c510407044001005000241e07001e001110075031860074400c1c01e103c0040ca0500840c1c00824088032241d6450300c0c0124520307048440680505000b103444990420360200c13035441c51040e847e0500591654000182208400350032601d500340c1d00c0b4241000c6568a89070100107490107450010b80000c08030000304099201e882134540000c81080151022255035042c0034503d0704580c4c8854100504010106034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 542336187 1250 542334937 542334983
    0x270a0806040f150b0603042003010c18151205360709020a050a181a0a0305011202060313020f100210050a020a020a0318090c030c020105090a0c0b07 65
    0xc1030340250900c01d1602036a2618000360079140328a6881107180404c0460b2544035001942c1c0d1141d4022410002c0340034002440d00d6001903070555992545c00d00d504030740003e40c000c5522420ba60000106c8040c10f85800403008074403042c0300c1d1200012030001c140e4900d40c0712034000c15040058544100d4030b0795803001c00d482d49201d9070b112a6190120300c0a0001100c10100030050080c580310404608059454a0081043c8207c6002c81c08100047c0e14a0310740350b50a00c021402400f01c501c00b060b5201405c00101000e030410707580100420300d41000001e803510000d0514134207640c006e103080d00e141e840200c030000c1a0507140c016031304004819221003440d02d500140e861498500d8000b0080d00c604200b610003503850003084241c03003c0c014004000a560000398040c4103a90505100440401c00400f1031600b0550703074000c61180c0d041c0818460400d8165024000340794181e0b000340100d54460b4410756443c2c009290040241b82c20100411100150401600e501c51154200004034600711500d240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 542337437 1250 542336187 542336191
    0x408160f03050307110604030806010507051504030207080d02010c0e040f0209040c020705030c01020304180b0127060801060810030605070509063007020d0302030601030b0603070f1202270a0806 85
    0x80382e000000c4c80a542d400c00b5078400448070781d40050440f0f103029034000b008000040c121a050100229041c41080401e000c006410161160485034030324243c10029a01e01140c400d08469006907108200601c1c0706004811518140f51500420104000b09000050811107414035500d9402d1080d005959514054481c0303d10301540140760003402c01d8101410841c41100442c195403041000f0403d045160780c28803011412003400040c140003180051f40d0706200402a6003d107050358801c0342c03409403014040c609a40f990b640e4500941e0300e49405030740800c2c09403030061801d162100100001600ca070070840d1700054038503110381000b0004011440c01d402c04e40c0070b0050039403030465804c2e00c4681c40035040c8064800c41502022401d0901c4040d403902c0800c00c0d400201900000010791690198024880e094005809141d0301e00d4000e1008107040d1810701ea000010b150881c0841460300c050080d034400c1440e0b01d00841503040b0300c0020020508082c06900c0e0881c841910001c2c10071002d0107030f14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 542338687 1250 542337437 542337443
    0x190f090609140307021302091507030512070306180f06182a05040e0c07020d06020d0e0c0609010810080d0c03030c1b0f0501091e02040b04050f0408160f 67
    0x41084240d80c903241e0900308120400d40341d280d00c1484410050f941c3c2c80e140c030b16011607011b80117076148003c60103d1901c07056908406081d0100042540415502c140104030701740403510102c50340c0e15004011010303241a84109102400708070890b1201c0704195102022881c036188000030065503da08040d495003980303c0c41c1181c07907602d014901e40030b018051b00c0180303212844040c41e0000030100014000b80250b010f41500d0300d00920010321800b501c00100c51090307030000c1c040580f965051520070040e510043c0c410b44141d0901d2400080ca00c800640380d02c0b69407000b402c660512002d040115050380c401402038048034170303500002030003070320a002c0c00e400305440d59a01c803000388039401c0150aa0f90180c54400401582958843d0340d40c0092542d120b0742940503e402030025024144030303000d402e4582024024040c1c00c61400d40344025500c02c2c000c490300c241e40c1804514241000c110860f542100c1e80c003104810000064001a00040185103651014950050602041c0c4542d840900014030071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 542339937 1250 542338687 542338691
    0xa051005030f0c041b081303020a1a0603010b030a02032802040614011701030203031b010b040509060108190b1b040f030605180105070903081617031602030a0206190f0906 75
    0x212100f400c241c00f400010b440004040214038040300401030606c10002d0424440c20031035054542014400e00c44030003555040301401840b005c401d80c03c0b5140c50710955426204c0c1d880c2600c1d4113074a04011440111032900100641000c41810f000e000d02202804051800c01004103a1080160742d940700d1000030b070810301940c005001c0150300241030f1101007030710b039100461218010070040c0d900004440c8401400741302d034103001201288440c050200da003049507001c0e041c1001c202401200141040c1212031120031591030341403c40d0019055404507002420344000741c00052400c1002200303500a2080b088680343ca4545c0e69500702d402c1d000700d43c1044511170740356410300c481d01f1002d510ac00c00342002c00f0000c004c46d06007001c029088100500c40101b03c0000880c98100c200b000d40c0c000210b1310b400200c1000e00d50486164100306920444d0070324002014034850355185440002500e2103000c40c0d400130101b60310f07105005000d1802c001e00c0051010744501b10b014200007a8002e82c501c161081c42c0c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 542341187 1250 542339937 542339953
    0xa1e0f08072006010b040e06061804020a03063f050703021507020a06050d0b01110316020f0604060309060e0f07181b212007140d02150609010501080a051005030f 71
    0x10348040d05006423045100e1001032051000c0f4003014819031074000c204443c01a0303100b00d0301c442a0041d003c04c1d804030701ea0f54802c1060304001100e0704029215010710720717028160300c0d62810003610741e11401840501140d001d11010b000505200b582c0c407150307502c00301e4400d0920400d82e001035183e00301030b080040019030200d184a134801c00ba0184443c50b040c01d0a10600b81d103961110660383c1d00440e1070303481c2041d060448103015502c82030034032108014040d1856a1300c607213951000e4041c00c201e101c111065450100f03003414400c000700d10005088000005800c3d09442c00c041d030801c20400200001d41c19945991000454080d155118a0100e941c0c603002e2828268502e2000700480380211014214102112004081c0400c00d440024108102f00c458071210541820b03000c01c001005002d460b4400da6000800e50f680003d41e103111041810b0b02e149a81e40d030b140501c003051038207110b50b1340841c170b0400105e0100391003608510f500981d4130804c1004d096135100002c1c5010807802810425401c5817003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 542342437 1250 542341187 542341199
    0x30303090a0b0c030402131508010f091e050c0108090102090604421d0603100e0903120402090a020c0105070f09141014040b0a1e0f08072006010b04 65
    0x28041e0350168202505074211718003500070032809180d100760900d80542d01c40d0240c1d40180010340d00030140c8640c10082000e8001d01c20100005e1143c00410707984000c11210100712002c4100100010350fa0003005040b030810480c00544d0141805400319040755028001c0d03171002e40303550018000420b6080301c0c00c403005160510b09200d054401d08407001c8450300442012440422040f8540c010b04c580c81d101e607105000114446403001d18501e1284c0c0f00c200042400316a420302c0f40c119094038600c1d107040d405600c40d40f808656912601c29020828000310000034050316002c50b40329445121803038050303e0131500c0035585003110302c1281d0394800b01d5039210300c0019003640400302a010304010381807070711000030800004000301465441c1c541040036001c05500780307003085815100240440c0d0785140e2100d240f20303406043c500c2410744401000c01c0c1520780b80d442c10320407009228110240d484d41c425540b1050802c690390b0508032000e803a40300d10709105025403401000028020300d06140e100b92928180b41c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 542343687 1250 542342437 542342453
    0x3120c0711040e060414030f070510110c1207030e060c06091027230c040f020301060f120213030506060f120d0507061509020d0f050709051905030303090a 68
    0x41180707801a850710a0710558401c0001350325410640103000b5001000000c1c14291840c451100099413440d00070a255042113400100e002100350410002d212101c2d41480c59191030145010240e800c1c4c0c06500d103110030b07a219000800c3d14502916000e00060741c150080750b4198807400c0d00c524164002c00421208420901c004d5a800045241c240400003101c0001c020507000407480800f004505ca00710010000390340d91045c1003e0300f0040c0c010010500c0e00140e42c880902d00c00d01c2d400fa0b410103030828218400c501c2200d060341e400ea02e6042c0d140c50b003c1011201d01624080003400f041c0e0030000644a258125045002588920018001480c0000c00c0c4a40104581d450358001e00840d659004600000315000101c060301d40382c45502c0d0341c0b003420a0000303015101c00c0f105006071500c001082c031401d2a001880c2c1041107a406000d00300303800b9120421250101c074000006260148180120320346017075000303a03440300c80250102058441c800a4199801500c1c0c000540c0d02680d044000c215440f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 542344937 1250 542343687 542343713
    0x30506042a0303050d0f1401030302151b090d0c0b07020a09020406050306270711060709060504090b0604230915031f150608090c031c08040503120c07 66
    0xd500c031032440410300020400715441400020244400410700020072030701c90b801010b989803413480901c0500c0004400d900410801e000aa00500070a800c3d40c80105a010601c0c2c02034081c1080340075401e180d038416155503002941b00130782c0040c519010b9000b0400c5a4a1440039104a80c0200e40d02c2c038840c0b040041c106002d501c5041102d0042c8810000150404c058076403100d07080e514400280809040803500b40545408101108410f2007170003101d5034059044103100f901c400407078001c0d4590751001e40d0000d0301d500c03500000030000c010500c205201a044424080d801401a600386a140d00d15002d00d0485004402c2d513101d999601c180d03051070120310b01608440745440e003694210109020a840d15008503e5a41950160307185942081456108010680800030300a01150301e4640c01030002d9410380b0000081d02c22030300000c0003482d01240c5800d0041d03075005520380c842000c080035102144010025101d41c04107020141e06140d59000c1240b0030318207140b40079070f114401e2502d145c25a541d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 542346187 1250 542344937 542344973
    0x1b03020a230a150b0a15031e051014030312040219081f0c08090a020118080f010c0306050102190b0406060b03090106030203010f1a130b040906060f150203120c0d020403050604 77
    0x5040b4042240301b45e0030765500401e0390245408101e8843c0c3d0315841c0c1c2a84422803100030640d1034501000740040007440c104055440c2d001c1302d40d85e450015400c041d5280561603042c80c895403c0c201140062504012803145201d8555014030b0946d42d40d11114100541012080c80c1014548d91500c25407140e4447d2040240d514108201c030781c00c01c1d078503103941d401001034000e041c0039041c4880415000340d103a07480028a80c060840d610365580c8075a840c041d02d0f1280d000c3d00801d0809802240179030001c110a558030485079500c40b00c45505441d6080d0302c1402401c1600c0c05981c0c1d03900407401c0c103a1100103603c50740c624070010075080d2445c4141801c4907143d0721001001441c15801502c10007481003515104071084810448680b02c64400800902c503d100c03131544a45400d4a07282000f041d03811000860300ba100c0380d80303502c07a5100781c900071001024101c0380050f0800c1041b0400c080c440702210390803a410001c50307030400c0150a0100100d83c081c0d003041e50a0751003607003048100036140c4816200306d68 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 542347437 1250 542346187 542346199
    0x801060f06030c090e040f0c0509090c090421080f090303010605040510120203130209090c010203121f0b071209062a02190302011b03020a230a150b 65
    0x4684219140c0c51945030289204040e107a1607040032540c4038140381805000104054000c500307151802840401c480ca00889420034486000203041c03403c15400e034421921880a0402c5524044c20010403110051088488400400f40103160114134241a2443e555503100c0d10400c0c28006001001c44100620703078820303540104010310045500c0015502180c50566225842240300350003aa13240c0ca2004906100620201c00c10002030b01040000a109009403240e450517152074410715291440c40d00000d025a00806c00151210340001c54554041003069000c0007004106c0303400e001c2450194400c0482c0c2c0804644601440808581000d0403100c605000342002d1808502901e240340c0c0c0700e41407107010070300000104072000440d20740489941c028004030682007188401d803800005404142d00160600108881036450f45408602280c0c054009109680c065910746101100002d000e080340003024084000c02c0c541000000703c442d2140140c0401e200e40040d0791000c031170146189a104039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 542348687 1250 542347437 542347439
    0x203040314130501050f1c0f06061b14100e03070201030615090e100f08030a170c090409030516110301110702090a0209031c03021801050f03070e131a0a080106 70
    0x4400078441c0c4086072000c5c03c00e00d4031240380407800d40240c040c144038840c03001c60040c03120103010791640c46080c8208518401300036840d214442181c0003006103680f030400f901280e0081d00480c118401c20794410f5107100845070607940d241c1078034003903400c14011b400c0c42e41d001043c0b0408560b0507018080240484103002158000f00c001c0c01440d0f00308501c0b4401e11130380d503500880c220b020055001009441c5100044034002d6540b00415900d5020440e202c0015003039080d91701030344000000c400e000e904c0380440582002107038003c201c01050001c000310180308042000c00074501e01440000b0055018415500c1214a00d40a240c2034071848904585c8a034820440d9a005a030b80c60002d07900161001001070300c880350a80800d01d400e8036041c950100f81c50f0a240d00300615419002800500c041803644e0820444100040d241b501035403c100703002550520010744880c0c880d2824000c5100014502103501c8103510b00c1404485007901880c13105ca03100324401089080c201110b5000700a80d0000304121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 542349937 1250 542348687 542348707
    0x30114100219030509030f070e1e070e0a05040f0f0f05010501120b150f0a020706020102031512011103150306013f050313080c0103090c120303110403060203040314 72
    0x1920542e00001400000c1c0c0a601007490300c100241c2c0d0603040041c08441b007402842c10195a41e00180c454070600b001c0708000203070b540c05941080004942904070a046a4545180c20707030368034002281441d004141c620000400b1760b540c2c040c0403400020b0810004415100ca00000282c0307040903442421503062600402c26030740d101001c2209201d0781072001070a042c8000c0001c1c502c044c2c40380c0c20041d203540803c10b950020803440003040252080d0302181c071025603030102a07080c1e000803100c00c1d80104041c0c2d10114642064059030594422440c000100041041c010000503041926090307407030003904906101300c0c11b0800c00c480c05400c20100d8004100c10440701c1640703040030b5540f641c0040300001c01a4a1001050507a40d1601d540036041d0703526a141048803210101492007178164a20561141a2280d4044d224030952990070080642005003000395a521030b00740d100c1c00b18101640c0d07004020b058a10710010340080d6209450250b60381c1428240180318810030f0308132181d200c504018416032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 542351187 1250 542349937 542349943
    0x1805030a030b2d0102070602070e060d060f050414010f02180d08120a0209041b08010311130e0f06010501170a0504081213030f090b1b210301141002 65
    0x50300064900400c80b1007030800410038224801c8040e01100446101100c070050f4000d0111803c00002e07401c4450b0170b40d0b50142241d40b01003512034100d41d0360100380492268102421046000c1d8010003011600a0003290a44115102140d0564000344841400b070074004080c0208034038959400303400d604000168400320481c0c0711094019102d000c86c003c0c45c40401522106490300503208400540292401440c404069448074030540c0c404c13450300e800c211440f03c40b603604c807520b6600c0381d44207d05682565121070b805246810350b45d9001804004500004045008101208084c0b00240950442e1415281d10700001a003009043c8000c1900a000c80c904100c541503200d01c19060100740c0e03803100c1c2030059017845180307140403107003500c9000c1124544001801c461a00d03c01c1c3d07500c0d41c1c144a44041141c411055025a1545440c00c000c1450f591540c0000345031944800c405441010300c240000c21207082101c0d1043d01ca1400c081b00410200104081c0300e20a21000d48101d115801990030083d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 542352437 1250 542351187 542351197
    0x801020a0e270a06050301060b03010b0a030507032d0509030903100b040f1a0a0506211009090c06030f060e0121020901080109110a0e0426030112020103180503 70
    0x1004a0740d1004890588a5a103607103402c46031035030300844883c00c1490729280504024020316010358207000d00065404001d00880e8103ca000c07403441814151402802c80c094040907100d00c04154075034469941c010000103603083c07145510b210300311070040b04160504c10344074010815031481c2c105002c02c40c02e58501240e9000c0c4c8070000d180008481c020f0400003070040a1080314034412504d0038402905c071050f130b19000107030b03044c0403507182c0402035803082044690b10900b5545c0c1540c40e815034410641c810303442c4607590010312086035591180d0300d0720100e2040f18210318003996001c42902003000381c650584a40340e41c220052800740a07580c2026425500008103204c0c0c0b10302060a50300043d541c0401048900d0059401400214a135946142d445e010303200301c4405850382c03000482c01c040b07146011070714401151507103046402c85035a2a29440b000d404200c86415004600303000d0a83d041134130030000c40c003801c40000d80080e00700300350000404603401c03031104944607a4054040307400b081001043d11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 542353687 1250 542352437 542352439
    0x2119030e041b05030405030d18030e090420221506020303040f1203020912100c08131205190f110114180c0a030807031e050301090b21060901060801020a0e 68
    0xa44c0e25215894280d00d140306182e2580e141c107240001d0241e159410720610280b49020f40d846007000c211942c1000310041c8259401000748480d598002c42c18444184421042900182101e0400b1000d4040d6010104494050312440740c2e100820071a203540e200d203000140c5194401541103180c503035602640c1d240417080182081d403881c002c0303011140c0f082d01283e0180d0381c0609030502007a03850080d0ba03500c83c0300c0486895203504103021821050700c601c0c3c4080c40352000448039003020b80b260301c80c2c10207548948100d4003080b10400036020041801e02000c0642c0429a41c3e0000d1064006401000b802d0b0b01c02d2555100d034146404100b4059088403c181c00c0003524031909890214649844d161a881440c4250404218400001030129440c0941810342c02a100c81c800b00717804100e2481d505c240840f10f900403c40030702c014003100b1603e6100980310354000d40140c2d403104846000c04010744092a07041100d91002c02007211410b801c0c080c031030082c4021002541803405402014205c4000d041d0b82c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 542354937 1250 542353687 542353697
    0x4030803130c03020d050615060f0f0c0a1e021014030412021e0c030d09060909051f17100209010f080a0f021909080303010e0103022119030e041b 64
    0x1d212020b0000802107600400b04404040b0320b1034180c2e1140000c859203005060310b06002c8005007032101c1111354968001403c0303842e12160700304001d03850308005190802c81c4500e040840c0056060b16a13801545020505444e2120b07092040000c10101e56a140302088403010540901214000580b41c109500c0600c0304100d280e0034804901c0d082d41e0204200d0f00c2990b60030340488052000c911020f000206406440d030000780c00340c0540d8003180e544142c00008039820420014a0728941c021a0400b400c0c0203c8500700b180c0540260140d0740c541c214122031008900300e801000700400c400c841c1c00c5480442541450150307400a4900a100d014031000e1140700c800080011a41e035000c50001850302400315103420300000001c0c5540710407011440820320540c80410f40c0342d40041640e0403a0180e0080700c0c3c0f2a802d66081c0038207604101d0513040b540d1f080d034080f88158801408425602e0743c1c0c00c0320030800000f880c01d000307014a0090348418015442c1042056406860340c0e0302c005c050700a8289 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 542356187 1250 542354937 542354971
    0x3060f110f0a030e030a0e011e170903090d0b071818020d0b030303010e0906070903050615060d050a02030601140f070602132705012403150302090f0a1104030803 71
    0x41e0f01802c00c9100072a03081c003000400055180d005580909441001e81c0c0c0d00100c800305140c1e50b4070542150346414041400300320030210f18954410450341c0240c0c6a01036034200b02003107000c51803200001c101150601007000410103d1548030001c8006820700306180c10907d46410092a01c080c44000100440d5800060041039098180c12442a4800140449a0f0781da0354a10643c0800015500c154090040d1000714035014400c14614042c0c94001c03028011603241d0801100c24003c0610701581c02c90018807403070018501506c5564400c040340302c40135940e454002d00040401c0080b1079400b0444100f4054000120b112205440308141d0169005a68401c0202c0c0503141c048190b0203003065403854131255002101c44541c50220315001141030100780d0329590086642520051851850805482c082031190700c43c5d004000807201420401242545940204801f55070481c1c88a200c260888107014807c402441012000030000302c0f02400c00341599212040c504c40a0300001401c0d401c40301c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 542357437 1250 542356187 542356207
    0x60f0f09070e090c070c0501080f0f0411060a1205070903170904060b03090705090a0513240c081e070917010204180504051b100c110907050403060f110f 67
    0x403180e0640400030520020f52400d05602c072250b5000100c1102c058a026800050070b5009104042c0160008031700a01595520200c0c10001d4400800503902c041b26140e16512a84034040184070b0a00181c0d02d0380d5040340d00c0c0100c41d06490000c0c00e100104250700104001042440f9500603c0040d90900709680d684c1001c001400381c060390708200612203000061041d030b03440008968003103500944104005540d0300442c0b0701112802ca91807600f00c5080c1030440e0008490340c1c0100c444114684015074607048a80e60001221080030004011558180c00d00440103c01801c440d8281008640b4400500d002c5c103000741104d900c0c1c070581c041540405460b034207a030700a405480107000b0317482c1078542481210035000060b160580b0140d0b003c0c010082c0e880040d481840c038401502d40003404000000c8811201116a42c1c03c01d00199190b01c0307200c0c1c0782040b56540311021800740718541d48040c0c0311400c0d42800000c440c014610788001c0c624000d01442556000744c00c0da03090061070310215845002c118 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 542358687 1250 542357437 542357447
    0x618030e1f050c031b060a05060a230d1b060e0d050d2010020a08090a0c12050109020d1b170703060c0302070506040c0f080c0904020d03020a0c0602010212060f0f0907 73
    0x3d9841c64285c1040e04d10741000200250300d500c5608086810300590702e0384402d0080e0b5580b6400380c3c009941120b21a242c0300c103a00d2054403424200548426498586501c40400c03101090311600e50086070340e5000c01619501034040c5076580000c6401b0304090f4040e5807081d13a10310000c0c604009003d00021840303080c1001454a01e45140c110040c2ca030000c929211010003548403000c038070007240e0341801007116402e00003020b12500364403040310b42c045401d04050021790300c9a45c1301250f9641d2170f18561401620b40300c175000791151082c1511040c24142c09400600500c82e508402d0b160501400350007000600007401204a98000d070000420103440c1000720017a00c1103e170058118800c010030300080100c02508a0200c42c074114484034610f0300c03103040b00c1d01c6c0c2e40e400219136071240840009c0707405445c200c5010154075210f80101ca50601e4503507030b0000e0b01b0085074442800340c2d501044800b00302410ba04115841001121440d0803140d118000805956003040100c3c094011800040c044038054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 542359937 1250 542358687 542358697
    0x302090c0c030f04051e030a0b10030206040306090201080606030f04030806130219030b0a030201090512010e0d03050a0b120a120e060c0709060b0f0706180618030e1f050c03 76
    0x40d05590356611180590100da50243c845c05019013440307060140c2d005040618080b0000e4010003912614004d51154083e800c0f01800300c80141080c0788000005aa4080c0104011480b404c00401c1107038140c000500380501c010321183c050345040080203280c917481d00c0250783c4194036052400050700e0f0800401c034881182d00303804400c2c900c0010b560b8261580d0a5141e00b600b2030750b80d01885004402800e1000c010540e22000303010a440b03d4013440340c2c0c40c1c5103507180129184000001031103203c840d0322078609405145c400300402e41c2c8070244602c1c004280203008107150f054a102042181c11501a5076542c2d5461000c4c00384040181911005407041d0b40c40092007800a0100751202041030340b0f141c60b0710840c443c120f103441c074044000840841c00010b981915200410340b5003000281d8070351f0740c003810320310540e09401c40146003080009462842045240e03d482c6105016035903540c50041e181c00c070f0080c1454802d040c07005c4c110f51012403021281548492618003c1d0b1a100c00c802c0140c030f1030141e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 542361187 1250 542359937 542359957
    0x12090c03050a02150a050f2107091a18060a030e0d092405070f0c05040212160305010503031b1f020a0206010f050105040e0603150c0309010c03050609010302090c 71
    0x10060008103011002034800a4a4000c8901d069000c03000905007045118040b0840045030052029071803104040000d080035001401d8010030880b840c40160b904c403c000c4a40c2c0000c550b19a0040c44145050106011210041c9001c5441c02c403990680d024803138085000c441c03244000240700400f00d4440e801407500c0c141d4407422108070a00e1010040c10400a070b004217413500201007080414600c641d190f20b00b4020440e12028035094607504c0e0400c0302084004180d81080286100082a03191440202500d036040290520542040404400ba21080ca0020720405081c540140000c5d6008030032513007100c050301c8560300c90000c141445401d00e03640503402010303440700407491802001b040e00101910b80c0141e00b40c40070f9a803144c000010554150040300d0004100340800e1002481149095800c0f41008048a640301d1075100c0c0b50384410300c2190340b0440c0000110038084040b500340500d1005091604080c0310515200d40451410503051201920030901440070480c2884071404541a11034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 542362437 1250 542361187 542361203
    0x70807020d03081506070c06050304051c0e10020a05300c0105060109050307080a020108101806060e03070e37060e07141e090a0303020114010e010e01061209 69
    0x1405082c0078042040803039518039000d0352106806950b00c1c00a080300c49250340954145c0c441810b000c4111216000280200d07000d20070f00c10103043c10140000c14610003d019035481c600d0711406d009010410408400e00400d55012a00760710000c6c0020440c00302d178600351a80d0321442d00c121181d803e00b1130040c41440034204000540b50f1132464040d04018842c502c00e0303c482607903550765020702d03a40d074400d441a0000c0e50000c14408005610403094a40c011001045203181c1d40d403205400a008030f0001d4420340700d00d5407240c0030080c1c5030b008680c6000d4410304502400b222842d0090800400c500100521400c40305104003990300030302c010b04008030402c401c00310078072450226000c00061046000b00c003002c1c158500092a0b07240f08105510302d07101e07440915400c0c842004d98603400c2e07018000401c05000c1c000d001c904215160408440000c502940c004505071030760384415150400c06800c0707801d04030040c1005000e003c00d05a16241141e103a40b411525652207803032a400240002000203040320 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 542363687 1250 542362437 542362459
    0x1707020c190302090f100e0c070b01120501050f070f050708040e190f11090409020103060b22080604020d14100f0e1c09120f0c17070b0414040207080702 67
    0x7503024111000e0700d10a88030b0140781d440750105110443e0701284c1c000740086490700140050f03000401401d8004450b1520345091200660310b05a02120907000300305c080c40300301c3c10030050010900405411083c045100e40d66420000b4000f410041018042c40501030f000460004028082c000c40e0003d000d0a00c070b00c00181010308a2510030105441a99413030b07414510400c0c081f103501e1164903c01c1c108050124a0080c100c002c1c00003a2031030203000e90605544040000f203071607546004180641c007520f5280a0059840c01c003064403e5550013444a40d4841d40070000140c80d05200400e429801c6888005c9583c00c074102d07a40340281c1c2c100c9485101d8101081103851608ae5041040015100400d5521300c0000c420344807100d200c000458800101903103010802e00e020f048045202034000c841e0b000058080f0317212200d00004a40c03000c140f1031621603451348803180c14402c410107049481d0070325103490724080080304105118902584070f1a400910403003042500d804a40069074007070a486989 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 542364937 1250 542363687 542363719
    0x621030c0706200102090306010501110a0b07080a0c0804170715090f0624180f050c03012103020d080c0714060403030c05042108090310150905071707020c 68
    0x7111074125079401143c500305a000800103000351000503074060001c0031241e1070b03e80111101c0d00c8009808000d40078940000004c11158072950348940102d40f10b24026003400b02d07584007110012841e1004100d514020710000504078500d81e0030105046c1092a00d66043d1704215295800051410205601c0c110300d0404114150030b44541d028050002040f80031204440c2400703100105100007200503030401e0500c00700082c40064241c103201900e00007004100d001002c0122042551221401d4002000402591070020740030900c58003483c039600521a15550045d55802403002001c050001c007400141da00b0001e40151803440b130700491303800102503c000d04d0a84580c000d55040d0006070a114400401c1c9029008450441c0e1a90710140ca002c2000c2e4011018a0303010f034022114040c040198401d1a9003c101d0001d4441c1014000035845031010b40c0c95002d000141d01890009041a00b0000d0150f00800c0c070080c2a841c81800080f942d035000e0080342444401340720150b218001060702424 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 542366187 1250 542364937 542364947
    0x1401080a0303050f0c07151b1205010801090b0c0a18061d060405031905012a0801140904060e211b01270311030a081e0621030c0706 58
    0x80c0c40c042c0d1010007040d180c070810b111203143e0440c3e00d5403014408020081c00181d0b90f050007017450b00315000008402a1040c2815400340c0e410070340304000f13a916401008451301c58800c540c0140713090b0008010031002070f51160201c0710700030202d00418802080d02e14031720740500651280041e40d5900d030301400751110707030260103683c1289a160161241065510710790510fa000c4070181c60380103005000c13500844014000c82000181c0c00c9a955482d2400e140e90310481320340800302d85c070402d03500c810752014042e801441c06d40c0590101e40708244580b8104600c0d00c0d03a810194110307401c000c020921080d018270103460090706d00b000030104510010301c81e400940715030151042a0301c419609000d00c4900203001e098a0088403844080d448643d40b0001c585031151802c003280b03129048c40b09042816656403411500302c0d80441e00460200420401d41c41c0b85224100110b80c10800a8920f90a01d20040b9031461414a0045403122000d0030141d540c00042064402820030f580461301d015480d1400104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 542367437 1250 542366187 542366203
    0x1502030a0e01053402030d0c0207030512071509061b050a02010c0504150f0c080c1b0105191d040501030609030e03071413060801180209150a050f04140108 68
    0xc07652821000c14030007000c403502c008480007001c3c9146051400f1020a001e00c2094040d480c2c154402000b40210044c040c2c0a481b42c064860b4000c0e00c613551071402d140b03080291361040400c0004003008201e0000d042101d00880107c544c140000d01003203903103004401031007514484c0b00115201c8201024550f4800014a440616a402441a4038030f200c0240c0c0d07640254055000320301c1c01d07030440e10002880750300055400c1305e0a10305503000b0f4840b500c44a5056202047c480350715003048141201010050003c074111030002e1810928010900d95132004a101d02000390042181c0c40c814901c40c5811200140c80b4000020301c108a65656480d03da0000c00b4882030407404141c1724029000c0510300812a14101d070726103004448c85105001c100701141995044d2030300b1980d5210300c0480c070f003c070034440c141e00001d00324848000d10905004114844200421210383c08411840328811520746a50800c1203881c140e491188205210000601400d00c010350300f5545803203000001b0781c600c00019440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 542368687 1250 542367437 542367461
    0xd05060a0917090102030d021303020d060615050c0c0d052a03010b040c05030406050c0f0307021b0f0102191104020a0503070e03060105010e060319020d200a0c08071502030a 76
    0x601000b0300640800943d0040c902c00a0150b0411b200c0f003851080c460300101880060a0724068620b9100d0380005c052a200c014140c80d1650317101800c2c0452180c2d0251850445402d00b0b00c81d09128103503030510741c0e80d907091041900504a03100028100842048908242143c00d464402009920310b00c5d5401c0c00e08029205119600342190103103582000e1044028030151640c906d0318540d039684400000e0400a0003506101d6000c00840c0d000c001079501943c050503440e400360500c0b807080c243e02d040b00e44c5407004062068243d0400300d12580e8000074400034005246801700240e003102e0a201c45005a0051104c0c2c12500010340f1918660340400210311a6150b51124412540712100b455500c0300240501408920600041c803518a41203001c3d590000d00c07800c4074080c81c020255114113a07001010704241c2c0c00e0300c81000d006008011681202c0c0a020103c03024100225900700500450161402401c0d0080c001180c6060100000d180743d240c00c1c0c86c2200350755034102048104018400b8074011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 542369937 1250 542368687 542368703
    0x10291611060a0c020907020a1703010e0609010b030a0c0905030106060201050103021809030a08091e0c010210020f031f030b070e130e0c040203060307031a070f0912110d05060a09 78
    0x84003545040d406a4680e50440c0e914880b400c40306034248092194054281c10031b51207031103502030004490141d21000e9081b00c982c12a00e80d490000a442c41c490040e060b00d02c2281c156005100740c403c1c01c0160b80d4400030585021038a240010010303551483e40c1e810041d015401c1c00804903450b901500039604881c420b0302e40c180101e51600e221640001c007690380c045d05400030000e40414038404d00c180c68202b441c050035150f4001d9503503603120010038003860750081d80e00882e024540c55038041c002040314481122056140500c00100041c070340c8402881852081e200f42030302d1120124022052000e0740d03010a0740500d5081402000d400d1804166055100e403c1c20200e01030701c001240031310380204c2e81c042c00401e0441ca000041001942004040c950148524400000403070310b41811040a01d0b0442c00320440385c103100300000e11901c0e41c4d80040091004240041100c00542140b44403081e8214042d10300b812036100010b0001980454081c06c5403003000d042c0462000d203a071004000038071507400c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 542371187 1250 542369937 542369963
    0xf080d09060804120e18090a0312020c03030414070509100905061512040618030323070c030f0207170d020d02010b0f01050f04030b07050a020c030105102916 69
    0x4102e8144508a500424a0071241d10b07140c2200e00030001c0c996000c1e801451048182c0b003080400c0304450003140e000da6103a00044200051582041ea02c0c0d4000c40c03052010340c5401821008285e80f84400340c401000d03035210108600a0b500203005060141900511090f4581005d150800d450384a500411107011710300303404038401c0d1034480818520950503404c19030404080c007c0743d01441c440144107441047c4c071001400e1000c0b030400840344160b44030b034500081050b07005052141009040340280501c01a802c00d109086d500031100003000c942c107280070501040b00c035030101c0c2070040c16485030700034411441c0008107000012030856082d15442e03007140c4408803c01030490980c0c0d210403640313802080041d08060715500c5800140100d050300300a86280c15600d0350b510030701400880e003004c0091030108885010513414454046c444008500034002410184400680806240303d184111842c0c2411000c81540260200c00c01620342d1030010f072110505490b1101e00900410100d8603008480c0c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 542372437 1250 542371187 542371199
    0x71205062409190f020d061d0907030f080f0403210c0305030c0c0c0a0b030f10030302100207030e0d030801050a08060906070522030828020c04150f080d09 68
    0x1001e00000000101008031648a010050700c4540c0341c12800e0418a81301c010100510600c3c0c002402c128000c403000140d024584202c03520171910b007d902e0080c0c41e03108014840348140c00940001902d8004410b0154820249802daa4500c910420f1114050011030300200380070404081082030800140300e002180a041e10440700c080c1c180310001e011540900124500700c58031030140020280c03082c111030108548800050100070154002c1c1403022000080041c2c201985141d140c004414111040e50f0f81d04503540a51680b075a4040040c0003980821584181440741c2d5000400c00340207011010703c428107080c018103845090003554040d2148400000c1c0030800000c0b400c2c402c8030140c029010356191040b044819a1105030101304415440041c0c00020102c040e98400962094a556584042e180300c561068015500002150120400d04105031900819100e286140c01c440002e4011090301c42c0c0289a8090b0b000100f00091000010a031000005004405401251a03400000c0e0785c81c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 542373687 1250 542372437 542372491
    0x30b04230307020a090b130e100c021507030522030903050c061e0c0a05070b04080d091d18070305010f0f060303051204060609050c0d0c0e0a140307120506 68
    0xb60003500003000707040402501085a2002e01e4442c3c00810a601c4482c1040303401c030695041d40501807403500440729a0f0179403885840b514138006410700251195410f0190720300b40c0230100600c14414541c0f0382c4001408071028010100c0840021b2030324000d45201030600400024441c0000c480b10300c100503030b240c59441d04000382d425001c1c1c518040f04407691002030315221038000000c1e8a2082c030071400d5038000030340240700800c0500221000d0320f84482c07600e03c206180c80045110b01052106080d01484902818030791801c0050f00040311410320746503007a088401041d00e40310205240105c031004820070038103401250301610250814000c006a003c0d000003261040c0c480140440d00c10818801000d02032100a603010f4054140054050765039602102a40c20403640c44111560000e0101c21910b060301c41c00812010700d00d003100340e4000000110700504028025003840c0d49040d24092602e41d001c001c0c0c0c0e4003a1082d07803503607141c0440910707142d07998030011781d01d140403c2e00220b40004249024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 542374937 1250 542373687 542373697
    0x3011d0307060b031005011d010501090b0a0c11041e050c040b160c08150712050105060301090b03030403051204180507050d090218071d0102030304020612070207030b042303 76
    0x84055490029640e94900007040400c8480d60140615804d20045504034400c0500030884413207184220101c81c0300c0f040e00c40c2c1058004038107000420f9020721800c007003e02038031410142800c0800340c51449042205030351502d00c49143d0301c107040020360342103041050a020880400801c027807000307466001d1001020b000f41e004013030100ca007d100d031880000c1d0081181d6602c50054004500c419125902a4104007854282980c254910030070300c40101c0e4030001c0740c0501c0c17103040020071407075042c01c00003161480107103d0f0034981500c0f0a494082540c040c01105c009541c071408a0f0012070303c0400560460300984140b0510900040085009811500038244101c240380d0302c00b0710b44107a00d9400d100605004000741d8104404100360000400240e040c903001d1042b6495a6081c0d00035040d601c06c2c001c1d40303106002c0c1150028020300c401038031a0816100f0224540d003280e0001d58940404a141242c1a88047c00580103181800140059520316074040f299030820300c10559580a0007903032ba0710403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 542376187 1250 542374937 542374991
    0x20c010c1407120c06050907150c02030604080a210509240601140d02031e10060507260403080a080a090f110f0301020705010515030604030203030a1802040212060301 73
    0x70030020500090b0a45030b864a01c0d003d1428052099002d42d200c0004481c8200d4508080d580181820b0111203c0082c10740503a810610b494002d458403540881d49604015000420044012540c41c95282c00b07292007034224080c0c01c0e074586011030401115000340005a0316040e441c080da016590308850141145001c3c500e040c14407920584a0500445081312000d104400c483e80900c69180c800380c040c001580501c4890200c0d484004071041e07044040500a0801140c06580890070483c254104080d1840190402c02c80211203114052a44070342c195415907044505000030080200b01da00c2c4054902c0040603500d01320165604058002204c200040141540c92071511315070010b034048101c03c484d40c0000e001030f444804100c3c00b003402e91304410b000b02c0321a51200108010750005003030b074082d021000c40060140381007944000c0e44920010740440403460710340c0b020035031400d000021a88a50741c054000c55555600d03030028000b103032083e6241d0b4421b5003052914501c3d138036040700700030070380305 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 542377437 1250 542376187 542376227
    0xe100c0c1712030405011b0302070c0b04080a021509121509031806090d0606060c1e020f0918150403030509060106050d180b090609100c090909050c04050a020c010c 72
    0x102c20a55030407030b00020811911992603448403c051000c10401042c3d10519440150321200e00d4a010801d400c07040c0c0100c0e442c01028030003080021070025175890010340582b194100d2266601c14207080d80b18074000240c21032040b18800140d440005800e0201c820840181c0000351030f000c13030036038492003200c0785401e40e030301c05034900411894a50000c1c0395140000f04440740742076040d81e81c80e05a43c02c0e0b070300071130201d40821501400d00602c0888102100e10240c0044034039005940060084040c0c09002d40c01651001c0005940c2ca22059003000381841020031150300c0140c15942c4d02c46486c04545c11000203081c040070942185000a200d41038401540301c160400c010b04400c500204006090104241c00c0d40b012b10300401d5a00700054042d4941601400c160710302500d04070310304600c203008040a185802031101c2042da00c900c0042c01e6400351400031038040d9090904510b0207060000199005c3d250030b050003d0204164020004414220000e000180e24181d066070402c4c0c212010a042e65 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 542378687 1250 542377437 542377453
    0x3070201120c200f0601270b0d03140706181e05122217060106020d090e041103030d05060901050f0d0b07031d011a0906180402010e100c0c17 62
    0x940c2030140c003600350842c0d80c1280e00b0f9410800c450703450541c00703910020016050580094548000030782d401f0030501e21000a010341d0f2008000f194400a401c01c01804008400d641e2a6002c020281244d420705d82050082c001f0301c04411910310b5140709280f041301e14000d400b01c181151000c203506906c0d22a08070b80078281041e90700e03000085982c40418250200c828109101214007081e0707010030080c16654101240140446075034034900302043c0c00481c10343d1b10001c40c9004581d8440d2460098541c5002c550300c843d203840ca40070700580034110041d6454000410507030230710700300c5511041c45040b044a04040b2640d030741092180300310364040c0300f90700700b0b2502200ca0013091a42c3c001c280c00520341e240000d43c03100070010010780d62000d48078810311a510380c500443d07681c08490040c1c480c007204071010b002505154000501001c280860403e603160140c0004040d0780c056200c0e01d40341140600006101030107504010640d2001d2002194503a143d2800451111143ea88503200b0b0050b64004100070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 542379937 1250 542378687 542378717
    0xe01050f0d110d02060d11040513020c120c0114010306020c0d0f020a0303020c0703050312041506060903060b010e0603090312090c030307020910080a0b090105071d04020a0504120503070201120c 85
    0x3c09100080c2e0300000e0030071085801e020307184500032030700e418899069140e03030070401002807042d202d000342444d00e401170207580503d01002c42d1413451801040341c0e082d03481c24030000c400d0141c2070221081481c25600f400020501140c0d03002011541c803404152024501012002d6943c05111031111006a00040099001038000d9005100c5440404c040301c050719502d030765007465507100d07030f01080c04074100c007081c8030401060689040c5944480c0806021450518070f00600c5160035110140025131074010300c10340f69009405030070081030003504056403860138000c40c039942c0d480f00794003509403642e210003d1080b00e80485c086090071801806107151400799000c1240404021706003401f070040d4030500180b903000c05c000c0c203625148103000c408141d00c0c1241c01035084030f0000707082005001d1001015407086060742800400e4420850300140c9860780d044040b641e40c011a0445c5040e94800b00c079940a0002c00406000c14900c00d0707a8014141d4100c80810056404d00f42500700400c401131a070b1001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 542381187 1250 542379937 542379949
    0xb040603060302032b2d0c0b011a2a0109030306060e030c0d02041e090606091a01020709020a0309020a03060b03070f180506011b0b01210b060d0218010e01050f0d11 72
    0x140094806aa00700c401b03407103403100f0212940c803032100103d40300864000801400c001c0640c010303e02003003541c2c00d0301010100c07030409100309410004e202102d84201402d081c4051106542002460001c005510062178003400510340d9010b1140030a403a0130300f851075490b0010f4050310305000074003c200b001c1c000d0750910000e0280340c01200d00c48400410001c0540405101d055101c40c080d800101c0d566117400707400707011a26540f000301d804030840c011000d03469800046000031a40342200050751421602c03400c40c02810840c4000b544151100b00020038001e0710f03000424140c0d0210281c4104035641c1d03c81d504805024400c500d00460120000602c841c900c1d0b1100742d01c54018107001405803009040c410000501074001c4940a0a880042c005030603480c08404000032250080b4800c5c48076626107680d0350800402013407246801e8484101151102c070024011072110400e082c44650b182d4446044c200000d000d4180101c030050400481840c1007010101401d4002004e00034035800c18003070040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 542382437 1250 542381187 542381207
    0x7081b100302120408041a090306070c110a1701050a0603020d030c15180c050301021c480309020603010501030902040902101205060d050c060307090b040603060302032b 74
    0x50542c03e000210034480c6031503505106a01c115046965107040c4422101410822071200750100c60a1100c000c3c0c5032400159181c100220f400c00000d008482d103400c2c10b424811503c1140c10501c40d000003c2d0b08185140821044802c0e000240180e94440300c24100707c0da0300b484044d40c40fa030480a018007280c064050030300c03c43c1c05100c42c0c0295540319400030064404048081120740e03000d00040091004041111010340800c41c000d51034003034139007505030701c00c071884080086140e500c01c4091408031095800d0900038144010841c03182103200044945044056402d4004462085a42814500c02e208140d0019030050100c4d0840c0d0034240110300803c500c10b4126002941e51180754050303a980e85030841100d80c00c0d903444c00005042d80d601803e55102500e100e004a0240744c80e040003c1020524034808001516019160365400108840706c1c1440e43c402815240d000601286856040e0000000d82c3e00036000c8440ca1081280380085c8403419211907142c00c0c1405c0420950749200c1e1510340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 542383687 1250 542382437 542382469
    0x905120601300f0506060312040b16140313080c06041a0d06080c0f0d1208060d06050702010b1008160f0e152d121008010515010207081b 60
    0x10800b18060324596100c551602410380d2000d04120050703040100130001240d01140c1a009401c003c8200140350380306009038000c0d000801c001244900103070030540c0212040700e0b0451100d40e40c901d40f032029203443e82c0c060180c0042e0b4141c101008104e1841c0015a154076540183c2114500351a028005194180c0c403100415951810002113403c8846409070b00051311414020340801071600e41007003c10180100d0b41d502984c100070094000c00c0c1d180c01404100202d90902c1410f81e40c44100003012042d080300000c2c02d40e4501428403d81d2541580100c00c00c400940b852281600c2446050320714180886907601110801d0240d82d1a5910031442e41307603e5807840c20020071901e400d4000445130790048001f0b28034000d0110b13900d07100380080ca841000180c010001c4041c00c802103c0b14601034400c800c41c4104e40300c4100b001c40c80e0000c42c1c003510303002040c100c4020031181c00c0c203c8804001c8a81d03900036130f00601c80c5081c00302d540c04010546141d03442c010100300c014040c401c02800302070340c840c540b41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 542384937 1250 542383687 542383739
    0xa08030c0a02271905061009030b0406060308030406090c06050910030902060c10050a0f0b030d0503060a120302030d0b01050301081e10020c031b07030209040f02031006150905120601 80
    0x500d902209080340c00e0301a01e441e0102505120f1144020402c61714014082c3d4840c2100a04106402d40c01c018418180d94104500b071003160340d54280180030741440d81c0020280c0030004108020721074550303c100c00c40d81c0b064000c00e80313441d61450229146e000700000d00d58401c000544002c0403038000d60165241a01c06004981849414a0b195081c003540c83c88203544030391250b08000b1a041d03035218113400e041155000700000320413a0301082c2c0d161042d0301240e060000002c003003589170b41c0d1509034800804400d0b164116040151a000b503c94101010300000d86052035580e0000d0f40c010400c1e0381c1600c0c1418010000344a200b482d09032407410bc680c820b40740703001c0c000101842109500003040344204000046a440310048522041c00520350340e040b20942051000f400180c0e40c00300c1d46a00140c01c80b08104000071140000f0341441c1a02c83e0201d0303100d103030000000b0002403400031808445c499849a444041e510810702032000401105403400b500414018400352115419405100c0c540c5010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 542386187 1250 542384937 542384989
    0x2104060f110903070506040e1909020316151706040f15061e09031502030a020d05010e011d13020607050a170d1b020615040b03060c090a08030c0a02 65
    0xc14100e600e03429100000201c0081ca28015080401502e0020082924490700c2c182c600880d12040e40e00180c03148000403000000055024195005150510f0f001000c0c1d81090002074480c40901d0081d100d00c8204401700200351184034001c440030b1001c00e03100d102202c850307a10441048002c251070100d8080040d91650341c00c1c1c1043c1c48552040c09044182c40c0c1001800081949880108401c500801000112001400003900c08112034000358a1448007589a131a0702152001034000d00002e41d01161514000103085404452207030304843c1500078401d20300d4040700040c031806030200d580703500301eaa40c100600b00504082c0003e00c1d21034041c0040e0343d1000304076a03031213100a8000700000140d030404148814100d600f071141e600c0c2c4800c40d10120144110000000e5100e0600a040342242a011007501181e902c036504100015140141902c95a2030b0250004140750080700c80c031406000d04c000f011600c140c001040341d1070403000e00001e11003010b041d420030100c2c09030080f0317580c0c210b841120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 542387437 1250 542386187 542386211
    0x1303090b130306021605010e030703020a0f02060913060504110a020601050603041a0f19060e04030f020106170105090d020a150f0b041d010b01030b0f01030911121507020102210406 79
    0x2000e8907003117401410309403600c041c506003103007513582e040c138450f605800c104107140c0000d07000580f03c0205980018210303480d00741130000858034010005c2c0c045c1c0011007090303c422030035203030350095055030b5084504013320000c011010b4264000c1c01c5c4810003590208006202c2850403001460f40984180140600706090180203959440142c81c03082c0d40c55201010300110050703191420341200c1400d1400c003c0189403488035412286c0c090005801d1150405080c030400c2c0c03003900481d000d040c43c407001c00310400c248840c1034000c00c02188c000d0028040c4094502c3c1d0a44042202e84500d078002500420680075400d01d80d004000401c201d0002aa50300008555900d40c0d01030310034201c1045907914003000360410003a00355190100700134109880c0c034030b05614596403180103130188002840e0000d02001c9901d00450403440704030110f0b6009201031011254400002841e8881541550a0707140e2074032160400da0a0f405540061015424943e211084403c4004c2c20503038010301641c408114181141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 542388687 1250 542387437 542387441
    0x1b210a030b03190507080c0609060301050f04090204020c0a050717030406050310030f1a0a05090d050a09120b0402100908030702131803050310120b04032601120b1303090b130306 78
    0x42c1041380c50750409041000003c8043c80b40d944a85000d1351820302e01030361040020f546104c1401503074420003c803082005103440fa9030042e00616805081155075020501c1c0059550443c001c0842d00c512403001301140c498101c031010112203400c3c600541c14541007550a98140d04000d03c091400c0701d1070280000804c4103c181070001c03602075100507003030b01c0e601004601d00003402824440d06c0f600381018402210000070f600c220f005400c0ca07049498400403a021035a40803030b0b600c104403900c071090310003041c0300c000a2010b000300e108907000d00c0801003103c1c0070788140d0902d104d07411243d0824041c9001500b02402495004400d14400044114601004a440341600b000c01e400007440441080f5010448640082c044c1a0034014130420302031039910720120406c0104000d00700115001c40204c82c4c41175465801d05412400e05a807519031b103d550700c6d01e0b941142c24007a00e9226610010403101c070700e1007440c520415050f5462804050030904040303030540c00340b0341100800703416040020220300d0074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 542389937 1250 542388687 542388733
    0x60e010c06020d0c03060b0a020d051318050604051e010b09040e060702100c0e090a090809100e010305160512071b0809040606080c18151b210a030b03 66
    0x840c40000745130316850300040480c1c640f81c201c903440b0407040200c941a04d03000215404115014513140b596007800801c0b18000821581c00540b1108244001a03488031940e04032030303c41d46040e40c0811407592032482068104820407400100c10200c040140000003c003002000401c201a001283c2c900404601c03500d8030a044858100507040607600c0143c80019000b01c141000e101d240c40b031040602100003d05804000e01000c1c90283d5414680c0c04100b400800e8944495000b048984020344490f0050400c0c10850b8070305001038a00000640310311201c1c49204481a40359132040d042004407030411812030809800c400a001e10000400301c4038445802c8a403603a84030790180d60300e54100b902440b0a843c400d401010900c1354110811505003001803c3c2c4000c1070328401d0704c16a03840c0d144c001c6001c85200030380c01e848200001403c8442c0740b04240b560030280300c0b90350032107211480024000000c8044081c9808800b48100075a50185210b03401c0f18281d48002070544074a0b0030302451001e00c141c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 542391187 1250 542389937 542389957
    0xc031201080f060129030a090203030a02060f1609031101090f080307020111070b0f07150612120905090a0e070b0a0c1b06050403061107020d0c18020f0301060e010c0602 74
    0x20882d000120040140a443d00414940a113a1404201480c900f5915050b030301d215034041d40f000c000212071840305d0700a03800c51a00502580d03660303509a00c0007500c1d0f010844210013010344010104404044404034547e05401036500c00c3e17065425941c50300c041ea0031070b940b16070400980c0350010900e00d40e6141c03e076004021001c02155503060030b20016100f40030724003680d206034001c9582008141c409504907100c040c0460300c0103070344080034541700b07003001507100c280504540780c400c001c43d00da60100740350002c3c14004c0341c03004000d00d403c12080b5144a21030050310382050f2250040740b1484165005032030108801025154039540b2000d8114003a00840404030006940220900c103108440078000500304801d018110800d0030501d0180403442a0300c00146a540c1d52049040301001003003c0d00c0d2000e40c000c0c10805140c40301e040100300003269000c0d10101e00003010850000703c54a10071550300600810701e45080d68a0010b0644210052099440c14005029489000154140300800c081c0074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 542392437 1250 542391187 542391193
    0x60109020d110c19050708010509030304150209210f0102073005040b0a0e0d23190204020d09120f0305070e0612100b0c010609180210050c03120108 65
    0x51011104107582c07403001c9801d002c800802040190200c08940a0b04000082034020048000342c03400500e400c5841d84410b1440d4600803e011000c90080020f50240b07004000080030703100b10031100c0b01207109a800040c0c0c441046d000c0c95015400810b104a10300c2d075500f0580700d8166200788980d09aa011034012079100208102000d00903041c80f1f90400307850b41c0c010003d501d0400049002d0080d110b103015507040300c080850100d4030548520351140500f18003030000100301c030716490010112003c0e46000118034152852040300ea03200040c2d4501040b002c4480520307d00c00c19002d0100a40c440340741c2c1006035131100340110220390104607103000d4490940e41c8890320510060010210b58001e042c0204110150a07210001e60f03c1d28181c0f00d00c8041c2400082150301c54183c1118070801c107600590000d0408900b2482041040d403100c1c0880d88070803000d000740351a90355803c1c40700c100c482c1700070b6010540340c54610902e0f1055018003203209051085030700e0090398900310035071041d00742e02c902840e43c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 542393687 1250 542392437 542392447
    0x6040504170406170109020c0604030e061b06060307091107021909060b0d0b0a030807080307200a170405060417011103040b1e0910110904090605240307060e0d0506010902 75
    0x40c4c407071210900416400c0011420448042d41d50781d20b880010384090b08219034020340c00341554607201180c5056402c1070703c01c0d01445800800a46416040398071500c80d0051180014042216000f040b02d0b4000030220149012003d5081180c880020503070304649019a64010903154a81e100700310107030803a0180d2030344915040b500c43c001d0f900c81d01d03846401951401d40170800181c1d22004d403904980c1c0b140b8850741340d0356079002c1101d070003500d030104000180e0f541c1e44248031302d1000b244941680c2d004280c44408071747d19682c8948203103d10301c502030b0040400c005c20442c509908004a80806c5001c0c000300b01c40c0b40b10004000c59400a66007600c982c0c25000a00c51780350107034414400800c031180648401440d00080e4291142110f10a1000c82500c80c05101140c0100004588400c28020f00411040b0524205280245001c98a0f8401c0d810034454103204444e03051441e07a600e1000400800300181091401c60301d22250b4051290000300821050f00042c000388032090107012610001030301c130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 542394937 1250 542393687 542393717
    0x61506200307030f030902030f070e0a0b030a1e08270a050d030e060a051605060403020607020f0304140a051e090105010504050a15140301030b0105010f030606050306040504170406 79
    0x2800c080e8040340840d900400c2403000194200340130302000d009074107000540f0281c50011a00701010348a01c03008a0180180c0400e4044284601c0c5010300c003030200c2003006001e414240b50f07844a080710060700c00c48202004112031802c0c00503104a00e0310a03000642401404090402c03c0025082c50980b20343c4210303060001c0c1e080502c82c0200400c02200d011110f0f10403501d000d8480c1803405d000b140200c00000d56603082c60700450803220882d4101c51003601e82c0382c40f81010703915503a040c0c0b4100c005000303400c0030580740741c800664008090410806585400d141105982c1e0341d1401141040e004800044005051340e00c0d042110599541c2c040141540c0c0101000c0220b145d0058002c14103000d0140010300c20340c0ca0700d1000340e0035135011580c0314499040444041d11040840708110303020010000003c0300300001e60100d90304a9200b030700e41070a0100b10380c1d01a0140c40244c000d01d00040d00c1800002c0d01460980c2001d50064080d15028021440300c0e0707e148040c1d445504a1000f00700304601e82e5942c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 542396187 1250 542394937 542394977
    0x315051c0c05120703170a050304060c02010e071806050901031a13020d031101150807050f0402041e14010f0c0b1503030409060f090c02030327012d1505010c061506 72
    0xc400c41d41d1b180c903280504110010748240000381010380b6407582c448000000764001d50000c00303c509184100c45410360303540e100d04105c9000640c108c100a04103400000c0f1410648811816658010000006000b48071a840e2800308010300101501030366880080141c0c40e983c46030020180280d8401c121a1031411059003591070f503c0d945040040c40000401c540f901c08503160099a40448154400308401d1000070068021078104070700341c1a0058602c3d0a51800702c05420446084020f9204401145e40043d240307149034007911404a186d2110140c0001c603d0002e155014074070303140c4c188051090307078003003841d54205400020030165074050601501c07405c0d0240714018030300e0610038481503002c0b0b440292070340001340c484420042c4120749001c1140038101109041100d80c2d00801901813150201c0680e02103940f005801d107070841c480b8103a01005070041020310301c0c01b0211038050902d810f00445218800c0702003661915902c05020070082c41d03a000440c001c1c42140d603407011280d441140486 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 542397437 1250 542396187 542396213
    0x21c12030911030a08030c0a14130503100c080c0702010507050a0c1d010b0a0e03120d05152d0118030b0108070803070b0a05040309090c0f0315051c0c05120703 70
    0x48031341d0001c500240001e13030344802c481d0700c00c0107110f1487d11644100d40c15140d07c2c00f51050816504030124401c5098507022001e5400c40e501102244c240a4040c0d0140d411110715010744000503c0100001d4116410007000340582841890514a03050107500c5480c18401e05480c201c0e024a503a85c400c105c000236120310001050002c0c1c80c151501d515060f02c2901f144101c2c1d40c43e6007802030109042c20f10f5941400303050010214022101c0da9100c468101c4070041c68200c0700700215030342c2d01d40308241d6400e000340341c0d00b011810b610390070131460a5031444100da801010b0002d41006180041c411001e11218080301c015071044600280b01d504182c4036a0070f05505402142d0140c0c020b104200200d0b00c0501d0309030b0807608d41c0c40c00040c180c80e2400c0441c2c4102070b0342c00c5514094180007503c10f40c10307840402c0c01c040341e60540d410408583c9502c0081030014503445210381c011009243e60401c2c0d1029506070702580d21501d00d03a403440b90303580f000c283c04584c213042c0e6a803250840c07034041050200000c02c043c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 542398687 1250 542397437 542397439
    0x3110f0f0f0c010510180c120f060e01060221040501120504021302040806010e130312050c040308040b0a02010506060a05040501140903010501030b011503020310031b21050c040207020d021c12030911 87
    0x200c0f0609240300014203405840742140d648c540c850750103250540072944440040c00d20790100c8112903840f5400a5940d110107006215081d00c0c8003c0780d0038520380403055409448050b920050700341030038000c000c050407000e07100341d07801203c503c1300c1c502481c100e01c018001459950068145985800865084210000d0485101194003507003100060340c4081c0303e07941d101c503440c00043c04e81c440222004043c080e0b60001003e154000a0104d07102c07030103a0190801c60410b038002d00243c0c0d241014003015002c0d01403c0400301d1010b11051255602071f0f0140341aa2844411107800d0a00b4180040c0c2514400c0e40b0503200d064001340140030240a42c0980d2040224a040640c80d6044c4040c00c0000c9881d284400751150b03c0c602082d00a48001c28030500c010301c5040c4001d101199104540410f4200e804801c0380c00d4810030440a042d030034130707000341d030205900103003462040ca6954091041080407155a441100d07000003805002583c0000d06403c12007072640c000130040900c5c07034000c000c0c5c00544141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 542399937 1250 542398687 542398691
    0x1510030b09010c051605030d14060f010f12020d021908010e0f09030301090c1e030c0e030f0705221517010e2508061603110f0f0f0c01051018 62
    0x580d045a40010485520203005440480e00f42034a0802d61f06500a80340e80f01882c60501c107520810030110000c240c041d5004640000b074112074240191090442c03040008045203070f9051030642c00c01c26a001d0001038604202c05860319180c4641c819102a110721000d010030810070040c440c02d21032008480c0d01100c406083c280d54100012a2640c0e030005205111103151940c0203204028855102d01e21030101840c1c510011007640c903c00f03406000404a4040000e003009500141441c0010740d00241c0e145079406030050508044c144200c0c1907400100d100700e03481003000820200f0040c8508002d03a0040e0901251340d5082c040c004960703075003404040303500b0382c1005406000c0f02c0010481540c407101d480c61524800d000e410842e05058403035801207020b0301454041002503404542500d030000d003140ea04104003800014603801c0d0f4058035800a0381c6078011f02c0310b05032034a070910003000f0030142940d00c42c1c2040d00c2a40c0b100c0c2554401c884c0c0e20000089a1010400384445200c0c0603951480c41c1d41c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 542401187 1250 542399937 542399951
    0xe0c041503020a030b1b0423011407050105090f1f0c0509030d030b15040308031f170f011d0a030c030909020406020a0302070801050903120a110f191404060c051510030b0901 76
    0x8903d42045650b2303071541e0421030010022805a000303010000500001c40c1604e038440c000c9007040c81c02400200d488000c603004030a940c1c00400320100740360041d110088095102c05a83c022076000900100306c502050140410450041d540c00708180115a01c02e658040b80800061060105e07482c1d200c03000000a510501013400080c2e242419a070f8000704103807220103040841c1c01c1c3c0c024030100f0355111085900e806125401040c4010490401d803c2c41d01d0020702000940e141d4079440803d50b102c41000c01c0d040300d00c0840001e07218100e40d6a0040c000d00c1c2060090b511a002d10080b0f038003980c00540542c0c840c081c1c3c2c500f00b540500c0a0780c014020140200601d242c4555403075104e11400e5158203101070024009070302e48a580d401007da80c540100842d07200ca0701035907150426441100e4400c5550a41d040c0038100307078815600560311140b280c41d22070030185060801c0d40d410721903400440e80e0303015441049103540c03d50014540300d0702401c0802083e2900e181001ca0841130082c0078100d00783d041041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 542402437 1250 542401187 542401199
    0x4b0306010518030c06040f0f050906030c01050705010b03060a0b0f0a0303020c0d02120f010b0a1505040504050705091504090f02040e04030507031e210e0c041503020a030b1b04 77
    0x1940c07060040700800302c4005000c000040e0401201c0b60b0010741c01a404100400d8030555001e0000680303100c1400c07207031056211410002003c004803030703140e4582c0c0804001c5072554031400161150324440d80002c1050b00c190800281020345c12104a580290780380c01001052400030040000301ca415a40703115445c2c04c54030300a403503002c80e15100e2300400034028502c0454a590500c04142c0d039410055030400600d030b514181c0a0548541020f00c612407405001c07c1440008c0008041c40b9000d480d02d524043c40c01c400d10000c1c15005145400748901441100242d8803011114100c418403a251190369604100000d0704840945541e510110720501c410300401e41d5084981d03800942604010340c031541c403032170b08882c5010500d082c1c1c01245a0841103128072500410050204107400140840080c00a15048102c1303119504908040d0300401d001c40f218101a40041102c0407010045d281c02610303078000c071311480d505030b1080b5002100181000f2442400e460034044981107452094a0710345005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 542403687 1250 542402437 542402447
    0xc08010e100506030f070206010f151d04180b0c04053f0708010b06180405220f050706021903030509100f020c011518024b030601 57
    0x40a601000c940d04000704001980007058a0300400e0014003580d40c03807030044042e007240441520342d00058441c680001c103100d10682500340c1603c419800b030900c05002ca04045803581240c0300080c28660f1001d1450306a1713100d9000e200580e0359240d103071a80d140c0683c030b030182c01d07403000500c4240d520070305001c20300135a070320003410030340f0b4003a0b601404c501e00d19030310b190500b40c00e00d00c1c2045052000040d04620035944c0403507490101d86150000704152a88002485024881c81072802881071f0180ca2012192a00d50702c840e400400740040b9040111030701102800789c04001c0701c1945c40f0000300b4099010004108a8007028000c40d1000e0902440d901c40d100603421943c40000f81403544600015400034810018400e90419a95050080c101c9000c202c0c402544800c0508101e075007409031051120142c0e800c900c04903440c00e80c0d21200700284520402c020340007100c00c4000b00601d40d00c51000f103d0301903c070b0144803c0104440041001c0408a00030f060340d03071401050411740900400440740e03049 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 542404937 1250 542403687 542403689
    0x61202010503150409030f020c04110405060c0f03041e080a1109180703080403150509100c0e150c060708160e030a050706080702100213050402070f061103060f01030c0801 75
    0x20700707240352291034205082030307064000d8420942061409081c81c00b8185d0003850038030f11307040350b800780c94150554000340001e80b880c0004840c0414420041004182003c5004003800302c944030130b42d0b04981104a015007181e02c00d50001410188071154051345111009010000781140c000030100d00d051607840003000411140a284529140c9001400d102c440d214500c603804074083c240c410064480c42c0a400c140c2007400700399105c0e00d0040403101c801e1041d2252900508841000f080361107503540707008001d814604240c40800000c0c006d445003503211641c114180c51804014191681c2c80f407a225485c004004081e0000c2041e0002070200f41e02c908500110011010f1030311141c00450500843e1030b00c0303c00c54004040748210040096000d81c4001420700031180381e8240c0c0d4520b0340250001042c0d0082c50780c10464880021001c111614090b4010909144102003905665005031038120032200d45620b0403400020000c00c000840c601242c2845900c4800d0030204948520790400030105070381 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 542406187 1250 542404937 542404939
    0x12070e010e130b010303090617060108040b2a07120f1209080903060f04020a06090f290301060c02090a060303170603011e140108030307020312060109120b0613061202 73
    0x4220114046000e0301e03180c2c0e4a402d800c4490110303a96503d00d0002d1200200740f0407800040c3c141e038118011141c20f400182c0c05514141e40390304443d1a551109800c410000d060406550038030b034a136000c284200c83c0084900c0d111841c0135138a070b54070b9041441e15501c4401400041024203903400302142c3c1c202c00032840d804020600011100d40518014409101d11499242d0600ca00c01c2007060840c161803070142f10b1482075a41072005a1380c5c9001343c40f01c0c00d403406540060386410701c051211b021108034600c8401d1020b441940b0350310313004002c440958000e812280015688503140c4081d402c1810806411800d4400200705540c40c68a005004000010361261820a94000f080c001d075000d40004426004000024240449400b9001c00a00c0140040100c9145140001500b0b40c004002c1d00d110700c1d901d030059881e04a1140700c402c1c1d05100180514140126a00c01140031501c030402c54000c1d5200d0300046010741003001c02c00010201803074070484094107069050088a0180c00760310501c50f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 542407437 1250 542406187 542406209
    0x30305041413060b0a03061e1e0509010803070c140d0318081b0405010b03090309010c0c081033053001051806060a030f0510050108010b12070e01 64
    0x445000a60510052a00070410a043c03c1c03010490340c09040c020300d580c080310348041280c50ba44c0c00001507404c0d281609000058500036007000041403144160b01440070003900b03071154588450010b03840b14000e0b00710801680c004580030080000c280b0800020b020565100c15510301c11200080c030404030540c009040101178035480d002020940101d5002e000c5210995103200f08641d00d2a8110700180d036441d21450805000003100107540089a006a407408051841c0c600707440015154445620800c80b2807040c206800a0350320f1050021146481c2113007804140407181c1c1c0958006045903d8600805007400c084002010801c6c90191044402c00c1c0c0740104810386c400e00c018080087d807441c502c0b214520144040090b0030661166205d44982d4090704411010120394039a101c108640150700089001002d0010075114902c194500e0310030401ca40c0c050001154200669000ba404010240c3d101e0411028624050b24002d6420011900404840c0c2c50100340a00800042c450341000031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 542408687 1250 542407437 542407469
    0x1b0807020a1e03051c050919050d03020919031b08010b0d0303050a1103150901150504031b030f03020a02030d05130b030703092103140609070e01031b0e0f0102060103030504 76
    0x1400384c8150f0340454255082403040d1420364107001d0180c80200d449010f9802403e003e0000311540d241414545500040102484404003209800039884502640ea0104000301c2c100b0401952002c3c00001d584240056450081e103c032121405c000c040d040314906906001b03180c1d002c0c2d10740b2611111459094540030400b46c9405050400600720b100400e040541c0000c2080215080452182c02c6d0800645440c91103030398403030106104440928000740040d00810042010686940003190301ca80803810342d9060940e00c0d40c403504070001c0d0580880c0540c005e041c0060551030b040c00322242108a90604078038040c102d00103081c11800361300448410b1140400840d1000d8030960000c250540d010303d07180040001000307080e40b0740c0c60001c21540040e040042480c1040c01c07900c00140508005401c401b0141c4581100362041c0860003449810940d0b50700068a60140d41401d02010740344607101d0500c555410350501c03505001c0720580c0f030705643c000c000400009900008440c00c88038a149080402c0e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 542409937 1250 542408687 542408693
    0x907080402040b100c0210090608010303050f120a0504110303030610180317070c0f03150507031113050306090f0d14070203010c0819060303050f1c1b0807020a1e 71
    0x1c01802079229000354600d002130f040e068000107030551807402210313044100200c104080f07808500900403000081c128000420001e03001d07034084e0178909a902030310340c10b010f060718583c450b8040403111002c1d081d07240c00902c814040040402e0a8a80054016515600e070000100301000151458002003160501d0040b0075880d10400c004051548581c61800b000049030f003140035a04a58029104070303044d036070006011441805000100d035400360034400402020500203008090040011090548420388088810411002480c0d241c045000503c4894102418507107002070082c0700c0c0c101644210210809218000389441c40c01c070036407611800c1d039515881214814051040c0003501507003002e40c01c5002ea40c05c241d00030700c182007001d6050ba102c0c503800329002c240c601c10f20000d004100c0c200500500020010010203d440b0684420500c0700043c40000301107a0361508107a20075140c1c1811034500c5a8800741c1550001a1440200b211515584075929010030003640f903518628105200c41c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 542411187 1250 542409937 542409941
    0x31b0e0d0606050d050c031e0a200a090c0906090b030f10030b040507060809030a2705031213050109181a040e010606020c0d110d050703080304050703030e0f090708040204 75
    0x58500604124051840b40c07038051b80d22190390764411b1180c0181e1418105200d10b0041039141103150b04014200701c4250348885442d10403032603225a0700900d0402002d06071b10340c014581c0092242000011b0140c40e004802032620800750000820402e054a040114401100c203882e00005210b820281e640c4607040041400185944005e00362010401000240103000c20602c00f11000d0b41c03034080340c1da0750f45000c0c182c8a209040c004d00100d03011394044034103440c219604001038465a08654030761911a80002c1c40c0039010110020404400200044000c07800310300c01006000a08140400318100403c4900d04c440c450807012900f40d542403c130f4041c481c45044040304000c0a08100a204901c0c0c0005000c1e0149004100140c1700d445a00c071840d042c1038007480310154018021481d007000c1d0008002916020070b4042c0c8081c420802d003c40424203010046002c0c03403180700240505491803501514641148050354480c0c07484001084650b1641501254070014a03d82422240e50324400100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 542412437 1250 542411187 542411189
    0x1e010e0a030809030d080903192f0d0309020a06031104090608150711030409051b040807140d020f06280309060510030c12080408030a0906031b0e0d0606 67
    0x9800080c000c000024030201e44014032010009400361003e000068000369540e442c141c440980f1070740200300f8020301403400000d03c0b4401000d0b1070305001c019414111003261b401001c0c0441b00e00070140c14441c02e409402c10000011454600b1f0501c0703510a07a80010309480b045202d684d09054540060030440740e030f078008503409450141c00401c0261b841d040280e5540c100c0c0042e0318480040c203400325071034601400600381a249139000841c5420306095081c4064140039086103120300034075800c55584a41d00010708080c00c00040140a024548418490b138244091346890250342200000b07009621015070030100d4103c141c40040d41c81f00b0841c42d000b01410700510f54210383c94404d402e95052540f40c0c1041d81403d0140b481031015407075512214078081e42c6072000a00c00c00e90b098040140c01e20780c02c5564942c030b00038101e80342019a207010303140c21980040507140000341c81c04424032170640c051092945400256910002c0b501102401900c0d90425201141c4252039640b50001000941c2d00000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 542413687 1250 542412437 542412439
    0x120e031c020f0307030f0f270503091e0915030d1b0f1113050c070b1b07060516081005120709090b0a1404030c020603041a04030207030615051e010e 65
    0x3981c0c0e840d00c075500400608101646d050740e00e04001c081e9200003498040c0800d21481200c003026080f40110324002c06032006002140d0901003400020410303a103c5000300c0d0103001d18403460600c2040340041190000c8014440c900001c24603540030240e89002900a19a00e501c0c10321002082c4441819004e202d0101c4008041402c1050018100520300100008100c800c1e22140c100c81c8003400d1020a9a000f00c4495800341d001f80000360105203003a100c0d5401c002c100006890800c03480d00d01c880d56912029040e81e08544030713001e1042e8a01446060050100d507407400f502c0e68180301511602001a911a15216030801400c0c1c0c3c0d0241c41c144108401085158420405440c10340b60019400f10205d070400768285ca400190a00d12840c0d14185100d42d91560768203014074034aa00b0032070f0070380024005641ca81c03440d000c0c030f20300341c500c595040e4003881c00f81d0000c2119030f1451501600352240d6418000d00c00011200400107074070751410050a00b041d50300420407800350303000101c0d68004510059 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 542414937 1250 542413687 542413717
    0x9010810030f0c1707050102120a09050a080604110d031d0a091d0f010b0604060305041104050405060f090712020d0f17070c050306190b1201020a020d120e031c02 71
    0x101d0030031003110810b40440c1c894507039000750660413000790b54840c1064801c2a01580040454080d0b8030758890042c4003140302030510103801519500810344481503a00111480da10600501c400d00685a0b010403a444d02291903280741038050f0390081001d4000383c3c034800c80f800811074640e802d43c0d800794848060a4004d40070400202511010189455100a818480e015107007007200e0203401030284200e800c902803c0b041c41c1902d091004c40040c07000030019100c01c1241100142c2590b9a4040c1c507000d2401907000740000c4c1842250031f800c0090240051040d82e0003a802003000021104188048540403911b801d542e90141c1404102041c442070010031b070914040c00300c24a00014405884401d0041482c190003c0d10340040c142d4514058602010341d19014804041c01401500f18214080018140350000342200420609981084261b800960004880072400c40d900100f9100780760319034003060000001d42c2c25125243d109034a80d240700b804d40a044002e0122403601100c50452108180b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 542416187 1250 542414937 542414963
    0xd050c090a2004030323070f0308090c04050907050f0f0307080717150a0209060d05040309180912030e070f060c0218060a05190801020d02040f12080901081003 70
    0x75103004000002120b072020035840d10080402d400d003000d4800b502d50689880300c0c2c040d5421113458280c19035070301d4070f02018000c01c144ca00040080211104082c841c0e2038141c0c650400000c9942402800c1480d280100e180c401041040c0310000307100c8003168400d60301010100007860115254580000c043c0fa01031055810002c1d4003c80061071504441080c0000f0600b0400b003420242c407a81c00c01c1040404402c1200410380c1e9807503540c018003c450004080c246003000004c42a4140d800458041d0301144281c60f00700044000100b01d01100703400c00e803040102e08140d54400462465078a41e050401d5a0750048142d40300080016001038401d00209600351a80c604000b40855080c2204900a2001e0a1802486c68840702040c1c0926002425107507014140014801c42ea012002c08044868080c1000522584280b00510689202c21800b507522800c02c00f500c0510b9070700368007407160f0400c03c80c4100081078034182940d4109400346840c8200c0e48410b902ca4503204c2041d007000d0049400010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 542417437 1250 542416187 542416201
    0x20306031c120e0d03050609070c1205040e07020d120e0a0b0618010f08010c030e0d08070306171b032a04060b030a091b15140d0c0504060905030d0903020d050c09 71
    0x40c14900e080419074060003187e035540309004041000350b078aa00410702080c2507400140015079614a44c62031072a00b40e041070360301e0000c0002040161003880c0544c12071294442103551001e4151600303030702800117100d00c80700445401d03500d4184031400341903d08401d0210360581e80c0e4551940c200c00380085c0880d855610341403601d400c00540d104100e40b9610f00080d00e86000e01038000d420309940c2c48000342008440c224002c3e1940e83c80104560101a580e9901240381c1e48900034815569141c14014404103000541c03020400e50404d0103284213a02401040b80c007030f07078a14681114144a034012813484013004003c10041d1183d6006400403c8000c8204254440c19074403d50469014a60001c040c42000c94064036005c0345000b100031091105800c810f210380103640302106000c1240900e8070f0030409802c004119038801454400050b030020701001065845810980903010032400303058080080070b006000b1409510000b0b0081c001c00d540801400f5051001c2212a000680441310718030b8001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 542418687 1250 542417437 542417443
    0x216020a0e090d0c0206181818062a0d0b0604151d0901050f0a050405130215040806130525170303040b040335011503020306031c120e 59
    0x1101002c0c20720801042c410081c0c45641d021040b80c0c0c0141c4083d2030039541443c000344440c150340c4442c0d0859403100d04004034000420000388a204101d00004032444c19204050610034040d142c0c000c03601c11480d000202d0050403803c0d51080203480001640c0d08800c0310320340050300340e58900d65408040400c00150020f0f09401103c1f8608c0681e4500b028404002160b0528191400c4980d41107202c85005104c1d608000040c0d2465280c0104100c81813560f5100150a0b528122549c06480c41c103100781c4030841c00d014400342a100350124542c0e041c103080c5030006035207540c018107890340001010445c81c14418144418421542016500d0400c00088614009440130501c11120142030440907a00d6290010055078010fa51110746641940c507a500c00300c070140c5501c02c203074500c00c8a00400709039110700c0d90313100701c06542c0043c0340e18002e43c505001c0e00700d00c0031220b55401c1450b00400c00c002c116607001c10407401e050071502501a03080c1e1349050840e80e01c0114042080710340d06d40b40140f04144400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 542419937 1250 542418687 542418691
    0x62312010f0b0a090b0f0c010603050c0102010e06160c24051803041a07020604080f0a050606040506280b0c030c010e0c0a14150304140d11030a030216020a0e 69
    0x40810a60199407004a2542c611400e40382c1400268418018000c083c650b10050041c080c501110509004076584a107084600c142e0046540307a0000c03500e1225541c0a00948915512410190040386003100743c1101c80001e4a18080410050040a01c10062040441c0d07804910040c00210b8040040ba5488000d00c000c0d56001c0a540d680b84034110404d4000084070b01340c0c1c400b000d80c4600424025840079040d0010320040361700c014240300c04155900100042000d549030700008001c04021400c3c95410010701a02c4070b402107040c4010029a0780320b4000d0030f01426a0304101c03000c12083d0003207051a2104d0780c0c01019032880d001860711035070301c4000f002c0c04140f19040c000304180c504c103145030f541d1100004285a001283c80104202140070a6401c85000c040940340b8040711800902804859104403421034030344100c012000641070f01080410034422081c1001800c010000b10a9584c03400340449400400d81c0004075241c00c0c824601c2807a00c0b1507809802180c00e203450300341c165401102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 542421187 1250 542419937 542419949
    0x70f0f03080906010b04050d081b03031b0901050405221d060f270102071b031209061d120a060905120313030c1e06051e040c06231201 59
    0x1600d804aa0401c02c089001812155001d801038501803502c07050201c8401403081c03d80d03d520051003410401d9450702da03c07404d1010b882c0040d41c0c4c0d82c5400c0b03213205011061000100f10140c414041d03070304a80d130440300306d400342c0341c08a0745801c0c0303d84e012441203040c1980e062942501c9051051400100b5031080e0301c01c04161816064407a2661114a6241080b1049178081501d80303072001d11264611522507510000450000003515041c00750b11407880030030b52003480b90b20b030005248c01041440f50303002c0002d010040a01c0c0c0417081c0d03403030800002c00000740400c4003e40703503000e0740c5604403d9544082854000820405941d080c40b041e090640050105c6007040c1c900b8081c5030708080300802900300b01d1b0f00c10b010402c01c0349822441601d08592804410300100c4007041c5415000752401c50828401c0d08041c882c0710003083c1e0b4a03104007118080078284c0c0104000007901030510002601b415004410385102d40751160040c450440001c102841c0e0b0280c40a48400c002100d0907002d04600e0b019041e201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 542422437 1250 542421187 542421197
    0x60c03080109020d090c4205070807050d05130509063a140106060f17070e0d05010c0e01090303141e03070201060303180e07032c030d050a050c0304140102070f0f03 72
    0x40e0f50342c860704203072038000540341f60107440d129140c000c600800c054140d0038000c80d0340710b0810060b50b6886242c2422400e140001c25004074815952184240c0e0b142c0191600355030310241030070888007080d5a03901018510f403160817000c076100003040c00c0e445101c2516103010992051100380d42400a90380e07900107004505542007900119009000d2140f00c0070007407260fa10840c000c11542e08480c03220001429402c00c1010903490222280d031881c1d40c80d20a10301880c00003464441640c0c01804080e1582c2810341405100c0d41c0c01c001180d002080d0703142c82220403622a94441d01c0d440442d003111010015112580710100074009400d5055001c142564400d0302c60140380e04551804442c071140d81e2140550316602200090051807182e0031450365060114850351840101c0d401100d60b200c0a550904d6242d8001702e21031a01819500800750419010241000300d0f082800021400d440002c202401c142e84c0c00789000d003242801d5040380c08040c0c100402051000c180e00e00740712801a00142680050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 542423687 1250 542422437 542422499
    0x809090903190e0405010e01120b070203040f0b0c07170a03030b06070f0309090b040b1005070204060b0f07061805070317071509020108090c0609010309020d060f0506010207060c03080109020d090c 86
    0xd1b101407c0c0350580c1c14401c07120101c200f843e9240c0c610020700402d0102140011712002402d21f2803101c542020701030300702038507498000c5882c1a61402c181135004d520f040e0072007050f408041c0b0000c926a4803a640520740820001914008109c982c07150007002410400c10203202000c1c50b03030002030b076016503c02d41d00510980032a00304000984503941500b580c4038101c401003802c10b6000c1e4000f01180d510203040170900680d07810191000340c2002d1107580800b0000691101049040d104264000400f054251528041c82d01e8650391140385010050040c040390700c6400700060040151241c1c541e00405025400d010b1204032070207858800b01c01c901180f00c5002150305080c001c29040044a4064000382c10840002e0044014080000c026a0040c5140d190000403076050700a445080d61102c0d001f00e02c038140b490009203840200e82c010380c108000072a8040020798450009811a8500c000c096180c40003501000001c100c5203200034400300c4800400552981c415034500d034516041d000320281a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 542424937 1250 542423687 542423699
    0x1e0f03010f08010e0318031524030115030f03021204090606112b050f0d020414060f030c1305220b15120a11040806061c0809090903190e040501 63
    0xb88290011318041904148100c1d0700302d04004441444100005084600006200c18035522007001a6406c1c0c84a42c2c00750100150341d85048440c0f440d910382034008103d403101c0100064448801400018540495400b0142c1850310030082005041c01070000e182d0707030350ba0700c051070402800640704500110314840b002c901c0c0c1a0700400c1d500c0004d10140d445000c220200400c080c1074900b03146103002800020b20810560761444c401810001c4603681c00184c0c1c40d030a00b03540440d02d4156020451040a04000301e0666002c050b06a03034001842442d8030742c544e4100003c6640c0c59165400c1180c1111000854040c0588010220f104840240701c080081c4903107070301072198000d071208008008000410484990340010309200d40d200030140c100141e42c074480d11109000342c1c01940540300540c031000c1804014645944044080d8944a10411800200e56581c030000c0c0143d642091244070000005404103c080c821902d081000d03030303c2800025850304029111540c20061180514500740001ca12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 542426187 1250 542424937 542424941
    0x20a0c060f020303040201030e1218190303020a060f140c0d0f150303080426031b07021e010c020301050a020a02060a09030c12170a0c030b01020a171e0f03010f0801 72
    0x52481d203034041c52445e50765800650140120140342000361040800c0c02282c000c1ea44080e0982c246821300c0724001d21241c00800c0313460904480c42c585984006082000000d0f00050f00340324007940b0a00c08152491203181a80041c0030001c50180d100303031000c04006203a8080d400428000c0c050a10412410003504c91180440700040440800405130a00601c08a40200d2204e90300c24800c540e002c8079104940b004074078141810354003550080010080c490103400c0141ca080c11040b411031050b0404040360002100c010200020074403044101d030150800307034402c0d40042100754001d4002e00c42d60800b1603803100298030110400005000f0b003804503036405a18090600282d030103541e8240b00c0700c3d0603103d094a006001c0210414400c1c4142710140f5070358600c0718248620b40300700c00010b40303521000c805030030780350034104040c111740081200300d0006071100b00c07205078610718441a549440150400405540e0154504958100086034074445801e4140041d410b0707074050788240c240c00d542e0700c42d4242 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 542427437 1250 542426187 542426207
    0x60c0b0f0408030106110705030102070c0305070b390609030d0e0303060306070818070b0703080c120c0d0e010608300901050703090509131407030804031e020a06020a0c06 75
    0xc80c82c0800c200402c00203206503803080004a070401500c95880e900e60009017280c0c400380c0b04a516100c80b030003c20a01100b40804030052040c040036034500045520715600440d01d19162070317075000f66050f030002d81720120010b00e8000c0d10108100d40c858100402190b642c0c0c1c01006200e400780c0d007048500c44111801106a0740100c201500602064131843d1080e182424000d03d69010342080e03813032a584004007001694020314042c0505c0e551480745d42001421b40c040205040c1c2da0040400681c1e140818000905901964410005465240c140c010102030016079206000030342c00c1550125858001081f00011180d12a4405c2c45560418191042d05034440924481c565030034866085c965003c3c0004120752071203480e103488010f0701c0b5000595402400d0f103000d0fa20021019100d02002071900741001084000030081145520b16a5152050701c02e0340402402000078007103220002c0540d8050070f981030381c024109042c09031234003402941c4030400781003546c12400901c1c2c0080e100e4041c40003a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 542428687 1250 542427437 542427443
    0x90b0d060e190c090617070c080a1805060a0c17130b09040c0305060a031b1a0d0606050415181205060411090114100c1b081c02060f090307020a060c0b0f04 68
    0x802c0348444c2444ca0403800000c2c2880184804002c1d0240001c9e504c00c01000b2412503a103581c0704a174411a0f000d91845c685801c0713a070240ca410041c040c580c070341200084009503808112120a84d200c0344824203d03004a500420444008850102d0101100c401402c2e100d842035500f0000c0f42e20101d011016a902a00c416070031010f00801030000c10007648244d840c0031030f030707008800c0b4031640e80001d0f4100d0005403411221124002c0380040c556001401043c00400300c61030101d00b804c5c20700740c03030480001c01d800c0c1180038800000100d03030702d4141044090005150381440188100d440e804e109131112821542203440108a2207880c071700d80781140c804c0e41601c80d1200707510411000c0c4000c1c06014040c03640700c03100703100c017900300307200021031480302c2d1001d448490200320b080c0e40c0351080051030002e01000e00c01420390880c80c0c00d204182d0000d40c095000303048076100c89090303c81280d114214843c109000e9000285a1004500103402501303590043e440307071081d88120744d00c078164020401c0c000c2c1d40c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 542429937 1250 542428687 542428697
    0x10f05090c04030308130809060307030c0f110709020a02010e0307031707110a06091a070e0315010b160f060e241303050d0b090f0f090607090b0d060e190c0906 70
    0x30850f500080306042050f507208196107460a1039650002d2742d00d4100b200c8030300c0003139102d02480c0b03400c030307440902c2102400306800d085011080f642521340e15240240541c0b600c2c25370114880001902c02d410480244080d030041da40e0315007590600604c03c10b1004400642c902030000482d861034071407011070500811060152200b040c981d9070344000780c90711807400d030348642c2c4d04542d02e082e01d801d84041c180200c019440e050103240d03410041c14100a4050079035103003000b21000400102032031008848821406203204003139450360703203401150f1212154014000500c5d101c000d00c1003241c0080d00c52034209070024120880350072522030317008400b400c4903489049108014003d002900450281200f103445a0b4045000400d0502003070f00284112124060003940506014010300481c00d100c0d00444140090640c0c2d1a0514000e800045288254021900000303014070043c401035005c3c3c8098103032100030b4601070805108504016100e00c0c02911210700e0920301c030000d640512148030445e9540c0d00c1d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 542431187 1250 542429937 542429941
    0x510050a050702220605010306060f0518060c0703240606020a120e0d06020417070f15020307060e0c0f0a050a050909010b030d021c020a0b06090405070905010f05090c04030308 77
    0x120703440d80020208907041a0141d900b8400301545184142811052060000e0114a404001425280d2950154041c0103403035031040c1010781d2042c00c83d4860000080c18242054085000c95500d1044e01144100b5000c0c1920101c10000d0b40102d00c184024240f01301036152442d411200c048420301d203c2c100260780300344051400035806da00802000750285c10140d260300c0f101400709017607030441d120441e1100d600080c14080d0941d164440e0b00c0d44d04070a40140580742c1462604030044005024014a6440c200411015a4800c00860300c90304e034450001d0007451041c460b055552003d62451610070b030074240800701213040440c102c4c4e0880c0d02c010080c0c000c031480c0605000910300c029225035425500c03070411780c5007501c0400050720b581d109a40105024481645164807042d44841500f0454000d40b00050108100c1c248654009800300c51210782c0e80c031507190282c5410085c0c1c1c000e0700300d1420500000b91a24240d082d05044890550309000c65550701e03070459005114500008001c40c0182e40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 542432437 1250 542431187 542431207
    0x6030709090c030f0c0504030203161a0304151b0f0c0b0a0b01020f1c140307020a08090303130602100f050f011406070f0c170c0d08030907030209040503040e01051005 73
    0x42942c41901d03500b800103c04580400b40000e80c0c1040c1c003100041640002e08000714141044411244a1154000b440c1c0e42d0030702c100780d0781241101d2075010720a0b0b0040b003c40c0c1440a00100ca00e00d0000341081002421032403512020110150740400c404501445140302d011805055154480e66211020603c160f03200d520540080070300e6a141d83c11441030703d00070745214800300800c19142e41c454034810043e0718800b03c003d154400d840343c0c03640c4807003081c01170181440e000110900010b0384440501e80350031043c400b1911354042e9006d00d00000f60003007c009620746d0003203843c80340022181414001000c0345d46506007501c42c00ea6032003500c507401e440104198842d0796407202100c580100300b1890403160b03844151038901c00c0c410a440110300880100030038400359030084c4030b4011a401a210010ba00c0c400500c001c1000314000d440300800100141c0040002d111400146034002c2c01940c881c14141003255036500580030b824a1680035000205862800341c0c0100c081d1000b0f41d0f2510b203070440002c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 542433687 1250 542432437 542432441
    0x10c020a12021e030309060601051201030b0417030f06090603150408030903210603070e010621020915070507050d05120c0c131b0503060d0b06030c04021908060603070909 75
    0x41c1e40e00d045010b04030b484450041030340312030700100107072100454890a01c0c0005030b04056014190905202c002c0202c080c0512402154074110ba8100b1594409542d030741c18201c81340741d550260b460406500008015802c015411610300584080e1088609a41c4c0c41003803560b2109c0c0361500041e0381c20740d40f0020740011113000080d64840c80620079242810300881b1407044040816251a0080081604100c1c40e800c0c1041103200409840c0b130548841c2d40341c184050000d11810400800c180d400144500c1c2d0007240d90112400420b014000e00e42000e9402c20501e00b68210007000c880074042d0510014042c50201071709506550400c0107032801100b044200040c961128030b841c0031034060f10402100c01d690b20b0300e1541c80400c0004e0046540c442000e94100c0c0c1c04c01d0030084d06c003888814800d010b004d44414003442106035012100710001c1e11041c0c002843c00290440321a401800003900c942da406d401d24048070000d6460312405580c0d04e8000c20003444d0f00049400c040001d0301040200b000c2003890b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 542434937 1250 542433687 542433713
    0x501030203240609040207240c09060f030b0a080a1104022503020a051b01030507080709050607060605040c090503160338011509080111040311011b060b04050603010c020a 75
    0xc001902e044c1e07054000c201607811201040e03a4007500c20403600700140000c181c49a0051112004000310b42c260800075001850364000c5a0401c03d001c414103900b207009511a00c4489001001c0c1340c807840da5009030315034a2031111411517541d4241804404581001d000342d540e4a04030340c20041816402e02c1c40900002e9807130a0550440c800d41c2d0445001c244144960a42c1c49642035050024040402c00902500e00203440f210410801008004001d82d00019000640d101261115a244c2d56410010040c0031703e5005a64003910382009040d000d03811410342c0044440680c16103611185050340c0001c4204688400f415411501c1e0b54206c1c50700c030140036060030741c101790686210b494041c1d840d04c07242c02098110100d880f1007103808d007160b41d0f00917088100514208000748a1840b00d0500000b49001c0c62000a24010707814100140d1680503a01036014013544018210843c1c003a800d0140c06007924071101303030240b0300d060b0120321241418092040c2100154004140300001c59441011541135 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 542436187 1250 542434937 542434939
    0x20c0304050d030c080c010f050c070b0f190614010306050d0302210c0a050c120c13020c012a0f0503061e150a0201022101050907140f0c0307030306050103020324 71
    0x4e18201000500200080e08241c0388603000010940f4003c040c000444070042d0010241c81c105010390f00003e0308240d4059440f0326060000310b16500e032606841c3c0c0010058034008000303130403c2004204640080c88550303074841d00340d0301404115a50028007020411041d0054010782184408031450401200001080241d900d5107034030304030111160600b42181a002101e068004a502d80a02c0c5050b42c401c4200c0140303000542480803240000461100440c801000425000b051444c5803035820352181c8004141611501c03841c00303c1411620455514403201404586022800e18030310f44079905907072003280043c1850406511840a10306880c03014a0741755400f5000d0000ca02c00c201e04080501102001e540000d62078044020b068001640c122103080354601c0d1074401000151395a0501940220050070210403071024116003034010700c01e91740c070040b8022000420070442d4400000074980c3c41d0090341d04010303850f201d80045051b4401038451502050862125024400c4504c5281610f010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 542437437 1250 542436187 542436197
    0x315100e100b04060806042007030c0f021801090c1404050112090204020d0f050901020703020307032a0b1e0105150d0603020d0f051207020a0e1f0902030a0c0201020c0304050d03 78
    0x50340b40c2d01c000a5a000360065400101303482d051145500742802031803280c8850251a8044810504500029015540015041242001503001440301d1445a0007101c5e0300a84030100741126032070080700805084c0b14000c403e510700030000c030840d40f09105000700d1242c150113407490035152500445a1440350210008202c2d60360218200503652440202100e0610402c041601c00c150000d41c0c04070b400040403200b0523401008400c00180e070200071a07000075818100140880d00201500340f2542201c6404a828480c0160f007400b0b10481201075407141c4114140030344d90a02c41a5061203006081c440d0981002c0c1e002251200740282e4400340110441800000500e9550381d00095084a541030b000c0c1c900f107040300c082506114040c4280181601d02800b11441c10185501203881c8001c40d118010481c4c00b0580030403035031400310850200700310101c01000e50840e143c1800344000e5005540852070039203055540018580103000b03a501104e400000f4504062030403050121068980901f1000c200d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 542438687 1250 542437437 542437439
    0x6080a0b04060e16060e06070c0e090f0706030b090702190803090f1608210403110f0d060b010906090302030714120d02010203040c05090609070c06110a020105060315100e10 76
    0x2680401c00f40480d44c4149400403c9103180c424003a064903450074000340603083c200302082c04600711241c260111807004000003100d98940d040b140c184a04d03240244039500403070000084466150300010181c08080f01e92094548880b070081e6034544800305110240b4030760702c1c3c400740494a00005994800c481e90203a0f41c081401c4c0307102500b42444003400040313060101d001072114a504000b180300e50b0800e10500d0034640307081c1200c3c0f0564012444000c115a164282d00f508a88501404445038030002c0c1442c1810000791071f040000d00f6402030f0031030019110b03450005400784620920001c42e078026000d803540c141000d0326443c80684100c401e6809c03500391410140000d000300180c1c0c440700e00503800161a41050b25202000c401c1c42e50203e482650450140000d581d144950b0035001500307420040c040e030b210361902030082e00c051101014840e40110341404055010341103540f140200320240d841b0608000a403211002c8165404d00c80e0360010781003441041001c5000c0f40c3c02207024102c0c06452 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 542439937 1250 542438687 542438711
    0x40c090c020c0f28170105091e0106050406060e03100b1e0d120537030e0a061b080c0a050318030d050103060204140d1509030302071707120306080a0b0406 68
    0x100802138882218858424200040915443d00c0031401240f04000c0c0903500b001484075941c0d004908421858102c06400140c101c9025803103840204000790007031041503a55034003d00480100c0d400c05009005107a0195510006d5100360340c080301c2c00400401102c0d410782c0342c0c82038408900000c6500042550036100c082200d410340402c200c1c3c4c055441590b500c110864400454414000c1300340508440d606810681c00608500120b191b0245070004d40303100c0d103c41940c44d100d41031401a01591030040c415401c50711151140d1151042620b62150684581507507180501c10313010024001401480460342d507441018204021085442c2244d0608004411920440e00d0a0b4422103990f5400603080050b0804040820788040c0210f803d80d509000b01d494080440b0004002d0300e21044d501c078200c004040c00fa0b4107640c0816002101172030010b903402c1c1650b00d1540710040503a040340384d1115440880f440380c0074001c1584d08900c00741803014035580d504200a8000303042201d403035494817491a04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 542441187 1250 542439937 542439979
    0x3021011090a12290f19090501020d0e210a020717060601080c030702061816120b180d051e0703081f061b0201020f030f03040c090c020c0f 61
    0x18000341c1d038900c400d40f440761074903100b80c0c40c500c0301c201006100300200f186580100d4840d10350001507031403030208560710205030030007020074041410441442e0030940c005214055018110140e2004c2040003201b0b0090502c3c0c0c0d0b1340d50014440ca08401c158081140441841c001420780c060544c01120341d032a4450300402ea40e41c00c030701070442d1264030074810000c0660f805050300740c2000b06011900e01e54100f42d48001c2d11914020003140706c0079000398401034142d0702040b503002405030001c1c400c000c00e901d503154800509103440048d82d003042c43e200441c080307100c071641c5c10004203044001000175080d0000240d649030003002d241d140d07079040d00b891140c0301c181c2c81d80180700700303446540d0341109031511600e24045c0040c00a41480008900340081c001c40f6000308540412420340358021140f00d15500c0101d203005945000183c043c040800d0002940509102442c001c9100f0b1884651440d25400c51034202d4914183e00c1b801031340080c5481026090500f4000b010080c085d1080c40c00014050350094 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 542442437 1250 542441187 542441189
    0x902041b05030f0c120f04020a12050105090c01031b0c080d02040308090109082a06131d0105060a090603050403030e0d050715090c0303052811010b0306010303021011090a 75
    0x404a500002080045805161150f130b010b4840b400f02400e00d00c40d03040c810540c000c001d200f801c0c8028200d020809541c0e071340e00c0c02c0000300040101c1e47c40180182c501580649001d03074000e0814841e61440c7c03460ba41c082d028dd440c1000401c03c0b070601c40f102c2c10404485202c0a41c1c02078031500301c2000340050446081c00248041c501408141d0340ea404c1510004150b03120311303404008190040246e454420a82c003101d400c09810001c151551064103030001001881440344814a01c9203007031001656124991001c805540c44126081250380e85a0034400300e407044044000c00a2950b0100740407031402a846260000d0003841c0009079000e46805013031400c009106002c0208202007a15010050b0794511b120003082490000e0101c0b184507079130300c4a00f203064003005003400340208083c1c247c2c2d20402624601c80555201d46107283c207070414040c0c5083e060420102065083c040300e441070382000500103040f02c5c0d0607402030108140800d00280140600d030381d004017040041050151664501010300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 542443687 1250 542442437 542442491
    0x60c2c0f060a11120c0606040b011e030f0207060e150c0703111c03051b0c070b070206190c021c0c0501050f040504140f090f100915051303030e011509090204 69
    0x59920300a00060300e00d01b80000707001c64411802e0030f0071403145917401500c5000300384003644550b550070304405003640034000003a48801c140b4404540442403140c03580050ba82d8444e254180ca01d1a00d5504810700141d4044444542001c810040800000d1280d90400741c1b036001041903610b480009191030b041d903442030381d00e440040c1d110014401000d00001c04c0c1d1005400c030150300d601e480e82400840d9150b603100d02c40c403a254503002c2881170a546481003150340800c83c40a00181c00e48036a2005005d03d04008401d90240c1124102100702c40c5505086040b241d40010107898428913010045445a01030244c12003034401c18400083c240e2076a001d00d02d00c00c000c07030841031850310b8880d20501880c0c0004100780142c0d4081d04055203061000324250042082c204000314041c4114141505103a0203a203024100c00c3c0307010100581e020721449441c452078460342d01840003041c4c0302c800e00e00362030420210001040f407561701040b540f412640042c0d20544060300214a1070454007520104c3c000d124983d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 542444937 1250 542443687 542443723
    0xa050612040b1501090306050601020a0c0f030b06180406050603070801060e0a0507090f0312090e01090c1715010809120a1215120201030f09060c2c0f060a11 69
    0x10100b00070a03202e10310380c400c0f10038892000c0c01e852680000e100e81d0040c4405808180d0794008100340d82d109025120310241c0002c0b6032907101c1c1d9102c400d11070040c8640b0042e5418000c0c41c020440310314241d08040060080e5502d06102915180c42f01001410090305855140c440c856000030f03194400e0048100500c005030008120303140c0740d0300344019207000034108c03810441100b1b818450a40310000400a50360070445058805056a07000d441548080e0001e410303a0181e24000202003031150004204040030703a4481001c007141011003518403105071140044d64000d40d1840516500c00e10030706903ca21a20304803034160018260280700f903404083c519001600703900c031021a0381424041c401103900c60783e6480703401620700b2240c2d082d864040d020003410513407510355050103c0500d81001c04015042380c400c1021401e1b015001d0040034031080c2200d5a1040e041c021a20000d603103031418045ca002030150700d09031100404001c0250f00c1210307450b0901001800348800e500c0200805111070000002d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 542446043 1106 542444937 542444941
    0x30a1808030f1908091c02100f0903090b120703180c0b0a11060f0a180b280c0c170d1404020a0806070c0b060a050612 52
    0x118256100102d03030b4010b001d50ba40700800340c90020080e00c1000c21040001a1844802103540a1654100c140348524402162201e0030003841580305807254111040e2a1004541e00327050380b00c42075039442020104142d00b1181c00300c0500146100503060014091203841030443c02012503080584603a43c0d1600b141c0c1030103000c80b955901401c40040c503034413007503018003941002e1090700000700f1103000645070304d00c0410400d01a0052a41400441c0d680b41440006071101103844003d80d180000301c400411030b003824440c002d440d90b04211895514940070750512080700b8a0f626060744c500b0f681880025000500502403662241500000580c4407040110318011106154a1541800050004003400c103207442c0c0700f076100300c41100c2c05e561503014182d0381d00d800f10ba055001c2881c03007103e5004a00c0f070820596004c54000d00c44090b40c2d448001188240d0401081c00ca42d0f0b10107001 = true := by decide +kernel

theorem cover : BRFrame.Cov 542266187 542446043 := by
  have h0 := BRFrame.cov_init 542266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 542266187 ≤ n) (h2 : n < 542446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
