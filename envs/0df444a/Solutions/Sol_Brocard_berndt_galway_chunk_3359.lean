-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3359
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:26:17.12508+00:00
-- url     : https://prove2.me/submissions/8dd80431-a6a9-4d25-9517-57e80c01dcd7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 603956834 ≤ n < 604136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 603958084 1250 603956834 603956851
    0x50a0e0a080c0a0b0c0309100c0209041a13020f0d03030e0a0b060118321e090108012706090209011d06120d050c0a021f080c0f070f140f0c0108 63
    0x1d17156684003c16101d000b450006031003441c0c44807165080034010810440540d0b0300600380322361885c3c640340c4100020713048142c40c80c40d01d031040c0c00504158085809070149940080140b403c0d07041d000b0400510b080d0701b0004804052b1035040102003860100003c4007260310540329800c0a14010340010712201420602c4442000201c0b02000f1300144000c0c1606001c102e540b200f40e0003001503141d260000684480300d40c008194400308007003155010513445584070211058407550f44d980d982c0074280c468003401c3c525810303035a20005041102d203254104901d40300d01d40103d03114030345400250b400c0344243e0000001d98500521701170315042d000485a8003e00484540c2c0c6041d5552249580c0c44a603c00e0b140e061000020b001d4540f42802c100e0002c00395401000a0000503585210142d5a9000da02d5940422100c00c0030420308400807056070883c0180260043c2006800d4032210210b000c1002d0654000c0b1020001028054040c482c9114000d008401011081c00b1240010401c2c80001d00c0041c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 603959334 1250 603958084 603958087
    0x30405060c12070509030a0804080304030c0e01060203160f0b070305090c030a030f12060e040501151a0d05070302070b040605090c0102060402030304090b03070803280c0b07050a0e0a080c0a0b 84
    0x2c04a50341e00300ca402018618002d0380307920510010a1800304058006404a10017050000d6400c000000502c04d42e0704c01c050f1001040e540d20786010002c0c00c20301800025070070078003a07032040103002400d0a20701400f4041100782d1841540307501c558200c040d5501000240c60f0010001c4201003003001100000e01500145405003090320000c02d81d1582d240c20340e0800251100344211484650480005001c43c84143c04007800c081c60b06c01d001701329140e405403000c04056400108000c1e60a003c04040404400981c9800c034100c804800030140149003e0505034248012008941030758011481184a041d00040c0381c2000c0080301d10b4010801582030442d0310030b00c10080140c60100c00d440c1100d42261011908407d000006030a003462500700342d480f48400304180c48042c07803d4802900550303000200d95581d0146e00012982103070000009003034021680c002c50800d9204100500c01100f1900e0031881d2501014001800040140d101c00145c1c3d0100007200041e02e003400b10900200754280400307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 603960584 1250 603959334 603959347
    0x8060f040201080606071b030201031118060f16060b040608031c0f11131404181410060b090f01020c0310091707050303100503031312060b100203030405060c 69
    0x100144802400241046242c40c01300d030301502c1e01010307144120740c02880700b6680d081da62892000003070789100a0303000a05040720103882c00780b907004450440c10011140b002c90030414041c05815445a44180c45488040065100009005110010301c1e0703c50329001c0340c00d2070604100002d0310300c15003048120341c20400c00b5040103d481014003c81c045c400c0070110315030806003001d034001c0654800d8803402550000314614414001c0b2540da0503900007521050341c0c02c50b07050601c812075511100c22a6900160000c56008c200c200c2c520300914003c0c00e045513400c000128565096940aa01102c1c1e01c03c00495940b05602d050740ba4070482000c207100602d08070b9044000030f5a1a024040b070300c000507980e8a42c64050003012a58195625442d920080d40c0e040a0702c1c0c000e50703c0e40119070002d5030440d00c0074041454903010040394050b216040030780740414207207403500c580600419412101346958642c481c00a456030307442e402c0141c60607006940c5a1a050403d80d0070804020080b408075201009007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 603961834 1250 603960584 603960601
    0x23060a0b070528020a060810170a12050d050a09020114032a0a09050405040f290c0417120d020f0c01060b03010807120b0412021f06050a08150610170c0301030c0806 72
    0x8820403036814601d4170500b2014441014101398ac98840949003503040304d0100d12998100000305403a040e942000c024030399400d8500001c84801440090000d0140b0728412500101342c400b03940c201c0780c98110030b030924200452088c031451403002034105005002c181d0f9000d183d04001907100521054400703000503e450b56a6600d100744080c0e0040030a2200145001d4001c000c032a0056070001c05100e840440c10002240e12440c0c00600c10017446104c19880003100d0680400c130505030310005040340f07062100c81a0f00c0000303500b204109140401c03003403184095120f800d0080300e00501030344941560700d504102d0407604040c1150000303d902c40d1000d8040000803000e40403254450340281c600035001018040403410305600c100701084a01e0039040e00c50000741280d2100c800c9810440f090b031100c99840045c15180c01407421020301890000d0000340b503030300f0300d00e1030b00340b2204003071030004840150001940c01028040d070385920a084040014401c01201c9410040505150002040070f85040d014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 603963084 1250 603961834 603961861
    0x14100f080a0f0312050a0603020f061611030c1809010516020d0807210c020f010e0a060b060403020d030225180b0616050123060a0b070528020a0608 65
    0x80007002c11001c0088101410b1050304034021000110505000e141404031901015080501080c0c0c41080606803840491405c3c2013140d03911500c0701100c070311052480c0c5030403a07086000c01c40c0c1e0383c150003841503040ca160f9075200d4600c07400c407490000000605200c400542120760041c82c7ca050604611602d5041c1600041c02c010034184524005460303079540c440c2102c05969488124803e80242190300d60f0740280c0d80c00880760000e6950032512003803000f101083c00d88480da902010703140c11100090300810260340105d10002c80192005240c41d03525030110712201d1035244242c2c0143c00282610ba0b40190700c3c04608004510b030b00da0001030341d041004000d55166081c07150702405e980c5101b20b210315207030601900c0c00300c080b2110711140c041403400d02a010b0201c0c1e04a035000400e6140c0d03580c0d03000d1080340c921030050401621040b842030600074506055880594195030510642038001c1c12100c04024105d10108400401c1410f0030051041c02540c0b0903a0708000d0511051200b004100c484005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 603964334 1250 603963084 603963103
    0x16030606090b0d14070c030e01030506011d0d0b0f0106021902330a02030702010315080729041d07140306060a0903021302030106120501030f020405150414100f08 71
    0x5200e5590b507200c0f02030800400200b5689030310607480d00200300e181604100c0141241e8000d4840f0340c840c03440070004504070b81048a1a80c003042201140d1281d4103207024200c00c0d400e4014002d00a442402d89800b0f81a1030200d45402080300d4500051001a07030600107544100c000c1c00580401c0304a0fa030000c0c0751011120041c1d112004540402c0ca50180703030b05103101c2c8500030301c19032a50761f80070054029125401484181e0200e402c0444884509214428001c1101c0005000e40115420421000d85892a41c000340c09050701414840000400010003000200f401e107200405192803001901c0803118014014401d00095405024881c401d404c00ca81c0d00c1082290340030b07601c1403000015200c691042e08041e410100d00104007006a003640d00841c141c4134943c84480712300d580c501e8200c0580e002408000d02008515400c4401824160070440d00700078000c9482c400c010450010900301c0b06079400c811541102c410038030201500501c0304002030300c003207030b5030170110f0b03080800c0c80703568a0115 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 603965584 1250 603964334 603964349
    0xf0f0303140a0e1503010812030103020f010804030c0b01090f110a020d2f0105061507200a15120b04020a080f18030301170106060f0e120118050102031603060609 71
    0x3405902e80303031080384a46940752004160340380c90380369408441c002c0c2c1c00074000d00109101e80006041c0c051104020b5a04803039000b80180412450340b0f0046410110107002101401210756500c0c0001b24150300c914080c200f040d50002d050058041c400c4140c0724416001d40c059202000200b00c21030f4082107240380440d0310300f060911080d1840c4400c18424154009909180c1184403204100701e064100a000c0d000449001d0001c100b4200390299030301c602c01004001c480715800c00780c112003451400c000d01301001007a0f0500b01da5181d18a510b40000c019a000000c1c0051460121040c20b81c418441181d600f40e60841c1000307451079005d811800060000c40b8900c0c0c442e0b00141c1490f5044248013030140c462400e494070380d40c2d689820308100d0750721139158069508101010404034894040c840700311085584000040200d1014008080240c082615140d502d0b17915403802a4002440050518850800140e4918000d410b03049103c0314044aa01014140402004581e0703000c0c1d0303040c055a188 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 603966834 1250 603965584 603965587
    0x302160327290408030a08011406090a0608071803050d1713020618280b0315100e040c05040302010e04140414100c0906030c0908030a21060e010f0f030314 68
    0x100c2d18506000d02540e44400004d2200043e40038015a10407442e50489004006140e00b081c1030030200017050080540403900815102e004120144c415216640c00414a0500d85002d44a4408015400c8481c0d0401c1d2030f1948108c65041c0e03500c3d888402034281059110f40c61403982446807030903140b0741e039600c0082d1140c50040390f130b14440000301141030103155000706104880c02081305140a00000c0860182c4000441c1000048246185040302d00c81e024500051001405034010000d51824070315103c410412407407008100d40d12603208180d5940866154151a20b01d14800104201480d0061a01444c28007942c003080180c880c10b410340003503010208403c2100d110f0211440c00c00002005203425081c030024203d640c1c0c11020900940340340d40d409215112680d10262000100d910030fa400c075034010800801010310424a4940c1450640e00e82e00f8840c0811101071300b5621035405c124100700c0e80d0340040010600d8060101c3c010070382011420b4004d855074070041c0000e40c410640140c101070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 603968084 1250 603966834 603966899
    0x1c03021309020301080a02100806130e0337030b100e01110607080a0b040b1011160b0a02070602060108060c0f0403050f010b010f020c0904120302160327 67
    0x100c1014520140c510907900319125a51101d5107940c81c0780700b072400d90007810058040c010039440307040c03468030502d00900080b182d90ba003500c084004104401c00700310507001c18018000398150316100c82000885000c51207a101d40d0500b04401d1500720707140100107062402c0d4015a0fa40c441802d45030003000c1c02c0c00c14240b10002140144c440c003850300d100d07400074002c0004001c43d40e0740045510703000b050500300400c000e03c031083c01d0004030387c60840341c030342d21520101511107403920410304c00d01c45400410580320f45949030f000c58100710803030380c022204420020807109450340d030400888001b0404ca100a14581d45170021940d180d54000d4048107842c003000540500d55801032003260f00030365020049400502c1000c440342e008204580700c0c1e5000a28100080c1d040500c0091488882103000707203013400503142c503999800821804043c4105054080c006115449561a40a40320a019032120303205914503004c103684151044a00100c800014001801080241e4089204011002050031081030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 603969334 1250 603968084 603968107
    0x70f08130312031a0409021305090313030c050312040b160204021204082a0304140f15030405071d040f1106040b04030219031a0414060c07050d021c0302 67
    0x603540014211000e4498100c030415415480010751002482c03000710311079a0001000103031013119202942c46404030091000082c0c1581c021501b08862204991500e1065480100682207580c81540d000750088410485400c081c804488044940b10740c162516052034200a1580078091a83e24001108a4000c085484075411200411549490441303a1715042c074181e6099407019400e001c10041d030b181c0b0300001220fa250303520400002e00014504041c140300c00303030b2083c220501c403003540031102500c24405526082d514012007112002c204d5620320341410418500a015880350000c0b00e50300c01c0d11084404503611880c1c010b584000c1024518840e81004000003800703501c5243d10080c006000681d9880f07050051049a200703584699503040e41103c0103a040606200190002b015040c460882c04a0300c509150b11074811094500810a20403e00d81f90ac2c60481c0d0b400c03409040002c4030001e10000708101694020f00d44000d1842411a80c01c0d1215024803084010605401060a00428 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 603970584 1250 603969334 603969367
    0x302030a11120706050105040c030e1b060405060409060303080f010503070302090a1b0f11070509040201050318030703020607082811040806040809041118090a0609020c060f0705070f08 81
    0x40c100b080c240c1c0b50000d43c10710b034000304400c0c418944103c0ca804001c50145000b800707203088250300b407400b50901d07440486000407103402400d0416400b000812002c5082d80d203000151000d0706a0320000a901070443ca0b01a109550241011030b0a4941000412999500103051801c0d6541a601000140c9810b0455805004140306440700d080c54503814001c5c1300c0c1c1c80a004a094145951200305421051030141c0d00c07001c0a001d2940c102c80248001005540114000c64100070000c1c440465040042d0400e405d5030043c000860042c1c0200b007e12000a40c828149604050030142c0d039940d502a603140d183c0c00c0e00407201840d02440d1100e40c40c80d0a54042c80940c0d0007000c0810655200e45450700e040300c402c1d030100400318130461820402890103000c5c14180c6004042c00d185080e402c0032204104004401e004000c0c0c00784a8507242c010420041900160101c1d0795080010700180c1080c0000140280f401010101000410700c404004039580e41060401d168101036001e0703540b400c080f05402e01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 603971834 1250 603970584 603970603
    0x50c1507020d140c0d26120a0209090f0c030a090305131e0803030f0109090c05041404020307050f030c01030f1404120201050f1021201203070302030a11 67
    0x300489080c24801e0043d0003500c0c01d040194003040e9040c5010602c00c111109552000280070744512640e03121360034646106041c259400401c01d1403c1020881e90f142c8181c004440c5490754a401150200780d40c02e00800442d00309202c0d101c642038500e01103580c0001c07030200605e03050300c5944400414050601800403101c1680c10040404600f40d180c4000400366200459907000c0e01c21610320005018802006070b9005083c0e88100a05c42e0b482d191034100901100d000507106080049000207865440b40700e44c900d1414035203141c090918040c010581014080d42c00180128541d00500303546640100e65007821102c2402e00284030350700d141c07da400600380151000c070008000d100384014859115001110070000368000d1101b5500c0780300c1044c80003025138444c0e90120300f2031410f0243c010f004d44035069201c40d8944940a115098460740e449030304013105550191110100d400c01c40c01c00544031100e444d86d034002145028000c1d94000d54034403038618a2002c2282000c6a883c0100007400719469 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 603973084 1250 603971834 603971839
    0xa09200a03020a0801090201110f07031b0905100303120c0f140903030c01090203160803121504050109020d0e16050d05101103070e011b26040b03090c0d050c150702 72
    0x203025884845045c0200030180090b40840c9030318050210100700059038090000810018110391403640d5601400000310440000521070940000304140790503106252080d00c0c5891140852131a504001d49516900f81c8000303019428006400d0400390045804443c0c86d21a240840c03000848588001150180f0106160301d4000041c032040c10850542150b4103150085046d1908006402020103005059100702e5005810a00c0800c4038000d4100038681c1c0a039880314014003a0103010002400c440c000d030401d0384000da000c01c00f400b20004500c1814100c050f000d0040900400020b120314401c0c046100340c2c1d2080d00420002400c01200340f140e411120b0b074440b014014000ca0344030720540ca810031034900001884000094a981d841425191200342c04829017000007109a01c4000040c0d0100005200380c40995030b01412800000001307000920580102e00c0d00c908020200504252050360340f94800c1c3d90718803070500841e0001c200c00c100c0071002c07a2201c501c2d0440f0102100503010300e04010b907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 603974334 1250 603973084 603973099
    0x50c0a1406010303030b0613090f090501140117031303080903070b03040b0405060f041203050417160c0909021c0507030f051507030203130b19050408040602060a09200a0302 76
    0xa200300006403a5050f0380c440d481c10300440201106000c01ca00940c03006510007210440d040040603415848a0303624521000d0128403109184c9170740742950000480340008900030801081354078441080c6102c0b51120344051490200c04645041c0c4074801804080c010440001c1c262585607001c00c1404c0017070015001c6c103030700c0340341c1030401c6003c08000320b800303a515014503030003c1c1e09084044661846941e102e407841c80e000703142d1032040b40140030080c0b040715003521101c844400d003030740308001e084402c3c198084508484454900074280c101e60f68060030a550034201541c0060361180000e00807034503454441154943c2d103050162400c0c00c2c5500c05810783c0c0d4158444d60611078089041071400b020103202c1e504079198000d0403022440f04568010a10034580305603c00039100c550802d0308404460904110b480c003004c840400c441080da0121411030002508002c03654042c00083e03030111002d0000c102c0c2c02003a032500000c107a0b50312405890000300080c00300d6942c0d42e2064090255030041d040c0c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 603975584 1250 603974334 603974363
    0x2241905010b03040c3c03080315010201060e01050f06030417031303030e0c060f090d021305041202032701050c0a0507081603050d0813080315011101020c0706050c0a 73
    0x1800b503441603c040c1d4180f0101e003400300d51010003486085945084d14491150507603460300054807002c8030000b041c0000035401000002c41c00001c00707113001d40b0910344c0b802c1c1c4078181c803000a82160281d81c05003100da03803524010041d95840800003ca84031060301d5403541d030754840c0f9003048450708603c6100c0195102009001d0400c2ea100c1404554510a8508004d603400d894a032130380d91040e0b03041c042d80c0f11f80100048801e043c00d150240c4400c0801a05a20305041103174000f0742d6007a9060145800e8959032000c02c0f052041701800c40003650b074a4005036150140c800343c401442c644036003540f210111414549031069100c4c104a810700da1519050b52605803540c900300b07844d01441c2c821941036200b0b100c1075030707001502d01c60809d040380c1d44200206114a50b503601a19000401800362005034001100f082c08a0519001184520740e5101342c0700e0890100800501042c8400b021100560b105125500d02c1034000640e44c019507150b801c009841c0c88419940e41c0c5400801000140014000c1c02c1c1d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 603976834 1250 603975584 603975599
    0x100507020c040c0206061302160b0a05090106060c051203060a2411010c05040e1314060f07080402090a24030503130602010b06040605130f15020c010224190501 70
    0x307181401008580c14042e03107440b444120b07034607a016101d15602900d44101034410580a41c020543d0501009540f441d140030703038507002c1100204607071440d24251a84c04101c642c200a104d4440641018104100d81e00c45a444040c0e5071403c460000c44e6880000000c1030203a9229140c0000906440d0741101003489400c11081c500c512010b00d41d800320b0302d000c40700d0001101c107006c0c22078550303074543e642410a8074003034244e40c00d040d0182140d140e10b40181c440c140418891a10383c1000c00c4d40724014900c038101079114000d00c010090440d002c010042007440016550f01d1032035034001c8000580412540762860394101c1c802ca00d1013141100300d001000c00030030040044080d10390b40901d00160002c0716a0703082c0603400e0b11a03a981a90784084100424001d09000b440a091801126800034100c0303a205c21404c00d0740c0c181342d00040100b04003e422548420790400c4010b2040d102031000d04020303c04180440e001e1001f4034041600d1160702c40000e81900c012619203080c62049031414007095946611 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 603978084 1250 603976834 603976843
    0x603060f020901181503090c1715010b0724060e07200c03070e1b07080405210705040f0207060606030c0801090204060f050a0c050a03050409060f121410050702 70
    0x6440c04940400e14540074101c13134000c408202e44400e08017420050082c2c0c0101d0045c00c8080d030484440c606000c0200c2c8052156420401050100004180840e141005a585804140c0c054240034104000c200005040c480b9000016030945400f41d89100c0491050009005036030408210300901108006070315901809004d0071f0543c5038915040095101d528581f0784148091058050344211420015002d8828a0790341c042d030444412007807a070703102500e06442e50040e841035031101004a01800b0314504090203031300051042c0585d0060f070121312045a205c10191280c584100c1d40d44c1d040d03401c4d00645404441300c00383c1c00401005071640303881d000b400a109015800000683c2000040741c82d01d040d02c202e40c1543c1854441c1006d06403520350881d05940a0081102000b00c0880f10b00b00144041041c5042c00c0c1c407a03100c0703507122424108090100d81301584036078002040014104003109809074031004480e040f4404601180b20020303102d291800381c048803a1072602d00420450700703960204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 603979334 1250 603978084 603978097
    0x1b0f0d081509010b03152722030210050a020d060e0f0106140306210114160e011e050f03100612060302030c0907091809061d030d0b040603060f02 64
    0x340350070780a10003020b02035801000d0045403844441040440c402d07036030b448030250b540000100130b207132400700c00d86e03580d0b0f902c1800e80301050100880500f80702c0080c0115034100c2e0006150f5070011541c5101d5100290341b00310f584c0001070010340d0307803001c1907814189804582c21407580c643c060180c0c0741d40c0ca1400b016008210346009210b52b28800110b05540308500e15400480001802400c40d282c1d01c04100e200281244480202c8101d042440c070114020700650202c0380700d410700b040c030341d1608004030b5060820790541c40c800c00206960000c0142c1c1c21503003d0462045c0880000c0980514080c00e403490f103c0c030210360300d0b0040c003c0104018061f280380a24152070b450f54828269400600c3e02c0c000b0754070b4900001f941508610502030071400e100385c031964000c000d4944050141d540f13095101c801010a54500d848a0311102c05a040c4650b80c010040030803010104c5560f62011031000d244c6900403444100c54094460b4045072050752a50408000380d5084a410000c070200202c91000a50242 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 603980584 1250 603979334 603979351
    0x712180b0706060e040c031106071e03030c02071a030a02040504110d0c1d010e01022a01020f06011406030405010209040203010f050f0a0302090a090203011b050406080c09061b0f0d08 80
    0x1d0008168489810400c1e8091039100c81b12907103490669940742000c200360400541c1000f824090400810780e00c0f0503100c03620351074081d008030711300981c20010107541400ca18030b019507102c8802040f001e0302c181c14108840e0800604a61662540041c0e8006441a5071001c2d0f0b006052181d000c074510a480c001b041c80344c2e0000c2d02004090704145081d51211040d1403042c0c0303244040811b580c40784d4021343d8088100d20051050b204507203c01c0d844404c00580e98a259024502c0c0002e05002ca541c040242da03403103560b800000c08580d8504440d1421400107109018040c85022000c40e0030130030250183d13015064010015922503869070b1441d90888040d04c10b0521940000d4a403c0c2141049001c801c2a65000b9080f83c0191351400700d2500039000b401d00c2240c040d90380c0c030010001c6450707000c05a0102070306a50b030559114585800201310781c00140600203085e03c2005010303002d9844000700c50a180142030300b5004407440c0c810322401d062000800b28014003900c2130700381055910800d810f01c54280d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 603981834 1250 603980584 603980591
    0x17181c030e073516030c091a09041101020a050a030e1e090103111210020a0e0102030301120308061305070c0203010e211e040b0307170403050712180b0706 68
    0x50b10b520b11a43c2e000d441091482c55140c1c3c80c0b528000000e290404190340e0a08111840034503000890000202c3c554020f550140c040c2c6c80c00c0c07000c040d030b070b009220918642d01074000c0b41503c0c5000080300c0c4080900700800e985d0216110340d03081d9000744141d00d8440d400c6415245034070303035904003c2c100c1d540b1134ac14544183d170030703084180200082d200c0c0745440f10005880304246a09660398000c002c4074a100c00b1b50b005141c045403101c0190308100c11059010716050158482032089005080382ea6507200346c030305641081c0700500c040e00300005030409030b5806107480705207519100081210b4000108004040ca03050200304162140c00c0016040744078402d8000700481b40d05210722179110035141c0000c01b04604031403c4030003000c00c0c0f0360207810580b0002210070070801550081001c244c7c000c5e0b0081c031512001000b0011569088001d4070b482140416105a003031030650b83c010450700c14a000100440c1503141c01d5203405102c1c40301600c0b000e206540d00098107403240d00c19812900b1000003100c40d1402d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 603983084 1250 603981834 603981839
    0x5030a03060e221101030f090503091005120c0a1b140c010f091703040f080a06180f0b040c2c10290c1207060c17181c030e07 55
    0x8001002d18640050007400c41003c40540c1d44125605242c441c1c554101611840448250340162145841c80c2c0d10803c000c1d591809950b00f03100380380b44102030800c1801000d10401071618401e0170451f40c80603102c0e0707a0a580d55401d000a561440d4002c5030300b0741603c0603051060070000b0821218a44903c1e00f422039544401e02001150038400710030600300000c410610400c490030111205c0ba150b508010f003540c2c03c00b5101d05c8815260f03405988801304560144200c43d0500c2914458110f5002441902d030300c540c0c0040e11020700d49a045e02e0010a201010000241030090351400360001c4c0c0807002e03070780c01c0c03501c0070301c05407803400042c5c01e24070004000d0400400c00791201d46150300100c520030302c0c100003601031407481c1c0c0b00411070000d09400a40420031601503900000d008e407200701c5c0d419090032626140c1c1814001c2c21944900c241c0300910490321a00d148110b602d40d50268030000d0580880c1e0815421000541820344242d166070700d80260305000041d89401d03401c4440200000300488801a9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 603984334 1250 603983084 603983101
    0x40b09131104090b010c02121c0f05070f08090307060e120102032413050a06090c0c050c13020d06090c081308070602030c0438070b0a0b04060305030a03060e 69
    0x1100c00101007204241007000704a0403049400c8812800e405041c0710f101c03103006030042200308480d00c03840c810b55082110a94003542040741c00b03d01e043d29034940580c1c1c4914120303028003507109042000d010030710058400340800954004031504035a001d0b0907509050f40c1d445001d0300000d0744001e694419000c4030307482d85440f501407083da07114441e81c0d40c1c060740b0075519010550044d039080c1000c41d000f12082d00c030300c5032101c414040c5034000e0b440203030009091031030454803804903082406044100b0030329181c8080415400503000d400b401c4202c8805010004d07840d1039400a02c1240d80b46080c0034108003001488011a038040e0380311492035200d82140750b4681841110196a20500403c101b07806c0c0030380804074809502565101195000d03103032406449075491004d58101c030401d45591259461300c00f415008004c0c0ea9240c501081c0a5182441100c1c5d07a0202c440c0c100803e40b00300741d076560300b603018141c4d00d6401220095070031905a0742e490706801ca000f0041c20b243e0240022540d1a14007107051203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 603985584 1250 603984334 603984341
    0x5010506011b1101020316050f060105010908060a051f06120b0603010509070c030207120f0309091e0f020f1606060819020d020103140702011512020a0302150f040b0913 74
    0x3a400c91000075000c8009a5588001d030b0f1500300801d0443c40140040c0c442c50707440c09a8815014040c00042030881f408406152402c00141c22a43c10090350800c02c0060346400106540c02010703003800814256610829075001d5442200c100c100c001e400c201c009001c507000314030220002001c8409202c02d5040d50144040c40c4020b1103002c1d0890600800100168861800040c04030310030b00c156980c066440d007000501c071190715015224042400d410004040e0880c1031007005050f807250078012484001135000481e906100720020740d544600c900a81d001155040ba1200700591403d00c0d1940011a0002043c4000105c200c6401e03242c1600418003050024814649a00702407148010886a074213119809a1084089041c55100c55032000d0240c02049401e20401841d400061608600c07070384031401c18055070100481560481035100540c66503030f404004c0d650140e4400782007520030741262000744660f840c0d01060b03050224002c078400d401c1c10001c0c51003100c2101c14000c145d101c003110300c0c100c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 603986834 1250 603985584 603985607
    0x2310060f0e1b121005090a0506100305310510050610090506040504020d020c0709020c07050f03060a0921020c01170609190605120d0813030507081605030a08040501050601 75
    0x801000c0c03010800c50940b001509031301c9400450080e50300d994803004180610801d4031003c07400764464042101a08114480b00400d85544c07806000c1c904000d0342c2d41c194161401d501c7d01c0160b0400d803207100c0c55000c1e8500741d40126400f00450708200718406a04000380360550f0510f11a000b6008044119441a4180030644034004c049a14051406080100942c440f4920441e00740d0240070450981d1414021000100f9010381c0c09a41d40021580d29824020700e600014852001c41c61340206d1750301e000071910f038440b2030300c5000615280305043c9610305100c20200c407041d1060320000d8500c0c0541c08100b080b01300d4000e8070b5400100748541010034039800c080760104c0d0860380b040e000951000f03400c18039104240603103a001485580701e502280c8181c61400711040c1a9014010080d541ca50060005501405001032015001000d66000b485485000d50203050340101044100f03041e10840c10b906001940003086981d035044400c0090010441214152403551034140001c030194000c18020a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 603988084 1250 603986834 603986881
    0xe01021605011d04050a050f060604030b060d02030309030a080a0207090501061209081c020315042d11030a0903110c0321040902030906090606010c2310060f0e 70
    0x1146050900455100a01a101c91040800c046072483e290700c030382c418140a07403500840071403903203002c2100400c1190301418450140204200400119400c4006c55030010740031500f2030036a21980c00040e282d07014415050303915000d00c5104604000c03110004000d600701e181c0a840d0b2440d5110b5400003241c00c248134140118143c048001d82d46c00d019800b840442e84102c4c0d0380b90414000d19522107503200340c000c8440c00142c1c00400e0100c080c076180248890000100c41c207000b0321300381c1324035882a040c40350b015864075a1b40c1d540b030a0340424550000b81a10030349411440c0c9a103070030716650740504220351080d40441c40840f00031417004070204841d041c0500140c010501c0c10304481403044d0344803421404140611003404081a402e0050008600488051009020034184440d03100d0500101401e06d5040c402460861030000350030107080d004003162084131a012507070320256241007550201c4900070491070000007003081c043c60340c01202918143c4c1c007406d06030743d01c0260703440072044112036858 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 603989334 1250 603988084 603988123
    0x30c0a060f060305070b04061b0b1302180106050d0e0604050703030c05070503060a050a051003020609061305030d180603050709090c0c0f0302061014090f06030a0f06050a0b06090f1002030c070e04030e0102 90
    0xc0c0e1755041c2f0391049000320710151020558202e104254200d84500381c200e840003074000224510121600e011300007844001c140502100c0c2425581ea030b5850741300d403000905200a0b00614401d000b81072005a0080c0b0b0090305440b072500d0b01d184a0310062004a4041489601e4000421030310b216809040301580c1d40503140b98a80745101003041500c5e0009000d0380361111000402180701e4400f440311079003203c0c032600da0691840340391110300241c107202d0700f06404262902e400c20500329071000e180d00458140340f03c0020030200104040303d03602f140180281580504501150070580c0c005180c6100c8d100c1224010399464031000c10380c802201d0080714a031320941480100b0003150b508402980c200c0c1000b01200c0d4a14500d41e15548d00600d0282c0030350301d5550b19401c0100000c00c0307010b84014940c08468261404a80c600010741511485030b1a81c05a81d541041d030b00381e10b00070000c071046a10110120355541d0707982c449888921400305c808900043c50750080410550000610703c401610b10341c910b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 603990584 1250 603989334 603989341
    0x2717010506030c041838070c2006070b0f1e0c0a2105041703070507060b0a090e070306180b0109090f0b011401020c0102030c0a060f060305070b04061b0b 67
    0x10028201103072070720800660401302040050f20b2040c0351100000003a0200c4202c500718106c0c0000c0070f40b5510640c04041041d400c0012040d8404080140140d00c0b2003080003e04a0403200132140845108040e00880001800307428031001c030940f903210712019540e8255541c0c80424200d1004003002d1000c00040c10030b8086100c003412800504904580c610703005280320300003035403c011950310380688c0d5180c540d104103000c01e10448060480508241c0070300d40307145003448040102544152503000e4200f9644401407010740c0d41e42c24810000300050001404440d1200417041c0d280d040da0301c0700325030705850702c203a2416100d4035044031020150007202c00c6103540c0c41c14140340080c0090302400c903002c11022100c0700c00292a10669030180070701c40c442d0300d05034484e800003a241c40d442c5142d00d41558401d2040c0300320031000252464000d03a111a010450078400d00300c1030003400e00ca4100519a020700200891300c607100c5000340c0200c44155a582c0c40b01c05003600c045549418405d0003401100842001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 603991834 1250 603990584 603990589
    0x250504051b0a0c0302060609010f06080702011b020309040609050714130503030a0e042004060e0102070306110306031009120c05250503070807140108072717010506030c 74
    0x60359000210800ca00c0c1e030049140940e070321503440060080c010601200c43c060915a04104d010303802281511003880035410b0500040798000c6c648990000c001001000581c028800c2d0054101a032000f0055141e2100c000b401a4494010019080c041c84ca07003240050207120f00d0091900480300341e101c034003030240b00301c0c00f5031040e074041c11a00c0c102a49a410024040e141000141201452642ca20056129501c10172060ba40341c0558109181d22203610071883d444e4010848007140d65604150b040c0801078070050707080411951018045034502466908080144401144a80f004406660218081003120412601c40f02400381c040394407100046601c41c050801e200c05070780140100c07282451042c065201442480088148110882004206d03604041010001804c1c103100036000f003034240040c4240300704106a0690406c110030011070130090040c0304050500e00615440d100d03003000e100440c1c0d0b100405128400700c00da05d800c85100c03450010f101d83c03401490018081c10b02100b001c000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 603993084 1250 603991834 603991841
    0x70b071403070503030f04020406051f03020904060509090607090b030c0a031104090906090c080f0c09040201110a05070f090246020f010c030c080c0c1203070c0203250504 75
    0x4803415078882002154040380d0100050341c4242c0105041188a00d854814401518010385c011401406031046102c2d07000082e29210081c80001d00c0d0040e110308103c00050050b2805a0045800030920024081c50000201c0c08922400003a100c40c82000d560b40da602e1051710085500003a0350b64140104003d00e84a40c200c9003258040e88905401c007034079414403070100c0300c2d004411034500e0b0b51400050204220b40f80c06800400c001c902910b00c1082c48824203460341c600d0f00c025481402d4003800102168002e14050a010300b0680071285041420302d400c40d07503021140039002500504850010f9211028021214a0452012600c08140107100111a6008220451140c14540f044080d040170344036034920511041c10b50060070070758540b03ca0942119000d40c3c0c50b40c02c040c01c0c00344440b80d140c2c22a0800703030000120020507a075028403203412410816030f030045001107074002040c0402660b101c03205218550081f8182c0d0410820a170000714907441c02c141e0801501008d54003049549007960 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 603994334 1250 603993084 603993113
    0x10c020c0310021c0608010e0d182c040813290a0915050901031508070e09120403030f0e0d0c1e09150f080105010609090f020c07060917070b07 63
    0x139202c0c008a0f0b409001d101622803d410080303550395900702058100d801040710301404003443c20b180302601d840180e1000407540c24010741c000c040f41064040d01d0309009501403165880c0441d40600e140c18203241000c59540310036611141c0e036900e5100030070030460000e0098408103070b4011015807440341101b088030b0f9801120390035050002500d40043c00404e000d2001500003001d5841c0b940c0d851021002400301d90403134400c5074240c400840207105100c03000614100b80d84030358103100081d80c1c64401d140c0c500420346591030200e0030007007400020580c10040308425810310b6110780c14150130f07110a20032080d1414a020707101d14443c400070000315110040e02a590070740109500703410b6844143e00310540382c0003061403c11f124841000c101100441c10381034068100d031402031005516000b03006041000c1c0b40100211940e43d0010f00342d8031a103e0741200c20f400c0403031003a41c0103030307983e44000b4000203401d01c91215240600050448614804104881039901e0708020504042580c1c03159105803a010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 603995584 1250 603994334 603994357
    0x109020a0509010813021801061403160c170c010203061203090a090e0a050303010e070306050a060804032114010602010f06030308130203160f08010c03230a06091409010c020c031002 80
    0x14074890260f2640c00c078210387e100044030380040c5549010b200030540103400b0110070609005200703000c25a188210300308580c001e245003c990340c903120704094842c80c000000045002c1000503100c0d100482c1034000d54411001241e42e56142c081480c1c110b600d0b441030b5503241e5401100c002040c410410182c1c02400e580c0110780840d5900041995803515603402a08281c081c82d1006e03040150081d814000e403805020281c03170a04410707103814000b070704210002e00014144402d010080e40345210032020b031840240c0d00700d8207214198a041d2400350440d820f02600c00194282070902440070b403a8000c0b40c1c01c981d03155803020060b990750501c81c1c1d08044c02800490740750050102007075a13107000c00e402c00042c041c54610081e0141c0b408000030300715600020100c0a0505042e0306214082121742215003861900c0070b08210396583e42d81400c01070100b074004441103840c0c046104180440403403a039100fa1204070007080f0f990013103102030b0f960b0714155002c51742c5036008443c40700f44202030f80c0107480c005062 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 603996834 1250 603995584 603995611
    0xc090e0630010c0903050606030a0807030503060d080d05060108010f05030705212d120301060807030603050f0a060609091e1104180b100609060e062703060109020a05090108 76
    0x4545080742521000584a0300003800d04c001481409814000345410036811002041e4503591940d07112018029140c000e424000040001407880e1100c9847c0c5e031081d0b500c4a40c032684c42554249440050a040c1e9003a400500050004178a003040c404076181501c9004004005151410080260140c180140710460340c1c0e1002c00d485003002d00700312848000e4024600f208071792001a19280030080c010f5414031040d806450703006e01c00c9818a00701d070305440c054503240102e65107500301a030282005502c01440d92082000a012100f00428883d090510401c41800003d9840101c0426601c6035100a06804c105c650420754230000039401c0300c0d14a108a00101d80c02d40c250300043c080340d40c0a4858203040d03184203031010030019170100700c81d4031505031441080200e0409000800942d1980503003400c0c07054010a42d0301c1560b880d41910407200482e884002d4406d0742203074980100c1e91250306d0034020b1084070004141d0030300900030364001d14407580da000d080c200202c00445441c1009481035245405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 603998084 1250 603996834 603996919
    0xd0b15091017150108030702130b0a0e07170c3604021312030503011814041104020c01020d06050a0b030f04022214150301090b040b07051209010c090e06 67
    0x140150f486000703088410245d5215540c0c0d00501401501078440100d800345410480d001580e503940303044081d07a100840d403001cac55491344401d4555180425100040d041040c0410203603000c554002d1424050300d0341381c90783c20100c1150020b000c0c10009400c2c0c8040603403c94903207807070415a0241c802c1c111820000c110a40c0d54240e44030f44250300600503000200000014800c0031481c0c2c050302510034000d07204012203548400e00b5141350001034001400b145280c03443c142150340720f405660000190300000c55940026100000041402d03100c2d8502420324580005440101c8605980c40346c42c007016281810f1b0381d154204400e49401710b141c020743c10b4036042054035030040c83c07007613056119201a8040041c2002c0079016001800300080600c02e85c1040146000182c6226026400c154401003c2c000b545800d1400e851602803001581b00004000e010045003490542085020305040d495480500d6110b6a000703c2d60807040f950150002034040f03080b00521106001c14000e80400c0c0c0d0301188008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 603999334 1250 603998084 603998113
    0x7200d0506271f051b0703030f140402030a030806060d061211121207020315090123010f03110d0b10030c0e011a0d0608030a09081e0c1e0d0b15091017 66
    0x1040351b5005c0c0c0009641e842c006001e4035452154800900e045070b4801c042c0d01e456800a0741c2d5410301d01c00141042078040105003187c03034240c02c3c2c0307a8000000006000d05512060b0703010310341c085103800303030356600c2c034152510002d0400d52400300c0c8910100014007441d013190040044c240c0d0000ca000c0780c1500c90160128800c40c075401d0f41038090400480003040300c90b2709411030800d07542f61b030780d444070700012450041041e5020240100e080303e600c8040382c100f003200b807030024a84c030211240282101e800b00e020000078480020046059038412500110303420b80b5400701c5190b03158240100d482c42d032920505030580c64211806014182003c3c5804034141e51190b184a045801004030100800d20b0f00030140b2880c41c00344240701000075400c42c9441d0301d071840f004441d43c503520407481c1d6009600e50901c07400100c20000d0f00c294002405040c2030901c40e06481c1081d880b41044a094545520441140019240020b034060090200382890783d40141081d10528040705441c501e203056106115003011030a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 604000584 1250 603999334 603999337
    0x2d020903032b111b070b030a0906020c060903092719201902010207080703050c10020c15061905090c0c121b0307200d0506271f051b 58
    0x15402c0c0702015210010030a0700403038100007144850f13882c4c0003004244416944807050766485600c8801c0400c6070242130401900034031420314030441c20f0203074404222905800000030100c4005c10785000d4101c800003000200070003221942052a0301c4645c0200b00c064240c00840c490b644040c02000412160300803808007450b010f91a0801c04031404204a001c844001034465404c0c1d216000035490804940d666049a100740800141841400f00e90302e04001020043d094410a803d0002c665a0031020411a518a501000c2141d103040707060005440e8101040d41d03030201078848411440c4281081c04024902c1c0f00240a03403034a034000d205070004150100180035149854491041da5084c02d8038030840455501d00d44100c42c1c2e8010808440010f0b82d0035920b070b15511000400349009003507080020340c1d621343c0c0d00000c0d00d20310a101c1400404504030381b6441e82500b01c080728201409841d44010340354041d044440c6621929030840320420b0304141c01140d8000340d45480c00c402c41c1c08500482c9003d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 604001834 1250 604000584 604000601
    0x908030706091419030f030905060609090102070b042406050102030d051f0f240f0c020105090901030605090606010305060d030c0212030a08070212160809010207092d020903032b 78
    0x2206000c0e01000307041d003101c05e01d94000c0c06c5180a100d009140e40f0385503074508004c0c180354059410030380021840c190a41c103a8565660110034184541040d041801c514860076080002030f0345580000c44245440740700c0c8104a9406802940c01c100451440e040140340c02800118400300c2c9a1002c0d40b8082120000e4014003081e600325072004e03080400307141035501080e15140009480c210081c0d0800e40100c048102aa103d29003401058030301d10040700c01d1b0040458bc0c0d500500014004001c100103a00a6031007009050100d94803951164011000c1e182c1c29203110f80c01c6803040080401180c0b19a5020020900140c189084100e464041a180da8800e00100c00010300c1d40b414001c0c2664117004411940884420b11810807600c0d91660304c0724540481c0c0100109000102c03030035540d0080c002d4600034440e88a040240f62203866a15080b1800039018070305000c030301e401906036100030740300b91a220309003d001503080041c2c680c80403030b0f03c81001524460842c400405402240c0e0f65005504a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 604003084 1250 604001834 604001863
    0x6110a02102708010c031b080f0703021c09121805010e040902061602030708060601020706030c120f0c14030415020a0203120a0212090a0f06022a0c030c0109080307060914 75
    0x1c0400340e840b0b0003411039900e600d0144807041140e81e241800c50344040403503007001c40c20089c42d6480e280d4000c10303030080c0f06e07001c143c41031a4443d00d5548503482003a030000c82854000c1100c0d1154484603841180c00c09441d0060400780030030140244890b5206841c00c55181c0d0001d071000404907803a0f00081c0c444c0e04130350a8412107400010408045040501c9500c00a1010714000c00d000d041c840000f079150310040c0909000c1654407403440e4400b1344144007141301c15500000401038040003041c00400b40c14144491408116890810500380c240041141c2c892504508101c0f154002614008040d510035221402107201c00e1010510261050416501a400b00400142e4924034129240e0f950100241250002d030041d50104001c5142c0104408400380c0c0700d01d0042c1d840300c0402e80000e501000c601000d4070a504480681c0b084080010300d501c619404030112a00701008000448200090b40150200394100b44240c20000e04150000707041c442c400c122061540302c1e00c0c0481c0e450080d0343c001040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 604004334 1250 604003084 604003091
    0x10b04061401110318040b0d0f030c061b05040b0a020a0803010e010e0106050922060f0b120603030a020a1104020904050f0f010e160815030f03030106110a0210270801 73
    0x514035a00f2000305070042e0100c002842c180b0b0083c5455806030101602c0444c00317075440f10003480b0344c0e80d83c03074999002603544050390f18404042404c009200b070b52401d41c2120103d141841600e41400c2241840d514132110356903003803810703081114008581c0c1008400c0000d41c883e01d595900003428180286001c2c0c6209150510158034042c0541c000d55010703480700040c05802c110a554907114000424905802962003038503c10710700c22a040104035540c0604409900200c000c5681c8840e040106540c980403a4440a103460700300030582c03240b080051140269100d800014001621407403c0b4007200002880181441e1138540820107a901c22141c03641070f80403083c1003001801c150001130b405001038078826265450495140c1d9020b090b0040858140059800041c2000030380c841400d0030340300e020f41580c0c09003003000341c080c0d5070b60801c5c01b818000c01c6501d0000300324441700154582c506a0001d0442e20302c00301c105420b4504602044254038513500383c210313911074509213803002c2004021900001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 604005584 1250 604004334 604004369
    0x51c170a1d010302030130020a080c0102010e160512010212070e010318081b071a030106110d020a141c050910030209030318010c0f120801080d0906050903010b0406 72
    0x4114240c0c41400703181030601c144018040d88560780f45940d82959202c403000c2c0d109017400349184000e40d5000000358410100d00010400c0c00000c100300ea140384017030700203005221141a0701512541c400c410801c1003845000d04002c28034000c0004404d50000380001407801ca500c80740d0501c0e622003100c210012407503c0c244442c081d40d04ac80340540708080b1120450418a10345e03200382584c4079515014803400c1c0144c054181015062204c1c1000303021010001c81e07104ea0510045401350424850200400c1e04540000100b64000c210707280d800307007645d010700440051036440c010300008003194406603100c1d15036184541c00005200c0b49542140792900d81e02e0301d031001d040190440c070a1040104150040c000c400841d140041035460071150048915400d0244800494005501a901900c12907000741014248031010075084240d448075501d850ba05d07030700d81034100e5441340758103103207070009500440401115204d04060004400c0040011818004c01030000781955540c1e0000d800d01442e12598 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 604006834 1250 604005584 604005617
    0xa1410260105210607050c010f15030507063605100c110d02030a0206030912030408070501110a0f030903050d02070b090115060804031d090705120f01051c170a 70
    0x24180042a2507680031001480040381138943c4009085003051000215031000508401e40041134000009003040000601213841c5e20307407159061209581e240101075021034198810724896a010141036000900d244406061040490344100301c0340f00b403030394000c0110382d69940d0f003480400c2240a0381c80b600d46080e40d080c501c0ca020ba0105060340303e500051070810041c1c4020900c10000da40444882e5140d682c0c0b02c54440c108801070300500c0c000c45c070000410041214800140c02d9450048008001ca84503040880c0f009200d178092001c089072001e074006899512079085a410306110f842c0182c100f030320603c0604143c1e040130380d045407210b500804220424009109401201244d12058444c01d460241f000d45080c2004c0c0010b0200403580f610f0484070712000a44516074a00030700646514078081030300400d50380103922940c10301c6200d400807409003c1c040003d9070503940014000500030070300f241041100210108121207410082511004034481c80c00541107020460f102c004004000010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 604008084 1250 604006834 604006849
    0x70e040f0c05190e0f060325050c07090908040905040f05100606110a020919110a0c0615080303131b090b0909030319020f09130f0b0a1410260105 64
    0xc240030841c1210b004c0400750344a0b19201000c04060726100d40d00e468103070300b081c403c584071075098810f035000760804440030390312000501168805805a50139191503580d6541a00c08403c0d0147c102034040c0300c180705041c4558003081c0c20034404c1c041d00c00b5003203040d17a90038244032260351a4800107a4460f810003040303800440c40b40c2c131181c03950040d04800c1e0703243c0d0018441c504054094006569a07095008c2e40c11200d62203100501c00f0510210b03115617220320010403455400b90200d400380d00b0b05c100c01c03108140b6028030800361a10040510f0550f5500c22096090309030681050720345200c80070380501c03c85413048045024012071076011542d0040c000a00458200181c41440c0300e60040041252403406412041c00d220802d0741c0c090703a908460303240340078140a208070f020b40c0076100001c0004800000d50200b48011000c81303042c8803802d0307400c0c1044202c0040d845805040700e1748400101032032501710a56002960b0a040c44100a402c10b040072070443e1560391694440c524100060060346040e94 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 604009334 1250 604008084 604008127
    0x3010515030f0a0b0a08070f0306060b0a020a14160305070503061b0409112701020105060402160b1003080403050d18060c030f20070513090506070e040f0c05 69
    0x14045241d41084500e00a0700c0c00300510a8003030b15a14079140c03085a4401d80c06500030141c110844a205499603c000f0a040a6200c12240c091418000180420000040d14100a003507000b918203200d80d501c88074480140c0302c0e40c0a00311701072041404a0403001f00c2030f16000c0c6003c7d00c0202091801e09050502e040c0b000340251045446101005148520450850b000e036940030002003030700240d4210740e00c128041c1450083d9410040d450303078130740e400003211140f00b4200700364000d00481d191401800124032404030801900e046091040c00030401940c1d095400c1007100441d41900d640d6512188120341054004a40a4202c000501011a80b00118802d08a00e07000010300440c64002c020307200804d203600003070500c6600c210212500703019010304c1a00a05031075989100b24030304c203119500c0702058081c1900ca0509000e41e490b14038000c0c441c080f07a1a5100e0010051034454040c01e40c0c041003e0000c1030b50080d100c0301c000d008031a031401941e074155040d4642ca5180d8051b8014802c4801280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 604010584 1250 604009334 604009369
    0x1c0207090c0302070c03060c1416050d050301050d1704030212070f1a0403060c020f0303072d0504170109020607030e01120e0d050a0908010501060203120709060c1520030105 76
    0x521074000419100c17030418088035030000c000035510f04080c0099844642d00040f482051230007150741d0004c0e045d10851f5001d402d2250b0140c82e450002c840c17040d15039010a02a90780c00800f0305d1500400141084480c40c51402d55007800e5051650329400190b406a020724143d42d2a00011410404020311000070000b604861001400300c00800604401a0040d444064011503c43d000003800c50b0091250a284440550543c1e075203182401c00a800c801514042c00100512038071a00c10f50b00d000c0c103003e402c10303a5560301d072031030145403003c03845080c50071011841c82c03950b840c00350400580d00c0038000c00115209480300d07282888560005084602e01c1c80a00cc8428100b00035042030400114a0500c4034049007030458407584005011910b0010769000380781c3d103628180001c00c1d1039070000098000d1a98402080d112581c42610403201e0803c0c511480e804109021918000600c4009443c40740150040002038034101d4904810704010711504181d100d400c0000042c84076040040c002d05004496 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 604011834 1250 604010584 604010587
    0xf200f10020c061501020307020f060d0509070501140f03011403120301230301020c070315110304060204080123010605030c071a010611071a0c03090a03060b04050106031109121c0207090c0302 84
    0x260400071f0348901c10034000038400c8076a401080c540c0d540e001c080d200b240020340f00411892900710b400c2036403030351140910350101e400e44219410456141003101d8000c00a46441410740e468180103c5410003000f403210703413500421028100700700c1158007840c02019404500c00424045400f181182184840501d00a900412619080880002d244400c49130710070542804085829180f078001c2070000e0b40414403110000030f12050110607005413040c1c42c0580000c100c0b5501d03000c2299140f0030000b102c49000c4100c40010003050b030180e4081c580c4003280006040c9444890b030345045134900041e1003003000078034150040c00119070103001150b14581c0d4000030720b946810310840ca140b080c400f10000700c04030000038021007400014020740f2820a4064641c01c9030ba40c80786010300150422000c02800303941b8000000400c940b003030062091000f01000381c1480d041248007408040030101d03140310010322511100c007031368824001e01c1803075074100c903070141205c241003110050a4403201c55000041500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 604013084 1250 604011834 604011871
    0x90402010c03080c0904020d270c060c030311161703150409080717070312022502041508160b0405060f220909050c010f200f10020c06 59
    0x820468050790715030903050699040e603a00c0c000350494451251304580182c00482d2180902d161350b0002001811091803240301d0390034482d22000200754070080500a142000410015039014a0b00f110b9450f0184c40d010071120211a01030380c080e8001c8010010042c020105001840b0002e1145030603c0d00424005155040202180701070608450700544595030300e400340350401060504070b40070198424000c206100c3d661081d0204c60300107040650100700200d00d804040000c40c822071b050002c0d0618210301b0f40c025001440d5064042c10700c1260099680e85080c01175030000c107c2d50005000000040000c086803180e80d00c0d18200715841402200bc1c14402030080350b60b51301c140c1d03010442081401da214500038072000000e00302c0c0210800c01190041003c50fa9032416006902d845004038211110240854011200c5c83d45290300b607000a1054006128001d81d03140320080c010001200302c4c0e4400802d03201340d90900310114803400f2229400201108049030901002c1e0b8000359843d600103c001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 604014334 1250 604013084 604013087
    0x40506030616030c1e0203041e0302030303040609020612100503011d070312091502010f0b01050a020a03180e090a02120a0b01180608250b160605070201020c1002040603060509040201 80
    0x1812440d18083c16162120303050341a1140e40005020200100702503a0306542c003001a4a95100b8000e145103020260700d43c21502204062210807698041c004524650b41c0c2c1e260500100340152089034802c00401114820502209816010301a401c20380d8500c94900000c141c00c40d07402c0320741340c0b445415490604d0300d030340c0b03000c2103660489420080c41002c00d50194030444401015410812405220006102c210340d41540800600701c1c0b511410040311003403200658280c005c9205841c010303400001e808001901c510740030500020382000c84488103448000040c00300400b100c9070850303588080b40030340075403030302c40d02d40c40d01c0020766400390443c1d03501351300d4502c86007005000d4650504038400142c03030304041c1036005d9001094240c0640d203404420390240c50b1059015554540e041c404101d000c0b8003400074104848003484508030780d407070304200c5ea42c4d070700c01400b0000c05c042c0c1555400d01c000b400424050107030390440e440c1c600d00180e81f20b040542c080c0486850350411405030340410704010041c4d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 604015584 1250 604014334 604014361
    0x9030e1e06040e0a020705160302090a111c0e0718050a02030c04121505010803031006020606062d0a08040c06020a03170a0e120c07241b021e0405060306 67
    0x555950b40d40014036a184d07031102010b48114240142144101400039408841c00b90840040d24421210100c075902d0b001451002c2c1c0c0c21482c04d980c4403050812038140440c40f00540380a180301449030215841a21054075070400006501445180349404000740c2002c2c414800c055020480c024114110b04162141303001501460180e00e15806841c45001e06001c00d48540e044096030949003800503603100d40d0b01e03680329001903031014010000004081161400421014480d030b1010303000350300340340c0340d04020764081101c207120350494003846640c81e81421198006044088480e10380c800141000d20300715401e051160300040840d00052070402c006603010032103600501c1d03c2d0b0301140280d00c07070f11a004c0013003e082000700d007984200d62202c4068805c0304081d04541c0040d07001d54240b01d90341c89201d00020108940b109904000c4101d500e030960080c604038868120b1104c2881d06003d85a002c10031211030881154100c52810b1000c801c64070703050044030b41c805801e4014141508000740e9940d4072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 604016834 1250 604015584 604015589
    0x503010207032f0106060e03010e06060f102115090c0906200a140d110d1103041502010920090a201306091208030c09060c0109030e1e0604 61
    0x740e088099142400b070f82c840c002d00740b001802080404c0d66060081c040d00301c0340c400b060081d420300c680c114050b400420a03d01c03a02c1c01400184443c0d071110208811a000800e6980500034403503681000041c850908614400030218005082001c0c0005071032042c44c07644c050310390300b030400d00c80d038620a6001680904440c0325050000c0b400041030060603100c802402e00400b00d119004810f41886a804029101101410242c0740d49008500003266018540b07050128035900415038000420b02c5202094650023004060b06c0c106a260844012941120071513900142c2d1141a05814814800700781240300503070504184103007225501265130200d004002c421501e541d01d00c000340e06011103041007103964107803040650705d402920b210143c094440c0907010004030060000b09106141c0d0860100094001c03856505550710001c1004641c0e214802c115048503091081d0201010240242d0000500c251246e0865130050803e028000801c00e10f1040c00c1141704582c54500c0e1200c0044405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 604018084 1250 604016834 604016867
    0x6160605090d02120c030a030b06040504051003030e0a060504031e1e0302070905070c03181d1e01030503120405070f0b0c0c0922020312040f060f02240613060b09040501050301020703 80
    0x192005136400190132b0340a00e51269800c00e042c1130403c403011003000b074020182c900c00e889000020707050506001c0f041c130050080602046c000c02080c00404c1d60710040703c0084100508240d2084016540c02040c46030341070000d40c241c98904544010140c0522000e4044c22000d441000545003445006045034622800a0b0a22440c4c000c0041c2c1ba054414000028100c1801c90081540c032a0110690404c070850740050450604003410f80c5119150320305c1c50490313070807030b0055050a0740b000358949010005001190280324295000543d0301c0741d0020b000007407403031030041916041108490f900704403008013400e209030800310400c5190440320100c40034680310901c0c1214242c4c0d840c1302213464150074652006200e5000b003000184030158190798425607805d962241c1544c2405102640d940304a082800100d01400040100326814119101e9121500900c0c5010250847c00004219095034101f41c1d0000c0d00010320392198140380c013841d0300500080d0000c52800c625620000c01c0b0744031109482c82e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 604019334 1250 604018084 604018091
    0x20723180a11030711070f120201080c1903090213050903031b1b070501120203010e061219060e0c0a0f0b0901140d050a0c051806160605090d02120c030a03 68
    0x4091018692218070041902e141041c1d40f4144454040c0c1004407a00d40e11006102e86030700818035401d205c80c41021102e10070303201d00c1452032135401980c80140050042c0800f03030303040c4040a6000701d4201070320000045918001034408450050120548082c0301c40d41002d42070078280400c4050001c00c99a214240c0c1b160a00129903a0605a000307110305441a42030300031054901c001c00310301241030412a082603c940950020b00c051000503404248207a84400d02c0b96000110075081c500209800e0800070010340340200382c8a0002c4250b00c100140c140c482039622140d14a0142c0d04120301d00660100720741083e0100c1c50928100a0f801d681d000c0c40b0192200810448400e0b405550f0300d9111100050300d141e19448181150001410120f515080990510300035030901806403041700d0fa4030708002e8142150401c62401c0c4040e40e402500801003c2d049a440440070900c40c0c4640d074041c02c008800b81c06a4892603100074038080b00044e01d580c00700c004100300008400700000300e46490a4908021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 604020584 1250 604019334 604019341
    0x3080606070203120c070e0c040501050d02302406072102010e010f020702130903051e12010602121225020f0f0d05040303230a02072318 60
    0x19681c1c020418001c0d01885146842000302d0b29070740181510324041011138a0050b074034031103040340100a5034002a401c408120070b1009501c00c10081032255554a805890112400c41405091000803910003a0a0010740f11380d40e40c8260840440d041f501416a17281c41300d04000c540c50580c01d43e1070b1898821a170004115040000c419101074421280b0500864074140268002c0d010b0045440c12100652030302e11a840120028403d4520994015001c0550041281d0056008142488064042c0001841007250700d101095080c0e40c1c0c010002d05103074a0b10010100760001349010703000310095401151074210b1000340041901c907902d0b0000fa101000d619000309507400040c2440011030018040001400902c0c0c00140070220160030741c0c126502c0c602c5404400c0d4460590110002c00500704000400c00311348524410030110704401071610141e030305003000d020a40e100e16000d001680000608025043c1254601d10310416803442c030301c82403002c240000300d82c04c03500b81984103501c0010010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 604021834 1250 604020584 604020589
    0xc030b28030803070816030c050702010305041b0b1206030307020d021c15141f060f020f0d030c18080628060303031a0402040803160512040e0f0105030a0f030806 71
    0x500c8011908006290740c1c909104800a0403503e0454040185441d054280710700a88288140303441c2d488156034041c108820b60f0300440281c41c004d4010707191505030701c400d02c8090600d210100c00801164441683e07482d0b17680f07100b510f0b4900040925119400c03d00c030580c00350300d408112811603541296003440c1000316501c03443e02402031000291135200c20202000c00d1070159800007403400d110003100c0001b03554401d0001c89151500c50080c40c0c91003581000c0099600441017044041000d0041d224910050346000c1d181115601d00c0d00c0000385c48200e103641d904d030801c01d401210681004804900ca0600001594984015102d4080d071100c424400d80d440040e07803092030600000c0c5400740701c59613a9040c003c0182030f2292440b08031004070031580103545013a00c00c4400300d4442d1405141400c441d4018a21010a440d4082d10a401008000c0422221107002040034250100c100c10b60303400d01c2d0348065003408050f040580240d002141c80e0004c1405001407141099240c03601e100705680340c401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 604023084 1250 604021834 604021909
    0x60403180f180b030f10020903150c040311012d0c06021612030b18070903081c0c03060803070f020a090212090c01020c090103170417010507030c030b 66
    0x2400d940c000c0c0010200b00c5010485509511000440303082c840030031550101038031150001038100030380d809440c042da00440c0310303009040505030042c01d0352503042455103840c4600388200c80a110f903900000d401c0c03040280910520366a0b003420b10b042413080c40c08080385000d4640200d0f400f1980100740d80100c512074801c0c11003081082c0d0090f0155102d07141e212484580c0281d241d0304a60710442a003202004134480c1c0314031480014005c1c003110500100c0d84202031000d00190000080006080c000b00224080400500c0717110200900f00c4090f46d210102e41c0b04581c00451410105401c1060402ca0701030004150307866540c003c8907080d03a1280034400030700680c08507440f80b12810b0000c1084096003607a480300d94843c2c050324098a451041a00049071500d4cd800e003802d502c00031502c01440400c100780449550000d041c9062403400da01d0b9a40c4529140000f100303101d840e9180da00308035505505000b4500480a1420107100200c0070030005601042d10003c10804d44d0003560751046418280c00c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 604024334 1250 604023084 604023089
    0x906060c08130b0705100c0509010e1507021503070e09010609090b0307080f07030201140c0a0b1b030a0603050f1f0e12040609032102070501050a110d020607030c1106040318 76
    0x151183c1da903680d10704d49241c40c0c0d5207806c2114041441c00741d03080007540c0904c0495030100b0051707441040001000d400c000c1607002440d0100c80c04170092180c0300041c1c0b00d84e1180c0e082e15040310340450b00e0b45480350008060310942c0c00c0050003a4015401004003d8120b880724003500c80030803000c910704200c900800e00d003d10b10341c0001c0c0d0302d00c41c011161500010204044050328001e0362030301008000002503035030380e201d10020701f01943d01026110001c10610300310150804c000302511031100580002040c4d903a042070b524040425950002081084020001e04490724030f03030f1001c0d001c404504049140b061852451074161b5035100c20106032044e10034080c0c12201550749400741d88880d04d40310f0003808a580b0b03000c00c0b1100900c8026501110880e141c0441c0d07103004030303401490454100341c011030f0a44c0000d00d800081c0840e04100f03000819040c00404080321b40d9a00400d803c1c50162002000c0d42e02061301070061281d0121192102c400228036103501c01e404d4140082c9440306059002700402096 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 604025584 1250 604024334 604024349
    0x100b0909220f0c060e0306060f1912080406090909030f0807020703021807111c05070c1805070305061c020d210819020c0309010305060a08030f070c0906060c0813 71
    0x892031042006150043c8000b0380c0c0e045d685402451610710185903503400c0c1074402903400602a10740010625202801009048000300441c0c50107aa444902c0c4000c03010b41c108a484880c00b00d424820f4940c031002040007020070f010140030a04140e14050010411403203030343e041203d0702000a03185402001500011075010b884040c40841d5410f40c581404025a584000901d580c070b080301c2d0941c00040e50b52103807800002541491442d01005544591003c030b400c50740710025100028000300494440422000e00740c9022446180c0b00d4401022078034000c1219106000900e945442060170b0324001d9150703a4150303400e40c00441ca9040502c0300107141e09014a070201801c0441181542c000003080c010b042101401100114a5072000280d000b207400c162250f500a000701d060a603c00d410040c0c001c840500401640340c1c48d00c1b56142140e010502420b10000001441000c1001900e00c01c00100b001c81b034104025820150001c021280700140607144010106440d01481418262000108000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 604026834 1250 604025584 604025603
    0x30604051012031d063610030902040f0e070b0f120907030b0610140304021203030901090b060612010303050309031909080d08010e01051306050303070b100b090922 72
    0x10781c80c004140c0810810741000e103c4c3c18075081c141908048050315401616404420390481c140d84110210491200a04010704404411400c4030340303a1042d4440c2e082055036002c5000401350051000303a0f001032004060192030168900741442c00441e0b4441941c0d0100a116551b00181040042e00d0050301c0c0b48130940c072440010b210031540001040403c40c0e00c150070720941641c454040201410b0b810402d540401c50481c5003071180c00074003000307591003031000b00301514644a104426280d030700b0440740c545c0140c3d551044001070048a00400d03a020404998161801d015a00403041140040c4002005c1c0240800400c4101a081c01540c540e400c0e01141400040c60341c900052810445100c0c40c1060301440020803040c0340316003050350581d0740075100d0001a0340780400740082c1c2c40030b020781800e100f90380c0c02000c246035805200900313009000d414420a9270500343c03038292982480b80e00c003144c0d0100400154101b616807491081d8080144142d03030544e103600c0182c0c03212507401540c000707180f8502e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 604028084 1250 604026834 604026869
    0x60902070201080f06060d0b010c0c08070807050d02031b060c033411010807030e0106080105041403070c05060d0209060304060515040b0607060509070f060507050616050306040510 79
    0x54590103004614001d0741d6003442138a60085001c0c0c00c14050364100c6c0c0000d000c00c03501c00410b03a150405c1c0558081032400303c000a0454990700320b0200542c0080341c80c1e400c43e2404003e016400c11403000a400704907a07249104c0c120307600282c0c0e00d1110496500381013900d920752027103036034900c81a900030140e070314103407036403203074105040e138141140c0342c6410103070030484400790104115168400111681c00010818428030310070054400d08c1d00100500304050316050200c2c0906030a0080340f008140b039074004501d904003071400303180c0c010740800d0545070f076030051120802051001c6601e008a800580b03880740e03242e0710b0b2808000030303205d01c000c1207800038000401e000402c00260321140c4103150420340e010010307160400300000d0310b084010080d817040c42031203407102140c495404641c01090a400302c5081e1a41e81c46000d01101c503640c0300e0781c0031a43c0460b062041c800140219540510344045207a01c0c01000c0d24094060300003c3c0940e4002d5580d10f00086404007040c000f103000d4072090410300d00000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 604029334 1250 604028084 604028099
    0x503070e1b120a0f06080a0b0604150905090f060708010e070c060c080403080c0903030a14040f08160b032206090512220303050702010f0311071a18070504020c0c0406 73
    0x18826a0308443c840d00d81144132440e055180310300000d580401c006401c0c3c5100030703110101a0240604a142d00541d100082401d000801c0312940061000d003401040a14146003054105080d004003c1c00340e802030340400c51500d501514150540d00c00c83c0f0081c1041d1a10300e01100c1c1c1304c40014008051074505075030b051489410180d10f42c851031007903032004c841e80e95071b0490843c20f014071083d1603007551042c480c0740240d03070003070603c3c220070120104085c2c10140d4444240614203256400311059410140b00e40400341c41514001020340030340c0006a20714180b003100e48112034000d9000300a0007500c2070302d00042103002c2d00300d8424550080119503103100c0d000da02d010181e01030034403074000031855441000c241c6c85e5800c41504680c1c1607218942080c015800648514040c000000d013015540d80045580051203c040c10340e05000f00c03844414010340402c480c0380300c44050b0050740300c0c00c108170410813885000a9030340c013620400d540150300c0d4110100814038260070017110030782c4203040150119180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 604030584 1250 604029334 604029367
    0xf0c050304030507060e04050a0603030f0f17100302210703030503090a0b3102130b03030d06030f11312012060105041d0705040b18190503070e1b 64
    0x1100d041f01d0421807a00c07800e8824044400c0c86c80010701164009088103c20340c050f0082e06c0131403029052500c4002c02036617030881d140f6000c880d21100d80c40604002c0c8254108034111144040c1000303801041c541c000c2401c50743d03403051884024104880000066050b80061088180040d485041200e0300d04010044450558800301c0010924030520394469640180c04035107040c054000d4810301078850480c07003400140010951080d010b20007000b800c26080d10920030680118003529141100e03802c42c0c600004900301c1080c0d03092203862100d0021250a03049044038858100081001c0e08003648280c0c010050b1a9100c0080e0b030151041c035001f4200c9903001c004183c20314290420b023011342da6010040d1001c2c010b42c0160416007a40d00078107455619103406c80750304200f00d41462801e055550480b554150312464112120525a070604195800c2200c0c40c0320442000c0744a411842d410a40420764480e030500c100c00b115031007a0040781c1c0c882c01840c000140f5a01c8520300c2c0382e5a281110b4104000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 604031834 1250 604030584 604030607
    0x121709040203091f2016080c01020a121b030c020c031906060b1e0706060509190e03090d03050304170307020a0507050a1a0c1623040504030f0c05030403050706 70
    0x551080132060350714107203281326008500519204004511400040c000307219040081030781185000a420040400c91480140000503010000503130740b46401c62000300840030245a010f0041e090000c41da07112001d40b9440070340d05009140c001200d00540000b203140203840841c940d0103005e800341c0c480450078128400c8401c03d01030072052203850355403400380c6064400c49160819205440c0c89035060880c0010051407000e0243c0c80129001d51280002540000151240544810740000c8a041c03414207001d4a81b80b18101c101940c100f101403804250340c0310100100804202c8000001000c01002414000040400c1c6d180b0301d841e46000e020181d65029010f106645500c150138000a151034681c80e01d2080c0c4031500d6044400070800340900500c1c1d00001c6160126005094288500c0940040e41034002d1071101c8400c0150000e40c90800d000b400791400860155081600300304c0840d070003841445d032440341071038515498042420154218002ca03003006050703028420001030b001340d01c44442181c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 604033084 1250 604031834 604031863
    0x4020a0e03190b1f09050f07170402091b0f04080618010c090b07030e0432150607020d05010e013903020c0304080709051b0412170904020309 62
    0x100030354800d0101c1012080e45000030203c01501c0002205060800508081d112544403083c03c0c29441d01c0c056030079110111900c0940c600048200050594000e440d502041910781c880076460504e0380224440407401020b01d2400b81501487c0030310401c0340021074418071032040c21307161516110070b810f40d00c2da1015100b85c41e441045818201001c00180b042032034403000d40d02c0c0c0d032a1462502400c0440e98214100940600c200c1e00e00c01182c0342c0711401101840e540c0b01d28041100d46000c0503d200200f45244240034140b404e90030401c102d02c824040c0707004110129aa142c071804544001880c00796003c134000c00950030144400c00301c01c4150048549001040344043c0d5202c036104d01405024070349000341e00807108c000c1203500d00702c1c0241e000304903801402080e41d10345074a4000380b0b8070385540fa51024050955440801045901c680c0d01c1a80d40c2d5a001c0040d80351a00d48414800000940b02e00540307400701d003c0c1d45030340c01d115104c2103916420340030740159200d290900a050301c80c60041c12042 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 604034334 1250 604033084 604033093
    0x1b040312110303070c03080a0e0a05060106030c02150a0e0f070f140f060a0806041b02060906070302092115010b07030915091e05030703150c0e0904030c1104020a0e03 73
    0x5201d1001c025244a80200d645800009003107440440c0d04a40241c4841440b80d52811207050302c443c00e02801c4e10f494055401000c40c2d5242c24001800c5804454072801150011502c01601d8100210000d07000003881c20b000c59181c4041c180c49040c40030764400015a0301c9048000940002c00c55007071012280c1744000c1c3e06d812104e43c41809042180751142c0b6a0000c810440445c05900641a5a0704141e01820008005024500e85540912080c03902ca001d07a004400700700011404002c40d685c084418a8258208049800803820000e4090000404071608000351040c00008015000044003416000c1c000d41d6503a698550065110303030810790015103d00d00103c0c12544403014100021410341d41d01e05200d107803580c40d0380d85c0c80140003044100290070600251542e8204010006180035140100d41c1c100148441c03402c0300d600c52145c400f4810000403000704c681ea1418074a520035058140720503100e20f1840c1c0b0310300c807505500f1595805440410321850041d400031a0261516080c1c0494 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 604035584 1250 604034334 604034357
    0x80303090a1e03050d090f05100b0406091b050309030c100e0d090e01150c050f07080d0c2f0a090203060301060b04080c010c050f010504050a02090708090709051b040312 74
    0xb031280c03944002d03024000c22810400c401034180c066100300b07003036409007a5031100740d1080d03600c10f400c040001f0011020980c686404032400d00c3d2a100c1d00c80284500780d8200300d003000c882003a40c079010b0301c01485030078003074044005119800140700300c03000a10408140e5001c1091070291400030a00d0000301180d030300c50300c80c410700d50381d0180a00f0b600b95400b40e00c0420b49603107000b40404c440e08100c9541000c02c000304180000045040000850100d0200301170b041050508903000d1400f912408c01104000c01c2004550110308203e028240140340002c003100c800610002041649254070101038002400f01000074288004e07901450040c41c0880080c0b1240d50344440510480c0658090201c1c2504074120b690003541c06040b20b078000e5841403054800b415500120f02d421110221800da480d0f421071158401180313415141250310405a080400050500c50380301c075601c078800c0c040c8082056071748001c114113001c1500c12201403000d040310942c2c2d8035140d01d0580506503040e024407020840c912841d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 604036834 1250 604035584 604035623
    0x70b0c09150f0f030c0909070203160f321002040302060d0c091a09031207051e1911030c060a0c06020a0302091c021009050312090a080303090a 63
    0x40380c0e65490010a580500140849030741d040d58031011518071404020054400020700d1580550722070960b172202282c541c3c221718184051039030010019802c64108201d08160f10310b0348510540c5141e0080301c0c0700300b54445490040000c0c000000c400c00c1a4522410683c404025032000d00e81c104041c00a030f584100e480a1132034164002c1d408021b60110781405003240060b0180c3c4661111600703031610303d206554078641e818149200c03555803841c003500010b00c1800b0742800c100e460801d00600f0240c1d0b103004030300c0d141c50f501c8050080300d5413007140c2040201c40251200f0018100015881440481411040c1c03828501482402d041e06020b03024100401c40075260180664124148548a6400300451540c0d658003d512030400d1205055091044c0c0c8002e8442c4c1c545240601c0d200500c00c0500185401040110b00100c241a401c020070480c091080c4d46001c01d81003540e01d581413607a42c0b078007040c10000c3d14126583e002021180300c0401040340e01d00c000680400080e028983c28114500030205 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 604038084 1250 604036834 604036837
    0x40f1209050a050d060f0c09080f030405010921050f01020904050105120d08101509180e03091509540601030f060608150d0203120c070306050c070b0c 66
    0x6071942c0010040030030070a50500c0a24030810b0f9109910011701d40c244000d01c0001c4450b42c038994400100e442100b4850080100040b206007194140214101460600001c001c0c16285c0103043d521100e913508030f03407105948d1f840e0004155001050700c00d03d45040e03c0743c90013508480b405038403840c100000040c2e2030a05440903031085c02d4002c050501420b8865003520f440728050000240350b03200d00000100d82c820307508a6503808441da601e1031035451416101e4203007500100e2000c280d0a15207222600c030786100004841040d030041e209030400394070f60000450b850041ca101150400b6940115140c0505280c0d0700380d0f900703408940e03034803d00b80d0000681d00310072903022048081540300c54402c0005c0070f070800d030035588808149004501c6110f061455816660359610100201c0c00d41014032011560008084540e1001521048c002e042e55800195684003600010001d1010025610030300d08020310051001d0b5810620521003400c003402c10b005190b1005d10b00303480751003d4202040d008a100c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 604039334 1250 604038084 604038089
    0x50606032415270303030703091b080a0606230405070921020a1a0a03110d0905010b03070501110a1e05030c060103060b04020c0d2706091a070c140612040f1209 70
    0xc000311b04540e14000b00707a0003032540c00002e0701c1c101044174618121115288000700a00f801802a10100c141c0c0d00e0080c0950f416a001840036501304c0c80c8824030800c2103030103507a807840212800308903612141000e9491000703e4105800900b402e004081e00c00c07220300c0300e40c444203209075206890207984011007078000b9018aa01d10310032008000e03144406100fa00505a1001140115071401d840443e81038200e43e0b41e644210780c1da035102d06517817072140740900c900740045c030080c20882d20710307181c41c4103082d00d0f881d08590013403503c1c0d804a0362100108038040c8803540d1542c4142100e56031492144800d1303031001c0074401260b045040411002d11400c0500a69508042c444000c0603141c9510f80250382500380800d90f080c41f1407488828283d040c0384616040001e1140da11910b4000e400d114046511820943c030b1f080010f070040101000242c1020740450441d038803000000711680701000041d0051081107903220380c00e0180c0041c0300034054460003c0c0c40750761107141c07402c081300c0300083c0c01c3e0303403001480c0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 604040584 1250 604039334 604039339
    0x324030309081b0604090c12020309100515030304090515030729121302030c0907030b28050d060b04060306051e10120c050307030f051005060603241527 67
    0x9110030401082c4075009487c501000d400c00c4030024502d0031000c4101d070401c86e2854469402103c6100c0210f02510a545d00001541005d9143c1444000480d40d24441c903c5400030980e5541c00049548a101c49080d459100040a0300e0500f95a0b4003120300c0d1010794890754a01c02540d0b0030380300100020408999001d040c1000840c0d041c1c0d1120700d5490b4038400c50100342d805020740043d401c030035541d0740c07035003440340b1003030344000460341a0202402660ba44000022003200c10750b94a01078114040324006040b0788088511a10100e001c6c600003003d0081c0b030350000d40040c1000b80100800c2035541100e07105e20703000180c614040e0290050001242d0003030311468981100d44c8402d2100240d20b001c144ca202d4051000425090f9a03000070a00c0d00080da40184c55010070f0400c940704202d030031300503031901c0b14010700240100d00300240010028070020300100c0c2c00103002d403030245411308d02c0e0110707054285005207086846405000e003202161f00c9909101c0000d104000c503820602c6d0105034602000001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 604041834 1250 604040584 604040587
    0x30405030c06070201170910180c05151b0c040e0a020a03060b060702030a0506070806090f0c0328060602010e0307030203070807020a0302120102250f030324030309081b06 75
    0x100600025512980303080c1d041101c6e81c000c0b00b07801403005810500440c05000100031410712081800e0840c8d8080c80c030814088031049402c2c0108090b07510110030780e042110b860b1803c81c021224401070b0312413160040440a8544480d104c10303031010a045211000645050190f00030110206454071500d27100203501680f030380c40610204013154081e07000c2c0c01c0007600280c9842c00c583c00080c80d254201004440d141d00c0300082001d0790b0341c400c0919400410603204150681045042151201002400307041c01c0c84010001a40010f480041072003c40c40c0700110b544a01c0036403100001526850107890095801c140511050020010403965801d40541c00365003003000355910f00740c4035403201109a0748400c40c0c42000c00540c2d50b10a010041c6003440d000140e4484d0480741c0d0507000740d2164116040305080910400c045422240714000c1d04c1c0d8146000100c0100d2503194403008900844a400e1560380542c01208158005030052f00307842d00c913000c803812140c0851203541103620002c4243c4d003200c0d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 604043084 1250 604041834 604041853
    0x108010b04080d1101020c03340203030a0c0f0c1509050618090907080102121012080f0c0a0c12020103050c0c12160f060f0c2f010e06040c150203040503 67
    0xc2168001c1e255075503480003529200124007e945560040c3d04580c1459081202c0b8164808404950702c41d020403508411030314403141e80021782c8038007440c031600c02400a0a10607200f00803102c154854010b50140003030580980743d01804140502a14524000c145080b0380400c4924011040c0c0f51640000d01c030b0740d0001d03080d42c024007440715405010801c5078464004007051001c02030010b0440004686007010545c1340040c48001502e10341d500113280c0070414000b07000864460012076901144151510760750308911407059151200302d401c0070381500310903000800d5a0328948400c005190007640d05107c9912501e9029845108480d46c51040d5031103c40d00c2d400c0d00e60244058031041440170880012009980c4034002c820344001c40c11243e050b6203100b0407100001c1c0340301d8948840c0c2a45413009031102d80060544a018074410103281c060220b140702120701c42e01350400400b80100703105032191810103141c841d020a08500401c0c103d880800320711800d083c400000c3d14129500140181044130 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 604044334 1250 604043084 604043087
    0x2030d140a110f100b0307060c02030c0d030e041a0411030126030d050129160209060a080a23060f01151106040c06030b030109020a051306170c0108010b04080d 70
    0x101e074035800303103150140c0d1040c1d01c48400203228228500c085a0008117207107a81c4401c060500c10141c000b8000d014800078241c01584001446003003041040c0c03464040d0b000c141c00e064400b070000200c5942e01906101c0741540820010100800c0c80205070743c184034a0008200120107400240503210b07907064000a80d0000c4403496001c030903021950000d072071401074140000c0c01641d400340c000d6413140301a03034a0100b44d902c00b4030301d40303038148005034500d818484012551540382002842c080d10561845010494a54480f10b1000040500c4000c1f10304044e00362074800e800101409016000741456100c00c41c003c130b400300718144101820729103182541e00748010321458400058012041001510300d4a248900420046000794002c0b104a84036916021009080d0f4082120483c007a0741041010001604c40704034120075940f00325440c00259143d03943c54001407500f80e01034115201c042c0703c0c4c0600744170046600168044203030380d09400750780c9414400b05240b00f10b00c80ca030550780c040e0350780c02100d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 604045584 1250 604044334 604044347
    0x3240c0304080c0a030807081003031d0109050a060315050906031005090c0918070b190c08190518040c0e060c1e1b0d0201020d050304150603080702030d140a 69
    0x144100c1c42c641c00d184007006282c1c5050603205045000c28164424044030b03c1e002000c5580c80014101864541425640d000389280484013004048108200c060801c3c0c0e80503081000c090310340a481e205100d940d4020040c0901070340131381d0301c00004003080c000c507203400c001c5084c034411503028000341140c070200c0302080b00500700184151010700800d1440d00b016600e11081d28082d9401183c650103500b15400c0080c00c040d00d41d404443c00401c2080f100742c42c0d00441501c8076800340c5c0740c10104652034850030410781c01d00c6810302003001041d031400c0d0a100641c1040141040c50b446100e00c00141d600181408107c0b0302c0d203480000031a804100c4000035150090042113190281000d8411054050b1001401c8040c080c0f4000442e070440071190840e650148101e0030300c80400c1b111640110342e42e0700040c0d100d001801822040100000002d414819a094520740c010000c1c3c1c402c00c000ca0341d84c100300c0300c2c6401641c0102c0c440e005011851000d1031080d4608507041c05805107407413500c0c80280c03050f9003c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 604046834 1250 604045584 604045591
    0xe071d0a060306110a080a051611030c2506090302060706020f070203150a0b010306030b040605040311030a020a0c2c0a0e0102163f03090807050c03240c03 68
    0x3100c0c0c070381c40d000c40066100c3c05100310301320208400c161120400c48000e0400e60008007202c1c103103458441000200c00c0c10800031000158503042000d040b481c03050001c2d080d4496404a80c0d298462002105215851030360700c082c0e00c0c1076045400d0b42c43d035141e4100b26038200740780c440a0340c400c00a124001c0441c1c5594001e286d1258402c08440c60000c803640400e044c07482d440014926810740b2010440070448900441c85840360074039041201509596906a04000280c0040c16081d0742c1c200060030103014441d082c601c108110100e03030b100c46990b24000c0da01ca5036024203d0f00211222400540c101480c044025250000c540c90a0303182c008800c100111030004000d076040faa2502003990003030000b1310080c00d0f9200048480114940c141c01e0013008101303401c56054010f0800500442c100314071000400c21014925038900f041d410125080303000d0041284047c00811002590030104240040c19050380d10003607003550f081820484941d50b1000d0501460382040c400c240c00660500c00f40c4004650 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 604048084 1250 604046834 604046851
    0x1f060509040b040c0c02041802130f09140c01090f05010807031a06160605250309050a12080711060114120a0c0e0a0b0f0f0d02010e06031006030e071d 66
    0x1d0b589038200002d0103039040d1003140004a0340d00c03054002541028003994402c02d030408029030300405503901041c02c0303030030722050500211703507030070030090920b9140d04000b030183d801c40d104e00c0e100b91f502590701d929802d0440046d8040360f0b0b03038000000c0042c44507141100b140c81c140c5850070940d9494605902600000400455110b00e00755150b03440e96468004c4d10003031602001c0164080d0312494075004841d8054451034844024000c51041500b452040e01102c6c603607840c0100d01004546852440e041a040c0c00910301200254102e51591780200400d1082140f591090101d02c281020603403102c80a00520591600da003064401c6405c1c000380e4600c0140c0e00c481160750030313407668854000075a07558202c003035072000302410b2104200321406030311044581102c1d00c2100d0740d50000000c045502d50915540100ba80c0000d4006580c0554205002210003400c8550f5a2078541492a6210124028000482c0ca400c01480c040d510001d0f4800c15140294a0341d207408019070449604200001d00741403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 604049334 1250 604048084 604048091
    0x601030b0d1b2601060509040c1a0c010f0b03010c09050a0603090302031603030209151204140c2101180b0a0213030c0b0406082d0606130f0602061f06050904 69
    0xc600d00c1e8420740380711841204030312081410f07041107410300303690381944240d10441a1405200116084d4603e04040701c050755545514080c000c02d000c00c10b4000d24980c20459464990348080319441500444824a0110000c10079220001c030182d418046a0046903000071492070284140382c000e48c0155401703406801204d046c1510710303655003d030340ca40b00003c40000e9008180304907581490018a026031030b48650b2207062410440700705141d2400100b016106002c40c0c105005a000700f80582080d42d08003501c0c0d443ea511400d0040c0e010091000c1210748c0641c43e021040140300f46d8195024000c40d40860030b0007041d183c49411001079000040c400360710055903400000020240202240289243c107912a00e45240080203003580c9402031a134241102c000c0c408480140c0b5141c86103d10100c1c0580c40c214584503c070206100e400344032080b0340715000c03543c800300727160050300d1050044414540c00c50740c1c00c1e41c980110320101c1c0403005040050a00c1c0d82e8007440031500910103410001400390000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 604050584 1250 604049334 604049339
    0x90b0c0d0e070b040920250516031101050901080c0d15080109060b060301030302100e21041401050901093b19020906040909020619090e0601030b0d1b 66
    0x240c20702d565540441c014900019007001a001c1d140a208082248001881a400800c040c802c3c81440360782c0590b86c09160202e540019445801d60300704103190000d080328aa078014200b000a5035180740170550b140c0720440b003000020b61140c030450720321642c10b0b5246030301501d91410b903400760742088140841d07a03900c1d8807414544ca01d0880c16040248108000070031101603a0900c0e4040356214140385010300400c05c010701c04070790000794032a9103100144001501c540041c20003820b10a18029030b000138010341007144411741e20400074000340c820100d40304500c148818015103c0f0b01c641a1068082014401d0070400c140116502c1e03a0143c01404005d4200c100480099114680c810342100d000d903130100a00000d120f600b6100194148881c10441c58401c01400140f4603000f14858000e500d40c031101020219250300003921407103a40b030703402e2901c20348a804000e4101034403030140310030014a43c00080c2c540d40c800d004107490604060075141c104551601e6604c400052036081505126121100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 604051834 1250 604050584 604050611
    0x306010e100c0201032c0d1815050c0705040c03060314010209010e130e0307081206030f100c18080105091204030b130201020a140c03070e01031707052a0f04090b0c0d 73
    0x15010403400c03031b0050400c0d654401c0002d0000380c061085901d9141c50302c0c00910021407020042ea401104034200039440e03800042005192034603982009030020305010340a00541d800da0070402c1502d102d2181c001c0703000d41e80ba0619080340200c1254a0000d0700c00360204000e410400c00e04008105249000710302a8540c040092460303000c0c102c202d84c01c000c000362400c1e041c2c01e040801c9422610880140807041c0507030b08595901c0d00d002030380703140b45030750b826002070075502a5400d00302c0210f01c2d540308640030713688514090080c901110079100034054200c4e811042e01a190890b8140d0382d021441c59950788400381c81640620119204134107500c90030140340045149440c4074048480e01c0030040401240240a05007012040c0d40501820380c2440014000035402070305160b00b04044c6c80910340c9858007410320030300d00007882d450001130b480070300e00c0c03101209010b10300f892100d032094031170010005a00007400125164644c0103007213076281c00301007003002341d0540041c0350342880b0b10800300e0014100c5c01d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 604053084 1250 604051834 604051901
    0x705030325110a0605090a02190305011d100b0609090a0507020c0609030c0405101505040504180201170a0e0f01090203010b0307150f1e03020306010e100c020103 71
    0x18580040380c07030054491079100a12a181d40320a20510340b5480c8100701200150b5542d01c1104003c20342500c40d4001006458200410003140e60020003482003900a40c0c41c14010755054007040d141c5500b04400700482c5030320300025282d071104603070080c22000d4101c0072242c001c01ea02a06268421410400c1c19550b41d1a01d20b00c502541002400143c0c60a2860303020340b0700000008074a004040030310140c5141c5d038000c07801050102007034601007050707654a1189220000d650704200d0302c4452950400c4800c40d4403201030026a00180c1c3c0800825507003510030085000c460700002c0c0000c0518051541c03040004500390303002030031600c0c04101e1402d40903601c0c3c10000d00f21061405a99070700e48030800e5203824091148491010b802a00031141403600d040866a0f080c1900805d10200c258141d007034a20a4812180b4160303403507039024180d040e1080040280d0b106a521038001b0750030300d42c100c11a1800f003a103070b00d51503800d44901429408990045d0040d10508113241c6880c07101c82101304003c0c00001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 604054334 1250 604053084 604053091
    0xa12120614040c09060e06030a06090e0a11030303190e0c220624051602031506010e01030e030904090213020307020d1205070927110309010c050322050307050303 71
    0x100c1c211036207082003061004949001902c50308110f032040c0100905a042030007040f59850a0b1903e5030390307565401440002e061940d0000c038a66280100b03220781c850021984a441a101c1c10000d481030052408040c0d40340019142180c45030300100002d428804168460710895000707101365104220b03000300048140072680048204c280c0151504100203d8a100e03a80182803050109504503d09000d441c83c442c0b1600c1d041d030244840054510340010003400407201896000781200d0380c01c0300704c40c00720a540740d080c6d038520b0114411044149441d80a40140281d06403100c0040d0f050491041c00c000140ca91030303005070b0f00701d000319200c000c07281183d00055114000710740050041082910000b0102e42c1801c00103040c092600050006181d4041e142300102c441d00301420102c2c1e03905100c6808242e408910000c8113500e09210b410462014002852003120001c0080100303101c01c100c01d4545210868890031000013138103100702c40220320658121418084c00c1201e00300031150351094615481503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 604055584 1250 604054334 604054349
    0xf030306080d050c1513060e0c09060301051603110708030f09070b0c0304090b042a0f0201060608130615080a0c050607030503040f02030c0301060605120f040201020a121206 76
    0xc000078415641c04024103601c00b25549031080c60521450744a94442c3c8441000c05e592030b400768042103241030041541024113403c000c0401c01100d01c008403e50b12051400f145008410503000038010b4901880b429104170414020000c1e54540304d0000c400400000940743c20140342070010b84003080400024510401e080d6980b45030310305041480d00c1c81c00010364040141100100214501100c0202c162070071100032020100d004003c80d000035001e802c100401d4143c41103e0300002100d800418622810314815885844440c0f68000040f401d8803034502580380131480180c085681c82145e80d051b000038602851000904114005401550810580c03140c001e90744580640800c0c4280e1112900c010716003142c11034641144e60750050600d000091016042d003a84030191425034034180081c0c81c114200400070000c0b1503c4440c043c015400a20750505a00322110000d50004189082c0c2c0d80903d80580040c001418650f44103426424100c07140d5040040a9200c00c1e0030700d040380100b00250444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 604056834 1250 604055584 604055591
    0x908031305030d290a12260d141803070b040609020306070918150905060a080105100e010f0506040b0c211b060114010e120312041502040b09011b0f0303 67
    0x203421004c2003140d1561003881800c2007074040180d0000d6106400805500c40b0b185002c4500a603626185c8a42a143c81c6002038000600c690302c090f0240d1210140245408100000f5100d04240c441000500c04660880340e100f0090b60010032802d20703245034810f01c00c0101003445419540800e003881c1d1309441d882c0100f80e4002c800e110070300000c09a0f50000c8141c0d43c0800214042c150001056a158482c01c500c15a9a44c04182d440d10703000e03004d80140c80c50030000e009a0400407004081d0016620442150b100d024002103009c8010019030411070310001c00e00c2d03052606028489003554400c003d4a042c81c4540c0c004461104481070fa908062200115841d8844240c00540114000c1c41c540c0704650fa0020001401040304420085608103c00e01e00000310803850320124268030b16900400000e0320000c42c80c050f04507200a03200344603038480c0b03044002070040c100000059026900070204032400c20320584000c0d521a111001420201c3e859128001c22603484030303a140c519441c0280c00107038a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 604058084 1250 604056834 604056881
    0x16020409061d0d0525020f0a0e0702100204080a08131503020a1407030206070503070201060801060e0a0c020d0804060f09020d150e0c091303020705090a0204080c040908031305030d 79
    0x81c0403c407203202c8079013060741c5030894842c94065244c004154003154030070b060545e5010754039201b1044500003c0a08449080b580f10380040c4807040044545100511403880e142141c00424000d81e0304680c1c5d80c2c4d0080074520856a00c070169608a0890300044002c10400050380c50b001c20302c800044e0385103072070041c2c3e03800c2404c2008203401c000c003032201da001c2010410080000e60005409a0084080c41c02d035840352a4503000700c3c050a4690f100d0030316503003891008144a0802d0a80034002e0703441e00c108124484030349606a8880c60341000c20408110f4401c00140452520382041d100c5c10200640081ca80d620b6a001850085800505407111000c0d40403100050310240704007082c84581200424144076080c00280c50008010321110456002c001400d08140c001c101900141070014684d104074641a025400250030a1048142e01e118801d401c1066040501c01e08507d5504600c40920b150345103a031821400c130b024402294148001c1000300346045c4240b103824145510200c1603543c400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 604059334 1250 604058084 604058141
    0x10e0d0e040b09060d060f02270a060810140f040528200705100e0a12030c090501110a060c0507020910061709010603080403060609140601051602040906 67
    0xa10b86a0359602035222402406402d03500c0f2681e21301c00d0365000c07030003048540c16000641d0190240040b40f030309003c100030448261000203881d03104d17028000c2c0d03400c4040070750b40c41007140c0e140d02c1038a00020140c1401d0080c03041030340104082c1201000640702c0b200e4010400c02140403103400311040351404901011700854030750003c141450300b00c9440b2051198000c090300c043d2040c80794020504006000240c4031040000038405280c0c01d0703100d01801c200e183c01110710281c540303e400008459000580807a00b00150083c42003507180f00150b42c0d10011030f400d041c010f40d40f902c20f00582401900c20300e80c2076070000f201406503000c43c00b407540e98207071610700300d20502c820307108007600c1c1440c3c41c880e0711011700445501041c0c600c40420081340048540e159100103e0040400d90030142036914001004010300085400100407606110341c10001d90302c2140d504224401c0564910740001c1c81041240502c05480340c0404000d4001032001603001820b5907008211614094041c4da410903030300034424001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 604060584 1250 604059334 604059341
    0x1a0a030b030109021c02040603080307020c10050309070e04031110060810020c0d08180a0f0b090d0807110f0703060c0801060507081210090207031e0905030601090e010e0d0e04 77
    0x560268001c1c0990380320fa03400188122501a40843c000700d0440d2540250741da9030f080b440c02190031200e0f2595074207080000a40740d0401000c1c160240c0e07100d44c001c250261050003200d11561000300600714150400c0c1c92208185000b0f0010b0702004500c2a450000c218240f110300c03a8402c5010000403070750302c1d00c0300c401d0912840007007500035280b05110141d007028011503104851100341c0381043d1196030398001c0605076490b2064022082c840c105a03041000042006408840d01480000e04150b980062556954601c01c2240c000a0a080c000c00d8500d030040c1c800581d4181c900302620b41905c1c50808407490a08590310691b0140d403503025803484280c00080160142035586002403410349c1d151103e94a40c40356115060412111000082070b040c007100814001d001c000805540d143c0082c14010003100070204000d03000300c039a488132070700203015440c850100c8402402a10042e807820a03110001c00c043e00480350f003552210302c081c0301c0c00300910112041490548401c00c0e052140b80600048 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 604061834 1250 604060584 604060601
    0x15010b0403110402090303120411120303010b0c1212060a0e0103023d08040204110c1f020708071b0906050117040c1a0a020c0103090f0605150411210403080612071a0a03 74
    0x2801c1d0041955410140100843b030540360308818455881c01c0c003162046c03501d03444a00c0c2001300200800c128401040d8010780c0d6028100441b644000e01e9203d440307094030520284002944030b81c000509a803215084901c0700d0320f40100c81d44c00400c4507206110354041d03025402102000409940c1008114035040c461070350345501d00c5071021309090002c4000d9035581031703045071040b101c4002c24401411030191740481c0c010561082c03005403a0580341c40c000307004180070040c24014249451002c0f820a915200e800c1c11924169100d500a0340d1100310301014150150094407a408411b00110760710303094200ca541640d011034110755403140c003513000a050448480201e0704160030002100040348001c5000103105400c902d0002d55900d1b03200009180d011000c1c8041d8100307041040c8400c07990b0070301c030240464400070003500304242d00043e00900d07040c100721001070202e88902c1c040b44081c2062084c0440703841501d0300301c1e001035031500c522080205481104401e501c0380094100700503a454002c103d031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 604063084 1250 604061834 604061839
    0x6050c03010e010b0304060207120c140c1c051204080a0c090507020c010521070e1003050615210f0604110a120e1f02040815010b0403110402090303120411 68
    0x555042c5000303500b8000041c460f01c080000040301083c140a01c03036040310f501c941d1001c049405524600070103426000d00035000d407448032403290584409070000c1508481c2200081002400100a290b145004528104141c03101d2150b502088815029070006002074101a0018000306002d458401280302403600056840b40c1000240124a600018200c2e1041024240107840300c2900b45801405007410380c0a0762081045401e21600c01e0300002d43c4c011102c3c080e2850f02c80340860000940558009a940c00d030840758411042c1501e10161000d492980c0d1600481059010421880400444141c0d41c04071403000000505c107642c0f600f4440c0928100056920b13909050745d980d8040c003d1400c0e03821a0001d01c0e1200ea00c0b0660907018880d215020b03c0345c4046140000304091010020b41040c01865510305c5002d0309410b90006001104c4d04a4007070780f07607040c81c20b82156901a82d050703064600e40c1c0c01036001e001854041e1f4040c000341c038201071101c00d01090351416081c001d6003040305950490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 604064334 1250 604063084 604063087
    0x501050a0b070807150b04050f0106020f010b010e0d1e060e160302061c2408060702061003142805070504020f04032414100609050a0315110c0a06050c 66
    0x1000100310390207132811150440c0c20300700b19803001400326001e4a51280300035131003403a200410011004259010b41a50031366801c440c00c080d40070b60414225543d80c04040d010031042181c001c41c528084e920304030401d108401c103184203150a54034008180c0e041c4000c882290701c03074154000d14401080140107008a11103e4220b40303240d40c0101e44188269160706003100349081d1480d03200741003604201001610080e0401c0c046d0301c440c1024140c200b0794000d880c41c9004980100b01e03207d10010719a8010b0400c4106a0029460344c2e4443d03505c80c0ba000030040b0180540341d411613401c25918003a20748511050114101d000305460300a0030300760141c010303d1040f841402090580c061941c01e9a080e070303a100c8000e41c0302c0c0380c003c110b404503140c20752240d1294506107803000c8144903e091850380540e01005407089070941703801095400045901803150880034450003040851354041d85600d000d903400c1400074000e400d01c44c40501c0307075004080502d22a8058081e071810400a403060707035400140040642d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 604065584 1250 604064334 604064347
    0x90a03020c1f030b2407110906010813050c1908060f0106080114011103070807030f0c0314090f04110a09120809120f010509150c0c0c04021b030c010501050a0b 70
    0x90001c00e00d6030b01c103003040550729205210562503011312200c2c0d400480340040c81c420000d8400710307040d40c4801c45c01c444604642407280160f0504030703145405140140c4540900341c0d240c4489225000007a00c0c1624588185620142544c07501e21307060b03008987e5140c00714007507828511045d00d801400f90521b810016404010803d0903805003c02e41555041480d500c6115403000048405000d9640c604999002c0040d94008100c0540020600726110340ca48100340141450300782d4a20788400ba0140c0416014880d8841701d4080100411002c1c000500003101842c4050206044803881d601c3e0400c2981c0000340310460301d80024096004000854150b1188000c81e610b840690007520403090064802d82130b100e010310404c2c85004030510303042e8000c104528141d84004e944411401500c000d05101c003021a68080c3d04500b02c83c41c2c0c00413980284040c48070b020a000095001c8c406110441d581410351051009013070004008800000002091550405040128511280d03000104290040101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 604066834 1250 604065584 604065619
    0xa2307030f1b1205130b0c070602030403051b1c0c0e1b0409050a020f0c0d0318050309010c1103100548040302130516020d020703080c0703050303090a03020c 69
    0x600c0d04a548108032045003144110240c2e4140510045d030591081988000710341d10040f8005001a200401d04480302c490740e401d420b9880340b08034000074080b9003204404c982414940326452080c90406050b4020080030109641514608d01c4811940b007100e0403001c005544044002c2c41d00500120000d5548403c0c50b005980948198424030392100d890f000000d900321300301c0d0b042d24140044042040d65401089990780d440d4032040400801103890226a020000c403001e001001169000004610780601000191900300c1884422205062620140142c580b0140402544000403a0b804541810200844140061002280250314903441001e400300c54915800384401da41e81709500110007210710901100384120b41000c1d402a10408124100712469030055129584405400174089048042261a4489c0a80d480016400840d0620105407007100070034452101d8011226044d50700c0d620907040d030f00101d0b5040d02d543c110b50744150a240d010301041d00f0014040768240c96100340c141d070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 604068084 1250 604066834 604066877
    0x103050114031905010f053903180a05031b0f030304080301170309190302030d18170102090a0f0521060106081e1f09200a2307030f 58
    0xe06040950803c0000c030107000080d4440c122900c0034000920071881c0c200c911380c5205201c0e41c01d407282408082002e03010303020a03103031103110002c40764105032641e280c0000101c85201042501c2001d40207400071600059020401000380b5611003c4101b00c426500f1051400c0020604684d05d4a03003007003040100042662040300d05440d4842c1c100d40301c0310500c1100d54618024032240700c1e00090100852100c403011102c0b21000c5902c00c9003140d085003c60780f4111451f10b8980390320700455205150900c2500198804004429000c0d0001403c01da14000021516001c5501042c030b072680c19507040c0060704000f513804040610210300c03461030006800900e551440b05110307400412400c400840d030700d5060ba007010f070f1250341a00c41020843c10311480351011035081c10002410701400f03034400a840207080c0210022600c002241c80120301d000385002d1050b80c0280104030400501250182070b0048040104404030710481e195925038000e8a0003402c4c070200c0c000550180522011039035400410b509 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 604069334 1250 604068084 604068103
    0x60515030c0c0a08040603020319090c0311010c060617070501050c0714011b030228020d0f210c03126f0501080c03190207050c010305011403 62
    0x40119540c2c0030000402d428402038280042500100080004d10f0030b6150300914006c400d0700b01c0205250f54210700f00b1044510541c001001c80b042541c003080451202c2d002c010302d01006050a402c2074019035103034011140f05401c2541d074043e600100c2045c207074081102401130f100a0034154502900c0071111343da60441403194604070300940c600d40c6a142d2007800802d04004821840c2440070100d03140c065200c2c01c0318098501039002c42e40000e54120841c3d482d44078115005441c4c500b0038441a00c50355208212030b20207846a425810010030801c541800500e40d0020503034405d0382080745440c0041c074103001228000b0f082d506280141d03503c42e10394892032100c43e022010405280c849000f9804800d62170719004a41680b0030001810400741092100e1580d2000c1a400c03800b0080c11400c0d042003030013a006031030000d901d585c0007a205800540007160032984a40f80c0d42281c800e102d0854083e40d02080040729240c0050702d41015550b00342c051580901000c0074912a4003611201203641c0d0790080707 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 604070584 1250 604069334 604069351
    0x10c0b041b1d0411010203161502090d0309060e060301051c1a1017030703080c130504090305040504390c0215030103021f020c28060905030106051503 66
    0x19403a86442401c05540c0340000c1610042c10b265034582800d01e4040c0c203508031410707200b600b144484071102c2e6102000315090000b011040c5840c9800a40342c0c40124894400269031240e42005280c00c5603480c4038403114020700c641c0d1450140c1d03003440402480711038040285402904103000610140e0344035050311101c41181c144005001d041d42c1449114404004041d89179412058203000c201d005280c40c8105595000080040710000525695a0ba20130140e010300080c5248010400034a2a64024240303481c07081c1440340f003903445030002401c64204100440214000042c02c100c2410301d80295400d00c040c2c03440601596501405c4443e0071340ca00e0642031400c96100040000c21401101400000307030300901001850040074040c1601035201f8081039104543c40d8849280a42c1010807a18440300d030782d070152030042080c0c01844548004940d140700c0801101e401c13101d407259003012103c02459150348100604d85040141800c40712190449401007120002695240b12085c1c00c03a038001070307070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 604071834 1250 604070584 604070603
    0x3190c080a1218081b0c0906010c0c0e0a020a0e0f01080103120c060f2301080a120903120c060c03060b030415020708030712050105180708071b05011a010c0b04 70
    0x401e40301c801004250501688120041c400704180304c0100080c021441c0441c480c0c0a00210078800207035104110b60b00d20b64007074200b0740050055441050348004d090304c18550102d200f0703203400034100210003c4030071480c1d8590200302c180c40240c1c00145004403d00a803072140c0e06c1401000000c0900e10140809044d0300d054069090a00f4480e005501129030050400c1003891505280d0102414070120f60074000c10001008004013002c04042d981240d0a90000303080303910702d81d03032400c00288901440a080c490600b6000001c1070006a144054201035601c90340e00540a144c2101260b59090300300c0101841d2540501480c01914212600244c009404270035030b45280007070401922402a0003028039801006005856801044110100c50b10500030320040c0c1c0ca510a020f080341110780c0b001085008007000c100311501840d1503a1b000050ba1514020035400c4101031411000e2009080710503030340d43c0b891521403020407035800031091401d181101c030b1891140c6406d808094050800f81c0001d21 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 604073084 1250 604071834 604071857
    0x901021e12040b0715021317150112050f1605060c0319051e0f070201030906090c0b04050102010e030c0a0311010f0603061a04060503100c0e03060903190c080a 70
    0x102040039100d044181115103580383d032100c01500c165013080b60304076074201000c00403d50458050007031f01c02d62110010604178052070021400035401400c00440902c0c0690b2030008601001e00003c607001e0240403107440702c2c1241d289070031403418411104004d41504440130030102c065100810108480c0101c43c1c0980701e621030885507043d8440d83c0141640903041c0c09800c40f280d604440a00f880305420f00404064007120000c200707144c41140c1c880e20401c40704110600066020307901c1400001d00030540003820081582e40e8140041c29900f103400042804141044550b07424002c0a280c24121360146051034190301c0084e83d281c20a01c0c00409000d02d848041061000950000c1e0094101d9881449015601c1c200680104010040c803241d403001e86602c03a02c00d04150103140101c1e000039000300314120400407000c00800d03580e0904d03c1000300c034008c03a000903501044058003c00104c00559980c05515400d00b41d450b00c200040da043c001d100d0103aa010456a0090316000c59032800c09032a000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 604074334 1250 604073084 604073143
    0x10c0f030b012007080f03070b01060f0e130204080d0e030c0906031609051b090d0308090a060f0230010509221a0105010912080901091a030f0c090102 66
    0x3014180c10f0011070b8019040303410400d034000392040484040100f41c0710b03003103800e4413481d40324403482001800c00d1600d4401000b2040c440d010b000b51030300d1a403801150010003203001841c15161250280741c1241c000c0740078000290103108100c5030185070304100d4014001200400d440700f190000986c455a40b040020348a17031000d100300301120110b0405606100c0e100ca45a00043c0401d860141c611900010030004040444013115240000104140320151480d5021900110000c0ca03407070241c003c0741441c030002927407401104c038010104440941c40d10890f9461800200c11042e100c0500c036048241184410303842429581581d4041d6000440b9645070301d03e864000d0803011805030085006501e420502c40e1260300c092a516940c0d80da981e040e40c0c1c2d000110f071007038598064100c0c102c02200c0b811000920690041a85440606280d1003c0d5550341200709044041c0070a022140400001c204c00038060044440d803100924070315604010030440003d55a03400070441e98000d200f09079407541d404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 604075584 1250 604074334 604074347
    0x10912390b04030201091106030106080a0906020c010c09090b0301020301061e090e090d030e07080d0e04090501050705040e01060305071d030a0b09030705060f0121030302070213021803010c0f030b01 87
    0xc58228503000341a06051a00030700038420f0320000d498001160030f420b401407802c00308803030407103815564003001600ea5040d400000c041041c0102d41c15a800c0082d45c52814082c00307204042900ca80761101722518007407c280036a034108001c144030340d204100511066401151031079400003484280580c0090301e1700c050313a5210070b54001c0c00c4419481c0c41000302c045000540004072001995092183c80c0142c40b174980d031030a4901810081d50452811004600d11030080751120b0f4800510209211104d626031600b10f90f001e40350701000400025040c0140c00c5044080c90050069107410030562512002c000d004650000c0c91880e00081c440451047e541e0800401c01c8890700b202ca652402d00b400010503a6035841140100e403c0d0150400040806040010190484411303000c6a5a01c1c480403036183c0010034013400450074107500703211070f50140e02d540040241c122f5100e04d006943e1208410300e00d4601c901e081c0807900c01d0f0f050030b0001c681250701044421a80c82c16040105142ca24240180c0e141c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 604076834 1250 604075584 604075697
    0xd1b08010617032a0111030105010e040b032e02030106020c10050a020a2306010b090a0911030c07030203040812070204181a0601090e0405030a03051b190c080c010912 73
    0x240c5d07003400f0401080b1400c810080d8101e03030090300e9403c50041a002404180c0e100100d4141d070503080314410041c003180c031042c1414101180580c040d00040761030f9448080f6082a0004c0c40103030700c128000c1955007461506046500030310b0800d10f05052684000a5035800c3c3c0980050112030000100b4520050b05903155400162840950f10f0359a12811041000c1e004250180d1080ca101031000a45082d284510b44030900c851350064915a039280250141d82e01680040b81184400c100025031401e081c8030380403c082461000d07942d14101c41c0104420b0b03030058044540c06182c0c0395000400150041d0242a812007d501392034602e80d01d49006844a0b42a648410b008502d05400c00c020020040001d02c4400348545003040541c940f18900d0210100e030805a180b686000c00c40134244200c1164480000c02c040d103002030f05000b01c1d03035a0700e017207400a1422585a030b4549861400300702c0301c40715181300e02100e0325003a14100d0a2204200180034802c9039050049913586103c1b4103e9481ea200964 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 604078084 1250 604076834 604076917
    0x3110f01050721180e150a08060405070815060f1207050409030905100f02100b031216030305010e060a0b0903030906070b010f050f0108010608060d1b0801061703 71
    0x1143c0501140c603100c8a00e1403d00c00001c600c42c034001881d0b03024086410a854038090620712680c0e400200c0c00c1c200c1e0304195403660000150030002043c0c0410480e580c4514407400203840e05a142044d050b242030300d41d07042e42030580ca00b0020000c90303031100003d01c40e404c0001c5030300f028050702100d030107802e00d0100d4004136001814001d0510602d45c02c40c2028003181c0e4280c48446030210841400c40c0c40c1c8040460700c00050300b041100c07418000503900302c0001080001c054410841a03450702c2c0f501c40d8044400102c0c81a0418052410306400d4800d171401400907000350b840c945010800100c581c8445d0003513030300600000c02c81e117070a03480400a131140b814000c0c00250356007159080116240e54244960100c0410b070200100d0217040080c5900301c6e103007041c2c5802d03001d41d0a059040e180e080004080d541c105d01c4080114000c584980c211040981074601c003108000c0c20420150f003500c085411140c3ca060f603151440000f0407000003143c0e2001c454025955085007010950508908413040c2c601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 604079334 1250 604078084 604078103
    0x120605222018040902090606030a0e1506120a05030d020c0304080106120506150105030c09030118060f060b040e04110d050313140108130303050601030f051312020703110f010507 78
    0xe41060940c000b409241d080a810601c1a4449410803003601d2000e00e000f50080307070680114030182000c602071504404421008175507218040495480c1202c1c5083e076900e050844410300506081c405203405580d85038002030001890b460715582c4e40ca204020107504003940c0012801c261050500513a00504504002400030541d6156003ea4180d803003141541c0c28003844012480c01000031a2028441e141038481500719aa5101c2ca502c25400c0144080d405540700c0b466039a00c040185a1408000c0c42448001003044c400d201e52012a281500b0201413254100414856141c40c03960259010b0740c05042e01414401d0b180200e5544200000000c10911001c22801001180f1140320703016100c00300c445159030200c60b0011104504c060b038030f84203092000d004500200b07210b03030081603002106040c04180c2c4030380c1c48241002c8850403215411103402041d5110200300001155104c0d245c0903100a00c032031411900c50042300245598158810002e080001829134050b40c10b540c0032a0300b00d00d046 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 604080584 1250 604079334 604079381
    0x109110105221223100207030c051e0f031608070f080d0c14191413030f0515041e0c030c03080913021305040504060b060301060f12060522 61
    0x203d03030001c04008126810a404800c0b160840b1a62699690b400c0c403d000410b410030325003004074025805643c0c25402c000c5c000121001160040040340d1980c0452880d06c014950002c5455060000b4400c01803041d0300101328001941e80480c14080d255900148201d542c1c0700c443c9040001002008070041c418080800c000f40c03142030030b6000000155103a00c0b002e4228490b000000d40301e02c105100c42c44034640c2020440c1400784100c803c0d02c42c110351340c00035501e410740c0291700d2002c914107503008540c06d6001f00013500400c1003c2c010311400413404003203030f401d81c10999540440c00300c00b101401d51444c280c001580c1440364031040d0304010341d000032040c012a500c0782400052039201214071409004640804030b0900f602e032084880303040c882100034601500745401c003c0034010280083c0d0312184c5540c0314411aa8601c80114001d20b000e840b8500038030b20141014010380c82d000e40c080b8126140440030041030b04c03071052040034000403c00c2d0400301c4c49030300c81400c02404202021802c038403001520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 604081834 1250 604080584 604080599
    0x207020d080316031104060807020705031002070201020c0604260312070903112d06130f05010822121b060c17160503040510050702070306050603010911010522 70
    0x710300a150070f0205181035140608143c003565000b400d140e0504e0000c1000300f0100703114054454000d10503105441a02d651013000a281101c2203021920490340094a8011982c04000d050001036040e41d0050a1030700c1c000c0b007003820071801c0b131184007104400c80207400c9130001401110b030420b1405280c50440c0c2007465004103040ea05010444400d10500c0c00356504d03140c4082000e2420b0300d441100b50000410110444481502d800155003003101030107004d05281c4051380310005404545a54800b076868000010444000134183c1e00e1030403440c000320040c82b11b0a00c54551040e82080040156451010080700d0314102043c0141c981d00504804800304029904914211001c0b07070f4a0b03a800e0704005520010031542942d0032042c00030031a0000b600c0c50300520182d5403143c001c3c0c0549501201c00352100c1c2c2541c2c4225035406c0143c011030401d10030003159100f01c1d80c00074001c1c3c0007007000d03d031265107060011100c0440706043c00000f044130340042d4080413200c20061480400c422446984110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 604083084 1250 604081834 604081837
    0x20f0d090914150f0409080c0a0b01060c08090d020105071b0302010e01020312010509040f05030708090307060302090d02040f06090e0109140d0c0f0503041716060f210207020d08 78
    0x103040c0700c1504103801c0c080c0a00160902e03502602222441100c2c011003081040000c0c01007052150b0002e84568405000c5040e000151041000c5480a070844404a10308000005016000038040c44507044240b0041031050b0181c8124100944076000b1540d90303400145e40398020010000c10141a8404545200900c0320807078003124802e80310145010322030001680c41380030f841c01e03400384980c0307a100400c00e501d0f00b034100507000b900075074008251042507201c05065030301c02007080c2e03503120000600c1c440904040010100402503031404505240700348000400c2c1c4d44256601902c540c0e2202418106180154881c0004108110040100d0384000035068040e1503800c806a039000d0b00000342030031090700401e0024611245684400f0403041a0351010000c502207001a00c2c40e102c10302c0003041421210302c06000c501000c40052105405800c0c5000c2c1201132508220200159001c0e00844e03150001c12681c1c80c03128090040c0b5000c82e0030130030f9070000c0c05007000c041e5100fa010841d01003480035040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 604084334 1250 604083084 604083089
    0x4120804110901080a031701060509040b0a031403040e0106170c031023010e150906030c09040204030b090d1d01110109060f020919050906040f0905060f06040c03060503070306020a020f0d09 83
    0x8130358890b1003034481441d0986200900c20f032404102c0400401cbe48034540359200c40b84000d0005d11074482d003070700c0391104070a402c0d903000f00a8042c0c0c40000c00b4440c181500c2292030050002e854542000e050100740c90005000160000c41002d6010010850421514240001600000143c0714101d480529a05083d580707c440040c0030a003000c041074881c0c01c054401204c0c4192288071586081070340030600555500050591102140500038405143c0e22400140025406015001c04608001c40083e09142001c040d4038240030110b01a001301952100070940386000900b01050081038404140d8090601c0300f80003000c4501d4181b80240706012607016104040080c0d031814100074584603601000035460180960100014001510524103a00715280a6400880c041001c6030140c2c1d40b603203088016100000c070404140300b000b641c0d0405214400071404503182c04d0040500e0000840d456103400e01020700080d0b00000c02c01c034018000c1288451040040d800c0740c0c0d6031941c13264000c0100301c7d01d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 604085584 1250 604084334 604084337
    0x911130f0c050301150e210604020f12070e270d0206011508010306050c0913091e030c11150a0509010201060504020a0f0c140109030201140f04120804110901080a03 72
    0x1120400380707228000ba00e040c2d4440c1d403170b03005a2070f03031100e4140c0c4c12000d400d40031640100e48207a610b20849117010040e041071041c1d4024a0141481d20422a0488106580e180124042c50703d2944070300c000503490301240d21492002410391511082d0042c0d00c002c03881414414400070170380640b9020300041240100215900340d4407143d8950b20f40320034803903649da0060005440800144046002039000503080b81e032605005180000300c50128034003114080310a11384507074400c85101030040c1c0507420300c1c94001441c80002c600a680d9006404c0644184001d4001c140146108039540c0303c100154030041c41c040a10780d00d0713000e06800240a540a121070741d0055081080010755800c142c000d0f40c1c1035130a941c803440c100e040c5c02d00302142c41c815144400d641590350004200300c1000c0a200e48850180641e00100e403081000c081442c0700040900a0440303c0107000c10000031a215540c50036a4111520304808507441c2d17818003404200300c10195aa011108400000d262100014202d800d51700c81d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 604086834 1250 604085584 604085591
    0x41e0203340e01080d0f0509040614010201051f0b090f030303010816060819050613021306110a03020c0904030302070218240f0f0109120602130806190911130f 70
    0x102c040701e030801c50082c801d81049900941c0c50700e4071140120b103240820107070340c40d0040c10f00074560001019150341750b01c82d0b2000305490040c41078550f03081c02902d6010006091140ca5804078900b041c0000c12076110b854101c040200e40f511655882d01291000c0300c40081c04c40b078036035846d01c400544400744000350343d15808010302d0010354a802030f200f840c4240007400d5489003055110600b034004e00402090203610034502c0d0990191131001d8406080700d0212205c00e041743c40e090070405080d0f0a090310504900e94440c541a900080d40050010f4180754141c2e80640035803a05e140580290140172030003540b010810582481d40e81a60340301920031640110800c18942c1c1c0300b001d800c0c8904081c20965045100c1d0140040345013441c0036503c05040041c501400a541d840303144401a0900507000c0399843d400294009905040901d05805000044041d10050404803640310780e29840c07040c40b00001d030711401c1540038003801c0510001801d0020345100f08002c101c41d108070090443d9101ca400a519 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 604088084 1250 604086834 604086839
    0x11190b01081c021009080c0f030a110a02060409021605010e0a02150a0801030b1003050105090106140108130f02040b0618190803120a020f0a020a05060f041e020334 72
    0x803800300da10b0b030900650300603000d030074130803511075000d40f03074456065036070a508110310250444200305500d0341c0c40001d0007130758603044c0c030b6240105030941a400c00040b0758085042100542e40c1c041c200c2d411503c0e240d10050780c51140c1507206030b0001d0200800340c00c951030001d6080880c2c3c40826440d9240d40f0031a0071940049201c942c01005002d4064598001010f00e070051000445401680380c01c0307a460328480350483e989607149800e4a008551166403a51150360801071a4501218000c2e412401d081c48002840c2401c03203100303040040d6a01070310720903049222505644682d8401c07040158050711b031030f070366400302030342100407a4103202240c1c0151a40084000c030201d072031010900b07655492b03010790328200103914585c150340000f0b0000c140355642001203003d40c0c10908001c000254140d0003804401c041410038a080030001040242074010010800002803111201004d0600380301d445d4141c2c0d1010b50000ca45094466900140b800c81401c81030000c00c0e02d044e504520304d50601010909064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 604089334 1250 604088084 604088113
    0xf06040e06131704060207083d0f09030e2110050408090409051005010803250302122109190807110d08070b07090605040611190b0108 59
    0x50520540000c035400c00000316555220100300c20407924041c29064039011602c0400c04107a900c5540648003580c48090704100381d0201b030010401c501382c02c0c1b10400500d94208040003c0032040350440706240d5401000c00824465540814000b00d140c1a04004c0ca80a41c680500170003806100d00c0d00c40c407807a41341107420f00b183c04c1500c1c4d61310b8540e2028048003040c030855600644001f070011100301c0d2040c44946c00e01c1d00d56115180303020780140020000446080f20581c06c81d801a082740080d600100700070300301c0d6100031021450854034410501c20082d070030708080741000032900c000c1c005040009100b201403610b526100101d0301401c20165241d80b150f180130b5655030340084900b0082c1c0c1c2d02e5406031012442103400741411320701802c00d5030002944180010540d20040c4000c072180d00303010964200f8003180d11079040d4417041500308040854145030001e019400f031842990101b0648100240c107101d41409906a000d6401280452041c194540030301c0c000c00902a0081c02d21425401c50070300c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 604090584 1250 604089334 604089341
    0x3050c06060a08030a120f11120a0b01020705010e01020a0b0907051201020705190c08010501030827130c09120503091215060409032c090106111f09050f03030f0604 72
    0x16011038000710b1034040517001c103486051074522040020ba546102c182c1000c81d0034010100d4424905010503601d03a00c0400200903440013901e11200e07a443c1034a031800c181d80003e211001c0d508242404060080303041e0040b80b401901d010000d200251820502c00c0b904800a204410b03914121043c0c044100d881041a00b02c1c00348a10162107640440b80c820795200c3d05060f030a800f04d004003480800c0507264800e003070a482c802e0b401101c40203000180160b402700e0401e840a250394907a041143e0b10070f580d100240350240c200c03840101890361400d094580b50b00a406000041040880040241510b420619269000003000300d00500266030700583c42140071440000c895101307d1002d19503100c0c1c3d02848014095039800710f09000d0901c60000c0001040d107400720041d08204d1a030349951aa14003880368003030042e403004c4140070485400320b80084011071a4030381c0b201043c0d1a4084105a100c00001030014150060010f0081410720424024044011031141b0701100410321281c490200340f1085 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 604091834 1250 604090584 604090589
    0xf051506130b07061d030909060a06020a03140c01061214011503031110020708031801051302010810030c06090303030e06040f08130f120c0510020a020111030f0703050c06060a 77
    0x940c80c001801e0000c0b034005005400c515002c0d0100150056880051114007410148004101c1d40301180c80b0703449250401841c2d81c40300c015030360b00125928005001c0e54038010210002d0074080c00820058400306680145e81501251078024001c03a0341c0d0f014003241003080d60038140d80e000624401d00d01045414007400b9003445000034180d904a00e1500c0450384550f030040c10744441d000e21460b807490482180050310340b00317004900d0030342d890815a0122020300c04020f40b9941c164100000c201504500d00c001208180c1c0a080c805c04079910403203c0f054112058000402103508603c000c00c1070b55000b8032540942e442618104403078284001c035290707124400c603801462581c10610790380c00980464098a950080f50805001c0c0301e848010301c0d0705001a80d0451a0349406e225040420300c4400c000010003002c0c02d944d410780c11045072100a40b1500b104601078140009a8240d84503001c0400481303040c100500032041c0c0b620702034a8010010750080c03110441c1c1d4441e100120307141c0d03e058041c4408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 604093084 1250 604091834 604091857
    0x5070f170106080a0308070216150e180703021c0e03070302060a09380702030918040c0504020901090801151a0c0d0e0609030304090626031c09060f051506 68
    0x40204c52650103d650b403800404400860003882404081707090321340d1100b80a00740003c062800c80282100040c905104206013130b103d0704010445041c00300c8003505c0241c00c11202c1c80c015035210030103400e0303241c0965480c09150350035181c840450103071200400134008151190742a2211500c5960b406c1007035440a0401415440300c0442c0310b540103d0440d21010600511003a08441d2814011504020071045034040e0158000068400301d5207001240d0010140c3c0d004803c48440c00d06880706a000c3e8054000c6c103000e00d03400101440640e0160040400902240c0000c0c0400843d000c03460400c490313288154a82140d00c480e4400740f0809240a458000080a00070000710104100440d002d110002040d60002c40411800503036803411b00c0204041c04000501083c0a4a032240d00e120010b03000b030400342c50400004910045090100031a14200740d140c00c01c400304400000390174020100c0c2840104080e10f00b00d51500340c103046400091040307903131401c0e480000c2c58100c2030003502d1082600740b01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 604094334 1250 604093084 604093093
    0x406080307030e2205070e121501150c170d1103011809021c030206240d03050310120b06031213030b10091d070b04060801050d03030905070f17010608 66
    0x41c01401c1402c1c00c9403654030301c5040e0044032404c807216001224410b031507600010b030000800c03c40c0b50801c4c3c010110030514031401401070618030000259502d0341801020b01060b00c010381151403600c01c01d444505190004000c8160080c00102ca14060740104540c3d20300b1401c19070003203004a08102980c2c100c6091682458080c40601c0c00c1200610400404a0380411490148030070309038104906807000d44260000d0034542007511401600c1c00340e11540645c203406900361142c55445400001105e9a03043c00d28a4983d2540000b4132107004e21074102c0818413015a082d60700303205101b0a5180203100c207a0940310204d0340103140d0582d82c170076015150391001581c031080002a070030b0307460305034800b4810040b002c10b01e8076031550b0710543d000c049120003104001030900006070320a00c2180d0080c0018074209117030a19140c000781582c101403145e9489401c1000080051502a82001d04200d074844150780c0d00d0351302c0d201c0c00d50b034141550080000030507030031080200c10001481070368140c800500042 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 604095584 1250 604094334 604094357
    0x31140402190507050f0105010b07050105011e050123070c1707061e0201020f160b010806040209040b130c060801142707050706090b04020f04021e03090c1905040608030703 75
    0xc1d5420f0340801c200b00d070307540325910074400e120740c0c2882042e01800b140303000169038140c1418128259030068200c1c4144620f02442e5803001880c00c076403801180c10038249000d80c2c103c2d91100401c070850191800a02400003c0e030b60f4200580024850182c81b401107480700d081d007101440303d644904174050303400402d00c444401c0e0600640c00d118842c1400c0c3c40d20002d450004000d60950701c40e0840c418002200d010364110404010504e03904d0390160807600001c00c001d1a254000402410028101402081c41c0d040490f584c80340b4929480c641b90b4114130340d103841540d6034200411440c02403054080120003841c0c5101c0d1b130b05e00000800d0340d40400e00303921908150346403041c00851402078401d90034030104001c0f00e40021860f0082c07000c030b04c0c00f0718081046850203005003c428242002d140b480343d4410003481d001c0c4e140300300915849010f25441e917610382e85c03055149480d1410104446034080d584201000740380305c1c41030f001c10a440c01030b10284030003642da41d4a15500d00070344500801203a2681c044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 604096834 1250 604095584 604095587
    0x901090e030403020604030b0f1b07080901030b060310170c0f06090117090d030c030506010c0609020a0815190905070b0906040e04030c060b100903083114040219 71
    0x280c1205804007601d180035a280d0001304190701a6008403001103c01d4100a03501c0ba87c0300206910145426201c91444106040c400181c40b0718030f8020000c89001c2524100341c0d1095000803d000d0000c1d0141e60b6a080409100040d141580700f401402039030506074414010300032481e00088a8082e0407000203220000c01c014454020599243c10080304605d410402c049418031180a40c0c10107029108180b40c00c040141038814400da00024582444244806645d00400100945400c40b1000030090044e200160402c0101c0d8085251413252100e400c50000b0000e8280b8003484a140741c02e1b5142980c0941601034625501020f0429003141c5000c00203275800d070005000111380145510714041e01e9081c0ea0320a410700b51021307800109008200b804001d0349200f41810044c0481e40070016009030364000b058400140070007804110b002c01c00368040307003070102022503070750003403901c03030110f0000d8250022221128450248580c0051400e410326081903c2210000c0d07481070000c0c03a03c00c188040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 604098084 1250 604096834 604096841
    0xa021c120311161502041806050114070b2a0a021b010c03050c0c030a0303050405010c0e030c010e01020a050319020d0504060503060d1b03110109090608100908190e041a090109 77
    0x15582042041080f43c2d01e41343c244001c2005c0d02034082d0f040080c00713044110104a480c56088941440070010b4a41c441320799502c240c032a00366010002501940c0c90313000e003201c450b0001803510089100c0c610041460722891000e002042c20982c21100d8080c103540401041c80201f40d000d50114903501705800c0420310581c010403416045904448840341d107a004680f070b00400200a600196540062004000d02800b80706001c0b42c06180001a07088210f0029841c1e41000700c41c0b905008001e5841d810342c2e4006c0c00096181600503040e03e0306e803a140c0519141c40404038800c1c100500554103042034085c020340507a8103407600395903035504541e104810300a10f088150025038010100703403c0b1142c500b8403403481101840c440c9900d110114441000504070600c59000071803600e0401e00203004a110018001c40321558040c03010400401c3c0b802d04400c144501d94075140b52001411401c844c141e0003d50030305850606580401901a90f43c4c0c0d41c0b04000450a1020340c480001001001103144980 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 604099334 1250 604098084 604098127
    0x80f04030c0f1202010f06330c020904110405060102030f1204030917160f030203060a05070c020a0e01060216030f0b04050709141e0108030f0c0a021c120311 69
    0xa2081900401d10384603400002180c1d01e90764010b030b4480072000c0c2e001c1c0287c0120b0008007400c01a850103215031032451078540107107498003051600380b000c040d1481803161004680c810340182044409040900780310642900d220780d42c5001d1414a00410240c1d4800030841e0b10150701240c00506101480314111132151001d4801e80c100440d0450124102641c243d107285a08218801800700c9440541e2801d4000701e0340c1c1c4503c004103901c1200b0009614082489607121055940c0040c0340d640d03024013a1103800c55900003035000b409030400468403074007070114241654126001c4a16080030181e1184021444d404010312a00c403d070014000036050100c000d070031912031300c2aa00d00d40e4035141c4810450b10303010008040020003000b031011010185800682d540c4840c0000402907040911240d079900c18008078180020b00081e544440d24014088075842d80e60041110303000c0034656521200d20214040c0590701c2a0004007042d4019000384640700340003440b42c0b003282c10081c00d5024081c5405400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 604100584 1250 604099334 604099343
    0xa0b0301030b04061a06031306111c021e07030207060215060d020609030f10060311190b070303060f060f08160f0c0c0521060a060e06060c0a02090c0d0c080f04030c 72
    0x2031020305c0c1e084d03903110060361144401c8120004407078818288102960310134070a10607107100c10005000c2d04131800e2410400e442ca00203002d662551129400c10300f645602201101011010030076400301a03000c80c9105c01c0b544560301b04d4070b030710241c15150918850240d43e003542c0300744150b90300b2005040c00030180c005424014213956401c00300c1740159041034100c219040455a8895040c0200714001d5400514100c09071504061001e15402d02c2034420175074000d06500c840080b940c078041511a07000240500030010041c10219a20700b005082c841080000a010440820000c2c00b000a10f080311032160000c1d80c0c50300d48030810b116090b00d0007035008a05035001c0394000030105041d1500d10201682055064103400a20a1401440e05101c030150200c80040c0c1060010800d0000c10b402140d00400c00f04c130704030740d65401941d8080c0f4103000c4c4a030003900304020b1401c101d01e60001201601818894400500c54803e180b20100c0304010210355002c214862400824007292180d041808030314440c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 604101834 1250 604100584 604100621
    0x20f1f0b031603050705100206060a0504051b070c0509070518010e060c0304231e100306031202010509010612050a08030903070b010b0c15010b070b09070b04030305090a0b0301030b0406 81
    0xb4664405200c045401c255010390040d20300701300070306180e0801c0c0c070015281c1c0f01800090506200080c413082c2c1d180300b05842980c4130310204d04084104040c8010340d460340f44445039102e20320b1030b0225041440384100b500c40d14500002400090003801280c04080c1c0c0d403179049803c580410015641c1200d000105500000d041c0040008140c0800040015050490380d2031100580c100003480b0b0002c9804000b800303541941d40310141600c051f6108841404110b907101841210900d048000300110350025112034110140010a244c06501083c01484450024400d66480b00f90480100340c01e00001010b960090300004049142c1300040c40e00101c004c0c05680c50712545071a107c034055001e810801442c400000c400c401c0c800c1c20040c042d0160007400043c4401c5d0300d13084004009000350307800500480724203400249040000e0048101414071003440d251580d40320f04008140b82c101002c05401041810300c0807500101c00002e8a0403a13038003444080e0f03507940b142d4441d005480803402d47c0004100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 604103084 1250 604101834 604101853
    0xe04060507020124050f010314040305070203011e0902010f081501030e100c080a0513080f03090120070c1e051c0f060b031c0f03021b030d0606020f1f0b03 68
    0x164042d40e060000130750041c0744401d9081c50100030a21981110880c1494644446070480346440c0600c030740d01c50b802d8141107443d0807407400031078090621081d1000301d00b0415040110049960b034040c00702d903070007a40c0350074801c0009078040d214810300b541c0c060801a5800500200d56209401011086010b2415103615417681c0c030900301611554101c280100d03036004d041000754541e5100b9540c2c8890b50104180004a070f5444400d003603c243c990300020420008001920040d00b50001c0c1840c0303001a818100401030407405101c04d400c00704c0c0c2201e402620300f100180038515001e80704e24112106104004091406081004d110382450256044060450b10301010a40000700041e4490281a011a0009210b810581811a00d4081420783d40c0182016100681e10828401c0c40101900b00169a0500c0404014200f00400e500140e28400040c0da4103111b0a40d4000004840898003280c2010309100300850b1520072084d8040d10144500205a6540090f0380020b4110398020302501c24001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 604104334 1250 604103084 604103111
    0x303130c05130e0609010612020f061e03071b0c06111c020a030e010507030e04020d0f0203091c020d05030420061605190f06092a0e0705040e040605070201 68
    0x100c040440a8249583d1400980c8420080c00710540c0310207005d00801045041c41300c00000c05084101c0a80a0807102029000d1522403000300d49014200100c07101c2e08101c448240d0401c0e40c030460310701000401c4c9801d0800d03460310b030b01c4400e0380d410390154a00034220309000c0b0441d4602c1d50b03160f608410f032240800c051442d61f00f40c03000b80c0e681900c1d5400742882a419050103000707040565900c504011042203001e01080d44540f95a00f1035400302d901603590145406581c028000074080f525145100006102a240c400103428109410324040d0000c8915038110aa03110104901542c0114a00304000340001d0403030b81074064811040103404184203c11008036805400400c10020072910040f0340ca41030100401c880864614140e4040b0348400b0940c0c3c404685030701a490041040c1c1d00c0340500410040b50485068501d1101440003c2c01314950050052000c2148034001100c0701c0d10000c92540c6203e081110141d07060b48407081c50940750396031000000d000080804003155611010944081c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 604105584 1250 604104334 604104349
    0x4111806070f1e0b010b04060806122e0b030a020303032e1514090307060e06070506100e06040b09040b040c052805040605010c080d022109010c110303130c05 69
    0x100c142c4088440c8082070f91410035404441a004580c8010081c041001404d520986065200d41d007036400c2c03510b011119449138646a04107081c442d85082030320748200f00c2084007410345645c119070002808880c500006064580c0301f1315602a400d600100300046000066189003c45918407003420703616090303a5000502100c406030490104210521011480581d001c03500e17074410112003200710320300903440000a503145c00038401c07181401010f0884019650f9600c00780e035102a0490152840c0380b42030740c440310400c0c086008618000101070302143c0182854464603144c0103020b8001101900c958030340c0524004011300448410300c00117404192303134a1b58807404403a6802c280301c41d0030822001d01c0c446c1c0f805050350000ca0045292000400143ea80312000c1d82100da04510f88645e2070143c000310102a100788410305901400c03011541c0b00c0000d0705024035101d480c1c204020442d0705103d0400b00c0705003100146e00070050707005201040081c10183c2400b01524032443e46c0c1d20680c0d079548007183c041c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 604106834 1250 604105584 604105613
    0x120711010212150405060f010e0102120c0c01021e07060c050102190206090d0c0c0302100203130f05100f120203090106051309060b01050c060106080c0c03160204111806070f 76
    0x1621102403d01c00c2509030800401d48646080710284110324100010030407050443c030106041007240241c10403642d009110410848101c0001e050342c40300104c030002c2c0e03a211f00c032140500502c948821001a5440940c0d22250310104402410740c3c1460160111150004402e0079503441d582000280c01314400b02c1c9000941101d140c0190056107030100c02a42000000e4540806000c01420b403c0b00251f00128810305496045800d41c1e02d07404642c5040b851401109a440001c0e0801440490348074010000442140c0d801c8400211300420100d04883c9000000c180d480030662003100d03a42147d9258024541c4540c06a0002034201e9a034400500c1207001040b004040580e070b9201001400207501031600244000c0c203141c0d1402000c12400f66450f40c1c1440f13540c0c2045070b640041a0003000107400c40c0c014a010004503a11006d90440070b501c224100e2000f284164503110071717030300301801800c103a5405002c500050003a1004c50703001e0010310f0f885002c045510492001c003640c00144044d403800c85 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 604108084 1250 604106834 604106857
    0x90501060f080a02010522050306070203031f05010c20041a0f010305010302011b06110307050a08180c09060609040e0619020f160c0305031c060b0f1207110102 70
    0x200503192030721580388080c65402600c02608520181000350740c02104075041104102e03030300407911070031140722940300030700340c004607498020300080c80006075002000e1400b8018000c9100d075000d9036074010b52140b0f0464402d1902243d04c070802c48000c140104071682d150b0307600103901d00000100000003000c403103040c01d0144540110302d000e440036040012a40301048070a0808000550558001078080b11158412500c1d0103051101c9034204622501714245842c440b141a5480b420104400340c2981c020307101c81c900050003500055030304454101c1e50000d484522014003030290215092100b001001407175140c0101041000304466107035880b4140307540796008042c04141c00c0c02ea94000720361003503081c1d01c980030b070041c08418100c0744114201c4508420346404071030724185500e00038810b04800d600c040c15900001c40c030038610b081100b40d81c0d140301103017007010031005881358040099406918002400c4d520140656040a43d1015080390030950306e0510381031583c0a8181a130070380e400b20000f041d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 604109334 1250 604108084 604108091
    0xf0126070903060b0f0d020d05030f0f0a0e0103050714070804051005070203060c13121112161208040303030b060c07030c0509060d05121c0603050105011d010608010e06011101090501 80
    0x900441344650500c030a800c90303500e60001281c00c0010419460010007074406c160035651442040400c108403420352011500240c0c980c1c80c0300c42c04102d0f603003004200031b0220707030300c410740a54070b42c82446240d200d0041902c41c1c03c83c1003410b9465003116089010301312000c40c41000046015901d0384181c0400e8142a9100d554847c40c510506041c01b5001d081e140140c5c0e4180007070460380d5491094003041e08c481e17070360710b620b031400f80e080c02d52003282c10381200350300710a03826038160320803e0102d4014016560268010756050f40c4009a140c00c010744400170740051014001072000034826000480d1508004150b18280003a003081c881c10544664800c45850440082c100300704e06180d02c0e17590788080704a44089207190700391a442e46a442c101d403800040c4000244082201c00751820184c2961056802008042c0e160b03d4503900a01080c043d48061800000001000380d0b038102d040340c1600e11650f295205a4070b40b207050000c408001e8541e41c140b181c00c3e11342640c0808248580f0352260302850020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 604110584 1250 604109334 604109339
    0x402090403030c0e15190f0915090302090a1a0307030f02190b130303080c040b19021204030507090b030d021504050307060f0b10090501021207140d08040506060603060f01260709 78
    0x840b801a0320081b15030070320200d01541c50f04580c00c070f10b100044803203003180c0400e11318600d0b1085a9500c86500002d40c000041428850300c4082a1300c54101c0b141510701c2c0c072240390070101c1095666200d6110051004032010064001070030301500031413421104650054200f40c03034080c246115044080340c88403112620408005150b4010541604944140740d0b06142608200640441e0b1182c01d86090403121504014240b00c4e20811944e446141d1a411240c0c40e9900c91411603102c000c507100b441e41d41810b1005155451a010034445991000c0760003d151218048000703654054001b070041e02c41e0b000034026440400c1060280d41c990807809140003800000c10004c0147d080e07060f810703510402c8800038050007580d80005030560401000380ca025100c001a18041d2081d0442c90424510781c05982402000d0300d4122803118040d030f108001380c840d25620042803100724002250107680c00204410700b24002d500410800d20000b00b100b6190448841c54202040c03804425a0f0b100000341c2040000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 604111834 1250 604110584 604110607
    0x70305030c010b0114040506071103100b1e0d0b090a02300c2202090301064106071406090d1403011508060307030b0a0209090f0402090403030c0e15 65
    0xd10502d0319003402c2501000002c0011030340036028070b007e001e0040100017607010a02170030b1b10f0600316500001b82140c00c0010b0000300e18000e0940758441d2405403462400c01031048000c1c1844049041c2c0250000d485002261a4403a0507000504040e010340a100d100e000581c581200030310303031280c5c905c041113034201c5403075071100030580500d054402c0768000210a02e03060350344503042c3c1840018108a01c02031444400520000e201d034940f4580e05610300640055040c4881c10104400b102250104141e661a0303c0e074103504103101070f080545808070004449a5240030303009884c1c901d010390000d003004501010341e1482c1440540318250960701c005510758060750700010066420110780348090a55150000e0450890450b0401c10140400c41c8006013068500300408801190031083c0b00a503800c111480900035400250014041e03510b990005031207200c1224014001d41c1d01800d03103040c9945d10786040b0020146201454100a61402504030301c0d075640002a54148010620aa980000452 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 604113084 1250 604111834 604111841
    0x180603050c0f30061e010806040c11060412020c0306070f1404030f1103060a1109040b010e091008010f02090f2202040e01092403030f1205010b07020307061d0609060903070305030c01 80
    0x140c000c0c14100000c8102586e6401203500c0d400c910156030209038542d02d040700f81c40070740202540d404240f0a490400061050f885902c0c001c0440039001e8802c40d0030b412082c55165941261500701140202030b502103807521401070006040307100b540a80c20703c0d4032903445142c0c1c1311141c0340c10742d0b0410a0184409551a0a012650300000180b400308408041d02501c1a032900403480b6991156940b2180c0c400b01b0f0b40100319803140036000405c10216840e113042800f01484940c0500c01c41903180c104000f25490b42442100d0403424010720040c2d144582404010f590b221001d940108000c10424070541c000381030016001610341e040c0600003960602c6519400c4500a040e45c207604032145070b420344510314200d11030083d60303010b107009e510340b0350540816264002204a82d40000c2e02d841c0000a0005003800646802c510031000d5070a410781d50704084480b550110301d4000c1d00c0c00c03004017100e141c2c136001c0d0081000401c0a44203500304602c900029082800e03aa00c1550389410000795501c80b04021310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 604114334 1250 604113084 604113109
    0x111602040e010b0f0f03030d15090b01020307020d061e020c01060303080f011512110a0f021c0210020d09020310090c0b1c0b1f180603050c0f3006 64
    0x10000c00903840d901c00044c0d5501e02201c400780c000c10f0b0007500da060a40b014801c6440300c03d200c2c5014072101403d10805a907221b400d10821801030b15044094501d07620110071651190740042c0410080c2d0220385400005041c11090540c482c1c0c26807008100445050002e03008102034140001241f610b142000b9003100703401080c01441c4200e150041c81204104c0c0c250080b03100180c58a071a295003145443c90081030181319030040410701103a018466a4828000700841026a00f41c60f1880b61b0b01c0f40115584035861020340c0981c000c1c0c50f03584080421580501040302c9840e002023003021058003c20f080045c6049410507081c2c5403d00d21b4107129031a114038005208410b58185040d9242c4044082d08640c500c0b82c44403603842e64440c6241b9902c5c3c240f000b4080d69100c407511850b4080b90000342c41502140f400009040e5680c070000b030b4035806031090034414801c000251746030082803050084580d0003901a1002c80c0c42401c5142c40c001250080c07104440c00094100e40c2c181008010072118101c5103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 604115584 1250 604114334 604114361
    0x110a080c0d02071802091503150a050603100512030706020c010b01200303130c210b091b090c1c0203240f090a020415020a06050105032e11160204 64
    0x12008101d000300d101c942003080798a010340146c45005640004903003601c001c0507482d10302c4002c03040c00103a42c0e80922880d03888600302c1d0b41c0c41c1c000396600b0900605020803580c10b1b0a524595400300018103110941000b042c641c41d013a2031078001d8075692002280c0000284034200d0395141e42c0e00c04256045544c0902c001d510020f40d4880044a80020b503592100800c0304441d03e049580407020800c1080c1144003030b051200c40e402c8060000d00500070241c200135410b94801c2e80c900e0106996141c046400c95401ca00041d002d03c54a00301c40074404101009403419900903010008a42e0400f0000d0fa007000800c840d207005640d80c2881e9204605800700420812400c127900308a62000d9682d410801e0904e0f001691012029942c004400b00240116881280844040503903a00c00540c0455100e0501d0700c00c0d5010803a40e600e075802e0603a141010754004072818121520204110f10601c2d591407800350740400400d2041d0504000189604480b0b80720780c182030301030381200451400b0f00071a0040d503580c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 604116834 1250 604115584 604115593
    0x10c020604080d0b01020c040f02030a060b040503070308280c0309150f08150402040b0406120207081b0f0a0f0203060a0b1c06200702120309010c080a110a080c0d02 72
    0x64880c012188120b8581c1c9841c0f40d40c860403e140c0364002c0c81400c40d9084020b104025494880d40c0d000d010307510440702020010b14041c0c002c038503805036000703503001e403000034008000c06811582e071444079501810306e0708654040300310440490420100f4030106840d90b6075541400c00464034000d803504442d900a50f02c401090300c0d110140325444540c8000c03a520300d24000350142c64003140148100349401129401600006022074a07002c200c0050003104c00315900c480809045102c004224051000001e040701d20800900030300c11640c080b0030034a0008442a5a003a00d441c0882070311b8004400740450310000c0c0944080b065107400d2091030b900180104c41480001000c40028100c5148a01c00c80c420340e4001e1098020700c4050303031020700c404022403950030006a084851040c0d6422120b0224070809169030b808580003400300c10380d6410741c0103031145a480f183c83e55540c0c0b4241c000552610400240100b00d07000e500c02040700c00d1401c0d008080b00d56540d055951800d0070400d402c442d41055600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 604118084 1250 604116834 604116841
    0x24020307030206040221071e0f080703030f09080d020a14150412030e100b03010b0a0803030106030207062909011406070b15030706090e0114240d0c0908010c0206 71
    0x700403420a134029070468110542010380100c2044000d011803c080075840746e070401003603580300c410000c18603408003800c05040710396454141609203814080c408884d001004204002802284210181324450a140c00380d035840310100b600c0c03d03401211b40c100517480002c0120510050302c0e6410014107204018205402c4541300d0300c248120080c6c4002c2c10780d8000790051046070300c258030400c403051030718094130912100214181c1c040d12041c00741a10951030048581494503018000b0022524a0b1000e541180c2c6000c40541c001d4002d0002074401c00d85484c0310514205818603030040d0781d10740e20280003420401d01e0034402c0e0202d05801c0942500d500c40240340305642da180640d80d00d01d80c411002d86183d03461490164030450441c858130381600c101007000c2405034000000d501039440071080850b07541e80e520064229245520043ea0f081140000c04603050b0030200703260314801e1502000711303203880f02015284c01204d00011486d4002103034520103100c076038401c0c004c0300c1d003620541c80102a00e04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 604119334 1250 604118084 604118087
    0x108010b04030b07110f0a050105040209010602010606080106110109080309060f0a2c0a14060f09011404020105130e270703030e100e030307030903050c040912050a09050405012402030703 82
    0x607010700035005010484080c42c400c5c0f901013002c070149070005010348450054500c0c02d45e02810307058500724070034a684400401c1d49881441008129074190f550203030a030740390000c20394030341e21003800b9180517540b50003d9030301207022440154040c0c50454014030203403400912400c107010000c0c001424141c02c240c0c1d14003010303080102ca81c50081e03002c2901a030030501e0b0001203142140103103000709500c0c3d01064040c0c2443c0b0104005100c1c1c407880401005070b0342d03540701e010b00325001d9480c0c00c141100b0000119000d94407900c00360002c22402c40812420380d840d6407071800c0078941259002608061a011051522030360041a016038500744c0081c480740382166000f0f0440e88030900441e028040c600030b0090030900c00d4901c03074400d00c40030381660b03594000c03410700406510207408155194441c0c1c1c04850b015041c24030442a07190b0300400c01300255003034444215441d0b403100b405001040404140421240c2d80c1d4481d03103009000c030001030381c0341c4094042d80c0041e80740341c110440250b4002b0701c140404039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 604120584 1250 604119334 604119353
    0xd0905060d0e010603060203090d05090a0b2110050103060b180d051501080d0e18010611010209030129090103031d21010e1b031002030604180c050108010b0403 70
    0x250011190280c84007403104580e001001c68020b2440503600300701000081c000b055004602521200040c1c8030340d030501c2c5405580910130314140380d0700007000c00d1040010a6002c4c010f000300b942124440c01c01000c2004400e92400416200c0301c000408040b820130641d0b03010300c25500200603100ea09800c00c8400c55400d41c00750b0034031080500484003801d000080180600401500d4011036544821f19612070841c1c554031030a0034080d0340031441d1081c82c19203034546014004001701004c0c88186c416800d1a504481c61200681c5101c450364081c4200a003994083c040d80c0001d87c160030291003a814034503645c0e80c41085112a26004000d04030040c800b00341d20081819151200b48608604c21030b2140114002c2c10320301001c0500008201070b221407040041d0008854031881d28202c0e400250810003604528000140c0c0d545e1581c0711349001403610401b5005142e1284000700001007642c1581010b4841800c003503021120414284010b001a607000440c0f18003600c000709003582400d00b0340d1780300c540c034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 604121834 1250 604120584 604120589
    0x1211122d06010e040303060803030103050d0315080a061d0111130608060607080a050d111b0705130e07080a05100f06210f0606140f0f03030a18030b0412030e0d09 71
    0x142c283c68001800d240c0039400c058001c1c100007085a40e01d40c0d41e070400d1034498500405c0080082d00f4411000aa04c4074041070206544181d00503014505050384c07071000500c0c2c01080c030960380d00c040e41d6070b8051220030701c2030880580c80162a1035440598484400d07210034203800c200144130302401440010f8407024143e83c0056444800c05a40e030603203800541c0c00b8002c25108911316410910103004054201c1c01800703c01300c607507003117206201c0c203480307402e031101d19178010742e81c010f002d2a624810720b01d070a0f042007824400700e03416141c13161744400406052111800003521294031400a8540c06013091160f007104068850b0208600c0d4204071007014050000b40e41883d141c40e60703901c030009105048008850499015400700f101c280d9078000601400c0824860394403500040c9240b0543d8140000c4040040c0c41c020055440c000201e0805e90350f01883c5e00c03200c0c44101c0c0c01d420220000d200f0300d403ca0b0096010340c0504119100d1504e00400f07a1b100c020122100790006103207190081c0e048001d901c01e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 604123084 1250 604121834 604121849
    0xc0b16020604171201150e0f1e04110a020d11120306040515280b04030c0302150f0304050106170a020307030b07030e150a1409071211122d0601 63
    0xf845944580c412468050300074500000400341000040010742e08041d0309409000c2c4e10380302d480c2d07030228081201040e003841e200c2e50030049030481141e42c2c0d0310060442c0c2c0340e00001400091010301405501e1880d4018804000c0981d2107400c3c4400610341140588211164900007030914014503180b5401c907000260505000301d8850011035040c18181c24901c07403000024010206074221071601030401050b070f00081c0980d0840c0c260105568003103900300d50076070381c1140748543f8091942d824004012107030704001c41d2649045c0310b510b581e4507084008501a600440000c2080c50600740100c00713007c1c54043c030781903961011402a005031800708601c402c403600322243c01980d0780c41500907405001c80440700e0341c042c01000400100f0149183e403950203649aa40100309240d110032480e00b034070344285c1c1c081d2100c1c3e0104034104059513601c070300303e0006031241805070f104080040214040004811056055412a624055090200c200304000900303501401002d40c45c039150710347d500c81c40c040c054a035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 604124334 1250 604123084 604123103
    0x503040606080d0f0807020f070b0d240f050406061704020f221103040c090509330619060c051e1e030708190e0406060c0b16020604 58
    0x1420301840d540315200620556060310700b80401e20b88000c045082011000c004240e030a0003242e83ca03803000407560340c1c40ca40304004211150400648003641d0304403104040905403502c000d01140c1c1300140100e04045400009000307003030b0801105900f202c04680189014614041003003128076840030440e03442a070346101043c5180c41d14004507140c036252284036900038100d0514800030300d079032002c2c038801d2144600c801c20240e000d041034620030740300c180c4010b0655170003805e082c040a07540740e002c00d8000489808480210001c1140281c090002200702080070307034161100c05802030000502e83e80800c0444144607039401c03d02004100c0c0010740207407000c20100e001c409040110070030000301084103403000100448003150b02c00ea80e03084150440c400406100b04110300c1c4240020680300980d038481c69160070240003d08a111506000b00141c08001c0c0b00203039064139407945d00c80c00c1d001e0301d0076684040140c0a68180480c1003c4042d0040c0c0c11202d08615120704a507020404030780107a840300f00782 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 604125584 1250 604124334 604124341
    0x705070b1003140c04060f06080f0a0e0615040510180905010b030a0813060206040b0115050d1407090f03020d11060d02030a060f0e04050705060f040f030606030b0f07050a0503 77
    0x741d03145a0303a500000c290034214119110414000100341031043c4080b039090200c00c0c2c07644120200074459108500c0854524404250076540d910700b22035011f0340b40d000c0028003108154816141440035600c24980100d421101c04240c200b5020302d07940a1484480003800038500510217003040c0c000c905090b0360540e20100941000320a40203004035000040031205809002c0c2403801056200c200c20017044010706400140c2d003400464a40d114a81089040b4503e80c85c2142d105c041e00d00b00f001d80003c2101c02c211520310403240e44601c02d80003030002245109403814402c041d01040494000c140744051513181000142d03141c52120541d1b07540198104a110070380c501250302409051044e07810513001104202041c0352a0381308004a611b441c02c0522120f60b5454410a1141c0c20354000c1c0040e0408481881141848002040b4980511551714505035850074441411101a00222110340c1c0b40c08082080c010a0b50402e82c0244c49401b40c0c0d019401c01d41000b51180c45100e284e581072081c00f1000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 604126834 1250 604125584 604125601
    0x201150303140903060109060e07080415022107080a2f0d06260606040b030d0e0f03010207030201051609081b04020403020603040b07080f01210c031e03020c04050705070b 75
    0x751100070f0700c09030032180c055841e04114406045c5900911980020070b000103030724640708484150040e50007208441d8080c2c80c2802c000c0295208a42e003290010b02e018400526901000c03450380b00c0c81c0240d4a2004506002e0030f0a000c0c0e540c807025a8032076100d401ea5412807005080303196116401200030f455034600035050f10101601d0958858000d40440c0c1c000702080d6400c0c0f040a29613508010b0503107190b642d8140800044030013902025401d80d00c00c24039881d5260043c90701e140241001003140f020444c5080010f400d907448250102d006035128803c1c8503021000c0f0610503a89905820011030300c6003804645551003172a844609050040021440c61a40b103c0d8101ca028540141425a8a181070708040d46c0b0004141c607400002000032001400414103984528161342039201070303020714035240400ca84400304440d01552440058040040000d49058012a010f00e06058080740c5800750300b00641412012010940183d081c0401c000c41e040d0320002b140d1505034070207080c0c4a0398450f501d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 604128084 1250 604126834 604126837
    0x803040920040b0c0706021f02070203010b0909010c02060c0a2a050d030506030d08150d060f0204060207060809150109050405010213090203060f0d080403020907021c051306020115030314 82
    0x100785408080c0007402180e11040b110041c4100c0a001040310352299880c80d00702da031080f400025100c044072050341c00c0e96254803500200710841c002000406c2040c0894001041e140c0d081d24801007aa40d03910552040300d0301030000c10385c448842000c50381801411003000c1c006548a01041050040e80b05071940640724410034084407640203001c850b140301000d10041e0003020140c56681c03003031250b4a801e04644c6d12515030f00e403095000f5070342c004007000240f0030300207140c45e0050708940700d54a80c4103072000c41c3c1c003030f01c090b000070141c96000305501c030b152100241a285000d030201140b07030444250b038100040031008007811a01c18110029007956281022030080c003550740701c02d50401e41c40d980015115815006140640c0b401c1391a008805603880400284180c4000d000382160f00c00e010800c0903207841c0d2007003540a241401500c9441007404000c251800340d4191140100398041000d8110820041511001e007416000820030780c0c400410703100040310544402030804c2140e60140300500030120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 604129334 1250 604128084 604128131
    0xb0717031f0b13080a030210270c061412071407050a0b091209090a0c0e030a051014151201230103050c0d0b011809020d0302010506030706030608030409 67
    0x304000d010b44900d001100c80d8010351140c00c8202c442140400c841d0404180880c000381d054004000e12808460000c025007400c0850074030840c0601112103080d6902c0b00b41c20917052091509060581c01e1580141000e41100071a94000c50b00f440641145280e071000b064002c2950704000556295100101e50184540300c80200140030301500a000c202080816500504200c2c0c00c0c0d03203e54001400e0003595020f2000341c41d40c0304c0d081c071001c42d103264015403103500318031420303e0202c4030440c40700082403608c1070340c41049400368041d10305c4500072141403055800c8040500202d030240d04107030b40c07007040c6880c070b1080581c480c43d151810110160310942c0010019081c452201c0e02080c805440000d041200340720584176401001045282407a004510583d410342c403502200042c1d00701202100044068210004065512510351001d070b0f455540c81c03200303148281c0c0041000d241120030326050042c50342c05201403500700501030000c04004004d4800b5903060b12800159070201c018200411b00511 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 604130584 1250 604129334 604129381
    0x90e06161209111e030c01050a14090a1205060f070503061503130209100e0907030503251707030e09060114090402090a06051e0c0307020d03030f11040f0b071703 71
    0x51103104000c1c44c032040d03c20610f003003181514510120f600056842c5d00c5460b840c0300c0000d0b101280d6818160410000e032000d141c024000032851500e441c09001c400f407610364140ca6561141d82004010001c031210141c1c0100185001c038114204600454600e103d00c1801810300400407000071f1205072150800c198680e0000d201c51807608141d90380301c0384403905000320040c1c2c00c1950001031560400049540c21241c0c440020741c9425413055207500380003040c0d11400803032100041818081141a040848061141d00c98141d0383c203541c1c42c0c040c00000780702098038003c014000811440d6a040780d24a404110204d018a60b182c10940000c5c0003441181c00d03299008100700303000310b55141c0c0980a480f0301c00900060341c245c948144054007483c0540d004202240c1c0c0204002801400c0a8090a168600c0b03414045039072040c014500065545401c0c80050105020a041201d1070b034218860740180000045e080c5800300325100c150040d5407441d14074440b00f000201243c0e0464258403075010402d00c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 604131834 1250 604130584 604130599
    0x40060e01020c21010b15090103051003060f06060f0e010f03180c091a0603040c05100c06141b31050d06050402010215011401080702011104090e0616120911 68
    0x300315030340c0941003000f03e901d50310390301e450400e522038104980292004d0118121060601401c84011805000014100c024600e03182200100007441802000651150f07000e01003005814040c00a1010f21700015950800072202c0b03100500d6604500460b1041c105440c0100d04083d0b0f0001703401022401050090000c41003400010308402558400041a0403043c09520401c030740d50b04201d024042510040c00090072501c013000a450b2441e00d045c049030309410514200169a101d01044400401c09040e03254a040c0c2040700f520f5aa01d01800c1e00407042800a0a0101215403540c1d0101c20107059606800403500c034143d05040e040324000100401486615505511324040d0082e10044e98202c0c007511420400ba4262448280344906a58598801d08034901c80d480045484100103003290055541c5c901d1400da21882050050000c0c100d01071011842d01d88042d0310624012000b401020841140412403110316400f1200200021070b2281c041201c0065050000d046075198018a50000c07c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 604133084 1250 604131834 604131859
    0x10b1e0405030d020601090c0e03061302030a1a04110103200318070b0d0e01060e06060a030e010e07081506031f0608070e0f100303020606010c0606080340060e01020c 73
    0x500040c0355068881f601e01c00d002d003401c04103054840398001d40e50181e03da00a1000281e85001000840c01401d000400312103c0c00004e4650080c5003614282c1102d100510078100014010900c0c02048009001c0c60104410342641600c040b001c02400d260b08001400003001c40c8042c40443e42440c2115485010355032041d40c2d407811043ca66226001e00c00b030310390a051241203a0304041c4184001c0382e03400544021180c5e94031042101036030180b002c0c0410f0580d5035103406000300f401d21401e1000280340c0002c0c444d01e8245030320f41d45041c07035911580385003031500c804101c850748000c55a02c44a4201400c028030311004207420310f000d003005401c12070741407048410000f005202c1c86401801540340826881c0c064981c1550803410180d580000307009030340504040f8500e94814060f101e001c90041030001403003a15a1801429075000146001c0311080d40843c0710b001d440c801c100780950840c00c28000b06180040140441d500c5518414902403046909008265900a12202958150003000240301e01c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 604134334 1250 604133084 604133087
    0xf05060108072108120a0912110c2d06190c2001020c01081005040f0527070e1b0c071e0b0f030702070b0307050918010b1e0405030d 58
    0xc110b21660500380f040038020f00200845840110350640c000c03d2903071a00d00d204000340c22501001d841c541e08541d903002003602040002050a801a125503940204030f0301c1d0b854803500d13001e01c454281c3c1c803c2c0302d40000b4000d400c0780000b0b0010003000c04001022060300420004408d0f0103880d100594003007100320380030802c51344071540c19640c9203d2900c00740f51245070050705008100c10110140541d001c6410160190f00504601e54050040541c0a071090741305c10100f0140c544103040001341c1d51300c8005101c51085048038100c9900310030074100d1070b00500341d041c81d0381d100341c60b200300140c0e003d41502145d0341d6070904011004051441c00b07840e580c0c14194070700d03681d5888640329461403920045a94074064800f1008642203031139031070080e41842a0018841032640c000313441d24055100b9800b000a08003160400f640c800d1110b9103c1e035860351104014008090f400366220714400c7e4004005100b000c0f080c005448222240410b07500c0c40c400011000000c500c225004258948901010591000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 604135584 1250 604134334 604134343
    0x3021e0a0e070f0302030c0307032f070605010803090a09050402010e0405041101090905090307080d060302031e0d1722020913112e02030405060d06080123130f05060108 74
    0x41c0038540c2d5240300c2e075181c3c0000b203040780400c2d81c42e08010035040012031b0046101307410403030344800b40f445008500c07018078402c0907582e1600110040c048501007038030402e01c14548140c600402e042c4c0040d52520140340d0020385004018012400242c0d81c9501080540e441100c980e160164013900410950500e4144654041140281f01d0b00180c10f4071808101c03416a0b00905001d02c02083c005d605001080e590100390b82c21200c00b000d00203541d0900000540d4080041101c00c0d00320a000c9595280001c10380b0342400b80340f050f000c00380070a1880403030300c0460030315003650b20004040040c842c0001070505820070300480705002c0d52141c24501403003496036002103940a020b1156508944a203190014020400c4070313a44200b5220042000000c48e010f6041c00009407800b03148156850f040d01c3d14001040c0d5041030041e0000c0f55540c040500548009204030035a9900001010410503c0c0428203558000300410040503007801c0c08030102004071103643c8200d519804816280150b0312481895500c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 604136690 1106 604135584 604135591
    0x703094403090f0109020102030f0c010e0d0f0306081f0c051e040512012a020304080303090d02010b100203030c0a050d09050a020108060a0f03021e0a0e 67
    0xc11880395400e4021581000d15102e05011141515015500684650981c036105a41001d40e07000001c3c1e0f160002c0700c424082da90800307502c3c01400340030245000b001922540d210b1666641d00443c0854101e9960344c0e0400109940340c00c401d40e00d101205101d00c6000092040300e1001a0542140c402040142403036483c10980302c0c4204601e050350f076120b00607428046401e008510b03201c07005042034440c40f8024000f41d81600151460400da1110062440c2e810f9100c0740700040c000d00681c1c0040c10004180c175100d240c0b140d000760b02d4854200d04140154a0803001d5604c23860524240c2c0c410503a1a802076040d50b4030310003154099070040c2c51034030034050b0a000501901032103015211104e842240500110781552001500d118005800d492003144981e40510121510714456401c99804845000524252005495841c0924111640c01001c48540400e2601c0864583c500 = true := by decide +kernel

theorem cover : BRFrame.Cov 603956834 604136690 := by
  have h0 := BRFrame.cov_init 603956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 603956834 ≤ n) (h2 : n < 604136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
