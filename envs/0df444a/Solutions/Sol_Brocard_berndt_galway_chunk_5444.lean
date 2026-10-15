-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5444
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:53:23.580226+00:00
-- url     : https://prove2.me/submissions/436fcf32-148a-4d0e-8e93-508865048035

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 978956834 ≤ n < 979136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 978958084 1250 978956834 978956879
    0x5071a160f0c05060c011517030702010e0a09020406021609020a050f09040b121011030105101b120e0f0d171605120703090f08120a0e0424060215060d0804 68
    0x110580301c1c7c071800110003215481000003550101410b25128004000c590b0020b4091812043c584002c50004401c41a50741c05146241d100140000b0303c0ca40100300d0950310714070120405440c941c0d441c090301c1a44202042140050300030400300d064400408090308038950041c00008080d4103031008100e1840302c104d25a42c4641c030095200110b0745490294400e80306401804a084d5450100072600382660010103006201e2540d0390000c21004d41c0c02200340503070304032080c150b20842031180a040c10301415401c0b801036030f070707000c4401403070038568031020201b5405005e0400003500024010003d8205005141c80100322801c0c080104508120242000c00026000c590ba540e03107203400340c0a0b0075640c0c0402e0502c0c44010f0100324443d03010809031359005003101141d40c1c2e00200c0c80201d03002d80d414036400354064500051040c245410200d61182c2020a18003210081e2721a0010390340c80120100c034048040c030b403000103803481c2000706484403860f1240141d0383c1415140d1145e0509019559403812 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 978959334 1250 978958084 978958091
    0xf0306020a050c073807080f0f04030c06081e0610020a061e05090a11060d23011a13030210020a0c0e0f1302010e09070908030705071a160f0c05060c01 66
    0xc00800b03210402207001442988150704812542c1d145c64140c0901100601444400306010715114050002c0721919181c283c04203030360f692070745040c0c4001c41c01230050400141514000802800c13800c2c0074181942c0e1103d00007440359036a03104018940302c820003050118041d8142e000300085160048201d258404c0b0540c0c4070381f0306940c03031090403076000030b02e452171503807103800300314049068400c2c1802d0b00c4130160707500c0e580c0300d135202c04007009007141414503041c8015004020030b28802158181c0d05139241e040d03000001c03100f031038125070366800351003026145520000382c00c10040c40c24446003500303014580150741c07100e1b81e2901d40d4643c4540c02c2e40301c1ca0f500c441a1007001084469004043d510050940c09201071a005400003480c1040c54421036009040090115100c0d600a49a80000704070b498112981c030b016600c2c1c826102c405611682d2024070b0070000d000080c80c400c1e03003602e02030001c2c4c040c1c01c40700816584a1410302c42001000782c2d0070020020011613a510b40c03d0040440e07044040011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 978960584 1250 978959334 978959369
    0x20c010e010e0106151202120403110105100f060806040e0d050a0e010306120b040614090a0507090c1b060e0601120b06100915052a0d02070f0306020a050c07 69
    0x960950b80c0ca555401c0c0d0720307450f008081c4419010200348050351811850400740c20700740440290000e100d10602111000341e0074080100301580040352080d100884e8001380142c0d11036869040101d5210700a0103404008040180701d042e00c2012155488078000303202040c08010b00c80000e081c802c0d0240e040b0000b0b0b82c00112007214a030091040c108101080c82e04000c018640350000c0019103a40c00000d00e2054942d000c40e0903c03496400c050400f4020300108a0241840e9407a035039030b00e400305400c9a13607029410b00042c00009030700c122303840c0b101c103511380c2c1d200000c0c20150054103200c800d0301280c04a54580243c0026542082054003810798000030441c00070050800c42601c820041a07188107a01c03400b90340c440c96074044281c10454100b00d9030060140e01e1f10005584a0244100303640c1c0d80c02e601c40702281012440740c80341a9283c20501a104103245003201282c9a40441c0900d88803512150130410020742554001c014100721443c10b0707400e248100ca542801c14903994440345840051020a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 978961834 1250 978960584 978960611
    0x8071b0608040503190e1002010b040e1902120f060f04060e010e12090d1a060f1002030906070c08060f09100903021209241321120909020c01 62
    0x2104050321a5081950051805a94040d900c0c404c0740314000c2c1c1c2c51060b64140c0d819a02030100d10303001600c0100144414805414028001e0560b003208911560901a00120120000c2500c0303020f2025800c0c0b0313103c260165000c1c041d401c0c807428031000e6103204080c030b511a4683e00b8490b06001d401c0248041120742400d0800c503041d0307001d41071001840d915084004110100c0000c0159501521900309510341d604400021602d003c0d01c0005813080407000654115550b1401e080c601c203041c2216110030051034401070120301c6413a0a1083d02503801081403007524980000030f0440342d40302d0b407028548540c5030084641008425141c00711503002d408107100005406011403810001c2c2500c00300101c03500c54800a40d2408035060341d07441c103032000400c01d031591155441442d8481c00d4100d0708040110b0444450349540c800340c0c008000d101100400300340c04965555034402200c2c510003071144203d0585501e0060074041d90400d0a12403907110000b014411800a00400c2103010300018038400d45220 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 978963084 1250 978961834 978961883
    0x7050307060c0512060f130c0302030a1503030f051c06080105151023130b0c0c01020303010e01180f0f0b030c0604080d210f060302010e090f0105010507050a0807 71
    0x582c1051000500c418003880920024003a800941140e50040c094a0b03103011401c2454003604a94801c0c1c10230030303803048543d015001140030399600c640400c07150a0003c0d078049501d8281c08000d0000d1400700080382514840c001a050000048500d070402c1074140c4031100031a642c81c0d100c8000c50b510380e020042c01c1a080918107200074816101c446a4007802080200000e85010b8030f100e0080074185d803240080384034000d51f0401d000124013030b0a82c41c2c840c07507402c42da03420007201c5503480e100d003140c9076a4552001c4103481c100d4103000242a026400c11003403400908a50034131700c04c0aa0341c0c0e1601c0d000c20045000d801002c1090301000104e1070004400d041c00c08503428290340c042c0b030041004114114000070b0f1145480d43e81d2900001101221201e880d14200ca603807280398560900e2a0109400d842e68440c0c400c0300e1013600e440758000340700c10900c449500100d50001d0f029a159004020b00d50050004109880c420b1068a000f05466910000150040c810581d210881c212620a08201c140c1c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 978964334 1250 978963084 978963101
    0xb01031406010504050103020c070f0815010602072102030f0d110c030316020126090d0801151e05120109050603060f041104150503030a11010605010905030a060515060705030706 78
    0x48035080a0318041d000a04a44107a2054904040e1300088010040c10140141c80c09462001c0b030200303100b9550b01c0c0c159500c0080400c501500c010305000045c146000103207040494514001090a41c68442242c10420b4103c080503601401a440303030030703603000c2e0a100e08030090b1a16200c9094008030803014624040e01d800049000b0750040003507141506042001d401d0440d824604480000c98900e4015142d0300102c24001c490078292050000c020000710b04640301588503036540e01107030386e90101000c88014001e810000700e000c2c096144450042d00e0b50201e000784203401d08600c0d120940301062408d0100341c1c403000000742e0300c20078088949810f00406800814180f229001c07070610340c641e9810200d046d4145441596908030025000c4104812a00141801030580f61580c001c0030380a05112242c0708080601e520b402c1c5c002c5015070161414000365400034008101000c1c040d52408010840507254070784140c1c5585030001c2680d0350781c0003410414850800b030343d203a5149140503401d458151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 978965584 1250 978964334 978964361
    0x31207020f0d0c020f040e070e090d03051e180304030521030f18010b090c030402150c15130203120406030f05040209060108190513031b030f120b03100b0103 69
    0x1c140000c61580e1160f49003030415011500c030840c1c00a40c030b001a0003003411200b009414069810002007010500885a100349680c00641e1007500c18620100c084400456542011501c080304610031503541c0b1840c03682c80a038290003100c1c2c41429030086443e5402c954412641c0e94804000f070300c03011900c4218016980d860032215801d50800510342d052814000703004c00750041415020184111094206845442000c2c100c52500e09129101c14503e074001c0381c0c00d9029000c034130208040b042211084aa51100c1d003400f511000d4801c03140d08003d0f00002e0850100d2200041c0b400016a80c28002c4402201158085d00c1da210b103010b102805071405a40c280003190300d0316042001584a0b070140301d50140302440c203a40c03581c0d20040d030104040600140160514030f44070821010800b6010314485960007a05c810807600c50100300c00140011140009000811100018240d140110b542c41c0d441400703224045030307013070180d00800c2ca0101c240c02c444000507143c12146015580505c103e40c07694264 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 978966834 1250 978965584 978965593
    0x6180203100606050f0d14071215060f0c020d1209061e0509010c02031e0c0f04050c04060305060a03050d03020a140a1403060d0602040f05012615060408031207020f 72
    0x4065002c2c2285c01180355980c441040002d103502e080381c03158000d2614400d0050b440c062400c4c181d4008007a000030b0707000003800515007440240d407109401001d0017240d100d956207107240b1251a000f00d40c181102c10080707030042800c3c00100005000780d42540d00e41c9910f60f4450032a075180001c010211402d0071140c00845004840c880d81d1654400c0444948000c0bc3c20302c14428007041c800f00345806a0051013030500a120304042c0600a03000c201400002c604445024001070301e4020001121002d880e00c0400e00c03c200010000c99000f9001607030300c18001000504003c0d9a61981d03410720110b040d8840029030b0016032000c189411003004400c000d0701d01e580302d0401c00129809004441c0c44101491400383c040001a290350320003215002099104c0c46c1503480d5030369411450001d5101303005107070110312034000c000b044451550501b0301030701c10504180c0041c0c031385603000d42200a405c1e41307164000c5420440801c2c0c01c00e04100520070500c06096940052134224002806c00d00b80010004540c0c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 978968084 1250 978966834 978966839
    0x5130201091d0402240304112d15120709031a040f03140c0f0604051b030d080702010f02160201110d121104030f201c08070c03061802031006 62
    0x304001c086902c0313641951050a0b00c0045461820151181c0d1000304010740000100410000f01906440d08420305858409104420000079641d040c1075410b400c841d1040034030301044e03915004c25945a18001c5c20030f603500d4010422180c86403503c0840782c02001c0b0702e11840070410400483e104800c4115004c040007901d0a141d61040b65417074403910082c040280807081c48007000e0400049072054a0002c0c11141d40c0300e11500d040b916248110750a803260700480c4c1e2103c0385110b400d05800c050781c800034007800380d4400010040c0e0b10a0750241c100811507580c0d003c00a01281c40c2e10080c68022084032002201e6482440010b1900005903c0c521311a00a0140141d0103500030302d98000003411508085100c60a03029140c020f0f0080c0d0b03202a102c492906c41d00024403400b0154000c0e08508425403124408801060000354003800241c1c03501e40e424131900502144a910103054180d100e03045030204259a40c450780c00b520403181d0f2a04030110300f00d02c2d113411840d0401c0340c50450516807409102d180d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 978969334 1250 978968084 978968129
    0x1e05010c0206070605060111030c0a0c0e04031b0501020d050c1c0b03100903050f030403091703040509010b1804050f06030d0309020a0e060109090c180815010605130302040513020109 80
    0x184075004100a44841c04150641c0c003a04c42603082d00d81c420100e2b0348410092800a50b1160140d034190740307214400c0d00c08600440c00706802e92003a0740645034003036220003401648c07071108001e00b001d035510b550a000f510410030842c0500740c0550f2145080940f900c043c100c01d861080542c2d45610030b103d142200c160a40d80b0040f6510f42c84041401c0e00003a02005810b00366017920580724985000800001000101508000303560240c1d8000e048a40749001c6402046a0b01d02c502c1c081c0c690f2001e0400010080701203440c0081501c2c3e9100c64941d4030090622021034262103090325210b04060304d92007000641e08081140180c2030ba010b2a060081c1030540c2c00ac01e60070f1420740512441710a00c4000900c07241d001e1009107004141d0321101300040e03480c2d001c0c010112106080d820300d1920080708000307081d81000a0b848001c10861440031260703440c20100740e0b01c1c2d9100c10103000c154600c2c080c0000241c1c2d40d03817165600c21052000c10742c240c1c504520005241101d1600b28010900742841c0520025 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 978970584 1250 978969334 978969337
    0xa0c03080a090b04140c090a050108150106050d0f020d0c03090201030c180311010e1c03080609271608060a1407090308090a09091104050906070e0d02060906041e05010c0206 76
    0x3c2e00701702d0f280c03040711400031154100f410300841960403c04500c140111155642c0c021412107a43d1000d031100740c0003500b01a40c0710390f0203200b400000780060003a02107541c101c0e4891410f11030000c4005140c40703103415404e01610002c0c035100000c20780e200382e143d041d940c043c0110000720340c0038030f002d03039107a100d601e0081942c0b03550780409000442d0401c013030b680e00d9026441c0c00308100001413a503400b00950031640c1c0754042d0510b03030403000100d010000c54054204482e003180614001094178503a048059120121584890701d070704107a2040d40d1028010a0005143d400540040300c0a810b1030f18160303070040c2c1900c42e140443d6040403080810480794540c00724281080d41c0c1e0110702c0d83d40d01d140c9030780050010f44035900300682052400003048100051504540ca00071350a48090200eaa035008a181c1c440300704a800e940400d00d00c0d4521071543c5080c3c0a1f120740e45200a0459082015542c0800c0080c2c000750000d508014400c1c0880705240d020a048000403e024600b82041c00099070200385036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 978971834 1250 978970584 978970591
    0x1302181012091109010f060306090203061305130c1409061203070f06020408031603080f0f070e03030417160b2a010227040c181e0b0a0c03080a090b 65
    0x5056403803106004004000f00d40e04003948006000f4145545c64802206052203d0300c00c09021910702100060703042c0c81c90080d64403501f0300030050669030454a85010141c8001001c10024112546000000440701c1d00020054580070710610b1034607808105104100070042c05103440b440c600b2100704031040c000003c49469650001c5244030740d041a1030000302034026600302a43c076000115050840c0802c55200c1034080d802a501c40701140c5640000094400d4199092042c0c526a080050b22050081040a480d401d0140071203181c20b907994200085100c42d0b0800690540003100f0502d280348000c030b85640606146034181c1c0c94070b005020100304003c1205801500b0785041b03e0300c500e040100b0350691f00124204102e00102005165000407094160706e07907580329a15111081d2002403061140700143c0e00b644440f5008a4105040d0300c209042c404480c0c0418142034401241d00201075001c0e2005d02c81c95194040c1100040c80c02804c42c00009141c812042d01d005810400719107466901c580 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 978973084 1250 978971834 978971867
    0x80a03110306060d0b15070b0a0f0e0a1e06090f0311060106050405041503062d060825050a03030e1e010f0e0f031b0a0e010528030213021810 62
    0x85058110020904500c55101c0151b44410081600e82c02d001601c0741c203d03c20301c3e181380c0c10000f4044019900d800c07204100c0781c1c0c0c0c4c010760144000400088d6024000402c0e000744086000d04c10b0b500340c3d9400141c40c2c1c00c49085880c11401c1d51001c080540143c00c2a0321214408098007056040000c0200b071400f46208007031181d80c5460a071590003482905000207182c000f2018002002c5245c10b004252941000c858089181000304140c40b000d50300c60b03181942c01000c090300035045003886442c010784c2c0500750110b07412100c0c100050b82e5510010550011842903e803210402421004c10030401c00404228500c00e00310001c15000383ea1100e400360b07039840642801d0000720b807514081240c0c0c580f0702e0883d6815129240c000038034040c03080300c1021890402c4400b0b0384c080c2c0c0c480d00011a004800c4c81410b40045e20306440500003800850f003400b0301000510303003410841d42c0f0380014003d149241800003183d41c2c00030f0b4101c00200720804000908600b503895044071342ca000c1004020311a401030908 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 978974334 1250 978973084 978973091
    0x3030309061302060f0a18050411040612061d07080609060a0302220204060504031110080f04060e0d050322021309050f030409060f0e07090905150409080a03110306060d 74
    0x2c0441d900c2d58141c80707522484816240e110240f840002c3c10164584280e0380002081d5280040c4900d000c0c00303449001c0c40700305090343c20240303004800d481c04604000064030454440c14041010074590403800d10010700345400e254581000354028202e44006007800c0e0284d0803001c02c03c01d40781c80304496401101d50650764581c403400381205c007040c481c0d801094189190b00015001400715400710180c0240d034010f040a40e00410b80e4030070004103c2c84c24132004041401c10000450703ca02c60301d002c540c014010040818222008000c40d802c0404d11806400132a20100502524000304450b03c1c231684502420401c0ea24000d0b00090350700d200d400c3c0d48507401522420900108901845980280c04166044030344403600c401c5040050705c07140c010340d400c0c2c420a840000d214809000641e02540d043d4030707040b421508103001311002d011b004240040440700c10301c0410007603e03548281661603005200b4180c40c0e81c084003008040e916030b1680e8100407102131081c099182d0300e40d0202da849108412000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 978975584 1250 978974334 978974371
    0x1810120b0412030e100606020c010513120f0512040612091505070c170301030308071e05070c080610080c030c210114071101050f16030f1d01020c0c0303030906 70
    0x200c000c4d101d20b002c1c0600500411018440c90881c580021003036a40d66001c2e10500c5014038011500d9006006040300c40340030011301008408608a100486140240e5091068000796200e280c541080c198a41032058000501007003c90303402216003070340f20003252040c4144030079034488071201502e025140341003079902c0c0b0104010a01610070600314691000070004010034029651466400901c42a408034030b01000050110b403103000042c000c40b140794031200b40c0c11003440041382d082e08880c0c0100c030f40010340d440c0455296000c0003528881c0440300d51580c00c217400e1040c0790303091a0882c52030a00030741c4080c000e00d0b400c0c5ea490030744040140000c0d01c0c0314410b52000d80c003540500101180780d0502450f40d014004104d40c401c010301c840d040400b00070300c4a5195007400d500040d1003210601c0c541010201c030158164800e40005091403201c00c00802d500300a10b03817140c00f50700003050711800d980d40040d0301c00c0000c0d0240304a806040c0118050760442c41c01c0480d85440e80030003031010100340d40741c0642 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 978976834 1250 978975584 978975587
    0x3210f02100b0609132405090106080a020d050c030403030e0102040f060806031c0809070f0e0103030f02070503030a11060105181305100c090815090d0e040b1810120b0412 75
    0x984514940c020039800210f507045000400174500c401b54280080c2c441d2520740442d1041030f00f000c0448002034240c039401d03860b020301101d800b44007401401c0196000c0104002c001d481340030303484c0500040c010150344da003414607020b01280c007105550708250b4010300041010300c401e09904e030704440300d40c101f0641e82d40d1210002414100002500300034a07c11b0b420440c03089a00102c0c2078801c0c0c00c00401c580000e6140c000070301e240d090b80d204002c18050072600602c0040d00c07a80d18420700304494011904055182c0340003a0a641104400c02c00060001c520f550100300e08214190042070195502e650a40d4030050f040c5516000800314080645c800006404100c0208060703900e01000d0041088100100240144824000c0c0300b14929846861041100c000704003001901401408002384200e1400c1d80055030000003105a00398010f5031415031503160303107841000d002c05ea003000099640c0351034020024602d1402c0ea40000c51504003940742000087c200000040c0c11903000900c904c1c1031800b0302c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 978978084 1250 978976834 978976837
    0x17120319061a09090a05090703080703110604120306090e07051c1b0e010b091e0f03030f040f060f480b0606121b0c0703210f02100b06 59
    0x205445a101629403402e5071100c00c005030039200701c100c9900c020b9031980342c91a030944074143c0c0c081149400c005030400014181390020b0031410710906241c0c803582d1811054600b402d01c1207030241c505901c4c83c0c40c1c8200d61075045c407404010742001c40041160449001c44141d4500ca607004242c01048085250204d840c92007090a4444d0750101c511b9056101e0003039054440d4082c0e01c85d5400c0e540c003c3c00041003580700e0b141980c4000c01c018216070b5100d54200d9540021440080030b00307030003180320364403040b458405000900c00a4200c0d0380459031344e4a841c09001d03181e4100e43c8040c0400031540c00c840811984036003c8481e1089041c54071a01c255200d02e03860002040c020f0340341c030100e500c1030300d0740102030620007420905014030340c1d80650365a200180005803148843c44401c2074045c000290301052900f030070107103070050080610304000d5480001c601d0503580d50800d88034140c206120501c21401002d400c81504003929084424aa500c04048c4d40c424160002c08006625020001c2003500c4000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 978979334 1250 978978084 978978089
    0x18150906140907600e10031103151906020a02120d05270405011d2206020d0f090c210b160c0203030a031a0604050a03030c1406101712031906 62
    0x10a8468480076600e0045e12a80031000141d010305914003c0000c0075019101342c030b80281082c2500381c9942e43d1000c015190b10a0303070070040c7d0b004241c0041001d03c010b030342a09202030100d07900180244030306801000100d012420300c20f210303540440131000704642d110301a0b982d619001d0f895460100000300d101c084080d506032041e5082031408000088800200b184481080480d189541003501d03240207200c4590b03868003d81ca003000c1d008800900040c903e42c0200f290030400400000d4030380e00c4c80c042c00140ca0101c1c00036030f284012104140014013241c04007042c03006040c611079244441c83c1d070f1020b940c0800144600c0c2c020801d0402604a18040c08541450a5000342913075640c64074604080d000b0041c4089503130643c0958031114810342444801c6400b0745000610b48002c03e4510755048898000c6018100c848229152200c002000100441d50280a010259020890070180201d4001a9020890704c803640001212400d007103507202181c3d04a21020300c40301c00c0c1403642460001900056 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 978980584 1250 978979334 978979499
    0x15030a0605030a1112010c0203031506073305040f030e030c13050702190203121608030901021c0c0c03030c05070b1918150906140907 59
    0x101e0f038080c104000c2584411075484100e03880414200401203075800c03507010400c0c0b0405a03104001080c1c0408071810401031804001b03104501e00340d1140e881d460038800c15803409008210001c9801c0b252001c0c4020a0100016014200083d10b42a00d0b490301e40d41d807243c4050180104030103968541c1d1024402e81c4260640070380656800f0040540034001030008030359250060062600e00c003d0009094024242141c00030000d219080104400906991000c1201035400800c4000c00c1c0000d01030300301079407052803030400060701d03000f40f1500c41c0e03881202214085c030418904000c600030190404cbc49144c0940d0076250009203134011440a0f1014170031400045d0110000104214000c0030010001c5500003c0c14024440c658445100c1188402244402403d044440d440f01005c40701e194051417085000316408210100300c1c04942d00d401d0720541d5103800c40e4010420030720080151501d440c80e20781c0b5800b5240c20100701c00141c1103985581c00384014494001d0041003501210f41c1c0146185103000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 978981834 1250 978980584 978980593
    0x11707080a06210501230109020309010b0a0f0e0a140a050702010b1903060606050703120c1e0f031103130620040e01030512210a140106020709060b0915030a060503 72
    0x183c1c0040401a40d2845040b0380c0c3e503091145c000d52218044e0701000b002e4003102494074282e4200110407001c0c2d0402840206190758030203a843c4156662021003006120310f010245186080201d84010f0354002050441c0031410140144440031200c90065803001d15203c001030151a400c0e003c9014010114019620800345540c482c980b000009070141141d200310800c1044a41c2d400c0150b8080c041c103103004e408500b00c020007056020f0250012041d01e0741c2880d00c031340805005003500c0445180103030940001081400c4807210103070103106e084182103100c0440c40c15407420103441080707401600b000500030350b12900c07407100c40c5811110b007000c0c00452007980c586564035805000c0c5014000d100079207052251110800c2c0908010301112070404000607079800912006044004094003c0c000755880359030351248007004640001e401d8061300482e40031b0b112030f610f485400015200e0540100390100d07400c204050f074960701d0300110059001e11a084603100d0f514180f0700b40003003a403580102e415004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 978983084 1250 978981834 978981869
    0x7020a0e01140a0e070e09040c0302031e0f061b0d0609020d0b012c09090312090f1b1806120732010212130b0d05010303020c011707080a06 61
    0x2a60710505000030b00940e0408112540c4118071694201c058458002049000311340003141d0402c10800c80e4414042d203040ca958950700d40c04a4649070800901c0307410a6412038a140d001d8009000030569164814014012414043c030f02450b401e00c503070304081081c4000629280c140381107800600080400013400c5440d0307208080a90003810316030050078000307140040e031096440525000e60f410030318299070101000030904d00380300d4500d001030400b0036170344401d00c03100d03842c101034441d0180f2407500354000d04484144052001d150146040301004100e040c2d1600c0041a1207040104480c240041e80304100758640303401003a100d4805200c104004d00400a000c42c070f143c0c11010400c00c80e8080c103800c00c04c00680419003601406009085801a04000419001e0b000310170041e009646421400481c2039070b998440350050303072006041007481921100104181601404035500c841c0c0e0038289980f50200301c4134542082c800060120007030248002c04252f400a05500140c0a044800240c403140c81 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 978984334 1250 978983084 978983099
    0x5091e1302030c090114151903091101050a0c1e02030a080711043c02041d070302120a020f04030b0403031d0f0d05090303090a120605150603070507020a0e01 69
    0x201105000d03402442000320003101800d01c440158121025489007034078441080041041c1803410203040e41051600380540f0180010441c0d0740c119001d80c584001640c800ad525005130055100c1c11020f050207000d000b040d94032504813525003510f9a005404034a50451a005000e10a4103500041d405100300c101030001c0000c528000c3c01c2081c020104100010304134010041036410038040302c240c04030700415821105036201032000c00b103030b17150504000c14074400208034101c0c0c01c80e60010302c101c42148030144241d800c0411254000700d080c03400354a4070121180603184400003800c00040290300213508070780060b0860070b03a0080e55103c018001c545c1814280100900340c41d1460414002d1030a0071012a01d50006070b003180e8032200e0010304030702c40c0b615000f86c4d915001071200c0c0380c06020401c1219542d075207001001010b05611101c0d00742c408014105901100d0f00280824242a00340000203070326a200c10a59501a829203051544d070101840402c00416083d8059445140004000710707451 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 978985584 1250 978984334 978984361
    0xb0a08121b03030105010e09070c0b0a0906060803030c0318030c0109030905030609010e070b0d11040303031e05090c1c0c170114011d09070b1207030b03150105091e 72
    0x104250188120000c18140761601c07840700b88641808100350390030760304c0d860500c07641c2c10340d00406034100440c11101035254041c203008126030780c2d40ca0980d10407042d030801075140300707810240110fa0011070171031038012946d41c1d9a00c4041c28004440f22442c0342104c5040b401c00866043d00c08003c024816142c0a01e409040ba0145003c0c0502c41e000c2c0600048000505118200c8011080700061000601c0d01003801d0099203c0d0b080049490389030109146c1600440700107100441c400e40d400155042c0d04410411055409500d0080e024104400d10818500c00101c01003c0038007101e030b001020720f4076079040307003403186045e0b00912003c04083d00240600544e00c500322a200031a0003800305520f51480d9402d5207809000b858400394032400f00a8002c11008409030340019607504644205441e00141c40312500110800c003410740e140c80c00c003c00b15506001d540d03102c2e2030560041c44c60101d10020314860351014050380307001c0d003c4440004d9680c05800d0044524000b285640c068a05120300c44a4a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 978986834 1250 978985584 978985597
    0x10c0215400503040e06090601020d0807020307060e1c080c03060603070309120810050a0308030c09061e07020a23100e040e0a0203061b190521040c0f050607060b0a0812 74
    0x82d944a40005819801c0c0784540c7d80c0b20300f20580c00761800e0185a00c0c140c038406000382c03900c42144003e000880014070644150000640c59500401c00e26091196000981c8090b5915104102c1c10006011191007000c0640e0340021040700d00645903503540c5811002412401070142c08411000040610b07503801c03030516400f601080124003001c0d40c41c0c9d003d0180c40c4a0502c4014241c080410006058030b80520240c60380c80d0300103114034900704a0324a03604a800000841305041100001e000c0110300d0901060f00040c09400c40310401070807140800c01c410121200441e001d11424440090043c0c441c040908101d100140208406c1211402d0b1a03900c0070f01d503400b24040d1140303402045c086140803100501052801d0140c41c9844824070f1036101c0c0202c008080c10501c00148074120b6912140d81c010000c03940d1400d480ca079146170a00b462619945243c2c04803003902540801402184c03a5030040b260400d401c43c1300412414032b0f10340440c906002641c0101418042c0140e8851400d41c210001e042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 978988084 1250 978986834 978986849
    0xe0402010f0e0a0303031808040617011e0302130e030d0b011101020313140f100b0f04110a0e030c100807020706110a0201080a0f050108010c021540050304 68
    0x741e4418202040c0c0c0e416100481869024510701020800244240c0114a4a0070f9030461120032251660341c000d10b540003034100902103a00e01c03515500c10121040050300400002902000764902e001d4400c801000a0001070301031428000f411440d0401c0d40c008000302207010040300c0ea070302031904046005000d49130805002801d0031402c034941e04070500a4900500c0c1c01907001500543c41c0c0d0360706030800c01003594144a8001c441d0007138180b580038000b0b1800c00204110106840e03000b002040141890021001d20442c58400e074841c03e1081c28060310130091142c00d12400000300440000e14140600d55020742c04182c0003030f094841a840a00c0a019111680885400548801c82943c0b10143c0100c40c000681c0b0010100016602c9520b05503049000510002118028880c8040a0354400d80042c14140c2d1601160b01d00654100445c402040b15001141c6042c14204010b4988001c0e007491115000ca00c003000508615415000103e46206284105440c2010f40f52403510382d00148150003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 978989334 1250 978988084 978988097
    0x51609060b0301031e0215030f01143304080f07030c1d040305070c0306151e050306040f0206090a0e10091406040f0b030d030510050319060e0c0a0e040201 68
    0xd01681ea41d05a0741038075808094695600b140c51007050a004440e00140e03804030710f244079401c070240c0c07982c000d50142290041000456050903950f00b01c80c9481455280502080045045900301103648031401c21810b002c120482c2c0840c01c2d0b5140c060140340c004042c00e000b180c0d20122260b000195a0040720f103d5003c030401307503036100c4401c4c0722204200c0e0300c066404420400500028441d0005040c480d1154030360401d25a03d0361544812103641c10010b0341d10001e001d0781070180c0d03c840d10210341c00e48584e100814031b182c2401c01094035194054001401400d0880182d0300b15a9018191644400080c0600b0328095640b041c81d04103800036155084409034541c03010504600320b000b61000e081c2e500c1c150380e00d1502c801c410710004200c1c1c0500d0203135495071141820400d582c24411240707000c089960218540c02c0c510640a00f111b0640d001d1842035001410001c802d1a601e00c05100d443d401240000c0c0b40ba518010481c10015088a05a48070124250110f03400382500b007264000d90003070b80c03602c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 978990584 1250 978989334 978989339
    0x11071d06100207030305030106031808030406092a050108180607080709090b0d081605100b04060e0609040b0a140c0703120b0604051003090204230f06091503010905160906 75
    0xaa85030701d254007005e17001407002c200520074540207811034500030800c18000510702075503031a900d400b40c1056800300c42c10b944407040316003404030401c003099184410b5035043c18541c40101482c0005010f91140c07078188000e80002801c0070480c403190b401250120001e690542c50700010092451808030703200000300d40d884d0b001058031142849494090b0201600790b403030511054803800e68940040002c5000c0b081c5a0000c1c0000440c1172003018400c00d041c400101e154007041e41004181d4006030070148d401101581088440c3d60341c0800c882d00b16810035104480c82c0c80d0b80360400041e18000c4035180100b90044284050a00c5172801000d500e0b00903502c0c0515801d1206551090783c80c1c5a803c0b5901c0581031009000307615040505002282e00be0900103864042540410700f41c50060f05400303200712a0300f045d00301c0ccc01c0455a166510012100b042401840c0090010b186500041c114030700301e40304105002c2c80d50b10250f00011115400c0000c440c18a05066a01400f12010780100c1c9110345c10803400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 978991834 1250 978990584 978990587
    0xf0906031a0103050402060d09060b0a0519030f1407030305040e0f15040209060d110315120d0f09050d0605090c0607030207051e0d050601150c1211071d0610 69
    0x2860000c5140108074a03010416200460142c04040c0059034008010042a20080558410041d0a510410740440c10409800030042196515802a4000c51b9480d421002600e40d80c4007a800303480e8440d2241303d11042c5420000202048180d20607004e120b100c40200c1811b80000150089807100d0440705032607a1041c5030b100035004203541402810a8410440001d80340ca900503020740300d4094502c070300f4801043d00c81c005a0300094240d04800c0e8002040c01964100e0124155200f41c003038800615480c80203004a50750300d0000c800d07800b0400c4081034421b40d244520182d50013000d00911184e41c00c036590800c103000f00380c191040d0525200701d050000c21800d0403820349e5941c0786c00d50042c003a000d26000a204844401200900900c401c45014401d55680e0003074400a1500440c010103241d81400d4003030390010341c5c94440c0010f01001604107000102d00d40200a481c0309c892500d41030071000045810320304042c1d504000710484d00d808042e8480720b19010b1045c46494100e80041e10982c0801c0c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 978993084 1250 978991834 978991841
    0x302040b061615020f120a06060305040309090b060f0318210d050903221701060b0f1602091306061424090a0e010e070e06030114030102070204020403030f090603 71
    0x400780b4808044010380800f0983e11041461180e022080c09444c1c00c00448101c056540078443d034540586101c801d120b442d441500c943c1014001a007070800171400d294501a0001400d807085010054032502200016256203080d2811030301078103a400e89a0400080b440511a020701d0b06001c0c510403c2040d16a051001c804122040001d807040c0c1d11740350008181d000a814020907101041c40108020702c1d0745040300d18041c54414500e010504014109111607103800c603118031090380703a1704040c41807081100c18002c030341008110002131651010540d60310500801d60000181d4088a58020003501c040302e4400019214480e04c810000390b031302c43c6490300550500590b07917900290030701c1c903c4004901c00d40010501d07032051303044d43e410205520009451041640c001141e8580d01c08010001000c2001015412a90f05c1c2800c03000c007100880403800398081413040100a9003c592111481e40f000c1d81141d4070300e40c0190003950380380c8c0c0724100030f0400d011010050340010038895000481511911 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 978994334 1250 978993084 978993097
    0xa092301080a0c0324081e070b1c0f0209040606080f0705032e0e0708090a0b0630070621051801050a15090b06030109020714060103030206010302040b06 67
    0x8540035000e03251000d4070802000c0d00c282050615950310761152207441aa40c1c17130f115803200c40e0960410541400302440c1041d0b0280a14240b2a0042030440c4e503611021640c0300984184590300ca0701c40c00d40b000045822050242c4000c403081c0707004401c1502a4bd0390300202007118040c0d0301840700c1d41c0d95850488000341c080751045080b21044011901407481600156045440003101802804500d10701d104070781071940e26141040c1079420208445020444e416034803030f4440c01c01c00b620b850a030036942c0c0c0f911000714000300605400b400040d416543d0151210060b40040101851040c0c800a500d8030b41c2d114032030044d054400c0c00c00c0002d90030320a0449510a000380d50450030000d88185d2044040d000103060609500c0c84d0150740c0c849880c0c01d11900d845010388040100d00004000c02030902c00c201034001e5603006040034821215a1034603000c8a0445201180040c0d031000c0d5400c2903070717501c1e10858421809019410000040c59800240030b81030b40d00840d403c01c01007082c0c0080003210310070103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 978995584 1250 978994334 978994337
    0x12060912030c11120f1308102403022404080f1e060618040305070b090102030f100b07140a02041103010905010e13060b01020c090106170603030a02060f09120a092301 73
    0x10041c2c2070f134201139117014000380c82000750701100b00d94540303c0b064141851050b10115003a99020800134900f80c10400c50107000180b01e80000341c0f030858000c0362911904500c0e058525000302e82c0d62000519000843e00102540002c0d0f6406510344490140c80c1d1071100c2c00c3d41c8240103030b0030004601800c040307103043c0079020007003403681841120201110f190754014000e409016090009001090800c03284c14071540e45800010395900d04a0760008142d90045c2c40c2c2007080d2a020001d00c510350020080320407554020051141c0c6c1d40b03003051054584990600c0080d00705040c80d40c1c03402001104000341d0f050b11640982446540c0c0c90300803103080f01c0000c5400c1d0760450034200c1e1110102da02540f11140c02081803055510244411001c00c050f034100380e00134400214180100140641d88046090f00000c04038061441c0100c011300095591001606403060200f2000c040344501c0c83c104903050104004410140d1500e07030304200a4510b8482e442440e640d94850074a00804a076514003200312082c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 978996834 1250 978995584 978995587
    0x1906050a02010e010b1c03050c0303040b0406050901050910090611070813081209100c0209010803030a18110f0a1502030a0e010c0c09051305160915080712060912030c1112 75
    0x2003a1981c4941000e410903401d1003801c00040c00c9c40141030008601c41c6009006104140c10507107000300440d800240302e900700703915040034089040c03000310300708003104142e01c00482c840c3e900781000d40007000401d48620b0b1010000510030108003401c0c0207446449105600e401c0840d2303661035890340b03070f0942c1c5e254170107801d004010100442c50722404026205001d031800380d11004250f80401c0c0482c1007038101c03084a52000c070400c0300303942c481e0040001030245006491401001540c411501400008005101d80c07107004c1c049903287c84001590700201402529040359012161002c2d4482e4055145940051410a039040c0c40d0b50040c041344980b01d82c4038030061081c0c0e14100c0b4000083c1400b0341841c0c0742454126411020980c100712840c030022480300006041c916140c000c1c02107402c0c1c0089440c0300303418010300300314400001c5503c0048071184560300440108070310b003042c010442080014840c209800a558541d6410303032040d03007110000d031201c0400106180c00c880d5144000807540036903450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 978998084 1250 978996834 978996859
    0x615231017130c090e010902040b01030b010903060209010314070e1c03081609120602040e01090902091902120412020610150e0d05030a0c030318030c08091906050a02010e010b 77
    0x41c94081c102206002d206010081078692940d0310540f0f401038400c1740c40b42c1d112081c4d1402c0d85441c3c03040403014242403c1c104114034242d40043c2c0030302c002d8800982007650101d44400c0a0b40607801800301844645000d5540385420b5101800780c4034000b101da07004100b4100d210940c0e03c840b21550014a42580b2403200b203079500303004480d0703000e0b40c0c0d84100108183c2000005008140b070142210403882886c005d615142030035410100010146e00001ca000e003002c03141800350301e54030105900040007010b0342030401d80c821080c0010744285101c00c1c20501c01001004213103e259042c000b40c070105030307007590b08640356550301032200c0400e409001c034103416000756105e000e8002d400d0034018140c0074015002c1040315031541030a58100182d0392001c549080c100c1d40800d54540319146031062814200f8881c4245500d009000d42d44d41c0900802c0c8400000d00b20070959140c0c60003010080c0c0b100064650207860700d0004201c1d800c4040047d01640c20004600c02c00b403410f014510485a01501100c00c900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 978999334 1250 978998084 978998101
    0xb06042007020d1b330804080708030c0405030f06090c010c0201141305210a030f031404150f0603020d020f010c06020c031809090a0615231017 63
    0x5001c054120f0388010a002c0c40740010341000e0400032240c03000102203103d14600500d480d40718100c0850203404941622080c0c00000c002d90128000c820689424402da81d524035150781580728485d4081c2903540c01204010568840300c0040040d61811b41c15034842500038900540c0d1410141c4160110340c100142600695218828440085005140950009a14441182c1603070b009820440080501340d900f40705500303040c01806081141900510380d40c640018096486d4001d10000404100c607800107800003e1203034100007240350b00c2c149940118103041c03400f6032000d40e040d50340c020034030b0901a036904001c169210b0403040303a4000d070a000d24070102e5030805c9200050b80e40e41e1418005101030080100340c0d24400b404e501294640110b60780c2c15081103054500d8007400390b20744160714101c2048500c050104e00d07099007541c04280840c0038901a6195001640d21341c0148440c42203002d9000e8a502c0c0e071922a140e2050107680c19189041c60703010440f4803149040d8031600e400c070004007051103103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 979000584 1250 978999334 978999337
    0x31a0a05041512050715020307050d03021303051e06060d0f1511030405071e080c0114190207030b090c060313080706091a010b1801051b190b060420 65
    0x20300500d8002882e81c2c8520400c0e0303007100c45a2094566600c02403061040030b99070001012001c5450005600380910f50380c450340da0703000c0e24904004041d004035400010020b461482e4001d15071217000d440c03400b6098960034080070b01c00c0050742a503104002c00f103039540c20100988005550080c5044281081549421a04000c141240d400044d40d40c0e41030000c4100c048082c40c001c80c4208054040c423480c02c1400800480362035030755010742443c540104081c400014000b41c108400382031500505900302d516043e14042c00d00d043c01800056008500540d40c0801d2603825644a54003164071900c5002d0000d6072448200d0300150020070410100320b6014944036284c5229108040b01072400c1501d0341c800d800e80c1c0706a5401c481c1c110707045080c0720350703140d2215440b8090038011040c1030421b51400085149031a00410300c6050200c00181240d442ca89108210301040c0040101c0740100c04015018074541d00c040742c01c0c0d440301201c40105443c2d28241c0904121181c0c9080150f41d41d609001041009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 979001834 1250 979000584 979000601
    0x1c110717150c040e1315020901081f090e07180209010c03080a151203020f0a022b061104032109180f05191d191509060903031a0a0504 59
    0x11118280f200048215007100c0d00d5125225001000c0a170f00c2d11850b08070300c82d0104d11140e0310380038018030852441c1e036804490154010312001d440203198111725000180f0004071740044a165080080002c580130001078130360110344018490760719807200620f48070124010802e070036001030384004410300403a10800d155508a24000382c0018010350200951400d280b03264040a000e103a02c028242c241901401010101c203d1a00a00031110075030740060510503000b400c241c45000d071094082c1c0705030021500a000d0940c0603004100f44c054000e0ba6801d9508148000c4036600c0280442d20309180000035044103c3e40d040c0c07984680075040038130300d80d80e19112404105141e5a1403070038410807050b03801214058200d604010907040c10300e4603602c00b0350f4103600510000e4440480e01603800c84001904c002c1028524010160020003440c0c50f11011200401d0910b0f2282840c103150705106241d0b0286035400c0c8282c50802000b001013201070103040d403410b09070354480e20503034042140d0300b004d0708000070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 979003084 1250 979001834 979001851
    0x19030f02030409060906030303051f032306040501050610021f1e0234021f02010b0a060f081501020a11010e0406180608030306150c1c11071715 63
    0x2415103525802084594a500401411b52690810424160580f1a0360f070882410050301c2141c01c00318080c01c14911a1703100047c601d400456103042031800121000311101a5a026074000c3d00f081d042142c080c10040d609503120300500f82504004c23900002c0c00c03840815503000302d0085017400300085070081c40c1c00850181e014554282d1070040402a1008001d042c2603500e91180003080e000c83d01488022040890040384594882200503175501003100304904c505030700d0001111503411089014000458030301d50041800c0f030010030240e400880040f070b01c40e400d944103111b036591f0081c00c480c070760411070109015802c8500254041080300100c0301c541e42040c1400502141104049006c68111b44d2007003140611150b44008802078a0188500900c2540300960840c14200b00080c0d461840000d000403109001a1800252000b03001e01c0342090070000001200008031600540310310445c1c011200140102c0304042244800e41040800000d02e541c0104a0070f80a102d8103108101c002e0010340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 979004334 1250 979003084 979003087
    0x1303020a060606021c02031c0f0e0102070b1b09010f080a110301080a02010908011a120a0818190819170417070801050606030a0c1106070518010219030f0203 69
    0x101e42103001d880e00601c0381e540101003e84c01c1000304452060341400f104210f4104200301c0704048062a0b0010342c1040d0305c840058001d4a0b1041d00f802400400308181065001042420a0004c50a0350758400c070703100c41d504514501101c224400c148149500d05000c5882304400d981c080e40f14621159001030502800980c440340600c000382140c000340d2044c8115401042141c0465a014106800030070000300280300340341e03203800c9110111154411090140c2d02c0784011812600c3d040000c10980c58200340d00e41da44021800d400d20340c04000c8007410780501c0425a4212201280d08c403800111a10180a80074401c00700300084504180b5920658001030340726405000034800c440100020002c58000596070741c28a100c49081c410140d0045910764074207000c100c11074a404084980c00745441c0070004400650075019209146014159130441c0300f0241000402c6810000a01e012194076411081c00d480c440b00491341ea0110403112103019a002c000d080020f8043d501c1d90107042520300550303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 979005584 1250 979004334 979004353
    0xf1401020c0a030c050307060201050103170f120a0b01140313110a091401050102011506080c0a03230103150e0309060a0c0f1b0902040b1210120506010801050a14130302 74
    0x19514020300d4100355004c010300c940070051481d017042030000500050000f03214940c5540c0341d003122000c02c03c0b43d210346071000089403c2165020001c4480124a084809040b030920f40c3c148001840210801c4e40841c180d0200000e1140d00403080d6441912600c0c002d2070083c02580e01d1000415000310700c4c50304000381003400b01c0e984030240203000c40201c0000c2c526103c3c0d8504400242952506108445507104070202030085035804440294440142c0c0b1031542d0382c0c980108120001c1098031070f14004404040c2c0c17800e12050800f1045070403240200210b50712030707420b20390590803075801c000340da40b941d48200841d01e00781c1801d0020340750440413800d00e20304d04a01526400c0446130304440898605182c0d8914404015503041110050100b5440450a0900b00501c1d4107035849009040e100a840e5800003900c0c1400010b1321001034600c1e00302c1035041d006103280941d0385403401c0c061080b181d402c1c48000f03002401280b0410000001999031030442c0e440b1300101c4083c000c480d81040d8114040d1a041d17 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 979006834 1250 979005584 979005589
    0x2011d0d0501020c01150f0b03270a02030c030c1c110a06022407090501110705060a0504090b1903230102030f0f070c02010206071b060614010206010e010f1401020c 72
    0x440c00114080d40001d0703920a00e00902c182100d10400c03421025102146060040e040c0e20b007082002da4105030501552511144c0044900c2c405581e0092143c018012604200d4480812002d05d00d81c4260229000c120058042580b691540c0e0003142c0c2102d111000a88003508805813035141902030410302c42c00d45c108901150351090640c101d40c0160707002076103000900c1e1121405610111030100c6e6407040c2d050091004062480c18400c144c10000c404010215a217420f12a07003004201c02000c2e40e5640c41c820380003400a0f000f91094000e03d6141041b03c0d092820311440c6403003030b0800c140385183da142c1181d0790080082e41800e001c01103d41c1c1441e00c00034000092000314003524001408222524200302400202100104440200820b410342e40c0010703600050f41a4001c542814902e080444d5401038000311440903101401681c2030007000285140d0500c4525051542a400d84140383e0320344070b18581e40803003031003001d035005001a020015501c80740c0d900001ea401c144180c1d184102030760b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 979008084 1250 979006834 979006849
    0xc2a0f0e0f100f050609030c10200102090303091c0f030519020f1f270501050c040819020114030a060608061507060e150f071202040b030402011d 64
    0x2181052040e0a0305119001198107245940021480600c0c1c1c541400c082210211100c1d9204107030154101007051140c030380d420700038a000a0000341000a050003003010044c40b06001348003980c25407009483c1107125007818000c985507031802a0007103162602800c188117118880c44802080d4540c0c0c1c409900008007485125544c0d60b010f0f640321130321482c0180006420b4175060030b5100645d0f10019020a54000100340300e0084407c00e0b04005c2a854480d04400141402d5825802445804130083c4ca1200d80e00521143d154003410003040541e03540900582e0300c2c45180a00311040d4040c00c5058102c1e605c00b100c2c402c642d8418500555003140060001516400a6490003d2a501c40c0010310040e0751150f02280d1098040300c01c01303214501041004c50714401c002020f8801c0d80c0703c006040356070808001480382202c0504050000c1d01d410907070b20060b0302c1c0c1514800d000694180c150320750b414160003518140d41040004034515100c9900545602417041403c1158061400407440e0aa6a644 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 979009334 1250 979008084 979008089
    0x12140a050709021806070f03030b0310020a020f0f070303051e04050901060309030305060f0d0602030406090b1f15080c161b0501021e031b0c1c020f010c2a0f 69
    0xa003d03880b01c40645540314480707030072040c03140181018080c00004c6100030144141440d01410300040081811300400d0070000071542e1b20841074000248034102c10350000d9056540b81c2060150b9190700320700317200e05440f40d07081d10000c0c0c0021410711402c030b03940c2c2c030703000c420420181d24111131403901d41e589020400e204802d03803041c03002ca80d56004001c02d06070580030b01e41d805182120701c400b500eaa04000500306415031600039150b01d038007100103403c00c10301d580204040303600a001c461091401c03c0c40c80f10b409201020403070000c4044000041d14002910111030b91a505031110810b0f43e41e803501e1a541c1c0d0704030742c087c2c04000007246200804030300c2520b10a21400c0103110812400c50800d00064904a05848442d02454a034000042440d1000c42507440350b0110541305d20030844100c0e0000d20702600b00300c8003944491417003420750411030700d0711001b09410b10903600c17a0010061100191240d0807041c5c00a8208103001c0304003d5640e5031503862505450105559a82d407640342c00e43c010101240744c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 979010584 1250 979009334 979009349
    0xa030b1c0302010c0e0616030201140a1b11150402010c14010e070503070b0d051e0a150506073203031602071e0504020a091d07031512140a0507 63
    0x10318030062690a002d04118900076041810311041c140c400701e07001d032103020032441014821203400c0e401c0500c01e4000010381c54412010046030700b1300201c900000c001c0d403044000150030307a07000c15101c130b405001348810a60510011709184050510b490089041c014001c90401c07103410f54010000780300104522000c50007000000c0d1a455052a4a2800d9111340200340310703074001c0c0700801c401040c01040303030754518100c000031030741c0d44071001003030324180030300e107090050484282c10486034502942c4103103c3d1240d48006805c07015590401d100551080e0303038003d80207002d6006640e000c1c210507040f05285011159440c0c0b07aa51044510904541084c1d43c81d0300c43d040007014505a483d4100510000303008003511103030341030241c0321581510074250302c5514042c64010800380010741c0140d40c00d4004101038840a000e21066155910714500100c8060b008649400b030481e60091800089100350350400b20782c40045880da40b103902681c45040080b074120b00c034820f46040019824001040100340c4e5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 979011834 1250 979010584 979010629
    0x30702100b012f151612090f2312030f0f010e1501140a020c04150503030d020c10140114090f0c130306060f0906050607080f0a030b 58
    0x110015505464005001d207040050004100001c06001c18071100360402540c418031021080f00e20341030918002c0d4250fa80400381c020100031183c10301280303400b405451980c488401c4140c0000b034401300c0b00c81000c05071a840e40c244983c4000f46c02c140440b5030b444812940300280c615013221140c6001d881d04482c2400302004000d00102c407503507480d46030b0080c0408180b41203540c1000740a002d0180020460783c0482ea9030720307482500b81d014000301c0c1c400c1c044294034160b49250030513000c1d6441c0384a4440d140901c2c585058040c000300031211070400d6887c018060740c238005141d40c00e94081d4000344d0800030340e40287e9000c44400c085a208400384006000724205d903030b6141c40811040725031a1482640110b19540c00c00016024000d91a07900507581c050141c0c84450301c1d107150003a0704680e0070007412980741c660040f50011094160804603501d58000b0303c110b0752100203104441c081c0e0980141180024400c02e14940074242c050847d3f500e0307130f00c0c0010385010b005d00024000c1c4111403691040c0c001c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 979013084 1250 979011834 979011853
    0x29040b07241d1b060a2d080603010b010509010c0204060b1801080c25140601080105091618051906060c0b0a021201031104020403050105010905010f050114040e040f08030702 76
    0x3181c500d5120100345890107000c2c5038441601e005180410391040a00c2900005050001d07940145a01c140038203803507004584450f1200d28404400ca05c040b481000307e42c0031030000700c0c1480c0c14003d1825000c410794646041c410f0700c2c00107660601a003001280c0c0543c0701e50020821080e06005025041031680c540640300300c01800140c40c68030003800c01c0c3c94842040117612001344070086100c148017a9034400802079155030403c406811417040c1d4115460040000001301a0815000785005110302401c0d0b40c18400e0340a0800c158108a00c01c1010f10040c604170101c0040141e0310143c2c1c402c808040d004034500300c0020b14811501560052070100d6600340c1401700f8003410070b4400390f01a051a00c1140f4100508850100071441407000804068640e400354606407115015240110b60002c001e0115507107994002c005401c0900582e1200c440c5d91500054940c0315040c1e034205410741c2c248143ca007a0030400c150702181d00007801665282900d07548000010302c424001e43c400d070180ea0217030401d0f88 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 979014334 1250 979013084 979013111
    0xa15060801320f0c0f07120f0f0f0c1202010912050406030c030e06040222020c1b0402030106051204082803241206060509040c29040b0724 61
    0x8000b6020741d1140020300d0810038481101010f1580000140c41c01949038100300c03104a00038400c00c14020080c090502c1d060000c1074100725a4503d040c802e40720744d40c0303206019204444415041301013400180c481c8052101241185030303032110004203031001140c0c180844d00c41e60002c8144044e418002100010704004240d410700c1605510f52180c40c0610040a1850841d5130341c50003e003010380300d040104101d13081d080b10440c041419072642501551104078581c50b80303444808103070355440c0500d0781c0c2061200b02d150a00c04c5030f05980b110b44071030342050b201d41c5010400c00301c0100216420101000010786103411402882d07101c2d5030101074540b44841215004080e42e04001d040714003420314041c60b08003074401010500503940710300028039002d40c0e0f50078001d000d04070075030209400c1502c640620082c419120602815075480c0b441d0301d4461085d01805034284108a40741c5512500240030512034424240014054a8010f0155110010398540b2003440244540000c01c140c0d0383d10300c100054403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 979015584 1250 979014334 979014401
    0xa2301110a1d1c0b19050c0901030c0309150605030c0906100c050307050114090d090e0c070314030c091908060c160c080f0106060c080a050c07080601030308071205090a15060801 78
    0xb50042c17009024a04244950350751a0156001c00c2d41495280c0b41e207480e4492013980070b40211604044200c82749440081024020291402014040e008030b0810181074205000c07868040c01001d0300d90a10500c400d2030480d030706408201c046600c0d000400030710011420900503d00070120380303040410f45041080d0160701c0c1051000c981410300660220401840309070a21070b07944000e000d4407540c0d60307010518082311480000080004440342c00710603c81c0b43d0000700041c00400383c0a680003190390741003062100c0c001007036210f502001d922100004174000301110140200307810f1910000c0c1042e42c1031b581c00d00052401d4000075aa1307401a12100400f00c1300340a5900103103207504255850380d12948914035140314002103001440030028059003204010000c0100412151054600d2540c40740780c010a9810141c03407101c0060170f0100c251000c4007441c400e640c020b0880c07600401c0b440d0300c5565480c4040301a03481c01008035542c0c03040060101400c1c0908150580c0d03603040da400d840c15200048030079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 979016834 1250 979015584 979015621
    0x60a05030a03021209010e0a09050906010b04030b370c0e0a0f090b1c0812010b0f0711030322031208160e030a2301110a1d1c0b 56
    0x380e0281600c5000b0a4000c01c0fa040300010f0740c600c03590344002440041e00c03000102151036801165100c400107178820598450303405981e800c01503842c0c507641e40c0c03e43d6161380110301004d0184122807000c00c0c890042160491080340e948500746000900c200e0304822032007001c184c2c054405488028600040750302c110039201c0e0f90380171100f040c00d090605040f406040c0f07240c02034001c141d07580c01c1c0701d815959607480c650120318054104614811003e24107078051340c00c0000c58020301000329001241d00410141556014403141c0c4680713080909030303201d404614244a031180e805000401a0340725910f038414006618012074000c48990f94a940740604154422002c08001c00440030144108802c0c8901d50746100d80d154501107101d41c41d030074002400d003803d8503002060801040955004040001c2d5004402c25001c0300800c01f000d850990b40c451446152034110005942d0203c02600d1812100315200010001e0328a1901c030316018028062500001707420343c0c00318150810070542e810700841c00500c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 979018084 1250 979016834 979016839
    0x2604031202031905221208070318021924021006060903170d29040506100315030203030a0e12010c231c0b040e030921071805060a05 58
    0x51860404480320000c01d2039440f54110903100d4010404075250300c81d8901e2038800501d00103890200350301d8000c1b800030010300c44001060000000075007a5000303200384030750200c81a07038030561402103508128503288800305c444141e40c0b00250218600b1440d542d8070745040001c0644802c0d030308240c803002c0d1502010003184071400381050f00902c03000d80c0c0035170f54008880c1d1080c43c81100350202405070986020300e1341118040703841c001c4110300c0010790342d12000b104480c2c448480880c02e03108043c0030580b0307800c44038540c20a411100c860b05c0144213600580009070704080500d0300d00e459500083c11640104200000500801e034030303290764900a41d40704030402c0a4002004801d0788490094110403090060501c0d6988a90b1040d400c80c40c20403c40d121250f01c17402e032a03100880aa614001482203900007800356280c001c1500440f44004100c0c0d9610310f0003020302900590451a40110004410043c0c1540c040d07248006030351041d000c0040c00d0100f003002c0110b000d01c1c1640620884440d40d9202a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 979019334 1250 979018084 979018087
    0xb0102070b090d080921010501060f1d1003060e101d09071401110a1401050a0b031e161d161b02010311040f151e030c2604031202 57
    0x200075030398080c983e5903081c0d40400d91070f4032003166600040201303140c13080c030b10b5044580002c510798041381940090f05a4482d81c6841d0562a00180102c503141e0112aa0304c03643c482c680038107038441c03920404500440203030749030105110780c0f40c0c403403000060b0080d60038086000842c40c0a04c000c0c4000b210081a4207442d07290f8095529064401d40d039180c0c640d214010025000b6060041c203070344079840d066050000345040b14400b525501e0718600c01032061402000c1d95180001189041013140645856000020700406030381c1000050340e81e0500d40042103405a208120207071110b4159807040000529070b00c49039040300e0b0b91401c107491310408010035450768440301d500d00c0380880b03401405400c08000030385441080a150392005030010030507400406034105020400140d85046021060259200034504049264904409035900310702c5c04d008ca40d03240080071403010510721941c01510340a8152a11319244500d00c1070203204845515801e054504501c0100014150880e2216040498000086 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 979020584 1250 979019334 979019347
    0x3160827101107060e150f0903060603010e0d050d0e0d1806090608011712160c051e09090313060309030e0d03051905071b05091e041401020712030b0102070b 69
    0x4580f1031140b0f0007400c050114456215405803584094201c4104042860030b540f00d0307039408910201c1c0c0148001c54030910816000681600f0103000e46000c85164600600340c80701801c0d0103540e01d410041d00074028a584038524604010100440c00d8103003002d40b1120807072083c0346a240d81034180750b0051024400181020040b00d640b00d51270781e0441c2e00ca07031f0400740da85000a61440c2410300b00010045002004198407500d02c01c501404005a8864900c4003a8155200c050200441d004030700041c0584140c152030702182071401760650700030600000d403860b0408404011801d8203039a000500041c0c2d55040c15020141c00a091003d454400c80e5602d4142e8110307a4018124420b28280d1355007150002c42290416005109807003180d40e000baa00b440f100301c118422040345140b40b0071386220b00d80100100b90f0f000418410306a00341602401100c01d65902c1d01d45110305002a0004505590308001c0b59010424181e02100c48106541d00456055080c100080c070300040340e003003802c9010041024 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 979021834 1250 979020584 979020617
    0x9180a0902211507030914100b0301050112120504030f0b0109050a0509070302060f0405032512050a060c0e03060f0a200702040902030312091615020316082710 70
    0x10f44060014000c2e105082d5540d00c00c110054819460000c04850b100c020281c420342000c0b40f0700850400c5603000700000d0303070f010302010300762203080c481c810442c21300b280b682020400f00d44d0303112407013040b604080b4545a034a6841c8007400c00106800d5520f4040700f030050004884500810b40c100020500920140c180150701503103c04592000901c42d07c0000707040c000d035145003400e4400a1400a06860041c54440c1c1c60005007140c0c1c0c0617240310088001c00115204041120315100382e60410000d11400c4840d40d0340d0002031407212019010b00c050508014081e6030304101203803244480320103d0009081450055058036940110845940c8224004a01440e140c03000e80d807a1540440e40410759403150f00219045100702c2a0128800d12a20300300504018001020340d0708a90b0060002840341d51031001290003403061404c1e0006800400c045020003010000012000703014000541c50100c0c041017901444080300344910a0141130500f481d80752802445032510341c00142408c8101d00c014100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 979023084 1250 979021834 979021843
    0x5010b04140711070f0909051905060c0c070f2411210d09140c150d0207150c200c030604080c0c1005030603010b010e0604090209180a090221 62
    0x40c0030800f10403200c0351000001c00c4044020305400b101038411544070728a04e405484084015501d40c80f071a80440006141c8484d144502900300d800740c001038036a01034511095100c14201002403003140b00c00b04007104045040b0313000708220f04602c840d42203400343e824050f400001121060000d0110b1142440c0e00c04142800d11603001640116241034604041c58903000344202501003078605890791041007030003400035401079109401c0303400c140644800c102c14040c481c00f042ea41c461003070058880701d200c9138010301740c064070500f0420402150318444000f00ca9004402200045504107050940890000098500441223000d00000d800c00f402003030b5654400b85c001045403400241d0501c2c590000d201c480755415000341440000c0d11b00d6003000f81903400c1a50480d10a502e0400f1801c1d0b158020320041e4000710015000608152400362002c000350010302c90903412003000da841c06039007094032803518801e021090b070002ea20b5070701b03005120b00c0510004410800d042e0700005141000e00014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 979024334 1250 979023084 979023091
    0xb07060e0114011214060f061e2b02131a040b030a0b06190902040f050f03070306050a02090613090b0303030f0a050c0702030307120f030204031515150305010305010b0414 75
    0x80980b01307101d4505444010041d80228042e1300031502804010602044418061501104c12540c000850005a41e00340c1881032803d81c0198040c0441c202502802e103900142040400e120760401800d4020510030b21518501d201b40c02d6507a0191190006071101107415030300300350350420403216400d001c281c0d241e0141c400602152044000a0000d5640107100c2d00c1d148100c1c12010146596800c0d80c00c041d400034000e44540c0e1401c07400c0402d05d800e1400d1501c002180041c01021360311300c0c589a036070051801415016071030303800b00441c02141d10358100410080031146c0c045214a0714000d00302041b5044452141c1c86500b080060000e00110b82151030b4000c0d103030300b0300099903441c1d0104d805230030710030340500035090300000c50f80c0d03801d00c801c0758030300c02101d8646c0d100c11480d40c4506d4002c504070701c44d90000401c503c0c00d401804410040940c40441b03150310140040c42042d444104c0b80705841a002c96120003c0d8075080140300300402806984420b080a072420b01c00403001300c0c01d5107440b42008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 979025584 1250 979024334 979024349
    0x411070b13020a0815062d100306080a0c1505030402091b04090e06070809060601050406030b041d07080721112214090f120a030207020405010b07060e011401 69
    0xa01c03540199a121005000280f00000440e0038003403a504804520800840e035240c402c3c1800481200c1080716030071004600300c1d4001d0780d502c0e80c200341001c00a003289205034020802d40ea41c1c8001c00c040c0c0701081114121400781103a0a12103180003030660028620070000000c010341807043c0301c010303100c0c0501c0e95001100c0144687c0307c4021002c065443c1c0c029a840280541e050a98500f00c101c004103d03d4082c203c1d5940711070b5103a0314642055a6903205580040c0096020442040402c1c805d904c000c42c505002040441d14400d003c101c4944407190780c440c401103810890b01004146410404240204560300f0442e07050140b0780300054680c17244a034050802c1d000212031004d2a41c44481181c2101b8031810f5a0b6001e480d100a640010b0005580810105080c1030203d000300384c0000f50701420000381001814816070a801c500b46035044100e1a4060540034010803005a580e805003602800c00e000740a9114950b6080800988260749100e41a07079162401c11024180c018407243e040d910300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 979026834 1250 979025584 979025611
    0x213060c030c050d05071a04050c040e150103030f0809010603030f050313060e0714150304121b060f1a0f060a090302090c0d0c110a11040f02180411070b 67
    0x31401d05440310700c1d4011005010303000300320746010b10039001400b5000b158020001510860100240c03010481010b0f6400342c20b0380c1c002d808294032480c280d00031405241c240c5050b2801008503c0410b012409c0a07001100407840d540141100168464501031788451186c0080c44860700e582c50203441e10001060311404c018000000469000440707000b848a198000400c0211799200040240c454485000316401c104807080104654030300f9180d506401d0b407c00c1d0001703186841c1c0d5940c40c8a0f524003101e03d00e0a002d8040c009012041400803d42c0805000c1c20020a0021104650b44101c80200e40c140d58410301002c00d80038107484e001d041540707035842541c000307944002120098580c0340d85d40e07100a5100c4154000c120040e04920082e003520b0b54516401c2c0443c0c004400c0c150790080710100c100200703a100c480c0b2240416041ca4111a20910103003000807610307644031014050346d11040715200480e0729455020443e0506103c0c19900c4d40e82e88280605141160b5142d0024450180c00da9001c500c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 979028084 1250 979026834 979026857
    0x60f2e0e0d0c0314071a070c08030d0e1c02031207051e04151103120a1503050115050307080d030e120301060917010c050f1c150504050901021306 64
    0x105100011000018010030001d91580703050044550349000484050b010030741c007007a038004005200c20503240540341240d103400014460a03c540c20074441034400041e01c14001a4007081400100803069070420040380d0f01400308130381441c1227145840417142c1c1c00001c90b0154017550100517141c0b2001c100318a6142502c0352081210240214810005d0705414406051604a200c030000e01c12980300c40941503102c0d500402c10749a0081d005003140c40340c1c00800607403044020b50031545070303c00c1d400f00c00011646007103114001d04258a4004650580d5505119041000b0782d5446200602c0b048006007811402c2900c0b41e602ea41c2081c0c4030000307040d1603001d0340a02c1c0009100404071010301d03128103a00c940c0d40707600050819005102e401078403100000500410302d01030161030183c1106031122031a001400c0c840c0442c03544240d84c030005820030003c1c8800a020300340500240d42203801071000d4030038109000c0004403179000c1c01c820b0306070b0b00c100541e010000024010104032040f900304440401c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 979029334 1250 979028084 979028087
    0x16080606130803032d010f0e041e060b01110a3807081602011a091503120918090705120a170304030e120622051203060f2e 54
    0x12007a8118240e82d000210400c00ca031036258040782041009164201c01c40210b400b14110544020302407000701d0f0320b150b8002d000d072201c411906608030784285000804105020200504120707907007021907420341c1754541015a0342e4071a18450741200c001000d000f00030f840da6107421054003981b4520400c210680300e507424180e07880d003c480c0381230502c4051903441e15042100503c18101160960144024280c03660b807440e00c1403243c1442c210f070140544401042650801c4043c4100400d54281c0b0160300c2d0350400182c130b050204a07402c1e0780d00320349152a1144641084400301006508080e0304059404105124100283c49011600305862904000c1c5030101020300b000c0300548042c00b0710051401e070b002900d828000030b610075402a5580c40b0601c0b60384040007884001000552295030004d008113031103411800c0c80b440034030303090500d050f1401603d596050414035003114503240010080104007150818901d00e40c911502102c03d00c1d8a140ca804a0f071210590384442c1030326010814140e2070459 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 979030584 1250 979029334 979029367
    0x2409070507060e0a02040c0c03021203062e0323131b080d1e021e0118030201150905090a03080c070f0813141e0d0f0c080616080606 58
    0x10b401200503c000d0701544a03542d92504c41c07100c101e01452410b40c000e07403c18811200e0845ca240e00d0703800b03030800034001d501080c0c036600045d20b800d40c00280d24050200980311840c1e40c0c61106140d500445581074600310190484010400d5a21300c05000076a5840950003202d8107a440300c0300c07090801c2562128101500354121144a012000c0000000865070b10700c0000c0405041003583c0c0d402041d12004c1c846540031005a121600240e4807023400421054031000d0b454003003000003000000c8076800c64010350030640822070181c4c00360b503462010300c1f03498120782d0700c0e5000790551340c00034041820041409691044010310141c1040300c2e03c07000c0380c2030240c40001c0315000342d0800d0b85440040102d080c24442c0e1352107141100003040320400001090203c00d04d168000301401030080715210302425105502d0b810a03004180d0000d003c09605d000038003c00c40c0c5140060154003991002800c0a00852410070080c0103a0526444c81c0c611a07903003680b003902c007035100c0e0080c0c0c0d00c035441b212001d4408040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 979031834 1250 979030584 979030597
    0x8040606050d260702130c020a060c180504061a0a031104091b020c21031e03010602070608060f0d081c0f060509010e1315020403150524090705 63
    0x4002d0b208031200512034165001110100c007030941041e520541c50142002d8424000d0003500615061440c00c070307030041a03200c000d81e410240107071901941960b0315481120324003412100401c2c8290320105c1c0c10380d198080d0f28003621064400b0003e00d810304441e04c82242645002c021483c50010300b203002d081c4681c1100e2044c40c0d03400002c5403501c1c1c4411354840034200c5501c11071074174a501e160000c0c0d000c1c0700081d039445440c40940720816031070800b5881c12080c0001d82c9103c034a40320070040c2c81c0e455009650b0000c0b0303c103603240b1301c0e43c0c480d414418000d003046800d901c410100000759091003c60b58615402c10781c208011521607001001e24941a0480d01821114070307400080c20120b20310401302d0341c00641c0701444101c010804241c070741081051000080c003602c64a04640400240d1f000030742c0c12060314180c0160307003d034107122040009005070f90160704212800c0006d480407141c074a8240c012281c1118000c105c6517880300488200340c100304a13600d01c8a1281707443d4004039209501a4084071030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 979033084 1250 979031834 979031839
    0x4150e0604091e1a04050c192a06091101050a082202060a0804060e03120105040903180b0c06010b1206040c09050d06090b0703051902091908060906010509070f0804060605 75
    0x14107060007421082d01c0d04544c07500d001d141041c0024000c1c3d4482000c6480064034040222489910740b02d04a610300c909030200e424008081510580490506030185c550320300ca1310020802c645186065405200c0d0255464140b1134284594860660000310260380312100c4a0607071070001000a00340c007106032032480a900494006800c404556008000b00d10682c043d05080c8020b51014610302e55078450500214884038a01e00140120b15041c0c0240c0600d41c0646424086d0503600f00944108200f140e0013049809800038066440c61802d0060070300400c00c11600504106030710ed0f081c1c2d8003100c02421a8400c40e03444a5070b0300800c0c06070002001908019090101c496501e1034241c00800c13005605894141c2d8402c0014041440ba0141600c21006281c11008880030021040041d4106440da29800b182014120031402d02c04446900248502c200800c600c0c24810a05400d04e070040c0c100f1b41c020030310002040045a000690340f001a6414038001c8031980e0380e400c000c00201919004503a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 979034334 1250 979033084 979033091
    0x36120b09190b2d18010b150717040b13031a37112109070e0a02042c10062115030302010c090e040b0a090305120c04150e0604091e 57
    0x44500f400e1280305081c0c404c060003005801c100d1000c100301c03e070444200c00d88504003000301d03000042502a040200000615855003031646808400000e03410006034042302183c2d40b02c0c10030606c8812590a6048031585e200d40c507041c141030030107150001c1c241101c0000c03410380714161a4a00100e000d208a403007002c1c4000c0140480c8201400c00b6941300200107040300e82c002d2000c0481c5005024110b01031031040d0b00070100c8074a050f1010000070401440405000d85c02c0c00300280086204400c1000042c42003085200c181020501c02034002d0050140080d50171032800503c0390940084140501c625820f00c203101809102e0010340c0a41461509001810312a00c0c0000806405401141c1c8000342034984c5610f941c0c4031208114800700c201c901410b60784000000c03511345540f5510058580c0d02074a0f059241c0020045c0c0c9035440142035401c241e540390002800c114854100c005205181c000b450708800e005403107400111203016a005e511585c660342c020a410485148041824012800e4030030b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 979035584 1250 979034334 979034341
    0x30e15010e1f0f05040c09080a030201020301051201140a020d02040f1421030304110d1b05030d1b120201060e0109061536120b09190b2d 60
    0x6101a003060340c100c001d07011550b0407244000031600e00441036503880076a003820316141034100b1000e040c501c2d02400a10800520206501805000307421407580a0740000da030f03951600080c080a0788c4001012002a407404250901d441502e1011940040607034501584850640d4070740b400a11850b4007900740030907003c5c400919555010381000c820103045444c8091803d94911400b1184178aa103a500c03030750410000500002c258585a418811005c0e007080a000307a80d640b4103860020580b800c1188248001e0304114614003007004c054031600c81d00d071882c2900c4031000b10100a014403400101050581034407541d200340300354000c1002300101c601300b8034156504d03030f070070802401a401602d08030b000c104842d03200980900c440f84c4280c40050110507504c03580c19450110744900a070440c40046c0b5030140012044c1c3c0441180102c2c81c0203201c1e54000c1d0400d00c43c0070740350032800c252030038090750107100542c040b80d049001283d101e00344640184072079500046c0c083c1408601c40b001181181c40c00b007030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 979036834 1250 979035584 979035599
    0x160908010c361206091a06030d0201020a1d0312210105100e060304060f1a130b0a05090a0204031b0806150303030c0d11041d0a0615030e1501 62
    0x40241940e64200058030000700b85980d10381d01c4003451562852402074a90030014524860b40c040580c1d4001e440010701c5001a60b26294a2000c070040c06c0b24000761030b0b040c08032a20301803064800a00060000714648243c0d017a0140100d054410b496902d0800c413000c0e0341c82074030240008a01c501c040d03a01d095903102c40302051085503541c440000c1504180000100d1141440568680780006d9501c45110840000c010001c03641d00081c0200d448607141c0c03888881040880c011510000100e898418002c0c800c601405000341c40ca9040321107407410100c04c40d0307107a250303803600009035681507a914001d50b550005000284c4200d80c0010001b01802154007054004180b41d032061301c201005036840782c2c46100701982c03122210001c042d419002040411000d40141e0010408042c0a16002ca80b00c10105e0852a07140c006030310030000c815000d0003110111040d820020350242200108101150030300c1c40b0210f04c424840c0150080c03607a0740302c800c0c0e2200420001040c06c0c213501c00141241e9a141c150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 979038084 1250 979036834 979036847
    0x11103040906060c03180810020706140403080108100204050901050f012705270a05090a0c0b0a1119030e04060e040606030501050c090102060a2f121b03160908010c 72
    0x2051700007511705a00c203c5030720a040c62101c100d54180c0002d1503001c3e41903800314002d42c44200b04882c425551101c141c2040341080320380d0f12450182d141d2801c10f6241071142402c0c06102d284504407180704020600c44d42c1d850344e00f41d0313042d288195281d45000c130078040140c40510024135800d02c1c0242d0030808950401c0a00002015110242e038103c2c6064101041300c041440c241407250803981000000450468241e07000b45d5008041c1e90450f24803d140352255260b4a1441c0c00c10804d403000060540f1000e0341011342502d84200030002407103011600c0c3c2d2044030200140b00010100220900710303044aa80340c0e0895406446044050101070805103881c070010306032403008980075400c18000a035000d4546080d00c51078071042c0c01500700d1350b6812420038014081004520f841d800a40250040f21003102c00c0700d0b580c1904046095950ba94011408079840d000601c02074039114140b40c030380d16a6101c1005c0c0ca400200004a03000d40352400d000642d075002c0c00b40c2000c1d400358600925a81255030200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 979039334 1250 979038084 979038107
    0xa06031713060305061c06020f0409020d06050a0605030a0f14070f02070e0c0913111b0c09060a060810080d091d060d0305030705071e030f090f0501110304090606 71
    0x11500c807202662080c0a0703007554812078502d544211541161400c0d100210300f03442c1c403284520300045c60f052101d011000d080e00282c1103800d140d075000c108003101080a1141c07001800b403c8480b15000c92070220b00402500c002401d020070300e5141c03121401d0840098101000b141c24010100307041d80b40251000b0300c5860343e00c0f210801840f070706e40c2c001110010f03801f503140107803031100e100341c40d00c4010018808a03100c1804011022a0368080b02000c40300300700c1c054243d1840301c2041070031085007409054503010034820003e110f2110311050024554900000204555880c28a1001555002c0000c904603070968000c1d29140500c4001c0180c13144d2080da01c030140c4405800140c031888544003034050340134040f0307180764000450a41d4480460300980186501c80460725081d4500200ea9881d5403c070460103045910b0384000740e11002c00c25401c660040d00c8500380746021004c80f86899030456a80e00d1038415281804544580920004030620072034000c0e0010386420b00615540c3c6100034070504020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 979040584 1250 979039334 979039357
    0xc070b030f0a060602060114030a0b0a1e1a04050402010c0c090203090d0e0a03020d15090503031e060a050f0604050d110f01020304080c09070302121005040c030c08040b0a060317 78
    0x16000214142c84520400080d14503d500402e034503070a201d881820659118840d5505100d03000c04000050003030001d0502c1411000740c003007002c80d500d1030f406d40e03100032031814501102e045c880000d000d410034514528415104841c003081e16191400166040c5003000310140c0100002d4001040400701070700110300500d1140c040320401401400300701c6031440141480c507030111008100300301621780072424003400341c050104502a5030398142d8850840d2114803040b1400e4101004014050560780034031901c0c0031185038947e4040c902071001490391a024010688100c03a400750003040703a1207400c20380c0c01030034000c0c0c00441401c07414201301601610258101340b01c0c0c402e051202c022075201000b65005c850401004103400c80301c03902041106d0100078030000401d43e09009800e089132400d800036000d004500c2c42c0352420740c00e190504c0309680f92628020141824100c8a103034103984500b110717170704c1074001d00d5040550701d030030700d064020704125840640101031020b40c505c051000c0a00030401003001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 979041834 1250 979040584 979040611
    0x282d060b03061003030504261f0b06090f1e12100e07030c150309020a0303031401050118030b0606120906070e030105150d05100c0905010e1e01140c070b03 68
    0x43c0c1d2118611400b0a010042c0020010f100801c0710710078071400202c0b0144c0903001e224012185041141c40c100300c2800c040300d8441030008004040c460340c1b1450300c0e025400c0d9203c52410102e00085402d0500052000d4003035070750f406501d415000d165540b2011160010811070440c41000243c5075612061401d0880247c03600250710000400059840200c030740c800c0300d40c0c9003140360200a035052502c120502007410744844c03191006075228455000914802d880c00110300c11f10002d10f40c1d10300c40c141c000c0b034184062a40b601c00b004902e50400801c40350b1107003045c5129039400c3c01148140c0200f0f6441481496900c0501c40450804215a131145203d40d81d00c44900c0d204008241c06c2c0c91060301c4801b07201c0b0040300a6101c41c20031244881c030300b0b402841100c0d0122000b002132421120074508d54000110031050600c40c540e4000340341d2950300d0341115200300280202068041c172060040400781480205507440081400710030540b52041d078000241c0b03100c4c41e035911820308680d00c11101508034200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 979043084 1250 979041834 979041841
    0x10b040204170601050409051903020a0209040c142d04090c0f08101a10021f1e090206030106050a18030302030a080f1b030603250602282d060b0306 65
    0x10103200347d100d07903900900200683c52203c1100b078107095000c0b00c294110302a40384000c0144c0c0300c003a180da00980c8074034000d40c00189045007204616848505142c40350f140c1e5a5820007070814241c6054280d241e813401c00e5507001003e40024000c0c65020b4004150302002c0000107400807000011344101e5440d0011344902c0f05041c4500ca00b02c540b2002000d02000011802c03200906050907000c1401c0e5440c011140300203090514550500366070401e400d080350b04c41d04040703080765818640400402d56020180000310250b400039119000501031081048408194480c06c81e103309046541c10702130030303007e609490300c03420004d45a0780315070301c54000315013103001103000912841081403051034003140c400c4404461003030034071923036002402c00e03585840350107921410011840030019074600a036108081b050f142220280c20052900000402e1140c0d28a5680702c101400344800c2200c8e50209001440c0403140c440c2d078402c07a512401010603142c080300103504000d903580c450544070b107045046a0750781e0f9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 979044334 1250 979043084 979043089
    0x910080601050d0c0b03070302040e0405061f0501050d02090f06130509070c02030a02010804060b0a08010b0a09020f04061116030501022107050706091406250201060f17010b04020417060105 83
    0x10014100400d04d0b03004400401c1644c080740090b43d007005043c5005031405070384203000c0c43e007884180c0f4207450b160021414040c94048801031020b07000700840244081c140b50600180c900c1c0252801590b0081c0c002940025650750703406070600a08004104645501904440d525a20b03041d025203405220540041044280a00d501500c900d03801001421101495801107a01c540f001c0c03c111032041d02c900c107803040d642ea0b40781507001a220350340001504440780c00802006a600380d000018191040000200203210802141e0542e4402d003808002c181c04440100d140451200509840004401c00441004019002805405032404441c032580c984580c00001c0107100342c4801c00810000c1126200054894206462541c01008903410716101c24036050709010084804010f0484175064203054841c0025403519030000c980f00800c02c00381041b2003d03d06003080e0213600702d202219102e00142c030748250007107c0e050030054820342d160765035024269505900c08807099094000ea40c008a020b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 979045584 1250 979044334 979044349
    0x706030e0a0f02060a0e130c0314060d0f0c050a0b040503010c090e01060c020d0609050106081507080402010c021315090e15040615030f121b020a0501030e0c091008060105 75
    0x3a5000b10080345044815400c005507603202c201800e050000200103100709070344611300380040e9000c4640c003162043c50660010100d4a28039450361301c08401c00306008907903c0d14142da081903503004590031004562424204900760540d0701c595803101c8240ea001c540d0020340000790003264420380007404154030260040d1421705840c0903109141c86801c0c01040b00503c07940280f411580081d203100300da036820352114ed09442c10240151544d03911b0b05030402c000c900401c907055030050203291064560400c010700910049000e4400703410001c0356111107040d036031540c0280f20551310040040103038035038080c4c20b8450750506124640305242360030349201309590081001c5004400c071402035049561070b80e9814000b091244000c0030107040c0ea0802000103030090b40150b00740c501403c4074a0342e2400340b900081042f0710b00e90742c6600751035210401038016100e0103003c0c070070344800342408108041c06040319450268031075681588036040c0e80a00c504410b030b0344d90800660701200162501a1307241c00a11840b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 979046834 1250 979045584 979045603
    0x903021b0916080a0609020720011e030209010e0303210604020a0e060a0e090a020d061a0702090414010c1817030414042903010b0a15050c1501080706030e 68
    0x5610b0120b00401e07030391152070b100394011928a000143c003a01c034011001283c2200000b01e60a00344a04034168040c8203c000c0104888246001900011040c0007488a20320755504042456004549000c09030f00950940320b14000c0a41140d0f20754124201400ca00580301d0002c0c039142c0060070101708681400d00071510006007a4980e07161508140382405035561014a03520308101d00b11050044559030700c18070b06d004a01c110070240c0c8402d03043d007001c0c0481e041503100082241000040c15a540c54013004d441c241c40c3c040728414502d03034541c1004212035500140c0c682c0e0380d51030800c17400b40e81a04515148140c0c2000d20f005a20b894550b003643c00608030200c403078246a442403200300404004840750620108000e800810740388151785080c020001f000704030546040d01090218000c1c10248520851580105c541000451805c0c241c000761003131200031103081150000301e4010400781008007040d010b481512002085d80c0d0303031071003540b15034050160500184c10920000101c901c001041a00b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 979048084 1250 979046834 979046851
    0x90a02090c19080c092707110610030201080a15030b07020d0813020a030f1406072706230408060a0b24090915040c030c090e010e16120903021b09 64
    0x9400d5440c0100704580d01a03070445a490f443c641c07681c1e0011903100c50402e01131078142d148c0d9600b45070b400c089641003070390050901e28070441d40982007016031703441103405406c0030803e14001031400d8202c0015605510a40000d0131403881d4a080c816450717030000c0e40c450141c02c180d43d0ba00441d00c0c3c80e031004a21519140001c0e601c10210a42840800c0ea030702c80200040d44600e182c080d400c80d00004150078400111501408901c03051400880c03112100c0019248541d103d00c000c1826091403406090340c041c11854181d81440d202d9109051080d810840700a040110216400307498904020801760040754915030041210071007003510041010030541c644a4086441030400d10348101b4407010b518020240c0303010310b4650240c4c0400d512540305400c2100d4180d070b8040355100d02a2000391502405900a203890f1442c4401006040010034455030060044007420508407583d160446900002055026003d40391035a903108054002950400d0740154485610145002104004401c40c08a48030034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 979049334 1250 979048084 979048087
    0x301080a0b07020a052a010302070506010e07140315011806020304050f0a0518090124050607030c080310030c12081602011818181a090a02090c19080c 66
    0x20700c2881e0340c03560140442c412034020014648403503190041403044d5001c860880a61910103981e003940c1c045899400b0300341586082095902d940d6502d034141314120b2410341c203502040000e8450005010f9407a44140340700d41320708215842c102c24002c01c95100c4d0103d0b000d4100c2d0110b844031242003404999494010318189450542880640007c044986a0185041c0300c046110340c1d51822685001410074900d46d03180ca07001c4900ca003101d503c410502d1a080c0340401c0c0a030326801d0320314504c040c0e407400d40710b03592078542c189400d0741c413241904001801500c010040040302d401031301801c0b0849000b104441140c81d594900c054210480c6203014107036104c104030350a1040f98003d20b001280340f040c9070090f07854107291007241c04a60345410902c10703c0c1c0300c206c00d00609502809401c402c1c0c242c42c030031801d10050947d40c00a0440c208480c05204225000c001102c949091041c0c80080e50040d02c5d000742d601e4200b0200314a54040200718000300c6100498000544c4107020980c0304644001d0501d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 979050584 1250 979049334 979049353
    0xc02060d0b010519080a2f1b070e07030c0c120e0a0314031c05090303070f0905060d02220501091707080313030524040b07020309030d050a0e010302030108 68
    0x401520049141c50305000c020000c50f4440c0c0c400e044154810011991140c03100e0400c2005182550b4494040c101e058010440e9050102c54660590013184429009039650317440e074040000d8644517100006d60540112400002c1c51201910054842e0700745035010050640b00402c06d41d80803e002c1ca026002c40e08080400451034042e40003aa0640ba00400a8080d03d03600d6890401c407030440c888040c42600f01042d6084c191560640720080d151181030180860f16000c90016540d000c0100410300b046034009258426500440419010b01030103040503540d485031980e1f81c4042d40c0111802034052902d07c0c0710f1a0a0701421511409440d8160341e0f0707404291401d90540240040c882d41c04255000d00d031400231303a184041000744441c04030514003408051441c00d00720f0400004458041300741b4100d56001445140050040340c3c400e51020480c0e2294a59410807803039406a40d003030a40511a0405032500290014041e003e04107403592045001f003484401141640402c2c41407200700d510a81c2e41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 979051834 1250 979050584 979050607
    0xc111209010804051c09051c0515130f03391b0803070c050909060f0a05040c0b0a020708010506010e1c031b0804050a060f0c0b18030f13060c0206 64
    0x7850b0070500440840b03000500d4911070f0300451180c04051008151b00440401090a042c5001585414602d0100344600c0d6641c03501d6850b41d00c000000002c41e081301c00002d05022600128043e46a000b03003281c0d6814071680f80c09840c0c03d1145c41944211120340c03d104400000604da0a248200d840c0540e030003860641d9155014800c56075100e420f9501400004100d8810410281003810301926409040b80e05d4007040c08207171345000d40301900c01c0c0c10410400c01c65610707171040d042d004568280b000a2a07681c6041580d50145940c100e8525100d00250490a0b0b51b4001440c40076149540001c004075100c0c0b20041d1103003a07000c42030a400000076411625007403400010780300d4082c00b0741001d140802000d2480200303209034441c122145240450f0901650034140d4201028102c2170401e04155010000003030b08980c3c0c0710000a201180c0c200005401c06025488165001e501c1c2003141c0d1a0000c040000c0b80381d80082001d0421030b0780b11140003400d14414440101a10b402904031072402e202220f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 979053084 1250 979051834 979051847
    0x30f060a1226161104020901020d1101021b1b01030c0905190902070807060e01050403140c25050312040303200a0c06030b040b041505060c010914010c11120901 70
    0x260002410b074203454019240c03040a0003088004031021401c1c00b00781c190700d050740c507008041508a00882c410300800354244d80005181d9506507250501410188400403042e01a21442000e01605000e0a1100300031000000b804801982e480d143c0110500c041401101164100516100090f000c82020005030034519401c44030140c01c074048141c180d44810451059a20054084515907070008104090081300e1041d030403103d41c0744000f840b550405480050946005408000404070001542c030900c05041119405031030b14240103512214401c50106116040351207220700a018504844401d981c510303003110140c0e80d0540b18a1200b10729500c0065411074010307003e41c0c0e01d128011491021030304919518004003000e503008070383d0300142024842a1031001c544207008a0401c140e1540303080c00c0c180640143e078819070707986441748100e14402c0d0144c82c4500c0080d02c141c1d82c00001e00b031200e6040d0000d040590285d01c41848043d00d0b40c012541d140101d500c508010103060244224544c850030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 979054334 1250 979053084 979053113
    0x180524030c090106022104060801030816020a09051005090118020c120c0601180902010e040b03190b0717090c0d14010e16090e060402150f0d02030f060a12 68
    0x24201c0d1642a0441c0100d50b218100780c01c03400c0968441c40c0c010017001c40c0c0c000890800003c2600c42414a0300d40403000d440d41c40c040c00014102e00000c21407107001d000e40040681660b03001003400c4245c0343d070790b84150f0040c441600c1c507140d4420307940004500350403c0b01040b41240e01c1ca090042200400a005400075003040b02000490700980300f02100310100f98001e4074000504d0005001694904680c90003a89000c601c04120f0740d05241c4a000985c1e0040548030500c00103507408250481c0c08000a4140000304540c1c540d0764108400c1c076014009903554240c800e000c40c1e01c48040306d005242c00c1d0720014601300c40902a95010072010300480c284001041e00d010300c140721086500c004942450300351688a4452035255009210f4004180075420514004000404080180b40c0c1002c5086440e201c0080001c1e004902840403001a01d14440444a146020340b010a4541940301d807060040d6100346d90cc0144082800f01041c11840c1c41c1c0031000c1142c02c12404007082d01c21943e200d205c0c001224 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 979055584 1250 979054334 979054339
    0x702090a0b030c10030b01080109060b0a0309031b0f2a0311030109060c030507081b2506060b040810110412050c12150c040f0b0f07050102040906180524 67
    0x802d40b03d2540c861007444c1e911300700c2d662004544101401300060141105a201054840c1081c0c001c2102d034003010100d4140305928a400b151200c964102581c00c08181200310308021070700010b4070300f03114149011103da1481426280402425034070381d03509003a040c0c84801c209110281e010400148400c1c10388000513030103400401d0349401910b50b541141e03808858100401d40b100c040000b0542e220690551041c1e0403074000106c0d41c00441c01070858080d11031000b60071568042c5085a6030f080680854120341c2c0244203000c40b50310380480c0c0320290080e1284c261917206414500301c0c2c81e040e40c080d11111580040001c1c0c1440d2511220041141e8417910035a40703401124030300c04094aa4501d2203140c0760443c0300070101d00a02c0d81e45075612820040040c1c01c003110620062181351500100001110f003110380258491908003039044041c413850740001c20030361001800042813499604000210340d10b0350050519120800b40001c2039079022102c001100010f501d50701034608004004c00003500c0e01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 979056834 1250 979055584 979055593
    0x151101060503160305010b01080c1624200c0d0815091006140909070804151a0a080c0d020103050a020408100203060f030a11090a020c01051501030608030702090a0b03 73
    0x2034502190401e100c0f5a41520101c00355402841400310034002c803115608203180103020b901d00000c0f040c40500450b54040c035454441050041409034040400000609501c035500302d6440600c41e00004010000d044443d0000305203400d0b500f014070f07070203a4811020113409003050340c040701422144544001c004201c90520303034440d40c80d280c0354400e50780c3c802e0080103100515641841000341c1520390102d1280c07200b107401c00000030151292060705401c00040c0c00c08900d19180d41c1b1307054042805100e480d5030017134038000c00b0b080000d5a10b0407003808488152038016200351185802504d13180780c5011240c01943d0610142c00551003a400700e41e2115110790014101741d195080142044800f400303916840c0c0e00442840240d19211152011010003200101103200d01640d4881c0c101d91081c103000d200342d03400000113050041e00c0c0c045415245808008100c0307403500141e00c01c5184e0300d82040703c0c0064a40140482c002d1000400c4400c030a030010141c03880c59645102030030140a0307018449806014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 979058084 1250 979056834 979056839
    0x10302060d021c0e0f0d1e140a02240106021b060f1204020a0501030b21030f2a031c0b0d08030c12130816050a0b010f17060115110106 59
    0x159003d03000f031001c1c06808041410511108003929091800552203041e40140000c2d0103403e802c110f000e02c40190541c1004001204440d0a6034040400e98024028690014444d00d10340c0d404036188490b010b910912060503d070303103080192501c509005130000350380400e6840078a44c01c100000c09090717200404452500045481140480d000100d0724803150101005100840c5003096080d0083c001c01c2c6000c1000d41e0342000024412084030003c12070080301e000c1078080e0b440003071040300c855024448005036900d458411449001b135001c0d0b6050605000420b02405001000c400c403200050b1030070300f07810100011601040101400f0390501c2c0d00002e800c2400001604100180d4450345130790074202c0e111880742220b03140000c2c0013840309407944e0b01d41940c0400100900150780c400602e110500e0544100c80c6085498250761100240507504100c00001d260a0440302100980d442e160000410800300901103a03145805e000380c0d0780030400c9602e904500380c0320ba278041003800c9200c000403501c9907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 979059334 1250 979058084 979058107
    0x904140c12010213050603130b0403030b150306010f030507020c01180f090e060c1e0706021b0601050f01050403020d1202030409020406200606130e010207050303010e04110109060206010302060d02 86
    0x350758205501a50350003040c49240034041ca05460002c043c151001491843c040e28203580c3c2c028188801401d040c030020208090501c2a030010a003424081c0440b104c09680700900d96031034008940c2d4500080e410300b80326907468800e010b0180100c0e0a0340040c04d031a9102401503c804010700d0010b45a82e207520300000340d00c1e008032915001048803000000718104480317030081c100b0b1001442c0e407007850030130400034146074804144070809440c02140c2c0c85d10366010707142001c082e10a51103070101070f90b450b0580d610f0840c004035807030341200d5088a403c0004034196006460034001c520010b9030003080841c80d040411408001050070120a00c10380780382c42d4035100f80ca0202e803c5a0050000109021124032440c9909024103401c01065130081402c0e00c2c0c04c030005000030f0070f65407241c2c02e41c80d10740348440703a040802d4040e11410759109042c2e079100d40c1c4440508401c17000c12542582c1a03100e500c002451540200742d881e05640c405c2d40500160b03803d42d02448002c0d0300100c00720315229401c208096450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 979060584 1250 979059334 979059349
    0x312092a130f060602010c0807050403111c0c0f090905100207060b030601060e0f06030f18010b1332070c11092728051c1e0e0904140c 59
    0x2c403002e4100040460401c2c1000742110b100c4000d10040c0010301d070600108540001c01c1d01e040340e40c80000c4525041040010810070009105029140c4180e0005941080400d106030810396181004103420160358201e03003421b807190b110001e44141c0000140d10022030484d0014031115001c1e5001249146015001c249813520903441000002c0b4500451109031806042c880c15400c0c04031001802c50803c1c8401a517118030240201c011081d403070790600c07803400c82900b25a0340c0b95030041501254065490708200549414a01d00c0d000d004211120014460010040c070324201e0301304005902c1e81c2c0c03401e40aa0308002042c109944201d100031503218a643c403956854451a1911300c02c0e20030518094455810502100b454032860b008a405050200c6074003155100c1c58004c05400752101556040450400a10040806800c2405400c03c900c854100352811400d4081c1d5030710742410b140c7c1c1c2108481010b00404071580c05204440801c01044d034042140020011440030303203454a0340c00e00000d055 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 979061834 1250 979060584 979060601
    0xa0b070f08030405161409010608060312030c09010219030206010e0a06150e0f040e1906090501050a050601020d0f0f03020c0c1806030c03010e0d26090312092a13 71
    0x603800034884885601d03694003100001c4c108071b450200102e107510700142c15184140502e1081290385000541d0369035007000102e00c3c00341c64a500a6807030a01c85000f490980c010520b1074054402c02000aa100da26850036210680d0954040d2605900f4124504400311011307040064181d11403002280c1100d4282031303000d0040711030712007100040038a07041c040c102000700350b25440b5624241e810f1002da280407604560700c0016840070788c0c013409603180202c01012240c0b8050115032a0504000703c1900d103900c070314042e0f003090702100c0780ca82941c802100d00e1946520841c00160165204040c11406900940b21003088942034504601c4a4804a5812002d0310045100700c5011007d01101e41810f001b0031018a009500030302c02070044200e085e43d100340302c0186034100105160380021500390880000c106070354200780302159003099540280c1d0b0790006080c80345511200c20105000c220009440c12898105012005441b882e51000c1114280215046030b0081c00f0b06d103036003600a00900c00c0c01c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 979063084 1250 979061834 979061843
    0xb16031a100e1f08061c0210050d110310050102070e160503070c06090606030b0a02041a03270a05240a090c120f060c020705090a0e01140702031c0b0a0b070f080304 72
    0x880d103400c1041114814060381080e41803003030400e031b460168894440140407030704541070040e510040d03048a48010516526040d210390404001e000740040c81d1503840b41119001da0132520744589409248100741000e5a61913004002e041c1000760950003100619401420b6003000c40c1111b295407141400d42e040880100c80007030340d1f91424401c00c0744040c46960000d400240450070141030184180302c0b503403031030845403024001000188074846400007002441d0324100042d840c4d00c007090221070f5642c01d64881110580619100250600b038126001d40121b40070609440b41c40c0c55009400008007a404800e0300c21040c200c00114818101c40e0f10203031198400c8000900070f5510b03042031003c0780d00503880e500c210f41100340101b01f260380c1d101c80c064100a101c13000140d01062030b10702c18014050000041901c0000c4e0007003060300c03a0040003501c18000a05e000c03061420718400c80a0407903003800c0718154012403860052110200c1070018150f054414200c5201d1021513803620381460b08205c90448 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 979064334 1250 979063084 979063097
    0x21912121e06080318011b0606060507030f0203090a050f010c080a0c14160315060e15041b021e1501140a081b0603040602070b16031a100e1f 62
    0x1504685110b44401008618091802e216a4000181651203a4507140d410080300030321a0306a2044840800d0655901020400074140e5030800a05540c00c09182174006c02e01c40b2800c550070b10b0000c01101c00c3e1840040030a011749051030100080c2140d0107052a0401a2a21507000050340e0240103001032021500c3d41178040840d841c000350a0741e4002002c0a480d00420f11041944d0741c94107040065990185101c250800403010795001041554407050f058528042171009002c1d44d070038103041c02c10050703400307000f01c0c0818554464010100d030701401c0143d20158038540e10300c1d0342016412039000c80101b070302d200c4010208100703522030b0301707130080c0c0d1010454600e0030006280070303090603000303195981c0600b4030940d000048582201c505810780303000d1400000080e0400040758122801c2581c0f103001040d080c10300c0400305990000b80001c4402103031400d01112800c400c2c8581c001c41c0100010070f09621205442e1049a0141c040021141c02040c0602c072a88a00c05203090107504c05659a00d80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 979065584 1250 979064334 979064381
    0x3020708070501030908030114030a1709040b040203090c09070504030506010b03010602151003030f17040f06111e09011b0f05100902031009031b080d0c02191212 71
    0x850401e40d8541c00581071500d010b130103000180900081e641142d21070501003800240135008a070070464a500004c00004002044c020114241d60142c8031903070080c0c078100021218132041c001244802d440c14841d0b640030b698210410315182a071164859060314025041984d20740d9054a0040c1c2a0052015818040018020145c0c10010032006281213503501d000d605158011a410102a00000d010001188076101c0340034064280790388242c0021003000540d180905003c10401015a400c640301810300341c2c900040501c1d40c040d9120a084020703e6841e4181c58122a9100d5000c0300d0301c1d505108941783d51403040700300e42e0a55104a40600c88000c0701c088289001400c0802c9140c0100c2041e1a00035a0405601e001a0601d21040800000582040507050a80352004000c9107a10069211004807003002919009000c58415184060188440c103900582e120141e040d070712500c0c1ca525000c0031000c512041c2c00c0603580c0790700f0700b4050362151035422104160b03505d9408143c0d0112040001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 979066834 1250 979065584 979065599
    0xa06090302030111071a07051312061a010e0105091306030312050906010f030b250c0b010506031308210c031f061d0a0902070f170f07230a030207 64
    0x41e01220302448103102c5c80c017030703055694076504800080000071604814000804841c0034004450f50300c18072480810440e540c800009036202d90002c81150094141042001c0580319980d80805078001610b500c0312302035600004540e6074015409255024200019141e0900028840c6001860013aa01e81481441007004e440903500003602048a43c6e004100401483c071030303080a40156548206840b000c3e48810194450300503100110011030740b0300040c86100382d50010118007550380305010754140c50f80d80d1000c21005001c00c6a140c070f10139054103010070019109070f004000c940e190030200110041c00950055414000703c4142040004c00018800070f840c4038020030141d0301141c0068011581040402400448842c50700d200c0c50b0059075400c5800e680301d61420001e00300d444c904540700d94660501e00c00104540780240e030140042d03428514080c4825084405c0d004051020310314200c05550348150340c40700b01050284440c0941c40041d1142800d016060400303019500428006040c06907 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 979068084 1250 979066834 979066841
    0xd110109080703080a030509030c060906061002070b0d151a1e18010305072a1a1e100e0a0903030c181a07080d05010905180604110a050a060903020301 66
    0x40721800c0da028540400000b0483c0003180e45048240c64041542c0c2c5440410ba403a6000c0c00c01c031405180240000c00890001c0003a44c07501c154003c40300b02c070392040380c210142d84458050003145001541001307490540413140d0031a400d85ca462001000803e41d603116401e00d0001c205030101c0c0b103e440040e445018400c900002d8090340e010b080210324000c01000f018104071020000326041c940c40d140081d00490107000130944420114a98a000c41c2015011500c1c00340e1080d0308640d1864802010207001b241d0001075031044040305426540da01c410384240e090140014400783c0d007020542c4000c2000c40e81903000754003d440c4001c01140c044031525015094480d5442c004d41081341c601e07408001d6200086d4a402115440c82040c84412100c0c6441c1c0c0d4913200e400000b1701020800102411150180e40c0054120b60710804100125142c61505082110305049a00c0031940000e0215000c9141100c80780c82a0000400c2001d5403030b5260049000340c0f2007a0701900104081890800543c1002e01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 979069334 1250 979068084 979068089
    0x308040807050a0b09010807110304081005040b0112030c03030e0304150c022b02150c030a0503070206070509060703050307031d032502031207030c05010f050106020c0436020d110109 80
    0x100e580d03040410913000200403410003000c10040100400d0b8209c1000c0c800e10403030b001b412450040e03889900c5442d40c01805080140c4085404610210001403c0095068a410a103030b140e40c0b5a0304045440d1000c501510200b200d6420b03902041100040174402503082d801450100e803207612141304c5500400880e222401804c82804030200b080b822100c01e10420a24140d604645400c4100f0310015400b0306809044910042c5220000d81000b078550018080d511906165088901d943e44040d03040f1580e010b07140b4075980191050080e100060b00460145901c41280c0c074001a020401000d049003510800d008401c480d000001e0011180b8a01e14010900c1c0d42c80c03400e1810402d0b0b40e940401e95500902050441e0b110000c0743c04001c0620442140d41a50f400c10f0003403112003460841480186000c2c4501005881104d2000d500c0b804c15004001e0380082001c6589002e0039000940d9060080305025000c05034038079000070005940d00c01400c1c0c03500d07010780e05035282c1600c8000050411107440c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 979070584 1250 979069334 979069349
    0x21c0908151005210105150306090c150a0219062405030a0602030c12010b09010e03060609010e060a080a0501050601030507091401201506030d32040308040807050a 72
    0x14204180d401c048641c2e5811100140e40c1e000c0d5840303184410483d40408250049000e500b41010300c541c203550054012066802201a0342c22030726041c0380340d80d0351450100c2e03450700101c05010301c034640740700034028100d040541d00544480c074241801c81ca0102d080c0d18002c88110b42c0c3d4805c04180100e0100c0c0c19003a880f0f18511170b14980c1d0514000035a5642100750090050380c0020004600000070350a86203819004510031107a561200301c0a00c40383c10201e800c034001502404500180d10300083c0f00c038021030010380100500d03401e00e1018180c410004000c6900140024000600100100400454280070740000245428a01d0004040e02c50181900c800c100e1a010706000041002030440c3d441d01c001d0074898048904a50001d0f103800038802d0301d0395140611150300903140e011502c4684a004100d041d04c0c686c1d0703008501a2103000310b5566024010122036035410440490110003034084000c000c8103410f03d90303241d851462a6009400441440d009084108070904000070281c01030310343e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 979071834 1250 979070584 979070623
    0x306070f09120809060d0605100c26070f020102120c07030605011d0115090f0608041b0f050904020310050717010801090b0c0d0b060310030b010b0301060c12021c0908 73
    0x282d840f03400c0140a400c0b11035119120002d040004a01e003580400000c08016040050050301110040e0a6440e004401e81c0e940d07401181c100d07204261507401c465100d186052250402245440c1d8007041c01c0312010490540c41664039000c501c11340720016002c0040342c0001010901d00707615002081d210181c0c4440403802180c1690780520b06000c070903a06588101411203641100c3d05011148190260310540c02e10818500100d01c840e0300000280c402c1c4e0084600c1c90110f5501c044500c1c24611a05c6042100d62041c0001e00c4a45031050b18560410b00040031603e1610716001940c003110000d441450200718000a688a41c80d070b07854100b40102091b1000300225455511103042c180e02c02804040b40c0a0001204044900e09500410100e00c0140c01191645424100044200d00a02099441d100c1e500000102c0c612068201c9040e07484541e41c0c00d0390a030b0596500d54031110000d10040643c010181c0d03105001d80d40c01e9060001c081c3c2940ca102c0400d1500010b43c0c2002050022041400e0a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 979073084 1250 979071834 979071869
    0x40812030714161b061b02060a0f030f0204090b030607020f0a020d030c0605010b03060406090209060415120f0204061d01020726060a150830090306070f09 68
    0x104801410011044200d196594509034080d90352080000c2c40d005000400d039940307000042151904c003200356401074945e45050200d01e521004000e004480080d4414020421810490702c9001854141c086e542008645000d81c114207100360380298108100c015070760202d040c480c0c83e040110503003000d010b0000e81981c18a0b28611500c456800c50007a004101c40219003041500c502042c450b040d4102074204901d5842c1d18008200d90300c20341c1e59912841c00c01f200458100701038401c46001a4000b088985801e2a0034110040072103510140002e0007a1111a102001c0c010f000364520704050714001a0380f2820520042c01094003149103540708000c00c0d00d0f42d202640c0001d201c3c0140c45d10004c41130044030f10400d4102601903140192400c60040106001c212071943d0002105856265154900b0719100e0451075655901c2c00800094a070018020440600107407410105202c1244005803528210002203854210701f507030500b000480d8102c902164981c480c8601d00540044c5880d044800b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 979074334 1250 979073084 979073087
    0x10c08010605250b0906040302071a03010e070302091305010302180c0a110c1002060405070509040b13050a0c0803070b090105100308180d050601090e1504030f020a02090c0408120307 80
    0x1510020341d10202e220a000414000c0802c400f2075140d900581030f01e41454032803041511410b0075501200503208030a400305002c01d800750b107070401503803889105056078a0400018140000a8503030002d05a0030031882035a070300d540350380718004103224501140c654511b03c1848002e406604400c007880c80d9603010321044e01c0800044681c02115850403150320141364000c1070901d400c00d10b80907804180f41028584181d00030401500c030b40d0090080d5680700703a90708188003a448040320010441e003000000122100c03800740450300041c0c041c404a4070b050060b9a254100480c00b84c000c40540ea01c0030403e2001c0040782500ca6074801d01d102c00910550810395400a8900000d000080038102c001c0b43e642c04e4031081c1000c06400220007003e144d803003622400d2071074aa181c02c0c01283c11440c1400d0304044403040c0025220031400c0da000941565540c0d030780b4110707005074a25034414218010f1030707440405669107442c07040c09421fa60030902d948a10302500c152030704c00ea214144601301d07828010468580d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 979075584 1250 979074334 979074337
    0x6010806070914041103090d0314040201091a041e050f18070309111507031704051c20030309070e090304170a0803070810050f0f01030218031e010c08010605 69
    0x7103c0707560000038050070500004014140300d190b284030381c3d1000300411100003030000c0c0c4101446041d4038100008052002c8000c0c80d400100c40c084d02041c10303580708009450004807049c0102d08a07600d198200358176000280001300d95130340ca805920710346140a1020340361030540c080c1941c1040b02c00400c210141000401076080013003070b8105040d176a2082d841405003810a2001c001402000d4802c0560142c0302084160410f21040d40000c07010400b00b04290307121b040050056030001c1c000c000d008400042d4918001c001a08501040305034003010625030360980d11340c1c40505980c005980c580c0303043e0034410f25103015a1b0001a400001d80c0900038420030220440741555401d0154514240400d80d9161030300059003070080c540e950020400044503480203160f401440d00001c20f03070000d43c0e6031040095803c080400180d001c58000c2d8410a550301a41c02170101d0060003400010600c2c000c00002d04005032a812440c0141c80300290851401080c4281c0d00007441c02d003020649541010b500618a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 979076834 1250 979075584 979075589
    0x103180b0a110c07090203070305071106011814090105040312111c0204030507030627050c0f0102010e010e0a05160e04060b0f3105090a02130905030c0a05060108060709 74
    0x1890b640360041e10301c1c803040104807000301401c2d0040702c40301075070750400d000294400c6502d03000091410002c40e000038450702d44160740922500c01485141d00300049010800a1081c03c40d240e1582c611481d058554260002407040912a00000e003500d42810301501815980900398006854154042180c00091085d41e02d9000048180c0307070b0302004d9000c01c00c020702c15a0005001c61007195400005c02109400c07800c407100208141581c4800c10743e2800358200030401700101036401c0599011a00e080c020800124103c0c140300200721071b03a4550419007190b414000321701e02074100398940b209100003049015188000ca00c0286542850800814824600508014403c9817284c1124006995100302421075141c01001306000180003060042d10f0f403070f0a030b14143c40e000002c00c071002d81101c0d03100301c5103d55100b0025000d5846564204400800e0120710075401175556000c01010503070030400703030072203070b16170001040004564181585001c80513070241102d07a0144c170412000503401040c1408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 979078084 1250 979076834 979076851
    0x41a0a0e030c1e06040515041a0f0706090f080d06031a1b070305130f0311030f07051908120c15010501020c0d0602090306040602090a120c03080313051b0103180b 71
    0xc00c4000000b0341c18490786d88403030b500a200700a00c03030344400001c00910403660b681061911b0140303029150b6050340640380030485000418000d25000c0380181c0c00c42c0d0380442c0300c0c44070740c540035a1513920003046800600700344002e507613190001c1c800c0203000100381c0101000708499180500e003c009203001c81044480500c045ca8010884008141c0a0401c0d5003c44400c51554210241c45112201c1d043c0a64070050301d1541410401c540642404134164541d070242c2000781c03007a00e04100c04c1c0701c500301381000d04240e0010b45180001f40d0040c03d00c58024526808401c55903161071281030f00d40b0b0441d00c498059400d0f01104010030150380c000524a0440c48181c0d000d8056098505098000b0302840e01411b400d40a09010481040300396030040c04070316012a008605d8903181c000504186a0311030340180b00c6950080180042404070025541c0020018061940641d19654150409a04003980306400041c074100c50101c0d038041c0a10041d848001d43c40c520301c24415240c00c1c0b035240300540600f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 979079334 1250 979078084 979078129
    0x3030702101427010c0c15140d09110a06120903030f1815020c030f07060e160f0608090a02011d211002090d031202041a0a0e030c 57
    0x10300140c090981084540184044952949203c2501e000455010381d00d007406440e00740b0f02107141c0e43c05031032180e06285e00505003d00c2c1506001aa2081301d01c2590080e0600450a0090620184203c001c211860310200301058001d01807400c01d9142c012004210b1040f50b40c00001d00c02964440c00790031148020100101d107600840c00d0030782c0107118030b121810000341031400000040e000161000006c5200303180300c5c0307880c02d00c0030109012400707816a654072503003040008514241880000d800b406020700d00006640c0e102c2e04c00d551422250034442d0801030000c01003008543c0c000c01018000301110300b820f00c1186032041d0f045807201c911342c800a0510840714000041504013080302c240f040b8002d42004248005445c070314110003070486281d0302a1240c0303800f020110700d5500a6908071600a4074420707a04002e60f409603000811000e0313020050b6420301c000a055007400340c200600c1c88426244907510707002e500e8000c1002c0d05e0084024040d50028107541714948904040300c003022026076412 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 979080584 1250 979079334 979079359
    0x1b080a0f030c08070c090207030206070f0c0f0218101502070b1210030c0b121510140d0204230108010e06060702030304090903171807060e12070801051b0301030203030702 75
    0xf00064016040c0181c03454000000114451181e40c0c000c04c1602e0098013161100da80d251001c82e042c2c6644c60f0003100042d182910480003450545584100030702c000c140c608103440003071104501d820111220b4060403000c0404000d00075050356101200b114030301c0038001d05401e040040d82c0034891000507030b41c2c000d01d107800960380c03105c00703041c0f540610f922290b042c140d243c2e0b0790070356403460300400e2031640b89041e02000f0030545140741c032507403503210f202610950890700828001d44041d250202d912401c01810464004000c110388020406040141d490030900c2000d07090389140c60200d00800d9050160341d1005020364002c071608190310140490740603a40d0703510752000c2410340c011580120451030401d6464810150010510791083c0b1810001558540c0c0301205110a0150700406100c01e0b00000ca0610445100301c18110348404060005800e80d100e0215103440e0101d640c0c80240265900c10902c100d110302404840c1244001e901041d0855046130002516031007248402807081c446107001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 979081834 1250 979080584 979080593
    0x3160f06090609172b090b091305060a080105040c06030e01020c0714030c0604030614070c0b0402010305220308010f050f0315060117010e100b0a0f0e030f07031b080a0f030c 76
    0x3800100b4035214101e0100c4960440980408001700d184400b10302c40c0200030900904400a4858549000789903d1940340c41700000c4000f040f000d4695900300c00c1c0e00c800811440c000340211406944100000039225207043ca00070100d80c204100403541e0390040100e8228000000386400a8400c2145400072050099002034038101300350706d81035000100810300200780001507105070b038500b4194454001540e11450221044003c0303400040c43c1d42d0911000c100554441d03801982d11650f04440c02103245a04030301300181c0002403c007140001d80c05001030229414140c0c0e00310007000151a0003c4041c0c4040c00039840b1001c00500080c002c00880c005603a0760302c504d40687da154088a100b001d556155085200755407400c641d65030145a4810000800389030f400d046403c000c01c0d69550011711142084100c900040124403a81d1620602d185d03c20414024419000110b228001c0e800c808041c0340f4151316109007039030091410781c101924220108001d526501c00850740352a021514032001e261 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 979083084 1250 979081834 979081843
    0x100c032f040f1413140408090f0d06050403030c0318080f04260c030303060105040e1905070e0909030a0f1404120b070e150d0c050903160f0609060917 66
    0x142c1942d0307010150000305243c10080c660303407208040d18024600c08440034100241e440e45031018007610b002200050206100034082d0107194801032480c0e03100100d1000240740105c6990080e92500e03980c1c1d00384007c164151080210318a8503083c18001010050980c0c0c04072060107402070650786000a011a03001c1c00340c0100c401401015002d00540c000341c1610000a403030040c0004014403501c0902c40c181c0c07600000b41c81c0703e0703001652000c0c074007030420038070f54102c00700501041c2280d28069400a400c1d90680030706841350800d590340200085160f401c11101d008060b1040c001c0341c000700b110681499006001c5020080182800030380c40281500c21040d81c0300d10350161881e6125141000f0400101030f110a0182da40c85e900c00806030180c0c004c00903041403901609451f141c080021041040c86a00046c4031600d00c0d01303010717051880c4040400e042c40ea80805500444c00d03503040070710855143c828014080e180b2482c0991085040003409010150280100e5000480700941142440350410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 979084334 1250 979083084 979083089
    0xa0318122a050c03160b030c07050f0d03021c0207110405100e070c0b0604021303020f0f0604080304060206010b070c050418080c0d1d010905040f150305100c032f04 72
    0x15000410030025041a0391500c0f448811070303202e0f006414022280d00303520740264064441d00c0350620300c0c40c0c943c002c0c8510940d109100491b801e00420703484100c000824070103001414034548000d030b951842e03a5540c03006c030310042120094003407040c001140441c21006140c02402401da60000c1c56442d8010842d055042035403105c401c0800d4901044061540441c1d801c5031544100e0180000d80c841408110690052601e0100c0610f0182c50410151908074007900c8201c001400d100329071000c030404a0710707550144e00500c0d00e035400010b00b04103860b81001158010a09800d21500302403036540d4000c4802d51034460b85103d59111000045242e0f564072500341d0350346e03000300c24659580c4048000ca450310300480342480482c031010005891041c2d001b60503901c3c0c1c60140c2d2110712944c10001000000c101596481e00000c0d80c400d082c1149070652007116000c0d5000d040244160441000c981003a13075100c10071001058201210401f10118500e0181e5020078015603840c0f640c0d5550712402007501903079 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 979085584 1250 979084334 979084397
    0x20307020f1504061206050906010522151e0203040e0c03190c0c050d050f07031125080105130804180e0d030903020f01050403051204060b060f0a031812 67
    0x43e0018040740c1000003600011940030b070a20105680b030003005000c1e202100c0340c0c0d000c200100070040d18003041c06000c42100b0000007039811843e031101d045039a9050720018442c0801d030f18411500d4000071007000ca28115500740b0082d4505420308001c8203075000c0181940c0c0c2031000c0400800c0150819a1a0700c1d00030345c1e044e40030405a59081da0003840d40c560b05000f41c4076800b400040c10002403145003100c1f101803000c48480d00d080c1d49990201c50f89440c400030107400d4066010850460109921f0140303000102c0111150740c41e0a0800c201c1c2140c10140001c01d03d060003890791000600c00d04161001c58003c0ea000e10440489903100d1005803200c10203002c541c0c054042c00e030120f5601940800c3c0514000c0d82110400121403044600301d400a440240c04154240068100c01c00c2c9a01d807180c2c003138410140469200035082c0800c07100e42007a01c0404041c80080b0765034841c560700d84241000022145c2a000e0702080a8580000b110829401300c0e04102a00c03000d8800c015425070420280d0140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 979086834 1250 979085584 979085587
    0x10e0a15180308060913081b07080d020f060702010c0e09070201090f0b160e24070b0f250e01030c0302040b0c030a030e03040e060105091522090c020307020f15 70
    0x6450000d15030541202c41c03d205d01140004070310503800c40e103900d40d01c07940e000c903080c0e190005581da8040781a07414205c090040c8122080498101404e0285442440c0203030005c0810750300618140303003040310045c80d8808680c58480c0c00d00c0c01581c880070092802c0c10589181c021601d900400f2405490190009031021140c00364980410000e084482d104101041101c481810011000c61701c01e154854196842011441103070301a41505450041500140030050318040320303030b901c3c40c4e06054229507c0c2e606031500c200b0000c107a0500c60b4481c0c04192a00519032520b11580b01c05442d543d54107101ca8101684d41b207060700514041d9040310042d1241c0142c10303880b400014101642e95100d41106400a4101040303180307820000010380301503e40d424400003040c0c1e43d1000446454010640107136000300c0c03c0b4840300210000000030003070040c0c070100700882c418444400c00040043c81d4040d01c0c12900d0502004402030f03000c8180e03140d103030341203c0c802e500c1e0f50044005554480303c142ca40043c0c400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 979088084 1250 979086834 979086881
    0x9020405071107050d032d18060917031b030301060e060712030b192c09030301030f02010e0405240603070906030f06050603090a03092112110105180f010e0a15 70
    0x71f049030141181045980c80d1900000703c2c50788048010101d1044402140b0a040c05002c2070481c802e03c0c40410030350000704c90812140c0080300251441c1c0d0400714031103410000051004503440711803144800d1080c0c600500c2c00340540d6614807680100341503030303081690b541c0c003072070082d07485a02c614940c0040c13401200f801c82e11100d6030000080029008100d03460441c8400200851280d0304510904602e00a1402c682c83d54580091441904030228100100215001d0302a6a40c0c4035003401141050385254649130a400340e10040c00c48070360014418041801008500c83e40080c80100351020380c80d010510740304014403e030207450303d41c00c04e582c407000101c02c1010708c19000503826609802a50b8541e1003943c0ca6400310103440952940c00b10711103100d00d0040c08a50641801102411103107042181d00101030306a60864205441e01c043da80c03480c104a41e0460010030580b03100c0e040c102c008001c00d140c220000b41c0e4400b4640c074000e1007083c100b02003c19a1201e0b5112540c030001c050750b2107a000c3d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 979089334 1250 979088084 979088147
    0x9060a20010f0e0c0a0302060a0509040f020403150b0306070f050705060705090901122105120405030405030c030f0604030c03170907090f0203040f02040b0f040f09020405071107050d03 81
    0x401c09440005141c6032680710b60758000e00081c0000310000245c40121850304640902c0303020f501c8161014240103040008020584451084c0110001d02d92030060704e9504600e040041e0910401e49008040d0030041401d03101c0d50045959900205503050004982c030222a0a0350607000303000002e40103009440c100205241c2020042a04000440c1c03032404c0c1d607032030b0607541165255a02001c2c00d40b44601344061780303207005100c1d85555180d0320b083c182d040c1440303280940400c07201202d04860540010400700054101003108500c50070046003c2d00000e070081c4145661010000c20280400602c4d2050100381801100410004680090254858508841c4480c0e8409042c8512000c1c2d030719000d041e491006d400c1c07098034080d5600108801141040e9000c00000e0102c171030020fa8003c10740c0c043d2464690341c80c4551a441200c0000200710760b03c1c5801008200c840c0241240184000a5074118900501045140c2a904115041e094007109414121038202c1000c445903004aa4805a4201d10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 979090584 1250 979089334 979089341
    0x81504060b030406020403140a120807050c0d090504150b120714070b010816060f0804031206060c06140108070e0a1d0319111f09050307080301140405040809060a2001 73
    0x11f9029080c00244c840d00021025901d143e04040544012405841c00454501c29182d50390002c0061405508101040340d0745410000804528070204803542d00410203410f240c040c841d00d0390700b840060765540d0300c1c00d0a100c003241f083c7c6c003c000441001000040d000d41c094202030400c494940851510750581c0c5c940150420028051500c05104801903400c00400080b56407040d2403071640d4070049401c00d40803e8903581d0b0082d01c100c0900401100131640000c10b40b1030340300144081c1e66500e503040058104182201c0e595088000005c11030710043c000c0003000604001210700e4404100c409540300b4602034010004509550040c43c0c0b0200c0d4008050760000181080740c1e680c944035010001c400700140c4030101d0301442c0180725084444260415456256044003152110b100811004415554682140d03c40030044946400100051202012450000700b43d080291420003803414180c0ba041c40c5402039006062180400061841c40e4074807880e0381981010307803204e4035203a000040a01c80d018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 979091834 1250 979090584 979090589
    0x1107030822050402070f0209040c05040e030904110406020c15071a010e060d1113021b07030c0906080304270c020c1c080d02280302091f081504060b0304060204 70
    0x81c07120906002c206440d1600c00c8a011542c803606000c0035034441c0c0e09004100704014000c0c4c41040c0c01c25400941d50301c0354000d503005074034020040c4d959a0740030010002194170344240d5000110060100f84070281c0c000840300b0140300304540259423500100c461242520410000030500407800701010a11701010801c94180c50800c10070782c0c1c540e83c411003400b0035030200d86005010056039040110050400820307012410300000c00261501540e010748050341084a0041000d07940b1005082003403015511015000e00318802090081910344004195130740924024100400c01071416039030902014800c00d401050042d00500c11500044000782d12072035101e102c58050100401a0070b90b0304051041c010045034060500c50502442c2661240213410080e00c6000c100182c42a0075078400408040480401141d5070140c2c1d03c1000c0c005101c403001a03c0398914482806003654500360750000101070380500c44113403014800380600b0004000d400190700440c1b5050000003840141312054004009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 979093084 1250 979091834 979091887
    0x40b07030e0108060d11030307020d0b07090b0c060a15090e010c091401080103170c06090a032c040c140f19050903060c21090109060c030506060a11070308 68
    0x120009074001520500412501550b01025070f401e810001964025080444840501144d00700101c1c9c1d03001c6045a21b12400544100c95054200300095034400072810141103884030300c0e41003d41c0d041d40e03541d96610140c405061540c84844008905144019007030042266840520506a4000305140244414950f00c030015030009004030351480008003000c1600d1040e503500b21141c1c80c2d620b441c421001d2021300d848000f40d0410440020f2401007081a00544001c000381c405100350303150140024a5888500791031407503400005a65100000d070344401074100340c401044170030210808071004030400300000c01c880d1000c1030412082440c42c010301070414007281d02e03001c08108000140c1d4580554001c40390b043c0e00c070500040d26281c003000070b084107040c0c1c4410058204030182c00d00f20303041c03000c854a03801c1e6035503122504240821401150010b40322820304000c1c0e400d000300442c0d43e51251031005000d00c001c40701d40d00c8110070204070300c4009682010702036441c1c6400e080da103031034850044103222 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 979094334 1250 979093084 979093097
    0x130b0109050a0c0e0d030302091507080a0e0a050f21011104080c04021e130b1c1406060a2d0c0b010e190b0f031b0a0605120c0310030503040b0703 64
    0x50f580c082c215544032004000c1100035440705555040b4040c0d0300440f40d0941185100c403034028103a00c200040c0034a0780c07051180a444a11580009080800c1084d400344202803c2c8010000313921407809841c0b0005003030790f0000b00103c10b08071400d08002640031b208015823a202c0c200a00c4450540a00b0954024100780d07030340301c1c5031401000240d02030014071280d031040c242401001c0c2180d000c0100342d1809254103c25a8a65409a246041d0044006a2074100192007060307001501440350700c200c00f444c19003c200f641842c1c2c0110f41540948540c59044c028a4895003018144041940b000c0e5440058139800341113600c4801022030a82e84401c071240038200740040f0b0342c8409850341360f02c82c2d20b80107911103403c00382c44a0100501245005182c00a004180300d5900e0b48050200403c0c0d610501058151b0b107040344180890911140d03c40010003900b4803490300700c00c20080d5044d4001e1401c0e44070325103e4860443ea0b0b1801e150950008049210000b000a4410403d00c064075081d0302130b49450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 979095584 1250 979094334 979094351
    0x3030c110102070b1314010c0305060405060402070c18020c0703080408060907180c0e1e0901050d030c0609020102070f0303081609150c0c0f030c050405070c1a130b0109050a 76
    0x8900780d0090000c02400c10800c0e100203100a240b08070040c5c0110300904100c0c4820900318903450865408014120000342c54008010302070a05014058118105407402c611300801d0ba140e1021012040c0102c0307040901c0100c090f880e0b46102d80507101000055401d950b040c580d680f8006401c1c1e800744c850f91625024410018000381401705260040303c0c002400c880c0080e80c007820307017402040510b0798a818086403a11803002c0e0b0302c0f802564105160007604425100c040c0d082003180414050b800b0030312418480e038012001079800074018608592044020071460320314070040c1d080c422250042d507000c6e107411078008140342e070206225002e095501602e2003030458a407411100703001d040c060b102e0021041600446228880c8058000b02405103220400c900c2c0c55107101064039009510a8455002410060140345800c1c07192507086201414280b8583d0951b0752001c8140d1803060051104002440c0090559070041c052010a00e0b40204114815a140d2402100400c002d4034031010351490550304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 979096834 1250 979095584 979095617
    0x1a071b261506010221040f06020c0a05040b130506060912030307090e0609010b1c051f0906210f0f030c1103070b0f0a05040b0d0903020d080105061c1803030c 69
    0x7080c0525810b901030a81c1005502c42070542806241c21382004075003c020004140c1561000a0701401c00c0d075024142c661180c0c07041000c000c2c1030750007852003107140c028280e60740d680320300ca20fa4400e401840302140e65690704000038814010000c00d2500300500124444041201100851045d0856101c8505445d1500c5034801c0079801181c6980e0800c803041c00602c0008192800352080343c116a98554900400700031807000c0e42d50517911f100145400350320545400c0b0000810502406008001f0000c4502e0700803140c8201c6081c003c2904c44a21250011050080002c0700045554100e00c104640c02d40f40e180c0104030041c0e4403070646490082c94441e100c00d00d004201c260848201024050420782d4910a444840d440003802c80c4c00d019080000040320b00b07001e8007912881100c0d9100241c80c1040703090107800c10065604000c10440315200500440d51400150303851102d40c641c0a502e80034859051100811148035907080030f15440b003c0c4030805070b15401003101400c05648a0030944c188201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 979098084 1250 979096834 979096873
    0xa0b0304140f0a020f04090606060503190209060306010e01090b0a090509061f03020c070e04081911030708070f0204021201090e0f0a0f0302160603020903071a071b26 73
    0x8034a402c0341c1145001102500c4e0440740e04c03005800c010000258240c0aa946a0813503409600040202c2c0e4044100211244040f00480c908414144254074008a201c00a225403000424a6043c486039404800c504c0e44290704000c0900100d5480703556401c03104030054440304151040500c80c1c91503600046243c105099800c00f01075035141e0552100d45011401d502a4114403c800d0301c40c070805200040c42440030400c680164080c903a410f544080c8183e0000884018401000078421140c452140200c000422141a150041d081c5500c5203902d142070801c0301620000a580107001148504082d10752000c81412158010410405140103014043c1c07982e209802100d0903800c8606e4690104104901d021907061081c8113032204100360122201c0c0c140040e41280e17000035804a0314940b00d090400071170019007010200b5004000c540d041001d05445141e00040c20306101803180401c0800f41d08407000503104904014208009881c1090303150501107100c41c0141c820160259880d030a0800e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 979099334 1250 979098084 979098103
    0x30c0d2c01020d1d0d06050f01080c0d03030c0207050a091410050d0b0a200c06012411010902030106080c03070e010b0a0f050d02120103211b050c0a0b030414 69
    0x20041c00d0701aa842e0003d9503441c08600c4c001c8214640c03003a404486541c0e020031000c45d140f0074403000400e170a00350800d400700b400507040716400303501c00c90280d80140d9800e03008600641c1d052401003500981c0c40d40c101e00704841e9074416a0003102511020950b00445e42080400c1c440040154510f40c0d1a12000310320303408644105504021081504400f0070366a00465901c81040c420200d00103605c01c000d0103130f92076040a80f03240210041140c2c407032000240041d500500034440b84020304601c0032004141110203c24100134007440c200c441000035820341101c0d082d150014020080c4966901c107007a02c1c0d925038004035109001d00c0d400411494900c485d268166a03070f0340d651508064038814161b03a04400401c03020240682440b4000040d4494001005a900050303038040302c0d0f501d5481c20403018208548450030781e2000aa070210b683e64030a0040c0c0140401c0025522201e44038204541002c205003c040e07005095902c0c00300744042040000d5004602c00ca9100400403600c5a48507100d03007194 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 979100584 1250 979099334 979099337
    0x50405011502010c0f0518010e151909030b06130b09040818120d0309020d0c140112021216090f0f080d0c0c03020d020a050918010c09080c0d0302030c0d2c01 69
    0x600c10141c000c100b1f2000d16014182c1810005614012480014084940e1007640003000d02d0008e120581c2c410001c1e151158801b46040240100d8150b44e075840030110020305250240812140148040c00b103a04807000c2a000070385a40c845003007a0030803504a906c910102a4041d1b05160b0070186030500c030500c0c09801e6450000340c440322850203000c8000d4034a01c0c4c001d0380c1c4214884012408182e00741c403124006c08081500d640810364180015040700e21142100f807160b44180a04a40310b901301080c964010591400c01d03a40049003601600c0e0b076450740e0003040c8a00800d40002c546581c0d00800c40041d1908802100d01c603a070740480480307585920b100001d2100c29403420820050400121001e111840140050318172510350002c07840c1c8140840e140c014880641d480300b500a5002c7c0f042a045640030b1904101d103d0418592a5403042c071001094042d2004800c40801d161092003565071403200704c2c060310013078036038150000c000441000c44c8d80c180300400054240c03c10340b40d40711a1a0014113 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 979101834 1250 979100584 979100587
    0xd0207060b010e030712080714060a0b030c0d1505041e0807051b2b060e010c1215030f020607060c0809060a050f010b031308030703022106030a0f0507050405011502010c0f05 76
    0x196039a022240d00304520846803242544112700c030520091109920a403044c100c001a2038071000100351511442d1400240035000000044000c984100c0000041c0c1074a40404076131502c4a16141600000c1c155440c80c10f604a01030500c104003140340102141400b400c1100d0303a60507907090030b40c41c04005a108039840780c8284000c03401d840354050000c030000038020126688031f00c1511820107071103640f03400002a954481482007003d070007443e8540150a4a001000918003168980b08001280d0101814960500340300404650301c080440383c040d64003103414024000d180c0300c00f40c00c0740015902c40400f4011000015611030080c4603881c4100b0004541700016441c01388152440da2010380f030038024160301050340c4041080b1000940c014450350b43c005a607050955407092030403d00f8a025425103145000703000c16550002011001380f500803011804c40307800351500c00e03d40f00d4603501039a00281400000074444140c40d0701580d0038400303600280a0b1300b803d0b00d03048600800c42c1141d007021850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 979103084 1250 979101834 979101869
    0x6060c0d0c0303090512040602010f0506010f12110c0f0f01151403030d06030c090b04020f0409110d0e010902041d07140409050708010f141b09060d0207060b010e0307 73
    0x20607019240c40314040d0500140e001c1051701d5480c00c12010f00740c81c1030f500800060030003e1a909100d0b802c070312040c1c640200a10300304240002c2c80d540b040081c0350f041042865807140c441245501c40c0c0744c002550320085996404510007107803200f00c1d1804800301030050f19a449038541c018000d402d00301344844200ea0b503090501c80c007a0f0001c0212041160144401e1200b07035460180f0340b15550103540220144841c1c0d915200784501560a45403406000c0c600602c03000303210b8a00300042c2d03004d03540020408a513040e01055204500d000c1d044000e04414202100b031441c844041d03001e901c1030380c004d40d400e0101c04800c030392588045000400080303980c0e020400400c0b501c1500c556111030880020000308003500d954465600d44100f0750481801d50b50347c2c100300914501203200306201001c82c03105e206a035161a028000c4080e580c0380380440180000a4085130f1582c4aa0403a401040144002c54031f540550070940000e03d1287c01030340c0409e01e000c41c002814a0001a210700725180290101d15a04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 979104334 1250 979103084 979103087
    0x6030a150609030b0408030a11070b090d14030a020f0c1b0312070b06040e1603110a240c0206070803010909170c03250203060f0f071701060f0225030b06060c0d 70
    0xd100509048c44c00daa1110007000b1b8203900340080c04013030301901080c0880d0401d060f10f0f03420006413808034014007042d020300506403a04001030b06d9000c04131040068a175134480078881e019216140c0e6078001d502851100c40801404001842c600000035400c95840390750b040d008425603c41c802d0003804c07030409640000c03090710303050300004c4103203000c841910348400b05052480c440000603042280c0d1400d03103080c2d003541400c1c41006c140c0140b00001510031010b40040540f0914040e42c20300d40c040006015034401903403034600c11511599030041074a0b51365070355900701500a14181d40e045480401075001841801108004d07241030756010809140f900303503c1940902ca000c450764840c10148144901c140c00340c1d500348007480c03041c404a441000c2500d452007100500003001032070581401002c40b2103012202c203014400341541c00c2410802001140311505914102030058102d603408420280502c58011000a203c110307803040302048030a0f22018100305981c0200304004003150302282e22004001d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 979105584 1250 979104334 979104337
    0x9161e090b030703140705040b060f071b2c0601030e100f0609020f19020a030815030a05060c090102150c03270a050319081b130506030a150609030b0408 67
    0x20310010b04950080380d503941ca10415000704550340341c141d003101c14100500c0c00c0c40c3c020350701d01e80011601d4525040c40d0000000c0b40d40182d03030001c1c040260380e1030206404528142e03150301030048010320761008030300c07141504003d00f0341070070203001e540074080807500d039501034090750000d02001c0300a4101d06054515010040090000052070300c0c1e2a620001400030542c80245032210703418905540e600c201d03074400415050808115000c40d030204645002103035000350120307006881c503007040d602c64404100003464624421405052401001e00307200ba5600010b0082510f044280c00b590841b1070540769040e0002c00c00c481d000b0f140001000054100511610004102190103c40d5803105880129040c0381180500c401ca076658800190000c001010201002810049103410b50f203610b0110119084e40807202010076040c100824440001d041502c1030b0740190001130301864492810103161000b812143d811600c0000135a0030105d8840c1c031a4100e1811b0700c0e0045a040303501d44584d51441101d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 979106834 1250 979105584 979105601
    0x605030c0117070903021c02010f1d0f040b09150f030d0212090307030506010e01030b06041803111c0c230706050c01020412200609011b1a09161e09 65
    0x10003011312004401a955111104a400307131301c0500c0078501d01980300251100311114484007c0c040c0c05102c10440515031021400d03070b400141c0741c4e4090240082c002c24050606d00a07459031208401081009110000340f07003481d6040c003180d0280f808c000303940602d40c84158810402c40180c1142c890000304000b040d00521b0000700c084c080750509a500d88800d0b0a020003038110001e00c1940800400500510183d03041d0440c3c1c0c101c5003080030b6410200010031901000100600780a0b240b240d04140740800d0007514a0000b4601c0c00614078030500d04010109000700b03108490768014100d440b1b100d54000e010140c0303041c2110300100095820321105641a40241c0c100c800c0c0d83d9000c110200d4441a0301d0004962548203181021400307180c14000b10180401c05191800307480180b1500e00d451383d01003102180c4020f409110340c01144035041c00c4c0892102c40e441c0c200f00c41003603c14040b84070400034480b80e249441c1d802d03580d82c031929240703a4984041030502c80e55000c03600c980180301d6050940e000606 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 979108084 1250 979106834 979106837
    0xa0516020f18070305090304350102030c0a021608070b0304081e09040b01030b0109051302160f1401060b090120330f1303050c100507030605030c011707 67
    0x400d04030704800500101150444111502d0004040c00101c54060044c1340c0c1000011000e0750600f4108000000700c01070210020100314488803412903e098000c0c00250100c2a03003000b5950f070b180c845580c50350b5500c8425294014401c050101e4144201d46210070141c03003102d8094403905140494070030030b5030000303401a200075800304501281203840d0465264244e000030206600d420450040000311807200200074140360070100c10004680e0300916080560b01c00300c0d81d00c0e00c49811a540b0400038003a206900c03100040341006034040c020311040c1c21942e244103045408061880d02c00035030a85490b8842d00c8403800d014000e410b0150700604180288502900b990115030350724100452401c014070304021300006142c02003241001200a41052100c01c8154003003540c01d0064100a080078000d103401a50011414110b00b01440343c2c0854600c40c401c442210355030000360141e080240000d41f8203402103458480d0009840c200450965800c1105856100124440702c45038103415030002e10707410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 979109334 1250 979108084 979108099
    0x90705090c0c01020409153809040f021b0f06040b061201050f0603060a020901020601140a320d050307030e01031e05091513080f1b06090c060a051602 66
    0x205a1004d02c068001803281410104084030384410890400d8466080400c034203120064000200f83c040c4200d24907580400000541001900b44c1001d85020340b241455000c2e0609503500303030103401d0790045c00b0300111390710020748a03402510711140d4620200c1021380c4240c00c4200024040b640704680d10342e110b00301030302c1d0719550641622846e085460494240e03c41010b0601070080b181010082241c0c00414141e0440c40c6c01034480002c2d544070414440c40c441d8101d4460f60480c1078990300d1605000304030b0f04282040c8400308003400b11004007000a43d010310065100c0b03030000382c607000d05030304d02c425000006180b401c41540c0303048810304e0300002c0090500d500c072000300c18040b010350312001c950001104002020300341810350b5030500c21180d01c8844c007a0780039070600c2607811a0b06074142c4034651000403565129400c4840d06010700a1072107400002d8102c0780003451100e004500d092090340390b0000c1e0703a49000d82c6005c100a81c000d09101100080c070502400c0504415011814061030000f88202c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 979110584 1250 979109334 979109347
    0x91202060d020d0212070e010c0b090708010c021e1603020d020d050d050c0123191517011b050d0c0903050a0f0209011205030d0507050d110c070608090705090c 70
    0x15003070380e004141d115043c0b0303400507030190305c051084412508070320b86107007164002c2000700000301050b4030444040c00c4240740c080070544820302002a400104041070080c0a528482d2001035103c1000c03101049164000720075034629200c0c0481e1403405010f111154220060640d02404450000605c00301d030071116019104011820800a405840340107681d19a66015030000c2c0a0944030044684007480300b41c0446003ca180c44910f5941d40031200d03100c0c003641c0c4001c8442035005031180240080c00c00055100204069041500d221a00c8901c4070007800101542066800041011001000000c40c280500d503002e0a290f00140309011651501000258884d1030319418010b080c04211500b00c1302407400c00442c2080250b45006101000c21440c80c0203243c1c940c540c41e480703594002d9144542d80c0002a00f154000d80903200502d900f25020021075515428001541d4072110307642c06180301c0c1000002e0a070744079030b00c02c070312400c0c0303440182240514100520030f016102406185202e582880704 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 979111834 1250 979110584 979110607
    0x160b1606050916140a03020603090a0b0717070503060a03030e0103140c070c0e1e1b130611280804051e0901060f0c0f0314040f050a0b070309120206 65
    0x815010780050006488041c41c00c582d0704094a605a201880d400d40440700e0005558445c2c10120460303030103840c001d60320365900300c2060402081c5800103101ca1584030130301501541c44180b50b4601c2220201407070558440351030a403214041101d10f590720204a841c2440082d01c600b100f03182110040c10f0200380600014100390150314202e481c007042110102e82c0000780001102e581c4010616030510507920308003103404002d02c440024407040054071010106040c3e20102c1034024014444102d420b840c1d400400d83c559051005110380c00c0090248042d940980f400444c2182c1001c044401c0003070041c03895404200e08449036201600c880c80141300004050701c80080c0c449001c00c0400e140b00912800d5410002c920344180c00400400259500400825402900c0d00e00070700e0304003410f00c182000b82c1c6011902d0381569818561203a00c081400652044501100d000b6100103d80030f44450b03071074052181a5000b01c180c0540042c0004400300821070019038045141400945030502e000c941240d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 979113084 1250 979111834 979111841
    0x80a150e1213060e01020a032a0b04021e0105070212030c010603050706030e15010b03060a051c0215030606030c0c0109020a0f0303030b4507020c01020f160b1606 71
    0x1811802180000d032420b90080c0ea40d030050090580e0341482c0200030030002c0000d58444554a0003424440040e05010340c0708900480064414028400e803081c0c0c00480c50180d50292081c1d800301d000350380741d2015254414005200c1004410181d4401d82030003080c0d02000700c420191000c0541a00080020700003d81003802a5005940100014080103140036402001c40720201c2e51504e42c0e81104013141035800600d0101d9044494900005440351507241c00100c0c00c4005511142e80304040d2105003000900307059801040354021540d10b4409500740c01a09028407049400c694001e07000c0000408011403034010304010081c40d00006152603056010800d02e9215400c07000c1c002004c0e490401c01c056150258400c1340c4015a00c0182c400031f14200030340d4000102c40591001341000540f00c50340d480c62400c042890314115502c99036400c0c2000082e4507051040750850040c054483ca00e4600000080e0340c00200d402c4407200c0800c1890126100010742003ca00f0322154401006c0d1103000c43c00600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 979114334 1250 979113084 979113103
    0xf03280203150105130209060715020909012c16080709030f0609111e01050c010f090f030917030403031803051501170109032f030a08090606040501080a150e 69
    0x1040c0b00294103001c1007000390740680d071030100c0a600402a0303403510b8030b075042900c00d05030740701c2e02d0f0714040c20f02c00441c0406805403146031074002141000015103040d0350030344940c140c52451070041030000c1d0706d00303600303070310f44c41100d24481814034211080252403040244030384c0100c2a2030301c08409601ca903116084109000320a8078641e4072007002c0c6061003038042c1e0100c0751240480e0683c20120301001648483c803200c0d01e40b103050010100304400328450a420054821340301120401849555141414056181c441c0541c005001c0c180c010030b114400d070000c3c001c9000348c2d00081d42014916902201d8466083c61400c0d0600202c450010001d4010031002900c00a942c00100d074942c10000310701a131150440300b4820760707810308000c0c00200340c1003c13103203028090a02c880c42c40c13510604103000d031b002200c1d90312195911000548a884580c001c1d205400384800509644480d203e4100300000e461007801081034035003007510b220000800000090b0381003070b54150b000c2481200490340c6070520107900c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 979115584 1250 979114334 979114363
    0x6060f0a17010e0108060412050d0606090e0c250f0f060203060111062809080a122016060f29030106060503010e0c09030a0809040b0f03280203 63
    0x5060400e6210311507841c90b014103104041c1545640c03410b04001c0d5101c00182c8040d05400d690000e003507000348110200c406003040e00c10207008044d41c0e900028082c6155104000c549083ea00110710002c14900850f2071442070f031008a80881007542c040c00c180e01c2684411282402d40f881d1010005d210103251350011802810700503101d244c0840094242c09440500305001d40006d42008103e090131300f9200d100307440e00c003022a000001c1e00200c100601c00080040d050303010210303d0b0105564407803c43d07a464585180f0a000302d1030000501c0308042d18407647d19480440c00e100040d0300300d0040c860341c03105a01038034010982030001c0c03c0d01401c84030350740e0141c050f500d0001d401140c1e0003c910340e041d00520043d0003c1100c64039158004001b0f005c18041c503c03004000d070000c141601502c03001c0d01d0703958bd402825500401e071503107807204a540c4054406030045082128058544c5000c0149140040000e0003074071300750560401d4180704801e2942000351000f52030802d000940c80820882d000d59400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 979116834 1250 979115584 979115597
    0x41707050301052403060402150919030b01170a03090909032007051e090f060d0503040e0109050105040e0c061c060308030a050c19080606040306140402120f030f0306060f0a 76
    0x20004101104030b6458104e6000e039209400740401611007041d481204180c2c3c001c40c1fa00c0b0035826001a00f40550100c0600755880140404005c0c00380c0300031901e04031900c960006d115600d0b005040750b22180c99040c040c0c00304842e10381c00c109100e8543c00c80600e541c03007441d110a0f10840521220308440e0505100041617000c0c14080c0f0007410242c1e18800e880f0700220802c44140030400002d55403820003804d850000c030f00c85010842589440d5800030601c2d0740201a251107680b11110340b00005800d01c00c136000c1030308000000600381054810000c50116000c09004c4a01180c005d0003066445214183c102d02810515501080d240d03200c5c7c0c0014500c034100041d0740c0d040440c2c3c440c080e01c50240850302801820071044d100d000707040f8081b8500c5038181c1085092075564000181c00e40c019544040c20390b50030100e40054043c808134031540314034400c0315201001c59890b402c4a03034400b6244849010795100b000510b00d00381c841e10281d0340c4540000e00319803405181070f103040000d0b005070300c08402081c0d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 979118084 1250 979116834 979116871
    0x2070905010506070b04060b0303040b12070f05090904030e0a05030f0615040510060323090a0512040b09060f0712092c070804050a0b010f03030314060604170705030105 74
    0x540600c9005180469081c1e0519038207440301c015400b005080104034036594803900c4c2c07a94800740f00f80c8004080c50760b0000d84405404400c8900040119400e4000840c44104c1002e4103000703805403100c0c028003130029a1603984a84c4c003039425140700c03055643d0103080c0d04000612a0340400c5101052010040034003564241402c00050200301e0a98081c071941c01e2108003c0300303006904400c011294a840c02042c0442c0490840803082e581101060b090080041000107030038000500c0b210462041049038020b0380a01281c9510780102d010b9100700d45420400c203016460a07402030101c4081c6914500d2030404241c2d40c200c2c9030b140e412414000f00f0b1506504000038280c01200c440203c40c0d0f4405240d041e0050b0540c1c23941c42d0b4000300020103102000c00402d040c06010000d0441c3d00d45c0c004014030007541c40b00303002e080c0c248281c44100c00007403c1210b5071801044400300a8090394014041600701801c00d101c40c03c074503072901c04070182480b4004001031a5030b400d0080600622201c0286100d888 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 979119334 1250 979118084 979118099
    0x30305130c0b040f090603030c080a090f0902091e0a12020a0504050a06260d0311091503061201150e060d050d05090a050603070215060f04020c0f0f060f0a0c1209030207 74
    0x42185d0000c8481441c194042000c00d4100c050200c1c0140c0c07028140790b850156400070343d10044142c00c040703000d5014070008201c00703c0e42d80c010040c20380c08070b03034401c00365501c000b5603518100002841c0307400221104042203603402610440600d240700800342400142c4441c081030440340304642a821864945c8010450400d91000c0c030300341401782805903005c2c02603010409554014140c4814101955811800b60307907540001514441c4c2c0d0020100e20f0310b400182c1c800300c61030700700f9518688070341600c100300901f00905106100f00c0d1111984008a2249000709001e150a0018013054003c0075190711400010740622414400400b00c0c3c8410b034680034000c2c180080108103801c030303d0145508000f80928940c0016810001301c0d0340b0800700c412a030304c0a011540b158041c84d0700580143c004204c403100c0600200f0815030402c10300341125454180401030680d90340c1e05482d4814080c0c100d6000c4dd103c450150046082980c8504054045210200c010822107890000940058000803824030034071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 979120584 1250 979119334 979119359
    0x7050a0c05030f150606040b070606081b150304080f070f03080c0705100c1b0302010f05060409080307050c0a02120c03100642090e0903030c0304030305130c0b04 71
    0x24201a00246180c06069002e503076a484c4402207000880d05450000e0300e03d903100800c5070b010300400500c09881e44a245003050103080c00d4005e15056000740d2024440b030b201c0030218101640001851544000c030b80c4546a82c1d20b0f8400341c000d403207500c0200725907012901c88000a010140c03140190882c4840b04e070800078001c1030003400b0708620030010050000450000100301d10030080b80180040c20202001064508a0800b1030307040640c07203403001140034583c066108504101c4140c01c00d028580d02c00c82000704030364007520020b10074207003440403a400502c104080d14050050b0f90468866a02a0700043c682c01c041813145101984040d590b500340381402d200806402c0c3c0070381400e0064508140200c10109171400c04060250410140c203c407003c40341c00c0080b40c074003056600d000e00c83e15451000741802100c0c040c1548650401c404200700c2c042c0081201e1244036248212800c544a81e602240603110281001d1074a50303c01811101041100000c4001030040700c4480c0d0352546400d0061088 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 979121834 1250 979120584 979120589
    0x290102010221070c06110d0f0e1207031b0809040e01050402150d091401150e06030604060b1206071206092307020715020c120c150a030204050607050a0c 67
    0x11a40140480781d940c1e000c02a00084041d03201c00541800d070f0716500200d641c242110000352510382000548070b10807010900038030201c1d402810a10100d01c00d069000142d8007c000b00100300e82c8100c07140032880c51004082c2c1181c6109181403152140880e1503000104203902d0309030b0741104005080212840c5c81c1c440e4081c0221288000d00c00f17450281c000030605601c0034032291074054001030301d0804110a610030042154032802000000b9a09845030740240b00c848250381581e08807142c00f1540d0441d07400f0040c800d000c010003c20141e5941e0303a6176000f0f016244011030700041402c07042c40c19443d040c058207120306a503580b5061740200b54039a81003660a1a4002a4000e2801c040140072800e072010318220407600c0441290b07181c54282040b41b50410355031042c20f8010000c4a6652856030209450080c1c44080300d486e212001108aa50f40b501100c510f269403002100703102580c01506580945030400c0c00f801e0040c14035544002180c041d5029032012030303490700f000c41d80d81c0801149003841c001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 979123084 1250 979121834 979121837
    0x30a1205130f09290307031502070b0f0106022a10090b070b0601391a0f06040507030614041109030a030905040f0c051213020a08030a0f051303060f06092901 69
    0x100000000c011a855020600001c2c00990100101802003488c640455078a41d6014500b4019843c0501d2209540602030046000600526036141c1e4610424000b0f203407032240c94580c0402d581d02d82e41c00c0194604111041100348500305400003801000c110140950714000c60a139110391034108001010b81c51041511042111600c0302d152000107480300480d5401000102e00e001000a418031800842601c1d410108000b601410000c14103121620b1f03070302440c0240c505001c2e6454060059096414a0190984070f4055500d68101ca00c1c3c1a005080c6805801007c1407904d14400046800d2070401d0105070086500c01d0802c00c014182841801401c0c0c4d010501000310744c080410051551040100008000b01d204020079052589044100c030b00310f500410002080c1e036078400c1c081c0c43c1d80000d0b281070041907010709000580c42c00340c0704440d03a02d600d0130200954507007503685440041c10329414010710240d40c1d6101082c00e5600b441035000f0b60342c01c00117803c6044800c801a00881c505e1501c110f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 979124334 1250 979123084 979123151
    0x518070803130603022109101803210603050615130207021012230402034e030108030c060a1404060c022415030a1205130f09 55
    0x1280301d01041000564070303e441c001da6101011001019001480100d03070907100283c4003484040b100c0020410300782d580b4141d0134003002003e4041c01c040c0309400c04019001c1100050b01c2c151006040d004901d040d08140c4001070803507126202c1f1072801c03000700c54200d070b41011801010b01e00c0c527100c800d2000c21340d8801815868903d441d8041074110781041d05d001f041c0f01d545d0864910625480d004004a01c162402201c40b0003d10a95212080070996042c2e029004051481c0da011041c290040c04105444101009100762070b9201c0c1d484400341070a15468010414020900001140c0118000d06080000b9905c0f0300540503003500703050b0090030102d00285042a881540c0d02442501c070750150308104002106004903d0503824510f14120300c0090f0803000b000d000044101c68030b954051550301443c2c0c45031004e298145030741c0b00c611990140c071480403c0c000f4421144210001c15412851400580138103a0760b820b598904ca0340343d04140700c0541c031500140a48182c0041c3c03034200080080900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 979125584 1250 979124334 979124347
    0x20c04050915040f05061311030303041a0a020c01060803030711060f1b04080a0b011404090302030714070e010801020406080604061203030e0c130f140c0d1503060518070803 76
    0x841d9164031082c01000c07281851400101488680c404500107513170031000352445c910b0110a0080f02448842d42142c03088800b4203040f841b810000140d0344515400b0480b00c440c0e10b004014010010402400607101c80d40811141e40303040001c0c007900340140303d07040085480b4105814013900c042c4030042600b8503503215104005506840350b002540082c042e2036480210311580507007000302e1045420000b003601c50700200004000405402504841e00100300d040d030803505030200410b90754401c202400582c014010b010200380700d56041c0c03403420352407012200b1440d40c40700071100e2001d00b680208443d035804181001503a41002446c1e6114500b01d0741004142d0401d07074040210032408401404065480c18081601001080440030404d0010400e0350440b024120300000f40082e038801030f00c01800c20b2500c099800306217140b40d019810a0340410704000051501400901c08a5040d010f07222055000001141561044601440100300200030003140701d140c1c54980b40a940c0407000740e82c8100403e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 979126834 1250 979125584 979125601
    0xc0105130515040201020a061e0e06070e0f041b08090d230309011104080a0201110a0b01030f0f060f020712080108070b1308030a1110020405060a111f0c020c0405 71
    0x101c0b50803465407160300c0d65448500040380707020000383c0d0050400e031a0045045840c0201c0003140c015819401c01801b403441d031251030a8941c50140c419038003269000c5080c0c0807503e041c594800085102400004a145081503a00c005919611610300411039003c140316403000300313204040041d050b03800c0607000040c1003d0405003e18001d00340c600440404030110710300b04801c0d00320551a10303e0020254540f034460040d03e03155650284d08902149058002c0b4003a0b0300c0104864000d01e4100020315120303861900d4100201003017000c100c852110a5000c1400101035114040140388031030401a01d03103d00380307000d411a070801c51039282400591130040111610004940b4152405092260344071f0510391074000518809800401e154080820b0700304060743c2c0f0112080004840e08100c03407000c00c6607441070007288101c0c014690040c001f0090b290310140030b0b0064049009250040f901d040e81c4eaa1100052994450194084681c5a840300c2e506a07504001c050b030088000c660400840c18102030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 979128084 1250 979126834 979126843
    0x911190b03010b0a02010e0f250b030417071e0b06011b080d0e1207050607050316031e090b0106110c090109330905101d06061903020c01051305 63
    0x1403c42400b01c0003400b40d19440c404e421000035440351900700d50b1540e210802807500c03207000e07500e200d158010901c219010001c1e4051034034126520000454038507121622141411025900d5800c2a07032001c200080c0010581c104903447c2c801151320200005845141030010f203180a080d242c10440e0034004501c0456061000360030f1183e100d014555640340c415142405098050740f40129030040c00c2405840703620082c02042c10030700c10001d0b030340c3c250f846100507115400300780c44601c13101c0c03988851082414040d5001d80d921080c01690140102ca10007070900945410b220f040300c0c0c440c05140100300140d01b0250425100c95008090a00c1e59441808980031910510a001e0544e40f0340541050390101d410b032001560551a08000000390a154a43d82014080c8102c0c0e200901d480c4c005a15401d00c0162941645c846000001d030368081c1c141700c0607103d0000740159501103810400d04405c91100e182c4140100407684001d40c4454a0403011402c5841c01090081550080b644020000b600400d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 979129334 1250 979128084 979128089
    0x120106080a1a1e0301060b1c0605041812030b060703030b010207080304180203180109050a050f030a0507060b04240608010b090a060c4806020d030b03010b040911190b0301 75
    0x43c0b407a00a8a03400c00001d01404040c0c0c480e0401840c00034280c104450041d006020140400000344082a81c8205000455101060105416082d00310860004881500425008200d450b01081c1100c030300000600c03070b80c0001822004030341c1d100b4140700b1315601484180300034107201024504081ca400c0d01d0185610070075000c50100c0c0d034000005010800400480e41c5240c07040b0008004a1502d403608a030b96900d240000e840310b200c0c001c004035809c40d001088508100b071942c2c800f8149078555070342e10013500d10019004ea1007500d940c25805224804240001d00f9074a00f00b074040d40a1400e0806003180b00180c109030755000c81006180c015880e144003200469016107011103102042e070130000f501200303100c00204c0512101e100f8402c1c00c1c81c0300109100c1d00f10b404541c905401c0340c0c0c41c0420075549042c49141c01581000011800780c6000c0da00440c8040800b0340081045034054002800321113240700200c6081402410303003181d070700704086012800755602c44500c01d83c07810071288525601051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 979130584 1250 979129334 979129369
    0x1203010b0f07080d09170f0a05180d0507060f0216060c0f0605010b070b090c0108070e01090f03050d1e02030d1d03030a0e16030c0b030c120106080a1a 66
    0x900071052000481266685900480e41e9030700c4000c0811020041c0070b4100043e191408010310307041c080f81e420002c640c0c4d800d2034145580e243c14a070850607600c80d000000c6041015041e61107000e06501da40c4012407a5910680162481505144028000c40080300d82c1c103045520060190548001410404094540d2428250700940c010300c1d1002c85400345541c01040203003040700016401d200640501a03840c8a1903480030309699107a081a56041c180e40407500080d8603001041d907045c00340c0034a04107840c0c103240c184a541c0d190b405140130002c240d0310848040d44101903980ca9070340e000c00e602e0328103d01c20241407418090440003e589000b000c800c101c203181d85e80c0d00401c0d8820500300d403402d0002d403e42031300d4503443d00c140356100070070345a500e0b903146000c0d03002c0d68400300700505241015664402c1d142c1c1c1030981064510341c0c0e40e400003014111441802c000307041404408119982c020b1540e80e407140e03803510b845c409030700c241c4030000c000182241c0c23545041d8169940380300a501068011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 979131834 1250 979130584 979130587
    0xc0609030f0b0a0b03030d02040303080f150d2d050c0f01091419080c01080c0f040603240e0915040c1203021015050406050a0806040201050a031514121203010b 70
    0x52070b120800400c2911130540c0c0c50f12000845007011581500604100c90080d2140080d136039070300c1820180322100b12501e03444801c41003203130300340c610384a01e50719800380c01140031032070004a20103120046030f034809160749100440a22401000010005003540c01000d84100d0199080503002801c1c0e80580c0c052070580580028040c03074540c4500b03895130451150103900301031035a604c0500c00d03200c048282c14140040c1d6103000140ca075107480801c40341c2403502d80c2910307483d15113011811401001c10f4104074100744119078200d00745809089900014104101010780542003000b0000d203841c0e0540c04651384514110f0800010520b4072070f100d03003115003207003812501c550f4a25040b0700f8000e043d10402000c91a0890707003000582c0c0685503c046e107070f0030b403000c1084980f1201001910f503100c5c40f407800303550b100d0000034005510407009043e0140081c14041218410611003c0740c06019411059080203e08800041840d11260704d00401301180c002c3c08200c0b6021560a0003403005003c0d40d4500b9a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 979133084 1250 979131834 979131841
    0x901080415150b04080105090607023012091504030207140f03060703060f14030d0c0f060c08071704020928050a0207030306050a271b03090c0609030f0b 67
    0x94000c035410003080c901d0825015202c3c01c0701d4600350400d0080030034135882c0c180024040300000035039a00400080e0000d000500101113002c3c140010600d410055458400d000c101080d1f4200217001c14482e141c141c55040e141c6085107505d071200051128800013045d80c00c0c000841e0300820710f5015503c08000c0032551000040100b042e0355070466003941c040c4118820401e805130305501c000196401182e00c02c0001da0f43e0300ba24a01c00f500602c115506d42c01c091a8500000c0c0a104040c105d1849030081910f4214240c07100000c40e007408504001050b000c10810901c01e62101115203818500519020f083c102900801c403061001010b40103000c11a0159003800f4114000761260414001c07018046481c007003880d540650030500c01140481e08198000c10b02c1d11304000c141c1d00307403501181d80c4e59401584681b11841e40c0d0b91801c10406899607880100c52040383d4540540300b01007591000716540700203191500c4035204030381c8540104110034400b440060759011a08481c2038018800c145182c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 979134334 1250 979133084 979133123
    0x6060303040f03201c050c0316170a020a0305060405010b010503010806070804140706022d060a02030411060d022d041707090c26060d0816120e03011109010804 70
    0x500301d030000c6030305c00840703595102c42102e01c104607882d40d403140703040d50800e1140805165468070f07522810a15842021400d2003051010f8101a030101101801c0714a4622180c010481034929a0010786194005a04210910409010300c840542003803901c03900d5580340000458461201401200801c03a00360041001c0c029a03413080401c0040440588464a581d04400b075650020039030359074446204e8265040f600f00042c0c002c9000c105006000e800166502420300d8006c0d4002001182c3d0741c0303412500d501f0561960409090040348a110041e075910541d98aa0103101081e519600c9100700c0980310002c0b84800d00540d02104c0115043e0b000710000c02c0422401c00207107070824107550340b42c0740440110903485112004000d600c5203a0101751050200d0321041c070282110a90341100807284400000745908000f04000310340308507440707603d40455a0314010042454560b07030016040c00391014030744c070307003803046600b0103400c100d00f54542202500041c000520041c40a03018000e010f40e800400c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 979135584 1250 979134334 979134383
    0xc040f0b0c010b0405091509010905030a110a06022b060f051e09040c030318050a1503090b150a0806093a170718230a080f06060303040f03 61
    0x1804004e2090082d8a0b00b010060303956056074522611103c18003020404007003061140d401003a40200103503141050081080c3c601c070f00c91380d50280d0544a103412000100703d82d4406400f045d0b030401d400300300303a12040a0700600039a0700c000405026203808010800c0205c0c0040d100c04565040e180a5680960340c00c1c030202500100414640154401c81040100510050b44c0302c20340340700703850302c01c6100e09401d045008034106014a40d0014407600e0b06000d9001901d101015a0301c1074500429054100d9586410340001501c1c001e204400ba4443c22a041c42c20217100c0014120f04402040c0528180c14840d94410203620701150021034205200481078520441d003100038180550741503200500341c0000d01b00480d40d500c9030b0801c1d940201250103e0322030315803020200070704d41c08901c1e03c0b07040c0070030591880d03400343c0720300b6425081b8200f2200603100c0f5820744c0000d2000002800e0812805000e032410b2640090006101e90400c100610450046120305000d5a07003102c1c2710020109c8446a40124 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 979136690 1106 979135584 979135601
    0x4110f0a050d0b130b010809150c0304020406050904030512010e36010603050303010317040501021c17010b0d0b06031306051b070b0f0c040f0b0c01 65
    0x6144104042c040003078010390001600d0203110001151000303d90500c4c07080c0d0b82c481c2600d02080d80c00c0520a03500c100c0c103101078180c040441c1d1540160b10f900a00300190b003031007c004582551140e611040240c078000c1c2011a403800c10b802c025110b80c00085101c1140c0014200120740100000f510324010510b4103030f0051403803259102041500225000d120500f40802003420605070f0074018a001180120003442d565411402c0004032000b00383c5010000d618100401c000c41d1740c3c0010030b0002d40c840704140190f900001c07001160842e031039480b040c0c1d0056a0a00200e0341c2c1c0c6101f8020300344608000c4080040b41d0000040c001d03140001c4400c614445201c00c031010214203035801c9207610802e82e41c6004141c450044902a05422001d01a81d00381101c804100c00b030030101ca0001d400c07107a040d0700e050900e440d0402c0382701810b007503000b03416510401240b5070003100e00940040c85ca = true := by decide +kernel

theorem cover : BRFrame.Cov 978956834 979136690 := by
  have h0 := BRFrame.cov_init 978956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 978956834 ≤ n) (h2 : n < 979136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
