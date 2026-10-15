-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4193
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:50:44.624979+00:00
-- url     : https://prove2.me/submissions/806e05a7-fbb1-428e-a657-1b81300e1e4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 753956834 ≤ n < 754136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 753958084 1250 753956834 753956843
    0x80f040b06031509160b040b0906090109030b1f170307020d050705100f030c050408100c0306081023221b15080a0b030a0206130e0c070308010803070201050403 70
    0x1201d58070080460726154a14001c514105541c4081004c8440c0c08244261000c0552424020144e030761200c05000e40130343c0c042d0010340b50702006942021b2410303030000e281d941810305045070015626140c0010000088550046860b003c00700b5000d041c0d41070940c00080c01c411091304596074403100447d40d0b80d000c0c0e614001e00800341300864400740501001a840105402043c2c40f582e103001040080c100c1c0120004180400c1c10202d030848894003d5040d0b5060341c98020080000800f01c8403044080e2201c66105402d1640d100302c080784849041c00300c42c2541c54440c00c04103000d0101101440c1c51030581084030030f1001608144840400700441d04512000c0161111900f0030150034508564800c48016505442d903000000404408403950b042e54143c1d26243c1c410704c0c0c1c3c0c1d220341c1c0c0d10941d5203050383d95138182c0040e1941d10040c0703021000b40c0f6410016407890140a0340751520550038900c01c0d506082e00ba140850108100350344107428502611852025508090495001034201e0041b40401070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 753959334 1250 753958084 753958103
    0x9120201032a0f170609060d0f0827061219020d0915050f010833040f0209091f0b12120d0c050306090c1c1104060f080f04 54
    0x225600300c45854411410045070000080a00807001900c2070303164416010221389a24403442803040e078545180c1c0300c0c0074040c0c4005800d070b43d0042082541c000c010317412904003800041900c0031070b140c440605400010f86000e0010804038a14000289160740b07501841402e04100d020b04840711100241e4021a210710001902c0903e03041c4080640560115440310701c0c9010340c0181808648032aa004e0440881c0003001280c50b1180b40c01003111003400303030110030340c8000b803403928440b40e020b21882c1c3c9654040d10b21040401202900c201c0600543d000d43d200b0404409403c00e6180880d0a2a04142000e0080005003c402c11880d03c000302e4070310000c82c0741d035212090002900c42c03542c0700200301c81c2842a1050710b14401c0700035000d1f40001d05081c102a00d0b00050741d0300e040c042e2084a028140050054681341d592200ea01c00c0c5a0002d10a00111006049451003103c0c41d1f0182d40c60170740c0c014900da6159030509000419400d011007050301000304020a2095401280071050307000b41d046644407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 753960584 1250 753959334 753959351
    0x23108060c090409050f0118020127060f030b04180506070f090303030b0418140c030309152520010924180801140a1407110a0807051c0912020103 64
    0x160300303142040d03020603042d5023403c6064140041c0900c1400c0b940d03200b40c0b180ca110300340c00d41c61300c0e00700e2215207605510340140d0b0005012131401100d040ca2a00020715000c2002c1c00c01d00086003d0300c00741c90b502c060000720301c80c8000805c4401c1c09059400741103460a4085401e00c140d0050000741540b00180074160f81c0d4405404980362074103d510000300c0c00c20b41280c0b4140740e00e4458401403c5002c007a04134003440e1004000c5203808022214102001030603650500018400301c006980005d60055081040900d200040f001c0f8102d110300140c003681d1040e0004960041340c0e0882810544002d04104500801b0301ca4801c0d03018100c100156115848a501080e003134044e03603280d043d82d13008824100444000112114150061450070b81c80304100d00c015112006244280d424401c101110b1103810800511203901c00c140d2044c9903c8400101c504000840e1103098003a400050251101e03084031100c080e400d8041070003205544503501c1d04034003140c5016081a1040380d90f001c003c0c100750300c0e00c40300d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 753961834 1250 753960584 753960593
    0x3050c0f0a212310050c071709030a0b0a060807050108070f030f0204090608070b0301240512150301180c15020c040c0908072115023108060c090409 65
    0x40030105500c10342a183c400c0c4003200310708200e44403103041e0b0554400d40304500b80c001501e009030b0b8001d0b0441000c1c0307414022181d80b210380f0070f00c2c40c1500242410b0123200039402603908002049102d03000c1c0350600354900f8148056029035980d500070350415440f0010401a59902c80a03880c1d001d066844c2c050355802d04110100d010f041100d410031a9a030000c540802c40c000030358000412107030501c007180c221030303aa403000a506010900c075070343c00d0704100c80700b2101511030128443d1170001c40c0c0c41c1007403403d4aa05e0801d070320840300f0380304038049102c1809071403000d003402d1107401c90501003511800701300107031a60780e007071a444103004004640100c80b10302000d19008001454910070010000d00a900c100702e0f004020181074407a60400380300750f14000900350300b5101d10307400204486900606802158860100300118074a1f1150010341c2000000021140b02400004800311841003000c0c02e080c54040301c0700c04146800610013904040140700308421220b04440480030290f4001ca05c02413241071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 753963084 1250 753961834 753961889
    0x20303060d1505090303010504060816030201111603030305010e06120c060904060308041d06061306050f04030807060609050c12011401020f0304060e2b020d061e0603050c0f0a 77
    0xc550b0010b05010a10548801c040080c40c181e4405440400c040c83c0c0d1861a01c0d5102240c0c203581d1903640e8040c4081c0055481400542d425440003000c03100da01040f24000d0703032400545c0c1d209a000990700d0f00180051003200101c1900890304466581c00c038902009540d444410b5407429a1091a00194000b4139846942110004540003402c4684940c1d039210455088042030b96581119074546000450b680f0f041c106030303254051085000e003241c5003880025913007507021407000750214109100002c006003c00c0c00804d8050710807600400e0003841c1260b00c0050301c0004d003101e690030a083c031401860304180305069044442c9000c481d0035030152100180d003411940c01c284180b81c080001c02007603541d04842c1284059200b0350b20008910100c25481e6640548049040092460758500602618040d06002250341c01070800003190006001c440301130800601102482c00c0d256107040092100512407202c0507903081e541c0019100180300000c1489407a4040c1140343c104841501c81210004078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 753964334 1250 753963084 753963113
    0x301060819051c080f040c050d0f0c05180a05070210180c0501021915021603090312020c091501030b19030201090506070c030210030b060409140a060b0d0218180124020303060d 77
    0x9c0c51501000c450742080510540e4003442585c50400101d00010b144c1000c0300c0d481d800c450744070544855a04c0718400c0d0310181001901040c11486031000a141c2501d8030710600d808210150818140d404141c5000d020001580d17108605640101100109682101c540110920f620203428034500801007038801c0240121010907442424007a001010150000001c1c01501d0140d11442c410000d401c004a03500c0c0e40e002d40d080e802c8400000803402d034138440b000003071260005050224139140a030000c40c0d40340024400d41014488003020420a558000d600a4081c02d41070700c00c01e10f8002c883d1100714082c1d056100c028003d14000300201b01041c4240d01c010015140201456074030741d500c2c03211308040e00b101c03200c00c0000c0c000f110200704154118450001252103032940c2c03070b0a200103401070400075044070006113981d09101511024503501c500c0f0035a20841c070000300351629410b0030b0f001401102c45524260181070b01440400f50240c002096a5001c4d8003118840541c80f45407030510b68182d03026 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 753965584 1250 753964334 753964339
    0x1202060c01060603020c2a0d062a030b01090308190c0b040501090215090d03140903010f021201060c03022509020a030b100309020a140301060819051c080f040c05 71
    0x114010800c1a81a002041180310200482da0703000f4400a40c80020480140c04085414001d0b030301504a04100d41380c83c8d4905d014a100042d0743e0410403e000e80c590f18040d50081c000300e001001d40c41c064040c460b01e0b10009080c07918181d150308541e07420145100d0420001c02c4106003929295a036031082803110382c0982d01162407100c9043c00e1070458040c1554140403403040d42a04000541e4280460544a40c04401481d495100c030103600c003910f031011010354a010b080801c0200e070003662003d00405128a110420060340d072616541c0d1804c8a201c180c00081c03c10040003286d0303011950010340050240c6405544a8a034020080002c3c6800d5503944000100c90002c50007400068041c0d010040c3e500054440040c2d04405060071401c842c0503100c000c3d0302c800300d441c042c40b00340560038601085100c007900004170151594803a91801d03d180c951120485003940c089800c003c01407004480814a00d0341c11040c02420104c0a0032400c0020040300503904120700150502000b400010001c0c10003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 753966834 1250 753965584 753965591
    0x5090a0323190e10030902240d0e0f010509070b041701060f080109030e01090b07080304080903030c160b1c0b030c060315010917060103080c07030c1d0912041202060c01 74
    0x1c0b5002810319403500030410b106041168445200500038000d0070140c690082260b03407414901600646680b03c2d4a0000c1180b060a21029070385a03024030451103d0320b110801405c2c06002c01600a080d1a8010500c1800f40c0094404228541e400010340d015201e0b040d041a0b110a02c88c1c5845004100c207900001e81d10500c4680041c0b9108194003c115007802695080580e500c844015200c55841d4460342171201d408100071008190960051a040783c410740e006444d00c404540040d02e140c11070b074a042681e8000c1c00003560034030390407101c0c1002003510050384e504001c00c20211038461481104018a8030741c4851089440e550f00340301141844600a0a590722424025202c03103003c40c84000050110310020008150454000c2c060850300d0351104c01404580c1c25996045040e0f0090201402c1070720411001000082c170400c1c00c1000750840c10248540082600e03051565240003030130300342098003c0c0c100010252022000c0f94140c0301c0381400b88200790154404102c1c54072907102524025480e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 753968084 1250 753966834 753966877
    0xf0210050a0e0102070803180604050d111804020a061b051002090a1a0d11120a0b101106060f2d04060e1e0606040b1c05090a0323 57
    0x10450064001490182d4980030040494401a82ea4240a015655466005001e00101c1e1490880d0814000d600505507900b850350392000702c1d8500b1144a001c07503640c582a24407204a06101c02120350b440d02d8440c88500500300380d008510f002c1000c1c0580001c000002c01001080200e440c0c0019229511404840c80d59000b9800c038002508000240c41c030030340455000182c0502031070500a035020000c8010b514101007a0b40f03142c02000380c0300800d100151705004110101200110051113000e42000c00306009183c0c104100c103150550201c0c4007070020000c00c00624400002d40164081c0055a1074145550b42c01c0001d083d415400f40c00c00c902c8103028091019044144c031008203504020341d0103002d1103071202c00340c820185c000c03503c1c3c4030451027100301d440c1d042c140d1750307625908000090301051802d901d40c020480f65070300c0403140e80030b416114801d114407807129100703a40c0c0c0041031801802d00600c1d10340d4002c01d41c125018502c1c13503800400c02d40169210b000000c6818894150001181002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 753969334 1250 753968084 753968087
    0x309180903030e2113050d050f0c06030f13030201020f180a0801050415050622020703080f06030a02040e011d0604050105090106061209240b0307120b070c0f0210 71
    0x21014007180082d08003503408280c0180003d1008404d200920702244420103201010300a0300130841400c025004804005119140c11040908040c040d0021f40412550840102d2803d81c00e041d0340c5000750390400070800110003080c230305a0422018103108140d48240e0400721702a0042010a2104100025034820000c0480500203043d403010340340c408480b0782d5903800710308a46080390050507203441c0464144550405a10540e8000300080114140014184004500380105807072400b25030760006090301030541022169600c02c200c0002000d05141680101e500c2c0e440c0e11600034080c07601c880e4043c90340c170402e402807451200203900e140308012507801429600c060554080d9803551801020030304440040c01044182e6007291920f000310260410340070300a01008005035450543d150040d0b110ba02401a101d951060605021411000c0c4904060404c00c040e03210031310ba612000301c01c071300048203000300b01d5105903c1e082000c2810b0490a08184642145600a500400b80642c0d401d14a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 753970584 1250 753969334 753969341
    0xa050d0b061801120c0804030c0309030b0c12061f05090607060f1d01020412080a120f06061d090703150f06080f0a051312050417010b09070503040b13030918 69
    0x240c1c00344d03514004010024811011182e41c0904480010500c00014000c24060403880715154800e14189500640e40d840e15405d0541c1598a00031000e000509000350020074400c20b500980b00b12207404840303001c2c0b800c0a141d0080c10503a541030107808201ca120b182d49802c1038541c0990000350034010b0411740b441c0c41008240040003c0c010061022880108070b0052096400780c0701c40c208030b0821040c0740c1c0c403540542c1d000601c0000400c0000c088106190f21640208421065406404590b44d400c1150140400114001881e14200d000001000750f665050a040d009003090400081c4200c2102240c81341c02c20b41d4112002c400e440700400500250300102c42c3c1c0c80f8924000420f2881d0700e13032080c03460546205544110103010b418000d00c01140c0c03003c200f041888024100700d0b00e41951091704000f040d95003d40314a10343d640c3c1014003007030300303080e0714107031f400071941c5801441d524060380c5904030f10a014203030981c004803416154042500031100700c0090b112030004014042500d14028018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 753971834 1250 753970584 753970627
    0x60801090c030203160f0303030506040b100215160909090c050904030c06232e0e010e011a0f0f040b18030d02030415050309120301030506090c03060c0a050d0b06 71
    0x40d2044100c000155030111030080143d64130b91b020b03c1811440e5031001c401078080502030903481a0b40340341c2c03500ca56030303801d4401e4800320654029101403280000c0418540c0001441101c0f403c8000d181404015840b5454005070303800d03100700040003d0b090400000411b4582c2007070780c00c02c000358240b000707040c0c1021000359102e00c08d0800b40b01402107242d500840c0011f03441c1172000c0409500200301088442408400c02d80c004892140b41080000c03c07075021040542e001c049900100d000600c51322003001d6005001d0440384010014100030401d00e610703140306041c81c51481880c00f041110520f0b075250100d13001040503000c1c0f01d840e480c00b600b100310b800d061209800e10a04c5031401d80c0b0342641c00441a541140e07501c441d002008610b11009580e03075400201600390b903000740b090300ca218040c0030020398080e50040000f00070350702e00014568540004000028801d5001d070040144550001c1c04030390081441d443d0183d1140d4480070f440c40505111141d00b948000045001b8407003c92098040c01d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 753973084 1250 753971834 753971839
    0x102250306020310081c08070c1a0a0b01020f030702090103020d0f0b151e030613081e07022e120209031b0f04060e0c13031203020304140c0d15060801090c0302 70
    0x1021b0410884601d000384030507400040b80f580000201514007442403410340b103001d00c0d440a48410541102c264540f000c8455144040c3d8a01408003103580c10845009507005c010b0003985020107d40004011180c1440000e03c6040e42144150030010741041810304e09500c042003508606040083c40810410019294003420030034056140c10703685c03816000700000300036000d0100e40e103401003408000c0b24850001d03500d540b0100500384031841c0d00c00f44001d107d040d80400c035403218118410800c3c0c2ca00d4880395074001d454105503aa26144003100344280402990030140c1d02c1c0780504020358041e0045030916549405112109180449090301c000d07000c00b8100d50070311015418004010440d4145d0240c3d0200c1020741c00003590722100040103284107110030101074003c030b60320307902c90681c050740060400000c2d4020081c88200b01085c0030b071240c9084039801030305101c1e61180129555402c00c00c07020b4a07a008840842e111011140d1044006d8804640240501119030809245034241440103d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 753974334 1250 753973084 753973093
    0x1060609033e040b0a080a0c0e010b03010608060a090c080610050406020c040f09080403150f090807061d0d02070f060801050307090b06090409150b010e010225030602031008 76
    0x405101440001c08030300e80da124850702882d516600040c0e40c2c40210115810503070b24401e076801562904c1d0030400418410f0020710501e40d503032421842c80030540d446205000c080c40014009901204180d070b054030014a0320801c07540e030703140c00100b9252407071748220f41062900c0044113002e94001d048c180314020559600120741d000040c01c550a1140307108010050308a000750302c0700d61805030482c01140d5903c2c000440c11400360b403240302c1d46620941c012244580040c6484884d01d845004001030003d00f4441000381004a4490103018400d60300014580b55941d403125060006a90300944414100310841c0c40d030051444c0302039560040d40c00b0b041e85060341c0c0c2c4800141148240441d5050b50006005420700c2da14101002002d0401308016541c0140c01340104c00140e10340b48501d071a8540905820b01450428202c1e007405c990746107448604120b51040304036450b980016401c4001d02c120f141c0d0040c840c20925036015069240d41000b04070354000024003150380c40003c4500140c440060540307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 753975584 1250 753974334 753974363
    0x60911040c022b2102041d01031a040b01030f1a01090c020c040b011403311208040305091c050102030a050402090c13030809060c07170c181305030c0106060903 70
    0x240f0820300c0c0c003106800040c04501310781000c0c104481d40c00c81081c1104005410721740c0300c2c0007c150703aa01d0b000100000c42040c80041040c00040401c070522008240824000c500b0700c0d8880c06c0c480380050101030516000d88440b4020007204606112030405d104840001d50750312041c0c0d8101620141e04104010f11a100b0f40580c00d142500c1740040440e0161502140c565101170001e80b103800044c042c00107485d10402d500b80d0345042c68541c00604da000c00025800140c540741681101042d503110004010342c580c1084000ba4112080701c40c642c1c021602c000c2d0109003901142000c5d00c0b9182c005080c0d50010051115111140d0481c5020780c2c8215090f4425a0360b481900f2524003d901c0000da02c10319007a0200007143c003400041030580c1010340b07141d02d0150030345121450104c082e030102101c80000c8400c01450001805504041b94080b201c504052464520030b80380c10501400d540c11003e03400c0381c00010840f08100322138608103418001d200306a40d0300c002a059031140c2c48140c6440305014000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 753976834 1250 753975584 753975643
    0x10c0201021c030b0a0b0309190c0305070308030f0108030306210c0a03210c080306041812110c0f0a05120c0904120f0c0305031503031e1e16060911040c02 68
    0x740c07480384070b8040040151504509c2034041035025081d0a95049aa044c80803002c181b082c4620300c082c60080901070f9486c2054841d2201c281c1c8143d1100885402c10700900c0403d0f5955510110f00340f024120740c440c0340403a200d4060805091843c025400035032040000204003400c0d24900086032001500090701303244035001e68a030700901c0300042c80c00c42d0400008280789000d50000300e500b085480c201a030007511b03907152100751010042e0034001c2020103c00211180713042040e94801c10b41a21078408500000b004500808810f0044030301ca81c8941c52640904030040150f44007400c8028070b070402c1800e0900b840b001e0f06017500d100741c00141e20700690410f00307401341c20908202079060b500c0914666840d0031071130014554480065140c003040294004001d145148004401d82609000b580c0700c07950082441910300900140c0501d890920004001d0714200042100135074010340c02142e820074034940705481c0d03151450b58550041c6420f61038091365500041359040000f480c2140c60340320300080b00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 753978084 1250 753976834 753976837
    0xb0709150c120e0112050a18030e04150506040e0405030c070b04030b07030603080403060207030e130e0615013603030302070303051b0a1b0803091f09080306010c0201021c030b0a0b 79
    0x1045404a4000950a410a4001d41c0296840f24080301c5c0090703025114021104080c01d4188140c00040c001440c2cad0f015450207101c0e0088036000071041070721051803c000300e81e15000b58401e0301c041411902c0010306002d03041c81201d000c40c03220000d842c22140c0303c03d0601e1a6822500043e00c1c0c985a010000b004603000340315600c00c4d2500020807a040c1407650741d622000e036101c600110200722944422030140d4844a842d008c2820108401013240c02c00300d0022444d20000030500c040c41c40b1414043d0055076000640b003254002d031040240840074120000d0b008650143c4103c00300132000c03880001c00d0580c154041c10300c803032090b901030015407103081c003151402440e001c180300100800c000d1030032400c0c080c4500790b00304402800c60740010055a181c2c400140c100f1a00c828840d00b08100c140b50400380c54418a00400d28404100aa86401c5e207408c030341d42c000140914144041b0100d8130301560f00810000140c0d01500c0d21141c0b60181c03c030350003806840100c540f603000f801c3d00d800201d0444200d10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 753979334 1250 753978084 753978107
    0x91e0b04230a060911181f0312180b0304080310061e110c0901080f011b0203120709030233070203060f0402060712050a08070e030a0b0709150c12 64
    0x80c001c00d446001615035034010400404120b030204842d00b0111002c6d26149001c04e01004034070a04203141c0b40502015020f00c603c0e084450301c00110030014070000d07508400030590a0f03200e280c00004201d0300104030164405e60782004c10425408001c200c200501d5200462054401d900d0f1511929940c40c001d48000c1940702441e829660800840301482d0700c40c4525034224903400d81210b6424400d030010444603c02a000b11a854000300c2c1e040915503824058011801782034403281009602f048402510b901450a51048180d08080850081440b488403000a1a001132850402c00d41d44840945840360410043d0f1444103030b0000c003685030119200351014140c0140140916544140a08804841c014412a44501d00788030078401b081c80668080b015070442c0e12455692207403200003034070500009220000f0004059102902c1c0c0d02d003c02d1202804d503101440320096112440260750208050300281a5900b20006400d07040f41c0c000100920075006100601d5a05600350085502440e040e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 753980584 1250 753979334 753979403
    0xb090414090604050712111509040608211e07081b1606050a0906121d0f16030f0f021513140603010e0f18060115080f010e0703091e0b04 60
    0x240380c09090498041d400354280d204052714100c080c0f4001000c5640302c0d04181d1896202c26802c2240c200703001d840f400c100850003030b002d0600001d142c007458840702d404415400e60074041414803c110f40b100c2501c100703040002c13440360b13240384090148ce500d104443d002501c09800c51800250755009030100c550300d840964420010702e0420205694a8840103020010340b40d0f10741c0c0760401c04a002400e80003c48111025083d13002d001d102c541d1608a0b0035840100040601d8010400030b10200520680c3d0b540c0903020484c001d01c58000110700d003002c548010482e610000c1c5040e00b440c040a0690300b6140c241086940c21907052041c0041030000b401610302c983d12040101d0000300181480543c00140703204440c010002285801d410500c080c0c0c002d0180c11407696030300c80b0a80c0c01c00801d960005c10f028081100358904079190081d001c020f00800700741070759a14410107114412402c001000c5c900341c5401100c2480e0324203a400150112800d44130111680d4091800c880e124101c611603500c1c0d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 753981834 1250 753980584 753980603
    0x9031c021009020a0f030804061d0a03060c030b1302030a181a0c040b0706060e0a0e0d18050414010e09030301060905220e0109031103070c0b090414090604050712 71
    0x305056100802c0e1102d01070f070b884200030307200290300c54210b900000603500c910751280e1204c0ca03044016000c0d00084000303818500a42620605548924681000f145d42210010820a0340c2280a50051070a1218287c0185000c044440c3e0000700d900114024103030f1340d000300b0541130840c03541c640b6801d641c031004140c0075089803000102020303072003065085186c0001c1c0fa0b140a5980e4003492956000703038012a02161a841c0401c00c0c0d905060701c0d0707030b880952028148000500050103c0d00e588619000900344000007040c110000d0700c1d13905400251002400402541490584001460009204042d04400c2e02c9002031a4004040141c074100d9507681ca400c0d0341e16040000700480c04040c90100c110340340c451414095100380500828240000e800000180c0000301d0500070410904c45189140d5580108800d42c0020700f501c074144100d9100d921155110b284890008016050520400391517858000c2400850f460106425014620841c1203451503590750301004c00100c801b40c00905128013 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 753983084 1250 753981834 753981853
    0x6060a0608060409060209060c0a0c1d280606051309090507060e0105210411220b1201060303121b200a0b160221030610030b04050403030209031c02 65
    0x1450b8004c0c1808621418000d81024007280210340135402210411503030b540445000c2040c011b681c100c140150041405030035154a5005400c03c2d03c80300540700050a5441d00081654405103140781000000301080c18020280d03200d90040c2550403600406a00d001c4600b00042c0b021014030420540f0743d4058081d040c480d10306501a07404080c41d100d145c0c14050304203c50148030f0462540382a14016107001c1e050241014140524101400300b00c1354012080c055180c203080ea4120f00340b600c0700718401004100741407080045032440c25a000301c80328075070074502e012007015005075808068081c0000100902078408042c108155021500b5001103259060006001801850320340c0f014000801290450703460342e600d2101c2d50b00c0440f09600d5500f4504001c1164550600a016009040d412004001002e8551030f0f044c5210192185100e121151003591045020760007510004400800801072840e190901801031361041c1d407a02d10038022040f840380500500f2840702d03050161640280074101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 753984334 1250 753983084 753983089
    0x110405010f11100516080a110d0c050708030c1c060605071112070b04081009021c0201110f0616031808031302030316020a062a060b120a0506060a060806 67
    0xe020b50b810003540c0070b90442d101d260a40c50140314080c0b0000b86441d11890100c81c0700401110300a001341c40128180307840c500c0100039001c21740c0d04482c0c40d2000041d0204051000356041e10989078000c0241c5004810851440d604a000d0200c0e0803400710756034074082c1100d0b0304504903074150140001007401448144003290500780e00303030501480680303849120126030309801d02c1c007070301a0f201421520b4009014021480d0a016611009840c3d5a05000c0c80c40d10744d0000380300c889021090443d01c03401c280c42d441560f204000000b20002a142510703955101d0b0030000b5103440e000c0718001e103440603c242c02e80e030301d5119205100622220b0107050b00c11020f569545c40c1c40741d20282008540c207070b40801440c0076990038402841c0c29010350881c460780407031602c10b01c10361031007550100041c00182121203480c0501d400d0320000b10008540400b03040d011300e00e403003001000d9100300039070054024020812035110000341c500a00340240c0c2180c1c03d944d900f202700402040f103030080d2030000d20400085112030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 753985584 1250 753984334 753984347
    0xe180115030b040f06090c050403020a03020f040209090403080106200613020316060507170909010b0a12140f1b07030e1804032d0e1c02060408030d110405010f 70
    0x8542910340481c080b0640c400240540b4007454070050380756550328007000800c074148903941d0b0003403050610a040a142d40c000850303010281c40040d0151048484608465403258116034200c2d200070701c004a0382c00c03d410010040c0200340511008280000f10f482e210070000708036441c8065002d0010400e0707039103120a228621a810a080fa0540b00d104200d45009520042c0e200280c041a07903120f4072140c150a204810000f410081e5075290020040803500d902c4002e00c2d1810b483da80058a540c0b00510b4008888120005d0f421490f014a4020121a0001400303411802840301d4803d05581d0b886900000750144190481d40840c4035003000282c000074059144520350450051091440c40817441d50850007110455013180025801042030004001240341499012085030300c4003004001080050000e44050b0b060302d00c512040e418448986442c02d0200301c96503800340001391a03540d102c00ea15580e4005102c00d80c00350741003240f5054039140744030584045070030580d504646440704e20801e440700b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 753986834 1250 753985584 753985619
    0x3010801180b061045080a2a0909020f0405010503060105010c06200a0f02070305030301030b0901022703070608090715200a021314040809010c1a06010e1801 69
    0x5100070b0126a001c145da0b189180308404054000d040718201c0181000d0309845a1203210200d0700380b16240c00c1c4014880001c00c400d00701d0340000403040307800d02d001c164610b035600d0745007005012118440c04180d1491035040980080e100355804600004a0001c01080d11b60034080e003505980001c00400c40740d0310030010316600b94000c000004042907030400c8055111007100140341c0b13240001622240796644000d000d04000d400d0310141082c0d50540c0d4a05803207110621003d448101c640000c994110020340c11907030042c5441550b280300b0b0721075000c1e0500413601c01c041144240940b070000644240101422481445030001820ba418140795103800c44201095034541044030b020541003c0c8801c54981641d0003814600810044041307104000208800c032092880043c00c01c0250f00c4403074041e00c000358003e54420f004603124a8a08012500301c01801e8001e006800e01c0c40041e200c45000520840c0192070aa030744000b40f51440c0306102c01e0050105680c2d90080c0514010050701b1500b9850503003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 753988084 1250 753986834 753986837
    0xa050417030a110d0e0d050c060622090501060e010519030204051806041a0a0b210c03030a051b0f0a080a030b1002060a0614060904052a03010801180b0610 68
    0xc00511100100b030f0303d50032030001ca415031581e40e9503600344070ba01040f5a2402034901d00d811445d00e149010500d40f1418042c014070b010300f8580031004440402d101c07011504410300c1a040001c2035240c14202c0c06814079200302c032102c070660000030134941001907500070030001e241841c5007420310356801d100c02044000c0081407180c01140d00e00315515000d1000038000c038050341c0c40140410f900650801540006041c51041619181c5103c01d40e441e1410898a05400c01501600720440d400c121400c02c04400a4698140000511070300f402c3e030800301505845032404200360348045403031092a551100c01d011045c855001e030103040c0003e903d1000400111150340350224608541101060603001c801004201680040b000c0003804903061003194014a280000d61100341c0b050008200030303102c1c000038503010700d80f190b0001d0100e007001400a03004200381045103040050344600214a500280107400d41d55003001d141e00c46404040600c5500e040d04000d0015480d100c1c0c104005a90041907450320 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 753989334 1250 753988084 753988091
    0x106050a02120702181006080a0b011b0311010f0905071a0f0c010b0303030406020a021c09090228090f0b0301051509040b040912020f0703050d08090a0c06170a050417030a 75
    0x250f0440c903044083c6d01409010300c444102074248a000b420120001b0981c5110501e881400d11142e030b800480100c02101d131440004c09119035043c200d03090340441002c00b0440d070030709042c4209241290f1054050758060803d586805403911820341101101c00203500c1a40418030031040031500354001089107203800c10000905c2c0c00c4080100b410b68004550a940b201d9010070303403000e4583c05002404100b0300c17500004c0b15200d07924201502c0c6800c0c3d03010b040e44c0c030f69011030707040408400c07025808101079034680c020003408450b01c0b000700360096900600c00c2c034003030071400041e0740c814040039a41618401454055245407000540b001500300030717141741d400354903140d4a8826031114810880014000c41a03a1600502c1c500041d14000300e0100c5002c03180d009100c10008a00c000c22050880c011b9487d001001e03454621401e03285c404d2120010f440f0075446100000e0700d079001910700380b1500c00c04a81d0801c660322651400220b82003142d01911010045c0c684d00001d20314003009581c440c91001000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 753990584 1250 753989334 753989359
    0x50705010c0806040b030a12080c07020a17010e0d02100207030309080d06031b06020a11040e160303020d050a020a020d022710080f0a0b0402010e270106050a02120702 73
    0x2642901c0700e800490010400100030f11039182000d005010005406800a1840040554415420000d00f41e1644200003941000c290344050140841d00555002006a00d03103c1d01c03024580640c203101c28038000305600c1d012104500030400718080b440300c0e031075401400b5041ca0701c0700342d6006548941422001c0640d01c2600c0c200140840000c6c0c000344036804400a021402c0d071402010a956064158046000040c81004165030003e00c0251a50340455418007100c801c074003103800342c01d80007010f0a0034041c2c040d804914400c13601e2a4006c0700d000740e08a070054412400160f0f8188200400f10300103030072510210015041107013103512424405000d10301d503000b0007003200810302200c100610034091680203000503c0408a402009441342001500d100940768040c29600c450b402030061842d6039080000301503a02891600c030002a01a1492010900c0d050500003002c40b080760411880c45580000310311070348550262000040150000d0550b141c070a00105540d0308a00c00480e808030041445 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 753991834 1250 753990584 753990593
    0x70b0c03040f091d06090c04090f02120a0309051903060c17070c03091e0e0901020706050a09061a03060c0c1614010909020f07110f040e060603070603060810020a0507 73
    0x180d0010f00c040ea00c00504402d81c003165110381120603030050040e07408841442403142c1d0102d19076100402c11100000c000d00305180041c540500010080e51204084242c211070380e0300444c02a240d41c0c0302c0e40d01c20ba0303040c1d140c104002681c106442906e1000c04150ad0510020303600e980f00d80d0940280b81844400000c405039140004c075001c503042e0b00019942c2100c0b81c109078020f80a68050800f06a000f40c1c000400294a45884143d100c1c420320704042c81c001c04c076401800c1d8120b804094000380b05204514102d10700303001401114104a13210b91500c0b403481444050010b000300c1144004000d4a0291925460300340301d50014044c0500303130b001d0b48114880c44c81359250743c04014283c10100c800100c1003407001606030040b5610455895004001d100d4010035040101e464550388164040501000f2034081100c01c600d4101311a0000d00d8601004024000010900d214030b008030119018680c03911002c405940091191000c658801c075000b914000700c5401901c403400c45031806609146480d00e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 753993084 1250 753991834 753991859
    0x30a0b0d05010c110106081c030c3e0303091b010e180a051008030901140f0d09060e0d080f040305190806010810030f02010818010c030b0f0d05070b0c0304 68
    0x43c0d100865000c403041d0b020000207018610060503e40c014008503c44c0d03200300c078001c032015841c1c102090f03a60003000480a00038155a44c0c001007030701e902d611140382e811007004085000b8081300590060400c5d089030300c150000072a403003040124050407900c603c1d11030f000b0710210403040d1f003814460b12154034032080d2079194400b40421214180c40d0741d1130030001c1e0501c048900190100410303003049a414401c4400c000205c5d1174500c4280303000c1c9030b40c0b9007003c0c0e00710050140151940f04844002303500300250440f9040001040e0041c0c03406c210f80034904030400d59541d8179075045808281c1d00070002e004120181e241a512034002e0814900e050155110f41800007a15403011307003c00c44a0040c460156440101190301201c0c4900410302c82d4211740312140000b01d4014024108254400018501904070034a1540031900b04000d03c00513815580c068040c0c038112180e40c0c040c0c418035a071110186001804031103601e03003110240034514148041030310741d50301107070071054588001c10001400c0d008044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 753994334 1250 753993084 753993101
    0xc0e01082701051806010305062a04030305130602010b010e0409060615090815040f06050601180f0303080a05011412030c1c1b0c05040e0f03120f1308030a0b0d0501 72
    0x4000140f1850082d09100340c2140603000c4c07400a41c0401e0042c00080e200003051500842008041480c1400ba40c4210a403065004000310074003101040010405401c03401074040800054101c12045440e880c049007241e510840e800c1c00601540c1c24902541440e41c0580c802c80d000d00e4001c03d03907035190b2808096a03401100c00a000403140842004210000d0009581c1c420b2031949140560030b1035200d10b4080f0340301c110007030516503452010442f00e07070190f01180991b028010401c02560f130b84040d2406a910944819404141c0c1ea00c0041d81c0c1c0f581a08c80c0c0c07416a0348119140b80c0608001041c4915080542d082c3c050750304c810000382c1e4040c0b10411811050b11203200599194810340c0350000c0010444101302c006588841102900280c0c48086400c1607400941c3d000940c602c10724251464041680303003812003030000281c0c20204a4604071920310070300e50f0500303155103511201822510403107007040261079002c090000c2204412a42c20980000340020001c0b006a071303040d2500c078219200301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 753995584 1250 753994334 753994411
    0x203011b0504050a17100522031214010812070c0905010915060c11010e030a0f0b090c18010311040605120c040c030207020a0b09030f070e09100c0e0108 67
    0x100b0100403510744041c2d07020140440040034212003000070b001682e02c0c00c00001c101c01c80b40c0c03500b001034500c0441d21004100c0c03507007a5109900c3c4da48681005003440d8800b80441c1d100c2420080b081411807110541c40e412200c0308002091515100038a15200e0f400c021004c03500303c051003e001590304024000c1e00d000c0d1241c102c00081411465480010614696000200b4003001c0301031341003c50403401d41b43c8d540324002e0a040c81c01d10704010010342054000d440040c411840540302e10180b00c03030020500c3c4a2140601116113140c4075804024030340c20041d001141c4020340000620028000071042080b100020b00701041ba030742c450000520142010484100f01c0d03101004100719840d181c02013841c0c3d20307418102145025040e030081500883c86020f0100d04500004501000303807400c0000f5040d42400000f6243d00d02d4507420000300c410400d0354084c4403442034510194000040d1b01c602d4550288503116040a100348400543d00150001c01450702e11510035598501b442c68903c00d4404032401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 753996834 1250 753995584 753995587
    0x20f030a02010f0612150903140c0736150b190e060f0d09050f0a1a0c0f0412061103070e1809150411041d0f1203130203011b05 56
    0x115243c03802110304907440442030100c880d0300301c0f020070030400800c0e2003c04041070200b0329043e1800c00b5280407000e54414448903000240e103854880b00447c8680644000f04035642c0d842c000d0f00600c55030514046419141804084141801400103903c150100703002050f401003500c2c0e480502110541011404214444a040605000c15807002c0c004042c140e0490f03a0500f40607000c1681c01503801102c0354043d025076a058040d00307018080204051200b12402210041809440d04814104050f0712131002603100304085000c034602c0342c042d14880e03c1c0c82c5050b80d007814505410402c1c6c0485001b0240d9440c2c5e6541c0c683d1804a5465000314800c40e06500c82410800004050281440b8041c00d14001c100e07188092055411012440540b01607e12440c807000380c446060007903004400081290344549442d0036007000104a10164200c880300340c041d1007a48101511154803035000c0b1910242813081000000c10941000140e140c10398000b400000e100422502040821120240a440403600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 753998084 1250 753996834 753996851
    0x1080703200d0f150b1e030a020c0601060c0305070b0c1207020304170106030b01091104080706080609070813080a0201060306050c0301051203072d0b0a0504030306051507060c020f030a0201 83
    0x240d400380300d040424a042c01c00004c0022035410920319405c1c001e44800303c00002d83e4031301840b01c2c0300070074030f01c51114031101e9900c1c01d081c0906c0d8001e601c400c440c201c0900501e400061180c0c05541c1580c1d0b0190980c075890b203851820354a4028100e0010304840b40000c062100740f603802902510b092281e80660005d40c2d58600b003000700c89500342480819000b603030501c1003d0000860b506201411201c3d101d00120f400c04003141d40f482580582d0f00004510300c40c484e000200c855102002e80d010303a60581d54654140c13030721a42201c021000700d613088000600300101200090f02440201710310125440002002ca880e540d03040300307403041a01d100d100c442c1c002c001400313503141c00ca481c07101c01031042c2c005600d000e0784c030768070700e0002c80c1100c02000c0345042400d03240151440c240082c10700d85500200710307007281c909000780000070f2005581c2603001a203443c0c80802c50b410f1003215a20b80c040050000f50501e0019030390117000d090401911001c50140d070100141c1c40108202a250170a11078002081c08113 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 753999334 1250 753998084 753998107
    0x32d05030d0911030c1509011413091d030a08070203220509060301060f0b07050102070b0705030a0617070e0c07050105100314120403080a0201141806010b180108070320 74
    0x11183c040f00c0388070fa0420121aa641d964040030426044062a01203454040c040016139650b0380519003883c10302d1000407100c5106000385146015141c0b141000c20490b0b21500e80c1800030302008c806c40c81540c0c000c0040e4040103000f07200d4a90b11603103038811282384c421b00107140d099540c58800750fa0031103100942c0c1417043e80390803040c45501000580c000c001d03861800344040d041101c0e0b4801c0b06580080040c100081c0403007074045640b9503400c5a411400c03170030102c0e001090380e07200701c2c0c103024094545900861907840303074032045d0059403115004042c13903802c1c0740107645005005049142039060030442c0300300042c403e002d0148144540782c16201000e05e9400d040344043c2103006100001d400c215000200c03020590300380e8041d00e0f042810740c1d4a0307003104501030380105907210381c01c804440c66074200042d107c2c0142142c104405003d0603224140d980e590300c0c0546000e504000c9c1481c1c1724508604403294480c1c9502540010030f03250100c2d158850414042c01c0304101008201c454500248400e2901c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 754000584 1250 753999334 753999353
    0x219091b030e03090f12151905130206090f12060a0b030f24090a0c0906081005040f0b060a0906090923070504050c0f0301090f15032d05030d09 63
    0x165284042c510b402d080e02c00168540504003031700d601c6058001520020004100010403004010f408890801d0038a254035080038a1555220329940d800d0000107507403200c4800c0300120a6038042d0400e4103009030b050401c603140760040107003a0001c0101d02c0c00101480200702d06401080d0010300000c42c560500c05050822080303040d100e401c1d502c410b450060400742c4440040d28407540303c59150942e101c2e4506e103414181110790203070400f6000c500100d0100010b0f8080d500b16240d0104454a003082042c00c10b01ba280102c2d0007612800003000407201089851a0f86503000720b00030820040d15403941010b40c21907042e80c0011803c0b42d03844040c0000c10410f00001065a6080d003003017030520f41040d0000e83d4407401d074018180901d44a4020400c00345140e02520580c1d039611010f1600e03583c4039031031070008011940c0d8401c201424010100c450980d5549103000ba6500b02000440d040740c000031202e80040ba40c4a55a1003c1c02d403440d00000c110148043c041080d003508000c65107040d681003d8021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 754001834 1250 754000584 754000601
    0x13050a0e150610110601030204050c160b1f0806060f0d0c0602010c1209020306130204270501200d02070503070605130614090d2a0b041208070c0219091b03 68
    0x284044d4901e0301c1c00e8104002130550445e139048801194990780c0c600802d00c0350003200e4004030f440c11880030b41010000c52103031142c810740014113030a070342444100d03648414070150700c281021034001c40003003145410505d51a54941d04080e0684490001c25543c101c92051107500000040c4d42d41d204843c0c84031f43c00744020313405203c00c05040c00700c201701e40c00081d200c07480178040390828003990402740308540b01c581050100da10495120852064200d84034103a0004903107049500c0d5203010f40b03e5030724225440700c0c014081c0628000c203081030700c51540c41d0025401400141d455210621016002402a004041c42450f0251030142c0305038103441c0a81c1030301c0400c1a1690394400103800c03c22013200000f1448080d0a9a103403848034200500c8071251501c1241d403002812500101403402404482007002c0d000310300c54040c004132030a4400b0100e81d5118299007403c0042c614195141c050f103001c000c01400168800c1d15030520981e0781d80c0c4001215840c0310300400c1455000c0a500045815202d503148 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 754003084 1250 754001834 754001837
    0x3040906050d0b060d03120f0b03060c190f090305031308010f05010b0f090d021806010f09120609050118060c02010e15010312021e03032413050a0e150610 68
    0x1d0007010356a59400315400908580c01404244040b0b4145881801d29144052007d04100007010f106a16a0064049019007178000e206542c0483c025508050840d00c0301c15000000031102c00d00944100c901c040084210f0081052214012010500a1000344069050b082c0400e124a140514481c25500c040003241c0009152000402c558613482c002c803920001d0000c3c1c015a41d0204100058814000e02e4019421603800c0d00082d10300b240400206000e804241c0f070b43c40b8030704a40d24084550311581e0140714040c00d041911180084c0c140d0300140310303048c840c0300041003d0441191803c45806440310a842c041e803100b0840c40f2054082c4642c036280d0600d4006820941d17510b83c1500103031801880000c080801420030848014400e0211841c1c05210b80c0c200041c001110302c20a84d40c1d0810748044106a17225500c100085200503082c00c0000405488003400080c2403440f1001000003c0090b5421500c070030500160700828001c80401301135050b1207248600b07101050062000c2c44904880 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 754004334 1250 754003084 754003099
    0x30b0126070f3207061e050112261605150a060b030613140a02090a0e07120f0e070303020601030b01050103020a050f070f170a08061504030b100b0c0304090605 70
    0x203034110580124004810001c8480c1032000030740201000c0f080c42106000b03890180341007000b0b50100450304a0000c0c04071000f0050202e42d0304ca80300e62040303c02c1201c0082604900f2031030603142409000b13410b10451058010b060803c240120300662624801d02c0032200b941041c0b122512450f035020b00c240d00441f217a4400c0107245d0605c002d90f48075110241ca0b5034410710558580c80e85416181d007000030003058020112600c2c0c14500203040194000000180c0b140340b1010b00030402c1c51845c26020301c1001a070303844851860f4203100b80001003501140202e0860380300c1d92a0052080108498001075219074001c040300e41c918280300b0005201038210b94100340c0100000f9503035990110903205201c2000300080e640e50082c1c641100c0003c0c0d981c80051038200c03141400e4000c1c140071406095914401c0d01c1340d1509030758070f100308450300081f200480850301040c0800e0000c50b11200c005a40310b010050b002c55000d031290010325a64000308003000441d0310010f401d00400703285000710f000505007a038511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 754005584 1250 754004334 754004357
    0x81f08070b07050102040807080f0c0d02011205250f091205070308031f0306020c190b1b0f030f01150509010504060f03150303021c09050d0201030b0126070f 69
    0x45445a00d039200300059820003081000520000f0341c112001007080a00b218907469842c80ca046d110600e4107401017050180c1442e2000c82e09240020310f00d5194144d41c0c14400c100c002010000512015180d440c8104460701c0300c4407040c0c01a41210503411081d00d80507554800365000811000c020340141001d22442420354001480003e615001c3c0d070382c007200554481d92860034035030601d0050b100d10200105101800400d10001d54010000d004a142c241c92071103649200104d05c03041d00c8800144800710680000703098500200300d0200d80f000947c5d64504d8480c58003542d00030b030f41040d11100d03c0f01020384c00400c82002d1701039042c40002c4481c2482c1e03040c1622800082c2c0503004611840c0c00788a4900310b42c804040c426071101258489001d641c94a40c1d40700e04000f03507518242032282d4000c00010b10241f41040c05480082c1c2100c5000f00318800b03042c095801100500310010b181410b0000d40301c031b80c0f2341c0940b4101480b140c02c00106d03406c0301c0b18036117440c004001800c848a60320a01071001400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 754006834 1250 754005584 754005599
    0x1140a0f060804140601030804030605070e0a032006030f09011b0804060510051c0b090708030910051303050604020102120f1222110301050703060612050c0d050403081f 74
    0x254811101c140c10005003d03501c6040030003020004510700e02050054800120070001042c010f0016603000c0c0d1010401a6034800f01a01c0710050b401c0c5003036008448510400001c1c18061089102d416103010f40d0750f000c6032040c04070351540c100f1f403012041c0002c900304100c8100030910801c00f1018030b00003074085060660102401641002d88058001a240c03000561a902c40000d80001040042d00400180500d18507071405a1401101200c03100701000209012100018842d400c0c0c90145018501e042c101c8000c00c0084656a003604091050601950f4400400c0a1013080290b01403405080d40d03141c0b503c002420440d6005103030200300424032400921815000a640000030300040c0110252078451001100f100282240c5025020614200c0300704041c00f00c010a000c0001c1d0000c0c001901c910606405546980c01200c0001e00141c01904e4480c0d680d4001540003268610064a003170003c540f01000e488044906402048035130080c40b40560074840f140b000b030703250740c8108095036050001c1e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 754008084 1250 754006834 754006859
    0x1502100f0b010f0e0f121b10021002070c08070b0d0e0105040816140d05070212070b120c04082a09160323010611102a0507020a0e01140a 60
    0x100d0104011012082904c07a40310740c3c00e10402800c0c000e040c45402c509034000e0550340d42d140000b00c40d49110081c0844d02604202c0a80101030449801030f00c2810040340c0018025003110600343d40301200142c000130280d20622520303024000d03441e88180e131010001c6d00002581c030818011010742c2e00d041c0810010441c0d0303e0035a006034011420b94040c0c1d1246c1c1c00c094185a1a00724404110b015100d214100150042d008142c01d070b01c20385641f03040c00846d141300c3d901e03000d442c840d4a905c2c4000b0003202903d0759081600c994010300b0004001d00781512181401e207083c0d200d00d922941a001e071403842d000c0e8021700711409054202120741c4002854180310700303182210500181d000f070540b03440c00c20911074910903010b0980043c080341c80e42a580c0d5400000c20582a030b144d01a00c0d401202002d07103000c0c0c150300443c8010202042c81e01d040b14003020544480b04070340842c0c0c03404c0120500c44000181d468011503001401039502009055040c1102c0904580d0a0704410344a0485180100400c102140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 754009334 1250 754008084 754008107
    0x2203030215010b120a180b0a051801090203120901090b040e1014010c11010306050613050108090307081813050f0f07030b0102070510051b101b081803041502100f0b01 73
    0x20004582c0c403903800c1c40b251482c04a10001405100c070002048000388c040e6201d68442c00d8180305100f000745c04810385a00b00c031501c41021307425400000050b002d142d0700b40000c1403010f0042c54100401030791091807400681264004020508404062125000030902294054801d58240c445040040000a4680c1100f5040100700700000303c0391213203d031301070341c0300c1c10040c20050040c50781c6e65501c040030090407403240211400328182c0030100700c51074800815505000d510286032132038500c0780c08100c01442d01c0d144201e54812411051440d5200e41400350500412603840c0d0b41e412400e01402a80d4a4500200800c0805181090240c080d03a40040c3c03d0084840c1030310b0104100341c5503202101c0c40e120300e004205003504003d4005080b0880080e10f90003140000c2e00400034281103d03a0340030340521034888000066107100125903050340c4901040904249041182d140c50341e03649440b0040e0303030300c01880720250300102e03c2c02007095280c0c01050804551144100010000c11001801d10013911 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 754010584 1250 754009334 754009351
    0xc01030b0d12030612030c05120702010512040602040b0a0302120603030310031511040305030a1205130206031302030d02010b19060906110a05060f0a0e070b0306062203030215010b12 80
    0x280300203803070074040e6100c2405015543c03c17a00502019050151044603040e004a4980c0b041001100351040000c1c250b50a09a05a40f000e10303006601d1080c0e829000050401d54000d0f9003040f00003200d48011000b0940210399817005610380000c0c0440c20b01104000741014040e400400412003020115081407090b29801a10303880300000112000300105510344198100b2080020f0102c140302c40040508000b5800d655900c201180c5a1f0424043e80c0d8141d070070150a0055014100042c034006000d9071b404076214a10400c5e1b410305400103407030000000000d01c00760755244445d00781400c003504a40c481400a03c003d48010b49442070003000d40c3c94500c01c14040210808101c6409401840314003503143e0031608480312402c0902c0e15110130201601c4c11ba00d100d181450011080c0004101c1000300c1389a078601d2400c699a01040c410141d00035402104d0100c280c3c840464050344141c0048090b50103640208020780380d10360000540a41a041a04015000d01c1407010081d1000307640382c0c1c001c1c0c07130 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 754011834 1250 754010584 754010603
    0x51c02090720190507080307050a1202010b0a150e0409121803050f0d030c0c051513020414150901080a1b38041a071a0a0e0c01030b0d 59
    0xe40410300040400746886003d91440070755101084070b82003003141e00a40980320010740e2034150381c3d0340344a91107009010303070410351900e0007294005046a82001d034030b000100f200c07070392000018000c050f503811503a10310280c1c8000000d440e51120b80254145401d0780d042040c0781803030304e584105e02541c0f602d003010008086a4000d41086080b0510001d41d449022135910401e8035005039100d601c45003840b0002843c108600c19161b10400460942c2e54101c0c0152103c0801c0b040f034182c000e0f0000f050b01c01207021801214005856900c0390452240114055070064184a034010b0004102805010f20a003003040040c40740c8440418480112039105c078020702c00f150400d6880c0038001c1c940c1d2120928a0342000c90717804006405e00301402d0800c0500760744a41038400c64041215006034019600b140c0c0b1300021080713042e14030000610300300b030003600091140d0110140041610714201c0741e181081e0b44030340c40040b4661042001c081100e80908050184102c44000b00e0300c0c60f501100c0240c01c0495 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 754013084 1250 754011834 754011857
    0x1021303060b2409041b081807120305070b0105010c050601090c0311030403030b150315010e0d08130e0c07110d060603020a0b13080d0c15060e01030c051c020907 71
    0x21054814854119511410308030680f810005412a822007840c00b80500d0030054002e80d5103200100e0038443d1810b81d01d9039069074450b2030850101405c1c68400300518071601c040400e441d504000b40650552080d558135503200700394a0705d0010090183c2c020f0341800101d02e82c50000a00c007003070180c10340307038a800005a000010401280500079024010000794000800d020038194550031950401c4c4d025161408100751a0600e840b07030f031000f22031100c000c1c50541d4140585600c43c4c1940e108804008210001c08420364442d001203078801c42e1a41c0b461140c00f201040026584503500c1ea0143d40d0f080c00c2410b003141364031303030101120b100711070184918056520f40342005a254052805141c024141d0f403945525000f030410540e01890050a1049522000081600c0009181281c03000301ea5190910444285d076800c0c1c12500c0020f500aa1780e07110000482d05048502d80103000314010030040e41e040345480180b207508401250f800b07010321201c00010b000b6031143d40d43c440d005412032901155404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 754014334 1250 754013084 754013089
    0x61404060815040503161514090714030f0102040e09070602010b06040905040201030e162d14060f0f03060111150f06030109050709021201080607120c11010c0f020f01021303060b 78
    0xb01d82080c001d440e1114030486e00c1849514492401041041c00d020008a6890400c080001d2801c665078009a03004880501108008061811100d03102408a07462104c1c03038848103083e42c10a800c01b01210113807a04019500508119210061011340001c02140e00b595010940c0c0340310300d010300458507440c0c1c80030a0445e440b0b0380c4810b0840390600251680365007a16003d1a01940c548103242c500f040c5d03143d81880c0090b03080c084444440e505000c070174000b0720b80407101a445c9104844a64080f0083c0010510070107910024100c83c92024030380c0c4c0da81c0c03a2540026001206070301c01154207600000c803290b15001c0148140b0b810287d201025445581d6550010340901844000105140942c0b440040e00d0362582e000780803034050800050780d80340e8032003031a0340c0d58135022903030f83d000241101c0c0c0d41486140c40f580500e1001d03000c4d01d030220075010341e05107450270b58a800c256500064800020442d00c85c0e4140700800818040d80001d501d17007203204500008401c541d000140849990312500a041e9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 754015584 1250 754014334 754014337
    0x1803020307121407060603020a060e0306061201090818010825030b0301020409020d021b010b030d0509011e05070c061e1b02030a14011527140a061404060815040503 72
    0x1c00c44154030741c1d6250400c1c17400c400170b4411031008134040c1c44100e80c04952140551070784907266030054018600f170750326542002100e80c8440e18415855585038001c20114085900500d910300790301c04c9000004102500040c00e210000340a940c0024040d4100c411203164595803100c121801d01c0c0c0403c4c0c25103581c00080c0284219449140d0440c800510364032003119540262000c0c4d00000007403100c0413aa80c0314503003a80c1d0080344660385030700100d84461810340100050540080180741c00e4410425420a07140c2482c90202010041440842e10408010f8403441c954058422454010010101845507071214040740350391000b0b02007200f180396900307503858004822183e002400c80c3e02e0800c5500b4600d1200410b00070b44041c95080542410030102c00395401d80450300350340c0c00c6509044448504189402202c855800a10340758100301d40001854800a80500c0d61000005080c512b06080260f11140540907140100d091400070449804040384001c41807200078600001d55689107000c0b41135 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 754016834 1250 754015584 754015607
    0x80f0403291b181306060e09060f0a3602121e070f140d050709080f031209010209100e18060d0f0507080102030406060f080316020f0a09050a090204180302030712 71
    0x1368900711000a070035900281d51140d100d030554224680c1d44641080c01210804c0410054010406100400c02d10b0180b000313802144041e041480c140103000170043c054007003a504c0030101c258000c100620504a1119229080b0b202c0440320301444103200d207107812800008151800f4400300308a14901d9501404450348500a09201c2a5840d00030010001c0140820b9600034002101050082440c000004516509101d039000031420050031266000e02240e000f005411207540920003620745403120f10150b6420347d010b840c2c0103040109034061000c40c0c0301000328200d001201304240001e44c0c035085000494550010380c00d110610300307400c00d503261291540c09490a503200000b08010302420b5404501612541d812000075981d55004480e40c81c040d03199084c00714941c0300401c03001803038020701340703c174014000c1d124140840e0740b410148225003086030310b00b091644840c02c071411440c040c400e010428260b010320301c014039400c1e20001e5507030190540041c0035000c0c031010b0710507150007400d04004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 754018084 1250 754016834 754016869
    0x30210050c030d0603050d0f0518010311070b0402011d0a09020a0c05070303110628090309051003050603070b03010305100b0f0901030f0c0819080f0403291b18 70
    0xd079a00c0d043c2d00a00181024842a03a00e4019404170800161080b00180c6107101503507105810820030314110510000c01e0360305c032410304d0364400c500001100d8807005040c0003400f41151155516050002514407211000341c9602e0110f000c1c42042156950308958007078410341403005841c0c041070381d000d0b5840d50702d200009d4034078401c1c250700104041d4004200046c6c0c03526007040d203201d502d4000d00420394510700303411003001320155040b000d1547c038651722408000d030082c0b8002503030980d6030380440c00360341007a0304140001e501e40b0200400303400c0400110006190040c5424615855034540c540c54284120307200c00700c10784030544145150346603a8038640c2e800f0020024007117965207203450121410250700880d0b00d800d921000007928a400704400f004034040f046070703141f0605140d4411040798448040c285821506020200206624265130f42519402140d10021070400c01c07103c00c510340000b89510400d640280f20141007110b24815942c0300300004800c602180e009500082880c80c0c810040c08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 754019334 1250 754018084 754018087
    0xb0c0a200d121803110f0d0605100501021605061c020d14090f06070807050d140408130b041412010b03100c170603070e07050f161713030210050c03 65
    0x2840703a40e10084840525903103510403c410f1124200e12110003900c0702a0444210000da4980d81c10554242c0209540090007041c860001e550340c0021214242c030184941d04044005205658040001541200341e90960301c410034030700b0340002d2240c420501140e000121404c6100c00b0001daa4040c6c0b03d0b030004269050140e1100c0000154082d007080383d039052a03100307501c40c0041007040411024050580e596400c00c4030359401505454652180e801c5850703041d5034030069908040d200c50007500891040458550b220417201000207401c025400c1b041c00b11104100c2000b150351054000200d006c0d007034500c81818009245103c1c010083c41c0082e0340c06000e2000b0581000c01603520a10f550710060300c03200e030600945c10700504c2100e0201d48140e05030307001850601840d140100d41650140301464903034942003001c5020203082d00242c10264422607584402c0301080401420150341800c01c451290605002c1012910740050381d10001e4001c054407114119118822000c9514080b013070001ca0303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 754020584 1250 754019334 754019359
    0x51014030a0b160c0c030303091a090a0201050f04080111090306160f030b0f040c120e01060b0d050604110406020304030b01050906010509090916080a0c0e071205090a0210180b0c0a20 80
    0x1401038a103249c004c4803030000145c02c101c82c07406188505405402030000070601e40326590b00545503603000c200c9006112170140800079035801e09008012510110f4240c09440b0400031041c5850b010b00980580d005498605417000b0080d8400c0d40700c0d0840e0307124070b0041030403010301020448035400c05400540150820303d6410645400440c04000007000010401007a4222444203013200c006008640107800d0420045503603200582010703400c460000c0000901c0044841c005466902035402103025030004038080003807018070700d40c1c1401458166203501483c508180001e00038412303604038501c100c0311500400c440900821400b0b4a0100d0f006e0918000c039203c191036691000100411207482c200f250001c0341072083c080119000d03c0b10750701d07000300e00c0500300c00d804040e1800605035003c80c446e1707036410400359445a403140307140c0c245512400401e01c8150504948424250007103058504100102481468005032003165a900080e403441441d1004001c05041e20003000159409445206034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 754021834 1250 754020584 754020587
    0x206040f03210912050408031804020f190201050601170406090303290306091506090a0908160b0711030a140408010903030c08010e09070522051014030a0b160c0c0303 73
    0x40501e00b13001d5400c0c25000c0c1119401180c1c0da100706d00a4000c81c0d007060080d9121380c0b44074807400c20300f5500140050b04104d90200f00600e84c1d0080741020800604a030300160311560203115240d0408428a0122180001c4d00800f061206001d0b000400440e0369803039582c18148a98001074000640310040040401c0d44040c8207050000000071a2290203010003040380100c0001d0b100c0400d8080c110540386a50308c0c00100310009000070b0072442a0342d2665186000908081d000306203241c41075140d5010031350796092441007284024043c00501104107a0404c10384400001d445a0802d2841c103482803040c1110303980c860f402035a0041400e5070a0940030340800d178058205440800740c55965600b260f9903244000b608081c250f86400707032900410001d000c241080c103240061111110b405581c0250403222001c100d885c1250319007103507140440709101004000c004040f4016088008003951003654a801c010503802600540000020801c4c0e0050140246840c1302081e070408905518240e5a040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 754023084 1250 754021834 754021841
    0xd20120307031514060903120f0d060909050a02090709030b0103060603170301150302180913150b0619110307050d1416060b0f1201021c0501060206040f0321 69
    0x40601c0801d0401520503403400101d80e8a0080700c14000314000e01050000a210030380d480b0000c1c564240c0514480310540d40d150300010900c00781c2002c42e240d5a81d0580e01d1040031160640c000146450a01e08114041640010b0301031849804858a00864456003410760f0003018503400100b4810b4580000018003800390301c004101c900807200d044140d060302c009103880303110034003c495030303189290070600409100364080d01c02d107144080c0d000346e85401200014494130080303c489040c1f101003144141080409910b48401c43c9039044c0c140040320851001076194007810101d003030a82d680b0307624158018810b584440c40c4c1c880b25020707299110001e0900584a0000042600100d00310340d00703107590201090b00b20341c12002da00700c80c104910415602c01019007040812103a0003403400111100e540e44203038110110a50400c00165110705082c101001c500c8640654403120746818010050710703070040b51560340503074041481000401c45103400c0d1100a00305070400c00310310000c100c804c00401b0591 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 754024334 1250 754023084 754023091
    0x1211010f0f0b0a050d020a0611101b020f19020d0206091504060810030c060e130e01060603050c12070f21091407030c180e060903130b0403050d201203 66
    0x201c00307103a43c5440704140800ca00380c00d68000d40052541d6001c001c114415007101540191407015524a45941c412050607035260380c00c50307044280107010070b50142d50100b00100c1000c1c0c8034805880d000711101c2c6001030840ca60781020b40160b03540c4248508650f0303600c0464407075801c014400080c8109071241d440403034000b03002d5900401c24070380c081402c5202011a1f0022254040072a2040c98205681194445100401c1c80c1d000740c0c15140600341c4080d540203002120382c400740002483c030300d8800018162a001b800361807010b030f410000c03c030444407541c2d107081c1d0006460910803c55041040100c0d001802c020700003503880d11044180f80303a141150403000307103940551a0520240346020321991100c18501c8010b210450301c40c0c0800100300442500c500841b20103400003503c0d46800220780c20500c0c03c80ba10891500006007e1081b80808003050f005070041218030b03803c050071542c58980e58483d0320501c00502c42031001c03420340620300380c03000843c1507255426140c5408413240c0d00070303c41e08191f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 754025584 1250 754024334 754024339
    0x613120c0e0f0a1d0a03020d0f05031b03040215030408040e010905091c0903020a090507090b0a02071802041e08060603030702151e040605090109121211010f0f0b 71
    0x40c40e00159807441900724500440c0000b204254a0300c0e610a0000140034107503002d90343c0c030300134040141c41403000c0c0981140d450003a005481849141440280318014034909607041c80000c1c4140160300000c03090540310542260146540c0c0d0320b542c00003624080703140072070710610308001080104020500000e40111041c945140444e49d032100d0804054031011229aa036903032044420801c0080340c03003c5251007036190309000320f001c1c1c2c80750045240900b80350400001103071503805101d4070741c0e40709000000508001030b42c1c031305081c60020001e403955124441c0d41618103102c240221784c512103504540082c001c00c4801042c030004041700c1c200800c605d100e079082602401c8001052820080112090207500402c48a504041c0c4600000590024154038880300307030303010402c81814501c0c0c00600103000d00c0e40360103840340a050001020348200350004940e11902641110004000c2809012102103d0808040108013551403030b004007154a9004510740c181941058040c105074031008010b2407d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 754026834 1250 754025584 754025603
    0x2040c141b0d03061202090406181a0705041d06011404120b07050313060515040204030f140a080d180203120d1104081213030614060112050f010b0702061312 69
    0xc070420340032140588907090303131703040f030100424018500580159230181c030580c0001000006111284803241c03065100f01c0398017144000c400d0481100410140c2d0104030703481c0c420f152504007004541c10005862a400840701008041500c582c0104200003448020340c02454803140d654040c04155208035400b610725459080203d005948102c048a21800481d0200c0550100301ea070380c0001480d0043c25a2007909000880f802c05a4590000300021401007070070420f035400d07030b0030021400005a140d103000d07a400f04a0031000134060038113864031075011102c0040c0d801e001c00f1004c50107180718040254036000d90080000d091148030040d064001100f0410440003041c40c42d210514031440c020215030303502a854444040d00940b000b407582a50a1030b24420640c2d50f40e0301d10040e00d503101d81d0203003c020b841c03081003219680f02154800f18502140d01f40842d041680c01b24085003818041d0700c2083c0800204403096454290885581c0c1c501c0008580700e060b920110b0b103c12400d0100e044601d07a48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 754028084 1250 754026834 754026853
    0x90e040605160c0c05060a0201020f03010920070b06010804080d090507090c11060f0403050c01050108030d0f05070e190f080d110f0c061605030309150a0c080402040c141b 75
    0x803d0080f503055592003442028910306200c20401513420a8481c035003199020440c80c2d00107503004000d140200040140458500b500070300030010310100235200740d10f0607010f0207944080b0720115031007a003050b030030f0070880000d03111800c20402c148541c01480c4800750600d519002001400600c0d40102d07281964200070504d4442c10450b5410000f0b00301f400154442004540031341507404c502a0171030700c603040092420785001089400c6d90001d9200002a8102082400d00741569005013403480220701010440e07803a01c100040c001c400c110519a02440c400e400480c85000005640300240414840c080c18442d81c03030300b1050b9500f01100c0041d000860203910400d8100000923488001140390000d45001c02c20785082c00b000d0703000b0b0540800e40343c03d462114030100e00180010f501651080014000c920f001c8100500c1d1004094620000d161801903c1008a030744004020b0f006941114041100010000304440344c6070801700921042c3d0300052100d80b05d68000002c40340814025054601151 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 754029334 1250 754028084 754028087
    0x303180406080706020a08131d0405150c0304060506010e03010207050a020f2b02040f1e110a050f030406091a01182c07030c090b0906030a080a0f090e04060516 70
    0x2081c030606000da440180c02d140001c7d92170001e4403600d802d08281c0720340c290703642d41d90300c4034020192065004820640b0a01003841000d010401c007032000407a140d480b5051083c0701c640789210007040a808543e5031000300d406c681c4151031681d50008010000d540328040e80c02c0407511140619800c078441c07000c2844010b441d0400203150921001443da41c0c0705c0c110000181080c160780f940c10200d030300c9580d58203505003024030307482a00403180c0c400301c144800c900310f401c1540c1162209400320b100f52405114491826502804894810162451b01a1a03445500d041c030082d10403050024514003040c5449440d541e5507a0780c20f0f0480741002542d050138643d80302c40000320b40a035095491781480d1100c07200c2c2d05088560306003224540d5042265846603503921140d11a1142e6000320315495152840200f080c0f51145182d03412504c11409402d04100554074034010f482200080070521140b461030514260058041000074000e0455941e0980341030b18003c2c00600c0110b91390b1528000e2400341e1020715 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 754030584 1250 754029334 754029343
    0x6021308070509130b09030d0504062f160201050d141f12080c150a0203070905090f01030b061f030219170a0e01060b16050c01080f04060515030318040608 68
    0x1901e04c0d140c0d103460301c00b05131079550a9240003800b51050344070401c0480c1044403a842a5442240a0f450005203c02100c020720505c0c04194a800f0189404441d03220300d00ba000000c581005555000c0750700c2c0f8108910050b40d440c01200100c00000c1c2c6403400e109181108420301a2180b4403940c0b1800308001002290640b0024501a0440e403845081401c0c0000f01e40e1401003107d200c86400300c0b1008141a0151640c1034801c40d04612550b801009000219800070f100300080e0004075890a0717a03280c00040764940ca601484094800b2000ca0301080c904d440c1c000400c0032440c00208810704400324400068013950181595080020030070300c0c0021010321412010000b00744546842600c2d44950036800b000e48120140c42006542e610320019142c141140200103549600e01c5554150356035050075803e00404944007418000e54208100d01c201400a45551080c0d01080000c1ca94942c400c94003070030161000c4d040e800d4030000864248040c035410401c1c2204804031001d00c082c0d42c5881460f03407038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 754031834 1250 754030584 754030591
    0xf061204120908030d2007050d08060102030a0806040c0302070b090115050a060c2d03120617060c1c0c1e0906020a060203060d0f0b040b01080106141c06021308070509 73
    0x513a0801d020302c1c01000015000305540394100c440048500d21454603000843c0d101d41004c84c1c56912589000155a80020400e030384032409001850030700c510303400b01070441600240001d10490307807410306444040c000e505a415160300020295984d2a11041c80741c002c0503a00302c0c0400380b03000d032800042e5519041c06032000703507100e03503a80e003c2071109695881d160a111544c542e076000c40c42c84083c000400f14100d98048903001e075507044140701212020404440c100d800000940400076442e442c085000120703e90440d0b200036600c3da680710350140740c240702c200da01242c00035141840f0140504503402081b41005054010070484588003c3e0070640f100d00c240c0c450900136810000320640895195800345600c581e028000c0c0d0b8120b10282e4403400c9400a20b00c04a81300200c840c01d02041c00344c4060b0403405001c10f40000c0042c40d0400c503040000000c10100e45100b006582943e4888065080c2000751140d4045015900c3d1884210020051002c5000c1c2c0c0c00e2902c214800060b00d0315102005600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 754033084 1250 754031834 754031849
    0x62d0d050408120a09031209030c0b0a0218100e150d0c0503040302240106031a06030702030a020f06010b09060f09041e15051806010504030b0f060f06070b150f0612041209 75
    0x200761a1f001c5404002d0540104c0503014003200054002c08100414803a5104680703420b00140d0303910380217108848081c401e202c1d0074000c0c018608a40e0201d6084543e00e50040801c95182c0107401e08107040e10800e03c2511581c0c25038130b0a100000c0c4141d07821502940c0214480d4080c1c54500034000c121a0342101c5080341c9541a60070b000c01000004c0c0690701400f0101c003498442200010080b010502682c010307211000141e10006910401603030600c00303074a400740c1000103805d09514000c1c0c1c074000c0f4029a40040e02c640e8001a810840c0a2050103c8011500c00791003407003070345100e0300c4120038035440004d03400c0c6031424020804d540482800c1101e05a42e0005c05003400e406038107140030059200202170034140141003001101085800030b00c0d9209e6003e140001440d480c264060000d00b112040280740100c50602a06000449108280b40c0c0300505100c1c42d103040030000001110751941a0100b88c01a2000944032140c001a50400c2d100314001c0170610600000b41d1002c6483c0400ca114110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 754034334 1250 754033084 754033097
    0x6060a02150a060b0f031e0103051b1807080406060b0a020a08131a190c02030c010c06061502160b0301060203162f030705062d0d050408120a0903 64
    0x640c22526888640e0000071a50001588a1315166102c2e090b5001a1098007084800f00811442640c03051480000d401c40c00b03035440e41075255983d1942c1e50718817400c0c10329500012080810f5240c07111006050000f0700c040342e040700d60070440ca014100c0b1006a900780d807440d0a100000c51800c0c418030441d0b0500d182e5a00070304100a00d5180d44580c3d030040b01045110700b41040b000a01c02a003603250305400700150030f5055440485100c2020701c0c0fa85503101100340100c8481200142e5404130f94062030f07290130301f085e40c241c1105140ca480200401d03042041d29010250060115540c00158555040c3c1d854140d100c0454981803085010f020910950b00142c1c420444c1c10306030307000c440c070016801e0307c1810840d11044180080810b91005038000702405032002044200610b000c0081400500080d01c82e140b80c146c00d4a1a07158400d881420a1005808000103070140c1c6440e0b01101c0708884408400c1185040900e02400c0b144d21000110440185910101e000c26503244501d0100aa2580b1081c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 754035584 1250 754034334 754034353
    0x7120e120d0e0619120c0206100501030f0b060c0313120203071701020913020c0c091b0c07090c0302070c06050c06160c15020903100204150809160e01060806060a02 72
    0x40ba0303204454640c1d503821000900000301d803003500315901e003120300240e202c81010000c42e07410300c0c0c1168004602c6104550104080c800e00b4004101d42d0030036a4003c2c6000704d8507403c1c10342c41c40301800309840810341010000403c2d00500c0c1000c0040c1c4103000d000e40740e810b0640d42d220000001038605a40c080c0d4150000501040541a00340841140558113000541081070500006100070610001d890340140c00280603213042c0800d00141c445491304540c1ca00352400e0902d801c2a00036a01018a08501e90001d00c001e881d0740108400f00051048080074400c542404170020043c0d00550001c136002c0100c014007260b02e0b8010300903113106103010070042001e0360351503105800c0c600d0109107280900070300c030109a0103c4c411a07a680c40e0040d618402681d995a007100781407421a07101104000c5c00e2042c081400100e80c1c51011005500c00c034034041304a61140c41005040280035040403030316200c1e20b20001003001121590030f0490f0040d8907088031540e114814000700e07101e0000c000b030058101913141e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 754036834 1250 754035584 754035587
    0x2d01170906060427050a020a15020a02040c0c05010f0212011d0a0b010c0506090106061407022421060a0506030f07142a0f010b0a090b1507120e120d 65
    0x14090388111003410302404100d45503001d61101c11345000f038400740c00c0700600b9020341c24202580002030402481c580404d041e40342e402501c0d048131910091051343c490121240451041024265a94102c4000c001d03003040030f810031000f907201411004803d50344c5000000e04844071300d0b910700034404615003200c5950b503030301c40031700203010700075419051000510110700400c104020340c510840000000081c01c03403c00750040e00c4544103241e60703070211004229244c01a1503400d40c410400b4440b1030011032406101000307415600884d040c1001140300c801e1403590740300103070601c10b000e05801c3d0744080c6415168002d1103803620045030f61840c84840a0041070203144140580d01c02c1c6a0142209400d28403800c0c0044007202e01d0400800391083d005e110b81c03824040502c8140c09201c000e5008114120441d000300d00f04412a201e036140a43e0f40d0482060161290400c48007000034100c3c44a90b940c0c86403401007200070488407800001a401c00c1d007001c19003400b9075001091901d0000404c0d000130716450 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 754038084 1250 754036834 754036841
    0x5150d02100813061d070816290c07033c060609020a0c050106050f01080f10030210080a050f040c050d050a020a030b090d05030f152d011709060604 65
    0x808441d0610040e40c3d01e01050041c17140201c19074240e05101050601c215010307140113425000150150041440e001d0307012612944801161841914100800100721030764503400075481da00c0c1a0103400040c403450082e0301113201c130140e0784100c0400415030448682061404e111084580c1c118084007a07042564203042e0010500500c9000041403440e01c60400c41d050381c001200c3e2501040300c0c41c00c110104202802004c1c0030304010741e001c01c0c00d08220f9000030b0895074054a003180401803040800d00264807100d135240074603006040e4586582c48140b0042c90f20714100c507000c0d280c07071800d40400c03008901d00042a00860f00b1a80748903e0a0629003001f000401c841d00407a0544100e4803643d0058035201d4041008500500101441c1e140400032541840306c603402c40410171408008020744100f4030031080b5040042c1ba0310020081d516100800e40c0501c1c01101c0081404c4140300c01128090b8885407814078100a80e07510041141c0542c424110384410340b04901d0755005140001d140f03042030b50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 754039334 1250 754038084 754038091
    0x10b1209010e341413050438010e01060f0c0201140a1701090b1206090a1707020d060b0339150c01090209130f0f050304170105150d021008 61
    0x145059103480b40015407120700041540410b00d544d2098038011003030b15061070060000d06002105202d03078941940c03401031030b0344400e220310004003420880400032496030840f410740e01c10481010006584407102a40d244509104501c00100005518486184103200b81d2141d030f5030686a1410151015821b850142c21103a5014200061443e41c00c000746c1410401078000d0441240000720010138105101e584100600c0001c2e10380c1c44a0b003446151100092030b031507805c7c2c12016401ca07012100740e0350440ca2045840281d4414240b011010a100c8280e2001141c418200c0031207552040c3c5034a43c494080068000108010107010410040a1903503685131440c81e0082007001944442e841001c8242c001d02c00504c0c0382da554603600802c50412441c00d03134010071200710401d030398402d40c2d171151451250f81000a01a07100800d0b40000c01c10200150340141442603480211038030b08800c4940206000c80380d0162828441c0090000c1d4240f0850052940b5000f44c0300401da824010026581c0c0c94000d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 754040584 1250 754039334 754039393
    0x30509040f0b030a12141b0d0507210212190e0f030d05090307031a1909080f0705100203010923040b06190503061005040f0b0901060f020c0405010b1209010e 69
    0x40c1901ba80b0610550014130795120b65005460301001d51001880c900714030709403840c007400340400c042008039601b401d100441540e64503240700e80070640784080b4144180048008620140404c403030b105900c0d651a840f0380d01203281c1c5e8051700c030b00050040052041203031240701d0300741d040001e1900301e49210f00004c0100c0300014003103d6020395207669608103940b00c0000751005c0a800c40070300150407a511a24011010010010b001d03c0d4500e443d500054072440c007601d100044000f80c0d00c0c0c1009000c1c4880c003004c0d00700d40c004546239a0340d0540040541607811a0801d8844032040d480100202e101100f409075402400e07401140d6199400c1c0014294600c58400305102c41c110000703030540d42042420700c0340b9212503407e840b1a18103420302c81582e4503003110420309810021820300300d44603458454110740081c0b502e40161061010203a08080340010001d411078208000414640100401055090402191b4445507510030411034221184029080e8142d009144043d801c41d801c548070882d20502c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 754041834 1250 754040584 754040597
    0x60e06132c1f02030405060f040201050406030203090a1a060f01030e0627160501090909020d080f0f0d14100f0e0c120702010606031d250b07030509040f0b030a12 71
    0x82e41c0b00000c44140200c00b542c400d4000040104100c006d00566401100c1078203450340500702540080c0544c0036034002c0100700f55010000880910b0100480c0b11900e800800c0103801e082c040c1e5064000000c204d45090080400c1d500300301482d4403a00c140c240000d66403014200c0742d212210701000020540c00d403541048e0000146c01c1c12520f05008000c01101c4c900032140c0c00c20f00e042d00151140f4000d900c20400701e03291000010140c2c0794000f01c003034126070040c2c40b20360703800742c000f0180c3c0d080c041d003006207000403004036040d4081201980f0a07121680412640f8a843e0b0301c14035500002c0d0b149010b1218070118100c81041658007400085030000c081c0034641e82000c47c50f20710788018420489144006039112101048143c0d01403040b000501c1d000e0b418880189690300000d60b807899090340c41c0200c41c582c6502d9421a201c0d480c006c3d4040e0a07000c0f0781c070b40c0d901e804d800c0007080d0390450891580303d46c0c9800c2c07401c4911121407207068000ca0000c0d0240c41410b41d5501c8a020400c2044100010b1164 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 754043084 1250 754041834 754041853
    0xa03020f010309080d020a0207062d0201060f12150e0a0f02012c10030c091e0b03091510030201090302280602160e01210f0501060e06132c 61
    0x744c07805011490100700c0c0040e210202101c00a02d0b00850360f0140e001e001c29044041c10601d88010000a4090040708000300040091800c900500b51503010701c1c500c00d088440890490740d40000041c22500034010703000c04564550103c8111000c5160980640d0303c0001c46c10001802900143c12103801410074211000e401c86484030300b844010400400d00001c2244031402e450a1030b84031603040d4852508004108403030001801000c0340740200405001c003a04411030707100c145c8071900058044040740c261242040070b943d595400e0141e182501d08584040021503020060f0b502d08100c07a0160b4135482c0103841c64007482a000305a24140c90091240261f01c404e2805003e8004000d02d03807a4000c02e440001190108154143c54010040c41040100100100341c407044c1c0a030351001c9070980d800c0003c20140391600765075002c0c090060285d4204400010616080d2503c43e11400c41683e449210140c0860320600302c5041e41c004020003c0c1c840e03224400480e11095240c0034103c0d02c800ca494112 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 754044334 1250 754043084 754043093
    0xf05061f091e170f1e2a100f0e0f0d02031e0d02030708090103020703031d0309031b1e220207060e010207021e04110418060e09031c061502070812090a03020f010309 72
    0x40100c0c007900000c980c001c00605981010050080f18a0451230720030580c0d05800c000034100101124424450309a6180d4102950f4503020f1340e4844940c0103046502100403c0250052501507050321030190042c5006000000c2c0084101ca101c0340d0700031503c5190682c40c070010340c020b41006000703500b0555100d13403a1840030b428001e00110091171500640e02ea0400c60101481d04e081462100009038594a604405844c2c91107100b42c640101100d50740d8075035000d400b090324540c218400c100a851154500752000005038000c0003003500403030050100b41c0b06914507500b41c0c4661180250803030008030002c0310300001400e500103003100050021540505d54008114a034001707402c01c00010045942c105d80350a034511621000300303407805c4518014a401d0799803a850707004040000800200030781d07200d4021036103907002d8805080c0900c540c1c0811300000c2002580c4440354050004c042c880c841e44200c0084910050780c44400009044050841c2598207000249001d1803905043c941c480005d2030029 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 754045584 1250 754044334 754044373
    0xb030c0c010c0c0b0c0403230309100306060828050408040b130f05040902090c03070c0f080307080a0e0d031112040311010f05061f091e170f1e 63
    0x40301c80343e0362960f00c840c140c1401d0f4284000540070426588013040200000341da40340818407a0507404080c59180d0030100c44080c00c41c8900c40b0507650182100301000120b54256010b50140c0b4040e50b106084c540d14501c1c58100c0039038094200c01e45510924011040c1600ca800582e8024494040a070601d0b07074030741c1210815003000c0b0010781040d0303d9003028000340066200d100001c10b000c0314103004c40340382600440c4101c0e0001d070054041c504000f0002d080c0c0b500032502140326650180d202104c000e0726013005146604185d03151800030b0300140103d61216500d000340301d4484000ca01030070924158860982c014044c0c043c0300c1203112030912000d000c604944c1c841512543c000c0d1501c2d04034240e84181e1508481444203000411b5150105012850311181e842c2c0b490440340c040441010501d415003501c440c54150301403c404032130b41c159003201c0f105114210301110b03c610900b41400702500e806a8640050380e0504810ba8040700c0760f0140c01c59850525400b40ac0510150b9201c86035001d80344011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 754046834 1250 754045584 754045601
    0x1a0705040513180b1302033423040e0613051c0c020103020d02121602070602060c070f0c09060602340504020c010e010f0f0605090c040b030c0c01 64
    0x4288003280411090900d08840c0d05080007200e400c02110120020316452000c8502002d80060074003c006900d5444240203207404a4006089848000019100b890300d50131014021120700e60a1900d40d18024610085105550b0345a480101d50b408488030f401c1000a00e0308079682c496182c0e540d04101d18000c4c030295005106076031031810404028185039292602814046060320b402d03142d414207a9a003e60300c00000c950901c0c0250b50383d81e03c0f0407500f002e40103d800302e000c02aa5442031100e407102042003ca000c1c103058003038402c000c0d40e440050340c482904403030550481608201000c000f5a160b119241c0c0c00d48a1094880070b5038888800a04452061b0000c0e400f507803201c01d20015400e044c645002c1d88055000d000d0460302c4054003003100a000502c48c440c003460700030071040d400c01c6c000e4124909088200000f0800c54459400354000303814881210580d20386021000306560800e410742c684a94012000c1c203290514081009480f94401484154060010300021a01a900b030245020303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 754048084 1250 754046834 754046837
    0x14060601020d140a0507210215060a050105030415090f030239040f0b03030a08040209070801080a03080405010b0d050a0303050c0c0a1103012414040b09040f1a07 71
    0x42450028006071800105640aa0501902030845049803400c002183c81850b02440d040ba1506117614004102002d42c00e601e0341c602e10501045418203900040c988001c9044030740b6803040c1d03152142840344440c20b6008040c0050300800000c2d000c00c040f5005408224185030001a504045032145030b0b0501946070204c0c010380103021680c001504604c0341552002010400b00703080e94041c031078040755054886005010350349400041c010480700d9442641501c0015043c0daa03100b6100034014114842210203e203d84510000704a4480c801d1040d00d0590303117094000c14104095450035030704c292006104891940d21a4040100c64850161328551144148020402c411480c40e001c1c041d140300500c0048d44e01c0c0103008003d00030400194644040d034011402d40081075418020074003401c40d8103210240b240d01074400403001c0801450b0b40b03080b40ca214401030081c0900404000030b991034650742e503511985035004900071590420003540842d100d0076a096600c403280f02c103403484103000c807410380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 754049334 1250 754048084 754048093
    0x11e29040b1b010c090e09010603050111040617010e040f050703050106031109060f0105090d0c0918120c080f0307120504050c030f060115030b06041205160914060609060714 76
    0x1101a181c0d07011201c421080e682c024070031012010f2005008008034031030070304400d0045000c82c001001c203511500140d50480003d0010601c1081c010440c2c0c2d202e8460000002d654142c01c07010040700400c014140c540d1314200e110f85848a46603401b0107000200141c90304d014030309000001420034440c5400440c810148510b4103071040c0108015840c000302500d02518080e0407404c0076a900c0011510722034421135011582c2d617050306040016850f42c1c2c000880345440c01d1040030145c0d510030488056113104101010b00400c500340d04540102c489040200401c8040c030480c00c400108201541c1c1c0404a4500f450012410149903030a0f524140c2d02a611074119031003001c1c441c202070141d0700e54200c02000074040d41d45000140c0000c0b1092000100800d941d804441426039124822180104021000a07071f208a590601c640c540c1c00280407146590001d80b000201e100b502c0c054111240d29071030081d65039a580768140240b603400240f407184c1c0258100250350010301d403c7c05540c41301060500a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 754050584 1250 754049334 754049347
    0x108060739050304090e010f1a012106051c060c17010b0d020705030d091205120f040204141801061505070f060b1504030507050904020d030e0105120708090105011e29040b 75
    0x500300d8801203224500c44c6e400b030040c1c4009d030340c01030b2401741c940c05ca10342c2d81603920512903c1f5a00030540380c6c1080307900019110724860284900058581424010780041100d8483c03050706075030841000841001c2041004010030030410400d0240084804c45103016141c50015954241540c2c048008102820303624401c1d00c06003c480ac80700c00c081c10040c10518907000d858240188160f01c020103a0580d003514400207007c540f150380000a0401480341e001229042c42d500184085111890310f20b010342ca4140000340c1d1807212200080c000c101c9407a0103151844940b20040305a0703504e43c090b50090380b6520b1150840c2c403a00c41903060380003003410311502c90b4210700d48542804044c3c2e0000781314001c1c004c10b00015980d01044641c55076414241041d10382e40d140d005880c2400b80002d2101210f43c01010852015000b0302e610348030720840c00003044980c2c0c91b06d1228400c000b5100001031052600c0c0014040c00c5d98a815010ba0a807c130000f84c1c44006411a0010f066071142d002081c1103035010911 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 754051834 1250 754050584 754050611
    0x515010e041506050307140a030506010303020d022503140c06041d0604051e070905030a060b010e090f1f08160f0f0e06010c020f090108060739050304090e01 69
    0x4070907040010102c02e016442c81c04000a40d107004a0003205112030052032228505e0380c802c6600401164490300b40c4541e503950741406503d89005540400242c05151034240089a1a18401380810030f0b09400c80d21542c21602d429000003032010441460344101c80306a0819518580034000400503151861145140070051552460740588078600aa090106015070402c018030f03241400b060700c0411b5040c982c1c4051040b00e13444165403089405018001d044024001d07590002c81d880902a00c4900c841c640080a000010008440305d840354a41400803440101e04000b090394034440c0d07110102c4010742c45004650810009105225503c05a500100241c3c040441d500000b0644540788070103a5181031502c0c212071a000305054108100e100c06042156109401000c0c2010050f111080340d6864054440c1e40305401d80b0038401140b42050400c0c031070a01c3c1c1c4400d02181e10801c0894003400103c414100c22200d12032412100d9001c24000411943c61038801d2202018109002049103248041c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 754053084 1250 754051834 754051853
    0x405010906050c1009080706050c120114010c08090f190e07020a0503070f080715050423030417030702090f19020901020619021306080402030d080f130515010e04 71
    0xc000300740041840500b441100100752140d9141244d6808285041c0c0f03482c05054901c20f082c40101000e00d02410700c0039050031500540030054034094100b4103a40c0310090325060410340305070680012850710741c2000007503844001c0e0080100c05058500314041c00740c0054008446001d0740208030803030050810203034040c11401500a0014000350651441c0c0e5100c5d55228421160701620f078241d4030ac0301004003c0000100c0345440d800021680450a551300d0190280030240c800360303402c09502c0780e140500910085503008004030f0a004601c0c0510f4180ca190091405000513009400244000310150710358090b580c0c4034188c01c3c612190140b40c400084103001c0c0301076000307907501441400424480d0b41c001600da90041150381711400811543c0054030081d108541c6404078151890600045841d01b100b40347d80618401c4040e28888008108210f512a00407110a605402c4000c0480e070490004122141c0983c000c6080c0d0700c281031209410b0045400a070f000d084d071903100c0410042072114401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 754054334 1250 754053084 754053089
    0x10f051003020603070311091011070e13060509070b0f0304060c090b0304030e0307030501021309050c030c0301060c21090612050705090f03160303050a140c0a03110102090901030804050109 83
    0x40000d40041c1c10341d000f01d20360740802820f0f00c013410740d20758214403201b008505440100c0001015181c00c00800f5030700600030640f140003d280b510a10001041c4000ca0300c801c0c91103806880b02c140b0f038280e15521448041c2002500404180c01b80150200d40c00034108002c024080c0341d07000841d560b042c146002812104202469010031001d51800c0c4510450300b03007240d4002d0740610308441e02c1d0b8002c40000e03051455a900042a9600c00110a2048d144071101e43e4200c59000c0d804000c40ea851045223246403000302c2e00040260010401402801c0c0078110b48048580540c001d2000c070081c84045031094142d01c8031007804209660410804254070000c0306403402c01500d4240054180400301900600490b8100c92052151b000c001c2e0050711304020720422018100080180f2951b41d083c040c29a500c41072036030001403107030050303510b10481034000c5402c40c480c0b840041107500b1241e207040320891520b80d614a1595004c2180d040c65980c0e82d445640039601805e01d150b42c40d4503046c0050402451070703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 754055584 1250 754054334 754054351
    0x703030c051c0c030c03020c180a0c03060f0504020a0215090c0a08031908070c020604090b10020d1209030e04052410080f0a14092404151d0f010f05 65
    0xb40312904045500c294040c200680c141407414000c81c0c149001d030304002601510640250480c1100c0803449040900360b070007800c40d1b0f1400c001901613280e04070103407400c40c01280c0e10030508440c1017103103003816801000351070a2032042c5c40d072400030034043e03003444682512500955880303001050010300e0710198840040040c0c2c00254500b4814150201150030380f07610400c04d1005110014880d40d010300300d01081e5942c000c00c00ba6440d500e034074108004011072103a0a000d02031410049240c6800059501c4800029481e06803c1c0308201b1400380240c404004c0031010002600409086920b0302e004060241c50318150340c0c964400442021161814036140d843d1007450722440050f041c1d9000b5024a030000b54022070495a9695480313404003a008003802894908550010040c0002c0c000c2084012291080180003003241c0d00603142104620589001e80f010392415480c04400015078003c0c81c24003103001d25654003001c8901076170304003004255040241e07510358481c076035035007010b20030568040f80703a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 754056834 1250 754055584 754055623
    0x2307031404140d020a08100f180b22020d03030902090f060a03030507140a0b090c06040e01090203040f06110711030109030e0d080904060609030203061501080a1107050703030c05 78
    0xd20010710700300c030030a10010f8041c4a0035054401552585810301001d006040211008400c00c80341000061401c0e04407141c059107030249644030802c080c012081202d07001840d824154480c000f2807504420040000343c02c08030114501001612013030f02d81341403503000f51000100800a401485000352008103407035054a44d480c200500b56541c42c200e40192a09858156140c0001d8a0030060405420244c801e451082072420f07020040d140401f14480c0b01c2d58800d43d104c03c0810f009020740750080b4011168120941001071000d0402e42c1c1c003955000340145a040f21042c1141c48000031101d25085031002307143d000842109010404020140b4980e082d00200410403031903e004258003001c0f2100c0d031256840504110501c0000c0b42a58419040140108801541c506000d0031169543c40101e0107030203000c00180f4007601e02d07a541d154960040c2c580e88029500c0c440e220000380100c91000004003070500408000c58010080304000c5c0d0320075101c0c40070000d56410300314030f8580e4200740010350400e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 754058084 1250 754056834 754056839
    0x30f0d2c0c0d02152203050106032003030702120a060c0810050a0f290c0d0e040b180606040b130f05060309120f0f160b1f0b0a2307031404 61
    0x701e0141d01c0b568284d16502d9142c641c801c42c426440ba0f441450b80c050103221304140c011082c0001984040d0480703100e00c0d0140e10680825111414050b94000030740e0380f50b082409400d0141c1403d40341c4201c0782030180c040e540300c0c0c010b0b640c9420031582414121800201d42004100608091500c045d020700021211020ba9602d45440300040420301d000743c4020602e500b114030b035140700707109044000359001e200c000c0d140c0e1100c40306070f9544d21940c2e07801000296000c7e104103007801c0900c20103504c1000a00440301400c03105403111417480d00030b804681c0106040000047c8006c11101601019030300e0250703034040a14099491512008a0f00003d1040344100144480f540b400a40496800c4200840c036848110081e42d0b5002c0b8010318020703000c000740000d0024103207140d00d52480842031041c00c82064035210000c1d402803030009000020040c0301151820310040044034068100c03ca61072500221041401c40502d4104243c0110703251303008404a110400c06811800740c403031810711100703400c0c105031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 754059334 1250 754058084 754058089
    0x2030c03191107060c020109091a0915040c0201140a0e1c0201110304150e07060e011b1a18010506130f0b0613050f03010e030f0d2c0c0d02 61
    0x2162040082040304880000300d49503000d02a000756080c2c41d10705030783c24180d48240c060606003042070224009100c03444042900c110503c030303403103070000b41c004070300c0a03a03100310280021694003030a9191b11042d0f11344840700c140e50780e00030081c5900c0d040c0c2c004903038405880c41070030210030085c004149803400c1c0080703900f68600c001101000c4171368400745c03001d0000918030180c0c01050182800c2d000b001d800000c010500251391550140e1f50f0300490304000b030820607070b002600c42040780a80c2d00000c100241011141d881948600c1000b60695050540c0300641ea07078240b50054a114050308020b43d0000300200c410100c00d00c080342c4680e40c0c0090009240c07400004215000a0451004541e510940b0016040d40c5a121181c03051002d071056070f9850420622411103100d511615102c0c410710451502d450806018010711100300a000f5424403c1c0107441d10440e4106d405041c0700b482d968500300317500c0c800f000316400c840d102d0f02c400b02040f130b907200301c06505001e000e11002e4081c0f0152541000141c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 754060584 1250 754059334 754059337
    0x9020109080d02190804050a06050301170f03040501210f0c0f1106060904140d08220804030303050c070f110a0501030510030b09100e010c110d0e0906060f0a020c0a050102030c03 78
    0xb604d9a900c6507402942443c0002c11030180c1e81200707802c04404a00407a00729081030095044e100981503108407607444254090352200741c01031b00c4400c1e0b00180070800040d405607241021003e807820420024880e0a00c0380701c22105202542540f0a031500e600503003254005203d41d40f198651b00e025030000580c00c076116640d181c003811150040300340b040050188070310340ea00c046192004c0010b941005440c1c1c00000d00c0308405075448070042c1c1444051450010f0101171081c08558440741c03150800c0e203151015001480010711030301030700d0070812845000030018020a1001841406004910302d00c0703034203001d22000503401c00c9051501c1d002c14448050f03011220041142c0d0300810500b02d5070382c0c80600b41e08020708942002d41850030041000407812040d041103541d02c009690b00e240780d40409201c80d580384039442000d004a44006011440c600342070880c0303644490045d20503441c14119882c03840d440e5000c02c2c0c1420042c2c011021980e01d0346400c08103040100424130085060035101d0744105d80700d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 754061834 1250 754060584 754060603
    0xe060c010f0c112802040e06010f09060e060f0a0e010b030123010509040b060c07060210050a1812030204150305042616021903030c0b010f0609180605060d09020109080d02 75
    0x16401400319103035405000301d070f581c0d111758064401d005d000ea4405007540e9580080c050442c0761800441c01160b450300c10310400b412119048041000d68941d48203010481440010b040e030014000e200200340e64202504070350003003c2a40c0101d603039614001400c10b120710803803400300e0508202541c03180d0300d81e40034041d1115900d04403000600c0303000c1e42c00001d0092003a8000c008103402030a0001032640d03004500d04501408820092003580c0d1070f42150030490b04480070030000905210050302c04a545601d01ca19156641d00300185042d40303d82400c1c00c0c040e4101c170304400080c0c85200f04010080c04652120640b2804840c001d81ca0f01203640da00c5940c003d012200000c14541c01a1304159564100302e256102a01c1e106018215282d0074000d20842c1d00c01c1e0151141c40504000107100c09440300000d08580d11f5a60382010705090102001c882810701000d1010207031656008580d90751440d004102000079140005041d01d42440003600d4034045910000c005e8025981080d500b0f034001c90780490 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 754063084 1250 754061834 754061863
    0x111040f0506030a0f0626241e0a0203160c0302031e070206040824060d080c0c030706030605030d030203010509010b0306011209030f03050c0a1e0e060c010f0c11 71
    0x11030340e41300c4503020700404c8441074429016040540001c1d009080f00c544c2c9000110000300490321701d0168004aa5500c80d030003203000550180010000301c202c212894039001003200304900c1c40d1810b1103200d8004100309580110846034000148884071801001900300c806042c02c02c2c000103100c139200070307484c1d00804454043d140e1a2062280c00004844200d0b1240ba60061850b522140c5034131113240ea8031504003013000c0e017071900120f01c0711070650050000d220b090020000032a0810310b55500c4020340000300c502c405031240c2d41c0700318296507050040c00003601031a94001111880c00040610b0001564050030030326104000520054807818281815500c549403180e5480e00d5180041307450780c86814400c55860f203003680702d404265014104440504042d0703400d020075200ea04410b81e81e44240016080428400e9083c030101d00401c400108800d40c03103041c407078a0400c500c0c0110f60150712400d0030001c107035550080050301c582c6030311407078100c0d04003071410b006124010042e15541d4084940a40d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 754064334 1250 754063084 754063087
    0xd09060503070e1327151805150702010f02091e01090e0f040b0106050c0d0c06111b120f040911090a1401030e030c070e2d07020111040f0506 62
    0x5010a000c0c4031041400d00c009080754040008500b44c0c00d0042070684240b40f41c0c041144c060650078503007090b1503040c0980100c44a0f405100180041c4024400300d42094005444610010007040051005002400010000030900c1c500180000e08581e030f080c03c0145603d20608c50607074981c56248020741200c039503100c06c2540c100b0b0b07080140d5240216520459040108008009240c2400d11855000c2e512414a51410781d0700c0b620b0a4549018401065015a01005008d0080b500c160b02c50003545000350700000e941c0448058158080c1d101c0180d030740d000f010411107010201c40800c45108185c000c092481d00301940c0c2c0d102c1c040640b08522460900903143e10a96400b103002e50112148400b00500b4603403015a14000052440c070140106c0780824034101c0c4200e150180841107614207803400000d0326a031400c10940910100001d404c04081000f52403074201240c192942d0b0503140090503a8245440c81d160034000e095a010b20780c0e0b8454034200b03010400c0198a0380e100380c015224100d6006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 754065584 1250 754064334 754064341
    0xe0618150a0e13020c011d070e0106050d1d3301052d0901030f03121413080c0f01051b0405030601360e010f0203061e060c07080706110d09060503 64
    0x4e4016601928040d510309000e20b62882d94004400c2089040da105075440c0307565801c02910304210910800c00400c0301001626000c0d1140c3d440020400000000c1e0103000781000301144c645880621028169418411000c805000c2401021100c1011240d800c40660601c400b055003e070040c0c4040210713000b0501c941406601e0344950910b00301000d44204450340c0c1d2070a00a80f400c45609054010844201821164400d507000c0c607498545043d500a00e80d8540c0152070f00b02105d07100003503801c42e0301440b0b140c0e42d03030781d003448404012102d020000c07805040964070441007842500035800c401d0300802003001a5103000c02ca00d41100d080e01d03520b46a030300750a1400190b08034081c000b020000010360780581c660f916648002c008001070720081049404088110080348419035086031b02c00520300039561403400203148080749000c058140c07803c101d070b4030801e03030301d440347c035400161940d00882c1040c071240e540031400c501034110b2080145241d5500c8030000c4e2200c43c1c1806a5010800004000b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 754066834 1250 754065584 754065619
    0x1050a12170708071e0303110c0d0e06090a0e010e061c060b010903050307120813020102070e1b040329070f0806030712050f0d0302040602030a0f0e0618150a0e 70
    0x6440c80d1380d400121651130081128207100c002480710034200c0129181ca9041c15180031803000350350044120b0001400d28030b66440040e00c1002d20452259030180003006200040c1d1503800d0004020305014048802c00c0d41004082e04c100031000700941c2c017460086486002403403071191400050354000130006501c46040004035440541e07a0805413076440300080ca8010000382d5102a010440303150399400540e01c44520001817045604030103030040e03015020910030800e40a42d03044d003100c4a801d520ba904110b009030071481d600980c0c001d8803000304654085885420660040700f5900d0b841003904511300e4007182c084d020402d40d44004081005410028040352420440301c0d010300782d483c014980000c16890855a1000c2900b4840118001c01c2d1360300304100c0c042c0c000d56058840316000396085c403050901c01c44030840b040003d4410000c14241c0019079440700c00060903484e088001500c1d201c1c01203420b000030500200103002164608200d000310440c0d0000070b008560004403a00030700e58803034154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 754068084 1250 754066834 754066837
    0x2307031a090108030c011b2705030a030c0c0504020304020d11030106031e030e0a0617071b030801060e0a030b0c0c0109021009050315010e0105090403030f0c030501050a12170708 78
    0x8a15003051071140080340320800040600071040c4004002d0040714502005004243d40102100011131544000303c1580701d50081a01103031801d0200381c81e10a507a5074002880c2402e40310b002d50100b000d1071201000c0c040e400203080041e250955081d86141082c2e404500b810150500c0601f03031510041c2c20111725a0290031080045400121044100c8041c044102045006640840c003048104004180302d05101c000e020454030103850b5100c80a0192050100c0a00018114400c04c01c1010300005003c10320707200c0c00381a034000c1d5074800d502d604145020301100054103006100d0001c220302080054519403603a603000031708200140d2200c1c00c9101ca00d02401002c54000c5d44040150b40381489240d022045004542d800c8044400d80b4800021203402094280030390b580d050b540f90014040c600f031151820760041d10034900000c3e503c40c2c4509090442c0e441c0c84204000076111030040060b482c0c070303400080c064455800c044000170070590b41c505941c0e0b4800c0c0704584400d0045120018040d00c01c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 754069334 1250 754068084 754068131
    0x1e0c06010b04060c3e0f0103060509130201211b03090c092301080a021f0c0f1a090d08090c090105042d0c18030203061807080114040501230703 63
    0xe00d400190300c44041060f0b0005043e4581c940100c11b840c015904540c03080c055402143c0b0302500c103c99076110350703110180c800c0703505000ba414040101e1a00100c0400348544502085940c02d000031989807003032064480400c00f01701031003014200390509010900d04a918030848126240004004400e403440c400648005000040c408170795a00000e42e00801140c101c0102c0d0ac21075194000451101a0313010341d80380f9144410016402040c0c2c940041c0010500000300e50040340504880c0004985000b0403100c202ca0107402d130f40145a4080125400000c0f8036000035010ac042c0845048503c08500c2142051296a11503501c82554030902c164000d03903110302c094203a88501041c465000740f10050040003500000080107410403841c07030519050300e0400e132603008000c1c00c0c00f0388030204e0b00d108400092032b0058040c000c1c0300c1d000031a076030309200381d0000c1d140b88803c3c43e001d8a814149242190045044101a407030791004109168903603064143d405032090400148462011401109105014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 754070584 1250 754069334 754069403
    0x9100f09060302280e0618130b060f1813060603120f090f0b09011e1107080706050306100905030102030c180406051003020a051e0c06010b04060c 64
    0xa18021a400886400c1681a03a0080e590400040714030045880003202c041c150380d8004030303c0d40e010301500ca02440c2c401e410220041c04000040c5000c451681d100c1c1e0107844039409850003020fa5001c0001c1c542460b6809001161040b81c00e1010740c0210303205040c4402210305000e40180007428840c042c0441c09405500030700200440b503280d01c1c11300f01c2071300c2c6058440d000c40c1130b081d0000e142070310401040040d038010706420301c2114503010b142c1c9c0d031581140b61000c1c18072041808800803440002002003000b80d00e507560080c80e01281101030b0034040d0b141c12076070f0b031600608414003045800c0b81c11a6084941550000d030140c070071f4082282c1c0804541c01443e1700d54000411700910040b4040a4504400d411800c05180e03503c010420088600c28030426800c101c9051044c040c4c1030280c0c1c05094140b80300d06005142003003408101c0d501400c40340c00d080030640301084089812008001c480c0c00350540708c0e61245802d04000d405040d2100130744000302384081d036410b0f80b8200d4004000290340010074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 754071834 1250 754070584 754070609
    0x1103030c0307080a06050a061218210203130e1e01090b09130201020a121103161b08120318030c0d0e010c0b0406050c0723010f05150910 60
    0x140145450541c0203035001000255a03e020814808203440f954045078801469602402d2a001307040e40c0f00b0044103d0340faa42a078854400c458075800c8c00880e40e441e0b200d104548400c8223940040d510f080b0041c000d90045501c1170001b9402004d85000100a0f241a202491419614003102c000354070004ca00c0901640050000010700103101e4001c801b00740f00c01c42e058480780e628042440c0726600f03642c2e40a401039000500740c80205441009800004100e0f01d843c03428001c805000c5495507000e4401d000c88050341d803019a0600c0003020030210032001c003440061405150148050b0344203d20f0180c0252803c00001040306821110b0701c1c00a050702d0b48041d26122800401e605840e420f0340007141c4041220241e00d403185610561070940c0c4568802e8030505c8581702ca44401c002007100514164000f8802c01851020510b42880741c3c00049140c4c02080b80d0345841c280702c90070768692400c450072480c1010103000c0c901400049450251030160781680c0030741c0c3d900b2420701d04600c5c20390091805644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 754073084 1250 754071834 754071841
    0x1704020f0d08131d040308070e27010b0708030a111b0a0c080d0f031d030c061b0f030619030c080304050a0b0a0509210709020d0f1e0c110303 62
    0x40b00c0018000c0e4040300455030b400c00760b640d08450452003d030045546804403240008001078060340803503030808034914200da41c00e04038001040c0e42e088034414000040d201e0300c40d001a07017080c8080c0b66002d0302d801e0242500b0545136554400ac24000a0300404041d511200175090040c0d84100742da00300000d01c100016100110009035466540d480400e8845260441c0d01040e000e4000a1f03907446949255541107094007400c0c1d044004204000c1c5070070510814800349a5014000c1001e81165500c00000d40f8207420103400c1481080e81026010110480030300851101410410030340f5070022084c0e0301c450551440e66810b41002c150364000a141000c1c0d03071404904114000094003d03500d042d00c4c248081d54446080704601c1c09801254800103504000e011070f281406401d00746803002004102602015002000c1c0c1403401d80d801118401c1e41c0030403507188000050040d030f2542c84007100304200401c00580b0702d00000030403215000209480b050720043c650702c1501e81c4802ca15810003566160704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 754074334 1250 754073084 754073093
    0xc070b0319050a23060105030112051603050715021b0108041a0907050f04020301050901140d060203070203180409020102120903030c01061d01151b06110d060503010f0c1704020f0d 79
    0x5a0620000d15404c07214155460310301041d507800e8000c080507160541542c0c80c140c03060400d000c4502c002c076150b019000100c1202d18000c180440a944600080c0c050329003002003850031803200085071720841d48000e52481000116000201000c6c2084c40d041d000f43d42c4500308204404490036480420b101010300700000e26034085590300580e40c04031400c140100401040005074042070281d16400b00070308004000b40c61320700e0215410300034082c001012401143d1111340407608121140303405a000061a014010702403d000d0135003842c100c03800c001c40d4619400007507580104203000f1030005c800140040060b83e04100f07448100a9520086c03240c03507181c10a0b0700700e0007124a030042d02e0701e0680b80045003800210a086001d0030103a90f505c1c022000c800c05140003540d080fa42903500d80d40d140800e804141410000f80100d600300040841e006180c40300781401c59401e0100e4040701740c50000b0315120f45500500c1d40c3c8180c1100c0c900c81d01c1984407800001d95466140300021361140c2d21942040400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 754075584 1250 754074334 754074341
    0x1a10030f050106030e0309040506010c120e0a06090b120703020c0a080714072405072009160e1302041203120b041107080721110c03030c070b0319050a 66
    0x304101405112a9980c0c50741501610441c100c540c0640d08180070340021418150310841d840201450a01001c84040e10342c540415241141c80000698407181e400803802d00c4140b030402402c2d24600540c0b014540500c100d441c0c000d050120001c440207101080c1719501c680c050701c40b00c40b4400c0030f0302c0741c10605181981140e03010a204a810b000c005d001041d15a00209110080300c0c00040302c05070084803200064084203101c2100c0f42402400d00c01c40010454001c03140b10040c0d206200317061802c4061040241c100e0b002000d04841c141c100d42c038040c1c030070b1380100c1824800740140c1c0d0a43e00740b83c400d02e2583c041d02031030300210341d100d90a0001c04d040c180e00080b4001c01d4028810200151462a41880f007560040314141113821000c001c40300024021a00400c1154001d11421602130403440041d00c1075000c8401c01e0001805241074407081050a0150007a200011001985000c0b00c0841c181e4460680d48601a011036011002a4210440c45e80148000c610701004000e549482203580006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 754076834 1250 754075584 754075601
    0x92c130b10080709180f0311031305010201050901090507210b09060601110102030103051519060e1005010306031a07050c0601060c110609010804020f0a031e030f0816031a1003 77
    0x40d10440c1d00000d03480109106502a10f400d505c6903a01c0d40801d038840d49100300c59200b04800b00648800ea2109881060026025880400080903043c6e03240034002420758002410b4480103925003a0707030000203000041c0d100201c0b2961415000850102580c000002008801c0078101340d00e5001005000c000c08501c25200306000d0b22000555990320300c9003800c0b80001d010080865214054580e0040541c08c055035200315060f07103c203c0d54010328048016620564011005150000b040c46001d0002160103000b410080c0b0b01040308603d5504c0309001242103d040000145240e808a00304503c9807040303030000e1220b002155000c2d40d45050061541c807003600142c0b50381c000c8810245041c0b41c10f104840840405075214813070f917251a0200001c0300300f0b40042690109005000000180c1450101c80d00d46541c1143d071108490355050240c01c021031404680d00300002c08003040320803141d0b12190048901f01745000500400c03180c0442040a49200c00f582d40824003034030b0b40303c403141d15402c52000f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 754078084 1250 754076834 754076849
    0x10203090315040c0609080606041109031902010e0616080702010e10020703020103140f1f09090f05010e0105010b07110411120a0f0e0a0813030c03080307092c130b10 73
    0x9450b60341764001c40c2e02c2515801b9669840e0041c102113a46840d0981110110074881c0c5801850034051000191a100c0034180b40001c0b03c80e0145850103540e004030007080c4a0a040d24680d10300101c0160400e48603c0030700d40200581404904d050035a44503036000c0c2c1000c80090041e0180c43d0710840c0c00707940c032802448128002803c3c80c0a945880038080c5045000d001108480049511196110030154440002941008084041c0021180c02c40e00070300d5055801000c50742c25000440c20281d0945907500314100300c680c10b250041144010640880380002d03003142c11206080300181c001405001142d11a00500c1303c0803c4003145009224401c43c02085101c00c1000518204440f50065691200050702203401109002010800d010700500c0344814040b46040c500d80c6035503078032910343c0481e001035400c20740101c200f28082c1c0c4c003e0200c40107080514900c69101180d681c200510502442c011018204404041344d02240c0441184e000a680700c4022062460075040d082161000d0703200d000b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 754079334 1250 754078084 754078103
    0x4090f02120714030c1c030c08032d0c0406120608011a04050f2814100503060703050f040f02030a02180901110c07060503190219200d03050601020309031504 69
    0x3e555103000078500c0940c220103040c00543c03c02500d034842c050400030205405102d00205032100292200000310311440c0c0049007280d4400e094010b200c40070015080101540314100180300041d0b06100036501110b0345460300d03485210502d100ca10140615030320903006c3c0c1d0309040c861081e10f1100301cac0c107a00410094400700f09643c0c41c1c410389072111f6410b0768000424811140a8130403181c1c0d000c0d00d00da5400b03035013038049031610380c001181460400458105140b1f03e540c5809001d03510701841b40c107422204900c1c00344110b0820141001013218054402007500c90009070b00002c41d18144a44809141c00814410520300504508481111f0807101d101c415480d00c00c070004e1003035100050714518858500200b0380e480c10420181c4480d84050011850000b00810f407034658917982c0010144041d03484250032180160f43c03009070504d40000c0760044525040392900e070b51240c0014120254900c079280210b8503490b040010703030441c0700b02190240c02d03000300700464a41814500180c0d002d14451041d10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 754080584 1250 754079334 754079369
    0xb040f030b06042d0e12040306050c1206060a090b0706050901052a0c0106050909100501050901030f0b0c0f160c0b0901020d1107150f0e010e0d0204090f021207 70
    0x80321079100720100310303141c0c08480c1442034441c280d41c084c503030b00e02074400112868070b02c00c604d183c01c0203401280011100002c00348100211405915081203409013050f080031020743c40b102c80054000c02c3c003402580c020604809040c46010782900904580d1070032540c03480d45040c0708000e0320b000c41d40e0f040a50301302004100c41c02c4034403804601d8030a43c409481400c000a80014615500500225480d5900c810000c101566001c00590046a0b490020036148035840c0307841090319416841248142c80300c400400100f40c80003d030b60f00c802c1e4040d02c9a0425980d042500c20140110412000c04100105103607044500c410541002c8600907002e18580eaa62450051410b100d511030003401078001aa90391192401445040d40c0c41d0506019180740039101d1003e045c0740f0782e898101030000350840130404806d58011558a555400a1900c070318103013001e40205070083c002c0c0d00028052542c03118418203000120302030141699004010140b000c01d1044420f6441c400d50140700c0d0900e4500040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 754081834 1250 754080584 754080589
    0x7031d0303010b0a18080d0c0302060f04020f280609030b010504060f0302060304080c0a0b0121031409030c03070e0601270b03130212012c0c04150b040f030b06 70
    0x15207040f00d4070406400e1405103040e0301150b01d0302c0d4405001496100c000c0c004038007240d00f40600100e19880341e8955040300a10f0800918140020700303440d16620021003400090b8403034541d031240f6140c0950f03014000e4440d01d10f00d6001c1c40740080b1010b5030b40044102c04608190701c501c0c95000c690180600c20440c0c0d89807001c11003218100c5c411040c401c42d4043e0100010309040d005941d000340100c1c5094105405401c1d02e80c100306e4000342c200e0303030000c12034014404281c002211104c01c90180003046408511560050602d00351080d20756540100482c407031495650401881098420140a84a66580e02c0c00b04000b264000c0e03401a01140d8400880300900740344c581d500300c1e88170a002640303003603500e032200f500c200754006804107041c6802202d9640140e16166500180c000352a4000200c50944040c2e5900b401c1d81c410384441034218940c09999011070004107407102902c22140010308106080303244829030225404450004004203001540c81e190b10040c00840303002e0310343d110135652041c08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 754083084 1250 754081834 754081837
    0x7150509030303040f02131503020a0e060312180a09090c0b070812040303060b1305030d140d050c04120c0608060a120b180a06091e02010c151407031d03 67
    0x82207400d64028800900418942001e404110340054048105081054031200648158498041103074460703540030400c608000c0f1800d0700401c80c0c01c0001000b4100711300003030b868804084d40440e51080100700105070324000441d1212004e001842d6024895440c482c090103024000800c0e102c44888070400075100e980602150f0301c0300d070310015042c81e0010310000f07180701c010050416020503540d210081144c00c5104001c003005844024502c90a510340001c042c60b054001c881c04040000e9142c0d8141142c3c506800e886001529800201b029591508a004180120f50111035800d4440300c10b0700602094903141401c0d1030302652407c0c141d0342c0b000c0c1400b828040d10f2040c45141044807030381c4800300e510300c0310071a00004001900059182d001000514220b1130b00e009940741941c1d10169010841c9800c03100c4841040c1e0500380d8284000c0d600007818242d945200030340040341c5201300048560311980070f110800c01c600c0d240700d0f003824020340c010000d012040201151071001c03900084e08440000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 754084334 1250 754083084 754083097
    0xb040311040c091503020a1704051c14120a020910050705160302090109051803040621060b040302061b061312080108060a0908070209090a0c120201090603020304031b05071505 77
    0x3405044d49015803412402903100c280c1c1c140402080c100c10982410450714028040d6010380000d08588000383c890b5240b290901c0401c1007482440898808050022010b4070892203a80d03038605443d9407502c0e9520301900c10301701c0040c0d001c8406040c24403191340003070203000b61310301600460f032031800246000301c050a00c601010358442c180b50010001d841440e00180c0c4c0c03252038080d42010002c0006e003902d203150816000440824501a150389215481840700035a4540c066824082c9a1074150012081d21803804060f00540d00090403100035821801da030221032203144102c0300c2c81c0c901036400200201e9004c10449505a95801c03131140180300300d80680c1600e03080000781c0745548590314018010551b042d02201c041c1418450031001d13030b444a9242d0b100c0d400d600d01a106c1e010240c03600c40d441b583c19030801c1100440c0c1d54005800f44c1d80c844050425100d46041c010ba90392190306007a01c1103a40090a6140d0a41904e4000108080031824904a40c400e000070f590044410700151143c0c0102e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 754085584 1250 754084334 754084349
    0xf1e0903030604180506040c0810060f03020f061b0d080609040201120b011107030b011a0f0403060c05190e1c1709060c0d08010303140a02030702040b04060b040311040c09 75
    0xa0002c18200e1610303500c450058800c214400340d482c83e20ba0341d61820800121001d8809407980c5408002840092017005040242c06c0400c111660600a2140c1000ca4502020707014450025441c00030b0740b1101c0c101c0707a02481a10707924400c52003d0095654501d44491031300005203c00010a01c0707070600310782940c000c80d07058540105507208400c80e20000d148400210741004074030b480c0c0740d840302e0080c0701c604080c0d805000116260f60504040702c40d21030076800544c2036078408004045c45900c4000a0f10160303540040085080c0c00440000c5481d401580081c1070440d0300b0b19609850f46400091010300b0031401d50300f60340368120342c5855060f0724644183c0500001640d0315000424100080145030711200100201d00f0b007600f6001061500d80d0141c42d101c04541080014003d064110f0003141c01034458003040d5160843d0000025124041c14500900454442c411200c8654032a0060405807140e25406c030388541d0b5a040c20103d0110b1086294002d0303140c80105204144240075040541e11030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 754086834 1250 754085584 754085587
    0x1b051905130605242704110309061b0d0204080c0a0504111b0a0519031202041401080a09080a0c0b1b040605030c0c070f15030b090705160b0f1e0903 65
    0x103a1200c030380c103c501300c01e0a0000d090100501c050011102a102d40c1c682c110010020f0442141d03010302040310041c07581c11011550034402c02c0748143c0000390030355011109402d07980c0c05d511012a080c881e80140c07655071022a0006c18003040e2100d001824403000001200d0301c01c1c8240d584c0701400104c034070100010341341c0042000b50040d00414110300c01b00300c1e0580000ca4040001c039481d801e0500e10300444138002082001c2030b120034180e1244031104261405141149020f25040c003e42c050403503020b03a141400900000110300b5081680900708042d009a411a40c880da003810042840e48100c60460f044250340d0007066842c00d0400503404500024059180b9040c181038040c0d80a0b08001c00d40c0c1d500c0e44007041596640041800501c00a008070ae09a850b150304080c41200d02ea01c0c201040c00405180c02107100890b80c03046c44841d0051030608241c1d543e80c107108002c4003c488c4482014102c142e17100c0901215040c6c00341044c1c031500000008030011300544081e050220350582c0c000344503520 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 754088084 1250 754086834 754086859
    0x20a0f18060c0203210304030f020d050301050f01020f0a2a0b0909041b09020702090f0601080402120f01050903031b0c280f060509061003080301031b051905130605 72
    0xb80d030900110b540000c08681d0b0b1941c04409000359080f241030802c08034500801031000301078106031510b911910380d001800e4080364601000f00702d80014801c00e48603402c100d15440440c2d00038030400c001611038609488101030b01d4107054808500d105c00492811100d8000328414610b444445429100b0103940e29103054901d030100100d168020300309a45800d04840700010707101c0d007160b20f41c1c0180b0b80d0640c00740c1c56040c0c5004020032503000800c41ca10043c2d41d54200001070f0b80c090151584540c1c11141601c8100107920260314189580c090800590300e00b03810b1240b8050008055481480c120340c0501d0f80c0d80b2003241d24001c0d4041c51100102c6ca901c40c442c1007014002c1c00415091101d0000310899078659940c50312038849031006400d48a0039940e406020440c507051020903030004100981400161550b6125039652005200241c480d01440c00541c43e00300d108107454004040c020180c40c01400021f9404440460604c80c0d00c1c8a402e5000650000c2d03680380c0606c008880c00101036241052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 754089334 1250 754088084 754088087
    0x60c0406021f0b0a0305070e0a09020f040c140a09150f090b031909062c1e010f0501080d02060a140a020a0306081209030708070e070c0311070306020a0f1806 69
    0x20700e1111030b82030988641e5224159103520036010010341c0517074000d011183ca4400d0f102c1d0010805000d04a046080c052080d002d6252078a400250761016240050710011611044411400c1d005546249000000f800360303225030300150703a9082d550211201045029012826110710070981c0c0504040f44000320208888103000c009164003021500c1800002d01d120b8031070100300c5401030421226a69601d4030680c030300c2c0c0d1510042d0b881108544081030144181e518050382c2d4592400c4010f20581c901c012000501d000b0340006c4091044041c080c0441e507114204640c44040c0710070480014881e075000a9101142809039460a4415010302b16080d1185000040a5070000341524181904e031100015400001c014600440314040f0026450b10010410141030803581c0d880b103c5c2e180d010180074080c010004940c40d40004183c10035180c010183d03d01684d00074909002c80c2c0f070a0140e50000008e0000513001840e031140180c1c1d5a90121f078281074292a1400300c6d698500d2209211041401f089 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 754090584 1250 754089334 754089373
    0x302070e100308040303050d1503050c040c270509070f0f050c21041505090f0127091a0306160809010605091005010801050105071a06120a050f060c040602 68
    0x12094600c00d5881c251a41c6500081e540650f00c114001140020820082009440345104c0718a405a10880140c5140c551580d00d18004041e944126910a40201018012322400b5828035140b684500740c1c200103120b00000086510035180100602d40028403214030038400c0310300e040f94540b9108000506400708070b844d03030415017492906115801d00040d0349110400110050940c80345001e03034440c1002003c2c1402c14580300000207201c824040148203a03540080c00d08000d6003843c100240140d0702510305c003884c04080f0180312410f409400881d0ba20540d80140c24181242401c40ca00604e855092580e184421291014001521400307100306510643e038094104500c02e002080c443c0e01c4000040a40c2c0c4143c0300682c1d96050b0100070025542c02c071100341e00411003400c00900b4a80c003a12004102c2045000c90f0110f07504400c0000ea40f962282c03001407402c040f4900725038000415107001c9984040130313108211a0703c81ca900244110b41480200c400344d402d41c0d405001040c01442010000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 754091834 1250 754090584 754090591
    0xf0f03060506130e07180903020c120102040e100608160f03110c071e06020106050901030327031a2d040c1d010e0906070c1e060f0e01060e040302070e 66
    0x8240445594204200c0c1e0040400450a05010302510340c074007050030707681c01b0700c2200043c07255062030f25500110b0307000b181c010751000c01a18010195500300d200e0500a1007aa0040d10220382d101090001a00320010000e060750055243c010840d164010290614584241403d00142120b0000b0b910a44a5080007007115900070701241000d80408400f401e140c9140c00012030310141101c4501102410703403184006100c2400200910303420240411141b82c014003005c2e00703101140f50b808441440e03a42450100300884414103030400d0700c030302e49403c0b03141c040e285500b245c00300d01e0b0104000d8180035a81441500c0148008e8003900c0c03420132440040000104183c2d803c52615800103001c03006912868a1003440d2440c00d5401c1d0704200d1030750481c91014114030080d80c00070341000f040e2a04224640c03505a042283c00740034091200308045104a02c000080041c3c2c1000c000c885501015008011034890407402407011546562040c1001c400498016005034407601040141d0303940540380030740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 754093084 1250 754091834 754091839
    0x90b0907030906060b0409020a0810060c0b251110050603071707080613020307140f010c21030b030d0203182403040b0103031b0309060f02010f0608010f060f0f03060506 74
    0x10205e564020b880e44540281c1e00004000b60005032042029078064483c80d4001c543e00080401c2d2802c20034001c00e40505038000030480002c3c41c0214041e41200355030024820f2598492080c81c2184110040500e144104884200d20403c4170100300c003466070084900c1088090020115240303002a0540d03250b078070480080350f83c06203c0c00403445030010b000540c0700d060385452442c480751580c818189820499840448250618040744810380c0d075510341c80c0310303110092038030b2420300001c1c1c201503034040042044203907000a4203060020054241c0c00c1003d980c0d008a080d201007030200780050342c407842010b0740b644c0002c4442000c0710b007d1914242d084515140d000720745400c03100c2c88140b21000c0e0b00c103880548800e2802001003042541c41000380c0300d03150b0070982d0091030520540d409084904c0b00d0091006100c4032080c5d012045200350700150b0075103203000091242542d2380d100540200102415548101c1c01c0400100c0c0d41c1001e14141402c0300c8075506002809459503d071440202000b13444281d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 754094334 1250 754093084 754093091
    0xc011b05030403060b01110d05030415020c060f01061805060d09140601030c14120a02040b1c0602182b0203010908030124030c020c0f060c01110a020106090b0907030906 74
    0x20034810070141000d103206007400141d50013080e0015050881c080280c04a0b0741c0881041c0d81401d07401800d4030340081e841010010f410280740f000001901409111040c0f6100d40c80c20020020521403032141220750b01d032a180b0f42048142801001c800d4580079098101c8000c00840d00e45481c142d100d024624005e803600e000400190001a00740182030303000380c40340c4460080500c040c4154035041c4032980d40445584003038240d044c0b0401e855807800000a4840da580300d480181c42d454244c1000840702c0e9502c07081942c08ec07580b4109009420603d801060b4264180903142141015004000c00c3c5010b0300ac03400c3c401c102a40ca0701e0301a8242d402c00c9030103540750024500010020805180a072420403107018481501035070840c802c0050342c096900f054149002e41d00020380214040410660a9850507420ba0707865020030582d2285911231a0550311380260b80f6004a400005070034020807a41c001d0054555503102041078803100c0b02550303442105080807030b0159002e40d01c0000194031507500403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 754095584 1250 754094334 754094387
    0x90b0f2415040b0d0b0a06080a1d010f140907050f0d05070b0307112e0f14071709150f07021e010501081005010308040330022404050c01 60
    0x3074107540241c3d004060b42c000c007040da01002c40c071a019006920100343c480000562802400802e0110094005095150758030018003e1000b2181c1d0480784055400c000e00c8121501844000140000300242c4441c142e96804600410000318000b021924001c2001010824034000c102810001203000c460510981c0000240250180c01441c41403100307840366001c260391402d129080032a00003051340c20500800940d034042614101c00e02201e0703c00f80307001441c00544c050b080c0040400c5030703181c0b1b40401e03401c080181031030340441c2c0031201c0e5042681a9520303440e04c05c1d032a1b950b24180c0c050038151040b814001540c841e41a044994000460320480d0004104210480328030a100359a51100340d44900060042100421024000915007482000a98510388456040703000341d00008001c00d0043c11400e0400e01206008103c504a8961000c50f107031800d40043c1d80c1d104034941c0109180c885001030102c841c0c0f4402c0c581e04c41c0d0740110151510706080f2004440051102d05c0b0400001c6c02103200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 754096834 1250 754095584 754095619
    0x4030311190f0311090d060f0605040f06090b03030c2802090403020601081218090c09060d02030f070e01020c040c1b1506121e020d0204050901090b0f24 67
    0x1480c8041c0c5075032105581e010212070024140d40484055036900341042105c00780a8544c0707417202c04002e401c410001035881541c0c174030300c014203510390049511a041502c00d401f1140107903c45411a00d4820f810042080039200f803680b20702501c01114641c3e00050184007442d569144804079400c1602c10905402e034a680c001008c00300f0640301600180d0000005105080e420800d050080b4481040f09080c42c841c0b01c1c184180741c0100f03907060700400240d00032517010120750003941c0240800800c030035140c1c03403000c0902009410884890103001421400f098003a0300030078010701c5141040e800361001010700024480900003c400314000c001000840103000700e800314000804501c0380c200007030582c640154100655081340c00080140b030004980030001510b140c01c8030070a14040300b040042400c0c81c000545441d4112001035041414881003004403101940f201c0041031148100601c40d80b00c0c140d00c180300d688129000031403a001c4404042d80c4181348200440c0e04000203004024041e0200382c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 754098084 1250 754096834 754096867
    0x8220507090504060c03050906360a03022a0906060a0c02041803091401051207020a0c03031e030506060f0c010b06040828050606100203130f0603110705030304030311 73
    0x409681c0139542e41c4c101e072109503250290f140c05c5240c00b40200600c2c02d02100b14490410030f003d45c0c40c0000030300c076154096041342d440b40c058051402030a0320305501450601940b10707150380090030700055281d000d180413075425400622203031501504040681d80c9060074001d03254402e5141d40c043c000903507000001682c503400b810310702c0420703501c010145141034a00a416100307250445a46062141c1902403166402825074840071210100203040e83c0b00c003d0141c0c1001e9803882c000d4440c003030940c000f10a054102f00c00308030b0030600210020580d000040c080342204c0c025100e0541c0544100f10140d12002080098481c0840c1c00c000000e0b000311820000d46554455032044442d50010580e91f40346503a107118500f015101c1c3d0018808640032aa03a09031034280040c8010701c80e09035501e521210500c00c000f5a244400241c131001c0c80952034010582c00c1021603c103250000f410521550000540a0b0942e0b08880c1d01030020750031501d459030207030b026007141021500086400d2000d003103d00c1c0c9818 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 754099334 1250 754098084 754098091
    0xd06050403050d15050d02092a0a090509130215042321031e07060c09050a0512070b0d0222080607030c0c030f031104080705030d082205070905 63
    0x80b2025910101444020103403555480907080c81c072204041000241c880c16090340c200c0368102c88001655403086403a0200c58607480103501d241800700b02810a040024000300090241c070346804040f15a02d10402001e140201d402d804402040034000d8014240b45002000442c100520b0030f050079143c8900c1d0403050900c60040d4407071102c40e841004903041c500081c0440700b18143c05202d003000280740c3c0a58034803d046e070301d16021160740c03000e03417102c0e5800060307444c803952085050241202021006201075060b00506206c0c2c0b80d95840090319240c01c3c81c4100d840182c600152070342c14540a0607620540100f481002c0c40d1341c08200031181070076100070824400301c80d654040300190a100f68030b40307080310091404040c1072a1586400741541c2240314056180da040c80c04900400c1d044004901030030094142e4141610081400703d09144080f40d48c00584209404a410b5000d070342c00102d071407540c15103c20b0411410007042c10003481100a84c1a81c881c01103048030840380da6180a24121b40085 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 754100584 1250 754099334 754099337
    0x50405030d18060201050c040e0402012a05072106020309031b0a0b0a020f0d0b12060a09020f0904170a03180804170105090c130e0d021507021f0b0d06050403 69
    0x1001d0300c0d54003032602102c00d010302060702c001c009a00d4074042005051243e802003000244007080024116031152003079010560340c04400c801c40f20140d20700c0000d00400560212080d004130400482c3e40114858124005100300071400b090726843c0d142e900003584017a01503140380c0020000001000104540c032030452003154020030f0582c2c09400e0085880744c0107081d40240c5401000140700001d400d406580c64151103140010f1800d03010000140b00c0c842054400110307018060811402a07680d60004500c5402691004410100c100c104107401500f11030003042920030450b030500d10854200a440741003a107007030020b401d0001d1603090205182540c002c484201c8005028880005850400c01102d200503001348101c1c2003035003000c0c0e1036086c000290b50050018a084044a905e40d030050b0000c24110820740300c1c8680d81030340003034039485200070b00c8031302802540101c3c0e00107200189441022280c21104c1102030441c3c1d4100018140000f0981e0b444000e0810405c0840d6840c41082d0151348203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 754101834 1250 754100584 754100597
    0x10602071505030c040605090f091801110c03030426180f0409051209010c0204020c0304150c1a0705041508010f1401080c22030506041b050d12050405030d 68
    0x1000c05200c1c12a414220090030040103000780070030441d104003501d041e54950b040c01ea85401642d0042000f41005000070380c0c2c0700807443c0030303c045900d825003c0c0c00c07001e44850083c00840307e40d60800955100e846e00f80a030ba40d10401c00200030036046401c00b0a2102d2880e02c00c0384441c40303d81c440c82aa000301e82500e40110154116091701d241c1109900c000c00000e0320180301c25003068503100d0300d03010a121200c40d2904c0c0000d640d125a0300c141141c4040c40d900030300c11521405003150141c0d6a410170b0103a500f6489a040070303084094010292a409250300010002c0740d400380c03100100501d000a4200414003100b4400417400a001000849445410766207130ba045604d0300f00619004045580302901c644120080310b042641d008451960100c40008001e82c1e403168006840c64805004500310000024880044104072002c11824080c50007558540e0401060301100c1d4500c0d001885944e0f8091001911300c40060360000f560092800e0904000d400c096961001c281030104520303c11000400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 754103084 1250 754101834 754101839
    0xf120901240501170112121103040803251203091509030f0810140d050a0209012d060e0108190c0c03140c030901110f01020a0c050607080708060f040e0601060207 71
    0x340404c614600d5040e42c01d106241d545010311501800c0c030720301409008a10390b40350b100009030140ca60810f8155804088039611643c551400d900d0340c00c5034100300400060169031030000802c400c4901043c503001500100b80314610722040d8014180362008541300589110000000103040c442d0348210303402030302d03101a01543d4240c020880b440090940c0f0300184060802c0c0003000f42c95000050113041625203a8080100d41411840d044a401c4020f5210780d806001040c2e01b26407043d41001d10a05c0a206034441003191440c6034030703002900070900026010080703003020398811180a9000080d01030a6a030040b0b5100e2000141c0c4d28800707074034020414051652080580c0100e0203101c03800300c200390b1403d080b0840d445588a2240751045810001800412000c1410610071403501030900c900841da50840248060102444204240c91300e004160010f070500b4080c0061510076181952069802c2d0b49078402c00150301401142075400523520301030f950640d0810090140a404160020101c162 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 754104334 1250 754103084 754103087
    0x313080f031e270a02090108010c020615031b04140a020306010f09120308310c0902030601020d031107020d060b0306071d010f0311130e010b0f120901240501 69
    0x504403050665041110400c000c121006801d4000307080914503c41c4001803110080c03503241c9040024007035072200c1820000034001c1415408281401039903001d80d078403a5501800401040c000e00d0300035400d50000f05100d40e030400c9440300221001c02c000c5c0002032032080301c50402c00c00041101ca506540341d0001c140500c541e0040b4204c0450b500610300412140d00b4002c0c03c0710400302c1080010140074070800860740c003000728074100402070384181440b00c00d035070007814014102c0090203064600980496000c00d10007007500072680b04040c10307002401c1c190f8074000c0483c0100048004800da028080c064400145c0d10380140304140c030302030200441c0e1004008105410003401409100621050706804d10840e0b00140800d500381c0024240140300d00032181040d0040d0103500b07a40c0388414000104003405c0040d241824060301c008916285443c0c0e214441c040e1548074103012986082e070284a9405101c1e840d03405a82e00c84007002c00450118039456000c10481c031441da042e17900b100314403c03c1c0030a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 754105584 1250 754104334 754104361
    0xa08030a060312111e0c040902060708070309210b1512070305030904050a0501032d06090b09010c050915090a030501050c030406200d090614010803040f050409020f01050313080f03 79
    0x4007840c80072a6040c078100c0a01d176548500c0403a095000c1c988070082c40b4299a1450207031101141c20002d003580c1c41d207041c540103003200d05d2406024000c901241102000c0094041c030642400d90ac40e03c200a15202c107014141100019950581c3c045210304400c4950902404520001c0d84948015030b181c110040410055072401400b0414040c6440010400300d407103920b0103035406100d1061010441c500840302002460149005450700782401c41c06401c224000c0c007014030404040000b000010043c480c00c5915104032181c0d51307842807100c40380d1182103211000034001d00c8001080c1c1951282e60b60340750b13800e4840441d441404d481d00482040240441307400b900c035101e0221103c44180d00c2c1c0315040f1203103600985246065481d9520700800c1044590351003001341009580d420307081507a6841403c2c0c2c0c1c95005020f048251010032000003101e0401340512810160b00603d044000000d800044603250001400710074001d00c400e00d500d02040e4a540242038000b048000d06690303103884100503014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 754106834 1250 754105584 754105603
    0x130c17011205120a091505180108040c0b09041d031b0109030f0e030f15070e0301060305060105060f040f03060218101d0301090b0f010501021e0a08030a06031211 71
    0x440c0c5202070341000031404103010900e0300c51000c42c03d0311040d05110071201401ca6400c003090003ea404031007512290840c0103040c8030b210b4411079442e25800c00300116a40790b01a40c0c01059000854414049408a0307005859558409400028109441051010701100c00950f008981d0400650800d80100040440c200c0040300402800206202d54008000d401020010420880750160f14540f0365030074090007903c2600c80013140d041074070b141e010b200821000d13075158000c220b5202c03080741c150606000b581c04030b0b6045406001268645424003581c3d0303008004a4584405c10003001ca80c55207955680780c090f6001e07007070060322641d404c16403003000c0d00c601d0416807046480b01e1141e850154090b01070441044044420b900050300e070408070780986010b02c4001d007a402d600c2c003089540c54209130001c0c101c038004da0850301101002c2c2d9021514051108001c4102d4001d8068140800c020720000e503003002405400140c038540e252218003010240c6520040050440c041481c0480e0701086000301c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 754108084 1250 754106834 754106849
    0x6150a06090b0f030a0f1437020d02070c0f0602070b03010e150a0909150f0603080a2f03130602010b01020a06051b0301030c082a0906130c1701 63
    0x180941020321100540c012074400c003143c5100000002c142860b5a005440b81b0201c2c0e400500c40d98100d001c1062a101c0101c0d4109586006040d0160b00c81c6886504180c0e0740d00341c8554118180c51011055005c4e601c8403107010a01074007080300f040000c0781000f13644010040070003001e0f071040c00d2900003800c2407030030750140303101c000d05000500c001042c05001d542c20802001e04a103414024401103204610760354000da4080e45450030303d0051040740e044030703280420318100411052171604c070280c04880302ea0102a001003010700410102c14040c1110b605424080e071420400c5995407284280003984070f03620307034881ea00042070107885082c1d8042c21001070451400240b20705001c190000b5a5105c1c2000c019280b41d8844010414181c10007032900e001d8013803200210365968490814a903800442d00c10007040b44505040302c212981402010352102044003200b290401040b1b040143c0d407030020f482140d10824660082010700e6451062081d503002c161641e415030a9140303440a58540b05038130008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 754109334 1250 754108084 754108097
    0x30b0108011b0905120f030a020d090f06020c01080a06090609020d20160c090504060e12070206030610030b090a0b0a1a0d0c0908070e0103121e050f090306150a06 71
    0x400b540c0080942e800c1d03c0c02134901000340940740d102c0500c1c10a001c0c000411501001400c5001c550303012542d004482c0c51500c7e0086815070700c001000310003200d4030850006030004c864800d500c0d071280d680250821004800404c4040e2503400e1170381218001e0740182d0305a40e0001e12140c3c0030300240074901c41900034000001d0003c02c440c5080c1002c0c032a00e150200804501503401d01001641e80d419000f512410f1020405480d10b07207070403001003003145650900c901c02c00203c01801c40e0b600040300d56407035028083d141151686d9040c4501d18080d00303040028161141c00c01c200a41390b2124140c03040c100c0c0c460100764161904180311420341650000350103591444142e01d2441003030000c60785c000c07010010008500c084400c040b10b2507240350300550018007840d000058290140540241681d0090141803542030001d40260394103030301c548140e0060b1304505541031410b80528040c120000b6503605441c5407007202d000082c10180201c45c03603e14036072002554002414401401d2000d4641410701c0ba = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 754110584 1250 754109334 754109381
    0xe0a0b0111030310050f0303070501050408120c04081f0b190312050c0a140f03040902030a0b0616030f051b010204180e030412320d030b0105040b0d15030b010801 71
    0xb1281354899001c0d0300d004540c40c0100f02500d46003041201c001e00c1c1c201000300003905140c070303000c0c10f103a000700f0301d184294441c2804101d84810010489040750010001441742144503a040c011700d40840c00c1e0041e4160f510b54603d10561a8410103903030505559416000240c1107103008400d00390000c4514040080c14082c818400600060080c4881e401502080c1582ca6120741c0d646040202c409050346404040740005c1c40c41107640246004d4400a9414003030070b081c0c6414441a402101d10072004074580842003400b0030300403040b4802d903e42c2407602c00c0c0741443d412007105043d07540b82245901a0b40c00582081030b4603440fa4102525000040309100039020b002c82c4039604d0003503001e01707030040380c9401d20b2100708100440e4003041c02c04100c1e02d52850412440d000444ca0b40d4202d2005c281d40160b200e800c2c29180710b440307880e9100c50140c4a0b1410181005205000b54021000526050b6598044000780b03055401a9100441c481c0746c0040141d03042c2484217007901c40800d003681e031140342d00400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 754111834 1250 754110584 754110601
    0x15090806070e01120f02192c01030e01060b031e06030a0b160c051501060e0a060504171f1e060b0f071a01090614120d05130e0a0b01110303 61
    0x1c042c01e02e6070900c2d0007003020104802c0d41006003002c0322070404c580e10004110054013a42d4048041031082034607240c0c4045d840136042c04003003100c660800c0d4505244c1c0300200c000c0d0300950110b014242c141c000090620713240d2201d05056070080d100c00d1601c21101141c01c001013040004568800020b0340038050540f81503849400012000d060745082680240502e41c00b0752042c0c6100c40055044000c8511042080d080010340600a01400e00001e0500700d2a600c43d00300340d0662406c9500c0350f62101d1501d45405110110390200f200300300701030f009449506142c41c0c00e02c50f03071405901201000207266012881044100e0003c91008001c003403c2450030801e010040c0203840c100c00c494030043c1e030359400394074080d0198200d925002000c64160b01c004642138801e64840020340b05459a441f5005610208000410082005480070380c3d000041c00701c1511b1083d0013410040800002030a501602c0d07101a01d0420002c41d40b45410983e0b034003c0050a40e0700210304903c494540e0091840c6003041c0e800e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 754113084 1250 754111834 754111847
    0x801080d18031e080403080417030c0d03021b100e06101202010f03020f030f06030105071d040b0a050a0b0a020607110c0f120111071103030c19020112061509080607 72
    0x400741480e40042c1082500c41c107a094242d40e038650104429917655100d00e0702c60056007182c05000032000100454030303d110b20010490703002020850040c1680724801c90120040c0d8440c03010041030700729600041465030420050300c2850b4155607400b06004040a41a0740361010003000b9141e014284541009402e1105c85003480d0b9980a103440d51588142035402d030003a10640c80201c1c6d41c0e910010404c80349104240300c840c02650100c0007408503896160044640141d150b8402c1c43d020230303025410800b85400c0e400402c415038050024020b1542d0350001a04074469507110030940c3c68001280c0840035130500040d0303482100b600b0030303544518104c10728944e034401507440345020b010900072070705440d900c0140b02043c5562081c000e01808002480090042d00110070845034900034080d0342a841c98048107903864140704034002e24001c234803400f40e4060a80301d824203034103019404103006945486405141c000d00511040050954081c0000a00d00d8071150300c00c00480d000340e400c0c04001c40c0d0110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 754114334 1250 754113084 754113089
    0x2010e0c090c0f0a02030f04090b030f0c1513150801150206010b0409020306040e0d091a091008070309201305070e01031128110304030804090504030203190801080d18 73
    0x29400352161810360f005c0c0e00c0e6119203c1c22005c0310001280010750010302d07400450f4024400c3d02540c20043d080d80541740d40300012060070303a11a180b184050b000000382c00280c1013011621014054007590344501c0c0503514030225040e000122400f00502000100c90030809542040c0d100612080d031400b644601b540c00340c1d019401c1c11680001c003241c01c030354864205000d03852561042c0c413082c041c02a009400404140b19948419a100040c40d480188020070303150f2210700a800301540c40d001200448055000904d000c061558540002004c591041140345000c201c0300c0405d4442d451302e004011008040e6142c110f244c5042c0410451100c1d84454a000610001c0c200840c44500f810703488841401114807421341c641d903614800a604810858104140e80d5035102d649100d00f90000582d1a0700c140d020140000c002000100303c160125800b16501a000384162400e00300b0070f000078107906a18421040c0004d01510052002200500042240000f241070290300d41130011100c0444071600e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 754115584 1250 754114334 754114357
    0x6030d050a0518240c0f010213121a040b040b0604020c1c02030c1c030e0a0b01151e020d030506180f060a031203150b03040f0b101502010e0c090c 64
    0x6074a80d40301d44136603010440c40650384c0c404c1da6100d0f00581da4841540c000e2040c0002c1407041c1e010310022800706108462a203001103402c4c0109505050300a08004e5500c4030403500608070304406002d9120110b0300c14000e40c8a82540850703414507040820202c6409004548514810000502c40c03880020300e242a41510050242e00c2001403072050b0b0842c040c5c1900b0b40301d28052290680c4085c4c0c1c4a43c01c0c070075800c240b80c0f02004201e812102e507030390b502ca188900600890a4400502a2400c0d00940e00d03002880b514013806039143e141c0ca91610f24220261540247e8000e291401915800d4010180e006100b640c91060045081082209801010301400045071207200814141c1c6c03200100d0320065130304941c03015140b191481d0028001c1035824040d9001d58042c61000c07860070002c10407240516080601e00f151100c10340c88601c03001002030050110b210141c0000240d0180c40100c04640481580000807100041c3d440d0700c1c2460502500184200c28100802c5001740340b802c291050350006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 754116834 1250 754115584 754115617
    0x130f0b060307081f080d0207081c2003040b0403080903060c0c072903011e060c030f050c070801051302041802061213300201060f17100f020306030d050a05 68
    0x5a40030743c0013a02503003102a95020740002d10401c45d40000d040d001310b41540003103c00410303c03a00c800d41004402d106501c00601d06500b000c0f0303d601850220991091a201500c2c0f422340d03554503052007a07000340e204454480001c50701005518044c0a40d55106030911146450001c4082c1300c5a100c040341e010300e12504440d8484042140009200e07242c1107101c46031344c07590301d503184c600a1303106449049044401c0401808042219072040400910031039040c0c0340e0005a2500c01c00a440c01c3e0080c540072083ca03c500c160010711410b090003034600426808030541d44030f00c03542c010b20090314a51040413104022141e803010050312010b00304c0e40c00d5503600924403c039031201c0401d0208589020300c080d280c04e10341c901c2da01403084c000341c05080c02c407200b2403011070b415088030050342070380e41c288100340e4400c1455404029900060100c505502000c0c030035520852001c042010480d803c030300380c540401d80d0100400506003410007103001105900c0c100242400d00c4d55500030074911502880c1a4207554 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 754118084 1250 754116834 754116871
    0x80411040e070b0d091502121501090909031107030b011404110406180b03070e010807030c0c1712090a0309230609040b130e010f0605010e0d050c130f0b06030708 71
    0x304d58001002a980803010003441c1046400175000b0750481d41c82e0304150b40c0480c000c0b4542c400c00c0c14a034160307054182c6400c0b038082e140007c04402040000e000750140321000c0341c602c8911106014a101843c410340041060754100b8042e082c000d405400c0c0c0e140220310386544443c541049400ba03a003241d22078079203107410038807001000039410a1a80903416000010050140ca80d0308800184091a020399611105503508075007142919407140318000840c8585002c4008038204500e1080300480340b406aa140c990b200c0e2955056240840380e02c843c3c0d81204600104155001e00c0d080c00801c0c1c1844401d940610a4403410301009000d0f038243d00c2480c00240d40e0301c49480f50342100c0e1241000070a40e441c4080d078848448083c103c1080000000e501c0c02c0f5442021100301c0c070421080d1a0185d4991032507520a2040c0f11070703c024900c05580c103100b0402140e4903580c648416120040c04100c011034050031040e140415260424921881542c040c01081081ca0f4403901865000f5807030314070005c0030360 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 754119334 1250 754118084 754118107
    0xb040510060207080307020307230d030e01080a2a1b030306050f150d0f0b060412020f100f05031e010305150702070b180415170f0a080703200d080411040e070b 70
    0x60ac2e80c80c45500f10020001450034141c121285090700c1c982a20380202c3e0340d41d451548800c4400d940c1507503550703c0810300345e01d11010068106803001c0c0c0c22400d00c0d5940c40c0c0071080034500c580d2188401c40000b81c0386c0005100c181021080414a03905c02d0320b4480c00c007034440f05802c10300d0248455000115654100700200c00b120b80c0c00144c04020060403640c2d4640c0c540c1340a2442e4540b00d031040c1c0c01401c088480e034180d81003001c0300d03030300d08102da0b55021908900a8822a0b0b194006850700460302100000145070004542465000f18071600c0203000d0401d05280d05500324030001e010000303542003198200701d058540030894007415600400f01e20000d203088005402400d400e000b0a0100c402c0e0080071035102000642c1c50303280510882110420945550181e5441c0340314034000f00841c0c03050001d600008c2c09070b1484035245100e034542c082c0050f090202c0302e180035040c0409000054080701842306001561001c004d6820003610305006c180340701c07004956511a184600e102c403500000f1203800c0d48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 754120584 1250 754119334 754119389
    0x91906091b1d060a1101051308180d060c050403030f050301031703040203160b0d060906080309010e13090501090b011d010303050309070902070507080c0d0c0504050a0b040510060207080307020307 86
    0x4010080141d0b8a132000680010b200c0c403400600251039620740000710344050041000c0640c41a8072021a5140000d2007030001d84401d00e49481039000a5075071640400600f241c00391402c00e0300030f0350b2503d40300c600e141001000319035540100424084100014400329800140403460400d5aa2070039969071550310120789010a001d51002d20380144010201d0500486001064051100c00c0d083c031085403076416070022905584100030f400d920801c110200395001c3c01c1c80385ca040d000103101c1441c40020003150001c2c2c03480180121100d940d609201405c0207440c0c034505001d000c000581460003c0d5628030940d02510600025041c00000b10001d01007903010070408024140701102507480b0041c5161403584c1c2e5610707000711143c0d4001c114884640d0304000b004050b04a800485403103455103420280001810301070103d500305519a4004115900c45001d00b40c002c2c403946120002ca5032800c03070002c2c1400c00d00c0d00704101c141c1080041c04096a13001aa090580341d09070305000b4079000d042001040d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 754121834 1250 754120584 754120637
    0x5040201170a0e070b0f09041505060d020d061505030f04210801031a0615090103020702040603111e182d0a0506030304030f03031a091906091b 63
    0x8603010303040000d441441c0d00241c050f0203c8030102c130400c079190b00150202e4000c80713220412540c0180411101458507400402c10351100000a24409480b02c0108085d5030065804941258000840d050100900c3c4120401020786821380c0103000c42c00303040180184009003003000d48071500e40110b030a101c4146c1071007480250084032445045507070100074000720402d10047d82c03003503001c14601008841c2224520301c9054006e006981c000100079403d102d5402c000c0e0f0301c03410190300b44103102c0107031034521400020798019401d10315406200010404100c51a10000000c54513907040c0249a4a0b02954900c00c2581c15406c020190b07512184c0c041e410041282203400c009183d050321070b04081d10242c0e6409904044030500c00c943d103440a0503500e12913440014a00c2400c2000000445d1196101781c8100d460074200307814002140c800501c22031400d544500200c80d940004419140707280c80740380014110340038184502102c40000080c030070790b030501090030300030100c0e004680c220003111070401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 754123084 1250 754121834 754121867
    0x10f05030411031e15090601150c0c0b1902070302011224140a1a12040303020c0d0519020105040f0b070c1406010e090c03100b030f0106150905010504030b0a05040201 73
    0x202422545404c0300040e8140c0b01210107806a1207031000174201c40ca845500c2958080000d060340c1e440d2004542080320907119910400010545440c0080c26a04944000f0402c2c000d10340d0b00d0315007050603160038048810b00c5600b558001a82000180d81160708403c21042070200000e54150b0402c6001160714180514075a01246510101e03003a2a0f01c0127a4440070401da03203288601d030321034a070004d0400d0120100c1c0c8180400b4414942c4480b900044a64083c0c40707440c0c0541400190152241f5140207035406030042180400c4100c0c96010040010800d0290f0340b00a00c0b05007080d032075201c54444c01100c05002e130304410000821840c0108a04c24410b070f070101018890390340c03400000303031104401c3c01040c1c1000c0c4800c001c2510204005601011841300030082d01040105194410084c002d01c0340e01070301030044c42400315482d0402c2c0b00f40b42c001e200551780140c0c01d10390641c0c010a100d10703a411444c1170000501060011510561800c2d900c84014100003a07580c43c0c07400160741d0603002441020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 754124334 1250 754123084 754123093
    0x5090601170f040b0903120103060c030e15070f0f0923090c090405060105071a100519170a0807110d0c14010801050f01020309090402120d0815040902010f0503041103 73
    0x1e80102d4461049200d14052031007040c071031301d03031840c015100c1c460800e14580042c280001400840c0c1079a01c2000c1488403810300051031001c80d2100d50a142c0c803003507e099074905d00750800c500590002041092a40c0503e805060030386000b0010700070203610302400c0103050010030701e2013381704000f504c14102d08008202080602e40464129002d5000741003403401282014042170055000c3c809603840c02d0351203032000086800f0300c2080014550024070400340104c181700c3c00541507c0303800640c40c4204c0085602c2008904051147c0c0041d070442c0961901ca40c41074402e0f0011602020548032650352005a0500200001000076150920010b015140401c5450b0001d4046803030385084036171038400e0703e89440c2aa41c92041101c018038800c10f003805030300200204800c5140007031401d1b0703105100401c051504c2131200007980c5014040c2810401150281080c4003da110700c02c1c04114081086600f800142c4907540000d04550000f2008000d01101001003400c0240110210b0b2014a000d01110f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 754125584 1250 754124334 754124341
    0xc0109030305091519140406051c0603140a020108060f03070b13091a1002150a090311030a03091e0210030b011b03050d061a0f0c10021818040506010509060117 70
    0x103070650070004408404282c00340d02c101c2070101b0050a40302210110740b906401d0104a003c03101e1026160111600640d58603c0c01000181c0b102d4400030030540004001d111050040c0b0000d803000c5400b400441c401d120300c440740ca40e140c1d00000d042041c0e98200e0b40c0c3ca030300c41c035011440b6200b00039242c00124086090600d900f20300e03004a000161244001c503110840e80c007129000f0790305e5030b1203a0300c0c0010007143c000c005401010103410002207144607141c1240e00c12060f00c4501c0c1103130001080e0200103601c840e0305109100400c84a1300c003001e0b001071185030701d92141d8000f51207034103085c0c511801d058441010500c0c076030086031500072604034805030010300c410a160042140e40400343e041005803618030042041c4c0c80404006400110b2146201e1034036800c19140043d0390042c041c03440a600c02c0c907844164481407800503101c1c040300800c4540c180c220b07201c100b04070814808108889500c0b814104000f01e2400101581143c03001d9440140c00c2d121480120745999288103081003144040d41032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 754126834 1250 754125584 754125607
    0x103020f12060f10091a01030e07030204050c28020a0f1707050f010f020412110d140d0f110303131407170c0312030a1109130b01030e0c01090303050915 67
    0x310780b00d49800e4120300d08140e105e400f15002c42e056203a4412468164030303402041c550080c1e0001904005030011603044a40d20340c00641910720846000c5d0501d0004104608a00401d518103440310b0901219a00c0311074407100001e40c1d0b2003000f40301404100150f1403810034450b80b0305515581d0fa6400c0c548036914801411300c0d6550704244418000c5a40c6170004440001d2510b20903242a43d440240ca075131805c406032504c40004120020503a07010700d035a90448002407941c0f0080d0850303c80807024040c50050700d00007030a0700c03003054882814400074034000c4001c0c540c08012268407900c0c4070740300603120303130281412400302c050f00c2e0001115100300000880c0d880610b1091030100c44100c4111555001f0140a15845480302c00b42050501c80910201351921800e8000350041d0f1b82800044c1d0501090303400280380008204111121695155810285942d0601901180004c1d0400074100c100030a4002818a103642c40301400b00500813406030043e54504441380841200584600c1c3c0356031300e500c0d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 754128084 1250 754126834 754126861
    0x80f120403020727050a0e0706020a11030d090902070f051b09011223100c0309060b0d02100e21010b0916140a02150703050106260103020f1206 63
    0x141a005482071040000da1300100a21200f035010002c0302c040e12280c40c43e8142c2001d494050801c1005985030382814020440802500c00100200d9009200740040c0b4141000c40c00c241d00902d900941042e940c0c2105a42c11415503802c641a072440103a8510346d90800107201410303808018464001d1002c01448103822400540d025141110780010310390385c60f42c0d00d1040700c1d585100100310050409541c16a59410f1000c0c14440402105541c680d1403141d034110219000c5210000c04242d4801c41c000034003009129402507808181d5140c281c204d0301d17800040c0e070000304042810410903825021320960712403000b00010741003800b180002818a0940326400380403428001d5000e180000d00042100f0418101408001d42f103403282c103030740d2000d030500030040d500031150081540302d501280e0008001c996103e03841507056640018142d410400020406000c0500102d2215109100001910b100c683c2250440382d049a640030700c03c240d00d0108481056281c00003c07075008000410070082d2101c030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 754129334 1250 754128084 754128091
    0x30b0114071e08030a0e0606091317040f0e0105010c03020a021201060302090a0209010f1b200d0525060503010b130e0702060108010f050403021c0306181506050306060a0c080f12 78
    0x5006202c0c550346174806d10f80d40c50b412180213a02062410100300e00c185441d4032032130b40a000e005090480c2103840800c3d8440d034030540c0a4044012030b0901041202c1c208214540508030902e06440fa1014540b1f00035134640c41103401900c281c441c0a8a00707030b0070000354000401903901606141d00f40c645030b00144000c3d00070008131408100f4010100280a00c10040a0795a000401c5643c0f07030b600707603922082440c6440003060030140f10700c1c1e44091060345e500c0c03c0e69003009100d1001454401c512071181d030610b6080d02128005804003660a00c80b464115043d2415100c0c50b80d0364540f1000e081034403602c1c00c10154010f00c241d41d809030a0014241e4041502c5060742d100030024400c0c84042e1410508407882254003500680000110300c10aa20120b660303808070f01c8615021805039140da1100300441e036825846268250740360300c41001450310301d03548002041309003002c42c19441d01501081c6513114105c0d24404000b0f0b1594200300708800141030f0b07081c110f0700c003900c1500c981c0c15404e06440c0302e400b1b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 754130584 1250 754129334 754129351
    0x160801060f1e0b0702060d111908100317070606060f03141e0a0b0303030703091b0812071502121807060906030c030e0d020c0907030b0114071e0803 65
    0x7071000700d0200101c0c591402c108103540714040c4000e15122001400c1d800c1040203d91042c010005080501c00600941c08a040c611440550719210f4514404c5070f000f03107003860030074441000304214224040304802e500700c940042c8403502507002e00c201c0004621450384001e02c3c00d0320b0241d002c584503901c903070500030303142581d1402c1041040c00c2290b4042040100e612341d500e00700d001d5025120f1981d0a0707020350012244000480c2000140300001d086402c00c860250000e580c5102410a00c582040768905031a640d0b9080c9c1c4055080602c0740351240d86442c0117215000b00000e402c810041d004004243ca80700c406021920b41c0368000352000548010f407640c401c00c00300f03134000000855010400d4012292940c40d654400f501e012420f402078284228000c0606603298001c20300b0043c00c0c0082c200c120001c1c1c1c0a498024040c0d070800010781000740c8007000700351030600001410303600310f145c030800d007000550440c3d210311582c82c020806104800380c01d42c035900401000340405c0031130005140034003d203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 754131834 1250 754130584 754130609
    0x603020a0210061511011d01020306030d050c2d070f06080a0212010e0c0706060f050910030f03050723010504020f0105070c0e040602040b0309060405060a0b1f0216080106 75
    0x850b88414180c0307a09024840010070604089103030a4007480840204c500003e0000c200007803003900d107000408881d100c0d5011a5000000c010840c40d044c041c206101134241016414041d001c5201640c0b80c088000d0f0700b0045c01c0c000d101b0140110b0b902100c00313a20341c0c074004484002c1d440740f000c440a05030398803400000c00c60807030100d01651214000e440c0400145d01314810340c1ea03c3c1007031031061054080d00a441080f4100300340404242107001e03101c0980100390450a09030314020a00600354030051600b811641189824000605541c0f100019550980340007921018941000a5403030343c030b00700d00400b60700003005c1d203019400107402447c4a075008076403d601000e05140151071602c10500010509400140140f1074100c86126554210b03000fa000103081c5620b0305580e85060340140e414841941c0b00c2000c02c400c0107010040243e01411091b420302c0341d5091a00410040c2d0070b0b4036240000200c41411120005200304018001d800a104100c16140c0e6a0f6207154000c0c1194021002000351 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 754133084 1250 754131834 754131853
    0x5010207060e0907180b070605060901050a0e04140c04020a0215010801050c0417010e030a0c0605060d0209132f0a08010b0105161a04060e1011030a150503070603020a02 74
    0x29040890309140050696616a40c41050807100c0d9006444140e05c02d01901002040780402d410281c0410b61040d50b000405040103800c224038440160310032841009940003e005006e03041d042d803074001703a05c0307540a0040c482c0075507a40e007059101403c0740d41280c800314041b0202d40d4000b8054a03007c180c48094010b036600c4004140c01c4c1c0b0800c03944802c0d0f96100f00700030007040c8000720840d0000c01030f071000000d4000c0c0b80c040c4a4210340c04000e94100045000361040140300444c810a50402001c4031022003525003540455010b0a000300201500d0f0610650304c01880a4540030381072884809141165030070660589406441c1c00500d400d00896100b200800e10120506c00c1c1d0500c0700c0140c5509013080b650181c1441d080913a10411100f9800103908095000e22140035640100e114501c0460f08038002c441c5607141806501c2480052070070502c18010369031141c000c0340d41110440c038000c40e0b01000c4100303424041919500c60b54262080690000311203506070b01510302c003952642602d09000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 754134334 1250 754133084 754133087
    0x4060b01020f030a1b06091110020c03190f23160e1609171c030203061503061507080706051303140a09090e0d030609060605030c0a02120708040501020706 68
    0x6084000c140107540c010405041113074004d01030415503400b0a103001c1a4031a69948400513101000300c01c442d202129106d540d4a468a10088401200c0398401420354000241c00030f81e6920340c0c030b16110200c50891200005026004009104050700110f114040d0240841100c00404110215103035038000d20403580142900c00f01d030501100c2d04480c0d91178241c0c0320b025000351203403400c0d1010414031800100019490101d010352001007203c80010b81400b1001c600d007409144494888031040620410800610340d5035110386221341440824000c1d201d58602c0c0125890714401d00c4a60814480030030a81c0400c541c02000b802114800c00c006d0001da10b03440c118080c484110100100030a9851038107416031140d0001a1810046907e48501002c0e03071242c00b4001c4840c01e404140c0960000103441207480d426028850082c840207400b000741914054008290340800b40540c101e024000a4a6019510800103075182420440c080c50383c0f036003285419806a40180f0459015004d08580040e10a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 754135584 1250 754134334 754134343
    0xb0705070507050f060705060106170721050603011e0204090b1002060a0c17090604031103180424120510051302010806030a210201050c07030509011107120b04060b0102 74
    0x1d51050041a030541041e0400910798041c0038a02d422143c00d010b560041001001200c1c020300b07582c1c8506030160040746484204442c024248030a0050141c8007020f5107010f101c045100c0040c0c5000040c1c5d54807403000090140200c910003020250407086260300700203241d0300070000c44440f4001084081108024400d641c8200041e80d009030300840d0000309075800640110388007940754508030071078069681ca0740e00407100030b89000716941e01110400c010950002c58204c20b411b0108003e50400300c00111020303000c000d484016000e6500c07211710f01d0380030620481c40c6410b048050314030a207103070711030b0100c43d1002d601103001d584912a04e0300180355440740d032140c1e03070207421a14034140603c1d8030354005450001c40501170940621400c8d1122000c035810081042d0740102a4449041200a80310020300703591010f813490031502802c01013900080e03080030450b00d440360300313007000810204c42c4004a0b08001a035803002c42005220910b174000c02c1000c084003445103110700420032144c1c401000484e902c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 754136690 1106 754135584 754135597
    0x807080405030613170a02070b0f1c0e0703080f0705070e0702010f050f0f04081e040e091b0f0d0501090501020a0207150504061b140a0b0705 62
    0x20b4034041c09603581041c0304480b110101d00c481d8454190030f407101000340807028800103880110500038010400107102c0d00c207a031500d404005440740d40d5071380205241c90310f8401000840714040c2c907510800c00710000b00001002c1060641d03550041580c411200d02c102071005002e404d000030004c001403409031920b84280c1c02c05041c01d0714083c0c2503480b444510440e841c145800c00981c5081c409609611020040c04c1d0345603a1164104600d142c0700b40300001e404c100c40c2000200110242e600140200e03620b96542c2c0519990b02c640070380e1a05840c026001c4001e04a0114a02d24a4490340f01502d8050007010384288402c0c944d02c0c035013120b48115088078280d4000c1444d80c112501400510010007448004166035050410020108c0c455030081e4030600544026440450720040100058254046100e00181ca1503941c40e943c0d40400b6070741140e0800a1030009000d0a00c504152a00d = true := by decide +kernel

theorem cover : BRFrame.Cov 753956834 754136690 := by
  have h0 := BRFrame.cov_init 753956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 753956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 753956834 ≤ n) (h2 : n < 754136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
