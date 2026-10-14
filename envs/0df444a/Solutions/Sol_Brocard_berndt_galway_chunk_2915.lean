-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2915
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:07:21.942888+00:00
-- url     : https://prove2.me/submissions/9e7d5c96-bb55-49f8-b3ba-3d8638d45454

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 524100719 ≤ n < 524280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 524101969 1250 524100719 524100743
    0x90506010c080307180b090a050105070503030f100807080304151b17040308070f2a1a0408010f05010f0f030b0103020609120307110a0504050c19030b0d05011b050403 73
    0x2e40d41801640c1c4c0510390b441c0540000844005818070b204041d80300c2041c1c0d6200007400c3e986800c0008000024050070f080880c5840c0c02c990303a140d6240b02c01080d141000003424003090540c1c10f01003801c001484123800301c0d070b1000d44480c0940c0d1a5031240c1f01e62041140001010304040b401100031340e1a151103020140d014401c581c54513003084a148a078860000004c200c0480016511000792000a0203080618000400c03480d00c100d0040f5510480032500c00c2001802c40001e210015400035124898400c10710300341c11001400c56401980c012503215424129201446102d0394001c82c12203103603c6141264079a103d2030f018034804140400340403412190300500c0982000701c0100240200903281d0003c0c400551511f82c1150400602141d100460f0145102d003840e0401881008c0c0004890412850030540310003016880351081c008418424110701c401214060f03444641000307405041c0e094078040c0c07890080e0007802982c40707a180040710b51011103000c43c42039080d2401d413a4004105011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 524103219 1250 524101969 524101973
    0xe0f2404030512151305090111040f27180c05011e0509030c091e0609070f0f0201200726070221010609020903010c0e100f020c0d0302060907090506010c 67
    0x1c40c0201203c8103442d8007005500545c4031001012000c0220340000601070074030250b010300b5641480241d46d1549400c1c84280101c0d289001044212417003481d0080502c1c00d2846a54071903a403460f02030007858500391441010381d00c00390120507881c1c81400c404102d191183c0c019a01c8016158100d0012060805052207a5008be0010702a038031000b4110303a55501301c0000100c18180884c0c1140d00c554101c2001500003110160759a08450201d40310409490459001003540c02c2c0384210004000101d0617020403a0300039032000c015070910800c28100c0d0940c07054040203650141d281290800303500907641a001c1140848034100c00e03c11000c0b249080350303c1e020400711103c003900341c0804140e00340c0c1c000b0103000c0c01d1081c01c00401e41e51001507221002d4004050840b940d0403030341024440c1c46101d00c800c4d5a01e6601d507410030007081c00e055903c1d00242074200e150103610354055410600c900484001d26400090f9030f48596958011101000c4d112400102501c078161070242c0440e03845911000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 524104469 1250 524103219 524103247
    0x61425030c0c0204050103050c01020d030902010f080a20031602030403020f0f18070306140d0209060103050a18201806010c1a0406060501080108032a010e0f24040305 73
    0x40032a464078001c0b14805440d00020120341c02a8401c8645a001e0006c451455030180300d254044901d0341001c11a6001c680c00191100c0560400701080040c601d00050612485078001e540180c00040d0252124640103c44d001c7e503030041d101c2c0d0050441421465860610010031641925406418a07442a048000303000780c12000800180d40710751280d8100d010703001d0075004580310f0001c0d1b55000c584145001c410b0358400210440711401001d940c0d83d00760141c1c5036100d810760018020300c3c000440d540d0b00000e03030008041844814500d84c2e02c2c400e020701404070520100004014000320b030a804001038003040810000d0360b0002c004d5145ea4000102e41d58014281c2c0b401c403e00900c0c940000c000e03140c4a0a003004401c4504840d5180e4500c4240304035613108480c02e001d0102640110700e002c032043c90b080d01601e01d80007a48c17a03c40141c00c204042900a4021104609d52a0704071200c440ca403140c100c0d1200c2a036a06402103d940c2010080e0400c0600180d500954064562610780301501c0c0f6a0780d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 524105719 1250 524104469 524104481
    0x12020d0f080c0a0501150b0403030e0111120409050a050603010c08010905060d0c060c03080c030105030307020f151c05240402130b0c0a0b0a06060e060705070b0706142503 75
    0x6901d910042c44466501c1c801404032803e160f204a000198005034591800003178440c54102c45030140c0240028400a0303044816440072150909101410707407103125000f07240039108400046264404200042d9090303964200500600846c0070500242c6d0310031003132500b2030b00b5542c40e0f1800111280010840040c5690003039030845005012001003221548a641d040070565001c20001410060f444041c9540625842d400c540c00ca4036407880d41d42b415000030303901d018801c4007910032040d91004142e19960304464514000784003000c0e607251000c986034142842030440e103001c040d50801000400050701c184403003403001d40c3c1a00710000908280d0900009410107010680d80007242078001c030b10034200001a05800c26400d00403d111400703490308083c070303500c050003101203142000410b216035074008188515a0409451040e142c04540c14400e01e000e4203030784003001d202d074009403407014080b13903801c0400c00c01006c4841240c2d40d145e954075140f01c881c400103440d0420f400004040c640314880e401c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 524106969 1250 524105719 524105723
    0x20a0c02011d190306050a06060e100302071505090f0307080f07061424090c040611070e101a0313020906030123040201020105070503090d0e13090c03060612020d0f 72
    0x141480102c004003044003031842c2d0000305400c0003112410801c204260080d60361082900c6014460340f03261030b40103410000030403001031042c15442c000d2900ba40c401d40c140e980c05a041461450400d0b69001d02c500103150540c1d0003102c5001c0c8141c94521000000200d8980707030750007081030340360500342c00e5514403035002510f084504c1c5443d054060b45842c03603280c085001d1803d04a01c3c00c484400c50a10345655646800d541b0702030740c08082000380740304ca403506540c1240c0e02d9060a8401044844c00d1900307004141d00042e680003019001c1c040c52810403881001640c41100c900810000f00281c0d0348018001103802e8010140319194070030040c01c10b080c110780c000d24042d0004c00d004411011800911241340c11480761030030900c04002c15583d0901400381c1148607070504a1450500344c0325940c9071101b8112840070710008034816603c0c2d4648252a24803030710281010407004c800c511f4070384403c18041c40107548890170480302050605900001c0404680d00600b020300000301540c40000c81c02000d081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 524108219 1250 524106969 524107007
    0x6010e041520031e0a09050304090e01020403020d14100501120f03030b03070902120c0f0d0510030212100b01051318060b0c07060f020a021c230c13020a0c0201 70
    0x1000b46440750500558016845244410f64010459404003031150b80141604501e50518910740c2c003258001c02100c1c10390303076a514041286003000c441075029200d00c1d88025089801000d00c03d0502155102441007149030b00142c2d1801082110b1107000e850382070241669070100008040000703244803900c0007115109080115229089100103400c0c082c2c254041c042c0700340c000440c001c01041d081d9556600c00e0600c500315050050501d403410050140401c1d1082d200d945a01207000030805a510300001e40c0d001740b4a01c103c0074040009911511041c000501c0c450806041c8005907004805480d01503200c2201249442c3c60031b01d40c0001150000c1049004503500c1030040b0302c604500000b049804400e030010080d05190440081c0a0480303146c0340300441d0420311081c030050f503a104107082c446141107170325004052603080000501c541242125802104100c4040c2c00450100703015036800c0046546880d00d181c0106030405900c5809110000500071841ca03400640c050390a81c4044498419 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 524109469 1250 524108219 524108261
    0xb01080403301104051507032a020301020403060c0219031e05160507030309080a0803040b040206121006030c020f0a0b22061a060910030506010210061706010e0415 72
    0x744041240d10000454016500c0004c09005509041c601c0c8175091092404951809025850007440d0f10036161480c4450841000d852610050514080151030340050085596a84d6450310500900140a07440054060b105540c11150f42d1042600745644d0107407201001500340c03c240c0b01000c41644141428044d0034850842c41d021030341e020341e089e01d11440041071b4190441c14080c01204042c1d10000c02d560080264000007071924007030301e40090344009088201d486c0c61001131f440340030f0040411904070700401082408094498007000b150010389040041000611003280c45000082003046181e12100070780001515074001c0591002c040182030715072180300c00406400307101c03041c001d070391803034803071295592804040c241203603914405c075411482c080d03d600106544540d018030704018165500c1c002040da90081c44000c100c0401c0c20300810129407500421070300d0a0000170350021601c5610000b20300042c80c0c01c0818010f0341c02c02e40010380c40e4098045440a807204454001a00d08191 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 524110719 1250 524109469 524109557
    0x5030f0a140106031a0f0c03010f050402090105040b030f0406051b16030207032a0509060315060f040e011a011107090507140c0d0f020309010914151c0b01080403 71
    0x80c10700c038041c0c042640054211b050a090b140004a0042c1085184e80c0d4104010442c110300f8014150840301c0540300940c40b05101401622913005561250b55400000420402c2113400c01e03020910451080314200415201c0c18001c8403041e5250040c3c8068450410240080c12000c80e48003440c58442d104030b4041c0354032592691800b03200b0502040e40d10854880515000303070900e5009000c1c080a0703410001d1450902c0009607502107014a1500b1040610007188507601d4200f800d00305548003501c02d0051180c10004a402003222806281782001c090100680030f41c4108034469000c400c4000412249040c339242c8402402e01800c010305204003083c0007c90341240c0c030064040c03400704034060496105420005458030b0342c1800c800045410410104180da81c01094031020358201c00c40080151500c8000b1622800f05101004400540400c59001356090119001c3c0303210200ca0f024800c60500c200155400181a00d00402048001140c6134504210000040c92102c0101e21080b91030400303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 524111969 1250 524110719 524110733
    0x509060d0603030216080105040209040210020f0d050715020703080f0a1806050f091c0f03060801110c150402060708030c07020d1103150103051903180803040f05030f0a14010603 78
    0x6510840260700001c5410705c0440e00221264024548a4000e10091802d64001203403010000d2000f44100301d0b08801e860b003140b003040000d010302e444008a5808101e80d2401070205d0708040000c03209800082e00010410074207000703480104e03501d51a043e1903515100c003031b0790105074003c05c8542c5003036540481e442480c5401c1e0040784541e00074100050320382000140c0e80751705000206600d04640c0165014403128000c0d9002c2110420586000c0f5410343d403c0340110302400d204c1c0d100f41c0703003582801540154005040700070404102c0040c00c9822005084018021106084170007a510000c248402000710f0440c07401144e0003800004180e00e002d01c81d60002e100c20003c0902034445440103030840e915404c04018601d03005140410704070180d072655507126620002d070040d0010318035070318144104160003091101c410802c20446e02c0c40c119210104036030381c4d070410b01c180704120400400000c0d05041c0841c42030f0100316030790302078802d900c0541c541c41480456404048015980c5243c000045140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 524113219 1250 524111969 524111981
    0xf12050403180b030402030c06090f121501170c0f040b0405040f020a0b13030f0201230d0501090903020312190905060603100507080f04050703060c0e15040f03030509060d 75
    0x801d848408002d88109418107140c0d0b125004403800d01010000d201c09640d0000300e1035100c00702116029610041d07040400c4840200050717007904003c18a042c0e009240c4e01081384850441c0c1004d80f01005c0e079a8000c10156040c042c0000f9659401440d8004254100105800f0144c80040c0002c6007884560000c10b003100c0e01110f00303881c00040212020304610304111a031004200440c3c0300c074202070354180c80c0c80c50916180f2000f01504000b4614900b107901611f241503900c00b80e00560b41c0c0e004111810b42140e5801313800c1140110786040000310b6041e030203100b07114545030117078029070420703610300910801c0c0340018000d0400f001054900d0030a2a106000d9101182e01c0f54002c0c1c401f606014080c03600e48811124903042c518202401c001d610f07544891040d9106140202c02c0c07d2607122400c100307040c40310681003d89043d00380002442c9140c1c000078134400c03d0005036000180500701c0c030a410340c1c40c000e5020307103d00c5659100c010000310380f243e0f019120180c0300501c0245004410b078054011685 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 524114469 1250 524113219 524113223
    0x140304050f12090f06030a0e060906100b0406050f1815040f0b030405030a080a0f140103021c051b06041206150b160609061b080a0c020c03030301060f120504 69
    0x4030036601c04080e084140705910682182040190400c8580400a020b40040a0001c1e008040c0480003800100645e0068060003070500141c0380c050070543c1c02952504d40480d08583c2e02540500005880c020398411107045800b150307100350900d4681c038182000b42c1d025030707004c80a91101e1041c8a03055503c1c8510a000c1c0078800c0c103516560b5107026400306040b40a6403012107140401e00c100800700710040b045402c0d00000e85050300d61075070798506210040c4000c550800486241001c0c850791000c05c01d0320f150699000300d41146501d00c5402c06403421000c0311000030b11075041103912441c19503031001000380501d4010100d0382030a1b15441d03404c0c204c02c6031000942d429078551403542502d03414200740c4805400400041840c000400c40c11032090384078030340005e00040d0f8620f03059003070260641c031a8054603071602c90781014100264004088810070b0300c0710040145041071000c01030780001280b15100e2000b502030b40c25607203404d0781516420850303102102801001d036060000c0f846182719043c8198 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 524115719 1250 524114469 524114473
    0x303061c022107060f030e070317210105010905041a01080603030c0303090312070f02030a0503070c080c0d0210061a130e01060804050c090c1c0f1d1c050409090314030405 75
    0x10380b83c08801080201000d0210b0141450300004000c5107601080d04010342b41c00c00400180c28908904205841c85040c4000420081d07000701c013244400c030f02400074100c805c01d81e200c480703071600d4900300001c0340c0b0280c2100321429041078080c400c030750040e00c000e0384c400710041c19207040c443d0469a01c0d040d41d204840c400000d0700001b0301500c001c000d8442c83c40d003108651078065445030b02008040c1d600c0c4101e21858060200c01710005219611445400079455440440642c480d11884400d507600c1c6039000481025001d00c640c0012203041c0351041e0b6003120241690b240c400142e601c1e030300b00164004202d5141d1004105030200e90341a50000d024004d08040c0d4851100e8502070030300360304012080356100d128150040520503028400015901011041114014020326261a0304001c1060200201400381420103182c03103034403a4862480c82c0e480a105540f0307504500c0300c200d0001c1c00d901c203482c00481d07001e00c400c0c0204441640a590030b07510070b0405103c4400c82c0041e29410b60000c071011121a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 524116969 1250 524115719 524115733
    0x1d01031b020106091a181306020f070209150d020103090602090d0b04050c18071d10030b090a0b06040303110c1c031205190207110a03230303061c0221 66
    0x54481403298003100c0b07190001c5203207041980800203582803410000d0186d5680302c400480e151414072840f0340c01103a401581155114500e40c050340503900803d17030a905c41e0103d0b40000d41001180b1207070030031150000704010704855141e401900104042c40c010350301941d0070b00071600c0c651520381104400c04e00540203050245010b142092420303002c940524000c9079040c19803071812480020642d002001405d2400341825a1554981070303800103a0100c0d0302100c40e0008a85054055100280041d0141d4540c805035031811310401c00d482c07a1104c4039030406820882000404e01c12205902140ca803001078030301d150b014000140c20701040c071035034088070324161000f102010b0300004001c1d42c420035880144003501e4210346885c88050700344a41c034a15500000c002c2d04011450340c0c1d40552400007080000c146480e400d0001c5000d0304200f03048541950303000541c50524000054a102d01c0008042082900c0750315103046441c56881e208903004206840c070141001d40d0712034003003d2080c004000f4248 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 524118219 1250 524116969 524116979
    0x110a03050109051c080f130f120306050f0f09040305040806100e09010c02060115021f050709080f100b060d18030e0f1c03020f060c0a0e0405071d01031b020106 70
    0x100116000541c107401c6103440b103403680350b0300300c285d8a40c0009658003244d5103a650b10011626200e01d00002001805016042ea04100c0700c101a104c4035a9280e408201b00c5450f00244000810301d10035456100040c000454214030384804410b5109120f858020704107503842045034a050815030769424850a101c0c4280301003510003005d0303688029600d009110056155030080e44034a4103010700c02c210400c0b140e40d13100752070080000034804010300f201419200320001800c0020203042c0d840000003402c0d0100003e229000040c204680c01c1960060480130031000d02031001448a8011250130100900c141680c4102e00e1203108194802852a8080d6407140e18001f4803410012039440e2250200321440e0020380ca888545030410886e01c1451221025182410fa283c80c40d08903a2040c58416502007104500018000e8206400703280c580c003c000070410f040200341d8400f02c0303116001a400a00074110705500140c2c200c50380406060015504900d0350904d10b80e155021024000360f915400e003002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 524119469 1250 524118219 524118223
    0x30816180e090d0507261c0e0607140d0c02011805031206190614040302090c0408060f010621060e07170f070c0b040c12030f0e01021b040207110a0305010905 69
    0x2110400380c1c0b03000d52604006a541136800110f15646d03d44179149480403280590180040380e1003203110441c80385400c401d65188030301400240c40c0020540c007400000c1032070f01b8002c00308221640e0309425080e00389582507142d00000c101320349250302150340310103000c00762080030209001450300907009166160810b2400c80d0b003c03100034100d18080e005090215843e12600d20405082d14018078243e40301c816004a16007885c045c0da000a54081449410700c0219036801c001081198540d0003510b291f40c0e902c2203002c035155024406da03804520007400620001380d2024030440002d08003040013541c961103120406001c8803c507840004110010084607419507016038441d03125400300040c00321803038800e00080100c1c018201c0240000c1c4401c0205041121142c034020252081c80c82c6180e0200403400c000b8441a04c4000305000302c1c1c41403007403500301d5101088510003c814a00440b10f0040f2001c18003000b0360202c1811341d2100c000041d850599035803090f035070b4010b60060002040421250500380c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 524120719 1250 524119469 524119483
    0x20a060f17160206091614040603021c0b0a0c02060105062116090f12020603040c1802070b011d0103030815030304090c030e07060914010302190305150a03030816180e09 74
    0x100c029400412070006186250000000347c6d01c00c90000003200d25048007140c00f4004542000f07622103c5401c4441a0550308403503114003d00840111007a602c0b4000c035502290b568091000060f000303540184001c0c246403008040c003828a111810307a244541d401c40001c0703a420b444c0c0c40f124000603813107110b41c00d5110351218003520151486205192030280a6040301190325030080c020407011000405014140e10f40d44010580003020046050009e840c002c0294009030f01194803c8006c80003041d418040d24080b500750340d405101c0400d030390031510305480b50343c4020310303a00e9860064907242d1003a8500380003500003072651100100300500e840602a0030f89540009801c981d80c4400f1042103030550100c6a00b04540c12222240102040e100048000c0d10030b007052034241403090040d0b00201d55242d4081031156000004d0f0400e115910400c11a102c03816200103070000300c00402140b40c680c1d140c60040200318890a007006059402122104040f039103030302103202c000d401000c1141801060042d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 524121969 1250 524120719 524120731
    0x20d03020f03161103071506270905010204080115050916020d0e03070f0308191e05091f02061b0f070f0201030b090c04031e020a060f17160206 63
    0x6500302081e0148200d030600000346601003024003900d940400740c0c00741c8500151010745000b41c0340d03607103070a08000900807518003030001e0451410000148160400300310344103031280140c10100c1045142c01c2d0f0320162420010a54207550308000018a454092143c500350401c138000484c0524501402c00400400c020036841500114001c0002003580c04070f9240055403040c14012907003206100420318002070b41d004003500e044102008010720513030070301030708100407102c9400c0d0a800403d442201c200724018000ca608012070b00100a140f030090000d4415420003811402d41d2000c200c0d840401006610750102c09a0003890512079005038a0211001541643c00b510345482201c00481a5034810341202500c6600300c40089411a846030700031000703c010041015950f41000c10250b03110390b00501c402c8510306140c810202c480907044044a2002c0d13002450019a14941041980e130400c005615000b00203041c0b03182207040c0c00c0c40c1c118600464842c140c150141c0c1102c50302030f2400d2005000703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 524123219 1250 524121969 524121971
    0x1404060908010e0601121217010f14040c020615040212340c12050c07060224040206120711060901020409140f07050f0d0f020307090e090d0503070c060c0c03020d03 72
    0x50206100b034020030200b484c7d2081c82d007110401c0d1228101c81c1e0f4080111106e120100d0071000090952070b822049081c0c600702c002d040e002e05400801c1008951101c006038026030400c90000341c60084c6d9a1001000c0f06019202610b0401c5400c4c0700741110302c048409203189404a006180c2d80303d00c140c0010682c141710715040e810301c8501c01c0003a15208050400401590b88682d001071014070800a6540181668080710b0340d40c4d480e400003039110001e0119051100440301c0c0c608580c01e8603c0d08580c0216006081680b0b0400d2401e1101c14500005003900c045c015014002140c2c144208003e40c0701c2d20b800c2000584550510800c41e00350f50303902240f601d0405008040c003540308030344405c040c1c006040707040c0035540e4030b0010701015a1303000d1180180310261030080c1c82c810380310407070700194464010369450301d0f61561200713103e980000f02919405661391200b140c01442c1c9000744000c5402451508041c09081c80783c2d036490065903200c3c40e101c800900780b1035007801055010440807082d09280d0134 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 524124469 1250 524123219 524123221
    0x3060803040f09020a09050d150f1503080c071206091a091e07050a090f060b041d0411060c010903030b01021c031812050c1b09040f02011404060908010e06 68
    0xc0441090200e400b0701c20043c0c0d800581c480750075000d100894003c01c2c0103030484c131840350141004001c548004012003440360424803111800d80740351042031800481816400480d0f030854440d0b00702904134032026040342c41400b1010507031a2101d004550303103512030300010840540a04e080303030803001003600340c26081000a003400862500402d4101c00011010b008180d5010003080d03035480d00c405a030166402000395140418140c0b1690480350302a11003140034403055980d44503980040c4621f1051401d28400318079406000d1f03008030b42841e0014080c462841d24240700200041e8140c8c0841d003114410ba554410800805415010700420303400240050711380c01520155030150706110103a0380d130400d99540b9003011440c910480b810305c00c0d90000320004d19992001e0b00503083c2da21240f255070b01c03031044c0304040e00045800d2442d0f403200480640b60740d80f039440350303914014103000f409070490520502000c2c44441900c5400540000c1c00295202c442140c0381544190031070391420001d00103600250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 524125719 1250 524124469 524124479
    0x203070c081c020a0f0e1915050903030d092603010b13031703070809030a05180402090d0b270d0c080705100c110105090619090503030f070306080304 66
    0x9902801030304512031542d105182c0e1091810455541c0058030800e1020603114181a0b11000040902c0301540301c40550980780700802c1511403541000d8050702e002c8800a00c081c03032820700844030442c0a424046d0601407400c000038116081a080e80c0b482d243d5a0b04210240159080324503d04405104d111103203100524183e07440b44014000c0c82e0088100207901c1104102c000c10345c1d001507400c040324091a0f9900c103585889a8001d9a800f000600c5d01004541c03d203038040f048580f0704a40303445551400c1654000c03c20503070100307a079680c1d00030703400d02c40981c0d00d40300c1c1e0010250a9200d603448002600e040c412440807101c130034603c0016080040310008415800207195112002c56060414841e0718610340a007080c8280c1302d00a0403805910404040008150400c17000460180ca442e40e124184450345800c1f21021201012030b684030801052111040083d402c2000b00d04410100b9802c0c95034031540c0c40e5a0040d1413800b9207203a500104110180d16114103809442d454028500c2c0c140340ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 524126969 1250 524125719 524125727
    0x30c0f1e171315050c010207110f010207062a02031c02010f0b01090909060b06040305030c0606010c02031b060c0304060503150103150b2503020a06050f010501020d110109170319020307 81
    0x5070281c00a4010f5030380c1441040ca0244054924810105000b59682c1e8034074075144514030301000c511030181ea5610214003640d800840c10800340c4a40740e6515071032107036405542241c0340c001010301072859a400505005030314180800c104070031001a0700e2404000c1400000d00311401d1030088042c9514000c3c003181e40f80c0e840f1329200100c03411120041190700c481d00f001e500a020007400540e00c1500018000100072002c0040d00c070488502060300c40641d601c2006441d001c01b040e13002540f40e00101c031a811005100c6a0030b045004000d0449400c3c0070500003421b10307690250300900045000803007004080511402c0d20074404100380b034203025100381003800c0c0f5440300c42c5000d14050358502040c9194101600c1d20980078011000b0380d411544003260502a40b10001d03004140e8a103410840002c05014141c100c81c0d04840060340100071070301a40c030045400c61620b545a00c4a5503c80c22000042450303490000b00c4018070f504999501e040c08207010310100d04602c1c03c80b40241c01841040141500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 524128219 1250 524126969 524127007
    0x2060604110a080406110a0207030c0b1201120f080d0e070506040806070f030e071805150906040c02150a060f0603050c0901080702011508030406030e0604050a030c0f1e17 75
    0xb450030a280030b601d0300d260039000740c41c0a1003107080c0c101c0c000c90401645a4002111800c13a0b01440c8900b04803503c64601100d50300c00c082a02d0a01c1081c140100000c0c000c560284c2000d500075000134019003180da5500115601087c0120b6515450354465184200c06100c844d0041c042103d50b180b4181c5008121a12400300500410510544110038041c0c24025007000d1008004007041da50101c1d1500c82e4039051015624003c03210501e880c00055012001074108210000001d02500c1d036035465204000c06084041224411801080315103e43ca58011080902a0302d40501c04a0510300b022542d084400d843e43c000010541400c0c11f1124041d074490886200c5072082ca009040c175510048280c0c09051110354a09822540c03030b40c0000c4800d40032000e041614010f41d414051200464000707951820305a80c041c0080e041480b011001a000c1c504181c0424030031650f2003a61501601d80b4021130700c1000280c9a03100301755021900300124001c89070201483d000e101424035041603500b50803184 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 524129469 1250 524128219 524128237
    0x20f0c131806050121051207020a080307030f0809030738010b090f0312030103060c09120302060114030a0c09020703091d06010216210204061e050a050d02010f050d0b041103070206060411 82
    0x81f0010b88a0150b48651410700c0203050450101c90765901103181c010300d402c0809180e040010a543c4c04a00380c014040201d412241e0030501e2244071740c5000d401454070240d181d90000d00c40803503c80c2c40f0540d072000702d60030303000300381c000f0000c1e03201e40d840424001d80c5100c0d070151911a030400c4803000203d62141080e00d0540750001d80001e0311820005007500e0151968106660050420906608145c1e0005e8154140ca100781405040821000c1c1030517966040940e0082000201a0003400791030225806011014044d29150180366959080000c11603103a20180c002a030b200c1c02080700558041041180c4400b4403090225494581100c0e214113001c041146c00300240b003003010320103650b5180c00c07000c06003003014040345003041080d040441180c00e6105140c090b40b03c0c000d00060300d18040e1042c1103a5074044e12403070f68011491400300e17401c1d07102c45182c00920b51703170310100d0b2f5403a00c1d640304404060648250140c0d8030300f00080044e140c240d005180340e120360304101620308501080300075184040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 524130719 1250 524129469 524129503
    0x10302010c06110f12071d01210b061209070f150806031005100503120309030913140a0218041e02090406030f1a07020f0c13180605012105 61
    0xf0003d01104910740b041038149a01810080390449004000c1003905008400ca902c5182c49800c1180888141451100c280350203e8480364100003d20075507003c00040b801d0499001407010301150001c2c0c0543c2003145d0114407012500100410458100410070141c04034410900c0468602200003200a408003200e40801014401003442038504028800f91302400d007100340705a1404100300542c3c4040c0384a040d201344a01750380802e50381c00c100200ca0044240310007640c68401000c040c001461014480c1009056a5030780c0d48e21400700d030500d04c6001d904402e4025a175015035100034170b540314a1b11032584c41a89000903a0800c490050442c1e60070001582015854180003000280104215030001d404a98241006c101f003200400101c1042c6051001c0040d51b900d43c00b800b280d44065030881d2004039030050b4800300e801d26000c0901803840f500e0a80110300b03610407034a50010f480c00c00d00100c46c0c06850302d0041c0204c20080c0910080d49440103a201c0c0d04070358503110107544140e0041c1000307884c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 524131969 1250 524130719 524130731
    0xf060a03060f0b041e0c1b02040506060f0a02010b04050a1a090705090d050d0215011211061902010903020f010902030a0b0402180f09010b0409030507031404090e0c040c08010302010c06 81
    0xc0342040c2c100903c9014001d000304203080515104000008180c0e02c800c0201d4941083d40b008203000e0f00c4031030843c0c0080b4040380d031904582c0e42030100810000d440c1c40e81c402402c0c4203070640d400b06c07580202104543d1341d0020441d85036007424041650405040b1900080c140708404210080d030301c008182e0a40115100da0a47d100c5280130345141c851246090f07008200100710070140280016246003205030b030b90807108141d9009840381040b0b0004e014500c000361500e24500b001c5044916420f108050044c011480c00289a1529000c504452400c8000d81d4485207040306154061050fa00c001144000038004030480b40c4c0080d840d084d8803d80140403104206c003250942d160145255800440c89204003c14105000220700c0100300b00c840c1207041d0300304075022100d0b04250080703143d0541d06841c1e00303040012a59080d00c0200c0da00b4031410102d2410710000895645c103010749040d0392038003005800ca296100c1c06010940d90f00c9100e150501070441d00400050340c2c070030350100c8020b0700101d0001d11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 524133219 1250 524131969 524131991
    0x120f0c15271a1e070e0301150905160f0e0910030b0f0a110a0806040209012309030f010c1e03022703010507080114010c0302120409020307080f060a0306 67
    0x15401030000500d0040108000300d20401550b0741014048a400c6210a034142d50386071540c12034015004903207403c4490910218070740c2d40c01103113510600000180085403480c1202c1030f040800303425070300001c0269251024003e94912100340140301c0382291a00b05c4080602c060040e0042103405d400c0c5019262000000e0082c1c0c440038140340c051a40109910120700303140c807100d03070b15040941c2d40083c414034201d0401a0981c110040344c40e8002d85849070041607441d0010070000b90080780c1824148246032580251803601007400c0900481c1c82c0f12400d417100304801c1407524050b444002ca0000781e1501c606e036116030f6004503171140705100302143c586c1101300079001207000c0e014510662102006050300041c840a02500c03c41821034207500801c11070361800021103c882003845103054952a9101c00001c03540300d410030180d07403406070044404032030035001c044000d075100b1341c000c40f002030703012040c0300f40b45500c1601590000009041030515043c003900003001d040b81e80c03200510780c0d5030780e9001e182 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 524134469 1250 524133219 524133251
    0x8060f010e12031204050d1e02070510110607210b1f0909020f030402010f1e050309070e090c03010b090907091e02070c08010623060309070b07120f0c15 67
    0x41c4c2c0511180a41419007443d1074260764881600e113020004c125502003e105401c40700c1c0c1c0c11801105141e005121151511051044002c140400d07102088607903605061450010401c81d801342c0116600c0781c903191043e2603142c0c85055003c10f034030255402d03d4441121a0740707141d000b15545008004009403107403807913425074919440b5031054140e5400480e000c40d080020030040c5120714002e07294080314441d45602103a03000e07200304000034a012907640d40c180c8541304074041d55100340c00b4422514550307141c0900001e0124110b50b826515408020f095034141401e0094102007042030354102081d040c001c65882d140c1c0f4880c003541700c03255602d803082503412900c4000100305501545045640312103d080c0401070f454140200d2440c2e6007005000100e501ca07043d82c8002402000c003160a5075049001007194607800035140703400e0fa2203030300d00105d44426400010140144201c50000080c03a00d418040c00d1030786225100b800380300b40000c0c1c0f4004505440240c4c0d459240360080010018660200380d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 524135719 1250 524134469 524134477
    0x1103010207021206070e010503010e1329180a02090f27030304020a08060c0706020f070c0605072d0b060a080f010906050f0624070803040f0308060f010e1203 69
    0x182d0303c01048452807504150200c1c9807402008281c0c0c0d0000a020100019100c610080c854903640c0b050040008030030410b85207202c2100c82c4510701c11490802c2000e030300341001c01506440c07442480300a0034030490442d0480000c8840c00035070302501100c030b5240c0005405080040030103030800e5540c0c0c0003c9030b4644c01040e051168000e461810600c2e040c2c41c000750380c1c0ea00100e50803809000e000d500070482900c0013032882d02c107440059841e4608401581c4e000041c0d04405c028450000050004200080c10b8012444c00380843e03568494440c4c1c0c1e2400d001c00c00c4030f400180d40700200c140140007515041c038040e891400c035030440e135215a15111440410156001340c1e004038164043c151005142a206411031801c1e00c0c00b410081c0015140c0444030084d0200555050340c0c0011a0b9492060300e649401950300740702c050794016401c1c03410b15121800140d100321b0b000c41c0e0990000d960141015003107100c0715006141500c038482070342005000642248150039000d44202d89030402000d0701e403000c100301c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 524136969 1250 524135719 524135723
    0xc051f110c010801260604080901112e020c0316051009031b1b03061d0c090f04240906060b130b0d0902120102041d04031710030206070f031202090303071103010207 72
    0x6d4100785094104102c2d00c0c0c000007111400912609440c078145180003900e002c00c4c1044a41160708138000180c16070b50342e0801c3c1e0401481a40900c114400c0c40c2c802d0014048409201c9090b01805e402c0c2e203011401d15850800c811821858501d5400c0881d43c45826404181f1643c1640a561070450034a8524240110381d150001c0b80b06900200c2042001d8101c50f41300941c11400c5285503444e000065241e043c100c0c0000e812150210000c1c82c524020412a80c0083c00744411003800d200b140c0310340b8482403407a00d241e848180c58401440030044288103240c01000c2443d04141080701040c42c00110101510030582582408105000d800c880c03948914842c69000388501003003142004c0090103900584160701001840078100b03010165000d0000344100d03031554444031075400a80844981d202e0180440c0312000d00c180b00440142c030b07204020501c10b805180b000c101103a680c54000d00458195040918540c0180500310301c0c0d40b400002c0d610102d50100328140104400d20111b40240140100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 524138219 1250 524136969 524136973
    0xb0f030c0901140a0e0a0503070803070b270705090f0121020103020c011406090a0513062418050601110d110a0b0c0a02010b01021204060c0c051f110c01080126 70
    0x82c0340d0107541c200220149205c020b4682001d0710365507608154448444d44101521030304104121800103903c400280c0d401341080701e1084a500076049600c0350490340e0796801d28241d102940c24002480c4c800305441d0301c94000594400c2640c1018411150000e0280786400c1d55080000300e103045a000390182c0340c0c103084050007005801c110364404040008191000d80c02000340502003001d4035218080d01c1d109120144107690780440390780d00d400081405119500240007001301c00c503a034a403144581c0d40142000e070015a23900c90310b494010101c8001412140c14403010700c000c01c100400202d14a08080303481d081170100c0500c0a1300030750901c00354480090501c0540000c10400d103003507001401000c030030380c0d000b040550070b40401641e840c1d010340c2c426075400b00140800c101c0342d440b803035004c42d98a2080903103c880030b6607800400c1000700410001200031142401e031850304c60348220590001e13031110000f0000c500104001070300b03085042c010015108400089590000030350f2403036041007194001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 524139469 1250 524138219 524138227
    0x150b01091e1502031e070b060607080c0304120b06030604120309080d06150f1b11010201020c0f070911031608091609140a02090a0605030604090227010b0f030c090114 73
    0x142c003d490340e00c07402004107292484622800101619015212030395404007407107078192110010061240c0240b0740c225204081005002c41e0917006201400c0200450000040c03910141d10b0b20005030701004001d0b40c0241e014104000124881c503d068190401c14100010f488980c0c3c10040860320a0440319404d00d400c02d803001031048681c0724004441c40455440d0101d1000c1e43c081251007101040a2425041c5c081406a010603040c001c4c00c103614005000043c50003582944003800c02c0c07001344d5004002d4026100401030780c000c40c00707203001ca01195001c042c07031480c2021103c100e41e00184440d00c20449501c00151500310100310009014042d45009000c440d41c0f0b0b05d61001030409a0030f01c155107019000030a0380383c0224000d80365610303401000c0d40d55441c10a04111003641000b01640d601c591140401005a2600c41060103c00342c01c0708900251901d4051031145000c0680c03001d540f8000030840500d0b208120801d0321380045081c4c04042c5d80341c0c02c44004944285540d0304c81405443c0000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 524140719 1250 524139469 524139509
    0x60a03020a030c05190602030403030e0a03050123010603060602100f0b03150a060909111203041701020c0d0c03090608040c030c180605010f020a0204050a1d0703150b01091e 76
    0x3c1c0080044440c03c80315071060707001303d010394041042c40d80718580c0940e00521003480060b000d403290790050040600001c050381d03603075101d0720b0944c0c110010301c0c1281c00556000ea11340b075100c80c60403405042541024000d4a240000013507640c1c4035416103030915560f580314103408c1c510a800025001d24010100c80200b101c560000928510554403524018a00b910015608125004d113500381c1d1741050101101d41105024082a00f0b110340144040f40030400c004101c00461031840b401c120b090350001130b101d11030b184a040c03a10100c0311007030041c040c03150801000282e0001d00d14043d00c900349043d6030b40742c9440c504501c0c4600540c1000b46941403ca8020170012040f80000c070680d2242e800c02c0c41003980e04d50041d50307540c0b107248501c00185c125900030710250600e038000d180c22031420140090081c0c2d44048060b007082600241042e6500800790400031311961059400b8410500e000070800d501e1b4180001c1c1c2840e22901c00d074845005062624601c00c11200691001440c1206422085403411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 524141969 1250 524140719 524140733
    0x20d030f020715080106080702100606050c070e060a0b070c05100302220315180f060b090a05010b030703111b012f0904020c0304120b0402010e0315040b060a03020a03 73
    0xe0003280010300c2404000034050503c0e100321400310609848420050342018400c9940700c030004e15040070f603c200342045002080621908008060035074420b9205c50300c0d0341100707013030003401d80c06204210441c2d4284072032566000c4030b2a0442d0b800b1486213030f440500313191420000c10303181d215a6120054246076800d1300e4241d0028104141108010808207040480490183c002404054854207c50202034804003140d03200c1c05402010444044040805039600b0304280d0601c0c030700701c42d403d864240c1d0920320f0130a8902c50f50000b601040030310556050102d064014000204004200b40d26a0350340c005120090003103c001500d40c01041c091071108141c0d041c003811914215500c220005440da885602d02d800810b2048c10040100d02c3c44d001824007000040c3d0000306050a0500080100081c84101c4003595542e0740e114041d941a185040d000141480c1c4100c0d01d101c0c003c2d044800000709490443d032806900c25030014481d22140c80c1e40c804204044c1182d040207401c1521003002100740214 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 524143219 1250 524141969 524141987
    0x90914010218130903121a280812071104060302090a1a03191403190201140601030204050105090d060216140c0109030f03050a052a010606030b01050a0503060d020d03 73
    0x1050300c504622029800f001e100300d070518140035002400001c070449000b0f10541044096041c0482d4640001c0c1050002488000403080c0304188803007040d07144c0c2c5000c402d8603c2d0703400601d03880e0046d200c3e00340001c1e5001101d1007404030040140d60444080600d581e40c55000f00042c40d0084d110403050300c0c041d48018000c10340b502404107141e800102d8054103103070014003540000d03002c00c4503c071603101315940c064038841059045a102e020034845446024240300c00300d4040902d503400403400804949490612841c00340c019810140100700034061640c20800701c994040040e5072302e01030781206085c000000d02441c51880c0b5074038510711601041c401407401c0035000b05119020348100c0d400142c01900d90400c2c511004004000121540c80401e0140000d040c007240907042680c6000079154009041150b05101e41800c0005d00780c001c07040c04000d104020140c401386c10104455052180060309a00070301880c0740801c07170000000de24a032154060311582c0c44d1701400201e0203d10038603029002c414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 524144469 1250 524143219 524143267
    0x18050907170a0501051023031023090705061b12131d040b010e090309042a09030c140609030708010b010809030909012121110102130909140102 63
    0x801d0034085240d403c0d21b94050000c807000105450344444c8840158901007001c00c103070716414010500b5401410103140280000180c25103c403601900c0003920b00954041d01415140386940300090910581e103c000071507903206606580b4848050403040e4041c03601701002440d00b07800001042e04441d0308010100c03042640c0d8100380401c0d400358038190717001424004980c003400c00b00038080100510b1801c2d5051a0300f020862003070307a02d030a000c01c000c1010785d035550019502002c0c50541c43c03481d080c141100c80a0291162410424035413844e2148240081c0d10301134003c144c24424481141640c0310b20855012510150942d540756603140b8049000f060886015404250300070b000034807500e004401c481644900425405003642040c20300302c20700c030108550038081507000761180040f84120700c04004a0f0300784004142001d411420050002e80740020100c9940c2c0103102d00f0501e0035500ca0a0030a0b00e8614000058001e5281044402500d41c040c90203169440021200c440c080c80302403610b038440c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 524145719 1250 524144469 524144471
    0x3080711090c0909060433140301051e0c070c03050c090f090a060c050903010f0c020705010c0c0e1e09013611030111300402060702130b040606020109020a080718050907170a0501 78
    0x748108c0240343c00c1c4eaa040b11000e03401400310142d0501e903210090015040200540322608103c201d43d91030104100303070b0b003059030a07030300004521005140c00b66000b94089043c035100002404c060010607500c5940070801441c490700c541d240802c051003001a10340ca464002d000340310b0451040e03224402810030503000e0006004540b03021800c0e50141d03c656005a038400d031100b658030305c0e0105940b04104041d1103000c861074901da50700110910007071050300507030300c280c00061006882d44001d44684203107042100d41c820360f25004d151640c502508502c003160009640742180c022000000c0c01461128040c8410550110309945840841ca4502e803c0200b4103611462201691122110300c4400b10342c02503002c80d00704000d0780103041c80c00003c41da006044101085400304200010242c40c8640c00c01070041c2e41d101592015890307d0420880140400d202400040c2d062400d64070101e8000401c0340700f1180c0320804600ba803d800c004403c003e16001d40c1d8124001c08042c04a0b0721020426400d990715 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 524146969 1250 524145719 524145749
    0xd0305030a0c0801060c080a030b10081e01180509010e0a050f1203220201020106032a05180103021e03060124080f0a0c0903080711090c0909060433 65
    0xd024a0209043c5c0d000c90710b808480300c41c01d03034491800394015048038040588610442c0f525880c0c1c4400000c4a540b243c950012510302550303014003004981c005a441050404010480302050000c0740d401e58101c2c010105840c0c0d00c2c42c12003400740040e1355500302c1070310170100301505000700402c0c40c41c0c9a00001e17040d50403954880d0405070607808161b8064802d40854110740603000e03072505010610138810300010a103240d880d01c1c0c0f4803c002d03503604080038204404019541c02c0e504a55030002514044604414920001040121034081400024001c40396607425100c0841a0310407840342d140010229020742d0384640140103400301148040800481c0780b210001468050b0801d9841100001d035103001a80c1c4403c07000000d0246003208609000c0f0f03101c0080085400000200441800381c0c4112602d1041c541c2800324a600c02400e20140c000c09000700d0070760f992034204d019084034040f076012031800e441e402c04403040388c1c0000071a00c075001240142c0140d000f07858061021511301c1c1003c00c1039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 524148219 1250 524146969 524146991
    0x131205250f020a0608251b0803090c0105120619030b0907090509010c08150d08030a06060e0316030b0c161110110c190e010f0e10061b03020c0d0305030a 67
    0xb01d10341520382c1c910702d00880d801a40303115146d80075440c00421518000640c50115442c0b2104480880003d44d070080700081009000e5208001d9558001c0082c80e01618102e108100d0034080707440a000184103000d0085904c070600002110100599003100e81704d111030401c01d00079941c4921511940c12918245000640e942d5410310915560842c0d82c1c8030340c081d070307034418803990b00e1202811007095215488402020100b42280003641c0328404c0800e001882c5400c10341d0103400584000d0015110b64440c540006000808548200890394040310a5100b40c42d030100c0c449140c043e0340010f8943d1192810f8403414020f40c4040d07200320b20400d4603100c080c144405400c80b4030410b10040419158440506d00700b541c00e040307540407038149150303800d1a401a19801009035a2200b07034040c01884103804000d00c010540e00c0e0144c0e8200321406c00768080781c2d180081c094001e02c01200b00d0406410f0004814051500901c41c5d06040070004203c0c07600f0302c15610740501160000d88103c03038658600848040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 524149469 1250 524148219 524148227
    0xf0705041502032212060c120204090603140607090911090d030e0f100e0607080d0903210b0d02210304060c06060b03090604080a0c08030c0406020105131205250f020a06 74
    0x30940302c9900c0b84210004440d01c406d000390121035101c3c0c00300040e04a0031108a0801d00c060030143c0342c070840100b80300b4a5030a0221400ba1200c40b00007170341d0864000c4c0708d2007a030006070380b0040b104021000701d08003030030080d03d803042d004030f02102c2c0e0403540444001040650000c810075103144212403200c82403005009110501e0003106040c03021030070299116441d480d00070050f04002c0c0c840d0709003e2030700c08030340c2c602416604909070841c081295041d64502281c010342030b900c800e008898080103010340e0398000441021000001034001c2181c44003851140151050150100c601b4000b1203035155070f5a000240202e0760050261800f600c0c003000400c0e0300d050b050031640243c0040c2c0082109403116103440107030741d00100001050181451101001400c01006980720306040072015890b10715041c0040e00b0340314014034003004440030510050004262420340d1b41d50300010b10305591642c0f01703d280d500f089041c3e0030b07030a0051412152401d0800801d0b9002003c02032007500e03004a01c1c1d66903e4155 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 524150719 1250 524149469 524149537
    0xc08010e0a08041818030e010807050c0a080706090b0c0c0106060206270a0c08030d060e091218030303100504150e010510270905070e03060f070504150203 68
    0x20500003040108000c3c1d02c0c450802c010b8908a00100020b903c12807400d5030042000340d00d17080300840c04011030b249407580c002ca5800d0703001b00c090401c2171401134121090398544c041a280100040b50201c1d800d0203111a9621100d805030707001149040741c2c02e28842e6002260005a1140403960030844042211840031400500500d42c030710880c0c2c1c008521506048809c80e0018001010744541c4440201044c0d06a450703800a0040c40e01569551480c628000103858460b0888002c4400c094240800d14030005554418400403200c4a0740b24248881e40781075032035420709141d031b06101c080240940e5035540a540422240c04403002c1000802950200102110610070144010504d0004110a08114044a84036400b0f45414210b000039440c8224420004041e0210154040340b024002c6100c58410660048124206802d0304a24100003a60b103020044c40c44d101c2c041040086071501d4065015103000c0d05e8044000d05041c0c45102009599400c90100303401003442e40310300b0b602d20543d80c02c440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 524151969 1250 524150719 524150723
    0x15020f0301050913080703090609050901081b030f150609070305010b030a0e03160f060f02040803090f030115060810091a0919050108101b080609041b030c08010e0a 72
    0x2280c2542c0ca000c04000d040c9000900010700c44c0ca50302d095500090b803503c0188081c038031a8548480181c108000284050324036042603005088410040c040c1620000300d24003224003503e0760300010050400405c0c00c249070203510007030500c04c0305007405c850010881142d20510043e640c603c0309580310001241580d00030301c2014004002040447d110820542041006007501da04980c6040842040c0180c0380705000d809a80e0380340449901c0c0c0400000f40910005003142003825814641485031107030b00e0340310307040425100ea4500c0030340c1c880b203440c2908900300829105404c1c482141d5612000307441c50501321040142044003450100e20807005104500c10b040301101146114441d10050100a00b4042c00c0408064401c441d0642013101500406010f800500301404850b03410341c0200b0250b2308581c441c103031070031044c00f080c000281d072103004035600220807205501c0d2903d03a0700b04a4411181c0e90a82c190440c0000310110030703c00c3c4207460340200c44402c8000c004103c000f4a115403201510040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 524153219 1250 524151969 524151997
    0xf07091703041503020c010b09010503030315030115081c141204111306080709200306060c161401020c100e040e19050c011b06020703030e0303070c1502 67
    0x8280030094280c19000e20002562040301d2030b058440031003418018844829400107500000d42d6021a8003c0c00340c1d00b4802c406940700b403601c0d41482c3c0001d850713000c010044002001102801c1c002079909401070207482c00117810045425480751000ea403961042a403850b4100d83c044034100790148284135102402d48100c0300d0a0400400200040541001400c04d0b9000b40d107007400d44001b0b948545495a500907040d100040300ea24048100b4141403856100e40c0006252004c60f01d00c0030404100381402c1003643d5030281c0c3e00e03500c103000644580a82d02c510941442000003207090034482402d502c042d50500c06003c14494812401280c2e22080404525003000c0c2d21281504e03102d01400d500c506d54000204045400c80da07140b061442c10250307086a22103012464214424032005000c818012035007841c003030394100350304054000c220b0008100280791381e50003e000000c2c94800e074000c000301e00b000340c2920364038140031100504d02191240240d41c120519269559504034620032941c5441c00000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 524154469 1250 524153219 524153237
    0x10308070b0a020903250b0406210e07060309020a05040209030312070e060a0c0c09020a02030f03130b041104050603060601021009080409090507140303040f2702030106090e0f07 78
    0x40c1e19a5030440152805000d00e4080c010f0380d4156405002103554050f41d0101c002c03001243c02440a550b50740b0390b21020024100f00002e216250b032010000380c10140030180030300d9261312110000c004041e241ca004009000356800862080e505400481010340211100c0d40502d803100c3c04c000483c403808080681c141e200308404840c0c24011a060780c2d0101c09800d140d2502c449a4011456540c0f003541000700003080011b5080802c8031403000d1303c01030440004114104400c20b01c2c0a50740f441a4000b810b03040c8004000518036184003071004c0c00480e405030348155070741824030304001002240406c0c940b05500b0680015110f04002030a80d1082d80160700030800d290300908480010719800d101502c00302c000700008100801280140441030b8400e40040c02440d10b000c0c0001503601003103415038403a801c10032040141044884074101600c9100310a03c1c0d14001c800d541200e00002d114041400c58000b00000031f0064004048108807250f00b890f5a410380c0c1d1310000c026066204070f820101040c040c1c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 524155719 1250 524154469 524154473
    0x327081909080c1923040608010c080109180b2a090102010b03150a0209030703060c050c062211030319180902040f0e0606070807050109020a060804030e060f040b070605061801030807 80
    0x22070501a4415003141d4400351440d41c0101b0b00392851340c0c0080b501c070703074440c05881a101c1e440341c1ea15004050100c810010710158510304900c213203001d07102030f02004151021a080d201d0030f001c000058402c80d2200e9045180c204001c946a801040d44a03000d5403a00b04110480e0030003182c00e50000d4616442003203503a0380c49607004025002101003d03054130a541001c000940d19120790700d980c1c0510f0300c039941c0b101740451a4a203401401010402c0c0050000d01042205030800844080705a01005562220320081c000c00e155000d880303401039401600b001d51a078040e0700305900d0841c0c0c1038036018075140700c1d8881070b20740705034492031142202042c0b04038001c100074400e0003042d0303130030040061420785440c01d00c1e00d030055140c0002600b6a8a03940d1405402c0441c07501b0b081c500001c104a090101c0c162900f510040d0034454285500c4c1d0080070f001505015000d81c8030100c4001d052a100c00640741d55450170300c0700007044201e1f4128050094038981c03880302404034200c0b40c103d0b540300800c03900e00b030401c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 524156969 1250 524155719 524155739
    0xd080a02031513020d020d1a0625020d080a0309141906020705070e04060b010305010501140a0f05041d0f01081606030207020109030804060503070e010327081909080c19 74
    0xf21074800d905501744020309185030741c2d0000f0b1140c00c440c51408036aa802c44070b00780525240005540d441140204401ca00031111038040c0305041c95014003408039120f140c000700380e0006d44004001c004180c00200e8003845034045d4400003400307010b070b100008440600314400340d5642c04988414004111641c01c100000c0d00b40d00280340c0c5610800c01d0309d6000d941c41034005c44465017690100d4102d5160340b104cd000e035a0602c22140100024a000c41c1490b5810080c062144540304110f000c0100b050b02408025003c0e40440c1d0040080c20950b100056100001c8454100280d841d00b1a111010000054120000074003460700d5880da003140c400c0c1e80c0b4104040e0000e5014a9041381806103009001020481110283c070041c025521501d543c0d240c07046008001a5041c1c804074140342c84d25142c140c60782c80b514444d228210420b070360f481c40c3c10624184042d00d401003034003480c2d40c440e00c040641600340d8000306140c11a0300000884205692400030049284c0050000c0c001c400c021900410807201c074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 524158219 1250 524156969 524156989
    0x70501020a0803041a0403020f1002090a1e05060d02480106030606060f030518120d0902030102040f08120c2a04152c0a090507170d080a020315 63
    0x1044a80e103611480b1012601c0c3c08170300c00c403415005608848a842801c1800b84200141d00300c1d4240114030301000c920008111030074601401044c00e91283c040b0410154034494000503000090139540c03624580860b03e0042d45c8400382c0c5000d451440000102d0703c2d4080740304070002044000502a5001302e5003408102c41c00d901c00742c1001503481305000400706125110321006000103a94070001742007c000f000d0b050300c0015104015000c2070706203814144001095420344660722031120b5685500206d040d0003d0000e82c04042d616520005002030300e21035180c071020440b4041015a0704844160594003000e01803040000c030315400100302c01c0407241c40810a0340822800001280da00120306010031304840058054032020424028140002c50501d0500303e001d40b049106410001007503001c004086a019080178a91500c5e11500c40400c1424400700c0d003d480360b92a040c0c484100c4a44040d0350781d040c0d4a1410108803400302151fa00315207802207074030400c803110000a8600d2500280209008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 524159469 1250 524158219 524158223
    0x301090b011b0f1b0315051302030a20040614010306051c0f17120105010305090102042904080a050a060c03020903150a02040b120417071218120305070c08070501020a080304 76
    0x6008204c1c01c0000303040305143d0041d50249240c0a00c0c0000c48110b00201d810151407061b02110060468006035070008440868650007505004000141c4001001c1141030803400c0350b201e814000041101c10004d90102c2e000c0409907401d1041d16070f22014404005055040386a2040b440002d81004c5641141c4502d2407510801070102800c0f401d6840b07004640000303401d22002d07005a0010052903a05d40a0b40d500072403810001c6181c10320b00900345140c0201032100c4100300255428005c1c6c0c85895800341e0b401052510142e03040001e29191040d11400c241c0f00440e4568602a00340501311b20038425580c40c098054000e1030542c007180c0d141c1d001c80e41d0003021709100603000c100214541c5c007010003a210240d511004030701181014070709519074022400200c00d1610040c450341c0702155203910086404151424038bc04051007030a11724250308403d40003080c503402090500c030304041c0e21a00400c82c5500860f40500c000340c540d0b08060310b03404103204a0b80141d000f61802000b0030350b0300c0010364100f4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 524160719 1250 524159469 524159483
    0x30d0c212c120d110303060d061109041b0207120b060d05010e19050601080115150c050a0c0608060a06050f090f0316031703070503180a0c03080301090b011b0f 70
    0x49040700051607188050014400d981c00003066186a65003002c070880f00014400f02550562809202107005030141410150041e900d41c0016490303414100100e4a120001070b00501102c5402c0401804074110b041e0010014032408000040c0c0c0b550400a1750000c541c0310008207419190740041103200d00c1c190b48142c400d075581c0d070302d02c0c00d01440401244542d8283c800b03136444c1c44001810000c1c00c00d601648a604140d0628030304003000d5229900762025038801e03a05101050405443c122003450204c0c80040c0140b158124032000e201904030b41c1d038210717012642c80705456903440303080c4002c0c0122817043c4008a482800b024012180b035101800104001034240e0500102030300000e4900101040011040040d0200900500030440b50354580400071902c4a451401c000364007c017180b1004026a003006d80310b885440e440304050205103480ca412801515040e5280e0420541c00c1d802840340008892624002c61807950040d60003206011031039601451504c0c442d1141c01c0481e802c464100c40030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 524161969 1250 524160719 524160797
    0x303050a0f24120c0306110d0501060905100302120a0209151209010e0a030c2301021b0706090602030403170c19020a0e092505030d0c21 60
    0x880e4552041078801031607110107a041645000702800c1003a000d03044414600f007850b43d000301140c50822a0000c4940c001000224001d42144400c03a90207a0b80084030030a041000004103298003403488070665400b2103480c94507203240d80c401d80891168814000440c2c82c4030001031440c80b150307800b80000b11406464005424800707081045c00394400360b90050342046031002c0c421540001d114182d616920300005014084003503c0281c003c8011100040582e502070380c600026140020ba0071440207000402991035011002024051142841c0d40081a02c85d5041c00030f407651140719103108580b9140c02840c07400d829519840000440500075a01c03000741003043d00f00d4240200001540301c120440e00d91006a0148100f021f00c0030150b01c8990780c102800c003401405a0041416403807040030954a5110390114080c050030145a0350041c0d616001b8072001c0310b0642c0c0c11242c200042d40c802d80d803208080030494124804400c1580641300001c0019101c1e880d0110540c0d5036618081d4001586000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 524163219 1250 524161969 524161991
    0x2010f081306240b030a0507030513120314011203020f031e0304110a0b03010e09010203010501051b0109050d0f0201111303020607030210060303030905060f04031b110913050d0207050a030303050a 86
    0x150f0035a01913180807000004000c226005881041c2e0030000030705d01400719090404002c12261038206024007155001d01c1040d940d075010794040c04500d810340701c07500000e40c0d6800e14030300c10126191007600540500d01c2810301186010044442200c0000c43d1889001007203911302038180c2000703100320340800c0440d80c05041966855541001009400d4a403580da40c1443c01d80c2d100c4480180817030b40316078010b04c01408260b070030000780d649150080d0703009540315845c0340150f8054004141c1c042c00b20b010b403109815110364030140c05d111100340b40d0002d0000d0400c803000100130b445a00c505100b07442440c44144014940000100001343c02031045407420041c5152100840c1c0d9664001c50102c0d545903002001c0140c18000560700980c0720491148900d4651005803640040a02141036a041b8010b0b510400002c8c1401191403d07000d45241014034240c0e10340206041516802d03a030314866a603400d1045d0b4800504132054aa001d0490440301e440d5a4080d8058080a009006096204e10b40811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 524164469 1250 524163219 524163281
    0xc0b2701020717190b090d0c02031002030403050904060806150a0e01030215040902030f010f060e03060103031107080a06020d0e0a080a0c11030a15110901050738010302010f081306 79
    0x1113064068481d590560a016101c1807038401c07440e0222060060760020000584e41c0418040308101d8806070150380c80e81c0e81e00d42114036124208015500c1443d0010208036000002007852007000c1030f50a0603280d81c5c2540c10018140180e110300c1b114540140014801401e120070701c095106401000303203007030940320003940040c1d820494803405190300540041006450405401c0020041810001c80740480c0c0300c04641c60340300c1400042d06100069511481c21441001100000d029003c140c408a0f0414074100c00a50720240309041c2c094180704602d4407452012400c00f01c0150b10a89151138801400c00c1a5a4003d101900b0384402c500104100603d440a00c014814148907500f0740c14914007a03440709003110044090f1906c0420103200c5209140d030010111000b507074110615411741c100100c0c000d8095070345024465a12054560316061140c6003d090505992013600c2c0e03048400d8031400700f00e0b480c140885110b2454807840c80302901040c42684244a014200311408a118500b00c2d8940 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 524165719 1250 524164469 524164513
    0x6050138090d0b16090b0a080f0c0c07030302061e01060c0f02010306150e13050628030807032c0108070c05011103090d1202030903250c0b2701020717 66
    0xc0581d080b0604c800302580c000c11210203130003100c0c0030741d04068000ca801055000028881840010b140300030800d0f400d6044141c80c4081c40010495414a80385d1038000d445100688600e50150000000c60490001281c022410f035038480ea2840480f802030348500c1c42003458000241c0c103040c0d43e001c000c118807402c0a05010343ca2060f4550245122440c030500144044010981c00c400c3c1c13074841889501d540d8507e4091510541078505040c06403007680c0f031001c6101c6544010014140029404d0405801a2460600c02d1140b03458498000354055254812660454800e000500880002d215503000b070030b070003003028000c20000840115421030000b845d4019626900c2c10380c80f00c40030b290200e510211750210503100010650450a000807170980d603000303039200d58400d00001941c1c1420341031100c101c8204103030031611080c8080c2e9145e03402e2420f070b0311101c200d1044100126108900c6030560918004210042c0d008000751488c00007042c00020b6004050b020700d000e001c007022042100000c1d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 524166969 1250 524165719 524165731
    0x11515021c18060e1309030f050d110414030d1e113c1c080417030c0d0b060a140c07080f0303090c010f050403081303060906050138090d0b 61
    0xa04d140001e00400020840d0483c00307114243c00c040b12100000d90102c13240f145220781d4100303252030341d01102109000d401d04625010407400c1c04240055420040d17561014034903415003c0d140c10051214007100c15000c1c3c0162656104220300200d442544036852a21204000105171000100c600018040d6030440b0707552091080c84110030720f09000044814030540e00c24590092501090310415030004164038800c107814002d040c0300040c14071031401c0d19542100010403000c0e5407031401c00d103032031442e030442c0020960312480c1c4486c0b56541d00300300c2d00b1620031160540350030385413a002210342481b0764001410324800b40540400003e441e503042286404647e0300c04090354603403400400080c5070644000800741000000103145810503000001c80c0c05481d044449250780d480140041c103024442a400282924035001d504000c1c0708031544094140d070503c640030103168800c1440c042184c11400f040104600000031203960f29400c600091100bc0310203400c00e420064262200301d02c420b0100c400d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 524168219 1250 524166969 524166977
    0xc04091a13090308012c040507030302060c03061e030c0415030b06010e0d200603010b0304031d0102030a1209021f0206091b01110c04020c011515021c1806 68
    0x9100e1074140380341240300405450400020801d5180140610418841c0c034810414070100080107041c41c064581456140700b90101356414103141140c1c2d907800310721054006010b414040781000308001c0c212030145100034901d0b50702a40700945800248600005241d151081051440580e03e403801800c51280c20640484089440c1d0304001500450003080c6604118001032401c4155a404a40c240b41c1a082526500005080c2c4907480da0400c101c03040c9603108001100015207107590310b00440c4102e100340c2d00c808400420100000e61101c0729030100e800341c1c00c2030180300c2c6c0043c0305049408000180030030109002e0169004195480504800d1210064801c80448062501000b855403c0340f10790004004481d80e4045a0181c40000b0008504100c01c69a001c0500d04d4200808109180300030421995950b110304001c1c000d00c148020050318010384000001c00039070500403c030b0480e00030780103403005000c171202140c10344804503110018415101c4000800e103d408407201c1c040c010b00e403a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 524169469 1250 524168219 524168261
    0x31407060e03010c090605130308040e090d020703020307060f21090b101404020a0221130605070203070618090c020c0108130c0b1803061e060105041a030c0409 70
    0xc00108030010400003a8000d0303040c520b0411030a544001100c0031140f171407034440e49650409940318401042c07684050b2418801103804210741c0c0800314914015000e49040381d06030442500141e03191412444040d42c107070841442040414069203500c01002007920300140030030b0380e04440c442c2100c060396148480383d54501080d0304000c49101810b4000c3c040030301c0010028074040c00755814400c01c62003c3c2c05140c02042c6181c0d028000c01113500003074203020b4030000318040545143d56682003058080c040d03071094100080c6090081044075115078000d806040d0950034280141c3c0c54034603511a00a82050a0b24001800c4040b403040344610382c02c0d030b8003800046c4103600004044080103828414584001501400001d07403c0d8003c00403950054220340d22545803e1228009001d9141125054001d6104010401c00780550700701100d03444007101260740d284d00004480e603009074007445030035284110840340c101c6c01c5d0202071030741f240d801520b151505458410110981c1c4001031800600c0070245 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 524170719 1250 524169469 524169479
    0x50705040507050c120f040b0d050603010b0d02210a170304030816120b03030d060915172a061b070902090f0f0a08070e0a0c02060f0105090907031407 66
    0xc01080e4004560b480d0013070600d80280c0200351034404401c038420402200285944015a9040aa03030040002031855070301c4550b1080d50101624080320154444e51804840e00301c90300d048000c500f4000e401901c049008403041c0d1901c1e070441d0f00340721124403a110704106407001a003a200c0030701014134512002516403d05103800b502842c0040d00603540040450404404290301026002e4019421800404e8403894180402e003584500021200800c0c1004000701d2282e00f00d800c2002d0325050f440c03040d201140e544040501001d03464840c140503401414250742e6040d0078018105401003c002000003c0030302500041d50750f4040ca0303040618440c10720100740c1c1c030705061180714001c0c94501da0562425466000180d0058204280184103038a8403007040d07256258001c045c40500190710489042d651101403c01600e10129480400319040a4050344024800714400d406100e01c1c100340c05a80e400c0204005c40c0034401012041d440c0308030100040804c40c51807204a40c2000b0b84090591a8104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 524171969 1250 524170719 524170721
    0x1516050c010806010c061d060705130803030106230c03160201080f040302100c02031b0102090a090612080a18060918140a0b0a120302010203061c0b01210c0305070504 73
    0x1000c00c0d0520044604104003641c0284034144010351090f00018a8000c0c400e0140e82d0071205000380200b031281104000a03581c201006020034000165213505155031030341110398138070090003032400003205007805030140f40b940c0d41090041500e88401c17905001ca42070245d495071f003268014500c2e44803100c451400f0355800ca200c06810144a1555644a142c5514040e5490303540040c2c1450303440d27803801c642850314824400e03140c440940315410b400801203440c0d454040e40040d000c15108644031440040e120003140b107818119001d0711200074241500d510744042d260000341440b4240000038100b0411080440d1405014004a0700c4800d045810105140e04801021006050b5145401c01120010100441c01a40309070304040210703099004401060a00c0640e52014008a21044040d41010740640241d4071959003900d215005011000f90380c40d1180c80554085c1021443c0c0c0018460111801104880407102c41540c03050391081d42d551510f1019240c1c0140c0d03042c1c00c01c8070280018506 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 524173219 1250 524171969 524171983
    0x81c0f020418090b070e0a0e16020c060703020a0813051f0e040e06040615030f0530031302060c07090e010b0a21150c030f0e030a0518151605 62
    0x22800c2005402c16950210000d20150055041c00061441007010750780303460703802c0c0140115020550060414031713000c03080ba00c609c0c0489030140c0640d0b0400740345e50804800ba150307000c0c8c159000305038000c0c007615409910342c0201d20070780301c24811101c0440c0c0c503124100b02152114041c0e4924010b403104400040c080d4030780040c1103210b41c0c28282c400240480000b050380c0c005030010b400180100c290080510303c1e441c01e07400203241c500c0500d20401070100106500ca174401c003c0190a03e1401c0f0250380b2802607214400003e001441840410140445802031854076480070708102d1030450781d200c9071840c005282d03020201c525101c004030700e4507010a0080c081040015a9402915410b08545070f182288201403800602d0410004205200b00400c210401802c00c2c6010090324881140c020042d20071420310101c01401c0c01c0c8043c500903400030032644400300703c4da901c508010302d11040c09400c41c2807880069114081d0103c40b0410020748004002500c0744d400031051308612454a40c1c10100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 524174469 1250 524173219 524173259
    0x2040c0212090411310503160b031b2224050c0129091006021c1202030c03040308010b0c1f0f0908092803081c0f0204 52
    0x10114000707000004299001075504032004100c1903404038000e01940600b451444000c15183c0080c054803444041076010300e82e6003800114503946400a250380c450071014480141d001554080000842007000707140c0200d11a031151028154070616202290801d00d00100d01c031143c00c00030100007040c050200000c0c4041004407130101c20005029040c2c0100c0448078040c0200024040c003544029440055080d0102040440e915030040940c0e01044149208500070310155000c200c1c0c07500031449120031030300f903540103201000700000282d03202003030300c21001c0034000c0d00b032110341c081c00850000d14402d821341c6131025103e10342070400505540d81a441134088541c10424285a60720205000e40081030b00040c000038924008804c2000307000340c50031300080d14500103002f02042040c000030314002c402140c0c2c00100c440c548041c1b1075402c00d00c0c8481c480d10252580f0070000110714001512001c5a884282140040c4100108050b0781701c212403080c44d00e80c009002d04c1040d401d0380258007009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 524175719 1250 524174469 524174473
    0x215131403070501080417031f06031406150403050a08030703060605040f090c0e100207031118041b17030a17091e0c060a08091902030a060f02120403020a02040c02 72
    0xc0c4103800860b455030b10700d024060401c8a4140014244001e0000c00c04c4d0b074900200c0c4041e504d107401920441d807122074103040301c0042c04403100020014842d000c0c00e441c1c528490004042074980c2003c00061807000744140802c180305100002c04250705108507005e45000b001c0700d59691602c00001801c80308560083c0e401d0000511091121000c02501d280c02d850100c0d100140c2034201c010207039403904140ba61264000180d0800003025540821160101d80c8034101192400201008214452401100b44c0602540c0040064003003484071120040150004a5041840307403030301e000820380c540e02004d408440c5d00001b41911b10340e91006c0d8540c1c1c2e600c81110907440d0390400b091341e103480b2b0ba040b840742d100c00c650142c84280c11540500041c418900010804c580d0f42c889280003609080c002c490304440c03400707003440c001d50340007000c0104850207500030003a05083c0c00700c0d610f030b000078521903400720000c40c1d0130701000d04800b9000d00030300d0040b400707a0001c0800d81c0385881003100351036070041828119 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 524176969 1250 524175719 524175749
    0xf04150216020321040b090109091a1003020f07020607020d120f18030c0603020c07050a0807050103050c0f04150c0b0c270a0510030e031602100f200109021513 70
    0x13031129002980c05968951200c4d554502a0f00012101c0035600e4208501e810715010444040c510b202c00c0440210005075018440d00b45190416422405004646a40544100200c0006240180c02400190700c0103002c002100b0140e19420005264804a1404204800c1030b145401390008446032101400f9800c900301a425030f80c0e5100c1d803e006109c0c45061607000700701091070810901290001e040701400c240034895840f024030b0350300d2005110300c40c0424500b1001c540380114403000c4130300580660202c24541071500e400c0341c0500340241c003ca400c0100f80d1581c10700154203024801e0248140c40749080e2966504501e9810fa03000c40c20500040c4101c604940003240c0318200b00700d0403144211020308001207100c500780c0103003a6a2101015500001407018445010702c00e000c15007038002c2d03130406188801c1c600150b0714520409141070110703100a00e402402e00900c0c00c0c1502041c0d9840c0003003400011a804198070041e40d41695919000c081001006041a07501c100000c110240c584107031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 524178219 1250 524176969 524177023
    0x8060408040e040f061b0906053405061603050a020a0207060807050f030f010314030a2102091809010e07030c050603070329010305010f030b0f041502160203 69
    0x40303200d1031040b11035200c80c490020f020310001203a04000a608074a040c0302440004451650841c8103e81d81d0000c41c4080c100892042d01c40d030280c941c070511203410014001040c0d03154407500305a5220010340ca6990081c41c10000d0401c0c4803040c060b44c0c01c03182001843c4808500034040c0c500003080c42d000b40c3d00c10321001d0140c1e42e00142210403a051070804080c582c4901c41e0440e8103118891800403070010020034800100d40a50b2414100c0303018202c05030815840900b210b49078800d001c0130000196500707440b0760380034004240100019030030840040ca0b00c81040045000040c02c0d110248059012401b04118540300b8003c12294000b440b002d01042421070750354200e850b1060068034050a004000540300f603001c3c1d407103082e008105101803c2565100b076501c0c1d030107108185885002a042c07000001e040c885410005041e40c2d800070390510580c0d91005c0070804501c0003807003910f1780d044c2e4604ca1901241d2501c010700000e07500e00c41c041c0013090140145443c046004c255081032120361002644 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 524179469 1250 524178219 524178233
    0xb0a05010806060d050a0e161d09030a051810022b0c080306130905030c0d050f030105060a021204170106050d03171509190e0109030f0c0203070f120b01080604 70
    0x1107448014130001455450380c0a26400070004405950218440d80c0740a4200e1a104100d43e400c0722000d020034403250510000682c0f080800703482e15400b540c014840700c1c11844c00780c40504100e0f0307561180b5490720003007103001801c0401c41845c0200540c0121585046689112100e8058429082c984842100200e140186000c940c0700c40644841d10200209046a4842d1b49640d60001e05c1c407420305c40c1800600308581c40368469805910944540481800014003078400d40b40c0701843c0c0c20095096078609000c1c4000c60303111141e4041180038116440000d1070b003d0005d080a84005180415040d00d00c080d61401c669090b0807061140c01c010300d00300f000a5101c46c01b098004942864410182c58110700600342c4840302810991054440d010012105c01c0025804086403000c001405020003014509088032006000036001490300c1d5001403480340100c1e88010424400703400c03039042582d1595414800b207660742001d03080c614500443c4043c8071070703803107840e0160482c01b000d0100303030030166115a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 524180719 1250 524179469 524179477
    0x1106130507090c03020d020406020708101404030c0305130807050f060f042105011b033e0904050a06030201020c1c0618080a0201090302210301170a05100b0a0501080606 74
    0x32107690388031200080d03c2c91294055910240d040700066450315110000603454000303902441d600c5214035001c005000000c0d004107030326040f026030b4007182510785841c01c982012000c9410390502c0010040c0304000e0142045001c01006040e018010490034082004000d80c40904d010f4031604061001040c8080104d080b54115941070707040000192113003860540590b201000500a54607016a014079a0682c410080c60742d11185d504000d64105a03103140d510500d0009180e42c003003e42d08002c042c11844640449000d446843c0745030800f40e400c400181581d43c100d030042e210903190b52042003196010031841c01003041c21916036014400c10050b400303c0c16403039180500421b484040d40540c54448084060740c51381c2100c501030340c51000300d201a0180c141d4510450040c880e80698405044c1d18202c0034074a2074007000300f07a1661740703031900e2030031200c01c41c001541c003a005199000e40060003c2068055018100b103000c40c40072091000c0000510296100a041c4a454010088169910030480e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 524181969 1250 524180719 524180729
    0x6010e01050918073009030e030d050a08010e070c0b04140f07080f0c2206030f06140108030405130b2b0b0115050d020a0909020414030f010207020d030c050f0106061106130507 77
    0xc0c0000c1b00e04040381e060446240090301405106a5404c034264010000e14011403aa141c1080d42e0342e03514031520301c42d1001c4070366100189041da028000910f807804500c0c0c20038020103040c0e400032480384c0440e0400c004045090640d44c445507080140900900002c9100314084000c0c0850750155400314071300d4011403041501c40105540c030501c94040e950712210103580c100c00c04001058031407070721000900b1310314803a6804180701c00001903d50303400000c0350300341e400240200c441c04c03040202440c00381043da00d40c60b50080491039803496500084206020030320584140d0303400c91825080000500c1c5047e002103041034000640da101e940d4010044401201408c1d100590740d80c020041120801e9141d04849284c030f000103000114905203100b605503401048082d90a20315008200ea401c034401e10800039000301d800320003500130070b000c0c014500055000710159000010404c8265086a8007a0403070004a480090b00c001c1d409800c00c491503020180c2d80400002541c01d481321503844880d4460 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 524183219 1250 524181969 524181971
    0xe03060f040209090a080d02090f0a15030908040b120f07080c0702062a1605040902130506120616031a0310050c07060207050304030b07080c0306010e010509180730 72
    0xc0703240b080c13003007200390a160b0704a0f06c1c86450303500004001020754021109176101e07034901ca03000d070200e1924a40e19130407038600b00d26907da4040c0c025425400f0b0409100c06580440f020b100c001a544014002040d9560b0002400ca49514110134010305031800907203034000b00a050002c2018030000c034070440e02100c0d0101c8a140c0c407815040403100c40450540fa804605504000381482c3e504030024042e00300e041c07200300c000ca070551907406001c2207a401200281d4042c0c4114021200003d01d6409140c200c68084c10303c01c1c1030160340034003d18120003503612100b030340e12000c2000c08e1181c1c18810710b0942401011281c44409850b000039680c0c14401d4664229540d44c0c030080741c24041c4100c11900510344c04507080d901c44499091050f201c1d04240702c01c0d902050400002a5050f10911075148900e40400c3e82509588808004681c102c01c04441e19050081c10000b00384107075200e1070100300041c035000f40b103a4145080782c80103008035244004040800d00c090113200e01c420b40031040b68115228044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 524184469 1250 524183219 524183221
    0x3812040606120f0b01080f0c12030c06010b13150e040b01020f0a060504211b150f091a070c060b1504082505090402011b120309030e03060f040209 64
    0xa00c1001010903a102c140600c40000400c0200240984810803240c09a088000039a0740e030301c0081c0d100c46c2e81310701140c11904000c0030f050142c60502180c14a1030484011607080034030f90349009150031004e81045501e100f0101c0c40300075050030f550005c0d000e8058218080011210b100d0090081b403015413000d0310035920b51904115591080054805803207407542140c07032880842c24079000810b8155800d8540f14111681c40151002c0d040710340318154030b50342d0390745a000e501c030030180b4981d400340720200e5500340340741c10540354914680281045004c0c0300c100004c2d040c0703d520780080841d001100c0c6420424200003001041c80d08010440300340b98025402003807a041c4c0b580080e406030507503203140300240d134080750200f051040091900081002019100720b6843c1e01607074084100140d00c2000c0e401109140020015442880f4a500703a000c8a1086c40c031071691580c3e14440c1b01e10b20500200002e55401d800010305034000554001080b0640c0940034038200441114084440144040d01880c5010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 524185719 1250 524184469 524184473
    0x1503030c0809131b03050a05040203060c0a1e051801020106031104110904020a0c0b0921090d0204060308090a0905060a060f1b030305040b07021506040b011206381204 73
    0x3064410044852000c00c04c0100e250403c810b000283e000148000207250400003510101188200f6010380e800600404150307942000301c1d10594002a29103017001814442c00c8220300b080c03c072200558019031241034803100781c1e032998542c0c1848000d5080c11681410800c0010811140c01d80ca002102514045180c124082c00c0e4410741c030031413191b19000b42c8002a1204180d600c00107009419204614840860f1148104166070352080341c40f4401d08083d08558182c071560042c01000038010240c448440c0c80c4040e00002e044072842c1e40f05031b405450010b4090307124503001c14071030040d10707101504100c1c2d4140140851b180140600402d82801800700d4500d0703410303000f08510b0041c0f07510301c0598015561180703002006400c064404030b0354080b503c0c02082d6001d00104110425544080e5944401c0d62260f0400002c1d01441c140039052100c01002c50760466050b01450015100c2030302d40206a106002000300d0300241044548208550000b5512040c050102201c003044018944018942c843e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 524186969 1250 524185719 524185729
    0x9040204021e130815070503130c08030a210e070b090301020f030114090f0408030601081807030818030708060a0903050909070f02011103101811031305011503030c0809 74
    0x405091400c0c030301061a0395007201508200b401d0341e0510003070b1640c3c1150a0300e881c03070741701c0140c80c041d0200c0d50510014110680307200b1140003590081c000d80141d141d5520b060340c19640540c10980000b8200b0060402940044004000001004400300118075450341c801e600c0c0e0030303180900d906c4040e000640c3c80b40ca59007501a00c03041c3c1c07c2a40c01e150b81c0d5a46580c84400a5403200c0101d006070402800107524070b00c2c01c03400520580c0c100320788601c2c607520301004680c2054020800c21440c416804003d5070020f0400103070000e03522070890343c0e50f50b000c2510340140901c44c8150062003a40a824248001d070000306140707402c24800c003c0461030303a0203403600380c41030300509100c15040101c1d60f080090859016554070250080764000f00729a5000b2401068503100c1110b1038221900b16582c1088002210300c407407160708e8550302c00042e0a425241d40384046a10070345029110003e6500301c030051010031700c22005600901c1c110340400070311f5a40c010304140b100349005081d255010a0406050b286c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 524188219 1250 524186969 524187007
    0xd020310151101050901110912070b0a1116050d24020d06050910050a150203070602120105120615060a1b0303360602070c09060e160e0904020402 64
    0x24624071100c5104004002869400800c1840050b0360070000031540008040c8900503600c042c0503006031920507101e091107052a0100200061071042003400142e1340e004c4405842c3c013200c1999070320b502400800806190507074001d10034811f908080010401691150050218140d00020010700024543c070b00b0900c0f0a200362112900c1d40c000501003220300840d50011003a0b41003115410400e441d80e800c401e81380d0140c3e000d0b064001d0703d00304092100c4d0340d901030301b02e480b10750500c1281d24101541c0ccc0c428040e82c000320008540710503c00c0c014032031880c0024a00c11034000c24802090a8582861051281283d007c2624021040000c2c00604940f00d460350010110101940b14102d0909180060040c102024291013076205440c0180d02c940c1d8440301d014200c0410710b011000c2e140c0c80e40700c20000754400501162206003541001031010102d02484e40200321310a000400d0f0b00d00800d002580082136107460007040a642c0543d0340c0d940c1c40500e00d94000ba01603400503122900f0a00c02069000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 524189469 1250 524188219 524188229
    0x3010512280c1a0301060801120201020d031802060706020a030606080f070e131d010b040908040302130212040f03020c060c061303030e1608010f020301050303040b03100b031f05010f050d020310 85
    0x4103551241004440303c00c0154100c4405580312203080eaa60741d4504a1405034140c0280140c00c00d490320300d40103100350803d000500081a82c411145550703400583c99500010040303c240e5004604030706a5509423003841c0007003101e41004583da19200001c0260008010500800d000840006170520784445d00c0d54051840c520108100030030045407542d80c6680b0306100301e080c0b5800d11a200203d41131602415507555486a030160801e0f00f1a0300f0800104510f1030003001007682400039403000e80500b2900c5004502031100202d07903110b2804c0003420140541c900d60f0240004000d0391022450004290340e0280802003040d51a40980c41e045001c1d20f5840c814691030700c1641115940c40c4400d6807000c0c1100c0c40c040003000902e2700c1310a8042a40000d01c10f26501d90004e010401000100320008e43d8061355010f43c02e540192a1004400d035038006607004500f001c03500a051440618401c0c3c0c0c00041c01090810307070321070403444900401600c9104640d014440c1c002c0086052803407600e41c03c42c0540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 524190719 1250 524189469 524189489
    0x60902060c0303060f030f070314010216030801030b0a0b090408070f022701050a030309050d14030a03051e15010f110d08060112060501120b010512070503010512280c 73
    0xa4541c1c0180d52504103941e80e40c403414048221200c28640003076040b81c402e6401c0c0c00340c11403600c1c64880c0200d0b5000c0242c080380f41d540811881101c10891f107040600c4610a0702d944400b5411030a0024811000070000b6031458a040920b159a84d07480c0700103a03020b54045c0c00156a6101c03481d021314044e41228000f50440e07080003144002c0e0f0b060b10395070844103010769800d0134543e03030b100c003040388a01a510002d404171761400424429401d180400356070141c095403a40380040703621408640b66601c22200280069500c2082c0043c50001c80c840c2d1028241030241c504c034030300b803002d602404040c82c0358409040c0b00c210007004105900a590301900313048103105607000e0403201c10b0080c00c010303070480383ca42c005005503880400c0540288110416110107956039660300344103001c500b009112903076400b07040c05020f11008043d071481604075813107205140d42d095165454a003c1c41000c80802c141640580c0044000c107000304201a016418003002c00b141060003801810100d0a6200d2a0441d000103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 524191969 1250 524190719 524190727
    0x41a03042901061403040206040e1e0a0f0b010513050108070e0d0609060c08090601060c140f010e010f02180f0d2a1d040204090507050a0621060b1606090206 69
    0x144041121950407500c0f1912181450005140f60001920040300c0017584118103000601c1002031f0300791038942c089020580d0345900c1c104007060055564048130283c1c2d1603529141c61441403011400340207200306003801c00504050b403071307001090042c44a00a481c100414200000c406a1180780c1162040d000030701403045000070350808102628007040d0603604039003070802c3c2502252041150074490a8003801414640c2d0800794100d400c0b250f180d000391490b04500403801076011040c000301c20f10806000001034849a40c1e81d8407401c5d56481602d40341d0051041c810032910250403903284645441c1207826030030303403210b80c40021480e56841001034102000355400640014800a04882075003064005516040e0741c1c291b20321400001c020017041681008000c01e00505054000300407080c0704200340c8030002e481d071020401c66003481d4411000100c07089081c02c0701115010050051030766094047c89981c2c10010b2849241c494154a1b00e50948010b0f00700c000d10029034840d0503000da006160582e9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 524193219 1250 524191969 524192033
    0x170a0506061309203f070e01080108120a11070e010305030d061203350c0d0621030f210e010b1f030902030f06090d080705041a0304 58
    0x2002241004400c54040040320100c881d04a0240c035000d400750440641e1a42c54040c0c8491801d241318420b1038031325000054010076105e0909220301c54121581c8800c80c1411500004000c4041070380000d1003078108043e002c00c42c0c000c0004581c0c8240c0ca03401c0250110412070740c094501003141e071007116600300b03c1e4004000c018010000b846031040b01c52003481665259500d0b02c1d01c110802100501013403458500b038030144062101c14078940c2c01078403800c6c0c2d0703490301501c540800002258011074204001940000c43e0315140b20700703000740c1b01030201c04c0c00001514211942c450150307038000d410b11451042c81c0a0345440b0301444001c0e140c0440605903024a031010580180101d032064902c41e50134002c40080c9410800e2010720102c13602407011f81b0181520009400805600c1e205a8041c0114851540041e104020300c03801265684028003140390b4400e8000c26054009e04510100b0030100f01c2000007003100346200421011201c0310300c0d80e0391500c0c501442d10100034504000130030b0040d901b20740 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 524194469 1250 524193219 524193221
    0x1b0b0603011b0518011b051c050a0512061f0302190903050d05160602040f030c060810030605090c1215061804021027080106060c02060f03060f060705010209010f170a0506061309 78
    0x15403d42c042e004164214644127459600580e11000300007442402904008045040402d402076005841c9190800d801c40d0032500d41e00308000380b00d0109800040e11000d216001c3c83c0300040c5002c43c030b89140741a0440d41e5580c0c0300c401c455118010410085401a0840b0442441c041095401942103541e01e640c1c10751049a04801e10041d41c2e88100c9142c00a54503020700c240c03d01c5450b1583c90040f440782540c4c1c1d60001030001600d0074001c0d1154a01d040394079166100031224101401000704a000c1c05811022981d10008043e1802244040e44001c005034100b0480e64126074115103040c0382c143d10040845009520740b04c005a0b00d41a18441d0441480c903101503402e581d0100c0c02484006c0d01c0e2001980c04072500440250400402c01c00040d03402202006180c01000041400c070010b02076000103081c079002458140c8050b54000f072500e1903580c0040301039082d06980e007000c000c070f8500000e4048c907001c03005203209881d40d06c5000080c981c1e43d030801141c0c1e6208442c5d45c046d1000381c40d0070a01c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 524195719 1250 524194469 524194483
    0x2d06090a080c0f18191d0a0b090321090c0d11010f0801050a0612320f190c0e0907090e06060412030f1b0b0603011b0518011b05 56
    0x1d02841d80e070080140c040c14407a400800f10080c00c0304c2c07140b890715108440d02c00034458001158540350f8036910b401c0c07003880c50300c0981c40c0c1038000b0000b489002002d043c407509034840079000301d0301e9910030020800c80e105980e000c031401290034042d00025a8405426504200b0900030240d0301a41c071000c0031042204000320804162001e070b98a04080d040d0f0501511200d6003130183d80d1b0303c0220300c142001424459200322800036a03441d0081030f00c0c102540412a558181c0910044200c00680d81100801c0c000640c2039200c20f41e50181003081c140000700c010038544501100720741913241c2c80d6070b40419000e0015110400c4010309015001c1c030340202c0c02880c1072420301440004460034408038425180038819102074812007250310724401595501902c0c1242a10072140c180415401d42c044c080340140c0604500754000c1c13000182d5464a203013090f085451498030007004a105849054034203a0220a03120b4560410520841c04040b41005855001540001c2241400345d500c0c1d030010400b001c030300305c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 524196969 1250 524195719 524195743
    0x240c17030406150e0105060a051c020715020703210902031b0a0f0305030909101a0a080c0a080105040f061a1206220f180507142d06090a08 61
    0x70401c03500e29000c0e146200c0800c4c030a400f120361100b001071029241c80c034000c004000282c10598034029040c1c222108010a0700c80f64080d950b40483e1400520528850802d0b501640c40c8007140b420f600c0d65006015030b10300054011002c103180441045140080d070158050316002230440d0034240342003072050903030981201c0c00c0e40568501c041c001030302cbc1943d080701e601b502d0303102c409181000c002009000003407000610800c0c10100004000450296000005012507034031100e141e941d06a00101a180c008054041010410301f040b9180d052a404960181920000c84000c111a80c810b0b00c8040607199a400c4104100c40c1c42460a0314008080024441d4501e440710b9866030b59030703c60811980800000c50340500981b501e1030711582c41d0700f5600800e004001c2000004200003403994008010442d40f0301120154045241409210340f030f0001030300120f208454084041344000c4c007651148801d0500151400c180700c040000ba680c980f001e584121a0207030100e10f032250384401460340c40c1011044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 524198219 1250 524196969 524196971
    0x70c060216260a0e15090a03050f011b050a11120d06080c0a031a06041b020d09080f1506360a18030c021801180f06240c17030406 57
    0x103035044258202c0140d0304040100d40342c2070f550b0025402070203128012003582220b055030404c4140025a900c548020107503005000910210203040c0e1958211040c0b5030000458809603540440c0c03a9600c02c04881e8070b00c600b032a1420040d03040b00011440d00c04c081e100443c940101055003001c1c3d030206e41c081c1040b14000801c48841301d01c0001807020083c0d20b030001070700d120f46045508039007804810340a1703040780010780001201101c1d10307031852080308849000401a0041c3d982114841e074002c07a5040903001d01c4005c0d000314050500c08550300c24078a191900c2d10f001000000380c09599100c0741c00c2c460125050701c51b032102c0e0340a802e12002c118003c0c035400d40100382d07000b05030a0845881466585a11017011007046a82a1801e8030030300001101240d0012841e07105102c049042805207000300012085000d401101034001070944101422801c0260714104003041492154800030700d80303581e248075860b42c0500c5000111025010114060b144080e880300e45058410440700441c852800380c04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 524199469 1250 524198219 524198273
    0x20301200a093507030f1101030b03060c03011509080d02010b0117040f0b06061e0408010b0d0807031116080703020f091506030c0d1505031c08070c060216 68
    0x810305014400d80c030701d01c1c0030301000c3c1403850046450780b045150342403012404c03200c0c016078994609082502240045600b0801d41101942c29601805400070100c0110302400c040d1811115402e001e010500ca4050b60025880c0380c511070500400507000504507a205981e0704621050303003c1c2c040c06002011030300194066112000005415940c10700650780803910410482140d16804040c00e405001c880d4842d00c1000141ca680301c422841312032400049030815180c41c50700c01e6942c21261400ba00f14003880c11a006440003a0342c01d0111811130b82e041c00c03c03141d003100010106207400003001000103030701005040818500c100041d40310440744200d0380360282e20b00341002e2004040b402d5130744240c440b1011242414605d0103502441c0d2040d41c50702000c4c2002100003004003030710612003080c03158596030b0006010301d0405111001d20310200204400340e806031104000d143c204028404001c0024025000c2c0411181341c04a9007900115000740c036009003542400c81c650248034000001c0401300407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 524200719 1250 524199469 524199479
    0x40e0609030c280f0201030e060414280b100b03090a060f0b010e0405090c04091b060806011706030a0803010b0901090f1202040f0e060c1e03010f0302010c020301200a09 74
    0x1800301d81511503440e6248102da4242c0d40c8411140130484812814151140702d5000b00d940100010b600c070f18016440c480745c0c03001c403d88071418002c5010a000600458841034890f02c40c2455841c00c2c0c45d580075000107aa030381e030f01000c000b02c10281c6d082010b003128000144240742c07100080007180c00b80681004c20944c1e102007030000c1220034241d010b9001c076804034220b0385c49181660102d42d000310400107403900311901000040842d05000c00c21209049000c40c02000b203140885408003a01c020300340035019044c940300217800d0303801c1907a91899603140c000004445480c144401d8a8899221100c1c07a143d5850310400d0440b50000d600700313800240d9603800022034911102c4450700700d40342c0044d07241030b04005400707000250208a00c4180e084e0344900450017850810401c4138400c45800030450b85981a408a61540c4d4200c0801001c10550600043c0640084210001700b1254242022818520780e4800310b0301401d480d203044a07414042e1441d0100e8402d468005200d446059900da0742c81a8036a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 524201969 1250 524200719 524200753
    0x30f060b100906210c1706091012140a0803070f0903242003220c06030203071209110f0d170703022118060306010c11040e0609030c 58
    0x7000c40008002c1007080110700d008402120302042c40d1401070031280000c072540401d988110041c500010110000e0000890800020b55004402207500403d1820490b00c00c1d95050118001e0341007500b4241028010003108103810f008004012044e190f0300c2c5082e05241c44030381c03c21200200480d240d02900d00b091441107503a102525800504a862101c41c82d240507044502041c416003015950306501028a5079080d400e150034440b19111a500d01c0c021004031840344103198110b80c001042001c004c0021650031049058400c03a14006072641e4490307078111024121b07052010381062410281000348600b6034011007000c202a61210349009810301808251858100058448260b0100600b00106c10100038208180644119900031045860884010b80340200c44021100d000814810311480900c22110100e41158420304615010f000a0b0101044a0000700f00031a00c0b40e081e6000d07601c5600a4402010074012a8804d1418880301641c950112445281d18841c0c0c50030012004a6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 524203219 1250 524201969 524201989
    0x60e061c030827160602060c07080304020607060e0a03140c0703110307031a06091b07030807050c031317160b090301061d072012160507030f060b 64
    0x40e4100403540a009500e040b1200074002d003002c560107501c062280200e003941e440c040105010540500801409504130500018071540b1040a641080e0200300e2416916010ba5200c2500041c0702c5580385d80314400030b0003074401c2c41c078010300c41450b09043c0c003600400000d4034902c0074801d465102d0b83c5002100c1035049402071030005030341b550003000148001412004c030b4a01042e07016046420060301c0e0f41e1070021182c10004004560700b145d0382001600e04d0b00480ca01c2e0401d0810a034608002c00400c04400381c0d02c5800d801a05215040c000305400398402c00440301d500c05010b058948032040045901080003d92107054030030140464100703c0c420340490f120701c05086495540c1c10382031800c000c05400da0010800c1c2035043d503036410300086030084508074804915081d0090041c525210401400c000e103008041100c140520900c036001410004881481e004941244c40d1503809081809843d2500650300030480c0c001d09030000100500100c025001034811031b01400340f440550180040140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 524204469 1250 524203219 524203249
    0xf0e01050714070807050f010509160b07021005132705101d07050f030403091508040c21060207030c0213050f0f0a02130305060105180606071202031c060e06 69
    0x800b0815100065004c0e001441a18440c0d4140d600305400d0310322071400c64000f00e600c00e40940001c55502808980f650540015009402c11340382442196000f24920901100700c1905000d40007801c016521108184400144441d0101080032540d6020341c2000382c020ba02200710950828003c2480305040b11401c01c103486205010b40c1c91485110104a06050042d0000702845010814062150f0b883c0c80154800c1e402900c50a5459103010102010b0344145055002001010700502c400181ca5290590071216110303000454aa00e48411081c9a82404001000c0700e10000d8501d08241d0840203080420340220b0f01c24401441c1c140015080d40c0b01241c2d0301d031140c4110000103404a415000c00394001c4448070005043c96804030b00050a00d6a6810541d1039a010b00010040d91910200f00a102c6114a40000300382c00d150010030154040c00800400102108261074100c5100f00166811160170140750880d000500800a0042903e40a60464461a440011703440d043c03007103078204860 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 524205719 1250 524204469 524204507
    0x2190509120a0c152c060d02130311030a0c05040c020c0607050f010513030806010315150804060c0c020d08030c1e07050106050604081e1c02030c0609010c120906020d0f0e010507 78
    0x1070314820810780102594a1140c1c0106e05002031000c0190502c050320201081c41c00c1c1071402415410a221800f0100500510070343c82411483c0016601d0038401c01111800d5034041403c0341048010390410500c245035640041000c03c264003800381c001a20030242007420020451921100050350791001040c902402043e010f00208025500c41c5e4080e4006103554594884510749810851040090300d0301004000f9801701d003440107018181c442c3c00382400ba1414103049506082e80424001c109910340a09008030100004480c02448000c0301c4046030308407c0f050200342e082e1840751076900402c506071415840c041d40410981400d4003182c0940703815030010701e4544410761004400c800500007104841c0211300d12001d91b104841610000400b16402851b1565500f0300110703d04603008114035803a85c1400c0b039102c01c1603080392140459990030500880d03a20440d040107030186c0309030580c1030116850312541c541c60f0a51365000c05189601c2e54028002030300e842d481101c001d01404c9180c0008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 524206969 1250 524205719 524205767
    0x1203080705090d020a080d030507110c091825050405190e0a050102030109090314041d10030507060903032303060d0f020d060b031002190509120a0c15 66
    0x424041e001501d004140200351840369605030380803031034501007640304280a6211441c0d40c50280d425009056001707040e450440c0383d00c4888000d481c0c1e941d40820000707002e004c084001c51905075810300c040e420908100c00316100391130303445c08100b03900c0310202c2d480e002c041e00e07010082607a1800d0b00070703580545914040516085540652113000301060109940315204485096000a80a0020750f000300f035038100002c0c2c442c0b01410043c3c80d65550501c0d81502840400c02804040c0c12032034000407400c0e0441104400c0e41e208000c0c131080354019000a0110721825100160942d800301001059910942c4c8124000f03c0705030310113840000351040510b0201c410300008a45040410340c1c26203940c01040103255038102600804c034842d421900989000340c81c0d441180b200d08040000d43c2752480c800c1300441c079220752186500c4600c0e42a580300b40c2000b000161031852a56600c00c451181d1540c1003e444881446181803246d101092050b00040701070b480003141e000b40201c40501c0c00100c05444a101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 524208219 1250 524206969 524206981
    0x9060e01080114132a0309170708120c2a060403112802010306060206040f020f04140f04110102010c090b0304050124060806150712032003060901120308 67
    0x103294000c0c500c2a04503284280482138030119010f0203a414207031103265032218403140e0260303d80c280118000018541040207800000b08a0803003420400180c40105803035141c141b80038602d0344074240e0102d41e40380c1200148400302154000800d03215101000c0e44103000c0506404400c034090035414001c80e03030088400640800e0203050400000c41418041d60140303000e000340c3c4e0391129460413080c0503d1083c2000e030380031942c1510580020b804180001d028a1415640c0c4651000b550b000007801104404100d448544075600445080c046850341e9041503e0411400440454220790980e82031404907446c051650041c8204d046041e400da0f5040d81040c1081c02081e42580050400c907415981d44401801d002810001c815449030001ca52107102c40c03611800501c044809004035200d502610300302035010155004940345140e010a0540a000010005a0080c2100f44200e0074600c4003170745250002d450400150710842c801c1314940580c0e6200d41a4480c0c00511071001404104001d0100d01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 524209469 1250 524208219 524208239
    0x140c091210060303020c310c0507060903032306011b0c170604060509161e0f0b040810020901020c09100302100c03020d0c05030d0b0303121609060e010801 68
    0x4000c200036800c8408280149001100b19211580140c006811540d03080c0c1c0385150882001c507003150300f01c00038247c2c0b841800c4004101a08603a401403515500c903a00a0114054000d50303234001e80103075042100103a1070401401810341034146018800701085c201183c0c1c454407081e980902810383d10b00e444480e00360308620703044000c4402038441d42029a00010001210500a880b800f1420017801389410715281000c15150b02801c003840681050050703407503031030440d425002216414144c9079140c41d6002a1b042040d99190461501c581018002040d0f00d0010b60050048820410031580f42d161140808412030040020703150040e04840030607803941c82c0800207280c000e101d0034045070038541e50790300051000c04e450842c480401c84421080040c15014400380e09009501d01b000b0303106062a0751900d840e80700e030202000c0286d03a10700460381d0799101001611030002d034a00406240c0c1c02d02d0309452003103e40395522040040d1079020007041031340c031940c0d0954488006841e42c0300d45034244074000e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 524210719 1250 524209469 524209489
    0x20616030e0105010b2206021b120f06010611010b0609091b07050d0306082103100503060c0d0e0d050414040b060307030b0406060e0d081308030a0e010201140c09 71
    0x1420181c41d030441c0014860280318241c020101c091056030b4400042003141000c0310350245169040d041c1c01c4d02040160b40200d440e00342040e100848818910000000031580a580c13610107000c0e10402071440303001e9400061483c16228942c0356902c8405001242c1801d849001c10783d29004007040c40740d505541000c2c02d8058101c040c070f000d45040c003900d0f50b00484140e040352006032115440b408803103041c160584940c7d405090b030040541207454104598100c480c1c9030040900e440380b80040002e540300b040b00001d1001e41001400e603200760038140d10b400141d4025204505180780752075108900181300140b45010b00a50761540e80c00c00e880e02c40b03a00d14060701852075580160b15900312407640c2d540c1d40001d520481040d20000345001450050000b218803a40142047c0004140d010a207559107040c102c0c4555445680d00760b40c0d40c030584003000c840300c0300d030b01141b4180710104010090a400440c0881204002c2e030003005a104503e200c80690001550442e01405c4100000c038100c2c18000400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 524211969 1250 524210719 524210761
    0x150a06140c0f0f0304051c0506060f04020c07121203052202010e06121902030c0723030f0c1510090c0306030b09010605030f01090506060108071202040f080c030d0206 73
    0x3480709105814902c500742240080c0d0340d12a034000040610061410030041ba0b02680e014111481071031195882d41e82d41c03c0d01401c41c13481410821074072641c590382c0b40c048074000745611059030354860b03440c091a41922140714003120750940130103010011300d10a01c90301e4403418103a83c409600b520480300720321b5403003284041681003040070600c0c2d03800c6480f21001001e80b03850b4500f91541c02d2422928080b14000e0300740ca883c94160041082c84848012407060f1400c40b034020241e031071007560b0103a054643c60f0303442c0011007c50101141a00708079140d40083c0450240e506c06071480340384507152803211007008541540d803040c60301c0750038071988005500c21521798683e81400140c50780c030382e19034018585086a09108583d180c0b8000d001a00341440800d114040c2c40c1d0003402215840d0b0f1391182c482d031000f00603604000c41d000000300c5051181d1420007120312502e0003159503d4a4050481c0e8060190048070850b1043c02c2548503030b8200081d2464422010364080c01a689030190212070040c1c1c4c203003503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 524213219 1250 524211969 524211973
    0x118031e02120301060804032d110309030106140a1d0106030e0309130e01060905040c1a07060e06060117070c0303020901020705030f0d030c050f0d0f020d05040506150a06140c 77
    0x2042d060707101c408008502815050b2219012440c1915004200700c12001c55407100c0c006800c0c0d4032081000c0031003e0b51150000d424003240458454002d03a2550040a07080e503455800d01c000010001ca2044403290f072054191009030b55251134841c91500202204400304101c2664401006070911a84c03000c510050718030141c0e490001c10f4000202070700109500c0250082c0daa28014001c19030910441c1c0040400060074003551610744c8406190003c1783c416040c48003d60810180c2c171031444030840f0b00c00d0790310150402c0100e83c2c442150b9513560080301d145003c40c00514540c081c00c600c1400d8103100d400c0c01d40d600d412403030840e03904038040d400110b00c042c10740c480c80740080750a540610401440082c980001d0007042841031006040d5807000d0308040a00104010803411600810212246000303002c1c800b0403d2401841c0610092003042450b5454078908010301c0100100895000d0241807141c00e0400d0240501c005c20004141500c501b00128001c041065020040380c03003c0d08000c0c41a900f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 524214469 1250 524213219 524213233
    0x15020d0212040b160e0102030d02180a09140c070510200a03050a06060905010518030a0b0c0a0917070e0c070b010305030406090603020f1234020118031e02 68
    0x540c00d01d02603908455140e144410401843d01c07800c0101d111800503d0001004c083c0391001079120310861050440040d0009184032040c0d102d102c1440f8682e8016158443c050383d1410280010700b403202480441b00c00032000300f003c003520141910030007030b007200180245c1011410401c000f410f112040010b6100c90500d6048940281c10103000c6503201e9440110311480d11030465012518180c11131014030404410a120a903448000d80380b940c00c40540038405032602c06d000030f180c40d036102c81c001c1c01c05184004004410b10014080c010003804e070b44440c0c60494490f56110440c0d6a00148a003007503001110403c00301402c0a000d0b500042e05c03c00d158134245450b00ca50401240c00d07081036559070f00000f41004640e504c0482d000003000c06240c21410041340c072056074114841c0303003c03a6101000410220703042100840607130102084c10855916900c271001c042c2a004000c041044003d07500c3c00d41c82c95442c001d2880906492a4107582d01030500140440513000682810194001c500c504c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 524215719 1250 524214469 524214487
    0x1707120e1e1f060305060103140114010f1706060f06070305120a0204031a06030a03050307020c1807021603050307020907120507080f010504021e310f08030715020d02 73
    0x2005032685250180282000741c0b02e10900c00c0300c44802034901ea40440c500a010808200b01040c0035054a40c41250480301c886241d5400c0c3c05007480d55041e0410030602400091444003000d00002129200c6200303020000050f200d81c1e46440c0b084501c1c0d500f0444060103c069443d011008000b07143c820305245045c699069810451584102c64280e42a60300060a00c180310100c02806940d000c0318660400307a00d4000042502d0704190304004040c040b0100c0071440c1c142c022b0210049501000e018105400c109a4858510100c1a1540b01c05802440c5480d030b0f8440c1c0c414202e1064a0b004401035103003456030b9080c004068030090414042080c040d016480d019118054540510503540c5c9490503800c0641d840b843e46041070380003611441c0304100c40b0f00c01112141551a00782a20103074951504412000300d11110214001c1880d4003058014281d04809549076500680700b0f03242001d00a141c5401190343c3d41d00c00da40c406003019019284101c07814409400819510160740000340c1082d0b005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 524216969 1250 524215719 524215753
    0x9060f020a08030f04060e030a0e0d060b03061e0105120a11180109090b070804050a0b07050c011104090e0d1407020126060411031e2508071707120e 65
    0x10368025400f1603a803030034801800340900a00c01310406a0000c2c621300200d400c80504403212b03d40c3e0f45806148140d14010600909501c0345104210103000c0d51584c2c5400c0c0e4400141c40c00608150300140b01040010410381480ca494500302030b4054020407200c000382c0c681c02d8201e0b030044612a8801d07400c0d1071101038241074400c143d00918810701d012420301c0d118a040c2107440c41c02041c6004000000f820400411701c00601c00300c0454010b0794006c80c5888a10044900d840f072a00900d07a1903007850f401c0701c090803051000784121100c140b42000034a00e00c840c8207844640c10030f6040005000d8000003503113134011800038003c56105040c0724492081c10301030120f082030f10041090104a9400400c01d55091600070a13565100c4a051b192452a200d43e000400e000e42c0c032002800c203017285000907545416243e250b41c0800a81380c008100c0c0b201c4000080415000b120620001044040b0025441491600b0203000f890135449002d5418680700602000704151030102a01d44a07410400020100c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 524218219 1250 524216969 524216971
    0x10051509030a0f1a221a0907050a15140a0908011a040c0e09010b0c2d071d010e0702100e060a0b1801051507050d05040f06080709060f020a0803 63
    0xc01c1403460712104840c01c101c0954450b00d10400d1041e083d9000f00300c0205603084440170307a100d543d4042810400e03142002c140c0d50b240000c680511030001307001d000b181803000842000b00e85040701c0c50140c2945804800c0a5030003401c0c2c0c12000308603000c1c001034207805994090100d803000341c42e0403481300c2d075941d6845003958044600d0308070314250010b4007031b00d80c10240a0440b4000d040c0c00d040150008103404030305400414403981d8031016010940320070094041c0103107090783c200301d01c4803a2000d080c94200c15031102444ca031645a8420280002401d11300501d1014034502a52154080d60f0702e000400a070100b0018401400c5020703042b582c0307885c1401840740c040d800b52060700809040c50406418800c440a0b106541d00c50100c0c01c1143c00700d01b0004120a040d6142038a685060803070000b0404000d01603000010928000c06040e021102c0d40000038108982d8507010a2410690303540d82913442c60401d4402c180002c08544080c018203000c1c2400318003038106071040341c040c01440d40f622101500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 524219469 1250 524218219 524218223
    0xf02150a0203070f030c0e01051e030f0603010b0d0c06030c0507080c0c010224150d0f030203220e04030e1203131d011d100509040b040203010c0810051509030a 70
    0xd4003106100403e0350200c0701c0c003030f840120304041084180115000c0c0441a041c900b090400100248506403510415203001040401c00a101c2d12410600c0c140c60007020100d0f00c0314000e600e42000605240b42821300c0d049402c1d005045508428200481103015003500266003007800303800c12840000400650041100000c41d0010f46268003514000a0038103900c40c103030955104c5d10b00061880c4029004d801e54100c015484a190b09192240c046072804410400241000da110030707100d424540c01100502c06203201c40311140001013980441c05140645003d1a580c40103075100240000307000700190408210000c0590944403c00740703945207190b1011949220f400c40d03a034010400800aa05400850302418982054a40c10b014086000c11116440c0c00351484240e03000c5008682c0711030322280908005004900c00d86001e003080c0080c5002030340c0c12400303586481d8071103000d98031450005005540c0003411103130192800040200102c141c103521400c0f0001041585090381c0c0c100281e036400d40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 524220719 1250 524219469 524219471
    0x27110619050c0615010215270609072c0a110d06050306060303040b0a0c030e09040b071805090c0a2c09090d05031801091b080705011e0f02150a 63
    0x260141c4031810039201031310031129105009443c1466070780104000000c0c80503d101280c8507595500031841c14048402041040303c404041944c00c04000301c0c02912400011040395584c079074a111648100024014040520320303801d03000c07141c070055140c810b90040d00aa00c003240b0303400314894086c0e15510186840320010b65940c010031090030144002c030341c4200201c1c0503500309131034440410605d00c03030003000008120841840904040c01201c01d02c81e0f03440054039401042c90070b450303e02030454040d5a51800b181078610780040000c036034900d000951300701030b180d038501d0f4940a80c1080c03640c000f000a0018000c21320300f80505000c6a0a0101030084004d076400c95844840c02400525003001d002c606560300705110301444039030080201da40041c1e400c0a121150014502410f00400a9110081c4001d00303401c95007441c061440700d0b02d01503482141c00c1e18989130b6201c00640300d12001d400c14002c80900c410902203c28000c0c42c0c00015030055005075040c61040480340d000c0000f08459000b20320b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 524221969 1250 524220719 524220727
    0x1e1203092409010b04020310330e01030f090c0e0a02041a0711060414101101020c07050f0103021e0706020702060a031b0309051510051908012711061905 67
    0x10b160902942010f0041075500310b1550401081a15240c0b05074041c0243d0840c10003d8251400e035895680101d1003c01c40b81855405010700d40240a0b10300307107001c540001d00300550100c0d102c2103403283c0d1035019441031005c83c0113842c1403a034299240004003070000c904c1e402c1c00b001503c42c042800c407012000c50005525641e240301c0c41c1000d80d01c030b03441480e9405404244418041891010940001140100d6141111882c10401100d001c6080300282806500105089404900000e11101a28000c46070b0310203050007400110200e00458403080b0381c00b9041035511450f0030320a4000d001440c080c40c0302521b410030355004103000b58000d025039400640d40d06000c0350b0304002012030301014040e074078007802004c40c2d076142d150750351011941400402c028140070901101040c2c00900080401804615810074182c60030112000c50740702d004641d500301614101c514030701d41c0c1101c074111480154001c0446a0707444105070202c41e8a1480c0c0c001004001703441070001c51a0044404641c20360342d04c1d9072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 524223219 1250 524221969 524221981
    0xc15020c33040507030305031f06031b02010507140702030307080f070b1b090907020106080115181107080f040b0403060609140105130e1c05030106021e12030924 71
    0x101c011500d00310400d00300450a20000800201d200400c43c1e41602c2c4c220f46030740f03e2444c003050302d0070303e80000d2503001c089020016200340c01d500551340d602d4148401e401d034030701d000c001030782a5181140c04c0000607100000700780c00b6108100281c807a00740080d04903402c10b09190303558101a030006240100f1490f01260729820402000a01503005e0b8580a40f00c0300000407061182c614042ca500701440750f0021030000c0c01140c803d510400c010b2210b000244040c050300280130324015400d010307a03010130003940d404042c5244a4018002e540001c0041c0300d1400780c09440f019455080616000350a0004000020361a03110201800166001d16070002c0c45900e0300c41c1d40310480d6400b049800315500c2400042041381e0b030380700c0840c402c142030380400710b41c0036058051141000c2880352400e1043d2030000c29082420380c441c0185059981d00e030201e424102400031401c1071028a5107250103a580940d48181c12007074180095038001c1c115404650b0030b2002c4c0304e00070340281008400c07591050900f000300a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 524224469 1250 524223219 524223283
    0x3060c0e100509090a0902060d050411010f1815022a0a080105130201030b0303040902070b041b0f030219091a0405130f06090f05060f0f0105060306010c15020c 70
    0x11031200d080c14030528200f07503000490311200340246040b0440703035580b04100075520703440d00702e403850800780390100320034179107480d0511510300c0c7d5501e12070002e12254a40c1e2007450003000c81c0c1d9002040c005ca241030662800e1001081c500b5035041280840c081d03500404200c4070243c4200e10400d8048003181c0c10001540c0501c8a070b000560f02030842a0704160074041c14540041205003415020b19001c079045180c400800e2039440b40d41d101400ca140b001514105014850460600941c4502d00444040b046d20702d0b80b0f07070b10200764000d0214625101c00100018035008144010306070441441009c43d954902d10b4400311481e036010196900b01069404100d854103104140e07000008085028100d4983d031507080c4a803100b450000c0032a65200381040c280603003020b08010860f40a4100d8400d403038003d82d1908000e0007565501d500000120001c60320b4074111055074400d0070306a503114120300c100e4031070001114003c442c030119103908001004128005001514400c08826540e060b660a524070b914 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 524225719 1250 524224469 524224489
    0xb0c0c04090212151f03030503060909160b03040c080f07152c010207081b0111010f0203040f05010606080402100c020a051201060303181a0d020f0d05040501050a050606160c03060c0e 80
    0x1030401e45c0c814010b0001a8101c02500d0700b064003a0340c489944d549107124a8907040141502010203044484001181c0407428000c41c8507922552008185559500005070340b020003400e0228035402180741880105d20505401090841600c0c01022400c004400c800a1200481441c80e01c07540c1c0b01c040550365601006100c005051580040001c03080d6840c1c01446401701e021180d04000000c07400e101042025081400080c405950465490a0031b2411007106150400212038650030100700050450107603070303803500c01da4020300b5882d40780c2c0160004443c0702c40c4000040740d12804034040803440343c0b50796100078048180354000144035070460501030507807000340c2c0310000c07481c0130100180006041180d00310340500350f944850751103442400102c00a80910030070b280259001090114030358500340c0100e03000754002c0c0002c00c425251900b158050740c1086076603941000c001c104e1a000d00185000c410401c1d4007840c101c000e15603ea5941c4419a40304410001c00560500d182c2c030a03e2038442071030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 524226969 1250 524225719 524225761
    0xf1c0803130b0603210c25210f0b040213060605030a151d09070b070c05010e0f0d02210111040303020f0d0c030f14070605010306060b0c0c0409021215 66
    0x140358801c60441400201e4420032541e0075610408942000150801c000001c2c44854482015030000c9204490401f444424400d1442100d01d10084603a04480900c8840085410200c1268004800e86443c20718680c00341040760481d0030302220103034501080c4159000307000d86548195036401c1030589101500c00d0704000c2c03d141c0c03400381c404210030546819421142c0c6c40301d01603840a640c41d4900c690801384a42c0c894105048005086401c000380107240700207503070090b250ba00c10490340720240708601c0c515800103a0002c82c401c0300c04025140003800f05601280d17005841c40e1000d42070b186242900c0c4c008a01502580d0007260034000c0507018001d501010024030018101403018400090000390a054050144038040c42c412065910619031828062034450783c99903100020720306240100070034401643c08038500103010507402001001c64000c12150b4004241c841c0b0340e00304101c0101002d084c103d80c0250840c00e0040b442d601840300b04000c3d82010b1003480c2074600304203000043c0c40d4a100d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 524228219 1250 524226969 524226973
    0x1409090901050f060f01090e0403020a02030d0f030c030b0d2003010f0902090a0b1c1719020c0306090717191a01080a120804030e030708160807050f1c0803130b0603 72
    0x300c416547d0b4071180003400c07681c5440c688040c9445900f41a070520325590342c0650140211002c403504140c00205c050b120303030b0145d5010003521280940440803200720400c1c4035448044405002c02040517059000c5d0a03110700300041004d2000c5600081c00c4414082c4142e45c007949650a1505600e002d200c2d4641c040e00561040c8208664940000c0d03d6030701808165014100c0141140144010705281d03006d2050f280c00043e030344d0880b6404242400d040d07000d007040188600040119141000310f002030041d80e44000034688a802e0031140f0507258805102c12001d403188400c14a880360146480c10076844c0940c0c851540000318040d02901104140c04c0340c085075210040000c0003070000d061a1000301401e20b44405507481c0c92900701e5110312001c408a506108072440400c60ba0030101d0299880107010309010606c6075a50300741a11060b03284100e84c0d00a20310755440c411814044c07514200304801c6a2100d0001c0c1d010f03600c5024940003650403c20030341d4031001e15010000e0f00c0e440e9540010342100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 524229469 1250 524228219 524228239
    0xf0c03240402060d0209060a082d06060c010b03010501090c080106030209010909021c1a0102010b0a083406050d0b011d0114091c0201080f09030301061409090901050f06 74
    0x901610800000c1c00080c054000082d8040b408451681610719403d00101102d80e02c00100400820000d402c0e0364031460b1101003620520301c00781c048002241140100034403031503503490504220181d006100889007a540b61022031025907030a1003024042c103000310300040c08203c0b50f6030083c0740d0403050304400c0915104200340085aa00040741d18102e40302e520016941305046481c9501440f07004a4034441d15050000b40304020790100e040c85100b503000e0f070003040a4101c5401f0494039501c1441580c10035001422490b48101099004610f512580d61403002c55120700300e00d842c02148c1580c00035000403400f080654081120740038001612909180010f030b051400344c558806030780500c2406e814002e02c486414454280c0805480000c0d00042c2054680714249a6140b0071050010040340066898400129090049295540101245001141140c0c01d0001c240c0c1c10810404084070102418091400c840d62129030940c8140e00000c00440c9c541440582c005a40802074000c03445107035010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 524230719 1250 524229469 524229523
    0x1502121806090d02040903030501090509031611030118030c0b0c0304150c1b05070815092113032001030219080a110c0f06060d0c0618080f0c03 63
    0xa00c01440140e04440d03003503440394400c000401e40044550002d4002d400c10a000b000d02d40c140e80140d040343e1001c0070030b000070794505181c26180c0c800e0020306680419050306088c08100b406803484a41540940001902c88051321480d403801c0301180101c001581840380749080040c428480c54012400000c0d2038210b003060ba5402c207101000a4040c1e101c16501c03510f00d01414801e0303c0c83c92100440c00f00c05221174117241000d50320f43d00b00c2d001300c0440b84205844040d0f000071200780107100b400d114010700364410302c0010f01c1100c0c0441031600f2a0303078502030101c0ca2940c80060019001035200710142000199440c9100300c1c03e820040e4810305051050054061402070b55040c01e40350403c0d0324000c2c0c1d0682e24240700b00c0084c0004644012084030118450801540018005024098140c2120580d0750749008110014115520040c41d00380b00a81c03c0055030300403044504684c50002071700b039065403076116040c5090310300301c0910720700d900902d40c030742c007a0030240900c4040c0c007a00c09a0000010742c403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 524231969 1250 524230719 524230747
    0x1801060506030105040e070504020d02040807050604030816150c0e03061f1401030e12070308100807030308090a0516051305090304050f030307080307090906050f10030507090906150212 81
    0x511800d80651b4582c904003800384414081d2001800009008544842c110341000d0000e4100d40a2403a180c801c1900100d481e01d800016a401c0344e5001680b2440c140039850580d030b020250305400c03074001103500945a0100f4103401800325034101a980c17035603c10082c9007010710701500509184d0341d101c0d002c0c60703030f1104034808030b5600c040c0e5000a0b20248a5090800101c00401d20b1401b82d102034014260048052018140107002c000c2c001c2d5500c0e01c0c162034000c40b0301100310440c4034a5040ea4801d800420019020700c4d0070a0344218038030207480e0049080d44400e41840d08021750710113000c04140c010b105500e03000005917041000c0200401142c0380a01e5141c1c0d903480f0714003030136204001d0003400c40b107141d0303041045034820350380140d209489003460200034158903424040c141801d42050400718160034100e44200740d41100030031041e11070483d00010350040901030b01307a400f04a80c1d1440822462442c3c0a0310006000c00ca810860f00740c0e400500a04005001200700104c1008010000c03800c03183c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 524233219 1250 524231969 524231971
    0x918050f07030c02150612030d050a0b10050a0e06040509040b0a05012321100515010e01121a0a03050609100b0a0e070512010b03060a0807081203060402120906180106050603 76
    0x400c3c035641c0b8207480700c1b000200c032a4890100c000b864030002407000703a40742c40c80c0c111b540180d014003014050084000104002241c503502050000b500034851690120310403076002c5003464018150519242c3c40d8070101d16044d0003203600303030307000341e80340050001060140c4030b0580140300d0040c0a403107034603045040e2a01d00500f0b6a103d445000001154802d0b0711425028bc4500c02d4210104c03041c03080c0c5442118007500c0308894015003148805101c5030913501620070010a03003816510044604200c0403202c009100307a41030b01e04004080b10b0100540d4850f401c580b800745001d44000e01c1a460300c440510b140c421200c80d100ea03043e01b41440d8500c0c90305d880c88010709441d011103141d00c0e0359031001d4045802d0300403000400c0403401c45200000701000c3d40801103000311800d8421100064940c1c91965441c110761240e200c440d0305c00225942c3c5030300f01402554200310000e01c09841c25408483d0032403941d00030344d01242c0d1504036a00b80000c1b0001402c0d00c0c0c050500e0740c0000c6c804903191000107030840c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 524234469 1250 524233219 524233243
    0x50c0418061505120715090f06030c0c06180501060b090a180b131a01020706020c0d050c1203210c070209040510061e0b0903120a0918050f07030c02 65
    0x1842e00300440000d45614444400707404080c002445440c101a01c4964502c664030070303a0800c056031901080000d2140e64140300381e03514044041200e0f45448811001891072220441c00c1005c049607500001d0250700402402184114001582500e82c4c1060380c2110050351051541c40710070450301142c1d4881000b40d00407034040b00844441c8807403106041c006070440304002903210441540085200040e03500080041010080300400c00c00706100683e51100740e80100c01c0560300c0000010000d02e0629a42862648142c0644101ca5041000324401113030030780501d142d603080451a00c1e00d4000103603450941d84a9020858410f08141c11214010701c41c260010f40112a2440000d09110042210f501e8228003540d04002040e40d824544007441c1c10a21220315406400070000b400003690004d035190754400601034501000c10030040380030340e4001940d000920104040c0014001001148803d041045002c08591031400320300180105c0340041050702414602100100d59682c0068030b010a98 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 524235719 1250 524234469 524234471
    0x31203100609150c0f0c080a0b07170a0c0203090a0b0301090c02030406090e04030e03030c070509060102011a06220807080d0801120b04020303041214011407360b07050c041806 77
    0x403925003000b8950089001000e1b102010801c1c1c0095004400600407901c5800b402e0441816220000203c0d01070484102e0100d00346030f15000b00d500081180d0101c0203041ea1030040320300c0d041924004c10303040ca20581c0310b82c2c41c1d030201000402510307a490041800b08000f52000e10326260420341c01500f04401405850410030115000400b0540254039100382c511005007101e4990442c490319035560903d074000d95020b803031218046103541d401402040828056a90007001078181380c01030082c0340c1c00c515010f4400050050021818000009902c0094104180601a55400c0c00303056480c019110340d041d02046811801000b485505e423101541ca594031480007030032034459000191440c0180e40025102c4111001680c0421400828140700c504001e4001c0c0000703500c044040790810701c1255480040b035102d54100e0721203002c140d940480d00c0301050300c608042d410079002d0200131078540c0041244940020b081c1c03040c00001c00a61705450001c0f02c00b480308400841800e0103981290000805407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 524236969 1250 524235719 524235737
    0x50a061107080d0b030714130b0f0405310b01121103012c1b09041b0311042423101806020303010303080606071103120310060915 57
    0x102a0341161511600b00449039240c03066094444000c09800880d01e01c03a10400c0c0000805c2d100400342c441c0001e800502c0307031000c9024420031101400802240d2540f060020b25203844c6a40d8a00c6160300814031041700d051310101e04c102c09064000041c0300c1c503504603613154203040014a9041900d0540d81c211010100071540380c54503005020b903114440390303d94213102000f0010b1907441021a142042d036403420041c00d010105040d00d400030044c1203850341118001c24941030401c0c00c44030b07401c41c0c807440c21082045c1360701e851403800d480d068100710342c031203403640311148180703003a000340203400c0103030b0359000040040c040134030241404510640c2001d8038030528410540e0a02d81c40e00f4210f40010f0540180401843d10040c001d50040b00d554412260346200070961720320000030303241641e50584908104c0e8840c40f082000c039030420401103070362030004840b280c05030f05c0a0143c4c44190300e0100029403030341008400511240c00d0f41c1c20440410035094030810070398024080141340d804c202d081c44010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 524238219 1250 524236969 524236991
    0x8030a050d0b19031e3807031506050c030403020603040215070305090f06030f0f190e010c0221091306210311010c080109090302031905120609072024040519050a06 72
    0x1500a40380300c05c07500c10755040c07c100c0b1242c0c26800c843d8011602c0020382024548602003a50310b8001d442d0b0b0841590700a000500050903c0c100554025000404140109000c203d04040e82e0380062000c40010380c0c0800c0102d003d04002e41c200168030400c6901c1801c6180500d503801011a000b1312a80da0500a0808030b0b03000d90203010320081d8a40e600701c0c01d00840540005103806412640d07442c1c1e005205069001c8a100e0a01c4202a200a000344001e450302043c10100204030a440d140040d00c02d0341c50400146404444036100b030005000d0710903000f00d40107400c0c045d00c41d00d90042e21601503410002031061340e07a80b0080950541d0a0b140c00040e60001508040f13155010300c010300c00540801010b02c03800d25800001130203c01c240803641d1403460759880d0034031046950581d180404141c8042c0900c810303150801d540010611030340c045402000c641c010300c4150304166030040b00014031480c01c1c4802e11505105901e0001c0220030082c081c40c00319030300c42c2c3d40c8044022028040903596540311030703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 524239469 1250 524238219 524238293
    0x190903050c0a030e09100317030c040b040305010504020f030606030c061606060e0103061a0603060d051005100305010b030303010806040201050d1503081b010608030a050d0b19031e 79
    0x1c0d40d219248112100d20003507150142a508410361224810b0690340c1c00100c4c02d5000e000c6000603179034890b1000c120300041202c50328440c0c01c0609031100942d000d00c40030030050030010140c401103006000220301e6080500501507031540c01c81455000340c0011040189607240040c001c4605001640d207180d40302d07600864101c0c4901004c1e80141a242031000014100e4819241d49050701d004a00401170380250707140148910b80030b64001c81d00b01e0750500c001394191801c5004030307201a0199081e01c2c1c403920082c0d1100100d13501124403000b529501d42090043c8038092051011282040d0021890f550401d03042d282d80380401032000b4100800050040b008101581021041500b50680c507000301341c492900404940040306c0240b0135044015444100c1d40b0140500405c4403005e0015615040c0e00d03180481d0750b584021003940714640c480803020015220b884003d050050300040030005a411450089400c00007140c0f040a01c80000c600319001c109035041034540303a030720405d140c00590500c04003c0c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 524240719 1250 524239469 524239477
    0x5060a0509150a030920030703111909020415020a0803010902030402060d0509060a0c180603022b14013006060506161b080a17090a080c010f050319090305 68
    0x405071078001c240f00740368a825410003215140324200c0c2c40b2043c0720400f4240030020038044011b80c10750012401b0804030301040a6001450000fa20809080760803504144030100180e00c1604c0080c0d0024041140d000c3c48441981c920300680301411494403a6195120540810300038218501d50001c00700e411541c84e80e08640081881035424001464070811094030317008216403d450860401c1d201405462047c1c01c0340c0e05042c1034a81400c00c0c0c0d800c00808030003d40140d15900311030341e0440300c002c03002c082d2900e2031200041e0b079a20102d505e27116000252040c11060303020003801803581140d80031207200900544c1440100e0381580c0310950303142c00d042c3c0281c82c00d5440180c210100081080482060b9100c004219005450740f2152001050142c05030300654450800310f50400c40040380026800200e0b0000dc071a04100d16080c0342d95000003580001155010314131307540c0811902c9100e5600060aa490074160f800c0042c00c0d454100e144c003400a14030781d000c0c420a80d0b00d101c1501018003807000d071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 524241969 1250 524240719 524240749
    0x80718060512010911060909040303090203010b0d0c15050a0906050708121f0609120f060902030d020d020106121a09120d1e0c1b050705030604060b0f03010605060a0509 74
    0x98920300790b8034803809000305800f2400382c40c08000c1002c282d500e811300508440303401c90058207803010f0380d450352411001409402c5080382d16540703a0401091556902c051843c4460146940c160028901404034244050b000c21040c00c0c00010300032a2070250300204030f0720440d400c2c1e0030301c150f66004030316040c01544200c8081d0350b0343c1001e200c10310484101c8801007d011050207008595484d4407200150752100d650f1080022071031074827103440f0001d17451123405112103208820104002c005980002e040c20441984480180e00c6038078840d032440d0342400b48500802c4115020700c070b0145a6261844541d800352041242050928041072076000308100a0740c40044042405444d00c40c038010300c01c050f200d07041002607444114882c086480d603540c07159011000c081c2c2c41e03890310303080e0001d00c8504e106040101501c803401240000181c0341c07818499a403013980301d03c0d000202c07260b00e1020000c194002200d07030ba0181c2e240000611940d290641280c1c00d415050600750748401c141c1000412003c81c0d4001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 524243219 1250 524241969 524241979
    0xd1709040f0b0d170c1c120608102a021f0b0d030c0809040e0d0e180103120c080307020102031803070c180f090501090b0c030c0d11090402070507080d090807180605 72
    0x420b031078501060000111088047d902d0412640c0c045040360151002c40c01000b090707130006801207040009661042458248108542100840310b10b00211040d0f400c0340c0000142c0c100c8000c940e103403c580e101d5070f5501d00c880c0e101000300040c45e0000c0b4003503d5035450000c003481440000c20081c0200101540c2c11494020014090340300c04c850340544840c1c980706410301007880301440d0b11041c0340c42054818041030641200c21281e10310b4480003000300c524034007030007401440540b92000c205c2800040d449069281c001680e02d0030b000003a0305100e1840c4c0040c0025800900041d000241005855011900c40f26488035005245e003948400a2000c8603012100310310300884081005019080b080515010340420035181d5078030f07114071646120880b26015103000c10407040c40d915a4560200300c0c0e244042c00c5003800d2075456008102207a0150009484a40c4064410032643c3c83c200b014036030015291504003481071521038030030754440c4a400340300803100189001c5da00c0d040d0941e00407402000c0c0140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 524244469 1250 524243219 524243233
    0xa0317181606180608150607020a030b0f07090302210f15160206060604061202070f0807111504060e030a0501020a0f0311070c140d1709040f0b0d170c 66
    0x11052001540074030440c0c0c0410390481e2607810741c1d0440b0200c40c0413150385860b030f1451540c0c4c2000105280002c1003603c0d51000060041402684600d201c880282d4031910340e191030ba061042c001e403da190010709400811045c008140016140c1c607811040d0031500c0043c1c20381e2200c2e0510720360b003003001045220704a8072400050800d01028040414010004e00052044503030841d0003c81e10b6440840d129038000b402080704205840c42400e244201641c1c0030801410401c0a80c1c622000710301420b0203460040e008110035007404025040700640c081c0441780c11010081d54020050540a00c2c4988010b0045039800d91001e034400748100b0300003581c490000c6544501d1600081c004150403400040001e11317007030380d2490080700c100840702c083c1c3c4c000c040b030f054845c64840303c2011052002034440d000001501c2e16030000d4076400800105801400d016525401041c080c003044a622030600c0201c00c0c148400c072941038460304901c0ca40c003074000011444010700f28181001700d1041501079141840b5540d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 524245719 1250 524244469 524244493
    0x6090c1505090132070309080a030c05010507170a0903031e02121807170c1306060e0a050a0b0a18090b010e0402030f0109020c101103010303110a031718 67
    0x51022040981341d1462442941c031028201c0180d03294400680700034414814884c140c01e801611095200345030070740e04191142111800d140030181c0840c04580854040e40811030213000b010341c4451149482c0d904104203082d00c1e0a41d040141840440c19503031515002454402e400000c98105284640310302000c50008031002036014a00c003003204d4441c1300220b05500507102c0104d0031440d54900405519040030144a4000f10108055615100d1178044101316110b10580b42c08003c08400d002545c145089005000c0441e0a0343d641d2150054520078000c2d5034170b0303100800035225046070742502c401a031201a1000c01d9101000400071445500002e031449240d04070300d22030102079960b20302d00c2c88407406000c280e000c10380e0304d41d40815055006000c210055405402c4462094003210748584038040210200c51352040a808138071030000060050541051400e50000b001100a02c140350081c2c50003400d0f0260f002c041f0380c105440502080c0100080b40895884004007026540064411 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 524246969 1250 524245719 524245727
    0xc0509031209010c0b13111002030d0506040b120604060b0406030314030c04030803041103010f0e0a0b070e300309030d03020d0906020417010c020c010c0311030d0203100f1a0706090c15 81
    0x6030040341c7c1c01b40400f250754a1414603500030460404140c009500f818440f00003003015060040078140c00c140c0d50401c2040315a5100710317040c1d00107454800b52034581003c4c1007000a4a0240f0381850143c1e08101040001a0380310ba030320300e5000081005151030781c90300e4000850902c507a0b030000d02140c402000f44410700c81209220f003032545044000f0850780017080d158005031150001c83c600690005005100455400320310f8980c8140c0350b25052905801c1d1000150069070982101d545411161100d10786001050768075101080070b44005505017081000040e58038a0310600300002c00d40c01007449600c81c2d00681102c903005074025015516113840d4180c02107a90880031007008650308018031030071282d0002c6407286001d031061352111800d090580302905d80b02000b0a120410344820005030310611a144007440c050b0301103100b80b240803031510740742e2442c40e51107812007220408a014107a5003190788a003201c2d0026407000010900e280641000da4000d81542e1251f0030441601d14088440da0b40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 524248219 1250 524246969 524247001
    0xc091e0b0d0b0a02070f140309040b03060606071506121a070903021e0607050109030c050607020111091e09090c18040209010b0f070f0804090c0509031209010c0b 71
    0x28a10041124504040400c440c1c1d52a510001e46048120000f0484000c125001084d0050080c1c40a07a44510b07183e0710418520785428081406070030101d0400350b035207000d00403480c14400440040101d410680001140752240400042c01c9203941c0c0407042c1002c01c507400c600700030844035034500f5207036441e03003820100103030f81c1d0460f2042c441407030740061541d40c020000042560380241c108540b074008003200d000e002016402c400d600001c1844a1000503600340502001e10348070750f64003030000c88545402d5140420107006071042d641403881c1d890381c8400c6002560f028810450b600d500c982101d41440c1c80300c8242405054004083c44d00304013040700b000400120307040060354009890030b80700850b8030005a069a001f03511070616401000003a05140c05085109004013000340350800d55581d143c00900707080000ca804a02c00311342013008500c284144410b00f06e250501900e07102c00c1800190b12900b0100851801030004200d884643e4850140c2054207a0300001c100f00600780400000340b6108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 524249469 1250 524248219 524248271
    0x70e0f0f01050603090715050d020d0c030c05030f0403030c050f0304060b0109060f0c1106210604140115210e07050a061e030f0b0604030b090f01050709060302070c09 73
    0x1403040001100d080100440b84910f0055015040035414480c400d822005024a0002004010700000c10290814402450315641ca400c1c00126840144c070301400b0744072840c005c24107010051082050441401c0a0503511a5040c940059880c0701044240d455001d06402a203640902100b0801000340650086da0700304000d8888030307401550b4640403540700404001c1500003503200b64400c00014640c0811002d4040010459410a9104100390550401c012501c000e00e8200b5002e00429060620504210310b050000b13940c019030400969014803030b2011942000c10045110180180e48940c0c0c2404246d8000e081c207101502c02984043c0e40c411082c020710344a160f005000003030450041c0b5002a419010041030751f114032840c1401e60081041c410310003023481d240e0111400a0351414020009148140300ca02d0584c01c0020700c03079140403540c0000f0b41a40c1e241106010765190404694400c0311110703e40581d4602072441c112001e0601548400005820030381480e50178607804141c0c000b504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 524250719 1250 524249469 524249491
    0x306090305030f1b0a0503062103030f0a1112150a0f0518040302070509090c030d0504170601050f060d060e01030b01180c0c021e190815010509060909070e0f 69
    0x18a4082d03d4248035513a070018001080410058500440c0c0140041c59100c2c400809a80490304040d550742400401e03042120a260000810068034045260807560080c041500c00c105c031540003180510640700e000041400748460300c2c002001000f0148040203400d0019100e640102c0d502e402100281c8440d000d501c0c440c5840541a14541160184851050b90194010a81c1519000030b20a084c1b0020300b80f034405010b0347c0302c00500c1d030300d040003d4080701550f6916169a140f074410490b01c8020f40113403041058100100410151782c2e15940218011000c0340e583e607507141400c4070200204401d038015041c5204180002082c4029441c2c00b50482e50b240c001c055080c00407415a80c1210100001880170072a81c42c0d4020250070030840404801d50742c1d850a032400300140340014003074225040524108443c040c014000c0030000c0c0302100d0508007401d9400c885505010010b91600c0000b0021401211098000384207000308101080c0100141c10001010341400400c104070b03600100c2e2240e02d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 524251969 1250 524250719 524250721
    0xf060b03060f04140703050c21070e10090605091804050f0d0f08070e13050a0911010306053a080702033f0c0714030d03051e060301060306090305030f 66
    0x1410f19000348440e4035110881034541c1e0342d41c1d03003003900144030183c1b009041f494140001d002001c815084946041d204211003042740c600305d00010110103034880c0c0c0d41c8c0a0045074082c0940150002100416039800d8100542c03990045804900c00350a1442c0046034942444180000e0000114800001060250035036002d26001b92054030702039843e40c680000214010b0000d020380c0d2140349a0381310700e8001080780000380815440c480035558148e4400d9915661008800d04000c0c049820f840d4410080c2418080e0500d05400200301661000d100d400040c030200d4014048808034004809016400680118154080c100b41c2061740040e03d00320701038441d400d541803401100e038000303621810303060941c541141c5144003020030203c101c0b43d11718001c98080c003100801000c03c1c0700c00780150092201505a8032101020580740c0104048403c0c103252601007400380c902e440b05424400311001403200209500c6101c0401d00418050384040d0072a03150524803801c1548c08801140140d0f06100f00600c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 524253219 1250 524251969 524251999
    0x200301060b0408070906050a060c020301021c0c020609060c040905040c030b01080d0809060609010b0702030f07080c032404240c0c061b0f1214040501053c0603010f060b0306 76
    0x106c1724580602030740306090103001c0080e10f10810143d60030610247c00503050548000700310580c000241c40038030f8460b03244c652048049604100306a8080031500c000c2403942400340d04204030b0700c0f07039000d086200350329240080d050060001c0d0b8a0000c550105a60a096075200912610f46150300b160400141c40b14002c00c00103100016005d004210080481210364030f0b000c000b070882e41c0701210890b0540140b0200d083c4807841030100000501d4218080c142d00b410060402d424195824020400842c444000c0c05c03280c080a10020340c030650041100444075103a003450109900698100140300b4140072414100b41d601801200d43c01c5c1c41400d00307020040300c181c3d689649901d01d13a5800001203030f662070404814428042a608070340c000c0c0c030000f03074014a90403640400400f01d41c20354a980d16107007481a4940080103030f20900b04982485c200c10390050b0100c0920001c50390000040010302c00100e221a81c00f940607508403a04000100120703551483d030340b82c6c15081120301d9442403e0411008117 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 524254469 1250 524253219 524253221
    0xe09040b09071403100209011106040c15050301030b062e021006080d080a050a0b040504050c0a0501020d020c040203101e03060f020f030c0313080f0409200304200301060b04080709 79
    0xc1091008002c5c0c040884500b070102c0080d00880c0c0007a0400290b0406940701c000140718840c056070264103072002042c11702ca165250020b840c080d2074200701c0c0406c01007011039030380260300303410a90890300e00260640c0ca41b0200d414440c842d0490510702325008912610300e800080780041c82c03c0b01c02080c0401555401c040e40c03184414080c01021503e604002080562254003040d40544103040000d050485100801c1c100d0760101d0b812143c40e8082a080c01c00e511b0b00442540081c0802d1000300049005000000e480c1c44076019a5405242c010003c151007000400f0000c0c00340c00c0e545074445000714403442d01543c0003100e1001346d4690b4906207240c28107480c0d600031640f002819200b050318544480881d29215071008151109840034101c03040b000520420084c11107404a00b9140c0d16103040c180d00c0c40c126050319180c0a80e0818010803d41d11482c43c5c000d595000b0b8010083e0150410480d142c092000000c8240c140e25500e44400031900962500150041c0c80313410040700e40007903d56075520 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 524255719 1250 524254469 524254499
    0x60f041701020c1b100f020d0e03100e07410d1a0f010801020f04031b0302100c0b060a050d08070c03020a080f010513020612070528020607021203160e09040b0907 71
    0x380042c0c00c07a03908d11908601854441002c084080d045800400010a0000456049040040040c2c0008500700a580c0b10700304880044182e0b00d49060017966150b80f0712000c0044401900191215000d80000366500c0703e1040f40e01d20f803c114070210300001c2020961126000f04c50b200d40813444440042280c0c8414402c0d10f221003c4000b59516050450721030448003520402c5c941212030f5408004070040c0c41c0c00414007444a1541c546010540240c50103010703031a0018251401100c418404216540e01e4081c3e562603144c0108846644003000e060031176540c080c68102035003200c078103480010f15440014030881c08046100007044982c85900c0c0c0110401c80f40100070354010381c14442a01100143c08a40e030300030700c9904140e40b40241d41620301c04180603151160150101003a110411560144400b0b640044140b000d84055060030105031114000a480101c4a000400c00b4051090098650401f00500141020384529292074170200e031187c12544502d00c0e00508900142c40e82c3d240f0840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 524256969 1250 524255719 524255747
    0x20423130b210a0c0602010c020f0303070e120c04090813080f0706081f060207090509010c080a0f091407080d021c0f2a02040605060f041701020c1b10 66
    0x610501e20388824119018261540766402d103000e411000d00009008014003002003005800129840e000e4100290512292906844040d0020010000c2e199480b40e400d000e0703090101d1301070311070f00380e1013510501d408107400845400ca490100e02106100301c10740681103d40344559141d1070b090311224041e071642a450b10f4082503501c080b20600000c1d00071000b49500c4440c0041c485000d104120402071000155402400903070845d9a0a1180400314069a41d00c1038217817000f0302201032542c0005100700b074024010300c09130750b6139400d80844a5003900264055504403007400128150341710802d07141d040038429501188a8100304a8805001142000310046a40076012541c1800e40040e204c180030327164420100a5941120f6800502004035501111000e85c00e41c0c0c0c00c4003c51052008665081e004107118000c02c0c04100120290342c01101c0c1a1a49142c6006c0001d0034814214064080c9010040c080e004112075480c130b54124490444540400b143c80e02e803000e243e0799040c0ca0801e600d4a02d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 524258219 1250 524256969 524256979
    0xb09011e0b0a0e0606070f03081f0b09130e01090308010807080606090c092202132102060706150305060406111c090c09060b09030606060901020619020423130b 70
    0x100701c002030070b1041c0f99010700050071131071522000b07076a95000d0f5160300c0005c4022546c00824094420070205461841c2d940002000503090b00b0803e1104090041800040c41040402c88040c0c4e4145030b0f030030024100031110300903c09600a071401400e004801d00914000d0b10a5200004840710300040c154055400581420025195246a01003e80c40414101d411a00c09007141400440f60408001c090a103c0030050700c8040d550440c1401c19480d6010700e0010074038401c1c01c800350280d0700b0f01c0200f542e4122401d0380d03914043c1c40c1c81000342042402d0002042c0740d00c01c0000a014003c100540304078400d4204010b500c181d90b0b449503043c0204002c00c9902e0075000001d90005840350b03c14420280901000c5000e603a40c0c4900c1000d803075071a08000c000c078502050740401070404000341a003140d01220403a082c1900000002d5036120014600c204034000344182d020312841c04d80c11600a030007841c01c031075a5800c5020700a00c80d0000047c0c12809a042200c2c41c03248070400d4400c2950444000341 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 524259469 1250 524258219 524258239
    0xa1206050f131b0c1b030b01150327031b0b060d030c06110912070b1e04030f06021908041703060f090a0506030f030a0e090703090b09011e0b 62
    0x10074010800050100c002d10340d50b03141c0040d461508100304a941502d899680c0b840b149603503180c424550100c41140442e0078072801c10900c0001c0c3c1c0c030003015064504490440c0a02d00c942001180600b200d01906501c1c0f0b1920010404c5044103040c2c40091140a41c03038441e510801003510040500343d50304c010f0200c1002c0000700d0158074101c8804840640246000e480c81800d90b15800d080300d40c00c0c1444a041d030341c0000c11101070b04040c1d05820b0051424800750550610b00b01407000c880c81500030003082034401001d000300011114007614091900f00841060384070172403422400039444405580c0c800742034030002e0b1040600c1140e5640c425a0f0000b10b082000c00301c1030f541c0300580c0014001c140d0000c0c41040845040c0c1b20010000d100303000842c0081980d05121040c90700703100d00d81030b00c840b0315017041020780403881e0014019110282c054030720425a40c3e0b9405d040380140701c50380006001340710000c244124008150000d0030a2000c5002e07409d0110000344c1d401e421542880312403070300064000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 524260719 1250 524259469 524259499
    0x3140901091715100303090e0118020703170f06090903070201021207170c030705060f15010e01020309041514010c0206030f150904060b040501060f0c0b0a0902030d1e03020703081515030106050a120605 88
    0xc2c000d03011340dd00c40e06110110300039003403154150b2031b404c45000312140030880c2080741038035114403615003180420006d9840e0180680000707448035550f000d00d52444030700003806002c00c0780d61040140e0042e800380c44951140360b00d500705030b169880190306441520403100480d01110034038111038000c0c2c3c100c0d002480358040b0400103442c0609101c040606501042c000041c40382c4460190402540d1760241003200380b070400c100c203039007140a40780301410003828001460060715250f084030341182c00c0c5010a01070781c0d036000701d80c510090400c2c07950b0303003203030311135080c403040203140c0e00300c09030704c06007168144110380e01c4032801c40e1810300c440000030001742030051440109002c040c5140d00000e803034001203045040c42d00481d00d0038041403603880014590b00c9415200ca500c1050780d0a00c10020701d0294501242a10010150a0060801e80c4241000c40018205940d501082400854000e1180e80c403580e440700064007980126501c0e45c0807580c0c96070700120f02e0b181c81c0705000644138014400204002d46c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 524261969 1250 524260719 524260721
    0xa030c020c060702190e09071d0105181003120c0519050d030b01050708040b0a17040b1501020a0203100e100509060a150e01030f03140901091715100303090e0118 71
    0x1d544d0171401d00d00e03094045011910001110b204108440c020150603240c1406d00034000c00200c0341c0c58400068000502050360752508030003110304840500074880d02e0324600c1080540c800d61000701464401d00c034100303140390000418a000c0d40100d0030340714041510041c920790b1482c051001802038020b8103200154034041e52081c0c02c088010b26009003890001e98414015034003503081109210341c0411801d06055015500805215504280e21000d081030756550400c250090802e00301c01e10a000244950307442006144042900103080790141702d240088540200b5869085000c14020a6020f21041d00c80c1c0c001d042c098201e02c0c004120b2035840c49241c1c0000c0400000c0740c41d805440c0c4000240e80d040c000c621a01035400382c0c000103041865450040c0c011800d0420301c6503407c0b03041c0100c010f5030703802240400486250680c41000e00740c0b5013115074106150a13039a4400d011401041c0710404220341c4c0c2d22070a5074469100e040703101c4d45406400c00075041c00d22030402c522401c02010454a011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 524263219 1250 524261969 524261989
    0x604060203100b03010308120c1912020d2a021b09060d080403030908010b040c050a08070509030d020604060c020303270a0b130501110f0a030b030307170a030c020c060702 75
    0x41c5800a01540d0b4440e0143c1503254020303481070703c0d241030101c0c1d800c8600010080c100e0300052644000b40c507085010114200580950f2100002e0011110b2221041d030070a404540340d1440611003004902540310501401e17003004948003440d0011034850000c50b500005032904103207484012403035410201c0701042120107000708000e40081c0c02c2a48980058801001b420186210f510b0b20112641001700031403c5901c580d24480c402c908184911200d5034000c0c00b02c844d60a01c511b0705c0c20080d59200d41c00e40300341c403902030755682610808186d00503542c0c0c0407035a20b0180e403240c9014894409500012603580c0016140490003c3c0b07588901600d000c001c1700100704150301001650085011511924034084c011202115061603607070805003005403e110340b002051b82c214502d802d0140707100000d560b6000b00000c1005155443d14402e9040d5030401c2682d072a03130b034015502c003104007108403103003c030741c100c80e240c0300200303052510065203540045000242020301800c4182841680d408110080310 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 524264469 1250 524263219 524263231
    0x6020f0f0a1707052a06310b071b14030703080604200a2604050f07030c05010c11060d090b01090b060708070204020c0d0207050109321f1e020c01020604060203 70
    0x41035100748513045c00c00740724081c401d48a224000c0312180c401c0b460140200c0080941c41c2842c07046221010000714185203d40e00041c00d854080c01d00004030007801c41d1034925100c0030740713201085401b9507000f07080003001f0300080b40703c1d6842540f16114081404180c80300038007140300c001c02c6c1d040400503803890b08010740583e1240b0f04d01405619240d129041405e4105038440700446c8a034010401030103000c1005403601c1040368000c103049441c6403208803000c0c6181c0030b000e0400c801c4542c0c950501c40c481c1340f42409684020720240d503070000b40303427910001d05404008451890943c40000741d009001c0c41542841034000d0495441c200c0560360741d40c056031120a0499201703a0034042c8420468003000045000341e402c4c0c00030314800e400e04001401d241519405242060310034100f80802c1c0e5908845416011642c90040201034170a01c0001d0004900c01d988048c000100c3d141c0300d54a40c2d218001080c20520f240f40c90b01026140c142c1240c40314540000140964031890100b40040c1d003079030045d07500c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 524265719 1250 524264469 524264527
    0xc030a0c050a060f0510120309090b031608250b03160306080a050c0f060a0c0206030402060418150b03060d0b1801020403061a1c080706020f0f0a170705 67
    0x2042d6a00c2104440c5260180c0520325511030800561002c034800c4480a005145986030002d0420b9500800c10700c0f0501034060400d403a100c0a1045403420041e0a40d94003907020b5a04085440c2c030354560744c80c910044110524a0a2484064401d2160f03221800340c41a58607503a185a0350041e0142d071041000700000c04140e6907410004031940144000e2458920803005010084191000c10503c50382d10380b14107210300300400c4003107003954120000c000ca030741d4169686074130380d501c4d0300007d03815018681c003000300d954001c0c6544641d6540c40d404003400b411644030702110310391111005140303400125a41508480740070b20000100380f840041c2c40e03026058000c141e50712403491031014203a0b0401e5004039009626481d8901d1001c1d2042c80300c2000d960240c8114000b40701540110b60071154201c0c0150113003d0015100b014081150100c601c0408451a02c50342c0d0418451108080e81c02407811a001582c449620507006940e04846030094111b0fa42e624100881407050301d05048104e20001c0703880c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 524266969 1250 524265719 524265733
    0x120705070213050402010206011a0a0e0d0b01030b01031502031519181401080a030207060818010c0801170c060a030c120f1b0503070516050c090a0617030c030a0c05 72
    0x160b5440b10000d540c1201030101240c141031030300c000382ca40031040e0403103c60341d01c2401c0c000b01c03940c0c0040e0540b41d021440d45028900040c004012607401c07610100040d04125440e0004800e1200880200d8100c92090450b030960900000b041e000b00d00080d511f10503103100700c001190703091030035035003811016000c0c00c040e541e900e41c3c2c2c80da180041200e010b09840415150f1825400043c03105001500401c071a0300074000452180c0c1d4025101d00440c000c03c0d0a1200f12404100d00e90041080c904044003d400200305050340b4000c0038008000901c9403000c0c3c0300307520400d40404200440e10302d50f00d08000d429203090440002059001c0c002c40310030001001108400844401c425015a486000d1110300025001249489031030291100d40c1d40300052010030010b10800662201c2118000441c006500003c25805d20b810380c00d0102c0d40c0401c65100108034144001584c02d0f9121038125510b224003003a801c0030702040c1c15100d00640c04c602d180b90300140015401d66009418680040e8850b0f0162050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 524268219 1250 524266969 524266973
    0x30405100512040b072309060f04080a030e0f010507020f060c03070503040f050109060504080a0215070206031e0105030a0b0115020c030a06020909060a0e0a0905030c0f0c0301060b04050612070507 86
    0x80c0c0c4000f1201139a50503008800d0145a58001e040611410b121400d0600540c8000303d0040705445421115400b5100000b00d000c10b0800c000c003560042c100303442c141c03182c9100301d040040001008108003403040000c9804180598028421943c40d03580c0540b10b002407954800803c450303034010000c21007190104000340300010b541480140044e08081e21002e100c5800c107400105181c065400175014820100070500c5106400181310800990449040300d400c5000c20132265a03020303040c8020340040010040c4100803201204081603040d480b00206541da980d441055565007854034082c2c886c02084006000044155208039040900c40c012504251000e1011a15040307005005540c6c00d40d0210703014882d407030071405490304098100c8800c0611030400302000259180540411841c50351540458200803091041c0d8150303202020030380d8003040144644980390154002414803e5103401804615000720000740e4050746c0e400303000310f824820768141040501001405580600c0020301842c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 524269469 1250 524268219 524268247
    0x1080405161d07020d05030a020906040b040b0a031b090302040b03030c070b19090b0406030b011701090207060516020a1407080a031715030c062a03030403080c07050304051005 77
    0x4010807021001079860b500303000080c804000054031810454101d1076441008a43c464140c9070000c07030f1301c200160355245c50000201c0320711503644241ca2072680803070002150040100600700c0300b5100c0c2c0f800c0c009108a407040c00f40810070010405c0c0410040b032024405410144c0c001c0040c0140a001c403440c00c001034034040d16100040d03000c4a00744100242880c12106444115540c5440038200f12103403c2c2800e6001c5030a00503030250904065941d00400026842900b41c16280305149500002c0755840703c800c6800b030760007200d0680741e850030700000c14440040611815040061580503103070a480c1c59035072143e05025007074210140d100d40c150201e010a000d0041000140c400d80b108000c1035000181c1400761003008200711004a408225100d803a24007103034119845108032203c90760380c1c541d84e041c01b2160048400507482e0381c0e104400c82d902014004000c50241e03001e5114140142d45003001c4800c0c0303104941d402032450700140010480750424009680d8081c1c168100282440924200a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 524270719 1250 524269469 524269513
    0x1081302060307300b01110d080f1e091c05070c051c1203090303050708060321040b0c15010506160204020f0c010e010c2a120c14030301030302060717040201080405 72
    0x84021503560303005d84059030700f0103903500800300c5030301c064903070303995200006810764200400010b00e42034003500244511401d11300a0b143d402c0c1100100103141811143c25076a400b52406135035a01c0080c0d030040781202d01620035142510740c020060a0308034101014402004d03070b0f60b420a1a0011182c616800180c120307400b1101400007603400152066180c03d0040940704094850011703c0203400512190340c0b00404c40b6000b46820109030251303076030900c01c502000c4c452a03000309104c07800446d429040d138001180f141c541c4500240c0001d281d98a0f44e007005254400c1016902c0d42e202c40050820050034641c001d4460300710480030450030140c080518a003511420010400036942d1410305510994010b881c0c1c840e141c8284c1580d2100d640c1c10007103542d00741e8005074003074003254158011402a40c07040c0c485503082e1340d014000d8142149c00b001841d070799810a02046025001d490300043e0b00610940340048000c19144942c181c5444580041d521090041c0c0b041d1524003503e0800d24202da0750780303248 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 524271969 1250 524270719 524270807
    0xc0c0b090405010f0b071b150203071502030105060313050307021c0c0801020a0512090a020d05030d06150504031e0803100e220b090a06110901081302060307 69
    0x240c0d40da000542004120740c0141c01c8a980446030b003000303006451030103043c0d030810340e40001c080803001c3c51701d02c00728582c4034242d000c0038418225034228000396070301001074148144254101c110340544280d400b0140d0009004281d04007000b4000500d0b10321110603a40c034224000d1091700e1402d0b0982d0081040741625900303012007268081c040d403042001001c6564010480100214100480c207580204240b06068841203210071150200e145174000f40042c80072035600604d9103010005c14030302142c07650408443d601c241c078581074000071414452082010110706950360989490704590b04c01c05850b402c4207110000d80001c3d01c0c00d0f000111000c00841c0111400d07071a01076407600e441b440b80400c81000f040359030b02e0803010480c454120015507803000c405038042603802c09940c81540c403d10302405604080c4c07500f400e00d4161407200b10260018524028203a841c6101543c8060492100302025031340203400c07586c100300080324140f10f9889140603464840380740000c440038940014071880c80c8042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 524273219 1250 524271969 524271989
    0x12120c031f061d0904120e0f090f0609091c050715050c1e04050a0306020f0f030c07020909060405100c0509040608061f030b0408090d020310150f030b01150c0c 70
    0x3041070002031075150303c50000b40844008001e07151550b03d807920452502035610502c0fa48030444405590f0308500000c03418409015201945042030301512030341e100b40c0340c2d28014459007003c1003179000d011908a20a0a01d145c00080c280b400e030704101c405603c0100f01380e850385113038039074001c10142e5401003d009400b1090784d030351500c2c0012550244140744881422520700200b00411494840007401d40440323402c52001601c91880d614040310318480c1d480202d045803000402c01042c1b0849c28064601207000750381d0900f0a0b80d60304581d41c0d503a1019107000c0c2c4168050f071604c5248240303940200803118120720b1b016003000f004e0408a800e40740c40d034103e044a90803007010040c810001038110405440900400d9190610703584070301c000c8650140001c0d01e450800100c40085072580501060020380c09011907602c07481004806d0018026a9502d00d00340c2085080090041e09482c80c2500b0b6942001c0103e0540e40b92800d045482001e500014050000a0007040b011401c00c00402000700b01c00b0307036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 524274469 1250 524273219 524273237
    0x11131505091014040216050604031d0111031c110705010e011107020109060311040e041b06031a0103090c0b03100824010306051801180512120c031f06 66
    0x400c2040c0140c0082c1403603420710b03414100304812016210805074288095400590390001d041440c101c010900390058001c0c420b440c10b002c00c1580c4600030350b00601e20343d000354a08520000c011182d400e021100c11000d42c0c000c3c01404610300d200001e40740c40707000c161030000b40014000d131407449a8000c0344013502d2595480074140007000003030050200604485e0041d900c1d2092660000e00144514007804007010b030f441200400c900701100813607010b00601c1e000a242343c0f50900e003541e580c000046c40361054840e9080000b5000340680103100c4030130b00b0204200142c00c40900118010a4803030000c0c0c98200c0329400c005003101d8808001c40c0200590340318090042c3c03d11907501cac17070120554501000080003030100c4805e2216400401d05482d402000465107445051801c1c501200d4285400307601d510b0450282c00c032000040250400d07501c1001920013504c91104107071244d004462410380c6280500f00055014406a80210707400101c0c0070f2a00e1b50503403003600411008000380c00071008150b880d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 524275719 1250 524274469 524274479
    0x10606020c1e0607030815060f0a110a030914210105180606030706030f1b090602011406060f030912040e0121051b04091b0303090807060903111315 65
    0x1010030110010003842c15506042440070800c41e2080f4103020b410088120b0210303d000500311112038a07014020801501c4d4002034041d220250300002058000c1040541d1400202c400403800e103200e960152240b80410307107080414060281040803641e408501d900114041c80003903003014252040d490000a60f40c5418550f01c001400c0020807011141c1c0000d0401400d680c1c001500303415a145441c004c02d044070021240e1014100c075504802d1070003c80c8108510f42a80840340d10101d41d00c960080c070174115030200d0840980c1f016520310b50400001c0005181d036040348001540c0041a40c400c0f01c4094641c848464119085070b084110005a400c004100d00218050364080300c00c0184101985407845076a055642c2888088540700108469840c114581d2070342d01c061a40c40d00f00000481038003c0304024200b070001404118041060160046035154000401c902901d145803165200c450860710780c1c0400584244000c1e90000308009011000384103801003441c1171600010181c007043c240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 524276969 1250 524275719 524275729
    0x5010e0105031c0c0c181e09050703080c15010e040b0a0c0516150f0f0e01090b07030f0207150c0e03011a090a09050f0a15090c0509100503010606020c 66
    0x60788000c2c4690302004000720600900710203401e00b00d90a04105010760010318000c55a005e090344080c221520522904038084a0f64019042c400ca0400c1490610300c001030601040301e87c011f038040d000d030b403043d04148001600e100c001d043c510301078401c4500d00c0a5520180000e013a090300030003255a9004107000400c05034214840e0424400070061002e1441c00000034818000c4071518211910036104010510001d40103040080034403404c1406100e0043c3c5126014040103114560035514241c0c006480040620400050036808048100c0549454004801038407003400210a1140d007040380000082010000d50f1003180c074100d01043d03940b80d034000901322500c001c4400740240d0400440d83c4c08641039500c0601e00c1002221400d82a440340380f5510014071401d036000f003051103030300a2440c4000c000901c40710001d10505114100311141c1d0350712001e5504000380203242c0800000e0500441c50901120343d4003810110743c140c031941d5100f000030b0946074140d101d98056000f910a0740039604003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 524278219 1250 524276969 524276971
    0x50406080d0e0a0608040b0403030e03030a0e06010e0c0f0a032405040b0909100917030721020703050405091f06080709050607020a030204090311010c2c030601180e0102070605010e 79
    0x801c0b154105054980b800141c00c045d4000c000402070b02d030031130006042501035413003000791641e4181101d86903e00f0144800007448550f1043e00b861042000000c0c1a0100d806c06a02c1041c0340e4064a0803c0ac000c00100c1c0f00d6041403030084141500c44442007010314100041603910381d50000320403240362800342400110b503c20008240035110040030004c0c09940001c01c0714107800fa81a0009000480d804c00c0d0207010445220018218070000611604a0781310111101c1d013000000300c0003c0842a20b02c500c220703c911315000300030800600c4204080e1429501d06c6074000166000300c7e904849241e09184010407a0300f040c0080f4044409110111b03a000c00080090002500c005141403100d8000444006040c80300030700c6151113164aa04042c030a15040800a010800902c1520200c403c003411700c030b442c4204030402c1542110424040c0d1a014410300c0c0d5003002602504880c1d0804801c80819041c102200e06038503146d92038210300c50824401451014000c2500040f00e50411081d4255804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 524279469 1250 524278219 524278247
    0x250302041409090c0f01021906053120060c060f0903070f20060d09030f08010e0f09012004140306041e260d1410061107050406080d 58
    0x10b0716810041155000a03000c9410034040300c08640381001d0000403854120a0341e02c0321406d96480d00d80c0703010041d41d908180c0c007503c0c200300c0c1003180200c0706210782c10704580d4040c0440b043c007802030b580003c61802540e03161394483d43d01d91240001452000700d140d55021603c4d6030711a80c4007004004815401c800d0141d042000003000d94941074958641202c080014840540a03d24140d1440d03c01b8121442c00c95802c000504181d03291842c0700503903002000820700030b0b804640000c0c540f0403018030800405041e0b511942100300c1d1522a28101c01ca20000107280c82c94965803144071000401c1c0260600c18290b2008404070340d21400c216841d0520b0380e10417a102c1c060790103442800001003001003078400303c0590f85074584002d481400c124608403d540042e003030703803030800d8031210f00503024200800c1a01114801403007180484400a01d203007008131441c140e440014a0b050009a201e94540e010841000c8102c460340d644901c0010200c5540b13502c204203d5002a021030100741e0095801c1c88008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 524280575 1106 524279469 524279479
    0xa14030c0a0c06030b0409080d05040f080409150b2a0313030f0201030b0a080c0d02030115080f070f06080c09060c060406022a030d052503020414 64
    0xc40320f0241100090500c00160150304141c000c0380401a4404070303c0d450845081000b10003003502030000c4803030701c240c0d024034808501d000000d00041c18482c9030015031490207503880018980560b004c502c3c1c017001400811402080f5090584c40d80141a04e001c0400320070300612070641c442c1c07006014680c103070440e0101c1400400c02e0030044845c800e883c10803d040300301040040d001a944140032042d0700202103c5054140381444602c618405030010681d14224901200d207124141c0084c402a8001040da001c040c2d010880800141950f0070140c501d0341c14100300503c622030041900c1e03001180081d000000791507a008807000d10340d0800c2911110306107460454060b42c0000280b80903d1003c500454852046440c50f00d598104000154a00140d9111003405042c0041c10041c12015030092200c11448a44032010070107025600141d882d814a407245200001c0324090034090 = true := by decide +kernel

theorem cover : BRFrame.Cov 524100719 524280575 := by
  have h0 := BRFrame.cov_init 524100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 524100719 ≤ n) (h2 : n < 524280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
