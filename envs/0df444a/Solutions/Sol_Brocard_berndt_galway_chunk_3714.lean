-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3714
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:27:49.153987+00:00
-- url     : https://prove2.me/submissions/d18d5597-5ca4-405a-b4b6-579bb8eca6ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 667805755 ≤ n < 667985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 667807005 1250 667805755 667805767
    0x40c0e1201060518010b09121c0f0f050c030307200a3c2307090e0606011b020103111b0708060105030f07120206120405072402061603061d04060b0d1a0c 67
    0x641d809c150860010741c1c0340410740381d2000004009190410100c0705201041c04900d00032100030040d664081070500c0c0c41200281940440d041c3d0083d0780780d00800500481c2e10200510001101c0b440c011644806204860952507113503818002d440f43d4000d90040400c80000300254035183c055100c4521150111110400c1c180494202451580081c200643e2040207424010040c400e66500400c242001c1c8504052906280310306400c402000781010340e6121030a000310f40074010341d09030003001150540d8003140e40101383c0d650302c0d0340c0c081c1800601c64007000169500d000604a1800742102e00030f010340c5482d00742c644648481e02e101c01c80e401802402103402a0307608810712481136005000078941c043c5400c10400c103803c413000c9010680c18105196200e81a00040c899400c6103040e045029a51413a0400300d004011640101410710f01080320450805440d500850042c0d00844003040b40c0810342c402c00c413500300c0041c4000e222011000080b42444005114160301001740e8000382e150003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 667808255 1250 667807005 667807033
    0xd081005040612050f0c01050316140c160812121b0307050409110307080f06012102040924030b040302010908030406090b100b0405040c0e1201060518010b0912 70
    0x3089900002c403201003c904080c1070100c20001c01c2c4848142d0805854851100000204280310040c00c465182da1085c1401d840a8854940303d030034034510818181e1a00007a040381500e62401803150b1085046811000c1031001c0c000c12417014940342c0760030301807610104c3d41e520103003003400601c0c07049607009904a0000c0210f10134003c510442690780c0b65642c460901d00104e003183c25071a80d10306800400d10401c031080360004125604100685000200390b44d031780707004840040300d591082c44043c860744803076290701520780c01802c00e94001d4030041c0b26810b10b0340c018500440700640150520340d1040340c1040400c11480030f070303504070780a072001190a58081c2c40c1c900143d0300540707045403981d41d2808900b06101550b0240d0b0f4011071400a040000f42c0790018006883c041c1c0d00415114a41e90018680c609001302d0b04d03e0f404a03c080d00d4945038402c81c4070020700915583c811103000310240c0d034070100e2459040080f00d05031000c01c02400d0400429006100010b4143c45a41c0210302c0743d110030f04160 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 667809505 1250 667808255 667808261
    0x15080d0e0307060f0e120115030602040812030405330c0a14130911131706060612041502071a040201110102041d10031403040305120c0d08100504 64
    0x2110039200c1600810509040c90b00e042100d50040c02004141e101c0083c0d103c0e48210548107a110880e10403041120032484903004082c0207140f0341c0c440206420020070441980c016208940d0008103580002c1150007204206120444006006800440b40c91010580881c01007080c44c41c01d000c042c1008032441031030417403c40281c904e200003060204000f82540e5000418050400006000b01d0811810140481d0401054082c05d2481c0f6140d00d500d00b10902c03084151504c61507100100b02e043d59444409814442c403055003101203001b80400602030f400c241089611a40881c000c0c40d1443c1c1e201d0301d5a14030041c1c000030004600782c0800989000c581340070007001d01008500e0085000f0f06151001500c00714070324413580340b80d0b4014401048500c0315603a07000800b03282c4ca0070722070b001d43c3c0707512074102000141d4000070446203411603015600b40000010f00300392840388045410400d003191114629001d40040c829507540100380c8a8039083c814240e143e008610211040840b41d03c400014007030f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 667810755 1250 667809505 667809523
    0x506330d210e0a09060b19030f0911030f03030610030e011e14060a08031606090c0f080f01050c030a0b0d081c0609090f1e0b0408040302130b060d1508 66
    0x10607096403400b40b494030311542d100038058402d0422450345802e079440c11074020100d41490707102c4040c40e2121700c240641c200210079a40c25504128504080c941840d0508018900c0b600900c10f01e50390003c5008000101c901400f0001e040030585141c0400407809003036950a000019500c4901c1c1407246603115000c02c14205c02141c0203d2030198400325000041c000070300803403056504174003c0001580102c201e41c04500d40162000103003071541007a001500c80c20a00600301b070b18038000010b00c808500c0c08182524108801d60f1205110000220b098801c141da000715240005c0011565900180d80882400c480207084030325105a02d88560159400200402c03640481d010302c0764244116900c2104003600c0168810801c08519480e100c0300e810b02c40600800c11704000750030340c11034406520729000141d03003d6144280c42c546407070b001c0e01d40e4125120480c0039034843c0078544025440d900a0700c0d10741b100640564246130300c08d1041c4019212038506418042084d03103004c1241101403000c181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 667812005 1250 667810755 667810757
    0xd03210207030e031c0c300206090c060901111005041b0504090803130c0f0902040311010509150a090b042d030b0601180b070506330d21 60
    0x288451150a010380362843c250403042c481d030425130800e1101c03100e42c41c2d0403034184814584400d01c45020310b8007900001c000d4407205d40070005211858040308030a401910034500356401d40b055038884141c2c56589013108442941e00c41c00901000c1c4c1c80f940b0070b0340c8809805103103908603004a03240018001c100c1d002594251100b820340c4283ca03401440400b4403400a01d0f0944042101030380c962034405503400007416054404039200d0f402c409102c00311110300c1c0641031842084480c0c1c0d640307240340350003940b0500c0112a00400b400e03080a245d801007064892891001d00301403803d164180c510b040b030780d1000141d1028070903103403800301d11003210501170300280a242c803001d0003e012401c0c8212041c00c041d2030081424405120501c0001e4503500b025412030005c1c24403440007520100881d140021a0f081084a200003160381d805100c0c001030801c0c0143c080a40b60300b0026804042142c841c0031036002c131001c2c092b05801c04c806078141006018181400703100050a160b000c110304000315080404240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 667813255 1250 667812005 667812007
    0x10504150e0906301f050105040b0d110d05010e0d0e0a15020d0822080306040608030c0c130e0a0803010314030a140c0109050706120506030102030f060d032102 70
    0x1c0d9860400380c05264000e00120f425150003400c51000201c1c003442200d03818180c09418640b0854550100602802140c640070100a02c640040501c4000c01e024818030b803041e82800203440d05400c14414811020341c00c10000e040300c0c8411024014840710012048401d59a18240842100c0d000e1003483d40320082c2daa01d440d45482240108604010f490b0400c0070040d0380d0a84409442c2e400041ca40010720701c0782080034443d80d074403542e404252036000f040a90030182c24400c1c0308000c8044010344c4684c03000c0394200446501c580c0030a5917030140388200c040e154004041090b80313161a10f40c4140c0e60300d103548007280000c07803421100e017000a83d040450b00f011010005004008100050480200c60b100003182040300240300100500b0800a2000001078000f481c59600103083d0401005507411004480340c00b41c2d242c13001001c0c40070000402c681a0b2070f02020801c00e00c0c060003220b001342e80d41c1112240039203d400030000c440400355011000d10042c2442c0c1e03046070801011281000300221001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 667814505 1250 667813255 667813277
    0x20f13060801090b09010515091806070824060a12020912030a110303060904080913140106030b0607020f0f030703120c030f020f0604062f0406030c08042001050415 72
    0x100c501551301620811250741000e08002e03184148222000442d4421203000001d0b03214413244c080c1c0c0550904541c400c5016103010004241d40286405006207611926940594031460400c0c0c520800c826200d5071040c0100490381e0454801c85400740c412440c0b0300d00500e0b080001000825106c00d4210561482c0c1000c02c800c0032680d040203c4601c82a04500030718a189883d00005020010043c4014101180801c4010310b0307498940d8103080c22818540100011580c1d251414035601e400d03c14040000d082158120041c10004241c402e05276010b0020b841c40c1c044035041000401c81542040d416110b0020b0020104610408140d01071003103485042c281030300da080040400070106080c030306541c041c914074085000009503007584180c04c1000080c10344000302d04101c81d00740f8442d5030b80c0f003203030805a100b50344070084000304115445901d04020600e040704003a10403401c11176020380302281c403030506400121001e80108140005240c00740ca400d4403084c0581801d801c29180c0d9000409010384 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 667815755 1250 667814505 667814513
    0x180711121306080f0c030f040f060e150a0c02120d0b0d080a120207020d12021e0c030d080105010804110112020a080a1415010e040b060301030515010f03030c020f1306080109 76
    0x201c2c0c4c0c000c10384560360001e601d00222002190310000e401d00e00a035950310002403c2c44502c580da0403549921a0b000e1003004808081d90385d0b02d40802c40d100490000c00b10105e84080e860340310746404003031242c0142081c0c0b44001c903100b190350068010314081d252656100c06c40d40c1c2d0740da101265240c0c480d802554480b020144010058101d003178001c0c0c41c45104000400240c7c0d40d903001000d40b035501a558001d82d5100400481c1010f01010f0011038901ca4080d0a16410401150310001c1c1d160940403161101c804480880349404281308071408034682c00c0208000c40c4010000c400411018100038001c10000f1449000701d90000141400088099040c00603012080c00341c08450700c2034248262981c18002401c1e20828003801d0202d06001d00c860303a50f4103540b2513402c0300d503806c1002001e280d265079581c1001a00c8031031810411014004850003c14031205901140c0b0550f41c140d95402403991180c0d090000c00b06480e14030303560140c41411580303005019070080102418400c00003141000c16071034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 667817005 1250 667815755 667815767
    0x5060108070801140a090c0902030112020112150b030c040b0a03050727140a050a0b0a08092808120c0c011a0f150c0d020d0806180711121306 62
    0x2255a410800080c0100740c0303402c5042c1c1c05c0003c6240004110301a45000140288164003035803440e4004400003d614032010755403072419000b0307210803400c02c040e80030301c20869030682c6020540b011411000d004144541000e99407003004040f400c0e01e0300d0703156601004150400e81071a40020744a0042083c0c1903480015040070103113808042050740d00203482c01c4000d448500615606508400a041c2c0560f00c00000000400010f004131700e03429150b68094a041d44045542d0011800c0038010588001d80003445108540000b1355040340d055403e80e03600d99941108005580200043c01000300100703c0c078402600070380f00710140c0b80d640d0303008207402c030b09461074140d5041c140420000d07907803003603100c01c0140d04807860225040c1d45420f0702071a60800d2805607400d91700c0d030307449242952540c3c29000a0011542e00c0c0075110344019a444008211701e81d41c2d01000030003448520b1010035400340c040c42c4001b40e520703801c105441031802c507a0710340d10b8240c01144589221003180c8000704045a000781c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 667818255 1250 667817005 667817009
    0xc1606140c06160e090c0307030e0304060210180b071e0f1e090312050403020307050628110307050303011502010c020a1b180c0e0609010c03031a09040506010807 71
    0x1440181003200304007603141c482c00020144110720b004030300f5180016200c2d002c0b400745400002d00683d0700e0b04080d11001e650350021601000843d00e4044a207040142c004161002c0b01c0c0b40b5401048100fa801d0350719402313020b0108000105082c540c04480001c4c0348c200c1d006110303106558958400c040141c8000b80c07500c0c1c22942480a110325011080c42c0d5603480348400d029501d10024440640b040710b90115901202c43c1e00160100e44402500006a42d00400400031a80200d046414444d02c4104100d020310030b5000c0d50701c81d070340e00d0915003003079012081e01c607203802400d818914142da02604540782103512403442154a500f000006101310403940e196035442440303601c000c000e85422040040c0d03903440c00004c043c10b141c44030f07640b0040031030045080d500070301807a0b144201000c7d99190100b000c0c00941d16000007107041d45810741e401e800e14405031542c0490582d180c084012082c1c030709900400c00c8029a00b108500e8541108150b00c941134250701540c0b0071801003042d513141c40b00239810001c4075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 667819505 1250 667818255 667818287
    0x606030b04031815180b16050f010510060e0a0801060b0d0f09080a0c060b1306031e08030115050712090e071b0305030c090a18150b18060c1606 63
    0x210024803440c1800728000c101421300d82404000b4004651143d01c076411164058a08140001040340c0800f400d000503c2e41181f042040390080300170080100d090301c40849000c40f4802403c0c0080111611407d900c0c0410070b00504400456a1540003030b44c01d488150304640c4401f4800504070000030042c1c0b080e8521062450420404210141e83c0c00c0020701c075500040c1c0c03c0240084000c400e000da02e0380030f035040304c0c001401d80e42c0ca101003c5800d03014000511050b00e6005c2c0044140014003540c034180d00c200da0340610420314503030800300b44260400c0181c4142003001410301c455070010b4560032880765080c0703c9072900c1c0d40c07407803806041c049003460041c0707038008104000040c00b0101041d0105110360980c1030034040c0c0c50303a84010300c00015008101359a03922954035900010000300700800d01002a40542082c0428280c1c1000c4080002540c4a0303013052400c200205220001102c4464102400040c0790310300c1c0c44410f14805142042082c1180b1103c40c8a0200b04040e42c3c20440c04243d00d401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 667820755 1250 667819505 667819547
    0xb0414030109020f0405061305090d080703140103060f020706061d01050312120403030b1810060f0c020625111c030c0605091009030e090105030a0c150c0606030b0403 73
    0x205a010400c2a5110b131012030003640c6950209005a942c10502409030040c950304104a242c08180f90342d80d80004c99094004c1494540401c2d1014803c0c01203a081d00c80d80d1803484240d92071540d07404e004140c0345130002455a03003840040d0000700d50b4010540104690800c3e550740d2180d0511034185405c041c0c1c4214800d9000e2294960502114416110024081d008070301712980c0f9402d00b03901070002c40e134903264800c0040c500c41c0020241202c020380120071030301c500c40401c0c4d2902001d03502800b5840c034a00101e501a0020030062600100a0089410442c0e0110562400d100360761203c04c545d030301c201d0380281400040d501e903091040700d1304450044c406865610038441e1710050704c41004104060590b541f00e6000421b484010420102e680203d44420070440040b410018456141200381c544110708503400058549000615031804a81010032041e6651400d0400140280d040250909000b102c4032000f0114406200f0b80d001035000d094511aa441c0030b10b0014400b24910302c840c03868a072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 667822005 1250 667820755 667820771
    0x6040204141314010624020105070e210f01021c0b01030506010c061812261b0a030912050c010510030506071b140d140a0e040b18010b04140301 63
    0xa207540300c500203d402c07005484100311a0140e06002d4040c5400001046408088064503045046441700c8800c00d598002c01c140d03203601c4000c031408001145d000b540304028841c0e8004035486201541198501130b003c98540200b0400e2403426a000140c0c508c4844505031524043d5802c40c1c00ba01c040c1036424602005641780c4000003038081901050041d049035070354404e034640d000003645165856904407005200e294001a002000c0f403821014030120704a0340c2c0003000d14040d04900030780c040c0c54109e00d5010f205c0e02d145480d0b5034a4100c0701410b020513807285e41d1000410215482e020706c0c41c00740d6588a9450564081d01707820b603000070300245070188000c4000c2020920128420781c001030036103420300c5040c02c0c0e490346191420004001900f00001c581075250480d10024036141c11045039101c0807031301c9840701c9881c44180100d07410103020a0042c00104d019180a0380710052000000780060f41e200c0316150140d072044001d80124442400015080c85181c002e03407040c0d150240e048000344078541c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 667823255 1250 667822005 667822021
    0x303101409040f11210723040506031f090b09032706070b0a09060b090c0a031509050907090f0c17060a031a01030317041101080601031b020604020414 66
    0xa00014400741c1500e01c143d01c2002000b0f0030207800c401541000342114442c0211801080903910b044086500724840c90600049a5001440100b0300300d611071941c50f0313a80c03d08406d00010303201c014035040e41405404001410220380c0008885c030039a414800180b42038603031070300c445404c2c1c014181500591007802064031070301300722260311490100d0450005146a10401143c0b09000c1c9a000500100980c0d08000300f091a60b448054401e005100602000034450300384054560f090341e403001400400c01001d0801d6009030403041c5100e00d901908140595140c00c030900b02c1c0c40546004969800405c030400040ba20b81c0606030f01c100f4401c41c10414039101c224040e1900900c1d0465290300641d210008a00741c1d80c0843d008000e42d0060000620b210f442d00403416407007424002100030a800d648041c20034516062058400e035480468408030072031000041d10040d10003410141010f4a402d580071407954000001d4045000c141c009145a051510405c02a6000c602d20095072079199030811050b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 667824505 1250 667823255 667823269
    0x50a0b010e1909030905060c0f010b040903120e0c120303090f1212090a1b030c0f0b040308070f02130608070515120c0705010633050a0f110a030203031014 68
    0xd620140001040e0f1520702d402e4645001e50f40c0155030000300800c1103004070340c01113081288810410300800512814404010031a40c00c580302a000030518452444400500e5010071424403091040740d0748000c61100084504103400984203040d080481440701f800300401202e165540c0c100041d10110840700d07421005402804008e070040c8804401107045040103020400342c1503002060070603045c1860581c2c200d4410f16101c21510807d0802e400942c00c40c107940703840c0549142c018241e2602c1e2940e16103403004d8005400645040c480041e0060040c0d0341c0c42c249a60741403d0003c00300d5094a45503124ac18180781d0b600150140c0b45480c44c640c06014200c0480c1c884420204028805841340002e00025000d40c010043c000d601c0c00c4c0d00411212100c074009901c0c4401007031801116203c07490f00c02c00390804425081c000c6001400306011050051815444850903031900c40126031303d25002618140d5091000e40158200009108031564612121030140100e0014040011000c4000c1155 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 667825755 1250 667824505 667824541
    0x30b0601030209010306080a05030c070b07050312040320060603010e0a0b070c0f05030f0d050c1c2f04090e1501050d23060a06080a050a02090a090807050a0b010e 71
    0x4142d80000da00c4031681c0282d21000240510108862069a180c6003641d540e07401004441c82912401100041000c1c0d601c0485540301c2c0d00102540c18041c1d00246001400c0c0e02034021401e1090040c0c008400000104400b079480320850b005003203504100381414212040e10000c0e130300d16081405510040b401048406030418403c2c83c00c1c8020444609200600b109505c0d0001c0c180d000000388071892507051000741001911a40e8100580d440d107203c2141103100380c0007900112010340d0400d60901120f40c2c00b002e40700701102144407401d84840d0f00c4803e10702620740c0380c02d0004001700303061024095031700c291487c4c0d0440310010100c000000041d00a080343c140315141c80340c69940c41c29020002511040701c0141990401507001c1c4898609940c0c54640c11038521404510345000002c00000c0002c1e40101160004041c0840f0015502440509203001380020949a1604400000500d0490042010038040e10140c91a40200d01d0181403854041e0311403040b100c04501400b540c03001500640f41c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 667827005 1250 667825755 667825757
    0x50a0f050a110f0d060e070504030606060507030c14030c070906030b010e061305090c060d0c080610090506090a0f0e0a0e070b0418240614040609060f11100e0610030b0601 75
    0x81c8843d80708601314040c01d5140c004460000c3c203241802120754002c2c000d44142d070302c951002d12941c0d86400c0b0484041c02524406000284442c408078041608800c00344410010741050300d1070101421341003894000154802244039503101000c00c14002c050a200380503003101220315542e0f0a04000142088522002d4080c2c2c0c150f840020603264030040200e4007001001038500b40c0c540d40784000e0b1800400003003001d08082125880003815505c0d1404140e030344018243ca892528905060078008160840d242c0d0035000500c0110115054108070701c4c12006103904000c0005514080d45034005561058068004942c0000c0c024041101900c080d60260f91410a113000c406940248640c06000900207200f180501c102ca000c50403070240f080350090392100d44811140c4a45030100d01a04c3c480d6100b0b007000122800d4091241500c1140314071000125032a0070f40108503550061410304810b0303000411200c1c0c1d100c9208504c0081840561b51100009040440407461500c45015080c13008108034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 667828255 1250 667827005 667827007
    0x50609030703023a020106030f060f0b0f0603180f03030108010e070b13050f04140c04080c01020a021c02010c0606090209040b091b030c130816120c031b09050a0f050a110f 75
    0x10f211305100350b000e00e004640007440c0003114002824107000900e0341c002e912901504140c04070b51075050900c0e0000c00c50320b01801403032a565901c943e944094040d184101014080c0340040507046a00b000a5400313003071107d0001500420451686203044181e42c04007407144405c4c05052004103200401d1000c0f00c000313a8101d810030030241c0000b001030004840415065000400340003034002d007100070f030041d100c030717541100c3c0003084050041e03a403003041040c001c0d03100c14089803000071340e9005030003a130300c807071060600307103c0740d0019500c090595943c3c0e00411403090740818001c1c040c0c07030640551f0030802c2e009e441c0040d1a060200b2010780c980c0075145e581e040d50900002080d42060504111440300b80040024003050307440b05100c940b00d03104641a0342d034244045101007030a84000404031096584140c289090602d55618922084040300100c120401d100c500011750412034051284a56100080002d48403c800c09550496a029040c0c654251a1503054403401d00d001e03040f80c0b0425040a012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 667829505 1250 667828255 667828363
    0x50f011b0809011b03030c0f0903020a0504180515041104091223120f0912030133020f1c09180b181b0a0e04020d060305060903070302 59
    0x1030754440b192030404d00285003900484410301d0780c1540650b0b500078241d0ba0300700c030348809007404641d04000c500019510082c00f00041189280070784c000d010b0b41d400d041040d40c0c165050b0b00c0e141d042080d0501030000e02c1e800502080300f0000e60f2409000f49900443e42001240b9441d156044104147d502039030900c0800300e12840c400e8000e24000d2068012003e8003030795403201010b00c13003500c441274400440ac0101240407401d040004208603d2071122540d403107003180c1ca0114004090745100550b0500d1804114845c0a0f80b0b41b8203d640e000c11403d50024104010416680c2e071a20480c2c04140c07950407149c80400c0103081d84104240304444000f41c00d690615619401c94005002156010358003e400c0590802c1c004802602980b05041030540300d445440c3d141e008010b14818002401c00248292486005c0383c50940e02608104151072400142c464907561080e140c9441034480c00d040d684086440c208141d81084141828000808010300100c640801d11080b00c0c3c2c2c3c1c07401542800b40f18006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 667830755 1250 667829505 667829507
    0x30b1503030406030f0f0204050d030521040b01060e0102060103031d01030e1e0f03040506090108090316050f010b04060b04032d0c0303080c090d02040509010204091401050f011b080901 81
    0x1400014150040607280d0321556804003a00400c01e04440d03030006405e189081062840500c00c1e601200c00107003000c0300344a41954200d49961125114402880100c070172a400c00510884861103584038150700007035541440d030081d181600c0706240d01e0441d0300280c014000654007004000d0441049201001074034000c80058000c1c00141401c81d40728402c99011021701089464424480000c480039103442092502c0d00700d451b4400c0340035650f00b10741c0400800c01954481d4441d2a405515001940d041414004034195611a0003205850662241c1c507541c5200d0000e01c04c500096800715002c000790340c940405480e43c0d00584c44040c090054850b44003040c0010b54070400850300b102420b2181d008a1403418030500d00040c0401d90008400c03400144270211030300c04075034000e5001090325080e40360326030800c0041d0000405225182d5002c1c00700084083c190b0250082c565003050040d030300e0350304003014803098108280c85c65040088200706290805d02c141c0321101f1090304042c960b81e491500c0c0300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 667832005 1250 667830755 667830781
    0x1228141909021305270a031e0e01050d0e0604231902120f3a020316081c09060e01021204110103150801090b0106030b15070f02120f07060305040804030b 67
    0x520003a0001710340c10030302c900c810040f40100d4458420349951080760016020f20440500059400011404004a0240b65801100900241d2a4a910200d0313a40030103030020b8103206050b01d0484e6860030b5540115054440c1d00d03240390424030400f000b44800214251207102903840b004019000c0d900124401c401c820044c0b0051180841541c1200c41c02d9200da04c5540c14500400e8002c000312200f4ac0286081001160402d816000d1503030003107040c040500054100f0001003801120410300802040d036194181c41000c400c225810386001501d00114140802039075054080d090260340304000e20003075224031090135904690890580d081c19108040142c1c0201611641320b1210317564580f001515950540112240b10f100300d51801050342d0b5101c0030340c191100c0c01401175011a050060100000794100601415070196625413003640654001c10f450701c081c0038030701c8200e821201c107040c129681084060010071031868200010301e417580f10001030740103030700008041c103112102141d000f2104071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 667833255 1250 667832005 667832041
    0x318090504030f030506040c0804030509030717070501020c0315071d0630072106090f0b01170106052a15070908031228141909021305 59
    0x2401004a0304007401c001c0c0a8040b10b10241000908040004403282000d004016188a0b0381d158407025440c2c60360140c401e034011000e07450705407040040004e41c0d90501802c1c601540000e00180040c181000c00081c1803000714050b10340a82d0000025940c464280100d00e07a0210751403901200c02c403560100043c8030103000300182e51216010500f0f82419026218a0000c602c450080c07010811030f8070042e07180342170101c481c01301160401868407107031030940800d0a10081d104500140194403500f14074119540404411010365440544e100c0950f0051a040211410360798002c4440d803501e04010620301c60301199512000c80502c0303007103060304095000a1940d00900030f481c428070f82c00e9546820720308211a103000240300c44400250301500802190340f00c402c0070140038030039500d00c0300807022030906007908281188032802d43c0c5104e018a121703020b0b4445d600a02c1140038107010300000c0b582c503104e0b10340d4040d0340d24240720600165a0035021140d16200d5810104883d40ca403580490002060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 667834505 1250 667833255 667833269
    0x30a0e011e02060a0b0904020906010e01032003010e010605180409021203030708041718090912070f0b0105040c3213030501060803030906010e09070522050718030318 73
    0x101118901c560300030522520520001400b000802041e03020050f25241c2a50041e40054543c00480c1c000c5d40305840030012150107050104d0040c07290b43d92140804078039200642c598001200512400d000c1000d81c900400140c03a00c5400c20360280c0700003035a01865000c5034482d42d41c0302c03a03a2781103440d542001d649010130340058a840340741080c409041b5500c1101e0271510042204142403401100100f684c0c000c481124178a18403101090a00290004c06010109075200d1240f12000044d650070040409501c030741080d0358400034a14000c490860180c00c2244501d007800008500954000c210b88421205251204006000710060040c00e41c5081008031031001e0001c1c014141d11a0b911910048910600007044041d03a1001c1c41501e83c0070a076184501e5812400040190380601499150041c2500040c1c0d048c0c240e9a10004140d0740002401039030341400515410b0100300b507485000d910110314205044640721140c1d0b00d80e1103100c5070200809129440e08100c90140180c04410080d00107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 667835755 1250 667834505 667834547
    0x1906090b0a1a010807020d030504080d0207150c020d05091e0a090b090f04080327011805010b031f111e0c061b0307050a12060f14040e030a0e01 63
    0x20059881d80980b00d0041c10031518003800110251035481001520700c80c80c0d065001d0500c1c00a542c4c2c003100030b010007030410341d10240b06000c1891402101c0c0300500009210340d903441c25001819440d01c05035138042009005540141e0b4030146083d4100044505d440811900c07046c034038141d00804411008800e41440c1c02010750840400e50080c681d20000d200c060844008000b0f135690140000e41482c1102e0003070581e50140017060304050030038142c031850403008001032040d907020818a0300b111030844081074001401c5c00a5070a01c6070a20405807088419800340400618181b04021100031011071a0348440d580c13650701a002000783e007521408268a4042d00035200aa200098240c0002c102000c0d58001e070000718900782c1c0c1445501518039888210541107a41d100d000751420741103d00303150144090382c5c03614800701c851441244042d0118284aa01041c00c1c0050202a10f10082005000781d1038000d912018090001c1910f0071502949428602084440012035007000003190303050324a41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 667837005 1250 667835755 667835761
    0xc080d0e101505060a2d0903020418241e0c0f081506030a06090905010501030c050f010206010512070e0a0c1d010512040c0f03050f0d111906090b 64
    0x25000c600200c0d01c4068000912204840080c1101c0c0320045128156000400700151000c007409000030301300d606034000281c500f01d07403507902004a0908200d072041c00180126418001c44c81d00d403081c082e0b550300c0401140e610466650703031601d000c0791103040310450955001920080740c0079900300e4100c807000d5202da1140d140c06002001c0182408500c0100465010003584040c0351107241c18a00c82c1e14101030b40140404280240402c0f07520103001c7c0103c881d183d06000c64004110b0141c00c90032441000001902d600d90709050310000c100740c001c144138809425455151b680d0018640303055030400ca035401d0b01a441191090315000c0e542d84451342d24400d0008004959000d0390001221480903100d0313420645081d41c00b51790a0082e02403035808200d003842682201e5100d41c000b00e42c0f0074465801d4004180e1128a0304c044c0110301c2c2d104961301e0340300584034450601c0c28040c03540f1400310381c24245c071205c0300d107407009458400301c0748016440401e00000344144206504401e82c900e4009040c0d00f0035003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 667838255 1250 667837005 667837031
    0xf0109060f140f04200d03360902090d290c0a0507060e12160c0f080712030c061d0c03070f0902090102120a05130f03030f0c080d 57
    0x4581c0d034503403200c01403030302100c40000091150b50600c24019000840015604c5070385020700c00144908450000700c00c06801840f54448204020805009032a4004030004031403000d0400c040444441d0240d1144036404a109040310440030b09854070040050f072504040004103050121451000e040022840707884250b030220540c50003100403c4034040d024075540d409191006108000703500002500c20081030000c644254400403c4e0810f40c02601c1814501c480718100c1d5400201321002c402802080000410a0440c500d030002d101100312005254613010146480d40081c0c070460000051054040b410588142d0288190580c40075041003260307048209401c2c840943d0008031681e1240812030200c910b000280c10044900c500c9403010b551b802c081c0050302a40050300b2450546c03255034038040c00c511101010f04a418101c2d81e9542d220300101140c0300240b40c4036031052403400b8101d081480130030b900c4510320000301d02a007014171810fa60f901d4850380301d100366040f4808061a2131003080000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 667839505 1250 667838255 667838261
    0x201090203190b0a0b010c0209041b0e010603060f0b0409021606021210060206060f040b06040509090303070f050a0c02101e0206192309070b031306110f0a0c02030f010906 75
    0x115000300f4111000366160201942142c21301e00c28103000c6040c41503900f0051030f06032030303072903005100d649601901d811184c010003c00300c00c1d801800c0c04600c084010303c04150302d403064000600204400030400d910300304201d000c52103940074510074503400140394107004842045032000a5801002155280319448034400340c500c0581c0c2552180e1108140056040e200092043c000e100041410110000c1081004000e002d80203009401c804188000101660f0340c0036503510950b10b136006036980f40b40c0300000600d4106001c43c03041c180003050005001e4254004e154410242c0d0644158200042c00da40641d200c1100160400c04400800ca0b1034200c40d90200c0c4d498011200c2800e840e60240440e21090240e0300100e2510440e030090b401e0400c80311103003605103a00080c10100b0f8400e12500e54032244425482114003105411048801d00300f00161440780881c1c151000102605152501006010520940d40103404008401c407141044d59001d102041038103103550005c010600c080e141000c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 667840755 1250 667839505 667839553
    0x60e161b141009080d0c0905100801031a07120b15190306050604051305130c060f02060907030b0612010b0a0f2c07111006060e090a0c08160201090203 66
    0x803400b64a41841400c15207000d003040385035001e4902da09088042492800401c2c1d0802400100400c0000000c1c0f29101c81c3c0a10244400682e5603800640c10341c04c03e0082101c40841032845074080d00c0030448166808044110094049200800e110500100180400d5250b080b410b4184000182060b0004038582404000c00a103440031300c8910364601c1007200501981c8611078000c60f034040c240b000801030340d101c181e000d800d50a4603600036150780c030340e07800c01c01168000c4004642800800011590100485644a042100103200329070a5a4541d038000001405c0c99004010403501000b9a61080d005092040c030040e04d1000840d0b5982040b0040951900c904015482441c4022882c40340200c2c801c440410b140040c10f40c0c0380c8035140211052101c07149260172170b014094a40c00c200246024a000404840e82c81e803092071081c0d401c00014203009407001d81002c0c42c003030304043c1064002003000da125901000362442c4909180f410f80c0940020500294103019040802003070080e62400170748 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 667842005 1250 667840755 667840793
    0x2061204171204151505010302070c09020711090c16030804050a0b070815030a020a03020f15040f05010f081e0711031c060f080601030605190207200301060e161b 71
    0x10104c1c1c0300100c1a81218551900c00c00c6241901c8014061540203400a01c01e01e40725201280480b80e451040004a0700400c408032440200400c59151a14200c0f00c055046034011942c10300d00b2100c42c000074244004c071203004003802a04400a400c7c00410f0015541c40c42c0c0004c0d0074401840d01001c000d026600c100c400e0012421840c4030410b060500041c00a00d0035805011600201e0841d02000340300324001400c158091034801c203135203c0c3d00080d4007400007080c00600c504010303420400050800b4100c0d400f21410000b600d01045450540062031000051004000780c07682c1d03d803d202254505524400004e19100000c1c46034105d55440c810100d0b80c4103018802c2000039201d149441d044202c510403040c9590108006101081d40307039000d1500004e0040c4115440f410080b01d800903a004210256010720208861407020001c00300340000f010800c900800c240703401c1c040c10342d001142c0605900c4007014002d04550702e06029600d40499080d0120100001c50500d103400c4610f407841c890000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 667843255 1250 667842005 667842023
    0x50408091e210307110a1a070b07030b031b01030f02070308011418070503151017010801050702031b0f010905060117070b0702060d0f02132102061204171204 69
    0x2c0c0c1060668070041d0040300c0c48401442c5040d1082e19110180c00722407a00c1d80d4040e500c0034000486089401c41300900c00c10b000019903c03002c2c4c034200300b503000d0300003003101d0b06150800d840300301079035404201d203410216074210b5090041c40040c012001050a803607058042c910004004040c9500104964121004054017024500d0103005022600703035100c03100861044444080f0703030380a0107440030f140e0143c0520300c00328140e2a07a80004640414104081001c520030707038000e005034900f101900740500003100090100c0d08110800a40d2480f42074940001042d04642c00840d605090010400b03a4080100034001b008541c1000f42d250f6000f2311501d5494849100c0c1c41d94140344c082600400c07100d120714000d040036403680034482c036a40284055004030b6640c4003500314038106803001c0c08414400f480140c00103414602519000791207400c041e0140041c07260b4240059070750a0840e01d0414200040032542c0c5c460386050050001300d42044450018082002416410100c1240348a240611806 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 667844505 1250 667843255 667843279
    0xf040503062203141e0c0c0a0303020304060302090f03010e0609060708040f020108040f17090312130323060a091505070f110f060a0b0a27050408091e 66
    0xc142c006603410b100704041030740c0072035040120740646101030281d042d48891501e08000c0a0b001c0f43c80034181140119050310108040b41c82c04c0e010440904081020740c0d16500003400d40d180a580c0b80035030305c00d00e000c1580004042865072103140803038503008800740081c049414282d00c3c05454101c2280d0705840c51084000141010f88160b103468080da8000c100610140c040e50011240c0001c020320507103824502c82014400180651740f00c002ca001c0d8850416181c1d843c0c442054100b00c00f181903200c078818107014140380d07450400e0031007081302c0c0c0c03100b081e481070705a00b0b40341c0007007414101000c1841e0280d2410008124195001401e00c00d01c04c1c0c4480784455190300ca0035040311400e450100c009040b00e2002c48126004d017000a87d020718820407a43c400548111592402d241207500c100303403688603040c10101e802d040b03a121010700b003081d070740030b544090403404001c21511160070a1119511440030400744007085085440217140038156070340d0310140c040c00c0031000300b0b04800360b40a00031609003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 667845755 1250 667844505 667844521
    0x9021b1005090c011b0209070c0f050c0f0103090c05040b041b02010213050901150e0604150908061e070f1205010b070c0803041404090611130312080613020304060902060f04050306 79
    0x1c45c0d1100960541013440d05510b40c00780620311100070010424040400c5c0071801189004c080064854411001812403807420740a000d511078011098605050809907050002a1b112a031030b0162030040e1400a803068240740050007030060340c0c2400c14080f1243d508124a01d0b03041d00200f403020642c02584900c3c554500901c0750400d024401c0d654144500c004031a15140300b801e100c83c003042e009110f035007015100c0240d40701d800d4a0003807150105400041c100300b0108240002d5911184110403d0f003099854810361500600050903681004003d01a6031a09802610b0460010000d181c1c200300a40c3c44a840c40000d6002040036500c030700381c41a000030308030300000464090303500011880700c2206d402018400503110040c001c803001ca803269607a10b00312014102030000c0343e807120009541d907032a41c00d10030042c0760b006903041c00300f1210100b044101c1e210b1064801240e40150801603030b81d030310f0342006001003030751410080d440200014200c41c0801c13150081d20680700704900781c5407240c03036040c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 667847005 1250 667845755 667845767
    0x623012d12020d03031d0706080a09030c02130f0606051c050601020309131806091208090712060219020d021212130f0516170606010909021b1005090c01 67
    0x104151040128902190040c28008141d480c3c0354424100820b01078500418418124a4052122640d5000300da0421030a540682401d8110803c1141041078603480c1c1c4005100301d0240001a00800707150802650f42c030240c0c2c2c000c0c1c641c42003514081001507201d1400801c03a034080031a041f0103400d60b161004410280c0d2050a0080c01c0c16001146400c45036410b02034038040c4410a5190641e94110002a1005580307401400a00c9081c2c0003034040b2041c42c4c90030000d60036000c440100b00306001000050103000032490140d17030200203503d888510f280f0f4800e0103440780450003640510101c5100703040c02e80002e06200c1804c0e041d02a20b07030f035909558224030f10340244401110740d105540041160034044c00d10020645004208400d211001070302c1d41c03860708a03035081030b80c030001c8000410030501601c004940c00d084c040340b000d0007032400c10700c000900311a2240507921045a00180324141d4280210b040814400d03400107440348200c2da8002035006000c00c031648a40780c015080e508241c0e4ac4155 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 667848255 1250 667847005 667847009
    0x3050c0a060512220b0a14310606080a261317031215040b0a08060a0f150609090e0a0210141e0304022b0623012d 50
    0x942001c41e6035aa2031012131220307050703021035050b010b2004070300c0700454903004007207103d0094000089542103003d84265504400104a104200713180722500c120840c2e00b442150803c80d800101030040d900d54200720005046a03802400320344103c00d0355204115003140e00e444214a04408800c3d070303611540b8040d59511890504181d0712117180d034184a88400c980e907009020f07002800301ca08015085000b045061019521920300754240000c3d01d140d46444d0140d0340340b801050310b41c3c08520340b030081d48640c1c0390f9000e020301141986408501100009a80c01401c49100b03204652000595800e0301400d8120340e40900c0711201c2c00c00d003e4801c0c807900011201d01281e8041e200c5854900d1003001107400508004c5c001d03c200000b0002e03041800d4120240c0002e24080108490352820940704020402c072406104a0b217444071505200342580340740781d200003581c0c1c0215004c074010810320b0001d40c10411a1110103a000074010010903030810a101900e0010154204c0c000c0b907910a089103011803900b8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 667849505 1250 667848255 667848277
    0x61f06090b1606060b0c01060506090f010c1a0a0c0905040e07031218030822050123040510080702190b0114060d2a0503010315050c0c0102030103050c0a0605 69
    0x200508200c000400c1e0014049072280810510740868142d403030360103484841d13200503c03006020072094544a8203205120040c041105c3e02450424080041208009908003280c14090f000340310f0001d000109400707001c0d1800200d0b20a03080d1800c03a00d03180c014040d0020b107100207512124080303942e09041c41100c0e1003102e260000c181246c6141c0d0b48039050b0400742c0101c8200407080320502c003104801d0300703294041e5100d4400a41c68a0241030600c1081840b4412038074802010070007003006036005850000c41071902000c243c0f014440f21a022240e209990103190806c0c40000035000440d0700600c802d0150849609a0306440d0a02d07000440740500000d000d400d49405600420018202d880c045800000c094126400c0011240180084542140c21100e000d0744011094240c0220003003240041c02540c24610704650440d200c15903104600300c141041c07917a8072408200245550000d884080003035000039981c944c2c60b4a40b8540342c841000e5094094150040081a07140c082c0c011f5840049030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 667850755 1250 667849505 667849517
    0x92b12060b1209150112061a0f041a030303012607030b070503060f0315070e010203070305181801030c150f021c0e04090c080c060c03070809061308061f06 68
    0x404400d032005102802103800c5109400740c0001000d880130342d9900800b500c1c12041c0102e0040d08001040e96118054403400c1c454a00010315182d4660024100089041c0c0d0300068580ca0131039010071040000291692504c03000c0000030720400080c0301c800d0420810080744016240c0b442d42550b854119020081841f146640003402c1e142c130a01c051075210100800d84400c6c007030704002203400c0c00f0381c4203086245224070408100b01d0b43d810250000003410284003e610b409001c0e00c0c000d00d180515140d03807014402d4000d00034210340d6401e0240d141001c1d401e14409042d6900e24085c907160a8610610104048805800d54002e00451010310320003019006065070529009060b903440d60411094001c1c000d00600e400c01c603446a1058a011900c01c1d6981001607042c26510781c40c1c40c6140d00840d102d1441044510014500030044e1184503a004000513100d200120000e4054014180301c1c840d14408124009079007103000982d140500051a009411050109000344a1160760701403e404605 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 667852005 1250 667850755 667850767
    0x306060d080d1401030f05070e16050c0f010608070305010f020a0905101e170c0708041e0510030603031805030d050f0706020a0804140a0302060609092b12060b 70
    0xe60200103200d00502c0500000c0d90f0041c0c003c008160744001c0e08160b4581010340580020840b003040b03400007904800c1303000e103040d182c0442a45059906840f01e0b0302080740224001006200070009140700d641060000c0c0013554944407410303a1802c50741710a5600d0340c00d00700c1c01d031111800da1007102c50f0701d04690380b41c046850821081c0219407000f1048442004080000000660508403000a5000d1195075428440109205560342e100d4060102920440c08000a00c0024000001c0710111500d001e40d000308a4182c207241d000002d8264495500504559403110281e641644040160781c1300382c07601c401012100e1460310710b000c002e0141903019407100121400043c0903c01402c0c401c100c0c5903a803031424256548200503a0440240344000c201079a083c031003080760241602070030044020003010f000c00c2c50348000b5541d2a028098501810f1a41e01080003194103200618403000750515100c502c4c1807400701c0d60a1000c2c1e1048000010f0310000e40c07010100100d000c3c0804031124110000e003400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 667853255 1250 667852005 667852013
    0x2030601122d1d060606180109080d050a03050c09010f0e040f09050703020901050d0f03080402010e030d020c1509030604060f0612140607030c02060f1924050306060d 73
    0x1100c00021080c015501d0304403902c0341460341d0304129501e4038400002c0303190004010b02410b500c0d011962149990885810841192601c50580b0308000345d0449000c100c05000700140c9060890307420020b114024280300790551034006006007a2409d5681d07080040d540c0b100090034040c0101c3c5851030000c0e0400100943c15407141c080c400103044001d20000d0440e003140c040c1421256100300403115a0040d040c02c0007946800c0034040e0042000b56045500803030300f079507202c0346a4145080202404815070100c1c082d640f0030400100c484502604a800c1c0e256129000382d034550b8140d0207248601121130007524421404003c0c1d03841007001800400d00e80d1107603640d107400351250f05c4200b55140da07118000950070807100f035030140c079501860900034150a03810240703045c8036000380420309040c181a25940700356800650240d02403044a482013150f202d001050110409501c410181d00c2d040484042110214101c085030141c0707200111040c2c03595034014141c4900040f181d0a601141001e0007034089 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 667854505 1250 667853255 667853261
    0xa02010f0201240e06010c03050304140304030204051f06050c2e02040e01081002180907030b100e01091a0301180e07030b0a0f060308040504180c03080a080a0203060112 74
    0x40403550001141c01120104101c1054941511003005011841c03002c0098203142900150440000c0c6844e4001d4206520042e0007848040e200800f020542d0341040e10540042c41a9009958000c2061000e8200f8540031503140c8c60411040301c0035540c075000000e21a01070300488001c0e01c28900607012030340d82100601801c848495114242c41860402c1091a4080c1e00c01030000e0241c0600450165040520051500c0c1d480400b0026041c81007055410308505911044264a01161003110590715000c1c110301820400d10b40d1034200603440c15581e4101e801510701c4c2c6c540e800c20381c4c4101c4566030b148240c01c0c54106a245400d43d051007080144412a140c0000600109040c040402d121500c000740f42e00e00003132035000f901e550b0b40d0b034028001d2840550081035400c100f106020300191381540c0340c00d0514400d078071445106542d542d02c40d810030041840d600d00c0440d001030034482d005a481c10030ac030955101301c01281c0007030351480010b4000700c4a8401c3c1e030301641041c1d490140b0303618582c5108d001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 667855755 1250 667854505 667854527
    0x506070c1d1902071719120207020d02090702011e0b010314150114190e010e030309090106030f0f02040902030130080313120f030b1c020906040b0904030309020a15020a0201 76
    0x48680030045100517240454002d05811400445030710003545449001880b1500d01191960958010000d910150b0760b49800000c050741c044a03102216103e00c80e05030f0040c100c400c11045200e1070700e00311220006080d841407035030047c03c2e00c06028030000e540850110280403a240a49501520100d0510754410030348100d03003103416111140381c40410341e82401d15600d1500c2000014078001c40e1403005507404003030008501e4080c1c00541c100341200e0000380446005000e203000b09a640e04440307251210742e4000c100c254a81090456540791038081340c1c1d001e58001d0048284060090104049078514113800b455400ba1070381124401605a80d0385403280e900140030b542c207114800c109100841c40010b0000318009c0f054441d03210b030701e51112020b020343d4001d207142c9105411080782d294403201400304058a940e8101d07004a00c583d03c000008000300780f0303c041d16801000c0c4000708010540c043d80000f4009000320f0b6110b1f8899034070071b05e00c3c00038119034280c87d005800a105070360040d4043d40c3c100744 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 667857005 1250 667855755 667855763
    0xa0905010c210e070b030f01030227070e0118030f0605070c080a050a0509041b0915120906090813030606050a150c050705090702030a030615270506070c1d190207 71
    0x2a12590b85c0302000d08940040d2080c00f200e05060004000314680b04080001c541c00940401d050100d2802402c5400313100100200c1c14011320a42c2480b06030310940e220b032070400b4091007040c501030f20781c00d180d4400350b0681e4045030b2840c90325000c07a14440c015002e00c3d6903207a001e400703c0d00e460740300381c01194160042e0222a00b803040c1804460341603902d9005031200c4508018042102000300349005000090b10f502c04540a00c0103410b821040364005074003a00c4041c044404912016980b500d03030014480010083c0400001050b01240d08908100d0002160301468080c403040d61207508200e03d00e000d51080d04241200740038000030460098001003c0b11b805042a00c0300d044d55080804d255910884001c0016000045c10400464062140300701074101d0401200742504e040742c010300300140090f80074296844016400d0030031040c0082503070150070f010701025150300301031401c15503107100c0f8024400302c4541f25003005c00c480700b4152924840d075100c0f51b00506c019034540f5118000d6110754401e80d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 667858255 1250 667857005 667857013
    0x30705130207080714190809010f050c01060603050108071e14041d030c19051902060705070618060203120103080d0b1f1707080a1d01050a0905010c210e 67
    0x4010a090102504559000f40080703944c2d0602d0005032401e085140c20f6006c58201e100b0404008078150800b0f448600000382041052041d40e100e0581b01806034500c891020341c02c04c3d8010440740e50640060341224070201c121244c079600c0d10300c018095412443e00f240110103008041258012000c05c1a8018902510006010000c0c402e400181d00d003105104005600025000f6961082005500110003710408004030455a6180c82c0c44002caa80f840c0c610b51804074a4070300b136548400444401c0c551003002c403018181c0d501000f400c181c900360505a01d1594030500000c00500100031a24903504c00000001c0380d0b801c44da1106081d0f0007880300c04002c5030b901c58100e035460300c610b4030900d40865040300a4441165902000b000c1580510030303000c2182491051003000790f000750450381c210041413000302e00240100c00080402008079203c403810743c02e04007841310004d001d502c404c1416028900a0141c050004800d81c1d00050083c08004010001e2107071416103500e680c0000c004240c110306175 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 667859505 1250 667858255 667858267
    0x1060503150d0503070308150f030a0f03032405030d081603050403020c03030d09140703210519261302190f0f0e220602032e0e0a0504020307051302 65
    0x20791550300a50303021800707e10218103002180310741107142000050212501c02c5c2d6400074001003a140c0d00300d040c00401006040700b0380d404141c001d40108012008a082407840d8880440703070500100a58840d50b8080d010700b08039035041620035040c0d903202d0b440105080c00c0f561181c90040700100f200410590071402130240101081d68113000038044c219202c180415126510704100340b07a0700382482c3c03400e40b0b079010f0340341080020641c07810b0748079001c81c859002075080c071101016105032090142a446009001c0380500f5119005450480c06881807102071000d40444034252036210340540b207890204800703484640051621403000f80000d901003050101c000d6075400203241c100440e803c0400001014141400860102c0b50b00c5540b1044925114081c20343c0e21001b03c0c661052408064140c980000020300c00d060311924030010201c01e44071508001e000c030201c0002d401d515010740303c1e040a03128081902c010340343c041c0070301030b0f40c008004c0c10f0a68604801c11400f1b226668140801580a01c61 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 667860755 1250 667859505 667859513
    0x504050d0c0905071206080a0506010b0304031b03080a1b020616140426070e010504091a0c0a03061a0a030519050703090b2805090109050f0a1a01060503150d 69
    0x101800380c00e83d600c6141c085c10b00c2582c41425950541c01c0802c940c8d2200e03650b0b41c08a07400003901411100d0707890180e80c0e2510b80d030800303d8000030b40c61080c3c0c603000012240035041580c49842e00c4d02c180030240e420030800c68840d9941c0385544500e001800141d0003400840e00b00a1114540c000001d5076090044059604410558058000c0c0c4c0c460003600003040000501e00118540c840005400c000240020a040c40c01109490f41c041c081ca6008503510f41209080150a070742c1c12020107074440e00c4100c42d02d4285c0f042c401a600c02852240000e04042c00010070360100010b13003650303200c0602141e003480c2d0f58040031402814003d2050f04940c0d00b5118456000c42c45201d00e80c000e11b9a5038001c13903215200d0420018000c4040e04210100004540140c02d4014000ca8503c12101d002000b00f21a20740420b90f0b400340c4000d01d406031041c020302d070b04000d09440000312002103a10440669941d0302810350842b165803001d10501d008171303e08000251301e202d002404e5860420000323180002c060300300d450b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 667862005 1250 667860755 667860761
    0x203061206010806063316061b1209034b090f0b030402330d0b0a030b0c091906050d05090102030705040b031902071209090c0504050d0c09 61
    0x1010b02c0301a0002000e101c140e003070a40101c1c50710000c1d9a40ca900e00080241c0034114440c41d4a80740c0310102c1b01040d1071025403050401044050b4004000380604000c400c000d0420251010b4100c02198162010750200d4803036001c0d00c199542c00d0b446e10102504070440d1181c2141e80c020f40500f4600d034403401e40e0b401983d1801904180c080540810045e081999800760108a0b45e03000055800d5543c0c00c100510282101180e92207036050f1400030070000800c4074514100d010014041c021501c0d44011245448903001410101d02c0400c014000c0b210000305000142d0303d01c2c00040c111205a10004400d42c8040f4010a0503d001602920003040004c030030107004921500240001840015a41005040c074000c03140c10540f000021445e41c1810f840c060441c0c030861143ca0800c050100008a48a110f02d014030b00380300c4c032040d080d5582d43d0586041c1d10030000d44603c1c0d0011410500000c070307c0c41100d01c10018044490344809203490304100802041d0710055a080b0340b500d03100342e00030420002c540 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 667863255 1250 667862005 667862009
    0x4050f01050903040e01152127020906010513030215030a0e1c12021234090e0604020702040c110f0309090403030b0102120703020a03090605031504020306120601 71
    0x58009252084102400d403000508603000541c0184401c2c40710071460124541141c1d02c60105c030400512496050f200c100390b07001424001e14010030202030022050300500c20040c81c8400c101c8803c0e10211035a90700c1d12003c140a0741100080001508179405040208166206007141c40d0034550799900054003140820740d003c40164020003400f400c9295030003520462407440c0d0203004609030600000c00001c0307000380342400b0440340c02c1c055444088680e04540082d0002c50840102e440e00d46020340c0040e030070104400c848803443d08003003001c10740321046072221140c99035590f00240c07410500d0395030380350060704032640b09038200044401681d4510600e1403030703000c90f01c880001a0300401098100810452203c07950341003000484000c2c0c0e10100b4142d40b05a0604000a01550400040740b0300503613800820a83c2c540001c0c00070901da000158006480d200e41d498a030065222002218180003c1d0f9007c0810303400c112074030b500c61505801650b030111025011415407500040100c2c9041b5080e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 667864505 1250 667863255 667863263
    0xb09040c053c220b120c010210020310031a1008030c030901030c09081f0605030705090402060304030201091e0b0601030b010e040f111b060601050705030a0806060714060610090513050a110304 84
    0xd40400d42d41307030926400c11441c1e12030460180094180c0140081d442d404656817038414550700000090302e012005a400d4055500020340c091103003510f00c50394101c800b0584a00e100050311150003e525040042101c00c03240101f0050b509101e0014015809413550a54400078001608400301c4c11100400c600c2d486a0340c40c061152680a403030308803500f240d40c5504100e000c1e40001805014a40303030381c81020b030401e41c16104e0907a030743e40304e041c100d0041500d18801000013036451a0740c0e611064039048480d44501800a85603980c807098010b408444956070001d01041103c83c203080b5502d00356002803550383c0b000c940461010303e0000004066800091035441003054070b905088241c80411242da8890400e0900074030b44013071511015502d0041c0c10001c4208190180060000e80b107001c00e680e082540111421401304480310030342c0c0c40d440211002405200005441608580328000000881c1c8000d4000f0040040c54072000c0082d11004007604009a1103414454113002560b00a510845c0a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 667865755 1250 667864505 667864511
    0x70f06020a080709051e0d0804240210050f010b07060f0c02010c030515010918060e150f01080c0409110c030f030108160806070f030b09040c053c22 65
    0x50100a04800d00075040a402668000500e00c0903034540b0b058400c03405011601b1546903500340c54007230520711507500203080d486060700c02c218412006280071005c2ca903640d0203a0f040d01524090a00c03c80d82c0807141100f004a080004019502a200051503100c1c02407001192054030801c482040d280c10101c03030b000507952020000e007030f16410b00c00c49030400e00340c64010f00b12400080c0024a040124043c0d81c1c0c002c9031900c2ca004100003142c1c881c0c1c1c0200304440c1080c29a180c02804001a06160142d150280b04010148900c96114507070180c0b0544080b2a080e0030a4240303e4842d0003060321118200031800f003000504900c140401c06450120440b402d9a0382c2c96041c41c5545050090351185410441104041440f0f20f0601080300c9038042c180b80f40c01e40c6041e91084048010b4850941c0403900005030700148002e0190000c4020190b810941c1e141c503039480600c60f10040d000c0944c2441021182c6e200c60b03000c20440c80d410105822500400130009000302e0b00c4a109000b49006031000c11640e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 667867005 1250 667865755 667865761
    0x50f0c030106080106050d020f0d1205070210110a0b150607150b011412072a020102060c07380109020a08070e2416031d0a060f05070f06020a08 63
    0x14003405018060f180d100001d01c4020f1500c1c012a4490313082c5800240b04071440254080680c9600c100c00042a0300160284001d04101e64050215032100c501640a460349584c0c48000c5409407003001c2d00c008005e070050019400c652203030030300b1480c0603040c4000300c0b002660380c41c095941c01d009401c1d9035020b04109100b6101140c001c030101c0b05604151030500c10200d483c00300010141d0140d5040706403440c1028003d907a00d42d41103a43c10711510038034166002002d200a40e49084032151006da5100303800301d80560729404003c040030b0180e940c000300384800c00c1c4440b503441c1249029191140ca419410071042010715041f549101d103007600519030b030782c1c2e001ca00100c5043e0b00c8441b45810090b1801d000c944150780386d010540c4118051b10040300c1800d040b03c40b002c01d444a00c00c5605400d540c00385819020f102c3c0c900240b00b55081d84250101118140043d4520300d403078800f40d0202c91842e00e9202c1203041c0014250380780d40140da42500d513003030900c6e500c10105061740000c1c00c10b04075030340d100c5082d45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 667868255 1250 667867005 667867009
    0x30c020615030f340501050417102406080c07020607060204031205210103020a0b03130c0602030d0501051e10020307290a0c0f0c0611040b03010e090606100c050307050f0c 75
    0x101084d428240e04460081088166001803c58064030b095808104070303c45440d20251611442048049015142401c08180691200c1d100044001c400340207909565841600b12016402600c444a2300441044403600502d0725000802440d0320403500982890350300c1d1222031751014141050340c0418800101441c0400502c2c014038040018601d01070806e50454000c20409034890041401c0c994001000ca0399075640084d9280046a2000170f03050000c0d11080000d40701d070000701142d2419410030300003186c13600e4525010601d0001100d001e210b00c040703d40403c409200404024420350104200038400b1549400b0740451240c00b409900c0340042c9851024443d0210052040040c2450800c219201079480342c0e00d81d15814003480d001400300710905000d0000c01800c01545800c0b0000900002c000030200091812110700d0700000d600703695004090391302c680044440a520150710062401d4440c042c030340b83d203051400b070003c80381800c0b4030f40d850b603240c078803100361a0103244d000784a008094 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 667869505 1250 667868255 667868323
    0x1401181d160315060e040809041e020406090501110a121b0b010317031e06060f0304060b0319030f030c0516060b0f010c050714150406030219030c020615030f 69
    0xb0720110f4080021500d4050500480d060150000b0450140024010555642c2c0d0700f1181d1070070900d80c1d00268407120508020300940c80780c841c910208000d05000a0158060341034689102110009440d8900d0309540c0d9141c0303241c488a5030018041421418248252402c508900d041e200b0441d00115505609089a83e140d10507aa42079200c5c0030010800d942c0c41c810103038130070100141404007064070792000080c40c42c02144000a20780d2408001c0100380a015000908140e4003581034440c050f4480581240110781c80c00c000d00824001042004803920941c41581c5051141c640345082c003201000e002072001500606440aa459110141c0146495801445500424241013504030195a03940d03840b25480d120307401000244481009580c0c496808a80078002a49611903841c0d0b2a00300142c002c3d0001ea41800514940159401c41d00e8000d00c6010481d41d01d0b41c00408040d078a000b2100c0030314009929a0750540500701610002c83c1c02086180040045603c0000354042051040864 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 667870755 1250 667869505 667869533
    0xd021e040602240103260f0d050402040506060903150c040f2405090328020d050604050d05120a050a061a0a181203050c151008011401181d1603 63
    0x10107031108010030006400c5210780d01a0000402c00790904038086d04203224a00681c1e001c4010541c0006e0203c000d400d03140e02040c440d502c2102c0810045c0c4503403060003600d0040c05001038141e44589101b4100025140000341e01c806080c0e42e841c50151101d001c05006103059025060100500603400c011880d034500340e004010b42c1c0d190680c200032002e8002691401a2158100151300c1400040746462a00d99030241454002d031901d05030101600d480c59407403404440580346402040e214034209440f03041100c0f8506944284145151120b568a0b40100006000b02404607581c982c00070300007506031a040200e0f030700740d0300e010f85aa44400000e00903000380700010a28045601c8240712001d00408290395140d0185021601c0307449a19103603140c061803c1442014009036020446031714420050b22040d02d5400e0001c1c050a00340d10100c90300c03a0000e0041d1402240d100d59440e01020150b400910344070910040e1640100c085c02640b401d240491071504420300300360009100780241c600400740 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 667872005 1250 667870755 667870813
    0x2c010b0409030504050105071511090a06110c09091603060b01030b01090f030b0403170c0301060e0102010e060609131a1b1804021303060f09060f0c02030d021e040602 73
    0x201001d034a6400401611807400b409052050100c0c95000f8404196110b80180a9402040200c6910140480e403950045902c140c400d480c0041d004c6000c510403180031040f1007d0000928011710320408110701d07404001c210310303554410541001a08540601008003c50113100300207030000818000400340c60302c1450040c1030005514041200010440010b000c81340c000444c00100d1311107183c11100301e01642c10b60740250503100d0504c140080124029412102d09840f142910302c3c01200580c01e80308803010418480e001a00042c017079081100d00c00e50f0102805800c203030081e0680d65612441d0303a1100841c0e0238169114104000d41c4000c2c00301201030000d881c0c40900701480d0780c01c080c4000c1000360502c0d0107142c010a0218480c0340d003100c01e1014542c01141481414141c1c10614018546c941c2c00360342c1c06040c41c5485200c01080d1140e00245121580514913212902c078044020750702c41100034480b1a44444c2d1518100c0c0404050310103050968054021401c2d0711a600348060f005940740c80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 667873255 1250 667872005 667872011
    0x50919081b0a0312020a05030a03020c06060a0323030c01090303091403031603023f0a0b010207030f260d0c02070e04060f090b10210302030a050304062c010b04 70
    0x141c1d00c0e598503030000007281c1d800f0041ca11340b6099184204e040c5603120b10001c100d4440854600e0b6400c0d0990050000c1003040e81c1120308550f544000c014a0242c907220107080030520f0340300980d06428110304051044908012030b1f01d410104044c290854007043d005a0000307903540a0141080811100c160300419150011821810540c4810b40801c4105182e5400c1c191300090f040c10083d6081c5c280d051510041162040c0412081080c002066050001c1c0030059480c00003d011103078075221380c4080d00010b03130060008506681d5440402d02881c0e8055075a01a2002d03100329150b9018030101000030091540b40d04e0f0200990b400c01a240301500070025900319a1080c0700c01203d10003d594016042007010420558010a060081600d1500a4044078142c3c08100001d0070f40740912040b00c0b00e43d00c1c5034011040440d200c005c0305601120060040c1c00070864032402d14407480140d50000e00440d00095541d80e4a800079aa01c00200e0601d10022541000c0259118080c4261403200800365814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 667874505 1250 667873255 667873303
    0x60b040b070b060907022e060f15111f020706110c060702030c06130201050c060a15080309030a060509150702010c090509070906030c020304091a281505091908 70
    0x41d44440b42c0c1100f04400c00320101000d44103280040a1f00c1c00080c964004106480e119412014000041d000c2c1f8091221a0300180c101688030300180f000d44c10080340502043e0203510610290146a251b02e0103d0315000d10042c0027164507407003000781c40c03500c102c2c0050340c0c4c540c80d05120742003c00c020820015504203110820904002180060380000c0350854080d01345603074801a29580910a120351480c0710320803c100c03c58015070b12200324444980025130060b966540c0c0c142e1750b0301c220081541c054001303032010070000d071154001c0d41c0c100070707404191035031100c4482e00b1200c042c1d006c03030307030384006039100c01c3e41e06051904180104040d16068451004610b40030401400a46080c4100303820180d440800480c1a4801d0003500c0161224100510141000d42e4501010048101d0504c0c4600000d5003007641110303840160110402d0080d21100034240b4100b0140205428000d0303440500404201c02c140c40e955000c0c841d49019080b4250111450901e142c403880c00702c4101c02c5280d0041c0c0e1034a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 667875755 1250 667874505 667874507
    0x601030521071112030313110a081009110306040303020a121b0c03020c100809060108030348071b05152505030319061d060103060b040b070b060907 65
    0x48070341d001e07005041c4404510340000800e04d00d40040c1604051800044244002e000c2290030310b00701540610b401c80c80c00b200410810142d0f1541e032144808a0780003080c076a80c2c042ea283c1041019500446c1d10b0b050b030a4107140030030300301b0b181242c0c101c000030784c0020010541a0000d0003000030004030304040284d090001c0043c3d01220850200d481070110035041c42c0201882001109a0040050500900101c07240b0b4094041e01c0169190b5880e8081c103400462103110000c02c0d81d214801510301101410320800682d900c10504221007040d500710041c2800c203907a022038080041c140008005940c41406090066100303084048000800150100400c110f42e180d4007003482c1d444021014503510140e0b2a0640d1407016000740090702e1120f0f48030a0b000380880070000d50310440c120114007120075021004d40302102d1990181030036000f0284148080e0582d0082e54650122040c100060140c2d00e481510360141c102e640018005800090888200003400310555005402900c16800d50305041c5c04c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 667877005 1250 667875755 667875757
    0xc0603051003080a20070f14030c030c21030f0a030e0c06030106031812050307080a0e3301141309020a09020c1504030512130f03080c0d020c0601030521 67
    0x2000340200070117506022885080305902c0d000743c0080c0070440e03074690b95071304296412500038815004031046c1c01d00f9400050901080d20070200314010b0142c8070369860f2904122030007c0d6044030100c0c541414003852050481003006017109491010b44075120451581c00609031383c182c1c24841003581250a264489440b0300d801d4905407081401c0c0032170049100c842a501904a0f004050807820f80400c84404039a041401103000c0d2240d641d0f03030380040c0da44000e403030141c03000224407907419404802d001c8441c41c541303841565072803400080c40c03800900f2014003d0000200713800c19549044810072407003203480d065245044182c5101c01c284900301142e00012a03429061242c01000e03900092801003850f020312044d8820401e11181d0700d16030606060062140d04400d400c030a450340c0f42404203400d8803034240c0d010500740c1d000100549415055400f00c41042c0701a00c104a01001030009059421881c0083c00e42004400c3c02001c86603d1401d0080c07801a0081c01c00040c40c4694070789154131600740d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 667878255 1250 667877005 667877017
    0x721050c060a020c0d1a090f0c040f2d0c02010b1e010c0206120a0c0903150c11030a050c010617070e0403050403140105090f010225150203040c060305100308 69
    0x16462030701d82d603035003000307a040c449040151540b242090034258104150300408428802170141000038036034401d000e06a5916a0300b034001ca0582c0028043c100914003600f14122160803104040340514100c0400b040040c0300d000e1001081010f000444400c000030b2152090346501d0b44020301c80c020310000800e051f02c044000d160808858a603030403031640d02420080d190242d0107016190342d00b9212a00089002d001e59006d00c029081401070713054079200d40ca000d001d03690400c1034180c0d42003081901c08000c2c01800c140d0f50521104440d54140702c0d9084c80544820240e0340c40e00e41e40c80341a40740407421505e03580c100c1c0c0c1e0108c4080001028990340091071405603003101c000161395031281e04040e03641e4000d5500091035803007900341e445254041904114055030403801100c4090a84006060030303406207111034003d40f1400406030032210031020640300d405003d40c1e40c0c03104e40c0540001c2c4005076481160180da250111000c1001000c1d40351007255404200300c62403015941c00c56842c0c0100744154 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 667879505 1250 667878255 667878259
    0x60617060907050a0315020c071211040603081b011d01020903071e12030e03161d0f13060b060703020a2d080d021c05091902150c10050106020721050c 66
    0x3640b134015500200c0c7d811141c40c00b0403c4200d802c1a6074589910503078806031001220304622241c10302000c0d0405010b0700050765031180b085800e00c104c640007000c249501d8280c0c2c0c0510340d29284901540707a45498035401e9415460300159a514050741814503003480c07a405941000e01041d01e0700b55010a01c0b41d0841543e211040004414141d824200e404011105101d540b5000728525078581d8078003c87c0310802c484a09112004072601c079403400240480c210b0b0040e80501e0a00b0001e1587c0c0040440980214881c4200254204402c1c0101d4501e4211020445c0540d00400040d42400822421581c000c04607412984e404540458844075485500200074000316010800d1030840501c2d03016120b401c1d401900200401c40100003540191200b0390b07244889018200c644800741401007008104542c01812101c02d8600c0b124004509620074588078416009642207003c9002c600d01440c1d0080c05c055005002281c01c180349801a05802180c0207162000310040e10300040010903200410081 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 667880755 1250 667879505 667879523
    0x304030201211107020406080d02120a1407140129040b21070e090a110d0303060320031513030305062404080f0f100f09060617060907050a03 62
    0x61040a4005a01c0b40d04000000d814511100028094000980f1440380211821b005c59a981c03806070780c403665078490000c01604505441c00885422a0050190030a10f1510b070241c01c203031032004141034002d0139040752902150103003680f884809003c0d1210602080803100b02c8c45c010520a20100011a401305009940303076856a02c2c07680e1907441038109204c415085075003040405d9885525200940112401440303c880030844ca11400600c1c01405075100034a200030103402802c00611100c020300031020161510b2010000a00540000b6207094a44204901c9150340c0010541084d0381c031880b98501030380301000c200d01600e24130042030100307400d41000140c030b40304c10011840410f50810507803802c00a0001c40c00c550545400100102d034040f400f640c0703407402400309050702c802c41c0032081e1490b42d000b43c02d403a00c2d09005900000c8000d000c0040080c00a040782c0d00c09069500c139900c0114400e040c1c0c011800351050601050740c0c002e0720480074040325414070700001c82000007800040c141e010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 667882005 1250 667880755 667880777
    0x606030a05041a09030a120b061b0c040908120112081c1410031b26030403060903080106120b100e120304090e07060f140c0312040506071b02030304030201 68
    0xc00540c0c640d0351000e031116140202c0c500f6400c00c9503030746e11514041c000a94040c10351014400e29114105410b180141114540344820f8210510000700e444800e00070302510041c6407039541d592190b9400c161141c824540c85140e07042151031f240d40140d1010f42010072241c080c43c0040c080030308540d04d102004006001000781c1503900401800742c0c861076a51850060180401074400070f003d841207030320401208409080200c0c000c2e8901100340311b5001041040300c0304d541c254400c00c030303c03002c0100b240c0200c07410181d981c1c48041c181e8240c0302c0190042020f0000501405a111015540d03840b03c050080c4004003400c07020420400302c11304240b0030031240000130000d030380e9001a0750030802040c0b400c91b40c4a64440202d007008141c86410544035100310316000038100e0040b0515181c2400b980c682c035160401001c8180703207035446040006954001000400d0001d48012810fa0059008100a01d8246400d45000d0500400881c050070151071800c000f20040c1d0700001120240c81d42840d1241c0c2c2c00d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 667883255 1250 667882005 667882013
    0x402090c180409320c01031803110a080d0203040b010501030e0d0e0a0b0c03040e010608040305032214070e011406040308090103090f03020a02180402030a020d0c09020a120605090606030a0504 84
    0x4440714001107803140c1080030b8a01381c141c02001d0104001c4000240d840d40b82c40340006500b1101d2225000020201c0940b440012078043c1c1964001b4100b50b0301652602c01990307445600c80d0740301d00710003070025901009000a12401c000041c1c0500f0f820700b010010a0952104c43e03a558a05800701c00400104028000c0240c403494400f200410b0380d5801c0e04e454140c1d078150541c0b2a04540030700b0080b10a4407000141451284010030f0049425880356440c58032010303400380009105d004a07000c0005118845c00008003811901c500c40b03c2d241c4c000c2c8c0030040c01c0460000c03c040301a40840020b1a68101e032860035911442100c0c11240c0c006041075031114179000680c050a164040a44000001c4a1100c181a008240e00041d10710071203c2260402e4081c110b041c41e01406e031001394140c0c0c41104c0200050508074804503040d8000c00c4212401d0b81d54a003401c0907640310f8544100001c8103a801c04010b00314902030b280141500300d8003020340340340c20b001103591800001c00000d2800c1e242c00201e8180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 667884505 1250 667883255 667883273
    0x90a09140307030905091501090b1608030a0207060c02120d0e011b02030307030b01080f070813051c080603060c030f0a06090204150e09090303070c051903080402090c180409 76
    0x4580e0010079242c6410603828041c2c100700c09482001c1c080c0c1880300c0040d4038100c54450007240708030161241c0d207599040040445090308498040c203460812180150b0200300a030300510321070540c0d0040540e0301c105911f04001500c5c24800b0034000d5601003c464920f01c03040070151001c101c945c800c00945001c030909043d014009000700d1103c840c10001005d0f446c02e901000039031080f101c9450a210340c40b000f200450f0380742011030303021152811110100b13a60600c20901380d80c20088500880001c10800d03103400d4105660210b0a001072041030080c01030b15038011050f558000c40c103c0c00b0346190314210302a20000d100081124034204108000188003030310a6001c0b80107002c0c1503004644a644440a00c0c264400c0c001d244408101d01461804640c0762032000540700312000800f640c15038030352920599074071841c110101c07228010381580a04100840c02442e015034041ea07285499401c040c0180102080c0c05003400609402c20460000500c50407044000b4441040d18001840d010b00e0400b0410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 667885755 1250 667884505 667884533
    0xf33031203021905090f0402301801090510090c03080408070f08010e2a1306060f0804030c031b060c080a0b031504080d0605060f0703120b090a09 64
    0x400c400d104155032110398540c1c064a419541c01511001d0ba90b40e8031800d540c580603200d41c05510004048400100d401c06402419240080f00c440105404251103100c9000759864660744015000001f00602007440e4801c1104030130401000b00b00c02c402a403180303902c40c0030024001d074000342c6400c5074804011160001a00031600b1410300394480e03803580b025545803d4a0721582d299018030742c00106e800311041c0b00d0100340c1c10342980200040c036200c0c6807118124408078114842d201c0702511042c03107a1038540d903a0302000710148001400e24100344000c8c2141d01d0041c039402c00c00541400700700010760403800903100c840d01030810038116620780d04224011860340c2c0c40100180e0411421070422a04005524064484000148801c0b840745081c541c6c0c4641d210340400c81803103090045800b0034610801044840c440d8500032400c40c1e11000482c1869120000400301c0220005400e010f042e4406c0c040b2030348109046052060b07000c1440014040c4c2400381c14030441d2651007841350100159120840c803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 667887005 1250 667885755 667885763
    0x5280903090816080c090f0a05090c04090602040524040b0903120403030c143004030203190b0c030c04153005010e0c0f0a031e0b040f3303 61
    0x182c03c00283c0d00c00d80c00701c1d100d2007001d84c10321030500140b4180c6040e041052150b800c140c8040e000381d40758803001000c2c000c00b424458181c014104d08400584681c000c80d54424000e40c00941c2e1240341c0024040d02d9402e40c840c40102102000040c00480001021903046032200740c0c030680c48196000020703080c0050500e02403a1031800050000805402c910a005068041c03600e043c082803181040c50707200c501200086401c51054481050b82741844020710300310392a210821403d1503141d03808281b0b071250003031a607620b00461844c038804100a860040d0781c00340d8107030001f03800c5040a029080c1c1c1030007940683e40210085c2510400001c0c814005c2d60b0442c520003404604130b114035680300a0701107441540003c018100701c00481c1100744c40b19064026601030840d245005c2c138681426101c0d4119140900c10075031209a00b000c0008a02e8100c840f92044400c00218035449000308021156400540d88803c1e0401022a4520700d94107820705060030000c0d071004072001c401c101c0d140b2001031500014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 667888255 1250 667887005 667887013
    0x909030d1505100f08160e0a03030305090d050f0702011b02030a0b0106120203011401050c2505010e1230040e06010e090408041a09130e01052809030908 67
    0x1680c0584808802103900c01c0d02c20901c0d1480c0910b048070700710140301030701c00031030f4504006c5803106480b82801c0f0541050340c42c2c048201c0e040354000401c00840c40c0d1081e40001d4940c000d105000c4070500030407070010b1840c2069850000c0c0069046101d0080002c042e05012206400e080760150400800761a56402425100006100d14008001d44030070b0150400140308081c0c3c800560140d8401c49040e5154900c813008040714040c01100c980e84000c404d61581e0040401a54010707164101c0e9100c1440c0041982c80f5540c10a00014055030508000c0c07485100741c140004000321001c0b400d0303c201011015520b03100b0044000403e00b24132071100403140d01c4030000c0c0018a0f200480c2d0301c00c1c0200c400345d91b0088000020010080c03416400c0d0b5000d005104200700400200d50080c0c5e8a00100d10303020305d11030810344e4030030000720440909081440c03126201c403540b1040b007c003841810303444403000c0e440140f0340d0450f100400803409115a080d24559403501001c05150041c1101401440128111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 667889505 1250 667888255 667888271
    0x51b010e06090c04020403081602040e0f0d18061209050f0d090504060906030b070516060908130b0a021f060506030c040320010503060d06060519031e0507050909030d 73
    0x9a03503101d0301102e075903801d4041e035100c0d0000e0b031503d802150200d03038101d18014107000d00e000b4112043c05140c40d04980c8141e4406403102c0040c0140442c3c0b04902c0300f4000391804c4601c1c024050030001c03142c410402094900c09003031000540003c01c048c05074080c0d0300e000070403c48501d8141c0c42c2c0020401a822644203c3c4260b4410a511889540030b5030030540d424010903a0710410340041c0c641c40d001c000c00c001c189000041200d0b214401608522226200b018400070340303038a4800403508186801d03102010005528010020b002100c00010b00150321014030340200614001d450b0856071041c0194204404020b0880010340d400c40700141070010410303540ea040c00c21220420f5400742c40219001508251120500c06503089981880035040e120b00f40341d036444900300400004900b608840c001d5072038a000c1001d45400204007110540d078410001c406055003411865100d040085200c4203e0700e14003400051404103551040700d00503501e01e8442d07200d8104260444c0543d42f00c030042e0318130700744031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 667890755 1250 667889505 667889531
    0x11413240b030f0114040b040305070b07030f0b12070506090409120f1b080d050c070b0406051f1503090521070204060501030b01080f09070306020706020d110415051b01 74
    0x103007410000480894004030031043c2c110b401d80b00c050342d02e00700384211000002d010030517074420194002c1c424601384d45420100d0303448429540003600c40400080c1e40b402480c0d0786134070714401c500d40c16104550384446d031001000d111f42d58581c10300480c1d00905000c01d5178803554403a5002550419440540e455101c40c100303400403c01510002100e00081c907002c181440c1d000c6c0e421010984503003101121780307400c1821078264003620024141040300d1804101e004040ac404000090160344200000300d200d0912070786c440140d40e6500500e41d5000100001009070b00c820707028402440c40503043c0401d104030541001c0d0b083c4001121165440c3e501c040c1101c80f00c0c180c0c1030042410600c00c403010020b8585442c0110100c80103034a80354045990707200402e507070b0b8900d414003035406926801103a2a95441e84e4804091b43c102c01c0c0c5c100c500d1a004500c1204403102c83c055181c4840024214509040c50501c2c4000000108040b07a0144680021541156100c0540311000712900c20000d00c5580d02480c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 667892005 1250 667890755 667890761
    0x20904050109020108060618010f110f1501150504030618020307120611090607060e120423010302030424060512030a0f050913020906120910060801141324 68
    0x20049001440c03443c002899407500105480314003100c18454001480120012b40300080702a001c542404400c0b0510344002c9020401e11015401c10703405090002a481c40c03003c1014410b80000e44501c40b07038a84c1e4940668040140c1e0201c980240d404a00f10007100144004141400c2c406900b5004001004c00c1410314070b0050382d4414840c200c20084084002982002c1c0e0091030b400030b0b4054410002000440c980381c01210b070503210801615000780e1106251601944503a0111041b0901512290000b18190090703004003103081c20254a54a00f6950b020303a005024080c0080b00c0400c6000ea4160b620b140e80302c2000341c900941041000c58044d2519a500d8010203165000910b6000748194000d1040b815a03515001c082e004910f01c400d4654150069002080c1441d00404240000c49050b001005035502a4902c00c0250118225003500c22064070000c0d04000410b80c18251001c140130304005020b503110660101c12110140607282c21a9403001c007445c20700001e641e5800142e0850050381c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 667893255 1250 667892005 667892021
    0x1020f030717061e01030609050112021203040b071e08040b09281502010e06100e1b0702101704210c081b0709060b0301061b200303070209040501 64
    0x2480744034003490801e01d15100100221441904003401d6841040003113043d5110100d099014180030070416203500080c401c07144240e00001c6892500e180c098103605240252a001e0320041010710300c1c0034249000001c2d10b1041700c0b0000c05560189c90040040851290300c80c0c0c910b540075030040c2e07655039140b0302d450b0160004001207208243c0100d0700f10148031100703414525080c6818128992901d031007000c20b680103540503d8415552a10080408814240401885036003150121030141d801d00d402c042c01140c0040c5039510100859036041c034122005010749001d07690403a981355070644603120454482a05000ac411030140400500013008881002803c10a0803514040c0150400e03079021190b00c0c49200e0080d206100410000040c00d02c501c800c54014a4000c003160f0750280e984400c0c1044038071680c00030219400110050000c3d903804003601010580c0044460460741454441f2021007249000d0034030b8103250202c4030f40c03440e1000d005403155650010303d030000318134244c00d00d1400b0302140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 667894505 1250 667893255 667893257
    0x2c0901060e0603010504020109091a192402070909080c01090c0e0c04060c08091f0909060504020a050a080702011112010f3203070b07080c0601060e130207021201020f0307 75
    0x201e0000d070907424144100b5110b00c6d01656840c0200d4a040b20060060007500c02e5844800002e2007489810784480c0b441e80d0004c0150010481c0c1c3d1890061b003020b800c860810030112003080c0d402140841039000800109958001000091000092500c5000352060b0542111306500340b400c2c08081c0036408101030304403984500c1601d01581c40b007850400610a030300505021130220140301001c0f40340400504245800074000c212400c0c0401c0e2014000c10320320104070001070a0240c14440030b620341c0503510003071030141c0f02517003889885400a00180544000c41d41000449000100014401d400c402840c43c03044144542d2110324030380048450009014405110709081c0780040c1c1800781d0078410700410321104d04030321000c2d101e0000054080e18040c1050b890312500001040d4050300c6030041003d2441820303400e6540341c0f250141d0382801d00583c011300600001d07a0300c8242035150300c144591070209080c00140e4643e0a840042e600160500c50080d181d03202150a0065501d024000d6001e0061 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 667895755 1250 667894505 667894529
    0x90c091807051305010f050d0b0a03050a080705010f090f03031a04020c030405011707050f0706020702130f0c0e060f0d020409020a0e011209080d020702040b040c080711030309072c090106 82
    0x2210010348500e10f00001c1b00000070010420000c906103d41c3c00b0030b02080b0300601d00181903540f07854240c030300102c00c0d10665880c1d600041034410403009102c0c0f508944c0d10303035005020810454a401d544466084805400c1c9510742449828403c0042070100101c00000c2046480d40c91221819941e6041800f42074040b0340c4500c0191084010360100c80d1103446a41e0710580b8080d003601400b41e05400500d011a5090380910109005a450b0f0450312107401c01550002000c8006881300c01c2928180700e11481481742e0f414205c04243c443c04216010140f544e060380e90b4408502c007a00c0c0c000c5c0300d558481e0f0301940c0702040c0d02a40700d502c10304000d0106002d0341d50384140c0c42c101c40202c045801da41c0d40100b071010104050110251660068681740e800100000780340404440840d051301d0b03400306074a000540201c2005a0f2a03000884001da410002c4000d5055160084c070095a03452940500070000d000000072030024007240304200014070482400f150a418414641806045c040c0121190656 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 667897005 1250 667895755 667895759
    0x8090319150c0e060412051002210117120c070509011211010516060b010504051c021c030905040e031303080a020c0607260405030114160c02090c0918070513 69
    0x1c07146807103102240f4000d10440c40c261915000f1035030150807510031a1321b80a030300d030362181804180c40070f05404d01d2401c0480c00845a051754800b10355030143c00c100740b000388800711052801000244821440c0d1107c0381c0a94030340a0303c044170305d0003032903911055000e0110740000ca0300e000ca000d98903108501c00c030400b4826582e031030f005480ca80510b091210300a99154091004200c0071340194620071418140070340b800c2c0e1500c011410511001b80e80f944e0240010b00c01340110b080681003550310140d032501080b480b2401da076008141106510a0600c5161914862140c0038000e00c1101d81c04d15a001a01d01030b40e40d6480c1104864000e0301025001d405407000c8034285003014800c80b0320050344200103882103296140385400480d00d42100b0b001c403440901002c203098074240304282c3d100102c0018500145888100945d1500c5c418050b40c040022403600540141c84101c45290010f0103000105d460b0075a040c04a03d03078a00007581304101c54001d50902500a1700100100307000100d591a28420315 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 667898255 1250 667897005 667897007
    0x140405060109080604060c030b040c1106090714150c0d1107060212041e0302041a03060c12040b1f030c05091e16050d0c0201060f1202010c08090319150c 67
    0xb041c14031078603203590402e00028002450720f038080c00000d50b42e070600040203c44900030404440400b20340030081100c0d040c03081d440c1c0800704109640500d100000300784190404102c08500340c050301c20540541e480000001995146006403183d01d00010102c0d40310588801001349008240302019a15000e028000300740e088c8089600d0194074100d00d0460b240c207140510406414160001c46d0034071126040e000f00045c0d88601070110704a860840004900f4050410182400806081c07203070615410045c0c600a01d80e45c25115170720a40102c5149810341c2c1d280070701d042420301c8102500c1501951030f404400c000c2001440015103d0944500201d6550544c1c240c8141811800700103002c42c211000071595003550f05a0000488030b0301d4840e05185c044540302050b55110a09000580d449400902c400c106940c0800c0042030040c0d0307802c0d250b860680010f4940001c46202800710350001031681000d481c1080860144400411000f6400c119424851592a0a4240c46810368200070000d601c0c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 667899505 1250 667898255 667898267
    0x4081221072f060c0301060906020619090c0e0a0c030507020a021f02122110060f030c0e090906160203071106091207060815040e0c12030408071404050601 68
    0x248019180c01d600004a5441101004841c20502000710b0b84014500707800d4200703004190103165900c2003240c5039410700c00050180d4220780c000c0401c650102003002003900c0c0110858803a83c00c14000043c0c140ea02c2d0400b840c002215401c281300c0139a00e8001e20400102c142d1250990500c1603404020a0b00c800c2012600d03859011400b9500a045260300c00700441802d10400186040340100c44e0f65018015180c411070f0081c2c104049030003800c0303060155841c4003207110b5a100810105c540002c50401c500a4014a000142401016a41c41c0010040780c05000b00c91981d080040c1604401e1501c280b00d55a100400c94903a00c0d00e5000c0c01e000c6034103d000000b07035802c8584c03001189103080000018402da039004641d207594411104242d090190348107120310741c007030b00050b5240803952a104040b0340300c140915000c03900844c98110303624000740340410b0000800c1c2007100c5802c00741880640180c914029600543c00754040c800c400a038598040404445c2c00000b03540c280300503600d1600555807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 667900755 1250 667899505 667899511
    0x5181812070c0f091a1e030a0602071719050904020405061b010f29040f050117061e160c020418140604030807080a02160803070216050105090111010204081221 70
    0x20500b014059100789160040204250b8000d00b009034110004600c0000d02c2c140407040d02703842c1544d00181000074044881080840c1c284001c5e601490513264080d4524a80d0010110608020020580981c1551660100c40040c04010300603078036110030014501c1031581480c040752156292202e407694081a40c005c20114402c0e48056a10080342c021101c0030302c03120b001105500c140d413407068a4804510b0303c40e443c06044098042c2280c1160041c6031403511202518950f284200c000b681c2c1c443e01e00f0640900d5000c3e84081403000e903941d20315002d94443c444644001d512a0402d24034007003c04c061445021442d000c0c200141e640e8104410b480e031204170a40c0c000e000101c06400099102e8000d80c030450b082083e0740d80041c5000844180a00300b030203400030407200280000b051126130f0758100701403000f440e0f0303802c0751030049c0d443e1800181543c07043c04280c0c1e05114812002c2d5a40b1300302076054030009d203041402da401e6042815140c0066601c4100d0b11914032000000c00d410200c2c00d02c0003584 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 667902005 1250 667900755 667900781
    0xa02010c08042103020f120105031506030c0d05100c050d0f0b13110f0406090e1e15062710180306021612031505181812070c0f09 57
    0x1e58107030310a80b0028910071049000d021326400708110100b419070500103207103820b43c40d4903651480d410030041504020070071212038203c408a0003845000d540c003049a580c2420b0444031426541068508581410036145106d95298036012540403000d0b042401007000d00d0020204210030b155200410049500e0040750300c2c0c00044a030b8072807451100c2c907405154200403d80e111810840442c070541802d50140c2c00c82d40010b690780f0002c01030b00f0103031840300303402140c0f841099071008076402c030f00303500c6090052400104850000a451740341d22004210742d200c6106100bd00800c3d03074050070000342d0302400c441c0c1c0303800f072031205000d6261684110014144c580702c107a80c075680d41d4515103078400a5003020100d0130b042949600154009100c1c105070360320032120358a0200d0a074103c107202c10b00183c01940304501480000b4142d001c040e0350021156030014000020910b51200c1001d468904074010003080c0c02403000040107020b0180115409e421224845044d00c901500c2c0c90040c019500d001070084 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 667903255 1250 667902005 667902023
    0x415180807120306120c050f1e0121060806010806070822080f0c060604050105031b19050301050106120e01021e0a0e0a121406071725050a02010c0804 66
    0x505920b1900d070340c990790742ca000b0031640d031100705514004002c1c150481d5914150f030000c0085050861804581e0402203070042415400c6203005281c800e002d18202d41001003034405110711151540707159059410392001000a0713929042c04580d0b9180a0085040c01d02c80c16001071000303403150701c50b944604540c041c0d8659512209000314800f1140d4003003110240c1c1c060005044007441a80580341241c094002041d080c18a0f80c00c1c081200c2040c0c2110b80aa0001250b00810a19007114000a03240c280d138801000e0b400108009840300c0c01c0d8102c2c4da03055003000d00002e0f4407030380441c03068944142c40004205c80e66064050074200d01c980200180500500780c10140c5d01c90058001e0640c0d118141800100240c82c02c1c005015540c441c0c000240710744c0d2010040040c003013143c9003d22410504001007506080802e0017030942c0803091900d40d0b4884500000903d03040b54801190030142145076810351201810a000c1c089401441490006601e420601d00520f0301c1540551300481c0c20101803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 667904505 1250 667903255 667903267
    0x150c071823071103030a0b0918190f061107150209010e0f04150603020c12160f0c09050703092112240b0a02070501022407140304151808 60
    0x1a0381d000030010082c90500c06101d05a414600701070000303500c10003183c600080c01c81c80b1842040700202c009450050500b0500480703840318000040c6074015040200d41003d2603044510b05500c40640041c0c4c014445410808079440040c01b240c060009588540c40100d400701301c0c2c0d00c1400890143c0000b0070300240c00c0e90010394a80c14041072000c0c2460000e403005c0341100b0301c9000d20303260b8581783e40540e000075400542c8000c808010b011044800b158180303400d03c4c0040070b100450a01d00c1e50000034100c4018200c2d04410400c0c4500c404e401451114003d225518215001134002c201500d4207640f025004240014000519040c83c21038103010b4840c1c14060b100b0700b071401c00415003500c56080c601c035014200a40030602e220300d81f00400032280600d43ea005030040080c1029000e911042c10340d8052412021034017200e580c1c80c40b030410706e030054880300d9441000807a26002809144c140d01140041071000b400407510b0002c1400741c00740c0b4140041c4584051020342c401a130000604140014004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 667905755 1250 667904505 667904561
    0x2070b03090c1e09070801050f010504061e0531120b16020c040614130501050a030807030309060609050f01050102071a090a0806070815030607120b150c0718 69
    0x1156692840c01510f00d210b0700c242c0c0c400300e410858180d8603600460f07200e10040002d8a04420f0342211a1800e282007420a45400f5024102c540200320124080344280c1c135507000d01d4441d0050364082c0c4540c3c0303084440e5003022030818442104800c00d400710201e407603501003003038a41c2024010016a0100c1301c6002c0350b0340c0500d1610340303116007090401140540504016907566900400000d0402d00e04202040d59454041040c0c00303211900100c0614140401000195587d500080440781c000d0052a909c4910b4a07040f0003d2890840c004c14892808030003040c2140c4a078007241c4594540c41308c1c0300c20f99072201e0041e0381c0c40005105000807500c0742c1040100e0f203020140500307006040a00001192a00d40b0115401c018044600c800007503001c1080104d9842c0c06c00d004146c2d6101070300541043d007400d640090800c0302c174803c2e01c0f480d82d440c1c001e143c6860303c51481d4003070401c5a00262030703280c0300001c1805807107a6071403003441d9000081c0c0c400006001114480d105141c0c0c41d03154889100c9000c0380d6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 667907005 1250 667905755 667905769
    0x3010f1a0418090c14030c2b170f040501030e06100b0f19110d0c02010903061a0909100e010b0a0515071202030d0c0e010f0815030f060702070b03090c 66
    0x90401c0b119480c0c0381c002002070341c5006410003800c540d40e280c180801c0043c06051924078003681103481800042d541c4c02c0690781034030307103410782c40607441ca00fa070742c0221404d1400e64980380d40480422440300203540089a12050040c200f0b445003640d0905c0314074807500095540e10320076924004400600f0004201084001c130003000303d03c40c50340003203003802d0060004200c0d454011a004000c0344018083d825080c0007032200d00c1100009041081c100202900002c3c540340341c1e030000a04060359661070300c013840e03001080d000c1c0300c050062400d600f501c0d200c0d140c01c2e1074a02d8404044d03512414090032801b824018010340c0b0340030001034095840c80740740604100c03034240c0d401c00240f00300808200810220304410f00340d551204850b002199070301418031b521400c444c0c607a440041004103034000c00d0b840c1e0b03074040b00b000d0a256440ca00010351380c84411b54141c00c0b441044100317606106000d048008824040f854500c1120a83c00340c03040641c1e55910300200d844111000001500492140607251801107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 667908255 1250 667907005 667907039
    0x3060501062d1b0f06020307030501170c0906060c01180c080106060c170403150516030b0120010b030d1709060601020307030c291602030901122f03010f1a04 69
    0x3d101074032180c0c480e101c0c0180f4038000c25059400319000000c101e151034050088134010f20316404020352481d0011419910344403545040743c0715541c0e00010031b01c070f555802d064612203003d40008001000d580885003006540d0318004a98101c0440400540c0c1031042c03280300d0483c0d0464441101a01079640c0fa540141120340000540180511010010507070b48a62070201e52050103000485013030030901452100f07001000c40c810181405400442a68440c040403081307101450070800c0502c0f858846c81c003502c0d00007480f54140c0b0489800075040c40e40130719820003080f4445116030f200d1301c92032015500d44a00711a502d015a000b0800440000d01c18409040c1c454000e04641c0b013003420306025000b0700e80030303940140190150342c070520110794200000714048858500095140660101c0083d007100301d1400c111142c149d40300482d44800a101c4000070705540c80c1c41e00c2d20500141300c02207149541003801411540420301c480031980c40c40e443c01e007501810154146509140c42c1030380c504400c541c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 667909505 1250 667908255 667908287
    0x72f0c06041a030a09051e0106140a09020315030318040501050a050a0e04240603030206090a0b0a020f19030203070908030403260d060305010b100c0803040b061903060501062d 77
    0x2820f110170204105100b103001c070900c2e01e0403a03002c06031030301ca0309800c1d12400e800c500c040a0304003a0700c00080d030301c0f028444201c400702c810160b169926041140001441084200d40601000440d14004030208002e840c0b220411101085030740d8882091040d1210540030342900158401c0082c00384218076411254401e10407a0b1222420880412078040800b00e05200491746c1d84a4005204068041c011598080541c000601c1c2d100459114240400006410302c001142e00040c20030700c0c82c0e5100c04484414a90f48582c0c0210042644010b0085d407003101d142d000514042c401042c01d08001c000c550440740c020b541410304042c640400c6c9440c0c540510b5400e050841009002e07203510650107410700560059000048101c420014805003845402c42ca2040140f04601c0c800000e84080071b0369005a0440c810701d1035942c450000c500303d03e4588010038080342c18440004104280d642010b4140d9102da9205200549011005030480f40e41036940509100341d020003540440c40303100070201c54068 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 667910755 1250 667909505 667909511
    0x6060402070c1707031505160f0903020a0e060f01050340060f0506010212041203030204170307030e1806090601140f04080c0307050a090203072f0c06041a030a 70
    0x5620048600c01c40008209000364004c03000410500441c07420101c01100c0790340041c029442d00c9414401c8003c03070215241c0078000e540001001192082a001011b190302410b800300301a01e800998840c0c0100320b48107403284071040b41d54005940300b5016240688442c82000701c0e8089120515440808121001341040e9849102c0301700340c1007039980034010f450050b040010039031000f050300c0082e80c0c4010507241c15940107078403c609410f000c2c0211030440b001414044403002d15868218013031b1003164890f4140b034690754401c0c0d22101002c0000c041e01842a121889008046001d2101640d60782c0c48162040f051580010090700f041c19103154041e505244c18642c1455000000300c258101c1411203042000106090000103800c02000e42084000c07001040c040c0e1411780082e80b5442a80225249181c01001140180f40101003c8850042030b04564440c603621a01c0307039035041101115159280700c1d204c001c030070605000c0100e6040e14a2800c11400001c09100300b490b03aa0300c00745c0042d49840d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 667912005 1250 667910755 667910759
    0x902190c05101802040c1e030509030409090320012904060b0c030a170132040204140405150321070503040f1503020310061b14030307170906060402070c 67
    0x1c00d11861440e002c04050a407480ca0003401030201b2661080355040501c0b14105030340440c030f160074202c0740f240e008038680883d0369a00c91000508500a542c0300100050424282600300341d041030031542080d010140644040704d01120907030a0b1904001c1c05061040003202081001c050103070001c6000e41d02500c0070808a5856070303001c4181d4040415011507800105480b8038455100d2000c2806000c134404002803035040019030a407114406c48204003002c1201d090f2070401e401000c80043c6500010411034503141c1e50599650707142e4809014901c11382c039000000d00029481c120610b2031100107401001d00320303610708050210504815080d07440060a2281c034000a208200610141c20503032400300c555441c0c074201c0d0058441d200001810b03d401842041041c0000654841c00c9903a140741080443e1001100304e008a43e0141025102000d00000030844202c004001c500814455682d4407020215042d442c04240f000e41c0c81c03d4440e04900041201c0d403401e030b00a0a0310a0040c4d0000d18826 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 667913255 1250 667912005 667912033
    0x319090507061e05031b130b03040303060306060602210906070204051905060607110f060c0109210c0c050d0303021308060106080f04021809101409070902190c05 71
    0xd050303021600160900c00104031a8183c00b0110709202c82c10b050181c15810a2070709a070301c01440c002001d15101d004900d1104c4001101822001007072440c3c40c9079524203003410010080c1c880c41c04261011410080e001402074400514921102d8042c44004402c035000410206c550b80441600765211109000c401d000d03a98500c04d4a02540e43c1140c074403403117080001c510003502c00050400e44154801c4c0322980104d1480040648070240c100c880b0108551814001202d44c040c41049803090340ca0003405000b00f10745001200d0000c900b02c801e604418000d03500803a082c6424860007009151a62010050382c20b2004441880a11908000d403e00241002c0301d07910003281c0d8001c0007a6480710300104901038000007401c0e00020000c0403140c1c03d250580114800d0003580d02401003e5450000107282c0351402e0012086030f000030700003800445505050703c401ea900541e5001c0540c0a209400504882d240c401c88280c3d058240c401d20704c541c5455810f8030780e00001d26080da00d071b000b40ba0b8035a102ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 667914505 1250 667913255 667913263
    0x140306100201110a211808030601050708030a0b010e090c25061401030c0509060d03050705281b06090605072402030403031b02061305071a0304120e0603190905 70
    0x2244c2d42d441301001907032500032202e00c81c0d05c3c03100c10710705e1842c0200d204884243c00d101c28620b03d410144560303582c0c59001c012581c40c41603d0028140b40400f0084c0621036440780c01003900b00000f680d80c010301c07850744030404c0b81e800c2095034060840441000340407101400a51629800d4169240002c0b20039601d0300c0b15000d507051a0580041c45803008014001c004100480d40c02800f810f9800c0036035464006c0100d403140c2c1ea90fa501506106020900c1c07030800408111449400403c0244400d0301c041401c4807001d03c1e0b518000848455803ca54100804520002d000c02103442d1550780807403841c60001c040e40e13554000441960100d05511f0b80200e101c0185401000c00400c219005907607150508000741141c010101e20301c131810848003041c09243d800103c9a07081800f030086807007038003070318a009031508155602c000c0410040c2e0f101e03046c0c1d039100c1c60090b51180e40140b41c1d54030f513451110007c4902e0001d185031650310030001d20115800222a84803c000c0800740e060000d4000002d407600303458 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 667915755 1250 667914505 667914517
    0x30e030d02031e07090302040203060d062d0908040614070b040b0114030a0c0e0c071707050d1b0b040c03050619150e06090c210a0c14030610020111 65
    0x140350004140101902c030f00500c241807603030392012440b00b828440740092111401c0c1c40042d1180f5008408100c0544d200e80c0c031441c503a5800082004029112501002ccc9401441c0818003049042403044004600b54001c031071885038441c1000e468541001c00a6807900d50758580600310490074000103000864203200580a1350142d1a80e850315858a0780201d40c1d61904444207002c0d401c1010804001044a07801c00c0036100b590800210b903980c2d10008400c580515003010740300000100d6000080200d6000a080041c018001c4d075030340d003404c2c0794241c03a4202c6031141e0742c108004e00300300c45000c6601c051010380c2282c4130754003590090350350b512460714110b0141ca10600c0321503c6240800940c2c494070a2500040641602c0c0101501c0c3c007040001e50440200f8650041301c0e400000380c0c02501343c508543d01c04a0001a034039003007050b211840507828084541140d414540038141d14a240145400a08020011101c40c5155550424021f00000c10007001c400d564070761114039002c1d0050006008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 667917005 1250 667915755 667915777
    0x80d0e1c0b040312110c101109060d0906050a06080307060c0314090c090702010e0d030b06070204151d1003080702121e1c080606160b0a0506120607120b01030e03 71
    0x501c4c1e1014241c0c4004850005c0c404510300c3e2801c0081c100f0704180841d40c807400b251035040004050360344041c118000d1140585984c2d00000010341746205c2069513004005480c05a01b0070050b42d681d0910890860f00c59018000e0198001e006c820000b40b42a004144203080a10b004181700315144008241694143c1d00e449807074004215500490600c0d4082503030091061009124604480081035150100702c0d12080030107480782841f00d20394803988111045207a01400c200161048000700904444e403a0185518642010100c0100e1071860b00c5030030b000e6009410580b540500c0e41e078405420f58080c640407604111010035001c2c44040520042c400320480001101e000104100200d082c03072090392810784440700101066100541c0010100d034050002c0d00d0302962984c0079100c4601200c40880c00030b02c0d02404401300a0034444c5504454010303101a0b41411120903044201c0e81c854904864103400246a607103410380d203550395080314401b07035418100000ca401281a02905503030048894031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 667918255 1250 667917005 667917017
    0x3090d0b011d0403080610200d2007090504110901090c0f0216050613170304061706030a0318080106030812010806010311220f0c020106080d0e1c0b0403 67
    0x41c0b00d0708a00c800300c2c205075038001c000036407410f640d02501a403009001b6601907484100501c811034001c0900d464403c048100034030506130a10340840d0390340e40380120031000411404541c40480d910709854050008a00058240385050040c450014840204240c450a00000d00704400e0780f1502d4410703010f40750481001c5800ba00040c3c0107441507203207030341c00c1d811580500307004003654448009260545101304e450300d43e5002ca804488520040325003020a0810444c1c001c44a1413100000900440d8040c5d241da81109101d4142d040c101d18088981581542207159107100080c4034520020720b03d10540070504c240c45e154160303103003118060741086406900000741a05075540d4100414014010b19004151030340c190b80e5881555010324149a004060122400b040003001d80c1503001029187c000070402440d1034400c000103031408000580c050752a121021a00850200c2d202d5001030468580034150248a01406101203500c09800c0d2019904844840000c00014646000314042d40c2c5007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 667919505 1250 667918255 667918259
    0x9040209120709060b070c090906021903050f0a02040303080730090b151e04060e070203070309080f0a110d0b0f0f0609071b0501090236070c02090903090d0b01 70
    0x38400c9030b4040d0071130011210148101000038449903051f000b40e40c503502e0b01140d20750781031800c000039004800e000030b4180b2241c8090910180c1c140c1c810381c8105003440c822590b90309c40c4080c9c2c82c124031580c04003800054a00c1c001900241c00f031070b820700d440681d018050410007000c107007000c1c00428000c1100700b0907499964400501114011068100c0301c0e04521980a000d41d01c00592185022103202640b06c01c030b0420290320395900c0c0e00860080250036551845403030040e01c000d40303c3e800141d0031008106c980d00e01040d00c680004420508501d80b0300200401d60560300c401e010300d80d050345036580c03004940403001c001440c43e1800314090340928840040700c0c2800181d0b4001420001c080d10702a42020040040c0301d40e11403050b0308010f03082c175501079501c078850030641d002d014a0750300079411115124441540e00c0556007840064000300501e44c04042c1c0004812146600c01d0b59200f0001e1280c1e0604805440e0400220350480045000c60349492240b01c0815807540801c48180c450715541401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 667920755 1250 667919505 667919519
    0x603101e030c080d1101060f030f21080a0c020a0507060e0607120c122606300c010212040e1012110f0402090a030b090705090a0603111212090402091207 67
    0x105d54225a0b0300c1009000440c1810000910b00002e03100140c64003614043c1d4900f0f1112929120400848880901d81c000c0200c4d000980114400d48200940b0f0389003071000380f0f007288041455045980e110b805416010320745031080f0f509140c2c4c2c10721503604c003204010b1b071360001d03411500c510408a0b864481c0003c004240c09c0009090600b0b03426001400050303c3c0e5844c03c003294440602c5440c4010585100075100d840100354540b00c80444e024846050002d0400d180f00e0061580340d69900d03202c01c4600c6040b00d07100480c0c1740d40d541b0130004485013081c0030503c080300b01d94800395840510b1040d400c0506542e440040c24008101100ba100b06c0c80300f40c81d907600c5041c8040008a002c40c203071820343c40c000c030520200f0000c2134280300103000030600c0808a161503500340101c400401c0c00808a12503130034040249001072090348000c4480000041a190103400d080f10040300400064001d000301c1d1107180f805141c10f0340107000c0b00703034403503401c0050ba0303d2a51400000010110300c0001001c0a88c10008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 667922005 1250 667920755 667920767
    0x1e0301090e12280507050318041104050a0e06010c0b0f16030507020a02130e0a230d021e0a0c06020d0806010801050d0f0c0b0f030a0b0603101e030c080d 67
    0x4800c559002c100882e0b940d19484001e2141c1038500340810049a0120040444030f5000d0340300000e100c0d0200090140400318244a41e0043c03450440b81000a0080300c0c0d0f0188051042d440b6103034125524601c2007080f066030040540c1c1c03050040c1881209140c07503541c1c0301d2506230121190100040001e0501c10080b00d01c90480f1403500090400300164144050301070f5881d105058001e202d941840da800070740c0d0b603181d0040703e1b090202d00d04032803031204940b41081404400c407803034800c56030000d1445240b0040c00907200340c1c180101d4002d06240c152103075412250b40d01e03c0074000350701e12a18200e800000c40801000005101076805042e10002500c0002c064042c042d110504202405c0010f2081d9501c0c0410f4511b0b4550140c00ca03402c400003442e141d0720b806110b0b07002d4981e04101280c03004102c56a10300840c42082c43c9031040013860440c008214007400266441c101c08813060100b0b00c124030307051002c14608204000170301746141e80c0303503110f640980c0660401e100542040f000f404d0905c0e0002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 667923255 1250 667922005 667922023
    0xa060206040b1012080a020a080a02031803060c1c02091804050f07081e07051e120304060503010e0405031207050c010c02031606050c0d142403060103081e0301090e 72
    0xd58800b454071301007076215448501e031405481c80760b0000f40600298020040785032030030307070006c98240c1303400018601a459820595900d281411101c022031214130b400300c0c00910421030380c001182030100c4074090440c03405902001c3c070480c0e41e08000035040760340c1f0301403100980300ca05d965034100340c905843c01d40e003003030884200d4500c564410039051040c10004104040070a01141350540981c41c0006918034141c0b45501c996081100089440d9408000e0209907a0040051307800c0060100824440c0791307288218410400064814001408803244607044260054000d10480307040040c0c0545211480700d060b502031022400c0052004030381d40c0300307004461804ca5640041d41c144681e00c01d20383c11041500900070500c81d52035000441185010040d036403130302492803042011b250113012040c1c101d81c00b5034260880d5104882c1409440c07513684890207080002502404d180e0b4a950f030f40021320b41260310703a908212035000d404201c1c0e12500b4040d41c000c2c00094030211f2000d108030f0449081503800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 667924505 1250 667923255 667923271
    0x341103030a020a06320a0507050307080a0c090b0d0905010b03070803091021020a08010b0a120c090b0c151e04030e0f090109020d0e16030308150a060206040b 69
    0xa001d018112500400c40400007a0081800705808084480c440f240b00c0a03074404628078041c035030440308052440720b030051040d14003580800440c0c0f82c2c0601900c6501040312a40c00250810b00055a0742e400c0d50007015041d1490300385041c450362240030b182c100b40c00031001d511801d50f45a01d43c000b40142405109020282a07003d0205c460401d1420f50b220700c2041c920324020250041441c242d02c0c810124040740c100515445802c03c80700710000c5005e1350060400c0000520711340004030f40209010200e503410f40007602e1b8120030034400455403018080812031207051180300080003900103c800018400700028074043d02d01c955800040d024109000303041886075401c41c400401c03c80c2060a2001e0300a509802e004600a2681c0b0000c0c2e0008414602c4a0b0040c2d0007000000b0cd42c903554001d00605d4000f504244103103001d1074002555a01d501d00c001400d031130401810400300340600da049070000412150702c070b8280c642c0000310f810060607074031401c010f034000401c000501028035581c680101d21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 667925755 1250 667924505 667924507
    0xd1b031406070f0905060f0318060c031f0e0a092f010311040303050301210f0303050708130203071a090406030b06031603021302160501150f1a030c34110303 69
    0x41401180301b501600042204800b40000403510100b1070f8036403034920200d4503085400c54544a409640c0c6030700181e0304400700b02800385203c01c0016003a104882079510794401c1990320f55072030840401400c80b90300c040c4c1e52100604180816912240368200031503400c00c20986201e694013000404880c40d2004401540c0401d00062000a511104903811240c1980d045080959800300103c0c6003511800000c041d5408980342c1c000b0590582c0006206400588520540759a0b410004461000e1445c00a50641154009001c01c011a11440700c0d107d03003e09166040c00901c8010604556407034005840540c446010000300380340411002005c040d2191074000c00310300e10750100d020300901100c40521140c010511066860340b10a44046250b0014024400310901c518800a0003010380641c40440a010202141c5100b0a91103d0246030340d140350580b0395602c890940300700c1e8010040b4141101d41d07800c1203402c90084c60300c10850042c040401c43c0103034000c41c034140c0071016070202c4160003030700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 667927005 1250 667925755 667925759
    0x16050a06030b0a0b0c030d05130c12020102060402060a0e0d0602030109060f140d080d0f0f0b010f0207050f030a0c0f0503061b031b0f0703110d0e0d1b031406070f09 72
    0x5a9003d0003045425884046454103080440941540510031203034000078980b600700800c022800d040499520301590540404a455400c0d45c0c01a80051501a01503880000450018100800108000011407420075903618066001070f02c0c0c500285803e8500540120060000a480f0301c645801400f2202c0c070150414171b010070b0100421184a481c40c030644001d40c484007841140011610305119044041040301c1b22803e5400041041650000d1a24500720180499500840340207054004030f4005101c02843d210030400d80c0392251080303d80501405030f501c1c001410303407404003001d4401c0400700c0381c00703034149800d041c03070010000c0c01c0c1c520a19a5444221917008400704a98204c2c203000582d80b40e01503403c0c9204524860300081c03070117001d400a015414954010b0b201342c600d2070494142d590749007440004403a4205092030840c0d001c908001c1e00d10006000c414940d5809035204900e030003840e540c0e1a40f031500c07071101c43c16500c0c942005080201881c2e001e070507400161194288000e40034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 667928255 1250 667927005 667927009
    0x10e06100906060c030302131703070c09060513020d0b030d020d02240f060f03030c07061404050315040f02061603020f0d0207060c050102090a090914031204080313020316050a06030b 80
    0x5801028060540c00200f4540410025040d00050000c070700c50a411240f0108400e42d4ae58040e03001607c0ba800c8030440400c0a1a150003003008440c40103000c2c02d00506440c090340001c0d07000e1080b06420680c0d0300301c1c2c00c8113514180188282130407180c025102c05400c9102c06810720744420105a0f800055543c0e2000341c0c10f00340c00460b0040d010318606106c030ba0718600411061080c2c019655411f10000c14000e1043d2070024201003034500703541d80c010021751400d0007440e07240218000d6640c140c00081241900c1c07100019440e07440360142881c0c100380301854003c124940d103e0107400320440c0f00c0c030031600240b540420945071901303e480010508549010b500035140c10003401072800b000b034503640316414002c00750192000524010710940009030b80d10000401445c8421045440080c0010004c4045030003000340e44d48460842c1400e0555134a03030313039203140c00da10003000741d89200103500d00c074805070f2020012040711821a40090002c24104020802080419400001003605001d0100625 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 667929505 1250 667928255 667928267
    0xe070e090a0518072301110c09090a0611030615160b0705071704090c1403041e060f0b1c0c1401110313060906030203040210140408010e0610090606 65
    0x140141c000800d40c48402c19030441d000050000c012901c221000820070880040d6001c50050494060079217803c820001500c881c005400400d01d240c208003d90001810b08203a00c2c0d0340100c00205541d1000032554503a0212044041208aa502c0c0801002000c0c10410924160b208070041c1c0035041c610140441001d84620440090544002d2030204d4900e902510581302081e500c0503d101c01c07032075242ca00c1d40c0c10b60454401c100c02c1d02d0800d007481070158052544400c4c200300c4076030880d05d10b035102d131100d142e80c1035000c0001c005220120301e07100101c1e100d8465160590020070000c00c00d40f020004000f8010610b0101409101702c000a4400158070880c444088801440940c204002140010384000c401600740070f04501000407890680c3c2800d84064040d20f8040c0c65100c0b0917610b44004034100d01003120b00039003108680018552081c0540464228840d070341191500d03007620b0381046070a5071002d250f548500d502241c18041c030783e0940d20954000d842c041c1e5042000c01d04d804802020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 667930755 1250 667929505 667929511
    0x80c03041d221b0902160b060108070914031911040507050301050d061a121e01090b0a181416051009030201050a050d050103080912070503070b09040615090e070e09 72
    0x60411094020350089001020020041c82506130440d12214400c4801820a071164000c86925042c400007841541c018049240a290140e072041021801e1001051001c1500030170300303905204081d41154050a450b584003143c5200304081095136031000c0034482034403405881841808010700062140e0b845141e43d80c000c1b541c00071000f00395100003441d035443d4400c5081c009900039860b01c13280740c04414001600350700c00b080008180c01c55108501241d01703c0e00f450400600042e0800d005c2031007002143c0200241e4100000c6580300055203644210540e188518145200d03041480b1025903070003840010001000f06071018003c5c036a509400078103038442808002d0510001040408040344600c0680b529a80140d50411444d40c5a003042001c64121840a41c1301c3c2c00c1ea90729090030b1501c0031400c1021160301030010b0038110b0070941161860b42107400d4080e00640c0d1503000183c4940c0c2182000d440002a445040b2850300300318646030310480003403d036018032100307180c001182c1d1200221564 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 667932005 1250 667930755 667930763
    0xc04020a03090b04050a0309080c060306091e100f060201020702030a06200c010204090c030902011709011103150a17060406020f0c1c030f0b0a0b0304080c03041d22 72
    0xa5511164032040e4010514844007030800030700c0c0710820041200018081c98068001c0c2c40b00c1804580ea004550360721031032007001980040f414030114070f45042c48500a90030070760019083c0324458607805501d10b41c100807100302d4010341d00c000080042c07046580b0100090031080c4002e5251100fa600466035414418000a0080d40e80b50300341e000314142911200b40901040701841e40d2500781c9140a4042c0d0818012801b08070325214080c101c580c028850b04c043d00341e042e11405000032003402c0c0310544480060504029549402003c0005136901000b58030a03180420740b41e1407481c8a105106040d16581c001491005407103007002000b010005085500aa1141002d82c2e01e03042c0c070403403c1c800d0251400300ca40a00c02c6084901c03a05007007030048260101d00355000c0005010300c0070508107403405c1210036604880300d4403003030000c045554001c0d60300a01400b05145491486191186568040e620144544441c1c0104c0c829a2109040c0c041e0480c2810f4038550891020b144203403401c1c005218020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 667933255 1250 667932005 667932007
    0x1203070b01181805010c02010c09080604020f120124090e071401050904020a0c110a0b0703110c0d15050c1e212e0b03040b07110718150501020c0402 65
    0x440d54249400c41103d2294095003420100b41518003c1e019040c944402c0001d9400c0210422006100b4400b8500b180d00e10801404151a0f54003030203084180c3c1078005070002d03040c0b00307840d00c8103009006003030034034040c189242c00b040e07030041c204040c0250a4006040385805c20310000d20b07560001904509480040700856001400800144c3c2d4921400d103956810500215243c2007003a00309510080e01805091085029401c9000304040c0c000d030380c0103414440d40140b00200100e842080b030708a004401e40201d5450262100010340307900610b81c0c0c203e592681a44000344143c1081c021142c100a00c000f140381403280400040601d4100401c0b214a904000701d901c8041d82a140032030a842000401000c61070308010444905c21056200b040350300c209000c003d0061215551003007030884a0040e00a4210f44442e61500b1030310748081c1182d82000003158441c3e0346a4030034881c00005000e030300203000181800c0741c1100180c0d030002860f0710b803041304843c04021a07600800c0303140749090111001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 667934505 1250 667933255 667933289
    0x308070507020d0311010c0f02030f13030b15130203060d1103010f05100609050d0203070902071a090115090c090504020d0e0f010f06151434021203070b01 68
    0x200c849000d800800303036000b002da40710141456006503503041c16032600c10081c418091090410380c5c4101009010900584c020020030030a856250041c00342188a045001107165407521070003058032003904c0c01ea401d040d8200e0300c1d240500c0d00140b088409001e04c001035085141400000e07403a0781d800603001d0712507100c408030002e141d5003c0d800030855083d1300404120a042240f0084400100340c02a040415141c85004c0b40320702e0f00d05a03010304154000c0003020342c0e504143d0400081d4201d0442120420382e000081c03c43c80400880040c400c204450001881030f02010140710086600d5201c3d00306246014030a001040e807004488003502c50590740565507003000c0e00041d0040913880782850150158041c1e490302e20106410815120301503501c00e000e61350f10b0b0b10348032400d40d81c0c0c40340c0b20021410203180b10b0340303500089014210700c441c2c0c0e2503602d03820079a840280201000b6190070710700c0c82d4407200612085180804001c0320642c9560025401d0038602d540f2600c0c000c86c18000c07410030b484480c1c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 667935755 1250 667934505 667934507
    0x903030f0c030c0e0a3c0303020d1b0506060d020f180a0501171e0c09010b070b07050c0a031209021503070f020613141e071409090307030807 62
    0xc0d03690903102203001c0080a04000e401030003003a8403940400060007480d070406a614000c1c40030030654940c600040a04403100e008000e0070005013001100380740f01d0240d14400b03c000d03001c41d0b40c01180a42c001d0030b2081c940701070041404015803030619440290021540101d400000c400d54041d80c10faa139400c062071a40009225031150081e01940040c0c3c5100c1c01140c0d0000250780c1b4096482e8900500c00c40c1d0b2542020b08110501c0251000103034401307801040c03681b840240c0784040c1000c000580d4008007503240480c4045800f6000628070110014001c8200102c090040c1e41c403051502c0c01a00300146c0003d590307162404040b0160030800d885c0f5030421404d00c241e00242e02c00d0f03030007820741800f0a9105002001d68204a0b01c2d28003040c800140400002d0020604504c50750503c11424001c080580e01c101484070110410703502882400380c01110464860a604645a031101c005c3c1003140c90b1268000c54282034030082400780b0414014428100c90010654400030b03894204040c095030f038114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 667937005 1250 667935755 667935761
    0x6080601050912060723030f130c1e032303040b0c120d1b1e0507080d090804081b061608070b040b07110d210603170a02071d0a090303 59
    0x1c0700043c003d00043c841c04940103480071b0351199800107426240301450041840c00e000031540708944060440c0041c03208102043e464a00500c54100380c1a1252540048403001070104175620841d80d03500b901344240051a00600e49641c441000311620480002c1265201c0c001d9200d01c8440c01c3c0c000c0380201d05001c00784060788484941030006a1500401110755001c0d242645100c1c0c0510001c0c507039801000d11604084000484041842044008499003288c480d4403c880036280c421013484290148a078070300927200b855000b8840c13562280d040042060030200d1076050424108589070141c1c0503a160801a28441c3d60030092010098040382031000d80340c0700d8280020142080c050801c400c0051321481c440c02000b80766110802c0d84e0726003030465a0b5015540d1000080381e00f1001140303c80000e40d0a9211400c400c40700400c03440d94035a1000c1e0750711075012001060b0a03011800c0c6a805504000d00c0303000f000c0c5c042c140070f4a503501c040860078401c0044d18044903036071102006014540a50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 667938255 1250 667937005 667937029
    0x32b020114090c09091603030804030c0b0f0106031d07090b0102070503030403150f0b010c2312030a0513170304050a0b04051b090601051b070305030c25060806010509 73
    0x34401d02d40340c1002600c80614444851268010340c01040b50400000b4055030040700b070255000c40d090842c0c60568555200500850800c800074160340c0002d000084414050401410180119418948054180d400d583c000d40c0b0400003e000a0710350500005100b0100c40480e84005540d05c00e07100100d040141940050342c0521001400004101e03403005d40a20551002c0020020402071170125800d072401000c40e503000810440a00740421448541458070b10294001031503101c0391354a01d181098031680c01910a0314000c401c1041241d418003480358849090740002d50b04969a54039110f024600700d000203d5950048000303004c1210410a01c20150b404c0b401c54505803600b86091544c80c0018003ca2101c0912000042c100f410101100b03405600d05842d018204518612040b2440001c4502e0000610030300c000040459800e1000b0000e010554000e030a90000a01810780d1240300e0310607020017008855010842140c0c0031144a800600c24a00b03036503565550000100303201002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 667939505 1250 667938255 667938281
    0xb07050a14030703120204121e0b0903090f090f07080a0605030318100c17090609040e0d09120201120b01020307170c0c060403260c030a09050906032b0201 68
    0x9401d5000c0050000060606107200c3e07a41c2c0c52040104440b004264000c40c800c10103640318201e03408000410a0030380f13400144884200355840045910703180e50603442900c070246a43c00018044d0440e040c4a5641c242120041d079207039801e030030614a21451424014800810821041f000c59900d203074a07008200244030043c2283c0e2a001d400200d4110348540103202c5214011280700d41442500550b110801079410141d5250702030108060680103074000303098581d10040402c40ca08003540e45100d1003c0620980000780744802540710f000d0301500140d0031440100c0d02443c11107006030b03408007c92400300840040130502020110060b4514082d14100070302d0b086403002031018046802001e0310301070040c0390031200031b0701d80d00091000a12950001410090388089100000c14809e070f9000f8507161130020712860071728001112815600b2083c070100005201d81020090381c5404083d00d0b400107800c80181841a0780e400305e240304080e68040300690180301641c4109824000c3d80034201c94812 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 667940755 1250 667939505 667939523
    0x240d0e0a0f0302160e2e08060109060306050603151f0308030901091b060c0b100e0c12150603150f0409032304030818040204090903020d140309070b07050a 68
    0x1070740ba019440b41c19140100034900001c0310001813440b0501807541c040c41d17143c0c008181441c14080355000c482003150003021446044080010f16000c108000742c020b00f81c801f00091614150314200040d180302500b0b00e8860761000c0780c0005800f100900301d81e0001641155030055180849106440e00d2160340060700741c040200800c0040030064000e02075861040b00e80e4180340203060054101664503006880c0003984818400c3d0002e1030507003d041e0070084010310303006602d95441324118211011552a00c068001080d0b60789100d0b02c40301081e41040c1001c4c21007095104131400b003006400010a64155a021010b04008a4991949107210344d02c00ac1c2050050410b58180907003203028000403420440d5414035851036042c020310542e0250b03a400f80c0c5070780c680004101250b480c205000401c2c0d034001d03030130000010300e4540d912605407a240b0175000340c0003000d003140d0060004894200c182070031000400800c00c02200c0850004107607811114000e4482c405414030754600404c075540103190f140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 667942005 1250 667940755 667940783
    0x507240b040906020c07291b030403050d020c03060c030412091e06021905070303080702011b0806032509022a06010e070c05100506030c040f0605240d0e0a 68
    0x41d90760014894145d141044a1480d95500079819400c6a02050420256000d1f442d041248101c040201174920b60681503000c0510103031106811640b00e40e204561541c007014001c1220b0f601030100c6614000128040c14044c50202501115844000e00c02440c0e13081c003e803500320203801503413014040c001100f00f0344e00d405a240c0c4160b55440141c0111805032203043c454418490b00e038074100c40700650141c003600c8103516640e03003910300190107080b40b4250354036041d40e407283d80d203424580700200400d80d03158507050034100c0500d81047e440c1d1146c030921702c10500d003030500b240c98031203150f0803181008001661640581c0c642d100404401d007081510107401410010641c000085142c141c075850f100600302c50316284415110000c05003002441d9400c0064090303840c11169100941c801005400e035202c07100404001401c8807070341254440d500d0355545050000d410a20718600348502902005260010306e20b5030185180141072040c05829290f006210314507600b8800c80b00103d60103410b90365016 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 667943255 1250 667942005 667942013
    0x12010e070e010504063f050a0b10120512090a050909030309010605010c051c36050301020406080f180f01142512110d1b0507240b0409 59
    0x3901c00e104840c070032410030348041980d4903000201c83d0310010285562000c60066058201406a124850080880f0b010703103103004113005000180030716200b100301c40150f203000c07803083c40c50420035003200440317a00ca402c4090001d80c0000704070418400c0303030140a40b90000c0c0c41c0000c0306014030381c1116402258035400c1c40031640000020311b0103030081000905c2019101c4004641c11449500094125480f0303140748c0d4030a045110600d00280b0103032404540c40300d40c2254089601e102480c070080d105000808115030381c0d1018004502a040480c000e40c60f180c41c003100140b480c040584a4034000001c00c0c0420482c5403100314405140301041c00340c070b041d9540d11b082c250091403000c005030340380c034034040010308014956203840c40110308212181014007501d9800321a0402c039150300030301090b514440303181054140000b03404c803032011440c0030404022110a040040f9600c00482003405018016880024003040403440f150241c1c800302108014103420a201405811403d183c03c43d01d010b50082c240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 667944505 1250 667943255 667943279
    0xf040b0c010e0606012705100f030c02031e090a03020d0c0905070c15020705010b0a15091203170a060b070803060f03060601120e030720240912010e07 66
    0x1465031802008141d00303694903151504011a0403034001508489280c40e030451141455155882c1901c451007030070703112400b0070b00610303504c0c80590100b402c1c1008035050a0b814021036a00385120f1000c0c6040c80d0340d2094000310100d4140040721261000701d503040003a21110756402c000d68000f841420317080daaa007840812440503004d00c2900c1c0b4201400107000900840004404030340c040320fa100040070282d2100001d4010100171107840d5250418881c0b25501c04190002401e00036002914503007100801801c65a0305030302c4540145d403954802c0780800d400955015007a81c011340c8540761030740c076000c8900082c0103d0f000056110000b08200c424450540301441c0300b084280d45c90104080044101541c4543c100c882c240000c10890030f004000100e600991602403100341140d0409030f959032103480780d00c80c07121507180d40380d03c1c0c1c038600742946050303140424030a020300c0310700e184840054190030242c4551940140546551549218150005d60002c43c0c4032000005540ca81c6895600c03a50b46 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 667945755 1250 667944505 667944517
    0x40905010f0602070b04120510151d0c040509070507050609031306030209091605040329060612010620011802010f050a050403061104050a0605030402031501050319080f040b 76
    0x854101c08081401c07400010044190303420320f52aa41054070740300781c007070004640c214112205c0c0030380d4820450041d0070740160340300d18101034035030342d0f045040400c001305e412180d40b006841c03440070314284480842c803403080f903040d20810340b4403403140d903103981040c0c8503032068000040c45c501c00c0104024030b1407004006441640c61044000b080d8543d40c0400b18142d000f0f802d800f41c1c2c001091800314070a01c24505003042885802d081c01410b150340d9444a0003403029000c9048840e007070308503165006082c01c00c0507551003c0c0441d40c0c1414061030040140030a03505015070400e2144890b054881b11070481d00040701405804005d121000d07005200188078089150100d0102d558550780e030301c0541c024019182c420005d070381d540f41040c1c91a00e40d00c0207003840d40408800c480d020000070445403603080720b0002422498856668900342807041c545411003260562071080c0a40d00140019540030481c20a41c102000382112403a21500304070304036205a03040c40680e0000040c00054201881e07020b440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 667947005 1250 667945755 667945769
    0x8030c0703050c0d150507031104080309031e0303040803040201181205060a02030144071701060501050406051c05280e0316170304211e0c02040b0604090501 69
    0x7029403080501030078200c0b04070000e05032055405000d0300d00342e9543c01b150b0302803054500403030090b9480c890079505500c2030b040750543c0d40000418042c907080411810302400311114035080d9240e10005e1203030302c0b8007001d04024416680080440e065a200c0c1d900140031710300900c41c4285013036451040741c2840b441e6200448060250100040d0a826a482070f24101c1b180a01d00824004003850303081021154850a114542c032590074541d800302070308858000000ea074030010321030740341000710034201e400c403440807400603a0400409020b1668440c0a0310704480c040d05209880d81c0401140441103180b080c10310408031310b8601008010580f402c1c101c900d56044081c1d000c038012540d07016409540b10401c602815a1013082143c0011104485214140f800b0342a05002001c000d9004002d070384c01640c0c01d03580426071119118800100c4500e0012480b05810306e850000c40540c0340c19000c48804c25420103101101d030040b03041d501c407a00821910b4100601d041c1c1d48070f440e1000c0c0b000402003809890303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 667948255 1250 667947005 667947013
    0x9020901110c1c02060c0f070509090c0109060c060e01141501080103330f09110301050f0601051e0d0e07120b0402213a050316030608030c070305 64
    0xa04400d10104403403442c448007922070081c80e50f048543d100c109020100403030b0000c07400c02030102c041d070060120000c80038a100252101c1c61901c800c00c840180060005001074201c448005036680e004210034080324030300c2c20700000301d50290415500030103564098140c90b500f06180d9011102040302e0192140104a90790000c0015030710045480007002d0000400d0641e401c0d08852071010700c03540a02c0002d080390403c81420320200a840140c0c1c072800d2880d82c030030b5183c10340e00040050003179802400c000190000c0005291981045444450123050f441c1884000151441c0e003801044244001c0001038032100e035105c049100c04001840000c044106a009001d130205000b10310300f1100e10300b0354101981141e00c1d10f4a808014503448250300e6001e03800381503034003541c1c550824000c05040c01079104940117012100461164002101002070344155075080440903a29040f0060742d8001038001c0e03981c042200010815001402c0c0b58100e0307140d40c40302003800031603804002a000c060360320800540d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 667949505 1250 667948255 667948277
    0x40905150a0507030e07051201150f03050c060a08060f0406050d080d060b0405030607050d09021f02070f0b072910091a1f0e0a06180b0a1b061509020901 67
    0x7241205c0b40000c10082e01d4001040401c403a1400c1c401c04c81c0e0100802000217084071000c41595030f01c03802a03101d41d00c0480700315810018000c05109150306c4405c1035a0b0705142c9141300700b000306224801800716115441d00503900c9115180e550203040a020f01401d054034144079810050a560003014101c8040340c03c5c160042884290041034604507400070f001020180c0301d121003500caa8000703903620001c6903519421000542d41d02010315401072039421400000f00c1d81c80b01c00038103001840d00131140b02c1848440030000980c1c48000c130b8440a4000c002c85243c4171024500c0c05524003010002850b01144000b44510080010780f4041180c42c0110f08000402580c240c18030081c007015040741d4080b0040d80e81400c0403070815110960104035181a49010254600003498503110746c101e500040d8038145074182441c66500104081c1210851050070301d240c0040040000420306902c03820141c5001d1080704004d50390300400d03a42c0708032030201c04084d40c0300c446440080d04996562400a80c030b030707622 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 667950755 1250 667949505 667949507
    0x60d0b010e1f092f070228060c02040b1905010e0604030614180d0f0806120d0e010e010206060303031609152c01120e0a02030109052b020615040905150a0507 69
    0x10403038200d1801c4d0381001490340070484100c00030345541c00041c00c0317a160a5070300c100c81e0705600c0190486480781000b001e100d005000813911801042ca0240418884105803200000e6402048807000d00c0c20000c050380c0c0304081010b13030146510050410b410480340c0c01d10590700084440c454844030300106440c014840103940ea0368a11060307035010034403110500c003001d840340130740c1c0b58444c002400c54415004003141c840d00d01940071903101c0011b0503841e40e555056900c40c60f8203546c40c600344028030140c204036001945230b10001e000721130b04d07030f00400f201c40071103004140f1040200b0719000007007604201550b014043c00040754407603049405040d003100b030314404a40c030b40e40c0352401a0360340c1c03142800301103080f0700030075216950203540d1141071034400c0180c0d000d00409020b00d00c100c02800c0d039616080c80100540f4000d072000d00c10140444840304803242e00181c8a503205074544001840c20102c000810001e180b284030180490040c400d04540c00c540b4400340600444600000700301035503902c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 667952005 1250 667950755 667950821
    0x903100902120d0e040c0e031b091e15011709071a1204171e0403051009030206070f0c0f030c170c0c01080a180f050105060d0b010e1f09 60
    0x1100004a40b030060b500712030303085c03543c41190380000d02e041c240850440900001e1406903a030b6642000d000941800100f142401c50105800003d0085000d102c1c110341d909a04031607100404440b10020f200c411140140e215620765001c407804400000c60509000c80d43e030b512100a401405941d1840e040003a20b0201843e00316107070049881e00710a206d4a503641c0d0494280b0a121000140e0402840100c07100c1c1a411403035407500900c082441d50752855443c11a0030401141504142c0034034207050040800e402180300c0b5030041482c03034442d0301c58800c041c040d01c040301190b40c05401e6807001c07140c25040540140e18203d0440c000c00c4008002130750191055814425000701e00c4168210f6000075603107500606a4a4015101c01800306004100d6032040c03994100c0905c0c162101d52000414400b800740c00c1c071449030404400c1d81c441c503100c840c548800c00c1000061250070b075101000000039030b00752109805810f14007200c181d0030b0714007641c440d080c20140c1110040c0c840400321000760820040b600130 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 667953255 1250 667952005 667952023
    0x606010f0e0907031d01150e040c0b0f0f1b06090a051c02071203020102040e0901060308030424051005031209091501090b070501050f0f041104050606090310090212 72
    0x1e91207000668074401442800a0060041401d060301e030350075100310340c051a42d4a02400c0e0564000500324140800c441b400c0c030b1659120001c8a8200c0081c0000306d00043c20313000503103041d00001980c078400308500d21024890007020800b01403010402141004056100040d04130484088925070b8552801c480e44502108500a050798884003414140d1000410b40201d61b100c1350040e031303407010303038841f200885420b9814040300142d40c001030502085001c109040c4d0480e5400d0020882203080d69203100381440b0252001c1c013020400450041c9400c8403003c3c5405000d40c100c03080c01035051031030015800404034020203100c1d000f508490494075000f1400d50b00e003503e00800000715078464580070f0030005526480e03581040300d12240810014001c0c4c00608019106034000a071519025441d100300400c094003901e10760343d103001401701280c20b0340461101110101c1c2d000807181c0710003000070b0072071080d0b2840c242c05003d854a1408a40c10301d91001d10344c103000b40d0750002c00c0582c040059449860788 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 667954505 1250 667953255 667953257
    0x10e03011401060f0c17040e0106230f07151b0e0f0d0203010e0d050d0c080c0a0f02010b0a090504060605100507061a15180f0f010c06020d0504050a050606010f 70
    0x1407004103c498030555481c1c690103210708000d03c03000c002e0303183c2020307003401c081c5041d00162000a0030440132440c0c0e09014010300061420840042d902003000b14038803241040070841040200d16403d1009050003101e0b20300d54000340310345100300340380a807802500e02d0103004008e074142c5108907641c240c003c00050b0076003107000f400c00800c0c0f084041000440140484141e0f01990703154248210000100009030709020782c3c1d107031540c84d0903091a036007095a40080c903040c10401e040d000d210b0341441e4241070b2414002d03641010558074030400d00807401403009248599009541e5540000c00c904146d03c4503020712f001d080148400360f122000d00083e400510390980004004000c80c4001c203504c0c0d4404031240070781007602c8098030401d50025581404c0c0d044d109a8003417001503900c207540e0800ca0303151480341060f600d000b08003614000142450f400a41035506014206481004000e455811141c94405140f010085400c050415a0380e03910506030840c0e9610408001c5111036001d400041c42070515 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 667955755 1250 667954505 667954541
    0x30b0301021c05090c090705070507050d02011b05010b1c031701120f0f0206070c140d2f0312030f0a05010e0711150115121a0613030c1202010e0301 65
    0x141e0101c0c0b0b0018840203141c1c500b64041c000c400f950320741d070705400315010307c01c5642c400b626650310341416414013007264442413281c002c000c0e1440050b6044041c5141030000e550800030850541e00b805800340c5075a0070919071043e10700d000e0104103030f08601350b1a0b41a00a03914030310190764009125a02c14000e0040c50381c00403a40c030603803002130464102c0e1500e883c8034036000c000c0c5103202c1d404240107402402c0100d9031480307441410700a4441d00080b000c01048116a450250207903503c482c031307001c1035004068900080400c410741c5040650101e2010780200601244d41d016202031240e01242c00640300c0514280c444408200300400d41d001d414180c0d1000325052585840d1342c0c07025a212281c43c403540d415405041ca506d0751070300400040f60300a140c0c40180c10002000d203500107101c02280407500801600d020224156004284c4c250b00101009403800b9684040060701e103007603020190301c010725824130700708007042d1740e500d109031000100d1003038a84a120324003000c1054240c610001440001e02c40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 667957005 1250 667955755 667955797
    0x70f05120a090507080604030816051606020c071a04030b0c0f04060f030f0203090106080c010f0c2003031b071202062d070f021005040503062e060f030b030102 70
    0x155648541c291a00c203008a13415199503030700081c2405400c91381900885c0c0365004101850005030115100001149011840c00e8101c2c0a0700041c0113041c0c0014000d0b80e80452032281201c000c00a24018001051603009445800105c50309140d0241c0000c541c48000b91002c00d500404040030b459501905002460400341040011698070310900020000c00da11000c20b524542800c0c40214080c3c80010000f1440d103060a800c1450040c508500604118074201000801503101403000c051581c800d1421982600c005100240758103402041980740c00006031407402441c036108e64034800703420002590001a0713101c1517910041c05018010350000c004010100300010010071519600c2c034607500030f4030254100486003915030080b0000720740440c000781c1c4500c29443e00c8004d01422031098540340c0d01d05801c14000c80d444840c00352a64042d090280800c0002c000d0741ca092965011408004081981c0d44620040200f8840030160f404070303113010301d8445182010300895101c00008018131005c18 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 667958255 1250 667957005 667957021
    0x16020d050a051c0c03090501111303020402130e0f040507120c1e031b0302030106050604081c030b03030703080106080a0c050f0d200306090c2107030b0a0608070f0512 73
    0x10b0f101543c00c1e8203090b080c50301c00c3c0c0305000ca842403030424002942e0004410381c091901d142101e241c440c20303034440d8106020007181d0446a494440070f403a4151009616107024041c86c01309400d40344c020400c02554a1300b00140c040c0d00043e00d51059028100715000d666491040e180b2071600e1100190540c070040e2414400c098400a801c411120b2a040c8044210350743d81750300783c201e034010041800d0204c80b01000c106620302400340c4400341804585ca5481c0c9841c02900c3c60707580056803038452500b24041440300d01a4005e51120f90400c0d405000d5030782d0307048030b403600801500e024040d0320080ba65490104d003445105202d80d982550303031510340e83e00d01003054900110542020302156410b42e06e41d01c849203035004209018061401c03c805090312401c0040400010140061000e21244014803003e0390b081903020380c42c0110500d4401280c502c0d218880c00318040c041240c115604a02070490001d000355100d0ba20a00c981c40319540c00d484e617046000103d96078401c0741e061040400607803010507069 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 667959505 1250 667958255 667958257
    0x11070812070801051c11120f0f1b0405040312060b0703080112030e01031a03030c030405012012090d0605070806010305060a05091f03150603020f040e060403300516020d050a05 77
    0x190080e82e0f003070399005a01c0001f1344d40700c0d60021211044e81002102d01d65400c000c00814022a81000c081c00c401d2000080000e0b003120800122485151502d021800303060140f101040c4544400c041032040315107030700750380102c4e41c40b0041c21400219580c3c00000e490f43c0f800d08641c03149030302d030b0b40d100752401c8a24011000303440030000c0c502151040442680c0300f070381d00b0001040c0c501c0140c4042c58aa914100c000341c001d59201a040d03a111444c40d0040c0c580c604045526030b0002901e0140d1616030301c082000c00c01c600307000500188001d241c001440b813840d8109000e60721402d000da0301405240d46a0090141c000680d00c2100d03000300d51140800e40108003010703400b140c1e2001e600032380c0d24681d42c0d4132074040d403107110403501c0c650640d100f00600541c2801da0703000344044401e541c1031001d8a041084180e880760000d00182c1044a18200c40b10f0b101ca0f0119045d0000b4002111038031103004601210005041c00d4500048070307950030444e9041d240c00814460010005ca0b1291401c0018a03103050304c00e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 667960755 1250 667959505 667959559
    0x60d0f0609020f030a050714120715020118030519140708070602070506100f090203010e070c0203070e0c0d0510030804120c1517090c10050d1107081207080105 70
    0x3001c544004203c4080e01d0030000c8605aa0089006040c0700380741070547c008140c035490030140956115030340a00f81c040d0025a0500700d4410b0001c8258881d040c4100728010140304808c280f2441c000c801103428560b101c0090182c0c0503585415100020365001c055414100c507140e0118a41030a206020105900760080c1403060300803040503203041d15654907581132100483d110052500c2c454000d001707410b0207804580140901400452171541846500018540000c02030700030040813103508000c41d28107002640080c504036540400c542484440c004c1d01d03070403258074810810302e00340009070441aa09018030480c2d0f0007404852a06041003000220340c6103540095502140030080081c1d952103604041c00d0360703c1160f9802100c15500e9207005084400034002e650290700c05415451640e442c0c0d000380e649403885050066861104840300806080468485200488086100c0041c0105070008020503900c80307550141c90364494200f03503940c06080c000c080c0c018005044509a500c104e00710440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 667962005 1250 667960755 667960759
    0x130f0e010905160f03180204060308030405060708190908130605040602212203050a0303062c0115020a23011407120f0902040c1206090b151e0a050c06060d0f060902 72
    0x51b0580c03150041016903446500803101c0c558004104014004140000c90300040d107840c020710107052204d01600804005d18100c858603965052a008019000007100c10541c2c03241c1e4000400c0780d96210140c81a0460300c03d100250103103c0c50200100d25010601180c3c1050005c01d45c142000425a1900e00034410510000c54a082c2008400304004002074940240300303aa0200740c031401c10015040c050701590000b0b0054941229560410002800c17070745c10b6600c8401502e0042e400e00380c080f03291140c890409000f000d4030b81c040024080e6407000d0040c2d0045482c00900400400100000035010101c908100180c000082084003981a8202043d107a03d03004001c04c0c000b05d20740028040ba03c040721040701140da05000101089000e018420040c14410000c1017420516000f06000004070301d849070310203000103200c0c91500500000304000c00d003002c400307540fa0a8210301c05030055128038214686c9104910000c0c1c29440c05800380b0202c240d00400c1d000451445982c1d580c050b0a04d103400300c1e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 667963255 1250 667962005 667962041
    0x60c030915060315050906070c08090a060e21030d020c03070b0c030403110706020a0f05011404050304172a040b04020a1713030e0105130f0e010905160f03 68
    0x2010981ca203002108070030145000140003850340c5854803040082074081c2c5070090600081086a42000c1001c2c0d40c0311215042c5002042e03e40c2c03519070030354451240c100c1c0e404000100041a25940031001ca01040c0c401c2e904200c0c0c43c080302c50441154035442c821540a0743c42040207228005080d00501680d502036003c9a0a000b010751f81e5106096003141d12000044000c0f0820013403540c498154a941d841e66000351810b10f042c600c00a44030440d40c6c4014240107000101c01040040c02d51000d20900d07501a860003442c00c00e841c0c01505c0b03034840e11814084030210180c1d8807100c1c60200b01400141440540c1010b007160822420030500c1c04901d00c540e00c29522007400c1c1c071546507400181515000e0307a441d4a5003948108600d00043d07000340591401260510416001a4000c3c02412140d4000d0030240d03120041c000c00b42002c14416008034024541c40074001501042103c4114160740c41c0d46000c2c82186ea44114198060824410583c00034501c2d00b80d88204034000c1c6c0c811300090203003443e40b03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 667964505 1250 667963255 667963271
    0xc040f14040f0c080703030f080a09020a15090306020304030908150105030c13150e0718080c0906030a2009070206130212010f06080a0c0b0a05030a05061305130507080309060304060c03 81
    0x11901740041d6034401c2d03001c02c02c0c0114091049900001d01d50f802095607604201481d403a40102d55102d0482c0a00703914080c554400340300160080703402000955120b44103644c1c80c070746840c00a116100740d10502e03d09224803c2c894107141c0c1e00110707950503104054024100e0702b5180080000750a84c00b109024425911a0040702c040c0d501c02400b40034000800da58046400c00817402080e0b910900010b0a108440700310a0020300c10104e511000024129441c0c40b907500c40e240060300b008074104004042649071856030000b28042c0200882c0924112050809550348003010b9031511070803117a9282103052030310340d48010b1a10551150426010500000380c4903040940d0908407a02500001034a03480000000d0400403d209009c019109001d003103410291910700281c400e02015240c5051582c0300d000040c12a05c810700109042c00c04001c040c852410510040152a084005c095445018030f4501054210002086034004070010f0501859582d840c0c0b00c2c0d40042c5201d0505900301070b00c5440e8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 667965755 1250 667964505 667964519
    0x4140607110d0b1008120d1d0d0306050f1008360601030209090106060915030f0204031103070501080919050a0b01060504080606010315091503080c0c040f14040f0c 72
    0xd10440b41c45190448801d0403c1d81001007203810662103d025036000b50740e504e01c49445d00c0c05441c0103401d8510b000c550f400070100806111403140c420142c540c0301d202c0c011000503074540c002204455050ba030035030010441c0d5041c00034840e00110b03c54049180f160100b800d01e14201030b002101c0004c480d02c0c1c0c202080c07a01145111518140308203680d50302080c0103100390704e080d484154000074110020000c052400902070300d021070030321520072070040c0c141c020884507019400c20b1003044d814580440d629034a0746002d900144180300702c80d0081c410311402144035402050342302e004402e480c005110021001810003800000d0702022981c034003608150304000749005000c00d010384582d846898546081c6407100f0701e001c1b0018240d42c105401c0c00c5509a80c082d50403141015561600400715810000724210724180c1259400288180400203515100b8a03002c284c41c12040390495041c031142d100c103445041901d01c10b91801e41060411004140001c3c60502204a0b651040405952040d41c80700c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 667967005 1250 667965755 667965769
    0xf0e030d0207180902031504030c06020301090603050f0f190c030804060206061804110603070516060e12040b0d0203091002070b06150703020d0e010203070602070804030b0105060414060711 83
    0x406003001d030b808900248450212041460ba1041c0d030120200061149a000030380c5d03c00107070380003920031110780303010806051142504080c90f41d0800f40640d546c1d6926440701c001014644000d1380d043c080d411000003040d801241c900381c5c450f0a08000e0481c0c00c22071440c83d4802010b100112040c00c03440000000040802014000510003074000c1d00540c40c04000f0322207007501d901c9010000c10845801c00001400714903003003240c160b05450140c0c83c1c0d0749154060702d040c4513405100260070f0503000da0b102009610340191a514400c1c0301a20581801e60000c2c240b83d001d0781c002c001c00c2500a21a001f09900c981d809503511071029022518904950307062103007268040c0c1400e60342c0124090400c466800d01280c0442d903d280510740d940341581a403402522490751340e030707200c04212080340c091419038400c0054407161030700400308640d540c016140440e140c0d446484129400c481440c00050946007101c00e9404036034108408158100782c66080180701c2c2e014202c00c03104201d0721842d0a0103a19416 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 667968255 1250 667967005 667967023
    0xe010504030f060c03060e09192f010f0e03030d020a09051c11090f0a2f0301140102010203060d110d08070f02090a020315040b130507120606090b0403030f0e03 70
    0x2c030004d000d00440300010192507164102c10342d100e5038030040c0010403034001490b5114900b00748504118072682d03e0250300244200000014420840020719949100300d0b02c00c0701d51400980304c1030040b951600c02503500000c10b20416906070010302980d00514820780040c01203464603e0000090368541e000503444030ba06030b4001c00d41138240f080402c01c2100d00c0c00c204010383e5040f2410710051900342c018000c8188c0c018091146c140d00c0740702402503100c1c1c02d03014403071028084003040102e201048181e0943c1d0000d1203014000038030400407070304950040c800c40f40100f102800d600c03440e102c00e481d00100d00821000c019003044103006c150f001301e02740e0009442c0b0b0354403544650b03890580d00c1c010022030031001390210405038410030038000a0b01d02e5000301c00c003001d4181c03408160b80c00302500240644144404021059080008101c0c84680c4882101c03881c0314014000c1045617258181120b040101e07003c0d00e00d00c0c079401c00c002d00120340110701100c6511030600c6e2500b074507001000480e0401c0a0340e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 667969505 1250 667968255 667968263
    0xd14150d14011103070306140a12051608100612050a0219270b032d190b04170901050f0912010e0102032e0b0903031917010509160e010504030f 63
    0x100505c01703043d0745400b51000400c007112201290401000000c1c0d80c90341c29100c0c0c640c5191305248a08100b00d400c0c003400740b4034214000320900440d03903000542c2d1101400c58140c00c000f40f410701c02140340e260342d5441004d455003140060034a0000d0f5402c1c4035080b8204840100c540c00c00040000d90110032055030208903190301a03044034140c42407041000d442c1c0e00c101172803083d0046641200d201028000000d6000d4040340d09582d010218921203003014100d0562000f2807403140788a03c180481e412805026903c1440c04000810700c0207208007032070080741d110303500098081000e20510110342000e00701c0d0500051245a0814100000c507003110b04840b01000c09075004804c100c00d51501400c89a1040701442c0a041100021011200c03c2d50071030048020087d40420701c10020f0302d080040d100401d0803e1060398074034108040180c20f03042010740e6650344200d510004100c0b0b003025003000307006888100b011241c0041400081e503140c06840c5103541009001e001c004003068a0a510707481250103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 667970755 1250 667969505 667969507
    0x3180b011203120c120b06070b040b010e0c1809070e03030c0106080d090b0403060c050f0c0604060f0e030a0e01140403060609060503070302061207050d020706020d14150d140111 78
    0x201c1c5405031103601240c481ca0003e5140408041400382c211000da001c40000503070000c0c112140c040081d04a01442402800c6d03e1261001c2008000b142031581d41a10300c10854600c46554440c1c180e4650310809100640303810f160f0552090074246036000d140c00201904210501041040c04217145400c280c00301c0e0401e81d19094204150340090288100f0850b80380340c0881514100f440c001c5041c4514440240400c1c1c0d43d201c5c20700214825025599050201100d0507541c50054032056520042510152a40d03481e24614646109891080407501c80d4900d002d50b0420ad0301007030642c2d9a030810700d5998140300070684070301030b03003c0c40e00020006184034070800950107041800e00005c4400301d800c124001d5200490031710140c1c0d038501c21b0f55905461a0f8284596036900402203800d07005502c0314045c140d00108082d010084560040c1c480f540c91181d0400c03000c4440b44a140f04001d060302c03104048001243d1048842c03e009204a240900400060308108051102982150141101c010281030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 667972005 1250 667970755 667970789
    0xf07080c01020909063712080a1e0912020103060306020a0c0c0e1b13050604320a061229090907061205151503060a1a090103180b01 58
    0x1030554903440d0002c00c2521603413180302a0f0881191307070701d034561148070085e0410000c83c02c42280315079003800541f401e034071010b00b1942c90b0719002e1019000301c0f60030004a04c00001d03003c6010204400301190300c2c099602d240003c1d18001c0c0d05000540002826410591a107130f002c40412038500040c101c0314443c0d5507199072034119040901204401c1c4d003144601003200c009000d089102001c141c100e40c0340c415502a61040c04400c0168400e41c55445190440000303d40003552018031500701002e00310080c811012100d059100300b604886400e203007030740180027010902010f4454549140315002040c030000d00c04000b03124560800714400c0303000c074540381c0118040300281031008116030881d4500d03008141a5040c01d40c0905880c585c9120344840c150341c5c2002031403208100c00079000352140a400018140b0401c2114401580704880d21801070850f00340000761050304500844501e4070480c012400c000441c4011405450425000080c030780c091404400410b545101083c0202001310b488001c041e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 667973255 1250 667972005 667972009
    0xf060a1b0b0a1406150c1905010c140313080a0309021c030906020d0203030103061a10030509160302011d0a0b030c030712140402010f030609060b03060a0905040302030a050f07080c010209 82
    0x1c0c2c21204140803c2ea6240a218141e05ca140072444401020a80d1580303c904920f4154582030000511960001c8919101001e108065012003041c2c0213666603c4c1c883d0002d00d490103a01d10080c0c4000d00d031200b040c800d000108a0900141c038041038203140204509600350000b0f103807030f0700a10100c00c03c4250b07034003014101600702c0c0c1050300030710040c009002c1d16040004003a40324041480050001030312410540d141600c284900f0030300000c0185030345d07040000000020014a421100b403441e42c8103030103044010b00c218158040807213070f0503520070080d504100c80340404070020302c400ca60026040b02010440040110140d0700c2a41040da07540e859140c41c0310020f000d180f00860403645d440c5082d00c656507002d01031070706039401602800c100646070071103101200245001da0211180d20314042021500136042802036000c0d0f5821034805660340c0d110b5444004840302524024050390081120500781e070b000304080d003641c10055110301c0c24180580c840c0301059001e041440300c1d0340d50005041c2098 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 667974505 1250 667973255 667973261
    0x40c20010218152502060a08100b0f0703030e010204270f090206041710061d0108030f031b040308070c0303120506130f0b0d0821060f060a1b0b0a 64
    0x1000048072a00c0091100820043d8a440360b441046409848100360010481030f000e03112408a038082d00840c0d441089850092882200340c50b00e024030800c4031000078888940760265840590030400c514601004c55809400402070194955000c2d5000d01001401000d224076580d401014801015440320040d0038040442c0d8103251540c0f10b2901c2c102c20400542c44603400c2d2026603001016000b0040f994102191400d4042c0c038048801e2410000041440e040079003c20f05000030008040316166201c0c100741c0d481303000c0c810303102c1c0d0313084001d00001308501500c400c80e40ca242e0064244514080d00d9485030303210b5900549059801c4208000708204141d4021904c030900c4c4a038400030001801c100d00003c40c1d403040c2460050201c0e880310300900e1001419401052104402004400081103d2800120f6a000b49141c404035440075001203449800ca1058540b150b107004042d038420b150843c042210340c1e080b4126160403c6039113451449650402c2c0b440c40d00032030145044401c00e10700312003c0029 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 667975755 1250 667974505 667974547
    0xa022215110a0309050409020409201507050c090c070803010605040510020c01020a0201081504020414101805090417030708010f0f2702070210050903012009040c200102 74
    0x159911a5950b0b00211351301c41c1100007551011100410311040794000107024041c40390340a0800e01480b100078402c3c0700c2c0e060108000c40780650303e41c00a07006004c04901c05004002000e009038100d806081c84034602400f07410342c0288030103017032401d211407a02d8004140c0c209070001004134400040c107002a29065001c5403861240c0d1006149488131040002c4d140e001448000b418460820007050000d10301809040b101000a1700454680342e8504011400030100c4c100c0500944070030500440080c443e00741a0120901a080400c5482c039100a00001c1540100300f51404440c5801060f03d20030310f070004502a40340769842c0d40352035041001e461302c42e0605500038030882c21159000c02c0b42d50801c486015106010040103402024850501e4019101720000250b000f802e00c0d408141d0207801c000500003040d01600200041c040048a20968428186c6030f1003805905001040740d07850a034200d0100c800042c9004070100c404255600c981a0946104041ca0b035004120148070040c6d01400c540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 667977005 1250 667975755 667975787
    0x314030a4e050f070c0308060a05040213500402040e0f010b0421060f0e0604060b0301140c031801060f091505060f071b0b0306040e010e03030a022215 66
    0x10850a001402500d0a00005e0307004003440304c928001031007079907901203100003442c0180065603500380701030080b00e84417186c0c001d0b004242c1d84840640100a0003803c049031480e400b0014903581407180c40e548a01410205031030264408000f01e1300c90300d0b22580003400003412814030754025420a14003600c4043c00582100c003440d5414441045500070300c002c54200031070500300e4080b21100d5800c0074005440c803200340101440c141900c108440d0301c002181c2d486140250410800e00351805d04140c00d981d01400c01049200162020640490304032000799041440c44180100704480d020101c0d0a59082c0d501c200c00a100d1304500700108841d5001d100b03594107100f01810103050501d40014450b0285045020580b031001c200c910030480c80c0040070701c0788500405c141c114a9954441000a0344c81100c3c0031340641e0903c0c141d08401a0140520403850f40300c41c000d0b40c19a620071280400a4001b00e00c40000c40700c904440361410340744400401c0241000c158a0510784a5601c0043c010072100b40b0401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 667978255 1250 667977005 667977031
    0x2090a09020f190504062402010903121a09180d020705030607140c16090b01030203150f04200c06010e0106021527070314030a4e05 58
    0x9005aa070b034070010220020850708151500d0400303040c424038180d160409a0814500080440c000e501d000c03070480020410100034002040d0014100c0c00d807048080700401080081c034610400740001d401104035800d541c40c0e03e1842d10560800240791001c1590180104818405550b2007030308240f1002c000108030780000c1200b1482c000100c3d6488100820682c01c02c00c2c2c803403030008c040d2261011685122107420031248440603540f02510020200c1c03081c805000d183c41c0d80181503500034001d5a20800508a90751a10410392003400080345040d9141ca40c029951003200703138803a00d800c1c08040d044640c0a480c54848040000140c6081c0c41a0480e00306600c00000401840c0e60000b40301484003405c0104076903a40322510201800c1e10b0301c00074030701e03100c440140300310540d00001002c6003100d0141e011028103402d40060f5a40340d20541100b1740001c5c0d14941d00194803510602c001640f020f82c00f031814200c124402c850110038900c80c001490038900d400e00266540311500a250700844010340032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 667979505 1250 667978255 667978271
    0x627060102060c0f090402030a14010305010e100501031208061f08060f0603060d060c05040312211a0d020a320102010501060507021c08030c0a02211b100212010302090a 74
    0x50119400342600b0ba0384507580000020702c070094503410a82d81c016004502c40d01caca5850f0315019011b01310740260169644117005602010030a01d003e880d04883d000125541030711401003085031001c2004180c141c02c114000380c001001702140714200c0480023955034103000c078140318042080e4400b4469a0070302c24003080c020700c159656600c036003086407603000a00050300d81341c0c5002620719000c0da0380040d0141c5903040e00c3d5502c4980103000301048000e02c1a00140311109100700e041120b11260341d14501c01d4121240e4074080c05c1103082c8000103800149203070005a90790903561900a207046c5c110402d41e0300c0006207100801c031046554031070002400284025814500c00030884d01a9582c0a0720079a01e410304034082c000480f403405051a0400d0788155a07181078810f691080d03200c030840d040144282071078040c028240280b120f01c0f54011b00303011880d00e40001c805e44c14411960030301004a000e401c640d80f10000951008002ca11007110b0b10300b030301d98554010007640c4840140078500b02820201c02c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 667980755 1250 667979505 667979527
    0x18051b09060d03140a0e090a0203040302010506042c010e190309062615040e06060a080a0c0603020318030711010908150a0c17090a02040e031608030627060102060c 72
    0x2901109003d0400d6680d143c400d403400c02c03101d4007030018461f5001075540c0d040c41140e901980095110324003940080c03206860f140b050000301c490031900440000c0249100001d80e03412800704504850400c0004203503000b10504040c20140e2500e208984203500f414030a04040d00528040000c018604001600075045c4d100c01508000100140301d064200200160802d80c2000705608140005001000056200460780c3e680390015121948602400c07400090b100b0400581100d043c0d5009021140692601c00142c020750400742503c040100142e00491441c1400c00c003424400f40a114101c0300701860b5000546240140d0700b00e00415044568441d403142c40c05488280c0014100d0400980707440200720803620048915542b440425110301480361004000070086404c5000319410800058417004969991081c982183c000045000110010410140165a000310301401101e1842c200e620036905100140780c43c4403150101ea0184100b07564100711080d440f01700504001e16150395001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 667982005 1250 667980755 667980767
    0x140d051e010810110d0203100e1026030717090a0b270a0b0a050d11070b0403081e040f0302010501050108060a0b03040606170f0d020d0c0618051b09060d03 68
    0x380f100754490311103031601049841c00003214604968a034045459050000c42d9414010796441105041110400822003c5420b1074224086485101c0000340c180c011503512555550080015550703800188a280d01003003010001240300e00a03103081c0e5660f00418400c000042c44c89402c440e50720b000c240110090801d50390401c101500a016440d20481c4001c2d001901d0011503811038005244040382c0001d0494208000d00604004d240c0d090100480c461809a06405101405080c0301584000328020078042c00c000d81d0484000305030000c000048002d00c40030081e09490072110510507000000074541d0a00c00d581c00340c802464041d00900b8800001101040e1038020b4408d0614004040703400c204466100350700500041c203088035924440b44d500360712807020350881e50250068600014040c0c2c804180312001c4501612074100303a421070340755000105201030303d0540da2204452003501103001000f0034a00c0603452460150b0920707007001441000c500c00342506d402403442095040c0000c1d007080c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 667983255 1250 667982005 667982023
    0x6020a14030901082e0f0311030307080304022416030809010902030601181508010219030c0c14010b0409050102040501020d0504151107031a04021804050a080901140d051e0108 77
    0x1e440768842222240700c074000351000c5d442c86084413103070020009070425501e10300e03022280030300040700f400313040d0030240341e201d20032114028080001000000e0040c58181d091103503625400b9903050f2146038043e42034005070303c401e50b43e0014401c0102c04034100340c2e004ca403165201a040009200854166000c2541e0304818000c40d14050300340155030018044d154045008a9a03030745160041c913664030722450003944541c1ca124010300305072080d081010700034007464090300180d680f8154483c000e6141e2419903182030465140070f5480d10020311880c0e560b4020480c246d030080000690383e9141c0800a032500c206491600f042c008140820400c0882e42c105203001d800d01410a208805e0000828904158603500b0040020104d800780007101607515600d540710794800e46041240031810500760520281c200c038000d00360307480344801c1e200042032a03018040020f010304106021905040e494545608100740803c041941d901c100007121904840e482d02c24110202c0d000201d504140540b91205210 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 667984505 1250 667983255 667983271
    0x1b080403140918010509010602030c07060c030318230c010c0b040c0506030c03010906050d02030c13021c0e070e24030309120105090c0303040f0918060606020a1403090108 75
    0x5048075804100024040302c5a2000081c1084100c50001000e4400d00360280200c500600c0000004100d20303000104450400b0307512001004140c3c9041011103003400c0e110380032401c050700d03000070a01d100303401c00142d2005845190078413030a280e0f9500c0d92849500042c2c0c80305071a8410300c2c0190b01c41c5d80100340289038a4101c2d840c01c001d59a54280105600090390100d03402c40c00c0003003080055681e03040514180d5000d51018400d5a40c0c0700c08000008188407006503250300802c901854920b0504180c68000012150150030040e44102416001030b0f18000701c560302c0e441d600210403055040c00113501400f02485a0b140b541404d407103440c40b60803085200e5881e940e00019049260780d01700709568800000900750401804003203203e901170301040d21280322600c038880e8000014a4048152030a4440104640008500d0842c0c1000604107180c40d00c030710302510a43c01c401080c041d00540014140a400810000e4124548507821003107252940071039030030600164242c2d0b81e210041c10341081c1d171 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 667985611 1106 667984505 667984517
    0x507110a050a05010c053405090f0426070812070804051b0d02030727020301080601063c0e0406031511040e01090f1b080403 55
    0x8038018594040002e031030512003075106548180072103000e00e084030500b11440c111107007000c0c000035502e215200310003c840b905410940925004100556071170f4000d1410f18018180c10034090002041c695480021a0040c50020789001c0d440413003255155440e407003441c1560184c2d0110344400515000800055000c81c01071a02034071482c0c11002038034034000b8450030b95004181e010000d41c1d01007181e054400150b1800c100038009044a0a151000700b02401d045014441d20b10442041c0342d401000140044a0041401030443e04542012040008403000c0d40c52030074024200c40355001e4034101251100780550b040740c1c00c10183c079128a00314240190500042e2151400040c0210404010b4000c144041741d0141c540c01141d0420707141844d44a4605400c000402c5c0d005c2c2c41015103428820490401034400c00e10044421103150101510040000c5d10300d220042014080c092 = true := by decide +kernel

theorem cover : BRFrame.Cov 667805755 667985611 := by
  have h0 := BRFrame.cov_init 667805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 667805755 ≤ n) (h2 : n < 667985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
