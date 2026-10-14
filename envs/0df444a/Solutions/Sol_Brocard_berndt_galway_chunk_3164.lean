-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3164
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:51:18.999043+00:00
-- url     : https://prove2.me/submissions/7150869e-ed78-4293-ae64-623c6e102201

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 568884892 ≤ n < 569064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 568886142 1250 568884892 568884913
    0x90a0602030f1e0f22060c080115052104030c020d051f05010803180a09050408030601030506060909010b0c01090203120c0106080303070f120219030b030f030f220f08010e0105011502 80
    0x803281c406071a141d14040719815040001e600341b14421f071380c51490b01c4400d200e40c541244a02c1030340ca135451030414444200f1290701c2003010b28040500180c1c05080c008980c0d1202e060448000e27080200094001c0c11900e10b000c14000002001c090381e00303094030042c00c404110b104107026503000f840340859030307841440720f403403500c1c0380e0300c841554040d0242003800d805681ea06180181c810958050350040d2001080c0a01541c0c1405071551003c13040e5406840c00340a1000f20310100d00506c42c0b0076080101141c42203d841081d00a4018150018100e484240c14216802815031119030942c0e955847d00c5400501c0000c04001d41780324804a407075038043c5109071881a1843c2252003001c0259680c02c1103500396510310001701d000414003565002803c081407109140c40d02c080c1c1c040442a0381d0040c417081040c01aa9000c07904040851314103461000c1e40076013a5100b08210f504006015080400003142e55181540708240300403209000b882941d0740d0301c0c20300c5107140c03515203000c00580200d0040c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 568887392 1250 568886142 568886161
    0x904050c0c0a060203090d1103030f0a0605040e0304151e0503090a150209032b0c14060c0c010605010e010c02040c1101020406110f0105070512090a0602030f1e0f 71
    0x180d500140d141241890320520204890034016111012100b10b83d010040c45940d0800700b0113240d461003142408071011403521402540c80c00001c20f8040014007000028600e500c1d02e1f0484c7d001000701400c103200800207802401d403a504107000301c8112503030b03103c08007134464480e0910414203000d1044161400c1200441280e60350300c0107101292601ca2903a60b0000110070b8000c403c010002080c006880b5001030f0101410402d181e1a0749000da446500c49084148503041407002d80c40850506110711262403505110f5942c100c4201020f03030098408202904540070010140402074600030800d99442d680196660b4401000382070010741d09031003070700050500760b20404900e2054180039811a070341186050a81e405a00700100041001d084078404210400800c4242c0104000038400391802008c000c00c94060300305540203e03081d02d40418100c21007841201d2025800c241c0556803441c00303840003207055406981446009207040080c1d41c2e007402d40110f1501540a03152588400e072101e2015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 568888642 1250 568887392 568887401
    0x110d020619030b1f080a0c020d0f0e0310050f090102130e0a090204060b0a12050606220f0605300711012d0b0d0c030b0406090204090c030b0c0c030904 66
    0x70000d143d6141c041c1c0700150303107115000011048160902c0301000300741c1c4000340300040c058600c0384405c2c180442c50082176000705910b14050755524000c4d0701184906011202c44030758003440c54050280194441002000c0d07004580306002d08400c0c6051610307120102c5080740f190380308100c414008050180241c0700000f0805800403000040406d24000701c0d00040c0445426502c044154600003440c4507110390041c40700e0760700c10b5800d00100402e2a0900c0810440c1c451420740c004001401c0049090b22031040a040d0040e082888260380b19030b4885101038215880625280440b5161811140140181d9031003043c5450f400c4d01c40d01d006840781c0200381c03245c0b10144c0d810030030313952600600d005106240f070700a034402803500700c01c012043c201d0b0641b804591803d45001d008082100d40301d00401c90740740c1010304480d44081c1d4804070355214200b0200a1619181c0254040d00f85080441444618403644040d00d0259031840015119491031041d540704401095040b90000d000c007000d00d1401d5400b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 568889892 1250 568888642 568888687
    0xf03030c07060609051302090c04030b13030306080303070503040c090218040906291f020d0507080d1a010905060307270902210f04030507060c030e031303110d0206 72
    0xc0104580ba25401e130b0f81c054540131100e4006030380521481c1d50039840d11580c8a03800001c40304c1414074050454172551112080107050110380040c000455042602c0303a03011400a0201405598036400c01c160010b283e40c0c000d07201074917841144040070030806080d10840d151f01c00f200340810034040001d01800080c0810321401e89189540e121640d850302d0320070065076060708100542611a01c000c00c00c2005a400c689904421101400c2040e40d00a400042900d6440440d0078155101c80c402e1604403100d201d03181031900a00d0802e1100b03001e80003d030004882c40d8000343c0742d03030107900d407103000707210040c08129001c40009001d1003903040c0410b080d100c40040601c10000c18280d50b034665040c4000c0ea4030850440049160949208000f0411100c006400810755401d25840b420680c0b0010300c3d50051100140500fa610064020154001c0d4041d883c1c40720240252a20b07581da41000101d4040188802c0d03822211304c10b0510f40d10b2610001c42d4603d550f00801d041c0c102403080030903c51064a525 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 568891142 1250 568889892 568889903
    0xc020406030c06020106050103060f08030307050715060f1805091902180c0903060a0b011205060339010e1005070206040e10150e011205060105090d0606060306080f03030c07 76
    0x20000300200c0c0845495201900c0f580d000031640a02c0d010004044410380d622a0030794400403141800501c8001c0201c940210181c5070640c2c60b031300c10f402d1105045111005000d0303c41d00c0d2800000b0514201c0750000203c03800e1544803000da00c0c0c03000100c000d484044a4404407500000d520840113522007610307462131400542602c0016146c41040303000944190350980c00e0140c0400e00062600c1c00b081110352006000d10103001c0110070a001078a03103204151100040744d1035500060ba1030f14100064500c90900c0f0042c41040101d400d031202098504580c141a03d844100d4007401075405806008406040034140d0100d00e80682021119074000810890340040b0030080006c4040320b614402c2d0140c2030044540704c00303a02d0540711000d070f010406400c0c1c4c1480003603900c150490b0f0308040e031540840e81845e8003003800d5641c0700c012200c5d07121381804650302c500301c2d50040b010308c40c040d4004800c1c1c62194a04100c0c4984814135190f0707030348840c010320741c040c0d04c104001380000079094090001c1d14841c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 568892392 1250 568891142 568891151
    0x1a010c03112401080c19050105250f031115040f060e03030109060e0109180f02030316060605030d080606190e0a0816051f110c0a2d0e070c0204 63
    0x292000d004000001d0005414082280d0060280f1130050140300b56841c41103070041da107001c1c5000703a00d0100c12648501030501102144002294481103104a02c0e21546850b120f111070040c9411414142c0001050b0005145010317100c603c0031000a00004d065846800d5a001da50b40d0b41d038200d9801000710381110020b440d903d0f4284000c00800140d030183c90b2035240412100e081c05101c911f222016406080d81900301400b00a035184425107480c8469000403101c0f14009850001c81d20b54400e512070102d16074820250201880030540c07080e4207440e011402d540b014031034014221036403082a580310703500407c10003a80009000c00e198240414903103080120b6030420240c001070542145503ca108150030903240b01001070300d0a0840005040c0881d203440300017028013100d1001c2040a120078060102914184c001000308100750302411000900b001451038a0b00070048450301010015120f07020881c60090146500f2003200c2d00384d1b001c00c14030038100ea845000860340400d0300001070742c009655 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 568893642 1250 568892392 568892413
    0xd02031e19180b040b07080c03064b0a0b0705060c180a06052503020304062a08040509090c010f0c080c012c0109080f0703051c06091a010c0311 63
    0x3d40c1480d102e28002d500b0290759240111024050400003800f0312540c1c1c6040081118a54603004d050004020110380f00800025040002010103800400040c18001c0740d00340c40d0101e0003c10910805075800e4500241c41d980d1030a041582d0300900310010300c0f9401c00800203c1452411001e132240c8115004201e040d18070080c0411000c0790749800c070600181c00003c1c00190264420040340c000d507102e0050031000c204684000303489020b240103520400240400151211204000601042d800302c8951140485a841c0460b20b95000d84610f80c01030142030000303400c038807001c10680c50000068588051481c0f00d0001203e03560344602c1e045480d00c4081c015040c00d100240f10340751007841441a100a00d12100c19456030940e9551281c2078a681080400d0000400b100107440c020f00841c5405901d5008502d000d848601804c018541c10300402507840200304141d400c400100e46a408003048001201c0a5012011a01440403800301d00c00c03000d00000207201d400c0c2c420001c59040c0c00d443c1d00412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 568894892 1250 568893642 568893653
    0x4020f0d090302030307080f070e060307050c01060902130608040c0302090c0705010c2a15050a11120a060b07050a1101030f09050c100207060909090201020109080d02031e1918 77
    0x18407207003500168404020842102d8000c840b440d0040d14a003451175403482c1048000304016141ea00703550040402102042195000b441a81d403102c00000090103410780b00c28501e4000d4100d01400510550030820000710907004420941c044d0390000c04080c0c9160840e0203011a8a4001d80585141c943c00c11010000c0b9800b0321491f40642200c0d602d000d096240031950b9050031800c503d03240139403400601100001882c07030140c603a800014100110b00c41d40c500e0202d200a01c80c81c40c40031402040000c40100c0485c000440c0340c4205255042001602d480301401041802007400050503070741f043c0c40c0c1c0d2001c1802012000c3c2c0d140e005141c00702e18090b4200d9000e054841400c0204d44035404008080c90b0f0b450560548001340845100030b07c8000d2521200506002951007060701c420354421040d01964400c0d0091035010350041d00360b80d0ba2355a045554002540100c8401d0b10949040f045200200d003804013690050316404114021100c4d40c20107000144400b07500c040004005200d03100000340d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 568896142 1250 568894892 568894901
    0x40b180907081503010209010c03080a141608130c050d06090c180b030309010507030c0f0507060e1e01091e080a0c0e0a150303141b06090c01110c04020f0d 68
    0x1581c607a40c800345810181d09000702c150200e00d80314885c0e401442480c20303e0f680080703030704040350b01850220043c0e116108410020091940c8034040158a0010024001c401264035000a200c0340d035040460b0b40ca001c920300c50860340c1200146071034803800c0104940d00e03019000c07904641c02000b0000e8607618a6441c030b0b040381c0b400d134490506003106407251a1408003500c41c107110030b4000d078003075803a001c0c0000008186125444009042c41260015101400102203e8102441c0e1004c00c403000940c5942000c0e001c00c0200c0640b520810104a20100d00b49024080c001b852006864001c1294109444030781010b20300d2001e8501c141c99140d00040348a820440408164081c41a040c0d107681070007481c40c2e100342c00070800321140d424603004065182481004504607030b010700d032840c2001040c0c18055111304c111a4514a05c60440c101c54000410104100c4d000d2000c8100b00c0e40c030841404015202500800c6000c0055040600314980c1f41c2050340080620210541500c1d00d0111600b05c0c035811603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 568897392 1250 568896142 568896151
    0xc090c0304150c1107050a050a1502070306020a0801050a0605120115020a0602070b040b011a040b0f0d0207030207081e03030604050a061517180318040605120a120e0303040b1809 78
    0x51320100c804800d21400d02c0410301504081c1c0352402c546041c0404035640c11128420141c02c0c241704d00c0031030050b070720900010b000703940d00c01401e650301c5c2800702c03000701040028051588a00e0710b216001401501400c11205112506400f4200c107031f06c0e19440000b580b030300111110079030040508100004400b480144072072031040c1545000c0d8186400d002940d40f40580003450a42c201d155141c22084201301520212070300c0702002030741d03415603440218040c011280200406400481c2403020582c01150070310950710408200c8a8508500041d4a13944c0c0c21402d104003141c1082000c1040c42c10705070080390b804600340002050f0f07269185054140c0505900c58280001e107002d0740c3c0140380300b0890070580c12890300003464420350000701035262244604010895040b16801c40c100164840ba00864018480140804c240349100c0c0c1c0340540b075403050b000c1103404001e0301c0030b02440c650049845c803802e10303805001503081900384441d4030000c3c0c1c40292510304e03e044070310400c07046659201e07403988203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 568898642 1250 568897392 568897397
    0xb040606210606051009030809030a02090108010b090a05100303080c0c1f0e160e06220c110105090a290a0207030e010c082a01020f09010206090c090c0304150c 70
    0x780d1106003008012160b654000910401a42e5015907049070300640000c242c0384c00c0038040346c0d41d00c0301e80002072404503c884000c2d00030303c10000001c0c03014810b5009102402098800d09000c1c1d403211410021541c2c200c43c0c1d0445000541d40c14000b1a1240910351f51200c0505a030038030301181c0d002c1952070f210314018054041c00c0001488110740c3e905001e4032006588070401008814513010808603003c5e900d000302c61503071032107200040084d65040705140400d440c0320b16040155440c030700b10305d0290504000d9000406c0080e081e00c101c510051055600c030340c80307a0001d44046549559801203840002c400b004409500865220b0011540d02c2450700419003e040141e55082d24500540300480114101c2c3c107210180103100045080c017400c030b900c10440c1d03000107501f40c11503038140840f40c2039280c080c0045602c04140c4c0c2c034081d28400001c0070802026002c540850395000c203459600c0100131f41090b000003003040425003110781d807800341d50003503c81c1c000d8003a4802c8034030014007103400700d800c00c000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 568899892 1250 568898642 568898699
    0x260a21030207050307050a0c080609060a0e16060908011808041a07050609011407030219030e01060314070303032007080703030207051605010306060e030303150609102102160b040606 80
    0x10003015800d001b00409c40c0001400d96443c1208030b41d6250b14000349992030071502c0c1e9483c02c3c42c085040c4400c58201d0348000e000040c0f15240c42c4010441c8196000340b64156191124100014002084000341664044402e40c0780504001980c504207440703498141595805100c000c0c0018002c0c401d1500c210300c01000055641d189402100f07043c903014102c28145032042142c0ca01c1f5115440540524210303e00f4085488034a001c280703801001150300203048407032800c1f80c000655001049170800c6030f0003075409020840c8014101c603003c41001c0b1111801303110800070b040005040d0780242181500a0400500b0f0002c0c0b40c50701400c20103448a0a0f05020405d0414003096815100390006020340d031030010400f2080c2c0f008a03980384000741c9800314030070720305109254580c0c3e803130201e800b001c40140c400e036500c80341004098515811481502000c09194000e000d040d1480d00c01e0300c040082800e0324504442d56034a910303a50610181c0b069808540329040030500103180d04142000f528807401c1c00c031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 568901142 1250 568899892 568899913
    0xa03021606230c07170405060a020328050715181401050903030601091e0807120515100e1323011a060406050d0e010501260a2103020705030705 63
    0x100075150100e03038900b003140c00801d10614600306410b0710a110707407000e405002d0484204480b0181d02441e40f1040d40318800055110305141d0101c05040100d40f81800107a030204842d0015000510180d09030000500c20710500020948a460040500b00300b440700240e591290041c7d101caa5007007070001d85119a030305181d101040c0c000d10030103502c201084051340c25410203070002062041c05100b2090000702c0e241076800c03e5a2001c1c4070702c004241c0740c81211a07240da11a5250111212590150344500861b190303100e182500c0040380340b150301440046600b43e0f082205091144a001d00300c1004003810710440c100207440460781c02c04103442801383c101d940c4440e00c0c0450a41740c066407014041d120300105448039444160030f90f41a03501c942489522142c495074610002e0020311610380c0c0d150b007001d0002840e035414049154000860600c7e6543e0010b0429515548600c86100141464501c03c80700c8490070707012040c2124405035190140ca040e4041c1c84e010710b9901324020941d0503401c4410f111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 568902392 1250 568901142 568901171
    0x50a0909060f23060901030b04020c03042603040311130f0c03150f1508060d05190b0a0203071e09030b0c04090c080405152e080d0e03070302060a03021606 68
    0x3890401112a0f54404210401140b894002c1d010482e0515449014500b140e941e907406a801106246040343d445566449440300d1404a261000720000202d1007400c0c22024040120740c10b482d080002250a07046910912031030b41ca00242401c5081c2e0b9038081b405c00f800d100d0180c0d0400649564000c05c02800d40f4081107005442580190300c1c12800070307000c00440707444a074440c1c0000c2141c28400d030365170b942e900440d4003542e0380c11000b130950080c0c44450b12850501414400428026039840040d9034075a00350b08102c0c07005035a400080b402000c0c2030804900d5410703010901814600d410300109a41c3e59540f8034200041d0b44c1461641c0c0049824842440c13140300c2c0da10076404a20308440b031400c140d100d05844c0c2ca0178491641140180d03400180c00c0d0071703d9000943d0001004507100407201c6074070342440c4e1404040c2c001c41446005003007071100014440c2001c5190408020302404c4403600d0b40d401c211702c0b5409242c5c840c080c59024041e103130780059041000344400d8002d01c40460340500c420f411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 568903642 1250 568902392 568902419
    0xf1b0d0c0e0f0d03121a130507030507030608190309080d0207080d030204050a090b06120708090618030904050415110a030506040c0c11180a0e01050c0702060a050a0909060f 76
    0x12036001e4036111941e1808a41c0c401407001c070b25017082030001000b0b10300c00c14012800c039603a0b8569400203070f044540f610110381d9034080d030300c19140340e90304024545030294200c040d20450300c0b511840343e1081503e24001c05c0b041c598140e8542c0300342080884d01c3e03520104581402600c00090340540c01c074080800450030140311a5808401c2481d0131840c2c942400000b0f140390740c280c0120205165070300b042c1710140d00c540b800c94051002c0c03841010103601e4501d000801001c001c0b034004885c0c0c000d00d8003007200d07143e9043e13036801e541d4035400143d420444090280001400c00400070384a903a06400d0a01d40c014040c400c0203203d03560b001840c1c4d600c40140341c0140c01c1c2c4a000d85000d0007507107060030300c00300d40f41c0c0302124039101035204a201c41c20407403602c0002d004006143c403803032220b15490284082d200c0180d07c4a03490703015480090015940f40f20080748540295000650022802c01121003140d1248006000ca5601814095166502c0b0044c60b811540c664014034000306c40d101083c008414000304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 568904892 1250 568903642 568903669
    0x1207060809010e0322090216111005040605091c0b0105031507081504020d11090301150b030705070c030b0112060b0f0a03170f18180f1b0d0c0e 63
    0x90000c0d400c202c1c43c0310381e42c1c031540c0094008810b60740c5440e50f98681c1c0c0603e41e8010040c0e04010364560355038104034241030704101c00845500829000789815800d0103814102800e28946905050614108055440b0707808240ca40c0d0b805001040b0118060070010b012105043c00f4200d00b070500d604083c1414501030340c080c0003000354000e5000f0406159401a406540300709072090300e00c689154440450081e01030003400c9200310b81024a203140000345031014250071002203009124000704020190f04180844c0200b508141c0200000b600d014082e800404450b4805d408844415690340c46c1d5900e041400c0e040039210824600b150400c2c40746d54040c83c0307003c6c0005c5a0144221a0240000e4080402d51000801f40c0d220b0070100072080103c002510b80c41008414080c2d41c0d0350006072201407800c110b4910500c100c034a141d10307003170309403041d0601c500c42e062002460b4a151644105032541800c9100e8408068208100c0680306200c9405403c001c3e4040e51911860f0450800030046103110150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 568906142 1250 568904892 568904911
    0xf0306050606120624180406050604081525050a08010e1608041401020a05040302090f0c0d02070f061a01030e06100902160501181a040804090b0f12070608 68
    0x4496010009400a02d40d08130b001100c40c19015100840d041240a00c600e81e01c1040d40000b0071502c3d002e8080540701890324404850420506d91900108603070340c0114000c4ca06a40c0c004e91600d080074440c13429117038202250321074480c40c01c045000036090750601e030a46000010004266000d00c6a0001005030141452625240c034600e450b0100200881800524104000c101c20101c0c084c09079001d181c094a0b0080c4000399581c0c160b4a40180c415070041c4000c9011ba0155000114081c14800b0058003804104109038545081d61050398041d40040300c0c00c3c0d0700c84c05c1d00819480007440e01e1051034a10840100090200030b030420015049841060420b50203030440e10030010007008042620b0151a10244016120b2045c01c2d022000140301c07841c001e01c650302e0283e48528030b164020345405414820505d0102000003402004110902545c1c020074402c4144020b10103c61290400700301c014001d040016440240b400040d0b18485168840000e40c00030702c000c1c03100301d0b032101c1c03815407105552 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 568907392 1250 568906142 568906147
    0x20313120218040f0209090706020615090c0d0609021612020601030506070c0303150b130909081c0f1103010f1202060d0b030312010f0e0702010e0d080709050303040f0306050606 78
    0x2038000c103a0341a9580c0b41c401c10502114000b80c10000303204c3c0300850b80c03900070f80360b40480c3ca099507110b95105200e00075000581f040000046544003030384520781d03404a010701001d145485214500905800c0000700e00ca0700382d2140804112048c59101806014981c0c0f602c4611401090604036003000030a03004400b19000300d001440490310018440e40c200a061030b200004800302d0404400030408a400c0c25200134000a001130300003140005020011014419075546c141d8900e064030480b49240c00c0201904c0b030501001c1c19101d101206031400c1e00c403604020600500f814a424111044a40f556401030004001800f18403014082c64003d00020014a080003403242c001468030f000c1c4103103005c0c01603120910f42c03596440910030b541c0c80300e104250030303051540c40341d060400c003444034051610b42c06110300010304294414014000e0700504440640120525142c6c1150b022030b005044c0028080790020016080c2c60030002000104003520110300c4090442ca40a02524400f0303007010700c6030406 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 568908642 1250 568907392 568907429
    0xb0102160308030a0f050c0310080d020705040f020408190b010807030206120c0c0a0807020906010903120e241335010b0901060c1401050123040b03070303020313 71
    0xd400c604064a4200050a0300e95480e01e003082c01801405003007007400d60408042c0000c41303001d070b00518000c09103109100f949580300d02c003055503211031444c5440140c3c8400020032017424181c0c88000110250039000d850306454640d02c074175080d02c0e2002d0001c00200d801e404020703c4080d1241a014040d40c5020f00b00151071500014000e000300c5100801d250b500b03101141808070148111600c2030b24000550714090064142804150803d45d000c0e80201c904400207101c0d58851107120741030300d0b80800c0b100d1040910700811510802242ca5868100c4c501006039504d0300000e0280304898540c04200c96521044100c0812051240303500800440c0f0031130492403501c1484041c1d0499060820b103881081c2d05c40c0c0c0307901a01410f0f07400146604076564030008540385511444000109000e120521100b81580c100c3c6401c03a4400d2042607040303000d01101c13202c1c1030071241e59206401c000800200d080903200c80000e060031920341c0f0803005a480043e600f00ca04615150540040c41e0840c03c44040020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 568909892 1250 568908642 568908673
    0x319050316050d06051008010306050a0203071407032307060b0409050c0904050115090b040b0f011b02030c031b03101107060507111c02010b040e0c060903030c06090c040b0102 77
    0x440c1d440e58148600401c480c1d803140c81641c81400144001000c15910b20001940070302000d81c02e001c2651042c0c1400c0004056881c18002c8030300a41e066941d4039240d0031114203454654218500490070005c01091886045c61043d150b50050300090700001c2d0f60b03c800349004c4003241c1401c400107004600b004920800700360045a8210f071180700f80d8032a80c1c2d82c0c0d11458a580102050f18140d0383c4103422520100d02d0030501d80c010003444c00161b9040040071018805c010f4500000444240003541709081d605209420303048040c0388510103822a1003258010000a040c4100d5200300d803400c0b854180085003e25082054100130035a84804100c007440c45000300340030744510880a842e90346c840000c1201c540c443d101058011502d403041c1e9020044229841c5032404c441800d0303500540c2400300d500c040d0701d0144101c0e030100029500401409180340306000507508444506603046c0414801140254000c0c4400f5100740c888802030000000380c8010407048a46002010381150302000c0d031f01c0d21b000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 568911142 1250 568909892 568909921
    0x90e04081e040e0a06060912021f0302041d0603120703021b0a0503010e010510050a0b04090b150c061b1812193503010b07051005070203190503 63
    0x11100c1c00d070000004100c40e05800340b140350300c81d151103040103080054007146503005005981090355560180c9564000301c07900440500f4002e03500240d503420b00c5000c0c1806100e00c07081e42517a814050b08107540e5030b07031170010950b0440c001050701441d0010403149107001d00581c4000205012510b013010b14a880007540c2da0184c8507051342901c0325981b425003555405c0503e900500c9c00a00901c046000424641d0203804142e900446500e214040410a8505104c840040c3c0d036041c61041e080c640b0302151100905000d11183e9046002040d004000300c0c0a00020203460520700700804682c100304e4000a840d268103c2c08260201060240740081d8452040b03900d41a20100c8090b0212200d0303901c0307542420010484450740b56a0b4143e1134040082243e01c6542c0c1c0a2001ea102d480340390364150304089007050b2040090811010001400841d001c503005c0d2003124011f100b11380b000c1c010703220260121401582e00c080076074408602c6694402180d041a0034103145031401d6411414451070948484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 568912392 1250 568911142 568911157
    0x201021c0902011b050109110f1302090402070c03080a0905030a0305070303051807080d1107290d0504060e0c0a230102030706060608101401020d08090f0d03020a090e0408 75
    0x8035152a81d0038296881101a4042100030080c8200000c069190090091171109800c07101c00000c1c07411000b4500d0070310002c00740704001502030104c4102c108101e030001e501c8420401d5110383c2c00d12200000c2404c111103000030b144105103160340e6001c10704019000401c1030f408580300754422141003002075400b070706079140740764103080104d42c80d11950300c201c141880d0b015a0030680d21407400b000503030a0f00007500315130454060700c2e41c4004201140011b5110380c854041c000e00540007443c0c0842e007aa84c916040b87c2c09007403981d594100f520382c40b40202680d030151016240b0584511f000d0b40c0600080c0030910b07443c2000c5a08001d094640803003240c4a00c441e16004003e400b18a000004030f9000f4001c0f01c0310320340d10101c104042915620050f05002c0217a501c0c50815180440104280700e203842c01480c1044160014059400304100480b0046001400480c145c020150a24902c21040142d00001c80785070300c0260b120b002ea8200107005041581c415003080203c0010311011680c99006c0700c208 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 568913642 1250 568912392 568912447
    0x1091505060f090c0c0a03020c041109031b0303040b0a17071707030e03120103120206070c080d05071e200712060b031c050a08252109140d020102 64
    0x22990b44e01d859080e203002c0c49070900b9140c001c40e014130042540c04900b00d45103650454041012449084021f42c050003001d64003a0103074031560804010785909413613203150140c01411a85425242c01008550703400c590801408200341310741d0441803913002122980d202c002494444059460b01920000101c00030b010035061558a0003280d680311020300850311861803082c4001069650782c13038043c50b50001c0a00d0710f4018000d210201da1201d10603c417624810340c003ea280e0b0b0900e158282d05a005240103003c0006000c6e5040c0403c02403900d20000c80c101220070f84034868100a807003400e420300d03144024090a55045440207000c00b01440c03403080c1849400003000034004060001103460450015140c030040110582401c10007548000205403c000d59640c40403241c0b903111312001c92a040c04500d055902c010310a031419588200c14072022428000e41c828900500303100001c00b03d40f103e85040d01c03950748840100124040400045207424040c0c03008610f090402c00d25441c410840c000144034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 568914892 1250 568913642 568913659
    0x11b050a0f120e0312070206070203070b06010c170903010b0a0f06140f03100303030c021b12070306050c0d110f090d050a0b07201c032a0201091505060f 67
    0x20140c03007164105002d160001c1d0400c010034455120075aa900070300c2181070b903040705000290f07102e4404a500e0380140d00740c1e0020750070304c0041c1c7d84400040b0f0004045604020300050400041100b10303000441c8445101011a542c003401010b142c01c1d181c0c0190343d1805683c0e403d008000b02c90319915200d0803038001e483c0c802002d03401c0502c600214881c2c4581c60000c00707000300a011590382d0f805454400c4a129890400403940c0740841640c035881c46400d00e109400c0805110062030034070800804c04d070503038001a5103002d0703140d17500c401c00c459040e1100030f0f400001040070b0110008501c038070240c80d041581200d082010012450781d03c1d00c0f4500031140240c100202803410005c1c104544414a540300c6819100e074604030700020100300c580c0000382c000d40500c0b0461602d0450225040181807038580030b101c541c1c0642e04d02540a416600d00c081c5440c99015545683d560701c504075400841083e50000c504c02580b0305040d00360814101010000c1454842880300030b50b43e028991010701c3d0b081c0e45141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 568916142 1250 568914892 568914917
    0x70e01060509011806030c0210060308030601050c0f0a0b011505070c0b0c0a0f030c1502120403030509030705060c040e0714030112080c150a06090e0a060e0a15020408011b050a 77
    0xc6040049001400100d913015001140e99900364001c680c0c071404c1030342110b2034255546886410b50b001840080e0905104001050244d40f10383d0050081c0342c029411074002c21324802142d032804503140c0050383e503503001e5401846101a0360489081040b12450002d09107007440c0c40d5810282c0a43c4078880d5049000a8940c2e4410000d004180c3c541d03410042c0c1d40d05400300c60070041c0907030344005412a0a55100c10701c2c0020040da51090365106100d03d10100d103a9519541c0903402881c0140800300c0521080c01050005081000081d1041c03142d80c10301d0380c9452515507006800140075108800744150000c2009885024105aa045801c0c1ca03c000c01060740d83d00703000c02c4c2c0d44540d265444441c01186054203400040c010464000c424404c42080050381d114142c0c412220020b40020b61900204d0180001c1126900401140c101502c190740700c100c201c2d0b50310a00c050302c130b1812400054011404000040c420700c40c0c088a070f040701c00c0c00004140142c0008000388100965001400404010716 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 568917392 1250 568916142 568916147
    0x10501020d05030f07020c060c0115060c0b04020f040b100504170105090d0509190806070e121002130e041209080c010e091015020c03070f0f03080d0f1409010b03070e0106050901 78
    0x71f584200b0301410f80e9581c0d2100f50a047d0180110860280c20007092440000310b031031044c0200040c8075080f001c2c41d232403034880b03030700700100c0444040c140c2380c1c060717107404802c4080e580302e6110015444154036040d41e518580700c00c00c416a20304104003e80341c2d240800700110a113011460304401d00d181e01d0700c81d645e00740304800202141ca0070402e40400541a103004183d1050000303e0500901864640345480b800b1801003200107034014042c030070160040580c4c400c112050343c011b416107650a08020359429220580c1500c42d080480381581d070001105011480c040d003040340b00c0b01914400c2c025000010441c800604503038400000140508050400148488040310741d000162090012244e00d196440b50020f584080ea00f0307030359200c2e020740c3e680007400d80d1462092004907072940d110b91078450310790380b01c4082940052065640c451381303c0c201015104564030800c02c0a0040020484581c01c0681381c031030031507084050705800307507002110500010040070b820074110b45551a126565500c040c004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 568918642 1250 568917392 568917403
    0x1018020d06090f060e0610060f050a1b1208090106080604021003090507080d030e030309060c07140105190b030c090a0b0f27130816171201060305010501020d05030f0702 74
    0x42c0c50200b03c0c810220401c800b541045070000004004c64a0035150744030540c1c012000e0303214542c041040c1c141c0c08403820b4095130161100048504111012540e40132001c015800300b01401c4420741c00b01c25003e540035800c080229048600d50008006c05c5d4204017030103594000103030020703209a6400708450401031107038100d51201036114080d00c2a076655210310390394980b2500e105a01007401c28018032141c00001040d20b01c00d0321030328000c0c0000d03221011000a82d44c8200f030240c62103070a0fa2001c00d0610424012140100050250300d40703480e15203403c5500f102e46001005100b038005100800710703603072000f02d42034201c400c1080008007a00c20800285180112440c51504402c40a1202c0810b0100965442850b200c80c01d16090760359404891a13030010b0000401868a0303810b11034a41c420180c00540708085124419080e020607290350b0507611340d00300b2191a110302003007500611415500d80251401000c0c00e000a010b410b81c1c0c04405000340c0130060040301114040000102040d108120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 568919892 1250 568918642 568918661
    0x2070206070308060328081e0c0f010606030e0606120f19060e0d020a14010b0901090c03112a10020f03011401080c0d0e1c0c051018020d06 61
    0x1140da9120000e00d000307482d035201142e210b48a0300580b02c04039084a4402c880c81d0180140c1c21490440f1162603680118a0301300c000d80c80804188040c51506001c1d5000c000d16200146600408240c0c14114441d0b00752040d81c0c10500c05c0600700804800d55204c006001c540046080304c11400c407146541c40303240340188450080700c25210b440c5a05010800814241045900840702841106180216155543c0c280100c400c0140d01c8a00c03844003040f00307810242d081c101c014002154803510303880041d054850a811140c07405544001c010442a0036200762250201000c03069803e108030046e25a4224a810301c1c1e01c3c55900000ca00303000c0d20b00c4180071546102c4480441191100440c0c0e51300c54454109004030100118802c6140f96250702608556200741a130220041c541003d010541c0040c080c2400b494946101d0485107070303800e4000240e41d4958150031b985092110100342021407504495015000030949452400268030302c00e015007204154041e54407103004202d610700fa0004086480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 568921142 1250 568919892 568919899
    0x2030703020409050a06061e051608040e181c170a060302030d140304060903110601090510140a1a1c05250f0311430c05010e04020702 59
    0x108228940340c0590207003040c1c6810440401445d50781070202c1c41221824000c1c40042004103c0c4412041160600041d00c0441c614080b0300b0048010802001d00c20118000c8031049000b140c1484031a490000250f0b000c00030111000218a15540d865103d400c4242081d203000010347c03001c041b850060100c840e04940c2021441c125140501e58400240200d0204074481d014400321690a18403d40c0d100307100e03944904456113161119a143d100820702940210701780308040003007201940b01030114034000c0098280101d20345c541080407203080c00d826041803151142e1010000055150083e0a60030344e00e10340b540c6c0101c034906c08483d007024000c100c0c2c103c640450044507032040440c6500f02c82c0c09410010058a490440d148002d050040f2022001000030340340083e001000e4400c1e00020980c54502003503601e485042c1043d0605650515031500c22303c10460f5100501400f900a03c0d0172401020702c66942001c1c00b41c3c1c1c1c3d4000454948919030401226814455003030340c4580c11101c0d45035004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 568922392 1250 568921142 568921147
    0x30b0108011a09070930120207120506130516060201020c010f1107020405040309120602090a0b1306051c020c15010501030234052406010507150b0409050102 69
    0x1904014040c00780b040041c1d1550074801031424440c00c2c041e1a0314094020354442c01c1c0303203e0070480c0702c403c02c04428200c0c800350700f81c08066100038600c02c0300400c0c03014060881685a04442d450181ca8844107601c4450814000c04179440030402c0440c1d0769030041124801090081d10074240305141c610381c3c140204140050410024105070154010310001c01c41030001d00c0401803d8480c60101c0c0e010a1056021a100b041004018038007a80700a6129102b802c001031041d0302c440502010841983c030484050341c0c0011000e06916104110000030450200d8051812058040104807840070b449101e05008003c1280b1031186800e41c0402c444000840c400c42d1180140c00b0060b03074400c00748404240b111044c00010038194440c0c0212446042654402600034040500c1e1283c0e940d210701050882070029043d140004405202000d080507420a082c62400d204401c0001102c001502c1c05040c03050810250300000c02103c00302226047d49880040c2d1071740402c000c075010b851356480c0100b055100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 568923642 1250 568922392 568922399
    0x901080f120a0903060e0111030c04090605150a0f0903120314061504140109030b090d08130b04240903050c07061103090f010516060501150206040f110406030b01 71
    0x420a6100284004551086086049450070761040041d0280024408072052010030007503081100c24131142c90000071704100207058259540c1007502c094541d000c00040030041c0b6402d90054101500013121071004e020180c3c2c04030102807140381c51000c203004000030032840443c014840b901c01180c0007801d0110024046000400a00c1440040744c007011844000c20000d041c1803034400d260003c04211149041d00700120708221034607284049040049120000c00010300c000540f40c0240c80d40310041c0900d040c100400741c07100c00e000b09400e90414004071503a01040c154624142c0040c0c001c48544058282c2002600c01c142c5186902c3c60001d040801800c00c00d9804402440c07071104540c107880d5102e403200001ca680c1c141c3e50403141c2d80c6900501c046203661800715046040c8201c1410300c5413034040401d041e541c0c40040d00c00103640c2641d450740100041c7ca0406e60700f2041d80682d1024148501c1c069658100c01620050b0247c4080001c8460310883d80301c0f948450f002d59044042c0705120340c1d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 568924892 1250 568923642 568923659
    0x3040f050a0c080d120911040218120a03090b030705040e0604111605010501060905030703110307121a01050103060b0a080601110f060405071e06050d1803030b1504081e03090901 78
    0x350b1350400e8000545400140500903013074450005220740c0039105803001c0c00c841040002940000c0c0c880035440140c400c40107103070b13910310740714111004601c0050401004d103401c001d040a0040e1344a00e40b06082042000140b5501c20300311003d995907100411555100da1012500400c6059001e210041000030906081d999400d4000000c602c290001d201d140e0321004e08507012445031207400d425600c1100301b07100242603010000f0a4280140449060a903901805034104c400060140c2c1e020801281e408200100a0b818a014020030300703042c0103480c505200d5810714031071b08031200100700c1581e01082541c2c0c07041903043c9080c0000c104440069142042c7c2580380c86041e58111003511440700005052250740101264040e0040c56545956151540c142e170b850b880680da9196181d030302c2c000c40d02d904181d607100490301070290381c00003a0851410300380000c10380b1810a44141e180180020440700b800007900d018401c182c500e6035413110030170a84107495030003242005603001d20f1010001c100b50300f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 568926142 1250 568924892 568924903
    0x30703020c12160b06010e13180b070503010306270204050910050c04082401030209180717010c020f0319030905030a050307021b03060c0334180b03040f050a0c08 71
    0x18091380300c030b54058407603c0040d2400c540406850b07402c1850342030850324081c0140d20003480001e041c00740ca058035a45079619111140304a40f11008030380040014001c2c090305120b01041d0390f462110041300c0f1740021071391840100519500901c540d0b203032030006008410a0101c4450850084028091741c100069608140d4002c1c0c011284180f01e271000100358100080071000302c090015500c00c041ea42540c003800440c00300100b8920b14450041052007400004001c03060040040901000412045400301c03401c0d992220424002c40d4003d1800406070800881102c8101e001c00c2c1e2242e54031003001e141940500680325004d04a808007154100416810900861084015500361181d82d01844007600030454841e641c9901343d84a4400900050494801540c10000d9000d05403180401c0ca4051b860009254071001d140e00e1030b05c0c005919050b00140803030060a0b1240d00c040d07031581810002081400b0041019203500940700c02441070000c18001c00260a0b003008021007200d03121020165200b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 568927392 1250 568926142 568926187
    0x40c05091f0e0d0c0306050702070e04060510080606130e0c04020c03030604200d0b0622030212010603031e0c1b0513020306061c0615080f070203040b030703020c12 72
    0x4146820b8440301d490102c1e0000003441d44840c0240c040c50564440c0801440020280010740c8205040132854114030340400c2d2082c2d21600020942d45090194003150700125403181c02d4a500000510900b0703515211120100759041400044152181c0107961a19070742c001c59603041480094507041410010005502c82c0d10256414407502c400300ca1443c0700880703140f0514102034001e101c1440021a80e81140f07800b408018481410701c2369410110b00740a984540d50080e400400e50100114100000d0300038290303036030380000c000d03881c59a140904050402e410246880910b00c1504d030305180101c00343d8450300d03003000394400800304110144800000c030303006143c0300c2c40985808020b03a03407442c0210791280e00050318881c146450360008860708504803a49a000c0f07506d4441c04107a030502a03a0580c2400060b51341c3c1c12071410400c0003030070a40005002c24045420400050180f82025001c03a40c1003865850b0050f0b59101180c1210305124134008583d1719100e00249c081040009003151641e0b5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 568928642 1250 568927392 568927397
    0xf05010b010c0f0308130b010816080c0109121a090d0206090309060a0f09031403120604051b031009020307350703090f0807030c0b0f0411040c05091f 66
    0xa0100c0d0000554003100b01c04001000441000030100000e0b00c01c0140c241c108084640d4562017000079a00c11410303003426007210b101540213a800300c005040f458070080080520030f0140500340c1c4400c0009040030054080e900d03074400e4018a00c4204a62108000044a074a9140c00311500381a9011600e41c0c402d201240014800d14000c03901c2c141011046035810303c40108950b2504907400c1040c3c80782c5442d03131100b2007070150b801800408641c500755240c1000c00c01c140030f195103203482e85401c141c041002d025035000710f01d00810040c036801c0d190300d401c0d00c0404004c0700541302d80d08c040c211140100103170086682d603030001c0207020440360810289034401001307040c03404035844500040541060220362030403902004402085985010368415980b40c2c1c0074201c000c1280d502c40d29404100e52041c0c404800186074900014280520b2620854005045202000741401e103030710f480040411641c0840d105944d0303142c00009840c01001140c0e03000c4c4000c0c081c903074811440300c412580715440c201031002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 568929892 1250 568928642 568928651
    0x15030a0b0a021b2a031e061617040201110f010204240f020c1002030408011b0314010f06180e0708090106150c0f080c060c09031006050609010f03180f0501 68
    0x30302d0320301040c0c544030103121078152962000603800404490700c010801c07035094011501402c0c1b842511051092a00345014004e21903030131f1400c0240000029644440d04100700440d400413216060165150010f8091802032050003920941c141002c6006150544c2980700040002c0c021442251020114400080003205250000e07000d90f00003400c00307030010058224207040d4517549060307400c000d03280e40e5501c11282095141d000e084e08444815400f444001c4c0e0720111402c80c0c507494010070400c02c0c2e170f034604407540e0b51605143c4020504140141c00070b0000c58500d403454003240a2000d002008006040c42e8039041000d0054a07000c02602c405003a035080240104030880303000008851480c0e42d035204029030714030380c44480c40c90035031010071a40300c44108141c1400740c3c01001101d0041490461496941c0030325000c0501d40302c924608042010300b00942044585d07500020388942420030300f41429410032081c812001440900d1640c00c120b188880c000c2d040c403911020704031f02944070790b00801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 568931142 1250 568929892 568929937
    0x4140606010e03061614041d0601020a1707021309080d0c08160c0203030d06080f0705090105010e130e1903120603080316020c040c0c0b160815030a0b0a02 68
    0x10b40b03000c0703001d070255016800307140854041c100c1103001a540e41140d00d09103005400501114038945e0240d800607031200d20302503550791020b003100c4d80c86401071001d00013011404039903075460300c40d03252545401b401404085144001d40d20f58203a802a915911401002121080d00d0581044e0700078580d0080c0061034204035492050049000070300840040410346070051f0149421180300780c081004a0b00f6020901082110341c0b03960103001c014041c040701030102c5441c400b000c40d1410f4055441107201c2d16011004102d1a41c01c80d86a0088244c182c8c3c80d6420583d100d20054060216140085564840e0300d42c41b000b242100d40c0d042c9034007803082e5a14180c0066007150f00080e03485600024050b154104042030300078105440c0b000b049405070041e03811804440002a0481c0c55030039040c2c0101d42440501c00c104408120010b40c45016640350b41c40c1640c00c940b000305000802000e11491004120703130308020b43d808004c000850b41d0311071005001494045614000394011b001c9404509000c0304284 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 568932392 1250 568931142 568931147
    0x602100501080c0607140f0f0607021c0f11070b090a0b071707020109090c05070b01170a140c030105040f0c12050d03050a140a0606140f070b0a0b090414060601 70
    0x19049804000083c2040c4001d901004042d500c0b5210031500d90130030145088500c8010b11908442d01e004038043d107500744581e101c003814403400412800c210340204108030501e5883d01082a6040034a1400c0c2806060302407058039050030303516a804441c0708900002801c18107100c001c100b101c0060b100c01083c2541c9202ea08032a02501c0401001e0203041242c042e06e225850000c1c0c09181d00500d8a600341641d102c10000456840014060010700c000407038038244800c00100c0c90051400c14000c40701d1519000c0c400d901c13545920401000025a03462202000108004a0100000040081001e81014941609000d12110003100e0014465000003030103140d00c9e84040d0041d8204001c0d001a8030980000c40c010500200000b40305640c80600040c07c41c00150300e60310034201000002116030400001510031503551620107480c0e130007001841c141759421000c1c1d90105500403440101070300d401e0400340251120b5068542c004107a80108014042c2080003403031a22801da00f03559082c0c9502004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 568933642 1250 568932392 568932401
    0x518100b03060105061608070308060405060627120312010f05030106080d05090402070f060b0f10050d020c1009121101140414010b090a020703090509070221130609060210 75
    0x21603050700803400401c000d0500600401c000900c00c05802d1a081e0142d40d061f04075081300304150002001c000410401d07060920500350030100c1116040d00f001e0300c1c3da0320600281504294880303407000390014815a40c44440c400c2c15203038138900589884054020001421650900c0b8140c0c02caa0300341400203040c101845043c2c15101a1000703890704001c200070940b0181c0c0446901d9400c603500300050400301d0b1103c110000e4161041c0c4022581001c9082040b039802c00b540110b0b48110000a443d40b40c0540101c1100d452009008016071550700103c0321500f0007080e40144140a800c0070000404c000b0a28284000c1d0000c54560071600205c0711704150032100c0e442c0951000b0100040030034003082e60340c0ca1103095003008000126628000702c01254451400b520001d0040b600414681c0815030094007540280400f5a001002c615210100035922a0300c2001d101f02e00b4005904465409100d004803030b000c086070500000c0c1c1554401d4000c000e08818401c500040c0201e403000305088030310380075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 568934892 1250 568933642 568933661
    0xc0111211b030f0717190b1f1124041401020f0901050d02160c15050711040905120c0618030307090303050a0e0a03050610170601140a09051810 63
    0x505a00759030b141483e60390061006003d0100b4004064a403085c0d42004002452162210080d004802e84003c5480000e6948074103015202e04040c1440280950700d0410104090b112880c0c40f901411422885a041c851140481a0098240207821400704124224030703002d18801c0c0f11300b03131008040800140c00c030301072070b00c030001410300400418080c2e61050002e04510300e5190001482c006650018000041c082d40086422504400e0104806144201083c1500d031841c1012854044903983c6e4a01e03800303c00342124070a80d99030031008140101044003880f4440c081d80141d56403201d407240c0580d240c800f220012083e0104401c251001d00c408030a8034001ca52030746403410030a08640e000e650a420880c855420070108c100341010135560b0f0310741c1a00840c00303038000d0001e501781a13000b5520031000b5004405d1030740054072504914007000980c241164041c20621804024980000328490801d2b0710031880c0d18105818001c03170b000b40340c4900982e092004125006004880b1119081e580e1010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 568936142 1250 568934892 568934941
    0x90b0c0421020103141503010606140904181202030310140d0f05031e09040e16120203011e2a05040303200d0801030b011208040603020c011121 63
    0x52035001d44289100040100c5441410040b41103240c102d85d0306410070f0210b94407107018042011400c91800c0a206d00009040e19141003d049003100482d5040c41c8642c0c050107004550f10f1003211500420000c1030a10f40c0c0e80603078202c0e80044904002507403500241ea91060520008400152000c1d02650b4401d42c80340140c0314108034190740c0c48000e210907004c44140c5542c0010001045a2041049040c200401c8006515200c00070602840102c0b040c01050042c680c0c0224010200d800603074024004a48052001400840d0349201190141c1880400d404113440f07a10003100035040103422005034400015900c841c04c2226049402c2444690a00100071804c02c00c03044c03012a200c4d00914003072051048240301c1a6601c3c410603890607069000d1400041c0e0124018401c119500380c82c60f0040c04c04004050100d009525070491501c1b0724442c690a0550015800240341000c1d00000d401c0106140d0581d00d481483c0b051450f58902d100861810040d564001001a0307106e551411700362800340d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 568937392 1250 568936142 568936169
    0x6040c0c08070c0f0b0d0e0610171006030f0b0702070312050a020708072709080f0903190b010807090e0c1c060f0f050112030c120c0602030901090b0c04 67
    0x1619101c503558052001920005490080420f00700d020300c0d440c0006001c100240c44d40c3d0355040341c843d421240b2580100c101ea07040b0f601030240f042d01c900341c039a0a4502c0c10003056445034865264070310b000b240e4566400a0380c02c01d1000400d0001940399102d819008100000f80c9030f6a0324007c80e1600b49070f00000708400321181c44101301038403c10142804201c640103e448203a121079010b898254a6441300c89600039001d040c007006003c0403003010750594141000d000301450380d522840750b80501800c5c140011000301d14a0107941c0c0420280e00f1451000000c80a51846070030b240c0c282200901510b0910300c18420001048000c1b4890840b031124644040c0080c862640304000018031081c1c0440c01c1041d8028140c1c0c0480e17018401c0c1440226883c40c002040340101c000350003900c0c03050f408400d444040400c2d00000c81e4120381e0000c1c15a0340000c44010106a1042c1a202d10444c10b0300989413502c04400c10815400551198001c02d024210407402551030604041c154800d88c000e01e0b292103080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 568938642 1250 568937392 568937417
    0x1021c050c01060b03012c010609180b093c0a020c210d060b031e0c16030e0a0b16030c1106270a0623071202030a030506040c 55
    0x24801074411110a040041141c642c0c50320040b209400a80180c954074050060f0b554000103001f0b030410303180d55610685007840d89001c40240503100d051040b510f41c56040b40c9a00c0d00b03000030b98040c103422800205400350314100000b1410410601c044c3d42c4d80e00c078100802404154850880444841a22440c0314007117035543c29400d400b9410003401c0c00c1e5284a041036803011110100c41c1c0e002007000d403009081c0c42d16071100d07111094400c59030000901380400c000703003c809050801a9106800c01d10a01440380e190085200001e03c80c510110a6401d241e210440401d940150f000b40c412070103c41c00101540c0b0784484c40c03020321880702407880050000c0c00d00310000e4000c480d4030351540e01540e003006441c20303e400800c05980c018217449580c45000c0b030304a080c00f1130000451f070b158074007920100207180c180350380545100348014031085001c02c48000340c00340e90a25011500d0090340070403040900c0c180e00b07030081d589070421664140401d0500c4001a800d040a100d40300e0940d40595072404140300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 568939892 1250 568938642 568938647
    0xc04051c020d02030601062c01081302240d0b0a06020712030203071703010501110f1e07050a0f230d0215070b010b190201141b040e0901061401021c 65
    0xc611422030b044190000074401503982405100e00038010340c2c0b14807004d0300e035400d0407002c088000c001c9040c82c5810f02d507801c1100c1e40c3c401042035100f07018902c003510807005400007500860060b81c0f0410f07000d11681070140050b070000c02a01ea0411b00c82014072110465101f00801d944c0d07035001d0840184d022140820071a006e000040644c28040d005070391500c00e07140c43c0c03942c240c42e401d0000c00c00c0704c0d40000104450350b401270000011012880150510742000144036440b0940c80081440c0c403501c9d900394000c000700a115000c01440028443d58009543d84640005240f05108194111400d04281e03a00c90359101c0c010581c001d402003c2402e1600c960f07003085070459014465040740001030082d580026103a004040c003030241507010684400e400e40110181350b8040740c0b50011a4140404444140030321111190010760160036980c00720390882da00c44e4180110f0344100c1c01a41c10074207000055006500880594040c441155041d0ba594401a42d8821001c001000401882c841d005903051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 568941142 1250 568939892 568939939
    0xa170118050426130e1e06060408010912030b0303040b0a14190903050106060c11090a021306030c090f0b030a0c030204080f06012607140d0204091104050c0405 70
    0x184200800c8290880c240c810900044900794240091040003030310301004c3d03401c3c04543d07009101040c1c070b810240c9003c007200061150002c9542420290840c040307001a50b4000545000d0000c1a00800c480e2505051038514103014403500c2010a00e40242100181004011102a504104400c910300b80450b0000c1783e0600c2040445002d0300030603c140c0007202250785056031140702c550b603194070090460034410b08480655000d03e080c0000e080403030740018103100c228440c05800b15280102c2c0d50390008480c000c1d10907203107550502e01c031f400400300e03a10380c260340401450041a40c901310040e840362480184080e02c1c0c05030004807007043c000103003402c680c0d0300289400680d600d009414141e5540c002ca2030b208800c2a605d03c3c90300a40c00620201400c000715094094100f2042e2118002c05403100b51149420b004103070760b8100781e40c15041d00b0380342d068541d45c20540c0074104003c2c6040c90f04104500b1300288055074810340c00c1070b010030102076180d401d071400d40307100a1090046841042c00c8072031302c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 568942392 1250 568941142 568941151
    0x100e0409080a0f0f050301050d0f0512160c0602061905060316092f0406120905030d0b041802031b0406170c10020f100902120a080a17011805 62
    0xa844050038400225003101620400352903072943d11501e88480d40141800140c00c030f540381001001d200401142e500d4080e449842900203130803110240d218207016041000c0d926022002c0d00b40007030700c5c2c0060b0083c040401d01c101e003c0d00100031016140c040807030b00c0f0b08040d02c542c800100840764151240185a201036000306000b0122000b122002c0881c00c2c88482d075611000d50f00313680b1007290b05003081000d02c0f00b40d5442d800c1c002e9a200c040f0300f44401001d010718019441081b01e5401da8501a50b141d9002d55070054001007107035295100c00600704051f2216003c2d07076001d181014421000441c2000ea0f001101e0342c02009400782504a0f20040080302c0305030126a8066240c6800003003284404401007000a9048050325402400b5000d21070007000d004607003400c542c40644a00c028030008501c07151264040782c0046a11610b03800060303801c07280080c80c10346c0d60088458010410a4001c000c0c680c00100d51075180242d80085d10141035070324248a01010b1070103092030b03040f42c0c1c0400d03482175910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 568943642 1250 568942392 568942399
    0xd060b120a0309050123030708130606080d1d090f072c0a0503070e0c07030302040806151309020607080703051201030b070810080309120c030111040306060506030402100e 75
    0x380500c0c04151620032044016008903a01940a01255034484000303d40071492000741c1c0c80c16480c0b0301818000740310040c94803081000101c04181c141840450a42913a600850107001311501c86c41180e03262050050706101141042944034881030245081c009044d13401002e100c0d056481418041c20300380010901002c102081010f4100404000b04280703410341c00d00b881241c64112a000d02100c03c1d65070304201d03c2a480210200309140715200b08030b62140c1000406510b070fa1031860154081d0247d03400001e103a004800800110b6203107004a800404812600e4801e04040e40c00b2103400c440d07800310083d4001d0010402200402c24803802004000d01c40d10b065840c041640480d854032400a8204807030710041d503414082e83c954042e000310f4001215610321b40c0301500d4045003e030750b486000b0380c450044040d001103041d110030a110490351590050000d01800031229517450032940705000032110b1519091010071203007000003c0d03d2203942d026010001440008800781c032030700c01d0b61070207503803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 568944892 1250 568943642 568943659
    0x1b030d0c05160306050a0f0902060301091a060d0e0705100504050402030c07020d0309081510170106030c090207020109080307110111030705120702090f0403050318010f111e0403020d060b 82
    0x740710160300c00d03800150b0240d18001114100101c0d90002d94587c00b00305208142003c65000260351554126811542c1d4410300043d545010540401004200e645c019881113000c648403004a5032138000348810b8038940150344020b40c0301d00800100e0300d2100e50400c00240d0920090000e030620340e001759040100048240d0a00044d40c0c00603940030700030301041b00003614075031042018290030800510070440c041c0d1140ca89240030818071000c4c3c2c202d032184c01c07060014200c903074802ca5000e40c4800083d6400840c52040c5030349402800c0e0107035010410882c0000d00c11305001038203142c04416900c400342d00c01a05520514100011a00000c0010854202d40400c00020000500c1003040d02e15080041080b45d45401042c01045841d0300c0c0184004100d280d180200030001c0c0d0702008507548082940b038058510440b80248030f00420031011481c8400d07207480c0104800c5c00a00c005000907041f004216040102400c0c000304583c055840021f4000b45003462010000c3c4440c2c000094484003c0c08100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 568946142 1250 568944892 568944913
    0x9040207051207121d0103050406020d0c0305060a05120c060a020f1c1d0109170102070c0311210703080d020f0d0b040c020109110d03030b0a03080c1b030d0c05 70
    0x1420700c1002c0300c00d08120800010341c18200300d007560712070086100c13070b09201001410303000f2080310121010717000c1410143c2c0c0c0c40010b4100181e981c155206105e070100c0c1000000016040580140010b07102988a41c20a8a001a07a85000341c180d040d461583c1001d44003d140303100a03c0303980d82140325508154000c0e5841c03010b80800c10000301ca445034080e401890030070000c0001034080910010b140d44a43c04101c00307160543d80200006048031045440c114800040440042c02030041d01002846944880000000c0c06603a48130a07689180072284040611035511104241e04403c10038040d036038121140402c041803151001d465802d91400d00545407400c4c000f0000342952003000f0a0100c240d5030000038413079007420300c0ba040055002c2d000805c1040e4454540341c80c1080800000391144000c0d0420208050bc6a0000c0002400290004602948910300400c0c250440d81c0118005c2c402c07850502100d85043c900000300c8203014014020400403a9001c8402c0701e80c080701034919100d5000a107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 568947392 1250 568946142 568946153
    0xe0f12060903040905010911033408060312031006110a061107060b01080613180209010303080a180c0e0901060f08031c05041a090709180b060907080c09040207 70
    0x201c0c0700e9180040950b9480c3c0c24202110200d42040e0400e01d0303003034602207191320a201503e0440707400c4040d01c4403144031a041e00c2c401e003490381e0350880c12041e6650041d40c020399107500301e24010300070780c42207081d9458500c00c3e060b1070205000807140845041c10303400c0d041040301d00610401101c0d07150325084d250342c190262170b20740681d820203040310104e040000d044000c0c80000c0c860300541000910300100301c0c0c18900c0c0040d055185c00c0c401c0d500d1300c0c1d075605105ca020300815903040740899405400001a0360750ba050261540c10101d070440902c0b400c01040740d0003101c0304002c41800070381c0322002503085410078044070003000b03004004034841d650f1098007048a0381c1600b0143d006100d06801942d0341c5a00041c403450b9184030002c0004658200070511000a0b155850f0f03031180080244440c00c595a12002d1519080c1d4a90102d4405480c0c0580d40403484540c4e41c00540144c003c0c0c41066294483c1d00c00c0c0504480d08440180000d500000443d007843c0521004000d050b03001403007d0306100c502e4449 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 568948642 1250 568947392 568947403
    0x606060712210c080411030d08072a05031314010903030f0216080708070b040803040605161e120203070209040b0a0b060f0a02120a050703050d06120609020a150e0f12 73
    0x841c04034200b4010441003041b0b00038101c0392030005038042d004c11070015801510b0400d02404041c28080c0080b0b242c5001260721502031050000103603480301451003070505079143e500500020708004003d440104100c581081c16125100040e9144d40e40c045c038548040741c009a40c2c2d0039260860003981004140d51007074401c040003a00c0c000c5d000d06411403502c0081490184254009449200103010802c440040441510f080700c0590400a0742c0780d140c1d64405070325041e030000080100c4001800351483c41179009004940307601c1404030100103040000d0999030f0740210f603802580050280c001800051000403406d40001c1c9503030300840c43c400c070100007981c2e54000041d11400b0900210b003404030307941c0c104644c8071800412882107160002c00340c8010100c0c81022005401c0c8100007424410f42105a8844402001080300182c0a140ca510b800b00103448404000d9104031020301e004641113807284816a0340400d65111400c19004c0002400b803c08290103115030b210819100e03580102c1c90500c10b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 568949892 1250 568948642 568948661
    0x504030903021207151b02100c15060801060906050906120f0d05070b0f0103080d2a020f070806010518040f020d0b070306060203070807080c0c150903060606071221 72
    0x34140303031402e2912500f0060151617038078040240f0820082c040411095a28544503015500151060000403084d03440c409143c500401c1005408450f0b0100d083c141e000c10180c038114802070201c16901c60340d46007a200070b070080c1c80d4000c072924007248203482e10340310110251321510184d032600d41410808a06085603d2240300118600184000c02c22010002c2c1641c420a01da5007903e082d4155114070301c540c001ca240c00c005040c1c1d40d032070344508006250340b05020b03d82507042c5078030800000b1000a40f07844000b410310641d840703080b202184000e00441e0040c165100a800d08400500c400e101a00c1d00101030000e803103002d0030813030000143c0ca80c0703150640d1460103113105542d5800c0ca500024102c3d855540881c003150400d00150000801c00802c4580c826046a11540c0721410080c109041031083c1e01c46075071000c2c50100c0d078447c0f4450794001d07100c03105080f8141c40c1c0541c0d820050100520803083c00900c0c4580c90a520f518030380c041c00c400c8501c50198494600c030586d01a03884000c0350907842 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 568951142 1250 568949892 568949929
    0x703080f0702090f0903030105010c030302220915080c0d06092003100e030a110c09091c140706020a12050f0a0e010b0a060f020c09010308030106090501090803030a050403090302 78
    0x51a1003035080400680b504060381c41485089071070040e605d20707120f00040c0181410010345d64914010306110703405542d502840c0d20110300d520181503a040c212035869200302c1016909000307032a80c66117100d448100c2121340e800c0140050580c00000c218100423514412036401c2d0f6250010f0000c2025080c11b06205c1c0020803031101002602c404152404c002c910342e140036281400c908001d059404400e480d404c0d1524140a00591000380140341081c1407064016002160f9408006480c48001110303c481c28038644c02d544e030b54080c85030442d0f841142c1d501421401c20100a00c80026950398020250220640b5004e0318803050700e10000140c9000303a904185608601090140d440d449201d1542168548402000030580c0c00c000f14a480c8400d00c100f0043c001d16292095a2900a003d0103c01c69401006850190b1b140e291200594000707004110018400c007001044d81d5000356841429560364400860540d034580036140d000d484020301c106c003000004036000005840da040c0c220110385505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 568952392 1250 568951142 568951147
    0x1502090102190c0302062b0c0816021c020102090d1a0a0501030308040204050c0d0c0302181203076b040504050309060c1c090b0a030c020703080f 64
    0x1000924245580c0c614140c1012040d080800040380c02003e8400c07294141c0d800780c0c94900001c45007190745406403503031080000c24202c0000e10900740d0f00c401804042074039080301d2070300c60172640800c006a4541c940701581c403040080c40000e44600e40d2102103595840050314000c016008150280c045a80071520360400070ba10049000c0925049a40500500b00801c0f00b0341c9152802000104003820190055613200042135481060404469620700c4845050059113081d40004000394415200c10780151940f80054101e40380c0900c0842185021000450800c4e91726142c8240403c2d40101c0100041d50003038102004101d13000122100c0b03244025001852011342d107580c2e2485021140364480d070b10350600741820340540c1e544294106441078600042c1940d40d80f504602d9445000300c1c50398440380200c0d6504030038200183c202c21406100c040014900340044094230306c0841400794401c05181480a0000148250310120031318945104850401d640c81e1604011a03012860750f11414100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 568953642 1250 568952392 568952407
    0x170708010e030304120509150d0f02040b040302130203090327150d0c020a1e0602040b190f0305041a0c120403020c0109050a0e1501090b0c0109030e061204080d06031502 74
    0x45e0b20002d0301c5850030818a84030b681000520000c52061030f142c00101e0209040b00c2c6229941c3c00b510407c00414030031540c0701c2d202e8130606480d4109120803482603450790101412b902e030500983e4000e03900e2500850a250720041e040040b450000d041f000c01a2111104480307541c0c841409000804a00b618241c0d14500c0c03104003029100340c02c904806541c40038142030000780d0170701240302509083d01c1000c50710240c2413400030040d01c15a4030091594801040d0300d6492400348007100d42c03020740e40d02c0d106040d00003c0c0e0203178155032080700c5c0542542896036003001c0341d4103400c21080d4054050f40781d843c034001000d00042c3d4801020b4030300f0740c010303408190360180030350700000c4160103482c00316650a540381c1303040340c04500040005c05c15401c2d20040001e14600e640950102d030080c0c20617040082d1120031046c0280d00920f04540b080e000650080b00f50b03005410684100d441c8400611880c0c0100da669480e1001a41e101c0d200304d21055a880e14008089580806070030f861400c0c81c440960f96452 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 568954892 1250 568953642 568953653
    0x3020f060a05220b18031207052502010f1202040f1401090e01120b0601031407230c1b01030204030206040303021c031407230c0609241308130b0a03060b030105010504170708010e030304 81
    0x407145020200710b8ac00d486800151307802c158510a545c2c0c580c90b002180d07040c580340302000f03030145070300c9001c61307100d071740c0b070214510500500c1c1d1281d4a10a903180c1d0381d0382d5035170044034020040a104840700c26192080c1140400d4510b020240e00c0003041c140440e2615800c004223018041c2114014005003d1500004040080c06801c200c449804030842d41801d481c5c800e8139440724407060f1a8001e52070b0041c0c01010990280e0182c800540c1c00901c1e85456a1b640c0c1401380d2075000102d0040c2028001000c0591218080c0c0300714111645449056825a80c85100c25907600e803041c0c294551410880100107a0b02d01004010299080014054001c50401c801847d25003a400f042e800d10280003540000307038800020140303651001e14003034214800240c500300002c0500c1903041a03c019050220003242c800140c10080105030749a60b01088840e80d075445100c0d25000a020f0640041c004000401054998400c001d101041d0801525051386e91104080d00315015094882d0300ca81000c4104424040e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 568956142 1250 568954892 568954927
    0x105090a0e040c0902191206080d23040308040e0601120612020f1008061e060d0e06061801120204020f070b1801060e0606030403020f060a05220b1803120705 69
    0x1314400294144401c0315060140c0d080e2840445040000e030080c07901c4c0c58010754004a00404108013070750181e05491100420034141613038111803003e1030301516a9549000400c88040300d400c05c4640741003a05004005150340000342146041040c680c154400c0c00c03401e0700c1070000401d1101c044032030b400c0e02c5105000c107103038650401510500d22210100f00458000401c0759000804482088122415001015884104170781842c0c1001010540d881003151325400790800c000540111009a076543c420403030300480915804044030b98240041099104601c0b4500015100410260820802910074505a080004151034184030382c018080200000350000c050045a10028000b56040c0800580d0204026289600481e0004000340074148240300e15030403001c0050695000e41003802013007010384401e80e5035000c8074401c02e07406c080c220240078120304039690010200300f840d5141e400c4922412000c84040740e05000401038414188885a00c8500c280f020307464958071041c6002d200d00d5000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 568957392 1250 568956142 568956149
    0xc06011410260403020f0d020d030b100c080a11030d05041e0c0b091f021b060a0905102109030306050913061d070602030403171c02090105090a0e040c 66
    0x114802d5403414404040007800c071401e07145428034105076201c0c0e103000c0b071400007000000da074075004a1803ea8101da50100d20340b099210682e4050002d101c00c0020080d0040044209001040b024503c1100062140d4090310301e0b04285e0406c40d03403114602c80c81d18203551100008401241e52901040100009050400000800301038400b05041c02c40e17881c031824410358084d240390301c0d6000c14904c040b40c0c1daa0900c0c40105440d05080c81100d80d0103480079588140d00f49000c03420b1000540200d525080c004150f4644d103210303503a40341c2d04e103207000d060048030000174011008010314442c00600d001007240d00c40600441304d07140041d40c07501500b0002c04589081d0002445110b4400c20b00042c0741201e40d60410701500143c3c00500c800403440b03042100902003480c2e031082c1c00303946400500350b9000f00152049030300405c0c80310034921030000c07000703d42d12030404600880d500c00c003c59413a00c40c165002d4040e41806042c00d40c50195800005010188154070420743c3d5041d00c0104400c100003042c0c444001e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 568958642 1250 568957392 568957397
    0x309050d0b2a0a11010b0a030813090b0d03140705010518060a0b010806011206050901171509060c211017060937030302070c0f14040906020c06011410 66
    0x4a102c800411062060400308003c004009042501e001002e52081c14070040040c04203d0296507841c1c40040c541020ba440280c40c0035400c00002e2110302800351a030740c071400406001405000707035001d80e045041d503031401e035045106000150015200340700302405210080c0d102e84426a200d610365182807001054401d0041c00c1c011320398902c0e40c00c4000300c1d4000000f401c00c0b107104080c40e44594020710311640029840a84800001009061829652103580840782500d6a0103c1c0d0041c2c1e803121070f002d9841c2c0c499603000da80050b40107441075000c3c0002c0c01402c2000c01114a558001c45d1080c00c0a0310300c0790419826900c00c000191444400e01c0b01108240c001d80140d2400c420066110700e500280203101d601c039201094804428000d07111854401c00c40080d1100d819410003c0c003d400007001180c0201c106030020440707103000c03140701c0c040340c2d44002c221142084c0e41c800e000190859890072503150341c0a02042c1c030303005c4082c0f1403140603082a00b1668100180d5008100e140e08901c0c104106 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 568959892 1250 568958642 568958701
    0xa06090b1f0b0a0c1a060a0b0c030904020304080f0a09050f0d2003010e1006061106010305060103030507061d060910021204060902030309060d240608130309050d0b 72
    0x11600c04440c60801158880801143c50314070001090b500f0502c2441c0051046150441c103014a070356402c16940500c1c0160303100807040307894266403e0640704045104e092980b040c4586a9586013580003035612501c03650380c46081003000c03003580d0000c0e0880c01030580403031030140c1b0900c05820131540c5d24041503012980c44040c100191a05410240b0319021100c614600e044100542d032000d4100c0d6800a011004446200c43c001440070014941409524005184140600c0300b0140c0003407130605a030382140207483c03503910303560f406c1ea401c0c0e000c0c043c1121000d8855400c40b201d2210034140e6002030020b82c000e88070601c2c0a142c03440c2010204a100403029105022071150036403a451034680c403d9110b580020115030a00000749503018141d2190307403021001920351041d0301e65400c10078440703500d51512541c0396580130114a040f20746001e010000394a1500003646d440702290001200c2e800780c03c007040322a1310750010890316803e400b81556181c00d1442404800d00003402100d10b400a20542e001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 568961142 1250 568959892 568959931
    0x30d050313060507050c07030804051c020a230406031104110307020a0201050c0f07180e15190b04050702150109110403020d0c3204150909030309050a06090b 69
    0x15110006220182c011a56040068000d074002c00803a14038135050070440302500c4e03072481c0250540c1d01601585008240c443d4120014003507a03080c020741c6e01d50081c602e50780d4a00b002924150800c00d40e40a01600d0b01007004646581c40e039100c0c11300070758040d190034407100c1407110501050b6481066241b0300c80700d04000300902c0c00c0d03010904000003542440d0940daa46100403946142c400d0400380340e41c1c14060740b040061140780a01d11004c40221a25051088070b162a0100b9103a01e21a1800701c51b2004000001c0c010652080c3e001035098040c0c40001441a142c00201c0c0890702e0031078000016034030103905001d0300101200c00c64010514540180301403012040307066030500032840300038014110380240100300040010100003170505005903c1020700c0301107015000d940300345441e591519840e4145062400c1a0007008000100c5175698190302c1d1810f100c200007000454401e80c205641c03808440300041c0d060044486e501d00401c004510b03140300d82404101c008000d0b01000310080c0320705581 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 568962392 1250 568961142 568961161
    0x501080c120c010e0117070801050102060c120c030406091b090b0d0f17222606070e150304080405040b0603041212090f03090e0114060405060705070b0c010506030d0503 74
    0x510b1507100a00e44405031144030701c0140e0790050303400000c60b204401e107010045040c7d8480d0301c8904880c02682160143e40b1262038031201441421580c1340316002c0e000020304210954001580c009224060009202041d525070003599001c45500034241c070b058a0007005900501e00640c1d81e0306004072034400c440042e640e20b0a0078601c4c0702e1001030904134181c219500f04413080d0299074101104011000703c445884841110503820390040c4d02180b1940000d140380294007141c0748940341c410200500581e200c0b01c10030b484550000381207a9020240703411440703544400a0195000710f104040c1b441d100c40c03e202c00c102c02d44d004581003034010f0703005200300804201d604100000542035410805110b218a10b1440040c05416070060140461030181d5402c06600c2103480c070031601070302c80d13030301c21640c89586112010f0241285564004000e01051086107007002c001c1800510800c100c85803195144000403c980103100032a245940d9076040103e02d080920080e1200515031916501d18540a5030741f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 568963642 1250 568962392 568962403
    0x6020c0a09090f02060a0210050c0c0a30020a1203110304030305100f060503060f0a12032f100b030607080c07030309060509010e070e0c03010b0a0905130501080c12 72
    0x1000d50203516650b4250512584204450039580c018000560300c10302e01d44041d543d2034882c40211000d03403428002400081d0040191090300d42050090030700002152204090141310421440b190f221052070305000c44680300500344401e0003500548045201402c1c00d80300049891540c1e0240350400c0f00c0c01051140307807800c4992055140c14006a982c540c600318240c689615000b02c4c02d0075103402808110603030800e01542c8581d90455001c00c5440345441804142ca203130b485400201e0600f110103100003030140c14024000100190710120703640214910074481a51015191900c0d0030000d05001d04071414080e44040e034078160700500d11410321080c001c16100d00140a55040d00001c40c01004052080d00401045034020f03209000c035040245046009081100c0e45408500ca03003540051105114000c0c41d10605603024564196860a408004641d1011144108112032070101055555480c1384580920302140b5000601d5030516909500d840e410081e401d01c92480140c000e46c800c0303000030301c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 568964892 1250 568963642 568963649
    0x50102060f10151b0b040b100302032112150a080105060a06050a031b120e0f1e07030807080307080606190e01050d050a05150d08032212020c03060106020c0a 69
    0x1244083e9010100d08070b81c1c40180380140d05070700741c2c203420074810300410456581c011802200b00f6092901d401011a000c7e503440d10000f0741603001400114800300d00c0342002c4031007400c40c441d50740c0380010744020b00c1028034044078030410f60012880c0d84400d504010340c400020b0000d242c000c0000c2e041003000148019450320542c1704010002440f2004a132103a0000007442500f0548030324441c1c0500c001a114030071000c50780e2003140c80d0491811030103000207000c0302925201d8002d04250814559055101c40004000c402d0510900340c0c00800100060000c107981405520705649905041800400d0400c0140000d0320502c400d0209213030440a48424105008860a04054815100005a0703440c060f101009080502d03210421102c10001e4118611608011813a01ea102907a85c0421000c4107182001502002c02440002d115546001c184807010404001c0310b503050a0740d95511440c0d125690a03000141c00c480740308181c60404004203405400d0728000707841c0c070740303407800100782c018403d0710 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 568966142 1250 568964892 568964909
    0x2090f2e030807061d1b0a0b07060209060403050607020609160b0d2c15130f150923070602070513020d0605040e06100b13030201030f0b19050102060f10 67
    0x70f40d0f4020410107600070b4100741c1ea00e101240111800410742d45e01e400d1840d0241c0d804c40350b502281500ca1030000d10302420340702c3c0340302c8007400d003855a1a900000c0d081181ca15030800b108000100124070204100b500c184030b960b00130451441e00c1248182006081c00420383c03004d501d5a4144841d403165005e44241d9004018001503c0b01240284600da40c0582c07006520040100042032a015000c160042c2c610100c1000071b01ca6150316401d800ea1205503107000d4905a00351032000d001034110f000140d000360800c0700120350003c483d00c0d802e2203084005400c16888402c04000a4030340c03801c1c0400002043e40380090040ba5103803002140c0c01103419010015015800217201c5114042d541c0400083c1c00042c100b0800d0300c200f190030995419068070000c05c2e0000e5801c0014880c005201216902403400d00b21200040c0b03594010740181103490b0403044443e4613420b040c1416250110840e100c0c9401d0641790036642e141034006814103201904115000c81e038034040007181040c0d182160212080c44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 568967392 1250 568966142 568966147
    0x30317071b060b09100f351606030b030f060108100c030e070f06080906090a030f03090b0a05011505030915091c1211071113020702090f2e0308 63
    0x285418401030450303e16043d0701600303540500081e0300d0320348100401c0d610010000f612107604c400e0380798050582e0301e00342ca41c08446461011521800e030400400101e0110b01180d0302c102c44100c1c80e054410075a0441800207a403000c1680c4240342c00c0119100415412000d01015410807203440d484442c85071020740c0154844010a03012480b0341d0001c04c84103c42015998603e413500300c100340c51042e0303108040010f9502d0307010804030600840c3c0e280c000c00c5480300410717444147d55416a6440060a6050103144d900e0f0000e00125005407880d920544411600203110340c1845c100c20070444219540400f006414000c11066440000e0030424091107025655495610440514a0f05103032604086050302031509170341e005504100c102c0707107503020124203012000c14a040149180242e0a0142451200c051444250f0801c07034407040402e60f00705005440c00c2e18980101e540e90174252901c151040d6000200600540100000300f84003140c03141c4240c8100280a90005260650101801310b0000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 568968642 1250 568967392 568967447
    0x310050d200a05040f0e0123010302240703020a050d03020703090b1312050703030f052131020a06030209091503100504060504020a09020406020714040605030f0703031707 75
    0x1815890b0740104401003007841589517509010018240160b1100da5035070030102d00e5850540d5030b0041491a1806400c4030105038a181c01300301452080b2502407103444984c02c0e0740301e4420080b100900310b06010360000d000314002071900750300d08040301c2c046108040c814000d0b0000240d00400d040304070b03618038911b9500c424205140901da40d01a078400704078041c07820600801c00a0214410086a019480e081216822030388182c60314030130100c4900060021020400c004c001d44c440241e00100035045002c03044da8840d0298444407103441038500001d5044254508502e01050720710080c0540b4a02942000c1d0040301086144e83c0c00751090b4002811150303000e0480d03c0400103080d444ac00a06e082c0613a0800d81001c01c02040c0542e0168040c01c42c5140c0807400340030034003c50301110b410741d0042200b80d18000d000354101da080c0358200d501a455030400242e81c1d80c01c000404a8404080160069510354580a07180030a00d8070384001c80762880c0104801140c010025460000c0b00210482c234401c0e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 568969892 1250 568968642 568968649
    0xb2809030f050f0d0c050709020405090a020703270e0a0e03070311031201030f110d110f0d0f0804060807020c0114091201060f05010e0a1a09060d020d020310050d20 72
    0x40c5005000f20344201c0e01000310b003e40c00805c1003031541c020020364080d50384030080002a4421401100d8011401502050400c07810354028800309009290800200c0340040365440c148615003c0c162415030010410b00070500181c0e0b010343c00c0701c80c0401c10071501c148021225264014103401030306202078040740710310786c000a008882d01c80b1400750302900d42c1d603100d243c40300d90084602c20596481e180d4400c2880b1600b00b52403081d0300c0540203075040c1c541031007582c2040221ba5a03c0d035182d4201c0b0f10381060000003401180280c42241c401c000c22a151800d010000b000b14000030518004c40d4012400c0754410391b04200c00b50003030b21290201d1a912020000840c01d020103012032030002d581380280004070424021907000a0307500076a07070b13440d855044604100408402d40144450b04580d8038004a821090b000101a075210107041d00303003032209250403007041b40c0000c208030090580003c03c211003003003181391141c042c0800711420b10a41d5804d8035261049224848001003a400a0384003071559503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 568971142 1250 568969892 568969903
    0x303090c0f06020a0614040c050f0a0504050a0204031a01031a0705160f0215040e0c0a0215040311060105100215060102010e0a1a060d050307080f090a0b2809030f05 72
    0x361032040207a1550b034906000f592084904003d40d0038500c0c0c071001c654041110f100103401580c000c000ca01e40703e8100300420203000702d0004076540c00449039100152a440764025244512b1500c2001030b200c2d40b031801c02d042c654946c512000814540e0341c00510001e01403003420702c0e0f848001b82100c01c80307580d01201030b50315201c3c20020b80f0080d071180581c142081203e141740c0010910036120079131040c00e400315440d554043d501901c0380468000c00000e561030000170140c0540c04051044a01d4040e01151829040d64241d03015400030300c030682c4407006803000b080443d00409003610281da41ca07517034030070003901d0b03400c0d031208440a28040c00100b01d59038804d400001d00c5018000035242e841d095854031901440001c0d102071045030110000400070b2408a2040c0c49050700030010b5441e0241359030709c45600d07500c407044541072044184000c4502d9198180ba10006d0621010780c15070303490900d006e20324850145624043c1c0282c04240d00e0741c14660110b0307400120ba030b101f1040c901041c1c8500c2c2450411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 568972392 1250 568971142 568971149
    0xb0a050909010e100c0509010e060d0e070905090d0905011d100201020a03060b070b130c031a180703030f0c06020c12090a08060103022202211815040303090c 69
    0x4011942400390000065101e100a6a0060700300c131081200050348405580c0d09030280b0f804541c06101d0404a94040c03a00d120313050a006160a16000701c2441305011201c40e9841c0c09583e81c4a001e050046061b90300c245904051403000a0444160303e000003414845280a0709040000c0380d60301604070785034210001c0080300300401400d80c03a171030202e0090007500070340484000642400d000041c1d15001004a82c851034210072410359941e00d00c242d0303410003855107008592017001c1e0b5100101103001e44075001005510304151501c6800d040c01c8201c201d0880c0452000b080e0094002040000c0e000518120840600d05100d600c400342410400024029480720000d24020f01468032111203801004003070300740303040f166164042d8a98000c603640c1c0c002400001e400c49400840090801103c1d400140302483e00e01d009880c1c100d1a40020060202c44124117695002030400c0c011404201503050403140b0740c1800508081c11441254510307110050400f03014156a4072510061000120803071002c1d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 568973642 1250 568972392 568972399
    0xf090b18040602030603120306101b0c0b030601090e1e0901110403060606140301030c12151401050405090c010507060b030a0c03030e0a0f0b091201020d0609021213050a060b0a05 78
    0x4601c0d16050a00103540b084910340d120340500500040010f51160541c0e00038600546007005880c400542a184012500341e103000303d48114428000140408410601030055500516240d0802d800094045909038007c082c2c5075281c002003050810450312a90f500301c50701039407440c241e02d8251002e80141183c21403012034450000d404800d000441e00400100e40f0141e80c0c48080c1d17101c401018203c0d01081c0001814041b03500410444200084074200c1114012009030040340041014542281d1112404044c0d6900300001086540703000e10406501220318006058603001520000341140305255000301040d640f100c040806d602c2c02c01910112a50010b1860001c90700c908000e002144064075403031044100e00c00200d0944503c01007041103c003100e601a0402e540708080110712141d01700c5c110302940d82031010350501c1c00b0740d004100080c0480c800050751280328581200803038500034095055955010b080c04006000090100030094104a0000d084000d01000a4410501e68040c960 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 568974892 1250 568973642 568973689
    0x10f090b0c1509010c1d060f04080f0c0402041413020403020d08040306050a090c0510110106062319050c070b0304060f05150303030610050c0313030515010f090b 71
    0x7038801d00080140600666100c0c400d900d540c3c4001041c2641c5644012034001844951200002e40500c501c014072294010842800e02070844500303910754000e075005d01c500c0c0e4803504001110240c113202c41d806043c800c2d0707400c0d45898100646400344e6440042501e010315190b118205801e0040d030306840c041c5900408140c0310b8039450404a2241d0450b010a443d15441c02c0040b0790030490030b22031000c11550101c2c04001081c078200030002035921600201c030a1040509440da01c948081c03041e2000b5203801c0c1c4074101d81c90441540c443d04924250240d0b43c000348104050b0001080301c0d01c1d074285c0310b00c0600e445075440c0310108220341480324982c0560100f101c04000e0004100c2e06402c04200103001c03002c108002c3da40d008007181c0440180400c00e405400c10000718500342040402181c103080e02c1d04000703241c1514041c40b2880d43c0d00400c201c000c030003078064082c410420288400382c003040d0806030040840d41482c0744098015000c0c41800703001555130700c004803e500c8403498040d605100710641030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 568976142 1250 568974892 568974907
    0x3230307051c1107021c11090711010501090515090f0c031e010b0a080903091e040605031b0301051e0a0b0f280603020703140310080708100b060711010f090b 69
    0x1264010080807845034030040213031891005107034800f040d0b540d00005000481f228001c24440a901d015001100f007102c070003044894100309000301802816000c01c000303510700d01001c04036001a030785070005118114441c240b090300030002400903001580045503542d00c2d11400070200031010400705036000034207464000140d403d00c43c000780a60004584035406260ba070000d00d00d0700c83c4100780c917a951007809410034800202c0072009800038000c01802c0026025181d00019141403210400c0c0500003110030360f03003c05405c00f8003400b40c0013150050003405400b2018a5126100001800350b001183d0b0341c2d80d25850340d030325074000b0030080348044c2071440310800400020a01c0400e0301010700174006001c0000551600c24802c860f01d20381c140d130f5030380d080c0240500030411a6002409246500070000710105a044082c070500e07000340758460007010006003c25001050350020722602e84904000d00240012800820311410410340910744a1000d0f4400e00040d40c0070740b0180c1082445030400328042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 568977392 1250 568976142 568976171
    0x41a0405060a0e040b1009060b120a0e01020d1a0604081207051006060c0201270e041b0608190917070309080609010b09060d030c08070c05150703230307051c 69
    0xd0b4014049000b1300c046c940e49031070202c0161041ea00c80c0661012041103001c21b5015641400380e00100f90340808201e5051007038034603081ea009241004021a1366031001c18109141d581c0c0740044600940314141481d141520490b2507041484e10014070320b8002542c0020801c00b800400300c4804140001c0021503180e0300000d181d0500c404003203002c41c6080c09510b01d10003200c124545071300b0703109002c1c1e050141010341000078a0800f130412a00d85d2142d41e0310450000b41080a00003a0010342d481e00381520701884c1d01032801411100c00c0100c0c9240095240115800b02200e800e0f1103940103855607030341da06107400c0310300c03003482d622885081c000e8205218820106411122002000300c510810342e455440c03c00400000c07440c001070118403162402c800060324031019090950142c0640300d2029a00d074041000104481c0420100da0000140042055008000c500c451120b000f48903450782c10080c6004907500c0040c100205012011400822b401526580c01040b0310a014050010001083c141c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 568978642 1250 568977392 568977413
    0x206040e04020f03010608062e0b1216050703050a17010807060f02011505040e0304080a030915050c0a0308060d020a0314210a081005120f01050105041a0405060a0e04 73
    0x201c1c0300d6250704030f5500d01c1c1c0c50b0501410065a00d18000b429280e120b84c801240c2061001c42c4a10300c4c4000404031584980141007503200410014202560b6080003000b154186000204001888050600450206503001c401d03114420303414140150f03200c500c2c40381502c070500e802e207102501c007058000110310500041802c4080351500e0300c800c0903403100c2480580c00d841500000302040c5241000c00c11031407800e0340010340869460300035030b4601911030f50004e040c04a007502c190007048947c0f004004541d2409a0080502d4071440c01608100104505589800300071768050708200c02e1401042d8607070341b0000c18064140d0300a0002c0f55844d6245005030b119822000740e0203650203840548040480801c003403008020300182c8807441c0c250b408000743d031410f00142c00002109262000425141c03106181d020302010440c0080080214076465a401d40c3d8058106900031410903c00c5e95091a2201d4800500501220045001d6407100c0100b24114145d0b03000110441601c8144414404502c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 568979892 1250 568978642 568978651
    0x2060d090f0b0601020703021e12030c010b031605100c05030c1b13090f031101020f0c1e070609231008040308061507060209010306051e0a0f03110607030c0206040e 72
    0x119180b5545800c016619140e480c4400383d0010910f01820300041c0760911480b810f644000c001c42e01501403020410300d582c0010a15124580d502c2c01840314038502002003400c8090341c2c282c80090181020003003658040841c401d5030a1003407004514040240c144140d40e01e01000d1800c858107010405c000407044070804000c0741c080c441d841882d007188806401000c04040c0c105582010b000126501141c4007c05c040744492039540c01d08c01c005c52009140020241c00038560001c0060000694441d101611802c0d000c50099024a10070001035801256510442c0c082c5841d1a02498500050f800804500000c1d95444009500302009407900107102d280114000d50f43c44409607690400e02058400c0842c190001c00300c01d00541000480603002004102018074000c0b13501c590f544c0120b01603020140806c80850b80d510340a080a08288e00d8960040c0035001d828015145561218844411440a000c3c0079000c001005030030b05000e540403c07091540504620358460b07882c0b69100b4032150696 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 568981142 1250 568979892 568979903
    0x301290103051645050301142403071d041b0e040f03020f0d09061b08190504031502030f07020609061f0305010603061406010f0f0c02060d090f 63
    0x102107900c500c3c80940b4120019000e03126030080000c40070007800548903070701303c0800414100c591080e01d245603d5403900740e510b508000003051803c1000f01820b44020088806610a032102004000032500f1150007480d408411550400d1031000701003401c0440c240c000c04140c03004100c0c4a2400300c02c00003050300c03a5014401c0100e00c0380c9149215007030909148694082102d082d800704000c188500b013000740c641c0c4280126040541c501e1b02c054181039816000f2004903000c102c00f0807106802c09011810955543c41e03070400303410b5650b0703000d5980c01aa8800c035002510306654074081c1c2d00800483e005140c00c641030124012200b101140a50b004440030f090258455022070005400010154061820000503200680e61800711140018400030203080d0800b6202000001c201c0a2051401440c024180400c203038503a441c0000c007511003e0902410401c120781038085082c0c0c40290b0b503408003014a805142400c1d24000030b900c5024088050546510302064401005140c603896030b611441030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 568982392 1250 568981142 568981151
    0x1110903070b0a0f0813020409120e0406060c0b0c04180603031403060d0f0201050d020a031a01091203031503060c120506040b030703020f030f0604230d120207020301290103 76
    0x403042006035009400402d00464104e4540c100303080e004502031a485113078443e081c2102501900080c00b619079045050b0b441d405404c5440c021070340e01140c0c00c11003c2c03064405001080c50706000608448181e00301900141104012540180070403003114028034500d030044d1402108061000010f10191204074040350300142454803590100e0305891180c1c00003070a1180409540d103034281e1840c40c14004a04100081142030000d011920240024401da83c0c0c0014001405403405880c610f01d0304000e505220b844136040201c030000941c102011549440c0c0440c03106200360208484c1c882c5608000e08050a04980b0441d180c1e002082c0040c0320b14010080c40b15480d8401480101c50200d80040c1c1c054019040c24000f5051442102d481c02e10b01404480200c0743c2c16104034240b440c2903c0446030205010030892400b8490b10020040c01c4105015051f05c0000b0380001e00f050741c050000070503280e00451020250740d003c2d4003801440038029000c0c009031200110414990701144d90301c2d0b0200703180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 568983642 1250 568982392 568982399
    0x109121107050a0b090d15060816030206031603090506040308041a16050c07030209090703260a08040f12020708010608150402010507170403060b01030e0a0b060913050111090307 78
    0x1510000b00d890140000b00c15a090032500b01c4c4651002c4011a0440e180034155000224907071904000005d42920020b505410500034078102038240b61002540022008140b016980703040440780c11115500507600b50740288602a4090a01c2c080040c15030b0040c82c0070001410307081940644200e100340300382542e81c076014482d604074000a036070100c5610f8510003070516083c0654001c203c03400d07521044441d803680e01d50015180e444200e41d00c3ca203d4210100800400c000c60b011400412400a0b0388007844e050305207298901d0103034841c0c07075007004214008101408900180500201d401c407024160281c2007a10183d0b54082d81c0c07203030030391561030582e0006080d070000c03c0d01c040002081c100d250741c3e600d55130011250380d0400b010039100101c401544000309071040c0003c2c0019841000e01240b922100130001d0200c0b55a11508a896003000b4001400900d44070003090703120701d00302c848060a440c0d100702e035001d0070035040c0b0013043c642c0303454101e04008220f0b402504444c6000c4080324506500c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 568984892 1250 568983642 568983677
    0x724030c0f0f1d030609150f0408090f04020903061303020606011809200d060f120f0303050c0d06030605060901090c1409010302071205071130030c010912 68
    0x212103a00107100782014110311841000c4003c454182040460300402c0703007200003420100300343c409058035440070300e100c480c000342e84182641c810449004084d9528042d114461a4818606600e100d2030304d102e1603d100740d5036079066804000c4050119141c618200c183d0700032443d4001810303005846000300240e4203603c0f078459003401c10180782c41e2141840c039203660300c4050064141ca03101444074403150a292503184401030051134904884c0454074070714200311130700d945800780c0060000c540604050804200c82c0c09403a2071301c2c3e5140c0760000b0340340da4450340541c040c000c0086c2c4804160410314000184003054000d0760040c8400c0700d42600302e903a42e8240d081152255034105000ca41441d036221184589000985841c0350107040145c548074160391815030340441c2340d148102040003c2121814094a0b0002d948152010b881c108180b005500c280c0c01030151501c0c0200038440254055888103000380181d448202030f210003807208aa151030440da04103805240d44000540c0164840c07413181 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 568986142 1250 568984892 568984907
    0x3041503060f17160501020a20220b06040501050a1d060408070503070806061f0905060706022511040b180115020f03030105090f071e08070f030218010509030724030c 73
    0x170016002000b11951030f07542e0006420b20310010040c0440701c3c134040c080c0c0340c5404080000007800c0c00040141240006040403c50f138440c45041d010343c03014041400f075640c1007811203000040358104070503060082c0d1760069890103039112158001c6008035001410340000914481920021002e4030300d00740d00c0d03540465039850b0844045501515600c03c0c4d80c82d00307003115030000d054074407494501001621800419800e601042c01100c5580d0700040320307610780e01e140a5480c0744078049691103009500d69100c11080504190602e48181e9841114942c0d6907103122461003000b120305844005903a4484480c2e0ba908030f400d1144003d80217515004114010100499040e220014000d0005450704040c80100100082c14441170113025011052061140d0500380d000c0b1619070394120f054502500014400d1a05403104070502d40113000600c1810314030300f0710211441080c07030102c0c3c6900162002a140c038003280d22103007884054003103010480743c513031101c000d4141d050786041c025070400c0502161001c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 568987392 1250 568986142 568986149
    0x60f080c041403150f010303030b060702030706140405120a0b071e140c011b1220030c0f0a1215060203031b091005030a0e0309010203041503060f1716 66
    0x8010400040c400030b4030141d00c50762820009402c54544800d10800c0340d4600900342e0b00c140c69030300307041c00400c200b41c2c1c54040c541c0c03240310a8445078200302150303010a6946942e8054003080c0111070340b02c450401451801d81c0e00400004204c0c21080c0680f26409440748a60742e070548040c80a01c000480c00c1d80940032a0700810764070b12205402850007802114280e150003d070a4010340e0030040c465103a00b0074000e1b10000b00351031440031000401c060b0f010304a0080f174a0140d0702e050400d48000b07140240d403c010300c9041403003031409660343d44903412035015104508668178103076804103980300c480b584407800401c00310702504100030b120b0380080051181d042038441c00c00140c0c0100f0006260540320070231104840130b004006400c212144000400d64520211140001078001c030800841c0704460040901422491003d5803801c40c141c0c0000303440780701d18061040b44510711034103036015500c80d90007040281038851150361800c0d240ca5040141d0001c000c01081c4500c03031403c80290700b40c21180c400044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 568988642 1250 568987392 568987411
    0x20c0304030807060b0607141005100915031b0e0106030b0904020f12010f0902010305060f01020705060c070e07030203160905010f120f020304060b0a0f0f030605091e07060f08 77
    0x2003034615501c80da07881c0c2c00004101c400c0c0c1e440720088a0181c82d00005410803520031904c3c1a44446682c001605d0002d81400f440c440c242008180a06104044141d000380c074000307c0003103041900101c08180e4104940e20080440e090001e4045241c0c50172402c01054440c000007886250741e9a61b8200d06850900441e9a44000d82c400030074014601352070003001d03000024100e10b0b1002550010f00e82110b4045601141c15501d074107500c4215a81449a194810ba00b00c0d04001041c240d840000e40da1181c0b80505400f80310005000100c1c000d040001c00010211140e0740d8035580360101008000e03420940c0e80d4003690b400c040d0000203c5001e10031910545d40180e4138a51200d18244d011070b240e80540f4203100344140d0310300c2e00c602c050200c2c0c0021441503001300400300e0340724001400c1c850003c81c150700080407403000c208107001c83e040342880201140e8010030081075135110306d02010b0038030064440b04403403824400e4240d19000c034003192681c1103030801d444081c0d81000c2d554064804041c00c0b103407280c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 568989892 1250 568988642 568988647
    0x1d09060106080702011d010c02070905010b1615051626070f050c01090b04260313031b051629070317010902030411040204080a0f050c030a1b09020c03 66
    0x1214442d206050344000c0510004c02e08490b8407510860b800c0d007000c05245d03941d45502450300d1264040203c0401040c0036141000698905800e42c12035020f0900340340e8004820951460902803100210036604070000d00401071030508042c0c040d4100d2458003040d020070b2a030500c40c40718860240114400b020442c01e81c1d003040d03a0b0040202d4142c0c040103031060600c070007807007450b42c100030902c10004041c0c0320784c42410241c01d00b0300704508802c03910310301e201600d192000e981140101d8141541c5c1c1200203004000090006480c0c150359080c0000495681d205813050113a0a00c0400507020301e149442c80b0148a10684640e014003540c1d114145c1500d0103100c1900092030108108000c1c13051034081e103032210700e9440c000c103101100340d02030b400407002c15004001d12090200a694110030b85038219411442c151410224039100d984040e0050080c001c2241c007c414403500380b007042d04205000f41034078035549541c07034195103035131005220f00090000c044e004141854244211a251080d00780150b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 568991142 1250 568989892 568989899
    0x215030f0f0403020708030711040e21090a090e0102030435070c0b040f081204030b0f06030f100e060921030910090309150c020901090c090302100305011d090601 71
    0x80e084034042c1048045205400c00003400070780610240a03007510420100840c00710307541c1000156220020907020540041000b00080c070800320294241c3c0424010b45a25800f800e80024480056903010045030f6040094403c81809c065008500c5148a2040301142c40541001d140e08032220690403e050740303a040401b52150b5140d0082c00c0c4d0540305043d4183c18545a400344071070f6804ca03a00c06100c41101c1d000c1808803850034000100400c070305c00a1582040d185450f08040301c00c010b4900e0001c0307a601d802194140d1001d200201c054400c160807a4500c06404040d0002001d880c00243c000e400b89101240030150089207204110000342d0708104440114210fa500d540d0014103030310b40347d214090172080e8104030740c060400c10901a072074004400f481d084401d407109074441800b13400c01039001c018030010703500d002c2c4d40d03410b50f2059074002640015120080d9590320030740d04080d500141100c40410040c0d0725420860603140152058034044c010302c40c1540030650243c900350310301e030030080052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 568992392 1250 568991142 568991161
    0x1519090507140d020613050901090504081602040b0a030516080312010608060d0b090c1002010212010306020a0203090a0b09100c030f1206170f01060b0901021906110c0a0215030f 78
    0x32002400041104038030070b00550010300654006d2030308203034007218018100a10f19150b500c4a00412840105214030701c0e00d03540d4103640d40700303070114203060310700700d0a0000664556a10481e030004c130140c8a1a0550f40340e00306640e03075030380d00055100c1034414030001003071802010080d5400c40d4200d80001c0c6c3e4a9082c100c090303d00040050880350450041c04403030010506421649010340c07403803406440003134001010712a850341c0e84074003402503a004215225640010100d050304580e0840b2005823502000b000c105e003144100c0c1d072065440400d0301d07004034a5642c2280100480e210880307980712107603540b85082d80c443c010a040540030982e03550711048664011059481c1d00d4454400000312561101411300d00f0100d40c2c0300c09000d941c84000d01d10b106000c01d00c55803000d0000e40d600907080850707120000350388200c001c40c10901480c6201248040060310b4114140c00a00c1030622501c80209410040d503070006028241d1142a001800203140304094040724003440c250182410a540c820000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 568993642 1250 568992392 568992419
    0x10f050405041d0d030204090c05090f0108100b040b0309011805060c030a090609050f100b030709020714030301030f03020105060109030b0a090f02041503020414090d110c031519090507 81
    0x600c10003030684049583c480304240501c882c50710140d240103845500301508101191030001460341031010410a20358142e44134a40311029507000d1034045022703a0ac101407005003c0450340500340d200720218002c00e0b000344070700285100e15090742c001c20180c0b041c0c3c00311807480d0780e201c40090042d801140c0819188007803c002140c0c481d074101d0010403a07510668800c012110071082c140d58940120b1034850003c1805c0c0710b11581c04030103040c184501111140080d0b01c840c00381c4124089281c0c001a07880800140300c41241041c1d5032034041c1ca44960356070418040b4000b42d05401c0b8019444e0100289503980607242d200b01f42c0f60081d0801649035140a140001080900305c1518a028034440210041c2d0f114001c2496a003040440080740034518418401507a640000d50020040c0100070801c45101c0081c024000070741c5480d01000c100c41604065042424a110380c6406015021500300d05035800803074580610382c070311440545403160321a008111410001c0041c181d40100383c0822000c00389445 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 568994892 1250 568993642 568993661
    0x809160e13020603070509120106060e01050904061a03011517040f030507050615030d0c02330a02060f06100f031e18050d080408040e040c082a010f05040504 69
    0x6901c00500c6081e0005507154004032801400200700048a146034103000100c0320002091100a1000c03e040040103028841c2000c0c02034100000801d912a50759996003150300201100c64104100481007070503501c0d01d034424003400f446401e03d0315001d0711542c0300d4244011800c605402d02031154036103568004004021400540400000303104443c0450301c140182030080c840c0080d280341e00c0c80c60f0800e25060040e13180c2c92005101c404131910000d038607820f100b502c514500d0208000c04420f0442c004054015481907490280350100302d145010380c0000350107015046540303080350340307503250340401860361104200100021203402c05090110f009070400600803000210407031310416810016011241e820003851000310b800312001d0305200041c084c940c0120901e260541f150b2800d51116080745c4150300c14941090101c80c00113050119662420020b0000310f404c0c0c0c1c45403804004a1900c49100e41c2075001950044d1541921540c0a11043d030607041c52a02c0710340c10549007104000040030041d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 568996142 1250 568994892 568994911
    0x703050c010c0606031b0f090e030d050c04081203070201061212030504080f0d0204050a090b06030103080309031207020d0905030c01200a08040303050301180b060403120e10020a030809160e 83
    0x30000300008103000e401c20119242d006e1515019484d001d184501c4841580c851100c10b843d105510308031803008000c40347d001240b036602040c40d4403203c1104800780302d6603200103454081c0241e09070100e4030302c00045000b2074499000b44207543e11003169048a560310f060083c5851561a01c0260540c007a4209a90160040004509022400c070540b6081c0d0311074a44078405583c0041c0611003450088802406094480410040c00704100041005480180000781a600c030200c001151100308008a9004680c03049110040342400c80000c0e641d084036042034008074000c030704082081d060001c0c070b010240c14160b5554210480012480401b2460a0910712050007204840c0020480e03c0d001440214030942c3c903d0350369803404084c00c10b0418050a942c6055041ca80b01c0c51140e5160410340c0e05803031b0411f182100700404440d040d180c200050034100c0e000321f011044018901c2d004510900701034000d840e100c1c1d069440054064590768024080082d50301c038040300b80700c06409506174981c04007142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 568997392 1250 568996142 568996151
    0x6060819020316050a031506050d030305010e0f1b0a030605030a031707030509150c130b090a080307050d0f050c1b0a0801020c1b01051209100507020703050c010c06 72
    0x2150aa824000c10584401580602940030421800c003002140401c4112560510409041c000000c2c9940d0305484054808030741607010000c0c5d4041e0ba0b1264006190084c404c40c01c40200c1e14001c5c000d132209208224a05400c203001800484040c1200c03403242482519040200840c0d2408224540107015801d08042c1d035580d003c901c1351420086032000d230f4000e440d403292050240e245081101c20040c54101090700b04414001224400524112450284050440182d5900d0320301c0c010780c0209400d03405001c03166200054a050321800800352030b8410354104602c0c544442c02595a8410b03114002d02d1a403007062441200c520400700b0300c40072111454034602e003020803109949444510740c4907440d50301d07a041c0e40c414035103403104004009007584002941000017400c040c1da11910a82482c21030743e0617200360720304580e00c074000301d40c50104071443d0340111341000d4414a554660107440c00c4803003803801022808850000511f501240c1d400740041201030481f6004451101d410103048417155281e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 568998642 1250 568997392 568997399
    0xf0b040204030501050406060f08070b0a03020904090f1e020f12010912020105090607090e0708150d0605091209090c180616170a090509340e0a060801120606 69
    0x890008000640c0201c002258030700300790508400325201a0300001510304845020040c00c500440c0c0300084031021880300e80c541c800c0443c00d502030700c51006629881343c500818542006000703c1812101402146900504104550f40918105200001947c0281c0707900381c441c0750346011900300f0060100c400003c950340429a0f60200001c140ca080540580d4580d010040c441000304419a0701150910380102c50724a1726001c000744400c01f40101c42040342d440e0025952082c2000e001b140e03040d01400c0414801d9040c2001801880c0c03e490050301400b98801d081300b684039060541c1d205d2140188151003c0c2c4810402001580c4000581072184020180300401c550b03500002c1c0000d5401904182c821510358502403580303003a0a4601c01c2009000e02c40381200a62080c20305040e50015103900031075840d00d29004080009108402c8008046604200d4261030325070341041c0e6182240d1242c01026040e10f040108500d4580503900008521070010400c20150600124a250240b907000404a45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 568999892 1250 568998642 568998649
    0xa0f110c0f040b03550c0b0a03150e0103080a0c0c0b0f0705010f1e110f0724110d020708070b0a0e0c0102061e0c04090c08010303030c0c150f0b 63
    0x80700a07020009050110007510402e050200003170003540c113110301015010b610540300300c07001c09022403610724080c19228010005220000b602802c0350350422900c0d108090310080c00b03403410801c0e000c4c0c1002580380000c0c41404414145060341e0303000c0000d43c1000340c840e0741107030101c400e990161124080d08030001030200300c0c480284000c550800d602c6943e900c003400d1041c252450755200c881e08610f40340c44c1c114041c1c0b5890340c40015032141c9601180c0c001070000110a18000d004602d407488500240d00010480c03006590158000d1005401c2d910030040c501c9541120114900d01c0c0024800304a51061101168000d290743c41c406c0c100541000c10701c0d22482034505042740c40d100d41030780e11002a9008007041100d20745055091000301014a4010800d9010100d03001c00381d04a01444001b0030242800c6105480160520a204000807001204010401d00b020310007600407907c2c0000d401202d51081c000c100754544c00c1849c544102c40c103c440b48008050b118500c004966030380d20007611030355 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 569001142 1250 568999892 568999903
    0x32505152517090d0804120306030203030d09050105010b0717030720010507080117121b191106030f06100908010606020106090e03120c030702070f03080a0f110c0f040b03 75
    0x10752955a08003a80c00e5581d5480e0801028080c0c0322141e21000c02030458035401079000758000e510a8000b400000c1001050300501002c0e0030017903050102044810840038258002c0840601403802403180ba666403a41002c18410000043d103d81cac0a5240c00c1d0703040c4134a40c0210b0b004500c43c0b07426002c030340c00100b01d1001e0840001c18541965100c00a004110754030450203400341080450204150343c080c4d0080d940d80e083c8801c10403042d24007046503d02d4102206805106410b540c05980c24251000008448841c1c8080c0460700031110504a05842c01c000058900c542c4101c00d964149850382c90800c204690140c5820b000c0005550700071441c0042030051600410307182c0c0001c0b402a007048c4030780054503040030503604198424040100c043d00200c50721500030304a14141f90b40e136151164101e041c1401038000441040c01d0035000020020384100811484400d0756032a00e10080000d030441b040820104402c1046e4840021348200717242c824414806050024400141080c000c0046030800f03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 569002392 1250 569001142 569001211
    0x7050a060804060605010212071b0b12091902090103141f020c0c030307030c02060a0306080115031515211e0302100b0102060c03130b0903250515 64
    0x700d01400340410841c0c2402500c000e00000d0000e024032085010701e4202d103024021019044204070700c0360354070160f01d60f213001010340660303861940d4070200b80b46001e004900503517580700584110300c0d00010070440002107003a85030380107040307a030346920f107440d0820928041441d00c0042d002e0300c040102140362140d03101d121140f80020140e1240403608180c0d04101b026102c0138000d4004110030400203a0000102c4092a4103e50342601c07030f281010304074024620b82c0c020400541c03070001c80c1050141315035150b0040382e116903540d1000050320150042903800d0602100800d42c140001807003008045203441d95240c031500c91103d00c1c00c3c015140c00c005189017910811404070705c21208014190706000c40c50b00034050000a111101c400030000790741d4400107121100310100070003c1144480314009506205030004401001c608064407415240c0d40804510341d000d00c8903a06110703103d00015503180c1841c0e003080150005042d5a514108a110000d00101808000c0ca082e8480e140b00d01c540040700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 569003642 1250 569002392 569002397
    0xe0609060a0210050f0601020f03041802160512270a060e03160e0f01080d020c0d0f0b0702100e160e07030902090702150106080105030327060d09121b0b070207050a06 73
    0x21b091000c00642001008610382405810401c0280110b020031610721007405001040142d0360348641000e00444012020010071341d010b0002810380100c0fa090141550700c0025002a4500b031500b0003500301c641c0002c0d0400c0d00107040c91002c00110340111440c641605001d001c2e140c1410410f20090512609504040108580d02c01070042c001070f030380004c07405440b02300700030014128101400b030f6840c0d1490444500c1410402080400c120f80350482d040f01640c8005240028200b080f400703510740c014106504800c624102d200d460001c0c002500d0540001c2241c1a21041428030308a9805020010314602c00e250300c03042403030016115428864132902c1e042c4c1c05402c41c2121384030b8800140d141a8400310070480c0020042c804d503a0003004a0300d178400300c08100c5048500206c10f01d00000050300005a01c0600030803c0d03400c15100707801a00c41148500501d5079258010801600e802214604204802c2150302842c400100d8000000360407003201d00480c6e6086a9840010b00360000c0f41c0c120000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 569004892 1250 569003642 569003671
    0x41404050601050f031b0310020712180f030314090d03120f02031b07150501171002040807030b100803031302100215190e1c0f0e0609060a021005 64
    0x9210040c071045000d05000c480c22401c03220401c0c0041e1b901c203040b0040b84c0744140c5903401c12109650030022541d10014112080d520360300c15080140485c460742e013040380030504102c50300c106216440c845d0810b5541240f4503845850031038800302c1c0c295020300034201c3c01c54030402000b03429603250301e80d190700c41d4465900d070000c813009010104d080e991080700000f2103034014401d0000d55001f6004095149501c18a01c648501041c00d041c010901010344607410366107010000310381c00c2c1000140c41050020301c3e04031f4000480412720700c8224407aa10505480d500803000500004a00313012054102032841c8814115503221800c0c582103038030544026801c00c40381d03101601107082c240000c0900c800d89002038800c40c0c08440b02589071203030040c00341c54080c1020308410011b001d2070b0311103d803441e20070040707943e020001950010100c1107820300ca4040b520350740b960610140302d00020001003401418103820900741c0e4092040d140c110780d00500079409900580380076010540b00b1240708501c403120020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 569006142 1250 569004892 569004901
    0x140a0203160b042a050d02011701030b071803080405040c1e03060f05030c0a030213090b040b09160b0405010e1c030c021309031b02120f030d050609040203150907050414 74
    0xe06020000018413080e41d5000d00c0c4120444c5040038000440300c040c5c07017001702c914040c401220148042e1000c00303402e01c2004000b105200c10700e0308241c031445030f6448525450b032410009030510038041c403004000ca20104000c1c400c50406401c0301020360301c02e04140910030140001901a20043c00140f400682d81d808100080c2274005c00030001030105034080d05103104440086500c400403400041e00a600e201c0280c41160700e103500280c80da5400110703c010b6410b1a06c1c00d855200020748030103403640300d40ca015600005443d03020100702e4000400080c42e142c074000042d6101c40c20307907a120713521131017040804003000322451480c0c092030f1007039841c009040960701c1000390003480b40c000c0c805010300c1c16200000290308002400004100c404043e42140c6c02880054841026815450f0403400303080c0c1c50046084001003c1c0961001c070322414440c594521040c0440b0480c2190040e41c103511800300b00f1441040c590300c0319040b0380e4103401e86555503140d40105041e200e00e0421b44120001810801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 569007392 1250 569006142 569006153
    0x603130230010b1203030721090302100c03061203121103090c130b0d02150405060c0f06070f050d050717100e06040207111009081209041b140a0203160b04 68
    0x100900c3c804803585258a1520719020f6035130b0000404020078000014140c184c60300404028400e0040d03039000610080c88035160094490420345c07820400c0500313040300880094064060b400c1518050341c01d480038040039460441e032f82d552410748508142e03070b900445840c0403401c20040d0b00c44d42d42c1c800140110840442840000c1d24903a4040701c0301c1e450b261124140ba074810424a071001d40458120083e40080e54a011640c4140d912103070740280e00103440c1d2107210002c140d425191002c98161765a0703942c0d09000b504e120070580d000000003842004004101d1400b0f51201d50000310503d0700700c2c0501800c111040d42000180d640b481c41140401080128083c0f40c04800ea2004007a242982002e4540da5007040074030740c2d5840c00b4411080020301d1111203104215110003009944100d81e21540400003043c100d40c000c201c1c840c09203042c40843c1048400b03155a05036542407c0c0e48580c98061030891211050304040d50807021400100703c44882c030702606e003010140c0c5004800780764140c100351806 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 569008642 1250 569007392 569007401
    0x2040501031a0a09050706110c0d030207032312030705070501060e0133050f16080405042f03090a0b09010c0f091202060a030902060c01051006030902060313023001 72
    0x260040c1400e200680c00096070100e400004c54407d41000035182540103015400c0084103c0e0703170741e00a00c201020740c050540c00146002124081e200103403c009418090001010300701c0181012640b0207801070014200c0340c0300550740480030345400d504064880d41e81c24207461a0b03a10440021920a00600c405003031f02107040d014010400c018101c1c000d20041d0b10054482e08031410307050003400300d464940c241085080f10a040400042c042c140490b91601c6d40c141d401c075001300390156280030030400101e11280c1e820b515480704080130791072100150014a0080c1d20042020800d0701920942500080c2050b02c0075000303000050012130030422901d002083c640c05501c80c2e030104442040d040184c8140306002c00842ca4041d2007103552817010160540c068461810002d401c941d0008155685c3d007010340c0401d0044c60f40d1041260306030340e40d1074100d040d2906054046c0d4071000400c08038075540b005c60316041e034aa2025000511200340b10551280c3c1c4501c1103140007404000300c41c900c034000d07000e229 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 569009892 1250 569008642 569008651
    0x405010e120c0613030203040f24050c060a0f0e010f0b0f040603030c030f1e0c020307050a060e120f01020f040e01050d0b1f08032b200a050702040501031a 68
    0x2607141042e04031071245070343d04030141013003240004201031503090520900403607006c0c1c110000c0341c4e510036035a0b22480391404c2c0070300030400240070285100d07490b040c4514100d440703490340e030b0008144580b1946034980050840c082c0f001003150780c41c07040034520b81c004c0c0940d2032017698440700002d00d000c50106001c02400001d00381c502c500d14240060002070b13041114070000303c0c0c1500c0c00c0400b43c1d040250594401031524542040541900300c0800000d07408581c54401d076100354207560086a84005100f51212784d40078000c041103070402008602d045c045038100300d0800440c2220745207020600b50790308aa1000e0b540c00b140510001d004d00c581820355112034010703c41070792080440042901e4060710608042c0103940b8040610504c0700040142c10103c00281201c1c90940350313554421100000080307540030a2451006116100b403003858603601c65412441c2440c401d05040d08021020780704250322440000c0144201480010701580300c2c0e2154a010307501c605400e204c4507541803918540d1000062 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 569011142 1250 569009892 569009923
    0x6110c13090209060306130b070309051f2f071119081c1d030114010b0d0e010504050c10020307080c010203010e0109090302100b0d0602030f010e0907140d060f02030405010e 76
    0x800e2100c464440520703c00707441d4020601c0c2c008d80d202d012048002c1c018540c0c0181c014400c030013a41c40c04150140032402403c804580130405500004404403071440d00d003440304503400301c410a000260701c1d01c00003002814407803c280d400c4200442c00250314080483c103081d0200202100901400104101d081d00160400100b28405a0311070001490003520340d400500070500310384402040d840c00d4100c60f40c08a000705000d821582c58031150703141500210500c11001f4102052118a5039040c440e4500480c1c110018084102650b400e010300e01c0c5021151a003184802c100b8030000c1b9001c0b401a2010384a04000546e881d498004986d01103072068200701440c1c1d20b04680140040c0e00001d94038100c006007400030642100c2000045da02c4806d4a10262201340004204016070a42c81d046038181e88100300e282d0225100c204800d55200014010001e20242985949410b4a001c051112080f40f14820200c1c617a4003c0074140166001900c040702c440c0c3d1291a10885480240038002407802d00c0c3c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 569012392 1250 569011142 569011153
    0x5010905090f01030227070819060501050906180a1502010605010f080f0c041802030f070e0a0b030c07060608010227032d030705160e04080406110c130902090603 71
    0x442c02034020003062100912940b10b558081c4400b184984006003c107502070708007041840c00880140c00c58100316601014080c2c0312180b08046015480790809503401030b9105410701465600340082a44040100c000c10100e00300040b020756546681c0f9005001030b01400c00344510079503000313425522250003150500c00d0781070040c1c003020707441910241c1c05403ea001881c00d07030701d03141114103040c46250044000c02054421700c5803a0300054000314050030007404e030b0074075655642030202c81c4404040100740e4090b03200ca07010803044600030b028540004207070f414180b42c04219035030401118000da00100e400d07500403424410002c600300200180c8541031b4643c03500d41502c40c00013a100c0300755440a42030b0a095043d00805c0702e00512608030300100c80c0342125610042c0303003002c5603109143c4003000414412000c01040c181583c200c014040c80c1c0c003500c4c140c10281031407016202c8201c035074800c007900c0c880e5541218486e550b5844400310803d006100042000490060100b0709200400345402a4000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 569013642 1250 569012392 569012401
    0x301060e1009140c1c0605091302030c150708210106080906090a020a0b0a0c080403140f0c0d0303090812010b1306020a0c0311060c01050a0609050603012a090b130501090509 76
    0x280c108503806400d404041007408000c034403a0f1710040c1800d40165400526203400c0269105900e8811910f0724000c5040311030200d017110412803145294080342c03041100c01d10886001403504405002d031134218601d4440303101e00301908034a0f1808240d02c907400062a201c184024000107004c5d55410498400c0601441c50180d00860383e0f0750305500c114580e100c800524241568458125030b5085a400702a55507615036908061611001407100a8141c1c090400150308a0900065101c20082c002d02013880300a091f4030305030003c05500720301740ca9900c800c0003610300c502c203201c800398060502216076a445441003086c182200000c3d0f00504c0541d07001c501c0c024089140c4c0d0740300c0c108482d030000b1214405070b49107010814a0082c0500e182e03256003410103115003c405074008905031880311004112030760b100d504141c04d032101d004d0f41c42c034962584040c01703110080c02502060344502c141440094903642e0075080c11164014000843e0b00100c0d0f0030240b007035680c011034200040504540c1030f0f1003400c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 569014892 1250 569013642 569013661
    0xf050303091f05060f0108070228030e0319020f0105090d0b0919170d110a020a1104110a031a3303010b0f070f02060307020102180a0b07060b0301060e100914 69
    0x11012202818000b00e44000703201c1a10810402140742140180c000301e04ac0c000d8101c0c042c1680c050808c40c045039600c240380046040002e105440700c104191032414240310b540074410640e89850703100b410424100042c41143e142c001141b040300d4880c10310001c99140c0350103541c4c24000b000910322041528a00d044000c18a075068030400c1d13a01c0d1307852681e503450395814050300500c0d144078000341000000c100035070065004180c00b1030440c010619110340300403c204200c12600b008014200358841448507244041c401d40c4000c4581642002e040d040e04a024009080f042104007040204202c40c00c2c0c0b4440025030b41c0d000012aa21018441d0565061140012142c01274010120aa020105025050080308500c24030b645401600c030545d43c0c104110024042c0d442100a1030040c82d0101002d100c43c04c00c0458501264035020409080110a40d5104007800e140382240364107640356400403400c066640101d41c0156103030304000d8449440e03c14500140d44c1c80c031235215066031004040000050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 569016142 1250 569014892 569014909
    0x120708042f010305090106030516090c050703171e0114012307030c150c05030105100e0901090b0409060204080f1b0d020121050a020d06091104030602070f050303091f0506 75
    0x41e024200814555034944000303004108a41c07000c0c00c0f44c415070100074080710100d201c01007545d8120a041c026684c040c1c1084d00c96104042c80100056072440f02c456581403084043ca40000c2000c0106508158034042c01745103c40a801070307000000d071042c0e000c2d510344c2c014075111030600021110301c403604a8211300e5242809035007409400d00043c50340b20020003080054860344000106000c0040700c41c001001400c0c0c0e002401740307500507080207404001940c0a270560300109980209900c2807a828500c4001c0503001041c0e00640250312114903000254040c00507201800040c03005004130310a6450344e40c6040c190902a0b61541d10020783c928158a41400c95100c40350282060445000e0741030045040d042e04148807102c0a290905204c104000e54008240a00700b0000500129480d81000d4084605a401e40903032640f04100801c002070458024200f801c0c00380c01c10b50308004094440c181540d00c11036413000107030414030b103c0d0140c1444c0440c0c1090712582c0c0b4070030000c42ca000c0020400f80d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 569017392 1250 569016142 569016233
    0xc0513090b0d1202030d021305040b0306091b1c05100501050603010819020105091008070905060a091a07050a0c0e01090207150b040e121308060919020612070804 71
    0x10b0f15010700800c0000d0080080703506900c01090115580c1210703020b000c0d62078141c2d000301d511490520710400300038900051054020341c0010044c007121002c00e8003014840070300350000f541181e02c50482c0b603003200262003040c11450042015214034000d0384010804c0754030507001641315100c1440140b00d4183c1c00944003944411040080785025210700058600303014109000781d20004031407002000c542d000301c2440c058500b9848580050340c030345007004407a000300e6451100181c600f120811103031001c180c0b0001c5690b40c0c1031141e0302d085490b44a003414603140c54000d9a40500145080040c926204400fa0050201e000e0840c18803aa1742e90302c8030f141d13801281c10b004594664164064950307a07070340b015256100d60021500550800c40ca019065000028400070009003940d001481e5000440c2407880f03460b400380940b86040040c0130381c5a20021a001c1a41c00c041c0c00c2c04800c0c4060484c1d80342a0060303595454070b90b1240351901d89019144c60b0b026102d000c100c0e210140c0792885100c0070030007121 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 569018642 1250 569017392 569017403
    0xb0123130611150721021b031918090903051207030218091e0123041b0c050307050303070c060b030f0606010c060f090b0403110105090601090f0b040c0513090b0d 71
    0x10392100d0800f12960001d0300001c1d1741c152040350410030f0320038071507005100910000100a2041076450201900c0c0c4c007072a080050a224500102640c040c8140302100d00102d00b0002e40000b191210b81d403c1c11a20302c0e01d01140071640014a10301da600702105c2140d400346691409502d809050800001c00030a9003141e00d024028580114408913405182d82d2010042900841c05d00c3d0f03514040c920280801014807000b203010403000c4000790400b4006d0000000a9034202100402e45050407511002d00c00d10588650105128410020360117000940c0a070f5201d80e00e107400c2e00f01600b4810704840015445520a5010903998a2400700100303459034015800d00304240c0d5450b0340d040c100c4c040c041c000c580c2c1026500e009152020808417040b440e00483c0a1360710211464144230b505401c0701c0301a105005503503c81001000f400c00d032600803d84458108601007424040d202c042019507010b00180008a0004111005810300781c1c8a0310300103103000001840707540303440e4005c1000c411391864060310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 569019892 1250 569018642 569018683
    0xc0f06071b050d1d040903030f0b0609181b0a03060303080109090c1a090301050c0406030e0a081c0216052a01081b120112020306060d150b0123130611 66
    0x41010007519813210580c000382c01401049a030b031034028000c1550faa43c141da0355240140010f45414104103172801a10041c10300042d802038140c603401307a600c0052019a09205c851280200d00c0204d40290507190b03848d0b107010414070b042d0702c3c0191403080143c02c007404892802c0d00c0500403a82d0304a90030201c925594102c5d11004000142e03403210b204085100b50998246424803031400c0300700b0002c108480c1107540820840d000c034031029441d40c1c00b19201a2405106000f440c1220f40e032582c40790607504030031000606d070800311410382803089490241500c19401c00c40803c1007400740c10000c0991001c0150005600e1000303d00064a0710310090604204050542030420300300704100101c0740c0200d0181c000c070500b5a0f4464a600142130101d130100e02038010107002c2440d5040680400c403c0b40d074041d40048010720307102c810b44018547d00014904002c099021145070b11254103600c460a42140751140d541e1410701c118107a980c03000c0c1e010008200050240a8607120042000d400c84800550740c0d08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 569021142 1250 569019892 569019917
    0xc0f10270f0b03010e060a060914061e0a08090309031b030a0606120302010f2702041103070201090b011d13060605042c060106120f020c0f06071b050d 66
    0x2140c00441c0c004000c4401c1c1e400010456000310400b85040350020102a040380da151014050b8524540c03040710042514a1801c0c090580c0900c1001124280908900e081c00c15104242480464246611800c1d0a00203a83d0400c00d030700c2144154898440c00c011803421303003640c0100350f552403014252284080c000d6007503991550140160580706800048c01d0240a8803200f04030400751401c001107003d90702e407000038503240b2514042c0041e20407010310115034a40500042c115448403c240c1240e0156a03481400c813006a030f0b40255024401d40c4c0e000066850081c5800781142c070040e0420240030301c4803194058502d045128941d40580d60010321281d8440d2031800c071001c2c0806401055000f070038151242c00b21540501e400d008441800404101458421085a00c802c8280208800140d084001080306401a0010f000070520503e00628005140040c036080c90017140d100c0506070031a1090001c8141d00c50306154080c00c9101c00c8001e114055541d40345c1d00e14202496509002080d0b41c2078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 569022392 1250 569021142 569021207
    0x110c010c02180702160603060320030c180604200711030f06091c1809020a11071e081b010c0303060e0403020f07120503120406090804080c0f10 63
    0x180d860314a10807081d80c0303090000f03001e521240d60300e111040d804400382d0001501e610034042c4100b01c941120500001c101c00d03da41034501815102d0352030701407040d1100001f040e01c030240340703100b00d042c1100c05201606000d0200001c0c2e400d1040540d0b0070003016040d01c0211f0801c0002c642d2290740c410b904022040c2400302081c14240c10060120315401220300b005094078002c540070648241000c0e25502101d16220255200805084040002c0704805024000c40c00c4a40c024149007105003066a4003031501d0791918500318441d04020070403010f00f2101400c1110b091000780250038542c01030505011240b02c020381c5040503039452410800021000e00a00d40a0750145014200c0020301003258609403d02964444082410f0f01c19803248070380028002084007010a15194050091407809480340510034218001802c29284140c2d2a40503030000784041004000405100c03028121074903500c820010174a02a0f00c4a40c020303801170700c59000070740e4070a1100768081c0e1902d0628030f00d40c0c1c920503007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 569023642 1250 569022392 569022409
    0xb01030e06010f03110904030f0c081c02181c0b060d170702010806010311090d140703050a2a030b1302040f020702030609070501020d2d05090f01110c010c02 69
    0x24103050003528004200c44010102560507a409001d02c0c0407948028000c0c0a403065007150084e00242030301001c502c20303602c074201010501d13000c1e010305030810f0003103001243c40007040c0010002c0c01c1e6000660104005010071101400b00085515174081d25607102000208540d240004102e4100c05000400036500e9480c0c0e10718180d000710444d584171800382118031041d0b10869041c0d000c80c01d1500080e103550300c42d025030308601d480c0d062154140144141404044400c3c140f007110620000d0505081403178081000d0001907003c1c0d0001c1c50b02c00001d040c4480e05100b00070b02e18030f00034550342a4070300087c40841924101e0780e0080c07200d18a40d0790072056211a41c0c80c80320003075029040c220080309070841c68003d06681c40c001c03803d94030152280001181d0742c640760310480c1d02580003603a6900165010708060322031070031000c1120510702c00c901d1446481000b041c0780200860300116002d5514203011075200c160318001e08003c0806440ca0002c03d0b55984910341c600d0410100405807011500c64844 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 569024892 1250 569023642 569023661
    0xc0d140c06010b12090d05220812030106140a02030301050d051c0e03010e0c0f01080414100204090c021f02030c040b030f15031f410a020703050d0b0103 67
    0x141c420a503100d410410081d401651401018518900407a046142c045801d14010044c4e440d102d140624402c8001030740c0c4000342e0121034003a649180003603a118244009090920100e0318507030740391f0400c40e019003407480075010010301e55824031181900e10f130008222415950112a0300a00300c9151810074030b0000070010743c98082c00c1d084010000540c0240e0980700169080b802840b0030312840c51682d548106127851240d115041310211885035005644454000c0e0003044240c0804402c0700300c0501e0300c101b00c3c8100d0b45e103030b40c0060100704040851141030052001803015000e03a1548003110281010f582c016094526800070102c0d0326401044115001807407044211600c0e40382000b09442103200855000402098140b030f40c103000d240200b480f80740c5140c0c920700c1d022540c0800c612000181285080c0c14141b60b000b9490140c0c41e5410820f95400700c048807240c1c2400205c50800102441000d00384070301003801884150300094010081d1404100e100744001100c01004d001207000c0d062400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 569026142 1250 569024892 569024917
    0xe100f0b090a09020c0a02010f020d121a030601061205070f0804150f06260127030903080711011d03070e0c0f070803160507080d09050109080a0f0206010b0c0d14 71
    0x1550081618000c01d0401b00c86000740c0300e03040314010400d000c0e0785421419404000040d1001d01000c4400425032041203140068010703003019000c40d001280c50854203800150114080e09400b10129005000d60369004d02c083ca440103914507089005010854003030001005620440040718101200354003c0c2c000000c100011311856640380300d80314100020705070716105801010b040c00344884050103071881d2068400707410440f02c0a05428800201c00000c070480410450340e000002007070040000c0c00100d401000c18032b1480c6958000074104a603400c803000c541d00c0e0030308045802c0c1ea5000c0f8604007210700200e0068005d5441c1c3c040030003e849032340710100c85600701040903004e021144010718851620031092003490a912a8117071054006d594004040c03020410040550b61500d8108001503445200041480403040d82c5521f01c42c0c011045000000e0240c03504d0585e2158100030890051480000c107500d48815501096201c080400c81175060107006580e21100c1c0b25410200d841450504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 569027392 1250 569026142 569026147
    0x8010b0304210509120106060516030e1915020706020607030e010b03120a2307060b241c110a030b130920042f070209040503040e100f0b090a0902 64
    0x4902c0a8004d401c4014114059552050740b90350809051062000790741951f1240c0d810128008800d0f512110940000c6042106130717440c2d5001502e03406540c011480080c82c3c002002c90070300c0d8034003880302c0259415204560041e0010001107402082c02600a013880c9004524024079202003405003c600c0ca8064040c450a60078070415900d0b10302a2000c07200590b90442c0c1c0d540c0106414290501d071351604580c00c03030100002000202c05622617021040051700c03910200d94204035221000200840720b000000300042d107424000c1a0035802141d400031000200004140d100c01d1401c2400360011200030700d40d5035103101c0c00507641d960700216007440d402c000b405540124540442100105500480100285d0014900c6440c01d40184c04600b05950558040050003400c0c1e0328403c046440015580b503401c002c150f0168940004691190780124020766482d8a0619118a0001c1c010b002c1c4402415401c424041224103103000c1003110394440700380380c41c0c1d009400003444400c0a64030105505100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 569028642 1250 569027392 569027453
    0x807030e0307050f1510080d0f0905060313030f03020a0c0215070209160f0905060304150605030a06020c0c12120702032b09050105310512072408010b0304 68
    0x321707451407012400d0884a5511031008200d80d000d61406003031b406030400421000344610843d038220b0307071109619081c00070680e01c1002c03d00a9200b9500c1c20b8140c4580c1b21480c0506070010180809510b041c501103152592a01b801800c1400d0104001d102e066142034249800e0070010550300020b07001000700710a4180081e00c921003c0000c0e1640020400d105905c80310341d40a81c14a100b19100905402c2c91541c0796a155469520901c5550200c19500c450214880d2410082c121032248107201c01a940e200c0c034100d007490110000640d600c40c80c00e0100034041880c0200300c43c204c58015401541d1104c8540c80081d040508101603178403c910414140407203c1140c481040c010381a5444461006489100450b0030744641800c100035056509641400e1103081b590f02c0c0b81701c00c021404900f9203901e660014907101c0002161006070f5000e1141031040c8a210601b03050b503108404001c06ea0700c2981031015104c00c00502c42c03a048204003000040911001c410b00103815003c00e103281f4030f510003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 569029892 1250 569028642 569028673
    0xf080a0804060b0303041401030c090f0902070309090b0f06070f06050a050f130203060601110f0615150c060112021306090e16050312030705040312030f0b03060402010807030e030705 80
    0x90840d0140c900754181035810f001c41c20003008803400c0c1c031030307554070f215049400d00b00541c06040128100800c11440c40000075100ca20120144054040660301596038bd40505009250340d2554200000d1149440c0c0c11500590301d05122005c1c405054032007030380b07411003800d1003d19103140392070140c2480d0a000400c2401c000741e901075441100b00c6080c05203d0303292541a0720700d40c8142c000083d0103600c03901c0482d18641c02506424424036114040360940c44110b009141400411348543c0b2120103c154201c10905d003032241c3d10040b400c2ca10100c1d051105100116176a0300040c400d841c03803040c1300c0c2e000350705544892840580a0781450003d01c0100e0351013017400000c00220340318030303128000d52122910210000c036102c1c040b6072004004004c102001004a10280d20142000003844070410001000034a0505005804461602d00050742c0100300c5001043d18404913403184030341c104104000041c1e8003e1043c541100080c50002000003d840301249144900e03074000e003ca201d13090f50a0303403210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 569031142 1250 569029892 569029907
    0x30a1716050c1e0108010905090c22181502030a0e0d020705030105060a0e0c09030a020d03080f0f160c05012009041404030c060b060910020c120601050102190f080a 72
    0x240c1503480854082d29540702c849a0f980401d002c50018000700e00400c00b0083c0754200c5501300445100741e801050440e00068005180080e01c410100c0390700d02004a200350510400f12500e1403c0d6020909642c1766641440211101c10111a86603002c80464210711031a444a04214040350480303411061000303001e941d40c5c1152180521070740c00c06e40014041e00b490084402101c01d1b0480380c291a4840b43c0840405411210700300e0380510940c0450b5002d41d8131300044440c2c5a00030b8565103098180407202e628094030050100c0c0c090340000f001c0c840070010511001f030b03501c240b038509005030107050301d401030243c914807a01044050b1600c000c044150028402000441c0c821a1b040000091010001081400c101e5000d00881d02151000d000300e003075500404100e00004011600d03264100f000150058020314503c1d0040e84541d582007014240542c15000c5510810300074101da40c0352400003507644c2900058042c01112800e060400c1040c1e102c0d940c100d140d440703940c030340e103c0c224060001c00c1d91 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 569032392 1250 569031142 569031163
    0x3180603020d060816050103022110150804120e010e042d06140d0804030b0c0d0b0405060a12030309060e01150f0305030a080603100f021c0605030a171605 68
    0xb01d1606a0015502c40000b45d0314803640c08480c00741c03020314600001900250402d50415140341d61022840701c001440c0d1880600c0342c00070b40381509560b41003040c0b040590301c00010070801c0c8848581800041108038001d100e01d12898035003200f1140314240100c4a0030b0001407060341203401c003003290004030400d02c09414400c0f41400c0750584d00049413444400c4e988140b045000d2481100324080840c10072144116200d8024043c081c503283d600c1e561034032280390488803010b031000081542c402050b503038040c9161901c03088038140403504140d4005091f5039158420549003809030196601014000d8001c08500f0b900301748200801d0500c103116501070981c0b01540c80000c180d518000c50301e40c84916030a01582d40050007541402810402510b88020191030190f1610402c0c00303a85903924075000f120f404c0031a05ea409612070a0742030070020100542e607070310000d40342003060074406c985000031041603240e04400491481d02414940c070003e4490581c3c407404010f24402c52030288500003440d070022 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 569033642 1250 569032392 569032417
    0x3011205210d0e03040b0304030e15120103020f190501030b011214040b070212120628090501091a06070812010608060a0b040b160c050a03110a0b031308070318060302 73
    0x8900c3c000180703441e0b10860103580403201061002c0340104e881105840401c0401034842030342c40c1546400681d45400103102244002a101c0040c411818110440000c2020035541002c802d00c40c04000d000a0015010f00303810556210142c0781180e00c101e4150b1201001d10303004115520040d00f115001d07880c200e0b02a11000c2414022901480c40020b40741415003e40d06aa81401211502d80304601d00241c080b55101c55080d03555104007100e0364421440191038000e008991389072440000c00e0b102c050f0b000342d22032450050311901c1c0c4501c030621b0b4192001c084594a0340c5100c20310380305860740504080050009860f10001c1504d0f038015003050b00840c01110076080c081d075034508101c09072140d0f015840d10800d0078051000c030032160701d03421034085208140d007510b450388440c04200c0780140740e40190303040040d04091507070070f051080d066030203040b01d40d00403403a40c900031401e408904400c1400500400c1d0005403c4c06040c420000315900d00c2000b0b000990280da2224014081e4200b2040c1000c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 569034892 1250 569033642 569033651
    0x30403020a1a250c0602060a0b01020f0d030b06070c030b010305120316050c01241a13051201020c070e040525170102041505120f0c03011205210d 64
    0x20030300055404408400b8144442520b04140c14050468180b060101c3d00d1501494503500c07000900c08500c1240a49002d5005045034600180c102c01650b0190314158150340064502410001010541300b0b140384480c100802c0b40500d0101140f8284140c840142000b440d240c1d021081005000080e412a07000f00c084036440f90394620802280d110640d802c01c0901140055105842d00034400741410300c00440c0001021030309014040c50120440504801712000101c0a000f0a00056541da850080c100c41ca9800c0c140500c4084000c400240180361041c10603184502d440e4009404a03100d0fa408082900e403100d9440c40e240155080556040340d050081c0f600103442c50090304100010f10500d203004422039880d0104d110344c4080c0300031080e031080d502084081181743c240000e0080816569594581d615a500c001320400e0202600c502d00c4021500180540104041c0650b410364480300440002e8020b01e01c2d10505c1c00102c0d8104e60940c2e14546c1c1d01b035555080c400e01803d040440c1000902 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 569036142 1250 569034892 569034899
    0x9011404270209030304120f0b0109061518090203131718100c061a1c0b07020607020d0e0402040302101107060906020a14150901051e2a0417030403020a 67
    0xd0981c003c4600d5070360940d006000c1040546800349030f0110003406001d07410f0100c01d498441c9034444c1026008a02d0058842d03a00300001654421003200d85007051400b4290004c1000c9004591b1f01948204040c544c2c0110100d40c4205100203070790034040d4880030003109040d80d03411188103504880f401c0d4800884014200d549030520886407100d40520b40d441140c1c00c10f8907034462006202180c1d00c2c503524071410101342c100c0d03180d006598491014055541150342902d28103082d02100003851007046410410074007401d207400141c031800d0b10125003041a10031014201181c000d01072603001075070044c00130713840079a20307500400700301066819501510380c1c0984440c005d9620844910580005034850051440424040c100c40100024180199141c80d1580d1076203400124050b205049265516000d10080c6c40700002080b00302c020312214003496203841c1c00042e18078072400c002c4102007494001e501000900c90380444000d05041e1480343c01e801c0c02c10307503c6d95072600203000c100e01a09042d030010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 569037392 1250 569036142 569036219
    0x2402070b040305031e04080106060507050f030405010207272f09010903080c0f0105041a0a0c090603020c0c060a0e0f0603010f050d060209040f02032d0c09011404 71
    0x7581901e4210000b036142141d0b03120030340b200c43c051008610904e0006d01010480b0102800b4000007000035a490715150307a020304156050802d0504422200c1c0d0042100700400d903000f08810040f1130300a5600d001405a40c82c1d540411015030400f8008245003503d2034070b406c0b02c2007480c00008000310340500ca0300d54803410b42c01c00e280b045108803030104980500c1040050342c62030003051054418419680d400146601c45802d48400750b808641401c00183c4101c10fa4081e1380540d98000380061050201e083d55200c05800d1070720754003c010405d40c00082c6403000f80d80400050b099000c010b04550359031039001c42d008009000300910140f08244031a585c0c10a4038001c1c09980c1070320031000c1ca02c2c004914100811444510058040720081c0e000d01c852000c90743c4030b00c0f400c22031317001d0210301694030318101c9944028403810440311141304160b8480b0495158103040d0556004044005440d9901891401a10301640030105401012000500810118504e0060310b030381c240340c1404002170120782c0c0e020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 569038642 1250 569037392 569037397
    0x30515040e190f0b01080d120c050301061223190510060e18040c170105150603100b041d070219020402031b03090723010504140a2402070b 61
    0x40c00140d0b00c40340b40110710003200309100045030712030a0b1015200c0500d503601c044d184400d90000c40303d6000041d452a1032a0412040381e1801d021b08410056075110100180c0b1034003043c020710040042211404001860551140c1030401d1169152104220a03d074000b840f07000445441c400724900e4035440c100e00c91030f0f00130940108800021282c1030741c03c02008444084c01d00e130f1a26405800c0400d00203003001c01802c5140078a0162400320304071030a06483c2d10440068842c1c140d0340b07a24240030005040c1400825180012086681e56074030f0311100c0100ca07400b02d0b5a001000b68440005000490b4080544180e0b027421452180e0785040d6507590069803588546c0c0300c80d07a40300c4640800a0010301c0c00e5402540d014031440c3c101307901a8811000002150811104200b4990148406002c450a1040300c0c030041000c2c04c2c03010040030b10301d034002011401a80300c1d41102c9625240d00c10400e50b0780d91000e001510b200781880d41c10400101d81da8550310380300012000980684030b030102e04050800c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 569039892 1250 569038642 569038661
    0x810020a08060f4204120f1502041e1502030a080c041a0909060906010e1507141605030606010f050a020f0f0106030302010b0909061b120703051504 65
    0x710108180e42c1d40c02440030346040500c00f2070784040d103a0111880342e0218032141400115202e00c40d0b0701102a5015902c50110058901900d0b0b2070a0200b00489124005251942a40401420400c62480c900021425442008441c100d8004240072034180030788014044100782d0100e1404000340d4034802c200d844c1890f400e0300e10050304204a41152903018030441074205400246c000d2038269905410b90301c5150844124210002c0001e001005103003880b00709030044021514000e660a003800040c1c009c49040041d18000c0c6059007545441c00c40030001e540381141c208407181e86102d50300680c0f540f2442c90b0b00c80c001e0130410520010a85060004116205410603114403081c1a248401600d00b900800700901c21403042d203540303501550701442081c4841402c0000802d287c4e0031403030040c0c00e60f0003042d0414043c40c0302c802000382d85180090400c4c0c1002402c2200300a460140c2c400b1201c9229004404025041c02014000d649034161701183c41911400d48100e00c2a0f003940410059504014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 569041142 1250 569039892 569039897
    0x10050c0a080a0b0604032a0b2206020d03090503070203011103010302180108061302031f0c110a020d02040b0109090e070f0905070c11010e030708060f0c0c03030a020a09120b010810020a 81
    0x41800012088507e0300034040c400303c101c0c2038454020302c142100e20070a405c4882c3d400004900c0ca0641c070200d5031010740031712095210021650605600a589a006a80c60380805881c0c0c82e4003401d008050080380d00103038000d0300900c1354140c0e501c00b58104c3d034020b1100324011602c44081c01c41c202c00341c155060680d50707542d028060039100d001041c40c40c07aa9111040e60316001d12030100c600894040c03a0030a001c1c04800000c5444045148050f00e00000c02c0b10010f81c640241483d0001603842284010650b681180d00144450b607120040360904843e410140c001d500d04210b040b01f000340028280d0071510703120608401c080e101d010050a5410545000000c82c099908103c00103040000c19004107006150101209048600082c40c00c0c40320303400401e55400003010b03c034140c00420405540041940d031042d141140d03003c980c1c5e50b20f100060001010360f0b4041031161071503208106940c001c114030454100040d10906101911500130b100d0070140f403141d22205903514115009882803051940c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 569042392 1250 569041142 569041147
    0x12090803030103111c03080631051e04050a05010c094e060e060f0403030e010204050406060807091e060320030f09060105060315040e10050c0a080a0b06 67
    0x5644d03c1c10818403088041703a2061034251100d5100b100c00d00c0b121100e41c000d03130b5450850b04210040c80b01651280204800d0340c02d5411b2410800d00c80498881900d8200c0035000031965240ca031071a100000d20f1800c4000191500240300610400040030901c0c580540001c10983c820040c054510a12030722480d20100b2040500c2c41c0882c0c041c40800090030707440503800100c143e022004007100c0c1c0031506107181c025024070548052003158810b05038900fa03004010495418180070100c43c280004000404140d150340e074a0308110340079010f81e0001c2a020304103200f41c80c1c132410701401c0c0c42030031144600003070004180022618041d09000420b200c2030216503c805003400400c902400c61080703502c19400e02d0302e008013072800c000d400a612404003c05155501d0400308295410b120041e0300c201e2141c0742c00d00038000c881c26000146a070600048600107000044000252305000103449980089460079040011406c0008010010706c15540d560501e6a80d40340c03a464100d030380d100005074000b5400e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 569043642 1250 569042392 569042399
    0x50d031b030b0a0801061d090f0a0b0907030c090c030e01110d0b1c0b0415020903070905090a0b0103080d1d030a05031003050f07180c0e150d020d0504120908030301 72
    0x20364000c0c401c0310006000c10300340a89604846007551610751181c22021f114596034aa074441d0600b00c1a081100c000141510141150b00c0a0303a540301c819000c3c0c40ea040c010301090b00414104401c800950748200b618048603600c800c904000c00c0c209800c000480c1c109442075400a0f0180318100e16140d6160f00e0f1810007802e02000c800920801110035082105406c014110f04101d0f603172034644620441000300c0a1506103030101c40304518038040b1540ca4010700c601001a64081891400c0e1107540301d0001d0160350340b14840d481e10000d400c000e08444010320000c01848a2400106800b5001000c20702c0000c1192021007541e038010038a0311041c2d0410301c031420032180b1400081d50428a07022041900540f80d071600c50500c8089061040143e2000c0b100708444513587d4030380280e090b07218008011703280c250140500048003035220244604030314203424128031000026904481c108100864444041101c40001003406071420345905106020420f90b081c0b052000c0b1059403000000b45055918 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 569044892 1250 569043642 569043647
    0x151b0c030b1902071209080303010b0d05040f02060a020706080c040b07080a051c020a030c0309020306040f080d0e0601030b09030717090a030b0a1e111b01060f080604050d031b 77
    0x80500400b0800d01e80141d010600302850010f008018065140800c540b03aa0b141c014005001c0307030f03101182c0b68000f0b00040024800c1981907403601d448190002c01c0310f41c0d940ca000c0580c40c010301c3d0000c2d80309401040024005a0001c0c010080e01c3e42c0d600e9218158803003140c3c000c40d41c040c51040ca140088104400000038011034090007014005003003140c1481c0e2141141d41c03040301100b144280242e40843d2481c0c02540c1401501d07990085400c08100300321007500425221400180301500321803000c9100001c0002020480322010310b840301c100501a004040151648000e10069484100d0a00030030340d0102c01008403160142d00c484100d8091001101c05030f1550040c0381560b5003c404076000102046180c51034a125150351140000e00303400309414858005c60f000c00ba109030514209d1009402e41c418001c80e509107152200342c82c41ca4802c1d00000340903241d60380094403581288900010081000500503000b180320300b055810030480c01c80120b007140c0c565520901440604507070300b5001070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 569046142 1250 569044892 569044913
    0x20d0b010809030d021303141005070513030f1104020d0207030305013008040308040303030b031e032203120e010f1106010501050a170114040b010201020412081b07151b0c03 76
    0x50161b0700358440743e40342c40c0c841e4150346005030540182c2000c229a0010b5166124650784000242441810800007810303070822100d29000c01000310040706002d90a0100d07141e034009400900034019591680310030070302006900312102c2100403906040000c03680ca038140c981d4081001014100b4030059a0b81c0041c5543c040310440107070340700c0601b0000030000c150180003c00c041c0d802502e0115007090500281898031304590030785c10381400c0d4a01002c8802d00084200c1d5000c4002446407034901105944026540000d5070000b08014042c0a62072800354205149101240090321b0f02d0950032601d6806541c003003148058031069421040c010300c01580600b000e0051317560b10b0315108801c2c18461802c3c2039844001c2e0000c3c0c10400c21078544490501d01805084001c41c070070b20081d0305103403070281d0304450b0300b846038801400383c240816509c1c203940c01140000b4601000c80201c8001c07595458400354580d540140c0c1d40d00203070301620080c010b031b4280e840004444d83d2001c0030f003042c07500c0d58603001d4001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 569047392 1250 569046142 569046157
    0x414060603130b09010219050a12050c0d06080105070311040e070c030c020d11030c0613120201030e0d05070318030b07030e030d0e1608010e191505010306020d0b010809030d02 77
    0x1444080c0700c84000c43ca6031020702d8840d000b0807000607075845035200000c0d88140b24803540c504200d030801081e420700350301a2210210800e042c0010805450304411840c0038001c07844001c1c10103142c5140040c0202c03054101c1c07409481d0f0b0307840c100046000c421000d01d4600c100c1c001d0304070003130400d404254264441c0c041211614041c1c80d040c080030104d94000b542d02c504200090b50210b040204008051031b060240107800641100c00c10b150801800d5028488080c1d1b10580c100950108840b03c1507900070b80240d03840b0000d178002d40d41103803d9100c0141541e0041d80302980003503803007402e00c8400e80c10034440000f81ca4010304000d40c1655940e800700c024220441c4883c156010a00c240d1011940c2c2e03000360318043d07032928054001c0c890f54140f00e00742c041c1c0170b0388a100d144c1e046c00440e0490420100c1d601a00040c4400405030589090416941d105840d0080059880c9060300003c180101c41c5c1c040d01c8000020982481000b4200004545c0d502e070a65100c0c009410801c42030350b101e02d9550042a64 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 569048642 1250 569047392 569047411
    0x1a0621100f09020721020c0d02061303050303070e2b150606030f140106080f04050304081002070323091c06090b0907080a031205070210060803090f0414060603 70
    0x540311418412510002d0b80300103a181c0e00403681a007013140c14100b82c455109a400d680c0d4105908480007551200509052070040c01c0000039101551200c0040360f1001441841090100e680ca10f80b003940d07684112842000100c5d4030954082d04d151440c20011521055403000c4c0c0030700304c3c8500c03203018010055012a06050410700500103100580141c0c8014102600e00107002002c0e005404107680e415a42010481299401442400c0d00041001e40207098200e803884039070745a1512a166204580281c0c0d2144a00070386500080c1c0b8940052040c1c6200350f4a00c03803011031071129041840400002035007480310921072072505040c8071501b0f0f040404c1041c030f500d84620341070b2aa0380445480103810341303144400b0801c11030003500401c841c9009000320802030503071221940b001845450b00c6e800d030f8924144c540c0045090b0314401c0080781e503d104550320401910b6514101c0300c1d941d0740a514500d00502c03078440d00b646146000c2c41a500d1040506d101000c4680d0ba400803c4a00d51004094080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 569049892 1250 569048642 569048671
    0x8061302180312031b27031e0a030905010f17090109020d06020306091e06040504020a03051905160f1509080d09080129010c0309181a0621 61
    0x255000c204101c5200601410f250352828240f0500040c0d0156080140c800b050400c4401c1c150300700c1c3c0d00e00302c0c056000e084111000043c10800641400781f40401940c2c0c040c01342005020b010030205005030064807036101d518031950f6880064400000f02000200841c4c40f0ba058950103e4483c404582e100d214940009486181507001504060a55500342d806a03408810000c250034060900d81d04014070740341200606510001c110740c04000281101d008640b0381010400315190006458081c680c04000e8420f901c040060190303810400c09015a11440313400740c400d4940006d0303074000c0162a298140c0000301d03414640380d5401180000790300804c024a80c1c100041071f001c05d00140348454038590311002b00758a40000503080d51007505920084501c0c0c0c416451805c4103022002000c140c1c00c0c24244607a60482c10282d4a607030741e6911803040d54070440202e1030080c603141e11101924440d1440c80700301074550001d0200c40e00070112008800e1600c40c8048280380022419a94000c01e030311203841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 569051142 1250 569049892 569049937
    0xb0d0b090f070e0115090b03041502120103050c03120c07030f02060d0606080a0e070608070c0c09050910140106050702150d1802120105060a1e0504050f070f08061302 73
    0x1d02e80a107590181402450080061200034900d85200107008418034102501384d0030005045180d00c000340008ac00d44100c5680e00381050751613010781d52500c6241c81d400340251303501e04100d9118440580051f109006180c02c1c403925200b6041512115503030300c1e0003041d2890440d510303134984445810050303074051404e10105034400e005000700d402405050350780640780c1c01d048485000f0f4991076a07101c0c2150300100d030140540c9c0d51000481e07601c11010301d070846020300381c0d04107000ca6006d07540000d40c01b0750801042004484002400b00768452500008004003c2c03d503000c554540004c1c00741400045003000080050300e0110302880c0043d621120580ca881c0d00d04d0015011641c005e0b000c101e100c64000300640c01c2d0314208500b000300300e04c000e000388002e140401c000740541c01280201c02c000c001c9000d445080142c40382000c0041d005c00740c4208802e080482c158840740f4001c480d80400241700e0b2541d0103200c1d00c646003c900488010b0900003c0403d14078100010b5000401c1200c050322040e40900d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 569052392 1250 569051142 569051173
    0x90615120118022d042403050c011407050604030309031803050a03030615140c0a060f1505060a050a0804141c1806051608070f0501140601030b0d0b09 66
    0x21003440d000e40340c25140e01d07051051104e0740e2103500c80305200c1c51920580c40a072114001e030140b003080c03084a000030228496200c1740c20034201803500720a03030b11640d01d01000304400081d03101d080c10000d895a13100020505036081035132240c09002820b41d00403202050000340642c2040c0e4540b441390801503600b6100b04080d090203d00c541c026113059002201c101e0615400d40714000207860701021400e00e540b845040036056021403040b40040303040004004906c0e11080c010382400960000003440b440d03071040f0240300604020000b40242c110980310004283c0742c024104c440700c55141d1640c43c14400802000d40d0408001041a9101c54240c000171a1802e02403061204c950b04004031071403005d40c007800040000b00109aa400007074400d107803d100e0b0607000340039240c42c14440241440c02000031700d000b07443e034080d5001c02003003100040205d50811006401c40000709104c1300c01d83c1c20a642c0c80d401107084d0303140070701c090790846a81c4c0d42103000302e015010800da1100c0240b080310001c04264610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 569053642 1250 569052392 569052401
    0x303020c150103031d030607080603011112041b08070603150905090d0e030105093c1c0201050f06211002040509010803040e0106081008160504050f0906151201 70
    0x10301c80e0190904014010541c114009450348420609445e401e1405070003c65a9018060b00c0c100074010384100180703007550250007140749110910216a1200b440c1e03454001880e206aa0840300407145076051145078206803207103001ca4100c01c0007024420f01d0083c0640060918141d0140103000f90103021a0411190084074015581040180290029000020f099503460030420340300f03905103010f000b1011000a405040d2050030b403207142140070042e01044801401e0308004641c2e1044108410041c200451000c4656200d10a030246411058504a089400859a10030346c0041113002c0b40403420700100703000145102c41da00001e01d20320200f45926044080c07500c4080a03400007020710090030000e841a004000e103400440c213140c10969031081c00c2c10140103001c1046020000991b4031003c0c0313051000100101010b4410002800f071900381190428003c1074012030402010404010031280700500c035001b800b02802550701d0300400241d002240f6140760750300c10341190080c40505000e104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 569054892 1250 569053642 569053663
    0x8040b0f0304060b030c10051308010c020a0b090c010c030f030227040c080c0912070b07081b0a050d1b0602031302040e0a03120b130509060106090503031c02070303020c 74
    0x152541c681c90b10b440c122040c4c81006109502035001804100c17200d8450410388040c00b0701500b0003545910420064260512050340440074a608166a4101da2600400c0701d42d005030140d01809050769600c99039907500d0007960319242c0000d60000b48032010034070580c8002c540700c010385009403405c00052050303c1030703050200e41c10f544d2003040c012019643c54103114003420010315043c001e031145811941008030340280741115001c2c4203c1141d03152900c505020040203404406100c540710202414030540703070341281c10031100c0340c0d00ba1500c0d103440780720005907500e582c3c1d0711100400410a44603c112007150180411071608001510306a00040c500e001940c030036003041903600d0080310a401004282c461401010503980c002e00000340201e07500200e400304207101d410020405450301c0000c50071002202c03142020161510003403082c1440c020880d18101e66082d0303104007049442d2800c264071781c0710754417101081008900b13108240e02901d802405402e4040d0400509103082d032450142041441c0340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 569056142 1250 569054892 569054917
    0xf1902062e0306020d06051c050105060d150903030204170309030106291629010e0c04090e1002070305040305060c070807020f0d050d09030b09010c020601060c08040b 73
    0xd04010124541d004401e80c01c88814200a11040091040d4141c034025800068400e9800040b02d020701e04007500021b0007002d000c1e201c0300000040864510103910070344011240f40d402d245c00308110340341003400f0380045504000132210b950401c2c050b0200404483e202242450b40070720001400860000070720b1040b0085a0266540310588010075084800c1500b0204120b01908155600d40030040680a03091385403c1d45181e0381d40b00311282809030001d80e40006d104008591000c0e05030809001c0001010244418995050340c81e0311040d500300324100c40905940005100c1085030000a07002282e4081d04d41c01a10f1000b02004207060581c0c1c000c14080d00401e000140c200100002040805d900c0744800100f9428205c0b40c2c2d0320911240300d8450007a224403143c00007200300780d4501448900c0541e00500b140d080c070081d00405403401d026880b00742c0b19101540009402c006041c0900031181c2403e41c00340c42241c2c2410400e076140388810006940449c000d100100b2440700d40c90007012000e0000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 569057392 1250 569056142 569056153
    0x507050c01060b0c1905030d051510020a0302061909051c0816021c0201020d062304090f0f0f0b07031e1503021e0603010f080f0316080f1902 62
    0x3800880c01d5405a0f0300540c0300500070050501140c030081140c1c64a030308843c4040400c0102800e002c1e145001d00d40074960411f10300750900408544205907010507050944282600f00a5840160303141e0300108005400350f00650001020b00e82e40e101c5201c81e00e003148400007800740494486070320f000301050542000d450101c14411010760482c1c00c8542c000d080303203a588809414543c00949659045403a2080000c0d814120401d56000b9010358154180c4800c0800032030b642e030802060101050b0405071906601c8124010103401c05016440045400c80c0220f0158802c0d65070312001031311000d900780d621045544806000442c0524140d0142401c5c1d41c0218441c102100d0b0f0300559626000120708841c5011507559240f100c0e100b845c001c5a40480e03140d035a0506561145d858112030140341a0320100010003c03d0304a02c001d02d0354207841c43d0740102d0356507020381c40c1480d68a214484103440c0f07050b510081c000000b2091b10007810306005184c00b06040c101e504410802d4100c049840710056000b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 569058642 1250 569057392 569057407
    0x23120a170d140403021207060f092d0f0b13080c0a1109160807110102041205120f03150f1201240620010b030d080406060e06060409020a12050705 64
    0x740c06070399140d140707003148445281040d03540170f541e80950190380181c8800200d9683c1c00d00c5410382c000541d81d15140400d0000121381d02e0300103800b1000448141700f40d41d1840344000c01090003014211031942c0b0814440034500d9649902d50119001002070b0000f02ca00618a000902da40019000304003481c4000d01c0941210320b0a100382240410b140c0c2d0181c0c41403c2000300380080354108440d82c4620341080015600c4101c42200c5c0d11090000682e000d60002030000740c40e10b448881c01490500903401c0c0e411b0b10354100380c1524076100d10401010a1001440412070a403603401c0300f041030460003801e6030000e200389404101c020080100b580b803181d5444100d900311951102810403492140300c0c0c80701100d414180b01030550034070001d510740900045034203559034420940c401030315038100904484044691510003092800c084808035502c40c20442e0002d4080503d0100340e014440007015941001c0c00c1c805518000c1d000304100008000b081d10389050352006030f2103a2401504955600ca954040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 569059892 1250 569058642 569058667
    0x20d0b0411281205040f020307170c0f0d12030216060c1b02061b07080703050c030706051215040f050405010209010311040e01030308090307080d0b010923120a17 71
    0x203000e0104121500703882070070100c050f40300d640d000401020400c0092503803581c1c14400b000340d0b034a500003500341c0706558000c514042d40c2412002d89102410440305002c150320107214500d0b00f84621240c00034010310b079220008580e4407a590386500d46160060921211402140110a000d10140c48160b03442d8201a22140d00403451991550b054600d122000510f40c0420441c0c40381c60040c0e041c02908040c854603011080c003a003030041081e041200e41c13003512424403941b2850521900c0d4803a10540e8000541d00303007d441a10450240600301c2806581c3d1401d6001c3c44421f441c0003140c0c40782e0f031110351044c41c10241c4506e50089000f0000140c4401c8107000240440c0c001c07024a025074002413004224205000781e5039410b4a030b1510f028080c0d074031008445440c601501234000c080c080c0200c4c5000650455500061040000f682c462a2042d0354030401050880030010410b09404000d45141c1c0c1030824111550790001d20208a55918070313161180701060f01c9000222140070b000003035403801400d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 569061142 1250 569059892 569059927
    0xf0302302a01080f0c090109080f01020301060e0a15031e09150501050117040f03050f07110f0409080307031a03030d050a060806060604140f150306030f0309030c04020d0b0411 77
    0xe000f820403a0031802d001d41c044070400c0b40142540c0a60000088070291a4841d0503810300411584084803600c10009032420301031b400900070034000407540041720312186003a45840c42190070040c031070901c003050b0341403c0b005020400303000d6103540e2a810803002030710040c0c03085640c0e29010394240000c0303075508600c0c1b806841043e031206041101b40c0c03d030f25128061310107080d41c1044d800140508070203402d2800380d8150203064110100640c01151a1080c814940b51211041c0c40c11120f42651050b00300c00c20045402c0200040d007070301406d00c00a00c105009600020b0810f1301510301c40a0b2602d0000001e00e990b01200f141250161070340c060044488550160310301411809026100e1403a080000c038040b4001d51041400200c441d001090703264841507014100f030480640301040c1020b00394501c0c0810f9001f40c907514024410100c1401e40b41c1002b2081d6081450014044d00031610081300304406134026540700c0c0d1807180d5400a00b07550b07a40781d200b800c0281c0300c564105600c0d1010035180c4500107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 569062392 1250 569061142 569061223
    0xa030315060207050108061318151b0305100905010611060a0204030b041b1212080709030b010506070201210915020301081e0c1003020c070f030230 65
    0x11030380c0d480601006402080460903a01c080c03924042994031680050000c2d130000036440c200600d08243c1211603001c035101d20a0090180c54000c06901d000005041114a11000f801f200b009541d01c984044c2d2082d044107801000503c6118001c40d114040d0300300711202030780031402080c0380c0e40c041451400c0c05d01047c0c0d44092130300c070214145861030300c80d01c202c8540280b0040c619580070004000080d62003401902800903081100510032840c981804011340c0301c043c02005c50b0580c40010003140c416144501130301da200540c100030313928000078400c0903082040d08905000300c5003001c1840c00c0b003250000c3d9046c2b4500300d02040c034440908211605a210040c029400c42c0100010700048200041109040424200d41c12038058500c11907404c020080c483c0a030b0211781d084e8200ca4a80c0d06070007501000c0c4102c016220841d6403500e0002d0040c000d807100030f411905445580d10185903405840007141c64500500d01c0c0f1039003902da80307410328880054440891109401c0c1040c94400e810f00c40300d09 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 569063642 1250 569062392 569062421
    0x10203181203010b0306030f0703030c02181303080a0b030a0f020f010206040809010f0e03011a0406120203190c1d090129040e01240503010b030607080a05041b080a0303 74
    0x50006030705440007444140030300360782c510b00003010071600e480c100070980401a110083c0d4101585034a030041411078040c0c0181c1c0b06aa82d20221600035a036802024002c4501c08171600c2c0c4602542e4042e581c1130002000000c0781a620341c21440399440a022040110744207003e401c00b03400003881080303e940740a158040c1194000000c02c0005002c4c1011110401001d082140c800185000c0807034400b00300580b0941c1650074204418142c481c0503074082d00c610002c440070f01807640c40d51036107000801c0d4507202941c0f40e8000d0600c241135140000c040317900c1e9402080c0d0920302030b483d01010a0882c4100340003a00c00c104100410428003007c0c80341031a5040c1c210300c80d410034604071081c280c000102c1076059102d640c2c0c40d044804507803000d42c0304102140076100400c501c01d400b8802ca881948542c4180e40c040c1d4201120b40c610b0340380106606203d150240c030303400c0079515100381d0a0000c10740108104ca01172a15007000b20111010241c410040505000910129075149030040030707240642c0403c800e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 569064748 1106 569063642 569063653
    0xf0b030609161403150a0f0314060103032f07060509150903121b0a2904030210022a0a140d1d0d02030d0201020318 51
    0x4245000c403031405007592908650034522040d07000000001d1141012014040302c1c0d10051500208040203440d8144c203505c0100e03d04c41095040266040e20b248004c10804c031b03a00e0140c1c034902040c40f01034012549507541c098240e10600c05440c0243c010b940a000c102d805540b12050240806022a1b0415503100c0d07000c1d055600a1400502601d1452000707030081005070700320f0f820002c0142c01424103900c1e80140310190307000b40c40e0314480000c00f0500490410002c0014441090081a601389000602c02d2115800d45100300c810f255824071108220121750003180441c5000041880541e40d48a41101c00244c8450503110300c1c80c014a00702070052040700042d400704540d10503413007402c001104280450b600c0160b4401038002030350304818041c2424041d1355208001d240a004050040c0d81940000d0402107841c038080d0050f94084108840405010403a500c4848807074003034030 = true := by decide +kernel

theorem cover : BRFrame.Cov 568884892 569064748 := by
  have h0 := BRFrame.cov_init 568884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 568884892 ≤ n) (h2 : n < 569064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
