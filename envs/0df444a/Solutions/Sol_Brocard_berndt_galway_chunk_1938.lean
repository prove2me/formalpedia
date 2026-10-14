-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1938
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:13:43.927307+00:00
-- url     : https://prove2.me/submissions/b1553d90-527e-4ff0-85f4-134d536a5818

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 348381294 ≤ n < 348561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 348382544 1250 348381294 348381337
    0x30303050402030a0b040309090b0f030607030513082b140c13080f100c0503130f0f051c020717031b0f0a050c090604090b0a0f0e0a050705030114040305 67
    0x249003004c00c40c00146211009402c000030150310540c03c00450b00600401c0c001d012040301040422004050081c0e010f5000e5800240700500c06e40025801204143c648030b5408080e88541c0c01c1075121085201c40440403081e00d04502d041c003003900c09502208241008920824000c0b014864800b900d4103942140105407411000410b410f0ba00c014006142103a0180e480c00080c1c83c0c440d40c03034440400c440c526001210322168002e02c2128850a115103003903d00c03034000e656540c100d0071140e5081e1018403c004c00b01c0d0000d00204400e810303141160000c0c0740411042a40286000d86540000c10010003200340c1440c1c0c07000010584045070180c0c110911006841103044d4038203010707500a0951881121465005e120001c0f074504010001662040ca80d03541d0030342030101f525074070070008004c4406040000c56045441e440303070b03000c0034030003c3c04201004c400002a01d01000228203030b400e07400143d8100034030304c0d00344151019a08800032140886c940342d00d0140190080401000c2c4901b07100010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 348383794 1250 348382544 348382549
    0xf0803030f180d110c010804031b05010b040c030f150f050d11090717100f0603020d0e0d03060e0a14062b030504081504080f09060d0603051c030b0a030303050402 71
    0x104000c1c0d8071100c00b01c0341e80c00003000c1c00a00c00b01c0e0701c812800c0c2e240031741800d16039030754030460360184100e401d40c0700c1c400340b13400c8030b404201e4540d18070300250303000e550700e2020320034590f9035004e8907034860072a90303022400174025013880f8202c130040d40e02007804c1149503104000026030360002c1c40449408680303c010306a014140504420524680c29a1004c24030080101c00c6d13402800e9280c420400b24042c1c19181d40b40c0d10520b4400300203002e0060340d4050315404000c894400e40040155500c0702001280d01c64185540a184c00001c101440100b0307120103040c000804610601e50380016251000e100441c4055003441c81404040c002c0c5005603ea50100c2c031941c003440c100c440e200d5103010300081c081c0e0803900b0010043d030010f0081c031805000c0c12101d15000280c1c144214000d981002e038541c41c04c4c2d002c0040c0009540f080200542042d801c0c01308034034410051154100441c0030b48040c200502500054211402d03052241500f0702d850f042059085c1d803a81111901a603034075060000301780c2c446000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 348385044 1250 348383794 348383821
    0x108130209130326071b0b0610020f060c0a030b0906090402041d030c03280f210e0d020c031209100e060703030b01110a050a0b0714041205070f0803030f 67
    0x181c501300848960641c4070342000c01e081e410f1040480d955110500f084403803000c000f500c81c03144007030103102d80c001c08101c151414030043c502e09201801203480e1010005801d9041a4007141c840720011030208800314640e416029400d60050101d8270107100d881e064000035000c0b00c0c050b01c00790240342e443d2008410603d501c40d10900c2002d503103007160b48031107100809960380c0e40001444141074100c3c4466a9070003001d6251780b43c907076015841d0b160340103504610480704500f10051300b488401c0c2446110210a2080c411010000c03040c0000d0600a41841002b030301c0c0c04120300700c41c0e000754030101081c00c202094038283d400c4280304607030000c0c95594503e000c5484c85480680140d210300c001444004254040e4072550b881c2c071082e22645d680b518424034654070b5222200c0c1c0908507410480c0b040700024442c0820030750081d0113003800c1140300c0c0c903504c00328a90b401c20382000b54410340c04181d00d070074040100725600080118a2403109038900b004540c039102c0c00f02130207a0b501c41c070a0002203002890b94a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 348386294 1250 348385044 348385067
    0x30c0c0a1407051507031b05010213060203030f18250b0f090a05240705160308120c07020a030f1115090a0816062d030b01081302091303 60
    0xa03101c032851003000741c494075000c0318800c1620582038135400c400013500b5001034804050301602d50010311075041e601c1c140c15040b0217030105c450b0b5500b000815605000284014040c100a50095849207495004c40d0348141c0d0180c8410150315200c2700428403200c2c00180300f1080c481c482a840c031142004a00c03104d0001e845d070804410700e4000714103410b1102400002e0300c240b0100300c52100c2e840b076036541884561030740011014440102803080b45032102c40c0c1d00051070360074803807000c0356141203800c0384030f0b821050b481d001127401000c00a00074580704542c05c1d156800c1206050b2951a0071280c0c0d00080074448a880010401400d80d20000140002148100c80c00407000d005070152154160020040c1e6208140c01c1d481070700454800b003050f6000207420349989003032002c0402d88c1c5040c82010b0315204459443d2807070035480702d640301818003c22141d42ca408801e9840c01b040782031242c400903291002c020140c507100e641004400b00580e5420003001d401c0003e40b103d00294488a040c121041407500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 348387544 1250 348386294 348386303
    0x3080f01050d080a170117010f2007081605010e100e10110c070321140d1d2a0607050601140301110403050a050c0613030201200d1106010911030c0c0a 66
    0x9074000244a001445183c047d8642000204040ca8200710b1184c116107121700c0500c001030b01903c0c0c00310410f119100806e011030003442d00c2c0c1e08295030303e401201c0b91703513045604542c0769448040203164008204141e00160a0400040c1700b69126141c02c255500c04101e0842c81c0c860f20380c142540c10044480881303c00d40000c3c425030f28074544074100030819084d20442c00700f0b100000c10840320010f114450740031040c5043d2080529000303d50251102801092644528031111003000d40741c400c40400c04110030191400d642d03600500242640c221241c2c031000000d0081c0d104011160000d90082941c0f81550302c105483d182050075400442d0050803c040300701f0740d4440000c0d0210030712a00040e0711b07081901c104121141c00c80300005000d082c0c010294819600340c035800341800150701480d810b5801d510811640c801c1202e00e20744091400125070640004140c20403d402c00c2c1a0007031021601500716410b00b03100030703144100d40c1c2d42144401084000040000300708034804000501c00b00c1c4006411 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 348388794 1250 348387544 348387587
    0x106260c130612050a02090702010c0914150423040902030606090a1121060409030c03230d020d0b040b010c231606120908070605100b0a03020703080f01050d080a 71
    0x440c076003240e0351428444140e205811001c005008c03d881406400306070039440c0e64105c43d6504c2c104405c14207804500605d41c2c0040303400c4201c444101c5200281c8000c1c006c44421641038020340c0340c440c04a58505203054022414646180090303103000030380320b400c21400e80366100d56956605101c0003e102d038984054451000045803181c1103072011884100c0c0001e203103000c00c0c40c1c840300208411294203d1000340030464200c1c1c07600102e4094886000c01081c88402c101c002e54007a10b400c05254130003036440411607404184104491114400c2c4038040300d040e102002030082c1003002821000740364a00401805003000d980040005500401e800d8003000b40444402c00300e407886402c2580c159003e440700003121038000340802140d6014000455070860142c03403030107000d0f444240107880000c280469881c841c1030001110340c2003000600000d40c03265401030311041d4618004040c3c4501030090b8800704410300c018403a554038200344500083d03000310400d91301c508a04041d600c4448090004421044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 348390044 1250 348388794 348388829
    0xa08010e0f010b030d0804020d0507050913030e04150b090607080309010504051c140a02240105010f03110d0203040f08130e07050c07091107060e0106260c1306 70
    0xc0003034052030000190009200301c5400c80d0a155880d8081d0300004001280d03e00440c015080000400c407840e800b80082d1409551114040b4480c890142c0304a0307081c0419400722424103501c0314503d00d058208032020310483c800d685601c11084068002c1800240c00020080404ea446504481019034401e59580d10f92504100d2075000305001c95041c1c0d6903005000e403c20341404035040c9201d04400603110340c1502214460040540d401c01d0000b4029842488400300003000c00350044004a41070080d105c11540c1454001010b01c041482250705050415054080200f0450151501b559400380010303200d1751141403086000e0a209409045c50700700107100044090750300411001d40f620000748035956103800354225a144500f09258640340c1045900b13000c1888150402d013030960741e07803030038500b070900a071651012a2080400c02040b60741d80c0350200848602c0842c241844540c0682d042d842c004030351680c61f124102003858510801076200341120b460200d0340110040c20343d882c0382601284 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 348391294 1250 348390044 348390071
    0x20f0307081506030105070801120b060d14070320030a0f050111120726060f06040513020d0f020a020a0b0a1b020d0215091e10020f0310080d090506090a0801 69
    0x302d003620454002d50810000444141c000c0520714102c2d0b0005510324016102916404800c80b0094803241d40034400c89107a00220701880c0d4a051108004406065501d145141c501848a5000a9082260b0341a0b01e5081e0030341d004101111850f03040142c060859405140180c0148502d1645c2c61510401060364203418816444580c0b0a92143d114084451040b8401000703044001141c00c0c80005203000142103810410b4000740000c00c044c101608040d240d0001075103c0003140f1401840c10783c0800c499842507224000d90007412800c100440c50040713442c1000b5111206844050003016840c1c022913030042440c2d0040034810b424090154175401071142c0203442d50b10b0b44a8400040c85884c0b048440c4004002025008012290080040310440d1403004504001c0288688040c06060559448896980001c0c00300d40341d400c08103641c0f45050600346484404640240e401c940c00810b0018040d60824286001e0703602c01c40d04141c8884140000442c1902c090f00500303004c2d402c0141d920b14a2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 348392544 1250 348391294 348391333
    0xc14031b0a051c020301030803010b0705120307051201050a0b041a0c0d030902010e040e0712030e09070c052116020d06152c0a020708120c04031401021303020f030708 73
    0x44095040d034030f0044101d1844000c0c1c3c0400e02000c1c1445034208010040308100c4030043c15450301c10310549901c075607500080b41683d0000c03039101700494000100d40d0300034007034120554094130302210401595802e0040f500c0450249000d014008000d010700d030760032002d00f441510195030325241122842206a00018082c01040390101c1c0031420b002c43c4980c00d4a003034083c10101414080092034030724030b40640d849129070700760001c0e024061035015110b4540c031038113811031048c0c0c0c3c1500ea10517540384620b170030f6140c04420507045003a43c40c640e400700c1040703200030308070303010280c15891440b4480498000903604480000d001000c10f031170b100512902004000c142011901003442c0341c890191500300301c8141150015118181d049181d000400100c00f581c05040c000d401000d9a41c2444803014645941010645070000c050102042c00c0081090344100d41d2107012900e0003d504254400060f071501c4442404002e00c200080076280e24591000c000d504010f00c140c10441d40d0080007002c104522 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 348393794 1250 348392544 348392557
    0xa0503040603060e092b0c0204020408060f160e01031e0e070602060702010207050303040f1b03030905030111040e06130e030d050115090f0b0c0a0f0b10090c14031b0a05 74
    0xd0003982d0000e090100c4c0071481c01c41c0d0146c60b8040010040c1c980b40e0707422a841c42d6a080801340981d4400310805a1500d102030005003580d02e004001070f0405a0028699000090036503000115102981d00700b41d0340000348062801081c200450b000b0b141c00102c0c01c121203420300e003040a42c40c1403e403880e00c1d100090300f8422034a20350290340c01c1e6194401d0490a030301c0303501d401610507442000482e00089107003140d006440d0103600c0410201c01c8003400403880f150550b100782e0000710301417001d20241c5400c0c446c1f45080c601c0303501c0c114a024a400c148a604c07000c01003500380704080c41d5403203511200c3d490300040c481400e403900340c07582c0718080307911100103080a01512f004006c0b280e1041d011907000e800030005641500090540d6113188c043c080030198400c07a40c1000c103004000c040c00c0081c40c55103005a810b442007002100d036203411260345400d41c82651104c0440c40c1030408082916401c00c90303003062880400c0b01c0c90340d29a581c2410464103c820803100c03040c03020001d0389500f199404406443d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 348395044 1250 348393794 348393809
    0x3020702060a1e110d120204031b0312051c18080a11100507050415030e1507031b0509130603050a080702150405030c04021c1a030d0203070f0b090a050304060306 71
    0x4103c2c1c409035003110008800041c40090f548800c04150b00d041c003d40e44080002e103a0321025103001e480e6510001c0d0750400031349501e1100e689a40610400c645580c0e0212000040e24106007800da054059a2429403009030300e10000d5070341d2243c1c1181040e51980c107000c60b9040060302d5682d5607002401011420f540d01000054040c0c02e44c1001030085900400340610382030b668480c01d041c00c0c02069048611040700702e01c24180d0706d507012f51299200f40483c00a200820040c1c143c20310f0940400380a0b180d81c00c0d080303410310541e0b62100841e40d8002c0145c40d1281000c1d1500341c1c2c4c49260208400007006180c001600a10443d4140001c0246490040004c00e20039503c0010441d1940f545130360034040c9015455254011155916032030034564054500c1c49204850f212844460b0858081250b80071150b91042000158885607281010041c143c422105403004500d1b010721500e8494882246031001098807044001203401c1d80c42c100412a072068100e016079541d69900c240180040c0850304c200e01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 348396294 1250 348395044 348395087
    0x809030d0804050318120709150b09030a0b10030507090506030f06150d0309030b1008011d10020c120412020414010b030601120e10090c0e0705040b0a03020702060a 72
    0x40340c2034414a5102d0040303920800850801a805400344109500500d0f0581c0001804885a10310401000b024008140c840d2000880c4550000e01e40002d89040d04208030300c007402c001045094400142c1c10b0a1903401c505281c200d601c402c9808803498400b0780c00904948200000800c1080365a4001030080c1000c4080f030303a405010f0090682c07101022110a03990214070759000d01c050518400c000305092081c50000c00254607951150004031003620600c20310005d03082c051015141c00d109001c43d840c514606034282c404000c1c1c80b030360703a0a0080b002d220140e8000c00c1c501c18a40c0e0030407400c050380340220b444945850300d9400d14002401d20800507403096080c049072680703026400340104e041c1d610802e07045107950b0302e00d40151400010070f802030100e66542d0b20f014000d40700502818040601c001d02c08075092905092446103255150080d07205403401105000d281c039007103001c030b600f154062407190340c5629400300150001e01401c00080e402160000e211400c0d268411000c083c00100c120401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 348397544 1250 348396294 348396313
    0x1050307051807050c010f06030b1e10180b0a0e0406060f0b0f130504051005030f0f070512010b100806040f0917090a1706010314010b0609040b060d09080903 69
    0x6801c01048008060b801ea031201082030b1500c110003d1018090300b0002041d91002c2c4041d0310201c0700c0c1c0781e000b500c40e08130920500205040c00c0c0d107200641c0001c0910109641001f07402d4504900c080e116244c05004002800c2009403025084140e0744100240a01d004542c0d0b0810542400d5049908813005840c1040100e00c1e40101c00680054400340701081d424001404c441040c00e0f0f1000d0701844881401c0d14001506030342d18041c0c8d1b445080e119506101d042c3c544410b040c0f800c2d0a0304e0200103150484031040d11340003030010340041114822919052100420080f0728010300b940745c1d20981101185401c814080d80140209002e900c040e10200240300030031000000703c0320300030720042c0b8801c08001051000032015010349850100181000111941c4004c02c240301104100c1425460300184010000e01842c60965002d4285410003401010702c01800140f85202c0d40004600c1a0b41d6071030901c0c1d50392121410b89031000240e20301084041e0750307414440415000344180074802e01c10b81282 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 348398794 1250 348397544 348397549
    0xd1a01060504030506011206150b1e09030d0e0d0501111306030b0d0b090312090a120206130602070809032d01151403030705030d02210c2a0a08030105030705 69
    0xb15002c507a00403000e401030f64241184140541011801a80c1e0075482c1d11880e91464140d0445000a00c40a0b003095540d55459000030350f00b000d16840604d00301000e10103048261400b1070307603e01c500410b2500071070000a12001800c981e044940261480d0706e4208000851091400142640f458440d400403545507a02411010b03215050790540d00b00c044403222000080c0c00b08403031600406c00c030342501c2c00d1000c1c10304040c0d850301b0102e03507440599004503000424854915800c0c0c500540740d2010704120315022040250b11100c0a23001007040364000340398801d03c1007031000c0d1400c0d40c0000b410340e4250980b82004040000c00c68204401d407449444140090250500c6800641c442100001080a10f880e4003200400216107106416000c1000307980b0004005000501c0215584100143c82d41c02105001c0031a80001b138500c51100030f003406000546d000f1006441000c411014003c480550307818020491866245080589215505485080101c400080d5050f110306400725960259a00c08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 348400044 1250 348398794 348398797
    0xe07092a0e09070201021e0304110409020a0e0901150806191802010c060b06072a061b020a0f0b0c10020301050a0e070c08120403111b01110c0d1a010605 67
    0x81440800e000c9401c004950501d040c07001c0d840f2895000043c20110182140844c203403502c08880c940303060010030002040b04602090304641000e460400c00ca18490f4041007200100780a400b9540e20000009041001d00b5005800300c104d99480d61030712560340b0001d041d07031103005071058190b00600001e01c6100340118424244807520300d10310042c01c14000d8005440d5125001010b0315242e4881580901588400c8014280c4d284a050a00c0300e6140c3c90420501c03407640082d485040e196034041c10008030364801c100b007030344990010f4000e40490641c8001004951660f015010f88175103140c0007d42c030340c11400070b003240a45002c20b442c0d15041ea003034200102c0c0700900807030381d10689200e01480859400b1402c0da901c00c21609010400030050b88982c50300d50014000041c030a4840c4080004041e4015081240c480c0018002c2100c900f1240c4544820011114594100056007d00410350a42003240061200000d02200c1000080c0e0900c4070ba10100c0f611030250540b201e80001490611410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 348401294 1250 348400044 348400121
    0x20d02010e0d140c030c0601080d020d080403030f090f080d0f140c13081b100305040c0902090a1e030b0903030c030109020d020d1802130b0d060b0102010e0709 70
    0xe024003111280410142c41056240c50f118084481c140000002c2e40303010801041c50482180003451990b2406100340d01d04000c1d101d96208541241820141e070a4100e00c8154001e541402c0110702c102d9071340741000042c000404040d00d8402d4000b010010320681c800105045501c6003401d1228051148040d0300b6980d41c411310521300c6030000000b44114400300c000c0c09100c10b07001a200c0d03100d5034441d10316280110000030070001404036080ca1403545031040042a083c42c00341818050792809498441459900f481080350a0741c002580b4802d075a5100218000340162811020f90081c02100c0e52501070805d01088034801c1401010800c00d803800816684605c4150012500c0c5a08000c0c1c3e900c041e401040420040315000c3c400620003000312f01502c40c200400c10b56910b140004c1e401000344444881042c0c1454515200e40d0286688492100d541e68982005d0b01140314000d00c0c00403401030040241c148158001d60002040b07031300c01034000070b0041614140c990f0707803200d0641c0030200c405040c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 348402544 1250 348401294 348401321
    0x20720120604080a0c1b09060e07020c12010609061805011a03040f050703121d01051306080c040b030103140d0f090608060a03020618011202250c09090b0403020d0201 73
    0xa00000b00001c01ca0001850540c84626002002001c240da0380f00000b58041125074030074440d400c0a2220080320f00c550402019104013045d024145600b02030345410540c030b0000d00031204c0300c0103440c4142094000c00c004262950040202c01c0e17849000070a000d4804c85510012400c0100000d2280007105c007044005a1260a5502e1526030307642c0d4100c58403800004588a024010000012030449451840c1109854403050f444512034000c40f85c21043c40c00c03c1d28140401030210b00711141200d0021001d8404a0134101c0140d110303c288801503015075440102c00e288004008030810200030f5101c02c030400b400040310040054a001a00d02e0190840603000184102200b00000c520076105144c0110025001899042d10307500031035115407026840401d004050442000c070303542d0041c40350381103c113462011410204914048290003400103540010580114400030910282d040302e81d0040203500c41c104650529031401c400c0703031441180c055001d4040c41c541c82d0345070360060040790911441d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 348403794 1250 348402544 348402553
    0x8070b0414091306021218072702040f03030201090b100308160f060f1b111c020f03160210050711060307030216051b0a031505041502072012 62
    0x1d41051041502c1d0040a1250101440724280007044043c030040c10046545000d0028034070744640c5c08130355922101c1041100350b1000d0303010071600b51008910111642c20300c80407142840c503058040c3c040c1c002c2e82c002400f40f10001d140041095015800440c803a4800c40c90032400d551490340c0c400c4007280d90721000c2c0403d0410450002c100046d100b420507220b00c90601d46900c00c3e0151901c1040701c0302d00d0315440d0810341d1010791303040f00c0b2510400f0b01071401252804d0000d1241520080d5100c4007090600c100142c04c02103616144c900074400e015206030101f0403030f5124198152046103013848a039041e400b0b01958800401c5580c4160101c0c1d80e8107410040300883d8103507032428044181c0c0000c00b51010581d00341710700341007140803e10009190340140010034181061051201002e03609604482c03245140b003c081001605900d103510802c95441400192990f9900307183c2284200710700c500201e2031001610a08011881c454505c450054032040d50b00c042500c428800f460040d4204060281e10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 348405044 1250 348403794 348403829
    0x90c050c07030303020a0c2306090f030d0209041b0201020304111c150b131a0414040f020303090d030f030b01030c020703020915032a0402030f0c031f0f08070b04 71
    0xc0d00142043d806030310f0152070b140801c2e150400d0342c0c5100c00412203230b84221802c9070400102041040d800c0703040c00003d05480d0a9241605980b0300c2264000005181c011a141d140e554841d4041100310459030a8800b0382041132070700034002d52084034110b0350007070f044080c51501c0c2044102d45e1003c00700004600303424421a100c848001444064286100e51030705515580745d2502d030b0030300808018003034000c41c3e07485580c8030314407184042054090046161811606540500003d42030b00a5041020301405030000d001090840c40350704030f8640c004107007a11550401d82e00070030f60f0000d84869a010040010030400440668145408000040e030182105001518025004e1074015a2180542d16261550404241045c03207400c0c400120501b210b801c1e130090f01c05820780490003101207504526500c0c02105007220003002805c98070711030303002000050040e19840d543d88101005003a030504842e0384d81c01200a454542e000d50389940c0211080001d2902c001c0065034160f07101400603800d1200c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 348406294 1250 348405044 348405047
    0x503071b03110d050f0d020d091202010e0d060f15060f090e07030c030204030c170601091e0b0f090a052205030d02220b070317070903110111070807090c050c070303 72
    0x40f140265028000c0c48240d0302c1408081156030510f034455000740c042c0144000f00504580c0c15a84092a000f22703040120006130390205032500080001c5820a41421680c10403d00400e021600e0343c0c8500d29000c000e0f007031502e11000c08021200556103a508403058030000300e41c0b003403062050b01c2c5250600c4001c107030818000d0f004860550090314005041550306e448031150f200041c0c3c090100c942112000e003460703640511000e40500590202800500050622050342140007840c60110580e02c41d01c4000d19501c50700441400c0400510102103414107401c4900208015918140e4403181d4280030303508418a2072101e50820341200145040502c9801810045e61001e9140c0742c1d0960341040d01d1548800012054000d0081050059243d400750300e0080d000030a07142c03a5140c2400310700100070850340d018400c001500d5001000e03402c007a00900040e43e06501c00654401c85014084011a40705400030b4a0b000300c82008002307000c000c500d814151582d01c5401c04440003a00442814030129 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 348407544 1250 348406294 348406309
    0x2030a06020c0c130906052406090621010e130804051c020315091902030c0d03120e0f060f0601090308090d060f020307030b030102040b04030b130602070503071b0311 73
    0x1a1503030029038051080c00b000141a0200c00300380504043ea0f10140301c020f0101b188146030f03024103100d0408516031107801e4407080d02c054851100c4e100784400120b0700c905031500f40544501c00e84005581c5600c04c42140c004201e16402d0189441c5c032a01d0400181c0d40c01d5100b80660102034101520b2443e050403d82407010319040b090030380c2d240c110705c11503400060710f0402036041c044106425102c15802c1001c0205c0c20131400c80d0b00960342e5041c0301380c51030140c1d502080160046030122801c000d02c240d2880c068030002c003202401400e80b07151140d10705180d800482e130400000c0c0e080e007c0d40c0096560112522900c0c42c2a1030040c0000c200c16010b02c0043c0e414002044030071001001038800561039900c00060b940c400c40700c122400c1e0048244000c0503091f019194250504800035824141007042c08119405140300141003091101d02044907400e030302941c0280315810000541d41e4070424240245e40303030301080003190200b1103140700a003070a1034148404141c0750700001e07107400030320a642000802e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 348408794 1250 348407544 348407557
    0x309060409020f071e031b0210081005060a0c03080c030405030702150c0a0606171c030f0906020c03040617010308090907030e070602060109150f061b0b070801170a02030a0602 77
    0x881c0104962070205d0380500d401d0121480458120000c0409490000d00008102000b14040c100700c4d0700b41c10059503501c0e01c82c09140032612301034155640394204019000c1190b40050341041d00042c034000c011350b2101c0c0c01c002176402a2074061041d00c5292006c0a00d1108460282141d08140070150041c680302140001c60900b5103072690030500101d040130700700f00c82036100325415646c54900b00603005000b5a00d680500c00c09000d0720103524001900b0024841d552800d6040544e60b60341c2c000c0e440842d0703105a58140d04442c045456440b027140c06603030b0350b04c11300a00340030034606818980241d01c50886a03060342e900c0141c81c1d003881c011505101c1101c1005d0b10358001d01d51074858061f440e20003000244010045503008002952500440030200c42c08800d146115114003030b02881403a8400400750b00310f9429162014203280560054615680c80380d10003469034013440305100306903500807080d505954200982e83d44110100025598a40c81c900c00250150084200a00420440d5000d0002c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 348410044 1250 348408794 348408817
    0xf070b0901121b09050906010807320322030c08090a1d01140d030207050f0301060e010b07060b010822060b0d030201020c0d090806041218170609030906040902 70
    0x548240308050410f0f540c80000840700005069000d410300c90340806403400400054800103814141500020f1210760001d080c2000c2c0188120360011106816801440c80d403110040c041003d1460446000103500c16a100704000e552041a0100860b107541e407038492a905450b03464041070b00d942c0f030000b03540180c0611607020074078110001d44039100700c054644008803045125900d48c18021a12844030b000c4c480700d8090304607010a0707000660000340301c600ba11821a842c5081c0482d0b0310000e405040fa40e000b054905400300d0000a6803652a0060081184500d506000c6030300300400448181c00c041b10750903660007d4000743d000f06074107600807101d81d50182d800480e81003c114003055441c1e030b0807041140143e50010b00c501c1441e9003804103484201c40391405800c094908120f4a6882c0409403018150340c0d145540032012600420a17240c5101c20218002219a074038164050140c0c41c90501101a0156030006072904201108a542d00c0380b0040c00b20b401c160a0100365002500103800121 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 348411294 1250 348410044 348410057
    0x12140f0321101a091503011d0c09120a260f0903160b04032006030105011b1b1d0906070e010306030501140907060f0e0d061503050607020106080f070b0901 68
    0x3d030400c4101c0c5000034204462840641c1e907003141d01481021305003000302e40c81c550814401403000002410f041d26118803000310301c5450f5221120b0320405031080c60f850984c040c0148184421860003c90324103082d9001e0110b003100f8128000c03020b00f00660400d0100e00c0075504112a050503801e18018240d5210050111029400701883c042c080030100d03001418861001304040041041c1403a1480000d09803a1440e1041081d0f100850380c41e02060282606010704028104401d081189010701d06580017841750a80701400d17080e2010501a03070143c61046000e02039560510944181400c4c00360030500e0040843d507a541208980802c01d140e0720f6410181c80d0200000030030401d008292000f0001c40d0441c030142488100d2610b00100340c2c0c400d03807e12815407002410700740c1181d038094030b11900ba1009400d08900e482c3ca4801800715400c82d524034201d0b01e40c0402803002c0080d10622590b03550300200689500c514032a42c1d1950700502c0d0301c9644c2c1c802c000c280301901e510406019024418144607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 348412544 1250 348411294 348411299
    0x2a0815090f090319092606070305250906030b1e0f03030708030c1908010b04121a0f07020607020a0b0105040e0c090114031c1704020a12140f032110 65
    0x16080c0b010392080000079100382e028810440419116400c1e09015000441d140c1b0b4860310345034a030040180400b0506548500146d00e403507405625900100070800e840b0300050071010f000d030407070080740140400640f512040b20042c0c01c08a44030f070150401a035108000c0d050500c1000410456444440c0e0103000c14448100040d5240300510700800b02c0545a540729074100d003110038008d50101e0b42200700100e40004000820402e0111020f440c0000326201c2c1000e840c5c107044201090b06001503982071100c4040010b042441d0700d21500034803903682a5521500c0d405422030303550520480141011403403100400c8a440e050b400103008414500c2900c0840007064002034100700d00342c2c0700300d202d040444480502c0c2c0c0340510030b041840301c0c011a49407040c414107030024021103d5207400c0c03010200401c00301e810740d594444510020300601036445007101e071528201c400081c2d6a1001101c1d445900c4040311100c0011003607a01d410003090703010690b04446005100c4209024000380051140004003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 348413794 1250 348412544 348412567
    0xa0b0403020f03070f0b0c0403081608090907031d01060503120c0c030a030807031103070c030c03090801050a0605040e010203010302100c0303091b180608030901030f2a0815090f0903 80
    0x703015080d00139000c030584170850382000e0004902c0245600390f0b030a010081840011606415590003004501c180100407900c5d00e05100700d407207860340c041d510480950821980c568590403007401c55110040b0004110807042203e800da5145d4025203a2580000200c0c401c00e102d0b880162801c203041004984070041c0c060042070620641c0401940003807110b1b02082002601401004440424420071b10303d10f01d404940100407000300a001010001040d20006c2403621a81142c006030044100800450810010a40003404584141070182d8102400d160744800306201350f0f4102d90300500390904000350490100d40f2a00c0b036aa045050540e6044d880b0041102012142c8802e0101d9019480b454100460f0261140140d903002c0704142c00d0500502000101000b40d170181c4a00f030901190020032540400c2c0a4010400352484442a50340074085001400c0ca09096820154aa0302001c1d11201e140086807040001c02d9500070464030080703040c0345009241107501140d0f0100307a03030819030003038603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 348415044 1250 348413794 348413797
    0xb0406080109050f03040e04120c0614090c060c0c15040b030106201b040f18050705010e0907052b180605060f0112020d15080303091603050a0b0403020f03 68
    0x1030300140c1d9100a91020080100404500d40265100450400d0310b014901d00c1e591b03000800041c40ea48450701b00c210614000c800207281a54842401c0c0700c10b140c0c401c4440030703040342160300b13050f5846541c00c0c40e48642410300c216150f2044080251620300d0344030060203003070100300d86880d4400d201003200180d030310f0000f0082e6005e04040c2e42d4404120701580c0d00810418003c0318041d4183d00b2400a8060b114001740300140050b205650118142c40c55020290082c40c8c5481054604070042c10100104040440d001c41541d07000d072a006245100b00051142e0780d04c0c03c0301d400000c240100042403091210690b0100e402d2090307404003c42445c86020141591544c504600c07440c08401c020710304004490288d107a0248007a12000c503000641e0b00020803000c60780e0450a01c40e030b0b000580001c640c0c03207a0030045010042200092106681f0204190b982c0d200b110b1800450099070682d481c9c54508a281c2d208480e000ba00510351002c1e944c6500221f1080a00100e0551150200d0344019903000e20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 348416294 1250 348415044 348415049
    0x6010b07110f210a030806040e03070f1e0503040504060605040501050301061206120311070501050c0307060f0b210105011a0a1d090a0204060e03060f1303050f030117010b041a0609040b0406 83
    0x8001d080104c80501d00030704411009070101e032007241442080c06440b04000160744505400440c0a00808500d08140014501e9950401601422001000240b050001c003c1040701c800f1740f002c001d45690b5100c211800d005030301450303001406c1080100581841206502c07405540440001203030b035552124100c1581e04076004070041104c2da080c4042c020814860f2000915081c06c1085c42e040702c80400603200d100300c840081c60156175603180c4030018070f51b5000d1580c81c0f0003d010400c06152882d040040d4500f540010341c025801c000001c501d4582c140340100d04030140f1141a42400003105040e03641031201074640d986181e03125504902980d90350041c0e8003c01e964140140e5444c1845030051003120004901c500a82c02481409400c0c965603001e6039011480b80444038507420540ba0880d036502c141c01e101000c1c00d02c044008956515180100042c400c5020001c101d401c810b001440140d500705440c503241e945003818980c10b49e003007000051851902c0184001202c540c1d0000040c1101c2494 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 348417544 1250 348416294 348416359
    0xc0f07060e0102010f051006051c0f05040203190515041e0c051009030b06040908070b090601050109060e10080603030912030706050f160318150c0206010b07110f 71
    0x1d410400256020300ca06481e54450100510403490b0002c0341004c0240326200714000c01100158400d0f143e211034a5051b64403400b00c10500141e812100b000002d80340665050f8841d000d00c0d440d0000d409042e42c1c882c601c19502c5006880c00c0103208001030444d40004000744e0b0000d500d040c0d81248a60b0100c00e41d1070540c82211141311481c20402406070741310011121a040c445a0700c002d00101d60442e201c141e01130b40031034021400314114a0807060328024440004e041504640605c8000c00010980300e0503a20281c1c1e41040c429968141245c070a0071a15400350020301042110164a11400e8119803080300a803c580c9044802d002003058110300c2041c035051070700041040e008004580c01010740048100751004101e00f804800d1000c10b1116101040038903641d00c40651604d4160300c22000465005903805038908800103c8030007520854030b1510050042c3c8002241c5400300000351440300340c01903011000d46131a10140001c0c000344180869118842008074032100001c16000007148600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 348418794 1250 348417544 348417557
    0x504050609011112010b0f0f0d05041118041103330609010b040e090a0b0903130b210603030714030a08100e0c0901030b031b031902150c0f0706 63
    0x7070300050850f811181c5120114500b0007507030101443c0604543d042d1206821259590700020701441628400c41452110800d4041840c0040b00003691009100d03a00a50314020355a00000400ca140c0215031580010700c40540c01150115000c450700c0540e20f00003808031055403800b4130080c41309003c099001140c003aa02c030000344109032860b036401d0300000709030340050b13440d41030a8143ca11030081d4040c600b0111003040018940c008100281c1400c1500004d0165071818040002a140d0340603601c400e00701c00102000140e02c1f0801001c441842000c50402c01180340c1303c0c1c3c00c1c07410f0814042d00740d5500d480305011850110304203980d03101030032952800550395a1080c440107801804010301c0010f80030b508480402003c0c00182c1840ea2054101c85003590b1224ad1200503002000c0c20514070360148a100d0401040144203070309061038050407012901c4045408010080140c29514001d403c1078894410440c1c040d1100054200c5841900071703249511f50140445113803100ca03601100010b105c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 348420044 1250 348418794 348418801
    0x1211120a0c090c0804261629010b070602070512090307060e03030f0d090f050601181104030807080712080412020105070f260405062508010b0901030e0105040506 71
    0x7009144001082501c00a0100380409075000c0d00113500100301600715840c0c4c0d10048990348400030182410001403020607120080100b180e1450021900103ca498045600104200040a503428403860f01800c441075071742e0030300c1c164415a404c5680102d600075001d04c441070002c0d90a00c00c0d155000390341001c20b51a220760404041c030f02070341d0750310001c107101812039030030040c0e10f0101c00c9030030300310401c1d0b915a60b0f012400c1244009240d090f00103001100001401d600300000414490f04071a080140c00034599030302d01c02c0030225080c401074054000e000300420000141c0751005402524040c25403142800492380720031298012100040d400100c068040104000c48a600c484007140d680c030081020b0b26060b50f0281c0801c050340d0b240c4003031008003803e040c40036a030602d920b5041a42901c031202c9504041c0b800300c1c1e461000740d40b901e1124880715030122000200c01d13014200c15205030340d4401039928180e035005140d80a800183c1c10182c03a0382d00c0340187c807403d00806008500c284c009004526 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 348421294 1250 348420044 348420053
    0x31e090c2102060315060703020d12060501021506030a0803130b0109021c0908090307170c0103090206041e030c030f0b0c09031e0a0c0b180411041211120a 68
    0x40181c125108a0300700d14803901d1850095040c9158180d41600c04590320388500f410010703407005200400d684050002150b204160707010411807076000c4035446a442144502c1c4a80090320f020780a100e00503030040d010040340c228604010342e00910090207503030758140309407280c40082d4004c44203071403c0700ca0a0300640030420001c880f40e0040148031400c40c28202c20f446040c4241c4900110403e04a40b108810f43c1440207031421104440c2c00101160941950b424528010450398903491015011b0500d4242c81540640101f510643e4014a4649803c0c104640000b2440d028850040e181c5494640880001e41c00c00d5400c01444c051140e041003600c0501d0880302740b52000700300d500340c46824481c81400340c8000a0008038040002c130388805807000003440710724000c00208090314040c00f20300d001030042013036401030042d030344820340c201c40d043e08800030b0005448050603c50300000c000c110401c2412101c4080007840c500c6442c4000c4030881000010711540c405441348841500304852200800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 348422544 1250 348421294 348421313
    0x3120e060718140d02060d0b03010f06050a050a15120204090207080927011208090d0303061502060708060108041109070e21031207050409060303090509090f0a060c031e09 75
    0x1410084000301c49010401d000c104400131040c00280144d001180c40c05000115070858521210f024008119000c40c0c241000081c0c0041d210341c0d03024140142c2c000c40c03030741482c401da03605880512800c90f203002d44401044030402459000f07000855801d000200ea070b16040c3c001080399034054502c1c1d0342c490040310200300c40c80300c40e85004502c00040e040b18101c628180d036502411101081c10600d548543c074144081c00f44a130780103856004070100f00c40420107805a00a50030781304030015030b59a00480350300036a9104000c2c2c0b815000302e00b007070000411340d40c414008280d00500c5485815000a4600e01080e01500156500030100d171015000d55051300341983c2100120710090300d0b020b020320704950740310340768400c0c07500507402030000750f000414081c064400c03100201000f400c02c0152980d241001400401940625407045611074042161a000017468000101e1208058055000d184d61140002c002140e1141c0030306854021124110201c00000c0041174884180890725070702d44e10308000706 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 348423794 1250 348422544 348422549
    0x30112030305011403100e160902130503121206150c100e070e040209100305060c1e280201060f060201060302030f01020f040b0904092405091903120e060718 69
    0x8104080407213280c958000941001c4413032500c1002805156820905040c205044400e0903180000d40380022040c00356402485c0122042c032200d8003054030307001010707100c02903003040110054080c400d2507018004081d0480c0c03c41001001e100080d80c1d0101c90303070000d070401c1c072004200c1e41048001d4880c0d280f9901030b07a40c260a840c0701900380217081095440840c1000342019000d2494100000e41440b103002c50400a9600b00301110b4071840c0c001d59503c0e0680c0f00f0407500041410240549000603008810342d010690841da0b29a03065140d000b40c1303240e00500703c5142046640b03801c0c0015000300050680740c05030807240d001184a9056005251401e41502040c4207039030b104101a62101000b003080d60146c80e5440032060f41e074000c050000b4080c2181d9040a0404054030400040052001402c41480d0380c10311024821980c45070020354446100d401e120100c102a51079900c0000c0c4a4490800d201d000728500144000c0820781042c542003048800002240e01051703a665800f50f40140d9100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 348425044 1250 348423794 348423809
    0xc121106010614040b0306030c18041e170a0c060501090c0206090a03080c130b0a0804140609071802040812040f080c131802041a040c0509060702010c051203011203030501 75
    0x43c251540300442040f80302c2c0b48141e0130205008004a00c05079024080705440000c01008034146003460612a40ea0716003d03102124a0081d42078249121042a2000140203030001c0c0e80118401140c0030080c440d5020040144c2080045100b42000070302d00e1082c0c49c0646040c00c00001ca03c50b02e00b00c0a460a00e001d80000c3c03072070b40304a0031100043d62241e442603100ca00a41040c3c0c0f22000c000c1004c18500ea00e4100a213030160200d503407403da80d40907400034070030382c0109503161071522516a002e07282c9100385c0d0078000c1c1703800414080c444814640805855000c480c0d800519140d911421582403885e1420015810030340018100011106840100007414030840a0300d1900c800d80c0018440c0030035030b00056622910b030440319205a6808202030341c215000b410a101004101c0c10aa401440b49681036100304d10304000900c000d8802e0080e1011083d002d06900d152420313940041d110100c004100310f606100b000e071401405140c08014600030300c000724a51800303c02c946001380595005810620 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 348426294 1250 348425044 348425057
    0x40b0105030603030403032109030e01030c0e0d2003070305060106140a1b0602040b120105100c2d0c090507031a101101061509030c050f010914010c1211060106 70
    0x660b9903001310848003100e6050400e00030609540840c080b000110a990030341c0b04d4036240d090f0080c1034001082e00007c020990f01005480451401640d51000351030203036401162544c10f4070001142e801c0b1174282450301d9080705540c8010500068903124140c3c10451300c070b0304401e0040060580003407520842440300c80010b400c10802c014001c0c5491181503581130840041c03485541440302d02c1c1d0484002c3d2002a20455446211802c11aa03040c828441c140c041e018645810403003e02c0307002086071440e4401c1150072074403403500c044001d040a00402d404407044a008a40001c1c000b014031100410502d600410980742082c000740446014416602c819448840c50f050103a80d034000b148021031240c20100205d5800030b2529004240c83d400c07480d03c842c3c907081800c00d8207800c449e5000c21244604009110141c881080c13150f4100000205408a6520354040c811902402c1c00d10092100600d004a41c509058a4080590540c000b421001c5082030b00c110168031420300889014080c2400d01c42c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 348427544 1250 348426294 348426301
    0xd1d0d0806031c0c0b042a06051812010606022131170a06050a111b0307020405070302070605100602030f0a030912021c020c031507020118060506040b010503 69
    0x1a40302c42d40c07011041c0c60b4443e0441448242c0b8092015442410b410180500f05407070a458414808503103101e0405141b01081d0f56225480100750710302096400b19a03449091001c7c910f2142d807030012142201d6480882e10201303445198092182030000e20007a401400d981e1181190405103140650b002104c00030304004000f1512500d4070004140361000e41d005500111860644811031000d4004440d400320440712160f500b02c0000300c21001501540c003c00054a5600307480085502032651800c0c0d0520500c54624003001c1000c00300c0d0020685403c0d6864100140d0001c0c04640c801c841000100741e0100325075051101700c0c45140c0e13004003001821000b082c14414060341c0c0340250880f8030810301c030008211105600c6600202c09080d070286c920b00011207200c3c1d0203034481c0c640000c103214800030b80042c00021480065080807070400035002c2c0103110345420150803d0b8100408100640d900c1d4013156808290300c51406071040c1c0100e50028075800c200d001c00080e509100d0300c0c03504200d01401413 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 348428794 1250 348427544 348427549
    0x901080109060b0a080613090b090c01081303050319050a05011a0a020709020903010e030f0d0e06070804200d0302160b1219060b030702060a0b0108010308030f0a020d1d0d0806 77
    0x3100c05405507400d05c6200c5030b982d0000608118440c10000c040301d03080144480403c650688814081d40c204820756a25104800044868100403035101020141d004000008207015500a503000080807540c4400207502441d51130a90350309483d0904c0c10703940d5500400c902a10742e0042c078404440320160510384844003070700950300d11081c0602000c1039800100e00c05540e40c02d50110f29481154801d40b038a81080011081981c0c10641e600c1c032055007083d0f880c440081011900f070b40b0604440c0c0318a003a036152500d4412840d4080500c0b00c01000407482d18005c1591000e9003070b103610388258000c001202c2c0b05014014074801c607a07c800d140700414800f03a190100c161003141d521461000c6608070400511400002620490344813802d00c810000a21201aa0200d60a0321481c044c6a050140010300070044410060903c0058664403040c0081501031003401c0150350011f18010016003002101c00c0441c081790210a4144100d03407600070802c01650041c8801d010b003007101e08014046103045e801 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 348430044 1250 348428794 348428797
    0x7030312020a0512071116050406050f01020703060c0504050414180303070c03030221011214070303120905070512012003040f081c0f0204030204051305030406030b0f040207080901080109060b 84
    0x28007400c0f07800d08800168515214070f80704c0750680d03806130407201c8010144010740307c0101140921f500442c1003c0300807030281864000c1c1c8051510690040403900d2654a42c4001010001420810000c040000052070b0740c50b4000c4e4190782c000e4010303c0005007060f07500c080e0041006d5141e81d00742d40040c000c01c29001c0c1c20400b80300e60f0a40500f000750b503402c4200f0b08854158038292070403500750402000484c400520304115000c941c4118002c29160603a10a41681c0d2140d40c030006001481860100010030420740000d00440c0c8181c0444006a4442d800146030701071000840040303a64038142c0d44241d002c11501d202039a070b040d1890601c2c60a09865030f0b03440084c81c20f40a00800780000b80160030b071684621204580c106154200a900c40e4252408003a50251006038419418500800d104509618111803615403100045251601d4090264050111104401d40c0403d000041c2145a20b03079000604000340310304041b50350b60070408009849004180c0003044400e1901c413040c040c8008080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 348431294 1250 348430044 348430057
    0x30a03020705010c14161505030411010509040e0a05010515010e24040b04081b0907200a0204110c01140f04060b0d0f030201090210030b0904110607050f07030312020a05 74
    0x13801c000440c02e40c0c248110b0f40040d6500a540328858843d049801600410740001030f1a0940210301021724a00801c440501043e60094400312403910400d00c1076005400502041c000030700042466000300004034244101d280007603400303946402c20000c12104516004403260400d080c25840310b00800b012a988048900c00c1c204012084201813004090080075100104015aa4181d50329142c5458030b03280c10814050348082448203003080c00501d44610848c0c814801c42e69682c00203154540c0c1c40c03010081d000d40081d014080d843c91200581c5880c0a60500075140454440d5102da5401c805800c49100208210481110300c0c14418255400a07040e074001da003020003c103480c64202c000881c103065802c130041036106c2c80f8442e803041540640140040a00880390184000101d5a0950685d03031714104282e800f098520004000900f2298003407020707a005002e540c2840f4207559503900d0201c0c0380e000c000c0150b000d103100700308043c3e0282b0480080b086200381981000c041c1c9002410500504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 348432544 1250 348431294 348431297
    0x8090106120b090a020909030a0f030b031b1507060911030109020102060403080402041e05040606060f02030a050d0603020d0507080106080a02060301170c041b11120f1305040203010e06030c030a0302070501 90
    0x2000ca1203c51041000e4011a500140344480d54180400460380d070f81d0000303c60f240810717450402c84070707028024400c03502552000b03070203441945008580340c1d403c80702c080c400a501003d4501380c890440c4042c00681012440741070f0010740c03641c041c1440c010000842e11401d100c0ea050002d060011b0360302040c1c881c0c00540c103041c0030a03ea02c9520000b405014008104c402125010310329200030081500030b5802030340a04401c10009482d00f4085170f1480d9402c01344000350740704000580a4a1003100200000e40380d2000004040b51a94006075181d03907628004d031840c1c0d1000b503060012078000e101e401c0080c61351000802034400141d01103a481c0c04148554222081c8040b000140c030142800303d602c6040000700b003003003e0034161282035048540c1610f03034000980041407403a0481000181c15056002070880c1c141001000d41400700c641c0d00c0308201d41b00b0b0005020700000d076901d0f0b600280d4081e040b80001010740c0d19142d070505280200500903180301303521140260b004260003040301c6003500c80a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 348433794 1250 348432544 348432563
    0x81e0c19030f061407030c1d06040b0a17040c0503060f19020a0201020904090602180d0c0b1b010f06051c0b06090912120402030616050327060f06010809010612 70
    0xb80d0a1030340081071003450741c40721900d41000300004c259060340218510801b949842c548100d0708400038202c404042c0900ea04910b08000a108442e0308501500c1c40004503d802c20004404070407a6181080644003214424403240d414865032401b80300d20b9511001c0400080290710b401101d5203001500302c074540c11825400102411001d100f07404645403034402400c148581c40080c035064000794013601c03084030212401c6e1032200302403415070040801d0503000a0316001715424140c000c3d42e594011041508451010464a101c0b20302c28015084903820524002a015140409000c002c001452600810144a480308000201001d0301c15800200585210620b80e803040b40c400c5c500400540b08001841d004101c120100a504945621681c402d80c02d880c40c07503c80f44031480c29018400320031070205406100160304d15029000e0207855161080c0d8400c103180301c140a450a2440a0341c10340104040c17007080112650308910710b00d410001c1c16008201180c605920241814107080005100004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 348435044 1250 348433794 348433823
    0x21020a170705010203070c11010309170c07030507170738130f0306201b0703060f05090d0f0e0904020406150804060b0409020901030b0907081e0c1903 66
    0x8500d81a00e008980c0300008642e03d0525980c003a065030708000d005c941058511505001c694824003407000410350000060711403150482e24031009402c40042c40045109000380003022032010016940200001040c01c1c20208031020b0050400c241500401c0540d21508040201a02c042d44c4482d03005c02c4419411029581d04912506d152040c20250900c41d50183c00208104100707800300000c0341d01c0340b98104802407000ba116014881ba5207459080e8003001e2254201c1048202c0d00f2a00451003502940c03802600e96450104844d05c2c9901c1d00c1c10590b0302c42c1009010401040134030001490707420304061803145c2040003000742000c10140d6010388680c00100e800c41d180c540002c030182408112404240148120080290504850655440707007003407040761150801e441365801e62500944110441d030300f10388401c0c43c2d03d0b0000d06011150310440500052008080c0980c503004003074240e01d854801d44400300c081c40d0035070394888184116011080145092403e0000404480d4080f600c419450b9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 348436294 1250 348435044 348435083
    0x901060b040e150405010803090405090601050a0302130b040903030507180f0b0d1b02030a02070f1404090f0629120309090403090b07080409060b070f08031504060803030421020a 78
    0x70007030485103404c2401c00001155690010014044201c1c080e01c04002d599140b094181c0e681c1310030720556400c0103802c0414005410000c25010100e00f0340040130403001d180d1000706040f22411041030780025034a105000b41654001c080f40300d00c05805820150f014205140d071042c461a078464982ca110380018601501c0d641c94000091303400041c5104642c0312021440030392a6403003044464014010000301242b5018810300c01c00075101c02a841c2140300300301c074003840000d00140c0000ea81d1081d9000c03403640041d045001c0d0244000703d90030107003207a180f408040c0b9500c07500044c001d8811035100f032b8040031840c0004140c40310800b0484c1c09150310380303c5050a0714144030a07041194224800552001401086401482160061802000210f035101c10203191401041d034000e0011180d03014070700216030400081c0d5006a10260803510789218440014100d9105501030101500b020040205010030800c46150642c1a14a071201c0b551640a00030344070310b12890700030960350640000e0030202 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 348437544 1250 348436294 348436321
    0xc030607032003010306150e070f03020706020405120705010e061204111801030c0602070b040303051206120a0501090519020907111608100b1e0418060c05070b0901060b040e 76
    0x2e07004a00460b41d03544c507030a00a0103030604400310082e900e80d407000007401c01c3c5407040c1541b14000e82e03607601a005203405070807800f030341c021001600e40d2902480b01055941d1290401b140c510301346401010a107103810009805542804d1126118074818815881c5c1d03041440451540142d0000d800d5045a007900002418a4a441d066040c0c10b0300c00300c00803041014659008054070780350f4007280d540c80d560702d030005214802d07400020300059003442220f1440403011501604140010044201c40c04002c05140c0346c42241e46058400ba0f44403600402480402d2040c1203615050801041c1022025004645640c4000d09004100015440348001c0202d06002c14900780c01100e110130800c07036407012815501e9030712100500d061440c0c0310722404c0b649031103460300c0040701c1c5022000e0400f01c002420440200001c9504420b1500c4580c0700500042452184805009003900d48584490303590420700240a4000e1880768107030724101050241410940c156405c45d1410946036001d0359035980c3c0344402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 348438794 1250 348437544 348437591
    0x6070f02210312090723010320091504050604050d050a02040207141917090402040b03090a1a0907120809041401090c05040e06040903171003060e0c03060703 69
    0x10030840d214041e0020402200a140040b14407210380c0c1d1a485001c0c046441e40c10354840c0d502083d0045a101c0004c040d181440452504141000941c1603000140d49a00700710f01c840300d40b0b8075200042e40c100e0518054000314850407440b140d10b4141420400030955511560041c50300c58035169440404102d410007a00b180301d680035006540b81c21030b600d085040c02c0c0c00001c21410f03600a0700b90060507076801d401842d40042c1c116103c1d4014603c004d91740f0348980d01489141e500140c08100200d021207014005500030b00030711000b85a054502d09050429080101000d180c4010420074080c1c2c0550024200c0140c404404201e4420501c0e80750a0025124170481150440d041c441c445058284401100b070482c0d0740d000c4284a401d400d040c0c104c0d102c0c42240214094034a0500c08100c2500b0309a00124540744681080424004031a00e003111600d070440e10304402c00c4044006204001e501e00481c9022042d0310010002c0080c44400a52241c9000f00305208155403028112610004903004411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 348440044 1250 348438794 348438829
    0x3020a03111c0b1009050906040b340f110c15070212010603030219020d110102120c0109020f12060f0c0d0f0209090f100605031f090c02010e0c06070f02 67
    0x256031054941100f80e000e08a8414002d200380d04800941856107000e00c0e48540c4a001c080c115603661907841d074079684405031001802c84161221031281818001d902d004414480300549400782c0404401003001e803a620654003007100c014481d81c88031000249040360f03800226007001910058243d01941c2e03006c1c03444044e50103500500074540083c019403013001542d00a40c2660000c5c03003100002d00303c4008080000350030540c0009032102140d40f160a111044030144152550003015405a00e4240c10031074403502941d559000800071840e2104210b10440c0060315000c6203065540c94098407504001c0c2100301c8980c100700020721400d07004084501d15440c2010401c1400c3d02d0054440080d0001500c143c09a0340700001b042d2591010764816114094100e1a401e0050420303408650641001d001c065040e48152090070084000d001074070042c1803043c0d00050005030019000f400c0d03030000b96080700320750001d010005154031140c007194070850308040c46100003040d0748007040b841c0c224110f1101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 348441294 1250 348440044 348440089
    0x91e150312210c050901080606090a090504151b0801060906080c03060109030506011413090203031c0f090f0506250c1707030806030d0207080d080405010b0d06020a0909050103020a0311 81
    0x500f825080b4003d0180c9003400c1c0e813040031969035201440f200b1310500c6072050703100100150801603100d40b9085590700510611540348a004004440707819500400824560662000c90840300301c0d034003030440341c0100400d1421400751441d04001400d0302038044e058108000700080014141d0740520107060066a100040769115a5622045007021851500641c86a111503441c0d44c1003c14a000f001902c0303400402a524201003510340a144a02c4034080c1c014241c0c0380d40b441c2301106c00d2032150804840c00303000080900c880b9441e0030380c141030005100040078060741c0d000c03002000319010321182007000da0801c0502051a4140008000b040700955032174108005019000c0503031100100d03014210960441e00754940c00034090380c40b10031030302940e44143d104004039140c0700d1080011a0300f19000300c00009030301d082d1801140e0f401d441d040042d43c0c1d1940010f00b1000040d80941a14004c0c00003000400107541542e002800810740c622002d4805100d0000d641c01c1303591038507984800e002e00d01002c034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 348442544 1250 348441294 348441311
    0x203070b090d0f1701050120151902030403090b1c1104030309080d02030f1312032f0c090a06080303040609020405310c091e15031221 59
    0x10b40d02c50000319240d000500703505080020034020014000100c01541c5154110fa080c840112002103551035901c0243e1601c20190000c442e0600ca20128941c0100050205243c1084421000f44150700c0000d15682b04000b0440425808a810401e031500070400319961092201c40306c002d403800300c1d44c904109150889458011404c04d00900071244641c0f00c8a00a030780c2da10415465080075400000546c0080113484e0100740c00b04010004e200081c26211060b54a40514a543d1042118100c0104200181c00080300e075004480341840c14030351914004040c10f1198154841a9080710b00303000c5c9005034049210b4108a41160001e00404401c4035103914241c01c2020243c200381a00b42e00440ca000040382d2008100d0a0090a40017070401900f019201a1400c0c1e1001e500030100341c03010008040c002c6078900e031078020040340321501107444111a03907130120b100c1141d9004568a181c2c1100f1442040042c3d404065140380c5007050625240700740c48125403c4181007080c0d6114005850205079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 348443794 1250 348442544 348442561
    0xf040905030c1b090a1401060e13060801020a03060503010c0e0d0203030910050a03270201050d06050a120611070f031209050a06051510051c0f020309070e0f040f0209070203070b 78
    0x4403018890300304c031041e4568540340c1c144000c88113103c050300d18941c4010014054240220348648002e08050116500e03c821004180203c1d14190844900c1d0f9400081b0410716a5050180c1030191100301c00810040421110281c003041c0180c000303600800e59205103000b5960240f099a1100300d0142c110f9014044800e80140340d50321850b41f5402180c54007002101140c40e6120380c0310b8030071003c64110240c5129400564254001e0906001c80640700c081c081065110003071040003c01c690070f88100c00da4030f84d2612405990300c00c020b60907100014001341c0080386010b880101c1d0241c041c02c02d40f05403404051020041e02680801034840e1107021300a80c104800c9500607482065014000c90950400d90100a050f12180f440780e00002c406000b40e100c1c1c4c402200030742100103001c1000043c0f401c80360a4446c00c2c2d81080382c09080c5a089818200003015800e94251b44c486c090190f0b01806162036519801800101000613008482240024801500800c02c1f00d002a030070401200092528000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 348445044 1250 348443794 348443833
    0x30301121704050a120203030d0e070612020c0309060c161d0702210a02010204050307140109080a03050d05060f09190e030a170c2107090f03020f040905030c 69
    0x200c072034031005150941809490300903501a9540100466102454130200005c0444e07010003c0e641800200180182c212aa00c548005412400054485c851412001412844610340c20303c481d240100484a121000031040340c6910b00203c6002e61289400710351a40b03090118ac465482d90002c810000c22030b00c0319400d41042d6260780c035000784003c0e556040203c2c0c98005410038a2403490145140c40521150380000e060b00305a94030005003082d0b0381d00002854841e9175480f4182c1103484607a01d1806580c0040110301618030780005100001340d580d00104188106080409a2a9100f000c0703030490780c032060380c0000303020000d10f0313010642090409072401606132110a808589440001200d680c408400d542900c8540e40301e85410584035001c1400c4050001e100480d110420401410986940319110400320041c2d020136405150100016208007005c4d0801109034012940400040c0c2c0c03040180180510180c81c0414900301074581507186018000c03e08047e4064036544961186410300c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 348446294 1250 348445044 348445079
    0x1e020405040b0f06090d021f080a140919030c0f0308090105090105060d0204090c080607090f241d090115080c070308160e0a0e06010f0f08070f050408030301 69
    0x103070104450503507041040403100842e400369400080c1030118011501c1c0004010a40c2800507090011280c4a140341c80301003008018000003103061007052101e0681d05e07100310f501801e0303c040c0700000c1e418075048880d580c074016980265940c07648504072003003612038259405004e0380502801300c01040c91602418000c81185e0220303440d0310309400615175135014002c21b4060040606281000000e580a0102034075104000352410700c1c3e43d0400045102c000c11099200b84203959074150010b042c0b01c003030140c1c1d503080d503c0000c1c0b030340d44011a0011010a0420010b00e00709074144001800e400300307602d0344d4007101084460345c00300741980002200201d5030020030901d200d50f55040c4142d034601e2010200c40c01201c2c130150003d800040040c5180e1042403c0301840c04103405c03c000c140d05404c00142c0b40509a410242401c126442417150a580009054200c0c6103a030800808015054000078441a00101030000b0040c8003800202c1e484d00400440b0b010340a40c10503241d4030340e10b4060f2000081c5481 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 348447544 1250 348446294 348446299
    0xd080703090e0c0904141b0702061b0309031c0807050a120914010c08040c031b032001080708070c0602031302210c0d0b0403050a11060708010512070b0d0c02011e020405 74
    0x101c410070190418072000b4440c001c2c141c080c80c0a81c2c647d50307245404d9080b4050881c0c1000c1c00300070700049034000d9035241001c500050300865070b4031401c5080c141014501c1b2030280400c0c101c4100925003c0e008100c183d0b04c00850704e0103030b8507014440f0302100c0c021000c51002c1012407030481c1000c14010444030402000038068004d1001003645202241c89020480ccd0140c4070094040c3c042c400100e80780c00c202214502052901101c644035210306112000034034040500d03200090310f005c802d58006030015400080d40c10030400780d10b0458406840044c004000900366640040007901a082c00401800355580141640d040e4030304200100300d44c0c6498075032000c0a4441c9240c176006078034004031029161640100451066251650f098880e504103e10b0740e000c5c8501c200c00b410b041d01c42004054401e070015030b111000c4e54075040903c41c0201a130b10001000ea0000300042c490b54440e40e00f01c0f03207005140c0f40002000e0241c038030228010541400655400c1c00c1c2e0711080e903d2401150098420348204 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 348448794 1250 348447544 348447551
    0x90f0109060f140f0a0815040b01090c050909040221031e0f0409020c030417150c0f0403033516020309130906060515040311030a020d080703090e0c0904 67
    0x710311040074014024460804109200329020125040024a106005a005d040540a261100c01540c1855070301021031011500d44c0d01040280510601c81e00d00503c1220700c100503046d140b840041c1369118010402e030140e400c1c4000700e411504ca009142e00303d551424600140401c03095416607c0f940443c07250343d49880301045540c00f40c10b03000c045074030382c4024003030840c5014a4410040080e412004d10440c50740400d220000f5100041048003c0d04107410010b00018a40700703621100d8201f025090307103062902400300481c545000c0c0b04444c2641e4041c10100c40b042c0228040100b84100f054420f42a103d42d2608050304018074030015010f40340090150020425400040780d990094941d050340c4000818001c0e41c41c00c800394003000c0c1c480e01649001c41c174280c47c1d1020035403c0d089048400f008810004041041c04440e907400d0800560403409490b00f804107800240d084244984041c2c5101300c0091004101801415148010034a00c1030110840c60603000307561030381c0c001d040c2e0280251705 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 348450044 1250 348448794 348448799
    0xa2102180106090e1b0a1e17060f03030d020f040f080c0d030e01110a0809153a05010f060e030d23160507031a0121030e090f010906 58
    0x1410101810b8a04035a50344807075901d0104e40c4410050060b00c03003200c840395a00e92284042d0f1000003461180d0307690321020345000e10221600e589081c185c450008005000c5a62500009504c2c8e07429081030080302c22020700804200040e0030340c820a80410a40351002648002d00343c2d0b6080603000300c0740d104c407040c070015694841e00385c2c9903114443c449510030342480c100070001c0d000f24100c041c0040e0600d0198070803203260040c20304d00308000b14103449290002c02ca0041910300310301441d10404901020900741036a1405000c440581c0e030b207a030020101d800e4002e601000a002000350840520389050141d0b5a450180420360400ca01801001406000c40387c021401c0004400c8079007030582e40c4c2c58405a030401030001200034240d1203041b50900c2003000c040825024405410346d81e02840280494900d58504031904190f50160f00f01e8440304c0d01d0040020b075a661001e10740d025544440300e440e070009807030212000a00e0041090307202041e0b502340329103055501c0c0e445050303a0300807004006464 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 348451294 1250 348450044 348450079
    0x40e060106020c0118080d030501140f1e030a210201050f060105090d02060c010f0e0105060d150506010507230d090f05010e0a170303160c0309090203060a2102 70
    0x20240035040250f0f10254248159501c41d400d10307220030298000341112652281e0311181070505065403003000039202e034010300403103d9940d1225020a41194007100118150010850380b8215000d42c403003100c040e2145100a44043c01104111a4024402144010202e0304107421451040c4000c00662030f01d00001d056010042d40640585016180e560400f02d060040001090345c1071001c0342c000c1c401784415410581c00f40280005a80411000709598040d40318403070031650010602d034469012209420702049503102e5043ca05040301c42d020070380b503884030010b880321302c2000002448080034040c84040309400c4c072504084107903800d00f0b40d0503900c0b0160049655010600034041340c2e9542210402c0b07a9070041e00f01c0f100701c507030144c40e020a00b0340d40d40b0206d502d04081c0f00c0340100c0f900000b0400083c05451440807942c50700c281808000030f5655103000b0402441030244080340c03540013000c03c180307646c1d0190303941c010480d500da144d000c0c1481e0742503500c0d800340c603400490044038426594501c89 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 348452544 1250 348451294 348451303
    0x120c0f010c0f12111801020703020616030e0307050d150905160e070801030519030e1201090309090908090105030a020702090403052101240903120f0f0f020616090b030a0506040e 78
    0x2041a440043e05054140405c070a9055138814458154819044000010b0b1195009842c03800000b0aa10060300340c42e08000e030103050040003580c865000500d080c481d0359242c1281611558120411040d44510b04281c440145043c0001a00b140315407080aa80072580d00358110030364445105520712034603601c03010b8500d04803e002c014040d4108903211780070704268401d400411800303403420780040ba040c900032520121b6020103003030840c2d44488052080c5900314411704010310340000c0821002001d501e44800901565550604020002002c0f49241d03c141d01950340c2c541d0000e1400ca014102890040c2450f07010751000c1c3c42c0709c07101407400049001201200c41c1210104505441211000040c1c40c52281c1d880d078001d001d11590712030103c041001410007402c00074013511400c1e4014003450003c0c1c00741e803c4407203c800700000c0e40c42e0b4046c03032030b07010480903044210310100f00c1864403c01e80594004c5816000440d030840e0100c10085900400e400c0140142420343d0200b042e00095074145803103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 348453794 1250 348452544 348452561
    0x3080d060f050d0f031223090607020a0b0103060c1715030c12030403170f04030303020406080a0513020f040f0c0c0606060504050303030f13140102071401060503120c0f010c0f12 78
    0x956a41078134210100b4010203440354000c96910000841c01d0035035080790303804481c0300c0d1011150102c0034100704000e1002c010b1590800f5960009180c5880103031380361a2220014000103054540360008119658098480601840100004821540381411440401e05a8051114424410034080c58418103001000510543c03008019600d40340c00c6446c0c984500d002003400c8a911242001070045000c80300d80588003452003680e01503a00ea16000c070090100c0380c0506a800307041d2918003400200c106080f60003106540c16600da41242403503000090041040710300c40d0b10400c0c100112420090782c445d000c48182441100304106c20317600c4000442d0640181d000700c40d0558070801c041403400180c4202181e00c156901c0403001421155503422008848800c0744049580d0042a0841001340010b0190404069030b0000c01805183c500025620f5450320b055040803900003c1c9144c080b00103224201140100c10004e20500c503d5a0300203080d500101c008500080e40b808a0070618512801180e00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 348455044 1250 348453794 348453803
    0x100c110307061109030102121501140904051e13170a0f0c1e290c22170a0c060f020601210f0c092d1503080d060f050d 52
    0x1d000c410b540b640c004164091030091603100500849810b6034090000f810400b4030b400e40c190207410108001400c0305c001c0405503040c00707000c0c0440c01c030340e60301c603c103607007407860b00700d6000c60b1540f00da60140000144105c448004c20100380200911188420350103246240b14041c064403809a200302000355010f410182c40c00181c0d05103003120400e00c42c043c0800d10310b019a040021500284030301c500070365190402203454102c0f054402076035801e100c00b0b03081c1d55941594203034580c1c0782036044000a40314036080d040600400f0610320103c5074085001c2409010304805060544441c0c1349556640c0b400002d08584c5004404000308126203d03001c510f07400d4150740c00070034103039080018040c0040d003500c1c01c0c0803133b0031058031120001c2103504110703844043c06110820141814030f03425000b030f68500700c095109130a080b004654205096040c1a0321901407490000e5544040c40010740700386e50b181c0c00500310a0380400e42d0b00c0b0101a41d0f0120702254040500440080d90f10014004013140e480c90141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 348456294 1250 348455044 348455047
    0x5120a0b1315120c0e04051609020702100318140102120603151b0705030a09081207150f0b060f03070f0c0203030a12061e0f0803030c0315150309100c1103 68
    0x303d20000c0e004948046840350b20580c2007180c590840c030000103412942034a0941c40b645020175100c078141b0170750000e031078820b00030f615040e4103030085243c2420301000700b42003550310000c515aa8102280d2121801d5001201c2c00040703a0244c4564040e400c00744002c62078103100300c0460390701d20f03002070081c1040306200490089aa140351458038911002c1501c800114002c0182500085082c80148401101d0b43c46601c012418a14098585900c0c0c114605401c41c04000300e0002c01e5503215a20342d0074540341c0001c2070b052070304005140548040007130240c114501092201c1c800740310ba80074611170f00003640c4080b5250400c50040300c0e190311150300030703425030002c05c801e079040c502ca9401c071a04500030010202d0741c0d41d40e80b0003002020303204284401d100c4a44403014050f41550410360780003810044010f5080d1304100c0c0d15052584000740411000305400c4444120f10303110044401c0a0030385d00b078452178032860045051921682d40810318261a8600098815918000c0d0440f0000105500046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 348457544 1250 348456294 348456299
    0x16030b0a0504080708040306050f0115140c07210312180602030402010315180f02030c1912110909091c050702010c050f15070207030314090105120a0b1315 68
    0xe00081c034000e0070a4030401001c00913100441d0098005000641c03040f01c00141c280341c9202202c50080040c0c0008a81000004294401c194400c0f00104121850302400d95604201c40710145011550383c01012201701c11041d2419209030305650511590082d202d8003582c2c2804603d690896400703a881048191200d201e0901203030041d0b000e954010b04c181400035402040340c03d0f0344200389007039020564800d181c0144804021103800340e000d00883e840d00039811410140715138000d41c01154226504684401c0703c041d64148036400c264010010000108844507500145820f2136110210305806580e084d03003c21254840010038021018070112110324110440000300d52036848242c003a4100081100c5000100d801800a5407100308620000c00110b40f0342d41c03001d91741000c02050f02055420145040010a400c281ca0784060b00400c81c4140d42c81d2690001070f14180038011380c1c80c0300c104072401080180c8003140d00c11400110205e40c0703168040c0c3d0481d104029900c1e5042c1e44c204102c001c0c0c008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 348458794 1250 348457544 348457561
    0xe090c030703030f41071101080721090606050613050603180f0c03010501150e10051b0f0708010204120209040602040312050d06061e110c0307030303020c16030b 71
    0x500080308118603001100303c11002c6445411307400707495600a1000701c659526811803800124050f9081d9082c45d007070400c15107450384800155103202d11810700605200041890b449046811608041c41500320464802000c2400c01042030020071594289480c10100e883d10704402900c03010404450361040b01c2c0e0a00c8103100b0b182c0c001400c81140704800c4580035802da40709105568099810340b00625084860300201400d460041c2d100340400c008002040f070740140c0c03050b4038410140003612030a4641901c41c03011070345480340d004800075180d0703103010b01d17244040f01003060080d03e4800d100302c40515480703070189402c034032030361250042c0200404604401402c021600d01e910134010940141007540c1c9488101281205100b00c1000810006111014203c0313840b554004d0000ca00d8941101c1000b1601030011504400c40142481060041e032187d903a0204070b00c104048019090340e41c129034a20700900607400a581000e218010f504d21846802d456508802c200c9400000580e00e544811a9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 348460044 1250 348458794 348458807
    0x608040b060f1c0b04061401420c3e03010b042a030902010e0402070f080f0a030605090c07140705091509070201090804051903050f070e090c03070303 66
    0x580d04401c515408101c00261031404611a03801060096050300d03040c40c0c400700710f0300441c41c7d2008050742400140446940d620400d07214030300464822400c081c1200100c6c25100c40d041c0c4500351107000d4044c00e150507611401c0018098420035094403402014449007800d20900745480122004030b81c03c0c80c06800f00d02100c4182c9082c050000620304083c070001c1403e80306480034005000300c891218280b460207840c01242c02c4071003490100892a9940d0000f02030200d840f95a83c81a600880e00b0341c2801f00701d0004044580e80190b15035a68041c1c40e482c40c032300b50400c030340c000c0100303140c41000101d03401d2000c031030f0307116a4031500c1c0c5520741030b820f40d907580c0310391414042e100c802e114240300480c0c103484180c02c403400341c0d02d00343c044058400b503881006000c5c40f000b4520001c69040946803030010b104c2c0d0040d142501e0080304e00e40c440418000c4c0b81800b0604651001d03210340710340500510b40f900003044403021350745000803000040e600c1480c116564080171070f106d0b130140c0c45484e0401c0403e12500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 348461294 1250 348460044 348460069
    0x6030c091415220e01050402180c030c0304020f100809010617071710050a09020906030c0108190e01050a09050111040f03060507030f0222140906060904111603090608040b06 76
    0x41c3e4800894500d00740c2c41c0c00c0320841c0300240b081d07a5598007444154548068a1050340080441030742c610310300581600b16070b010203890100c0c2680084003160441d91003800c0c0c003c0e0b0714800707010f0380f9400c11990300040221800341d910384100d500c0c1410201d80044941046000c8e20260710040c2503562070b08ca004a40148001010f040601404068107100c540320302500e8051004604040f9400641d8010888840300140c007030b81c46a030008612405903600308200c0e561055100b03680c64200c80484103410040e01c654282c21060b03521781020446089410b501030602d19000314000c101c0c2d050910800742c6640b05500404e034403050500d104000244117900f0003548019103180200b8901074103400d140503038000b1408011200021a811228034101e0880040200b0580540385559001c61022a49010000c1e10050207404000740b810032984a03504040c0c80c40c13010307607501e5650310701083d2880c247c2040c9040071000a24409400184d02d4440c052003400307250801d0070001240c5940c0200044442e014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 348462544 1250 348461294 348461329
    0xd0b040b180f120703020705150d150627081f1407080a0b030111030708040b07020105060105270a0e0a0513020a050f121b03010615051e040906030c091415 68
    0x1fa24041030b03030346070041c651820840500000d80c03245402c8460f4801c0c0d42d001050790038046800c12080040395030100011b42c0000707002102c00a901c500b1603480904c0c024a8000301c01c54400e40e20301c0d44151700e400c14a00d00058159034200200c108562040070440070607622080040c144c00042908400d03a64400c08246500400000d001c0c186013250044030b07001190a0740201d803001e820402403208400300180d01c02a140b00801c03040c5001400603003940244070380b902c50248020410050760b82075041c02c4001c0000113051145141d600c0c0c0701c102e8589000c6070188000d6052001090115541c5040d01107810340c0100000c01c8182010240803030368042104060340204112008c0c04909003d10003030303a4103a044074176581c0d207003d504141404d541e21944140b452401d56802c40703240c20341c854242c6040c08036081035803202240790902800503010347d0f003008a01500e490340020401982210304000c9407801c01f818421162140c0d800301c2c507808115085694a55101104c180c20701d0048140c001603101c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 348463794 1250 348462544 348462553
    0x30b070813020901090905010c090b03010b070309050306180f0105070806040926090102011103011a0a0c1b1a090a14030f06101e080d0c020d0b040b180f12070302 71
    0x41d40004124110a80c044030055641b000d0075014800c0c28010001c0e41c0416092807103d40740343c881101002d110500c03d590300d001002c641501014803a01180d0700400c00181156924280042c041c5070709216210300003024428200417415005040c000c05200345160b4480d03400b40e940d502c0602014194980f0201c803000a00c1d944d04031406054804501c006422048a40d1514410300001e801c407014400038858150050004100c460508a005609003401c202c1442e00d0b40b840ba84262a040e6000c98010450f03032070342070100040c80b441804101100d0000c0706a0b036407103038440c4903060301e4481d411103d034105072894414441d11200c56a12010708401808903400c06540c040d840742804000d40308200520b41d608020030021000034500113164065224115501e0f00e0883c4842d50340c40e050340304d41d040c014a04021025035450703030b51040695030804c01030015071070300e894000c40a2000b203c287c60b600c03c044140194089002900b0a039000d0090014001000e600c0001000d80c2c100490440c1180324 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 348465044 1250 348463794 348463831
    0x1b0d09060603080d0609060801090b0408090f03100507140901022e090506150402090a0614040b0301080c031c05040b0904060506040b07050d050304210c06050c040501090b04030b0708 80
    0xb0311100801c90002c0401c000a49035041031b200c1c900b510f0701e0341d100c00c1940c0e04210840c800704200f0400207404c1540004030684c3c440c403da012800b00040080c42540c075009281000e1488991030f0403040c801d074007560304e10034040104500c445060040110250059101c1c1001c07840c3c400e004d98080d403110580c20580504424800c41900c16108182011202c1d13070030143c1449041a02000d401c040000308980a40c1000806000704040152034881c1c0810808028011544c00566a04035070143c0403140c0700c0782d0f0740d607160084195100750140d80c46000f80300d60f1000080c0c03a4409070300a900e22007903a503120310306484c10b14400800e070404064154480d40d1044001141c0d55010001c00050020483c8103465403030500300300f800e03c1d020761869801e02400b0000c04c00010013110104a50685d81a18500c09449840341103c0610543d0701c014005468502485038901205003d40108c80c4d090f0303110352232b0385d441d008103c8040c016440000c10b8002c3c0c00000c01c0c901401400c0c0d5541c08401c03094000381148 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 348466294 1250 348465044 348465053
    0x312190e060d0b0301060b04300609080408060702151b041d16030203040c091d07061805010302070c0e07050c010612020418050d030b030c03060103080307081b0d09060603 75
    0x501c0700c074081c140309640f0307080e44245040a016a00050040782c61940c2800c1c5400c0150740c2c4c4c00070007054000a000301c0d4446044140c00101043c141642001041003000014074000f40e40342d1250050146600c100c2c400a100981b00154061010480405000740e54603041d01280403030074400220010780b4818440800c442c21551003030041a5428a040f80d030341c1c103002511380c0c82040c46418000c101401081040080782640303050314216510400001215240c1d0183c0e000e0b940c4644901c0d00b1903000b010800507040b68480640908240400008440e60340d60300b005508070310030110000c2c400380322031204002000a040d482039001c04075003815481c0007100111142162455000700c8000309039a0002c80550403c1d2144000843c8880c00d89000c0038030b40d4890072340c2c2c1e105134140340007019160000a07100380c9003802002c00000380507044583c50350f1203190840da0390704120744200010700c04a00048105200381c00000d08021142c22a40c0350512002e4a035014040550007a030300305488078000400078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 348467544 1250 348466294 348466297
    0x15060102150a0f05070914090615070f05060610020a121103030405100b040b060d110d060602070e06030703031704020103060314031902030306031e070806010e070e0312190e06 77
    0x550719000c000581c1000071150f182125000740010302041542c41060014090003124160b04485c1203400c81c1e825a14400092100c180895800b60400d101003014010490a0f030000084c0600c26001d840050341c0e09d9091013038400501c40c2036801a0300540005003c65070442d460484d1100c10710705403c03202c0c03106400c949190f009440c01c407407a9004108002c002c101e1441031100c40e42040354244075500061001800c0c9008820919219965588000d400c213810340044808030200300d482480142c1c0e5400c40a0740b20b00091080c00030419010700003d000389004a1010103896041c1c81e030100c010000f0f8a14124902c00920407418150b891a022000c1407288a031180c124aa0400070340d80e826840340080307022100403c61900703541c42803044c0003040e6004500e80741440d0288036201700080e2100030710361600b81680e0104030640550000419100c0c0c6c250112441001c0d0782d142e040320a980c8074245a51015043c9032458880700c1070102884000701c407000302c01081140d1800340c0c3c000c1c1c00c0c00300180e180e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 348468794 1250 348467544 348467551
    0x51203040507090e0d050a03021303140109020112110f0705101404050c1212070206040315060e011a0403290127051302060c0a0c120b06060c1506010215 67
    0x10756105081c100b007620102d024040c906401303039002d0030b034920108801a100b80a103252a4040c1600410140103aa8a4110f010021504201c403a400c00480002c100e000300300300001a030004987d41c5212000c03403a20f00a09246950030109680707422050450030f802c070307004140126064002c800c600300b10b0020f5406507481c4240720542c20101c600f80780c0392803460604000d01850203171401c079101103000440030928020705008048025503480040c800600c00b07200e141c0008201e2050000015102c0010ba030115041e2641d0040c61031003a6224242c2e941c03c00b08154035007078401d000f0032042c8001540d005190404504442d1104204c501c20010307840005000d8104c0c1d404440c07185000840410350795081d507808144050200800c0c00e0000718104014000000a4010b4900140a588007030040004000142d00280704004407074503480340c8416245556401e54002c1d0070b51000c80e0807840d144084411401400d4020000400c10b500142c0c0c40320001042c0c141035009042c420b800c10349040d601030b8403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 348470044 1250 348468794 348468803
    0x109030c0303050703022e050906040201020a060e0703050f010c1b0b0c0a03090807061a0414150114121e130f020307090c08060307060206090d0810090e010c02011a011b05120304 78
    0xd440e030088251400c07508c0041c0607424a5100c01c040c440581d8010881c02e2002c0d411035000306d03074048003601551829242d50300003402403003601042203c440d0107521450711080590b507008120140c3c05407036002601c402d01c01400044030b00c000b09103403100031b0005010b04c11b880c0c00d0120f0400351302d4070703400c0340d6030020141a40c42035214500b00300c00800421301203407200302c21a0104045c00c013030b0040349011030700249500782040080501c140a68000c80400342500300c0301c01400c3c0d0b10720009460020b142c9007030f2402c0000101440d0401031090a440030f41c0e00c142c405091211600050f500c90041010940000360780502519402103a0354507103009004240d2025140c600c80c82c20050300349132030318096030700040464200409202e01c4030b01c00306d15042e05440d546070881039038403000010801210f4652114100a18020321081d034a0303019040b01c42202c900d038000300110240340c480d2850704200d14080900183c100000050781810461001d86d0260295086a8001045044030340b00c56005440a03036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 348471294 1250 348470044 348470113
    0xf1803050c15130302090c091002160803040308120a0e030c1e0d0806100318231209120a08070c03170a05032202180a0b0109030c030305070302 63
    0x241d55040c00450403900c0c04803501214901010050030765910045400001d00c64503120010891052510301921030700c0c04000d0290300751381d000ca07101070340d200d041542e0404d0751400c82c040042c10844c0801a502165008030104d8900382c03408103490200c0e200103152004c400d80c1c40c4944000c0c0e0300704001070441a00c8510041c100c041044036141c8422568144603074403070740052000b0641590202c4000e422010640c1e4451060b40800340c1078001e00b0140480b0b00503001d401100c4414440d00141801c00c2810b010414141d4426000650b91550030400e500401c502007005502d2807030a12403c0d00e061181c41c041a82e800090701d60b622503503a40007200682c0c424401c1e240901c01c2c407a040360508201c14004400d2803600b52046005400c5003c01480324400d03c8000051b51903140f2a0050f58a0b541d5005220061280030113587e10405501a601d02028500c0e01c003105856500810040098030b800c000082a401e185580440d8158800341c0101c0c214041c06031301c807070ba125005480d0520030070041b5498 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 348472544 1250 348471294 348471313
    0x602030a02010e032d16060506013b0d06020c010603050705060a0905014b0c0c05090c04051003020a020c04021c050c1c1a0907050a0f180305 62
    0x7400e40b800f0410780d80141e00204607a40700c901150300c2d03208a0103494920740c00c1e041c1d00712001c0c28031030103040d026000115400d058001048055401b851045800340c80c0c03510f203240c0382182c1d120402800001d111050000500c4a5040c803030f00700b003400703550758010015428445156070320400e81c1c2122960703c00c83e0791540c5081c0f080042c00d1016070003400301600d01341e041040540004222010920405050110342c4c1040010300f4660000d41c00708800e000b03c1080f03680a000d500d0b8400b0803a2200d2016501510500041d6a51041c1303402840550400808101c0b03500705010040ca0320b601900c00111510200000107042c0c4900c401108213a901e6280140ca4036070700c0401a0030f0048200280c0d1085204000194400072411075410a00c00e2401001a80b59264840084244a10b05400da205c010b81101110008029000b6071100c0c0c82d445412201900b6039814840400c8083e1403400116200707124082509220f4886210998642d14152008000b0300c5c001d00090b4030f2642081d520b540008908 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 348473794 1250 348472544 348472547
    0x109051507030c0207060c0615060f1116030308100305060c041d010513020a03060e010f170607170a090c09141605090f01020102070206040906030203060c090f15130602030a 76
    0x506a0081c59420180b01c9420b04103802900c60f50b0b58002c50b402d2142e481c3c07600e000c1c050142d000c190b051000201e0890301940f58000640020410341c400d1000840d1159490312541c0040b41141c40e02c0e01c81414124000d045a41c00d80e00e400000309240c003006804400040818401c00c42540224441c261090383c0b241051140e64003104450004808000d0200040100341c803103101c901030884000c1c1c0011303168034400004401400740f0b9400103104818131000414800384020008048910400e29000340c4014440140e0700c81310104c802c100410b03083e4003244410b90076141400e0b8010486000000c42c00d555075111500040f040d0401c090142e600d910705a030a0510040c070f15045030994903000c05010404900a10510400b4165070051094035015507499000b501520013580d8004c0004c1d44441d1a0f0754110700030f202c20711080c0d20910072600401c41d124902c0040312130aa40207090f404022030074109020b8402000b0107068600ea40030002100c00c0c0c10208a40400380035158040d55448000010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 348475044 1250 348473794 348473833
    0xc0602070b0115080402010207030201200714040f0b0607080903031603080a05070c02030d2f0c0f0105040b0301050910090c0c0201034d040b070516181d010905 70
    0x100c082c061344500384800360303070000741c9042141d5091a003040038205d00203140f945c240300513440240c3ca1050000c0070610000035003041c00211404e0300c0c1003100b4041406c0304015560580306030b41e0020410030501011903000700082211400103001c691600b03280112080044c401c005042c1e0000e1258014440400000e000d125000f0031a40781007510041e1540001c0c0c2c40c1c1c00701e00c0d040c00c2400140380d0b2120850020404500d000e03001a00801c03450b12480c00c0c15612800c079448028881e640040012403d98000c5003907030103464803601c26a0541e0700304420300c04c030031201800760703000613420304400913001505006201c08c012495440500f424000e1001401351a0b8145814031081e140856840d507400a0f9540248a5400c0001c064004100d80300900d00700f44007800381c410058800135000c00c1603202c0000a00d0514410b008031b40e800808489c4804000d0407034001d01409260540d0040700b920840d400245000c001a422400b080702c502a2460840300b0b182c204544682013641191540e00803c0c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 348476294 1250 348475044 348475079
    0x9070c020a0506040510111903020703060e0d08040609050a06050106050909221e080c03030106020705010206130605060a05041e0b18041b0e07030e01150b0301150c0602070b01 77
    0x3181c0f541054140000900b0030b00c0c4d143c094504021450503000f403100410410f08220001480b48808200d0890400075100e051a0005440a07406d20200440342030b40001e581004081c280d85014090300d603a503030f140151a000400740c13501e104030154007010664520440307000f004191146550749a0300301c20311429800080c801601100c584003c1e02c00014481013080341c05510840d0014156800c152071650110355000c0a05001804a508071801034004000c5040e200e4607021249050396a03401241d6800c821100111b20900d0080c02900041c00390f0407440c0c0160004040c0b41c1d100303840d08041170844106146e01d040c0c800d8200d29040d4070181d18450700150321016155814003034048808000c4100010784000c5c20111b84a200c40c281c0c2c100f500381080500074003034802c03415003000300d070080c040d002c00200943e60b94a4807500c00f81c8030f001c2d4100c1c1c03070890f00d41c465034504680c40d201d0010040c01041c49154141b040380010365000810510007001c00521a2030016015410248081409a80740c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 348477544 1250 348476294 348476299
    0x21002010c0206070c0c170604030809010501050604060f051b010c0e06070c0e06060412030509100219031209021306291801050c0d03050609060303130b0904090209070c020a05 77
    0x30070880e02a5001c41c1e0554000d255042450003002a03150441c40d0740072560111407818090815008030b5800403a80c0c0340503038060382e2044126150191000e080321428400c0581c817000412080200070300504010b40d0b044040d0600601b40840c084e21141c0c05030100044200c165501c12070200f405822601c10b09103018207448090601c09181e640240c40c425034040c2030103c200410016004c0d5807483c041300d0103403400302e0540000c41c01c240750140942d001f000c0354500c0364544030500696a8030001e2030810b41214101c0c8941240056101031312001201c0191400d4591641207010150b10754212010401c5c000318000901240b078003c040031421101c01700010740201409880003400c5003001952194452a12660001c00100c0c0058400344229007410784680030b9041810700c903680660003248207a106503000c10700c035134038581050385912900108070b280b5079024100340030108030b03180a0611395401600001c0c2c114003075000200e080c3d00403952500010081c1c00204110300b400c4000c6002008107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 348478794 1250 348477544 348477551
    0x61804051e0705030601051207082406100e010e0102070506131a0c03190306090f0b09010608060109030b1b030117070503070b030103120e0a060201021b0304050f061b0304060c02100201 81
    0x300f40c0000d85034034040c0b2800d0f100b8a902082c4030741415051144000900403441101e00e4640807004000c451101c4080c0c2c14940070b92000000c4642c10300c1d5059038400c20b002d03070714045030102540041d07580d0441c07210054110b200704032003c21030b82c0354a40102641980d2000c800c40aa01d4140004819a9041804000d42d4014040d6000303040002045d2038424840103207042e40c40c540b005046004140b40d40c014191f040c10a0850f0914240641c000400740c00f0940304440c0130382c1c035100d060341c001e00107031602c078002544c0040410109000300340443d0850720b80c0600b100d1000c0903010000e4039800c2038003c40c1214085005001d29800c0070811a0000d00050300500820b600c1c1c50000c0066010501c00a005400880c2c00420307640c1c030076103103400c020030000d214034425602c0d160007d000307400100c0390414890304464402d4200380c000050b1011100d00070580002c058101080c041241c0040614400c0020804150015030000f0300107800a85465a41c3e042004003d004104800c1c030030b500a0401d5924 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 348480044 1250 348478794 348478799
    0x7170a021c020109060804050f0303010303050d1524090b070b0f01320f040e0d0210090f02040b060708070b100e07021b0303070b0405060f1f0e061804051e07 69
    0x800c644c0103c112a2142000340701c0d9034850506500b4030b03200c088488110b010001c008004c15400c60080c102001402034100500f100c400c1010484140c1409080078034000e200c2000350700742c9068000b0250459030300d0440f504e95659050001e0641104600710741038403400007006120718214411078014011421001d0b11003000d1001c03001801c0c7e25646906180601e0b900c00c0000b920f500c402d140b071202e000342c0100030401a0383c0010741c860340d4880e120380050003074000c445035142c118042c18160a401001020700722100e80d0801004106283d0030720340140084c08000045040c84014020660182d03100d51228581443c5410080b0015003144102d00314900501103021707030014850000807007218848091127a141c0000e031444c082c1e8540101006002c4041008112000c50070758011010541c404074107458801c045400742140e20941014084111402c110341a040015140c02c05030240244601d2002c0545c1060070407800c40e001c1d50694401552407a0500c1480c00c0780034903441544c09026051b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 348481294 1250 348480044 348480047
    0x406150b09060d18030f020d230d11030c030f160503070c0809031f05010605071a1e0903070b061e06090a09060602070812030f011707170a021c0201 65
    0xa5034000500906000c100b2040903c503540c007118001e0f00c0003155005a40349860014404a0440c14010042c000d11600e01c80b442c1c00ba4003903400350402c035450803142c403102c108000d400d9006070080e547d035940c40e08042c1c2c83c80015200118040c92460000b259030b85008884c510803148040c0030740288007889288070b1405036100003a6600b1100c0c92234020220031050030081c2681c02a424450340c5030040c22008412101c210724041e2050300c1d90041400a40e0342c64900381c8442c001d03990007030465942c0704c0303216002e01384580c510769024408486816000f5401c420440b03900104640307441450703000098103030034004d030044a658009070071038841e20303100e400030030003100e9001100300306011708804918a0385aa60351100c171406000344141c20002141d840c04000d5407002a03104403445400b4201d05c6d040440280000c4034411249046000d440d64a4008144944000fa4088114501805001249400441c1c0840c10900d0400c001808048041e00411110130000201a00448440455400140d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 348482544 1250 348481294 348481297
    0x12020307030912110405090106050a0f0e01030308090109050319120603170f0d14060910061407020d050a030201050a0f02070203070b0a020703060501060507140303091b0d051002030406150b 83
    0x2c81140c445941040c010789403134a26040c01141942c0e001e41000200044c80e801544407070304440d02111002034107079a4208204c0f03105c800340030301000000c9510050000c02e010f0031009400c120a0400040e100ba46610740c5c900b10381080c1c41c0c003400e82d428000f00d21b130315503440800b211004003000783c2003005500e5560303444030321040c0c201e03050b181d00030115081480002400950303241d14060b40c000d0100740b14074441c41990240403100750b48a400c1d8070000c15500340c01c1042c05401c0d075003a500c1e60707281e880b81484000400d42015504a9002000498040c00a141441050305840c1703e9000401e00b81001980b10040e101203034000d49090748148240400f40e500001c2c4041140c88040c00b8942d0f0b030a045004034180003175038102130903442c180800010807960040040c0795040c01420f00c00d10b4041d422110039220711054a05d80110340c401500c0002d98107800a001d500070500078150491081c003a510340381404001c2c410165965030220400c01402a603016070041d4a007040a0f1008640c14840068001d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 348483794 1250 348482544 348482549
    0x100311032a2205010203492f0a080c04080d0306060e030a050307060f061205030702010206100e07140c100509010f0209010c110f1f0f02071a0c160f03120203070309 72
    0x20301c07038a40c3c441a0b0049551035059444103444032030b2882043c0340b030b001f006081103900c0400c8403403459402c80e0002c1d400300c02e48105040d41a000f28030b0320a26200890750b0090260000120b254104800514441c040008641100080d02c020600341d151480203044044500202c1d8000e41103840d802d000240040b003201c14030f40c0d102400161b000c46911191009118541000842d600091180c1c0c080c8900040a000345070b01c01d0f421100959112003004040304801e10840040e01a41c3c0c012807003450085605078680e515540100c0d00b1324080c460903e1800d5220b40303481079031a903030303000b4482c0b00300085c001d503000154840000d51a140e111000242402c00c910400b1780210740c0044e2140b41039a0341480b400142c0c100510040d41405400c100c45c4400180d02d8600c000308101c600461005400480c0c3c010840d421040c200000041013102c031402c44d40305890741030003800307401503801b0302000741070511000c1d0640c014080001c40c00e5151801e50034400c82d002c002503500900c400b0b000254000d504006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 348485044 1250 348483794 348483847
    0x3140a05071d060403061d0a0503040810090c050103050a29010206090109030f0f0306180f05060906060d090f05060c03010806150a090b1201050a0b100311032a2205010203 75
    0x206801f08081d0151070111140c0502200c0c0501503040c014071100001400c150355070801038031902c5040132a400304a581c440300040071b2400b40401080158003035841944c0c004000100800c00385065412100c840044150880405140584903030055904100b010b601c251005d000300100f64298802400c110f04150103042086603259030300403140e11a42181004000c001211441c07003900c843e9800241a20501035104c0e00c0c034020016040e46071822041d402030001504182c500316404c100400504580c1c213060314a180c52240707150010380c0401c546403050300083c941e02d450794101859681000c4028222881404514001c441180c1c3d0715004607049602e03022000402002d1400820124503041603681015403174101005512186c1d0780040d1410441211405444480540140d0440b40c00b40d10303141000e03009000044081070241d864000391a5900c0854256905180c842d01c6a84c0c00058144040489040310012060008040b1805080240041d40c01c018040fa20041400c41e6030003041ca = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 348486294 1250 348485044 348485051
    0xc050313061508010c02060a050601050a080103020f18040b040201030c0504030c0b0d0e151807030507050609040b030604060b0301060f1d040813060201060f0e061f03140a05071d06040306 82
    0x40c2d2101c001200d00c0c000d00d0f000c0028401030342d24034000380d100c41049810203d06030900c4001049584104111003d60840d51120b0405908580074050304200b22048650894400344086104080c284210f80c4202c1c407070703c060030303076454a84001410313200640c100a0621009010500000380c1c00c4101340300303071b845040c94107850715024001500035003c0800f42c402180500f5215103101d00402040b680702d2440460803c0c82003d00300c0003155a51710912000d80550003071401400107180c02001400e01400c01040402c44000d0382d03000070304080c001d40e1300702c9000e565116160803504081c01136030000c10400102030a020b1034091820019030003400c0e41d02041140c0d0001504210301030054940d542c8910715028070194a420000c1d00900c4c150099454080ca0400700255458901c4030780c0f8401d11010309585142d0340c1094481a00d150101c04000c1030640700c07071107480302d45003203909680320340c080010214130b038142242d02510291940840c50800707100d10010b801c6a407944011039040366030018001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 348487544 1250 348486294 348486311
    0xf0201021501120201091502030f070203150106020703030806061801120917070c0f1a0a020111160210020607141806030703060806010f030213111c050a0c05031306 72
    0x407400c1150020803a0382401c0028004141600c40714909080c15200ba26100162911040300041e4842c081d8031110050b4030030450031140030114406040c0851000e421241103402590b0b03011035044c400d8000320700585c048941001451740c0a0642d6030802c60030b641e060f280c1718081c4d130030347c01c40040d0001a038103015034810340003903c40a56010b0025540c10000c05035850061651004c2c2661040030203981150f184079001c6081d0941628880c00c6981500e541c654fc0c0468412507601030304003c0212056559810380d09514144607001404410b00c1c250301c3c0c0075102e5084c03040140c1070a8a8a03075404660200c41001441a0080003403850500e50000c025201c5640b1491608400c1d03214008a400450102c14002269096048202610500c00a80e20941c0c0c0300c0300090000c4200b4031019610040003c1c205075004030603489404290200c6080b985005910450450660740305100e0b01800d565078001c12a00c110030748224610703050249400c0380b66081c00d250008d0203150010b4090003082d41c49194 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 348488794 1250 348487544 348487547
    0xc0801060e1201060e060103111809040c030b070e1201051e130f080c06091207020904080409020c0d081501080414011b0302030109051006020616021f06090b0108040506040f0201 78
    0x95150424060b00a00003544c4500f608030300024243c40241c00310f410043c00c0c02d040d194a2081e00c0050302024091001c1e41c140c401002401c002c00341050b19449404000400070820300f42c0d1562003800c6540350303120695112424090780d80f115841c100110b0340f4080500480e6081da0b0300407100c0b00f5900c5a03000d00e64560024903909410050801880400384004e1282084846000742940d080040c003542c48982d00d11000355101c09194440302a90001004142c00601d480c041641e0445c2c0100003040c03c194441c0301c2c200c202d0b4841079850010f540081c60413441c440c1e0201c50154032414140c088250300c00106c0018041d104060310040007607214886140c2090800d40c00a1500e0b508581c00100469883d2000b034020741c800e0140a01c624200400030303a140001c04802802c8032555801070449550303900e111300610741054217500460090801e0040c00240c544040e2031103002c5c441001520915043c5d03400c003102c40304c0c0c0f00310b414080705408000100c5c0340890040c0d4003030f400c10011058058980700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 348490044 1250 348488794 348488809
    0x1090203220501270606081501090c1209051509161802250c0f060503070e011106010605041d04031b0c0905010f0905070305040c0918060c08090d030c0801060e 70
    0x4021840003099120313011500c220034a001c1c4510b0203080100480c0d5102d0030195220b9200d04031030114001010b00420042e0503d074095401e0242c64544441082d5107070b0704400a660b018401503c00d5440f0340403003032030170380701284041c2c0081c001001040402d140d40001c3c0304450162142000799a9241c001d200041c0d0150106c80905101c080c0c4200a04501c00400c03807071300208401030710159043c03400811914240e1310304100f9101a51151400e59403005030031140c14600650450400915000ca55564202040f0440c00b070710322078a40c3c1d602c4034104030b0045105440584030895600340c00007800042078026178100c110078104034a806180790103043c2401d000070660b010240c040d18120000030400d05241004050ba00e5081c5c040c40580c45140c42141681d6003a200905a209607090130401030700640e1010103000790804044421540c941c0b0750300c0031111403901e0340d0046026507003004a007000c14080a0390700d0146080801c24011801c00003000750805016807001d1280c8614955420303560300a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 348491294 1250 348490044 348490061
    0x6010e152103030712110708160506012718080a0504170c0906010518090711030d0903022e0c0306050d060b0109050a0e0a050601030e03130e01090203220501 69
    0x1006980c00100da03503400b9601d0740210707180e400061314030340f01d42840315040c041c81010f591608a0309081400d0781e103d1241e540e0020795800c0c000c4440d9002c900000d8001d114040c000d00050381000941403032140100c40c807001039448203265500c1d006134294440450400a101c098024003003548502030210207846038400d80d0440c0440914800c00b1010785500014003450101c001d0720001600d4403441c006449034020005240c0c00c80c808032410401038100381071039a501180b0780c034090141228514045003140c0c8150103a085d99500c58402109141d0108070302109003400810098200350022200d600301c60026442045040e2220030381d00c01e4070f01c20740285c030280100070900c500c05c001900e0000014803800f550b440c0826500180007502d0301e030050a0300103c40c10080300303100e641d4480740c0c24001030500801450506664500c90f1134292000c101514400c0c000c01c2460146609090071000700100507845890100c2c010010000d601c42c1d01085c1c4c400c81c04101c61542c078426070600c0c0840c05418500f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 348492544 1250 348491294 348491329
    0x80a051302120c04063203010f0207030320030127110a020f013b030f0304050a0c0506070305070303390e0d02150a03020c030a080103060e06010e15 65
    0x30300701d00240810200c3d00c1401c1040840381085250b0350744807040f20311108258035800c0050000c1580d680c031b192110000204d1a401800000d004042656840498016460035000680d0b43e40794021203d0b4014500c034049031250034243d05561500143c0714000700000f00c00f100294191070302c440340e1091074000c0c40350f8001c410090394441c001c2d03aa00940d103c4051602180030341c01d240c0c040c038100a4281e424450742414007001314004500f000940d090070725400c154040c13031004005400d420b62450020f180190f00c0303000a40404007442c10100201c80480e0003039882074004010601c0025040800c4030100d5030b01d4140071551158404840c224580503684541c501c4014100c0d9550b030f2500c55030051280062a1522038912001303806000000900d240025005035484407807014a14020010f050784400390b05d4054a007602d043d040c075096400c20140b03000881e501d000180301b00036030350194001070075071034005141d20762410604441e43c400292a02c000c020070615202c480c0e4071023404480070107864 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 348493794 1250 348492544 348492559
    0x120a020d15110309060619050d0305160606031205030c072d03030c020f0a020604090b130c0309020f0f0a03060b01031d0c120a0506011406300a0903080a051302 70
    0x8060044100e503104641d0f132145030241500042c010719040e22000c0d6030b081001c1c0300300c0341035040c80240310050106e4401a0107100090000500e00254810706903122886082e011440c1071552401a59903000300c41c0c55418031a00780308100e61042010300380c074881030b04110170f4008102e4191011786d0031002c8845407140b003038420b8140018542c054000449605842e0700b00c404100103514410384400b0400c800a50103901000104001d180c036421881f186c1c6c1004201e41143c0074929401022109103010301004aa180c40341d000942c9491024103803021030503242c2c0f00c40c80f43d071140055008100b5000080c072040d035074841103e481c0d02c00d50101c071460609c4481a54070302001c09215580b0105a000f6a204000b038001075142c0000c088dc4000c00c0d070b0b030701900801c801c1c0d0030101044c50100501d2400780e0448e005001e044035200488200c1c10868010040001c046031203803103604141a00100364100c403600300804000003d03404850b0990000381da0000040c00e440d4241013001848001c00c000e07612030038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 348495044 1250 348493794 348493811
    0xc03070f1412042d0b06031c030e21070f03030b0a03060204140f090a1a060406030c09140d1b0b030412030b0f0a0302060705070801021306020c120a020d15 68
    0x84102c803a00030780c080c44030640040000c404142c3d130503040080002c540c95030400241c00040004e40499007000005050380d0710a5517000780c0c1118540c00050b118006500d5400070101c101782070045225240195121209248040d6a0300041c3c0c80b418600414040e4081070200500d4841d40c0625606000100000003041d84c81c10400060340050040c90840481c01002c0455454481d501c5203907154040e00d200320580e02c050030500107000c6020352007440b2a002c08188071070b40c0d59600601c0039110b51784000690203c2d60030001e101c10116004040d40300c0e0b0185101060396580c0500343d20b26644541c2104140d5091164140c04105641c045104090003005200410010b811441940c00465900b040a80011010040c5501c1603016003904107003004c20a20145c14181c00070020180a1811515190b9882d40ca1b2800ca901c1a8240e24119100100605c445a4103115440c10314800301c80708041005407409642d110202d15800074800c181010491003004440c5c8800341030810104801c001c3e090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 348496294 1250 348495044 348495067
    0x50d0f06171203040b0f36150f28020a0c030f05030103020d08030705120106030e07120803070503101a0306090109090506160c2a0605030c03070f14 65
    0x20440740c018265000d0b41148a5004480205692046410600300300c07039500d4000041c400d0039400b030304034046950300716840600f449001c500c0d0108400000249000340c0701c110b504600700b610911004a0580110f41400301800c0211021508402c55040f403013a011aa00313404040c0c0c408898280f01c0180c0041042201c0e950440c0010620500907240c0310154903458030201e071148024040290312014100503074004c40c1008024592000d490304100745011140b01c401d1005003403d0380000c00194485038011400c07013042c040f82c4003c0c103c0c2502c5060312116907983c40c41d1404010484030811134048005118000d44462072401008141c20b0b285660402c041d2a080c04c1c0e20880f203a030f0080c013220000007000300f21489500002d54105016020a4603504a2036890039000035070304040010700807010340403444a861041c000c030716100768504080164a050b80900051390f00001c207010050003007004820084085a5108680385020301c440d0211030300503a40c1c101c220340c01003d005d10201d058042103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 348497544 1250 348496294 348496319
    0x30c0d0f1b0803040b0609100e0c070807050a0c0503010b01090504090804180b030118050c01030b061b0604050609060402150904020d0e0a03030e01060f0519080a080a11120a050d0f06 80
    0xb07502074440c603100c60341e03140b00744201f454098540300d90002040104100005004000580043c40e110b48a440c00c1c0d07298403000125001003c049e24107401407040c0c00308100c50380390043d005040c250001d00248d030041c80080e000c0318803481071500540d207030074440007004180e0702100c0140184d1a16080e0a9000788001d000410580050354040c3d81b07844800d4218000750420108400c0d404402458085240c1d00110050004c1d045001e400c0001404001140142d01c0304001000c01200010304051070079040403450a5009072141d012904142d05100140e100e02c1740c038001010302da20303000d0303034134515100810001d220312050244c01c140792001c480144034003c110500350701d000e69000e100c5080b070364070424203c515521802c04400d880d2031080260f402d100011100c24207141000c00c1311213a40364180c50070840104c004480120001a07160815034215910305800c0041500421080c140c02902d02d143c3c1c80303404010014840d01007491321380703240f8640151400c00c84c400030600c44c10341c1d644800004c0327 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 348498794 1250 348497544 348497551
    0xb0409050102131401020312070f0908120a081b030103021c0b1015020105010807090c0c020402181e10080405012406020d03021606181a0109060602030c0d0f1b0803 72
    0x1061084c0c0b14041982d8400802e079000101124159034036602d407a6400e43c1e58041094102090003203024000030b0320f007024810355a000120280e0550743d03510404c001031001100505804458001510407100304640c1c6042ea819290b060b1141c001d61160700301e0405080d41c0c1480020700016005040040c0200860b4011088480100340c005086840f2038059083c0c407002d000380003465020b000d0402880c10690000070a004032414032640844103178011506036441940441900103060102030302500709001c071000b0300a8040700c0920b0381c0710480700080364012a2602d000410619a01080a012003980102150359061070104600325000140405100540c031568016000300305402d080140a0300031540700440d20703e1405030f84011a41d800004010f0340c55065000c0005198000000d0081104c1c0ba07110781d61107980c2c041e613625100030324040c0c80a50b003098003107410900104000c02400034902d6280010b0341003610200c8011407040b40d040c51050a82c03444001c00300c0b0302d1010f20660340000e601 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 348500044 1250 348498794 348498809
    0x111912030f17060f060705010f02040510050f09091b0a210212040803090f060106120b120318040b06040608040c15050a080705192d0e040b040905010213 67
    0x40450400c0825581c910414403142e03060060500060054a00300740d070071102e00d00060406007441c2c0181c07100c81c00c441400c00040200b03940050203200f545030540d190203020045180203441c0c0b842c0000c60207218003a003001c00740903080500118241e00312103d100103046070720018058850400c8180188401c202c421404039000c02105000c03d40308a900072034200038031601c1c48280c103440e00d80e2403910710b520051040f51203010f900e2280b0740d9450280300c0c8038024030f80d80e694490b0b00140c0c400c1c0d602c01c90341c8040d1124807482d030058144000040202c02d5a10030320210700d820f9031210300c50011074007074019090204d521010000c0c0c00300b43d0039042004603009901030f0482200640c1c480d1f150340c900700d007901d4400300824024810596264883e90080b81c1c41403442c54000d0900000c0b00e84a040003455100f05008964425805032001400707000d0301e80b400c40100030409004680c03020207031070340300c070480454000c540707a07101102161207036007061131499400f800855498044441d0700241080728001e511 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 348501294 1250 348500044 348500057
    0xa080601121505011d0409030206012408010509190e070e01080a2d170a080912030a1104180e061605030606030a09020d031d040e0a11191203 62
    0x300c64a5061280e030590000e10603016a24508140c010360740751030100b03503a55460017009001806600c590040c075441c144641c000b4000b075414000000d0850040e550660000600d030b40c880c00e0600c3d031002d1081d044a0098540c82c0407500d50a00f013985e440c0820312511032071418040c4402d065a8006040e0301210001c4509a41503601c1c0c011540d2030342c1003550041e05010215000000c83c0c03807410521800344816440d800648451aa00e2002c81346c0d01e40e4800d07038a1503003c1440c508042d044510285c7c018000c201804100c000b82010000c5070101802000003680c0d502c8005a440c6060b50031070f00905081c2816166a00c6804614005483d0000030150303035005480109032400c07449414141e12070703080c2d2511401c41c0e0f90881440540e410041c0102c0b540c0d6110044200580c40c0c06801c100960300070350b9441000c00441100001000140300e20f1800303280707031500301d034070640d4082140e0009540c01030421040301101000600b40c0e03001c0c0302509059024002c000101071800200416041e84241c0303444 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 348502544 1250 348501294 348501317
    0x91d120310050109030f020f0d050115050f060a0206010611010e06090615011404050d0812090a0606050a0803190302190905100822022209060e0f0a0303050c0f0a080601 74
    0x4403400c4c00140300081441400310410401450038a261070f0310b03198040c12a4502d9001c9848190942d070b00810100001c640038002404242010f29948403aa88207481c0d1600d418400f940c0250f8402c0c0500c0f4000c02c2004000303d00500720340039086001610107800444005060a003c0103464400654040001440c004492003542d401842a10140e10722420018281481c000c00c0c0550354060902c02c17a080041005109611506040c1c2d00d8058083d550050441440c00d241120490f036054101c54032411040c80f0800c18108000100c448001001000241071602e03034106a000e03000340100e40712011b04644214030015480145d4a08440085803800345044180c070060b50f81e2842130311956a020b907080b5509400204501101a10b1071000c0c0494101442000203021042c000c4001c008103103483d0401c1070b0600c0142c2c0500ea4001210030301070158080c03031141041d036424403588000c043c562620f000901c90305e240d5059450b1241c480700b04664032661450003c4c0642c41c01c40d410f0340480c4424001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 348503794 1250 348502544 348502547
    0x303060e1e07030c050f0d151703041a041a070c2306090102070b030a0f0609050f06090403020c030a03031b08060102030d0f091505060102100c09091d1203100501 71
    0x400c084001003501e898003585035000220060280181281c003400010414501005000401002c0000c04403400003040301640d84221801011036000aa910980b1030f0509402c4801200b00c504071401c03800c8505000d842c07410341052502035580042e1040412110100440389054001e120321442951070442907604c03a02480d41c80d2000400c03030700c1e11035044290300c0d109042c450006c000c42d8405004a0342d00d640c0e02c0380300b100e61341e0040360f00e4601d5907120301c00d0860b01c000034028100541503048042c8490718181040040707001000f0419881459454086002e00d0f00a00059802036070190903a501d034a06814041c01500140c20101e031000c0380c44443e003401c04d01c648409030055038142e01030f626161960613040094002d001030b080519965414040002d403601c82c85c8000b10b400010049440d20740300c070001e41044010741000d10240c0c20700c0480c02c013856001c010f03281038a10802000a9020550300180a4800418101640d03841540001e0300245101d0000d0351041c12100d07034890040307454000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 348505044 1250 348503794 348503821
    0x80405091506030118110a170a0c0206010302060d020c012409052a040b07050a020108150102102c01090501141b070c03120e090c12010306050903090a03140d050304020d06050604180303060e 83
    0x2b203500c01070b005880140010700d480700040070308145880d805800d0a03456105039084070a400102c0f01c0c600b83c45604c0386040b10442c048a0010495490200004d203000002c490008883c0d040c01982c1c1d1400101081ca41000141030358003500070000c0c61174842c2085e26000b0741d83c1c0801c1d8000d0380851000d0380010f0102901008080100e0701c180e01410340900003c003040302902c5649100c28510498018110f1400110190401b08580040c0045001d01e07403801c025086600c01d002d4a40140341c0c5204008110121100c83c1c828082091031a960300e46050420060311020b9400040040c00c8001c010300c024ae80c805c8034040b0010040380c603150345071036010154402c2e12802d105040d080e6610030040000c58416440030741d200e860a01a64600f0103140300040b006215070f00105c032546814502d60604103410001c6a4046410742051480c40c00c0640001c2c0b1010103502c00204029250800108961500e4000c04803400c449a5000b01d40e04e010310300603004d0001802002e818103107107400103241480390340c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 348506294 1250 348505044 348505061
    0xf040905064209130e1e0c0405070e010f050705030d091a0109020405011b02150f04090608011503021002070504020d060305010e0105060a0620060103080405091506030118110a170a 79
    0x1c4c0720300c01518100756410060710500d0b03488030160140c1105891503400e8007000e008200700d07071406071078082ca0750020407007180e902401c5036042100000c10980d10381d8001d13042456045107818401d0300c950003850300c54694482d61ba0074224190a18210710100f081c528918009801400b480741e05a81e22901828200e004a1140c9030010b0102c3d04104840c500c140b5803112001d0000d04102c405da12031444400c041c0d4000c0349401c0f0308110004042042034014410b400217041c2e008000e12503262455450000c2c2c5030180006441a8840f01d0945d0009008000361401000064000e40d1900c1e90341c21194018002031000740c916500748080c030b0821803018410f43d0711842c401824029410306181d001c42d4041c0611803109808031080420400b405001c1002078001c40c42200c45d240d8807800c0c01c0c00c0c401d4038440603000c0429030b54144040350156488000b80c82c19a04a1710907000300b107041700c9961000d0404d5030342c007800c1c0204c002400780509520041e64004c403c2042008512501c1d4030000800716007000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 348507544 1250 348506294 348506299
    0x906073b1c12030e07090e0c090702010905030901030c1b20010c0f120207120510141b090a050a14031e1c0309020603180708030f040905064209 63
    0x100100d8120b0007030340301200712030801d4200d611722074844036110304641000403200540d50201040902501c1d0500e4015401904c5100a014000340c554540344c1d240280d079102418151994200041036100d80c1c0c01e4a81c9800c0110603100810312420001700d640c0b00c0d140d20142c00c8003801d840340b01c00d500800300780b81925403001c5550800c281c40d460384111110380301c91490450003001000070301030310064181304a060041002e49410403a50b0060f004a4620401d10b00000150000f04005103445448140e00c1d0000d18a20301d5907600c107000080c15420040d005140e1058214102150141000a142e665130501350100c908001e01040c403e8180201624654015445606400340580500c0a400b04440440c100450013058941c0001c0f141d81084800c20078200c02103180840424007000791900602001c8055442d0a01c9600010854402c40c002c001d102611200410f0050321384000040c0a10041c410000d0303080c99500c07229902c0a122040e502000000e4043c00c640c42c501002110000c0400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 348508794 1250 348507544 348507563
    0x30d0e011b060605090103060e07120b0a0903090f26060c070303090c0b04080303041a0702211204050304090b03120d1d0708070302040e060906073b1c 66
    0x503024403420110000842d84107031241400601500c8114203d070113584070740800314401201810a40c985159540b00d140341d151900140070200b002000e042d500b03c41c460001066120207402c06448802240e40800c004985040c0c0c0054450700742c034060110f410399104604081840550456910f980c01c5e82c510000190400900b40068002d07803200c0045480740d200c1900345940c6030b804038519045070744a510280c100200704020001210602c5c204000c00344442549401e0603d4020b6403081014800031185500007140300200360388500b0349000c8032500020074864501450401e40760b0300b0034403504e100b140c2001c00544032031901203815401120454940c1c1c1c140412003e4207000b50007282d42c402d00031211480107a00c005014000b5201411329400107000c500d14600c14841114240c3c909503240ea0403000c18010314160215419807c100d0510384040180301c0381c00e00310741c5580154610103c407484414601c280e0050207801d03c00700300302190007a0300040798041c0712445554000c0d006115521 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 348510044 1250 348508794 348508817
    0xa021003140a0c0206011811160203100c050d020d110c0f16030f0308070302160b150105040e0720070e04150903121109040f02030426030402040209040e1b030d0e01 72
    0x1030b01c0d0707c000c0c0400070f482808980c14803031030070303002807a807054002461b0804a401c14070194201000780c042061611002002051117440c0028030500036894400d0185800150065101030141c100250b19046041240c0e032761802c510761195a918141d46a102d240a910302501d46c0c00b2001c14118100c070b40045c076103001d4180640d4102d49602c002040074003031641c280281b104200c400554440e00c1032280d510220380e810300c821586404001020f40078100202000180540c0306000610b50b00900e05081c002e41a01e40040e40894440b107250040c45203110721240041e049286d04581030086009040c2481241c0c15100380c1025204070b503c02a020550300d00104103041c1c501e52008012422a42c915801d14030740ca000201520f11a24070803141e0364020003440107200c6802080400c1d55600d0f140a1000400050081c520b800002c2001c0d102c0c980c0401e00c000c4544441e0052500384900c8425600c00801c60f0303d02030380d5080a24070243c000d10070794100800c6140608a880005001610303031180c1c0070f4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 348511294 1250 348510044 348510059
    0xd05030d0209011704050d030b0a03030e13060302060f030109050c07210203041211030d0c03020601060c03051b100c09060c020f0301090c060503091203010609050f030a021003140a0c020601 83
    0x41c890203180b0704000700800c084020a40c0d213038610740214404d40c00780c82d158200c102c0003010350f2951400c603440354400410410003c0e030820ba00c2602c0c0d1800344c8132a034070803072561030f1800285030a43c4065040b040008009034203d002100542c16a260304000300003940b00c0341040b420f2405120320042921140000d401221145800b100c8840d950f50301c106ca141640301c1c201c13520506500c5c8011203a20014441c0c1c0405890240700000d80c8040c03c1c0380400c2016859107000395544018031a440a000004030f450041c035100d04204c0e0980502e14280c0500100081c07a860b40c0e8018818031b15100601e840303900f0800510500b01d4100300c4003560748102103261030f038003040000c440e0b03803021503030540d690504800054240c60130a0000c00b1103480d91500c80c030300300a1403820002c50440d9002d0304041040180460380e00652844142c484c140c074000390206250021038a010100c5002079881700c008442c801c0d400b941600030010f811760aa03901c5095803905074005059800c801000b030050381060005107c800d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 348512544 1250 348511294 348511297
    0x1207200a0b090d060c0e030609030a090b0a030b0a06090302010f0c02060405041a090406140c0304051509010f090b0106030e031e0f070b070c020114031014040603020319110d05030d02 80
    0x302c400902e426207046555a50604941e2615a00f04c003140f44d022070600381345011b00a00b64004160009076181403030703d0340014030984030750050400d1082c0c04a4114841d034800e6001c45143e05000e032009280d1612000c02a01d460310b20300c4200e0000d140d0310070100c01d151086900000d681e501900d0b960400d42403008000152a00c2040c0301103a800e4507200c0010f503681e00c2680c03401903002e244005420a0545000c0d510b60700d008000040c03442042080c000018800140c802c0d840c15444034180082d2110b204d11805404030300754010b122410807044a09100c0007106003812107200391010040d00c0c0d2500d031099140d002d00b8142500078052000e030743c044581554020301c0381c58007074a551031800a1582e20f041800105403460300002c3ca080d50f04c8821540c00c00204c0440d550280603090440c41c118075040f280e480e5602503d2121015400848029203694000034007455006056801b603178031011079444d0920004100340c48082000403040b001c3d0a11074502c00c0c105170000c01451402c403001440c48081d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 348513794 1250 348512544 348512557
    0xa021b01030b041406030105090d0801091a04020d0b03010612030203040905100302031f0b0a0e040f03090803390307081305040617101107030309050304081207200a0b 73
    0x1030548a945028290b40c9034407400224034004c0078071500c20b0030400d06144c21600b000740144000d61020580b0407000f03400c21103e9046036246580401d070012000000b01c1d4114003000615045400466002d00c1146142c2104090002c243d00800c0f9240d40c9683c1a140741804083c040c1c0913070001c0009125016143d00101e44c882004400380108950b40d0b80424030740f041c200120100340c4107140c0706a458134110b018065207003a00700c0f41d0811081c14003240880b0400082c1009221000a808400800d400760003100000c0070b0001c00d81e0303195030b1404025950b4503502c49d142030158442160b555140d06030300c4040312000c0e81200c0218106070487c2d88500780e903800000004241c601194000a450340c80e8000c06020700b24071050743c0e02e007081c28500d041c40c002916401a468506180c40c0c240c2110150054640c0e00d905071401007600300705e50506a00758860b0b900864218040c2c0c1c1856404c4100c0c140003014040e01c250b400014113050f600c64800b109070f040e440d0b10703888542150204052415039000d06075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 348515044 1250 348513794 348513797
    0x3031b190503061513030c060c08090f01020f010f060317040e0c0c070504020d0204030b060a1401030f090b070810080d120207020310151409060603040204051807030b0a050703020a021b01 82
    0xd890304c0003607610700350700110024560001c603001c040c001c200e440c49041008101c24142001c1c1000c00365200e40c150b0080c418998011489003070300c030690380e00c02c10806811000c40c0000700641d103408034842d809488a40400d5510301104580c15900009034012602103569070500301005407165100e0080580c07008580500b00d104a58011406596a00c01428818080700c3d0042c1e680d403840c60301c00b110034002400584240590b280400030510744820301058650246000146c0004110340b26004003400301c0d015110140e207204005c1401c0d0015407071340c0030300f410547e5100403aa40d000c0c1d02e6601c142c034500d02c2c40061105d101c141a07540940d000740c95071910090664241c9070701141ca045c220303010403000c1700419103414010442c104940900d03012211099800d4025442d250780491494400a403001380955501c1c2d000400055820b0b0f40054104592826104c0d4240d4230704203c03403103100a5804a41040c03500010944950082c400c58540030040d4002e465a00f84164000419624070310700d490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 348516294 1250 348515044 348515059
    0xc010507080a03090203030d0f270f1106071709040e0d0c03080720010b040b040209061e090303040e160305131b0807090207051501180504020310050903031b19050306 73
    0x1b0708c443e490292941d903400c2448009200d4542021400710010100341e4591074011940040020501400561071501d0b00500134521328910f401c08207816200b1500701808154807108030311424060a001010102c10880b0140001040d0440140d00c940d05030081c000410002c0c400c1d00d0009028044103980a5410304028085851443e441e09401d240c13900c000c0400e035903801c0c0702102c03803402c2d2003514009542a9011400c16062074086485072262110b036210415514804001c0c1521110403038108240207010780351030b55610340c00d203001590140d4040c01051440c45c1e40d800b00910a21031144204040505036103d5a040d0b240c6045040754810314518407240c3c802c0210301050204568401403030b0040c0016559040c50900c2800c00034800c1000e195150200b00410035101c0300d40900c91507540c80c100014464070350340700180c6441030800f9207602050400042054102010000d544500d507a24518001da000382c1100390190702c5903030b014035601c0410060220318144140c000d141e001d803015081c038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 348517544 1250 348516294 348516307
    0x60604110c0d03180f140d110d0e15070506180a1e0606090e0a210e2704210e15070203120f190c02010f0339020c010507080a0309020303 60
    0x403044c0b003200030b070a41c0c1c0e03492003888001b211001007002c290785404618000c040a800c03d003807030762500306440b001d01c00c0100441d20551070782e03100c42c0e40d0b4002d103402621042d039030000c80c98440e46400c0212150011660301111006d0348050208900d034446600401c5c000c81922049402d04090021400c1625800c3d91340901041c40390b914442c01d8244484000140101c0e90146042d0000e0b0201c0c0d100c807035002c0e2070800d028828a800c00326101ea08481258100800c8150115103820210003040401c40c80b00c00c10140424030580f040c00c0c0100c000c00c0d4011541e40d0313000b9a01900c5402c644514250050708100070412200d086c0009030400910040507100c03001612a03241c400307904403050056040100191740c2c3e81210401c408030005596500b01409041c8268001038981084214407909050329144003038200c088180c0028001e1121045001c034401070200c0031009000300c1503078800940708161140d4401e41c0103009480a80c1d07440b040e0035103040402407088019013900c000481c2c0511050001c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 348518794 1250 348517544 348517553
    0xe13021518040603052a0d020904140d031a10122d1d0f030403020603100905130615030b0118060e040803060f0f0d0b0702071502060604110c0d0318 65
    0x4100045015800400071b034604200c4d144490110b03200b00c56034202c1202501a8241c4036054958002501152800c00554a906103140707031481c40c048447d19405004040d071042ca0305640304001141c081d0000c1c4401e05030761800c2c0306d0a010410341a9021a405141c030303440b00802038100840c0c00030b6841600c0c02c0c00001600c8841c3c80b00400c10b0300b20506d030326640d0100350020f015202c1e110004510f0018008202d09082407a03c0384101d00000e8000d000c00000908840306030643e8100618072200100207902d0305220701c0401091070300e400c458a90400d07418004841c0000e0484060380d070003442e41c041c4d036441c2200b050581860304c0c4144903410b454234170015840b4030b000d05103807095000e2011140d59290000c20801100303005100360f44100820880314010391104018500e8260303201d079100310b540d00d60103400ea140200c1503006181802407141c05901803a40864900d01640c015982400b1020750380165056a000741c18007000d05a21070f1105011182c4030b9049641d100c1d00d130b00e94181c3e005c640c2c0e0b184c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 348520044 1250 348518794 348518801
    0x501090e241009090f06060503130204140403020606090c0c030406050c0c090c1206090f07030207050a0209090109051b0609060304060f0501030b010303080601020f0705190e100e1302151804 83
    0xc9100100f000703010100106841d5000302c00c01c0340c109480400c1240d0615801a115000c050107141e8140d001e14855000c5440d0f0707030b0100800655180e00e030152840c142c90025a5041c00711192401010148041001c04280c00e040d00c1d0f500103000099401e01d4103082e802c0302c140e080000514110f02c15400748041030f440d0240780f50302442c40b01498955030141d50300e88030a0b038100a0700e400e000c1e003400002c01594810035003245800c1842d038a00540d4400d600d00742240707860803900d006507000b0b904030148210f0311015408084c0107841001940c007040300d051000c0c060700002d40b61840d01b0400401240c0914a8068010341d8054030030480066880b40c0410b0410071207109800c12a41001c40310700610a00d13070840801c6038440d200f48020042038061400c45a00c1d0021442098020510b04800d94007101250b85c40074041c003074015240455150900d0940c2c0052218440c1c0c200c0b4000d00e1020401032000b102500104035006021a031007180c0c1c0840348016035000800c2c1700c2d250a44240541c41c140d84e00d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 348521294 1250 348520044 348520069
    0x11100c18061d210a212f0d031e1515090b040305030904050903071703130b040602070c06020d0203030f071218050721060b03010207050a060c08010501090e24 69
    0x30000e000c1100c9a14014030b0280500407420400c0da4081c1760302e0001c660240d844030460400680a00f940030840340b02203240103600b101c501c0c681c0100b019241100d5491361080385607542e031402400065805030705490443c0c031b0041c0c0e010780f0043c0f429800c0c8682c503000c07900704418400525050140581e22081203440d6001500111341c40e03000010725002c586064000c1ca5080700107240910b1400501e9520425034250849680c030b00c900740480042c0c0d4004d50711000022960300988210600e140500e00a4000d6001e8002201c8902c042280410303028030018501c848841c1d103400071850354494028030104484000d0281040046034086082c02074458000c0c849003450740d0340d1400b00040075250950400810ba0081d5851400c00707072560900160201180c220950840da000981c0ca21201c0820301a1298a00141003841140c42a41c10481158030004d140c4d030a9039a1005030745d88641c0116161035052241c4005104000041000c015030400030314201e445000300300d00090305820114003840d8449 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 348522544 1250 348521294 348521359
    0x90d0f03080f06091305010e010606050c070906060503190605060f030703060504181403041d0901050c070f060e0a0c0b0408060105030106050d0b0711100c18061d 71
    0x11002010140c00010498000c2e041407507440c03480c9000c2000c10144100180182c84801d807842c0b401003070200c00e521800c40c20500c2c10003402099264040981170342e0000041c5091441900c0002820401910504040c2c8042c0e80d105e603d151580c64071001e20058448a488920355601c00006070703039a41000030b0115008221101c0e440f0b182100300030b812566a42c2c4078074001c80c01c0480c01000f04c0441490030078115444412164190004040d081c91409103400030540850380b15610340f00307401d89115040c440c22100e0000e01480d43c4881d4024400d000c0e24800402c40045030358080c00080c03051300100c0c50a4981c070210380888440e42c03900c2462000c3e90348074070045400082c061029034401d0000e1809841e040c1c0090005030f28041c080740b0306aa904401501000001000c181460311500c459400e1400075003c40d40a00d00c121130100080c0a60380c000700c045810f15031100c104c26581c410b0001224150b8171800030f4800024900d05184143c0200c49500458101030a550105200e08aa1000424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 348523794 1250 348522544 348522563
    0x3010f0b01080604051909030905060f071209030c140621060a060206160503190906060504060923060d02090f01290f0a05070506040308070315050d080f090d 69
    0x12600050210359000d002140118100790400011b201303058600482c0c99804580000c0611407070800b2074040c66180c01c0264070000c0003800c2e907101c807000303000f41c01d115005041e541201e41c20030740181d6643d0348510000f80005450b075010014400c04092024055001030402440d01c1e40d460403003821907000d40e00d0a0105900700088c40380a08019008030060803050005241500381206c1100c9018180700806080210000c00070340403195440b91000000240d440612405000d0302e0034001400c032500415001c3e81c60107000041c0c80126000b4a1600310507041401d01040620203c025011801082c440d000301046071142c6c0182c45030382e11184035003101506980e0f50350404d20b000b03a41c4003560b03851942d114070802c00c0781c1a184c000001c5840030551403100d1552145144810b4529001d103107005015030145204100a054010a401d40b0621081d58204958800c40041d501d81c10b4041c0107581e0800000c4004000149400005242180494441a0030107a01000280b04000194000c07200000c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 348525044 1250 348523794 348523811
    0x301150e0723130e010611100c210e120301060e121905010f0c030c170613090501200a05070b0618010f06020c010c031704061514010e040605030c090a020903010f 71
    0xa001c8030303003805011b451a040700b03100580581c10307a030b6a0200d0b030a40c1d802580ca90000384c0e8035005001006004054014888403101d17035414110040005025902e01805200c4400030b83c02c0011048038160b6110b5221001450100424001028221402019503104011001881c0170b0724a00e500040c1e8400d00020400e0002c1c3c009030001d0750040c030745032030626040034048140300d40c00403c9001e0302e042026406e4503da03030303070030004031000451685d6011640c45c145080d0103201064014184034144030a480c0c1c1a021541c11900840c420b5142140000e44c0502181c000140445000c50b00040020f00996190011103d80b10600c0402e038050844c07461050010010313030b60144081d42c0134002c00d0074601069652614040e0003280300c3c030900e0740d5060228000a00b00f12495000a034240e06488501c2042d40d100e00800c00b5561500324214049000480595040e24140c000c0da0b0940d00301a02401c133388915841840002076014252080d1103809109030501d83c0c07824411446040a022070200b083c18 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 348526294 1250 348525044 348525059
    0x609020a09050a0f0b0c07050d03030c0816020714040e07172401150c05010f0b0a090207050c060a02030c0105040b01030213020304020a14060405090103110301150e072313 75
    0x1110b607010b02d0103120300300c1d810481d1400503107101040b50541440b2a64804c1031a120a090030f225030011680200e41030340b207c1c00e16031326600041c0d00040075150450380b41c45480900051568008030340c00107a002c13a40500200f02d54a0107103003024000780c004075600141e1102c031821704d013850f04041b0100d965030049140b446000c00594250360271000b40e03008000e905488501d495007050107408501910104c1c191a028460b1400700025500080200000c5150368020005810555a441d124190719003000ca20303411503100f2201400c0d0b002000b0304e40100810203100b00d035082080087c055010078882d0b000c1c940c030280100751180344201011548c81d81103104010fa05007020b001040341c1c80c414820040103890300d041150270345a00401402d15410744000046151142e03410254000650f8400041048107900c4481b12408040700284081301c000a00d15400b200a0301c54802000400404203c505004d04103641c1100407001c80226094a0780756035001980c40301201c1c150452280c01c0c10401c1b0b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 348527544 1250 348526294 348526307
    0x20a0c08070b0a0c09080a0b06011202160212010b0609240f040f061416020a050d0503030906060d0f030e01090b0a02100b03060c0409051510020a050f060c27040609020a 74
    0x2d0703904211700d0585c107040c500b07595180e50030002020021f13840080303842a07000f0980d09444507a10070040d5034605e4000070f00c10010451100c224025a1000e9940c00b00b55018001c0c840051006490301d03042810200c100207002a051200142c80078000709007540411440000b0f1110850410000d9a100d1615030303040e903600540c0c0d211004125500d13141d221a0201c21003101c0f90751103400c0844090850600005800365071580c0619400001903010400f0004080082d62103881100251030199440f40103020b20300c00e10390001422500708441d4580064040c1010800300003044c0740284240c1e03100c4400c644030340d0040c0441c201581c80f01100e046101c00c03034000d100b4507003007c0d40503020505058991542c680102d000d045003860711040001c0b82207041d07078045c802c2c102d00100308503109022500c01175150b0000020642c6d181c02a00e800ba24080070000c0e2090240745c07283d0400e4074201183301042400907400c00b41c200c000908403112003150740c1701d00411020301072402e401651800c0090000d00030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 348528794 1250 348527544 348527561
    0x130204032114070f0b06040f020c16141008070c050d03140610050d020903030c0709060e0112020d08031806071206060908030405041d07030b150105031504020a0c08070b0a 75
    0xc20700810051001030b0000400e07046099020300c3c03017041a1110750000700a0130090000c41c10103807010820700241400041ca10340b82d50036031803031600328941b500710312490383c4072006006802620000041e4269403003440d0541d404085c03490000250003840e521141440200b10850300002e480d107800c125403911405071140c0150045503c0807500f00c000030050902d00075441401b10040d8042610040b540b018022104050440300a43d40c002d616032115800400c2e450180381030301c01d0200000b06e81c1c851000d9440380707003d400600381554501036503174070602a400201031030000854810401c40100c402c101c158082c8400e501c0701c0c1200328034503040c0070842d9641d13801402003010f00c040410842c48040200ca0a071482920301184031500c9803059011281280c0d81003196100e80b003000401d01941d081c21500170001c80500507580310b218801155036003c152440c0b06800c881c0d0030401010f180c0b41d4000c1103e0506d90134100c00b020f4407910b07030040c0c5801c00d540c16202507525204124044c400b900c2517032007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 348530044 1250 348528794 348528827
    0x9050f0a050108370e0d14070305040504023105090408090102010917030402040f0506060d0b030c040207060203040605090a050601120305091521151302040321 70
    0x125142500000d21803180038410705050040d00008250a50b855013801c000c084403071160440e80e00c03030800d0182d05607410485002e075502e2400f40c0b04402c5100100700300802a00640e941d140c08007041e0040581d981c015102202400300400c40011240c445001500d040c000208403110407000703400142c0e14440038070410281125002c4024000c942c2d40c61032998009400200d00354440c011500141e004082d001070103407012104800c43d805290000e0001d40c40703a4420359040c00046054950707042994412b90340c0c1a07000700c0900a100c4480c640e80c0c00f403c3c1c882401011211041c89400205040ba40500401d0342d50580000c10030003032060354000c85802505041c010140c03d0201d450307840c0c40324010301403110706030510400c0c0e40505201e0402c0d180001d20040a01441200e100da00003125449800d01d583c0628601d44111507808400011a103c0c14103d00c03040b03840308000741001401c803c022507000003280c2c20b100c00700115016058020155407900f92007503a4541c4010042d10002c542207100d078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 348531294 1250 348530044 348530059
    0x190c03030c08062103090913121d100306050a090207060605030309030a23060f04120e060d0b04020c01020d02071707150c1707270f030b040c030b090c010905 69
    0x40e00c0e121940c0740d0510f07019015040c08400021301c072090840c070504560f01d07070100303841d0f081c031242c42ca4000c007118809205803001e9192251419068408a08101d2050400322030f00021000605105050681c2509071b40303000190782d500c4800064000380700390000c0e601a40d0104422007048003d1041101410086001314100254240069580c129900317004100205412042c0b2120b1030600d5501c00b00110720307066840d2850410300180180c0e404480c02e0380c000011010214417a4001d2074498401d480c0039001d24a0105045035a4024100c2a841e090f0040d44c00c1120490404081c40075002070b0791080009a076034a41c604040464100b0a1001d5002c041c04120032000144c43e00d81c020329040720f0f000003103400aa10001038400307420f00220480c9191404041214040d40110640e908a42c00c00c984000f241c0940d103801d051f00028082c90b05034000c59841400490b5001081d9503100d889282102c8a503074603a5036007001c0c00001c1e10440a01e91110464281540e0002c8840380a00416100c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 348532544 1250 348531294 348531301
    0x50102010e0c0f220612110103020a0c08030907030605010b0c0705090106050301090f181b0f06020a0b040629040c03050408070b102607140307030803060402190c03030c08 75
    0x5001000220061813003603081c00c540b5004440b4102c00380c04500c6140d6010400d455449000014022070f400b02107070700d43d175101407540e00d56000f44243c600803540c40c1d0341c001200450f9642c941c019400a03110f602c09104003040000091400d000d0700b4040c140c03402041d5128280c4414141c50150990401072040d04521300600001c0c2c0c0c0320090f6030442d044200d0100d4040000c00b6640014202240a25603110b0b01021045c2440796200d2000920845940c000d1441695071101c80c510040502604006030403c0c0300940101d41e1081d21035400502072074000610f035070340b901c186110780f070100e1107007004050400000e003041ca001c1c800c01c806103e25003801d00c5985001d0b51880c02c24400c2000c018054014103002c90150000141c01001030071042c2d00301c0810301559009004517422030801c0d081e141c410100d0210701042c40d06030004683c00080d00620b44241180c2d550b20154000804441e0480d60a11861000c40d2680700b00345601803141d128141d06082505006040d6454954100140b00906050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 348533794 1250 348532544 348532549
    0x307061202030a02130311090a0515010509120a0f060c0203090a03140708030a050c010612051c0e13090303240612061a09090703050411100e030105010f050102010e0c 73
    0x3894010461020016901d69a400e1040000e0203403460b402650030000038003100700408001c1c105a050030484203011071ba66921990025108100c0b0740030a10f100d00d080200341c550068000d080d03968001031080c3e03014207410340c4444c0340106240c410340d0181d40f83c03100841400010300c60110700380d04d18400703149000008004075103038200e5440000e24002d000100040410703414000803000e4a00401a01d40d00d00d80880014840d0308441100103071946070010004845400c6d9020503802c6901c540030f06034040f0301e04542c04071159002039403818080340e441207003140d9440344100c41c50001000c0780003400d035189050050840791030b617601e0440781941248212003112861501c40c02c8580500d0f0126128a07041021700c007400844d0b220346002c01c4120302052005020b800603000702c000c03d642c480050380e592242241501c030140c45c050700548007069404143e0400c10b808000d4840745082024808240380086800c4407000d034091031014403003900900075580d0a01548010031640c0009000070507080c0c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 348535044 1250 348533794 348533807
    0x14180102070308060d0f061e0606030605030709020c0307050304080d120519020c10020c0102040303170103030e04020a090503100c0e060901021e010b12070303080a0204080307030f050d06080a050606030706 90
    0x9203200c0c0250700366031006c000b0030340303c142c05d101e900c10b02c184498003488508a55503648018010800e80c24085c011031003600c244a600c013150070007401401011702e0305c03c00000030740c810010721010b03020805c00000810410030003040200913120050603c01943c0c903008145450442d01800d010f400c00c0288814154030310544145100c4903980140e8484100e60311519003002140c2c1074000500110b03051841e1070065003c0d20031a030007500c075100c03175009542800403a40350901009010800c94881420030f070070994003800d240d00303507803c10003840c50b00c4200003403a1444003c8070740746158440110350354050703000300c80d184822001d0f140141400c0000001030b40342c4030f038103030f2a8611403042c1d000d00c3c10b002c001350080c4101103400ba1150055030034500f18030b5105c0c051030100760080345010022038490382c41442201c00700d5031350901075414842036036021035020401a05113410090305205602c4100030720700c1030000800b80a070007000c0c50ba140d89005403c107480200a148282c0143c0740c10041d0b5a00030b00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 348536294 1250 348535044 348535051
    0x2031e030a1107031d1903081c020a0503040f0503070b0a020d0e0d020d032a020303040b0105010212040b0a090f090204030c05090f06120f120408061003030525020414180102070308 79
    0x69110036100b00e00d021a4002804036200c41c10800c1014000050000543c002d10210385549082e00740627031500000c0044c0d100702e00450000038000c0000401041c0490800f01d241842801a01d26084035034880916800c0c06460b80d402c0700e40e00242d5515800c40700d02c00c3c200100c100c0780242c881c1c0c04407190081d4590031110040300a05071601200c03540e082164002000c411718a031800141806100320095482d003044808484821b032100000c1111b6000140e4040302d401d00e0350740286800d041c52000d5405810409828080c840e054401180c0d0452192566010740303408000140c5991441c1408120700c409580b1090194481d4428040703800308820006520400130348100620070001d14503149054031144091095000e51450700c2d1140344848002c008841000e07088500035215403107008400d444600c40200030980400001da0030880a11205040480c0f03140b80d03680300915600420190b803c42170700070240c0014242041641c011144a145405228000071410044e89603400b800008000c2c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 348537544 1250 348536294 348536327
    0x2160807051e040903030c26011a1603020c0102070909170f0c0109030302030f0f0907090b04062303071d07120915050f09011104090203040302031e030a110703 70
    0x150300894407140425400070ba900002e0b10801030800603090040c0184502c0d070540300000e0940440350490751094190701002d40450880340d44603407901c1070a403110113141410908600c01400306411500070700014a0341280241c01421490b122240024103100036a044100303000c2c60300e2103074004640000e4442c403d003081f00302e074150348002c5140c1840c2c0501a1740e03800080e5600740f02030b0208240d4150055402004080f180c5003107a00c4441104003040c0c0e0444900c21031790300c480c208200011464000507100c0e1030140000503040d80320308400d0b45c11144010322112000c00d22203035940e6070030b080144c000201000448089400c84015a0b0902058094071060400000707804003201100e1541c007170606154060f070610840300c4030158070800f51008841e07450031404098001542940c040c00b440c1000524802a107291500384224070009402c0038106034110f10051040a400c03041d03107000f000c8000d0040141e16201d16094001005944030920008000072003441800e00003a004600c2142e00d1400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 348538794 1250 348537544 348537559
    0x110d050a02030f0d09050601120b0a020406080402040504231b01020319050a0e090114040c020f190c05060c060f1506070312110406210506010c0b0a0e0d09060216080705 74
    0x8100304d94000e007007414409072450003447c00000342c07c003607841002d018600c80c40100c0758543e50b40d40c244c8103c1c000c82c810301022680c901e000400604e0286e001640c000e200c0c0604100840c0d00b164000c00080b06140002c2003948083d40cd1190410032140c1061880024401580761800d9880070410a0320810381040030301c440840e8609046000c3c00e0b58180072000a0b00003203d56a607070206103130889104d041280664074213001c01d1105071002ca8000c1c40301410600170410540c4800b44940d04503030403d01955608030188020070035542c3c401c01400c24092b004d00402080c10003030100c0c40d41d40030190083c1440ca5418480361280d88428041c2c40e001505414070310180303008003800d1000340108100d00008803600140c0031910681115807945c00514602c040e50080340d40c074009a00f1180c00780c0d100c07404221000303e04800100100011a48241105404100c84417483d031920f00c4d02c43c022078440007061110605000c07842c0d04100c1e85c0ca82e484034050300d4141918182c40b1640b144600d004d4a80075401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 348540044 1250 348538794 348538807
    0x10501061b050c03010c09060f0c110f01020c0d060b01080f090d0305091606050301140a08060a0b03030f041d0a0921020705060c0601090b0a03050304060e0a0503010c110d050a02030f 80
    0x1000c0c0907003403003c1c3c00a0020b0080160202004000b58164058440869414010301080500c0703909401b4003164030014407c8414000010820328544c5600c00030304502c9948410941916404811b80308180300300380c04508400110000750071004005c180da0200c03100f00042000e2400002150030324003045040005480c0c40300c90403507007400000e10b2840c0c48009540400100c441e440743c0254121540210014400d0f6811000c11090345e6603403041e40c1699100002040c04802158032071b59040b80014126032509044101c549a26046a800302c60301c445010007012203030300a402e8556128038190020072503110103949260359a09003480c0b1010402d601c4c0d28020841d80200032900242800410147c2c8030b407000c01d1403543e51030090060901250a03d003e03164070313051107400101682d5002e40a1803c107800c0c00b500f152061469288584e200040c160000b030103850a22501804c1c2c5810381e80c00140c00d422001c0c00e072500e904540c2c03076402c01104002a48040b503002c000d9803001c07580c0b000e40555030071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 348541294 1250 348540044 348540053
    0xf021b0d080c0a0309091503080c1e0708061806130311030403240908030a020a140d020705010506060a2001020d050112050106081908031b04120b09010501061b 70
    0x10840d010003480d0030000119a107140d000007440c008158400e82e0790640968a4403205415114000e174528000c1c07515178014000900001c5c094815052000304403146003c0190380c2960f110300b46410500c55401004041c4031102080c80103642c00070460041550081d0b904010f5a03840b6802043c03245c07800644413180701018441c82d46c2c1700b15280c8a10450b0784403900c1e0309041202210b580b103452001007110100c602c2c5401f00703000b2100700715004000c150640d601c2303148200280d40300c107031003200b089400101144000c0380f0b04040c01070b4440380d110040e240e0140d441c007103086420117040244030341d9081c041c0241103540301e0314000144001400200301200a103c446001e4010142040301c1242084004901c102241680e0000140648000d2000d990350b1041e80e601c4e02c145007c04403405031440c1009000c03c00c403000170758100e0940c201a00d03a894150201501540140d00003800c0b011000c2181428000c040d4022078000c40e0403402000b10394501440603105168152214902c03e641c1c3c0ba6035001d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 348542544 1250 348541294 348541309
    0x72a0b011418072006010501050f0a0c0602040603020d0b010305090c041802130504030f18060f1106040305090112060b12060613082a010207030206130f0b0414010f021b 74
    0x1103156481e001d0b92800e0009018000e00d001c12620000031600001c62500e41e1000943c0341d04075075041e120b039854005001d001700c01e1648450304030300510034058080400500790788000c00003445103640042e20764002040c003009030b0b400d811307010341054240024406000c0002c5080f0303151200403500000c0881401181300c252402904010b50301c80e40d8914480000e82c2c054104510a0384240e80b6100001c556003000e4a4880880580118644030021b052013400e000700d4005440f0301072030800016005e0008242071078881c045a040340001e001007400c40b0a5604204110500e4a414009012041c2080c2119005006207583e079a1400d2081d00851004d4649104585030110074502252415882d1000c050f03403110b640145840260b80084072105110603200c540e541064140d015203075a52940d000c10250307070040428400c105080700c1001540003c404040d000420441d0a02603c4928040000b08903840000c40c8a0501c01c0e8666581c8030035502140c0b2500420f05612290300303005c0102c020400701e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 348543794 1250 348542544 348542569
    0x30303060f090702010b040527030a0801060c030c0f0302010c03110f070209061807020c27040201140d1410080a0512030a1103011202120c1305090102090306072a0b0114 74
    0x40c58070f070500c01620340278074200010314140818800715002d030006440c1e4030701c80c0c1002d500000342000014000345218a00701504a8041d10749445070f11000e031100b1001107103520f0102c0143c0e40d201115030041d5018094000b00c0c25510400380d0130002060f90110301881074801c003d200315001d6000800766071b81d01d808030b001c040c0c0406d0680c45514040b000a55260b0244c060a4402c40788001841d01580e43c207021f080395400201c20060141e2103550040d10820300c030801c6020341102c00d11510a0b0103803030703100c0c0c1042c0400034004c2c03030b80900380504c2524451030b45170000449030300051110030200350001240c01494241c54241c0c2d960781d43e102a04c5000380f0724012024050900007000045048a4400303800c038803030080b03440703014401119000c650384000118403140c00c40301284600d290400e065102c01c6c5d0048034480054501840c140c0040d042100c100c0e007080208415080c49000311118030303003c02000324854040440b40a190316074104102c014844c030803a840c00f81a2910480e202e4402e540b04c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 348545044 1250 348543794 348543799
    0x1103010e03040605040905060603040f0204050a0f0c0c1b0e012d09090b06030d090611010b0907020f0f1618020702090411030f0c060d0504020a080303091b030303060f090702010b 78
    0x2242c60300e801c40104160f0081c85114155810b00d40480d00d14580705044078011a03000220031540c403465801c0c0b00c0900740c0200f60a2207966211383c0c0560070862070107036400e1645143d9900c2084059407800041c402000c480712030030040854030512000721008000c1d8107691118800c80030741060340c046145100c1c401c0316850710491100c0c0001600300e46507040315194a20500758004603a403041c00303060351a054520054005101000108071007400303038010206104c0c941c0c0c0007080b44090701000c10581e03c020340e886001a40a1048000540028001040c0c000000c501070280c4070b12a0190381d507019042c0c0a00860441048440b4003c09a19411035111399405481403840d49403504140303954104400c98103000307000e028607001040c840407802682060009101c1307414440c0501029005200c024400c9030440c0c04040085500c0c0000c00c090341c421603c1000600e0302c2d500c10782c00b140000406043c46c82c040e40c01413082c0403c550302c0105116085105441070301d05691008030407809418804445034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 348546294 1250 348545044 348545047
    0x11031c030203010f170a121106040c2409030209100e180706090b1206040e0a050105100f060f1416032006060904060515060d0c18060c1103010e03 64
    0x419254141d0061812550300c00c0a48000d81d81d54046103411a0402c024030200741c21a00e07041c00080c0995000066140c541c1c584800345035841d4407454500001a101036a60348c0109204005444001034800344018020184011241d00040b004c1c0415900b030100910445074072001400120240724490010100d01d0340603212418002641011240c1d140c01c16407090007840f038049402e80c0600403001c21038020a41c1c0a150012010121000c0c44002d011941d005031582d089550909041008410351802240005030341d0909040002c0c1209040c1e100003580e44107000100141d540114110544070001d0601860503030030b010b27107044184216003907001d669a103000c403074084c140d01003800c0008101e4000403500451507a06100d03500c0400701e488941c8051341100150014400750803060308080f01803c905201c1d1010000600903810984180030301035910800500f546600c092030003d160985021880001d04040c00102a0f403554600940010a0310078088082d840940c46824156903241c00d50303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 348547544 1250 348546294 348546343
    0x206040e091207060e07050a080c0f042003011d161101061a071403040807030f030504090c05071a0705250b07020d020f03040f0501030b0102101b0221071103 69
    0x1040200885c081d00c1145104507000404c03e8181440740c8000c1c0c4040c0e000600c8551000000c11000086003504d190304107403140c90b10a5100c015041c04011144103100c3c05442c1d41c10030b0303084803002c40c40d100c250900b245207400f4801d0020b0500c02a0060b082c0b1880d04060b03890b00e8015007405801d00b0303444402e58410600c9005903403598180a042c001e441181a040741095090751503540c2d02030f030b001e400d09640206d1001c100082404c44450300c01403090504034100350365000d00c2001ca814040081c004140001000410466000c0601c480c004441c05040c00f141440c40c0b000f005401020324200001c0e079070300124008004450fa65080b52944a04500d01d6840e1210b4000e440d142184105c1c0d000d44079400b40c80742c5e1141c02005550580308001054545689400d0044019105145410707040d401000000c0c000c0d48418050f02210009030010030200c0b03286100f00070b20341800083c012000910410008003401e180c0811100c0c003942004101240e1001400000e0800a04940c2003601043c40e4403030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 348548794 1250 348547544 348547553
    0xa1a01050a05123c060f010c1713080a0c09111204050c03010b031513060204090504050f062802070501060503190c05090f0a0f1b050301090b010306030206040e091207 73
    0x10313200c44454903410a0700070241e007040d6140310540001c03201c030600041e0b000405e05d081030034100c1c0c1900c10503d0280d0783d41c0d0094840707901c0c010410102d01030000f4001800c280e02e038144002a03004000e500014501c648490b1140c0c001015a402000309407603c480c80341e900c0055440030b8070700000385800c411f03e031418140b80c402e07070b81c1120410040c020350030b01c0c0080303160b8540070500300b00c4425180500c200300c2d5261656205006859041203c10360390910001c02e011180d1300c503051146204400400480c0c240d000742610300000241100d10342250001d14541200310b20420182c14842201c001d40c4030041480c19a0142c441d0f50000ea07018820031510814014140c3e440d40c0c030880c001d09014402c0c0d91030354103001d0441e80440b80c1e041d03803c5248000c00c414516640c02610344040d81000014020070358070724142c1e00d17501d1072401d80c005030004c40140310804441c071401d0300101007420104111451a404036009000c0c0b4400c0040f410104030020700090320a2101005030f21245000a5403504203180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 348550044 1250 348548794 348548821
    0x10e1608100518151512031804020d0c020f01150501141605010222090b010f0e01030605090109022517030c0904090f030e0301090c0909080c0706050a080a1a01050a0512 74
    0x181c11043c209005c511003990309018004c10034020615000d140f030004403248044840500c013103100d800690801c2002c8100e40e1034421101102001d074068140026160791040c00d41d200d000e01403000c1269400c0400541c1e803c036070041000844103603459101c10411441c007c800c240750801070076a500018410142040e06590842000c61600c0351103d120780342e074038201c112014801c11324042540541441c10f91401102c3d0f209482c0030514002c1000b0751944080b07100b0381c4003a404840282c0e004140d011144c4402c1034a9041c00d001c84207580718014281c0c42d9403e0422850880c2900448000080f40310106c004084903a103072005002031044049903c1d00d0510700340d04034030a40000d18084803400da0b5240601900c005541c01c90504a182420026140c0042203061011141c00300104650079582030300340030201c003d2199841d52a1035024000c005020300a00400030716515241509900d19014a208543d00c000c0080c81d015849070f00d205c80580c0d0600c40c40d0032a0322160302c003904004c000e00d0300c02c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 348551294 1250 348550044 348550051
    0xc150203010b090111060403020312060418030e030705090405120f0d0203090307060b0d0f080901020c0d0f03020f030c1011040918030e01090b0313111002010e160810051815 76
    0x85e81c5880040d0800710703e82d1582d50640380103005130030030000051407400c580e901a4121030700070000104040900e800c14000003095108070081010310840b52045d250510a01c0c00510083c0d070b4500c950324080e9a681d8841c0500c051002ca48000400c4130041a100d44090b50300441440e03004660703a01300101003c1d40c0c6c1c1c0010308102c407004c1c105140e5081d00d003881e01410280650244d80f5507282055135844104507000314241504601c84c80c02c4c884d6213540c80480d14210680030341d1840c0c1d00c200e040d040090411310a1000100c0d554800c0040c409012800140c16003014600100000c1c60540c00003504c44612541d4441d411203810507800c0c1064100c0c21400c03d950910a8489000d4251351000640d07c24100740b240d00e415000600026904240360310091309603510640c000520780240600041555400d9440400103039503032800d80821260811181529074002020394070210b2038084040d603201038100c200792030715840f840810302c00c116000480b4140071030901603465820201641415100080b07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 348552544 1250 348551294 348551297
    0xd0b090408120717190f090b1902091f021c030e0607030b010e0f0f0d0f031215060e12010606050a0905040605010c080a09080a060e0609010e0601060c150203010b0901 73
    0x40c0403030180e901139803500741c0c01400e000e2100407503034420000030700020500c2d062141e000c0d00c2e102c950401a809106000065214039000d1802e400c040e085c0d02540300e080303080f2488a520402c40030310307581c0d10055410181c56012414803002c150f813038000c904000c3c10030508007170002c09441101c285034058106aa4244c400c00803034045941e101c00c11804d032050380c807400d80801c0c00c215140b2400e04240d070503280900e001030490301945076500c0c003061003c01e58a01c20744144070b01c40301000c100f5500c94034104540c00c0c00d0b407040c0411880c4000321030784aa031512401c0b09000382401d1004182d1240c100b07150182000708020482c040c0e5814001d0901e41c4400c605200250000c08042440d03e040d00c50001038030410707035800b42580c00990712490150b010441103020700010380ca0000d0510000c0110903809482400040b461440c0c0d59145c910b40a40648200304990412800b600300300c00028407a41140c07031030301d8008203000756810810100e0501d45201ca611500020002c80e0100d2660b00804500074207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 348553794 1250 348552544 348552577
    0x60f0a020f160224031b1e1201060f080a0506011b030809071a1902030d0906060608250f0e03060f06030705061e180306040b010f0803070c09020d0b090408 68
    0x7604013a0450519103240000b564188041169002042e803c0c0410350001d80d1480e1800a88840e41c6030030510400c00320125503800201c903120703840e01c0e82d000ca006180e80d00713203d403032030414001c060544140182890400d91b9a813000130442c1c0e1041640712800c072004100700984480500700209121400c441103d09441030640c0055050180d120240300754101c0506242001c21009100c0004050110343d28114401803240380a102618071a03d0f080910900300050000e1515901500d901401070000d10011110115035681c80140203014115a280e40380c4007200010305a800e50312094107032159078142c480d00081000000c903003508107010f00011012904150f0340c50742041414032a03a06458203000243c01c90290066459000e8444820711104148040c82c0c40740103e49485405c441c2500c410000000400203080c200710408003904011024600d0100592550900ba107210311402d414030303500040c064000041da61052102c00d03001004000281054100764030990407104082501140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 348555044 1250 348553794 348553819
    0x90f060e0c030d02030313031e090f0506030108030d05190915110310122405150f01140d02040807031202010c03180206090102070306050703020a1d03060f0a020f1602 73
    0x100003c8160404021380d00441c43c503a5908500fa629101411080b42800041415012201c48003501448080c0543d80c8508155180801400b46400d0652140c5d000d0f4504000501010401204686028011042c007055640f5001c110040c50003178010260105850468810100440c0000201c000522420b081c031640c0c866016401603403000707a07402e400c5610250703400c1004102c02009003641900844422218100882d00b21b040e84c0031a001c02c8551659030000c02c0340005000364100c60740c8100380e5001801c2c9904400180c61f08400300030414001e0f6002c0b0700c881c03400c10b40342c0444000d000c00a06561080b540c4c0d25164100d65280c0c1e2581c0095400d1000035540f00e4440d22400d07400490480c00c9044082c181d4080c0019036211041e20703070460080810100100f4818080c2a001d00100d54005994090303010005020540080244240365101e84c408000f0365400101a6002000c143c0f80f010300341c81d25402880284160400034100040110b0a4048016051080c2d42503034000da0f0100c40190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 348556294 1250 348555044 348555049
    0x90a050901051f020a0f0b1e060303220b0f1309050f0103020d0302151f0801020721090e07021b06071212091403040303020729070204090f060e0c 64
    0x1002d000b000d4100740b065240c0c0c2c882c5144106040ea103071110340161070b40041e640d294060b0304030204100b941d90f44091010300c0306e45801440e000079605800c65200e1030700c1c201000001c0d1031384200350390102209806a440384901c0e1005020000401c03251074010344c0d800c001200400309401801410001840c0124002060056400341c0c620581da95a42011306038215030803c40c550003003070001d40452043c4040f645000c81d240c03000d50b0182000d0714a5100a542e180008241e101103034000c0e2001b0b900501003100007850240542d00803883e070044c1d03c0d081400030071003100d5154095102a25104c1c002050001d02e540200303040c00745034000d081400c516a800b0040c8591803040610080c072501410180c69001803155040c82080402c0420100380350920351500040710b02a490000034076000010708208054042000000801c902c000768950400311510000f59429407899032501144001038035011903950b0b40c440d001c00c643c800d14a110700d49032820000001c09600c3c0d00104e42d4864041d0a10591 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 348557544 1250 348556294 348556309
    0xf090706020703020105070609020603040606090606050a0c1415070e0a0f0b070f02041506090e060405041208061305070216090203061c020a170a060b0d020616141002090a05 76
    0x903006500103049462035a4011181d591100c1019241c09030f481c2c410600594601000318044d074010a008030704241402c00c07040407079459502c804248502001080000c98101c1c0c000000d140d00080444000d900209205040c00d80040d0000c60805005042091840d004000b43c820200180e800108040c0c072145a020311500b94080c20768040b40901240c80021441240048600e20207440440e80c0b40c402041c040b0a01303559041900400c0e02114140314039885a81c1d2281d2045040360b003030026040544030140700c40c0b410544e40c000c200301040010220f85900080310301002100004100070b1601440080d210707040f4a68000c0c003982940e10000e550002e030300030f982c02440000d01079000c006080344514060071144100b26080f05003003000040f540c0c480036170300e017204140d2006045462035074a040022249100305042c4100c164114590250722140241d50283c58141d0209014518034100001e4080340b080380d40e41103218420107074178450304940182110b0001582c1c09000c0ba51a0000c10080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 348558794 1250 348557544 348557549
    0xe07090c0813080a0903050d12201902030708040603060602060702062403010605090c04053f0f01110d140c030a020a051306050306100f0e042c060f0907 67
    0xe048081c102c61010500c00c40040811000b14142800f2103540c95442d1401c101c040040d50011072564903081c42c07415032500a0703594442205980c0c06480901c0d207100e200d68050000c0455400000b02070501886000300100c41c2c1140c0c114150640300e42d95040c006001d400e09010f01030041c002d901c00301c2c24032800064038901034803101c10010514544041c41d1004034904114055043d074913403c0024460720760b01b00660003046410f507540d90b62030819042c04000c100e07880800c3c2c0307031f900ca00200b0070004a101100c0348086074081c07064100700c2e43c6001031601d05180310001440e55482d18591380303e0b41003030300c0c01094100307000401802101c032803810000800714100c9104000c82003c0000500e0000c495008101c0903c170380c140241822440008907110340119003010340030860020034020603142c00149074081d0f00c00343c0352007810f03450007d10003860180c0e0584d901c0e005546030502944e00802c3c2040382001c05e00d598801c42e03400e02090420313540d608016200c0c018201071941c0494940c05000c50076074203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 348560044 1250 348558794 348558811
    0x30e0d030207022b2109093809091b0a06050307080c0909160f02030702090610090b220506030c09011d1c0605060306040b1602120f070201030506040612110303040302040e07090c08 79
    0x200c02302010042e00e5600f07018502c00340796511049070080c080d940e15404074040d00d0352000510b02c0a21005036000b0503401c000e1040c0c0700f070891560400401d944031080313031350104c00d0340707003a880da07455610303140f00c40b03000307aa80450703004041c0030030401c80c46c10030840c1502014050b43c03401002580810141d07181e2154007c0603402509001c0010700e00e0403c54408000c998092409204050340c2d800360101c41e402a256503424010071800c1e40c00d444000700000e9001d010300b01c544510710700781032141141511550b414941400044400d01d03101603c2034030038580805000d0079103100e5103071400c1c904100601c9072400300c8010f8a007801041481c00c000171a58407440d4095041003003600e6022402c00e04c90682000d0504501c90843e080c1c07040d410520181240c010303956041911108a480050b060380c0300101110b005071f28000003002801401b40d00350316035030742050341c02e0303840c10060700428203502c61500041d403c9410034088a064000000d901804c13140000c504128000d50000111440c0b40306030f44988 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 348561151 1107 348560044 348560081
    0x4050117210913062301080901021608030c070614010501110c010e04021b0312060321090f011e030e0d030207022b210909 54
    0x264076001d120030503414030074903503a55401c18052048524811040440b40054000203640003002401d82041c603401415600c140080c214100c208101c1d001030362040010b803080700f061082c1d0700b0310303100d00c80700110011058507100d040c1e410107030028a404000704142c0c0006096442210f04086659406411540c580340c000b40c00100e10001100064020101c00129070b030780030348021803800c4221401600c2c2c010004c00000d41801d40c1c0c0600b4060b01c8001214580c2160f0780b59500d00c41c0e40304804407103802c409490442550b100007428200c00c1001803001c58500c0c504050300513000076041c5040803002c84006c03401e502401c00c249100d404607564010141c00c010b800d111001d00e82e0003a0509614180c0c25a001c5144203c900c0e02c40b01d040b03e0354070340001030311822194003001d281d0044c0013181070301503100c1222002d950004011011644601c00000d001120b8002c1d01007459100c0b0446 = true := by decide +kernel

theorem cover : BRFrame.Cov 348381294 348561151 := by
  have h0 := BRFrame.cov_init 348381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 348381294 ≤ n) (h2 : n < 348561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
