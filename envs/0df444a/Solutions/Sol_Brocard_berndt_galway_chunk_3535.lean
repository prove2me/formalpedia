-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3535
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:56:21.588668+00:00
-- url     : https://prove2.me/submissions/2d18c985-fb6c-474d-a4db-9a01889089de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 635611510 ≤ n < 635791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 635612760 1250 635611510 635611549
    0xd0806060d1104080d0504050117010b03071103280e01181a070b0c03040c0e04051c0306031403070b010b19030216150605040605030f0312091e07080601170c 69
    0x90b44400b08241484040032045c800f003180001e04010650b4490000046200c5114484010754180816905688000341100d0200141250607901d44141442102e2145058a14042c51842c181650301110f8802c02610408620710380c040c94000c0d4002e4180488001c00011200f0380c0c181089010700320360001e8210090701c40c005202007000100e02e01001409038071242546912407400c1d10304a110508603801120b0391214070401e100020718002181d41414604200d5550540d0411100b20001d0100d6480031b80030000300443c20980d102c0200040004030f002d80d961007516070304d074030840d0b00c41d11601c00008d010f00d40f210484003020307110368094230b0800c0b800100d450a40201e82c99008050812142050b5120383c1c1c0d81e4108124a403038410300000b01015006807481d0421005003136101d004030304040001c01c04101c000b50700541e05102c526001d00f0080300750328a0301e10081c80c0c0c80d070f140046d0007400c40d10f219010003c2800505010b040c01003a2005006100d014011801e20100c0d800380101550308 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 635614010 1250 635612760 635612767
    0xe070b0307030608100b03031207051905041409060d030c03050d0f02030a0b0906030a030804110a0e2a040308071a01080102071506031e0c03050114090d0806060d11 72
    0x1a0044100540c0120141d0703401180c8203083c100e9550410303501c0303840140c4403480d012207002c042c0c80c00720554454090520300c0203216a540c54081c0c03100d02c1404090703402c2112922041c1d804c19001000340090b114802c0080251100c804103101155070203440c0d07250b1000c0b00314540000203114a0034001c40034446d14205091006c1c1e2003d000907a085180c0d00242c064003c02000840c0e4034030310501e001e03140111214001814184d020a0700c0f080070500160030010900b0006051240c0818a480c4c6084041e101c01e118994907035120004410684810074910308065a06005d8210b0a00d4503002c440349110f0980b030545159110b4480e60b20001045512514038401c600385002115075090007011400e00141e587d80541c50107596810078840707a804103a00c2e0640600110b40254600c00041d5003e1408403000c0c061820b1003202084207501c003c02d198242258031100149203c0d80500031032000c000c5503205a074200e401d8071010000c54481e0780141e000d01c522603003805180c00032081c0581c5042c0b13440c43c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 635615260 1250 635614010 635614019
    0x60906030b064609060e0610050a0e0d0f032c0f0d03030e060106090503010606090e010303260c071509200a0f0b0a0206090d0207051e041508010f020a020a02040e07 72
    0x2158030980d10509a05540c0c80c001c0000b0146d10714440d51041040303489085003070350b405000d0300354010311005a0410400c040030401584542040806140d00000c0705a459011450014420501c04000b404001080c280c881d001d6100f004108402100040012107083c0c1400b0a0002400c51b03000d00394101911143d51b17240895003440035a01902c02070356a541c1d2035042000341030075a01154844410054084800c01001b10000e607241d041d40e070703d86014102030010404024141d0b400000345101c035840802480901081c8000070042c091040e0605c080d4404201c1483c0e00303c0e08061400ba0540f002c141001d15643c03440307281200e21680082a03240e01948540c100c504081d0207030800c850000f030001d0040b0103550100011644001e940000381003034a80403a00039100c40c00c1344202030281c0d2404089041801041c2d01d13122160768007800c1000704c442d010020070111045882030034165403a015056404520741e0085410045141c2c000305030031050741d800d0100404600034160780310f0043e80d20218 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 635616510 1250 635615260 635615389
    0x415090509012414090a1409030913180605040501060b1606060906030f140309120a06051005010c0b06030c040c020a0b1f0e1504060906030b06 63
    0x41c0225550000051030450451510121110210110310780001c202404c102c84104180c10b1451140c0581d080142511101200f030060700c101d07220401c0d881c00071010407520a000202400012104945800401a800c0d104504445202c220440d102100145910200d519500310a41180c404c0b8000512035aa9241031070707654204401113100c0c502100300c0d503024000c841c000c80d005004842c07803c1000502d1a83c407915100700f1070324003c0840c01342c401a00940301e400e0080d12030184001e0100108003d0003c1c00d207495202c12207048035802e2070a000300b0140c500c0308809074103441c0c3c1a1204058005030741c0b5203204000700185456854070882680c10702070340710390041d02089203054004100e03102051500982030240203002e110080007086c141a0415125401e0700202c80000300450980e4a50300d6000c0744134419500620b4110741064400540d66080e0341c440004c0b40e014042185071030b2124003c00284442c2103100c4240800000c0d15440b040001e4503543c0c40701d45c0c010705408605240c3c034000c0f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 635617760 1250 635616510 635616521
    0x3080a0c260d0b030309060405120c0a0b0c011b0f0509060705010c05040509010e040b0f07020c032a1905040209060d091505220308090f0a0803180a05030702041509 72
    0x81040e00c10220b05046940d4041c00b5124000e10218095400e202111000c103000d030049100319481f440d1a40750919643c0002d0201c0d180c4a103004e0498402940c4507111300200f030b40841040b031415840d004083c1c06040b10034415500301c50255550a400b2800f440c000c0740d054005c070040d03a6020b4400c00003800020070900c1040401c071541e0312405e480790314000070000c514005a00000c3c190158404000014004440880d03101c40300d0000c40b8080e03159484120b11303029040c0510f51f05403081600d00c2c01040d440f54500b00340880c0b00b20b4030b0b160503843d100a001d0a0f40d03c440008000c40140c2c03e06001ca80781039000791020307040107003003076052107030103100041607907040402a40d19540c800c410820303500d00c0d805043e030b001c5406611400364929664582c03d100700c122a0103020410313800041824010144625003e0043d00d2003282e440e56014101103025600954564500140002c031854041d02d000c10400301031600f1102440c200301c80c50302840302820001c038000c03220300d18004e0045607034101131203007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 635619010 1250 635617760 635617823
    0x5160b060612010f170d1202070602120a0b032127090406020408060c03151009120503090a08071a1e07060515091003060e19030f080c0403080a0c 64
    0x14540c82c1c40c1401625901504d17090b1500d401a0348800c0403150000c03140b1005002a080061340c4891b41e09240000b400392444060000c4002d40500081046a17041040303c91012000d8134145811a000c107200c035141800342460440b01807020300d0030f02d002c4902c031408205180c02581648100300c0c00041c9031407800c541c100c03a401e0380480c0601080c40100f201940c481076040a45103141032440e00250300c103002c00c2016120b02040f0f141c01c0e840a1003551544002d040b501d101d884004410728009840740c101c080703014000c801402e030006403003c0008070b02d800c507202d0010985200042c50031480c104d030b10030800c0300b070322034001d651402071401d03070745c00801007540036090020300b900300851140505c0d17507410381300743c0704401190a225220031902c3d55202280d501000000344514507802e100d041c4464a5803270211090ba0441e00c009064200c00003040d4a01160340b624810f599503070b0b44000c00e0149000240031041705001340034006010300320080b0414003900b6021251003220103020744c1c1c044c40644 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 635620260 1250 635619010 635619029
    0x1704060f0c022103010b07020607030c1b1a070b1f1d010806090109022b0602030405150f07091a1c021b010e0d0f110a0f03080705160b06061201 63
    0x2029240d200c00000308400c040c0c03010509813a5514088032050749000303202c0d010b441400c3c0040c0c01002c050294560350a0740351b0200000e40320705218049411049130354414a4500c840e4204070444c201007010072120368507884029450300c0d440e100300c041c90600e0f00409602c4da09142900c08500071110b9450140e480b0f400c181c1c444142e42c1051025414007801819402d6542c4c1015560310040c0d40d2003a0b0342d103040c20785503450b4403104003c0c241c800006455078400b40c002c40c030000911040c0321010403201c05103203140c04a000981c4a40c00400ca000c91700301d03092000140b808000b400781d002015030480c250542c025500d400c007442100c5807202c0405015101001950004112120194164400c01d92181120080000d031f8420140152107900040ca1001000800540c2041040c040c400380d04006021004465043e0118501340c9440000d014040c1d0209a41d540000c82c080d00c204d0885440f04440c40c10b05503001841d0340c48000211000d0141548000d0034884000400788403c1503078000d001c2ca50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 635621510 1250 635620260 635620273
    0x30902060412050c0f03010504030206040201050f0d0f0f0c020304030f08030a020702091003060506030c0303040b0f0412061505040614040504030311071a061005030106081308030a2a1704060f0c02 86
    0xf08010380071742082aa00d0280e4180030800c0082030700800d00039882030702070800382e99511560b00c6460f840e21540740303501d90b170601d040b54001301d05000e54401c110740ca041080801514030004020f90340e03800750340f10080c0740810048450000401d0707a00174507000313103c07580e02500b4200c6550000ba0041803c4401481c1d81d000c80e07404006201d640e008054010005030041d0103000b690310b004ca5241d220364001d504081000164903581e001041d401c642c020010303803101080054561612601074440c140a54248440114002c11180740c00d2050b030084078210503030741c910a004407091001800008100b40e05040e9181a207070b413600b0b407910080c40c042e0322407107940c94480326003a5110421382010b804c3c503002d800c4141425031500d80040880341511001d040c501011358403814146005001c058004080742c001106021140307106030400000c01a400062042911243c2070100107a100c491140e0000340742d50b2400000d86040d140f20980090085002050b6a03407010031220a450300305d00c00300700690010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 635622760 1250 635621510 635621533
    0x510050c07060306120201030504140f0f070e01060512360106090203070203031f0f090203070201050703090507230a0608011d060108010b0c0f01060618050a030209010603090206041205 81
    0x244a51006042c0c03505007000100e041107190440580c401600a060680e5a4080343c18069110b1040001a907054100c8035030b4500020f4160301c5490000c2c00280380d114444003c910f02c4501c03401e1074141d8030151f03107140c02c0000707280d9080c0c1c0074840600f00315051281c000d0342d4aa54100343d414168121a005881c507481b0340f691005a003166415400300d54541e1050003030122555010080b40e030481951400301c00b4505502001d4030150041c2c0c0c0c400c08070f5038012030300000d0210300d070b802441c440c0185070000c100d42d1f038030310741e040c0c050341e241c2c580003011074001d410240212a688915121010740500b44e4003144c41d00700021600c00750081d00100d012805801c01003092825519a400a04d034860750840700f00e04100b000646404018010f6051403c008131b0250428201008484181d5600c8c00082c032400d942d910340600b1504610314404081003400c500440d4504022004d0801c80c1d80c090329030645603107803c42c120020550004201d074040c1e03003040005a00c003004441c03000241d0180c405803070704820b403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 635624010 1250 635622760 635622763
    0xb03070602160b030408040b072d0b060f0904170d02070501151e052b11032109061e0d0c030f0501060e040c09090c1106092e02040510050c 61
    0x260f0003902c0c400c204008000008000d0400e60f0126400141142e071a10224544108290000c0c005030004a0b4130043c1610422090940503020301d0181103045030030340f110700c240405000002210343d00027150f10701082c001048ac002d0005541c0344544591f081111060341c01c0280c0e403280f581540c15a44036180301741d440c629103460f64000c008007584403020742403020740c2d103040b00090320555110b200e1444600103151240140380d00e00841c3c1c8148040018001d2404484a8507940c09490291107105441207424007990841d100c50303a41a80c02900f4400103600f006816480302041c010b40400e00008960b80003003400c05024101c0030b110707011950442c50b560040071075100807500aa0142040d00410580750001241c4000400076280030403074bd071407035a09036400d011a6001d04c12031407411650450702070380120300c100c10310755560685450f502c0301a51955221114006000f40070718a0f05615004e0340305640c910012071040b4009418242d843c80050001003d14081034003140c000149400e00741070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 635625260 1250 635624010 635624053
    0x71b030c14010204030f060e070b0409090b0108030c0c0f030304030606060f2d0302090a05090c04170a03021518030a05180109060807031d060405011e0b030a06020304060b03070602 79
    0x801c01c000314201441d60303c44190389840241d0251881e40c0c0c0d90301c071310328001d01880703038602500154040766655a41d441e64030008050112050343c408000c40d00110701d0790b001100f00c400d109460320003014031801c00d000b0002824014451030b070789481300f007200100243c07450080d800140916200c1903e0200306101c0980703040c020160652220040b981d848152111603482d07041d02070300610740180c0740c80700c12011038622510342d000aa40015840d00300050014180c0080c8261240ca4042003040600820b00507134929000d80001d001d03030810a01c9004420319510303c076610480d240c144074140032615942a0450744400714030400a080000c402c586841503034288000c400c402c0c640980003600d4050004c0092001514007801c160301c6002100386040502120a480307014481030b05d0b09401c2c01e1070040c1c02000c40209030321142101400800311105140714404400601a000d80381600c40303952400000c3d80000c108840c0b1640c1c960b003026003514100f14000150030b803500109158068110120720079032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 635626510 1250 635625260 635625293
    0x10f050f0711060a0b0102010f0e03191d0d1506150908030a0807180b120609010506120f040305071b051921031b081206100f08071b030c 60
    0x307031080042e0744a6000264198000130f8030400040310484200100d02404814403103080340c80c04c0c07604848600d030010000b07019407a0a0340441c4420380f41c50b0004d442035107003140c84940030000c0e0100a8014101060a10400c5210b0848240f1403020351040c00d040390810780100c0c0c000f480c000c45412955821800c100003034120381000350304110155800500500c0c000340404c003008201219407060003036550019028200c1d802d115a01d503140c1d02421480a201120098032440904000040703d04041c000c43e0044610715078503000c0381d07641400010906070040c10032810480100038600c0030405841d4440d049003d8124281e6085c1d1400d41000400d1000c41c3d15040683d000b81410044010801201301d1141c080750000e03d05080c4074103080c2daa24504080101c660380017056050304006100c40280b4885002c0c1d90800c030581c42c1c2006000c0b070180004840008a6400d2140d0032401e0300405085600014a01d09420803402041c0401060805450b003100443ca0708a1480708200c4005100203a0f00e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 635627760 1250 635626510 635626517
    0x12120109180816051204081f0903080c0315060a03090506060301181707080a020706021c090b030a0e01061805011401050a0c08040506270a0e010b090f03010f050f07 72
    0x10000c68407100754521810039010040700307a030044201041001d01013000c0c21604180c0e090b0700c0725600c898042c4c44400040c000c6023440600300842e4030341403d80c81401c0b9200d4041d40c600c5400e599618945400d680054650900b010307101c60324200a42e101b000400e83d40d080d960300841c01c58120b01d1f00781c0c074180010b0000c511a90401000e0907000d14a1102503034500d03002840501040c4082c425040341d44540880a88004000901c9000c41070b00000c52204031046076080301c10913420364500d040c0304a000c400c16000124900000c005d1020b14002841c0c1003141010005416030036001d0759800c6943e5a4044410502094015134442c41d0038804c40d801442408118541c00b0f18000008000744030340905081403000b00c00c206020f20454030160743c040d00300644159591014030b1a1070141484550f41311804850074000440d0b60700307111025508840c0710001c20b80d816400c0846a14a682141e4032944d002155403100c206503560034040c0a5002d200000001840e0a0010188602c070b040100b168007407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 635629010 1250 635627760 635627801
    0x10b03160e060f0f0f04020d050f1e040c091d0a03030b1203040e010902071401051009050702010e0a02040b03250504050105060a0206270a0614060301061d06010212120109 75
    0xd6214108030a0880e003048417075404401e40c03040028000e018841d602945070b403600d41003012007a50040850b0144c600c90707113924015078141d0207104020304100d40092504241500821100030b650b040101c040f4094042000741c1008003051700c1c64030380c41c0070040c0c0001e03468164400b030030306194034042c002542e003101070351902d820900d5145401c401840b600d040749a00280c5641442003e0510400e00c0e21580001c0c4102d007490400c1c4455442d00d40106d1a940d4944008210a20700500c2140522075852018220540081e020000208035448405815001c0c2802810390010312409074a028011502e42d040b0701030500d01800101d484c140c1000b03000d43e40c10020403040c15000280d213907000340011902c0310008d0b4519908918104a11002d0610f441031210200410245d90403501061170f40711142c003001d13a2580c040509840c8e15100d500f18035429402c41a0000210207082a440081030040720302c0e41e002d030f400c8004954442c1001e00f1400b0461030041c0000142401600110035132101108203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 635630260 1250 635629010 635629039
    0x318050312072006042003030a0203120703090b1603110a031b020c06030a020c071208071506060c1502160507030b060907091e0e100617010f17010b03160e06 69
    0x3910384e0b015202600c2c601c0d2540c0030400070841407480c030290311800740c00c0d651034000d1003102031340d81d411590307034842d00711210030009400e03e11034031640400f240c103c014114030b1f03190140000200c41c00403a11004150b21b031202c5100f085551401841c85042c40e540020b40300b05441f90441080b00781c4545201150005410416207a070388205980d080000c6102c01603540140f8000700d4a044500e900210250056a59030030500c00d83d0790107003207494000d030f2178841c84180300c003036540c11034400c0d0042101140b41c44840300c001c0340070001c80080039100040010701e000c0b80003049265425500c9011105d40d84251001e208101c16401040c0d002101176441500e1800d0040c00500156028001d00303d03505031210f180d58101201203c10002050700c04030510090070210f0150540f0601c81c0110400f0880540845d45048240091036041350503038801140320030b04140c131404000c0340f81c03002d11016649401881d07410350f800f0303c40c29900110608200508034900150742951801c010000f61107000885040305 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 635631510 1250 635630260 635630263
    0x6060e01200304061409090a0b1e130209060403020a15140a0507140a0c0e09010e0f0307020607020d1707060c05090a0905101710050112050307020103180503120720 72
    0x2815240d01c5d060070404040101c0080700740740268840039502501c003805008420a26500000c0030550649040c820f8010340b200c40340e48090024422500b102c8100c40030003001c541039020703168a0070000c02c45483d244d62034000400ba00c1058111890b03100d1810b0030b840080f038002241e050580c0fa00d145e494209002a180601a80202d000180280c0050003004004440510a03040160b6000c00c100180340d898956040840c6c03400ca5900407a5864904685c015800010f005d11008143d500150b00d4929107a0a0062682003c00100c2c0c204200b203106500140e5182d0909101117801c1e0300f5161110b046080003410384200c52224400d100c002c1007000f47d1900d07013040850989032983c5011034240c0711080269542070490340030082c0b040303c0205103410903401007041c0d000c80c0700c3c0a2041c4060b9807288904400851420300003001c95104000032030040d4000c2c0c120b0b02c1142d504405126400b0501d0722901c0c1507078030250201188d10318002c04c1100081e00610861211a00b0f0808843d41c500b0319507003039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 635632760 1250 635631510 635631517
    0x12020f061014010306090f0e070501022805010e030a020f010609060302062b0204030c050a0906123e04140c071403040b0c03030a0c0e060a030203071206060e012003 72
    0x42e01d114061440452980d011703411100c018074000b0f2003080308034202d0002000800c0321a20780c10307090103401e20020b072035840062080c0c0808240080158606010a04500d4a03c0a864100d841755225076140c1491070081c00581002c1000c0d8015000384008013a4081c04c441981e0009a4003603e000801d101684512099800700581c440f03d040303565030404081c408011511454842c7c05000107400700030806160648012078005a4031000400d4480024100341c40d0940101490342d012010104d0200702921600e00701042500070280c412005110502c90301500c0039008100c0102080000740035040c144281541202041c100d48410304020380c100e0741d03d101d00ba801400f5040d211041507103001051080310001c04d00e03894115078500c0321451241d00d81e00202c447c0729000303141138085044c9500554040e900d83c0300050081c0d00e400b052071419002504003074440d504101600e410903084140902c110006041243c50305150510107800041560858100b11506000e10b880650321419000042e07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 635634010 1250 635632760 635632769
    0x3604061406070c120b0109230c030403030e0712020a08210a0e030106091e1a010c02010905060c0a0312020306031011090a0b1c0213060305071b15060b070b0f0a060305070312020f0610 80
    0x55990720f88bd13608048001d004a40e42d40d001c0c03070090303d03c000390412042c0700424105100b6925001c916540314038030340d00c40c105619444c403000c100c46500e5080020040090046980608040c400d01c68040c0111342100d0301c54000304042581c580c00107408801030010041081100c07002801609120f901820789440c030607480318140486100403e08581c02040350b84042c02000d080152158071200455a84141100c0300b80c0220b8201100503100c440140201c03840340501800070901d120f65480741d040100200e0f001e1155a000c140f12100c1c16688000b041001414504071203a154010400103c2200c4000c502441c0000e00c1007120b01350011700104807200702c0e4068140092260f4500300191031520311151510b11410780038440204112008040310840224500c040021a841b00703100f06c000c0c41100406850b01c400b64001940001009404a40c8140c4401c0f02180c99580c99440c0707454002150001c50312400d060040c80ea070300783c0c104811240c1c4096030740100310500b00714000002d081e481e4040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 635635260 1250 635634010 635634031
    0xc020a0c1712090a120b0f1305060613060504050405010f0612030c0b070908030d05011e05090f0a0b031203090d0306030c09050403053604061406070c120b010923 71
    0x100014035540721000d000042c41c1c15076040300050390501d000c40d21006c0072517203010500280310100d000c0700042e10b0300003111607118005290540305c00d020400036a5100c10f031045c1c1591540e070003141c240c03603d01030a40075a100b01700108102030010604810f07101c240d042280310b043d00e06541d00119070321020626420b500705030700a1580e01d910320211742c8101907811540ca1031000050300a881c0c1c5182d8003060498104103207000c40551807602e40b041d410924070410b40d00c0341400d4046080460f04114854202d0350b4448001000d4444801103800c00f00029082c40c00300c03401004100300340000348000408403601c0d18040007400d04640c2c485649510900549613001e50300c0c0002802c04d8064002c8030034030321844041020307441540c007081c0b440210114040001d505800c0803420903007414080c04080d070320540000494980d0000a101090b00b0801c0e056550540800b40002c90790841e00c01402c0d864045e41c03507004558101002d0009071180708528a0b2002c03180c3c9403071480c892140c11400d80200d18000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 635636510 1250 635635260 635635267
    0x3040302060d0b0603130605010e0c070605060f03070f030303060803090a17150c030405011a1e01050d140f0907060c02010c030c0605070809100203091b03100c020a0c1712 75
    0x2558004200c0c0d102e100750801130000c14081440300b901c4000308560320503c01402140c0e02c40201c043c41d8102031f12038104000040c84040000780003500100e601ca0805025104405000c5d400680342941c50342c00382c00c00c0c6818070024406d040d49030003240041c1800c03a000b5451706840710045405924a84201c80c40c21043c1c40f84990603003000c0c04000c5079002804403000c003506165590201507801540c0444031586854982190b450200c40700c4080341000034041c0d802080c05000b414107070020260464100501000700748041d94091141050448000e40c82c41340c286412a58580d170000e0240a40b0950741c0100c6041041561200c640c0048680c20701c1d010740048454901581c083c1c103110303c000d140a042c14200a030040d40301e04000d00c90001002116091000000028100d101c1030354400000d070808039941c89452680781c0205c840c1e40c00038080700c440200c10b8407400d040312200100d520060700505180024018182ca000d000b0300001d008001880c081165080c0d42c64140020b594524203012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 635637760 1250 635636510 635636527
    0x1a03040c09020a0e1c02130b03010b030f030d0b011809020906210901180c030b182e2904021c021231020a051c030f0305090304030206 59
    0x44082500030148550155140d03810f042000c2d10380700340c51008a00a003511800000245501003c90700d40c5500540015940d03207040700c21502400d141e1420713030303010b640f602190741d82130704d0400c209410881c00d40e01540d2034815403032616060301c0c014240e90b410014a550360302c04412070a03032504125601c0e100010ba603404940041ba140e030049111400e8201c2c40c44000e010702030074011025104111010081112445841d12410110ba10035005001003491540c14000580d00032601070300449076a201025220b25412460315222031000030307648038440d00c21444200070760806035070764220303103420140139018002d038000b5007042c1401c0e1081d004007500c8138000c0c0030341c80705d604030bd0f0100c81010900c0c01c80011881d6080103541301c00a0a5030230159500001d60481e07588209c2d00c40019a003180c0e80c0d52003400600c104e4892501a07042e40c0c00500400001a02d40d165800c580800d045c140c0505003000c0b080c03e02602c81c401460380f84041c1820300c401c01c01842000700445082c0c03a0304a031300e00d031508100c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 635639010 1250 635637760 635637773
    0x703051b0a031a0a0f061b06020f04080d021b04090201120203070302090a0f050307030b070912120215070e0d0f0614160306120b040f0209040b0a060806011a0304 71
    0x24500c8102040400140521007030b41e264120258443c0d045544000e0340b03a0201c00d202003020390384501c020ba80860700041c031085104403001c034222088544062010740c00da840304030481e884480d41c88012400090700b003000b401c051004041480c0030380054110060300d02510841007811541c0644625510b070074540c1160b01030742996245405111003151207141c171660182c001e40c05003c8441c0704107500b80b070009004100d00610003d950010303001d0082c20340b8503500c08020520250001042c4030540201155050030640000e40c6240240c2d0f880a0002c4000c50103800c02440f8104604504445000c014420ba000300c40369031026400e031411013000d0600c0c1090702c240b00703140100600c098240507080850400d034070501406140840c2250400011005007901100d00c00c0c8105900840401030000100300c0c000002540980030705260207075a529a0f0004980c1d8008030740440305009440b09001400010f441008042d0508000401e22541000c40c0c80b80000380c00140803106e440d0000004007003005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 635640260 1250 635639010 635639041
    0x306050a12030309140d110c0a06110f0a080301050f01110d0807030209060d0e0d0801030b0a0b0112020a0f110d0537021f06140118050a030b091203010509070305 71
    0x40001e00034818a10030700150b606d41c03040c040a80b0000761800301c2a850104017003400c0c002003200411410000346041c1055595400d4180301d04194000c040318001c41980a0081d51104c1d0710800c20140d581d8100005c111410409051590400a640d044184840b02c0050391904a1859042c414070070340d00d13501c04034044e12079818440d8210401048405120406070048080d00c00441c05031140b00302908412290b0010920016101410b12000710314200742c4d07503111445100042c90140c02904020b01c0c40ea00342c1c0d1000c558a400140070360600002d09621600c80003c131405500984029062504c00030b02902503810308038071003507101c00c1c00800701c0d080f03030041810317080d84031050a01c1d14118000a500d803002d203100c02c0c224000750324118040c0006840340030140d4000b000c0f085a480ca4400c01100e000d029640103d405030321012000c511036445003403d030025441414262034030325000080c14103111018000c225181e1040c0300502560fa0344c0003100c2d0b8026403601e0300050507981c0e054070f00d80683d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 635641510 1250 635640260 635640263
    0x7031d0f06040306061505070b070f09150e01180810020f1e0319020901082206110c0c03060106082a070803070f09030206030a1a10021c0306050a12030309 68
    0xb400108000260700901c08480042410344807015980000380d40d40c2c420500300800113180383c0009110503000d1400d4580c01000c0c3d140841c40c075902d81c146103000e02e02208482c0045208518482659a404200c62412042c1c17584008021494002c1c02c90b0390302502c080b00c200303150300420500e5007104028180d4130013681006682001d070501d00c103422150343c8280c035800444100f0810200c601d401307074000c0760600c11043c1d603584205c0d46c0340c1d00480c1420302840ca5608200c1c0c98912600c02013041d80c002d6500300d1b010302d201d940e6200c040d17648103851314607800c03021400381d080320700104102504404000d03440b18100904500c160030307504000302540322454a0080b050303004100301d8280030480c000746101e0880ba4032000703210983c2c40d00540c0d00c02c1061000950200c0d080000613004c01103034204000301c6030702d00711290480d081c1000160700321141a0752080140d100e440041c00c1680342c41ca0070508405903040070012141098040f904c0346910380200400300c0c0c83d4131518410148a54403032982c06 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 635642760 1250 635641510 635641519
    0xd140d060f031b05030c3001051621150308220806091b0a0909050f060115020a03030b01050c250602010e2d03030f04150207031d0f 58
    0x1540c4032089480e10140c580020340700007072810104030b414420000500240e401c010002c0510007800c104203c2d031110041c40070345140d009203426070701c1c07101e00314044150301f454030001050324030304000c140e810300050820113007c001d080f000249881a0b108051003010181d01c0b000310ba490041c2000c1000c0c4070310b603800100380e40c2001070600c03400100005804800c101c40c000d0503000340e50710703540c45130707201c1d000d5030000507640240307104413800c03034a0140c0c510140d03a0280a842006541d0300038102154105a000d680075003000d2080c0324150028040c880c003404250521414039002c404000355038070fa0b8040000c05055540855414682c01241079600c082c00c02d20841e0035002200001003a248807400c200309090050b010003080c040d006000704000c0709150001894540c03196103942e102092440410001ca800300030b60460504400e000461159840f0380f094000b601382464205481c0d07c0203610300100030300c180500c10029910941c0449041184212140e0702590000090182d1141d0046150701 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 635644010 1250 635642760 635642771
    0x4051002070e0a020d05010506040b16170d0b0f01020a05150402010201060f0909170f0703051e1209060601080646140f01051b03090d031205090f0d140d 67
    0x3d00681d41c00410740103014070b4090005076030368070600040f0b000d14010070a098406101c035481c00000c0340c080702121401030240c905c002c440c203080d0140c290301820761284416150101803030141420748059080010138801001a0501130300c6141c1ca991aa0080c06c1035600e10f0000705080d0780c800d41100c0094200c42010040b6559100001c4004000d0f0100440748041c00e81c0c95101d07a540d05100340c0300b150307916400c51490810103a500b25140d50040030a4400000c100c40030400300108800a012500d00d420308250351810001542ca1401c00020146410403180e074041212130b40b50a094050941002c40301e8240e28524034035600c0d042c2d208244d24290745801c0c013140803140240e482e980700448034820f0710381d12401c0c0400e040c41206070700c046080e400700c1c80c20405841c89003010082d10350b40300395000690f420070440000003000f0b4407402a09400040d000300302d00c003008003a44030741904480d0210013441e20700d0f4801c010341e4507640c0000103001442151301d0b0007030425440c04211940050700c103404018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 635645260 1250 635644010 635644021
    0x270b03041b06080915010303050405040b0d050109110118030206190302070b090303072c060705030d0218100f0804140c0a26370204020c0a0311011104051002070e 71
    0x1602c1103903550007902c50540901781c038030050b96240d41070320b4050356a18070b028103010903c409818860704e41500846410511004a502885407115903481007011001940681000620984c4841c51418840d054007004000581c1c840040702c0d041d000d451110700125040100990080c000e0745406020564030f4030401100c42404002180310b0201503d070903c50001d112440411170108808500003441c80c802002e003185001005850418415411280707804280a80310003603030040896820392010882c07543c000c9241180c000a04043e0510f400b0040b500c54402c002d0091070041d0015048081000d65010b010900b88110f0003a0a0054100610340b551364000c03d2580c030312400040300207211303400d00b0222000081424240040c0c1200c0c0c0316000c005204200d03403580d010790050503018810210107801611240060848044100060019240f031410007170301124120240e00d009074902416501070700319200c26079081d1607017035071481c0518001030b200b80e19014040d001729070800100c20070842c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 635646510 1250 635645260 635645267
    0x51603140712180f12020a150816030509060414070510120509071206050702070e070e0307080706141605011805070f06140a12110a270b03041b06 64
    0x648400c0b00b50348954940c0e01c091000d01c201812801415038459510710700b0451180d0615079005a00d000030414940d0581d29540c000c2d103082107906c042d001c56030310000c0204440e14200e100c0c402e0000c03420180420b10340101c0280c0c882d003004100901460035154a1002d240040100d5405000094402501d1056180e030242c801c1c01d0840e0902c3d005401c3c100055141000403419200b25000440c00510019085d40ca40c1c0291900804150440c4070792480007504043d040e402d40e005a001d52a0403c0c9884120281400c1c500c01b5002800c00d54020f020401006511140901030040040000d68030b80200605074800c000b80c03d030f805483c660030060701180c18a55072028001807845803040701c9190741d4549040c4000c100e984100008074002c40d904034402c19030704c001802c0d11800c40c80d00c803501e51810703654003040782c1001440d12200380300030400c2e010041d08072000c1c6d1100c40c011680d114a40b5980222151148000d006924400c103000c40410704002c64071500d50340d41d9501c21020030101d40c5440009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 635647760 1250 635646510 635646533
    0x3090203010e1501050f0f131503121115010b09030c06130503060a0b1f02010b03060f09011a060702010f02192904020a15050c030301030503280516031407 68
    0x110a0f04040400003403d0300d08010726049525002c2c0071010249084410418280b10401d1140c100585030f070b25883c004184822202e0156104884108410000c0c4400074605143c40c40b0034001c540c00350400065030084060b00a045401070034a041d41c0b0036081c00130a040c6500350400325005007012809900c00f4124842000a60b10184c00b00e4910796201801c0c681941c1c0e1201079140c101c0ca20084007184480c5001041c0c0e61402207000200f0385c3d01001c0080392824030102c681c840802078070000e0003010386080c040c100107044094180114401b00800160023403094080c000d040c811504d0502007242d0080c807070102101103800d45181c0811603800c0c46440916004084406100000200000c6010340260300e4016038002d00f0b83c1c90741e607044c41603030107054884c180d1a1007844411300c000002000204002c40c0a14851006103840e51807103091003940312003201e1010480406640480c46840d8410260780c402800181103114004a81c1002d540c5403c21019404981a0002d80349060140c00c1b24203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 635649010 1250 635647760 635647783
    0x907120e060117070311060304060603120c0b060d0213090303060b040801090201121a040905190804030b070801061e14040801091a0c04050d050c030f060f0a060e01090c03090203010e 80
    0x203603d101050915007646030340da180030041280354181082c00003802c000001d03591007845800c00180468072519809c07180040181400002420780c80d0341401c014122000d030703403c880180c0c3c600219050a500040f60585840c12644110303684011100034144070703800200040c40c2d00d81c442136a5030781f038401c014060940440309a0110b07400c45030380780c3c0e01c060a21801004a58441d080e1990b031583c1410003000d45081c05083e2018840c1c424852120a010702859070007510519626503113500e14a003500016000034040d0b014414400c0041000ba500429035019400400003200c240380d034544015a80800c1c0c41151000e10040410081506001588024482c601504001c03007018002e1041e03600c1114121890120600144800c000c1410300301000300d240e600ca00241e400380c0d809180071a02d0a82c0d83d18200e1a0307a4041403d000c0e129404203c01030b004101c1e400280400c5040400c0e11690110601c6440741c4540c0d00c2e46107081452090b80401c0000780e00074001d1001400030030501d40c1c4d540e074981e01c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 635650260 1250 635649010 635649029
    0xc05040f0b040b1c1e020408010501050301020717071406070302121005060a050702132c0a05030901210903030c020d020a0203060f0711030d0609050c03060307050907120e0601 77
    0x2058040d040c100361400c4420341c0e45094a0401401c2850070303400c4041071390503441030f216044d007000070720441d40040c00c001c1c800d0001601d607464011094251034060f44920f011380d10400140011418080c00c12182020840c3c0840d564000da1400201065008081420310b0140c42c2c14041402c0d45074005040030429110b480034983c0721961041d000030580e00c1031a034880d2081015601c002d020300c000c0d1016600042c069001e10030140980320130740b1085611005460f80800710403198124400c204642042c043c0000d00703903a00a41d07602540d0340314412000703060201d10701280f0001b007a40c00c407403902c651a20b201071101170348902e801341c050004075a0103005030040385c03181c0c200c1d148001140308400b40c001b40201026107a5905100e41c54202400c032108000c159009110702200400082c00e80f500010030009549240c4480309080795000b403c1151090000c10600a003980c00245030401e03500100c0320010103480d0104296001c00c400001c0416550600504002003800410658105c441581 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 635651510 1250 635650260 635650289
    0x72d0b010510080601120f0e0304080114010311060d0204180902031e0307120e120f0606120d12020904090f0c0602010c05160c091407140307020a02010e060d0c0504 72
    0x40c2004a403201600303000b030028000318009000381d8480c6042d1044644100000202c680f40303c11070304156155020480e0456100060811880009100320f00e0300200002c244007040d41541c1c0d4010341442a00d030389038851000480c4010b484000ca504580040540301d00b0b080300400d8425091000d0241d80400364483e016030110300703802041c4c14041d121060204400765113480a40d0b5100d941500030482c80c44104200304659041300e4590704035203600207880600070031031107480703100c00c900e8103000926642c00b6035104487c03c0782d00d240005a40c161030b0b1842c2800c0e202051a00303000740003030113a1000e442d8424202102c01052040340035074100e040e809601030400140d00c80405900b40c4800c81c031598000f88081110010140b009503608041d2841414034055940d620300070b9009031078440081425801d070340028801d803141c2000b21180a1111020024154900001c0c0a504d0742041d07074020f4180081c5425080baa0f665800840b5208003014104010300581d0301c200600b41c1e00103002e450689004c030b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 635652760 1250 635651510 635651519
    0x1e0d060e0a05010e060607080c0118140f0703020f0d150f0b090f071e111005061c02010906030c0e090c07020907050c0604030e0102030c100c090623072d0b01 69
    0x4c07800b10384070700310150516181042941e1020080d6100d0fa184581c19581c0d10041c84424044030440580c0d58040c00803100520041c1800c5800d24045400041190f88001d40800058550342035501204000720340c424102c1c402c81c205030f220742d0001d01d51040600c0c0b034283c1c1080010080d41c0491000517065400f40d180d40e039805c8510384030040c00d44481c1c000c0741108100c02444020200e01c00c2a9904070b01d000808144007602e8946000301a44580480e2070700c0d502002241d06115810000c0c80d007041181c410303026a02d80001c1d111201a018000c109900ca9100c90100350080c5a82c1621002c0544140451314103001882015040300c01e04a20520750b40011403601c0d4802d10903110101b4500020b403142c0d03140c56900b079400d01d00d8050760700d0640c08244800b44000e80180140d020014103240040f5407040c0c40d0340000d0900b13125401c820306000c0008041800b210141140000d40d0441c2d410455803a521810000c0c0c0c0d8001140c444e034104040c0c0145003040000c09441c25040380d03c84c40e036044a991f00c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 635654010 1250 635652760 635652779
    0xd09200603010e040803040503071208070e19030b180304090504030806120d051b0d0206010806130b06040906060e041a0a0e030901080703020c01060305060420061e0d060e0a0501 78
    0x20311400f02c9000946002c540800c6406004541040c400e4003220310700034903076075480720707004407001c0101c04504204100510580c0001c40c4010303211040f40e0410001030a80d884900b200d0782404054034040354800011000088100c480c040120f02c0d201701d0341ca0319941e040c100c000d0013049808030002115180410720a08207001c04080c40c411030360150410b010000e000300e0b80364205000600c82c10500007000c00f8030940c180940c12507441c1a5020700b20541c1404401c5e440d06401402e08071511641d404680049040c282141d42c103c04205d8000c6400c2c0c1c05820200e025040b550800e002c5e1210301001d02003000917250b0500c2d15001a01d0100a29503950010b8408480c180b040c4113290f504100200d841c80e6104e8407070581d00005904005003013840d14881d4a0840c0c206030407c40c0c2c180d00110902041c89040c00303031b0304407241c404000c582030491088085080c0340951724411881c0e040c41e004000c0c01c0c6c0c1002c025504481e403800410051269907042441c2c28103003d841c0c4900949c50710001040449a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 635655260 1250 635654010 635654017
    0x4030c0603060f230603010801091a0601090e0411040c0801080c0114070201050904291e01020a1e05060f01060e04110405150d0501060e0a08010903020a0f03050d092006 74
    0x3000c03607488503203440c0160180b92411150090f03a00384007940702e12015542c5d07450165002c0c1c0407100001803c1425440c10f40c200c600c81403c440c8200744080d08200780c903a80492031405448070603200d80c1c01c90b00c640c500404900c40320008035078004d0500f603d890301d80368021120307412201041d003165049542c8a0064511481c1c40c0c00746508008104107040c05075000340300805030004e01403c00034512426800e81d940c0c90071500c80040d43c030076010f2001d441c54945401d02c81161115906146403498008002035070313610710030304014884102d0402001e01d90901d0035400d50301c0b580140c03d4038030a20b00b0003480481030809004d8400450485206210541861300c10080c05508680a25142c141003000b0400c080d0494100181c07406810400b500401140380100c60090041e80c0322041401044c50400c41c003103000ea00301c0714082c3e01d4040c80c4000700e5400102a080c1d02e4010010382521130070b600b02265940b0035920219002e5040c183d0003020007080541c44041d031000810300702001141c100030000c6030312 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 635656510 1250 635655260 635655269
    0x7020d0f08131e0212010b1306050a030b130f060b100c240e1c0e062b0212190617120a020a0b01180605040212130311030f04030c060306 60
    0x91001c041c2100240c0140ca0b2465030742882c202010545010b80d00049060224005040761759440e200440c0e0641018540d158202e6061182882080d007090007045680d50188000b4017404440c8000c2568090020400c1840c1c50700314080d294000750a003810300242c0340820030a801090001940c8414601c40d10580c1ca0403540510781040d520b00c00d815000c8010751403085e2038190359803250b2020b180b182c1003218101e0f034418070303059094000da0341d03501078101e5001c68403050084404000038050b0090840200f0302c12030190244140b031043c0383c40110028000c0301409042c101740c00d4103109a0640602c0c0c4040910818802400140e440356440c0c85403e410300c00b4008a40d211342840460f030501e15012b880ea48056204a94085840c0c0c1c640707100225082e40942184c0c0c510003c0524481c200c1e0042d40040c190944040d0719009080607080a00c0c04024008100851040341e08000c0520485030b080002c0710440407292100415640f144056010344012143e07111140310001c1d0700e0703000380941022039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 635657760 1250 635656510 635656531
    0x72f100e03070b1b181e090106030c050d0609020c0c10170406021e03090f0303010b0a03051005090115020c03070608010b0d06051c020f0406050a050f010203040e07020d0f08 76
    0x8845a80c1c4101c2d5038005072807030804010600c0031038844650200900401800b550302603400014030803e10002034542c41c0b030150001d8107200c1080c6c20303458104174a811a0003c0c500000c2e04116039070126014019001010485418004006240440d070340151211000d4507054848041a00c41085400407402612102045209404148110032142c0300c40d030150042c4400361426860040c0d51500102440400401007808420701030103501c2004100c46003c220b40085155505154442085000d20000103080540345c1c0c0008030807001e6110804003d241c040e1108400c0d507112a42c045244040501c1b0b48011311071108010344c0f92a0028450040306c60a44130b4509a03401d1203030840c03950340580d203d1803aa0f03032034a8001506855000100c2c419a811720000c0090f81c0f000c0c4100a52982c06100d80d074030482c145841405240c0d5149a000c3c100ca8046900d126003200d50700040c1d0031402154490607000480700c00704007055030041905800321100340d46000322403080940550700030009440c6440b04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 635659010 1250 635657760 635657767
    0x1e0c02091015051c090c0e0c030411041a040e0d0e0f06040618031208041221020903010603061503140d08151c23190803072f100e03 58
    0x503028000420607910342c0b211038400780f001150031000b92005c0d04d808640200800c13400304041d885550003550030500311080203156003811b449030500e841d11101010b21039569000b0066568210108000d0101400340041c0304040760782c0403682d2034003801403001c004200c07c0b40110203c1d2600003841c0324840b41c0182241d0515042c06001c0702c4004d624421390410003010100807000ca0148188002030002c2c940c0e40c06014909440d29015062000c00204248104418a05201e005215400001c5d4625040060321841084c0010b4058000f5078006418a40351443c9108010100e021440c1980e004003045811264100745081d43c0e40f85402c482000194524082a200706540203000d0080303400030120f10f00706608d40e8a20100c44150f02c011907aa07000040c0d030050159507506030054040c19007000d412030140c2c0c600e00c030800704040b90004082c0b00d00080040d030118003440c006035407052450744860703003141e0b00f20036200ea103d4101d50700d041c0703072181144410900d942d80c050b5008440205026509 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 635660260 1250 635659010 635659049
    0x15010207150c0b01030f1e051c05130e091203062101021c0e160b09121005130c0503030f0f0703030e1002041403030301050a151e0c020910 61
    0x3480340712201000c100909800001089005507618043c602038660f0f21400700c15840c04c0701c1e015486282c61009843e52455a0300460303000f09050130713011520700c010401500e5411081383c0c18400c108200c40d11450100c000701d042010181c03020311400700d041c201d4403051900354020710240009c5443c1a480240c1e9082400c00740020000b081900d048100050b0510203142c03005000c10750500c1c40b40c1c513155503480365281700c40001c106c0c202d07140c06601402c1000f9401e002181d2060311488642030300600d040c1407282c40d1164200b0590b100840c032410204014246000d4541c00864100c40503100b01d610342d000401c0345d15000c8120342e0389145014142c3c0c039042e151080780009400603807054081c10b59648030410307000300c244203030b81460306220001607849043c80b500d0703041c6040c03601d4134600a5000380018030142d00e0304001c01055a08031a000c038401054004200d40c2c0200c41c1d90700c3d40141d031208801c1005590001000f143d032620848188100c2e64428403900c540c00002d00c50505e00b107903684961003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 635661510 1250 635660260 635660279
    0x4150801170316140105070e0405061009091a09090a02031209010c02131404150e0c09070818070303020619090c09020c0a0f05070e070f12050c0904051e15010207 71
    0x160305103c4e0100201496501003035034210703902140e0450104058030301484c001e14251040c107502010031941c4640401030070000a040040c14024200003a999402c00101e5140c01c13040513a0601c4000c004200615240c0d1070705440f40070400049009100c0c1984101132591106c1c1500d00341c54040e902c82e01034030f001b5000c002c00c0804001c854407845039114080640464840d079043d1040d0300442503400c19860008200c02214101042411560007201c1041c01d25502c0704c011a410581c68600460305403114812881c86840100384c2c072400340f254500c004101030300891800c2c400c1400b08221603071500c2d1500803800b543c001c0781006040c2254a0418040124941e01400340042c2210448400c020b2607038400d58010780034802a20164030125040088a019070100d6502076118500850503a104079809010090034007400758409849400040950303100100b40d500d1031a00404c2400f990420f0a005a0300240c403800c075011016140380055058000e40c403003000500d0b010ba00400f41d079460008000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 635662760 1250 635661510 635661547
    0xa1b0b13061d0606030715050304330903080121020d1506060507060e0a20030307080d0e0d02071505031005030313090605040b0d110114041508011703 66
    0x8481c039aaa0304060200c0c0b51901c02e80d0ba5070698207030018050340c20000700b09031501c0c4480c1c0c80202c40c03801184003050300d41d50100a40e50000d0f88821620019005000c400e00c2511410383c4901c26001105081c1c0241c800300d8120580b8980651181c91160341c9a40d2680204101d1000c04200030b19200c00309001400c140d0181c0c04418080c0141c098a20030070020002510280c3e4007010010380041180c0017400498492496003400b214020100c0c804207030744001300000c215020320400301000e48d072003050741c80c28022506110390080b0039035502c1c0d8185440c2d5004202a1400703001c50320501c1c10011101d40001260b40580e07101c51303145140319008042c12a103d903c01400c507040e505030740ea00007460392010409010700c5c9095010441d070fa2428621014100e4295071300480c81941080543c0007261105d41c0300150854014400750100e40740c500041e14051b41c2c1c040c9044215000080c0055000d50311113128000c0140f40e503070100c2c66643e401000511014481041000c1d4004100c0c00c040400d110448 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 635664010 1250 635662760 635662763
    0xb09100e0406061e0512030c070501210c0c11040c0e0607030e10090e0f07050405010c030c0228090b03150603070807060305070e0409030c080f0405060706020a1b0b13 73
    0x11031020f0300c1301a030020301107034044518088000c500051146103401c0c02c0031b604003c2114019810415152802a43e403442c600c511414800a502c500040c1c03243e40c0100c0b04101d80c040b001b40109082c07240c0041401181d85020b0b50401d0dc2100040114540fa00449030041200c1da50203902c85002400c0026a60003c10103c00b4407050488000d81c030b80303922001d85072507020b6403901c2c08030f681740034002440c44c04010a8481070401c50030801590030f400c5030554059540038a4001700074101485c06603050240044040c0d48203d46001c03125802c9410801004420f4881d011400b001c1e640354903250640782d080c4402503042d000780140c84500141030500d00d034010030040031600200e95406000d410a10340c1d800480009444000300b040740c40d001284161a0784050f1001c01c803c22054400500b460080e0f2001058400005400041350b00c041050301c001d04001010320380e03071b02c030b03240b50800007540200c500704081415420000c0b0318100011000700f003075421982c1c03032040d0381e68220694084a4210070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 635665260 1250 635664010 635664023
    0x40b0d0611090901031209060c0b190209091602160f0b09031c03020309070501051c0b19090b0a0504090206070618140a050c09091e0a02030a050304090b09100e04 71
    0x156103240d603902151500842c0115540d20b2000361b0f6100003840c50540b904103400f440114418040003034000490240d0012090307080b503c080f998107600c000a0321542c0385032940080000c040c000565141d502c044030500054080320011280164031510402052103451003d229500041003542298402030142e03c81c0201502c591802081d41c0008500843c43c0340400a507000c0f040099602040180001030b100074201103003884441540c080c080140c561012003860f4480000924a8842890036002c00c030614460051042e00c6911140003028102642032103046008800189030525210b000041038000e86810b03d0b15041c0e0300c0b02c40c054840c2004042e1300341855030040c004201010141a80890b100700a480d4006e61410a20328040300c07841503a209804130000d0007206140044d15200d941b003401080c40c0c00d4142084014203014101101a4047c0a00300c3e41c1c01c10040084010700948905c094100f2400c0b5044040c0030500c0c0085030b0880103205586814001943c85924155100e032241c04c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 635666510 1250 635665260 635665267
    0x14010602101503020303030f09010c1d060c0a080a050703020105060402041d1f0311090601030507020706030c050d1401060f0e0a06032a39081c18020f040b0d0611 71
    0x1c4c0401e186500417280320b084100c0031030034090104c03000e00802c02c0c2d204151501142034000d84900000f9402210710b61803203a07100154040980909101d2003281d541c1010b002d0303845209250340608542d001c5d070000c50040d441c100004005207014820744060328041c00c40510081450441c541203030901a0007001404c008094100c244014104000d01551190340b8044074121110300307018030008054062814903040000f0000700903400141c0008036410ba00c0d012074000054101601c142c0b140d043c131041c40b81e080844074205003010310f84030741c100c610303650b02d00c203400717010308000c8410541c40b0000707641c00184100c0401c8680d02c04e8210005001000c0c5100508107003403500c2c050030f48908140d1101040181c0300851680b400c244010705008440001c0e2404080d40340c075906524032064a005000c40e40200b50012682a0310352010305907405003100300000120040d102032a4910548128420300940c0708400c5941010f005070b24651201400000007200c040c1c0d240c102030306500c10990109082031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 635667760 1250 635666510 635666513
    0x40c020a21052812051504110f0315010e01140a0e01120e01050f1503070504020a27030b0a0c020d03050703020f0a05030109050108030301030206222301020114010602101503 76
    0x280c1c4450f40d0300056080c4080780315980030043e00b110b014680729103100b840c000420503000f0020f40d00f40f11102007164000b0b80300c81e007002e55403084d014040070041c5444012017040644c0c1c480b40400140900262034890101714290011113070920400c6c080c031a01c610a01000303100314042e80140f0030320700b814108231605d04102c0c01040111b0740030190110b035980d120f205109135114240b580a401050140c017140c0300c03000c0c51300466581e1416124480c0106d03400911903903c5407050b079480038000317030005203840960b803460203040d40b11040303010a407801910540070480c01e04441c400c40584034032a03000341c001c074001d40c00d041d4003c0000030f0000b024503800f0002e40c1424080d80c4002c22456215840380742d00c95051203104402c4500580003600746a04c10001440940c1d140410b5400c60307041400300c8201c00a114400807403080a9901900c041181001c003107102407014554000b00450030b038003c0124a52103207031101d4240d0207101e6a009604041030f640c0c07980050f42c0003200510105042200c0d01d0b0742d60f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 635669010 1250 635667760 635667787
    0x91009051002090a12051f0c05180612010e09101503020f01120c03020c0708030403081606020c120c010c08010e071b1529061213050a05010506040c020a2105 69
    0x6090302140c2d5900601c8200d034052803080003243e41040c7d040c004020040040401038040e00c940c001c3c210690b2240e40080c5440c2d91090110388442500c10300e10400c3c2c1d69144948000c2100540e060445170141464100140c6010700c119503000d03a41d040342d11809480c540074807010344648403160f81000445411410082d0044c0220b00507000d49a60060341c4565044410b801d142040e0000c0384140c001b004108040390040064981c05000d0b00382c080f00d16241751034000000c2c0b00b803110b403000c036018090f00c204044101c04041c110103007511000b40b21100000b41b007114000d109000e00c1c0841035030340c000300d02040d10071b08665840356070303840713080d100800e494413015007940189000c24502905c0d045030000c1b0b0181020720070000b4101d1401c44910307210410015106002e100c1ca0103a40c041500006143c0410311403c0700080303500701c030550f1020105400e05a0180134100c411602079400d11380010641840090303404c0320030760000c04c20b0f405d681c180e1680c000f04031404841c81081050a0010140d40c048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 635670260 1250 635669010 635669039
    0x204050922120c0b0f06030c06070b160903051c12020712050d0b0603040f11010503011d0c120901060e06120a0809060c160315020909130821091009051002090a 70
    0x40317440511140d03e0032004041c58040700300d81260103000c0501c8020001943c80440035041501401140320b4502c40d24411558203100b6440170340180b09900380e1810624910200d503801608581c0d83c2c40d859500c003410202a0b11605070002d0008098001001c0214030600150081e014034200210350240d540700059040e404c155404c4d2004041c48011108104190810011099080c01d04904540c5843d200503400c1d100c810320180d07080d00b0480050710401071302d0100c4078050070b400356901d524200103c0300340c002c0c5143c0c000c0b40c9810240801180140c03800402044009280600400c07626500d84d131080d4294101003d035a41214050080b000c0454051043c890341b1594600c070902c0951441c244400840800158005400d1042146894030340310500c0c01940301923060030300305080c41c062610340c082d4480c103603440020515050744400910070725a01c0d9405088404111540e01c10401000307000c65080c4d5400034110303844503888031043e0a442e00581440640241034102e0155242200081400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 635671510 1250 635670260 635670271
    0x27060e01150e01050a35070e0903030f070216050f060f0403300e0105030601020f0601080d0207050f03190804090f0209100906080a09060608030d0204050922120c0b 72
    0x40e030010044c0064108820040300400d00c245900c4070300c552560301551039140440001e801d005902241040f0031303400b080184000e0200c0314030300340c5914004440c241c4a40090300c0c0080d95040000104030007601c0001d0412580417109031914443d131a140400c130b8001d41103404140c12103030074004800c4000d10400035200650081100340c400054144000c19507042c926000040a40005480303d0070b158000102c200e603140078240141d59860b2040141d151a440141c28100c03882040c00224040030003140c003041c40e08294085609482d01c40d000c0058042505040035003661280c4112040c0421418060aa047c05048060700e02a100c0c2c00a400307854800c0b11010744c0c4d54001071000e000b4180100001c10304c03d10b52070060301003414041c00401c0b03018003800950005441e07154040902c2820352081005002d55400c1307a64420540055801035001446801c0c81403429500140c0712500e800c140c1a0071034400c0c1161100031b5644d40c0c40c856540d16100d041e0040005004d440d000041008843d1401403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 635672760 1250 635671510 635671529
    0x1a3109030206040c060507080f07050f0607020d020706143007020a1e050705090603010f050f070329010309320106080712061d0304090f27060e0115 65
    0xa1600381420780c03130101298404800c111080021001142c2d10710309554240410079203042d6921218180f0600c0c003038100143c02c0c101d0080d001072205441d00002c5c0102c15420903004e030b500c0d56644074015a00050405520100300c03100700f1070100f0944d5846959680000040c43e00d96600544100c40440d529003207401c2400345c0d2000a0303180c24816401d03a0480303601c2c0440d1981c41100103550310640c95000502c5032030300404421000c1f60417584c080d0043d10f91000804020000c80c03070f02d10781c03000d80f0a5056416001007854071414102160b1081a55101c002022076601c615000c2d241c0110014003d0070341c19106003461041528074140404a2407082d01c194030416511007c4101d40542141c00c40e500080840c0d002d40800c0201035684050301c0540f5801000000d15803a0800f440502c4031b04c0034400d5070150200140204007210168800701103203081d050300300806010310701e140b0300c178070903c0a121000800b0f1080781d50004540d500a0391112421900115a486180500001008880c1c0003002203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 635674010 1250 635672760 635672773
    0x31e030c070b03190603050a031809090f060b01090503070e042102030703020c09010f05040207051603030819093302030a14100e0103020d0602040b031006031a31090302 74
    0x803120036410004c2114074243c1c0400c9264513550303580e6521030100c04010244649906000f4408981e40000c80051032a00e1061200c0d04183c03400c600b15014041003164402d10b130001c44642540309010f0507050710005001002480d06165844041d02d030300800894000c108550100c1102d02e9000300e02d50084079640065485a1142c40c3c0a42452440c01059000e0014000104801d44205601c1c80c1252400c3d200141d6459650820b0307403c2003010f2050035506011142c1c000101640824101c0c8030385290708a40f102060b143c00040140c40403480042c0c0000300350594603030010303a83c0e241c601c00c08010040c1c000b5600042030030076080e81c10464406c6080b9594a0716010355202c100d1819500c007140d045400c03900c604101c0d80804c0c5000601020f800341c40c2e0307034288504009960341101c1c05880d18cc44584e460703213001580081512254040d180c002410450102040c003d0040b103040e0545004200c410001012101021a481440e00091240b0300340908501c2081d002d00c0b542220301d0083d805804c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 635675260 1250 635674010 635674021
    0x50102070507031a0f10062d2304080c01050a120e100e03090603180a1a010513231e040507060e010f120c0512280902031e030c070b03 59
    0x4140b02c0050500e02e41ca0300304006c02504080034030503a0107403013403410102460806280e245010040303520050040070300607840e82d0310441d0000c802442603100d0a566000321284107100c441079000b00e1089210640c0482482d01c050341c007600141500100b01e14201710018407a403019400c1d224a44c0c034110040c0c201c80741d040d00c1d000e110700681346900040b2740298600085140403640c1c1d4400208588082c6c0380c20100c8104054090052203403141d0811403041c0e148508181804501c2400e100f10752182c035400c81c20242040d00ea0052011500462400d81d0031850391814074045568003c090902c0908290074054802909444443c01079000b0401800840d082c55005481c100e04204550705000d04202c1071819207500400c424100501c015011a17407507100c8001382c82c1806030b6040c3c006441d24400422405004c10240480b4104000d0001d8511007403044d03400e0704903071195070041d4040d0007018184c0041800c035542a01141c0041080b24940000400c400d400e015440c2c1080c5801c1070000b05022 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 635676510 1250 635675260 635675303
    0x60c0803012c0717090312130203010207052e050f151504060e0f0301051b0f12070c0b07030b0d110a0509070f0f02061e06190603020406081e0408030405010207050703 73
    0x1a801042e401c015481d1070108010f2200c140802045001c00c10340d09141c8001715142334054846032940001150308900c1c0e0072088801600140c2d00010100f0300ca20300c208480c060324080c083c0070701c0c0000002c00854550542e44542c600d41c216645401030344803d094004010b20100410003000d0756569068a00c243d1000c00c503d0350041e40740e4900c20b03818801031241003030110340d1f4011ba00c50704415040d80c403000000d400f03070b02c0d000798004915645109000c020450385c12803003001249109000c2e000c481da42e07103d02070b4126000007900c039801200c2c52441600052001d4159650890010b0400381c0c043d540d03400040030204102d91030000110a421426865900078101402c80416400680004d00d022014035145000151a1182014100300468007a444070301102004e2050030105141207501e0b8400600694032500c20240060342c0b41c0c00003092145130140d110038440c21031410002c161541d450b80c04007504040c00a680079542048050001107080112100452041d400e51044c08072980020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 635677760 1250 635676510 635676557
    0x3170603160b1330030e03070617090d1b02030c030601170706050702061204060b0a0e100902030c0a3506040614031e0307022701060c0803012c07 64
    0x804909a07070744000904286130600c1c07102002c2401c030f810f500d15040b40c2401c5644444840c2a5a0107002d090702c0411030799403080d022014440000c0b24403c090703c600010680c0c0d003c4a443e11400107280004116039898064450810301d80020b04480c5151170942c000b074101002030388200a4201c1941e00c41100388401c0c40220020111800c00ea4280809a0013284031803050206481c5c440c050940098200501940807002e05040580b0756494551508488080990140c0303914514081c0e0040001d031f2100180200e84c429224002002d04103200e00c801911100083c00e6410301001c84401210742107040c80100035401070380c02c00c20700d0080c20b1200c20300040790a00c0e0815422801e18000100f04ccd0b440c0001d0406020b019008828200780c40ea1072090f0550017081c10095101403680303951030490280324030382c000ca03a00f43d5140030340f50b90340c40f98103446120309044001c1c074440c0c06000410000c2d4040303222540d402075824510307183d00600c032416105140101e4220003c1044e08040c0043c030a90741805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 635679010 1250 635677760 635677769
    0x1030e1020030906060126070314060a030218040c0503030711100527011b0804030203010507080405210d02041e0603110f0c030d151403070303170603160b13 69
    0x1d2032450400d410300645074035009008a0500c0801d44204010603038003004003040d14001505454a07003401d600c004d001d0120200014400c040c2c8001085151500041c41c80850794028808684c1c0e0761400c074800d00d1508000c1c000d403160040f0b181e000540d52403e00050410303a00ca40582610300450404005810301e814030850200081401000040300d400ca0b1418041c0c0f6180c0f00c110a0902c000004964075400c16005c07c4501515a025000308540360010f8000d49100320000d01c10785d982e110044a0030107044801908a038440744600c0426100d0314441911030242c0a8a5441d06030050188400e81c0d21036032100ea412207201745020080141840d41c48090444e510b014442070441144100c2039000d0a002010a14800182c0340e2098004104481c209800e952040c40031801e024004c4403508805d1041c1d01c800c0d2440c5101c8040c40c039000c00d02400756075154a0307480c4100845000044101d00090880383c162283d286465401030b000c4a600c030081440e42c08850b5981007004120611a800c0d910 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 635680260 1250 635679010 635679071
    0x115030509030a050301090f0b060423181f03080a05030906060409080409020a02011e090c0e06090a05090c130606030c0203180603100b21160f0e01030e10 68
    0x1510f034441c1d0b84036007207a044400c0c4540c04910348600c10420380090185200103a802900098002844240c0c60b82143e50051030024040d00301c5070785000d001d00b03640f07030740c40410b0001c41c0440003403400d8142c00402c40f007000c0c528285a80460300c075030310925981d00c0015500085980801000311806c420010164031503000e40f8207010240d55941d03880824003d5014101407141c0105040410702d100354019502d280b64110420301100c040301d00c0c10010151000150389105030204086030041c55414058000c00015060458940e00c10001310000e1001410241d00750007201a25401e03a5034410000d440702042e1100002c2c9146007000c0942214164641d60056400038044040420100d03010986044402c0d61607030340d01e5980003040d04a051560f00411900d400103d010041c08148240c00c4e0070307644280d20103001c184c40b001130000d103805058a00d04001030348a40c5142a251280002d0140110306040110710f0191002d58039040c00a046c801c5003a89030340d016001c408090124102005004a00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 635681510 1250 635680260 635680267
    0xf0403080a0c23060a1109040504081e070c03020d0201050903060a0e0d02160b030601032a09060504032402090d050a291f030c03030e010810060518030114011503050903 74
    0x6403c00d4841c00000d02d4040955540c1000030000300b40a8100c0d215444020010403203442c10b40f5124110380c0007911003030840403140d501d945429000034220352a658103e407141207013070300d15420400c5c8071a190301e080781040f50502035900c25032810800d050190b80e2990300880c4082c00380f071405103000030003414502190f10090890041c0c2078040202c00a5600722107400d5503d0307464400680c0a020044401c001c0c81280100000f45d5000841c41e0107100001d66941c03a00300381d651042280c0602031800042c1085ca5149610002d0740d080720003160702005000405820403600760006020640404410f41d0746030045441041009010300812091a180d41c4010b0100704d80d1303640d201b100980090228225000ca401126954818201d42e04001c50303000e103901107000d40740c3c0741c010070b00c41a8940d018080341561011410b086070710083c00c420307100b860f0b0f2000e040c500b0004e030000c5035541000b00544c265503070b41a480030424461103114082c0c40b94111a2861503800c1c0c10013001c0f12401080050319030002d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 635682760 1250 635681510 635681573
    0x10203030c0f0306040e0a05070303090b041d06030c060c01090c21140a0501020a0f020610060206060d1509080a02190b04150f1d0712080f0f0403080a0c 67
    0x12000d5070500c1c50b01c91003180c2c40c0c1e6942da02040082801640400051148062038010020f0003c0c00c0c00c2500c0c480c0d959000059580c2c11000124060750280520441160700340f590b21140ca03a14042d0711400050464108040881c007254840d80a000c14035070994440101000b84202200c05000400b620f08090b10300d00800b5980103800c061321310300100a001400b9186c5e02a03042040302906607034201e4002c6565000880001d0301100d19103e0180140c05002d0015403002680004802107031000d4000d40750b5580c0e1401040380c00203034040c00702c1d0f611030f031955240c0b1508158454112074510518402d0340d20551608040d00c1e1610804244003810400b16404c0001109419100d4000d0f501800c40100e00103c6002080036040e1600a44240752070240004840c54840030090040300250080e80c201c00d455007400303412600f40e44e2001d0b08100d002c00803800c08814820080648104450001e41002e4880c2c1d11500c080d070000c9042400100c070800014107004224140303ca90f489a41c503610850b0201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 635684010 1250 635682760 635682781
    0xd0921200601030213020c07080f10060e040f030f050c1501030b01170c04050402040f091a0c040e060906060f0301030609021e010c030e010315080f12090a090b0307030f0305030a0b01020303 83
    0x1c003483c45c03901039000f00360310800c1403041003502e014000742070980d4541802e081c14242da5900c01144400418244138001884220f0f50090f207008682100f0440d0545d00740c0d440644103140d0002c1c0490030050104041d6018820034890300542281181020b0142e5165041c01d1503c081d043e007100050000000e86001d10050000d6001019207090b01c0c0440d840d0380c0c4c0c0c000100100300c00c261036020242000c401e0070400c100228008160110052840030b25226019245c100340141c1c01100240c109400211b81030703140c02042c0c00da200c01d0003441246003054910110307001d030b0002e030310071184c0c9a10b85140004601e440400441c81d50550b50100c16810021400206080d007000300140510200407801c1036141d210745c01c040080c40e4980070345407001d50740740d204907551041c07a42c416140b405283c0f2004540c40e40202166801c8034001c1c442c0402c9820301066400401c00b6030a0341d84c1c50701c01d580001000070f046040007604503020780c4489442c1d160a07442d580079a00359200b03050454104208110700b00c000e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 635685260 1250 635684010 635684029
    0x6180e0307060f1503110a080607050409090203030d09140106090219120b1e0102010e0c09280c110c03060402090a090204090b0408091008040201050d09212006010302 73
    0x4114001184031110540040000d1000c4000d2484d000704015004c81840008680b01c00008002e07100d01d0385c1150382d03010031615010196034600005404200402044849822130158140028141c910700000d58244200f100c2d4851b4089071701200441d290a08030780b080c85000001d1107201000d52900d81c0e0400c01c0c4044c081007015840602000c0021400981210b40c400158900064a00d1500c0c01c411805407280d0f8003c114201e0056003041e00805858801040c0e40710004405019441c1c183c442c1908201a00162180090722410324400c0d0721800ca2580902048003840f0748034562448280c1c04442e0401d09a01c007950300035400340b820b1000581754046104d038812020540040d0027a11031000034040c080031040600070868203000d000502c10004007c0c1003a52084448680c1c440c003818059610714421034010303011403018000380103510b15903000004090321890039240e03035071a4114062415407250103414005905170080c46c409900d11000c4ca04ca003281c45000b4039a40d80345038005011042c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 635686510 1250 635685260 635685263
    0x1b0c0311060601122708130b090d020402030903130e010302091e010b09010507020a0f050a050319020402090406030f15050702011e09110d0b091b011d0316080106180e0307 75
    0x1907640d920004450201d501c5c0040300b04078268510703a82542401c00640607048407225000400c070141c0e000618100d034108854003070002400301c510305841c503002c100007500001c1000410380410402c411141185d03001800203031012480d800f400354114010300098a60040800d40c400c0b00c584a2104d003801d48a400718115100790440f03690310070f20100129410300030000c2c000c7d003114041d240030805400c0148088251642911043c036800e6403002056a150020032047c1c0303066100f80c41e410094142500100b503201006440850034581c0d1359039919016003400c0003601c40d070a4054450107001600c0c0a4680c2091340d0780b000340305844071507540c0340d0484140c541c003404050792000c0c6e0310108145040780009008005000f84003082c07043c01c03c04e180c40001c4880012078011a106580c480c214420168130840043c0d5450000c4080000450140190281016814800c00b4012210322110100082c0a00200000452410318003480ea405600700148518400c0f41002c1c11900308480000503140303186d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 635687760 1250 635686510 635686547
    0x10b0a0212210411220b030a030f0503060d02150d1514060c0703080f04030c0933032001030b040506031507031e3c0f1b0c0311060601 59
    0x141c0f518a40130b85100c10303113822960003c0c2c840800051481d81d0070507140804031140001e0001c410040101515504007010040c00714545881d078030400c2d40700701c0c00b440d0300c210003030400c1d0302400064001801240022005003c0c113000000c0d039664489240c00341c14a68007102b1510350b10b040c02e01440801030201500418064040070880c00e0351803008100031001150000c40140d5110340758000c00c03400364820700081e240e9092841000030400d016208850342d0b03034020204d441081d000c80001c1140d4000c000d9501440440301e1201101040014040c880c000070040c100700300201cac4000000d0b0503500d5001400384118038090030004261030106051010385107400e5110716940c2c40790300503002002c0040c81039a0701d01031108550b00080d4183d004407110140b4988850412180c1c80315081014043d040c40c2581842001610030008025004601d50103000803003c90700c014005409080362085445a50010310b03541414014075812941101e004941c00c070191805280c00b900180c44c1005455550004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 635689010 1250 635687760 635687827
    0xb030d031e0209030c130b0102070b07080a05090102011d0313050904020d06110c0a080418021e1b0102030a061a070308040b04173103030207031b0e010b0a0212 70
    0x1660184801c58a6800090aaa030000707031041703080000301241f2200300d01510402c0c4020440e0070038039040d00c90707880c3c0c4606030310f00d403410141c5c0031117094200341051030566485001346007690b50080b85110340010700b90002d40c0c440300c0220ad0310f04003028550080b809103009005000242c0c9410207d1005982c000b00c003c5221816107140704413921071001c00b170751140154001c280801035140c00600440740381800000d044100c1c0340280003248031b1081c17000c141000c4500400d044420180c06807144801e50b100d61404040554215403ea83c001c82d41529007a90f228001d1011013080040c3c54140c5650400080c1020b10740e550191030f000c006807021301060242c00001e000c101034019007030300d00c01c088400319444401510282c1c0300c4121200c200c0c0351514020000400152640a40c801120740544c0100100303032858681c414a18000c51041101c0c140c20100403499035410321480f0700a01107803418a41e1a1440b200007030800c4243c1140b40d0510808215001640d1064124010004080310f0b00010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 635690260 1250 635689010 635689027
    0xa0503060a090212032106041404170c011a03012703050309010209060d09020f120d08180a0c14060a080105041508011806050108060417031f03060b030d031e02 70
    0x41a8022803100d1405220004055170700301884503014960041b902c2000070340c1d4032400200001c1d00c909041c0026140b800d8030010f008600e800107003e050355842944546800019050300782512421344088055560002099810341424490720344040ba0b904102c00d42d4080d01c911400515464040c044e042010110101e9002d10081d81102c620b458000c0c174041e92101d121200c88090f05000c0d000368820500801c0d50714031800d250a01441c040180702c0503002e84482c1500541b000500500700c0c40c400080e2032962011108100140e41d5414040c0c1c0320302d00704501c1c1c010712560b00d0300455200c40c0103400a1080c0b5044640111140e415150100c6010400c0d00d1100028036441d00141d0140c042c42d0b08041560101c84d19007074403403441a000e410240500d03a03c0d880041c0c0c1e207031030030340700108410503039001040d1a001000c05140c0008030003450380e484480c803403d0300e1104540d82d0415611283d131808059070900d820130071171006100c9828180b2205058514520103500c900c3d064030b1019070001407421 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 635691510 1250 635690260 635690269
    0xd0606050a030b0103030e19050d081204030c020901170307061805060a1a060c0d1112040801020a0e1e040c0e060c03030a06050306130222050403020d0e0a0503060a0902 74
    0x4018110140c50700003229a60f04000300491028441580414400c51084c03c1e941070019030170b107120380c00c4200d000d135680c81c020903c450b4424030007050792400000c1c05040d1104141e42c803c540141d00a543d03c1000511600400c0320008042e07000d184590003000300500c3d080404010b8070340060f001040081d202c00d10300030501c40140c3c400801811400341c10100a802c000b95070210110407a108056210701881c5018801c640c40780c40c1440e11180d000710b031041501881546a50700c11074641d4155540b1040802160680d5005900101e03c03a94010504c2e800150f80711007081c00d1110102c4000c60320356600040302e100d4070b10605690340510f40310030024160038052090410280c0015002940e215070b440b0091ba1644c005403860307400385050500000355450000707a041d00035440f4800b000150b80c0e59900b00300510f1106040300e240b150b6801451003404a840c45007500c12801f0f50081c11190000d0036000700b607180c561400302e211b03007040b41c014000c5440c00100154021440300c40050009104d00018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 635692760 1250 635691510 635691521
    0x150507030c150504060b01020304050904110d1401050601020613150f15060512070e18060f060a180608070504090e071e08010c030204053006010909020321090d06 71
    0x50100b001c01c2d00c91502103045548560b02c5140214400c11502c0b100c0c0004a86a20592080c0303503000b82400082404580c039201b2807a401000180842d080c0302c05543e42c0d40f9103603000424403150f0b9542c3c400708419540c0500c03c080d409442c00c81c0740808955240c2e25401a011580159a42e55944002101001440d07600c07a80000240501c00720045940d031000810541c031000342e1091800c9010046045107015500b10060712000400034030000d0f101900040320341d500103103100e80c0724120303119554240d1180802002d9401055540c1e4080303c00c0020501d0b042c8001781d1111b020806101c08021203280d00800791410303545401c50201e04030054107102071410515801c151040310300742107004088031050025004558000009000020100009504074040da01c40e0f507403c85c06000203815403610002c01074405843d002e01c00e5014040c04d0703c4140c9001401d030480c009090340d4180481c04c1d4501085681001c0c41440e0394810700031000194a4418007620726201c0c0140c071036400c2801005000c3c1c110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 635694010 1250 635692760 635692763
    0x3060f0e011a03010f060f1802070b0406051e0601050f0c0703020a0f0f0807030510091e050f0c270c1b010501092901211e0b010504150507030c 63
    0x28000c00b140720104450982c40d400703001e4400e610704041c6a0303860700b190142c90129103c1c00302c0d0212641ca81200d10000e80b04c0440e0340045164200408000140e1405446009074014200040d00d881d100103850b00c4440c2d41440d000301d01c0c1c0390204029031030707a10002302c3e040403400858481d116480700442c1172074500e03c0d070002541300d1040a40410300c0c840c0f5018183c00c94600070207075035605a44480f0280c80b2140360002078080e4100d098a601349045507004000540c1c4102d01659014008088042d060280320304210350745d400801200040c08420000c20310b08100c00c492040304e5100300d55100e01000c120075413040001403c5800a08001e180c0003d40c5c40f82540c01c00b88080f054040500309000300030134042e9294440c40d05101c40a2044040322880301410f4013881002c00c41e040c00d00564030f0104858244a0040d81415a001c645110b4010040300c0c4404405441d030700101c41d074000050b80e1a0003400c0d410044144000c21500d4800003120220480030b0501c9a50349005040032038640850200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 635695260 1250 635694010 635694013
    0x117090d05090a050d05062a040306021b010e0c01020f151321020d0f1b06052208030a060504020309030301090f2307080a0509030a080a02120c0a030f110403060f0e 72
    0x1700b00b07020021030320a04c1111000700c50289205200d80000c0c1d540d01d00282d02c0f010650038001480000c159034002c3c013000840050703840b074070014480e096080d5001c0c2101c410098200441001071075070104140110484000058001c441c4010000000410020145d4a0101038024004c0500410b803180c0c0341caa00c0070310103608400744a800042e50f60804e9599010006840c580b41c0051548290b80d00a03402107641d00100d010852512007202405000d401c0c040201400d0441240304d0307000341701c9000c0c0184542103041c2c40c1d02c4d20300030b0002180c20590000b030045004000f00401ca81000c41120b05580d0407000c0040c005030340142500c000c06601c038820703401d018a541c0054032440080113082c882d0501d43e07504403403950b595040c00103031107054030704203000d50042c091080070394010300d0000c2e8030801c0700800604100101c04540820786040d21015201c0d94005082c1d148281c1c18040c000c0c081160744818807012820100c1580e492240f403102409841d40d8400021807060300c0e4100c10f007090490b80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 635696510 1250 635695260 635695279
    0x1e0108060114040b060405041112100b03061905121b04050915090c04050411040c0c080910140304030302030708070c080409050a1d01021c05150f03070e150117090d05090a05 76
    0x42707a81280e0b42c405c030039003d0b40d03052410015035103c50f051001019508143c10550468440f8000d00c2020131b603545400100040d444000700d525211b030380c079850765415010f00919282072600550120070b00d104401a005500300000c01c2101c100005811414190364001110342e40d8030315070203600306141c0182c00d551050034103041c88184004080e21a4030070900302c40401c16041000c90640b010840d0320300083c0800401e029a20441c540718010340a0341c40386040c001d00060502840c081658002c83e806c4000c660f01006000190350710220040d4042043d06152000d0007c039259164180200c2c03283e000e0a548400000f820450190415081403103014a45045d9044034006540030f5006035649862900d903603081c185064005001e824060794000c0903404858940c01d00f401040b14a660800d03030075110740300b030000700c6000780d000b580d1003540c00c018000c843d41d01600004007500e03025402c5002d2040003405016102802090b00400e0004500380790781d07a10389000118541980603400581e114041e070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 635697760 1250 635696510 635696531
    0x1203020f0307080d05280b01020708060c041403070812130b0a080a051308070602071e0c050910180b0f06120105310c02030702091e0108060114040b06040504 69
    0x8000d04030f130034002d403810322203581c502010850440c0b0b0070450960a0b4000b0f24981d610440d45d90181c1201c18040c41074030303155510b6403106031400f802500c800b25501000902000b03010754810854054141c120064001c130351414481c00c0da41c071440c0c001d000f032154002508480c00d11085891a00511208862648600b44004c0242007600c04036912079000b810035000400c2020410310354030040b81e0140400f400d0002644540d4020b401c03200d8115007285a5171204a0400f42590f1322a0840d40705513214040c40e8241030030f0120302c01d005422400c6d005041d5206110400a0030754038070700c010a030540015000041c1000841c0e026140014541040000400218880c0484051410394a040e6042c1802e09203410b11411040e10a80301a12440030020308818142625000001c5541091040301e050101c0c1c0e400003204002e0030394a8281c443c111540004a0180150a080c014404400035241ca580361801d0b2181030000c100869218554400d50031010360b8a100943e0040c200c0079104010701d0041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 635699010 1250 635697760 635697773
    0x10b09010e1b1303081804020304080c1b0f0405150a08031305120705010516080a11060f0402030c010e0604030c0b090a0b0405130902041b03050a060f0e011203020f0307 74
    0x80d074a4590a9408482d20081080300004071004100310701c00c2005100d10b5a100d00b0a2a00045505c201200c0e5181c0c1081c00d641e40d500103140140c1c050403440e035803010b121202ca8030741450101401c0c036451803078840c800c0c0b07680e81e105c080640107410b540100d07240d991007a1041c840c050b008801d6030300204100020456240000241040921110380302034100e40320020464614100002c280c0395600086041c0125486100500300c0050180f440c0c0c4503c00c078aa42d00d070660f422200c483c1c1c0004d002078045110902c400c000b22071b00420880c1300b401e5107080030740120b034458084c80c1e002d50503c40c01c08041d403090340744d4004680085030802815001e00703880d003100b10700c0f80c0d02c6144000d1040601600100c0c80345010812501200c4004010445040710b542c008005006000400da902c19134440c17a0b0400c0f80f901030a014101806070307500080d03908c0c04541180c110340c800e4021b00440110318000703000c01e56041d211141961a85d880016040e40c15240484c51300710300e26289282800701007112000c210b036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 635700260 1250 635699010 635699039
    0x30109060509030d110405060304120c0f08030402010305071107150e03150402090906010803160222050a150503100b28080d0f0f1202090a030f0c0504020307140c010b0901 75
    0x718143c051045d0b64441050a55900903406003d603c0700041002c04c4c001090000d00352860941810300760000201a11100c090000a0009a42c0d10380c0010820003150390600c1050780c84840c5080000d85007120006241d079503045401b404410b120501460380840d80902600350f240b06004003203416060740c020391250701e4001030301c040740a41003000c081042d101d80402c025040e600700303400960030040a10140c00c502d0944540c142e800032101603020865055860640030072a003d258040b40a0a140e10f28108031082c4100908546410f40414801c3e40c2c0c000c074a04d0000c0f9400a000701e54040704000061503003d0b8454100381942c400c801c40a00780c402000d00408842c061415205443e10590301a180800b294640c1400291045100b060b800c0c0160078600303881444410060808030b103207000c50b040c2141074205840d82d8001074201000c100040350042c1c0503120544040d42541051003018002d800c42c0401144038600101e00407420800035402411340d00c01c0100000d0f4956910301c400980c101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 635701510 1250 635700260 635700277
    0x20031608010e010e0a0b1623091e030d0c17160506090606011b030c08031021020f01120b030109140c01020105010f060c050309030303010f050102061005011d03010906050903 76
    0x1400c2c0140c130a966100405c1c140c440c1c2c3d42218011426a4460071250351015110b00e010040c40401a0040200f5107188052800c580c0002c105598a450a000f000740c502ca400d0550000824035005800c0d540e10041000c10480505080540014500380781c20742d6070810980c00030608403004102c05c92114041079803009258021000c1ea0300da51a01e044058480e10202d03010f5010a2515886c1c0c402d45844006e4142400d01901d001700b01c0d0020f5550341d803661342c41610310645030100d42030b05200642e003407101c800c4034508112440c444e60003982e01084020300c45804003410f10640362002d03000074106410041c41010000c008101030071311440c2c0300040300210f040614071442003803405051540144140c170b042e07500c1101e51a03990b41c80d0580854104085600444843c0000e020382203213a00d00300080d41c060014007030001466801c0100092078654020002031860741c0f800800c2090380d0700203a90740207526500c4448074622400101081c050140c0c204010440b031714090401601c00d00200c00b134006d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 635702760 1250 635701510 635701513
    0x150a0201180305130605090d080307120501060f02070603060e0c0c0a0f030804030306090203090a02040213170706031103010b030c130803120907150e0d03030b1305040c060c20031608010e 82
    0x105d4917048200c505004102000c0d420001d14064200821010300265900044030314106542203600352640c01969400e83c0000301003015810102e0356607070184072000240c0154501041b40f9490002100b04c2414082c0c00000311a100044250740f00c0c00511042c030a640d0000740c7d0014404107480c00800d030700c0f4101c07000d0300002c3c075004000c02d48070414000c0300e008800348002000140e00c26020440254820628100c200780101c40005005007440401d0704d103a4820000b8001082c5445030113410354980c0e0300405045041000140030216822060301c5c1c000740000b41c0340783ca45141c2c0b084002c0b402ca0303039000b0240c9480003140d4500704400408410384603907802803c0e2401a6501c07170507180c84116504103000031842494402c4100e00b8186212407180f406072402040c10001d081c040342d86461801c2c04005000e40b140704201c140402021802c0052242d4501103001c0d40e2603481d04124401c0c800004000100c500d084507200d550100000290501d003000b59607070450b6140e818500074020000841c019 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 635704010 1250 635702760 635702797
    0x80f0301180501051f141306020609151e041b15031d03070f020303040509160f02060c2209060b07050f07141311072906150a0201180305 60
    0x49003000c91002d2005c90703855281e00d0291001680c1a1541c1c0000394605800a000303020082048800d00091710013081c0d1900070b00160b082407900e05003007015441d0038a00e602d0120083c811344501300c0c400700414100341444a2070513142c0c1d00e03002c446000c2c1100114800902681c011691b015010003c09072051507840401030424924845c4405520410009129400502c03204d0080303000c2212a4840701e10003400e0b24a0580c0315000903c030144c00b6109002c49109490b8035014650700540e0081e10400715000805552800c1d44403105a0300c00e05002c84002500e051004048400d00d5000e400900340025040c0001c0380c403140420700a070403c00d029a0140704100e04505080c10125181d02903812020020098030349840921035810b0f001d109040040c3e60b40c8035400032903c3d40e080034000d220700c105100014029842d070078490100c075014440c0c0401c100e4000f442060703a82c072410400039604002205448414107102a801001420094605169612907003030405500000528008060740b001000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 635705260 1250 635704010 635704019
    0x603040c170d140f130f0303141227060c130603060e0105011110090303090209010b0910030f06050a03141203070e060306060405040f09031218020d080f0301180501 72
    0x35141d01500d10318010490040743c40d040140001d000b440682c2d4142052460000e00029285884044c2d038840400d10100000520800d607200c2000100070715462011810042e00c102d4442807002d0207451410407c101510524181541d40188618201840140c607101d103011281420207500c10845881c00c00305000d0b020500d03e00a03c00d80702964039031000c0d100603030700b4980151964007064004280700e00c5010254002d924190040b140014420303034020504802d030780b0603c132600006070440713501114288840c4074951511042000c01e8021890003040100c40b01000c40020440b07500002e402c2404002c01206004032000c115840250810881c3d2540d11b402da0302d9551400251200e2000540400001003949051409141c001c0c0c4010086850542d54900040441d1458540b4000042d290740c085820b068100030400f00210741c5403020b0185040545900c1103003604110000d1051036010001e03024000e0f064141e44c1c4540c1c0301003100d0f03500d5031611402c2d61101000e240800c0140c1c101000401d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 635706510 1250 635705260 635705263
    0x1305161412060613140a0608100603050309010804081b031b0105070903080a03061502010b1302090127080a0b180c010827030a0e0411160f110603040c17 67
    0x41c01c0c0040002410294490104000244802c9444a40d030a920303040860601e00e41c04611030300820003c1400100d85c0d1034005042c2c00d000000c1003a83e03140c0c0ca4000e00f007001c64004012259000e40c01d103020100d6507901e1403c900360b0b00070440b40076940c160a0703840e4242007030004010003032034195030084070000e0b105190701800e81301304480c0c460000f207030761100700000b80c45030002e008615983d08001c00c002e516a041c24821516440a072070044c2c1d1509031894860801001e0f244040c0c0070540158a040b03550400a00a030340040781c0d0510092010500d2a0701d91008032624000d030060b0030130368038469018100b4003401d000c19100401d10042d110702066040d800003d240742000c8040e141c00b06242e0b02c400c48907550400b100e41d803075640c00880c0d26980381041c050009041001c01501c90440000d000c0050208403100c2d40c80c0a20030b840b0401001d1940c1c91a414814495035111664400b00c02e598500003400321040c0c500190810008401d000402260303010000c00c1c0d41d80340e0148145070000042c100d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 635707760 1250 635706510 635706529
    0xa0c110402041203050a261e070206060f01030b09010b040810060e070c0501090512040812070c030206031e040501050f0903031005040e12030901050a060605130e13051614 75
    0x1480202c410590f0800003e008401510005001c2d0800c0140d13004146148605c0030018500031030340c005008100031214000c55800e000002c0014051142c0c1d03c0c1c000d80107566403102504041c400c42020405413050b80c480d801c10706058002810801d92965640340f080d240d90072a00130100745015009124a0281451003004100c0720010000c10180d00c40a41c2a034040320b441c3d9042c1c4440d5240d45c900804507808100ca04101900010390560b502e242a041d1401e2017025000120010400c0150300c02103101d03460040d00307480c2c0480318240d81c0d80300c052115030800c021f8050007a40c040b2140400c0240301c410b60081c0e1140b03110900740c4415644032a843d6869100859001101c4e81c9226001e20903410301d54070401401c02d500f0304a640341605004070480d190003c0390704640d241e44a60400071482c03118096103000704030f2070a2480c140440250040c1c011340d1701d0700036400200350b0303c00026150004510000c0304140c016041e0303101803602c1c0310854502081030242040080e0505000300041c00e005800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 635709010 1250 635707760 635707769
    0x20f04080f060c2a01180b0106020d0806042c03280c15020c0a080414090c0703050f0f0712030c0905060a080406090206220e07050a0305040c03080a0c11040204 70
    0x25525041300c408035450300135800c020000c15200250701c0d504444200348200f04d41c4128049940000003103030325240384001d43c141c10003011500702c1c4a003072b9a02904140c1454001500b19030102d503202c0000c0507110215000180303920a900a18441c41030707180d001c0000e107494403c400b01c4110384100109020402c007004401d9500080141d04011f000c9240582c4981484400840251074440002ca07171510707101440009032401c50000408010845403001c60f00c4030345009a82000703c0b80b40804004165001d0000e003d02840000a120448600c3c0d1030220350752441090000e03070305c880e090306103607101c5130100328080b02203441d00c900b0740b4082e03006070030f0402241c2000702900c3c0b0380201c10204a0303040001410441d80c0d141c803040d030300f401681c80c04064455a21040c0800038a04074000c070083c1000466401450000080c2050040d40c5901c00211943d903801d46c00d020541d52214038091040780c071a6840901381060118043d662654000610346255029034401c012603801c40c02000102c1c4101d11070b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 635710260 1250 635709010 635709031
    0xc030c14061917010617090705010206060616050d0915230f0f030c0903101401120201020a0b0108010209041512110a090903020303010314060f28020f04080f06 70
    0x18440c48100c00c00c540144102040c80d1500c498000d007038800f10f24007802e8100c1008129540c1c510540c1c041522001a0701c6091100209070b0580303440f001030345501c00540004c4c0144000200241d4034000720084500f4075030b0001c200d032410811100000c107648403d00942180402e1031a07a051064401d401c1000c02c01c00007030100a94005e12844640c9603403003031503a140340c40d1003071191050a60300704001e10702c24060358501a0f5912a50340400d030400c2c034114880315078a80350580d06001400a825130b030381542c074020f0f45900c03100c00030700050345410700d001001009580c04100103c0c00c2c00c2c040d0040c107805081550180f022455418044e0b0b020b82041c0600ca52041d6007103040070200d140650344001824028200f03c58468a40c105602a1048075600fa000750f071000004004124011100240d0101c0c0706014059030b041003481800e03110b1000e40103030f25070283c845901d502a01e4298141480d000308560071560344018060718201d9030050b22031000c0c680600105141801e40210301913100714003520 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 635711510 1250 635710260 635710267
    0xf080615030a0b0904060e010e0a1a0c0412140d0507020d2010090612110702040905190b04110d030203040b030702070302040c02210901020304230d0c030c1406 70
    0x1040303424180c00080054010755259036000c0e200d40c441c205500d00850003240f011030042490007055003034615440310f40300c0c1703a0710040400020502d89000005200d0314410200000d4640c501c42440714012504454001108024001e082017250804002545040341c15500041da0345a015601e80c043c20f40041c0d0071140e8034031031701e0001e041c90300e8003400718103254a2403000864040103d040b08405070a0140400c0c0c000c030041c41095003100844a8820740b2450901000304102c480b034803a802103140080c0100e454000200800c14180300c2d0401604d8400c0c0c07141050989410051071041d4291001d8400050403103e440b00c50411200220100d40c15400851610780f0740a05400c459000510510840c020f000c008001a652409078000c0070388681d0007090886066031800700c6002100d032040c1450001088107500ba40d13004401c2d102180d5030000c1c5502075074007005004441c440b0700f03040f050707012848070001d10401900c90b41040660340102d42d030202041d1902c80d02c0410640a40401d544030b8001d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 635712760 1250 635711510 635711539
    0xf06121b040e070312020609100204050d0b06130f02040501110a02090403110f071508060a0806011202061908011a120c0706020c120406391a09010c0f0806 68
    0x64104400b1191460100d5a0f1290340380c645203504100148200010380000003880144c200402000b4007288506c40118074092401d40003032081c00003448020007001048c00050015501c10681c0c400c0b000d28403005014061081804400a520600419020513a41d009410b0707a180001200f103440d0350701416481c0385449a8038299000c0c503895881301c061b407040300e0081d00082010b009a41c002c20310034251100e0309400b030b04041d10022008050314081c00350540704009200000403500c0c115005800c40344940042400885c1170340c8140003c0342207100d40c2000f002079041c0c4c883c00081c1280c005407a443d04e49104030629a84912030719084000000900000c50403c0c91038000910600340701d9480103140c80d0301c40ba4407500345090020b80fa034105d180030404000050704045550030b04901d5080d1100d441e04889000e140070018104a1080c01074011014400c001c501102c1ea0700503031192400004500e000c5a01c0c0303000c0c0c9803e142c000005440d0954110019000311946406000d00401c50301c0034982c0c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 635714010 1250 635712760 635712769
    0xb04030b060d0602070b010e071b35070c2702180d060608160305210f04090209011704050a0f03030f0c080f180a15140f06121b 56
    0x6030034141d000b012580c0b00c0002841510040c1416846920003450640c0340000030242c90400616444c20b1005140000d4042401c0040510107217034000c5006082d030a440c60b40c48880e422100e0003401a0303000e000800b06040b060000b4103180361142140a4032540c4928018410400c407044145240340c8148841a10243d2600602503002c05420240341c3e900308000002c10208140b01d0a68441350740d44000e001d0004140070401c08805104c0c080c0005a10f15078038030b65074040c00c81c03000700d2044140613650b5032140c0800c2124a80c41c0300c40c81d40360b251622002400300030b50140040e140802c881d0000922030b00d05010000344581c0d0840b018080140741d5440d000c0440714400710403030030540c5d04c4208002500980c441c01c4003100981c1c0d62030400c0d180582994055070400b42044191688400d0700314002080003501790b811390b600810b2003092607100c1010b800a004080c2c41030401c100041e00700110f584445884d180f19007412510f1980c44041c00941d240c4400c00c2420051446d0603c450842039400c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 635715260 1250 635714010 635714033
    0x10f0c1404120812040b0a0f051504110705030301150305150d12120c020f060c1e070f050d0332010611070306020a0807020721030c031e120f060b0403 66
    0x269000340c60511904d61907583e0b424200c0b000c0316085100810310101103035038413628550320404d8004010509041e0000c9101c11141c0a0a82c4110786680d4544402208402a903000710b13800030407241c981d6114603400100f20f10165150300041e2500000404000c0203000c460511040036140c40c600684a8584844012000d64030000780b042d040c6105840f107201b0701c961001800e0550107400c0300e07906e143d001420320501405088200f04148800c032210202070303004611000c00f02414a50743e030790900e49800781b55a184405080d80c0030348012000390301c1c1c150b004080c44c600301c5141c1140300410030004203000812180c0300001c48e0700c0f50005020641c051010960744102103011a101c85650350384e1001aa4000a41240021030300014054465010040003010309900c040303000d80c3c49150608003407641c00070500034080009004020003071600031559141ca0002920200350440314001e405000d070840c0d080c00215003843c01d5103841c09800705100b100240c840380c44625141030300c2e54480504840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 635716510 1250 635715260 635715263
    0x1060c06020f090a15020c04020304051e120a0c030908030a0818030c0303010b04050f1210090c170a050706110601031506080d080a0c0305010305033405010f0c140412 73
    0x81241800d2507560040a4008000303200121000505d0084000c0c1442400070029000301d0040c02400001000461041400ca4801f1700c541e03c5000b1403a1200d14209400349036551610700001d0040035141d1000e0313034200a034003a03221403210541d20748859503284101c45d44040029003120100b030413420b1607e09c1a00d40524801200e00340078840d04c030301c0d003198800c1e4040d420449001808100303904190101e001c521600705c418044004200101d03a480f156a00d221441072995040c12100704107160051501900c0b4428094405a85d00c070304841d9202d441d0f4109803480d2144900000e41a440380c02040204050007028180c5a4a940e9841c541010039220105030291110804103003d482042b150294051542e2039900340d003028002078045370951200607040506090040c00860000411210510117080c280d01648201400054540209007a250020011a01c480c400c0c00700c150002c01044145c1c260400c903d10b0084010b03100030840302c2c026610064144010000d1002e0740f031002e00710720f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 635717760 1250 635716510 635716537
    0x15030813060507121d22110c060406090c0e190b030309030a080c150c130608040b0402091305030307030b090f07091502070504091a130b01150207080f0f0d0801060c0602 74
    0x4e400302c2000903526020701c00c01d40c240910388503003152408140e0040c500187c940e9681240b41400d01c0c0c900d00c1d00c3d4070700100080c00b400c1e12038041c2d00401404102d401c004003004c1c2e550801c2824030107070582c07685405000100c071440c2408000800340c6000b1045440d007400040007490400c0299a030b009898001c04021803140c019000021000b1900c140058840c0d0004a40326507100d290403801040e0031410f41081013045164003c0000103900d62907920341154045804504990301c012081022800c3ca0400902c6400040305211016030950030252450b50700320350b00c0000d5503840d10528102c200440d0200006041d0300c00c00c02002600c00403a0341e0403641481580c074296150350124060b03c481f40030890301d2140e5154101d003007820707000a161f000a0411030b20368146030251143c1c161440180501c0c80c00d00358240e940e685180c000c1000000408041041d10318034400d11031501c0d00c1d0340301880300b000140181c070744c0d001c43e003442000c1c40b5058400f40d032146800e08441d82c0303d002c02900007032401c2e9502e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 635719010 1250 635717760 635717807
    0x213c121a062b2d0213061d130c0e030604050304090507020f0a080a090905070c140106050306040c030b13050a0803040f0803040506010807080102210402041503081306050712 76
    0x1141c00502601040342200043d2071090800c50b00604503040701071440d00360091060242110030201c51010401b02c500074502200740d1960103001d40c0d01048010042513100e0039011801010039691b41011507103485984624840880c00000e06031901e100f202c0050050300204800d01ca01d011907440580c000308644126a6840c2000035480e14080913000c0664084002103102e841c2e1031760280211001d842c0f00c620900443c2001c80003d00517000711000100040340c08000790382406425400940100801000c139080380c00c09041c5006000118001954140010300008100404100318104000c2d4088018a50004581c4400403940c10240003110b104c4681807507130010641070400b46004a0044000d0807803540f40c25030a5141c80340d9070f032090040f82d00500400c00d0203203010010416106003c2c00e000c94655440c0700090003001c01400040071560300380b0001c018000b0072405043d800d003040031081c00d041d490300304c02c1d1014040c0c102d00510103800700c54a09d21240c0f02e800c00c5100021001d030050705 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 635720260 1250 635719010 635719087
    0x2090a060b030403020c030d110a020d062403120305010e0a0203130f120305070305010b0f0c030f031312030504111c140a213c121a06 59
    0x4980c0d200f914180c006901092045465184c14031000d03169003094144280c0b0105582d45144d110710401e40007a10445088005600b8440700360445000300e41d2082c40036101d6185003041c690f40c210280000e45804c1200b5a00f00300745402880b48605035140c000d962945980e800d400d04003c1d5100504180d07122140c00d80b40030000740e5030100489583d1180304082c0a00c00348003002000c90710010101c40800d42020010410315200404850310507010706902980c43d000c500e00d103071843c0304803403400c40c41c09000410821040031b580c4104055170301c5507268050010a4140840a5070f109940c00b42034014000001c15140c6403288140301d43e200c00e00c0f02081100c8142d210020350f01c1c5948001c0065400081381d1104101c2c6074800034002c8a17074418105841c14401c4801010500146103140d140002d03d8030034078151081289080314504000303440725070001203642c000c040104002000e540a400d10b206102900004e001d030114040010309494206418640e280f09061100243d503484003e52a00910 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 635721510 1250 635720260 635720279
    0x308011205030f0d05010302040506092a04080a0c030b070203031023040501030c0503240c0c0712050a1509120324080a0512120f060f0904030f080c040305060402090a06 74
    0x1014130010080003a03298914018801601c50040c000b44c4140d0783c00c01041990034003401d070180703d1180c5c40042a460042c031092440c172849a1380188095205d0790001c10100000c0204e104156481043c101d0000d0300e038075409a0783d88c00143c076982140445a00244413042ca000c0e01207040d102031b0114109104d25010210382112800c1e0401d6481c50420380042c01581410001a2104101e1840980f01040030380c4c040740c0120383c05031048180340c1c0009010100071030100004400783c0f01d134208040314031801d441c04664070b114014044501c59070b8000e841300002d03c98424011001e40040340002d11080001080f40240085845a550301700841f0b000c4004c00d80343d1402602420031100140840c059500b485440e290000c2e1080607008000c10035580b610454080c0369402c881c502d40700300c039541c8a585c006120300c035800c88115041030b4003001304024558802d461a0b05140c031074840384c50300e440d0445031824522460001030039641c0064080341c010300b00600c10503030001c084200040c81070340741c80014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 635722760 1250 635721510 635721517
    0x1704021315060306061b080f120705070516050102031204032a170a0507060207030201060909030e09062d040204080a0822050f0907021c03091104090308011205030f 72
    0x70144280703084000d0150030303058407400000c1c040c5400e150649441c114020440307108241001010b0840129401c4d04c0d46d0300d0072090f0b500659525120410034074041d08000c1c06c40e081103100f030f1a5480384007989080d203101d60f01d1150a071541079010350f280c03480c1c4600340041c41002070402c504200c040403500035401c0c14402c2d00d91501c040c03694101c040f143c65040400300e80784c40503001d0110039400c0040d90902600312003200e82d4140d01103805030f01d8071260f00303083c1e004203219404429000c0c10000d5400416520217611070314810200c90f1103138543c0391074080c842d11503c806191031500b030400d2003000c1c4100405548110a100080c0003600d01a25544050b0604030150303801c50b604840425001c4010503c442102c841c0300c1d2500013001030918010028100d148403002d410301071003000000c03452043c802d0029070414032100340400c85001844c0c400030020005400140e54407402c2088132011032900340a8001419050740c2d031609503900b0310003151020307100035104517aa403000704406081542c114014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 635724010 1250 635722760 635722781
    0x31b14070f0812071e020904030309060c080105030c0d020d05030a032c120a02100e060105010e030312073515010f020d050a0c0b0a091b030317040213 66
    0x34241061910100341e8105a1580000c01c65411960030810090940015510380d190440d08140498041d00410340c042002d907080a034008203203201f040107268054000d4080c2c84d1241000308200da000750b008a404800a00503e503140d008540d01c2652032070005580100180000c1c0100001030300c5984070b615590210a119020036107032106203442071501a081400c041e032007040a4840c0101260302c9032130700900321800110490108140004510800c031a4200750a090307410003c0c80c050050300c9503a070708244110781c00500000c22406003403c000c4281c841940362640d041085480c0d840040d68030f04241402140c481040c0201c3c44102c400406010681d00c03082c0c440040700341822000465506008448981030000f0402190724056000800010f005150b16049488036240701048403002591880500f49000784001d100a5001c2c0b45d000450f00703441040d50000c0c2c41c1c4400b01020000c5424400540414034a100100203003800c01d0f0525031091005044d1101c0041d1043c030401102c84a029 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 635725260 1250 635724010 635724013
    0xd1404050604060612030c0f06020c0f1f020a090b0c0307051b01030515012003161a0a110d05060120150708010b041202060c070b12010b0412031b14 65
    0x61106201062140728060115080000c0141c0d00c992030280c80300b020b001f00102150300c0141c03060140a0580e05489817001d40760140c480c5002440ba501d40da0ba00d100c0c00400e040200315020341c194500c540700b201e4410340a41c640308560f030301d400c460110741d4011110015050204210341000241e042c801014503503240e0800c5065100d10400041c00c94200030b001070381c006214800141c03685c0e000021000324240070111080701ca4104940203080d4090f01d60b00d00c628100202c4140704200490241000114224405d4880b90340c0704503480050316100c10700124091001c00c0000c0c07016900c1c3e00200d500000604007011142c40c4020440c040b903d640b800ca500a8001140040701401c100c001107804c504181390620389541000f140d40098492842031460861a55480400b15110351050b101c00c0fa40c41004d83d0101d640c0c440c7c0d240c41c40c3e0310040c1c100d0388000c007400c00450007507114000d442c1aa5561014480424519503003981c08010407104c03c8181d0300c50340799800014441c45460f04601c0700c44070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 635726510 1250 635725260 635725273
    0x15040b180306060105030406200a030906050c0f091c08030423010c08150d020a080c03071e030b15030106030606050f030c0d0813350c03060601050d140405 68
    0x30a4204451109419511a400070310a0107203e0303a000c015240c10607000b00c0005290164010b2500c2c44050002603c910458045006000c294065212880c5030340114810310030355842d295600c80d0343c4104a43d610300f024083c054074400303044c00f00026101d083e210074080c0f820015602c800c0c1c4503420403a000c4036405140039854006e00d032240110405003400c840240004911031300e001c0c000070340050003105000c1a802d50744080b6503903030003120b103100e402034001001d25403110b180e5500c403401005898041d1040d004000b41c6201c9132600d03034980c41110350505a10500f150f49034183c1c00300181007001c00c801011071161460b80d0a106040083d440b441001a03101c1c40c21041c42100780380340c25098441e4111103850740040e01d480040400766a4482c00703459a9001c0303011400301901d090780151407038181d8034601c0f42d8580e00815283d440d40818840031041080380300c203000c2d5510180c02e80b80341c2541101010882d40d5000e04007070702d1803c624200c082164000c10314900320b6220111410384899101c00e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 635727760 1250 635726510 635726527
    0x307090b040f0f060e0f04050603010b061804050f040503180d02040e060a1805030405310e1516031505040e060105180124020a0215280e0103020915040b 67
    0x3c202c1c0038000c010138105000092007540c001030050798082117140c0501e403540300190081d50700303511444086400400d0ba6403a0741800f040c200d01c00c071100000da40a18541004242c4903c81c00180a00c15903000009502c0c02d8000d800750100e82245502c41e6401120300034044005070f455000d40c03210720b00c1c0c901c003c04040c608001542c00380c038205045445504050043c1c8404140b0100440e07040d5101526040300ca40200c4100c030280200b040c08521162031450903000c1003101c5500404407078059401182c00d00107040443c0740005500743d540340750b041180303010f415035940a81c2002c01441c01c43d40043ea40c242e51b6001040c240c90030710750181201c0e040072006004503c0c008003010410b00c510250200d031581041c407004402e49408050350032020082d0320041c480e0f4800c1080f00e0799182c0c041c212004041030010609000c1d08080703e07500d82c0780685401c03100e00350030700360301c40d0603007001e641d2021071b42c003603000040d8000c2d880300c80c1140d00328040c080001c54000c0700e0740c020402000480e803010350b1068134 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 635729010 1250 635727760 635727779
    0x4110c0a03030615020706081b040e24060909070c0c140109090207030903170c0109030e031509210d05070e031204080705010e04140408180114030403050307090b040f 73
    0x5130001c80000200301d01a4280300d80c0010030b001a03a582e400c0c003030200d840c2c0710800034002c000c110300b0300348000c400100031072502c080016160085186c2c1120003a503080c0503e02c21445150706070200c6d040314042c8506006031a244406940200050400000d0010a5100c0044c00318180d0003181d03030b070b448099021866503448191103009101031402107003080407664004060701c0b40762001600c3c9071240d8640000e440700000c1125150740b810340003000040f403146000b40030840710046e000d209020724828603001d4900d00751817a01c961200400780103e10b0301041841c40c060041201051035510500041c065102c4511406000d610542c0718121418142820180740007140070b0200200c000c01d000400110703c0004e0f120041d00d00034201aa50181c1c1c55007c03c00a1055040c149158540a824442880031250040044841c105049100b1482c0c200043d40c46041340040c004116104000150210340301e8809190040300f28508100559641e0301c410000e42c0040c2c10032800c1081842082105101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 635730260 1250 635729010 635729021
    0x501091115030405030d0e030f0406080f01120203070911160c14012c2d01030b0406080a0b060316031202100b0d060c02030d0f0209090601020309100e04110c0a0303 72
    0x800407601032031407a00d9924030b40c60380920a80c01e10380c5503c810000324801000c2c020b0b03800c090903c0f440552200e90b03607040149014010342d18026202c140d800042000e107205060841d00c076801600402c0403a1074501c48000800003c1644030047c030f0140105070010310400c1100300002c1c05000a000d02034100075000b003117084c3c0311003140d050200302c1c1800e00349088410001412962811492210800c622002c60000309a948003400e507440704a1903c5c0d1400314100b00b420381c80d10b0a81e01089244145400e01080700c0c480d000b44407199002c031682000003405800c030a540720348042e0540341561002c170020520a0b0180c3c000b1a400d10840b0f0003c207a00b68104011414812141c1003880780ca04807002180111800410142c03046444042c0384203464000c000311045950248402c1280507807414070100250003070074001c0d20505003800480c8041d84000241c84a201000f0320340840b9034038101c004e8030b4000c00c0e1b41181d80c010740c88134141c42003088608081c004180d000c5006c1d1415003091f14000f401c82d030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 635731510 1250 635730260 635730289
    0xf0c01051503011b0810030c0b030a05011505070f0204020f0705030c010c1d010e01200f0c0f1804110904030c140609031b011b051306050307082205010911 68
    0x213240950800e080c13102100a00f0916940742419142511140034002400c2805c0d00041c00e170141c44140040c1809402e80218890032040c1e40810660f621842102c00c01708041d10140001907090041d031000c01c14150740300310822f02c001d100500d440544a50500581c00200050320070b90004104c050a401081c05541001e00503403505110030203140700d910110401103401141040440c8030300520a901801c070900700e058041d40c2c8440c1c91851850b02d0f0756580c12400b81768420b80910003803541e072810000100140e00c4001004550f110f04022050110080001d0040d0780c03000b18002d000c0002e0f02c81c45525801107004e582c0c1c0c1d0640252a0170040c048603403040b803907015a0700c1182045a5040040181c3c0d80c050b0940a0a460820ba12042d15002d481c94892120749500701803d5104c215803c400100b110004054100c054241d403503000f558540001c40c0c0b00130100d111907000030000740034264484182c14150321300d0b00ca42c641a4945500b11003081508884000216020940e1454003050014010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 635732760 1250 635731510 635731513
    0x30b0708070c15020f09030a050c0f0321090315070201050f150a0504150f15080c0301060e0d021c1109090109030c080309010b060313030801090b061c020f0c01051503 73
    0xc1c64940d507403001c85030743c0e00300c910a410740c00b050314803801c1500d10458208103001012a1642100c03030501640343d090b078412041c42144d111040708020b0078040381448444a02c032070300d068017006036050900e096102501c9281c3c18091120720740c06030a9041e2082c1d004a40942c000105c518006060915941c00038100c0d803001e520350416081965104000720303055840c1940e01042c81c0007800d44034801085690001101d07950869004590108104811040c0d1845540c0e4210b40d910b07081c1740b40d81103210a004903000103070702c5441c6100f1420429a6031800c2c0e48040c221090040c4a64010007a40340300350012a0060700760a000307845454040c580d2038020820600800050342c966501030300f036a400f0540105448030100004004480070b5000208031007019100a68924001d083c81a075101c054400300c0106016600100724400617204e9514140d20243c1540c2c541466002c0309040440311076000400d080d000c1050010a00410000e460300c44882c0d0004951410f200b00d4200800341001d100314080d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 635734010 1250 635732760 635732777
    0xe04081620120613080c030706050a0c0305010f031416240305091011040506072306060d03120608010606020c010305090102090d080a030b0303031003061b051801020c0307030b070807 80
    0x610000c110f858003c0d4054a4031018000c0c54a001c600c2406802804440e50101180ca013041c4411500031a1180c1c0c0c02003420013400325003000030340c1110028043c030326200e10f508106000007180e0a4214015145180469080c10318541c50080205a141c1101e0354105000510350900703490105540c0b502d00071030806101c0ca14240001c1070751402c1c040c1c84965481d4817103804075032a0892008a90240c0000b41c4040e83d00c00060812030840c44400102050196070b0a400c13615881012a00a0081e034004001d001e600d0100d48086840c50220f08018003051b5646800140c0e0100920854000300301c0c5401401040343e51800160884070020310b82845ea074010400b218a80ea00c100f103c981490303014158030f8680d400b9210032001410000c8600f6007500c40013040c404148040c1c109042224490f65007070041408125940491611041070b0b000442d006012031310402069000124401e5018412109070b00c1c03c500c000707807030308d00076074010384481210308184003055a000540341d0f40121242000c425 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 635735260 1250 635734010 635734039
    0x9190e0a06150e0409170702091003030e040218120f010f05090d0f0207090c05031b0a081504270309050a060e0f010c0219080c0103150e04081620 64
    0x804450b41607500204074060306801c2e015504c99100e00450382d04500c0c0a4925060400d5210b01c50b8002c44090344a46c417044c002032048002c01103400e0a51380c0c5580c82c0d004111900042c040650046101d03002c4a00c039044103000700d51248035000060694a00041039808000c00045003101c51183c00010707241d00704020064102000102c04031007a0103850501d002080c0203004a0a04003940c104240d108e06000b007100031150b00102a41c05126040c02c5100914a0340989095610410380c00c000460035aa0015070451f05440001005041c0504045140100020540c20640381c844e42000c1142c1815400b030140f550041e44200070b01400c2e00c0b220b0282e810201c005e422050b12503c070510960003911002c89a03417003445110382d0181c0c0541500540c8680e065840701d2407181e4040c004503441034070fa10b503082c0c0d0710a00880398007040c92140d45c0310b802d082900a10901100a00544540e88100040800c0e120040d13052801d46000f4103c0d16010682e60300480310350300d4000310052107000c2c005c1c480c56 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 635736510 1250 635735260 635735279
    0x20925050a09140d120804020307151b05030f0705030d0c080720010b0904081b01050106141305030a050a03020c06041a03060f0a080c33030a0209190e0a06 68
    0x25214000e441040c2c3ca142e040000b6080c00001e070008143d200c0812450820076000300b103d0340150b00c00c0b0103403140c0c5520342c1c010b00305081001d0340f66000100d02659805007030b41d0401030014150302800070740340743c00e42c02c0320f00b07400c55070062404032566440000c1c00c0052500300d202e00110b0000c03524160b009800c10400080a15800f0000390021805011400c850810254454240d450020b480400c0c80d150604000070103401200408078041803000c20f09009078810322459043e152aa102c0c212032404000301c3c45001d410000e020388500d4054100801c1c00d5504110006c4600e01c2a00244001205071900030b0604100c2c0c4452405414240418031004001c45000001d00c0c8040111a4480c0d5520000544c040c141c07809681d00140d203568003003105500410f0041c00000e040e1751950703501646040b06070b50034104614101000d1b00040c954640d0500d5440107540000b9080340140c14142d9081c0051070304030b001040803410074400701081025448000f0340a40c45a4905d90800c000b0385090300300c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 635737760 1250 635736510 635736527
    0x3040f0f082a03010c050a031d100207030c0501060b070c0806010e0412031506050315010503040507031b0306050a06060809030702090609071404031101020609240c0403020925050a 79
    0x2c641c1010401e441d0454500c00a0b44044045030080017400716018843e4081d0003075005180d030f4000a42030801401c01c081d24010b4828071200c00d00d00038082041103107a040002c0d00240e10480030404c00b00b59060114000f4010440074025400c2007070b9441410385484843c2c00082e6000340515044400100032100c0c281d03440c50740c00758005030780fa12000301d8181c04400a001c0c2043c04019122812008a02d0983c072401075445429011500d40202d0100001540c5a00085030f00070003da100743c2051000606e01c4584401400c00c10450815907522551100c080c1c2e0310407035040c4445540c41c46c2c01c1004591262200f45c110501c45c01031483c0401c580c000c550341e0031000b000035001d0b80320311011407012403084002455001c5010410341d2610740f24580801c050041c641c1860051003550049040400040758141c000c0c5640541c90380340c481c0350701d00300303060301002080754000020600000015031580001644036000b21151a20781c4518003443c1009a42d407030018030100302c400e01000fa0b4481c0c010442 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 635739010 1250 635737760 635737783
    0x1801090f0308210708090d090e010b1e0a030905190308040b0709080a03080a060b040506040e270606031006050d080919120b0c120c0711100203040f0f08 67
    0x126920000e41c841280d03110191001d0301c0c000b1103007508001156512500060086c542c0c90240c030460151128200c0720340d8a24001d0f155502e150710010003410007200c00030180e0000c1804482013407400c1b1070070300d103a94000f8045800840d459600140400000f03112203048941a081c00300b5040d4002c0c2c500808120008000911401815020034101c0740200c41d61002840b50340200d80e800442d51400608444013551a804014180603021501300303d090305890503282c3c098110340c02d00c1c0c6003020907607900c1c401406990300009000306a25458005041d0345112049880003008903041a60505250403400d00e00c0e1406c0c80d2412000740040e5641c0c01440303202c180c20000180e100c28001001800e1400b118001d035500ca14020400903280c2d522400380fa4030700c2c0c040c080c03c0c08e141e5204101c0e0000340c030405001d0000d0000c0200050150786055000c1d280d410f01030302e10428050012400b00741c89550007900c00c0d002d60b20102e002c00010010a901001500d05100311592491400c4601c07580da0165620 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 635740260 1250 635739010 635739023
    0x1507050406030f0608100f06090902030307030c110d0803150307150309110a0807060f0507050706110307020306010b031008120f1e04030605010e07110c22111801090f03 74
    0x9082c1420303800e5401c01000741907050180c41d055030741801d1b1034008196010042d0201820042c000403800c00902c80c9020003038010b40910b1808400e51f03003c40345071a460768110b942c542e4012441b001c0d0b441d41c818110300c640c0f00e208410303036900b06244484c00a0100301c2c1024480d50002005105440783e0b8001c445050381203040c04500040d203032920000d07641c554000b441d04503444220025050300001440b030110f0f4020380341c5901207000c3c41c00840380c40c031032600c0140050340040020040284955a250130103800d41c4240c3c0d00307200c01ca0b40001d0400000780d03c003159559001c0240a09440c0d8403120000078000c5130300801c44140f00e10b03402589400703110045101000041000c07450718034076140b1421403136143d04c1280e5807207859140c59402440203028202d80c0c1d01c442800124501d014046040e0342e4410400181550540703002007081c034641c6c0c42c6011204041d1071036410580071503170140202d020816400191100808802098600c0381030305001d0412100f082c04008030340d12606e201c0280c03500500c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 635741510 1250 635740260 635740271
    0xf02040608061b0f04050607050a170a0516060204051e090105010c0f11060702060c0106060305010e01080303060f010e1801080d052502030102120a09020111060c0d0905010917040602150705040603 86
    0x141840450045ea4000c030b8000e4400200d801c108440800c006180074071070300c46d04040603080c0d12101d005000e048c80420100d0030401a40150802d4441d48001d2240302d07074800340c903051320340c404911445500310460b14030400050140c1d0180c5009034a140c0504003c1c03074407418110158072003050903c04018081c3c810300c1d0300084070f180c81d01c83c0e000711100560090100355440c0004116580200034038440c00380080e241a00100d16240d030328054a048031081030041d821500c44404224061102c0c00b052030520400ba246020940c07203014030b00010300000801c82e04598501040d442c01c03e604e0648150412104000c02d0f4950407084000c8100540b000c0710b500700c1000c8610210340240302d120b6501240c2a948403c01040742c02c4d580110f80428401c2e61414000e8a0220f0556aa140240c4055643c61414010010015040e521142d1480c0c0200d001044031491a11190010103021249003000c280001c1e052021075010001c6824401130b8000c031207160700d03203020020701c0c0e4092405440d04258503207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 635742760 1250 635741510 635741527
    0x2090901051605161202031b06100b030a15090605031e0a0320060c0316031506030b010512070203070515090a0210020115060e030f070f050d0c09090f02040608061b 72
    0xb040d401140030b5000c03248a90081d85c090340607503039400010b00491400c1000311803150445012030b0242c0520b01d04407a10540c03d0401000d10410340005141e8140340f581d0f000081000354200707644000810f0303010800507000b400c000c14982400c51042005a005008040811041d13800050180903541c0600d0040420038044a5024004451190340c0000340300c1c090500180c0301d0104011409607010610b54426141e0208082c0d081c3c5900310b6614181840418040003001d0180d00000c40f50101450024608110b940e81080041d10030381d04040160b0010031540d0800504000f04520728042910114040c03820944107655034032032020080c014001c40303480f861420f000350080d450441e010a0130606032034541c10010010301c2d20315000b5110348541c00722100c00d004040b8040054514030004217864508040500400300b02140040b29001c68416000500f400d4034880e070000b0520640000c00c0340d000c01d0042005440c510b40003141141c11150a115042e80c8c841a200c400183d01007640e516400c60 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 635744010 1250 635742760 635742787
    0xc060405041112160306080f060103060213051c060606080f0c09010e09070f0f140904050606041502210a020c0d021f020f0601091e0209042702090901051605 69
    0x404180d9180e0480150904c001c0b40700da03110b08141040640e904100e13141d0754542d03c0d85e480c03ca04035050403a401c0354005002248c05500240044000d07401e5494515580d0b1000c1059600c0414440c00c5082c0d5140f2481c00300800c90282000801032450a0496410000b00e03c200c212405040d4560a940025801c0c040703074010402c0d01500e58005088003640e2034501405068000b012006800040e50441c1d103400e082e008504084000c0d414442ca10705000840080c04018240a0403403a07000031305000015101d002c200107200803510f2640a89600d2802c810b240346c03048440c3c14600310200041c010340300d95590010311200140710480f8403070415821800419000078840030701c000c82040c0304a220701420303000500701c0c40c502030113000c907405aa81c07a14501c081b00e449030441a00c16160030b1445885007070540203000c070180d0050000408020b40070280c04403005495004801550304031000b415490184a85603024007804000d01052420110b001302001041000070700f40407000c1380740c1101c00c08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 635745260 1250 635744010 635744017
    0x1c020c0411090103050703020f070b04020a080703050d09080109081c0609050115020f010b030c01050a03151203031b1b0c0312021507180303030515040f060501110c0604050411 77
    0x1500401009107514110056580040c10b4240400d09040c00f02d0860307480703842210010f56201c1801814039001e41e0b1a00c121100c003a2080c0e0348030712142c90108040c1e0040c80300c0001903104200030078121030380e050041c20b001b16075400201d069140190020200700c03000c04807545403451440701b1102010404e0032200a002541000010307515020012842903281869910003107890340031641c0303001000041c64241e030800300d21070f034040d042945a8812035020380c0162002b424181004951450f0349810b280384501554005040406030080040515401d0711903501200381401c2d80400b490107001d40600b030091455690303803c245d05415048207020044844401660348180e00c030004500c8018003e6482c0d510030384029132a81d4140115491a0050030341040445400311034070300c00c91030b68074243c0040c580100f05201c01c0d044900c00850755601c80c03180c0203032802c1d500000582c1f01c0c1002c0004010000344075110f065a8801e219030041e540d1070000760b604071401103c001c5000300d46640d41500c00d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 635746510 1250 635745260 635745283
    0x60a030b01110a12180b0703030903021e1f1a0105220b0702040605061806030a1805070e0a2d0204051905150a0c06090c080d090e0a020c1c02 62
    0x10041d501013005001d202800c0010050b40d110241c0200d41c001e2000300000500c14100501000c10540c00064003a400c0f04100d18068015141c0d07803800090b1450002c011402d50303281e2600a102412803140344943c0320302c441d4121903000c12603d295110100849440702d0700d40b0b41800004140710000c4400d074044842410040d0f040e842080380e507043c07030700c030320b034100f000300728440c07401d00074045840c1c2441c01c20784d0145104004201d600081800c1803094070ba00c00b42001401c240c6902152440c0f051031071071920001e21a02c02440c01c1c0d807038001040c002c0c5201402c40400142032084500982d8444504029001a506401c6194540700250500203100f01d0348a031b60452100880600160044840907003110016031b00d864054084464000c61072041e001400c000c02c9452804a010850b5640080c040e5442444040211512200030342d01d4241d409208200092407a2818007500c0c4d5188095900074541030010741c101040c810001d9110509001c28120079410b4004c5034440500c03c01c103544009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 635747760 1250 635746510 635746513
    0x9030206240d0506101d07080c090a0b07020102100506010f050c0304030c170705030114040b04020a0521010b030a051e0c10031a0328140111121005060a030b0111 71
    0x4000e494910b03200c400c126200c14241707860307040019801100782c00741c1c15122001d404035005a82e643e001550700640c00b0b4240300c442501070080198644444c0c0b030103000341008000d032503210061440028a01010040071040b80f41c2084140411a60450b0990400c10828101142c8801200b41c240c1d01d1800f45910260400c80c40c803c00142641c0100c41d0040b045940d074080c0c0d00481e403148189401e0b180c2c502754424510503400c0009011485180d0200d41142c0b00820350060180d403240000d030310800304c4c4903001c0d00d2101a603440100400901c602c00102c82c0941c0034104082941e2601c40e102d000910001e99680b5001611441d54481404640c50661000b05152407014102e0380040051200c40c0c400300140b01c0e40b43c25500c503403500013048a00c007130349041d0f104c03104000d050100d05500042002102c415050004400d041d00c02030180044402079080e66a0b16140e410110380400030b009401401015101d5600740450b0b1606800c441c00900c4509010818107a00c2c00103c8180454985044aa = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 635749010 1250 635747760 635747779
    0xa03020d02030127060608151836060f072c1e0a0b0a030f05010314070f0311040510051c03031a030309040b0607141501090903020624 59
    0x4040030340541010b001025421050f4410442071908441175030195402066440c400948058001039203c10002030262a4450650781c4103c100351508059610a0b00c0d01d2420701500c52900203540742d6500403e0340240c100c5c860b1322705c2c45440c0d22600040c0903008000c644200003250706004203806d501443c0c0d90444001c0b0304038a10320745400d04081d007540e02c0c4907110307110700c20345030700d00c103401d00103040d80018025000d052628107100c00c9540014221400c1c180c4841d960014214240700701402140200560008801020035103418900c881c1c100c20704114180c40c0038000700d20469145140040199030020701503c071845070144a5a0a40c030003540080610f00840400140691944101d4071039201400041d010300c86014801d91240003503034069000b400001d01500d0a90408000101e0240880340b9226003a00d62001ca88204402c209499001c00e000511103003074104054010310340100200414183ca0794025200d01f0003038100c03080c2c0e010a4185071845580b0a40e8401202030040001d003c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 635750260 1250 635749010 635749019
    0xc1b20030c0d021c051608060f070e01080a06092a020a03090e09030405120309010e03060106020d0513050402160b0907030b0c0a02101d070509040819020f011401230f04020a03020d020301 82
    0x91130082e4025a0140d0081c000401c0327031148440886401604a41c0302c1c0305500e580400110303004100140703601255074031a0400a2180c0c518810304c0d424411000c01c1409619495455220031107441c0e03141001c45d8070505440010036800114031041d0f503a048402d14450301c8010034039140d4000e41d0001c1d0390000b4000e28100c100b4070004000c0c400c5030000c0e241c04843c45104000c254440c0b9091141d50096040340301007502441c4070f280186102440c00490b00d0389a0b4030350300031a003284c00c519040241030f50604626820701c250f0019060307015081038014140b0a08581e100f048240c005003101407241804030711403803440d0084c40500c1101c1c0c8081070822030480d8500d2012011642c2400203441c901803400301007001e0501c440700707a1155401c00d403024580301c05040b02c0540407407400380503011401114403c1c0e144800c00e00800c40013981d21034812030254102002420009c020540700507450440e805a8000c1d611000403640300c0314000c503801070b12400c900409802078880c4903040c001c030902c000004507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 635751510 1250 635750260 635750293
    0x60a020c03011506110a1203110409090b09070e010f0311010309300503090a0305030601090e04060f0f09050c010e0105131701050c0a09090c1b20030c0d021c05 70
    0x12205540c0d61740424401080c50b00742c45405101d0b000c0c202408050b03c0e1081c0f18080d4024142c02c18840100516042e55841c0042c12980744800440300203841c441400303100310b420003038070000d004500b0000d040c035454584000f103a0101484000c0c2241c1d402c4014200c50380c000d9114000c21500701d501400785403004400060100519440681c4494082051008951040701924855003440d0000c00c8248000c2c0c0381900c17103400082c603035410040200300106103c42e84400042c01203104080100c0c0140f04010041c00b48c580106041160629080040c00840d60004254641c010282001c052801404004a426101d1181900b1444007000d20000c0d52100484e070040d40001080001c200985034400e00400d075206040c01d0900007080e04209200203241030740082811800c41c10700c0020007004050b401030131910130780306684e142c06014200680000c1030001010225080b4040c2810755211000181440020321001c4d018280c0b401e0203a0b0340002020325480d400e030304002200c44891503078001c00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 635752760 1250 635751510 635751551
    0x250801150f060f090504050901091a0a0f0902010e090702120403030509030d02070317031e0a1a0f030d11190c14010311160f2108180705060a020c0301 66
    0x2980d41e09084500003602500c00d1250300c103401040d075640c0d2000c074540410070001c1c002c06410400d082d542c0d600d9103c0010b1001c4c0c0c02c650300032601040ca00c2d8502c5c019001000301d500c0840050006402c0200101c010303039118220f8a03425004a2b000310440d190800201d25046803140340f07000c4240d001a0110a058000001d000c0703090045080721071818489030100d0710303003800d8400240a069480c1482068020810145501200342c9400c81100034880e0120f00c0391480540b0900d0099588205583d50458039507488025103d044ea480c45400b0304800c04295601001d010f070400300004900b0329690510280082c103056408403079240640b0820342032010740010340d4451b0140100c1c1008107d501940a40645a21406410800d506090400f009500d07000d020103c110b07040590301c20401d0014610380001c4200510707014116a0b100382c0c00c00c0150584602922400081d00ba2014480d802e1074009036100a5401c1a19590b44804400d02c00383c3c54072564640484d495424160032010310900485030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 635754010 1250 635752760 635752769
    0x2070510051024092d0b121e07030e010605031606020706031506030902030c0406081b0f0603060d15060603021801050702011d0d0f0809030607080925080115 69
    0x1443c06218040e1400f02002107100030400704100e1141040310400d00382454a04003414454682030003c08041a56001c00540200e610108040360f59210040c2610071039501c0103030035400200c0c080c020340c0014248440104031004050b00c8250b00049000d007900094005c0c01c000e030848505060b895119585e10b40e56014500040c03241980000f1000d10901400d031a425000c020031a142d401c024084019100c1841c090360144203047c0400e00684481c41104010450700c4060301d203c1c0c18a90005094401e021307005441031040c003400b0041c07030707030b610045a410a00c1245d40070016603031483c14440200c290951a0446c0f403810b0070002c0ea254154004207082e1072010301410a04c3da2070710055400c1e010301074020b4001000310950700381d8a804ca042c00980203c008024002c0c01d14242c2e074008001050a1045501c0b440c003196007520b07403d08010b01d0380c000d51681014800c9107000c3c103483d42e1700c200500401e2010319010041c1c0d0380c14944614ac0c400035081301e0000303100d8015096413034003403140c0714440c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 635755260 1250 635754010 635754029
    0x20108070f09050105071a070c110a0308040e1e150f271005030f01020c06010b0c120702181501020c01030e0304090f0f05070c0323040306020705100510 67
    0x6500c5078031a0201c00201d003050b441e4041080d0401004681907040000d0848010010740120642c03441d03502c401d02e2280a059030360f110342070a0340c40c001688000b0b0180715401501d24400500021301600243c8050f80c1c0c3d0045055081c2d030b0381070700b41c210110105040c40107000d6000c0c14031004041c1c40c641508041802c1e5080080d2504003402c0c01082c2c171151901c50000c51301c211078004004540d0101542114201d0804c1c040303907455000282c05c041c4010b041100f036a42c0010780c011209010701546004100d14420b181c141a10201001e440e110f5511100b40a1580054120119501c0c1d11042c10665034450700c520407403400000c0d842c52070a40d025030394054800c00700394400940c4a030041c12040b2100700055418075203407034252805001484c00c0b05d9038003504e5440745041e90400d40b003080e1064816a03a928001c50701814003400140d04c0071180160b0350700c000c915030070401c00101100e084a6001400603540e5001e81051360074401c1c003107802c46d003040c200b0003880049842d0480c0e80054501200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 635756510 1250 635755260 635755277
    0x11070b070518031207020d050c0604080f1606050909102309090c010203041401120c030516020703113708010b01181502030c0105070c0c060c031d060d020f03040201 72
    0x3040541d44d00c20b145115000803400c104110050500c9825600c0552040003142c1c800d031104000035840da0056007000805900814807088a4041005102c001d0040241454a00d078244213000302244550b040d10307409092075a0105442504c61742000000301403e401c0c54044012881700d20b0b8001e10545036413481025143c01081c01c1c001b02203030092000c14160011844c20f407920011940c605503c00310b980c180400380d041458a241c441c042c025100d0400e941c00550b62402101050415001c0040002150f100c50020300001ea211030800b40202c0302140d03460182030320701050070f80c3d20301000711400c220f0101c0c1e40b000c1c00300514800c03240b05552802009100c5440080011548a1150301c00c0107060f8803042c00c100050511043c071101c500400c0e00c1540c2c40d04908075520360075990300b070390658001080000401e05110421140c5009088946045a90710031141ca0003040d5000080b400110401100404000c6648190484d00c810f49030301400d540ba4104072507200780c40e42080300c0980c082038074135 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 635757760 1250 635756510 635756557
    0x222080118171c0203040308070c050a0803061302070c030b0c18040e160f0305060606033706060305040b0c0c0607080907030c0e09010c0e1311070b0705 67
    0x1030054849250300e08401048000c80c1e0307254607030000c02d000804640148100400d5031080c0004003c0300c080308a01e40056a2801c01c2d290052404000800c038208001f026440940042d20104030f452915800c808015200c0d12040300140704041d5001400600368030005144041105a4214038105c0e8001e502485440d5a20300c1703903400c0e07481280004440b005100c20750407514034195124981c0008003400304e4180101042945160000940204041c1c507403010081040045c2040803591100094a045045003402807a03c41403880c07141802091208001c2d03502850901d44007900320806a009040c45850b40d100350240c0205001e13101526400140000650031540f607400302c40130480440c0041c00241e444c5042101c602c00b001c0c01d80c54841c0103c0da00000071842e9441440040d24100090090710f0810023110381c2101c049400311014402c0c110b040800310354034000f003d040e4420341c1a0200c0c070b610360a100800c041c4211080100303072076001d17000e20a8042c1d01502a08030680141d01054102083c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 635759010 1250 635757760 635757763
    0xa060b0c030702060d14010e04150b0105030103020d0f05030a0512061002070614070f110103140f011809120c150e1009061b0f021509030412080d022208 67
    0x2845081000c56008009200040c10410003d20007051400b074001140e808000142d69050b400f039016091044d0a00c0074841889400c1e520707441c0080c0b8100040241002c40d01c000703845800144000303440b85035041447c07020302c525001c812010035407000650381d03205a1580041c2060f004505c0346071020b100300c03000407024100a03480642c40c240540090899918005048032690551042c034000c100d0284054000079030602d8040e00c1440c420f034641c4540408100005089030203103412042110000b80900140008449031181511070001810100250040d0b06201a14804000070096080c098022664584c031150160b0a24440c100c84d000005c0c01044810550311091602c607541e0700000384400e4041199408000301e18801c0c0c401240a070799015a21554505113590b40303001c5488498000d03001340e41370045141c2d05454403c00382c1d0506140d45081c0d81c0e801540111017441d04c0a035181002d001c8030030260b880520106406642e0760b20400480e039039000004950200d00310f000309020800c03040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 635760260 1250 635759010 635759017
    0xc020f12040308030c0c1903020109020f0405160806030309090405070f240810030506041a18071809050f0c0907170402040f0605060a050310080106062c090f0a060b 72
    0x410000181c15919542055030090b44514590714091041d41ca080b0b0007d81c54010481d40d440c082c0e0000a40e03140940107200b036840e0724040c00c0c0c0c401c83c540010001e41140c11010040c0c424034516106807140d80306004240785208200000e54051164000c100400000007840d400f036404d000705002074035940340c1c50394142c090901c0d245003440111802803600c0360300c105006680907017040c18100c40180d490300c034941000c0c0705840070b85040c3c95400e00e040d000c1503801702c425041800401e102c24020a03403540d158031000d040c018602c0719030b003404520308510001d811840500350010b0640300401c40d52141c41d90f940040160650180c8060070014030614003400450485a41004400c403060f51954200001845003148043c3c5003941e5280c0401c179520b03030384080c0a9510702501c40590b6030800409d100400e158070f82c89030260381e04014040c003103940c0c00150314041e5102c02e01c03140c0c0035407041054440c540d602c04c4809a00940301d0420008035030f50b62194280101c0c20004200b01c1162030320100211840f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 635761510 1250 635760260 635760263
    0x80f030301062106140a2405090f0306070504080d18060c060e01051005120102090f130609110901120e071a1306030c020d1701030b0a09060c020f120403 67
    0x1081403004201c00780c05440d00b480780e420300c14111090b030000d0808100840701c2542103265250a4100045011b0403c2110350700a042c5c001c1c02c4802003103249955481e820001200d070030402c2004104081151120b5454071090200141522a90f1130550700080070340e0001e215080040c4507054400005e10b00440302c43d014104c0d021a1001c03410300f001000c1e40d4181d0201030031644075139074107403002544d0f030300307100e018043d403030031040d2015540c07a1a042210503808490441703d9648100f2008409940f001014061000c064900c201441030780c08240b0001c25040e800b00100703900b00075a82d0b411040c0782d00140440760090700d400a003010180218406ca07070111a14100c0303a40f03d003a0500450182a190313201010b06001000d19040e405450b0320f69884640c3d01c04000b09450300340031080e0300c0d0180000c05a846a503d001003e2601025960701561410721000c0c00c00700c000300100e01d4020050b00203207409034204605120707414101000039581da400d2a0181c0560150401081e400240320003194100c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 635762760 1250 635761510 635761513
    0x2042a0905091308070b0709060e010228050a0c08030a091d010605090328030f080c09010c06020d240501020a020906060a0c0c1e0b030603100b03071206090507080f 72
    0x50b6076440d8401660072043c40c1c256421398042c418000020b184250b418440c5030740303070307a407641031403900310042c000c1c1c0388001002c0d0640d001441d204000a540115900c0e4440c22000000e40c2d6001030b09200d8205080008050400c02c0700050109030110004000c190745062a65820760302584c60301852003a441001900704680108401000f2903882403019002021008065030001122a0204d8050b200d180340c0012019017801800400d06800c018881c64101d0141454641c0d4070b4200d000c3c000758800c07010914140815580c4c06014000c90354180d17140343c03001078030401130b00d0480d80403421406010607107849607415104d404146035101040b030846030340d40981342c1c180644803e82002100e82244404c0800c00041031030b54400b02d98100300703407001000602c03101c031a04207038280985004d00f4a0780103d80c0c0d904041042c001c50741c40000300155501000180000e6801c107080c00241410b15a600c01d0782003003a01c5200303c0c180082da90000030080c1c03040301203c504a40d1804000c6c6c07200f003145c4428a55 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 635764010 1250 635762760 635762779
    0x3020c13020a120908090d050a14152208030903091306050a0902031801060b0c060109051302010503041a070f03140103031e0e0306040f021002120d0c05040302042a0905 74
    0x1414042d13000391156a105401180c1000b0200313000c0f81032a0118076054440d9071000c182c05090141200d001c5600100c190060070003a101c4800d90086001c01600090740c03051414001400914450203410750720b0b03031050000c0d40d82d04111405070f0742c0703405c4204040d11650710700410000c004028810300048820181c00034200d5840c1280c10002034000078181c49003007030760103880382d05807200384150400b410740e401c100e0361144010541145058016005010014541001d00c0662040c034040011529030900c0d10598a9840c4d01e030100318003255401034a10098070380700b8014820740100300805011450781d400c00031b1840c40f554800700801c003848090042000401c0c1c40420010418102e00803c00e2400c3c41403081202c14007007171510303204440503110711360f03119604000c510f40b101a640340c84c001440280108001001d4503401c03071040343d00d00e07038a40d0356841003010460300031001ea03401150020010009002401c0d650503002c0b08030b00f0f2400003480901c848480d6280120645000c0d80d0015000000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 635765260 1250 635764010 635764037
    0x303010b0a0c061b120e19021207030f0c090504020108060d0602160b01060f0e0f0402130803040306051b0910270803030f06030a0309031b0b220501050c0604060b12060403020c13020a 80
    0x80d10031f00103400e0f600540022503009011600b0046d6000030b43c0f0482c003010b81001d040c20314610602c21034020b050064140000d010250780c3c480203840c3c12100460f140b041d28010b9203400c1d4000c1c41420204645802c1c0581c04d0800e02000409550488955841d041c01d4030507110710844112030981001130340400501e095007018205503025140c04001018071500040d00c2c5c001803407840c1c000360b004a450545a03001c014180c0b595480d404164860340502074182596013000801d803011001c155401c004c00480d00c0d903809001600d43d0150650700080d00d420190300e58205548951040b0340030320400d0f070702c0c03c0401c0c25805e00062507481c0a03059920038001c6819076841c5502ca8401061b06841030240300350116031214194002c00000c0c0e086c1410812480c1d40c20040c420418490740031906002c424420399108900c0404d186901c41d922120014100390901c0024030301c1d903000c2e0490141031103558100010036400150244c07820360202d40d03408035100407000130001d0f40325a110510014002504181 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 635766510 1250 635765260 635765293
    0x1150306240f111c050705030c0109020109140919060b160c05090408030c03071403150103060504110412050a1a0109050906040c1412032205040207050303010b0a0c061b120e 76
    0x4d051042c6458401c1c41d2102d9921800d203950004861107038540d540300c42610456802c80081001000085403445100101e5000242500300c0180311554514a0380c000c840d040c14241d000c08040c2c14110080c0f0344a40303080325841a14280d0b000704444132416024080b0312032404904141c841c540c0024803e1540c1d980d9203405c4c2c26500041c0c40c0c00244101c806450b920313034101e580070303601ca5031034401424419014407000406846156010138047c038035000b1400325061354281164255185038503038005001962802074504000788901802d94910300b420302000d803841041076070481c0c01c0b0300c40500140c1c481100c000d4035090b09070740060010340d07101c108000c184e104185504d11144024a0400002410386010b803c5074008003800c000103111944c8680520074403d10000034000c103940450501800350303101c590320700c03060058850701c101c041468011103201c1e00400c92080e9000409100070701c41d03039824440341800420114042060420f20010450007441a0120301603410000c1c0041c42d041c20065 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 635767760 1250 635766510 635766553
    0x10807080a020607140601031505100b03070507020a0302130506031e06060f180a0606110708031b07090e06010504061203390b0108061305030301150306240f11 70
    0xb219000c000314500d085c00c0c03038140100303802035000d030340d40344119100000c030760041300c500414403070046000500c1803203800010702c207a83d4030400701d0403c1543c43c0302500002d11080d1059000a60200c01002c14a13002e550307036002240503138020703411107030041c0016040e661400310f030000ba000581e12000001c1c001d40703000c5400d0ba46030400078250551110541c05442c40300901120a05200758441c8802c004080d4408841007a80211001800a10f8107104103240c5900c41d40e1100e16101030b03000240f070003617401440070100400000074104500498416400e0b1291024458244910310707080c0d00141001c2032024408a0342d86c55965260900b0441c80e14002207148801c12080070810384401c106426a0183c0e8100c1c1c05006482c4840b45616150300d551900000519094001344444480b03c001140081624151071001036480b40c12282120220001c1c4200d034085c480c041c0f581d0100810300c0d0308400c0e00e030000d00302c203588580344041c1010003034462690b0a00e03800311a03030002e00d44010008050a05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 635769010 1250 635767760 635767763
    0x10b01021207170405060a030b0102160e1b0c03040f0e0105150d05070504051c0507120f120302130905040c06080615071103030c0d0810150f140c010b09010807080a020607 75
    0xf503a0500e51a400820404d0700318041190100350f4692490020303680410140900340111201503d4090601c00c4840d07080001500c400404038018030312111211030201943c1d0404900d404aa44442c1d03604d000b9a0008650700c500594441c07840004507090406545d00d42e009a1485049840d00b00c400002c080241001400030303007004003e20000c80d46030b68200400b171844403064910700c0c40c40c44500300b503410f0881d264400c000d8140200407800016044a0113844402d80160480201060b0a10160701a200d00c0185c000c032000f500c80c4c082000c13405948441c1c043c500800300c68400507140c1809489200082e03032282ea101c0d800d201080c090401090051807240c2c0b0599108240106880100703103560000401d820f46a0030810b14000500c0d80104c0003903103c031014081c5a4982d1a089504d04001004c59084040040c203c110480050144450200d58010b00110aa841c12a589000c0c024810b0300c40303051241c1000340000998480c009450016250900c0243ca1841c0e055801c00185130b110450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 635770260 1250 635769010 635769053
    0x606050a110106090f02071a041e0611040f3f0314070809031c12051302031f06050411041203090905070203070312021204030e0103020c0f01060503010b01021207 71
    0x40030a21001c2c5001c5d000715040d070782e6000b68542110749003910841c805c82110216400011080001041c1c00395681c43c084620034034054414a10fa08101c00070303080d600141e0f0884000080d000994101d80b500c20003c444101c5807907425000c3c42c0a106c114032640800c400d04402160210707494a07611041c00c1402d240c421704115400c1100002c003141c0582024109071a20500403c11000605040c444c103244290700446003c8600c00d6200d010342038110b814020700f0940e44c1c640024080110450400080079001400c40b10860740054040004240c0c2d01c0300610100e09000c00020a0b09040c041e48080d02c007102041800d00f4109064110034581540c03040c0c00b040040d2200048080040c0f00e45030042c03001d68042d5a89a81c00d0402401156142482d070442601c10404482143c6040401e55041641490514050010100101c0190144580040c8503004658100c0c03d00e00c015404074084440c103030300920900712410010381c0c980202059800e40c02104121150018580ba03000d010f04019156 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 635771510 1250 635770260 635770271
    0x61e03030f27060306050a06080a0b06091804021009030506010b03100f0b030f06011d01120e010f0b090906090d030504030507120521061003020c010608060709090f0606050a1101 78
    0x3140d40b24003504856032080b40c01c2d00034014070206a0601690000c2c1200b601c0c03445001c1d140c81d100412414006201c8819241d46404a02099855804880601c100185000ea45d5058050700c8040002c065174100c0c410280c1d2521555043e014100e2007080b030f0340140107440683c0c07912081e003205500040c120705078800d00900c041408004050110007800e0034801154480c40d00c08044080b1040141849040c0200410041618021a40c50001b00c070000c0c40c0c441c00e058411440c05002d0101c0311001c03006542404804026a40302e5484400101811580c6492549585441540320042500c0004144e00501c42c12800e49001e41c03c400d82091017444e00a00e00a000c0d1110b4080a1040742c0500001d0070005501c0c01007000307000701c10400d0f410300e56182e501e4104640029044048604000d06154010034182c0500a0a5001384010040710b002e4410500d0305031002049191680034952203140b502c15a456280543d01c81d4200350b4040f074440602e000300490f0255001d6805c8000031503103640702c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 635772760 1250 635771510 635771537
    0x1d0d02100f110f19030204051c2d021503070504030b180a060b03100b030325020406030303021b07050f151908010504111c0509160308030a061e03030f 66
    0xb1402031620001044101ea210f100302c0740d542404441d1001d48030101801440f0a001942d01d0100d58900c00b8030312000140500400d2918503c00d80c2c00c3c5c807008440704040d00301490702c070b44040141d08602d8422076069082d0a03440004c3c4107980010b499000c0060000e000510003d00100c641ca030b0000510046804641242c03001e0500d00701c1d1403030085907500d4440c200c413103a9040030400180c003580c862a06001c0c00c949100440da403801144040001041c1314030102400f070700710b102401c0781070750080d02c1840f410b6241e09000d0041d5102410041e4014104c18485024017004220401502c0008100395400e444090401100075014030305c180c003154040258200f141c41900c0a928991060b07103c001d141e40c5010100b204891100108951004041098074107081c1003210b45c0764144484070b000076150301d41c01c4000e840c11465101c14400501c940e0302c04001c0c040c48401440c440c5110b140300b03108194440d00b80705140540c00000e0317100e1501c1d45c8400c2c40000d00824040c1480787c0700e841d040146600780e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 635774010 1250 635772760 635772791
    0x50d020a080f070509131a07090b041e05010801080601090f231006050c060112050307020a080a11150702010e13060b0417030c060c0a0504090f1d0d02100f 68
    0x54802d5540660040c401045582040c0008030b030305c0342c00e202100b11507550907101c00741b0522a1004001c190400400002d00f1240180b41540c06401d200d4a407a031640c2e100e05c04003115544150b4950400b03500b916002030303d50b1040301403c0c16600400040c0034503910b45007031309018001840c4c4101002c0d440e04d6280c9007400118030001e00b2204080d0480a4600709100041e8500d0759580002d0304003c4108040060302c01e0000c2c40e6411102000d82100c898030340c9041c500e09500030071000039408000e40d000092046070028403003a455000b61a00440c5c05074607010440c4030340c1048003000e1010f9041c0440005503025900c1c0247c081405441c0030400e03900e00f0600c034201c42c04d40d0031003500d0303001c0450240308089202038044082c0c40c2c01e500951412188091180c1e40c1c08000301341c0c8100c884e000540c1000944108142e600403d01078030240b00c045071110004020702018001c40580c080c5c844841060304800207072901e51118140c02500700c40d007054401e48040d001b8604040c08551700d070700c96009001c18 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 635775260 1250 635774010 635774023
    0xc210303110706111b011b2001090302071a070f0201081e010914150117100b120403260105130216060c090807050f01030f0b0d05010b0301060b1201050d020a08 70
    0x5082c080a41c5d034490302070000b40c0490400c0e56411441e031400f14912540003540003100d8140c00303241403401e0480ea21030707803860300d030407041c02119803e50130441ca400400d600050003009441c0c4c846c800d030000c40c40c40e09140c091405282d4001d490151518810000b650090140c3c076080b62200c0e8000030814054a1406e924007000e03030103c108190b90b1392040c040c0c05202c0d2130182c1c03c1100342070154408607210000901d0304400307846207010421b0302004512075a2080328030000801d441c540031a01c030100c881440d0801e05045030190046481041034104650141400c421041220000008540d0030b0809005041000c2f82c002c0d42c409600f0490468030300141a04c2107804c902c51a0003160540460381c00508c101504e03030000c002544a89014012a520020f200003041000e20380040c000c01c0c050380650240c07442c400c0ca00e4002075540e000030240032041d0081800c1c00300540090020507a00c1009a8040c85201c1a90203030354002c800502580c80d0900502581c640000e010503a07030f80e107a20b0034a08181 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 635776510 1250 635775260 635775281
    0x7140103230a2003072a0f0c0501020f250503120721090311010c1202060601261902130f0302040c051911010608030a030204030c210303110706 63
    0x802038410031800310388501820040e020705103c0302100d4411590044110f001c080d0102040c4202801c8111315990328030f51a0700c20640000741228454075a09202c2c00c034080180b001e86007502070f07800c04034055000007078030a0b8000c10540282090424400c000008a400c40050349200034500f00009076aa42003000020107480c18200c01d903229078614240c045e9401d05400c001604601c2d407189a0043d41190002e811290040742a110f11085100102c640c0201054020810f01c03401402810f0943e00040c0c40d88190020f0301c0351001d00e103028a801000e0404101c0d0310b4220004040065074014140c1c0c0319603e081405000541403c804654030b10b51040701d5002425040c2c00c00004205520341800b54140020950400601d40a01824448000d142000d404410300803c1140c444c3d0007242544100000c14805007981d4807400300d110b004004c0d6110740310a9502c074010364804590041c071a40d003080c0074103140c00214652021954160044d00030b800d403404c04402c0500044001c035000340903011100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 635777760 1250 635776510 635776571
    0xa0305030f0601031b05071a040303050a0e0f190c0e180c041116140304090c0e031c08070e0301050709060f0f1202130b22120507140103 60
    0x2071600c044504810705000701010b0405090104142ea40040c11401081144052909598542c01400c2c501d0070121340407910038020304000200801e240c0d242d813000307000300c1002e1000e01403444d00440e030607607420bc2a84400c981d904041a00003841240b0148041c1c198070515800080340d035100c050a465200c11109402c80c0d51607840480b401e4041884500c046034800c440030008004060f203610b01601490301e034031540e41c940c650180309010091004c02184164001142d58035502c0e20004c00281c10312069001c04107030207107e04401ca290204200d1203441e284858404031140422045460312409070440091029410340040207850a00449100700d150742c0721100d80710b1420b0300041168410480a20070400102195110140d1040f10200c00c170341c22450268a520700080500030f0141c80b644100c00d80f1000040c65642009140d140c1d0f6104032f03804000c880441d0f510380b540301d4030801141000340160480c840078000341d03005d9030320041d28941c103240028050300e20100e5081c94516000307040094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 635779010 1250 635777760 635777767
    0x110304080c0a0e0103030914190306060513050426210106140a020706050c150a051f060c2d03020106090b04060311121204140102100b030309040b0f030a0305 69
    0xb420810b007000001d140e0b03001c00c030081e585103440c001e214000500541c20008445911041c1d2541d1310400214210441001180905e0741c3e840d0080c01030a4030300c611405010300000085d60b0b07000d14441e0138400c0d83c200026442001a000c00484d0801d05e00c0c41c0340442e12002d0111b19414115801c00f5030040381000500350055045c0f05000e0603268900c0c625a0120004201101c4101c0d0701041160446402e03040090703c0d594503803001401c003a400701125603600c041d4410418490701580043d40111340030f140b180c803a94000d00c0d402c125000175015030004601080c510348005241105c0c410501d1170040c0440c02c00680d040e4003542003451802050f40140e45541d401d00c50400c031441200c03a006011241004100c0c59903880201100900350700f503100e85035000c031188080701706014521035410858182d0b40d03034035283c003200391034550281b180f07600503c90307004000e02c40d6202d446802c504880042c001c1d81016191010440a444940745641d00600300d1702034032007180c400300441c400b401d10a4541584 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 635780260 1250 635779010 635779033
    0x3101205010501180c0c1b08010f0f06051507030c0203190b040b01080609210405060c030403050c0301050f011203020a02030f0a031e0807110304030c060305010801140405120a11030408 81
    0x10009000992441001d18011745c03941180e4004440c0c928681e130000d9039107801c0c1d00c1d030040c400c01c04089070310171041c84d42031406410f020b80040c1d010051079000705a041003402c1e15202070107202091500c071068100c00422003031002c030703010300900e0901510003421200f0590030b20000c8900c41403004402c41382d04600d502030004220b060803542d40507120304e100400503450000381039a03807072501030303500035901041401802d030492024040710003a05002d042507030b4840452240c960f40364000c1c0b00503a4117000741d000400c41460107000c0d0b0740c00b0790550388440c00d6513400c008907a5820807551004805610035441c2102c0140c50501048503986680f01c007400c42c2070a91305000e00201c44508000c00c0c01d4840e030040c000225001b0340400c0e005080c87c540f4080319076445030b0300d9145102d10b40024150101101000a00c2c0c0d5054011238140c40b0f045000340030101d1240c2e610000c3c20307410b590041254206460381c102845101c3c0140003407042d0ba00e1310000b01544081540e06607440358002c1e0030b06810460b003562 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 635781510 1250 635780260 635780279
    0xa0c0e060f1c0504031b0b15010210090b091002030702030702120c130e150606031618030803040317070c0b06150d020309011b02030d0c0908010e150901020406120203101205010501 79
    0x42c0f4100f0b41e4600b440311b043c402d40d6220102e07403000309848001e458800c0f161500b0b03442003181290144030358008000456450500101520044a11400c1c0d1311400525590141c40c42c001d690007421550015400d0240030b908000c420a00424020701030721890003001015610001c03100c1c540303400840300041c1c00c418800c030385060800c02c02114202c101110709005168840c9000c6079030024034501e41d24040c4014500032120b000c001e104440b8900e0301043d0200038004850000d5006600c603854038400558000591001c0318001c035441c2c0081080c0007011008107003660109607000d80014120400c1c04a0042070004640014001c401120b03400b00c10410380040034450300360080c00c0c3c612507001e00502408001d54a125002c034950085403a810303030030b84080c0203031804009010460001e2007140c103030552183d038580c0b0000d95141c20b26803090214a030b070f5030b06200301c8040d02c58581d90702500d101c854215902070b6101620040100004460014410300400c1d49042250303c20030003c156540340c0031450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 635782760 1250 635781510 635781527
    0x5010f050105011e0c060e010e1002180a0509070804050c040c020a0215040b0d0e1c050702030105010e0c0409021b0109030c0506060108010e04060b0d0c0f0e0a0c0e060f1c050403 78
    0xd10042c40c20b14503804d002c42e08000341404c080e61000c00440c0d140c20b030402c00341c050a09103100716143c1c801c00301d4103940b84109070080e1684076401c0005960303280281c0200041a1064070440f500104010049240c140c13003120503c0c2c1c01800f460440300300e44d019502140455800305141d00040e0400400c600440c642140c3c0034401c103211101c1241010b013005103149091103001607600303005685410041000f6010301204010b907104007038110740e6203a013840151503a0f0004200324481e510744800401c5940395040241c1c01441d15001080c282403c040d010700096006e0b020f403803100d03500c001070305a21000901443c01510b2103503a4211200d100c514015107800800f0f40b1480c1801400c2c4014003250710200141d9520030b412903008500c400000c00800c40b60102c00308041c02035803072880302040655030041217004842031101d07000101e588281c11107048030b0542242d94002100d49442e04614075000001e000383c501580c10140c40e240203000d942a01c640a4150f8506403521032041000707054210385039 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 635784010 1250 635782760 635782787
    0x50c12100515100c171222030e19051c1b0315050403050706050c0a23090d0c0b040315051f0608100308030a05041106160b1305010f05010501 62
    0x240015408000407090f80a40e1409410041c51071030b450180403110925015200584480543c1c84445130360000c103c6000301c4a020b03c402880380480113841c00722001c410080c1d00741d912445c41d992a4002c00c9170040c101001f070220088501d0700803e05550b404d100040781d0912041d0010449031a150452560442420242202c01540c0c1d007040800c01654240303e200700c0007400050140c1d40c524082e5141e000c0c04e170000c1d11407880c1400304030586440c54010f00300c1002540350155111010b0034225421441030f000000c80710024041805603003810342c00c0200d6244a40a49040d01e600c600c81001740d50025441620100041030728044524080d101d2581c00c0401403000c41f44d0307002144c04400f50600c3e1b40c4070344801c004042000809003d0072022110107194080811540d0f070404141c084090302055406641802c00305040796000e207440011a10040d40705840c0c20151115034582c0e5102d2070005050002c1c6150721102003001410030701ca8220552000c142c00105c55040000042c49141443c85 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 635785260 1250 635784010 635784031
    0x71d181015020c010f030f0213080c1009031e0b0907091a0d110f1203091509030d050304050c090702010c080f0106050f090f0d03052104020616050c121005 68
    0xe00c01d580400c44540702c00c020b0801d208550a8a00708900500c02c54292008251012075810312800c0c92914030380855050004580720019207108005c02c65158440c2d00012628a45003040083c110b10070f035103e0480c4004040c5640d682781d80b070b40c50380c1001c00c994543c0c0c241c00103201800007449030700c1105441d401c104050500f0003100d00101d010008203031805008000d900c00352414035551501364440b22440500050b5060150403450b55580d0818640c1a118410000d603500b4071014000c00d4400400e1b00400620580d4039044040d95180e10191050361903000700701e000e09403910f03403224141c040d207d07590000421104442004200c40000b51000051400d02001040308a52080c2507a030b4003814030341a240c1d81c0d400403000a0030882001000c50b04440800c40d8401030580000103060f00000c40300d0101c0f1180380107172840c1d0804100729402540403005002494452078006460802103100e8800c41d4202c1882c02c0000e0380b28503000b0040d820591242540018004c0c0303a02406400401600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 635786510 1250 635785260 635785289
    0x90a18050c07020607021c0503040b130806060102070510090e1003020108060111060a0e030c0a08040e0c0a0c12050d141801020403050a02010c02060d150302010e06070308071d1810 79
    0x500040e410b204070300010344540601080f45100010550003048055030000c1188d540302e80c0c452f01c4a07100d40280c401054036031460040041d68403008941148030b403105a02a003200c505081c01c2000941c04800640108151080b010070440e040542050013041844ca111280918500c0010f011040041600d81046031a20080d81041d100041c21600b140d0311400120b0003400740b08807103185025250250446100b194005002c0c800000020300c2030f00c03250551600e05550300c1d10303030611038400c620320040010340741c50000700400d034200c10018145c0c005103000c0349058822000c01d02601c142960f0001201d500009004c85c1400844110b0142c0c0042ca000f507003030a1030354441503191602a000a8103025408450504651780d030780807240d00140d4604204a51200f0342000c0d00c181016000c201d010881c0c000c0b410405251a10540d602c40354545e07240451640c885d80100c41c0309191422107694082c0c0c0c02e8083d00150749442e4140d41c085003250a170541b62a00d050460000003c90388142019207548 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 635787760 1250 635786510 635786513
    0x62101060305330105040c02010b03060f040317010b1e0409140106120b0625120801150503151002011b02250b391f0203070c0f0503090a18050c07 64
    0x40d4007811105c003150300241140400209a0141c2412a0a030760b15000d1103017000707036840c1e601281c0c40c003d50083e600e010180d46030103500c2003054400c0c00358469191061054032514000040d00400c3c07501840e40315420a540c4407091001d442884a42440702918a030042c440285d004902803a111500c1c0000e001d92054140414128410043d465503441c00301c12a041482c0389090f40d06220952290203403501102d40000200304907428025004003038260340812111610440a0701e015500d002c00032401d03012018100600d001682007800190354130398501c070380c41d40b480c04620441c0c0b04194020b803240400c102004070305003003081000540301c0389400303081c0b10b07046444d0b068440841e0031a0440150600a50019125004134580c00401120900000f00c5410010880508100414421310700c0b00c0f07081c0c8074000684c00b04132280d000003030340404c000d008507900702c2100d0f94107405201500e140c181e10074007040c9655a0340e0400c0c0309600c99000010030703040c41449225400042c1038400350828825 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 635789010 1250 635787760 635787853
    0x103060f0b01140703050f04030b04050d1b0308060405090a080409021c110f1303120e030c10270801021801120504030c0f061e0e07050103060509062101060305 70
    0x4074031005e0308004000c50341c041c0d60020001140c2c01b658014045038020f10f010315000c0c0c0e03608581210080018006440401100c0e0781151010b04c039076068494076540d58550007030100030900140540900c1c8250303440341022562a1000f040034041c043e102690f00d92100b42c0d0844940c2d28940c070803500da490b001c68004004415411340f05084042003c00b41e4403019031a11b800070707800c42d800140403080e1804040c54500e07044400041e464006800391403025003002c04000341d070610440820080f850201d0034000c0baa02c114895002c91840b0003c4002d841c0d00d850300203003241c01420940c003040c24500441c154640e041074000355802c60211040c48546040d03503005040c6401000010420303110070f100401000255088403000b1020355010014031440c3d800d201e000780003001410b0380d031401488800b10f0306500c02e02601c4142c0d4030107082e501e00c6440710818065000b80a103066540c042c004101490076010a001e141d004601070001070012044061548072500c8005003412116800c42079480449480c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 635790260 1250 635789010 635789017
    0xb15030706050405093402071401050909010521190c0503030f1c0b030f010b0f0a05030705100c2306360f0307030c05010506030d05031303090e0103060f0b0114 70
    0x2002402c00c011a00c0301c0e00112242d540c101b1841000510083d000202d1030350000320320048030b00003940700708030050074401566648207610345c8540020074040107020900f002180e001800300424820207034140e504100034100a9040002c0009406030740c4140c041c000d0302d01c001380c0940000c8018510700714514095500c1c51146100401e5040003c2e503107a8014000e90303200808544000d41511280598404014020660003c1d6180b10703989000441c003550400100c1d000a446000c1c004001150034001000655407280320f400e01000304544a04d40015004850341200043c5401448440341140d0525810010000c2207050003072401003201c000030307a680140c1c1011080a01e03000c4500f9900014035810001e1940b444051071100045010030990b00002d1004418010b80081080e80c8500041548800b4095148000a482440403400302c462000d6032859880c0320382032070442c0c0359a6200080a2840980c03054918a680d4014401d4414803405080c5090b5001d1915010360440306151048a00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 635791366 1106 635790260 635790271
    0xe03030601110f0c090a06090608060106030506040221060109090e100f090c030318081c0f0e0901180605030f0d090602070e0f130b1503070605040509 66
    0x302d000c60710310b4000ea04100a0460b00101c1c0c420091124406070000a200342d44071000036052003280b24034401014074a02404040d0b1400d0000380c11501c00604050040c0e004104000303c140d2041d240c000c10300d03010a409503450f00c2c0c0000480740c0c56425040554241d00c1c20740c19160311440010300300c1400100c0b40060110306880300c000c0c01a201e00f100000d104600407038040c000070f4010002e110542c60b24815a2072007a43c0da0044618280b00c0290341090405648641b103101a4030400a001ba00c695007410f0700b84140c010082030915405100b402c0c4c800c0103400c8548a40d60b803540101005010040031944020b100720b02c0d054960b043c64901c040070407910b172000901c0f2030010454a040ba17448080700d82e800da81c0c050039221202d800400008511600442c0603000507410244180201c0400000c10807012100041c1441c180700c5800003414040c00b03202c20007059894200c0706502c003 = true := by decide +kernel

theorem cover : BRFrame.Cov 635611510 635791366 := by
  have h0 := BRFrame.cov_init 635611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 635611510 ≤ n) (h2 : n < 635791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
