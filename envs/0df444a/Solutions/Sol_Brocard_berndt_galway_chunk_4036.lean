-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:34.455469+00:00
-- url     : https://prove2.me/submissions/7acf90f1-34be-4c42-b12e-bdf5a3940b88

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 725719424 ≤ n < 725899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 725720674 1250 725719424 725719429
    0x3020a030f050a09060e0d0b010e01060930020a090f0f060501050901020a200d210e030a0b0921031905010b0d0902040216050c01110607020d20010203191109 69
    0x240d1045c2c4a050516444c0c8482c1c24002c1074400c10f001202409020500d80009112410400018160f07a92135a52501c415110110880e040300200218034103074050000f110720703290000082008280c0b00602d100800b5a4a040000070340f04120000100d00d030f034828030044042c0aa128250003400f00b824418104004480041d454803440c50020704404013940b2014144201c60096a500c00c1c402000801072104908103481c201c103000d4120400d20385a002d0035588035000b182d01001c4094000d0080542c0341450745c07100031150016140300e4451180100c100360080394000003003410f1580c540074035103c0c5841038220852254410b190710065103071000601c0600085021241c1000c0000c1020a060b049840407178006c3c0b0400a4070219003e0321614142000800304e214450074030300341c0c2c403100b4088000c1c802944865050702e110016034005030105642d1802046056100108005030460700e4000001e16401ea038001c5810a00a0602011510070384440348240c3c10907080c0e80748500c0c01c0c60b490001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 725721924 1250 725720674 725720687
    0x101d0a060e0603101802060f04060905041a0d03031103071112130e0702240103060f06050f0d0305040302040e0f1203010e01050f06070c0306022a0a030809150403020a030f050a 77
    0x454100c801c0e10786084029108200000300d4141ba80a404039589103000124910a41c01500402000940200f00002c0914190140d80031150b0645400700240d4944000c000314802041021010b0685070390404035601800d0015600c0343c001c64450011560724400824200301c2202d060501615007804110402c29545030300409480e4160100c011680303c070001640b41412400c8070046040c4200b01d443c0c490a160b90303110303040740c1c8100c038140700e56450102d101040c0c1398540034041c0c020081042e0009145040b4102080150090815a141c140c403500400c040e52410350141500394085001e2701020042001010360610405007a1130a40d41407840400718402c040c0310303582c03084513040d0005441d070780c0310710880d1543c0754043c98259000780c2c0c0f840c1080181d00140d40700004982e80c0300c036503001420002d0314501d1400d0110040c006981407583c3c2a41c06104c01b81c1125501c1c071441c1030910038516070b14041402a8041e400401c420302941c50001c291001140c800810080188841059644c0121 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 725723174 1250 725721924 725721943
    0x90d020705030312060d030c0f3e0418020604080604020f1801060c02040f05070f030606020c0a1a0c10090605100b09040504060b0a06050405030c06030f010e101d0a060e0603 76
    0xc415039002401407c1c00c0f1020717413842d04080d1980d103940d408401000101c2003020040040242d41c218550080780200601240030b4411030110f01d0142c00400d41d601d0554840c00001004e002e0040000c2c483d43c022682c660815004940142c1c072410a02c000e52405922002012008032500c0003034000611008410318010310581c4280010001a9811542ca540000b0046640400c003082285400f1000400c81e20b92052982c002c86c0c40c100b00840d6891012885035819a00034040089441c5480ca55a10201a5145005410800784550710070031070107005144215020700310104401005003400022034030f020308100560044858100598a850300598004100031900003c444d079641c01c000019040c14070b0f50540c00351071104040348641d002800b52091303440607004c55040e02c6042e400c0c000b59100c2510150369000000004004c1441c020030304640c0480800b6074a00700c42d40c0c40e603d05200114800c0318203904640d01e000c2113042900341c4601c0c0000d0442e0050003a2600380000843e442d0183e41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 725724424 1250 725723174 725723179
    0x803060312030105151602100e1329061e04031103060106140901020a020307180f0b0d080c0c0301060311040f14070f180902070506150604050603060103090b090d02070503031206 78
    0x1b10b13084001ca180718016400c1940c000d171500304404000c140040c8514041c5400a101d03005000012641d6a4944140312a041084800c0781c1c0c503403010f07c4c11420000611340ca0941c001401c0101d9600264182840e92074800f42241c01030301d4a003145002040c403280d06940c6d90291784a80d004110141d48042500c00c070300705d40d0b401d6a81e1001d0910040b0b0400300c801d2406501880360200010ba82c207440c4190068182840008003c2e1143c1c0080e80d10a80350340420103503210786040180c002041000c0c1c010009051a02c6c01c0b90142030415010034207507005076205940c01d41c10f05070000b1407070a150103011800b281c2801c08201d16110b20701400e14500d00600380f5003c2200c2015410340f114001c401000708607044203400400180d4030710b040710296000b40d0084606005a10100718042280d120829018900818203410141004103111140d0001002c181c109038035000c1c40000b00d828680a54098201600900001005180b0182c50300c0b5a6034002c9000c0c0d4001c210f0705801c540c10510098000c10304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 725725674 1250 725724424 725724427
    0x21207050f0c06040b09100b030d05030903070501050a0506040c051903150503060f041e0c050607031b1214041805040201030b181509010e04030e0a0f03080306031203010515 76
    0x6181030401940503000045440f0f1040e0003d00040c00035500d0b41a200785403032401c96444141c4405010242e60003101119055031101004822180c026400f55a000ea40003084900740300319915400d09444041d250041515540c0b001e010003818180070796003061045050580c43c0c19900305e400039000c1d03144c0c80780000f05a038411071680401040a10b44005210080440b40c040c00c0100c018071180d802618200c0b031000c0003c1d984007030108845142c1c005c06d500f1403080103100e481e14050055940c0004421410441c0081c1042d18007842180040446801080c0c610030307007840d0701d01c0907004481c100303064840442c0c2440204180c0109803d00990a004181c003c5101d80701d07440168040d0502903016544080c00403060100b10500d004041d00ca504080b0402c826501d41c00280028144203000381410200b8020010300401d00994105502560103044098095942c840e50b0b4420310258104460306080001440200d2908101980e4110f082001c49842c6514090004030048986955589003420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 725726924 1250 725725674 725725687
    0xb12060f01090803040803090a0504050105060a031a10170f0112060f020d090f061a010e0d050c0a0b0a11010204050f10030f02130501030e0a261303030f1202120705 72
    0x42500c982c0014032a0310100c036141c4da102c201503130b1641c00c8010040d000d1240c002e0b0006d181e2410303006040c12104054109460700e16080340440180c4654003a4840e03440b060404500e80d0b40f945000003803030200ca5901c01e940c01c070b101501041d50040207000480d6184160700103000c040035000c190504d480e0712020010b450003101c00b00a0103070040743d07400300c1c1035442c1404400501502c0000303a981d44d4814001008030f8403041c88921445004c0090160000b0102c00c2010110700f0310081070300b0500d01a6003103c4048641d40009031b07044200d5044a805584042240c81001c0d411182101032004024029810a4100b0003c10558600818141c0c0301c2e50701c0141d40c1c014140a548458414844001d09541d61040301e91005200081c41c03041500192400100c0c00140310040344003002c1c554012290403035842c144011154690600600c0044001d0070044c9041c03900252550380001c41c400e840e10040040f1990001d400e1118008640004600402603500031590f01c9510550210081c00c0c42c513210507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 725728174 1250 725726924 725726927
    0x3170603010c2007260d0f02071418090f010b040b1323100501090501020a0309050927010f11070c060516081308060106030204080c0616020d14070b12060f01 69
    0x203060344170034800035240a4418000b12480f10003414510104100e60010140c900119240d0340c000c00600c00503005200103000d0410340c601410b22100008003003803c941e01652014040c4582a281501e03c0d03484584040c640f40c0c428000ca540901c4210b13000c00154207200301007a46d0941c0e5105020809546180c140d0140c040540f04000000e01401c0700340980c0f820203c040e030182000c1c040c0740e001c612080400500341d80300080701c04003580d060fa01c101e4404d2501d070612910800141c2484012a4a02c07581600c40601a80d00b506c03e0b21440300100e642c45000072a8000c03100204038509042208000900224030700803404000c845c1d65181407a5503110062040e01903001160008101c0100090030728626022180030300282da03034000a84402c0d0f6030f90881035040b032040b0301c600c1c0d240c0c0d00b00e4001d41c16940341010290045400340300000c60025110317400078009041c0d01200311014600c41d4504000984100602030191201c60205890440050036000c2c103039400401151242c06589140f070b03080d9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 725729424 1250 725728174 725728183
    0x40b09030f1c02011b020d0e01030612061401050102030c0331060c030e01260604140915161b02010c0b090322050603011802130303170603010c20 64
    0x401d0240940d044009154031804010110400c5440158207001e4505e043c103401001e14110008290000e1064800d8102c094401c904041c0401d03050681d0781c00d00007800c880e11a8076803a101d11548000610740802c0c2c07005296043e040e017045046503c14000360410300c0c000801c46407440046500400078038801d16120960704600c4013100c0c1d200301070690000340c01e600b01440011040c0320b51141182c00d10070300b004440072005030a420a403000c81c6540e05100d1040303040c1140d04414080c1c00403902800620980000350800d81d0700385c031390341d0045249c1052841d45407240c41d009801807c442101070780102004004002d04091318903001402d0b20803004580c01101400c00b0603604c0a40383c1d400b490120101912500480017503800c140d000c92a04605085055044090320401030805003581d003003011401079248508089050244e080080800140c0711080c0040154826541c00b524106029080d400c5484081c1c6814000c0c0e042450b20300034036800000c0c444c95400380c03001d45072944045100d01440d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 725730674 1250 725729424 725729443
    0x50904080c010f290102060730091212050f1602011415120c060a03020901050408070806010f1d06040f02120a062607060c0f06020a020c0f040b06040b0903 68
    0x9a03141050703c50b1602c00c0329001290283d5202014451404c460006a03140c0b03034111002800901d500e81c200b03170b41c044151145100384050640c0070f050020f01014020803183c484006485002c410241a11040d034031068150010300030590900107030506480b8142100c0340a049141c44070a80901510160b100358400008011400000c40542c1459010414901c241c1422107018500708030385000000000688804561800340c001071070071504c110210000e40000c40014104041080000b5142400304600000f0344140c1c2c016019a5140c407410100c0750100ba03001540345070600e0820041d0301d4451100603849401a04e001c030361a45202540c2c4000c1c45801c030843c0620a4020512403800400e60251040d0b50b44201d0011444500380c000039119295040d131f42c54507500106040c04400d21031030220085034828818070720480d0881d52100c00f6a0012102d940044c0c0c0040f0815410745443e6600030b00c0701005807400c00c404100c44020850034495801040155007000419000c42d403001c01041e0308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 725731924 1250 725730674 725730701
    0x411060c0d030f0e2a12060705030901050a0504120e22020d050c0c0703240e01020a020c0f0a050402070816210801210c08060108012004050904080c01 66
    0x55600c01d4207800740042181e02100040ba0745451101d0500100003c1e05404c03c0f50401c812841061446408002d42c41950f140e460300100d400e0040400c0c984100681c900403822501c0d456224541140d0b0642110b00040003e42041d0510043c440441c0c11009206500c0c3c0c1249805003a03030340880082040c40744d6280881000c4010104802d605042581c007a16442103a19010b11a40c1c5402e460041d080c0904a100e020542003440d0130400665521200700440c8001c0101da51701d12424546441101c104ea40350750940d0750000762003243c0c04d0707041c0400c550300030040b074000340640001d002145000e00103024081c01598005400c5042c0708551003503c140c00400b625080c0c00203c2860103600d08005200c500c6915840d40c240004120f0103107038202d050705c681c030020704081e15841102403040400c0f801c0a03a83c980441c0c40111381f0f03240602c071040c040c0c0450f03400440d00c10344102c1e2039514003030001c50125031088140418851581e5069040746c001e90046a040d49500e2140c0384e19004007030142d2103d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 725733174 1250 725731924 725731933
    0x3010509180f0d090f1d10050d0f0219061e1b0606230303030408071b0f060905091b0901050c0a0317090a020a033e0405010812030411060c 61
    0x80aa038030010b0f00c00300c6246a0342d40c01843c01c0c1e071942d035085441e01c41e01600c40000c040560500d950907030340358404c0c1d011841c0f6288010703590b61040803619540741c000c1c0035144030710740079030100a50818400011042208405c24400c403890034a006001301c0e081c1c201142a41c0c52000e5440d081d0381316042d610340030740010b8100400c10707815140100003880e1500c0b0717043d141c805110700f0680079604482c107102c06e007801070055860345e906d039030381c1019590000004884e030100421b9262050801c1310100342c081c0000410018030f090400c00c0c09000030b405903018034414844201007000d59203200401080c0854400311007130311100240010f9620f4055400e20040d01e1140c0c400c0d84040c1070340601540085030120f9100903840c0c440807041a211b12036010080d400400504080000401c541050301d124126124074908001c13042081300c5404c0c03e800c9056a505420b02e90401c050f180521070240103000342ea0040100004035030803a215800000c00251030128074055902d907a403100401c945041d0002d0040c0e5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 725734424 1250 725733174 725733193
    0x1206090304170604080403030507030306030b040b0a0506060906120709081002030601030b040c0f120b0402070506040203011d0604030509060f032503050903040302060d02070b01062001110301050918 87
    0x255a01d800a2080350a040c01c01500c41c20004408a000c3d400780f904440c0d202d2802d0b065441c107445aa11612003101050f0740c07410000045590740c06041c0c0950300c202803a4106d4105013503808203a42c0050301aa1007440c0c10009030300d00f5910700017190503070098080314142075a54400d06844407a003c0d401041d15001c5c0c100365882446541d40214841d1001741c908202923813440040c44101c0e1420711024020542c1e43d0340301d41d10180542400d55014004140c0801c1540311040800d0998009982c1104c03141c2c84103041c0011486d00380a0600b1580341c4404200404803941402a1380380800341001e820300a0002d0b941da07042e01d600085501e01c166100d21f040d0340707003484102d20a08000c5510303010180700900840603e001e00c00e00030180900310ba14011424036081d0340070011107500ca07800c40ca0081d0303420000c07034000800da03401460083c4110f4603402c0d0b40030884800003203408184454110039900d4000f100107030020840c10b49054420648245500f6598481c5d0102030320b162407800d5150703100e2030706074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 725735674 1250 725734424 725734441
    0x7050708120a0503040320071d010e1b07050a02190e070f0f140409060e0f090705010f050307021005010b0a0f02010506090a02090a030c0303031505010f020c09061206 73
    0x1581110110000c03100207905018a201141c0249049803000800400114020034401d405440200748030b400e21005c1c1c113404489031440e00055078010500c5408000982001c048030341c004c4e5004080004022009140290810403d080c400f00c1604041c60042210300c2031290810403034460780d60181c01c45401700605907040f0050511481110040170300400056500c1d0700c07074030242d01d00c07039103071340350107040c40c0100200f41c0d8856880e40700e000c4401d60900c000165101c0300d000e104000d00035101003c196081c51071a410074400700134074541032540852000c01c0383c0e0742e001c014508000c40902c0c180b526916039a0080b4289146d14918944540c00e00001246084100d4010b0079507000a4607603251001c00f81074168240d60044a219038001080800075a000016070010f04005900030300114140e612595200a00da0407070300250b0010340d5403802503100412080034040681801d0074000000121000d00940c3d41200c0c5425a01560542020580c0c03030b2224106070301ca192002d8156003c070f2802da0b00303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 725736924 1250 725735674 725735683
    0x2062101081b010f021c0c0510060f0b0c0a080304020109121a061815040e0d08090709090213110d0207060912030903022a040f0207020102121602040902030309060705 73
    0x700c04941005590303280782d5540c09001d81016580302c50f000380c45921103a500c000c82c0030712980740d404140140da84c217501c0059018803030b00b110005840c5000070b0280c1072121031908464160484074002408000e0316048050001e40e01c104130ba4032040440e41d81e6039510040724112050382c00814540c440f400c410040204441501040c030324010200405030740c501c020052102200c49041c0c2129071030501040a0b1000d0303034180321074900068004140f00c4800902903181c40408070075180001d82e104d041c080105000e0003004002c1955440a2103050000d80014034000301c04410408040c5d0b503440c90742e501ca4a403006481e84184807100440d190842420640090081c4010840e0300c80c22100042c15800e002c0e100384c603003240e0194018900c8881490348120b003803807040c05544076038400203d078508591311030041401c12440700c103016841d09818400a483c24001d00d03040f00c500d18041c00714040c08506a0840207070140c041f113000c80c0c0b007100c50003c01d041d442180802504a4000180074007807090019 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 725738174 1250 725736924 725736943
    0x18092a1902011e110f180910060908060103200a090c020c0405010806071407030306030210051b0f25050301181202010203040f06050414060f01090c0810030206210108 73
    0x42000c0c20310903d03000981c080740c000c603640c000c108030103005540314600f401c400752010120380100c45810015a00018003500e4049074458041b10849a0912159a0140f00c2d0001407545400a1a155040d5603a60014005003d210405080c070038284802561354003800390000d000d4a581000200bc0004009448101c0c048545004600702000042c228100050584c42010265a00c0c0c40200310300100b1010380e400303508203a0416480d05000310159458982c00300b06448141c440d03540d210380c41ca1010540084900162900c1d400c43c0400e4600940c000c5034500103180352400190030b10104606030031094025411a542640c600340035160307041e070312841d03031204940101c04030007400700c4182d0101e0a074482224000d0080c00405000b00003c1e51681100c0c0d0454401c480003615140c588259910b000411564144003050f8040104640615480342c01d10640a038076051103c1e18140d10340003040130051000a00501c0001101c20499107140614450b00400000410031560f45103156685c401c561fa = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 725739424 1250 725738174 725738201
    0x9020d1104081c0c050102030c0a111501060807090f09020315100e04090812041a060319020d170a0c060c030b010c0b0c0c011118092a190201 62
    0x6a4294210000003501d08440a00e4001c000307048155034408407006080c0c544009021900c8840c00020340207002451044840d50702440d160001c0c41001030240c401c110303610b4000d03000251007101c120242000701b41991040c1c2410b01c0c2c41e031903e0030211805a150b80c040c1303581c020300b00c0f40458214401d0b0019400741c4800b1040c0c4288040e10f10410020440d0720706c101d004114540c2c00780e0300314241500f140b0341c01c0340541d9016007085010f43c4003151640c001c0390120340c4034500f20303521702c086094440500e8000300180c004051407800d00d03010210607101c1c420040d22424203d03010000300041ca2907052480242404c0c4152144240311010b00b8150310344d5000c54425003406401c0840c14420300c80e00840000503980e464045c482c0d5101d149070f20310003a108402d41c19040002c841c54590034010f80c05000607000240f40d071144c4070414054284c0104616500c290382078010320074100b44c0042440f1242c4400703000400c4100040309a001c4074482c400005998003003910400e0407040d019803041d280c00705070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 725740674 1250 725739424 725739431
    0xc0d0f2a021f022104030c12060f0509101d010c0809010501081c050c010f1a030f0102090d3003050a050610050f0906090901030c1502060c07030804080d0609020d 71
    0x110420b0702070003071142024200503800440c0c07905840002c1c8402040c030100c5050040e103004d80720340303520600360700300e07000031450b101005000303020024a4030a9143c10600000d0402c03941c00c1c2090780685503d105d602e000b02c85500e840b5001c04031002004040c440b1001070b4002c00c00184d10131800741c0304080842d8038500e1075181c00000a00d80d1804100c144c084000c130a00458818881101640c040d013240b445036400e5903072820144c40e01429841800080004190462130720303d002d00800d4034082c6910840d402c1a401841007416540342d50b440e10020603030001e081045441751119000c001105407ca40000c10108404d1500c0301b900755000d03d002c4c1e640c5078018005551104244080000320015800000b07008202420001400c0c002601c8105001403105161110300400560302d10020703002958000280d03e41004181e0301748200788007525041c00507003524a000222424240100007024050199100026041282c810216841412414802c10045032600c1500c0002e401221802911030b00c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 725741924 1250 725740674 725740699
    0x40b0a05150d21050d1107050303010b03040f050102030c03180616050309010e030c0c0906010f090504020703090801050a0608120403350a0e04060504020c0d0f2a02 72
    0x240c050184203a1064101c0d80d007010022003071202550034940255100044452110355506000082e03410b04900d60382ca5503200c000c05600d81007140d03d408000c0000350070400c981d42c000307003000c402d883c11500d50100203902c0741d85508140c8403201c0b0451000b40694400401c0069444d10b48010b5400780741c4440035140b50a1529984913510303d4182c6010421040424011103143e2140c80210f6001400500224945103083c403590b1560704a2007002c14150040c45c60318841c0d04100140560044003482c04220000c400e040c0585642014040c2a002c2c80e0001028400d041c0140a01001080607400800440c6001d400e108010145800741d81494015980e440f40c4003e4854207440645c0d80100341030740c24404000f03800c100310034015003c181500c03405c5d559409111303486014102074450354481c250340c4580c1c5000c0004441c07075500040c0c465403040c44100c180307440005078424a0401403c145250040e410001e98811004a803103a41c40b52900c0040b0030705402c141888140b1a2080e1071000e003110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 725743174 1250 725741924 725741941
    0x6091515071104020c031e0d1d060916031202120f03190605100c1106072607030c02091306110a080f0402091f050910050907030e03091012060608040b 66
    0xc42c0c0d800b4171a0961040c00350241072040c03800200c1c0803d1145500c04d02e4005e80180510903074410310340c42040361220741c04061340c554043c00060f0380041e40314080c0005484003080c0741c4808516000c0031b00310407100c0300b40e4920a4000c02030b654604002801007501d03202803c0b02da521960042300c0581d144009500041021802d6008900541e41300808a1020030b5943c041200c0d98469960706545503112a40348007415243e580083c101c0c0390181900c0170320303400c80e03000902c00b90b0b448191002d0b0140081103001c0c040780c4c0c4444040141c40d811a544006501d07041c0c49042c0c1e400c2c020074050103a500e400c0c840c299424800008080c29452b586030000d090b99034842d5100508002c5401079002031040d03000440340019003001180407608081c11001e9503440d1070100e00720030000c032825011911b2a06050000780f80070f03044554030842510302803201d020700c80600341c1c9038054421500d00032140e5840d41c10704140101007002502c40164410442943d43d504001e00b1300c0c0042e10162040000c00000c2007000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 725744424 1250 725743174 725743177
    0x190201020c091b070804120614070e1f030b030607030c232a15010303080c03040c090c030209030a1b0506120103111c03080f0109090b0609151507110402 67
    0x185203220040240700244483c2d43c000398407414044a00e06010000071410a001c4109042c031107014081c0046e0901800c1c15901540c1009080c0b013041c40303d41c00c101080341c2c1d0350a100410b540c1120356039444242c3d02417000d40c043e00276a2101c40e810b0180d8005c00c038807250f1607444401b145002c4c7c3d0350003c101805000041100454256000700343c0d03400c01c801d8904e600300c407040e01c9075110500e08403206c03000800001402c0000320144a40c48280700c50041051640c001001508902c64840c3d403482c600380ba640d580214030070351045048650300c480300e8010b41806981920b0004c0400741c01c0e1081205240703030504950002a0540f9070780c0d13289000c08100350078a001030f100200c200164040341642141c492204038400001c036943e0004210342c1300031121410201003044944652102d5009003011000400c1d0b401058112a080b50728290998001c5030810f14155007185c3d0035584140d250b02c801c04004440d268500e5010341250080d00405188003921004000f41030191110b070728400c491a0801059 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 725745674 1250 725744424 725744431
    0x603070b040e160c0803010b04080717100b03010605030a1a070e010c170d020403050f060108030f0711030703020d0b07030b01090b0405100c050f01060801141006050d060305190201020c09 82
    0x410b045800901c50808403003285a03400d0362400c209240282d5566202000c0c5c0c401d821007100c03131501040030041d561040000b41c01401e14001c12070b0940c900040400e40e160759541624003840d03140c0304120326a0300c003903021a019000160a4402100c1c840c18100c40d079014030500343e81040d901c080040d401c4d81c03140c020450346401c141d40d1210a54038079128044940e64101100114584c1080030300b50442444c801400290310030b02c080d000410f0600716285c10000143c0c810074440d0810030000320400050400c44081952007030341c090810103820080f80c5010398a4100a4019244240322828454030541c485d114040e00c0c0e506111305054003004407140c1440e8400c000c0c1c1c00f802800b091240f032806040711400d085c02031a1040003101d25842e080d140049101282207941d644040c01e1204860078080e85507064640e1100c08891308018004100c000b450b44070312000c0040101d80d10002500c175800100003150032500300d803510501e401486483c815856000c0703015200728000c00005041180c40c1620 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 725746924 1250 725745674 725745689
    0x615030c15090904060e0d09170105010b041a0c030a09081c081b0c010606050d060e040f030503180a03021c03050405150601212f07030e04140702060603070b04 70
    0x2c081802c403e0190002020300110342054603690305030640b031420041c01c0c61002c46a0b940c4001070f4500040c1407140311707401d140390700140d04007001070007aa110101107904643c3c00c507000c1109401c80c1240c100c014000c1601e484403500001400c0008598046002004d446458054070000c0d0403a20301510305044180301c00d00420b14120000c3e01c0310035006200010300700e8140f02103203800032900845003101c600d5082070010400100e1100300032503aa20914001c0c098241100071541059160000c41d01c4208a009042010020004625848003000f0810a1106408452200c09a40f4002c1e450701a04210014101d488480b40c000c668030034000c05004a401201070181020204c03580111840001d1015040c0201160300510721480c2c2020800900c00d0100c4c0090494141115010144540800c00b1301c80c0b2100380304101888040c40c12540c00030350605247e014802124042170242c8a903442c036079804000030040140d2503402140261042d18200c041c1c441040c0c4880041c1a140120b003e03590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 725748174 1250 725746924 725746927
    0xe06040c051213030306150801090501050d03020a061a0d060c030b060a08070f090f06020102120105010c03171e09010b13060f05090604021b0a050d0f050307030b120615030c15 77
    0x40c4500340d0041c03d111070714002c1c5400f01c0e40a4039007425034002009021200006000040100403103105072180e1805441c08580152034585240c900075a559107164010f8082c9699450f42a03503100303e91000c1d40500009001c1c0b86994010741007410040040e0095000442d0400400114070714003002103030382266594440c00169214050229088980150040148220f00c04080f485046d005605002482145e0000d40c2e242d410040c808a52403040e4005810702031400040310010340c00807000c41c154400c1c001c0f00e1905640f0004100000c1e411030b00380a814407540c00a00100c40c5040d001450403110549003d032407103840300786410485415115400b006010400d00713000ca07240120340c407900710300000c2025052030840b05c0d0043e14140124000c00c01d0b41d0200f07016404011043c401c02c0c510f1050790070103103400e08810102800d10b110040100003016505c604165482d80c481d00001e10801c50300d022120380345030020314480b4180761610414404d1180140c00c0c4020b1520600010791b103c030401246 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 725749424 1250 725748174 725748181
    0x3030903110603011d1302091501020c060906040314030418060e10140f010c0506070c021302040e0a02160f05060718050d0f1a0708040201091d04020f06130e06040c0512 74
    0x3103600355006404051801080d006c80c1b00542d640382c0415000329200304800070004030610000e071a00381c0742200f040c0102800c6c400c00049a0703c040556080b02c0c0c02100d0030b207800904070140743c114402c0360044d02c1c200c0d51860320030013040560380c0310605071030940c007620b4450780358054840f942400500c030391400910700713401107500750410542070407a910043c100180c04200d50740e55641003820480b1307004000303150900c450056140650030520302c8900b000c403c52800303082141800482e9801050074400c20340000c2d0382443c42e80a208005003094100f00c1a038100c1182d8070303242d0749500c0140d85040002e9800320550384140c03084034400084400043c9003041c2d4112540d01d036019003114620071f540440d02c054241d0000b0380e68060785441807200c0d603503500c002d01d45440054449007903a08051f4100b03200700903424011000000b04e5030080e404903540820295000b00090303440c400e4404103020703011400b0000407850244030303007503014071030884040c490700e24044070032911800b515108c1943d403034407003011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 725750674 1250 725749424 725749469
    0x1d0610063b030115121a1303081e0f011701150312090e190c08130f080d021b070e0f0c07020303070204110910020d0c031107050a0303090311060301 65
    0x4115400307002600116080c0d44035130f460142d40d0840c1d40300184486840700f11404100858106480000c1c444040100905100c40c400700000c019600040902c0f0018012036411407003140d02d00300414103c840c1501c03e140220354480150020b00c030300344074054448481c094000040c0100300b00240d10000444200d403954030b0f8200c0d0303640d0408948040c440900303000315070360811b070481ba4403905020219071a5006180140001c90311120821000c00a529050051410400c0880068503800c107420600d8080c113410244468030a040780c48119500c00500c4007880e00f85122413110b44080c900c1a40c1200c0e54900c16598599800c5071110484c001c102c1c00240c40d03400304000703030a01c58000340803207040c52502d601003030031150741c070388504522100800d50512500d001c00d00010a003485201501c44e95410340e601801000320084010306001c844600d0064141e0304110700c1c8024140105211050780e940d00b000780c5081101c0c0010781c2c02d0f00d6483d110050324145030048904a41c0d189184050b003440d402031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 725751924 1250 725750674 725750777
    0x50718090203060c0a052d04080a03020c041e1e0203070207030b0105060f0f030406110409090b0a0603030905010c02040b04060e04030207080c030d11030c060f060328061d061006 78
    0x881241d03501da4250a018201f00c0d0400ba2000c2c0000e04001c02c0c02c00c4503428040d00d80384a031440ca920403070500d1000c001c1c001042a1460a404e00000041480e824030395010f0403040c140003800d00d0b00c5102100b0010748130b80c00142c4004480c018050901c80740d0721442400800c0c800c0201314202e001003003108640e091840002113522501860700010241c60300c101c440e0712070f8803d512078240b40d9214220042800b03260440c26070084104142048910f103140c1c0c000c1c15801c030b03e02c101c07810b10416901d10010341d11aa08403460040d0014400c0203126200d904400c0b050301c043d01d0230350052280c0034020894410000d0b404c845100c004009068041d045031080f0f0700803d84088088050000380140f49981c001004005e0245981e40300c00039071840d00d0414503107055038020000703e440c1c00021300072100040034010b085499030000345c08200744070643c084004604000d8510507007449804100f00745078200101810503a00345a60b203100030701e00260550301985c61028000643c8120858a183e00c0000c0c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 725753174 1250 725751924 725751967
    0x50a0201081312050a1e1413050a1203110f07030210030f0213080c040c0503010b030405010608030703050306031c0516030e0301020a2003030106090e04050718090203060c0a05 77
    0x8510000c0b004140d4400d14142c00304221280440c42c089841d0750301c950000c0072141344490980403031030f100440d924000c0035040850b40410030220f000999911511014110341d000c1c01d400b40800e000e85583d0303c0000400030440000b580018400b0404002402001c180713440303d05c2051006103034103401e507000c0044002c5520120018503548010300803174510180060180110b0f80001d2445903458204943d04150480381c0d0180700d1031900c1c0c7c01605071900002a2410344618600e150340301e940d01d01c1e149006244641088000e440086200000c05034003400440c440c403030030717400e880c522841c0c40403140d60707545101d0f14100842c40c2030012003000511000d0025800e4041e24060030717441000c1c1c0100c3c2c2240c2c090496100001c69140c81d00840d0582506041966801e41004519540c0b402900500103044c0d8090052000d03140004501405002c000260140024a44220b0030035a500003d10050070160b404038040d018a80005140c214a030007a100398241684600d850a000c250f0f4800380081c000c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 725754424 1250 725753174 725753191
    0xb0103020909041209080f210c0303040506150915090901090611040806090601080a020621190b1206060d060e0706110709091703090a21140304050a020108 68
    0x24004007801d0b58800d11032500441c000d00b40d1410020341510010302e208007a400190f510350145488841c11000020f40d400c4a0135003079554480103122501b64026132007071200626441c80b0220078007051100c045061800f811400460701c00c0c10090700140084490704980072011890b406032a2405800c0c1000c289600403482c5000040080c8159544001c40b20794880101c107030240800c090044640070014542c114030381c4001010705614052502d41c1da00c00d00d1360002d0144c800403554451003003030103280c0c40081e034065000c20040d24241c0c0120241d02140d41c0e08004207400c1094a50041c00d0080402410800140190003140c0d5540d0074808901000007089039040e58416030402884020b0003141c024160303071790f0362803003019407183d0040ca00b80c096004050098230b030000300b81c0020221801c3c082024101d88450380c403940c4582250b41441a1090058034048007201c0317185228022005c3c2e40940d032865107995035840b24800021107a400308440003052a4401c1e101040598014202c03540e0015a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 725755674 1250 725754424 725754427
    0x705010f0e13020c0d030212041101090806010e1902030610140717132304152c0c1e0702031e0d02150717090705030d0908150402060a030b010302 64
    0x790000c5010b58000c0254001001c3c1c2c04541526513403414001300c82250324901c1d06500b130202126040c0c0c0321040c00742000742020401d503013290250740074070045801800304000752117040d030351039070a855a480212200c1000c0e016501310324002034954400c2c4c0e400b406c009010034040515039502076a13140c401320000e0b007120000340607142c0000c1c00d500001b041d81c1c1c41c100c40180c448a82d038400c0603080d0050f4012120011071070420007a2106032119200c1800320803030f00481c0726038105005000b948802d4010143c07008044481c100d24200280c10442d0310001c07001850356aa5a80268222a00511264100003c01007006410b01c90164000d0f0508900040a40f00c000e5849102d05041c2020329000318241e40220380404212a014086c2120743c0202403c1c80000e031a003000020454094500b106400404201c0850301c903403010082d4a01925002d0100e40265481e04405040305406214080c103a1140c40d5048480c19031a481d140e00803640548a5810001c404005038054041001c216040560 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 725756924 1250 725755674 725755697
    0xa0c02010f1a040b040c080c0a1704030519050a050706020f190c0b0604090206070b09010603080c1f091122051e070e0303030a0903091508010f15020705010f 69
    0x40034810000b000007074008141200030840b00340401d550310403076024480c81c6440220080c03139822aa440ea40590302d4400c0c1076540d508031070146c441e048640c0d4040d80d500c4810b000c00003010741000003040c502202803007066910b4032010b0112458410201c4090000c0d80504c51300c0c00007856a0043c3c81c0040c2c20411b10b80c140021507020b41031300d4003504204c00c00a0899400e0800b0300480d1900035421240a5805103c80041e58004c101180304000004001c2545400051400202940500d01955006c0403ca0b0385a00c031112442c0c0c1c880c40d22082c1c0018405100401000302081c1c400c0d048003940c010042c00d03105004c00e040010030b2945110850610701c200004501203c001d100700d81c4a02c4807101d8040003843d007188101d41c0f4000040c840d405000c507480d90031166581c00001d03a54056813001011811000c14502250301c4180c56001800304240103111403c1142c000b01c00328140d414500c03458107a81d84c0c070303004904501d20000040c0050b800030360041c00305500ca521140e40c1604103080c00c51003442e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 725758174 1250 725756924 725756951
    0xf0d0e010b030721120201050402011115070507060902090a021330031404030609170313082118060c040f0905060105160b010602160812030414070e0f060a0e0a0c0201 73
    0x2000b0001720070060750340b8020442150b800000340403005180c0401800d092100d00003e00038407002618190501101050a40402c5076541148000d264040c2002c00181800c0f1140000780d002010400e070500c00c02c0001003440341d030b0302080c41160400c14032100c002040c005802104014410b400390204034583d051259100007180c0140010740c8503080000c0d03c1901c80c20700031908039103814440c02040003001440005c0083c91040190550425802917481c10b48603003042d8014000c0803040003031144801081100ba01e0101410358000c1c640054640980d03c164440e442031080b8020705170700c0d4000d24420700071036401d40d020541c807820606003580703001c03484e030f15464a0050107401115140360120050048aa06101414445401c292840e840505002c1c2d0151540401ca07000008000c021000405104101111000440c03051040d0351000340c49611000c603089084801c040d10101002c041703540e60420204000c220792001142040a8a42c0c01103c4044c2102601031401c540d2034240e2484c112 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 725759424 1250 725758174 725758193
    0x90d0b0106090504050f150f012f0706020c15030403180806040620090405100f0f0e010b0307082a0d02090108010807030825080f0d0e010b030721 64
    0xc10301074440303150442c0f4110400c0300750341000b011001c200e14041d0601036000e80100070000c624204503201041c071100c00004841c0c032000c14502c00d41d4801a4100c400c00d108070074543d008059404403d0f00c05070764940c41c080c0e90741e500200c90a40c00c000ca4103a4071202e2000302c1c0c003075032300b0904c28900071003984c070b01241c080c24100032034000c603265421800900080010303c0c864008144000301d0110314000020401d440c03a0f018500307006000740e460784000303495040c481030800e0140101c0526480082d41340c0c0b4040070000c1040c090003250302403110011541200b41c10580f4070482c4d1580e03801401d591f4101c150740445109664031034510316281c2e40c0001807441e0a01612204c0000c141c011b0b190303d031020006101c008181d11a401f1504004c40030300124025a01b22a41000d600450700e250201c20300c40c0702c4070340d1900c42000e441240041342c2c06035000000c80090010401d0f10300d050000e82a0100024200d4042080c055855409200100214091030261241c00803200410001d092019100c00102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 725760674 1250 725759424 725759429
    0x90612090203011d060f010b0316030f0213030506010e011230110d0503092113030317070e030a03081308030a05090616021f0605030d0c15020c0a08090d0b01 69
    0x13000211101451020f10411896910001c0c4804114055140180da011541710281c10021009052079414011901a4000c00b00490402104540d10020130107d081d030310215001c00c5415010f113400000c1c42c00b80010026045e600110708020702d24207955106002503041c411800e01c0405061121a40003400500c400c1010a82c1d8560032905070964940e00e0510080c8000281880414414002c00180009d41c3c0c0b00d25401800c00e00c1c40501001041c07500d503000703169902d50521800e203c08020103034814810480c0c50703100040000300d601c07540000d560040e607540b0f038960107034001f01200c40803034412a20160080900705460000e8140360300c455010345c0c412a030410749075444100340074270050108101a1702044502c104a041c10410000a48942804c5400012450214626400c4a0303540e88068002e2000604403080315090711805045070101d60419240c60050fa5120005501c1c50700031a20781000c0c0c10013400702541c203030360b88114075040f01191507001401008451300103103100029030301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 725761924 1250 725760674 725760701
    0x3040b09060a0c02040f2c0c040b040b1201021909150c0c1e081c0903290106020f010c0519050d0603060c05040e0702030403030c030c060f0510061d0109061209020301 73
    0x40e11204090301074003880c01c0300302c2131100342900c107940e2001301d10120320740c008d2110488000c54881c52030000140a4909a907001d64002d890030040e007105131055008100200220009092494900f1001c1d03a591150384114044c1c03a400882c40103e461069000703000d55846500f2500d40c064841d00d0b170140da034107040c105182c0c504560106104603c820801d80c68112202160a070420a01c1c040081508940344801802e9299030844001c10000044c0c6e1600241400e40b5240304560351484025941c1e1903011200c591540380000c9145552b2191044500030900d840e02c000030b07104401c40c100c8459000340b00e0701e64071984d5444c010001034514054406112282c2d55074948a82c203202d030081c0d04a802401d15815507204200410009030404181030803075426080c080300e60131b06820510080c101c0340300c840b40310500d44000c03c80700d4400c401c110f4059034083c4d40c850300c5654000301d00d80308580b00014050701085011408108003407149403403c0c00d040040358080344000243c1d00ac2401d49024038480301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 725763174 1250 725761924 725761931
    0x90f01050109240302150a0c0501050c03071e140d06030f2405011a09040e010504060c021509100e21030601141206011b021f090803040b09060a0c02040f 67
    0x8080001003c04030050b04070034001c40061035540041c003060000c89588880c06030200759154850f00030444c0e41c501a40010083c4054a400c0306903401e82d9008580c1c0d54003154243e070500032001030210503240311030b91544130844150b094101c40d605540103e00a01451500d500e40800012030701420016140c0c403460f180300d00340040d144412100011160f40d45c4000780791074010014003100c4203019048200c110900c1d0307541d26429000c80c0180044501c01c080355800e100c01e0204000306907114a20402050b426180805490b44200244540640f0751a0707003a84120310101c2948025070112158a6078401140c6040c03070204482011040100031020240602008000d11560040148401d0240c40c0d9000b500d006221410603100240203084941000080708071031140452130700f0309e070740c0da95002071661251050359008060048075540e58980084c110305000038442e032000007a03809896280858500b01901d50040c010386800080801c41000303101d031000409a120b500c02d541108282c05c1c400b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 725764424 1250 725763174 725763191
    0x1e05151804051012080318160504020a0522140d0224090d080901020d09032609040e0601031407080604080d06090f020304210e0f0409140d09120b04030305090f01050109 74
    0x49410303003011280350a164111114042c08e40c1c88460424040d00c1c0125401070b2125910b901c03c03103482c01020f40b41300d031145201209108144a0003020704c11070f0301e0582c1d0380360741445e80c0c2d0a00100c03200541e0000d400105111100d4200c240800300001c1110f43c007805a030629841c40002520402007000680b550100003c01c48002d59040c408540319000702c2c00d00e80401407071a034400402400001740301003c10100c0c088a441c2d42441000c84107a01c40c000c0043c41046040003d094441d6000c0c8021211507440d00b00e10340c5c0e10b00012812104139603a800280940d5903c0340c44160032a0700842c80c1202d415a54440421707050600c0c80307412540d8161904c0140c40340307000d01c1c1c40c400d03800607014511000307454610b010201551000701c008803010292044550b14081e0008070300507241d001001400541030070b00500c40f904002810003d480c41559980c9040c0341d9602d00700b1504559075002800d03000c02c0c980002c0c0400d001e0341180b0381181100b001c803054687d07000d0f80582100c0c001e802c140f0079581c844006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 725765674 1250 725764424 725764441
    0x90f0d061416180303120b060423121c0201020708030403030605030d08090607030c030f06121a070801030308150a0f052106070309020a1e051518040510120803 70
    0xb0301d4000d01c0d608007144010258200102e0b070302c0700d07072000030100084010100014981c64200100180014001c141c17250340b24000391405a040d569681d05100514600c50040d242c03805803814050310043c0035108241e40fa035040800e001844408405640d002c0100000143c80d440042d031085000c0d6800144d00c500b028201420b00d005034100e1810040b00b001440080000414400c2d0082641e050004420240315800d4001d031000702d460402d600d01c0c00b880011900e07040129404028801d05155200c070800c0d0202144140c8180c0e451400030f02c005005000290090200642041c000fa009840400103400020741e540d44030740004509020b8a4400c000d2410080f21150f10700394400d00c0441c9035681040640d5807044018241001c050301d441201056455200905014041c402610403180b160070711141c0d4440310303510032035020781c401890743d0740f1400441d02914004410300c000d00d45030200480800000d401c1c00b50a10486c2c078001c0c64001442c0c5440c80b2412581e9214596140d2280f802070720 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 725766924 1250 725765674 725765701
    0x170108030310080a1104050612070f0509010b041d180a0507051003020a1704060e030f07110607150f0e07031b090b0a2312150108070605090f0d0614 65
    0x30501c83c2c1c0e44803030112070004185507a8070002400a88001442e55a0b4000140d42101e80c2d548548841c0690350303010031072010300c100c04001d41c1d005030303444840c0f40d0740c4800c10082440759201c0c50140000c540c4405c602010980000d580240000088005054682030280e0500002c24001c039030551080c5010085030500b0344503400d0031055800e0440c1803603000388020f00440030040048815900c15800902040f81035800320b06501d04440c01c03240c0340c0441c101400003581c0982d00c103071a001340c09002d5680c2c17441e10600300e0b910258031003c090018410f04200034041c14500c0e40c0c030400191244401d00b42c000c0c1c01c11030180118001d040c41489c1449058043e203442c1c07101c0d000b40d08014200a0101c98540785c00315401d0440396040c460040341c2d1000040516480c06074030742140d002d10355580081c80c8940c0000c8441d00f02c56402455041a6a51810a40d40328068842e00c3c0204c1c1c420f11201803285043c170b0581135200d00c050103a48042005581e0750041310080c401c40c0c000c2000400900c000c038902d021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 725768174 1250 725766924 725766929
    0x111f030c02101505040b130203010e040506010b07120c15050705040603050c030402010801031401150608060330071b062a02010203070803090a0f0804060f02120d0c170108030310 78
    0x14030400403c083d00c0c107000c1250400d03003c0d10380685c0e16650060441c2e110034009101ca8001c400045480c0d585445020700118070a417003c3d0fa480c40786000108951101c0000c880406600484148900642003000d4458940f800c03c29180e820040010034011070041c0500c40c4500c16642d44c01d40d4840c00c0c000007800b102d602404200240100f8000c0100607600320514606507030b000860301c02c06400d9440803a02503c0344900380d4501981060000403495082104175005140c11019544003404408400030744d08000740310316500309500350b07004204903022402001c80d04d00515058110358000c015500c40c81c0ca141e40f1500004400301815864107003446800d100070304242010460306120f980000755070707000d102c2001d069400000301050b0022810450340242c0740e805010003a0030f00c0035003802c01143d0081c0c4103d60100385038142c00b814640c408259086516502e4440a0910003080600c100800031080c400061001e080940d020041070048103a000b8010200110360f00d15205100781c000c002540d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 725769424 1250 725768174 725768203
    0x17030907080c1302090d06020403150e0318062d03090114010807030b0c12040f03031a030a06050a27020109052704020102120c0c040c08060904111f030c02 68
    0xe030303104186540d518603ca07409061080d016840f1005003000074010016000001c00d610f2000070000200000c40c0340303280300749805010402820054060040d03c80c407982d004460550070b03500200c040fa00c0c100018088001211a0070002080000300c180c040c04014542488814004401c000184500b4065524000754000c401e03010f551408a066941e13005a00000700840c4801000400e40d41600c1c05035100e50710081c848880904007401d0405074603400900c1076001905014070b010402c00e984112a00d0b565018008203220680740d1110402490090580140c4a48540480890394601841507205605218039440d0151007440050100d0326039500c12402072058100f4072800d24110401503005011003441072542d5034403880103e0800d0809110300103550170100c0e000000c010b0014140c881e00400b5203080180707104090050721448021580103034083da40100041c006850200c1000807620042d12a12181f02ea400f5129801010000701d070000a071ba52080c10311150f4104802004003800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 725770674 1250 725769424 725769433
    0x181f08011b0504180b04020d020d0209120c010f0e0409020307081609060e04031b080a05122505210c070b07091a0a09090509010507020d1416030c1703090708 69
    0x14100100c10b030300d81c4c180359454420f60350341c3c000a0b1038403107404640900c01f0f000011961040340c1c00c0c01200070f400103501c1d01d0003010350050721208404000344103080c0c0e600585820000900518007280d20410350340441d030300561945c82c5000180c40400c01c410152007010040d2001c1e40100450302e55010700d40d440802c0040c1001010050000c9084100f5003050b0140b402c100380181103880380340220000d41d0020300e0b140000540709020307940840508920398041030360302c0a946494540d010380e10746034000e821103000708404140c20980600003c2c5210400e0981c84041c10b1b8443d903043d000900121080d04031032000160716030410100c50f09442d402003090401129280c20480c0c1030341e60001243c40702e4008036000034110040c0740590171440050903180010301c081c0ca4240b03030807030103004160f030780030098803c0503881c14009000301c0307407001750021040003981414106a071500c802d0754054400d40905c0b4443e1182c002040d4100c004441008101245554905004030301382c0c41d10170681e21000c620b800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 725771924 1250 725770674 725770679
    0xb061503070f0809211b0601260f190204050108060f01091d0304170f150a0203060a180b03060108070315051005132702181f08011b0504 60
    0x100101e04042c0d0190915103900341e40e40d01440c00740f80c2151080e1112151130a0100040d00c4120f40c8014810501d0030306821440000c4840304591303c981c20b010b6a003a00c4480c80001c24903003222048e05c051216041c040720315152036010810305101102c2441f068a101d00c4601c0001d5081c5402100d0040c941d060040c091403800702d4007003d4181e0107006c0c203046030783c490012000d01a01c08044480b140e01010940f682ca40c1d4804800c1c2947c2010228009140903080c0d503002d64200101e00525403d8410300c0243c03096881d5200400250b000400981c4e00143c2008080340821017203407500c101009903400000c58002e05820035141c00070580c00480781c2c1d8007080c81032000405001401440000313961012400303445400c4070043c2442150400e98108079005407001104845400600b014454103603d0700c410010303032003c0d400c01c80c848940690012040340080308880345645c103140d4040f4021400c0c06040070350040c1568101d03215400041c4681d10740e41403038007180344c0794a400b101804509200e0f2a152 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 725773174 1250 725771924 725771927
    0x71e0b03070804081e03160f0c060905340f151107030515040312020405010912020a2106060506180d0f0204020403120315180b0409020307030b06150307 67
    0x440208100100402d10010500f0840d00f0419201d0301d02d11801000f075030100003202c0303d045400c00c5507100e5004a802100352001c2d405413540002c802e4007541e030071407036420b0b80d19441d001d0241503c003140c4920802d4408111811a140004c50020741d0f904850400c0c41100003100d8214a644c202d48490150040c0400054040c0b80030a10001440d003031558440701010041800c0503181d0788041e046008907200d800c0089a0710b00c0251080d8480c2d00d501c001030302803000035002c80c055030081c580400d40c02e05007440a200d0041101e200306200502d4144466203034010207880c003142549900e404800c1d040e0b1801080200c0c068400a03200c19204203007040503040718490508441c902e140c0c000d01010154074240824100c402e20416005401996199901e19200c0c2e0a41c03600445880080e00e0b0030b5044400140b041c3c0120102c42c942100ca0243e41a2100a64001c0004903800340d0303c281d40316045801a182484084011405405d5041070340c900001840034045410380740481741d0100b0030130044002d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 725774424 1250 725773174 725773177
    0x61509180e0a0b09030702010f0c030207260a060614010e060708160b0c04050405070e03120a020307060905030d06120503120a091a091002130b0f0702060705071e0b 72
    0x1900320400840c114400c40021810560126000703407120150f20104901000d00100401070325100782da94801c403040502003100c84048080300200181c02c4074008001c00103602080004a80b1500d0460040950040c070312803908903c8101218400d884940400040d04880190816030ba800e080c00c18000c00007100040840c4070f070100007024900c0219416032102e028103901c03845680c0c8604401c0c00390a02071040c207002e0b08240f0403c2c4c410b60500c0c002a11003845202a0303030002a0240041c8445100400000c1154000401580852005201e00d4000c500c00d40210050180514003940d902d0009081040560b1103a8001c001d40d20b881404180000310000222480c2400750403000e170803034552070580d5019000398080a403003683c254070300c17008002400e111140140385110484401c24418151a4180e0044074100c3c190007205040c00c2040d1000741000700002a22044c145240210340d5000500907002700c0c0f001e0302c1070341c0907810034000c103c2c4005000103204550400210100d00d40301318050346 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 725775674 1250 725774424 725774459
    0x6091c031e1b060212010e06030601050103020a020a02010e150f0d0f06060c0605100914060a14030712051005010b0a0206100311010302091210020702031006150c1410061509 76
    0xe80301481c2d030041c840303c3d905882020610340b1920340030b540e40d0f040303a10031340400744c40544c800e0081000010b0958081c0c400c5451028444d005803140d21031940041d10204051040c103074002022100000b4a0082c43d4000c0092030380c4003c1c0700e511210800c07c96001c4502004403664468a0090b042c000c0300e4104003102019544204045110f60355a080b014034804c5551182d0001800c02c03076100d07240e483e055107045c0306043c207490a0f402955640f00d0800481007414002e40c258100310001e218400001e450320140074041c900315192040510886001c4801c243c3c06400c0a0b000403606480143c0c0c180820343c4c1084406001402175030440d00c41c9841204016002410b2580c0000c0b060001e0b01c2d01400c003180c5a03103080903610349070149107090b00030707501c0305070308030712074020101c2e0b400d010b00da1845884107071103800c0302d010015520081e0540c0c00242492042d6038642c05040480700d80d0f0b10030449502c5041d4850030104405180c44011220051000115811300a40c00014400f801d03600180014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 725776924 1250 725775674 725775707
    0xa0509010312030b03060c0c0f06070e041a030a0302032d0d0c0c050124060527010513060f120515041d01231e0a020906091c031e 57
    0x30b81441c540c10790040c10321001060305030003110100500b6000320740c0945420b003030307403001d68004040418000341c950400304c64200204452030440c0d0810300b0107600024200c0d10000307110610b080c5840001b8500220b250048005030700014a240e003c80500300304125880b1195100501d010b1000c45100107030040d0152100d00555035003103c00000e1180c1020703d5265000740082000180c2e0300810303403981c1039081070341030041480d074000980302d03100703c0881b6803090300610034403190b00490f8081c50340c0d03580b18190141080824424000c03407008007080303000180525111442c840803450009403002d980c8900f40b182c503518081c100010000100310040e04c00d10300b21800504076241c0440c005145180711600301c00c44d86091070141c5180c042e0180d070f40b110340c6c00281d84c440c681c0e60748402e50701100d00e807490b4000d041e2401000c54001c10054000c0c101940d0010401410031895501081c450b880856000700c564002807404010b25411036250b201d141400c0400341c2d51801c01a0011b0142200c407841042c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 725778174 1250 725776924 725776943
    0xb01090c090605030f070e220c090f09051e01080303100504140f0606041a030f092a0d080705011a0907020c090901021908241005031003080a0507030e0a05090103 71
    0x79900c505c01e011418487c080100b403108103c110844850b603012204120360706482c5061410a200f500561400003154002c902d4084800c0c14104075101408025008180100281810004040100d0300c2280601071242c01991207141c5451f6140d030642a540c40540540d00d8089070221070403140711801d5208583e80009010703500c505000c07031031300e10072548051011000b65504190031000c0340f00543c01040c0e400005109a01ca8002c580d4464480c0414190711980c0410214415030764240d020445002c002c01c0c86503040c0d46910b401c0790075400340c00e04640a0350f45500110b1112020016107082c01c00a4404141d9803904c450041e54414591042510841007000001d0002d0800d4045400b081406d000c1c101e20b0420003070001d04004401d0f01c10f0840c11046150707942d00032641c020584c8685400402ca5519001c17200c0003600c0d00e40c0050300c0c04202081202011003c2003401c0e006125040d141d0352095680d25042c02d0052200e0042d41019210700350040003040790399146d51146041d6900100383c3c0c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 725779424 1250 725778174 725778181
    0x4080414011101050a0603020316050105031902040302030a0f1e052116060b09070c03050409110c0601030507060908071401030e190804061d0d1212090b01090c090605030f 75
    0x103032090340c0b1001c8a501198244002c000d1109045d40014086900c00d500715020b03441d4203200c03480018054000c050000c1d10501c009829010300c80005090200740c3d110061400b500d036004681420041c2c24140c4518102c041e10408000c81ca440900c102140c8144001c0041d9090b0f64040d00d80b9605104c40f81c0580600e0752552020751f102c5d00300d5100c1900358042604012a5142c40c10140c4020811540f080f40340400242015016849848e1510341c1652080c1c0707040c4c20284002c004001c800c61030451400c06000081100705d041040354080c600807001001803903e4000c0042481c1456048940716800c0b0240400a07000e049485080c070641c00d08011550241c4801c105242000310032101c014020b12143e19028040408000c00554001d50740740741200c00c491955031401659203200301d07013000c00304a500c07000c10403c1c0e0008150810600d050303110100424660b1041d288040c100b0780d040650304c2e00411291384a17200b640082d80b040e00300301440500d00700c0301511034080103095220410408002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 725780674 1250 725779424 725779427
    0x4030203191e050d23040204060b0703080f100909050f07090b06040e0a111c14161112040b0d0609061203030b060d050106051201140f13060b07050a06060501080408041401 75
    0x540d10754503c405c5035400740c0050003105190308180c03400da0140d0710b4098085209468081150000c54254861288549a10038002c113605001009880c0780065050041030340a481c0c010604554069001086042182039056080800c0b5500400603d0300d00440d00c40350351190825241100e8090520140e55551000c50101600000c00c01e8100b10000080b0389413140b03200002c0c211400310030941004040c48174201c02c00310180c10b076898070700048004101d259861049150740c15120242d0140e6402064030b0103071200a13000741d0400d4009002c0800c4240e43c8900f24400c0c0710007814068418003c19180010b00002d4900590003d401c01d03071110841040c988800c000c81c1c00681c481c0808002d40c1d1307900c2c10014901d40040c440340c5140c00713100d400010207400d620b60703284014000030001285d0500d020704000c510516100080240c0d5201d00300020054503400c00f0b4151280100003800c2032480328545a000c540c00c58104506200c0b20b0024440403e2205081e1403d588445410b000401442e400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 725781924 1250 725780674 725780681
    0x9030207211e1a09012d0207050c040f09030e09040b06011b1b0311040e030f0a020f01090c081e06040f02040b0d2d05032203080304030203191e050d 65
    0xc01502035503c4140810700760041c218024415400d1000070000c030b448007054084d0a451615100804488142440b8a010515401010194490340c00c859202241502003010f81c4c0346e0f100101380e85581ca5440c00c0505810040c1644016011a00b6905500c1c0036a5004026140603202c0350402642074001040c1622241c1414880c0d60060b107840d0031408803096100e001c02540c0400c0380c6900501e000c403801c40c14140550315054030240e01440c106014050380c0c0400e84c001c521b85204503c079075500c0d42c00021081c40b814290501400c2c091020368200605079261495030280e041c841003100003407401c0108007103003460308142e000075808041885400010302800021703070f1803980b10111345511003c1083c5a0310707440c02078047c05c0c2287c1c0104011010448c1c0b04080f10f201604d02d8008100c0700c01042000c6482d1014051200909401181c9039161491542c01c121011405070380b000980040105035299898260146460302c2c030a042020017099030003400440410050000c0401c214005408680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 725783174 1250 725781924 725781983
    0xf02010c0501020705031c1e0b040212091509151f03080c010603020307080d0806060c030f0307033602120309120106030606050108060904120201020f030a0903020721 73
    0x6000f07545507282420070039100c1d03010f1060100d5030700d00b0312203038040348000e400f4810440c0c10b0940701c0000802c4034208640031300410900640d0081c2c0c20041031a0200d807c0e1010f0380100c2e548001400d0304501c0d0210060102400390151203d5400011101c4450604c160302550140451044d8180c8110401202d040710036070f6000100007050200e00c0703081d641c80550080c0c040768000c40840310804c2e50380704020380b61401202c101000a840c0d200240d05410004002c0030b4600c0d0002c200d0f1315050b042c8124092a400540e0880006a1610b2075010f05002d120030748018070301c03074a42156610081d1030907503903c1804000001d0045a00c44070501c142d040c142b05071072007060050014942c24800003039140c0200542d02040341c210b80f5000010400d54420b0b003025101d103070064900c90990700ca5031200c50103950f110701480e003159000c0201c40d020502442c05540618801c003004a402051072070040d0a05080741c12121000d9801e04a104412901e82c5000902c207810040e28600710704c40040c01c03051a070489 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 725784424 1250 725783174 725783183
    0x907210812091e0c060c1006030b0f160c020405070905100c05010e01050108060c1602040c050403230c04020d110301030807230309040f020904110a020d08060d0f02010c 74
    0x40707070300e96103590140c0169114280c004165444041c54240d200090b24001e020b800c881e501200300e03041c103030070450001c002124913501200d49100741d11841506484540c0c1040314065100014420240d003070714035071a0450a800c1038940b9000520f03600810340c10300c0a03c0a44655151808a6010b80c002c0740d0302c00103002c0192004103083c20355000070384000b004510488180d0f207000c5400080788410711515041c1e50080340034001c2600e481041002c41d130440c03a03881410360005025600140c1d1280319580c00c80e0560388501d0780341c5166043c0460014011201c0f480c90301e01d440d5035600883d4001c40d004070b000608890050f120310b520891407004050b418a00c07400c1010010001c401c3c4450360000d840744a10541807914121030160114148a000c1c080120445c3e0050003003007034625050b00121002460b4400c018280824040060300351030358002208016400018009940341e4103108008540c071107414803908904203040418075044640d02c002c0c103145400d00c2c18a045a2082603030b0729075035411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 725785674 1250 725784424 725784427
    0x90302220219021e210307021e2d0d1805030a05010f05130f0f2d110d02091902282d030e2103010302040501090509072108 54
    0x92041c003070364421100b0010300c2c02c4c0d019000410013440001801141074a0f8498081403200d2029a5001950700040e00c800158015101c80040080020040314806859403004040c942d0b51444050440300001c40d00da480c81c040a81202c0d6007010024015400d0700203803030b02c48510000440c07034044241054010030380c5030003134803640c40c24020150014034061114100400081d00c51300d00c134240c046c2c220345000f00540d0050f001d800101d00e601188c601b500e070081800001118034050051100026282480da0100c810181e0006005482080a08095080c1d80794405012141c00241010170000c00411012034070694001901d01150190b0b02d240c090351080451040c40c0004842c210129400160300103a000c104c42504c0300c0d0031150040a0111a4000c410a46030058044015048003050700344640305000c1564039080c1d801030303100a101d6140000c40d8895040d481080300340c07641a400854042d00381410300007650004a03c5400f01e4490040030024002e00c20811403e0030700c10180646205030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 725786924 1250 725785674 725785717
    0x6032f0a12060506040c120f060302090f070f020c1e060705010204060908010c0503011d180d0c110d210903020a0e0405010c02161215110c0601060903022202 69
    0xc06603007880c400e11042c0401c0c0d907a01d0500080302d06031145039000402e40ea062a0f500ea905503ca02c0130301000e03030f401040090312600881c0310120191034415242007800b04101c1c3c92a40044050003100c502d00c05052441d224100041d14002c1c144441c41062000c21007190310780e43c442040b0303207285078001c1c020b5450310f5a41a003e032000030180300e148159405c207a404410715118104890603682208824005c840c07051424007035003100181103601c24540500c201c0c0889004201100c9185d049546203211403016203003c00c11076084407241c40c02041070324041c0001440020190421380850b04c00c00000d08460842190012900c0e400039401c0100c0c46404140e0541d401030076481180103034028480c3d8400041e0480c0d0b100b02491220b0400d052910040c80b041401d414400d080705d003c4d9800019088103002140102c42c038560018120340300c0040c80d262802000d11010340100501d043c003400032451a00840d0030404500d1481c83c3c1002250075450b02d10080398141c80c20540c010002043c10704 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 725788174 1250 725786924 725786939
    0xb06150d0e061b070f031d040f0b01030e010b090112051c0201021b150c130e0a020403020f090702060f1314061902091e010203090303030f071206032f0a 67
    0x41c01696a07149044000340c0f40c4508181500c1203808007544822a00360f080c825031030031185070071f016030100c264039080d00c24401a9034640c0140c00c2880c08140002a004007100c0c00542151380109500480303906010980740299070300d006427811221131400e450944403492400701e04207024072503242c1e0350030300805901c140c0b6541503000d024005180306c0b412a60740c007840d505035a9403242099040840c9400400200c3d10f840100241118202e80080488813a4903840501108038007100c480200c2503003c03904106610b80000600c5d0030500a075400010303070900300c034000e440e81b0008110a070021846404604042031401c50700c4800c0380c01030090f82c10203890000300c03915044c080e650a000004030201a4a46030864070898100c44001010b1242c1d0f507654041d41c111584603881c0c1a41580424420203a00e07440070310040d40315051640c40d441081c0750001010f080140c0c0710101014462030f040c42400011820441ea141e000d030181d607240c1c09420302000689000010b09241c0c2c0d0072400c41e21b070004068 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 725789424 1250 725788174 725788183
    0x8070504050c1c0c0e1e13050103080706180c030302010c08010e07050a08131703090d0806131820040f1401050105031003080403030c1a01030b06150d0e 67
    0x16042180c0c1400741d51101d1030b010300c42c0c1c05804007002c20b560b03000500b0603440840c2c0c1d00468421102e0b04003281d120085400041c203401a004581020340607002864200345420040c68403204070b209801c001550454640b006140180705005088543d0744110641000000640341c0400764042d0801c6c3d403607038407440c0c024080c06e130f80500703a400b1694010000c1801030400c40101d1241c210395070354604091056000b02c4075281c1c00b0300030794903c150171b1603240c0214028081080c03a80c080c03002030740d60b0380c142680120f00e0680303c028203008010400f070038410746950340780454651501040c03002c52a0003180e030009914422034000100004480026000d181d045078046040e03016044504205001c2001f9503102502c0b400c1d03c0e00c4200e0000d150040c042c941c002ca001d5038001001544543d00c0035101e9450322450741c0160010f9002c030304a042c06400700071f02044e0411039402001705180362540346503281c014420001d0b10103803040c1e0804250000c1c2240030000d5810800c0303000010f20000549114003500d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 725790674 1250 725789424 725789429
    0xc0f0301091407090b1e13080d020601060f05030a050414010f0f0b010504050a06050c030c0709090b061f050c16090e19080a26150a09090f020f0105040f0807 69
    0x425010720000f2541d0f40039a40c4a400c4440b0100683d1421280c800302004a4402140c5550301032814480814540c203409103c1c7e0103070400314020152180340c114080d1500b10305a000c0020400c0300c88060794400d50146c00d590b00400880d41c013007503a46a170702d0202002e0070b0883d003c02082d0b02c1c1510036450140c80b070304100c2c0520440041005011440c20044074a4030603030080e690406804002000b8041c1303d0f0008101101c580c0c0c065a0600740d590f800241400c42c682c0c00529500e44400302c10040c4805812040e030040300c12605c3e0008514540205007004043d52100400c0c03050106202886100074070080b004801101c401d5501c070758403010750000402d960803010710b191249000501d0589120040b04994580001f08607090048001e0211641985100b903000310312442034a00d1810000001454060a481c240f4940035901c3c540a00c000e540705540110710040c20801a10081108081190140794041d5034207400c4409000c0140c07494481d41c0d00518501400290011319400c01007031a005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 725791924 1250 725790674 725790701
    0x8011503021e0117041410060f09020711130204170f242212020c030d03021c0917190f05130608040f05120d060e0f0705030c0f030109 59
    0x101054006800205454101229002c01d50a0070401c00c2510b240c8181a8403521606480e101c54072901c4240d41041d40c0040c20b000c00b01d440d454140003842c2c5500000015140441d2b086041c4031180d1034142c41600d190000c02d02900042c100400a24407903011200540008160341003034000d0f11100d1580c5d00358400740032001d8000d100d600d40303070b50a0b0446070800c5184041080081c549981580d05268200c608500314103c1c0e0700b0045000041d624000d28025200a8014014021021003403500303000c00b03290000d081500c104145000c0300a62a8081c550844107900000c0c005000d103490007010b900503030300508014012541c116000406400c42d40301d2446030355401c0b240c16001c803090b0703400d024a0454107003d08942a007401440c3c0300e02c0e203147e8002d000c1c44c8412044c4041d170f140c0608000360075a15003404000000c0404003180140100c03002403d00f20b009140d2480e044d40701c1c08a11101516850401034000003042c1c00c2c130740001c2628200c0c0c1070030002c0d599a5940e201080d00074a114100b011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 725793174 1250 725791924 725791939
    0x110912011103010f05332d0d0c0f02070b0901030b0a0b3735091213060f1e090e0609040309031103012405010207080f0705060a090801150302 62
    0xa03031b4058400b820300e1417503036007901c0c200750203c050b5011080d40d045142d032840880e903c2d04003076010620983d5861000142c040742c151f0b0318811801481c00360340b80b040700c21051003c066650340400e50f000802004403450b14020035100d030010b0004801070700c0d5440070345a06c43c0844002140d0703403202c40c006050740052840c035950541c0f81282130220152000300e01c0f1802c21051400403036110701401c01c0c2c107892402031070418803002c0c1c0f408068044045402d4218400c0c0020380402121200030000313445244c0c2a5113025080480641000e19000320703d004d45000c01400c3d016800c400c4c4d0144400035101310802c0382d010b62020818000814408061095480404440020410a0804481090040350140c0d03900008604546500400349102c2c0710440e0159a41e038030050341d05802100b01040310010410510407d450f10000a00c0c00036a600725540d01d030810340c0c0000b03101d10001000d02c2110340039541181c540d0080306054420221990002415500300703020207a952042e10307010000d4a1007280c171038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 725794424 1250 725793174 725793199
    0x6020601050904050307021005070f051501091e0e030910080718080a02040b0f030f010207020306070908150603150c07060f020c0a0f0501111c05010603110912011103010f05 76
    0x1030b01040c29100034090340c0040160f5000340c00c0645141340351010504103540b41c02a140c0d2242e04503c0060820354068121080100850368484c4035a0300400004c003040c441203c07109109400c054190760480000750b134500c04d88124401c14010703074802080040c01442c43c3d1220340c03409880c13040704903a6580010711021003490015101207040094441c3c400083c40e602c1030070713070170700c40109040c0303840e1a44070310a60590030040d941044003034003806024002589440d054418103103080303000b61118040c0080c10b4000d1101c0c3c05c0015200f0303d84203c1c0680d15046465a1010a0070603002401207044840710a0400c80f0100f104001040e4051081800700054100e0103005000c90082800e03030f034800e4020349400808502012151982c2c54095400002c003044505880359881d88200e00114440004004031182500c0b203201d1a401071007581818041c3d00090320b540345451040041043c461340c40c4042c5150950000d520000340c000d00c4030419941d83d6103606032480034070110b1040d07d01c03d840d0740813003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 725795674 1250 725794424 725794429
    0x6030c062a070e04080a02100e010b13090506040b0a0e340b1603031d070f0b04060206060d140a0302060a0f140109090201050f0a08040c0e07022a0d0c0602060105 71
    0x4460464081c1caa0380d00703d0307482c0d9a8690800794001441c0380110b10805541d41e0300f140880c400d0324005544100005400c22003034051102c090310303840319076201503d410360420202d00c001c615079502a40c0002c140d4a959100e03000d01009019003a904202d900c1195000c81040400d02c0c40f622141c040203888011040003181c490326048107a004040c1c1d0b2100c1030002c841106500c904100480380b113401c0120300c882e00c0c00c00b114049642d0104070700550b4032001040080d5200003808002070042c0503500c1c1d2400c1c2c20101e010b50f59403005000940a000d004803034078180305408495190f80b0415800787e41490279281002583c5410070f540b454000c0e440c02c0d50040e100348291044c148060040d0341072103516071802245000400b0040300a0f41440420003509020302d40c5a0000c0500700210340b02c0e1039a0b800c00d41421022007800c2d03000728030745c0c0f891001404010380d0001003030080c1000010100a20a41c7e0b1b1102d4003034403900f814083d4100380c01c001042c080241d6510454240c031855403c0300c01c40e80e07a4504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 725796924 1250 725795674 725795683
    0x7051f050106201c090815151203090105030601121a010216030201170406091b1a04050607021302040906090b090a050f040303050c12010909020301050a06050a0e06030c062a 76
    0x4802c1c0c40c540c0130030261504000c4501c40403407a10b1003401c0158449a030f8080c0c550a16801b40840490118031108111100709183c05801185200b52000c240d41c5030001c0d1215602e00c0b0304107085044c07000100002d08660b10560b015003d0680b4000240310051000b0014010300615082e910302600801180300c103070345041c007030400803a07030140e40d40c80c408282c4000d440b9007194050701c142d40c0c0799111170005000c5141c2c1c9138003051410307202042049003407500310803c06100200c10854070503071040004011341e0b5107800035245a80e404945045404560741b50072030013445103900a2104608100c40000c41f441c565020003190241500c1a80459848480e41412684121001c0c00094040000b09001c288641e000035441043c1226030b5140001d00e100c011603410090744403034503080e00e429a8004504003809401e400070480d01042c003942e42040006404d15800d4040c03885002d14010000f0138603a030401048045d101c010b45650380d500f507220140140c0c4600007000300d4441002e82c0c10140740c00c0c0e0008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 725798174 1250 725796924 725796977
    0x20c0a0b180103050411030a050d180e160905044d0a0201060f0b0a02010c020f0c0d0204140406020c070b0c0a12020f07150e0a12060207051f050106 65
    0x128881c105200c55801980100f0b405072003590302e0f810321019003040b61020085042003502483c0100000522620020110300381900349016007955100108160a040c1308495001f20034016100c0040030041012640b408041d800954041e05101d407900c0714642088210344440200f0320780d69048090301c00340300d503001c06010380703032600e1000c5c0d80907040380e00b10b0800542f0004440c3e00c00880c038103a031010700c2d1510020b1900001040c003800203013845180d40900c54041180c04e0b0b40040c00e482031003403e01c80d8030358000c4c034410b9001384801c03241c850842d9a17550080c2c030388030695809000141132504151009411280c842c5469204800000c01e01c43d4610081d01c0e220604640140030321401d941d03031520440083c3c41a2020340c03065050a890000c0180a42406407041c612a00104180320030014902407901c421240103042e5880c0600465a908400040340c0d60000c0001d40e03262501c0c0340240c40c040002e144151031a5822280240d07259160704541d04032840796803002c2604040302a241010121007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 725799424 1250 725798174 725798197
    0x100512072115091e0204150813050c090901021216020f1c03020d0b1305150d022d03061602060a06050f0904150c0215070e031f09080a020c0a0b 63
    0x21074080103040030b550040001d04c0200c2c610500c1400c4510030941c103036005908155403102c0a05880c03002030780c1c090402c3d41d00c4070100214a01d00219070325100d8440305d900c892240a10b5003840041d80c000c1c0709404440540302e10010081445c580490001d900e50315074056074006009058617032151a00c0014482d0711070000c43e998815051a5641c290001c1d400504480b02298481c0640070155540e00e10800d240d01180340041041d14001441552412080101d6072280c40807815101c0940c80e040b508807401e0400c0d240b11034183d100c24600a0011000b40031036680340c8070380402c00804000c0001e00d403402c01c501c1e40071500c0e035495070007041064500300d0107a03503000a10301450002d1450810001078015004852420007030042030301400a8541205000000d6032221104d04025050301c880998444001c1c41e28602c1900050300180c0c844424046088040000384400480e6070040d034040c8100984c0134000b20b644195a0343c0c080c1d240c000f18042e40d40315100e81540001c2484180080312410b96a8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 725800674 1250 725799424 725799461
    0x1090c0b0c060708070e0d1104050a02031509040602130f0815011410110709021b030903060c0a02010b030601060309050105060904030f030c090b070b010807080d020c1005120721 78
    0x11035000300c80c25540240800204542180c0d030300b106840f84080c2041c55230140c0c41c0c03481c0103004601404142c800103400380b00c816204008000391801c84400101c410b650460b025152034855080c0034010340a2480004d9a0300c82c240e10001e0340010441c050b90884061301c080c0c90410695803141c8040300424424444481d0000e10310a4107480e00851458588040b4204041644078081c0c0591500303c440e04405401703513000a03078613010902c441c10220350a54800096190140190101e40c5560003e00309030380741000840d81c280210700070341085004180c00f03400c032a000c0d031f0340e00c0f0014040c011a81090b1155480d200104200d030404081880c41190541c898104c80c0d100f1203000ca008100760450b010401001e00f07008180d40c0045001000414081c42414000c0c0d4185104c05090000980c01160107038003d403141c4118580201d010800d101d01101c0d881e00c25025030005035264466045809603031aa224100007141d50044004624152011540000040855514000c17105000d0441900002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 725801924 1250 725800674 725800681
    0x60f01050a1a1306181403191e080307080601170403120b09090102040f08070f1401090e0f0124080103060b040b0d0807060b180601200f01090c0b0c06 66
    0x2407240b51041c4020b40c44451034000015107950180c20140c0220001455002100301040c0503008007034098840c44001d5008125800c001903035407184010240c0c881d1000101c3c5405012040b41c00702c003520011080d0000507145032502406650080310711070042891100451200d500c0740d011701c40c00c005500d1070400c1700d441d142c9040c3d032020300781881070780324948034450000513454400c0e003640562482c0001580300d07030030080d402c4800326107034211900c00d40c00880104108820f800c0d4400840c0c220102100381c40706c0718070040320030468940140e03400c400400c062140741c22260070130034100d46c004140050041d40306c1010011401c824800c1100003030b010310041c000b040c000d901c0200843c0c030040c8001281907500011035510900404140c9003181c001c58410148121802001e00c10b420844090381442e1817a0340076038502c000640498104110260050b007803420010315007031014103040850f030391150200441030203000700400454515050203800205201200c0c1030b1038215010380080c000c41c0c3e9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 725803174 1250 725801924 725801939
    0x1502030c030609040203071e2405030a110904050708040501060f0501140306040e0d202e0b090117150408030103031412011409071d010516080a05070203060f01050a 72
    0x100181c02640e0601403040700203145000a070781e5082001c0000441d000180c07402d40e1064042e102078127040c99540c4101d00c1c3e0760708250310104507540b01d0b2150700001101340c626048040c0a0240504c280d42080c03422042c084a50381000d0303884d00c02c510a200a010081e00d9818400c407030141c83c172419002c184c160100c513050400d080043c55104002400001c0c1c145540342005160019402200c0c000c590420400c03075209a02e11441c80c14410240000c0c010174080032070334414080200d440c0c140d28000484070482c680c0702c030f800c81d002c03124000300060782c9540c48241080181c81c04a00c0d1860728483d4140318000030000e100214415074218040c1810341e0310b5501c064400c0f550026080f00c8a19042100c5e001400350440894040d0120854240d61010f4010500c1080140030340190300f404009000c1c0380c8400700c540c41c00c2000103400e2030240d03111916212114070360820141c00511074103010800c01680c580c000c01524035907008800301c41054030307815940140c000c000e00801c0d400c415100d0042c840c24 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 725804424 1250 725803174 725803189
    0x1110f03270627120a09061b060e031303140c04090c05041503080a030911030c030a080a090b070b0604060f030f02041e0509010501060e0301020f030105100e150301031502030c0306 79
    0x1496642e66004800070510440c0c0c180200303031981301e000c02004590005102e0340184150003074904c0d41044400d0050500346800e01c0d45811000805003921200000d00114082c000c0e2203400610f072600b504402c8e00c0c3c2c03030042a00448544d1544c014030449100d4025840e140c006e15a40d2508240342c81181810300c410301001e800111030154401035040c1001002980d0f80000b00398a8010760780000e0122007528021041141200344103101e0792040360501c1e211b54010424011965015100540d00e44003a00140c2c0e0360241e65000180c1c200c000b0481700240080e46220601ca803104032000c20049817102008400310005000240c016180b44203c0001404c0503070252000122400d600c4140410241c80c3d0000e030b900866484203a80d4442c0010080d151b00f10040c5024020304400a504142c5618a990b202d408148219407103040c000c0361190403103018010f10811100060300c0d60309080600c0b8940300590340300723110850f2800a483c050042d078900510949024450540c4524035540714002004440d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 725805674 1250 725804424 725804461
    0x8010c0306140f011b0303150e150d231e0105070f030203091005090a020306070305091b21060115020309150d2a02010e010b0307120501110f032706 65
    0x41c0f000341900c4004074071054017244840752195902251200c0c2072041030a91040a0340721600b070310b500c0800c0c1300c0003518403c05400c1e880c1c0c0c1030354005c1442001d42459009480c6031420102d580009400c0d0b00000031010401c1d01d0414143d0700c4400e060015046550b08a4030215007100010f80030030402000c551085d0025a0450882e41c111540030b8080742c5010200e84060380c440c0da032076002d101d0307060071820240b0201c0d0340080c0d50f040400aa2402c1c0207015120851101300142d0780d80c140c903401c81d103035075241040303489a200f0202049429090000c4290f0340e001c2801004401100300949402c0756200004946100101411540e420340300000903202c10380068207965070302615000c814140d0782140901c860808802c0803d2000450303c24400303400c40d05240041401c1e64103001c180c07405620002694811142c01c004200740302c035998103082d40140680c0003020009080010200b40702c00040d400755000e80c0307403403c8115151280e460409190320340d0b47ca0540440e0040000110104071102c2503002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 725806924 1250 725805674 725805677
    0x5070f1d0a1b030f0b010c08030c09180705040e0f0402060a14070f0507060e0d0c030b0712051509061906050f0c03030408041e0f0302100908011508010c0306140f01 72
    0x40e44510100b05118550760318054400003941c84844002c1070890b401000b096000a00303011500b04865100d000440c40014031007481040002031145032516014042002c882100082c1810303424200c07002804d80e8814802c43d4000140c002c0403070400050082101d0146a0040800e46041e03400542504c07001101c010341c1080103018401d46022a50012907c11054402e0f0080d010180c00d100e00607098014443c400f502404000040600143e00c040c0703007005a0360032150642886d600c07034000700c0d2815403c03000c40540354105800d000408000c03050070f2010603c200c3d4580351075682c800512080264880d40c020300000c0300001003110174015402001c00c0b4111140b09860006902c404a26507030050382d003143e0300900010100704501d4448840c1e031150200018070810f05240107c1030a140055000103845440f0013000003d100d401080c502c802042c001c802446002904020040c1d0b4015510505e600b1f94280032440760007a120344204015141a40f140300c20b074001d80005e00c003001c0c010001090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 725808174 1250 725806924 725806931
    0x60503040210141c060f180e03070f0c0503060a0c0c060510050a081612020a0312030b1302030402031203060a0b09151306030c020606150c1002030a0905070f1d0a 71
    0x3840400300c81c0146894400500e20040361001301141c001150700d41da00181d42440c2c02c6001380020b03c05141d012400c2c607003041c40850101c40e00c040c664194450582c004156148080c01c90080265941c148021200c049064411680d45c180c24103007620f00c91071403000041c0c15a64030800048695204a8109040c0303000741d004582c5036030118416002c541c0089a081d40300003660301c0c400d070341a111600a0710071021654182d01340e55011541458040c08010b00f5050340001540300c6c40d00ca40e0062800010091410511028000c03e40000790300540d02a40a0700441ea2041441108103044034007803500500120241032910705200d801d0740000e580c0603400b152415812031002c020001500100c00c055860b00d1f411440c0040180480d03880c10058800d5400c180208103050340c5007850b16082d256503050082e41c400075010428142810030140b0900d6620201c14003402c003070281d0095800511560807109126140e048480d01601c00e407150b444070100150b20100d0031202044001c0e0407400241001c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 725809424 1250 725808174 725808197
    0x1180c08012601060e1f080d20010b1c020112050c03190b090a0c020706110706080a0207020307060203040f0503030f030604090c030b040f0b01141e15030112060b01050301060503040210 81
    0x4445c81038261080040d1042011020325002400e01e4030b0001042460000c200c130101110004c4d01c030b2004a9100205254511a4076017036002c290420000300b80c00401d0350803206d096182000c031001c031101017640000c070b0001400001c419141f107090300401034201d5a42c03c42d1350b800744032800186016482c0c400144caa42d0220000d071200c00c206801200c2e01400403030241d101d500024580840c030b902403010408101000b02c000c0380040f943d841a24810700c0c01c441d050b551101e004010f031140880003901489401000541668040003401c113481d203081c074411031345a40d079041560f00e0003240f80c040c0d4081020000326081d890254050010180321f5046848a1640d0b501c40140c214801c80b01a148007102e040d1510410860000c07241c050320039502c10b4090781d494603020442169889505c010304003401e0502803815a111999072549a4401038a25680c0d0384030b180899840070800400c80e0360f5410a906401f2643c002c100791b034141c0d00fa0f60741d91815a0303541d8081251020505407444144001100e21 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 725810674 1250 725809424 725809439
    0xe012613150504030212071115070203030d060501121a0d030c1e0b0604061d091f0608010606050408030f090a030605010803130504060b0f0c03090901180c0801260106 73
    0x2800c028800e07401c0020185402d003030181c10040340b0340e005070b1002c81c01c000d86400580c2085048042d0203040c1d62003c03a0201220080200d03125104010354140f00104020220400c0368000d032041d60740a030780310801c154030895020180d903820449c4801c0e0130080b0803100607a04100282d008454001d107040c01c00d0385800c2d11074003a040914400c40034411441c844510500c000002c2c0075403c02010f076001c0100708d2a01d40114429050a400034179441220800f1492484081040450b41090f01c40700000503130f139500890340142464440c64139a542480bc001920f14000c03000d5404955611025501e00100300c0ca108000358050383d665503120100740c0700400032420500c603060180c0040300043d0342e1103070000c40388542c9034010b43c40306100c1c5003418400e02810910400303a42080d013405d2031a070b44403105e0340020350550098518035034102120100001c0c106a0403640a54040542c0104200c3d009070010704580c003403000d00424007203e00601903003080207017a031200d000b0380c60004000183e45481c1c054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 725811924 1250 725810674 725810693
    0xa02041401090b0105030c1209120d090203070b0c060112030504080703030f200d0c03050c0f0a020a090b0306191e1a04021801030b180906070e012613 66
    0x12011003215030014081000a8461001186002d007807240c11482d00c07041b00c018500c41d82150f0402ca8410101040030b00c5000c00c4981032440b00c1036485d42e00c1e20709a0040c07034010652164241e1092052402c005081100302080b600c08000d060050082a82010310301410300c101c500c01101080410000019004030601104d006944603a680841040d1540001045542c4515118044400e000e000f40302018000503128007100071420a04406d07406030500b56040c0c001c01055000314010300a80c044d000303501240c900c0c1c4d81d0f8030858080722000d40340c4105000704c4000e81d8a168042c0e1000c00822001c0700d0800020004601841e0f000c591a10418840301041503559400c00000b034070f0300d09807000d50a09070040b80410320151411401c28620b00c0060182400b18051503061641d28080305000e03441d4040600c082401c1010003901034200f40980035134541d0210303803c80000e01400e4449166602c100300364462044158203074081000300890903021035a018203040c0c4c4442c10100410001207000b030307 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 725813174 1250 725811924 725811941
    0x20a030209061c030806040c18140409020402070c0602060903130303050d230603010c020c0303071b03080f0d0c0e030606090703060807060512010b0a05030f070219051b010905010c06020c0a0204 85
    0x10388203031790b1342000400e1100b5101c503403070300c001401241d00032541510458552081102c248821401c10001e00101190042c201864040d4119000042c0281808044c01103102101c07119802c0750b00725174801c007683d03450780120084a03680d4050180c0800201e172041d0060001010103083c00940c8107500d101c46a0340030241c840c802c10070448a0208001841c00303114048403403281d4005001b850140b900042d40701d215003071005007215034208a0240b00074198403403501940d8400c2d1501d954000105c01501c0503000007a0000406060011504205124082c142c1c0480d030040c0040c0410b071114030802069a0000301b1034000c1543c0c4200004084408000f000000d150a44500c0e540e65011128005100c01c144c0015881110420504940740c1e40b1000300d86d032040d220750011041da200c0b03560403401d204040340c1d400351900c1c00d1080d050a1000214a080509009580003445164043c0c010f580c030810740d200d0640032407000220340b008900303142c0081800c413161034140c0b43c00c0301413540000c08940c1c070390 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 725814424 1250 725813174 725813177
    0x60303020f15091f0f0212010e06040b010503010510020c1c0611132303120408010f091101030218120304061206030f030e03161403100504020a030209061c03 69
    0x8103804900300006005145032180d42c010022107514000c441c0c03541d180725001490075240e40c2c440804407000ca250303001c040f2030b180618041d592080c4101d102c0407894000c0c01190000404880421400d2610b482050200709041c0c451500f10b0303107020b0400614402c0c1d0a039034015806118101c010302c0c2d4941a0705400d00300710507000c0b04d40d0103d604201c02107034410500142da08404001c40602201070134018000c1325007507000380702494038030100d04205d16400f00300d00d03815101d285000c5205205c02e10150003030300d081138020403540086500520907220082c00c082c040f0016103820703000720751198008100070b08030303e0000343e41e03c2000c0c00410b4505400c07581c4c000a54101142c10302c015039204400080b00f6090040070301c282c40c1540c503001941c10850000409111001640009a071001c2c058452480c0800400004a587d100a52a46032200112042c464052642906181c62161041d18051a006030010f0341c55030171a400d1180c0c0d054060141c1e58403103209490040481d801840210f0034130700c02e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 725815674 1250 725814424 725814433
    0x91b0806150f0a03300201061401050304030c11120322060c151e0f1e11250f0f03021506010c060b0f040f090b06060309031204080d06030302 62
    0x2080c0c81605207408100c00d2840751440030041c4a0329540c0c0303841c4005032070700300701c4048517801140c86004000c030031079041052030b40450900c1c14500d07406500c024201c480c0c1d41803011400d10644011501c030320007102c0c01404991580b03000000b00c0d548003070906007400090301440034181c2d80000d0501e1074109450183c03201100c410407050228180c0e122a00915260800c400038600d41e0340d034507842c0c41f0081c01c260515566076099003807208812a503944600380c0048200301941d80009080302914a10003400d550345255000304865003520b1042842c8642c074a011142040044c50300e5003114403041c40c482d900e0026950400313020948002840d55803511403401220f5150040c900a800c0100384020214586011010000e040c0d8002e480c0700d040340d911510001343c001c0d20382d0024282a00c40d0040a0f0400d2801c0c0700303035a24103240c0d0321455845005811a5000707645030b80030042a40301c101d40890303140d0020300801501e01a2084419001446a09650b0403d4441407038942141d046904c25070041e0310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 725816924 1250 725815674 725815681
    0x312162102071203050912101a031e012004090606050403032a05060106180b04030203071a090409210c020108011e0e01031a0a06050310091b0806 64
    0x2403104099081040c020a40c0162048020020b900d4481e41d21070307034210810b045010400c26104408039a24060014007050003140203003502079440300c0440800b401680781c0362915602c400760940768040039000900512515889035610440c613120044141491340d250b02d00c444810200c2081c0200c0c0d0913114071156125458191071406840103940130a06201c8200024008250f010385c128440ca49130301c01440b0018840b138001c405000003450003900d280910000460780e640c6c088503d420b4100b80c1c00c058840c140c1c1f41c20700c03040342d48168400258550b000a008106191b000d04080f005002480b19003402c0007004070100e0165901e03468115540920300308000081c0e00c004880440f40109803524104820399940042c019001c18020044111038004030503012000100424010b444140c2c1081034551703423403401040c41440c10310000c030b204c00c1200c00243c0c4001d25104034000c944000b0000c2050040c3d081d126401003d80101c1565603185008241e0726103540500300800402841d0003e0004d8036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 725818174 1250 725816924 725816933
    0x30f060a051605030106020a0611190503060109050909071712041e090515041107080d0b01020c030d0c11210c0907030b0a0302090a0b0a0e010e060a06080a0b031216 72
    0xb03505282003031040900060185581c0090a040090b81c00300001500240a0300c03488264000e80e2985080d81400c00130300c100c200d60106c080d500520007030725441c4543d5229402c2084405088460f02c04680c480788042101e40308041c807041b090505101510100b82e100c102c00c040c03d40c000d40000b40d02094442c90f0340d0b00c4000701c42c41c0030001c0c1601c1700c0400c60350030310f801c14001282c0c90084940c41280c448000c5280f00010308100c2d03140f02e903c0044603503601b11404180d80a041e44800450140c0520b4060802d0f904010403280460091070b036070f881c944a09a071320080c81400701400903801582e4200e82040e4010f40e07600707888207c580c00000340f8004007910100042154000d00007420503013081d02400141d00c2c1d803500719064a504403003006a983c0c401c0d06007001840b80c01650380c2e00044241c000074558080c40102030581e00d0300100800300da030b03c10040c44441c6185101e0f000001d12081e00248070081968003603c1003010040941380c001d0140007692484c0e8100f844050103080000e9044001c21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 725819424 1250 725818174 725818201
    0xe012f0c2e11091905030a0f1502040602100207050a0c091407050c03040e0408091503070e011e081005060307030b09220b04060b0607030c032714030f060a05 69
    0x549029006020b0341400340d6040d0514081e56800900400c685038409840b4004000340f10040c01000e801c41e0141d00c810300b004c8111a100c1f6205071040901d060902e080340c1154004c45e015114103400418840750043c010000a512104050b1860300407944024000b4040e02c0d20759008141c050310103d590348001604000c0e403039000d040d84003402010040c0242030800031013640c00f156803c0104680c2383c0c1d15400d00420350b200305040725a10482142c004004220314a000c2c50051050303544111004c078040c00192400c004206903006080d4512089009003885028840c0d40100016080c403941e6546e00d0102d45107410948280c3d01007070304c0b5a01c04105040c04a809688a006103900c403034074030b00c1e200c0c1c60500c2091011004e05140c44000024050201ea60010080080c01400a03580c6600c2420001d040e00c0030350008500045151081c10303440103542021001070350120b4044511103181100504e8030110060002c1c0d014007440e040c26041c0740c0c007444040d10815241102084034941001140c100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 725820674 1250 725819424 725819503
    0x903030105060c5206030c11030318061311130905011d0118021e150d0c0f0c120806030a060926030c031308090d11040e012f0c 56
    0x80340545860611031100544c0040b085580f1030400013054074040000b03c0701d200c88203002003207912001061148070036580600b000031180ca041518402d80f125261450001d20303042c0003920000450740075050f9450408802c4070b00203051000050282166a42d0509444100b00d54a1007050001c241c01040c800070f000d2100450b40d5080c152405004c280e0001c0c4014440c11400c0d9241019400d85030a82e45800001894440b64259415291444070420314044c00c4a80640c0300020740c003c0070110498013030301840502a034000101020300028a0b412107200e080101190303410302c512541c8001150781403241c0c4005900844440c03103108800740c01e6a01c44040388040c180006003c2040050b01c0aa180a03aa04403d141010072059281c0d8203211303289010b4442819404604410b07890100081c203050341420540a03a4144208040a80d285080b030b280c00030362880d4192140300742180c4082d44140c00b44070306608003100303040c1034002840d07a16082c01611222000301001500c00b00c00015204002c44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 725821924 1250 725820674 725820793
    0xb01060516060b0102010e060a020415210e030d06080f062220150c010f0b18180106030f11030706090510021c0203041406030903030105060c 62
    0x1800700c40c129401464440480041c04081e665040c04059a2007074001300c1c4003c40302001c039061414000c1401d40251b022348103103405000d0710070058510500a000c0fa00c000820300000c030200441444020010300078800060180b40010040031040030006d11840d0050415600102407a0102c07080903407034104090a985034110020500c5110182214a503907000c95104906074180500d54400050501200d4240d80d0300c6404140321694004048001c0d18100d00104002d2244203a200091002c03a24050400c503008000421031360301900c0e81101d00c80d00007042c1506000c8080000c49501c1c01c58820b13804c11075411408002c94014400304039590300c00168214084d20b40545803400140c0020f015104480c02045007a92030140309009000007003010845402d160003408515400075100e0340712340103160a50a865010078814140300068a1040c07034000015841d603400c06080042d00d422000c043c6580c3d1246000c0c0d8420040c6040943d00003200d90480e4032038214048411000c152450a101c42c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 725823174 1250 725821924 725821927
    0x9050418020f0d0f210318150e07090f02070b01090209100c02061201090e2505010c020a27061d0105150706060305030a1e02071e030203190b010605 65
    0x141c2c2c0d072000c0c000ca40c81421100c0361404201d51411000341c00422401801108041515120900302c02075248400700703e50340c1c100501d40c4250322142d0009460a805461000e000880e03104007010769002450b60300f14102103c0c1c10700c3d40c4442450a80d40c6500700302512540121340d00301009101e44607140502035014041d4100b017014070104074260a4500300c20100a0b2040610741592030301e4040f035802c0f4070f8041c1d0707405440d03840700c0240c400b03850311000c610b9903032089040e0310f0050441070301a5801048940c4d10031001d41c0c07620004403508503c51500f40d038440717008800000c1070b220748504240b040d880c076544a03865111021456080324060360050101e07034903aa034101054410802c03000c0c10342d80d040b124179031a00007056004201d8094018000c1486185c40c00c0441488400070180001c1075050303480b050031508451103030900a014111400150307010b86010b000010254018201d00070740101c0443e4502c0d41ca8000a19026814072a80008d140081050041c8642449924003401f114200b05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 725824424 1250 725823174 725823221
    0x70507030c02010c06060905100806010501050a050712110706030c0e0d031b14010606080603010c09080628050f09210702191a0a0f0c020d020618030607090504 70
    0x10701800e925800003070410101964501c2040440c0c0e1020002e800a0310040005d440c000d2590024841c0d2405404410b10441c00005040d61050007119000c201700d40c0d400b1b013084101c0da41c00d21281030001010703040c0140810800503050701005040b0060005603800309105900c002d018005450440c009030060480a8080d40843e41200c100444615809d0244c0a9a40300342000d45022008005090140d4241800091125440302c2c030a0300030f4200320000c00204001e804283e170b001c20948079994540d044000001e1001c401080c501c00e960300c000060380254a00310300440c046641c01c070740410f1610040c0040c40740084081000782100b0607070b6100e4105281000404c400c0318056008000e1068a1014000103030150641104000300401e19801c418481d9821101c41250090000d00740003600c1e182d00c1148052040c08495480e0381c0150210799000145d07002c1c4415580884075802155030440d803200f4480c1c4040004921403078165440e40c0c0f090741003030200010fa404841d5020b05010a0400c503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 725825674 1250 725824424 725824427
    0x905060f0607141608010f050c120c03070e040c1d04090c051512092104051f050909010e180304052808010207080304020a32030a150c0807050703 64
    0xc07100c0303a50304a01a114428140c3c3c100910703001d00e00182c0d402a080580000402190540081000013a4000705011543e07600f401a00a0300881881d10308a003045008108400e034241c0c02960410761500d48150300005403404107066900c10050540000e000411820040c41240440100d0500850b000e0066521603100e00d201946e02d405001d100316a64900c50b00c84c942500100d40f03e05c506c108200e036031440c1c1000b5132521891266100c0300810a140c1c2e0881c144517408049a0030b91743d00405d9568050200c1900007403001003401b01400380401000140a1917456404050007041d000528142601e059a505c140300c20301d6003c0035405034020b000078055580c800c1103103134a28103d02c5a410350308900c01c905084451545d4400c28082d44001000000d120420000354840e1b8000ea600c0c0400640e01e00c42c03c050454a101c0740c401120f195400c8544d14440004c0c0180c0390500203045818255994640c401400b18200c003c0c1d0300c3e56034400c454500950003002080d442000350030000d0038032545490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 725826924 1250 725825674 725825677
    0x1808060a061707150e210705101707030204080303090619020a02060f0c0708160c05060703050306010e060c010e010f0b09091f021e070201110c06040302040b0d05010c090905060f06 79
    0x580165402d03141d0040003010310400348040a800001c01a559100d10901b0300142000c0031700c12403e05000c0e4450110b440c1c1844001c84100078182c0d0740c2d21085000c12110464000000340c051410113408102c0001d590700e00300b002d14040d00c409800307000f40d814581010031400c0d4105c001c10300300d240144964218903401080c40e0f54002074505410105079a1400b01c00300310301c03891100904e210f81c04a48110965a02c420f1a00c0b114425001e003075200e520f0f2030420441c3c0c001c25034018000f541c10400180154030030800500d181a001d44890f06001c11031000c42d0070369011000d54900d603952030281410010f020b005005c0d1900041d185a0900d0804910301138031841350350310040b008004003011406a2034035a0440e0010384481c108910300b0388a1159000c440d40c48030005030f0000b81e4502c40754180307442c0800c2d8000c3e242c030001c108070310b880c0c03440d801e00004e01440c0c0100c550002d000c41e0003102261080c0500c812460f05507807410101f600b0300d000d034802c642c0050b1505000303241d18840500030303856400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 725828174 1250 725826924 725826929
    0x1a01061b06050c091009080d1e0e0301090b07050a0905040e0a030f0c05070608041514070c11040f09051b060a05032a13080f15071808060a061707 64
    0x100c010550b50740744000ca8505200d1082c03001c1d081743c1071240c008034040c1d0100300d56050310707100f034143d4804c3c0300000ba0840c0c514441401014007107a11020403001d003406000180302c9100c020f00040742e41007481d225034419010071035911020990000c1ca116a048d0700580607c042c14040b2020000b2481d6040540ea48004018004047c4402954520340e107d0181d002c0000d0f03c0c0d4060101c1d00c0190710f40000030401032058400b1245008058804104ca0200c2c2c040c004c0007180316100d1003d00e0f0b888610442d65641507040c113a80c07826940d50714680544413805001c2400c9110b11000c102c0504c1490310b00c2c54081100a00c04044403144008289d0341d44d400d08465240d281442c02c107841c0d031511002c100181d0b4000140c0b842c081020018260344203d82b0f401b81000d41364030301100b8200d0b5500c0600544480c00d205400c0c0c0e560300088c076040d85080c843c0c0c0c100d580100052070402c6004440d04003800081400d504002859030000041200000040c0a000040d0215994000806044c80f0300e0aa440181d170 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 725829424 1250 725828174 725828183
    0x9110301140a080706030911030105091b0d0516140303070c0b03040804050418120f0e0d0602040b0406120b0a1409091c08060f09010302100f1206031a01061b 69
    0x14146a5159520a030707014000c3c10709101516080c940c2d86201030014104828200c0e0580304400308041b0350726040c41028410701e030600141444103545108480d0790006840302c942d0101d900e480310301c04101e040000c01840002d070fa80c0d000c4a14103002618030106070f20141e075446a8400c10100d00094151144001280c0700c60f0803107605d80e00c681c41c11003920300030f60b0081a0494944211040794104803080500030724043c117038400d000c99108030111026050307030016001240c107005c007141e40c50826030b5030302c0e455030300800d0014100354032000851180d41c400d5005400048907000880d8a84210307228680380350008a4844d90340310324141c1c3d0680c0c0004040420b03803045c80c0c2d08000400c00ca10038018550400c1070421080b4610b815800090400364098444074081c0108015101c2d0504010524a068030b80090800c1d6540880b210100c90580403a180501000500459805000064041d81005d917200b164104083c4050366040e458400341640302c4010040034980380e00ea1450107000184a05800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 725830674 1250 725829424 725829449
    0x1506180e1e090111070302151008070308031005030a0302030406090f050a051c0602130e01050a05010509090a1413060b09390408060f07030b2b0b070203090a09110301 73
    0x10740c1c1185004110460311010310220000300d00080560118230b070440d20305d207140641c41c80e0300d500008082403440b03405100300d144c0c01110b0510215030500c0107154804640c011441d4111b482c0d030040f03030912510420031409139102040c20710959801c0f818050180085440c4055101c0c94034000030b00c1546640b042034010908081401c0c0c900d540c2211030007049802040940d5100300138108541030150764401c03c1248a0380d6400072860b031920654640072150160760305410400d00404206501c0d074050640c54000340e40704d62141c440d80c41071216620500503403c000002c0d8500d82070442c1560300000d5180d115220a00c20800c0d052151028021031100440080391200004811404010041f5041c0d04102001180000c1d020400003015886061054020845a11180004e805031010801d2039036000c1e54801440321808118503a0a5000c082c0030a240710500c0300b51242c5e040c074403050f90705400603000020341d8000d5003003220420340180a840020481440034501d914814003060048a08078001b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 725831924 1250 725830674 725830681
    0x40e15180a0213140f04050f0f060d050f031b0109050706120f02031501030b060708030604050c0d0509010b2b0b07030b060c0102070b0709031509061506180e1e 70
    0x642c10303554108001640c0341c04240d140e58880214902d03c006152041101c29224082c0b41424003d4901410320085015050b880b090000c2c5099003004000540180c280146040498400c100340c020b1f10188030051a40c1e02d4070002c1040c03582c1510500303c4081da04106580307000810000700c5000302c6519107070003e43d084103190500701401d0004d490310740181c008400d204000007804018a0b211000343c0703080110003201da0034080310b800740c0403026104070018400075505040a40010343d10180341610b003850421003803143c000715541901c15640c281c0d51105452414100040c0c071480104802d9442d101909490404d100080718880000308562804c03c00308232014080c1e0070075691004001d2115858401603e8090300030b4029400070b4940c40e5040011500c030728000c000c104d054a8110201484803840d848407c0064010f42e9011101c2c640c1e034619194920495500c00c4001d0000c1e692802c3c08013000e00706c4401d030800c1c40d4005075005006201880b04602c40d1800110036a01040f1a03541c40c2c1c0e5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 725833174 1250 725831924 725831941
    0x3002040e07090e150a110d09051c031431020406030c061101060e0c121003081b01060918020d03170106120e0d091a0c070803040e1518 59
    0x4942c401120a824004211030320140810009400300740322124681580e2440c00380d6040c1c13078003c2014002044c04204c1d00c080c0001e660002c3c5151785c043c40460f0816405151080850009000c00100080e135841000c0300f8440c09070348568011a00340201d41e0480281d06010605140407c204202c8882c94000340c81151503641000c5c004640200030b801d800d5903200b4000d0f21200c2c001143c0d017044d5180403000b0400c0c010b99020301e40071302d10384403130a402c0074443c20b82081c410030042c11900444040c9174002001601c80c00c01407040824600e96062019021006582911015008046011f06280492417000c00c540d00380c0c02c1d595011240d81e1065005410140c8003200f41d411100030001400002040240c4c000380d100b100403403001c030108641c0040316542c944802c40b13980f2140004a0802d010000c500300c00d441d9101c4200e002d0300c12481c0c00c1e0044005840c082003544050500d400108040214200d00800254001d80e11404007080b4810b01c00010b40c2d640b10409002c3c0400441e1002c503c051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 725834424 1250 725833174 725833183
    0x12022d0112061518090e0c0907020c04050405010c2319050f0a0806211015050604121e1502070611120402090106020d020303010b0c030c10063002040e 66
    0x2880b10052001c0341c4007503e9001003201200500794034000c000c00c800021309118511810030102c0c00800a07100001c80c0c0380401c28040d001400803c21885800c9121107141e4881c401e450042e0700c01d1000180364542048080e114200c80144400c4022080141d000b8a145c508200e510040f1403003007240040e940c0c4030b8141d42d240980c000d22824508007040304021070350000f00050180310308507030b5018107040d8800c7e005500b00031000d2a42d103541240480011102c45030300710a1010020103004024030380c5841c0850307c141c00990040c054107440c0005002403104000c04502d82100c845090070444950b0b45500f54007009041c075914141e64001101424441e91381e11401d94080094115541d44801018004146c24180c900741e1141003004000076a5a00020790a49550920740241d411a0701e0490408101e401c0b60f02252401e0100300840c0d481d900c4240081001c4940303e03400090300c181000103405504907968064802c42d240303c80c69401c11803a4846012714a0b60444010440204080140d03060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 725835674 1250 725834424 725834429
    0x90610180e15040b010f140f12011d01050f06030303100e1f03050109021305090705010305060f041b020615090a0c030e011b110a0b06010f02031312022d011206 70
    0x500c0014284020013188500a41c100c2d2100b8454021154a407122407114410500e07080e070340026030004212a83c10803041c010f41c200c202000025907082403200000d85000720074900c0186944d113604020410000d842c0c15500800c05030020f40c01c40c68420050a0300d07a01e180580c9441d102c0c0708000450182030458007408400f440e028a204040e542d1a2103406002070340001c0303119030041852014188030310b1040d03c0c0301d100041c000307040319450080194020207010700f12503088015403c184071980c4884c058102044078a5201c005075681d0880001d0628202038015200b0400c0c0001e15034495480b100039541003200070000140304251480160010000307103c030310955501f400700480500d070341203d0348080313441e890320b62500c9a00840361450b190703a0100c200400000c09100810080d5110b00200e1180450500480346001c00d0800c40c1c0b0409a841c0d844015900d07000c5403410118200191341281042c00d21003a4940456000782c8414014070002006040000409007003440060a0700400300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 725836924 1250 725835674 725835703
    0x405010c05030d020a09080c090f190b09090606151608030901180c060f031509050405030f070f03110d02060c0a05070611030f0907060905010530090610180e 69
    0x5036801c0320f4602400c0c0b03920904c90320b24107020f0441ca80c00c560818110327552240003c840d0032807003903541a140741001072502c480b80359443e94454100c6040d4403490130480c00703500c0c64030003021507140a1040081340d010100d0280c0c01c03013030184a0b02c040c401070400221500c40c3d2201344c86840e56542c49a4a005040400081c1c1201e0032011900d07080c094881080320131307901141e961003091300201006500360750300c0d480c250301d01a203070190410144617a540556045407113401502d207880c006d080740e040d4a40090b2816134950111070700345003c06800698a1a10484103405460025490900651030f00401403c4d81c070603103000118a5105803081046500141e03000408000348100312800202c5900304488458411a00f8400300d05000380c00100170003200c24613620720202c14140001110190031143d600410008000b842c102d01809220300202c2014030303003500c0c626600c0c00e80180c1d450718601500d500310021071000c09103c90409c50301c51001080c00c1e45d4000c50b4280020710f2051400501002040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 725838174 1250 725836924 725836927
    0x2040c03090f030c0b06010e012102070b0c03060901090516110f0d03021308150c0f1c0902010f0f09050108040f0605070815030705010e0f04060504020c0c0117010b0405010c05030d02 80
    0x1055001009a84d442c0c2c0a1810341c150f682e25840151080c0c0c08600545011442e84040c62200000c0400385c071a00e00c01010015040c050a580e418695000940f5101e4a18001104004250414551103401052010310908c90390030300400d6001c1041107442e051007000692020300170403503010401c1e0f9030800074060484525104c08440200250030004440501921060b0002100d080009010381c403240341c2a00f4840c20f4466825429003580540c80503502203a0600041807804040c5140d040b2060424102003011000c1d880010101e204d5403e411090100744c91190766010ba0014a58007070720000c0c24080b41c1521142060154018984402810617060800304501c1c01e50000303800d40500c514030b9100c14600071400c209900c80d103240c002c1c0740c006100025209603034909500e4603c818040904001900c0b900d510106050f607008500019103a0710074401c0d280c2c0c65a100360707144078806d100402211036505041040c1054443c500c107560400084100841c2030050a0017240c5900c44804d0046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 725839424 1250 725838174 725838203
    0x103171b030c2107020121110403030c1b0308030628030c030209012c040206070605010920070b01060c1506060c02100e0306061315030c0509091902040c0309 69
    0x995a0301e82d9400303c034480120600c0008000741e2400540d28420b41c16103e001d60804000c8403090000c2c81c0941c40202151500d00c0a03103050000c50042c8042c5009580d04c078403454030380c01c1080501905461201c1085541c2c402007020031481015241c000000700c0d135442210740c0e0750407500622455500e09500c42c51000b4400000c00070204164030440c3d2003075807040d405a13607078255000300541c1044104a49154413901884441d01d0741c9800394440d200420841c200500c9459400032500301340c01c4440e0070303030381c90007107224060400001c64002403011110f10718050003641e4102212070b040c0b1850041c401480c07500300801a09480c03c8030002c80d000c00c100b02c001e580d214010100194503a0990091164900c1d40011512414500343d00500180003001c05458901c00d10010080b2403124007440e0fa03585c40083c455820215603c03004600800c5080f820a0508040103800007001c0d00103d4039500c0034800544600788248180c07021b0b074046400007040882150240c020b070070701d860020030744030b01c0074440d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 725840674 1250 725839424 725839447
    0x10c060c05251a090304030f020a032415050607120c0f030207140109032001090b0a02010f1103010608190b0904210e0105040323120a080f0103171b03 66
    0x101c0c440580143d80c02401c1e480c4008640b00500010384030a00036030000c21040c008240002c2d402c081d07041c80541109100f568075100c1c016183c980c003030f6070602c42c14420290451542a0300501c041d20802e8a034040406203403000090084c03198041c02003421100d4580312003640d0184110b224041e400600808090f805851b000391501c0c1c2c10700074146003584001000519500c0340341444203407a0b110510b0201040c00c659043c0405003411401c0d41000000b42c03010031107640c948003a044409080e0004031f00450013480150950714140c0400d508920107100401c05168403440c0b83d50008900c0c9984441d146242c2c0303032203015050117086160020f525506100c100204100d140413640c51041c0400c020140300582114404062000140050300c10300052010174068030001070203249410a924088540d24500b40c1407a003080020b60340d1010100d0051401a0054510340d88401c9181c9800d12640c15569900e803100f0402581410562011420b4484601c0703504103801e11040c198100c948400141c0c54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 725841924 1250 725840674 725840737
    0x80c0d2a0605210121020d200a090c021c030204051801170607050318011404030c0b0907231c06050117120f0a02071a07110609010c060c05 61
    0x28550180f250380f428501c090b40c00c880b1003416141010607060a80468100001e441c03408207030305a034090b000c01c4505000400c0c250341c0245103e400c5a0705107117045e50804000c1c0043d03076540031302181400c0c00322480c038459010a90f85081e0382080070b6500f02e607001c610214000e0269400050b0090150a6005502d5544c2c40c20b6504a5410b030541d04480078001d400540c4031030b0180c503108046002400400c100080c0e02e0030500414402d0000042c1f20142901c410f20381400654054010504500c00c82090084010503143d1000110b0000e045941c9055020038022501c051091050448904662481d0391500f150700c0c0d0003881c03c11101013100c041c0c1021380c000d240a10660500071003400403551590800304031000401102c1040754282013503130058500c1c41d408948001b003140a040b0700810310320501c440410300852403034000340c1c40c0d00040c5400c00b66848001929441108240700030303008ca0b0781c410341d214040c5500c5080451021100380d0300382c0c0e042c040d0410030440000300d4880c0300240c200150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 725843174 1250 725841924 725841937
    0x108040c03170310090e1011130e01140102030703170703020c0f0f0c10090506030a0204050618090105010305042a0f03060e010b01140706090213020d05060109080c0d2a0605 76
    0x5104c40050750740203840100c2d125640310380450307004a00c10400c1041560b00503140c80400e48032403490318142444d088902d42c044d0300121000341c48040140184000103021071b0f200e40342070004514103501c6443c0602000704040010100c1307152800000d048138403a805503000002040211542e09003564541030315400b03203d140000f24411100441032501d0b08013007906000206460710b0381d0b1142002d050000303a42c002444d504c40b884d020040094161917003030061040703068255582c03403144e2489040041a0310184e11650415003084140030106040910b00080c44c0c2200700c00040e105454540e0f207110346002d03489101c41750507460000007031010a1f00600c0301d40c0c0e18003000f0070010440130019203049102c64042c44c6c00c60ba0600c83d043c00280690300503100c280c0020308465800c404500e010b001d81e4801e031f42c4680c0c42e80c0c4400034071075156008a00800a4410500546007800300341c00450a4901005000750550150042c0036541200050b52680e01d000007900c003040781510303007002a1007a030050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 725844424 1250 725843174 725843191
    0x90411090a020301060e0927060403080a05070504090f0b030f07061457010b0301060b0f0703090b0f04080f390d05011e0203060307050108040c031703 66
    0x850000d22110058800c41381078071410344405007014403000c10b0058003075000341540300701c201f65649003006030034208803141d5104012005203500d00d07103482c004108040142516060b14204414800104c2e00310f0300380c0c0e060310202100080c450750150103038006000800c00d60b03601030090000e8a500d02201003103c1003030383e00a032600c3c0e1710b010590300e03d42c02e1403040c14a004040d03a650001803040c04c4003103400000c1c42c80f0301e00140014115480a4403200d100105400301180c0007025413882d2a8402e00480204580460081005501c9c1000b0000c2d01e1045a0850100090006519003054082d0351208040d005800382c00703446441c140f12a035000d90050140c81c429200b03400d01c0d1a11501c0003c1c01301910428001c6002080004500040403080440061010880c200c000810161600244900700c24041c1c800807840700e0005140c00000344050f142e00720022300410400c00c251b2000034802e02191000e103170060750b9958605000700d0388103d03a0070086c4181c401c030000144007800c5801650096244 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 725845674 1250 725844424 725844439
    0xd060905090d17070e1801060302190201180201110703050a05010203270c09071e090e070207050a291c0507050c1c030608100203160306051804030e090411 68
    0x1c285098829a10300c464541c02c9140c0f0100081d81248070700c510764840240a4036020032103561000800031142e00f40c0008000960116001554490600803405000140d000802c50510300c18801200c02c0c6203604007074180042a055010201d1007001140021078001058a0300c0c0d241ca85041c3c1e0107548261240b1241140c805612041c8048519042a8041e6114020441e101c105410b201c94501c0041c19002400141e0505040004d00080888500c661541d1840d803000d00307103207030001142c00c0030b46940e04651244000780b0440e11000c02d014192005207800034a41d0a082c41c8400806400c1e2800d402051000310311041829100d0f100c441c3c1a49185c40244002d42c0c40140440d1240944214540e095204203800141101c4142ca02d1110000518000c43e0042d100d20b803840c42c002e078000c40e80c503481d03074000b00708090002828076400040c0c0d282d20b0f00380101c2d4980f90002c0d0f481c103241c58050001021490100381014080c100010022001401c400c4245c0742c5407c003403003005001e0354a030380a11217 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 725846924 1250 725845674 725845693
    0x1e090b04091a06120106030902030a0215120709180207050715110c010c020906011b021906080a020304030c030807020118120e0108220f0506040819170106080c0d06090509 75
    0x105007041d5001182d41c0132070300c00303141e180400c2280607248080b4103a03018015545800301689078401d112020400042109507100e003010418520b082000300f03400e0410241982c244040241c03611000074808001d20b015840b16031031b00b0618140a410f80c000c00070805501050300390079800c10702000784440c4210590b40d00b623060300c006503003441c003e10000358401035240008903030f580181e80c003040074041c00d80e0300c0c195112a0b601090311000c440407070703080c5100e00f55000c02107164400c401507031061040c2d0081d070850806a40c00390400144180080501c068400041d40c0306100f5800200c0e141c2e202200038942d81b50318201140c40d00b0420440c3c500058506003100303c194058003005009500303071413444c00264075019862000e042d003240c04445507000d2050b0703440030800412095010301e000f50340d03c82d80c6940029405d5800d0604a80c2d03070040c8402010705580d84108a5102c6044400070309010440d5901d00e502d2004d28172030041c20b94846468001d010401da4071507031120348102c240703208540d007600703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 725848174 1250 725846924 725846929
    0xb1e0a0e1f0905060109091a21010c092117030c0403060501080607120e07080f0d0801080f030d110f0c010b01123803060406140a05071e090b04091a 65
    0x89040f00c42c3c3c0d0100b0f088400400c103100048c4e0000018031900603180c00703078074414000101991a0902810301c00d244018900310000d00a120780c268104980c117000d00c42603e0203075410005000e001000041920a5420405002d5055519000801c1c3d03c0e44c0281d980c602490450709540083c0000c0c2c503030600e0030340085034501c6d0016144d4040c10303041e1144241d9501103007440780540400c0c0b86520203405220340005a50000f0000a200210100007428600c0c42c81140101981c00580c0100b00307039880401800c035071500101c111074080602c03010100302480c2080410314644240346c00c44c07100000014203c0d4281034190301c1070a0031502603070360100f13a0702c1c03c0f3384c105c003900c95000098510420391650b0380e0400c0b405a5050410791a0826245143d0b9801c8001034103180003202c081e42c09075140c08281c031190304403880013984500621005c11650500305c20040c90780b030b134940002d0041c402500294017007a001c1d0030044c00420040709400d03500c644600103640a041d01720000301520544122075001403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 725849424 1250 725848174 725848181
    0x30b09010f06290409020d090b0703061206050a1104080109030815030705060313020901080a0506011d0703090515013215250303021207030b1e0a0e1f09 67
    0x4400e5902c3c11800560903200c2c01000c0c10400300e6100507040100400203200a01d40041e0818800c078040001c0c514187c2e00349000c51400041c080c1081518001040c00b401d03544410140515402c0180024203a40c3d4a03111001031021807100c1403010404200010424070540100c5509440b80d9554000c0741c50700c17075240320300070740080405626130000c80041c0034a0400c5000b450b88940391000d46090900e07036801260031484c003170b0001c00203034100082c03c41c00d00034100491401443c005c4c035002412418400c6086409401400c41ca0401d5183c40c0c2a00c03d110081003990303001c0340724120700551035a581162100054240b0420301502e00e4803003c10030401c3c89010031526919028080d0400240020380258969000b401213092840d60004071401310400701660305205407003501d0040e0344081c003c1071200c210714014042800c01d818020415000c1d1620344003c00206044d049400c800c011480000707042120607000048495011070800030095500740e07030303e030300000440a0400140e88520520054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 725850674 1250 725849424 725849429
    0x1202030f120336010c14070b06120114150a06020a0c1401140a0801030215130b0a03020f030f07090503160e070309050f0109020111010c08060d050c0a030b09010f06 72
    0x2901001d1001800c106022403003650900b01c0f2100302c054400240720205244242415080340c203030356850071150655004014400303402e40d14200a81003e00980d2100c0080d6001480d07039000314050601824111402d4202c2c03e2400740d0170650001d90700d4a4900040c1c1c3e0001c13095018410710584400207130305070001c500304015070342110780c0c60446410490660b035146c0d14140c20038104030b05042d160210039000009000c141300c280c0d0310000c15500d103004101e0356004103120a00310305d00c200500011100340030509400c42d80c0c3c2c08240758440c038502d00103034024001c507000405d240d00b00000f080481c40d011902c15102e0310075602e0b200782e17880d01c51013850354403005007088042c5880c00d0b00e828001410301d4500035510030603624010801040c00e0b5039850520280901007640c6039115041c03c8115078000206405c401032200080180300702e058002410501d010780114003c410351040701d420700009020b030102d000c0001d86000c0c0c0141c0e1300d2504041c400404c589614883d46040d0701c0512002190042104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 725851924 1250 725850674 725850703
    0x12061107110a052431030611190f051b0604020901080a020907180b0f09041b0e010c060609050708010e090a57051207061d0405011202030f 61
    0x1151513080c0d41c0d6402c1c3e0110304203030104051510000c20f25080102c1c1400c1c8101c80c0c00340503005070318610f450800e850295240100410003404144841d0125901d40c1401c11000d240c0600100e07aa00c8050301e01d4445c800b180104031404449070004d1020003d80036005a1080d60511203136aa10045141c540690b0303030009502000050120b40801d1041a00d0800040c602c00c866061a41d074031103a00050307103d1010401c8128021039810014030385489181124003d980340300c0a607081410005042c41440442141882000442e080510180b0743c8550003030000b09c0030800c080e04001d10f01901c2498240b0440398626500800103240040c003280d42c00e0f0140e804540c15984400b2640124540c60b60807402400c2d2202d907031040301000101489004088200d00b042c104c5002036144041e00a00c541c1d001180a08158560301080c4c0100041a208444c51881c01d803215050f1004c1c0840261400c100d515401410b00d000030810350040e070401e070a8540308800300e8a200d000004059100d8001c0041400b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 725853174 1250 725851924 725851969
    0x5040305070219080a0c0501030510080d140904150e150d02010818060412020706030e0705040213030f030e09180c09070203120412081e0112061107110a05 68
    0x1001400c0412030b1182e00c180f207540c102061500d60144514180310103406562048819000f000b0550b010700c0703016004050140b030300310141d081200807a0f80b10015005201000000495402c06048540a440d880d180060051100b0725003410000c004201074084c00845a00300c1e00460381c108480c401180c0700500203400503d00e88260340054410540082c1018540c100390786d00301c1003540061110a21403403042a0310304841d12002402407809906801400525240200c00d044d61100001c60000312001141e02503540ca02480c560314680035140d000070724001c6425404405c242d08908052920101951313155050b40e40d825000000843d00c0d80469800e800520ba540f10909000401660143c0303240120392511101c16090fa444a1084078152820717045640c403414810392040a050b00811040c0e048100380c80716040c2c0c00140380c01845041c1c0d4070032504402d101040019000840c1a6482d010389d40c1e1541810b0901d08450400d240b4114424007a0352004585890b25001e40c80004000303c8500c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 725854424 1250 725853174 725853187
    0x21090b04030c0905060607060e0109030207060e1309080c100c0e0d0f0204110f0d02181f0509010212030702030a1e0c031211030405100509060c19120f060e010905040305 74
    0x200414000e8440741c6c102c3c1c820070884002c6400390007407500001d0214000244100709050080c01c100040d0468010062480e0250742207039203141081d46200d614000014916481c0d1410101030701c85c8000d850118040d0580398500315660b03500c8001c450070551a1500c040c0340820030441007124202c4010320304c1030722101d00343c058280341e40940d42d103144e0341450f0341c500300310b101038900319400c040920041d00780c00040072817030710702e5100c803c12018500b600c0d11301850820031548405020034010050400202140d801c1c056032003005501c4005840e0140c4d142d8900f001000251030b6404402403d01050311080b0344550380e2005500308002005640d075808045001380e03411260a540200300300f07202178541c450040502c54000046004520840040c14003480f500401402d40d440100707611100c1d040103040200003212401243c0c2e8603501a80120035840c070158040ea241580300c044810f06603e00403001c031100d4282d40c001010796107000440c40c3c50b42e80c0c030300b05a0305581c3c04842c01000a201070119 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 725855674 1250 725854424 725854439
    0x350f04030b070c02031c0e090c0301050d0318030f1e050c040c030207080a050a09080f0303060d05031b031b011b0e030325060c03050412110a21090b04030c 68
    0x20307400040502c2e1010308018103400007842c24a24200e00e030b11b107246607442c6c10070700c6e60000b041a03015042582e42c83c00c186020290004107010500c0748a014041906600e003c0511650f03045800c03e0407031006044090712410556000c00c1c0180003101c0c0d5802000ca41c030000c81740480d00c034a00d154000001d0129000080600c000351010401e0002032580a01c034000c005030f1b100b000703419148200d540e01c82c0c841500d034200800100007548030707030507980020100c050580300220850b640081c0988400d01000c85034509076146103e505481d80d440742e48144c09020b1240040010704039030504d150030741c0700d104e0070841542c00c850114603100d440030036850b00300c0340040c00740302c2c0268010310040549051581003242c42c0ca50050254030303480c2d0100c000d040001000550720130004202c401d4a805c022070700d481d80d5240795044001c559001484012401c44500c07540400a152140c0e50224006000e103a0625038490f225444080c1c40000c181c0000011402c0400c010503201140c0e00700340705ca00240d2601d40d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 725856924 1250 725855674 725855693
    0x311090619080a021813110d05072d0b0d0b0607062a0f0801211203050702070605090d02042403050c12210c120703020f060105040501050a090b0a03350f0403 69
    0x516030340000440e011030012902c148401c0c0010402c0700d0011107902f100d5018161020642211100040150301d01486640ba0840544400180ea0600040e8404509002411501803040b00400d0070b82031403030258000200070814103892002c108003010140d00550305a82c0c4c8248010b0050002c2c1c5090300401080c006042c1804141e00c26034280c2ca0030711650385030341310400320b00c200900119481e0000c1c44460b03a81000310b5001460799161032801d08540b003000801c5c00c0000040648900d44800c860721003002058441c1c4030003e010184065655903078035109464115654400b031140c811300400490201011810003103154000e10784812030b007841860300080c1d401482d40707000140702c0c0d08042450741c10503500030110980281c00420917002014142d0f07181400c140c000600440c00c1c9001004289c440610007003c0c0c0c0c140d2400400c0c4203d6880109000035040d90000e018402d07a8100e854840c42c0c2e00c1300d1504c107d03c24414000c1580200c2c5071050203071044001c1c12080900800c420804180c5070700c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 725858174 1250 725856924 725856953
    0xb0a05180c120702160f0e07120b120d12050105100c06140f01050301360224090a06020a050c0f0319081306090311090619080a021813 59
    0x41c1401d08085103a200301200324011121540540e200c0b400b80b1800f07102040c460401040c030b62800d4040706007001804c02d12550080c02100902614060420500e0030540141d0fa02c2d0b0005001c00030b100c810700095607560f2000c89144d1f408601320b500e10300b400d21080e00032a8140c2e0350151000342d55194841040326080030001e001c1e1030a076904d200007100c0c412a81d5403980600306030018411994106000c144c00c544540360354002000b44e842018415842035525150410008490702c035020301d0f540081403030502a60800c2c40304000c112090f081860019028101100040d505014019210041030b0303680c6039840c0740a4110740c007090300701046281905602d25052400340543d1202e005281d116100f1410340034049900007800308030780350b201031803c0d0840010300840c507142600740d18544400c50500c4420250a0050700d98070001000358076031085403900b00500c1c20030303d42606da90b2103100d51151108030049101c1c0d80b600010b01c05d08070603001004e001c0c10030518080c02c1c0c5c40090ba82d4440781510113 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 725859424 1250 725858174 725858191
    0x61406070c08060a0b1c030903032303180d080403020a1b09021c0b10080115020118120801090b01120b0102010f0f06210b04171c0207060b0a0518 64
    0x1510080703940307101400f11074040c034030034200400c0a201c20410080c40030854090502d0a8504141c43e902180c2d100490808a0381c140c01d149103607086821914040c1c0c0c40007245080751980010521113402c02080007407801000c01c205891030b0000005040356101d10569020f00180c0c0701c1d10034074002c12a062001c1040702c8484030000c0c2d02070b83c0d441032841641c10101e0780794007450150842c01500115801080140b601c115140310342d050860001608102d018002c1d1030900d0050041580402c1c001d5108103800880c82c1902000000c2d0b82c9414110b1030959004d0740e00207202d0380700018035544c89010f03054524805840b01c0041c02040f000a40c0246041040181150340701c8400c031241c4207940c4078071942c11620382c2c4040703030441c00c0034004011840080c00c2034500140c114503588c04112030445031038001d540024a04016012140d054500707004059555101a0345051103012514013036006040c154444c920a210590f03038641041850b01755449101e420051002c64503542d50074215000742e01c840300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 725860674 1250 725859424 725859443
    0x17010608070216060f030f06050a0b0903070314030a020d050a14070203150709080c030304050f060d0b0a09020d150f0501050c16030f02130c0f08061804050105011806140607 76
    0x41c24480d601001041e400303100803030310000c0044901c46d414040c0081c288511081401150f28060200b071201800d881013070031001010409210307a680900c0400020b60708000114107020f1a031080a07240c0d8801c107440303405480b803170b003d21114a0058040e20800405616854011031303110174a0302043c0c2c408d840c2243c0c14020000c00041c8402448683c600522190b6581004141489416445c103034085c403d00744290300034841002607681e120240d8010410a8400680b641000c02510700a01041c01c40140d018841e41c4000c2603940c80d65003c0c0540068404c4180701000307960000303070a4501c590041c2881200d40540922031540900c0041000c540c0540c100d500400c8108180c108030b620743d401c129040b41c5184008825072401004001c81e40311503000400c5841401c5401a0600d02e01d600c541081c4007141e00043c00b0743c0d503504e00ca40c40c846181c0300305c0c0c2c000d850145042c40c02070809014881140c15044544001d402d082d11803c419600c40a106203041d0040401708603450704071400c11902c00c01d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 725861924 1250 725860674 725860693
    0x50f12010e060a06180905100e03070b1906170c0907091e09060503070b071509050307140105070f12050a15090b0f150711130204030b010f06170106080702 68
    0x200b00951195030365050000c0e1050038490001604c07001c000f284000039041c030382d1080c0498404101c2c81200034104138002445420985450f0950080c110003405941190707040001ca001580241102107540c500b040109640300d1200c040a0000c4024034000b030b03881b072001455541003d01c2030790b801c601d00741040d50601ea696410030031003500030b426180c2410030094003000680110301442d0050300d0110041c0c0801d0741444960002406012400b8000c0310000980b110580c0660380103003912a085400d80e40d48a4103410b00d6441c452102881c2403ca610380000110400d2013418140341044035603070f8040f0359006015410000d40409051140c00320303030f01c02c2d01c0350002807803180c0d480c010940c00b203000c0350318501030f0204044803040d0598140900901000502000001002c40360251391044054120703803c2540840c4c828802c0329180c1009510010700803080c00003802c2114100c40714010078198060700c0d0f5904483d1184050080d00849060500501c08107000e044980d502000c42d2046501504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 725863174 1250 725861924 725861951
    0x309020406170a050607050a0c150204350106260c090420060f041e0e0a020711030a020901050904150501141207050603070c02040902060f0306090709050f1201 70
    0x984540302d041041e03000203403200c1040414040c083e8010000d04026042c014502c40c05042e0407003005004002440002ea00300c41d550440e810b03600031f0890070f18a030350120701030a031400c40c42744e03050b10390b10a8042404010030741c80014040d80088d0b815004085142403102140e094500714100c1d01210640501d040101d038036280c031640240b1890003155552a060704241802801184d00042240119820440ca1800d07140c80b10072181119810002c5100d016500c0d42c1c054102441904400c80b0504181c0c10b00c0f14851541d005481703601d001c1e0140319000c5020300b08140d41c40c0d0440c04025003003480d4000400051501500090348180149004031018200c20b0150044480907000b420040c440c03400140c8250404034503101c0d0611554008146a40c204000502c407400020211030070013502241480454407039820040090790302030002c2d0748031404800d107000d0503042160010b00590001d40014034003071281410f0b40171180c0180c64a640308414005000040d0402001c003e207544d00d0b2107003070b00f451 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 725864424 1250 725863174 725863199
    0x61812010e0a020108070e011b050f06010f050111190f02060c03070503030117030c070311060c070b09030105100308030c0304230a0c05040228020708030301420309020406 75
    0x219200c00140008442e1840090291030000c1c0015040141d11038401042da42c00104896582c51641d05071146e03040a85070040c41c03d0040c804140039406003c00008d110f04116000c0d1058507000d8035040e20131072002503003503501d480c11500708042d01c400300c030038502140b040c030611902203001a15441c603000242c0c081c0d07440c580c0500c104482cac2d6031001004000303680d81c0102d01d120b0240da038406545041c814085181d40c070b102501001c0c0c00c0201c040d40e08a256900c54003200d0901e400d41003541c2e401a61020010f19a800903003c06000b07508040010b01c007008102200c0081c2c0c0d50008407242036869296541441e0380000f8800c89034112220810070881c1e00e18410085605500c8005051281103442d01c03d044040e181d00840c0124010b2210441e0002c201c407a40651042c150058030f5441d084079000c9280001e65481600203020000000c5400c0c100c002120400e405c4640c0060180e5040520580542072000b45030005d0000354110400003a1107500100d1425000400c0450001d45440240160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 725865674 1250 725864424 725864441
    0x60914061003210806131d061504020c1e030d020c0a15020315011103090613060f0509010c060f090503040f030320070303050c120d02030603160506181201 68
    0xa2030840c80d000c104125502108503200c281d1161000d100c040101c0b80034004c94005400c552083c100d590080352a01c600741c2c006128041000340b401e500b010300d40100c5454030740940c1e1407419412a03400801d080e003818000c5541984030b10004004105050b00394540c0d0300ea8115030303015a40420401d4581e1034500f80040e241852007280506545049850302601c5081c41c9000d00d14802d0061042081f44404001520210542030803d41d02c4502814070560035886010055603101ca03000c241600540c41d6820480281c0302c5070744400300d4011207110309440d01c2c0a4002d1043c0002c14241321840001c00f03680000d02c034200d00c02404030302041c3c0f6503285411600720f1340183c52101c24030a010028180c6c4503d01205250000310b05000d01350b44480d40c036481d5645400003130144240001e01c06405401041106104850006142e0f1503c0184a07110080d500590301d8034482c1c03003045031031910344440584a000302e540c0181594649001001f181c4a0401c048015950050070050081b00e91282070140114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 725866924 1250 725865674 725865691
    0xa060e01030809010210060e0610090302042f12010315090f03050903121e030415020720061c05060d0501150512120307120b0d050d09060302090d06091406 68
    0x101c60000100082c40e00f86048020a240e6082c0707c0b04201c90125801d07c10342200e8280d035030301c0f003083c1c034120140c95294880d80025009850f018a140300c20f4941d16000070058030282400182810000c2c60080c503015030329020b0308045103903004000080ca5030421510881210780013003400d051507101c000f4081403051040c0c000c5100000d009103035240c00e00203030045403c0a2450703803c0a80821003d00f80015031b454049543c8000004641401142c540b950710003455064103556070144e51515800c01c0200c10ba180140e088483d58214151504600b501c015180d075103001c1e00900800401000545800392100d03400105403900d000103c1c1c02030142d0008810010f661340b590070301c0c01061103813180f0740420102180d0007070080001d01c13480c1c1d0001c0360707000301c8117151540203140043c030300d0001400c0a07404654858400ea140038100031010585003086003039601c40d4001035036211401e60a81c4541112190700c5400c01101100007441644100c5415020f039442860881012120518000003a0340414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 725868174 1250 725866924 725866927
    0xa0e070f02011b0c0807061d0c0a0b0a020a111201020d1509020403030903030c02220e010e2d150f01080c04090233040902070204051006170a060e010308 67
    0x140d0564090140355149202c900c4400c503012203081c001044020460310041c1600d000007466014030010341c010701003111054003102d50340060700000079502c0d0440a2030901940007840300280041140080e00d1a960040e009022190300c2569440c4140002103002c03a4070480340590320ba0440c00920262000b56419130001440b161544007900103420a90f1108017079500402040c40082d034420890300c200e0b641410181e807152900c7c400200e074580036401e40c2c04103003441d901c503210702e480d660408407594100c08000c00000c0b0401090741d4981d042003070458100311940040c8814810105c201c0e8070141c1880d400d8648a90030303014a000500c50a560082c0240c411000510000710140686803100a08840c00c0004540b03d60210740030303c181e949010f20025906c4003150551031501c2d42d090702040c410710440d0780c40351a04500e800075040020103a019919003400500340d00e1310342040c0300644001c3d4660403885002103081200e01000100190750007a220030000900240342800540690320408486 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 725869424 1250 725868174 725868197
    0x1c060e0c0a080c03040f12020f2a040515011103190306030b0705070b06040513020d0c140a08190201090e010f050117061020060f0109061208030c03060a0e07 69
    0x4080341806800f070411400200b0900001501201c1c0024080d580600c42c0c00000d03002200683c14520040c800c1c1000d0f0080300d12420326000c503412216014603950307442808031400300d410700048810490311041e125046543c00815074ac041e0108841401c0150112454908131200c200105003805c1080c0011a854400c01d004000f039008000358028000e10b0001d00f403015a442d18004207002401c40e600480e50350021800200b41c0d41d000b0b0580a4003d0810b03d907541003440c10036111b004c2441814120317148484910858540442d00c041100c01d0f000042a100e044080515201c0c006c80004905018100000088880c1c030490040e0007010198031000e440c52a11001401c9440c020f14a4040d54070100100b0007541c2e1020304041c40c401880c901030170786107030f42030010340301c910b02c080315501900c6580c04000311000d11035103045c180e8559a405100b15503581000500350340310044010b103459030500025030710003100c40245510400042c50034011a540b25240c01c1d00d0002501c0e19800140d074510700c0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 725870674 1250 725869424 725869427
    0x112060f09090b160c060518060420010e0a050f0612070306081228120f050a1404020303030403180e090109060b010809071a0c010c1e0c03051c060e0c0a 67
    0xf0750741c801041c0e166414205070000000700184040c0700002c0c5255a10004282d0170748103400c1e84201011403100f04c070110308003410101007609211000e50755280b800c4001441a5100781c00d06040901d014100480160400c42000ba5040460000341e41045051010312500e100d4000094003a4105e078400103029030815201c1400c00380e40103440c101c001010071034207103007006243c1c403928081801000c501c0c4031502e10300121820282400308c00003007424541020005010781d88080c4c014035900004014081594500402c408411100a54150428000200441d008800e800002c101681c41051102e03150812200d20040c103072400711217a0755034241a001c20600b880744843c0c420302404c0400302c84c50606100390b03a54030540581078520103c110103030200f0b04440c06071089080020000d103c00c8040c4500102103414060300700700c540750120100c043c240e001c0d2600c521103e8260b44c0c0c152034050609a10100b2203810802d840f0324542c0c42100154669000f200ca07030080c6410a8242e40da04e450890 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 725871924 1250 725870674 725870693
    0x50d11210f0a02070b060904061104060e01020c030a03140a0509030102041203030b030c03070b090402090306150a140a1208070530040e060904141f11090f0112060f0909 74
    0x42c0d6404900c10011000450030035408190b01c404100d90000340d554861030040c0182c52000c81c3c80703210002c0400c001c140150002d4103042d849a0a0742102c000850f01020544d0300c440c01040640803032710416030011003510a6005001c0781e013940c00d0a81c5807260807804242283e101c0e6001c504c0c1600c2c0140d04008040c0d05000f08090031400720020000322043c0d0b80000e0303c5111318881c88010707140000703081900c1e44513601610940071006050310600e1800084082c008194404920310070100742001040c0d030038800d50305100104026111803110b5041c070404400f0202e43c144191a10001402603c002510400055890328036050b644502412004100034000325000464480301d00c043c0401d024105000b41101d40c806011505480d158071a4141440101072650780070f00140116408112441541503c4801048082004100c1420000c00c914070314001c1e050010350010300c544213070311150320031001e50304000041e103800204c60303640d0341041c3c004241d0740e401064010b88a0300030100380080d052 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 725873174 1250 725871924 725871931
    0xc030c1e06021f05070c1406010302180403020c0d0f2a1508150a1502010221070c060f18060b03060f042105040909080d0501060906050d11210f 63
    0x4006180004031000040c8000e01c0780d040c8090740d50307400501c01600c43c58850480d0340e00038802c4847c030480d105819072100b60074001a402200507203120070407445c640c0c0825209a40550241200c207181404001203240d0554059408040507802d0001065410500f02d03504104000d202800c0c0d80d040c081103a288885601c0000c1d1100701c28010107409401c850031071783c481e00c100045401d1040e818001102150709410506d26040c4140626020640560052071041c0d1204180d444281d81c0d61014005d43d98120b44070000220400c0c503e60015065421a442e404000640070900442e03c07030700c4a160b15450001030701c81c4d648a154681242c142801400d03004003c050b10301c2c030140b4081d100c11700226100c00040000d40507020175035440521401c00d17200035200e48241405150148d06258280f50424940c2115892422000154090080d14448111001629128203108400881c00018824002040790540c4200500e90903604040b07289284070b910440511140e0401d010001c241c0031004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 725874424 1250 725873174 725873177
    0x60708090303010b0f0906070b040302281a0a0f050c071505220c05060a0809191112070e09030c0d141b0a1a061003180f0c030c1e06 58
    0x2000107026041084d822500e1040d1166001a41d51642c1030100f00c140c425060301802000f5604140010181d002c031308010300324000d065090030030801500070a03203800d17400001068129000602c8040d100c0c1c1403001544a0001c0e40700048003011010b02c0815a4401c4484180125001031200e0400006050f07440c0e1a00402c0001c00c01e41c540b0400001c035034000a5843d4081581c1c0250400c1008024580c10010300b40181103540c4904210700080c1c1880000d071191040c4e4041c440c1441a1003c10031590907055400000e4a4926a2034509000000c41c002080000502500d4004100004c4a01003c6d00a41c01d9100850f81e40c03524048190912080103202010001c0c020103450710b04510000382d54080003041811011500c0b4104a146000080200180741c1403001510320001c918008226103d084141c43c2d8108039002007500f102202d9406219512400c1d00309000b601042208845c00c0a191103140c4000c4c2940c0c59803541c2c900a4240d82c003c0d20261906c4c000c00b050782c820040d200700100f445 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 725875674 1250 725874424 725874427
    0x2060610180f080c15030f060f03010b09040803040b06030f0a02060a0512070905040507050702090c0c01020705030c01150b2a07050d0b060a0f030b01060e0117090607080903 76
    0x550004403500c14440c80c00c001c01c524080d0701000070756080001001002003180490315660b8824906495455007022548150086a10010070604a03411644615440010405ca0b95607200400c103041c54000342d0360350150b50f40c1140c0015511142c2060340240e008a090946a1a03e0f15044001220047c8100e000c1e400003048482d03419000100b504d4025070440e070940d11208828001c81300e07400780754924200a00300b5410310031001e0f0460842020340d441907c0c240003541c0d07a83e038256514440e01c24000d411590440002d07002c5604840139110b02c036180c0c0000b62418229481d40c5285030010b03610345e101341c1d543d411982410106805483c00170061103100a0a18040c4008043c02004a291ba111082c0c05c0040c0800383c1c0505010b045d002d40030040c400088014a030401c3c03018584200c90490080c81501e8010811a410455070012a03601801311101a801c050048944107111044a4140b1000c65a01584500c05403281e511809803a4001c0c0000d1074004001403e03c2000b0749070311081e800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 725876924 1250 725875674 725875681
    0x90b0604060b0d0b011205250503060102030d0f020408010204032009010e190b1c420204030611030405010c0c02010207120203071a03010812040e0f0403050d060311100206 75
    0x100902620b5078450b10f8000001e0000c85100144d584c50207420641510b20b00c5c000810a103410030191141d041008014150345128401c07000b81c816101c150351031405a4400e12880c0ca40030f269400000708030710401e20150410340d540c8050303400e81e08660070850f505200f40b8080344520401d804072401100045804140c41c6d40b4100a441c1043c1015001c1e00003030202040c0083c090a0607005101e4250000d00000381c40340700312070441c14102c000c00086411805000800c6c050501026803c025100c5240d1450003001e11135a0142c0d185405100000100b0b400b03000000108445108903c12081c02c400c2040c0c1d40e1915281c2903003115440c0e022142030200c0b03181540c000d41d03400112101921074400202c800400d050001138580080c070f034003018258600e000c800d1450381203c006141220991030843e981134002c1e28401d946070090f40299400c2064901c005008495003212194105e400303410171a00d441d200c504ca40c1c0a403140c1da00295040780d901400c8a03a14107086146081c201424070241c1841d04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 725878174 1250 725876924 725876939
    0xa02010204052407060e0a0b0103060f0b04110405040203091509010605011116090507020307080c010605100f050703030b01050706020a0e09010617040209040206130602070509070908300a0201090b060406 89
    0xd1598081d00c034070796078002500101820032a4001f1260440d0814210750f0b520b15103200507082c12104868148e050031000c01c05c50403d40200c10005114200150606080900340002500010020040f51080489030000c20b540001a1030140e000c9100114205003010005400303040705420040096000c40100001000c46481c014156003007404003003240d40380c154040703143d805003440152410b400080c004154000c154404421248161126129002c2c03165003503c4c0d4030040d844d00c00124200300314603000240f01780c0c000524001c0505100e410711825890b60803c83e000192000003241000c814a4901d150840c0c015004011520344401440900012007840796409000240140c0340480420215961401900c20400d07040603400710740c03551000025a00c44003842014045c0c20540007003606a4881c620340d606980d1000c00414540c400320384204c0742d00100016106104c0604a0440c0020690344001c0942044a42c00882c40c0078444c207000d400403c010300260300c203d2801c1c00810104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 725879424 1250 725878174 725878177
    0x10303180510030c0210020f180303190315030803040b091b03030a0e0a03170a0905030307030504050919060b120c0a080601050d020f0a0f02060609101404110a020102040524 76
    0x180d990300e001300c1c5070452124141d00d000094202010183d0020a5144c81c41020001902100100324160741340404800c05140d03d0b849240d0264021800002c2c2c40c00103280281c00246424419070003a10b289680c0303813100f4800ea001607504035030040306102445402c0c46c00f0042402c0102155000c0f10031400c041000940e644524002c00060051401e0468015036802c60203400450f089454010340762002c0590900960241c490708000c9820703000007013101e0800009a43c11154591260362030603041000300706400c4801040207034541868214009621035138041c1200500200d62401d0300e030b203a00181d4041c4a14020004881c0702c00621a150009900c07915080d0054000e0901c90f9a9007a070700801030180c810102c0e142d000e40c100040081e50a41d020004c4009100d00b42d0075100b90b51140d0040005056007600c4000902451087c140300c88116040610034102d4028000122405618a039110070b80082c03030700d000540d41c007003000c02807401d24800361958460580c511a240002407142450b06 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 725880674 1250 725879424 725879449
    0x8030a1542050c070b041802030a090f05101a091b1b0303010303030c0c150b031f0605010e01021507051602040212100801060e040b0915040503030103031805 69
    0x40d9005200d00008490100c50034190800000c50903107021041290040c0056115518a00301ca100e0352000007685143c02d0252001e40f0449010074481c141a642c080740a0b41000e441c20321001d81d204410000100d694601d603030070510840141c04008905030660044900512282c50351140f0324020128550300d07442103a5011503541c034814004101d40012081c9030143c2200c00071840181c0501c0c40104100202130340c1200e200c1d6400307014000d4200001c403403e441c9101c004102c000011791203001d58100b074000e5002141c0c05012640c0c0800740242207040c2403d18148054080c0c0e41c1c480038011540d10000700103240100780010907601070300d80e05401400e0801030004041113800f10f43c254000b01e9448a058900e50000c0c8255140c8682040c820107005041d1810141440d14000025030138106001e410300302d0f10b49610302101039541d07481310742806000502144080c00b4092402030011041135100e409280540001d6841e5030540c03030040c2160306941d00b215400e50b00c9401c10803050380c0740e0250140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 725881924 1250 725880674 725880719
    0x11202030403090b04030b0a0b01031e091113060918150e03040302090a050f010657050c0108010f03153c0903080c0715050408030a15 59
    0x240d030355660800300c64070007258010b044014400280002072050040e280e9000d00c2c084641042410b24160040d0216035040c000b01c0000c0c40d181e54582d0b4948200c0d8052400640102416040560004005540784080300711015a0a80d03803170702030120521900c605d0340012090301c1e03c00e61300c000380d071126244024003602e0228810b44400c198603c03100c0c1403056070000c50780689005250304101076510003400e021120240400405000014024801c0100d1280000503040000d013048401c1d066240d030003e0107080d212442101d0341c070002c014803110004045421204d400000c00c80c060b02e0054102540040028108206400103020400b13200c0c6040c0c080740d0748410000107804285203408090200603034107a00e11109107800c041403084828481d04072100c0e0010b80e58920898070003010803500040e01c0580001da6200009541c1441f0354014524580100c15003c49014001c3e8980280c500486040b1405c031008414000c49a402e0f001e402c1084020702d000c2202c4030701340b001002c2100d405190050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 725883174 1250 725881924 725881927
    0x21150e0a111905160b1e010b03190b0d12020706110631060e0d140d0c0c060906020901080c03060f01031d07140102120313023c1302040302011202 64
    0xd048a0107001140c9420309900d415501070385090400d2034540c0c0048500302c0920b0760020712081c1105080d031406d4181d039010080d036419510340c803880c00d2060145010001c4410340e503c0451410fa5101a201071045104171100c1d050030840303840090800072541e1001051206414109010200128406511006030b0601c40f10a100b25456042c5002c4052040991205103004005c01d2011503040074440e03100c2202150500d00455000b202d15040f4500e44d07000912090081c00000b403003036040a0347c03c110754a0300c0152500c0d55121b038030846142c070b07200311042980001c8103a81d07544c004000950201e5941c05080c218900070022503c000d840f2044a41090b40e03c0240b00d1450302c4d1604001c10a0f105a02201c03181900e40d900c1c4c0f07903204003440005001d849002810154020f91504881c41011450b42c8a12501c0c00790b42403000d203504061551a841240542c20455030b483c04c1d0b840060407500d14034210a40075408107100001c400cd0112110f9030740100414405030b6089a00394905d02c15041005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 725884424 1250 725883174 725883217
    0x2e020307091d01320d0c0f0b090a090c020606040902060c0706050c120903150a0204090218040f052403100504080a03180209040321150e0a11 62
    0x200d44600d61600404903400300700850404650080c084507041c2d60400408039204008421000c00b04c1901c001a8841c48007111620040c50a21034040120548a400068565510342020f400c07100d1071900140f44801021503140c03001c7c0b405051000040c100c20100301f03c2d4610101000f0b4460b0b1000b82458012a02c4142d20403c42d12142d0440c1c580120040503a255140c88130700050041d485071a0141d85445200b020054883e40c010071510207440007402048540c4240b864040c82910040140f030200c0d40c00c0c072002804007004e00041c04880c0e00005d8102802c881641080304480c2890801010549804100a1109001000100c0002100780381d40e4070564401c00091a0003800403400e1112810700040c8420001000080e00c1e1550103030728180984040060140321001e107240c4081d502424010101c0c001c030f8099003400214030541100001c061b4411035445007960352501241801d51080300c0d0400130241c01c220b00390341001c1e00400c00d11810500c42c2c19a400e6026041500300d80b000386691300b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 725885674 1250 725884424 725884427
    0x3190f0e0108062d04061203021014180a0f0605060108070207081915090c05120a050a0228031115040806011a37020c030d080601030b0a03050a052e020307 68
    0x300d18850700010018044651519482c2a5001f064107044000d44a0b9954140d003210b1079009504003e0030a100342090740d0340c0d10707408211021019140f950940a014041000b0581c050195401c6601407040445c0c60300b40350b0300040c40c98400402c04401c640062805000c1e0b0038010070a50240b112404200180144070f0901c1100001c070103020500451030030050f40d0412106100e100c0c11950100c80100075001041c6200c2e8403000d0b640f0b001003054111641d408014a0b020368440c0e01c001007448040c10040c024984410301148580040d43c81d40e1099a0004c850300d000c0407600300c05910014107034102458140456901d0741d0601420f03a0700c1c0c844031049480414003006403405865161130343c2d1640400c0503154011224008844010081244c02c014080c0e030001131800c50f140c0020b0001d0030f401a403001c0895003804050007090400d5200c1380142002d9449000c80c00146008202400c101001ea1401d249480140c00103030580f05420007a0724402840c035001c0105038004410056500e9039044030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 725886924 1250 725885674 725885749
    0x10902121c180e09010c08131e150c0c110423070c1209060905040b0319111e030c040c02030307080a0b1e0f0411091203190f0e010806 59
    0x140701c2c0c503040041009132000054000103502d5403140c40c2d030748160b15802c0320541400566a0080c000018200d0000d020142000d10846181e0080d0600c10008000c03134007060030b0301d20310402800041c1c0181140c0040c80340d107551b035140d01041100c04001312203015854803107480146400b041d1148480e40080d2800707000c0c030000e03c0d030254410080300e034140343c190300685098440d018a10024480765004510b0b403e080c400c958040000500070f00c507044682a001e400b04820103400c80f01070205500c064000d88541456580c00301141d1818414000803200b454035151500510900c15424440c2103a03106801101300c9401040501c3c000b440740e6200044400500202240550081d5480b50b40d1039420b0f00f814042c2d0341404007102e009070420707410010407050b650800268542d03402d04119011851401f0111010b01c0110b1b80d00b501c0c24080d0400d0035080c0701d9211000e100c08500510024045594021154203010703109081140541c00c3c22400300d4500000d006221900e07014201c0e061102c0001e011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 725888174 1250 725886924 725886929
    0xd0306080a230f0a0b0a110306040c02010f06060f08091506090907080d0c0201110c150a09090507030213090501031203020a02010b100f02010605060c0a02010f050f0c010902121c18 79
    0x40c00c69103c001c0b9800550b0f41c0f0001024165043e07851040442e079003441c0742c05044009101416007500395294001040028040e80500409541d82da002e0030714101614000c120050000380c9a80c500d003420301d07070050241c003c002c0408140f070b0171000c018548180c000b848030350401d005441d4200e00d6a61101e200e444d00d2202d4128800c1881000403c40801b40d000f07200d040307841d20030707030751a0040114a14810b030394040d050003c66000c0111001c6003500303120741000c0c0a40031541e150441c07178207076070b0610f00040740c4003940c281000a4001501e07901da070280e5901c030001440038800030045ca600d59180d80340400b5100741d17142c007015000102d416050341300350482e0004500062440e00c6d004124407003c0d04440d40b1400007005942841c00010b6185040800c0c0d443d500e1b2070f4009044c01c2d501d19401196190000070b01d100c14890b062120440107000314010702040f500302400061040c055004000d030348503a140700c0c1030705a03028a80e070b07800303c80c2d40c04422a00394809082c00c0103403a18000b9603040c03920b11074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 725889424 1250 725888174 725888243
    0xa03052203050d031b080114060d1530060209060d0e060a0b0a060c0f080c06010305010603030816050d1a1522120318090207050f0d0306080a 62
    0x660044144500032503690200003d9450400c08a1540000c18040017030174401070780402c030f00304010090030700e044661002c11400104014a000c1c2090309100c11a000c2d0b2601825106032a481480220030f0f81202086904000c1d00b40d8030158900c0d0000b8907100d0700c21a00424054000c100c25103aa1a8038061b14240e05403440107220ba0100c1701e210039550350040b1105806a414880000a1400c109030310303405490043da0303655142801d94a4040d00308002540c02c60760b040c01000250b5203604207104084c0698801d00001c107050f03107141001800510054101448558410107907a04503401078200d50450781d040901044c0c18850103079022141c210141c0e915041200c0e001c0c0e003901292904014407036030f81a10001c0c1850450040940c50045040c0100b05c4e00790081425400400d0103030668086290000142e83c20031074482414030280e801c0b2160403904c0354080e5080d032182c401c050180c00c0c0301c0700071885c00704a018074003002159911015440904800c400c0283c05e601c01440c071542101080c080c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 725890674 1250 725889424 725889487
    0x5010215370b1e060a03180c0e04150501050105040504330e1003110d050f1f0516050d0c0203040b04080d080c1215010216270b030a0305 60
    0x140700c101d50140c00b80160582c4500c499554000810b215200421480d11000c0e00c0c0b18180070001380180e005016030080c0a072540c80100d815000940e0295170040a021810010035850800c0d103000022100080706108103e41008014491030741c1c004207031411154201c80100e040c803660310720000e001c180d884402c0ca0000e80048985031a100440d010422a040c0400c5001180d540480032104107695000080040074419080075052402100c074010b024010019982c02c06113029015260199025441004038418400250b10400724031515512001d00200c04d0324024610800a00d80e21802842d62882c5035201013082d03215208000765405807180500c06580d441d250101541d4500c02800e148000403064000a203101c4440340507500941000c040d003c40e81d0701c0e25a1a0380c1c2031100b500d101030441c484c4003a0104104122441c5000401c0c0d0781c95003154040311008405413050100d06a021003038109018200c0607100051400c40d9550545010f0740c5440006d80208000c2100c42c410a00d01640c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 725891924 1250 725890674 725890771
    0x1302071709100908060408030c1606050406050610091707080f010b0306010b0a080c070618030807030506010f23040503070303030606021b0603181212090705010215 72
    0x1120390003040c40c04000c80e80280c0c64020500200d0f00300c01c242c05540d00c990400d8000c41e001035100006140c120b02d01c14601801c113000100c00f110725018542c07081c0e03500c980f18800c0c0018000706108050300910b0640d04007060b90b007140c10251400355540b0035a84900c02d1300654114071601400480c000d0720043c1c05032070b4115101c100b468064101002014400e000750b01c000070b0f25000100480320040c9444d21418000e940740c4986105c190000e01c015151a911018403406061024810500384c40c82030f100d10038503003000540201101d100906040c144500c404042c091036400c8078012015001c50004042201c00c9a5000d14042c011640101c0d003501c140303c4080105500342c2c00c080243c800c1c03030382180c410862441d81603400f1240d04401d41c0d00000104007050b45408400504000514520100c440b40c0007020766124880c1d00907100280140c1d994414001110800d11041d002814244003c1c44002d10080446a41c0c010142c04159681c00151041e241c202d0f0010102c54000184c80c221030440e00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 725893174 1250 725891924 725891963
    0x703051806090316080f0c22020910110c06030915041a040c0602010b060f0f03070c14011e051512100c0504060e011d0409170c0705031204050f130207 66
    0x4070501501c0010f0003021030328800180b0002c0c10244501f0010700e800d1a02900c16654804001012181c007802c5400b004844823640754109580c08100040e610140720922621032242800781e004030083c810041082403240703c040000c2c254044061400e002c5405440d245007002c8014007080c055101c01a0300c4003040180700080548104540c62a0000e000a8194030208911441400d054ad14a4841840782c8041d114000019503031040300c4d400c01140607041c903100c161510420042d005c200743e44510401c0000494039425410300c0714800c1051180c3e0514030845085500fa007a40f181c01896850342590745c041c01008504060076111908009102c8950b0300188154054022030300030480d5003800302c078035512401104540f1100c0d0001c006c8480c540c9000c0101402d5408410350303080790440c4070718050202c0300b4018500c851800e4001c00c00145004207042c1400449100801c541000344001c001030f4680300d25040c44c4141c1250b03810040312026240ac4000e000b02d030806442c41c243c03010000b070400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 725894424 1250 725893174 725893213
    0x20705071d0702070b0d02070615260601120215071a040308070c0b04060c030603020303220506070b041203021902011d0f031b010617060103030e0607030518060903 72
    0x109070504116559120030099940f0561031080010644040004582c1240164040d2410f00d11450700451102e56605004800715042e4015403690709101d1043c0c83c40e0201c2c02c1c1c80c2c0b907c88071030001030207042d80340c04100c0c01903029104010303019100a901c20f5504c5000e11003103c50483d0301036042c00301044103041c1c90444040854088000c00c40410120309000d0189034400b61082d8000320301501665960758810103003d0041d081d4041c113032582e03004001640c0074000b401c094080f0084070402c1c03124220250a00c0545540054041e0004000f4500032a240103140c540c440e411841c0d086010407119401c030001d100300c05400c545200070241a4031059810b4214102c2030a01d4200080c02c00e03d085812500c1d60402d5204480306e6108120544011075082c2c01c1c05a200601c200001c6e03007550784c0000381001246503010448076040b0b000140201030300009281c0c6400402e0b540181031480035500501548140c05c00c400c07928401580701c1450b9507603c0204d640160300601900c0007104038551040b0380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 725895674 1250 725894424 725894459
    0x501091205091009050d030f18031b092a0203120c03090601051005040306110f03010803031b0a1d0d0213020d0e03092412010b190207052202070507 65
    0x1400304503565003940c074803620581c0e041c2c0308004d00345001d250081e07505a44202315500c016051007201c8510b03900b400701c01a0003c00850180c141e500b500c4550517040100410160003e6403035a140c141c14070f190100c1009041028005284210b40d503040d41038040e0300e14040c480640c21a41700c0c440802c1b4540c940f890140d801020120101e5483d03980321000c001d0f6201c1c0107920750002483c01d110401c08603209070045200010741104641c40c0028a40280c00d03158400d80001845520010038000c03c0e030003401d50b1110201c02d0f07000d0b0b1400c01c0800680207001098945c8001c1400781010600c117000e6071030080e540660359005100c220ba10300c90408c4280a1f401a181c0c0008191501ca4101c51059001c800c69050445c0100b200540900c81d9020000852400740c1b01c40d040b13001444000801d058424106010b00900d1034880d441e4042c81c001d250369a11404a910219084030700100300c035440c1c00005d12a40075401300281c0c3c1e200c2884000000a00aa00d4040c120b4841e6100c0069a0907a144000300c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 725896924 1250 725895674 725895679
    0xc06020105060405150f0a050d06091a011a030a1d010510050108011a1e07240911060903030f07080d06050a08070e060a03020409030818010b0a12050109120509 70
    0x810b640e6101040b0840d10111640312035519180e5009902d40380203004600c0f82c801c0140500055900c03a400b04000100d00c1c04111201ca9032540700400344454412042102c200c0c01860210542c10082010840342243c00e2481c60300b40040007041100700740f0b4112820070980f440c0000b0600c600c8252603806054140d81c1c07050a6100c591002c0303001d500c034000c4181a90b00030021030405a0002e01c0c0d643c6640d00220030744500700700280507040721292032002000960300500c042801c81c810760180b40d42000360602200c8a15140c1741881b800194005089074004800302c0b00340fa00c6a10a10120f8214400e05421580c0c007440021580204070290b8098003080c03030303074020030041c03507488400340704040126001d500d0166001c41c01c200242107580401301c5e4042d0018040f940155902d03800b15099404008048000c0f1340d160b82005500b0048100d112641d448560003481410000d4010410041d039500410414500b5020340d031007072100940000280c1075021215a403208a6188010815041070348540d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 725898174 1250 725896924 725896931
    0x40b09042d051e0312040b040c120f0f030207170102030a0501060e03030f13030c241d01080603030f03070819152105070909020306101a0d0e03070c060201 68
    0x140d0307040100c408001e41540c04002850b10200244240d4003605114aa0308428881042550140c4501c2441c0c103004620503000fa0320035040c9842e101c1c0074180ba42c5c00a02c92444500b5000780402c0c00400c00e0010720f9005080c010000403030f41022030500c5074641122404084410b1a030300b4a03d0154003e502c6412030b2001040702e644c8941088508000000710645d160344180840c5142003070038402000c000007489130404441b81d0303075a034000c89001594403054541d080708410012100742218540607501151508001182444101e005481c40240c3c03801d04114040b030002754151010012207480e4600c0b0745540380c6902c0c140074000c0c6004c070212909018a10b280c0d0347c841c0c80e500540650b000c40000441345d0b90f0100e041000302d821602c0020540d411209031464600d002c281c01741708072805820201c00216091a882c014540380800c080e10008501c0d040400801401c06481e1541c80c80e05194001c0c0b903030310014900d11102521604030b400400d40800a04107040003820040001110420340003070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 725899280 1106 725898174 725898233
    0x7230d1d1509040c30090605090703032d05030402041e0b0f0f1f0c0c0e0a0c0216050f0102010e030f21070c0f02040b0904 54
    0x10840001c0000380c903489070505000b4042d00c0c0815040107010075800700c5c80c441110340c01261060511054100340d05500d9a26009481e1080d00300358140701908040d034134162202020711088000c103081a0300d0900000300345008080300074809440b00c443c00940d40301070310745901c007c004a81c0700d03650360301a4190481c22010900044c810500000d4011303083c0041c40f004121001d0740d980b02e030409440b84a42661850203c0654207201000d401e4841c404450a4a5251000c04010086e00c11914003061020340048417a11911003418103002030440c11900344c1c2c031041c03c6d00240f00c134120103000600080c02c1ca554140301401042c400018801700041e095800e6400c100044114160f000400c1014031500c4110a2440401c800040d401800c008001512582443c28000c2040607481019001d6580eaa80300c50740000010340341000e2071901e80781000c80b0351444141c01042e0f04948594 = true := by decide +kernel

theorem cover : BRFrame.Cov 725719424 725899280 := by
  have h0 := BRFrame.cov_init 725719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 725719424 ≤ n) (h2 : n < 725899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
