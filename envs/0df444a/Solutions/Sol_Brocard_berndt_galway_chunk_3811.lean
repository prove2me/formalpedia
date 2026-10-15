-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3811
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:45:15.668382+00:00
-- url     : https://prove2.me/submissions/23bb7a0d-1809-4614-82ed-e5f3f5a27c00

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 685251798 ≤ n < 685431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 685253048 1250 685251798 685251823
    0x1b0d140705360f0a030b04080d20030105010c0c0807120201020c0a1a03250f0f0824040f0204030f02010206012103030b0f0301090c170f0d031e0c020a14 67
    0xb004a075803442840040308524940c2c80d00070f0240c80c1c0100c0410756a42d9294441c511650010b0341d6103082d500c0f2142940c0000c05041203075001401042041010320301600e06480007840c00e0704030121207007000c2041903400c0d882404580500c01001c074421001402001d035540c000e808036030b6601040814803442c90840c0c0308555043c4403600c0c2c002c030016900b00003141c0104100600801ca01d0452481095022002003407001184c5e00801249800c0d4004410300560360013820400124a03082c58901d203030041600f0395030551140764440c481030780c2e035981c4400788491304503504645880d21307031801c440740c0600c119059002d0700c83c00c03000080c090f0703403409186115900c400400485442c1c50741c0c00d50180001e440710310b6002c190030001c88550384091155801140c0510983d00d22645007000b1810b0500000c20150301d550082d500d00301d40c4400005456800808525002a5040c001c0300c0e03603a0301c100311070110a2100e007000d44a442c2c0315400901c0c00c120600032141e0314035031401c0ca080607503a1604100b60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 685254298 1250 685253048 685253137
    0x20a0b0c09092a310801020d0b040f05091b0a3c0335070606090e010905070510050415080604050703022d09040e01050414061b0d140705 60
    0x36a04000303004606407084c2a03041d090114090307114000c190070380e0020010016010780e5101180028546030060f00d15898200360108207508003260081e40700c403220070050b0103800d0402e8062031980c8075035060300018403840d8102c0810a042028107285451f1190108a41440c081d04004d02221220103030310850f9449414103110100701c012196051910200c80e1400c500c158a01d01002135401000f0110184980f00000383d09082041e1041103030486500007840340e16000c0311100140000400c2c0b4156a411111465100c2100f00212950312071078010000c002141c0009900306a0080d1100707008600450f004d0256584010046040340240707510b100c2d620b62000d0038400d0032450580ea100c004e18203c000c40c0d1a0140680101d070940301440c1840c00329070742d0b40c000c12040c01318051038170030040c01c4000030304030500700324a00d5200b88881c50054600680e00140b030b2802d0801c90fa2240307040c04004086501c8516000102030101c0e00205201c1000300203503280f00f90351551000c0c0001d40070f81100c00303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 685255548 1250 685254298 685254337
    0xc0e09070c05120406030f0e071202040b0d12050408010606050307080c1315020a061404080405091302090f01080d0f0f0e03010225031d01020a0b0c09092a 68
    0x2203402040d1110240d405000d4800c004000c83c401c1001400680780035180450b04030790301001c18040740d400e01c00c88801a04000d02c00e0100001c040310307040400750100c50201d2010b400700c00040403107a080740000c0021141c4149185010382010142045a2021000304406a5240d005640c03c1c40200d81c0b04d40086d05801c0000d225032640806440707030800c0051880c10700c903210314000010200070101000961310032a020700400c082e0b400750782c100c90340d45118070740c25080ca661030034894081c03401428400e400c1c000003c1d501c0800210f40e0f0740c03180d4004000c0d07441810202060680d8a0080c002c40c0703c00d004044840051a009501a0070f4008035075440300b0149100c030f0400c0b98488842002154103540802040c210b1041b03031813008011880170050a840984640741c041c104414001d1012201e0454100c00106a80c0209078404001d401c03010213950b0740c1e91120f41069a20405c980c0f10740c403100a0b000c1c441d46040ca40c0356240205100c080300285000e00240a0000780aa003904915400700a0f6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 685256798 1250 685255548 685255561
    0xa060c12050c0a231209310f021207020316020f010203040e010807080607020d0203040623070303092a140301113402062d04090e010c0e09 61
    0x400426004030707003074192180c0340c0140e541c1310494900351042c5550f420310805541e84040081c451640e07107102032104136191a00344400300e03481490110104050003114200340d541c1e42d000b260300801d511006041044400406040d150083d00450746070352071501e04400089815000004a610142c6080030f812081c4450381d003004248401204900c0c1140002c0c0300006500c0700400189005e00010340241050b41e05000d042841c00c5001401c2d5404c6500c003400da06089500403048500ba145140703850078640b10b500410b01090100026240814800010740e40c00340358bc03640c8a94030640c0b082003000141c0e1802f031503208000c86001c0d920058042d03100000c025155915040d489403400240c000300b003400c802004400160042c80c581141106407260a1414452120003032211f41c0c050690045280080d4010500c43c4c024810702c0240e01c0390b0401c1070340b510b156000e04500e0740d03401e034a0482c0d66a6215030784100a4040c41203209050f60034000b00d4801c00b4064008008e100001070510002030f51140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 685258048 1250 685256798 685256807
    0x3020c0a0612110d09080408011410090c051605060604050a20030402040f0204030b150603071704020a0e0c091e01020303160509030d05030403080a050f070302070804090203150a060c12 81
    0x201c000880f00b01080501e00300441c50050f40007050158403a6138a451034144d000d07003910810b40c54607042038003807002c000c114280b400c40041a15080d400006200c40022400d40302c51107074440310041110451104e108000b40003407500d1203020159030500003616428407140903210154040042c0c85140a148028941401d025662150000300041424a8010b03085022640300c0d80040d02d4400408007040409801035480700c0c40300d02c0540b0454030314585108010302452204044616160a24000c94195501c020103c4044d00700b0722903aa40030f050103000e400d05580144862802016656420241803241c2010b4403102c05040c2c02440c6150b035041c1c00080c5c0000e41d010070b03105010061110700c8094a0802100e00c0001d01921144e17601c0c1003a00b40a414014000c1100b02e0640c11700c0108404017528101c80c07500408681005600c0b00c4a0340b81034000f600032034000c0501c26101100300006000c4186d0100180304007130300c01034030f41500c0e80800c580c440c1e50350b00054a0740c1c0721042d069403190b21a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 685259298 1250 685258048 685258061
    0x1b100b24040b03040c030b16020613050a050609030d0627051f030b010e2202010e0102030706140726010b0f120f060a050109060909021317030703020c0a0612 69
    0x521103000c1c034141e140c007440c041d070340c0040d07900381c91045443c1400c4c000c01c9030804100703420589030740b1309010508507080c0003917940c00010007810916503e002d854007001070411001d42d105921100390b03511403600030b00c2c160303481c0c010050040405090410001740ba01281803002d000c02a402c50078004241c2444145018010150403543e030081068155200d020031a006000a544100d005000c00d514160340071068240c060401d06065100340300c0d020820648138091a06076074282041070740c038040240103038114003070508050103103401d120031000d10311100c0c10b000c2c0c4a002c5039255030b440d82140001d2070401c00c51481041040281d0b0703070018040300b0016005005d440c0d4404510342e2400709000c00c140f0179410142c03254611150800184861807500e0501007001c4c0c102841c00f0080d03245001401000c1132807911801059980c0010b140840c204040d107d04040d20308201406004000741c600310b5600d500039403054005000b14030f10307902c2510b4400c01c01000c69400c1c1d0307109840d064244002c00c00030b102 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 685260548 1250 685259298 685259359
    0x601090303120c0e1807091d1b09041d100501150e0a170313080c0d020d05010b030a0c0f09020a0c120c0c0603090b0a020309060f15061b100b 62
    0x4e003055084607a9840c995005048003c03036004241e030401003c090f07c1c400c0741d038100ba4050085c80c94030a00041d1417031500744e40550708503162068001100c41c0082c0c17512520389480e800508020350b00f00810001030607404c520304520100e2310002c0c011501c1800700c2e0801c0c00341200c1101c1141c95010300c68401d0258026401008251012442d5500c0c003652120302c0030f0110072119000840c60800c14610102440c004080385000b416000203030300001124032240c440000d00c200c1c0e61411840911009511804417004040c08403600e20181d4141100700001d00d100e02c5d9050900c00c1c402040c0c0c402e860007514401417841d11180c280d004c09a0f51040d1071400a03400c1070400c9000c0341500c000c20300841a440061006480c005404160360908109803a00208401c0d0540d00402c240041100e00080c210f501414407004101d40b0344400d041c4a15501208140c3c40e40701c440429101400e80304041c1280c8030440540441e03228a40503241d05040e038500f210441c0d44445202c840740e20407034808403004160072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 685261798 1250 685260548 685260557
    0x60f0608220b071826070305060705070602040807030803040506180607081e19060e15010e180a05060a0501030504170a0504090e0304050111030708030115030b0301051e0601090303120c 81
    0x13140b07071041c032810310154415024400c4403182045051070b010180040c040d0301a02420340c0a0031622401e94402c4003070030801c10801e00207003910031320040d617041e00c0103410400c007510050781c0d403410300494035041a074042c0c880c1c0c0111008503c0b040505001c034066145c200015186558485d1015250903000820712264a0566582c10024030303015066984074000c0c185040380c4400d090300400c000c031441d40c1c11014882c4621300c140300403e40304060300c0c501c0380700034641fa80c180d007041004110751110903012028101455000d2041022007904964414203040e07ca0846081d42c0e90f004405071030094901238402c121000f0460050300b1250000c1141c01d0150400701d02d8a5030ba0000c0400f1039980d058445a19080421b081c030140da44540f0844220062600039820007220b51245274641c031061056450641c3e1003203903088030034044d0b08000d2030a60014002c000310700c1d10002c0c82425100b05901c00ba003000145c40040c81c03d6001d0052101520340540d100760301c52044a454000030710309480540d0030700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 685263048 1250 685261798 685261817
    0x20d0b011d0907141203220b0423360c040311090c16030504030506010b0a1d0a0306141504020a0203070623040c15030515010819060f0608220b07 64
    0x6a074100005e040341e02078040c4502c40f40c7c482c203455a00e0701c85a41c0100c680c05070300f00400c00100d080745c1020355000e44c190020102c3e4911001c00a2900390854440481c0c0700036403d400c0200303044401c05250b1080410241d00d891303a0316004140214405d5010040c05a160308840d035545003401800d07290b200e006001c0391441c0000d1340c0343c480140358100100310b000400c0094107000300071003031154034014090858003501701100310130b0103410684288030782c0c0322520303480701c540140c0d0f42c0340c0c4084c800031a0400380070000b00302550340000705064100c5200c0d90191034a81645507606062003228000400356016605041e00380d40c0e008068980c1c651013181c0726500c802c1c000300000c1e449244a005034424220b10030444d04d040a0404940003030040603082c140f40c0f104100009845941c010f0489070246010b459950359100300215007980000c503a80080c0c544207001ca00c3e1000f10585405070303261921400000d43d038622100d91042c6d100d0048440303c1c3c4c02c00c0042400111000c448075002000c0d400d1011a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 685264298 1250 685263048 685263079
    0x50f0109380a02161a0f070b0a0914060c0307030b03010b030d0c030801060207050102070314150406020d0b06030417070c090e03070b06010806030a03050c0109020d0b011d090714 78
    0x20220000e02181c0c2a440000c0e1034062940401802d96440c81e04403002125516005602c52080c070861100c00000000003403401010500c4401c6500250344170311000f600741806034004009080e165021135241c5002c00015040050003302a44a040d01c8102d182c07659941e0201200a40304c0c40c10340e640c042d03480e15030b05034042c2e4060018962030310841e901d08c108400542001400c007141a44450159042401d0a000c0d40e40d002c50310109498008171004441030b40ca841c00e9280032091a41c1c052490100300c14081003081c250002c0922003a001e1080c04940300c0d860402c01e1511003138400a002041e0010a41c101c1c0d01c0403c05003001500a00e410102d0580d00c2c0c1200c411390710101e0120b10541c000003400350400403a070042d10f402200c02c2c0303003804541c581500420343d80d0200000280c00d00c00302155030055203000750006600c00d5130103080124425034620706446802c1080c0110071310785442400c5041c0e11400c140780d161103441d048006041c1145000142105002e103100c0c1b4230b0f0420030b0001d00c50310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 685265548 1250 685264298 685264379
    0x150605130e01091a06040b0409051323061609050d0204020405150c07090c080a1d07170706020c01140a12021206040c020c01170613060b030a06050f0109 67
    0x1d0600a03000b240d0004044c0100c00c2c5001d2a11006100321800e00041c450940d00740c0590b000e80315545070015103a2500000c4180048074031100504401c44100c2810700225151020f105070300f040c00845031030f51912151a25419003a188181c000341001c0010403032440c10f92600d40300e071400548014031b001d0b20780740401d800111540b507030140008001354034803800c5c608000003801401c0d5110f040200582031003005018800c007824140150f902c2e280c0c050403a0b81c0b90440082068644001c80701c601d542d45240a81e03540d40f820380c0c1d01e02d60140c1080019010300219810500c0c540c160f54107800400c0411006020381c0050042c1d00800c0f07022441060b20b08003a00c010b140b020000d40c0450507030301c0c0800030441518042c000e07990454000c081036051340d1b600f10071020078014081300e002a541d6100170114220909030890104d80906100c80050f03281503110085002d00728080003401181c2d00e42003070102d0300c10751340c0750b450005001d20405c0152151401255640701c490311080300200302100032884 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 685266798 1250 685265548 685265551
    0x1230040609080d0c02010507140715030c111605010c08090418063b0f0d09060813020d0b06060d1103060103180c0e0405190309140301150605130e 64
    0x40109405070010710600d1820064403118105a1400c00850003460b03000030305500925030000d202c4c0840a1904540c54801d1041c0d00140202e000209561880031100070060080c032030700c0d0008074200d40310a241d005800714a070040302d103e90328423240040c500380c01110754040412050704c480e03200780103d03403440e1354501804803680c2c9100c5804041c1d031001e060013012203000c04483c8010280720a49814100c1c1803040b00c4e42e40d2580400c42d400d900ca84c1c204a1410a100684c03d5a0707a405081d1001030420f407c4030440e000e40d62550350f02c0e11180d540c03061607200414074000180d4000c0003040b02000207a0f00700d1041342d1000c80500084d0500007100c189005481d001000400616804820400c1c0c1d564144103490300c61400e121304400b10b0405480f40341041e03045010301100a080000000d05100c4200091105108485202034a1440c40d080082071200c0714058400d03040d810005c4454a441e050003031041c80c2025100e50b00000e482c107001520168042e4a000e049051082d90015801010f6480c00c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 685268048 1250 685266798 685266809
    0x27010f03060e0303060306160509030a0c170a030c06052d0106030b01091802130308030f16110c091018020301050a0f0b070809011206090f0506123004 66
    0x2040050461030248155111007103200355542c800c2c0100711644d13a00185458000310060002071110b0341d00c02d411140c51050400d21509071103510400d9080100c0124000d040703502c1c1030751111580b0b003141c40b81500c60403204401381c0000c05034448a008540940d12194004030703103030030a28814421228003080407000c01c3c1c2117a90384080500421034160940240c1c4410102441c01c002c0560400c1540c1403450015a613080e580c42c4d000c6a083c00d05151528000302841d0000792047d00c030f2601e0201c540b000b035003c490040300e00807185618000c180c01005c03034070010324007080070746600d5194505014203048020307d00e40d4842180c180000d40c445210313034040c104600140004daa01e6042609108501c40140e0000c00c1100407141c00300f041f030f4170800c20798940c0d070360220269545051100040390f00d42d90340001540210301d00800090071000d00d0748a0381c02d0744443d8000307000781c1d034a83d802c003e10350311080081401c60300480c00000341c850380480c0195202060f40070400c090320402e10382a403e0380154005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 685269298 1250 685268048 685268069
    0x2070b091908030a120e1e070b0c1b040c082206050c07030206010e0903250203031c0f09080d020729091002070305090d060e010c031d0a020a03022701 66
    0x305201035201782c12002c01ca0200e5001d101c181104640c071a550082c0d0a03007100c0844203610f00d0480c202081c0000d030000c1c10403400f101e031605908001075848800c0080c2000301e90ba4007003400095410103004047c0c18200350f0301c4046240c1d5456524078642c140302100c079416a481e1020b02400501c50784134543c09102200c40280e100c40340e81c81c01034035003501038200ca580c64004000300081002c000086442400da41c048181401d9048110b0324140c0c00c81c10300c001d506002c00324814140700000f00c010307483e100ca00070080c8601c0315580f61160481d90100400ba21080301041140c60144064000348445440390b0814140d5192811740381441070000c0441c0f8001c1e1500c00140040d820007004102d82025503200d0851030000a41d501030890f225210403140109589804101440f140c2c0c0e10408007400050b00078030502c3c40198004004011074a20740780820302034814001c1740c00c00000c00e6070303040703a01400d0f180b480c50540c1c003008169402c401103088001070503c05280302c002161151402072141074007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 685270548 1250 685269298 685269307
    0x6040615060206010e04110a0806010909061b02100b010e0411030907051504030f17031f080703200d1502031902091f230301050414040302070b09190803 67
    0x985085103691001c1c04540c01003005003c500203502030b060304158403840c22007030500c80030301044210788a544180c0c0d5034000c6500005030f407843e64000503450b600c141030400962600c0341c40c1522400c1c8c4010203d00503802800c0501c81d061803580182e000100504001700325a4102000800b6250b0502c4070b41001e410100a10000c0c2c2010014030380500170031144060b40d02c0c0303000c611510f1801240f202914114402d21250b092042407076584030407480ad9149c003640c92400420180c00b80088081c410300304000740c003002442150208401d000e4903031120036124071500740e0b802a05484002080706a104c1881605400080d0b102d0407020034800d100c80d005038591500118072000034842c14038044c3d8140c010000440c603a554819031070b550080c1c29001e5502c0e5048848111000c4462a807000e005284c214000e031500e030380e894099412070704105d4007480448031901c2c0d11100130109440060140e0b01c04403090203421350401c054103024001a24851284444c000307400102c1801c0d03400021035420014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 685271798 1250 685270548 685270571
    0xd050c04180204050f040201080f071b030e0f0303030603030d0f0e01140709060c0b040f03030b120a02090105030f03041203020c10050414030619110c060403111b090c070f05060406 79
    0x184c154007003250303580b1031542c0c0340a030001781c90023400410b00400c4099140004184070701480322900000d98104034600c00042c80d00e00074100d0001001a5489140c07406900401071900004881c4107001c00b07009941010f4014030780002800440045914a50701c0b050201001031003486030000901c3e03680740c1c1110740d003044180a05421030035040780c0c04000480c008000452030b13100503141c0042d4443e00000250009050480090078400400c41d800809204000300d941000100265594000c550b135098999031035003015910110082300c8852600184810021000c0c0c444800c11041d01031300585081980e59400155100450701241010940c00704061140d254400328540c0204030a900502107030429181d1030b02444540c402d00c606098a801c004207564442c030090700e000031040c034201c0f00d06041c2490064240e061919150f80309200b1705002a40341c101c0c40381c03481500307032020f054800d480c0c88200401e5403d611110341501c88000e00766842001400c10422030344601e000d00c50000e0181c4059 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 685273048 1250 685271798 685271801
    0x302070201031e150603050403052b1104050102190f02040504081201030503030f0c09010e0f01030f09050604020111210a2c2103030a020d09081b070909050c0d050c04180204 76
    0x5401c174408242c6407034101f2001a07007003003c40e0804010000740c64540c00e1541c29900b103603d28214161040c50401202d0b421088820000c0c000b510426001d94280012001780200d51040352400540840200040d039009070809511441c1c2203402540c0c40c030b00d840c0a10790100500b01c4d081e0b00c112125070000041004c41101070b18120f41111084801e98601034500e00001c03c0d01d4060148544101d1030a01c2e090745a0380603038015400c00411200500000851b814582d0721082c0071603007603010814816001d41004001308864800307040081e5400c1d0200701e009080c0c40550020070fa010148604400b4810301c2c02d0074800c02c440e4a0211030741a20701d0710248420f0240c5561400c00c20a505007088400105001c2c0110940341c0c00700c0301000c01030300c6901c03040000000d031240070001303400c0e118001000d5902c0380c406003c4200e074401000440d400641d4900460302100d4035124058403540108020440600c3c1040e1162810b60090044603d9040794a00080407503c0b0340d207081d800d0f44c4c0190710450850405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 685274298 1250 685273048 685273091
    0x4030207030218060607030e01110f1c0e0a03060203070215010e041a07050919030812011a07021302030601112d0313030f050a0c060801050f0d030f0302070201031e 72
    0xf40398500210304021010920074014210010203000d000c1280c615207034400e07641111502d54900c215403103205446025070300c8101a400a40086072445401e0036002e0003500c03200c1d4644030181aa0a24a2070358803400025000034200c60304500030048007100191420496034041c001000d4120220709051030f1400c8020700c0e5441201c8000c01d00010006da40d5000815903d94800175510101e040007082c012610003241030700010681540401d50101c00d5090068007810b0b545181d950b00340703a80e844070700303c5079038007032064004d60003108070f041400305445a4001d56000241814214490010100480d00300b090b010b020450480010711104a240026040b01c86071505200203103242201e050305030402d118090101401e144442d581c60010003034200945542c081d0824103900d2856240c0100030044517007881458841c00d074500c02008d203450220000e044250b8035480e00181c841d8041e2042e4081d400008090381070540e00c0c062000204504c0d041c2c4116440a850001664040c030000c1307418003000f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 685275548 1250 685274298 685274329
    0x1e0903040f09140a0b030c1908030406180f0305060408090402092e0305161b061104030c09020a0c03080604060803030a140f15040911040c0f1b020d060c050c0303040302070302 77
    0x78145c400b8605d07140400c9541b881082560a054803038042c014202c20004607502c410001d1000250019100c2e9001c1e16880c00c06036003141d40301029035111080214403906000c05070846e00140042400510b241d00142840300028001600700381c81c4500240b09200f40700c544486000c00241c202d000313082880603203030100ca82070038204407606200003010701c000803071000d0405000d40014134404a007914846811503540c4240305102e85c10b40c8029404a41e000b51000b02c1d11040b0030f280110301d03c82c40b402a2444140c095449003000f0529450850705440d0251a00d078000786e4070300700450381043c203200440c0701c3c4801e0303000030852014010f04016002002058800d04074551014091000481c3c1c0c6980240e200448d4041070003062820b000480001e02c107010341e8010b18003c1d80030b04040c4c02c00b02c0c0d5000ea107501e858600030400c1420b1941c100d1000b41c00000d604c0b0446000c900001000781d400076107542c59a161440c103080d0303966036040c51640f00b03032000d5015a0000c0c0f010021850603c1409507900c0c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 685276798 1250 685275548 685275551
    0x1909110931060908070c031502120f040c15080f0906040c0e0406060906061e090602030417030c0d091e0501080a200a051c051e0903040f09140a 63
    0x150701640c490082614003254070908520121001c14882c03a60401c074030f0745400160f00360343c0340703a1807501800c84c482511044502031400101510380010320704c252003240b00c010440d40b0107580c42608900c01c88900400841d0ba03400381c20408508109100a404195852034850394001d0801b68040483c2036001071408289502c040e04001c0065003480c1c0b00710881d03071003410000d220344462400d4001b42c861038000390380c030303a1916100166061b40015143c1c44101400180074130015180300854080340c0074041c202c0982c0c41000700b0824a269100e01c410003071070304020b5030305114880340d01030309001e03185640400040c8078030300500c80814541000500e0003400d40303500c960540303030600190000384001e040590f0281c1e0342201007079054112240300500c3d001c1c0c09a1682c3c4401d002c071b0252403a001080001c504216080040480700c86501c140c502a4219400c00304c81040d9151400c075190a0040c0190344074007051100013400c60110b040c04025010b001400301d80c4141c0c481107004e0a8800a1202ea4600d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 685278048 1250 685276798 685276831
    0x10f0207020102030922021216110601120c03060c03020901180e01170a051e070e0402090a05070504150509010318020f19050607060204030203010e06040b0c0319091109 74
    0x40c2e80002c00c80e41c1030b034010780d05100110120303000c2100e200d0034061b200c041c8900001314100c03c2a048500c65216911207080b20702e0400000004a03203001411070084480e6200f0001441025403000040304402d00c40d0406020040d02e82d6030741815035100c42c1804000c13980100e02c02e03c05681011000c00001c10145407400310340e14181703007100382e03c0c41846210244203401011070340352182070000144160f082003c582404000d8040400d24000c02040290207007d0703c0000300d001400464803d001c3d540040801c4801d23100c00c41c1e40402040301601d580207101d0100b100088030040e0001c118000d181c0d83e219652182c0c1c007480090113503402d50f0307024a240700100092070011380c0ca4602a0b032002e0010740c0c4100405413000303059032141c016500400d0b4031000110743c0c40200050b6070010400e61748280d000344100c509203050b940e41c0d00010380c2d0051403100b40f00c000480c0d850300c0f08083c5901400f5910001741008203020304030304481c40080c040e90301c01c48107041c01040d41003d041c2c0303d070410b64607010f80018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 685279298 1250 685278048 685278053
    0x30506071d04020906090916091d0c0d09021e0a090b1e0a090603060504050c010306050108131a04050607080906090d050715020f040f0b0901081503070312020d02010f0207 75
    0x140200d80841c1d10481e4085402005030b00c910341603510080e0068425105400c1038032500c1021488910b10a000420700c000c0464900c1c0d070701001d042a400e21220701201d6841d09580100c942c0c1050900112095984072020007582c1c44000b41c13100424000d400790025600c01041c8032200001d41c221500160a0007106174807620f0b0300c1d0002c42003084ca0598105060707040d10010701854600c1e80030740740340c0e402c201c00031040c0440342e4407242c06036205e00200d61128258030015803e40c2c10b0b0b441294041041c5100103849645005140b940300d9100b5520009811049012002403d1040c1c0341590294003100412290b41d0300608d03515044070140004003018a803111466503101d841c4c0c400c0320704011010030243e00300000000091414a40590b00b59152180c0268040c804c2c0c005d0b00c1780c0071350701016000c00158044000c044904558060355424402e41c1c1c0c0c4c58640c2c81203034401e0308158061050400010201d904500325900c402e940e03601516203140070b60002425100521760b10b05149104101e190f00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 685280548 1250 685279298 685279337
    0x80627070305070f1718010507180e040305070219050a12021003140612030c100e1902060412020d0f06021e090a210f05010b01171303120e0f01050103050607 69
    0x9584004c1c190b506985d9503410344928a15404114071b503c2d541c24002400802ca8020040b85c14043c004500c402506680740d440700b81d00b84040d41c0150119404103c50000340c02c0070381810301d00050400b0040d03050383d41d907004590405a1984104155487c0c84488030840c80e1521258217441070350328040c0b0118691700a00a0340000203041c0b14800c0c280619490340f544000c0c8181d90360741744180c0030f4514a00999201e0006007101040c584400d000300e2514400500d42c602824103060b4018010741c0c00c107800c100c0c089420b5007040b0416640944181e031842d000540410001e0301c510310030140940c4034540b020103498200300c51040449403481c188a04196502c8440010b8110f40801040820321b1804960340d0000d581803900203440c07140302d02451414440150042003100f4000e030b0391040d01040b02001c005030720005444020111100c5014040464861484815040001580054400d03104101e19281141e0b0f00410074850351100010403d0020501070281e0040c01410206e2441050020028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 685281798 1250 685280548 685280567
    0xf030f07020f1e1c061b030c021b0418020303160219030b0408070215030106090e0c03010b07030e0402090a081605030613170f07031808010204050105070201080627070305070f 77
    0x1406901c081c07404a50850030302c03402e0140c04d03810590800c101c1441e696504d4414108101c014042418441d090024502c006034550004402c404820001540d4008000103000d02c9941c0320601a804d01034800903a03400d00060090507083c0d034030501c5050301441448000f00c666048021001c05604007000499a0425219070169104003004d40e82e91191000403105090f0544603006018084000309145402842c0781e02600d11041c2020010754481603099607503c000d00a501c1d82e00300a10803040028016440700310424030090015007440d40311400710b4000d810070f83c0f10641e203070300101d802c284210304440c40030003801e400d0f00500421303c0c00f2200c0ca413400c401c4480c010310b2500b0100801c10601c0640c030554074656a000302d410380c2da0283d410001c0c50000000c5441c94010119400000c04041c14803c80d001c590041e103034542040c90540064921f41f41c0244080d401c0075840c54a501000c2000c2e0320642040320444182e0b44504144400500326a0010040d000b80081d4510104000d42c0008a80c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 685283048 1250 685281798 685281859
    0xc0503160e040203070308071a01051903080c150a0c0305090705060f1803061611071a0a0306050a06020303040516141c12211a0d02030f030f07020f 65
    0x81da050301d07980f000c2450102280d101801080000c1807010420009030a94442c0b103411009941e03250342c94408000c00c440c3d080a640c03e0759050614100000b440301070141c40c00002050540c3d1904811100d100200703103080782e91034910781c0d0f1518900540341e0580301c0e15400595a40081c0038190038640071540d9071040c01c414440c442c2000c14a0100f000e0b038102c81200c0544080c050314641d0424032100100c4960b040a09004034043d81d04460b1404000282c0d035044401560503400114008000d0401030380c4401a80400c2545809011405031260802c441c002d002560040d42e41303180505005080200c3c041c60381c01a10f144920401c000f150580103044600800c450807940011304103070310303480c020000c5d40c0204441f40103100c54403110b4114044030089400e6030303821002010810346200448981900c050a0348444a80000301070809500b0090780a102400b10384050101c203c05915542100074018032219000030342e40c0131410700c000002541c890a44019141038034610754440310f007070020701d031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 685284298 1250 685283048 685283069
    0x12020418110d2901110a0809031203041211060705040614070609050105012121020c09090616050702030d0e0f0a0603050a0516140d060e0903070c050316 67
    0x80e580114440c4110395108040802c02c2004080485001c000d00c81c848035000c60b101c20b0190f184005501404c1707401000e031a0503014244010680d03446910641040d400260944202000c8483c0428801c00450045003d40c2d030081141d41107079070040c001c410041c850413207500800f00740f00d02d02e500101036a081e2907050078911b02e10a9046500346403401117601c05020142010b003440140f004c10b500c02d42c1603da480c6150411b401a8a0080704500300403200205031040c8248000400c00c10421359404082c080d106907480c400b6540005804100c05440310b82d515005202444030421280105111040282c10064100030454001a4030741001ca43c04005001c4000a0341100307944501c50092040340c0103154000b8030b511160000c000b40342c101c1d1828001480c05c0041141499203401154074210700c4d0303403015903401d2503d941d00403a41000b0300c051412500d0380c0c1d01060701400c00c11981d10465842c8c00841d1508000d0500d0038250714a80d21542c000e40003007800c21a10300c00680c0100a8860303050700d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 685285548 1250 685284298 685284311
    0x703020705010212011d09160306090206040b121005030606100e010e060a020304031a040206090d3008100f06030902181303080108120a0e0315041212020418 69
    0x40440c0640b0a52600c41803181e081c0e00003044c55a140329103800d070800d440c6e82d500110380d80d1511300d139a0743d45a021000114001500200002442500000801880545070300d0501d0740d68466003e02d504910054100c080c00306007048040040750707803c0e2001742070480040030760b400c0c0035001c145a40c100300d00b800b082000c0e01280700d40701d034002c0d8907504205c200034004030f40e13903c2e240d40000e4030707078001d8081180e181c1242c0c044205c900d650000c4040c02035070002d00c0c0c240387c00d8020080208a1001c401d0440390b80e20324a058114044540704604c0515042c10f41005820340c5041c4024040c860050003a0f030091109a001c0c0315224620344054103481d054240040c44a03424000100c0000e07500011070f5401c0c01c81c0041041907000001551051882501c2d1041140d03225000c8540717030311916441000007031040c047000744010b00c20040040074490240070744041143d20390700c0000d18034044070180c600c01605280780c0085540040e1000200c41c0d81c0d0411824241401c1d50100d48200212807110400e48800c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 685286798 1250 685285548 685285553
    0x906030213022b15030c1401030908160f0f060510060f080604051b040312030c05180108040c05060712020c01030603020307051908160801060603050c120a06081e160e07030207 77
    0x600024450035603081d4131410343c2da07a2a2082d8079095a0050030b42c0d06008101260041d4000c1c0100b9608a511520403410840a031100c00e06490a1304415104101440c0340c190103c4d140f8180502d02e5406020301040614100c41030a2064080b90300207020415200e00c0208080d501107103a0f0b8103c070045a0104242c0c694400c0c0c90501c079800d0340c03070340e0309140009400010040e00040f00086000700351801d2000d403030341d16400d903a68010440480c1e0705481d00c1c002005290711400000f6840b40c031924040c100306031500701103100da820100e8100c41c0b50081d071030210705c82034040000074140c0d00b0900c1c0a00c03c07682164003090315664984101d601401c800040c42a440151041e840068031a00b4111528401f41c0e402d0403e8070b01c507034465862503500c0c001c40821040d109000380361142c181c084066207041801071005960002c01050803415540d81c081c04606960140081c050306480c1d450809184483c00400c1420a02440001900d2800465040100c48901982941d00c40000d01300140c907040c490 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 685288048 1250 685286798 685286801
    0x60d020d0f02041e090c1403100c02010f0c020610241b0803071d03062518151b03140711180403021501060e061309060906030213022b 59
    0x900310600d6864200000700d40302d14036517110021041c060100490015070303400640007000300740c092543c8c0582140d2014600c002c90340e00802c1c0803104920000601d018809103c00441e0b100040050040c1c10160611201c8a04500c05501070006000c601081505000d203440c0c0380c6003030403a240b05010300c001905c46e0220080d8800c144598025101d03664920b001003005207900e8043e080c84a08211001100000d8140022228030a032034201d2480012540f000814480721300b08a980700c2044900401102c880640541c9007000307081540030804101d055080c050030034030768076008141510460100c203000c240d00040015408450b048a5951000e26040c40aa11900c02601079000b0f03c00585080f0b00400c8503200511807070195003606d000319460084019040b03400e214000010f0400c4030142c00a16001e0000d00c407042040054100a0b070356000014203444080d40b001e410f007640e401e81002541404040100b4130724000c00210302d4000da400c0700000c0300c15048180c21071001d041d03a90180942e00c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 685289298 1250 685288048 685288061
    0x712110a1b0c0305030403020306011a0a0c02130911011d0637050a0f021c0e03010204030b0a021905071a0c0c06280b090a0f02040509130b060d020d0f0204 68
    0x1070054102c481d00d90a01030380d00e52261100728002d22a41c00001003840c10f15164800c030f1a2684d4009203000c25884049400300d0202e0403d0764441020000508050354910030710300f0716803041c1940044406038200251645a40d541c4180c0c5081c45010341ca11169651000c0f81c8200c58640032044040400c00500c81c0820074603c02c10110a244110005aa60b0414050603100d00140d0780c4c080150b503107050413a2240e0180c0c05080d22071a030190903001d82d0380560a0b41c010800060001410965243c99031035821100360b03035048106500043c01c00c04144440c80401e4040c84e0b9091041c94a029540d50303030b0340c12a43d400c0d10076480c0081c00c042003410308035602b1a03100141000488900e070400c1e000c1d001d0004400f401555a0802c0b41c035a90181d50940d00070750403a0100244162015650115490081c0ca1344c46401c84a4690822000c10140d640e01102806071078050603102c444c2d646071926100c00c2c3d0000e00b40d103104140540c80000160748020940b059643e000d101e1580901080c408079014001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 685290548 1250 685289298 685289303
    0x40902180d08131a0d0507110d08041101090605030f0603070512010f060510020a0803061c05060a0e0114041511041d0f070c0803070c02060703080712110a1b 69
    0x100a0380414400300b0b82c00342000903d840049401965103c2c41800c00480040e1085400c560078048200300d80696401036910100f5401e147c80c50151201c81c503400c25407200710420125940109000510401000002003642d00b070074105184da04249000d0400d0200400032080c074031640f000075045460a000340030091001800510590748400c51480c003034042240580d424a1600200054500d4140c840c1c060303d50f156005071400881d29150044039603c02810541c0040b07000c600b043c41ca101060144000b54000e1000c1c00070360601c084290107442c10032085200382d80c140544c2e41043ca00c1420f03107541083c0c0c400b600d00c0d010f01c08441940003500f8020b280b40d114a50200300010011032052052166403035078484040b0540d41c1a0600303002c25400e40d002000121049012000503403000001d40d005103982c28402540e01c465400903540b079002000890010303001c18140403060350030103c00d4142c002c641d4028800c070b45001c240600e580c010240d130f0100b0080394000804081f2203d4a8080d00d11340c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 685291798 1250 685290548 685290559
    0x42040608010b094b1e0609060a0c080d0207050609010615050304020102210307030b0a080a03081306060b0703032307080c160f050f0304031a0c0408010509010605011d030304090218 79
    0x204100c41e04aa141c80351300e18501400820030012186440f0403814451444000c020314100028801840255046840d6030000d0001c0142c074080810a980d0150109000184000d643d0340c855150050a0610207803104031642e05000c0107116000c00071421004841e41841c10545980c0c4a000407440c0c4032407400b104c0300c51040514040d10045a50004521803985510203000c000781070414401c2000c80c030b2140c18030f50780081e02000300081c841c81c015500003070100c3c1000c10344e440a8840d0f50403078520f136001035109100003440300101600740c020301200341c0020a82070b6550090400181068070000d00c00030400201d90300260b040001c0400365a000007200c541c840b8000e46070b140490800000240c20b840c10312500038000395521000044800ba6540481e141002c140b0314400001c80c500042d0481210000902010078195024400c452155429400224900b031804002410020b100b40c2e0606034140150014100c40d103000080b42c2c22904001001030740d0324140710048480c52240080ca5a021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 685293048 1250 685291798 685291909
    0xf060f0310030c0b0a02100c03061d1b0306010807030c1b0515011a0a1b02090c07153b030c030a0e0f42040608010b09 52
    0x2044803000c00d9050740d1046032508000c43e00e6582d1306500f40209041d00c00103a0140c809503098088542110418402c03600300452120381f40d03d071000c1c5140f100c03800c0c1e03040041e07000c04110010400c18070070041c40422080c0d00e40395040c8940028040f030001071580041c10740315403500c882d1901c602c030300148030425a41000410031191810645620740303001104121032a110000c100044c882008618000d242081d4a140c00c150400945a5500b4220a01410b404120005000da04c035400240d1162a0b80901c0f16917404c0f03035103444103c4603035812400710b0091a040c40001c08102600b80c010b2705800e549200980450075010f8a4500121000100b02034000426001c8600e08008086e203001112529003050b45120802400b0341501d82c010901c4d400700b104012208100303020500d28849641070448904111075508811165887d000c04658001800103020003c0d1a80720b1046030251045280e040c2c60044c02d00c0004039010020164000030303000f00309847c072000c0e4055203d41020a000300081054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 685294298 1250 685293048 685293061
    0x130b0a0b180a1a06090a181b11100e060a1d01022a0127060f090804080d03090c030b0903040e04030905040c0e2d0a15030605060403080301050f060f03 66
    0xe03040701050040e200da1510309242043c91310308190740290402600120b510361800c4490904d4140020031880d9640e0b5880b141d40300f0b46202e00c14500c44203902d84503a01c01245000b5058039110030b41442c45801c610300340d040d02000c8004500380b9040443c80e20041303107540c030801c44140d40920700080c116a0b503100141010904c1103060400b45268010100540d070f52081081030307400c2c1d9200d101c030707030503294861182d50400103400d01a9280c00b5004590000b400000803440908850000d001941c0010010074200240041084071122440c144c2c84d042c00b074546584d50304914403186010050100d040c00001a61346003081055a0041041e0b0381c0b5213145003001e0501520205590280c0e40c01350381081030100300782e4015101d80d080c00b01c001c0d20510200d1080300c500c1d054100d00300c0702128242d840142c2e02d600d6507a41c5102202904c44400403c44407040d400025007115555440a0f020b00d109003c01c00210704520103485c11518252030b22403101210400180481c881c000d013003540c810011040c03020703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 685295548 1250 685294298 685294301
    0x13090e0304122a0b0d3303060f0e060a0b0d0210080412030606050921030a03060e01050906010917030d02160303051f0501030e0a0c060f08130b0a0b180a 67
    0xc0702c984500d41030001d6030101071400f000c0d8541c060034104007010030000304001e84c19481503c20914a541c08020b44020440b000c80080b40400920300101c1003440030710a01c1442d10a85110082c10642000341e9942e264803c0e0304c0340d90007440058041d42c2d40c1c1d03020050303486e81b502d09000a40e00030980ca482814064000e00290f00644090b500c03140b041e81040312560082c0324544c26a2026100c1504041d040c00800c41e210100c0040c04003140b072144a0352050703407030400c003a1002d2005a2400302e48075050038000061603005071301082c0310302448800d02a8590300140c1032400d82c1c94013589050701d4050405003d10b944200010342e45260720000e94003d0a40309042201c001620a07541480700780c440d6a11452a60000c0110401da0031910208002ca58026800725070b01918010680d0103899450322920745520490f8020000b040800c072204448a9104118960210381e108203039000c03244079201e810791000010010340d1b880369100c085140070390f134480c95080903180c1460f9813080e0b850074454140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 685296798 1250 685295548 685295573
    0x171807080604051005070c06020706060302040204171006150f05091509040e010605130b010e19051c03140c0319020d09050604150c030c21090b13090e030412 69
    0x8906008103545412161014040c0a016100e1b0351b4415030124620b440d40360003540011000c4444542d101d20010041e119400600000d09241184401100c4480c0c80740e42450140b43c4ac82d403080d850318078203114071042140e140c610541903250152001c0807040040c1e54601c60b0003581c1c0d0703003c0310b0303440d0042a05445000400300c4050581c0e003842043d00c14000f05003a6051402004c0e4042d61140c003007071014170151311070401c1c2c2d641458140ba0340700c80c41c404281c1290042c44a00d180d580c100c4001d120b50301b82211080c000341d1910301140d01100c0e068070001c0401800d110501c4803514000703401075441408005890305641102d0010441201d0480e0195a9541d080320284c04202400000681403412000381c500f00d0740c00108090021307144080484071205414011410b02021951080c0403076910a2024088442049440c0d840c2d54100009030101c26241c1c001c14500b00e0420403140213820070b071042c030100d034a06c50001c01d00303d007414003042c03d41c000e0360000c030446407020941c001882203d901c5003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 685298048 1250 685296798 685296803
    0x6010603141603021c060b04050f120c0d2306010810060303120c02070e010e190b0618060c1f0b04140103030f090e0c120c0307171807080604 62
    0x1004191550800c54000100440c1c58150207405002c000720681c0c00380e0020080d4080c6030400741c07003944540139140b04451640d0400041c0c64070201e0288841e0405424005102000321078241880b482c0500e00c40e0365010340c4426902814070000a0010468603090003c2e01d0040c428000c0c440310748965010303a4900d400d01c1421468800c10f100380c6140350261240c641520303090341e2403070020a6840c9861005c0e14a0401c40d40452190800000300c5001c807582e07483c042c00a0b074078224000e040c0f840740c0700000803401da29039100034682040700b100d0b5a2070404480741034044050252603079401e200084e0950044440d4002c881c05070540244140700480e0401690342122401001809508010301044400201420503605400001440803070301920406100281502c0c022210b951511040c144440c419a60828100008103c0c0c0442d1403160010540c001d09540c409411443c20103002800c0c650141c90300100d0808450128100d0244080e56070070448082d07044601099603059596524041168203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 685299298 1250 685298048 685298051
    0xf050403120b0f01140d02070309080d080c030f070e030f0a0605090313030b130804060815010309150906110c25080c0108061c080409110306060d0507020a06090506010603 75
    0x4110300c071403140b2540140d00005045521050181d000556503054680021081c0c0d00c4140701400388020203000800e100c0d80320781d48000700d16107050306840c46c0541000c1d601050084010401c00038003d45410b0300d0b88081c007040ca4070016110510203480c8000a26412601402602a800c1603e04005401009584039131000c00403640c401c5001a00c074045c0e142c0154403c020b41e002000415820010b550300300d5140c040c0129864066540c441555100f42e03c940c0c0032a80d6442000b410141502122170101c9003800d00b4000c07142155101116085041c4191000303640d641c0e002d40602106034880480c07030006080080c2d80d074010064055480900c00c42c81c0c0141c0b03000403051400c8606628515080340c2d401402000541c1e03014005540d048001000c0c203800c4254010002c42c1145015807400d5118018403003140d869007000d90003c00d0b240c14a201d141c3c80c03942081444a15200c04046070340d0365002000004903510303007d404905100e84414003618079820031002000b8000085031850484010741c50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 685300548 1250 685299298 685299317
    0xa030813140609010f11070602060708010803070c030b0a0b13270503040614070b1005030601150507062409140a0e19061508070f060305040203061302030304090f050403 74
    0x400c0c04810741401803031500501d00340b200b0b000f29401a0110340680c141424580b0302400b03c0c014541c03502465034000c0300168001010302c052150002e00303080c05010208040e600d800010780b10901145010710008001c0501c540000300540c40c10f83c8420361385a001001414000c56001500014101c0440c1d904901c0442c2a003040320043d5000c454001d1643c010069814079141c02801c0c0c4002c00107100c0540100800c0200500155144613013600c10100c0f00280d5805038200828103207404016001a40b4020f00c500c03104031135680120580748184e83c03207200030640c1038200a00600000041d0086050601e0b11030000c2000341c0c0581042c6d00800f040c0c03441d81c1c00e0b0b0b5124801101501d41880c250f0280e9003104100c0e200d185451a042d003951401400c02180d490500340c0c21600d0410b45070b002102d19001018103011820306c5501000080034546024801d508080d00069100e483c0540b1480f810200404440110740f418006c0e41d004050340d142c10000e4a031074150b80c02c05400700310380840000d0302003003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 685301798 1250 685300548 685300559
    0x51b0a1b0608010b1608070b09120a020a1407120b072607050304020d082a01020c061f1e05090f10050d150905030405090f060114090f0a030813 63
    0xa441251542d54584140da46400c001c3d140d5540210401964900710030040008149100002c02e005031082605203498585040c07050b06000358070988401c0587e080020716062a400500e041000e50400c206040e407109820013145000e640354440c04d2030208404d0070f8010311370441c1c40340d4070855103a15003c5500c2d125413900b113a400800c001d207008000c10b99000c11880b51081d0061540a4400b41c264030740e000c07954850501c25042000d0b08081441c58221110f1507103070207894605a028203000a605000000c8030441d1079400003410b4200f404101ca21000741c00c03680e403a60b00010001003891101003410104030b0b89202c80c042c001d040c010f8403928042003150a5240040c1d100314031300e0000501d92401d0004002442030826015a2851848410390411400900c110300f6454401c40c001c56486180c50140185038034002d06140d010601c3d00e04012041c2d0304210310040040000603030b245c1d603072590400140741e15014440b5540141d000300c0040204042c800c01810100b4030f1124040b00360b07540c4c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 685303048 1250 685301798 685301843
    0x60f161202071719120302070204090b100b1c0509070b0a030b010305060609010804030806010c15061403031303020d14011b03063006110307020610140d0b07051b0a 72
    0x480c900340210800034580008034000003168185c3c4800762801601e001042c2d00000e0a072440c0d00c0041d501c418006092200d4000c4a140d9403000340001804142040c03000d150280c0300e2034541c0c695142c01234949000071000c40c018000300e030280c10100740d005c0d10703030680003c01802440c0020b07a079804249480041841c610300603058600301d6105a541c80380c40c1d41c403903404032000c1c100544258140f1a0400c07a103070000f01140708091410320342c407400062242c54010a14155100c00342ea5070b000390010000444041d2910343ca120a6980550ba500d02043c913501e40702c0700160221582e503110f5440c1000c1c0490805030000915640c821560f418099161101c007111800320148418200a4002d0308454001c82d410080e40c02d5014000c241c0040c140d0b0828078410850f6008443c11001600708400300598403207104108170144c001154802c41500310306c0080380c00c03482a120040c212500c070500081800e4802c1d02219458480c0c0c40010054003805030526989050160003110042c100006144418400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 685304298 1250 685303048 685303063
    0x50108190b01020705030706020309130207053406031d030307050d050414011103100902030103080a27060c020103050a110306061b1f0507080105060f1612020717 71
    0x800d4110012160950150000740400d501081c1580161140051542d034103004060041c03000b42c01460ba04d12240d8204103c4d569003100003100c0500c1441100041100081c4030f86071611f0007d0502181f0b85009418504041c0e0038080ca070550285400c00305840d94142c02104e0206003240300000c9d45694400420b40320f001c201d800c0c00000740144504082e0324859009590414000c010500305130328001c5c82c150030340da141c110f0801a28070001c1070203032052194003030800a0801131f404608550450345e0301c2081d882141d041d803041050308100704120040c0b20404504030b104040b00c084415568910203000d84d50400b00603800b1038640b82c005100340080740513040d031070043d42108602d16910507082041a800c026024011715030502ca281c0410070080101040c0103034142d030a0609460f44144900c143c9030001c100c141001075080c010886616a00140ca451412070150750392070b114007007901d0300c0c008840301d00a002d070810481e9072844982c011a40d501a41d100b000812841d104010105986020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 685305548 1250 685304298 685304311
    0x20f1810170a1e02030408030709141e120d09050111010e0a021009150e040c03140f060f0a030f02010810030b0106050307031122080109080904050403020312071107050108 75
    0x4000000302192000d902c000000c00303072054500c0c18003c448050b40202d8000b1617044410300000400d1040135038025085400500d05003010b020b98445d020302103411200242018000d03050000c410242aa0700d41c1c2c000c86000160300d00b03d5401450304400203142003000c1c4203150100b00150301c242c00152040c050995200024001810154030582c2480303030715482c0d03142c10010041e0385070300861201006000c01010081e15540c4c2007040620504005c100c40d1801d1040c3d051514042c503040039100589030300f03540311001d10310152507a500c10b0003080381c0380b01c85c0001039071001448602004020000c8080080315000307030394074580c5a980f81c02401c101101800b014091009500040202e6445075005691101e800d2801007000d9074039000356103113500700600340301d141102c0d113544002540c040d003185002448510000d119400300340e03c030781407288101448140030315211000102413600800c00c85111140345d03045040d441c944544010140e0250340f00e814142d0045800000313141d031046540320301441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 685306798 1250 685305548 685305587
    0x6050f0c09030c1c05070f0303120903020c0f030309060703030f050114030703060906090c080a02011d0a17012d0605090601051603141c0e010e0a0b0406020f1810 71
    0x10790030b04120b50715081d2040c1404c0c0c88481505400041c0052158000030601903084442090441c0b40240411b42d06820311254613142c09002004203900080090518606964642e100c1074001d02007400e6104042000d03820400c002060003c261f81540704100c048020001084141d03201c008000750381e0512902c80380c0c180d20900051010414a5001200c414441c010015852500e0386d20442881019070101c900e98108680300001d550704100f18001011031105072080900340200080e00280c854050360341c840c100c00316804c1c98140c0075072000045803210013580100400100049010040715013102001605000b80081d041c10300c0d41c101c900403107058560b14140051025142042c0202480950030490a01c1c0c44a42001c2e02c44010400d000e003040c0c07851000e044440c91101911100068464507a1401207810b00f0b1031004500d440101303034880c034002a03075100d40c10020040d0243d00140c4540500008850180c02403658049030951b0707080d22413508050081c0030a0380e4100090807052880e2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 685308048 1250 685306798 685306813
    0xe18060604090f0b10090c21050105031c020f0106090c0f0f0c03050c01140a0209030d020f0c0423011e0503010c12050c070b0c04030506091c12021606050f0c0903 71
    0x3400f403a1805034407a00500b0710040031561032508030180d840d030081d40804030b010700703144003401800c1c23582915214544880500c5954503003404179a40c0c0311380c1c00c0341d003152045001d821225180309000070102803a80b24000d008a036240c40291001f0300200f0748000220b540b000c0e0100c5d04a000d040c0c4043c5802c5184c0340c017011a0b005450941d1103031f000104020465507185034140130003d0140d042d50040c100e5110058540c86a24181032a04503543e6444081d07500c0481c0c400744c0024001580035030001d06640c08545c1214682008a4141807284c2c2e40c2d104044000c0086050740c000c60f4082030880340960310070400c0c3e5884041c14201d40c092910540004e085910317007010703c4200e41009070003400741ca07080e500c1d000c15901d41e150f080034280d81911102400203810801d101c2c0400811707401502c500090120401078a407200148a04d60180c0d42c107004020581000e08203440c0e050304e603800c1800c03420325810916403a004004000c22035000704941c800c2c0c004240c10a042003365501c0f000058018200d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 685309298 1250 685308048 685308053
    0x30709060f08071a0729010f050f0307050402070819050304020a140108040f14031c0c110307060b030a020d06021909050a0501030e070f080a030e040c080403180e18060604090f 77
    0x2568414581a80d44540f001d01400c90320300c5041b00105001c1c5002e00009095040c5403140c0301240b5554061842604002c96103841940d01141041c01c45a08440c0180d50301c1491030716001a0048503403201c1178810b0301084000c82500070b001107210f244202c0341e81c89080d480f040d1450100c44a441c11500181018001a00040c90500e22009040c06200da80318000d0040740b0301031565100d84c007814904e8200f01c42c140405484ea01910040300d03180e007400401580c00900980c0d5074003440c0805042192900d00d07540b80c070340341804400000c5802403c4d170b005119060810b00080d51007100c070381ba10b492640c0c80d510039040c843c0c07103001c007592801003608002d945001e0044024100c400458034440c010702d8000100c00e0040ba4484009244240140c4001d42103805e02414403d501641c10303003d10f00f00007401011552050100c2c3e07104da4141071404007101c0030083c4181542140e0804841107107641d0501c506084103402c41008071400c0c03000c440141e560b8509010075a04580001088041000d141500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 685310548 1250 685309298 685309349
    0x20f0105070c080c160b0a0e3109050717100c09060f0201060e090c03070b04030b0a020c15070530180a08190f08060906060306040b030709060f0807 65
    0x1005003050003140c807407210100ca26a0914404c6e488025000b80024161100da5085010301141d04011a000d4400303e80e800c080341880715101c0300c1500000d60805104042418070351141c180103400c0405c0342c0c101c6071605505841e0078100040c20300c9510440c081c0804d001c0ba24042d152500d44259110f0b00ca59103403120640740c40d15a40d0003202555222980072030b0210326030303020500c41da00c0c100c0204100749212080c1401d003440d681002104800401050001c10181a60380350441c010210040c0d40300945052203080000c2c0c05850700c140082001070081e42d9a208000c0c101082e0509030000e541394440000c0303000404090f03580a844000e690001c0d03507214a40b04480d69540f0b200b0250ba8015034150b0f41c100850344100c0d140070090700d04180c4c2d403448507070201521b880300286007070a103018101075001940829000b00740e54403840d8000005a49a10b403a000550810320207003c540003d9141c80001004d85082e0107180c648214100340000c8060000450307404403803c00305c00601c038201c800c2881a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 685311798 1250 685310548 685310557
    0x702030c10050c0f0a02091e06010f111917120c09010e150d0c09030305390105041103030f03011202240c071e050402250b0403020f0105070c08 63
    0x2000d1100030700070b034a1103e40138000080e554642101902c800394a6204103d01c1000280c001c90506500c0d0301d0003144161007285282e04000c0900700b006030280362002c11034120800101520b4140141071164501480b086505c41d04240f1500a03075070b10510785c018030170240c00b51204000100301d413440441c00001180700141241001850007405060040c0081800c541c00e5440501c0d135070780300243c6441e9808281c0b240d40e603c4590782c0f0300205241d155480040071401540902509110b0845412140002500317904410300c00701803103134440c401304034081070080c83e04440aaa180303448850307801e25480c003c07003114210302800c85002e00316424460101554a40080300f01e821101085940c8100c3c02c894141c18103041d8459030701c0340d951a403074102c06c2c1080641d9001c10071040744580005c001d180340d4415001540c005480043c2c480d00c4001e20000e503c500c90415501c400c400403480c506210450903140d20403402038088030983d080c80d085160803203200f200c4403400240c000e101031000400d044001c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 685313048 1250 685311798 685311829
    0x2114030907051e0d080316021f020307030608010c092103230c06100603200d1806090302030a0f2303090c030115140402121f09050c04030204050c0702030c 68
    0x41a021120f84045001c0104202c416038176414080b0821000c2030340804041001030782031000e00700c04404401410484d000d0140640300b5180c01100113005180309030301c510000c00c0c400d0024082218400400307040e00b0200d004203030b40c42c41c1103c01c440d0503000c0c0b0a081c0901e00c0d171540e100290021200034005960b03d86c444414903084d010420350304c014504021240c02004c06500c5aa04203140103000350494a081e540700c04440d81140c03aa1250070a00401e5401402803400f011440f0801254490b844038000c800c0100107915292a00c410303d940040a130001d002c0503220030002d01d4540000f95020090680c0d003449901d40ca446144040c44150041c540108200d02251860f841c0c4000082c00e4904d80214058206d14000d81089044003651030070141500546085142c003079604403903a107000d8001c3c0344618500700c0c1c0c1c2d00018041d0042d1810001841c03420030412640c2090840701429500c0351006038801c50900012444020b00f60007100c266543c010001e00072812104240080c0301110075a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 685314298 1250 685313048 685313089
    0x6050f040b0301141e030a0b150904050105011a1638090105060d0b3c0601030507170f070e0a0303050c0d020601060c0816211403090705 60
    0x1070304038501016601130000380d03004004c244c00780810712600144040069a08820303400c15449191004650901032a0304603038081410743c0c540c1942c94602511102007504a12000100002c0c40703010360285041e42c1ea1401181c1440d000c00d55088038070300550840d50040c10510443d8800203c0010f1282e03aa141c5900d142003260950085079903003c100c002c0d60b04aa280101c040140c180020321800c0e50084007111003200a4400e1345a51500c42c0c4014041c2c40050303052a89062450005907200380000000c8904a05080d800c0442840154040c2d95082c042420f090102d080c1601405c03e2121550058190413035a0303407041404040d009002d07104a0a0041c01b0141d0b82d040e482d40820310300a18000d485442d030b112003061803240f0b046540e01c0030000b1504403a0043c0640c03684918100c80083e0800c4241e0707118580380003480e0103c4404400100032803d40081c001a500c22101c00c18042401911114402c004102051803280700403511034919030001c1c401804a07180074800d0221021410f2007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 685315548 1250 685314298 685314307
    0x90f010f062f0c010206100b040302040e0a050607020706080609040807060c0306090c02030c0c06070507030308070e0405010303110f01050c0901051e1615140f070e190911040803030106050f 83
    0x260000403641a6044055a0b0441c480090032945c04108031604004950302c91030f485450302c00750703121354020f500000740b040d5202c2980e141c2e41901000125201c079000400e540081c1003958000c1c0d0303510003510584010803002c0002405602c1c1400300719214681203614503141242a94a1900500800c00614245503603241c001c18401d02c1403055003440022600119600e0207803843c49032070203100400092080504100741d2000450109642e000c0320783c1810f1241603515003102c00c4d01d00345107a80301507801c039203000000004e160b40300100d80500d4100105491040707842410035401d0f12001c036005440310008001e03407030095100724001e1030582040c1c048601841341001403100641e01803034003100002182c03505902800020b040020fa454114002008240e00420310625401d50090202d01420501c50000f80c58900407200032940107001405510126002f01c00c0911640da14001c9400c00d600c6c18011349c013021440c83c1150180c0305500021425686880000c641640c060510300300040d10500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 685316798 1250 685315548 685315607
    0x50622080904090b0a0c110307021e03030d050a0203010509060102010207110918010f0f0b0a0e04020105030a11030f18030a080c0c0f030406110d090b1b031902060402090f010f06 78
    0x180b40c0d8007171070703642c00302140d8003043c000000c08045800200101035042004000016507420821034000b5480c17420380301180b40640002811030180082d01c8054174107080411802c4c000e80c0d80194140d52046406002c0ea07110b01c0c004900702d000b018001400c003400c0482c138004510301000802d500c8030912140c5031048690a010390300350303401c0040386d00485484a6500d0141c550500440300f01e2035047d5003400c0c0151504204000d07402000c0d00190600034000045000000c95401800070510304101c200d5403428551709144801c030b01229042840048074209111007100072085641100d02540c5020303447c0c5a2481c00039803a80111039a032510b101e05001c001d00728600380041e00c010a8551a075490340d190014075a41403e0703100c0c4a0804100c50b80100340690020a41a5400702c80000130112006c5240c5440526600c21802d10f0203800170350300c0030b80e03841e1980020100d200c0e03842902d41c6500c507103030250f00b03400f5134000307000e800d80c1000043ca040c082d15105403401104402440401301880d40c0b100d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 685318048 1250 685316798 685316813
    0x90a0f0e0a0b0a112d0d0603030f090509061e03010e1c12140a020901020c03030f04170a080307080403020a0204144c180905062208090409 61
    0x85108507403001c8440304100440320b161082d5001001d4100450380745c4031741021008045440408240490318400341d4200c10f61803158180c684500150004000440c1c490401420b031004183d001070028890044c0443d190401e2441640101d04c042c10343c1c044004800503a201d1001c0206080d6015940c698155200300390801128550389100320007244242c428000017400b002442e00e0200205090200c4440d1a582c0440c015501142160300140c5400078240104d00300350401c50b40690511006c60300e4508401414010401c03588500d00d612028446950090340360380a84002415000d01131001403885405032400d243d12a2182c03040c0d41010031a50300207800c0345d080d485541c41010a0300104404800d1950059200c0303003c0d0301000d01c1c010b000c0100d0241d041c904040c0c0d852040003846510700340d000c0401d211350181a114440520070600505000000c02094000781e4840c4503160114000c160318480e0301050980e028088481c0c03a0b680d0712a092541d02c0000c1117500305a4600000c2c002c1181c0707 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 685319298 1250 685318048 685318063
    0x3100f0e0f07151218120e01050d0b0f0a0e180a0c050118080f03071a040c060e0102030c030d0f0c0906020a080304080403061407090614030610020c030601030501020d1406090a0f0e 79
    0x10031201c0d60b8442d11078142210381c51b0f03140d1000428400000c00d0070b48960f8014040e0b512040140001040a80c01c0c00081030307882c80101070094210031500c10200d004000c2540e060300c0356804070000c000000702d004d070040c5d03030300c50014001d498800408024412944664101021301342103100340c0c0300059030f40e5580741c60425142c0c0302c01a250000302d641d404200e1005074074010b4201d5000c3c080710303600b044d031250030a20640d03101e840c05000c1114080c400301d034024001c1e940c9803141c030303010349881c0d004180c000400381c5030780aa2021864074101c40c544403940510300010580d1525402012000705590b05d00f20340d03504c0640182d811070700c00d01c00000000c2480c042d82c406a02c2c0d4030780e4000c440c1006d11010300100303030a40200e000d1100211184c11003045580640782e00001c01c407904002aa0701481c1a81405050308009425000f448000300c00c0c420150001d04001420880c1080521100c041c2114946419030b50503074000c05040216014000c507800018000c1b008000000d420b15640c0410f5141030340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 685320548 1250 685319298 685319321
    0xe09010905280609050105060903191e030c05240106030522030f171614040503120a0206071e2d03240e0402120a0203100f0e0f071512 59
    0xf21808103101040e001d004850042200796040e5003400503241c0040e40360783d03d09d85c50045040d502940c18061180941c1000c10305401c40c04030711040206030900505020607114192018842e000307680305600d40503d0115800c05a00320340e1400b82c0d0030702030304401519015140c00701420290300d01810303e020501304205401d11940f0b685c80270000e403440161251a8410001c02c01802c21b100700406140342c080c0400180c5e0309454101425443d03003070003800314040c03500000d4151003201c2e0300f4004140e4040c024201e410759602114402e54810104413225600c081c1d511080c00e012000c100301c294054010085481880e408110f40d08480700c5002c603040c04280c070384000280c0c45801c601403c41c00e45280c0e80c4c8900489000c40d42c2541441400c10f01c078440504002d0080f550b134180c0b98407091f020f0020003030556004050f41c403510390025a200142200380303c840c0d2410325020400504440019014013407044480c00707040c0c4103207800340f80141c0281c1210304a047c86005980442d401c03100c1d10038070450300ca = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 685321798 1250 685320548 685320551
    0x6190807140f03070803040b09010c050142050909010f110301090e12120408070807080d0f0c200f0f0f1903080610031b020106150e0901090528 63
    0x620300d070208a098980301c0070080c0039130005002802000c1d000300855040d01e210000841d44e070407650004858504061074050101d51030440282000c18955400d010700c1581c80030300c0e04904413402010300b0341410219009441000c884070412190a000283d00c2d03000448400000b035521503074030110140d5450b07507e18462002c0000040c0104611445108504e6020760300070255000c1c400e1044a151103a441095140900380d00000c0400404c4401c5541c11a13000200d61b4544070103250049594221a00040d1303020300301404140c88040d144207502d80c081655a0f40e6a60700250000e401440120b00208031707050203480d5442561000409c100100318038510000c1c14692341210703805041200d040b081450040140a0010110303600401d0240c1140b812103200c0d91948103910f007170313000b0070b00080d000440d00320200d480e00c0e0041d010b5011800326a041307070420381081451a8226840f002005a081c0d100e03202c1001884400c0321544190b034081c28080240241500c00f21420032022a0882e001901a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 685323048 1250 685321798 685321829
    0xd050705010212130b0306030c0312040e15030a03110c0d0b0402100509030d050d0216140606010e100e0307030c03141b0d1407050402030a06050a1d06190807 69
    0x3968100000c4403c481d2842956003030600008842c1060045403250005490010001c900e02d070303030240006804000020101c0e4280c80811803c041c1c03540091280020002e101400907484040904400c09400030080140013424039640d8291800e41d00341c501d0501500c14880728428030b488950103009120b0064103840f2592400340b04000c0c5181c020441c510030443e092245501e03c0d1400208047c0e21220f509209403201192040007000f030080d11540c004911503042246c00340100c801000020b030700d0450a03200150368070001515448035844950b6040b915001207070080d2442440c00041000000b0107441402d40e40c2e865070304600e1641c1d0400d80d440c0b0029121900c0011042060b40304035000d954086a1501c0b4074400112400c501c0d060190074800358110413140010103010ae4030141c000180704645909200301010014004c07401001d0080166003000315091404034411050803050018840720b0b030b66402e0a00c040d244055140c030302c224101000102d00e0304814403040000d0403c00001e603250 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 685324298 1250 685323048 685323059
    0x90b07020c0411072103020f0d1a0910091d0703110907140d0c360501030501142709150c070b0a020a140c0706261303030b0d0507 57
    0x1c907103c1440d1860060700810500000a91040c4071140f54000c0101c0307800c8000803102c0c203070043d201d441002a407844c0c00080312124002d1075803000940c2d94080c0d0f1120f00500c0c030318082c08020171040d10001981101320108000780e400503002125400b015210400710480c4c984801031502d542a0030884440243c1c8001e403203a814020038980e844a0146001d140314510390a5800007841545414602c141c0c5075000c111829000d400384059844440200041c0d802d90454070f602d810701c1c0340a00d44910ac02d6003000098070761203805094180d0b00d104050072411030131401003049038500c260140e1180d050719a01d041ca4a0305030904148500104005041100710f803d80d15998103800030314001c1c140005121210110380390a404035480011001e00603521034002000b9505a80d8100012078070004c0050381b42d02c600008100002202c1180d100c007030102941c440c030440e0780b0b030040302c2840b8645008800a24908861303c0185003980c064100010740b182c403880440c40c1128440026943c076441210308004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 685325548 1250 685324298 685324301
    0x301090620030f0103020f01113004080303010915030506070504050f0d081c2c010b0d0206180402090604090504031e020a061109091608060301020910030f090b07020c04 74
    0x80c58004000720918600e492090550600c0d010b01001c1c1c00342d101c905001420764041e40f901482c4502c10b004950390702342c1060800503140100c9081c1901000d002c0607680014461000392415210000c0c05141180e003040140e400411084189049400d4036810003c00301d43c4c2400842d0140c1071030347e105640c031070803e810700611825828400b8021801d154103e07000c00c00c1c05050361030541c80503c011440502d031844950107130200e00006c00c00700da005d5540000c02d80002d0301c203841e40303240c54000303004158030b203010001d01240c0d030013020390800c0c420001408012000e40101d550082c000f040103090400c1d80021452640040c3c0210605030741d10301c1070000307144c0c0140e01c5c402c440481c018400c0b501ca014a000944550410030000c000c03548070780c20f540f48070f841502074030040c45001c2c00b22442890320700c0007001844122141d1201080104003c22918101070007102d400d080d01603c43c007007155880004400500300c44109048a9541e40d41c038200141c0c280d030403503002d90703440c2c1d00a10029090303104100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 685326798 1250 685325548 685325591
    0xe1f1805030a020d0b4b01080604020d05030d0f060602010e0a08040b0d1b0309120905060f0903010e12090307060c2d0b0424020711040507090503010906 67
    0x303229921000640b8010303951180b55074400c0d540310110710301d2519018001e10226840401c00c00708191102c074220b00e0b00c0010310000620075019054400310070441704c13100c800c0c44070030700074050b0b81d421101c000340240c107000702c20070f01441c0f150302243c1c1b810300301400d280204d0700e160001c00c440b16182d0104002c4203509000b02c200038601c0b5809810392550f0b566441e5290720840c801c59141141c00700c0d162429001c039612418104422080b020f1010a56000043c028080000d0444009030b1410244080910900310481030b50005002140380142c80401c19083d03403c40c00d07410364159203403c12260b1181e03042c0005a2010080d640558a0703010000030581402c8084d00328000f00f1038820821030100348004000000322001c1c034003010380a10310f500c0301c07030503a100c0039005442c400645e824801040032070fa04000c1004003054500710105d9440e02d41d242644a40c007005000c41585034007202640c0741c03580c0202d8001402d414100700d401c0e5224042030075103071220000c2d142e4642d01c8807429210200e900c080b6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 685328048 1250 685326798 685326809
    0x915020105240402090301020d0e072c060d080a030c030f02131e050d050a12110307021e10050c060a09030f03020307120203090309010315060c030e1f18 67
    0x240840e02d400003000a03822003280d0742d1a21a400b800740011151038650481e5000c0c18060029903981964800744805001a039854900c540b0940c1c0d00040d05e42501c100340300c004483c41d01e40604140043c034040d8217000b0090b081030342c003401062007a03001844e91001408003034003030340300400c0d03240c9684406002c507001d4140c2c1c00b2205004202c2d8001422003100e0b000203460701007aa0f40c0c00540810a074050006040e0042c90304000170740c000b003050050004848404521a5003140210090f0420841e07198441c1501c000455000740415001454109001040c8042902040e294112148006920f1807104440c00d004500e000894030503000c000d000942c1e1105104009110408050f038008246442c0c640039581011b60104c0801c501d5440344962000d042281c90081d500c2e400d0040099440f036100d400b55501280c0361a8402004030442004003040314010380f5031586000540d2820b88210303020f164080e900402182910410a160400185004401d5691641001e00315420360003402281d800c81c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 685329298 1250 685328048 685328051
    0x30c062811031b03090901030503040f1401200f030d230f0f0a0605060d2424030f0207050c090709270e0a08030601180b0301090b010203071209150201 66
    0x2980121000000316030601600c0e440320f19501820302410343c02c5003e400d464a500c1900741000009000c1d0000c060000d49180403110080940e503a4109401801e4814049020801103101440c2c401c0c40a44d0310300303e0740c04443c1503900d52079601161034207551003c108120006e03680c180c014a822847e03070310505149003450b03d15002d4180406990310349030009040300c80031801140081c455041c140c02c00c8004080242c070054a0300d4040261102401c2e400720040102c1d500039103504001d03601c0f031403410708884002c2d00300d01011018004104034812012070820a1640301d030b5007036158482c2480180f203620b010f9405401403841190402950550181c0f0020801420050500c220901c0000e06c40c20b0700c120b40031001c003103100b40c660f545c09001c075400134010a0080c4040e0340c060041c0000114840c10090b43d0722610341c504c04402c8101c00c610343c080c20210071070610050121006503404400c1c44c0c81c0c1401140e00741450b5581312960b441c42007181e03074002000070500f048100c0c070140c980d0f426920030b13000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 685330548 1250 685329298 685329317
    0x6040503060c03070c0b0420220b0303091203040311031501050108040c090c0825080c0d02070b01080f0c01050c1f0e1608101b0e030c0628 61
    0x607980351009405109401000804200d2603402000586401c0d50322482025032403800d42002e1085030310005a0003d142d81d034011100443c80d20150481100c0c1d62219205c410508200e852801002085600b5415200800219a85503a00d0130390311304c491941d600a42e511130840c07030520b101aaa00ca41c20b4003e0b44800320f9a041e448001901d58155003003031801c41040d03a201c0c01c007003010943c01c0d0b03c01d650b071500d4684104074042c3e11900c03640c81065100072011074414908115040450391340c190b440040d643c0c0020807500320b82032005160300c2c600d8000141c10f00020707850310310b84075030300b0f0340401c0706a4070800580c4d02a00c4103000c12100e40c0d07006d007040c6080001014210b600d4100481d8003002c8106909101b4162540991109030b07100f1034582291000c0c11040c031003c2c1c4c00002400364908a00c2043e008018410485c0108425040038071202c2c801c041a0490a0310006400c2140a60500034012404059102d400c05080504c1150b0429510100e00c051a072031803200c20480e90040100400c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 685331798 1250 685330548 685330559
    0x60f19020304291c050a0501060206070c17071a100b090907030e0109050d1106060420070c0b0304061406041a10020102090d03080f010602061b0d0f0c031a0604 70
    0x8890f039881c01c0202840e421481c074048100f01a100b80d00f0020348840840c0d803418001121984040c0c480c00038018104a03d9880f494180e07079030704c812100000000c4410310008001085442140c0740c0150b10f41840e810f00100da514044464603030b00340e150440001c2c204205900c2c10702100000148095000c661a0070058000f03c0c07c4010014502c2041c90389440c261041c058095204182d0286c010302926002942da180c020034440004001000520400010505c6817a0a100303c26541607081d18644100c02000092100d80e00705030804d40d2001d080010002d60344071698001c0d8416132045c0400540924410081e15000e5005050680210310f005a40d0000d000c0300c15540324040c2d000c55100d030b581d0004950490191145c0124113801421000d1501c04040d0000c2d807160017030000c03c030000c82903031700d611040b45d440400701c80120120043d00200300e640c0c50a08000c041104000c03a0120b481c2618482d0130003611320001919002a5035080742034000049152150760a80084601c6854149080d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 685333048 1250 685331798 685331819
    0xa0b0109060c030219050102030108070501031a090601050f0a02060a05130203070e1902120a1805061b0706050906060a08010b0105090910050d0b040c06030e0a140309060f19020304 79
    0x24007907003080c071840100b400c0602d03000300100411002034100080c168080f07490403d020f0f4000388980101440303030200104603917002e809030051a048403070340b080c0b11704180e50411040450160050f81803150401c43c043c001ea4500e4010620240345800030840c0703082440c141022100c0082800c110032480c095000016680411008200c03614440110381c1500c032070380084501200d608503030852034400503e142c1c0c1e4800300590380b0720034801e19204110310001140c1c4000c0340f04055a00030803541041c0000340018a41d090700707c40039003150002c00d0926604c0d981d50070807200103031160700c1a40d20030020031246184c0a0710a0001c2d10b04900240404400d14001070f100d8001c012081f88142c1c0c1230400a615222000c4500000300310050009070310b940b890414141d1008207a0b426a0305182600010036001e00a0048000c54007101005259038101c5840d032104029803050403080900003003000c81110354031034020741070750b08451504541d81e040c209444103000018400100a5404c180410003000504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 685334298 1250 685333048 685333067
    0x90406060e0c0a0f3506180906040f031205070c020a0f06090608040203160b12090303040f110316060906120b010c0f15180203010e070515221d0a0b01 66
    0x82d051007520304c03101402594005c0301c950030300c1e507402103d81c010302400380300f140b01c00d4096003041ea0740781c20400150b071440c105110700300c881a0aa512450204000801400303824a10340d000703242ca18001521440244107840059541da40000d1b5007000c0c603c15883c2152491000b40a101100010325240941c054066640d5200300f006002c54040003406545043c00f10703640706254444540342d140d0310340314445220742085000d0f000140e00e1000081102d030000085a005a4001c02a11441c041c280d6442022060f40d11105d505809000141c800701a81324000c0fa01510a586400301c1075403c1613001882c0c0d180c0d40c0c0716000058201090740101782d810070400c040c440d800851082c4c01c4c0e221400c2c042c81000006805c0000c0c189002c40b00707000104078500040b0350a09c00c40007800380c5130082c45e0150392007040740900c641c0506403000700500903000300000c041410900034108404c0200b9140801c044503154044c040c0c95184614900e520801418003030792101a6a130208202102080020b048020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 685335548 1250 685334298 685334327
    0xe0109020f01031a0316150201060b04150e030105070807170f0708101805070909330801050133021f0624021b09061e090406060e0c0a 59
    0x503a120040e0ba084604444c03288864409000c80e68080fa030703686003105e480d945104045008103601c400e41c01452040c0181c604444004002c5800c00742003107020468459191406000d120b51824801c003592020f0040b1481800b554035020389900d030401c0054026034605980c4c88a1151800401440c401c42a0404d40c00060a28140c4610354400b041d4061113030080d0800d982e1019084002089520f1503080203204907026900d0601103680d0318420820348031601215641c00c107034402400f020801c00e80101000d208442e5801e42e006654040107821204282c100c0400c030302e510034141154920300380600c0100b41031842c1400ca47d1016240080d183d1130203900d201241228600b000d00c400c0d1494110b00b0260283c002e200700710049a0210001555074183c4c0764004d40900452022034190f007848103031000b1005030071410941d8402e03003000b80c13070403406694140d100a03030040d85800d902c3d1804904c4c415480340c1400103840f41444200d00c03c01c0700c0100340d4084a42e003088801c1d0110703803180603111882d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 685336798 1250 685335548 685335551
    0x33050a270209041401080610120305031305010f0906140c0901051803150708070f0e0a18090506010b120109060506070b040f02030d02030715060f0608070c0b0f01090e0109020f0103 79
    0x50b0a00002805840d0040104029500100002c85d01500109010340030b50080d00c120780c0c185a0710310000d240001002d001030003092003030000600c004043d00c19580c40f18464000029406d0400f60f030700e02113444401056851503038403500c000c00031301d2004505801c80d047c01c551a0074001030000084c421712840c000c45c40d40c440040752030001074030700300300312048004510340b43c1e0b51900d0710f000c004240403400c0b228180020300b10382080d410903001d100c05403950700024000d8071800d8100040c2c00d8080c02c00b40c440c800516902c05046020070024070100e80030b010000e924903038070300380d0942d161341108068104c81b418900d490000c10041c0e4440c07044410460f400501000c0c559500e0420180310420002c010f034241c003882d1003070040568040b000340110740c0320380e44410740010190044400c645a40c050700c3c140700c030303009800d002d803d00601c0440c2c2d000c9020700d01200400d425944a8460030b900340e503da81c408401070300502c0108040c1c02060b4a881420008100e80c01d000d8000440c0500c3d0b40c81c5007030525 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 685338048 1250 685336798 685336807
    0x7090b033a0903020607081801033b120a110f07030b0408190806190f03020402070503040b0a120b010203032e030b0907031109040c060333050a2702 65
    0x41e01900480b001150000d200d1600e17001340e420115100d521a84244614031414120700c280c42d8001d11954240c80351504441083c0248205120442034440700a924000c510703d080144822007084032a000110644120b612440408006005d100c10b800c4080320329041005614442d03040010150101c1747c0109041601e0707210b9040c0b80045104c2d409102d21074040780802d910965402c9046180108015108000c0c00b03e01d074030010031047c100f805039845415042e08100050302c0d0540142203200d00030300c2500c3c071309551180004481e03031040b00741d000880e2000320401c824035680d200d00260954280003a6155142a51042c00302d100d40b00f000c44408201150f045041c000110036140155030301400031800c030304100b049180d0390b62031403004465843c2a4209500715040000302d143c01030f0380c8130500303e03101402c0c60000d030007412101160141c05032804095a03110b00200002c01d40d5010340000400c810380c1008180f1442a206400081c0000c03d0148504200c082a05d004c81c100c4c0c41184005844 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 685339298 1250 685338048 685338163
    0xa08060928080a02070509011a091306120b0a060b28031113090c0f020a1509020d12021011070f060f0e0f06070e0603011e0807090b03 59
    0x10505000141181c03901003041c1c00781c113400145440035a103013103d2442c10f50f0383e00c1428480400c640b070078401d6203090a000b0385551313041044000e001c5003802d80c0301048450f20751041c0c0301c9072803080034240c51203c18101403201c0e0310328030f1081e58040d06195030480c0c58003041d0f02c40f5800c00100040c10070090220214a00340c164403035808081c03404500d540f41da41e03841052020210484c0c10380035000900307107001c140c0300c0f50500510f80341c807a0101503005000700c80540e440d08070040c0550210704070b441d0b45410b009001130359088080181140300302c40440c40689116002841d2052440b4005070070b600c2c1c070202c2441010307100b0694500a03809007440608928603c0d046021b080244d001c070010703e0418108400c10311001c246e856611078a0002c88590703a4801004135600e00344804420f8000200f000113000314441c120300d03006001c010b03a00b8403170301a5990002a14105056211240c1966152034100c4245030a1007194601045000c035071260488a41070f0301060380b4074051041c2000e81c00c2c1940400b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 685340548 1250 685339298 685339363
    0x5041b030c0e100509040f1505210c060f04030c0b0c1c051b0f030408010e160501080408090d0f060204051203070c060e010c06060e0a1d100f0b130b0a080609 69
    0x50221f05501844103400d80030f400c0a200501c0e004191088031750072415202d211701591341003045034a0000904d04002c0602c203100c03107940241c250401c500388c204030200200e80048201001401600300050f600c154000c0b09605000400351010307051004a06c007212180d92140c16280382b40b060460060502015080c00780c40d0080c003003480950f500010600090301001035010380a4076400e401a9003140004400101540305a0f0003401c3c00710b140c800218000c80c001c0c0c80a854941c4024214890fa0017990700c95040030301061104a85950b00020188580e00700045040b0240d281c00c0011030070000e6580d500101460386000c0d40040000a40d06481b2a80c820f40c94540704a4001a0412809407a25000c125039001150083c1200d0f040c000000b42c0910224800d410060f18100031701407003107501d90f002c80540101e9540b9502c0a844c0c0016980c5c69031a03180c02070840100c60000101000c842060001a0180380d01c4182e4581200d0100007909002081144401410f111400c0d011000308103903d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 685341798 1250 685340548 685340561
    0x8010b091315080712060e0f03190522140a061215150302031006051606110f1308190210030e160e0702010f0e0a020607080405041b030c0e10050904 65
    0x42d40c413820340001095100860341a40180c0030f480180b0080c020303c9400342da40c0e881540180e01581c42040090340c9010301e501600c01859203071504a00e0585807070444103201201f160b00302040c02d20030b00e04120b6080020241c0c202d8080c240d8020710503d00d0400003914410034113103441100c40d1110f2285088490f80040d0b10301030902013408119070039851a0050094104691041c0350111364500428a83e0091040d100c01d0000c011020000326120382c2c5443c003801c1110415442000184a402c000c1002d86020381141551448000d289500e0b00da4071900c2c040342c200340501c02d08502d005100160b02e9440c0a08981e29441c02c01088100c0031400302da1503c90907044e15800b45e40d00703c00c0031807024998a10703d40102071660080c4180281503140d8412100c00e4800b5102e564440816400117040c940d020300100d9028a596038205a40c50000ca42980c001347c4500023452000111a20500c0d0548520440d98101d481c1805451484102044080510b138056000340714ac0030801c4001680c1d141c101740c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 685343048 1250 685341798 685341809
    0x2404020604030c24030501210615080c040629031503150411010e0603011a04211a0103021008040807061a031e0d05030717070c0308010b091315 63
    0x4110364810400c0c01500c07144600c461003820007410034054078424041c0e14141d13100400841a40e000006114a44102345a0101c5039070b0345035200e0703a1b000c00320f011490340101507020243c21140808801c1008941a90700510001003c0182e425100d540c82551440c00e012201e192641e41e40301c07103c2001c03001036903030841a450b200701802c0003002421401640d018500c5142013502c01c692401c0190760ba500c14485203074100c40c05000400c5024a003240004c1e8141d402402d40e4078098941e50b044203000c02070039103100c11982100d001d4081000004c19040711031182d0404410a504550002d144803002c010780c6002c020030580818140950082210b24840d070201d410010b5050b1180090790b0001c620b04414460300410304e4001032155800386601c1050038000203084004411481902d00790000ba000d00c082240c2d8443c0e807411941c2034203105000c2c154070b07168001e1008a40c500100405016004004940d00c01c0c80404055110301d142c200780000c0d120780214050b5456010f1002c1c110050313010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 685344298 1250 685343048 685343063
    0xb010203070b04150e03191d060d05100602120d020f041e0302030601080d02031213080307080a0606030b060304030c1403121605040312080402010323060a0503240402060403 76
    0x6010401c500e0003008103031342500410a10071200740f0350200d41c6a014901030000c00d400c0c00300e03900055a10450144207616141048051550b48000c0841d070950466042c440100340d403a0244225030300162280f000410035440109000300e40340301c18907014010b024200350b020303030041501c000300028101030798090604220a4002d506010540303070300c4140d607031005074080d003c1c06002003107101010510319201405500110300d04000394440185810700100000c0d0030444016111f0001840000290300403185944c0c1c1d030306030b81408901c01044070410350041d81890324150001049480d2507042d254403a0b054200030380110b10f0350400b0703000c0d41c01d200b0444685020010f07080248a40302c4151034001c7c1042c2021640144110b0400d507502c1c8103900015028050142c3e40c0e1041c20310441043d94000d20600d0081801c15010507040000c0e00e118003290301c4c414240702000310600b00a90b1040050900710014002500058000c41c0f45458412000421101042c00601992201e030200c40003117030301100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 685345548 1250 685344298 685344301
    0x21807210209190f0e2e150804020114031305010c090807170a02120c0d0b1501020d0f2f0d1205010308030708070309060603050d1103040e06040b010203070b 69
    0x340e0303400950151050300d210b83e4101c2a8151003c0181c40036000f9144554440000542002d1481a0514004040100440030300340d900c5140c0311030003803a010b0340d103d01c8800303c00c031400d110180e40c0300300505298804100d054010080581c0e4041d441142085004581590325200d1052031034400f000d0700e00c007810540c20898958052940414104115200803050710100c070f846015042000f036202c100011260710840c4440302603d000380007210b0503c601c0f0119450910180003240380402e220800341c0b40086c1080800036205211301c5800460f940900c06400800700d540009480b540c25541c00300c2c02c0103500c0040c80300b140380400281b80400c0301c0c01c03128503001c080586010380d40c01e100f0103a580011a820320310b210084a034060507059036440f5025504564902c68212501c0000400751800c164807042520040f415901c139903800755025a019140d940c04445001d01100b51441c21551642e008103c100810605004010b40100041714003080c5079014100403031560013038040103080c1030f80300e80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 685346798 1250 685345548 685345607
    0xb0f090c032a09060312220905010311120601091d07030b0a0c090b180103111c110405010903020f120610060f050708070204050402030118050a02030c0a03021807 71
    0x4520b42e6010065556032400306400a105035800144c810541542c00340c2c00d8107a40c03140d800040c02d4040352191400c081d440411001c91040c4a40f54010b2100c1c51b901c40050040c000500421031035010141e4040030300055401f10141e4841c814446e50b45201d650b10106205d45011401d14440ca00300c0a0489000c6610707810314042d001026222614660f250100c050f10290140700380740100ca40c003d02c0b082c103142c84001d141450900828000e410545e444d43e048100c0084c02001c0c1c4000036070000b110800c44044103030b0004654511410920000c014003040000781e9104040c042a45e6055461010000490300400d00405c03802c1c81404141c01420100f010080d150f910f80d0f404c1360b00e02c1e607a59400303410800099810f8130036400f025140280402c045009810075802c100e40291010700000f80004545003c1c4100c42001e40044402d030b00700e80030640030351070b0800ca0800000030440381c0700f08075803841e0300003012030800d2003001c0b82e01c14003400056512802150120521030f0060b081006202944 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 685348048 1250 685346798 685346833
    0x1602031c09140d080318070306060303030b010e0109050d02010c080d0e330106030c021204140108060a0e06090a0e061306141b0c01180c0f060c0b0f090c03 68
    0xd01588012200c06482e481e02c80c03401c580c0c8008101d801c1a1928510313266a081000c02c02c80d2900310035002c3c42400300010000c1c6c21840307080000e60007503400049091400c00014802500b80c40ca944c100010700009214642d01c0710850460309909003401240e04c000da142c0044c0e00e0180454010703156103420f081d0140010b020400301c0f20071040240c80b030809100543c11040c56040710384003007075080001006000701802640852002c0360310340100c42030303103008070295800c60303005401c07902c444444001244019600820811b80044003200d00145050900744451003d2134000c100b10b102c0d00b2560040b0301281174a90002440103142c00603100d80c1d1a11303105002e507004078100304071042441c0c1680710241440320403c20b4003071076080c0006000074682d0302d008003083c0c208900e5109155618288080c00503a014013a000651090321a4985146403403050b03600c000095006000313126100c10044c000481c01184c0c95842606002114844d40703c00400070f1908034800000c9030580714189152441444d072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 685349298 1250 685348048 685348067
    0x20a02090a14070212030714120c18040b0d080f16050c0f040515010806041413170703140d020d090b1005190902031f0308070b0c0304081602031c 64
    0x42c1c0702a042d03500ca2200c1280d907409180c0120121640034004544d48a00c02c40c02c07440102c00f4441014104500d42c074000454241c00d44000110450010706251a450300301080c080320344048604120f140005004281c5001d1400e4000382105000201100701110b10300c180d03111010ac0320703800030a900030341c41c180342c0d540c0701c070740201e1b109525080c801d852515140c011a846030083da111400011041e00055a00d2030028003034550094880105140c91000365800912501011255207812107160411010100a8400c3c01e040107408000042c0441c4d0042d500440ca2000d9642c0035987e400d01043c480000e0040d6084018a5810620b149061103840d01c51140107585420807881c12075a00c9040156600e8004580b01265546040400003200300d81d02860b8002c202441342244e120042e902d84c1921a6150000c0b107441c0000300c3c1010608c220b07002c005601c000c5081c4080c0c95400d040d00d030002c050081c803c0800342814084061011510240110807914035000920313922400c614030080c146074070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 685350548 1250 685349298 685349321
    0x1f0c080d0e100912080415020a32030112030302040e070503102403020714010c08042607020d0c030c0b040512030a080c070501200a0206060316060f020a02090a 70
    0x41403045000094140308034124164451840d16100350f000005032000301000b00203564039000c61a90410455503400140600155a50ad0111465000415020070500c04404500803140411201006a5410200c9040d1131601196282c0c000051070300300c01a1145030410310b8084e20754024403285a4009002d540203a5000c0b40001c552501d50062000041201d0070741c001d0641c50f40100a42c09001c0e80c0101040e50090101910011540c03c0d8036003500c5401c0728101c00640d00c4002c00080c0301c2001c0525460542d04c00e03040595203c082d003503130702c03e000d140f60280c4610000324038801001240d242d080300070342d0701207100c0c0b44040c2c1d142c540c203403581c0107407103414040d01790103040440d811030200c00c442200f106a121512a0f4950086000342504444022940340d9030f0b0b4209445203400c9041c0c0341c0c0031401c490040c903070384440091000b8104100541a50700a50084460740c803214a100c0c0700c04c0549003103160100f400348140300c08038036100c05841c0181d04070b09181d050009101c80707608141000031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 685351798 1250 685350548 685350553
    0x90901211b090b10050a0e060c071401110f0706050f131401020c0405010b0706020304020d0b090105070e040b03120a090b04150810030b0c07111905100c021f0c080d0e 73
    0x1e12100031311440c604025038680001c0d200700062107117640500d038100300f01d4002800560500408090503458062203801c002002201c5000842107581c0c0507031103a003810f030644080c180d11880c08080a0f40d900341406200203111000c142003c5552410048d41c51403510b440038603644d20340d40c0ba110003032a6200c0c40b02c2801030254030700208003810a8050075040351403103907101e40307003400a0f10382000a4201403c100da100c21580070300408140c0140c2d00038044c403802000001e5a027030000000d081b01c183c1d503510320302660412a940350280d40124030080140812040c4650b10f400c3e03800f0440f40c14060f0b070032440c4075850201d00032948c4091419802401c80c20b80d120344019448044031010385490510000b081c00b103807540020381e1115486c0180c903020b441f603d10318602246090010308030010010784c081c0503100c0c000c402c03c03192400700700f007501d10416818049028001500410b24030030007407421a00c10f200c4846071402152141030f4508070303a900190019240c0d22000d910802a02e071503030400c50340740b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 685353048 1250 685351798 685351811
    0x9130e071d15060c0307050105010905220f0201030b0d050c0925030f02070f1a010501050a02030a0e030c032a2709011508030702090903090901211b09 66
    0x1c56008080e8001c41800003441a0a03510b01035250000040c110728160003060078000300907290401c00c00391031581d01c20400030540f0760520018404840c2c000b01102004043e016800b030840900790350240d00d1580024640f02c4401c500e000507005001c0d40108590022000b10708901801b00c0070aa22a83d12001c5855403616190a10081c0d40020b00300b0941c040007607840080000c060080d440380c44409a69034025080c03121540340c20000d040322280654103008600d00d48c1c1c6281d540b4001e0703c4e002d403100742805130912480510081d030303038040c074060001440034400c10104107560030000720b448504002c00300d8681c2000c0c0311700c490b5041000c0a5100460f6102c490803420352801900000c120354180c000c6600e0444042d01454821350050f04160f02d65623140c48044a011610120a000c1c02880000750394410303552050050b41d8400501c21405a04103100d0710a0b603690f02e242e22411103003040d203081013481d403074045070b05035003001b03100141140045109810000f02007400031042307801d4040d0403c401d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 685354298 1250 685353048 685353059
    0x10e190306110901200a2123030c130803030a0b010807090b090d1407080f250509074109090f09010603020303041404180816020609130e07 61
    0x482c096540003d000c43e0490300c1d402c040e19404401c003201305c1c04d08012901340c640030303031114020020840703d058464034000c898018040d400c044078010b04410741c0183d184607024100e2801c91408050201c2448801c0040c1c0d80010520403000e4001401e2400d0a5903603c0c1010701554004055400d0114041200e140028400501810142c3c0c1205c0c00d25411905c0c080c1500100105034001c00021241144c100b003000c843e01d00100b11440c003030201d070401403100c0240144440e00e0701c401419004a440005031108101c2c5058a10660442e00152185101921403100943d0241c40800c41a2900c056201d10360481402c441c00c403032901404d5942840c6a80c107490341494092051880306500119aa000f150280855401b400d0b40250810f0002412076142e5002904540c4160720280e0401c1101c101441c00d41b615102e014010b00300d042c00b054810f022a03560303038000d00a40c1e049445c1d8986200c18441952204030440300c4408008009500010145000600074614550140d0103441803e07070110b0b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 685355548 1250 685354298 685354331
    0x20304030305220b2203080405070801150909050c060f190c031b021c03030501080d030507020d0e030304120b040606090b0d1704120507080c0a0e010306020702010e190306 75
    0x103800d0f0440161108003040c1c0390940c00c0702c800340003110428403da00e4001d502410007804400c9621a907520342850400d41043d600d000a070750090842e40c2d25040122841244107c0307403504540e100103002c00c04802ea41403040c28080181d02d005d800640c009030701c1c00200c60b6100100740307080c00300030902440003001000b203c6032074603142e0003400708904185010310f09280307642000c15544020011490360400845d42ca00d05035403000100c01198032200184190300060065040824041c641048146402d41c0e0080da180515480981405000704016013035450910171500503280d0407890020450880c5400d5410140403901600d10f0782c44d1240c04940e1002c54058101c02c03c10060040e41c4644040d260040e02650032200840111000c03c000240340c0044c0c03021010307190045000d440d49510f880500c50501d11803040e40780c81181e4090041c00300c41c100c803c106d0b043d660000b130016143c20303441c4016031b0b1030000858170781c1d0b004043c0060300c40002286003200741682d200705001e214400c8080e51560 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 685356798 1250 685355548 685355581
    0x7030914060a050d15060201151d011e080a080d1802060301050411040e0403030209270705031305150702210909060d06020307090608070824040e030409020304030305 73
    0x181e11440800801031594401c4000d403104140c44a000520049424070340314403075800b6407142001d40d4580c01e0001903d5200c20041c0700400514500300d8000015941c00f145203481401407903485850380d2030007a80d608070140c400002d0315a02080350426002ca0406a120b50003071019032000c1810700714402008051079007807400c29980500500c0c2140d00b08070400010f010305444061804106000024482410505090169000343c43c0140e464002e14240403902900302c81c0207081540e006400401200116025a8804680d01c0c0c0345840e85c0741e0803101246d00303102070400350051080000440341400c040440c1409019940c08848105c00d0000414101c002c906000b1404100700380481752850510701d80c3c03c2d80c060001800c090705202c02d40e840030104c2e002518400300050000c2d01c2072107010340162400350403e0560511106514003041030341c15255101000d10b641d0107440c2c090020b591116081742014420703802c19a40c80766110a0360000130741080743c040d800070341030501040b00c90b12401c0106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 685358048 1250 685356798 685356839
    0x120316051c0314010918051e0610060206040b0402041d061008010b010c0b0907030804030506060306070e030c0f010509030a0819030b01022121040303050c04121502120c070309 77
    0x80381c5e1030024410000c0c440c002c0ea00b031703034031440d0001040024800d001d400d0202a241100300031940034a010a4901240106181800f030403410041c01081d400080b40f5600550241905225540f07a00c0845c000e0580500c41400c50b00c0002011300b80076102181e11840f40b103014540748030305907030341d1410b03400ea81001400b140170540c03000465012603c01c0341e5055000caa11001c80b0b011540c1c03568ac1d5078090340305070f00075601500100c00b400980e140a0103455000710180c500568a01e440c04002030312904c64019040c406c904001c0404043c1e4061004d9801000005098034022030340d40c1000c0d0000d902a030740000c0c2c003800b400c0d0750b0700d80140280305640a001060780144408806001d100344100480c6008114a500a001070740a01c0c15011415402c0c610541088869040c90b103006415110007400c40d500c6560f042c0001e00c140c01e0048018507002d034000c041c1c0204580c1d90502c01001703100d030341160b0044e054007008006100c005130700204100c40c07103035441c08400c50760748085030300c40c01c80408036 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 685359298 1250 685358048 685358081
    0x70506041a09090709030605060f130905011b0309030809121b0a080403030302040503060708010305031e0702040518060702031804050c09120d09080a05060105120316051c03 76
    0x740070007104207103180d8001456440795441c1510440019810440840c1c908000911002042c030070024a40a116040740d010b0384c0e05030b40d000d03443e4000b4144010030f61082039641d40d10800c2405229094201b1000c0ca40414080304035a0140c6900401800304a0810b8001c01da2079008503803020381c0040d80140c0c0d0401d0100c4c440c1004001d80f014000b0303088000c5655054800c2220210206802c4002800150b110380c500580d07940ca000d05142c1041c0e001845001408200d10041000c42ca01004961640b140300424103c0c40d480c03424100c0d024010054069002854481000420040e1608032500c000242c400c40b81d69039076540040b0b80e01d10580291503201d407010f0881d440c2074205a048940c00402c0150441d0801c801140800c40c03100080700d61a2150f8000a14804031a4010340c02398082c01050010b4480420561212640d640c81846468000d03001c020304124000406d0082d650040020030b020001710459003041540c0b000c50050905925507550590b84a43d8001e118a00e000d8502884 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 685360548 1250 685359298 685359307
    0x10080319030903020f03120f0105100207050f030312010923041a061503070e0f03010e1f020702190617131106190914030a020a0b0f120109020c0d02070506 68
    0x30214003030100e5042c120254801c11041d444d4603141840a0300004d105907000c40e425180c004500c0c0d440d40e50682c041801500103611010030581d0100d94001510402c0d01c811682c0040040841d144d81b08000019111044403400401c5400722a0007201070f19001c01a40188103142070400c0081e1b00007604e0003800241c900008107425121600741651140f0014402071080c1705000c0b40e0f096540c0708a43c0c500004803010034145041c80e280400c14850002540200185c02c1803801d45599000c0c203000091020075021141c004d40d100c0c1e50105c0c2e1f042503010b840003598045a803803034001c903142801903c0110384008402c00c60308004d002d00c203104500c2c0505070507c69040c2e8550032454110100c032540c10420030019007602101c2200e61250a581c070b541c49001d524603140500442d9920380c13201d140302c0c2d00050a080c1c0940d0300d00d607289040c0d034454141542e5610301507405010078412040046800f104c40000040e01c25002e84c094660092a0030540f40310382000007080f40c646c401c82c0a0380b68040418007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 685361798 1250 685360548 685360597
    0x30605150d0605070c0b07021e0708100209060903030406020601181404110d02060a0f08130503040e151c02010e0a050a0b090a080124090203091207031e08100803 71
    0x2003102d90001010304040003d40c05c0f81d1141024540c0031500b59000da400059506041e1145c0d624141e0383d0b1450f64040d004403401c141000c0d80f28450300744003062454011400384d502d80e441d42c0c115113803a0130007022030b85e46954411740a51940c009100384550b606240d40b100c00d40e5902801482c9000e148120307907846a41ea95556802e001c00300c906896044000c0c0031040006840340f45c000c250303503032840c0c50360560b4140342180207004038001440c1100c130403408001640080d0000042d03c007a0b410042c0110150b40c0d45c0e507004008a04410b00b0158000d4102150342d14503030103001489072481c003c0ea1003040101014080c48487c0c0038501c105604020600c9080003048910005060103401c000e225020b55596441507030b082d41d0b0031a000031480000020f41c59600120708821000800342c14009504602c1c04140a9840b400c0c2c1c05400e111100303001810030201446602c04002e61207814040003106000008024080102104ca400301810109400f0130340440c00005e0322295800c00146a40288210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 685363048 1250 685361798 685361801
    0x30c06021b010804030c0c0e01090b0105070c05010c26030a060b130b1b03070501240f0b0a03020712090303180b0d11070b0c030a1505012010020c07030605150d06 71
    0x20030607420009001b400720700168003c074074080185982450800254148082c0d4801ca5007a1810141808010020100007440e000380400850b4402d080c00d0b82c114003203080001030b45c034000c0a03550103130401280d40360030400c21001443c014081e25800f001150703200c5400010511490700f1499000201160400c600d00c4000010219002107081003550844c0031016a455900004002c6481d651552501c140340e074402010003881850b03000e00741d0301113890031076400c80e50f9006014000480b0b0000490340c0c41c0c0c502a030111005a68000d0880c0542520ba54000700100d1881c007044000132803004c204003640c6041d860540070f071481010464540321103013039800e0080a00300310f04100500140110001300b005042c2440c0b09040300d5560503600e207080b5a0400440b07006503420070b130174602140c00b4840381c1da0100040c0e81c91808070030210418600d8524080ca042c6030320301000c51180c000906460000c1001c6072040442e841004184029140c1c0342c840d8103000c400b68600e0b604490b211582c0303004560789 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 685364298 1250 685363048 685363051
    0x2402011107151e06030510050a02030c03040807031803060b0a0501110c06131505120f010e01060c140f0309010311090f0d0c030203030a0302071b0e150a0b0c0106030c06021b0108 78
    0x6604a0302e040c041083c1005440241c1e1007990190044604641442194000d8541c800a403800461441c03818510302c2c0d20b03e02014001800002c00410400d040500513007103030404542211003261341c503541e454810050f04e4441c020900a0090aa00280c21750181e840700702e068104c070010b0440740309140300b485500c0d005020a01104645614001040c1e403a0348084140c1d086241c1d01d165540d22171030500907a0007800b41844d03a4211110004109003400000c502e13040d0f503910b1925103100100d44c201150344070070780140e01c4564002e811240f04151400402072106020a1320180185681c400b4130f40f9880c02404961900051551000e200c035280100801e580c281c81648203030500d6440750086441c1d1381145030070720082640041c0d201c007030140c0114440d40f0072950340c3c1e000b822a42001c024195554001c0d00d080d80010503000d040f02c26540c1c4c400300b50054440d24a50076121301c50350720701c02d000e082c1030303c01590161600480418068404901d0181030900341c203854007003040000044981850 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 685365548 1250 685364298 685364321
    0xd02060906070804053102030c21090f0109170a051c0b0418020a0311030c0607050105180d0503010302221a09070f0c060203060604240201110715 64
    0x60410004055544074000782c248140500304070780c1c032103041c03070140b05a5600341c00008078036150480c0b004680307000d003041002842c1400540541c5a4648820344800c60282c201801f80c03040d0941100300d181d541c0c291041d441950601c045407a202d03003540407a400c0320300b4814080c00c04842e103a40b4001d203144410041405079843d00e015031a10060301001700300c85c0980c1c01035010581d00c034201c085041c41d081c0a1404010086a40c039006203a050380000c80e240c105100007090f443c20003000118076907081c00b00c000ca4450241c0a183d48808601e001da00a2100f1103803940c0100400328048111071000580c0c4001072220b842d078070300d1a4219001c204504006c0e001d07107408085a0300e070f161401409030040304065480bd414424440d02a0f200308a00310f500100f00c1d10404c01d41c8050071048690000680c590190049001640ca481e0200487d80600c242e811166407000c1140c810042c00f00d5403240100d513004103500030841c0b040c80418041841c4a1140003801c907003842d8000403a560900e900150907101e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 685366798 1250 685365548 685365559
    0x60507140f090d0b07030504020f060a021b12190213060302010903060203151f021c0906030b0301110f1b060c090603060406031205250c030b040c0f150f02010b0f0d02 73
    0x750136918446a0740d030468046001070386401c2400308600741801d00150b006400c4850508041c52078500a513a030901c0c085035000400000035030081ca84441140b610382c060803000384d0703d691051050481c0c64412800e0120b0041d01c01301e4511000a4040c411003098a43c141d4443d23414500d162500d001a40010f0807807500da4030343e08201aa65500c080c150010440840815101c11a040001904004410514852158144000d00005984058210251082801e00096100c490700202c0e004150485118201050000d410b94508243c2006400b14034030804400340305c3e036400100340342c0710b94080e511005140f5041c89221270a2400d5806160b11030304c0900001890b40d601e403150707541650144d0b00c810105000181040c001d000250094a032400a4101c68001c140f0603a150310030304c1c50f94170001e054941c038070003c03c1c100700c00d00d0310f1140100048103580320240d468420804610040c02480310102d83c050401020080c010301849100400051140040404035414021560050101264041c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 685368048 1250 685366798 685366819
    0xa0b061302040f0f05011d031f090b090f330901020d1a0a080c0904060905070f0801020d05011d010314031b031908191e18060507140f09 60
    0x144020f4a00a004200c201c9400c0011031400d00098002d502072410520a1402006440034589001400c0d01010203044200303489440101d581c84020110020002e00412540f07040c0b0242c1000000c00048400d10101540c82001c41050002078540354000a041072290840c0c000d800444138105065001c412040013600c0c0c0242c1c490200e04841c5890f826800100103086000c403241440c03100003010b0519070000301030320120680002d0003c0c0c00140000c00d41510341d0040401c005040c0601c0c1c00418924814441540e00ca2503040d010350005951a54000c1c6000000142c1d102458400c05603030203124003200e2580d0a54036520703240000301e101e80119210410401c8201e150b200d401240514200020f19180c9528200c3d00c008969001d4007881000225400c2c08940e9440d84401c1341c00010100e03000494030240f00100d510090048101d0744458502080c20f20701e28402200400690711401c001c2201d983c0342803007507625841303401100010030f0b0b0901c150740c0701c0003080d030060038008401840694071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 685369298 1250 685368048 685368059
    0x30506070e0f0d030305040b0c1e03090a170304030201051b03040311010219030e070e04020310180c060302030f22060203040206070605100f060e3d030b0a05030a0b06130204 76
    0xf0038000340001c0f00040ea4840810013480b003c40c00c0e207904818850078180c6448000d06481d080c240f40711040742d070092800404035111140030440300d99695405020504000b068880e403114a81045409070090750820000490b46005c260081205115440d4100c0c1940c5854508407819a02e0041000e1070f99030030050380395034028200d10080032040c6644e0114280622804c0d071410700f2265070200c8041840300e0305200c010303038002c200030614042c8000700007803907140ea41c3c0352400c04402d840080d06c1c1702a40b45d0040780c415410340045115400308501ca5626031203050b0110707012444c010030f482106288219580001d02190000c40d0000d0000308224106041a15204129030040c2d8541c2030034122101c04005441c1c201d800c2000510050030190840100100890a0100c114101c8180180c418101101c0302c2c0c4076101d4644402007207542e0308500138040d4005002001c1601241e440b905507004006110300c5e0003d0010b001e00d51051401020f6141d02080c0246040015242c444054082c0070200340b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 685370548 1250 685369298 685369309
    0x5031009020310050f04060503120c010908030103150e060403120c091a13081603080a031d0c0118080d03020a1407030801090605180612010e0a1101020d050301030506070e0f 76
    0x15114080c840040c180341c01304101d1400940e801403400317141803005c108480d0b0f501080b04030003019040c8020750b44010642440c0e005041d04a03000b45012000300020060003004e5488129001c20705100300100e60800d20401d076034101c105c0d8000c0c00141c00100400b801c0450740c004071002030301c6007442c0320802d03103519011000480c400d82c281c00042000c5040024042c00c2c02003400204501c1000c0e108d0712a0345201c0c200d984003940406050020001440c1150358032aa0007900c3e61034140c5680400e400016141070340718450342c4c60392800130310a0a1058002200241540c048440d40b20040c0700500080070207a010f500440c4000080c0442066408001000301009010f00c074440d5840141660405103c2c50442c1c0482d04894001e0840da82e0082e01c00c0540b09000341c10000880d800300030441c03604200c40c003400918080418a028043c0440104180c410b00c0001011090b002e071039450302107d00446e0540000d01c400303010b507400301d0041080540a17040868044030f01500100610000c9404100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 685371798 1250 685370548 685370551
    0x120e070302220908090307150816050903060f0109110a08060904060b030312010303170c07020906060f040f180b210a0204020c030a11070b0a0e130914010b0103090c0303050310090203 80
    0x102c1381c0c00001075034080c1c0d26052104c038001d410f160041d00f0300c036100660300501c00e0360020900800180d20401008070a4018410f68100d40380c0142110601e1400d01d0750507414120a05c0f440f60142d003444d46034075241035504282c6009411903521b000e1290b5482040001c410341c09801501c0300380d500d820481d4140c40500040100c1a0502c1507045c6551462600605c401c6030154540c009090010030300554103017010803a01544d80494036001140ca82000084540c0320300820b01e9079032907000074005201001810504215850b0a2a6100489901680909035524840e03016400001c000513020100e05075100380c02d110b10100101c070303400d40c600e1340410b04a0b408060001e441d03034008910217090560007403020100031460005401100d00d000035264260140205000c01e00460401104103030300c1d0f0001d1081d00105041c0240001e50041c1081890000e02100d1000c1550811000401d00d500902401158079444011055000d2a40e1011209030304068203121b40860500d0000404440394006035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 685373048 1250 685371798 685371803
    0xc080708070b04050f01090b0c07110307090903020105060d0b061c02090f09010515131d030d050f0a11040608180a031e0306180507051e0a120e0703022209 68
    0x70030b41410641482c5142c82c03c55803a5480c1e41c0e041c002d100d4000b0b200d44031159006081910701b00d0322820f02b03240110b50344041d02e07052a0544506040010041a19005a01481c0c06038000300502d031110014050010002800034004003480c0d404182e5504007000504000e16680702040748511103a40018038640043c0c4503000f40001190901802d08070a10404e80c00c0684460381d070714000034000205001440c1b80c1d2100080603540c1d440d008007514464401c101d0340000c181900d41d10090b8100358401040155900d40814541c000003c40b081050710400b0181803012243c0c0e420b003441c00c04100c0301e005004016182c00052412889240e03001044080201e600c05d440750010b81200003052062140c00303c81203801c0500f05041008003041030940c04440b43d6000300d0110789540c5400c0e0030b03a0b00d44148070740a0744c141ca02d000700b817119104460160228414036a20314500280a21240099a0b9240c40d005040e801c2054100014600405000109008080440d140422013508070044a90600d0207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 685374298 1250 685373048 685373063
    0xc030609050603190803130f2001050406021f06030213060501080a02161205040308031006020c101706010306080304080309180702060f1918020a05040204150c08070807 74
    0x3808203603001e01807180c1c400015001070600c88488400006500203029014143c44400408a010040c0c80c072000c41045400185290024240c1d03d004943c200e40716030341e815541094041014551b01c1002183c0131202c0540c01070901c040f209010710032107404051881f009a5a9180000c0140c1b68100045020b003903001c00000c0300c610740f00000d40031010003814400c9140c41006084400c90300c00f000a0b01c1103800015854588030b661000f516280300350b030800341c1503d2022007000f4008504c0b041281c15540306509503282d034401d050070721600f25a401141d002181503007034041440b40380c04824640c03010b01450007182e190f81d602601d908551158100e0041034000144a00880c2482c144410009402000c0c00c0400d2038800802915044040d041c451170101b4a004a2030a400c1040c03503400c0300c85151420803400342521080e03400700040d004105d00810705031000081038a454400d2f1400c0b903281411000c441f241400c000c50301c1144142007101d83c48800e10075500400c11441c090704103180300707800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 685375548 1250 685374298 685374311
    0x2503020909070f180f12060b061902010c0e1e01140408070305210a14120709031b030b150d0804090b120a2f090906071202190c020307090c03 62
    0x1c1c000c1008012040e10f00310004009820000c0382200250002111b0011600ca103403a101e500d0294017a00690f00400d61000002c121006000703101361814440c16680c0e002003108000840e001e9849580c0c60a00a5111b050203c180000040d000600503901c0c20501d40030603042105d56038030303509401981228919511008041c410864104094882074985041c601c00d01450258465818842d60301d82c0720401c4646880741040404d00000e58584161680d00c940103480e210300001d140134094401034036590554014614142640c030742c05070540341c2148081000d944c41003022490018500e00407504540e034114548085849400980068580241c021594522400420451010942085d101c60304410011000200c54241d903e903810703415021501e0f0160204044e02d0210421105075030021101c000700301e169240130410b14403071065501d410110090960b01c5000300e018018013490302d5203175010366180c4240100325403060103100a00311203095840e08825015100707084510340229882c0c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 685376798 1250 685375548 685375577
    0x27050102030a0f1a0103090206040902040e040209130515060d170a020609150a050a1b0f02010c1d06030a020408030a0302211303080406060801092108250302090907 72
    0x9040182160400280064400c3d5424140e9590680c0c1c070481c14035981f048804115150302040c0c0d001054900d8045448995501350711482c1c40c000c44040b441080c0c800e000032200035010050031030703644d040401885640b110300110130358950302426a0341e0001d20388062200003032170320048210500c4100c01107500c541c0a100c01a1038004050001250b541200088005421800a10f2a80300d0001c20001c00c040d2101d02404005203402003500c10360585441c3d00c480140d810808130204090f069000b001080c22001007250090f06242c1d04604815021402004519010010715048401200d0042c41c0980c0c0b800c2c400c2c0755900166410010075004100224081c0c46840c1100c00c2c54031724469104a84ac1c0b1071009a05034151440040c180101540414288000360307004070003604845d8001c029940035801c00c0c480c15400d140c1c0c002003009190100081007803158055070700416044000ca0b8030250850080000500c00070601c030304055080c00020100d42d80c4030060380c06200309440701c969018144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 685378048 1250 685376798 685376801
    0x4200c070b040e0a0b0406050d0303020702090f1005010c14010912020f011509050703110a020705131a09090c03010c09082e020703090f0308031e060904020427050102030a 75
    0x96220707555641091004101e9801c02c082c1095000804000018528981d180050f004007404d41001e0b411806a4102000b019050b07030084c01000d00032900c58500d0358400c802070044220440c0c8417540f0501c02c0b0010406c95014052a2440d203100341080c8403c20b1001d1015403c54004904c165a608042002866019010302c00141f948910314024084410b80944034810040d9078032481303881e140c5c1c8200040c0700354441e6101e1420380380c4410800e940d84004510080d5520b4180c015030b4800c182489054040030450f1050071900f0705a8002007040d000b0580802583d81001810003809010728010008241e88c28420041d64520513100c000781c450405c441149098644e0583c920404149401c0d096440e411500061100404240c056641c01c0e040c6407c1712101c0c0250f201100e10b40c80d41ca0040100302001c4041e500c94405180228104640e100400703100807801e50b200d42d0030107071420120303000d4140303038010450500a1070141448803024120001d061000d05405480d141d5010083c404d028195 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 685379298 1250 685378048 685378063
    0x12130e070314070804020105070212010501050a06030b15070201120e1e0a030e060d020c120403210905040f020c0f1509070315020a02010b12010207030320071104200c 73
    0x241e1a040100600401440c40d900c00080e1018080c400f0441c00241168490b81c12500c00ca0303806007540840030644107125020349801e01070240700c2c1c2200c1001280e03061080c4a2420308a0000b0705810449003180342002650f03102c0310043c0c0c100070320302e80710034441c044501034151a4003c13a0010703c140c0f2030211180d15051801c045a00b85030300144035200109a00c1603480890300d0080703c099642c0c0d1400c0115400903c40d4002d80760b200d0041009079007109018030080d10499019081c038000038401403210f138030340c1040c0030714000200340071800602c8941020780c000018802040c40062804c103508c28800d00d0084050000c544c10790158410444807001e928015420502c00700081422504503602e404004407420007016a0a50209441004510035008454149000342000650014004100c1d002c1d5000398019000301303040848007100da100d00c1286050710511164054100001543c0d081261583d00c10415402601c4002c0c00d02510041c2000d21150f4450340040e036921141d013011036081102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 685380548 1250 685379298 685379311
    0x30705130e04120e130b012114090d0503010b0a030207170d0f0c0c03030e070f06021c0206010f05041e020d02040306050604420b030114040911060c12130e 68
    0x3131074000c204540d10752a40d031510003002d00d4804a20703030304144c0040710949101003501d651010610080c1c002d2400b25032040c0300074418000360507016a00c83c041680d6440c05136010304000f407400c100400102c8030440103400d0b004140d24000d03113014841e440f800582c44080742000050301c400501098810740e1881203c2c6003504039007040c4240a12107001900c03190300400040c0a0680303a4555a01c1a001805840c000d0154401c0a040042e00d4a00080d5120428500507180e01005090512103600025405048410800540202c80c1c28401803102404002000038031442c01d509480400100c980058a1a11000f80c401600c45280d4107006043c2e034005812140540d18151035440c001499080c4000001600c1c031b4040c440c040140641031741c00c201d4005004040481c24804907041c000540250b0480d1b601405401e400303600d100802c000c07100c0401d001401c1c210343c0020744c901d504160b4050400e480004080d914075144e40c0b0340840c0ca0380c0c800c8840102d000e20083c414001c4090380800349400c0034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 685381798 1250 685380548 685380557
    0x5070e250314070c0609050d09082a0f01050c010c020f071409011e180b010e011716050903030705011d12040311042904051506070602030705130e0412 66
    0x15003401c2d50030700c0c800c01409580401002454001c00c2c001d254110b04900c5a0100c210341c03a0102180008210341418061001c4501079200b80f500b00114084001d944011706022101401582004001102d680100c8190501c2001d010080317030b1210038420408481e1241c1c0281500c00711914240c0d0800d282d070342021449040c0d8000260083e21003080703150640e8a11401001d81540451016072001384503404500d00c0030031041c0c44000080590440c0c40b8044d8280ca0b60342d0302c243d4080040d981030040c0508031095040010004026240c514080c01c158212414081e2801c1c131000e000c00c0c10343d4080b01003a952b50307450b006400400c030b0240e00040380340c58442c0b000c3e12011441244104080c455433101402d17070260300141510079030ba183e0122010f071210241c1000160f5046100d0b506240d24605414400d81c90100011042202c00e041403a00d4400207146070725081a50303482100a40028001c4c108120041c08804460303070400310001c02074400b030103d0624900d02458414808002806c1c0c0d4810403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 685383048 1250 685381798 685381811
    0xf09020a080a0317040203010605060403060207021f05120a062c0c0f180f0d0f02180106050d0f090f08041e0605042102090c0703030b03060603031605070e2503 70
    0xe0380198804c41c4d072486070840c042c0d103881d5400000c4c00742090340c002a0348040002000801c11003264010201d0610035903c8807085404003080343d100d031600040780c0003c203004100342d02c5151550000283d100864200000c2c1c41078442d01c0780c00c0b8075404140749a1070045540c001c1c400050001440c0341d0320101c2d00c10b0340383ca4824400c1000d0070500400c0e02f076400030307800da420891071661010341901000901800d0800305401ca800c1c0b52030b070907245c80c3d81139000c0d2004543d446a102036011a050603107900e0707100d00703103045d83d1104184000e0400d031006207130680d600c6505000250607840520b200c0350151040607221401c080080124401c111143c400020b0200c400300300f00c0d50420140c070304582c6250111010900e0180842410a04a443c001e503c0000c1d14200301380110047e024180340b50099070308010404000003899030b14882920404c2c0d15520520100c8941075100841c8261980300d0310540754a540d64007000c0f0102c4000b5100310014242100c0d44820304103c00c91031a981002034501031120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 685384298 1250 685383048 685383053
    0x1020f0a030e0a050d0c060e0613020f030604020f010e040f06080a02090a0c090603020f0c070824010f0509090f010e010209040b010f0c0303050912040e04030e011701180f0f09020a080a 81
    0x1c40c01e01710350a07400e000064415000b03005040d03118581024072071050712803610700390701c138810840c1400308102e218180394030030308000b410006041da11450307002e04003a10000c9a8001034803c580345001e603951103904c0d20700407241204a03004940040200300014981c05a02d0720412078091030041c100c0304110b00d0400340894141c0d01c60306801c1100c4c010700300140d4806051050390524428502280311522400c4000210340c0000250300d030968020b500c103112810440150340c1641c400038070603403203081e0b0400014041c80ca0100010b03a08103510b4411644116015420303942174804030300214585035804a50384001d41458040c0c510100030902c1d2480c0c0d0b90702d4001d0098400165540301501305a55000020980380c0f04101a068845800081c5602c4039590110407048110450301140001e1840c0c1428506d0f50040070031002c0180089010a140c1e070805005110900c00706100301000ca03225000a890700c04144560104900c1d048000b1a80e551a80144086d42040361704c80c01c6294001d107241c202 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 685385548 1250 685384298 685384303
    0x6081b21190629090c361017061503070e0f061b0f03040312030c351b12100308040f380d0e01020f0a030e0a05 49
    0x8030807154807000140c24945081c98001844030000e04140100d4424002c010000b0682c1815141502114941500c4d504c0413012121401452142440c901c4080f444891107040c1220310700d001c2c6d08070705030004500703424030001d00c02c1303483d51156001180034103000081c186080903810394843c0702500c3e003d00030312a29200c58128840142543c0800c440900c45406a955015001144910050626481d10001c1c0e103082c010100102c14440c06100f4200180c211000100c180c8080725007006013a8800c0c10150402d0300034240000d40c1ea02040415024183c482a940528504078113070008404401140030300d0240702a10058200d410580300d4020394840b01c0c005404840ca250015490340c2c8540c1c455000d10002c002803901300a00c3c0010104010500070040400b040c00c46003110300741101c03000034401c2540c5900780c40d0f00e5566010b0a0a9151130359031041001821114501d400c001100c124007120b542c22a004903a102045d40d900007985005203906000b03044903201c958016018007403a5682e040d6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 685386798 1250 685385548 685385563
    0xd15060c080c1f140a090f23031c050604090b01051504030501020a02161d040b0601020c0d060507120b0a0e1b07121b0c051306081b21 59
    0x30092040040e6100344404148428000c1c0b000120041109206800d032000c041c00d1305102c1c858840c60311500169107021079018803541940c21605100000c3e005e51200071076000b40b5400c280701600010b41400c6860300400040104401070307041300a04c000c14504000a440000d003805210740d0410200d030010a218030080c9044a00449201007114000101c0f80a580600d1b403000c0c04952020541d0061990003280011000c850121512403a5480b48520b4034486515803a420443c0b0202c00060005200e0000c505d4002205004607000c403207540e0005400c41e146107030110760341030b11103080c4036445811411505401c050b00100748000f1700c02e40041a000010b601c10031030717100540408281301c50340e802a040b803040d0726040b03203d9842a0303d0400c0742c00c0302c100d420050001081c840c115049035a8500b07000152a40c024407210725180b401003049405003803184800d4903555a00d0001031140c1040264494001107228034802620050f8204002492061502e403a801520061510501c0c00400d01c00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 685388048 1250 685386798 685386803
    0x411030708180c040207060501140d031d041103180111091f180915090b0f01080903160309140303040b0a0c030903061d06090c0d080309010f110d15060c 67
    0x10590811a515603d2030f00d6039070720300700e9085131001681e00709014442c0c020740d05949821300010051280c040c02c0c007004108401e00034002072840110344c0c03099a44503d441d03862301c00c010004510184040c4004150b60f1003a1016140151014074042078001c081c00303850040d803d03401c68503042608000c0490600d20461428041d001180b4488114082c01400703000c4030352940c8a416036556485200500c0180300c041b00c007c0690048446c0001c549606001c1e001400c40c02500d9641c1e000740b00001501c1e4a0005443c17030845000a12400e40c0b500000b044072600c15009a0b107009a1600d03289a80d01ca1442049100e4000c0d04204400c0c45048404021540807002610b80031079014003c2c1000c039940142500010700c00d900302690305080d00e903404010001c00c0883c8050b00c4680c1c5401c00d40540e00c00c00144030350f800032510710800010440c041c0296600003104c0002141c149400107501007250040cc41ca10f500c4e040c0410340c960b10320385603c207035050426401c03003c900960074100003810300c4120700c000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 685389298 1250 685388048 685388071
    0xf0c120706050309163213020313080d021201051915030213090204090b011d010e0103270c080105250c0209014e020a1508060411030708 60
    0x1003030500200f0081c401d551104d10103403508294440c4520003160304a651098000181074500d9030703e401d46d0103451402d400d80100180d0741c090700c0c070341c290b0040d410090144550361b45e0280030001103845507004240030301b031006005a83d800300d4101d0100c1c4040603017145008840c1003092501e029004403080096803407044440340030328038140b000c4010784544c400c803000301c02d81e020303000528040680241003628580300090050134000c030300445580801108403074440302001c00e031185650140852441140c030600d0f021800a480041d509800d0a4000680303030780744820070348442445041d580880180c24000000e01190034280100300f07450181100080300d43c1c90440b26402000d003c0c00010300369070ba01134104085983d480c555105003070b40402103902c840328514410599250740d10f00181c5841c460815690b415180c0b0700c81403003007199004041744c108030b40c0103020803041c0300405c1e0100004078513500d192a81c078101e0240019a4802c40174648240818000e00802c20b411030703a600c0e4407c01c81000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 685390548 1250 685389298 685389301
    0x7112109060c070b0a0909050604020a02151f080607020606010f0504050418050105090f0709020a120f0e0f012c15061504060509030115030506130c0906080f0c1207060503 75
    0x2543c01c0262035030225245030000510640b40c2c0303400211020482d01c1e080010412590740c60309200c280d1080300e88400050300084a468202000000e40d0364024003502c20030794198076240d880c2500484650000c095a034445810007044543c108241e80e4002004c1ca8080b0403483c00c00c602510300c0c091400b07090321a98171404401440d8400307581511405030004002e000609001d408541c580c0c1c2c00c021201654083d002c40440c00301400e00858002010316038130001d80342c4c2125400e000500c00c8100c00b84901d80c68250f074a900b081c0412602401d40c0b2800000180000e9110040c19198000801000384403c82c00001c200d0703031740c0403451514500d011324506880366101000038070481c030b502c0e20450a80300c01041c040b42c1180d11101511040d40103034001c00c4620900240001c2030010380c440204141c0c010f40000d006148825040034603d84074210f00c1380c00d1500c4d02c420ba0203980741600020001c0c7d001400341c045400b0704220081d54004280c5014a030205607058050301c4406901070765081c4a2b0010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 685391798 1250 685390548 685390567
    0x30a0b040209100e010806010e0307060e03010e0304030813050108040c0501030c030b100e01090b03040b0705220e0a0f0902010815010e0409030c15060f030f030c0204050711210906 79
    0x70112451418002d24440c229101080090001c1c0c1580e12280d00013002d010010360254020b01c2d20519160740103006040b10740c07500704101c6a10380240e516a405541342c0d020000049010405813000d18810030b007040e2240c0d00c2580c1350703103030340111350000303040102010912001c02c1e0040f42c2e86054480038a404660000010b80a078068a1805032454000030014240c52045602c51480c2c4440c403426a0b400d00f8141d60344441c1c1c01d1502050b10042c05c0314a00700c02060250380200024404040d442c464141e8100c144040041d0480583c1e101c0030b2950090010442e0840c0140b06038070b4029160001080715000640008080300d0004203040c030485c07504200401c02c0d0380984000e0001c968020300a0206504915005103075070488902110400994000c2e103036141041d01421080e5042440701da501c0c40d01c4c5403249079801c1c81d80801035060001d440188000f40c0c5460007994030a00c0c5549030180501000c0c2c7c141850600240350740310704800e824408400b4407102004480c809001219a540c5811480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 685393048 1250 685391798 685391801
    0x40306020a1b12110a052e02030c12060402120402061303020d060207120512060d0609152901170c041508040201021501050d0201031d120c0601080d05030a0b04 70
    0x810308106000824255400c12640040303c900030700b800d42d07908254240010070140d070341070405d1004013181c0000136807101d5403081100d03079640e03a071b41e1960705440024481c00710000c0b40d00585207082104c03000140c2541c02a1003541e406e4002c4c600f550110310b404020040c2038000040500002c0c412080002c69014000d0013000e454041c50b0000c03c040e4001d440d0707141410095010401c11504442c0d01d28540007064003038004d40702c0741c003001103070310050b6619903041001c130300c80600040314015914480740000c1034045d011160002d600f1200000d0032507511941781c0d200401240c01180b1004a08107154159a200034000c00740415080503c1c010b84910120002072700841d004542004e5400c0c04c0c424180303900c6003a040c0070b02d000382c098031070001a940320384007046024001d60340c0041c04403030ba4400551003036001c04840d42084914050798100182c903d8282204011910924a800b069840c01e602d0203110841c01400c2c4c51000b4070248001c140e01610a000080c0700001d00b603510744d0314030025181c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 685394298 1250 685393048 685393067
    0x5150a03080d1d0f03040812031b030a0f02070605060f031b040203061f09060e0d0803041203091e05070b040503120c011b03050f102d0b0708071407050105040306020a 73
    0x802c800e0b1384039020b6142c8000e940c1e8025115404c12407003031120034046420090708403405007201003a00d14004009010000c119072010300a451a650740d544ea41030014602e201800740c0c20710548000c14181003c00c10000460701c1c040205d0300c250400880641c41c0a80e02d440c17004403400507034002da220703540e8000080c94403041c61050006081000040350120354000507442c04c0c2c440795210340c10310303042810a00240140c8407000800c1844208003180109884c00741240351a0880d15000c030b80a00320360786010325450321012414012089290302d4040110070b11002c0d02420340420f98030300305450440000e586880b054078600c0081d00004a00c6004007080d081441001546080c03606e1045a882005005120480c3d49d40e40c0074240002152581d02512921002c90381120b1000f07445043c0c144401642010306142d40c40305203040d01c00050b007d000380c00030f000001e0180080c80d44500759403c0c1031410312010340000c00310740c00400341400b0680e003250566003503e030081e10060316084400350a07641e0844 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 685395548 1250 685394298 685394351
    0x3020a0203010614090c09060301030b0a09050a0b15030a0b060603060d0803010b09040c0c2f090a0c030501050108010f03081e1b10090f12020304050d03020105150a03080d 75
    0xd03c80089405001e000d0020a03840050b1600031941d66900300c0d08210b030158818095021004100401c00b040880410b83e8001200c1c460000d03890b0f510381d039105e1408040480880d82880d515041000d91180d400c0520400d420640141c040c482e00d40d617501581c030400600f403910507800400403450742e0700c031040c0c18409030f98400805a580e5031035581c1203540750420480d8034402d508000344001c415204500b4004910742c07000103c40325810003602028949220104c5034229010004503550b60b95400031185d0090300c540600003100f5030804002801c4d11016000641440b81c204e004000241181185504694100c200d440c0c65806d1501c8a00070102d80905920040c0b2011540091480d08814241c681e661104216218a203540c4419802d5a907650310142030025280792074000b041c000507020140d0481441643d25141c2c9a40000310505084841607006030743d240d0030032080e10b0082401100b1500c0484e005d46805180d40e481207071074400c256240314444c2e102c5080302c8200c111801e49c5030404a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 685396798 1250 685395548 685395551
    0x60803090d1b0602150604020c100c11010f02030a0e030c120d060e091015080c010e0406030b01030b0f0c16080901020f030408030a08100609121106031602010c0e10030903020a020301 80
    0x590b29a002581e50030061640c1a400b501c1c180801c6c102e14042c400c84402c60340e0300e4050001c8005401d107410040010880841c14056090b81c1c540c0906001e02c0f40d00341c0180b01040041e102d051481e80442141ea0200500c81981d008008180e080782000441c40c1c011400da170816580d07074400808800181c44183e100307400181e80b071020300200d080003081055050201301d00402200c50a0b0f40c040100340c2c80c030b101c2d40714a504401520003195100d000070350309120b0007810100d0096540d80d00ca41003d4426442074400e02d0500301800012104a0702642e000489030412504051802c101082c10040360030004010100004180d00581d0003840462035001c0ca0030f0641ea120b60ba01d000843c0c03a50703c101c18010000e00d011000030344500442218400390341850396001c10040c04c0080101c1c00c01072400054601092004002e10207641d1070008510800d00315048101c1803200c028040d00b035a40180005007840302c0d082c00d100c5144c848200302110540c0c40c0c075012445074080d050a0781029540c00010b034055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 685398048 1250 685396798 685396853
    0x2090c0702040c03050106030c08100620100504031710060528050306030d030603080301090c1b08042408040204150302041406030c060a1d0111011508010f060803090d 73
    0x2113070907901c058102c800c80d44052005042111080f175074080b086501c100c240600143c184181440f80809118614801c05a02565110800d03618509640780d9001c02c100341d111000c0004250740007141c00d90800300b48400f011141449480928a140d032402800c0070050041440e120a124140c80740c0c44c1ea00c41c65071095608207403054010419442150224028070800000000e0580302c0c0c0b103000708583e01700f070740f8504503400d000d12040030b8401701c0400800c10000d4122442079120407025020300341c1c070900d0003d5465241200b0315980403191500500d403904080c0c244140b0940040d5400c4e07100d07034100c1d40066000104011501c17203080ca504003a4110b80b8146003003519010b6200311600070350741202103944010709141041118415456620000b50b0b002d4940c010b003650100394004d00d440c0504008031680480d03c4104e084411300140e03034006064580080100c00000c0c8502000000810380600c460360810050565034410f01600c280203111062164003400646445240100b4000b440c5400f43d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 685399298 1250 685398048 685398071
    0x304270908030a0606140702060708030601020a0507060f0f0f1b03033803010c1b030e150706140601020a020906041107051e0d0e1c0206043f02090c070204 68
    0x4c03c410b0041c2d0000c074104070011182e240001040d980b070b1036030042c412864214242da03440d883d80c1015219134150f1003502c074110b0000ba418465000604859900c00c03d01d424024001003c491450102d101404213000b503a03940e4682c018000b601d19415800d180440880e581b0381200100181404c0d5040d12541000700b030b6905803440764404c481c003901030381e140e117001150341014202d500450f14800420304082c080740d4803070012445a04014045e0920035039041c03a440110300b04580b80700d0780b851304880000d4540b081007c144100320a180201811000303500d00710001039a181c248140280c420038810000801f00e54960b0044a540800000c11580b14040b601c0d025556140d500103039404c0302d024000e0350401c14000906101e650015a075004007955503a018001d101500c2e11200b52410a011045009602d0f110f0003800103101006000c49403e80d402c200d04226a403062460440710030015000b20b09a80b031143c0e02d500c80350103c40c0d01a1507140d03449a242d0a10035488002c1d0807a0504013030004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 685400548 1250 685399298 685399301
    0xa0f080304080106080606030309210601140102060a06030209011e050d050c01020f06060105030f1909030e010e0607260d0905070906060806090414030d2406020304270908030a 77
    0x440780d040c4004d004c2d03181c0302d006503912440c0880b4581c1d050f030f000b03100c00d84d00c5281120f00b40e1407100036001090061520860242c0c209070f0245c0120448902882035070000e035038104030003507201c0d004010410209046500145401e08113200f0a41c5102c440482e24944e82017102240000301001808400d07100b4040c90402e4607403030701c9490b0b14050b01440d120010100808a2034030310800d8165590340c07840d604c04005548100c2c019146d01142003181c100590301d44014802d644615000ba200ea0b42048880c0000410281c031108010780140c0043c4000000590405002103c00f000700d10b00c140c00c920708290105560182400d081c0300b81307041024480901c030000c91040240c96130307282c092084030749030759040d14418415100a50084200000500820010403145211071000c5060700e14114a101400c8151041420034800106c0349030b01442c66000c900f0320040092400b40091810145401841c3c070710100001d42186000031001c0404000c451660f020030300f00c6510220181e01d90034031a42e01170 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 685401798 1250 685400548 685400557
    0x809041d0f070f0614071502070f020423040f050a020a0f08060c0306030d08040c05040f05060901060309030c06180803090c0112060b07061a04020304050f0c0418030c020a0f0803 78
    0x403031809080070102da002611480801030b11490346852081751072202c0780c402d031036018500544405964814494000354079000828510f801071001070b4012905004000403500c0d01180d030b001400c004c00100900050040e84c0031361058115480070094550341c1000741c1031008141000b54001420368010452204811058050781c1c4540e0445550383d403050400865444140c0e003907a03040e801030250a40e11032040440d2540b05204900100c4902e603030ba0041001ea61840074141c09603912a403c012150905803541c3e401001301380740500505040c4c0d2005849001d03101005800031340c944210351750b8201407101c46410280e0100d0003030380c0c2c1d1600540b07058031441005041c500081c40ea181c000c1d42d00450740100b030265a2800720301d070301d041c5032039035548010f140c090640614503810240ca0310195403a48065803150323000da809040101c0440303403924140307400c0e404814443d42c900341c9103d80201d4112040740201351b143c10f04d030941030344500008030280c1c07969000c0103840e0040d54020410314404005030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 685403048 1250 685401798 685401823
    0x60403020105060d020105191e0c06110414100207030b0a0e0d0905330d0c02060703091208150a0f0602070605183a0212030c07030809041d 61
    0xb080180c42c1c940420108600c0e020000c0e0003d05d080c0104036000a034441b0a050801b00c60904519035641000c40014841040602c100801c00c103070072000a22000d400742c04240c07040242c40b1803405091004000c81c00c1c240b42803580c01081004001aa41030081250002858103e4280b101c0d5240c1690028080d10a04071310a0050094142c605078560144a03036a0540c1c5005206c5450741d4180c180c41500b500c1004882d8a000c985103501c445030560358401480042810301d0085030002d10a60068504180505030204040c50719604c0000b15080038031982840d02a480c20010703e485c1d44090480807100c803441c01b41d100d80319490014006e10284221811200ca5409852005030b880340141d409018208024580002c0c91640c00c400b89480c070440c156940e00445a00650040c0802c901c4002d0618014203c03404d1103084a0720a40ca071800c000710f01c020f60390000b10b20344440840307007070380b00c40d481c0c440145400404a000d000d03d555641080e00440301c0e600b09003143e007445080c2c1d6661008003841d035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 685404298 1250 685403048 685403051
    0x9050402150c100e010624030c08041106030604090b0f101a161a01140a1401020c1005160c0905060d03081605040b220905010f0b0d0f0e0604030201 65
    0x40c00314084140701a42d459440c04009842c100f5010a400030140500450199455584060100e0020206c1a6008451081301141e407134440410300040c048620700646039007440070420030000080c1440702001071054003501d016444c0d8840601190103094200c800500c03229080c0c040002c50045035051038410b02002c414a0340311641c03603440190044140c10710313003140c44082109084c050070141d513522042e0322604ac0002d002d52071010b82100c1800a80004070009408a03c43e4002d1170a202c107140035201d0000241e02c6003072600c00107590340403075039400d500030150344034011013441c040c10903100031800e4101081c1c1284203a01c0c251142d109940180c0380d0591500000c9072003814200c00304980280e050322a0780c115120360b0701e58914020302d56441c1003008070801c0042080310490018040304e86416007441c0001954170995124610540c11440c486403900b0010050104082500d07c00c4a2200a143c2e1b6200a400c81910151101c00c641000450429030382d54107885001500d2840389009900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 685405548 1250 685404298 685404319
    0x30c05010f1a042904020f070807050d08010e060a030618050d0315090e03030f0405100c210e0309150d14040c08011401090c03020d050c0307090801110414010c0602030109050402 78
    0x1100c03500c9580c001800d152030304d24410502d001d0a166000f030401081892280d0300b48101a520308a480d031000704100d9480d00000d072403888943d04805e8181c090311102d403031202c29140c10400b041d2610a1480081c0c0525212822017003e0985290702c201107581040c02d86801c822403801c045c0241591440d60028042c1c00d180010fa48003942c030500c094401c209000d03600e5511922640910190060010303205805510b09003200c0e0401482040901a0643c071512202c40030004415090704c1c5880c1003c0300b4500700f4601c40e580d00d102000303e0f9443d510441c1c102010071001a004046400b4400f5215072052a00401c0c4004074000341890307104078454850981c0c15034a070b541e09420388810031b00b41030031000204014003901c030064000d038008529071300d8014100818440b060064400549490500b500c0000c00d10484681c0f1240c40009041504020f100c1c01a460349000d241d803066200e290150000344100750b907203031301c9600782202141d0402010f40d02e950310303101d9043c010402901e040303124030050344 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 685406798 1250 685405548 685405571
    0x100506010c0c1e1719081210030c0902130312270509090313060c020d020301050a060905060a060914061902010509011d06151512041a060607030c05010f1a04 69
    0x101e44040000704d0014041d40b404241d012241030485000846c0e00c0c2c081400400504103036411402e01c65030262040b4170a080c90f5043c20740e0301d9111500800d01c0a801000259500d01800040d282125805442e41030500e000b07550488450908098040c000c1140c180850300d400816039a038010740348212205810746e01c1b21042556244240da20b01c00c0514240001080a80d0041c8001c15a650010f0701043c0540c015500007401c6031b80490b41400d00342d60352201808048200c0c81070a900040503200b050540f41400000b41000c12544903000d2800700720340b03018105d91180802c2e00e454400e030b0880c5403038500104101078040e26003124420015860800040501413000404152000f0800050103042d11051405030803070b403406c07003401c1d004801d01c40712511820082006008642c2d081508480c142000d162020780b01c46000d5003e14240345140c14040d180c1e4528040700c0c9443e41c036042010b9409481d01c1d0040c0546500f80c4d41019151805907a0341151400107101022a50111401c121058904 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 685408048 1250 685406798 685406819
    0x10f1b0207050a06030b0103021c0203090c010509060403170c0f07080f0102030403170601021f0906060e04020a050d030306050a061e03112a070f0302100f02100506010c0c1e 76
    0x9110b01a0312568060040107a075020740d02c0902a002d061501500d80541481c0c007034200003030f244120400765400020811450818006103c802d1424038165103001c0d0300100049a81c0218080601705170070490840c0101510300c0c00b118042e44102c42a40c02c0030746002521030312001e01e071041c600c440c001c1001c5078560302010b01c00c40b0310490341500c070402d44101ca0001d451b1a054010b010700e06512800341600c0c01d58009035083d030251000090b01040440c430768903021041c0c6225900c00c0c6514030103074090000594800c1c50042c02c1d9002641d810820151034242240500201d034445038000054450202e409584050195074060680182c0300b1500030901c1c04030101d51801160303141c01d010602c4a415040325005801c064883e41c503221041030381d201e500e05410442168000b1640e84801715040086003032414030584146903608003900c03500032104001c3c0d210090160155031b11030f0303550005001d0740e000c0d1441803074064100702055407490701ea08031191040c0c01c00c58030301080391030081c0010b00e02c1400e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 685409298 1250 685408048 685408063
    0x7080303130b06030c0a0b0406021204030c0308090d06050408250c1511190c050904051011161a0907063e01020406090506040b1218010f1b02 62
    0x10441004044400c5803140101402c02601c0c0350790501491168800715921104900d000d0710454a006658918000d406854011104110000e040082c001000404d0604062100b1640c121140175503410400c000215545482c2c2002003010303261005003c2030102d0b040280142080d07550342480c00926410503120003090200c0010054041c41c00144504e61020304102c4261f046410701720121100042d5540c101285006a81c4031400268911020b02007140034a0000f07150640325000720742480d0310b0340b503161004105c0c000e101588811507640c103040014121030000f8079070301e042c42c841d0301c05103840180e4401c0d080d1003407090003440d804540c3c24000483c40b02e089036919115000100d680c50150342108a00785040a1881046454007524040c000540032001002400060b596828488046c1280c2495009a4002d038014407061060740c034034404036021061510200b0340c0030b030b54005242c4001010301e000e041c025404d108410500a800b134110414a01d403000080329680d0401e00101d0741c4011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 685410548 1250 685409298 685409311
    0x7050903030d2c0c09060105030903041208040b0a080703060f121b12050601030311012007111003020903010609050906181203180c0904020a0b09040b2107080303 71
    0x1c1040012614603140e070041c0c00c1d01540e500c0ca01480041e40542156000c0c0382c2d96400d0340c0750000750102d141441d01e10f204a9004c102400d00505604003034105545d64088c5000b58081810182e40034018007801c0c00a640040144000081d544d45607140c00800459041e00ca0002180c100100854107680c3d807132400007555040e0012071545486500d481c05400407501c4918000403011001154180400780742c4083c1c1b50090005140710f500d180b0b80102510074090720340ca001d915103103005005582c1071042100010b403080445444000a0906071104c1000d9020240d0203d40c0303541c2c3e840c103e41c140d005040d84240031002001500e980b849082c0c1998011907540f80f9a402c20300020301140440301c411320103041694102d07038a020007259103d029038001e540a100c00203481d0303d03400304e444080001c0c040010b07003a1007485c1d09083c180e01044030b0b0070791030151a42200307001c40c005405440b030745d001c42d2140d2402401800050f014031046445147c240010a265015001c000700f40d0110000880e070181d203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 685411798 1250 685410548 685410553
    0x110d020c13090b01030501021b01060e0105090c120702100605060c0d03200a0e0424150311030109090309050102060c0d020f0d1e1506050f031f06090e07050903 70
    0xa0411080015214038181250021551059403001141c0a514018045c5103c2e00c001a640e10403000581c0d090ba221100c41c800341ea0400d0800d10004c0030030500c0300d044a405645078803098854041d40410f5000c3c006a003020000d100e002c2189040c0d00080b88290740038445c1042282607114400d010042c49102080c00d41540700800034441076200390b00003400c481c07000c440c0c2184200c0c60300c072441c070f01d038401e102003c0014500f541c00ba0716440c042c8608240341003204a14100b14420714022051407000d03105011a00e030a007401001d00d14042d80004444140124034659650707140e00c045001002e0070301d0254001159410040303103039400069003500803421488070505104c02d0399129406176100c4183d1052444040c028100807039002d0040d16a0140c2c07110001030200c050b0721703250301211204803c41d0034004000d4010040182c00c40212645003c40d400c1c150340c0d0765a9424500980d10b15800c40d09008141034000041142c0e0080d45001600c645406148803034039100c004444a000300000158542c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 685413048 1250 685411798 685411813
    0x21804030806040e03250c0b070c050d050a030309022404090e031201150e09040b061201060b0a031d031903050a0903050414010e15070528021219030e01110d02 70
    0x1c0d0003102c50506d10000c4c6042c02162103e6607401c0040d425940a039500140100300d0604205a03d0540006000306565107a00400d0ba92a2966182408000a818155a0080c0005645401d8221201a10400c4440304d15401c6007072908605d42c094802d20689901d442c040d0104818048100c0c3c22594443d94580a1070b400c0001041590f21912a180140300e81501e002d4115101c290140b446903004002e00e00044c904003060085030950003a1507070440c0d160035010721050b07016000303031200c1041910b80020129803c44140c0348002c038404407042c0c548070100d03015440c01d4210315800008040d075501132010391582d02845094500801300200440c1c010b01c0248450004014910b444010525050807031860314004a0032000c3d20300d104404c2034800145000034400308220118245c19801e10100010410a503140c00c01034220702d0003442080e0580c013603612400108081c44a034160452400c0c15103c0e94070303020300b050b030b5055200d60200340d04042d602580c841c003080322007105080c0d4000c1c1404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 685414298 1250 685413048 685413067
    0x150f10080c0a0c06051003050d020a0209150f1305060a080c090402011d040f02040602011104050d2402030907031101180b091903080c0111040f140409021804030806040e03 75
    0x1c0740c008410300c0e4100b21005100314081080303405414041e90705014404115815810842d0920b04281101e000303650005000034016100c40240590040f04034144544011a07003000424508942c403001e0390182011100040740c0805520180c0982c6049552035541990b031040f282d181e0514a84041d4014401000617015500032a00e50058030f14807805c0031403c0c0c241c000018100e404844122909070340c0450305100072502441a003d10080c00d010b250300307103071802c40014054a031900c070003000028585c03001501442804040706c004071000c0e2056489160201ca003c3d921700b06448181d03141c0024407981c1d00c0e2075010b0341c8401080011464459205801c044003200c95502005030317540c100080b0114004c103180d102c04c1c55070140d0312a08240340d42e00015800c0c00c0c01d48010041c1c0c1e484441c8108010800036007071102c3c450031286c40842145551407101c0008005015080d0043d4000b00c542e9200301001003036071041031041d8420386582109840711000e000444000403034182e0250b1081001c001e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 685415548 1250 685414298 685414321
    0x30a030e0d020d32030c07090f06030b0112050601050904020906090718090509011b0c060b0303040905090d02070803250516060816020309061c14150f1008 68
    0x7860014086100026080d030b00c600700241800c01400b01010f4080314800111031508081309140c248100450401c200c4504458070348119101d40300c2000c1da11001c1030943c02c0503401500055803c2a0940e071075680d1482040ea68a01e800001c907614080c0500109452038044140c80c020754010341a0900e43d60f544003070041006016000409020044101b01101106404040c010b0141e08a0109050034408482820749030300c0903180f1074000c181e800c2840394945c001d15030140d49d47c00040206030b00310f080c80464158461904120041c504110402c1080f007000940d5080c600b003207078201d480055407507860640300e0150000c050500d43d0420810700f040100c400c000703e14180903030207580a090180c215003006401c89c0d4400b001090441007003140c03100b2081c04400901403140061480c01c455540010b140d48210346072206169024210303070321950602c2e0b02440c055003201e20001a2410031580403802c843d074000b1801d00c61150030403000ca0a080081c46105440855254499640c941c0d084000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 685416798 1250 685415548 685415569
    0x2508070b1b011e020d06080607020a030809190f06020904020d091e020a0b0703020c1e090916060f0315030501050a0f0b1806150a090317030f0705090a03020909011a030a030e 76
    0x10241c1c0c0c44402c045590301f428020140100441d4000f00040381451070041c0000c1030081c0b0a02c400d40004010b04c2c4e000d140680201c980e0f6a0000302488000c0c00d80c030700907009009110070150480c3c4041101c40c40c095a82c3d0054003070501a00c46400c00c0352580180705540b04490710002c0d00218414003c00c0303105104c802826981e8400c2c010f4a6030302c1e6198001c940b0301c4264049040b0100301e407256120241c14555080d035008840900500f100d204c420702c50f10b0610b1558402d25082088010484400920a6200c0301100f082c0d141004200342e078905100d4040c00043d21420308992400b203034104a480b051189140441c0060b01140c0680a06032521040c0603008001030342001000140c09200c081c0040180703100390254590305411415030402000c61442d41c4044074208070100709120505001070b111540c0010145482950fa07c80c5a001c1a030b1001c403540000d4016401205100d02c11406402441d1381030140721010072400801401c044e9903a554000150100392190101e0701103003130010010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 685418048 1250 685416798 685416817
    0xa0312050412061b081b030411091305010c09050f090408040f0b030103030816120b012001021216090618051026092508070b1b011e02 59
    0x220304040d42c940c201411402082c00c220350056403009040342040400007002030300f20251415100360f00d00f089044011070070380491030501800202c0010304005c08070b00d00b0458100043c0c0503003040d08041345d071039503004c90700001140c07154202401048482d11441d005011076000030621f00b000e28031314061060280c070290054a0841040002158002c6411004070080041002d0580d0301d6265040040072450080c150740b450f40c61341224164219405000842e041511000002d5064084001a01c090f50300407403c0480010840b603041c810001980681410903232505010f046560703002d081545400c10015070341c04030b00403100a0140b584108825041550913035001d1002580340d0002070f01000710900328000082c00040ca11140541c040d00500c0b134024040c0106da074500b00088a07688404800391700b1191183c0481c408a914200300e04114010043d04003510701558580c0e00000c1c2c60f44c003046546400d10508900340440c2c042c144505254000c41510381c2c3c011814140480b4081c1d1b0141058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 685419298 1250 685418048 685418057
    0x702060c0a03150e16020c0102030f0301030b0a0b0405100807080a0f03050f04180606021510060f0509060a08040c0e010303050a12020904050106030f110f16151b1403060a0312 77
    0x100d0301c0034844a46174000c490f201c8940c1400f01d21401e000303190a80c403041003411034205006600080d1003201c241c906403540410028515079078500c3c154001c202c00302072150720070f04240901c640c111260188600359004c840a851400d41c4a4410720390300d00b10700340c009012010307221a04020034462400303000360042c0d13a00313503034a4a82d039240c0703030071a04805820412403103540d004100070541d010089032001e0725120184021a203840403100401540300c3c403948080c09140c1001558180c421012688607641c0200050f4641201c14030003881c5140403102107803200301a6802184041030003a030f00c0d040fa981503840303600d011041c40302250b40c58501120300e8a15038082c842450969a240200b5010f0145c5035000210790001d003000909890120b038001030101c004000252003030038140107c44400b00250008a440003680c607041001c00c1410f00450b8500b8035103001400c90340250134242d84200000d075a0440c441d0b11201307044000d840b06840741030380040300c1601000054061088001d284000e4100f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 685420548 1250 685419298 685419341
    0x15040e06043804021c0b0c0a0801062c010302040e010807080f1b01031d0d030c0e06180603040309150e0f0f0d020d020316060e0a0e0402090a05040f0f0803040b0702060c0a03 76
    0x45152120b003003581c1f0310940d94400304038004101d0b404107030a0b004189624100300c8260040449401c6000601c0d0041c2114015101c3e42810364040e40480c1c0061503a0300035030500d91b956980007611003071240500c403494042c00c00c546002480004280d28890015922100c20a03581001580109140f1003c48110841034020000d00344050002d0010b03000d10351000b20f420381035518000d201c0300000281c18443e400a102406580b0ba4509110b001903030b0030f4800300c1e0b884d1628107090711408802e5100030710b0f9034800400d2000695203d4104180342c0d2003500d0641a07500c8200800c400507403d41c0d0800d8100c088004004054903010240300c800d5800501070380d0416a071103642c43d20fa41031503000180492482e6144800904103606030100812506080d080103007850b900180c06040c0c05400d00a010350fe0f200414103001040099254095001911210075201c80c0307811600e0360803c81d0240d5108000500007000c0a001142451241080070f880502c0c012500c4816802801030581106401c0c00200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 685421798 1250 685420548 685420553
    0x6011d0102120c0109050114240d0c060c0303060608041104392c01050a05160605151009090c09030204150e090309010815040e06043804021c 62
    0x400802d9000e81c1c03c400880c204100703003041070a45255aa00601d422290401c0080c459000000c0401c0d03160314002c0381641c1000c6100103018101c01c07100141012041e43c00004500750401c0502c0055846614144103c9a0b280d9007540e42c150304940c06040300c60304501a110900d4260700082990043e036448040900030381c02c54110f0700301c18070300c2c0b502c080c0c00581c001c6c0401604008100c015201101e100001e10f0782c10590941413074240c8000c5030520101003840340c0814041c3d8117030391800c0d800c0c2c02c1301f4a4005040c10000c012300300c140c404a01c1d01c8140010030b482428040811a031111541d201c9140191400c002d0348001c01c070f00c1051700100409020084010703034840c0038220781c100344540c071024414180b800145030004082c0034a5080c1d8400c102c1541c041e600070101c65401400360300f180200c05802e07008200500500e50320800b03103000f4a4100000c2000c26081c02000800c1010010b486441c908404400411000050755504401e0b03000a8014038007622542e00e85403042d03607000c0740f4580300d5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 685423048 1250 685421798 685421833
    0x806010221090117241305040606170f062412070503010b0d0c060e060417010c0e030c0f04020309070e0123010e1804050106080d02030d1406011d0102 66
    0x203000c1c001601c000018281c0c0b480d80e0200c00074165845039204000c1d02d05000b52048204d407481401c6003404003459150303000c0c641c0d40041401d0b805460b8842070056107001e260000050140c3c1c003e000d041c0d60b146c0c6044940c000300140100200380020002c0c0801c0c0c41d8602a440302c5807580b01002280f000b030b0400c008903601d61140b80103000001c0030081c2111400c1108040c250b50036890b440b40184482100c04000c0b032034a21104040724240d003411042d401800b4040384503072145806c2025540510440b0354007502d4150304c52941400259030b0246451317118000c042e158910185203550080c800c03580c1544614148e8011600003030340c0800c07901d1b284c1d42c4c0c8a417200844400da000c420341507401034504400012920390382c0110f060901c4c102c0c0000c010100091608400401c601c08214001c00003d8100002507100300e025020381c1040320b20b030a85940c0020341d81e511441450354120f013850000040e248080c9201400f600d4140c641101c545490007206810194030035003d81184a101c0740294113001c1c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 685424298 1250 685423048 685423093
    0x40209041506081506030c01050f03010e072c030706050a090e0627180316140120070c080d0c0f1704060302030402270601121506031d03030606090108060102 69
    0x95130740d150a00c2ca0034004060500c50740e900c2803410302c20200402249600301008480c10f4420340003e00701d003504c0b6a030045810084c80c2701c2c1c400c8001c0c1d609039665100f80cdd000180d916220400c0701116001a01c510b0121118095813408001040e0000018003041014244080d03110101405503031a10716042100887d003606112030f0450307200440d00340460b03074003409910842a10440019442c01008010f6040300014100000d043e90200f003005403048034007904514650040894800c040040c403c5215145501c0504100d03298a40800c00065407800070504488030221601c5d441541c00e1030382c5a0040704058041c080365a00c02d40e929509100b41284040c0001e86541d660050b242e140902c148541c003040d00620a40700e1541c151680c20a0302c00300031490f03000000b032800b00300049010040c83c01416141b40d004000c0c0564003000729102d0b6140d4030001c0300344490b29800e4601c00d24184802d13120b110030303501079070410420410b04c010b0b0f50161950300d40290f01032045540c5504010513981c0710022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 685425548 1250 685424298 685424323
    0x201050c0a03110d020d0c0209150a15021e0a02060306011e03020901030b030606240d060b090109051503130804050d050a060b040b0d0f0c1508010f0b0304020904150608 74
    0x81c90752000c860900204010f05004d910342c001071405a8043d207003d4030222500700d000303201e40012400240010805950780b410060060000350302e15071a21254414400081034100041c0715583c00c100c2c00a040c00c0100059134041d4015201003540e9400b40300d5a07034001041541803050310100074007000c00f5501141006440c5680050300e9000c07207400141a42c40c1c0d6802d0510a901400c10301003240e87e1200c5901c00b40c4041216a440f41540c00044031050040d0040c02c0c0946240c01c0300013a1039003406004111400c0240d0301c58400719155400c00c5400c412030f0103400303040c001c00d0000400400a200314082281d0058032014100f0b5540d1000400c0c05200c000125a103070804d54040e01000340714042c1c185854001c4506101070041d0030003141180031610406400030032501314403c02d0015242c0b2800151a03600b40400c140000c40001800100080c0702d055401e482404000440030204020759000740c0d0300801c0480a5151a03e0b0240c203601e80e0b00390306450540e9054009070070141042035114000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 685426798 1250 685425548 685425557
    0x180402041e0b0a1208180109050d051e070f150507020a080f1c020d050d0b0d08130815071808030d0903020f010c0509011206030209040c03020f0d030f0c0201050c0a03 73
    0x9642d80140900c030040d55000b2084404043c2020740041c480d001610f00000004504071090041000120b03102c201a0b44201d8200c00b01110700d00512002064074682e800030079040500c1a401105a66656500d611a8800c8002041d000341b120080c0458a1109140340380f8100c0d08101d01a0001506901b40758002c8400f0303409501c0d0161a0310060004007400c00f042003c031460f405201b02c001e91038508a601c22405c03c41d00003400e0740284e206a00074030740e040c8041c01112013005589000c51660384988001d04800e680c601c40050742d4000040c100070300041d4540c02c00001d448100d819a17130b09600c40010365100c101d000010551641c00c101074602e03919126401301d1400c00c941006414100101c0c1001a01e03414403100c5520075420404566030f841080c41c000402c0900741030500c006104c140c00082d48184804103000500c0440e1001c001900d00840780c2c21544040300040100d1503500c080c00074049034040028050b00c500400d200c1d501c060042c140903160501801c000d50602d5a00d035000c40205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 685428048 1250 685426798 685426811
    0x5070512060306010e01120312050c0715020f04050607020d05060c09100306050d0b071e0c0b1f09050c040503060a1407080c120c0f0a020624180402041e 67
    0x140122010607002441540034051550501c07125142500c0305010306907480d51240b2500c01018414856032401505c1c54100b0170541c18000100314141d4041c103030035200780b11000f10f07170200d200c0300703200f1142d0014400300703101e01c0c151801c418480180c000c20000e90744204038180500201d401400784521883c0c0381048581e68803004420007040c10b013402d0b9010101880c180050101e0b40741c00c5095105541c102d02a1103c95503030351300484400100c0c640c3d01c8c0707820034403052070201e5941000314030352403a10514001501d6030310014030a41001921105034101040c40604014544565014035046120059164546910741c00800d240c034a040c0d51100c102a82c50070b802c141688075000c00368014603c2d00c0c2580840c14558605080c5014441d2180b0b100000700c00450707034100b403480c2215841c1040d84078454031640c1c0d100010b03480e1314040741c003e100317090b0304214543d00310590140786050b00d50051102c000807502450030488218001c000320381040e600c2f8951890303920f40d801c540c41030350426030011840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 685429298 1250 685428048 685428067
    0x104d0601050405150f040e03160c050102120906071202160303050c010b03010513061505100f1d0102030a0c0c0b0c030d0c02011112070207030b1f0f050a180e01050705 73
    0x1c075100108564070341d981104100c0b000317a41d100000c8000c01011200030401c084a0050281507109000c000a140c502c0c44a50000f0040c2600808084940c241c090b40c501b1061440303103042c0c500c101e211595000c0410002d41e4002010640f044800409a104480d0100d41002000783d40a030240c009801080d00441c14010741c4c4001d0046090607007069000344600c0c1400303159900030303400b9840001d10640d00c60303e046402112140b0203c00400c40184450151706144a01401d20007081040400054001c40300c4003280720080302c0c2003c40c80041c0d00551901d11041c80442d040711035481c0446c0c47c40d800040000700d204020000d0810b0101ba01301940d55049408001002c039804000403c0969040c00c0e200311260101105803010b60150345140155035496500490910015410040c0f10110181c02e02001c0c107200950010400d01c110400b240032602c9201c141d03d0004248112a0701c002c0c000300921003446000a8140c44031039141005c95005400507485007900c1c8100d400c0c40001d500460042d45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 685430548 1250 685429298 685429301
    0x506060304030906230a021e1605130b0301020307030c021005060105220f08010c261605071a071106010806280e0c0a06110c1c050102070f02104d06010504 68
    0x200170f08c40c4e5004000340250080760807411600f07842211b11400322000d1280b02100250065812454020002c5550340f07003201c0050003c3c120881c08800622411180c282d07160110302c2140d0103070308140c607040d050010740428418802003c40700d800b00140c0101002130300e440c0982040d00a0104034001056441d04010024290041d100c120a9100d401c20400c011154400702d08a4011400c1117003012072004450303065800384a1044e000345802074007041c0c1c280720340070f51282174000e41160f9501c85a48041d003401c981c0d40c010031300541e05550011030200300c07102030b060900545000f12203007007042c030480c40409904a48816800304401c0d044480003a241e031502c82241c001424480c02c050000c0000c1845803592440a80900b6000703410102d148420307844010700c5e40b8015644800207551701c100710301e092505080c4241d0124005c4c844244049009401440584400848245010341c8400c64903141d1050b854191090781002c5078400791048005900050100590b40010003041c1552411080c00b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 685431654 1106 685430548 685430593
    0xc15060305030310080106080706080f090a0b07020304180504051509010b19090c111908070c0801051014100503060415060807030506060304030906230a02 68
    0x1c2100d5060761080584881740b0080c00b403e95a0705009030744164901944000c6800440003c1d55283c41e22501d03540001a2401c50303c5031489912428140a0140d54540040e000003d06002040701c4680042c8035840c046800c108624090701c84d2915030140f03030221035050100401051000c40700350802003580c07c004121020408050010313011292041c443c0d0b000791810b08111182c414051006a940780c00154054918520006468400201a11000c861200302800a48003040c010700d095000350101c2000080c0e0360a1400540c640090b260744a519045268040316106803a040c6103500004510300b02a51291140700000c0c0c06400c40c502c500140e60b2455000056240e8081c40050058809031003c00a076100c0c0b400f0f12880d4401100e0280205a04003010004203115500480c60300b42c800d150341000b10001d014516441c0e0140d145c034030040e8483d031000e04440c001c010000 = true := by decide +kernel

theorem cover : BRFrame.Cov 685251798 685431654 := by
  have h0 := BRFrame.cov_init 685251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 685251798 ≤ n) (h2 : n < 685431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
