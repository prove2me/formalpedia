-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2171
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:51:57.77569+00:00
-- url     : https://prove2.me/submissions/8374eb1e-eb96-4736-bd5f-a31dd5c3600e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 390287769 ≤ n < 390467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 390289019 1250 390287769 390287809
    0x11070203031306110102040f090515040513260703051e071109181e0c03030d050403140306010212031e0a2c0703020103090510020301090203061e100f0e 67
    0x81c010f50b80c101000b20880c911030030007940f501b0309000d8803540708a107501c6510402c58552010030f40c1c040309024602e41c047d4001d00108503502d0540300d04126144115070590b100c95600251700c0c68035042d5407084002d04442c0078060300d410701c01d50b41100c03260710440c0075940000c4280d101e1801d096110004182050162000c0e0308040544000c1000c8030304054503140015400c3e4016000145001ca403d8090750a000a501d0003500e0481c0d005041410703540c8403a906010025080303640c0c0e00d8aa000c40c1c007031400303541c0b110044501070300c07860060722060b201d00b0b015a006ca480c800d078110151008551005d440300f00d5142d08416a080500d50080c1a140003030000d4540c2e003070819640150865100c420348201c480700001031780c040555214001400080d0401da110324150040c0202002032206204a840086659607550a1150002c0d0000d442a0b0310036408000383c4c000e40c841107d111010250028848651004141c5007518405041110b40050180169100c0c2d6990b8482d201510b01c41001c1d64 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 390290269 1250 390289019 390289057
    0x60d150911010503090a1b1d0a0516020601150306320102070303050904020702060702060310061e080a05090f01110301050406062f01110c0c1504080c041107020303 72
    0xd0310318051200060340c281001010320401c4107030742000440c2580c5a40040c81880c908102003525048507c1a030030100d05000e01030071100f1484d00b02500c00b40300700c80d4814100b06644581c181002401e00480000005038090801030040c600628855a8074035030f00c0c04c0001d5290380c1c6910800e5050418400422203131011504501c5c40100c09003c0142e460003403002d80043d41c115600a401c500504880902840d13011520404644921040381c14642d0010851a100d28001b03851070300c203a06078040c0c540096440d010103c0e641c918200d01c45001c07001c5450b4242c580c0d5403407400350300405009000b48150321408250354081d22081c07082029111622024a940390705000600c01603039800d40c40703007040250407492039101120a620413401d0f40d52400c00a40d0300d81d1143e44240c0581207a90481a070780800140707905018038000340e0711021080c10340d840c02401d08541c200c1c5446010780d1256003601c0e008103140f41104e02e400c1d03100030f058a05e48001d09041071519000709144d40c005110211036070001c24 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 390291519 1250 390290269 390290273
    0x614031f03031707020309010207030807020d0219030c0803041202010e01140a050d0605240307050721080609060604060309020a0317031807140112021b250e0105010503060d1509 78
    0x1185600080c140000c0d4031f88030b070000000f50b56505034840600005000321315402199a804503a03882c5540003812010035a0002040c01d42440261004680300c0700c1c0590300054804000c07040d54111106000c150310001d010f50010365842c2c00c0d03a2606070411007800c00b000408802c200252000c1171f036a984603512a0f5848030b0b0030040700c4654224500c07a11030014401c040c0c0710104465001c10b08550206512500c030070805641d18016250024130a50a405103000494041c403940c4103480c010b0364485201d41c03181400d00c04030000955140e80c108400b00003c1c00582e001c0c8e00003201003031003c1c08c003480260380e9443e100100d5070340740100394000d40d00005108179195600c0300c065440710801c0c0035120b460318041d054400200380e0442c45043c0b003440c041240c0120190350540c4c1a00119501003c110390f00f00c503e107911144a000008000c040d01e05a8182140803007400000b62401000c000560384d08100040d0307007940004100320350081c000e000c5000001c01c0441040c521074040301d004181c1c4507040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 390292769 1250 390291519 390291557
    0xb15090115110601030b130c170102180f0120070b070c0602120f07061e1806050c0c060c07061d0105060f010f0807030c030e190204050609010614031f0303 68
    0x703102c03981115800680180007040e0368142503074021802c00c0010180d10740318500280780000645c4001503401841c00112800101074009060902581d4480100100c41c003003001f030424003a01c41940007403056580e9a010881c031281056074440c0d00000c076000c45a503581080c000c0d521400007210301201c032900c10856540c04006004085261514003828016054001100c078010103030041d1a103a21a0f6124650515a50444a0608011406008226a40780e50000c2c40e41c0d1614111566403801000450f800c020009a841c00003002001c1e2006860300964110180c0100d50b09590207035132100c02d550304003480e81c030030301d1241c820704c00201d003600d0074000300060f039221165428148403240c4600c03000300f42c1c01901c04e580424607007030004644541150481c000d05101d28008014070881c10038008020400d01880d48051080f40c081c45140e50340700501681c4179081c0702d41c03400329425110007a5044d540101a5500c00203042c2d18070a02d0354903039011141c54600760b0050f0041510207030000551006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 390294019 1250 390292769 390292787
    0x31a041518140906310209010e090c0f060715020d0608060901060603023103080a391212050f071205040203300a0801050109080601120b15090115 64
    0x83c41d0103043c551401140181140078071298000781c003d0350710b035807424550141916241954014005002d10368451822030401d00c0d041c7d585424920070341e0f0301e204a80c600142d0407103400c20090422818100556039090300c115503203141d580c06d103030288a03c20a00358a8070a000041007500000c00309820f0201445003191003a070402010540100100d0300510200e01c094003085169912001801007044038186241d801c031b400091100030009807480d2041d501824002039207400c081d0128451020004258940d1401c040c032000660040001202052454940d080034a0b035a0510107104800b41d0a0041154011940c82e48480060818049204d6000c21046a807080c0c400f02004241450340000b0340c0c03050368201d011401c0305070603001c42c2240d4007482a280501440344800b030702d030300c0c610001401079002402001e0000b681c45070001002000056501c0c100e030740215080f00d4080b0240c44403140030b030005003500803506001c1b5071541180c0b588e0f50054002d2100c0051440340d5100b584c0c00a200e115 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 390295269 1250 390294019 390294031
    0xd0207111203040605040e0402030f010e0c12060124020a05030d051005040515040e01020c1c08060a1505030402180f0703050a0c0203090f18090606030706031a04151814 74
    0x80b0501050010035004012503064843d103c10502c0c1d01c3e0344606c0001d29019240340716034408d50a01c40080d03260000010b120801207411511048102d101c1c103100e5a5500091191140a00100010759804504c0194840d500184c0b481610345960f1291100e0746181d000c0d912540e54143d40c1c008001800400f06c1030a80900000c0307034107000508104280e031212890007407106106558a49842c8445802541241d0b465460b48003541e412111270030300d1140a00740c4600350008a0b00308000a0307168605218114180d440507680070341c2c0d403075040508844540000300200e0b04142c80840800d4045407806600d445512180e400d40041d1406413002030a440c03001c0c11141e00541070400002c50140c0100950b015490140d80014403860244009090754040030840c8044810302801e10000c4840458510711072a4140c00b150030203940d41178101c0444010f002004203003c2d0704103012203a4645034006081003941d00001510543d168a02104141801b036001f0041c265200c01c050240105e00d880c3c82e600c42 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 390296519 1250 390295269 390295273
    0x190f09050103200103230105090105010519140f0408030a02100e03070605130611030a1104051e0102010e010c020c030f010513080c0a0f061409010e0c04020c030d02071112 75
    0x75145540341210a0320200107146440e8692196250f1a4804d902000c120480300104560070712581000d030314101e4003801054010440034001241c99401041103503021310b01e0301c0179005612080c0f001250030320b103452420100100100078503800d000765240a00003034003c1070043c2d550380b012076002034030b0042d686200b000140d0800702d000040c0744020043e00e9059400040200349a6240311075840304140d85113006006c1444d00c18090307003444003200514407030f40190b0810070a800010101e14414050f0317114242d40030420244043d800f02840d10044446081030001141140c1c0c404040f0b0301792900c113855440180e111026503021894108101c00c05d1081c1c1800803c000c0c00d04250f5100f000c0e0030305102420081000a50f98005142001950380f440c0e00803800b121401182e24003907010303020003142401c20188800104d10161018402c81c0c0224060000a001d001c401e041404082e400c0303103228096a02040c0302550810040340001c01c8a2803107038842c008040003504c1000034045518005c48429 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 390297769 1250 390296519 390296521
    0xf0f0513020112020a110304082505060405210a0b091005100e070c0b0114041406010c110a1205060702010606050c0c0d080705030a0309020f01020a02031207030c02190f0905 76
    0xd070741c00c50041401c80080640160745d41da103482003640c07418214200c00020780f0001034002200742c000300750348a4500e0002c1c444412509450600c44492006014155200400704010401443c00303c4940b0b03003829081420210402c07d600032903041403070078034003611000709010400102240c14048404000000d10040000b42466030550388800c0c240c0c01540c0c04245a840440c400300e01841421200a6104a44181c0e40da100c45251603551070040a4501607414102020300e9510740340d010f03c0c4103400681d00e5013003465881e00c40e03207082041c00490613045260030201152101944c4240111207000e01c005101909042070000e00311341003584420200001480100403005020566908080003203600d040384103107605000c2d0b01c603c51a03100400620000510102c0fa03074040c0c0056007030500856690321903402c004010f9880c2d03078440000a40c50342040c00302403041c002c0c0c0e034007a01401e400703464056a00c00031640800c0348000d40d90b00302c2c10002841d50007045266104441107024101d684010301403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 390299019 1250 390297769 390297773
    0xf18050115060f080112080c0604110901091b03050a0b06041205190f030f030228090905070c030507061d0307060b030d050909151c0605060402031302060d0b040f0f0513 74
    0x44030306004410040f11b0207280310b03040c0306100003900d44807228482980c01c4d504240c03410140b40403542003406d00600004000140c8800303184108071300080c1c068001e00c1c400c201c0341c10450091170000c20594610b903640b45103c100ba2030744000791000d02640c4020060322107681c18550326213005103a800950480b4850400001009002e94400907541824449000c5003440010f074081d0140b6880500d40c1c900e102c000c445641e0044521002804c100c1d15419426503c805820040d071703e040b5540d00204540384240d1000a125000038980580236a0300010200061301549006c204100380d00400e0740e0000c01c02c10144465441481b203c940120000c2600c40e0014401034074600814884906c582000b0300021540812001d0405100704010030201d202c0e07181c06511040c540f11103e0990340640707444005810360030705100700c901a4181b491441141440d0b07034200042d540c0720300c498041c5151039101da4005519180181c1110300070701c020101c1d48100641e140d80450f540142142d01a007213050300070340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 390300269 1250 390299019 390299027
    0x5390a02010306470307080105100201060e06010e01050c0604050a0b011211010c03030f06061806090b0711120102030f06090c120c091206090a0b01060f120f18050115060f 75
    0x10070351007444c46204d001844489406401c40c8149032044410001081044140d40f00ba4114140c501c12203c101a07820003040403401c91700c441c001e04001800e40c074003081c444e41c040c40b4841a1048145046450105000029800e105040d1070440e12940071038030303000801288034111030142040c0d17151501001d020741c4039105062400310ad00d41c14804880102c40505210703800110b10004842818406c07665103900080000e4403a03405c0744045070440ba13001c039180c0e01c10203c09040740e6400c0c88050800500d42c844801144142d8007041d800240010000070b2041c0c28009148554410320010601b8682041404003010b03009140082549080140101041d088441d15421906203048207440d0300e00e01000c80e03414404c120b22004c0c46c0c0314450412241c5040018100c44a41c400c00c00040103036618a4181d0b0191360040b1000080786019000400e0014070b50f01c00d107141d4030f18501c04101070014046071006030048040a58032a5100d5000e040340781d80c0780001c03100801240c541080301c86c400200c024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 390301519 1250 390300269 390300329
    0xc0f02032203081602010e0103060f0311010203120907030203100501060c061a180a0b01030903091a09060f0d060b0301060c080702240703020606030d05390a02010306 73
    0x80001101592980888000101d480c0091a0320080040d550310840c403400000440c6074204038001010100c03c500da952103806520b045590076000020118110303620528843c40000b4040d04520061041c0d440c0d2400482405004c0d840c21b2015100b100d0550040c14100300301148000383c00c50500004000440d84034486144498204c900051115840c2007502031040701241026404109800820840c8665411181c040d0115000c100700c80003660b401034064586c43d500c0135000c509203c104004203c1d07180202004034404103e83c81c585081d02000440d6900104c03041c030f10909000c106640217101a10990010341206580e4a0449d85800d82c0113045111074100104010303004580c1031300710b48500840c00682d41b443c0c0100034120348280d5000c0d1183d0460041900140300310704c0400c4441c140881c0840400c038469540310b14005946140c441d0500c600c80d90071004040070b4160409984280c218606070b160740a029007060054ac5c0001001e445803604807401c44281105902e00d500701911240c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 390302769 1250 390301519 390301537
    0x9052e061a0c07050a14040605090603030a050705010f1104031406091c02010e06040308040c06110a0206160b012303010605180c04031b060801060c32070e0105040c0f0203 75
    0x1242d4468410241500340481c41d44860b402040496000c15880c0042c08600322940341560208001741e56035080018034031060328460b425800030070146840510031340050070918050000403a0030229483c12208139802504940c0041c000440c2c20300401c4203101c0d0085070342c140c0000030800360038440081d40d110780b1200c1140000392510784460404600030b41214848000c0c10050321514680343c00e000d02103541c00c9800b1034100401c980007040c80c6005800b4100c00140100013400030100c00d40c01d100ca03e500080c24203443c41c00c0c190000d0005034000350154043c0074582c6134541d1081c0d0181070700405407458030105100b82d041140a10103504d40070204000c0003400340712009291180c074186e800b14450780e0400703404641c00788e5042a0300040b1000e108102e500e1591404070503a81c8010072130f550f0001075401030100b083c06080104442407100700c08d0360401e807007110440d940145840f40c2c0c5818050740c003041d41800c48200400282c9014460302500a074682041e00031081d072103400035142e204154030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 390304019 1250 390302769 390302819
    0xa350309061902031e130b0a020d18050c0913020405070e040c021203040b0a0e0a0804051302030f060f1f030e061509071101110a1701050a052209052e06 67
    0x3019040c08941ea80c00b41c5407c280d6400715820419050b4010f0343c480e540711501e0780c1c188103a40b07a08226030045240c5480d0480301801e40760011008001d0713a00300242100c8a4450742d900c40c400540d455214150194005807200c2c010070124a087c402920030184148055401c030340d9001064803059000c9a6110764450850340303035640c1e0b18441d40018165034010442c0352013400c1d481d1040080190090084c4e400896009042481c51a0240241c0c8002c5030f244803004c00c180c010421504107403104181100c001020442d840c102c0f0000580c66546041480e070001e520346404601c499014810f558000300c58100c60702c603021051010854540700a4a24420080c0030340010208090a40c4201510820040d2013903907894540c02c0203100c10348194010300c15025643c0000b803a4a420b40e00d9000b00c6d100640100301d281c0c030365004444004a880504413095481c1c41e0428001b0303800784200d100c2c103580114a00c54a100344143e0026440c1180c004007045840d102e01070010f40040800c00824000100c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 390305269 1250 390304019 390304021
    0x1b090f062f0d0f020f0313120c0302061317070602150a060b040e0906060102010c1e050715140a0c121a030609060601020d020a350309061902031e 64
    0x110031020714112089007100d0088051090149a00000e2103000c2c1042d81d080361403040440c0c0c1070703a44922810940005000c5038540400880c2a01b184009926003e40f0707940b41d405c0e0307032034010884035404155151010f0307502100c03c0c0b20104604088484404101009101040c10244041d6442d151140c2e580c1c3c4008108002665403172081d046000278040004c00662203942d40e900d00c01c1420403d0790808507a02031140003031110b5105101c0c104901c61241c0d24400c12202595525144075403489092007008010012030002c140c0e91001280900050f5400040c0c0009802211118540140c2440080ca040c11002d030160313a48020200d001d121140000217064509190303c2c059001c000c014180c240c00f40504018404c60081441882000f0030307025151601c42d03880007261a0703902d81c0802408268030a2800d1764a480c0a1a21207954000da402c048c2041b4024690f40419002111000000ea006104108041d4005070100b403904602900944c01c500704002d61603021940c0b881a41500c6000c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 390306519 1250 390305269 390305327
    0xd02061e0c070f030c15052503022a07050105130306020f070b0f0a0c05070510020a0207051807021506180714041211060a1407030e041b090f06 63
    0x2804491a8507400310701c03050381454900d03001d00721a010300d6055071030403072103607003c400d09046d4010f243c41032642c00d0444180c0100b00c0d0004003200112001070b01007580c24012169410075801000c07551903118544100100d0381c04071000d207400d01980185040060078004100741403403c41c220010340398440c801588400809122644034061210060100f04118051286c640c01201525014000ca50303003d00c102d4000c0f240c01d607035900c01c00030b00820592000107202000f8030310350b014002d840c402d407041d00e502c159218001400e0700790155803566010360314000c2c0600310390100b290180c0764101320320840451030f144000800d03c1d03800000040700c280e6002d0005560910403245990359100b0422400d48890b101d60b400c90040020040880e142e1401010005941c0b61403002d0300e6175087d80707035505060510a414005499088890120240705d5401c0c9101c40540d994040c0c00305640c22070450102000c0440c4004020800c240c3c0130030402c0b070f03006400384403081d84060f41c01540081c18042c414014882c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 390307769 1250 390306519 390306541
    0xd02031e091311130e0c070b27061501180e0405070308040f030303050a1a010f02030d05190c0c1106070320010504170313031407050d08090d02061e 65
    0x31aa000d062503280007250106040003c0c003400425216114295034180c032440992403524065900c5001c0d28028440c0c0340c0010880d00300c05d03610000b2400d0604403580380e60001e40b0018403403003c0d40d5807500801d04001c0c00005024403c28401c50074070301040a400c90742821225010240551141040032600090510a08121450045920000b2150741d41d64540b10f0040700700c003a0108038006401d01c404140140064054058200760201880d24020041c1006451240c0701079001820360005009420110109101c2c151061507448004a044188401020700300c9a44009503070501c80f03201c04120109030308540200900d2001e5694541c1c50702e69090580e5014400d01c0030b00c201340c01484070303281c40110640003140598810100b000b801401c04078890560b000840e43c071804414103060702c1d00424410340c0340c032003081c01c520134042c503040c065207400303003068407461b01080816500b03028041c14090400618a0800a610140045003064001219400c3e80344110803d02c6c1e0640d80401c00606031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 390309019 1250 390307769 390307789
    0x40204020f1605031e1804020a020a0b0a050a0c1803030809070306110c120408030304150216030206071e0e0405060406050603010905100b0a050a12060909050f0d02031e09 75
    0x10b100080141c01601e4600141e89601800c0043c6440402c1e106140713840840505888255003250880c80e907100c1064140002500b01e005844114032500d80d20401041c1840b000b54000c80b20348801103558900006514290b400c0050000c0820011080c2000b5598030300c4101c40540b80e261402c101c40f520b0700a40b4502d420050f030000781000f4500b80c0349486012400c4020042e0752141001d6510004103102503c246018906c50450150020400030340003034241d03211075580b8041510018100402408103001c00d0014140c11070169221506014404d43c00945007000032000184020608030034410090040141e2001c0501594940b00400c915030703140d8106a004d00701c0a4035541d103035039403071014002400c0103079081c0c1e4000d441048046000301c48003080f940961890b490300c81c0382070b0502400719000262480a100d0142d6100000f1400480301c0c00b801003520b000b02c00501f810028003803000c0c14074404188000a6500c00c1000e040702c041d219003429408205030041544070a90070b0041069a42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 390310269 1250 390309019 390309037
    0xb09010c03141606060f23040617010b0906100203070303050402060f070302161e0b07060e01050c0703021209010c15060e070c1b23033c06040b040204020f 68
    0x3000b00343c00e480d0281d80ca081d0580940a284103100070b5079502c0200b0041c0009001d18074104101c07881042101c140c21404807004c1402500004030b9a503180800c5403000d54030302211500e44d44a40140190f890f113200703d540c000a0458411844900004006ccc0d80c0e8454400001e05040e11a40003070295075803201034440072800c1007000d0750f50f0450381c68002d45030b0200d1351122a0005d1990f01c080303940c1e2a07450080c0075509180c0d4130b0064250908020201da07800240c0211007140d1110f804e0408003030700f27018403401440c0703440f2256168009890080e041c02461900450380750010310183c80f00d40e80c0301d901080850380080e50309000e038801c0c441450160006400070404040368030280201198030011400c02c050043c000400f81400c5a500306021021510410b032441003141426903030450840b0001240d900010b08032240e14107280b001840c1d59504000500744524980c2035001c40008940492424800b00e1000c3c100c00d18103650f0b034102801000e40068025940810301030411001c032801c60b20215 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 390311519 1250 390310269 390310307
    0xa0b012c060d1d03070305120a0e1213140604151407050a0201110d020c040507031d0601140303040308030f040f062417030f090d080418060e010b09010c03 68
    0x3455900c6803901400ca81d030445040030300f8180300c400c030260b00070098508007541360b0341c0d2600e0b040914006011501010b005a051103940d1ba401c04d0b4200d200304550308010441400301a214469130034402021105035000740764020366909034080a42e03c81c0200c4041d1440f040d40320b00384403014a02102c01c0006074040510581000070f0160a100d000142120040e02c01d070b9400460030040c08489403608400081e0a026900160390212103140682285034080d44500d40014104210741180c1148640d0951100007504440010310031100c1445100003040001e900851416146541e400c195100081915802c2f02c00c8401050400906000c0c086c03201340c002d0b6050001c038a10341703800c0c0315a40c00445031030314400400f240021f88064000c001c3d580c07906090003950030103842d402a01b40d144e0140c485942d0015095414000096072100035001900340e03000c004c910803212000c05400c8540340d810252200304200b00420011030700328100c4110240078a000358980f85945019200901070400c0c00a902c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 390312769 1250 390311519 390311527
    0x32137021309020d0f09120c05030c07090f0e0109050a08210109020309060a05070e1302070b07020d030f020403080714070e1f050a030b072007060c0204050a0b012c06 73
    0xb4010b4018042c101e088132005c00c010880c3c07684c24030441c0d482110040044100c9240c01c1ea0203401100a600868012420307246801d034110115030800341075401c00d80103541c1d04c4943c440c4080c160301c01e80701c40310416402000b1118031521132039952036560400400d620000940f4142d802000300130704d0350030303680c103480303d004da50b11000e80d64040c0d0000c4461820b14455800010101342042c01020b0040c2c15589480310300b00c5084061100411100400c9401a502000103100003940380700c00610605a0380d02130410a188990000e0076a0000520310f400305005000c00d2001c01d1001b000ca408155000554086494020030280e00384500c0d07904c4812011000340810008404000f080290038228164081c1d04c940c40c0c80800c2209141c500000e04a0315011002a003604e020315840384100c40801c01d00341e111405445500c0ca040c4081c0c111800184121000d8021070905029080e000881d1083c01e203e004004030000380750b03c6d00000403808c3c0d100b40c050700b4900c0056001d40b081030014060145552 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 390314019 1250 390312769 390312779
    0x3051e03040302060a03270210110a05030d0c0f11060c0304030201090506010303020106060e09090304030803070903241b0f031d12030411010f02030702130e0321370213 74
    0x3090703880c03500e40c0f1182e503001e4000440c0c02842c1d05528008e60051001c48141648502140d14001e94003521403503100e61419080824002c00c06050780c00150740001c6400c00e540c42000348010070160340401070007110700b100b030040c101c04610b07141c1c03056203600c0c8103480781d42d1410120301418101d40c0241850041c10004000c1c10740c1904540140d030300c69100c0c90061130191040c0590410708035030b0800303650001c3c0014000207844000441d000340c007a19000042580b60341b81c0307a00c0c800c24400d004901505a940f204041e070070f5030040644045482d508849000c05005015210300e00c15403e190425030388040d036040792416408070440b0201480d044901c07154010ac061401a40196015a1010030303083c4c0600c05136200d035a440e1100c41d000e6014504001b401e90a100014661010040041d0b03168648032000c0c402c20000b814a010101c815040c2c3c22a00e08091040d00d100030300b810035540d51910b0b0703a454081408860801000c1610700750004c1d0908117403104001d00a140304011124404000060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 390315269 1250 390314019 390314021
    0x9040e010b030c0f0307030b0c0705100501060311030702060f07090f0801050603100e03041202130c020a030306170316060605042a08071b02011202030a090c0b0403051e03040302060a03 81
    0x1800c1030b8101c4107010004010051042c9100041381d62691101c50240009014044600d802076901507007079050451a9403900d003069401a0035262159858004210716030b45030055002d600d07001d4404510350f00b005d02009499200c010300c080120031500001c0703a4454883c03000076005101900700300b41c2c119111002c02e070107850261240351180c4207900010125591511a074040e101c030b02c2004500c1c082c5008800b98441c084243e040e0391084405404c4005801e00703001e08940805542e0203070005c2240c52801a0888000c0c0e0042001400500040c1881d0301c0000201c400098440c559010790071440d261040240045800254005007061481c0c0c4003500075000c11840700354001c420050f4503001510845160a085031100c000030780810060320700520b010140c1541d1801854550b0071205690401020303a8002d80d008024035070f0b140c2c01403090280c4410b81c0800350807408803080c500340c41c2d900c3d1103944005a0305000ba41801608501514030410011140295405405c080c1c0752003810750050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 390316519 1250 390315269 390315281
    0x70909050c060c0c124e0f090607120f0807030e030d0b01050705300702060d0b03071205030a08090c010f08060a03080c0105150306130b0c09040e01 65
    0x9810748619403030165240340c8282030300c074203042c0c0780020032403070340c04030304000c0c04500c0e1601014040c0030f103d03080c0032900c2c6e03000e5021034a01d0a282140c10903510000240d6175440511503140611002c40c0a8054110400011070307071b904800480a549a220000000b48288a94000104642e03044900035003840d81100c054100740e44c0c1505e0b106070aa4405c0400c1d01600e507081c480480e150020442c9500c940000e45c00392207043c506240c518101245541c50324034104040700c881c402c1c0d0070030302e4010f4442d40d44001c0900b0104807203c0c1c2c407400c0c080141e0202d080d03402a024180c880d643c5600782a10346403130030081c00c0004e040380c02c0c542d03c041400d070600d5600c9074071400e6900002109000040d01328440000c819140080c182e5510310700c06a489011640c40b0720190030f45030300c060000c0000020a09400140c1000d140800001480c1d0402c0c20203244c041d1420107465010f90000790400a20740000c6040050036604400380d526035680303240305541c0e00d100f03418009510a01c0d0800c43c1c0c1410b00154400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 390317769 1250 390316519 390316523
    0x30a0b0909101104030b0402061605030c100b030106080a060b030a0209041a0709031203150f03081b0d080f090319030f11160809030304050d0f0501110702060406030209030f070909 79
    0x304683c03081d41c0e8040c0268400d6000140c100c0368864045001400d158000700341c03071140e41e41d414110511a40da0541164007000f82100d85510a204030541060140300f88000800308400030012203150100554552492080142001e5612007100e01d9540b4144007002072194000c01c1c80311949041d2403c51030851180d2146922140c1e180c00003035280e4014400340e0266504807545040e031954a807400c6024100c0142014040d50b902c0d0000140c15010070704600265114200280d1684030b042c60651108040707500b51241540103070314000403590807040c1c16802040b4440d030107140da80c032003159038514071512480d01e5070343d1300c54200c260300d582c0d00d94021658000c40101c1440450010a191005401345000e485818000071048400180da41c600078210948003a003500d080640e58400142ca40301800c80c242c803003480540d00401040b5081c416131030400304040d550703410010366801041590056010310310615a00007260f44041d5010410340c030503040070008075900300380c65074030300e20181410180c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 390319019 1250 390317769 390317771
    0xe1803131701050114060d0b100207030218060a0510020109330c050913060302060d0c090b04060c0f030309062a052d04030506010e01140102190305030a0b090910 71
    0x1030071401001c103000c0c040c1201d200c80c80710f0510842c940104002c03584010120300250340c0c0c0d0b842d5500c041e1500d070744840403803030f8603000b6142183c5540180304034011520594190250908200016581c030a00c0345015030701c094502442482c83c9a40c1070307004180c2a500a401d072203032240d0008040740386610440c25580b1100e0444054212000342405542040a114000c110284807500c0c441c284805040d1036004014030129400d5644d0300815403c0c0e200e14030303500e40c454407404004030160f0000340f110010640c10304201c0c030b003074070702000101a0603c07020000c152070341c900103040c00d0501c00d40080e0301154000700b003000100b000400b0642c052400ca4040c50000084111640c80d2601074001c0c3ca990a4403039000300e681e640c2810284010801e0428070321101041444007001148080003200e018010340b400200a5506080060101c02c16540042e811036004010b01070040c245940b000c080d00350315090598880d140c6c09007410140c1761070303200340d0303000309140040200e9148000750008151841d498 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 390320269 1250 390319019 390319049
    0x51309020d0e2103061909090303061508060d11030610030c1d06190810020702150f2b11090f0603130b04050c0d0302010b03070501030606090e180313 66
    0x80c000740c4400c64110841d064020500b00c042c2da0003443d400a50f40444020070503c0b41c920006106800f40c5e1341c0d0740041031607603581c8800204243d01407084130017414402c035817001c8251025100402c0c241000b400980224a440c11a0003081400600418880001011303640249000180790f0f00002c1d852106807001107c40c10001003044905100b0040401c40e036400e0000c55070f40ea02032084002d42003d6500740c2d02e151400015003400300340300c080100102180050703038404441c0100b1034080e61440b000c4070705010410a001010104208641500c0c40c801040580d41a0310361017250700c1401c495000d481c0c01e040180c51300c0c02c190b00000404c0e6280b4104c440803c640c07400010302905000c101c0300d4400c1e214051035140c01182091040541c003910030800c40301a655844089041c007406072904801507034641d00d40d000d242c6014400803010341400e103005c02c00c0518049004044580d5031280c00d1758418941d002c102881c401c1e484030fa20034410b0380100ca90341d14102ca40d86007a000e9601c2040d4400185003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 390321519 1250 390320269 390320291
    0x405070c06060f05012a0b10140f1011071a0d060e01080a1e020d060b040b04090b01050121020703090e070302040b070b13020d03090501120b03060c0703051309020d 72
    0x400004142c44045c2d451824010900724103941112078071000c606440e4084d407400000880810b80e207442001a00070f29902607103808000c9c901d000e000c10340e0300d1250b50700c40f2981002e0b88501549000d41001c6150540001000300f01113030800740c440c3c200740c04280c6148034000300c2c00c0781a0010301c208200e0030810441c40c1d5031400503d80394202030103080580d420020070100440c0705921a0140092024001c1c0030b40c1c60030398002917000c0c80301d600031504651503040c01e10322403809104a0150002c203031020722803420f955a900c05030799014050103050128440035008801d5550403005451a20408215039490090030302a202865600c52178242124140c00289280c0c424001e50f8202d4074580d505500304034451fa604408450020a10040501600c1400d00580d1380c40c0a103014841c001d8a0380c081c15403c2c00001001c80c8507080101e05000d0500300c5201560310b00080d403590201900c40303415140c079040e160494052242c4034891350514005807001c030322180541e0040200010184041000c48120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 390322769 1250 390321519 390321539
    0x3070e031f02030702160807050f0d03140f0f0304050106030c0609030b0c09150a08060306150307150c0507140117191e06030f1a0f070c0602090405070c0606 69
    0x12400d44058050021240400c0c500030b40107180c22403000c4c0107540602550302c402407110f50301c5500032a030715070185104200d20b003070a2105101000d002e0740c24030020b06003620042d1004500300315503c1040400601400086000d4003a03520208140400c550340381050709146004c0c1502d0b0206540c1c0140d42d4000207025030080c40c030902103030b50107142050035507101668078030250070100b19150050030100031800895200720040440e8100d58448844c1400c1400038140703480e500900d2012001840a410a15640d0024840c0c0840380c000080ca000364035604000c03200712440c440d00070800d22a01c00c01040c512190311071000190000e80e00e88285840c004070000e00203200340c8560500210070350308030400d4401c03600040c20041c07041150b0036440307500f0030f45201190b1040d4020f4640d100384960b082c040010902c40641482c8240383d001085060408a50003003c10140c5101c0070300c800f2400820400403903406582100e02d009008120300e02c0c0651000e440490884022207503289070000c041141c11031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 390324019 1250 390322769 390322783
    0x120108060a0b100f09050607061a01030c17100504050108060414030703080a09170a050a02060c0f030c13050d06020a170f01050d05031e1c0606122a030203070e03 71
    0x4003c1a4020031075040e001990746140800c500e104001c0034007800314103612484001c0c983e540c407171100020320030450358000c01880345852074181058203100801d000c6641c400d0315002c0314000c5009400d1940c44600030215403514640c0101c1d001400c01000044000d03010585a01c59402500011280d18988029949030f10416600401142040010130780c061613980c801189a8413603507055500c10f60481d4020f486401020312400004c200040c48002180d05025403a0000020300302141845c0c0c0c07941140b0000c0c00020601903030018041902a4411480c403810030040c40041c2150109010f02c2c14540c01a51060850700c011400c83e9201190800514010318452070b65540d0802c026400c00c4104954010394820698241c40107101549036018282d540030340d43d400305400f0359a989034200452482c1d01508544240040c0713000d104010b0075401c002c901000c070030140e900041059400c0c03940001c041a81e4501100e106004000c0e000054255004500926240c0c0711150700c40d040208140d610b0341 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 390325269 1250 390324019 390324041
    0xd0b1002010207150506011e03180b010906080c06030f0603160f0608070c0b07031805011d06063703050a1505090106050a09022d0909010e061012060506120108060a 72
    0x402349112400c41480b1550300307006c0c40c01d68500824580070b2101384142c01403910100ba560000154010400520745205940c002c0803040003820b43c0f40d60300e00c0010320780d004c010214001d840380750340000c9040d6000e01c042d0040c111986041d035443c1d07440d50b5201250b40154000d400c0810b5503140461a20785c0242044540c4a0740090702c0d68060340d50050480c06080380c41c0030151203a410a0744040003410a018081d00452a000b03250b02040419007080c1c40d007000580024054001c451414440c1c5003001b01200a8021204100000c03041d5100c141e245821140c0c4050828040e03082c3c036008202403a4003565112005d4001400a038076600c04083c201c500511406d50300c0380d6402e504200660032900500b03240642d41449119000c51740018091104102149510510001900a0051600d00040d80c09860580d101c1c0b4032030320300000401c000305103c544250070720903941c80b4014070101a800c80005007802414194407940012003048050702c082c0190480c50003440c0c00617806055a10842185907 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 390326519 1250 390325269 390325277
    0x1050601110307060e010f06092007050d0f090902043809040506062b0f06050915040603060618060b0a090612090501050412171b0d0b100201020715050601 68
    0x1c441070303444500800c1205d8280f403140d500c03407450352948a041c0c03150030b0003000c81120209000580811a4250303404035029800004400e006141c081200000c25030441003c1d41080e508000c010032040c0d035024003130ba1081d0300b108e0001901203008401000f14a550b070000180300c0307500e181d08003e0507a045014070f41e400c04485042c40640d40924141d004540c0243d0043c014901d4841c0300800b91030401d00c00100000102c02c41081e07407242441921a151a01e80e00541c2000341d24201000074407404030240c8004140409051911900d039070705c0d40078800855010b80308018660340c420b404110361020114130141c0d94900300000401541784011120a00035a0b070301e07035116a050503000c1e1950321410580d085030315582c4506c0340028400b4481c69020f00e00800019070002d00507070b0020100404498400003003106441400510042c8204ac40010000f1750310243e02c48004510b15001842190103480d403084140c880e0710100d54042d40100407150107694500e0b58091012030b102c043d51000d8602500003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 390327769 1250 390326519 390326527
    0xf0102120921010504030210020f030703110d052503020c030409050414100207170a0903140f06040b010501090e0c0f070303241502010e0a08031003020a090e010506011103 75
    0x808103010007400700e07503001441504030146025070b46000101c1d072941e035007450795188140001d2580400c00756480d0614442e0552078107045009220703440c000a4200c909054030b03524200c0036508080c1c20b4680700c0d0f410781d2080186103042020148000d11500c45442c87c1120403046002c030302c0c401d00865807103406881c000c51504c1d1070034035010000d2800401c10b0b00c5041f821040a00c03504801d011059044602c40c0c0096240c1003181009a41000c0e494007528041c00700704440e00000303410200d0102103942181200785030041081190f800c2c00c900604c01c1c803003800f850080000704602d07203040d681603d40c00c4c1da07400386080d1520ba4000c80a9800e4804040300401803283c1d02741b080d0554010301e0500d01c2460013180303e41040308000d100f120409191900c2c995454028042010386c0c880b5501c408401c2d100034480044068191622886054000b41c43c1c81000000034110701c81d040b60110007035034090882d135134543c0d40d660308000815441305c0c41c030582e508290100d10325600c1a907209070798000700c50265140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 390329019 1250 390327769 390327793
    0x1090207020319141203070924031d070e010806090a020904080c0307140c0f091b0904060e0106023d051e160201060e040c0e090705091501020c0f0102 66
    0x801d2035010f0f411103e104007180340c0280c0c1c03a01403060341e0b552103040c0e84040d2070341020080504140c240d500710805010314a041011b84e8464486203203210800c500340024003518100381e40c0c0a404081c403a0200e5480340c40400035519003001c000c64100c8000d6015201d039601c0e41d0341e115403039800d600d00c0694452101c40100d4041040c2c00002d101d0700204074112807515119640c0d62400000d080341c4885207401c070041e200d002e070401145e4008112422a000b51091401030324100d90300c02c05a43e01581e00001103401035441e1620362228003d0142429480b54540c1d544030025922646445040c4d0105501c01c201192000702c1401c07910b4810b00c0002c04010103207003001a000401001b402c42c00141c814480c2d1142c50800950900d0180c1c403580803204070b80720041c00103400d6a407280d0001d41e004a840781044007013800c0c891034400740c1d400205070700041d407907110b2082d00d0081a074001f60f900450200c20300003441a9400252032103482030b001e407610760300c40004008a0500c508045400b5800840750070361 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 390330269 1250 390329019 390329053
    0x1e0512060616030f1b0b0108150415180204060f06140705030901030f1b0f11070b040603090206070506010b031605090d08030604090b0405010e060f010308040b030a11160b010902070203 81
    0x40c80c0c0c0300d2131808401c2c4c6500c1c014144840e030304969068a050b081000180305101040c40f00e442940610007021085003412fa840008803000035660b91032042e0307100ca52161000b482040c42c84601e80040003070000c13940380d42134030a020b07245200b6070700800c12032301c0620101607840003070398030b440d80082c0a5414040740c0001035010b008520000301b0800e07070b20b0044c208560250b02d54004041c003190360b00c007004026004081e00c0d5902c07464000d181640703c2030081002005c60400c580544a41c0d180100d000041031002c142c50b070107880e60080c0980253300c004950502c030400a580b24681d181d0245407a10368405055609100e10441369810074810344030a804902070070011a00000050070015000101d6200c2c4030140c0e00580d03080342d40d80d46a40c0702285001c01009916004400a0386600d05545560780d103404600c034a115030b90803a2400700c0002c5400d00140d000e58100a483c040c0a655214010380b020070003440d80710102e0b071a4445100100c6d0307901c030a200b91000c2d00c0c1e014000300110010070b40c0c022 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 390331519 1250 390330269 390330287
    0x1e060d08090405060f0925020c090117030712020a060b0603040b0a110903030406050d0c0216121a010909121b02060702300106080606010f0e011e051206061603 70
    0x19030045214000d041583d00c1d1540106d02c01c000304194100d10020600c50344403903540c440381d001f04650020303c802d02940c5e18010351504417400135036288840481441d195041d8010b00304050601000340780360500b100d4020070381e50180d501c148410010001001c04001a41c0000e40f4041d2060100c1d8000600a5405910103039402142c1d8003c2800e00c1c072081c2c002455544641c0080d0001100800c0340c00c65170030140500d443d071090070b0010f022903041107101c45c07010000600ca20804981c0d03211841061180440d02c07070302950f180c1111002c0c95030b10703449050090000908103d0b8078501c0100a40015403080b91450090134001041c5030011035542c08200e02d507001100c0699005a40342c17070030324201410340c4000d4900c0c114009180056050140a2401c40d1401d50140361541c21000070490140e900c4811404156901d0030844c200f8000c43d80103c40301d400c0c14200c2e54110450083c64900e55405c00e0152141028864400d00103555807400e00c4014011686001c60400054a400340068000c0b842c0e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 390332769 1250 390331519 390331531
    0x1005060a140f21010605190e0a0b280207090c05090a030308060306070c030e0607110a2d03020a2106050a0501060f05091e0105040306051e060d08090405 67
    0x14a0105070001140c0016032210707100016846001610075004204001402c0120302c0328681c2011079850100045c00700d00c070b80604c0812400e6406801803070b281c01080071016405000e40003d0310b8a4855034081000c1d80240754280c100315a5801d0320b06510841190140054039076400313440074500d0002d0f10400b4243c5240c03150705210061200c00c5050711180d1848000303502070395a01840d400c02000345800d088024012070701b00301942000c0b601180d0401846c482c64482510404c2d0b94000c14181211901140011a50722069100f00081d03030a9805203291741001d4050b0041300c0865185180c00d40120281c40000d4010149000400a2506011104175201e4081400400c0210381d0740e80d000480301300f02c9682c2c0030183d40300c0c0103004107580055660418882400c040d46001510000909448040c0e01144185548060801656484ac4d0240e4006550110003070000d4240300101c0b1203c0c0d00242e002c91528015100059140c1c43c05200420000d40c126a1203880c0c0802c520500010b00300082c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 390334019 1250 390332769 390332777
    0x20a050609030f01180314033c0702010911030f15040507120501020c120a05030f190e0307020f090f15030102070f030c02040f05220f0c0e09070b031005060a 69
    0x44040c440c0001e01a00200440c8449031300c500848a240c041c1c80305208005a98048000307100b04400c007160a0034555011f401c000b608050a502841011036040227000d510002201900c28480115015005002d449210310042c4842c44440c505255569a04060384902a0b11441060000d800400c113942c0d00030b400b510a81d460185c44a818420703a01150100b29284d030b500041d0300e006044103224450700100c1e02d0840303900c0d2440c14940280903000151480004841800204004259030b100151740c3c912599024490084031170202e03600ca4200c40d6007a40030390700500c01c0c82003503e40045424440e40887d400700301d1035223030a107100380030054141600f60550740c00c1108402040d40d44a44040141c4260b48840340401d0300d10612003960384020040e612142030106012480040c0b190450712222081d140b52000c580500308401c0c3ca550b00440509482a4031001040c00e00003035038100d200d00d003124101c03a03542c0d580305600c000d1403104680c00b044a1404010510442c42e210005004441c1e4a00c1c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 390335269 1250 390334019 390334033
    0x40314210a1d1201110a03060839040f061406040501020d050c16090c0e01080c09040f06030b1008150c0901080c1e091c0b060906010c050f0a110409020a05060903 71
    0x5058210f804d0b17010604166100410013003c840d9050103a0409400700c400640f0b500c004802018003c5990f217415101c2822285200814080c04406030340c0004e10010000d2000003c1e0754488001001d0600034809001c8103841c01c18810700705a4122021510107900800e0103164112045075207810124280106005855801130051159503820000d4901d090300002c0e02c0c000001c002d805148805802d0b41480064010010465540402e5030810001901e0129444560080400c020101c0c2c0d080209007130b1411080c000019245404ac0060790b9007101180c0c0c1428a0400e4141c03140412104401808410866448a07500c1450155002a5060801420540e05c13500409600c1c0740f00c8644411288040303104005840d00380948041d03c2c0a02590010781141c54540d200c0007800244464003502200003c00c003603074803444021010b550446c1c1a00c0c992590885071945805c00441e0542e820100c4d40c84100051030144a0545125070050200011030f10b4a0280701c03003034003d106c580fa070600a4030303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 390336519 1250 390335269 390335299
    0x50c1201030302060f0a0b3007170d02060c04050f060909090c15070b0a0c020c180702060114031e010b0307090504121701090b06040314210a1d 63
    0x1a84940c041e501c40d4020b06121300c0d18010313141803420700074200000c0604255a50b00c0540b103d182480034604000b2031100c0d42c0f603440c60031824548041c4514003080c401c00d600028807034201c1c0002c60800000c1820f0710510f600039141240d0302c480a603540444007504210030441c500c1d00800100d1b0950015042ca418004038a00083c20300b8011141d034249a008500d602d002e40c607100e461407040c0ca4141410500304142e0781c07110350801b00000d01c10103055558081000b212030080200d51003846000707000000141c040d5401000c1c96405132102e1000d40f00f1040046071294088000070300b000360240041400142091102c16001c4407210383d004a0f542c0e0f0f0700300006c540c030180030380c2c00508208080400d142c1080d00d171040501c4125004d280410030300c00b00c1c856110100141240c115402c82c8404aa155017880000741c49220b0396100420049400c4005c1d0307145c11000c2000c0b06081d048407070307400300d071400748002c071f0345034401c0300442c5c800182d484510000d200840d040508816402a190105d038083d58 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 390337769 1250 390336519 390336547
    0x50c0a060212040605091c0c021c03050406020d02190803040f1b0e0a02070f032304031103010e070501091503020d0f02040e090c0a06050705011401240503040b0109050c 74
    0xb82d105440d03042ca1400c100000c1c403255005042c2c018010a00030b020700b00f0384804004011459441050410141c900010155541c9240015a0710071500c01200c40104c0c91801802e140e00c03901c079081c09400381c1c2031400c40f65400410700411003071440c1c1220740000701684d140344003580028400c403a81c032141441e40020841b000c001c4510902c0460815203a00d082500200c501000200b542d6040350040284600080c1e440c044a1200c03689400c003207140384c00401020041080c4001ea030421920086400030a10284002200c840241a0020403071260030f540315a444803101e014803404118166030400840301c00c5030f403100b00c01400345401400c10882e0b002d0343d07094945660300030300070540200e400e0000d422a003d482e500b1080e00740c002d001d454945000b041030300400f40708a00c14010040703000018404c007904000c82170050680e002d40c0c02c1d17841e0706107030082d20b041040f962040391050044401d01c0d030280c41180c3c059074101541c0a8183e1a207007024024101c0149403840b80d0100b88840c81e20340b105 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 390339019 1250 390337769 390337777
    0x80c03191511041d04020604210f05150702061e0a09150b31020d090b040c030b0912030c030702160608041104020702010c060b04021333020706050c0a0602 68
    0x1002c046640d82c1d140080000300008849a400c207451482030074440103a9840341100c0c100e9182904c1041c180c070720360400b0340c80401500d40140c445a405401c190400c0780c04075114400c0d2145107052440740d110614100ea459000f207400498034018110003428480c10100320b5940000108400b20b442403e41e52641e980d800002d1280702941c1c0c48090000c07291801042039100c3c0c81104014502c5a0320150311203054109192441201d542d0008070004802659044114200e800600003012414180303480d4003401e2141c801580c28803002c80100728405404500c61010000c1c0060050542d00ca81d56007864507071015069000398810480002c80b01021002443d0003810340b51034800d06480c050829003a4070a4044440744200d10401000340142c0e04607000c07a080303c0d0010b07000648402580003090080c0f003420b4105201140000740080d40040881241801101d40c0d5502c4046000e03500c1000100700a03034040002507007000070b05001d040c0c8110090204450a18201c50080e5242e1319042c04a80c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 390340269 1250 390339019 390339041
    0x904140c1215061c0b040807060e0609014a0105160207051504180605030f0102180303030412080c0409051006113f2101080c031915 58
    0x8090b4400100d40e50145544001c0682d84d0704d9000410031a15102e0020075400203000300740020216003840808000c2e1040300c0e07844103040002e240003410860751014100d40c41d56086d803c0c0104101001501e10111141c550b10382118160310380d00c4c01d0309140c83e038900e442042c81710034040c0080321414024010a4003501c04000d1814103800050402400c100302504940e004080c400303011000a42c3d124125800c54900e4039500400303071502c203141c2c0003408183d800a40c0c18411000040c0241c0819070040103040309862034118444150b4007490348030b0108a80240540c0340800f1f98009950013204d540760300200b5145c100380703000d07240c8401d002190b4041d1510343c0031541c5484180b180c40d41002d0840410102200100001c5101c5051000d4100d0b1800480f105003141580a651a14007806002d0301441200039280c0c60300c09a50411203498a00c1e0451300d01032a041000245140002c00c0d0314145ca82c01074003800480c0100840b600c1c0c0055075200480c2d000c280d9a5078500c4080152144014241c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 390341519 1250 390340269 390340273
    0x30f07020706090e1810090b01060e0f0a0302041e0905160b18060a020a0611090114071725150509010c02030403060c0903080a210501050904140c12 65
    0x10509500080c41c010054018805204a401e001d01000c2c0030309200c4c070f40c800c1556209003148440302d5138050424860101e62034a85007095002801c0000b494002d40c140c071100e95417404a0901c81c3c0c20003c50181404000742c00405583e000e002508082e0840300c0140d07101e40220b22105c00091401313048900d101c5043e03c054200481102c0180440c0503210024023404900c6800c3c1402d143d03080001c80c0a2054641c85410b00050310240035000344084010700b80c0041e410000c2200d8146c0040c040c0c0d001c00c064900040700340c614810a001044286c1e030b00c00e0b41001e404130b646001140e001c42e1940c41300b103840035102401c0c10720440040c082c107000703034803280300340c4090140c0582c071705481c0c045e2800585503200c00d0341031920001d1240d034000199400c0344d8018101050400b003000c800d07a00fa803011740014100100005440c03040c15080401075001c0d191802094100203010034900c070441e1000e0050316400000e010204000c03031410100c0fa00b601450341e0950300c00009030400680710590541c1d6540c1c441e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 390342769 1250 390341519 390341521
    0x9130603030e12102f0301080613080307120b040504050f06072613230c0102010506100302130b04080c01110c060702011815090314121b01020906030f 66
    0x42d071201411403000d01c01d460b5401c00048a44940c0d03203c113150070000c140c80c0d0703460700c4007228048003c17544c00055803544040c0c0142826050781c583c03260b00c01d009420b02da03c5080e0104c1c01a201c0c0f400c00039013282e0410142425a19000e0049802e4840301c640d801c800354503070b1719015030f44d07507a03100d0f80340184d1080004003d0f40500b021014208200102500240446070141c2002c215190800082c44020150303580780f42ea440c814100070050980002420989030000c0c0740c10b444044401540742ea07000501103841c0050080012403d84e00704841b5940c224040a50b40700c410307402500030340705440c1079600001843c0e464564060440e001903101c445141d00005500380c13a540c10005802c0e401e60001d016060391034804011402e9840341480080c10006840000010017a000300c211005d01002c801c00501c10341611001030039124140401d44914080e0f52441d255094001048070980300780c07502d29801c100040101100904160455070701d955003c001683d825035809008501c5900003560408403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 390344019 1250 390342769 390342773
    0x3060f0c0c1618110306100318050708061810020304050f0609030306120118022704030e1002011806110c01020d0e0f030a0219030c05030726161202010209130603 71
    0x30070f00030003821101c035282c00c0c400d009509454003121b5010506460b440100781107134400301d004011203c086c451880b86a00d01404021000c606002143e040604440d031302d03112450b055100e00003503a050b002a501251f1304000c1580c40da005958024000e20a8035100d00b910044203040c9041122030043c65040002080707880d1a11000e007030803500d8154020032080d001501401c612480e6158082c1c42a1040307401002e91020050506004e41c2a01c00f110340c603400e042c50080d20440c806040b440c480c040b900000e40d0b2080c4140b241010600010103041e00785001621280700400310303000c041013400d20411002e820448240003c01c844d5441c848005588880345807258180400300c0004080d40d0020040d07002e000c1e6001039041110205100180c0c40303026245003d03a21b003100c11200524030300000ca280310500011100001840d00035848010500c0d000071500c0072144500585080c200010750b40650118042480c2009413481e04c3c000146044800780010b541c003860b00c3c001d0030880344c8840040c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 390345269 1250 390344019 390344039
    0x3060412090603020702150f160b09010c0503060d022e022401030c090b031f05070906031808070804090603050709150b0706020705100c03020403110f03060f0c0c16 72
    0x30042c038003032504500f400c10320340c002528030284860030041000049401348400e6105400c984826614102010110340545007049410300202d4000840e5481d100e5400c4803540903e040ba40304610084c0307035080c85051a401c0100070f502d1240c20f1f50080c0c5c070001c007100d10002e80c025826581c01031070300205450079040741c00021070007105a01d00400d40301e6000420005004101030015142000004143d030115075010901e0f191040c502c1044e800c1c10003090030700892321580311900070701d050781c3e580c20003d49806041d0190b940c100c1d00030144d40c8508542c1d1020130807000c0541103044c850a58a45000d565030064802e54003150404e8a043e01b1800003000740124a201e04001c10f0f03075040452454520b00301d590080e034013030840082c00c40d50300050060f042050500100b01c1003c125a810440002e818100600075041400b08580e900071025144045180c1200346000181000b00141447d9540000c0031050b403401500c20340c1040024003044d840c1e02d1003401a1410a146401c51601d03107403810786502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 390346519 1250 390345269 390345287
    0x10302030a0e0f0f070f030305030c07110411220305030a051606050c1306080709050114092d12060403030b010233060907090918020d0b0106020d0f0806040c0e03060412 74
    0x4030b4046c40e400810001c0d0b0450181d07540181000b186035112941800c0c207003420924001c0707050f4064545003c2c0d00c3c000c082e14000d4018103c80303240c1031641600f80b035a0050044c501c2d000280c2554020f03c510b40d002440303071004000000c000d401c1e901e0408541c0d0f48a8003992411340c1d040c0513100c008140c00c0b001150b469008802440240703886441410150000b504040c024015141040300150030003145031010800c03501201e5000e0542c5030740480704e4100300030601c48845040d00800024103000c603503191001241800c0142400075210648071590141e0042c882d54134600e041d4080c031400c0700d900002c4c0822402c0310b800220341c10782003100c2c9000d049a10302c7c402845184a0702aa5061007240d1340d1051030b505c250781503144000352621a400301e10f1581416182e00940c451480c4410f00100034820b03010702c0c121940c079000c42d505240c0314441070343c46040d00c01303640c2d0000c0d21a4001400520b4a0780144959164504000d01d440c110800071a0504600b01c0d82034402103011041081a1644a1050303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 390347769 1250 390346519 390346529
    0x90c03070e06060306120f280312091a07080f0604050405030d050a0b03030403060209090a0501061b0f08030f180c010203070602130807030507091514010302030a0e0f0f07 75
    0x80d100040c2030008040100c20081d290328051280440080c207039442e85c000e01030070090070f401141d03089180035440c3c030350392050b0746107003801c3c0c40000354400886071402039030413025581038444009400302d44074520010b2491040542c2c001d40c06c104140c1c400c034250340c0d00a0064503e0303510180315142c020000061008054025400307140340c00204004580c0c04010b40300a500c03501000f28940d140c0c0b16003d0702500d103114400c0d6150100060000400a41c0e50007400541429940c006955031400014011200c0920521000c95103584c030341041008005034070300003a88940810505840d00d03480d00400c641080301c1944150442d081440207026180c21030392100582d01e40140036445266000075101d0148241c000c1101c0c1d004200c03048428a0b05501402800804c0d085032140b50f43c9041c0141e6032841c520508888501c0c1c00400b680b01007000100800b9217444440009610b10f5200044009610003002041f08a40e04d01842038021400d105101d00c0e1103d0388000c005060185000d58240b10050b401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 390349019 1250 390347769 390347773
    0x1e091103040809040b0a050411130e0105030c15040b040b0705010b0a1a1b060903040e090c0f010e0f0a0e1603051302100c050a0302010606030f0b1806210303090c03 72
    0x1040000b40220301225034600040d0b41c04039aaa0f041c202040514001780c100710750007410860b01040c43d032401009000d103100c0100c0350340c00056407035018540e03040c02801003d4041d002007007111014280003440c1409407000010716440c0c5a5100d0f960038258001d5001b802d403404000941c40305200703090043c4064424203c55220b030091034000d10102e46c60710204102d25016010803109580416007031030ba60b00c041200d040d1001c40c03401c100901d4895003d03000d0b40614444410100310310540c0082c1c6e0501000014085003690182d000064036051103504625902141c01980040700d0348440d68490b0050801c140315480c40d00300f880c07000c100c04d0396100c5a0801c2520348020000c0c03030b86050507075a00e10354054800070070001d40e140044440c20701050015003e0b110752580082090ba0551101048685559003001540707004ca00010030307601302407180c660001c681140c00e154000680111500f117603001b0502140044220007249c0000381c40c0380c09500a80010003004503d0364144110310800e001100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 390350269 1250 390349019 390349021
    0x6190b030f0a1113051306030c0b03091515090a02040504091109060102122521031401080d0f0504150201050a1d06190902040f0b010207060918151e091103 68
    0x103001c0f2001c1605221703c07445a0b680a00d084011100750b40610003031740d00b008860f540c00d0344079640c1d0042c0b03600541e1080c0d52445024166520310b5502044c0501030b0254001403d04200e501080044405010780000b110560801c070000304e55945101e40302c43c0733503c078014007000c0e00d0042e42000b006800007841c19056421642c8400d101100f02c00440d0341e404076603084400d010000d02140c1c043e803100f0361030042080030000800e0402212082c40410b40601d95034042c0401031040500742c00c494400e02c00c0984581c030400204c61003600810a803035140c41140340450405685802200d11f030840714109c440940d6541040c407541110783d0090002c11030311050070800351030803400c84940d6603c000342004940d01031a10300945c0000036411480565400500507c4880f4420203490001c10010320f04502610034601c0010302c2d140244507030402c4402024600030303448821a0b02c0801f6151142180000c0c080fa640007007407500c5002d0940781c0140c03501e098511214104820b0404a44c003200303000440940501c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 390351519 1250 390350269 390350287
    0xb06030f01021305060f09210601060c020114030901141303120e0c010804030309081809071404060c11060f0307081008030a1d040608060601030c09050906190b030f0a11 74
    0x21014084900a07a0790694030024201d14a903140103000113a58007220683d07140d044080599124580520010300749c602c540d0f42c401b002c1e14039080d03014009000c00c0504500209200c0740001550788982040e00100c1c0320b01582c0740401c403c0d41d01301c0e66151054400305500c01415485a648031078012094420003620442d440c8855403002801075903410000c0480024003094840e4200c01c5540364003814940e140c5284200f41d074517445232086214010040a000110017511074007480b080750480c070074064985802c12508a80440100500b40ca0104840c1f0740b034121a01e40344010107841c0640a4469243e003010340700200554809072205d8015041040c0501140d440802156043d0102c0c1c00c0c5016400742461318484000c2070401003076403040c60302c80c00160005010840314400c803000d990030808006035500030380d0404124000c0e66040403075440024250b00b045c10090408030328544200c1a5280d41d1203a8651a5000302c2d4441402e034000d00130321034a10214000c269101c0c1e0b12400050400d00340c0307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 390352769 1250 390351519 390351547
    0x1b120604080c0304080715030c0305100b0a050903060c070501050f01150f09080109060902030c061206040f090f03090302011e170a0f1104051c051c02030909040b06030f0102 76
    0x40c00280c00400c001602d884486010403c8030002c0809005032901030796103a514003005114540c0520100c1d051040d1154040d11070311a0301d200e580400d0034000e00a0902500c50001c0c0c103d891260103029007040951403070b030340800866200b01c4000410682e140903510b0700c130307094502c050030501007100103a0043c40f1000481140c1d02103484503140c01011410b030514100c50501007030703011038810351800c400c200500c403068000c03800d07a1b40280c003111404204c072824480d484c8030306180c1e81c25181015010405a01d03158020b0901008803035000705403840345883d040c9110100c034904901107680003c1c20001c40d40c00804688854003020800c803800c3c2c0700400080c16019034015041e0b000100000014901a0141d101d236481103008241006041552010f0700825446070054602c900481003144040e802c1401188139400d900001800c1d84e1003003a2802070103c80c0d50210303082980806d106d13035241038903549060761007035000d104c1c10001803d100701494107000f28200d2802d056401000070700001c00303c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 390354019 1250 390352769 390352771
    0x100e0c0d02010c062004080a210906030519061203141204110310150f050a150c031e03020a030c03141503101d1e120304051c021b1206 59
    0x4113a000c2100d41002d680340040242900c2c1c00c001d04203010801091100e00051201c861a2140c1000b10103035000d400c105000403806072842e000680900000e00074144203802641d0003001000780e81031000342482111007039600d5a0840f41100020f01e210009265211a0b00014200210b00641c5020031000243c000900004c0c4040c002c01682c03102100b09850400c9000005501c040003000010502d80403500c02034a180316203070075400c859501048a00c0c103001d018045501604040100a6100c0c2c8150350b0481b204100f40e0034007800d00d0300c4242c50350f0000019801d107581d59400683c3c40d606040080c0841e02c103c051a010945004507501040d91003186142d00441660781040b21440541c00103071401709104103480280c5c1c10301001003242c802c01288a041c0c80ea0200c15669902d90003002c1803214000c605841d107003a881000c0c1c0010219020f00150707040b5014805881d51900d0500d00308100c12903140224005130301402000304003605080070311001e0441120b03141c1d13145030988007203a62020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 390355269 1250 390354019 390354023
    0x30403090e06061b01020405100e0306010614070f0803042d2319020109050915040f020d0c08150f010203030c0a0306030c17120301080a0f03030e100e0c0d02010c 71
    0x15440c0701003034072940d80c0010f6030070b0340000400243c800c0c0c0078100360074040e400ca4460070b400f07544d80c1008005c104d070052203017039041c503030140042960b41c2c0303441c4085076103022070030b9076682c40d000c2042048003040d140400e0840c042e001352002c641d80c0c00c0c02e1409070030075150003503001c80c01d814034040c220850707983e24040644190400382422000201c3c0703a0401c500110030303848501c248a60002da052340d00003540c409100b40c0c002d032124540c2c5940d50060200c6c0140c211140c80c880b0341403080048140c501640030300c03030400c40942c0040c00d009000f507541084540b0701d401c03e8045500a410001000385039000c54100d0081502c82842800113000041c1d030340d00010308413078810000420130003100340c4250b05c054002c60700204060308241e91001c06514202e11480300d000d442c002d12040881c0b500010044904940310308008002c101d1142d141d0350b2242c1c80d4940708404240d2650f0311407017100c4042100003220308420200044060780e1000041c90310f00d000310000d00401354407103a2000b513a008001c0000e425 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 390356519 1250 390355269 390355289
    0x6080a0b03150405190f0c090c0504121a010305010f0c0302190c060e01050c0a0201050708011511010e010204090b0a080a020f0915090103080a030e01060315110c1b03070b03040309 79
    0xa115880c1c000c0c181091100383c00c42c0324017104141828456001d046015540c0100d409148140e11510401c040d900d4030210600406c004002c10003c01d004098800c03155405103c0704002003449440d845440d01c0203910a440c1c0740c2d1680c80000d0b130700c00984140902200319050440c038000c00c0c2c8100104050071542c0030303c20b005081d0081014000d164208400c2900c41d280200107925046a41403040d8108180d23041c015840c0c500060075290080d00130078183d40798015000406010218121500e545d0710f080801c640d500c2d4006890104000d0019001400640d500860249042418010f25861301d034041d84c190350250110781d0150711400c40031080707007100b81e80030451507175503a0300c44611001452030356400100355030000040c000341c03a01605201241c1d070703000e00203560030700b102c94203030340b49804080c0000080c4c404110002d51150b00c0308034502e01350400c01d07040c00314a45e0b0690605040d11540a146568251024503620303050009501034407603010b0087c2181807584004040410034001c0c0f940070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 390357769 1250 390356519 390356521
    0x9080601150207120308041a061804061b08012d15140c0c090f06210703050f0c0a0608090601052431050f100311070b0106080a0b0315 59
    0x402d200303020801c06010407070224282c00b0318914000b401d86000700d40541d098402d4072162220103425456807809100c0082a600000c0d03000341c5c2c3c082c4480d1004d04210f03041c030759841010003d807213100000302100d1001e0711101741c5985000500c01007240200c0b100d10000403011884440030f121801d0900540b040c6500800c00f0300e1459609a8031054025030074420003c2c00f02341c0072030900000620400003d026600340b615074607103551840030b1079420f5a0b0584e110880b07400207061042d078200c00c0303181900c011044880342546c0740c41d441d00b07040e010100041c03940c01c00040c00c503081c2000303403841000f0581850202c00b40d10740b106269899440600805101d07103180e103483c40403c12801c500352940b030400c403041c1d5952564802030540e0240c100c1018188041c01c041084c0c14680802042c40460b00c0c040c04c4040e0030003e030003c10441c1a882803444090650319810a1400b0640c0c00140c1140c3c2d11a8180f214154105000604010300003020040094286110907a4548021610410314a5100b503c3e0880f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 390359019 1250 390357769 390357809
    0xf06070609050c0d0507090c0c120305040804180204091401050d08090d061803030b0301110d0e01091707030905030d05070305071401050703060e010506032a0d0504060e0d09080601 79
    0x80038010f0340f0042e031003641e04c03500c4014410003050407011203103100320070807520b03100d0a003e4030f0302000351034064541101c0c03810802046000f1b030071165015100d40b00843c5043d482c0e040c035a180f41e0314405030800c1c0c0d5501007070a0118070b40d14419500e00550640121f6525850100066803d4180780c00040050318045210304980e15070f9030308510b8469110301c043c0920705641c610301528004100c820744c0068141903020703105040c10320810001e4078691407100e240c00700c500c0b401c201900b5248080c007819966107584402043d860440059140c04031140503a46201c10f0a00808180490f00054803942000c2050113016800108442c00070713503d410030075111070f03039410141459202001d02c00781c0c650a050401061550560150003034a003006280122641c80b4420b104050000f03c6000e0702544109140c1c8081c00c22040a068000141c404142d01d051081e01030300c01651000c1d40c04a83c140e0321a040098160001c0c0b0a03a04214110b02e4a0300807145884811680c1c0c50040c440d004074034402c1e00721468 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 390360269 1250 390359019 390359023
    0x6061213030e09070c030206130519031110020703080f060a03031d09010e060a060315060e37060305070e1e030f030a080105031603240e070501020c0f0607060905 71
    0x42c0c00c840041452070646403200c0044c1c152002d0404c2140180030f05030000380f005003c00144801260000020021042c200d00503400034038059400b50103100d104e850340c00494008011654150401080250301c03812945400b92080d00060140c11203951500e082050b541c48201024040301c0e01454004480c0c2100c1681002c40744445505641207803000001088410340c2c005541e009000603588100d800f03030345400880803070700640d0b211503006292140421040c4d109401c00155a1030080c46c00095840444d0b44151340c100040c4c4041d6410010310040410b556030540000040000b800c0c24441351070080d4000f400980300c504c0f094407505105e101060703800d252000f10a19030501030f00321510280c0980e0015541c0d04004102d0700015420400800c5038200468003000c01030404040505150442c5d17100c24032901403510310900455a0035401108040074001c8800c0a1740c188050040d06092070002418074940d401107038041c102c050100c0040c0c1e120002150403294100900044c54056450302034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 390361519 1250 390360269 390360287
    0x90b0c1020070b0402040e0604030905030f0102090a170f150601030b0d0308061912081306031e1109041d0d05031b030a0b090c04060306080706271511060606121303 72
    0x21f4544592401c100804d600041e0303100030f850040701110350f0300031480641800d0348100d28101c0c0d0009000d25040001c0f040b003c54480744941c0490039141d089022084544c9060b0484090b03105508004040c41b040c0c1d60103211759030340030300165000510342c0e5190314060085400074040a00270590010048112000d1803101005401040d86520022100c0c8c204001241c20a00d52001c2101810320300207945da0003440f60b00e04803118030004522000049110310010400c10012030203040081028600ca9910b80c410034810740b0340110083c4405032080042450f00394005204402d101041081c0482c501d08028130001d258a8280c0b01a9243d17a40321942024044100950303800401850074024500001d41c0a801603c110755000c001551340c0b030800f03984c0c1c0c008501c90784011070085c001c034190401134483c007141c03801030520620300815510070404400c0b41480440c04009403c0b40c0f40c171121b0034000e005980e0000030888440d418079000446da42442d450180c201d8406c42a0900e00c0307020580207200c06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 390362769 1250 390361519 390361541
    0x6221e03020a0b0a0209011d0901060c03050706060608040303140108060a020703050d05180607050307050a08150a06030509100608070b0901022814011e0c090b0c1020070b040204 78
    0x1000301410308541244c042d41000924901090b9100382d01f0102c440d100314080321044000f4603000ea0f036460131005407100c2040b804103404001d010083d0b82c8c0801c09500034040208046e985282c003501d007605001381151107142c1800c00381602e000040144080010b0781a8001100800040c4e840c00c492406907400d2083c0c842d6103482506080c02c001444410404d1800070b403030800c0944e504c030b9844107001c5601b0301c002ca4000300801c0d41840800340b058030a145060303000c2130580c170b02c0c60340c131900b04000f500d070b25015030207940025260002c1201085c01030210b100803505100f410f112540c1852a41e81d11854a070141d840440b0f004505160180c1c0b01b00b1140380c0000e40504400d0b4180b011011b09040509102d03016211502000306010581a05204090b07210701076040c00100c1c129802050005400408203500800805805c00303d42c01030001c00070440444800b00030508040100080c01c00d03601c0c1c0e4210b00d9961400d041e20034403000103003401c42d001c0760781c0580c404581e03550302e01c00034008286100c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 390364019 1250 390362769 390362783
    0xe070b0d0f1b090803040b030a0504021201090b06032104050402030903090d060b090705040b030f07022406030f06060604170a080d1401140d0b0406020c0a030206221e03020a 76
    0x2240d40204800150540040c4840d914201d19507296400c4617030b64450740c883c01c0c840b02d40420001c1c400148a0388141e4201d0310003006c03c050502056002ca080d50100c040a43c1c420f2080801d001c03d502d0200014910303000c40b8650000b11104144007100c541c0103e104050080360004000750030100140100c400d0110b00501e0120b00400c0ca0808074014010303c0c011070700550702d64000c10301c1a8050030540d42258a081d000a20790759901070094540400985103806512402c28407644030720944550040070282d1038010f00480c038100007058508243d5215081040d0820010710040b074540c5000c81c2c058a030300d800340005031055610f4481c0391045103d0042c2c01040049510601038500d5000349620398001c1c10003042a980f0360380741004000103000110b500110718460b110000350200074082e130080c0207040043c180803542130502c3c24414090300440041c0c1240c81044401e030800c4003d0383e00580202150021306015940300300c4035040498000301020001e04180007014030801c5000000c0b03502c03100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 390365269 1250 390364019 390364031
    0x181208071e0b040501060e010e070c0c0e011d130f0b04050f10140a05070905220f0902010906030903091a1b030a031a0607060b1305090717010e070b0d0f 67
    0x14400c0407030b0401e82d02221103500388040046c2c084040c00090741650010031148520780c07038100f416a1101d60191b000c64651420640004103029110886402002140b29003100b50761002024640307100020140340c51002d80b0b01225012503038083c40d10b401d5a41c01110200d0a4850382091890300c85400707090b0005105090300c0c200030440c1381e0009000c071102c01780d500f1035a450f44c00d003890645508035100d80009107421003c001503c0c0c02d11a50001a100601308a140d1102c49039101c259603111030b400141ca601c0f0300e041d41c00c55a00011580040410b86000c0110700e041da034000300080c14038480e00446902c090800c03056582e80400b1550300c0f952004003085250791256003a504c0340c200e2801c110100e441e022040c4c003501e10281c081c00304000001c1c141031402e651a07984000070702c5200c0c540d9401ca2000b116080d42a0564840da030f008200580080c6081484c081840c01e69501c5801000c040fa414514150455800001e940e0141da0024502c151600090301d01030740104500c0b030321403210f0b50500c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 390366519 1250 390365269 390365273
    0x20c030f190305090c092a03040c0602060f0708060d0c08010c0801080c01050a0915020a14010f1104080a110f0a03060614011809021c0207030e01181208071e 69
    0x40c1d45541940d92a1001c1c041551403030041c40d1580380445509800021b032000041000407035101900040a5861012082a00d168402000c54104503002c0b82d82c604014014050103404100007a170044072015961154a400c1034000c02c10034018115500501c48414070804001c0700c6104800908071040080040001c02c3c131005081e601d00384110320150040300d0071810380e540b184080761078514254541006103072800185011441071740c084102140108614003001912481128030300d172850600201e64010903402c00801c131043d0304001c03170401c070b000c004c00c02158001003a4450896000010b0004c400e40210203d945c84501003070b101e9200140c241d0210802842e0b9000805035010103514004480050740107440312056114680f03229402c0020810100b20b49800809003032030003840c038089035104440e840081c5d0b080b003402100402c9000d160f07460b031b95031300042421000400141d2024a6480c210303910a9011600e0b8020f0650003000541302e040c824440345030202c480040c055041e052481b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 390367769 1250 390366519 390366547
    0xd110d020d06090b0a0b030d0c0218010b07170712030902210304080c0303030c25120509011e2c10081905060307051309051c1202030103050c04020c030f 67
    0x84085034042c00780400708441c880d51b8440e0040c0414003070000d080324440c1140a46503400481d00490380180d240c08208140300d66040424024140900a95120401d610f440a001002006056420813062003842e02042d000050248030140d2801e00048041c0c1c01d0004c500c10481c03e02011055078004000d41c0420070000001313000f114007072025640d00080d1384080546a00c004e54040f641c20f0010300a9210010071400301b0700407041030300141103602d030305669406600c004050001e80881c8010492010b6540c202d071422442582082200142000d62000030b449511405542c0000c0041da0341c0c241101001256600752511004000c1081d8441880c00107205c40d0b0b044400000c115141c2c142c41210440341c0c040e0b5400b95400401402002d030412060080300030442810400c82c41d118050400410005d20000485071060314501c809588001c1d8041d040c0075229012007002403040004002007080030401002c107003000c4030050f94441130414120b145014424040150640003e100d000f04902 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 390369019 1250 390367769 390367781
    0x7090c17190905030a0e0109031109090709090c05040c050a08070e0303040503160801180b01030807030c0b160207081b0d02042405011b120f030608070303050301050405090601050d110d020d06 84
    0x140d60346c0388045500d81c3c004550440d0a071000401518880c16105041d2400c035041540c00203541085442c1e40b5034a1600101b500c104400640c2c80c00c1307030a4006e20a9003014000d071900c5c104103050841c0f030408130b200001c0098a00078080d4040000750302c0e50040c2903509004944c0240300041c103d036994082c0603001c1c54103048500c6025000d600e8200c1c01c01c200d0f0396500300c1e08615a04014482c0700c1d41e20b10340720148550700009086042000800141e000a41103c0e13069008000d0140d20301d031407842c0608046c0c6008081d13003144545502469020030040c81c43e09840743c0803282510004801021440414045c100395400c1210103d41b02e480b030310210354018107001c1283e900340e9039021100b8031901003e12460405202620400307401368154000c0f40103607024a03034096103203000104182c1d00e1a0440c02c4c0b581c2d0350030407000583c000004026600d40350007882d80046c85040603000a5150000190b01940e04600081851500c0b01600780290b0302d034552014800e401a10040c0c0412180c030b408401401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 390370269 1250 390369019 390369037
    0xf1305090606030a03090b0705031e030f07020303090721081224010c0204021e0406020f12040e040f0305040e0c07150e03030105061303060e01020c07090c1719090503 73
    0x1c01c1e00c0004000e0b140011307401c18015010740394030583c181000d00e856040d90103890b06a44a00c410001c43c440720313020003205040170250000381526418644022115000094400001c5500c1407003400702d40c01021a1110440d40c0b0444c10340d0b11074490814280440c44030130b0010748000340c080b4004000c103140c0031442d4420340a00302640c4071030001358524400e507030811110600141c000341c840b50050400b640206010b04c9901d0701910000000b101000513540550003030700044c0c1240c1000e0202086c20080381c41922408003c1a060030b00b804441c01c000d83c3d00800207000000c00f04195400d1501440440d40604000c40d000341c4d152401c40d003501415070207964100c0f04010711904007903488210740b040c003000007800d00245142d646444208401c03038101c20b0b80c040409000020000010301e0f1440b5090068265074009a00d0b00d4900302038508010190b0f121644c00c0b810462007646c1d056010303c0c0355105441e05039a240043e02c0d00d29541c4c40e8402107114000d400c61806000300d003401000809050451 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 390371519 1250 390370269 390370273
    0x30d0f050412060b03010c0e09160c060f0b0411130605031504020f0c030409090c08150105041a1905010305090703051203041e0510050703020f04150e1801150c02010509010e0f130509 80
    0x20b2103612b00040117400e07030f080100026500303000080011f10143c104480000e814038020600401c240005000c43c0c40f070180d00800d2140016004511038245103c8000030f0125040c000e04502e0103c0c0700103055400f9020403449254000b0318012810201006c0d56032500003403044035165500c40000070010030440070281c4049400080015503410300081c00700c501038070200f0b04002c0d6441e04081c0300113424400072402032154800f040c003415489040780401100d1549158000030b03807500001500711030000d0302040c801e402c08101440410b00002e001e1071081c2440c49a5a80c0f0390311170511441c03880d24480a2002c0c1c1e144150204240480002c2e02200034a031107808100545800c4015002c0b44158a002103a502d001e10040007403107521401c201075416507007082d0003000c800000007038000b007c0d1150901540444001030015000b1141060603c801c1ca040a016000340c58001a08502440340300c2d038104407916110717900e42d840c4c20080000d10f0501070101c0032000c00e41c0902030003030b00301120400c00034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 390372769 1250 390371519 390371521
    0x11070b01080c040c0f0e0a09020721030606051206010513081b040203060102070512070801051609080604020105090f12010204121401050402010c080706021c0b030d0f050412060b03010c0e09 83
    0x20389068440c41382c0484150301c031404031002940064507030005000720503a000315000380c00501d08074180014605c4a105440c05030101400c06615007110505d42034580405146c05414000307503030413001b15424084900c1c0f82088507513450300102e4080c810140c6040c81c8514556001502031000030701d1158007000c07104140c50384010801444224002207820f41c1c0180d0003010100064188049003400300c0115600743d452050b00e42c81c07047d0a40d034059881c4100c003041042d814242c154400002005001000d0142ca007606194000030094041c80700c07101e116030545440c01450790b03105258001010b12003c0250344542d5184012503c102c00303000c041e60f007d51505010040d1800610505100b254161a002420111601d52400e039410000d81103076013036820407815400c659056056048d12900036004074203135810100341402c6c201a182444140103c00520f6070043da0005c0554065030003500ea111003108803800e00201612140d03080a81551a00c104a40d1060f80f2048400304502e00740c50a05007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 390374019 1250 390372769 390372793
    0xe06030c0103050405120a02030c03070b01031406090705060d0b10020d09050604030210050307050d0501030f0213050f06060d09150203060315220309081c021209060711030111070b0108 81
    0x43c0c840440700102903070031400d01080801072000140c204020544116420464204295841c55000c1079082d154005444010070030814a50010030700108884060081400c25842c0165504014025984200401704031480b00c41081d0748560100a801082410500c0e1419006902e440c481c49090340011102031022546050210459085a81c00380c00307554000b203044421030b51508050100c0b41081000c100f084144600c0d0b00405001c0c43c016000f00960309035034410404420300d241d646106250401c4104407031789a400d50340c25400141681c000340c1d40d11040006800034951914000c068000300150380308080110b0f800b840c0b0552050f0101c51290300401800c0d0a0403000321030b0007034951a0001e103004400c10480032407601e89d220342091000d0a40391800c0d64108165206040c4181b04407400a241841e41080390400e4422031b81a110710f04030060020910134400c08001500f03000cac0c100c1e611711701501c0942c0044070b592240c240040d119080c81c0341111a105083c420300199201c1c0c001d21101e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 390375269 1250 390374019 390374021
    0x2406360d14120a050f070804050306071d010c0f03080402061b010510090e060109111903021c0e0a0f08190c0b010806060f0d24060305010e071203140f040e06030c0103 73
    0xf029010940720241800e02c010002e01860707102d090200e9006030140000189034504010243c0620314a4031011201501001e41d548002529000746040022241d9400040b8540c07607406d0101c00c0d0940341c030f40c0c095561400400c00d14403070600405208105e8401140e260030065000900890100c0300c5802113998400552040d04c101c40c402041c10b81000c001001251141c0c0e100d807a80b2114011102d04041501880518000d01d01140741c0c04640c0010341c0344104184100410160301050074200042032940307030101c1ea201d048032001070000406680d103509109018094030b40204140e03500300e6000300c40d600c0c010901c03168404c080301c0d0f050404001241d01e003004039225101c0c0d9406840e15a01c01250010400002d010102c02e45042c218071040001d0400061200c0044141c282c4011450391b2662411500715000c2010b11800f60300149000e02c03002002c0030900700000c7d0580b0f0240000a640c2c0d403185502d104191000c48500c800040001c1c000c1c64a550f4144281c0c8100d0a507000b1000140040d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 390376519 1250 390375269 390375277
    0x60e0a0905030a081009051315060e010618120c080d030b010206040f0f05060c09030d051c020702180115030507180608070c0b2406360d1412 62
    0x2441c58000b88480c2505920590240d640031440e201c03880c0400d640c8604030b0040701d01c05d45d0140d41c5800c4001c000002c0c46414403000c108614180410400c861400c2c50804031f40e2018010f8000f0048c109000380c0e458000101c000004e0141a904410903040500d8070701201e070305910407403841d405120050710700c09009200d08a41002d045c1c01078621035a49544500c12072100b078004540c80103000d0750300360118008001c024441c0d08034012595480c1700000405d442c01c203000011070100b10007040344c004002200d010303000403003502c004c000d81ca81d0300d284000382400543e00c2041280e0101d1000004501e50b484030303601c1c400340d02510b080102e51144041111840c1d820041e440821519134001c00000788105074072540841513241c0380890f40d155a07113107003441328240c030401d01c40e00407401000706d0b85c40c2c408040b14100104990f143c5c50b20800c00c201c80d000c19402a050380d100d155400d2030360810544182d054100460040401c0318500080c58604041e8810019202e464421305513801081d031542022a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 390377769 1250 390376519 390376523
    0x60408070512060714091f02010903030b030307050703110f15090406060f0e100201060b0c01021e07030c060e01021b06090c0f060f091507050d030c09150e03160603060e0a09 76
    0x40840c1c1a05c8201e07002d507a903c50104280c20482c06611030000041808051700005215400070928a00d1800d00800b5601701401a5200790810004d000000b1000070329181102d901014058418100c0c0002502a00038000800d40101c0c3d1442e0a000106048005282c0114210780c100513907900e4100c100d41044084a0842c086181c0c62100d5000e440c0038454003103580c41074070000c00d51688400c3c00c090300d03802100200700c8076034004c51051244884101251200c00000d0085c904250150b02d0051001c0100040074000641c0c5134003d0f07114030f03820340458008031004103e01c5646400340046540c0c8610880d0404024000d50301c889490303141404400d49500c2c00100914141000e540b4101d40e542d01c28210030350320440d4080390700885413140c0041e0400c0d0740175002920b0300c4003080d0400303000d80e490701c2d001c402005004003080c002c00f503040c180c0c01401c1d0f01500e4204001445540403a00e401004030101003515088040092681d51540000341501c0c0706103590210ba8442c000c804058035040400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 390379019 1250 390377769 390377777
    0x621020a0503012d0f1a0901140a020c03160302030d030b22090c1d0a0b13090f0b0907080705061602090402061b1c020a051b0f0604080705120607 64
    0x10095007054a82c40b064103842420209642046141c260b8089107075544821a02c417207661303040005455035070310301c00c44483c0600c102d864210140d000030310800c02c8251280707814901103162842c2620801505100c650090216410341420b400a1060304809120492107841456601000a840b0340122070324114043d110410b0004544241d4610000401a6084143e43c4035400e10104c0d41104281c2d00400d218541107a080c15807102d010103426004001c200218106407884000d45c0b1848120b09090829020001d619540c525000030020300c1980050710f100c685505021903258007040d45400c40b010501103400700c0e13544030b0038042030707001d245965580d90380140505000341c105010803d500910007070004d85804c0050111890301340c0300c0f40c44416240c1c0402a11010040e11401c5011010440c0c0020602c01c2e40595403d0b60325000b0030019840807052900d5a2510344440240c212072000040200740c655895000b002d580b4031892081d18403e0444504030320f0505030100c0d40f20300440b12075507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 390380269 1250 390379019 390379021
    0x60602012c0c150c01140405010b03150703020315090709060810060e13140f0108070f03020303031b041802120f0c0409020705031303050d18060e0108100e010621020a0503 75
    0x704011040464010111a0f841d0400102500c003200703100f138028021840950107014142404c0440c216006146100e0090340004000c6407250070b00d51100d64400c90328603000d1303503a80d10a4148100d41620780500780d0840c51413000d00101a8000d08084241c0307110703580b499030507940ca03009103c1c10402440f61401190b0b4060b403012305030401341d6840074950914100481c0241e5035000c01036034148115601e450a03100000144404103080c0300c0d540080001d03200c01100d1909540000380c0306c1c40043c0407a6580ca58003030030700070200700d0328040e82c00070302019a04540c00740044600c3c2c40a03610041c001c4105c1040301c0f00040201d490001750600500d51032450a0070319041029110095124040030b032070390320003800030800d01c0600074880000f841c071880107405150340000000d0032180c40f40c00b680040500c260403d00070140c0c4102420300300c01c42441c10003180d07220700801c0402c0a0940e005000c10035410b10002c07031115003180d4059200c00d0040b55108894100d04101740882c0a28030041c130004500700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 390381519 1250 390380269 390380293
    0x51b090111010603020603012909060a03050901060302090a0c02060a09080f0a0201020d110c0c091909020a09110a021902090103170d0903091403210309070801060602012c 75
    0x184000d804107041000014415183e0b0001031190704242d0101e81424465038032800010080712140501400c008289804e1469a5000403104c0c080e504a440415a441b400144054400d4020100441c0c02410a032064140b06134024040c10104810310094881d010109a15510358881c015043e90030000031410200c47c94180c100035480b90340171808540d0240010340da8a411032007010765000b404424903030355510420300242403180540049118054060400c00240c41e68501c10034862034080000070356030960301c0014810019038211000d850f18009000a0002e5040001e22018100380c08503510307104480c030900310702c0102e41002904483d980300100b00069080c01c19400320545069181c0c10080c2d0500300700201d40440f1415000036043c5c610400142020f074030a800d0f0901d0a4000d40f0b03514841c04060a0081301c42d152027802c3c0e8000000264101500b031220b20050703d82d20000f801110380d5528001c0c00fa007011074400a50f00d0380ca005090580f040800300d10f032140ea42c0000b03054008114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 390382769 1250 390381519 390381527
    0x1b121806021911060403182408010506070b040605060111120406021903051e0910080a05070c05031b0a0206280504141e061314153f0a051b0901 63
    0x410021f00c0000c03072018012401070703034042c00741b05540c0403640c0369401c614002078001c003500c1041e40210b0061f1f5003004481c01041c00c4031000c5a0140d0044070100380d82e100d81004a0300288502d00000680c02807115040d80c10107120000c01c210f8020394215501c22012010850008141d0280140850001c10400b402481484e542c44120301004603440c2c00e144146000c9961403005c80074840001d0038820401404810f10300c59250480301514040e0400041c5a0381c3e10380d280320310200c20610389011100404d07400c908102040d410f5502501c8280c0301c406a180309401c1c280840b803103628030507401f219030030303440e20030010707a800c0b12002c18545403c212844184200f502216000300454007040a848007a501e6090080941000c601e00e501c4c4980d10305000d0340e290100300c2c0c01311407040700701024000480c200c80080e0392003502600b07001070100184150620103035481c08016420840300ca0010501c02c3c1c4280d41443c82010f0a40c402e000c2a40c51060702044000c1502641018a00a000d610710715442 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 390384019 1250 390382769 390382787
    0x16140624040c1130160308060103060512060405060709060e0904050a1a01030605330d0227060d020108040201050d0f0903030605030d08040b130212031b101b121806021911060403 78
    0x40c10000f40bc0e07034941c400b29200440e6500b00b10000d50086081c407040240c20002a1b9110b0740c203203880783d04641090001000100d040d26843e115801d0701c40402d06110b418800d0103030080d4403866100f41c48800310408100ca00f07007484244c82d00382c90500001c0030a182d900344c2c088100400620449248103121480301305183c00903800b42c0100c000c141c0500140c03980710450101c0300329401444480c50030b0031202c000a100040c1042d0190045c140c0220040c1d03041041141c0259090070040e480e03a8428803194000d0129250039065030b410840c424060541590110007900c40135420380c0c504101000d010344d0424000e41e40280301000c80c41c005010390745080840d5200d0362005058022243d5030340ca41030720f19044445034607a000e0320b078840d820901130304002e04602c07000c5902052041801e81c01702070703640c5945548244180700a05141070300d0071110780e10406082c44450183c04504440d0700b0b01d20001c5d080fa20f0b08107940145405104602401420400305412125000701070540d00da03601200d121034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 390385269 1250 390384019 390384031
    0x6060901170c15090f1503041e06060303050406030f0519020d0e0f01150806040b07050901120c0e09060607020a090b01020316140624040c1130160308 66
    0x28034182c5460a96654194030441440f00c042d05807503031150300030002c00d8441602d20310310400c00400c00124044900050325841034010548010304040c0c06404880507854140040001d481d0070400b000305904140540306880041c0e8040140c48003041c01001258400c1c0d03050b200344903100c613200e01d22980030b40003011070600c0e801e40410690b6802d203440d45050300e07110350300600b80d4546000c0740780b41c54549140700091010030300034580b40c1003a850b201c0082801504040030020f000035049016400791114040035003210360200218000064010000704030158003501c01d0782a000803c0c594a09441613905035038000300031301d082d1031a080000c2c00520000031400c0c191b00084c4200c1d5400c0441e6001d5405140c080c11511902d501001c411604004008050341c500039448003202228415800d90308103904420703100015101c0025005440c0103a020b801c5141d01c0c0f02e5410350a045001d0401c40102d41d10b00101101e020041207603090003180a40004909030203042401400846d00c6520143e800034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 390386519 1250 390385269 390385273
    0x120302091215220f050c0a0305031206190b07020d0f03080114030102040312081807080705030f010504111c0606030812161e09050306270606090117 65
    0xc0301800100311052020000059541c0168001101115071112650780c0000a0303d0a140c03066044200c105629410b448040c0c000005104a14200a01044000c0303401400800124040d41d480c03034615a80c4d4000d04000c0885444000800c01c2c0b4149500244940211011030111550600c461455141c028000617a0700102000d40000415400070004110704d0095540c44860360412160b681010505842d881c0641e02c1000204081281240c001c40c8495061800b00e40c240c0300d400301500d10100304901c0c220103000d2600c001038000800115101150350035008d0750b9140003844051070884408a40c080c201c1030740c0c014065110b14000a000c0500c4801c203400100300072a5071100b408407000f54004a411800c00030f07042c9120040d0075a095800084e4080c0c4582c030714640b43c4024031040d21500c5010130b40c469000c0c80d00d1800c3c021016103000c4e000107402c5403110303d000c180c01042114904205040c14490a01101c1d0031013001c200d0030700c0fa050181c24901540d20341074560034492440c0c00710b04414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 390387769 1250 390386519 390386527
    0xf0903210201020f0c0c011805451e010320120607020307030813020109090209030a020405090c040e0d020a1106120a051503010c02060604020c1c02060a110412120302 73
    0xe904000074100780e180881c001c0c46d10159a40015162540e1114104545000000e04102c40d039540b03285001d0780d291031107200c9901c1c0320880300042546180741e405080000da1450440b22042d01c44d0107240f15921449102c50a0120482e009042450a0001070000305140f40540707070441410f0a0003402813400340944042c803a022089070700b030a005440d40d00050b003000405005040d8000f500d20741100b200800da12145200381d0020309090403c1c0706016001c1c2e000304031000030b594140b01000c2519006802444a49040e070310941d01c03070b070481000c1c81c415407504113066160f410000d055244000c1c0c6030002c080507603103030b2103488001038502c080591100e010416000010b113444c000502920708000701159900700240d00380c02d205242c11405000740e14104004c2c03101640043e07110740142c002c0e1401a034410700908080d0801130300c1c80e900c0c52458200d00065030b51a6002503c60b104809c019402c11140e444000080070307502c0365100d800170b1817140c001c210010030034003100f60001d0b0312107007001454 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 390389019 1250 390387769 390387787
    0x2211f092a18060225121b170601080609030301080607080a27111504030f080403050d17011a09190504051006030f0b0a15050c010906050402010f090321020102 70
    0x1ca100e50818401a017194000c8010b03102080081d05a8411346000b00710028245801c2044810000001038444040e5001410102410341c0c6040003030000021040281800810078555505080c45144040e00c903082c000b440d1f000020099a042e00c5400020302010380340c80c541144c01e80782c0500001542541c83c8041944108004e200943c0e0310404000280da568850512144040040c080e20b4020000510800d401d01c0d0400119002d80782d010280c000c2102c254184540b050089410041c100d11400403001d043c184c00000c0d41590000040f44192213a0b251049405c8100018040001c0081c0c2031140c80654640400c0a0074904a00e6454100c0c1903a00c0e40041c041c1c070750945492020303401c1c00030140201a0b042c09540380300442c01d10180b02e20b1680c034000c82d20819035403092066403800d0340c4020354040c4c0f1503012a0704070141c11009000040f042c1c100b44c8000d0806a034100d004c03460210310641081d0103450148200d98001d0b0701c2d00c40390503100f80a150b41e41c0583d1507090465608000f0b0713110f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 390390269 1250 390389019 390389057
    0x339030212071a0a0507050a050d020c0706022802030c060c0a12110d020c030604080715050c0d1a030c01180807170115140402211f092a 60
    0x58031078040d03420300e480d080f040c40803e092610003501c10307100341e0f0500d01006601500312089030549204c1c1c7c03501948e1460038606080003400744205c0c502d41800368200000e0459030008110f1080c054011030031740190300c182e841404988250900075010382210121104a2801101501100d40ca10301641d00c14441552685030704050740483c880403400c140021094010104120030015002d0300040c40d100801c800002d035074410050009010741e400245150400128000c200e000b800994001e200310f04102120962a420a4103c00c4c909807074003040c4501404200c60003e8a0344014003d800800220f42c011a0505c0c040c0200041064074001c0009102c0d40800c48000100328542d00300c141a403510b4429401d54114403c60342e1807128102041c4a100d50110451910000440c0e00598604102c10100c0c401c1c1c00883d8500a0010702004003c034248074140888854030180c10061070301c070744a90f0000103e0321629464410b052203c034105202c03044e4411a00b02040c11820040d00b002d2030310403104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 390391519 1250 390390269 390390277
    0x6050a0905130c0813022b120507020312030408030f151018060c0b0f150a06031b050412022403160e0105040b03190e190339030212 58
    0x4180d07943e0f0707600a040b0340c0150f0043d0407218052405484007050340004044149000725418030050a4004070440815140c0d40e111280d48120002000b05080da0b001e450360700a400141e00030b0242d116072256164580017101e214503031154101d42941c8445140862a038001070031f009140c51421214400740c3e44d45404280342d42d18517601d02c284284007820501c074942a0b68491701c203010312060b00c0e00014200d8505164400441c00000900d6629030242c110852140c1d6001a00141c0a04d03000c51055407541200351a8040c0c0d500030141c001c03480500312194801c621a1308101110607200c14010b1a00001412000c01042807000d161020f840c600022903000f900c01c2007528001e014050660b80d041212205145400d085c03042c02e0502e0300300c14401d04e200082013508201c50046080101c0f1043da803202d58941010801c071542c4a00041c400544503002c20802d401040c0101c0107074001c00c5900340b81f6040350313880c0c0008000317688aa11812003140f070040c6c401c07020740c0605802010400e420030054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 390392769 1250 390391519 390391549
    0x40e0f06010903060e010b011205060d02190e0708090609060106050409090201020f010c08040c0e040803070e120601031b050909030a140f030a09061409070608060d05120a030501061806050a0905 85
    0x24600d1147c00090580b200d00d07500000300e1800c4c0410802036a80d40b540b901c11041c0c0548a10700703440c0a007010045800c20076002000d81d00c41c44428070142640c84400030b80324140880c110381c1d041d19021061640d0309024802c1ca0002401000240511030540c0c020030352851060040310350141101c9901c0742941c10500350b40000071880010030044c0811044100020207124240d207009003007130b0b10b5600c040c0c8001046041484a001c0410300b09458685104070201030309425190300356100c1c68850790030005e0b50070742ca60310400b4003804030f5a072410071040c0d80211844070041d4500070142c2000e580043c50158101c0200c0010f00a0b1008808030600451041d00c00c0b140c0010001c01524001c0200c41d4407000030903140145004100c03106000207000d07029107415041c80e00b61075941170006603285e403194200030143c1c01a8108030b480360245102a000c034904584041c84aaa00d88000301c540c3d40441f0a00c00c05050440c0f01049810701800c0200405519032803c40b28842d00c40001c907035001190511303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 390394019 1250 390392769 390392771
    0x3050a02101a0f0a0312050315060a0305061009080312040c05090c040f0605030609060f0a05030a1b080316080a121a0301200a050c16030b090c06040e0f06010903060e01 74
    0x101024500066000c0364098203d4130f01000504686961341100507414a00040c0306001001c00c10764101c03180d000204901c01003090382c1c1c80250000050241c001580e081c1d0040004200280e040d50060140c1026188030030010340c2401c6c1c00c0320740c040ba00400600140c611400300d110116540c2c489022062150368072183c00f90743c0e00e14042007015405556071109041080510900805641d20011990400400c84803107000c008202c0021701c84140c80d034015541441015051010080d001c040140c54002da0520b5050080e50707590000c1c1c6a100b010903034004200560b580c840020381c4140900fa2600182c5400640700b2101c07010703402201e504290024110a203605008840e240034024100400c4024480c0d85c2d400b845411340e044103008168000c800e1000108a00911a800308050080c144c4041d001c070b013903030380d50b800c1c200c0e400c00f0166a00c1c18140904403a2100d1800d202c1c084804490900c068491217549880002c0341e0128045d07c07540c1000f0301440c001000c00c0d410b00611010b8049440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 390395269 1250 390394019 390394061
    0x30f0f130e01121b26010b060d0f050c0705060601110a0b0106030501210809011d2106091501030f03050702030105010e060f0f060307030915050702061803070f03050a0210 75
    0x3010044c1820f200c05210f410b20609009100680d03555615444a2100180c02c5090101c4480064003410903d242c2a81101c00418055505401c1c4e410091100074040000c120302d480f00c02514105100e4007001805a030710920100c6c0c929440340c04803029611078941521801070b01a076900284090a03408540003c0e210001070003642c800390141c1c21a10140700b00280ca02c1003955030781c5214007440442074144460b03d0000300701c00304802ca699031240002440300240c104445002c4c0c40480c500308c1705400c14803843c0300080041c0c10004140900151002e40860903078616911801e140b52000401c0f403c000d02446001c00507202405218080c00c030720458401586002802e1004044602c5011446031f03404007a404030300d8540100f10fa800c0307081881d02050031506801c00c104407006489003950324901d09401c0050065010a8640c09140000d4000f00c10051b10140982e503402040c01c060080c071034609075000040d0184008002d00d500fa8010b41d00124106c99003002216420002d91040103541c0d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 390396519 1250 390395269 390395273
    0x7080a0806120a1a07020705042c03070c0302041508010e070e0601020c0a0e070302041d01080d0915230c0106030506090f0d030b06070c030f060e030f0f130e0112 71
    0x1a4881000480d240c00a0100c4552900c48507491050503242c0606580f22401017070115100b8004000070b844041d006010618400e880320503515a0300c180b950a0880e0008000c404101c08012160710907001010811044d007160204001801004240d001c298a08480010b4000f020b005d5007424901c0c880103407424030304d4050120000400184185d0440d00100c02844269854480c41000e4031001c243c10321480e03803091000e030002d1040f07402092101d4010381a244001d55424a564142c40106040da8101b25103887c3c15940141d45006814841191203140103c0030712a840030310f00401d040b195041c0d200043d5000407600d0740310b02d409000507511900c003403040c08010032034540c0182410300244030090380181c059440781a20310390b03d0201a1a0800c0b07003007031354903403040d46d081d15044200ca00507207960742b401100a802892048400354185030010f0a03080c00071090300d0280082c144040c0ca8030420782906070455020701040c1c000348000d40303408640c440c040200e0034042c2036003982c9007041e0311141c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 390397769 1250 390396519 390396529
    0x18180f0b0402030c03010c02030706020904091a010303021c0e0103150e090a06062c04050f060705030106030c182106020301080d02190f080702041e051e0f011a07080a0806 75
    0x2550074061ba05207446070740d0003940001100c4000d504078000586400f01d0b580001c000d4028894068080c4044007200000101c8581e1024101e138070940171035050b5000c003076050b54034003004510321b80442d5545501ea1800d50090f0408038840f80328a00480d440754a80022070840a001d031864951a07001200800c10402940b007150058182c010740074010183d5960450301d0f00007a141030030308044004010a00308102048090040c00c0c20005540c000c7c54111300c000c016800920444000a080481991489000e0b0384800810b000c500034800b04079040140d141da208228072135041498218040c81008144a8405507002e809100041c18002d101e0794002450300100c0080b140c44643c5005107900001c8100d900e0500031507002400c141c8406090000600a0440303c0c8805d5080c20300c0c0356000d01c044400e501142c031501c1d14a2880c805a00012141d506540007180c040d0800305c60640103105940e00b60108500c3c581c005400b0074505000ea42d1030200d580c000c000e02e80c0214954800f0b03c18280f800c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 390399019 1250 390397769 390397783
    0x60e0c030109020604050d03140a0302030601030c180303080c13080309040b0a0807050906040b030d030c08090a0b13020307120318050d1208090c0d0b0a05090718180f0b040203 77
    0x1003240280300c0b8200326000100c0728890792065510440e0740040761420107004403c00507898601c5000143ca0f40f051150290103940f04a40d0240020300d0444950105400790034110040c0c04004030003c0d0550840d40c05503104803000e41040400101480f000140800030280718000e45070441c0a075403107022580500c410365624211035441440000010301180d80000303032000458404503140f659503110480840d0050060042e05505030040345494100181c040c0c201508140e21552003040b142e8030000156115000c03120002c144010001c0807620748011401015140e500081c150780c1030383e542c2c80c0940020a01000100c010420300248140107100d204000402080203450100c0807100b00c0d901c414030403080b04004024440361402245059004110490503040013810406241c2044d042c4802280e404035400120b1a0901000582c403200c0802c2100c21500302d0308803600ea081c90f0f107003100c02030142c1c2c9165001c014040c1c41c00b000860321b080c0551000138060318604c2507509042c0181802c1c015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 390400269 1250 390399019 390399043
    0xc05010e07060f12060b070b1509071b1712010e07020102090a0603020706090212010609050a0e0c01080403032304050c0d0c06030f0912030b0907020c0139060e 70
    0x74500c100401c54008411402401e25441c00c2849600001c04000040c60f1640000d90f02c2000852000d00f00860840b03558010740c03452507c003d0b0040030904204004804661140c00140c0b17031031501c4000101030301c50340f40091040345c0100840701c040303141042070382083d01522540d02100c001000705407180d5060b103811844d0351000b07510b40049480070800c0703055144a01c0f410558001115414003c10b1360089070400e80c002d025806d2024200b240d0741c00781c0710a0240d590716070301e010301040c0a42041c0c0700780401d510706800a005004100d40c0156107440e80100250280340e2100368801040e4600b02d09240d040842c000c40c1602403c190070028501480611810b004c4c41407802c0c0c0310003190401043c6000c0b50000d280c040748001800202d20050500140003e0401d0124403000380817076010342004107140d40540305c80d10f01c0d0f90b5188080b43d4800003429981d01154404a00101e035035003201454425040d58440006881c144881800b06024155010b98420342da4100000c405801840381c1c0991403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 390401519 1250 390400269 390400273
    0x31205070506041e0219050f120c221b08061009091d01090f020f0a0303090302040209120d11100212220f1103060106170406090c150c05010e 62
    0x30300c2075803001e03036684002c0c00c05000040215030b568606400900b6440007180e0241c040d0302802d40b10b180945070082c5a01809100f8000c054142d14203050810b040c14001c5100c2d801000c130b00c11010140b0900482402030601001c030070042d030b000c80e00300500910321000200ca01c10000c0494003040106100805000b05100d01d40d003001d851610350344500e000003078480302d00c400203950700301e0b0300d401c00085a8040406071a5003400b09150510850840080480340241d4000341d6a4010300100074440405000040c0480c0c2d0a020138809400c083e07024040380880640400703468010101c0551034a62417421b5140015007418010144000c02d1010329035a84440c0001d609100d035407000c10140031801420302030242e0b0442c90707070100318190b4100c2010701c44c3c10000d00c20580f0040d04001c1d09400404c07800364000d00c1a000002a142d1148824002800d001071200e82e498a03555511400381598010075100001c00d510080707003421000803032155040321a2030f0794090b011070303242c0642510b064480030b10980e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 390402769 1250 390401519 390401527
    0x3160503040e0f090a0b070e1215010909020907031104030c14030f0715050f0f0c03180616080d0b10110f070f060f0912060903030b0306010f0b090f1009031205 70
    0x4000101185d066500142c920782d603580750241142c2d5180c080c61110341c0241c55030560048103801003402e02c1c414001c041c24040c280c0e02d41d00840280c070000540203404c440100009102c282c402d03440b4084c22101124007526007980c0b5103078480248420b82040103044015160b046192804012924000c40c0740e5001c0c02da294540b024021001c0040403031407050010000c3c405140c4091001150042c0c1b0004040d9078813644240740d459925048912019003030314000348e106820b8500102900c1c608807443c0c5c200c100074692036550501c56006406140c600325140c0141c2162a640c00c109855209900c2c3c1d01c031084038122084140ca00003015103d195a0b80140c081880710030b500b01c10a03402c0e600d4606018000e051809006c079000e586960142c0c0703844070b6043d40345003004030741d40064030f50b03a000b6a414801c207040c92041646501d0203124500300030400c1ca80402480c48000d01a0810300c07401800790030b5101c183d00102d10300200c00c084d802e0000300b60440078000c000030512414584551840c4c0310b820 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 390404019 1250 390402769 390402781
    0xb0409050c100c0506040b090d0c2303070c03200402041a0307050408070e0406050a021216020102040504150e24041a0607030903060e0c06090904020303160503040e0f 73
    0x448405807581800782a0300700024045500603119100d64a41c4503003292820b1800b41400802c2100580c1c4004c52805410314400c04c0a10482c02440040d0f042048441003024000740811200385080020b86203001c2400100c0c00300d16401da482000703502600c2c40c100b1060301124020000000e0250707144c415031040c1b10900060609000c40d064222003503607d16504d464080003075559001d203a000090038400e50401040500c02038441502503446800107010b82c0c4c8078000d41d80282d006079480c801c44186004000381d170104250781c1c0504112114000180380545420206081da00100b45010302d806030504100f2140992403259503201000a070034400c022480d10041800c03984010b03409110316122181c0300310130340e0800038040003100014020395481c1510700d000707400d52001d44010f4804518011103181101ca0100b40c4007015400141030520b00703a0403408000482c0d40140080c0d0309031005006481040c00089410001e25020f1402941c55604e40444965221801055440344a691409004c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 390405269 1250 390404019 390404023
    0xe10050306041503050a060b0102010b010c021c08040b04060c0c06110a111c050c0f01020105060d0204020d0e0624040605060f0304020114030a020d050f0112080d0f06180b040905 78
    0x281003803080b2000f02e01051a80f450140c1000603410141650046d00c01c16400c00c00181c0c440c09040f8001c3c0c0082c050340c0031a10040d14613000325280a500113030001c05c1d141c034500c0c5075070019040c18429203880c1c2c1000c2d00c507009140c07540c00036048480424010717000d0106000c2004e111100800c0d091070014841c2c21a898a0b5440b1104418000c102c441c46400d03c8240d641d84003411802456030310544c0c0e081000900f0b0541c3e5914401c80f43c54050000005201240d52044c001d00344145000b501002c000d40702542404003d6210b6000540f003150f55444400c5600c03000e010b0580604d201007007114402c914000c210250f03074081c4072410b2281e860007104010310340351801900d07a10ac1e0010140c1d9104d03555800103803034600300002a004031a40020401c0030400b0a41d018211000c84004108226511030008903440a028050324140716881c47d42c420000365031900610f0a070050341c40c0416114540c403048410340d811500902c01c1003504038104055510702c0d20800440c80c4048500b8440f401300d603182c80f5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 390406519 1250 390405269 390405271
    0x6030108030a080c090319060f0608031c0605090906062d0112020d06060801181802040c020f060910050702030a140a050f1b060105101e1412070e100503 67
    0x1109012003c000100c1d00410b003000d981d40359001070255450740d1907405c0004040d28000c80708803502031902d02d402035468614800e030401d032850300c80111f20380b405100c15940103105000c0001d08194403080c0214040d00c44040050042d0001c1006004a080103001c00195048a550078145480030204000151180070310302d202e902c80c20309060a110740c10382d0b2121302030700c00c0100012540f420154005000ca40c0100320504840c0484001b003a80c00341000c80109464401c50a100c400c108281d050003d460140d000b07a0705106140120b540791004130002904101e421100020f150b0843d901004048209000b8282c3c8001c00c1d1001d50702d01942c001000d0310b03002c0c0006400003c02404180b00803494003550855030b40202001400c2d4540850000d405070700c030013600880c1c0c034601421000158a0800320101c00d0b415007103031120701e070f104444803170302e00a0342c0381e40040030800c0101400c2015480c0ca2800030001400129804043e0746091341c2e001d0103040d0b02d2481503014203602e030701c001081c56000d002d032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 390407769 1250 390406519 390406537
    0xf10030305030a061d180d0905090c0415050a030c140d050702010209060f1305041112040503071403180603010f21050312010603051b0319091209060e0603010803 71
    0x2612a20f51050140040a8a402103481e580d40c0c00480c1c010b140c000c1c040d852040d801e0006090515064640150b2203050140b1114041754003250107110074501100c9850b802119208650f040954548400b048104280e00360804180002010440c00303030305010f0b19615420f10306151300303c601d82c80c08071203191049031840d8011541e518081561140700b901143c0072910b0043c60340b500c481002d582d0701030070b50200c2d6601218145108001038a402c05000f0802c0d0034003850040d60421003000000f00090300024411a002c3c0400c00004001030801e5021803070a081d00702c01591502d039076400600d00c00606090682c41800c007800100024415110310703800b9541c1e88488096600c05c980c04000c2e007500a0071005045010210b00350f0f840440d100d044504032030084e40c3c103010a49414101910b084400f01183d4801d2000b000080c1d030101048082e4410740405440000c0d01341003a03240e00c08900d00018426000507000303502040800c0e842448845549412200d191440d4503003440341d0b60301c3c40b0754905 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 390409019 1250 390407769 390407777
    0x60702060703030e0f03090a09270804030c0e0f250327061b091d071205040b1008060c04050f01052b050a0212010608060a24080f100303 60
    0x40003041510a40150300f00404140858140d1118841171729101c1d0004440c0500480d144240040c003280c107801460312001c03044002607601000c0308840409240f4161040e110814104400800112204403290082c00b0062230105981000c1420b103525000240c20709010b000340d00250018030f000c90841c000b091a8a040000e4000450003060000c900781109001800c80c84040b5030091041c2c5800c444100e01e8480ea15035a0703681c5148098403074600e6402480301400007108011000200360b9a496040905c600300b800c0c021203260903100035103008490803200082d1040602c02c00c0c20501514001401e01340020f042c103131600003942603080c0a54400d45200782c00d02c001c000416409641214000f1840c0708164041c078207070103040c1115181e0740d40300310b400a24040004183c13030124401d89419108481e4448056403034004100c2d10b8140185c1480c1c4e103d5281c8400140b4090001b110380d004504600300c103101903462080281c54044014000224240c1c01401c214032100d4151031401a01d0389810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 390410269 1250 390409019 390409027
    0x9060b010c11040b0f06070f1b08060f0714070309030b0a02161101030e0a050123040521090d0c030b01050109032303090406030302061b18010e0d06020f0a0305010f0506070206 77
    0xc001143c1101c0c5c0b083c015080360000500405000001842100b00e40c0030b29040c0d045409141d500d10908170365441400d40d40d03080310001c103420580b4210300380e8000381149403414040c60a094009001da111540403000304442040c10001c001342c0c01c20340d81d803102c1206411414039542802c032061140d00703c500105004c0702090347c009140c1c0a54800c2802d003600e031088551150300c624006000300b4210307040e8a103410000312600140100154007a2082e03074004081c1c0280c06d10303008800c0c2c201300c01c842c0d102a50341e020300a141a03a26122038040c4ea041c002e007100c09111345181824041444180c02060421080780d5041c40032036000707210100303450035403111940c00441104007113055000364001143e120341044000005c0c035500003403079802040c0250010b080304141e580040c107648203507000146d4817500058904007544c003030000c6101808001d0417010b410301641d41d9a0040781e100305103800e070300003022a030481003e0b8984900c0e8054550800708824503802c4c840050224002d2210092142400003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 390411519 1250 390410269 390410291
    0x30605180709021e210f0f0c0a05070b07090503030a1836180f02010e030d0f030e030705060106021c050c0a08180a03120f0e0a05010c03020a080d09060b010c1104 71
    0xe03c0d0010032000e004a006085d013051a46c48008031000c0e15a0107100b02c840003c02e65403c1140e08848880000b51541e501d0000e559860341e101d03620041094040c812034803000a810b0700c007840209041c800b65a2102800400c20072203c8019080c2c1c0c00000340d90300404031110503408510030340c250391400d6990240074038422041d494082c0240003c0b004411090600706801c2000010064818903c02d0300c803130110308944018160b55070711002100000031326078034900c4d913070034000d9201042500000e002d0300d14140e144d440c0c2c180760960a138172440040c1d201e000907510000e1010002c0320100803910b080340c40c1252007081180e6130b0801c00805042c901c00010149800209141c92003405900a049005200c2d5a0304007289142171440c0d0300c60210302201c104071069881025440302e5080020200202c10f4282001151006003000c0300b10305622401080e40b010030300354805010b80c0d003400b00d000b164410251070040240c4508140c003d0501141c1c070010400a4014010348100c00d01c1074034002511035800e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 390412769 1250 390411519 390411547
    0xe070201060e1902070813140f0607020108040b070224061206010e2809030e13090b0411061c0e0d110c010311130605040e01120308010b0c07030605180709021e 70
    0x44203025141c5c7d40c51800598140c4503841c00d080710b0300444810b007110b0f0003c001c0c440107110344c51000b800920000d00080c002504484001d070045081c2c0b04070b031721003109811545100340c40d81c91002110001001002418980a60003004080341c02003d010607514104d50340013440800b0b01800c101c40000094402415140d030410f007180111103505014806c01410b02400301d0110302205030007140710a1162009844a0151100c0c1d1039210751200c0c10307036030741d03444000078810301040342907004000300310011505540300c01d01e400003003030000c0000309000b885407503071325014002c1a40014082840c004490320200403074680908c15003030801090b07a441d002540c5425214038824014210519280030a1455010000c2e00c152000a40e40d0855640ca8507580f05803013409001c02400201e5403001404024025005848250600c030100ea000e80d450759211000c0d59001c440c40400760040500c4a00c00310350800080000309094281140b030143c0178414607000e0f03c5a01280c5480400005084c8508410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 390414019 1250 390412769 390412777
    0x102041a07061506121d070302010e04140f0108280f020f04020a110705030c090c18060318010b040b0120070306110301030213020316120e070e070201060e19020708 72
    0x210803605200b650710b45801802062895170709089062808910007100c45045042c994100e9400d001089410705e550700440742224200075094006880c0d915201d0100041010340f0f000e8203400b00780061940c101040343d8a42400308a502541203a82d0a00d0f80307002c1d0038140500800381e0001911003107032002c0e001250400c10b0900100f40c2082c40040d0369181c1a51100403503c240900d00251248240e6660400d80c0d600c0e10081d40a0f804030110300850fa24201b400b008007a9403d100902e00c4100b8084000104c00390811100c0c0e21b2141314441e0461070280d82807085030381d6044111010004401d144000a0122a0381c0d0084551a40c01010010780310b101045440c1c01164000c41c00d111148032505c680c0e40c290001c2c8422801100301e02414800164540262440381c0301c04810101c0881252004032114030100c03421309441c47d03859040b45000c560510810700580200a104900783c20140c00c02401c4603045d40c0300210b0214281d05100303100e4100184908171700d01081d0096142e4001c0d0401e0030841c03007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 390415269 1250 390414019 390414041
    0x6041412101b1110050916090c0909090f030e04090b011409010503030a0509090403030209181b0403051c090806071106010e0c0d0903050d090b0115020102041a0706 72
    0x840c518030000c200103160005075901d1848281a07000b42058401074403910321403601c104040c0c00000303c248050340b181e0f0190750b205024504403001020641c0c040c051041203a08081052520b907072600d281d042e00440c4010003004040400c010342e02d4141c6482111302900380c4001d007000221103c0d040d50b0360b22500511011b03508481c01c04507659507043d05662800c003000d401c41c000c5000000014540c82c001c0152140c031941070312842c0c500070484003080f00440d001001101850390920a40302545c43d100110850600010414102030412040410101115504029405030300700000e00003d1401700790b12040320340501140306408a1601c0036074001d030311508988640d1080c03078100000c0c1356129078211203840010341920201c0c1d895504e5560000f02c12540a141c0350350030808107903544020790010314114000c0c5840303400c00c8103007030403502a2491300b60113880100c2c1100c0148407101110004030a40c07a840d00003145840e03d4012801403440f001802e44c01116000319007107090105540200404103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 390416519 1250 390415269 390415273
    0xe06130905160c1a1320091b0d11041707090e1b0d0c0315090203100c02070501081e04080a031506020705060a05131d0f0606041412 58
    0x5494024640040804031500000181454855030700c89019a02404903d0780000d003410f208140400b036200d02c034602800001244c1e42c1485110041900c400c102d0f021400c890816444410151040040f01c2c4030160940722440100000c0710740000b00b590031940c40c024685d00c0400d084042a440c104180655442403400a9888140100600e000b2980d003095a80c40c01c000c0100240401429681e0b800d002c0c081d400c0601c01480d90314081c82c11000d00900240305501c109005070310787c2d4400c4292610702d20314544803501c440801c1c2c110b18092001e01c0b001d00709088100209560640300a41e1007180f0700c01d86044c0481040400c1440903a0980c85010511781003280c030180c101440c1250b5154420005000001d1900c900321580b00348420383e03401255069801811442d0506080000f01d620420411003407080070400001030042c5450a50300030000d0319104840481035a0400c10801d10050600121510140030001c02d03940c2d030000c0e10140e0340c200c400419446c11140c007082101d10400c40032074180c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 390417769 1250 390416519 390416557
    0x507020402180907031404080c030702030f0615011107050f010504090507080402041a0d1e05061f0f0b0a030f0608031b010b06180f03010b0a030b0702060f04030e010e06 74
    0x69841e452402030b40d054281c42d0581079a507110801c400302c800c4000a07060f100850008140030810b400301400c00500301800b92813400c401540001d183c011500b49051860300b041c0f08102c4040c8a500048101001c05c0c03c0c42d980c050040c8460a032107290f070740117a81c80742c607224005406d540d1080041d1000341c200b2200420603401e00311000f402031003084408030311460401002c00306d0b1506050007100d031040c024003100c05000c0141d030740c4c500001542c079004a480c0043c00e1040040345003049154021321030f12144207400b183c60040700b01685e8003600101c0a542c00d441d4100038400580c012281c02181c149800604404d0240400000c1e01d00d0740e0005070503100100e042d03907000340000001c0c02c6151071080200011000c42c070601c94107004001e52003440700250610404241042c607000b031a1102c004000081804104001400500d000d41003504c420703c19904104038250100601c0b42c001c54074051400851a0944d802060072100f504d00c01d0412001660000f51920340c0b100369094024a11040b0200d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 390419019 1250 390417769 390417787
    0x72c0c070f0602091e01080411120111090907090321020102070b0c0a020106060305010f0308070204060e07020a0524131113020a0e0a2607050301090b0115020f1c0507020402 76
    0x41c1d041044101c0c0b04145c0c3c0040e42070880890244c5840c1014181c40700181d40e52151910701c4d00ca9000c04140741c010208500d0210120020701c610302403079280e213a82c50748903000c040074419021402040c541c188400e110051020035071b2003400502080a0340001805141e8501c0b00f240a409000e80081800c61440148489902400080c1c80042c05c994004c100c2c0ca980c03584104c041e03510038450f0900c030002c100001c1c004038914800811055002800100b1030faa51400508140c400490b40303100160800c084c413030108401030041c0b418400a080c034131030225113050070720202340c040a03015480514000c01c00380d0800c501010701e2040302d50020211003c407864004254083d40c85840e06800103110606420f41500d000f240708803d40e1011440c040402d11140d41704144c4400d8042a5003c034031422100040c00e55007401641e028a00c03c0110f0507065240649446085240c03065a6045d0742010000340415030780000c101c00c910307440904000c2e500245580580d45803007041c40181d000341c000100160303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 390420269 1250 390419019 390419021
    0x41106040f0501020f0a03091e0503030408010606090b03040c060305070c0b0f0105040e070e370b0f060705100b0d021507050c010906050909040602091f02072c0c070f06 74
    0x200302c810a070207031203017a0ba0064085884120550b002000300314140414402a060910030181c5418000d800524440d12400000e155410030303400000307241e44885003030054580c00f0308100c0080281003070340c0341141881e540300b100215803405144201a500c80c0003441151040b1000803071940c20804c06007286c24511107c41402c0800d00485000d1401e02c00680c903050340010f5400221000500d035444203860311000300010f0707100d441403a001440b8405a0050103450070b91042100f01484200240010301d0200f07101c00001280380d01b91142105000c207070003003038001c942007032100d0440100007184400c840c0021810f2038560f00207900302e03203035881c0c0b181000c4c0000c0003020708070b0095003212a00803a24004480060150080500096050250080c0c0d401c140c40c3c02c50300b1620440300503050880000110b02136000c0b5952003070410b01d503181d841d04115010701441d805441d000b51800203200720340c031144206442400da07811481c0100000100c02c0c0909505684e1241c0d803007040d042000c0320340d080c500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 390421519 1250 390420269 390420299
    0x4050907080f1003031d0a08030f0415090602031b0106081519060b0717040e070509280506090409020409142806020c12300f01030b04110604 62
    0x1003280c4040012441103c000122901140c2e8940c1e500c004ca010b203140c1c1c0400200d0050702813a0441d418110204035000d0610260140c0e55110184031b86036890001d06148102015511005108181c80c0c2400380b95804800c03191001c000150022103801e02180b001e0041c1000d5000400394005d400e1038401c0440840f2030340d030180104503178030400307100202001c3c130480307090340301d00208401c00300304500008103030302c1d00c000c0941d159007102c0c0d0030725584001610741c455003201e000300080c40000e11740456203070040190294944860f000b0500402c3c690001b54403052074090a4480c1c0c40214039100c2503035454102c101c0c03581e40030300188400e40c0c1030703c0c090ba02c0c000142450720090003000000540704565002688901d43d60303003210f075181c01c1c0300d4607441c000750322000b260030450240f01c1d41d804040c072041f0000c0c0b042c1c8400308014000c000000031400f12484080ca1000e2800c4011f0b0b0500022142401d1020f054039040800403229484601c0e010205000c070064480d004000070400140c0445519409 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 390422769 1250 390421519 390421531
    0x1b0d06090e1209190f0f0e100e0703241715071d0325090c08040809061c182102070e061206010e150109030c06050d020405090708 57
    0x92000c80300c81c1c0105500c40465108201ca20700080c020340700b42d4a0180205490011180603101391551a54407006070f07461181c1003012031500d081d01c100410410540307096400881c11128040f00c0b0704107000e25103100320141c005401c05894500748024071440b5644c0f00c441103202a105c0b80c080755120311003103003200a0202090b084c011007880920050307182e45058071400b801c0e07507030301d44c44200700103901111110030356055010b10030660243c110100140300c0281000719920005101c1d450500520241e036907110b00041000044410300000a8510082d80d0101071304031202038541101c010781d007202042049039082054240905c1510745000c099040025500658101c0742c400f03403102e40902c03101c0340c000e0000c006a2006030100b001d08202da0503035801400082c101861110301d03041451030414203030448a4031060340c8080c403540002c0182a1000030100707090041140d0301d5915100074000e16841900103000000400790314200440e030440b40030309002404042e40d0b042840780201001c00403201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 390424019 1250 390422769 390422771
    0x3061902040f0f050a08120f03040602041d09010606030603020619180311030111040311040b2413080d050409050702160e150108151e0a0611061b09091b0d0609 70
    0x80401d5070300010400d69002448481c1c51440c8c040c81d134400e000349910080c03040ea001c580c24040425000b4001c4510b600d6000d5200c1c40d4241801e040d2003076421503500340d20503010f0528003c000c2005031509002d6980d0b0007180d0f44104420b149001041d0390380d92003030810b28103402e0b0031000882000016030030b2904940c8240c008005102403244441d00c80d11650101810b4055914504040c0345072a401c1010850005041d882004514000c00b250203200e0f945440a07032100455161008020b5006a50044c000d0900500400391940c5010300745200b5405070714206038603800040c803494000c10103404402100340c2d4031845c0c3c581d07941c50860700000990700810210500b448403400d43d07128110280c042ca4500694010b00b2aa10080001052032481e9002900700703540701d20a044e50302c0309400b100034000e5440c0c2d2203000803180d4000e404c0240c02030410404507100d801700c180110014050740c0c6a000d0030384030f82646440345810b5510300c01504114400080c0005252061851213410580464001e040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 390425269 1250 390424019 390424039
    0x30c0609050a0b0d060801110d0b0a0b07080304031407080a0810030c0504090606030611030124021b010e0405100807120f080310030602030a0b09090c03061902040f0f05 74
    0x2411260059148119540300d59980424012003200d000100510100340b803002800c541c6d200e09050a6480c0044030107903904020500c050300408500800c00155000c4031284400c500300700038094280100e446c060840340d00440041c00b014056090b03901c501020b09610350f151b10342490403010951098411303500103120107001c104001040180441a2079100314003c00250400303083c0401095681801c1c2d6032070b03803240c4d0000042035035880f5030036500d04080541075807507041203408407081100034481e02c000c0020022000b111940403031044080d8020b810a41c0000b0120b900484015510040300340d0310600e044144080c9e020203003074230350841ea048c2e400d1310034031070f614203840c0f04a6001303c00282113807030840b00000000f0605001191711010ba110b1050046032a51510803ca0300109e54962403107a40b05103048807460714410a42c1d101c00307483d009103000040300010a0304c0704009007600b400c030200d4007081c409010080c5c068901804075050741408842e66090303580c05805481c803a40d805202038030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 390426519 1250 390425269 390425279
    0x1103010504170f0409110c0d0c03120b0406150206180f1c030608070303020f060a060b070210030f0f2004080303012108031f0e10050d0f020409050304030c 68
    0x201039544540c0d08582e10600c814104020710146034030414000c525101c08100c0400d090080340700c0c54014030100310f00715880d2000d81e24004e20304858003207a107040c800700440c005c0020ba4082004140c03910301c0103001c0307010b200500c00b0802409654100b030340c0d807032601c56a00000b01d80c0054404e02c624420700c2842605042421041d40f189140440d8202541021004401c0d03d0004400c008030311805140001c0c0f040d0f41d80c401c2c1c504058642d00210010303001072075070210854003040041d4010040c6e030010000c59150503491a0540b1520600900950000f010420a103000758080043c0003a0440c0030b105408283d40c044000b0b10000f00f07110003c20b6900c820784405007218040c3c40548103403d000714516400c2c40d00d03441e28612003016401c0c1c40784149800c0000202c406000c0c5005040050802d841940440c440b0010001590420340140c2c0040d01002061a107045441d4125003050b40c1c9916840c4050400f44030401031084080e4020381403454900070400000001d0085a005045001c3c0740386d210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 390427769 1250 390426519 390426521
    0x305070b0c0c03121308191202090a061d150702040e0a0f030c0c1802040509090d0921020405090d080f01061d1201111b03030f07030e0f0f0604110301 66
    0x20b810400d802e64401e110346044002c02005054100c3c032480d50903410840789543d295101d600c243d0510080c2e00e007528002c0c8283d5048484103d4405040501f5070078910f0500c0410000107040c8200010002c03c0a4484010b01c403100784200c0644001d400c2c2950400341030582002a408200224011850040180600d007008100c04008561101040390b4800050314110b4059900710826980c0e0b54142400140801039041c400c0c40e481400800941c4903071a040800a0f0032200400b04803c80d00601f50b071707030011544800141c050314050441c20703801c804105502c3c021282032040080d08a858482130203030003400000d40e1440c1d960582d80381206961403103028401400c0070301c00c050200e40d00c0140100748070420003000d070700a2400b400450f80700c807210143c5401d45064440e018186000020861600742111005005a041110040d451424101c2c0d446841240084c148030800d980c0340790122480c001440101303c3c8030031007011038643c02e0780f110070241c1780c0c102600c040b68202c0210207903010034241 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 390429019 1250 390427769 390427777
    0x924020301120209041e0f02010e010206090601231207090b0d0f02010318151b02010905060a09050f03040e151804060b030118051005010602150114060906070305070b0c 74
    0x100c0b90203218591074580c01d0155401020340222018620010852042d03144241301d103002500038982c038841314a15000152100c08142c444034115040101045580d1100062040c11121144c2000500369040da842051030004028035030761101e928900103407494000100c01050302d5130f84404001c091440b0041141401e1641401044c0300c1e00008a0405036001e0b40c041c0c2482480410b4140c8445225a02c0c015920301c052418640c031303540c8030b20401c0700c2854038a41100ca401d440c0000c100b121a140c54641d500d1030b00400f0b100d034160b1120120010000300b400182c00740c049403400c9a03100c580f54031b64610280421645801c0181d04450702002c2480c015a04e540114a808400705a617121629000b020304403403210942c0541d00c461540000750b480d02c0407030758140d000b40007070b04103115030f52000300c26950b06920290840d80814203c02d4951160b2411074112800c0e40c04400d0310000d00c1001c07400f107005105016900c00c070301042e0001856003040082000c1072007204418003660340d051084910b402b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 390430269 1250 390429019 390429029
    0x140a0c110409120f0c020a0b0711030f0c09060a030f0803150a030305121305160302090618010509181e15010f0504020d06080d03020901090608060904240924020301 72
    0x541d62001c01c032594003949084c0e104480302c0c9403846841c6495008103c10340e000e5071111900c52000207e460a0000480e02940c01c8107003140504041c160007882195034131401540c45100c0c1c21510301007901503860026502c021580160412204035890034400e00c0e50b0412140d0790b0000c40b015980300c65600d800ca15140950740e258441509010005d00120a4500000c04024034509180d07642c40118208101030b100740c141c80344201b03a1240c03c52042c8040b6410140005001e00c850400e00d05064200580141c10740e10103a421400705d954a00400c0400c1703030000b40380d200d58045d0542c3c00418a4242515a0b01d04851030100c0300034030f072a00703014561004c0900c40c40600b2044e05c03909004e2403515400400016880c8600820841d860320f03007a07414484c2800325180466070019065170556042400c50004000500f03000425103072140120341c2070000184010180300030404070014445401d01c111580040541c020000c800c0186041a00c40c10040c0728103030301e1038284801c00a036000310300071641030340d0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 390431519 1250 390430269 390430283
    0x60705070203100c05090406030503090307050a0b0d0504020d081201030b06120618030c06010f060e120a0605061305090c01390f0206030a060914040f020907140a0c110409 75
    0x41d41255003040113110500a51042110400c080c0c1841c1c1c2d154090740025500410156658801000400d0b10b40140703648070601416201604020000b900010398603d1221b0503404200380c0e5980c40000e0000a140200030034202c4003281000b614011800e04030706807486440480f05585a0f0010881c0e40d903400341025985500100c0010074800d90101d40043d20520303542100c0c05c00e6010407185003401c2090b00705028841e202e03542082100d50288004005260030340c2c03600e107074500e519211500d86001410140c1031503114000700d03c10382c13180c0503d40b89a00081c00200201d00307000c40a151a11040038045000034032040b120a1601508168810518510884c10b2100c3c800a204017600011070309054440d04078108618001d130700c07007000035849a80d00202c00554141003841d06011110f02c2180318040785514400c010014000b02c409100180d0101ca103070aaa55aa160440b142402030082c1e2001e5000825610301c81c07500100c240301c55500ca43c102c069090b040308248001c448030314202400070703 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 390432769 1250 390431519 390431533
    0x50301060608061e1309110a06030204050d0b041113050414010b0328080c03030106031416050d060b04091536060503030f0d0f090201050301170109061805060705070203 74
    0xf804480114032140b000c0070b0003405d0403c80c595904000c407070800000351040710303a2951014003440c01070304034009054182011400c02d0708040100c0c0b65821b13042d1300180316403000c00106050256024096500700c01c010081d9016084400104010740000c1e5002c84400714403050040908406000c0c050080c03101400030029802850405100d0300b8030140c0085902900d60484004031b0001d8005050503030304c0c200103640e03070751401800604580c200b18050111031030300c00034054410440c400c04805100c0c640360064981c43c1f1654108000d1119501440701c01000003170001c0da65442d50045002c0c0380d200b80c00c41501ca903686020300b051a00b03010352102d58811034031440c00000e01c4240751540600c1d2080001450f03648482c0841d00d15841030300c3d01190110701180118144070365000704e40740421198410b0001c000c00c0c1c2e001a095010600490940c601240e202d1152407401354000721032580c12400a1100395846d040000158498440540311030189800003590305002e00100c8140c82d42c040d00600103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 390434019 1250 390432769 390432799
    0xf0606021006360213030b0106080702070b0c0309042d1104030201110307060c020610080c010e040b0303070c0e01051207061d040b0909012a05070b0403090f08060105030106060806 79
    0x14803010f90742c2c410000881058006450551403000c5c2881c8100341c1c02e44100f1500b14188407402c1c040590010042100e19010070070610307030104580003110404040c00d42c5030400b03110401d00714000c0307848103074001e480c0650120207841a03044140c903071920a071a0305104c961043e0240c0a40c0c500014124804008102c1040194850300300100c6814140c0b003900d0600e00955155000d60b00f03a090290010780c0b001c030038024202d25024014005050b410003e04c201c0e00f103880040d042400d00d00006105079030301c9140000c0c0741c4050080b50301d4503920644c00110203840b04071103500b001c42802514001c1d50500b907140e800280005400055034000c0d02e030700b20140c080840d80c403004010040d11581050f21524802184e0729460607441c0204010303800800e0480000c00059541f0240700b102607070300d904110000c0d03012030b00f02c0200c0e00c0c025000b0381e420589039220304080d2000e40d02981700b110b040030383c50000220300b5804641e55068810450007441055a00c00d012030b41100c1c16506968044400e0b104214 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 390435269 1250 390434019 390434069
    0x61e090c0405150a17010510080405070f0803190305010605030a090f1202011406010e0d0609110a060f08070309171e0a090f050d0b0c0f09040f0606021006 68
    0x5400303001803668600e069140c1c008292030003005400d00d0481e080c04240100302c550030400c0d06103007054a800d1310074150f14004c0020701f90710181c8003040038804110041014008280109800390514222141941d5a26080c090fa41c2d0300450700402c1248911082c1c822542c403d00880b412916996a1241580c07944060039000340b00d4061f08940d00700c0f040c110b10001600021800304110515000012601c184d007030000100703030300180a18100030010343d010182d541c5d515080e03000150000720020b50600c1c8d500e0072440b9804d02c0b40395641c0c050303540703040020301035031241411140d44102c2c1d407140e1070b80d1211003090f000c0e9140d803540103001800c0192210660b80701200504441c6a112440043d0051a400030a0301c940c0800e42e001d00242d041c050a0054569115880c4010201a68000c1c04e1440c203483c0c154a958000d810700301741e203000050506000708410700307689030407400402c01c0240d0385403451140d00078190340c485e2502500a045d540400c20b42d040c414501201c40003d680324914601a079407035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 390436519 1250 390435269 390435271
    0x2809052802041208030105180610050a0c1e0219050d0206250303051b090319140303091e0102090f04020309070b0301030b04020f030d05090415090c030c0305061e09 72
    0x400c1440d0300340400070b0510320203802a07124501946030b00f9a2541080103110f09405290700c2c0ba4142404c1505000458581d510f00300c0080d059880c11549500701568200d45044107420040c010001c00300c00c0c0c1e070540200032142c512144c42111171103654105003010702108100c034400d2030f030300200100d000809810722000600c0c0f0303844003181c9000406c2410070403c510620700368098000940d68010001780902001030800e00c61100d40c04c40d03080c44990340c00240e41d001030b0003c100000a10658410812610b48094001080460292794481c0352008840f90384440a2012800034480040304440b14401842120488140a00152050710001c020310001e980003600c4a0154440c40e000080c5910008018502861103031200051508090040050841414000c24031070380040422002c03041e000421a10329050607a0045400c0c21128241100d00342c181e405076444505104454280982c07650084a0044858a00b0451074403030009100c14a414030105011030305400b94403041c60300c2c20200c0d10f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 390437769 1250 390436519 390436591
    0xc1e070807030b1b0307090302010e041107020d02030c2701060c1e080d0e1f051315090b0705090103151a030903041205030c0c0f090c0711280905 64
    0x5010010301c0c031303104080e280e0080340c0c14000162820014001c5691207208034540f51401c1b5000c0c40034004002c450017140c0702e50040244541c60b880100d50454a00740494000908002c0c502c0c90301c0c44c407040d0004050640c070340211200100d2840040784540c090a003d411054003d05d90450000c038000181c40d603003405441c00d4500e07034000c0c003480084540741d0160800b51803010016107100e1804000d421007070880b0300d101c424082d05203401c0004a80c1c400340131441c285d030020004090044035800ca400103060000014000c042014100850300386c010008283c1d609003070b60b081040308000d2600b880044581e001e090880074484c0e12422086c40c1d200090350304450203109032898542e032400b400d2199400c415044586802c0492090340064080c058428640b0007500c0f00c6000b94112800104440001446110103043c0880d404003801360342008445204009402818645107140b503c1344205812980460b1000d40785101040c01d003507500a450140204005010301d50f2030200a500c004e20a40c03c0f0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 390439019 1250 390437769 390437791
    0xb160f0605010807170d0203161502120103110906030613060b0a0305010c0f0503010503030d2309161205060402100203072f0d11190801020c1e070807030b 68
    0x10440400c0140c42000e00800c541c0f0010a0070914148180c1c11602c035803070002d00180c0040282581054000c01141c00da002110001c0700408c40524211071403040402402007000e01c08074894171129450700f01c0505803401060801c100d44403c0e020000d10440444040b60944c00020110f0f11601d80b40111301240740c810800403800410350000304216290380e6009440c180c0d110b1501840040d00304880000440345860014910742c1071a002c40e03624803030940301200003940c480944640362a004080b5a42900c400b24074070150400c003c200c4c0c1d03106490b84400c504584d04510000340c0c82d005804041c0c0840c0d1107800742c04207507916000c00c043c0c0c0640500345010340c0400c01c017040000c0c000d881c0e040d918281384840d55640c042e8041d06464035813039181c01e45005e030700c604d01584003188201c0d03407036074198004480b24984c030a285217082031500184c0c0d100d42d00540c008030b902d001c0703002c0102e000114940c060900f20045040080c1d8145e40c0c40c0d0a1041c0c01150b042102c051000c01e9024a00c29032000305684 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 390440269 1250 390439019 390439043
    0x1403030408010f0b040b0d0b04080d0e0d021c0c0b0412091a1215031507050f0d0e010b0103020f030c0a0525030905010f050a03050604241d010b16 64
    0x103141400d43e50b4520f02e01e2500d603581c2d204120a850a44110000080c0075079000c81c2d0001d8694500e0701c003007809031028244030008115170030012542c3c1c02001c403482c5010191201c00306030040c00f95940880d4499015000e040b4203101140328807528000300919004003800600b074440e030700c507265110140080502000601480840c4200058403400c45203080d01014996540800303085140300e20024003400380d2040070309039012082e500040ca0050000901ca80d0b41070641ba825400d0341c0e41c0c8505100c1c40721012011a0030300d000c0700f00e54400000c92140350000e100045032040110100e01c107035819119810300500209840080f11405422441442e00b001c0c0c0c0b400c070200c1414004540c0305a8000e014500c0d040040040541c403828070f800908080c01c203001c411407180000780c500c1c003d04a5441c10542c3e924001001c9a4441d00290a1020015600307a10036103503507142ca110301214006c0c1e40703002060840c1070b0304c09249107400c94100c40c501b0300b8281c2403104100700c0c9507003140351080698070000801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 390441519 1250 390440269 390440279
    0x40803070b013303020a111903030b030601210302100908030a0b010f050d09020105190e011b03024902010e150c03091005010b130e090714030304 64
    0xd0114a00501c039065082d0302d0300d0408030810720000c1e80c003214039403402100c02c201e8240310628841c07560307a03080142c0c80d0585c00d40225592500050000300358070561080346004641c6c8902d480a880c000e641c2031103940d50180506643c0c0000384682c0d0903005820b1400507180b55a4a151103201e40f00c0d00c151010090503504140c140d0701002e500340c400f00380000600c04c20380400d1040d0b00c40101c0c01c0c20905107015680c02c010b03200c0d004001803092401e4440088404580c4074200300c0c2c2112000030020f000fa44a00b82005102c810628925404079000300300030611682c00046581c98968035500502d00d155002c035000700c41c2000311010740d0036621304a05e00000c200314003002403201c40010055031035100300321400900b5030781c140d040c0e80550b13004008031344062811641c070300341e00071f071440d002c0c40da00d407140010179142000768100d2850040c42e110001c1003040d800c0009201201000f100c0d542040d80f100e0001100c0c50040d1aa0340c01648810b030100008910b8600803140b110000707043d80d00b4240d5035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 390442769 1250 390441519 390441523
    0x10b06070204090311030408150703092102032203050f030c0303010911040312020109020a0f0e0402040c02150702010902010f091d100f09051b0717090d0c06080901050a020a021905030408 82
    0x6420403805600081c4010041d038645100803a40282d803858180001e09141e20781948400300e032186048040820740b0050307140341c00fc004442840401c0d504014195003c8040f02c031070440c080c0400c455a00510005641c101b00000944042d081e605024602d140d18281c214801840d404a601c12004130074800000400e848917001d140c484003c2d000410381a03140e00c10408007032510b0f04142e0fa450001070f0240302000301040402c3c0d201d60f040d01c0000c0c108034a03560907481e01d401440c13440503000684040082c110740c1904440e44652003038031420701211f1a05016118078007540106104080624055038003a202511015041001c03220071702031032a251491030300c0c0d100342c1d900a08202501c806c10300ca0070072030401c2c0401a940e020b1840505219003076543c1c42d20f00e040c80000700107580d4007041d44181582e8200c3d103507a983e9400a5000341b1180c0d1840c0c041c0c101d20003125400c109510301000107580d80d0850080301e00303140056000d0803003801b0110302c00801408410003039407584000d00010542080c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 390444019 1250 390442769 390442777
    0x1903260f0d15080105090d08073005100e010e040b0402090403120501090c02061501020606060a031823070509010b0706020f0a020724021e010902042408010b0607020409031103 77
    0x80f04002140900d0040704051400340421210b0701000310b5041041760180d80b10220110300c410002c181d00e05103400310100300100031900e0920291034540418000c800307003107801c9201251200300403207406a9844207440e516400845010342441c00040010380149040e50120f83c0c400d00c40c3c102014044d241d2124042281c109810442d1281c1d960300300f2440080c0c04005082e40700e90407074000e070314031031f02040000d48a85000d800c180c0601f00115481035814002e8018030030494440b9601824903815040c02c203a002d8155840e4114113040a100c0c1c06180008143c00058a40103081801d03142d2034808004011340c0603500648a40340d0074800102c0880400c1d000f032802c07903072542c0100385590500300c03214012010880030b50216000c401841080540205000c80010141900340d00d269016011550150262400096100d482c10050380124000441c0c2c4400d02021204681059902c078a0716908851448200c1d50340b20505101010061070182c1000b41d03040d1007031420076108401c1800240c5503800c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 390445269 1250 390444019 390444029
    0xb060402120a0b15090607060b0a1703030103020114270315091e031e09011b030305070e12150402280305010c080c070609020f1903260f0d15 62
    0x146546486126141c200c0c4d0001c1c40300c1c41410003d1a200d0b0640016003e403240c1203000380040e840d04000541d96441c2d41070742c8006c00c1030041e42d01c004510041d41c0358880d40240800c80c0071403014100c558810b174041054410401008203a0508040511010b0802e81c03840045150b1601c80d8503405010900542015030007510002c0080448502c4c480524001d94aa0403452000c1d03441440700810300c1290031610325040203540e030510f903074011850048480d42040b00151401c00b00c50100002015490350240e4401d11242e40c0f1342440c09049010020001c1c024507010f041c2d81d110026215944101c010b0440d0041e100400d400c11021218106c081c21000103081c0001e1000010710410a0050038005e003a030060b601e00d410351440c0350410041e1114000c51001601841d80c0b8204034003103407034240080c0c07044c02009003003411400c3ca200341206180b01c04d000460f4803043c91030700c4d980c1030464082d0010007078604425050811300e0049046019410540c03a48807025114180144280311048020010700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 390446519 1250 390445269 390445271
    0x1050d240e040b01080c0306180a060203011d010819030302160b09030301080d0c120804050a0605191d15130b04060e0c010905060a20030a0306030c060e0604030b060402120a 76
    0x31905083c0080340d21016480f000c06a044040d00100540d004144598800000d501e007003d408120440700c0e113002d90b083e2008004600c0003002144440e149421081000c1c80039001590980c2c9514000e030311425483d654505001c540029000001d0198000d000840424007a51001c0351003615a101c03100029618208507410000050240040602c00c0e40d811204c2c6051504104d01076907150404008541c11420811500001040412a0074442ca032440d64101100703100c6410250f21030302c0e0403030354200c85a1409181090500202010090000008010b000541081c0c180b0403c2a05404c034000d040f2400300c0c816103041000070300c051801e140924040d403000200c800004604900e858800c17082103040c00301e050010003082c0d840e9011a5801c18040ca4000800184520850030100c010384180180c0e000200302c1000450341940908101d034065000150029590401078400001d114800c1d40c22010800090010410501c0560b401440180005141541d200f100c000440300c181c070310700855 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 390447769 1250 390446519 390446521
    0x160215040302100c050a11010c0507030b07021e071e120614132006040f080312010608010b07021915120b0109050d0204180b070201020406090608040201050d240e 71
    0xd0704040080403211080342c00e06404013001034842940d20115040300402517030528401e031505900c145040c000555010341228245500ca20f80741d001503400b00c075460010321890301003031002c1c60002d0310180c60007114006008581d003003000c0c0e0403001800c0d0781c0c012118101c0c1c49002400d07080d82035100d0400c2e8060316001030000192281d09205c01000360102c0265080400c0d80004500380101d0300d14450306505080a0140105022621134042d0354000d45603040c000760700041402010004080c0705a641d003102589070388407601520801402e01450005c80401c0c4640030060400303138451030580d003480106a03400360f80c86100c91036000e80482e0a600260707a404e40c2c004000d015000791240b410007420020101402c02c030118641c10034200010f8400c1d0380f901c4203c540c583e000101c49002940040300e0944914102802034043d522501c603002c00681100e00000d501c40c03103210a1802036505955a901e0700c2c0301c1074010801b820f115440c044000701e880300008105d220141c800e000604522903240d6a03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 390449019 1250 390447769 390447773
    0xb0f1f11030307111009110f0111031206040b03030301032103021b010b0f0a14060f09150c16060504060f09050604090f0f090b041209080118050f0a05060a021602150403 74
    0x10001201d0401140609001b410000601c41d031010914801040d51607030450714596004882030118040008a94080000c40000c0c80080c8103d40c1e00c240340585003802829008400c2c1940c2c0d110034400505800403441c5490013060300d00c5103030b00e4442024900507041802c110816240030034210210501380e0340d50701c09210542040f000b1080304440c00c46006030894504010411170b451080c48c82071141d000081c04100d0341c0d0800003030303e00560300507003100b041d001550541c82d500e5008054200701d40c4070741650701d0a01804529442c043e07608540c0c0b100d0419150000a640c105803407540081400a4403c0204c0e40e625001c01401c0284091032000c2031102c0c12540c503000322662400c107007004904059031103020400380d0340690f42140d88448028100740c40078000b00d982d440305400150083d401d1203c03001e0040f020310110a07507140140c050b203d07400b030107080b45980c0d490001c80003400d030f41054000520005095000c0d00702030080003600502c140d01d81d0b001481040e43c500c0001e854450106083c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 390450269 1250 390449019 390449023
    0xf090418050f0f030313030212030106090e0a060602031204150915060f0b071b080d080a0c1704151d06010303090b1314010507080c010606030b0f1f1103030711 70
    0x1502c030801c0000e400460034400c58280c0fa80f100804950f00501c0d030000c8841051b108011900c070f00702c8080481d544031f503100d1030001c050040d03d03c61400c000d04100081001841988a810211a42c0e0340086d442d040c0368454032002c20000a1041d155003114400141c0b050300640561200e29224074080e060001e152004c0c50300f2664240c00074943c10703815900a0009485e540d045800f510b030490f4490750750002e141349040748012560842501409000403c40c4100d03048180c031800b0b80c002c1d502c1804243d8a03807808446000d00c045604e800070762141d0126022a100c1e000e000c0b039200d1802c0c0045030050310640c8508818003010844981c0e036000b2b40040003030660100b0036001a0802030a25454540c07541842c1320401c01d113010740c0038084180d003c9442039a008bc811116210f41c00250240c6a81c09400103e0007419507214050119007843c02000e480e00e807018103030044420040900301103240390400002610ba100100c0b200380001364150b140c1c1804104051842400c0721307543d801c0011148510301e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 390451519 1250 390450269 390450283
    0x32a050d0c020306011e0f08010507091202100e061e120a0c090603050a060e041a0703020406090315020f0c061f0308032e06050a02060c09060405060f09041805 70
    0x900700180c90440500583c0c0c0802e180d41140d9882c0082544900b0503e8212001d10386c542c041401289106000200b4000640001c0e105890a49869401d5540c50710140f490b0714007000000c1d4000009290605031502480740c40c02c0c0694003074089420502d03020140000140c1c80007124001c000d011411007403002d041d619850b445080e0050600940e281000040d2490700b290152500f41920b444c001019074055910200085c402c100c086d500701d0070f1908000c020802d4183d9820f0100c4440400612400d0080c02210101c8006645040340c0130716681301d940401c000c0a8140b0f1803a9020002e0042501d2001c020703001100e40c3c1d0002d0b090341e04100140300c45502401810002030340f1204020000700d4a03040541c0d506c4080d91034038266888034a00000d03102c84800c26010a40505840003040203a44003028049201480d001c03502d4540b01e42800ca0880c0c00746046180c0d00c11030800041c449410028080c111713840000801c1401e1060360800201030311484003c10b0810b21103070074020180300c0704116103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 390452769 1250 390451519 390451543
    0x609040614010f1a0a020715020a0c030c0602101b0e0102030409091b060201091505060f12061e04120e01050f030a051506090f01030b0a031b06080c0a02060a09032a05 73
    0x450714141507a070005e51175040318860204c0a002c0c230003858180328000c0c40b00e03e078003d522808142003141c0361325000b00080700b280a100d00500c05e00400c401324026610480744940181e03040f04904800801044400f44006c45a8030b0440c00148000602103005000d0b403c2850700c0b07002c5c0c040c0a01c000140342c10b032035101e590042c0b045a04004100f0045007001040107400400014003051076079480b004203c2c03100220000e9900140c0214100c1050034001c10410301454445100b007490050a803045102102c0599010301907030300da031058880c010f00501c5e0004051006041c02820f000010510b041d49400c102c44022080d6141d00c200002e140d0180085800d484003110000d0620076880c0100d10814a0201000e0500d940c3d82082da9250380c0b5010004000e40e484204c03041310083e680e04825543c5007a1191001046100300825980180c04081e96031180c002d9000300184c2d035540001c0000350040100a4040c0110b00f04610309090380c004d64003004100a40c0c20002610640c075009262550528403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 390454019 1250 390452769 390452819
    0x711010207030c030821071e111e120304030207060f030212060f12100906200f0d0902040606030e0c0f03030403020d1109040f110a0e0609040614010f 66
    0x2040c00082c5510580e00c3c1940e400040c615160b003204940800b904514140c101c45001a090803c603034194005070307800f4114404121040e80a2010b9000c1d21051381020719a44950009401c0030380070303010070000180d4409100112015011141d0a03181254002d42d02a80140c000210500c1803e411050b8400d81002500c0d00718904a2049007410440f800641224400e01c0f009145801c66920300007103c85414070b03941914204034210a0761401080c0304441214203d04101200c0054107140b06042c190202ca08500791800d42c0801044000b54030483e0154402581c440c01c1c10302581f500d118010180171107407400a01d210800c5690362a00000c10311092059045103152002503c000c01a5000c41f941500e0303480150f400c6242507000e2514040c01c1d00c1c0c21025840812060021080d181c600340c3d0300408002c904028030005115a00d029401110b01440074500818014100000d81c1035119015100002d40d10b1019a112400315100303034403100500640f01400c0c0426900d5081c0074448c504183c1d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 390455269 1250 390454019 390454033
    0x303021510120204020c0703150603170306030303040f051204030f03030509013c0504050c0108010e060a03230a0506010f060c02030a0b10031a220203060f0601200307110102 76
    0x100d64000b4002c1c6034000340a0341d000302d10400400c008100307172800f85500a001209248920302c1120082942d48000c0d6005060601410313006600c031012a806010081d015518542c0d454590103079400782d50908441501c00c80709641801e110f00c1e030192007d54482c0c00390040c0c0b880c46007001010b441c1c02510491140e498076008003a0907001500000f00d0203125075040350340c1465075004142805080390208019802c0808000421201090101035083c00341c8610079140d0300c0c0d59481c0407c0c00e04491581c0c02c81010705040c404184101500703040b48015180070340210346400100750038000d04030011511031380010018011410b124000f20064140c5240c603042d5003070142c000a958400301100030380b0307080401c001308100c081e101d03201201440d00284c81009850312038962a41410048502e048020120314090807030903400345810590b0790f0018000d01c0c640c1c4520f8004004050b01920841c140500291600401000801031145071310344503000c3c0d03458250506080316044010300800b8110f40241c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 390456519 1250 390455269 390455279
    0x7031410050108070311130509072105060a05030d0c0b011a031602030c03070c06080f06030c13020903160314031207030b01030f090b0613111c020706060303021510 72
    0x39800c208860742440d1482c2d003621100b506800424060300d94070032405000925404081c1c2025828044410940c0c00301c00342d0ba88c0c104202d586290064091460000011021409030304030303003015812940c01000201003540d2080045e190164444d80c090110f0410b01c1a00c0922a0000801d0700600c1016022401c801541c044004148801499034007920a4014071340f10051003042600d0007850b0701d20440340d503070b1010704044000c01e24a204490018800b0000181c0d03000445080720301503000540148008440b21007000880100034114100c00344c2e007442003000300e6504202c56004500400f50600c9020300714108100e020304903c02c03002c0705d6441088491400f03083c030800d607030b0300c070441c0d281c009041c031000c6004034094644200c01c0d00c403140c10444c5480522032420301d014014030048483c01220040013030240140c40c1c0c00f1100e005106020f100701a10356401d50328120b1a6058400010310303007645980e4500031960980c00aa0050b0700c9000e40b0030025100304041030b0821013409038164040d140c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 390457769 1250 390456519 390456541
    0x1e091005060a050c0a02060c060f0603070b0d1a060d0e15040b0f13080708041811030622050c040302090f0f06010e010309050f0f0d080603101d0f06070314 68
    0x4400302003c10800003400d44050800340040800280d0041074142c3e200c5241c40103540e10001950031003420315101d03000c10100c0c90009650421500021400c0d81043c00126200000340182c0380c40e0b040f07041ca00c5074081502e41d500d400a2050808250000a0185c907034001c5611b010516801d80c0d140c02005014440460a080380d0503900010314592203090380e44041142400e1481500020000800840c0c0a810080c661001e4402d4813814810301c5e400c440080035040c01c4e01c6428402c0207c042040003ca0040c2c1000250404169800700c509588080300c00c02080445404448203100c1460114040c0301f1403a202e0030b81d03504000514160145802d0002d41501c00100250032181404280d402c4030324142d009822080840341c0202c15070384068518001a074440400308216400b50040025001015018a03001801020058002d050102c940300025005021940070304294041d60380059980b5102003180c034903001a0000940700a00340050043e0507038001280081c422403201040000b64800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 390459019 1250 390457769 390457777
    0x1803020d090e01030c03111c0606030b0609160f1b0501020403020117090c04020d091209030b0a0213051302040312170a050603030a0c06391103030c090109051e09100506 74
    0x10803540c240c0d800c04000001c1121035120b02000c0c4110107023030001c05100d40e40d801401103d0041d0b20103050369850744204000c51008862500341c820415089155442c481d11120350070403220f08000d00a880c02d41d89410000249400482c0d20780c0d0009414421942d000f0204a9610b146140360307889030030021041520f07000c0c03440f0b190303003d80c0d4085402e010410054100b0200720780c20500303039102d21440c10b800804c8100103010a5540406000204031940418801c40fa040c030f54410340101024100b000f007113204200126a0b10b083c2c0d409210120105010220603681e00115854008035030b40c10110000ea1100002c3c40c1900d16460901004501d031808021203020340701d54944001080380c50702d881d00003080d0541424499420126100440100c44513a0344548581482c1400f41a00c14400480b001681124601c0e8190020700c041200d0303010341c1c405400d5011050404000b440e0700d0340c000c01c01c5c0d8460041205074105e4003d000840d18240a0400f5400191902c0904003140c100340c003180f8a03202e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 390460269 1250 390459019 390459023
    0x10c050405010f031512060f0b03030c0c190803040b0c070803090d120917010b04050a0b0f010c0c0305030d021b0c060405010c0c080d050c15010501140304061803020d090e01030c03 79
    0x83ca0718003124a210720030b18060060102d0880240d4004620700f451f1000302142c3c03007090034035864030041d00c40034039001041d03d441d510b14030010241130000c4401c1c40300100b103050802c041d030a2000f102280104080c0041c01c0500701075543c0c0e989400300c409000703140c000241c0c08070402d40c10420840040d40c40e42e041c8481002d802911102841080341001c81e840091503000070510302824110b03003c1100103400100800504a50074015030301e030301100f41d0868008450301584641a1131802c880e55002d8410810034500809207440c030f02d5071782e855031070030f66001038640c0614590003d000c41c0904669015010340e41241401005007611280c003242041c81980602e505000d916208207003003000040200001d016140c05a072101903051501030915003080c0780381d214901032924003500c2c10b102550b0180c109d82c0c0581d02c910138505000e07074452055001600c15a102600c50703241740b0405031101054000700f0f219600a01241c1189074000b4407801d500e030005180401c3d44001040400c24541d06041500c0e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 390461519 1250 390460269 390460271
    0xf18060c0306010c020a03080a0201110c15040f0b070827071e0b1201030c05060c070509070c0b090c1003020c100218030703110907030e3004090905010c050405010f03 73
    0xb403514001a900b80c075000100a43c0802602c2c404010441901d02803c0e89040c01e030006d101d4607031609000342d441d00503003801050607403044800210950070281010b8000e80038400602101c03415458a90080e4011243c80001c11541c1044c4214090903084144115601d10700c61413140b01c80c040c101d611900507214180c5d01c00c400c0c1095889003056008001e005080603801303da0f8030104034205c56108a402d01c8280d1750103041e01000202410a0f604881d0042001e9018101d5a8204810400d807404060888000c004040084000103100b160311a4007590380f5000415040c500d0310100224103600040010030107006000150141c0000510301c01800551072026031035a40700e00313004540c026500300c80c41d414480c5820000c140250b00e0216031400506544d006030507901c8000580540d00310075400c00f89036005181191226882c40003001c0e51888030300513507002c44211900b507540c0b070300150000d07103080da5501c64100401c0b600344201d0741080d000381405405c0c0362a120000e440ca000540d0300e40241 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 390462769 1250 390461519 390461521
    0x1d070215041502040f210309060c081902031206030318090c190f1e0f0e0f04050c0901081b1c020408010606050417070b0d0f230f18060c03 61
    0x10410002d40d4074410b104500454450350384440740b40e1a12035600c940440c19005200440031081640407854800d130705034849084043c9081c0007191240801c48083d10b050b90148003840540310300340390f03103154148a0b9000f1034032140d008403449407203000544414882d030703c208401d084a542240b0540780503c0101c1c5e04138819540c2c2510744610788104403011244104800203100410780040c421a512100e0f59078245042c56010315500201145131903140c0803075a0710200f115054400c1420426100001c3c08148500c040725011a003038407016581d5020724171011400d84215640400d4441c2e018010141c0201c82c000a004565001d21030040d0492002110307004d80001c0030359580444005112020081288035a0f13800c009203035402600030304400354040ca04200421f000080c1501c260303150b00004a00d40f81c4039407003110007410605013014589841c0c0b246003481c0724844c0c80d00b0030441c05200d4006960f01d8111f255000003a00141800c0a08200d90a40c00c0c031003c3c00158a40d106001c50000e5179a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 390464019 1250 390462769 390462773
    0x6140717150f03010e0304060306030c08011e090f0b040501020a140306061b030c0f0a2a060e040e19050d0c030e0105070201030e1c0801080a02060d020304170c03041d07021504 77
    0x5d00a90b4409901d980310000e40002e034a82d00d58411800c580c050384402e0245030316800898283d41c940b180880b00041d440d1911100c009044c0d0007070035054410004981c41c1c211554441c1b2503c242200e003640c46035404a1300c200526004840b103221102c00824507803840c134040b000070b8000e0242c64820312041c924821704000000041003102d0b03400311140215520140c50b01c1d0159600c981c00e0808507041244207201c94100207140300174243e145c102c885201080c5003841811a964412800402e904c43e072101f00d4070034190018000c03860300d440601902400c04019003172051403d10494090410022001100004640e000b80c8920f06000c1c02d180c07555541d04c8900048002d000c21303101c000700a0090000c0350b8607040801102004060240c4c8510f400790781e0301d03c25582c84003030f0710138041e411507400c004412000301c0b20341c0116442486098000c203016203910f0b030b004441c0c0008804240503407001806108101d04402c651042c5524500001070928164a0003516146440c1004401c1a610700100e41 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 390465269 1250 390464019 390464021
    0x10504080a05010b040c170402131118041103070503011e09020406050702010909050622110a02030c070503061e13060c05040501030b0604050907050f0706140717150f0301 75
    0x51840d1000c84100d48450304002d40240b40c5202014810303842c0038442c14a4a0044c060a6443d8000300240d241554868003030040c9140d10440d41039446035140c01c515003c1500002800203458810b109844641410042c8000c803814070909078039500041c020041c042d544441141c0c1545c054603c0041c03034100350000c050701c00c0405d802088115002103000700c0c01c0c0398001d0140a08038001d0741c408203071564a00642c03041320780580b00650032a00130743c2030703031550100001344800400c8031100028102100804581041e00040c0103c0c0043e040015200d5410b01c08000c8840038102c224050b101d1800c0003074014070b80035194841d410125440303600141000d280032a102c44a160042c005020420400e04000d050b54002c0c043c55010a00c0d02d0b400e512030b42080c8042c2c1e4152000135000c0300ea40e882c0c601003500c042d004030800444114040002c1c0700051580c2c01464000b070441c1569079a40d00300620094009084191101003405002c030401c07500d2842280001d00d0707458251248201e01c01b0340408a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 390466519 1250 390465269 390465277
    0xb09150f03010605071e020907050c0a1b032904110607061109030d0c0809280602060a3213020607110906010212090411070501050f070806030a020d08090105 69
    0x10100c228040000950b054024000309031040c410004491440f800d41ca0a0700d02d0300c41e0110107500005008000b460307030741c000c070020401400c1007800c0300c0d00c2c44510356031446620a9040c5040d1004a80c0b0010010007441543e000b1003d8543c0311001d955210195506ca0080c0380100050040707070041202310226110141114042d80e00314506100300d00c12945001c8895128020541c024441c542c0100c41355441a1039414006500c17010444c40d003542001006411603404038541c420156540800c40d01040c1000c40b20000c0c070b1250058030f00381c60300b49110400c66030113605803003c4d1010089680e410601e5480c40024040c4500d00b02ca4060329042d80029900c02800c500940150000442d03c0500504009212015504030360468450f6900001240c440f0b48601c03c40c40c0c00e0400b8801000540b407d900701501d40d06400045078101a4552201070030f5480550315060203696034014844240d501c0000c259126600341c000b0614124660302040c0c18000041000c1d20244010513100805e81c8110111 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 390467625 1106 390466519 390466537
    0x80307150f0b090a05070e0a0302030d0f020c030f0c0a0902040302130903020307230f0d0c0305030912070309060314100608070201091203150905010b0915 68
    0x500140a520801c44020340d119620740081c0c2e114503000b548030301051000881c4034141031802505020a030007045000b200786003000e10168400242c80c010b0482d0500d0048500521a401242000000d16040d5410302842520440c2f05400040c10508074100701d0b80031080e02d41d1a08404220310440c800250800c49a0a00002c039541540c8540a40ca0027401600e1820b001e81e41d0390b54001d0045090b601c076080d08a894900b0224003044081d0070700b107180b0000d15646690000c0035001c41e200e200c1c02420450b00000150f004c0c80180004421035000c1c10006444048528002e443c1080c1802080c0010340381241a420f4806100c81e494054035400d5180c25042c0d062030003c840000c00100701e030042d9921002c403031380000c075905800c1e0308a5045550000305202c40016900c0950840d40c000e01030310341001c006000807490381d402c43d604044110342e928503010001041207030760b001daa014 = true := by decide +kernel

theorem cover : BRFrame.Cov 390287769 390467625 := by
  have h0 := BRFrame.cov_init 390287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 390287769 ≤ n) (h2 : n < 390467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
