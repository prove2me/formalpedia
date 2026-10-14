-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:58.078974+00:00
-- url     : https://prove2.me/submissions/1e98a540-609b-4551-b700-44f8d8e1b2fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 362949640 ≤ n < 363129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 362950890 1250 362949640 362949667
    0xf14040521280e0a0803030a0f091a0a0b1c120201060803041a07060c080a050105090c2706040e011d10060c03021005090d09050607021c0309030b0c04230303 69
    0x1c005218200311020710b00007515900c40c0340660003171012100441c1ca81c18041c503100100d441c0620b11800301460502c840d00000c2c4011440181d2610048410901e9580e420380d0401502092840a40c030000c029142000040d1405076211554014032410407401c4041e20103901b295218098424164001d100800041606502c042d04004844000300e0603d86a583d0300c00035244014904800f00c0c28050400602c15458030500b401400c080300c18070103d00b007211495080e4820343d21901c1c1d40410150307141520000b0102003404800014000c0d079a100c3d61100014107a40b0280240c901c14500044551078000690842c180030b011130980f40b680403490031200b0b56092000d128100c0c107602611a5201c61400184100c6214250143c050100c13403690800090801c0300302c0d0401ca02c500c506210800160300c81030840b52025007888072000303181c0031303078103082d03030380401305d90004103048005010004c00c0c08a66002d07004031510b004600346411880c907101d03c0600765140741e5035095401844504042060b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 362952140 1250 362950890 362950957
    0x102030f010e0c07051606020c010c03090519120f03080a111204061d010b1c0b010e130b1005100c050a060b220203040506011a09040f14040521 63
    0x3070030381c4030f882d0131950b0799240d04001c0007003001c0c01c1088029004008080d01441004200d60003460010300e0b0610756a002341401c4900c0c0030300c60003130000d8015400300484000094020b020451450750300411989000c00d0f2506400364107e0000362103401003655807001c2e008051040740705c2d020301d6041ca02e40d42c1c4412003040c0d00410a171140ca0b1524069160100754001a2184014120010402c48594030070b001050030707003a840c01000c0386500c450102081106d80204d05460b10038030040d41681380c0c0504411803c001c09806030803410f1000038132003c94052601001210300079501c0381c07441c500078003003607400c0b0341c02c000c000d070175504041c00b0032002801a502c60280103000618141181c0144615044030042004665034190b0340081440300303001e0200720160044c900006240c94080302441404098050f46810038041e0781c480e000c65040c035440b80c1041100c1111000401d03118035042c14a1a5140030703900840c100c15991210060300203400000b1681d0003482a80c1a1756102e114034201c408445 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 362953390 1250 362952140 362952151
    0x15030b040f0f120f1404051309020d02060d090b01090203071b0c0b0a02062532070807022412060303040b0c060108010605010e0108010b2118010e0102030f010e 70
    0x1048180d900c0c00181100303e1410f0150b12680d402d494140d4030100604043e02c00f210419050300180010840760341c584c0411207154821a4010424541a1000c248080d100d448001e601800100720b860224500e83c2c00100300030f02131001c004050342e84418090803448240c03605030014460301a0741010442100001d50000d20505910080313035519418466550410518440140c00c460b01344940c0c0b01007559055171794450124038056a0040c4c5001500024400c40e00c8a081a4401e11011214001c1c0c01c585281c100c41406031071740c031400da240420b49640900e804070300c41d0795105888440782c8109880b8526055440d41c40c0b0b85081044031022030080c60082040e641403000300008281740100b1005031512005140050403207504201801c0c1c02d482064000e107040000ca58039810850385e04c00803c038111040003101d66540c544014a0200108030142d200034194142801e225899030f5405080101c40c0180b0020014186a0b5000b24240c0c40190f4400c7e0b0112031020050014110044000c0d8001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 362954640 1250 362953390 362953403
    0x2702010305100902041706090d0c120e060417060f040201050d0b0d080f0903150c0a050d0b1908070603020301081e0a14060103120302120a0f0b1207060315030b040f 72
    0x1541e4100c01c3c4143d03030180d004540500ca0942c441b03c5244801c01402e5085000300000d048507226070100101a201c403020050000c01c1c429210270030182c01084d0000b0300020141406581d907403195030b00ca501e035890200321652441418001100c43c2c4075681214042e550581da624a0b0107411902800a41a0100802d0380403c0e8205030358002031001001f054403501d845241502d0b18007200405040121030300503030141115002c10410610004c504407898980507042a039110b041c100240d50081c1408a2802c0e0000c3c006668000f0703481c003d47d00201140c042078122840716440302c0f0110140d00080c1f003041c8043e0300c4030f0700f041c9544956621a981005c242c004580b6450380545410360240d0000b1804041c81d08040b006000380302d00003801c0d4000c2c100605080d440c003214002d0048908400800803d0519522030422a0741d0310b0f00e81040151400040501100c00b04011205440e0304aa2045c0340c04217103071085907000b43c80c1d1030312101c0440e5000740c2d40302c12503130b40d94546804181441000300c422 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 362955890 1250 362954640 362954671
    0x3080d02090d0c080601120305271201051501050c150727090b0103180b152d01090305151f060302221203050c030c01020c102702010305 60
    0x2515402c0d0700820741802010f0303018a543c0f80003055418090107070400211200d0b0307480100042078111040b00da02409041122000c58940b10014401442482e000c561000003420200c10000d015000380b80144180f21140f65000b04500040d1440d2041980150b600d40040c207030528044c180b200c504d81d101905081040721003e60f1403188041e0b21402c2050781c01c1004115080c00040013a00c100b031012003007070038100005000000044078107404084001c108401d000005034401801d5802074003044000b801c04d03540da4600517420740e041c80f480024003488110000800400790300c520740840803640c02c83e0103001d5152450030803144403400101001c1c0c50321714541190200c2d120701040c1c1c41c0140071070798005846490503a9242c540c42c0624117222100c2d51394003820b015201484084801440e45801e20075034406c0c0182c90b050860003428080351041d4808a205c55110f40e0100c0c3d10200700306000c3c030402c806664803095100300031241d086d01c85100200d5001c0e00055009600ca40d4103d0300d4038204400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 362957140 1250 362955890 362955907
    0x80f0a140708011104090e0d090302121c02010c020105090c09010b22120b15060a030b04090c0807051c03620c180a080f070e01081603080d02 62
    0x82d0b407581c0c8030300a00d50313500181c100851021841825070f4012104040d01d407100c848070006100e44c00c00e00000e445101030320f110041c0b00710b0400460a04490101111040b9134082802074002e000030341184016500f4000001c0314805d0210305071311201d4008190035066401c20b6552000b80d0400304d5606842c140c038804440c1c401315002400001021204030903000b041c41440c0c1100c1884e40500b001b030300500030380c210111580c1c546050b150388076020710340018119440b0f40010045c04030090302a0560114001c0071540c0100440e10300d0a50314142c8010f0118042c6100c40e185401001e10040c0028007401c00420024005001110701c0603454030317401d0b1020307404d41003051800071000c000102c450500c0c120340d21002441042c0c0944440c42e031414020510701803a807808030323220b10004031000d1040108214219600d80401c4000b0b000c40908075864003103406186580d5a01901079028008078940001460b40c4001602e44411000b005041404a10f555a442030030341044032140b681d240c0034001c00d507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 362958390 1250 362957140 362957143
    0xf04020102120409050a18050c040509010212040c05030d050307080103030c1103030a0806010e011b021c140d1803020f0d03050c0115090e0c15031906031b080f0a140708 74
    0x8050070004c54001038600b060b040d0001107e5500485a50b6040d1991081020903804142388844039010f460104860b41c4174120240240b0450b0700e040e82840100c1c013800188030350342c0c0095081d140142c04944000440305030644060104823a40000146400010f00c0000c0c0b00300e402a072818404d00500041e1809000000d0545e00300121500024109030100301e0300e580d00c903010070030140d001c0c00c1199240940440350010a184503030064000c02c0c00c000082c0325400c030440071300c15041c0c121440130f1600d01d203944101d03143c5d290720051500184030f1240b842c4035541410300c00c00403294001d216007a0f104040060008519004905070b041c4001070240c081025001c1c06807505007051401d03500c3d14182000954003c80d100d80e405c0c23603400e0703009042c50313200340d04c6400700400c1c0d5601114010740c03a66204540700c0c3c4003450703440002e4501424280004200705050f0b500607890102072111840254580400951381c980040c10b04809601070403108000c241c842c0650706140c0b08080581d114541c50f513403a01d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 362959640 1250 362958390 362958397
    0x130f0f020c010f060506030928051606030b04060e010e0a110a21050c160c121104050f0f060f0d0b0718080c0102070308090d0f030905030c040902090f0402010212 71
    0x200001c0e5102c55810880f5200d41c130842010f40000c598007400c50500013a900d03a904004c294080c1f04c029262160b074040541440d40c403191646c44411910020703030800070f8008403110f41c4540d00c0400d0600100d18080e16090141000b950b89c203800e00c5005038600388001804400180211b050199101e50f180c1c0300b081807074000c2142e01e03110344440c2010f00424003044214105010415042883c102c20320904240074030844920034003042e098520002a82030801403240c4a40c010101204014801c2d0208000404040036841c422034040106944942c076060703207104111009a02a0b110380d000034172074541411100280712000e450a00e41c881e0300e50720241c840805585080210b250845444107000d14071040c03a000c0c01c019005000e1012081b00041e54804050000519505000c60480700d580c98404e061b10a05802414030b100c07450090801815503182401554000c0c000c2e2070346c10b51281080e0045003078040d40640040b000c1d40d60b02603070066448000d04200d0440c0500d82c000e00c1c04101440c0038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 362960890 1250 362959640 362959657
    0x70807140d0837090803131202150408060106110f060a0c030209040f020c010b0a03050d0c0f0b0a090302010e03040f12060204030b04030305250509040f150909050c04060302130f0f02 80
    0xf100b6010030f2a140a40800f03115403014407242d10400c12807100c14221140300c0304075034500b2038102c0342a030284001052080c40b10088125640040f030005485400004e05a040360065107031540c0283d41104241d44400001014100d15480703d000b0803503421403684186d06842d043d00e4010f0810072050000340607a000040c41c00d00c1c198010850850141c001c1c440c100c113034030086902010003403959490b240c1340c00401000c00c1c240108981c2c41070601c414101c2c0108003a034000c1801d199494010303030040c000c3c1644401a4011342c40c20a030482c03480c10010403034055410445024458528040204411076549801250140d130240700000c00554400707100760003613100361400716051401c0324031a00c81903844944032a42c42d80300351522a6282e0090110350120b401030720003040b904c00c070060841c0500404507620a1030124030744001111100b84d071000100c58401c10a5501244001003000240c2c1d0b01c034000a580420408194000d00129030300408240c6a0554046080113041e6800c0007243c0240b0131 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 362962140 1250 362960890 362960977
    0x180605041505010f0603020a02010b180f07111509010609090c06110706080402120a0507080d020f03040e130f06021c0b040e06072f070807140d08 64
    0x140300c10040c4501807210480340040c810441ca6252100c6031490001300c4c45014141580050030000f014803c1d00700045003074010381030129038001e1800060301140210b03419015581d00b440410074107442005c03150090300c150001040141801000c070f0030603c070080d14035103596684520016180c4154002d050307509000300f0400f5946890030002601c040d46540d844002a0807880c07080c0b01d1550026055074120b90143c2e04090b4002c2160801454a42d40d180040c18511800e100011074a2001900c0040303070800740d0a440240ca041c418056483c0141e0145241c07010072000054980c0c00c030344200100f8507000e841301c520094000d4440d48108c2c0e01c1004103004400384446c08190300e00082c06071018501055400704a00ca03a0f80c0005515180d01401c2c1c0300401155240c00d0b284d0600002060003540415219800560008607404d44d46030304603c1642414000c0400c0000c002c0c03503070040c03548405d101401003059198242d5031102550322032820141080f14091000c802c9e600c420b103002c050006000c1c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 362963390 1250 362962140 362962151
    0x7060305060306150a1401030f0e030a02010b031b0603060114030703060504061203090608090102040b041805070c050304030602130e090f19030905040207020307120507060801141e041806 82
    0x1c0515007064030091240d41800003114151800e82c5a41001c80110781c07030f85414920711412680100c0141144181080c0c07000d09050300c00b1820301d00413009000748010764000b0803080341e5a1701410b031101c03108400312404401444691880341001c500031580100140f510341d5621031000000c0d01c0369041942d103040000c0c3da980c1d061000e03003002d03c580000f601a02c401100b000070a69001408490580500300400c034400010404600094040e40c01074000b050220f03031503039190201e00080c0720720022403160072820301c0c0c0407038609030003482ca2400c000d800002071403a0605545034000a1b5000c41c40840301d1a00083e80000c1003203103044076501803910710024110106d041c290303240c64001007850210104410242c03010000e50012050011504155009a212656400043d0425400d680061518640401034104101001c940c04c0195042030326000c0172a40c8901c0c0122041e0841e00c901070700204074010494412004d2a00e514203140000c00c0030442c100c03801f1130b240801000c20000c40385240c403034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 362964640 1250 362963390 362963401
    0x30e191506080327120a2907030c051201080a03080f01050d02010c0f02180906070e130506040603021201090308010803030603031215060415031404020102060610050c07060305 77
    0x148405005840401440740c64104500c0545910484512405201e980f00c142c0c20f04140100320603038680d0005081d13800f5124104a00d82e19030404540885421681c0a907030b120301900300080c041c0070244015003580e00d90b100b540980040842150b038000303002c2d00340442500343c806035041d02d02070114007014105060840c600074019401c054003180545040070010701494070b03200c0d01c0c01200f42d0240381c40f11703030f412180c203046290454450300070f5017141941d0410311024004034612400351076281c1c200c65942d076403142c08403514030810070a168444448807802c450881540c1095400140042c4002100b030303a039a000900148040c3e00181059440e0725034002811b4200e12002e0052003034401071403440c5032100000c0c0c0c40e84501034031803508a0204000c2102c034030324007811080c40c44000e0001955030b0344580502003a010071040703c0340001d0401e01e80008034810403039058011307641a0000d1400e80c41da0010040d1852400c509001001014000b0401442c8108036010043c0706640f40080c050a06 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 362965890 1250 362964640 362964653
    0x30105060a032012010501240807050d092108150901050307030206210106051201080109030921060207061d0d0909020d0b030f010b0319080316030e19 66
    0x811991280007540001c0001c100c05a21074003034041d01600c4000c0c0650b050303002914642c2160744c0c9075007075885e2000110315400045030402d1602520b4298840c40a000e110840c0d1300442190304800241e03050151210021054100405e0340341700d207090f1111220300c60000503080c08140607510000c1c00c0d5034244080c10318401c0410140070000d030307500826981004082603603290b0301e101c000d014001c0058201d62107000403d500580342c500004034500740d656108010016082aa5250b16000e0148000074000308148254610264562a0300c0f0040d450040113003c012243c090000c0400c440d80345040002d07503584003c01600344654000031350a80340202d5070a01c0b500c280000400d0b40c0c440e1203003030006900840180c04a4800080240c1d0302c200a0302068040c2c0861040c01d9010b108074490740007140e0064101752003d140a42c12a50200441c40c8055452822160080c0607004200041403c102804407241a41d1695090101d42201c031040707820b19000010b486900305282084016041106 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 362967140 1250 362965890 362965901
    0x80c040e090a110301140606090109120803010315020309250f0603090507060f021e281a01050604060815150304260a03090f020901180b0303040b04063006050301 71
    0x200b034008010386c22480d1030303100580401a2441d031060b4000300d06498141c0c8030300183d00103052240c9503407c00c0c00303031031920b811580c0080c00110303568807150605920091061084d03c1c40307031441400900d040f0210728140d18030700340c02c0e0207907030701281006801094140040c9103d400928096900007140707926400c1a90601ea00394018800b0051046000c01c0800d9001a21001c14520031a40400c40f40d8401c002501d45843e491004111030800324007402c1d044a0402d500d0700c0c0034040c010507885512403054046400788240103007507000000703100500500b07119852080c2e220b0340c4c0c00400c507000000d14001172003d1007001c01d202440b1900104110800c100c10760329089101c01d80c1507904d44c0301410030100016001d150513000070596222103030000d015103005e50302c0046070040e24503540c43d6190f020b92480e825240703c44100c4542002c0a0440c00e080000482d400ca88400d029141020f060138000c941c1d24040100c9031100f61022102200090201d5503500444681400002803070362400041c10700303603213 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 362968390 1250 362967140 362967173
    0x906150e030109020901211208040201110604120c0507050405010f06090e150607050a060f1a010e030319120e01060f0603050412030203091e150c19080c040e090a 71
    0x9052003d01801030311080c107807906403100022103480d004041140c4c0070f42010064005802e2900c00e19030152090b070002c0000e400399000381d03120400144109101c60380c450040c0c41c01048180e4145403a9540751107184030208043c40744095400301640c1e4400034050b03030801c4c7c101400c01c00c1c60080c1040901d41001400000349180981c1c02a01d207810781400e1200c1401c5100c0754001c80f4001032080400900340000540e003588902c04101c2000c0100800e00146040d11040a00701c00b08040041c0341c0d03000d01040603050b03c00400640c030b01683d21000408690040410000b8810340781d50310140301e6400c2c003c200e0071460b60700c000a0050f207013680060080300958000000d140c540004d02020600407101864400410b06015070349480302c0746124609440d2403d21545d0740d03580a0b801144400104250000c941603440a0f4242d440c0c01402640611801c445d140c04003001100c940340c80c9008511903603020508480803401c241c0d41d803c1c60001e0040c229402c1e085500001100e0301000980340c49030541c0d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 362969640 1250 362968390 362968393
    0x70224010e0906070c110a0306020a0905041a090402121204030f03120c050a0c0302070f090b090105040c020715021e030a091502120d090f0503030f07020303070905060901090906150e03 81
    0xc0c2000540036056007520017015140d4460f140e00e01d151600c0f1000080019980071500f19a11105400028042203480c01524880d504103c001140d08851588041004800801d0707424039403070350750030420313038010030360100e0818013801c059002c5881102001c1d000450150702c00c203015103510b01d0000c208096014085030240d2030a20004110380c4d11006980c40d00816080a28045400f820141d1800d102c503480014150301c18080406c006095410683c1006030030740d11103180c3d03602c50042000f071350411040700005a12000342082001400200d00d100000b01d80103545541220070101d44252002806101580c2d100140c996a15588022414010300c004280b218a642c0b04510082d1240040500420032003008159503444051b1940030f0058141c1c000c81305040741c80c4602d0129225003007114110070003268040014119800441240c0c411036256403802c070098202001c10100760088076419040020443e404503e01c0e549110b07071170150400603198007400c52240d00080101c1200d00c00d00e40207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 362970890 1250 362969640 362969653
    0x1a0c010b101b0c0b1303110409080f0f0909040b01030b07021c03020f090a080a031701030b040b070e030601091d01140a0902010219030309030801051207030308070224010e09 76
    0xe203a2010298441c40610030000302e5421260a0011000356039400c411072aa00002d001c1e11080c075074034603201c1100d101e000c1a0b211042588100701c222210030802a00e00b0340104652160034140360020403904050038040c900b0070b03070000302060741c0304030454048814000c1071005200b4802d051030107a41c0003c5510051a0602117080300704042518110450203042d000309039450b41a01c5030b0b0580d1064007020707004200c3d459403103c40903a1041c2c80d04040d00850f91021007a400f24210f561028140c1c1e4000a002c1019221350b611300040c800010490030400c600c4412100c0303d5902402505c0c003c0900f041d011510a2041c0550200010749014025150f0724004141a0b0011380040d00303039012181c0200010f00c030019000503800c01084210070300c600503040c10580d08040d01584000c13080ca01a0380c4000e0f45a881c0d100380a201950244c80103d2684004010400a0b209400d21584505e40e40b0507500b501221110a010101d242c83c000441802400010b1114102d41c3c0f24080c0e015040d003005100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 362972140 1250 362970890 362970919
    0x31911010c39060b040b03120307090b130e0a02090910080607050a020a0b060f03070f0e0c07050604120504211505040b0708060a03150b030c27040c1a0c010b 69
    0x10b00700c0c040000b031641c4c0c0c44920403645941c81d98826900540060141c44065400003402c0001d42c0c0102c1d080d5000c03a090140c00f190b10480f000a8641030050000340540c80c50401c501e2001a480090108521980030890b000b416260403c0b00d90080380300c490607404a9040c0710000781420001400d80c41082414071a020049900168082c089500240080c8458131882c0206060207062007000b0b8252140140c0080c0c40e02c10840c409089408210101d030094499040740f8215200c2c07001c0140c01c0d42e0101c4080f0300441c1e58681c0b80c00c43d003141402c1152400741c2e1500030510b946005a207c0c070812501c0340082047c40940310340c075054040410380800c00c51a05584055003c04013800c000700f00134941c1c001075403544440c1d00e400c02450304005032452000c0038141d80c4014100000040d4003d004850710010036040411800520346000c80c00c0542002d0070f582001210100103005071440441d0000004a605228481c4e00c0242000b0124565a01c5401885405d455403c0b4219000d40f40a84200c007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 362973390 1250 362972140 362972237
    0x1030b01052104050a1a0403140406082202040e0c010801090212071211040e0402030c100e010302091f0306050a0e092d120301091508031911010c 64
    0x941c4107100b21400641c032981026403900080c041c004081e00d9203e030030114019000e10300030f40b01b18403d0742d800f15000120344c40b4001c1da000703510580f40801d40c520040356035a41904d000e83c3d01d203600c0035202c4140c440b152300054269032158203e078050380c20003c015002941c0c4180c2c1d450150249900a520f021007900219100a00090a05007000b40c880c0c40d005a9040340d400c42c02c0c002600d003030040d450b5525440100303141d0f10f042c1c030f08034441c5c418602903401a090012020f0640c00407a21840c40b00107510f00154041d5001e580166030003a2020860302e030b521510a03e07d401d00c8810b681c001440f90070070007888030745401608100340f03111698040000011001400c01420000704400402c2a2000d481c0c00d4550752098050f0500d0b4000e2b40c0000d0b00707001e02503003d0340c12604545824041e450300301d0784e003203064881c0340100c205540041020789280c2c8000c1c0c0d00a001740c002c9141c1800c6100846400070f08564201c20341ea40004c00e0840d03110740320032080200d000481c4495400e04d4800381d07504030a2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 362974640 1250 362973390 362973427
    0x90a140a0509210912031b010f05070206070903060b0303120a2c0705040c09050907110c04020405010c1121010c0306150e040b03030f0412050601090501061202070606050607060b01030b0105 83
    0xd85c46200300c0600c59824000600a48246115407180032907400301e5040518060729900b03125040c1ca61a1100150300c40303100080380d50080c09203888141c0c40310705640310300c00a00b00b80841c0381d0301072004002d2005420280032246100d007203404130001c1c0413128402005000400080d20298000340704010541c103840103e41e0808a600031600020010007004003a2001001c0798001c03507108030700000704016030740c0106298201d811000207031004e0a455178108401c03400345014040c0011703221031000c0005204407140c000707204002007412a624403881e50281500c42c0000e04660030380d4462201420b020340502a82d406000e0016806050740c0c03805e013000b031810042401d502d200b9a2100c00d440c10540342841140c44a00c41c17407281c42ea40342d0315a1800e001900c9664011185440344000000d01031003c3e1090b00d043e80d281e41e4a104407842c811260502035048041d003990300e540d85480000340740d0f580384000c0001c107114403804210764061400150846a0400c0d00700d0610408002d0360ba8001d404202c070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 362975890 1250 362974640 362974657
    0x1203040305120315040617060a020c1f02070f0321050115030207030309050d050a1209020f0904030201020c0105130b10060f0c110907051e070b06090a140a050921 71
    0x40342c1e207942d15003400c0d070810b0f13030008241138100c0d14200300495401a01041403010b55280d00c01c50f4119119880030720100d205030010b41503260440c3d0344c54401c100c41c100c201c200c624410310300942842d000f80c68502d0308040780c070000c60101e05682c0003100c0b040d6059050011444510034100010342c5010902c4200071554421901090b600160440405000ea803100700c0803500300e000c449545120f00c0d0701130441d03402030f0090300214084005420212113030f8001c1c0c05100b03501818818031400d502c1c00740651401c0141007101955000c1c84007907465542440395a114101100003050f02010303a0808043c1e00e18054a5000c100780c40c0e010030300ca140e030408001c0800c204540381400450001c2d0508030088132140e6046540221840c0510441c1c0d0340c40b4010305051800c4101400307a01000c800c1c019181e100d00c06000f07241030602c10000e00c2600e00105d07410fa101e66940e401250b0104108040c0c05101811a002072445640380c0c01e0103d107031010072030390032318082d4045810000d514a1390384400d00d000c0c4046 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 362977140 1250 362975890 362975923
    0x2208010b0a0312110a080a1101020f04050120060a090201080c0c07050613180c090f14040f06090e0d180509010e0901180f050118020607020f03010209120c1203040305 73
    0x20540c3c103248244880c140700d00380c4d038081d1031a8141358130f040d41465100105900c0000c2061020b070780c0810040c4200e070306c00301c5c0c0804a40d1429283c10f00540741983c1c082d0880220326000c10310585018000e00c043ca1054086c004001100d00c1e0360310000d0101031000d07100c1c2c882d2440a100c401c400410005041c2c0581c1e03004c498244d10b403040c2822506205040e40c110500c9180a0b0145511000c21a000030045011540b21601e8460302c602110380040111f02c251094940400310788851070809034400d0b803070300501c0e241c0401c40b542c9400c0400c09641c2a00d05201d030540c480c014000655621042d40d04034a607060301c0c0c61030801d1038000010003c00c018014070701442841c0c3d01040d01c244096011003081603800055605100085c10001c0d50000d1b00c47c400c0e2065428070071022040118124140c420950050005050411940900005210004a80b81c0541d42004021095950400320801c260110401000204889014400146940b0440c1e00c0d0581c41800107000240012400d090400324815 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 362978390 1250 362977140 362977163
    0xd080f0705093d020f060105012313030602030106050a030b120703060209030c0d0c0e07050a0f0c060f0614040b060301030317040303200307030509060402010f1d062208010b0a03 78
    0xc100050109001c3e002c20aa862078425401c90303801103111030120503104203849451380da5000540d06078040c80fa034085001c20b40482424042402e4000c1d01001d500c000504600070f031695141c400300e9000381c100a022174004222100f400d941801285884103058949001400d925280243d4070300c0b03103010082c409a004110060107807803c2125200e0200000c4c1a9a1802014103105110740518010700301c8101441e80050039881c010720031500040300e00d64407840e142840100c04c131201d0358001001c40380c0c6510341404800705003050280e18061f00303803852450a155070304001c1104a6140b0450b40340241030601c0100042034000700c1803842c8200803082c80c03849544034039040b0010b09075801c07800c00d43d44124541070441381604000e9440b65840e600c04000984031480761680d50384085070700074005000700c03510030241761141069420034401c43c44402824072200e4000740c030f99085254000c4407860b40b030304002c440c0140b1a039820000d001700720082241109007008500445064000074026850341b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 362979640 1250 362978390 362978449
    0x30c120c041e0c090512030304050a0f0f14031306140706230901020d0e010504170c010f0203040f02190308090d11120a060506060a20010b030d080f070509 68
    0x5007507510011a844604003e108918003020b020003d55000b0240600b0165070301c0794550900000301e0740120b4010307008100e41d0b65a651008a00b29400320100c410180b00c0b042d00300041e1400c40c00a00703601d8018081c0d07460383c8000d503210f0201034540d401002007007400314000280a500e5802c803504c054001c6000308032041402c42c00da00d90441c200040c80308100301c80030003c0392501035010703000c44001c0460070b00001105000c00d6080c1c80041c2c3d0013621512401c840f640000c01043c0003020303a03034000000424001d0b6590742101c1240c0040743d0541e1440300d1005120114901011011130103041c42d41c0a6007100e055480b010102e0250110f4640110014101c01e8288025003600c18502c0300d00070010b000c80034030300742c3c1c0a4840111900c211106820100826814544107080e124580c6103035840c410180f001020400c1035040e2541c00d11a6950b03034400748001d07a1000c1c082c0303160094254031210001e042030450350480200c001c2c900d0041010620213544150764111091013180a022582014aa4076 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 362980890 1250 362979640 362979671
    0x250905131404050c0103110307120f0b0a0b0c100e2a041814010c1b211d0a0303090302060a02150a062105030a110f01020d0b030c120c04 60
    0x1e14203403018403045008202c03c010000940c544d11000a0740d040c0314800b4807102050003800107503032010200b40da0210100c601c01c0990b103c071609402442c0c020034071107903c1c00816548402034000712503505000800958400b420401560702020b1510208503072203548016a40381c0202c0301d00b03d2410f04899401c28032960320303440c3c00107034000d00420400004030320480b04103400b50030542c220f84140c1a00301400030440180700e00110140107445082040029a490100c810007122003250140f9440c020180e220700701d1202c0f00c0112001e0340720200010411050344080480030340346176100c0e005285c0d06200207a0b102090fa03003103030340c1035030219201d220b0b0000aa05240f01100310320084803c0500300710910707555800001c21030b85200364100c68180820f02d00c0358246680310000d0805d034000c00c54461868450400503101c1c0100702e040d526000f461a810609a030f0210791410340581e2a14078005641ca002c8c809022031400440b070740e00b500456525003507100e20380b1224251165a50f05605030300040b6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 362982140 1250 362980890 362980901
    0x3080a0201060b030c0307030c020c010905120a0611070201020709060b120a020c0109081914180607050a0b0117032b0204030206040b03040302010b0d1a0402011e020625090513 77
    0xf0b105120b440c0d141c40013240c24241c1041b509200081c4c101000c2c12001d038004254907000001c10383d51010402d0a220a00001b001d140c201e80e03010b0320508809002098280c402c0d000b581226400b0702e603590b1400d0000903d403840c40d8110b8000e0ba4030701070f8101300202a10045441c0700320704a00941c0316640d410f860340c00a00481e00c085002e542407a02d000100400000100664010856200746030082d00c5000c44506002000c81080f2032000c01c078150301c228508201c1c1c030480348004d010520305041950303814282400b01d20112200c50b0a81d0041c00760103826580f00110400c450000c50509001005c146a103812400d411000001c07054041d40a1001c4c40d01290055038003d0031030303039449544a250f43d0726603001300e070309030015440d10b0508052440c083c100105150307085042c2c403000c840d0000307129100420240080307061210308411002d45030401c402035242e01d0f0168001d002680350582503280c0702c0a60420043c0541846506092110b4108a0300d006695041c0c42e00c10091660781c19501c020314 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 362983390 1250 362982140 362982149
    0x3c06080d08100612112a010507030209060306040e120a05091c051e0705060a081501050304170307090302150304060b010315170304050a03050706020115060816200a140a03020703080a020106 83
    0x111003401c206d03c0ba1040080405003241d81008101540d1051811000ca008084030540d0161003000810140c1c0780c1a00700748100720514054461184a40c0c90a100551203591802c0100300d001c5558101440e100e00d06141769450314009102401c1d8607503036191a11524003500c041e42e0034020700606031003000c210000c0034010242c50586d84400d107000213803a15004940c5540c640054540d985825441202030f80e00644d885441c3c0c810b1048071600c02105900020f14441c01c1000b8800c0000240e81e500b90340d04142107402240a540e42030508221054812500b000c50505040101c61030444100c03180d8081251340e4038080324400f8100d1081a42188500c0e03202d1a407190b100580030007401004507400040760000c0c0c0080000c10400d032030f0340780c202400784591004102d441c1f0008a150340ca84180301480c448034a00b41c0c3d43c04100410000d840c905051000b24240d01925a0074108440341c1064007500c0700301001400991304540d0025510940c3e0700000305417081c0852843e503014001d400410190 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 362984640 1250 362983390 362983417
    0xc0a05270c0903011d0a02010c1407090e1c0503060f01030e151608070c03080601051b03040501020c0402070b0103241a133c06080d0810061211 63
    0x70300303280003220340315004420310500c01d52821207891020448808642100c80c0000050110104d0701d400545070000b203400107075201d0010442d40240070000b80300303181c040d040304500002e200f900c0b442c4141c078003030702c0110700010711401004609005030040b041d0b9070b01210445400c40c1041d00c600040700609036000420041c0c1c421140300b4000d61101080c16807190f60050344611040454642c200e40c802000c1d1078010100399045101070110b4410041d15074410018188507140000d4865143c02ca8031800b98080084d1300b02146c2803003590b9040c080c401d5152000c4038190b00384110f80d20b440c4840f61b8107110017011480000354144981400c03031464849015000c4003000001070703032640160750f615481500b80c0b01e8140d204010f0400c420522402a124080184511014881c00420300440240a9152142101c04419418012141d00800e00502804009054049202174010304884c20143c1200320b41540c541c4240b00c4682e1001b003034000b81c8040d1002107440000c4542020803442074011820b4038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 362985890 1250 362984640 362984719
    0x6130f0504060501141804020409021f0f0e03010207023f010203061305161d0a031104050108010615080402150313021e010e010c061122080c0a05 64
    0x140089a4030144c1201c81c4d804400c54509041c00802c005080c0b020030304001c403100782c0041405420603600c80c05c2944d01c06024480480911250240b81c02c500c08031050016980580082c0d210358094050710362020213a0007541050160350001d100304403100841c0700c2640c00359908540b407488940a2000554645052122910b401700500303010b07500407520503003d2070300f00091b200404500d20415219821a00d0481c11282c0034001c105d07a194180c2802540b641c1080f544240340b69622003500008512030311191442c1c1081d0020702c002e80b44140c0c03150b403031a454104d0400101e100c0c00c8000c4170070b40f0f0b585080d800350303981d0384000b0f008195a130b010712141050110030052249040c009003180c20380200c843c5803008480405064010150f11252800a0344680359807403554080c400c82145584102004160420f4410a845164001c0f11503008e01c11004c5003508030b080d6420308001c015003648806051807190701400b086d036030426440f485024200000c508107003441d28080301d0070101c4030f44804152 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 362987140 1250 362985890 362985893
    0x31a06040303030f02040f08071509051e0d080f040e01120b0c03180d1713050c120a0204020d0516030c020c0d060f24050613090c1b03120e0d0806130f0504 68
    0x5486142b401903004e102c10700d00909c0340c1c450050403003004482009001c070409031a2040c06201c100108c05240b40c00c141980c4582001602c1ca00113003c080000368013185d00d1714a00b8900500080040c0e000c20360340c4482d500c1400204031266440c0c0e80c00806144910384c0c075180c05032480500b4104101110080c0550707900011000e52081c103644440d042510a111191910400300c0e242c5000315000130066840240c07a0305d03a40c102042c031440041c200c0382c140e44040d00d1680119041c0d80c4148a100301d046e980340700304102f000d01014011009942031408000202c0d480034042d60700c041c00c90003107114010040c0e02201b0813416801407070404d81d904109103c0301c00c0649c05c14107140085203000d0240c03203025101068504041d01516000c45150428071700091074200010010044210001c0410005003540030a103811a650006030034840e55400181100050a0400711042c41ca0008000c0d00a104900035103035121100c0c0f900900d0850341085001c0b07010b41c404004011400c800601682444104070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 362988390 1250 362987140 362987143
    0x60d0308131502030412030209011e02010b04110903060f0f01120f0609032001090c0905250f021c020a0b0c0d060e04060e06100308071703010306090201031a06040303030f02040f08 79
    0x14000c44c49a10706d500381b08036020741602a070080445080c002095004042d00d03054007510001602c4a80c1c1c000010100d140d000403405803007010390280342d20200026015a203081c00c1042d25440f400b094124411400d040400d401412030610030755421102d050030102c11b1209002100740705a82c010001c1003200810700e0040d007090094140b2041031a000d209008082d40e060180091060380124400c8010b4102484200200006842c3c0e510034a10310404012000e0801104000402e06440300c01d5071000b485002403030109450218400b0140e813605d5481d881c0c0e00002d090229960200200c80c4035551122052414050b410441000c0c0d0f0401c1000600d03000ca426005000354010b84040c410342c03401c40b060568a040236940c1c2c40125130001c90400102d00320380083d010b440d22546024042000780820064290020b8006895880c0d0b5440a0004c568152007040d00c0030341852143d40c2013a061000080c07035401244009803d040d203d001380310440405038115000351080311909200b1507101c0100340e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 362989640 1250 362988390 362988397
    0x40c0e040f0303060b0307120e0c06070c15030603020a03060f1b0f021501150f02101e0e010501031e030315080c030d170a0c0509030a0b060a0e060d0308131502 70
    0x540c0444c0c90240e010603012941021240310303240c25102e501108078424009001440051040d42c41c0d4028030000072510350780d82c2d00900e411406440c080d00c02509001050b07500100d401000c0003414905213080006850b10485982140d4208a00055400c040d1600502420303511a801c1105140000d0320150f00d90040e81c03510744088285c0c03c8078004d6200c15030303210a95100303029855807114903180414031584182400c131016149407040e0351a00d82c0105018007070755000d1034140c00c014014650f1403a0405079114001c1c64008a400030301c0554950b440c1c0b2941e118400060485450b0b80c2c48080c0141402500300a24041e000701508440341d82c0e44145c1c5484104000c045031003409061084a071080c82140ca0981e11503007440d01c1c0d906502c50f12100d40044c40e0b04514002481000e0180c92141c1e40d013406034070f100c1806030303150060616001c810410201c1c155044009007146100522520b61280240c1042840e4581031400140d216070000707503c2d019988900401c120003020b6090310f60a0a60042d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 362990890 1250 362989640 362989643
    0xd14030c1b010c020712080711120d02010225020d0605060a0509010f0801150f14010309081306230f0309150106030b03071d040213061502030910081e040c0e040f 71
    0x79102170580340c412021450030041c0380540500424060301e40403522031050080d4040c0700a2904c420140e0b116001c504043c100300111000d0303580071401e2220382000502c0070414400c0c0c208402c0c1d00e0000c5900041441d0803400340603141990300c40c00951640c0f55068120060980103040203000c0da56813004014045050040120a50a0044520b011102b01340c00505680304010011000e6003042c500c0032810400300d0080741016111a030000100e8580c40060111036502620420b0417800c180000c1d10914982001070020030803003406000b0b044034081070350000c042c2140c0e03040c0c0d00c1d1a4071541916250107422001201d60070740000103003517505540a1401c5000507810f0311421680c4100c03141107008000b50040034030800800003801440c0c9040800c0e421480403000003101c94a6246070002c01014491b002d0141e400060090280c0c90031400b12400c0b541c0f0361604004a140002e0320300c5091030340d01c51a101e0060100c1c0485d00b040314007c040409012020700310702c0756242c0380c2041403045099100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 362992140 1250 362990890 362990893
    0xc030a141009020d1403120703090201020c010908030f0f040b04180e15040b04050a0c08210f090d05190b0f0f09062d1e07020d14030c1b010c02 63
    0x10441c0004000e40150300209070014120061a034158892440d55110071400445c540420002112050403265010380a0340c080e6500017640c1c00c003840064a00204e91100c64140024040c080100740d80000446250394206c040580d12041c516030890b6940c052a00514000900441d0204000b1605491443c121040d02014031581c0e1a0710b10031911000c4c500c104007042c0c0c0304900000d01003008121060b030060300c21801c860496205865070302c8407200e00d030480d10440c3c1100c07003040343d040c441c40b5450080e6841e420010303213001c456030b0469610b0712800004602601002d0317501014080180844c03240e91824986c02c3c200d9a8082c5412032407694122103500c1ca2810a4020603c840d0310a0b407014819551080141351035190000001e0300e501c0041c40e0707403000900030320b01c501508006001c01c42c0140c03107031046d06840c0a400354201d000444014440002c541c03280c5080c40015900c070705408043c0000a07407482c1c2c2c0351078840400109204059a0b403084040d070b001055401c00055010b402c00b04080d50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 362993390 1250 362992140 362992153
    0x16030c021503071209170f090d080306040f0501150e031e010906061202090a020903030c030f070c0509090c0112020d051603060f12060f090221070f081c020c030a14 72
    0x40c140d0444045c91006031001d4181903100312007141c1d04000b003d074010356600390b130304060402d00050600360720003400312084500032060140c00d003020b0080b0030182d0080442840590b04141c45c0c40d02e01d24281c0c44d05030802c54403003500005c90303d0900c03603420404481c2d85803400b8641404070040c081c040200044078901e1500400240c06803075000400b2820784d0080134040c42e5218024020041d42007051240d506000c10043c400fa884010002408041c40e0f501e04d640c4c640c2620704003d01d035003005a1059000f8424002045140e040100e0f14000c040802d080003604070082c111890000d0281d450352a0108d031412040c0004260108010284a0f040750390070301c44143c58442e8421203004510910b222210071a882c100021025003210707a0310752540c100003038508459000142501c000c0c1d4179164451006060a082c040020707c2620040e04d01c243d20501190b1914900c03580e51103482c0000115000c0d4140e00c40816803091000e41e4541c0c00080448490800a0402d802d003039480d500540301c140b181c503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 362994640 1250 362993390 362993417
    0x19110103050103110108061507150f0204031212021303030c0c06110c0607081213150b0105031303090e09030a12060503070e04050709060e1503011116030c02150307 72
    0x7801841d040e030703a10095801c1c2661883d0019161040050b003469031080303040d4511020007003035501410219016060400c11505180108401c81c0c81c0700030001a000e00400c02440440e1801d10840c0c04c1c80e42e03e01c0c0003901e0f500d500c41c01c14000c0c080c00303041001850607503400006040d4410148400c00d40610350383d14400d5902d11080c1c42c14030400d10456129003240c0e0b2103107141e140c11030190107007a010380040e51609112440305050480c049880d0000120151702407070500910b982404104180c10f5010042c1ea660080046e007c1d02004007500d8031314803102e9000e41010702c10b181800007405800c1d001d4030b290900c00d102c40c0e10781c1c02425010000488a401491505200c0d001e1741040741c074042d0182c0b16803814600c0c1000505d0340107109440324480d006000440030381c2d42c4502c80050201c87c0d004410390a0465038904c3d10100c410003030b807080e17041c10694003020b421a4200d40b1134005500c20341c1c0c079103200b901d4160340310104030324040c4d8011684011030715039007910702c001c40c030030311341503441c07030307000307000f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 362995890 1250 362994640 362994647
    0x906091a06030d08070c020a08031617090603130602070501050106031b09050d08030c16050d0905030624030c032a0904030c03080703090602130302030105070302040b1e0c191101 78
    0xf910102c00240107030012a0301c0700e000303c1ca03042c1014000740c0400741240d00c51803518603503444a90081e03a03034104018418107105211002e0051130051803881443c0100170740c0041c88030b003c050541c00d04540c81e5a004420000243c0c126410315a001e4002d0080303694685c0081d00501d000d411003160b107070102481c0d468207403203403400314192003004011260b64901d60722005102c0d04014503203040c082040056035100e04440000310f82c80c42c4101d000704485c00e403030b40001340850680c0c4c4c01310340039034050700500503658000c10416110340d81c8502148000742e403540029280ca01030f83c1d6800e40502405030040c00c03100e400182e0390502c6444a4102c102c1805c03000600c0b2548204941c003800007070300035000780c0000b8810700c40c0070740186072860003003034060090321242c04980c446581107851385c03004541082181420b014180c0c0c00042ca04086052a1402c1034484d100d1241d40d03408456090108078201002442906503003004264034100da003618101725185500c1100030606940d814000090081d00c3e620 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 362997140 1250 362995890 362995903
    0x10f260f0603010b01020a061d1501081011030a0903091e030506060609132d0203040b01080601060c0201050f072a0b070c0e04030e09091005010b120403050d0906091a0603 75
    0x4041c1d00074402243c7c0f5840d980014019540b4000008002c1100d80c80c071403004101300b201d1400b200d401d02c5515417600400030b142c040380381c544406890401101075686402c003020740307038400310501c0301142001c03852604992030040f03034024403d99581a008240c03404802241081a01c3c4110f00302e0300340b0740718071081144a00903403904950000450051000322000c40c2c0148040b0007210030401500000c9081c4031603000030021603100c41ca17078084204428441c00c440d0540c0144002c1c80500384550600e0001480e42c6200900a4103100c000201c0480c2082e045089802d103540042c5050458402c0844c1e030240d2010340e030748250085600c1c002c0170580108060442d0b400c203600c0440300111502d00102c81c802c0000007013041d0b0600c000c29408804944824072024412207160010b80740d84508050200101d0300180c12140e180034003405502d103a00c1c4a018055002034042c01c01940710f4801488100150810a9005003071754140b5040303408010501020110054145117000c0c190781c0c499007410399540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 362998390 1250 362997140 362997161
    0x1b0803191205151203040504060303080405160b0409150509090307020112060e060f01110105040305030723030a0e120f1305010c17090303091207170303040b0105010f260f060301 78
    0xe010f640390501071500340d241c08000408070741503a09050b61100068126005980706a0214100b142080208001409818004d800d000c100d10009414582c1002040c0118003a0110f100c1d91100ca2840c00c820100b8500c0003820020700c548050720309684242d8503600680f10880c04a525a0700e8240115034038014001541e04001c040e030101d660712710405c143e54115010303040c10302c0101072155103240d0083c01510b101d140240c60304c07a980d0914600c010009090b4244000c0c414200400103903600400c075080b00d4003d034120602040740b03a0a4a8958200180e82c1201e9111000c00942c801030a5000c03006880141c615a12460000c0d69420041d2004511004010249440200381032048c2801c00054009044040c04403403c00c40e100000ca09a0f43c02003001d4078566001100070001e00c00c680d4075620084071100095810342c1410b98440311025810f006d018144500e80480012480c0705441c0e25000303c4100309003c030203007042d00c1000d1008100307980c10007002603501d00040413400d050203040e01c01c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 362999640 1250 362998390 362998411
    0x4050418050d09150c060b0402130311010912060f06320618040504060204050402120901050604090302150403020312041202121303031d0405010b032509031b0803191205 74
    0xa49198801c8500c00b90300c000484186d82e41d255440482d40f900e1004e4040041c442000d44180c5041d070405413510601030403203604010072850b0900c5640342030b42c641510a030344031b0000700d10604029030400103464103800030410b500600100313442a61011040c412021940d041e81c0c05201e80f03d00c14000d091251501c0000c101400444485041c00d050344850740c42070140b0b0740142019140d00009043e42e11007021800c11103d0031b028802c2c0c0003028495140c00c01c4084400b0003001e150344d600603445061900d111107030f0a004000003010316000348100d404942c008009402c46240900c2c0a020044400190034018460305801d900001c013080d04403019000015070003c403d51869a0803100b260b4007410b0380c7c00140f0000c03500031b0182c6641c020103001e040c0103407081d6200c2c941001d564421015044c0000411a0440c8034161010f41080c440c2c029281c00ca5510b80c01e00415041d8500d081a040d80100001d1000048075440c810131202c860000052958131444402080c0b441507055880036179400504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 363000890 1250 362999640 362999669
    0x23071b1a07080a02011512060e0a0c0506030a0b10030c021b0604090f0905011406031603020f013b10090f090c0908010f0c1e09090e0304050418050d09 66
    0xc610b01d000075003020101880041007a01d8013100380085050b055002c466031019010740b400400400380100444a40e0342001842d004040b034603030841c1480701c0c1c4100741c001c803c000003040c14030105810081003014003a100039007030141c629004005002150710000140203e007a8442411080d8110404400000340fa003030402d42481041c100400350610707622011680c80f001440000d90a020b4140004034026000b8070901d000401d150424086210030418aa0701130700600c0103036102168034550820a10b403190100f0012030395400d0b80c08504079201101120400d00a000c01612150711417400c2c025600c1c0c60080790401c20664005e4111b00038502c4405100405000d00d8030f4517440198200365620382440b040d5031352002a82100c40d518624880a0b03220034000d50144d8100740c0041d421241080030020410250b40003c000c0111401081c90603500d4411042d0440010025600a408010810850103c0b0441c0d51560120b007a1003c17503060164660f20221580200e2004089403460011143c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 363002140 1250 363000890 363000893
    0x3120f0d050f15011803050f01061d070923040509010506031902010c0f0203160b0307090b04062102040b0f0414010c03081b07080318010f020c0d23071b1a07 69
    0x113102c29070b03a80e003840b00c0c5e10011001003c90020000b440910070003100000b026030a10340c0e81100c0c03540d602e40b4940040800c405100c021540b10001e10111000020880700c114028505442854403030640c107a0302ca410300040c0301c400b0340194031090259408804803072a80b1404040b11104c0e400460001e4003085807035980101042c40000c04400452004080d00ca40c1514031040181400880d00000304940010041080c1308c1c2e0048164805884102c3d0a241460301d0428003c101d104110388040e41450014a102801140c40d01a01d01403c400e06405031207041503898840103800c90b100751500e00718098005005035004281d075884141d0140c0d10303e03410780d0320703407014020449503c480b00c21114005c0142802160680c40030f50f008141c00980b071040305540b8004142903800300150491000d1041012000107800065200380c4126a0300b441d80b010045410302c4424911804604c501415001404c8010854081419a0b03600a49242228031a071103808500600001072400301e40c04038200700100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 363003390 1250 363002140 363002147
    0xd05152206080a0b0a0501050913110102010b03030d14100e180a02090f041a090c19080102070f020a0e090309060c03090307081e031602010302070203120f0d050f1501 73
    0x21880304504001040060340c841c00c071854607815110a46012500301c0070b00c01c00e0249402401d004200850748010182421001c020b03a41c00c8200e0010a8511001c4044d00a40d0003900038980c400d00090981c0d44441c5400400000f400800090070103c081d5413001074007042d00411010b0a41d2114403000b40e0940d201ea441d054410383c204602c0540d07101d0f01c48203c0041c1d80301e44a0f24070072400050481482d080900d0411007000348440c01c03007261400380380ac000d40d1080002c0d52000c25a02150f00340d66071142c0076610241e081c0c50341c00c030f00e41c03e5000007440400d0104161040d0700e224030a55081443c81e41d141c40f5600d440200761200c450320381041101242e2481d01030064203c600900095038a0001100d002902e002540ea01c10641c1c7e4019503000e00908190701c81d030001c8504900c0c00381d0f241008891541c1c1c41c08400080007410f0580c0460001c043d528104241300300c99040001003070fa110740b91210303150035030083c000380d0301d0316810300c00015030780d19400030f5841c0641c42d05a841c0754550443c50055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 363004640 1250 363003390 363003439
    0x509100b0708070c082a181b03160206010611070509270a0203010f02121906150509030d1704020d05030c0102040308120105030705090a0f200d0515 65
    0x2c0d200d20b4020300941011031402c5844d140240994401060130f001c62600040d42d501603c1042e0201001c1b5080c10591500e80304000f41090750080380c140190350355071600403519080000d00c4005c8841c0403040142c031400d0602c0305960100a9000c8410583c1c0e580b0049903406c80b02c1c02001c0254001401c1007045083c100306490704000818401c04111003011055002c401100d422905594030240600c01503007028490401c140d030106a0a44c580740f00c084441410308005003e5900d42e4043e1000c40200040d9a80041d0240c52580021701005200c0c410050140e00002041c502c01d00800800140c0b00340598000c9000000440002085944507020001180a401000c1da4140030410070600c1880c4213100400140d441b0740e103000e0725118191204201808160400382c040e51082c0000c1c492a6503150540b6880304490801042d51f9a4070140c85000c5c0c40030101800581e0341596101c0001d00004001d09206014004204200c3c2d0314051180e040807100b1500d01e811103084543c200d6540002c0204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 363005890 1250 363004640 363004643
    0xf0b0418020322030e13051303050c0a05030a090303020c09010e0109050603071a0a11070f031b0e010b12070212040b09031f050405060a0c12020c010b03060903130509100b07 76
    0x110b4903605a0182c00c0455410043d100310005403024506031017a18110145403141072812200700514a0541030900301140480009018040701085004600800704081d4504a07401010341e925085a5400a0440c440d01d010032000f50042c07110751102e60a1102015040715800a40b040c0d6607440d1846c00e900800d400b40484d074041c018000081802820010400c51000c481c58070b072503480e03100c039200400c89441d0503070141e1960802c40307040105003000c0c0100300c10b0303e40007801d412441480e19440a00c2c40c8255201d100c03804884e0000103a055038240240100340011213800c0c0c050340d5200d0049803074401034002c100c502c0c0400d00003403004010140242c0700100010301252044c0016040b566070120b074510403000744940b148100020044140103668211102010070b0202c800c14500180c21030000e0021000d10319030200d003c0b60204401d401ca90302102e40a001c0c0c0e0b140d8104592515141e0384080001d41081e240a200000d19003403e64400384204d404008801141b030401c0502c161580c4030400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 363007140 1250 363005890 363005911
    0x1302060904060b0a0207080c03030a030c050415050d0f14010308090a0308030a0902030705060a02030a030b06040302130b01020105090a03170414070b07111c020910090c0302040f0b04180203 83
    0x10848407038950707200d52000362280851041d21803040d880000c1c503140240e003103e0f590b45c20402e900c1d40c803520000151154102c960a001c92002c41602049803903000300d1b031082840900030700e50801c0c1580c2003001404030400c111000d01a8100040e503440039204818114540703810303032400400108548402515400074000e1500003480d54039118400a5081914620a02907450071384404500e010031580c402024243c40f420f04119144d01c020391a0700030494840b05260300c0d8146010039a91f500c0840740511360060440f2403640b04000360200910446801a000d980380001181501c0300c0010b28030801541a41d03181c411901c13a44030002e144c040540201c40404100340c1451900e1414002d44018290b056012a00d0b10141d0822064424080c4000e0b80503010980302c1c00000c0210b00c15000c0a40d406860400940e00d8030a481d011141d0641c0c0b140307032110310f0903000c5040c0540c540c00034000c6541c107451400b50b4907100c5180100314807a43c89001c1000f82400301d000000022034029580c403200818 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 363008390 1250 363007140 363007147
    0xa0e1909030203090d110913030210020c0102300906060d03180801052e0608010902090a090204180e0d0e0d0302010902090c07140c03030a031808070f0b1b03130206 72
    0x41540762000ca5000c646c02001c00c00a0415810071041e03065020341501030030360106545440c00b94440d4070466800704140d40020703807100b116409404071180c1c6840d5008110241c507444c402a00c0346e1100704055841d5012520100d01000b80004005001322002081070008400b1039800380e0f01400a0b10400007510b80030080024410f0080c8241445140e01c0c00d000b84543c036084240709404519003011003503420742403c0502207942c1c4821034905503440a030300140e035054068006800444030fa0301440c00c039400050041250034516908003880130400c00c052180e02c40c6101c096032180110425480080c080c450640d00601d080b03110041e01500a00000500c1140b60300414040402103c00d20000e030b10000c0c00c0c0e000c0110049a901c08920544080e11070300d1000c0c0e0003ea124400e1480d644209a02d60224210700482c8006c00c00c0b400da4071003201a030303600492400000b513801a01c800d6640d08414000243d403241d07c80c00326030002c00103608441c6140c0e02c054819410283c40c0605a070040c4050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 363009640 1250 363008390 363008407
    0xd0201111203060315090606131526070e0609040c090f05040b090a050703080a020c040609060e10060c02060f0d14010302040506100c1e0c140a0e1909030203 69
    0x34021003a1548401c1c0a8555a15050040c54949401c446003481e0807034140341000300303080011800c1c540010b0101c40c80401c82002001c1c50f005000c009401d04080c01c032110002800b120a902c868042c0120010f0b654402d020780c0d500c0030f846000e00d100d0f0010895020700054500d140421080b503116124032500d54a5036180e100714800c94801140f001c5500e5507804c144002c0c0160102456882641803008040c42c0c21259030b125100c1c901c80c80010b02c0c90401081400c416402840100c0b07001d4006402040001c7d0f46211a4016084a205e0030503072411035008246841c1c040d06c0910b060b51155128005400155401c1c408680d00440086045060134070280303884010324050401116410056041c281d41103004110441d031002c0c1c04203110302500006100000d81146020b40c01c1030700701c400701000b00300413551514000d403403000080003400c4044020800c40d207140f10820003010140c1c0d010305c01640320507148040e5881a100081070b040c020a100c0038030007047d000710002d01d01c03910580f81489141c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 363010890 1250 363009640 363009643
    0x20106030c030b0417030403020c3703121407030f020709020a110f0105091b0a030503070302070f08030a120203040f0c140f04050f070c0c030f060606080703060b090d020111 76
    0x85410469649031483c081c08240b04081e82804842d504851109245080c56039010b5a80c50b04115414040e041c4903403801425400c103200c51910820621070840703844210106480c0b0f04406010444000403840b908900c000d01c280f042560130000d91590070303d0040741e903d0964030104880c540804601c039048001c501c9501c240054a4004940c3e00d03039414847c0d1244029041004440038601d42d40e00d0310f4200950703203100003592560410110030b00740c41e2707000c00c0c0049951203010b82c0015003148800142d4004240e400200034048805844103003240c3d90301da1100c0307601c1c1e01c580c0d5003a000280c0e03c024845070420043d070046401070b01c1303000c03190365220640c0d803840c621500175813010000321f010307244412481c10891001800254100ca04101e40e01c1c1c420184a5101009804074003082218030341e030810041e24110240c0919000304c4101030040303140c58500080e0465001e590005510000030070348030740c000d005140569058800c118184140c0405220440c401030b0000c2e8108400e260000501140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 363012140 1250 363010890 363010913
    0x3060117030c100902011722020f0603040b160801050a0501080a1803020c030d0305061c03020a0510020318060402090406020f1c060609050d080a050d0207020301050f0402010f0f1e02010603 83
    0x550f68000c150303000350f0700014044082c503c2c0e840005080e018108181042c498943c2c25001b40014101ca01106260020414185280e100d030f0303400603000070501040c414540005841140400c18080080080d12002c4410700e40c203200c0d541e000500c0240520056003d92305140d80a1501c200c0010f41c142d00c40c00803002c03030302d05000c2500941c000761418041828140b107079140980180c2000e00c04d0b4144a000304009082c4101540360305640c40b01d000040610030311001804541150459548002d4206000000e50065900c440a01030789052200303003030f1021610b1807003150014006422640c0380d442c4d41000c0e60040b4000c1e60002d40400201e000d048003500508181c800001c8009002400e0a10142c081c034040e401c101c1c803c01c00a840d00000074800300803207150203075034034042d526810700750010346c064011044025419400c060410030440e001c4108203100c0c5000342d80700165401262800e03a42a80045201000240005001da01a0f00068824070740e0300c5803403000041071552900c50118210 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 363013390 1250 363012140 363012163
    0x201052106030106060e1f03020f120901051509040620070308010806010b09100c110409061505011407061a040e0f0d0e10031509050c040317040503060117030c 70
    0xd10901895007002d106000203802141850700b034100150000a240b6a46550440d5a50250b00c40560069100b50103403402c1181e0201200c1e2185007004a103804810f003100c01017032540c03814001a03000b22442d1001c0c0901c00000c1c2024a042e1115200c00f4054886450100e80000c2480c2600c200183e2207401403000782d006c2e40d01c2035001d50616035624200081a0b012540d05d01040c41260460b03500c4a4060350000458213010424164503d00003086103000d83c441c66005190561250a20070650001580c0c3c169103a8248000c549450056450303403003103048810201002e00003400000c220740d214882140311009030b21044200107002401391282e590010b600c80e04040b40560000c1010440d5101c1ca4526041003c03044201d100410001032495810504040e02c554803900800b101e187c0000203804920b4007408680742001c00c0c0002a441884225000d9131004110310a030a1010103407415948001d0143c001a4600303c85400507403c0001445c005000c100024280880100300c0c440906 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 363014640 1250 363013390 363013447
    0xb0d0e06090a020301050108010606022a0a030f110316090905010902030607200c06180616050d170105030a0f05150a0c14030f0a020a0c0b090a020a0803130909020105 73
    0x41140c03050601b0350360180e11000f501da05200b1309014458001c40c00299120003071442c410789a044c0c00c45444014582020350350055020301011050080c11101c0ca844140100f840c0594400001c00b41a40c2d01a14014580840c00908041c04141c540350005240366000700004905404581c0000342000380c01d40342d1802091118000c0f807410080a0302c82c0b81c440441d9000f4041004520f0302041c00352003003c034028003034030000064200d0380d50b0b600c058440d9201000c3d0707490403400b41441c00c65940d201020b1320202085c0940192401c0842c030800640c181c2e10040c0141080f01c030150307101da0300d5030170b0060125007d000713650074640e030940d20340480e903c1070386102c9010400049442024280b80820107000d90104010001c0148448030030341c0d540d402c01040400180ea590340f15008580c100c22549000f8080c0c95010140700c0c1c0c000340002c0503044d00d0f008648034000c00d0b60305c011081d924843d0b402010400c240407134007001601a1684172841060041c1420b51074041c01316840300b40c0b04880600109403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 363015890 1250 363014640 363014653
    0x1e2125031202070b030a2007060c090f0302010c0b091e0c0f0904030c0b0c0f070305040e0702010b2209060606030221061c2a090e070e010b0d0e0609 65
    0x14041c0e81649100c4699041c006000414101050482070b444010904004e854440d80a030305503059000e11020003100a00b071b00e42d101e2942d460000d000c0c0102c165003600003030781050041584001403801d2000c40b64143c6034041c0804965a50b44a0400c00030700103140e5000340b104880b4000d5110010803201207031038001d000000d48580400034020b80300030a841c002c20140c2d080100003508032403140140b80d00f00407005100e540710204010144034050810040300008070310b010070503800c40007910641c1c0d40d4000f0380c4003542d03460604a08076402e015060b40c2c0091081c014030308441c0928089401500311480220b641a0591500400e86586602c1900001d07800141e408640108102260104481c40060304541c02c0c0100080c40c0804216188441107048802c114100140558161940c80d500d440e80f4030640010080050103622a11070441c802d400c1c001440420348011400405540e003000301c0002c0740e4280401c0485581100380244d0502c0d41c1c0c2d0f414030300001d108210091103040c032803000b01003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 363017140 1250 363015890 363015893
    0x90306050703140103080c070302100c02010e0303130312050c011401091a0f04020a17010611120307080f060d020a03050c0406050607050309041e14061e212503 70
    0x220350005140034101442c01454416800e03907120103038112508851410385500401c488030f4208111540002c0d4001c00307012104001c3d981001000d062a8002d8950f1004c074007540c410326450b80b20f5030001005868007a4014400108158500c80d400086072a2090800c00900c80040c21244032a4206120255000042041a156008100e0303800c50a1000003030504090012803001281d4490881c4110f401040702c100b2a84980c1c060181214000125038440d40e588001034040490000c1c00021805400706081c0e040d071141d01100d0003100c03940c7d01d0f60340076956000c00c078540400103041c9a6000c10040c52580140c0e843c8205040910b0251026014250780d8030100021070344170340c2c03110703000e10401c1c0401404114003100b40d03080340d0b01c1510040f910604124102e41d421545402100040b0314041242c44400103d40c04684a0baa0a8810765042c1c0c0403840031180c4002e601c901e0f164032401d0034181c0f0020030200008419100440c10846095000310f080c202140d21a2500d0b4060b9869080402c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 363018390 1250 363017140 363017153
    0x20a0c0c0603060317090102101e0504081209030c0c1c0209040b18010b01020a060b0a080f0609060618070e06041703190c0c0b07020a180e01050609070207060c060209100903 76
    0x100503403440e48106140c6151b9000117912072000c4110601410b584203d00f1151404c0d204840742101c031400010032061a092400c03044a80200c0d0300328516071241c0000401c4001d0010880f5912181c1c0801030042c1d0540104200780311032420120904207200032004401a129016103a000d00d01c500d194182c02d10f46034601505e0284440881030880c0e0512940d180aa41c010610110729608004c0105030101402c0214080091551258040d0703c92030a02c01381c0d4a2022135064000d83c51401682c00030b031034620030031910f20550b140c07003078845014402082c209400b401c84244082c102405850802c0c0e5915619040407440c50a802d10a4000081c0c030710780c0760964002c2c281c242c0d5807800c041d21242190789981401040702e0003102026440003d11a00b5581c034200000001d0044101c01d0032030600e00b441d0350000e00b0441401d611650300304000300f001860b1041c26a44540c86e158000c09686240407401c4806002208003501c590f41c1c02c001400d415150f4080428080381e254032100c000c18a5131a150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 363019640 1250 363018390 363018413
    0x52b030c0807091404150617060109030809010f2705030601120b0705070f080d0204180605011409060409050c030603070b040b0306060702120a0b0612030f0d020a0c0c06030603 77
    0x403800c200c0e8000c200311095030003090740710965000f61010303901c100d191804103005002e130061950850625907000a40c0a900000300b030602c001c00d4000381070302c2d100c480064a02ca00710b80002841a07005021044945d40702c0e0b08000050221464141c07400d034020096880d0120200d41d802c1144034088005001a0400b04891801844804000340c0510800e490700d640c4040007034210410400009102d406202c83c40701020f01e0582c00ca61401d584000714205e110096110703201c0c10348100004002c3c154507501910a440441c0c8041e1242051160500c0c0894500d901028805030300c05030030b00c40428100342d2807003942d101d5401f0350344603542d034100202010f00e41940341c0c0c045222081d04210512a80c00c25405a07500b0800680b0265114402403001882035625040d5500041c0b01c0c140080041c050034404050244105179900c40b101c1c01c0b10003006480340f14a1040203a01003041025032003e103071682c010222240e00b0716002d6602c01995483d00c4084645a1020340004e032100c10602c28454202d040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 363020890 1250 363019640 363019661
    0x308040f05060c0706030905070b0c071406130605210115030e06040f08070303060801050a050103021e0108011202180106020109050c040b090a050a150b0c150f0103080304052b03 78
    0xd90f080000d511100b0340c0e1401c1c2400f0b03103010182c03030309140c0007040420040700c0041d262114403280c5030590318440c60b82d00c04140c401d04242c51110300d416911410300c0000c882c2c8002e0910310210601c1d04144096800ea0b02c181e203210500810612041017211030750401c3d9002e80344030b0001f01c00540e141140242564000394010140c0d4000700140000031b05611611600103600140d80e586801407804c043d40100020391129401c0d5091000b0815480c0302940181d051300d200300c5141023802140c1544680a0244d010700b1404104404014070a00e0489402484c3d544d00c0180005140c2200000f007413100d207004e81c0f000340980c2d1510503110400205101003054001c040c0c03010020819488001102040040c165444140c0c2e1100403d00001c130540040709032076003002d08492456540c101c501040d6000700c0c00080c03940a0051442041030002d000a401a0080300c0b06030a141d08688a00055030710103402110144200314428081c801424200541c940d0070006031002545540c001506944c101c60b031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 363022140 1250 363020890 363020899
    0x190f06051803030f0a0923070e0705040504050426040614090105070209100e010803042402250504061d090105040201121a13050709060207050307140f0a0308040f05 72
    0x71807864880002094a80c8000f41c041d0509158888503801c0004026100c00900703a0102000d01241d214040313070103500b0a400080444182940d03800102c0034006086d60450300103681080100701c0c606c1d16070003c580150042402ca080800c081c040c6c090380d000d114031202d04003240450100003840d08030308041184441402c0e0b291034002c1c0c10000920b14410710030001c1c880d00d01a008201c1d01e07010182410041c3c02042d00707816965854421140e981c6e002031003035620800744030030401c1c1c0e80d4081c002c1c03143c8c44800c66001401d40911080744490307120a100c00c10844000150382c00907850303440340100401014881070030359460701f69450700070390180018800c4d02568144014000140d0f4003140003a000e694131000043c503040c09a0350404c0c000c50410b8503580c0544024481030b507000d9191f01103030007540300e0b45403144415a90b044c240d8075442c50388150f549c581c0010b001000036800e030540d0302091240c000c0c010040705200b9400105e02c1c40c01d42d003042d03801e120701250a1007080700e584000800b07808200c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 363023390 1250 363022140 363022171
    0xf12030c07080c0a0f14010f110601060806040f021806070213140103120309030e0f031005150906190e04060e0d020f061003080f090301021204030201050916030503030f060102190f0605 81
    0xa807178400248044801c50b04003d400c008e003560441c440c00b141c160f40c0d0010000c0c0e42c0039507076a80700203103c40c20507100d9030b00c0345180c046800c035460443d01c01c42d03204003000601c406008502008200303a540241c00c041e40c10a40c00c071403800c110b010700e00c9049001c820303c862011055055040080e82c1038521101d040a1610301241d4001084d080380d0121031001d400c8070448031000f404d60100b800e0404c41110800701c0c608000a100c4020140a1501c0026000703a440311070301e079600400c0101240e280c0c9800c0a14103010b003410f10820801c4416103a11900401b40401c0b02c010420748140307050130110250300144c0100440000c0f03442d0030b2040caa000006444450000c50550b2910f220902c147146520750000b00021f2210711a0b103083d019140201c440c0c901c0c84045162500700640a802e04807801c1d441d600441000c0711070540c414103404262078201c0015402c42c0d40340d8030302514020000d0300381e034158032482d401540281d1400c02180300d10341c4540d040113900501c5180078415101c010f8421003001030302c44c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 363024640 1250 363023390 363023399
    0x70b030c030a0c050c011a13020901081b160b0a0e01020c100e0115170c1519031d03040f0e04031b1a012c060f12030c07080c0a0f 57
    0x2035003070741c1d0002c1038000c001481c00912881a9228821807505410f00c0d403c1509000c600c0e010212909101d007025558480240101e95040d0102c0c8511407002c0d0100b020b1201040101c6421004140621341d541c1525140c80360220320b04680360886882160b0410b0a14104460140c030760003860841036000e0000d509107110142c00301e44482c600000c102d40960384800c039021480003500500041301d5144190300d0415101c0380c4000402107140060080da120720700e001c42160130082c900041a11220b00514105503d81d82c501c1c07071100070150840200343d1a84081640f09030445519580b5010700001103980302e02e04034140a0030704071503222200390b0059100f00b2002c80c0e0001e113400814007021090703d108030880d18144480191490045d100c00100300c001164801e0444500d4a00b4141050480c0c3e80a0041c2c0000c404500d04540c20750b00002445004107882c20990030050b0380c1000da1040c4ca003814610100e5500e854060303444a40d01d58001c401100039400c054060710084c21a101c185a84075003030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 363025890 1250 363024640 363024661
    0x10b0903251203090905072a08030c0913050106020f010c0e090c03040c0902070c051516080d0e01020f090103180803150f060c15060406030b0406090203151602070b03 73
    0x1d10450700e58035501d0600004040c49910504d014116411040095003084c4800400707070031414003c08401c1101852500741c0e400720b03000640c0c101c0d50000f010751465071000d0042100350018042c1c00d401035242001a10310601d54000c41d4040d007038640c001c0c0341d0344810381802400d4481400e6020140056a041035113241c50300b07043c495000144c090955a00d44507840c1c540c00c03148041d8024136000d031000c07448a0400a0590000084403002c41d5441d1703104180c1c083c4004e162050900b03241c400302d00391a601001500d150098000180350410004500510000702c6003680d20045d5032071030310a00043c003103440c0c0da0107110717549190b039501c0d140807000d401e541d40300580ba1101500e240103c010340c41941c0c0043c1e0b02c085e24600d031140f000d0001a1260340000280c1d540e0003990007414640b0300402c001810b5424144558002c581d08400c20030103d0711262207034402802018010303601400340c100c1c144101001569920f0260000c80b001006840398160001e04040c10b542198021410800901100d46003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 363027140 1250 363025890 363025963
    0x50a05010b09090c0906071a0a15080c01111f060503060708040302151317120c0a090501110102040314060403080601140a0e010c12030f061403030f13050306010b0903 73
    0x7201104c066591036001c00082c1c1c14099504001c241d032165641d01014004000d404500030816030b40103200b18002265440824030300d501515606071b102105008640d8851001e0302903c001c240e040d50800f0711a1000444038000744242900040c1d191b400030069070404104069000502d454160024105582c00a4640d090f000d00c402070703450b0301c0c8080f810401a100c1e02070141a4044207602581241580c0c40500d600311403505907541c0b00d07100001c1c0490000400b02c4050070140d58a2840c8681050015601240c00c0d0380c4e01c0401d50b41c203101c084005840d10f0005641c80e0507001c020051480c03d46402840200003c0c003ca041281980344943c01003002001c0d500d00d0022810034400424581c0300481346018048800b8200f03079008144075405940540c0700c42050390a11000b40001600c60000d201040002081150903500401050201e20343d502d01614000001e500d10343c04055407240001c2c5001c80a80281581280000300107069180402050328500c04a11164604108c038128070960b180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 363028390 1250 363027140 363027151
    0x20f0102040e070809010f14060301150f050d0302010b120102090a080d050f0a03140a06150e060d0e21040e061c02011d0402041509120b01050105180303030703050a05010b0909 77
    0x514500840c001709400e4000c0481d01880c02ca00704a1903684085205661005aa03503d0180d4681140c03102d1042c140944002030340c01403801c07070003110300d8802885940340f40c0703000c294115540c81407101215505c17103000c150b140080e0300000da20348003143d04009080f0500d50000045030312260002c25074503000015108140341c0200715513100c1e400b01105402800780201d022100e200311504008000c0c6c0340780d0115055402e0703488600c5000702500001e9401c96294104281d2018051106003001b620540140d405500c90805076901804616007a1001c0c880c81d0658030035844000c64240014a200c0d0f01185d130000c002c0756101c403140c0c4100d00c8994505544c01c0003038104840441d0072003c69051103008604680068011951595208000c045148004003903400180c41142d00080c141003d8110700b1003550060241940c5034030300001581c165024401c034000460900d00b0341c1400c1d0b80c061015510500306620040303214503119070700c40216403050308085403524080c00680c000f9100c0050150780302 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 363029640 1250 363028390 363028397
    0xf1e01050f060d0c1e030c0e0904050703080a0f020c101b020f060d021e03090607080718030506070909110702060906040f0f060e063109050108010c020f0102040e07 72
    0x100030031408940319214100b1150221410114815100f030350017940c01a00c6008642204a46501c039581202900d000c44440d2000410311301648400749001e03040d041e041132003038084428540c3e40740d4484095401400d002008030b08999900800340e5011302001a020710122075200146110601c09443c2d500f114902141441c4a10b1030a803c5444010b0003640e100740080c40140c90700820094080030707500c5800c0f10b2030407200c41541c407401811184180c90142d0680005454103035521041203422610003846081008000c0c90f0f422a008102d80710040518050405050346142011014000196a030b100035941458240009507142100060b40c0301c00703a04842c12507071848031900046580c0a03a4000303640752205180006800100d00e00a10225030080e20380e00c03c07082c403003420040f643c094442280707400d600208820140743c001c900c000211092003101d0300020b81c0c5803040541111400d802004c080d030364591010400c582c0400c4801f11407007044000350718140c280100d10305503440c00351034202807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 363030890 1250 363029640 363029659
    0x207050a0510260903070218040c0b03090307080a1d0108071d1f02060603060a060506030f0a1404031d121b120d03150806060102070b0a03060e0f0f1e0105 68
    0x20b12029203008140c3d4582000214558108002116101c0d403020700102d101d8400510702c1c4241c04a074411180c030480c5c2054070190803900c0c0c1041c0514507840104062250301082000b44001130b4010098040d81980b43d0f41c582c0780704c040c542076100701101c012005061204071000c001d14250700001a002240071800e002c4101d0f840a80810340300c051131140700783d5090040481140e82640003032443d01c6200700303c0c221155034031090500d504031401800b4041d00000100002401030014075103082e00414242400900001c15002c200d004440030749044002402d644484100b4109540708118075940c203e5951101d00940894155212480e4803d02504000310748000e2041d520010914800c10008044d03420384400c0b407034000c2c01096248010340c1102c081500201c7d441c140001c0c101d12400c0c060b0001d10754641490a4480b03540c101304003140030581c441101040c6009040041c1d40503807000c03d9607104504040c0740140303007114000c0400070106801d84125007a0381054010302c0c1140c90a13a100c3c5513 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 363032140 1250 363030890 363030917
    0x10902031b010905030f0d030c0801030f0605040317040506010f050102010b0d0b06030304030b09101b02030331050105060906090402180901093002030405130f1d0d0207050a0510 78
    0x442020f00e40c403050b8140aa42130f0300494510100b2008643e05e00b95608000c082c06c0d0300b40a40b5040c0083c080078003004095200d0a00040e01e650100340c04c907000381040700c0d4094080455001c0e042d02110308955a070081801007001880750700d07440000c0c19003400280020044580440d4220003690000b50101d001e02c40481c1071a2802e004071009960040e440030080d1038004000ad58610000000101c0380b85001c0310708810030003500340d10b14481040c0e0f000e5850741c0c4400c00321118162043c0c6000111150500c5441c134106060311200040707d1244001141c989404000c201000390f00a1550340117200300d03820070005a551860362030028040800340451605d9044059004102c40140140005034400c103444030b40c02200c035000312807500400c0a101c1200f00b00000c986134001c511800c0d03000040c040e00114a2880780d0070000b40d6246030300002820480700700c0312401c48180e212010750150003e000314180300764140001c8005d0102030707401006c8a031500b00428a84065203100c5000c01944455030f8a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 363033390 1250 363032140 363032147
    0x2060304020d0602070b160503190c0e22060f03050a030507150c081906060e040b040b1003092003070603020f19050903012901051303050a06020d0e010902031b01 71
    0x8200a4203c1d500710b444158900e040758001d00c065520351401100c01c0244140c0e41d114004491084c2d02040360b144941042e4101c0134050818818503205000085c4c03541c0200762904141154a0b02441c1481e450500d8080120400c031a600e411030990454000c0d002d202188002504001c1691b1500e806e6079903458504041c2072090603071004125250421460302040c982c4216800c1c01074034442c081003502a80c10000a084550920400300810082c005018041c45d02d984040901e41014101080000001c0700103a010059840c40030007007560344104d1420310030406034492180754414485000c4c0c1c206840040e0b0349011500c175800405400240b0002c1c0350503ca400e43e004503403500784183d40e003510180003920640000125034001d40c60001c1a075030648466140c40100a282030008840780e540e071004460541c4040714400d0b10080901c0c0003c00142c00700101c501039030040b08010f8860005642c8002505d801c1c007001000c82e030604000d1000341c0e070b010403050307800d007003101e5820902400040140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 363034640 1250 363033390 363033409
    0x4080c12032b0b030303251b06061406070b04020d02011b030305010e0705070b0c030907030b0f191109220f021804060e07050d1104080a031106130206030402 69
    0x20400180b885410395410051000180301440d001c0800380401030807a810300d5503d000407210400c400f8100c00080a081001c55203100304901c840c80e10080409030040e0320000a05501c00442e00160f40308810400d0007003103509207075200002c441c014038240850301c688000960180019201e4444800000d0840e030180300030920814200c000019044980d040c0036000b13040074810261a40701417000a50510b111b44100c800e0141c0c042e41c031078140e85aa40501403150401020b88004d441940004400f040700d1401c0144900036404982c04240b800800056400c03150410845101d8101085100d08106400c11782c0d411234802d40d92a121940c0142d9100001c03002180c40083c010b203040043c07412045503400034071000080c00d5510400d0140c4000303101c1190b00340d20074060f510707259802041102e440b40c1e00620780c1e07101c1c8180c04079149410107007450342980654803802d82ca83c0718283c03c008041d04119050000c078030004c00ba14540c94000614042c0810018000b841000300200007001c40d95030b030303504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 363035890 1250 363034640 363034657
    0x615100f030225030801140607060f020705031b10051e1504021303170708190507051b100305010821070803011d0115050a080402030c0d060204090b01020304080c1203 73
    0x10808901c610100700500c40f25488003a800100c0c5070f400811054903c800c04821001c002d441c0d01d282c241c564507032400a041d003180003a601c0b50208150408244d04101400f880c07103510b036140031041001e000d10b030326142980c50600b1903141072004000345070f400c1103540ea80341c400107441000555242901c40221200040c0895070241c0f022071207100c4000040b2109003502e103c2e0449404480c43c20100b06c4e84e90062110050408004124040c3c00c610305115011146031a0b05001d4100b0404d030b90381d0380c01c009141c840001c0007035102896654600d40030f0040c001c5002c50341004c000782d50400c240d60ba11800c220200ca016801c0300d040b5402e4815000c0d04440c251600540860346950b1140006000c00d0b88072125030040c00240c10001c1034520300c10203110b42184190f103c4519046400c282501c2e00300b4001c1c000ea034903000d1030001100585540802000d001d104140043e03507a4105a903540450780000c4da10703411940140401d0217201d20004043c20280720499050071510301400d0103604d5031180018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 363037140 1250 363035890 363035917
    0x9060d0c030b0718030c14060c01181709010927050a06151d0910030f0605040302060115090e040c1e05240d1d19050615100f0302 57
    0x80c000180111042c9950007900b041c1e441004100080c01480404c0226000c0901901d0791250200302040d040c540300040c900025003298107020a01c1c1d295401c642c0c078104041504c00e65209601d08105010034100c0303168034402d824600304902440001c005141a01034220150883c03950120451811418081d101c2c689280501c170600d046000b42001d00024410508110030120703079014524007a90796080404c05030110f403d19166620100308041a000e0010060103612401c0880810f40035410900301c2c9000d070001143d581000e160003450000b050380040c0f108400302c240d03100442d900140c12001c0300d485008500c507039111420035150842d1242d002441c480130700b658064419200741e8800c0308950702119001c40308403075956528081180c90105c0e10103a1420031000a100d42c282d4005da4202c11a440c0325180210031140d068988000f403001480039004a554200030842d081001981c09103820301d400d1608480140840c4503c0c00308525041070082c200c000724121387c803950564500001406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 363038390 1250 363037140 363037163
    0x2090a0906030209060301020423130204081501050303090a181b020d140a0e011805031f06170a020d030c0f0c06030c03091502070809060f03070f11060609060d 70
    0xa03440d2005058030720049000380101000110a880e043c03081d01c003110145102c00760140c88822000740c100e0500d18000d94080c1090303840c46c100302201d10291001d060240001d01c205260680c072490b09110507400f00d446680200b01e2003820741c6401d020482103c84030602c640781692409200e0016108100110b006509903250507070800380d000070303510a944915100c09900344a0401c015106218100340800030030680707101e02c011355118001906031220a50030000b0456181c030f0001e804c03c1c0c81300c1d00c00c0c0c81c6110403007079030304c070480040c840d1600804000040e0492124010540c5841c2e041076400a031140d0185c0840c0d01c03e00d4000c142c46504564400c001000410503450300c0b07440c0f44468064100000e00e01008102414041d12840c441039400c82c0060342800724860694002e580b04d40411a100b9106000402d0141c072054003410856208280c016140d01d40140b009245258160110007040f54100c8407050510340440c035150402002d652003412662104045841d2482100b0010143d60614 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 363039640 1250 363038390 363038399
    0x50f0702190e070504060206060d0203012a09060810210510020706050105030a0c030b070306091107030f0215150d020907020f060709060518190e060f01080903190302090a 75
    0x801c0800076180307190007615240d22a03e504807202d024a01070030026a116a000c21171a1410111a0004510040000c100b00e01d09005010707500519598144e8011004c03d4a00844d50b0801301c1e5001400c95858044514a80040c030148140914881c06081000d00500441501c00010030300e0a10313600401140c00000010101c44002d600c0101d080c1c03142850580007050514011903055000360708040074a450324199104c12585401c09403e8405141c0e5a8800141c0314619008491104800c0350480707031200c8003070802030000150450414215009003041110300c2c1c1444505a800ca0408513146000025a6002c01c180344800301c80a540005a00301300700c0c0c0194006030001078900c03c00700b59003880d15485c01c195400390b400e00030380000c10b1003401288611809124080e544400091007178580d406101ba164007008001d800021880030002d081006c41e00b460903122650200a03c0c0084840c038003140c0041d102e0040014078440d1f0f019444540352441d101e80c06590905000034581c0f1350144d603d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 363040890 1250 363039640 363039679
    0x70b0f130b030406050606070308060f01030e070e060a090e060406020706110f090a0b04050d03181e06020706020d1b030314090a03030501230d150c030e0c030703030f050f0702 77
    0x100c50446404e400c080000f401810a0826140341c00e034140c407042500d44507201040944003c006881b410140da40702d00d0003c41c40700b0805c0070002c0076010380c2000a410f010b400c0c05034680460700f000071110301b420842480360000050342039115410010060b01d800282c039140000c0d040c50000d11340820808940c0c160141d1a0100812000900f120903080307d070b517103803450000d900a600c2230540c4900d009084c440846e0040c41203103030079888084803401b81d1340c503100006c20000a000c03502c107291060b10814080d0680401008015041c540010001011604801020103c405000030551011103814504041c081d41090418401403c514001072a20340c9500342d403a9a203202c00c1e400241404c0000900031644a20407682070721002084c064482c600c0709208040d00d43e05c13021201164141811540346207148a902e042c24110755003c103070301c030300d00255515041c00c51425910a8000030700410000c1c2d003016240c1e1407003410f0300704a511340d020202d08261900070307150041d4001c0c28502006003040725 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 363042140 1250 363040890 363040897
    0xa030c0305120f01060f080f010b0c01060503070905100e0c04030f111e0f010c02130518030304030207030201081e0a0e0a02220c09080c041805011508060604020c070b0f130b 76
    0xc0c0341d48582000f24014022203240c5008d80e494000c840031074005111200518004190034000f40c400801d0056681021074540040d69210b1404156034506101846d0b82c8400080010000030504516505159a800d80c542c0306070f01c0028031014060400000700b010448100080f600024148040c0700269180c40c01d5110300038001c0e9119041746c140c0d02070780e580101e2241110a40142c400340d09021740c50700440c020702e4054000610954101c1c180a914001040214803540c0304c1d0b800790600600e1480007622034180074141e5003ca0261146801003030a0304c480703444d4031402022000c2450705014128904000c00d8040c040c0d0821051200079212043c1c910706041019802c0400300203004102d07100f20340e407a40a000d140ca540e00310342c008849500c2c2039084140c1304020201042005250342c2e4a0381e08407907011000200360961414200400c840c2171007041c0d481070302035405600c5c240c100240c07152240070341e0150020003800803407040300718640036042c0d0711404c40d841d40e07032a4610349401c0e40000300d40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 363043390 1250 363042140 363042149
    0x4090507170f0303060d030504052701050d020906040911030f150609010308070f020105121e0702010c0516080d050711010501090b0a090c1403011205010f060501020a030c0305120f01 80
    0x8061120145074181d000809640b5000c2c01c0300a5401c64803031000300000b40d12022019001c001061001040e5a030310a540001070300d40d0260400c1c6d80074843c050207001114160300042c4103041050000c0096202c0904269201c0c0042300c0004603c6c600745001c0c03000c464210103664040c410380390710854820001603404444121400042752642c0d85a0401520711024080200920b81c01d009020004e815140f0030405248141440e0303040c160004510380e100c0c001103e001c4906407101d01001c0030341d01c1503034242d604070178548020f100c01441c4186c06001ca06c500b44c06a640c29550300c0503c07040c061810300307440819100450a00076420503020050548082c074019000f25440c0c000001423484140c032481d07041040207444280d01c5c42c50041a08002c14003c150441400811750154000800003801075002e0044218000510103460504600719014016005c1c07602e4038040043c4903580c1c001032617092140d410b1a2040c1e1030b05603407034210b42c2c5018110102041c007500c2414050a01080105035041c1c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 363044640 1250 363043390 363043409
    0x6080a051c021207080d1107020913020a0b0a0c050105040c060801060c03021e19080d060f0f030f080c03070302072120040b06040b0a090b0f2704090507 67
    0x80d0340700c400c001041d801901444015034081c843c926011800b00c1c01034071003540905052803d102c801164802515006414032041590000b010400c610b4100d04590300180020440b801511155000c01c2501c400382c0a224407000f004202c0c1084948100039030084268000000c3c402c07405c0920b4810304a103d1405038401240400002296a52142514103c0540c00d035004102600304613544003a90500c6010101700d034004c001050100030705960310300c03459030301c0351070312903170340e00041a028046440076040703035480c1403803e002009100b1000c01443d040e01d400508980b00201d561410611911480600c03030b96901000c142441455004100101202d0040c0d03180281003521016820600402103170003071401c1c4523440c40b20242c00c5000520742182c4009440044c03624070410000e00700384c21640c0100c0070b0500000b400b204003640316080000414108038514100304181c0790034451402500b1961080c21f0035071903200200d205010900090030b801801c20441c0c0c007110709005482d0146070144107003c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 363045890 1250 363044640 363044653
    0xc0a0b0706200313020a0305190b07050c0a0809030a210201051b0d05070221030109061e0303030c03091208150306130b04080c0d02160b130902091306080a05 69
    0x80145030481070582210b050119145076940c041543c1c0c02807050800b6604880d15140c0400010000c104160751401302c0d03112107003150740030b05d0450004500200702a003000070501403c1e52a100c0000d45090150744464055104c100c04008a481c100c61444054800003c3d074600311811a000744040ba0a115140d0007444aa43ca04008680c10f004c02510300d541500200604120014158401600250b1520556201110000101040d01986103566a5071000003004222100081c41904000c02116039013000000c460f40d20104c4000d414070020b001e1503201c10158010310310030751080c040030340d1000358601854030301c5100520700c046c12170344a0b21084000048600750300e8000340b007a10884411110701c42100c010f54584c644180003030b208996604040c032198001507004d100c004e00c0c9104540c001e00d99104152100170041881c3d9004850b490010000c10079840c60300710070841a1000000d000d07949100e0000800e1801d080c080541300c40515010000c00d0b00314011441c070300c6403801042200c04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 363047140 1250 363045890 363045911
    0x1a0c0d0b01170c090a0503030d020a030e0a020108070809160303050304110108090d0e1203030901051603020c1b0612161d090402090907090905030a08070503060306010501110c0a0b0706 81
    0x40450401164024045101c2c0001e80300a0f8003400400c4a01409000340245c1e030399500101780355803c59000e84068540210360703c0c00f03581d80740c0b0070501248080c0d0010320803170569800190840c18060002010001503c000410448041100407030095049940b51070381990307820020625081542c2c201c0301c010380e15481952940c41042c0e20f0f0b0180c011600604000039050905841008010b021660064100003941d40b02c46002c2c000385225000381800461030385070030400b4101210103440700001b8580b0500020405000c005036000c80c040243e1010f90b0140c2c1e050740060301c035005540ca4146104001c1d801c101c0440480404808464510785444100070076880146c1d00c4241c4884138290071050f80030005015103000c121990304541e210040d10b00854072000c20700d050301c0d07010409403941d0b400040d000549a0740040c4443d070004061802908500306480020780312034061060604011560004000807102805004002000100880116982d03000c2402032900603c00903126246051503519 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 363048390 1250 363047140 363047147
    0x50106030513030e040b031905060402010305070c1e0f0b0a0c080903070809130e03040303090612060501080f0604020c030a1d0d0302030403030c0602090603090606100e010c0f1a0c0d0b01 82
    0x181d1680f42e214100c1c245800401d220007011407031125a41441820440310802108004007145540202e01038080d5103010300015066a80203404801000030b8452002e0109105000300b904a0101d41c9050b1600b500c0703400c02e5005e100720900042c2490b02c0400c28404004021f0740818100c0304907481d0b181b0f0380e50340c68030140c2d1070380510700c0b0141066030b00f040221014a00341425410003100200c0002c1c070b80700e03c103080a2954010360022004a080d0307890501a10b5048071a22011034a0500700740169400d100000f088440e0241000406041d2070300850b41c50380c3c0b5a010b40c0c0c8070440b0b84e400c032500c8a802580c003d1a0070500741c509200840d02915084507810a410541070030f0383c054005600e030620359501202c80c2c0000f05420388003035901348000002c681da210003c50003181110000c0265040040404c030807030741082c880d002072100c1803e0078940c030b07600310720f143c01d00c26000003c444410b0b505003400b0b81d40543e40851015020789a50070000c0e80c0b14240060154107075500c030100310b014602c00056 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 363049640 1250 363048390 363048421
    0x1103090c01080c0c150c0c01020a0c171c05040539120c011206210636050309030601030807030212031005270a02031b120f13080d0501060305 62
    0xb03108a4114503c12150170b176150b100b03141c105010302180b6280c412030500721400c903040100c10100207480c50a550040c41001030321400130b80b643e40c100603d04402917185082c04910000080c40454560b030028027400810300c0f4043c840d19401d07000f5020740b04206401050003043c546100c0361701e4040c1c2d41d48034890170a4480d20380c840031070780000e080c0c0e100e40000540d05203441e100c11400305034803200041010a41d0440e281e0f060414110380096420382803a041050310701c1c5490440c40902d200c00e030250071181e200341a00e58030000c0074507985147d00030309040c1c0c254400c41d0407558141c4154000001003052101c000e10380c0d14001c0d030a4941c2d01c07542d01c01d81012880300361558810310084110500040c80d00002c034540300c0b4540c00c5140d4100c410030002032101c010480d0b8402c044c541c08010040f0b10465103030210318109982c2405490400042e48510b09118041d142421001c03103c40011690380d416440000e41c00c1c0c01240c0207465030100075620015110900a50001038101800318a0340810000e00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 363050890 1250 363049640 363049657
    0x30706030e1209060d0e032a0f240619030503091c03080411010302090312091c12082d06030d03290a08030d09060c0816300f0e030406051206041103090c01080c 70
    0x111140c40010301c1c2b0f0306140c000040e06180c0d105452041c1e00c00c10300c0c20131040c0c400a500c6140510340f00d0740803200300000c80340f0f42c0c0a4a1031400382d16928dc3c0c0086d0b40203038800d40c010ba2281c040b160306200c40004030024000d0b0001c2c5034062146d11010071000000001419062400b03c032480310400040c0108080e01041c40c0d801404440c14003901e03510746026000059011180c8900555000e0b00390b00f00e01c20118050f9490050301041401b4092a420141321411502c1c4032800e007400502d400c1c80700400315050780c1c074500303840700c42400c000042a913942103e5002840780e80d0860707440d0300c01c0c81c0c1000c00800b40340600b20741891526200c4110180581035140c07162500104009603801003010070341d1070090701007038803052186040903588408842c00d400350719070700040000036040000d0401b50040703c801d2104041542c3c410301003008055440403c540d0001c0402160052540383c1c800803e020b4899000c44d440340382030200401080200020384940c905209070fa412249880d03150702054280b05014a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 363052140 1250 363050890 363050923
    0x503060124030b1f0c05062809140d200a12030513020a0609030c08072403020f040b1c05090d030c020c030706030e1209060d0e032a0f 59
    0x1520754041d00992080440c090058000d0401a4100c501c00140052640200e40400c10351001c040c00e10804014480d48030502400c5c030009010011040c0004024145c0280d0007903440c0c2410301b0411007100089030040d200002143c2401003400006846011072088040340c0d443c007170088107940c44c400950400d50707680016071404400b001541c201d01074500103001c0140d18100101d1940144c403403d035101c00500140d603030011150306514103a20750404a6202800c254000101031101c1014141c800d54800c42000f00000019540d40081d8085e01400d81c040324580310108002440c00f8a15008202d0781e12a011940c2a0f1036600c4e8280f030442e40255203d01d00c0d42d10070324445816900941c070190900c5581e0040301c10030b11000c00020b2030150290040000245c481d005180609801c00101000c014500701142c202000800070178140d005090a030441d003916000100a01c0c0b90900441e0420540c045150304c0785e00d40b041d55000341b1070304440040014030540403603400d031030300200c2c40070100c101211 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 363053390 1250 363052140 363052199
    0x2070f021003021911120301080606100c080409060312020609070306051f120309080d0503130303020409090609021c0c050f01050f0c010e060c04050904060c20060105030601 76
    0x8007849040c0508141010a0503801c1001e940c40050241c41100c150309a9070780d0703100882e03951008908003600c500110740724480510060120480c00314445600c032009842c0c0040c500740031031003110302001d82c80018200b2440001c003c1540c5400360040f0040c0d9018102a948405e00039000b01eaa032003048501e0a02038100c8041400060429003141d60010034106002c403401106403680512104140c3c46005486c682c50010001c054011058100500a1502400155802403409481c0780f10080050925000e000044d00401d40a64140e0340075009620b800c0040040d5498404000c00300c4000a0b84183c0e80c0b82c07a110a140e520b01c0e402c0380900e9100341d221140900d46030a000c81c00c030280c10018103100081c0151403c01400d00003400308520440c0001c0340401d00d1074001410050003604d0031840c0035040105200c6074450356480d80d0010760007100050001c14640003151151240411007121104411a070800c01c04001681410f07200c080741950740e5641d8880c00c00403080900b0004110416599 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 363054640 1250 363053390 363053393
    0x21010e07090b031611030409140c0702030706050c011803020f100e2d03131706070e0607050705060c03040306110307021903090308070b040614040201080a09080c1c1202070f 76
    0x1120005002c602c0c1017402904d04003540356800c0d0340194010001c02c6503a0304007100b42145400e40c05420030000301e030482c41c00c1001c1d004aa201c1d00310b806000c040c01400140d0080801c02540311700510014078296014144480c50000d403640349580070710500b8419040440302e0503025104081e9a21200c000408260044040614480244980f01c652011040b280301414a4041c0001c0809406800c1c8a100305403c5c0509180b54050403201c6400035400380c801c0054640d0400e942d2510000112165611410349107419807a03c41207400490304042c1c003007100da034200c0001000d481a00d1141801344200c0316900166452400700700e5003d00182d01442c0302407078040c505019941140c1c02854803452454490312540c995a01c2000222042c000d28020401441564410864030001c101445402030078140c00082100d100940302c481c001d41d88001038810404050121820414100b0903600840710600150180700344611410380403a240d085114402040343c400ca80c1341a6124074242c8155815 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 363055890 1250 363054640 363054661
    0x405090c09150d12020102031b030c04030204110706061e05010206040b06210706120e011509020f07020d05060106030c090807150c1a160905030604080f21010e07090b03 74
    0x1030480036422042e01c2c2c0503d000310780c0c1000002e0700e01c0c00c150000340c0c0c3c030300b012080029190001c8400d0050000103000740054102c1c000308582c1105e0f01203d010800c0b10050811140c40e1286440c000c2001d03281c034400141800000f1307000744c0c442d013406c080c1c00b100030341d01c40c016603c6070022030b00100240d100100040480c90042842070f451a40100845543c4448c0c03081d151810384a6007100740491040950300408401034040c040b2001c40300c000a22900c100442451000d1696008034212a500450040c40903020303441a121840c2d00203152114610329400c00507140c46d021b018040020341000111003403140070f40171103821a4103240090840502e00704414071450800040b08081160113001354001c240e8080010035040c200c0c0400388840d05000c5005011140991061400d00086040c10052540c01180480d4010340100c81581e40d0440114540114400c0b1065141111501620401481d00e072600c91070580c4c0d40fa9480f860375889000081c0c9074500b00d84505030700c681d000c10004118000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 363057140 1250 363055890 363055921
    0x31b03020109020319050706030b030604171c050411040203010e0408071b080d0909050c040b0706060308040e070306060c080a0c0507030203120901020c040b01020712080c100504020405090c09 84
    0x6840009901540781d80040e040c0b5000000b81d8541403240c038075800500401f8031401004000d6800c0030040d031900340012a40351a40200050301e82003180c150390388400d240804440b0209500c1e074111001a880d1900d8000401c81640c0986040c015030680d801542094401c6038161107920510100541c2d940c2d645000d1684010012a079124504202c4800e8032010200d42014261510161100c0303052002d00a14540e070640c0711480701d07428201800b1803824150115020ba0b03144e01801c0b6a03c1c160741c1040c8000c3c1002c9d5200a100c0c180010b000500004d20320011070081203195001d12815507200000c4484e44043e480241c8140c85c00c0100326030b0540100c0283c2025482001984ca1035952030300001d0030200e842104212055000402e03445c0742d80c0c18070200d41103410403181045142c02e0500001d41e210410700814400615070100741041c0700c580419100395071000d0b0120b43c0100ca100030b0304405468140d5081b8059818440441c8002d0004140d40f41c044002802043d41903840c40081c007040c46 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 363058390 1250 363057140 363057143
    0x50105012c0307120203060709030b07140f0403081e030408030f0a180311150903030411010c120201020703090b0711040f02070c08060f07050c0c0d1712060a12031b 72
    0x360750030320284464800b032080c0c50081c62154202130701c19038140189800c06c080103002ca01040603d001c03d100103404407003089e03084071440c82c0089030382c1181091a5100d1048040041d403d88001ca0008200203488000b4080200c003a10140820007459400396101c0c081660010925201032000440c40700d50040c1c400da0003a5151404941024504a07c118403840408140d0006428503880341200301c0c1005034100d08051512000105c0c60607040841e1070380800350005240459800211040d42e100d041441d1000d41c00480c00d24101e6041140030b4000d61114404401003100f6020000e0510240b1090b00d506503001100308440c1d620b80d02c01c1200400c420711580502550902180010440a10b038190140046000815450038052820000000010189410807404004c0e2081808002c110584a04d0003500c094081c034155280c0407001c51070200d14500e170344c41d010030300c007010b480d541210314001c44d01511000003181c0c69030b00b0b0049605803c003001c0d012607482c00c59130b0766040030745c41c0810409 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 363059640 1250 363058390 363058457
    0x1009020616031d06041202091506130e010506030103030e040c1808070314010207050d030509071503050a0b0102010e03182808190b040b0601020f0601080307110405010501 75
    0x28101d1000c90440001c07480540005448580000c01c400c1c0030310700340301440002c461603410146451b40c0b04d110200c4800c0020302400c01d00012a10301d00039401e04266612009080e07980b2501c10f4550344aa10840c0c0c800e50f0000600c20340001120b09000c81240d05a94240e079414a80701d26003003d000c01703407041d00e20040802240708101200d00d0000c1d03506801070403c40c0b002d40034507450350401c8190001c20402c1e464503644100a643c0015a0000f0b404001c0f60381070402081554030105002c0c1044150351241c1062034000c034000c1142da905a2195106510084040042401006c012803c84511011400403544200440124140d0088004900a600802c0c031801c1d0540342c0e850360f61301100380008031460b4000d40d005200d2a241884100641208041c0300b022503541d0717440c0e00112440240000c1d0103400f81c1c0c4041352040c0d1081c040d079280e1049008c221051541d5036400c0542d00e41c02840141d40c0101003070344500c0705103000e002d0581200d4059448440b6114031a020352040362950046101c003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 363060890 1250 363059640 363059647
    0xd0c0207090f140604020405010c14030904022a0a03120f020702060d060f061706040504050f1c0906230f1b150112021302090609090f01080708030a0210090206 70
    0xc046960042c8400c0024100020403000010f201112450402403d51442280180410b2110340d82c404c00520030150001000f01d004508100d8050442c815400c4203500a80001144910815005807003144145621070801c03c1014071100c0b59202d03800284001d001401410781400303e0700e05030300031030420901d000005280064550002c3c6e4140d1141058454a94440100300042a6006d4022005000c1400d011212106406d03500290800003040703180f01c0c0e40c0c1d4030f0108040c80401c1007031200001c04442100c0200340340314180480e01c5080d0f4a01400125288404034500c2d02c1001101002c921020741a5000c0d48440c0c51068150070000b0003050440c01803103840540580d4017403040210f29944080c20403600c1d480012488904140c2181d20580c2c0c100100e40d0068230785901e980d8403c1542800162602c0344000060781c10f119071104a580420701a00380300071000031f1141c16040341c080790112120b01da03031b50018a0302c134003031900c2c42070140c3c10a40e14903a00c1c00183d040042c915100806842c034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 363062140 1250 363060890 363060899
    0x50d1d0706020c0a030309350609371e1406070c020609100318030203030906090c030a08030a0615050d0c02071503091b060f0206011a0d0c0207 63
    0x900848009214045034008601080300c5601404064003090007550441c0000e8110380300a0222409441b46080300480001e0710340d6440c011854070a08130b49500100124000c252085555840090f0380c0c0c0a400c0c0100b03c0349921481c0e03400030105401d03050505c1c10f00200c81d4260302da114489034440548440b459134503a19201c0110380400c0d000240701d490003144000004502604d0120020054003d10003010b8409015940700419103c020000701c07401e121902c0003242c00c40150004100d20030301400440c00200c02c258000c000b45102c0c10122040707039126aa5828440d940e144500c045903010340100320600e000c101c08034000c560200300c411003c15842e03a02c0f20b0580340030703121030b12060005001281c00f0b503410b030b014016024000e0340d07840208860f83c144041403910200038510301d0213241d0759104500130480480540e1480d0008859018416079a40c0b02c007400e0201c0e1a2004401405203000105000255030040040785400c08071850800a401c4199130080c20035100010130340c46048000113 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 363063390 1250 363062140 363062171
    0x130306050405120a09031407030f060f0b060f04060201051f0303080c1306080613090308160e0d0804030c080312070509010c0b010803190206090c041e0f05041101110607050d 76
    0x80700f0342e003944c41c6070220385581008a0711600e1000310752071f0b48d0055001080810081701d444d039916908280000307041c0528941000007460840d070805d4000307202003003140ca90100c6801410403034100d60003d01240d41c61180c0c2d080d0b880103e0200c51054080b0110510110344241b009075840382d10101b4152a20408050301404a0b11541c801c10004440780204417241c1080ca444400044a41d4814461040c139554003038090000100f66586100420200e07184041c17180f040d1094880c809801c081c501c1d6442d0400540641c454017042e03544400300800002e01d80c200004885044408a00310f1400392100403088400e81d03c5060503034102b05803900304402140c034040c42c2c40d00030070100c80290340c1c480401c010b400d001000700f6003503000e6402080411a4420001c6007003941070104580c000340d5401c0340001c0c1030528a9408002c0c0108c6e02c0e02150300c2105216034007540c003850240c052041441c0e400001100d6545202c1214600c5410a901147c44280510098138102c0c000f01c4020170b500b10a00c140382d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 363064640 1250 363063390 363063397
    0x90103081b120f03070e0102031207141201080102030f180615041d1b0d03023c031804050408070b0405010612030e1e01021f021204060f0c020313030605040512 70
    0x43e11070340400000d0000d00358001d144d4100141007800511300784250001c00443c07004c0300410f03410600083e0204131142260b280200d0300c86034401c4120883e10758540c110503000f034008035040982c0070a1400465500249841c10400c90302174400109159519613000080401031a1700041d000354503082ca401565141000b20b401291002d00101808134081400117258450070060f180600001c021308008258040381d0710520300402c6003090b42100307254192941450700c42c268030000150300c212032404e5103004001000c81461031955180e58000d03080400c0110b410a0300c0040848508200d0307800002c4442c44c03003a0340035018a0001980c29a035070404040720305c01c100102c000590300d00040346249030400058004801104032118001c851f480042c0d59403c9550350381d101ca0102e22010f09680601d90111003a009100c0310341c4007503040030320340040a40315460010701031a0806280d4403550b44000182c3d2a10031a01d100c001200740f540e182c0000400000e0000d8407280031f556200d91040a003103005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 363065890 1250 363064640 363064657
    0x328020a0509100e0f040e0f1c02240105040e0a0501050705071a010e010b070c0510090e090c0a0b0a030603080301030305030609070c02010804120e090a06090b090103081b12 76
    0x81642c0d4407100c1c000c10518900451011042c402d82d083d103542a034595401c81c80d003000080c2c1d00002c0440b00410241d190039507030f101c460450b100340f00039855540da149084a015020035000c80d18450981428981d0152040313400d04803100c2c2e00d10040100f0f00d45508051120107099041e1440d04119071540307403d44a0403a1200b02003000020388100300040d001c03100114041c2c01614a400e5410b0411243c40075030180700d002c4080d40c000c280001400002d950050050400030300000300c010246002602c1c011852254104084961000650b106800701d0700b545115002010304d1140750911134140b1440d00300340581020195121408800600400300070f5000e180a40c5480340c40e4508001084034180008190b50304000d24400c3c0780c00180d03002034450b0f40240d03016500c107000282d049003c40e1010640801241d00c4007000d0240305207050107501c08416a5040d00c42400420417602c14007074154020b22008001d0b54042000d18072a00024032826031000d210401d4a00746040e03891840001d030403000a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 363067140 1250 363065890 363065897
    0x70c0320070f0510020f10050c040e10060e0f0d0b090102220305010b06040f0e04150c0e24040b03090c0d030e180c09040504020f030109051b030606060328020a 70
    0x42c18080ba1416400881c540140c600c010f11300e0340a0b43c8221034075078280342101c000407611500840e040c428401d0035a000350044070030b1071003c0e103848045a1211240c41c4182808036246140e01c0b541c9003060780d070401808001510a01940503203903a003903079640009140d42c0141d50709211041c5001207c22900c0540301200080201d030f1810740c02c010f8215030800301c00c503100d140104030403c209100d9011000841c1c5180b49186400d50b41c60500c00b440040005001e06454a000344000c1d5040d0010501e085c841c1d800e896560360140c841c04c43d02003c2d01c126801c0720808106210400c54000708800955000c290030081d0350100c0c0b00440420105000340714114040351a4031456090307424064a00c0748108424000320b034181c00c1c19a20b0724618414110054011074503000010255298034404414100d0040c000700440407190815688509c1e199003503492810000280e10603501d00041d46501483c0c0040405d03141da107031040c0d85051800301c03181c2c003601050600a03c61300c444c40340c40507144482c240d49 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 363068390 1250 363067140 363067169
    0x90a1d070521120307020102090406030b07030e010b06120907211a010b030a020c0c100512060307050120011407120e0106152316120305070c032007 65
    0x3000400b0b01e04000c910781c6032001c05075a031480c5400003102d0a420241c0c0d03103003c0d56502c451034100d000e846100c00c0d072900181403c20000400400a4000c0c0c40fa15440d6000c00c406009a2186420b0315a085407042c0d015806011700c00c2c141c3c11009049403c60038880c03c4401c00b690f10501540d601c0280ba02d01c510b420701c4a2007040500841c603000341c150101d0100300e041c1a604282c0c01d03940d00e000c091710740c5211076070100d505c030041c10080085181000006054100f41c58802334010032a0307101a294a01c1c01c80c02c41e0228940d8100003071a14180d480517164000c020f5174a41442c41c46980b4000d1018844d03403104001c4071200c8a106442d40600781c41e03624598041a00c01e420001e0728901d8041c4496a858131800700001c9103061201c3d82c0758081d92414681184c6403402030706410220058802c2c4503030300082c4c40c0800b010140103460141d44a01060600f0400407a03059040b11300c2200c0300008540a204080d000a01c0381682c00520740d84400400400014034807071350b217071408a4125000260030703007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 363069640 1250 363068390 363068399
    0x160b0702030c12070b0408070609060509030a030f0204080606041e0903050909090a020d0204020307020f071202030d053406050f010e0907122d03050306010305060d050a02090a1d07 79
    0x1d029080202c65440000c07440d101c00c41d5917840c1e00d040020805894a90b02080d03820401c80c0541000700e5403900100d060140e030400c0802d4944a03807188050401092402804d038145221030b0094400706d5581c0c01c0602146d9507a1414000680103030240001501d80c072510a850911007481101201e5010f540e035981c44511140902c05d60312806840700030300da07115408443c010b980b010f441070000c0380d05a070056100c2d00e40000c140d02d004070110001c020350084810204100313280303610400106000b00c0843d08001e488090951f4a88101000e06a4860641c040064210029412081a842c603c0f82084540500391540c8040740d01c16250880740c0100d20b001002445030601c42180c00c20b0000021780b00c880c0c90404007003034810080c0f034014031140100504152514500183c80f181c42d0222107120948006449c00400303540c8111840742c003091506003c2116070800e948002c40b403036400130003801881e03110340030809030384002400360540c1c2d51214900c06208a40c5195606c00d0045403004129003400c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 363070890 1250 363069640 363069643
    0x619030605040b13090606050a1403060a05070519020703020414040209090316110a050a0e091605010f0516140f06090d050316021002040e01080d110d0302160b0702030c 74
    0x31503011030b20036402c14459840c030b5a60000280c134420b42c400f100090740c13003040ca0300d4000b40c88298081d50b031222032150002118040c80101440800084082c0e500e1542c5946a540881e1400e94171940010000d0108414103114000742810106083c0100e5040070782c2c9900060a842459100c00360008011042c441181015041250807203e1500078608040f050744d062146004518800380070f180b200502d12400761252072854020f48009042400100d44691440300410b0045e5068902440b8000d0801508215850840203850301651241c05580d000310044030036401c0b0034100c00042203005800e500041e05400202c0c0c41c4076600d0068038460340e04a070000d0070020010140340b0540c104200341014181e009007120f40c00307502d145c0c60a840d034055103422884d00003102ca19000b0b40d840081c010492501c550300480c101ca407240c003110050145804c040300c0039100c152075614183d00c06210b482401d4081c0e000342c03004041850004100da640768a4040d0402804c1d81c4820150308002a40c40400c01c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 363072140 1250 363070890 363070901
    0x6060b09040b0a0302011d040207020d0602030717040803060d030e1e03070605071a040503070b090307060612030f1b1e0b0711152806050f010207081509010b061903 72
    0x32280000c2c0f4034690303000a00140210941e60b00c207031040c1c1440d10f1296842e0703419102d200d0b40141405080c400c052420304002e41c82641d603907011442d480c0c0354180142000c12440e2107264402085421074031036500780300b0344101c24602201840880074a264858850002e410004040e10070901c40e01151102414200603407030b0044000c00400304034003c04208c1d6202c080030803803003800305200e00390b4941c20041c0c00d501a488000701008040000e00a10190010142c100303603020744820400241d41e00b42c00d41c10310128000050101d020105240ea6640c0980444911074501700401400c0c21003e50710442e8402c948840c2c0c3c070800403000005024090300180c0194880703020708191000e61140002e4990b254019060701100000300c5000950b050030310341e80c80c41707021034480761f5040016012003440c0103840d06004480c01030100220801940d88000f0f0024201e40460000d01103002000654803a63750004045108643d22040503200780c0c0c40c0d19000704080b12503c0e0403010403800480d40101034030b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 363073390 1250 363072140 363072161
    0xc0504080a110909010606050412030e190510090e060f041112040b010602030a020703060506060f04030b04110306060a1a040803131404090b06010305070c02030607090e10060f1b06060b0904 83
    0x3e06d801c2017030003074a40220440b415107030440340c52444041141703030466460039009026a08051006005100c045012100c80281e4138101d8880c5074480861800300c80c5030a841c0300344582d5180b0900410f0550604190605204101034004501038400354480107891384031070884030780803000c1d20400c402e011101c1842e030b014003a83d102561904020f044029903801d1a8000030702440c0c5d84502090a03a900d4008882000c0d0720b2140071f0b0380b210b84d2030403c1d0250700c404031800d072014503000e40507000318580880d065100b03110040442c0c0d1000c1c02c00000044905201080300a818810400480d201c40c0401c0079241003224410011300040c00e260450341e60451404c80f817401541460303400c000040081f1060743c2d10120a1034001030690742c0d40400c8499405042010790107004140a0040c070551045110090340c401c0e018030004c94450314121003042d6907502c00c3c0c00000f0840542c40224a110300320b203051442001c50036220001c0c440d1101412240940e120020012002501680e103086c54050b40b800352 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 363074640 1250 363073390 363073393
    0x190201060504090c0b0c1c200601050109140307171c1b0311160e0703060506030405070b07082502010f05030f0a020d09141510031101030c0504080a110909 68
    0xd80783d96181c3c0d02c81c094a0080c4a80f60314042080020004d0400441400d483e003803034040c9428080410140a400d0f003a001840d03642810a007138030310000e001400781d04070ba906075a400c03907040c500a1262440c052007500303190306000d90000060241200200403018500301e10113084042c51001b00f00d030201d400d6a4040d0140f0404001c00c6011300c7d0f84400041030786805040802c100d0b4590386e2840d081000c1d81026812040f0b080307030080307508602094803511400854404120160301c40381004128002120014401c0d40b180506008002c08013002c2d1120500c100c04460130072a409420012082c9100c01032221020720760000030039980d0110000c0083e1485003491460340c2000568211505d0000f4018200c4e1600040d94040c0540182c0c04009401e4110500ca01d00054183d8640d40300c4260042544003403110310085036189055024450440b640031442c90714100303100c80154094102030354064140a011b010020303a005042c0010030089200b42190380c00302d03402a00700001812e000d0840000c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 363075890 1250 363074640 363074651
    0x4050408090301140f0c0306012f0706050c070504230108010f0606080405031207050d0905030d1a031c09030b0c0702011701120201360f05150a23190201060504 70
    0x70803203a1106604103121101595071fa5852000603070303404054034000200300d0006a150301ca8070382c000341221012003540c0f007550101695603e00b19680d024206a8080c540c200e0b202c10011890700d548810b03408000381c40b082c07444400444400254002c01d038010802d03651901d01e00e800c1c05600f4460740001c1c00a0b401d28440500f49601c4103903403400740200442100b10200042000940144161901030070800814840c1c2c0b1480e01e8a5030303c0342c2120446043c5107081820390060103451040c4500469405001858484c0b0280c20007000f07060141c15000c14818149000700204050070b131400e1044a0080c03a10766620003910004003441e42e00140c0390401d400100050181b44062150f0411850f0246000307096001c3e000b941702180c1d603442c04104c841500807081042c401000d485c200e401c0b1403403060000c030481c0d40c2c2c0007807282890b022586100400e60400c0300b03050030340c0224641d0024030703e8050344001750729010800c03000c1070703018240a42c42e842603100d4072003482e503090082034054901690706201 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 363077140 1250 363075890 363075901
    0xc0607030f0e04050138181206070c120908010c0503090c1e040e0114040501090209010602160603050a15060905240301060e06160c090c0302090f01120b0405040809030114 75
    0x482c11003c500999180c4a0641d00c070710101e4a0b00407508446d050390b0503982c0768584003140c0180c0c0152107400e40900350000d074518001c100410054442c0a0395210b0390b00032001641d540a900c2105608401440000310700850001000d124a158800e000c0d20f84c15942c0c1000c0c45594900010350108900c1880d60700ea50351a4504112100b1039000c10a5401107401032540b010940508480360514065451040c20841486015040f0645140c02038071402d502d1b903225207040380c48008800300d1110031882690100700c1244603920495115200d0a0002444c0800c6201409400143c1d4800f0000402c11502071155191522146402091a80d0000c0e0390b400a01382e54052804140328040a2289200040d00951036101c1102c5901c1401141c84060803c64030b4042500040750044c41070305413070300740c08400f664043e1080b500780d110003c086a0b0100c1d2a8401190007900411000711919102c484041030f507180d50081c940518411460b0369110001e19040c54215180442c580326045151400e008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 363078390 1250 363077140 363077159
    0x903080301350a03120b191401080c2703030310060f051c090c080f060103051b0f090709080318040c050405211203010e090d0e03100203090c0607030f0e040501 70
    0x1c102da81402c01c08a105d1a1440080040030440d001642010990310001003a81c1030741c1140e02230382d600800104110348403000444606100f240c285000c4003082100c1200311412454501225911103038405459280300b01003411500700303079072600500400d400c06024031900400544960041850090b00340030b847e1000c1032031902440f841109165039040000140102c0c1c0d40180060151101100e0080c90034490f1940c1d00c01003448161450b001d8948240f041c82084040030880040080030381c503110400d402040300943e13001d8400018441c9454001803240424000b030990800300e82c9200314070b080c0200500c001e0f944284103030001c10500700b00c10b00881c0e8442d042c14a07440c0304007550038507084000d06698502074a10b4a03c85071a45e01000004441d4480144248105d040d441030317a0b102c0d07842020a552410800c1166075054200b544540303000c6070a58040e59100b0307588000c07510354642c404089452071b80081420740015088000c408003240d0454409400d00c002680c003003003958581030f102d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 363079640 1250 363078390 363078403
    0x60e010903031202161a0a0b1f020a0203010c030c08161713080403060203040615081207050705100e1906020d050705031e0405131b050a090308030135 66
    0x1810f0080d10742c41c8503000c0e00c00c0d5041d01c680b06483c1e600803011030450705010340740c103070000318200703880302c0000008110042c1030003280c62024014042071f000000c00c000d0301c041c1400022016003184258122840960b40c00d00038400c41c198207440000759200b41c0c080080c03904034000c0c03010389044410404089855884010040400754500e42c0c2980768482c5041d81c0c0a42201102c0980360a001080100a10620740e009500440c4501003c10051040700341e040104002880381c02c01c1d607013000c68840250920785009060b818480c4060344d5041d51204000b07508401525180f600080e440003116500c0e00300745814400890640ca414a2081d10b4084001c1d0354100d01c4a10303008024000c81d26008000c010801e850519000c00d07100784045680e003010064640080c0300d154401c0846c10342ca801e0010303981c8100c0d18a07402d01620074072035842d00d003404d58281e40721101040030440746940010204800c50003441c0600b0585107000307c00c03141c0707964040403d0180d08480580c4640071400c0c503080540010304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 363080890 1250 363079640 363079643
    0x507140705061b070501050a0f230402061b0318010e030f060103030e010c061a031204050a03080313080d0203070206060a26280b070c0206040b1e0c060f01060e010903 73
    0x1240e1540c500d80039140f40e000d080c800030925800c01e001c0c00540c022581040602c284180e804005895140208601540700b00080c1001c032003080d0045009820400000e080c41c410342e814203c0061030601040c1d00d940e11004030304185108851800c4c1e440e40c0e110491700d400c0c800403401850503a0080c804951111010b110040900002d441c00b01000d9020700e0100a61907003181c801c00c00300030052102c0007600c0407000e03014840d000b02010000341154540c19101030b19009071000625508550b1844010340c8013030584240d03424001803407000181c10100402d102401648003503120b00b4031000103480d008001d07052602c6000e603040c080c070011041c2981d408a042100d690306035001c103840002070a00c505000720031011102803030300e800244070507030412103941e114200402d145c2e541c50600b1a0404055180254060b60800c001c20031049040c000c0c1c100358840b101c001002c0c030301c0d24150805d00ea00ca45080c12140d04550200040d04076500e03c0d96004042074209021103407010b90000701008400d000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 363082140 1250 363080890 363080911
    0xc1f0213090b0d0605010806040317070e041805030a2006280b270a05101701140106091503090201120225031812050c06210406050714070506 62
    0x110701c240d03a1541c101200f601d41000081005503111880d0640340c0008603016000b20360b601c1c0140071300407238110f0001c0c41144a41d603101c1030403001804100140a42c104402c2a092a50256002040c0140020301d500700680e210101c1c200c41c50040c07100300160407c00c0e2505500000c0400625038000203440480c2c0c03941d07011a444002160b542c03c0300a26803840c4142e0070130050589051280da8640300060b1042000842034010354442034a0b1007540e10885818000754078000301000300f400141d45501401c5a010000710706908103004800da000d0090340200d000840140040042d0409484203a812041920307050081460940001e0711012440095581a030782c00141d50b2000c80080d44100c2c10a07600100e4030915040a04001f01451114a0b00400035141140000790700c440c0f80e0300c070074042c0358000040e14241c0c000d0030410441f034101040543c4c044003503501c00104464140301c40b41c03040d445114002424200302000510381e03004000d500150400170011900803030700000700705610004804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 363083390 1250 363082140 363082151
    0x17010807050d110d05060103030306260a140a051c0306080309030606010e0a1701050f070813060504060b041b0909022d040b0304030210051302010f030b0303040b0c1f021309 76
    0x140030402030f504c00d0320003030320600601300040201343d81500858112880400380ea2144048241081c803400304c40d010064481c3e22003e1034500241c200402d0901344a862010780d1004005034649a0030701c05a009176100c40f504043d00003008641510441c000741001500550038012450080317691924042c2402d4144949240a40c1d0240e03036650905001d0075443c0300000d654498807400340e000c0d203000e691340141014200c0019444500c600c2e03440d841011801c440381803800e5a40c44800090501501c00e403000340d1903641100c45c6444174000c2c030700d2282c044070350104d20046214005001881d150000440c640c010000c0036640084a00070916a001c03104019a2500442d00f04a41e50b11655000d04401c000100421040c183c01080211410300c3d864410300c801c4e80c401e981d2242003800302c0d40c000d020480d941141080340344a0307070140c2400180901181d207011b40300e025039081c0e90850f0742c11024651051198030b5425086100310400119624415130520410b4003406440703c02c140a061010380e0b855 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 363084640 1250 363083390 363083423
    0x708130323101d0d02030301030c080303130f02060909070810150f0e030127170703140702030a0b160e0913030503040f06110304051c0905220c17010807050d 69
    0x41d190a203500e003101c004c69441422215010307480360024807043d0380c50307054035100041220300030048071703c25020710a9500b19545642da0790080c25490352820390b0094024098100661214003605011340820384401086207080754000805c0603254005404007024060506c0b0070541100c2c00b951580c1c0e00d402c1034940c00d6000310210340103007000b06506d403413042002001054065858100c5000700e0094406855502c00045006844d101d8840e00a000400a81140c0d04214101014101441c40141a00d841d03141076142c2a00442d4241d60305002840e080814510494004119800c04c01c02a10b1f8a8001d14001641c58080b00a078000a0188140040068100a44583e4034008660300000403c00c080303440c1c1750624280c00495040f9542d1058501c4031b5099503004030001c4a909217075135162006c905050070f010640310328415804140c03c84100c0100022030b00d01403402c600c4455561020581f41200c00c407006820103a004c9490b80c0c00600c0b003881603881e651121608a504520500691402e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 363085890 1250 363084640 363084671
    0xc1203070b0f100603060503030405010507150e100606140a230711010e010203090a03060b0102100908090102070605030907030605070c0f11010f051c11070813032310 73
    0x504600402850300e0301c0c00c10641054203021036000e03e1807002c3c0c103841140c0b41d90041e02180c1343c5000d460381c580d0040c0410401c5d50f114100400c2079038891010f0448145080480005603070700701d0a000d0795900320740034460b0258154804e220042550345008440c4101200d215112403150600e00c0d020000203091400381c2c140110f101d4040f5001d131600c0c46a03140041e007003110b40540d0745c8078024009050086040190f40c8000160b80c0b420304000c260b40f044a156513200001441000d25060650003401c420701031600780c0388240a40e1a0254003e555990f24107000207003400c410760021030920109005000340107000180c014140c0c3da04c41c41c00603d580380c841c0291000e59031014020201b8500300d10020420444542c3c0101502c42078a03000c00c80b4a4510040d96103000711084082e4402907040940b240c0104d9400c40180c81c1074130180d032880c19180e51280d1159a2004840d6048415084410810044070224210b0102055400c581144100a8403141ca8800c001c038080f01c4c2589401190030715410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 363087140 1250 363085890 363085897
    0x90604090c031b0c0b18030a0e1f090801050601030504030c060911060f0d0f1a01180909140613020105040302091b0406020d03180b060904080409140121050c1203 71
    0x1c16030540310103040c003440011302d2221903140444103901c41501007100072003a02601c03207140d451704010b58104185004201c035080c0003120f40c0b990040c0211400c500d4400c8011a580d00c0551540d14080c1d500c0c2040030b014290303000544240e040500e410100404294030180308414941c1c4001c001c5507500b42801c3c6a205044158000c6a122100090305903203010b1100c020441044029400d00240511620340d0701255001894109000007041c5070180c0c56110305018032600005404440c545a01c46a40f072080f112800c00468075410581c23441c009003a01000a1540520859110104280d1f1540002e00d10300440c80024040e100200c041000001c800540545610360a10416156659154002d640e6040c0c1d921000100c1d1802c03045100510303420001504203500540d40c0c40e481e407185001e03c443e0400082c001d0704c0038042072101240ca0501c5002e01d244020380803481c128594117003c0c0480504c040100415422510071129000050700450850210001290444207070590211254194030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 363088390 1250 363087140 363087161
    0xd0903080325031d06040201050d20031e010f140d020d0609081b160308030c0f120118020712050306030a060e0708151509130b0708061302090604090c03 67
    0x42c0c4801000304220f41c10f41c0480c00e0315201000d081c00c02c0d10340075240c81c4c4414094401a0001e003041007075440711381258025102801000c1009000000386e50181180340c0c000341c039806440c10300709040b00b412009049591340074042800388141320604c3d210007410260000d440c914092954140040b05540d14030303005400c0c07560002e40600c01a039580c03600fa1059880300708070003034802d006410780c02020400200c0811107010203003024031803401c585542c012034000070048070304034004100407292090050043c140c1d03d60503035009003040d41840d41c1c3c0c500340003440c118030501901c1072019501017040e450a004010200741011036480c1c48520101e8208000d01c0409452541428003401e20561300245040031685404151b8080520704c1402000070035041c0c65041e05d0241c030000c3c0034101c0c03030080080c6070006d4000c0002ca07103109041d0b691103100302048070650013050101c0c0400c0000d00f050041080c14202e258000c510b0f04282c1c400041c0140114090703071113040c2ea2007180249041c003d41c400c90142 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 363089640 1250 363088390 363088441
    0x6130e06040b040c0603090201120225080d0b010f0e130b0a0803030a064509080903060a0b1309081308070305100c090303110106270e0d09030803 64
    0x240380034142480440d80c2510112011348403042c00080140c802d200314241e0387d80c1691000d005008114020000e03400a94403803041c211044c0001c1060154040307251070701c511401c1066128000540510101c440030030743d15051201d06084680102e60107803e020300060101d9207000c040314210b0104000340502040550400c030750020114490701e0000145100700c4101c0004d000721611008070720a900d0202000946240c8045414241d818688804183c58100d6160020440303140724545000c3c4c0707580300d0301501c0c0340800040320007041c2014030580780c0c048402c00c8248014424900801d00991440418548031079070f5450400800001100716205950f486503c52001d6171181c2406485003144c0c88202d40c0352040b645004e02c0f070400d80c0a2422424402c0e11040350582c5103440070f841e50802c59190005035565800c02003000707580c800d80780b03807017500036242401101c0245003103a049600c554020100f66205420342c0c0001e65004a406090304e62040c40243c0360b842d50741030307400f0700000e11a501c000c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 363090890 1250 363089640 363089653
    0x31506030907210317131b0626150609030709020408060117030d02090d060f0b121204120302070b0301030602030403080f0708010302040510051203130e07050306130e 73
    0x1c5400c00104401580c0e000d110020960aa007001d0000f80c42842400501007401d101e0310070700d480340c20b0310300a500403880b0040060600442d9100c98802c45104602111840c1d00c0809120499000b80942e03a040710140c4000c1c981016000041c620800042440c15401401c0c45c1d213640c9900d4140c19139500c46030160840395425101d00d50030001c1d40140c00350903198071404000084144104c0d00c440b01480300d20001d107140c80040110b6102a60040340d00c40c1d044002200c100000030024415601c590503030310030010f400e01464040000d4003400c2c543c160032a500600f041c0d61007402600c00c5408035880329654510300500d500c2d007a81002072030f1b40316100c2500c000c0300000c240b10319500210301c1184070307980700c460a68803e40441d1010b0b00a0310b0b2800061005401480142803a0344910342044c0f040400316007955403440021101080305080551540001c2107202100c0c0001171100040c0c26031703005110540ca01008014007900006214030b01c941c6111010941c91905a40b0500f40d41c0d1000d01522038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 363092140 1250 363090890 363090901
    0xf1905150a09141f0e04030e0904060b0a0b09010504050405041109010f140d05101e0612060e070e1b0d0204060c12020715050c160e041209140603150603 67
    0x2080640c04920b0f940c20303064000b500389030039103043e68400c100162000006038104018001d641c1070081c812000d00200c00c0402c0440d0381c942e01348a20840c4182c0000c2650341c0c10380d083c8811541107030700c801d018a005000e030152907038000007900c0c243c8005036070006a698807410700e0000c09201d20030340b0382c0200740100081140c0481030082c40c191143c006c2ca601d50082d0410070300052096404001e003480c0c01c0600c0c0380074810501e4104080421800010141c04160b0034400f104032201644000d548551420307640d0f0420065008074030380004c480c0050006a03107030216041074844010210392144000c0072110f18041100300540d0100843c841046440350303110480030f0451840d140b0b05450b10f00b60400c6101515200041d0031059642c0100d218002a405180c10341d216001070007405060b02801031000201d04207060f40d50010207a2802254a078109801d00d00c5240c15002c41002c100109c2d400203002100d200c0241e20b6614109442c034a5581d07440d400310090011041d600070342c1c070280c000180403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 363093390 1250 363092140 363092159
    0x1091a1b0609010b0d17160204020406020705090a0902091603020c070312120c02030d0209181315020403050d1d1f0207090b100c030c080406170f1905150a 68
    0xb44258640c500804c600e5007104204541038012003070080c10310f1034600040307003100151006091b181c10004241c0400e0b602c1c40e4001826a0020703003010005a0041004000616141d400ca681103204100700b0001c820b01a00820f0071400300800e800d50701298000c21b1000c0c0b40c400c0e811034445409960a50740e0407522813401c5c10074100405030755000030701c2c000324500c2c0c0f18072584170f4050b8001042e0000c41c5001c0b0442508030180d00048041e9501c401400c51900c00142c1c8207030030611450281e0a402c003080703182c2c54800e400080c40d0002031a0030740b051000b440084c0e00000c1a420246003810f04907009440300240d800700140c40c0c03400359040308415481551034684980d95490f0618140c00740d901031500c0d0301c5250100d50180003000e0307100d5200444140e5642c040e1100910f01070081c6040c0946001341d440d00ca090f5030084d845640045c2510080240d401e0703d580403190040104104001c5504220389000741005a6800304407c0ca81c3e10804110040103241612000b604c020b407084209694810644 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 363094640 1250 363093390 363093403
    0xc08100c0c1106370f020105070801030318050604030503090301060807060c0206030612030c0705010f0c031409120d110111030108060a0e0309040e0309041a06030103030c05010f020c0a0302150601091a1b 89
    0x45210f05c4000103c017070060140c140f040e0000e64689005030b00c0c2d618111540600001900c2401080020200d40c3d9258540200b0103140580000d40c3e584a220003850300710b0b5402d44c0301201e140c008200038000c1c26400f42a89010310b0701100c00c00d8807030325000005810302c600c0c4908035010b4440029180031424000c500c52044503800d0b281c0130030199500005540300c0c0d115000c001c0018240d26039070a0400d0014018001c0ea54003d4221310042c0c06c6030401c5071503c020303011b070003011034070100c440322800400b401504850030720003003041c0c15945000740143d5250400f6240c40420f070740361524041100004c106031900181c0007402405050b001e486841d0710b03a8441442540910f0034007080400d115070b849084011200082c119900c2c680c655202152016001c1e0411a0300d5500c0ea2000761840d1214006000c002c08500b0103400d40825620300685807012800b0400000d00c2c00404000050382c0006682045503909401066450020b4207021251f1283c640402d219401044c02e40452480000e0f55 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 363095890 1250 363094640 363094747
    0x20304210312021303080309030f070311060a15060809100f0b01080604020304030e01270f06030c022b020a0c030b060a091109060d090c08100c0c1106 66
    0x241040140342e029004140d11444a06200c284d204480400020b1540c2004650010103081a24113100848800d40190781c05000160b001461440004030038510a0200300d411000700030040003c0080e0100c0703625000014403421061210348000517880c06014040703502910001801004030421f03c0c12100010300d00306400600103000100007a07403e0402e8401c0324081e64058654207104007081d00111140140100f02c491150004c5451700d010814201d6900044d15024144182103420900001c00300e54042882904651242d079244044800700d041903000c1c0f2501403200c03040c41c41c034441c0a03843c00341c00120081100c04034140010034000c1159916001d102c0484078103010540e2418290282c1d0203402c0d240705403038000c01008038907142401c020240714080034400304000807203441d04040d0f80000ea00001c2c0d0754002524644402580d4458030b400d1480a0038070302c0c1c00d140180c0302c0b201d100701c95200f0103010703a80008070021141e006008286500300d001e1442d0301c0b00f220f140a04090040340b18103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 363097140 1250 363095890 363095897
    0x406080f0f0a0f060c0c050d05190f090b030907031403040303030b120d0507020a0e0f1009090305220b0a0302070b011406090d060f0f02040e090309130b010203042103 73
    0x669800c1c418040b80c00e8042039008800c004900c0c0d80354903500010010080c1079420700c401d200428001401c00c0c40100d440c083e290b150261900810401c004148110805e12400c1101c040d51046002d034005400006031504403034415126a074805001d440c011031a00050440c444014103806071200c004010700a5a01c81d0340d0501415a0350070900001c1601d4071410040c5821560308108100d02c900042d20102c1c0c0010000501160f5030007103c030340f00300c0585e9906000010030307081294000070540020000c115844c020841c80d221520000c0c070f03c0c083d11400c00907070346189e03e1807491a48a00340710000b81101034a0203a54071610030f0301400a50081804540c0c030000c800000641800c421455840024090949450410400f0400485429400301182c0b82a0744110002895a0394070450076203103190003005949508001400301d80e4200104008825401080750038003548806420403001c14003d4008685c00c072128006034114055038202101640701252002030b4449660081d50405000340c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 363098390 1250 363097140 363097153
    0x70f08090a290403121409040c02010f0b0901080703020f0a24020d02030909010b0d090c090e1006052121070605060d020a0b0f1201080705011d0108040b0402010e0406080f 75
    0x10b0950040e00440c400a0400c80300c2c1210104064081c0403076105503006140341d140b80c1103100c00010300b01c828483c04400140c1d07580410715000e607103074440d10741c80c5002191018050361419a1056031000701703004c002d001f60380e030595550203a2140c0117518040c060f20074040b880d540b0043d00200006002c1d8007103c00502c00c0c154952040c0c0d0000c03080b113015950281004485a0038001150300e20b9004c0c02c88030a01c1580c0e1402007010885d07290000000d843e14000201e0041003000c4280e00d0440c0016000d83c403e40362500403c61a5226030f8404009680c50490001001415034040e041c54140e4204204824401c81d030402c01d48280d070010300c40b0034400c590030441c6444403024808002c83e80341e4000c1d0000171090040c451034850308090802c000403001074525192107612030340f40700c100c2a0f101d019541e000a000b40001d42e04400074180038001d801210000100c100c1c0004c0c1141c10150015043c851b094000c80c0559120b0501a8080040604107021131a51000500e03554003030f00d482045076001d0007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 363099640 1250 363098390 363098459
    0x72007152309240a031b1b020105030c070510060510092306070f03020c130509070e09030c03180109270504080c030a1e090e0a05130c0306060305071a070f08090a 71
    0x301c040303c01d4401e002191f40c40d1403141d640151742d5030b0700180604205c40c2083c05100d0000e482081290005000d41101050152901c030510030b00740080a68181032081d12417040c0100d00c002407400d00c2c2480c0d036241c1e00c03010480f80382c04079040344955034000d4640403408407000107164000807000406a03050710079400b143c20000c19001100c0083d43c00000b103412100b0204508840068003d800c00c03080c205607860103190510041c510b42c480b800062a504954603000c04540e040240d45000785010009081102540c25009002c81d80c544002e80205607075074081400d0049400550740e0100c0c42c0401c496071005100d01c09050039100b442c4915a070342141160000c1d0b903106135802d01c112681d05890110300d896405005000d00710007810750210000141019001c1074280002c2c034000c1d802a180010810309506007a07040c6580382d0880c80f00340b10072140c19402104120112601c0310f03000480001c0142c00d51800b040f06200c2c002c119035110016202c041516142c0c030f0140300c0281c080780c00b13240c804941c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 363100890 1250 363099640 363099647
    0xc030106080f011d06123418020a05040f170f030901050f03181c0908120d0537050105041103072007152309240a031b 52
    0x9015920071034111314100e402c0b40701441c40d61904080300038141e039402e607502100740c4d1a1243c00c1205c10b801020444010f94002e80448036a01603d058110010319142007a0300c1c106080704260342c0100f065400150056807510540941d00134200c24442e54480d0341d0380f00b203005030b040036644510902c4c1c020072805045541c000411104510b4040e1505801c01086601d00c2281d50001010003004600950b07007603c02c540203000c25101c1c030004540e580102200d14100500380c1c111030308440050384c001c1c00310310a50000c02c01942c010100c441004640342c0e40e1080b0b8920180d00f070940307103a00410b08055040b4442a50180c0c0c103040c86010404000380e1307a0356001c20060b60340c0420b0b58524501d00b00003080301d980c0700384560f112011101254084040b41c0c803050078a000101da0001c091008580d81c0c00180982c840e420304850219220004204c100f1002c00050034032582c003030340e44520010050030003114540303081e0b60150101000c00a0703e48a00c04005000307000503400c081d95480380720644200c160301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 363102140 1250 363100890 363100921
    0x6080613060302090c0708040504060b0a0807080f060d03050c060403050c011a0904060b1c0f0308070c20040905030c030c0706090b0d0f020c1b090601090e0f0406090b0c03010608 78
    0xc0080a050181d1900d401c403101707661013404283c401d07400802c804106a20380d0700461009111900000c0d41e00e00400703c008010341405080a4100094007050140c0002d151040c913810103400c48402030384640c42c0ca070035281d0b803103614143d0401d03008440410080c03641080c041c00315034401d0701c02400140001c2601350b01d00c0302540030007079000380490041408244203911607400703150041d04030b0b1010b10107100306404810048900b1248c5103500320305441055444a5019000b0059003800e039100031003507803446201c07605601c04000710300d441001c804c26036070f550300445001c1c0d4001c82540e40c0c0704a019101c41d145e6001d4040c51206100d11400000c407144180da0341d4044070a1500020705009810100c140a05018248030391801c0e000d01120903100b40070b11403086144118028102d4900100c2d0900c43c42c018010000350501c0800e0304208500c50080b910342d680710307454000350030180d599840c10760020445100060a010b400404000c2c91000c0400103506071200764841c100940c0d43c80c003400d001d900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 363103390 1250 363102140 363102143
    0x71106070e0102101d060c0304021c0203031603031b020102070b070206090318010903080c1005010509060609010e030709020a050c0f0307030f0e0f03030d021e07030917120301060806130603 83
    0xa015141d141000b4600d5841400c1c10545080c51708801c103448101c01c3c1c03402c40c050320320420301c3c40d000040c08118900001056250b51003400e110071982415000aa103a004e2070300590a4010040c000108040c0b09602408104004900d4000030b1541a036000b4002d4018040480300d94507040d002c81e24441c00014000d01c9042c01c0b000440c980094141c0d0b511f0a58960b1030241d0500480a01c04800908c0034030150a071500c10000621144107050641c405944042c1c1c08a801901380c0010700045840300303011105484001c0c2081030355100d6542c0801d2070140d082d40308680d2248041541e8240c07075071200080080060344412a1107440701c403203040b038480c89041c1c0f0082c04200000a04001e103801580b4020390100020003882c56402d002e4003181c04c0da4421101d11041d03d40c00220105000094581120403421003809103040c000701d69006000948940205504140b2942c141c03440aa400c00c0351880406007002180d4032941d40b000c000e40000c0d02500c14510a0000c0c01d07509226065910070b010459 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 363104640 1250 363103390 363103393
    0xb0a0803031618090e0d180b2803051605030601020a061e0603060c0f2f0f012301060c0308060603071704262718071106070e0102 57
    0x6481e02c100b810703903105a0141c1c0c82d040c0100c2c0600c807500c8012584002004001c01c02021561070603040700d5a00b0300e5039501400c0140400e00d50400f26004501e101d080a0300c400320b84881d0340d618610441150350709110340c100329158440040d845c0907036064000c18040d0b910f04010036281c1d480d401e130a0b21140030481d03450b03005a0140b100c1401080060f00700c0389640101a840342129607078200500c040c0c0300030742c100b601c050340c41e14a103400e8160701003140308480150345401c421407040084a02c1c0c140040602d50100b1500c03624141108100c10300000441c21000c000030480004d060f250541625030100710b524100c041e10b000044d0003401409604045903141d520030f2060303078500080054070b400242c05081081031500c403540c5110500c401030b40c0180c2c041e40c01d183d006610701940a200501e0200b20300300e031400a002c40c40807052820801c0e9242c210700e4850203250003000c0b0115480c085801480074150b51301505100340280c00c10160f9442144407020f544d080d036204841651310b11000b60405005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 363105890 1250 363104640 363104647
    0x2805060a0215151c03090f1a0d1e14010603020a0804030305101e0521060c090d062307050405030a02060f0c060c0c0705030a03090b090a0e07020c03010b0a0803 70
    0x110342c400c0801548210841d03840e401108036100820b4910301c5a00740d0703290410124541809158009110070000c080c450105600d01e400c1549030301d0048140c018101c102000816801130b00c082c41d8000050f6a1000c081c04007941e4007852501c07000c6e28012641550381d840440c00400d44a21074000c4808560094a40364180d45983d03604030300402000f415011002d5200314003140c00c80710041d400840414480900c408030342014108132030b90100540825112050039000202c0a2011505940c8510440d50b0281c6aa00c18004a00380c44803161000341007078505884240c812107013013002c1d079075801991040c0145580f03a900c00c2c1c4041c41103004060703066000e8040c2c0740040c580140107042805000d01c1e61b500304613010700003a2405406032003458240c3c1000c5075030b8168071410840035000384412401006407074400c1e00c0190119409004151b82c2220001d0041090380302c5d1801c0e04000c1a0001d1030301c00501e00404c0080d01c41d50520f40b00c0d403082d42000c08820451404c5404542a11aa100550315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 363107140 1250 363105890 363105913
    0x9120322030c0614031f0506031009180b01150201020903034510050d06080c011101141503010b100206181f020a1101140a0c181a092805060a02 63
    0x1810001100b0312155100c0840046125181e50012714001d414507085050044d080040710300c240d89581c00c41e20000f00b0300203003d0001c0342d40c0148030360448100d190082d10300c92011104a01a124506400f90107210024031642500c9045803001d01070001602404083c188040b07000302c417039031141440611120081400d003124540a4012400590b060074070529112054048106484d00741d407101105810004d090f40280d604044012460030000008100100f411031380c003100b201c03028087d11541c0c0081210003806032001d500c40c0f89100f20044c04100c001080100003961813400300d803894140d80000c0c001e0400b14000180c0e07410b02c0b10010401c2e0800c0340050704500004d4020900603801c1100900050b500d4050030b100354040e400d0b0080c1c03d508240340c0400342ea401c0d01d040120980401a044c00c5040c0300d002a000d00c41d095a48480c618107a5550340c503a040101d01420503aa54840491032481c201e0114007981c0ea0310b464a01103c1100c6070340e4030b208010ba6805091070306000342e005180c100c807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 363108390 1250 363107140 363107161
    0x506100e01090509190c0f090603050c04080115081b0f0f0a0f031401180f0b0a061e0302120d020607081902030112050709050c09120322030c061403 65
    0x4039210018508140026a030b440003d201003000d84001401841d171040c0034040300c525028150b200b900c0380c201005c0a02d13aa6900400b81440c2d0301c00c41c1e04166032080404c0000407200200c2d80100b03c0e10000b40480040c038210590003000e02d11411605101c0d0f1000300011a484e4019035a0800300140a94004014a010b000ca2107081602560303214241b03050200d40140c8401c005405540155001400d504115030b10703a00b120b40d17100032100e01c0740101044800080707159401d20120b0390705c210022050384800340c07840c01a0a25400c840e440d05904c0c0c10031851940090792480889008590443d0034401540202d500c1d600903111240c0160009000250a54010200d00f03401c480001e1404c00c44070096a03840c0201d070000e8004030a4506001c0400c8103221040007240054018108200302c5420181e84800480c03144000c42409084401e100b10902c40301407055900354081841604d80403011080e001c4c4034a4600d020854510a82580116040f48100c55103c000301d0b032420102c1c40c684603646080c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 363109640 1250 363108390 363108407
    0x50303040b031b0a0f02061e0402010e04091e1a010f1505040503030d05070816020712030215040b01030201080a0203090613020f040c03050109060b18010e1203030408040315050610 79
    0x1280204206100b0404107240b4020080c061181e0745e002c01e0544910002070920030041c01c2c54921180c0c40904101c0c240328800400d40141d03090a0550713160f5101c0001c90090080c2c070308003403d00c45030740f5a4511341002140c1107602503481449008500c182d20740c80c910381f9100a0046103031605210344284050200f08051800041250038050f00303140da958002440c0d90312002c082c101064480052259080c0c0002c5502d80050040822103501c80d64a1700080d5105010310403001068030921540781498024004001580f800c8181d104180c6414244840107082c01c1c40101d000949050005e010004144282c900600b043c1d009010b80b030f1030317918030000700001001041c0d91000500d90b041225980c2e600c0b03200303400e8103141c601040562400c600b00b03003180c1490b803100b01c2d064401c00c0b111121603410f1a0042c0d01c01d509080954030754000001051100006041c802c100f40b1001003400280300c5140f000c0d00484e4483e00041ca1428440265441034803c2070b5050b6070030001507440340405a000d007400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 363110890 1250 363109640 363109651
    0xc01200d0c0c33020c090c09040b0a09020309060c1201060c14010e0f0c0102010e1e0c0904060912090e04061a030d180503190f05070e0a05090c0307050303040b03 71
    0x10740100c3e12200c1048900e290007041c20f502c0214050203d50006500c0841126241140050700c401c003141004980100030042c200100048002010b410303075940c075401800b046201800302d504460304c4400724030082d030068400c00c407a80302e81d90029550300d074100200e50a4070351200341d030802640303000740c1900e10309038008003294175030005003038000d02c80320174425a2404240040146001c03505100f01c982007500e145000ca0440e41011082001008006042c85602c180c110096801c404100d105c40e082400f4100500d5000d04a07805210a01c00c4680242c444103001c0e05406040c505020410303940700180d0311548644040c0940094040303074950b40050300d500840c4500400c2c0100050000313042c5818000e0003408240c01d40385c1d0040321080903105401801c816030050013140140481a8002024104010a0321543e0303403130b5104000341400442c00400c0314a0020400c0d04001c05480081d200c1200c1c1a00f9502c1910007c1c41c1600c0c00144c14002c499000c0d02961405050840200c12540000e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 363112140 1250 363110890 363110903
    0xd0807020a060f090b060126150d1a0609070f110106030c1d013c05030105040609060e0703021c11030709020a090603020901050f16020d050c01200d0c 66
    0x50080411441c0c020420041d0320f954000490300168503141e680900c02400c00b03810015103004110384100107408035480d060260461201c541d0b02c0e803100141130700820754210740107644004014104082146201d08017800700e04c01074501c0d6118801d02000682c222001c01c0026504400307200811300400188c2164600500046100f40d01ca8a450680c41e1203503022651040d02c140602d100ca5a502a04a000d000300441e6640c54660100681000521035080343c282c64529420ba0154401141d007100010107018000b40034500d05428684005d01108c01c0540d41c2078100801d002c003200c400314031b00051325801002030118211030703084c060800101942c200c03000c3c01e0298800c485684c00700b05820041c020380c00003598540e00484010070710421640300c0800d060050058485136078003d0141c540c1403401000f03051725500125909442a800500003940006e41d0001711703000c0c403001140c01840d65200b03803552501903261000000400d4030400004e8080e80091420000051044040124080c000d21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 363113390 1250 363112140 363112153
    0x1c0602070f03090512030403020f09060a18061505030f040b0a2705010b030601030c06030c120905011505031516020f120403120e030303072f070f090204080d080702 72
    0x5494001c000d81600701600402c0301c82c40200498540307a002c110f4145103040145d0700f0300b45503030b01145280d02c00480940c89030380500001581a01d4908440000303000281c0c40c3d0400300035402c00f00c401841c041c000d100c404d0507108841a9400c0c040c20171680201040c3c620294542e8450b2109213034840c0c05000003854688a515400308149038000300f04012030980700d509200c288600d0720508442026860ba806900030130010804516400700316011038213282004181d509003003d04642d103a06207200311410b1031070300c6022802e100055214034a0440390010124a070b41c1c6034030825584eda241c0401100300038420000039488891600d102c0381a00c510b0044581c600c441c41490b41c10441c03805040d03840d00b00042810018410030080c045c618034601d041c000d0b80300c0c0c16030f00400c0d103a210040028052200400d201403402c00c142140c0c088980058134409208000461815201c045a10440b405559101030100b500b0b140e500c2114112140741004010702c2c0380c004010340d43c044008100c20294041e55 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 363114640 1250 363113390 363113393
    0x306040c0e06070308060a09050f041713121209050a0b090a0504020a0c060b010305010605070b06010e0306180705030613140a081902010f0c0f031a030a03020105070206010b091c060207 81
    0x1c0c8050800c061103a194405d6a1406006010388440c031075101c144a503081c80140300c0c880b00c400784103540241c0c210034102a100b0340c55401d6811032240c081303400e40b511b01b03d02d0001900c0d0007100100d46c02510610100c0080c50758007000315234510060041e182e0120050038100011074943c0300070616040050403845d1140e9940c07001800301d03046002ca40011950400c28a8208403162090310b26564090030100110f5061440040c4940141d500c018889080c030404035066a00030031841415180003001c94000c0d1400c4481c03001c110702704034607140c440e10400101055914010910a10603c002200c038892041a6291010054484001c401050260321103560200da807203001010000210f41c60301b603044141580007401c4a8902c0c0308000c0c1545030840b000c5042c3d03408101c801d400b030741034076010030410401960343c141140c0220b6001c1e070502c00e034a510700416070103402c181e01c18020364003900c110743e0baa09031240f100d1040c0803002d036001c40e00d10002d402d88170b8858901c0400d280994001810708009 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 363115890 1250 363114640 363114649
    0x60c070f060302130906030f0204021c1b02100e0307020105031905070306030210210b1309110406060906020a080315060c060411060702031f0905100e0c01140306040c0e 74
    0x1250081d0340000d40000c1e00e9007840704c10300007220003845c034000200304172442e6407aa0f02102204500c02803080350001204055001c16000d03001084010315020858138a108064110f01a44c805254026008000c5002e1a100c8144200b03011040701402840c686881c941c011a525400240031008001c4210f4858100e04078510550f882552a42c07000038910b41503004000081c580c86c0038a0081209540548640c00291159103c0035808244007161280e40000052041558682905081845c0c40002000e0041100c08004151800d850030481c0540f0707448101c8100d0424050040541c0c004045d5600023000ca9001750751049110480c800d0b01d00c2c0e601d00043c1c42c0e500c01da40b007510a40c0100b050100f4080c9562110459010440b005894481c1d1a4082a21140d40402010050400010102c42c0c01010f4200098140d0b10030169005411218244070081000207500641c0f8441c50380140555400345462400c010302d900440c07411035842e501040054808002044100b01c440c19290b40c954a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 363117140 1250 363115890 363115919
    0xe16090f06150810090c120c0504050316090c1b12090f03032606150c0c09010b12060306130b04020a08010606020c090a140105060a05130b0403030f1805060c07 70
    0x103295100b0f030181c200801c07100d00c11205900484c042a240610f11201160080750526020300c40030404200c2a440003c141c031107028640c007454050251442d4005140d41ca500d47c0419a0303802c110030000800000e50071111203844040703040d1000300307400c20303800400e4840d40002e00d5900c592600000d007a44074045520003101550048010400303d071074960b005404506801d0360390f4040741d42c5500614141c00043c989000c9007a0b010100c40d40002c0008072200c0500000780c0c50368005d40404159651403813108a151301110510346813242c1030011901914021941500a890f420303200581e14805440d400b010b4840904100c5c0d2260507000e000400d003600b030042d280104526000b0349580c140324424447c3d503030030007000f029020b071510900308000001e941c201c078199582650310b162228100c520541c2c1c1446010031640092000600004100c6030700c41c01001a2032090384c40749541c0f05018010b44551540d01035080703d003092050203000f04d0910a000d80620038040b011510100d035900310040d001d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 363118390 1250 363117140 363117179
    0x90406020415051801140d020a020c12150a020403150f020706050c0409110f0703050912010e1b1207030201031e05150a0b03012301050403050f100e16090f06 69
    0x1800882c0509100105242c0301c004000b003800d000c002074140c6c1d404002c1600c10100000c610700d07400b1401200d030340e01c02c0014003940304000d0040a00b1004010b0600c3d41d83c5603440d03101280310b8422000440e00e182034000da4040301c2e80100c070a400080780c41c01c084003406008120f280c40c0c690038013109010514a000b00c500a0650030b05081e03075207080c40d1928050b5040d03040c190130895006c11004080442a00885007401d4040c42d005403500d11403000903580100281c0383c0c0610703600348020b460301c03c9004281013441d61148001c040316007080500344020b4680303039041da80e20303034000000400155000307401000940007188d4005c0c0c02851030440b2541102c0041d80c12440f40c1c41110024401c1c1c2c1071903034413000a041d482007240d08640c94500c181c90792a102517201880d003072007500d6190351070f40590300342c802565000301620305480c0c00c07480041c1d42d4000003015203000d5042c40c40c404400007010482c8508612200c10080ea0141840480c001500f548048844061f030759003c0001e110054464200301030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 363119640 1250 363118390 363118397
    0xc0320010f0624080612120f0a0e010c0317190204031b09050f0112031b080c01060b041203030209061b0601080609010b09160c0c08010902031218090406020415 70
    0x1428151000400091201c0f58661503011000600010f9048401c041d0300030000c44600300203510f520400d9040060001c10f075482100c01140881100c26280050710740040c440d036079044898404401101c44400200d80600419082a03803500c0796505103240592000d54010303001c3c05a44445a18004c03603200d507100741c07000301a42108085d503103162228000105022107041c0003d080c10032002420120603c114244145103140c0c0703000f01401340403002d114161846400c2c801c1c80b120300f4001c18a07401044a07402e036500c0c5c0321010a0340c1b800304081ea4142d40d44104003041e001601e41d0294000c1d407120b903426a02c00303400c1c4250002841900410201c2c00c08078030107031419500d0030a90b91b1600001605c6200c803a410407a40440c0750f1980003900c0c0d44040306101e800038000c003024094800440b51040a050342c480c410011031040e105400103591148258103c415546c2c2c0c03d10380080b94000c06886d01c0801c0b00710154403c240c648140e106130403d01a0100500d00ba42d03442c2d80e04e424001c07826402020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 363120890 1250 363119640 363119651
    0x2003010611010b060406080c0318030a08071112190504210b0c090f04020a0e0a0303081e1e09030f070606060914090115020f010603080306040e07060c0320010f 70
    0x502400e0044840b042001d5a206041500b40301c0041d00307c01c0c0c010015100d00101100040ca1200940b201d000c01c031054100340e03681d40da0070b0301004216032811101000801c1c130000a00000c00e030002a001e038240c0300b46000381c2c2045112400d400e01541140c400c00c04001007032001007080d01d05c0c10315000c98604061884800c1e0038807894001d1040f10700900c0d126180c071090064000986818035801603040301100c00590702c001343e030820fa40b40c1000f25955074100c200d0b60030120406401c4500c080c081c1c40312510b4941500444145054160003c54052004038291501031580d080e044511907003006811066906100700403807641d049401080b029921103485420030000903402800410140c40482e845121b5410369a011404c28003040c402d40da40c038170f200452541414803c3c0034450380b08440324001d00c00c3c99038038100055150003c0c0c0709684500e00c0c5c41041d0311100fa00098001c1240e410303407141009a1f1071914242c507108a0580c81c410030b007220030018144038000707106040c824400301c0c200184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 363122140 1250 363120890 363120917
    0x51f080f0103030903111302130303020c060703231b030405040b01050a0c0b0402040b0303070b010302040506011b0f03020a080307020a0c05010e22110c1005091605010320030106 78
    0x20003605028001640c800103001081d4800c04a0042e250044051441c55080d0700108140d0740c0401a038501d4a413001c40c3c80d68000d0580b0340c000c0c08890003682181d100e003985070b003004518030507014001d02003003050f03982c80002c070800e042444040340f00480749405c0800c40c62508041184000d100840b94000280c140314506c0c0c05c0c803039802d2030002840e1890a0440303440001d814404084030203070640780607400240071550b654010b0400d603000a0b0581c0e07120019403500319040e82d000c0c0000c900c940e08040c0013034525482503030041c00f00584444070981a1505807141e0800c00c842c240c041c1c0071805556520b90104444000460161203264000d1240d0181c030b042c00102c02c4a59007006041100728141c4450707550302e01440201450305180e41c1c0d000340c03101030600d8004007180c040c000845203011900300c000c0c682c0401d95084588024a06204a6131940c50040c2c171160804420900390042c5107080c095540309a1001580600c2034030304800100440b4602c044c4c1e07403c00d80c8290700184a4081240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 363123390 1250 363122140 363122147
    0x406020f06010f360605041103160c050a0b0f15180105060903070312020606011205010b1213062a090b0405190902040b0d06140f100306051f 62
    0x144014003901414042d4180f001c40c4078a08038500c91026400e0410181e0000c104d41c03c031000800302c91200b600c0b541da584100412000d03280511960f4032136813400d007424030909401c008891281d1003d203601e6401602d0b08400740c0709030061170f806503014802e142130200000c06035840c02c0d02a5090880038900351400300c1c141101c14807900c40e094020a8034131000080e0390b903408842c1e03043d9482101c0054541031f9020120b0b00d0b0007030340c0c0d001624602c81001d000c481140c0210340c281c05000c00303903111400925107141000c2520f07002c0c814103c404004000076000c2c485804090794120000c20103004010200d6102c0e002625441038040d4800f42c0300c0644104400c2042a030601c6091450614400e1240b0341080e500040c0158031a10740540d42034843d007800f00200d01000d20180c04500c80442d101c3d51641c6460006d504003810300040b20f850400c02207144061140b001c03640312001010807145031324420910110400315040d8005054661101140507030f204421881c148005080205951360244e00c000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 363124640 1250 363123390 363123403
    0x30a050606090d0210050904020301030c1401020316030503040f140f01051303090510020a05100b0a060e060d240e0901150501080c031f0b070203060c03070504030f050a1205040602 79
    0x124030031142003208408545408100e0b80b0540c4d011140881c400502e4802500d1074415864005d900510010010003000400310a100c01e0f1106187c4c070200039003545005990328840d83c261b00c02608101c1c81d41d040000d10400003554828890804008440316a136604020400c0e00d119802d210f800c40410400451000d126a40d4841444850040090916200542018103d0086502940450b058181c141e40200b1012516561003800c1b00c8070403059039000c41c000c1a041c541c03181704a00120000032080c0c42205e040380216802440c5518000001da501c400601e0100c00c00070005644c5600c5035021145030505d4401080c280340d01030454079226000030300710389460062240078690a001403101c0c2c1d81c0300b001d440c1e01ca03400c1c0840640e42d40321194005070140c030302488005d501c481c2600204000000c14050903a1034403c0e01159083d807900303050020203010403501c1c0400a0428031040000c030f1016004d01c0d91580c000c00640790050b13240e0b201d403601803080460380c1c13022980000f001c0000c990f0401c284d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 363125890 1250 363124640 363124651
    0xd0204110c011109180417070b0711011406041d030c01020403021504260102131401020105090d08060d0201031118150403051902120d08090106090203090706110709050c030a05 77
    0x20f1501d01180310b000100d5020100c145c41452039040e1000804220b44040b00c141070340b20000c003203034403105ca03071800e40c0c40c08400300d80c4a0b002441a078644140e142c0b050044820125400c1240c0d0901d030b0354070b0140401001d009400c0040e40b100002d800741009c10900040c02c1e8143d40c4000035070740b207003140148141400030799010a01c8500800003005001c04401c9020662940d0101c50410343e1940da040c40c0c00380c09283c0700c0d091295800100007074000c0c2c00d0040c9011000b020b800a000696581201e05d450311180d28040c40810305040c0011407500d01407869504a500c1414009130706190a640c500d5690443d01c2d0060203658840618076003464110143e00710350418032312040c0380608603620152151006600302c458441c0c0c00f200402103550742000041007104010446409c010310720001418108151000d5010b5483c18001242206050003141d11604081340100046480c0403070071222000c07000000c00b000c1c0220500030454001d0340c0a078900031017040f94595140c1c2001d004c14030413034102904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 363127140 1250 363125890 363125921
    0xc05220501032003040f081c020403030e0303071106030606070501050f04061b050a120902060a0c030809010e120a05040e0103030e0901120221280b0609041a060d0204110c01 76
    0x5442903e07506500403240e1242e80501000c07107078a000d140005d0385015185202e01310221181c0d01165903040d5034050802c481c000e41d41c0c40c00321a0740304241605c03449030000142640100100c00c003004c4c28624000c42c0c219001504a83c64aa49900d903542161800c1e00d811140d8518401031105009a42c050402c50918000301440c5000c4100800f030424402c10010b0020300c84201c01000e0403018039446008241c1c0c000c0c1113141e0302c4c6ca50f25002000140c07010000c030f01050400011841d01e0005111380c0358a50580c50082103842881c442c00d9440d5008600300da02000720801001c41d01c4440202c046000b54402c2d1a61f03201c6410100420400b040160444001c07900007400c56809070343d41100003e440000c2404040c00101040005e03030402289801041c0030803031003900108006103110700364035828058462001c0c142c461004200320010280c5000d4940049254000914044007403046d406c01d8000f8480001512154046000c0d90807030034410281c4240869003628075203003800b8000400c10200e5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 363128390 1250 363127140 363127181
    0x4172a0c0102010e060a0504060b120a020405010b03010b070b0402031011040e070203120a0207210c0b01140609010f180605041e0303050a05070c091523130c0522050103 74
    0x440c0d49070f170360100910614010707480748042003e0203055804094041000741a28008205170301c1c5081d80e4040040c0c080780501d04e41400000c0d126004e03400c2e07034140c904410f8940d150402c5a1903d03c98400301a00c1070380c1c14002c00c42c46810141c5540320740301550440480b00c0e500c03a841e100c2000104000144032000355003040080d07015099001034110340c0400203940058441e24181003502d154400240a06507240c4400d4480f4130058020343e900b02401d11074040d407400c1c2ea0302c034451401e1955040030059044041440046819030180c82e005840500516004401c0702c0084070740a42d203501648010007107840010280b00c4600210b0035146495a1000004880313403640e07500600714404d0005050800101040d032004100001c03440900401c40c0034802d00101c1d405000c2040030382501e2152503103250001c40d05100c0c0c00111040b03000c039094010700b10001e912042172b0303280c09082c0c4003000c00d00b01b00c400c22100e00701d814901c6140240b8552a006500003e0600d40050211500c2072981001c024000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 363129496 1106 363128390 363128411
    0x62814070f0c120509031b0a060c051c0e0a1502070308031005061b070f06090b0310051c03090807050d060c05072004060e010e04172a0c010201 63
    0x6c50035160055181d0a010014070414081a074004140764410848203000b243c0c0d50001c28050810744480e88007101242207c1144200100301180c12140141042d05140000c840a0400034441303440421400802039a184101c0c4802040c10320000002417030b560b0301080c09002050082d003a143c030340d015201261070062102c0503101341482440c1c000940502d0300c00c030200c2107034410340b00c51a10b98100641030180b60710084c2010f143e0381142c0070020740360722400e0780301d0146401c5005506000b0300314900144200c40c9a07201022550000109000035590110101c000c0d0368080f8000521207141c0000b60f8107400317500d4028000107030303801e420b0800c01d0503036202d40d00100007100e0130002a9101c0c40d070500c1c843c0082c00341c650760305546400540020119070950300c050000c407040a09024281880342262280c628000848144108010b00034280802070589510400d0000740f0098648 = true := by decide +kernel

theorem cover : BRFrame.Cov 362949640 363129496 := by
  have h0 := BRFrame.cov_init 362949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 362949640 ≤ n) (h2 : n < 363129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
