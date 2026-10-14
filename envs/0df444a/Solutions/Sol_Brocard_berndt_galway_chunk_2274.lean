-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2274
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:12:33.809234+00:00
-- url     : https://prove2.me/submissions/809f82e7-bd47-438d-a245-c9352d74a3f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 408812949 ≤ n < 408992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 408814199 1250 408812949 408812951
    0x191b0f0308010e010b0901140d0f14010501090b0c030304120c0b070f02100b010e0405041a090a0b060a0509060108102706050a0609030305030c0f0a08071d010c08030a020d 75
    0x10205040041441030300f4041c060341c1c10144000480c0815510081e00d0034060169594200780b0040203040480d40c000b4901548407544640484e201045980100000c0c4c806c03080498009600d020001461064142c0c0280c404c0d010812000320340e40310102c00c803a44260407046400c0c8199480c00d003100e190920702005028444040144540d0035840380480b50102c060354219050898144809003c68150603580ca003c10101c41040c0e541c2d062070340065502c14040c40e2140c00d900b450102d22035a40c0d20440e851005508400c9031103081000c101e2203282c0102c0e0556a100e5020300b0203002c6400510040c11460501a22a00203132805403843c0d00d00d000340401641081c54108003c030151800d0440f000c02d8030030b440c20200c5c08a01410a400c8120032201950b441e080c00c503185840a440a6102812850010700100a44501070801130014900802c8598403004140350440c4020400d06500c00001d500303200c0c0860728100d5a81c400c403001065034010114956035110210000002e10600341c21006503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 408815449 1250 408814199 408814223
    0x7051005040b070801050a0b04030b0603071a0a0f08060f090910020d060e16090501080705070804030b0a1a0a0b0a030912020f0607030e060c0a050c250902191b 70
    0x41504a540544484d49414400c0d9880301c00308030481c5064026418910b80900040008c2020812a150402c2c00681610240303074440360220850500307500386408170302d800580c03661510791240b01052030035003614150300c9505205001410b8410080d90840c4076035810303070200709079a00611401140d44004030381156282c2c041d2003031038054100e910072b114034129542d0000c2c007075040c034907c180905542a0740d0706a616080000654030014054a0141005824001640000c01560040010310b000b080d01141c18580981c0c00780c113941081c000890342c1d031a210070910880e2520300c1c0103003e841e480d40c521915a00b44020807002000003820141c404a10798001d1003810f90081541d034041c001c41c1007501c001c0d68522409800396108036907889401d910500010312010f804c1000f40c01c030f10318a8030b0b2491401c10b1400c560791a00c60b2008a1024041446c05c01394115400e400c1034400074000100c1c00d46c1441c3c0d5240404c080040b40109a80c14040c8600000c403a10021507010048554016042c03a50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 408816699 1250 408815449 408815453
    0x180f03030b1206010504060801020f1603021c090504180f03080a0b09012408041e031214010f05030a0f08161203050f0a050c0a031d010e0f060a110d020705100504 71
    0x42c0340c2c400e10417580568501000447c05420600844070f0210252808501d400303c0860968001c045d80c8500f80c0444c01100581340d950a0b480c0302d801d101407055540c00c41c100d0b00342300800c8107c1321040c0107590b01e0700940a000c0001034003400c00340355407901820400542e0b5070350101400502010302c045175100144c03100216082c00b0910545101301c3c5480d10401c800d0030580002e440d005010f03140034040343d421207103038902c05540d1550403031a5486407030050b2140d011045820b0035950303410300b45400c00d180000140f103a03d5203c1004001041d08600030840801180c40d1400440100b02025121010004051580400c11406540e50684c4401d0310f0301840c043e070320000c00600064074044039210082000c01c51810170b6001d45030084030400c941620b040d4040809500030301144401100c1650900f08010403e0000e01c00c400740480140040c11211800d00748940c20010010034060100b890044007003140b019100658900c2c14403a200160f03500044d0074058582031144625213002401c1c4010002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 408817949 1250 408816699 408816703
    0x101a0307030609110d0203070e040f12020c090703020f09010309050a0b010803030708090c150c0c03240a110313030e03060a02070212010516030209040e0a0c0303020709180f03030b12 80
    0x18014040d610a5036020704480170464072807002807000c3d602d50b02041080c022401d880e09016009031240140030046042545c640c40c000050911881c00346e0055148990b4a047c0700c25a19400002032400718907100f00104460f600b0b0013804521410140d0721203482d03041000c100413040c60a90006141445980d44010aa58135803003180c0c010002142040404c00d185000619020151001480c080c540c0c01140e81d01d00240d001042d9a60440c805c81c00c4403803068409100101c02071048805500c466551080c0b19101e0b9903018254458076464103040d600100b180e0400d50b900010360b20000710352040c0e68203084442c03c082a80c11039240c01a901030004000c2140d00038014a442a9403005050340326041d0f4074202c44044440da0843c00056038a50000713440713a402400070200042000422500001c103052a240c019101100c3c1040007401c244249501007200c0002000c02100078450707101c1459001410040030100208242d4005911a0416000f40c00000210308040c084190305240005419 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 408819199 1250 408817949 408817961
    0xf0d121a18011e0b0a0e0420030a0b0f0901150c170a0f020d08060405090a050f0606091f05061c150e072f0c0d08030a050f0603101a03070306 62
    0x80030404500300c107589440c0c9402a282c01c40c0c030b281400c18100100c0c2c0401750740201d0200341c1c0c80c0d849031341e0740301440415a01101051400c005200c0c91278036450700c898a6811203003084040c3d0701c01c05102054a00300c0da41c94041a042d20300d011556100b040040d882039030709803e501c000400f801d0b0070f001800d0381c6044140151503440e0207507981040c10400c0d94026602c81c042100000b000a03640000600c1c10b040035000150030015510450308060080d45409080c000a844500d00c250003d505102c0c1c83e141492035183c10001d041510880000c00d41230420b6808920300c5510300902001c40d400001641080c0c41040c031150454040c841d144031002180340c240600d000d0b10b030100d0340b81c1010448080c800c101100311a48a00000718140d040503400f8202500b000050340c0710391041080400060300d41c100341c42081d40c4600780f204c0c0c481c10640340280a464006002c2d500e44c141010400c200b039503002504441c00d0781c8540000614000c00401080d030082800000394062182c04c9000003004190343c00340d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 408820449 1250 408819199 408819209
    0x20c10030b090a061d090708100506120f190206160b060109081b01050c012c0d0507020114030a2d05060f0a06050c07030f0b07020f0d121a1801 63
    0x306603990710f0402c0401101d2040c05242039070030748415020504d010481e400b6401461140880e004c1564038030100c0d15050810081030040368541c010b0150300e0a0900c1c44e14620180381006c2d001c0c040e00c410000795555101055542c18609652080c020340d16240212148924800e072500700950003070508001e407010550700a40018610b00c3c000070084404118408001b241958103508107a886004440c02e0b080003d80300080d5503a4100c04280070441495002071840c120012981c21024a00030703410b280c0c02c01045c20500c50200070f0303080180c6c1d210701c2240c0c07011030a603000d640320740701d50f5201300041000f850680c03d0140340642d14000c051055484552000350314030207000a40d80e51041c040403440b04030000350016941d07107007401034901845c094000c810020040707a115a540e030f2640c4032000a56030094a40100c0e89043c0031003568103215030103401804500034150b46038500002171003c49070b0302e61224030658620401d5090703801110212502c0303030000d0030491540740400c103200c0c00396028418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 408821699 1250 408820449 408820459
    0x507020118081b0a0e0a06230a0605030c09030109030e240d05041505040804030b06010302030f0103060b0609030102030903040e34120c09090b01030605030c10020c10030b 75
    0x414076641e9040749151090301e04040140c60540c803861950500160090030440e44910005808220880903c108a21660050201040103858580400b03c64a00c882480b07070310703074049824211580c03a5a01d6060850f001840c01c5a604d036200d03000740d400d901610403080d0b415402c10030781d5030038190300c1f40d1400c4003200e084400005a00c03c1d2039010318040350b21000c1208104080c0003031401d1000e00c2c1d0255500c64015094100300d07810b0303810f1440403030300100d404448101006c6820b2041c44241c1e54aa60300480a003411845c40c2404101019000c40503c0001c0585460b48031512094461174251031451074040c000b9902c7e41130501c241034594001e4000c244801001c0d170001010f001080d2152501211a0071015104984d900e01e001c801000041000b000d03c0b00c59038401d0011907051003404034040703c2e035580200c1035040014040c00e5425070400e182c101420054144015074010441125144040f5401c03002880c0d0b07503000380d08102c0c811200951050108202411a64040e08001410300007150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 408822949 1250 408821699 408821717
    0x1e0906090e1903021606050c060c030708041401200414010c0b0a0f091e050706090515030618040f060f050c0403061a03010501080c090a0b030303131401090305070201 73
    0x3848100e03040752558424603400b9007840c1d0b010300e41001020424034040c0c070551741452a104154030603081c50b58403550000b81c0c001030341c920380302081c040e503500032058004407851824440002407012002400150081c550032215401212003507001218154401d92401d44103080e01c011001c9075080741c03050003441e003800745d02081c43d50302c5005c0e801c07240e680c41880d005e599100e1603a070350018000c41d040c400a00d541d40440c20042007201c083d1850f04407120054581c2c8840c1441c03c28104505a0720003130501c903082000b0321040c0d4503c1641013911707440507101900c0b980c1c0c50b000290307403042e44070b80401800d62000501003405284d00112149134050402404800408a00001211384c11030b510404030300c080c881480004c22a4008940140c2042d60020a41843c10006402c40750280d11640c2e8992000d40780c0c48407424030140301da41c00700c4d505008000c4540c103007010a45900c0300038550010550300001c0e10f02041005034203a06901c50b1070b00208500b4425244c040c2c007680c41700c501030380031941401f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 408824199 1250 408822949 408822959
    0x30e0f0616110109080f0a030b090702030a0c170a0c140303040f11011106071e020a02060706020f0c071e14030a030302090301021c06060915080609040c1e0906 70
    0x1501500640032900d6204155448034070460303602103104603114aa5403545190000701e108080a4080b21512040b100da4a0140c00c2c0c025044a00c50b42101d805000181e08104c0e02c203801009941d078201c2103081c0700300d000c103045c0340c15045100f15010240b1000e6010402c400000d5200307042c18071182c400d0704549800d00c024003826540b40000c503002030141078094961400104150301002e4001ca060600f490380c0c41030340e903806052560440c0e0032030001d047c802100c90540a1140d1015040703003d0300180c80482c0080d0045000380c41110301c06090181c001a142c40c8000c100b400719050a904101660080d070780320341c0314452004000c0003284201c01c12400c0071480070300504203010f003035400500130020702080741e9080d00a9041110302a5143d54203118119a4101100302c4400034000c0c042c0024100341021405481c06100b6081000c05034a00003280d02000c1e004008690070000c2201c0441d01c641c0e0b58a0900c50b28007582d000350b106c0c01c4410b115130200d00c441010890a8419080e0140070786070300da03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 408825449 1250 408824199 408824203
    0x3020d0c06180f0506180d0f02030705011b120c080307020a03090603050c1605030f13030c0909020603040b090c060415080c0a020309131b0908010e072402010e010c030e0f 75
    0x240100381d2032401c10300f41001189025001071803000c005440000c0c8084c040070004661300940281500c10b01010700300c400031440c2c1800320700041c003000d003811035140e40044a00c1c0340c81701d00b24a00803c618800e0402921150042040c0e440d455440020203a80e4540b6031002500c6005c80307001140803074100e5401180c50380c0a400b071584510340f00b4042c9814602c1d000e000303021b0780000c810706503103a0104010b0614030310844e000904500003e40c0303d85000c24698a0200e80034070b890782c0100d203007920307100e80c000040c0c1e03c0034203c0340c0180d08112a04201d8070758840e4241410f04000c0070581c040030001d80020855210703040035400a03034036241c1615580d51786070401091300c00d04d1401d100681041040009134585604201c42c82020b845000a0f5840d04101480018402e004e6000102e041c0c801c08100d00315003402940c0903c624100504000c51801075a082b40000c41c418001c0c1c41d5000814042c41c15100b540911580003000c4001d206204c0180d101900801c00a41c041d40c141c090101c10200040c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 408826699 1250 408825449 408825497
    0x804081501080c1c1113020901080604091109041a07030b01170105060a05160c0605121f180f05041b061706061b1b04060e0402010816020703020d0c06 66
    0x20190641800c160b101d00d01a040381003a0304100c4e01c00000342090390300c5d601d544041d48000c280c17120b0016620b000d00e01c00034200c05070050020707200307a060500700b40c00159100f0124207100e00135110784081d5111480d000030445408030f0340d011401501c1c2c0400c40c0903949030f00603c94099081c0c071280800500c0d110b1200100e0f009000d1207800000802900325102e109100a00c0c0e0810784d18070340e200d011041d41c2c4e140c120f40500d6000c000000c2011138800164280e14600310b030000300b042290560500080b60542c071401d068810b08409200c015002c117105405034204030281a4080e07400c12103403030107180c801e0400002034440f1008a003035040c0031541130700030411b0340304a0040c183c0c4600180d4518003004a01c1d804864901400880000d040307180031020810320344680c0102210041c0302411200323000c1142c40c0c40c0d02036881415107100780310151360410380341600002200180008800160310036840d007003403944000c2d0041118550103041c800e5015000d01034440d95940c103d109403c45910b050450340b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 408827949 1250 408826699 408826723
    0x30504050c01110703050f031206240f2a060604020f22030b0f07021b011d0402130905060f010801061707031b050304051c090303080c07080408150108 66
    0x4881d0414501541c000d1410300100c0c01e4410443d5205516980e8081c103000d05222480990351003c80c081d030b4501020108103038810000d80780c1015540d091080d0f480100c04120311130025520004034900b52003d04ca00320f0710f40c03d02c45804104000460540700164030380302000c41c10903001d50004900185064001c4031543d29218a1040c1000300c29041d504410281b142c401c120000041000000944161540c40c440c5000c444440903601d4074131006810a800d43c80c040102c0c0400e02c10002090b07801c81490180c1032515481824200c02440103d002403241102050741c0050320100000e00581036003040e44100810340c1c807a840c5c0444500151007180003801a00081400b03111040801500c00d242503911286900c0c0206400c1002c1e642c42442d220303010702c40300005000008000501104000c0154000315003400d0712060300100c4401400a01207000c0101003001c03c0012541d4005050244c030103c941154900360303a1665140740e44d0380c1c0d0514501901100455400018958002182d03e1100034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 408829199 1250 408827949 408827953
    0x5010509040f060e04080a09150504060e030a050f0d030605060408030405090c220303170403080c070c05030610181a0f03011d0303060a0e090a1b1e0e060103050405 72
    0x106240c410031010381940018281200d96880703001510000440e0241c1c000c600840a495468080e83c00081c051040c81d00045006001c00c218082516405000c5800b100d440d8a07218442d5800000001e08203484100c0240c25441070700d18500c4011804900a00604400e4508000c042d03920400c1c04190300443c1f0680c003540e00144020030403418180401c507031001c568010180b0780911814440b034803540c900050400c0c205148828002c01d40c1024040c0c60b10000004810314901d415074008058120041ca0030340e103140d000c1901810009920a042c1c007404000341074403110f10f070001c400750411046115203103a41c4012081d41c20f41001902c1425000e400980400e401000c2c3c9a05000e449581d80560303170340540d0703a0031320004c00302c00006e0880541400000a50381d2410002c081004031002d5800110980241505010000000045009400394081c4184d89210f0700c1d58aa07081901c0329621400032445540300381d00c481d0680c1d0101005a5902c0c600440341500c0b030388011802c44404490080c415 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 408830449 1250 408829199 408829207
    0x705010219030c0201050f0d050a06090b09070e010c02030714280303031515091403030c0a0b040204150902040510050c0c0103110c07080a150903050a11030d050403020a120504050105 80
    0x102e031103242c3d001c0b2010b0041c1043c0389050480002d90072a41d0040350303103502c225a107909022460f4035a000c1c1c88010071119106001110220300020040074010307144905000c0b00d034680c102982d01441ca103984044d002820786404554481c03100403d5100e410b020b51003150301108070140504001140c2014800140f41e403403541c1d00310b640a074010705092220b010745038000c800008564449442c40c034200b2220342c0e40c0d00d25891030041914540f84808103400d200350020300046405c4000010000300103600a0907080480d00c4900100d0000c2100c01c89010003500d0305030010070309084d583c0003002111820f4400c91555808000f00f103696000e2089100100d4015400a11f940c1d8880c0d00028161140201c01c0e92a19903c41c501b0703440c0c680b840c2d200c002584c00800648080c0b05200e0314402400001510502c04002c1594004025125000b6034400380034801da0f240e07100f210b0401c240d51200071500810032050a05007130180d561403029a0440790240001c8040d11000c0c421419681111810b84400d410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 408831699 1250 408830449 408830453
    0x281a0c07140303070819080a0b060a1412090a0c05030303010b0a0e01030e03220b0f030708090f16082a010f05070605040b060312040b0706050405010b030f010e0705010219 75
    0x401c11401c0010350500c018050b410104d094200185100111110000d003403204101300600b10b1000288000003007072070408401040d886090488508041a2600441c10303540b64441d10303501e00442c40c0b0100804001c008100111400064241c085070142e151b0000e02030303071001099034a100034052455010b5090244480d00c50141c0071a1100b84014140844c4a8101000700d0b03207940c0002c2843e401c101c0081c040f425203456804007050140440c0d1412900d06600756240c44d0fa144005000d81c41080304801c002480d82c030052013a9100152a041907a282060b01006042e9054540c05a00198014040ba45040300001ca683c1007c0554100d240d4107621140d200654645922116a00601ca010020318001410a129840c0701d02e100700d0904407a0308000341418a044100340c80006850010402845030100b518280c80e40d41c0e60052003c196581c40c0c0c179081c1c0c05804084216a014400e41050501c240d60640104000a003803004480d50a603803030004998400c1c010000384102c644603207542d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 408832949 1250 408831699 408831719
    0x1e0604020d1707060c020705040b0109030203150612030703030b01120507092c1602011808120c04261903051e12070905010905010c110f281a0c07 64
    0x4005106002c1d400c1c24031207a5210f603000c1c1c80103203840c000140c000c04001e006528080c41000b00c035040a1801a04e00c5086501290b03950b8080040a038180243c50002201e940d1203042401008002c102903030344403043c515010700540300205070302d40804e04500000c80e0314890751107041e119228698a084c00b461404400030900c6450380c80090002d101c0146031030a10030354640d41c80c010380f0310440c031001c05e20b4480720090840340951400074034600015203c1002c668000280d82c5200c5d501000140700e500e54100550680c45240d200d03401d5117030800c2050411040d064045400e440340082900c03d40d9903d1030801070340d001043c5005001ca0b90a0003034540c503208481c20350755240900e080030391604611000ea080b0170001142c3c0640002c51a6005101c80d583c02043e000040400303080225440d2065550403115021003691240100400710604030950f0740c401181c41c1174459040d90010b0001c1100361280001c20740e01a1542600019600e036030504a000e04031408945640064120241440c110b10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 408834199 1250 408832949 408832973
    0x1505071b0302061509091209010512010803030609090111040e0408130f06170c09060a180b0403110303040324060e010603050a0f06180e1009051e0604020d 68
    0x604000340300e6040540310004503003010845009400504480c40c0081011000c100c41c0492680225600020b00030312120015000c000c1010075070b5520f17240d45003200100c0d0309015088036040b1180201d000014018004401140500c009072600b840681e981043c0c6070030f845407658806125441013008100c00f941c13902095070094859404146040b4540441c400040c0003604048404c1191860070807809401814110004540d0b00c610743c0d16240c8903030308242900592900c01e020303907400030710003c02610451a61018843d15012500415140c400296080c5c01500088440b0a010740e07400e82e0a150010950b01102e0303202e0000b0300b13039102445070b02012401c482284080c860712030314041072841a094400e03003c0d00855900141614017030a50310700f45e69600007050130041c50000103010320940c42d900844400a8000080380c100341c40c2080614000e03245021007009442c00703000d58104540880c40400c0180b400c1d200307030104003007001941e44500341540d00a41c001c0704804440d00092492450f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 408835449 1250 408834199 408834211
    0x206070f030f090501021b0601060804080d14010807090f060b2d0703020c01090608060a03020114040e0c0c010b15030f07050702060703030e010612030818031612030501121505 77
    0x200342c15046030301020940d030b0b040c4012682c40e500030802c80c80e01903d40c1485a440d008010080c00303030f54500f040140c108000944041d001c600005803241000b0415005000b0301c440c50021241103617510740384c0380e403601914021048102e0922400906142c0d03035000c0e03c0162031030b0044807031a055100172402c0d18072015007547c0c1c107820070250f810381c0c48110020213046c403240250083d107100544e02000400725a80703904600203020101c0300340a015200d50248600f625820300308402d0001444d141000700f406aa448401c28520401c100f12510340c019015106c8141c100009001207000c0c4c504024039180c5c88000d1174000340c81440000c0310314000d44666600702035182051441c1c980c85401040d030660080c6010f0307004c2500c852640d0381c00182403143c5401481136030100c40c40400c480d50000c1029070058602c015103a010a18240c1a440500483d90030080202462461800380e00c2c0803e40321000840c18004030b880c240c00041c100191441d881040d9a2101d4918520031322240864018007001d020307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 408836699 1250 408835449 408835451
    0x9090e0f0d02010605012037150c17070e1302180315011208070203011401080f10050705070222020f090a05030d0e120c09010f080c030a02010206070f03 67
    0x14440ca20361080c0104107954455078004111103050000140624040d010600d52540310b485903c0328a81c0301003207942d045680030322903880c0e02884145907541e540e05032220085118042240c40d080101820340783d082000c140d02e0601c0401d003040e2096404a640c1182c2d1000741c002c20000400c05882150503444c0f00c00005c01000520000e00003040c00c90b00050b90f00d4485051000c045403091500308010b5a401d501b01510110a60600594059050784c1c09801400480085100e0003191b4080d000012250300701c1031070313844a41e910704419942c0c4868241618481c0202655164542180e014151140c0c00985456203040c800ea4203001c0c0206000d000822040d940c0d40e054100c1c11000c2c0001c01c03800e10300500c070303603114011b802c100f020200b1150b0229100c0d602100c604608075400c00d804a841c3c400864011100b080c1c048612828800380c030103015030051540d0004905401c019412500b90b800c0d101c01c070382448980c481816601c0c0c03821900640135030300003400225801e102d900b900e40200c0071868 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 408837949 1250 408836699 408836713
    0x4020901081f0f183c060e0c1201060e0102070501110c0a140f0612060409050f0a03080a1107030c1103031b0708060c040308040e040609140c1002010c09090e 69
    0x81d000c5050161031308410b950014400c1c102615194500070840e000d48143d0340d0a181d4a09041e1103000a150400f0107643c40390115400d60045080740d1094004180d080c85011481c900690f4106c49584140d14410580d840e400021a0300c500c603001c2c000d442d0318103800510b40c4909040c015035040800c00390000346880b03205c4441c200394641d0802e4a0041c1503411168903007403840703402c001c0d0803d108140a80241024840e40b00090904145030342c101c0001d64000a80103250709145003001000c515400040c4150040c0070101035205c41c000744141c05e02c0e01c0803c000b003280c10040e1013a108408014001a801d1441d08000c123030481c42a0045220003000c80b0b103000e00103292801c95841a025400c4103400140e420031032003105018003644a580b010030300d850581540e40740034540c00340780920202c18490314002003c00c11107031f0003600b140307400c0000f010794448441c2c0d0b101d5a42178501410381c0940c11820074040c12030700500402490f050a80c4600240c1410b110782a001005e002400f2011886592 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 408839199 1250 408837949 408837959
    0x60607110319201302090109120803060406090c05030604151e090b0108010503071205010207171c270c0902040f0602010b060a080c090a0b04120201030b04020901081f 73
    0x103400069203103003010b94004916092110101110f102d0f98020200a08401011540d8000c50900543c90b007080c010303140e007490344c0122941199900403003030410000094006100155019520032101250180402911030084100b030305c0c119402c45010940a0001c0b0b440c42c58950008505849000c40001c01155140c00140520ba0a04000000505260018020248180a41e086440080c28444155490000401e50f190307002e04c03414200704c0001c11008104042034040b101c4668209130b559000a194903090715140d44904203000750401024180b070040740ca540190300c01200e0f044119050303005080341c0385810a096120840340c4d0300301d850021900314414030140001e00303040720b0926242801d20341c1c040d0031070320041c203014401d020602003402440d5002002d10790140d117091485443d40075031000300f0542c018541019212810201c0c002c9030110a0909000e503680c000d0380c0034000004001c082c4801c03813080c80c00c8207000880f0000058010349032404031140024a4040780710380c0f141d0303070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 408840449 1250 408839199 408839203
    0xa080403081f2303012d1e1d0106060e0f0301020d0c02030705061b25021806101b0222060905040b0603011a1302040b070c030303060b120606071103 65
    0x190032000f1000440010310309072003101e00356100d1019044c0d0080009401108080200300e9074003100139280d001d9031041c0861180ca64002d181462519440c64540c21115109000134046078104080416013400ca2607918080c14080e0604841c901c1d01c0381c0d24204010000d010200f0040300c2a290590740800c5241030701b040c18803490400020310745c0556240d1000d407030200c4c01c09a019085026030344150010380b402060403800c80d2200da8110306242503481055000d90001f00701818083c0d44200c110f02c07545405801c0d92002442010122030301080c0790000401070b502900e04526106a60648000b540010304200500c203881e0100b000c07070032012400b0f80c0045070564017290829014562124288010408003021168000d9402c0300244542c01610000404542d10206414070a00c0c014a1034584403050340d04590140c141410b419907030710024109215a40650301c0b040b400030345400c100003500311003c000c2e075120340340403038460106407504001c0003c00d8009040540e03031800d09164000e559502 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 408841699 1250 408840449 408840511
    0x607080a0b06390d0203030c030a06081006060806010f05090d02040b130903020c09061819020403050313080c060f09130903120e070807052e0801090b04020a08040308 73
    0xc944401c03500e003854200001c088052585503c0c4640c4441d000c07184035038000c011f80782d01002d0030b03146980340c0d40c0e010240e4004e070104d540203003850302444102d0140044140c0004003516100c1c3c580c1c48203511840c0c01158007020715400c0300c0016005200600c0c861030104a156206400284082201840c5100182440c0001000c8886003595945808100740d011300c151170f6044000c503000882d501d0520702003900d075051180070340e0260070340c3c4000a0381881c11100341100b1106141045445686a1914660302e40c054404420700d058034803c0001c100000048503018050701400160524143c0e40f4450896000080681e81c000076103440c59550081c64461000003a0080c1e0b500b034000c400811302c0c10212400340c040d103006a0000b001c244106c100015024080b0749090b1941641d816202004021010050804550360603c9070360003080d20741c0c000807840c1a1a442c000403c03059103401c2c10441244124510400401c105400241c0401e0140380303101da100345003880151038108c014282c0a0240c807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 408842949 1250 408841699 408841747
    0x405270916090501030317090f060903040501140a020a120504030611031e0402100c0512041203091706280f1e060e010306020a0908011802040e0607080a0b06 69
    0x404001c0c0006928201030080d0010710303440c07000300015410740d04c00600760314107185a0788103100c0a0b0040b031602c6408021041d204d81c44107041e6013950410f200c2c8261254050b10800b40003804404a51220a0800c2c0807200780c4150b640040c5a203514513a80c21060740070401084c01480001d0000101180031070042c000040c0014031580e0703aa245c900c4c5810315512068020b501c815620350108001a200c66481e00e013020321604203d20011020f20f4128035003170700c80c4020004000049000103110020b0311030007450314480e03218100390b02d07103c94011070100303406003200384540e00c0400429a01c003c034031744030b240b008603e8011203a00a03401405100b40c403014210381280e107a5603480012001c0381c00f029414203030b00c6460103010312071030420089080d04041c04081c2815074001440030205000d081004d0040230b01030300900c042d00220800e05042c5404200a0f4011410585580106203000c918917200d06142c1c0c5800b0200e4407405210001405003c5005070001340810828103405020800290130b03103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 408844199 1250 408842949 408842953
    0x10c1403070f022b1b0f03030e07120b010f06050f0703140705030a0206090d090609210b100302180402010206040f020102030c01020c0303100b04031a040f0807060203060f100504052709 81
    0x4186850010100c0e658401c5c001e001c11203000f45500041c51070110081c825405180224055010000d120b0606080398030180c00074501c88400340070005c8040e031003412076100b40412541290388034401c0e5a14070620f41034800d400700c104450000240180c031a00c041340ba008011600707060a80c2d41c0c9611310b0b4428055100581c2c040d600b013029100c01001050314445461501010b607030b01e010005404100f060003907400110110100810100742c60056a0165411000c40240d81c1042c0c10000680380ea00d000c145c0c0204a40c030300c80c0814090380b000182c061030303043e4010b02c815542c80d10366182c00030192200301c1c11400200003080d520f00d0300b4000f034661107500c08040c41d543d0521081d100c0d202801c0da400b000c6211014001000401c240c081031400b40002104480c40700d55840c81c00c921802c503100070050115002141c020b040c0001503000c1d47c401c1009840c400703014500e100810100051000c1e202c000a44200018400350906da441100ea400c1d103d4015050f00704861002018207604641b400d00c15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 408845449 1250 408844199 408844273
    0x604121a0a150b0c03040902030a0e150f06040207020f011b02030304170606091006120209031009061a240c070b0a08010b090105030c180a030b09010c1403070f02 71
    0x7240b4801080d000800e04143e81c1c1d8079040b0404540d5441e4052403003000b00c010b5000c130005580002d83e811041f04041c1c440c003038a12800950485000000d01a1011720350068401c1c0024580c0c102031084840080d0001c0800d042c80c200000119070b1315070003006050042c00c0b100301240041c1c070104080c0024241e015aa071801e45403e100d071618214006165510410b1480e00307007e02c1e44501002001a1441490100d204243d00a00000a0302c1084103071905407007140c40281c180c003000c1e031045114038030401c01800f05901c031707640c1c0c180c0004280e083c6c0c0e984003540850251101c5d60030400345014a003900c48590406000c884441d00384115a80440e0064034002521803000742d000d1a114090300416107114106409070000034510301000700202c1c1d00c0400060b04100440241d02e42d0700c0340031402008505520707103928002803010402d1712003250a43c00c20311259200d40c0a800f0f681c800415403202542169a0248100c0d01d050b410005003055001d210404030031010020030009120a40441d44580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 408846699 1250 408845449 408845471
    0x121a040b090f060c190c0c0603020d060506092b02030a0c0e07020a1a180f0c01031802090a0207020402090901060c050c0d0f170d09060906050f060604121a0a 69
    0x1d0000c2c0075a020102c0d00b0000801c00303044070480a81d03401c3c0403c841c11800c502c1c4c0c3c50350180c4174284c02040162541e90001d40c0040c80c02e90580043c00c0000c2c20a0b828003000307940d20148035a034005c2c600141e40c0400c080b13547c60380c4c3e1900300505441b2503040c090501903000003900824100407401c01d003035074040b10b0090b05025400302c11002d42d4200d00c440c4000d0510320513617140c582c240811050045c0040c1c82c818007080142c819071442442e00c01c0c43c0700540b280c1e200c424902558036070041c6a00340c04a07007085900c18582203030030288182580c015101d00007039035599428000950003407004a07400740c0e09002c018015250385c8611030113000e8903102c1c2400410030b81816403500120712107451044000d80d04110000344078400d8200b0b541d0b07010140310840c08030300d00c21130401e004440030303c80400e00d4610408180150742d0018144030f0f004050130012901c0f16240b8810300601107417643c0d01301c2c000b00700c00c002c05a1190107001e1001d0140c020341c1114455400c1203005404141c41d02da40e220744541416039 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 408847949 1250 408846699 408846703
    0x2040e041a09071205030702100c1104061d0a1508100e0c100807030e061017070f121406070e0f09010e070c020a0302030a1b0e04020307121a040b09 65
    0x48464100200d071041441c2c030020207075444040b03004a03c0c00200c01200442000010016a1551607006200711101c8240c5030004190020b07468003612420300960095000c0e0030180700f003006841d2136640640741c061311075000c0541340c00064003c80500c0d40c0c849a44a1190a855120014040c400003a010104000c420042510f00c949100740d00d47d00f0550150003a640d850f5280b10382c0540078286020700d42d071202001d60040c500201c81d60014040c1c80c04001e05500b400c4030120a41d00d8214810100d00c40811032180d86407100c0c090f012010040c10003c0c40224010162125820b2190129001d1030b0f4152a000c2c2c14500180d40c040042421014414500e141c10641e074440024255504501907252050792903d2801c090103000500c0704148100e015521a400385030055a0054100c504200092030701e84100e41e01c4800d03040b442403601601043c1048150181405142c004005044060504040b2410380d5a51181102c042a1050410301d01c0f01e02210000e00c01d0f4000c40c1e03030107000e00c0c08000581c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 408849199 1250 408847949 408847973
    0x20d0b040b0f0a180f03051e1c150b0c070f080109020a060c02010e01030e010b0604030b040c0e04050d050a030b0306070c0311070302090f071112030411270a0b0402040e04 75
    0x700384142450704c920f848840001094100c142c110b04981042d1401d41000e8551b40b1038520101d080d82c4440d00258881841c0c5c2c40200030f1000c0c0700300d500f2442128003114204543c1c0d55906409804010304c400c000361210f0070003a03c1d43c59914020b0369401036564814810300d4855038018901a51030300801815440e123044e800d402414103041c503c03101d102960000b4025030701808100d042c5955500f500f44048025840744181a001a1051359256120709018284a008590840305001744001c04189a013140030018040c9510400504011544160030f440a07000352814204041d070701c5d10180540e9030200178040c022070300c2e40c64500714500c9a0130020b101c034006554001140e405038000b0030040c0c8aa1251650104000030b09214540f900f400c11143d00da8500322039011445551103810180348444000c44c060b91085030712080c0112460140945040f18004813107091400060180b00302040511656000861040c0003401e25600f01c0060100c3e0820782041142d5044101040201322101401d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 408850449 1250 408849199 408849211
    0xb031f08010b2706100905100e1e010c0602280807120b01090b0f040b0403030801081c050702011d09090a060501080606031e101b02010c0309050606010309020d0b040b0f 74
    0x440107880922641c9084400040d003642e0150101c02c005d4103a5a115003020070142500030261a1459031000f401040c1c58102c40f421440390403c80074129210f10494444000d4040684404900e4021525034800035009030148079402c01190807026410207007580c0002c0700c100703192034107146130034101c43c014a844500c80c25a0700c604d14100b840d401d41c0e03806c4100c9a00f11209540c1c119038a0702c50101001142c020b40c1d001800c065008180807040580111102d1305039140301c030454801d044200c40390381304035100c0802c8401140d42000f120300954414400e01c2d040e038203a03641409400020030003060500714116805e5007a030f00a1400541042068001d650040000300028a42401c0c5400040d4444483d10340d020024501588060003000c4103010342040803a40850070401102d102c84c41c000524882d01040006510b012900d0045500030721130241621340010050600d50703110303001940100155041a83e0207501d81d0000400201c094140c2c40c4518070030ba215851900740342c0d9050403040390180203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 408851699 1250 408850449 408850489
    0x330504110409020f10050f2803050106090303110c03061816030804121a0a09030e0117010504020a020f0f01060f0611060c090a0803070b06090705070c0b031f08010b 72
    0xd160250b95241d0002881d028216000c14045030044801da659110358450740d01f401030003060380070108400240740682c2e800f2080d0782d150188440a0100c00f00c0e1401d010b05c2c001308482900500100f889002e12442185120003251411884031000178901401141d040c00d00c080107922800300300c0002e025441840a164000e688800e0a581c0c3e100306500640c000c08102c0c0070110140c109002205401003201614101c00c041141012504a0080c10070f1440035804590f180d03a110b400340d40300701050307200d942c104804108203908100400020f5800340a4200440c4910094000701c060184100c1c40d1002c0000d00000340c46144c0744492003000084c1e441181800075068030036912080116215030f10800104070785035124242c8000840080032500042e2241c4004600c0304100720105d0340c1103000b94030407101d00c0318640d50b84408585921070030324028554102d00c80104608001c0704050f40d0080b0301c00703c40c2c40f8108807801150100442c2d50b8810304580c1c2d140e80e2681c541341400000107a22107103802c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 408852949 1250 408851699 408851711
    0x60303090b1201050411160507060f05040b0316051e0702041401050603040f0c150f0201112106060d1e0b0d1101080403021c35043305041104 62
    0x103401407842c08144034a50081c1d0300c550381043c0c00a000b404a41c0c0d42906824101110400c508000340d80b0030702c41c010500070841101160040318020005d5400312482e0381800c40c40d40c2d40c1c2045d50400300d0383c030503500c0090100500c48600c914070f4104e440c482c529000c4e407409440d1139940c0100000d071503081421420100c0180e005010700d8840c54100e950168206694022185035807034041201300999100c0c00d0000c65512980d010741e40d000400440c99181c0f98000c1c0410010102000000d01c2401c0e91452035000403800820490100301403207601620052255050070079030303245102580d668940c80280002105141d4038012a14441c440c40c1e110165004103090820b50b4a103502041e5050b465030602c0031850001d030425108000741c1c6840341102d02c00315403c84000d100a44111500c04800c1a480d0200f400b0b030b4500004400c44120135511600c0345483d540301c54442c480f5000c442501a00b2440c5d0004c1fa09010404e03010590481c654030181c009030340c1c40d103803c2121800a150002a1180e82020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 408854199 1250 408852949 408852967
    0x5011803200a0209422206030501090506070c0305040506070f060903030b0a0b0903150c04030602040b040608010506071208070509181b132304050a060303090b 70
    0x200c20540c0d03040d035481060007a21524040c0e850820402c0303000b940920800308005104024100480d81a41d10a080c8820300c0a540d442c40200460411146806254091342a40c549003440785284d0150505158606e510016043c600540303034aa002601c1981d1100010010480104000d40c6d10481c240f40c148618071055400600b640b16500c21107100c1d2a000c9004c0d400d02400d4903610808503840f18040055080718600034000d481401c03091480380410002c001040905081141c4100c17900402900552031034540454007420040c00e15442da010a02010001075010310081c0003602103080b1031505c1328608000103050040c140c002c6401994140000b00c005020078540000148035400d01400580c1c8a00d030458490042800043d4050b5580c4128810242500e513400c0c05003019411100c00090010f0b0b10011a01c02c040789900c25040d024810021000d40c2000c10360700b07500e02904500b11010a2000506a8200ba0b41e28226590351b45c00400415420141c4a0000c00a0707560080c1020016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 408855449 1250 408854199 408854207
    0x30b061f0801091a0d0605180c060304060905240907060504080a060c121104050f0603060915150403050f01060f0602030d020313080a0503090d092402010608120705011803 75
    0x18443d01c00c943d40c5a400c42c001c108900d140f44e903607010004d051030307881d10814201b0340050300703094615443d40d240956200700407903004100030070600c501600300c92075512a1760b601402410398000591f0b4601030031100b4507020007210301d0b0101400d0000c404a440781005da0203541003240503030207141480070821041040c6c0e400480c116255580000001034100d2403100192400a021a280c0c0783c21071424003203c00c0c60945002400943d04180d4081401d61501e8080c00900e1006903500e40d4005082c4001810030741c141c41c0c2d0040c85441c0607181d00340c2141a8014421542c006803c21900c5130031072010b001c8410000d214940040945000c9204041e2a080000e2b449108040784211144c0e000030000b02c2040c00694101d80c0d0326031005400b0390741c40052800400c03a8000f40c8616001d4002d2404811400b44501d4240c41982c480b041d030000104034034864160314440c482c9100e402c2d5520b4403800a001c120500c1181842c800070701c8803940d15105450001e08442c400c8102c00030422075500c0c18808070ba48 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 408856699 1250 408855449 408855451
    0xb030a1509050c040e0d090e060901120c031b060e03060f071404080706020d17190b01180f0f05090c12090f030f040e0f07020d08060a0f030b061f08 65
    0x5600c0001071044150034618180300e01120701c59046402d00310f056030000d02c00103000b403039a0081d0782c480003203980b902d00c1091070003001c1d40c440e60301585040060000384010040800e1061184d02e815081956940e1910003c140540181500e11000e01040041176004801c0b054401402c03809040c071450f040c454070101d010091b152008000c1032042c01340403006414121000303000f00008540081c0e949040003136030344204003080000503105400010182c218002c005014800340140401c2c080350354510000104030025080d03041102580700714201101ca11740320005416a0f110480400e42401c5042c0c1040c511544041d01030117800040041940982c1c3c02c2d2140003150203440619600c42c100014078007540c1c01d60002150100250030f0b8024000100104201c9035140381c1e4540c41d41e50752031802401c1d10115180d80260b002a110321401c54410302d11307141d03c440000c280b142d000d9150311990000381d5003900122a400d07090028010a0f142000e450b403102841130410701e00711621500b0003001900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 408857949 1250 408856699 408856733
    0x902120f130311120403080301080705100207030206090d08030414120a05120714121501050c0c040b1f08040525060503040f120203281704050106050d05100b030a 71
    0x6a4400442c007000f0040c0201100c609030f10400e1a1180e4813418188110b500a00c00c044882c81031480c0013409007000840015820241d802030141a40385800b8000950b10241c901c1d68000c09010000f400103459801450245000300b0822007140e131120540c41c030b042c0111a007070345010028001074107072175445011200440c2c449414a001c40e11218019240a5410300300c5005000021400d100c0301541001c5580c460602c1c80c042400c06002000191010700c58001c5058454010000038009401c09800c12440404090b155007030424001c111406602c11214010001500d0380c001c1c4018001d0410007070454030690b00603541c031380c1080018400108403d10540e400d01101100140601c04449440b41c900d640190001880c00807100e4025140c1d400007800300101c0d402e4007460f001c14160034003034018003500c030303260341046c2c1840607856400343d0b400500c01c40f410b6480302d0000c0782c19140c032000040f0640c0304000030540700c0794400451050700c0c44002d1160203a401a612407001c2111041d410301521 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 408859199 1250 408857949 408857957
    0x807050f04050d060b03060405030a0e09070801211b05030c0f060702010c0501090c030b0105010f0201060b0423030f0309090a0903080f0c070c03140d02070503120a0207030c0902120f1303 82
    0x1030035032404c04080c0040b88084c41c1d02d401050200030503c0070100040421954556415200350355071020000007010586400c000118410018804c4c004002c0c48119602140e0780340d01c6160b4155036841c2d00c440d503035221182813400c25110411090408100001c68031a045030007406018280002c16014020900d000e410080706020b1801031000c01c2d40320b04181d5412000b1100c086459092a007803800007849001c2c00500c9145103020781c98810f21800007034403100c642c501d01e082d251504a40f105005554290012414031b008d462031030781e08000314078506001001454071400c2c29020000e10a0700207244d44140c505141c00e000009a000e240c1c00e62002e0120364904444c0c48a03500507085004d0343c480103000c00003010f00031051150054202901c001e11070219a03400307501c640c0403a25014279200b400c0d050342c04844102c909150040182002c2c5a03284115120103a60780c55540e50108140d1021a02d25400a4410881328250060300d80c4188071140580290406910f403418103115138402400700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 408860449 1250 408859199 408859219
    0x5070f02060307090e0109140708090706030c020313170f0a03020d031a0415051504081e0f071e0609120b0a1e05180105060102061605280807050f0405 66
    0x444c082e8103c58064150072085820320768507039040b24000e1080010f40411107200100081d1490300c10002284204d014001403c0040c3c03400304160054222000c204055000c10301002800900c580907490061050000302c500c0345c0d880d41c41e03150074480210110045504208618030100742c0019144c12104a42d00d13001134000c10300180250030b07031a02000140d1107828000c055100300c07019412101a220308a4102004030760044030280d881c0b0a42c07040c0c55441e0807000800d040c1c1102c0c0300340c0c00307270001e107600075a142c20264411080c1482d8040e009005d1080031101c0303400808207823241d400003410007418803e030f82c242481c0b900e407650860054000d2a0441c110001030300361311030340c0180704a10b058481a4102000b800740040240c00112003241c42500b240520900c0440140200c40c010401a005040d46443c1c002d00c049144992000000503c03500f041110741c0381c5a9603480040000c42103000400314440e80000601c1070b04040c0c2040200102400300d82181e02103502103070101c0343c04450603188 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 408861699 1250 408860449 408860461
    0x102090a0b0f030f0703090f080c1b0d02041802180f0a09150515031209090a06260c1c0302060708060a12060e120408070807080303061c0506011e050105070f020603 72
    0x87c02c6407060081090b038203e40e000c410481440c01414070201c5131019070702c1d08061880d0304c007403030800d00c420b0a0f030007141084814054202544103000307100c1003418145040b00c060b000315080c0f81180140d645401c1c4481c0400c1030b2540826009504200e0050b01400b200391151107040c0400c041042201c1c0302c0e5540c10101b50400032600a6403031000300981918250b5202a150b11842d81085411500662240000902d10000b6114031010340c2e81c40f03103130403d05d41d0f014910210084000402107441c0d1203000100441c1c0d40c2e9205c2000303001c84e03201903c814919101d16009041c9030000d0034210902110406011107540c4001c0c4100660303800307090032007074802c0c1401c4c11009059102c45a410070300418070208245030f0840010001d5406110468226a5540c10f08a07510400c51080c0442ca41083c00402c90314a0f01c0c00c0c0041801d1044000414801415141d640c14000c0aa204e0040c20404410848040052000d000300030322007402c00608000780d580300c01e0714154501c1d8009101c0d80b0300000141c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 408862949 1250 408861699 408861701
    0x19091a040e28060504200d05040206040b040f05040c0206070c02062a10141b0d02090303160506011a0403060203041b090c0206060d0f060b03031603020102090a0b0f030f0703 76
    0x300960303189101d00900c076510305000000c3c100d9004407070050b42401d1003140d20800340c0c01d54407001961950040d192407460345240005000c00b0b0b00890380b111003040b0002d981030318a40074001815680c0c2e0401c102501d000700708000c0b070b400048040b055411400402070603503004480488002c0c2c0542d2301035512180442c02158410007001e4604581c0d0b041a000a54203030b002554000d40000940200a20b0b07140030440800244100c50306103041003480d01254031501e03a84054404100310764000750801d20703014000380c00c40c0c122103c0e0002801c20340690030203004040045074014450220080980002c01d200031481c0d12407400701410564002001ca010489074031120305400f0340c0b600a80307600310f85504461000c1d121003603040c0018824030001c80c48614110014407407950340001c1c107000c01141960307002e015140f250040c6074140014070004a402c000000d981450a1007540010303901d10440080080850440d04680995001817007280441c040c100c003100d8000301745240c511010359031510128 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 408864199 1250 408862949 408862981
    0xc0f07050715090909051e0f250608010b03281415060309210d050f04140c01051b1f06030203010f0203010812160c060518030d021f02040b19091a040e 66
    0x1580302e2040709c1081c00c00d5500f418407003a0440c001100800403a50f140d01c00c550b41c1c2c034203000304a604d030010804590f03007040011207a0980054009058541001501d210040781c543c86201400c050f4940304200c000040b888000070440030407034101c2c2c1181810800c09548040084061540031503010301c1031045901201940d900c0f40e80008140003034a0850865551040159401c5410705080b4040b401e241d40d01090040881c0f0040c0c0d0f0b0340e8140340390b242c907140daa008480c00034102c50040712140c403030396191400d18000c0b03e140800003095003495841410b0840324008411941c80d40f06200501424030003251801c815019005400e444070348855103013811910010300148a4800e0250018607a904000504103044080d0900800c0c4480341091503125111902c1031001a0015180c907161007040d2100e2062030458090b005041c151200c4444005602801812090604503624401181d0b800302581000e8481c1c00340b00500d154103001980628011800303900c1d40340709050009103004007841218 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 408865449 1250 408864199 408864223
    0x1f1a0403080d0605100c111c061d0c03011104060503190f0b090112020108041502090909030417070e06091b070f060605010c03080c0f07050715090909051e 68
    0xc03a81c0c4240ca254800010800c52040c40d000d400090b0700000458020f100010086802c4031000e44440407c000b00403c0200f0101860f48100640000710041280d501c102004c001d030682091803100e00100b1407a1a1415072408039101e0f80c10a0020060000030b10191400ca5005040c0907031262201c5060355101211116076108180c904110f0500008845c2c1190020a4064481c0c04050344c8070807000c580d510a46a0203030204d0602400306c0c0001d6003044003003081d203a00c0030005003400942d400043c41d40030191501031041d0301c08107061080c0c10502041400c00100364001305003203460640310b00302454000340054400c40c280d4000402e07c0020300c1e00303034503a14021208199901d110b031424603540d0503000005c3d54524a0848042041e502820050700c41c60f070075860f4001039a5491803140681d500400d0140903005080c0482400107008102180c041e1142c00f044403419500385100415080c0980d0154825138103100000011900c00b00741560b085101410000400344082c20300c0345009812044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 408866699 1250 408865449 408865463
    0x20301060b0c0a020405010e06030a020907121a03011506090311030c0a1e27050402150a0207031403090a060509010327150504030504050d0c03120806091f1a0403 71
    0x6525810040800c42803030f8980308070303070800640e43ca41010294000e41182c0f071030707015440b03c1c2c0c4c04805854410300d0035610a00c24070307103d400405003071240002e480c1c20b8049041180900c107400710702490280605003a10b20742e00a200035841c9015070062400706103110103000043c01d503000c194180c805000d8010070000140c0660241030355640d003107860403806400d201a400d04943c0114440550101800c01c025035004a1541c884c10594944020f00002e04220790054862400c64445415a03024003032001150300600070307491039130900c44000b814401d08801030303030030070441030000341c2d5140c00200c240d80d0030b4a003030303034031044003900503001840701ca8445041c070f102c0c1841e4110724841004460303000354461907076100034012a142440070b4078400ea40040114109004c10700040c02d00d0003110048034024440040110340d240c680c40c2d084c0c5660448840002d28500070014141800340710280c001800b1854001c410824034118494008a405282a801003000070a24180c4240090320099504148 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 408867949 1250 408866699 408866707
    0x212070c02040b0102010c2f0604210f021e19120e01090509040f08040e090d08070216060f02210a02120c06190f0906150b0a1407020301060b 62
    0x80040c2900c5524441284918100103400d141c80d4818003460502c1a107545481102071f00b12a1540200d25030003200d0600b10540c98083c9145420420042c0c0c00f40d03016a1000c01002945c4940218408900c1005070074002001e1004c00b2180c0d0025842880300744a40e01c8580980321114070505000403049c0c5c5401030642c42c0c0f103103814007140000246800ca82d03902e803002240008001941c005001e40708655000c82c1220000d0080f41030310800640079072142d4a03040c64a91201001c3d8070440c0140c4440480ea0b0041140000942e0401c903040d030000510b0006040c410340303604e4014141a04c6008181c108002481d8003201d040c0200600b244d5404114404640c11100107030404042d080590540018171503410b41880404400c0704a4054409c600080c08150740d501c2007a1909500b10600c01c54015a01c04e0307034805804c840d2040d0014a4880c89020032100700e414248030794010107070800313800100200515120380da000250f00741402001207030941c41d40c41d540000b038010078459104400000e400030f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 408869199 1250 408867949 408867961
    0x6090604030f12030f0c05030406020d0b06040902070c0b0712110f030d021206010e2b0204050a020315100e04203c0304020d0c03021003020d05160806130212 69
    0x3c16034094060726075404200c0d200004640c0c00940c0c4071540c0c1071000c140100003080111724250024071a4081145000c11400d000b5408510715501039440010b2055000c50302c84100300070000c091000303085034407440e42003102c00d480b1100d440010000c4141401548990004d440e4024003000e05c0303403100c0c02c040d00e80b00d100003140b80300a94091007420300d96490308400141c0ca980039494010040d0b030060480b4511000c0101503105400302092204403400d004040e900060f0365070300074203105201d00301707000d0303128148500c03010196140381d000240306a4030a41c3c0202c2075580042c8618140713104441c04142c610048107001030fa29010b520410344031400043c07055480031942c0c0c26120b003d815100d01c16981c8614029641c116481c0b40303001901442c20800301e800b624080c0065001c150181084882c020356a40c0059415000c80d040c0d1000700e0380220b6001d00380c04480c801c0d075a116a00d00184070388043d4050004200c04c42c02031000c0c0c41040281400c00301003402d0b9042d0342100c0382088142c42242403103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 408870449 1250 408869199 408869213
    0x30f130c0b1209071208030403030e061801050609042105090d140f0a03021f0e0715030c1b03050a051c0501030b0901020715050c0f0415030b0a0b0906090604030f 71
    0x40c5188081c1c860701c50000c02c9071101c000400008440520218031064161966001c06e158130140040d0201510340c100907031851800d01c80300317003e490501c42c2d18002d000d0b038a0312582500e400034100c03803041d4080b004004c007145c900e08603029102c0032000201d4003208903400548840c000e41d40d00c9074105240d9030040341000b4102901c10400e0320a14102d0307510548040312240c0e0f0745c1400c0c000030b00582000711485008030100309600007201c18500c0c00b141d1540b42034001e0389030004503840102c0407840c004000030401d4141c0b01701082c80d11709107051681c0341c5140904040710140104000c003040400110b2480346031060341071700c10f00c0180050851600540024510181030280000d90700442c0040108a0080c8140308a501c0705902000c0d480404c40d00d00010001004020440405880f0801140d940312b05244010000340c001201080140c0c503c49900400700c40144036054011341d440380c024041e407407681c0b05403588420103d40003039517462094003041c82030080350300041c500b44080700b80208209039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 408871699 1250 408870449 408870457
    0x11826010509030309100c09030203030a031a0607030905060a0e120615010503090a030309020307120501052401140706230702010b010302090f0d0f12110111040506030f130c0b 77
    0x6000240041c0c1c40e4401202d07140d00c0151412011540900002c928500040d0420038000c2054100b5214459603600400c1c1154421594900041c1c3d5030303444100c1d28018095501d429120035207655041994555020f40700b82d039580940c03407150b040418003181c658070070340a01740244405401006422900c0c0345042d80c50500ba00c038081c1d4403a6040c019a00ea5104600b980d01c202c0c1020000c0c0310190190300c06078000c00345207009a8040c00b0380c050102c0c1422446000d41460352156000142a2501074a102c4402c501544014040303628084c6921060ba80a8450080c2188035280360342d6074100d82c907102009102d03001c410800307094528400d140704010300d810b0360711030401900280701c1000401c004400304e11503c40d0069000007400082000b605201410f0042940304016240c0080c0481d03c841d5041034400f44c00b0030000d55843d21103100d0290a014240440f54500052800c1c0b07410140040e4440c00300604401703a04014200217a44038400006420080340c015580c0303007800f034030b40c8070102081d48 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 408872949 1250 408871699 408871769
    0xa050f040503030c1b03030307051210080613021504050604030b0c070c06080f1803032205160315090c05040b01030f240e0c030a0207081201180e0f0a020118 69
    0xb078140007400c178505004c811240320701d07504c0c1d03145450200c1d02d6185285e145806802880e8003000c3c00000f24244000f0000240211640e200c40030003408103204100c24410b00d0201040d05c0301042c0301c10405915000240d90990340d00500b0b0301107598903208214403034020700601a080504900c1d0001c0c03020340000380140244038661070701210b540c0710031410500d000c0c1c0000c81445c580c0104000303500c41400c10035060801d29005e040502028035515402d1074111f685090089000709181e081081000340f06a50342c00085580c2d05102c05034542c0c80f818042e80c1c041c843c0c14021901d5a401060981c441d90151001c0030520740c0410101509020414100101404410340c400e90401c001c00c26405441045200b2014210001e1850f40d0741c0034100e000e0740200508884e9064140558004d4011006c412806004200000d038192800c40d64114203440035201c0718921034000c0c804030f0700072030070214446103c2030302800c1140b099040030404079001d016591040c0c80700c0d8862100d10340d26220800d20070850035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 408874199 1250 408872949 408872983
    0xa0201080421050d05090a0c090510030c090c020c090f042012060106020d02010213090f060302060318100207020f10090f0b130803130e0405010216060227060a050f040503030c 77
    0x6c0d48007441d1a030740c5c13120442c000d80041071108042104103420307007100e40d1120b04100c3c2c0d003185d180e40e07540b5800d0380891500001c0c8010b80b941c10362540294104011040d00e0030480705403059040200b0140074040340076001801100038404800584410251031880d0110f02511403c1508520201140c90394400c0c000c0c5001801544000d0000314414005d880800d00c0010079007030294074013000080100a2800290f10243e103426000015a4684000e54030601c4038240031030003180801102820800583e5101c40300d60701c1030221002507103801a881b10b40250584100b0100c08600c1c0d0180c0309070807039034008094007001600c04545090007401905148040440716104c0a80302d40480d920303402841d0302c80019040c2e0500801084500e05030b0f2680181c0036400051504088071409004440091001d54505030002058801c8405582075404400c04030403240c41c2c1c40001d400095480d110b110002410404046010f4030050761007400c8030300610004044035912820070700d00c01c0d218400f1200c01d000c48 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 408875449 1250 408874199 408874201
    0x170a080307021c0f021e191b0605040f05041d0304090b0307090c050f180d0b04030e10020303060103150e0f01050901080d0801090905030705120408010606030e0a0201080421050d05 79
    0x101e400f0781c04c50030f0982c0c1650003804101005421079018204881e80400c03080c07060404503030541c4101c0318203d1825001c0c4440c454111501e000c181c00c40c0c41281d100314104402084100b040740c207c64111416900c0450707010601800c82d400740750070800c81108034603ca00000500058100c9594090550141d00b030701a04c44c0c0307542c1c814a00048401001811020031010020441d519901c01c0051004841c82d1030100414440040410f1441e90808800c41d101074500d0305101c1856009960038403400021100001a0342072604029268003025064505158440341d000c1c0e5210100b80004c40941802c22401996160909614200c4c031400c2c8607481c05103491400120b1410000300301158090503d444100f101e0340f03404c1c04100100a103810565181c00244103050010f035090046071140c10f4090901d03912141030000082c212200c03540040145403500750b441444c800d011070b89001240c4c09090101543e074460400d0f00e4005110b010315466020169900c2da03071075030407402801e003080c2844420082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 408876699 1250 408875449 408875503
    0x90114030f0622090302150603010c090e070c0b04080703030b0d05280b0a1e06060215061f08070215010b0702091510020a02090604090c170a08030702 66
    0x15100541d09405038040c50400101d0508210320110310401c000d01110701500600007403001210400f40c0100e0041e000f40e81203145081c03500300b0707007900448114003c0015a030a560b021740f244605c1d101c0d00b81f100c24440001950507000d84d8008562a81025014101d1f00e045e240c10340702c030342c002d003001c801103850b00da1001003504200b2840348041d58000e00400861840b8006025022401d007c89501e44072807102c00c0380050700c5281850302840100ba40429840020a000010f038110a0f501c24a09498100104100c540c00900d4210b921886401c501c995115038000c1204078142c4040d10382d642d40c03c0c10750b84003101d40c1300c194a8825052039003500c1c541082c2c0100724081e0381d0203216000e600c1c0800c0c04040058030b003141c02e0329080301b2300810307013960180050086038a0708508000140940c10085c0c402e000d5003400352a203544904100c404106441c05982c8007818500c0d41c5c0981404419054803500350808100000b1443c0d941142d116912032811010003983c41c010b180700c10b6180141416440d035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 408877949 1250 408876699 408876737
    0x810050a09020a300605090618030a0507060213060203040e01090203060121270302010e0c0913080d0f0504060e0a17070303110403140607051603031109090a020901 72
    0x4903680c01800c0b0381c0b01d0f078684528030825941607000350308690002652450f410382034941310740302503110726030200720f034500941260f042150083c0b5014032140c5000004600007808000c407000240c00f0f0400d56103031009400c20b80028029043d6a8081c0340c907111010805680000140c0704807000064852001e0fa211500304003a804242c8015005c2000c01440002019512480c40b080304141d40c4001145511840040840000c12940c0c40000000c1710300902070542c280034020000c09287c0041149040712804203082c1c02008090740410110b2016a00400c0b41a5040f15002c51080000b404004005a0352400429090720211003031490303e034518006101c003181c2000001d40012030003900180c0c00c900046c060340454411030400da0740e03400c84a041249580600302441c05804241d00d44080c81071060b00d040c038084c1110b024080d003400401b0203131718211080121180c1c076150108543c00030030005003941c002d0341843c0d644110000c0c100b19900d419079000d004007250982c0d505940078040e0440c0c0c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 408879199 1250 408877949 408877961
    0x9080f040602012f070204050c19030509010c02010539120604180c0e13080c1b010c0809100e040219120b15090f030a0804050f0a05031b01050c070810050a 68
    0xa1320b4008117001100140c03030305601480c3d02c1006030b803825117407034110001441109210b0083c0300100c0c1c2e98100f8400007400c2481030f105c083c1d115000070011810041000440030310305054040d010b010701c2c0f5442c440d11242e491405055030203685083d071034040d51903181c10105002c0b664240502e280c01d42811000440f0340340524900d411460240300703182071020340100320324010305509090302020751003800a101e81008100101c02000509100c0e40d00803011000400c0581545041144506105010403030b124120703041c0d074800725582090280c40400507160b11080300550342d8080d1002c1213981900c4d6512182c200000203560301c00402c03043c0107100d1070448044c141e4181d0049402d009800b40c0c26000700040a142e1b03070007480d0701090300640d80040d140204d007a40440300030001141c00c00841c202443c03405010b200440740040c805003805c0120741d440420500200c2c100c00c0004190b40aa4010400c42e203260661000b17803030b069503d07078805035901c4c0412501e0004042c605800180c070540c40b407042e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 408880449 1250 408879199 408879281
    0x807060f0c0b06010c030e0303040602060a0e062e050a060c0606170a110f0409030915050a0804020d0c0e010924034803140d1209080f04060201 63
    0x20841685a480c0115524070b02c0d03170011018040da000c40800036980c204090030080c8450b60060419243c0440e00c00107030760030b10b6403001e9103030300003801d1204d00f046010303000d0b10103200314014070000900d10704d071320015514680c01160481151200498529800b030b400030742141c001d010900896076542a1405480f0381c035a04900e10360409040c041c00141c5a02d842c1840c100014044643c46e20700030f0004080300c2c0d4031a4114017003044913800f0030510149808000040b015030401c1420070008000c00b40503090001e200038400c0310100c0c611000c1000c0d0394030000107003d11105004803580c5403c007490040581c0b0200858004d5411121503020700650403490650b039001d60070204406a400a501a150010000369081c880400c200a056020f440320249500e4001c28402c1e00c0c1c40c51340c1032100800c154007040811a410003400c0001498020001c05442d003015000003031502c4240c10010810b000e005000c3e50b82c4c00d0002400641c071581504051042003110b80362034054221903180702d80007201030301c4c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 408881699 1250 408880449 408880463
    0x1505100206090c060901120203010f062a03030b0301021606050720070b07210210050109020a1d1c0b0108060702030c06070e1201090f06050705160f05030906040807060f0c 75
    0xf00364a5041c2000035103000d04042c1094001d91614500c40d80a03600240c0080310b2944c60458200706c00d581c002e40c1e6120b030200d40d422800010185030443d42c07030240014000380a160720745228000a8500354111020300c48a00c459061a00701c43ca00b05002d8001074032590001810043d1101c80c0000b1030b41e02c9804804a0401002d00500d44100741046802c01c0c8402d555030100c054000d17001000140f15102c8c6800b40d07a000c1c1040303c200b40c41c100c0449034107800c220b01c001d1041c03048101403a082000081811024990200d4180b82d40000403c804041c0185030310b41c11607100ca45003084440801c070f40c142e9507220b060301e401b44c0c4d8003074040760799005a0255442c950300800c041a5070b0750103464408001280034002004ac00040746016007559500c140132584031340e03035000741e000344002440342541150042c6049403600007a586800695428003601800c110355200f90441005003c00864550b12000340200d501c0d1603580c00780d59200c001d50720540300494003001c03500a0491060b0049151030f980204 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 408882949 1250 408881699 408881713
    0x50a0e06100905030d02030316050316230f090909010c0c08030a092a060905010c061a09040b0106030c020d0504090e15010b0d110405010c02130b04150510020609 71
    0x10000d07448041d003403100911140c0c1c007010445403414801c80650650507002036035a41041c2d107000d1284401544802d08201042c02030012500c107910401d440c00d10030303241414814106a40c0e00140521009484003031b0780b80064010120400b000140040200480320707200e590f59060344480c2070b100384c3d0441e0400a00352255000000300204003070b41e0400340c07508001500070b101d80c0c1da041c00700001520103101d200171070080d8402c01e13548092842c084d11451910241c844e10b04030010b03100702514000100b0f450b88901c86103d10301c2c0d811407555020741004100680500702805e0600c0254028004d54000a05206407180f03124000100702022410175030710a4945890014000001c00c8005400480c500072040c2d5a180745061006132406407a41403016592101c0402810f4221214007503042e00e500c20501040000b070f80c11514400142d034040e1800400100300c80c08030002802c10300c444031760284c604115100299000200a4269103054840c2c200102041c1d4007a030780e52030102d074200e4051340071403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 408884199 1250 408882949 408882961
    0x151112120c09100e0415060e010f050d05010b070c0b0f0316030f140105040c0c17030c1605060114060910030b030c06040e070207230f0a0e070207030c050a0e 69
    0x4000356215007800440c608000d048000181c54990049150000600b0440030301c105203402d04c01c5c260004c60a01801850350b2400002402c21254003030401d05200300c02c201c2e0300b8021b00503021a21100f00d040380401281d07841d82d0000b001a04035200540c5c80b640440000b007800c400c550300304e5242c00380c0c0e92808c0381180c0d55129204070803180e01c1e0309081007603183c0d1036002c00c8007800e0042120b41010800e4161096040c44d051008031502030328501c003000410343d03c8202140c00c9813039104907032060340306842e580c6c0d55815401429114030038070035001040d50088082800804a2064180e800d10b550784401d00c00242c003000302174090401d00c11340c4602055400b040f201c0c042e90042203034907009403c0d01c0c0070301e600c82d002236a1034101d80d00501e0005070316420055029410310101d000b07000e04080c00305901c0e42c643d2544c952400005980d5007c0d5569440356401666118207060082c0411401d08266140c40480251100314500c0200d07071924080c803003c0303035500d4400440020b030342040d401c50000340c1d00d0b1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 408885449 1250 408884199 408884227
    0x70801080606040b04020c0615040c2a020103091e11060702010e09060a0b0d06030b0c03100603050c1920010c020a11040b0306090d080603010b0f0108040302011401151112 75
    0x304e900d0b0740d01ca03074200041c5098020030303c50301e07101c3c20a58060700c1e25403812200b0702003981d03000c0d900102000310307501800980804070400f02458400209040c0360701d1503a44016001040080005001c0e042250140100c0b81a03621101c00120b200710350344421448040180a41d5018500000b400304480345110350b140d007000d01001b54408001011101056a10301194405520109100c550aa02d031401441404070740ea000700d411414888409103546403140410700311110a004c0d11041646036004103031032940e40303401c0d42c04d8042c04510315150b10b54401c5001d0325030814903094100d10b1040400c04900428180324000380c9401d10340280c04100304a0340c882d0440501c514100341d00035981c07003815403913450400c1194400c2c4c00000080001001c0b010014200040040c00d1a01caa81040c246084030f07259107208040d8900282440d0150751034615059003d400c20000030700720704c503800700002194121600103d644496078ec8a80134611180380e05191151183e200ba00d1003103408005036a090012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 408886699 1250 408885449 408885461
    0x30c03071d01091820131202010c081606021b010b010f081609090c0305010509010b09060f0304140109110a0e012102150f0304030e0603040c091112010f08010507080108060604 77
    0x6034030002405148590601d442841030909074003100c10082180701e00e800700c0f00303540c102420807904104622451940020008180180300400d140740c040340d1460b0b08033380002840394039503001000355215540d00c40d40c14a00d24801341036100c0b542c00d00c0101b000c154026105003a50001d50b9440312038a5490b2101c60f810032400501031010000c46502c00542c407004c52103542c241b000d0741d0381c0c00b24687d40b61004210316040180c1201700c1800040180c0419030792141c04940141880c50041070302c0303543d80e017001c3c0e404a4016110341803c1d400c041c008420003074a802c024140702e608845500791142c440c0794040001809006100c0c14000000001c40030210181c4800c0006100800c864050b17019042c01940350f4000428031b4480280c040284010981c0020a07140500c00035900d680c114034154503444040303a0b1902c50848501d0b40ca20740c4c0841d00340501d00300c404858500380320403415607540ca075482152149104000240d40b800010506140c86059618100c59a9000401e626111582000001e0031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 408887949 1250 408886699 408886739
    0x8070809070509010f0312020d090302091b03090109021c022b0f0308010e06040b060702090a1b0801030506090312011707090608030703021b0a06050903010908030c03071d0109 77
    0x411031400003030598a46168901034000c1da5141a031191440c0303081d81c81c0c1c181e500176600a641103200d11103242a030ac1040c2d6422203804030740c2500252655408410f1400c0504004802c0342d00000801c9040001504000d032510b100703940e400550b19107807580200c03040000e42c00075402030044600c0795054035144208010020b40c2d0203c009041d60036520348854000000044012a002200400c0304039100900f00d980040107032018008030042d0400241c142c850500b000b4407401022000c03c1c14190558048440a801c000d44001c8085000303a01400844007480b04407440d105000014002c42400320507250760300d03260b06104000d45d0030b11200800407240b2034102c0d04180b00307641d00000c0e821868010b0300000e12220010303603594110b601b0001d052481c042d482005800e44c0000c42c0e41e4944a8072048070403a6400e00d40980c8a48403600002c0c05006540c001500d0600040706110700b06031010015806240140c840242c071444c038001c3c17031007400c02c4100e240d80490400003041041d10039003103920039045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 408889199 1250 408887949 408887953
    0xd030606051210260d1b03051b1212011208070305070f020405070309030813120e04020909040506010f0e0906040f1a150315061507030c05150402180708070809 70
    0x144c44003510b0510a244424020102501810741c8182440074400c42120f050f43d03117840320b0800850350009a07840c42e040b40041c100100004d0308040ca6045004103c0b401c580da034207444403000004035a03d00313078001c0c103c0c440c0d1840404000061400c07100085100c1c07a5030012159003403950540b0142c076645c01c04c20341030f182e00d540a42080d0041e07403188602c0744940045d032000500318040f0b05000300145001040519591642214000170603081c0c580405070340d0142c1b0706030f001413078840d0104020b40600d40d070361504600000305000c100701c1d0110f43c0074141c511160b400041c4c1703a9618184010b010040e0b603c0f419580050b400b10300491012054480c007240604986410710000d403500941c1702d41c0c115050600d102d011501044140307018005402c0d2042d400480303c1d41410188002409070304c03e00302154031007800054000070103000300c002141240d005000da41048003240741e800c000940c201c41c101d100e5440d954000c50501d124500f02030050320190327912030103640e4029003542c2506d00900403401c24 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 408890449 1250 408889199 408889231
    0xd02060924040f0816030b06060408010f0605030c03070b030106050f04030209190b04090209011206060816050109060f0c02011206090c0e18040b190209090a0b01020d0306060512 78
    0x508000035544001d290501d003075669442e1002140305141c1507000303c04541c220500203100b5140c0082c00c0c00079039810120440181c0c07034860018507244617543c050380d41942801000a2222469449501110000c1d003e072034040e808070f020181c40304414041e042180400f03000500c0110b2084000e0001058950030381460320740c40750009081490200c2e1035000c0c0c180450701d042a505202d014040101d04191403d108501c19030b40050b0b504030050040d0706001100f845c5d1003007406a190480700c001c0c00242c0035510010080040300c0708624a07402018042404800e00050070f5108803200000030031650340f0b403800d035105c5038011125039000d60300c1e0a5002d41c403803502284001b44c07403044014140c140d4407010044812a400c3c41440958803040d22030f0700d160042003201081c14001c645500084121001c6241da4840354040028018800c02e02e81010401e01001040031644c0c1c068001c10800b40c00702c0350b240141c450300303c0507600d0b00d00071600014002e010000c0494004024130707810070071500c01a050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 408891699 1250 408890449 408890479
    0x1401050405060408100c051801050c12030f0f060603010b090108150a1203030e0a03020703030822032610120611130515030405060f09150c19020604020d020609 70
    0xb00f904250040b0400e6084841400d6590001d841019640115820a5401c010200415440400c2006412414070000141c84801c0705010701590b0090802920010749034104140100054001214130403240e80340c0c50080360781450040243c0f412542c043c08114901240c1000441c2d00180281c107650700030220700f05015844d61100d0101002d0311048140300802101c07803d00900343c072603c14001a0541000707542101080d0b0110341c1b6070a9a8050030034410503164229101a030480c298455010400904000820564456031840f035044c5800c2e0028030b9441c001c400c110701101c042d52480c105502a0104020900e48481000b81c40d074012140003e1501200780c2125081c3d000484001d50044020700a02c40351808203602c000b509a081d4000d800e5281540d00c031a524800605801035129407400003038003040c410404a40c4d044145403100c2d446081c82265910140c00110402111001c0b101725501035500c000303401392295030000d0032651041003540078031810707901c04030351a071f0418001e43d00a03003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 408892949 1250 408891699 408891709
    0x20c0f0f2205070e0d0506010603022101180c08060d11061e040303110609061f03080a030905010605040b0d0210170709030c050a03020d060e01020415050c0708030a091401050405 78
    0x1c5080100003000c01d1034a0026401003601c800380e1840d501c200b41e09101540403a8000400a040d81d041d8140180e07100741443c040d282c0030001c85a0700350700f0000400081504003c02e0400c81c03d60361940302c140b0150040e030703005a4025508071aa207804c040b860030000d000c00d84080184a5112000d040c5914103680b00650300c244151070180c0d400b01010000d13080003096442214451402d030040081c100a041160745030351100c03006454211300d00b074815000383d000c04000320641d008641c00000203964070f134445400b03000342c29100002d0b0b41a52810500040c541003a0040940b48080201b868100403030603070030401c10700340c6496030100f0002040707191840002658a890b0040c130480e2145041c240c6140f40c4055440c0e00f540006000b044c1d03c020820040c0c894884c030f0044a9808640441c4400300615000d00a005941c80241541507150581c41801c1d003010040c045820b000086e280615140c2204665078404c0c1c172400c900140116104001040f15a00c14a4045005241051400380d459001817 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 408894199 1250 408892949 408892999
    0xf222403060b1503010f12150e010506091807170f01060e0f0106020d090303050702040b03030a0509090f01060c080c0a0803040c0e07030b010203041203020a060f0e0d020c0f0f 77
    0x890700c56558981580303500e04910aa003600642c91942d070701d1507040001c08103400201e44511848610042100d8040000500a100c822214100c0800516201110480c0a001e0695900d4080d92040d00401e00f8402c0241810060030b071100700802d101483d115111745007440441040040e03000d4a202650054002c4c0140c000501c0341c6041841107007411203807810700c8281070b442101994414203038519440d400890100c100e94140c20030a40307400382800850702800000f001e00703900d400000350401126802030054072401c0019a42c180851ba600c0c45620301e0350380280120310100314011908800101990b008103c0c42c000d081c19201301d00101e540341407854009a80440341400480001e01051823418155907000c1000d2900f800303d00280b50002c0e40b40d100c2d500520b01040d40c00364800d01418020440c5808d01a80b100e402c00a21074001c1915000704800713410b0341c07a03d020348080c1c03903001880012200002d000007400300e104000384c2d074108039004090240c01a04410030a08069141c1003080040e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 408895449 1250 408894199 408894203
    0xa0306030f03021f0204120f0219060906030612050c211221060d0201030e0f030d0207030f1805040b01030f021207180f090506030703080f090f222403 66
    0x6005426120208036980d40082e00300c0c030b00ca14810320003003140e80c0da600c03002e549060300008c405510507898008600507ca00c640025150b1010308800261280d1000845007240c039196810010f0544410001540000844028080c0e07480002d80304800d107420005015180c10120600702c2014140e8081d0741032218840b50740c155074002080d00300104a07404c003502151003407240440783d07500d0800001441d01c203020201904050b5134400d4803285140800c52085c6e025000c90440c0e4890424a81c04d001030341c00100102d0000f154860b103450100d001c1d010700c5511704400c05c4810b01c0103051a05100040c08484011810107440340250411094188000c040103286c03101e41041c58035110401034403a425907508014030401c0000c0070840c2c1c410341000207040c1c94588070040b17003580311400003e1401040b1b0704054442c5c1070010f01d02103d800d0070300040414500a45080b0501d2481004025500c1b07007040324400d94405407046440e060b10503a01503028104500074ac0207403042d4140000c0342140441e001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 408896699 1250 408895449 408895453
    0x60305070902130b030903270d15060603111c060e0403080f010e0606180d021f08010806041203020702010903080c0318060708070308070908031305130b150a0306030f0302 75
    0x1c640b5012800721250806132501503030251450600b6211581e03139126a015081016506035510240c10003a20400b1064502c000c290408200345828001c810907030039000545020b18010b00041e81d04e000c1d020303000074881a072103058202a041982c00e51401030400c030620f01b40d03036101c41c0070503d80c0c9808103043c0924000d0796003000a10f00b081d4010a00001a004501e1941414003004080d60322101191540d488502000c030300610329101140b8404003100000b90b002040d00c824458100320307101c01c200203440c2075a5084159903283d180f180c55040554000d002800d40344400c4441d0f5009030003e1070a24810300d000c2c00f0300c0381d5a485150464100015001841d0000a0480d0501003114070700d402c5110101d600c94a8000c55907075480300d034480c00100800b8000f0907000078100e24061181d00c0010040a4240d81d620281d013100d04810341c4d10307030090324410510100c0c100b17940c00140c800d03400c01a0b0050900310a41c2500513103991076402ca02003034000c054880c00080300141c0040f151140451203500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 408897949 1250 408896699 408896707
    0x203040305011503052a060f130e2403030304030302031f0b040503010c0203120f090a0503071a01060c03120213050a09052d0a0207030e18180304030302120c01060305070902 76
    0x1825a01b840c0c2a00901d905c0b094071403240e01105203aa040b0301071028001c0380e00b240d60780e401041f65092402000c2061099a10300b410000c0c00c00201d0040b6441000400300422040d0840e08105000c1d41200ba02d4a406600500c0004c000a0095000315000045c2e440c03c580f500c07044404032426003141c0e42003600c84403000700d0f042001b0b05090203004548181230002c0c5040c601a000302c0700600100908854510a951010416861003401032160264010302942c0d61154103052003501c64040414a080c0c4081c004000104988a9860794014541c59590306861000014507100a5040300c0b0480c4801d15445500051035030b240084e1b10b0003132040c604c0224240c50040d030701042501c030b0b207a245000552110a0364408108000a695001003181c0c001601c40905003411600220030304103054120184194040300b003021420241e100d84d0440078200d2283c40010746c0f8a81342c5c040d91100034090b074480d56650079034034007030405080c3c42108400000b80e007a0b92602c61a1610140340c0c01558503e074001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 408899199 1250 408897949 408897953
    0xc031218050d110c1908030301240e1804020a120308041a19020715021204050d050c2d0a031707090315020901210c080901090308160203040305011503 66
    0x10140710b900a003a4144001d0b01102c010309191510195180248159070300c82c1d022401d10744c50a41c00d0040d01080b421aa1250b84903001c6d50307611229109c03502020300f100d09420406511901c050000100080d0007850040c80d0751803104445840075100326445485181c0218100480b00c0c1c04100c00780c000c0e55180c5543c1418200000489813410401d041120200100702c6150020042d0300b600142008005a855200e0b040c101235041611220b200c1560001a5142c0000e41c0c14041c18010703802101500c42114500c40c0030b03149071059040a01103500b001890f040c000e61416891715040c030f01904080300c0c003c0c02c1c0404504003d440a030440c04076000e82c80c1842e00c0d41000c134000c0c1d80034410f4249450024190340300c5400b145c40c503d5101c039a5540000d03078804140d1003002e0904005124072042d20140c2c1c0004241000340c621005d01c00300084070b03a80020000030301406010302094241e21040e03036913198060b09400b40610001d005003035100070000000060001d02c1800d8201030054503d100c19030031340c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 408900449 1250 408899199 408899203
    0x7030b040501080c0a05060a020f03030a0f0e011406060f040317041e0b0f18041506030b040908030c09060715091e030e0609040b0603270303010303050a0c03121805 72
    0x10b82010301d0f568010030100301c458495011500551b05d040350210344600100c00100c1c5444a408540d85040c003000c010700401000035006071451080b9820f060281c03400030701c87d0600300c4501d01d5214424020003000b24105061190041000c00e010004003807401d62a62101c0020840d602c0301d0b8242c04800281c104101000243c0c0e49031407200903184081101e01c1d040021125004a00b201019260b002a9a2904401000c1101400c0a016005000351401103001e150241594810240403a00705588812585420b03c0b07000c040d50740c480101400c5490b80204c40e84540c118140307c68000904219283c04a032100c0c9040798070340851080801e0400e8149070010050100050380400f04105065060000350424041d41c2c10007400d58103151241e001c10001000b030161542002d421280000500c60701a200c800740d88940c1b94055501240f1a1180d11010340d41e100920001d40007500900c0b00d540300074491078045102d140249401601c0c41ca26211700c80440d850300302c0b41003503d00d80d031014000308402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 408901699 1250 408900449 408900451
    0x170f011a0f100c020f01030b0d030801030309090e15040c0509010308181503070c080d0e0105060f0307031a0c07080307051b0705011d03150c0c1c0c02010c0f0b07030b0405 75
    0x1003542c06000d000600032000e0801d07218508000d04c01c1d400444444544d91190344034441d03803400107103200948121410040c0034080d003030009030001030804401040c1c1601038021100b101c0014001050744200041007039001d0400a84210351000c0b10420000e1035070b603002c42140c00b86005803046580c440890302c0b01c440d400302880c8181e0082541811043d40c0d02d0301401900d03442841824201e40d05003007490701c003580b4410805172600c454680006040305900c154080d910900095502c0751000000380c0405540310200d200040030300c1e100d4805c080e60100501d02440d08070018045c0c450a02c0d80d180c0c0c40740c2c24ad400032038410380050004103600f5004410300c1070180300d01096001400c000b070704000c0020840301ea40401c0d6400d0341040c8100701300030784040262035040754843c2080702c11410a10317400c100c00c4d40217029040742440761048000700302002108048142c0119150340800b000d1a60040d2048404007070181c803205080c25118010500d412802d44c890f008981e800a01010040200011610 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 408902949 1250 408901699 408901729
    0x20d0f02220f0b09040b0a0b0d0209040501051801031707170a020606012307021906020d1101020a0e0d06090605010b0a14030105030a0f050304091406012601170f011a 73
    0x2103014003c210301c0a8100c212607100800303035000b0603401d20550100d28120500c0d400240311a0300000e2402002a0590150030b401d40100c8080c01142d903070320204103440050164a6911840450040000860945541e040054076413107007420540ba64a45903005002c104000403000c2000030111600e541c1400740585c000e8090a2880d1010700b14a0320780c6080380417034104a10307032400203070303060030765a907902001c0d0764183c0340e5801d480b05529500c00948074079440c641417010031900307a400c54003603406000341c03146143c4642e20b180c0c80c00c5114041004c2d034401c03900181e580c03590341e030741806c00720780c1c41d005041c040d00314400220781d110003030718000700100942e01040400110a1005104994000c640b4100c00c540044611030f081c84581403135030540c803840d070005a13a64503001065480700040c2c0d46c03c51080c00c0980b101c1d03070a48415580a4800c0404030b4031a68908401c10061098203009211410f002460340c0440700c510400d41703240c41c01c56845c02c12144010400484001081c0742050725440c2e104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 408904199 1250 408902949 408902969
    0x60c03020319050c04030b1503060f1e1e1614040f050f0111070305060a0b060711100201020d1515030e100207050c0a1508090c13020d0f0222 62
    0xc64001e101002400d0842d074a2592a619800403d84c201034035000e0f02c003e90f42000c15030747c403410040e03a105102040708480c1802402090700180c02c20715031007030704c80c4144d1020f107044070f005104024042807940c000b0400301c1038040050550b40401048200b2034403c40860406000140317a071400030382810500306018880280030441440a81444100c1c034003140c0e4183c2d8440507014101006030340812581149010303520542c1400000c0c000005040b60003000000c004114000c2d8034414040644a59480640f900b10500d00c46a03660600210342c0040101e80c1c03000604007181601100295100c01f81004420400041d0500840c9212011b02031046601c1c10100000e8241a00058031001d9014030340041c65400700d289401e00200b40308c001c042550040a0400207522205441c080700c54603403003c4c002806985c0000d0b640e01001030768402c1e140303009240c183c942d200f107103411010754800800400b80b83c0d101c40741001901c0007400509103ca8901c00d00490300c80003124907000320292640418900c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 408905449 1250 408904199 408904201
    0x503031309151a12181e010902040207050312010504090210050d0f0f0b0a05030601150f0e09161e050904090510060b0a12020f19020f0726012a11030d020304060c030203 74
    0xf02e00008441e0740e0b0410f0008055480140202c41b240182036405c40a5007083c00052034604004000c802442070b142c10b40c4c07820707116980b034105220403140e8220000f900104400717120540740b40a0300c0940301c0b2110800d001302d2032680001c10402070b11000900b00000c0d035114020441d00340f03020142d1102520b8182c00801c110f43c5010110000304076680e00000501a9002e0b00070011031254500c10300350315019100711801e0911801c49080454030341042400900a00b840b0007505840c0450840640c4155603400c0c28020740d0400c000c001c0281010071a1188950f000701501d001107800b44000a024144c0b5483d1a014400d002170311200103049250100751040090701164582c0c9000e41c2c0c50b900060540c21400003813840c040e441c006c1840846c8070284100c040000c0e05900058001d0f000045104200c075106c5401002d0a0984503540041c83c4003c40004070040d010402c0303001881c003070040d468881001042d421172241940d02c145130444d0000d400104110500015005030307290b414080c0707011459 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 408906699 1250 408905449 408905491
    0x5041e080306040b04110d0b060c011b080610080f0712090501020904140f010303050a1101020310090b0312070b040c03080d0b0109050f010e040c11160504060503031309151a12 77
    0xb88a815000c9004554410703040d40c1032784460b816038176400440d00080007000e41d003d040c0c0f07110f80c4041061400041c030840c002206418440101c0d5181c404507100c0d82c0300c030344614255066491000f0164010400b00030808411090310380241ea012502402c00103035100070110a010030741c1c0301801448040d500060034418200302481c007203411207405240c2941c50b02e4584008031202c450308501790b80b41d50f002009100112815492800451b411000d082003600901400e1503203507a105184544248001e000b0b860101d4540080e0603803080c801c0280060240c2c0700e546460390b40c0c2040c0d19040b61590b4400008540c0d581110600003d0b0108540c000040320590000074002e6140b10701c2503000300e440307521490300c16000d2015000c980c004032080d5203a000103e92060000e0103944540380c813590621000040d079040c08801c07228803400200c8540c0c5003604240600010f04100040c94551000b8000c0014046000703903d5446c0c0480c01020481c0d0320010b03030034035070b10504020700031036002200c000342009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 408907949 1250 408906699 408906731
    0x1306031a0f13020901171f09051006140c03040e10081c1d09010611240c13120b09150606160c030b07051c1e05041e080306040b04 57
    0x40464490b10700581d40700044401269441d00d00e54030f0040c160144000d10090328400c105030300c100f0305c800c40c010041680d540c401c182518001d85420740000301502c01800710520a90406c10f4104c200c5848914184220040c24950f40c842c0d88190000c04008042c4200350829a001038000c00328a001003520714501070384500803000d01070503c0e0a1145402031020341c40325807004103054441c000d00a01845da99080090006400c1050f02e010364080c00c0b240e05c1c00da200004e222500380d170f040c05160035240d41e0400c00060541c4042e585080f80205002c0008081c0c1c45c0b400449a428801e9007594071134107000b07041ea458000741c041d150030f24003415030402285440d0002a0350101d2401d1415522400c0d040c00d140144c910300d908050580b4061000700310012303802c18001d20074904050354214002110b490032404035540074412984103050342a0610340c905e540e80000341c01c280030f800e0401203810340d640300c003080090b03001c021280100d003c03082041514151103140d140d020199000e000144160300d2483d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 408909199 1250 408907949 408907969
    0x140a06030207140f06150d0b040f020d0804060c0c1d190f0204080a0201090e0103080403062a0e0405060a05010c02060717030708060a0f030818061306031a0f 69
    0x482010340c00314642040c400360580c0d01c144401440709030741008860041503a01c8003c12204c5a00c82d5a50701d15100c541c0c10140c030300f000d5198102403030056175240c81c0e890a0b040a240350040ea4410511104000441c00d4035000704020020b40d203031054403841501d0400e05580d0305601101c0d01200c000d41c412150602022140d90004504620b103c1c0d140e80e06071000028a8854000c0c503a035840464003092282002807003c2140c2e000362104074026588a110003817003082404005c2c607602e010b020410000714140c00050b9001d003807a141c950f01c4c1962007211a01100780e000e030080054003000d030003c00c0c0e040078030031a0b40144d01514a070301414141170000c2c3c1110207504000780150400503a0900703018a515504d20307406140c2d054943d036410b0044000307110b0401502c285128203440e0200048c0c000c50b480c00c1e0011640d00411a5042a0307185088444045c141c40301c07a600070780d00700210214000c021402102034840b42c2c500103030080c88941e40180c10540c200d040d80c0038440d0700341c10100c40d41d284a150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 408910449 1250 408909199 408909209
    0x210702160303021527060a140103030914030c090f180c1c02060c03030f01031407030b07050c0f070b0705100b0a0e040602070c120308091501060c0512130501020601140a 74
    0x213024181c942c0c07103079a00e8000c04480542011120400c91880180d0b010440354041c00b290360090028000000c511140441d080c8801004030b0b640450400c225942450703444e0903003c0050a41e5203001c07654001c190701c014101c9104400c0076441041140071140301214000d042c511000400c00f0203800400301d002c03581c0e82864210340c110040750002c215a10101201c0c2081056400d40f80c881c05d0480744109500828041180c14aa0441440c4090b500001c0c480c0c040ba508940c091a0b00d4840000582e50f42e4045113101d00140208100700205d41c0c0c0030440320b00200b092040c1e8951725515030070301c14108000c0b01000045a41801e0381240141d4941406d28165607a801c0d0b012450746403442c1c000001c0c803400800802416207808001501407200d40f100d003001e4020b0303d803036255998100c007984e202d0030800075070f0740340c4645500140700701441141c039444a644603601311403d149480350709a542c1d82098101000744444801d050000756414014240100071144050318030011900c001940242103000d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 408911699 1250 408910449 408910483
    0xe01030f150c0e060c1c0c0212010c050f18030105040b0613050910020a0203040e01090c09060203120c0d0b0409140d18032402120a0b0a030804150521070216030302 72
    0x1c1009448014448441259406903d500c0c56a03850b40014190909620b000d034409c8020402074403906506004d20180c1403500d07650340c2d2800020340c5500d51541c01007042c000605d000c0b02c6034007049490900c0754a010b80d0142450075014648023003006200c2103095849441181403809000041400051031030001c0c03d807d0740980c036128041000c0307281d80903941c0005000e440c1e01c0000a00e1405035840028188901e580f0321091907243c8409a030703680300d40e020700290300d894200050f0408a2180c060214010b40240104122048400107401c0d0744402e08265000d000012138040c06131003c02079071403580400d042c40325500718400d403940d10f8040c9a2101500404088500003503401c4884504514000028411511a1180302548007103090031168043d220b03140c503e600c401450100022800c40c0c0d40214418940703800c09030b0502000e030392075001100340700d0b0038040c0544405001d40f0080c00c4030041908900d09141c01031000703180c01900815540c41e007059250038008a07a001c9481c00c000781110107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 408912949 1250 408911699 408911707
    0x5100f05060d0b011503090203060117070603020a0c0f0813030305130806041a0403020a120815030102030c1e070c03050a05210702090709080601061d040e0d08100e01030f150c0e06 79
    0x10191b01400143d41c00a5050103420004254400e001c40c0c0b0f6501d114944046845c990f44503081078040f44290365502020880b045051800151488012020140b240c203200c1e00304105180da840781c23522140c0048020800110302040d120241040f581d0041604500034091030506844840240c100d0100700d480e440c0c049000142414020840301824070f9110418078078002003034000900c0c0c10340541e554402d5580321481c0020360710b014008d490040e8503c2d01e00500d010354101038218040340c7c40c00084200c840c240044804a5555000c0783c0c01940298042c0030340f17086030f2501c070b81011a0751103034551070074101c148915071484035000e132007105906861111941d1150700c01a580343d040341d485800148106400800c2880d8441c010b00c411004d40014048400104010002942d0251441101e9903004a0449012500c0341048076000b42d882002c0081803a111160104400426042980c1d001001d120b81c40801c5000c41ca404624a501a4200001030000320000c04042c100328400c0d00c500c901007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 408914199 1250 408912949 408912989
    0x603100e040f0503070809040f050106080a0c02071e030314030f180114071d0607050a12140a020a150b03060115021203100302010e0a18020d0905100f05060d0b01 71
    0x100e000070380385030441d0403a912020790740b0344007419907c440d610340c1c0102d08000400ea10496140902c41c1079a000b5116020943d4403066918002d10382595500d045200d040d00011320104185840fa0301d10300e08103408032426013503050141500c03051640c0302c80113007400c100f080961164040b0080d0440008076007250440c4c202048a405400c0d40e154002da15203100d800c0c01660b0b41c03c0304052a10403501e540968010603201d080069500542070060120381144403000700044d10039203403102503861802c0015000d0312a084080c441d400c0340000702e015a1080352000107202a40d20101c2140810070011710000040700042030f1650818805c001182c0c3c06001c5000f0424001c0c0507801045407041c40903030710b038070300b543c0039070140340c42440f05a010521215003110581004030140060303501c2101000b0034107011201c144000e502c0b00360707502e0300c49550b02d034114001641445009541c000c800c80200b0440301051521003101d201509051198400104a20000b0140001030f03046402039a1060002c070840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 408915449 1250 408914199 408914213
    0x240901030218090a09120e01080a1d060a06030b01121203151a1908070c030804110d030e010f0f090e04020d0507030308040611091c06290f0603100e04 66
    0x102c01982e01481c00002c12509000340d034003070a40c15009040c00340341d500e135003081580d03410040e1055a0005061800181030182d0707980005400f01b028081d19086c503024104540d040020544801040c952a0030041040c4186000518003401c0242118001c1c0c0d00c41d80d8402080c1e4248420700401e05869804400c10744501c40900b200030075155a83e0881e81e100850f0f04003250f840007206200700e0040003000c3c4100c512807109a486071586480e901c00700612510151801100280200d07a800780e07031440c0c101c69866203010480382d10721036100c1541c8100321100240490b0600703e140300402903018000c220b410382c080f004904940102c007001c00c1544860010400520801001a015200d001e00000400d54440020b522442c0a040c081150609482c6c41c02c04521410143c141d100c4961004980c40d82941c2481d540e80718402c1c14005034076078849403554080c000000549145040e4000f42001c40d0030030180c0c0e03424841044851900d5403030440c1d503045034902e041c001d440c034440c0143c002400704503072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 408916699 1250 408915449 408915487
    0xa0605060406020c090a020a0e09190c050901110a05031b01020c0f030304020108010609030c060f030b0301060e010f0f0b030705030402031213052b020603070507020406030c03022409010302 83
    0x3400c019911034540c240655582c800356003a9009401c00d0700001c8550409101340c1c1c8035520940d43d40c00c2c00d40b0310142002a040d0008c1c0c4006018009009480c04855052080c4d1b400d51006450390703078540341080005060f0000c0255220456002960140d000400200407140d0117070b902e0304286008290360000342c0c0203020342e036040c0840340f0031004c80c001d0101c0000007541c42a80700f40e9036000340340e803100400c64101e8a9448024000c1c0603444c0148002c5000b4600d00740c800174545400030fa44030443c0d0002e400e40303103503a03c0000689081c0d0014042001c40d5650903001d00809482c03000b00f01e180c020820b0841c4401001c500400c03102001040455600344400c00005849410301da85501c0c078442d00401e0325a40e8868188103a59000030141400c18126000a42d24110000d00154101680920102d644010940400c000d0100182001030b50703144a0384000e1409880150700c6d40741103206000d030180784504420f980016952440c980d282960040707407181d000c00c0c0780258440807180c1e8000140d43c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 408917949 1250 408916699 408916709
    0x30b01080c0a140d09060e030c03040b0d33140102151b0c06010e010611100b01050c030409020408010507020a021c0c1d090c04060f05150403080714061b03010306050a06 74
    0x4000445004d00112a00710b0011580108410007283e82c500c111070b583d0388039400403110503400074002048411511400b808a94900d00404104040c0e5014140e0303140c404024084c9071044102c943e1943c102c0b040f407208000e84400c2d29580c26203400d140001cbd58901c042203d65001404c200e0006100c007501d0008000741c158002c04140d111032000d00d01070780f0b070182401a8190072560b14000903c13180719100541502c0c211602404c52090701c5070400c00a000740411031070522404004c80d40b8021000c1000f0001040300040c01a11142403002c0d21f0309580000c0d03c210308542c01500804096590800b0325081055680c8003640480458504024580c84a40c41140756009a0340040c00d00468002028441d810f04000c0c7c40c0207408460401007142c0035801107620310011414180b082d404c00c0e1000300d4040c4103a0700e03442d08140d501e660340c41272680480c50456070401c01c00302281c90b406c0e04000c600e411103031030540c80c04d881e10100d202c10a00c3c0414440034020584450100d9122403042d4002d41c080c0c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 408919199 1250 408917949 408917987
    0x150f051909140f1507020c09071803080d061a0c1e1c1116030809040b0127050901090b09041e1b0612060f0b09030f03030103060906050601030b01080c0a 67
    0x1c250f681c458507050030b032241030700124607800001e24036840882c41a0803010b00070201e01e696203400504a034014110401c6607450408d01c403004c030214080700040d00390100681000700c2c501d030420207a26110040102c044480001c1405401c01074070000c07c3c2054505034880c6401100380140c41e215151280c01240744600c50a0405040142a405249a0a40d8104074125002d482020300d03072581840a6100150000f2001c1c051070b0521728040d007150030082014504031011654030100780301d80954a038420b035080714680c1020130003400c07c402c0041c010081e402d020001180310001040c0b0302d11000748000d18500d800c44c50303140b0f03c001f415000c507c17198208030145009100f034081c6200740c030582c2c050b500c041065801c903001c10007014000c800039141c00710700c0e84031158600600100c1301e42200c40640e90500510390700405603401000a940254061080440c0303002090512104544000d4421410141010f0311102c817640c02000e0b450308075030215007460341d4204a000c1124540ca816031040650 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 408920449 1250 408919199 408919213
    0x3030c0f08040909140607083c0f060114070204020f070501021204020f1e06031b030f1006080f040f082505250e09010f0603150f05190914 61
    0x20300604d07808210240c1c4124070f504181356440003c0c540e900c3c0f048465000103850003000400c19900d0110341200400e4000f140086940c501909040440190031001031501d10401001000303a00e64030fa5542004085c2840400402c019001554910a118000e802682c0003d0382503500ba02c080300301c60880b90402c0c021512044510b450140c9058107a809a2080c20f40c80c02c0c03904946002d002e00e080f1030040015920310b02c0700c41810b10a0075000208402071000390020100315460261004512031031300780b00d040300c452402c0c1d01060481d0355641c01020130400305400700455400900b1425400c160820060300c3c1d42c0045103007c40107071099100c218149600c542440c0e074100144402901101d105a007501e9101640c49a00038000b80d144001402264100b4810058034841c03450550300440d0550000c580e4007222603c0344203449599108448984804001444201051284911455800c5418840b900f03151a5415101c0c031602c0e495110f060b600c1c071004c41005131700c0d440d107200c0241c40e01c1034401c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 408921699 1250 408920449 408920459
    0x2070506160201020c15040e0a11040303020d32070f080c030715090809132a1e080a0e0f010c0320040602030a030f0b0d06021c0203010f03030c0f0804 66
    0x703564140108a000d1710861404098a1600f10403e405480100b021340d4106031420f0851050b03514041d22100301d990340c0700b090411486029008002950080c0c00402071841080030042c107240351005005030600e016021282d82d503100004000002c421000f000b41c540b511410000783d550382e400340040a500380000c10005001010001c1c241c40c500684042d0b034118900000e610644e00e5254000f080301108100060062402040802540c4042d0200054211a030206540c2c801b11007081002d004d81a180c02d4012164040480b01c01510028080c244500c0c04a102a00303201000c1c060b50481d6031241480f9002082c00c004411641c0c501c80f00034032611038000300280007000c0d42042080c555201c00400d031840040d50080718210b6015500941c54601d10785c3c4110010840401d040d01c1840e02d600481c005070390b41c0d4401c0483c65008590050b41c0d50144151000c02c0b80380c00c58202358042c0180b00400c0324181c00c2c1001001c980e00f5081941c145021460540d00c90b0180e0000140075a80220340854 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 408922949 1250 408921699 408921727
    0x703060c020d02030c060c0a091503020415030903080705220b040609061407150e1005060a05011d0904050f070b07150204180e0f030a02010b0a1e060f02070506 70
    0x3510200580070340740d00d510703800801c0340c41c1d02c9030400d020581e61090002c2880040358900a0080c058a441c1034400942c482c840c05582c9842c0c009220002900482c0c1408a540d208454140d4201c03141000c20031071602e42d60261107030000800c2c601c24040046084040c141411064866011100100050064a0300c2884181d038005000341e000240945101040250091000d03215101080c180e10341000415692910540d082070898000c030341e22040d4020f116041001045020100f12001040a1600754148200b11641d68002070400146d8085031041d89400b103000540810203588010061713940d070400c540360070380c1d280000301203100700302c8001010906c80d005002040e110f050181d015404500340d444c2640568000d000120306072014041040c2910ba100c00b90116005050305c840001d482c4656041d07403c50581400075035101e6113903042518112118901900c5900d9880120b0543c0c201d0000087c15540924030501903060300010280e0b008000c0f41c4001d00700200704503030f60070f50030144034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 408924199 1250 408922949 408922961
    0x1902060f010503120d05070302040e150f04110a050c19050d031b081603060302090a020903010e06130821040c060e01021b0d11281202010801050409080903070306 71
    0x28255000180c0007151900d00841c040190700310a1048504003002c11504100404000d0007000903d58200b00014802411400581c4900030300021034038030800100600c5030098801d9040c610503441c241442400042034403c0d00c0c00707100c40e4640b40362645c0390306882c01c0c540b003603c64020181030140544c100c1005400145400000c0b8503036820710154074618011055015200086004500326000280c0451030b0032100a61038080c43c03030701003a220340d2038001c56060b03a01918114481500020102c505040900030501811000b000030100c507c1d1003030103c10b4003e11988010040180050f10900440b0021004820411820304030f0b00c0d58241840c114400d51000d1140c074020610134011040d25600204030321400c800c0b659903021010003450100111b046910700100c03808002c0e4101d00c816500c2d0301200104014000d8914102548411a4000c080301d6540c13240003200004041040180d034404940350441d082500d0110300c418803441c0070500d5010303403100300d5010b2240b1080003080c0141d9410007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 408925449 1250 408924199 408924211
    0x103080306011205090703030c03030f0f05090c030705060301330e011704030e040e210a020c062b0f020304050a0b0105100507120e033405180408190206 67
    0x82900043e6104540d82960000c580081e26a046085c04001190250f0325800c0c2492003403030000340b2040002c3d0100100d80742d5400c5490b8050ba61400c22040040810200101c0d00003280100022807405000880c40e21050158190160307604c0744c60350340c103c8943d00040e0040101d4000817001d08030060000e007000c00500c0d00300e001035115250038100c5c170840d0282d0740c007643c0c041d590a03a440044030b0500020b88a11440018980320317110fa24a10203034022079030500b1031844a140781c2c0e22134000d00000e2801500d00701903032041c4010450400e48038008014030042c480c518902c2d000c1c0d82e072100c000a00800701c0d0000502050b000004010070030902240e050707041882500d421440741d03203520500c84030461a11100c4c0100d902001000302060f0050509000b608441c80c2811076900d002d00400d05026450002c44d6200301c441d40c0c680740784011644d003c00f100c07010042e00b40005162000240c1001c00040c005100010240d022409103c1c6260448025800c43c410151200e0317540a0005e650380022108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 408926699 1250 408925449 408925457
    0x150f060112020405010518011b0b011e0b1b0705040c0509030d030c0c0605101a13060302071a1306051006081312110c090406140a0b06190c0b010308030601 68
    0x1007800c49080324420354060740c1040c0e507094101848110320780880e03800c1c011541d052100da000d8000d11054860031602d11303039125840d00d0680e54508211018901c07a40c003078484a00034200c4090000750041c009a40502105a100c0c0780c12503003441076942032000a0700007541117814080b180d07440c150000010140b103c0309904036042c0140b038110480c12280107003a0703000000c400102c2280481d1042e0001500320541c1031303c250520b659000050020614291240d034581004a8075a00070103044222500428440c00c0c01d43c1b42c107010780c0d01c980c401c024401014000c80341540100300b1500d0810340da100b0142d805001008581040049802100400d11804000034910030002c0d0b00e103201a4810558554454482410706221403c1664100c00b01158040300e4481c15800700f5503079883c1c459080c0030798010303c0d00290b0388a802c100940300600c003e11500045023449000c0300e079a1544001c68001c0540e007511104084a500c200b01e506020340f07000503101c0da070050000300903c9210801540540400d8032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 408927949 1250 408926699 408926717
    0x3070c110301060302060a0e0a05060a02010c08011d06060d1d030d0c091206020c121611030f06040303020a020106030c090c02010b09100608250207030c050307080c0f03150f0601 78
    0x41094283c41c094040250851802c1c0f10311110103024030300e80c00c0b6030040244201042a10754021982d00d030008009440180c3d10780c0044402c07150482485c0303014000c100d01349404e10800c040108000360004d0801802180b00240e14002220183d01681d4049000c9141e80c00344444520300d0f0b40e803a044007038079019041c58080088040d9005030041411138540360170512502c4541d403550f000030740007664245400c0c06020003036541c1010980040920103104285800b000d900d07810306a04407040c402a0314003981c010a5510044a800100d00d64480d505140250380c1d0540c8000490141a0a500c000c110021120380815503070043d030828031442c0d01d103038001c0141c00c60075800c003e1160b00035222144c04000c0210300788402c900c0751040d1940701311042c81c1740f100300c20684801ba8040d00250200d000581001000f4000c00c001c1c030781000001c1008600420701c01e80ac00c400d0b507468039500385a5900c252105c071030350a000d1324280700380720000b641101c400c0001c2c9000c950f842d4810b001120000c3c00250218 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 408929199 1250 408927949 408927983
    0x804110604080a3210090201030b030604080c0d0824010e0310020c0f0307030c1b23030106050306150405150301110a0801060201020708030601050d06050a0f06140301030b040f150203070c 82
    0x6046404c0f400c0000803c1d0343e1040301032140052a02c1c00c030030780c1010707100c02004989071010000180220310680416a0381c0290b242d0315400c0a583c6140c4004200d4110140403010f04101000440ea0341c0410040600c49010710042e10990303204160181c2500a40390840e50250043d4090300301005c42a0139074450403138400c04d01e512803080721402130100d12031300261400725480314036440303c5415502d023120f140c0d0f4480300c2c5841c45e05c448040101d040ca060480785c1460b41001c2c0a104002c21041d4001d05841c10300207102c0d0301070411640e0b05401035684900060300c85000301c0394541507500c00340c02049140c0011005040551050051030045034020b0000140148140300312961590010809429070f2602c000440e0140d00400d00180070f03586a4401080da0342d200c44115008190075501c81440500d030604c0134080110903002820011802d00040000c07850031010942c1c401c1c1c0c032030440c030705081452800034200055011100760b403510206c104005150003040745143e00f40140c0c14103040c58007074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 408930449 1250 408929199 408929273
    0x1d0606030c0a12060213030c080c0904020a18021903022215050f1e0306030c060f04050d0206120403080105090109091101030b0112051e160804110604080a 68
    0x7603a90716000107440030204840c000c810755a64005100341c20243c98000039030a0842034041941046d141810021307003c10440408000b03100c805607058404045600d0617400080403907000344613008103c40c010408001d42d120590407910181003550801260120f031010041c029007040c0000400c1c4104441ca9000440440700414106e8007a4414050b80000c0014102d80541100d01780910f460000d12640f40200d14a0203500000c91074201c045450f803402004051400e020058147d0042c40c003045102041e01010045800b0350714140c449080311452840030881c0c600ca2070043c0300714030400500f400704041c1e000c0c0348a4100d841c04c071107084017a62200c40c40701c11180c041c040200a8601c0100d0059154003c1d040001c1600b0141010481321800303104030401d8440841d03100107802c03c04103402044032042c014154000300381c0c0c0702d842c0d5803d038104800390411034041c0c40640410805150100242c0d50a82201c0c06810070b0005e4030705000e901c0c5080d07848178980c152104a030f007002d0900c207880c80c0b0003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 408931699 1250 408930449 408930463
    0x7060501030c050415142e0c2105040e06010e090a1b0509030c090402031608030d151208180604030b0403020d0e0307120203210703140a050909090106091d060603 71
    0x2100c1d168442504a08000c0d83e0851f80702c51520000034117403841600c074402d42c0242c03500c1d11152900300028100e45841d60303e034818020b640d43c034180305840c41c44a142c0d0080503101504e090b207091040130340303410f0016a0300b90403400c2c1c00c0d030f0b011042303c0030080c001c050764214120034440004805031101110398141c03858041d940b9010340591010b4004036041c40c080c1c40d155005400a801d51b04000c003494026011180e6980090070654000107182c602178002d0300c81c1d50703111091008441d00c0729081200d000e00004c0c080300c0107400310300c0102d1000c4500e101585020349002008020340e80d2265280382498560104450590160003002c0400a685000320440508840018080d286582c10b02544114401c917002c1c080e42c26100d44441d60904140c41c401c0404a4449200400d85a001514008098004180703017414203e000703000c00000140c07c903060b580825400c0750b0807100b582c1d0b101d41c6c460040c0303000d038001c0600c542004440c42525480305444801d8450b00070a40700c060b52500281696050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 408932949 1250 408931699 408931709
    0xf1905070c051e1905090a020403020918150a06080a1a0f010308032403011a0909030a02190602070b15040605120d030203040c0e090d0807110a120507060501030c050415 74
    0x3603800a904030310b00d80000200c0704c4040d507400e1454200d48480c0840d004c0d89044170910146035000a0510951500100c0160700802c0074202c091401100818552100100c4504c80c900058002c003286403aa103980051009c2e251000c00c40e4400e02090070201c00e43d60881c90220000c03800040412032040c085c155040c10b03680c0014420b032940e00c602e81382011031413102c0032404400183c44d8035074031155428003480f49010810f42d031402c031007440002003181c0042c01500c080166401082404007141d00403a04e001180c104a0529000742c560b82401c101034410a00c0042c8042c803c1e400300716842006803035515011209460421095880c1c0e0180306a5944082d030945080c0c0c02590101200b0b4803917001142d00c0b620072031442940681e11807030920440003c0d16688440e4010302d020707030f901c19030100c0019403194407032a00c0f4112a410940d11034581200110150071080c40e00c1e00030708468011412203000c950301c04010011980d490070240080031090042034403460402c5c4040481c0004038003030b50240c803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 408934199 1250 408932949 408932989
    0xc0908031210080f0c240409051503060403021011090d0606080f03120c091c050a020312070b06010c1b090204030219030312021602090a0509070f0f09020f1905070c05 73
    0x1100c1e0004220500c00d1241e014013140102c46da81860b103800301d1026000603ca25540462242004030303c43d40e5120403040018040d520007420080442d500150070000703035035440740000e03010041d808451024450f145401e80c01441c1c113145441004001d0780004102c03041d20050b660422090041039407030744030303051011764001c401001103405051200002c01d4000310081441e00c08140403101030440b0f84000205446a03041a217482c07040d0309040c4170300d0011100e00c3e4103075454401ca0390b45200d10a080030741a181002542c032007010801070340c0502605144044944039015a50300d45118010b907020340403c038000c5020b10300009028002e0084002a02d605031a5151410710801d0030701c00a420190400100713400690240c805603c4041c006030082c810030740c0101c0e441ca005c96045181c40003603407040700e0041c0948810014800b0250300401561000742c80940e4803400046420721074040d1030305038500140640446a00c03540c01800501e5041c1c418441d11090740e68602c00c01545249004ca500b032a5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 408935449 1250 408934199 408934213
    0x1060e160e060c01060f061412040f030c060e070807050a0608011502070b030c0703030b030f0309101106130c090204121203090516050a1a09040c0908031210080f 71
    0x140103075074102a840c80a4111414208030b6440b003030948040c1c0d80111014a808982445800e038400031403015601c461050505c0c042003c08000c1c02c8400040018220004c101483c80c1058882c220924010f500300d01e060010305446e2881c0342d01d40040e8801c0103481e02c50075000140505042407150304590103501c0e01c4400703a281c070b12050110040e02d0245021801003d0022510340c2d40103000d1405440c0030a5002d4860605141c060300310f8221100040c0301e41d0011511010030300b4000220380b000001030381c0c035011890381c1d00c00c240ca00c1c1010004882d014000d0710100004042d000c04060380042c0a0a07400b60116030b81e5031070b2000c07841a07009510307183d0502d124602c0482c4032803c20481005042c0307000594400f031078441a040580350740c08200c44105801d02000740b883e10040d42400740c00f00c00c41780103e001071030943c00c9180c8650790580c0c2c01540c940e541e005e50b00d405000418020002c0000b907075500d541c040e1900005520881e03d032210310200d40400b261310003002039181342a004c904010205 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 408936699 1250 408935449 408935491
    0x50105191103061203040b0723010905070312030b030102030c0306040506010c0b01030206070c0b03070f0f021603020d0c17010b01080a0b01080f100b0a09030203010c02011401170307060e03030901060e 88
    0x150180d51004844c0303200030403001038806903090003007814a004450500c05100c1006d0b0710300760034402d01d0450030540c2c14900100c01013000842d0341d504607580082030040d0f1201301e440c1070f000380014640350350741944088100541c401c182e44c0294412442210108029a40d14005541858036400080d0000700420010700050904100501d03010340101000d0802558032000d00d001030b0b008039820000148003060303441e03526400202040350040140003511000c07401141003441c1c040c29110292080c0412a4120140060607044202038040c3c0c88000311098101c06040303010700007413220a80060500d40c00640000c0341c0748101c0b110404140c2d140400d949030700c07041426003030029100c2d1682c0c4042ca140050314411500017860031141549074003089030714600416086070041e00455003517904109000c0074800d02c02101714156000609810680200d04d040d8510354007410704014119890440d036034000f200000003079480b802c0b9104c028010b590320b030494441d6080c415250030358051742000307200c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 408937949 1250 408936699 408936709
    0x10608060102030d23060406141e12030304142a040b1c0303050a0209010903080a0e030a0f02040b1e01030c110a030f020d02010203010302010518130905010519110306 73
    0x103082001481241c1c24600d00039030380c0007203400072801400c44550109000c200340c0e10328100580d200d00704440400895140070b0300c00c26461023961440e4890980d2201c20094000b10300341509000c000034001d442c444c1c4030725541554075441545c064468203c0900e401c94a140d00040c1000143d01b66081d51000d603a00d1414000e210a80070b0880c3d901980b40c40e181012750f01c401c03034a41c00ca885210b0090600c40e0150501404880b40640307041d00072801000b04a01d10f980000380c1c1811281e01003405035952078070b1502141c000802400465041c040d402c00d40092001d100c46e4541200d0084508010380c0e84e2900402c06030344113241f40519459a0a041140258003030350100500c01e038a0300b489016981070300300042c00e00902004c04c40109040e0502040c8041c2e0401c9501030401c0c00780021071443d4110b40020380315000d5051256640c10070b420300b00c00207484001c0040c44820401d10288200202441d03d0340c080c1034210703511401002c01c016110b14440d054011455881d00400c0038910f551251001c3c08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 408939199 1250 408937949 408937951
    0x807061b0c061209020d03091a0313030513080709020405281412011b02070509102903090c030d02010b09060d0c0b070c15093f0f050c0405090303010608 67
    0x1900d259a201318034800750f16081050100d00c0e01c03e94030f00c02e201f4107003505042d8540288618072504802031080280c40d121302e0354160b040542504040381c9903241d4210480d0903030103541024034a40039074580020035580c039802500c26100102e41061180b507038141400445144000d908a442040c028200409014000ca80301a0f01000d0035100c03050481c51092401d44008421106512655443c0400c900b58148920000780008035181100360400c07594451024090780507040f0709610810145052454290210208031300c101d151a4503441d04104c115181c4001e00750890003030280203080b0317410510603ca031401e807190050031302d142600c03840d080c4903503054130b000100d038014130010300421140740c01405018110f205038030308010710b400c2803140045c4000c41c0c901f00003840342c2410309000122503803010a00a5a40d840380000c1034043e0072030072044810300e140c0744d103042d005040700e0b40030301202a9202311910f004004803001840e4490a0004540e012259003a49410a00062000520400c0d0403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 408940449 1250 408939199 408939227
    0x405060f0d1104050a02090105190302190206060901080f0a08070f0606120507060306030b0604050402030a14030406090b04060507080d091a0405010b01110c0f06040803040807061b0c06 81
    0x204900c03008040070402900d1440400d55076829030071210005464203000306640102505030550808401c0c8001070100d024a10b1031400c000c001d00c0040d03541c98800d40c1030350200c084112201071600190903010303454600649005005100140c0082414040050a400c9040320200140070000302900c496200d50031154040b144004001c0049010402c030380140c5010345643c5002e4004000c182c500980b81c030429600060605083c60380070004110f001000f40d82c824410b44011500d5a10303480006d060010b01c69000b0124420070b00000c0300400004003034019a141511803050203500c408480d031480c0598410b24000410400181c070010b95060054034910039601d40108a4660300ea03203050404d103a008031500c640f6030102c104403e001007405a0b1100340d2081c00c1201100d8a400031003501c88454031501402400300401803021a00e820301140c0003000c18809407900d4030b484072503890311001c0510901e00060104280584000604146100b0740b6034030507960754110307107000705c00d8401c45466940 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 408941699 1250 408940449 408940459
    0x20601140301140708060a1d0105011d031e01151206020f0d05160e0f1e010e120f0111041203080c0d0906060501020601120c030b0c0919050f01050307050306040506 72
    0x1c01c06400440302a074a000d04d08503280d0b104245400e0042c0211603581c1e80c4444407000c90a0307402e004c01c800000040e41900c41c00c0ca404403042c90340340a0120307100c1c4c044610940500c601c00b003041e81c079080c10034110092517020300284200c40d22100265a840401d00031a048140c4818280d400589076500404200c0642c1c0c41040c10000c070b500d000070403540c08030f80c00c2ea8410f01c100f50346003080f0351010082c0001401292020454003480f03001c100102c0c01c0703040312211840400d00e000183da010b9080c1141c0302400512035000001d6404645803201005c0311034000560038505880d203160029002d483c151103010603411241c0126480c11681500d0140035030300c0b160020030100c03884040d0f50140d45640b502401010400718903207030009203400d005034003144d2202d444500303a4001074000c00103002141d4024280c400d054584103806d42c514820031481ba0345c0a40c410b810300303054000701c003200d8044070021075522003601c00c003000544081c07104840b818006181000003c909241503400107401c0240600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 408942949 1250 408941699 408941711
    0x31e090e01031b0b0a020d0c060b15040302030616021b0d080c0d090501030c0c020f0f120d030b0105030601080a1e02031017160b03041a01060f021b01020601140301 72
    0x100200310420b07003003070b68400fa9055030f800040060b0314020008084520005103896083c44000b511003644266020400c08002d00c3c2405100c070350b410070361440400030300402e000080c045404a9907406480128041d02902e00010b2020192410f11f1a90b01a81d402070422460fa900319944030721400f8148070342c440300691000c0d000c01c3d00c40024108100c5003200920342c1201004001d4660101c9a000d6130415080c00c80303010540350301c41402d90f1130aa050b46c1c90b048980720040000e403407100d44568540c00c0006411011445080080e5a1106050079102000021900e200454051000302e503000e004c16420000300b8604c01d05680718411001822200c52042c4031280e5880003030b60300a44109140c401c010380180400d01c42c44400051604070380008110401b000180c00c10043c066100d020284007001c4005004e000713808070a500380c44516080001c056071590b9010702081c0062540344014801c5a5010003841000503010748500c605170010150303a031030101c02c064540100e03c52940c041d501c0c2d503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 408944199 1250 408942949 408942959
    0x9060503040f0c060305041104050108070b0d0f0203271504150f0906020901260411060d0618110c0a12020c06040e01081204030305180a0506030f10050d031e09 70
    0x11550303001404131641d004c40e031070400d414030680c16580310100e14070503407070300c0010401c8690010716403086444803c80b4648825030484040000d081051440d00882e0001003000310401aa401703400400d080c48030541400340c0c8082a1603521084803010901201013a4081000318240d1110502c0d03510070b590703000c01da01901500c0142920b404920490341c0c241c0224502c0d0240d030700200b141c013420800080040150103004540e2452081c0503002401107107078140507a040ba00ca038012281076208051040c0207040d40c0c3d03103d8002c15200c07c610300748218680302252300c861001e4402c0b1501b40446200034400500d05455180e50105a000b03880c080d480f9504405103252203a0015000030080c0c03185c014065803404442c1c0b07003842c0404100555030b6004010603c00240c000c0290b0b40c2c02c81b2480f905200b18103e010118180100e0b5812595002e0404010010001c5041028a00c60f5508424500aa42d900c105209640d08c1381e400060108164403030100f00200700f9040041e600d625032a1001109a60b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 408945449 1250 408944199 408944213
    0xe0f0303160204050702010c05070b090c0a3002030c100306121401060e060d030e0a0b18150915090f101710030309120302011e020706180309060503040f 67
    0x5079008603a01d00ca400000e056143c1880790607404650390000703100a4002c040000c019118070840142a02d045201154062000f0492112504009001c080150f81ca81036466689000e8001d00100300070103203014641290785035102c00740300e80e010b40104180b08041040004080c0801c0c205010155100b100007802a142440e130a20140a045200f010b6110400c1e141d080d599903400c01d0000c1c081c484188075058030b038000340d028441d806240c03201180000500046a40302281d004043c00d101c0412540303140d9075021552150260221262100d2554664a4800902503803066a92011501401c295030105020051150440080c0b60b10589a00c400000d4a05004480b44100003000310f60311000740308804010581040c40c5440d9541600d145d0341d00142507007424022402026400802182014001d41102084200a10004a186440c40700490080d004440180c40070350070301c8010750155908807410040c05803d0f54030440032030308044040c2c1e065800900b044880c5001000000081014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 408946699 1250 408945449 408945457
    0x4060e0a272405070c05070e04020904020d082a160b031602070801060308030601140408190f15150902120c0c0f0114010e0c12040201110c04050f040203012306010e0f0303 75
    0x130320740701d22500c00500d00702940f030180150803000e882c00d2804240405079075985d81295010b54103d50455140326a8940300d10395000d10946009201b040d0f103c00c3c403000d00d0305552250341007240c208840d80510840c003106400c0c0303014880c1080041003000480c20762098107000c8035001e80c0b02e00440c0c4502e41c0d030f00d00542c00c45a2650080c2d88100002c81486129030340b1028081201240b000000e06040c1480005600c4003805442400c0c40241091488100f0155280b8081916040880c041d0030380da902190902400c80390041740d500c401a41400705003280c0f103209032082560541e0700306521f599880400c203841d52101c60038000e60b00c1058041d6051420900804c4c04c50100c0419114403549000e568440d0b90740060040141c1c088280100500700d0030b0301591030350003502482c1610303e4956950310349042185242030150090b003800200300b60300700b0b1040100d000710300c04d0b002005a40800c4c8444c00c154000e11016604400b00503011811962060a8000c3c20000c010019011480314000117480c40e80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 408947949 1250 408946699 408946711
    0x1030209121507021e030d02070c050909010b0405060402072a03170c0c0d030522081006030b0906010f060e03011103072607050d020708070204060e0a272405 69
    0x7105500300901c581d030600015034002c0740c400e9608040700604440d10341b240200781188013010303404907080040c003141502010050a02510450590400c03a1000e4080c0c075441800d01d000744c1c105004500c985c00c0500c00c48550f20340080340301000d000075482861699080c0d1202c1903810303109003404808654035a91031821408a1200035035100e00c0e298400b4180160710607814410140e0869107004030f604402162606407903486040d4000095646c601a00b0440d900004420311400821400403c1e941c0d01c40d905990048012210580e105a8440d0b036400b42405000b50a00c8030403010014107000b50b40d108100c0d10b0080010541004e40c0c035520450340c2007208c03a68001104080c01d02c003000c86100004001030041d040b544018a0400405440c1e40304400003c0d442d90b80c002001018086510260b5680c03d0b8020000d102c0305943d141d1094141d00c06540c413118407450003035246881e001c10700c104540000f0b80c1d440c401c6002a02d407103d00b84103504101d220121402c1c5101d04581414621070350348210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 408949199 1250 408947949 408947983
    0x1a0910030b012c0a0f0e0c19213f081b0d0608010203010308070c08062401111c11030913020c0a05060106050d0b0d0b060103020912 58
    0x516506041c200808103a0118070b0414005103d58440f4250300c26001140400d000d060403252180c5038030f80001d02902c804040e0b035504d02082d10043e508081005544040308858031445109603805a522114143c411000c403401c48540d10210500c01b814504d2002c1c0c000d403040ca120f003131200c0b040c410023100c007402c04031680d0002d00c0401d500d144008071504940308901c2c1c0302010f0310700202009504046140004a00d0402040c0c0d51001c40aa82000d0081c1070008025500c030750b520714201025810901d01102c2c54090070001141d41e100c00150640704201c08403004c0b910035051030420074001c690032040c904003d1175220400303400d6020000700040071602c80a01c19616a07140c002400766880e2882c28580741c0041000b0040c1d5600c0400d148032820f00780f000141c0d100c8070351844900d00740c92840300600380c1c02003c000044060300403002d0032511203215001c3c46401040c10400010743c2010303000524210a41011603895446580a028404000f4000040c6003c441c1e40c850310780032341d56850601d00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 408950449 1250 408949199 408949231
    0xc04140a090e03091c0201090e180f0d03060602030a0c08090109050916030f06050916020304031a0105010212090102210912010f1805071a1e0706060803090a03061a09 73
    0xa03041201d04000c0040036440c5d8503c080050f5800284610f030588100c5036884500c0300841d0700f120f40d6001090380092985d085803607800501104e030381c4404682424001003458070382c0000e0b45600210448000701d08944d6030541034500c0e0f645002d42c941028401504110704a9804103503030302e41c1e0811b91302840c3c10000111080758084801810b031820440381c0312462342400c07c00c00140e2652010365401000c40c840f00c41104444480032440d5004551000e0200014038140da009014a031550074103903002a801d803001d10030081291b280314450201c8080c01a840364443c00c0e07603a081d160940c4108410038000c2032030403400700009510f80810700c0d0465140e964030b1030103062980151044090403404500f00d041a084280c42c0c4503210321081c4140801c12407902c4600040b50003040c2121150301c1c0e00700210314451241d074819036240e0002c0d0301c1100c3c0a031401c90045103600000082c0ea030160002842c05d06c030700e825659848060415820620142c0f800f00c90103603407603981e1010581c230610a400c501a50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 408951699 1250 408950449 408950467
    0x7050f07052b05030708120f0714040b0c0a20040f05090a1502070c0e04051605031c05040b032e080a03052b0515090c04140a090e03 58
    0x14010164040d03032146008503078600540e00180303040d4140041402c00b520000c092810028214800c081d001490040002940d244280c1d942030080d015454000c144400d03980c50900540f42c1400040c0400c2c41c40006103c2008010f001030300401802c0304200559000c1d40c05950f50300c121607450000807207071000c10382244086007068480d0301c540c3d400301201400541424004503480c0c406420b00a44030481255060025048503012504015440100b0139403181e90b4030044001c0f180c094a0454050217003080c5403044c21901d0196100303540b0003d02404007844408081800003050302c096405020040c000058a418620080c0d441190100304e60844141080c3c15070540d201f1038100e090614a0004090003c40d1002980300d500c9030345402d101c0d66601220340c03244012000c810180e914103000303024121000c2002e404c2103008907a4a118592100d2005042041200046412242001d001c1c4001c20101604081c442104d140c0640001e485070380b51698001031321b0001a08d030100c0d07400001d00d80c007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 408952949 1250 408951699 408951703
    0x50a0203090f0307020d0209041403070b01060807081519081603030f1106010e0402041815050601030905190809130b0f0604032307051804060501080a15020a0e0607050f 74
    0x410780b040700514946203166000684542c10164048c0c0180220400241003100e101c419103185120f00049a40301d110341d1a001c82d03410024050000051780300d90101e07601754014119103006400d100d001203022100c14003800700700b000380c6110802d4100c580307000051000e024003100098a004810b20003109065040140004054405003420060b540b60704240c0100049561030544541c580c40e200540c440d40001005807503054002c200c0f004880114174100702c495804034840200c0d110081c880f998618006604903140da6001030b2140c1c00c680784038250544202541c04034181303c3c00c580c604081109000c102007401d02443c0314030080c0c0d00c49913021640b50051800c540c04c802182c4d1301e0718280c02c6664000301500315092a00c030a0100c9100312892500174007a0340301816020384404e04c81288541400180c150076141980c0caa0314010010910640210700c540840d0f81004440010001c07140708480250700400c5003604001c0405640740c0c0319910b80740200840b078060320080603244c41074400c0d24 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 408954199 1250 408952949 408952963
    0x90c1207081903020d0507060605090106030c090b03060618130509030a03060905060f10120510051807050909070c1b081b130b13050903071e030818030d050a020309 72
    0x2002603642d071014030000a5001542060f610003038a4415160001407610b500640142d400640e4003906070000070a03070740c0d815400851028180d50340c207050a55034075005000d0b13200c2134401c1138000c1c000300000400070b0a40703c18102d801c1d030080c250040c40780300c01c1680c400b00c510586021065400004c0c070701a4413039050040201900d0101002c0015040c40c2e000074006c00000181c09004243c0e004140d1202400340c020005d140902880600040c80c240d211207501d280309010b1a4404d800000d10420155640b001080c8150042e469051801400508000300254000c0c1040104410189910001400e50064400c9100e440b84070b02d548034189003030030382000b1001c0d8090004071100c010034801544c4485021a010596100010304529054013050006d185050204200c9081200b0701c09031500000003020200d011740a41710b034030000b0781303003444405111060180019010744046001c400c51a403d190003042c1c5542140e00e4090f00515030390075207a04407401d4150541c0441001820f00082c0546 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 408955449 1250 408954199 408954223
    0x803070605060312211305010c08011a03100509060307080109060c03140f16090807120302010c09121113090f030f11070326180a060908030d05090c120708 68
    0x400d003040d024005c012609245600711511a40039034001c2000368868404441060390450b000b8040c0d51030980001d0001d600031303c9100b0710418883d1000020200c0031050b02d015170384802803801502c1ca00801c0100144001d03001c1b0b42d05018114000800a0091203403421952151401140354286e8007000303404c80c0c0544031300100104004007004000c2140c3c1d000c4d55801400034440d03400403401c5000c12208200d0540262159200d0703e00003180c4e042d10101d01c1910b06110364021b1114407482e04040f05c009601b44101e11107080010320714000282c44c050003911441c40904000085100a881401a540306400a40390940740700d6840c403c0c9644040d4004850761642403100001c0038000c440d5030f91b012184809807000310118640460340d1005224081e83d003294174455a1180b40746600b00c00100700241d007091091105520010b1245c0c0558200400c842005000c0d600300488816904007500c0d000b403c04905000c4d205060f1480e9582c0b40101c00c140c903c1c0130060521783d007014596441c03c0420752107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 408956699 1250 408955449 408955483
    0x1507120516030e010e0d180b0405031b0d02100c1506120209040f020901080d111c0f14031303090e06100c17030c03071e140f0408030706050603 63
    0x10001c00344842001a00709501074074000031200e10b400d090500510214082d08241d003c0c0445150900d40d0000260f22031b080302c009040151943c80c0ca154085214521407590143c01101e00007020b0403001d060444c0741a00a0910b02c5040c07d1a8001108807003005c1034840850032240700c100074003405d1182c0409448800104105080c10049070b0403001280b004002e1061142000181c10001c01002c0c040d50180c0c0903046650702e50f10f038028507440c0c000302e0300c130000085c40c0c0540c454040d000004800c04403c40d0420245130700351310210304542e4250910442024800c0f104140d03042402004021445a10507107449000084903180090044419601461401600030140142c035529140105821070b01410008400703d954503110201e402d40c205400201c5030040200b007404c21044c0011841001181e403a94103000030005940c82800900301c0780703400130300450001c0c1d1100c05110010040c0341414690300d81401c0d1b40e4004207180d50f0140104940701d6450b0004c0c01a0303400d0411525079a40c43c0303904 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 408957949 1250 408956699 408956701
    0xa051501150c021c021c141903050415030e301206220c050d05090604050709051302040f02040f06140a201506030708010908030a09021215071205 64
    0xd000112000c0c4180700c1340440008807021580e40c841860070304054140c0c0000704c0030381ca06045d40310410f40340a00c10a4040c10404805015181c075080d055554551a05401c00c1d00300085050601081001c0c00700741680d0754004c02c50200100080c0032072805503071800e048031016400e90707405000208082c000d001014400c0c940c00100c1c0d46142c2d507000d00203a40c420380d091600142500603c05103610004124640010210569846001090404c2d1804001d202a494000d5415a5000d0464020b400c0703401ca0001071002c2101c68100c2c40e0018440700001c0c4488242d40c00003011039000e44856400c0350781c00142005640c825aaa00000345aa400c1080d0031141c0480d0032003480c441da010000401562100b408168100c42e00ca510314400c40320b04698554585013480700c010f8106035a40c5101c2d00c45c4190028103000305000c1c40407038039480400c05041d500c0b075103600c270050000004120ba20515030f43c3e4480d260780003004000d03032101034804910310608002c2d101501f00d54141c00c1400d9040c0c2004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 408959199 1250 408957949 408957953
    0x18090d02010e0c060f3c0403030818160803181c06050604061205030c01110a1727150a14040222060602030901030515010e120a051501150c 61
    0x807075141d0f0244002d941c1c01e50384019480200c2954810031102c481610090309626580c1081d100e8040351503a00844050800da03420384803c0958003440c403004002409407000202c05110b04594002da46026a00311030040c0340310400d07a6005803081d003103443c0710340c4045100e1820045488060b01100c60a41c0c01d50b45009201c2611906600c400e50040d1900d038030751022a40c0c50f00c642e0b00c201c000348030341e8070000310030181440d10989a40c4520440c025941c01c2001d5010954288011189082031a40f05c0c400349280300303048120401402043c1c12580f0700301396518401d0200400860032640c40c89009024207007028548082c0540c800340402c0c440901d810714840181c240c1445040e0002d8048500140110713103185911801740484603e480c0c040d0415500007241d5070000f001c1c00725160262002d102a90754032811002c0d5440008032540041c0c041e10308a103c90401307040d40b201005000068404c51040c41c4c50f0589403d407410058542c2e00028801000030214402d40000d0340a20307442c2841d410300c456 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 408960449 1250 408959199 408959203
    0x5070f082b05120916031118070503130c08030f0406021504020d15020717041409150409030225031a0f0705030a1401030c210302100f0b18090d02010e 66
    0x42c3c8909401419010046114210304028030031000f0340201035550b5450700d91402407400c080c019842e030700940c509803070012500102d00e00c0b07074415449540e5032421a0b403440407035511001c01c54019210b0050445001c14000c0d0b00340010880381e0b140021540d5541c0ca421030007490301050846010201c4149030500006070b60b5917400d50340b540e4224024003007112107440d80034000d00c22114000d102c1460115601c0034120300d98041d1045404902d806000c9002c00014810861400c4a100e42c0654a4050301c20b03051500e64001d0b1f224038000c0c41228400388884440c4000e000300300200c1020303140008004c108110603180c020b0400e51202c9030343c940c54180345520042c50b603009043c08040c41070201c005034150100d0b034807101c2c0c40350b40e590f007102c910350350780c1020032042c0164001da2040761516020401282c108000d461800d503030580c0101a0661452203c10080c90840c45d8000029100c040c00c07100c0b5610313104207090880715448004c01074101020024504aa40181031082d0390502c1d000300030364000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 408961699 1250 408960449 408960457
    0xf06060c0c01050d18140d02010e12032e031205070f060b1909020904151d040204090209010305100509010c0c080904090515040507050a0513020705070f082b05 70
    0x3e00708280c4848006000a01402c1c42c1d12000115185000d200402c4c0b0045000d10b03007000b2603460546039640d6112104900340d0300c032150b68003102e50110340b0000464100c04006c6a2210240c2c0403500f02610011128025080f0b0040030402551800418000d1085440c0d41050500d00c41c20b0403482c1001c6550340c10003074201d0758805441c042d560f960b044c119890b000042d000c460000751006030060307103400d5040000c1d000707030f00b009014a2805240440725174450051105481c0050b8030408400c1030301400c00d031a804000c1c070491b0007581302c11200c1c006860f40c00c03505020b035200390040c00c101c400c0c51007100e00300ca170000e100d0700207681082c0e148202c5540100c02c5000058004414079a03402140012502400400100034070303920945c41006121000266001c0c040c41c8601d09480300c0d29603420030009041d0310760040c13a1b480403020981c6003a649081d07008140307480c840c6090b5100c4a41d50340000d0350b20861035000444603000b622302c400005c41c1e81000a5042c80d010100e801103150000c030014100c0c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 408962949 1250 408961699 408961723
    0x603050619031101020a060f23060a0314120f0d1406150d11120402011106100b0327031819030605040c030501050403210e0a0611160b0f06060c 63
    0xf007208101c61180d10038840360b8400c1d074002d10103020000c2005500c0c00202050440c01580324606149902c015038000c03201030080c0c00c010f0042c1ca0290840d121a5102c0306400404203c0b80308150f031110304160314001601341d0b43e00c80e47c500340e19170700714022402c1039403200c8403a1403d00380542e0030003100369212120f10300c554a640444039199a15071001c40010304011303202c0f4050b500f011400003480204207624522842c400c1e610a14810b001079005660344809568903501e40d04440001c1c031402c40310001071940501075000e41c0b0b1818009035099507140620301c1c042c900d135410014220303d00c100d04074040c40c1104800d0722940b6480020070034201104030300c0d000c024101d94984012606200284a24101441d0000003c2200d4205840c000c0c0170411618118000c003014404900c000701d00074402c0c1c3c04984159000b074003000b00540d2b204d10003408981c1c0c0c0007203403100600100884240e520410317058148a9080da01142c1022000740d003407510000c180728403d1504001004080c6004140440044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 408964199 1250 408962949 408962963
    0x8030d0b24130509010b0706060b18010c0309091401150921060207120908100207030206060f01030f1a03070801051003060e0a0f0302010b1207050102070b071416060305061903 77
    0x40c580805001071480036406913a001951200101d43c6c00111002008014441c46040051566039001041d20340141648400c09030440c00040801d0350040e0340889200703203c0d01e004005c09848044050880d42c0c413214080d201d010010041c002014a410120803201107401c10386075252400c925003031010b40c0f11101142c0480380104040c10080c0b580c0650703100c00e03800540f0f8003002e56030810042894034148580d0160b445410f81010b8085918804c8908058155020300440c2c0d462005000c0d030500d404910324105541e9900c034184030340c1c2c2c910910400c240312105103045070152108240c07900805070040a080c0c0d150000f4800c201a9080583c002c40364003000110f01c510b480c0808034103111320110302501c0081ca40c0807800825034103600513451400e080701d081a150103c15800c81d620005400f800f809640f0015003400035400b11405070542d01d1240d401d000d0f486040100761410f151403082e402e1041c40401000344001d64040c068a0383c010015508081d0300140c07252200c080e0303c09448040c103a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 408965449 1250 408964199 408964207
    0xc0c010e0a18060f0e090105240603090a050f01060f090c02030316090503010f0207020924010302090a03051b030d05090108010302011d03010c05130b030c0d05071808030d0b24 77
    0x51100d40103071008240c07514131800c0196a03000b00d6904070780125480d01c059460f020000d411031040800201c2c000b00e00b84d401280400800703082c455240e001404142061180c0c295020000d5420071503694010400700010031803514014502c200c0b9440d5030020381c645414581c0085d00309500100313582e030040b20a4050a42d862004409450f83c8405070801901542815060441c8000c640c0040010910070394045d103442d9240046d5200052074101c0008409002550f00304040d80b00b138016182080e001444c20041a41c2c0e41e5030103181100801041c500c030b03403e030503400d043c6103400d0081d2950308045080140c5428200c400013804241c05020090510030800046210303170241946522400c1005802040503900b00c01c03003e0642c0e040382004880c046d0501d81d000c10400b441d00c00b41c1c1d00400480c0e030380c1c0f41002c240541520180900801103c03c1200d07010b174007200084900e50800c014003664002e165943d4400d9050005d40d02001803c9000c1c0e080b511403021410580b500e502c074410100c0f20041c3d00c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 408966699 1250 408965449 408965489
    0x30e011b03090c12060c120209030d03020912030403120e030601270e0313050312090108011415040303030209090105040c0804060905070512030d050f0708160e040c050c0c010e0a 78
    0x35400644c1050481d40d407540d02d5101041170503480410026201c2e10307110718075805c91404000fa881001c240a030150080101686101e000741c0180260a800408000ca840032480c0120b01d107400c90381c010342e1001003031901e5540b5a81c0100800881c0d003000e0300640718540c10308130700c1c2d581941194001c201c0380c4500c010607201d050301c40d80680c41d600450303c280c9070745860302c007160085100e01c5d001d040d20074007030501c59021042d0141c00300d82092806845502c807581c64022418900c0c8000c3c1c0c1119002b4010441407025240e031a070040c4017441c880d071401615401d40c4c00c10300c12580c0050300050702903890071101d02581c580001c5061b40c020750000c000300e640411840c000e802c015850b0b00c0103411082c950a058201407000c00074054400c00844100480d5840c0c0c0d03500315500006541043c00318141c003020a151190f500b04205000020742800020128007801140032640010072980008101040480c82140e092080d410080e0f0309183c0300c04411720030000140020b00500c02c40e80c00080c1041c090030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 408967949 1250 408966699 408966713
    0x60509040816060203180d02071415070c08030a08010509010e0c0c070504061215020f07080a090b041d060109081c0c050a0309080609070b0909070507020a15030e011b0309 75
    0x5a2150300c5070301035485e4140b10711030506207003200854408030700945807601001880040c48101b212441050401c1d8051408140044a0381034480c0c1981e00d6003c100b2800032484407140c101c01010441c0080d981c9503a070b80303402004d404041e00042d1140405400400c040c081c40c4940f00d80017851462655581c41888a00342c0c030340b103003031350201d900300741000400940801ea503900007520034091600e0148130250540108102d00c101c004c04444c1c4203051045201162018000d80f28002c0282000300030280c9030b46100300c45404c160b0203c000320700445555102c03c00b40001c0c2075000102070a0840085003400006500c3c1c04052401d40384a884c00d01050700101c1c480ca105400c259084020f54484000038100141421128002c0d800c461203150089030184030b0016000044404591113141031280100406c0500c0c0000f030440c004101e01805900007503900c51000c4001052090320141c0d0362007042d00301400717443e12501c2a0f44c0a174500007101c41c1d0518400008600a0705520300000c00301481d1410038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 408969199 1250 408967949 408967987
    0x30601050d0e0102041a04260304031403030a0b03030910080901020708071209050102060103050a02040515130603020a0f03031e0203120f010f1410080901060503191101030605090408 80
    0x61265400e00c61001402c400640c01881520009901001000c468098a58440c85a4441d25491001031840012110304c950014200011407000740c03482c2603a00e45541d001d540c2c01c00ca06803000c1e0000803c1c00f10f078482500c0303881c03020901038026506220170100021941000441001c007442016400582480020b5040741c00c03c65114003480c3e210082c0e41458150032607034000490100e81c01d06808101c660002070000c0c1240ea00c5002010146442d5080c04040c0c18003504216203d41001045007142d66100401090b0900d1340c00005001031450042010410150f80506480f410212040c00842d500000c071030a000c910b50039803a00005102c100320f155102c0c2a400d400601302d404288404414140700c074504039124100d01c1c0c080a91141e8000307101c0e00c03510381110760020010f4450480c25001c0c2480c40d5101c0f4241000060082d40c8401080c107181c2a640322008881004000c84c007005150345aa002e0305400b0319041003042e00700004182c5901001d403010b0300a500204a903070302119801988 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 408970449 1250 408969199 408969217
    0x251805060a0b0708120f060604230d0b1b0901201204030c0e01091806150e0a060609080706020c0d0516030f15151a0c010c080609100b03040803060105 66
    0xc103a807090f031414010036503042000d031340b4944100c640c00701d900f600e090103045001d1400200760750318061800d1001100c1070820460b210b0415610005000582d4030380c445648101c0c00b507608010b10740743c0042801032050804403810425035060003410310300c0e64005026034019054500c4c203031503010007440c82c500e041840700c0d1241111500090200404c0b076083c440400321805c800c01c411860f600c1c1c42d8503005407001d281613a0701c118000d100f8400842e01d0783d00910f0100488202041005484841c3c0384524501110100c42003900c481b0200049c17540845e903680141070b41d8000c4c0c82c20608007030000b0344809079680d090317110b086090181824080d040c003070f80c2c030500301d890100001c050b92450940303000b102000096410050480d8240d5140322580200c5c140c2aa070015001591800c101302548400400d400a64089000344070305240c040091050b00e21031880d64442c1030381880e00900300502c1c00f5005010700070040206c1c00411030800070800f560b8000340c2c46031045c2d8503542c5000040700d19010321424 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 408971699 1250 408970449 408970469
    0x210f02030a02130e090309061c0603351e0409050103050a02100203210c041206050f01050102120307141c0e10061d0402120d02251805060a 61
    0x340301c481a481d0b4000c09160b011030f000042d980d40c3c2c42040e0000d46204580d50b4500d60801c00000f5082d2400c1c10003420a1340b607050542250100000c1010211039a50b00200c540034865141c0d102c41c10341c1d0132844505c900e440304d5082b400011400004202d8040c80c800700d056600060500300d000d801d07010907200130340400c0b0410003166a480c2030003669030103102d205a0050b00d914000300c6c82c1c60300c0802140c0c14800b5100c41c02041400e0700b0900c5d103481c0c03001090b00220703003030520006c50300010000c484040c9174006c1d00041103c0c202401407503001601130744907d06651051001198034006442501d5002c006414001801c0c5030b00d441c0242d0f1727445010303440e11003841d22030800400082c266019111520400048aa511100d510b0703080484002d402070940c803540902040e00750040c40c210055209101070320b05404000c070720140d10b15003409200280003582080c010700f41c08010740364540e5001e40443c450789001903d8080140400420844041125921400000c0076a180c00160200401d08444 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 408972949 1250 408971699 408971701
    0x304030306170d08010f1212020309032d010603050d05090a0b161b0f051311070804030b15060712020f030a021b0a080d050711090708070807030c210f0203 68
    0x10301d10791254006202900131804040020800c021a8401c190680781001c0e1402c5462040c0c0d220008203030b4441c030082c800c6200030444020760340c4003030110360305440516900d07032200701c240700c0c00003040d0b9912901c0c0d90340f9a02d03148042020500c00200222001054104965544070050101700b007403040b50401c01605d4400142c40040d5101158009241405203040406c0125109a0551803404611502000c071040000500841ca000b40c40d044500c10030940020b270b030860f50000c01c406500012020341da0b080b40440c003041402081d01c51310350b100e84041c8034080004140c00c00200140500c1401428403054031203c280480c2c02000040b20410399202207907241c690301c03607009603100d1700000340c1c41440d02e8081d088455030510704191401d607040000600301201d20001c089909412011094031010710040301400d0b9038a60000050003860300e0340d51442c0a181c02a4042c100c000041e288070101482c10701901703115a40b0110040078080250100b41e280f401c0301404030702038104000b0260074644000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 408974199 1250 408972949 408972989
    0x71205030601020d020f0c01031e1a100512040b07020a0b150301140c0304081e07030302090103060b090f041d06090f0d08010e060418050a060903181a0304030306 71
    0x2009184100d600340e080384c41e020200c0c0c0080b40c41d588004048030240d84118030030718540d03000c0e80058030250a0031004001a030b5821241c00150381c041d03a91401403007090070310104503092800c58042a0030b914242185440e560b80c040b41201300d4020310242140c0d07040700204101901c00d0103400c01883e00402101c226062107a040c9140c40880e2800903ca5882c140387c242c840800d03502801d2007050040140750135907a8684403006a0307071101920894555807a158a19204010300141c00c07054041d50300180c850b83c100f00050101c03082d0750070043c2500303814030031481c02c0d5458410302044042c003a103000c1501c404d4650746040d0700b004560b203c0c040b07004950130010742d4130340098255003801d2403100700c1e40100505041510110028001d20090f444481c00203092810a1382081c0c101c1036060300342c03100c4888a91116802c0400c030440480d00e1030b840c1c5030040c0905500c4004c0030031070f10541c8008000c00746404081c040e00f105052680a10110102c00281414001d030712440040c400305060081c0141c041c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 408975449 1250 408974199 408974207
    0xa050a0509040515091003050a150b03060a0e10181b1215061707090c05040e09030306030705100203120406110c06160e0f0f0d06060f080c060909010e09030712 70
    0x3001c0c468058400c190001c0d0b0740f0703a820070341c6c0d004694210380540b1b810310590f12000d820100c00d0a8440005485d100c1043c4152030422803184196004e070702c009401054107800904001d01030000507041800d0082109040003003010340781c00f00798002900b00603d8a41080282da002044d40044d0400c2d01c03105080c810312110b08041407408039903c0c0c04104490b112850b070846160030080221980e407081e04d0502400f41c1c5548200c4a006003410180d0030940d0710080140000310171244501c0c1900088180422820104504d201400742202c0c649281c45401030f00940e00e001d4260319205024517400440d007440155401304000c10408591a03a560340b002c01031507a1114165240d10301110b4800f0b24441c40b44c45100c21026640c8000c0a1403500c1030948100112032207a401c680350b20103101c40313504000900600c04c440042ca07000c0c03405241c5034038100c00a0704001810480c0750180e081041030100c103684801200d415141808030010307264650203a07003499402003507001084100981829401e080d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 408976699 1250 408975449 408975481
    0x1b0d0204051f0905060313080d061707030b150d02030a0804030b0c0306030601030f0618030305060f060712140403080a0503040b0a0c020a0602030a020706110d050c03010b0a050a05090405 82
    0x1503642e400c07502c426465030304030420340d20049000280001814009450300030021500b20388074000b0785c2036040860303c991106d0b92085841420942d90b900301040410818a00603815821400140200910355120040031200c010081a415050f0a41c511196075a083e04507620030b4000d8200da2850707503180740c1030003140c0c890b02082da07000d4510f0b000038050520810890303108807000340151400e40d02e9980d4030143c220401d401201d000751181000c00c526a90350801c90701c0740d4000d07a808100c5040c01811b10244410180c2a03c1c01040100400004249800c3d10040401041e1030660507030340c0300c8403103410580034680004004420000f600c401c1542c0c0700c00510301460140840240c2900d505c0c10b20800c0702c911700d102070b000d81c00c90800d12002c1426980510303400780300c68102520f807082c2541c5640491711115081c003502c070008605254007460920030f069000315035480307081c555410020407400a00684440e80d080007000103100381c4d59803264040e40d14084020308203020a09000c11aa03c940d15 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 408977949 1250 408976699 408976709
    0x13150e01080111071a040c050405100f141e060906040305161403100f060807090516020303041e0606032001020d02030a0f080c040f080f01060e0411091b0d0204 70
    0x803c0040585600b9a040201c41e40345610040b001c41030f100701107410300d07182402001076920400c1601c002443ea207407030149900c1440301070400c82d40d0760b0503d009195465040d0700454015a0042c414460355121641c00c011241c40002c00340d064244850b0000e021882040c04040e00560085000420414002291001000c81008400f405034882d010f0020440a802886030301d90722440c01603800c0c0c00b00ea0320108608410175004224180c0b6244190316006440e0b120b04200c0303650314100300001284600c030214500751440030b1031642c01c1c00e80300d10182c00c0036000344081025900001100300122580440c000350b5001d89000700c00340700f00e808101300b014a105214098000c41d240e01601d54400300490728101010303140d010802c8507001c01190644001001d08400303007010080810040c0010303008200400d40100180780c03041d00541d000b400d42d4159030000103032030038141c14040058a41c050068800f03600381d82200d100d41c0c0315001380030328101c440d4100c41d10b64800944020424140e13001481a59 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 408979199 1250 408977949 408977951
    0xc240903080912030705070318090c02030c06101d0a1404030c1104141302040e01020c010203100e01030506010510121b0f08090307060b030f1002091509030c13150e010801 75
    0xd0204240301c0f0503100403601440020020803000001031300940c0400e403441c1107501c4c460f01c400d031142c0c801c0044680e05408400541d10201e9022a011010001c0b198494425000c101c2100d00d401d00c08500c410100c94602890f0859400040d210462548070514003945010302e15007509041c01e004c2c10f190766804003910280307a1990001441d00f40707030040b20407100410020f4080b540d1410f40b5054052003404040340d2103500c07452510340c007a8090014104c8407803071100042e07a070b08103010f10b0380010184c1e40c0040611003a4100400106401003a0307141110380a8600080c07914181c1c0040b51042e03840d440740c422241ca81032045c1e0244e4418400ca0000612940301c4c01128024260301b990050340c100c0c0d2003081944100001d900141068100c4000180e0207006ca0312010f00001d2401e007000000c243d402c0c0e4107540030031a02c0c102e1811718004500c0404941c010303482c00320000d001c6074560302e528005e00e025060802481a9001903070303209004c2c50f8080d40c9072000881d120700001c0060072007072060300b80039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 408980449 1250 408979199 408979213
    0x9010506030402131e0e03031f0b190e060c06040201110102070c050609030a05060108010209010219050d0c02130612021306120b0910050c120106020105070c2409030809 74
    0x2030401a08482c0159002010300c51030080c810419005002c1034508480302d035808550504500c5414000d4501d9281c2001c017461716860040c214104011043c403002c444401200c10820a1680d11003ca8440682111200125411561040e039288619450340f40c0c004c000000c1380c454551001c22034a0040d40b00b682c4030901828908166030a0b4003400340c000e807083c074a60100b040903180c980c4c0240300701480503069803440c5206840303940c1170003c241d00030001650005400320729582d040c404031406e01c3c1700d201510107445654032031035645c0440401c5401400200710842080d585c0f030a01c0000d1540060b201807100f50b48940039405501480d4408900a4180040c05070b00144a40100c4066501c2c04020140d8140700f80c40b40e074440c0340050205c02031802040001912480c1d640501c52003540c4000312295603180c110200c070161041603008a003103925000501000366400030500d039990f80c01098203096240c4224107803042e80d2060900380406890822280101900f141c03141e03210724035880c255051 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 408981699 1250 408980449 408980459
    0x6030307020619080a0e1e2503050f01090c05040f0e030c07030303050a020c061b0d05041211160b0a02071511071202010c06050901140103060e07060903020f0609060f0f090901 77
    0x1e94406d41d211100c13640100f42001050a9008107000201840c88125100d152140800b910760712414140709100d445072503c14000d0060803c4010160140f0314000c00250500d91548600a9042d02546200b03945404180300410200e4100e40d00707410840c000d0301e5980c06540c916666070b030100c1c0320440210741041c0000b404c05095100f61852100c060020700703856a1a141140740300b502c424581044030006210070100d0200300d109d030910503407040c52024181c01c40e414014101e20030030000d0561a0b84054030401d02200744502c0e900c00c0761450840341c1d80300d140480c003d0f030904845411086280310341c000b051000302d60005030042c04a0fa41350940304450f840380112100f0440d0800042d01250700103100f030340055041c3e80401da201200e040005100c89a499001581180aa2003540c1d05525944c0c022868941440040020406810040003140c40d660208030040500107809200f0f0f20081000c040e42c2d10b908080303c204203040e1441c15515482006030005a402c510b000601800301d250010034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 408982949 1250 408981699 408981701
    0x1030e160b1b2404020a09020403032105060307050616140607090e0103120503040204180b07020f070302010c1502090a0303050c01060b03071b0524060301050c0702061206030307020619080a 83
    0xf00d10002c0000d98100c40200b078424040c0e00301030003c076008910403034002200e490a00c040d2020318825920580000da420740220b02c03041d04c41402d598480d14040c107020072076800003140d10445500f40c80f010b84070090899180042416084013410107001d001e030f8440300e100d000c14100c0c450841070300d038407800700d40310110b088a2800034000280010300880c1401025801075000e558894030081021a42c0d691507114140080d5900c20304540148040090004094051103104116a40e4600601140b0700c0c64000030300c030b541ca03000083c1141440c1800005905810380495101d10005806c0d03441e100d680e4034008140d0783c4507803086445035182c000d0118404598408a81c0240f0342540c4815007884161180c1113140410f8008480c18403d141111081c54410303080070006903034850640f80a4a0007201b81829074500400350496070904024440c01a1303030705410781d41009480034006d00950350303a00c0840e01d94440c071200a544060302058081b03000008060001000070b40e903a078015140c407050040c070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 408984199 1250 408982949 408982963
    0x415030c0513021905030901022b14090a0b0901020d0e100515010e101e0e0a05030d0c0b18150a0b010f02030a030b0310090c060f0e09040201030e160b1b 67
    0x2010b080d80c4ca00750010041c0300300c2c0616041851403000607d40001c03002c421440b0445900c4668009103403404141990410b4401c810641d42c904040c04c50b5843c100c0400c1da21900c10017801441c0c06624404200419400d41c191000001c40030b000700305504a498140d41e589145884401e1010f0615001500040a1600c0488503041c1a112a42d0241040003081864010340e1401c0007003128540391094900701411181e030000000d5280d980c0726140b0700050001240e40c5401841c000e9200258007002a03a1004988a4064102d40020070070b444030a0701400310002c0c607282030202c0c814415084d19003507440690600860400e002041404d02c0d680054413500c2000000002581040c00700900c0329020340c02209149400070181d440401a0203d080304646e03c0c0c040541e99280703ca14103100c0f058100980021010351800c0c1180e1080c481d0000603001200108028101b50321180d80c034260f984104405002c2e80c402e0703501008965200c2c6400701003908a903030200c100c3d0182d03c1a440f5016004a610 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 408985449 1250 408984199 408984217
    0x30907170c0f060304140115090c020303090703030509130e06071d0906011101020408250815040809040905030705010e1e0304140604030c060c0501060501140702040b0415030c051302 80
    0xc0d03510220b0241c20043c1c95000104151041c0d810f80c465500000000c0c4604812101071004000509017080700ca0030840d040d5482c480290741c020003e000d0640d100045000850f40d15140031587d4003036a90200c0c00d2403071080c66402c00141800b180c5000e01a001c21003a1140d44540e83e0070001009c601c21520340320801c0e5500c50303004140710300881c1141d44107014880d8442c1056001520f043c1d56408442d18100021001d16141c5007410741d0024581d03082440c210050000000814aa5000602680f00044040e100030181400040d01c18100d40702d641002c0101e94014003500d40b102c42c5420914040c0c4502210100c1d00e005400c03000031a0481e500d10702070f007480d20070020b505150907c4030301300c03031603644c0008641e0115081c80b0000000e0310050038000506100e80d503070901040c5920703159081d5200c076001641405030519100d0441c40180f403c0c0e550a64044030003040900b81c403008140140683c141404220003c030340040184150700d42c426084810644400e000c50340e054001004a000b581c3d90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 408986699 1250 408985449 408985459
    0x10e0402040b0318011b0203070b013003090306140405010b01080702150a0612230a02010c02100c020a090b03070b0306010503011a1306080106020f16120602040b030907170c 76
    0x1081514211060b44c6006641820001440ba44103029008a40448184400040e44002031460403c0111800207004214561000300c070008a803008061424000700c803055040c1040710b407a018980f04030300082c000d6421001c10000e00240b050300c80c9891804541c00d4a040d800c041580c4602d52160365041d1103042e15038098084418020a0005000c0e009071500001603244d00010800c3e29a14119008480c447c8405410b800f52139100c0b0b40701c040d0701131030b6100190852608140581d070004080a0000e6049400c0c0000344402d80003a01c03841c0c10441c0194000e040d0250125801c90b40d540150780b1228104c00b1164a2591011142002d1000301e40450005006000401c4020000b9006406421700300c80954106050700300040100e40305540014000b440440041209a4041c4004100540690040c0406c1111400d05e80c031544154418400c02204581c032000078445c00764181c9000e041002c0110f03940e41010351040d0f80d00d1003580030b003109041e40e02884000ba424002507400d9080030141c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 408987949 1250 408986699 408986701
    0x3020f03120418020705030d0c0f0c020105090d150606050d0b03061003111302070602030a1103070903030809010905100c18080a030302070f0b040f11060f0d091b0e06010e0402040b03 80
    0x14882c201510f01081d0280c81640900407400029010b0010340391044110000103550031030f40034001c00c0040d51807000c00034002d4035000940540da1000841d58010010344d201d107000280c0c1d03d07051050380c0201c186640658a082808a503203070744440200015842413805002d10024082099100e07281a03440c40808001c0d50030410010300607007201990700b0701c010155103107014018020300a036070100c1811510903074000200280c0b103510384220600100300104890079440e140d10003506004150001400740b109000000311a00e40c00d4200c030100039489010745025140c4005e02c04060680b501082d00881e1120100c19020381c04c0240b42021107030741000030030f0142e040b6102034000b0350240c00162554055592200080350461071841d0050b44114400385466001c0d040c824140c89815000c0c621810081103c40000400d8006544100d140c0140005d004042413410f000301440240e010b03070506007a9040010440d4419403242d1140c41c00b030700d0300d0010468101c1000f00306c1c8142d014004c00660140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 408989199 1250 408987949 408987959
    0x4120203040608060d030201020f040e0109050a0e06060409050106180f0b0103051017030930011802120705030a081210030b0106030c030e0615040e06010e1815070903020f031204 78
    0xc0084940c05006c0d00005281c98003c104914680d03009401101421401d2001082a040b06204e501d921203d4002c00700142008440802d4903070002030840c0d4071803610b64035046d050140a5109100400300e6940805100703000104a0001d00514a07014248a20707003000d0100ca54002c1c02428400e401c0303115645130341410044c9091134040034041240e020b00c020300c000c2c2a6920744560003101d4260078101035140c0f403a2200c11407500303040341d03600607400d9040a590442c410003001040142640c100d80d206207600d002818940303001e440394042c580c14869200c100c802e212000b402031549110b240000250b0b50784d950007645444080f8400100410300344401003044a100f0f0b03100d50941803940ca4041000100890558a03029042c0c0b25490210415051001207103010300c180c9488110b01e50207081690b00d021f10740a040803008203907440c0c640d48820740124041c024070185d402c042907082c1c801218140040001d000607640d00049001c0c0c502032080381070603d00011143d45c16100039030b4035440c00c0e00f00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 408990449 1250 408989199 408989209
    0xd020a0614160317060f1e151206011803021f0e0406030b0a15050a030b070c080a170a09120f090810230c04050405070c0b040b0412020304060806 64
    0x307060301e081d041400c0c00410066403004100e0308489010b641c840442403591014603100c5040684558420500c1c20003044407515400b004010b008104a00d803005e501980b004034030300c01c1d1400041c040d004000108500b01c0c7d4404211280200401c1c0d8600940b02c0307490182440d0000f1602004c0d5012581620381e4611076003071041e20262880501d81420001c013800d000c501a12201d410840780d90b0307107035800c200708955144030741e5a90f80b090040c2d003124286040003007400002503010103466060b5480000d11081d00540514649951002c0400e50314014140c004140081ea444030a50b04540313903000c01d100104502956840319080300f061001032112150940305207034001590814000c031008001042c3c03d091107100922210210302040e402441c0d40141c9080140000104810b6090070600090321040000ea9003614000e42c0c1c0003401d84c03071b0440207552181c05890004c00c5040e08404000030403030b0313000215004520032103030080503614413001640c49016034020a000915110001b03201440c103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 408991699 1250 408990449 408990467
    0x150406090618030807030c0201020f12040309050a03080705010b060a0509090907090f061e0e130201170103080a1409010c021903050f0d1106190e07180e06060d020a06 73
    0x20507440010600e40c450b8002c0550948200150045580c450030000c0e441d4044c01001c940c080d0502c000c40c0b0b8030811716400007040c01101c2c102c0d40040740000004040501a52109014220041ca04286d241d602d1070200d0542c0c0c0103040488841d420164411054100b0200744e4030510344585482d030a191022003488007200c4010401c4403144070740030000502ca000d82c400c041c00b1f04900d0034045001820726100308240000485002d80d28040940204000c14860380e005410051849088055040d02d0004076142659a01100103031080800008100311079500101203200b076580324005100307410348411a0b6801000e02132070216941c1c842010052500000800856040302d56091070107849480719032814464401d140000d500501c002d444840e0004441c0901002c07800c01000c091030016035200030105c0c0100b041029646130030802c40300c1001488900301802c4280600364a0703050520000003d890b1710399241040740540000f00d0f03030605040016821031a00942850140c61034154119000c1e80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 408992805 1106 408991699 408991703
    0x17090f0c1807080a0b060a0c0302160e07050c0312100e010902040f05010f110609030a030e15040b101a0403031103131716090213060215040609 63
    0xa96807100715444101d920b00074009849480042018020008031681d0124000c1000c0c84965070011444240c580aa0b0031150b41c050902841e000c4101c260280e071440001c94000640200e00450080201245070011245410500082d0307170380e80d500170f0300c599a148020300001c101c03c1c0754031485030b409445403820031881d0900e8460303800070501d00b41c0720300780c103201c10307810100d4215002d1a107210111044400f50fa00500c0c00b010300700d0b00d0b507109122484c04645020810300039907c0000700c81006c03440d000482011625070380c46402c1e0316003005004901201d400403001c05c400c1002900c1e00390040c446602c040d282c509501e40501031100200c5241c0f202d074410301083e91211003102010702120b941d03410b07083e681c88030124058140b0f000089960311004148400207540c1c81640d004000c1d842c14420600b1101e41c45c3c5501301d072503003403c82000310160305808c01b080104886912000c0b1043c = true := by decide +kernel

theorem cover : BRFrame.Cov 408812949 408992805 := by
  have h0 := BRFrame.cov_init 408812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 408812949 ≤ n) (h2 : n < 408992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
