-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3165
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:51:39.527712+00:00
-- url     : https://prove2.me/submissions/d041d363-db9b-4916-bd0e-daa97e082506

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 569064748 ≤ n < 569244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 569065998 1250 569064748 569064751
    0x1a0705010f061412061602030415020304060816020717070306050c0a0201060614040302130e030d05040c120201050d0b0315040f06050714070609020102011d0708060c091c0c0f0b03 79
    0x440043c1d900c900c100d8681000c041100ba4103102e4002050942d4500c03844882404040c55403a0841c0410301c0001426100c0244211520032940c0146850380d0a2420003404c015000300081e1a004540403220246038010418405075803560700c241c00307440c11039214a032425280d0b13400103020b00e2a03c8100003d40c41c1e40c0f40500000d0307916a0092054580e030300e808440e0f044810900d0568044108030400051814000c0c403038040c040060b02041034a0030343c52840c2907800c1441104500da484000b004100042aa0468060708120350083c040e00b440390002089405071868626007542d8607000f4010300c0c0d401300a003540510000e5150846498241f4141032008409002140c1050405000c1141e0902614401c7c01d4004813000a6040600130348600c2e000e400904e505a042d95664174020030040412a07200c207080f030801d801005c40600c1c05000a2801d00c0040c617130303100101d00b401000c4199654600b0100385414002c0c050705450020300b092500610a83c1c44400e2112403142c00068510f0b4000265 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 569067248 1250 569065998 569066009
    0x90c041203020312090c09010e04020103110414040c030516030e0c090123030606090f070e030304140f3102120411030c0901062a0606030f0506010b070c1a0705010f06 73
    0xa4551170720b090042d80d5000c0702da2801c1e803141c641d030014041455180201a4420300515000c91004241030315040f0780c3d8020b8000c00e6052444180040300c80c1007074041d088031103419180030000d5282042c20f0a0400031646118020103485000d5001520350402030204950340040c1050460350b516140d0f0340581d002d404085042c810300799100b010a140102e06144240e0707019240000316621f00c18610792101d001029602800005c0c1c9001805480400c00781c80504030792486401000d03100c4041148907403103521481e1240004600c0c85c500811584001394400701441104250405030f106600041c1c003480080c500b42400b407070100b0060011200080c60751401c01e13026690203494080500901035000d00401d80451603c02500d174005009068583c0000c844001751922010142d031000b0581d8042e6000b03580742e102031405e84080c00010700026005040c4000d031641781c40c0d255a035031001d00469110300c100b40213442c0c551248611180044607c030b158024000c115201042d451400280a01d0166 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 569068498 1250 569067248 569067277
    0x50106090e010308040501050d14010b0915130504271b2408100509010b0315030304180c211d03090603040f050f0d05040821030402090c0412030203 65
    0x15141c2542000035050302d0b0028202c0d440c10303050000640e501da008a0307400c001325541d00d841008800551075050701a0495070052a0307035150b01400c000c0305034146250507480030340030411003200c06503013207a1204a0b2001d0380c010400d0180351500080c3c4021044500c280f085070500d041c41000301c803008008030010542108802d15869113002a071030152034800340d00c3c048403000c600d200d50340105080c0f0f500c07042041548080300d4403500860328401003031784590b030380707103400b00a11003100d0b0071560240e40c01a0070b030029030800d845e04002708411625050340304801070b0703581e95500340140300d60300d440d001c1401c54469010084040308000000c1c00085181c0840f102480e044541280d800f000701e40070324000608031070458449499211031614403200807903981c49804038001c603015007030100460110064441e1601c452030000c4076030809150020410a200c0d100d0b06803100d1840c100140c0e0b0b000b60301a0740113412a0780b07040c0007040324855900031b0300002e031110103180f08059000000f4130a01111240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 569069748 1250 569068498 569068517
    0x4080604141f0e011b0c24020a020318100c030f0e0d110906060a0e041112100e060f0901180e030d330e04060b060a08091e0709020703090315050106 65
    0xc58015100300c4440c10f5000422981600c0040b410340030f447c00c541c0c0c1004040760011003501c0015800c0f6840060043d0140c0c00210704100c0c6000320401901031070406072041c000c085402000280200c15400340102400700044500200318440c1085481c1c403070000c0c101d14a00441d034185299821101895584038900c3d07503000034001e041c4034003a5407050500341c4a040e1040410002c107c080e010000010360305a5003840200750003400d6150150050888402c00040342e410840030081c01200103101500500000c4440c0e40503450b2000504e04450741413125000044180d103407039020382400c0303074a00b40c0c034400803d5a00c8464101d900190040400054211020340840004071b050305a42e202e00c0c1181e118110100a07180800a0940d0720500c540d0f400240440918001075a81d046001e84030002158281080540c00e0704004180e2404240341c40452036030b0403411030070741d50440350280d02842c5401150140406000308074003c05160301100801d203001c0d640e426000104000d1040d640001c00058 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 569070998 1250 569069748 569069771
    0x3020d06241d0409050c0d06140907120809221d2406150705010504060f0228110102040905060916140307050c100608010b0604080604141f0e01 63
    0x2400b594504090b41e101410341008101004004c0c8000c0304103803010f02440305400343c2a41d035144450b054a11842000440042e110760403010901300610720103140e03200b49020310964481115812680c0ea02440c415038804ca100082982c005c120b058850000c81142c158400f143c083d6007201280101c1d00102040d40702800400640d40c002184240c1010310482d0180e0007a00102090301c0d512060160040c0d940c2c8031039521190069000c180c02780e03042e954031006e000c108100c5001303c1c0703803486c0d42c00825400d06540c03840328029100d50701c20b1405419058103407540c400380500c02d44c40042255900840d152503031204000094001201d0841c49a50002c0014000160b104c0700e0030081c82040e61510913045806582c1d031707000e41c4041c0c494014410300340b00544d0182001c008420440a90680102d0b1051520303e14038295404400d04522551040c001440030500002d01550b000750000307050791030040034a5072581015a601c04e016111041301d9010000440b4940003a0440c4000c180204100807421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 569072248 1250 569070998 569071007
    0x10c03110306060f0f0c0c03120711090a0b04091104060b0403050601090c0302041802130b0f0a050d021b070f080607050306010305180304090f0506030a031e03020d0624 74
    0x114000c0ca8040d818000304006041810107082ca20903003040301d51410039441c0c00515160090102c065569001a0700240d0a09003480000c10b0740003030501d11800c2c459180c1d100c501c41c0c81240e550a0040c0300c054006044580d040c1c001d45041e2602901c204500c0740141480400750b80741c12002d90141d810070301300280040038102181d00301d0340c01002924090342001e16a8002e000603030007020816409000200d13181c5440100e460b42000c90b04001640d5020300c02e222000484185d1203641c1d40c0c14180100000700611608642c900c0e9000e10300541e60f01010044c1c48024002d10201092030800e0340c1169554880005100003550201340c0e000c580b180e03884180c203588100440f40080080c0007400490003650007a04006d4010a0b0342641242500a80c0c1410b480c1d42c11070391024584135100c00d011640d40031030b4420b00e03030414403e5002c0e048081441d03c001d44050300800940c45c2c444000191a1b02031442a415120b41c032011180602006a4800e41c180c1001c0c042003540000f910000c84881400f07025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 569073498 1250 569072248 569072261
    0x24090b0307051014030403110607030e0c0a14040902061b0c09130807110310090507140d0512031b070f06050703022a0f0111071e1104090c08031b010c03 67
    0x15640b422071410032550016200d0b00081c008600b404044002022101d08c140b00d41d600c501c01176580043c200c00181401e501e00344032550301d070340200c00e0a80203010300101404141041d1005071801f01c1c0101291011a180744100e2507000f82c4101309418080030f0400c0498503c06203001110006405e480f802c40750a1602c0384588000e120105c10000580050b250032201c1010701c0c4001e05072107041c08060808404e40780d4403071085596410207038050203555180c0c7c00302d0000b288141c582101c190a5942c840356540c205500062800101100050407440ca52800003030122141002079112031070780c9800301d902c5003108c104071003460415000440e014481d2081e500c52558188003040f00d00c5984000c540341039039400480c90b00d4018138a00c0c0590b0380c024028000c8549c0c0c0208007a60719001030500c1190007065180b60701c0340240c0c441002e0041010a03600010700401264001450146032600c034400603003c0c2e100080700e00000c0748043d050b100a18015440171070303800081c48280b8400340d088040343d04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 569074748 1250 569073498 569073529
    0x70905090411010e01320c0616030513020d1e15020a080a0203040b060d0501020903010e07030510060b31030302010f05090d1209020a030b04080415180924090b030705 73
    0x580e06c00d018000c52070400c00c1d28203e400000ca14a440b03000400d10b801e00e802100c9841040c408800e0394004540d06114603980301503182a0182400d140345c0c00210350b03a03007100002d41007803c0c43c40245c0c40308840e0b5404034020307a0301c214020b070070742c002c0101071000e50402115800418001000601c4064240c000c03030b4840d5078000c49001d00340d500c40042141100c0c80d0035056030550740c01e100c180d0a6440074483c8000c1c91101000411041c0e00c1d5242c100e01e4064100c0203002c106003086000c00c829104170313051745d15400000200f8201c4c01d6094144d2040c1204034210a01e440c4180030000007071507010351100d6000001c4403c01e00c5075560ba405501c1e510710310b49070f499001403816058540c114100394820510588010f00c4e6103460381d641d4480000700c04050b81c00740c41140c00001c1c2002812201008008200352508001842c035803941d60044403541d203840703803031010781d02c44040c04101c2c1c41500c06401c001c0d408000c02506240c80c1c984260040c00070b0402d0314049c0c483c02e0008a45407238000300c202580c10303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 569075998 1250 569074748 569074787
    0x303020718180813050901090212060f1c111f0f09030201080601051305040c080f07021506060d020c010e0f0c0603090d1b06050702030a030c0c0b0f070905090411010e01 74
    0x14240e807880f0443d44045020618040515804070303556071030215a5009051722900540c45146110340c45400c450082c10051045030407601c01c40150300c5030444042c40128028694400b0255030070604228000b0302400c43d84601410454480035108a4140b0341ca5007a5a079852200480450700b13031081c10050002a020070b545000068156100d03800502d500a17043c050060351640c2d034030205055400102a02001c0385a01c1c0411a0741e8010100460340102c40740700600f8403540210908040140150605006540c0001c00a0000b00f064045610140d00702d03008002e0703d050b8205071500c4044100c8901503d02880311313400d50030310b40f50381542e015140400103003591100407403003621541404241c0280c2142905012000b18101d0f02c680e178820100c0e600a10b681d40011040101180d400000e0902880880c501c00c40c0459003c0c91310950000c81554050a19222518180c13285040741d403045a000d24640d0400040086d499071407443d072034080e2201c490400c402c400545200038615840c44010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 569077248 1250 569075998 569076041
    0x30924021b060d02040f0e0705041a1b0f060108240109050702240105090a06060c1101020f011a090c030c0d0f0b040f090b090c0d060f150303020718 65
    0x1c1c04084602604100052541d407a0421100041050307802980c080d0f481815900800c200f201c0f01684141d9109460346812454581004020718007240d80040d02c51002d60007265004090300301146100d030590b0420100c40060001614081ea0384501b400341d0306c3d040c09070130441d0003090b04040440c401c0340c1c3d06404428141c4c1c2000601401020700510391000c502c50761340b003617a10b0f0300c072001c01c000c00d03021010000000c1e606000c1482050b14025210349507807031610f1402c004241d80308180040f0240d0180c03c0310001809030004038a0500a40006c5038594a0207202009110081d40103886c0c9130340031b031000c13103156481c101040d20600044a40e030b518401c0802c4482034684c0b03070394813003403134006c40a0380003031110200d0021504581c110540022110b0b5502505002e00243c0740c0d489a2082c6e4507401031011035100408191400211440104a152100b21300c40381007100d900a1496182c0443c2815111652410000e546094070b2145a5900310201301c40b0040e0b50f281d000704042d040380141e54200c40d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 569078498 1250 569077248 569077273
    0xf010e060a0e030a0c150f05120c07150507020f010506190e0c0c0615040b0a080316150207050a23070303141204050c03070602010b0d02041d01050403092402 69
    0x303103500c05075079050060700c81a00026904130307145e4010302805d4904c1907180c5130350341003d03081c0452043c0080a000e810b0240d030600901d03185810790b0040c0c9031414140c8561051801c01400c90f42d09488200b0642894108013901c0c0e80040c124440381400c00081c0710b691201d005100f80b01c0701c6003035a01405014070300c0600142d40c50280054101410508841c54a00081245403c240080e10103000300c00c0340b040105024501030049c8421800101ca40c00c0b4801d08c0d105c4440da0b28410f100403020b0541ca080004018130181c038a1aa00c0d1354026042955203801038a010340d1100c0426400716038031107402003003840c0000341c82450b082c044c0b920001080060f00350380b0b040d22050000c08118449007000c201e8503060300507180c551b5010314071510080000280c0d0701704040c01e00300389030080c0c0216031404c82e6144184d43c9040701100070540564000800f01405000390b40041602d1901004a600f480203010030160301801c480f080f21051020052000100e031340f00c401d144900c10440c4016406041001074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 569079748 1250 569078498 569078507
    0xc01020c010e060f03091006060305060a1e0e0601090b03040b2509061b020409030e090702010b011d040b1005030f06090906040b0a0b0a091505091b0d060306060b090f010e060a 77
    0xc11410701007c803880d40b4002854601a60400d40110001a44810038041c160605524450180004800d00c0c580c81d5046860340200d20003612450240c44580004102264080c2004101402034403100950360b18280c10000074140058441c80e01d03403600b01008130030380784040040c88102181c0c4c0e9104a580ba02c0c00400300c4510230581003444003d0701e0204080e00590b03d51140c038224601c2a119408c40c20031020400809280041100c815a414050700410b140e0388000c0c2c03812500d9810890140105030f01d00803174000c24030201c5182c0c2159903603002480ca25040409944641000342001985543e21000e10802c101c041ea4900481d911140100e00019007941e1102c1e0b2110228000048282060001070000900c0350310214405588020150021312002c0e00c180c040c01c1c0a42e200509800c241c80c84501410b50074400e00040940490403903c019519000300000310b0b000319080c040a5199005a525a80a2507485110301c070003041c51074031540100140c03030350000002c00040c2810410f2030b060b103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 569080998 1250 569079748 569079751
    0x5240712050d020d050601020c061602220501121704031707020d080a03090501061e03020d03020705042a020105040c09021317030306102102090607140c01020c010e060f03 75
    0xc18001e090080c2c09072150740344013130107008201100102c3d8904207130f0300190a0620309000340b801490200500100728000720205080c0d40d5050341d101c1c2c182905041e81c054486010800f00182d07504010000649403061007803291401c2c00360b030b0300740181c540c040c03010b5940f8881c030705c8001c3c490404c00049000c0001c1c420003070030800d4000303030810703010341038554403900e860f840b00b81c10a0121703aa072605001440340074450400a0400c418429100a408803102c030102001403000a02c5040701d851658101403003446900000c201c00f030320a01c58801500081c40004044c901034200603419200100c02884c41401814050f0b500700d45050000d0707041c03a020402a5000d0442400c0c140940503001425500329584860000346c1000590784a06140b4100030015185004600420035008221a4913030100c1a009282d0f095916006035100c3c10007001c00e015004000e17024080309003440000e0b61410010035841d1121900740e0a88820a10b510010b44410160128040e00490b00b888000040340c3c00a0045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 569082248 1250 569080998 569081033
    0x3140f1807030c0e0c1207050d1d0c1c202803021c08030a060f0e09060f060d0b0406060f080f100c0e090c04030203120a05191e0801052407 61
    0x80c1d10b01b00000407201c2c4141e00945811000a10004040081d90140d00c22035881490052041c2c0c501044c0c00006903541c6a1003118600c100f4468800050318807000c08808122980118402c0402200c091035146072a581e5115901560342c41c180c003900c003040c2c801000700c0c00c80314000f916412425a02404054025121181c0042c1c841c6000d160110704004059031040703c00003400f041d501d06060441e101c40803d50f005800442d210020b1143c0b14802141842c8d02000880514002d507982c2c900040c2c06801d5504050300c110461014001400b456400441c00c0e20480e6204941071581c6070401d0342d8441050342c940d09550055010340301c0d81030301c1380c000d041c040b007842ca0a810221111000118001402c0d140e4510034400041c04000310308040c81031701c0070000044180c5040c07104460010b42103105449170185d1b151020549040348500a0480086100c220700380705686110004000c2c00d034441c00c1c000d5a2280d01c4080c2080b4284190b00c0700c4041607540455624200600c50b507a0b660340c0c500802c6007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 569083498 1250 569082248 569082271
    0x4021810170c0909061f110102040b0d02090a0b09130b0301020708041d09070b070201030911121609020a0905130e0d0f1103040531020a0816030605061903140f1807030c0e 75
    0x28070741c480bc40a010840c0400300c0c0107980b64030000811800180c0c0d40e00180401c81d0a00800c0816503e0035810240075507400004145514404e0001e03009105510b4003c0c014000400d0124909250b80106c0550700051645021582c960b044030680c1c0e0412803080d0280310340100130f0700300113512a070413440d4094825442c040d0390359910030001ea4580c0020031031b034806500c01201c0d030003010f8a400c0000300a00b1002c4013180b0300145400d00800f1681a409000c0c0944600100c5a0201420740e000716100d0b025141916411030768010010128450442d0700c100044100504500c0c44001104480850741c0091180c54684481c00014045491824119060003054842021220050700040c040800c5c01c2e83c405c034040c6084088116000250340b000420036240020510640c1c503483c0c2120481481d0507151071a1180010044025000c09440301c4615850b003003e1000581c1e2042041c3e004070100c5a080007000c0c3c040c0c054603500c2c82148400740c420804ca980400202003840c40498001d190400ea = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 569084748 1250 569083498 569083507
    0x60c050102040f0611070b0324030312180f121801091d0109050112030c02011b06020f0309190c061b02030a0510050604021810170c0909061f110102 65
    0x40c460b204050952126010403086032200083c0c4c0c03420b000002c0a048400141d48c00c0d810702e501c0c480051480301001c0e00d403041d404500c11016070303002c10559002c030710102002c11480c501209103001c282081c2040c5500c0b4845c094400020701c0011961159614806001500301003030903610181c02ca00b8010800d0610491001c04540044c4019100c10704402e040c2ea0000c555140480c007504a40c0164801c01e1b400901c40500800254855422a034460302480c0c05070079030b0040203402800b08602074001f00442d100189091300d811510010b140b05801882c1920743c9042d001c100c0070000c01a05400416490240f40c0a0008a0145203000903859080c5220b102c11031655020030b01d00100c001041c0d07903039804852541160950307406078644c0140e007681c0c15800c22044040307107950012031240c060301c42d504201039002c0842c0718223801021790980d000601c0079424040682e00f0140c0c031000b0b002c1d001d2401d00f80000c0f01d03030808040c2c04109000d8000854500340708020202d6004c0d6080d480c60406540810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 569085998 1250 569084748 569084759
    0x4030c020d14011a04091a06210109051b01020c101101020a120606090605161511131a0d0f0b06130e0a18030806030a05030c0d021501030c0b070f081801030e0106050901060c05010204 80
    0x20b16202d09e020500014807000e603428401d14001d000d0f400c03030303080c0e000c0c1a10000540c0d034045100e010710031080c0c0d0030310b81c1110313104030903500904506002d4910f58404a80c50021507401104d0001d1400901810081e55460306011581c201c03881c00340401103142000144007110440c0ca030120428020707200000c0490038010110f00741d407110808050440400310320f0850f40c13607c0701d1002d0020700c0f6190a150460300313141d20300340803400342c3c214006600d691150081440291908080d9068800911040d6106d031845a50801d024580c02810304400c42200001c01403103176441510103401e4410808203400f01e156038121101d031002894240c05008201c91707003002030740800140850245010150401c9a40e01400902c3c003058021000c0325a0098001040411102ca1080059a00d500c1c001a5207a01d14181004d102c405d0040081c82c105001401d0100050f03205d4004114540981c0c1c24404031480d88200307803d90301c00d0f0040c0b5a0040e02500100116401007183c1099284124005400d143c0e451 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 569087248 1250 569085998 569086039
    0x90a081c06060e1c050615180a061e03030c020405131b050f1504061b120504090b0103091113060902070501060501030e0303090604030c020d14011a04091a06 69
    0x50340b00344041885208032420500d400a100768035a454145580310301e0140b0b48844d50380d5503010b4003415440402c0080b84440b91680b00c03204d02c00d070150719400802410080d802c0d0000344518450482c3c192421490214103a6207004140304480c1c02daa03842200d1300c00340c0c0801c8014640a0440d0300140c408040000004e201444d0702e46c3c600a801c1890b0011500c0d0105001c001c141c2000201d10482c0013101d0340520145400540741542c0b0140341031103188040c0040c802e40b02c03801084c0030f485540c5034020141d14503801030003801512003e1005221704400d140040d0103031404030b90014822041ea00a805042c1004000c002e0200003941000c2070072036491303100720100c0c0e0006030144c1c1c81f130751110420b0040356007601400c485a18004001d506d14036001e103240784c80700070141c4001c040048180700c9809645d0b0b00012800340a400609501071141050f8103580202a083c002d042c1d202140c0c1c40c10741107407406104608000e034001060340e4041c02010700c0007101500c009c140c59401a520302201c500060b50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 569088498 1250 569087248 569087261
    0x3152d0503160314150117010e0303040c0504060e07081501031113030605010b160b07031515090501020708100926030f0f0705090105030414240c03090a081c 69
    0x40900e149043c29818065507501d80d0961503883c40d402070030b42c442000e03800780d502811140d41c81e2040b094044107940c080d025040c00030816450b4071002c0700344800d00003d14080001c60b882103800301f004031796640b401e00201d481149c1c03c101044030000054260034003110402049441403500050301c034401b640c6854241c1104140a41000f8070a4040c030420405101e041e015081074440c19046c0140003604400c821080318000740141140f03c086007041b80203400c08254402c03010515910f05485401340d034070341a410000107000074055480090300b54008240c1300c0980c0c100602501d0241d035459801c82c050070000c40112000000380380c07100e08581c8030380c0125204480302900e170340e0741e41004880005070f104081c004c1e00b544003000013404502ca800008950b8003030800e003441e68a03503846003082e640301581ca04641ca105d00805130301402c504065424054240010000d01e241030319003240200041c001204d000c08142d02c0900703090045283c12000d8601c09031003184000e0744070060807216064070301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 569089748 1250 569088498 569088523
    0x10c02031f060b180d060228020d030b0a0501110a0515010e1e0f060402070507080d18051c08040b0408010507030b0d0b04060f021608070303152d0503 66
    0x190001c000310081e01802110001c1c4006881e5900380001448900030080e003140509105401ca100c660307042100b190192105140d03810f006c440040d41071340300317201421102062080140203d03a90000458000d1082d1540620090209040b0034240001961607141d00a1000d4107442504060703000600d00300f20010800c2c1000c0402411945062410700c20420050070079131005d01003026541d48806001c1d502d030f0340080307a098508050b88600002c24000e114030f0002030500d004484021640346d000089002d03441065940e012400b01c0380380c824003862215800b0b00d652003480000500208507010440b05511401200102d2400d9a40d00d00b40e003255020340e0001400d42d44603002c00c1082c030380510541e002e5610139600b034140d850207603403071019a05000b0001003807580da41d0b207800264552681034541034824146040c3c05100b144c14966800d07080310904600081c20b0141c00c0389010f2410341064121030700040401480d2016502212085d01d5400750810101c0400314002215135040100300343c4007a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 569090998 1250 569089748 569089783
    0xb030a1502090913030f181508010e0a02040b180f0901060804020901090c0e1302160609020a05030f07060c02061306110d030b010e12010221012c060609010c0203 71
    0xc60905210190750014002c0120302e98130b61405000c03075080300010503620b080d4030308000508502034a07110704003a00d4100c00100700e6462400500301c2e403c02a444c1c10385502420f6650603940d1850928282e109501550004070070a01c215104200050000e4002c0040106402403054103d070100303010050036404100003a0b4454140b10940c140700044501401480d0360521086c610810060440c2d142c04030250f0098080c920400d0280c00e02d90f042e200101c107c4031102e1107034025800c00c18058640340800381d05c030342d0350080002080e00d4001401008007e44402a06613649480c505031070303410f0300f14030580c5c1200c0d00704001a0041a04015440034200340c2c0c64520300c071a0805045490140c1225400301850b150003d0380041e03a8101c0040d040c1c21104842f1004c2440c0e8a16580780603001d80307980e21400e01800000744600c4800d80d100103058031002038954820724901d0440030205d1030340e40ea182520301c1402d000b142d503509100b030003040c43d41d8040c1070414060718594082071800d0346005c1c8011180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 569092248 1250 569090998 569091007
    0xd09170f030f061c0f170307030b03061806131103030301030b0405010c1706060c010212010b071205031e0406200a11060402030c04021b010609092906040b030a1502 72
    0x106500c940f600b015064600c03070031049030840f00700ea0545000c80c0c080c095a04d1100040104150482c0848900444159540d12420054406005031841421151190158400003200d0b240e80c1090404000003000040c1025161560401b20318528420295541c85036000c244110352000c10085008500c01d45104c0e0161601c1e0801c6400c49032443c6040003081420180604540c200c40805900a030003214065996a00003032130350b0080c130400e404000c1e80004100001803100000d0003402c00c260088600038024041c489086507144801c8600000005000d0b2884542805005000b5400751003584000b0310130001031032041c3c00040010040b41d00c50000285080511303841b40c00c5110208500d03000780090300300307a8002a01d034000489501c1c015503022448542c6481032516484542410100030811140c580502c10050041c0304410717a00d054002c0038182d40c00ca05c40c05140d80154160740c00d12000d8651008210190200300c0a031503040c400c040545000c13440e20600c0b140a01c0d5403a000503540d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 569093498 1250 569092248 569092261
    0x1090306020406230930010504140606100909150806090718020c0c0603090703020d0b06040c1b14070b16110f15071b080f10060501050d09170f03 64
    0xb0940d2413240035003070703882440102c41c60b0700c5a481142c4005001d0b20043c1101c0b00800c0301461b6080c00300030b1441e0341d41c24102400144a4021074078420102c1300000da40d000d90b240030a101400391611400c1c00043c85251080004c0915036000d4403601da81340540749034103a903406195203013040a40b81074106170401c0c0c0c020812810503510780098140500f42c15030802e80402e00c400d0b282d600712040030340102030000000d41021010300c80700d8050350380100024800c50300c1d424204030400301152034034002c9142c043c0310000507009018000100382a201420040240741ea540180d200e4482d0000c00c7c035114460012840d00807807005000601d070940050300d2410410b0402c290451801101c0034060400d00c01803410301e4551200e84020300020b00860f6543c1c81a525180b40421102940d240401400100110341e200300800d0340011507412104039442c180162450104544207441200c3c08210100075040348a103d54010452841c0a043c10b42c3c0031a01303100751030400d81d20440c985400303c2d100000b0441d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 569094748 1250 569093498 569093537
    0x1f0b030f010b10051305031507020c010801030b22170c120a0503072d03091209050a05100201110301062109020f040e100e010e120306090c030601090306020406 70
    0xe4190010009111050001d404600c0418040d14403400304000094201c1076251030b40114401414003030112811504145500c0035801c1081d51180014060000c40c05400d620502e2194144d079004900041951204807544910a00e040400760360096003075041d40224091a07412850300340304138985c50342c4440200105040c10303491090301030420700500184018940c88425241c1c809654104401f40015458036194200e80c44081e0445004421a043c031109516401400c0801e214103008003002d00c42c07803400d8550300c0b000e00902e900182d09080400551411140c0601c04d1240d90000145641d501e0380c055103150b00036000600864290160700c82800e80004110a100258200401c90110704d54005286d20b85904209845281c1321340300e50705564424400303010074036003480041100b402c0c80040070303000e465400508038850007942d52001800115408407446040010020901d96945813185141a00050419170400900c44004400100795100410107401ea82c1c403203121507004d4800084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 569095998 1250 569094748 569094763
    0xe0306090105011805010b0a1107031403040306290402090604120503210705160602040e0a150501020109021309050c031204081002041d06131104030c12050a060504051f0b03 76
    0x300d500d4a80801000341c0c0a480065500d2040e46191524000203110742e01c51412b64140c0001e0083c803802e00c01610040c100000802c2100d1050f0014007803c81c038041c075285405003441480c80c2c031201d41e80c40d1406c1031a2030750003003584040041000b400c20361202007807044601c0c02041154260b000040040982c0400340c1d07205185003201c0031704034407881d01c1d403002425802151140741e0f04030b0740c0c618440100805901601c3c0680390042a84c5840c0c900000c401000e804100007240c4811440b41012035194410301032100341680142c20000b1031141c501d81d400041111b040c0940d801e008004800320540d40a020560070000c940080c262600e05002441c0d0030941892540345002d48100410014071000d210414041c0618102d8030142d6600c034004a0002124030900310345192405007200d92200c1d03070f000a00140c0e4090030240c0d0300b064542c0004901c112001801800c6988503210501c00544140c00440d803180c801c0007660091350f04080789400701402e01841107c2652520f207004214282001b800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 569097248 1250 569095998 569096039
    0x20a090f0203090114040201090308090a1d0601110601060c020909160321020a030912031404090c03060801050f013012110607200f0a0b010501080a020910030c0e030609010501 77
    0x4085c0c0d06203a4006001019944401130600c1008134425820303070b40b41e0800c031005000c1b40d48110044a61034114a00545046600d14081500a01e9081240c07800181485c140da69681b9011000750594003081210700d0300400c182650301c906054082e40380d2407010b180b4015407040000000c07181c00e00800b80c00b9603c3e9440030b6811584442c1040b004a94040000c030122100c00c40000c1500c0d1560038229046074001e0280030300b10900243c00110018554000c2d80345600f150b4040060701d03281c800050070303280c2c00c2e5000701c101d42840c401444000c607954903201442c00c1c0721300c550345c844500c1111543d423143c81040980d141c100000d42c680c178654000b802c0f0074001032554081c00395440c0601c40988580c441040551620030303004500000302608112030000c010b1401d049030058090740c81c201030300034402d0003480c0c0016024004560000b81600a440640200410090a80000500450091003040e110b0420081c400101401944060001d180030703040303100010482e5810704c0c400b00f1209605a044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 569098498 1250 569097248 569097281
    0x40f0204230a27020702190b0c10020f0f22090504060506061e0919120501111e0f2506050106020f031207210605010e010306050102030702040504020a090f02030901 72
    0x1e240d01c0301503150a01d0803441c8000c3c0c0050300d990140c00410403c1001003035841c58884114400310b070102024019003101c86c44070701110040b040c441c1c101c109a0040744524920100184400c080214041000d098600090b45040c0d000000c0e484024403c0c0310590b0042d80d0940c2d0741d0b0144024800320380a4035031310071400d4540503c1c0c03190b6146a090b031580c8041902c0541c0e4004900d954040d5a1395102041a000c20388040135050f440b4203140710340c1d030700c01171003120703550328040b030503d0603d0300d00d001d41341d860090031090800c0700c00c1c2c92003809880c1c1c885070041c07110340800c0010043c43c0c0c022070707035510300b980c00d00ea003000100541e442c00204554040e0407410955124401030782980000104035109a20b080f111851503403982c2c08180c52910405504502c440080b0902c14103c1410740d00030700c102c80c000d83e074880e0302c04040d50056045568a014040c01600100101005814a60030240d0003c0c4050704c049c0301950340d105141c007202c0400c907080d003c2a40000501001080074012000407403888001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 569099748 1250 569098498 569098529
    0xa060f0f05010516080c0f0609010e06130b04050c0607050c010f02011802060903100e0d0e0a05210a02060a03150506090d0f03020a0b0f010303020f0105090309040f0204230a 76
    0xf8000c0e0054802200641c0c1c2c1c2d0705a818100301102064a002000d9007040f5806a0041204103494440031168440d40350302e410190140c1810005049018800d40b800041d8104401c0e00c1c0c071900904010401d880c0c03445400d106460640b10360b40207002c05130080028103c600300c20000102615551a40c9104580c1400f1031000340d14000320400401e154112001a6610f1092020900b81304407031401564071864031601c10984c840100d258540043c007940d402d640d0310380c0703641040180138003402500d411040c2440103c5110404009403141c52400348201d50002d25140d00040650b4000441d0200280d04d400c588801d1098071300d001006003800b11249030031710404001144074406c000d031000d485580d40b08004400d15009100070707407015800c001080c0040c0f8201e4000c00080e802172108800501c20320380400074035007061160600840c00d410180d403501c80a48104005084801d9030321a00f59030070440040c01c0c0e04e00b140c18404805c0145400700d0f140350030b001080300c0000b0725400000c0100c014503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 569100998 1250 569099748 569099759
    0x919121701080601150c1217010b041508090c222a210f0212010905040c05041113090608010c14041208190c05010e0325080c060a060f0f 60
    0x3d02607040d00c100860720000c4011040c0100d0360040344007400303408420202d00c1030300c001da409402c1c0101040076526044141e60384041604080c032a030310800058041384903081a9681c401c81c905900509402c04072086a4111400241d4404000c5c0e0100c4480030044104220003442e40600d41e080c0b81010a25100c0c02c44000540c3d10801d04050003108120080039400c4040e0349a140a050584607401c0c208503803035480031008001e41c014030b0403102c1c00801500004240f5030501070644a2a0300c200c10200041c9401c0070f00014060120020031a00d81c107020b0024001d40010b2040003c02d14044e001c43c502e8603122200e401c580041c01c22604102c4000c00954911450703000b15030072a44658420307007e07100a402d011740e9500404000070084013070f40c0a03550380e4607030060780420b00c640100000c00542e0302044619540f0706c07032000007440d2810301c940361130712030212100c00321109400b5141280c6003c207101d1001c0d060080440320803002541c5c8620070f100c1c40c668202140040c0c01c40e8480183d03a1820f00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 569102248 1250 569100998 569101003
    0xf071803080a050c03041d24151c06030204051b0a050f040506040303030c0f050c0a11030a020916020d180512070506030a06090f0b0609010503091912170108 69
    0x500014112540000b10782507070354416411102070982da40e05032919a601d64640142c43c405007920002d100381c0d0035010034001811102080b0a1002a50403d98081920400c0c41903150070318109107500300d401d000300c41003000900741c1c00b981e45403454400242d2500b540304000445201900403a105041c0c496110f1a8000710350481d00c14503c5810103c6d1155500c2c1b005a159100c0c54000c00d800050202d0000b08160701500319006800150315100c1c0020f4007040b0459050207020804040c5501407900c031008660703c0500080716003c080c0541d021240c494011529452040da1444000c00407180b640391041c0d0b050180700340007105482c00f0070100000100b01201c40d440390180d148202c8000c001d0151001081000000400e005070134203840e03182404140300240140d200e442c00180c20091040d003098a64071804c2c6261500801c46030504001c100115415000100480d0540c8031300040c80401c160140d206180d018402c2c50046403074403440b84010016400555403202e0541190010300903054003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 569103498 1250 569102248 569102297
    0xf04021c0501150f1404050907060e190b1306030c050a14070615050406090603080d02030c04030503030108010902040e0c031c0504030b0f10081906020d061d0f07 71
    0x40d030a0042055050782891401031051010640c4034a85440c8006501032000e02e026044642c124400c021070b03c1c014003800207548040720b21140750740001105101c490300400404400a1b800340000350f840c2d0240800303021401003034000d8011544042418480ca041040d560740281090380f806208e4090444809406802107100c80000d00c4540b1441c1200c0310b12140c241d640c250340122052144101403550080061146d00503940a42d007420750104640089008002c1281d42c0000500d03c0d1604108032100290006845680e11000402c00040070410410240d8060082c45000090352032043c41084103d40000da2001e489400c0039034400c90541d0049040000e048504c9065400c015039000b00321007038440d981001b04030320390510a11440003d140461441401c041031515503980d29000c101e030b5210006009410410010317100700c00040d000750040d02d07034455601004203500d83c69001d60101c100100d68020884001e44003081440c400c542c40300e6400454074185510a00758042d54004c90704c2d0b2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 569104748 1250 569103498 569103529
    0x60f080c0f031f1d01090b0f101d0c0c0f0312130b060f0102031303050f12070c140a030204020403080306130213030b10081501031202011103071206050a0b070b0f0402 73
    0xb91080c1c500404c104a0110721000e40109000300000e4100c0d150164560300b00791003041407810a5400210040341c801e8880c2d064a10030b507081c101000344070190160001c40140700c0c580c3c40d04c0610402401e620b00b00905056800600051a00c6602e80055101001d1004044003030074295000c881022410b442c011581055090f00c4481240f01c0310780050385148682c5480d1070681140050010612801041100050320380c5401e40d030400c500d500c003500081c021890046c042ca024510100400000400e140c081c4c07040103001401850754070b40004040740c00c154410780c2e88400001c104042407810396412081011481811401c1040883c0400552846400028100c40041000c80e40b20440401d112000380300210803504450384070200c480f00c604081c031044400100b40c9440b0f00741c05006014100c0c10800d515109070640e82e64610460b511203044015800c00355031440081450380741e2020300c0015088520405942c0c01c0245030401c04440020302500e84501c450060000581c0c590700c0303001c00c1c1e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 569105998 1250 569104748 569104751
    0x3020a170702070e0a0b01080c1920010920121b0619050418060e060d0f06290103020309030403083708070809061801060f080c0f031f 59
    0x1e81d040030a0740381c100c89801510b4199100400c1045000103078010319a00802a039440d1090b4544504c051024054080085801c81ca125030490303600e4800c0da81c5000000003019540000405a486242100d24070f540917a1801c0c545200b056a10240102d00c0780c042d102a140c1d010f51040703150080d503c0d44880b00e125070020040c040da02d5036507a110026140940200c800c0030f013010321094805011640b142c456100c01440d0601100c081c000144250320442d02030030311801d0540e03542420040d1004442e001180c0ca45814107051000c14020701c14214520001c0782e8030320901803012994a07080c1c3e17040d0880c42c1014010010041030040200c00c0d02c084075400709503030792548a129407040c006884c09009410481c803002c10203070100d502d045e4606d4000090b484030b03451174903548001c03180240b00300d07034402c1c41e58000d0300070030007402c03551b4600b00f00c078000d01000041070f03600e80000c401c1d00c1c046a40842c0345a8080b040801651a0009000389207140480081c03c0303100c0001c048140044e0444070440045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 569107248 1250 569105998 569106001
    0x3050901022a061803031603111908130503090d050a080d050f0606090603042010020601050405071b0305070f02040204060302070b01050a060219050c1207090c03020a17 74
    0x5020940641d06081c8064040007025450115050080b140452940c5520700c107007000b15150180300035a401904103150040c518507600d40c240d03080300d5900700008908050340d52224020401000014020f43e82500302180000605280d0041c00c2480140c0750085480d034011504000803000021961a03007c142c40d100b4200406081c01d90a2142071440a00010000542c0002a40c0c0c3d5034004d80c4504146207404209486004c1031012a005080e101c0340c2080042001c500444e44803100c014170805124140c030340760b45501d40416041000f81c082c903800741e4060300050041d03107801e0048a900100306c2c0f07403151800c480994545040f842041000e024084001000300a00c2030520303001c149681c02600c290340d1107036612002002940103000940d4183e001000105461800242c400e044486990090040410000340c03800c80c907881500c110f40714800d05100b45d0642c1c9405038540e0092003c0c01c00b0701901072401800707206840d030408104003014810440500c4090f0040148101ca079800020401c45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 569108498 1250 569107248 569107261
    0x30e0a0605090705090f07090b07030906031d0f010221040b06100329041d0d030e011e020c060a090206030f07031d03130e0402061602010c0b04061b0806010801060305 73
    0x2400d1040c1c200c540c01039401401c01c41e980040c1c80c0300c64001e155581e00d0401503a03444008084500a07010f002f8001030400001b00f20b103520903009654003103940c07003030b0224006a4041b500d161032401459101141d402050341021210750002e40d0542d082e00c040410580e10381551009603048000f401c440c8249000408a00d201e8440d40c480403160481c02c0482c0e030011011009400c0100850b125030788540e0400c0c403403041001c0e5003518441369000786030007042042d100031000d4000e020400c80d111595983c1c2d4400c3c4120403892000d01d198420401c1005070307070701d020717600941c2002002014140010b0a2801610040e10780a040343e81c001c0800c80b092542da1140b620440c00303001c0d190391046803861505030602e44000c010000300850344071203204400307150b590740c0c000c004034408580c065804503003400000005c040320780802d10582d105242004000c035440e55035010512040d10f0070365800c2e540e40c0a201e01148401241e9100c00d065060100840c5006e40009005140500545d01010303240c0d40030400c1e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 569109748 1250 569108498 569108503
    0xc0509030a0611120406201e091909090303061502120d0e0a0b01090c1706040f150e060a09020711120c12010f1803020d110c0a0e07030b01030e0a060509 67
    0x25013200030100d410130b6080c03500b00000680b030140c07002d5020b140c000d5107a00c421001c2034201d0760a0841d40a0f2845201d40d405480c1115030026880d0035006032070603000d0605e8622146016005d054002e400003085042030800500701c44481d04916010268845c0044000340c00142c0b49603100203000f813180e0f03541540ca02075000b8014482d5805c00030301c00d090400081041a08600d07069403501002081203001e402000c4600200c1e1030301c003240c40d04031040481c0389400c1581200180b800040d1010800500c0c00c0c00042251900b584034003580070715142401060314000c228100244041c0300d05500b810520780b02d0b2030f501100070704041d2141140d071700000d886003818001c403040e60340020b14941400c8411219030f0701810565101c800b1140c54401481e249212843c180845580c160b80141007100c07050784141c07035900403c104803101d8402d0130342b8035401d035071015440c901510b102c5407040480e082c540006019a500c1c404080c1c145030403c1c0f48145a80c0002814410050f0484804160f640320803101c1030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 569110998 1250 569109748 569109757
    0x60209090403020109141605060d090b0108100b0603041a0402030a0512220b03070c0c090c0504140a0303081605070602070c0f0b030402030a0b060102101e0c0509030a0611 75
    0x1030300202580e0411003459010360040064900440400c00b52a4000d00c50580320240800e4840e01d10743e005d942404542480c502400c4c1c0b40d958032500141158150b00c949000140980c000c072141d0b0320440c042e291100342805800c510343c005a940c20b056041682c0d4901c070030060791103900c0d0701449440c0010705558080103a920340726000707401c0d950755144000e00481e00b5071011401802c440c140c502400303440f10b0a64004011107000142c0c42e0b0541c0c403407a9080f00d400000030f40540c3c8050411601080040151084000d0b4400c0358a4031a42d86281991198615031b8140d6140c1c420744180c0000c0000c00e421821840d881040080004003100341c0000a80d101d0050400240c0702d1480030441c04100101d90031a10141d40001540181541e03441c0c070404030a101c201c4000b509604024002000201200e032000d40001050054442c0150003481c00d03012540d01d10341281042d042404400c4007142e0070710a5441000d9940307001031a1008600200303076690ba945000520071a0707694200c18500901c80140c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 569112248 1250 569110998 569111017
    0x9070603091b03061a030c0d0201080c0d0c0e1203090a06030c0909050c03060a170d03090f02030d1d010f090314010605090903030714070b151507031101180317040602 73
    0x100c028607200e0800300b004003444083c030b0b1082c03000c3e60f41441700c0f840c00041c0000c82460081410358500d4061740111001c4001030000b8000303103410301508030016098021090700d91020399904510455501c2049101c0400c0140081150410041c0d03414584a8441400941d00b40c0d0401180da5008a0011182c441d050350080d0030651030441405400c1400e80c0045004240c22900e09641d95140c9104200c5401146c4514045912400d8601c201e00e000ba0040e10312980031304000180c1180c1e54000c41c0c2000759558035031001900c14524011804040900e003500780600386080d11450800c014043c0a42c4101c0c00701070104084c0d40944018a502508008040d01018001c00000d042128031244c1e290000d40d0b003140403902c03559414030000360440980c1c40b001d800c8913000d001511000725440c4a0000f031244c1d81d800490555054020241541c0103050192095982090526030250b00d1421140351101c26a002c1407051045404a82c3c4040441c1c0351054200b141c4a050300c1c2d03450118020b01ca10300d030300f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 569113498 1250 569112248 569112293
    0x504120b0c040906080a120201050f0103060b040b0603070e040c08070c0308180a0c0f05040b01050f03070905060a020304061d03070b030901091b031109191806060f17060907060309 79
    0x450101c5d0081104020180f03d4241c1d661108041c590603070903100c040301c65021040c070728001000400e4440c2c00c80c154101c4003a20010711460007a011510310b07402141c2c01d102007514030b400060b00741000e101c2c00c10070000910341280b4a041085005203003400c85000a410051540b0220711010000c0301e5070303228154003104481d441c080d60f151960901680f4455200e16524980d00040d46050600a20080101c1691178926004010100100715003000d40f83d00100301c40e40c035010959072070f9500201034201160300155151850f082c4c0007845001504803080d80407c150070804981d071000200703882130f680c2121040d61a41d0f11400440d00401c05110050198005248482d4501c01406161401e0b00c6c01410410200c620040c244403c480043e9a181c079000c1040c123408085861940c400310925074499800b00d02c02c204c9498400c00d961068201c1c4200c0011300204001c0600052421943d244400c4d0280c076440c03400c150b04a8582c14140b081e24241030321544c1181c104074060156440d02080040ba = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 569114748 1250 569113498 569113511
    0x30f0a02010b0a1d0f060306040f262d0306040203220c060e06031608270102130e0411010e0d0b16081f1404060e0403020109030206070504120b0c0409 66
    0x1c0c034002030140520301081a100e13000314000558131420700c1e11076880a03005140c59140c40d605c6101349644404140c407080c1e0420303178104001044074401c0078812501c4c00076640b00c9003004254440300c411503088541c01c08002400c3d038030f20702d4000b00f41e81d8030103400c0301c0c0141c4030340d2031441465000c3c540384e4482a01002d102c1d130000400100c1440d140984401e82c1c1e078001c0300011501403100d00d1005480c0d1504120b00804d000c05043d1040320b03911340c0241910b104083c44912100104510721185200c2d4aa607500801da01c101e06002e1107080004100030a111562420141c41e00300e140c00041c50131504010340302d281c00da0030382c0b00e24408841c1030340c2c0203101c0d00b042d10380881c01c00d40c01c5d03240c80c070310b00c002070038071004504451500007860160101d0ba224002c0c0072031031b010700320100290070642c00b6080368035000001524030041560381d21540c02a00041501e00719880c00070300300200144000103204c0d003840706000c3c856180d03014050b00ca600c921402440c0d11012100c2d09503015561080311102d08003003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 569115998 1250 569114748 569114759
    0x50f19080604050106090c0c060903110a0606090e010204030c090504081c0507020c0a061d0a0b0a090e07170601200303010f2103080f0403170c0301051206040302030f0a02010b0a 78
    0xa081c0d88202d00800c001c004c4a61290105010384a6404954001500880010021810551020000707038428100898440031035001c16050080d100c2090f03403195903503401000302c0f81e0715008111048644030021854a401e56480b900c1603981400342a4a059683e4000f50810201004035500b1b071020849100900305074080d400090501100c104005008142a0013810b00304030906800b036402ea034a0341030202c40a0307444034400da01e14480082d40801c603010009120001600105640b03040d0b40d45146085081040200000780c002d0300302d1040000c01001825a50b40c60b0300002c0d0008000d1038030b00e402840e040315100c00010184490750103400008000560a451007031001e0403140c0070001e60f2007250b0b900c0b4984502002c441c2000e0080380346040003c10010944001561141c070074200921848299078002240c000b044030010004400000140180c0ca0240300c080b00d4054108028096841c059800075102d00481c1c94040582d0008990600d15074000e4006030b011002c06806000c89690300c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 569117248 1250 569115998 569116003
    0x109050303040f11090c0f0d090f05150f09070b0c0321010f0602010509060402010e0d08030403080709140a090c0e0909030405040b061e071401050a060302012601050f1908 75
    0x45004544c451032140d0450314505000c95090310580700642d0113400c224480c02c1011395913000444107020650394115000001e13003840913407e030840c0175500405061113129011405510054140ca41406100040221809002807404d060310349100a0307a032180d401000d51440d5000e00346c1400300300c19a02201c80c0d4a0031b034080425049406450f60104074071366800c0300703908076901643d00702c4154201c0000600954062404016980009400d070703404008182c0350300005400030394080300024002c4040c4040c0650040341c0d80701034000c6800c003902c580040c0380042e882a80900c1507280998a49090b6181d941c001e01d0300800e88400a02540100d01c5c143d05015125403080c003580b40300300e190400804480c1804016103212140000302c4004485042d0f0503c07042d9046820125100301001103d581c00c10030070300807140903140320303070000c00d0841c02c51002400307015580e00200f03034100c2c00b04140c140c08200402035070b044038000d4918001c058241c00108850812104804042d1020701d10006100c0400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 569118498 1250 569117248 569117273
    0x220b0402240a1d3d1403060d0f06150501050301080a300507052e020f090d20100f050c0f03070b010f051c2009090304180605060a11010905030304 64
    0x2103d0440c8a07504c016184036402d0710001d114000140d801501c0b6103600038080001c603000078004080100c0c0340c810365100001600002000c45105480740c0c45c1c0d2400c9002c1c890b0b144054402424030500f150704000d100ba564486540001d8000554190b92480702e0300c001810300e014200990b959080c0e044203242c00741c03a95020110482c1d02e031140b410360003103d10385040300303159a0254042215a041105200303d0280d01300c40700719034200704100404011692011f40d00c588651190a04500a001c241d602100d007038806d0b01c10a025550900710240a80c1d1701c0003403208994680e042040d15840c841c00c44500d003066403c00e15001e0701c000a80c0406002c2040040360484005d00101c441c03041c0c48205008810501e03054451809002c2400c110000e521845d00380e04007903180304018400c00c200700000e10009025a65100c441c0c1000406100c1c4012250100b02c016481d503d003400310398981000b040f601d20170a10140b082014420b07035810840c40c20341041817103903000b40032a40c9031f050508060110380403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 569119748 1250 569118498 569118559
    0x251407062a08040920070206160809130b03060a05042a050a06030501080609010605090103020f1315090f0b09070807140a0e0109080c01020c0405220b0402240a1d 71
    0x1450503007150845e500c00111040c1a80c0640248e05041038000200701c0b122006d401140d501d50305101c840450f403910070466900811800000c0707940f5003c903041c1802d194000d0301d2003003013600740710802c00880c40d003460340a510000d5543c4003c2c4d13000682c2d00c0ca10075908540029601c40020300000401a0b4150041c0c1c0c141c1d40700c8025944a504c407030129034201c039154400c2079006681c100c0100054602001d8020381003c02410140640e80f4907d40300003100d5001101d04100f100c5124240034450303e4ac402d0045012001c00c0400c004d441c0140010403c1000620340c0c010040003070005014148a140c0704022002462030b42030700c8444600f0094014608940030078000340f0301000015003c00000340320001c000d41030300a0071103c15aa41808090a40200300c90b0441c03507807800d900918808800c6521005000c1c2c0300034102c3c1c1c10940f04000740b084102c890015001c10313415100b00c80031150030440d40c05540e5818005d0f10303034030200700a0094909603500642c1c000d101003c4900c1d4128030411041b80c0c0b0f01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 569120998 1250 569119748 569119781
    0x5090303010306380609030a20060c1009020628081b0a08090f070603090606080c0102120c010b040603141507050915251407062a080409 60
    0x250801004184107490300010500b480440e44100130b641083c041030304000034050314040ca4142c607180807030310345500c0e1501121b0010003c0001c1c1e90400b000c01c42100d158074121035591904411018265403240c034651808085690f07015020110350b00c5008031590100858580a507072034480c05c140d11029900c21140c0d01003280003000880d0381c6e1614507004d2103802d0030f001203070130702c64000380403210305d900186203c00341c1c8070304041229a07003c200003807030060825039000f2a40300000c2c43c0402c2a901d90b9800100c0550180603003100a0b07030046080d200c01149040c503240c40d0fa61440955016081c400203641c3c00615089002c000c1c840b420070f850141c462038008031501030303054064007030800204a8580340000d8050289004601e4941100c510000c000000e0318248400c142140c1c1c60700c80085e0390441030710b480b131b640c01c8108010441201c80066070600a03007451854400042e03c901c2024040d600c2243c042030107a42c0290481c10425901c0e40c1140340c4a86640d22404024002c1c2003070f0702a0740102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 569122248 1250 569120998 569121011
    0x71403160b041a07050412050a080c0f011506050703080a06030602160204050f09120a0c0b01080d1b02030705091e01141305160305040c120c030606090207021e040204030605090303010306 82
    0xf0700c08007a107901032482c03581c031a0f16141c90414420603440368087c00300c8260140000d90700120760f82001800200030380c10b010340354004243c9151805c442003020500040d801801003080781c0c0f03402c1020341d4601501401c001a0a581304040d120003400385800003000188049191a0340051400c80d10386030320310070341c1c0070001500c610b0900d1040b1941160020b07000d511030108100c8000740b0350050001004541080c9a0f03070141941da071910098241c01407000c607071001c40b9070404140c0c0100050344240d03640d0b4168070110354540110351543d0b001e00489005e1001800031407551010040d030b86d221007611f068051703000c1d612441c00380f080c00740101c1620b04c600f0b142d50090b10019218031625015040b80c00c001c0304100c5224074141c0143c82c0c018403ea40d9201d440000098031410b00c8503c1d08124801c50040245904618000c8204d034800d4200c0082d05d0b1051101c1001170321011815100e952040765119030045690380000c02903c145c1d080205214108014409026000009141070307030311994050014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 569123498 1250 569122248 569122283
    0xe01030c0509090109020a020f0a14070f06170c090627030f060105040c0509030a0b010306110306031906150b03040c0801020c03301e011703071403160b04 68
    0x21405030110b4154403041d06001002201c0d1940c0c001d00d680011401620400c003c5410014100035158405558025900101084d620340c00d110031000303050742d0b0f6090070301c1074140040100048004480e001130700100340d021803110708c0094240c400d0254020807440e03a4411061602c0c41c1e018203034a0040f1031840c0d08090780742034500810602800c0c0e40140003421641e00c0c11080101031b08170280079a051040401076618541c42c18001c031040c1da809070013662015450351803c0d60444a915285802c2d1140134014002d103942c010409140020038041d503440b4010490170044000c8c03121821900803030054000000d00702c0701e1440558410b44c0140c1c1300b82e074440da640414038280d01c00c070300e5605000d030801c01c03520300904038000b50202c1010600c1d860124401846891030011201580c01c51b100c1456294000348480d0f45041c1180034025000030f01c003c4c004400b080d0f0741d903030094480040002a014208a00013101042920200d034000c3c80d10100c6440c0344d0804410584095409443d0300c110121500d20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 569124748 1250 569123498 569123507
    0x70e13020d050c180112110a08090d0801031208181c0306051206010302010c050f1923030a050711030709060e0a0207080d1d1b0a12020310020c07090c0e01030c 70
    0x204d641d0b01c0d09500c0003100c000d4011500310401401da01885644d41d2502410303168241c001e00356000b1140c44119050030701009841c84c04c08500300701030400500d40018400203d003012040d6420441d41480c188546541100d404000d520b801d2015043c0300306511062816240a52115034089944040080750740b51001c0c032030104010020b95549501c854010401542308454030001940244191056510b0952400e81050311041081c40076443c2d1440c19424407d22880b00340c1070030303447c2d08071542c0d143d036180d02c45450b802003070014000d00c08045011020701c9490f00c105490998010281c0d403c846d19070100c40002d00340d07030088200c2d0411041c009844140301b40f080300c03c1c2030340104085050000c81c010010252006441e0030740501c00101ca0240510800c1005014400f400201e003c410b202d01c0091201c0b0a2603035000c0c42c1482004d540020151310082148041d2004004000d0383e1070950070001441c01c4102d40c014509645400c3e558a10260b00c03804e08510003100341c0e02445030551110f41100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 569125998 1250 569124748 569124757
    0xf0b01050a05032d07090504050606180402011e0e030a050304061701060c11120318030c041404082d040603140405030a08040314040b071e03080a05070e13020d050c 72
    0x2031042c02d00c6103141070405400c01251400384c038201c121011152214080300c02d590701524201c5681d485501408800e14180c07403001c40c01020b082c0700701610328082d0002410501444200322140c0724070b00078502d0182c8510040d504050019046801002c03503460590354070390040c40740d01c00042a07410070301c18240640110300d040b41c0c8980d545211076a01901c461540c008400b0340f0320750061030b04100c500b45100c14000350001d03c141300420009440d43c0c405142c200020040064882c82c038010b003010600081041240d00250404500b03921603005001d0b580d4070f017005403452482c03601c4525102d680c6629035001030099983c15501408000c41d000300c01800b2100070b44001301240c20030f111a001c014410000700c0e0788a0302030315000c030502d0710040c030241e441d0703210360001500c104001074080280f00d200007040c0d0301001d50020b00700140303206803401000c1e1107024001d840307410b484a011551039480341c071681c0ca0581c40244503846031200244d244009500080a462801d41810000390742c10002e401a60f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 569127248 1250 569125998 569126023
    0x7020f032128050a02010b031c0c020d02030105010b031e07081303031b05090301060e01140603150301050f0a150501230f1209061803070b130f0b01050a0503 69
    0x6250100000040350310360002c03007001c100e03410800c040002810081d044041e2201c42c1e42c6800c1ea0b61007010030020f080d10342d54070a040c0258403480416601100b0402d128060180500e8440c0a202c200c0c4005500030000c02c001952540c281000030680000e9840210302400d0100c4041c840c50b45001c2c0905001d0004855520118241d840090761400070900480c1c4154400d190000d00c00c2c2048617211000b4010300b40d1140003446c0451a603030b440c10244512030190034500d0002c582907140841c030100d000240c4051502800d4007001040c420001076100e0011010020028002c51510320000002c4a808507050880b041c10003003150619003070000c2d2817081c0d03581079450320907154410f01d15082605026000e40c0000d01c007004010300c80d418400c05842c1e04034600b941d10195003009800305103400c0c2d001d00b00c01a1010002903800142a00108458080d81d200329052036503941c2240340c0c059400403270030103007002018041020408c41a0b0381c02c241643c400b259443d492544880a0503039403451485603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 569128498 1250 569127248 569127283
    0x109090903081503160b0d0e1605060a1707210c0c020108070c08030903070302061803040306180209040c050915130504140a050d030614010e13060f060507020f03 71
    0x10820108a20b504143d81c0d88001e4100c0e440c1104850380819401c0d034503440090041004140840881b621b40100b40e07240b400100204100035454000c1e1359143ca00b807160318410b400c0080d1050380d050055820301994254080342069031f190000d809040c0c2e4200c1d01c01e10103030002140040c12480b00620800140400a5440e8011440c50358010b442c0074202414510a100301305c90340c0030001d041b07600250f02c0348004001039512441d0700c1c90080d00c1d10030701421a5030900d0344148a011a10000015501281c1c3c0201001c00c10344141c80c098a120310a90784081d40249a034000c00c42405009500b0030111482611800034680c0c41500c04040c66030f5854069620400c5048040b011202c0303504442e8000707000728820381003050040015843d000b5130400c00c40b4160003c407180c0502da601846190001e00300c03c0039403501c1c46040e40000b00000204094213108541001017500c06201d29448240030f45008a81c000c00c40752501c030042d2203500300483c100d1160743c1100e50140c540c2008903503203031242c41c038075203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 569129748 1250 569128498 569128501
    0x30108010b030c0607050d080c0f0c0f0705090906040609081b010e1203101211040c0207090c08062107080f030c01051509010b0f07080d0b10030603050c0d0c1d06010909090308 77
    0x1f000c032181c030790140034601c40140911409814040d07210040c07840042007401414141c401c030942d142030003025403040d8419044482013140f001d8001c81c00591056102000049130708162404190500400a145440d11840c4002141c0004154094000d080d008000c0b40d21518808103411000d20040350480c044900840c070400c80d840c1c1c0c0c40c0e800c0000301d01c2800c00d0141128440c0206084462000d01640141c0c4885070030040e1100314460b880701d050701482c0154182c544030020038011442d000d240c1d410200100001a0b03c800300703020ba10b0260154a094039540300010b01c0c07090f641c0d0000c13044040194a00000300c0d82c0c0c80680018078042c0170b0080c10801c40e030381c60190054182c0d040381114441c01a410484440052030380002030090001440001404e00f03140400e20042c0d110b0b031003e890074540b0b84001813011a0380003900396203c0008075103440715182a03180c00200000642d2007244402d4017a04002140302c0900022841442c080c1c3c1d8004006681718503200582d2487c06024010031440710 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 569130998 1250 569129748 569129773
    0x1e1e0304060f020c130b090702010203070c03050d0b090a0c090e06031222090c1e12150314070501110a03090b09061b0f0606060403171e030108010b030c060705 70
    0x41484020b0b0100740152204000740070040b0703030281c040b24250740c0030390380e60025050949044080c064226225200031821450202d10250401c50001c801400348607021030400300c43c40154000d5001200302612403030507802c1203090000540744410290012901e50344010440c11070052079144600d1009000702030350b841440f0b81300c0c5c242d40030780c41e03105410391000d55403800c5081e078644102c01049044000100c1420128004010150070120030f0490316203400401102517001c203c0d654913281095000902210514255030100d10b0799000a0414030049002c50b1030241c0031070190212070b401e803925425110550152525007100080c000e01290100605001821001015003070803540a4403061420390304e0036441081920a0345001c50b1a07000e05000440514180700c031a4000c1025030790380f03080605545d505103071000250100320300c14502143c0303101c59504011030701c02d1740116a40301640d2540c65000250191400c0700c450f6000e031040c1d07400c56031541030040480c1d1096400ca40030b060f0030241403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 569132248 1250 569130998 569131007
    0x120316060b1e210307050a0201020106050607031205151203030402090106140403031103041d0907091b03090519210518010806010306050a060521100b07141e1e030406 73
    0x8100000000f004501840b00f0301408000603c0c1d1140501c0c010b0141c0b18072803000a0035510281c00c0315000e104c040c005100001d410000b810000300004402007055560f520750018403032011003003207621030508020190b03001c4e40440110300440c0290380c0d061090382c1f2401d0545041c41030299205c00c00c04104420808648140b03c00c03911442c107a8180c0e49483c0c0c0d51907400203480c04180d407611900300544140507140340100f2a060003001c0303a4205102d0310a044e01600000c01201100605154954103c0d60030440d05000303d40b2045050021074000c0303603507414401c0241098a00308a18184c1403d46403200d6400364040da0400b445151070911300034008401150310305000303014103042c913443e40b4002c0381c9943e50050200282c00c99507151610b40c11000070680f924285502c0003c1401c09510900108010710004a4241c50b40e5442c2d003035842d460362501c2e05c41d810034545001250300804443c099918040f028055022000500701d608013040d90091800c051000c02c009412540200000c00445004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 569133498 1250 569132248 569132269
    0x5130b0705030405010b060a030e0d0e01020c040b04062105071a0304020d030c0c170106050f090a0228170c030709060f0201090b0109020706060f061706120316060b1e 73
    0x11000400e002d440306d404039981c0d40044400d031000c651503d5506211001c10804110100c01610b441e206518480c00042d40300c03070140c07805070300030b5868155215460b251030308644000e00350400c0816a00010742082d000b850143d54080741c0070302540070005070702401c82442010010401c64101d142d62100e070700700b00c00c00410306012410720003020301001c0480d201c2c1983c03400810300c55035644091030721824100d0031038a180e0400c0e88140e44540140d0b0489d101c40075011752115042a00680c0c80804070f140c1c0c1104541041520100c5141074411074119620261103100300700c0c0590305240c1034480400c10f41c518001121000005004010208500b81c4102d640712704007042800005680e113019100d10900721401d03040004e0b416000151b803c01c004140c4222001040d03802030501c01c40342040340007400e0110100f408141546140c004c00d04503903405000c40c04510545044036543d83d0766180440894036404800d65205241c03071501103c60401064001c00f00003032040d51181c0004003c00c0110501d507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 569134748 1250 569133498 569133503
    0xf0d0c030605090f07110a0f081605120712110a060902190608040b090609060f0702011409060f16050a110a06150e2503020703020a02130f05130b07050304 68
    0x72a04030000e600d80310748808600070010611200c03c01c5c5041c68019080020141c8411300e41c0d40401144c3c404500032800000e685903002c03800c1645c414032005100b083e010341e04030190443c050a0004450610103000034120340b8440c5011010340d052000081d580b6500343e105100c20368001001c1d04000031010380c08071800d144024091200c142d9000d102010301d10741900110081015070b010300c024070500f0b03000d0560145104004040901d010840780340c80700c00c05050081c4000c1e0040100742424004c0d0850401e01d4190685149a45043e40784565111802e9800b1403010701f8640201c0d00480c54803248085101694440518107a100c400450301e4a100001902c2240146528a00026802d000e4501b000300c04d1070003410704a0030174084102100000d0411011144204580c405100d117111000c038000115060050701c54542d0700b810b9007032905681340203503c034482c1c1900340c029080b564046241103103910002c10840d03880c0c0f01a0300080d00080405001c113900c0c540001d041510030002990b000c0d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 569135998 1250 569134748 569134751
    0x17040609080301080106090f05100510020c0613170a0809060901110f0d0f050a1b02060d05090102030712020403020f22020a030b0906031c0f0e03070b07030e060f0d0c03 74
    0x15035446510741a00300ba088240c10365140c010400c80b01d8068040d001c88800d141c1c100f048203080c02c20072020385504520a9500036081c40c008501c440c2d009009003401014007a1a055480400180300b601d160000d0082891081580b100340106410010342d4407905a440704196251105820801070b035a002404142e040000d501411042100c00307002004c01c8141d01710041402941079140500170369000500030040181c20300c0450030386980a00c10040020391441513445002003030010800d24440c81c0c03491866541000180200e00c00154001d621541052303032203190315006a02640b007a03200d01d00c0302a6000501045140551400010381d0403404a544a01000d041d4100c80300d1091303070400315110340443daa5884a0382e19040c44008140d00103801c07005403030b031445641e031300081007801101c160701004004400301220754050800c10b1690040141140d0015907101c0002c01e20380d02c0743d1011030000b03212540e00385070b07030074204181ca00b020020400c1c0d504040ca41c003480802041001d000f2030805 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 569137248 1250 569135998 569136011
    0xa020306210703020301141608040812040b0105030d05040f0b0a0207180204140d02130903050c07030c1d010b18010c0f030315140f0d1103030c0a05070b0a170406 71
    0x20701d80d0140c4200c4180c00c00d406055820303d1401014212aaa4500382406070610410404051a2a002110a29024280050303551103e00305880c0500030b8000c141021b104090611051105414007107048840841c1210510041c2c280100d90902441c841c0582445d8841000c0c020640c101f0b010f410b441e140d9104491509684406201400102100044002e5030008040c0f0910880d8084081001001c0c1e4050100300b0880c2e0216241d94607694855160541d0f9002e0401054070540c02c64041d0b1000000b25541c103510703414042d0b02c2034564410074816040c03103c850f550504468112a04945c0b11420507802c100100000e00040510302c41d000d410030090740b580000103184042280c901c2c80c003c5c1d60019450074a400c64001c02c03041a0842d100134050510425044d9450f101411003c51064034882600180e5103000b0510000c04203086505005c00b044030945103c00141d00c802070707800b034012524002d0340d41381c640c412072198200d864006100400d030480d4803040001241e812901c11800040c14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 569138498 1250 569137248 569137279
    0x6180501111207021906180236040b161e0504080d0c1101031a03010603050607081302010e220504200a0f09090206040b1206011103120a020306 63
    0x1c41e040c141c01200e4100340820900205425101440d9005040d800200120000c6102c1c010340f40380311030f000902c40c41c1c80300c503003010009425001745a8030f907001d85070944021485170b00b84611440600303603c040d900702c280b405051100901c001c031300880e0407050100e020703103a1042d6401a000030243c00010b004220803d030807490800180500301ca181d030b981d41500c481c10f201d03603d03040c41c240d0350140080184414048010461420804e8414502400d001900039a020342202807900c0340350b10140d15510b450708c00401d001d000318005203e51903641d9100003a03900c80c031442d02114041c1601900203650f241072010103081040d85500c85d441c84a44404c9081212142e00054a400711402c07109405482c40080001100c50341c0c0006040302201d403e50081e04010203070700f100d80c540c4900c9a803e5154007004040d0340f100001ca50280980f01000d036a1000301400f0146110030aa5143d0300080d03d4040740e8505c0c43c0b000c0150b0b00700f0880c4040600c0c032604c1c1c011140b80070750005000c0c1984107e40c0d25203800b9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 569139748 1250 569138498 569138501
    0x70515010305010504030806010201020a0806041a040501030602300c1303020405100302030d0e0102210c2a01031404030e0f0307080a0c21060507140c011d010b0d06180501 75
    0xa42c030800c0003080380d1415250041803240054580c905580c01032254408441c0c120701c00d075600c2002620002031030781d030481d8602c0a82003082c2d41990001c0c6001c00102c1445525001443c039186034902d42180d03261750b04000c1c6c882c04500301031544c400400c000030409080c0c0880003044002d14241400c410740b901c030380004044407002d4035250f20b000300340e1500b08118201031210390091030703c0d810611021503401001039101c1d01c8040ca44810f816a00000c03005402c0342c2d2043d41c410010000c02c950100721001104002040c074245c4000f034031481010b010680b503101c0c0c080c1d00c1280601803050300c03294480e6502510560380c00d16529912141680043c48a6101044120000c01c64080100404002400c2c161400980c98010502943c84100040090103558400d82d60b00c6600c000c0024840d42d0701102225041c0c0c1c0082842c203807175800a8009104038054010041d0078101c5429010390300c0500d1080c5080301d100c011826005007002d4a0000459800d03484800072103c141820703081d00c0d515594190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 569140998 1250 569139748 569139751
    0x503010e07052514030c12030c19020f010e03090f060310090507050a030e01111b120a0302040e0a150b071406070804120c050a12030f1d010c09050607020105070515 72
    0x103403106103050009100b030031441e600d100c40200000e5403821014040050311a00c03000c0f00e28807c58000008194007940b10300c03c907404100b50280e1100700504808000751a15600c941c141c076550f0078111301000d03019012040317500050005114440c00b60b015030034440142c000a00340703140d540700d0110005032114107014292040c5001e68034656124400080503086842030700da82241a0314003060801c4041250b4121402045225000e0b45000d03d0340c00000e1070f000c01022003001814000c1000f0181680580181c001e6850320000c101d42551401601011188003842c0ca0060400c284030070420102e40350001d1200300e0040444841d40f12a00c448030785400c0c0c01391843e000103184481048140701c5241f103411541c01440c5003490804070706407a0141d94407034020006c0c01e8100810054031880380282d00c4440020306850302405400c070b403c034084040c98000c0b078811500354205150182c00b2845240600d05560b4020001428401140c0044649800c6028200c5451043c4008460011461140d03603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 569142248 1250 569140998 569141047
    0xf0c110d0c050406080111030714042c0106030c0915090b12060f09090d03050709120f0b071b0825120f050909060907120c08061c030503010e0705 64
    0x90210703152605010441e03030799a00944080c0d2500c03e0a584002c07400003200e410009c02d2510418424100c0030142c034a01c20381e4000da40c1d00300151000c194030121001807000c0b9810140f2038506982c3e80b0700040e415184255840c5001400c2c0344001e2120515100e2480e00c0c504003481c2400f1340d07545039179100c0d03203d030300600a008500740035a0030005140f0b071214903440302600641c2c0528150404085603540d40088200010a150f11000010032803403146c1410402002d0103c0301090501040c101207410840203030054656401e5003000514003400360b8600c00390070700380c100303030f0441c04005071101500ba412090300d6940012070482100e40005c0c0704200e564465009201004225841c010f0160180c5440380076031301409028880c951a507a10003006680c014000e0320200c03100e42d44c0600890708401144800c1101c68905500d00449940c000c4900703105e56016122030740781813a03407114074902660440004000410410050000f40c0c0200d80350303a000780040c00c00c3ca040c05501c3c00704c1c10000300b6010a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 569143498 1250 569142248 569142263
    0x615110f0f0313140a03080c0c040501261603170c0304030c080c0102060c1213200f0904260906070818010c1509030512010f0f080106060f0c110d 64
    0xd00c0c2968035524403e60082c18184034001090030104003040c0d00764124400176155202c04580391040d4201804200c40c11b000003001004207607101c13041c03000c01ca400b10380c13001c41c400c0a9000303401c001000010f40e0203842d219251308a01c1030340765685003110783c1c0e01015001c8001d04103204000e50500c0070000340c40610312500181c500c05081c8080b66107001c46404046046501c008140300054a44004035829541000302040780344d074419000d00301321245d40000501c00c40c1070110600311506001440c81c50480c08440038000303440490200014254150340113407141c80c200c45821005200100f01d1080101c040d0072032414007080300001026904141000d46072208001782101c048a4284038026480c402420500100c5415031150b002070711801c0ca01d04511a500c000090038140114180d0b0790b050300148034000c403981c45416080c6120f62600c0382842001e01918040ba43c4c141c1030080300141c074480d0b680c8180d02d41e42190201c40700c401c1c2580941d00070b600121040300b40c0e1134400d4030321841402800c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 569144748 1250 569143498 569143507
    0x20418050f10150b2b0209030c0105030405060a0b0109080d02010903031116032307050304050109150c11120604050c030601091a04051503030c07090b040615110f0f03 73
    0x1c10724109074000303580811092a2002d5500c03001d0030918490240d440c1d04012580b9120028500c0c41d80c0c214142c144d03d201c100b40117074040b4003134094005220070b110a806684440341890300648140c00199030041c440c0e000b000c002480380a443e403020042590501d00107800b00c0e80c0e07203d12802e0100c0c4007580e00c0180d440754505414903416006400b01c25034000e03412441c00b01d07644e5440d00d0445060800804008421482c14511085e60004000120340d07180324668400492400315aa90300900c181030103c0c0c1c12034800207990701400101802030606442e015012502503552026100c0303c000b40c594030030f40e032840c0d0f044440c20812041d44503d2182004210005400080600d40801648443d88850402e000002046030a038840d010894007a1004500e640301c007030b009400c0c2021038542e50341510010030380000c00c4800040c1141280c0515900b001103501180503c000c0e03401d1401980d41d080c3e0b502e541013501d40e09c04c5042622000a81080d40c0140e40d40641c0c4a040052010004115910128 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 569145998 1250 569144748 569144773
    0x6060f0b131703070b09120d060905060109030c0b090402160303091406070f03020306151c0f05060f0d0f05100902010210230a110f041d01080c0d02041805 68
    0xa611501404002c2451000300c8146030045640c0c0c898408014400d60041c404910014400c002420403494086070301e94039200842041d200901da5031007450030320380c01c160225440394000e21840702680e030040703403c0075003a0800e8802c045039440300307918640040d800c2200c803020740707080c80613094201c3c400d5901003001e411500340180681404800075a2030340190b403c0c030094039044440c106d82c0b0b801a080140e145d5941900190b070034242c0d10380e55803c01e5800a4080c4141e010300c00340301c80f210034070b803010010106050010b0045902c21102260041044e40111102d0700e04508141c1d11544074840007031482c44240d80362410030514041046289884108210440d070701480030503000582c044040111846040820380c144c3c3e540003a04a020500c4804240400c0e00d980001e0100c0580780401a41c40d1080040520b00b58807a100b000707403860803060a01a060070541c07010703040316003a00041035070720101800c0040401e50314004a030b0107a510032140c005d0b1130109007170901d018002e4000d0200c2d020600c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 569147248 1250 569145998 569146027
    0x306040303090b060a060e040b0307030203030307030e07080106120308062d01121e05041406010b03010f0801090c18092103050919082b06061101090c1206060f0b 71
    0x9000c132882198000400e0040540c42070340380c2c031003820454020904501000100f0f040920941003e909030000004201009400d03030040351181443c4c9080b54816a0b850105608803019805031506410b803509605010034400d41d001e5410060003042001401d00c00f0240762404580e00800720003040740e0001d21000d540c0c00c01c04100ba012102c50003400184481a9803120002408000983c000ea4460120b01481010020a20080d000f03030211041944c6445696519400910580b00c0c038200f1128045400c003018090744503001d030700140f4000102d0030b203002c05014008004101121a5455140102042200300c86408040105450111600161b4001010b580c001012805103a020001100401c3c43d00115070564035040003001d43c440c000001c0c0203101d912080307a90002540b0b0b4840c00410301a2550003e03003203032071940b910400004c0f240d0b800da003078611940000d08071103401c503c20820f0900c040c1445404611410001502d25200c001000503000290402c213174054011808406000f4103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 569148498 1250 569147248 569147251
    0x9050301151a041d071b080403110f10200d081911030a0507050712030b0112052a040302060403050d030f090b06120120130f05090105120a020306040303090b 69
    0x425650503e810708120811866802140c1c1c641c0304044480000340c200d510542401d14645081007610312001c800d414650884d80086c0000d84000d20032800140203071912992440880c038015142d031240c9408000d05513a9010103400500414082610284002c1c2c0180802c086c0c0300c106494400750f508113920399641d10a018400c455a103031030180d000e540c6021440650350f0119100501180540c2e070044100d580c3e0182c1c40c80200709000ea06406007003190160002c08241380207903602c8481002d8030440c00c00740d41e003c4d6000130810107401c0e109481d140381c0c244d082440485a50019160279981d6001c188281d000d580240c4042d0485540300c0c2195034140200d01c0d4241c110301d0300784045503482e100d20070b00c40006402d00303200d10104095011041d07001e4121125070510603055403004660440041e00c5035000c1440340c81742018400c03001c108492029540c0040c0c940c0a440c203c010382c01e100c2888189061071040d6142c80c4078091084006a40c100549807140e88250f801180e0355209183c2611481c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 569149748 1250 569148498 569148539
    0x105100303140912102f19020a02060d0608150601090618030b040305030105270109091505090705040c0801123009050f01020f0a110f03010603111c030207050405070905030115 77
    0x1203201d1803904446c6142c0965030300c2c1003504608910883d58080c141c2c503009154000a40103c40031940182e8070b0916802081201c010310207640e40e05024400000312050210350f500e0214221890600c2110701c1810703c40350181c8900c00005003503840341c03541c4008040c01c403011800110004014032203810f20210401e80130030910405e090b6000591610b80c210312050090b94209991001c440040c4144841445d100c100944002c0019043c50401c41303071181e040c0c1c0500c5000b142418400960b9900c19a5400c0c121910071308401451101030b600c1c0d807100e001c1c00c0b115003456146401c02059500e540110035420403155111554101e28080a0112900c03043d01c03614195003001c0c0c10421004408200c0c0c1d241640d1040301e1084400720030700085c0c00d5059840646406601c1d000d40031040100500820101502c104c030541c2020000300e00d04c02d10243c03502d00c01030050300108410007050500da0481e98002d480c50502e02c104c2c40e114070110342100d80240104002006a280030019580c030213191401800b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 569150998 1250 569149748 569149811
    0x290a020f0409021b1507320a12050105120715050910080f010e0906130203010608031204020a050904030c0f0602093105010b1b01020c061305010510030314091210 71
    0x2070001000b920040340000414842111420b1035a8100046401c0e5007207031034240030441c2c2300e071000036004100c0c1441400200919103810f00115840c90a03140f0503090b010020b0081c0b00702400d0045010020740074124100500c1410f1000c1034440d81c4500406041503510303600d0b00c420b40303000110150070000607401000d0250f20901800903034079001c02d1041c0c0c0151860b034401c3c01d000c507501c04a801801a0381c03000c0c0e003a01002c1059029100000c00e000c0c01b80340220b9804154070f44a10401622241c2614002d011130300004044001509100c5600850740c0246401428401e42d90041040304c540f15203c501c800041c00e02e0100d070304440c4021841e02004403002048258182a45202c26105001480191006400110503084025011502da0030b070030106584450810f0490045480c0560b0f20032180c55080c88006280c00094600d0041147d4040d80c0d0b0070f40c40124048080342551103c0d0b5400e8201400c01e000c1040c0328010020a00c0f01080e035040000e0070354403495002700d44020102c0b00714050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 569152248 1250 569150998 569151001
    0xc070509161e050406030b2d01030614180705090a0603021b161a04030c141311090d02031908030601030b03060609040204230c0403290a020f0409021b15 67
    0x10b641c00400d480564010307090001c1e4a0711a01c0000305c180d4004d021840c3c00e14104181000780c120040b03c03481c00700900703032004c1c030106031904a290045050620955003208240e5442e64200c9415101d0fa0742180300d50074604d161903d01c4011802100070360300518042130300051168400f429074040102d00103483e0700074144d40380a040074004213034a141725208540c648a00c42c42040d204484c1190010b61b80810000304050b40c07412a980c07803000502c0554490701a00c014251248006c3c0540d48030980441c8030b480ca8690404100025000e14a0060340c0501c285070a074030010386a1040800030502600c20191a842e00b08001001d85000b02481307406504003c050000c81d4441d600c00c41e8000c1d5048901251501201a144900e00e03402c00880310455140b109200c01c00c0744280c020402d9a001c1e5202803c0c20780409500c440340e45c10788050220000600d00051410030450340034000e40300844003054a8580d83c0c4810405a801c11401c0e1441c121540c42403d0b9000010000200e40070414191a05507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 569153498 1250 569152248 569152307
    0x100b040e07082a0a031107060501050a08030f0d0c03110331230a050a03080901060f050d0f03020304090c05090a060305010509040f030c0807060f0b03010b03070303050c07050916 78
    0xb0288050f42c40c5407010301140c10701005009800804c4104d8900152a48035146401c203000030708802c1c030826000709240440860700c48004400c41340080c90480d41c403850100400070400080860200c42007c06031703102520080001154002d50084076030004c00c0c40c008011585804500c0141c01c0808010940c08071440c00107000da85c0c185074011444181c24420790190015030703003000094100280380d4040c10a50204058020080c0c0d80500f4000c0020800c264460640891440c0c050043c0342d0b200c507905c10f1000004401480c0501050301c64030540e07040581d5006044c1c00d5a0490010038080350000c640b10a160400320300302e4000700b800d8501400a545072001082d000d080142000d08060700c480c0300242410b000ea500c03426519809515160b440c0d83d2810010018051040e10000c02c03800c00103081a0303860140201c00d400c0400a02800b011403550b64241c030540c0c40080035041fa03015800c4006501d5458030880d6100d07011441d02c081c54215031220050541d40b521446c0740711004080c811844 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 569154748 1250 569153498 569153551
    0x10906060e040f02040f0807061d0f0904020a0b04140432130f0605070f080c1903060503030304050309030708010501060c120302160303060501110f060708100b040e0708 74
    0xa20641038034001001c3d40c007800b002c1c002e4425034024404101490400194004000454204954469503a101c000c180d00718400c0142c05500151a400b101304401c8800f145809603000340c1041c4010700d1120000c0e56600807090541050f48841d5001159000c207000c0303402e003800742900c8032aa025006c64040c81840c07440c4902081c2c44a854114014580040c41c0c2405500708061001e402c00104100f00c0154070f40000601405c9400d0000035424410705910305e07004410320742c000c07203880340068108000100c20301404081c01c00d00c401016150080005c80e604d040c0000c5000c0c60003540a142d80e0030070307042494507100540d4403070001e80c4c0c5440d004000301da031301141c1910780c82c0d4003000361103440c3c00078241100680921841c0d4110360054078a104105a015400102101c40070380300c284003888120040c9403119409090f040d0302703030490000074100a01c10080980c5c0031500c00085800c29842d0303508400140c1082e00050131003220142400f0159400031911944030002d640140d071149050b00e40d001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 569155998 1250 569154748 569154767
    0x5010615180603050c0f030109020403060e0102090f06030a02090d14010c02030c2a180a050c27030109080a0918020a02030a210f0b1c081213020a08011401090606 71
    0x40503510f4003c01c0800700b45c0c90032140035680c08400c1585950f1a140707c10025840383c4803c1f03c80768502a80c00c41e01150600941e0000d100c003c0082a99580a50a10034030f039200500c0b1240166080103110007660351181c5000081c1d01402d0803407110004041c8850855181136216001d5503c03d110980e00c54000195036008410b450000010000e0010581500d4400c807551203580300c40149543e00e000040c80000e540b080114680c00e00940e10b4440c0d00c1720180c815482e0002d000140300d2412515110281d03c000104180a1300015502c200d540740d8230342c141c1102c03c0850000e0f040071010072240301c03141c0148101400c00d407400c43ca0039141c128003035568800d003040c64080c820031042001010ba0a902c10703082c2c008407040107020310301100340007900a01203468181c0c4207039010f0040300c482c0944c2c83e02580070154000c46080c40c0960740c5281c2045880c00414503644031504907018401615000c4a01c0d000300b04070030000c240100200d191015050051300501111403500500300305a42e405031050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 569157248 1250 569155998 569156009
    0x30923040b19061110020a0e01020c1c08030916030f12143901020c060f0103021c06020d0c030f0c1403150d020a0b120c0306150c01020c0a0501061518 66
    0x1c20031058403132481d84c01d00800c40003200d805480860001000c94104440003500c034401d07400d55403400503141c1000781c8405001e518a1201c42044100c800046e900f000445d00116001c00300c174900c207007205941c50404110340007100c4141d02500d5000402510b084600d0400280703040c40c203000c103110100001c00c3c0c000c00d0f081e013900211802c107808074003030308131003045008202d103040e06402a448190702d8040d5019500ca5101c278030511000030405002000910b0503664003c00003090702c004602c1c1030840d1071551030196440fa5082054101c03d141c0c40c412580070310368030707100480c14503500c01202d01250000d00d0031405010031300c08446004001e00044a500c55a05100710740c0f4401d842c000306020880b00c1034000e4000c4141d90010407410a11409440c11614101f81c141c2150345c2d0200703010340c5001c2503032540e41107050641c0201c05046008043c0041c801c14400046c1440e402081040c50807039500401ea581e65510b03082401010b9001d0402c40380559035003880b0002e0361445904000c1c9440600c5036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 569158498 1250 569157248 569157257
    0x2011e020301142815021b031e070e130c05030f2a0303120a05070906050702040f090204020711090c0c06010e06190608090601061b020409030923040b1906 68
    0x318860641c00306941e6200001400411071107840328403411420106005007405031003121042060781f4140644202400c5000d0050829109541d410708944850160f04180e83c0c01454030200f0326030740500803240728103003500a551000c4905c0c03d0040304c0e2180c0790011806600b000300f0b821580240000c030400c150b45402d00321008260820b1204441c0ca800240444d41408002218623095103036600c40c5003c0d00c40120100059140c1c50420340b1000b4041c440c42c80460030134000d61001d803070594044a01c02d90304000201e842407450340098126406010f04940d00858441c0c0e08015040c0031818035800620f03850741a1038051000910342e80c401c8144101155a60702c6000074415482e030000a07403103894503039280b1038030a0b11440003034040c1404642101e068401c680000a486203e070a070244440440c90041994400e56020310000d0068036400b5014800d0111001550003004a04481d00c0c1d42401c40299880325801d04000c162988602d9403842951941c0050b4120b08546000200f10342582c03c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 569159748 1250 569158498 569158519
    0x110d020a06231b040f030516080a05070b21040303020c010e070f030809030f0613050f0c011709011b020307020301050c030c09100c0501020406030902090f04080f0f1902011e02030114 80
    0xf103802c00c0d4410741e049010b4400f41c1402c00010001d0001e0b103046100d2003261810809501d900b0650364508a002024083c4c3e40802810000117500381c000b403d01c030b00d003407240b901c0003400a01d0406903420141c9003180020b40c0000c407010300c0c00080c805c1d00740c1c0100c2d41c80a040c50381d2800070200008038141c00054030718540020010000d982c10031041440041500540f88030f450a4448800c1e91038840c00c0030b64107070241e2030524500720000310310313040000c205850307030304800020140a000b41c14004141149940d610a2039210005219613200c0b00c0c01000c4d4011940c07580c081c41418207550000d05030f80340840303040c401e0084c0903818506039800c450050300d030302400340c00c00c180c101c2c0e903000d4003c005401340d44005008600161725030084c230f00c21402038403003e541c3d465090780b6414192045802a040520601c0301180b1849e554006104038244100d07202c1c1402891202e1640d1103211440903000340c0e56907048072000c034544001c1d591020168002c110705561611646444051180312031511030b140340390 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 569160998 1250 569159748 569159791
    0x81501030f0c0c0210030603020303030a1a0d1202010b041a011404030b010906090605030604030903171201150e03030412020409152d022107110d020a0623 68
    0x24003a607144290208140300d46401e40a020b4000c1c402c946080c1d0107800c0401041156a00a0180204880e40a4002c600e556a1414214000c01c03440d00400225458081905550380d100c03040b2403d218050040c0340d14010360004080d00b112540d10440d40103d0034400d402d08075101800304d4091050003070070264209400560002d0b8248202e030802841901c0c000004a20143d01d42e1044068844c42d40c1c040042c0d540759000c0642d501012540100000c0051b0400c2c030000748105030303070b860000c2d08240c55414400c0c40d410154424030700360441668608020b01141070703240c1c0602510b1074028140c000d580340c00c0c00c01c803401000383c840000180c01551640d00080410240798072015100f0110b81040141c0392021002c440c1c034510381031941e41070f1005c00c0c00c0709028803161b00c200c0c0d030003503440200c8152a480a45005204a10040600303084c85401c28208540500a01c0282c000c440a5809495403608500d0031508603183c10591040080d0320029020300c94400f1009070760840040c0c942180c5407402c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 569162248 1250 569160998 569161001
    0x1021b102a090e15040f02030c0313060b0d0602070c050a050d060e030d2a0806060405010305091002030106080912030c041404091b1a1204021905031e060f010608150103 74
    0x3c0c0e200c4400c00b007038401000304400e00794040508140040745c0c18002c3c0418100503a040c1d0200383c901c0c0d81d60200800100e00c1d62105442012052489000040b40f041351400c000364894901d0303103040e18555000581841000300708000c2d07001034401180d0b900001c07820040401c200ca40102c00051900360350b240244898081042940d841c52504d810a00c80f0245600070030040d280c0301101c410300509007900b401c140034010240385e44100700c007070525400c0900e000c00440c0500000340c884a00d40c021005036041c802d12a00096010701003036240c0114a0800c604072a00e0100c03541c840e006414001d0040c03100140305c1d00115411519940040030380d440304440040e0052140c600001c00f9600c40d201c3c2c00d0640303c0c04a41c04c6c1e04460100e51482c09510513444141940c0c403800552403010340f40840010010300c0d040c1010003029030500c1c1c2d045480c40e02c810220b0301e40040d5803040c050a44010043d94019581007102ca42c0c0300c5d000c0b0f144606e40d540352010103095180c01401c4251556060083e6001d41d9209 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 569163498 1250 569162248 569162267
    0xf1209060a031404080d050a05220f0f0f05120306060405010c0203030d06090c090603090809012006010b19021b010f032003040606050306041101030f0e01021b102a 72
    0x70b01410f4055081078a403e102940c003c9064102c40c3d400c040001c0d0901400b840b406200d8144c030310f00d00b0031180c14418000e0080002e19411100c09181100b120086044103000c03020141c810720048500d00103a0415034980055801c0c814404c0000f0802c1140c0d544406098408a52080c2005100301c0d4943c80001d0070b50041c4c403c0c482d501ca1408000203090300198201d0000702985071a048142519841c1c1101520322041d005402005c0c104030404079948074190507540126260556800e02e000303410362508098003030740000030b80a00454038401c0030004140141800900c2d00081007109280310110460751103030021141404011400c45020794003076044000c10814050309403410504010788422581c000791010340305c02c1d00d8100089803078180040c055010b41c0c1c0103500c09209030990401100908240c1e042a2141c1c0d0321941d15a0000409001504500d040748203641804d00540503034514203070601414444090034511140ca010040368500710144c101034591500e0300c0b85240054030000780c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 569164748 1250 569163498 569163521
    0x1e04170f0d0e060a0c240c020f062410090501020c0a081504080903160e0105090702060c0919120212030313081b0d050309010507050405011b0c0306021303050f1209060a03 75
    0x104011085440302e1441c00d00f281b400350402c01c001c3c26504c844200e958045102d807000c080e9110801044030002203040d0882da2080020307540344080300c540c001c600d000c401000040082014510f05000355a0180302c4d01502000589614004c0e038500364610340e0360300c204484086901c3c0c100c0c0204040c02160300031200b015001a08450204030242d10001056440380701d1651030b0030040c0d001103403a00e00814402d00640141e4028410f646424003c2c1e00c66500a005869100380204904414040c244141c2c2c80200303c41c180002c1541001e00500c001c1d26451410900340781c100308104400c4006203c00e0b10036407500a0101611800f00d82d450450400140300703500c8291040090301e5222a0740000254881c6480c84000d01c40d54580100c140c41d180207a0044a020031008244400603840c80644000002e0042681003100340d9203403294001c1b43d1149103901a410002c4a0a2007800005c100ca1298041542c0c02421480310403803240600c0d01402d0603542c420040001e00c100c65510a8104843c86103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 569165998 1250 569164748 569164763
    0x2190c0501150f03060e03130302090705090901090507030b01020109150f02040537050a0302010807050706063215030402030a050102030c030f06041e021e04170f0d0e060a0c 76
    0x40c1c403080b00e8203c075019440100c0f55603040030701e584c025980100c19201c2c810800316010322500c1c1554200a10040010140010030100740a000150750318803200f68001c0205580c001020b0811310801000e0314070b2080a10706680c10300c0f000a0005007032141c08400c01503801c40003c0c60000d01c22080c0040d1165600041d400030800e00503801c44000441c0c0030410500102041400c020800262805407610f0702c0340310341c8100c1134072003000554040c0241c01c1c0d20600c03a2611618260707060350f07207404468003900144c0d540e00c1481c1ea1040c03900315160000e260705121440b03910200d4100d10016003403104128a084401030040045011520204000060264040029500d03440c1c440908200f40c3c20483e000c0c1d80b140c0e2540041540c80c103192154540b4028038401d0605c10401c1c00350b80c200a588841c40610395034035000d08031001402d12901070005040a031858807803582061050510313154014403588180d4101d2447d000141d03800070f1064454080544445481d4803072500251605150f06801a00c0701 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 569167248 1250 569165998 569166041
    0x10902030f01050906010608041502070609060e01060303260114040902030d08151210092a050306090c0a17010f05011716081f0b0d08040906080102190c0501 69
    0x2607064100d140304001c030008903402d81c0e903070729000c48110606813405042951005040701b00510380b6001816464007840d03001c40c030001c0553380c0c001101d030480c2c00d03084244d5449005008142d40001c0502d50452260040e1148081249180c2d80c5580184500c03200b000000560282c5030b1520342040009680040c150b0700300440407840981015401c0303400308204510055068014079040d020940740090f0b040040450502201c0288010310001d101940e001495800500004030740c02a1221101c5120440c04c000e58601001c1c0352800ea1302600040154004548180b050b480d6110024101c0f0300e4280c25000c01d060440d8842e0052282005a0816504110011031034036074001c810001c1c00170750001ca40c01d070b4141c4000218500c405002e118241e804c81e084030918810842d1201c1c4840e0511a00003070b141507000c000031030030342d4100760480b50901c0c013143c20003600700381c0d115501c010440d2000940c60008100c00482403134a1220304002844400d898000a0200940c0200d03200020141b202c9000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 569168498 1250 569167248 569167273
    0xf0402031014131b02280f020d08030c1b030702010e1005040f15020f060c0904090813141003060302032d0a0c05102a0f06110304120c030c110301090203 67
    0x14004c02c28007800035102d0301c0d0301c0d040b800c0716041b0241c2c501d642e11034940d01501d215503144800203491601c144e0b4000c8104a200c000b0030850740046008040454405030341c0d40401c0c05009050108141481480d0028416940580d821154040d0385100c01c966501091280a005492a0050350003e0755080c1c01c8000100c0c0c0e012528070049500c0c1031a40071500301c0c03100f440686075515400c03944103075081818885460a41843c0c0c0200507000c0c41054040d04111004a8104501080d940207100020404423503e1345400d240c0001002c000070b9103024807805045801003a81c074440c03144c696080d16450b1b29510060700128280c0210400a5016160900b1190803c00315040007405a184142402c0050085450045140d00140400e101078094000000035843e180290003d106a844205c1d080b40040015124032400c481d2031460510b5a0316800c146c105040303c83d0f44800c485080c040d10043c2d10000c65080790040c1c007a81c2d4440d11100c00086160082400f4095428001303416120b880c180442 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 569169748 1250 569168498 569168531
    0x3020a0308060603100512010603140d0306080708070302010c0f050a0f0203010f1a131b05030f01060c02030c0907090b07030503150301090807120c17090f040203101413 74
    0x880034000c1da60080c6a88409041088a100c107a4003038102e81091041000503003001e04120b102c80c03070000000241d190b40d07030312511a88031820341415850b030002608002c0c100d816100ba0b502a200c030b803004004003404c0001f050b5a0b15461700001e0b0510400b0881442040940401c8504943e409010f903044616641f41800741c0c4848414120712070f50822240d06c1001d081c0d0300c0341005145410340e04007040210042070080015468802d1403440f40c4441240d21861062190591445010341e910780d520301d417501c41700510507010703042402008000301d42e030005668006403205406004580d496110348801400341e40004243d402405c084070082243d805040d0800f003d035125541c04001900b5101120381050b08850304098010651304d8248148004100c1c00d503400c41111127181005441041e054840c80740e48001c00011801c412000100007503c0c1c1004059601c000005403415070541c1811403003951645981d01540420302141048c3e409255a11521003140d14407400003000b54a03107458600c82e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 569170998 1250 569169748 569169763
    0x30c0c05150a080c0a020c0904020301020c0303090303070e040b0a0608100e0106050702030f0105090312092b11010b09060409081908041e1a181005090c1906050c0a0f0302 75
    0x201003950000080c04031000002115045e030442d80c050301d1100c1c8058108000c51001130301c1030340c056600b42705c0c034052100208003e601400982d4025034032480c103858001c0c0080c25110110707008505188000302d19458688018050758100c4c18454000c1e0348916104082041c01c0e032180e004005074a000150380c1d030b00a0000d003062070098040d1111400c211001c28269a81130720b10081c2d42d44100800b01442103018030385500400c490701603540c09100700c0b10000c181c1680c042000100358000318182072451b007001c50b1040e03000c1d01000911800078580005800804001d2540380030720380380c24031042000059000c403041e41c4003403000c0c44184c945007600200204412507045411a801040c4020116174400140c12000e81c003154500c030841e0b01903038009400c90042d20a0607954441c000c50ba00c0d840040c450014040326403040001d09180c40c40c1c9281c54810352255240c054680c00c00c2d00740203003140040440c280d50f490305140e42d0b60856071100e2460051542005860040e032003a10504041e400b18401c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 569172248 1250 569170998 569171017
    0x60c05091e030a060903120501060e101d01050d06050411130b0c12181315050d0c09020c0a0f0b0703200901080402150408030417031204030c0c0515 65
    0x10031940c6280d040e00a080601c4001c0e05a040d8004606400061200d800c081c11003482480d04105c85420b02004906880082c0c02c0000403400c03400104409060807041110003c5007440c001500c6807a89141080c3c0d100280581c03070400c0000100050f016207103030041303801460054010841030761450042710544d000003141d411544100c60b00020080740c41c506036010b1400d100060484404540c220301110307440303078040302000309200090803c00c0d542c0050713004c2e40d84440d11000c585940c40c1160002c0004140d0011361164071083c1079000071a032031046060981d03900000041c1c0c1c444c5440a100e24105440030000e00ca01503070011102040074803070b43c681c040c181d1500c0500621101da21402c400c941c031000800c02229052144035019882a24020340050001c0c0c0007034508005603595a94660103034110032029400080c0400c040030050b001030041071816001780d400c000038248a2608540040c0c0007130100210a1111420b014000034000000c0600a21201441404c20310703010184e003201908 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 569173498 1250 569172248 569172259
    0x120f0908030d091110170405150108060a0e0619020d0e011b02010609020a080a2a262a0d15061824050c0105010e090601080a12030b01020a060c0509 65
    0x240395043c4131800000043c540d4031b88400704e180206140b00e030100f0080c01a03955120740c0780c542c007481456500241c040e110f003c016040c5490030310b140380155502e6440000080c2e001e40d00b008144080401c050001240003032002d6616440d200f43e400161052002641443d40f174010b0803a02c103d0703840401082540e142d002808195554242c040c224001d1001c804040748400c00000c8054005034441c0840012150009079696490301560000000882c600d40109500314030f04600c0750750f643c960380f02611124015200c1c0e850203d01c0101c05d803080c00d040c2c24600f800030b020840240e040c10140d90b00b0403402c0100700000c00503030420301e040c0b401c10320854010030040d01c1b1051002c0c0540c03c4420560f0446890805d034202c1e200d0b041c0710141c5007a941842004024405421194828003a80e07000388803003040c0c0001820700e081c0c40d030704041041e40020304903400745400100107500030040c85034038a02820000b460b481d000740140c2c00c151640760010040707460314455002290f0084090011030700140e48 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 569174748 1250 569173498 569173523
    0x60f06080c121501050112093504051e210a060c021c050a050f27012a080906070302010e0f1f0b0a032001031503120f0908030d09 57
    0x10103c0d01c50002162802896010348011320141d401600c81115050340f0000005031201075456800c28903081d00700c00c03102105403425482c4011010701000c6401b14402149034501403520001403045151103c40c02510f01d615045518242c0c1c070351040011814000e05070014403408602425101c12401c082160640d2401d0683c0408074400100381034440b400415220003951344180954668020003145000c2082c104071141520003800c0150a102c591016030103008030740d60322151180c20340700580c81c3c100084c0103490840501c403240d040944212180480ca8680410f051400080c030038800b600740c200308002144410164154043e140c0300242d00e0135958441904540c843c0c03a40030442103004901c480d4030b004030516406038441d0304100401424001078a03500d6482c3c1e01112000301440c480760181c10302c2c1040c0b0707580601400b00c804614030302000e000c03420755841140d00e200d4020407004011841c402860300034020880400030308078032412a600d403c2d034034016901408030100100c0c1c841c5090b12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 569175998 1250 569174748 569174779
    0x212150711150606120a0b0402040f08240a0f090b09030c06010b0c0d050c1618060603020306060315010e2119030522030209040f06051003110d060f06080c 68
    0x10000380c003484004051030302e416400d12a1031711503071003c0c01001c500740c0c0d140712041c45503550388000c00c02031a00c020702610a41c41d144050707060100702075030b115042c0900e404c101c0103950020380603a405400070400080c50141050700b01d00420741e00c007008080d404003c040c0b240d80b41740080980f41c420200c0b004c0b41c0d5103070388a442c581d810b80140a582c080b80c0e80490040c481f11800380703014100c200540000c03070b170141e07044003591003140341342e13502810030300f06180071401e5420706030700845000c0c0c680341c00e0540c039505241010903140c2c84024690300d03003a00c400202c07900c1d603071140e190403040000041c9084425004448004054580402d03544554070070300c0e014125540c000c103600c51800b9099240e290800c806801a0b0005440e0700103c48401c0c0e071180c601000590314942c046014a02400740c82d28180407900d410000c491000d0600b1441c2c0003104420400a0007804058118003c10780e40b24902a1a03840c00d0000f510115071050001c41c1842c0010076442c10008031102d2070701040382c5881a104501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 569177248 1250 569175998 569176033
    0x30b040906020306120f0309010f020c06190906090303020c040b0d1b181107060c21020a0e0d0f2a0b070605060904030207030f0c32100206040212150711 67
    0x20501c0c0d031b00350001d20079060700350b001e500d8a04aa890343d0060720300c103c81d1078000034040e5000000ea50202030171411b40010440d840346100024080c182002880d580c19910080c9d51400180750300c620598032a4031031203068580d420300c0c1e450300d54444109190245044104103854502d4001c2c2d01d8010041c0c041a400d107415801040c102586800c0c82d58601000f6442e0900a010400c1d01c000a108404201d0380c1c0440c400d9292013000002d8850058452915000040541c1780145507244030b00401d200b06130200d4030b0303403103085a607560090b820501a6401045104d02000b65003d0032031940c8401c1c000202ca0390100300410980e4403a101c20403999881e0b01c1080009641940c0290041e40100418800102242051440e00d406145401c01c0ca41e03607a10351022240030301030860f02d685001c101c904200384c0c096001840504044481246150095100075600c50f0020006885055011504c0b51611800d02c0740003019900b841503484d0510700502c0c0601000b441c130030500f105114828803503050f110311 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 569178498 1250 569177248 569177263
    0x60e0a12020d0509090a1d03030a020702040c0816120609060801050f0609012102010e1c0209090601150302030a0608030304120e030105010506070f020301510510030b04090602030612 80
    0x81030103146403140c410038001040302014010301e031147e01c070100020140810142d0701c00c002414003da511016803040c0030643e0800c0c285403003842412420b0140300c481c3c9800411000d000762034402211906544120041d021990008621520300b14012a4201d01034028904c81c00491300108003a850701c03000e04c601e0742000d1280214400d00c20344004509403c1050345d03807819005141403810f081000001804000d1600200007107007400d010b5600c02c505044e03170350035484903d00703010303090962505001f8806c0e9003000d15040101a40000000c0840b1002e0b0701c0600a045e90604032038a87c82c2c103240c001d11901301f1030a043c0200761003034528096883c05018481c140c3d02d028000c141003031466510030004a101400881c3d048d501e5203210703001c08140301d03400d0003828802200c40101000c0d4114082c100c1d6401c640840030b4004107803844910780e075080ca181017201e2081d101142d04c1429a90218000d00c2c0140026500505200095051003a00d4000c0d500441d012120004c502c50300d640a1940d0703095 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 569179748 1250 569178498 569178517
    0x10c171c180c03080309071a040e071e0c050708060108011515090509270d1103090901120f0b0109020d0e03030907030b06060702091f0f08030f0304060e0a12020d05 72
    0x14003010503c00a143e0070090754009511408903030007184c032541131581d40c28894000752095007000c24100400e8a00110301900300e129800d1060052141c0c001c00d144850700ca1010005201d480005001003000c104440c000034106601543d6242d43c6030321005010708866483d0250281c0d500601151500b030902e4948035042c801d48414056a1401040c0035400c1d00051100c4409922060703100c204e07819000d0016036040485001c0e01d104030350f4002c040c0c00c001088034071000d642d00601440c0d199072030b03280400d4199810038841c2d40c44241d9a290041c4103a419403001030140341c008000140c4070101c1d401810840030320755010300404201003141c1e0303500e0004a5034141103134888181080400d42002d5465004032020302040d01d4030540d90085000300c201a5000f400c0031500c00c06c00a0000c914554240107030030300f2480c0500c4c0c9480d08003540c0d0b80f409000106854644000082420440540c0c0030340340548118080d075901d070f8404d0a000e0a6482e010f0f0050015025681281e00454416411030307140d03c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 569180998 1250 569179748 569179763
    0x10050a0605030c1e071208070f050c070e061203040801050906010605120a0b01110111030612010209090403050906040f030b06040516050403060207260304050f0c0906010c171c18 78
    0x1016600a1310841080c0500c4184184204089404152421408108034119850304042810108002002d816201400c0400c014051010a00c3c0350303070208554003140c1d044072a4000f05d84a610000c1d440144020800c180c0303200000d8001100d00040d00301500c5a00044152601c580e40c601c0162014072a90103181e02078040345001840c400c0d00da500c000000b88041c501040c84581f541d5410742101d440000000c034514010013049200e18240c013541c0c80c1158504000d60030181890003113104694003420080074801c0105940040c0d488081c2900c00500440241e003207107030b507a401d004023100c0007582c52501035030404000071641540981d150041c0c20313040d40ca00780744c203282d41c0380c22009400404045030900302100325000264010b10741807030b83e01100b03010b540c3d07a42010b25100d86444503e01411340150040782032894180e5034a5a021340c80039083c20601d10401d25840c00d08500581b50624000350000840c00844044104501c6c1e0140c09120404110401d40c00c01240c940105540c0001c1988 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 569182248 1250 569180998 569181007
    0x90b010e0f0118050402030910181a070302071b05090718060e0a09020c2410030b040602070501091b060801030804060c140f0307030e06120a0213030b10050a0605030c 73
    0x6522030a2081e40f02c5401070500c10100f03499000050aa80c07090360040c1700c0c0d600810003075200c3c10451113000300380f40c5822000c1034a0300103031740c4017881c02c103c5410070030100c4084d4000403010b5010703804461100b540304010f00c45403402113130900201c1016000d9540100d01220016104500498107089a0f160b1500c000880f9440c2800881c1c00304460404140c0103010b0380400078614002e800a00a07821195010708000e03400490f0364982d400c460000e242141c000041130003180d1941500d11801d43e070300701c1c40311025551b8505108000c1d208400c8014165840c00000380240300609541316140a03021464441182c2d0b607050498030303101c0c20300000d4444c4200b004100286400383d0220303c00c8030310500030041c078845881901e604185240d202003125070000a080302c201540b211003161740c2d807412100c4608002c8203038030005140c0002801d2800141c0d000481c08051290924500015070f4040d4003204541341a110400000d41180304071402452601c1d404614240540c066903c2213040306035180c01c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 569183498 1250 569182248 569182279
    0x3120938120a0f180b1503030f03011406041e050909011e0f1b0908011d030304061a0a03061b0c0201050720100206070e040b0d0633090b010e 62
    0x5103102c0b5241c0b030384550740300c0c041311900030804007140d54107000e040710225514160608041e40c00c24a0742c0c182c4650002c00075040d40c00f4508059030f05540c848102100d4905161012500d1403150307400c49103035014000e1410300c0c042c00301d4003035209550081c0c40ba65a651030b00072229080c1e85845104240c001c01c0c40170302d0b5445408903889188005a03100c4007081c40d4040200c0c24881540008840f800038580c507100380404c03c030034020a06400c00300881022400c90502c940d40c0c503800080d03c001c04080c0c4640016030108650442c011149000400e1039411590b40d2400300000c00d84448140011203004800214180c0125407184840350103844031480c140c1030f03540d410b00c80c100e90365400d040040c2405451917161107141903003482001c0380e001415981000e59002d49130284000c6000d00c00d50404503607000c151150884010710703550000000c168000d08544510b8080311030018070400302608080d920b80d0500307039802c2c41c040b5500040200140000a0011164020030142240d001501248540003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 569184748 1250 569183498 569183501
    0x1b120c090b03060409120f021b01080106050304170d0b030708060919050304150c03110d0f1d040c03150801020f0f030705070f030305100e010f03120938120a 69
    0x140180000e1000071585d616903101c90321460042d80c1e240001d1146800c2c0642c0302c2d0100503074152070f200301803240c601a040c1000201400014028801082004070100301000700082e104584480c021a92a450b24226000c40000b0f01d8079a00b064800e2155810018046801040c400d01401441000c1e21b41e4207400c4540901c44814003000f254940b00420002400324894801003542001d5940c44001403c0a1300340103050a640d017140e0380c2d098100815403c007054114034210400026402c14000d02e2402604001044a00d0302c030464100d0700348080c00103402e906501c80e410030328007035154403240d0b519002590300f00c0c00b03205444400750404019418143c1030201c044e5521001b1440c050b4504a01c1b691111168508050b0443c040f907203600610480680d00c8403a0000707008080d02c00702c190361402441c5201c06800d880b01a0131410302c1c09024003442d2260340301d00301a190500c020789000664100c1414810350714071001d81302d40f21082400e1441c5411b14106ca1903140482c2071181035072900740a400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 569185998 1250 569184748 569184751
    0x2160803030c03071704200f0f0909070806091c021216020d1a010e0c07170705010e06090d02011109060a300510090e030304060c0c061b120c090b03 65
    0x205005503d801e060350121109917903807245110381c41c55828400c9019840b00d640509502e240c2c49100e00c480c450782c4a44902c0d06814510300210b454814585421508070304180c00f907004045540036150402605c5240000d1008000106241c10002d10b42c10041c200d03140e4280a02e1032003800003c200003403d0404144240c0c00050004000d101c808840e0f0790f07150202c81000c0e666170641580c14004020300c52a000e001a0301000305407441c1e01c3c042c15a40c600b0700003004402880c1102d43c1c040707801410711000350700c0a401c0c01180c0c1c0450f00d1908001c142d00d82c0e03548800d60904010360034907040015102020003502c1c4000c8001d0040c0d401d291403050300351200da104071041c10074141101c05607090b0f5804040c01c034001e00608040028681003c2040b09500c42d1160803c43c10030b800c00515003c04100002101e500581040c0300041a295032f000803145014007007805008103040020a14850501000079202009952030b030140404000000801351661071040001141d040c000c20081d0892040c002c6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 569187248 1250 569185998 569186011
    0x7110409120f1e081e01060203071704030807030507050609011505040e0f010c0917010c08060d17070b091e060711011b0809160509070c020415031202160803030c03 72
    0xc0c00c11189010a220f544400380e12001c001401d01810f005000c0c441101e51a00c041c0081000c01840d0304010020b99030f441b4028006001d1f80d207200076541d5441c0d20f802a13401640d403290a49581e4401824001c055810104041c0c070075020707010100b00c3d4035505105c2d64134200c403000c0119840c10319002c2080000c0c0503013500d080c400d000321312490051002c01c3c440c0c43c12044441c1c90304e022041c14640c01d400001c6000800c01e880740c0c0f4146894603a1500300c001075902c1a41120410490306041c60710000d003095200416581c1400412000300b00005558901c0c454100c14044075281d40440c4032004640801d48145c0c0a944c0040c00490a00c901c41e8028901085241002252a40c107140140e02841e11604200c00060146024000a45e1081c410090108080240c0482c090306110008094070707000b8201506009400e100308045480320303004106600740310b200c1d4101c00740e90380c00c0a105507101020b076080103001702d0706200c10b228030804c10001035905100045040d83c3e22006c1c1d0201560010f401d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 569188498 1250 569187248 569187257
    0x1031203021b0d09170303010e01032303040e04140c090a0e070503121801110c100e04090f0203070b07150e0c0a0b0a080a0b01120b011b0807110409120f 67
    0x600d442d800c10400c0000854030355855212080c603144c1d1a10641e51880c0209101d42c100300010030124901704141c60660390040701c1103501845d130404040c1c02d940702c42e0303111030f150101080000e0903000d002c550501ca039014003000c0904142104000391610340154002c0d6000d46041e000c280c428005501640c801103100c0c007254811074039007000034a0030100c2240341034a000c1c009401040a03003c0700291103e07400a013843c0c0c00603640600c8098480c0500450075024001c035800c00c10185105000e034100c05000500104043c00480c01c05e00007000c8201d1090380a889040c200149003c845d1088440240d0807200100318000480c550030302421140310800303414480d003030300070420f6980c28458078010000c10504075070303038000c40c840130f094418002c1c86c20440501d008100241d03030b41c004410700810520001c000510525604c0140e5502c0c401c01d01d541c42581c4480002030400c08814002c0c0f071800d000b0241d40c1010105981004241d440d4410020b00300d081141b4000d020b03038010b41000e6008001c40c20b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 569189748 1250 569188498 569188537
    0x5100305070c11041d1c030e072c0c13050907171e0712150b030f06010c15090b010e060f011101020f0324030a1e0f02060c031b060103120302 62
    0x4885450a40540d4174049039007002e138140410700e262001c512255070060074180090021011107a03101c410900c100b1042003903d80d13649951a10b400c0c8405002d401d4101c0001007802e0040300d04816800c08011b6581e00901880c000c076580c58140d88442c803170300899440110740d0340d02001c9481c00c4031000c4c0480a40f050243c03241402140c508128603c02c002030b40e103c09141c4a0381c2204d0041d200101c8082c0416510b11406000d8003100700d04403907000155800031000364580a0040310410f5160f64050000701420280c110005e40c0c07600700144013401b880c0c0c0c0500c00d90701d4980788001458250740d02640104070501385540b65014001c4540b843d20414001401e0610002182170103500c00c0300c0d000d030001c95109444101c0c454040410120080c03e4004040d070380c3e200d0f41d444103070103146001d01022010183c22074041189000c107039000a5805409261280c28407942503540c0d401400c01c101c01e44822280401c0d82c000f00185041c1241d0300410080b2900d41c008d2020f4000b0f5000d40204442d007441d030b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 569190998 1250 569189748 569189771
    0xe0a080304030f02130501120605040f0209010303030519180b042306191b080c070602180109080f0a02060901350a091a18150105100305070c1104 64
    0x1000c1c0c030007540108070b4421202030900c10030940b40d11221001000d940313414014130000d50020001080107a0081c0c000501c0d0310707641820b04a458070920025448460300c0d0000c010164950400340c05100500240d03000c040140c2820f200ba603c00c003681c3c0000345804651300011440c81201c098202c1c0c062000161083d1803011594140e031441d00810010794801414804210780c800c542500d0404210300800c26201d148200d200e801004009041c100000c590101f0490801d810445002c00c0d4070100845d941c18a10000c2104a0640d000003408607c020348002180500400e01a02c505414009020f1a0010b5801c2100e02d400458540b410448180b07545270b944040585103010080d203601c402c44549140c0908040d658200074200c0d14800d08200503580010b03200700300c01c2c08204c03800031046a946e5800765400b250b01000c024004040c8240c00300e408499809065040c140e4505072011040309111040035010746406035044000950101c03052004101c80300d820003c0c1450051002c503a902891 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 569192248 1250 569190998 569191003
    0x8060307031a0c160c060e0d200f19050405061005070303050a06030212010b0411190809121911030711040507020f0106180e06011d041103070303050403050f060c04060e0a08 76
    0x40048480f000d00170300901605070000d1001c080e9400840d400c8420700000e075110183c400b5501100104000d442001c1800c554076510a56400b0708050300c40c00d80d001d080002c0c030403805650310074540034500c7d200c0490346909000300040f010480548401c0c0c540342c0d0b10343e000c60040400034a540d2050307685107400710040e61a44207441001c0c0d81c8100100c1e40009100802c0b045807084407981001403001c016100c110007050b00e0000c107580050520b6890b41d507400d071a035800c0281d01803a280f2000400a5002d5603882c0d43c038508280d00316070350740386d0f10080503ca01065580c86035039800303418100000c940a1003460150001c42e48034259106075404202c100400ca82596519000074904040c14898140b18030002c2c42001c0c46030701080700400e140d501d0040c52203003240343c1030420301240d00c0300800101403100c1c01103003d51400001d4125114a42c2c3da041c001c246401c1400102c0c0c0e24010b2581030040d03500d00140460203140306061040c1f038940341010907242c98228000300c5800210b1140000b8109034103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 569193498 1250 569192248 569192287
    0xc03080a06120b16020604031d0312030f10090506010e1e0409060204060e01050f09010c1407120b0601020a02010e060310080f01150609080a02060d0b040c0f08060307031a0c 76
    0x40c3c035458045050480801ca22020720341d03026002c65004800304400310354810319916860215505003480110b64101081c141500255070200024000040c840341c282d04800b800d1103401d80c00100c0d280d0300d0b210510744043e2142662400e00240c20b20b0340e00c0d032039890400650340c1421510460b4480d014141f902140c1a1204d03490180c4541e54089030410000360001d140101c106003d281c40e6181c01030805003200240102c82c00c03141080740010b8048201700c0c00c030035040c03805002c18040303a006070380d18080c2407104003045004032114020720002c1282c9500019254182540c16113800e04081d5a00e0107001483e0401403d19a02c22140d03100084d088800340901e0350703c58225800459010340c24200040002420b603c002c0401002030b4003004074800c0802c150045903030490740103958140c440200d20142c0b846256003940107181500001c541908030007115440d59603525040032030741d1104201900c44c080746c88003030000f6400c03801d0702d9a4a910009a56441092078aa1030300302460550070303241e00b056 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 569194748 1250 569193498 569193503
    0x3020d1802090105030d120e01060b040305010b01030f061d0c190207031a07080711030405060d0212010b16110d06050702031b01060f0302060d0b04230c0a0c03080a0612 74
    0xd8004500075410050106805050141c008100340c03980307080010525070f50360343c0c00e480103959413803040d04402080d00544010100131600a0b1a503440b400c240b4000d20401c900640400d160110501d245000c80c09007108480a120540c44400c009058010026200520524011504000500702c0d03041000498520014503402068050304614060350480601d0b082100360b280c20400b0081d103540e212a820754803a44502e080e0304a85001e00c071061441c003980c3c0042d903000e480450040c1740d2051a5020b0034484144140030b00050b40d0301c0302d40416a10a4003030b159007101c04501c247d40031907043d03a81d40b6a441d070702500080300041203803516001c8903415280800143c00c00070303100200c102c0580008241c851102e00070005a40784c0010012a100c2c14400240111800b0481e9a6501c0082c0d0003511041e10192040c04407581c4000e11800c0d5048004903107e4010003100862004621f09042d24203000d13075030719200d822070301945041d41c020100030304c04180c054569502003200c084400f85020341c5031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 569195998 1250 569194748 569194781
    0x3020f040e100213030326060d0804090908030a050709030804051e0a03061b0e011e050c071e06020c060405040e2802010f03051302060309030f030103051b090717060103020d 76
    0x1c0c103511b002021541070344e10108140600500100201d001481021b070000811602100480c206280984203030042d40d0003592100e24120008040c08110b500451080c0883e4500700100d0390b4040095130346902e0390101422052060000b4401828241e20344025040034401c2200894001800100103000e0364100300c032619140c52044400c01c0b11160b290007601403608000d210410141c0c002081e07640000d80c00b02500006440500480b4003400c01c803854915100241c801c0350340c51f00b00240d0000400c6a116030000c141c80c0300010303602e00c0441c2c5d00240c0200140043d207420320b00030400000d00504100107000f0300030250a0361100c41e092441c40411b11f0400f200184500030383c00050185400c100c240000c1c50f0a10301040b2011706031108810704140c2c1101c426869803201e800c100e10394020650711311010040040048180000010394092485070b001140103140d1003042800f01d64281541c3c41c0c0045204007010015101102400c00d920031010301d00141011a01010802941e00030192001c0380e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 569197248 1250 569195998 569196037
    0x30b060a030221010c110303191103100602060a02250606150f030f0603020303030a0f0f1109031e0d051e16060606020c06070f050c06070c1d0103020f040e1002 70
    0x40d2017801540600e01340c600b00490040c41c4801540d0f00c85c400140180010050711b01003a00107480d5a1092902c03046210304c2c0354583c0b9150700030100c0300c8102d0003480050712460000030300c024101c1c002c0740d42261852040e07c0c40d10307010520401d00c20780001000c6810a44458010450701030742d41c2e501c50080d4442d40c95810810400b1009012214150940c0e4080c5040180520141e2000422079800002107000060701d603035495009030040c04c40003104251681043c01090080307a074000548880f80d0f003241900c511003081c0c50b00c03200c0452807921544854001000042d0800e010344080c1142d4803402c900e071004400704040b0754151341c5c00103400c41103c2c4035105840c8180a02d078030524002c0c1c00e8900080c661020194002141030160440041405032120190001c01200f40701000c2c07045400352489803107600501e0b100741d4060440c05000e00c4c0c103c24035204480c0c44000b007000d40c100e80c0c020703092606203501d0030b09002c003070032036507449240c540300d014044401c22103248002c00c5021720008001076172 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 569198498 1250 569197248 569197309
    0xe03090f150c033f04020603040f0215040602060a0501030f02060307020115060804140609030315030a05010501060c1b0f060311090a08070501030b0a1a03090a0b0a090308090a0507030b060a0302 85
    0x2a80145002c056480c0c550020b604c54603000380e0050740258040720400c3d1255601c0c1780a5104101540009400c0308420007541158030902002e00203988294080d51610758520402d5411940b0921015280d90a10180d55003d0304142e0020f40c0c0040d002d02c00880c1e25811110b4070486d1600e0b42d400200065010780400040c0803100060082e50780c4c841002d80b230b1300d09050322a0390f62400702502e0106050401c0200c000c0d1554108505004035520000074401c3e50303582c440c05002c00e020f4400a07100d2501044601c0e10389034404404405803030b08400110951414000110001c01890b0054032102d9820400109140d4030b54240400a1401c00010407010341044001010b640c103d02406000d900780386c205100084071842240020502038034010303165030314100c22070314248003810b02078140c0c8503500522841071402e030480d51140d0b0090f00d420443e6241c000251342d0350100c100d000307462900151402d00018540703549450304028000c0444503565100c0c1c0014800c484200001d014518405080d60310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 569199748 1250 569198498 569198557
    0xf030c022701151e18050406090f051006050d051302092502150a020a0c0c090b031b03030a120b101d0d03120b1503040807060e03090f150c03 62
    0x2c03c0c860916015104a41e00011203051915071000308081c04801602d00490301140c000d40c00090000900900c0b8250752400078a0040100302c10f403a214034104000909800c0210074080c0840c0c0030345c0c1d9400d1604000c2c034401002010050180ca0000156600c00d42c05603580e1010140510340c0100c5100400c100f24031300d003015550fa072041b1000d5402145d00c0103410044941d100d94040c01c0030b42c0c00f503660003091004035a6038080a00c014640c52070600c020807001095404100f0480d019412609160300302200b1002e5a007098030302552503401041107140c918443d80000710a07501c0000c1c00b04802e4070041c009645941807070301407070008115452050801e80d402d0f4141c1c500c0007087d24144805500d548005040c102d00004c3e10068548501e5100d006440d50151050646199070060303803642001d00d819082d5510030302e000d90310107003411641840a5404000c80d015141d0040c00c0000e10120001888107180740d94241341300004003480701c0080e6460510040582c00e8821460005100100d0807080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 569200998 1250 569199748 569199779
    0x1801030612031725050304080705010e030c0d0912020616021f081602060f040c050307060309060507020127031407030206101422021e0301150c0f030c022701 69
    0x488920001900d0812280000c0700510b138410304d2800320780d40c1d0703070740d0411942a02c43c0c031130005c0066190042101010001002500308c1c1c0000c81c090720012801b4003c11210880d85024501c451201c101150006140c039100518540b500101505e0060078a030300003900107801b101104801050b0700c402c010420341e02c1a030980c3c0c004403490001c02d1441c40940700035034801008000000340011034010505000749079001c0b4004001c000c04039004a5203500006000c0c1080c42002c4848500340800308031200e00602036145041d40e2005034000f00b01c0205004441c4211084040d03050209a03d608480394006200900b078060094005022905021102d0f140a4030340b03511003541184502c045001a23a108000e00b420900d003281400701000003410350030020710502c0c1d03016501c40d0070569942c0c1c1064400001d14121070314000320047d00b07403011906607112055400c009126444054032000081d00400303006a40e00e00240005114500f4006405900e901501c0054500e41404004110002009000303d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 569202248 1250 569200998 569201011
    0x405010b131a0a080408120403090306062310051201090b0a1514181c03030506120c0424090f0c0c02091506160308061e0618010306120317 61
    0xa200c101c045180b00758450150800c01000c01c039440f4041814400840b066408180644d010307001e440c10945406030640c0e1542c170045641600341600000d075a1855022804480d85a910780d8481100c154100907802d00c22000d0031017880002c0c0046100f00d0390340881035001e403081c8040007800c2400401007040d0101c1d00d81c0800c403414140f881040c0f030264001d4007a500c28044001980d240e03684109643c040c9a410700f40160042003022070b00000b08941c0b000c101c00d260203034400b00b01640f05d0030107002c00c0b0300c141880038202d0b0b030015055000c40c2c146940040c22400c04403001411455062480d240103001d2170303010801c46a261074100c2007001003486145581c0c015414000440102a40031442005009000f52407140d110781e0141150f88661301110551840e000100c4084070580c900508419010b8440c5405803d2444802c1b80b030014640b100c444141c40108000e04207100c0c05101078007644d013080c0c09410140c89500c0021441d295440307070450030f442030b04c1c1e06c0c40103030039004448800540145038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 569203498 1250 569202248 569202269
    0x10b06040503030a0e030c090a02090406140f010c060212240f010801120501091401060e060d080301180209030109061a0919020f0c07030b010602101505120a020405010b13 75
    0x3005680e50010071130f0280c50190034010b40c489118030009042241e01c110725900400403100f0804a015079034001d00920741c0440b02048800d484458004240180c9848107812003c0724145054941c000d1840c0d940c804e2044d0801351402c0034180c00c203003000388152000c04ca11600000965102c81d07451181d0a164070301603448041c2a8800d00c00200324084c10300c200c84140380140407034018000c1c2904020703113403604004402c0c1c0c84007264170b0203402030119100d00204011100003143c1c591801d1858009565084401e59080d0f03400c040d02003400c842d030b4034054040964200701c61016a10280181e60496004600010f171954480751142c0341d9041258049100301245c1c010003c034440c4100000103a8018807030300603126031004110119501c80d51310401d03a2031060003400000c1000a4070aa410f0310f90036800d442026413407400b403c0c00e45030f169129150794484800c003801a0304082845907400f26841d421640710084a40109044071000e81000c940c4007000240c0c06040c140b0070500000501d52140b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 569204748 1250 569203498 569203507
    0x4150c02032a012a0e090402010e12070f2d090c0e061903111201060c151d060106020d021c03020c06090d02010f022802010e1905010b06 60
    0x20000e4580c03180b01d9054040b650304421005040040101480403561a8002000301e0182c285041d00f1400e00c2080d204801400d00b804980114820826559070020240000038135403220350042d13842002c3d030b8100541111090b400d1490aa001300a06402001c2860305210258100548a2440583ca20b0040c1c028541d14401d00c600c45004290030007282d030042c000013201c0c0b8000600319a42603a0310302103644010042066540d0b42c1107000700b010b810349180c404020741400890465024084d0000c01d014810070361004200d010b024125020800d8810100481001c4d41c25601000f03da1000889242a504210005104207420014076014050a0000784500742500b00020755428410040c03200c2c5480e50001c92a4840c003d030140e50000c084941603c1c202d10b4881103441e55200d03d222007070015070803c00030103440c5005200f100c02c80d404194591605411712807544a41c5400a25801d0441d944c40c21500d00ca064148200416101c4400150240446504025080da608455040d224560420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 569205998 1250 569204748 569204771
    0xb070305150112060f06050d1a1f020319170606090a03031b0807030f0201181a07020a020301061e05060f0417190f1e03200304031a0415 60
    0x4990703680240034a00000d0000103055840090300c13045d8850f99483c01d484102260342074000d0f001e08100080b0303940030490203e18040820b9500e800c0d0880b20f8111303004000100c81041d41c2060b00000d0446401102c3ca440030100d0607075070100003105d50800144002d80d5180103c01034041d40c07a0021411a500742c1081c8034400014800c21091000605100e030700e202220703a10412030341090100780c01c00b540d55101e11a0b03080c003600a403020504500103518140030258500b400e02403003110aa08419404c100c42071081c41c106450030003510000c19445907c14410050b80e090042e580a01104401c7c103094010036030031b4003108130302e5400861180034184051500c84070352005070707000c4a008030101d024181c0341c0c0c0981418544000c1920182e00020b110607814001c001080007541031140e0348046000300c0c02280038070340914102000b0009a10011855240090502c82404014481c41500d103050390301ea0340c0720000e4240c0e40034074015480140800c01400041d0751410030203400880c0074001d00e40c400d13 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 569207248 1250 569205998 569206021
    0x203181507031d0d05031b0a14070204150f0f08010e03090d020607080406081506070c290c010504030f0801080c1903050f0106090606030e03071403070b01030f0b070305 74
    0x2081c00c0200b40d62031140d407144003c0001c80c0110007820209540c1e2120940380b0080c640d5004940241c00c0800e402d8500c0f0354440d40714210740c140300c8596600c0c6c022840d84504800f4a034410001a0b82c003d880c0d000c0410f1a07500442d21900802c99004082011403901c24610180c0c40c0542c4a00da80d64508240d00d041d0308000300c103d49210800f202c0401803401c41d4070002e030090080710030103000c0c80c0000c80c020a15903040010f803402618030110316032001484208100c220b02c110040240640e031050810040e021b12007400303110b03000541c24090716640034541d1404d42900900c4210000b60745940601091580003c10304141e100d05240c030601c6503062440883c0c0d98a07d014940303000320b04480910254540031040c03a400340d41c0c482d003a074800e981d21114082c040d010030702402c0b241e41d243c0013000400d503000380f080c0031000500300d000d94104115521409080b000c0c40001c40700d00c3c0400c20185001440042555029621035030200501040300c0c14604c111450040144080c9840c085c284050341081 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 569208498 1250 569207248 569207251
    0x27150919080904140c0403020306010b07050a0b2206090c0e040203060c0d1d060615190302070804092c010c08060f030a1709090901060506091c120302031815 69
    0x85081d642d98039060010800808180762401040520a03061100c0d0401d40c5004004690013201141d0041c1d0700e5046550703003445000001011039120f44039450025020724601c0e0303481124400010004550001043c200c942805001c07100f0b00c0d56118187d041141a03020300c40644004103c80b00985001d034003080c1d50340000341c004220004041295408403003a030708000d40c44c032410400c0c008207030503546800d030380c0f40d4050f1001c81c8200c0e6050314a8000d0007040c4152054105100c421418140e0040c0c000d42c002e5005030380035595002c040002103040826400b80c200b107034000806900421203142c00e00005c1d0307140c44c02c481e00303030ba41000125020150302014854125800b1662520900070590000380b5104a41c01c0041c2039080309454844000e0604002e04810300d41542d0342d400030368444415608035a654013a440d8446014440c01000c0c1c20114880360401c1140201d85116002540b90070546007500021080000d400004104141c0c05403003129180c075a0410040c25800ea488440d140716660 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 569209748 1250 569208498 569208503
    0xc0a080f07020a030f030e030a0809010c0f020d0b0708090a03050406141e0a1713030f17280504170d11120402100c050703080327150919 60
    0x404503060035406115021a00740a41c0240401c091695a150642080e018002c055000c81c00ba1166081c0380e05011039144840c682c0100d07050b20b089080390040d02c2c120110b5005445405280030000b0040c3c881e61011400580100c0c5c1303007002c2c5c0c0f41c541c400503c40d0000038500b240f00e07040390f04403100098208003a2426181942048043c0407008880c020b014001c02402c060020300080c0c094404186880c010188104159505106507007003070740c2c6d85421380f0f0954a2a004401d0540e201010900c568030500710388145107170616a0001c1000e01c0c1e00070381c41c2540e0349080c0d5210303d840d28450756501030f5050800c0703036402d10074401440c003510340d6161a00e03071a034180400c200001c0c00d03616180145c0e00400c0484400c0d08240d86030b80440c0d5070950b5540046804900039a204041010041d004000c20202c0c2c550050003044001d007950f88090701500060420752022107040101e2500146901103003960f248106c00411350398245500f010103030781016000901c903030400c20b4201240c01c00040c0c811034158 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 569210998 1250 569209748 569209763
    0x60a08071802090d05011826030a0f020c0a0317130b060d03050c07090504060e01090b0a0f0902090f0a06060f0f030b06040b0a050d0e03041d10050a08070e0a020c0a 72
    0x480f40000c94042104800020929480d01145034540113400d0400e280040c0152014545580341da801d81141000b40380c40791900601c14000a0005001d03a0040c905c14450041c0260500c900c1ea00003501d0b04170904000c801180103c44c1c091102c5d100407801e141d10000141140460060302d40300d0798007020010f004d1034002d0b540029400d0605005074100c0f408200200101c900090b41d60102e0002443c2c143c03400c0340c0d068144208940c1f4010140283d03151641c10401010f1541c0b9040d600703000502c0340f0700000c14015156181000076948240c090303803054a1107001d0510718a480c5a1010450303580350018010f0012400c62442402c0d446130310f1443c8a081410002150040342000a0090080750b10050301036400284288135254000094100b44c0c002c66018007841e074110740e000b03490f40242d00440800c0c003044003102c1c1100300301902a503003140e80e010003900084e4440022071810389180d0068120303030b400b4520070011015080c080035880300750100118181740d079000340f07541c07038000c5000041c2684 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 569212248 1250 569210998 569211007
    0x705010c051903230c0a1d1c15050115020d03090c141827010e0303040201081914101410111608010b090702010203060a150e041103060a08071802 64
    0x8540c03e10441d1203e00c0c001d0040704145007220108405d42c0c001c1030550001001c20f0b11107100c08010310b405603807407000202480c4800c82000400da0082850b40402d848810a511507a407064140344103c9021784640c202c1901c03041c2d20108084e103000c0d010009002014070b40701488001c2000c0b06511b1065072003602204202c2620a00000d43e40042103001240280d00003040c40b10744041c250050001d140e40814580300c0024030100d55080390106016210309800400000340190700c201809a1301002d1801500c04d0707041550800801c0f144468035041e001840c54050140c100603c40c0901d0007441d600d81001d9081000202280c001400104d20350140b20090803c204bc4050521000041c403880c600c950202d1555420030328013030012003580e01c0c0901044008140395a106000300c910421001e000b1603480342ca801003400041100c4c80400082080c441d0301087c0564690065101ca003004070100b540781e080c0041082a42c041c0395000c105158000002040600300c14004140004062035005840c4d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 569213498 1250 569212248 569212271
    0x90c040c030207080408070f0e090d08060a03050a0b04031d06120a09050d05040e0a06060c031103040b222903130206040b030702010b040203060a05040e070308040b0705010c051903 79
    0x2e40200e001c000c0c40e58102103404603040d80002410011100f200d12103c00480d621300e2078000c00802034a4271071071604024804d40b07000d4010b4000541001d070140003224650754a803941e9003065a0100100c0b8020398040038407003170541c0300105441e055050150451070b01c1c0003000042462003105106c0402e983c5480020b9100501e5a0051003103580103c11380381d19010499000740140c0c01070150b05181c644103400b08580c40c0061161406951154490400080c0f00c0c0e20260742c0c0140c03441c0c602d081e5110400007c50401010300142c4603c0401041c4031241c3e95000070183d90441072a0044500c9141c0030944d400d001005902440319608924134081e62901c4080c81c03a07078026102903021350408000100010f0003120036000394442d00704d40e40200801e560450400080e0f110a0b20b07202e80c0001c0301c1805000030702c0d080d80440c131208032101c115040e9a507030350740d80d503240e400940c4582c10450300400d0712070501c002801003110102151401d40e141241d20b0b10212010714240203601c5c2050f685802102d003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 569214748 1250 569213498 569213501
    0x2120f07030e0d1406040b0903030709030f06111305180903030c0d020d050138030601030f1d01091202190f0201030b03012f04230303041e06080708090c040c03 70
    0x603144e400c041d842a050400b0340c840ca640d001c0036141200d148440750b0014059034000f005032400341c0303943d82e1f44010ba2840c64550601c3c0c034113012402d485490f610000e036541006400020010140408010045203241c0001c1203203020540384c0c480c201880400821202d10400b104803948441c0e6090540d898140040307202c4028000d03110000b2591b40340c440044ac0e010b1030072800c0e80c175000300440301c010304001c80c503080350008820281808451505102007501507020303400c2a0482c800a0600040030494500300f10941074012a810b0aa40d6440c8100c20a01a660300b807601c40007801e000074902e88001908042206104942c05010400d550340c40104680c86a0400c2d08049802002841201e07203440c0760020001d011008820207100310204a000c0f00500b0b410b4404aa904e071725014500100d112190030305042c52130307089038180020000402c0104170040c800403080d03440e81e03448a005081c00070240c080c0302d02030401010307c049501008140c1e500085c0d80025000d0903180860034000c040010390 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 569215998 1250 569214748 569214769
    0x1b031e0608010b0916140a0e1504090c1107030807080d230a0903050f0d090c0617330a0f03060209090a020c06010603150909030f02120f07030e 63
    0x42640e051600004200c00150098001d0f0041240c8000e166110074103009418a0000202d2000c0382c84014010320035000c50000d0070990002d81003000030610b018002070140c1e520441c4208440401041c18405000b0604c00c071046495141045010340803200039150342c6185074440101400380010320141040780e0070301903488003807088809221180f90703024061a0b05954400068402000c8030000e40d0403007041c051400c1c140c3e01521082d181c08107040c1800d0f86a80800b0794403d10645880e41f0500140491041c580144000e540714421540e0103000030301a005c000c0d00105603040041d001e03c10384000271000c2c071300107001103c1444d00c82000740d01141180905901c88400307941d6043c00003040c0303e0540c006040220007162000c20ba5a0b03585045c0049000f42d02e08070246601607801842243d009a2080f1b00c801781c441c0c48074480a9881c1000c0c0161004504100c0004414003280e00d02160104020301c03803244420803880c180340c40c2005124290241c00c0f00502004000d0a1340c507241c2e180c610440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 569217248 1250 569215998 569216051
    0x8041106042103170c0a080414060c070506010e010f090507090f12030905040522140d03020405031b030d030c120f0903080f1006030209030c0a03051f1b03 68
    0x80d454902aa071000042d044410415400b02c0e4103140c1035a44002107801e040d205d80d04200200e420900003000854203200010000c4580c455911094080380b04104042072042031640182540c0d039816152190500e503040c0d002034240c1105c030005000701584241d1300c1c001c5d03a1000707000140640e10481700701c941c1d14031548512020b00301442c01181000c0320304001100075000343c071500c200720358440c140422600212659803c11951603403910b0312003611551501ca0328062000102c0c44c03802c1440d01810912451040c81c00729034009000c00c85410300b07108280c0034031142c04026050042e00008a030710780070005907050030540c0e140d01c0d1119050044421001d8500006401c01201c48502d1103030000740a50003040e800b184405c0006000e4114a07078807580f0420298944400c004c3c9484000c1d070183d0440b0f8070139540350194a02c0a4800d4803031004590085010714000c3c8000203400c0710390404130040b60f22503207086041002c0c001c44844504504604030466240004109004824009d1314a007060703c903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 569218498 1250 569217248 569217269
    0x103050c2209140c16030c1203050a0614090a0f060f0308071e05030405090a0b040e060412020d020309101704060b0f0418030315082a010f0804110604 66
    0x80e0507840400707580402d66885201c01c0100048241801c0011181110043d078071030002c00009403024600d141c25541c15109091045039812295511504040240413a40c0082c0d520020080c0040c9240039860044c49406c0300d41600b800034002007000c43d04c1c014140c04120fa141c0480c480108402d50001c0024050f0720030321442552a441c3c504010350283c1c1013602c000c414061f045418201f80400c94000d07030b5200006520f000d18002c184140420014848588565610044141600c550081840050b180b80c0a050640f6252a20042c2d072420010701404543c014092101900d4002040b075101074401c0b540842107051500c003c5804a441400040241c00404280001c01031720b0380154034020740445022150404101c18041214000241d400c240e204001440c000300b4040d512141820200342c10400d60151603102451418840202c861203090320912540708120000980c0000b04000b40391400029207101c4004285078000340020f484126080d142d94229510030040f034008040003110f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 569219748 1250 569218498 569218537
    0x902060d090317090c01050706050405011e020c010c140405060702030a0629030c01050d0509071a0c0c120304261009020906010903120e03010e010f02030613020c0c0103050c 76
    0x14000e0022000d10014208851510003140104d400071a81142680060303680e1814900b07d51943c00103402e01030000d90f0595a078940341000380140e8a10749400c80d10354032000d07980c0d581d40b0219030700b102e180d1044135003084540105074281003444400c96044803c12240c0903158034490001074107180000e800241040d2030300443c0f1310000011203403e8280041e03540604140700d0900c0c14540c60309a0021210f0020b0000c01c01c0001b201c249510541e00700740307210125140c0a4072a15004049940b08000d8030030300300d0100d4580030f0441c0411209140c94020b40304400755441e4110410307640c1c011400b8402107000b07990340340907108044141403ea805c68000403100080102086080100001c0205a004000c00070010314954051000c080480340c0c081a2001c241800340c9003250606100a0001d03819506c078640c0170343c101c000f4000c1c0064100000302c0160341e4140f240410800628001d02c3d91881801405000440640425501c5000d030086c01d020501e83d442204450390f6204010400742d840c80000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 569220998 1250 569219748 569219753
    0x50420030a0608071a07062a0207090b010e18040203030d02040902181f081305150f07020a0f0b0705040b180306090a020f10030608030a0e100519030902060d09 70
    0x20090021181110f05445484d0703101c01410000711030f2079101d83d01c040c40401c0101e0011f400781d4001e040c10322030078400503564039610003481104800800c8c01c100580c826074090024031450320484040d48030909040e004140c010001c14107025100459000c0b078022540000c1c1075480501c2201e0240603098000c41d13440c1c0d00c80300850002c0d00801a0242c1c2c86c144c1d01000c03001410300740d6681b0f8a01481ca8400e00024044500441d0b82c41802010050210441c9920400041c410849220b08803201000410ba0345000101c511880300010b008204540c082150391002c01d14407540001c0c115041103058050340c0c3c990724203a40d1032003584d0288981003400141d40c4000c0d1104005900f8045088003500d02c2074443d0301680e65a1840e08070040c1d40a42180d42d440d119180501c902c44c40c05500f07080c00b0030030980da810130a0554110300c26210210701c0760744080440749045282c2c81540b40306400c1c150f06040380211030240000c0c0c0c003500c1c1e5040c5075480300954155070350392040c0c0d100c4c0000f00200b80400180c91 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 569222248 1250 569220998 569221001
    0x9070203130e071d13020a02070e090304030305030411030c0a0b0712050c070b160210111c140310090e03070317040f08030c04050306162304050420030a 67
    0x81581842038448001c0c0891000408500d1600401495403040c030b80111103024201e0a41394450103d40c05079541ca6019080841800a0000b107a502d80160182c1d0346801c0082422040040140b407031604104010300019400c003080d680c115400c4050150303034030043c2d4042446c081c010580ca690011040d0000548420400002d040541c415110b404c0714491741c200545042c081d170b90f0341e00303810f411080050080c8001d090281c4881074900f072641c280e0b82c8454020072080501c00c101c24000401d07803034503030410381c00402203100b00c8000365100040c0904120401440c0c6105440340c41a03640e0000041102600c110504202624054808201c61a2030301461aa0b82e8071040e402c03000b02d000f40000310028924035000b40e03c2036412005214494071188d8802d101c4c2d600080c04241102402d0001207030640f42041640d10500c03046a030070304000102100684103800d0b40c03419100c5c2c45100c0c0280b51045020806842c1203c1d0190740204001c0c0e0b22001c030001c0404010040e01881c2c0c4040204400314596 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 569223498 1250 569222248 569222257
    0x601050114070c1806150f090611010209090103081b060609070305060316090b010210021201120c180903080c1314040f110a0e0307030804180e0a050c091f0504091109070203 76
    0x1c034800207104a0034806c2580c079030104810034800306800080810585003e92110000e500e1030600052030440b4580006003081401e80041d6408000842c80c0010040003e1030820140c0c2c0b0782008011038a1b00200003085100000d0410080503103850109005840c00c101c9601490307440c0b46001d04d5641c803030175080b0090903400a482c3c014030480242c400655514401c8030f620785054006030056a00344241d802c40c180780d2040841d00d903622204009071549400400390b80e04c40315240040b440e5602d50600500544014105007196403040000f07000d03202000614804035645150321441c0320760100e00140050188030340003045642880000d040b4a8001c100070000d440b0548ca945000c40380e07441c1416070b540004d02004010711030402061090360701048100310041401e15000c40d0384120440d04d5401c10b040c2c8902190a98405c0c0012503840c50000d681c294401e041042d00f140c1280b0740c0303401c110940128441e860041b0b641b21468800c0c418030984100013900c014003242d80c3c41c10a914000d550b40c2c80b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 569224748 1250 569223498 569223509
    0xc1706220912180305060c0a090807090e151302010f02190b010807060201050f0a020304080d0903050a1202090a060c1b0f0806070201050601080a1a0a0b070506090601050114070c1806 80
    0x200c3c90300c00700d28006001505803074201d0020000d60703984844036001c6038401441300041c8100540c0c0041d0012040010030003030610700d14003003881d04440344003074074204a500c20011143d4182e0100410b150181701c03001041e503024139200003443c40b03080c016800d000125000042d041c030303404800300038411402d111034104c0f100380c811546565582c40f012402c0b120160b03540f00703521a11070041001c115081e0061504580180481c034903106c2d100110200312480003008034003103075020600c411110342148a43d40b0441540c00103600c0c2c89071203c0080d001219a018031018841b020401c0fa041c030400c05034824504204004e2032074035646850410305001d01505c65141c1c14410107000071807051060251601409041c0c482d0356043c1c58401d860006852807218002c0c4084450b941448035584003100d100c0101605920107a0324030043c00e040341030000045c056103070f80c1c2c041001041390341da0100089800f450660007450321640185044a9544110b50110642400746060350040000340d9002c0800c448 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 569225998 1250 569224748 569224757
    0x612062b15050f061011031c050a06030309051302040305060f012c010315090c090203090111180f1302040303020c0a050f03060a0f0b12030a030c1706220912 69
    0x4900070500c041c1c9004541c5826910503840c0850381c00e040c00b0715600c0092016083ca4004090504401842c5400880c1e510306102c1040350a009a0300782c0d1f1055a400901008082c070070385080d07440150044006105032030007400c0501040c080040300e0381c16203020710303804421f880311810701e01041c0484803002e01610b1006105480010b02c0d10003d111150b500c52039028040c11568a50b84401600c201e2441544c0340e15500c8040d1480010300c000709400281407c050010780f281041c0c80300310f08403007028402d1810211700300040c002c80d10401c804d9a0030302c1c40c1114100e030014a01c0020483d04950141100c01039400840e01208054000c03451000702c41d02542c0103c0390542d12401c200c1e1044c80f02d599690180c0100c00415004442078003c483c420310030740400700c0c11002072804250070008003a4079044581001c40c00942c0c7c10340c54014030442ca4003070f00e0017681812440c540840050703000780109205080304c10714102141044081850301500000c4100920011806e0070700512031140d540d42c0006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 569227248 1250 569225998 569226023
    0x6030106060504140906060f03072703030e0d020d150b1c020609101e0801051011070b0a0207031707140303150d0f0c06020a1b03020612062b 62
    0x1144240c0c16501254099001300da08400600c00340050842c000e400d81c0e81000d020000010500050700c01940601600e684425412108102448003100e0070010103144458030981040420790001031706100f804210382e4019800e240d0300c009049100380510003481000045519003001d5103e6100305101a400d840207002071072078076100b0822805203003000b58410b0703090282c080c00e410045c281540c140c003036040451503000782d1040d00038600c1e100c4890000189a080041c00f450419001d040024800c5040c40003485000c060764a8517034a10707016080c0e5a00010810b036481500c00c00a5000458028035041040407034101c0e01c0c041c0381d21071501038483c0c5144081144044400000716841018003a4440c40c072141140101302c2c5650004405071410744c0c02d480100042a211f6040030020030803900140a2000d4a250812082084049290020402c6007080026131281c0049503050801d01101b44440e50301e200019042184513800807440444454a00480050607015940b43c03034015030020380e04c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 569228498 1250 569227248 569227259
    0x1606020304150507030f08101e031104060303090303050a0504090f0203070e030a0302071a0f0c010213290a050c01090305090415050d080307050f0c0a140a051b12070b0306030106 78
    0x100d01c5903200007000251b20103d1440d1091288040c1c03900b1101c06003001c03c40641c0c481c08154000d850300790200000000304410400c00c001294400d000c42c02c190703014040c90345191400341c11000c1b030f888042d091100010b0581c0d0650300c200b04840190000324010000030001d2644c4c040290000c8a41901140032074890003454507000030220105941039005120490078880d12091520810b07130743d00303000c04017403100c200303c1c1d0b40d04400341c4500300c0d00c00300051712461b0510300008c0b03129507540b020301440e1444e00c800c3c0704d411400c000342c1c24006104024036640e08012000b25101c1c0b28116003400c9a51800c9040000c1590090003010703801002c440c02c1c885c075144041c500000f0b96591240c1c9901110000203e000548004040d43e07010481c1e00308681854600440e0b9505270f4003030052a06950030680d00d04c01001030351300b42103220300c41310340040a40c410340340d40703059a4081402d10301005a0300415451a03598405a46040804840c0d00340d501480c0d0700e001d4503c4680094035560300c01e500305100440c070b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 569229748 1250 569228498 569228507
    0x501090c081f021c05010905072703020907090302030604050609071d01031b0506030f2a12180d0201020304060c050702010203040909150908070606080d050d0e160602030415 76
    0x70340004103050b04468210903080c1c000a500820760686500c1400c60105081c582d1445081d008000d02c0c0804203c40c545200009d003092064550000c1d030840f60a02ea800c3e421000702c605003600d0381521038000c542c0718034030f054480301c10592009505204440c200810000082809401102c80004441c0c0084d2641c110021150b00780a60343c4e02e0f50f02450041000c1028905003003d159800d00c1e443d5806626000070075990b6004403a040245c3c0018818002d41c507185040381150380c5c481c110450391849030700050100c50b105204076800e54010032004101c01c051680607101c60714000000b29603040d4036010000c1d010350401c540c01e84865181c0500012603c2c040c2d0700f2a2000380d8142e0165290504200300d101c0145007685054580c0e808540c0341c15000f19442c403480450502944040791a0029460068282c0d81b03e5088002941c001c1481c11650503004820b6400044421001141894698042078941124001c0368003030340d07440d10000600c1503004801030003910540c408000307803004075070b00c2583c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 569230998 1250 569229748 569229763
    0xb04030f08060f0f09060d060624020106030c12020f030304081516020705211e0c041509110903150f070912030503150409142b26040501090c08 63
    0x54000038030b0000e41d13a103071a0510003680e110b0001407070035290411545a100850302c140d0481c6000813442800d5842e01120580c8600c5001c00c180b0080c08482d00396502d540407010a407044064440ca03038144141159039017111071800000280c2260784550351703034503003580d90014548a002001847d40c041907a19034407109081d50440150020300d4894a00720a10210310003080c4003170038800041c084d4400c2480140a840e0650075140448040a03404d00e03030b0302e4140b0f8121880d0b284103520700f604500c80b140d084114402161079500c800501001c6610300003106101d00d172000d44c0e250088c0f85d102c0c09100a9120214040d181202076a043d655849006031030b40c084038066400520642c03034a100c0040d1003000150340c4010340300c503005070700f54041c0701090541c0d03078618080b00d61107000b00000d40701503400c006040200b0b960000100722040c00c0e28403824103800200a03842084290740880d88492100095416910700b01d84c1400307410f181138140340b03000303000050089426104044002461880020340b24 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 569232248 1250 569230998 569231029
    0x12110705060406050f21040606170d0e03070506130f060c03020616030905061e0a15150e190801050a1a0f211c03060e0106080606070b04030f0806 64
    0x41d46800d050100070764180e041040024540d5104005d000c0d5950083c203c002e14225070204216036a01b820f01d450810b507081354000308511b015940c84090b10a500054058011043e400d00040d40350561002c01c0c1000030302d0700100c0d000300c1c00258020342c0701d0b0b8000c0d5003812140840b01c4ca0700c1c4180c0321602101c5d8070760b8102d405001640910045220352072084400c1c08003503540d080010301c5000556483d400c1c0041228084400480c2140c910840c03610700c8409580003100410400000f52041d42080e40e440d00c44c041c118841d40705103c2082c04500813074038415000e4000780012030301c8421015070070b00003000b805841281d5003010081009050107005200b07140001c002c2e07802d00700c0c2c110428082405490382619034401802140c5841c000ca4a40d41d402400c02184003030f001180c000c502e40341c1440705c034a01031000c0500e400002c1102070b49900701103040d1441850004060344810000507031a0203020005070583c249103040c00100b542040d94521418102d4071650045c1d40c03007000b0812112060b00c3d61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 569233498 1250 569232248 569232259
    0x70302060d020306040b04110c060108120703110721200603040209040201170709050f120307080d0204030602120a0c032007050a21110604030905040203150d12110705 73
    0x2201c03000040d0380141d0b40c020b401030b00004080043c0d000060507214541000362003030000080101e840401404480d014080000082c460741105030203800741e621942d00050104550400c0c10720746084184454001030001c10710f136200034850041034001e00110448126500100b01d400c81800c42d84214145d000000010201821980c1d15000d21100b881c00800483c100084400403072840305580c00207901520059554042050500040c007029115205101c1d101c3c503c0b1007008011031400204454a956001411645805080307903208042c2c01070b23400081500b40003003030b405501c0466583c5d10340f0030b1070041c80500c00000c88031001d404a074501c1000c076241a000f00800f042c00c1c0c0502009102841c031910481e140f41d900b5848a41c90703005268a082d0403107003543c4d414580d5580c0715030081900d1141d100949031a05041c0d40c040d114070310301d110340b90160350040005517400c00d10b200c100d112054041c0c018000704c4103d1921000710100c040c0c0400c0403a6110074008142c1c2000034428040d2a4044c04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 569234748 1250 569233498 569233507
    0x80f010609150201140a050105040b0102030f0906070507120614010b0c0d11030904050c030708010608090d0e0d12020c0301051f030b13050d050403110132040f060903020f0307030206 80
    0x800400b06600c07081c0311043d507480c2c034184a10425002c9000340f05800e055000078540d41010700300400e840045c200c440c1158070910400780e56540d54002c45199450854036107035075540c189025410a68143d01c00d50b07021141054040520126801241007000804041011a07807501115a201d000d06041c640e003130b0b842200e030011814001d031400301c08902c00004413814170040000140603108202d0b840e2038600d00100c1070002e05034010071698050320351741c01d000180389024020345564008100d580305c1008418503d414881e01e13000222002580c200f016500075180e007450180d9109810181c0c14020340ca001e002071005450b08200000b0105a12420341d551817840d101c11142000240c1a501d50303a40c400e00310303000500100700a40321180c16843c0c194849117141071800e4a035400580f200c0c148030041c0d81045000e69811103d40308035098070007010860945018030000c60103150444801100184c030003083c0c454110720244222442100c04541d0110600213042d2203200c01d01c00203401807401c0c031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 569235998 1250 569234748 569234759
    0x1c050712051e0903010b0301090b1306020405060309061806010b070b0910020415081e01051c0203060a0e061303080f1902070c140d0c1a040f060e01080f010609 70
    0x5500218840d85481410b005480d00c1c056052541c108054040c0b140c0082d0b980c81030b0400b8016114048000c60080080c0000c0307440d014120600140055080280d89100104104955060b02c02034600541b10503100d00d019010035a88100645540b21400040300f00d090880d400000c0303d81c143d4040001280c102038032b55a6240c841180541b05c0f032640d00546c0f0f40d2010041080c805800280140f00902080c5410030002425031030b009400d100c4480c100845124504d040301003402d04480090b14090700c054151400c0000d1814010130085d0b140c01140188005180180c11a806110341c01007039400b151681011480c030700c211a90002c0c0800c07402030018501707003002030400d50305c041a403c0074074041083c0e0281c802264002c3c00c00300c500e14001c54082c40308032628600841e00201c03d07100440c00b02410385547c181d45041e0b200c1e0400d804070840c2284403961210041d68003d2200002507590a5110036000c1c28044441c0b050318000b4a5500001d0000d05d1408503050417a1030f13944a0f200c6260412 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 569237248 1250 569235998 569236013
    0x90b1f140d110d081b06090318030c0909011e0b132f0316030b0901050f060c070f050306071d06090402071a0604180203030f16080403141c0507 63
    0x503005490948030b100008040d901c8143c24821039074414800c055807010703200030100ca001c8a00384591516070082040142c4400000100e90b0f449030000303500030000c000840060301d0a241c4032265604900c0b00d805220f89404150003070320500c9904d200303c140e00200c86008004803140c8041c095803110607c040309201c0e81d00350748802c02e005441070408025280140d01c0c0110501c80050305100040000200162460281c01c003803214002c901e001c0c0320820808000902c80b0506000d203620486c03016580300d569a89a60444015200b55421f44520507a03d844000c0070f000c00d8881c1da4000c2c02110002100c0c548503d0039440d802404c1c404002444884809010842d00181402c40c0c00540c200800401300d1280420740c0108908440405010b1400b441270009540c4031060045e0001100780390b450041e5408801d0354561a1907452054917490300c21040580d107001c1c003201410482c00003030007006109001520712110f203240022640c540402c01407a58005d010005004000386090200b80c2c0014400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 569238498 1250 569237248 569237269
    0x100f0b090a0905030702030a050c03010b0a2303010219020703060c0309050a06110d0603140f01230606040f18050c19050307030e07060c1703061507030210090b1f14 72
    0x151013202d00f481c03101d43c0802c0c903100c2c52050595031507200494812561409004041050400b80c0c0c1125a440c54a0304546001d569228003241905480d01c032507009480950544815600c141c03800071030391401c1803001c0e44600c0a40002d03969281030402001070680207004807007840d07500c08010a9078500d641c03107071340040c0303051a06040088420030030700902481c240a104041c0d8002d102d42003100c0c1d40e0910052920003440345e582e516904011400b414070801c108422224466608451100d036035000000f905440350f40c000180c0413105600105451040e0a00c01149580e2084c0800c03054581c00600c074410f01450128080b1100c101d000c6540c400d22072000355401a40904000c07458018540d9400d080c80030980040c2c0001d24610320354024010912081e114bc0d0100c0d8000710300c1c501f002c0010846500100352101540c02000034001c040510801174040e14508490f0b0400400e01c0354a09110300010642c1c018686c0c00d122a452858014035900900803210704407611400b8501c110b003800f11403481c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 569239748 1250 569238498 569238503
    0x151b020a061b08070809090f0603031e07080c0d09080c0f06071109070e030c0402280207090f0515060901210609020c01240e060d1112100f0b090a09 65
    0x180410340c1000124100007400341a841421510b80b120400006e02181c0031009023009801c0701c40806000464401208481e410030040c0e240380500344440c90488450721817680000c00005000500080501d000f08462110a1243d80c030007440fa41d07201c6030340b50ba800102d4080c2c1e078401404a200c0c0c80380d00d004070040507403a10030707a0300a03414104c0d600000e440c240c00301c075100d001c100c0061210b40c0d14902840320303030f1001c2001c850031810042e22050712000c68146403c141d100700550002600240d008001e100e000b404610000e00440940c40c40c0e0344007030720081e103044845245d41980c490f150f28220098038441e8a040c1d40b03490440c06010005410a040f440010701c3c0180c2c0c07100042a0010b0300d000501810441c80c0c0003046e100d1028100c244800360055010180d946480403d020b0400c0c1101041e400c03150441d1042c1a07428541072040241070481c006923400f00c16242300044061010600c0301d0340c40454501084001c4041d00c2c408259820117621039170100080d40040c01d0b07803100d82c4c0000034150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 569240998 1250 569239748 569239787
    0x307080604060305030a0906030c05120a050403020a050f071406071a040204020f0409060f050a23061201060c0318060c032723040605010c14011401151b020a06 70
    0xd5a0ba2103071030441d4011b403d510b00054008805101d8141c0500418004049602c0e20529040145078045000e80740a08445059134450020406042c420000d00422079000000da0b1184400101410b5031556503100d08910b14550706044001864240142c400d0150802a415118142070302e004103038a20060080341e016a091120f01c0c008100c404c043c1010304980343c0000380d02d03400c1850000c00c604440d840503105881c03500e81800500e03580c001c0d00e0b02c803c040040c00c002e40003501c400a185402840b20400c508956080001003540d07100c014981d1445c000c1e00d5000c0522182200100c2d4050706010b1040400e000e40808400240f0030805045a0760401d44180042600c00302c0e00c4000301d1040d80090029507044001032202c0c3e90758200804160411030b02000840d140800103010341d10040b4014048980c100603014100d44207401130a01c580508100d0189503071965810503480c21a00c03c41000520342d1140881c01005800b401c07500250002d091800103440c258003100c0d80f40440c1028840351 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 569242248 1250 569240998 569241011
    0xd0c1b0b120604110a11250608180a032102030a0209090906160509040603080307030603151a09090f0a032601030c0b030414030403080a081509011701020f0f04090605060307050307080604 82
    0x2540c1108000c0c7c035002c5074202d8000b81468110028508a0094103100386c0d0440c0003500480303203600003403001a196050800c005e1202d00c040c40c4c40915212243d80554413070000042051047c00c65004122804003200c82c0720b1140c880c0b107103c943d42c10040b80c41e080f01c408030115085006000e00d0252207803610007031001c582152280c0e00c903160385d041691140042511500e062040000d021003098078100464020050000c0e40d04175550141c441e040158010f81c00100440c0034035809000f00305400d8081403c0720100311291a0040191418255920780e0711032210199004144605107a81266001080c58500301d0a001e0402c000303500190040703903003040d1071342c60301c40042060000d80001d5000d101d500740c0301c0c108110050038651004000360602400124518a5030340d840d0f00440c15180d0b0803810010b1410f05034902c034020710488140014144c008680141c0d10250300c001801601e0444409004840e0b880c2c0c180319060000351181004240103000095441d0b10403000c0c554040070040001c2a03c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 569243498 1250 569242248 569242273
    0x1103070204020d06170a05070e06010306082e02070f020f0d0b040b06033c0f03040b1b0f1009050a140303040303050601020c01020d0c1b0b120604110a11 67
    0x102e0f070146114524240e01d442d010020b8428213070f810304203004010f010b40450040ba66510f52a14030740e0080b224000051000310300306903c44da21401c050701c4040d08031650303070a01004640100c001a004000c4a400700000030341041c0381c07802515a4251b100d00030300000c942035820400610181d00003030b604508011043c401043c0600c0244d4055070203828090b11b01d09107682411704040240405144041025150031014a10714081c032241e10340e4a014035007680c1c04002818200400040c0c0c543c0300703100110300455803204107401866001320301010001807110003081c140c0c403407060351091708441c1c00c100d658101c1907845400a400c107910850a03981302c040e42d59580381c2d144602001e15101035101104000c1059058030803d80c01640900041c500940301c130000039507416115040303c0130000c003400e641041018001c1d041c0310703480c110f26002050f1620b03000c8402040d04000750212072414000d012508038107084c0300b0400081c0500038100d1401c2e03016201038500c408040180c590512450440003607 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 569244604 1106 569243498 569243501
    0x1031506030b011e0801020a0e0a1d060118050307090f0c090e0726132f10022a010e030c0307140a120f02130209030a031103070204 58
    0x80d040070f041d90b038002c210131a50240c0441c0d0700100c0d01800f40c6e5081403031000d65500c155050340b645a41c0781007075201320745074038007540c2d281c0444404541554811028070320014200416489e41c140d403036001c2403401c40140d1004071400c1e620508140b0044c142d000300007210741c1700e01e0100d09441c1040c1c0c0042121401503c040103201ca021101d441c3d040302400b02e40e101036141c02882007280f43c0101e01000d6080f0341001242c03c0c1d0f41c0b440c44130001007441c408140490181c15032481d900341802081c07103480c500b19100c407820361003940d031511807c3c0c403640310300207500c04820002281161603600241c4204086c80303105200760008000d0039084d4900003a400102c50030103d280b0030540768100854408203035078010500020540400c40148690302c1e00080aa80c420b43c0d0090740c21361242090403c901881100b035505410440d00311000c01d11900030200b0038505070060b20300c0c11506900040 = true := by decide +kernel

theorem cover : BRFrame.Cov 569064748 569244604 := by
  have h0 := BRFrame.cov_init 569064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 569064748 ≤ n) (h2 : n < 569244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
