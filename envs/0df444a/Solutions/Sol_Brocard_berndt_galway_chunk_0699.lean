-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0699
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:12:58.134278+00:00
-- url     : https://prove2.me/submissions/1e904f2b-d840-4959-a6cc-d3e6b25b0e60

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 125539568 ≤ n < 125719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 125540818 1250 125539568 125539571
    0x5011704060b0607141b06090f040b0604030206040e01050118081b120706031505240c0c0405090309030f010605060a030e07050d05100608010c08040834030201141315 73
    0x4e04d00290750305880180f014a40c1020740201e9400700d685002028007025507a01c00c200500642c60161030381001d0f250908002c6074041104125a80030030924842d6410194000c1e0002801180720b60380f5074219812944280d841d425651226185100e040045009580041e003000b1196240754410b154210301e8a080241500c9680030f00c03610181c076000d0140d11038008241c8510b4107035160344510405100400c030540c0c4408031100100380320205030212007658001104081000b040c00d801c204075103400224042c00420280c00d1010f2110b42e42c0d0000701c520340c8248a0b10580320b24001041c01520102e90703016120794140303881400180c01515036560ba90b08588039407030340010381c0d640c1e01c0541402d003802000980348950008440805482a94220b043c1e66030600e1311b10411258031003070760381d40140c000d04c404d51641e0041d4134071195100406080700d03095215841c2142c080c007000d50000c03000e030702c2a002003047c141074500194240340119600f41001c0c1c0a2207100d008107909403203c21001600400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 125542068 1250 125540818 125540827
    0xa06030f12170114011e020c090907030c14120109150209040b360105060405010302090301140f09071703031305120f0d0609021c0e0a020402030c0901020705011704060b06 75
    0x30700580c1c0c10300913808061542c040c0e00500910b0b50700302c414158140f0b091000049907041d00712004c0d544074900704101e80954038210014042c000103100103400755910407004030450f2754884c06461121140c3d060786104d003400020700e0440700f1301403040c04100c603880511844c5503903010030031b4002500440c0d065904291100e8145074039a0303d40321040b06080c2003090031003950a50070700c0c0c030032060380d0a00c041002da0440701c010300c916514442614120303002460301507030711401c1c03401080c0909040c0044018180d001c0d8203020001c0755a40d1454031036903034401210340160751401c851003440035842d03940c000d942082000c15626222030713112082b014020700490340088032007600d003a40b44c1c0c0000f43c170910900c40403580c40c21408050183c0030040550310400c2d030801035954100d80d0b10302c1200291111aa9580c0521403c10401744022110319030000c00454607840d010307001c0c0015601c0b15401c0f9005018414021441d1342c054001c0c14141d80241090008985d40d0b556550b00510361305001c41e512040500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 125543318 1250 125542068 125542097
    0x105010f0507140f0c180f191b021b0114030615070302010c080109050103020315040311010c0207090c0314011701090f120206090715080604110f070b0a06030f12 71
    0x650101074508400a00c00d80015044d55820304d0361101001e4820b0a6807401c5c1c0e45400f000510541d0081c001404144042c0c56040007400c10b80c2d60300e03d052042a00700a941034149a107443c1c0c031440003a00345c080d100c1c5084180c0c401c00d0168001c1d01d0b407501181004120301d00036115034000e0b55001d41e014260482402c1003452600554000d041f00f00c0c0141c3d160f07610b409155a001203445c0c0100400f00d8107000c9541103a00007038641d09010804c01030403421074001028180b155500d0412461000c0007003044286a480082d12400c1d1400360507185030521138010803e52291207503102c02c1f42ca01c1c00c91444d690030072450100c40324130110141c8440d92180c510201080c0702c44840c4403602d101c5d00006d403045485070400f900300200100740007080e400c101c0701003204101200b06050703034111a1a0000050382c481000400500c14a4a18100c0701d9020690718a41d010071001424114000c26051045a0700d0ba032160050710303058003004007010f1a1140701000035280d400044000e2209040c414808620362 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 125544568 1250 125543318 125543333
    0x100f020403080f04140a0609060e011812020405011505030417040803030106050409140103020f040207170d0c0816090909061e0b120109020a060c1704090c030c02010c02060105010f0507 81
    0x50385040f080000000e030400101802541090202000307640141019240c1a400351054101e40718080c1805410070035188961b1089040507030080d44d42c070798900040d40706c408940149005110882c020351612001040a0f15010400c200525180d41d40d98515030f030300d540380070f1090015209403540100a00011691480900286d03010b00115640c46441d1450450540c0a450551034031103200082d44005202580700c1d412550104581520302503a00c400910300318a940d10b12000d0158000e101003006440d1503c030350407414204c011b41d078458900f51540c08040e00c40700222401c14010132005e110405c1402501d80010a006020742c000140c80020004200030b0181c240c0751065249540c0d1040c00302514060248480818000c0c000700404001b66010030380005a9002d10424400c070b0b160f4110800c002540c09d500c07142d0310003003225107030f941d140e0b03520014158600c40c03400401e080c8640c0101c1d140c0305100c0c2d201c3c40b440c164005c2807103074279081c015280045581846c900f084402c1080d4000308844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 125545818 1250 125544568 125544577
    0x12110a0b0f130e2a160b040201020c03072d0e18061303050708030901021b030301050a05060f030403032a0c060518150c16110f03060108100f02040308 66
    0x249608542c1e80e150402c074150070aa001c0c2c006009501160052200e04581d90003c1c540745150003100000d0040c240c45910040e004a4aa0b41041c083d08480d8004211205942c03501891007038003141c80440c8650304150701c1e05c1003070054841c1e400b555801c0110030001e0769462901d0341000d40040d410f1a03201d4074003400700c541c22a09140f103070120180c0110040000c1104c654002b003265280c0484901e0742d90000c0803440381c900050035000c030100100705e4000d020340c110740002680b04009514100d100d00702c5502c940091003000e100d40386900780020745041420859440b99120007200c0d1440da5213590540040040c0344081c07403060602060083d00900c0c4000800743e09016484c2c3d9015a4164500b12003a50f20003403007506120f201c1c800d829110440040e03035003034000310781041010658801e550446180220b011445607540002011801c5c020042c52002402c0d030251a07210003d01c40c1070905542e203000388104602940000c21403c44405550300608080c0c604a8000d460641e407a22951419040b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 125547068 1250 125545818 125545837
    0x903020307032309061309052e050904061a09011d010504090206120703150b090315040213090503090402130f1a07030507031e0806031002030112110a0b 67
    0x20303100080c550820942c6034607420400c0404503c3d0f80c20304404803140900d41c2403e0145030046480d407000013000f503011000e0302c6500c47c200a03c0c9044281ca0145035544070540504030080580c03801c011050740d1100059a80241807a0030545036a07460308002c01e004500000540c0c1ca180e044840c0b50b8915007800c0c000c0030201c00c2103050310b03007065003145804010f0348102d01c644c2c83c0c44011700040e1600c0c000c1d03c03c1c504140d0240076840c6c1e1001c20680252112400c0e86804115003540458020a4003020340a0984203404698400c06c24071000c0c4c10741a007e07200654000030301440c4049404094204000292050050b6030504d00f0800110702079804c15003091250181000003170245604907803460008102d40202100b805511500800103403280d0311005d010464001000010b041c0940e03689100d111608040400c3d0aa003800000c190300b40580340c1030700c607002d00c5151050007009d60098034140c1e60281901c4695805540d00c00346e0112254107002d8109000c280005549a80c0c80083d0070f602c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 125548318 1250 125547068 125547073
    0x1902122e03020d03030504140a03020a0b0105060307080109111b10051b0a03020a1b0b0a05100b040909140f0109020306181b041506031508071203120906090302 70
    0x20240421100d00e0011240080c0e01a81206801c00140e5540d042c40149560103040006054079181065804079200190015080c86004140c800309036000605040150103105016850b90701c40e41000703098482600d10400252a1b44018409480343d0f502c6081c0f800140d000ea540303840040c12041c600740807020030819564005501c00410410305014040d800a811103020f03000d59141081e0342e0b103500500541404050340480e842d001280141c40c2060b41108203030910316200c0b803600d80060038480407100040d1503424034000c920703a40802c1380070f201641c0152008038205402d010b400001041d0150703003602e0502180900310350340d440034003071400349829020010403404200c0c0140352810001a186605040031000001c0f04860041200310700e140001241456220035080014060003860b040005514443d00e00043c49039056408120300720034012007140760680d84e402c1e02c0d0700c0b00064030a003900300d20f642c0e03ea200068452180b8480d0307090728000c00114081282c48000c1140c2d01840101d0140c0e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 125549568 1250 125548318 125548351
    0x405130b100806010f0503090a0b0c0c0d0801120609020d0807080703030b15030601030c0c020303030915060d020105190c0c1d150f0d08041508010f080a0308190212 72
    0x141000c45000c080026107080880b01414054002021803400b04040c0702000b4020002c00c44088040c00000c03800ca0700000f00e000581003850000d0402d60000d0411002403281c030040f803168600904226040744d61f00794003400c0b00480c5450340005041540ca04a910030109803420300026103801c0a040040d0168a0b40ca8a880c0c0710b14000c3d0440b071000c0c400d5440343c15851181c0f43d18808600c00c50358000820310303004c200e00c44948070945920700c04070402545404044100001071800140d109032020480b10010341035202d00c414800e400040c1d02001e40050b40401070076076000c02c0328802d60712075215451b00b00c2d02c0c6500d40c0c07604072642c4000d40180302d0840401100c00007107111040c00300c1c4c01051b00100443e441010500281e00380004841e0a8010108103101c5414002c03124261001080c1084200341c94520031040242481d00074024903104c0000711001160714640081c2e03146030140d06454142007a01c2d034410074034407416501401d9410f2030b001c00070400c01019a6918900602000c03240c441903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 125550818 1250 125549568 125549591
    0x1c021605061506030402100c020310052a04030602130305120d050601030b090106120b19030b01120302060f0a110c010506010e120c130e06010e01090507030515100203040513 76
    0x604401502c26021055150003206255070341c48112500306904446004c8064040c040548044200b2403029500d8002c0c101e41000e00441600041e200b001218039000c819010510108007000f009040b43c0140b080074002840011000d13801050451000317940c00340a90f90301d03540c1c05d15007201d140ba64a0b50351000305882092510b68091320386c001d4403d0800b4040c04012001141034143c0c144200f138100300b4285174001c51440c10350700505524030b003d400003a6401924103102d9900010744801c5035040d4140c0b0001403202d40358240c151030190702d94040e0107142c0790000007a200010217021030104039901d01c0c0000300c00350280028010341c0814400440c980c0341c0800094418244402078600a48401054040184012a0f9020007503012034040c2010101c88040c04c00401354001e08604c075106010010981d2851800c03504e0480c0e011841c240400e0b40c80c04800c509030b5000352601c0c22025400c0c802e00c1540d14084d124040b00501600c1100e09042d0b071000007904940c030300031119001d15546c41c40d03104c0703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 125552068 1250 125550818 125550823
    0x200f2214010602030702010c0c090906200f07062a0f03050a0b06040603021b0f1f020702310c0c0507090203130f050f011406030c10020c04021c021605 66
    0x410111616000e1540c07400304080d440e445440e0001341000200040d0104110514400c01e0190480b4a0304002d440314500e0301c44000e058a00004102e03c003120700155500000c2000c60b034608416001c402d0919200350345140281c04183c1c40d02d0294082003a40c590000c02c0c4800d50701d83d13a43c46542d480c241d584c90140280403994040c200c244203c2c140303842118207440d00e0080790221945c1d03140c01031f0b6604003510409090000c2074040807107070089881240c0100c8001602c2800801c45155541c0001d840b80480c008238840e011000f500021101016000000e0600148038035031880c16964401601d07002148040340c2035502c0c030700d0106a26234040e00a005003081494082d11510f0070451450600c41220f0b02c03081c1c0031640007060b40d0020b0040808000e410300c141a41c1062000c000d0042c060172402805030710004545840c000d101e00b13884038610b4506104588a08501500034200c1300c110314007400044d501c20003035020741580c4000749004240051000b00400e1342400c030920f9004d41a4500f050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 125553318 1250 125552068 125552081
    0x402120a0b090f0711100c03020c1506030703021201090b07021b12030331080306130504030917030c070806010807060f020606061c05040b01140103020403200f22 71
    0xd02030340070b60081104034483c07a602c042d00b142c0d0718102480259070310520320380f500300488118401d6074141050918520303007680260005a2034207054811000c0218000380300403000b11502581544844020005420813002c221584a03c0c8000420040c940f80c581d151104e1f8242c0304e420061340040c006c0b03041c400711107a442a04d03002c1220f45842ca07a80c500261a40d9000c050308098a46540040c26910042040c00030a1850008400d1443d00e016600340303205150402c0700e000b03001da01a08001012591184039032032245606496121055003040ca01c0c0d0300c5070789030210568003403204001100c0c0200e420030401e8010304c6240300910b002c1d030400f403482d810304040350302034802e0281c141c803200d684a80100340f180d0f00820968489441d004000445043d0140d80c241400ba4a03203800700388001d00c00c800e12003030305a0f00802e070b1130541c8001c480011001ca00c070340d10000c0c040c480c40201032420103020101020b581c0b84000d10059681101100041d07504200c0740d000d101d8580c0781002201288110300440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 125554568 1250 125553318 125553341
    0xf0509150c07030909050c091302090321031504020c070806041a0103031d03160b0c010b0a060906050c101416020c01120c11030a0201060305062d0403030b0402120a 72
    0x350309140390380d40d001c2d01d80030445c01741c1051a52600b00086828842106032400c1070402040d03401d1041030700d01c0c05c07070081d0301175004107010f405000040b40542d541d0001c01710b024161580f40c030b481d6503034030841e40d00301c0003070503041d942d120b5000c000984e0031203c10014000a054144c0240c5024105403802c14a00391040e0fa224141003004801040426000810f511190030040c0c403505004400c000000c4c280080c3c10140203d8000b07181001c55001d40c444040c000d00384410000704008561102040b80d4584580700310707800aa4422403e0100c0381c400c802601c2030898075000c0303071010162856100151a10380540c20304041401040080140740c0c0c4080902000c4580003800e0b008d400c0e807000900869090294889582d100d00c92510000d1040414204001d10170041e039490302a9403070024040c1c0751500c41512240f2502c000b107016241401c101400c801118000700718035003107541d42c14620b4a8014803e906141e40d650040c041515030340020700301b5541c00b00540c00c0c00d24150200504440c4139100130b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 125555818 1250 125554568 125554591
    0x1e220f0e0109200a030e030a0305160201060312120204090504050607091d0609040201020a0203010c050d0608031303030f090e040317091b09100f09061401050a020309130f050915 78
    0x1110f01440703216a042400010205442d55074110700300c01580a0700210701c8076401da100010b4100b80103545540224010442016054507541003c3c030f0803801e842d8280801f80010f9080c1004148650203030380300f80018040000003500b015a180006003c03903104440683d42d640003103040244040d440050071015111102c101180d101c0603075030703061800c88000c0c5654080c840c480c000c90290380c02001001e42d6154010000d101c1c2540001000300540c200b12940e4018a05040c001702d0f0310000403040d100d0084541070010713901c2d0300c1d640b030499404400e119041c4c18080d0450020400801c840f0549204038020f80301c0511142418141d4a03282000604081a64204486148511030415050140301c00200c85000c2141c440703003e40c944401c11a405500100e41e20000000ca1803002d0304403500311041c402e904a8601310050054906100f810309810040c1c00c1040311400f540307000040d13a94050b480100004500c103041072a5000c54000341c1e030100b61760340021030244603c001400d000d80c0c8641742500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 125557068 1250 125555818 125555831
    0x6330a02160b041404090503030a0902040506010f020c060d11030f07120c1709010f020403061b0306061202070812041b090b061e1608030403141e220f0e0109 69
    0x15900c0303030f00450280766014105103d00b401e8541c0d40d0740211408036002015203580381802051100180703d246012409503040000003040d560161803040d0032800250050140401e68108100b680c4d07000c41c7c00e034403071130707540340c4280000703460520165110f10071243c0000c425050004c0040d203000f40e8103014196850405402c0c0118590009459507003c00d6002009940c2d00da4600c030074003404240c8241c0c00310b20305c0440d001042c4001d9400c51a072010b8001c5184400120181c012800c1d50202d00503540070562602c000b018125845d4014401ca501070f038100c0d4144480090041140d003810340d000d883e09102c4444e00c1c85151000c40010000340721010303042000090000221303007240a1004c1d45000b261184420000c4078220f0812108806034481035000007104900e070150b0207800698050303000422845050481100310b4044801c035200d6120b0100002000c05890b02456101d5490580000d203102010b641421310b504048003d00b690445200a41d42025880c64001205078001c0028074240103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 125558318 1250 125557068 125557079
    0x9091c09030c09021e030601030609020a020703030e0f0108040f080d050705090310051005150c01090b042315061207080105090d02031c05060d140102120108030702010806330a0216 79
    0xc1203400115001705502e80340e968850041e17005046a9012107016400014000506580400c00700e050b2486601c1d00004070b005071041c4603030081c190a00c43e0105011901040200342c07014513220341300c0c0c071031155140342c4190074022070b00355901655224007050b00032030000400d00e81801044100502c0340003c02c00c070b01d0b012412690449103441924095040016851480d01100044682c0035080000902801d503c524000110080c00c030b4058500f1500c000403a11b824660170002c0c00b081000000500714140303070789082d10034000050300c46a80032301241c001d10090354090000744000c08641000041d00c2c03510004c109e08080601d002e41c0c007190000c000113010140f80070b582c01e45141c0b95541c00078142e900c40020a210118409000e4070800407501d09884409054005108a0513001c8404405990b15822203541e4010010002d000c2540400060720504055003c10390024121500a980c2c514039010740318052039903124181c1448002603d000f1280e01080f044802840d14080b10002c0c82c03a10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 125559568 1250 125558318 125558347
    0xe0708040b04030509241803030a0210180501050a09060e01140f0405010b031204060e010504030809090a0b0415030506061017060409080a02010b01030b09130209091c09030c0902 78
    0xb8801010f0080110704055151240c84170b022100100582c074046599400a0b0485a40c104860345040580c140c0118100d0f400c0110940b414404540c00070030460780051503002c003401c1903945281410450345484000300340240070303050181e10a403000083c520710f2410150203407000d450b098000c61381400d00070000d200e40601c541c0e034024905003a0540c0d075143e03454901c3c050100c6100559252045810036034003101d10500a2089a42035195008401d02c6100151054003c500c005014210184400343c101d051091256510103050640000e8242c080e000140450708401020002200c10110500c100142001b1903500004c080f0785429030341540c100c0051141507410303c036042c00f09036a00803900d962219008060318940c0f0036581921442c0c0751000034000d01016040300e0001c0d05140c804500f81c20103400039030080059010107540403c5640900240d2800500090f80900c107024011404548050820403842c84c1d0780e86000c80580346017800307442e00d115508041080c5204225100c00c03071161 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 125560818 1250 125559568 125559571
    0x91a041b05030318040f06060203030f01060215010b180303041404060f0302030619060e07050c0d03050c0a0f0c0606091401090b03030d09020f041508010e0a02060f070f0f0c0e0708040b 81
    0x1c602c40011300c8003e5001003406444014008440300e4105040801d1441d00403000d10b100d80380b4400e0011003070faa0f41c06c00b00c1c0d0b16160a01c29500c101c0c840001406003400e500b000b0903200e140118680111607a10700400e00d540c0c41948084866000f03204844401e1526000380c10060040741071100c000780c01c6800198580402070403c040380b0200050010380d81919410405c010040c041c1e00d0010380c600000064240d510039001d0120034060902d01300304082c06031041501500340129100e040c21981c91040c0d500c890307518100d0040c00a40250300c0700080345030146c030000d41551140407071400c80e0310b0f001c10300555060308400384007401c0c01e003c00919207000007651400e5858000100d28002c485c0049142482c0c6d20708025003060412041c160b0200403035198108a0308038100800820641c00000d60300c41c6500d080c0254403400c1080300003034a0303c1200c041d101480c0134130494034840c0301541c2c1b00300e40d101011500311000360243c10200300c0420144180c603440b45860903c8140d510342541d410400c01e40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 125562068 1250 125560818 125560837
    0xf010c05100e0a060609090213050907051002150c0c0f07180f0b03030a0903030e0f011403090309030d02070f0b16140c0301090506041202030406120b04091a041b050303 74
    0xa440b00c50303a0014808004060070543c1103101040019160941c02000e0b00e0f09071000e80c0201a4081c40c1c1d985040584505441480008080c0c41c107542400d00700149802c04800c80d40c110312a5114080c005e417041c0407164011200c20340f4040e80d820034104e18504101c00e06c541c942c81b43d0081c640411081810380300c0f1080c50400d2a90002d80d0300034221b100e80003042c42c2000650103210200304810b590390062080c0044d60b000e51a81202a0980ca00304106000c070740741014001603048000d20898840711000d1a04030840401741d0f0305110b6020301092520f81c2e031102100041e400b806003040756502d40321140c400740c90308008181c0340c9001d0710a01400a85804070090191100801ca0b2001410601100340f1046004000707118425860411a81c0c0e604140ca080d00c041c0e000031440c408080c00003080f641120421f0b140e0349185010f41107c070009003000c001c480d4100d51151070000000341c2c103464194038600c5000040c0a1410182031415101008014030122111148018001580e002096515008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 125563318 1250 125562068 125562071
    0x1e0315060e0703020f040906030f0501060504051306020c0a080f031602060709060507020d02090a2703020d0c03210f0c0306050901092a0c02090702061006050306041b0305060f010c0510 81
    0x44881c4079a1702c074070039580710a8180b46407480110405c050054030500f0b15008200901582e51103804100c01c80f1000d03500c0765030b074184c400003060024100740c001d4140a20301200340e604801107078640954a034811070701c942013100f00004020903108508000007000e0010310090000d4608910054024051405048180300020601004640e03400c00e0040c003c55018185404c0ca0070186420000340c4805958681020708003280c1031010288060500522501a030003044001d08010003510f105044090560030009030103aa00301580c007440c2100001c00402400141e84000d42504400b141e6180c2d0041081505180302040385030b483d521a203040d1540303c4000a804103007407212140c0c90744101c1c42404040030b6850052103c5810064201c40f80e802a07501c902c903903940d500c08a885000450b90f003112000008424083e841c413450181d42c3c8488040c100082e1840c0d14044040b05200000310803000039160300401030141032090300e10410200a090003d942011580c2e0a91a10203601b83c2041e020b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 125564568 1250 125563318 125563327
    0x1e0c060714030d0f020405130b130b0d050307032d020a110d060905060105030c0a0f0902210901050610050a090b09010309020d0807020108010f030f02040c0302041e0315060e070302 79
    0x1c9000303104031984480c10200411040c243ca401c610042e4205116141c4034910f00105403400d0031442c0265600c81500814100d0000030061071500184400100181c100f40e84111000003e081003005050007800703030b22902d007054000280711180b00d80700c14044000101584901c0701e110303000a40c0d0840c082e44020300101d220741501c08201413461040000d40024100a0903005020300451914107031041501a250a08100c0d400e215000c0c40d01e12503000c0c118200c40042048003850341c0601215420f9100c0e040b80c21444019100a1540540d64048640d64401c10b22030249416055807114003164140380d810031003a002c0c044c109252a01c02c445018000054a46003607101e580300680c01d079401005072044c1d6110741006240381d00041c004902192003a0004604014100756003000c03681d0000702410f01001503800e0002074059240c1c10f806150b000d00001c9030729071017400324814940d1984021303041903145040904258001e0760080107800e01c1c050302071100480002d4440ea2001080c01d0240e80c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 125565818 1250 125564568 125564603
    0x150c02030c031603050c061303030305090705130f0b010810050405041104110c06010f0e0601050a0c050628051005060a0c05011505031011041e03050a051e0c0607 71
    0x14030031641091540b6000c1c0c9648080d4580440c0015815207000d2000c5840180100007400014820607103e0462440c002004100280c4a5080154480640342c180da8410782d0f42e030045a904807440c1c8040c0c0e281610b40c021060a40c074540324910340c2c0030091800c3e0800341130031202a0380d1541c10780a458050358a8038002024030458a03e41304d47c001c0040c0c0104204450640790790626040700c00500120301400000003042d02d03116240340f090742e00c1c111140f80e00383c84100040d202071f84040034110510140b042d404002c00c90510810707114042000b0312580303001d40c240c601e036000e00310b9030a4010124988002d02c000c0e0005460b464054071030a03501550384125040013611000034800d40282250300b80001410240310080054046a9040d000c0350302144440324450107459031000e400b49040c2041c0f00410054010184a40c06840e4150400843d69100d441f002d007408040602030303585a21180340d400b07411025140d904200c1440102800021005c0c0380014090700c03407000c010703040e8040c800a4424 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 125567068 1250 125565818 125565823
    0x90109150b060c0303070c02030f06011512391704030c020102100f0606121406191a0a2a0b06060d1d06100b0306060c070521011104150c0203 62
    0x2a10710f900201ca403a40b070318610051503074a0600040303000340580d0308981c59210300007442505a80045944103011841300001300d03051100d03804000c403a981c9440000888030801170f5000b108050b0002e40c0340c03807840d0215209903801403261052007040220341c001e0700c110150241d0550030903403606c0e006030407403500d0004030302d0a03001c0b81c0c07408900b516207203999030314010395031044040720415183c4811580f0065079100484100700500d20f10000000002040c6103014021000e110b0211255a040c0c1c5444080003810000100040f00400c0300018207078510540080700544581401c920000002c091220700004800f51290020850321198020072a580c1e1400140d41d46846981c50802c00d0f086480c50030104a410464603071414003076a404520040c080c2130041c002c1e581080d0845241d91640c0040c000640d1042c07410302c12900454001050356a00c80e0204440315010307008070041404880340a9007141e01c0f008540100070300c05c02042084000c0d0140201b4442d4150803d54010031081c00420b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 125568318 1250 125567068 125567077
    0x9060905040908121305060c0705061302032401080705100519030615020307120206070e0906040906050106050d0f0207021c11030106082506201504060c0206090109150b06 75
    0x304c00a0300810010071508442c000601203000b81c0031524243c075110000907484c4690310700507155421160018181d4006c11030410549440502101c1d801401e14000ca01d800544400250042603941c00400581030300700008009040100e403c0402e0900c41100580a4801e000030390308000b8004c11807a00088c02544104000d0045104420480580f19802501c035400940700715a010104070000820510005841e440748100c3d454142980075170b4002c102c00100c0c014130050f401502c4104200010b03120780526030081010307840301d40e10760215420340380030789000d0780b01c0462080c8180300303000243c0d45111030040000410040401a00e017107040003001050300c0200b2540640c00c1401c001941000010303456030100e04417920030350402170200d11071803070f07142e0b071182c000003515450600c0224001050f02d0728059064504230750040c43c403001d400e08241c004480680d80320369541710290503584c06210465010409000811000c2860780c1c510801c12180c0100300b041c2a40c840c00b402c002c0e181c880441c2d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 125569568 1250 125568318 125568337
    0x20a020a031101080a1e1109060703090e090a1106030408070605010e06010e0402091525030507061b021c0311040f0f0f0e060402030a06031a07080709060905040908 72
    0x84481d4507070422201030940020201c0c0026040380014003140382600c1109446c02e0320002d403000810740185450090284860740400c08241040500241c3c0e17a144001c01c481c0e80300303807609808189000300c8140f0a40005210b56890303048094944c0004090080b090303154482114880d80721784450600000394080c11400406031403a000c000709102072060303040d40c400c420036600d0000d6961f000c0309003c00d80c001d000c429500070112136a031241c840b40703000c00b505120b210318030f50382e031406090350241c003a0040f003041c10b401003580041c950050041e14021002500415808001f0b84194414002d5039440c403800e0ba00d07080d084d2000e14044035846908046d0b00d2050415600791110746415120440c0c00407845480b40300c3d6142100062000c50f04103000c01151700341000c250950361000c3c02d00003c0d50000b89040f002681c2c40704040001103503140c5800054800e81440045450a00d034080c0c0919409403061090000f1840c007081500d91281600c01580d03016100030030300e4002440c110000780120440c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 125570818 1250 125569568 125569579
    0x2b0504062f0f060105010207050906040c0c02090403030b040b010801050f131d070f0e011a18040e0604020a06080910020705010605060301080d17010e06190305030d0b12160312020a02 80
    0x2040815000209809500606401da50f00e990341c1d4401607070f03201064801d0b10340140c3c0307000001d242c51403e0781c00f000c4440c1090400206000656001034002d1b0000c480031000b03e50344941048031820903200c0c8200b140310071308014580e541020000b0303040c118024059803003811a2a00f2024080254111350b00311181034886444084005641548a003a140100c078001410100c0018219922014030b9040390f2500c0c4141700c02c041c0741740b16800581c0c0b042d034a9103070002c04a0000d03034083e10303948204c10750b00012001820060505104010207200075078071400800010109020100d20b02040e442d008004070308005a4a0a0b94681b190141075150300855001c2d0380480001101c0e070380441d90091701001540c83c0030084c1d00c904071120644000313005401040040b10002021410020000e507011142a081001a0766581e523545140d50b1001d10760301c42072900e46072010041d0800844a580205403d005070541005003103100030740201603c4081c01c0702000166420790107000740301e618107040d0050034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 125572068 1250 125570818 125570897
    0x1101020f07060e09060d0803011a16030302030103021f02070605090a030b010f03031e0203070809030a0f0809130905030d0528091205070c030201031e020301082b050406 74
    0x1c1d28107068420f21601405520f0300054103490a0f41501035159808030300c042c1181d0030b15004101651620701480c2104200300510010f07000800000201c151003507801698940c1144107000d074049117030400c582104092070340f41c071340ca6402045520544030140b80c416200c0c1d401d400000c0c10b500340ca601c007a0205003020f00200d000c40c6001d10000c1a01e009840e000c1100c0604004508001c1010b9102c5005800501c5502c001032519801012405c90080c212118810180c4074401c002c40082e104650800e40090214100c2c1882110f00c04890480d20301088500840d84035507490307205500310341a00c03a903114005991000f52210340a099055030464401011000140000a24003440255044043c43c608618654411012a03c070942d010308003005580c9983c1c0154042c0c080381030503000780d00d080f00b1999842d06151000e54000e206c40390043c01000500905c071459009403404000400000060044c850ba8100007214101d44462030300c8909062061001110405138800081c200b402d00131 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 125573318 1250 125572068 125572079
    0xe0102030103050c0303040815040c0b0c070305070602030c06040605060301110c0604110f010c020d051213050907081b0901020c040f0506030115050d03110f01140403080c040b071101020f07 83
    0x1406107041c0c0e8480c0c0200c40029145008040c1e07280501e03c902405540701148941c4c80b2071040400d9034000c0d100301c103012022503d5620040c0c10340c01050b01311003d580007410400501c0001c10440c8001c0045001851034401c0c034108064170340e0001440a80300b580c4400119440303890960000100f102c2d0040401d468108108199031100300544080d44ca11114945610a0349004243c8032480007058403080c003140090703401d0048116412800340c92900624000c8040004a03000078590b00001c4084045581d003001d007000a892006096482001042030400541c1103502400c1880c96115081d02c070344038511040100d19142810a007075070814242545003080101a401050141504400920498184004102c1000301d24810b02e41c1c4001c007105c80601080c0a18117000600e05440c041d42c0040c03d44401c1542903032141c2d084000501100000c0009160b4040c04c1203400c01c00c2d218202d4541864000011210f0240d80400b0301082d10170100c5e904242c1c0200b02c5500c001d5503402c02c1d110040c0c0c1e200d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 125574568 1250 125573318 125573321
    0xf04060807140313031808060106050c010e1b1507050102040b07050d03050c0a050a03091712010b070f0327080303010f14212407110a0c090b130e01 65
    0x295006404200c1c0b00c10740c1e0340c203002581c042d28483c0711503000c850b1101c440303624121081c4a120401180c20b600440010644201c14445a80a4080754660725680c45404400703e084918070000304045130008003030017800500c007419441000804549074021040d1002d01405ca44c400d40c0f00041956100150006d5803011001c090300d03026000e04d0a80f101d4402c041c1e0290103a4004545035040c0604c02c005030060107003e40040d1860680710716002968402e503649800e41000559440320989102040c40d90010f01101513050141203a03500b002d0070600203a80c0c003030289032078807801014488542075424070815070001c2042034542110381c0c244455964560340703032264400e0180040c104110752022404030940217801441101c06000d4031544024117600314003400c942c81002c0214020300d419060801c1688000c165480804130248410f420804006042400c032005ca4901c150407600802001c14008580a403c442d04180d0104034800404000b407546080000c0d84901189003030940000710301c05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 125575818 1250 125574568 125574571
    0x7020c04060510080a0f150801020d0507020d020d082e150c020906090606190806092d09010e01060308040e0601230702030c040f091a090717030f040608 67
    0x261410400d540d190b40900440b0f0014240a8001c00c40140102e02010225480302d41c4520303400ca80040c50312102050014036821650001049a40228042441d11002d02c1103c1d0005428002400d02c2c642401c406074540c000030b2054814040d40d0350001b10b0303940031b500400300464900050040c5045041c40b41c00d140100c940103441c0d80c80784107070202c01200cac005e0b00610305c400d0300103040280e1070761140c01304911090300905480d00101c0074000400c18002e80010715465413510746500c20381d841c0c00814804600c1340140a02c070184240b0f600c2e000354100e4440300b49440c0c00c100039803800e130756070b4101524058219200d4181696103007510000c180011800031700103031080203503010b00c0c0e5103c11004490403511010030994101083d15075000f0b04810300c0c02481c525102a054503004825200000c0c1100c0116089000031512032582d50104a00e00c3c03052500d1492032000c01c1050300780b841c4955561890760203003490901d241c03000e542549100700147d810481e101454999142c2d158000180b03c1d820 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 125577068 1250 125575818 125575843
    0x30902010314070c1a010609260d05121b07060c020708030309030c0106080304051c0c050a0e0601030f290f1f090f05100302071103070b0331031103120702 68
    0x180440100800c4400c90805d0b0704070f807e01d58408070024101f100e140c080b40810001058030398203000c0c860040b60b03c144030030401e204240d19043d446030f41e860b15000a00d00d0080001c1d0700108008140000e00f0091310555624640010001589809509080c0e161103030030b4015150314072002c4100907421038000f0041924040b0a4001d2100701da407802e86680e03a005900400d0b07400448201903501610700d041c40d0400781c070302030b101e02e1814554600c0880c00c00b5196800c84240d04098008001c110750701070041100c1040340e2001000f04012281d035840c849517450340c065540304410303141100300e5070351300c03400c000400001800c00c2446c4141e8199401009030b01d05281b000f10700128400030700c220000020200700c0b0300c040c20b81c40c001816050124000e41c0105812201e056880c80b00055544041040d032000c0d020003804296642040d59181d132801078520100070044504400c003a5004c1d04a94890540960500782031560400148186007180103514240c0540103450041100304ca5001031911203206 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 125578318 1250 125577068 125577083
    0x1302150310050901050303030f07180f150f080c0d09020603090109060c02160b030c0712020615040b1503090102070f05070518010303020615010504170307060608060f0106030902010314070c 83
    0x1076642e41401200f00b824455281c1c0354000340002400100101c041c01d60140003032901e1090001c6405c1d110b802d40500c1e4001254440312500188502e100704440b4111481c29400c12030b010100e000d600501d003040080c4005c0b8501c0300441d0300402404250040040103a00800305901c900d0100d524600902001c041a50801d00703100402c0768403400800c0500c805129610070b0340c10107003001c810081551001c1c01290036035a0800034000031503807030400800115216805031515003080a1407503035071904d132440f01d84140d02d00385102e0141d98a440501040402100d03106d6180c3e5100240030b4024043e010313000c2d004c04000c0420b50200400843c0200540ba01103c81c400042c0800316020b10401c001d000c028050f80c008001f0540400002541c010100c00514005261680307881e03140d00c2c001507032240700c4e20710b510100d044410040da9015000291624074020701d070a00c0e1680c0301c060b00460601c144000d0590340c0c06001c0079a40b10350801d14000c00e071054100c00030300300741000034022500f04100f5264030b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 125579568 1250 125578318 125578351
    0xa09050907140102060a021629090c010e151303050a0b0a110a08040f060f02091203070b0402060715020318160807060e031005010e0711010603050604030813021503 72
    0x14030680803034140c510b0690051031a80e460440c5100250b101007080150459000c030540c00040740703411880400f4a010126a002000101c5c1d410000c000160620006410045003000c199030f1200f400d0b00403081c125001ca800005550520b10280b09600c0e0003074000320840d03404001d005000800d544440c0c8584c0d81902c1c41c2c0d1750101d00c00110360080350300604184c0104140400c083c410200d00340c1007402200104042a065915481220510000c0a1490340c011503c1501850b08218000c401c4040002a5180103a240d0b600035103001c00600080c42402c3c0841d1050512468800c0c203e0303d070082030021580c03810700d03035461440d0b10341403150b4070117920804145070064584424440b003103030129001044504d007040001d481031508400995010310079020384e0703001d844142c0200c6000340f810840d0300d0024206020010520100c00928103860713810100100001394001031101e41c07107a0585003051040d140d00360043d1141d2480c0101a40c05103800d26030403120318001000354040d80404034104d0310f6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 125580818 1250 125579568 125579579
    0x15111b2209060b0112110711060c1c030b0307080a062a020102030f0c1306050903030702030604120e01051c020a0507050a03030b09010504090b01030f020102010b0a0b04050102100b0f01030c0e0a09050907 89
    0x141c0d0759500b46c42c003100d0821b011301000030f015115010420700c8024005410300c000c8401d518980110884a413400020782125486240c2e01340c4188441d0300310541c0588070745400c00c2000e55482281000041000e65650320034560f6031881c8818400d842043c1801c07910412038104000e000c1e4105440054480c0c00500102d00703030b642104102c40c030340301c0c000f007603184031500e403400503500ca41101c4a40342c2c06010420004005903070034015140f0a81c41038406038800b00320f50b20020b000c100c0d501c040c0c0d130510000f08a40070f51804105900c40a80700d48110250752134020300d80807196405100c5000b0418825541c04408058140c0c0140308494030070794801040341e03a541d00700320596030311f4507004d0070480400c0300600204144901401c035a6006000100382c001541e0040b803500300199111011b0280c0c045000e04c40c035030f414068402c0480b0900c4042c0311140a03a00022036070001c81030380d6814542c0d14001d813201540a444040b28a110050114840c15a55404030018010807541e00072030f4002c0741e102240c3c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 125582068 1250 125580818 125580821
    0x108030403300e030c060c01050f0703020a08181504300905010e18040b1801150b030402040e0111040623030c0c010f0615111b2209060b0112 62
    0x212801c2ca1060100d03210b1104010760300031082201550b0140105441c000c806d840304d1001b0b00401c0080d80000401346411b14a10100c10030261000040500402100840c1648800029044084940300401401041100701e10704001a0584040005480c04200c144800941c07140610b6003091210040d060000c03041a6040303413880e480e180400d81c2024140400d501c070f80510284075501401000703021405280b5550041c404030b8080310811811820841810768180e410380318045000001c1c040c050540003544c0e0300304054040c03010000c0d000710010b019076445030008846610b086008024800c2460b5115450790f110740928800308801f8403040c1d5442e51080741c1c9080e030000340c9000c5400c40d2114011101d196010740c5182e1a150b482c0d880e5021707031194611a041c02090103110b802c140341440d0101030402411410001c0154101000d4440b5645c480d95100d51000001c0340c48401c0440c030038408005032900b00500220071071a00b0060720401c52140d004184001003601c900c41980c02c01d401a40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 125583318 1250 125582068 125582123
    0xa170f1015030f1823120a050904062903060a12031b061a090f0f060a0305010f0911120607031d1c03241e050d030306150309051c03090b0108030403 65
    0x15003a46c4094110821140307660050580c0224901c1c0080c501001c0c04001400c0e201c0c2604074114540295206074802da40b80120000c031500706c04005800c40ca0a40009104909603120b0303903411f00364940f10302c010944901c10789281ca000b1050800030000745801c00800401d540141c00b944a0b10300d6000610a08c0d11444d46441149001c0142a030381d9100246601040c0c3d016025a0704146802301c04000104203001c0c0c111520043c84000441000b13a0030824001c8081c41003680c040c502001c4600311358078000c100300707903c0895030030b010480c40805030b482111800400e2003048079020b5030b0401c9403094410020b8070680082580e0503c202d450310040025988214091000c04001000b4100004030002c40340c002c0808034a00a1152982d50340040382148406800440000b581ca29007406900700604082d52008013519081260f8462952015500c0c481060a0580726624291461340d26200360000000d40fa8003c141503020f5030344401d0165242c02c14003003280c00300c0784403541c111001d40040651 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 125584568 1250 125583318 125583383
    0x207050604050c0609030316020a03080706021201050607020904030c110a0e1608091504020328060608061603150b0a050706140601050403060518030a170f1015030f18 73
    0xe48c0b50502c0340211a540e2011140126002103115800001203444813000d4225a80218000b42e996a0071400081000304142c200d07511601c4c1c10700c100b0380980c540301d034840e50003a0301d41400185140c01c0e05041c41352034514285150b000000b0700001c18150304c0391400c42c1c02103c6840c4100d0a91446050a903007100d400c840080482c1d00010421404a441d5070005400c5400036017950310007060540300320a001c012000d88860200080d6070b1030204151486490024105480541030504000d0350b040b0000c403402050004041c0ca9800c45419070b0300c0c0c208a000188110300d00345c1d5494403400c00180c0702e900044800e4038958500f4a00048032190700c1c04140c480c12059403514a480c3c2541c0c0d40900400d005810030501421900c000384c0010401c100505a000b069150310120041a01011030700300c0c0f0040a0700c000ca100d00042c801c001c24020b4500342990100904035452900260040700182021029484001c4c1041280c1c00e194160003140b2227a1409200d444014480b45000d180c00d201102021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 125585818 1250 125584568 125584573
    0x2010e041404020603072106080f0a080a051b0a030801031e0305030a0e010b03011103090f030405060301062303070c1a1e22050607020118050304051504090207050604050c060903 78
    0x50014031303000b402107512803490b0a2045201210149038411142c2c11000054107982d680c0c002e00003803504001c12043d003401c1400404042681e0b58440041c1e000e000320500c1400004680841c1071280041c0c0520a82c2c1d50030b0403a891035606040c004e10881081c4004d480c1c0344508803c416000c904040811201ea4040e203441e441c40c2c6032960040b0007000000c03c185025540c0e034944240d42d039020b000744c2c3c0c0340c060a0b03103010781c03641480c0042d6801c214032448003c42680c02048100300d0350f00c4030005e481c111040750400749620120320351b8100f42280280d05610500b400042001440ea070001d52082400d4040e0720700b07404090b42c17004001000101aa180043e242000610f80b000c0c482d03150105510081403004000301c0f0b03102c1d040c5809601d00e00e940860b500d03044a410401311603824801c0d80c820b0321687c020340c0e141d414940c503041d0716032085020711030080c90601009404032030018101d50003019800011941c9070341a051242c2c460b201640d044400780141d0803401074600d080702c01c0d0355045a00402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 125587068 1250 125585818 125585821
    0x240303070c060c03091e080f0f12090a0e10060e01050301060804060506060d06030605180d090603090303060b1602010f0201051b090307150c0b0709120308100504150302010e0414 78
    0x14103684501410104a0800042c2e01c0013041d10295490059052252074525000c107e007801e041505222990103090019480350100070b000100000380318401600810b2072a07617407503003400410211101d41d08000f00003c1c07c1818402d030b1603403503140703101180c1c01a55181c0800707200c0c10046032141300a2140200103901c0c1008103010a295601a40d000b010003401603152030042150714003942c3d081e41c400e48545503140c04120451150f66a42620604d100e40645800e20345100c2c0507001d0743c1c1d01d004031810103a40c0d00d540c10805000f83e02180141038150f05841d05d07880245a40a10980080800c0303000410420342001207900502a503409007140e1181346880f01e03900e10904000780c201e40e07400f41e4540300700180040d41d1509804a801c111140d0340e5811804201c50400542031880500960b003001174805d01001400c41820b03658a1046e403614181c0240d0302e602400b079680380017a400007680300341340104c10403041801c00c80e00c2e011a8401c0c1c84000c007801004042008645103030429078503400c0d4000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 125588318 1250 125587068 125587079
    0x6170601030218030d050d0501050a030f081c050423150105060c010605090106180e0c07060924061a0903071509030f0f03110c0117060612240303070c 66
    0x801805210701c40c0ca41400071094040c3c002840c0458143c80340000c00d00006000000d40041e00500b80500019a410100e081c42e41e613492000c0b0386640d0024041184c080b030044248e61100440c0d80c803c0c01491820701403801d1a09240040101214020a0041d103810b0751450103034020409803c0018810b0f524080c5a00e000140100e03039000311000852550795940110700d654034070805d00c0c00f030030055032918a00c0c60701c00038102145c01c10350418520401003400b0000309102d104121741034070b5404100442c943c0c420b89000c495980ca024440d00325a108440c89601403060307039121904079145d0311320040c0140240d030740001651090038282c54150b04038141c14000784a0340f0024140b03900c65840d01c5034481d5502d8442134003040529004a0359400c0d004401428143d0200304508100d60141c0a4600c8125440021f400000c45d58038440b803c1c02d411002032416030700d84043e00d8541c042c1004881c2c452801035002c640094006500030105d0b41c50711518046401d0010036519125400103045010a0605 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 125589568 1250 125588318 125588321
    0x1090203070b0d021b072603030105040b120d0f02061b03040605041407030305090f010302041206050403110a060209030d0512013f05070501051e16081902070617060103 74
    0x1080b03c4424035408100e907022281214800380a10000c103030181114904064082c040c5c108a040d070103441e002540b04c0000040e101004070303070446000b210300003006050078011425015020a103140c45009405d40405816000655040d082d08541c0c2566101d0340c82d003001c0b0030f4015a0303031036910004505000180005501d540090340060085004005a01d8801121450005190800c42c00903a000c6421700c15401d141c1400418a1403d09082d41840e042c80e20300b2541f45a4208003500407038a510108041c180241d48101c24880c0d0b000503141800071034140540a94400210a030003032003118030380b2244c14410825228000010307905c5030300c40e902e091105a0b601e4140300c0d0040d8070480400307408003015042a03a84680c050022a1503410b000d55043c0303541490100d40c489814040b00b0004c160400c500c070078801c0c1401400c2e5410607117a00c45030ba800c0d40c408100b00f4004105520001c0c0c131003248888023600c0c0004c042c40340d00300e500e0541c90301001c441c985042c168040c3c2c00d50540740403c8156009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 125590818 1250 125589568 125589577
    0x13080610030f0501020903070602070e011413090215040906050a0803160206130b19030b220f021b15011505090405060607120503010503010e0106030b070f17100905070201090203070b 80
    0xf40002601b04040100080c0c00d03d402a40710002513404610104688003444503006c4c01403400b02107480200400d200803460021840b1448000240d4443e000e4045503030b03040d401510361604c190400d84464890f00f2010082400b40511846540840000650343c500041111448404c4e1034900202150543c20301003540c2040c1da034580c688d4060324000c070340c201c0c0341c0000e842d54200402080402d0007940d01c010b0b0440f1ba0001d8201c1c0140302e00c1001280c0c007601d0811080302e00e915032030002060401689030f040203008003000541c041c400030306c1e9519083c40000e00007110481041030b451643e661404049080c165464001010810503c8400810b141c81e900407580a1400b61215151404542e644002c00d41400b5102d808250044018002410b003441205074a0040030004c100c03203400d580317a01da0103150003081c003030400c0502c5c103150004610901071900c0f8081c0b26034028926040024a2000f6100c1a01444424515100008840500c14050a00c4c3d0540140291203518281401c035940e6520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 125592068 1250 125590818 125590823
    0x1c05060a08010e0303150904050606060a050c01020f0408060105030d0c060203060a090216120c0b1512030f1206010309080306010f03180b100f0f1203030f05090313080610030f 77
    0x12600300c0015007000030f00981c0300c1c07000001e01550703032481d1011040c0502904904054010f142c0841000b00140c2c00007038140d0040d800b1540642ca03021001021204c0740329992842c82c940d40082140141c00c00d0440c060400c0e50381d04000d07189031340c0c0c80b1401d055565002d4800f600005120148202c003148140c6d00035501301801070440b10080b9169407104090b82e10220300c420a44d038016007114103001c0700409807511440946880349076089070307454030401030794003801c400c040070281e004072102569844c20305d401140d40d131400d0360388451003811002041d40102c040391814101000015800750b00c1f034801c1d030702c0c140d42c0314040d981940c5070000111124882c420401082c180c2d200629040c8a98101c1c820301c6451203066540c90340c0c81e008403141c0110640d40d01161326824610000d20076100c9209071142030f200d080c070148945c03040c5401c0840203070200c103500c000c1c6036187c41c0501c02c020301c008c001020004030707a1420840741d99507412800d540341002c940002e1030209040041c0000303042e2000d001130450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 125593318 1250 125592068 125592079
    0x201150b0901020a06060b0315010e010e0f0a0302090903030103030f030b0a09020c0703080f1c0c080f09121308010c09180b040204051002010b01080c030f1909060f201c0506 76
    0x226035603503804440e0741c0d402c182c0501c0070204c200b09c90389030b114126041440f0300b032800031015690100041c04005199009034441e51145800100c00d4580c107504400850f0001c10001f60703810043e01c45c9899900030300040d4001a201f1890503900d5010380164449114050000820b40703140011180094021030410741c0320f8011034a001001c00c9400016014650504600c0e541e0350798003174200d18194100f4901550741720708180d0320685050300b01d10041ea1204030300b440d0030840e81d01c41e1841802c0911400c4010325640300414040c1e40f1200d50400300040d030f140400200034110003644265a11039440c482e480186c00d101d2400c0c41031040340c0c0c0245e40001d03005000542420340f144e000400c1068101c10a00040c3e5664024000c107607442080d445c0c100308500c418a265013030080142c0f000301070061410200c100071014088042c04d060b4001d0840d140c00020811a0502079100e44010b840b140c600801403801da84625005460349a0407100780e100801600c200303030300300b12101c1009007000500895000c4e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 125594568 1250 125593318 125593333
    0x109120203031c1506030f0c0206010f09020708040b0c01050a0c020303090a1101020c03070b0702030105071b030309020f040507020106031704081b060c0304030803040606090504081210080d080405010c0201150b090102 95
    0x3c4c611940a005072045480100c4c5c8a006055518101c0c7d0311030403440219403100c401082045444070003041502c2c03000001503a606e5250400c5440d621980d0701c841001040000c421100320419071142e8051019120140010001c4c240c0403603a0340000c0d15001c43c95000f111a98000914804101e540c203401030059540404c0e0040000341040400d41c008180741c0e070000f134414118502842100d512081e203040c40400114214040c071000c40031804c00a090596582a02044d50b80f81e0161904485000f08248028070300700c02c00901800c42403008540b09044400480b0101e00c1101c02c1d58141c480d00b0380204562614441294054084400101d4028400b000300c10703403500d001d100520181d0300811219030740341054500b910845042d50301c030001e0140f80005000002d550a0116210310303407000d18034402a01c270b580c0200709480340d960004525100300511204007541101c0b80030720841c040d1300201300581d400c240681c01d8400040c5030344141d01d0014030a2042200c0300d8007600000c80184110f0700c54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 125595818 1250 125594568 125594591
    0x3030a140a0b1c110a031b0b1309090f06060305010902011706010203160f020607080a0809120d1a030105091f050105090403050729011806080c0111031c09020109120203031c 76
    0x61702c0c5640041d22100b500400400209000030701a10041001180003442c20000c60030080030250607024500c90300c0e4860281c002804100041d00414035004001007141a0350703031030640c0c0200381c0d05004a0206000060ba141c804120040051107000103801440c58407072803880258000400a00486006e0102c0301c40c0400360300d0300d10180c04850b10401c0c110b540d4480c6200040e00f240d070000c0102d00d0540c4601512511010651305a590010782c1c094081407106441c003442e142c13109030b1408036805610741b0f4108602d4050002d905084440000362084205840c0d85014056035070901410390401c00c09000304001078400c500402d0250701030702e01a901021088071950030603400d41c8401100942ca00300600c1000561200d01c000000304e6002003000710314044c8440d40342c00f540c40c40300e410711501c44001040303150140100c6409e024200204503900f4012140341c0c0090101d6002070307002800403803001c207100d200704500200d210b800500031801c00b210051400b04058064994400345521070068004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 125597068 1250 125595818 125595829
    0x105150403060e06100807080a241e0c08010308030105010e030a12020703111909270506010618030f060203070309120908060a02040605040314030403020303030a140a0b1c11 76
    0x1040d038184040d244ea400c10b4900f812100116410004480d00b00c041d007040f0a2100180e845255640302c1c1d41064a03401500d241c1750714007550110300602c41e082c00e50700d1001c08a00e860090642002c54010004c03500d1005007200c0710902400b0040c81d0082c1040148030540c0102560700320030741c006040f070302400792a940b044507004856a0507000350f440311400303008104100c01c40000c0380034141e80740720b03a81d160020241482855842441c8046568400c1040c0300c0600420321401c16500e055000e1450b03215140055a88200340306207000202030115401003c80d0042d070740004c80750080368034912020b19442c3c0c4002944003810240503d9135a203400f00020b508121041d0b020101d54464505a91801e04402e082450092200846520400060140a82090a9506491304400c00505c3e620144030705e00d20310f200302d40000c1d41c1884040100314140d4040d030405043c3c40504000100385445205c0c4000580d12001d6140307601008081c542038000c0f034501c42450215011301400006060084007080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 125598318 1250 125597068 125597081
    0x10509151e13210215090604060908060604060e0705160c06080f1f140a08060f01140301090213020309070b0a030f0513030207030b070e04020a03090b130209010515040306 75
    0x80403000070942c0030041070101d038a031006011200345400b101214240e142c44a03c20740600034400d9400580320035507560910240c513405e0202806840d507550f11024050b1400e80688582d905074410340d000107803e82800d019210484040032030081c0740780c8500c8002e5a07603030002c208a0300b65611a48081c80400c2c0c840440900500440d1034001c500e0815001d001440c44000b0b200da5800c0f004031503a43c0a10903083c15140445071604010080c07215440009520300e6002c0e48114024807555013845070010301c040f451b50495440d19030107022103414200f030500f80c400b4010083e5002e40040d0b0300c803840c1d00b5180c00071a4422540c0c1f080d03503002500d8403600f400030307000381aa80f00000d983d62a20040000213115258010b44035603107140240d00550f40c02903440f845800020080003003900800d401501071004410034a800070010b540b036101b613032801001007c5610b8151341801088001ca1400c05884078205e0302c858001c1c0c42600160300748018443e000c200c4525145000008202c0040411210711500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 125599568 1250 125598318 125598367
    0x9270103080a2f011d1f090501090501051603060b0f250303020912011406010c031803032102090108180c0a12110105030f0a0b040b03030a08070801060e01050915 71
    0x48111401c43c181503400c4904504082c0d5511280d00b0001d46480c40003e4442200c1e021594408090280f80502901521031420018450340c245101c1d0020444d06401051040c0e4a01c000d03020500e07644c5008070251078003403040a44030f090800203410203102003c0201002940d0302800f03c0055001c00680c0c0f80c1c21840542603000a43c041070a094520700056074409042220000340000c50700340d40200000400a480c4606004898088100b01801401c816400a9081b0030403030209a40b414060700030700080d115080300641c10348400da00260300e4801c0d1000341c0c030b060f0754500503641e0350348801083d000180c01d040100d00c92804030540307580d124001d001c042c0c401040760824403622858000c04042c500d4000b1418020107004001490242c2ca4440750300804008020840800076004500100465400071343c1501001801400391a041584140030701c0c5240d0350280e403030383c0e954000c48106a20010a60010740104040021031034608895800140074089541c0307042030700d6440d6440300d4140c1100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 125600818 1250 125599568 125599637
    0x1009061d0919150506030c0304032303070807080f1303020f0706020c03100501050d031d04020708030702160b1e04090e0a051903050301031212020f09270103080a 71
    0xc41c02c003200940101d14240d001035841089030750030007000500c5c03400010048000080c0210024041c18480c6490150111074032203a40042011a40b00300c005600454050021441e2100414441441a0310461141103004003681c0c807a2205426008164110082a0110b00c12024540c28032038062000000070902d540041c42c5d028455418181090402648908120700d8240104500c0d01c91510b500761245d031620f4031003d0f0b0711010140740d99a4484a07100c9800c0781c4003150200400140e4001140a007040e40c00711742d4500c0d000302408541c4802c600034039403c142c042c0401b24007844103072081651030361010306c094200703900d035910b40048525400c4541440d40c00442164103000045c4103600301405880000310b8181d00d552405800d511040c80010003803000c0408000429110b03a0011003002c0c0181070a55031b07008444109480e41d00940c400c640700b02c01241d506181030200445d08160414505900c0d030983c0c2c0703592035007042600300e91030303210600074040b0740300c41c01c0d0541081500200309400078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 125602068 1250 125600818 125600851
    0x10323070f061e1b061b20010912050c010e190b0903030705071104090b04060506031216060b0a031a0a1b0e0402030604060504020706050402040b1009061d09 69
    0x24003e0403620301014645400300036440030840903500031002e0180100014030107601640d5481c000004200c030010680980b002000c01a800aa100900321160740c21648217403014400b10901d1800c0b1114110000d1105012907601881503000381c2c00381110020900c000910498240380e01414000182c268441882501d8001700410041200603500225042e000314150710348401c0240c02c520405402400e401800035181c0c065a0300c0340c1000c0b03d02640300303d0075071060074a1326000303025190a407032045c401c2c01800c110500c00300c2e600007921144d0500f0705c03603510309820941300d04001f010000312480c0c201e00d40c0d840200100d0020704216010380b40010901c0396510b000d800850468807101603d0355844c220f4281502116405591500c401c44e00f241c006075a61101c6002800806040d80881c1c5c2050002c102001840440da0015203d640203030b40602103255020b08124405090503c00d10100c0c12034242440a68810b400c0c0b0002e512100c0f4480300c0404540000039a0300000725060301c1c000c2803404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 125603318 1250 125602068 125602079
    0x171e010f05090c040303090521100f0608160e06030f070b030601020601050a03020f090a0b0d03020a120819090519150b10050d0e03132301080f010323070f 68
    0x444807903000742d100c11494100b030304558000700008118442c19100d1740003200b034450f803615000319207161407030284c0c1180c1d94841e10200d0a0701504a0b8500e4900d00c610342280014007033720208000c4403050000c503240c12503501b000c100c1011071601410580c0c25214400d07105140400800898003d442205901a02c0c1c1c038200c000203260200507041940100c0010008000580b507510509852040460b0b0105055840001490082013004c8580749d1101406003c0418560080349231080180280c40c0f50b003804802c0031040d142c0003006d86401d4641401040350580f4801b60381e10640540344614255a50015194859688001c40c001d095541100800e1009841011761040c51107100d030544d00400a964280800340c4103000c0ca4000145441d116243c8048108083c411640821401c5407021700d05500c03a210201c0501d0605101e840d90300e00d08500000940c0a03585c0148105501e80310300381c2c3d40e13080d40d4402c0501010012101050a10302081d080d032030001303103c1800601590f21403000032a1621 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 125604568 1250 125603318 125603329
    0x30406150e0a05370e160503010f020306010806121002040f0e07030e0607050a110a030c03121104170309040e010209010306051518060c070801050f01090c171e010f05 73
    0x141c241e4030b045002c05480010083d203103132074003213210640c0c08120115801115030005000b200c1c030300d0100c0c1d0081402101c4088059881d00b82030b903409400030012602544007200c228401a1100783c04100c41c60002012481c203006000c200300f110006940c0c00c2044403241c50b06a800c01d03000521614100802400603500c065652980300b8064a4280100300d1080360060301c3d4200a00080100900003d0b0f0f0815140a030243d1490b50510404440c4044070f50309000b04000d01004003180064403443c0c40001810507405a40c0041e040c0b052501d150900c1c00014200044101512180602041c488130015558a1240c00d02310041071001682c1c800902000400300c81542d0803041c0303d000d803035100c0000c4030f40c0d200940d10071000203003c500b0701132503038400039009001e030b42609403203481101d902082090381900308500400c0c0d90b050b11107080c1d880e040c10030240e6801256030320000f540501c041402e41e02c1500500c0c0c1045980803452140c030071560b01409440d10903049040301340d05040e020072035030900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 125605818 1250 125604568 125604571
    0x180a060510031101030513020f03030705030c0f07050a060909050709080604050c09090111040902030a021e07030207051c0b070e06160c0e0603060a0209031005070e0108070302130902030406150e0a05 87
    0xd28081006d0f20f41030381000700c0c12403801e901070700807031507803050030850b07141041110007031900003040303a4803100c54029036030341c5560881c165105400303044c400041d50f04020100c182516034985440036014200450b4070002d1800608040c01c00100780000500c1d05c0d41401100e0250340220040c2c00783d01d10100174071900c0c100150090085070300d000c038002d1540743c12205036415a040d603640076a8030344070108400e0203801800300d1041007e00e268561903200c14824002e1025510940031b480941c0c1d5507800304801907010300e81005988940d5204480000c4e841c11090380e0080d92401c050501807040d02c04502960400e071101d81410b40c51704040d5050000e41e401400081c8803088aa20341850480082a04d81d04040c2200800c1d54005ca2890360a40c0d0600414034042e0003803100b048585014000281841f040d1800b840c08034140c0c2c1c0c04603407464880e000300c4070200710146a03206024070b088036100081d40300a0040c2d4503542d03503c200c41daa21800e000d01d0b4005001e619400d040070700344821400c044840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 125607068 1250 125605818 125605853
    0x1a0c160b04050103021b0d111b011403060301060b0a03020a03050a0504020303121e0c030609070c051c050f0406030c02070b040e010e150306070801061101050f180a06051003 76
    0x1002081061000c46011241641d000b0320340541c9800500540c5001c0300164040f008150040d0110b0761203041c0d010303c00d0205403c5040071074100c500c440341c1c40c01d048158004154001512004061100081500210b4000754054000906d450740e504007017020380c00c030558101c00250009045d203095980342c0070340341e08150166010081800e042d80001c5d42c030b01c5440018038800d400d503000100c03034513550480072140240c0c0710030100b01071402509142d5070740d204603280c80c4603086450110710034074815040940180d500100411602c20442e40602d8600c0d000340b80b00c01001010031084485601000280c0020b204a8401045c1035034680000b0381444e00540180141a000748020004114051021070441c0c01488100d405912545403841701d100000c014103030580324500c00e0260036940306d000c0504036185513545038612418616114243c420655071850300e007004401007601c00c0300010704108041d46a0f8100d5503031080d81d075140015030790202ca66149a0428407401c00c03c7c00701001980b4242d60 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 125608318 1250 125607068 125607103
    0x1606050a06061d150c1204090501060f090308160f0c0501090806040f03031104050319020406170a0b060612072a030206070c020a09090c0f0506070213151a0c 69
    0x1820380f10b1040181c18030655041c843e00c105803240d018000004221000c400c07141050f00c5003003914070250344955001d44216a00c0a05e01350000400601c2440e800c50414519a0350000d800c0ca1511910820f4020246400c012244a1400d03800180580300c09602c00f0703c55801c45100c0f5281c50000741030036260307900002c12600714104110000b18080410000c940e45801e000482807078005401940307001e2a040207801d0710440740e4808412003458608801d0078801c40701400200d84544088440852401c40038000d1382c401003030800041c1842e8540d5a00507000f078100350602800c107030982d1000703c0a40b0b1200114a00c150b80c01520f40c0000795070100d142101441d40940100b5580c001c2d95110300502e0070080002003100f8504540c0c0b4100c3e20300c02088203100070300c00880309082031001c0c040288503072412214504030000351070400e50107540d40305030001c00700401d50804415000c00751200a6144801001142c00400c4103201468003400b0840b01d024001e4882544a5809241090100f031a21084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 125609568 1250 125608318 125608337
    0x13080d08060d030f18080a12030204050f0f0301090204061205010e030a0507061505100207060320040302010f0905030a060603050c01080f010b0d0908040e041a0606120c1606050a0606 80
    0x607200c00b01112121079252610104002d103110048501c6445c00e030002400c10300c10440092801400150364010b2170080d2541481d00310300700e10941c100e00c034610565400101004001106103417111805c002e80f50054008a403660060780020100c1301d0541000400180700d0003a881840700902c514811441000000c6140c81c0f40090058004d015101000b014580c41c3d415070aa92061307a002ca000511020784510610454080041d485039054042c800c0020310303100722542c40c403080c02070a1002c03080302035401c0d240504503001142c646104645120501405040000d4a51000c01140075858040c103c00074129082d45400d60400500140c01810880c0b9a0180310305000d203120b500d4110b0f04000c44660340c5501d4029134101a0409101c0641000030104001a607141c1070041c0d03d00c120712803000030445903034810000301c0d040c200350340326034201c1c006000240500b1101050a0340250f40ca650042c1400c1c540082840842c864100850740291242c0c1070110443d018083c0030060007c070305100550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 125610818 1250 125609568 125609581
    0x611060c0a05040b030901140405010b030f1f0c140406052104020a05130902061206010212030c0a050d060b0d14010f03020102030d050c190816031a0d080d0213080d08 73
    0x9409240100e4000c541c002010685600c808d6000301900400206250814546070504c54000c099948025001e4041e5910100e01c02c0404079240c6000d0b0440d0315424040e05401072031000a003590300940c401d20205548030924001003001420040c9401e07550540d41c1c82c401361f000c81440002410350b82c4110013002c14007006a0b40d1070f040c1d6040d0b070421b4841ca55002500da5020020b002440e1000c1d4000d44005017880200d6155604184160002c0e0221281d060b0401112035062100311000e0400700401d00c40c0080c40c9110704010300c94204502e030041000c070f44401c40c1c2152a0300000c148404030f5911103002c1066640d00c0308a82c0140b8a04503036071001c51950300041d441344504c221714003a180d038450006958102541c10b4031180e0344102e02001e2011040a00a40356101c00d99800005101c000350181d40544a0b018540395a0b105007402c0039030301c00510901500c0304400d0380480700000301380040d1080030164805004401d4a00c40d0b62402c6605d003589003801d020016441d0010480484108000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 125612068 1250 125610818 125610827
    0x20c04020a0c030c020123090a0e0402011d1801080114060126040212060412020f0a020f01050a02010e030c1006090903090b03090c030a080901030c03050114130b06040611060c0a 78
    0x240da0113003054503e8030380310f10048907441890741c0400c2d005040010304085185c4841c01418603800151504040c181e25103070800c5219100300c900900044520b500c11481c0c841440103c002604050090907456118044102c1c1c5d10000740c10465040c2c2d505c0710164070501004040c10341203402030803c07451750840b0240d00b104081c9a122010000540d81000c2000c5407240401180020113410685050341864500305e5040030406c114580144240001500c22240c0407074003003106540200122041c1903450015299904035111200030b656841c80000300038a0148000c0c810551480c001c0d02c030114502c0b43c20007c440150700030901c0760b480d151010000a1300407149005640d01003543e1501c80c2c0d00c0f14a014a04840d10540503090b00990340510104281c0340c01405090900345c03800d200c406601c050440464030701f40300c3c81b80440c0d001e48600b6002c0c108445072080d80c0700c5400d001301e4010b00d00008920b031544035030720800001e40da601c0c034004048402c1c440b0503040b031580540e49240007042c280040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 125613318 1250 125612068 125612087
    0x150a060206070315030210020d1d03061302032a100305010b2506020c0102040609050402120403080702031e070b011a07080d020c0109150f020c060406020706090b0115020c04020a 78
    0x1030550b00c48904c1031100c8074602441c0196402040c0c00c1e0143c000000c029210280e03d50407001080c0c6444109103044001c50100f000380d10060028100c56980d110106043c18004400342d8143c050106240d0ba001601c61403001080c1600300052802080401804200c2c19090041d03410149004014401c00304404200c2e0090410001480f40c7c02c50b00c1e0007030f003103801c54100000b00900d10000e030101940c1c5040d00980101e07600c3c1c6d258034080c1c0360b4035410310040c0c0c0308550f0b110180140000026000a0040e44000e800c00b40610441c1d00f000c031a101c21050b264010080303103c0f50f60000c98102c0800914190550150041d484a00640d070192440740c4c00038001e900300101b0610f40800e8240c00206245d058481c0c16000344000e1000b0841400c18402021116040c600a641092441103200d5018022510402d8400380106880e41d51500d91300002d4004190884119442d648800042220403020074060314200c12407001c40d01c104000640f610304a1407809008900501c020f21180d070b00b209040303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 125614568 1250 125613318 125613331
    0x50f1801050d1704180b040e0d14041e0e1806040b0c250c0f14040203040507090908031e0c040605031005090a09020906030303010f03080a0302040914150a060206 71
    0x25001c60b00500d4224481004002840742501c00031800058400c01c00e40a40c0285554800c01c0090102c110b0601c01601c102c13001c1c0d22601c0d800450031901d014802c0450745a503021201044d800c01e510350607400078840e101101c6801520f080b490170300c51180590806500507548031244800c040061094544445c40180003620700011140000e0b003481c42002107a804002200210342c1805d11928682c100d201c2040042d1001c4010b550007040008025a9220950701c10380d5440c51007100c04010040030358001001196136010300303480007400c110140207031000e89100d014190b8891510302c2c8800310103408041d0388850540400144501c421000c0200c1c0c0c255007081c944980d580d03503144101c10020400f80d109540129400d400c0080c060641e92000440c01d00c01c46070000075480320b1040581d2070200380144140b0300040d0138104005403440000f00f001d00518240541815680c00d086800c070b50040201070300e0b03044414204040a421040f810700214811140c2c41d1059040140003969400001d050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 125615818 1250 125614568 125614579
    0x50c030105031c031e0501030308090109150c05090402040f05130b0a03120e120706090f08100902030f0703080304110301020a0804080a03060f15090807140136050f180105 75
    0x20039a007500c030350851039980001168081c40145c421000b440105030904c01500040d504001089038818103004400c4d00a4001108c02d0080c800c1043c014000c040d4082c03400140f100c00c200d413032044e80303442c000390004111002034039a26515100a03c540328080107030750218a031501c00d1002d950790340c1e0498281560b4008002090025202400ba11503811101d21158072000c443c00c40b0380b0f51440010b01d08150707103071642c07181d0400c1c0d41c807052150302199034010b030300480d00860794101450305154400264640000e0446164801007140706050543d140c00503121600d00004200510004201880050f0000d8000310f180083d036180081103114041c0004149010001b20110024869000b0030003400e01511042c00460741c5042e291818082c0d05240b20100d03950080c0000e1508002c00c65100319a9449450103480c90b90900440c0c01c00c00d0f0103640c0c81e8050104246405540151300d4000c100c2e500c026140e4406814001040825900800b480744601d01d5801441b245d103002068490450744160740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 125617068 1250 125615818 125615863
    0xa0602031006090e22020915010201111e0310030b130303180305031801110c1006090608060103060c090f06110c0a2102130c0507060501080328020a05010e0102040306050c03010503 79
    0x210481181c03400d0001c1d60240200e0300b032100031a0b030041e00c403402d403000b60020001d03030018101d4206140103e00300c043c0dc00d080c21010b007240f10000b02c0250362000240445980f000e45039921100860030a4a40c21a803401d1030f1400401c0541510038010541800741c6461100030842e50f005016101c01420b05640083c40303210041c9020702504400f00c0c2004d19000d460716250101c01803a590400d26201ca10841c1c2014000216041244174041c145c44211001c0c0030981c0c2151180c0c07000d0000c18074184100400410001440301c40a1400390260a003550358641c1c0d1850b200c100c601e0200a1001c0c10320402c0e1410042041981044c1d240220900324209040c8030812800000d064460000b2060945410091244509940400203245442c49240100100d0340c840d90210fa5a000b5401821240454850100a40e004061045411048520448442001942d04c540c25500d0710355284407140e40200717040c01000280c0c040d45a0140408a18609540c50280003a0380c996001000d05050f1284c80c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 125618318 1250 125617068 125617111
    0x170606040308090613050a090902010e09010b04060815040c080402030609010b030c1c080a090314010501080a020d060b0a0305060a24050603130803041505180606100c02030a0602031006090e 83
    0xc0024001b000e009007425861a03888107002c0141c030611034120b000400000c0354600c6440e01000260581d001401a03c2c2041d051050a0700c030514041c11020284055094900c00c0ba6105c1c02440b5903111170781d5a030045414284141443c01c00c001d042444541d0400200c041c19880025140c068400101c1d400020041c640c41b4045136005000d002170542d0f94001100104941c0000070401280e100b500241d003036008401045003220001c1c06086041e800c10b150700b90144c9411407a0102e00340c018080002c0c610b006100060740e141c42c560040f91a5040b42003048500443d61180c074656101201103041b407610903501c0001240c1640c09102d20650001c40810300e50203d81606141c419800120141e40742418108004d840c0c1500d8200070409081000003000c15400f40d594038080303032124000f04100d4940c40100319201d02011411070410030505281000342c3d07403c00a40c400c00d0302501d0016a00c0c100340d44504151102034000b0824400c0c042e40401c8061228107505910440e080c101102042612 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 125619568 1250 125618318 125618347
    0x209030a030e040212010b04050a08061003111503040f02030106090b01091203021f0b0301061505070b1b120103020f031507110c060a030b0306220f0f050307031706060403080906 78
    0x481d04214840510300c0080703500e0403258010802d8600480d0748018242d2f844500315600c0f001140c4c28020179400481c104005282a55040a41c00008000c2c1c0496400c00c011660a0f420803501947da40e00d400d0000415420300703120b9503000c0e045c80312003402107803c0480042d1030b600b00b0303101d101c2601e03403c00c810400741442401000e40c085403900309503066036203020920026020301c4204500c254039045000500042c010b14800106103e903c42c0343c18160b4540b40c214481400401c058164441c1610001801d10441c1c004c10f503202261100494030350450051000381c1c805e10511300e00030f03400800100c0d1814910344141c1ea000c00c4901d082c0380140c4245070214140760110740150380015001c41c2c88050141c241d0061510000107800b120460b43d10410108844940c440482807155101440c2501144100810041e403900910030351201c00001d030b0f18a071455100c010150700080300c0494004084024030360b02e07a0806000c490031420a4155200d4000034440c0c980c04c0c52244000040800402e0700c0c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 125620818 1250 125619568 125619577
    0x80f0c0f040b0319050d0905091609090507111c0e060a0309080f0a08070309110f0d0b04080912120313020d020a080f0f010204030c0312090e040f02040f0209030a030e0402 75
    0x140a4610048004c68800e00860300410102e40074001e207000e600c40c0922a880100c202e5400074200781d07041d16400d01800310750340740c401c0083c10030044a4021035001c62a00480e40200d001d43c0d5040c0703e403000030252a040807000c140d801c0031841c481d12032800142d800254403103009801c8400c02d0b0b5402911209030000c0c1000f49008206110100d920a40488103401a10400815407111020756a8240c02182180d4084c0700041088680380300000301420014582002d211010b0310700312804c1c3c100d0321039220f90300b8100d504980010001070280e420781090039981e00c40d42ca50a008003080301c03c0c10f230329803214007000300038445004804903143d043d0340d5035941043d100d03600900b107415010b80780c2c0341c1d6989401d0030003402e00c3d081c0700b1100f59a0110805208640131240c0000ca02c821031170442d0380d04008407446004070300401c00036140100300200d200410a010720300ca001c44481070300191051200b519145c0c0140c40b403a81c0b0500089942e030f10b02280c2c01c1d006942c980351041400c000c001c0001d009008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 125622068 1250 125620818 125620841
    0x60909190e010b01030605090f24041b02010c09060824041812020a03140903011104090e060a050405060609070210020403060e0c0a0f060804030c1502090406080f0c0f04 74
    0x8103070000054410641c40529030b054282da0a0288a4640c001d000701d50105403903614550303001a00103451400c40400d448220034401c602c4d14040000c1c0c90000f0155000182d605207980b8101980b4015141c092080b00c03e600c031a418100d4040b031800d08080d18841c0000c007142d0409000200c92900000701c10040042c844000744200586a07030741e0a1f10071980e4031100e04030f070a0129018450a034500014030a4085a07240d83c0310f00032940c002c0100640b541003510074136010b6481c1c3da03914269805220242003e803000382c0f000511413941c55401482c0002c003800f4000350518040c140000304001043d0580d000d401070750011510f80720f0301c504924014103200301c031449501c082404020411a60031076032605066200311780445546108000c84240c8500c5070a4410901520401800f030141002e19481406410040d00d0480f003515001000d003010b0b090052120750015600c003030f5280a2003042d0191003618001d00d01d90f000b0420003aa1401644083c0384180c240c3d040c035030100c0d50f4039003128025a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 125623318 1250 125622068 125622071
    0x90503120408091509060901030b0d170d0b060a120c0e09280b010503060d0f080307120c02070302030d030b0609040c0504030b070f0c0b07110607050a090902040506090919 75
    0x1c0e140c01d00350b2240d002416028898001082c0803401034075500d007030b80e11003500144076a18000711540150300420b03000c200a500708800342c400401151290681c5094400139081041d560321507884d11b682180e800c10480e52040f04180441d600641d40600b64803601c420007140002c1c01440d02205481c200d490501e40d9610502c000c003004144403614071010031750400c1801d580c01c00705c42c424168040d10280300149000450a0000905500d00601c007500c406010b801c0150f40d403112510380517202c1c0d0040b42c8000c041510045a002c03c0183c0b441070410a800070310140c80300505550000b62140000401e1004054468100210795520300b0210f4850380e400070402c0080d001300c084007600c02d42062000743c890810070800184d0f840c0c01881c02090141c030564410b031a101c3d203643c809000348006072028040000c10342400e00d40ca00c080001900440c01912010317155040c0d00030080225006070864040540148003c00c20340d192901071319002c02085460080c9a80c8a504c0340c0e00f142004500c0b4403585 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 125624568 1250 125623318 125623321
    0x70305030a090803160f0213020a030507080f060108010306020307050d060e06010f230717070c051302280e13020a03180210030c09090c020f07090506010c0609050312 73
    0x5400001030840c1d26a68580701c1c801651200c8030f0352a4010310320801030303140140f03034000001010090b0188407240300410b80110201e403161848126005518a4000310760313074009006d0481c3d006403103507030b01501c00222246030b4500f00c00002e00d112010302c001007242c0e4021021401503802a0161100c100501c2e00400007265504607003010707940b0603101c041c08215186441c408242c0300303410b80c1e458801c15080c5121100411070142c100c0d6489140140d900d45004080c00c2a0107902c0030040401d01e0107008c0e182d91182c00c2c08100400c1d01103041c13400c09844d104114102200350b009082010506c00d2084c0c0101907001c00c0e0003035614002c0406125445a0498190000fa0b04030b0745c041c10401f605642d007040079200f0703902c1761800010205030296000d0907010075800414440c0d040250304000030f16103c00581d80d81e50480e40be03503108600700700241c0c210180f00000d0311010030121004041c2810180202c0c2410400a080312110b641c2c00780009072030303403034041c18004100201da00c95011514080f169 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 125625818 1250 125624568 125624573
    0x1d1f0b13020711040612031d0a03050102090405010806090a061109031e0c03070506160f0c0807032009060114120a020a0e040614060c0a0209040303150e0709030b040302010e0703 78
    0x358418203049071450384401496190b030130706100c1c150640d5016560158001401d0702d0070388203c4e1410194030401a07500b00d03441c090342c9644202c14011482440090303142c03480d0390100000e88005811040650340460304009520f00d00113410707441c03190040c10006941024203002d00a620608002e81c0d01441100c1002c202d41e43c05120300707400515448140c1d00750341445c100701510303090a0302c559070380f0036010722148006505080d2580d400b03a211303030800c428075000380c0c4d6001c12400740c0e40c1c0300700c015400881c0d040040c4070300050441d5884803000300300031154100100045500d84091300190400404500401d4005044e0080fa1240e80f407072202050140341801041001e5400f21201400081c4042c01c4c20380141050b001d0308003034234042c01440070402c0c1003109009080d048401004054803c002007078026844100d0281c0c01103010b5500810101c084980d04020b10301c540d03000110086281081000e010f074480401000d60b0781c00400c600c4240c1761810103d02501c00000403042c0e40c00f454030300004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 125627068 1250 125625818 125625821
    0x8011409070602060c0a030b030a06090506011a09060a140d0603110f030f06070813150c0912050604020405040602250302060702010e0a0602070804180603061d1f0b13 73
    0x1069024004680080c2e490300d400703d80700c00060300c441e20200c00070700001d90700350f019800c07072020800058100c43d80140551611000e80710040001c3d00d46400660040c031281c51103201e404103260302001c069103095101d03000308a0724480d250040003080b10155024071002c01c0b000490700003004582090081d5900c0e802c0031101140700400703062041c0e0000d281301c0c95a04010500e60091900d4501522669a84c03e0301500e514500034002840b0049052050300041c2e44042c0e46142000c003490006240100c842c2c1c080d0001e41e141d0010106044881c64140000e1400908294000d45c10307a00440e043d240c526194000e03014642051111140301840c007020394900055429040d4001d03400c6400a854050040e0300300c4602d8640d219080c0c101e11781c0e034400b00700c0a80081900510a070003442c030746651444d46044000c200c58511140369203482007001882814000c00d20501f0404003400c045070000c2a10b140c0d1241040c1c800c2087c0e450120b110038a5501550105100344070280c810000c0c20701b240350700b40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 125628318 1250 125627068 125627071
    0x5040302060c070b0408060f0a0b0d020405091f050115050c030a0507020a051503060312390f0703030905030303070e010305100b03090307031101140408030405010e0307060f0f0c0909090804080114 86
    0x1c200180c143c0024249d0180b401401c0038110098a01e051502d070b69000c0c08060704001b08403140f540b28038018019079400382e02d00384008000007040001d65504080094900c3c2004203104810054140200a56030402100b250369410f040e09069594034a00d03c00b08810b1b03a5982d0000340d00c180d058904d100c0c00720302d001c000c5100d900200c094a50303541d10394a13648214050750200351088002180c50342a100380000810a01c03041101c581403a42c1f40e4040c5143c40d0808243c1e407021290070038030003041011f03007106c9440060001100074509500d461640200f01c04030541d040342c105a1a08041220b41012185440280c481031041a80e40e04d001e000d525620380c082c1908130700142c01a000b2503c2da503418031603040a55a4203032403440a032541d8887e111160406001900c06550b549860382414208100801990f0302c9210302080c0308551008100c01c484541e510340d00d40c0b90420180702946944040c0003426030740f800c84000b407601c40e20305044846009942003a00c1c00d6282002060100300900005c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 125629568 1250 125628318 125628331
    0x90503010b0a24050906071a091b04110d0908040f050a03050715110105010303091508160302165c120303070c15090305040302060c070b040806 63
    0x303204220780760040c442502d003180f00704064966500200600402c411603540c0303605071245000307030600c000d00300010020351285d582102c1c801c00e0740c1c11703200c9043c0b07080080780c0d407106172a00a020b00b03110081100512a10051505d481566102e4910f01c5109006040d40c5c3c6044800c141000030070180d00d01003009500600900b010322590580029a52606400280640350f1080244c1015403030503001744034201e407500d000828080d190b20303c821070010034032400307001f1406039640b6001e083c0307425100101c1c08440001101003200f00410002d02c01034810104044e100d09140041c0d480500d08511404414001e0009203064903501d41604104900a8482100b0b200f240c0109085080014560359052030400880706552000044a0140391001c005000c0c1c06000f805114100003003403911411580102c07904000718030b10403140014807030400c8008104000c83d610810920307103240c5000c0e06d035000d2444001d1145800140e10880c0c0a0705005c0e40300104002004561a103494035a031948460080341c45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 125630818 1250 125629568 125629571
    0xd0c32030309030304030611040b16060b0a0e06090604020f1210120b1b0f0703110d020f0304170f07080a050c0306070c060e010605090a06030b180d050d0609020a09050301 75
    0x11440385004402c071000d8071401801107140034955075606000c3d2120700000316440c28180030006101c00078400410300f102002e001511303500354074078048040300e10105540d8001e000c05c0301d044c0210b0000f000b03016001032080390300c40a40c0d541c50000402a02c54958491a1058041500b00b90900c808003072034003c5410900380341c02c25444042d0300000d490f00c000040c10210903140810510700f206481c404520640c0c100c1e40b8505010140c20300002e03403202504800143c0c803c00f08403a10b400a121401d080c407601d1020b4485c0e4024440c0c03040d80c0303000d14081e5280070301111102c003506070010807586920130054401da520682d942e480840e04ca075401e110940300f0b070064982e500b00318500881e24034403950045e1560160040d450301c84d031000701801c4014607099940c2d4000030580340d44440c09984075600341c1c10042003007811403130214001100031300348410500c8400d1500d00172031808103400d240d8151a107400c2da01c03050514450009001168801003400303100207a203280c0154030012040988100b43c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 125632068 1250 125630818 125630909
    0x3020a0504110307050a050432120303070302090316031b060806010503041104090204050c0c16080c060304021503040b15030a0c060503130c0e060f01050f090d0c 71
    0xe1005503030b29600c600000942c100009140907001c1c030042e1041c5031113032600c0e81c2070940300c0402c0c0d41007501c42c20f02c529003000c44603102c05850500c80c0e0320b4000d4008c103031050a4141c0460192503035902010b011403050540108160440e034a04101001c82c2c03241841144801036500d04108a8804502500403541c062071040812603901581480f030050b40180d407000d296640d01c2e111000701c2d50700b4003448c42d031103511444840701603500d81c092180549403084c030080d550001c01000c50303e001c40c03e1840195100c4101c400700020440400c0b60015240c05544982d501c3e550f0788002080750103a0080b04800d40c501109000610515400c5584140d221603c008030145184040568807403006900a017a0044d00300706020140c4100060340c0c00401444000350381e0002d0b5900d10f40c1c400030366004440b145c0d20040c2088041d05c0c0131110b40b00070002c2801c0291900f10b078484403252603c205440d441c041c1d084076074281e040100c80c87c0e07101c00500300419500a000c0c2c0c4072170b0140c3d05160940d04141c200c005980e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 125633318 1250 125632068 125632079
    0x30b010503010f0506030c0f0a030f1a0d0602160203060903070507051c030c03031b120501090203010b3007080403020f060606070605130611040608010902090a090b0d051603020a 78
    0x41200c2c1038480001a015800745008100f018070340c0b004110201c0c0c80c0341844425122480f00000d49040e003800c1d2000306a8420191000048592101403680407031072216103514162a0b6010200310340c0e03042200540e68907502d0003101d2524808890003501b500c100003c20070340c074801002078500d0510036401d4070221070340c0c0c10400040020303008101c41c401030095641000030707008080149070980319050215010700c030192012101802060410040ba0400714030200180f0180300e4140580180c400031030555040c0b01c0c200f0510f0107580c01d4041608062400313485110303c09144058081500c40c8002803e00d42104001c0600105940071005480340704a001440303400807441900c16803000e0001030070252661258005070070040c0600c404802c00c440304c400410818012034904440100d0300c0e568071031a000b0020208c14059220401591061100203c1c0750f032030302c402034116a40140702040fa00c84d072400140c01e02a500790010a9480742d070f1006044071422918600450307008aa10702d07662a501c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 125634568 1250 125633318 125633327
    0xe0a050a2010050904050a0b03060c13241b0206042403050910090f0803070302040602061008190206090901230102120403031407050708010b0405090d02070b030601050d06090903030b01 81
    0x240c0100b800b00e0030900002c103460174203511050784412a4507010a481d00c41d40c1c04a03040507425034418103216030015008007201c0c0410480001410000e80d103030314200404085650141040e42004200b110a042c00d01a200307440c4d0711225220740007032440d95901d907501c2c180001001c40c03421641c101d1000801e4084001d00a11a091040b1000409842100d1406640c90001c01c1d00348001c45801c0010314412000c5081980603500c40c00399903e0043c0e03500e0401034041c3c50004020003006c1d843d5400001442000c4001c5182e03101c040c5800510700124240703200090301c500030012410380100e8460f000240340c0c1c202c0e184410710148060300203020041a24012070705c5000c80600e80010500400007000000d00c1441e0444100c10b0411030181888420340e9418103103042503000c0340d050382d142c01c0c0e02d08040c0341510403103400c800c400f0010081c40c0038201011f03480304194400d21645080100000d4002e0b40500308075a5100080d5608008483e116031000c0e0050a401c4401d600203844c0045100665029 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 125635818 1250 125634568 125634589
    0xf0304021c0c03060e070b03010311010206090a110d081b100c03230604060506130f060f1706030712080d06061803150b04050a090201020d0201060609090e0a050a20 72
    0xd580c902c251801e54803400050480c191802c441440b9032080001c104440c000a0341c080d62040c80b0310807180d10440c00091800c079000d0f06d1040301303402c10401c01c0c0001d03130700004002da841ca080d5600d5250b10214181604c86000d40c120304a448044606107006c0308070042105004044510820441040032800480c11104c4460811400c2200040c000301c1805400051030783c0100d0040020912070303100c0300440c1454001c0c40d00c0a444204042c0280141075103480460041d20003454090002001280c005000884d06880c0940b41d1003c04003203080794030706010300c001818018100d08003403c81d5161034111540880307010312140389001b030081030300742c400c030b031000c44500301a03c0c1441e0440c01d54031000c2187c040d00181001c000d0341d81c8161815174845010390780c82206200c5002502544078000a800c0007110103201045903d001801c0c882c00307800c0441c1006407401c04d5800a04a440b003d072036882c000b941c070006001807048144040c2084070350f401c030b04507043e0300c0503144121008400030301c00e06884 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 125637068 1250 125635818 125635823
    0x50601080f0703030302070c050409140c060f0a05030403200f1903140307180b090102010b030a021f0203090409111512010509040812070e0411040e04030c02150f0304021c 75
    0xb42401c00203e4420740103050007038050694602026511400541200d8030398908031980400e1002c40b0120040a0110f0740c08680d081c3c558620305004889816a0f40c4aa11410303001e209000c0042001d061140041c29940c4c0c0000f0100d00540180715a03e9170b0b520201e900003550341c400d0300c04015603280351000d083c21269041d02c910f60031000004600d40c154100030911410800224200b01c4070030100d061b100e0040c190000e9055030b810200000a080d00c1c82c01c0046070013030b4400007405006882e00104101ca01034800d0300901190001d4100720b0a62190200303003070344a400c03c3c642100b07219100143c0d0b180760b901140c9142042c2010030024059000754036040c80349007000001041103040807100c80e07902521540e4460b24080c1684400c2d00050070981d00d240004842e44c03c0315900f0705280c4105c0d0031000f01d2034102420710317107030a014001d10240204010b04110114800000315200c0000040104100c02c0c102c5807030310300f4001a0201030b041241c0a9100d242c031200e40307601c2400b0140c0410041d0742c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 125638318 1250 125637068 125637073
    0x903020603070521010b09010323040210090306050f1f0b0d020d0f1410050411190201091e020a06080108030d1104120317060a060215060102010b0901030b04050601080f 74
    0x81e0342042c242c525801c404480751049841079804501c0701407200240e4080e03c8488507482e10f6038044000101142d09000d070203000c140c0800c2041c1c86130780d80302d4465503100d64101c42214441c1c2ca203032401c90b02801c860348000e0400742810240951803070001c822034030440ba80d076610136807013100307140044428216106d0758500340002c111084111005400601103040580004902d0101d044000c00c01c0750100601d000309001d941081c044018a03c008074001002d08075000d01290402900d40c404621072301190300d01101050708016107250003904032145440d0010306c2406800d600341207051020010714801c030f12403980000301151450207010340906a49080e401982095020030300e445c000d002e9180e600304048820302000030211214600030b104140710f43d442c50110148440c0d4225282c0c405440b44c0d1003108200c60034425a94001056803060504504449440e100c0d500142e00402074030b030f2130079000780c1c1207400441031041c010786203401a84900219030540e0307039403100d031030f00c1e10f09000c0000728a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 125639568 1250 125638318 125638321
    0xc0105070308150907030504030f180501110a0602070b090705220b010207091d0105150612180a061d010c09050d170d0e0f07050303031b190518010903020603 69
    0xd10600381e255100c2c0080b20691288015103000400001e800c41c0c1e07045c006919401004205903200c0900230b02031200e41072503030008000240181c01028207000d607904000454481645820040110341d945940001c81155102203c0c18481d001c0300044550584610800b1800a03e9003051081c40c1d482e03600351080e960010401060301009841580240c0307045100358000424403468030300c43c10020007a501d41c180154a400011036080d82c000030580d03540801c1403492001c5030744861040b0b46181c03414182100c0c03a0307078582c0043c180403074944134aa40140319425026080190a030300c030041c1e01d558000034415143c84103102500ba0756510400e80f00044101c481080030342003c03061540791512907000d020f80d15422000d03a9a00343c200c7c02e113405800340c9908007282015010310019006521080c05810040d08150101e59203100c082c2c52030036510000c0ca044a45081d00700141d44400743c083c3e00c0529a00380e030311401441504405554400f503100710024044a600507032042046a0303018000c00d046 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 125640818 1250 125639568 125639573
    0x80406021b0f0d030b1801060e01090b1306080a020705100c201608030403051902010e0315060a0b04060813050a05070305030408070e0c1902070f0b09030f0c010507 72
    0x181d00072181c600000036158000c01c01d045410b00c0403100d4a4a4400141002c40c03c951000341641c02c0c6601e40740c050440e51020046210715580107a0641d0300f0303410440d207e20052001240d14821f19400b09424881c003003015810302c0310a200d00c0e0100c9125548104d019102e10704890300b00e2080e600d00501c16400014641040740c0541c0160341e405900d400c00b606682810316407424800f880840000c00b9070000c0400d4100d050100302c06202912904c4021400d060665440b40d66606800003064203266035555004116071003244c01201d400b00103410b90705e00801844111032100801c5d60f4191040030700c0f40300415450305040c01d5404a4400e40c0d50fa6026032120f605110070f45000301400c0d500350040603201004200100801c5009511400003980d40d5807501e0021410020b65801c4585a10040e805102e070950015080e50150b00e21074441141882407060140e03c0e000a5078010250240c81420010b1040d81d00809032108100907400d0b103440c3d50f500c44000d13032a03d405441c03841c085035050282101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 125642068 1250 125640818 125640821
    0x40506031b0112110309100902131a0604060203191b1b050603090a1509020a0303050d09121d030109020a0e0c0906070f05150405030405060a020304050604032f01080406 74
    0x2034108060511203e08014401c4110598000d848030050150303001040c442400810000c410150304060410400c401555000800304240310920202d0251160300d4410414001000d490a00070024160381d5125520b00c1c0294603a000418131528046004181c54025809402c0000810801c1c40030522075402585d11807429080704400038103407241c4034101186039140c0c04015400340904100410319441c1a2400c0c6c1d40348492030614003400350500701c05c03e0040e200d08000d201074aa0504015807154000000c3d440209104c1c60041c01e00c001140405040707540003804000d01110812004030920301c004e051600703031070300d205001750090300888080151441408410303400100e1810b00ba45040d00840c00034416401880e410756210300302c5211501007210400c00b0031009002c03004188030f24541a1282c075120f004901c50640204000607040301d615100380100c4020b050014803141c5c90740e4690921035042c0071034040030006580a00750f45001829041e550200d1181c0c140d44081381941d46541d20f10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 125643318 1250 125642068 125642113
    0x1390207050a171002120105040504080d060314071d0105010e010207030507091508010e070302061b010e240108030307030902060d14061003020414090405120705030307090504050603 80
    0x10450280100108050b56410424030042500c201c48400f43c21101e20454103100c152441002807920400140101c290f03034488403030460b10b089030b001600b03582da8100300030144140c044e82c0c82031a18104010042050860038002c2c0d44c0542c0c4100c5c1c16850322001d5503925400104940a51003d252004004562040200380e06441040c4196001c4c1c0382e5907518075152845540204000c0c507114020b01720389240c21030990000f841458000c2c00403070026841d43d5120501c0d0300000e400380d074001407146074146c0e05260203282d070087e1100070000081810000c2d920791030004100740021402016032001107044002160503a40e40740041d61468035a005d081c1c0042070a91002c98002d8410b100000c00030540b0301c107e0711040c20603509540b80c2d292100810900815140c1d0700d009042c4140803e01c100302d00c01e0300c8001c00803015540e981c429202ca0400c0761400b04101151490118001107070707000c004c8044055800b92407d511001d07865611501000300303a0b4000c6075960b4065100300a03900d040c4da480b12800e03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 125644568 1250 125643318 125643431
    0x60506031c050408061006082e03030905090603160b090109030606060507060e0102190e0619021005150904020607150507020102070201110a030503010b1e070605010801 74
    0x1224028074581c000c115803400c0044001c040b40d0007050420181303600380081036118108080c188002d50429202414490340903016401c1c412001c1c0c007400c021107201003814100d04241078400d0205540b460010501d0003603004050281c071030040428064280000c403441c078403d08100f4003003580e0501c400210b098114100e01030400c23040d80400804142d451203000043c2034540da8032951850b0034200b400545e1520f02100404e40e2040144040104104521840d4400c01d07150030f81c1003034250030006e0194001c9060740901a1180650716400c503800003481404602c401ca4203008560b52001212080c40545ca01d560704601071100042c0113141c81801000e54601c0b80c11196003e5460205180448108542d44009031b0f500013202020b5603003220254101e10300030341c001c115031400c60b5002000b6000600c11101411404940565094000021603141002e8122174030f0b110b400030b050400c0909400c0c0f0038884154030f045000c0c549190b007400b5485a03454074941c40d401040c040348112000e2000886c00d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 125645818 1250 125644568 125644573
    0x140c1c0f0816020d141908031911030a02040512071d0702010905150901110f0f1b0a1a0106020d0f0e0301060815040501060e07020d0c0606170708010605060c0a06050603 74
    0x1448010f0f40c413030015800d194002c0090304240f01c900300d407081ca01000000028044000419900b0000f288003007100d6100b0481d034000b03081d41da8802c0d41e44010700320030300340142c4200c008010808103e000b940540201c40c0f0440b00411500710800c111526803a103030080701c0200038410361888076206120b40c500e800681501c00060120040e86a003402c2000c1c000c40c802c0084203070002c1c80003404003402131040240107251081e150040220303100c413a034070465981030780b171071404030340c89405098203a01e80300341140100c10b45030108903500d080003118100c0585001c0c410821000403030388520000b13603280d50000b69210141303407120151003a500006d002e80195810344d2510400300341032000b884030076503809442c58101500d06040c03400b142907540e03d401442740c1c104010100041c2c44e0b400640700c88122440c0c20b04650080e0503041c0b41c0b025118680110070800518064801032480010b01031040302d013486d000700070064032030b400c002d40c81c401c896804955502c90031410f008a11a90310079500074100808 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 125647068 1250 125645818 125645857
    0x15080106050702011115090606030321070519020f160501020d0806040605060a11010518150c190f0806010219080d02160f0507050a030803040b06040603140c1c0f08 72
    0x5c0702e89401840000c01c007810049409200291100700b044a410a40480c055030034040f101802940e030380042e00c20004002c5038080401c42843c020030484000100c1c40740340810f41d03d052840030350380d08021068000c0c180705056401c0c500c44a65030401c401d03984144c0c090542c4a0003004101c0304204080c080d103621591b140350001e0103035240070040448030103640b2403401d1941c01107100350031254001c0c0b4020306641c60050002c80180301180c8004680b4080100700307025140c5040b00b0f00d060040450000f20002c002441d902c80703a402400710301c20b0300d20b29603800190ba0f03a003d00480c2c6540701c0c24140b8400c1e0044540c07150000790000094105618038800040c10a980440281e160f00c0801a05560505600c0780080034481b05000300005404180d8210300c0627403843c2c1d200c6140d480000c202030040000080810352907580c5412010095030406602c0c0c4444070b104034030329291710a116405110f40c060490035100c0c030f046c5406100503550804a44003810001d038580680d10b510100400780101501c54 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 125648318 1250 125647068 125647097
    0x7090510110d02010b010314010e040b07020a050703030c02040e21070f020a0f08070909030e0609030f0d0f0f020a08042d0305030910020c21030c0102030c03060306011508010605070201 81
    0x203044242c039550011401005c03010014080383c008500c1c05503001010300c0140000b6516514040d0041d900501c148690350360010101e0800000b402c0c000c0181c09030400020906901079401c448803802200c041000740f510341c90040d51848410066059000101c40260380c815a01c0080d0140c20b0042d8080e200c02242980024505030407504554050b1108103c00e000728a03080044001a1a121104112100d0310b528003410b001030010b0300500c0782d5400100c11000781c03001d00003003c40d04044811130b005402d40d124043c2c0104200070300b00c4001342100e4000c011403072001681540700ca80101002d4070b440d043c4072456a581c2e85c101e08500b01c0702c11916540940c031b04090703100002940034101171743e2503ea58604015604003c102107000319482a00c000f2900d0387d8600c00c1002070480d11520707601c40d202d08a406400c50046c1e40f040d400a510100404c80c030a6145001180b04400403002d0b1a126a29801c2c81c40074404801418000645480010b0006d0340c000c40081c00442c1c0141400750740312030300c4c0307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 125649568 1250 125648318 125648323
    0x121120f11010f06080d02030c0304030816060515010e04060b071b0f030c030c0b0f030a0f1b0509030f03190305060a05060d090c06091202060f0f031e07080709051011 73
    0xf00d45118aa580e03140412003943c3c20700c00300c05800402d20245261018421065540e4042c03804060044000003c200110b85032000024011986c0014207011034501410209018901ca2041e640811050a018940b0385428070a01c0241c41f88102e40c141003040d2520b56030100518030018401240d9092804107420942c0b0105400440c0701d808900006811458046500181d5034407120700490140b06000d03010019500b502da00a4104200080b0b4444414949010300384032440e102244080313000c0f026505601100410350894140c04840d2240e160401c0b2590ba482140404403282342029130300d990b4a8440c2e0850b40d04030b6002045142c0840e100d00000b50550310031120103680300c0c1d4848500003000402d04144000744524200300e0715441c5440482e50b4140b2101d58024400d40001a05160407500d0f281540c1d003071010444a2901e030724060f003111900c5c06900b192000d82c41341103000103645611070145184102050b9642e903800b1460071051041010020162009104009800140e00b0404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 125650818 1250 125649568 125649581
    0x3160c05030d0501260c0109051e0a060c0611040b0702100221040306050a0605010e0105130e130221030417030d0e030a0e040b181009140121120f1101 66
    0xb00d1341c019040c040401c0805c0042c5401c0d40c4104040e0852142892070340c0e0400301c110211270058880c0c194001400c42c10fa40440b40c4203a0310740d441004828041221644242c6841d8054464201000b019001c2116403006015a20840840c0c0c90108000c000506004460040e01507150040303618100da10301280b01c9940b0039140900c0711020110b01002400542e0145581200208004015041c1000c1c0028120b00c64000d0541c188000010700e607070315200070b0401c0d0004142c6041308080c0c5041c6000361540d44d20030030006074840d440d0b414044407060507898070171034031a140340c004500c5c1030328040a0024001c0d44000701d0701c0a010a0203001d140caa654080c2980415049000d17540c1d5140420303020b00568403c0c4074a9020b02e10340402078441d0340350411900d400740304085a50425940e00e2075003e80d42001c03038110911b60350401110b401c41e40d490000b081c0c140d4241c0d00181c1c40016400d00d1461003004c012201400b2107072800c800c0910540a9044145202d00d00d241c4a1001c2400443c9142500c44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 125652068 1250 125650818 125650829
    0x1104240b030708070c03080a1d0a06090611040b091504050415060207060f050409020d060314010b01031a0d0b15030a0b01030c080d0518180702030d05010b03160c05030d0501 76
    0x1000040080c2c0580c030810b1164000310b1317410003019640254a0003000200c0c001c110b0030040340d5403010954202588164800740000300c078100c7d1040140f52a051002e0b02d03034034204544a03414072010f8055100380500360b03000d0b00d08203501c060429503a00c0070841d00030901407840000300410000412103484600540c1e0701e0b640c10405910045180050003031030200325501180412a5141031a588154400100c038210f4050b4100561910304403d011801428a030f40014401c40541d038052501b80c5042d00a150105000d032003c101d0441c0a6009008010a580c0019440071294200800044068013a81c0c0c003e024100d42e008a00302a0020034603001c0070300000e60300d4051140040080001d610302e19000380c60040701038003011010300c3c006440d0b4014040e0640c0200300c00e1310b101c45603803604e8007080003402c125800f5040c213040c030400280d00d907802007290008003410100042039503140341b000c0b03900030715803510b40486100c10140219090742c003a410841e1a40000c019124030945e060280901900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 125653318 1250 125652068 125652089
    0x30e0d120603080a08193b0a03020601060306080303061f120519060b12060d150213060e0d0b070f030906060b090111010605090609040203010f110d06090504110424 72
    0x910600086c0d01300403248151b140ca904100c0c4600c50443c41c8041c550000054641d0600303156000400c0441544007040d01c0085403207040140070915900084d803170304888860f2030802a0540354030045480344011529150072105102d44030700c1d603820b480c0d401c05402003146440d03001c6e0601d8505100507500e041c6c80d88040d50b0300074405544442c0c41489403000405262400c94900130b80c41d004113260001c0188654852040281c52000f405415010448101054003003103540300031880500000607882d001d90000030b182568a086103081c40400000035581100350b1058036a00c6080c1150f00502c1c2c000000c0c101a203d02ea03480004880380500f2010b0203100b42d419071140405400103040d2050309204066036810710074204400d480304415590440300c156a1808aa1b80c0d9001081c003500003111080b40c2540340440301c2103065025070203440750000740c18041c800c00d0364440d050302c250381c800d4501519905000c00d58480328682039010700c0e4550854140d40300b9810b400700a0042e40140742e0301518907078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 125654568 1250 125653318 125653321
    0x306021305010206010e180a0f15050108030a1707030b12070303020105060901030c03030302091f11460206040b0702040b040606080f0a0204080d170106030e0d120603080a08 76
    0x1012980c800801412003032000786800c0d81351900c40c1150000142240010302031501303181d41e96510600c509451305802003208600d500071450480b10316061343c1d070180e01d01440c201c004210303450040120b90120784d1a44c0e0703241007210f06820003142050040c0940c41490f95030041c8040540fa1459846504091100034094080c91400d0207403d5640040002d442810000300510020780508440c1040c1c1c1e4151170700680352400341001c50400c9142d041039109904a0f0340c90300d00203e030f0161107812a030040000b40d550f1818240c0700c200c03104466000c1c3c107401c00465882107419811030b2a04650308541c5000215040600d9004500c041c0e0141c0c1140815000000c0d80c40117604090140c3c000d035882c10b4804100d02442c0a1004000009c040d1031483c000c0e4255000c1113029030542c040ea8060000c40c42662000381d0000006000c058484c01c2c100d43c1e2200130000060038500074801d108180c000c00018040c0c0c2c014940b000c80301c0341007020405504680d100c4c00031010a4043d005410b08031111381391311000c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 125655818 1250 125654568 125654587
    0x10e130504110a03030207031506090609051b0c0a0b060a030210020f0105071404030201030c0e0406122003120a0c0506010e061e01090506090d0209160801080a0305040e04050309030106030602 84
    0x2c007805044010b000d001c1c50182040000d5002854004582e0400c6030030603a91580c0000d0b201420880e0710160105062100c042066905903100d82e000711103a076a0f075100304244200c030301014001c20281047c25045999004e0108041c807030510360004004002e100000d07100d5000a4480443c0c4614400507401700c14510075992003481015009076040c00c10a0504001c0c0345031321018416808000e04058681c1c5214840b14000e112000b82007000400610195032201c002c0180c2101e0248252121071600011044a0b03004001c1d504000b00007501921250443c4400b880c03c503070040d281c2c1c1c001c010541c814100854802d01006010303100c01510f14295080030002c05c62200481d000f00c01058148894403581c42e130b00040b060003103440c10384542d500d540c030001c00202002e08000d006500a10840100712900d04c0c0d601110024000e162212140c60b40c032403988507510083e1010041c0030070802c01082c803040440c602c90640c086d01c20401c480c641450780002c0703800c2d0351041d40704031303070803600170500244 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 125657068 1250 125655818 125655833
    0x90507330e010e03010f0e0c0604050906060c1203100f06030e061801060906030b060103140106050f0d0209031506010201110a08010b070303060509151302090618010e130504 76
    0x20114405144480050001000940080040c0420030901944100100ca0750740101440300351030030020000c0080e920100c9a4402600d11000007101e036000e420b16000c1c213841c180c0103031410340d1005002c0402e5a40c609043c0b0110b944014072010140c0f103041c21804c082c0c0c611030b000350710800d040ba0010400d60300e030420460030090300e0303001241413508201d240a541a400120300d6440b80401d41d400a40c501003186150048c0f030180c005108240c2490404000d00ca805202c8a01950080e070302000b41e418230300e084d120350800a0141c1000140200851603050407600003a01310740c0010000141740034400c80029240030940300070103040c0884502040410768080c81303565103000c0c0c1600014074080000c807000708141414011120161400305d1040c0905100b50b000202500d009009865141000039000320400d01c920b22140c41401c458119a05101d8180203481d800c0c075025003c1c03402c0c00c0301000c80c695401e01c400c04460400c00108500d0400d540d0308420451900c0c0381000c0010305003800d081215 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 125658318 1250 125657068 125657099
    0x9040602090a090506060d090305041a03090f0c090a020904020f120910051302060c01061d0103061113170c10030b090a060f03020909010609020a17160e22090507 71
    0x40c3c43c00d103803004000082d01c0700e0303045134006102001d0004151134035250581d0b241c0195000b09030005100705d42d00346901e02c4c1c80019402480710500700d44201d101c1c0359040c1e95408116403180d810a048a02250000c83e040e0098070f40810300400c090300f004a140520702154000348090202c0d100d100c03040c8507242138207114044005140050900a038030b0000e070b07840d1204c018514000e00802c0009034010203c03200b940200c01400c20303044191030001100d041201c81c0c050038042580e600e4641140440504440801c99148070001194100d0403481c0548003224880489048085070044a078907042560b074074064080412503940300010101e130307054240308207804010034040c00c0c24a44007061240500319001c035800c9a40c101c0d00040d1175a280003585015240c6540036a074858004101150407503041143c01500802c85088119503503240c00515000c0104220004003150351b413176050805060448070010108401a8003420400c801d00601003102d071110416209508004414414036003410b2380c21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 125659568 1250 125658318 125658329
    0x901030f110a05070303020f03040b04150515010c06020c100f06050f0a05090903161101030c18060302091c081803150a0218060c010f05010902160605060d0209040602090a 75
    0x104803054101e212403410384511010700c0148080451240c041500c6501104c810215101c03007691282028a00040201020340741200e03011501003052003400c1c07c922032035210365581040c98420400c49001522071041901d000d6031480c0c0c08012015269030104127104010f40c080c1750008003450320655403402c40c0d4090300118418031110011a941780d440d03008170000e407142281c0c1190f1680300c1c078400e5880c40c03141800c2c03500c00c0e41103a00c035401848010070700c3e40b04201083c0c81c02d000700b04442c4000c98000f920b905469458240a00043c45030501c25801741240400280c10340740c3c07a589200c03441e1008207034131000311040d0400044811451f08a0408503800a006400801d0b46c0010740c4803001d013100004154216044e404100c004a4518001c4c0422583e24050039069070b0314849403c03580030b480318450b41941d050074000005458907041c801c4840070350002d0551b5801400a68449020f0003024001c66845001c503040000580e43d4801003c2c080c0c1e118100060781e03100000c040c08407480c41544803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 125660818 1250 125659568 125659571
    0x1a091c030b01170709182403030206040f08040812041d070801030f06021b10051005030703021e0a061206080105040b0109020723070302121c180b07080901030f 70
    0x4440c9980020381c450700d10010b5200005541d43c2c44d601102e07540c143d540525010440404c4014032104941e100d20032692210b514014802104e0b1881c0950803114840200160700540018020418100d06400c8035031003845007a20f055941c184142c40c140f00f00c40c0007a50180c1c0090104102d00b51800382540d203800910060352180340c11b800103000c424052101500003010059072000b04041075049800384076011544030424030203110040e61307071480c100c40c060840c4e1030308001c105000c0e04101c41d00c1c00c488004000300101d038110ba00f40045021104604410f0320b0f2054080c041075a241030028000c0c1030389540300300d103007034010750150f09640c0e281d4808510b591400e01031002041c5002d821038152840d0318802b69072400b042c90541002c0c1d48500b00720703800042506409100c0c110200700c650032240212240c1074900d001020b46521160240103a443c0c0410402540d001c0c14000e105c4034580d00182240e450b181a40c0b0304c070000380d590000c00120342415000030803201c50340c0c1610515000b841c0d00b010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 125662068 1250 125660818 125660831
    0x3060807090e150c070611092d010f0315060e030d05031003080708090d03050c120301240903080406020601152f100e0a120f020a020d1a091c03 63
    0x1062512401803910809000c0c80400001d0b416500e4102205d81e05540b00c2c0c810031900f240307110000c541e44c015181d181d11a0b90013811000614000f0020b030040b01c9a0851455044820840195401c1522880c40024140c440f884460b00240501e80c090041c001501e41c2c54105083c14201400c10b856200c04005008080c0203010541c3c034a85c0d2003100b41e9034444904ca54810050800f00d106000e119912940030001d81604020154040090300c04032848800b1038618069503c9510001e00090082440040580c0300300d0350142c20101c1d040b011004542014240b154580d141c4401340c0d0310541100d030250b80110010130085045820141441800d442c00882c040d10001040112076114403440740c040c804c00240a07805e000902485020841d60542000100074820a40b515010040340559010303400c081d07035040050089894005445a80c0e01421609015900700b1120001208054503002a892810710490034101c0035503000b813030360710000d200401229000f24841491425000101801c054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 125663318 1250 125662068 125662091
    0x190504080706050307120e070302040c02071a130320010f0f0503130516060207080f0a03080103140a06050c071101142b0912081b0d020307021c0306080709 68
    0x241c0c800a0750310528006607651507a0008961035040b000e1244001450030341c0b01a034588002502c0705c03c403403094074181b044040c20a401d0740ca401181c0f040880e4112170005569070622010010300c1c90b8030301e18040d003e215032a034070b5030041480f80c0d000c2c0b21107044407070388011015a0400b08401683c2514a80703030500440526009044d40000341c8072024818602c0c0354030781045828041c1c1e00b02040c80362412821141e856400a50707644040c8034803103103401f038410070031541c41011468500f156010b07100d001d03a60340707075940b45010448888130700b94007409401141c8000500c90300983e806503081c103041c035441d01840d06103404420100092941445811001065101400703401c6d0340c0074071a26108035071405000042004c81d00320031a11844540d10700b44420040060b406884a03503060380d83c3e64109240e80700e800c000c42034101502d109a05120078490202d11442d5900210381c080814030540e03005140e6680c0000841d00500c200e1030109880b113000b80b045440c01c2015000400b0700c2002484002e1180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 125664568 1250 125663318 125663323
    0x120504030512191104030c080c0105071b1203170601020d27120b09100b03070902031e01090203071d0616051905100f1a061e030c19050408 61
    0x30341600980c40e024200050812243d06896180b40071800403d0158a401c4809034000354072a00086415141c2c40d80c01148191000a881c4030008040e12200c1c0f400480f51603110803452859540f0300e004d0045000490080844000764031080e1003600d0f03c3c0848030020310000e0000d440284081d0455010084807a9051b5012882c3c041c1c05c4001c140e00d521004810303402d1001b140464200303040c1d035140d490340d45042128441c06584140752401c15070b124140c1c500c8110083c1c0c1c80580700036905501514042c0300c0600707198001d580013a0b1401c003c5c10a84000807000307400ba81d09078464564a42e01008202c1190f80117104100e09841021021000c601240001501c5000b000b205224019000d105002004010000e40309a00808c9081070398a000341d1500964810500310505940750030804407034000c50040c040d903240b408801e0031910404072207400b0f02031960810302c41c4902e20510310b2840c80d004401c2000550041c0c144c05001d40d5034010800e1110008041480703c1020482c00304401c10606001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 125665818 1250 125664568 125664577
    0x1020f0d05090d1a101e0614040e040303060314030703140c0106080609060a0b10120b061b0601030b060603010b03010303050702010203070204060909030e100e0925020d1205040305 79
    0x140e0070155102d10707030400400c81e403000814004010304145503032001d0300118205120b12408001015980168a40221105800c01d005040800313040780351040c8103035406116041228000f4801c08c50030f0650714888580400e109403015001700b50f40d800240207014841010b44d10441d0040d0096142c215280d600a040e520348000d11080d450300481c40b0782031140c2c2034020000500060040b23402d6801c010020a03203840d016030fa954841841d2000070019810f10001c00d03a0010b0441e1100000110720000010190a00140095000008202260200040d10f008488030141c0c40c00038552907045152400c09114058030191107204103100400c0751140301c0d0100c9040d42c0e0300d86401d03a1210319501c0142d140d401480c60083d8003504100001c00c40e4542a070000305d0b15030195962500e004041c400f44041c195202e15010700140b00c8003c0c202031810007110700ca030840701d0b10303401850344504000c611901d080c06104880c0140c002d880e9295101d40e0112140e4100545580308200ca8109980d01500d50304c103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 125667068 1250 125665818 125665843
    0xc0c0c04020f04080105040308090712230703020307120c090603080906070602040b030c070303140f070e01050903010203010b031b0a090e0a020c0f010c02010c020f0607050705070305030c0106060e01020f 89
    0x3000141c2141142c90501500c2c0181240002070060342480e15001d03041540440b02400e06110340d0000150404c0000201802c2603086141c0300e0400c0029100c031600300c4da03051541502413003030010010041c4c03400c122010040840c031011410700c03511490003000d8002a43d004019050410360144041020802210640300342200c20a540d1000b501d404c001038007a50780007091224002c1b0030402403196030790041c10907e1081e642084a03180e42d01111080e45005e450b1412a50020030020710b03250300031604036a65040c14180141040e0555001900b603900c26005829866400700a10107184140340c41c00151140342452142404070001006200000c08d11503011307000044400714030030066960444010510340c42c1078400510040038440c1c003034408620314900540c6010380c0e02012038800b080d55440c1d288000064811603c8400d411112030700f10500c103407900c2c00741c0700f400030000c2c0041005040182d000e10001c02e446181c00c90103407048002d0704c142419074001c205803580b40d40001c903058032280c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 125668318 1250 125667068 125667071
    0x40204151403070f180c21060501030f090f0b0c09040207060204140a1508060d120801060801090b0d02063004021003021c0504060b1201140901060302010f0c030315030b07080c0c0c04 80
    0x10408003c5404000110031f044000e1840043c0814840c0607400c2041130b10401c0c0c80900100300310314450012500d100502034050501c0790b51440c000750316a4056a00302046c0c2031841d0501c040d10000604030307402040c040303400e140c2c0094200008500c914160070004801c944848840d07140505815a07030104030600010006503d0014100b40d03644203414413070581007030310303603140300011040640342001c01c0c0a0f090118500c140001404445030152440e0032502411549041ca041d9081c000d00da0485803100b400c0c400e000d524054100d104418000c0143c04c2d4900c1c1c5400c6081c140148444004015044800c050041103041408440b010094140c1400101d0010b81a40c071402c02500808588004940c84000d900c8405080b900541101c0e15900149138845144c0e161034043c00d00325109480001d01140300c1c0c44040d5480c0d402020485119400b9040100d11159005402444000305030801c03200104034000744191b5071350000955600041d6000f24514002034203c81980e80d218401602c2e1049 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 125669568 1250 125668318 125668331
    0xa0809010627060b0405150306061204051f0216020907020c03030d0e06180c060715020313110a140d060912020c150304030f0305040204151403070f18 66
    0x101003503005000801080e06809008840040e0400402c0000841c0707054190038001c0200b8022002c0702180c045410003072110301c284455a910700003940000744040d5003e0414800800b4020f0003410141c4190301c5617016103001152f0109811043e188144050400352062042c3c0c0140e84214134180011901203560300115911144224580a42c0204064146c08049410650301c012078100100449402c070a982c8603544d2008803c542da51800242945580228000351490030280018071500b03014900c1320300d04411660800042c1ea10544101c60160b45a030080300602c504c1000804940701c08846205003c1d181910b40358100155403401482802810600310401c071301d681c014512a94000420910f06114500203510350860507c030902a80c011690807020804440440740300340e51540307a040d818540380d14101e0080c400204100d8000d40d882c1d8403d007891a40c002e4580080c00413401001710b104400c1c043c1403c2002c20780c44192010008d0340140071801c45900b803100d00c0c142c01340002680 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 125670818 1250 125669568 125669581
    0x305040818030f0a050c0102070b09060f0f0c0d090f0509061f030209270f010605122805220b010b090a0512030a030515030d12060b0d021b010203010b0a08 68
    0x30020300075000d030040d200703413505101081404604003400704e10076001d40e01103565034001c240340c501c510600240d20010403c200e00341c0d1500000a08060607451a4484c01d080307224a038146030000078034401c0049004d2545c100214010180040060001034419100b84d080110215141d40042c01150001c0c16440c042c07262410b00c2507055030b120744c00041c0802000e11306440d846a4034020024401200140000040d0751128600315a030304a6419948051401080841a41c141003000d041c450790701540a48060780c800b40314041d612072007840840020780341051840c3c2c8024207206c800140c0c0707544170310043c0c1d40440c0019400701c1c1151038440d42a6640c1e00d0200001d032080030280c2080394010317800d00100a24000002c0940141c6003141c5040101c3d880d6058400802902280c40d180d155000303c4489043c244030b00c96441c2090359800000c208141c445030700130050381085800d030382490344c007041000d14440510009a238184400000310300c2c6504052640107144295500c1720280140900450390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 125672068 1250 125670818 125670823
    0xe040b01020313030f020906031507030506061e0a030e010b03030f0702040f0509030703030b010203070b04080a030f0c050903160f030b040510091109070e011b0309050909010c0906030504081803 85
    0x2200c103400c2c1c1040f40c05a220f141050001e0740c48034003680074030010310001d99207050000350003040b1001c0660211203a5201241140640802801c140e008070051000e40351422280b411600c60341c2000403480d0b04e800c41d40c203009044400039191084036a0420500f0b054a4070040111000600c2680800b942c9000c50300120b4040c110031a606e2100c145840c04000b4000000b002a02005109030740034040c04025000481e900d00a0f0540580314041007004640096154001001c460300d0600b00801d009042070080b50440300f01a00c41c01c0400e00c000703000281c83c501800b106641030480071900b280c1500702517241d40300d4141804001d009000410108051142c00c001100c85d0140c805030074445441545003842010ba829600c250080c81c0120103d03406500401003400102c034181c1d074500c14108180a0170207402c50044098040c015694804281341e02c81104e8540b0805408c000440c40c0345d9190001007076543c1c158410002c00d42b801040c07200150804080b03a40543c00b401c7d1aa110300d81d000300090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 125673318 1250 125672068 125672077
    0x60306040c06200f0606101d01030504030c02210c120d03020306010c0503030709050f030c010c0809180411150406050f0a050d091406060d05150405010b1017011202010e040b010203 79
    0x5080c4a1030100c54070b09440000d071030741b01d40d1050f40d2201e000c45445134103072030f0041082e00c8180386517281c100c503420303651007a400a40d2040c000d00c0c02105228298010035160110245c441d0040c68596034441001041000751440164040d1800d080c04024440c0058582c40d0004032a0300b00343d00040801c01c1c5138410801c00e44040d401c141500c1e542d0500301c1c1d010381101454882d4901414811101441c240b401013960705017074506131911010804d240d40c80651541c40720a2650340501d2040c9202204181c024080d0311131489180b06400301002c00d010010400003620321101414400c20050051030f03402001c0c1d880c1c01280324601070b100c01c000441500c5601800d21401e5280389000702003418010300700c0d9124a440b86100c2a21200d450300024098552800040500365500002e4403050703e05070800025032140c0948000030b61880c4000018840d07154414074580011000c1111500c0c6409001d1703098010302d200580460007107003640c00a41004170b2444103521440d035a04103c00941d000340100c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 125674568 1250 125673318 125673377
    0x206070803100515040b0711011112030a051003020d080a050f0c011d0606030304060810050604060c0605070c020d08030712020d0914010207170a030e01021c05060306040c06 76
    0x94480ca0582c04000e4400d900e442007612448a000d1603d40c0d02002c201250300762160382c1c85141c0790605545401d202d010b001c00d030044c10403081c40451b440d80da80a002114100380c0402186540c1d0034408181c10070784402070920a070b1005110000c000580d12042d89040d031503402803d50340c8600354204203650034010103500c0d070302949001546801a50040d8441d0302803040c0380886800780115032078040d64441c8116406501603104003c10f000407401a0002c5901000e1301c2d0448080c139403200c01080c03894010790700400120780381503060410030800380030f0658001294500805141141d400047c02c0f000549406804240004089002e45100301c0d100a90310b600c4600941d80c03003102e807001c100100300c21041075403c00c101d080f484000d50750600895608907003001c50544801c85005201c000340e8070845120042c0b55071400544251002800900861002c0b1403106004081440011064850040200e482a0490b50422000401529400080e070b0014503041400029080c5200c2000c1d0780411070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 125675818 1250 125674568 125674583
    0xa140d0f03050c160519150e040f0c0203040e0c0705030706091a010308030a0c11060a021c0f02030103120e010807050901030921020c010c03170c2a07060c031209020607 74
    0x7a00e0400058001c480054406103083e01ca210788039400d00916020721140000302050b0030403030794800c208c0f4412412004100040603944060203404440012480c8400f58001040c1003010010041303051794001005007403945086480e41e2103680328030901d1f40007412140d42c0c075240024007400b40d1a024504550107024002943c42c0c0c03c103103a641e00111110034180381042c02c00000c81c4d100701031115900e0420350062190341c4905104402941180888403040102c0c6034041032003007040c1c0a810054004901d0042c0d0300d50540c207140384040080e829500a2010602c01600320340d078000c40c4254407400c249070054886810b1001203010b001010005841c1c1c3d109072440142d40c1100040c0100305040c5602260b00f418040070042d18030000c0c134032001e00400c56002d00007000d00001030b002588010404070113860b1010741c0c40b2441460191040702c10308000e0304604001c1e148030030011070b005049103090000d68000181e50040140c054500240c281d903480d440e100c0110b4132424261904035510003039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 125677068 1250 125675818 125675833
    0x2070501050f04170901020705150f030f090c0f030303060d2f090609060603070f0215180f0606060f18030102071a0c0301063002180a140d0f03050c 65
    0x941005110980c3d00307482a10f0321000036101300d00c09004441e50707000f0680240020b40d2a20041018200c0d1408050817a1941040812009800b60b4001c0d403141c2a552200c01041c20020000380ca04104415094017444180000030207594001054980c03204045440b05010141c1e41303001c0f03040050101424440c1511010f88a0b0500c041e074400000d159025190240180d40e10000c11515560650389280c0000c41000464181846030951b0f011020041c01100d102c86030710019029282d90480d02c3c0e03030000c4d050b400c03900d440e40010300c8541c1301384200d00300418940c101000040ca87d4803a080c5840504c006c00510040400c414101c007898420340180215180c0d010340c14841c20401c600340100301c19100001c00a000c0c03004400a50707041c0c400e0f80c2d64540d130b140c40c45d441c20003180c2c615030304440004480510701c2481a00074001800c98032140d82081803081d450300248051942c464200380c0d0034600c2e0600c2d02c480d03a161034203801d007d16007203612000055500d0605450921550300741c02640d024109 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 125678318 1250 125677068 125677081
    0xc0e0d11030d0c1b0e0105330d0f1116110405010e19050c030a0c0c0c060207060201060e150d1b0e060a0504020306010c0b0907080105010312032702060703030207050105 74
    0x4000f40107041c024225107090b10030498110304a4402d50040c00300c03180c60700005200300d00342410002c80d8087c1d58407180381c01c0709107188005488400f0181580080400046990201c29240110000117500c0e140a103e080048140b200d194000c54008440106220032903906101d14040d01c1c0c10003020140040105585a0390310219442c01240c48540c1504841441c415000d150b03c40c541c4210401141641161030b8800c281000c2c1661070f0a000030400358054990108000301c140c5c2d8020f1540d50001d140c1c1a1404402a003035982c154000c80d180d400d40420030050002511000100d2a0200d4480c1c41800c100e15015891070b0800380300c24907400546001040001c2940b1042e802132030300711507252109076690200f10982c40101c904500107419071214a0019619100705a0000e81c25420b0b2051140c0301c0d000c007803c55100342d10507903906a485071f048070074507054411454112208a06000e5030301c0300c0080c41f24900e004585c028001d4600142000900d840395059403540c640c400002c0c4041e00740305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 125679568 1250 125678318 125678327
    0x130e0c09010905010206090709110c01020c06060a08070b09090912040801020c010f061419051309060c0e06120c0f040b090a24030e1009030903050609010c0e0d11030d 73
    0x214405400700b114a500401c0a40c00060001d10440d0703040300408555051a040310094031009985501810092103c5c681e03200080c0060000755442000914a42c034244040000c02c09155004602640080b10140034481d101001c407031034010191020000c41d12880b00d024588910000109607014001c600403500c404103400510200c80c1150092054040341c03142c05046038070034410000d04130941c3e03d06284506044031500740d0b215590074801005680c541c041184002807448140a0640e18502c1800f00a0940b00715442c2d4051880c0294078840498042400340c4644030403007000ca07404500060003580f15408840010005610340d87e290ba50b1820b80d0b64461300003040080c49000151004200401003009194072100074841450002c441c01c14242c004099000350019180619031000c03007030280b01d000707140c007032803096680e00034403232071420080c0c100729003e0040000f903410600c060079001d41c0106c00c3c03000b64004940c00101d1006515201c0c2401c000c0d01101074060050701c4a800300303603411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 125680818 1250 125679568 125679577
    0x40510030c030b010f0905060108060f01031b0302040e01090603080a0c0f1a090114060604120503070f1103120c06010303030e0a05070e01051302070210050f0409140a0e0105060a0605130e0c 83
    0x601c0c2060801d1915405502c01f81e440840380c142c00580d90800107242c2d45411301c20513034110410b0400088902201128080003611401344101082c1c00007010880300c80c1d403101e01401411100c204010a078115901d142103032088281c001d08003c5e4407416030050091040300b061110341d0041103115880c0b120a1b550541500840d211260f55181c40058455041d842001c140f03d004002c0140b89030500b4004000c12540a100059415220038001c100006400c990190000c9010b80c0e501044600c013142098a050f8821020b500c000c401400f01c0c8005600c0080e0881c1929410305000c50541c90014803140f0b0550221b9000d8254407502c0c07400141081d002800074181d550a4904640c10007442040001343d10070110002d42184002ca00d40412501c5080542035110040c80a40d117010390394005941603422818032014400d841906001402200d841107070f40c040c05180080c0304034075101e8000b5601300070b0b621404003801000916440c030007204201c1e02000c4c1c95510404d1005040c68503400b00207420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 125682068 1250 125680818 125680829
    0x1203031b0305090606011d06040801152102100c15060e07140f0a0905030d08090c0108040f110f03010e071706010317070609080324090105060702040510030c030b01 72
    0x2420452609403030700c039000d1030b8402c00e60440280803540f1034100441342c1c1000d400c00b00504032855980d800031036540c400140001c1410b60000b140381c2c00700d840c03400900502d035800307d412400d44114801504144269040400350100d03103a0210815400b001d6a070501ca80d04020041d101d428000c03120b1403410b522402c1501e1100fa840109a581e1000603a981d07040d86035140340905050021a0500b8088801800074204916100c0c03503960350740000c80e140044c9000003202040001c01081034011301003000d080341c102e09203041d04131410035855900304060428006031003d00116003071052600c8050496019607805402005495190111030303442d450980a250001c101400c2092648030300058002d060b0b03608a100104040100902603000383e02c01c1e5811920340d40c4075401d41c1c000c910400003461081b901c06081e441144c400710040d036403003c461016948183c4640b80180034949440341550a4203605940008850302c9103803d010665003103500007002665120008000c012402e070303800c2c0c100d41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 125683318 1250 125682068 125682101
    0x90c120507060806030a02060310080f06040b060102070501200109150b0a0509071e180e01061e121e06060e010f03020a0c0b040f1406100b120106080c04120303 70
    0x588520b02220151800c2c1ca1580c1d160f842041040c1c058134062000b5a04805000480b90341c041d40c4419260811100c59000d04803600584100800d200601040c0c2d07a0000c024409044c1d06401c2000181a091510f48803420140d814001102441d100754881c1e00c0060b0050811710081c028890301c4400342520741946401920400c81c001424206040e03014059107043c3c0360111342006400103020303150404410b401c01c21005d1010f0b8054030407144048030182c101c07450b100c1c1e21503041540c0504543c001351040340c00c924aa018071801d040d0b1000c4501e800744c411a10215044d05000320b454113010303841c0390200c0c070f41d0702e400c5000443c50f070043c000f0180c135842030700c80054802c19204240c1c00c9028600b05100402c00c1e01d441c0000150b080c90010380d010381701d101f4000d01080300307032211402080c0e034145024082d03110a06100082114440d120000d040c403500a034904000c000d010011160306229100c181b2030480702090b403540401056034081c0030040260a01c140042c203004029040d0341400140d1136 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 125684568 1250 125683318 125683333
    0x12060e06150f010c0206070f0c030807150c020c240913050a061707030201030b1807031d03071e020117070c030801151d030705030a03090e09030306030a03050a03090c1205 75
    0x35400340310300c41c2c691341d0010f03c1e10f8144440b54490401318100b0510444040b00c41000210000300150042c089090045404850055100302105c04660902e50b8802c19580080403001c116981e500c0445080a40b440f194811040089403611706030040855285d8080000c1c1280e64000e940e41e8030481c07107030800001c00e05c02e071561024417106030421800c2614058021072024400341d402900320795241080074003400030304c0b920f071880210002804e5642800003900c80010051218500343e2001c135040450000d1850480c25aa45040b003040c0300007500c4000000d00d03403480c15680554080410303002c00d00c000c1f0000d071a040b60000c00510100400714042400c40c00003095105242c031401414601c0d9461f110000c641946030b00c3c21509910031210751611402c0342c040f0700c0d82c074140020036280e44070340ca070080c500d42030105013240501d00400b65411540203104200d499074001500c3d004d140d4050401030740c1d0f01101c8800314054000300c40c0140012044405c0040c2d80074201901e264103d006401740d4150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 125685818 1250 125684568 125684599
    0x1802012706020115140d03081b07050102090a050102060903041e03020405011d130c050f0d080a0f0201110313140a0506010e0405010b0307030203030405060d0207050105011e060e0a12060e0615 84
    0xc1d0b00c1042d4030700b1b41240078180840002405014040d42100c0600b4944002c418400104680f0740d004240c2283e0994000c00c41d01001c0c10b00c50980c0010301030034000b5050034075203004810794a005507c01c07191790b20108a840350150824034960006150040e005001c2e543c0c41d005003802e5020b001d41514040c1001c000006d010440103140d00c80c14070f902c8982099041e01e4103082054000d10a0b0749103602c80d402c1215980000c06080007007404111680380c40300000e098050181c2120a0398910f42103800042040080c03014118502d00350480d485244030303200300c104030305007460003840d007400600c24480d0400100c1d084044030003142c803d91054000380480705090040c10340b20f88580c40300079090740c8107000c10300482ca0100050160400d89a1005003081d8158480c0c500b514130a902c48400141003a100c05140c80b0b85030082000f8002900307001e4034400c1d00c1c0b8003140070f5402d5840b540c809081482c5004003000b040d504500c8a5650040803129a03040c408844a410125044028840c82030480440c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 125687068 1250 125685818 125685839
    0x807020a020303030a110c010f050709092715020406080402120a03090b0d09060203190b0d0308060405070e030a15150b040504020f070b070c05010f1802012706020115 73
    0x2403269018010754219112102c4410140003036107a0040c03078040c1440018070450017446483c20781b500f80e000210300ca04146202818190858001410050600d00410340043d02003012240f03090310102c0850b441c00c503d08048814086007031085085500020b030009442e54040070107405203000301d034011250708900d0740f0380d941c60340008001001301d80d02c0003041210381c0d00d0a01030001010030302d60204105820344d440300c04076803084403a2501d45011041d0a080c000c01c900ca5010024410b441e401001c603656200505224070050071180b0031030b00e0303000107040c0d584101904075501c42c005d0f04488020565103001101d8020f0240c966940f5450700548505c4220300000b4401220018019140740504200038440650303c6401c81c00c203280320420100001601c0c2c1c42040d886108947c1e152031501c501c038a800703820740d40506001420241040b13890880c080403900d06a11041d42400d0001c03187c010089480440e03c246040f0410701032116070700103120742e01908090b40c5000e5601c00102029204c0710b0014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 125688318 1250 125687068 125687083
    0x90203060108130309090c020328080a020708070f08030601030e0705010c26120915010302010e0f030c03030a020f071703070b0a020d0507030f0c0206010b0d020702011106040f0201080702 82
    0xc1c0010942000b1480046000c860308070b0342ca000c0e280255840e52500c9072a0151812040040016070000401015001c589642c0d1940c000111700c0d11342c083c56039200010010f0f0000742901d8071013640002c0d0390080004280c21106aaa400544140504094107140c0d0084cac00c1104d00034046403c2000c03140c662a07011408406882050311410174040c02515005c00a010140c80d1030002e01d2003500c1e40c1e0b0030a00c02c41c05000e90b00c00c04404242c80345803040c03059041c60310300203490351548402e00040c00180c1e0400d200c042da246040c0e0741042c2c070082036000240b4041100160a415020000300004400d501007005180c82882100f11481e09948023101103130003044040c02052500103104510000741044007560b04889241c80141c10302c101100501c0032240c0940d0224007080e603503900100c050b40940181c00146407180081d15017985861039001192003051041c07482c41e83d000602c10304580c014a40d4456040184003161403601e850b01d49460b5203a030310442070340407503d40d00020720001d10008480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 125689568 1250 125688318 125688331
    0x5070306080d050711090f040516030302030a030b0303282a0821010e0a060608070806151318060b030123040603020603160807030207020604050f0402070c0b0c07090203 74
    0x404080e25500ba007110540c02151080311040305c040e00140380d6a403180082c500403040d40c40190500d050500e01540340134400592141d05880c010000c00119401005031195030549003404144a00b400002034114458201c3da076456909900c07032008543c071010140d45011142d81c8072001d0b510000b103403001ea00ca03002004080045800c8069000040001000c1c00007111040d100b103401d015001540110540c5c260003103601c0842e020100301344d401c8a030003400010092030070104664100001d00402c04940100018001c0001070788540074605540125400d200c1c440d0008510b40e078079141e0f070b02e0510a2100300a0b1a01e400c04101040d03000b412000c40381201c82071460900038034025000f6030340035020400f8880e80070780e4a07800080035865000065104100c40c100c60b40241744440c402401d64040600003104052050201c0710043c0c0704c007000c0750b068031400c960700607406000b440000c01902c50800010441e50312064002164010301001d00003c0700c0c861309441000b03450b01161403c0b4001103994 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 125690818 1250 125689568 125689573
    0x13081b0f06090c091501090e0403260402010c11060c19021011150903091206042310021b07060903050c03010207200102010603080a020f060609090604030f0e0a0b0403060507030608 79
    0x100d1120717001c40d1010b060101060601c0f40c42c2c00d40c1d885102180a0b0102e41c190040b800c0d080b5600004110101ea0a540da06484680d1301c5600309500028189404200020300c0113050490300c0781160b03191000e032807050003c0401c070b075030f00800880c1c80e46945c403003501c2c202d0085603640540554a4001d2100100400d803100040207040d03a0075000e05140c42d00074003540001e00003009013801302c2d242c0ca0104030115440c50002c15590a0a16250b13004152070b040d10410648040080f064030140852450715440d0703280ca0150b1600d506034541180020070295000180c0700c0c891002424942050045007141d009a0685031201e03444003d050030b0f48249140103081100c00805030048d5059040e8048800b2418400021042d0b120355889490ba031221550602580c0034000e0000a18401c00c08681d00510556125001c0d04201c0340c80796444401030002010300450100741501544513039525000150000c08402029541e00300c00149070f401404143ca00c90308100010750094082d0041d801160085e000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 125692068 1250 125690818 125690821
    0x20711090a09021305041103070b03010b070c081504030207081f020d0b0a09050612010e0d0318050303070309060e0313090c050904020d0509010506010c0b13081b0f06090c09 76
    0x411100000090007072081c1540c2d20060340158a0740d101401d28610071960016940c100380c1400301e00c405c00040650b100760b100c9403045c04070208500540c1c1c1115200045980c80d0300f840e14020301c5400c01c681004205218145982030b407180c0d2280c005016600a400395103007140c0726141d8079166006480300407010404c0703c4a0400981c03580c0d005140340104900d0001e00c2d02000400070325140c5c00c9034050a041074a50082c0406498107a500190400e0010020000c0441242c2d14640700d001c500002c02c28956030b500b80302240d5040c080903401465115003600d03900d18041d440035009014045040d2121460a1500000030000000325008240c00c00007400c6186c0c540300005020f0218644450200003003842001c040e91514000340285d081602c0300460355140000e07503203007140e00003480c0604211a656807400400c207100000c0b44c0018081c1c071003502c40768507400d080810788580c0040b00c400e0301001024a80d510ae010400b003859036144c0e07056481e10707162921442c0e601e102c0c940106d5444040b030300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 125693318 1250 125692068 125692103
    0x1314070507030f0e2101060311120606041113060302030a05100303050d1104080102040f1403010c0c06020706090b0708090105010f051003020306030f030721030212010b030415020a210207 82
    0x12420700340e40244415217a031811903204041e00c0c0250548036140c2e455900900411102d80b00d107400381c00040c2da07000100040c1c80c250a80c2c4090203090240141d560308110348681161f00304840030003070f5420402081d1660340b00000d000394400c5a8105035030f40381c031001c94889a5010a03200840c0c3d01696070b6400c091505600348010a4250b602d900351000403c000100004c3c01c2c00540018000d0b018020845442d24146c2111006103401d17452113030f450312107651480c5400087c007204040e00414010b031510603070326040005001c075900c05002c40c6d020320200501c03203502c401c0551207158004024025643e80c0c5038916001462070080c1a8820400356440511910a0b406994007282c0281211002c2003140f50541c21030307000503425507400c1004103481d1101c028001200352080078510b400c6240414441d0308101204046c01031680c0181d00001060511010400d851b440b0001e90300b0856035074034001c4014218044204c0804034071410303503084000e000010310030703a4800c5409c01c252031141c50411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 125694568 1250 125693318 125693327
    0x6020f030130061d06010b070312020301050a060f030b1903060e0c03030912191214030402030c0108061801180e0c0d0b0903070b0709140303070c05010f0507021314070507030f 77
    0x503c000640b024010080d5100c81c03030400519001f170204d00340c10b9580b040c8600b0000d0401000345000d0703404500400040006888503003030003044034406c0c5440c600090704882d08070040c0580711807030b6601014207050043c81e03100410346801124494942040794a100c82142510f50040e20f0f0001d91581080c40236044600345540d0034030403400c148050f61102d650740c3c118039041044140c1e090329410171040e48000d5a175044254002d8100040c0c52080c2146810b80c000780e0340c1e0071407103a0f41c1d04111703141002c6816501e07000f90300065040340c1014102035603151098241c0c0b0300c1c0c0e402d41508001d800e105804445001c081408100c005003d0700e000348060154568802107903000e1304007032003403004001100c0070480b01d800c82c44c003d40080e51001c0509280402d861601c0c507103043d40903ca0f030400c004480c002541001e03004119030003030a203140703100c074402010380c0e09004814010790048501106009202d41503032007003107919000d00c2c002c04c1c1d5840d803c1c030032100c0340144500100411695240812204d009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 125695818 1250 125694568 125694581
    0x51806060901350a030305090610031b0b07050a02010207060f05041a040302031c0305010b030702061503030c01091a070507120302072405150108070e0103090203030706020f03013006 80
    0x220400014003410080c1618a101c403e01d0100c2d02942003040e201081551600030070390800c039924010000350820315151030544045200080c42039815160385058441d0351107021005048040a960303c80040703040c07241d11159040004ca0041c0150f480c08589030380110030084407101c2a43d20541400d00b000455a4401441248030100c400144000001640c040056030410910220502c000416450014040d100180c00c02d241820f01071003084142e681c005034440c0d0104c10200c1c00c40c590b00700300d00400d04500c961054040c01c0e5080042140910150125550700048ae08150b004184d4899004903001e0050f00380c02408030b03010403e50b07502d151003a0040c0c6601d034050100e2070906c8190501181c02e5070300102c891804c1c207403207204200b005001e034104420861000c0c21300c00f099213011607006050030001032aa0313061580d5448803005549003002681c0d40030b41c0c0400c0440d6584244140f0032103a40091103042840302062a10050a040302c00c0300304101c12015040020100165441c5000f4011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 125697068 1250 125695818 125695859
    0x5100b0714030f0408070510050304021e030708030414040b030706081b0d050108061305280803041b060201090b04061a0d030905031204050a051014030a051806060901 73
    0x10300caa407100c0075100c18030041c4980c100382c40708907075900c0c90940c0040c108092036008a100c0c2455402000c081a0084100c07584164111480030800c240315000711030f0180c451210503014481c580020424035000401041540c00c4240d400030010410070412054501c5000c10340c1d011341008004000da2402000282c0c0c000040c0c84904000c904031061400c1603410055a4801040c1c503580100041c03803080c05520780040c030800702c0040b1402651180c5a071880c41010000c50488801109480c01080f103a4001c000c40d0b201d0b0405e5661300701801d011600340c40300c110741c005810250800054942c01407080f9000f055110900300c0351562561564001410300745130a01882c00f00310100295680c5001202d10113a1081e141c0359281802d19090501e003060003810310070444000c000034400f0b03503100301003a4110f400c101d44060340c6c4884184120b5003000d026210070460300005c001d103c541c40843c1c009074031503a55142040e04640c00552600e0341d801007910b02641040f0882c006000c4c2c1490301040060040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 125698318 1250 125697068 125697083
    0xc0c010b031c141207090302040b01051e0a0c0215040e060604080604080313050f010c0207050114120403020a0206030a1a01091508060609030d022113140f090f071205100b07 76
    0x1c04400c9088584c20301121468001074101d141130003186858031030741c150307003000b071810781d04100c0d10b01d84094a40020b2400f144d4421004201032080301c2c45504890b00700355000c0c0800e0700040807100c2d0414542c0140c05a1140081c45400040309400c26400b034074102e03a2890700404494569446030581075001603ca180902004180f20300070410800420025081078000040c038010f0441000382064010b420040c1009200500d05010382c292a05450034403859052003003c03611645400d902c0e080d4403803002504031402000304824014a503021009038a480401c042c4e1100000340112020f2150b40240c640030f00e20800d4410f4050702c1203a00c158400030103008280b03025032000000e0b1800501c0d096440060340010a0045030f08002d9100302c40f11010135150b20308142e200c0101110b05002030103a1003801c00307258103039080c0d640c400d400d064402c1c102400da89154101002c2e001c035a038200b10790040c08580e0403071040054000f00d10480340b1a194242c07440c41c046080c01d8404030260f1191000307503482d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 125699568 1250 125698318 125698327
    0xc06060b0a05030a05010e070c0b190501031211030a1d010e0901090b0406170d0c03030b0405040b070305060a0608130201090801060e07180b0a260c0c010b031c14 71
    0x1600104240710040c0c07201c2c1c1c0c89240644440c000d80c0c005070084054200c84000340204180c00803291410903900c8511b000c0d0351755440901a60000314502c2c0d21030030b03c0c00d20300008244054044840e56446007981c884c0301030700300031485990302d11504049000003000f00b0035010700400034020751072103604145016400c01210800040307018000384c00c000c0b10103030381e4150110945881c4c071800e00282200801441d01c2740031011700c2910f8500710304c902c2082c080c85c0b04500707040510070b6000d0701c8a007400600c01c102c5414107080240c1060401c0f1103c074013103490000881c2c0d0502e0142d034004e040780c0d016030f20408241d85120300b0000794214803108034103101c10b500020808103020300a900c05408145285031b99840c1c03400c0c0052440170500354600106505040c24000314003110226610700105040080700c440707503140e02075818100c48800c85047d030121802d10000040381801000042c1c00b0301d0081c40f440c02c20608040e103800700000c0e1084000804404840e186014100c0c98111440004010b402c2c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 125700818 1250 125699568 125699579
    0x60e010f050a02091e06040b09010c0f050d120216030e130501080604021906080c1309090302060f100503100c11071202030715020d030905030405040603060905060f07020a030c0606 79
    0x1507030300c190b8100c04100d401140005040c242915210b0550400049100e0036000b0391012a0680c030441c0203507104048006843c44260740100409602164450ba82100302d80ca40d0078040d4032402c0030700c0000d0004d8010603244100506500035176607030380184d020090f00b00c0c3c101e560543d000440454400e810080e8050124906045440b4550081903e0009850145018070400c041c81140d600300c148590301144090000c65405001550b00060444c1c40035078039a06020404002106a4801d0441505001c0c8080c101580410b00710300545180d030302c1015640750303480142e1f030151185c00b500e901684550351080d000840358100000440c186e0501050701765a4040240c1006c00d01c1e044020101018038445045080c00c20144000340828070400c3c51540c2d501200035124600280c80302d0405454012000501c00140102c600800c4000c00400156580c0c0c40c0031030151503540e005a0b040c2c003840001800d80e00190380d81601c02c1000794042e21342001c0c19a03041d41c207202c5000007a070350b1f0703980c0703202c080b85 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 125702068 1250 125700818 125700821
    0xb07110d2a03121817070b0c010b03070501020f0c010302030402060702040204080d1215060503060121060801060b0702180a0905010204030b090c0301090201121d2b020a0b0103060e010f 81
    0x100c889071591084921402d40c00e0002d5802c03800d00c804010401040002030007160b44840700d5050740c0182a00c0c6040110360320344149001841e8000d001d554000184610080c00154012050440e00360b054400c030999800041ea00d50120118644180e04a8524415158070a0b4020f40d401032000308071034100100c07600400c0403600240c10500c95544000030301c00d60b494000d032000c4102c08403d1000d2041c01024114503c071b0300c0c540c0c41510240040480841c0043e030250f52006032000d4401071144943c400c83c10540080c100300d03c12501c03a9440c2180c08078482180c503084880c07898000c0c010320f18500174080490b0500d8001080310b4a1142e590b003c1c003000983c02e000400046002d03403103030b441501349014554200021307607580c60301c00da16120741c020050740c00c24894001100003d10000c0e1520490503058090f02d0540c003040654000c0c0d00000c03124206240e20340c6c449940c180e0f03640c40041c440110603a500c7c0300700d150191400d42c03650010130006006401000c1c8480000f40045140e0010059820 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 125703318 1250 125702068 125702123
    0xa0c05010c030b150315040203070c050a060c1808060105010c05241b090a03110d0605040f1b271107030e0f0102010204060c02091f090603030305010b07110d 69
    0x180000d8480c86040c0903840c041e0400a44d40660492143c5181000c00c503262802581c2280c00340038503008000580c5181c050080e48403803c0d00724043c3c80000e00c1d0ba01d0000c00520070501c1110115403c2c0d21820756081444d007092059a9140004100300e900340001503400003032031041100e5510400c20301c007540460040c0080b1802484440c41502d50500522510f50111190f404150100d800e016145051356030400b01800c0306c0c1c00c950030803180c0680c4400300724845a0a0ba010381481c0c1400148170030000c2010b82c0c0c0070f02c60300440c25140e0301c10001414201c00c03446031107a252142d082120f45050001c41000c40c00051414090001703080c4462200c030b4900f5040039800b680892030001007400e4a040607400020116000d00c02145050b040040150164a22a030060b010348103440000d68100501b440d40300c523421500d01d60314865903030340305400081d00080c001103000904220000803440c01c00300942c0c2d05242c2c00042203c180d020101071102e448070480c82544c44036451000c00c4c240c2c04600c20882d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 125704568 1250 125703318 125703341
    0x30309210f060703180b04030305071206080c0f030105100e07031508160b042108070203060124080c030109050907051309110307050904081b12040323060c0a0c0501 72
    0x240b0301442c02c0040a81280c0340000c40031040e8212140740390001ea0002541c560007641800c00007140d03112100101c840d2160746100307940503490030750007103018080003900d5031401504a0303080195a6109083c14240c0d07800361a908050f00102d001444548240361030168880880d10b00006c000c0441c8442070155030680d4002d5040d5005880fa02c201403c2c6000440c019050360a0110301d000c1c40c15806010240202c4140b9020350410348040041100400c2107074501a0020211074080d616a40a200804d01c407030383c450800a00b04203401e035168000d0034220b100341507005407141141c0c41c11107000302078900148800c841e4059803502061550b40c800c41c40c1500802004001980442d62428518520300b142c0b0303240c032075031010b48200320300d270350741e402140d071180d400b2080741d0310b9507684008011640000001d5140138015110412030724000c400140080b079019030040d00ba50408104c0300220703070310400811142500309030000390b65070404d98001c1902d4007030ba180c506200e01c6940c4510b0300312411040304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 125705818 1250 125704568 125704573
    0x50a06050910060e060d0207150501180905060103030c020102010f0c020c0a091a0f2d09160815150408070f051c0615030209040b010f0b09030309210f 66
    0x910041c180312400c0c5034000c91541101c8025800c080000e01001c0c100b0700264032a41001400f8180d400381501500c3c14141e00042d0081409000362082c0041c15017401115284d0f6940c1c1808038441e100c5014203c06107070010058032041c8d00310f80b005c0b0303080240c03a981a4199074a5014600308504680b1441000c42c08640c05000034036080400c010086031198024841103050135880003450288a800f00741080c3c0031150501410941004103001c0620b05003928610350000c0c14000000c3d1040b002c1460204007120030506a1795910301c00034080000c0702611002405610001e904203000041c040c042610003840c02d801c1d0429102d124426600903001207500d41c10490040003400303c0d100c04036000d054100c03070300b81c206010714501104569000002902c0c0c02e0719000402d60ba8a4a140500702858010b440308145141508102d03e0440c028841c0500c1c6566070040010309005610a0361014403004000d5132030405402e0420403800c15860203903401900c1115552503c0c03108014444101d04100007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 125707068 1250 125705818 125705831
    0x2106151b0606010f090e0711101506090e040605090102040f260105060607031d0a0303020c0102070e0c18120f06220c0b0d29030601050607080f0708070501050a 70
    0xc80c03410604007411450600a80c2c030038000c01e85421181d140103a07601691000515070340c81d801114400703c907550304d500900030094900c2407070300240c026480011b000348415110b01d03640c1d48100c8002946210303008843e042a4007180028450703401881c1c100c400000094107040e00c40c2c80d5840c99503401da1000b0180000c44071002d61058000b9490fa0411000000801c010300d4440c0114200e44a100c02c02010003030881c19014810b020300308464983c25000c2d060034000c6890b4900139596101140c040e50151140b50380009140c8030712000b0078400c0061860a90a110a808850228101c05004d4960051741c08240d43d03007104041140d40340300071103440203101700c0c00c01c0000b0705a00410b10014110b4042c210b441200403983d0710860074111801820500d507507540102c400001440350304649000346100c80ca84d2000e05030714000f03015006034120143c42c1541d0b41c4e0f2041004903c1481001400b000d420b020300c004501d2514007a200542c068490180390500c142e40311402c4680483d001d04403c0d94414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 125708318 1250 125707068 125707117
    0x5071a040303081006091203090f03080c1c021f0902130504021305040f0f02120d0504080118050c01031e0905070303111b09060f090405071a210615 65
    0x28020b60708682c00e030071400700340e43c180200280991040c0c007c07588244090040c000425105083e050010041c0140c4e00017400d0b1130b443c080320350b5802a004102c01c1e2062044d003984098500100b6280f8518540041104503810309022451130b5054501d280d03803da80c1d85200c00980c90394a00800c00c1d4a1505000840c2d151620400041000750010312002c50b15100420000440304403400d01d4150300b1040140d50500c40d4400201000e0071020000d400740604250445404c0d013007030240041c4d6482070002d101441100341340014200c0350076409099940200403422255000390301c40d00c14444e50401c0100c00305c1c85e00c4108001d0307901c0001c003101c15922026007001450b62202c181c00058614201521403c250301c40f8041c2801a44590940b0901803000420350aa45100c01032040354400b9000d804640f07001e050407a200c1d181d51080e442801c0c480d507a461030411021049034076010a842a251401c1409100c5c09802100100242c0e0081d8a075080004540c0c402805030107141c404161410f14410000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 125709568 1250 125708318 125708327
    0x1a0d140106020307020f060f0706050609090a020609042003070207030b0c04050609040c0e0411070506060303070f030e042c0d2f01090206220501050304080906030405071a040303 78
    0x850005610040150040c040c2603804002c9500150701203528001c5003c5071400148a84114007060280400c0040c0ca501003280d160402c0344124421580d070300040d035680050316112810030100950200b410003e031140d52a0591200c00701e030070f80400345002484006a140556842594203c025a2245008108000440c0c00d110340c84609040c1d203a050520b401c000c03600c207015940c0300038481c03501c030312800402da885090304440100d0000c1c018041d2010702043c2407034690218406991b0b03400b8040006000e4100041180c1c07403581e010305c200c540b002c01502c00b125103480400e502940981c86010600025011b0f519540d005a0031003c01020584009a01441c00060003102e200340200a000b0390212003091020040214281e010400303242d41d10510540104450840290701c54000f00c0c0100189140308010013810703801d44000400286c0345c4005465a0104a400030541c040c00c1200c0c0703000d403e01d03c1c00b86821901c0b07081201c4065440310800c82c50a061403014080048020800700b0501d50300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 125710818 1250 125709568 125709581
    0x7230706030204060f030c0c1e020f03060403080c0c01061806090507031a010e0310020414010f020a05030403021c02090103030206091b130216060501080616030c02060613061a0d 78
    0x80c1421843c2c140b411801034401c0d40f920781c51006050b5103000c00c3c2d421501176801160440d62145888000500448800700c82c200e46210a074041c01ea12806540ca40c100091914002c940640314500c81d980c8610703541405900210851049540360580040d803a074190000701c10004100201040711418454003a00316400100910101424101000000440ca817a80c1c4c040c5030342860803d4050540320007080c649628034007c041413a1000800284803c1c042805c079503642401d0342c5040d001d540e00001280c1d2051451009402504204000c10061a00100285409409905c012561602c0740c000a030b6041c0242d000b540903800c020204450420240a100c48000300c10b100e0011001c003e0011826808685e20309a0b80709900103005c0301922030001a12000a41c440002d01042d03031909011900c411095030602c004105504102024a010b40510142c02040d036005003016580d00e42080220488100704160940d075925010031003101d01b40d120b0b41903400903061107036a800325002e600c040328030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 125712068 1250 125710818 125710829
    0x3032203081c0b18040204050709050303040f08010b061c02030402010905060316090503071a0c010b060403051f02030f0a24030303060f0b07051002210103060f11042108072307 77
    0x18204c5107080ca16002c00e079a801a4059034001040c0c0e0300c00d40103481c2d485032500129418400858002000c003010301d601d20a45811000a204400d10081400300501510003160003440d43c0c00a0300d22404119030240d507100d4014034045019594078004902140c0c02a11050008031102c06142d41c0c66400c81ca100c401044150002c0c0b031080d280501061908031401803018ac00c0030000344c84030008800350820004400024001c80d6203591704d107030080c0d5682d01e41000c881e40c007148220340d100ba05594404c6c0c84c071400000d210301c1c3c03082da038102c00d44005203c948000014049074001c0c0750078100a2001c00806588a620005000c608021007425145031950041040d580101301250002d100800c6d006001c1c4070030a00507071a241d600c40c0c0c01c60040c03078407100041c0800035a4000014424590047c080e0101e07543d00c200080801d03440400e90a20480c0202d807601061a031120042440c145a0f0031400f50040f0042400c2c2202c070384d1c641600340b032400044240c1c0c450f80400f103007800385e040c0000d000070300c0e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 125713318 1250 125712068 125712079
    0x120e0303070e04020d090206040602060106030507030218040504022e141303020111070302130606120c09050d0201110f010509060c090f1002010207170406020c09010503032203081c0b 80
    0x107000741c401050000b40c4a84a4000da401040c1485d110106402c0481040c1d802413031750b600c039a111040207680b084248a10b400090404012884440c000c1c0f08885200d41281e010303500b401d08a030b09010107800040d100302d800988491513055481c41c04005042c40d9103001d9802483c0c042e46040c020700d219505c0c4042c42c03412008000350024402c041c07501e202101d5082c200003485200d035814050400010303500280d00316a01010000c5510303911760218050311050b44648180005c07079010481214080c1004030041180b00000344000d01c1c00e1101461042c0c030501d05810b01a00c0c512400b410100798280342080c6a44840900011100038071080e07501c04031142c01c0c03034148001c4500007104000c0d1a600e85002c1c4e44104640040f06100b9011101c800ba0008a900e41112107044115074540c460710070203005008074500b456103407800a0303940b030485800a00640c1800021520b0040e180c111182c09c0c0014212034100000040e022409001c0a00c8d510b51000d520084110b454400d80351505511882075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 125714568 1250 125713318 125713321
    0x305044202130905040503040306020a02010207060e0a0b150d080f04031e08040501030f090203030c07051003092102030403020a0e01050103060f080a03120f09050307060f0e060408090402070210120e0303 89
    0x100401414001100c10000c0b004c1080e407114289603046214580011380510b000007020482903805400070000b20344542ea00300040b00018006540f1404103003c01001d54041d9004144845296031558016800007003031a44a4006a591101d0a5000400708415844046410010f01c00508031440c4043c50464401440d24816580d16405110720300a040c18143c2d5040400161030b50f03544800c42203a40501101e5881190700c1402c0d5596a01303118082c410151843c034002050300c40c1c0501041e103039019034035400c90340855161901680c030b0403e0410440c0b20900c0000301503035070201640b0091041c0007000741c095040a00050659100350840c2e951803402000822000d80f001403070071401c80c1c152921a11741c940d624040009083c200001416041c10304481a0030f00a000c401000524403440c400c00449100c41e0044003520b1001d1405a1190410b800003004603038544d00511000600902c0180b4001d0305600041c201d00c1d2080b99500001c1044020654542c03003031250f0300300c0e41c18142c02941035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 125715818 1250 125714568 125714587
    0xd03031406010318030c110d0f0209010b0c0a030e130c0504090506040207020f090601030e060901060608091c050309031201090603050c1906050c240708070804120305044202 76
    0x110301c40000000c0c1040104001141801110344101f480b00c04002c0030540004039908200500c1c0389004c10070303442151490000280b080b4040e041b0362482e4011400f800e60b1210300d44081c1c92011000078042d800001450315a0910310861041c0003842c2c03007030b48440d40c4450401202d4800c40d03000602c124059881041580c0150f41e82d810000c0d4611812500c1030031036628040100d0160210520300d200f50f1080d4002d0125419043d00f091003a203c2644e60300f210342d65407941e6582d855090700d510900c0e00e07a540b9034459843d880b440080d548000001e044901e0680d00c00d1070040d07040d100b40d1105400035030304c000510030010705120744105150101c0b2650b400d50360854409807011003620860042c40303800a124040c820060007100d64140c400c00b01403941045007000c2d03581441d421181500095801400911046c5c01880440d000303039004982080307200e040110550040a0103002610300f4441501160701000074921080211f42e14404944100129032108005400f0301404250002c0e0040c00003504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 125717068 1250 125715818 125715851
    0x17130b0406050705090a03060606020c0607020a05040203040f080a0801030c050429010201140406090201030b09010608060114040e1003120302040b031f03051608060f01030b070e0f0d030314060103 86
    0x3001900094001000c1d1034031181607420707100308030406400c800060400014880c00d41e0040c011549503409a4030402140010080c0512415000a40c00303102c0b4103003030015060a601440d4058490704011000304d41540714003802c0e411007090070000841c2c410041c8100001850208000c10065800380900c1420602c1941e06d6220b1158404c5242c4810b000442c1c16071003500013503612041c085190415040c0360420401420680c0400d9021904144000d24207092201e0064104c46803681c03442c0581e00e80c00700444000065441c18009148180b201158134800350101c0c9000d9005030544e50402440d515107200c40c00d9031550002c0905206120402904402c50100c03a448401c00b42c5071100a503180c066a00c7d50801508090300b03e10921003454016214107000c28165901c80080f6481c0e0790b00c0027803d80d1107034002d0000501d54001d880c01700d46800c0c040d440c42008203400a203480040786490001c20078042d1440e8040c1d00103900c0c0c00905100e41d0101880d25007280003841c0a20211036102c1d010817 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 125718318 1250 125717068 125717071
    0x703020c0d0201120603110f030705061606090209010b1c021e0309030c0d0906181409040204290906040c0203030402010f020f010f1b0c17090d0204050717130b 70
    0x1c0c0264000e010210440e0b2244485408005281004010540d201d0400c690700c0007030f00b100280596101720000d80c0e14580007801800300c1c1d40040010f0320b0140d195044031041c1c203a041d01280c20039190300c030820041c5d070350740c074903034040e0699003440c1d92141c03001280403a81d00c000d240d0b032103240b501c101f2401c00202d2200301341d16000301c1005941c1e0343e0703525840c540b00d00d140304d12414643d041c040c080100a61590144009080700d00c07660701d0310385039298080c414a40090610500303281e00101c03804680141003005106038054002031000500001044500350381103000c1401d440600e0030000740a201e8900681d0003a00000140c904100d0905030b00d9019640b40300c040d20180c188507100042c0b2070518820403207030701e00c0c40301c90000f404420b4201031a80041c2801200148908100004c016940c0c2d02c6100c1603005540c0040000075a40107011044006500541805170030a0b0f0420100c40546c07a6070090078080e0400b80d032404070080760903c900c6c0c0d00000c00b808600c6846164501800401d5220f04e245 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 125719424 1106 125718318 125718343
    0x1611010906090311060c031902090a090b01031103040206041a0c01090b0123010e10050d230f0103030e010f030e06090f0c03031606020f0f0c010902010e06070302 71
    0x13a1592012111b0340e805000c28070000d10082e440441051000700f01e070500501e809490000314800540680042c0c0e00940c9401c4c0c500f140d564148503000013401408800c904600341030b400141a84514443c035610861180c5c2031403401c500080884000101c100c000304103d2406180c00d50340c0075000d2203000a200100504503225003d2440e0b080304500c0e0503501da01e101e49040c0d0810002d00300a80320307082080070500214481014511901c10200901d55040c0440f205003031004101110003440e46c1101c84d01c4c0f0004000003900000820391800c024200b4081000020303100b1001400902c6041e80603214100c02d0040e9228007060b100d221040b0311041c2c03a0320b0988001895620320403080c84100305011500c62101080250380134002c0600000403040c58040010400ba183d81c0160201c4000f076591040070038110343c0c000c0b101c14103001040ea5071505000d0b85440103502c500d60310041 = true := by decide +kernel

theorem cover : BRFrame.Cov 125539568 125719424 := by
  have h0 := BRFrame.cov_init 125539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 125539568 ≤ n) (h2 : n < 125719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
