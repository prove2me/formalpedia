-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0209
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:28:42.836028+00:00
-- url     : https://prove2.me/submissions/e7a6b470-9cbc-4ee6-bc93-937f8bc06bf9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 37410076 ≤ n < 37589933 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 37411326 1250 37410076 37410083
    0x102250b1c0c08090a020103020705030d060f0602010e060c03060111100c02010c090902070309030215040315021b0109170c2a010f09030302071a07060c050c07050f090402040203041e 80
    0x740e000000000d40e400325030325112498240304401c1d0421035a1500022240c0301d8590a113000350711417419281003459402182c0c04490818280600483d00d681900c0607a81200c42da64000e00550b100c898190352100301c169410307802d5000800010340307554003d88030300001881c403000302d81500c03c03030380d80c0001143c05001c9804010b0751146180740c09140e000703980d80c0c041c1c40c1200045107070241c42e980c007400340d203210b1100030702408080a420300c0c07620710303131058070f00454201200d04000034410104038020b51044044a1a21015028010b2804414030841041c0c88d480504401c02e4041e22000300959000300324810740c035218050b91405503604001810b02400509400a171a4400410024082120801e088010048181d50400100ba80000da0710b0469460580340000842c201444880300c0c418190050021414064142801c96000005011280b8028141e82c0b402d0f4503131040103260f0524560003540b02140401080146c40c01c0d500458016101e03030f1100107c00100c0500440c0710409641c05e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 37412576 1250 37411326 37411357
    0x1c05010605121207030e06040906080d0f030b031b040b030129031f09080c010203040c0f080d0203070b0901020c0d0903020a090c020303160e0a030b0103200102250b 72
    0x1048181012910704000b80e0416018225080c201164201c603070284503405070070010002d10b00d9005441e40022035003d800c04c45401c0c800d2580701c3e402190f4601d83c1d02002c0e00010308002504883c240301c1c0c8240c402104000740a04421a44000c82c1c107081c1c0b07030328400b40368010b40c0c40d1082d4507595070034400e00aa1651030311807190714a403092503114842503d03925440c02500f20a10303886c1c0c0f60b0300061030340058094440000801a006050000a038010381c1e008829944c0f00105000c1880300050305c1c8401c44d6481c055a0b00c0d6181c844140c42d885004c4015008003581c403d20003240001c610020665010013100001403d0042e080c1c64145070180307545e070010204411070814015421700c900c807035014002e961802e10258000480c025900d11004002044120030a00340b0a101441207000f114070500041c02d0f0f4a40d952681400101e440d030a00c822a40388030030780c60240d00c18000c80c4007184280e030140c025102c01c4020b8090301c030403c0c0c00c512125a00f5010394102150501100c1d026002c015030b000d084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 37413826 1250 37412576 37412579
    0x6090212010e07080903040e04170a051801050f0403020607060f0c090e0a0b010806010c0303090605012c040f080304080405040207030c05011d0601090207050705060f070c06050a05030408091c050106 87
    0x21841c82d00780180000081107282000c02040d1040001103c0884002d600320089a035201d00f09030018500040d05010641800281e08940c1544a0050011005e181c500d480080d40520015070b03041c42015a9403180c00702c20b21040002d031078510058407050340940c1d00810845c8a8000d07000071600d50807c1800031070b5401c1000d00c186000b484140768000a070203010020300c0035480010749100001043c040c100b090180b6810201413103504007118090344444184100d50f11098500d5104803c0701c290481c500d0f01118070308070884090303034041c003540c0c202c54400c040400c83e86079084070307500040c01594000020000003e0310303210b038801070166a010f82e58040d0445010318205003564543c00021740a010880c01c1c940001001050280c112025030740c0041e0b6401251400758204007469101c0d503841400803c0301c0d601e801500000f0000c0d035106070300e80030100c1e8a43e1020744840c00b0b02d4440c000050b40a10005002840c940c6c001e01409038028501c0e10805400001d0a208001c80c05003115203944880d0b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 37415076 1250 37413826 37413839
    0x1e0e190b04030b01060306030f08030402010203160507050f0a0e16050c06010303080f0903180405090a0c030c030201021e060a020a0c0b040309141203220e0108010510050103020a0c0210030609021201 87
    0xc03921301418691405008540c50740c0c82d0082c803540e241034043d1801c54001b011408580c000c01c01c0701c0c0b00300800d0307006004400032820002e85490151060a001d8000c0018603541031410006240c10382d04450030b5140207484003038004c2401c000d041000e0041c031400300b01c9059880010851107000314440e0343c0d1a0124917140620000001d40601210059401031100e141e91111a000501e07004030180c1d000500d680d10700c0c0c080d5107003100071000078022028400c004414040404801000d0740e00030380807030300b14000000e24050404600342c907003032003074203d070300800d10060594004000711461807801c44805802a140d074951610199000c4012480501d420001c00b106402348192103e021078810120f00301a40202d512031040c4403440400c0395101c1c45c015100141c03c070182001c1e000701c99000b0302d551f8442408500900040c0c404c40c22946001e500020198801e0084800901050392901044070281d804c2c85581d000c0078107000e0900d43c445d00c010841c140381d0310141c0346040000c29048243c0d490f191 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 37416326 1250 37415076 37415093
    0xc1201150210020405030606010c02010905270c190509040204090c03020a020c01020c03031602040204030b07050a090812090909100c0c06110a050f030408040e070801080d1e0e190b0403 81
    0x100c0032070b0b81d00502041080307503400715403243d201c2c1c401c0c200192a40201d01c0101e40210064210f150f100581c13403040f1000c4081d42c40211b80c526804008c1170610307140e200240202e401100144052009400f00640685100c0c60183c5808000a000903090603251155041a05c02c11503840001030350225040a03000da040000c0460040b0030f002620b40790b80220040303500d0384201d40c2e02c426244030354510f1404540701d5074120342c0115080345880a01d42000c0318001c0075603000540c0d03040081e2956070701081900000c0f41c00c0145140c01c503205494411404d050002d418002045214240604604424600c2990044040c041d003103a42c0c0c0c0c0820a41890a50100c82400413154500d500911030340390142c0d0860100d0701c0001902c2500c50712171b501d1789844542449990003164a000c000428080d165420088480c16140144165544101015011079a41e040061030101500106480c41e500c0da0281541c00c404020141800c802c1c50756010b0011a03030046548039129010740003800f0001c1c0040030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 37417576 1250 37416326 37416343
    0x23070b040b160915021c03240e06012601030b060a1409070513030c09050f090c0906100908030304051b0d05100c09030605040f03110c01090e0c12011502 67
    0xa16040e001014190310080a9050f5406510903500102080c1c01d0342c18000c2182c1070b00d10380700c040e81404c422600c403401005084002424145c99400c41040030200f107200302030710191010381010307002c41d81d03a2100458041d2040442c1980307800c9241440901040303840e07103075400385006405908003400c0c0306040c0100340380141d00001c0070ba00303c00c02c0c0c1c80c2e480d070b10b41c0320301900410745241c00da07111900002000c0aa004651000380030880c8610001031008080d08080d100c1e03a00031101b01160303510350704001e45440f5002d1805034400e507400e000583c0c038508041c14200e455041c1c688418100d885d5034000d403a65106039015107955202d4845d42c1003170000002040f00e070210596202c02d5100713a80e518940d44c0c00755141c1c1c0c4041103440b100082c001c01d10480b046001541c001400b4425420b06050140c0d0091f6461340aa00207122900000801c00002500030024038040e03680081c6945800603000d51204090700480f09410100029400315407051003d80c040c2c20710584120700c2c0e0219070800b9140c01c882 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 37418826 1250 37417576 37417591
    0xf0402130e06010215070e030709020901020c1e0a03051506010f12020d15030f050f03030606070b06150a050d151a0306010207170c01140403020a0623070b040b 70
    0x40140d006400d80c081400021200d07010550340c0c6940300c8400517030400c00c88002e0300380f02030009000c00019551002c01c2102002c019001d0f02d511640301e2441400303034451010124050b80c0308805818480c209848207490f03890000510705080d40a880025880f00c89550064032960700c814030354032240e50400207054104201f401c0c549020b4036102030290102c1c201040403035080360701264141e101d0b4031640100d4183c4800d0301c1d40461440c4c032072070903107046466090269203903c126408010300420002c1142d01460004101c1400c00044d40d59120b1072010040199401015209881c004849240301038141e206190312480d0b2120101c0a4000c01c880303443c030109079104090310007000000c80341020031407410180c1c12090b542c0d545080050b807802000b6800040300a1504a04042c0d40c5004909503091050982c3c4032410f180703490740040018011808040d50000407a401002003d01820f0899002030100c0b088220341c543c070007082c05541c0c01c85c82d815103001c0b642c0410041044030f45120194000308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 37420076 1250 37418826 37418831
    0x5090a1e02130e0a0608120a0f0e031b04140a0912030204240c050706050a03060e04150513080d050f0702061e07110601080705190810020a17150f04 65
    0x14090002864218a200d501000700f800c0002c141c0b032801940050340600324110072070342d20b80c42d440544042c96120f0300d10800011100c0c000c141001e071080000b00880c0390014004c16070107038890855410010181052980a5074030252582000d05044005114a480707a500203015070f6142444003c101194881804140c4104414820b07682030100003200441c440c2c1e02030003014070f080c80580740108051000341c00c900c505003000450300da00c003000b000171030301d242c0d010b205440d9210102c03200341c0000d580003809140701421140448161368885584881e030781c0c00c07140c500c0989807030f81e0201da40442e80410b00c140e16a030030400c1803002c3c0c00d840d540204052004007000d00d4108160b0200903107050600c03444285010100b00c01c075128510745114110020705844840d41d5842c60b490750780c0002d1083c1c034021b0f0325180005040100030070410045413a48805040788400c100000d030000e50024002e0020b008402401d1858054081d621030301c0340100c1c0840000340d001d4441000411100c5064191140d0f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 37421326 1250 37420076 37420087
    0x102010c05120408090a0902070b060f0301060806010b0a02070b0301060207031e08031305011b050310051005040e130c0b030a140c091c0602031317120112060605090a1e02 75
    0x241151080c0350f01c03d8024140b03a4481c0c000c5400514480308a901c2110aa0b00108003407062044481000e4010709088400d0f1007008042c500f0b25098401500c00c8442c0790700008010040704401100414180c1c00c00d20598121980341d10300420160020780000e401680305000c24000c00940d443d488038400d031814030b1044141030320360702c1c00300314403000b4082088401c0d240d1000c3d0030010b00f5003048000b04c028400c400d401036040b000040c25078004807a0700240c49440100020b50742030034070580a980341182d5425260a04150b8210640000a001140fa0045540c00c61011600301907566019003041c00940d0381d2070501804200c150341c10004e1078101450410140003054003200c0489458407800d4507a0411050044003414010300c041d20003501e0540004104040700803a4030303c1000c00e42c8115000c2e0b0400600d04440318090180c4060254800707464001840384c07040c01c0e030000400501c038010103e00700d038945003c10703071820341a1085c502031a01c9026207105010300c00f40016011030750300400c50600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 37422576 1250 37421326 37421347
    0x31403031003060f151206110c03090603090c030607080708180c0f03010b0405090c01020706020f0607110a051006050a051507080310170a02091303090510090f140102010c05 76
    0x180c9440c0b0004209039900d0780c4600c1c0c8900e25412991607400d42da00b01c500d036103503140303512459401c4802c2c049449901d45074841007640c0d6a4401d49840704d21040c011810448408140000d6600c00303458000741d0b20800c824440a66410864035200e40034036902c60a650070f10310005071046002411700c1c1c0b03010041102400c505c540000d0300345101c020071640b41c04800d4034140800d00428a918140b50032909103410049500c0001940228104007a400c075146507540301c200300d03219505c000019a45070028004900e50728070520b04e007103a1a00640a0710304151050780c51b54542064401c41c1d011250b15828100403900d42080e074140100426a081e440c45044542550041d114040d0f004280010201c0451030f044c03e80c45a2501070100d14031100c1c85150340352289541d03041040422803081c42224000383c0d8038002c0000c912241981920351407406424641085000801500803004000c8420000940b180703001040b800104168000015101d242c800024203407450074681d8800c1c040700300310900ca507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 37423826 1250 37422576 37422601
    0xa030c121a04020d06080102042603041d0403051908040303061706041b0513050f0a06030f02040e010b041d0c04060b16020d021302210c040605070203070801060b0403140303 76
    0x44011200143d5915a0500b0f81000f017000b5000025198408140031a032601c00328848080480e108600c501020791070781e00a036580c480c038042c8041c0c040d000c0700452510091408140e030064070078144141880c580b56a020310800c108820000080c9406051005154141c4a44006003610003460701300001c581480035039a000140004111280b4451041440300c10303280c00d0809820010100c480300054041e4410141c03405844c82c0812000c04d001261803d64540f181c0812203600841c1c01c0c482c4001d03602000020044604215141c0d503d84000c1d01542d1764522a8201e81014034031f484000d01d0742c50440744e02d060308111000340920300e40380301401440c0780c075810b9074030381001da11421a0700c40e500c1c03000c615500f0705200d00a404ca41b00b120300c141401900d40242c80028420b003035038210300d002001c2e8100b0100f825607100b003080b20200024881c9602c00d9004080680c005000c44d4413503680d40baa40c4d42140c450358400f00c2e201001150500801c072203010320820103180704c4000c1d82181080012030300c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 37425076 1250 37423826 37423871
    0x3010602120c0f06010b030106021501050a03141006080d020f0d0206160c0507060816020d0801060e010507050303012714161808012003040b01030807050f030a030c12 73
    0x41c19030000c250000e4a41c0c007040940b808441007800e55286581d80d40080c80142c10a010f1100035000d40034052a10154030703209941240c1000303004686484c5151030b038036080144003000425501421094800c1881c650060000501100004100e500214032000b03003400808012a910f50300300042e5005050f0f80083e6154000c03105901031480149030390300a485109214100a00f580100b100014681b44c11904403846061400b500301030299101c5812600c54845c00003401c00b02c2d45410051040a00c06c2501a04041c010305110b46484201d403241d07490f54009a02000805241d0f04000c055100c0280d5280800010b0000a2200140a01c0005660304000380419034100c1c04001200e0141e229242c0740007000c0c400c0b452800280c4d1111400c0b406850203202031070100c0b000960503000c1110382c0303045a10898100110007442d900703580e1001c81e664401030701500c1902ca2032201c21500942403008100e02c9100340c0307000600c0250386038042e041480796080c0c0030382c0502c1c0016503650704400043c40e80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 37426326 1250 37425076 37425103
    0xc0a0302100c36030501090c030308010b1903020901051309060614030903030403030c120507030501080d090609050d050304150806040516080a0507030e010606020c09090d09060f09050d0305030a050601020303010602 94
    0xf21260501801442c4100558401742240d82800c09074424440c0700d4081d041542d0299661010503078968911040c0c2d442801030034661002a5120340840c3e92180d806040d0301e820501d4003501e040c44030f01402c04080419001b28445a87e154010000c260300201c9040040c215903490604500d03160314010303207070700004201074107040e1500c02840d1070900c07807074440300450b600b60400c1049003440320300100180001d001300c0e0304501c207a80c109800c00f4081c00500c000c40d2a60355900c444c45003003105101621070404c0c021501ea00c404e02c000729401003c0088403401440c1d03640d0780142d03441c114040100b0b8030805028040070103140200c020b40c4a50100f29280c2c400a0311101040310386400390200c004060803609142507519020b800304585602103104807800d0301c11516050191200005d90f0303100d07090300d00d110010071403046040001031701505031034200040d28200000e0903659207000c5807030549642001c80000d440081044101c1800d4821160088800e2008504641c1061000f03555040b90355a2403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 37427576 1250 37426326 37426397
    0x370f08040302010917030403170903070215070c03080c07060302120601030c0903140d0210141810020f0712030903020714060903010606020a0b130f02040509030c0a0302100c 76
    0x103000d050007504440700080d800f00301c40c02d2601d0350604802240c2c10680c4d003200015960070b55426000d25080c0310758018100c00000e1458003034070764200a4040c81b404521140303c5414840d90020030a0001404001c42c0180a41950b42d0201d100e0103040c0441c5401000c14148107102140365a00042442544040282000658400c0341c0105552400c200d50008142014a5542036030480c404a4100010031164088030652200140c046056500000d03026001003500c000140800021464502c000d00260081d21608d00d0000140d405aa1204a4682d440c0c07000003590410028445c0d60712060303404c10304d403c01c501c0900340d4000b51528254841c020110f850300c00c01003c550f990804441c02a44000c000b0841d03261741d10000303921145644c1017500c03030608100c009051048080804495964018030740110031883c0d900b000300a00700645140c00c01d10046c409019040c40c100036001d00c0074000d0f0002d00b1020070419a10007500d0300c0b020380c4820004907200b1405a2602011255120000b8a805 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 37428826 1250 37427576 37427581
    0x301030b04200d060c14030c030a0c0c050d02150a140705090402040906080607080912040902030c040306051509010602010606090504090501020910031b0302040e060904050f03370f08 80
    0x410340b01c402c9070858030390041c1c2d850884010898641c2c0255080da0342601c5003004540c2d4200f402c0c000303000844034440e04120802c00900007032080d5110001c44601422f00c1d09040c6680d841d05490804121900700150380032020710380b01941c0080c48158400c00b01d06050040203928808040500400b40001091040119800301c456a540d015036001e808448002c0100c5541c2d0203d8a9403a80240c0d40c0304d0210742c16601155a403080800e0300d442c41003160109a00c0e00345801c80000080d4002081c220300701d0018480400040e41d10b0080d1030240d00982582000703240c0d1a0304002140d0410390180066a240590030045150046a203608951080350300107208001420054064821807440c0c03581b05070441000f00c0c4071030b05a400741000140c042d50380344204c3c004400c00d0f02244114003c11500944520000707030b05181014480307a100d4411320a13606038070220348640f4510b400a030717a03e0703000d11b68100098081404010b201c5645910044165040149492001d002074120070b90403c20040400c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 37430076 1250 37428826 37428863
    0xf090c010f050f0705010203010f0603020c06012c070e010f0f020a080c0307080c0601060306060c0206040b0304050705130c0e0901050f060304060b150a020c010207061407030c05010509060f0c0301030b04 89
    0xf81c4040c412074415441c2d44010700c0c03802070b000354001d0041c2c4240029450300405c885200340b00381c0e5440600c3c400149072603400c245800d08101413030100c00200103c51516400c0c103a841d0420540a0b000300d8030fa0341050340c01d07000003415201441c04203a0820881125110380203600180818441ea0070099990703071040f800c1641400c41c450a1005000c21500045180d000040041c842d41214004e9030301300a429101d81048900b05000400a980b20001b4041441124020001507800611410441c0c4d50703140d50360041542140009182d50005640d540788209541d08040c5200ca00c03101141c2c608115070404001417034248180b0001030050801000050400a203a8040081c42000420410703440342c1076910301e18254456050800140600038050b11154000501403041ea000780c4c5402c0c2c940106a20448019001090300381d080200000280c00070540c280310796802020a440035005900e40300e20741502e0968050b0070a40805000c100402c0440c60b591030035a042a40101c0729039011140c003c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 37431326 1250 37430076 37430087
    0xa03020c060103050c18010308040e06040b040c120609050f040f082215020102181504031704050301051003050309091302060c010f0506040902010210020d1e050109050f090c010f 78
    0xc224058480c035000403082c0700000407121443c4508a9156101c0035044080d508080020f00c002440954140020b0001c03d043c244065441400548000703400400d90b07000605447e210703000303000480c4207622800030644041c059000505507054040c0507034140301d500e017400d0751802840a0140714154409800f00240101118200031024040d05c0841d80440141d03e208803032031142c520500d0041207034441d654010700954582481d40e00240180262203800d001c851005903030100304d80b000400001c400910504c1c1c290b8041002e6001840d01d86051209250071541c02910b1506038044081c42007002035800000c668880c4000e4070106003030389400c0c1c541e011014003458029408030004c11100103483e415440700c10000e000705810b120584445042c0411100400b10107401a004144400b1707084200d50000d10140c0248000082d1a81d100d5107400f60b40d10040550403000c68840c8010011000305014103078005c03500000008030740c1086030710381d641e03052100c88140c103000c844002c0c9540540260b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 37432576 1250 37431326 37431337
    0x201080606030a09021011100504030c030e0301020f120103020f01090b040902090a0e0406021c0c050720060f0408060c090d14070305010c09080f0a032a050109030801090b01080f0106050a0302 84
    0x30305018030001c000000134000415110001d411f5100d807130102c04526845000c1c55014035050740354081000c44070f441c04c4450b138045120440d0159002c0002c00c903415207450042a20302643c540d6814039506510420545004581281d4100528000d050058001e00404c032002c5501904006a82d090788102081114241e544101d4001d15550708000c00c1c0503807500107000c4800d2115010f10ba031b02d144806c0c04211003041038030b80c0015401388440700000c0d601000b07400d04c000074003540600d442d0401d000900c00c0d03402503604002c0c0b91004901000100310811440760051880d81000b42008003010204084000e1402d0280035440104806014a0401d0003504081c0d6006802888141100e12005e800365100b07201e4448036100d0f00d0030b10246030070003048600d40254190b40c0c04401414000010a030180001502000300e000000c40350000341091080140a51181e00c1e0048190b1402c8607003000c0f50f8001c0c02003410320004d40108100308034004101070640d00c507824095292456041c1c00c0b0001d0160 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 37433826 1250 37432576 37432579
    0x1060c050c041b0e0d050309040b010201141f1406160303020d2c07120303020304030908060412080a1503141908030411120705010e1206040b06030d05070201080606030a0902 76
    0x5102220f1200300d01120702d41c000880503101d611104001c0b80a10001000b51440901550018000c501c19880e00d60882d481540d01440003088006450000b0400d900055404206401c50700380f005a2241d0402050402884080d000d014403074509804103146100342c031132243d0b0f40041c0030f039007108050199040e1058820050420404c4000e0980424281c1d20228200810041d41203841a0400c0001a0b1702d0180d034142c42207003090a24030b940c290065003001d0011024406d4100c6c1c003280075002081468800c9c0d01038840d4000420b21620082c1a548000d880600114245100700500c410b0341340b1143e0450790b0040310b04958009480299040040c41601d0403a00c1501d04496000d02c00010003840c0210700a00100c0c03170b00782c0350304108841001004500360058005120070001507008140105621801801861601000c0e001050800004540c1150043d000f201480700905007040100e21600031400e1040c0741408a40020700380f20801450984280c80004c001031100c5850707000022020390 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 37435076 1250 37433826 37433831
    0x4020c0607030608011518230f0712050114190801020c010e0d031e0b0f04020a0305090f2d030d020703020a05010b150702060703020c0910060e060a050301060c050c04 73
    0x40400c4020b016003114402d2504542c04c00d451060003004411804040300c85000c0240d0100c40700e140b41c072000d4448002004098240a1100800f10903600c410718881e4004a481e4011403425610180402602c45d0104003c0d40c074100051144a0325001000004e11003200d158428034031500109440c035035103803c424455400841c0440c8015015044000c5002c403040a5401c10184004102c0840d100203401c100d000d280220103481d4400345034005801c030400580303103440f041342e0107012074140d03800750120b80c0000ea51003003003201c1c082003405a4460366859502030301c42c0b003c525892402d40e0a07150b0f500828148000000c3c0340f0304400b00201c0301090a0240159200c81c524200a07446030410352060b07815500300a04041d05180008050303444006c2c418010741404195000c7c80303801d80096400310154407440450810380da803030020381842101000641049142000740c000c00d00804030b01d55600400e03040c0b100d040299040011f4906440c428a0403030800b400d90304106180c802d008030b104d90400d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 37436326 1250 37435076 37435081
    0x30305090a09060f0801050c1201061b050105040f060e0105010302010806040209030703020a0603051006180b03060d0b0a0c110309031504210e010905061e0318070b0306030c03070f030f0204020c06 86
    0x41d207211341c1d0200c40700500200810765945260940a10840b15441403400a03140103202c602c0c01a660000140c0700c101402810700d15a80d035040c21213405a0702900e840384c10b032590b9410881c050140700b00340090040213102d19491035001901d00c050280c8601d11460b004141e42080382c13402c000400c000c5400a01c5043d601ea0f444501500500c010740b12080320511880380403c1e01d5000b5026000480000300003140498580080170380e00780c0018200710b6004590200d42804205c5e10402203000f64860080051120403840f000740021034441c00760740b9150404e004a0149582c0481c0460044038464050241540c0d989400794042440c3e140345c004001c001403002040c81e6001c210b6031410341003a21a84241900d6904005c02800b80110384d1580440301c180000d16964036002464200034081107003034556a0b10200c0c107040071899085101c1861010041168a02d0304004128420100750041e00b0040e08140c0960b141524a001c06800342107451042000c40d120b46d030403101451404000e40e00c103070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 37437576 1250 37436326 37436339
    0x18270408190c0507030602070303060b1b06100f03021504080d03020901183215090f18010603241502060c030c040501080a02130312080c090109030305090a0906 70
    0x6030005030282840c0654511a01030a600031061038042c0b50300240103244061455032030300080d5001c82021000c25454602c00965002503078040d20041d00044070050f12440b40089461910310014403100d40e0240c0d5030400c00c1219500001c2d4000d80ea0180c400c0c0c19807544040d1080081d109603440302c0d07507611400341c040d100d00e0341c16405852107100c00da890703403011820040c41c4519200729000304070b4140841d0414660b982c5440403a6102e0131108148001d4031014a0001900c1a40101c0ea0800c1c80500081c2140580b41c9050500e103e00003c03282c6120603000b00c0f0702c040024005016070818141da410780c515410f01d00006c0d407100d02c8014100410710a444040c1d0004491010031002d001d0300c00c035000308034000d5000d001e0302d1060364103209150415241c4401181c0104010740f121104d82c5e82002491600ca543c00c4515020310f01601031640600a41d080041c03441c2e03402401842040380621080c0b00c245c1c1d121403240c0c21030707416142003900d40c1c81040014400c3c40c0c09520140d182494000e000402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 37438826 1250 37437576 37437593
    0x12052a0d1103010e09190b0c1308030a110105010f0b09130b060301030c08060a1a1e04020705010e0706020304050a0e07030209030109060b1203040f0605030709030503131a182704 78
    0x36401c201c291b95410003104d500c098200c418640040c40c00c030480001548000c4880044e10034404026011400d807655442d983e42903504c10301c552800620880300300e8044800c00d000302401420300311a03c1200a161074901d46a6000c0c005c83c1d01d20910b07904952044507016504404803502d0300522195036540e5071302c2c088034412050b10840081d401100002994256581721b1a40840305c09201401d04981c0102008041c4900e4598a200e0702942200446da6849238400340c119241b0075000014000005005035181142c140d20403811548100030921141e20340400407011034115200031451a2200081074003e8061000345640661030100e150041c072585411610701003105071760506a51034186503050f02d070303c2240200d00c0785000c000c408010051055005540c06812468210080c0f601d03551820304540c08206210b07042140b4080038045086182c20504401d881c614201d443e0040581e000300e06509070740a100d200d410003c4551885030900703c200740e0000c4800c40c0d08071603403400c1d00d403c404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 37440076 1250 37438826 37438831
    0x503040c1a120c07020a05060c070e040803040b01050d05210f0a030b010305011e1a090a0303090e061f0804031e080103060b0a0302150f090a0612052a0d1103010e 71
    0x142c02c00300c0c0d000320b80d011402c0f0307085890480c2c002e4550b035901c40c2410240050365000704007800b1b8a100300c400c0090240361076259180514490705a25603281404e00309400980010f070400c0d40b1944900f12030400040002511091001e40044061184c200e0710804242c3c5000d030b0941543c800c5000207601c5005a4181d0120100705801d07241017020b0707621a42c5030502009500450007101050510512a000c0950081076440000f244a146004209004104000714582c000c40c0400c1684406100f02d50400c105a54000c0d8161100f01418001750489601c1207a620b14490510030f291000c1070070b141c4102212070b00c3c00001c045da040702050341d01004002500902c030603107183d880c110f90511075152640c415000c07a42c004080305d0900c88410b44400c1540d114206512210004202c42003494660f0800301d4000c1c03403280c4420901c072218880c12800d84800130841d81c00c0042c240b18142c420301c03420034840c42c2035503411070032a00c40c6002d2141d040105050207121005c144080000226218a50303440e92 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 37441326 1250 37440076 37440097
    0xa02180703060b040515090303040b04030c03060605010c030504121a0127020a02060610120f0207020f04051b0a050403060f0e150106020307030e0f0a03060b010225060503040c1a 78
    0x21241c1e480a107003c943c010303409500e07032000500da002c002d160f903000090900310000409480c6440e656051004080c0e116034001c541e158007138881001804000d12521b40286001e08102020184aa4005246229038081d200c207240e0309001a03014040084401c80030420450341038070ba1541c4031101555010b4150550222021101d81005620001e038000d0302d00340c0e0616001021903440d914200210403401280480801121411010403201640685a60b1640a0b41c005039604003600601c0740c1c100315075010500540c2400c06205507941100f5049041c0c1000c1e01c200d6855441240c811550780c8150780c009005c031401c00154221545d080d50169a9440381001102c01d0360309111911031140c0024032908001d80c206000c00008030f402403c1c0000d0369480242201c2c10f0010040010305c1c5000c054200f07030307200c6548900c000e00b00d58041100d05001c2c4001d403180342110385c074001c05d0740102820b405207008124000c000718080000074940d00b00504280e035604042803189414183c0607801c680c860f017 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 37442576 1250 37441326 37441331
    0x1050418080d0209031615080a090203060105010806060705010f0510050108040308060103020d0e060403030b1203090d020d03020703020d0302151e04381008010b03060f090a02180703 80
    0x1515140c8080c40d10300562948114414100020107500b50300030b410901680b038050048601a10409025850074400740c45048054003003d070141c100102007a90003403c83c901140b83c14040030140c1d400055040c1180c0d0709180040c45a610036010a005004121008040c1c1d070a116440f81544802d40190340b03c2c041c45242c0d00d0050340e4803c01140c0d1228203840140108150501040055110b5002400400d6005101040459a01407074134a8800200d4003030380000d647d200740c925545000b0304c4180700140c00b04011402c1c0418500007c801c91507059000b442a500b00350f84004160080c031011004540042041c1410211802c010b900e0340302c956482c001100040e00042e2495605610b102c003290b121020081c85d075515a95040254440405100f0810071403070004804804a2110b1101d00c0402d6040a04242000d11368000140001d400c03040c4940d04200d58000b0a850025400e98840c5c80c403040103000361128108079091441890000e5080403482c80306d00681a00100d400e80181401c0d40e08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 37443826 1250 37442576 37442591
    0x1118030c01140301030f02150a110d020c010e0d020f091e060901030b011203020109080f0d0f060b120411031209030c010206250513031a070306060509090c190305010504 74
    0x115074800040c1441c2e203000c041800180007192403109280607040c406070504a004030201d11502c400e030010300100303000ac1e46503c4c0c00540c2d00028816510f000440740002c2a10700760031000a40045103075040302e40100c50f1f200210056580c0d58801281900340582810004d046c0307240101300c2d205843c03c400d010403138070901140460401d80041d03070480e604440c00c1d210316401d0420545511103044002c2c3c04542d04c0d00004008034071110010071450007600300d0f0725a11040d5141d03460550708802945c800c141e00d002c2003004031510b084102da440034a00202030025580b00d1074004010749003c0e410035014450300c200d0021070f8100e400181841d4100310115442041c0b0343d401280e80d040704550407038400481480c483e003242d24000715400d0b030020604102c0d06010201f94202c2d110800c5038002d44507215440c0c0c9500301d030203402200c80e40001c0c00e85400d200c044d09100300a81103108245005009081c60f50000700c1040c146000ea410107950201078840d014002c4070000c1c0503141c00e0040e01d12485c83c0004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 37445076 1250 37443826 37443829
    0x1e0c0c121707150203070e030105010608011d09030901031d030403060204050a080607020a03031a150a09060206070c02010f09050904111003060e0a090201092103090b16060504061118030c 82
    0x960304040e030300034500902072000f4500c00c00a500041c10b00800d01400411916590740c0c2030181e140642559990718110f50724001030a41440c00517420090b2000c0d41c00184015010044202c800f000c2003030801080313841c002c554801071140d401da11000e4038040414007200300000d6400500481d0000c44009a0164646428a0312f6280565403d40940d00c200c040c080002d01a401641e400700c0d040f40b0b004c120640c1c40020a01846070703442c0100d10348200013140ca140e640c00c0103000b009020b0324030051880381340044010b0940410030070040c0c1408a55401c00380c2141c400c24100d405000080c169441074201460b02031490a403000d801c600c5144080c90f41351303000303100b403080604550301c1584a51203900c070411903000800810384143e040280784c100c00301c1ca21a00301810454884240d40806031554a400d0003009600c50750880491403c041010020044100b880c0c103020f980c20080000d0992107503c3c00070024440f03102c0405110707101003241d0214035a400306051402c4000d800f41c41141d28110b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 37446326 1250 37445076 37445123
    0x20c0a0501020d080a110408011d0a050703080903100e0604050706080907060e0f040507020303090607080610030e150c0405040608030a0c0b09011808180a03031e0c0c12 74
    0x20300c030300581c00302d45040d0006100e00a52900007424000004100c03d0840341910940e0054002040c1603440e11042026488413401c00c07685290b085014000d4891590390306915103440340b0003e00f240b80c5c00300d81400c603580c2c1408602c881c00d114040400030060101c0301e1700d48602048405541c14000d15000180550086141138810700c640c50181030b4103401c0c20400d490002c207001c0d080b030308001c1c40010b800c0580c580784900f5000d10f8081d00115120725058440514040000300104200700728501441806e8a843c4103121441465040100d41c0040c00440140341c07101440504d0150f5680000380b1800c400104000c000b030b6142960144038143d25544032030b17a80e02c03c0a046a000444406404020503131308240240c02044c00000810f0121501246415007a41005e0940e103e0380c001a510040904480551700201c2050301d00c3c40d503083c5941c40103042c1f0302003040840e1390250010f0f00e401c01148500c1d00d4030301040e40310305140460b94a500521030b0026110b0400c4601d5501e01180691011045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 37447576 1250 37446326 37446329
    0x1a100503010909030203070b010311120c0f040207060b09250e0d08130b0d050105040e060411060d18050601060206091209010f0e0628032a020a0f0c06020c0a 69
    0x252a594a580d19000c9044014440c0010075030840c00103104031030008a40c00c03400b50007103000b28441611054001d0800050040021080d03105034004e21078080151900c881d20400c1a2045800580b00d5407182401c10160100400341a40010110308000428500710001109a00d0036243d95000c2030b2500c90940304203601160342988003d00b0725110f800108244010f142c224040d80e00141d000e81c1e14810700300c140d0450186008581c0d00d030401030201d410a4400c4809600d140b1000b0002400d250300e91803007002080e5203241c06100300203464241030301142c11103643c5001010ba025000341c064180b05848a0b000e00924005000f640d010803009040001d42482c5c025480382007900d8400c442005640170548503100006101c0c03140c0301c444065450001a1840037001821f01c0e50421071031402a0300c406010342c0c2d000c245440c0008501860300d6001030b90000100904002d01c00c1001c0c0c0310164a440e102c860000c04015080c4030310070801031002100c1d01191401c3c0c00315078400603ea010004030345440d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 37448826 1250 37447576 37447609
    0x102040e010513060e070e03120702010f18080d020c031605090711010627060503071404110705061e01050904020603041101090504020c030408071202090403230301091a 74
    0x91100500c00781c540f02114081149448000082103a41c0700c036100d024081c2281c0c03040c00f05200003042c20490500340400403141d4440b41c061450880d80c0d5001814418a100064013040707070107030014414409526001000d0800c03502101c04040d00d00000a540d040441c40030382c000e0160b103110f41c81c7d064030700450500fa141d00038104101d9595040c0102c070f081499041d0340b80e2640d02e80c3d40005240c010304e0f518201d503181954440c2a4083d4184800060300c1407980118001c3e0320070b500030840c91016800441040900b288c001c5401880103900b110749010301c0c600074000f400345c6002e0110404980343d0a003000f110f1030b040034140d6aa00c0040180c00700040314007030741040d03081000030001069111405a00e2105042042980d030711800480d040fa082040d407517030283d00004050000001c03c1001d0001001e0b409030074003c0400300d07800700d1080d51002e0310040901500c8515001002591070302c07400099940c800b0a5181e44e91051481c01810311000e0391500c1100400328604241412407036001d20002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 37450076 1250 37448826 37448849
    0x6150e06060a09120305030a14011a310e07050a0c0809030a0f0309140306041a06030703060f020405040506010c030c0201080603030d020d0608120c0d0f1704150b03010204 75
    0x8400c4207020490348200030380010084003480108244040040b00c420080c0a5581c483d01c034a00710308800102ea001c411402c00650070349004010b0a55412004c11154030745080b1251901c054a21840544803c02000e00e500824800c0803141138401001140c1281c20340c1d601070005880700c1c0e6003a5118861701c0640b40006441240d0304c400b01e80400003c01c0099006000c44580c52070315161a00d0010181004600240c60801c0802c030030120044945000d00b01100500340b14140355a5040f9080043e60361900010203503000100140e609216250003550094402d00160030686007050081d402806120b115914100101d8180e520070006a52420b51585918114500540055425003002000c0c2c179070601c01040106022402d60014001007403a5400104105080600070760810003910142d001d210000e000d1400440d4000072049028002c900b07040c064034404440484040c1c00001c25425480d140c81c042c00208441c1c04006c41002411940400c00c03240408105401d078400c6102e418100d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 37451326 1250 37450076 37450081
    0xb0f04032a02090408070206070516080c030a0b07020c060301060c0303050a1415030118030c0c0b0703021c050f0703080f0c091005030603010e0106080708060a0c0909020a02070503031606150e 84
    0x10060790044d0001d01880415044c0000c590005116038480001116260440b0b602c8000b00788680b802c03003004d010340d40050140041a00046079581a10f040e000c1c10055050000c03511290081c0850401090302800c410303a290b031214400f40600e09000c0c01140024030b40030000e424000c1520a85905080c003451440c3d9030780b105541990072000b440116541075594018000e800980440c50b5001c8600c65191740340c20300c08604001e140300c03442e075100c11400c140030000140020b0b800304100d0000081c0c4902e801126802c07020484180c02a601c40c0926210006039603030505800c0713034005119010002c80b41101d565102c41c180d61a000c0c210350b0707580010402e41e0740300326940684003440e40010003400005030f94126074104c0b400d54135950b00982013600704280903c02c040040c072443d68018103103a800c1c4035084030050014413070201c5100d16100c083c3c0c04608a490342d4804d00811008000090440f03495a80f54802c1490811f850300c4200c8840b0300c1c03ca0751040c19072001804804031071109602800c5503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 37452576 1250 37451326 37451329
    0x15050313030e0f09070e0910050904080d060305030d0219020703020f010302070602280206091506040507020c0409230a02030c01030914010609022a0a031202070b0f04032a02 76
    0x504095401c00d600c050303c640c0034900f644913070480070b20600d400d5844852140c1c5070020b000580d500a810040b20b039404900900403610b0701070080e600540d21020050b910402e64074081c0c024502908000e1480c040020400c504111a1b0054003107507401e030700702c0b1450714020801684c4c1d52059100094001000b5614074645600a5028150560080d80301514199804590081d05102030500a180a910840343c2189560401c020743c1d0080943d401401140b401c40082030b01c0d038000074410340c482ca407038200040c030142c800e201c2c02d55032090140003440492454030b03104604280400302c00501640c02070103a41c2d076a0300080c0100b00690050060400d180755000110080c02060307600b5030307484a03048451051454240f080c10014003140301e0050300d03070340107101100482d40c418079072404030700c0241040443c1e0030f4041400c05500c0e0b41400c0c00e004010f08440c101c2e002c2d000b0301c0005407032004444204689402c0390b8000c0e074880d621035a01c1d10200b180b410350890034030400c01342c4004100035001040005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 37453826 1250 37452576 37452587
    0x905041407030e0c060c070602062802030601050409051303020f03070b040813030213020301140d0203060711121308061605030114010903060509031e0405031f0b03010e03041505031303 81
    0x142d0f03c0910903207070041c001d007003c40c210781d001c4240c110f1a1340c050107007008190742c148032982e00300e0000002025102d208031f20100c20400710711155844140d000000c0b8405038024801c880080c51610001d1000340340183c16132800e80d03060b900c103801600509502006420022040300c0c82668000303210f01c600d40b0380341c860310a02d0700b0850b001d089807148061b0100c05a40c4113003500181c9034098101603982c0d13040105164040c200c0d00c17207041c0136400c10403c450050307801080440c1d0100325450098a5402240340c0c10340f92002c180e441150f0a100003072810712406410a144040c1c885800481c0c0c0f5544035420b881007201c02400c1440005030b82440103004000c40c842c00583c2c1d110301490f10001035901c035102d100441b8419640f20000d07a0000808040548841c0683c100d0382104600d95400c1c04e00d408042a160310b10414420b800d00110f5270040001401d56001000650014001b008908400000c0580e2688030780104a201c0d003e811909804600c2503084a20402e118600d4490600d500d0b0782c199207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 37455076 1250 37453826 37453841
    0x1080a060509150c030106030606030b060702010806040b06041508062e020307080406080603010506040b010f050f040e040b01030302120301060e090705190f03060807080601030201052506020a090504140703 90
    0x29140103c2c0300703108240c200c3ca4a094091040519455035a5140c04805401c41b000c6600000a06080485038001a0b0780c0b80e080c0c6079520f80a0030003460036a03840380040c0c02044240ca03402c0d0703c0140814045125000740c0e020007030a420356150b41c11683c0f0f5003420001c00c049440a600014040182c02c3c1003100d9092008204206941c0102c3e0709005440c1c1d030300e2019401c40c0e00f00030000354003403082140500c5c09014564000200340ca041022a44200000f082d0343c110282880c14840002010302e0b1030005041201c0040c0a100030020710b90605140040d40004c0a20064005114603502c25004a00420407281215416100d181140d5810b03020b2101051004101e07009210090024a40a500024007103000c44255900d01d0125903002070007808842d01c1350420011903206050610003580001210b5056980900b0f0480e02e0741210122856542c1c82c07689120250348103541c100c41007000c1500a440e0031080d41d1503200d04551102e0601c402c03a03100a070000088555070000c628850b02a921018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 37456326 1250 37455076 37455091
    0x15070311100225020102070e06010c0c090507030501050109120605040f020d0507030c06050c060f040c270501051012090204020c01140f0703050c0304080f12010b070c05030601080a0605 81
    0x105581106100a400c00201ca030030840c10a4001810180c8212020400c181c1c100090f06000c0ca40402c1d500000d42d160203d010381039000d002c0750040303802c0d81e01564030300b149154455503c03038105480d003c40070003130181900c80c007010a06080001c00d4641c0141500c0d03041d699540d0300c4824120f800c3d200d840c05024003610130f458071081a400c980141c2c40743e10144540034044c000030300c0f203a451450303c11030100c178650010301000801d010790002d000011800903041102196001c810b0345071030034150340c0c1083c9a4400492058188402480604410701c0300d840300d00300031701c1000b02d41c2c1c0c0c55062181d0b400e400300d20780001030203200b11601032040719070010100d40e00151005050400303050243d421141104000001000c2d40c0c801c118504000045d103035803049682c035050105040141c0003050f20f01000c0c000420340c40010841e000800740d81d200b69444000480402d04a40d40e4030114010b2541c088c080581d190444110003080a060001d17645040302d002600a08603081d00c0d840d12001030001400d0031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 37457576 1250 37456326 37456337
    0x6050a030218130605010b0c060604020f090405150406060908010501120c1509081603020906030304060807112401030615060f030e010f02040305030a111504030302030a020c07090b0a060e150703 85
    0x4000c01c4d818400d071400f901e0030b507058070341e204030300c0c10502c1c5041c1c00245154401c90041140c49903070546074080c1c810160041d0760202d00350710399403015031040c0200c00e82541c104d8170307200740001d00d02c7c0d002003580701302c800380300c0204040c0e62520a11220114880750181103c0420001004074003401800400d82c1080351912070082511026868100003221b000c012080f01c030030406000b503160106405412505c110001c514103441c196020340902e2000303140c00d040c407400d503a4824803914103000c0e0405080420003014198089800e4402001a00780001d6401d14134000d1515480c6488442c01020303200580c848801e17400b5900380460242014a19020040d500c1c0c41d08100340709890b0024001442c03040d0041c3d6150021160000c0c10b0300031b0030120303450720f9100140350819030b5141500c040d040360701880d0146c0d403541c0d80424107006c2e10840741008840e1040d00000940c559140d07022911b8071000302c0c2d041600d15590300040345c0401a80c18104d0384500c0740304420803000c0800000700394841c800e0419 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 37458826 1250 37457576 37457611
    0x112030f0201020d0c120b010c0f0b0603030706020705011512170a0318050106030212031e0702041b08101a03010504020a1b03080108010c11030a0c0201140f0c0106050a030218 77
    0x1007419118003080c1c0c030011954003c1b2180700102107000344441d0940c02c1c6480b000a180640750040d090345941006000740422002050f0b981e1070520131180d80c5a00401c0c195642c40341490b0540c020000304021491080c0007100c00314001d68148007007003c030360300003c402c848041e4071400000d03107922418204061540d41d180d0403940d0040f0480000c00350b03010744000a030180c1396005028a14001550491080d0400c000c5625850210b030040c0c0309000700e002c50140c40e00721034070100d00100f9001c0c41811503501104401070006602500d40c0344a00d076000c00f8512450b5640180b40355101080c64500382440c42880140310300e08043e8041c2070390790801d24110780080b2050b6141c580c07014020304e041c0c000900340c2005010840090041d00c25491062a0012003440300c5620580c0364042e0740c11201c00c11200080d91000e5a100c0e10034200c1d07010b01007413030319075076091f910203c0e03415031200200c104e1950030309a00090a142014946040f250094500d281465801081c2d40703050300000c00340007000c601d803280d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 37460076 1250 37458826 37458847
    0xe010504051305150a03020607060c05040f090b100201020301050307030809130204331d120303070c030e04090203030f07050f072607140f040905060f16080112030f020102 75
    0x20581403080d1141c00007818201134a290b1820040c1410950140e024800c003080182c442c40b003103843e0540c0005000540e00f405440441e2244a1503101d00c1c501d01d804e52000c20712150796405607000b403d08690b104001044140c06909078002445100e5060704101e0080004c41d035480c009240c030003c010031603590000e035222200100e070456088800b0a501e21090070110200048060a21303100c114900044ea50800d0380040ca4680c0c440381b80d5502224000c0143d00d503031166114000d41400140a0b03079100d16242900401e0404e800c1e409900054070400d076200282094440d1840a80e000f030f0166140040304181c01c2815402040111428495a90043c2402d903061000901a0008078040901802000c04280c00540000c10b21049074101c40ba04100e542d860a4032055510010f4562440002d50040014002c01101002620a01452003008030f4880155446c4c0c0c41079a0701c0100040c120807608084a1418090040e01a100c3c5000d07042000b10f030040030000b00c00c26a80c8005413801420383c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 37461326 1250 37460076 37460089
    0x20c010614190819020301020909011e050603010f1202120a0305040e0a05101a0d050c040e070c080306010c06090f060e0d03020703020c040b15040e0108071a09010e01050405 76
    0x50001c904010100c07010811031800a140e0050324484600c4214a80e00301a400c580b6048681c042e2100000301e040740704d045403001c0d0107545203014010580021ba60b51504aa100c1d81302002240005403140c45011030300d03180000c1500c2c140ca45032580d400e411404d02060782099016008103036888903050615072200740d4200a041002882641c1e095200c600c2c01c44000700725403024080c2c9007140e051000300142d016a0380c0c5004202c40306500c100307801c1116440e034244548200441c409120b41804100920325462130000c0040390241204900c13140c0d180e0504641035009a4001050500c0070008600340d58410002402401c0c041c0d100019a064540d031040d0984240f00300465030180c03554880d04c4108018804500078081c28102986440c60599000351110441880c09215954862004415407264840e001c030111107450015030f1291115a4004202424401c043c580c1c0700344500880c2483e96603130380030013045110f0704803403c0051810041d01c64aa146030010304001040c0000501ca66644 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 37462576 1250 37461326 37461329
    0x2f03030a02040e0705070201020c010e0109080d09031401020703050703081009020705100c08100e040c09060f080c010e060304080304111009050307120b07080a060f06170708240301020c0106 83
    0x203100050761140f41ca0b0343c40806410061240381884400d2100c900580d802045c4014030310824a020101c1803106801a62107042c10f40004060703100380020b100010303070440c2c603000540f4029100160f405040d100c0f00b074240c0c0f04071403000340080c2040c84010300007070040e41e8181d00450700700c412200441d240d88001c400c03a001440306881e6903010009444410385180f1a0702c40d032004514210071a46480c01c90106040658410500c0d00c0620b40002000d0289400d0b0f480d000c0e002c4103409006941c1e548003242c0d0001c816000b5810b80340501d440420156001e058104640b1201420307a904640d210307103842d011504003c10075a800c1202c0c851000055803a0014410012a65181c03040c4260903c414145000c205405c850302180c80c1c03001110105566200603039000103103240a00c03850b5640e0001101a02c5540d010300e260f2031140d0303000310382a03411000065016244400e070343e009588a400c2120f000c20b050311903800c0c2ca030040003140c1014500c2c035001803d130a00580050b00e40703c0c9110041782142c046 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 37463826 1250 37462576 37462591
    0xc01050406020a180305060114060702040614180105030615040207050706031b0806060708031b19140304020d060203060f06040f05040b0d1203090c0905090d02060a020403032f0303 79
    0x5500d8003484c0c0c102441c400b0071011a0803001c445419a031340c4640d40c1d1410f0180c992061080a078604040d501c00044500d40350740580140006503407003d0b101c55412100301864400d4400c0703141c11503001d0081d00254100d4000a00500454560400d840c0d40030400340c2c0c400d40c1054080226130045078080240400902943e03070700240f02d014112500c3ca4078003410114504000b40c1d5004c0c400180d80743c600f034855043e0000795459494071007450703203500112604030700c4204a4022800080780d400781c086219514186448035810144101650005032008a034025404956014600301003403803540a5a4080c00242049000d988003030009480ca802644c0203400750740300100d05001030708007400303040c07100b0307400380c8000180241507612603072116030322001c482c20550369004500910117100c140f0f900070804020f040009050405e0084d841d0003038006020301510072400420684400e61086800b03d0307803d5601d00150981103214821200c000300600700350079202c4464850010790620045016580c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 37465076 1250 37463826 37463831
    0x80702070302210d0c020a0803160b090f06040b090118050d0c0501020c01020c010e2e02030408040b0a0206040c0e091005060a1d0a0b0103060f050609180a1505030307030e12030c01050406 82
    0x1c9104000e82d0901c48d8102c3c42c7c054006005001c4070745120140c15442c07070343c1710300e801606507551015240385c41044000403045100e103000340002d200311b0124050103240d1103402070117980030340154103146d9411004000c002e0b51003c501203080610070654001d0701481780c80094038082c10b0078a0070b400c0e6040640c20b910103964a985031f22160408005c84c0e14040e2849049000081c035030245024044100108031902940020000f801c10640b003080f1b40241c40305510f0f00340c41d0071540400030b564900c1298100c5a01d6400500450b1b65004480d0b468411400e0000074010001c00c0d007840b80c00340401401c0960020700807030b40461070b0b6103800c40c155140c0700390300301100940c81d00590303000c151b40d41c0b6144141030524101c020310240a06515900586605a0342c0d15510081e48010940e05c2c2040e02ca00c1c3c0e041008501484441c0c100ca41121240b241010700d440e0341251100c1c101503da10401c44005d002c81c5199141d100a4180442c40300001800c0d0b20940c2d00b4481d98242040c250344046174215822a03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 37466326 1250 37465076 37465097
    0x10302180a0f151706010501140a0c06060b04170c0603070f03060b0f1c0c0c02010e03101406010201061d06090606070f03050a030507030212011a0705070312020c01080702070302210d 80
    0x14002048180e418400045c60a54501000a0081030011900c450f44440005901c0803040c0030341e219451042e440300081007400d40d11140b80509800c980241c00081c158599142080c0500081303850600f0001840d40749103450381c1c4002e03511b0040c070101d04030a141d00c4110002d0410100030103000100301c440d40040c0c0c0c85c400d201d0745442d051845c1d8040e03943c0b1031501002001c3c903076100c42110361441d8203082c40000e0260010004c0e1402445681e0303a000c003420300c4030b040c005504900f40384c2e0040d5400c0c0c0080c041d00d07448000d40f011403040c0c000c8400c410403a4400040c418070303044410f15080400909003d192800300d840300f012004c3c401c00c0c180c1c04500002007283c2d58640c50321a1681c41810742c5030450070b148a40300ca1155400040c800e80b50305414215404182001324421540d000340d012084800c0560380c0d1501160841005c100342016001d4002058041e50040c0c40441c401c0007546d01802c509810b41e802c00c0b218240107104a0076980c615801c541421004020080c0960f4807500d6000700380 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 37467576 1250 37466326 37466339
    0x405090f010c021204030312020c030c011422020613120602090307050901050607030e010e04020406020c0a0e13080705010f0509061807080309060d090204140103060b030105010302180a0f15 83
    0x15074081460104642c4150010b84442079134800b514262070b45454002c81c11140b81e800d0f0000f900458200940500000401c1c10707400105510070300d03088646c04c40743c07900c40d610303090f20031000c820f4400052440a44c03505c3e040014a0000300401c03c1d0110b4507070f49a6002d0b00c40201d9400740000c0c8104540c0c0c1075000601c5943d514080000000508003200ca1000c250304000108200d070007002c90080a01c04680e40b0ba40082e0b01a1814020909014108540f100e0355448001d58401084054500468020b04007242c0820310001d454410f9004988030418401941d6404140c2d86c0007401c2035815541e507040d08506400c039801076070700848460300286281d0074802001008040040209103456221907001c100504011040d175490304421141c0c03d4880445c900032001901900e200294818a8400107401c1a14030840080c1628000d40080142c5402d04013810700f252800e0201a5019241a10244511070010050740c3d011098240200b01780e10b212000070181d0f14401e03420800040c50040a02c9403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 37468826 1250 37467576 37467581
    0xf03090c0e04030809070503030a1e0905090c07060e060705221e030605070806130c210501061404050f060306010c020d05250e0708060d0507060203030612030c1506040603020405090f01 81
    0xd004100c8c00b41d480d2062406010b440189005c4d44410580044500c07000c519000704500401401c0185c010081e40c90601c0000003030b60701c026130407241149000420740c00001c001503841d20508d03d0352101464044200c0400440445102d41200030380300c8000046541c6010400d4040074010b000c0c030304801d0ba811840c009007910300050422080018100030004a41da8041c61102071800001d0300069564484c0300407502036182a020f03600400118000b410114503036403045040b03840c1940e98540600124216143c5407240d48980c80e40070b000540c0d150342529020000355006001410410841042d55011904419801c00d041d41d19400224034805c5082c0f107400705181019a00303410407582800c08401045a01000d0000b0040203141c100040d0180c555070100c00074a9003000464034a250703141c0c0c4c000c2d640d90084400034090b011aa5603400c80100c00400c0c0c0c1c9481240c0780280104400c1499881100d1070018086a8030503110280080503031200d1081600440c040c4025140304452038841909 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 37470076 1250 37468826 37468829
    0x10603030306140d0b0c0c0c120a0c050108010602150a0605030a050c0405100b0412050111030f0108070603050405060f1504020f09040b0303160303020c011b0e010f0207060f03090c0e0403080907 85
    0x10044013a910340000c4e02c4c00c40c402c1d4010501c6803c01e0f22100d09030b1a06242480074032499801c64550040c120712000d001800515003813044a94a04150302c0e0310046a4030740c428400d240150303010411454002c8203020440358881c03da50000580c41d035031200005c1c03600740d104900f83c0302c4c2c0e04109409a00c0e41018050150722200541c10014601c4c42c00c15103001da48101d100d6004054600403402080003001c0d00445a40120085219240c0c11b00070171100d0a42c40a120704003840c416103c00140c418064002d080c45503030000701130001e0356242d29a80b0300424004150030b803440d10300c107c160850358403403024002840d000480306441e401c0e1082400102d0ba8090705180c131075442400041741d490381184d42a418181d0500c1d015840701100744800340546001d503000c00800000485211507980e00005900d03021034240d0702d1b09800c10030000240c1e1280414080c1070005003140a811191034001d42119003114895203161403601c0c0d46080215412900b43c9044001804003001d00c0509a0201301d10320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 37471326 1250 37470076 37470079
    0xa1e1104050613111308030c010b0102150f130602030114030c1203090d0807020607030e040507090311060702031c18060206010506040314010b0a06080601120b0603010905041401060303030614 84
    0x668200440080c510303c2503800440c20141c4c480c1c0c400c0300200080815640c102e5400c41100b9031050701c03005025142c1d040b66030313165215864401c1c100e0b141d41c0300042c040340d251418841d2205a4450520101030188000c001011030f0386013280c85800135030b0510045000b05640e8100c00c82045100c0101410200200d0049200301c5410b025098a414007000f2107040345000c403640789603603c4500e000b60307250290b603c1c081c1d4480b030301080850503d80c003d5180c00b008001218100b025695980080d14100d50030b0101400da02340b03031444080035081081c010302643c0d000030101e540c2483d840002440804800004030300240d10001c50441c007031010001f1402500241c00540348660500317000c00d080380206e20024081c0922040702c032200310350039071048203448406081c0440076519004040c103c07400554501d40010710524002c50300c00328500c030b20925100001c040602d5a440c00f501d003c050140038106884025185d20284c44680091180000561107a18080303402d515007803104038007126403603405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 37472576 1250 37471326 37471331
    0x501050903100b150a020706030f0509060103080d180f02030601060c05030906030a0605030a050a031b0209010e061c0f0506010f0608070c0c15031b030207050d110a1e1104 75
    0x144503039401040c0141c100c6900e000001c3c1025101e000150413100b0400000391900e00000c007078088603404034a075170a84819480602480c0c00851030041110030171140c503041d5402c4000140002101c80b8010305462640e0100400c48000b03140000b00400d5168802b2074010030810404004c500f020702c890360040069040040042c6981cad00c620707440e40f00303101c00035101c3c400000002d00d04816541c041d00280034041e04944040d030540c98020f0f41c07109002801c0d00440e03900c00100f118502c00d641c440140990140114096034070302842000c4ca10805400300750302c6240288054401407040b012920a50b0081c0d45458214016040203800d003003040e00000d4042c1c926400c10b11001d80c00c41051908650a80341541e203007003c900b4509211000d5412102040c1c05124020242c15459000b6070a002c1315100080000381d40c440d0203404030b201d10b0b10010140c1e007000202000700c034042e0001060420340303941074a542c0e80d03c603510204000f26007450859080701ca1a222424403120b40c5000000f00c8055508 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 37473826 1250 37472576 37472587
    0xc060f0c0f0d05120712050703050601031a0a0b0d09082b061202060702012001020a0905180118020910030c020105090d022e050a0b090901020f070609020315041506050105 75
    0x422610a080891301080b0501c00410b20441c803540d90007240050102c8100322605004000030042c0c10280c81d0907000a051044c154648500b0803020156040010400310720545402c00401058020041014010743e0303030078032140031800d100010500103107403084d20007540c014108080d241c00014546194450b29001c0e050160710140341030845c4040c2c040791916241d0744140b0048075403640e003044134209802030703102c0300450240540141248000750b44424004c02d032100b003030260300c8000101d0000d0002d5141d0041000b555078103280792528603507030b03000b514040550001c240306589801c941400665520716110982e035082c400c05400907200170250580200740b040c001e6450504070b001c59a4229254490041d41d0218501c002009043c0c207018041c602d0300c41da102c8000c00c0c51000d0140a0181d8000003501c001c018401c036650302c0401d101c880c0c10000343d03845100c004d00c1d04070022a010b01c1800303c102041001c0043e86403040d8407403c01000211103000f1034a050b6003141d07224506100c2c06100e17 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 37475076 1250 37473826 37473853
    0xe010e010f0603052e1503050c0f03040503070b10030605010b0c0703020105030604060e0c07050610080a030e01110a0b150f130203040c0b0f0a02070e0403021b01020c060f0c0f 77
    0x30084101d40c110b1401056a4035504031021003004881090084807a48420300200e0007000c02a00b01101c041e40b00c1d04444070700c035079000c7e819150100d4140c60001d00820044154040c94406550424054001c40e0b01f01981c907a90080c0001c029100d984c055042c4510402c1000201d001d500e0240810581c1c075400c003004114950307501d4005000081c10700c100070000404d2034031244d2086009200c44015500141030100c0d101d8120b42c0104c60541d600d0255070002201d0f501000f9022046500510090140501a85045880180a00002d4100030307010741c2d205c003090310412466103010b02034885030f469402c000d105404469010016680995080248249640d4813a07003904415030100001507541c1d55145401f4003461010340042c2002040469804a4855801c0180c90002080c1c3c0031600015101c00c12100f0b07070303001100c00030300690002c0c0c203030001d8005a140c070350340c1c203481801215144401c1f000020515040041001c05241000c1441301c0b45036401c0090780105268a4040c1c03000503070207079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 37476326 1250 37475076 37475099
    0xf0507051903090201031e0207050c030c01020607050d060f08010b010210150306020c01060302041d0601050901030206040302010c0c0510180e0105090609070e0d0303020403030305060f0108071407021305010e010e01 94
    0x291400515564075903c0c02903900035000281001c003403402d800043e1039100001402500804001d0321a445030b1103030030070107017070009182091040c144c004140c1d0b50f9504038200d80c5640240070500d0403e480d03850000c0c9200001040c03802a1208000104160303052074002450010b0f04606000f166092030740c0c41c3d000074400d000980c00d90760800c00141e070350303a0291750a0740900580c2d0700003034000d0300c0c02e07843c00b0070700e01c1000d81050202650310540e00241d07681c108105e0b04d1340080c00043e41c004002c00c010001980100d04802c0100c2c403a407806c1002558440000d0300e0480c8034a0f46101140d07100412020380700a195020018004654030041654105001300705600720040c40c45005a44150209009501410124141c444000c0408c00c81d5801854000c000e9000b41c84114086401d0001040052401c48105040f510b4107943b075941c56030300c00408803a80c90420602c0172071120b080206001580340c8040d0042d0045100c03501103940d5240038090000c0010582c400b800c451151801401f2614142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 37477576 1250 37476326 37476367
    0x31b0305040b16090b070f02011409030c0d0212070803030106021e1207030c06110403021e0d03050307170406060303090806150d0204020927010603020c0a020d110303030a0f050705 79
    0x100a00d540c40f40115020340d0038026903041001c40e10400301d039040400c0600008510298403c1c0c4c1d8800441d51040f203441c204e401421240b130b0781908072061600190414800ca03032041400101100d924424082c481030030302c815a00101c00c01e800002c01801241d80420901c01036201c00f24100581c0c7c0c1c98220205d407a440c508050080c1c0135800101c1034141441410104125a04901e0030415a42c858003805000d82c054801240540c10302c4521800002221002c0d8080403405072030500d0550140c1c2c2c0c202c54603800280a031003800a26400403800b401d40c004414420b520486001a0207825800e0250844a103580321804a51087d01000b0314220441c04c8a8060300040d102c6644050162000074041d0084094050b00913900440c42c601645118a0000c80d0242c06c02107552140d072252030490a0f84121030018040c1e074045560a40141002c48210825034001e400f141800c081300700c0042d0540e801a249680120340380c400d41141e040c0d60340308030781c6c00106074140700345002062180c0303c400c03000b0b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 37478826 1250 37477576 37477591
    0x310080615090f060103060b0d02040302010e010302210414010e010906050a0612200904060c030b030304050a0302061b0a030903030219020901060f020f100e07050f06040b030a09060c031b0305040b 86
    0xf4400442c0c5907900a8010038058000012481e44651014022100a42186c8800c0c1d002500ba2888a000c40d40030303101301c03009154042400c80d0030031211080c0d1400184040e10454041c1a04500682c02000c28403490b00742c03107207250001c41c030314645e404d080003a100041d0280a42c2d0749092410400301003d000d0184905510035840708119a80600080c02d100c2c1080341142c000981c141004102315459018021004580e102001201054414165240140d0241e80d400842c0d0170b40510151605101a1405505400b480441501c3c4c182c41c4d01e00304011110114003051380700e1414002c140c0c0511030241e22544400d00b0562252194000401c00001072084d20103004040703900c0c440c0c161090210095550541d0211040e180440314054010b000811118149002d05d600101d202c0c50844000c44003807400074205070038181080c58955207540b01510b01c84031259948850340c00240c49014021030030040b51000109440c0b40c046c080072944240a403441018541410400000c0f110061550014003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 37480076 1250 37478826 37478851
    0x90603140d0807081815040204150e07031d0d03090b070e060a0c06180507080f01021305010e13060b07020f010c0302250f03080c07080a05060106030209010309020402031008061509 79
    0x1c2d51110a00c0b00c0c0f03020707051245e450040017a600901500005040e00541c4251010842c1c1c1c0d80221941c89403020700e0080704850107a00011889680c0b00b030b00861025010740d4903c4406900e44d07548145001d4203d010b100109494556080c02e129520050b640e2050030380c1400c40c100001500028003034410b2547c600240815070704041c051203d1640008180c0e00a40d10850404020b1300300303c1e503a11a00e100d8208030b481a0070070040b040d0030600075624480510412520001d04080040d244d00c40251030680c0c0000c4a0032641307038000e9241c014031001b00012200d0650fa0b1800f40144002d80c0c0c21040707504c2c14010b010340f0010000c0c0e4002002228601c80c000c0c0c00880c074209903043d030b16002107540003040c4d094401c00080113122480005100f00301078601269581a5200c0e00541c4812003c2400360035604003400401669001c1e4000708548801494001381d02ca000394001030490304103803120030b10a81d00c3c941c113112203002001481c0d00980169001c100740e0b46504001449050000c007000b6030000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 37481326 1250 37480076 37480081
    0x807021c06022109070303080123090406090309120305030420060d05060a08060601090603020c0715170114031207110a1e0b0708030105010315050901090603140d080708 74
    0x1200880d0040d481a4003800070b55494114403180300b9121030402d0010f20100320400819400d80c0300154010489526443d40351440e86442c1c81610013285c150140851600803e0085a440d560f8405040c800d5114620005020710f01d0b09000b0040c108940009803510310000380d400100317801c1800c0d298003542c80010602003002000600c00350301d0038150401c2d006600072034103900c0c07904550449881803106a5407490fa559842d201140c0d540c03010303220180400c05042052203800d00c00c1e0010864550031504580b07907165564520b092403c030410104000580840800c810280c4c1c18034224010250754110481080390400003a07101c5007003074084000448002603a20400110a5960358984002003c80640c1c550750411f40c9013048081411440a840c20075000c540c0c4041001510113454201e0803950960382408019001003501c0000101400c482c4400000c8036030b540560305000c0c1401d4140841c00d245189030440c11200440540141c94001c1c02203140c0260380a0031702c80c1d1054241c900380d600da8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 37482576 1250 37481326 37481359
    0x503010e06130902130b0306060301020a050a0f020c030709050f07020a030203040506070302160e0115020312180c0a0303090503010c050906030a1508030c030403031d0f0105030703060b03090703051603080702 91
    0xb8003003d02e000390001e600c465140c03c030490f280c2c401c0e0307603c0000350156641c0b0758801d000c1500301d203c0c915103c00412401e000c0140c1252013078040780b1000c005401152180305d15000040d1806c0d8441d4450301c941030b00c07001007100310300e489031030543c121034540010085402c1c142e50294480c000d9014071780c0143c8000c100c040070301d4801c000440045c1030800c1518100c603296121300c1e92003a82401030800c01000031001002031307840041105c0e032840050036009003075281c075028a5402a2a001403612511032900d4508082e61480e8540c001103120341c40700003003a89030405050954640414000a00806000d102000e4698a003140e80c01810076a00180b03411000704402e40184071a007081407240b0001c14a00035070780c400001841520b0094440e140400c49907800c0002e10189a1100c40e08914807919030501035000364088c54001d60706042c0402c2da140c840c2000b21030760b0002c840c280300d2035003c1c078410000d010301404402c6207900da0505440f5028216110603075540300d5910000d024841c1110f0b0140c54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 37483826 1250 37482576 37482581
    0x20907030e031e120f01060504091d010507030f05060d02061806160602090a0b0408100f0b0d05060402120a1707030201110a030506010305060a052101021603050a0305070503010e0613 80
    0x41040c049000607010f86156990400d600203540142100c0460390104013441c48030384a0724101ca03699500e21746820308000220703024100d502042049440385040a540c01182802024032440a50303134000341d454600390300b51040da440940701e54050000760041001503250705045408001c150744a6000c01810900032901d41c0c85807925001544c03118004e4501000078540060111220450300c00d4007880d00c544c618003640c415131041030116403000b2011501e2088541090b04218032403280041c846c0804000302d01881c1003070400f11000d4003e0410002145006c0c000c010310302c94954010a501c1c407433070760f50411191426103c951903a078042400b2017018403d42190b51442075450343c2e10b85503028804054090070040d607007a0302080c10000016500e081c070801c4401210402414500e14415402000102e0300c011510b2510700c0d50200040607100070544582d09490b84a42c3c1c41594416140100038101d84001e8109070402404000420510085540340380d08a036049604032030601020403200700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 37485076 1250 37483826 37483837
    0x12090f050607080a11040617040c050402030a02040513020a08041b0906060e1e03030906090105041a03090f01060f0e0c1b06010510020102040b0307050f0714030d060909020907030e03 80
    0x641d2080354200061243e000107504e00401c0c1d050310601c0414811404c01c00e080c0114000c160001d141340b003004581329120030a880c4c000b4000e81d2178807141515400410140c0e031007151864400d9400180c00c000c07a0401900314081d030125000118204807100034000d00c0350340050310245c11134004264542080d500d00c0301400c02481c40d00c0080080594401015004003850601e2034403c8410880003010001d50030112054000002c0c0510310340f070000000c04c0001c0c1c01070344070f003070403c1b10038807004c110003541c0340d210400d4401250f07202e07480c0c2c502028440d00c1d01d809140414140d074100355081040e0290403100c0030680303002c2c0c04040165510184001014022401e9416003402a00b203440da501da00031400d9810f9480c01d65000300302100c4c0f040d0603800d138845c900c2410200762081000800c002c6c41200a0050062030844a074603100c0c01d904c60389015903c80c4c407054842d070000540301d40100640d224140003014031b030348107125013207817074000548c001b00c0188220b040c11b48444203946640402c1c4211074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 37486326 1250 37485076 37485083
    0x60d081b03070f02040b01081315110c0a0b0c0f030402011d0402180307080d0207090e1c0201020a030b0f030303060114041703030115030204180b0105040b040902090306061012090f 79
    0x2070302d07215203040400d040d812070441a07001e02c1c03a1100e1000d40c0d520404035a4410700c50181038600303107401d0342d940801c600e040b00b8021150325900e0316480113080385c10300200b02c4518100010245541c46041050080c0300c02f51031317420084001c2100c0f2100c00c0d441c0c82580e6101d40c0900f0700d0f100b083c0c54880d032414000001000c1c294003e10000720007034040c40300456141e00d8a070940443e090661540c04c0300d03039542084e0000e030780541e0050f40104400c204503080b00701140740960680304452a44400618501c10030003100300580d401003000500d8a03410b1290414034282110400080c0d10820082a281d10021301803c2c1040034140407524140640700448009024002c07040c0c00d41041507414644940080c003451020083c002c44034a041da00c2402601d007513920046170f212042c0e801c9458800100350952000381030107024400012600d68030300190000f05407010001d60364044840030141012401807005100e05041222000c1c00c1d50300480d54804102840c0001440003200d0803d2a44105ca0a1009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 37487576 1250 37486326 37486333
    0x4060305010c0e01050a0203090f030a0501110d0c05070305090d03030603080a02010b010e0d0b07050304050f01050a0902040c080c0307031a100c02030601080d05090105030a0b031e07050603060d081b 87
    0x200300001548040d41108030342e0340b451503010724440111102d104c2d000c985401030384144565407582c6800d40d00c07032103510740003400c8480010503607646600b51071a040c4016021007012078403007441d505c24002e4900300c0364185080f41c039103000760380e010707000b80200010380d40500005400d4404150080e40400060364001c00a2500d68000c0c51000b4081c1459009040c0040c626081c15001070514900c41000194840f400030300c0f9680b4a841210507800003801940c0c2841500c20002c02c5031001e1040c54003d03000c10f24041400c03011070042c070007628658442c04040003c0c15080240c000000c000303407504101146070100c1c120741503850a803c04c0c299400c000394080304540e410000617820890036581c0e1231003074080d43d007540c2c1d03900111510707003a421324003c0c04600104146222076114100641d80720b600c442c80040d51031481e4020074a41840744182000a003018681c50704160401c000d40303001400c00700c81040c0f0310302e000000301b8086041048001c040c5880401e00700c014140e00012105000d401c078084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 37488826 1250 37487576 37487579
    0xd0f0c0f11011b150b0303160606030b0106050c120d0609050108030901141201030f0c030f050a0209240d02010c02090f040c06030203040816030e0303040b07050601050d0f06020310050406 82
    0x401c0c03028040480e5000c10f141d5070050800c12150081c480c0b00c0c0f0781010b4100180030b00800e000000c0c10b031507070007640e15000800c03030030810841a40301480018000c40002550a040d4500000c00310010b0300040301b40300f01804076646030320000548191606400021686880c03510000710050f04140c1c00081c10326080000219378280000054062128240e95104603441c4503020628180700d0318085440080c2000f0040c400b255034000c04a820910545400e070302d4a0307490700d034104101c0220720b040f1055004010003505518010040325002241052880794110a01c112241d0945810300d20310f000c1d2814848203805e5a00440d00c542100380c014203009004d03d40081c03400c401100445088817084001c03080803544610a1096230b100c1c507480480d0f42e14190102e41c401d0140e01e000c401c220108000d8641d80d0490351030920190000740404128540c44040d44d01c0c01d82d05082050b04064091a040f1101e0404074602002c55804540c00c41801071f901e4071105170207940c1c0d071515001350340c0040c14040d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 37490076 1250 37488826 37488833
    0x40e030d0f050f0c04080d080c09100c060c0206060d0f140d05030712050105010c02040e0a060204080c030f0f0a0f03020c040615080901050601090b0f090904080406090f06020d0f0c0f 80
    0x401445099042d1001da0503540e0000a130784c440c051406207080540c8281105400207010f003200c580c01c5a9154041818810180d000036a299000c030b001000040c07907110350004200650043d48416032a0780050016447d1001c0400c01c0f118500e40e0141c011541c201e0f2000501159404024080d68a0400d03170b82d2090448401031b015a10540d0300c030001401d51819110406280c3c880c5a060b584c05035030f2800c81107596001c0102a00a0503015507050294042c80c50000d1403501c020002490300401030074800f46008105410452a00d0f1101c840390001500c1c0701441c00042040700076654000b00c006500c00c0142000c900d0f0001d15682d840e085481d111000c5040d8110001031000c2d07060543d529002a960f01250310b0903a241a9145804607a0601d41032000300701d002d001d0084408074941544c18491442d0009514035030641701912203090001d03081c428113500802404c09001c40e02d10100d065864660b00035550000b40410004003c0f4111040c04083d21030389000c1842504102400e422103036606 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 37491326 1250 37490076 37490081
    0x303070f0e0a060f180308030a02070303020c0604050d090b03090604060c050712210c080402010e010c061401091805060609060406120311071703120703020906070c08060a1802040e030d0f 82
    0x14800108171303003500440b0000c00046080302565400700c2024116214514500041d400240044003491b4003072002c07030790641342000700504c11809070009001c58001c802001d07003582c00e150005000e1200c20410400d5140c8009002d41d0003980c4403100240b9450001c00488140c0212240100041000d0050b00d00050b4004213a541a00328081440409903901040400f2203410b5a07407400428a9103002801660003840e00700126031060502102080560750791038226490a46c3c90304039010b90800522069000b84036100143c8109802030020981c01e444aa80d41d0344014003452003034414a00083c05178450750006401800c10000008040d0303e02e140182101c03a01d130b0040751052087c2c80d000140d0110308541450b111685401452904900c101c003c41d03d101c00030000010305808100d020825100c2a0080c1100c600031003030401480d0802024900700317840070f41120512824454030b0000e0038180041ca10020b80d04403000a08030001a401078154001d00c402100b2051410249600b80807898 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 37492576 1250 37491326 37491347
    0x501030308060f09040b0601031b0816020703030210020d090807080c011b1b050102040e270105060105030127021902060c04270204030c03060606030b090402030303070f0e0a06 77
    0x252035410301030ba110024441d068240c04412907111400b400402c0120714204070070364020070180b501090650080d800e190b0090181481c0000190b050b40801c07050140300b400d030700e01c0c00c0440d1004e00111851070320020b585d900c4015250103501c0e8005810341c2c40c444603a00410000b0340c040c0c0c0c81521820682031015198100480c3c1003059401e140720241c100300c4104d0990060307869030b1104c0c030394100da07048005100d01c0c0d40720040341d6940d030811003c5544541d0051880c800d421140d07400300752804c8400d94030301c1da030350407038502000340c1c100400d01003940e800c00107603410741d646950082e6078441100000300340001c030121165105440028105070b4802c02a4a0241450a6400f203400b00d032074651040c1e0744c0e4480c52003800300b0081c54600701c02044041036042d00d0301c1c005420001d41019201d459082c846022640100e80081da20702c0100500fa07010300411924050456002910f4541500440e4076440001c12550401240d051402400d5014502c5164001d80c06081e090341d07561079150180658010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 37493826 1250 37492576 37492583
    0x1b2107030c1205060603070e01020c041107050d080105030d0e1f05040f0807050f0d050a08040801140a150311030709060e0a0e0307051506060405090a0c110102040e1906050a09050103 80
    0xa0004122030b038024050640298000f40c1403901d543d46055045404208c0c1c1101d29045008095849551b41c2e118020303416110044080543c0c0c1e000d4030b01c2c2c507600e04820f42009000340f040e4071004000300d03600402c0c810f104841609001c2c0b43e43c1d00c490300180b40020a0455000200320401580014940c0303c8040c1c020755003011200b01e00d039510398401c507075211118410f007036201d0740c840706002c102d080008815034482d2041b0101d560595160780c0d001d10716001a000b00c40a43e544004204c11200611012a00150b00c900e0030802c420b0303e060502d8848175a404050702002e409003d1004540302000410020078444808109142c0c03180c0014000d880300f80c429030301080c00e110380b6003403010006c402c03160015805001014103071850425500560402070403254002d000b808001035a0b02c0300c20900d8400d43c41c0e640000396542c0c03c0311000e064221500003003140d1381c0c41400207001840c0010a800d0b0480d00402c47e1802d4810000d4441010340380507004150056510071000900340f0403030700224140c7c1e20 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 37495076 1250 37493826 37493837
    0x80607120b01030b2206080712060f0c02030304020409050c0406030614070306210305090402030702060f01080f0703060e0f0102070f060b1c030f110f0708060c031b2107030c 76
    0x8a007001101a110300703a03007040d800340038070031204503840020025400751101d1060225030f00e6a1103514a00f84031003940320040c842c1d000328245040054a00c124000001c0743d8000308a20301c01c400c002035517400000c1c0000c1c051640c810380b640c24060104030800101030014402d01c82c03152646482400303461058540364961241d0000b00d40018003e000318006d0703030002c42829111908950388a42c00c520218400d6050083c104000d40950b03e0b5400210b1168810341c0041000e0308103408560b0502e24140d02c010070507000307000f200035002004102e002c00c680c0c00140100352610000c61540c140700012041c1c2c40c842d0310000b240e04c1008090b00c101c5c01c402d8000c010400241c440075090220340f030101c0d107084000307400e24030100000034001ea1010041001601d050b404810213414094900094584203010710380c0305807800c009081c1e08102c442d9000c1c1441c00003a086080844a82602000c0056010600c2402044103081c0681050040080700e003d9503d4603210708241c5405070090030342c1094400001c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 37496326 1250 37495076 37495091
    0x518120301050312070804030b0103060237030f15090504030801090b0109120312060b03090d05090607110d0501020403120f02010c02280807150e0d090312030608060712 74
    0x42101095904031400903010b060309103e80c20442001e13038401c1c4001c440c2c0110600c80440410000800300f030280d846983d0059603000c2d8141d08034035400c01b90039840a60805140100548076001014510f01c00300e5083c04500380700422218800380086400a40c01c0d9800180c2c0056010b446030070131809603019480b111056620b51070130400f5100042c42d500c1c041070001c0d00400030040002c030701800c0c4900a2800c1c4c6040b080304550001543c0300fa0f800302104405c080240300724450f0900c032466007200031341020307890641d400010607264000c1203409810400041c003010699221126105a040d512074001c40d0740303940f2460440c400100c1001240700142c5680780d44824140144520020100c0d150020b000800403c1d003c03584802070b020b4100f203001000d954150000340d502e4040c10700e15101758083c2d4025040302034541c084501e85480d0700155031100e80070301c00075504000181e003980e070007049908002d60400025400303441c9950000c026840742104100240b540280d40d00c1d110034107650280300b0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 37497576 1250 37496326 37496353
    0x7020103051b0a0503040309170a050c0d020d0f05010204120620030601021005060109081e16031208090a02090103030206070e150a0c051608030a091d220203010518 72
    0x8002082e4482040b0700800c107541050740240c02640e4868800c0c82c107604816100d1001160212800000c2c5e030742940901040c8080281c140103400e110401502c0190046400d900050140c0040003006400e005020405000303001e002c0d0121000b5111061f1045440d040a10300740c0000c0c22034249035060300b01c0061900c940810500222409644140e00511600c8100b031880303001000c024001d01c3c10710154a04c001484881408100d0703850384d0140440d980c003040b40000b14104001d007040900000d2040c5003e000040f0740905012924056190034113035641e65000c00c3e883d258030124081c0d404080900000101a0700103103041c03003011a03544880d4000b0011003849400302541c806a030b0100c034140000855a032198040c01da070580240c1c101c45100e0342c200c40c50390f6503a02c030b90400181070700009402840c0c00e0f0048031080080000c01d4680c407003070740e51003050707060740391302518805481c6100070010707056608a4001171000741d0001e000f0003140c100010080c040e41031000300c010103800303100320105c900c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 37498826 1250 37497576 37497601
    0x1020106060c020405070e1005040303020f120412030c021c200102030a0f090b030a05061f02060613022b0b0906030604110111030a0f0e0415030605060409170702010305 74
    0x116120341e110141e5030002c940c00c12014220080070041000b5110300140e0300380d035a200300122815080c1d1aa140c0c2c460460070000d041050708018810320b54401c103d0041111980710884084030f9a401030015a07003c03621b01154005203c0320b0103540a202c002d681d00342800c581403d58002407088401040c2c1c50040b080106c1d08494203440b045c0540c100340803001042d805565070001516003480d0000c5165115494205260015501200b1356980e0364100450390030f24041141503010424502c0701d0140036220000e503168401481d040c00381d0b0300711080000c883d10540655001c21100c2c164038148003014950b0741c24260342003908800f0b15007050001300e8107041c01714503207001c3d40003e805021703a075549841d102030b00b008180c0303083e042100c007100e00050400240003505481400d030359035201d05503070f2001c0201b48070b20014005200e41d00c4c0c0b0520107119004c01c21020216548410042581e56843e80000d0050079004405000100311541c841401e80c0880024100c2e94401d89040026031100d6004542 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 37500076 1250 37498826 37498829
    0xc0406050d03090902090303070b0a02030702060601020313140d060207030c030216050f0f03030c06010801090c050103061d0405030f1305130203060109030f05071d060103060b03220c0b03010b07050c01020106 91
    0x3140043d0b9080c071000549400800aa08003c4e040b0f03031903c0300c3d554844601030002c0301c02aa4965001c014880c00701d81c14000903421860910045040003059100c0e802c5241803071040010010300c0c0c10f030101030340e2940c0121006654104204544402007400c1c0a44907040c00f81d0110010b01858540c150100c074132001500c00d40c2c0001c0c1051506030b4a84041c041c051101e039100503450300c02400408041c4104100c0e07035020740308400c00840c0c071030300380d1601100d4030303515801481c18141000b00c18000c0302c144a0701c0100c0601822440b11442d01c1d80c0c1402e83c1184207404100744658000100c68452800b046448400c50380d00391114112201210080812800252601c07130028011850810118a07116007a00c840d50107901038448466403024007420824440c60480e20319400001003090355070700341c820380b0002d00031071036000d165140c01c80050744102003105031180c01c49001d507045010f01c1320040d44040a0100c2481c0347e40d80396180d03600500c0300d1308103003c03c8407240f080c0c0c00303580060f51041c0107160 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 37501326 1250 37500076 37500083
    0x3020408030d02030405070b040305030d05010e0708270d090f120b01030308180109030306050306060a03031413180506030f030c06040807110a030605071d0904020907140c0c0406050d 80
    0x500340400b55407070001a510252040c0c1e8140300b581000329040d400078008100862041000350b903510302410308401640c005074001001e51010301d0030000c10941146400da071040401c00908000f036144442c0d1060180b440824018601c1000440e441003504030700e01c98107851640c40d02d0b512203aa030340a1601c8101c0c1241009240407034220040000a015126064200044088003c403a019100401f400c465858106400094454800300300300d0906003d003030b8022106a032554646421610090315a40c03c02c0c4540c05031000000342d0341240003030307805518041d042c01c45082011081c038220003005000150345407403180c010380f00d001c9900c15000049030700e20540900039000a95454864860540040310242d40640311250111265950055090040e40c0f040314000b44608104a0045c540020940d59003a001c1c0c6a1084220580d0388014460340258101c3c0c1c0c24a50b5034a11000716103900081e0030105540ca40400c0104031030308003080c0242c01c5c090980d0304002680e0341e40100308104e401081e024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 37502576 1250 37501326 37501333
    0x906080f0a0311070801090302100b010804020a05090612010608010b1207030302070b030414030a08100510020a0204020c03070209010b191407060e01060b0d090605150306070c0512121603020408 85
    0x100c00003802011000200000d10f801d40c0c09081d60b0380700642c2076600d15030045005822a803e00b88551009118102c072282c003e10300344c0c0c50b5240c9540400d0080c429400b80500c43c5000780c3c0060119541d15412045045000000780710301c03940c0d002403501810983c0c3c503191003007101100141d48408001895000c0380c0e0554014900340e032502000103410b82c0060400d9840c030007082d01054005200300f005000300703081540c0701e25a514283e811143c120740e498005d1072007260100c10100c0056030010b40c10504940450700180d5480158039443c0c07451058220081d000180d04000003000240c0c031001d031003915200200078a075100320f00021505c42441e99009544414140302e0030011401c594000840502000000985070303403a4071407451689c1114228025094407107503400100300d100c2c000d15400250810700150020306030340010ba201d9900130008402c000226a00a003804001c00c4902c044001c000c800316526244020030181000003156501c00300c8103412030505190740303c2d200720b40c2101c43e2007014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 37503826 1250 37502576 37502593
    0xc030708040302030d0c08060f03010c0e0906060705060108030c010f290411040807090b03010b0303040501320304032304051002010609020c0106030203100b061803030d0f0203010906080f 82
    0xd44640802800680031840b091203102d0148079030b071152498443c03040e11101941e10f8500100650b01090062090280c1d0418080710344480c1c01030030b03070851010100d404001076a6800d0114240d0f001d2400060518490076000041d5104040001d00711b4040e10802401130502e142c1e48401601c0d0080030641829021840e200c4480360a54001200c00b8130080000c2100c1a0482c0e02080581240c0c11041e6150040d400070000b2040c9449082c119120682c004c0c0107410840001a4030780c02207215090601c41c05c0d42c68400103c0441801d0452404804d083d81c13039403407041c8c0940c14103820072502100030a45500c45609000860700d8a01c1400d445880b0392031902c1e080030144551900075464007802d40d0340319040400c90072a28005054121442c03400061410701d140109440c100300d1000c00d120740ca10f800c441c00c520f502e0ba00116000d5907501c1181104500c0e0300004a4554814034010003101d5241084101803403001c0e80042d8101d43c1c407038a00744060f03515500c80c1c640b510526412100349130f00c00041c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 37505076 1250 37503826 37503841
    0x601030f050f060708010602070603050405100507050d02130e010801050f01060e0f0d05060709060807050405010c030504090c120501060f0c060b04140c0705060c09010e010c061e09020a08060c03 85
    0x144045198450015075580d06074000780c10780f81078010307601000460901c2005000050b070401600d00200094642409941031584131f04c0c0d12040b1a04005d5003203034603000014000380c020000c50b050700d12881421561402c0550048400d100070b40102da040700304030000000c040d001406098040c00f180e09001ca4182d2a1203425580d000d00105e0080d040544075080302aa9a2450160807109018002501312464070a10003000c4030714039000300050108420034011555031180c19030302520403c0c244916210f0781414156064047da0b40b1442e10a400d00d011026001d902114495034080c00c460144030b10b980b1400103961042100310003800080e5031140882c045640c2c0e8208007440003029100045240c031102041038410004c84580c0510500021713401c08006081080b0760b8411450150142003055000000b080400c0c00c00c07080e4100b15040600c00b0620440750711050070200e000e1801c2070145800d400301f10107817504107000c3e441038260060004003640003113409031040d40400d58440c915a00d269 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 37506326 1250 37505076 37505093
    0xb1c12030b120109050c03060f040b0f06040603060203091b0603011404020d0603020409031d04060e0612010b060c0d02010b0406030803180a2f031219030905011b20060103 75
    0x4824560000440d02c404402040a02c01c07200001e0083d406881d020100e4018103103010301c090140c410740034200b0200400300b0160507066410078021000f510550700c80c0d10005002d42140d800160036644004144800f0120005164810040c10f030002c0d40001a15010007030280024802c0c54000c858107408a003040c9850750040003807014803400090950340360f4005c90300b1075180e120200d01080c07a0050302c04020b001a50419291442241c05210790741c100740d0107141040000d07040724011341c412900c050320383c002904004485a00980070030345555440880300e41e110000c003004005540307850369500300da00b4140030b0031007901d4010304414515150b48901c900e9141ca100d0200189001d054500d0b40015401500c0341e001444402030490380c000b08420000b0752a042c0d038007a6100358000201461545c40110a4480008100c880000e0030180380c1400c1e0f0240c41700f400010459440d002d14101101000800c026007540281d40d40d400b16070b1b400c00c1600c0c5003581da10341d00b4629403000c0e00420010b80c160 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 37507576 1250 37506326 37506341
    0xa080403021501140103022104050102040303180302060406030c050d0908041509140105070f0c06030f1404150203100b1216020a030e04020a170f060f01020d0503012c0a0b1c1203 78
    0x288c487c1610908107480154001c0140c0b0b003251940d40005080042c55800140020301301e05103421032500d9441d640c000740c103a10807842454103168440c0f4804034414060410f488d699412100203010120061804030a19070090064021544a8101401c4081c0c41140c480c4180c030582a0318180b1151950011b450385d0b00b01d040c08440074280d009000c400110390b1341e0400010a805d460214000c25250f041346e054a00343e04d0044000c911120170000030034040b1101040a41806100599a4030f61112045124080d6042581c0d00c80d4001107080360301080c5074a00b03200310400c0040141c804010030702207844088544003d80000c04000d1880f55501c0c15500420040003181420021282e0500c400400c64004031080800f80e503800e010414142845410080320002c03d20142180118400014042c0d0106000e2160800d004405252503084c034820501017041205024541904d03161044ca00504200d41c0c49501030054940c0d5884090007a009558820364007452902d10480c2c100c070110000c1000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 37508826 1250 37507576 37507597
    0x30309030f082107031109090402040e01060902180906030c0604090f150308090102010f020a120504060603080c0604110d02090c090a23030106050a030206090603040303020f0a08040302150114010302 87
    0x208001c622032031058004840c103c2110809016510f080314001e0115400c0202c5188000c030104881c0e81ba658440c000c80b070b1f00c140d044a000030307607081c088155030040c81203070000f010446c400900f002040e10610160301c10071400301e8502409969513000e0540314200000110f801240500003440305d0142d079000751310741c403002e008002980300752500d60341d80c2380a4a40c4213a501e007000240d44031989d41e080c0079211178000000300c198a0700c0303680d5100400134101a43e03080c424a40e07032000b24080002e00d410610041d500101c1450f1200c643c8100d45481d00c0041c0c908a80c003100c0ba11003c0524245920f42d0815550014103200031070340c5512150244d41e00c0703408017580c409080c43c000305101a0821019801007520000ea40c000006001858210307811904918810b201000c410801683c03500202d03565500c0c107449407500d9031940d1601f64041c1c0642042060f442d507003c2104142e00b81c2c4111102e125074002c3d07003218889083d03841c1c1a1021007080c050f8091003100c0b01040d18095010380c00800340700c100e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 37510076 1250 37508826 37508843
    0x509071e05010f080703090f0f050616020601050d060204050a0303050310090b0312090d02030d030c03060f05030a08090117010816171c050c030f030105040e071d0a090f11040c02010204030309030f 86
    0x1440c0d515904c0d154080303402201c17100038070b000d03270710510a007008041d41c01a101c42d0800f100011001c8040d540c0c3c50144a41440307400050b000208011361078045d1001014090400032007140c41c0e1034041c003650811211649491004c0b00009509206409064002c20703019000e0281074030700080d007000c40c0e0701282a0640020114001d0780040e00c0402440044c0e5103150350000321102642002000d0b6401d55102510341a0100828011564040340c0341040340d43c0507100300c2c0d480640c41c2c0140e840032807010b902c055207030355075000081222b00426140c00d40320f07050610600c01d640b02c484540304400c400020000c9540641e0400100c00c08000641c0d440c0038203030800c907040c240f07100c03d02c52460b031250306401160040400100b0582c240340c002ca00450010a01604a86060200007080f10350081d50245036841214007040345000c21341e201c1c4c0365107070f0080c040c0780c0c1911960a100f0b2010850754005401585443c03100b1401520610170b86055075132580d00c0f4560070385180c03282111100701c41c4041e00e0312034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 37511326 1250 37510076 37510091
    0x1030804030204091410090308010f030302100207050f0d05091306030807151b05070c05030a0302100c09050d0602090f2b0614090a050606010c0c09020307030f0509071e05010f080703 80
    0x1900b045111b00c902070f0b5030004030703038002549001081d03860183d00c0321101c90202d250600010380c003c20b070b0781000d11030303082d00503100c00450501500d004400e0740c0d2200c9502540c3d107056082d81c0d011001f021210300680d070a5aa0880001c000421551203110145c10600305004800004804c02d04120a05848180124111110f0082144c0031a10342c200400851400580182081440c6e2015001040c1c124003400d0090351549001e5111400040320007106a601d500c0f01d401a4001c00c01300e006010041c0c242042c0700070518001c1c0095001c1921203119920301d00386a11540342c0b4461941c14007105046507050340f0041e52401c1900100010308540040d22281d01100c00c030880d801c0c0c940706a04180c001c0c168817429040150400d03101800342c2e41002044800d90000c5001d00b5603500440392078220060340c80d0342d80701d812001041c0d584450030304142440144407011794006542c1054400340303a00b10f5a46642510100020005881031601040080b01141c003024000c1d41c8071035003c0010304020403101c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 37512576 1250 37511326 37511363
    0xc0204060b03010902042408042603010f2d05010c020105040e040c17010908040e060d0b01080d0e0604051c02150301030302010504120203090102060414030d0219020c0102060103080403020409 84
    0x41d04241c100010300e0385d0100d010811a555050f480c0580215103900711181000d4460040c20510b0040020b0705800b00c3c09411403407000901812480303075410881d9241c0300d50b1500c40c0c8070301c030005074402c1c0f829226150442407405581d0320150b81002e84031403000c508040c50300d0019120002058001d03814018103020000d4003005480034184a5131055808c0345401d801c140e440c0841c0c0488981c80c500c160f140920340d0b4005041c40046a00703640f07040c0700400455585000103591103841190045c5400100e04c000136900c41c00041080c04071172a40c40c0d5108084020050003000e000f1485000e61201c440c0d8486000f081410303030151003450010b001282e0070100b002e86030806910a074400c40050395030700100800e00951004880c0e4818680c800780d0b18180113000001c2d61024060809020701550b07003910782e9040410001c64401d0724078601c0a40d250b0302445c140082842c03070300020703902602408920344d0346036201060440c1682e07802240c00e41018115008d000051010030821240b00e070358181c4081c0003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 37513826 1250 37512576 37512599
    0x18010315060b18010f081009022503080402091803040e0c070807030806040501171b120706020606090109050405150c040504020d050a0b04050601090b070f0f0803091513030c020406 79
    0x3d1035003040e42c540006988001481c8040c0750444c00100040c407002d0000e0001031207140c0040b10f02d1034101586034082c2d815080300107102200308222050100d0207010405030401d041d41c2c4603074000c03110401139035a4961038121103080f0b01d0006c941e6410070807003403240d9200c1002c400e0308009181c0040d8109038030350f5900e400c10b5000003815001324511904011207494180151405459040f80d002903a03404125040c0c0c1e100c0502d0407480c44a0503441c08c006103501c400c1c0348040901707021412140ca103551410080c0d111441520f4550203190400000300d50481c5502800d4001c0d42d00100a11807110300c4564400341e840040c021005107d030400c0700240c0360f0798500203009640c201d00070000c3d490407e04035007000c0750050b49003640524140310405c06180e81001e900d4041b64800e60400e60380310031616280e00b190780c3c0114010705210004481c6024030115034091481088820100d50f0000e01d0301c000b045010740210703030303401c0300000001d40d810005c2c1c0301d4400200c1d40307440900081503554613012a000c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 37515076 1250 37513826 37513837
    0x5091c0507080a0c0e0105040b15070302150a0c0207140f010c030c02060711030c0307060e0105090604080a0501020306090a0207051c0c06060602010f11030103080a030203090a0c06030504030305010518010315060b 93
    0xc4104c01ea01042c001d50030a440f0080c01007a04075401c204034801d000100f24181c00720402d10a61040c08030300303941414001d2011640d0344040c01a50482441c100000c40024000d20f01240014428680040340040d6010000d46184500034004003920f0705c40c000440d40180d42440440410031039500c51001610303a1405801080e01c103440134081d48011070b007810714180c002c2e0380c0c0c00c0c41b81d80810000c000301034005000880e034000a2a01550ba12480b4000c194684244e511003c840d209000300c80051007010f601541c09144120b52000700c68aa2010141c142d000d40030f0050031a800c40c141c02c00d40700d0260001c5000e200c0803030811000e1080a52142c0084507142c0d40690701513511482d0030015090b41d44104801c14140340c54035403c550443d1a403070841d00030b40c17500f6030030b140d40000400e0482404028403441c055004142d8000b4940310a00100680b000361401c40121703042200224291502d03400360340000a00b41940f10b016072942c0c0713401d02c2031200a088400c04980c2d4803004034040d940c4500818 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 37516326 1250 37515076 37515083
    0x5100c05160608090d14030c1303050106050103110705030a030b01030b18040c06020307030801090b0109050909010c09090e060a050a06050a080f070602010b0102030301090b0103022b0b0105091c0507080a 89
    0x85000d16007000585400c20013005264150421000d60b06442d03006501600c000c0c0001c0c1010741c0365074498030381214602c12441540c610341d4000500104000d8150044d506491084c1d9043c40380c2e00000c00d04001074014a00014100e030424400d65240301c0c86a804100500e40526004c142d919058022134402440ba86038034200c000c04030100000d0010000900c4010805071000710328150498600030040312041c00380c0000c641d01d4851400c22a88500c00b407002074600203002601e80c1c2080d0004a00801c10000e11a020ad9411a00061051400d1140c00da0440d03000e40a060f6556902d214030004100042c00d5185007561044080b0309a06c402020002406184005201d0401c040340258a4000c540d0300c201c04582c106401207181c0c0e40d01109990465010803004100f20200c031005130302a00990900b4a504c0b00c0c01e05842854030303940d010442c080b2140c6101040180800d100444051003021900790700329104400ba0300c254030080754007294281c0150140c0d02e03040c9c0c0f5440300c2c0341010584c00703094 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 37517576 1250 37516326 37516363
    0x20d060906050403080610090608060d05032101091103041104060f090f050a05090703080304050a06020a0504170a080a051b0102030708040507080a03080103020618040603080408070506120105100c05 87
    0xf01364100352903681080d812601e001c80e0159801c07005100082034016401040790710004101151078913540c4031401940f140a9940724004ad01c5960403c8400741600d40c2c6a06901e070001600f48014031803049905200d17458145940d5960301d0305e205006c403100c101a0800d55908000814001600700d080140c842407001203140c40620700c00b2000d480b80a400123007258a404184543c880c0006603500449500c10205a101d80c0c40d41050350404c010501d01a210600009070f1388140c2d54004010029a140ca504c11200c415500040c15501c03115a94000d10000c400c1049070b03542c5004101620040519804500013010342e94403441c26030f0030980b07203100814001c4051108002050118201500b40b0a0040c8820646074034024040c0c0780600c00640a1400011003a020350088422951450b402500034410550b0300e03e07204c245540144500c612500881c0310209062600d1304c04c82e0b20310f6004500c0e0b01100d900700740410001c07543c107840e200140000b42003030500084c0c00780180d46519810f4000c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 37518826 1250 37517576 37517581
    0x2060601091a16020112020706090311030c0705010806030709020408030301030b0105060c0a0605070c0501140403081014060c0c0d0308090d05030403050a0e120a050a05121c09020d06090605 83
    0x505452840c0d004031240310782d6000e008000306005000e072140d40d0300d0b00301034420152060005841e844d09565031041030078000292001400b08503000360400c10302c41e650780000440d801e0351b0180c984c0034240100d01142c1000404010340d600c102a46500a50001c040d141002e03603851080742240e21583c41400a40c001100400a004040501500501d03003031301e00d00e01d00b644120f0442d80f202070f82440108020384d50400f10f40303003a1181881104d120f510500070001840024030160207104111002c42c0000d03030744000a20b5108124005404640c0280940301500901d002004842e0b00b020081c01014401c0180d110b106a4401c030707104403043c0c0261900030442c00c0c45c05145040441c0007a0500c1440400c000384030002e5845021a122010705181c410188000200019031908003e000e00e4042e00c02c081c03248081c0700d004140d4a0300d2038451812942503014030390120600e03006410281d00c0c580311f031201c11703403008401c1e41000d100700d4401030103a001000c26a0f500421200203400666085956804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 37520076 1250 37518826 37518829
    0x60a0f0f090b04061a0307050409050702030c120a0c020d020301090816030f03020f270303040b12060a05091303051e04050f0405010e060409080c0d030207020102150105180c1306020606 81
    0x242e03200980b010307201489014107018209030701c000c41c541e00003842c2c00000001051035100d041030340d000e80a4000207000c5800c01610003540ea4005c05000041c0c0c4c000e000d003003e5100e075804111400400c0303d032285c0340301055503001c000345c400f140d500a0b0703015500c49034500001030111300200800c10100800c22540401400c00034058000042c0300401e0500c104a01140000e190040d00c1948114204004801150000030b038180241840d074260903100c04200032030000c1c4284040d0680030300d45900d0010301d65610040002c120002d200302034010014001082188100b100350b2192140241400742c500b43e294019284644005e414501038070700e001c1000d0082b40760018940d0080141120144615414410003000749500985031911440d03803001940f04101c0b410301074611508011040d5803c600e40d141c00680030b980710075000c0717006008008204040d55a41132646060b203001800344400651001000401060064580640301034288103030000b84900b11010303405042d56070f010303000d80e00b0f2150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 37521326 1250 37520076 37520081
    0x30e10051003030f080c030105120109020d050d180e040305090102070f06050405120c0907050c0c03100b03120403030e10140a020f010c032717030f040308070c08070b060a0f0f09 78
    0x81e4001c0c00c0024038811b01840c18204030690381510000c454003402d00b8030086c003a43c018002100c0003508642400070000500c280852100c501110310788610090015542002d90041c1d03242c003646101d100000d01040100e44608041d10080030107004130740300030f42c0380c250b10500400c007a40720303030009100003800f8011414280c00061441c20700c90018501200000000350b100080101024100900490040b6540340204503007000004060b0980d4250042414248042c0214411080c040c4c85031052402c0c212a03000200c1e4226509030f82c481c10000b200e0300800c604e52101c035100748104074041c811001d141c0020b034010070a00d029900140791002d40e403500035003515118602881814604540302c04a172034284021078203000490800c80300c0417030074584400c0b8550788106c440d0134854017008214400006030700c2d0a00a074080d4403090056034501104840400450000500d80c0b038061240d40f00240055500c6504004024882078146455405001c69807070154044c00ca00300c100c0030100010340320352 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 37522576 1250 37521326 37521347
    0x15091506051305271e06060a0806090304090f020702060315190506070201080915011d06091b07020111010e01061e06090b0a020703020301020f0306030c120706030e1005100303 77
    0x40034180610710740200420400a60129240c1160862045844d1840301c144004d0100c44420004000050160541d2070f5403840c0441ea4540038176022030000c074480c0800146144180c80d401c00a520306030030a01084040d1582c0289401450340a000000060b40e5032805944a5100940c84074490380e010300810000b4021200c5c40507428102140c24000c076100c0700c0481d110348d5020300b000b68458441c0c2d68402d2411540325007000800590500101d1044110001082d07141070300d9240c0c2d034082d2651010010180019616542000a11039075404800d458001a010a900505000980000c13405080f03096940c07181d241007443e555079205002c0c40203c40380c9280070604001802c0a0a81440170141004009005500411001283d40c0c080580700700004006154060003c1d510350081c0c04440c000fa40055442a110780503402448255041c680500c20b080748900005000192402c0c41c16801000500200c000f180103440d80e40181e0149402000d016500090000b80e45500d175080080c01000302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 37523826 1250 37522576 37522609
    0x8090103050a0c0801140619020a1202060601080703091a1503010e0304030803131e050307060c02030a02121614060406052202010f121b0315121509150605 68
    0x5103220b00b40f26581c060801410741d000b4500c0d24040400c0500041c01e01d008103000d4203031411110042c0c1d607000303901042080c01540320300b1351a165002d8110040c3c0c0c0303840d01140d100340050450800145480d01c21381084506900800026810101c5003200103401c2c6008c540385403149400d6040f079466401d00744203048440d03800d072000d1800c250440d903071160603201c054094461031040700030420520400141c0c0d81c4030600603900f280740310542c900d40587c9a0b04030580540702d0342c0c43c1140000080340048102c8100790420f5014181c0280f81410099860304041d4540b081880c041180344001500040c0381d81d540c0c20b00b1700c001c1a45103030514213103068500081000b4a2211082e400c010000ca000110003485503090828410440380524100d4950302e101405000d603d0400d4090040104074103406d1500141c01d43d020311070440502d02c038183e140c1061040b12081501101640c001c100c9002284d415124400301c0803034101e083d030f184d4800450f0f2040c20111455960a410080c82c0b5100d040504030052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 37525076 1250 37523826 37523831
    0x80102070c05040207020a050d0b0411010c2f0a06170604090309090b01120507050304030206011a040e0612010606090e2802030a140a0c23160f02030105010308090103050a 75
    0x189965500036030441e441030702d001e950081205411540c403a901c03800580800b91030818662a5803c00c180ea0100644058070120310046540710f041d480703800040c07100c90f0030080e100d074102c03204006031300c4910f0b015004d080c0c0074840070032a04495840d04150001090a61fa405190025051500c0364151020304050b01c69803804004500180c0c2240301941220100710000480281e9000141d0f05507040c20030803071030700b032a100c208050141c020000c0c0d030045000340e00f160902e0380c84061480001200300e10903840800f0500081160100c04800d051b409040034085001e80d02c6059031007400e5550315008000440c036034510034132082480484c00d82d4803920702100f40b4008103070801540008803600c0e20780c0e00c03c1c2e60008009010b41032203030070590031301d2182e2034620003a02d0001c0c1014010706128907000e000844000440140c4402410302200e1829540519858294003603441d00b80c4045004080740c14aa02c0401c600159070280314541c020743c041c22140c3d90710000907000404803000240186682031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 37526326 1250 37525076 37525087
    0x2030f07050d080a0207030209010609090b010305092503080301030302010603030f080601091202010c0f0809030d0315092309030a0905100807030506040e2d03120613020409020a18080102 82
    0x207594000d440e0010b03030003c03100f654030301c10000200d0030a41c16400103900004008000130b62035600840303130b20440781c65031010451114200d0044099aa0986800000d0f0303000344101c088244080404d4400c000110070030200c11541e039070351560b0300c0d0402d80c0183c02507551000d04006140d00040c0d400c4903005589800001c0e0700d41000003070b000100502840001029a20b40c240869000d540322401064001c0c062402c204014500122554040c0e404107000c0d01840c0d82c09030700c090080c051076500c42220625030b21241d04210402c0002e11000d6030f070300c0b00d00c08481035010904409140d094080c4050001469407552101c0000d06403080d584d1016014610380c42c4416070343c60380017203035641202085c500410161642000503000d00110311815202d8001c1940b105044841180725100c6078150f00d6010100c02c0700d4001d560b40702c0c00780701440c42d20921400005035451410482e1500d4212a0704130044c100741c0c030380305400100d07005101a000400c48082d0b05d0540040c1c288004001807002000a51811 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 37527576 1250 37526326 37526329
    0x307060c0c0324020d0f0c0f05070f0201030908220e010608190209100c0606050d080a030e030f19080124111e10060515070f140d020a02030f0705 64
    0x140c8140b1002e000c000c15181a400c01c072500f6003030700d90321400107142552518807043c1d14600425000d040c4070710461070900c00e518914050320350b802191905444280c2850403079104d42c0218907502001302d04255a50b000ca200042c003601c080e0030400c511aa60880c80b412100e004948110950004881900349000400040e58800c50b510f0740020210720010103240120500000f038069604402ea0110303c0d440d41d43c0c01141d00c004807803d400c0c00365006000e170a989605100010a1401c0003501007001040b4184540740641c0064400e0a03252040301d01d8240300e4a000320050b00862a81080985c0b201c000c03001981d84420031601401c3c00c0c404c0203026540540c1568040c0044000301401d100d1101180500b00708140075141455905121024a21103040305c840e4454100c504c42600c11f601c1c00c2404181d42c240382c881d0a01c4594041c103440d00d0041c00303884284030101044411600010301c0c1c2100c0031098030a0000082006003900144854100362040604014014614101980c04801c2c1040359 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 37528826 1250 37527576 37527593
    0x170f0402090a1d030a120b091b070309050a09050412020105090304090b060d0f020a1803020a0e060607050703080901020d030b0a0b03100e010b1c0504020a03080f0912010b0307060c 79
    0x4203980b8100040c583c804150903150408040c00e04541d140000705076400c8243c3c1102e000e01c3c10b20070300c0c41c040140202c201c0c204602c801d01075940c0074141410290b4141a12854001045154003900300b09030259034527800140036440c42d0f040300302215150b8062008020960044051030b4203a40024072161a00344003195072400b8600c100c0704055101d5000051a441b45e40440c0e04038040a501400481c07100d9022401039480440007000051079011410152034800c0300e00c0d015603500400c4903110a140c2090149015009052194084020044940068420401e14000b1449803010380d44a4a2010001e1b05001a04ea40f01044c0742c244000766045985051741c05060b152850f11240c1c5030344907040c0e081c0c03074103559030401a0030100100020070440c007618060a0811003062034094184c061604040c10b40301d06480003034201000180600000e0324034005412540700e192a0181840a201c000a20344070405e00d042075140d54643c448415428240001303006007140f4241891003079107580c1c4803640b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 37530076 1250 37528826 37528831
    0x917010902090f0a020702040510030506011706040b0604181115090d060207030c0203030c0c1c030e0d05030d020a081f08100b0415080606010206010e06010914040905060106170f040209 81
    0x3d009118400a902c100b180c3d41a918001d40160003003100b880c040e4650b454100e020701082e078951041e070000042501d14a4200c184200c0d4081c081c01c01621240d961440400028059590064079008401c0c510342c0c9641c10300210341d01981c00e09011003031240034000308070040303492403445131000c200c025850340f100b13119008443d900c4040140c0d944c0003810301701c50501114600948c1400300086c11201c0300c1c0002201c5034210000c0350300040b04610b5a050066422102c64010003150081030300c40001c0c80d0500c40400030f01e0103103054a1405140380c4521040383e0008200e00c2c00704250074140089410351a85040300003029465036a256414101019580c2c00142c03000c11003a505c1d080c2c3e0301115101c54100c15803002c1200d40c4408031b645c40c2d02e174003500c403030003207035024018800c0c80000104e01d692200321600440d01a10394004007400d10301e229040b52001c1d180c0c99006a1a1980b035800220100302403402400c0e85d81e2110080705100d00c001801040140110390742025040c103000c0942e4503520b8007034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 37531326 1250 37530076 37530091
    0x306080c130b0d081902010c0f0c050a02150d050c070c0b0d060503010203070302030106030f060312052101081f0903020d0c060b0909010f0b01020703170a0207080706091701090209 79
    0xe00700700700418614050120241c500d90424481c2e8114001c102103038018003030000005000000401c03039104100d0032036114482e0200042d43c1a8001c28074940240901c0d115240100151011490143c000c141c40e8010b00d064251003820004520003000407910402e60403d540310521882d0080a0710f5140220906001d21210034200044c01d018000e2240e000000520015009540f24901000098025002403150101081c00e00f900422400e0f110303c06c40341900d0340500f0041d040540c02c90101c510303402c09540281c0041d0321401c000021444081002d008120b0480244103002c000005481c160400185201c084d82c01c007a00000065008100c10301092010b142000e036a04203400c03c40041c200030a0760326003107080d06051208404040d0404402c0090150342404070308940001265601d600e4440900104011036080691790f402c0f40041105006510440b07004684641c01d0900f80810b03a0b22190105030004020840f188551004149400ca01c0f0001c0000c00259008141404801000300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 37532576 1250 37531326 37531339
    0x18050d03020903032101060306050409020a060503150d060c170705030c0304020a0306090b0604150b030604050402040207020a06210b060703030e0f0703080306090105040603030c03050903010b060705010212070306080c 95
    0x202e00e42c0b420020350b88885542e0b080d800d82c108443e0014000500d083c000c20002078203008000ca4070b41054012107041d5035001d0308802d041c1d441d00c03404903040c1c0c00103400030301480c0900c105a1411380d940d11588202078003c000008610460450140030003881304001216240d00c04100071609802038183c82e40403200603091980d0780e586d880019040b600b81c0e00001e01a61030a1402402c1c0400c004149216a005403810403120040d10f01e0081000814460303958440380810000c0d4041c24a5004583c026102920141c1064481c0e0300003040c1180c030746c0045c0e00180c11076035034483e100f80d83d02001111043c113000800c44140c5260110701340e403050000103001d040c0c95910b070380301c01a0204604280f0100802c25074412545900d0070800d264000c1e80e002d44201c5581c000807490345011b21034803044a90507100c0d1000c0c5101590191a56045000526490355940d808214180c85880080c02094440c80c00142e0381d500c414017000024502525500802d8900342041c0841e040c00210346540f042e089407003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 37533826 1250 37532576 37532587
    0xa0807060c0c120201020d0b0604140d020a081504031704020a0509070207030501061404150509040b090304030c090c02010c0c02030705042403031106070507020a140619021018050d0302 81
    0x5803200c2c0e0b04580014182040b000b4404103165066010f1704940003c52410b11107010820708004040c06203001d41c40709002c403040c3c4101c062a080d5586020035102601c424a06a503d6400301d0402b5200c0356522003c4010340700f00420141d20601c02c1c00310540880661006051070b4010801c07500850140c94080d03800540072407a0b45008000c0e00c0000e5910000034031465840350150048030350720441150082c0e0078207503014404410442138a041d03400c09020056180e2359526080e210100151210304280070421000c07001c524145902d5025055205002c5409955840001c3c2102d49401400003006507020700380d00103070303000305001c0101c46044902103000f285030301c10b0b410114407642120b09611403010700002007580049003001e007610780909403034603560340c46000c0da024810840000e501440795802400180350780076401c44140000f41005060400c80c5e6413001100c1c0382c21081d1300c050b82c4058500b082414840c090340ca243c102044031041c03a4032050340c1e105d40e911688d1002409060b0082034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 37535076 1250 37533826 37533851
    0x11010305091501091a0d080a0503040201090b0a080121030f0807030609060e07140307050304020d06091b0306060f06050f0d14070804110a0302010e010c0c05061c0501080a080706 78
    0x282601d0501031211966996501c042003002000c40c0341c05d4889003105802d0354a041c0ca803a28904040c01d40040e40c19182262003082110741e035200500817414448100b001040b2000309401a1203170101c1603d0f011080c0d4140420300c203401107a2920704006030000d1072140c00181d0b01404407040d03400c41d0b013008410340d1a0400180c0240485070022080d103403500c0340004403810001c81443c0148107036110010010340e440d40441d458402150000c0204408002040042c200342c01e030105014081d05002480400c60ba07a0011882c0c1c1000a04004076a4600140240a403900c1200001c0c03181511511026140040242c100d016804080d030340802d02140700500c210098000c00b80c81044a040c0400724641418044c000c1342d000d460903520b0002141c8205068201728550302e064a030140c4800001400c00001100ca110100f081101c00100e0f40344c00003482c1d00c3d0f12014007040714103a51800e050500121091048480c1680105019070090100070b011600c9a4201d5a604d508110301080840040c0e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 37536326 1250 37535076 37535083
    0x207050309041d010905070302040e030306090c03040f0803090607031505010e0906060409110304121404030222060b0405011202121b0405090a0209010206091219110703051c03091101030509 83
    0x621102180d400d04517071404109000c03922000340d038801c07101006500381c0703146116600e00007190000c0d04011020081400b15010380040d6900601c66141d10280742140d954a1655400a0b20fa020301035010400b4400c0f019054081c5099622100d000306207560720b0940007c0c010b042c02072030a030140421801148080c1c443d0302c101c0740a40140d150034010812144108411944100c0c0c05a0b504502c48020480d500c4c4031300c408a407001c800348000350a150450f0204900e1401020000340e0900d040104910000301c1401440002c0c6001428151903502d0200090300c4100142240b4269038810803030f075200f10041c800a41d0300040003900c2041d14403c544034000082c8550340250b80e010303644e8810040c00b400190000c040c110f030280d00b07071015501d9604225a4421031403005000c690740030300482c01c01e144c00c14403549507a070040c54a11200310b0341c1000703c3d007800c00b190030658603030f003222a003800e140d00404683c0140310040e1400f04038036481500e0340700d265200ba00120341019100e202045001d4001c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 37537576 1250 37536326 37536371
    0x2030f011a010c03022406090a0501030c05060d0e01110301060908010204080601090e120f13050603090d0f0905060304060c03060605030106090618030819080a0b010804020f0102150106030c03050a020705030904 92
    0x1b400c0080741000185600e802001d01207480600c24041000092094469800b641d41200d9111501e2401e0074148010400c840c0c100e888200655039489103100d1180074240214040c03041441215542c950400300007c11101161300100c00c0c5a004110805c100e9800041007811100d0300c41c4002501c1841001481c20310803002000380c0e074005d01080c00c00d41090140003d1001040e891400c10780d5075981c4091101c140001c545401c02038012228841100d4003400421311112030501d05101041e44070740c00546540c000351001e03950540c2d21506544280c3d0076100d1500640a5810204d0a5601d004001085004180204800c00c200c4200111480c00c0c03c81d16400134503400119071341c9450304900000607101c02210100c00284001d00481e0320669244100c4107107110681d075044160792182c0a00800d111050209411449920490000e002026108038042c0000d56400705140402c510010140c0308050f01200f12036104002d001b0001e6030006c1200c0c14014141d501043d90340c459101c160060250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 37538826 1250 37537576 37537603
    0xb130315020307020c0f06090904050709090302010509010605040608030f18130b03060c0306010512090f0d17100605030a0b01030902040609020a140304021804140106030f02030f011a010c0302 84
    0x150100c0303010840960091841202141d0843d4101c0b1050340c03c0020a01422404540110040000c4e00240c24880460366015000da001c480d030040d81d61155900705d034201002980140d40d02c40620089500a024002c01001b0468050000c0360030051025140c1c81006107104030301400194407013103010500c078a2030466a00401942c1c1d092550340c2071102030500256403501c83e000c0c1c2400900141464400c1ea801442d0694466084c4029494680341c461406490340c0c0f0a8410601c54a00c5054200f02010711843c595844500c810040301100484071000350034181215100310090007a00d620030300340c07a0f2104c005c45010480e81070340c00050b00104640c0030040e4003c0d05001001c100140a80c000b04895182c079581e24040541950040b180d40c003003034400a40c4460780c03003a914002c1003500116a0094014112408441d0440b10440c0c03c446d295442207542208809810065145c18001ca441c0200e041000b0311090120f1325124680c104182c404c0b85c148905013083c001814820041181554003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 37540076 1250 37538826 37538843
    0x108070314010f060809010e030a0e040e0109030e0a060f080403050a0c2a050a1203110717010b01030b030d0e100c141b010c0506131e030c0209090109020a0b1303 71
    0x8407030440701001c0c03c10380110800f01d81454007103000b2840501c1404a0050100c2c00ba500301aa002c0c1c00321001c4900007030b029800781c0c50f00111140e618080c0b054210142c0700f40c49201514900605114440d070340c951040051040300c505560340ba40d04541180e600a074140380803559116a90350035100c4490301e80014101500503591034403c412003130b1005a0310a210880442401c0d41c4404001455003a0f0041c0e0400c80040401c45e800280103e4441d692142c040c802e54030300702d8440e101d007500040c1540540446079100d0080960a503010700c0b0340e41804200b41c020f410702000c0c5d000e01412500018260784c0c0030b415581c40e10012544200d605d001d555031312070030540b9424002503416903212903480480080302c0b116211003500d503000d26402c1100c07990000140c90f460b51011406104100c4c0181c0503500c1240c80c01402c440c4221900b848500984262158002d402560042c00b64811004281103001e80c035040036000965207034002d0308121081c07108a555142c1951f056543c100940c1e6100410b0b512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 37541326 1250 37540076 37540079
    0x6070302030c16110f040c0c06050a061205010f050105090f041202030409020f0c06070809102d0e010f02030615070206090619020c030d080a0507030b19050406080c01020606010807031401 82
    0x402e1310981c400400c402c50301c0100003075030700c4200300444050400010105401080d804009071142d084181d105e0700944000448030b5440c81012040c0e005004100ca159541d00615108250144279003405014151106a00c6290018415107001c0e4080c002402e05840070205824092003041214007604500a0540d15070400c400320b04c01941007100e85007030601660001409030351082c59028400d642d45c000526900a0000c49040100f1240d44440c540c18140d0010384180030000010164035540c10100007003150111100e2421244203c40c4a070005004006010655580c0c42540c41000c952080482d9204241d10001e182885000c0000d42c00a00c00308a503000b4203810b83c2c1b084824401c07502074030080f07643c0700301700b6072240c1200310343c48049002c240229100104a5104540c00b4865050004040c3e80900025010503100500a4540840c156051119040c6402110000d02e4410300420206042c0e0002075105c040c003d01060400200c04005801a0f110350400070402c04440428101e95 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 37542576 1250 37541326 37541333
    0x705061e0a090f0204180605011706040209070207080d080412090303021c05070204050906010812070210031a0307150f020304030803040209062419050c0703020907170f0402040c08010806070302030c16 88
    0x1500c044905690103450180001070120040380302031070400192b00a05241c3c0d481350308008040d90050010411803013036410200d54005e080044030a152003c3d25020140d181a180c0f48900a0500c2c44c0d003000c01030900c2c1c0400009070002410407509002d803400d00ca0071003030043c04035580d00500711301941c0641007409121070000003042c00380c10b9800c50811740d80180c040185603038440c4a0107078000e401c08120344a090341c0c64481d0341f08002e0340c0f05000200c202a080c1200003442e00285804c880ca0a2050000e083c942a42240d00e40004042d5400a1814213107162205412070100620280c0070304004000150036640d5014040d040440c1e9a034850a2456a5052a50181c0050214102c8800c0711034000d201d05010f0026503c0400722140105000c0341950b0a224132528023400110501440d40441e15002d00411700091140792800795a41081c0360a004110650720385803001028852200014080c0385001715540f60b10900d50304016135a51248d030300c0c1c80c0d4103220743c02c00c1d20882c2d403841c488039040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 37543826 1250 37542576 37542611
    0x20c0102091e03010501080a08040506160f030305070801050f01050f0306040e031308010b010503220203031303050a0c1d0c07111302120604020310030b0402240705061e0a090f0204 79
    0x70407403c0c3c000300016a02c3e100c01c10382c0c8448070700d000781180e50244010000e514040700204114170000ca803c0d0005542d0b596003440034101200202c0c0400d490f0030803c258154050381503801000211750200344800f00c500003034403a1180c600540302182c000400140651a144c10160615071110101c95446161554201c00d45841c2d0207001d1081d4202114181198803a5003075070302400c51081c0b200020300d2402c0c841c1916085010341260035001c18001040c2c08540c0034000300c011401071015124607422898400ca1042071a0041d101107400b01e501d0401100c42400d80a5002c610214001d584081c90304003100010101c681ea01d6001c81402d400f0031000c9130f150090412000c0e451001703021070300c030001003000b070f4081181c07152a254110041040880c6146c102d0a0300706002404001c1c1c090760900451240f000b14542010f0365207030000750001080f1080100179406038440c4010020602c50310412101d00700d02134906011140c540b00072001344101c01d2400302803180d00a104000d1801030310b109509 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 37545076 1250 37543826 37543879
    0x60706110c0313050607020f10090321031d03070f03050d05010f060809010e0c010c020a09051003050d02030304030926060906010513050105060702010c05070306050a1a040c020709020c010209 84
    0x3d800b220080000c250404205481c103071640204031505450780c10050201040e90f02301c1c1d14003042101e44001001c14504031a4400001045403000d08001441c0d07000350a803003e42c206036508040b1411146010362011055680c0c090f40030300c407410000400c2c11708913060b02501078260301d014540303800010703d10319003c40d80c021514a40c8605100e50380d02d0800030308840e00c40c2020741280d08050302040442d881142880000b520003072490440b1501c880d00e01007100c1003110980710a0040440c18030500c00100b142d150744041314402103165250607a00244004502d1060038800c3c1c1e42000d0b44807003051080000400d290f0340c04101c0b0030710314050134410360b68003080c0f00d6075008a996030132201c804003050081c18140e44018000516200d081c0d4011a00307848500415952030040e03880210000300c05000e018001e04c0d840a01040c88403c0743c450074103050118900c24440c0b4949040c503203001d60003003208c01c101c4401020058032181400c00e0940640320f02c080c0303158461a0745103e00000741c0381460118 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 37546326 1250 37545076 37545097
    0x70806090c0a0903060b1909050405060c07240f050403020607110d090b03042102030d1505130504030917160f0b0301210b041401050f011202060706110c03 68
    0x1400d8864140d1103900c2d01c1111150070014004000c1803021401a8200b00c1000c0b8001c0c146100899020b1740f42100204103801ca90b88081c2c5030303024007007400004c00c18150003502030705140e4600885640c0e0204001d2245852440a100d82d03a085e0301952240d52048000c2d4040b0b032402c1c40145841c2c83d00a403502011034241001c039200340400c0009900001e100390101807243c69034100181022006a0581c2008000721151121210300c45c407410650100c0b180219943e4009580b2a1010102c1c0e1041d030300080392407040d401390381c2c0d0108081e649101550914408001d0001600d4a840c02c0c03c961548442c1c00c0461000c400c14400c1070340030000500100310441988428440c035480300d14982c5849064800c3c2c41e18413600348014400c440100400c1c040300c00740380341a100c405039255a00038094104a40c141d55090700c030782c56481098428000c465000e1002c40c1c1011039907050080190044034000c2000c1c1c0294004203030001048065402020f84c2d0b070030604455220b201c1203107655943d910515812 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 37547576 1250 37546326 37546339
    0x90e070923100506040f060206060607020109061b050610090b06030108071a120703020c010e07030b0703110d02031303090e040803070c03021905010c020d0c200303070605070806 78
    0x2400c030819100c0c1060780c2607550402440701e42079499900c240c1d0805049038880640b41a4002001c0d030b2404000e01c02040320310001002145001c5000c0e003490002004e85020301403c01c500c40050b0303444224001a1107080c1400b0080c081080080c01c81c60413810402003883c070900d0309000c1154000f0451070119905100144891031103c01481031030f010038400d50030140c0c05400180005002c094102184450b0300c00a507060110a6240d100f01200540341007010030360005556020742820302903043c1d13403801c403801811060314558800b800d03080000d18100805550340b00000c08400000115203169000000554590130150102c540c01c241c0300804078003084e8080000500e91440408507407007103800170421303403d40d690b03801d0a880d2144241011002c50080d0f480301d058179a0844015003640c2d002e80e000060f0707002d403c42e01030700c0d0503845002d5400b4810038102100015060701c0c003084403200c40502c5020140c0211022a180d40941140100428201001c01001d0350344442c40c0c0c2d11803c0c04030f584 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 37548826 1250 37547576 37547579
    0x3010c090503030f0901050c03030a0603140303040302060610030e0601030c17060405061302120a0c030311070e0402100203090604270204050618031e0a05010e011112040501060e01090e07 82
    0xd0350030390034034460941c15420602c05a0144000340002d001c480c0d40c181003061034006081d00b40c17403d59004403044034220f03544800034821321000300380c070072160000c40300158550b04054402039900c0d00020070492090000c02c1100c0c1d01c1e80c0c400d03000a803201048900b201c4a550310b0345840c10354108540070300c048a9802c0404007021030380c00100035000310b80144c05084a0b49980409507d13507090454240d8202d401400101e64540302000341000e1280103442d01601341c0c5c190325000382030340d01c0030160113403d5121290074040541d1429900e0382003076044808074001410040180c0c114052000456070094002c200015a1118011242c02c6211042c0c1420756a1440d802102c00720701541c0911500310005008010014000e5000404080760080890302842c10320751040401001c00201d90303d0f1908000704035410001c3c00d0290103280c0004e103000b40f0640c4c19074151103079103000c1c080c59450040c60a00114080c01420740c8031703202400c0c55100e94102c0b980c44600c64006480c05010205082c40b48020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 37550076 1250 37548826 37548851
    0x8011a01030c1d011704050303240f06031b030115030f021303020112060305120c1905031c020c01090305120703090c09020703050904090506070f0804031715031b0301 73
    0x6001d4503600d180c5504001c81400c6503c0300303441da0300000c000c0c1400040c07030b01492410040ca2407584940d100d10001d590301e140507500c048054050000348490f40420112052030765503002c400010342102a5206601c1e50742da011301d4903c038000d1103c0141c26440000003c510044040c44110b011a07d40d24144044103070310314000c00320300c50210980040e00c00280240300661040190301070b81c10300c1b100c0100b007103605d0340c50310f5041021010190800306400a1034202c8144140b080c0412200001000c2c008481540c4030b0340d459208010500700d03901211b00c44180e195240e9410b682100b243c0000811020304285005011940a501c85d280f15101140004808621034007982c05100e621458554819241c02c1d030440c083c1d0050081282848414819840141c8691198110b5940180010085418501c1010301124080205681005125401c01003c21380000c5189920344c9081031528560381c2c0e000001c003018866404d4241d25000342c0304080c410440e00c071241c201c0c0c980c00301c0080040040550 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 37551326 1250 37550076 37550081
    0x20607020609060711010b03010c120f150905070c0b04050c1315060e0f04150e010509090307080a0e090a0c03060602031e0304020102030f03010b07110402160b060310020408011a0103 80
    0x460009283c2d00031800104042c0c0316506001052035490004a080300741d400000e400e517921310141a00182280d2101441d40c6554011000c6019003c40c0c200044415190122002c8400d8026441181d440300d0102e0300140c4240c40d40f210950304141c00402c030b030a16140143c4c649040e1702006100700030360f0203071480015140c0304d449900c0130340e00e22100e40d032843c3c540169902d0254521207980300e800020283c296491724000e0b0411102510344803003010341070800150b03142c1c1c410b03001203000f40d8802017001483c0100204450b501d5801c160050707124034500e44202c8152406250158011348e030f200910980c081d940d00801010112502d09024a90b214001203a9a0045d68038498800c600e0600003070407005042d00440e04540180706981c504030103490810102c2d40300383d0240f2401200000c10310140105000e01400c0c181c0b0807502036140c03409008012600d1201d074a8050300404507000070a02c40e17070b41007209040d00d0560a20030743d1a90340e02c9680314002d024075040c40003203046045420802d584a071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 37552576 1250 37551326 37551331
    0x100218130b03061e04021315290306010203040308091504080102090102010e010e07180204080a050706090b09011e020a05010513020a05090103020603041407030501140712050402031902030102070b0411010206070206 94
    0x910701010551712a02003100943c011004100415591070050300210f04c1d21540c003000c2c00d03005851008506c40c005074001c1e05800d90705510360000c800d1003070010b143c2c3c1c0030007150708413504408a03648603403403800080c5034500e5042042d24107060009002804c10019009000f030310109030000c01001c02582030780c85c00da0f0600c0c0320300085504040e4062044514103008000003408287d401070a0075129400c01d0700c2c00405990035510b641c440d01080118035417101490003d0900442c105080c203000800103400c5c1031000f103c4108c041602c21020034800e00c2005043c4605421034024442400c041074200c0720540d0f00c10080e8000c51405001086508041c041309040700d6000d05001d10b55a2251101c0700404d800421003c04c50207134810001c0481c2c1b00340506c42c41c2070755440302c0351100d00308128040d1001030300c01400c5001074200002c0101594003c65000345d00000c0d4004a00d2101e26440007900a20440c8801081014200188003d004c2000d0100005010a801703c58182d240c00c1c1003640d03580e004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 37553826 1250 37552576 37552621
    0x509070609050103090602040807030f020a090e0d0309050a02041a03011109030d0c0c030f0302031918050f03030d060b0301080c1923100e09010b0c100218130b0306 72
    0x107040420655111341d01800980380950401400c2c1500ca03071074070741460303001e5005450410340f15224105500d00b0091000080a01610402081e54a140d80f1a140c00d031052280d03003819a68210341060090074040c500c4200c2d0f00400c00c00c200320000000b8800507580c01c2440c0d02a619108090030418004011524480c0000700284803250f4810011158038026a00442700f00640344000400a14248880e10045100e9005103488146d4480c0c0c40917041013134208441005542c19503042c0380703aa03a10340b4005888056800c81104850311022928500c00c503ca0941803500e0300744001803c40c882c40281d81641c440f54250340f0300316045005c10107640e600c61209412110400d03005c1110b04031080101c2c01d19840007214081895445000503600000303685441c02003400010030014a1400a020501400702c00d020076007400304906000342e03101c079601c004181c0c0c1c6a001503440c803007030840c40488444c03250081a28001b10b81441e25a00640341d03100711a406440b800d008100c0c25581c0c4c0c5940300c0403004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 37555076 1250 37553826 37553837
    0x30309031403040b03040b070f03050c0702090903220e0108060714130e1e010605031b0306030f0a0804090b010503060d03030c030f0c0306062c15161505090706 70
    0x259240e940d03805a101c040c0300110b100402000541c400d0b2040a14420b030701400c084040703440c140e10042c090f0303164090b01c1c004152800b030811100740300e80400d50f07801c076805030f5031803074243d8940720104c0c41d40c4180c4402c60000807100400c400c2c1d0342c1ca0031203200103403080555441c40c10399031a50002d0342c5110032340d03441c400b095403049a142134000c00340203007662807030222002e44c480d5903850900b070701018191885070303242d04000c9100071695940c46403103005141c50300d8a245180342c00641504080c4001114403c0c07402c0010120380303555802c00015414041e00c4041c7d9800300518649222103600922641c003c09080170042d90071f5600480541c1e03c191070203031001a2050702542c0031001008907208801c10306950741c0e0016900b001c0d0f445200c0b40c10800d901c00081c041d007080006400171151400403019282d0300c1130f810300c003042d4030124945018402d5134003420518048014007168094040b01440422514101000384020b90459840114000404001548440c1401c98840d00d00e4000e000103d03070b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 37556326 1250 37555076 37555079
    0x10c0305070c0504060f05040513120f02070f09090b1005030c04051f1e0e040206040509130803040516080c01080f060a080102030a02120619050d030c0b09070303030b030106030309 79
    0x34055401422002e104445a01c80b02da282c1c00010119661604410155600704078144100d00301441020340000038010b510205030300b02c1e40e60000b11241c90b4900c0d070400441c08a0505000e00801002c8090000c110000e00c0710b13034880d28104010650080f00b80c807a228400c2c045100c03000b09001d6101660406000b070079101c40c01400f480050304014051010001c4025452904400d912100320040d00c002c961a000700110343e4807003007510b4000c0d041007000316580003d11005030b4403a021502296002e6403c4204c5a481191300f00c81d280c805803010b44000b4002040204200d4042411034007051440d90300d140c41a11010341603030303414004e2406808034560f68041981c000001d50120f41c8110000c00c5a400303140c4488581e82603070010396020408940100318041e0028556401d240d0004080d01c1c00b65400001d4426030200a140703218550244183c0c0780c01d0401d151007034040b800c10030b4129000c841d50341001c0708050307550034961100b40c0005c1c1c0b41600706501454180203823002c40ba05940c410400c0e5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 37557576 1250 37556326 37556333
    0x10b120c0d111201090302070504020426011b090815040503030a110409110306151303080702040b090403180503070b0a03050c070614040b220f0302161205070e06010c 73
    0x1010a07510a440420542e0a128070b140d4410f10b04004a56101c000030440c0b0005180c041d03d4117070b4a410440c850350040c041400640710022240c04031f140c2e55600700221802c0245454010044481e448514440240c0c1d0342000d540c001c0e50360403c4400c02e4080701c180c00b4200c00c100b0303281101036034000c10641007080440d500d0300e80c5410003403035100090421031900b5030303811700e9204440642c621902c68070004003c01c107241c6800207680254800d4040c0c1e203894160160310301c0880c240300d40402010041b000c10000e007507444591081e02c0b241c801821a4030241010308002c5c0031044903a20b1030040b40441040412036003008248981103603424940300d4186810180c080c0d010b048010b0206045160504c11403000c24014043c00c0c0c1c009040349007a800d141054180100f4900000b4804080d80075000600c1550740034004008186c160000c200709500a00d6142c220305101a0201c131028070905510045550005140100743c0c0e2440b0b0400c07122050341c0d4000c0504c0b402c0003100c1c00c9010952050714500070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 37558826 1250 37557576 37557589
    0x30403080306060a0e06031602010501051507030804031205040b010305010e0111090f15030103060204050a092003060f131a0906030a11060d02030f0403031a15090609040204120302010b120c 83
    0x41e584030305040c007511200c403000c06d140703800440d0b40401c18171029500c5100d80c0c1d0280304031f9002d00390070b4134610710340f400c5080c4250070b9114000c402803c006070035000405041c8110740c50035008645100500040c00c007070404012114080c08280c0c0d15500e005046807640380140314480e4590701d006060341c00c00f00315004100c48081502c1860360808910040c002014004100442c080c40c403d1400603281ca062900b0720014808582000301014a00100c0c3e0039032054294070b66240b81100381c89a42d40f565a43c1c042075604213488003542e08801595402a0710078020313040154914903150908030359840c0071040104041058a0417500b6411125000021402070007885001740009000d0fa4944054640540105c0e40100c0d60076070041c440005110030150700d0700036540c0f19407600b03922440310034038800081c01480a80c040c003480340310000340700b82040c0c844009980701002d005100319101d070354030700c81044a6200102d044006519100003138131645000c1c1c41c0028204016802054413034480c0003482030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 37560076 1250 37558826 37558837
    0x303231005130906050901140c04030803160306090c03050f0c0708090f040902030307050a0c05040501140d14100605180f16020c040513020909060106020c060d0204051503040b01060203040308030606 87
    0x1020745034005500440c49a005d114060201d20b0000545507200d81e404245003c009040741424440c100010008608a441581d8000c0600d0404000810a641c001d500034103c03a80310300c8015051a84a44c00e20b078141d80110f115802214101a036030f500e104038010030b44546103000700132040c2849422140d0034004100d501564003c1d000060040243e00003074a59044800103d0745648124901800c02800d140c1000c01403130156018845035041000002c0a5450111124054680100740800707000074501d800f9445500b141c15528007400c184041000750415004150240421284102e8691070359800d41744208440714042c14140c46400c641c03d01c420031348612400310710440040124503507461007100d0160070150850300b100e44452040c8441803100400b448044d41203180100441900401c40300c40440303080341e0345c5940b0303003041422038028056500015000108032499124005c070304402140107038040c2a8401c0c03140c0e03960b142282d41c0d210b540802404000d042c4007040d80d9003044c902411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 37561326 1250 37560076 37560109
    0x90b16080d1107051c0e0109050d02011206080721030e130f020406030203010303030b030105010303080114010216080c03160605070311031b0105070912081e040b070303231005 77
    0x81c40024142c0c48003043d000600b00790b41581042030503111940140c040000001030030305110f0354426000f00064400411880750901814128401c1011684681e02c000d20765042010b08000380d17501d81c1015a500d8015018044090f10613400880040c5010700c0200c00c06507059903120110b007429400d1100700203500010001050f00c408001444c171241d400500040d0503a80d40c01a2207601d142001015580002c0469000c3e0740341c1801480842e6000580a056903c0014040012111100105c1c41c0084d200d0704102c109034203840200d8001004a90244c100b2021021510411a025030445a10407907104c0c14012410400801c03001130b019842c0b44c08200541825203042c20800130040800c4c090b0707400d05102c0b5035524800c00c50300301d402c081d0001c0582041448120020829920310b10180305050070020140401118031500302040c2003290007502c1c80400746502da41c0b0a18000d00506000800c40c20616000d0300c504030f0840c1040d4695200b0044080c6074030740c061034a0700340800c807606e100c0c910 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 37562576 1250 37561326 37561331
    0x5240c030409180201090603023a020c0109050d0f05220b181c0803040b040203010b0d0302070603050c0a1b02030c030312010302100305060315070306030b16090b16080d 74
    0x1440b58051007807403070719084511400100f0300703144001041801e49403c07500c1807510600000d030540048410f88100020b1513a606041d020500340f001c94000380481d00c000c1224000140d00f025880f041d04003865052281c011180b1030006110b00303072060300343c0b0020940081c0041c00b9640044011980d1200c0303000941c0c00890420342c643c04416900d81c406d803140b40d0700a265403103102c2c00d03060011001211600d81e081e40001d42e40c032641c0f50001ea00c030140001d442c96085c1d50125056540a5000d180d2000c03005010074a00000c41c5000307515100395210720030202c0d01d040e0000384031030102012115207003016940d8544890b040d0400c1a1720100d400c90070703a01407140103121103254070b0401c0280003016424400b00040e41c51841040454016106440100b50900c010f021994400160701c9c5c8214200418103501951010421001045a940302a0030f03611620244070890a0448554140d800d148ea54000010f840703011011035449500900700303004001c452444080f50054000d020f00e442c09241c00f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 37563826 1250 37562576 37562579
    0x907030506130c0f18051e06040e0907450e010f020d0f0e0601050d0f0506010e150f0616030e06071202071a03060603090a05120c010605240c0304 64
    0x24003c40391124000008100c10220711135003070b134101c4d03907600304c0c50f40e0542000152410100450344502d48104203040000488030310b2031180c0d071183d0980d00600f20040380b0b4401450103070600ca668443d10b02c1640003d80c2c034218036003055005000d1650000c28000c0e62860302510102e00c048400040a600010381e83d540d07090519a01400e00400900c44004180513032681d10f08c1c07031180119810740702505103107458140c4115884802180150444204550107409d40260341400c0759410303031a4000600c1d82c05144000b20b13442c1003550348540100c4404041000106042d000d1107041c1a0750065070b6030050041c489614014010754400000510a02d01055080101c4e00405d070a500044411101c08440101420103268104100b100501c000000c124022019402d0700810307200250040c1d0041c40d000001801c0c0480c100103440145501070b044500315220300082240503002407c5035542c43d403e1030340002d00c524005040d00b034011041a12542c4071042442c01c1d001d1684036268040342808140070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 37565076 1250 37563826 37563859
    0x120302090a06030b0f03010203041e03021203071d0d020306010e07020c04150801230601050904060503030a0e03010b0303120a09020109050306010605030f0a020708070201030504050c0409060e07050402090907030506 94
    0xe240041c11261001300300640340c0b03020482d400b1044440c60f402a8810310410012411810401c4104029049000443c03c00741c00c0417403d21040e0003070001d10308800010300454541c04821990602d4100c10100c03201d0300c91a04209030350003907400195050380b009006101040c0040c100641101081c011940701a0701400803409685020b100c2101c1c44801c41b108004c860420300030b0070245080d0034030202168041c00b04d082079082015004604002002c03d660301036403616480a07009e00340050440b5201e841d0003800800304800c50121a00a50800c8407604282c14008240d48041e080740084902a039030b441107510041161040980c1000701e007000005182c0c03000d0080602a102c40d0307031a1a50f030302e000c1880c1d000911028040e59041441000600042400042a02e400a609280c086001c0c1c4031410500c0ca84031042000b503511034035080d000400c0009540c44805000304250582e0039aa95500801089004070700c005504102c0075000510240d00c80d90200380d000c400246050200c24910300c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 37566326 1250 37565076 37565089
    0x20903160302121c080601031d060417030907060e04060b1902070f05060702101e0302090a090501050a12050a050102031503060612030d1508150f0c03040b010312030209 74
    0x540030324003104103141403065090220554540114900040c94a040840850303000e40030040300c1c03207040200510100d12568030a40210194544480c0841c030449440d5800030388803007040c3c500f280c0c40001002480311021048040e00d11035003206002c0c041719413400301d003a1501400010046c0c4e0250781c2d45008640f04c0c0f03640380038100010403200c88003000084c0800c060303e88034103504480c103c0703401940d04002a550f0b6074115652298152846d60550000c0307030302520a25080e01c0a14004500408040181603042e4090946843c0884e001e00c0c1103640d81c1c50850441c0c2c000e001e0141c0150001100340312203901510381402d498410030480d581c0302042d403511422038200340c92148404d240c1005050451404000c05c54106c64103d6441c1d00140c8408035542c0d40340320700086600042e45a4242201c030b145441800c20083c00000b06551800032070051808404100700c501d00d22812450005c2042070203203200b03403407007540e10602101b0a6400c3d0380b195a0b080c10203140c404201902002400d0701e03900c03942c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 37567576 1250 37566326 37566343
    0xf0b0a03030c02010909090b04020103020f07050a030e2817160303180603050601020a030f020c09090303010602070f03050c0f0a05120f060108010e060a05040305120c04150c24020903 80
    0x203580b00780030416284001089070034141c2c4405980c40c00c000e10341e004544000741c0e03180c12550900b40140d5449440304c045202e80178045004e8403a0051020203c203140d08403801e40085403003194030011441034021010301c3d586015128541e24a02c0c0c2c58140304029840d144200c0c00701a180c100c030071960f800d40d511824040c140c0c004030001005820f00c400302c01410541c60740a448241818000c619216000039a60040140041d0401403411100da050a00034084685034280150029140d0301e0140c0b4001c3c3e60750f00038031503800144a030583c00226590301d84641810b4039800806007100f103003000104001d1120b0310b04400e81c8a808080002307115903400344400040c0c0482c030f0140c03c603400c60304079460900105074403075011030b41404100d4450341d50228000d5486460540300107001e4035503040449140c0038000c00003c0b0900980300b40003e100ca090f0107402121034859820300c80100d11042290001c1c091100100400d905080c44140740d440c01c0410814104101c0c001410000903c0029140c507814 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 37568826 1250 37567576 37567583
    0x20708150903070c0609240203070b0c16080304050f0d0915031b030903030e0d170a02070203010216140a020a180905100b0405010b120f090f0106090c080703110d0f0b0a03 75
    0x9200d4100100b540076840120f90350030320321f03021410b2041c141c406526032245582c010100a5000005503e03d860034064440043c910b1550b1000e05d40507150000817680184d406407118402c0d000c02102444000859040321040d030b664040030649000240783e101d101415071001410b88400c1807114801030020428441d8505950100e1b0700c82c06420054200d40e2000864070b2240c100351111190b4a42168040c2c1c034000c080304144090b5540c1810120090050901c025819400010510307181c1400c4592288041e019582c0c10810301d17035145100381e440401c0d020081d0401a016810800300c17001c0650300301808078010021642c03c0c03a80d5180340c14010521104030300b01d0344d00c0440580f02d003000c3c480c0c1409050344a036000d02e170028120301407841003001403460000d50940350000d50425014401d110314500d00c04000d0021079102c3c4507040c098100e0303034481c0c0f000400120008090b02e210b0b0050785d1404010a01d100d2800c4005141500030f8903540c0007041495032200c014000c00e858040300d43d03006500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 37570076 1250 37568826 37568837
    0x605030a0f0213060b03060d06020405030d080108060f070e010503040f0b0a02031603060b04030807240207171c0c020712080a030c0c050304180905030c010615020708150903070c06 79
    0x1c648104054142c2c4112841c14803407400c40b003400a50341d0001125008013003200e62184803e410b02e40030002e4401c0d41c000c1501802410000c0d10390135001210729042e0342d290b40640d41e0f2030340d0b0fc244034a20784c00201d644500041c82c0c801844c001d035008500568210380034250340412011107031148120b00f00c090b607030340b44680ea00008111140400c92109150111246170501c030261030205070b000d05000318000545014800101982040320b443c000c80042d202c4420022205901c80040c00c00a400c541d0060719500704402c000c50002d44400c00321034160042c007080480380691461120000c140100c00e100030341c416158041041c282451001c45070318842c41c8425580c0340780c002d006061f00d2000da424418061f41c0c1d140c281c0050b801000395001d4858182421082480180f03840028000703003940074105000000311030740b0310141034000300207981545514244134103e819080f0f0f070b641014403445180750011008805402c405203042604074020307001302da041c41407a80760882e40650b103501040c0440c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 37571326 1250 37570076 37570103
    0x705090f01062f0a120f08060909010b090903070c050406030b2703070804050f09090604080c010b12010203040209151003050c07060606020d080f010f06080402030f070602010209120109030e130605030a 88
    0x40f04094250701744003520b032080c000c201103c030281031a02c028024031701c144040e8000581d1207a0941c0400480ca80c01403942e0000d0a0000169441e603208040545481c0d48202c00401d150405000e494200d9920540c01c10139540d4014002c03510301c03101c00c044080c00f85c0205404006d0f03541000500020b5024146080e5214034003400c10100070468803106005120382c00802207030300000707da140d5206130000d00a55503800141803a0340142800b111480c0c2c4601c8070000803000d0301055001c1c6120b030348241c1e0000407544840d889900200564500503500442c02081e5150b4284660042a003000e400c521490404d03284d07580300030031703603413942c21a4005900c00c0c03007030401c940d41c4140074541182000c858030840c0c1d41420700034501400e95004060a01103034502040843d2001c0260b842c41c0100d840954038101d40724030b0028043d500010001d441101c5444140c45405018031554040903815221600f065941c0c01c107009011000d030301d10300d41e0f05030788000005454070b040c851090034511640784083e251 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 37572576 1250 37571326 37571333
    0x607051b0105010e18070e040f0308060108040206041203030207170702150307020304050d03020c03010615030c021506100c120201020a0311030f180a05011d0705090f01062f0a 77
    0x312241054100e860703040c000104101c41920b0602900540441c40e60a000c2d070001c1113081c500502a0f0210061015000400062201140e000380b107003407090355110a41e071203690046070404025500607500c140100320410145080d480100f0703403a4828180541400d04c9900c03018207050480d0152b241c04040020020118984090009140c2e0003c0364140d0560400c90b0000f581d90146014903801005c55010000c1818000c0002e40180c3c58010700034000107031034001a44e102d100e8441d50700c02180c144030214401c0c40c00440e00a8802c1c400c2001c0764441d644070320400038000c451421180911070802c00010200b5803188000c2d620a4180d0005a42d404000c54001c00b111a0b140f100c0880c00300a01c14000c15400c0c0301d2601c1d8000d0004520b2103c10003203003184904000030000300804a610385040d24400ca650311400c6101c4203e42c07015611816910000d01441d00001c903010308001c0d6001006104550003002c40c40103180340038840401210381080070520700c0948510354030361035000300c5625041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 37573826 1250 37572576 37572607
    0x607080d11070b0a02070f020402191d0102030324060c03040e0c030103050c090901020c07031a010b0c120f040f0810060503070f0e15270c030c030a0b0111060705 71
    0x1c80070060903600d03042c0c254076902c0c0c181e100941504009a0006105418400542d0b0340d0500150018011550f4050120b209040c401d40c0c0141540410b4001e041c007070700121380707000c048424241a00035610303581e42c0080307180c660b6039021b01d4061303800c18000c0d502c12561240806880d81110f000001e5956609100c01540341101c01440308034607440420050000400c00300d21108030b40f0341039411061031344455000e640a8014400311589600c02d0780c80010a00c440a92450561013441e55080c3d1103036218410000c00d48a480e030040c07460b5018010f2025144036010080207400141c014580c10240c4a1003084441d8083d64003d402a5006138244055042c00d84241c1c0e0003850110010b000c007e103803441d54405010340c0d205421005100d400090031100e204903060326510002403a0024414507528003401e03124080c041d0240580400740011102051141180c0c0925890070000e402c40e030b01c80318043c0282c003000f6022410080041c10200e1010401c0000743d00409654503442d45418032818007066 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 37575076 1250 37573826 37573841
    0xc0807030c050604060504030209041a100e0f060d0b0c0d050709060e0109060212090105070b01030602070506070801060212091305091b0d11060309030c03120a05090604050d05180607080d 82
    0x201d803c0800042010641010840e001c0702d6041d5a802460780e41da084c511224002c6881c80403500410b2400c20824084504401c42900c85034600032400e52266860a14520340c12203040e900040440e0040c0d001c01d83c181340c10303a03105c20003240d028941500200303a10241d640694846000c151003440c00c2c03083c26000b440b03411801c50280b81c180055171400e1002036854400e020500004840040c0c1c0100692048080710003e070f4001b600d21030156034070715000d00203600c02101a10640220741c007240342c2ca84540e02c200d040b607400e0b0380200030882900c9007492603a800f1000d155803145104c10300c0840da041174055944180c4c0000701400799540030091403080c00d15183e07015403081d000e11309075100242c0c01140342840c040b0150f904544075510f4040300c1b0328511650400c54803030711021924003030550426184031311520b9005014002c9803100340400350342d41c20540c2c0060003600810200548940710320060201e9150a400e403140e60405100414400c4d88910b005807480341c0c000500b880340c04094042c404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 37576326 1250 37575076 37575079
    0xf0212070503040c0e0613020708130b0f070b060103021b060114030a1a0406062d05150d0e010f0908040510020309010903060908070b01060e0a050a06050a12090c0807030c05 76
    0x92661600d079544d405050a0350107024509000d54001c1140d5840e4110034002c50a016842107655a075075060545aa800241d001c0c0c01103140c2c594003050111000090f03401da007042d042c0160a1503016903030500c130300500420650406500340042e618000a44418440700510040903022030350401c810707803919003a034440030b5000f1b501c040209000207110142060800c9a005079040454070b5502c3c084019002c5940f01500c0c689820948598005821584e03060804002484170201c5a1701d40c1848820b17140c0c40c00e542018003003841007a0160701540c015607940d0304001f00000e506001c00c1d1640088803285802a1a41c1c0e0f4042001e10440c2029401030307043c0070140c0020f505000c66000000c140008a000040400747c4a403012800c00805000340c03000c659201c40031007188d40c3c6030a0000c08904991010130b20507400c1d804005000d0404084941c01e4a03040e03604c151802030641010b8a141c801003502d00e04a40c1d42d0784044021404410041020381072800160101034503505214160681903003115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 37577576 1250 37576326 37576337
    0x2012a1409010f0818030703080f0a1103010909140304080a03110313050d0303020d0218031903080a021602090c0912010606050415051b03130807050a12150f021207 72
    0x900c0603a00500094120f02151904144994503511130001e0070745840c1c2d2130761041c840481c5282c205904001e40c94401c491155610015a44000c400000d444a0000e1349003180030400c018003404401b030304038000c002d000c0c1c820690031814160721130345540e00030b50000c84250440480384003010703030080c0c0d0804c2c5c1011010042d400d06903046200801d480a512440e8403a103119a021003c1500030303010740d203812400e8041152290089007000c4848610311400501c6405050048054412160440741240b60541c1d40c0c10380c0759540780301c0e2800943c0700444107a0140c2d0031400c00c00040c0d4601e11014801c488030b9800a032101d00c4001440112404519000384a904100e414050940d0100a44007282d8451f0551401c10126182c169110300c14031242081190031940b00d10102c41c000801400701c6145080c0002c243c0780e072103907450784404aa004e4550310071651a020000c40d00782d2030902440c03078000d40485c4100e011181e465070441310410310110046801150180b681c240c04031107a9071200d01c40c10030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 37578826 1250 37577576 37577587
    0x8070b07080f070f0507060201050402090105010f02060a1116200a150509060405041401081c0914030304120c050306060f011b050c0604030609110d02030d0c020102012a14 75
    0x10070741da501071041140c846280102c3c00394148583c1d6168030300002d41107030550f40f0f12600c0c0c2100902030b020445040e8001d064100c000142544070700c00c0d92010031052750242450307403114440c09002d0116840c0100309140140302c4025811a90710980361214411851000c800c1030448100f2a880741200300d003486410407620411801c140140400f00a590034030f042591541164002803007401550001900b140c646103050300580d5640101030305039001201100c1000540300b4850003860402d00d034400000c1c1e002d480c20081d1140719403001c18030a5004007600c5c01c2c141c44d81180748110102510070788001c445107108004504040c800c0a4105c0003c3d103455140c80d05810011b010240180180d086010140d1801000d01000344146118500d00400e003e50f01ca5403414040003034452024280d412406031003008070b003032410789a0319001d10341c041c2c0a0050107640c50700a50303402c2d00028049e4155500e40300c840030740c91006118181f040041400d5030300381613030703149004100e2800f0f15805960014200b01c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 37580076 1250 37578826 37578833
    0x6020a05070603050c04030b090a0201021b0f010e0a080616110c09130f05060702010c02070537050405010b04080d0903020a09090203030f0c0d14031015030e0a0602030108070b07 78
    0x40c80e1095a0301d604010030641c03103900c0350b500c5900c86ea42c40503104541d00000c0c40416800421001d41084c000d03400c80c5c000e0b003075003220300c030b0301c0c21011884035400910340d2008605540103031790810056038001c100260044e645c1c42c034241814001c4400d11120051200708504030703508011810203044000c0002d0000c01210f00110b03011a201424440c480a42410010308201c03580c61082c07449035009003507900904040c0d4010780a0100321660344094000e541c0301080d00d0414007010358840c0c2c41131850700503455004020b9003080045503084040401101000f0616889501030b85000302030b1105115030f20703071412524034240000c80da42501041048102000582d89203010242900d441a00c0001c030120544002407075841400070301100446c0100ba40360081c1c2c00480c0c500c46070700070b588640c4000d044c019001103480c030040751420720942c00c60310213010080c403195440031003001a00340081ea0440380500e041c074081070002c0c111507da80020040c02484028400f12005009040480e400d007240da64 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 37581326 1250 37580076 37580083
    0x30e06070c0c061103070501060f17030304020a030b061201060b19020d020c270a0906060b030c030703020714060405070305010e0309010c060b04020412080901030518030306010c140f030d0606020a05 87
    0x8940001c00031510b11304c0c24460001e008441402e40c0c040000c1040c02e94505100c440c1400e9031140a882d50403054030341c3c90640020044078442e96004204551450850350746440c090340151149400c600d800400813481c032004d00c1510003410321000b03404d07240d441101e880c420002c07440408408640026100b81e01e11500020790707003200c0030308039080d9100406940110342002c200301c002017000700506090100e240003a50040c8941c5000d45001e1190b2526170600030024802070312809400b603404c100260000344254040d080c110320441302c4c62480710183d8086441d15a040e60700b0799458000380d07000c01c1004001d203d41c0356021003000103182841d10f01b6001030602c3e40010b601030803107a12640c68600d503544640c1114050a0141000300c0310758800d081a0310190405045503000c2450140822042c04050284a203503c0052004524541d101001103506584803081181d1900c980490301340e52a4041c00058920000400116200c0c0c42100b800f0f420fa41d203076131003403083d50000410f6501094020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 37582576 1250 37581326 37581329
    0x100302210a11011404180e190305130314100608010e070302011d040c020706030c0c0b060d21020a06061a0a050f040b040b091e03031801030b030607030e06070c0c 71
    0x400c11581e4071102c07200584580448000c01044014001780200d402c00c224814800c101e0312040c0100032901c00d00326190340c0d880c940c0748079503542ea003841c000e90002403080c4005c00c50030000120f0009110340e00d5031900398064144da80383e078680e0442d10005086000c2032242d80c0007000e054009010121010060b00d440343e580e40030190401509480440c03507031034541c64007050208003030b00810800764000c10094503040030380103000c006410100c03819400c0d4483d1105011994010a22190944801003000746184001504076028182c0300e10704007a02d0b002e402ca01181d8000c0d6005071a81f601c0300d00e0064102c90040d0003103410f50f0b12061801c00c55120003415500081c1442c1042582c03198942403080043c0541d0b404481d2000d000540404c0501c1505d0107005000403c0e00c6e4401c1c000c029104a003003407242e1609958060741f0600a02075991b0500c0c0d200c0103000410305000615110010120303052a82c1111542c0c0800d03220401d401018008000d0300380e21040d04d1418010803240340c1e83d01c0d03890350000e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 37583826 1250 37582576 37582583
    0x12010c1b0201030603140a0b0f0c09011b0605070e10030e060a05060d0b07051801020309030a030e0f12010b1f02030313080c150106030c0302042d0806100302210a 71
    0x1610200c0c1164001d03070180b409150090030201c1600308003481c0903a03810b6061021034594240c40c020403032150588004900072030302d42d5901410580444011a41000c20a02648003030b100c0c01e1510020450034800d4074020350040d50f0b002800c0074100c0601001a00421005041603d0811f40d45103050006c00c04a41044400f440400c0e15200c0c0b03400920700454111020741140c8010040c04501c580090040903000043c0c5e1841c20300219090041ea206c1c00307200c145580603000024114002841021012000d400050400c44071070414004a10541c8502c001505640c0d940d103052407c3d0300d40008024683e448219080c030104540102c025160700000d00410928010030401c102004400000d481c0d50841c8801201c4124010581d03110030344400384510320100b40780c12065948a1b2084c000c41c4e0917140d5016203000e006144032034030904500313100b010b090001ca003090042082c0e00140001402404000c944d11030305030450040169400c10a042c40c104000c055614000c00100880c904120344d42 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 37585076 1250 37583826 37583867
    0x30406021b0304090b191409040804091508071a1602010905060a02010c09050603011a090f030a0b011805060f010c030e06040f081204030b13060e07090b12010c 70
    0x601c01e0300640700c000d03101600800e03000125000c1181c840b16402004524011500c000c148000080d1001720f010140c040c541c00c0322680720300e60100b400c080a8a5410138461800c142c5401e0350b47c5040412110b4019089080510b56001045062003c00200024000709901c0302003001080742d0f075100521400c00401800003841521a0a5a018182040040101030816540d41c134032100000c0c000d0103038034040c4010904a507000305150901d241542d050742c3e2010304516282118020901c00f507040701c00f1544e44000c25001501c003646042c80307003180880c40707100900c6d00307035040a10884680140303103840f0340441d28000c204502a40d4480303052001810a0034807032543d481c0c03414211841502541b410380c000038001000a00c201c0303100040c900700c1d03040c003003502d6a41102090300d441d64421032202a203840e040c0c40c041138a942c24124000300b0103129000004107075004030356030750074401264801c2e00c02555520301c0c81d03540c2c00e040c3c0a034512018248000c00182e0078000000c3c22503a046282e4100120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 37586326 1250 37585076 37585087
    0x5011517070905131b03050103060c0c1112010b0307060c05100c1403070509040e0601060f0837050108010501090e0309030601090f060b030c0403050c060a09030201141902061501020c030303040602 86
    0x803c140e2020103102808680c090341c405c1d149202802810f000e1008980c100c0c0b03045640d400d154451118142142e034090458071401c58010b04020440c81140784082065680c3e015007050b566003000346100400144c6c445d01078104c03444c03e1185c2400000390380e10016505150b1280c101503031052040b41000803106006440381c5810b5400c40e0907014000c0c2c80da4100e840c2c0405410030290010f81305040f6806c940c0d403041d11844508049540345010341e41d071106040c43e106000d9005003124040c4104280c0584240c00c0300a44241d240c003a00c0080c1e101e01d5080e5502c02c0140038076105401050b0100745404011440d0142d0b90002c650b86a505108000010342d5490810204020b103801500c001c111102d000b9407070b414000441da105da40148400c64041c4034884d0070080782e0602e541a14500211600c40768a03451035900151004c244000d860f00d95041c00700304402561801c180c02c041d584066500a20301881c2c111110542c2e51004000746040d540220844819560008122607015900440c00340e1a038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 37587576 1250 37586326 37586359
    0x6011707051b06040609020a060c0206030105041a19030308010605031e15030a030801260604171b010b0f03011e0b0307030803090615090403051603020a020405011517070905 76
    0x14000d8000b070400c900495051105004043d00820b60355402110380c0040c1941e608801d40340640b41141c000e41203d0203000400030703460544c0c0540c00b03501140403d06c6107840d6220003d1900343d160038100150b014500e4042c800e050b4070071000382c050681414594907600b441c0e03079640d1401c0101c0102d08a06103800c030024000b082c00000480550a0160407656000114503028050700024000c030801c88484a40000040c580b4110400081c40040054642c54489032250500b041d02031151307500b0001d040206094907080b071120442c400b020000002a8050000100515254040051032181e03060844c000030070740a01c005010304415080c80003940c0322100c000b203810000c003a07002500e00300d130104c10424042408203280e48202d4402860840700c3c0074110402c0200c0c1020340303014001850030701513001e6030381c1400d81e00d41700c0500130700460302c10204650000e02901c000742c01c5114001140300400005075044080040f1110420004540c9880c0c19440280500b41c644186072051030b40d9424141c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 37588826 1250 37587576 37587607
    0x60403200a0b04060c0b0a0b010f0f0c0803040b06031b0603070e0307230a06020a0f0b061903050c10020316110105040f0803130506180402030c0c07030b04030201050601170705 77
    0x42a40b80c9071a034a82e540e98034081c2c040b00180340156070300240704001070748007901c92160030400541611805c0b0348103001a411114220981c01c0c61050050803030403003010803000805035102d80d20580454845203003080a06040a06508a511101b840d81c40d4202c150b0303171048166a0300c44101d140c50201c1c4001900047e252016550200c02c5582c07070820440c980350003074400000001e00c192080c00c82030340d891070102d0b40c03200106d802500071250500300100103042c0d01840340d0807480081c4502001c00d9000c101c036030240450781c000c80d61a44007078844c0c4040c1c04c1070f60281c0c01002c00d50000d10f0070140f0b000f4800750103444090004210150042200207240e000c3d4055502502810300c00120b040e4070303617182c1660f030f6210365084501d0070100e08001805240c40c02c00c50300032440210041d400049583d043c80040d42020700050740a500a1013456030f448800c2215800079030144050190382e00340350a019003101c83c00381c2400d0400100c41100c080b0381e8145c44400350000d03c02c0c41c100356900131150000c4074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 37589933 1107 37588826 37588829
    0x2112020d050403030f200d0e010903020a090c020f03030405071a030c1603030e011103010302090a0507080408030c0d0603080c15060109030f02040b040c050c010506060403200a 77
    0x1000900c144240d085175480b07030800114421083c0c1c0c04808400101030f60941c1c9921502007140110350001ca1f01c00c401c03800382018542c0e182543c000c111021842d00500b600c17161204041c81c22184208a007060351083c40064035200e007030030700e0702ca07803150f6032803240d4142c40719a20900c82038040310004170707409001500c1c40b8031310300070308020340c4215030903000d0701542859510380c04505983c4081c003072040e40070205400e40f41d5079030651040060100d006400051494500410030103480d42000116421542080d405910386c0e840d80c44604141c0715034043c4501150400c000001003059503400340540e441001c00341c0d004025100305955003000304607182400900c11007010004a01c0e442c8502c5072281c009403010590350a10000726056034100e04800c00062000100902800310038071030241c014404840840c5814a0b41d111400452080038400c4084000c4005c807000541c0e8005c0d0440 = true := by decide +kernel

theorem cover : BRFrame.Cov 37410076 37589933 := by
  have h0 := BRFrame.cov_init 37410076
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37410076 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 37410076 ≤ n) (h2 : n < 37589933) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
