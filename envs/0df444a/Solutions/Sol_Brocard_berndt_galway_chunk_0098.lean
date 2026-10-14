-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:50:07.696079+00:00
-- url     : https://prove2.me/submissions/87e0d760-8201-4b84-9446-c0aed4d233e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 17446049 ≤ n < 17625905 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 17447299 1250 17446049 17446067
    0x90318040e10110406030f050903030403050c0307080403030507020f0609130c110f0304060f020a08040b0f1204050c09010b0a020a0605040c0305060a020903010c0504050f130b0a0308070210050a0c0f03 88
    0x20070074100840195908443d03c00e030700500400c0003080c02c00007449084c00a41c46210303c078800c1c002c0994110348650340c00b100d041c2c1c80346503550706038801400101d010542c03040c000d00003180300391121995462180706002d8401c000c2001d05106607010b10501c9502c0c0ca070302a001500b0000ca0074006801105100c0543d040c0f56000414651031007000340550a243c400002041a074685413545c44003150000412070b603490411400401d03c0d80305000c00c2004a800c40d01070401c41040c2503245080020450318000f00a808403019581030380019605082424065082ca016021505041d41f40c1824400003a40e40d000700701c0001c0082c0d44c1c1d40c0c009010300c00303514844005035500400b500e00509140e407105c00607411104a0134820351034542c07c5840390f401481101e08440d400307440011416018400c000b5121a11304001c0a259102d8a9000881d5912807200010390b104804c201e440c0c00450040c45104018454240c0901c50104a0340c8451500f00007540980b070742c042401c2011698514040700c4543c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 17448549 1250 17447299 17447323
    0x20c040c0c02030c0118080f0c0f040501050303040b0307020102190201090309050f0d02060d0f0c08010f0806010f0b1b01020f07030207120f080a050f03071d0301091e05070f0303090509090318040e 86
    0x1030804608c074440010491410401080b1900208841d0390002c110441e038080c822582e15900c10841040050640d03400781d0f9008055000040c104440d41140015105800300e2000060b51b48880d00c004054000390b000d40941810351340780000040e8000456650303000003002034400ca4000c43c01e40b255420580107000c98000005080c030500c100c0380e101401484003809005070309120b20b040490701d0440056207030f040b55403160441070a140b40140810b0303203070302907580d44d1400e0700320f400c149000072000d00080c00f50175803585400c0c1da940024103000f070510915801840000c135034540c5160114803034000184a89801ca03101c90f5031808140c00c2511148945200d00c109020084208103145070404990810745100105d100e5018003100105401c955591030b000b0032101810030700940b4002d0012103210010b2184c411210f22949501000140150903801100055581c81091000d401e0500060343c0101c0c1140c019810029065a40701c0784407441000d0300d00841e83c2d001549c680c0c80003004410b000300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 17449799 1250 17448549 17448553
    0x1103160f08072019021c02031c0c020d080d0c05030103230a1406040309060201020c0a030f050c010204080303060a081c05090d02090711060702070303020712020402040305030307020c040c0c02030c011808 89
    0x924460900d40b200c044c01400d0348140721040c0301c1701081100d4582c0d03581041d4010058550f003040503003005918540b004400040040c0d1100200040e11506003905c2460300904e14203840c3ca260903a06020703900c000c041401040018401080050000758022645503100380c035030402e454807480e60a19120498001030110040c0c0c0400340c5443d44081005409940a540e03094107580c0c464805900b40c1c410750b407060311540c0c00b1150450109100e8168014001c4213480c00300c1c54950742040540c01c0e070304541c004030044d4000206000d5545443d00810000304031243c003420f5200c07003070b20b001c00685d14280042d03003e1000009550f40160b54400c1022000d0394024500da0440c1040c0d84003c06031802040c0d003800c1c41c8928404645124000601001261380c1640103019680c01c01201031103048a00c0d42c1213800680a00000c00000c205001440c8182d205500500880d1513440401081e61205116130302441000000036001d030310f000c1002d01c0d2851007130030f20350603a41d0518543d24640455510409280c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 17451049 1250 17449799 17449813
    0x3020f03040909110a03080d0b01021f0203160f0210050a0b0d030c0b0709121104020d02121609061706030a020a120b01050a0f050909070305011103160f080720 70
    0x1c42562080f0030203030103465090309584a440a01c0303001005c90101400500d01841860615400d54200c840c1404042c4103a401da4004041c1121205420303400d182d00c903940101c10041c05450502c41c4604910306441d24820716000c0d1140a9180c41d240e0340d5088402d902c0b007000a49240076500026802d07400600714540e041854280206944404c1c4021500400101c0c00301e00007030b00ca03032010400d441c428004081140c0d032070355401e860100401c1240b41c10980034007418500c188688094541d03040c44944411a0380f41640c6501c0310082c28441341c009000703840c034041c040a84c0c040e42d0b009543d40c03840082c0c2c06a86500340024071304070309000e0007036110140c21804600c1c0d06130740703130085903942c030403244090542d0703c03041004840d403501c3c002d14141014092082009103801181190030103180c1094880761901e03a11650b00b551f0a50040100f0b030701c0c0001c00d01401080381c5c84901d8140210740340603001d45034040310060034141c002c2c01c01010071805201d01000440313590b002c4420042d02408a800e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 17452299 1250 17451049 17451059
    0x20d030305090606090408040501050901020a0602030a06030203100c09090e0c12210705060708060604091401060806120705060904020c010e010b010e0a0e040303180f060b030609010b06041203020f0304 88
    0x2500007201c0d40d02d05409010082501c90901039102d50203280d005103e242000d04003401100e40d5000540518110300c184c0c0070040100341030384011402608400d2011039254154010b2510301400640c10034280c0d803520798203031891603015512400342c6a044202058203103400303c00926000a910442d68001241e07003218542240008e5071107882d2400a2071001c00d165040401c02c5c640c015000007400e42d030010740000795071920408000c0e601200c010712607402c0036120301c4840102c800d0f84030b00d00e00e2001c80e5001800060b030001700032640100c04540202c0f0100d0124085c03a140c10140c8603060203140c02040f10905940c403a010f4425036803950000300802000c4c7e03141280609020341d600d40c04201880d4070031007641460318105083d40c918850280140c1c546540480c01041080c0074010351150044031040000c4480981001d450f000b40700100e40d41d0442003c060900a014108001a84c903000104c240b6071034000c1070790100d81c50340c90700402807050340c1805c1c0d0805204559180031030000003400b0807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 17453549 1250 17452299 17452301
    0x304050f0a06091a090618091503030f030703090c0303020d1713060506010509040e0c1011030f0c030708031e010e01080c060d150b0403060507050906180a05042906071a090a020d0303 80
    0x60715100c102c1d030400549d180c11485c607101e0345c03002d5102074040c7c20400c020440d00d080b04005503003000541c50001038101c0a5180c0a540d000c5035007044005811803207008040552000e0001e130341040b601f50504840c10490520f80c0090031410000700055120000140700e40c0c010743c2a2081e401020740188203000c0502d81c11a20b038002051040d2094603100420b420310b5115501e034042c1c0c11030343c500542c07414225440b01041e90308520351841d207901c800c00c54000002d401c00c6c0030390b00a0391001d44034441d080c111000d414410074160003032140c81010f5001044850f05c00142088855000da884580da200c0041e031a4000e088240b116800d20300701c2c907000061710455000140116805500108042d844501c411143d9200746040c865100384107001609400c0c0f498061440700d1440140040711040d40da07000309007600c81070840034101c0c00001c40200800c0e0511844406041001c5481d185030106541d40e003440b140d1840101203641c0c13010700000328021000c01144400c0b940040009410b08038601c1c0080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 17454799 1250 17453549 17453587
    0x309010b010908010207120c080403060606030c1b030207120309030b010e010501080709030b07120219020102090f010509060406050903120c01051501020a0302060a050a0b0904050304050f0a06091a0906 88
    0x15001900c101c00002e50f45a042c403d039420035034001820000814151b004950b0ba9a0700d54003600c50840801001000603075903c00e405c01800c01c0d071404100d00f100c01d8000380640303200c0400348804803940c0c0c50801c0003a50104444060b689500e800f82d40980d908c0c20100c41d05642d5810040028126200219807100c4410105040341d42c240e8441c2840d54910404a884041d04d1100400d000c0003000490441805401c040c0741c5640840c00050500b410005110905146809241302503540010b5803038841c28000c60303c00914500707007001d51400300b0070000301c4e040e40304a200d0b110410402084082066505002e00441d00c005441c425031100220103c13180288011b640c50075440e184000d0104455002086d2030300107030740640103010139070395824524001d014010100c114080d41c2d600c0c111f449680e2540094052170168004685840c14a018412001e0786000601c2c45203020301c1e402c12a00f0307842010601514100341c01c80d03020141b81c0301e000d04540036020029070710070004521f00e00100141c070201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 17456049 1250 17454799 17454821
    0xa050d02220b0f0a0305070c020306070c020907030e12070305160c0501032304230d0e030601080f070612020409060902091504050d03050c150106090e01050a14040e0111030901 77
    0x41005965000ca40740d1842010b1407845920018400300e0709136402a03001d19448411401c1c55418162158006410300c00221445004075502e940d0715802d42c203011140741e5001055050070056260b116040980d90300c071002080140300800258507042620507815194605000744c00c022425903180303805089005235016480c006403801d5481041e2001c2281500418002c4400b004407584a988030906005524181e103540c030301c4c441d69030b8000c42900b041641454441035071180101c2159908060a024041c2d001003440d03031042000c3c50040d50085580c0086948030304003031000803170041004002e405194803c2500368908140000c0ba01240c0d0000c019000003205e04294a0901407900b40950095029858200c0000d202c1d0000181c02070004028001500c030403580305c0c509905410f500180c003600b0420001e00d000d682044211035103850395014040489a07200c15504242212800b6008150042d1240791950158408680294480180c1409484080741e581c80d20800c40e9001c0d03e810200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 17457299 1250 17456049 17456107
    0x8030c010b0d0209070806012001020a1b020f011803150905010e06010305061504020f0318070905060310020a0e030703200303040b0f13170601091103040201080106050a050d02 77
    0x7400c1c01850410404107200354000c2c103110b203603203030900201c0f04010001c00c8141800780240e69440200311500c8080786045645d0000b681e035041003403005001190012105100c0c4a0b00e0a0070300c0169903000140d845d5100a11704040006d240705050141007040340d0002e45100b0000d100e2410742c1c50799821140ca030a000e000280016100690749540d1a68244800340c05600401d01064481c45126149111302100510141c01e200380340054482542c41524440f007565a0403c00300d1003004c05020440040034101000c01040c580302303011907114402840e1070f9040c0382e8001404410740e03014055140514002038101c481064807071405014610002d030030034141e94040c0c4202d04042ca130000c112400c1da40781040309400d040100c10051030a82241d80d040a25a40e80c10020584501f00544658034944d06002080f0302c0d45094020320032516000c01d030341e81c400410000c210251740c20110080c11240a4a02141c0d140d40411080b14030707001d991002c030307040c0b4000038060034050041900080b01c3c14040304 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 17458549 1250 17457299 17457311
    0x603030f02031e0306030109020303030907060311070809100302040305010e25060c06020a020708160311060301030f020d0c0b0c01020c07080102070c06230c06041208060120070503060108030c01 85
    0x103041e40c0c1c0e0300540707098840b00550500102800c4100d000559001310000e00082a0f411582c0c2c0080e0540d001114503500c00d902101082088a41c180210070240300e200911500e807003090703200c000d0b15100c1c62a080d4029082c2d6852000b00340e1290b4104e078011500030000304164040d01c6552619140704008001c46441c18054180c0889901001c62049039000d03100c069100800b980d4400294003d1540c0342c0542c0034060002408107001c0c004030b681100102c0040d4905401d524185501c01c500c41501406110240700610000f080c6040310f03071250b90116000010031080c1c1c54410f0005080e03810440c1c1c0710002040c2c1d6140b1050540140020810750001e4881707440c1c03174558a03030803401182c20280c034422106030100005401648030252815108034401c3d035144008200210703940c000b02192056500c0700003000184402d82e80c10115a00071031412102d00c1c109400001e001c90071b02215240100e002040c03100c4c0460b410480300c001014040c041d500b9540c0d442c620b454480e04500580030195013844 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 17459799 1250 17458549 17458577
    0xe0909010228020705010c081315030608060c070605090708010c1101050901050f130c05030a0f060c02010b0a090b010905120706080108060402130b030c0d0c050a0605031317120a060303 81
    0x214105005a2140d000b08813040c0b40c040115422640240c054400f14030400020f003843d0740c1c140d0148058030341072000b154441e04a0f20000d0803981103600004094000341c0510042300e40010071110f0168006802045070f0300c07021034241c1450410707442100a580f9100c1d01c1d055158004400c0440400520002c000c1503a40300c014500703032001111032088180c5142c0014049015140c8500441c80c0206002c2400d00d40701c10200740342100c0c040d030a40305030000e102c64204021140c094080da081d01346c402400246842004070300c0540f81d078000c286895480c6c124051030780c1d01c2101050002d1200503c4607215040607107905884001d54000e250000d0002000490320100000f449406070341d018001c0c00c11040c0342d2020b5401007040c941f0b038682c103000e001506211555445405a20580510585115180743c40e003082450304283c0e000c1c5062190074401c10118040100308801a15040b480c50108003a0050032030308103200704100f42201501440038054203500755480034058030f20170340343d42003103500314 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 17461049 1250 17459799 17459857
    0x3020d14070f1709030706020703020a060c050319020a08011401030209030102071a0f0705070b07030b0909010c020d09030c0e1012080307020c06030c03070c14010603111509011b030e09090102 84
    0x2113462515903801040844001481e69000f854164020320644000400301e41e984026519880180b400055010003800161021600014214802003070210319045685101030704240b4148504501c01545e00d403020f10070390083e011209041e1004008560b44d011600e0542d2201740007181d803484036002a00043c0201412401440c01002c0d982c9400781421703640d64804d1a0b144d80100384804042d00d8170050403403a02d41c2d055485c003c2c2601c02c00800c02290b01c01d002490907a230706000c0c0d030030004041d5042002c21f41050300102600d0005400322160707903d90300c05402201650340048000c0e41c6103001541403240ca00091801002c1c280d0aaa850f10600700800609000546400712411400c001007a0a80e00a90010384c0b2a4071800d00507036100f40195002c0c0c219042a0300607105403000b070105800e2131400142c825900c181e00350b4514108502d07d00000c01c1c400c0072001d4a2561403aa040c050180342c05113100b0040c0312001010850f252402a540b68040c1d013090140005100c13030510800f82c040c0344 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 17462299 1250 17461049 17461051
    0x304120504030317090c04050108030d15060c1712070c050f120f07140111040503070e010b07140a06060308041d010806060402070615080606031212010603020d14070f17 74
    0x6568240b10f00c0013107034007142c00700e101401d40401c61282d0302141140b82c440780542402132001070081d6031215480c0203041e05990301c4044c440c8403407210620074098541c1000d03811003081d401480786040c2c00308200074a120b0b8450300282142c91071070502005030142c1d01c800b0025200e4803071b000781c1d80700c112110f045540e1900407000c164103540090040c400c49148400240800c640540c580041d014008490300d803c50321640142c200d0761200180c24002400c00300a910001d010310090259130f58504500151a80034a49000340204204101c03812035041c02c000c89078409811001c00c108442d40d0740342c040d080ea4001e100303020383c203640309180124000304e5490550403554074030040e102641d81c0d90304100c0207510840080b51806e903540030800ca80f294411408000d4418040204014280103080614003003a40b059030300d40160800684007513840715076140f41118424100540c450004800c0c40002d02026900816004030382400c124242e0340c05030945030910350f41d03100c4105140b0b845510340706201c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 17463549 1250 17462299 17462303
    0x5070f05090402040c1b08030618090c010c1b060f0e0103020310031101090b0d0b18040c05040c090905070306060e060901050f0a0c02030f060402090c0702030606121f02030412050403 80
    0x451007000401506040d0061454901c89182c00c441c5039100340002c50728400c0040b010b0305d561701c02008000d824200051061102c02191140744118a42185015620b8009003142e0781000b5081521304200710003064881d0300202044800c1076081e4441000910200080c0c8200300002c0b00260f080409500910881c2c0c080c52248402040003815610307805403008a5801e01410021020780001e100e0700d0380d501500c24005d03084804a2035220030030800500340004030001d1200225082840002150b035402d10003101d03c161004900d00c48840010790780f00450340d2180780e03402d00f4401080f0300190b1540c4a542911101d81303480c0380303440440060200324002d100700346010500420244071920182801b802a0901501d407400c81445c140c6c0c00b0a09140a8011410050307001c6424041181313450f18209a103c0452079055050881540010355903a601134001c6009000b10311000540d0601881814480c0c0741c4800941060045030103071900030b500446050390240020310034010058070800880d01142c1e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 17464799 1250 17463549 17463559
    0x709060f022d030a0903020f010201050106050d050a0605041d150c0708160c0303080906010608040c12030309050303130203100e030306060a030615030501031b06020d03020a0c05150405070f05 84
    0xe60605050740204240052400c2d215061501c000160001c0005100d98802aa1a480c555185105018018500c0742d125410742e41010010305c204d0380d000c0151224105818000b00b907644403489101d0043c0055000310b600141020060681e01403410b075401e02c1d00d1901c4044540d400000345005881e0407083d200da41000c3c204105810100e4402c02c09090410741d42100c24040340b203295110314689500d81d10403000700300030744100a410402840054010071050900702510302d0113969031104e103140760280c8141d00e5030003002d04051601c80da00001070644d00c24202c030365a052a0b450300c60b460382007000403031091043c078283d41103140481c003803105d410354400c0003103086440b5401004a0303500720314022807c040d92104001080407003c2008010304800d514001025411410040403445515210869050b130300f5408101466000400c2c00c400c3c0c800d45030040e1100040380b0112101c0003c01c4001d0020311880045141c814005070b9424080c0b441107048a440b0b13640c0c2e5401201c41103d43c411642d200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 17466049 1250 17464799 17464813
    0x10509060a0314010306051807060203070602030c0d060308041703090307090b01050c0a06060e0a180303020a140409050601020c090412052107080a1503081602030c060301060201050709060f02 84
    0x190800340d015118000c002d007404141c014425074850300700c030001d0384180e5800352190103000003292125000348146880e4000b41202a0416202955070300c9602001045154000005807101c80c8090594401601840080c44034a0b030fa81444c2405030407a020345481c0f00ba401140d40c00000f8004100c582011000e800307410203500c0c0c94a201c0041c131030380d00e481c0c3c1440000c0150518849081c0b142035081803080c400001c141e0b04007143c49040f03203801401c5684062400860090030605926403001c002c0e41440e025030746600580044990b02c3d42d0030b024021803440840e001c0f5202e1071030b400072031203440d0030b908859000e0700d507504200e801c040a40e8041d02d2060b80c43d42008420344903100a10310b1407235030455480d420164502200e00040300720b540c4070000e0703400404e0004804c094010300c040d0f0116020700c110b0309401c60b1595105c91080c4400c00d80000c029040700c03030840d1018840a0361b640001030069032290303951140603019000464031040001c541400c0854010f0042401d100c040c0c0c81c607030050841c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 17467299 1250 17466049 17466067
    0xb01080c07050703020603041401060f0302030604060b03030906070b01140402031b090402280e04020c070608062103030a14040b040303020c0a020418020406090b30060103030e090a0b0105 82
    0x41d4003468094803140507000020000d621030710002d42c052441010300e110b00401c2a8401c5003181d00380d4006a215034288041000580e8000841c180c0094001c9400034040c0c0c148400203146200b1400312a0700000046440d4003880f40c14003d00303040b10000c41d400242000c2e02c0080104a20089401440002e0a07010705464407441401801c1c0c0100041c02c010b150540942080e80d100110449200d04041020044524140c0c8841c40340c0c02230005032019401d1983c651121a1601841c1c000c84040082e00b0740004d100e40d480c0031b8441c02c40f1030a110324094030381e1400350300e40c1c803a0b1089669000c03003130a01148048469030311150030300c96500300300105515112035404401035072100088042c0c43c40b94480310b01c056aa540f00d000c1459951551802a00c0700303d10622058400c00d502500125141294203036403038854180420400c4110321428030000090a105041c0c060a81380c0a01d01c1e1003080c0011040507000320400c008000211040c3d9030343d54074081544103884031990b5031800a4018090380b42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 17468549 1250 17467299 17467321
    0x17030717090109210f06050403200304050411040e04030305160c0305070201030203070c0204060b0306030d09050d020f030a06050a020405011e09030219031703040311070602150403121b02100b0108 86
    0x41d103402448013aaa80d454143c5690030305009000b010fa0746940e450f030a02040540200c400c0310041400880c031081000001425502c9000d90710901d4040c0352900002c942020f04141180c000d000107400b5901c640c105030070018000d00045800c021680741c01c1010122042c0218084030410740e00d07581b070515181807540110301031b400242440301406294581d02c0010b9485006001c003810742e8952040d02c0b0314202c81054503020808c0811014407420071028032454544503200d82c4180d03016645154200603c1000c01d01c0d0040e28000030305034034a4601402020308050b00204116503099a5140c0c941001c180301d4031811410300e8903000469200802040181421022100002240d02000d08a9652a1507082e00080c02015000b1020340020802003010780140b4164030500d44000202403840c01d00320081d5885000240c0490703050303420b00005080501c1460300c010080130003d010700607003e008a008a520081c1001c100c00740c000d908002e58900018030401c13156180c140d5030504c40e9119000200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 17469799 1250 17468549 17468579
    0xe06060f040612021b150105010311070204180b040b0105100503070f03050703060f06030510080c090103030e03010b041b020106140f011202090612090606010c080307110717030717090109 82
    0x20f4041e03070244103070328040c0a140000081350743ca64003d412880d020011a03580303040140c0005061503e00a210b43c1340380003402c16500329aa043d070b0006224203071307040c00b910030a50150009100313068100400041180d4404031604036642904d403289100140c1f03c09950383d000845403040000e410000400b941d9100c0d411098000900c1c4c240010032030344a00d41d140342c1ca00503400010100e074950050000c00080705804400810122010340101c58600700050190386d41807001601300070f6130080710541a6000e600041c14207000070800c2100c4c41070b4a548000a00031808441e015519040380050b42580403c0b0201e2080e0008000c181903800340001541c0c600b031079074940e00c807944d800e000303074045070715081d004118030702012180001600d0806800c0f031901c0801000103040020202149000483c0d075010750b900000b882c1020b0019200c0f0b102603601d043c00340c0e44040c0d00708003081c4d00160030b01c50200c0180302c10390280848200100d12810703141010700c11201d00f140003540c940740411030148400705031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 17471049 1250 17469799 17469827
    0x50d02090411012106051201020702010504061202090405010609050906030a0b0c0706060b0d05010f1505030402060903150a051005030a020901051912050c01080105010309020f0906040603020402030901060e06060f0406 95
    0x100c1d012040500c607406000b200d01d40c07501800385c0e80b04402e1101d0b10b08071400309041000580203602d081103560008000e80078611440062000a601043c800007081d0140d901c50030026004011643e56644003e0200000b4803075a405480440041281030401103030b03814800d42c205a1500c0d007602c0f0f403001280c881d0320000041d100903558050102d2004021002407104420110000c02c0d15414803030214101d0f83e555000600303142c9802c155005079500b0505a1754050b4049540c2604d51400c4d60110741000078000d40c2c129214450000c01141504c5540080c1c082d600c1800055001c940355010306945445aa002a510811f200c00410142c5001c80f0383c400c00044551188200640d9403511035a1400301c400e08684c0d9070008140c50b5030340d581c081820f5005080902e010f01480720b00b500492032202ca41c16810f401544810f00061480d12680c001e4401180d000d40115500d1038840c002d24004c04440c029040c2c07208200c03010400c10301e065815112559002003105241620300102a22040d12010348 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 17472299 1250 17471049 17471057
    0xb0103150b0f0d05010e07020607090602070e0406180b04030e0604060207030209070c0b040f022704110312071103120301050102120702040b0d050102031e13020d06060306020403120801050d0209041101 88
    0x4400034810302401383c18002c201c031480b00042400e000030081d040400c014074650411001100800c0026400145107040b240e80320343c2c18140f911541010009071042c442d10a0008020880140410446012607841075020340c1e260310000c1030000c104901032082d8811140164000c02c0c040c405850500308a503004012810324036045400b030340e680000c5440486080d100798200c660b0820650800c1c545000c000d10020200d4841c4012440d440022404003810140592409100c0e25905840c1003280f0504000902c1079151070729600e03e0441c60403600442071600902136415590b900c003590f1002e032810303120146c0150842485466450556422011007664010b17224181844203480d44003e11100034011000580e40303151400c1251440c07000381c840c1040c000c5031003007040003014100c10721100b0300d03034120350300c4144141d5428001c025100c07540018100c680f00003000410011040100c0d00425840d07110320100b40c0c0c1c3d420420075103151145000c0d42200c05640003500003640c60b0300542d00c00c441414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 17473549 1250 17472299 17472307
    0x7180f020d0509030703030f0204060c03110f070929090712090213020901020c030f0c0103020d022808011d0f0402010201140a0e010605030a0210080702120a02100b0103150b0f 77
    0x20780308081e610150740000789500001044810300da4107000c1e40c06080141030f4150b2a1610b40030005146140401000d010004150840030070982c040c4803020464104504465640e034840001c44018480382c110f5150f07039040034200c0d02c4288031100311a1400c2030001c00c07240556903041020350780c4154090694100300d940f00c445c280180c0d01c000040c50103107009100162624080070000e8904044401664420f42c8000c403c803242280000b40078030860000e10f0090b0b10303401104198006070082c9204000320481452003e0fa21641103403500286260b603555083c0c050f60f0301c0b4000801c0a0401c1c0301c40d1504100c0d4400034800050345c40c1d001790014418400003d444128001080c02c0d03079401e07907480340c2e06621000c0c03a813003442090188070040d1404030042c0ca00840c0710360004401e0079425100c0300620003141d0002d0100c0d4000d03c05020300b940c0e07490b01d0a54991f18144001c4d00c4000c1450095025450141071480c0e0754420301c00d1101822402da990807540b406d044000b046600128121552070324200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 17474799 1250 17473549 17473567
    0xe011209050a0c05040203061e04090203070e04030306060504180207080d050f04020f03070602060a0b0d020909010203040c0608060f040911040204080304080708120a030b0307170c030106050307180f02 88
    0x221401501500a20292803003140502d00038030b80d03d1096001d01d205d18014024800329941e40c44054150a40000800c0c8403005c08401050140c03115010182d0f140c0549171000400d650b07a1566184500c0c442c1c1d50800c48984c0300e10003030340c490043d801400e500d80000c03a000c0c00c001103140e00800b41355010708411820004a00703103002c2500c1f8111a0000d46080940c10f100c110709100e411800809012030242c8030032401c05800941c2c1d1180244001280d0307884203602c02c40c0b921981010032045030054582e44440c500000000d0103540243c6040701c038449103220004000703200740c4241d801000018013003072021740c4400400012b000c0c05141901d000110040402055075688000c1000308100320255817074614240038a41003d00a41c800c48550b0029009070758038a1007502107601842d501d050009403071207070001280c0f810a40c4e811001c0b54400150242e1107043e00007814848982c0100c00910a0a0702c400c1850303192602441540a9042c5a820a03641162241c00450110ba80d030700d001401c00c0e50701 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 17476049 1250 17474799 17474801
    0xb0a1b030207170406020d030b12010905030a080601090501080619090501080a020a050402040605070209070302040b0a08061f0906030e030f070602130914070c021c0308010f09050f070e0112 83
    0x4580001180e40058440e041140382c89aa103003594070388040a09044c42c00c400a034079108595001020140ea45102c0d1255545038005900f1600f0a00b000704000f0b802c03841e02c285d40341d0100382c4440114207454005035079584034400d0341d4299134060b5075104180c1c48400501003140c0401100522840c80d03000c020a156050380704060080c03502200500c569000d40c014410700b0000b60f0030080c0a0b600408c410301045802c030b0b0407103c50075030603580c00c101c41e5a0b610048000307008036004412032010009200b80c0440d031108103140110405c403100400130540140114072001d0b012116008a1f560400401585d4000d9000e0240055040243c3e89001035103013090085611122040b07507459404103450243e2180e00a114000c0e0107200b07010000010301080e102c0004c08020412402c0194501740da00840d10b450750f190701e03940d124801c0c0003034011081c81d003d400071500b40201081881c0f08003000802921500449000d81840308085d106915074940807124500c2c510740090500540c070520700054045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 17477299 1250 17476049 17476091
    0x1a0903060403120c17040305070c030512040e07030b030d12110d0c080105030d0e100903020603100302100c030903120207050904050105060301050c090102062404060803040306110310030b0a 83
    0x100f0b90b0750710000f0180d251140200c80c014084002001410044142440141c1c090b494100341c150411945902491030070188600175500011705034007410a40c1c140c0711050402501c15176115003640b10980e0f403401c40c02c6045490760180158591301800340e044142c0c0c05000c0c10040481e1091011413a121f00000904ca01e41c410f42904001d1943e50a030b0300005940001c006015007011406001422202e110080c031110700e40c111107100310350303034104070071003d00a0032124021907000d01415180d10301002c15009180071440164026155025291a0b5510643c400081180d058640c090100d040d0346400d800c1c00546200c403c1580300b03440d00071485548001c1e5031407003548160000708241c0342c01c40501d403d4403806000e9446614061009104a03030b00428020b510010000e60880300100403a8400006a90000747c1c54102c0d1410801083c480c1c40070005000b03880c0681424400345445241205c40c510040b680e0a000440e00c0c00309000203004501200d070840c5540c0b20111340c0c2c0c2e600356015481881c0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 17478549 1250 17477299 17477303
    0x9060605030106030503090406060915050309100501180b040c05040b03060604050d0f1205030106120216020604060f17060303070209040501090c12021009080303060f010c0606060203030403080c040303091a09030604 94
    0x1002042ea502d40d460103011f0700e40644200e01e0000e00c100e1a041d00c330440d42c0f651a2901c0c1c28440e01200160a01000f045403c66000246400b8002965a014944d00083c0658460102e46041068a50f9907003400d0080d8010f034030b06669442d113000e292140208594101800082d4001c80410000440b507403000080d0310340310b000348900d1101000c54030340100010102d1620300c0c14004280010030400e60000468519050005809a0b64045d4500403035218040c0250007580508041004680b0550084046901c0720258a0b0f1036640180301e111186140340496001c1d80c5584108820401420103510303c03600603220350004644034049a50341020101c02c4e4201201005004441a080d4605501d10040c105101c2c284a541141011261074481c84000d2945000300c1a1103400c43e002d900c01c40a4000007504108104441ca4940300001d48035030042c0c03001d038001181c03a0b011990307907205c0004680440e80c1c1a180c03000d11510301100b0301540302d001e85a85801403820300a0b103016448c01e00c4500c2c4124 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 17479799 1250 17478549 17478553
    0x60906030209220b0310060501080c070609050d02030301080c06070f0809060409090809040c0503040209010302040b060706050c0a030b0111030703080601090305061e10050a03083603010c030b06030604090606050301060305 97
    0x309414080c9858501d140b01c1b0034030901d0a200c030802469802c4003103140c100521030380140d5541c0440c00c01c20094811440c0040040c0304080b1341c445d003e980030025506841105040c0e80740400b003602001f4040c050100d0261024100c0e030105000034182400808244e0006400e003401c0030358402c5501c0403929240d00c16101c40b43c3c00100108503107000e1084090140c10383c1001d0b030a508094000c2421160140002401075684da15105041c1e51010305a802056129070223001600d0300841110a5800c100e100c40c000ca4205910b2800d00e6004000c0c0c038140404030300c01103013000030b140c408688102020713000740c3c1400843e020220218406200080c4030750303100240020f442041100320310303102c00c0040c0545a4011030190500080d03441d102c0d50408c072034001c101f482e160600c0c1c44c14101d10500300e800c1c181c00c000ca100b640c0300c13002c000b00d00d0101c00690124000c001d0703460249000d0f0240c80d814a040b5034480010400039000d4070f0241c1c04043c1c0f0501962001962a803114081b908446050b0000c2e6419 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 17481049 1250 17479799 17479811
    0x1603140406031a01080c030402040507020c0d03020102180306040503121306020414030c0111070e250206010311010206070f030903022509050603070503030703080c0c0105010b0406020f060106090603020922 90
    0x9515401c0e0f02e001208000e2910b80043e15240015a070740340406000248144e49030804540f42c1071080140c0c03407506200074109107541c4c0b45031502034001d6002c44c0300d081e050b64108400c0c006a26010078000d101d03641010180d03241191400c12605800340c02000c9034820110400c1020101c3c0c2188081e0024000505010030f0f5004014101454001c030301c4500f0341041080b0809406070000419013004842460300640f00a031216000e070403040e248103000460784901c10321100686603000400504880c0111001e04505000c81c00483e00c4540803510f40c0007007115510000040b40c425800380c02e51038000c1c4140d9032003400803a2445c503468051800c40203400c00140c41800482400c2c07141301d4200400310b0090000340e2034000840e44902072030320060f003840b90310000208122282800c442001c101d01d070003003040c1d40c0c503020048201d401c2801303402c006104658031000071a100152a906803416030705c1d00002c16141a50860296003c11030790b0350010715500c4e80c25002d202c100b140c4d807140c0c01600d07800325107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 17482299 1250 17481049 17481071
    0xd0c082406040b060901030902010c06050f1605070807030809101a10030212040b04020a030501050109060923061507080c030304140a110613030503030a0c030609060b160314040603 79
    0x1110007400542c03203280760001c121480e0f9245000c6842c07000e82801c011460804074001612000a20480580303014103100c204401d220403190b5070f43c0300d0303100f0401001d0000000941200c0310f018054006000001c10030810001c80d0150070032950000380041160600c0c510111317903805980301680d1000005004048900240c078000807a0b6401046920701107040c0500d030302d401d070804034020b00094502010400450155150603440101960300b1400900c05075035140000704c001c081030b120b50003156107024200d4440d59403480740061206000080307640346456442c20002c40380e60056840070304910400c14000000c0c4000003502031502d00d48095501c91506003408102442c0044420386141c22210701031000892003088070210b0740e000d03200e903a103640340052940c52061050300060071511000c0f040188411181d0460521134403150380900c0100e5455940c8020356185000c3c1140d0190284181d030f0a000300003481c180014060300c1c003840c60821220308200c2035405a0400c200080d210205124 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 17483549 1250 17482299 17482363
    0x40f110c0709050c0903100507020313060206060306060405011508070e0a0603090b130503160c0f0305012901020c010c0206160b040501051b040306020a090806180f0601050f0d0c08 79
    0x1e40300c420010045d1a091000e00003944495940200501072941e0b0340c0481d605500c00c0080e030f954090310000d42d2100e90784684000c0e549440844a8038424820f01001507140d09050207118101c1d00c91110344c0e1140501d404080e6481c4000a100200304064410410a940c1d51264100020140340e14002450006804c0141c07008100410003141c019500401000203800001110150412000d03540c142c9405c0b4900740c0d0803100c0e503500413080707101c145401109025065012003904803991001c25050581e4000411402c03048401183c00350f040385070320b81e6584d40551401f038076552004090078078001c101010a2003ca59900c01502e03008042010481001000d1103a80e40190b803a01c800c1c115030030700d060040f1552140e0b00004001a401003401015180030340050b00240c01d41c0010b41c1d6180c50041160080074030b001c82c00314401e03c1060303c0e40394544804141281038880c082d202d04a070000361004e0100c07005180304100c0d4100600d200005500301c0034086a1a03070024900000505182c0c02d84400e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 17484799 1250 17483549 17483551
    0x11806080a1110090506030c03010e070207030804050f010e03030a020619020c0a020607030c060c0f09050a08030708090303040b041202040f1401090e010608010f020903010c090b09040f110c070905 86
    0x325501040d281ca0115505011260904104690700403902402840455040803079600144e000030022050000703207a90440594161402641a83c403143d51740201280e44181c03512000d03041c2c4c001088103120500300340869003400c0d28181404245c0d003407141c003c40c6c034cd0341c03044440000503040b101c00d1000183c0d500a00010104c0042401c0d424685d18502082c0c603261802c00c02880789400140c18000c043c01364054842254010270f0400c4120f40d8050050061ba140b0b620400000b90941000309480c43c10f034802205944200000718201059039948811542c007154440760f0510044c4000501410050014406001445000ae0442c4024030501040da110b1b1102202c02c24102070402c12088409189181110b805d1351000c030310010788044650040040c0e0b00050360b60350804480d154405100c0e00148020407055000300621134090604a85200c1c2a0180101030901002031042600c2c1075000700c0c85598a1130000121a142c8180c12a01d56004c090340b14019000000b00b0010520030384103403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 17486049 1250 17484799 17484809
    0xc02060609010b0406030203061804050a050d0507031d0402090a0306020405130203040210120e0a1a01060305060604120309050925090510030510030503040e01140a12111305011806 79
    0x706095410604280028080c1d40552030802d80d01000141c03240d520341e116182038040d00740c8030602070305007418441c2e00c40c0c40010b001d036860b00c2020303110078449101d070f4115140d0a4042c0d64500454645182c00c000070000400380311742c800e80902024040e5501c60102400641c030455006940d04d00d89002d001d103818072000c0c2108071074814020440541c95403085001982802e14181100100b5428104003e0581c00c4540200d4451122038404101e040603040c017900404c0c0112076020f030b0780c03000e0071001d5600c104c038460f070807020610080200d1803200301181016442400d01e058010b8640001c11560b460850b19000c0c9940c8100030603100780481e10340120301003442d01d0f003040f0560602c6c011580c1000206104410182d5540c000b030240d42144109030040c5511000b8cc17aa100d94074031001c40c00100031300a4400c24040c4407081e4040d864001000e00444252092044210030151119002c4c145608a1150041c10460b941c803010301c00c070b1003014080c0c503910b015455110070b01d060050488100f6084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 17487299 1250 17486049 17486059
    0x3130b0d0e0102090a0302040c031506030218030307021c030c06110307030e0105010e061e040903080906090d0206040303051806010b0d0f02030c03010e040c0306110405010f0e090c0a020118060c020606 88
    0x741203021740b03890f480c41c1c081e00c0d019540400c01e8100702c1c070110700610384000921840c03010680c0118201d035041c1c0051484a070000380100c0b000201504140e01ca10a140d00254014600300c284e600d0400c01c18181c8010078080d0520380c1c0800340700d072900420354180310100e509411002003000005c035058031411044201010082100c5d41c1040103040e450700000e0465407007040304510303003441c101c6c00c5d504c00d1940150250082c0b090346481e1402401c0f640301074942003580c0c000d00d00025100c0724002201800d6103040d0703004202e10745561718264004c0c503018201c0400e80c50440148007140c08200507450080280320f2030507540c0c081c2c070b220603002c48601061142030300c3c2c010014045c0d03103001881940d054a841d0342c2580d1181d1642d145c81c3c89410050b0340300500c414203100a401c400d5408001600444000386c07184103900310a034004a610944114041c2d91291040c3c020401440c03840b8050181070049000004642c025003a0300b410074a081d5808461550b01c444030700c21690b60510099400c1782040d91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 17488549 1250 17487299 17487307
    0x20f0a030221030702100b030102090402040f0518040305030a020d060306050702150106050f0304060c02150a020403110901121101110f030418020405011b0305040e0114010207050105030606041703130b0d0e0102 92
    0x1130083d121100b04454808090311007081201a82c0c0c21f5044410001d402082156526542c081840c85007046108852003a008035000c84c6402e0582c42ca118852907060b82c65516580d50002100000e40105c3e0910050b10381e0345a011000410034440c0c14041e020b15001400c04000541201c5007002c8140c11441c01c211041c081c814154280c8010f9036081540300d0404128a680c00004030301e000a1740021403c2d01e6203040074043c06080d81c0e0300900589029030001c480d40d01410301404054038003846005e095515407506900400c8031a1048060450f052411a0070070400708541d030f01e0720100d0b107c0070b041904001810041c491902c880e400c2c4221300342c0390942c2072900d8100003910944881e03060400b07000070003220104052041080390302503c12755003a243ca55840340d110070f0b240b190050580d409481100781c0401c056000e001680c0c4942c100411040c5003600342503855000401d600c500070501c0c03000340096a00401000b1801d0098448125403d8450701e0109442d010348941041c03011450344100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 17489799 1250 17488549 17488561
    0x102030a02120d1512050d02070506090409050c060c10050f0403020d08040503040e01260604080306060c011416081e0a05060f040608100c0503160f020f0a03022103 72
    0x490104803550b1154403581c0c07115103140c0c12002400341d20803d4480c2c10b80750003020039803013414421038010324000c1013128000c00e56481c046c1d84d114103a019065024038148500070b81752a05d070708580c445e5446082610881c48090380800c20a0300000751800203900004840038030f2001a20547d584003140c1c1c055605030781090f0b200652940c68000e20f48040000c0030700002d040c00301c104100c03001066005030f0701020b5a91061009410800a40c0340445054040716031a04801c0c00258540034030307084440f0900e076407108402c000b01079000850480480d505c41d82450300c050551200c00f0b210303034011805220910000080101703d500014010701011400e2242d10b01046420305159520030040f11001030300e9118540061140342030110400d03409420000081a25000800d500504c3c0010490501c4811034040054590b80011a00088540c1d0044203013411248a0782c01030054060500541d0000e8680418560400c0a080015030150744560504900a42078456400b00c40502c0407045003141440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 17491049 1250 17489799 17489803
    0x11101090c030803040206130b040302040e01050610050c0c0303070606050301050c030906070c030c052d120706020307090b070606061e050a1d03010f0b03011503030504030b0a0617010207110102030a02 88
    0x107000107080000048001703001c42d100c1100700d5606500d1340e130052100e11381c2c900c0c011880c0d5000d404206e000700c1c00c00600329180da00500a485c055400205600d20380c0013071003000c9480d9045080d42582511401c2031900c110307203003800101009402071002103100c9003013005250a480c030241c1219203040c010420010b0300c6001145198104509181c10b006584081c1401c880d03400d1840300c0175025028141d82d060a6101c1c145401280c1040b034001b0950500c84020b94503200c1640c1005031300030007030800000e000030fa1030390700843e480050340c200040c60986940c0c008030b0b2500580000c03520386907a17601c1800403d4014500984800104502840c0c1c100f868100403ca400ba03003510800b4000c0005a0705010400305500c5160281c024000700300c400200741341c8401030910301000314007a52034102121135034000415608166505074a42030703d030514590b0740c2e8040f004004c2188501c660b50310f4011031030340700d00721848505140c00070000d6201d0070541400c0b03170302074000300360130341954401c0040b44801600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 17492299 1250 17491049 17491073
    0xe37140f06250215070b220305030a14130c0905060a050d0f0203060c0d0b090105060301030b0907090c0905010e0109140f010309050a05070f060201050106080a020a030902180601110109 81
    0x444204811041d0b0600c0c081d0b50002c654400003035105403880a00805507130300a0151174800d000e88100c4045071222124881d02c2c03109030003c4206203a05025050100380104011030704403410603400500c403c0700008800b03044030260b400c41940710452407074a05110003010640081e0140d40010411801c00e000003c4a01e080b9106050152250007120402d00040040d2910a40d4010382604c2141c40c184c4140040c90b404880c05a0300140b030b080800410b8100301540d141030741c80180103980b4590854489c0040c2160040c050b0516100b82c10000c1540c80b51800b85100c0e40c5a1502c41804060070708001600c0c10010440c0c15041003945c000400c03508094030780010807030000340d4420000c4404600100c0140480503800351583c0700b80040c03e001c0081c0058880708644404907117110781a1101e6049098501c02e201b07040c0045c00304004070f6a2104164000c045004d5503040000b40b544175540030402c201002600341c2407840859007007080c10750304098001c0904911100070000c3d105c480ea40c4403000381d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 17493549 1250 17492299 17492317
    0x50603070c0615030602030109061205030912070816060f0e0a0302010809070b040b04030b01060f02030d0b0a1203080708070c03020303040f03090305060406051b0a0e37140f06 77
    0xd80303a5a03005010b81503000403400a41d8100d001e090030707224200b5a020390300078418140140c4c50f000e00012541d4440200f40c81c0f81da8400041c6107001204010040d41456040c5a139000b80030f80d60b80001d0300c50007003001c40c02400c1403000c0c12038003a152004c058440c4907050080c0c0280140800c04c0034141d50355003415000d072503090800b6102c54031000e100914060040e0014140000001000301d809004103010b002104d1150602102c00ea03200c6404803180d0102100340009644180180d841d0882c00d504414010400900f5122040d55500311070140880542415000320b4010310910140c02da201c00029806641420030403640740c1e180d07034001e5684c03000400280212803000582c00801d8810045000155003020403540141071034142000248010f44070b0b1041404607500018540d03601034261401d00c1c041c2c1e02e07241149600441030200e010304010758000020100c11004a45290b0804104428240001134603c860300300640040c038100d100b040e4902c640c0451513070018540c0c802c0102e50301d840f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 17494799 1250 17493549 17493557
    0xb01031a01050d09050c0d050a05010f0b01120902060904051303020d110703030806030708070b0a0201061409060405190c030b0108090303011401050705030d06030326010f12020f040504050a15050105060307 90
    0x13445800d0440c2407841075a651a840140080c0300e90600000150500503140140001c003d40815811184202d403403005c0c44e24042000042c001065401950001c0c1c102800900f8503480e14007000009811201c0440d00075a2448041086009040e030400140100031200d0406224446960528030f540c0c02481c807008042205a000245007904c0622910f002840c01c04120b480b4940c50383c0302c480203604540c2200005620b44100010381e20343c8800120201c4101506a0f00030f9211141488058100200215480d52035001c0c506100140c40c400c07071482000326900094013445c4180018002c2c05c0c050945507982d0f10500042c003070325503c000078101070002428204c0c0c0d62951840e0a03801e601600c0b8001c402140783c80e50005c20725401c00050008000c80802408a4114501410810070b03002c2c0100c2c0380840500c4000e01c401000380c0b2185040500081c48451084280c00c00201900c00454003268150041c100f0081044000b960101c0d04c0d00b08640c007841150b0603c0007042140c08028081400c00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 17496049 1250 17494799 17494811
    0x20303190908030112031d01090905090109021207060212090f0f010c060203010b03070807020f0606060a05090310021801050a080402010c0204020403050105180c03010207020603270708010b01031a01050d 89
    0x30000c154000e2038030035481a0000d46960356184021004951640c040d000306d070850120700f00c1649203041020162605843e55000582009010300051000a240000c03540d6942c0303205004d80c0d6110004115061002c0041c0f01950030580000e08012445030841503264061110000c07503510412803103420340c01911481101141c0400480c3c0c03441000030090035841c03002001241c0304620100071032081c80d0946595241ea224107400f280e4403a500e40c48091250820400300f0560714169008003526061803038910304056422001070309004080054048065000840620311404010b4900fa422000d00784181007076101900900040c1008100a040008804501d81195516810340b80a0740c1c000c4020170061902c4151401c4140880754070710894420f0f8500d1302c11030b24050085400b002e901400113825502c5c4c480c008014404150b402c0354030074500000665a00008004c80002401d6940011502079140b40014048401c40e00500080204803608207040342d0300201140c1104242c0c1d80d00041c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 17497299 1250 17496049 17496091
    0x30804050910050d0506090111070b0f10091a030c010c0b0a0c140a0e01020c040501080706050f0706020c0307110a05010c020105090409020a080705011101021602061308010c11160501020303 83
    0x844942d0001540304070140036910174407000103a103030310501c46a0003c114510f840810100c01e4010002d00070b00018a410005440443c02034030640c1090390303480c2c0c440030152102c88003801e036400f03003000c01e8280d043c0300c50b8200a46801c000f654440c80d03083c00c05014200c0c01d500c1c0d1003810b500c02848181c240b0f80f510081c0309000d2040400b44240050003140c3c43d100c46440d08010b080300c4610748854014443d1b40702c42001443c003442141e041701c842c000102101490420156010382100d801c7c027002020510220000c2495400100080001035010390f56602c102e103084203402c898096503c0c012420745009101c9a40c000c51000e9441d0b40900b002911580741d000041e02a101c0c02d072009402210880300020180340000d060700c280e40b4241c90300207000801890b060700b00c0c0107010360600b203103825021060250411800038110b041001075240e2400742c0303d9514074256601c6d021141c00240681603400d541c4402070010340c0c0c128142c2d07182801040d00e8900000d569020241840c4448882c0c55150f50f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 17498549 1250 17497299 17497321
    0x60c1306081306020d0603060e0d02030d0c14031f060201020a02030d090807060f051506190c1406010803070c051207030303050903090405090d08010e130b0406020c011806060501090308040509 84
    0x420140e02c0f40041d907580b04081d45e036070090029484100c0c1e22908140e50204901008178406c42d692016500940c14404221165400ba140d0341c102801070050403003a004443d05039034011441a08807480c211030404880000c90407c3d212940284216481444200c0e6010390100844000442079940801d88080c24103203030b00c140c850340b0801040b462038010108101d010a8020358440e82c4081640c605181c000c01c2030150a104201c0102c40440c008202c40c0780c51801600038140c014000c08600b1050586c02c140c1d00d14006d000e0704203008650002c51001c081240c01c12304000941380507034854000c3c0240b074085503501c2c1040e01000b0180754403100003d100c042c08005550000d003000b8028001d90400ad1041030302c0360100341d8000c0005d11044000300b0300b12505441980205030b141c880c004143c2d00d82c0ca510f4500c910280048554540821200c4110394090080b804142c0348200d036400b083c100e51070b00c1c0e01100ea0742e0b4060390611040400800100d41d0072001d560403940c00b950080c03411781e2001c014203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 17499799 1250 17498549 17498581
    0x21060801020a03140109020414041112100315090b130501020906040303050301050f0402070b040305090102070914060109090501080706030b0d02030105010b120c120406090204200c060c130608 84
    0x1a903101084625945503d50406988207145a605000c642d0300c5900e4141644200c1c000c5060141d1031a0260300d06091a60081203c010300f83c541906142c6e1114541d6402017040d2600c080110282c1000d000b88105002c40688840ea13a080070801107200da501c400381244005e040c0709061004e03400701c0f0180102901101c41e00312005280701c3d92030343c90f4900a4001d8000b801058090a11014006010b040501c202e81005030801c0c1816502d0752296001c03100b035400085103904502070460b00160100c00c60094a501450140c21210f040c501070000400e5110b059010049141c04c00e001000024400301c0c07100306a0b01185030205400505402180b1050300c3c154009401d5841c100001401c1034000c0054071180000c8110f130070543d01d03a003a0150050040017200c221030a807a0000c600051519481050150320140c004210341901c2181c3c04218181c94800e10b1050100052440705c0780c00c180040d40d4858110840700d8100700700c102802840d20140d0045078140101680810010610346201c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 17501049 1250 17499799 17499809
    0x10e0a051201020d060512030304080a0909050406020903010f060e0c0903150702070f0f0807050603060301090b090105150405040507050402030c0f070303090b01060e09160309080304050705100207062106 89
    0x1889040c1140c0c95041c000e500c9201108007417440c016021645240203121003003101c017003100450854a0700d444241079039014107840028800b03d038200140c603c1160042c1032159000e0f00d40141c4035169a828142035959251490030081c1c0740ca0414003444102d074a0450f0401541da00646e1a400408046480d2a90040280214844003420043e400d50b0000398031050f1111650100c801c2d681e50800b8a151001900421145400c00300e8107004505048015682c031a400030300224103244640ca1700c8482210a0313442194030b075122010403001607840054034070700c0d400941c0c0402151038203855203915201e0030b001d01489a500080440c080f6201501a1174110401210072940c1700c010349009001000100b004580280098000141d00b9004980948030040b003e0302c503103255078030024070030061280641e14405040c3d4844034500480d10b804080c5106a120748010241d5a040c20208107085405100c00821944580e4092002c20f43c0a29540d200d00c0007170100c00e820401c2c580c284000781c0101d13001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 17502299 1250 17501049 17501059
    0x51c0c0206120106020c01050c07051314070c060b03030f03040f050102040503070f0302090c03090a020103090804080a060207050105060301090807030c110603070f030506060301061403090109020904050a060509010911010e0a05 99
    0x8074909100801c0b00c0a03040b00d5058089800074201c80c0019181c901900d18800e1007500002420000d504190040c00f9245d1010b80f0f0002d2010391844020754042c2c001d40c1d00d02c0c00602009032080800101c3c2c030944030341c004110025820a003003014403071090311000340014888901d00245108000003501a580500402001e94020a4440743c0201c0440500d1005a00c9803003018040380201c400f90080b00d01955070003000e03041d000041d400540140ca4610421103008504010005200100303102105d0818868000541c4d5071907039040131400c0d280c0140000380300381d240020035000070311410211000940d26051050020450307007000142c0303602030190340d40c01280001c1008616a80606502e80310200c03510708000e2503d4000034424580401d00600d00072440040854051004880142d584010701c04000b0610701c04030b50111701c0d0381c541a01d085030164000f010356010405240100b650080c2030300300807c64191581c9550040242e800301150601c822220325100366110400c1c42d01c05814007030301c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 17503549 1250 17502299 17502307
    0x501020c0d020d030c081302031606120f0501060905090a0204090516020d0305091011041a12010806040b1603020c0609030306040b06190302090d050f0d030c0507051c0c0206 76
    0x1a4940c460500a5907000140101c451a0760070034064855080022a5507452038000e0350361200030f1020300c00300d5030244d9041c40b45601242c4085500c031041d1015080302c0c3d85012000d00000d040900b07440313244120303004490922005010055100d1007500071120b0459090001d512409401e100920541d004070840710f05103002c0212160815070700144803a215421034000030b041c20411030442c2e0058440810030f400104c4010100417841d041003201c0400e111141e441e1580d03504002c2c0300041e00440000303522402152259030108150f003158014021180074003c14a8145d444480349000180001000a0000d03510f622251280c0e0544040303502c00012201c01b0300b40b041d9450390300e4000b01c038601d100701d041013640c88442c2407580076100d90003d030108000000c0a040b070280c019401c03050550340c1001020b6903050100d50208480000c1441d450043d003160702c400701e001025181d070307191a40f013845010401d41c03000560000b071300b40c0b07440c1c0000c1456400200c0340ca81110951125200070358401c401007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 17504799 1250 17503549 17503567
    0xc030309050906090421020705030f07030b0117030901050a051c060e07030207021305130b01060c050111070503071203020d0e0714030105060901060e0a0b0a08060310020c0705010309020d050102 85
    0x4503100040d90301c102c5014072142d80703410801100e078608841c002e090f1a83d03080d007080c00c1862042d00070403904090042d9116103403a1004246042401c0c203900002c0c2d44031140810a02824140c401c0c05041c0302101c0d8044048003840755503a83c8a84050b16040090001e0040c0996124000f515805884c0b0b110302c00060b60103990010183c802d9005a40c40300e003100c00030501d89070003072007150080d6501410081d00701c0034090b0b540000f842d0003001128458140c642000c000b4032044402d0340a04401d40300c44207803030080e0400e142124008011a07040071420031110700858000070a54200a510a503286150011010110041c0c014103080d442c84e281405060a846080840d1040c10758841c8594902070034070046c100341c281d810a4641c650001c00c03810040c482e15105515014080c5806460f0460701075540c40500001d900440b44200003032140014070265140502807402400c41c01c400543c01c2c1090b00c000152200081d01c242d0f410316a0702c1004204546410b00380703003035180d005402107448444003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 17506049 1250 17504799 17504807
    0x70201120501081f05070906030e03040b0a021f0b090103020909010f0e0304090e030a08010e0c0903060406090201080601080705031f050303040306021c060810020304061409010e070e0103050d0e06070c0303 90
    0x2040342c44203882d82e0900414081c544c43e2090b50704c18a40b5640300d202030f80c0b80c400140d005010522200d03000c0d0001700804140d40c00c00e000102568032040e0b00412200700080d1a40510b0075540400c2c082490030042e0341c0c0003e64803107030502e0640c0c0d01180c000c000d5845890f801801400c0110b440b01c41c15041c988011269140803000c0c0044030b03006071082c000c1c25219280b45441e442003001c4407020401840041c07014105100e80980d012000f40d01c02031800c001c0d400000d140080441d02216020f85800c0d060046507480011541c0110702070a080c4141d0a0040c0003a1081c04028a50464454881005144562011118001040d010382541d540d183c0f2402d007180a94040c007141d403003844000c0c904240120107441100d08a9900201078904080d150b80702002075400600156006a1036081c1d4010b00b0f200300341c819004802c8031000203054000d51125a082c02c0507a8801c69807041180300400c0031590110f820342c5560001c4c50b1220705054046c00083c06401100d80207040e8081c80207000c001c051f00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 17507299 1250 17506049 17506063
    0x16050303060312040e07031806020310050a09020a0c030513030c08030c0606030613060b0604050603090604020a12050309280b030108061014040b01090902070f02040e07060f0507020112050108 84
    0x1541030300d540c4043c0c0750070b03044584224403c5940d0702c2e085000198032079100703600c004200202c0143d4140700c0b812503200c4c03500340e070000d8038580c900c0d10703620701e00b0009407404809040c0102500001541410300c80740003d03105a0386201c01900740324002849610000c00040d00751702950348902c1600c4c040b516091403e83e20f40001d683e40615110350404100325107400502c8611a6034424425036003c03610341e07200e1024103815150560040000d206c040703000e9a401e4040d40c41030400310700400d464030305801040030b02040755104100004100c2c003024003007240803003158041034090720b0b0800c50452202c1880c1c10111051340d808444c000b60100403071155240d90040d4100e07000c2e82d00302c42c003d0f2214001c07500610700c14812041020340d840c20840c0c035410203400c200c400c50307070504101001c6130fa1209010141d038412442120560441c0c0c0300e00c0210325080c40340030390040f4000010452681402c82c0501014009680c0106000000c10703c003045a128603404029281031500c20310465a481003071030b80e1803107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 17508549 1250 17507299 17507311
    0x3050304050105090a0c0306020c100f140c0a050702040902150c06090606100c0b09070503070906031502040f0b0d11070309060f0f090b090d1205040e090601081b03010216050303 78
    0x100f0070001c190340200005501e040c40340c02411250312035107550b440f40000d502c0400c1c8510b85006000211481013554490440c21380f4413030b00c0201b004103a15100100f521001010316403154824044422141e611a05441072140e040d01c1c0080c14401c1400001d4030b01801d948288038110000070301c00110b08020070f0f0a8021202a0300f1900c0c292141c0f020000240901c01301c4400080788450b070040803e442c1001c0942140702d484c1515041600e590219043c003209401803810180c9400040040013200441c510340c500c0300103011401c0909001084000c0400e41c410115260b1000c0b61540c082c00041e0322484100050b400a5640d03940a4500500314030034030b100f1000480daa02414050040c06440105121f00c107554542c203849041025400c4d00f5000a4046030700a02c842c1143c0000403c8031001c00d03c4880d1fa07031601610b4600e04841441d181400405902890700b001c2c0042060100001d5800e810300362604510940340180004240280030320103580031180d040344010000d200c0003200940c0644 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 17509799 1250 17508549 17508551
    0x30b0a15060f02060406090f021201020c07080109020a15021e07031a04020901060f051c02090301061a0f0d0e060a0905060610170901020403170d0b0d0f030e0307050607030503040501 80
    0x5a507500094903018030b03804a8402681000300042c00291030713584400c40d03040c0306401c60031103514150003103141c803401e07403041040c2a9030000300c0c0841c0d80360405c00607009040c6039000f131043c10040d60225519001d00d114035001044c0c12003041c039015000b07001d01d680c030000b80b05950b800817400f0250306a4400c014841aa038661801109108000d00c4015862003560064240c00460b460301c10300304c81d030580c8030b0691f1040140902014002e014000c40d540c0c0c000b01c0c41c040140e21500c3c442c040608551580d8809a0080980190460034103c032200b034511102040c581583c49901a4074001c001c2c003110b48034101980180f03420469494220750001d11480d00400032210b05555403003d1200711500100b1480100300703081c22a0074403040003031003268070404a000150815540c0d84d150705038030650795102552140701140d003641c41c260f0ba2190807180501202c0d030000111181e260800c030301c8881040501003154500035000e80351030820807a0001c3c000a0900b40d43c0f0307071060070001c0081d00255030484040d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 17511049 1250 17509799 17509841
    0x100e040305090f090112170c01020a0c0b0c0307080705090609060c15070315050607060f0501081f06060801090902010c050f0a14010c082202030106030b060301200f090109030b0a 78
    0xfa08201c2d4185041e1645242c260034500c0098507240c00d116240e40b21143c2030b00c010000d078010080700b030000d0107444580d510741a000081c40d1500080c0c1c0d0780020a260482e44060007081107448d0322108154200c9468149a503a840406020607443e1003200341903900306900207110070034030f100000d41c0100c0d203104244200c0e964403095011000c0d00c08500d0045112641c0000a2240d4a00360300200909481030000003a19151604c1d00d2064480980c0030b92419005101614030342d0789650010711510120340d404028035070400c10007612404041c080e510209507694404011640a20480100690800b007112141c141c40440c042c0d0702d001d8038404440c0e00700c442c14010700c0f03c0414020442c6070b130542e444100e2a5135072060200080c1d0f41c01c030280d408d40110450300c0384c09a20203124280186001e081c003080d4519015080c0340c00c0d43c201c0780760001d103184030551481d0007078694002c1d20400d1141c1d085407550788142e07000403641c074421600050a80324044051040610032540540103502c000c203529006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 17512299 1250 17511049 17511079
    0x11209081209100b01021e1f02030708070c0221030702030a050706020709020f0405010c020a120b0103020925080c220503010c0203030405030301050d020607060c0f030f0b0f09100e04030509 83
    0x140c0b1020b00d44c00b070160740412160203501646020000740c007419101220410001c02c4803600c20080000c20700e11344aa40003080c0310115500c40c1e50b01e580443c80e400c5c1401d8810456002c030360038030401440342c010191001c080c17045156003481168440b5070010211a030016681c1011074845006200320f40c094400c3e80000691742005000343d8182d034103510700441c02c040c5400015240c075160701104a80c0400c26107030118a6400550709a6403840c0601c103d2140c5606500c1884480103010b0f10790314117200d0304001c01c40d00d512011682e0710000c03440e01e0a11015200da0a61130003500071500f44c0c510030a40040400e800740302c4100c1c03800485100f24024032160b454202c3c00ea0b2203210649000d01990803c200501081c1051080301ca8007510190607185401c809440790300440e00c600005000080c0400c3c1211452075147c05039160303203c04040c0800a0107520000200d40c4030101548a004182e00c50000700a0010804600010001135925441c6441c040c03800030b11a031312901030980701c1d490100180700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 17513549 1250 17512299 17512301
    0xa1206060f021f0902120102030a05010504090203030a030f020f0a0c0c05120303070f0c14010902040b030c1e040209100504060206071403011202030c0307090603050105060405070c0201120908120910 87
    0x110035600503041a01c03508107641c202100f40040011580d482c1c0800c48010b072142254a003040c080c5400050316070824400c1c08003600d20681c8268812402c102c1c481e00941d6001c4100c0354031025a0034009815854009594040c0c041c4040055a540c00420840803a40c1c001003041d107854440e01403800803680f07a10401141d03811030802c4404a07403041c000900244c1c010090b070759910341e0a040407060081c6caa510081d0007001501d03000100d075150f0000c0021410031f40182c1c0d0046404401400708040c09601152618404e00f1304a09500000035011005480d81d9045642069020b80607080c8140d1100015050364894400c0b64014400c8200160b8101e1007980d4a480340524010540d1541e464002c0341c08109030401002d0b60306010360009000305507003c001e420004e202d01d40d00440e841b45036090041c216540101294001e034200341c10010709a60068441100316824203200310340c60306030b0301c281000b03000d070480c0101100d1000501c103404400303201c920340c89640a10203e80101d900000003034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 17514799 1250 17513549 17513567
    0x21803010c050306120f01380906100e06030708061005120408030403021005090105011833030507030308061c151d07030804030201020d02060411061602060a120606 72
    0x1000003107080c030200300189811760048049900300c404070740c6140f020840302800c40d0719080001900f101d11091355038451000000410640504040900b0310704000c5c000315100e048010041486902c4944801101902441c8481a0075501400345900d80c5880d2501800003841542c809124090960560030040e104404940004c1c070525506c080c1620b03036688260307817600050400c409500030304031050300d00e00711032203003520404441c0008100380d40b4080d401c20010302c000204800050400d248480b500154903403880c492403c580f245074241c0aa04401981c44840c0e800080c03107805200c0740041030583c00481280940e8080b28070428600440c01d00120010710658020310a00021061054000d01680100a135015891041c01c004614203811303801e124013608120b43e01800800c0602c195641040492401941c0c2d000510440c05c0030b444010440c80425080740c0f0035400080c01154881b01c54101c000f66aa01428a42d02d039584140043c2c00001e444802504640c60500c00040852003a8045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 17516049 1250 17514799 17514821
    0x503070f06200403030c030302120a060611070f140f060307030203010306060b040e04030c061b08090105010801020a0518010c060f02030f0c041802070f02030a081909030201091e03060f02180301 85
    0x51450301d451039505aa44449281c41035081c07541c24842c0700b1100c2c00d102915881099000bc00080d910b0406c40041d00d03205036980018002c5d4400c90b400e0181e8920480d0307100c141d402c400020490540d190000400c400b08811006400500100600c48102c0e09900a941a40e02c40d200500c800c6031102c500d07a215004030301c40c08128480d001e02103000300740a01030101d04580039031008100c00b01c4030038848140214005600d0000f500d000700b000352410302881514050455480250301d0036101d810300500c03600403040500c8032202c0c00c01c1c50f1328450380240c40600495500007028001a640780c60404002c1d0012100d20b842058844001001c11a54104807010360b10b552180c524140304400c40c42e0002d400c6044200d907103003071701165240940e1341007000d4110944924261561102c0280503900c240070605558400d10408031400d10060b038125841c0c005943d41e040c85020702c45400a851000100720f41d0020380743d28584000040c0049454004140d01100403099403100504041807500726402580c031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 17517299 1250 17516049 17516111
    0x8030d0e032809170d02061e0610050c16090b0909120708070209090a031205040b0106120b0d050f0c01050304020a05040c0504030605160e010e0306220503070f06 71
    0x500c000201080d02d29604006040c501050540d4842c4030745048840700f814000929805014850b441070390401c45035901c410100408a0500c800040c90080380f50054940361150b082e080f0f110503068450025280b8000d01c040c11202046064000b000c4240040e004050f401400c00b0000049418900232403401020207200912039203000c003000750982e0b040384038110303100b402c2042020003581d540313045240a480c0030409810340705070b2440d0280205c50210508983c945c01c007810080400c40e040c2c1481d0460300320f4104081012032810214000b4240c8140441e40504080b544800f80400018002000c0420760201d44454208100548042c082103800940c0312082c20018001c0d401c0981003a01016501c1c1401b07400c054499540c5030030341d80112aa80d02039a1030100d045403090b0311a6a100030560b080c240114011441130100751200c0e0000e020402c7c0413090354181c5031081584039403d40300341d080810341e5115409480e081684400d020341c2916610305041c3ca20a030316561210b100160540110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 17518549 1250 17517299 17517337
    0x50706030f0b0603190612030206070f0309050615090915061201200903060105010c021c0c050604081e0c030d08040507050d1505010603020a020a0f080702060408030d0e03 75
    0x4118090218181c95564864039a240542c0c551503210245000700500b407a0600071542d0b240c0d800d000c450559000100c1030302d12050705070100c0d8020400755044002e601c2d102040f0405140f042d009801c40302e03c010324034403a4400300240030354100e5810f051350f2000c644803181901c90201191344c540028a18003aa045200013054441c50300585205081c01d050001045084030312464204203000742100058002001540f646245414051680944001d0800c510000f000d9004104603c00e00075000e6800c0000c11703124400d01030403416103030040500908141d40c035074550648075103910000c041030001c40c40d50640030300c1c080303000304541406a9015000703141c00c0304401c0c0101c4a41001900c2944c003070043c0365000c00c1c1525410721069203503004032002d124510407840d140084440583c012000c0601c1030103403880046c6d011841e180a16003000f402c45404040713042c0030003144a0740d60000d500c0400002c000802002c044050100c40b2950101004207404200c00c040d100c0c4640501c03500712200700341c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 17519799 1250 17518549 17518559
    0xb0907090605090301110307020a030e01080c09010c0f081603030605121c030b0310020c0c010807210e01050a05040506010e01060906051605010606050301081e0303071419030903080708040507 84
    0x10090207410f100200081030800070700f070142c00180c0c0152003079801030300300200d03200c24076400150000707001c18280380c1040b45140800d2052600c4c050301d00840c4c10029904801014440b987e8842e00c0480e41107040c075995400017440051820013564000c402013030802c8000259450300720340c007034085505400034103800c9076486030802c40c1c1604001000c0078140d40d0070002850f03031810130805810b2121b01d0001641c442d0a40241c5107042d100f04e80f07480c100608042000b0045d640001c20004000f070300410441c0a124940414001c0c0070740c0c50f14002d0075031030030003007011807121904042d000d58002d80030380b081d507600c0310550051080c0c03d0041101040b54208100312161045008050711001d1891017640391055a90b4142034900e01c0c0c0c07000c00041c50200c0140300b441c1b018054003549070307812105d6880c0c01c5210603420351a404010890024480844140c91802d64410100e628501e04541310740600303860340070081c0c000e108000c0282d002444480c00907800d40d00030040c2e1402607070030000030304c0d0040c905 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 17521049 1250 17519799 17519807
    0x405060405040b010512091e0c1f0311030f0103060e0303070503060607030c0503071b060309021509060f0c0703051b030a0b06030705120105011e0b040608060f090406090203010b09070906 82
    0x3c1c0c40344078104201080b01407001102c5d244174074003502039107000d0720f80904800700d05140070208240b08051034020013440794403a074a001d05d01808100f010001c0c0f9204418000540003080d00f46a08002070b4400800c100b040241e0f8801141070300d103d5602003026290010541d03543c3c3c001140d6150102d94208041009860824050180d152280c908542640590354460303046820040003225040340d0010180c402011600001c809080145001c00084100e60009842e40302c8213154414800000503085070305488032002c543d10710030181220340e92111071141055882e10207100940d868050851000c50051041c8440800d88034018010700e007000c910f484218460b103000c0c100c00d5045c0308032800090551952075285050709801800042d05600d4410b242e920503180301d00e0304402c0d0500c040140000340d5444c00347d6050341d8083c03800b0b020b155070f602c01160102030101c490179844040e440801080081a420400000b8400d800034013210b051007040c0606180b05031040c4c1c001c0342e4040828403100d889 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 17522299 1250 17521049 17521061
    0x80706031107061b020f0f030d02030405160b0c010c03020702010e04020c100c0207031b03020a031401020c010204170d0801030507060c0510090302150709080c010807020a02090108010b010e06040506040504 90
    0x2118480301c0c541038140e80c0f04070032266400700c090304280190580b04510798041c0880100200a00d0140c082071100308011f940f42d105004161000540c00300104090003010006481c02010400c001c400083d12441000c1240d08018036040b1030790300b40070018442a1081c02078642d80d99040c0c60705c0360300500790f804000180d0001d0301145114410300b0280c01d0322483ca401802c54024040d00507001242c00c6041101080481c0c81c3c0c0001c52401c1d4100400050329a0000002100d4100300c07010340b5052000401e601a2164401c142c650398000308000c5450f22681c44550502c0030740c1030881d1480341948800b580c4500c000d2002030081d8100000402c074490041c03440d003041c240309800345d940740c80707000c00d0180444001810a80041c1c0c4680c02d03404401070a5540b640e0011980e0030243e00d040d2418040c0c681c0c0722400e0071140e04021204002c01c218034020400c68084903401020034401d03685408095000700440c1c54401c1c0003c545005510700350030500c0485081d990090800b9203000c0c2400c0a0001400e2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 17523549 1250 17522299 17522321
    0x12020f0102010f15090606080c030a02090a0b0706060906050906030a14030421061d0304061d03010e010e0610030302060c07030509030f030a020c0906180601030e0d111608070603 78
    0x14031102030550f104501c3c81030139030007403204211a820600b0300c3d90310030407201181c2005003841269014803a411250400352540548103009c0540d035482000e001c5800d06109501c0624110404901e1008104c1d15401900030f03542c0710202007003400d94440c204010b1550561394545c0540000c480080850081001c003204e24011104032880e00703944403840c030900140454004e4451070503580450420845000ba00860700070510b0711070103440315009a035280d22940c411401400080b0761f0640b40900c3c0c140c03240d54007001c01002040030358110350616010b400ca607540c0821500404001552030100c1c08001c00559805600414555981010b126a02c0d13115403400d40500c081400a55425601086101c400b2044030001e9600e0b109a210064600940001114407035070032402001041c0d03c0f56181030241e00b10386402c0401c96103449005800404011034500040d008ac8401614556004070b03500101c92070100451b402c45d82c3c1010310000060071400b800a054015132000c001300c03442034016050f540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 17524799 1250 17523549 17523551
    0x30402010f090506041e090203010605250609030809010b0102030301060f140c1e010c05040506070201080a0b040e0703140307081617040e01031b0b0a11190506040c060912020f010201 80
    0x82c3c94100040041d0050390040d500c5d80e100d501002490100700e51200000d003811982541554140034006d4a81c1c0a5800c10b0080401004516061680c49103043c0391034070b4000300d00300210556820002d00b030800880c2c0c55850b40d800c2803001d0076103501c0042224101c5480787e407020118064a1011682a0b0703218a00620b00d1005200f8010118810700034400321010103002036901030f40b054041420f462036035071030100303000c03045c4010001a151601100d81d001c0d82443c040c019681e0701031111004040340034041d90031900d4012021550364000a0410a032802040c1c801980d00410a041d5620b115140000301290014000711210b51036454014407000d00ca101282c906900c180c070001010781080e44101102d4135044010401d1100c1d540140105503d2035a4880585003403211003203281c441c0308008405c04c030109240c101c03800000e00c0a02010400b08042c070010201604009540b00030070b0364142ca0000a26000040290050900d0411101c2581200c1603402e15038081103029841450600d0542d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 17526049 1250 17524799 17524817
    0x201020a14010912020105040c03020f0d0b0405010209010e03010b0d0b091504061406100207050112020c060c030103022d010c0305070813140a05030a0204050604020729130206030402010f 82
    0x680c00001e0800c04840e4100001d00a4001d0030b03c8400b8204040d0480c05592400d000c1c000441c99546078481926015100380050780001c4c8007151451003440c50140409511200f48401c100d4190014801d80d2426aa260310920000341054203d8004c40200c81c7d20141c040341d49000500801c00243e4407110400c1514600394141c50700d10601001260116041c680e00c0c582d60820045d01c0d540c054110b042614107245580c81c500000c0d41e00d291030701910b41440009403246100140b1034040702c640304d24901c2520a03070b00b002e41c4170310781c40c0c0c10a000803032003200103011440c00030600070b031100401c080c5103101000e0400580010f5400269010064080140030414500803036486030041c90704500082c107034020b0350b03d0143d00000b450002c880c200d120b030b0405034081186550000c0d807003610b503404a900003160b454141c0020000d108031030001301000105207080c0f640e1183c0529000b0311000c444034141465a4400d0301d980c000030b402034020362010080c0013080155200761910f0402c144541020920 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 17527299 1250 17526049 17526053
    0x20106080a0605060405100e04030809030c030708070b07030b180402010215010608060307050301020a0f0509060405031c08060906280e010810060803090306070f030b060d020301030b090a1203090201020a 89
    0x740380c40808103840309612241800418203143c801c55500030240440c90350f0150038044000340400020b0005401c2100300c030046948848103104881b401014142100d555002610309a45203411101040d181c03800c03500001603c103402401800d07007012000313050f85101807540c00c040d2840c42024000b03034114482c0b203c0348210011160050750290020740c40da0102d61030403400b0180340100c0380d003041d402640184041181960040c001c01c2c03c4140e541030994880b01d104003c00d00a015590103260f140c442e800040300882c80301c991420201c903041d41c402c5d0b80e40e550340b8188603824500307840c5190425012800ca1004c00c2c2081041c07802d800c40c444102c402a6500c4000940128086c1c00c070142070b0b0880c18520116400c50b10a0318010305580c0091401c101080002030b8440300014548001d10941d00c800c007003018442d9000e40114000100701603242c407441c0040500a4000f400210f40d066a07060100320701500000708940520391100c0b00340380c42e0064620403805000422001c0341544101581000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 17528549 1250 17527299 17527303
    0x9030702041104083a0c020d031106131509020f04050103030801140f0f1903050f0a110108090a060b030a0803090a03170708040206281205060103020405060409090302010608 76
    0x710000c2c0e014080e203550404c1d03180c40c2400c1c8904c2030194030441d81c00c20a014514139480301c034002820741c8103072121048514816959070401401c002e60011078010341804242d000036501501318071032001c503429075561906125200865640280c10108081c0183c40302140e5034002c1c0d000ca0384090549e264039040c5801140c01c1c3c03002a0022008902000d0050182c00140d404000020404450000034040030030041034010f0024408a4002c40d02c01562103030080c1c0184c000d00082d40d000301120f0b08149400301d099181c6001500440300c1e0108510702a00079845414854020512000500150000e0b0340d5800001c12000a4458050250542d05004516130402540c426181140602160901440c0050240d5039000011200c8910982449603007a40a81466403140d8140d641c2960351400019100c0d05021f040da143c1000a0400c0e0b030603405503800348a0564506002800788042d4540070010750590060b8001c103900040103220800c0b2245c1c4a8205001640c0070b800000760440d11291924 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 17529799 1250 17528549 17528561
    0x4020d020a02010b03060c040e0109090611070c0501080f0705090d031209030207140a030c12060204030c081c02010614060d0204080607050c060106030506010c0807063c09030509090903070204 84
    0x350250355641d140507658103040c812584d0101f50500034070300d45410203c1c0100c058006000301051240d449591030200603141d40038005000d0b00c076080175102c0800b46010300b06120075005090006e03040102150b6805090300d241e5001d02d5540d11440c0c01c0107510800d211310707503a903110140c04008649103010403440141c4505000b42d07000c2d42c044e05807241424003911074030040c030820901400c61410104040343c40e1500000659250a960544414242c00c00402a002c1c5400c05400d10003280c00c0015860000074040c15011100304806450410700f603416400c80d042c41c841e00140484807030450105e864104020b156101002c032006040c0380c4c03205072041c60700a00710f48080102d03030001042c01540e40d081042ea0300403c5a840d09000030b01d0088002445100707a4440108030800c08a0b41400b0082240c10509149500e102200b10220080422140c0d8400700f5903a10a0740d08031100f40f4920b22000e02541c1881c9400d51201403400c1c0042d0241700300460b0040c015850303404180100001640c45c0e01402c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 17531049 1250 17529799 17529817
    0x503030702100e0307030b19060f08030304030c08070215030f0906160f02010e01060909050708010b010507061a03060403030b0406060804020607021002070b040308090109080a031e03022107090806010e041104020d02 94
    0xc00541400c060100c0201d90068116220102c2b0b55502001507010000c00c999000d81e042c604040950340c2403510039424007480900a5109420040c5400074014480166100d083c0c03950100380c880c0c0b10382d0700007a1030792004d80700c03241e02c40b26080055103d180101c1440300c160380c15200001d07003070840e22805401c40e88150007042c211900c0e20982d8080c410100718440160201d10002c1003150300c1800083c00c10701c56604001c05403510b60a8107906403500100540c080b8030050103848251405250081c02440e170788900e03e00c17903803400c00c0100d101480344600e036205643c007400403403820440b6000c00c624a02e4945074082144148a004107110000e400034200942c07044800036200c86017140003501050b01900114801d50001c1e08a202183e03000d840310310070320303108283d01003047e03d200780460181c070a18624890380000b80c2c5000ae410000480614802c03034440d41d5504400d030301c4500c0a516036070280300303c40d41c00c1c041c1c07408540030840041190740b42c080d00038001443d10200f1025541a41c200c0e500fa = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 17532299 1250 17531049 17531071
    0x307021309170a0f0e01090506071a1303020c060304062304031e0c1506080a0803100605070503030c030a06170307030305010501030b0310020c0c040e0d090503030702100e0307030b 79
    0x2210070859904001c101c0c0c0315004242d1070034861142c0004050b81c0d910800b0030104844c4030300c4214564010744a10000c1c1034050b100642c0d8800c1070605d0700341d0701d40b1814082c001c51a80d000013030302e0291080e0045003040d490b50150007407860784800c002060300040e10503076440d540e590025000000303070518a05070f09442c01040242d0b2a007410042e003500284502d5007207501c81c4500b81400145d0000044072801d82c0710303801d81d61b5881700c00440790003070040c2d40080034988102100d000c20f00c115440914400c11281d951100280d880d280308a03494012650014942da0083c0b0100720700f406d102c00a1503010914581c0061301d555038841400d5a15009202907500c2c1d00009103030000d240d49406018050300e005e0806104426441c00480c2d650080c000791031050030340c04140041c10400a010341380c41aa002441405203140c0c0d0b80c4004e468001c0044028040741e403540c3e0006041c100030042d41c03001e0340c0013003000f400c280400d4010783d940d18800340180d6042c010b0b1413000c0001044004014020410301d41c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 17533549 1250 17532299 17532311
    0xf1b030f03030b011d0907020a060c0c060b0d0b060d060b1e090702011407050a090e010801020a0809010b090c0c030712050301080f03040b0f0a0908030403050303040c060e0a061103070213 82
    0x501904a590f211110342c1002480c08043d50880c0515808a283c0b440075904804959190307402241004d00c50200140340c1030410b01840c81050340841c078030030107030300500c800c201451060f001c00901581d0603400034248824000010b8591900703142000700b103070040c42c0c045502c41410b80090030745010101c00360008224001600e810382004078600740e000d05503000802c00c03084110318007110014001c2200c0304000dc00120076070081d22035a5414024051503038039041c1c03540c4901c019030213034002a08800000d00c460000580d0700d0414018411b2940c0003500c0d00b0035a0304c1e0802d40e498a64081002007229100400440d00041c50404d00391020071f0155940503140c1d410320a1103802c000380c03010399018940c02401b050ac41a24003a0840790f2a01c006030301c585e80c505c00894143d4101d007040d844940580000301d0700000380603001c80250301c1588216201c1c1192925100103413106400048040d4010804040a01510380600d0941c8012034040080b242003220075030020714451900c415000d01107031540c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 17534799 1250 17533549 17533553
    0x10b07060501050f0a03020f01050c010516030507020d090603090309121a090a02061210080a050f0d03020a1706030c120a050c0603040803040f0305040b040611060105010302040b070f1b030f 83
    0x101c640c5000d0102120245044a084400540f00000a0002900c545a12031380400181e0140d8220361030b1030700c214000d01c00d51401014420640d0700340d1003194046803c0a000940003480072803020505c12860f240d0007078903401c0c600100c00034034220701c0032014002c1d001000b0030700e281240545a6814420b801d8058502e0f42c98160040b04100501410810790101041000503030300e960a0b10a65240103c007800c9075135442060004158140d40110b08902803803a10078184040800c07000401c1c1080011543c2d0500c1c42c00c4114101d2141c551108001010010a40001c0042c21079850704000010220b81c00800b06000041d0070055420803003000d170b442682c110041010a003c0030780000070448150b070862810f912052864070000b80000c0000d24031954440800d8010ba0a039000752940c1015551030390786905025203122058081c41045114010002a642d8824022201980d0689612030b0822030076955400a0000c400700881f04043e6103524807920308040d0365110003c5016000e640b052400038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 17536049 1250 17534799 17534801
    0x6150f03090d0806010203070b060307090603080d0c09060c02011107170c090a14220f03050d14190209040f090803010510050c070515090306012402240402060c0303010b0706 76
    0x58042d5403c0c40104810012a84e8003c801e5a02c40f41d0000321102d0940e540400007400d041c1c0640044540c10f1910502000303111007070024000c2c031a1540010002c44400c0300c029103075200c0522030800040c80038103028006500c110408048030140d07604480c8005d4885103110301a41300b030403d00045900c0340d00103003001d2400003003e90308560650010072900e00031400d0840850301c001d02d508200400018000030b070540800503856401c1d04440103103009113f518004085e68403d00da00341c681403e01043d000f0b564521501c1030302a00320640194100701d0f4000000003e504140105644140c0e21400c6843c80c0440d400b900600b1403040c0b031080d40c2c0f581401c041007580070740020b408080280601075000808000030303a20056a80c2202c8006954081c81e154502c2c030300c2906a09074060240d82c00000702c546d40302149040c104940c0e1b00c0c01b81c0d0400207200480e41c500040811300340c2c1c18240e541000c04105c080c6181c42e04140080c04040c075048084000c0c80c907641c0203030310940e01c01000062400c140115 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 17537299 1250 17536049 17536063
    0x604060f200d1514010f02030408071e060e1f020f0313030302060f011203180302040e0a03030c020d0203030402150702030604081905040303050909220303050114030102070b010b0306150f0309 84
    0x10002034a0031803803c00007480c02c000541320066040c0583c107540c0e014024020410384d8020b100b81c1d0100d815450b22140c100b655504406964000c262907001c022a0381ca00071140c050710100098036070702d1b8807600c0361065400c1034802c0f1081000d500441381001e00c03080c1d00380020060080c1c0003010010031499031900900e007010080500001d609080010300c00c8400e040c4001c0015034251a10201c1c1d40c002840c41010044603600007588240741c16042840d000d800704070462100c0c0640c81c100038011990390183c0c4c64015140c10034005800c00c200103801440c080040c0811081040340d2907080080a601007032401c0c20548065030a4040410f0322620481e1014010001e40c54501e4a642404d2456501800714010805407500c260750280004150341030051070004075a0304524003030000007082c01c000e0014030080c01181025610443c204c4c45c030781414000c450070075a000c02148526864a640f0301041d8002400c1140e000c43c88521450740c01d0410f402600d01460140d880941d00c0c00d10000312458144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 17538549 1250 17537299 17537321
    0x209010501030507080714040906080d140a090b0c0a08030f0a05060d0b010611010b130b0103050606030609010b070501020c0102040303030b03060a060f061107030c0f0e1302030604060f200d 83
    0x2042c43d040081c12a07010085581107a264107185150841084030500c090007a03402480e1000d00d090340020300e0000000d1802d4408000d9100c00103003170100d80341050b0301d10980c0083e50101d0341014003000121f030501d001345843c01c0c00c00151071641603d075603a100541e1050f101c128205112200f03101203803955206a90b003241003142c014104107615907980b64200c1051244106201901c050000342038001e4001e02e40b00100241510b40c0030200080282c010211121f4807400070380b0b04000500c103814131004a0b40204070051543d9050ba107000c0c4d55803100da002d0501111555000d02400c000d40e6424006000618400e40f00804c07401e000905241c50100020b09407007216050031000c10080e80d0b0150f0800079600a85071184d15034103c0e215081c42c0444544c80101034940800c1c0006125a9042651096402001c0c1103682502d81c40811030303500d00038000281d07068200c000032400003501948002d5000c03002d9540131400c80d075204402000c540b10401595501c03003000505513810a260300c9003046401e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 17539799 1250 17538549 17538551
    0x20301090b13020a0c120215360c0613090501030507030204050f1e06031905010506030f071a090103060902160201030507030c09030f020111030d0209030c0f0906130e0a0f020901050103 81
    0x4803811344000e000c21080072014000300c401c4801400c14520a00c0144950300e89407005a0840c100002030209038007440c0d80e0f001040c0301c1754000e130011100004460106541820091400030012401c110075a44050701d10300181001c00c0c00055900e8503809403a000394040d0000d00388461545c0103000540d1801001050750500300d20800a098014619410640000380c00a0a0a0350f0b1000030a00e000094108002d40c0520020382104000341500542d2068000ba001d442502065682c1c0c1507803103003540190030b1440e0181e142c41c403c414060000c2d00f0407040500d80880c03940da44400c2c04040341d001650501040c24080d00d40401e42d601800b0700e0f600314016241c104a04d10303c03803000401c000302e03501004008510310383c0440d017960b1150546c014958582c1090b40e50351212142e4080007580502d101c0380c020700031318031080c480d40740850581044002c0a41040d40c5551403000300214242580c5690340781e00da407a05e454420040030000303003990612591042050301407900401100d0041640322324105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 17541049 1250 17539799 17539807
    0x4050606030606070b04050124030203070509060d030e01021903050d05010605130b030408070204180b010801020703140306010908010e1f02071e0c050405040804150206060906010c0606030204020301090b1302 91
    0xf43c40d03120440d05016001001c005482c1c640345072140c094501600d848002d8242d0038503014000e41000183d5085910803000c8501070355840c0188030100004075101039100d804081542d0119014940d0300c1800241481a00c8454181202081800c0300304242900044d80202d500d8001c143d040c40f68901500103030130980e0a1241a007038600c1000c1032400740c0314945138080007203000c00c5100381c00d5885544e0300a00c2401300046103203444524052400b000d40313401034440000141d08406108403000d5a8151b44c4145610700c42c54400c1c6110340c00905418104080e4500004042c2c6080c41600c0901070484081c09003a61003110750000441c0e05000c01414074410440000001c03d4a031207080d60340307040301550203e01041d0030030003100003880e403003075070440d00b824108010401980000c00c107035400c541c2002115084520101d0355404221540c54101000002040d0958050079802d080244110340115040c1d4813540810280d82080e40008400d584854050742c0e03078a003000b020341d00d810300540c0450034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 17542299 1250 17541049 17541061
    0xf070e030d09180912050705070b070803041e03020d0806010e03060a0b01030c0201150504090f0501060906150e010c020f04060305010e010c020106081203010504050402040b04230105010215040b1807090b0405060603 94
    0x42244141110406d210b000075849040000610001c5c004142e038040482d240d00ba182040c044590084a08a40f14144145084160004c510301180321070b8055000300040c0c074850505541e44c14000e800d1505208802202400a81e410480340380704828030f680210b9030000400000d42543d41248141083d03904010325a02550100000d070004c440003110701140d00301d4541010310084000e01405440c0c2d5003010300c003003070000f426006803044a032000c01c0b0800141961030100c40400d00308260600041d0b46256100c05460315403450303000100d009100081c003590300d903107040c04c403405450034805507511906104030b044d80a2250388020480d00c1c002c0c02c0080701a504503005480140980c6100d035990f44089401d640b074680c0000c101d05e0019004220b207401013001c4c107403043d0500e0407040c0c0f5103502c83d0000c41c0d41e52002c14900c007494100c5170b8051403610356554082e90200002e02c9040600d130b20014010741c81d10100090b10040a660320000350300c205440034042503410040403c3d010380405c2080c044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 17543549 1250 17542299 17542313
    0xc0201020307110402210609070302040e0a0506011103040806010e011203140a030b10030f0f0e120c03071209080105010b040b0a1d060409020903010f0b03060f070e030d091809 77
    0x7441d40300310788120251003d80001e0003800340d18200d51845043c1002140303404251241e1601410040741c45c00c0c2d65555a000460503842540580c00051614201040b4400350b96000b46820250504001a040c54110706280c9550807907401140140d03c0103004000030150701455501410b00300505ca00b003d00c554502405114802050702441000080c2c9982420311a030310803682d2100003458013800e080607040080260002c40e680803205d038545826030721010340d00e2248002030300c02c55001d0031144500d8501405250000851141540802c00945002400c0f01109112103110742d180c0c121128100f010107800c441058004007400c402c2080305000c0a00940240c8100c04464a0545a466200751709807412108060300c0c290441c10100d404281d410154020709603d02c41903000300b20000c046110641540d50b5130341c4203505a00030034040b81c1040440c454040d4041040c0c208040c4840c664800309151a000041c44030014102c0b903014000c4a5208d41400c0c4000c5420605001c0c2c0c0a907512220 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 17544799 1250 17543549 17543557
    0xa0b01020a0f081603030f0507030e0d050706090206040303030608060c030402030a12050d0c020c01030c08040f020d020312030901051806071215050a03050304050109060203120109090201110604030e040c0c02010203 94
    0x75003088001ea000004000d070f010101d940456641c071201e109003859181c06006424001100c5807801d0900d400140041c1c42881004a2910120300401a002a03040d00380c80c1c036442240103a81d12500c90300442d01580341d8200a2004500c241e0740003440901c0c103405541401c4025001011000c010814080907a03400038000d014285c120781d2030f00400507400019a51403088001c0c00201d2403d002c0018540c0b0380100729005550802e0720700303018250b103100c012555207100300d0b4001c2210324100d44003405410188030089266101500701d808428080d1034084450304201c442143c541c6d15003041000005010014000365480940104070b10300f410040506041009002c00c1c0e00c507030340c5044d103031500344c1042141c0f80180070190400b035000e0303200c3c01c1443e1684d029018003408034200c0100094001d02c00401c903a982d203200314a100550342030003486d401401303920000ba410081c1035080780104007424804207014501c07a440c1c042c01c4504180030304c0195007101b803608044c400640890005070340c02004403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 17546049 1250 17544799 17544803
    0x120201060f0e060402160212010e07150503010b0a020114150a0e0103020d0311100608071d010b030103030e0301021207050304060e010605060901030e0f0d1809060b0405040504020310051e0a0b01020a 87
    0x15840d00b81b081e030f1501e80581141000703503000100c0c84d10580268410341c001408880781d00113641512b40c072209120300701342c841010365000940c00c00042101d260000060034500350315100100b54a001c11100d01444601030f100e10511312045010b9003041d00d00000070000808085802c85910b625540000e1200d1481e0030b000b50600c90311104160701080d092100144c0034240c07480801c4581d8481625964510b10b0380a02c04241c1e806003603001d0080a80b0392190f040311038184100703145070f0842e0341c12682504600030898040d9000d0214034824101c81c02c055214010959906407170303250600742a81030742e1b0311082012a90740b51180510141d00c0d01801c5a0103010700703080c0841c101c84e00543d541d10b0310741003440010690250340b5040c20b11980c0508801d00310144240f10325034258903840280100c0754148103d14840f40e08200c20004c0307041540250360300a0009083e03400020440109038141d13007040f903070144014000740721480d81012010003541c11003808242044600071082c0041d56440401c1c40c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 17547299 1250 17546049 17546051
    0xc08030408090d020a061706040e0c01110102120c07050c01030608060106052203030201020c06090c01050403022b1104140c03012601020705060711030a080c0d06030609120201060f0e0604 82
    0x881c0310342d4443d008000b81c441d9000c0c09501180f50303524401880320b401208101001060b10020411501c2c06010b030701d82001018020348000c09096006592100ea00b088810065400340036826000e092280d8403407080f14a007540d641d6500503031414600f840500300495060600d400410700c03010b0f03000903050b4155801424000d0f503810044441414010141180143c03d401c44d01010041507410b40181071200500d104588130380d120030034040d80702d0420310170090004030180410805480c09501c4c14143c81520a031a14030b45861044020b5131121404040d103101e000c0d0401c86a45040c03038812195001c202e441411141d00713000e41c11680620041c46031200c0802d07220700702c400e10001100f200008014000007199138101d00c0c40d00761384a010841c1e1420106485403041c111400001c811254803d50654403601241d84281c1035014030f030014804180c01075941c00340440013078500c2c45040009801514840c00803030040c40300a007581c080740c101b00ca1200c2d0720981088900340140c451908003070200c41c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 17548549 1250 17547299 17547307
    0x50705010e060705060901020403140712080a0509090906010305060a020901020c0f010509090708010e0606030106020d030c0e12010207060b06130605090d0f060c0206160509010804050a0606081c0c08030408 90
    0x1500b5014210002d80359028250074031a12000550003841140d22440d1040d91001141e001281c8a188610505c50318186014405001030041002043c280c0010b061040c140032a41d008241c1083c4101c44590030b87c1e2140d001481800420010a6400400e0f20019032a04801900013900c610006506500440703813820101500d80c010000e07190984001f030041840c43c503042500420166003840b441500b615048040780d80c80c01c010007200d0698590760020440c5910f803007030880050040100b9041004400d01c1d59048564a4000400081e41d1450000d0b80b07a1180782820400c032110056a035105840400c00304490086070b250840071a60035081c401d8403002d02c0c40125a0b0303403400c424002d01c9142c07050340040400c0a6a4014005480590f00b01c07205c0359036215801c42d40d03e200d0180800400c400340450240c80d88581d0707041c0d500c54420701c203882042e4a643d9443d4103450032600100c0c2d540e080508404568060f1040284240410b8a058400700001c0d031910006448081e00c05071903040000b0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 17549799 1250 17548549 17548577
    0x30105011416120203190f0e130b04020309030702040605030703120f0314040c0e070305010b09060705010b1306030314040b030103060b0111071502011a06030f071403040c05010f030905070501 84
    0x40450b484042d00011614104144144001d440e940702e0291206000750040d445009030b441451541800300703158452000d401c203084c081100c1241013540d480794240d00e0f85c45044450300e9600107940034004820045895a0b05481000180e800c1c0380c2045002e980420010004035900c0010702c003181d00c4500b0031a03130081e1000c408074003a160444103450000300c01d0341032004008820b000c2c075045070920190350707032241c41d1050220f0540b0003e1080f20848030041c0041d0401d4540704c8010b002076442a8000a0300c0e0788560f005c110864141c8a00000c45903684800300300b4075804c49004e041c541045641e0601d01401c11215000350300040c0000390656503070b8202d80404d6400382c40c0c446420380046c0212440c440d43e50041001c9542080d42a400550071300c1345081480141e030403107084d603180040020342503617078421803441e0224009014408001c0c000c0d03401c01c1c80754440c2004500490183c801101000d06050024103178100f03580002c0101481e101c3c043c00803481c042a44800e41d5005d01e804190761100c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 17551049 1250 17549799 17549827
    0xa11060c0703050109030903030323010312052a010b060a0507080d060b03040b0103110102010b011403060103021201030b01051e0102060a0504080c030d050a0b06040501090b030a02120702030d0509030301050114 92
    0x142c20007825136107092050420b05d504607442c1c20440b071007a601130028001400380d80c10704c03c50642150640c1c483c4140103100048980a0070700b001403140c07920764100340760000b502d01035212003c040e87c0110342c40c1510b001c407441c081c002c0c2e030740c010410f4488e54905440c2410040981c0f14052000d05600d0b004901113031320009980059005241c0001a0340c6c890409040503007800b6000c3c44100c50140c0e0b01d0706401015401070184110903070050315908080f205101041405520040c045410140c2c200525100041ca42c05880c1c043c6014000e03c0751190304040170301003000b403000c6c1e000c5144880c000d100176407aa400224180c1c01a110500820b241e02c561801d80c030030b8052002854210300004c40c2c2e0380304030242c6a1240d4070829500b001800181c1c1200180000c3d4411030196031300085049000b84070701c004000003140c00c041c08440040c42c00800f104031500381d501c281e40e454016040002d41d425100b61074014590403104180c06180365501d070100203820b0380c50100f0120306221010864002810784 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 17552299 1250 17551049 17551063
    0x303070b0c0f030403020c0f0a0b070318091803030e072303150a090201031406061209190309080d0305090304060c14010203040b06010813030207050f120109050105180a11060c 77
    0x6000c000d859080071701e0081c0d250114554200e01075001d0f10441c2e40d0520344108982c08813484403100320f18005868604480108805070000c481054050000400303800c0d038800d2807a801364080442503480f0b994503005082d62500311800401e580020028440d41203c10b82e1000030301e260050310b40b40c101c91600882d003000144c18a83c0f0100b48848100a0030700e05641101900b81d00c02d9a0030000404613074401080107400399400b03500440c0900440100120b103291a541040c10340003142c00810703461407051403041803900c00310001443d4040c200b1001030b080202449240c1d50341410301140c6441010642d49001f503100d140100102501e900040c0f166021030524224880701c000c1d9900d00d80750401c8005140290390060003e0f542400045940500e4180c080b0340c0f03607065010302071461411040141850040756040d5002d469140c6081015500748a900851445400003203090315204401c09260700840350244d81640010101c000001c2086d03041041a42c0304031000c80c3c07149800f420032454804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 17553549 1250 17552299 17552317
    0x50409060e12040801060801050903070b0403020f0706031401121703130803010305010c0e12060f040309090e0607020c0406030201020c24030f040b0c2a010f06061805030105060303070b0c 82
    0x50a0a0203000040c02c800500c02c1e9516000244a1156507920441c200c3e00c003110010b03120f030024854031001410721001143c00600920450b00c144040190080c1002c10a0744100d01090361034a06802480b4441c504074010901520308101c2c0c3c8070192915040c415081c0b28042c140307280080050902c41d800d10703a080c200354106100e191a980c5a2418500825000c40c841000c109840b405100c64a00280410400c21040c005440b554503120310f0103095850281046090001001011a540003a84120004242648005d0030a400d0183c0c0290070641c11000490140d403e003207045c800350340c0004030403c02d440c05544e5580100320710070382ca6000203c201c02c1c01000400000a00c182003645014050040340540c0441c81035481e90303100d8502610404042041d084604101d00d6551441f4a40004a480b0644004034030175041c510388000303c3d40150802c03c0424484581c082059400c6502d08002c3c00f0103800030003d80c2000c0000036035070b000f00440248201607460001d80b100c0a81429130305041d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 17554799 1250 17553549 17553553
    0x907300f0b0301061202130c0201110c0c0907020d0f0e0a050d08040305010c0302030f010501030504050c0415061412160201020c100c12140612070f080a0210080105030304050409060e 80
    0xc0004200d00034250702118030344258204600410020000030000442c640d0040c0740d000c0031041e03102c0c000d0140100c1a003c8055550340c08100040b21084c400500346588c00707078090b01c0300c04124010010040405844007086500030f03c004880203070001a001d0003842542080b00403880306400041c8109425044540c000c5000807400042003e6030000e030040d01d205070028809026a050200c080b4001200c58080008403c0010412075019601498010f030040b0b064405e0450a1000b04066030283c8260142640c0301c00410040345612074802c09880c10722180381450040080100d07880e10402a00ca01d43c2d0703625103210039000e5030007541104c1e0072a03c000f081d601c204440d888840000c0915808580114000070341c41c40c0082024410a00608040080c2c140551036000071b00c15084a050b194840c139100e060008110038528200031401480340900034010755440b0700c14001c0310000e48440c2070901c00114014446641e011040d64192001500d0004510010b81042c402a200c866a51980383c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 17556049 1250 17554799 17554811
    0x50604060206040b070c08090d050102091906020106050909060a0b0a030f050c0f060a021506040207081306030b06070506041b0b0d0e0d0c03090509060307050310050406050105090730 80
    0x3081d00420782c0ca100300d01843d01c02d0895138680d0070a48910410301d030001d02c0c201041052502c42c0c0f070024400c903400c0d8042c500041c1401c2034a0081848140d00354081040515500c000300b001560901809000d40000d41340440142004401c89545080103050f071044142c54080d212a280ca401003e000150340090f25a03803006110708149844081c00c50300da501510b21049200c8440c240b83d01202c110804543c0240a400c0c160528188610005404140e016030204610004130b4680e4000c0c24142035500c4005a129103088800340c1194603200c05180509002d00c00000851400308a09921540000304c502c41c40c10390080360f03024000c041d00300e4002c4c240041805103a5040942c005501000c1070011510100310030030302510806010310004000403248001882241010b4011a4000740041d08440c2002e4a500009013002c0c1c000802c40c0680f5a80c20400c4140600c5028041c0100b000380c5280a00341016000180410600124103030604444200502281285c0400214660b22101300b0806 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 17557299 1250 17556049 17556059
    0x9210503030a0f0617031e040812090315010803041202011e080f06010809280b040b07170c121305010c09090509010e1f020702030304090f0f0e03030a090507050604 72
    0x282800140846a5413400340c3c0482c41c1608001021840c401000080d800c088044180101c151305102040904100511002130242c0c030411540304600200c12015031189464810706107032980e040d0419040700301940041081d0700c0c01104880c1a83c2c4440c810801c10340300350005030f42090408401e041d504100c03c24402ca034070b0303021140754050307403007603030316104940b205030044541c014295405112030f0407140380c04101c0c007c004035540b8041c94010301e0001c191090380743d103074800804841c1a01c00168140801011544c810485405094903151030b18560600e551710043d10b004111103804d2009040300414400d820501c1e070480110703400300003030010328403a89000300544818410b03811240d080c0700c04111400d40c11301645480d544a1001400556100c0200e401d40e0140c00b0301d281c02042d4204011009030f2003c0c0000c201808054a02040c0a0428000e500c104c4220f8140d07120b26170300c4d00c801c0312031200c0301008072030f0414082c00b00403030301c4003050400500741025540455400b8a002500043c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 17558549 1250 17557299 17557301
    0xb0901180507020c01020c01030b120307030203041a070804030303020a030e010f0f0b030318010c0c031208040218060d0305031506070b0601020f12030f0c04090507031b0309020109210503030a 84
    0x300a21004081c40991540b00090342c4d140c1c102040c00c1d0141c1c105c1080d425072544268814070f41000014800c0c0c00d012581d4600302d080d6400b014064005030000981484102940e801c14001034034200c500e0341c5085400c1e11035000c1c1d40228000107007010703000180401e180784681c0061000340d64a80003000b404600003c4c4000815550204203001030506417120164038021080c0d50220700e42c1c8400d09001080d40004455804104070122461010b400011001c60410182459a02920f0321104c0140c2002e004100340c0000142a400c4540c92800821242c0d0310b0f10601901c00c1585414582d031651584401c89501007080d07503030690010f0001c5100350078080e43c40d40d202d000710340a8090b10078205124501d2078880d42400d04d4201c030760700c0c00c102245904c9007015003e60300c488080b0445080907218500c0d1001c3d500161004030001f512124003200c03c0301c45d01c0c100030403920b0b181002c11003a503c690002c1d1200c0b5041c49118480e0402003204040b08004e41119044141c0c08000e481d52032602030320241c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 17559799 1250 17558549 17558579
    0x20301150609050f06070f030c08120103050c0d0305090d030203250c082a01020a06110904050108060702070315090507030c030b0603030f0d02090f090c0406020f0a1e03030b0901 78
    0x81c0002e448520008042c1446881c0200104018002919001d155204e030f4068001d05c80044007000b075980c004030045a102e40207800b02080040441016501d1420594900704410b2249886183c07007066090000c2d401604907289800b090310700c09403425042c24160705500944034110300d0000c1800c1a4540311031101c2d06c00858a1082c51806204c603155083d407662449003003a21034112403840c1102d41c00e841c1401280c40b400d101441120952121559054140d0381040c1c140c40c0003e0b4045401203c500c2c2030700420340540510001001e25140c5210025501d4429100c00303400405d9081d0151150009500512240c503041400c1f45d180d00e64030b24112182c8450b92100762004903102011542c03510b0044210340d60b103000d4449441c00c00540c04900d000a40c8850f003620383c0030003150389a02541e100d404a01d485a01708030100e0781c0710b80c6059000781c101803240020b60419008841e00c400059071103421070520001400044092030f68a180580080030030351711b102ea05c8003100e000054005030700c40d042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 17561049 1250 17559799 17559809
    0x2010209090a1122030c09020403060c0309020f010e0301020f0a080612030315012006090105060a060306080a0b07110102032403010b090a1a060c06090d020d020307030e0a0302030115 80
    0x196860341d07034041c07444122021004240f0045104000c405614144041044001030300c3d80130244503140d4070361b6a00c0854105034040f01c21141c000c281001803050920800906d00054103083c44843c00c0c0344c0c0007a070010348a5000d5814084000052038140d242503064032a01d101c000041079442043e0200070300300110403160244903107109001141c0d600700c08000c1ea8010385144030621071214403c070064030f01440c1d242a40000440c0c2030a0344802ca40100401c900500c80107000255604004044c0400d4090b540c00180a040c01c1c42001c020003a00044ca0300350310754104401500c0303030b121010b0486613680c860300545aa0b40c00441441001c03862110120741c5000006182c090354940030061600b41ca05461095621050103400960180e50b180c01600c8881c01c0e002c1034142e21f18540c400980c03039801c4081025081e074425400c00510820070804490b540000d0300040011140349800207659202e030240c0102000100d01c4243c18544071060848003540c1c0c0100240200404d0075006000c0180c14860 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 17562299 1250 17561049 17561059
    0x40906030c06020318090c0906070f1103070e0f040807050a0302030a030f051303030f0e10091505010e0a090f0c0303120506040507020a060504020d0b0c030a050c09010903031b0b0702010209 83
    0x10b0842c000411103901c00c4000450b80c2c46001c01404002c0f0f844802404034032545020020201d207561200014154544100002c06c1104018140403d4904070b104e2003c0c02640080d500380880c0e110800d04a40c03200510400142e0b0382e85078070f040b44a82c00340810040951040009150030913802202a00001e03000703a80c108080048188004141c0340c060303428847c1d90815201e1640480d100e40c1103180041480c03213020542d94000181c851508110b002c454400c0766139000d4240c200896494010100d2070310100501c941c0d410000242085c04024103142c200c00da403002c102c81040494000d441c0000e40118502d0300482d0303a814003070701070b0000111001300c03030740760800250b1030346000d220380b50240d016a40148541016640e0301001400c0182040c0e07880b0184581c00e00c0041c9011000314401c45406c000c0303503102d0820a900d1801e5640c0a44900205c1d401804042c5069034482c282d0030499805140400000120b240c08140c1444141000b030023301d000001c101107680c0540051011b43c400ba18 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 17563549 1250 17562299 17562323
    0xe010c020604050c0d0b130c08070b0406120204050918070503030a050c010c0f20010e01090309030209010b040e0c09060717040501170108030712050408030c060a0b01210f0209030304090603 83
    0x4200405c841c07510301300400c1220400f002ca100c003030351030041d0f40310148a010000903403a1600c4541c3d02e04105c03940070358a488c00c00034060080783e511039449200070a041d5230a40c1050b0615001810b031007001030003207041c41c2031000c612040010400001c80203100140a480d0b480013414030083c01a8400400c2c004250300b4040801e0090b40700b1026521030101d85d540b081440c00181c0300001000c624804c10204075902c0b52003610380024203100b160209803080d20385050b040d295205000758013105900280d80214280b20402054010044542c0c2c0400e0a0341401d030744100c0c40340051641d0180c02d1001d0507a6100c402c2540740c010003d40244180d501c01d1701c412220241700c06550a0900090050f10320760740040c80414000b85d541d8030581800d480c2806c0507420a40c4a01580d40b954000654020700b981c08102409400405403141c0d240d400e00030300e020746a1801d410741100c030b00c402280c6200c0c0c005a8a240d245134524013030b0705032090024000d05980d5107503911903c000c043c10383c0e40070a5a12504202d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 17564799 1250 17563549 17563573
    0x906040905070306050a24030506060d061e081204060507020a030f0c0807150212090103180303060608070804050309090405070b0d0e06010602150115090902030f16031104090f0e010c02060405 84
    0x200b60030904840e400347c0110030344010407089026100140049800c6141441412925030a50080001400306503407407210b0041e289240e0b0400c80030550241d1307140c1d00300e02250a2020000000c03501540d1040c240301e9920b16427440481c2c00c0700c81d607500190011003101100010029200103d1089aa0b12003c0700c19950700e45580b140c180e0036030110032015a00c80040f2159840205010305204335050400140241008226081688d010b00048002039904c003000d1000540110304540c200c551407078060368a182079991180d603442181c421611036003003000000e040101c10072a0300302404000e9182610703448008030100150030b120b448100a0700a440022462a10002b0300e48801c04810041003003903480c00020002d1400b101d10b000e820080c41d800007207101500c50004501400c0a03144c00e55080c17801d80d862840b0b9003850801c00c1c00301402d006c40341406c00c1091080e9000c0e039a00c0301000400c10080c800500c002d11034003001919550822038491103280c1c0209e61144218006ea0a41302886a50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 17566049 1250 17564799 17564819
    0x10f0b0103110a080a0603050a080c010e19020103050405010b04020c01090b061c080706020c19030224011401030b0d05010209010909020c0a030305150307080c0f06040305030306060906040905070306050a 89
    0x70300524000c0d10b070034000e40c254144603448460300300072203481c0040d1064882d1103080c2849621402514012800900c107421041e0034400e840c50002c1500252000b4005078410035220b20000402070704040e00d901c042020f118080d402054034500060007159207a031980c07c003034043c0c00300340030a0b2a9644004005191070030000c00203443e200240410414815150350b95440a0304800c4050720700d20f40c02e110109000d81c04000448032000158442c0590050a180c02458440079640d20550700d520a200702c2c2c480e100c0c4200d403506450140d0519040c01540b03000480c000c103a000686a03003c200640090140b05043d0700030500c0c0305084e80c640d00e032036072520140d4099100e044501d442d2903116602c0140030070300c03c0d805a50005038041039404c41c0d00c0130b82d0009241c000f0303a40003040140c000915549040c501120129032480c000e0740c91604051854944644034000109054041e850014503010a81e446000300c1d0f018041c030100c00c1100d410032070380050040040d4000c5c1d901405043e4000318010100e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 17567299 1250 17566049 17566061
    0xe010b0603010504150b130e09030c0d0305090a0b0103060204030b0709032609130c020705030c060304060b0a0b0309030a0f03020702090a0b060c030403050a0204052d0403090b0408010f0b0103 84
    0x1500c0180745900e8074090000034480c1d624038800958255102103010b410b1000284803941900801036540b0b4140b015410301070b030740988000d0441e842081149020300c40428122244040c50134002a81c0c0c0e0781c6041942420b004410040100c21468000710801c03049901a00a89004028400f51551918130a441c880110701000c1c00921045100c41d07001c41c003044039808545041c030585030400a0810119045820b9140c56040040e242d0b600c0c43d45290f0304010b00c80007040d088009080ca1020000407a07460301c00544050300c00f9460b1441072003d91074101d01c040051034038060046d50b9180c8000d4103030b2250001030803800040c444600d01c117003072482402078031441034005213141d0042c1c0302c0e051b505c0300801256a0301d44e00b00c1c0051112070115201400038000850191b0050032220b40f0a03c10802180e000900f40040c0210b40300110740b0000c1c00e84184102d120030080125042d40341c030700b0705a4130b0282d2544403c80f21400000c01040f80701e01034100243c500e49510080c030001c40307088019019200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 17568549 1250 17567299 17567321
    0x30906060102070b0708070618110f06040f0b03100e1303080708010b0d0c090305100905010621030c030309050d1e0915050a0c050f030a090b0702030309040903030f0608070602010e01 80
    0x1350500c030b09404501c030ba80047c89400c3c45048005080d50100500c01c518000c0035209035034201ca04076480015050010000c003a44070211803061034641030400800c000701c5140920f1040c0074011000030320802da00c010040c05040040d410064a00d8800c0c202c0400b02c150705002c800040d540400316000e0350254014905980c0c034903e846040c0105104010003c061454800080220040000000c00c005000b0841c20a1042c00c002c40e42242c2c508007282500c501307901c441c03090005002c0e07003c0d80e00d02500c04000e4440e4585418001011941005c42c050007000e90041c2a0703005903006c842d4016003003071140c0314150800da8600302d00040303013900b980c0c0081148103240c605003041c030891281c1d6100e1402040000d09500341070394102100d86800703241c110107800d610001c0d840060079810300c40d00304a09030010310390b42400d07900d4005a907001c86c1d104c1c09146e84c83e40c0501e803169440c2c0c080601075004080c000601c01010088242c0d200011566404a8440c0c90f002d5440c00c0200c2c0031450060082400c003103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 17569799 1250 17568549 17568569
    0x20a03081914070f06090b04050d0207050607050307030e03031c060302010f050a020703030809100204030803010e01300611030702010605041a0d020f03010207050d03050402030d0305010303021504020303090d050303090606010207 100
    0x100e0ba0b221102c4c2c2c865064401ca6500d0381d0781c1254000100030f440b419005900901c01000800c1c3c43c0701c000307032800c855038008520640050110b4000520000221215540d061802515204001c00880e155000e03041c60040c0c1164409104e40b0480941c3e4002e40480307000360782c0c51442500000d8180e403580706030756084006811980c418804030380140c2d10141c00007580c004542010161384240f9040760420b800490b002030f8000010402c02841141c850f001d41910104a81c8006002d420b40c03400010703040e20390202c14000460403091002c6540603800003560404920303078a20300f401c4000c0c024429401a00d10652500440000f01446040044480d000c05040805c22202c0350f020003c0000c459801030350701d590200450300c0000e2003449450041c2c05951404521420680b04150a0003a1401c10f03004041c502401000420307400100d00056030052552004a6281c13400400d04510800441e5a000b40040c0b6940e010400000002d40c4100c254034280c80d940d49464004a8407a501441214082c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 17571049 1250 17569799 17569807
    0x105040608040b04020a0801020703090305160b120903090a06120501090605030c0f030c06160c0501030c0503010603020d0609181506050a0608090316110405101a0a030603020a03081914 81
    0x502084031081c4c126000a140440080c0da03200081d0a82e84611011000191000c0c000c10411004201c02604c80441d1030001050504102c01d04035030340a07110f4907068910600001c81c03039540d01441140c400b030074050885030005441d40c00c043c040120720180100468039000000900000030b20998058a0005001e00380006a180801074916800d14a00da4503000f1249a0900c9507901c40080824078040d02030308207104811b0420301c01e03a80e507036400903060505204c04120125481000c881c1035031b07218100140c1324104034015074010916074104401c0945003e04d0741c05001d204040c070a4015116140d00741410001c1c088607002e03a0401c2c4100c076004296000140000707405070040c1644442a0000c03641004004185540d40c331044c4201030320700040183c502181ca06160041507401012400e40700b01042c5000c43d4801c640222030800983c50001003044900e841c802e800180007035400810f1000710b2a202d051840c05c40d030018071146000c0d04051085091180542c103282405420041039500b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 17572299 1250 17571049 17571053
    0x810050103050d110316050105040203060906070503040609110a090f0605030a02090a02160807080910110604080c0a080309070f0509010f03020d06090501020a12050717160e0a060210050105010504060804 89
    0x2107845101201245c00309020054407a0b01d0540c030800103900610001c0b45600303043c0145804c1010181c4900321076004030082000c51504242160781181c2d0103007000884140d2070070118290400503441c00e0788a1000240010480e881c2c0c1c105203098401158104459a5070300d00f0182d9580040d440250825640d80002c0c1841482e64003400700300b103400c2c0505001150590711131506a01c846821503108502041d04942c1d418174811205501d181d40c10068050a80c0c1400075941d150010402420081e00180070000c001051000b88000d940c00b610f09510381c00c0000000b6112040307401a40c406000c0310300d00003968a042c2c42da0b40e0480d901c1015612203030341560284a00c00c00b058105941141c1c55000030400100309200a02e81c10107185e403148000c111040412058600141c000410030803001c0f60385001403068055103401c5020190101d10940f070030b8100350f824030700720090075500810f00400000c56680218581d02040400b45040001d40c0c0ca420040d9000e000740d020b8480011160030001340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 17573549 1250 17572299 17572307
    0x10b0705073302030703020c010e03030d0b1c030e09090604030f030908190503040209060306010b04121a070801030506010e010e06041806050a0f05010e0408030c070c1a040810050103050d 82
    0x2820b05144264191101580034940d140c40001c518401c0107a100060701c0040c15410711036019030100900e080282e403480440042d030380703009095004260b140d64025000d603d41c0d4410410074601141d513098030b02201107040c041c246000702d2203418020540b100c001a034242002c9400d134412a4562103071103441c14003600c11001414090307000c03180301074108007244d0100c0c01038600e40d008144d6580c07140d84c1c0b07143c2881802092107000c0c0520707001e076001d40014420410300109a03819115a03444803850b6991600340034114036010b010380680c16201005110b0030541c0a501981030701d00600c112031071740c0d80e61b0405440c1c00100344110160a240350300420040e1409400c80e1340e00012070205000d000100342c5965040311800e6804407072055039809810302c50b1805010b440c0c010003014014007403918150b240da10052000904811000c00300149140c10440008142d0004e00903207801c5a07807640000b00c41c1c0d5500e500c14040c91400c0d11a06107480b080000740d01609043c2c1e50322070042d0450900901c0259 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 17574799 1250 17573549 17573579
    0x20a060c0c0801060b0913090c1401140301080105160206060906150c070803090a060302120703050c281b050c010518041b030c090320010302040e040b01060206010b070507 75
    0x72840521840c001403101400d014072400b5028103034400ea941c99100b0100f0940f000c212280444150070701c0c0c403400225680f200928200d0f1121403071300c10b50807114001246d0040c141502c49000c0d040100c008500b800d0705611040c803516515046607a010075001003641c0d105400c40702154415540e100003001e508101c40d000d040e04503c043c01501305140e4402a40c02c044c51351304521080d43c0042600446890300034020340042003075060071490030411000c40c4004240080120b030625841e00b0104140d00038030b10840d100d07000c03040c00c0703600344c04413641000301244e035100d850800088881c014010254601d802001503d9440402480c200c18403000655003a080340a80442030041c40484054a489a000f916014482c442d036000807161401405002ca80d80f03520005c0130010101d1050000510401c0c0a41199000720f40030502124094012400b038441ea070400500b4508000a00c41003020440c041816540c0300c0d02607800030383c0c0f16400c01c1c60314080c0c0d8801030440d600010040105200c1c0320750711 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 17576049 1250 17574799 17574803
    0x3030207080702040212070e01210507020a02030f0124120204051005040905030405040501170604170d061410020f0c04020304020301090c180b0901060914010c1506090509010207020a060c 82
    0x740d0308000301900040c04036001314240b0340d2001124400c11504607849039501410441c01d0a043c1d28440d50120b140c002030095250980415071390300040f0b0407060007000344070800359004080f2521030750320042003400f8007010742841510801848049003010b11190601041d5910b1210f03510000c00c075902080f02801d006040085441510803000c6501d85540c000c00d013295005100955607249000309000031600140d12202400d42d42e0300740f0a42c8041c010540607013080c8c1190224602031210042080d05d4425160550f0b0018500100041c0031007081c074408840310021294808628908003060344c4580e10b4110504154000315101ca0300c601d40780d8061038120340080c00001c0d00203150781c1c03100c1c004a1a500f142241480a00025162800c94040d11b040c164090342c0c0804035514020000d08210142e009400074414803101205280e440b4941440e55507402511600500d80750a0851004120710b01420300010305050002da140081402203d452990162450786007510741907046a20700084441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 17577299 1250 17576049 17576063
    0x60f0806010c030309050105090c0f03010605030706050f120106030606030b0306060319060905060126010c020309010302030406180804050310020f0405090403050409090309051206101a0f0408010f050f04080703030207 95
    0xa006c40c00920850f80700c0d8070404018082c0310400f604116107403901c0341d6881c0c426030400d80d040c8280d48001c650700e0121421030512640340e440030403420900780035080401c1108e01c7c210b800043c00701c2e8035801c880200c4075181c8041090030304a030149520b900c0d0841c0c48941641c0441119107a10384508090a1214011140000d002405680c0d0a0030f1401c20f1f48003640891440b08265081e0250091442030340310414001c111301044004d010b501c80c01111001030515034080000380605c8440d4120001107004200c0c003100c038450514045203940c00030f006860107846401d49108595003035200715540858420071190070a0303c1e2100704528104018000c03020081c06110004985503140980785049110361595500750341000248070a09078481c03941e0985501c039805001c075a41101407450f05560381c0601e1103038000589000d5201500c10b031700d640205820b0004001600420660180c60128910340c0c0601280d00d030281c14514840e420740d00a45020000c0040000190081d401040c02c140310b401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 17578549 1250 17577299 17577311
    0x150f0109090203040c05040501080a0f030c060f1b08011d04020d1a0a0b030c0105090108270d020610050a03080d0506040b060c0a0c0501030203100501030911030303160207060f0806010c0303 83
    0xc440070590304141d804076040d1510001c2440945410f0040a0240a44100a103507041050700c40c1c2e1121800d0420140030710041d03030001c009000700c582209102691158040c4800241d401942c0c0074107841c0c0301c0100020301c018002054051603505540188441d086000025403296020000ca4603030185c03044034441542e03104544018141d0b030701544908858000059010884010315007000702140031281084801c02c00e807629680c02107802908881349440700d143d080e128040041c450072103903808044610032007030b12484045d4000784080c0716407468400041c505907505c00780100351195020080921800303000c48007466030594082d0380d102c031000f4000b040c404100c0010440a9104040d8410142c010b42001d405000d079030640322000340004e10b0210701d540b920400410b034250890040b14105a1907041d040180030b80303080b41202596005054070307500e042401100f105001c2042068000d030003045000100603003c2c90340300004440780d8036100c0301075031242c004640f00703000c100c411024165105 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 17579799 1250 17578549 17578559
    0x706140c0111180405070903031206080f0a0302010605040608121c0507090905090706050d1a040c020114010807050a0e0601021c0509030c090105060a050903030c06040b0609010905150f0109 83
    0x4000e01c0c04041502d0301180c2c1d0343da50032100004070115210620f00650030700d0140f00203281e01c91142400c0b2038141c5040540d030400081c4100181003d948084424462900e0740c1341103800110303081ca800c510030340080105039030b5002440142c668078400e098080d00114040c000b64050400241184140703400710080321041c0706100001c482c2c1c2520301000094050006210925031840f5640e004043c140081c40103a01c0c00800402c10711a1002081400740c84040007900501103840d04111340000400c00d200318ac100e0b80009000b03010b034049540c107145a80300000782c00c1d10085200310030346a0191075504003e040110300128420060684d5045105911b01c14906514fc104080d8000107a40c0d5090baa40e1080402c08d440c2c102d00c408014802e540390b0004000d55540c10003100c1d5140d440742440c0362280c0807103000900f14040c0e100108040d0254604000402c8811a4802c1c8601012144404103980700e24103002203500882d05142400c3c010381c4001c05914000480103003e14052420050150b110b0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 17581049 1250 17579799 17579801
    0x2040e150106080106110f0706030c030608030f07060506150706021806031f0801020a17131a090d03020702060a03110d150e07020a0c0b090a050405010e0406110405030706140c01 78
    0x2d92108000910040050080640c0401c0b005030022644005114182101da802911800e0510540040c15901c150321010180a500240002e001600030740e070710389206048d003070300f558003800e01222264a0680051707010f00c0e01040316050440440c800c41c2c20402d55603180390080d4000090450b039000d03016142305180d07403400d006610890350fa040945103010480004001d0300d006811404940e40140005582c1660080d203a0403a908651086e034019126603203140c3c200e040e460400b5100391140c41003092074008400920f07008444c0901221044525844105c1c01c0b80580b400013917002d0800c010000f078080c0f180c2c2210740204802803081d480d2940f0600040104c8001e043e008d8246139084034108050141c003140ea6510007198000b40208062640d0b03648044a0f49006480d2a031502144014071625502500c002414025000b0007995860740032a01032580129000c50707260f1308141c0800d0080ea4240161821190081c0c000c0140c24240502680d00c500360040705a101d00041c400e40d0203010003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 17582299 1250 17581049 17581051
    0x1602090406021c1e1109030703080406080903120c0307030b09090a0606050a03020a0b0f04030c0b04051003060b031b090d11010801061103090904050102070501050f070306090b06040302040e15 84
    0x890040181d82c0c41c004015090010100e0143c1c0754254a03050440c544441881101e400d40340401c4000107807680703511218100f6000d8220000c0e010301c24000003008100d100401007041c1e40c40341e01c8003011036035030a1002e9501e105504d0088640d102a5000c0b800c0800c440c0c1c09140c0048103802d01003141d9112202040614804030b8a140701640004c03900018404e0340d00c20b039005800d060320146045c0b8150b0300070481c14101c03480350710354903100050440340c0052800c2c291000780d03601401c0c040c41140d54030705039030042d04180100c0c0d00c20181c00c00080d2405000344070316003c891200300828110307030b40ca41408a49440080040000c1001000940b0490360b443c1a4000020b2040048178111404000010030031039058004c0800d1200080e0784030701200c400400d90764a9401202c102d0420340e036502c2c0040c007900814100034110741c03c160920450100d07041c4070f10b10030710069500300b120300ea44400350803d8034105003000717401c00309c08c00080c00541003540001d942080d188040301c110049070108400c1d8260 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 17583549 1250 17582299 17582303
    0x901021005040312060b1608030601020f070303020706120c1d01050d02040306020d06151b08090904030f0e040908070b0411090405010e160501020c0f01110f0a050705040504030503040816020904 85
    0x29044da241d03011240501c1260068156089a94102400f4030f01c481020080d989000d0701b0800c000c0002101d5a108014008500c1d0f4040d0170b507507009070f8a01e0065602e0525009840224040404040d12905c0c0343c8190f100f000020341d2460105a00031030300c0b80c00d101c034086146040000400c0040403050f0740d40001c00042d48144401a5105491032006d0119100c07500104d26000001112802e11540003074400401c401d040c0855120b03007004d1800e0110780c0314880b101078100b1004400c100a05404c103030409103005883c3c64190403140354104100450702031040040062000703100213008a40001661a803081c41a4002c611945c64900040c40030141114112442e079161454501c0c401014412600d10802c81c01042d1b01ca01c1c240340020f512805200107080c0545842c0c3d4512036268400c000e9206c0c072031090000c0e2030210146d60381c07a035101d180301c00d810b461611441d0310019203030401e44070315031089070142d6400d400e584965032940081da1018007460b20786218014a179016965801007107000724 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 17584799 1250 17583549 17583557
    0x3020904021602100804020d06020c01060504050705030702010501170307200414011a04120206090102011512020306060603090706081003050d032a080601050c100606080103020307080105060a030809010210050403 93
    0x90b0902c10804504c180b8041607080240c164140001600c0b007402a0049543c03101015881c2c500f0381040c140141140e40c04607500504100034080d83c13942100045008030503640c020b00c000e07070303c1c1c4007107100d60b804160804240794401c10451001ca0410350002044040008608442d080c03102c001505843c3c01400c3d40151520741001006080f5800d981020720034007442105003001c1c41c04410b28440444044064010700c8000390010540e8400c2d0304c940c0003107107101800103500b620746905903520089860124000d200310303404580355140000035244500051340060040a06203c0304980c801005044490010320b440008000214140100035081030107603000140c004100c016821020a0300c011120031120102610581780e60050001d0f500034420300b401c0c2c2e555002181002d00e4680101841413802c0d00d04407001c140c055104402d01c2c1240c0c000c504460a10307440c2d402c401c0c22103006882c1d45511640d40340c4c00b00005a120406803901c5203050058460042c85051410b040c0c607001c960840c001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 17586049 1250 17584799 17584837
    0xd140708060106091a03060102010f060b1c0911010e030f010603030201021312020a03030e0a03080c03090f060301060c020d02150310060f050405030316060204050a171902060d0c0302090402 83
    0x34103810000d85006220615000b488585042e80c001442c0c080003450244416000000481a9000b5004124910f0b1400003c01c1032a0380c6085419040d004007110008524001208840140f124080c1c2000d0b07a4200704001d02d6041044019114050703d80f014039058001d882c2e003040026002e101d131000a602070740016a4544228000311581d4100340c005000c0300c0c180e02114805a2142c85200c1b003503c2e45400c1c0041102c10440000314820600e5100a0003400700007201c10020b070000c005050f66000685140018201441c108052400240168000995220540405417130301040d4410268009071030f19450f0741071042554102c1c1c4c81211100360071030300c0d107900b0440c2c0b0394802030005a6203050310b4141d04003803c10380081d45a1042407840f50640026040c1b1005102a80d41240c0c024080107050410413941c1e0f001c6070000184502d8004218084e158100d03209441e01d0312212000c69005000c00e103017400c03106a103170041000000c4401019420b000741000e031344903031009002c0c901c1c4810803c3c0007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 17587299 1250 17586049 17586059
    0x408070201092112020102090a060215070509031209060909040609030e0a1503091b030b07030608030304030f2105010f08011d030901050d1503060207020405180303150d1407 76
    0x140b81450f40c80f0340986100c0d912040c00900100c40b065448a070f02148620030071010b0001280a8000d0000459120001d00c00015504d0380000b038440c800300c1488000140c65481e0401a1081c0c02010081500740e00601100c0890703101c0800100318801000386078a00740080d50000ca60010000c40703045806c6540d9400f2042450713080340d451001c4950884e00f8000080c14268040104141140d0090625494000140c10480c0100034800c40c1c0640c90118400259681401005200c0607501c100c0468509a004079940101108692007541c05840b07d043c41160b030601240ca07600003080c45e8903142c541000c145072100c3d141c06a2402402c01509081689060010041c21128540310010410b4143c01c01c1a85006022041d81e402c03000900f4034a44841d4442803980141c01c81c0704440310301003c001800710422643c0d90281041034001c3d0343c2003181c0e81e1044048a114072510514482e540e00c184006400b14840c48009501c440c006004038051034115980c400c090450480d00381d400350000780e01849 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 17588549 1250 17587299 17587307
    0x30f060506040507021b0d0f06060e0a020f251407080c06030402030c0d02060408010f0c030b0d050601170307020402070501020a03140f04080a1e181d010b03090111030408070201 78
    0x2030040802c8604100b035060000b4007035a0789001c40380240f2000350380c0c103040c506951481c002a031040d410043c8420b078070a840c41d01c00001c5c4042d0103800181c8040c10045601459148282d4400e0a100103000b807400c084400e4406110801040350390300503003c40c0c0a280010f803030300e9040803052400001454443d04224110f4101081e030306030680608014820400540d40c0007860802000c020788904c07e0400590000c22150710840e00605819800e101060440c4480c0c1d60003055500000c0c1d504001c0d1007008410404011500703040500154403c40c014003080851400c008848106a802c891074113030345902007000d0340c01c500b0742030b10265400710300e24000c0b030b4060090540c2201180710360340c0c09283c44081000d04481c0a08043c020310313004030b400309801e4003896010f01000054030700920400707000c84004014a600601002c811002c55000054103c404072050143e04024815000b0030317800e01040900641000781144419905c03400b0f204490a8580001c40c0540e0003948510b03541c00f110b000140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 17589799 1250 17588549 17588551
    0x702120f01050a02070b010504020307030e0f070806060d050309010806040213060203040e01090504020901090f09170d06090203091e011401170706020c09060603060d050303070c03030e0601030809091f030f0605 92
    0x81e031201c4c010001c00740041c0c4884606815104115401038036600e5683c0b00700d000701020100b190303180c46a83c0341420000c0c00050310300c00300d038101411500b1950b1a0400d01400e008240001070040c1d01c244001607040d070141003055403141c0050310040c1400f42c02111410703206c46075404100035070070004041c0000c18810060340d024203400d200a200c130b81801d81c045181000b05120b040d8002e80e54085c81084003040b50800702c40d043d00b05a03428501204a80822129401840c040c481a0300c2c003000003406c91010b00a4a128a0017180602910754201c04200c0c0503a0f40c08d0680d9000f55030711600301e4032080c04881c1c6140a04031450000304000c0303140000c28a001895040401075602408000c3e03143d0303540506696001005031821501ca0711410007007101080c0e0440000c006002c04001c11501507030204524480034065541441241c0c0c02014184c0c90354005e00010705440c40812090000d03041611289801c0403070b04a50380e003e000718480a000740400c9030000c4a608510003500d00920005000f05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 17591049 1250 17589799 17589811
    0xf1305070906140d170a030e010f050a0509070501140a090e0109061703030103051009080903010f0209040f05060a0302060307110304030c09051e0103110a03020405040503071e030206010b0f0702120f0105 89
    0xe0401c0000c980c03961704c5113050207002065403120014516510a209801007400f0046c0b00b4004c1c00648441546000035010850383c203100140744c100090703186140001c0c000d04444040e11000240c1d00500e00c403c01543c42254840240800080005031030b640e8616014024000c00b400040c84a0174841c010001c03210005440701d26034014001407000ca031010410f04065101a04001000300052034403040744d002d84182c0c2945940381c1003e40e040c11031240c00514a50000b201c040040400300a40d140845209650b6150000c54915082c801800c04c5070003590003502c04d08180380504500410646140d005030403c4503c801c14843c100820b521078040d135500b1280000b0f44040649442242e018211030510000e0300103400d40314000c810303849641040b0b01442c0c0140c018031052900c1d042541e40d96024040480d100480c040780341194250b000c46050301c240e03260b80945440d0346084071840407038015103807851718500100402c100595803040500d140549030800f40c03040c1e195106580e03084642c02000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 17592299 1250 17591049 17591059
    0x10f08060411040c11031314030a1104090c0f180c080603030702040b06250c09050108030a0305090106050d0302010504030e0a0b0a1107090203040f051b06030f130507090614 76
    0x34080002d048802c07004000e801518000f525849a0408a40820b42c038880a4103d000008040030b40c0c09001034030605445d81841c280349840407030420716544810340400035001c0740c0403c07414021480c240d00400030082c09850790340341090703c4072010300f0100604c0c1e00c104106280c542c400c5d000c95490b0b002d0500d00803418108404140351100c00720b0385900c11144000e2103160784803041d190642c2d4800a40700e0f881400522005550442601d29404400340e00f000e80708008003480000d41c1c2c0050f0701820b81604c2c101c074055410015420016409810040d150b07001c82d5407a0300010445440c1c00c00c010754818003036070001c5903900305800e029003510380c0c6001e003038040c195604d428050f0051000898100a0306460042e21f89a120130b01c050802c001508405446800081800705002c0302c0004131650034080c1e016910f103035415911006040b240b4400e030315000607090001680004581c001b01d9405980350030564500006030b50f17001d04044040d04844255995413405008040391110001850541526 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 17593549 1250 17592299 17592301
    0xc0906020f010c08010509061302030a0608100b0a03170f03070e0f010c0305040501140910020109050607080402090a0905030c060c0d06061b080c070312080417030f01140f0a080105010f0806 83
    0x400184130100500440380a07419040c04510303e80c450a04402c0c03880c04102045460742020b03210b0703001600b440e104856007031046001d81507041a4901c54113507449001040354101c0d518559500720140d80801c90b52008003424407068411402403801148200c4150b9101c2402955880401c0714850b005400981080080d00b01c50001039000700071101650000d007018400c0000c01d00d0b03400441c6c82504e0195030003990515032400007a0b01500201056485102910100c0e5180300b0107e44042003150080d5004620740c0208014501a80c40007400d28014403cad240341101d02c24915103404002e03a24a0b07021540066580c003c4070881c402c1c440585818500503040c0420580403051151010f00e01034204270f4000340c00608040b0401c2420300035035000721080c4001c50280409040c580c0100e509445003411986a00012814481228407406100f03500c0c0065909003c0604501c2c910200941d40110180305078036001e90311407510800806604001140540c100841c1c0c1c0d40d00c0c03200344d02075516540a20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 17594799 1250 17593549 17593571
    0x9231006140a0906050306030c1e040e0d02031905090405180705010302090d02091806090106060206010e06010c030c0203031b010902120109031209020a0312020c04050c04060507030804020a08010c0906020f01 91
    0x24403c608a80c61880c004d9107a854400020381090349e4031070030580c0454480001001c80a1000d00c6910b1028101c9003000395020542c92242c4408408400070010307042000880c1d030340c150340c1e88241d0782d200091500c14108113031000814121042030b01c050a011400603450f20300300904002190251100b841e09500b0984000d010400506100d4002889900440e00181120368614010260040b188044402509000507411300a080500610f001800340d0320010035001a54081c1c00d005441c182d50b060300d19103581c0c90441e880000e07248101d034140002c1105e0440f4400703200c00c012411703882c2c10000a04410380e00c100080a024045c8540843e41000310150120303401c170b581c0041c82c0800c0803000c284240d0520000384401c1442e08002e08030b0203041c50801d4082d030b00040490024906079401c00031500d03031556002d15801548600d60004804005090000b88101c480e680c01134030240481c4a0b550300c0b80715480c02e54140c012488000b0351841004c101003981044041c10401e4940020040c00700d0003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 17596049 1250 17594799 17594807
    0x1e03040504020f0c01050c0309010c020a120804061b0e0a050901050d0210022a101707050d02041a0c060c03041e0f020409120905090108060109231006140a 68
    0xe114107486070b40d02007006a50a030310402180c0403c11350a0081140b8a01000c2415850300b00b5560000c10350304c0c1144141c0407600024072007200c281c004451800350104c01d00d048402c03e10040045501a80f0b480300d0710712104900b0302d9504552002d0303d603540b042050000340281001d00303038811841481d94200410042d113540c00a611441d4050340e161070700ca9400a0141d241151201640401c0c48456030f5145406820500d0ba20654400b15404107400c25104821100c145200310051204090a40801d09040c062030080004140c500d02c02350804d03036a81460710160303049508941c28000e000419014100003440b140d54008512a080d5045050980f50000b6209503401d1502c01d44610242810520243d0383c500304d000c50380208180420511440c041c180090807460440108142170b1011a1519020034200d0507140c4502c0108610380c42c20241c2000341c10303140b0300080540841102680241c00d602c0040744608295001542d002c1e02e8150010426100c4134001c0c44018802e0100024060340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 17597299 1250 17596049 17596057
    0x30c0d03060f121a0403030b0f0102010903170901060302060301031505070908030a0806040f0203090a0308070309050c040903050403080f12010504180b060a0f0303020105090d020f07031b0e0702010e1e03 89
    0x3000c85101d070500e2591a0400700e8820f644030301c3d904e0800d070200300b204150f4590000ca0800e50b042e100c0c001c4040002006909841c2c071208003d02003103240d03200c0c070800c10000c0419540310130b0304000807c20981d80e40104042ea8000c1e0170036100311000102958255240b03000d12a00403c0c1881d20403c0036241920040d00c0780241c10707441c4c0170841c0f85d0b404100141c1c0c490304035060b61244000c2c11550390401c4d02407a981e40b04036000c1240841c0d042c100055209000e071242200054001002d4600403045c44200001000c00d40310071014130200348008804128400058140b61161821490f40d80076142a003800035a0164000d0b4030590034a40701c408041850745902421650140e80c40c103564070303140e000840380311182e00428218440d6010020a159054100c24060800c0c1c40582d010800388440490f00c4d00702c03c1c001c1d0040f0b5804000d0400c002801000600d907580030030715600c4101c1d902c80c80c00490401041c3c4120005070344440001c5180c0c54244840a2a00300588001c0c00d4008885401e5840307001e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 17598549 1250 17597299 17597309
    0x3030a020a020705060c030703030e0105060d0f0606081c17060a0b03091015030b0117030405060c03090904061a0102070e0106111219180b0906090301020d090302030c0d03060f 77
    0x50003041c2084500e008119050107044014000c1d80c070744000c042d000742e0f00d810440051700082e00300320341c40f05800d8040c41001d0041d8800313041c0da2100e00700d90b02d4650079110700c00c0040b2010b580e5100005080d5034240b015684101e0030030603503c804444040c0040c485201da442d030f400317010402d5090205541e203002c40309045500310301549489035664406103040c01540c102958406040104060b0821040031b80c20741581d200e22120142a601da0100003c180000ca0518042da0b0041000b07100074a004030280081d14440c03001c5a250108070404261a040251030440303102d505c2d5004080d0746c214641a42504000a200810595117002c12017000944184101401c0c0000c0d00c2c0541822041030104111140100c5009a550b40c41886c5803008101d0840f451030000303000d101c11208410110a022080b50403c400142c20300f030f008402c0080c1544402e5129605660800001900700070320f0040c03103001c502a8000d55100c00c4c620101c07502340400c03400360104162518005100480c082504501078072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 17599799 1250 17598549 17598551
    0xa0212010b0405060729040305030a0e0606030a0b060a1d010906090b030c010305090307060e030a0816020a0611040302041a120d080112050111030f010303030605010f080420100503150a0803030a 85
    0xc00c50302620020303042c1c0031b045060070092041005158101000310700441e400c0c0002c00a6840103a405500d1b91010750b03e566041d080708110b000811226809241c2080c4024000115141e4a00c2204040c00340d10148601c4000c144004106550107486084000d04000310709003c240000e03000203440707010711003407141030503615000b190000104209030781589600940c200f04652907618041d40c1c80e00411407840c0081c01686c0041c482030403410b038010306801903800030a00b04034155174503405001d0402004501c80e106010002c0036a40d14021040903440600d91024200108014003000d43c00400b5441e00a5002c18688484603601034100360450b01689200c5070b0308450f9182c0240541284148480486008003c1c091004004200e40b8100d074800d407010840c0ca40d54030010b640d016190034480000c628800c000030302040c62040c0f45910144640107907200b101c12040050100c1e82100c0341d40c00000d2000c010040300c0348602c443d03950000e4003112050000c43c44d0801060b42d900c00180500036003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 17601049 1250 17599799 17599823
    0xc02120403032304060806040c02031c0b041104080d030c0c02130504110f030c120c0d21021b12010905030f070b060a03080901261e1005010504150c0b0a0212010b04050607 75
    0x60b4402c1c400d079409100c40b540305503104030b4071403001400b40c110280030b00c2c400c500e402241480020707440308a4040f00c82440191a410226160940082141c62494c00c144031280d0302e004016612024121540e004918000401d4182400e0800c00996841c0251307010740704016805c480c86d5030005180b2244142142c0c810440ca43ca00a003d0906042ca04226040346088102c1e40811511070413001240c091010315864107402050226034501400106125010700740c5044159420b095400c00c000352043c1d070010420460a580e00c600d141e100b419603002000c004184007080011809100303410240c1114280007160660f241d80b821445070a01240c18000703000b00043e020b4071100c520b880341610011600b02c9034a000040d0114580c0429402001c0010f01ca0008860340d94281c5c111b0706448040e51561b04041c10300e41000002e08481c0711030024081c15441a100203490b20034081d12400c01301c000540c5903101c035402c0036601481030f004404000018401802991642026210b04a80202000201d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 17602299 1250 17601049 17601071
    0xc030206070c0305180f190302030f03070c060c03050c0708010b031b03070e070c0b070c0b070309030c0b060a030506010f0f12030512040602040503060a09050f0f100c0212040303230406080604 84
    0x703080e184403c4c068111f4031600e000280040b0031002c1b030080342d00a42c00d07201841d096240c0e2984030f1060b01c1000382400900001404024892045024624030030b0a2491a240c0803014561030f0511a170f00c40b60340c607912a940aa0b0f2800c040c08030300071900710301039000d0741c501d25580001d8503491030313020f00c0001400e00b00016228602c5206866040364200000340d2950904c020000c01461100030244c81c040703150070204041602c2031062a6610381c040e41c400d100d00e80750381c1d039444940c81c001d44180d0384090784200220120303070140400d600801603200104c0420340380c003022101d1a50241d011800003d00c00712030001081c1c002d41103d041020609141d4480da643e80b5201009000d80e400048e00b5214038800c00031025120340c8082d1150f03004d4030403244100a8800c40c40e580790342030764204030a604400c1446202542039005481e0840c0f60340103a5045040e018140011034100e0780c025400030342070680e94840108135009007903185e030310940064036140c00c0c1507024142010250599004555503001004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 17603549 1250 17602299 17602309
    0x4060510020102040603110304080304020907031112090706090303120b04020403080706021b0c0a090e010204050334050d11010c0c0b040f080c030d1206080d0c030206070c030518 78
    0x240000a020900c0c0929080d0002d000390410f00514010903c0d04440400185000007624452076010020a15642c3d645d4284542003002605640c10705440300781142d46200c0341341c081c09054149211041040c40e022002c0f03031414030190b0000003803025124040c4046580440340d000504601180800c12081d4a0003007030081c440c590016000e8800460031200f0081e248c1c0003864000c03441000c41c0201510b00e4400f6403600b001034003d9a0180241400704456403c9410040103041d10000050800c0c0d511000b10b82080003000c401381c604000940c2c4800054407140d02002c882c0890981102d404c6d08200104644050000e0702400384460700d100401180c2c4910301c81800184e101d1034000e0b070559103100322110398101c0d01071240355006010002c00e55140000c0c0309010f2070b130010020200343d9243c250640d1a11030894002c01400d848400124040c0b82c00c002c5071094503565030f201c040c0c1c00c9007800d000781020b8020b40500200901c04000c0c00101e0760202c203481c000c03904030b2500e461548006000030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 17604799 1250 17603549 17603561
    0x1b0204020d05010806060f01050d0b0103060506040602010b01020f0102070c03032d1e05090f22050108060708060d11010f050d0e010e060915010b090604080f0105010503010b0a0e0408030604 83
    0x258018000521540c600e0880d80019040f261014221005601c5d9003003005001c9404002542c00201c3c24000b45078a03031815000070740d031810181400915079880d00c010904583c0280c00c81000350b9100e4199100d1540d04004680801c20404000c60900e4a0356a0f492203280320740c8409400c000d090307080a00103407003035070390010400610300350750001184a101c054400c512a0040340b158804001316028402e00420032215401c100805900050240f8820005107000f0b11a140007021901540703509031919078803d403806001c207103004181c3c62528040081c61400002e002d030340102c5c02c42904030005020301c0c1405150017401d003040007800700100700844041c000e1554401065040c003400306e00c07044041d800b18011342408020342e0910360f520341d010740c1d6600701500d0100030b4180110041100860704006001c0c000b200904561926a440f909140b0f0001d000d007610a00340d40d200300401070341c40d0902c28201c094030103440b60340442c3d01e0421b44d1000318038010806840c4960002c0015125a150390101d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 17606049 1250 17604799 17604803
    0x90902040e1507020607050414040e07031203141b1803010f0c0c021e09010b07051204060e030f060c090904020d0c0b07060606090b071407050603010909060b0603040b071b 75
    0x181e08001a030351080004240c1510b4030300c00b40c0940004a642c0134410340231a0103550700340068000c2074018009010080141902c00301d520f0154010101c0003072000c2080c1c14014000d80e501080d400d100348a007455524005d0320b80c0c00c40d500c400840c5022040d100f41500e4202d2207502c800426400c1c142c0209015220f21034544103024139281784800216000300d03848000304e0094403019a01d2000b024081103100c040c80c100781c2d1103102c89004000495104c002480d92611072802c0d40c051041c1d2000d0344040b60059000b0401103000b905d1811254202080061035480f11600101241d0420a0340424948540f040c000c0c040d024a0002a096403119660115803641c04800001c410390740302d45400c0650841c0000301d03201400d01c0d1001a84d00d00c902e00c10800e4510600c0c94510345075207a07584a14202860540c12402d0145104c0040d0342c0d6603010265000b800d41080105105141e0700d48201281e08410a16201d00400c0c070520011803080761803181e00001c170b410b009100d040600100c4101255900300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 17607299 1250 17606049 17606053
    0x10b070f05070b0d050a02030114060c070315020405010210050601090b090d08030a0504030809070605120415060b0a110102040308030105190902070309030605060603040f06020307030905030706021e040f090902040e 94
    0x80d105000f070001c02040300000d100300002e40b01c1010600503480b0a1041e0114200307003824200c0d040c50828018840503070030704222050355503640e4400d038042e004204403c42007030b0f0201d010081560140001c01001c0c808040421182c40c1540c0003130401c204c940201c034240000031801d0341a5803180c3d45441031458108000a07140d01e4442511005804125000c4002901000102d080404000307096005c3c0c60781d41e11000d00700b141c1e410320300c0030070800100151003118003520f00703030801d048920420000d04a00135441d55204901c1801403d58809007030654100e030320400c4108041000d1100396410748030100d8801d02c1c0030400700c4c400c2c008825603402c1081414400107800040581000700d203070803248954410b110035a80c02081018a0004940140c1205425480320380015540d90086d0f030320204078100007404042d00d4441d140345802a040c00c0752003c2d80040d41701641e001c90360405010001c850a0107180c00d00f00300f2041c40442540c41440c0303c0e151601c03821021980c850f00811001203064007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 17608549 1250 17607299 17607313
    0x30507021f0203040311070f0501050a03020904050405070905010b04060e2818050a0614010305090f0a0312050907050303040303030509010920130b012709141f0e010b070f05 76
    0xc0040003503000351350031004030340d0240e0400c2c0c6c0c0131008107400c000c841410300c80c29081850314005503080d44c082030040e402c056080050722400d80c0d0702c0c4140b40c003440c000d900a040301400c0064500485006070009a0711000034881000029401000750611000546d56080d40b96070701c07442717441000c00003600702580c0028800003041d89802c01c10340644c0c400c03911406000e141c950480e0030003100e000d4010f520004a004000304099400703600070780c0d0000c2c0250b08444141c0b601140307250130810f01d0302086000a90510074020140382c0d5024268009160764081c1c0386803032401c0f000965070702c1144002010706403181c0c0000e412050030750000710429000503201600b0104d075a8482c510503003850100c5d00c039101c4140d01d401c00c00c01e40d02c980c4a4005040e114910441c8a103400102c2510001c09001292220800c011820060500821120000c010146901ca0a00001180c0d0030318088240307548001c2009020002c2c2050b000442e41160f04014220b692510241080c6014a0401c1d5000d0304501c2010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 17609799 1250 17608549 17608603
    0x12211b0604030e04020702060901030b0a0b0406051305030c0f0904080409050a0b01020d03110912030c01090501061a0a020d031109190f050402030c0304030806030a0507060314010e04050d03050702 86
    0x30030210321661199460154203518203081108900808801035080b01e0180714207021540240d01c03502d0602001007000e802c840d0344001000d800d41c01a044100003800c0841d5840d40c0001d01450f02c005407200f2409000c4000604011030101c080400c18103100b01401000315091169400c2203a000d854480c000b4040c519100790700b400900841010a40184100000146442e12074801c910220485803c25460080703040200316120f40d04240180c502e010800021510210920680d00544e10030f2001103041c528040d294a28a1423009011603608400c00c44184c64a60100c1c46000d401914100050440e00140000c2124044c03000075603040103444202400354804080c166040302e07440c04101c03d4540c2c0311030034002a4001910a800208814000b050000717004005c0168042e40150468800c10780075162a450700c01701ea408000403d9840001441d0708032918030550141090183c0c0743d2083c10a503031019519540e04803203404141d82c460115000e24402d00c0b03090300701d5401c905061400031650b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 17611049 1250 17609799 17609803
    0x1303050601050a08060702060103020f06120f04050606120607030218030a030908010e030702030304050d1a13060c03090f1205040b0406023f0f0706090f03080612211b 73
    0x38002c0ea40b1450705800d001980c0c00c000201948580c941d41e0240100c4e1346550300f48510a1540d1400507402001401000404100310000a03c5543c408002c031042d4241410014100a0040d01d00c0b4005e2141d1034072803200c0c080014000b5046902c40c50010380d0b43c5047c070a0b83d2001440ca80741c203945030042030098014150320640c0300d400c1c5d401d410020095811583c0d4a5a56840b5403440203416030400d00c8200910325048210784806030158130008900400e4000c0d071020307001308a60115031822006c070410180f150621940a4072032140c14100b00400803600c420411480c02030004202800c1782d10412111031003241514001e08059151701d894540b03d000113512040c9401c0f403000c07442c160651085920f951014001040002c2d1031040c580304c02e080509041d1540b003090030f00e16a100401a20b40001e0451141a00e824000d05881c8001000340c0340041001c840030740600c1c804c4261a44000040d82c022481c1003003142d00c40c44421030700312581c00303410307941c0038080c1c645483d00624000c00c1418000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 17612299 1250 17611049 17611051
    0x3010e09070e0f0406050a0b0d0204050901020408070609060314071b020111010216030206061503010b0a0203070c060305092109010521090c03100c05090103020c0102070c06052a0606090c13030506 86
    0x5c1a41c051055548450562080300c1e40c03804411703070200000705c00c0400760410750f100b139420040f08000903180a868416503860121640c1c8100c0c00540100380401c400d6615108021420340740d003082000f1401c0002000740300035605050031100c0701c860070919046a000d02c0381c2d100c1e000c02c1c901c025501c0f56100d45032040c4030030b10b0a6065000d80034000010340c1c0792030909400e44400010000316411642014440c44090b04021410002c1d0704c010411034000c250b004d40e600e8002c251b607079400318030b520b060713032003a41008500700d01050b00b100035468403255114100c084c4c44081c9030a2801507102c0c0c83c6040560460102c40d0032595030803820740140b0180800c08240c9000120301501140c107081d80444a0208482d0305000368000100140000e001c1d0350700c80c0d0018882620250005410840f50381c9a040500c50b455118001080002400d58000140745088a030008682a00e95200f01c01c960501e5440b01d00042c42944030b404410700003080f02d03c1c0d12080d2001a078114204028554030f0340780c169a0307014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 17613549 1250 17612299 17612303
    0x80301080708010e06040803130c03060f0f020705070302040c020c0414040314030f06010f050f0c0105010f090204140f0105190504030201030b0a05031c020718091a0403020303010e09070e0f04 84
    0x5841c030100308002d050091000d8464408020907075681c413601c45c9000343d0806011a0002040c1a8604010034541081880a10701508000900c02d101580c9078003114051543c1021440c0103000b41000300d00081841800c80380c060f41c01055500071902c00b2400c10121401c4070340d101e0b01d022004101040c2d038080e244d01c035510a840d6070791074040100c00410180002c645278181c212a240010701c03503510502030b0140c40546030921904211607000f2000b0315410180079644240c0d9950010040405494200c5000700680e0504619041c20710340d1903804800f40045540c0520681c840a2080340d01c60811580d51602412900c50030011110f03004000b175005202c281d00090030246620750b075141c000c541100310317200200102450900e0b0018680781c0d04504050344103602840b6000510442906038109070440e007044005006e8405280c0340f500c000c0e90003000001560044200800240c00008980c152020202415200c0d590440020300c3c144c4160070103004401103106002403510b6070249940214 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 17614799 1250 17613549 17613553
    0x50a0b04030203120702090a02090109030803040308060108010e010b0a18080a051b1804120309061505090c030106080f090f010912030b10050904020703110703050a021201060e0a180203060408030108 87
    0x121381140c040d96103002e0160065030000400d00801d40046269005200e4044181070201523950340340c0380d8190035041103074180d01141916040141941e1b00144890141500b4120603096505012003584030b4043c0d034807100c0502601c1032500000140b01c007c0d800081440303c0c03c80710480c02a191441d1a001d505424640c440c1500303801888910300503481060060910000c041103a80d2a290b003c5415620300d0908240f540d100421004120140101c851140c0c0c0301c40201021880c07c010702000201c000d050740c0d440402030005103c0356600c001003980002111490300f00b04d40b1035403041c43c2070110181c030b40001c0358a441d4000d01048003c0401403003d4800781c40811500c01400b003800200c2484022600c000740040282d03070b105107032650180c400300e07000e80703000503543c40030051203807618066030000c1d102540032003103910841c070705090b0602007408110000d1020790703e40505980111400f80912002e030b61a03040501100d0a4481810308050f001802c4079070508003401c0440255000b0301071a10b0314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 17616049 1250 17614799 17614813
    0x30b0703051506030a1e0c020f06060609012106060905040b1210200c0309030c0a030308060d0228061101020f040b0304051603060e060604061203120204050a0b04030203 74
    0x510302034452248160404903821405400038420801d05920003880300070201d603181201500300d0301c42005a1030245466000040020900d440680fa10340c0592100400f64004070400c440340d1621030542d515503401b801c24610b881000740880740d440d151841181105450500c0003d04250701c11201c10446c0c0c426035040203207044c201c0038082c8000300c0703a00e01c0509500102801000110980c4009980501c19944841000c10a015204a03520904601d9102da1021803030408519003441480500542103a01c00d045a00e150f42c0030300307c10f00c0205814814509055024150b40380c481d9038020312680444081500541d9000b06840c146a034040d010001c0c108200c03205a13102c0504c200c42c4641291002c9500305031402098508961004100b11420300403010f0701c9400e44106090b060255104000106500003d00c004034507040f0003d00251190341000801c110352005c000249002c20382600d00901c0c1d10010b011000c02038070403644265000302c800400001c40d83e102c0340281066a100318180c4800c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 17617299 1250 17616049 17616061
    0x6030403180609050907110f0d02070e070302030f070507110d0515010602011e09060209100909050603010c05070618021005040603051e060d060902040207030c1101080702100c0c05070807030b 84
    0x1d52010f501600c0d411400300c4012481c810b02403c0062404c1c10028100e5000700007441c8900c1c1404444014000513074482241485100c40c80c164450344030009103030442c1546045402c0704203096010700382d8414400b000546c20107000000017030915950002d4910740c1503040b10304d007542c0d42e503504204042040c0e0300d007030011418a1060141c4004140f00c40691001c09480d07003080c900410300118211515503080042424944481d040281a080c258440c581c50300d24000c000c0e415680e004144a2280c1d1400d40e030010182e0f041002e032030099401180006107007002c000203241c1c1c6e035104000650320117207017400a111603500200401c00e542181e9420302c01900c40050b01d1031461a445030310b00103280c1074400141a400c1408049246ca4002c28012883c8041c507000303c1c0813a4041e24040e400280110f501009002e080e0351007048002e000c0c40c1c20400c2e40b801c0d120081d183c210300418441e0780c640303440c9640b2070b052040540b241d545812206440200d5a52505940d0321080d510007141d142c9803010001e12 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 17618549 1250 17617299 17617307
    0x1b0302120607051b0c09071808120a08060105070b04060203180601030f080a18090603020f010512060906031011030601020106081204030b041a1501021204030f061505060304031806 79
    0x8010700e000e4940f030f801e0000d600000c1104004070000d0b49580d02c0307038415941643c0d4502d04001c1c0941d00946a150544010350001d41202540790000201d5038085011001421002c004560104490785056080b82e190040102e0720b0344103002000e1b03e0107405005010911450f070b40114099800104010400c2c42500761558540c002488050418540340394003602188040000700801401c0d440c090305101204a441e8107a6181c3c0c3d0020700016a48403030610441c240f204243d0318140c02420030b1402d0203030700905100014401081c1500803418040401d820b62410030884040049020051046904921286060b038004a515600540c03e103080042d00c5600404c1500d091041100d05d5881e06040d03031110601c5104c050720807241c80d074000520150a004d0041c6950048486000b41c10840080100080c03500c00f0307642d508880320504010400000b141c032040300c00243c1e0310003000b01e481d05c1c440c20002c5281c0350740e9002079000342d400002c10040550101403011902e80e82c2e55403003105915800211 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 17619799 1250 17618549 17618551
    0x90515030303040f02041b0201050402010909050f070c03030f020703080f06090c19050d1107060c0503190905030910090819030c030804020409080f0d11070f0308070504031b03021206 80
    0x15056081000443c0200700f0304103210300b00b240003a00119044030741e1080365005000d880c6001c0e0060f5512810f1204540c4c0c024483c1d0000c00c0c078104d0a00c52410b2440203c0e02c40f10020b4200400e104603207030582c00705406038001c07980c0105134280c00c646450742d60070050b000050880d41c3d1441d12542e03034009000391400b41a003030b00981040c4c440f00d003008440c0740e43c010080088420241401428050b08407620003034040d6082052882c3c0c201c40d1104540d190420541c0c004000d00000c0c4031080c010020420350383c2000c40040451000c01080c030207030300c1c01c1440c01d51050320740283d003003403400c08035451107a000030302482164804002c031004e0360100c1c01010b9032610400c47c001e0004240144800101e8030480c01260024002480000c0075032240d550315405030300542c0301a502c030030302213286001c440403031040807004140d41043c185440c0391580c40c0c000d11217200a0040910103c08080342102e03202e0340580d80507590040c180c42c150742a02d090017401003d90310080b84582e05508581c102c0b594003285072 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 17621049 1250 17619799 17619841
    0xb09060d0302030301030b07050405060a090303171b0703031104120201110705010203181c05060a0b01020f0a080a02030408012405030102090a03060f0908030a09051501030b01030b1005030d02070905 87
    0x6142542d01b141d44107014154090f018200b0000d0921000c906643c50500601c83c16076240c5a040341245036150142c00d200c610310310004843c0b1603d04011080c0c421101c103504860882281c5641e9a00030700d0140c00030301c10401030000032000071a0204403c0500080000f425000740ca552103c40b5604ca0030a903505c3c1076003d8940140c006001c09182110319002024040c28018003000d01c0128461154010150000342500e45610581c04d00800c510795104095103440b080c03015191621840408030f5660000c440c0040001d54005404c0c03500328800d1064a010f408114000c1c002d54032041c540c00b0044107d1a03103401c40f91000c0b140042c15240c14402c42d4240480074104981a600d542c0b141e1006111001000854903243c021100010700c0680055200d03214040c400140e01c62a820101d00c1c3c250842c1c043c08501000d00014400300d41103052250440e41d120003010300c1903540321044d03003891b41e0075400140c040c0301c1c04080c52021600030034074005841d580d44e4100140e695030404081182054054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 17622299 1250 17621049 17621053
    0x60603090c0105070201050d050703380f040b09090703060501060f0807030e010219080907090903120b01020114090609060708010b09060d060e04080a090801090206040e0711010507030b09060d0302 86
    0x41c12840d4014405403076402d005062160403c401140d404007958000c40704600001d41e03641c0c00701446c8008410400d040aa01c4141c1100021a401030128000c118507500344155060782e038003802c55a43e0381000701c002c00701070a100c8180c140000b4556980700140000c4a40318240000454058464080304050010355550300c0b14030384840200360024420150004002d54003001415000c0d400c4541400507514290749203021440c101e403005050000980060031103a05143c500380101350300c4801941006409036001a02d40e0010300107030300404030141c007004c545d4019020043c2c83c1d14080b5134544500c40450a8854564800e80111680d01090080449140c01800240d0304c904040d800342841d40d1000900241c1c10742c407003180f040780324800c6508941e07410000a656075034a5100030480010041203000380401005a40000e1a50045000300c0c801081c0010008060038410306e80c982c035449407035000b08101d0800510017000f40001c10801802000303100c0100b0054101110f00c0d0108940581c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 17623549 1250 17622299 17622313
    0x102090d0305070303060806070e130506030303010e090102160308040b0a050c040b07060f06030c1a040609050d060f09030302090117060a03031b06060603020403021302160809060d020c06040b06060309 88
    0x1400782c660743c00098090f0201540c1e4600829002d80411140340104140d4855804030400d540800c588071452a072201115400c0c10203010721a01c0010999041d141c801c0411215507580c074443c1402405584020705409110100d0380f0140b5030045611402075009600d0035013140d4038040c1200a645042d1944000c0c840700b00f01c104408400b1101800c8640d101e013101059440051040d001a116190001d0300c0a50303189100704004030b200340c80b6440c2c0c200e4459040e4103051a04030042c1c140d074441c0c410300b40601c640079940c20030012241d1020480c01241d01d000c00c460700d2a418002d0094104220040c0814170f6041502c010101d01a101c61054200801c181c603114115941210003182d645000b410700040c9041413000655640100340c0504101c0d500142c0700c0b4a9401007000303416828241000d298030412860502c03649a038450501c2e0303038005013499600c0002c0e401140542c410154650a1580b0105500728400404590303280194007036048c0c040103483d10400c119aa1005407007103415030388100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 17624799 1250 17623549 17623553
    0x8010203040f140a02030708030901021515040207060609050a0b03070501020304081c0903020a06020a0605061c02010f0905040f050f0c0a020601090b03030d06170f03040605040302040510030f03080a0e0102090d 92
    0x65148146039180350700340d1310031481660100789050b10135005401c00da0000305148106507130400c80e81d030a20120b42008801c1d405c0543c1d8a0080e9041c2c000442e000d00d400059a0051020541080c0300402d445001000980340805290005000604089201b4055030a0009580d80f001051b1426144000c015050b10340c080c0420707240c801c1408032601c003841464a0700001683d02c0401c100d00a125a4011b03000d00c01a500c4c0110032168018005481100200e1a4003c1000e848010b0030f034807503080c20156007800c0e4900003500c1000b85584210392003402c22080403c00d04480e01b00c01e00480e99001d01004540301d11044100038050050072600580c440b500420184030250041d40843c0740107816a842d0881c050051800d8902c2c6811542840f0140c04c2105410b03c02003081d5500114004003542c00c16041240c014501c2c46036110183c81180c0741e6000c528141c0030b1941140095900ca1700555a07480c651078090845481110400041843c001409090010600032a51507160081c001c202e40c901075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 17625905 1106 17624799 17624813
    0x30f06120f260a05070c0e01090c0806090705030c0f0d0c030506100207030305031b0c010f0b1305010509060915040f0b0f01090f0b03040f0803010e0601030608010203040f 75
    0x41090b160414a422098401200c02c900e4126580c0115040c810240380f4180c10480340c070301414000140902c0180e100c3c103500102916041000c0d03a1318420000026000c40311000801c00400009155211220041c240401396000c202d040000c0100e45904a45006c11208046aa03074800d02180c0d140070801c03c00d056565100400c0c60f241075503070050041c0009010654104940b95104a04440c14010380d010328510000800c036441031000103001170495504071340c0c01491010712030380201c5020b0149606030348020f04132058548418040c482e05460007004002c00d0040082c01c000c0700d540740d0060208241711410042350b40d1007030804024450340d80610040c1481043c100401c281740c844030901c421501c030000f06685030750703c505140b510007081c280700a2001b100040046450419581d05500581003a6010401c0544804a0901301c0c030090324050912950003504400040311 = true := by decide +kernel

theorem cover : BRFrame.Cov 17446049 17625905 := by
  have h0 := BRFrame.cov_init 17446049
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17446049 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 17446049 ≤ n) (h2 : n < 17625905) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
