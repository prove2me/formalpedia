-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:32:42.945899+00:00
-- url     : https://prove2.me/submissions/9a09778f-1186-469e-b7be-384b9fca00cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 906115107 ≤ n < 906294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 906116357 1250 906115107 906115117
    0x6020a03081602120307211406010c150b0102122214010504030f240b030f0703051b0109081002130501080910021b030d020304060636062301090605 65
    0x903034032200d28440710600c0003002c0c5900003014a4544500307210703031010108110802d0500d1f42420350703a84152072185580701d40c855000b40b0a00b840501c0b94115980d642a095884010760300c456500c0c09104078031381c030a02400c1d80c40c401150714251120071070300b2b400d42a90f800070a102111516600e0000b041d500816107030380e4603041611543d05103444c3d0f40b80c00310717922606e48003284c2ea460420000e68100d15510328580b0030841081d4001a504e11400a05242041ca80c0140040d42e000c1c460420000d880010768541c01000e000f0011030224030140140c0782c41c00c0340d030001095400b800700d091a080080e54058514903021840e00900319564034010742d0680700544d622a0150400c84442d0b8442c0078035001450020510503602c0e0301d58030012101c40c1190000551145095000010301c01032245a0083c00007400741c00307180d1411365049000e0250003003075107450000c4501501406050702c00030b03a4001030090130003010304840e100392070100c0a8070905175510b042c089003142c0d2010032070a03c02c0b01074074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 906117607 1250 906116357 906116401
    0x50714100801060503280501030510020403050304050f0103110301030b04030e01050c0c0d150f02130b030f0103030e0a03020a030516090e100b0a051831030503100f06020a0308 77
    0x141c26a42054000c89055100401005400c09104051440c14003541c0c400c0710742581c15100005e1550462504904041040040b40c1c034082c0140402c1c1702180005c41168100d0f08129040070700365526100503406010001144050b0203000703c00003061101c2c407003080f4400d0303120781d946100400010005450b00e0003100100300c10f591200094a01c01e060408124148130b0044c4045400c00450340740701c4055480000d11296003540104080100d02c2e0645602c8020380300a802503811460080d04290400c00c0501c000b40030001582c0040c14075031100c0b80300e6400755802420301c0802a8032814803d41d9104200441100c0341c0c2807000000b0500103a102d420040c81c40308014003003000707041d0042c0700507004240089a1104030700718005420b6031032846c0c0d55000c203591050a8998030b0302244200c82d1481c0c032032a00301000c1d405540301400f0034024a0b007030103441e4141001920383d161700310180c40710714090b04a0741807403140c000c000c074807a500040d008134403d05c2983d44480980d102c48114101e1900c8046074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 906118857 1250 906117607 906117617
    0x408150a0b0d350a03051b0307020c1309050a080f040515040611010501030c052101020307021c0e130e010b031506131e111c0609050601022a0406030b0405071410 71
    0x42e07044c062281d0800d6400c41800c1300b05820340300f00c00c03440f40066401540c194000da0b00101000074942080a0b18000c800e03081c1d001005003611941701c46480d440020f80c005d06079040040d02030000790401080c1c1c1d01500e0040d2102028550200c440d503da54058099003001c81c0a80500700e010310014042c40341a264816604010289400e062003003400b494140380c03610704255804cc0e00c10b110244040c62003078409038020150070f003201c2d12820f0000307034141c040010170841600100003511090101c06408128080c0002c55044c6001d0050041c1008210654180250012000c5200103889844c0c010740b001c44031408540c00d1040d00b50120350942002c01291400c55542c10408402c03640245d4904420040d10717403a00011030038070a410318040f0307902e451490b41d9a006121041052107403503072012081c0010441e04403184952a046013922080d010b11068108214510f81c403070340c100704000d43c0e20005601181c242450160380700d100f20302403804c81a01c2d4010084492a10b100034420026061b110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 906120107 1250 906118857 906118867
    0xc03050f0c0c071701020d05040b160f0206150604030501290406030201081b0c060709031709030307020d02011202040e0604050a20180d0602070b010602030408150a0b0d35 75
    0x20a2a85020041000f840c655082c8410441d80349a401982d100343e1150003450ac0620308102440c2c07600e0283c803890010800949004c041d0140c000940f03030b4203c0e441902249032034440ca00018104e1041c0d0300014515420142c0c0c244010705a11060300715030f82d40c800e80c42c0c5040141c9003800111000c600c00a40000c4101001c00e261403031400081404001800c40c6c145000c0b000c00700b035494000251401e800041c40f82400b0000d1150b0120b960388080c9402a00900c2e01c000c40b03000a0f82e0b4054050003a00c1240415240c0c01160b01a07080085a040454020340d1255562050881401012508140964100000034600c0c0c000b81c4505119040d440c0a0071a101d240d403880310413290001114034410351801c8400803d03a544800b840700b00c07d407040b00003503a1445a4074100d4081401a40b1440540d48140014800108080341182c4c41e1980d1030a81c401a0b81d8900f00c00c4080c0500d40142c503048449100341e4001e1003059080c18400389008503202d00ca04110302001001d28408114041c0380046c01c0c89 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 906121357 1250 906120107 906120119
    0x102190221090f0d031e020309090c03061819140c07080f0408060c0a020114060f101b0602250201050409020a050c0f03090312030408070816060c03050f0c0c07 70
    0x2001d050031030400340900d158000f0309000f158030160303800340540200e00b00c42c0f203d800381304c0203602269005100e0f00c041c5042008013070100da880040500038101c5545d0100c0095020b480b44441104528242c81c0c6441d5142008007100f80c000c101c0c138482240d0b8604121190820801c1501028003d034000300c0224541401911900015001070b13001c007840c01c50400bc000760303540c803c01015000d500669070082d03039642485006400c4440c6000911250304040c000c1000c01e9659a04112804c80c09441002c2e40325070100b0b04442c0b0030380118081d40c1e40740005040d0b07401d211481d4003400915140ad0b6076000e8009401d0b01d0075504d15098500240050700c10030080c001910540c024018800d540c4c1003403802c0c442040e0a10781001d405140310481e035840400e1000c054901040085031883d013a501d42840c1d42002d07280e500052080b0403010b0b01c110170004040c80c0b1306400302c2d9045521600090b0400006001d0386004003c0c020075100c0400c000c110001041c2c01d8214002240c0074540808010b0129500e404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 906122607 1250 906121357 906121423
    0xf1e0f061a196206060405070c0c0803070c0b030108030d09060b131e02121501110718050f010501200304050409050a0506010915121e030201021902 65
    0x4560540c4500c40d0030040010800420f10b003d00300302800b40c0c03060500b4003c001050904100d004030703140580d055102004100200300f9542110054401080d50741d1000c2050340d41c4180700c0401003560a01c0c003800240941c011000e4080c0503c00d02c03100c00313000d40e00c07841d001c00760000380200c8406400030030021401520503441611000d100f9000440c520348050005400c0f0a0001c010361b034400e0b01e40b80701100b20102094180c4201c6219001141406144d4119030b9604070b004020700c2c3c001c03031490a04600c0d81e02a11211101c0e0301b03070408448696031110880a07082c080803403a80e5101e800e100114450b06000034049050320740607555038034841c251306c0e08203e0381a14504101ca99000400003c6081e0700d8900406000c00d018000601815100c2d00d400d0740340039070507032000104c546020522106e01d111115510b00b142c00d00204090022400d0520b22103c06511524202c2045650b58440806806401408800340104107881a011010700203036116101007845048048002c0c0c04091005104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 906123857 1250 906122607 906122639
    0x30b01060806031608030a110111040501112b0219030e101808070e0f0601051b010f1811011110020c070302030d020c0907030204030f1e0f061a19 64
    0xc003150401084030141501c034a0642d003140b10646c00000f00640c6080e0410386654a80300c41c10001c200c10b1600c0010844035019078001c045c10080b0306510301745030240030810381081c40c0d5002c40900040320240d1246000c440d0050f408001b60050900307801114180b40c42d144d00098054039403c003440c1014042100d003c48002d2103205200341d00359072034081061a0104400b4001c50300040104601304000c030506004000d10001440c034845041101d03999001c3c1c181c568801201c4440070020300500c2c4c80901410009040d0200c86e85060714407000031403651a00c49000d40640ba99030900e00400c0d0046440844103d41003819502101d81a14181000d9004088504007801030740e2819440794000781c10032980109040059111046c4100e903803403c50070b00c941050382c030b060845ca03040c40c43c1d5804440e01c5602ea40a407400800002d01d60b002181c07450701c9140194040b01090280c8410300c0d02c50300030404c50000c2000740c2c8000c210140d450a060401c1c00b041505500108411890201c804418581e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 906125107 1250 906123857 906123859
    0x1030209120d021015081e0703080a080115030b150c070506070b0a1121101e030b011d01050d080c07060201020a1b0f020f0604080304060c110901030b01060806 70
    0x20400655410805202c9242c4003071003036018005100c00b001c0108192012002c0c0100320382481402000220030010b016520480710001452a03000b20081a03814090660300191030b10000103a03050300b86034030511700ca058818905c01c0340300c0c0c14045c02c0f00700e003200c1450429035044403410900008005007407018011550381e180440d02401e46490102c0d2854101031422101d106910040c0800e00075140184003102403120485820002202814091a00b203003035001450807038140443d281050390741142c809840c070b60704080c00440c00044030340151215407005a9080240c01d00200740c051509860485035135849001c0c0c0b03d1a424041082000008428122a001c908110450140109000000080606400050300c03814584406080b1120a05903001c58109d000000c5002441c031801a80200d50161028100da0007454080350242c49242c0001e00d6501c40070500144040e4403060002c442841641a920800d0844040c810789038803c0c0001885483d5420050003058030800d211903003c03078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 906126357 1250 906125107 906125119
    0x20f040b03010c021509010e0304030609060b090117071a09040f020d140106020d021f0c0216181d0a170702190323031b03070b0f040b10030b010501030209 68
    0x810140007a086030860b0b4440d83c056040078101301c9042d0a00241d0303550050700715009004002901400310f480c1d126600004102c05c0d69800c0700b07824400305034060340900201818102e0305503114007003980d0298600108115078465040080380da0040303500d100d90040b541d010b05904100b000410007000c0c0070300603075200046600740000405034810b4021550f8107050030100c0d0b12994105003001341440c004080e644250741c00f90700c41205a0480c9140d50a0f515042c2c0b1001411008200081b8186101411200f0001d03c860b4404a03034400c81c84032884100304490410042d2003c80100c1041108050a034011560042082c0300701198400101c40c80c5016910101c41c0307481e1556001441e42691340c05c00d0000982003030000e00800ca140d030b03c120302001c400c3c0b10119110070700b450815540d01c554440521f424524640c0c41890380e0081007640c2a650b4803a030344210314644107065074090ba40484042c0c0f8141e07048408210814620844403050f0ba8220014108036800e190040d40030358010f449140d0040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 906127607 1250 906126357 906126371
    0x210406050703050c15010302120303460e160302060f090303070f0c360b0604092412110907111006080c040b0d0209040609050708030c07150c020f04 65
    0x129041c04161740c2d24501c1003040603654198014420384400c04909003c00364010800e105841c032121102c1480844118615007420007107d0b040c0012124071203071030700b807114402e21f1840030b0b10454011026050020040380d40c080099005450340d01421700c000303900000200440c004298035880113213100400074088a00c0c1a050f0340c0c44404030034080c0c03811b403040840058144842e80141d40304403038507480100c0300b502040210901354008807170301e200004659525800280e464403980280d034000e09040b0001c009004441070302c10401c0420064803041c01030065800305001c0d01c500c1c0b00461098114541440d542c0c80b038428064082d80c040c1075401800310105d408000c00d8004c0002c440180710602c00031541c1403400d15203a1074046011041c0303225074101901410103072550300c41034422a030102d4001481341c485040120050041d00400b4000b4001c4080101d404080040202814092001140d141990760302c0b0300001c0640220440c0001180300302600c000d4501200c400c0341144005000003005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 906128857 1250 906127607 906127627
    0xd080301051509060f0415170a0c0201110a02011b11061b04030816060b1e09041118010e010905041509021815040510120f080c0a0f0521040605070305 66
    0x198102014500c5c00220008003405054950501d6007032030102810310518a1015a0300710089140081c029035816036100c0742001407910035004114030414040b07020380e071108141c1c0028081e00d494001070540c40c0480d01c1c2c00d07040600c07a5401d041c842d60100081c201e42c1d214000d5800a4404010301101c6000e020701000c000700b50494000c01e00381074903d140d0a2030244500e00081541c100120152040c1d040c07404a80200c400312808540c203a8048540e020965a1854055184100d044060307401801c05010001c1d903d85000300141030310309141040303441740c0c1d840b4a0300703050383e0307044400500c107805083c50010083e405c2d41118407040d1004068110008036645404000039003103031141002542800f0344201c80c14180f240d0754200404501c802085400c004081081c0024000c0091194030403162110500c5030200c20340d0711300600181642c0010314070341132200c01414090410b81c2e20303020305a0030042052001d007142d10700b6030580354000e00b4035103041403d6542e50403404054041c02010005c07035803c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 906130107 1250 906128857 906128869
    0x110a03272109030507172a28090b0a150203160807060509160f0b030708041502030f060f091b13090e060a1b0c0f1103060906150d080301051509 63
    0x1d803009046003242c01840c0c9110700c1c60260705401c0442da00111850021300c00301202d0503094032540a4070f2121192008c078504018540d40c0c0d07410081505e2201c9800f00700340116820a0114580441d41802265241c10012940d0301010000c2009607008010400d901008201600003a070701030804103080c4031032510b0703060036030384102c0c0c1c080d480d600035154440c1512400d414841c050030059010413201400c0c02c0b42c4400130302c0041d044034244000c210020301007007000b0001c0042c1c0d08152909640341d0502d00e1074401c0900c01914000d1142e1107505000b2024180940d14a10442c0c5e074415506021048090744601c0f03501044540303001755455a00031884420700c0c0103150808800d04000c1295290480b0001c08580300744c0d5600d002011440c0801540755441f0303840d4000c030360300001412885002803804610394001e1180982d00b60103410704001a04101003403082c41071980d40b082c00e44020301041000f0f9240c0448800900c480c0c2e0a00050250741003980c02110b01307298110b503240c0341040c000e0001d82 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 906131357 1250 906130107 906130109
    0xd1e03020625140c0a050304080a03020607030e060f1f062321130204090305090f27090f0a0f0326010603090204110a03272109030507 59
    0x159110105104101c0725400b2504031400c12040007541e0a04204070040c0620220030034810780e80400705491400720414481201c82a0b8460101d990300d5549490803512100803040035405070041c003001410b103a0090103415034a2030758002400007a959843c04460405020b41940042000320365040300a40f0307a00145006011240c40e45042114400d803081420340708a0600701440ca818030071622103000380c1040050000302c452000303186540300340c0c03100190403045038040d50150800a0304401e15400c0b50007041030031421340c1c0382c0c142a6080d0090141c850524092a56580706075001c5400b844051a444c0d50050040001d5910401510000030310f41a00030f80251508000f08890108241e00103c6100d40703200810700040d481581d050007042020741c148200b005050315014600b0443d80c0744d50109218607084055503484001403800107000f041070341c0c4c1080815111207229203802195440074243c0603800f1030402c8604086c4114a41c09000c461a000140300d4140c0c0d01000052080c05018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 906132607 1250 906131357 906131363
    0xb0412060f050a0e0c2b080c1509100608060109150f030623011a030a1b0e0f0102010b03210d0603150f1503200a0f090b09150d1e 57
    0x4c0340c0c9808a2072541c0c01d2202c000301c07891040100011034180b003803019421044050404030420032013499420065801e20070100d40c0e41c0c847c00b40c0d403500d00c036031282c4034802d034000c3c183e100c00c403803044c14400944000c8890500880311190711820040142e07040c01d40007003407126101424200c0c460b682d040c01d55100a0b4941040f10f4517502d55202c1c00540203a4240f000380700b041016080c415525203901c0d071185058075a94020440300000000f128100340b9002034501e43c150031480c00b020440c04800038030038000c140d4201d110340c1c0e1148801591350700c14018400d07085001800360031000c044507141420f841c08224680c007842001c3c0b10f5100d01c40840d1107074030004d40c042c001c01c45805880300010b004881400c021084414500001601c109100201c0e104c256071b400400c0410b000c1442ca840a110398040c081c442c0d00c200b404402042c1102ea889414045502420045c003000040c4020091120340c215080680c0d5249103210403501e1521544200031349000d06000c403a011500c01040c410b14518890503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 906133857 1250 906132607 906132611
    0x40b0a0e1002160515010e060f1f08070f0c03021203090106050a0b07020a050d11040b01030b030f07080f030f0d0213090624020c010e0915030a0f060f02040b0412060f050a 75
    0xf1801d102d0240301140844d400c8620900c07003503050a0b12421b40e200080c00441c010026040c2807c01502c92003c03003074034080d1494144421440c505001400f01e00e04845000000710003075407480700e06015002c0c0304103255058010b0400300c046440c9200345a00000c0005086640304c450000d042d0b152440c841c4098502c3da0905aa42c4c6058018800e5818495010b84d0140415401d500f010170102c400c065107103d0102c4d408504003000c0e0f030040f000780c141c02031110f5050044005100401d513000449200701c9044d44d0584407149000c0d00280d40303902400390b44500c541070822030345c90240c80329801425001c108e0217280051689900612088802d143c020001c0e041120752003000f8503030200c0c024001401030384001c203c0310001d6070008040344481448180200240702c0441c04c03c0500e20480d035121000501150030340030741820300140d100c1d1041070507a030161034810340404205503402202e0980341140c0e13100d40350a02c3c02c0c010304584552030a0a440e141d0340e034403100030211228056070340079144100d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 906135107 1250 906133857 906133897
    0x50c030703050c0405010e010c020f04110a0206060301021615110a050315030105010602030d1e090303090b1503030306012d090f1d0c030702071e0e070206040b0a0e1002 74
    0x2800b280d001400002d01102d05020401042c0c1c1c5c04032000c03d4014003882c0100b070800d084d00c0072804107010300c801303030350310905100c24122200821005442c0c808002e508030740780d82c1c9070703001803500b00c9c0309501c21521007468211074100440c81caa0300f4010301000301000050101c4100700c440a017908442d903218002180041808000c8500120284050070200c00800555142c007002075520700c0b41d814500000c60321640d03009120308a0103e4a590b61340880320900004610f440d00a00405038000111040303400c900c0443e40c0000444020400008060011407964448800641d1446444080c085640b400c3e20040c46005000d4040fa0801e402c4648403a102c041c01c0402100088003590001184010040ca070311003400c03030964190f600000385404081d942d03150281c00b2401d0900c0d58000c1c0b00c50440d900c5403480d4020b0307030306601c2c412160200144046901e407090300b240c4852040c3c50244c034464450300420b11005151340100362041c1800101c66580859048001c02c0c2e03000700c441c24540d010f62500e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 906136357 1250 906135107 906135121
    0x307031b0c080a3e01020f0f16240c0f1a0115170103080702030a02090114040b060a0537110c010206040201020706050f0d140a0c0503160e0f04050c03 66
    0xc0000340c80740520b00135081081001410038802007908054041101c5410001010303402407140051020002066031001c841982c0d42650f103c8650740501802c62001c40d002600c02900010021045803521340700b094260301400403544e051035100107480b1184480c0500c000a0614038415030710301d10b84503926100b9850100b0010f81c0c600c08030704910512103140c0d800032441d03032900c80250641b075104c2d5441d80c50b10028004640f410300c0c0c000c8000d4100c1c00e0b0340004207400481c022012180c0c40201e4040c000200001c013408054055594034001184041c0031181e0403010b080c415072030b40c01e40807220408280200320a00e00c400c00000c0280007045803541c0c400c0007003e0601451403003060030700040c443d5080603030000f940c0301854846c600c100040442c80e070828031410422103881d089804024080c400f0300c035040400c2441c1c00c0d2544c0b6040c901d400d8240900380d0044064900c03c098160054010516242c01650401440800598004042d605c808100c1d50355106e11401198400708898403490080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 906137607 1250 906136357 906136373
    0xf0c06060325030305070c080303070c1104060f030212010905030d0c020f0a080405061b010c030c11060105011211070b0a0917040e010b16050d05031014030307031b0c080a 75
    0x9201c0d00300300e10181401180c20307960080d20104503030741481c1959954006007058050000e023500406142d020010074844500d512940180e180743c002c441511588441d41e04000850342180318596030248120800c0000d0710f8003c0c0d4204881d80160300210302c00e22140ea03400e0640d48880c0701d910341703d81d8505002c59040d90400007000748203908001020590030903200c88019005d40d2051034401c000005a003045140c90344070320312401501c54000c0c014114040b001038003071302c03000040000141d0b00910780308480c500042c42034100d41040e118056454100d10030000034000310b2080901030401048a03800054081d0b01d000e1103400111000035000c4d0040c0340007481c0300d485984406641d0011301003804507802041c90b2070304592900c00304582d070f2000c4032180003074a601c1c41c00140044c055260703007407119038100000f144615091204000c24649503602108042100e40c5c0b0b8940560090102a00003805490350783c1c0c000c00e400007020003084241ea170300403880c41603800c200d4194202894403c2041854 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 906138857 1250 906137607 906137623
    0x30109061e09150c050d063b0606090d020603040c0e100608070318020d0308070809010903020304050d0c0302190503010b0919090c09020406081f03020121020f0c060603 74
    0x4042407107011031588a42c031640c0f070241003040082c1e0340d803032001a0f5640a0401c61340c5441519006110159940c3d4a03d41c81d40b018070488032242d980e00c5aa041000c0c0a00c19440030644100000c001d107444a0061001d180c100e41850740d0400c0d9201d04c200c0141c3c3c0c410000d544645d110300c6c024003025040a64111410101406444135182e03944400c1c0300c565005614a40c0c00358542c80c000849600071040e001c2d0305400d80102941080d01c0c0c900300c40916606c81c51a0384103d003540c039000c3c00ba880703603800c8030708a440d060300240050300180404c2c0079500c0e09031810b202c2035008e45282c45883c0e86070780016401d0348001303801ca02d078a50700f84000c01007400d080c003e909241e00d0407159180b0741d14195070803a2011300c06040303106020b03a0b200d03002003c00100709020b0000c0c00240000715161500d5401c060a217602c1503c0d0380c2c02015041054883c01c0004026210550750306949040d10080100c0b410160456100c6903150302c03d80074003840c41c440a201c8060300b082100b020040c4081d080400c14142070002e9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 906140107 1250 906138857 906138911
    0x503010f0b010804060509100612120809070303140405150705010605030307020108060f01031e020d050114030a0318051c021305010e01060f03110c0705030d03150504021803010906 79
    0xd044511001d681c0190f07482ea402a00b014020a907540c60540c05401c04045a4014000d1858407c0100e000c80010070740e14801d07071241d82c802c02c482840071010759241c8812202c10400d50700c10030003800003910a03500107002c414140c864504040d191000108a0360b1310090b184038201010901c0420b200e424061300f001803505501a40c84c000203030300024403040000300800d01441500300c070340101d40d1196011580301c0049050040c2c81101885418010f0744c004801d0200c0d460415002041e40d17010403c070f144400340c001300100003440b40c580e010b49002038811101605800c040900003081d03207940c00031180e100d46200104a0050151040005140807a5642042d035441c11006002094401051034103490703440c101140002c03117a001c104d02504241000041074680401c680c4070381a0002800700c29143c00700d00346d0303000c444030040803002c81d1802c0c40c840120791204d050820031814507900516171721440503800c2d080803410368042401c1d1100d00c0c00889113603a944600c001d00321140c1d00120349001c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 906141357 1250 906140107 906140111
    0x280c02031b01020a170d29010813020f0102160e011d06010e0609061c0b0a0e070806090402010912050c0f0604030506040b0a02250201020c0105120f07021002130503010f 74
    0x41c1007000031343d2030305451801400858082151840c14042e04151964500030507024094218105140b0f11040d515a400c03100c0c0d030000c03412418981d03000d1030410384980340d002c10050040f80d20303408000b9070720155070010341980202c140302da10503140040c3ca20058207482103640710b2549408407030564400c0c0c04150519042d0b1034810b02849070303481145052850011140c140c1c40341c43d43e03030004145100760444d24608828980e4030300d5041e100354100641101c0111f8810b0030184e80e40c110b00c60540b100321030460000714000b0010386607141001c1900d03001030045c5008507801e074950360310f0281511502015516588900700d04241c520f01700302508100c1c441640c041d03080600c0c40e91a03075510140a0030040604100e030340020303100640c07941a00e1604040340b80c03c051072844c07118021881c140c1004141e0042c081d1003c0001294000d07000c8528050f0b1041c1142050341d24901c807a458600080e000004600074100511910011400a05007042c025440b0b00102450541010700316200c0c0c40103041094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 906142607 1250 906141357 906141403
    0x1110a080f0c070f21030c0e01200d030905060903030118270302060a0501290c2b0813020d0305181009050f100503060d1b030c06030b190b280c0203 65
    0x20b50040a48c081c001c42801d0805055240c0202d5184414100c81c0f4103040340310f07810542062070303071640142c0c240301e00031403e56686031107414105403031b48004d000e08502c0b8611402c404495418036400081d203803001000820500d106864504d050b040f00c0c0e9000d5006a006a040c816400d00d20310849004040b61110a690502603d01c6006071401d038420f4546554004622040c0d0510700b8441302205100400e64000c00105000f98681c0d8008050342013070010340d02e00c2c00208640e1101240c044500e4005142960b401e515503000c540c90350001622802d80864000c443c0810348899018062454060701d0b210180c500307040900100e05400d2502074840c861700790807061317141d8100040301d070402d80940e60400c518171913003403841a82141c90448484100240d000005000e80460640155001035906211280360081000905201c101c5d026084107649101041858050002801c0031099172424249500c0c25010a03403034454401c54441c041481d03a800744007146014404143c0e4080c424031441461 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 906143857 1250 906142607 906142631
    0x60c060c0309210215010b0a0909060b09131e0507110309130b01140307021507020c0a0603051005060304060515060408061b0408100b0301110a080f0c070f2103 70
    0x542200001d58180380c0b42c004900a8910a12400020b14404101e800c06540d5a4280e5440d0358020a200030000b805a10b020660b14112f005510442c1c1d41241020700b00f143c60010019880b2088503510800d6507a5174a181d02c002c9106101c50300d0241244000800345050b010103800c14680c0c00401302240c00c1004138403440e64580d440d211640c00c1d08240014410106001070b2040c608011140200c1240402081180c9900144510034640c0c9000d40c05c3c001d0711041c00c2a40d4403500005080d5011284003802c5c00428800d030321150340204c8011040c0600c590b01d1021174071590013034805403940390705e40c020070064070804c0c0c0c8684ca62140c20b6425078545450100b8182e2129000b41002c0d240c020804500c603030b41d40b408000ea60150080e0300a45000c5020081c55000418035801d00e0742c006d508140940a0790030311982940c07007820503511446010b40e01c80006075503025004040c800420750911407072011030b81124000c01d650703106c0c015003650000003203503594152500c82003450416081840400320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 906145107 1250 906143857 906143873
    0x25020109120318061a090901150506040e0403030c05220f05090c0a300509120408031206041803050d06210209330103060f05090105100e0901060c060c0309 68
    0xa607940004d400910040e03003942d0805282c8400014a5004a000e01401071802041d409040c1c142c0003074426507201b0780d81d42c0a00116019601c605032850045c0300004010a000360414003c000c038034071707089180c41c13440d010b80c016000c0346c4000c0d2602c03481a61070038000d05070384c841230f00302030002216210218079110403a800148100004541000459070074442044052208204409201e590320680502944000d0000700701c01c45a840e824413941c10241000c04000301100d00740c82d18240550300d02032002d0512060007001070b01090b0000d07540c079440c00c0c8100c081011320b58413622030360321199140202400c0d8410b0780c03203d0b0004c03c2840b0050144a024402c05540c40740400d45c19148004c55a80d24029480b0006103840d004a5000c1036002015003c07844881401c00544240c032f0070890b1580304c800320310303003006c0500070380f07811800c0d51005221030f1409851401c160b95151402c82d8800707044501103240d0320780aa01100104100b08041000c204c01030180440928607450100701c4c005094a030b07184 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 906146357 1250 906145107 906145151
    0x15080c0607030c0f0812060112050402060910090b03010306020c0607030e03180613060206090f07150c0f0611070606082413020d0813060801031703250201091203 71
    0x2c14000d0f4802c983c000c208a5240d008201a00001c409854841d0001170b00f46460b8111403072030002d031400c41e5400e01d01046110703140c003840d0098402d608186000701072000c00b6075208008010300c0801000010349081d0040114043d5200300009a280c12075070302c0080c82c0c072102030450814107041c04680c02c3d0300345000003074500c209400203003001050f281c0c401050551040c102c0102d5110048007010640680019140c0e025400d20412545801510a40580c41d0740351400f400200b0f28401c046d44103d28032445480e106180254600307400301105507101d40890b1003a5444480103a00400c42c2c405102e9036200d007000402280003e4020085805c04c0480c0c000520721351100046210360103ea24420542200410300b68003a0800303400d98040e080881161b08801c51f1100c2010002c1c1002c1605031103401c1c9603040b60343c44003869004440c000c014240c1c94000a11035800f0103070940d006205401c60155003512424203400008010200303080c1250700e003034120f079144241804c0901d4031030b501c07a090002c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 906147607 1250 906146357 906146363
    0x152703150a0f0b1903020a050d170a140a2102030c0316030204080718060b0c061503030d050f0a14150d17030c130812090d0614070315080c0607 63
    0x40c104020346111001040e0070403c403a080500d51829110049521a0740d030283da0003111030b240e159981d282003051135000350800404450820000e5480402c192020f01001855030410102c04032100d54441d01c1c5802c901742c0400000c0b407013000300e0200603500c050101030880a401c203620754a8030544640040c030000c0c0c9601c2281c41c149410b010340074800c0d8190b0700506642c03420784110950741c06e07411504105100fa038196a600e030a9001412211140858601d80d1a000140c101903a41041461140b000d60f040c2a41600080024525400e003500c2102e10a1051a0001040e400c004041008849004c41140120100c080c144130b07201302400c8041c40701385006c50708481c44490a107055509070065002e0081e40d03940101c1440000c001c3e0300c014101d8546844040416541c0e41c103002c5a81d601c14100b00c65513141d0030400310405040c26001c0c0c200c40c500803140407070440070b03c0036040d518070803c94036080020740c0c40945840d01e58580642100414850300100f10001c1844000b40c000c0c805c0c20401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 906148857 1250 906147607 906147611
    0x63012160b063f0105010f080132040c0306050c0a030b01090303201203010b0a0f022a06130303020303061008061c0c08030703120e1515152703150a 65
    0x900390743d40c0408200000100000081c8125651802e01d0824035145026100c1d895080034805404038102a8094601c1c040d1f4056202c07440201141c6203902d80c4002d44140c80200000b0307400b00c003047c0f00307024090003078001c2c408095032461508401421912080015810003444140800209502c241aa100f001041c0c0c0ea095051540444c0d051400c0c04010440304011b0340807000080c025555009000195040e8864101d1450821000c9841e10318500780074285942c1e2000070410881c140700848054000a001e25251400011a81c020002554411801603000004116803414001882c02c4c0e00b01250a0010107818408001002100303840101e02a44098560302014001d26070b84120082081038152540c4070401d04005003980109004c2c1c014240c2061a00d40ba044800286540032180f8104140d0741902c0c4c00e0030400405550004003903000c01d2070f07030300080414014402007103103010120b007561000c080070301c1c016240400c4172151446900319904500c00050004055648003102c1a40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 906150107 1250 906148857 906148939
    0x19182f04200d0e1e070803130b03060d081201141e090c04050d080c120a0f1202270a05060702100302160b180105063012160b06 56
    0x2d0b0400408070084098464401d01800710340b2001a00240f40c0002c50311001e0312001500d0b120041e690f403046414090052003075000c02c2202005e100080d42d0440c0005100c2c0c800c41e02962980c81281e04030094080280d00094010007002020b05200314240206545801c05140c44040005150001c2148940201d05107000620b5100d07034901110040c01e03006040c16207030b040700e0030b00c0f0140d038100d041011030910808210541e4101110199001150250382e50721401d680020100ca01d402c1784040e004c0e505400340186078011074009503a840c0e20300e0003200e200a00306450100302c6200655031003d4010081045600056203800ca800403400c4280e041c0540e69014040c031212180080d03c4000c1e100d900c04205009420b05031b0742101e086020000000c0c403032910303a04100240302118828241107418004a00302d210700e03004d9545040c0e580b100e4162852500c0180d6080c14680c001c90703284403101d40c000313448070030802c52841c0a90081da0070750700303075032203914a0b0200040780740700c02003516040d482c01c50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 906151357 1250 906150107 906150127
    0x6031808180307061205090102090a03110d1e050c040b0312030c1e03060906010306060503070f0905092802040501050301090b040b210c0919182f0420 66
    0x1c0407541589000e01216007040d03468030020304a62019444c80c3c0c40c42e040002007181607405000b507032141e08000b0f161010407859651042010091800283e130030081c00240c5002140002c20040c552196081c04001140034520304281088610354040744200c1c5044200101c80e10006152207029601e4441c03540da0342c030f0700e4690001c1030003000404241e21803640a044440111440614060002502c5134403a0342c940074019030948101c0c0c011000010700038800120a00e114031003490420030113082100d040c0d40c0721000b180c4101c4007112900c25001c0c6170b0310080380718400d40310403900c01c0c00802c00c03c60030582010b0000304144030602c206050551608845a500d554a6200082c080e100900401d003208141c030580c100814035001d0003002d0b001d1206030f000300d414000c5d000c5108291020400380c80d01d04400e191030040040c0d03e180442440102c40350340c0043d001090003580000c49004100c0645040c15503c000507103801c1c0301901850401c0043c080c444594240c0c040e1000101400c1511494800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 906152607 1250 906151357 906151387
    0x100507091805240a09090318050607030806061b01180201110601080316020a0b180a0602010921140a0503090607030e0a030806240301080114130f0318090b04050106031808 75
    0x5084504403628080d070362010160002d0100c410301c23504070805180c5e85d0796002008a01d00070b004019000c207a44200040e42d0703103013110040491032000340b00315426103800c800c0c26003102e4401c0c80d031082d00f020701032a000942d0382181100b80d4010200300240741660410b41c00544074090f80e40c60501d8030070031500741c004550b40d1000100141c1000f50209880d210b1070019080f201c804003400c180208001c0802180580c818010410115000b9285586454030140c8201c00c6800c0090141e041001032552044040c0c4588004d107000b01d8a41c1d038a980342c2c10b090030124184035020780520241490310021540421021800845440c5c00d418400440c3c0c0c2c0e00804941000310310030030180405d100502c410841385400380134605a9a40b90000c02807030001041c04108064207a42d40360780c510010794000001400008441c01485c0b082c81c244039050801c03202c0b90031005140d00501c00080d100c006503c4e5a040c14410140146070b40e203800e00450946810015900c43c2c0a580505801800a80310320107a00318 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 906153857 1250 906152607 906152609
    0xf0e0c03061e040219020307031d0f060913050103140c0901060c0813080304060c1e0f080309070801090b010611060106050d0c0203040506041e14030607080405100507091805240a 78
    0x1740b8000d54402c00d0b80310007510380c1d01130b1030300706d0208d04880c140400d01e0441540c8902c000c0c1003d081202d01960520030070074250842d0032510b600c0a40180084000e4066001d402d0086100e00d000c588100b510000c0642450130440300f050040341086c004118680d0302441e0000d66540014803c0da4402c07a000614507040360f1070704103102d13600c00002c0c00699170364882ca14002d214018030801e07080e41c40c3d000000d02e401d8003180c0054082c0070000550302c0171901e032400450700040600d00701e42c0481d54455100d425035000d00016a10358a400004105040e0401401e03030b014445032000c2c00c419810200058071078001c4a8016442584e512b880001a600800495014100040016803900e944196400210004007131482c0f400c2039440300086d0000103101e000c02d21100040152070030f039841c4542110000401002a1881e204400140c80c0c0c04c80280328190050408e641c81d914100e0134500360301c4e800c00e114500811003d140c0030420113050a000c1d0791001002e4441340040002a1400c00104d00e01c1407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 906155107 1250 906153857 906153877
    0x31e0e0301090b01090c030b060f0a300e030a080a020d0603080705070312080c092b0f0203011803020a060c0c021914040e2d03040f0e0c03061e0402 65
    0x2801000700d09011183c0c00c814103c0303140800c01d00030400c00d0003048081d642c00212868012030244885e542d2000341d1005415141c1e61403419041401010100c05135400e2034a000101d44188440400e41c4e50000d8001c184441c04500001d5140100b494802401c01800611064440d540420784070041d81050700010019500704803019100c0001d401c1042d02d414592004450010400d1044001d42d401145800c0c49031442c005128180204082070100200401c0846ca09860180070540c281c00105035641d00864004c03042e00c8446040c510516084401c071100c101e0207080004180d0740000c0d4001102550701e42d10040200d40c000000109561a4544107070007035102948110058280309042c560504990141446118840f0007000340b000f210504200c0310341c42c1c0c0040c10312440c980b0340034094801e2018500c040740d00d1080b4400700d15040d60050b0304200700071101c22004200f0709500a1181da000402000c81031301d10b051550001d0703494814511401208816074a144c00590b03145d505484042807 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 906156357 1250 906155107 906155111
    0x81317070503031e1b0d06240215100519051f1b02210c040e030a020c0604080601050111010f050708040209090d0f030216020d0501090b0f04031e0e0301 67
    0x403034505151039030001c480b08840d51003044d807200100c81c0f9628000f8040c2c04000f00005100b0f403256000091a4001c401500b101d5803100c10015012440c1c0f03001c80e030b440013140c0201541c00382400340242802204241d016900100c4403e1010465943e02454100c503811580900960140d0080800000756136004543c0282100903d000c05803800224101c0001d503940e84494401f040c104e1820450102440039410148101c9a880c21062000540140000c2e100440e01d0344408030700090b00b43c90a503900c04095800110310007418680410260380e202c01d048800c14103041c1070940c1c0c55960001441218104001c011031128a031500b94400d00010402410501c441d01e8a000d02030b003402c0040ea8124020f02040002680d040782c08100c4030b94100340c40c0d0341d10031410076034103086003e07401c062091030341000d08858490069549030389401095105000106502c5040c0c03c2c15000c00f4401003074655200012000c11000a501c00501d00c0c00300b14114021550064009007141d00080c4d0248883e0958 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 906157607 1250 906156357 906156367
    0x307030611070b0c0f2515020c0c010c050319140301030606061409030a03080903040e010e07111b0d03030b221104050d112220040303081317 62
    0x7019070307401801e1060050403451455210309034803503040c2c4610102d0703034a264014020301d000245a1600c1658444100440000d100350303036219035580c01044641030309210341c000381080070329100f480b4a000c2d20209003424084810303d601c455031207228008407002090011412260400d00a0001021086c00100d280703480390b0b1280740c480c3c000c04290280401150012141c444141c80d03480864600c1c110190103030142c441c40f1b07541580d500c0400303401184075020600010403158000743c8a01c1c001c03d20150410b00c43d08004402401c1900030022400d002e0300b040d01c80c402079107110070180700c1c2440142c0c0ca02c10141140e0a08800410488141c507510000183c1d001c410012252520241b03890307259420002c0c2100300c9414620751141c3e224403500522048120004211248042e458803c4050030003528001a240d0411032107090341142209a5552042d078001340341071a41600328803140d40300840ca0542147c4025091441c010150b007044c40782c500d4003104100010300307a04400148071000940712 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 906158857 1250 906157607 906157631
    0xa11070803120105060304151d0a0809100905061b010f06120b1f03060b040e07060c120207031a070c02150a03050606210901061e150906020309040b03070306 69
    0x39800204628800801080003044c285000e004590160380d000c00f05c1e00402d003d620a50b405000401c0c0280444008444c40c480c007603a061140780300d80c512850301250785400d15410000d203071407441045410096103520500003030300c40a0844a943c10078806660500070ba611005024000c9070f004980440d050803c00a129241900c551050511512055a0b90758607101c1c081d10022003100d4000101c14541d204001281c0c89034401508048007030700100307010211541c1a45404240ea01c244000381e050b454220910107006030b0006038058a2010303103030461850306c400305982d0340e40e40c1103c1101c0c140c4004c611490f000306d1f42d40c20283c2d400390030000651401c8184900e03940040b401900402c2c18200047c2251a0003021180040f0350220301c4008090100d540c508001d078002e01d83c44c1c00d9941c030310300403c02d2400004200041a591114405610f0500111001103840000c2c1c0d43c0502c80d4800062000301e80102c01ea512280c015100054001c6801e00042e241c01c10300c0e400074105030325110540ca09 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 906160107 1250 906158857 906158863
    0x3021f0b0a060305011d190f150f0317030708010614090a0e010503070f0f03111315090f0203130201050f21040c06140d0f270506010504110f0a110708 66
    0x12250a5141c0e0f03021811210a2240d1000003214031082d5480060201080d10711681c1c0200301808d41e40100094800e865011211510040e41000c0310980d6003540c00c004100b0400722010000d118010340a04500740640d01810f071000601034101803204010310340c8081d142d00f000395003502100409021110b03543c3c01c0c10f50903200c82801024002d0013518408102d0762201001c00003151290680d102401e480e40e12080c2c1c00c005021039495104641c00c070340c21042c0c0d41c43d01500c41000e000e8565440c4061611038070404a4680700d400e080b503113006004104045455400c2840d0907602030030700560f542010394003040c03244211660204010f502010301c414200503850028032883c401d0000f1000181c07a00c03070968500c2e0074001c1d0102282c0e0300700802c1d05403510542202030000e02c9860041003100e403079510204030aa02d100a80821042d0742c0510b400e1000130014140141025202006a000000d6114906104050500c1d2014034001004990940700d09110b540c02c4504005480c82d007602c2c2c40546403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 906161357 1250 906160107 906160109
    0x4091107050d0c0809091b270102070b07061a031609140903030406050405031b07030b010b0c03030a0902030a08032406030c0403110307030b040c230a060e010c0503031306060b0703021f0b0a06030501 87
    0x2121761888e01d40003400794000940c040654138035501d80380c02c3ca1307820786d12080500000002c47d07018042500e40c0c0c044a403002c00016103811124040d40e407002d8141101441201c49050300442090005018040318003008421a40c019401081c0450181c0d2103040040c0380d4842d0310744084240047c3c4403100c00500d004280340302680c1c80b0740304480c0b050741d85211204040c003440c1c82c5c1c449107800800102e55003000035440b02943c08c0c4040e058518201158840c850301d904229840084122080049080131464119074101c81800301c6a00e801d5007000c0c11000c20b140200c2c00000c040d882c45206445043e9020003501c0011640400c44240c0380c41d05260203014508030707120703a0010381d1801c0f1303504801008510b030340500000c0252495403a00d103401d404a5100e11030401c0a4103101c3d4406000000c075030180021131256181d0840e05018100a01c2d01e54100c5070b40c2da002041107001031140c0c60000c2e601044000b0114545000440c0481015a048006010904445030b000c0c00c000400140c0c0c075090707003040b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 906162607 1250 906161357 906161407
    0x1090606020f0f0c01110a0b0c04081c09050d0629100306030b04020d06092109050303120c280e0a09050f0f07020304091107050d0c0809091b 62
    0x2d602d41c40000842e60b50740661680000e4035400440b44c60b0031070351045400d540d1190340101103642c80700282d1110700040d00c09441c1c4105035000041c00b80040c1c7d80070407201c0d61084000c0c60300701180080d0100109021510f00820384150f500c0241c00b8103001058004140490301b42c422041e04210003d0817514040d10f001c0e09a008080b00358003121824001d20401e03089a4001e510270100d980c85c0d40c2000b181c0c1c5070703050040780c020766502910004134511107503440d03c26820810000e4480d00c0c0403000b82c17074040e10740e00c5a40f00764010040f174800003404082d200c1e00305030740b0758501c0e898101c080b180700e1901c00c4000380804008408051500d45aa000c8281d4803044801e542c89400350781c640c080c035825524206c80079011030b1409004038010514100380f049d44216544180e80c02c1c81e44908030203040d44d805003011640a8408520b00d001e00500744410a0003419906051035442520b81d281d0f00540182e590032481104c01100142c1c0c5500d00780406d4250400c0c41c00031580c0c43004030310100030351081502409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 906163857 1250 906162607 906162613
    0x40b04021305091f0b031915081e10110c16050109050d11130b041a0a0603060f0b0f04030606090911040b0f09040204140f0403140f071401090b0109060602 68
    0x220b203074200504c60403007902d2a240300e01d2040506145100c54154000340545482d280800d00c81c1c07260013914031035051851406840e41900d1482c041800b032074100b10742c217034440820340c0c020000b08000000400000040560078041030010210b4415152409000e0b400407940c041e20f0200d642c840250f40079801610826220401d10035120800d010381c403031080000030800101603145449518001c0403424105400c008082100c000c0c080106059030343c42e01c00310140030700703030710442c82586045681035016140b9490f040081510f0030255200e00d0382a40b107082448400040c4e42d8228100840840b030103107030050380520a642d40c41150100401000c001911514450707881041c0d64900742c0690007003582c00501c59090300c00b080041112820700a40708903802952030110050340a046400e00f0710030202020209414030b028200a040e40040800b40e12070303c501001445031700400c40c4241c034652600480f001c0c0000b00e03d07259441c0100161100903140750a00d600004208182e90001415120b1030350039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 906165107 1250 906163857 906163861
    0x504050907152007060c0f020f120d08060904050706120608010513050d02150a18050109050102071a0103170307050d05012d180b0d0f0507090b030604170306040b0402130509 76
    0xf480d1510620302034400010503240014010030282c0c0310000049000901c0c40106030b0b4030300c0c001424081d920150000580040c0e00c5103180c0c60700840315603400b01050750441524500342da03405e9164141030180e4414400d4050116402eaa03003036102a01900320382d0020021070074210700e078980030620040200c443c0d210390680600060300c0400d000c5060b04203150070000c1c3e070b00c0ba40c180c0c1c00540065806a140351885101000100340e09000350ba031007600420005a44461508210b600e0300700000340050740341c1402004100007410000d00150b1000990002e54032034807944d00407901d034400c5038405d405907400c1c14008540b0962140315448151002080800c0000c2090815041e11519100d0003003889100c01804090030346a03081140f2401c001801c000c2440840d55a2030024010200c0550300c9600912040c050000c1c688522640e07000100c004184905e03059683c0e848191030f04041a00c001c0b00440852556240c036004002c0704c0400900a41d101c424954003400c0d08a1940700c1e1900c01e59100300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 906166357 1250 906165107 906165167
    0x61d1e0405011b182106050a1418100f021902070f17120f07050615130513020111120c030d0b010507030203040b030403050f031305010c05090604050405090715 70
    0x5a0340303071555002c0d81e014480780317030194004141803151184009046050081d20001c2c03900d1043c98400c8190000024a801c40500012501d4074020024450301807030407806040e9500004283c403070a500403d020520206a150160280c0a01c01040c0f401c03d069452071211a5000b0800034182c50f0604030620074907030341d001c02d8140c401c2c82048042c00c1e5000360842c04204101503004245202d451a07002d864000715581c0d1900c0c10701c040f00c00448035046c4802070356492038a10b031407803c0081c1000b014402800c01c1801d208283c0c0312031200074180400e01c204810b10800c1031140c03c03020325441030300c9074951488640307158032903112203003004520f481c100c0d00341c0096002e1000d036042140c059009500b003504010680146510240c415014000305006040103103100c900114407580301401090303911485458118290f0340e03030118500c00e0080602c00e071030382da403603441c1681c045440858001c680ca4807909441d03410102c681d0840003e8401d0b4105501502da04450380d001c50b0411a565a81014000d403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 906167607 1250 906166357 906166367
    0x80307110f28060e03030f09100b060906090a09061203110f1203041502070c09050604200d0209030d0f080702030313030806010e040905010c020c04061d1e0405011b 72
    0xa0040509014094402c06204a50121210300340784901000a850412401d49600d160021078060015800400030804450018004014059030031002840020454000507580b07028401c40c1c0c500a810200304081c2595038034160500034104464200400390711161035108003100c4c900b06901154401c03d004035980c0c070001b10704000c031001170041d041e8081c41300e80d201c5d520f90001d0002d8401c02140400070102c103910f403008280c094850b07505604520714120113003013915801041ea910507440c050240c4c0102c0154848401800c1034917030318079620320040750414000c1c000c840d0399503054840c4161032040b66410141103040848251200d12580e603c060b003ca0b42c3e44400c5075031494000c4041c0c101c8000901600586070002414189440507030940e1000c102218108981070308c031603441d148603002c402e4040c460090750303201c159024481e4604004031301809140b000e8034081d2000e40c150000d843c11400d42c400b2000381c800d240110030076080c9401d02d64040c040201706002d822078154009203c040c011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 906168857 1250 906167607 906167623
    0x20d0b060705060c070507080d05030601031a01020c060d0603350a051c1d060103030801060e1c03020712050303010f0509091504080904020a0302040915060203160c03080307110f 78
    0x11004041d44e030f441c810103068680007400c084456100b5840c01041e245421b208001c420003c2c1da556503124034200000606035010520900140e1001c04400c003001d0740c0c049292501802d0503103201d6034071030240302c0c528001c103015403019040c194010368000828941c5400741c0c444c0084070300d8103510b031f4007507041d003983d035100c1c407078959010403401c2040c448198254242d400030390036460700000700c1c0c9a417000c00606c030100c0c004401580d40c020030b0041c801c043d003000d2202c0c0500032500c2c1244156080b1004141d445821101501c04901e45410395030405108115090140c0007a81c982c0c101c44403946801c80d03a81e0005e010b070b45c00104541d900482c42d404d262244a02c1102c60b00020100207060030b4003c2c86008000e003080c0c1d81c042081105c03480b03a8a50b8001410701c1401654010780c0c0314502600b034000c444441c080721842003041001046459400020b036504182a100340181085c1c0b1807810035a690b03e60351000309501d4001c020003100030740044200c2c55801400056810509009024584501130 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 906170107 1250 906168857 906168863
    0x301a040c0503070c2306090106171203180313080d0f050f03090124050f06070b18102313022b061a12240402041d01020d0b0607 56
    0x800d10003c1c021501c40c001c0498083c0c013500000c6a0040701d6002c0c0a80b000300382c41c203100181c3c8a001403011340c0c00244508001406a540c01414805d0540c1a03280c8032100c3c200050310b07008005c404a1a44000316a00b0070242580d0b10449648509641e9100840c1d0074620404d95180119000c080003540074641407150041c950792864944011503400301d840d900003801003a10380d036841c1c904842c0603480880008589400701c00d4807542a00d07010802400074008002c041c007034002030250400280c00c080b00c15410200d403401064038603040c140090b15114001d040850220308000301d0b482e019842802d00700000340d0010102003680d850041c1000000d410841c025002401d04009080741703d010394151f900210250b042c0e030444002e907143d003002e850522481000c01c41c00c10b0403070015031800701440180b920f0203a014002d4140c181c806d8115400007502e020344001d5034003001904655450f400000300861908800c1c0050f030350382c3c4665000350080f1400044003843e2030a003614500d000e0b4240d03811035034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 906171357 1250 906170107 906170117
    0x501060f09091b120e1605100e09040f02030f031603030c2c0303040e09060f1612050612100c110c0d0f080405150d0f0c0e01301a040c 59
    0x28a81c08a603a20b407040c0c2c13503080e03083e600e00750001a09020b00c1a8000c00c1d14a500d040c42090a0404001c9018181240c00042c0314002000907100e072901c11030b2562064000072119010111800841c1c00c107900341c01002014000010391000061100e4082000140a07a07801c1080c1c40c940d03203050704c00b00054080341008dc266045140303804905110020078641002c0c095a041654814440f00200d4054a000100e90403141c2006a200402402c56034442c0307005e5084071003000d400300060502c4410305988034480d80c4a0000480540740e2041020442c50b000701100c814954005140f40180008040407000030445548032084010000307482c0007004006029011100f507507a186001005600001c42c4e8122041c00002110703521000306c20a4521503030b013225600c0700342c1e55000040310b07452064240b900d032500030120b81455008024a1090000303003002d101441c2c0c0e0b00055400d090000b500c4100184031218260b4000109403c040800c5a041c482d20b5200784510003000190b038007030688880010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 906172607 1250 906171357 906171401
    0x30f0b160e0d12031b030b1315120804030f080d050108060108250305010207240203040b0a021804020a0f020f0102070b13150c0906080a0506060f0901120501060f0909 73
    0xb0300c1c509003091032051103040c0010400071503402d2009900d1260022808256207000111f282d041c21542149501c0d0041806c0011301c00038500301c03181c082a40114514160700306c4c1110204400c490440740507580010500c3c0f80d00e161498514030b1076000c203200070700c11828040009022040080c0b0b060680b003000001d0300d55508285c2038462603848500451401614514002001c03900a2005102444c00741088014049403400c001c4c40f001c01c1c500c610f40da03d600c10010000440d075460400c81d00000020400750752460b04004201c1c4110b01140760f250300510020b0441d00c0c55400142c0362610030305503020b940101020b00c00e52801c0340078002e40500780607410380020f01046c5440500f42d2334a803103078016801c1c400d80c00b004907080f9a510b1840c3d4011070f4459505102c00c41e0095a01940001c11040c02d02803403a08002045060003080001030000724046945840d80e80501035a201c3c104000100b0842d0b903940d104c00501543c42c070740648003ca09600b40200b500e503160b005003444a04800700da10409 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 906173857 1250 906172607 906172613
    0x90c170c04061401111e06040b091f02220b0307021018110102071206140a09020a0e10081603020f010504150e0d1a010801150501020c0603040507030f0b160e0d 70
    0x5090070b080007016a001d20100300321080200c141c1e02c000a0401c0000b000c1f00e03d05450030140803000070b01004c1050b40310107044a0889880c4040300d1b44010412409a22000302016001108000f045c8080002c00e54042c045030b801311000156100c1c1506a08882d020f030103c412020480b04082d0403800d14800f0118076002281540141d03503000b4106204842100741d4440d501c064100401c50704440050f150b1035013007141d00351a003409170401d0b100c2c0300400c407050b01c56000900c4203507640714802a003040400000d24441e5040501c2e801068034030151605840741e14030540d40c02d003041c00200c2c030409408a1001d0030f544100705440a60715000c1011341d00c101298020f49955066100b00f6a11000140c0d481001568041d0b80381000007040300e0107421541400406401e54200340303211198142c0d1040c003000142c1e4001a2000061016605540d4a80312400e00c141880501e4002070710442c0800c0c502030400012041540c8a400030f031080c040c04244c414070884007400310440300c55100d0f052000078004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 906175107 1250 906173857 906173867
    0x903090f0e042303031003030221030f060105090d0605160512010b030c1c0506181e06030309091626150316060512090c0a1701090c170c04061401 64
    0x600440f5000100c0c4442406000c2c0d2031548110b410f486400b040400400402d9010400001d1494016940c01e500251905284540d80001410a154028180c002c03030040c1c0d0041007140c2da07102e40a0524400a40d02c0d05001c0c02504096420f0000514030113000e0500501c541309492090304101011451130b460154000c030540c01c040d0a400002c1020450203540071000c81303054640f185d0148010503180b40007000c02c0b00c014442c042c1384098042080030403040d079116034a140224000303400c0626003070b10b0f1100071078610b004040550f40c00070b001d1010f10100440b6400355005654207aa1405900f04a0040d001c03215808100c05100f4241e803d804180c0144444c1c0460040c20000b030b084680d5002e171101c480c0340d03401541d030007030010800010703040c2c42c1d410f00e001c642544070034407100a24202407403002141c00c5000c075108048440250103040784203404203411024005800c0220700d03410584802040301d008280152a44941c4540c2c214068182014001c0d0070413039540e4141148003104c1c500056035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 906176357 1250 906175107 906175133
    0x2090a030f03022a0f01110721020310062303060a092109180207050a030507151a0a0e10140f090924191d100903090f0e04 54
    0x400e50040c11a104c191a000c500405040100e24a48029150740c0c90144036960103a40291342c1000070184560100c02c000040400446032801c0107610a90440c2c61081155101010000d5140c0100036104000400a801c01e10a032440524540c070803100c203001c84003408500800d26601a040308002640040c21540400c81c3c2c0c1c1d000d00710804005240851000c101601d04070b0700004240b19a03420302040310383e00300140510390fa0031000c6203000c01c15103401e581c60070b50311030090410000140c064100500c0014607443e224064509000540440b80c2c04040309891942032802100800d000084840b0001c040e203010b12501040a00b420b07060400d103050b01c00384c400f04030f60060380301c0c01103000a889600d4424450340082000d8442100c510008002c480d000c0045801204010000c1c0151031002c0754280c800e4400c1010009035001d100e15186900900105070a0b8050042c004101503c100ea90400c610845c820b03600e024002e515810200102001c0b80030764206208200c00103400104400c40c80701d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 906177607 1250 906176357 906176363
    0x21030516270b0d09060b011103070206030612330c09040f0209100c0b09010209090130050f0d140a0309080409020f0c100203010e06010c031e030c090902090a030f 71
    0x128080d15860090096403058101d50043c50b500d03012002800710920800140140c03d203010201c00900c015034030368900851a02034070859000021805c280d480e40082d40c03072000707448241c40c0e0720245184001c0c503914005103e02c00c91076052241624a40d400d421003413041c005081c4490070301d038140302440020041000703d5a24150308004d00c1d00d141e40c5d05800c000d200150307692040304074241031824926508010300b18140d160b005009242c410fa070b0360700c04a4151268142c0a1000c0311007100c00c0e030303400c1c0c02a080c0c180301031140181007801d010012400f8424070038410200e5581090284040300c0c1c50401000700c8100150078000c1ca1180c030311036081216164081c86c4840e080c1921501010b0807680085944200c0c414006001c03000c40310305000d0f203c2012a019021410342d17260201d0300c1c02e80200105034604210481c1a0b100400d40a41203444911811003501001c00703880d0040035000b000e100756043c000c5032100c2e0380014004454000c484001c18003804100d0031b240346139212406080c0c0c00d0380803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 906178857 1250 906177607 906177677
    0x10c020a1a040213050c0c070f030c0612060e0112110f03060c090a0e131403030c0306010809030c12091201090c0501050a021e031b06270a21030516 65
    0x401465140b0f4010311b400b5542001c1c10543d110785810318103162407141c0d031000c030740d29070308420400100b000c01215804075099810400d40100e8103801c1035005240c5c0750020300009203104004112161110401c45016108001445d6401d4100c020462402c901481c4103130300d50300c441c0014982d12000301c0a000400c0c4003600c00e02201d0744401d00400c2812084600b0f84d1100301e2070303c240040c00b48100c0e0544070101c0070005585541822101c00c030b15031100401780c505000014001c00d4103c4410000c8840a0f01c0ea441911005125403001c1480e03540b02c1941e50307210381a0001a40c2c017100c01841080f04055006652403070383e0386004010341d10303504001d8000095014030b03504070200d9101a480710080040410195030360b107c140828482641401101445541c0650308105080c44c0d689803c450030401d20460840702d5041030286450400720700401080ca00310f0245000704010700000c00c46601f225a00e0030b0000ea5a10548218212220303003468002070040c1c1001e0761010612100d2000400c050160 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 906180107 1250 906178857 906178879
    0x1b080a120603320c010509010c1e03030506150d1a1203090109090e0607210204030305090f04050f130309030b010b120c030c071407170f010c020a1a0402 67
    0x40a04494540d03106440249800d15001140220070440d0f03100d948803101200d1940d1143c29007240e0b01d00c0c50358051818404000b60780c403400d0780a040e0841074258000070b00c1107200d20a403200f000007218480c00314046414036010803ca0319241e000c0391034040070980c0c5207081007010f04031a00500020300410403086500a420b20340350311074181244007640d060000310f03074448000303000600041280d440700c040a45450b5402d4602a4007081d503a400014915000101d81d102c190740d6600300544805440d8020720011340001015003100c040c0048240854003403441c4145142440182e6030200c0d01c00c00284001c100150181440d801d03c041454001d2600c00b41c620307242d50710400b4510007a049442c0540c0041060704903034907011071880e84a018210b8440c1141440042100b00d03000e80da00c002e203100f80100c1ea440c1262000c100c1c40f070003401d60b003141d82c0118170b03c803110130b454000706a00c141155007000d1200c0c105c00e00004a0b400820790003040b5500303040120300840341e655009041283c0c81003485070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 906181357 1250 906180107 906180137
    0xc02030a17220f140c0d0201051c020c0c040b04140718030b012301020d050d0e01021207030b01020f0118021201090605090115120c06082a04030b0105011b080a 70
    0x200c602140d108003003d0601d4081404c0821400e0f80c542d0825100c0e92101000340580c0c3c954400000009078282401902c442d9421441381d40046828141c001d0103101041c204440c3c24002000030202106440030000c0f02060000d000035a03800c0c010b0980364005180101e00c0b1a44201a1a4001441003d400744082d45a81c1d075405608020781c0320008003441e17200000190452121100c0c4642424001800d640c1107001016080d0702605004002c0d1540da0b040c03d442072030080d011540717602c144440980700c40c90856400380c01445811071aa00500c903400d0341d00071000051040040c0348000d01960006107038668208402410b541072809840e548034460200082c4560152038081c50400f80086004000120100c10b4142242d00440308042503510503030200c4c28541440090b40c1b01490700b00c90329074503058201116101002000d0501c1459036210080810980c007900c1620721030540344080341d90701e600456001c03600e02c1040514810706810600014007510052500d00786a082c02282c11010f02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 906182607 1250 906181357 906181411
    0x801020a03090c0905190506041d0f0f030310050d1a0a0b04150b0f0a0306080a05011a0105071101080a0f060e060a0e041a07050f0406020c040c02030a17 67
    0x1600d0007080c2c07249041410024a0340d61940038003c0c148081089180280c6040c520341110348000103029501d5000c10381c252126000610036107041c90355070b03005410100c07805e03954200d1a035625440f4004c0040c0d1071492803021044a004044104146617400e0a19041010580403070a003220461400710081c0d01c1004001d400c02d12448440900043e51940a414442600c0039805082c409441081090007400c170702c202980c0640f0740b800c49036a1204070034a0160f0040c0640c0e0011003d0303100c0c48800f401004015049004208000786549424402d000010741c0c0301d000e1808002c10036140d03a582d40c036a95101e80319195100c4c1004101080807100c2880840440304c4a410400c0200310b074000300100c5050805004005003454146d249152409440d0703418140c5400c2d13611201c2c1c00768400891116441041900c9d0700d918050351980c1d41d41d80c1e07190040d507542000e0310124096405c0500d1900454004416541d141d5255112802c0003a800d0380c010510140040079441d0100c40441c1202c81124a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 906183857 1250 906182607 906182617
    0x90a0306051f0b0301230d020a030b220f030f090f0b0a3c050c1006091a22020705150403080a06050f0108091e0d1206030c0b09010504080102 62
    0x300075501c0342404030b51100d01111071aa001105081c0040004120320380d00780100b90040f00d022402070400317000c1c4100094150141d4a006584480d000201000b030045e000362507030085c03428800c036400418200f00d08520b15410f030300020f8403001d040310030070011900468501450340c159260419202e40c440205040c11007050f0410707402c60b440071411100e0181c0100001a401c001d11050001c2540c03070f110f1403403010382c0c43c480d10840c0c08820b100f0302400c28004d42c190703030b0b4001c5484e0540e14011800024000102454407600250a042003801d210304201058040070014000d00280b21340c1c1c8150001c0130602c48103d5401c1e501c1542044030401080c403e00c2202d01d40e902819802c0041d0816040c003c01815000d0605e10340c003450103404100079174a440c0c42c04d054034020f0a2165a07555043d248a0500e0f451800000d620b412940060100740004078103a040480c0a465400c0c503c0c2e8480381c64001c495440c000244981e1080006202070340c01c14001c2c04003190149001132420303031165002801c0e40c00c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 906185107 1250 906183857 906183871
    0x305180a050f1510120f08030c03040b0123040e0c0d0501020a030b153405070503061e0f06031c171501120b062101051002010c080408090a030605 64
    0x7510340708900282800304081d0003000d043c1d00c1e81c050515418030baa09489922540461074611103804007048900d0386e0f4502141d8010807810307100d1601e81c1000e80700e50b0080358221400310281c000031940f0744045501c641703804d4a10400040c1403020b1004e000052289482e6502c0b06e20655200080c2a901d41c040688061302c507800240c1c50301800f0601409403815072038054460b603440503620271020303000c40a48109000340e00103440c0340500221026494903c0e200c010219240e9645024144003000602500701d91041c1c1c1150b500f030340d4400000301d641041c1000141e00e03091072000f2442c2c003221415400c1e00200300509031400544d038030f5803014140e07001a50f4035012407000c80b00d8080d09622030800301c7e4000b1409a40f0024210841d00082031813900714010080d0340d99950480e4040c4e1240025650705401c00c02440300303180c05c095264655034800344203840c42480c000c0120030303090344180901e000d0b0180765202e2003030684460366044540d40002d0340054101081007000408950903000d964003e510b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 906186357 1250 906185107 906185113
    0x40f020c1f0605091b0d0c0f090b0f16080c060403021515060426010e15151c03021614030d0c0503040b0a03020706022b0c050702010305180a05 63
    0x1c101d452810120aa414100c40a61402da01001103441e4242401c0d4054035144401141c4c108500450303410b40960150001d4140c070700a0358903c910780041c8000d0840f503454a5a481e241d694000381c5601e480b884520420b00b50040c401a107079842003c080002d6188908401410035005c035900c01c0c40c000040750194016071005203e400503003d501203c0e90086004400155042c8804000c01c0701c0d44180c1c030516028400d00c514404221205a880c0c100d20f16200d002800008041c04a50740c0d21115440d4040c4990802d81c08910411306400012108410140000c2880c001c2104600091b9299a2044d01940540b103150820b140c81e07801658054022074407110320131600741050616003854445040d00b800a043c407100c010074000010340d02190012540c2d103035110100c8804902034003411000402c05400803558030001047c0d03034500809a09058110480455034102a005444011081034082282080801d000d94841d40009600558524035003200020f1810324602d04080004249c40c150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 906187607 1250 906186357 906186373
    0x30305150a060323281407050a180902030907060503060f04021309020403061d010e1506031203010306020a030b0a1a070f02130b030d0e0a05060d11040602070303090b0301080a030e040f020c 83
    0x10307610450381c40c1103402d000800c1242071020b051b224820001d010790080c02004242c00014611900e46614520300026031002c089989040c17080c081d400946803000c06000d00b0001207621440341040d04d100b4140100204002c0b41c1503014040254401007502c08065404100400d040035140010401144101c600296240300440381000c01a00c031000c0510903410707c5d0359070000d14400030340d405400030304012203507081d180c3c100060711305101c4400b8a1085c40f004000082441550760250002403d0b40c0c4042c05500700d008104845c411340d40c05002c011010303080c0090240292100a040034078415896030500e030700c460b00018002c22070780c40f040075850344402030300516040a000d4030302207800608084401560b40000101040021302a41d0b00508011a260750407560a030890440110403104007641c9a4075144025103403412400240c000c9150100000b610704410800caa04860025002d8440080103540c2101c20301021103840b680143c69041d0f84840c880a8801006100b03805001030680d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 906188857 1250 906187607 906187651
    0x103140105100308070b09030c0d0306091104060c0b0702010902041b030f0b0a03060e0a061b022e0209030c040c050414030109050601060503040c03120c030305150a060323 75
    0x56140240b4004504982c0001000010210b000743e42c51681e1007500e407142c41c0c0c0c50b800399610310f028039040c5540c180300d00031041c0c0d5000e8040c0d00400c203851200d0307028040a085405112410300c294442c0f8800035082d40c400e0300109031002076194000311148000325200c2d4035a00080c00b51840c15444440c8503004103c401406500343c0300f6520613950008081c40342808042c006540700f03140d807001400041e01c46080411361a001c0c042c901c6481d600c414100803502c04503188020032020045000e025214040300c0e60f09001d0b82988518101d4036101400015900100380400039400c5106001e4061050b642612001e545902916035402e255503203071130300c4a2030301801001903910b5000e0700d8040d9241c4040c42d40400c0011a409065440a09003240e0704d4507a071030107500700b1016900142c5040c468401040c840b07903000380040b420a009a4092103542ca03056041c007014050050b00c6030340b2400390f41040103414041c0c0c0149000e002c41e40c80c8188208801d410016111800700c0780e501c02129408901424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 906190107 1250 906188857 906188861
    0x80319090f080d0e0a11131508031306030905031b0a0510050a0f0920151c05070302180909010f1505190605180f03030706050603210d0c031401031401 66
    0x9514030200040000e500c4a4851812207580e11030f40600031f041c84c1801c5d940c28580c507001401352143e50005500c001e0703076500040340c684d001941524901d4400b100001a181d100340221000103400c000518a41a658156000d6101d452180c010007401000b21040100380e0500c14045982c410700300c00318540c40c010305c0c120110768400c0c0003022450f00c1c1c007008a000c00e41860920bc00b4000a400c1541c182d2900300024820100003515482c0d40c42c0000303070142c07841d00b00108100008600384820702c410b845000c0c080e020b0340941c1c921a0301c5042e101910006c0e5180840034150001d144000000e15a001d81034043e050341c0d00c0351030120324101c0c2c0c1c1c0000c018505112140442031000c2442d0150002d00300380c002801d9108021104000c00b200c00c2000307100d075440c0710b2448404200141260350701c1203645002c00140408840a901c2800740d0440e40343d201c11501100251f00400e982260301d0400707407044d000001c051940084080594425005007201000803405010390b006910980e403503c4c110a009003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 906191357 1250 906190107 906190121
    0x7080106050a0804170c0f030a1805030a0b0c090310051609030b0a0b030312090d090f05010c02060c070807060507120302090a050618060406030608010b030307080319090f080d 77
    0x401c0000c01c034100030a540038805642142c0d100c0c42d030004501d42e001d0081c1540c0102c1030b040f50903000b0324140e1990310a000000f80302c0c21318192070b1590608030b942680f050b04c21f03107441201c0e051b030000c4108100040a0344122540002008001e50601064a021918012440c1400e1204583d01e000f440007020b125990007080700300368a0034240f494150395481907188400f6040c55400c0c0c0e01d0f113888401940d410b1040e1140100d8802c1506450b1804c2d1020030f1781c83c0f50a580500110b14480008030b1085400d06182007602c0c2c040c0c590140d409625800c0c8003140d4800544004c580c0900f40c00031030f2490b014800700005140d150340c3c03036032103a00130305002e41544000403a8005062041040303030460b86440c200501150012981603840343c0001c206414100381341c8100607408000084d0100360143c03d6844042660102e40c02045140c86450a041e0340e0301c0b07034040c0504164020300018810f0f452800c1000d090340d040b9400440c04da840d994902015910200003111818004150404000d04038400d000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 906192607 1250 906191357 906191369
    0x40204110d0b0a150c02010804111e010806040b0f010507060609090507031407061b02030a0c090c110c0a0b09030304031a0f0603161a1204060f0e120301090b15030f070801 75
    0x44109404c000702800340790707600030001d061110350000182440720102c101004400081c201a1090404021013180320301c10001060101d001807001ca034143c1400d1285140c40c0c00080c1004401d145000015940c6402c025000c81c0c4868640002280040250192000c00e9100c0e400600c40b1a0a6103054103c91700100003052480d4009081001013680c408a140a0245283e920290724022400800d09052800001a25009034024006401000743d0321500c00d100c2035640300b0301102e400d1940345490706c2c08100d0040c4c2c001c5100034140501441d01005000c0e0403001000c0300e02c0c044d41e907070f42c08014442e06822031000703100c10410040110701c00b40c0780d02d9108600300e0213400014900c8640b114042200d0007910307400d034282d0a030712541d800d0300b5080f1036005c0018005400c840c5044c0c90020050201501d000c03940d81d080c00c0c08150150780c001002c80d4204d02030958282561700302081c510081035025906640840d6204005c829000c8040003103000712a4010640c00c81e1404241c0a021094180c0c00301c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 906193857 1250 906192607 906192629
    0x5101030c050f0d11090603091c0908060a02361807021c0e150c07140a06123809060d0807020d05063d060305040204110d0b0a 55
    0x303225041200000c44a5403c3c107424002141c8040d114990114058000c440741c00c8000001807120001d4001010201d6602c41c1007540d45805040d42c04441041c050712407043c0661041340400c680705425000b070700d4134401600c4042100c400100b040c0c076500c0f1000304040030820ba08841d0301c1150030300c1c031000b03101c040c8445000c2d2218100850300079601c41807246a07045c45038140c0076208001e4480c0003051a20800203000040102018100070010341c00016042043d2082181c000b801c0c2c100c1020b071030488000180100d181d1440c040e400c0e120004d9900110b0002a500c49041c2400c4259001c2d403084840f04002000d00c4d00d038a000d0b5030328081003960300c061281404a0420030309036a5074032801a0594040109138403443d0701e1002c58011111101c0081c1580901000c0280d520720f103143e148c2100303a042d215280d03440401401c4698401d0400c0c413689049100342411b1065a00a4204a03000b5101400c00184400c020440102c103401c08442d002d01c0a4482e0380100c058980071030920040d100741412 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 906195107 1250 906193857 906193867
    0x9092a0408120f3a0617070e0f180106060c260d1503061a0a120510020c0c1e1026190203040305215101030c05 49
    0x60400503001d0b64103110003044d910302c0c0340c4180a03c05a804480c40d0710701d011390360900e00e003480e1590113031106000c0d54408511150310490603400c0080e085044814400a405154803506e10381c100101008041000210020701c400c500c180e0240b0a440c000d000c140c1c2d80c2c001b9012580b400b90340c80390b850242221010b038030b02c526544c454200001c0324642000c1400008100d02c405940c010b440c019503102825842c504420000c00140c0748444102a00088490b5801903841e5405400020800e800c058900c0d40810001b404d105400c0d401040415090786c2160041541900010194003484044400f84513641c0100c40507410302006030a41403c3e942008070341460001c0302c03a0300700d03c0039500300d000c501c07407c0d00070070038010380306402c8200c880383c852055650749800d0034080c1840d4400001042c102c149100054410342c00320800380e01517054041d564000305885e40440caa000b60b10040d850300302241610f489881c4c84a448240810560120001004103002c000541101d103600140001d0080c1082 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 906196357 1250 906195107 906195127
    0x2405121515100f140d0621061b08040f0606030f141e0a0204020a03020903060106031406060a080703270606031103010b060a050c07120609150e0309092a040812 70
    0x9420b8a000c03030000603258541e000d441741c0508071310b034441c240204220514584c0442166000c402c1140520f9044c842120704034082c00e50480d44c100c2000000d1000e07004580000c058a0006011600608001c5241d54a989400556034107140b01118107850000761039440c20f800b446048a07121b40c051300034602e81000c804490f101d540800c8020721842e40080d620400d02d010f0760650b401081c001d4101e40741503031038008c00340050032010448405c030f24808000602500c0c0880c2110300b002d5040d60f450b40e0a8407190790a401400b4207001e00c2c80c50a80444035a0341c8405104840c50f8030030f0140c00d01003415461820680030000c4039541481c040c0e41411000400394841c00125103800b401c0740f8240f42c0c2d503040b0550043c20070050750040f500b401e907064164424004280c12900d00c83e801802296002c0c00c4a074032440440d00344c003070424040e803c28480750203585045204180d000d8264026075031500d005043c44802070980c07029080c19401c003c2000c1c080b0a00820501c05e140e1902c145451800035084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 906197607 1250 906196357 906196367
    0xa02010509010c0c0b0a020f030705030403030b03071d19020a170f010812030c25060e0a020906101e0c0c060c020102030301030b0603010219050903012405121515100f 73
    0x680c02410004941700030a80700c170550380c1202c80f0f2090080140303441c2d0400b00302c001e21561041d40c09600003800d108020b0301d58500420150201d075540e90f1460403408840007007282c5182c000740252511125550030329000442c41c00200b4041342c070307950f50084125540200020042c006444072608441034001403106003070001e840e41c1003681c0c0c1002d581d2a503441c0a5000402e206041103020345001c0e4034004042d402e6140d907810f141d24800c0344144120125288004d5840800400181d84010010701103080e908050b90f20710160a40c501c4c0c82c011800020400c3c206440780a40e02c3e000207807800c001681440815a26903018040c030703150403800f080a03030300000e5590106000241c5103200031004600c03255025811030301c41121444281e4148084408040c14072707041600810300a50a010004101d840340c402d0101c00ba050804007101d5003818036041c07000800d25100c842d2054812001491030607401081502e20800d6220091141c0d0382040d400c5c80b1811a4500500d000e001d2458000b00039181c00c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 906198857 1250 906197607 906197627
    0x609051f11070b150607050d0804140303070c081806210105120a03030225060606020c03010b0604090c020a080304110f271f0609050405010803070206040608040309030c0b0a02010509010c 82
    0x1000783c0f0130981d40003070002c3e206104214000f000c901c20550290100d40d007180201c0d105902840310202e01c01c0d0f1185c000da80b288011607031600080c2811400800180904000e84800c03008259590100c40c40758000c074038982e102c0c0322048201c841c985010b144400b2000500c6014000c15101200183d00c603000a6039125210784008080c0364001c01c3e41c0c074040c40051012640c40240c020312403080040c03420200020000c5010b090014000c1010360805401c1c1405040a4408040c1c2103078070f810b10304642c81e80107002c412900380c01c43c002c140b0440081081607028500581c010b0004029282c0c00d1400c000a4074071581100313000d0a104000b803880d003c2001c00f034204080c0280340400440ea1401200b81e05005881d00304660070b00284000326289034071856030419554159401c000e9a40ca41481695038021414020f5000f80d08000c18414244500001c80e0010f10a00300029000d4503a514410440d2541d0003848042c0c1d00071500002d0260709000e0b19402c0003e10b00200113a002640005101b8900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 906200107 1250 906198857 906198871
    0x20c06041511040b09220e060108010513032d1107091103010b03060a030204180614100b0a1101020d02030702190c0614120921040b0d090609051f11070b 67
    0x211720340000340c40380301d00c00d40c40c01480c0800c04240e0008000440003022039450b50496441048000305450505100300c900900869080704030440450383c00b1949200c000403418201132020480b101c004800e40c00741c640100507030301d175600041c0005040302c1c03a10b100c1d68407100c4505d017081c0c02682c01824000031a0f043d40d1070021441c0d541d90342c040208040d280560700c020340141c03802c3e008043d40b942070003030000103a00c58501800700340f00c42880c0c0000c2c0c11040d580500300326408242046401117203002000f89030706a082040304044a114010300320313008010440241c5800104101001c3d138140050114240c130402c03028050381d03568484003035101c000d00481c01408190114140b0121101e030584210b0b84e81c8050000c41441d1090085464000b000009059401b031003045400301c0d580c02003501e098030811240c1c1402c040c0ca28000070f02805408005513080c99441d035420011038400e1200111210444440100951401034154222031185054002d000c005004a20014a01111003500808 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 906201357 1250 906200107 906200129
    0xe040b210d0f1404151e030e0708030414060a1701080105010612150b031e1008010e0a080a030b010909020d05011e051c03030e0f1c080112020904060f020c0604151104 73
    0x400b02d4010303918180c00ea016890641c240c503801b09030b525850b40050f200401940305495050369208110790340d03405a802445807203d101d034900d01c0c4504010002d003444a4082c600751101d00e40100580012007801e8000e4040ea9444000601880380c114500d081e9080310031b00304001c10204a5420188d4007024001c20303a04101c00004110042036041980c00107042d00702203241141083c8151080c000b8407441150119400d00b035040b80000b03c00f02d0341401440d000580b4510b03000c0d074203504800805405204d507051000d00400892011000c1c4054560001301080004555040200100000c1500800e002c114903054406118a44610305440701074118042014440700b40b919050b00508809440656940706042e134081d41030500050032030740340406641e040c43e00c04505004442405090184480c4100380024030001820200c20203580310340903903000148800d2580d0380005a03803002c0052401a4400814072040c802111441d840b40b40b4090710410207003400f01488443c600940c810402c1d150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 906202607 1250 906201357 906201389
    0x10305060f011b170a021501050603070c11030703120302070b060604060903170f0705061504110910110327041b08070504050612040615060e040b210d0f1404 69
    0x42400c2643c54085132451520540300c0442d0f010003035544444a03211641100380000005180c140482100e0040c071a607a40d8004503001601d03184003001c400e40445416126006002022030241c0031800d0b250724255034007603501d0186007414100c00b00003070701d074600c5004100010041c03185c01c80c585404403503201c001800944e500d49002d10407401000c80c68403160000040440400ca40401c506101e038410010015840c040782060100301c0f40031a240728588141046401d01601c0d06a840525203110340c0f405400b20481030a681c1c1c1541c104003000800e01054021150317200215144100b1211b40654080105080d1204110000e107800c0e100a0240541c0710040341007140301310101d070b000d0503000d070026984003d08005182855070855065032403138640b030348450300085107104044c2110302c03a545008000c074020042000420900d40780907070020365841d10f902c61b8442a00000440042d070700c0038245000c038048000c0c10880484240b501040030150071000b076282510107403130581d0058411a5102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 906203857 1250 906202607 906202613
    0x1e06120b0a0b031806010b0301051327080a200604030c1b140f0301090f060f0e010603060f050f09070e0c0c0610061409030717010b12060402010305060f011b 69
    0x42101d0780c001d01550200081005039202d00c004a905910300781c0c10460769281c1c0d0f142140c042c01c2c0001c0c01956401100003404a0b0f03500d820f50042d41a005c4032102511842c3c04901c501514410201e40444000d180460000c3c10075420140030791a4000a50703440080c3e82a0003c89500c5507801840101400b40741c0d03100c5030610038118020314440c540a0032075030300c40b5114421a40001035250900d072182c07001002c0d1101e24181030140303e001c0b582c85040c02c001803003d540d8401c054281c03445001d0b40560f9403c0008080e960900900e80190302500f4005801d1140c81104000d886000b0001c00702d864692052220a4a0000e010011070b050f09050340166220101011881c2c441e51701c1a401900c10300b024814021180b00d450390486d081c5407941c1400c038880f041080054052030ba0b8503036041d08982e0007044008112040b100d0320204170400007940c90500782c006484a0030342003d01aa680c4500200400c558041c0705041d003002c0c3c1190000d100e101d01d0b0000130b001c01da405c420b00d0302c290090101d40c810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 906205107 1250 906203857 906203869
    0x9030408100e1e0a14010b03071706151e041e05090706020106210609020402130f0b0720041d160906050a03080a020a17041e06120b 58
    0x26060303150a807003900e1800d4030780e0000303000c180902001500642e141d441c00f456a100d0b80e20844203604000d0b1420300001c0d02c0710b000c100c441c58000d044554940c80025078954090201401a21040134040010b0000407940351070108028440311000d20f00c1c071500700482c0c0d034003402000804c603401c41d1812464041000b1402802c14027140c6900d1000314000d5080100090304031502c140c4440342110b0310f050340c46904034240d400e513114150204400190102e4140340070380300b441040b4081c0601048e40c5a155000c0b50403130344105a91000c0c0038441d035060046100d0858007000402002c1e68070790800101c0e84501264401c0c82d00708001c10003105451044030746950b002044d1b103010504c010703030f01c000c0001202d030749450317190701c04084103400b0601c04502c0802ca489042d058440103030103021170030b0659460050341c2d4011a00f942c1076105407000400001c0034442e0a005c050b2160403265110362030a480b80c4c10044038182c203011651400030041c810141d2100b4403501200c5002004112200c1d64408266 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 906206357 1250 906205107 906205109
    0x90a020604090e060604050f071b0c060230030c0a0c021504050f010306030b0105090606193906020d060314010506190602071a19020106090506040b01090509090304 72
    0x2411520100d00000c0200d4030f503014480c20031000042e21016601d204c100002c403041242c1d540310342c0c01094003140000e48900d04c442200084900d6a40c4140110303164030764108496809000164009801b02e00c44040c99100031150786040e030b49400c0c004000c9034451000b4080201070141c2036038085070124100b4821612505000d1b0080d04244d400c403240c0c03190500c1c075402800382078080d41c0d00f220340380015442842440c2c1140d402c06120546642054200495498081e04a650100e0300380017820403000d464203400c0c44c2c00c5017919120340d182881c0712215006032030041c120b020306864120b43c0210b216000c0e2072100b9680d00030401655010741c1c103041d070010001600007070107200c0019400c140c03400d4154000ca000780021105c00c26030854006003c0801d100b0b0340594001a00720b142c081002e445105c0d403246040c40070b05c031034906100d004c43c0c000520b031203034161640050303440c0d1004102040044c82019041801520284a5111440006000600c40b40314640c000c511100015401c20710502c03d4070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 906207607 1250 906206357 906206359
    0x190c0509240d081309051b03011701020c0d03060503100203150d0c080a0501021218070b070825060e010b032e09080d0c020c1302030603160609081e1203090a02 70
    0x2544540003059030700991284c900034080c81c1880c20300426407504142001d426110030f641c0360035245a091216400542100b802a62800c1d9028444103084000900103020720000300c0e40d000950520b01410540342081080e840c0c40c00a10403c180110312080180d8130070200010ba581c8041c0d00568038080c0d102c00c589034045003990040c400800208201034005200b5806007107404812034640b0300b0f1004c0f140480045480c015800f0744001c0001aa080014186a502501c2d072241080c103134800901d00307241110a1070511840d076224181c00c10000d0320072482d110500e800208540030071000440d649400041101c03468006504061181c0b182d41e0502e0425120640c00c14440c41d90f00d0310700203986400c00301010032503074204007000d00d0302d038400680300d130581c00001e0000300e600c181804010000d60000d081c04e03801d4094081d500100c0020b0003000c100400300c1d661180c0d0450b2400c2500f6082c901c01c40c114403200a0400c64405140600140c05c001c000d07030000c074107640e07030b2103141c1c0d5a441c08440220003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 906208857 1250 906207607 906207623
    0x1f0504090507050301050c2703030a0807050409021b0d1d01050903011d0303070207140307050609120604080c0d1805101b080a11010903080a020a03020903190c0509240d 74
    0xc1c47e034004801800310349442e00c0f4586014a01010210000841e2460703440d00742e4001d101c0311100320700c035484007608102c0a00381a4540364540b00745000f41d030b128181490300b00701c040a4030304021800308050003240c0b9661400c2ca05800541121150b89081c68003564104040442d0719012964290300c40d02c2e441d070b00c1c0d0151140c0388818400058030381d041111044054024240c0c0021110180395460941c24001400350510505141c20407095800c03034011507403c00701781d080b513020000c420400c660244c2c0c05141e48540354503100a1032450154030841da50100f015800700440d0a410668403501500c404807038580c510300c1140012100202c50f507102c1d1017038440007010041403003160b100420070950b0b0760741c1d0050f03541c0019410a00b607407800400103001550034000680101d07003a0380a820441d8031480c0140c58503081c480040e24010b14003010b020b45983e05182e5604000f60003083c40c0040c0406e64502441d440d04107000440c0c080300c1200c0400c09207805080039107903682c0079001380e01a07070702c6011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 906210107 1250 906208857 906208861
    0xb040b180114030d1713080d0f0e070e060402030402030f12031e070c020d05071d0a050a050403020a030c06061215050702011a012a0f0b1f050409050705030105 70
    0x35490000c0400c0c0701d501e510035074102c88408503040102c0c80c05004130558032807000249140340041c082c01070003071941c50149441c07410900041c01d1600148503002300d060002c64224800d40720702c41243d54408038211190f000b41420480001c808075400d602200450b40182c803541c9500129060000d1030b031481c4140c0c069480841e8402d20080003071030140da0260002c042c02c42c409008000600e205581e4800846e8441050344010b14010094016040c4076109403040c02c0ea4405400c001c0c0d12104004051000052041081605440c4078065001c5502c003824072080c01c00e40c602a4803480d02620190030015900700800500842c1d811110080c520b854071401c0321203560030604c0100c070f0322844240ca05400c000115004e24814050340001c51604100300e01400c50640040d0307030805102e078400303504605c0d411303590303540511410b102c0903401d00800052400548910303007449104002001034841c0e02000444c05036400011625078151407066400081105030303410102d1030104980e100310b43c95030924003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 906211357 1250 906210107 906210139
    0x11060d090818040b0d0f0309030803070504170601030804050112090b131401060e070f02010609090302011d03031e130f060c140f0a05130f09090c270b040b 68
    0x702914940c280c1040c44000607481000f0070380390718802c125800310103250b80740049a890100c4406061107800d14101c916603a0745c401441d900f00321403a20200d84040340030030120f0b240b0302e42682e80030403103006041b4940c1180d403805298007a9009060410000580302e000c034055981c0601c640f2a0000316030001e034030740407005e240d00c611200c0040320b078070b005006120b61102050040d0810360711121361403c000d40e115070040302c07036030369240300c040856484030390000707a4003c0340c411005618000e070300114030122914280c6e00040b0b01048105401c1e481042007042964550b96400b4100003400030700b10342c2e80c80e2044600c566032564003018040e106074803c0b00c000c000d8903500c20313080181103440d410903042c0c0d4141d4484ea10700a01e9040705c2800c0042020115980c071920003890b40380da6111017000101d445074514139105056030004172070241e450914001703001840700710100408100807402d00d040304081c00e42c0740840c14140041e4000d81c8a010b60303400c0b5901c5400540c000b9030040c14400a61074450 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 906212607 1250 906211357 906211373
    0x2b0e03090f0306070206191409030c0d0801060507080702010302040b03180d050f030c2209020d0501090605031b0109090f02041d06090f1504091a06060901020a11060d09 74
    0x48940c0d10501040404581c20704003c91500e104501c50380107060566606074111904428010075035180c075598030300081003030801c441024081c800b0900110785880d13071032040341d01e002d04045c180003e00c1007000041002680c094101c5a0480c2e11520568482c0314074401600030340565000707a03481007008001c000428840c0890141600000000c80304206c00a03e42610305110710444288940d400b04002501700401500400005504448010aa45803d940004119129041040480c2e00015959a00320160041c640507180725403040000c2c1e8502400284e42e00c1c0412401d005092120901d000c485e80580307440d10040580c28824010044841c000d00001d40c071500856240b00e00080b86662780201301c0e46254407c8001030301c035008a4a5103203100714940340080149040c80e4042c0c014400b40d8030b443c0107040c0c034a48911038200448a070111420440203004040c54040c800030310000003076a0340003910004480e04044914041541c50001c0b441d98030410b0350100c4414188220030741005007003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 906213857 1250 906212607 906212617
    0x1b0503060406050402030105060703050903070801061e080705010e12010f020c01021c060b252003011d0d0518040603030c03080a0203040503040302120c040c09080d02122b0e03 77
    0x8039020020b158a503400c00c004c901007801415040b40b8281302840020303010340020301013028028129441036645080321425540c00b500580c8071615034610f0750407041c1c0c007940c0d107101802000016254503800c02c00002e00003c240f040a5104034800c1c01e0790000b040c03080d4003101c6440d012400642d622142041c0c1103020b03510903100003054021004010031281424403406080e9a11461910725191080083c0d0b408a0222104034407024a035a20580000e508503200d00c109000750100702c29000300400c100740c2180c041940c0d0909038840c81166240c10b200100e181d42e00000c050034000d44400c29030401c0d2419502e107101c00381e0058640f4602006140e04030031141000c038403a55a114007955150b120358285e0105030b0340100968014042480145441049010305038215005c44000034081c00c0000c080c0c0e030082c0b1001010407020b00d4144580103051050070100f092600051018056842c050446441010100c40f80c100100849810034810721000d03407a05420b10009000c5900200f003415203a90103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 906215107 1250 906213857 906213859
    0x13051b18010b0d020f130915060c05100e0708070902120903190c030c021e012006011202030a020603040809010201050109060503060a090201051b07030b060d0b1602011b050306 77
    0xe091444103406088403149070594241a9005061250400700000070790400c89464801c807005028a00e00c2a4804100c2e200030a501c010104281244a00519220080360000000c22120401c0c04010650025507440b07000748900c000a00c6000c500c4d0800e0034a80d55411008070750150380c40c0001c15150a0300502914800040403590580f10030500555a11856804c107000da000c45064241d92030180c0541c1045d1402400c0c44a06041d0755030014205030074201504194608107140040e455912a04024444082c41d6070013040385010041c69035595414429022110b20041c000411500c060203103101556024121940300d042c00d20b08900590803030030f11140150310708000020905d03850b000c1d03d012504081c000d01641e40301c030803044001e4641158181c1c10301c08200300080b14422800924040c800d04000540b40050441c035000318615000b40200b07100341d9810071001c01040c0369107007185d0080340e8510320451015500200740e000d81228080601d141a83c03003000b24110350040029403082c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 906216357 1250 906215107 906215119
    0x40b0612071d041409010621060c200d080a06060c02190518011d040201080a020c0718140f0105030d0807140d091a102d091d0a0203120313051b 63
    0x3231240e03c210100e500102c40301d024210482d0301240860201d610011800c0ea00e840c1c031041040c0507812803640400850541c1c03da50307110500007010158080e40094114100d02428008949440002003e4420703075140039208109109031b4181e004000088600140400f030002c02c000100c05820b6a004242480b5074000c1d051403d0036048d021003880386881c1324070360503100c510141d19035203461030080d00003440c45c0e0414131400e040440d4100c0c2c1108494840f95019030701182106186644044140c006001c01840c4010303600184050741e40810702c6100f0160034a042246641c40b110b04540d401c59401ba281d02080b00056030200201c101c0c0c001e111964080d28400003550b814890701525488102e4400c040b18090000611070702d100203004102c0c05070006041220124000c1000200d0040d0350b00200304e99950f00e44660801c0e03062200c5611507000307032000d88018181500400c1d2601e4203000c4a6400c8030300000000e140b004120040c7c414a9003040848000d4400c00082c040c1592210191030b100722 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 906217607 1250 906216357 906216359
    0x271b032a02120702240d060609120b0606120c030115020a1109060d02180703111e030c0f160b101223100b040b0612071d0414090106 58
    0x3090203104004000403a600820340b0302c51881c0241c0b0182c000a00c2203a02c01410034040c0c0040c10b10700501c04001480c80b010940c0c5020078080c03501102d05550201c030611100c0c0c4403c202080c0c4041c10134072600d40109141e100b50f0b540d140025041c3c401d40c3c0d410b0603c3d03100402800f420f220784a0246050321100120540c5041417a00180c1e40c801c0d20320002800c943c0011981d0f06182046440d0980204016200000400c00d5a000422a0f01c40c4100c01098012990400c1403130340c1e241c0900c0b9134040c44954103903d01020481c0b00800404004004180154000082003030040500b04843d4030158422110303131a80380080b40d41c1107141c8620302c00c0c2c0344d03400c250000c5407900300c01c0314210301240d180c0001401000c1059442c16100c8086006406440e00c0d080016014004184954446d0501001f00018001a4101000112541e614025016803402d11510b078007039044075015600007261703007001c85034030800c900c0084d2032076150b2100540150a1100030268102000009401850448000d01c000703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 906218857 1250 906217607 906217661
    0xc0f07050102070f0302061b011d03070614040b0f0c0f070506101703040501111c0c0b100605030118090503160201030f02070c30150510271b03 63
    0x304c5218080a9800b05080040c040d010525041240b004c2081a0010602c4825004c0e48115043c180e034401800c2d0b0030015260b42040f6440c851a0016a0401da8400071410503460b49140400018000d4074684850404201c000120b030040c2e823040c09820100d0303681d490561401d291690340a0764040c0c80c54030f4080700802c2e0180522b40c000c02882c1500300443c00c0504e40001100d942001d02c000c1e06042c0202079032603a4401e4081c0c060511020282c9880310b22001c186020030500f003000b42040c070031490310102030028075440b03130859044951608050341d003650200d440d00f004110780c48000b092844006040400d078490300103103042c100d0003628200002100921402d0a034407030100700030552001c804081c8101d03c0b0b08803401607442c9103440301c85070b401c0d104011a00b880c00e0b509020703103100300c51003070356440014540155940f00f5022411a4220ba02e1710768120071003500e6070b00c0c0c0c1420803040311411841980ca548088000e0a024a01e00035030008041c002c0c000f0a4010010341130140d14201c10703910 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 906220107 1250 906218857 906218879
    0x18010503071b140d022a0607080c01020301170102070f020f121e070602120d050c0c0f03120a140402013605120a0506010e04020a0801050403031407030b061e0c0f0705010207 76
    0x3e140c900c07a0000b0729450039014086c000807000380035602400c107110100129141c207002c1d200c000000d8000503925410b2000c00c81c0c3c2c0111142004856a0042100c82c00141c841b003030785000217070b054031062206406100018840034240d54540c1d001d01c40c1520704002d4100c0d401c80740040c812404151000781b502c8910407a140c8051409032130804208000042503110550300640d4400e8400e12814102400056041d0400560064a1016a0001c11900a254084070b505604028198000c210700481142c05100c16040184080d041c00801c48809520103184040900c1042900e4411810b410516004c03d46030312860041502070a082c50203408050b130b0010314042e649402800802c026071905480c00c030b242800900890300100c80002c0003070310349070034041c040c00b031482524040b6889044d0b8004904085006101d001018240903262429885500c111100285070081052412501e0210450b00f8411401c00741407603c1022003482c800100818603c0c20340304241d007501d2a0590b40c40c0c002203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 906221357 1250 906220107 906220123
    0x20f0909010c0f090e010308030619030b01030605070507050a03080c090a030303050414011e0b1f0c03030e160311120d08070207081f0f0608010c0c0b010b18010503071b140d02 77
    0x20b517070506080140040350f0030348069a40003000a00401d501071010862074034030b0466034070484402200034014020020703e40079541c0c4c0100c0502d081410880c2e80d44035076954003940c2c40040c045c840858007043c002c0d00c002003260030700c00c40649a243c120743c0c0d074030340180104012601912110b031010040711213004180284048210140e820b4100c030a602c80300c80005043c100c120507032205d40c4030240d1541c1c900081c58210601070340e45440030941c41342d05000d070646452940c6c01c81e403a0000030307400342c550b02001c030110103403a0402c03c284000014180492203035180c41c82100c081f4490030520441040c1c1c040d0752a0303c1980c1c59425280100e0380c0f040c0c515078661003c20f9260700c01c46040d00d1940c0030701d101c0c1d00040800e0950341c804510f0684d200021800c403000d212950001900190542d000e11030750b0481a8010585207841070300e00300020100700c0c0a0603115022504000e00040816001e07403041c11801c0862940c648100384185840c5440e04010711007500a0a41d0f01030460444002c60001c51030351 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 906222607 1250 906221357 906221369
    0x18081e0111040e0c0405041416020c15070c09020f19020303060d14031c0617160306090f0b090d030f3b011d19080f0304020f0909010c0f09 61
    0x3420b06041450302d40d40039000408001a07450140400506590346000d001212940c1140c0c020260914030003030b41480d954811100150740c0041b500e6895520b0300000b04882ea26255907282d1200b945250042c21190310b90302c580d042030b0004c1120300060701d14400915040e0440c404108514881075001c0c3e0701e030302003100d01d143e0080401440b000070400c1905070034000c00720030056a00d031660040000c400f6007000781c0c3c0e0410f074580c0c0e8201030201d130004072050000340310188010301c0151031140c00d0140c100954040200301c1c544400000041000366000c091440f54000b0700740c0c41c580b401c210660f540c3c0d6112650034000900f0441c1200c0000003c0c031505060441d0285518004a00c08443c0300740c0e000f01904910b81002080e5074000180380a20885a2a09001c4503060700354094205003807802d900810700c8164842c1d0300e0801000101e0314001c403079135607000b0741c03900c4e48a40c1d0341e000080060020b0311500b80c00804a40801c80400410b520001507030303003c2d8444503001d42a00a0444041600b40664 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 906223857 1250 906222607 906222641
    0xf030c050103050402010c020409061d03072303070c0b0306010315141011011103040c080c01021f1104120218070c142506030606020c1008040318081e01 67
    0x14000c03544039410440d441401070404506003800c541c0402c003114001001900e05a64131070042c002c005036150a0042c90403403200030b5007495a42d4581c0507e14622041d4090300641c0301d189085000428420b442200ba0001592004156249004010b5510848006002034a00798041c8035080c6070800c00000c2c0c0d41140c0958518603110003c0c005414003c105220038010000d00118491780d00340030f0b202005d81c020212980700c0c141803410340310804075604100107582182c0e44c0368000380d0b400075000c204c400c040390303044600c000455201e000403d042454150b19020010b00480e4600508610705841d600c26600151188078288088100101c02d840d41c1002940c402a02d00101e070403449100e50600d0340d0001d0320018482586244410306061001c42e008020030a010041d04c0c0d0913205501c02890b0f18000350a032301041c00d00056012610051820038401c1c51400314081c14450091001102c13050810307100751a0315800c041d540c403c40704041448402d42945210f590440c10701400307661541c03043c21 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 906225107 1250 906223857 906223859
    0x1a010902190324080f060a06051c0303090c0e15010f02190c12030c02240a03020c0f0f010f06050f150304080c030a0c0605160c110109031b06090f030c 66
    0x3200a0f1035103100038100501d0303a000c40c0208050800d80b01d0000d00d119002094074041300310310107084c102e00a101c3c0114500e024010415034407084220ba00d0014442101000011203107000c0e0014440d005001d080d055108030045031180190034501d002d1207071100c400302c0d01e4510f0001100c1c0c90b1030341451580184c000021b5040440c090151140401d4030481280c1102521004041c410558080041c2c000640b02901d540a600302040c7d0003061141402c107850617040d41c0d143c000524440c03400d07828101940015001848401801201140100003060790080002c07941014013070440d0520700c131841480c5c004002a280303402c0d40c1c00c51b240e40014108038110f02654000d00d80e035800040c82920808020030140c00d9516090008011241c0703075490b5001c000e031150800e070b000c4a200820680d5150314040240d01c0346030b00176001001c0264070901c44c0d0642c1c404080100c458559640c4010000014900e42c5d040b1000c5030711440081e2001e03541c81e61030050741c41c03110307440c2c00b1901d1002070403081c60128 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 906226357 1250 906225107 906225157
    0x706140a0e06030a060e09031201050a0b04270507020a06110a1407030c0206070b0f0109020405060910022104140d120311210703060b0307020714120105041a010902 72
    0x61030740113800c140001803072580d0300340354100c0c050216804803040d000050b040b0719121403030010902401d41070b0f40342d0204c0c0b0f0825507440500d100324085c2c600c6056090172044200c00054003114001248a2014050340c2081b04c8069956000c21108030785440c101203484003202100c005441e0b49203200d030b031f0340b0f03c0030b4007101000316041d0311290040c8d0422032000309060150301c46c04001c00c4418840e40383c0c440c0d42d10705031078588506c40040e0400011039004000030001540d450060380d050940448007201a44000d01c0240d1511100300111804441400c24242c010b040160240c01140d004140d9155042660f504011000c04414001072031000c030300c070800100300d2180d44410340210318040c1d518a0001104175840424110780001500002000204402190f05004031b00c0101009001d090540c24407480c081d440302401d0140d0301e1110308004800d807581e0b561841441c0d114103a140204500d040c141440c804c107883c415070941c0084c21030b000000740d40c80b6910072102221443e1010860800e0008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 906227607 1250 906226357 906226369
    0xc010f050c03041a0a1101090b01050f0a0e0a020a030e06040b01030314040f24020a02060409020c070b030a090c12030801090b0d02041118090411040509120c0706140a0e 74
    0x41881d0340684824040492101c0903803010064100d1200e02c40c0da143d908003000200185100400303c074950341002040000901941c0300c042c1954811a01041000b5a801c0410070300c0c00660b100880d100101e005001018846a009140485640e6000d101a81102e80c1c43da90743d40c001e880090001040d58010000b003440341450000394442e0100f0507280595940003081006d915401c517034444008804408001d241500120074050011300180c2545041900040c660f4060345c4964405681c00080801d4440014007250b006080171140c07907034881c181098040010301c60100215204203041d040402c0420341c109000034107990544c2e410070030380c1c2020681400b4000c110800c84c1c100c60440320450060f40d940c002d054618008101c0d45442c1c42240403c8a010319034010300c540a1081007050102096181b1842482ca4405030fa0115981c0c0320b6102c0d80d450403600c0c50300795408140104000040390b0b000318001040701da0a6445521445040803140c1151140e5174401c00880d0040096031540d0820f4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 906228857 1250 906227607 906227617
    0x20a030201030c0203041e0e070206161b02090109020705010e1f0903090305060f160c0305040905040305040f0b03070801090c0210110d090605240a060309020d0606061706030c010f05 80
    0xe48142da04041d074031f41c25034044040d10410032131160304582041c4000c4e1240c3d051140d01070388500c001d0980d82000005030783d041a0702c2c21907034100300b05510818400041000c60a0b60a40e000d001036055603529069031000b50407036007040352a542042c1c0c01507200c000000b01c3c9400010b120228440b21005403000c2002040d2503442103050100e2204000080350f4280f01082c41407030790340e4403504c0d1858510081031001111004540c14400084150408680e000307055038180c0703011172000122030b00c450405652600a9521034220707007005000201c2c00b440080042e50103a002500e46031200e90700d906100007660204040d100069024039a07441c2d1088150f00f1052011040340d100f035181021500007182510403109040e5100b50b221820b0240d001c3c41c01141e80d25080389149900e9066100200068240803503210310001c00d42c58401f004159035841c101c0ea40d01991180c001c200383c5541d44e10143c00c050302220071082a0b04c2c2c400c0000c14074100440c10f542d8412050350754a43c1d8010319441640c09400c0307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 906230107 1250 906228857 906228881
    0x105061602030c09070807030c020105010f0e1b0f0a020f072d0801020a0e0a0e0c0f0f0d09030c02040c0306211113201e0f09130c120603020a03020103 66
    0x1d0340400c0f079100c0c0c40e00c8075114007822030f9680f0240c1c103140089002d03041d1014102843c04581c501401005411081e12100007644c4910620303120700d032184842c44050281c411001d8007200307400140c2044401c0b48000408100c442034007a200e1410051080075190b8259114602c10a01c65881d4010116001c40300d10800b41c05510010140581341d041d014226081074280c203000c80d01c0266818114038100416400030840600c0e01c080b10318091201c40350a000341091120b0300071020580c014000c070540d0030350f16115030340401008400d0b11810300518425540704140d0003640346c002e80442c035a01c00d0280101390303900701c1010301c10000490764103000b6040f04e200c165120745840340f45403819a03a2140d03000880f0011800450812280c0140f08403003075a0351044a800f0000b004401080461082100440b1118000700c0381c94000c0c00d511560a8866420380ca41c0c0528000e6411090040c0e950020136801a1655144030914042c2e1001c000c0b500d190102031750040003c10100019842504240b010091f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 906231357 1250 906230107 906230113
    0x1090e10120204140f0a0f02090d0809011e0c0605010e0907061115040506070311120106210e06150105040614091503010b040e101d0a0e0d02011a01030203010506160203 74
    0x60b054244090386006a070030080184440342800300e06d94140c0256a5801030411045141c082c0f010001a0200100d010003442040003040c0c0d40c0182e0300609203802d50a50219054580719072901006040d0392080c1011240c20385070400200ba01144049818800d044880060070524181402514400c0284080c801c032840b6035881404041c5880000c140218460002410135080c5580080d058405000007020221000d1100c0c5012080040e02d01d81114950305000348441c071001014100c0d81c42080c02d080c6010309100c0326010029000400301c0c81198450b4540051b10014801154a03110300e105080008107454a1010450341032001040032420003044000a2112a000081c840d00242d10003404a140400c040006640000085520a401040380482c6604100881c615658040006003010701a040012041c08095028200211806080b910060452103009029050003000c21210203003544588104e5400f0b8020b59050f42d030700402c9141025400030410b40d81e5140000240e80c144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 906232607 1250 906231357 906231371
    0x60906060807081f050c04120614090d0815030d1206120c0f090506060d021e1b100212011203030f090305031f060f030e160f0501090e10120204 63
    0x1c1010003407280181040c0700589190b840c4041180b018014840000d1940360503c003c00c5010700302c64040703a00359204607004024150140c14040d0080c064000f0f45070001e803c0e01d05020060000040300e54035059030b580c3d40d1400341c0d100c000d10038858521804590305940301c84400500c96000d05182e0495080601e8005001540d9014501c01d1a101982c1a6103030080f0840c02d01140b10004110b402904411205010b42d0034000045806849030740101c071030455000c501c02001d6540d4030301c08003001503944095912002d1b0307040c88020340c040084401082e8403030080c040c0c061520500aa031540a514122036810740e2a10086107012814288101c0401d41e07100310300504044944500c48031940a6a6035075202d1604002d101c6070038081c00074440340300b11129070801505034420201d03402c4440e98500412034542822001745000d0040b0700d000000b100f5a071011460360b4625040101711042682c46008841ea03a12400d849244d0a441d90b100d9504005824021007030980549180d061002e8400500a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 906233857 1250 906232607 906232619
    0x131a041a03060408120a05060609061c05011e06030509031b12040303021609140c0f0d02030c03090d09060f050a120227030c010804061104080303040602030f070e0d06090606 76
    0x12100b1102190310320701c0421503803070000901005d240d100da0001d0003081107041160010f60301e80513150ba014400d10000603440e80500c03d2910850001500503814440c13940c54026030030303074500b84209030b1007810001000018000d20030701900303002e0b1b90362402851500e00111a4031400c0603003900007110301e00c03c1c0b0715100c1c1c1d081d502c0030040c00214001d13070140035154401958803c42558030703400003040c1828034408444080860f600d0356009150300010759910407001101179464016031181c0e08400d8404000c22403030501c0040103620039907124040d100d0800340280169403030500c40c003800c00015900640a0302050164000301a00542400e00300100308240300030030282d80c0060341510700c2d4001006c00b0320b1801140f0300a050310b194124041c00700b0700c0311400024406000144090720f09500c0d03103041943c003880d0741d00f150068461b50003600d0b0791345441e042000c041e5000307aa07181400c440d0300c8006040148280900e4000303110084c019618121152110740160501c244156101c0e55035920019031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 906235107 1250 906233857 906233863
    0x40f0506150d1226010305011a030d0f031d0f01060f2303010b100c020f0625020a051903110603040f03030b0a0e2a0405030303011703070b01060e131a041a03 69
    0x800f1380c0c40c54100700030342c11481c0907800c0d01c1800406c0061030704092208203980e81c010480d003486104030300c2c0104642100e050120044c0c600c0b0102c41c40740d0103500c61506140c00001c58680083c039421070017400810ba07210380702c82d404c158520440b1340c42d1102032905003996803000c409281691004001241c1c08440d02c1c001000c00480c2103009022a2407200c0c80700860030704410740400c2c01c408803040c1e0b0414100d0224500000002c401e01506002421841f07002c654450145c48040c01c8003406008084100c902c1c00720554015000c29540d4081d03101c64500d4625100c42124800d96100700c0c094580c4485a90070b80103414400102039009500c0752001c941c0c1c00758203030303070300c2c0b04a08114000880045200000c040428000c1501b503458004200601058a000085a0440d00c441207502607031350307181100344d00b9030040f040300a100350b107020000030f02581d003d06982c03407195040344c00c5055040307448041000c849840c01e445001c5515000b40400500c1c0c10b84c040b80e0071010800140441907035000010742 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 906236357 1250 906235107 906235157
    0xd0f0807210b10030e0615030304030507060206010608180a17091e150705060408030c0c030406030b10031b08090f0a0501231909060e0105040f0506150d12 68
    0x7092907968030b04000c9442c1010100401c00e2250504001c02e14100080b04d407038050080c60700464403603080c5e138040c040d182001260011500907080d191115118100251691020f1140c0300016071982c5c007198803d0200700c4004000e9034400003d00f98003044c0c0d0b5440b15414035101342c0d000c1e10981405450754584640c5e1005c0c940c0d2003040500162590400700300710f02d00a00d00500d01140b942804140c0010301c00245030742d003260b0000145520382d45c5110303071400765118418803560540000f040000d04d450b0180c000a0400742c0072134180100b900d5024088040f18032030300081a01105514280d03040c0d50155000710b41050030a401e44504851000840745054036507a0f04950981d52013900c01600c0003005401218030444200b401c5190904071440c142c2c80344810f44114034242e0381c1d103c1508000d503660001c2c66071403000c402400580351a050580c80b1b030304049801d4585020340c100041703101d03100728019918040000d00a0051301880d03100c11103600307003045150050108850007403503a844607401e010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 906237607 1250 906236357 906236417
    0xb07150f18030f030b22180f020f09041a06120304060512010e092509090f02100f120f02090a0b07050d080411091b1c0e0d0f0807 57
    0x7036a01800c2c40c0050621000b242940c0805282034403c00d201c1c1c3d240c03a03030038603100907001e2040e65038110b80e2103840003410060799500412152201d000700708a00030302610007070350007203c1c4103111034000e0b010301181540403140100200c28940412101402c03c2d43c03059004a00904900701c828000c43c3c1c030500c0c540c02a004100030840200d40c030540c0c0d40403d07034241d024006007686d00c011400d02c020195555250344e2150201c851303482d040a000000301040300c4004006402041c000c904482c145003c9004d00010180e00815884040b60101030027800402000a50b550354031402d109040304480041c00518503c256440d020050050b45a40d031900400250500a015554520071850201d290206880c0e00350280a03101d820800400c019400c14580000b00f550407080c035594404641040d0780d017084807800d14180c003044c4c056680120103200740d171064103003004128603001c440341595200810422480010740c0c0807a645050b51003010025000040d60800c1d0310000d40101e41c410803c0f02d41c503101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 906238857 1250 906237607 906237641
    0x90504150806010807060f0807030f0507050306030c1e10050705030c01051f0501080402040f1b02030a02070f0b030a0905030c120d05060621131a011e0b07150f 70
    0x1d2186840c02d010050060000d0701c020001c2d1450704002405d19850302600c8002c1c010031400050a0701e009230484c205500034034000700b120346031000c005055504103599890184c403c038081140c40d800d2040500550845e03100200400481c20010095038403071118040042080c24070009000900810203406911b00309000840c1c10703d40164400284030206030041e0841c202407604200e1a40c0101c8000d0f00250107807000319811074407006600c0501092030110354003400038001b80180c01d034003101074104c0700a6075003030303d845641d03030401803402c4030707680c01503800141013007020903180c0e80258819605c0901c170703074140c9080426031600700382030183c00f00a94201e000006000e229212076407040641c095401c555050400117201d034408a11101c100300880d1954141d8041901e200460100c64050b40c0d0021058a420040107a031511080c000c2c420041c021150b04980100e500ca00400034040d0360200310003034284036098039981c80e0528040c180000840e51020584060b003894011820000440b010f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 906240107 1250 906238857 906238859
    0x50c0d05090c032116030c0218010603050a020405010e1011190b0f0c34060605040605060412081e0c011407140a03020d0621030206130209070c0309050415 68
    0x18141881012129042c0004131003002c410b400405005031420000c140000562443c000c0c6400d840d00039100001a500c002a04000c00c5605000c40f0745038182c80341c0b540c0500c143e0719500c00072416400b40740582404201d5000c10030302c0c14204007071129084900c0c2d281a44003010913541c45410050003441c10309034103455203800c105200c041c2c080c1980140b589480310703130646024555440380e4050741c03841c01c00c0402c1d00050000910f880c20034803240280d0840b0082031009103841d15a000342100c1c81441d005908110b4000798614012082c2c07000c80d41c0140c00c96101c0d41040e0b8038240b032a40564070a541d01c4c1031141130303003039914021000350070100085030000541d141c50001c06801801c0c0200760400b0408040e04202880380d03010152003501030141400340e15802088000806400c0c6030b08032280940400480d02d6800c400d02108164540c085e03003e0302c040361191802d1102039290414040c0d0070500042c003207408144102011200d1078042e1509400c0d860b15000000e00f0345410801420107520000c038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 906241357 1250 906240107 906240109
    0x409150c09060c02060c071502010222030503040b03100b120f0a09170d021e0a11210703033308031315090305030712030605060715050c0d05090c 64
    0x1140c04808802414040c41807440c01c50300402d4026010002402000040b56030407941c02c0400020001d0411092014400011414024005d4102100e0310010000f815036031005160b048010809998200c0040c2d80b4040c1840f05014140c2e002070700300c00308102c0c0b0000019000c02e071500a0162203e494002001c9410041c0051500e010041c1140401c1403601410400048064000903045c51150340e142340c81e8154001034200038041d80480c0c440c00c1e580640d1103107075540c00000030302014000b078403070030058443d407800d49c2e03a200c00700c0c8810003409040441c018001d20f0068041d00c0301900c40d18011a00e046815014500c100a402c0140c61040d00007560301e40351101c0400701710107032240c500150306200108400400210080c42406205070907582c1051180e0310451811025541100071640d03101d44a140c100c608500220017100041d01c6c01c8404a800d18000c0101c5005d17540100f07032000d07a00c0c0420090001014094025084032000300710b50b01c1c0503000341c0602489441c9207001b8001c103444c010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 906242607 1250 906241357 906241361
    0x10806060405150904060e030702040510150f020d0c11130b1c0506060f010c020a06050315090105060a142b050106110d26190c110c01050f040302040915 67
    0x140a50038540d01003411443d4680310700d85481d5202d03802440115501c459980514114030540d00041d4015040400300301c61105421200703012142c01c01d207120080c443d010403c1b00c03082038200e00403005030002011034614520a504001c1ea8501410388010815591000500714161004404105039144c022410745481c1181c0d19490201400c54503550000c1c150366025150900100301d02c0c0700d4406001000315130f034403844034000030f00d0307010340380194040e100c1c040604141c008848a590b14400004029500d080c19512941204e201810705402d001d04030000b03a4109003c5020311010030750501111880e0001408464082030051091000000001c0c00c1c0000390703941600400305000c0d13090110884030400044020503c41d45140c9044a541140030b000404a05112480071404850041c4588648420400e94090440803002c01a480b0100d00c02e46100c0e1180c0e040d04030507004251100055400f60004081d1090404811482c0c0741d10717640003508903047c011058401841e460485034034038541c3c2c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 906243857 1250 906242607 906242611
    0x918190f0506131b0804080f12090f010c0507200a0b070611040b090d060b030111030108010b010e033d05010602060c030610110a050604050c03240a1d06010806060405 73
    0x440c40601102c50342251140e9990402281c0600700089100040c05200464054510b8511100003c60b0749d0000040d04521004054690140c140074014070901c8401e030504c19500b0300c02458540a0502400303448464082c44600954000c041403410082d040d81e070f400910101a1010058250300c801d282e080c000111400d41441503c400c00400c420f000d94022310701654000c5030125600ca13a120a5881d01c00b01034001c0102094040d030078102011000b105a402841c1a1500403000b04611440c14004440007802ca02c66283c050300300b400c01101034581c03030711070100c000500704000c90110002c10b503149044900d059450942907442006001c83e65060180540240d0b0b0030301c1060031414954005064141c40303010900c10f200713a1404208802d9801e114807015a03030000103a420a142c982041c54440c0a15414548203000c2c031560202c4017a24141c11171503846c400300005e401c982da83c0444070000d10072440f01000040003d4022503014904024040c0a000304070b01030040b82c100103090009032940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 906245107 1250 906243857 906243889
    0x6070f02040603050f21040927030c06051303080a0e1216030e0904032c21010f0e030403020f12060703020d060b090108070804060608070602030702090604020918190f0506 75
    0x30088034007100301c1c46c0b003099600782c40d003020f00011030000c0c4100005c5648060681c0340c026108050841080c150821400390465015000c2401656076410300380305001640c0c103009010800c0390f8046103141c031640d401240c3c070003030010484400a10202820109400600e05004480c8048042d41c0805501c03a860500e034040a8515a0160405a40c05007046002011042c1c0a11210320941d000040c032242080502c84094003205280b85d070442c4000318100c00703d0390b9031141d42c03c01084100d482e02500c01c0444801100d006541418219802c010200551450f0035900c2000403c0e8044a41c40922185005014a440069884201404d1a000e8942076030059403d03610a100a40c26079801540d0f007984060305140011286d81d03149029001081503812144180c411803001017101d6800000074510702d0b0084400002603030300d0000704070582c03140014540d048181d21400354003e100211016800087c074513049008019101030ac1c6003128050f42c210045107440d51b081c0840741c20032006846443c1c070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 906246357 1250 906245107 906245143
    0x612020307051005072a1d0105011404051507021504060315120303050709080f030405041a030c0907050f03130311060c0f0d06090c020604021201150506070f02040603050f 75
    0x501d9030740038000d4080d00f14003510101c804034200b692082c400001030301000010301b070f402600d81c80318803481c8040241140c180f0340c40300b84400416590b015103590b5410b04504030744186000e01b40000e00240c2025455100969a0140072040069407603215020104801400058075103180c820020b040c0c0d00f030036041c0740410a000c9020700049003003804940007550142808a21501c5446080f20080d00651156146d4040c10381c1d80e0f031124002000401c1260b070219800d0060340003030300e20404a410301da400326506078840f158a00f41420a40c1c5031960124407824914245802c6d408880001c0c0c0c002c449881d0084d2410554100709900190255440e102100080c10326180017003000b51203124000c40280c01503004100000c1c416a207802c190054004080180000e41640c00080e54915058400303e119550302c15050b41c2c41e001c14440d4500c0a0750703100725441701c0c0f031a00c1d00380b00c82940800b10030b44400c14075805400143c3c4582c01950001e40c81040202904800c00300c0031410040040d5200c14003403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 906247607 1250 906246357 906246379
    0x2070f0215040b0d1d100e010e030301050604120c09060b0306150c2104030c0806160c0c0b090609040e0d020f012309030c0d030e07090501030b040b04020a050301061202030705 77
    0x22140c1d007540c181226429000407a00000786179540301490b2034402c800c02d0b01c00d17420200000180d80c0c10070360301040030300700a12442c4500b07818036849002c00d005140d040b10051004024584510790f00380120340c015035242030300303c0c1c81c0d1080505a071000d4003c7d1912240c0001840b00c18240038440350380c421180707080c0904025299500c640c80300505e0380103a5000040d54101c14220000b07100b100c0003907502c410b0100708250313a83c0d1581d841c0c0320102c4d000301c0c0d905c1074560b540e1a00c2d8000e845103400d0301d0380031040600c04c90500070500b2094010504c03190b0041810b108034650354840740700e03003242e014410005124804400100034580f02e60741c0c41c506101c0e41800c6800214905903003000001d4a4a69003c00185d075075500c6152450050344d1a01c1220700c00c0c1403001c115541c050f03015072000c40d00c40c1e080c1c0d0700c201c1e200c00c00d030000c0d12002c1c40001c01d2000e6070707030004000c81d00c1c4900f0a500107100601d4400140d90300c0300064207540494122a000c2924030281c0c0c411842c040107001c2c01084d040d03075488605 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 906248857 1250 906247607 906247619
    0x71a0a0908030a050c0c010c02060103060c0206041203051b0f090a0506041d0a0f1401031b061407020d0b0118050f07020a0803040311120a02100e1b010c0602070f021504 74
    0x50700000e055150804c3c0c65402140d01a40e20320150f030600c01404000b00070420420f24000e545540038401900c00c285011001564640b0200e0914072031034000234070050728111440120010103000b0aa01100c40d603c5d1001c0c0c2813004a040145013081c8906112612101c24808100c4620402e5004a00c02c1c1410801004000906004251802e01080042d4140c3d602e0504840c09043c1150311640d5852900e104400c004c00d12010850613a4010030700564140c40c034010308451311034140980b0380071071144010395102c1e5540b900200390543c805018410305288a81d0f0308640f0440a0700301c242120b04a07000c01000d00c40c14070921354020340300c0041480d2828901c10103911021210300c0504061000000035003814000c4060007131210780e41c0101c0e107806001c549900c2454110040e940f00501800d08030f4030400c030b880e000700031031001e803031b80501014100d112500410060304d64602b81400303e220f804002090742031000d441000d005103030a02150f0124410002a844c0404520001c0394082c0400d20013 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 906250107 1250 906248857 906248873
    0x807061b020c0a1514070c0e150a12030c02030f01060801180c0501030b150a03060608060904051510090218040c02070e010b0d11030702010f0510290f071a0a09 70
    0x440350788802030113000c0c1c0601c20440310900b8003d20283e9904000560004009070300c40024216540030801006d41d4540b803440d400040256448250b002c410104140140007038403d180320340c2d510a090018613900940d020905181c140e40340e03080303a07035980c11080110100078010000c0d0b01c00c60300d14a640c0e00201e69100041e07110680111410140c0e01c1c690401c0c0e980302c1046102098041d10122500d8001d9144010040c2c29540180c2c4005400c01c00803c48038100700e5a5a80900d91201c00b030029585003c829601191000708030200400b0200c50005914010348010003032281442403000b0b078490440e05010a84614441789030031548250350402c54440c41c0041c150644580c2c01000e0340c0c0340d0101c000d1201800101d4400c0b80c40030b200000740107005405500504944141c414240b00d03d5407001f520740c80c1e40c040380c81094040c61030f1202070740d48840c070304064003285140d110b02c0c0c50401081c81c10b2244130303800003130b800ca450656400411444030003401455900c208081818408400c13166102c0311 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 906251357 1250 906250107 906250109
    0xb0108071202151e040e06010215191a0a0e1605070b0c0c0114160828090609241118060a090306050c04170d17130807061b020c0a 57
    0x445030401250a040490b0403608071390461032005410381d201c83e103a102d501c4503100706442450143c4101c40e0380c0301d480d400140d00c4d03901c10040003081c1744000c0035a880c080080c084008121b1381780c62102080100aaa903000c1140c0a400e6a80d0149402d142c00039034280c07581100c1400100303004082c0b11050000c6c082c0059980c4c004013504003540c45030f4038a4803141c00362441c41015681c5a581104105090007031000c0004070216039511041c82e80c84040b0004001000c1d51140715500383c2d00601200050f00c40c0d089041c145108800008061406d91101350300f18080f0945040c44d007002010800000d041801848040b40c00c64001c0342c0751400e07904004207540350445c0d4441c000c82c0e001c03903041e050320300407501e110065802060900491426044507030455102d4040d00310b402c2c0460135117140071030700000e521186000603114540451301cbc8601c1034900780001070250405100f41030400c000200d074640a003000307511400021a640c000540310b00071000c0e4140c1c1034000c42d44a407500101c0759981d1400d841c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 906252607 1250 906251357 906251389
    0x70308092d0316031d151911150105030610060f0813061a0411040803040e0603070b0403051b01030902031c0207210c05013f090b0108071202 62
    0x1e481650084464118012201c658410f407004146010600d0b41060303101c110381e840e07241c0300e1241300420002c000c20358070b685580e201c02d14014000e01182c60302210b4101d00400342c0d81000c0d0b83d000b11b850803007840c04140c0001d40098030440c800400a13420708002c0d040d004030344800a00480c50628000034021312240c0c0081c001c0106c0100403800c04100301c1c1058210a800003400c0c03000d03030109000b40c0920243c411542c0c0c0070b149000c65150885c1412001e44c0d09030350300900070310302c2c1500d0222041d02a00b0064040c0703525020307071100003a642c559180104002c42c490800341003111030200d22084919100d0b010141454200208000160b5010601101c544040e060349070250003404412840c0c42020b40004d8202614142a41650800c4004045055114404125526844400464132424036046a49a4032110604104c0110740400d140c18001c0031154060300c2c00125110020a035454444169000d007612801482108418800f40c0040c00ea10070015200e07605907400328035103501042c503070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 906253857 1250 906252607 906252673
    0x5011e061a0702040c030e0312100b0f040b2214041505011b0c0f03030e12030c070b0c010f02040b070b070203030c0a08180601030308240f0913080f07030809 69
    0x403c0c0481c040e40c011207c240b4088104c0c3d407504030f10405802091019a20301755080049a8005200d680540c00c986040e8141c807089424145041d4402185030031100082c080a140664680003402c40804c044d070040c81d1f0741c0e59803500c0b403440c18144030880b0703021013031022074108004050240d80d0300310310702c0525110b0392400c86801c10900d04294007504400c2e0000d110b4268030103000400d15034051800c10301d0340d60131500801c0f0b03107a403002c00a64034443c003000a492034111031030800c101c00740f40000c0c08008044200100e10104039285140c120b078010b80110790b541d5008600c500070b01c255610001e6108800e40015841c500b08840c3d0304009014800154042114650004d00031040080c03404800765505811204556140c0c54090b0541208450401c2201072140000c0310007549000c81c00c3e580355010b41108003400044061008101009111561042142f0003000004170024018440040f84a400c01c1d01c0c0c070024640104003002c098202030f480c0c0c1c0129a410380c0200c18040d08040c403407506c440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 906255107 1250 906253857 906253871
    0x105041511010c0201020915040e06091f151101060501090b250609051501030c0510030e0d050a121a0603040c12110103050f042003010905011e061a070204 68
    0xc200d44903428403908000c03550808008031421034054001c1e00150804961412041c4e841c100e60f2035040c040c9105001070f0254a9000c140307241484248a60040c2e40c0759104280e502074860a618016000d038898404103c0041c1c20343c0700c60380e00c80c80c101580c0400e1002881054a40b100081010301103000c0c910b9901e00001d80007441881610b0f240000c10054034903044500c00710305105000303122500b810b0fa498010368881600c1c0b0428044145e05803070f4086401e00304107040c5001c0c0200700090019842c181a5907640c0c0751054002080b0506003030313506c3d5482603911014010b000300303084003181d0460109410200c1d00c1c520100100410038455100b0388400b9240e0b690350070540c0b407103d0a41d00901030b241012002201b0b011040c181b400801c2d0b4203072818403480e212610030400b0484201d4000c1c25090440c84822080e000f120701c071104022000303002054014607522820b003119002482c0c468054a031a00c3c4042d407410600600d00182042407014843c121001840307215071041c050024803490380e80e40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 906256357 1250 906255107 906255149
    0x20a05010518130f0f151212030507030e011503032a11030c0d06021905070b06120106051305150402040f03030e03190f03020606030606010917070b071a070c02010504 73
    0x4c42081005103440e01440440700440a1200030a60508160380300044864042008081c0100030382c100d40d4040310b03803020301038400e4045000b480098101e404240c1c40c0c034040782154500b400340652120501c80c0402e4854654034000c0c0001d000c0000c411403c100640d9400b10305602d00ca14540c00175008880d04c400c4940c20f0000a05100030400e40321341c030007020310064050007a2139024140700341900844e4140300c903440f101990180074401009040d80c05880001d211418058000c0084468510001c1542e40c2c0300c00005450b14024900c0c4030b01c0503519010840020030000803036003002015242185494207028425105072200e000180510400000104850720200240c0ca40c0300d1541800325094040c030b01c0e210300d6807920341d88107900511920340894081d18001c510075001d0a0161200403000385003151851102e107400c14405c1a40c000c40b50001000590b6100074003030544291000100444c140e01da130003881002030a00010030120b00601030040c0d0308142160305a46088948036a42c5002c55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 906257607 1250 906256357 906256361
    0x20a03060e160f0921020a090c0c110904120c0501110d02250b06060c030405150913151a040816030506070c02060a0e1c2f06040603021c0507020604020a0501051813 72
    0x26010740c0c0350b40c9c40c101c000e4040b43c1e441803040c0340151181252a203100410390400080c03090a07140a0906204160540a03e03030040200c000b00910030070010440701c6040c40313642507540148107500041034000480c080c04034404028004e00c0c121004140f940000d25495411840c60000d000364000c2d1400501c8071494802003064a00810008020107425034410001c1c28480d00440300c01d80c01192429a41100040180980168828100c440e1049686404140000b5203d094070031201d07210300304000b1981c1c00041c040d541003c001c0c1c1c0f00c40308000c2d107940f03070591901c44000c00b50300400130444400401030303540300d0403918035500034504955400c0c89480021a00e002e802e140b10700600c030140a401c10081900600300344004902e42d4507111910703441d901012240f03009010780c0d00000c10001404024001d5015010200000e440c0003e03016919420000305d03030040c0d031108050307071100d0200011881c14400c6580a001c0a00c0d100d401d0100080b414030504c02000804c41c07042c40c4250654080301065 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 906258857 1250 906257607 906257609
    0x3350406020901300614010e04110c061512070608040b04020a2d060203090109121a090106091a0102101109041104140312030406020a03060e160f0921020a 68
    0x769180100c0803040b40010010100d00c00368070303400341c0c2042130001e040d6051013101101c6d08010707140c0c51508140301007048010810591518070340c0c0c034217114004505c0e504201c0184031f0580b10340141500d102c41401c20900070054551010340e030740840b41c10b12401d588088070581203580010030306496211403000480d40c140300d8111050503c043c10b20111488452882080c1c003940c00c0382c030bc0c1201501c50404a80b2072180300ca499012551000381000111400c401c42d189039805010314020380c040d484d440e0326442200340c072402c4003691a600c041c441d050a40c440c0045807a10b40d034000032030410420020b0345035205981c50140340c9648000c92500d40d041d000442d100b281e401402003240380d00c1c0014030304c00e9801c80d00403551400e080c981046142d040001c0d221010940c1c60340700d00e0840d47d441c5e03113040182d40031080701c004040d15060002180050300b0600c071b000c1c402100301281d03218400c1c00014141d403081002c080801c404035804006000482d40c20100c070702c1d81690b26000482250020420030b0500f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 906260107 1250 906258857 906258887
    0x150e010f090b0a050708060102070315020d021b100204030b0412030e16081903021c02160b18090103021324030b01080d1403061c0f03350406020901 65
    0x100400d41c1d0410a90031807092060240100c200403d44034020308a4001c94111406400b59110f00c40900105451490120007901d030701e4000740c500101d005550342641c1240030f42d01111000702a500c030040c9001d00034207041080d402021802c141c9941c80d0101c0031840500084c00000c90101c0030180c95110790084888000f011044503d012500e40d0040180002880703500d0b100d006002e55030400c000643e0410040540681c018071400c00c40340000103d1003602c00d014001c0d4400e4042c02064021000103000080020309192030315854603609104030345140d00b8a4a00c250080d80061005030303180740c06051903070b04000f00040c20402c0c42c20000004c002505452100c01301e030b110004100300d000034106042e114030f00d082c2c82034a200c03440d0645680c4c0d41210310000d000000c2c4000389080c20110441c0030034007030b61044004030520b036864402d415206441e00703500041e5001c2c0344240d01c0066002d604c1c50700c94a283c04081c01070851490000b01031001c0d1009003806d0700050a00400d03032187d41e81c9c0c030460704 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 906261357 1250 906260107 906260111
    0x15020d1b0b0c18010203030f1f030c06032c0a0b07020307081231020114070623010602070509011a090a080105160e030d080612010c09030501060e04150e010f 69
    0x40008042c0d01075045260f10343c010300051000707014154400310607a805505002018090780d2078602102d030f114001c54441240e00d10070813000202013203d4044843c010a4251400100500d01c900041800c011000f9042e80c0b50307004010140c00d02c075000440c0c0444035004010b0342d034251140301c4203d0a621801c04080c1c155032001c9407820035200c00c800754601942140100002c9204180206544280c84000d03100100500120303000240d4000e4440e456040d451b420140d02e800100c0e1750724011100c0c214400c2c602c0b9501d900c4d04914504c03c540e05940900741900007829038500c1c2c80300068107107005005152410240f07031030003101d00740351100f40e1300410802070210b018507494049082c0285011616003a02c00d10360b00409515600603a0046613989028010340782c80c505080c82664401d030050034658200303400d0081380040300b80030312a2001e802d84036170360203464501e103050150075101c5642040524142e490180000920200480390041c02c03c1440800c002c00340c2c81500e40180700741c9002411040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 906262607 1250 906261357 906261361
    0xf0109050c0f0103091a070c2922060b04060803041514030402090f1801061203090e0708010e18190312050907060c05010b030d0e03060115020d1b0b 65
    0xc519515040e0040d640c0b0100300700325800460944041c494080c1c031428452803484940d090007500e19600c001c0906209150002c075940b0104450240380c840034100480c0400b880703e2864046070700b40c1007485000c484040707011504800304500d91444008041e982d80e0141c002c00b649460b002103006260302410790740c885039200c402c000b483d02112100341c0002d410310700740d000c8862042c041d02c1c040d42d0042d220641d10307910414195059040070b4218240c000c8244020f48140310240101000b600e02500a13440240c01032402031308803101a0060380c145e82000080041055002c1c035207504440c0d0b014854030b038980354080c40c6200040c00e02c0c0e88810500038980c240c01311f20251904482c0e0300c1c1c0b00e41e41e002c00030010072495404840080c1c9200300e841e001054204040da105040c100c030a14001d8000145080c044000a890a1199162400032414a903120f8850346024400203005148164141c100c44880358002925010070164041c140300740300d014081c520021b42c003a002d04650251600e8424 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 906263857 1250 906262607 906262613
    0x10815120a0b1f0305191b15030b010c0203060f06120a05030913150501031e02040306060302040509030310030201080403171003050d030c050403140109241b051b0f0109 74
    0x500045480d00c0e00c215501068004070144074000404807074020001d40785d46c402c40b84425455200090003503d400d81140c0d0031014450542600750000c0501078502101c100d02031030082c0545030f00114580c144525441c010700503803008540154094204a802c420a0f0348000002d5a0012029214101881080c140314200a4000010301001c3d50880b40702215145000c0d0744002c2d00c41c103010920700a520214208850b5019400c0340c200f41406000d103104600c00d40714188200d0f08a54800d6070050344450041041d400e0511810b0340003050f04000d545540740001c0c54052903001c1e0300c4024104603110001600b03251182c01e421081811413003240c9621705249121a84060840c00242c4060040914110700c0c80e00071f2140e08440c0100e80c42c0d160505281d40c90b02d03407211603402142c0030a07540320b41d400f800242201940e0300c040340c002e0248282005010800608803003c00600078040540d01d41c0c0b52102c0e540045c10340b0220395003110074503000d407400040542003440001c1140f00540c05e0841c80c00030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 906265107 1250 906263857 906263873
    0x90a02160b0603060c04060519031107061413050d050702130f15230d061409030d0b031207060e0c1203120c04152003040e0f15010815120a 61
    0x10b20000c40131195545c541120071280d0b44074038807410000c20410800d030006482d4040b070021814121342000121509401c44174450f42d808800308071603031541c40407811001e000c0780100e030f03400c007000b440b5841c074103035155036006d60f912509020041481000310701001150b5032145a440706d0f5041150603c013001c50b65000b100684281000f0b40d420b0f050b1644041181c05400e40340030b0301150244032410348000d00b101444800620301c03038107035605034644107824807101e4101011802039410000440e51140601280d00c1194400c070740341e43c442e402c80c100c031004107035010054a510170b402010000d40302c403440840c10b00c0c2c04440101c1d01d03000409491160603150b0084090408000c0301d1042c6c0d0501c4d901e10740c030580c0e42d02c40c07402030541d02400c040c078114400d0b120326544116802402c3c070b0701c039580030201e1403a4074580050b8007901180004030100101c101c2c2103981e10303030043c0c041c0701c401c0106800000040d0003000b00500301503c81c80c40b0b0704403000c41c2d03a4007010f201213280b8070401d803070144881d4106001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 906266357 1250 906265107 906265111
    0x80d0207081213020112110409231501020a03031d0607020709180b0412020a0c09270c05091e01081006080f060f04171303060b030304060806090a02160b 67
    0x90201d007484000f4081c108150a0801900c1e4140d49a510010210780346400504004004058030307030080c4008101a5007030b03c100e02206502c070503200d0a41d403000d10203286241c40140a00e51407001802c0000b80340c2d800045411036958141008a000e03400d14140203003050300c4604c50a010b00c980410710003015000303e8420259100301e9020f000032819503101c200ca212850700000c1030b4401c010001408900001d07403011300c00f041481075805040c00c54640c1d0004d02d42d960400300100d81e5440724200e843c80c24900b1082d41c00303248000c0c40001c51403512200d4144c00d00344160b600649449001440300c0359100494202c40d8181c448086555856022a643d5510084800c0ca002450301c14040340c61500002c2c89100500850000c28213580c0d8125603644501001d072013261158400c1400c1502001000054040840c0e8103070004441031441c00c0031010340b0286440c0b0f80c00b03030b0410417042c40b1980d0f01c88500e5070b011105640e40c10715611283c400100904c11150400308041103c40341078100964400030134 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 906267607 1250 906266357 906266377
    0x60f030a150605010e090411010c0807111f021c110d0327050607120b10020607090b03010b070602160503210108150a05090a050f0a0615050d020904080d020708 70
    0x407655444000641748400380c8480540d2000340d4000040002d1542c80044032a400185403440c2c04070b1003a66030140980001a00716910202c1c050350040e0b40c1050203565110440d2545030514402c03103620065104c036000b50044c00c1c820910b0102d031034100e005100c2080c8184040003101e00d07070400c0c410300800810103035580101d10104010302c6d02a82143d051a403842d075401101500103502c55800a503183d56104c0313199012952603401042180e51030502c081104450307a009040345203000b0a009004e0040340d0881e0300500000d10040c440f54031403106440180741c1c00032005950300746100791240c1040310b00400401d60703c800500e80c00b500035a41c00325003209002010a40ca6a602c84034020707207600c545140c015402001d1710005080d081960040d07a0040082400e490526050780c81d01410945c044006003484d90040c0e828004001262250054003904c03041c1c540010790400d00060754071960401d002e4032400c98000841c0a0100c500115079a89008807400c6554000602c0c081915401c00d0441d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 906268857 1250 906267607 906267611
    0x20d120c0c060f031802030715030e0102070c0603180b130302031c0b010915020a03031802030f0d020c0a050604150207081606080a1a0405090c06070507090509070609030308060f030a15 81
    0x181c150325418568208141d46c002c010342001c60414421a402243e04034400040644801c4d00420100c801e00c02881700d240030b0f0198110382d50070618043d055441558150030340d0882c038501000811541d281854014a068016509407501418124910300400c1c8015248080c0c040740c0c0102c4103810b51007202d4540003a01c2d95001c00341e96800c01294103040120000160b0000c56a6000107403095000100d994030b010348100c00c481c001c2c2c004c2441c080714200d00e401c0799446144011400c40d0100b0554004e85400c50301002d0050070300300071410f02d0140344503070525000c02501c07032072480d40244440005070020034119180700307881d0300c1c0000408008e4450722001c0350402020900d640400d018002c2407800e52890034101803034004c1070000424006203110321900903031b03000603c2c82e5075480c001c001e814010310040481c5030914030305c1811a8000b4080203c03e900400040003199042616070301243d8040c1002c2c4915991034000c01d5120f0500746500707901d4003035503164404200d807000c04020514070390102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 906270107 1250 906268857 906268871
    0xc1303063b24010501230c0618010c050f030c041707290a1d1c02030c010806030a06090203010902090705030a14130f021504082107020d120c0c060f03 66
    0x520311001103407502e450a0402c188010b00c0700f03501440310114401194800744010403505440300c0d416400030940c40303900b500500309000e0f200c0c0d1441c04800b12500350000070403014000e00c10141c0340b8800e07500d0100301108003100090b00d00c03044405a800416076207003041d1411141480342600e90203240900940035000c1c801c54201a11200440694558040407991030240b2882c6d095803103103134518100c0d0442c2000001d0b80d1107030302c400003a041c030318401703044031100d12480303204050809040d14030503810040c0c20420000c0c0703540c0c0020f00280c06a0070500020b211502400442e02401c0e409001a41016510091043e89988980114810314034503c08024240c500b4085030b8000c038068072601d008480c1c58548002085d8211050f1401b03602c0104070221507196401409a160040e6100c20301c1c681000280f10844841c590b880003405d102242810315003411603000540d803101621000d0301148840480d80f800b18040d0741d00b101c4181c1c200c1003031001c0350750300c96006281c000d181c15144002400c00071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 906271357 1250 906270107 906270133
    0xc03033903070b090d090303121b0e0307080a030903020d082106030d0e01050406110c03011a090c040f141c05060703061410051e1603080c1303063b 65
    0x705d000321090f1555600b03240e030340366032004c60310b0882d04c60b030b64804140d45414100428800352081c0b0101901501c1d4583d1a0003110101418003a4035802041f0300e4004450b118000b07980180b08105032941140d590a11100394200b03d542402240c1901003c10600c2455525103220740c0c6801e80310740000c0b41144d1040b5811801208d119800c80f4049001c04c00c1484248082d5025010301c11074146900c2c1111540686003000901b0740d0f40104140100381d410038034160040c00d10070f100356803054000014614003442d100340d120340c0038650b102d0fa180d101c0000c540001e031940c03801251150300031219282649107929041c0140c5890042d5605008a494240300003a280d1040d140d0b000040c02c021310300f03608950703016400c0e181a4840040340c9400c0010b241c1032a07481314004040d0000c050541407200d491005c0d86005030044a02070030514084000340015a070081d9001c14010960358803000214891007459440c15000000340700b00d0440c15030401039002c04059000484100000100407241203000003c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 906272607 1250 906271357 906271363
    0x60f09140a0f11011b0f0317221718030c1206040204151703031f1206110d020c3415120903080a05090c03033903070b09 53
    0x401c008004840c9040840085607505070440311805060615000700d50700c80d00c4511000e49294012500d440024071130406140d406a82440c040d26070900d66003e504248088241c89245488000d1a08404145e0841004424020f018482c01c035404d9417500c5003000e18801c103038820fa01c01203074002c0c458144202c0300b515248080c07140740d8110002a0155494030f4081c000a000d403600301981b083d82d46030f000118190441c15850f156031014000d90740740e040155074075450030580c6c21142c070000c03121501400101642d06007240c0e5640d1154000440404e85884000d0902035520082c2040b0700c0800e002068240120700f03100c1250500c00c1501803050000909520307203000a80045070300384c00c02070602814545943e24038007400070f400c0c01092041851a80c005407624a20100c001030784200600c0883ca0890045603003081a040c080e000e090101c00129682c1e000b10409401c045448020400c080c4401c11103180d0f507007041110301c40c441000e406080c0d9480d8401c40c01210008400f10000b00c24002c08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 906273857 1250 906272607 906272623
    0x1020304141b01050c070312020615010c080a1d1c0c081212281d072d08010c08010f060e06040314010b0a080d0f0201060308041e03060f0914 62
    0x1414a50050b0040b00340115084d810420407401e05100f58080800450320040040c8a02c10440d801048540b40c0042c1c0003112803046001141408440005240020030780016109524a40d141062008a4410b080f2020b00c50f0759401940007044950100701f8201000c461075401c90007114105009541c0c2c03801c080c0d55100c1c11640f000c600c0c80034083c10701c41892026015400c106c40320040015450b00c010301440d1107a040903e00b0300303103550703070040c0c1c2d18060000c103d812010500d0000d070031080d1510054004140c01e2406900d030100076030041000a0011144400290407890002c0103070341510340004e412190203025180390401c1c50000011068032801c0780c1170b181c0001800580c03c140c41d554400700384c0c4082d040551119502c403034071225551940d81181c4001c0c42501c00a0200704019600904007804005815046904100c000c0c8049901101160122140328810840d100621622078034202480c0e00010100c50509a0800c4052940e8000d40c0c1440e000f03c02c0d01c0906101c02e0a02c641d04c0c016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 906275107 1250 906273857 906273883
    0x200907090518130201030b0612190e0c0d030809010e150f061002030d05060627040b01030b18040c08030f04050f0a030f03030b040e0304090e0111040e13060f0c020102030414 76
    0x1500741c070300f005503c2074100021000b4050003803400c001400311a03035180715003218a00ba100300410461070103040701c5c0c01a14a10440b01c0040c0c041e8001440105441640c5580003906200403c0c2c0407480d16002540302e0703403886c403a5505507403816070f050903914100c0a050741c240c1008481c610219000340340040002c4074074075941c0c005600e003243c1610848080d05e401802030358403040600200200d02e9189600b0391031068203800d0050081100002c00c0100c0d401c3c8100701b0704051503c1d6828070b803034880043e10300700003051140750030065072030b46050000b498168111001500002c42c40b002a034208401a005030752048a070383d405105030b0024004d55029611010b00002689140c41020030f010381e100c41c000c0c502c00351000c034810340d20b104014590790042d0300144030709a49a010301e180313480a00c2006100d8020020301d624140c03914113065651403000d0880c0010300144094a0100104c0341c2c00314111150100e01844240d601c2d80c0042c4c000e4008417003d44490300c0c0c03128a501858408220a002ca200f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 906276357 1250 906275107 906275131
    0x20d0e0d08060303120702011103070c061406060405091008030f040906061718120a02030c07091b1d0306042003010e031911100507090902040f03200907090518 70
    0x81103c85d540880540502040e066550303074294100902003003c000c520420b21901c86002d0030400e03152010882c1c41c3c080003441d401010009004581d52890100c4080b1441110351041c142c07903800b1054240381103030b404101c4034400080c021184586034000340c0700725105030004100d0f095072490141d4202001701d110b554079040c504000b840038019040c0c002c0b001115001110129100c3d04000d07800c950010491902581c004600003556210802c2440090300781c0d14800d02c90181d041908901e00742d10001c5035014802c1d012151840c00340c00340100090318400400310f13895420b05042c00381281c0300c1c5006500004558003e40411801d050182d5074901803014001c1d4a45540c80d0303c6861059025202c0104208004008000f20170003007001c0203616180000010345400c102c00b0152019409522180a007401884200b2480c40d5030041c0001712608a50000c1c28000d1070040c0c9200c45901c0462250700881c0041440701c1a6400700300c01044e50000d4a0340c174181001d400c0500d14a450407680000049 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 906277607 1250 906276357 906276367
    0xb0a0b0f01200d0815011b0204090515250f09030314040b040803090a050d050c06090604090f090b07090806130c1802190809060a05040503090301020d0e0d08060303 72
    0x1d4400c4491480780e221480440402c030846814140c24811000c41c40c00014001c2030911841001421000f80418402d0a100410b0001030000d8130901d0a0343c00041e1240d41d4031506102400001e010202901020601442041c07400080c5041e48a0000281c005581106100c0b4450309002e443c440c080d640e040e40710601403070700e9a94111020300880c0c001e00da0002c4280000940480058040c101070315107180595202c0f007066040c840d0102003036000600c26130341e80f4442c40108101090350f0404c042c0507948aa0345840c1000031642e6440f840d4401581c0500d444110342c40d406981e03124031840b52049080040a889400040700c0903c10350189031140d411400104e4481381171060001d00440c030860a01000540e00d505941c08080020820b42e905500040d08406007a022030052401103803604000c6810b040100806a56110051481200d1540c400100d07040c407000304280c0b042500020001d6544a01c00b0b01c2d80009040304d00b42c0301d50a4840c1c0440780f110180502c0320b051081c5000340c0114100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 906278857 1250 906277607 906277609
    0x60909081602060c150103120903080a14160807060b060405100c170301241701050418060f1a03280812040b070807110618190c030b0a0b0f 61
    0x440001c10201d03841002004540402c04081c00041140e40303101c408294158035500300f00090030007600c2d0440400c4400c8106000140112042d200507443c01d00d010322103066081122030309445085a410030315003c070750204040299140c0104011480380c90107100c0b0129503402d00030940183c3c0100c1c0d500441c031540740380c0000c0c4a01900c450803401001520f4624800c0c440b034034410b90017138005c40482c0c0107030404030900d07180ca440c000318107092514003a0b50b00d0759a80d58031a641501801440d2060b9280d00c0364058045142201c0022540c02c000c080000002100c04100280400c10040156402411040c04140b4000c20031119000918490340403850b5051000d003812410107500b116140c0c014000d002070b0317524900550303104902ca0000307201c041c100070344090300100700180340340c0802000c80d080d01c1034510042401c5402101107000340c0342020989104604041103d06201109081000710005011f41902607a046074020f81502030a6103d20700050181d07007004070142d4020300044000081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 906280107 1250 906278857 906278887
    0x9120e0127170d020d05070b010e0405160b03100f1a07030909060608011409070906050a020f011e0e03030903090f0402092808161a09061c06090908 65
    0x1240144042048503691501d0522030070003100b00390803100341d129901c02614503404010648007407050b400c1844c02c04656a4400200e40300501038443c14518030f102007001c005042000786d02e010100c00d85000b402d81c41d450210450341044600c00780382c2a00d41070004240d901b54100030b054442c088102050f10744500100c410540c4401c000f00e00f00511144005502405407140101611030b43ea2802c100c1d5140c070f44207449400c1c0e0325059501c1820b048060000b45600040c01c041100c45030b00741580c071884494426403c182e0744c03440b003072019400c0182d5000c0702000440403010409403c102000603181e03501d2100c0c2e0320701089035450502d034020002003e0f9468045130f41d480040300104050300d0410500040f441d42030306036070381ca81c102c1080c181e040c55640034098184003515490004104002c400007400c01d03151920710400490014518002d40340e0f20303084046416409002c1c21240e501c20030301101810324600d00690131401032401402013070000440c01000906900401017a080240460055103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 906281357 1250 906280107 906280157
    0xe01021b16081e160f050123030f0c16051e01380a03050105040b0f0601021207081603050d050c040e01060f03060f0f03142d0106120609120e01 63
    0x182d881078010070300c00c602d5000c050700060170740600e03a180842c0ca004005800004a90501124002108420f20f142c002c008152a44054652a0444a038491070240302c024030480440c02018005501068188180042c0e040c0e060005050607006000e0910340c9a070889610080c0800c042185564040392280040041d100b0365028035081d81200b000c0b0360002e00e9465080e441105d559440f1020003051180682c080d660241c0f418040030085c1c9007000001b911380c032080300e20300f181001c081004411b0141807019111103984070b4088280210543c1006803250708058440750095050034001110110400242d03800c440d4000d0340260140d0030440140c40d2002045060700800d5550040000d0321090740c20810020310780c028000d0710072410340c141090035940c240344441c200e511940c1c250500c014002004074a1100301c005621100c0140d00080c0e000d070400d0b600103402d00e40d00a00c003501740030460b400b4001651003030400f12100d510304030060380c4420302204418041100f07040c20700c41207015078650070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 906282607 1250 906281357 906281413
    0x2090108071404081c1b020a090c09050306360714030a150f0f0b130e030f04450509011518060b07080702040f0e01021b1608 55
    0xb6060680361155603290a035012200000caa034206100280d007504100c03c61000400c205591078100b01d203401180c2846018420000065621031a0307442d40c074480d501c009d000e40030040a0f940242840c0e203081300380c0448012215946e1401d020b00e2005840d84c1081304a0151426018102e501c1c5400791a090582c0c0031b06410b5058015050703900001032140c02c004044403540c40b0300141c0e0300d056011501c125a80384505261451802c107141c038040d0340350301c60740784100e82061000c181004556041c500318002c44415044203800841c01144007102904818840715030103441001c2003488000b00842c00d242d8603146400f04910851aa58110b415008580d00c04d150100100d614040c2c030840c040c15151583c0030740d002410481183c0c192449501a0720020b001031040541030a406844400191164a60003807083e84d075103100e0011300c112600f03c1c10000c0e034a200215180c214040004201c0b2003440d1000d51076010b1207402c0340700581124100d00075200c90a00a00c1a0200e0004c01d82c44000f26860b51 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 906283857 1250 906282607 906282647
    0x9050a081f0b040c0810060512060409290703050a021204030f0e10050c010e122b02220e160c0c0308130303030e070b07020906190b07020a05040209010807 68
    0x22903455500401d801300c0859514040d103403422142007481c42400d0341041d42004010030604500c00929406260003080854000600c1c03201403505409910803d841c291505030341075401e029244c0d51b602022321400b101e482c03d02c240e0780ca14448000701e01c0f2f0072010007003d0f8a11400f04000c40e1040c0d84c0303c10448030b6800c0c031040c0340220000045452020002100009000003a02d4100c0301c0d0a000703a0407031700c480c60000c1030b07221081d10a4101e503004100580709401e02c0d012000300900c80b1004e0b410120f210140003159907041c256814140105184620036810740180710016004003031141c101d108506012030759205545484080390103030045082a40c106040c080040042002c500c0180900101544000d000da4030703615014081e42c0980c00c00c91620b422240e010400380d00d81804440c81359a045480040c2e031382d212000584210304151407a854201e09030400b0031032102c154024602c00b80201c0d215003215564808100a80c4110341e02e240c0010003240c0030030003a0340a24034000c4848007101c18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 906285107 1250 906283857 906283871
    0x71b0b061201020318010e0316021c0605070804032c06070c03060e03120f251e0f0e0f060d1509050405010605010f0e1f050d1b09050a081f 61
    0x6801e00307a0300203644042d50302040d05c10211120009228144403006024080d5040081a0059011740ca0382803070b01030700a0340c0b0b40d180c00d92481403154480d0701441e404441004982484100100806011102200031800601481c4c00203001e0000c16192019481000c400200d50b500511030fa58010301c0c2d08172134a200205001c00040c0031030284006130500740c001142c8540c0c0f82600303900c0c0c4060241000c041070030484284000690800204182c2d58503038141b920842d80c4103030048840558954002c07090a0707031101900c02c150742c05080000703418440e07911160380300d00301d0040020241c1c00e40c604079403100b01000100030381d00303454002080303031042900d2007541c655a0308c41c200c0503120100c3c2e00329400e035911203081c4403545c2c101003402180d81862a08505e041803040c04261034040813820702081e4110340c4054035803d40f00c0d0301103070501164400c0900c5007036010326240043c0c911400005010514544c0049060f00f089803e6404484100b801480d954039818205000310140c035251011103074840403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 906286357 1250 906285107 906285139
    0x604051506180d11091003050307030c0c05040507090e070f0509040f09080a03050f0705070b040204050a110408010f1a24040518040b0a0c230706060608010e071b0b06 73
    0x4004010240515101d40d0003401c0d040030002009001040310402001b141c1c401d0021980c0001558045a80b40c10965000c41a608010401c1c0d0b9480e80191340c01400c01c0204498240d124025400302d511a06032490075896103582034903141c02030026400040c5042c01080c0c40b81c5055080314641c6c0783c80c0c032030010f00144982c0303032a42c1d10741c041c03c5d00101013a226001e1204004600c0c41c801d0340410716181150520400e036a40c0e0401500103031019211315190008114005141d40c01003002c3c1c030700e42995030754965035240030030302910524039025415803512008594078001038203003004486008000d446207003000104902490002d4132070307c28030f0505110102d150f484410071401c401c00802c00410061516181c14001480010001c6100c6400c040244000c0c0350000c0007100c031000802500101d24606182200150049000c040d040508159002070081d82100d42503050b035102011442455640e200b0669014500e04107007100360b242c0354084404034030104070980d0000300c01841201c020310861 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 906287607 1250 906286357 906286369
    0x1031802010e0d120801060908010c0f0305181f050f0601090308130b07030302042c010b09010c12110d0903051c0507050a380105040c020f0601031a060405150618 71
    0x503600c00c01045c101401404141d810080a01c01001114000d201440c06c0d403000800b400304581d01032040c140c9900209184000548148100100000c2281c3e02003a5131400254a40d08070703c1e02208492820b0089000c10041d198401d120302010784900e640c0354516030340c455443e4844030b81070940c80001c000201d41c1004100013030461074060380c1d001d45c0b130380c0c144217516405128200541010140c100b001d0030b0128502c0e011306044482030400262550920700c0140c50081c00c81030010503209120084c0e4041980100c0c0d80a0742c002500101c40c0d003080c28010980b000086404054401d03401803482a03124000640354000d07105036450881d007410302a80d61a45460a2900c0403124250700c80b042d101c079000c860082506003c1d0f510300301354104013845020100410107019090003241c68401440540d4000c10000c0810790301d58040710400d6a4074141003442c8140300810500801d10100499050300e070a020300e03400340304220340700c01c02991482c00308221a40102d0441c03103460710f40c215041c4560740351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 906288857 1250 906287607 906287633
    0x70e0907091a090a0509100b15030f0a0507050304240b030d080108160501050904050402031e010b011b05030912190506091606120b040b040911010e01031802010e0d 72
    0x2c141c90210700d01c0e81c100030b8480002018841e0691610701000050f290000d6002c1005c80d40741800201803c018010410320f41440720500c0c0d41c460000140010b01c4802c8241e46e03c5160f003290108000d89071a00100c4840c4000e40c0c2c0640031414420b2100b0f0b600340350000c032855140e081000040d00c00907030800b1a0401c48001540b401081410004100c0c240c02400680c401c120030000740d411035030414001a00354082c100d00e850081381d890b0b0024046441c01c003c43c40303030714420030805082c50204c0f001041c007070700501c420a4006142c8810b03080b81c580f030300e4010482c1180d102d0091410080b100c070901c100368260048072007551107070103034a91012200e05100205d8034040c1d0b010b81140e250200c00b03140303091450040b081e41034003104001c000c0d1a1707200f48000f00300c031800c100124020940c080003402414440601d1640a40341158690130850296030a40344d480742a00c814044414020040d000c07a0030503041d1800c3e0602c44110b0100547c1b04818a42101000401d030303034038050843c0ca41c20751071401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 906290107 1250 906288857 906288881
    0x603080a081504092103050c0a1202090901030503070c0506070c03060903030603080309010c08010515070312090203150a0f0618020d020d0f0b03061b0a1407050610090b040b03070e090709 82
    0xf841c3c10b0410903011701602940d4a05800d00f0700480c07c1903502c508091082c40100b104100200400c150070025540460b4070a44000780b00306000d50710f9040c40c0381c4a91000000301c4041c1413010b03001849040c80d43c2901e080d00e420150022003189903072500006000c0e146411002c05a84060100004d00544051802841070400000311880000009000b510701a00003030711605440452490034215803003222111645881c3c60f101d038218035840071002c2d044226009501d03024481c518070301600028022881450b00440500c080c0040541441c01c80b502d43c005c60404296010f4501c00e0701140d500102210120703c0c7c00103142584200d0b800040341c264890b00c00503240c6075003245000c4d180400090f074102c02189000082240f030500c800d82580f10b201d0859091111403104000c0b1490712401340e41703020b90080180c5500d49030030702600d494104503001d1100f0740c526218284146003460701c2003000c0313508054003c0c5011130820314072041c42c110080881003a480b40700300220705020781e4083c0e0070030068 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 906291357 1250 906290107 906290123
    0x910050c0f0319111c0203310510050714031914181302030405011d0a020108011404060302100201050a05060627130e0c1002010603080a08150409 64
    0x1680e15115007003241e04400316034603074024440d40c41034402401c100726400e00581840300d1000d41d140340090038500013100308942443e060301c803102c0c41c40d00400140790a940750050241d1031a49803c0015810040101e00290703046e042006004500341550b0200c81354140d07041841c00d14500d552858182c0101c0c03010070120760000f1400c1c2e400010300b10b620014188803801c1250404c0c03c250003c1c0054061f00d0484424017010502510141e100c0107400303070417011141800c3d5620310300f50401c01e000e464140c01541240d96094444d601500020640001180e4165160315403a484c240120202003550300e149271b03200b0390794600080142c0d1790000b0140140c980e80c002017601d1406c01303491421039038020003403801031204024104060501041c0300c940d0118140019000d83d003200d0100c0c500341d5410540c10000703498807409240c1440001600e4580301d4086503524100300301404103d091b030b070961100901c029030510038005540c2c09080401ea100309041c2201c1c0c1d500300c0d4040020b058502d064000d480d924 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 906292607 1250 906291357 906291367
    0x4030207050d030c1709060706151a130b0405060703050d0609020a121505090f0a0906060f0305070909030e0d0f020607060b18071d0604030501050133050d090206091005 74
    0x201c048081401d0983d030f400c40450031b00541c6804100184100440104480d983c0c5120781c00e8855401c0c0800083c0401034181030705144240c0000d00d4580c0100b0311040f002e484c0c00c40c005000d29540c0100d4040d50005002503081a820390340680fa507030802c04c101012240c0350000801e01030401c0c4050002c1007a1a41e4409840d031041614804551118407a0320001c0c2c40030702c2c280125120400f0700c40d008500c2c10ba2801055070f4422420008085d100720052030581490b5000401d903034009021019240079000f031303c404542c0e0301c00c1d0740101e80c910ba10090200f04880358515036441d09000315095035006404c42c401c030603d0b40d800150141d005540488035540c1d100705882c0282001d900040c1b158055481119031410300c8803002d812618020f0600344290300031209610030f526800141d5004503440002030116584440d0101120410302ca070201c80801c90640a100d24958800c8107605005503840b418506181c1488583c060010200e007030360001c50402c142d060584460104201140761595400d40304c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 906293857 1250 906292607 906292613
    0x150c030905060a051602030f04060c080702090c04051008060306060f01180e0114121b0f040609020d051312080c0705100603051b0f0f03010b03060106030e1501150804030207050d030c 80
    0x5d600583e0f50007086620901504202c84072100448041d1002c90400107666021450281243e204401000b50487c5070b00040c890b406800304050800c1c0c0e28221220501085150000c4442da00116000e0303500d41c0c400000b0440318140035601c00d02d01901032500d5404441042c64600c9a041140d000d11906d00c0440300411503412040451850910101c400c7c07515011540d001d01d60313900210503810303100305407444088010b5641859070f804134007010300107100450351900e51600a401c1031481c0300680317040c400061003051074042800081a070244400c480748144000c11a040c0c0001440305440072002c201200c0410780800c015144440c2100021a01908501c0c040c2e0400e050074040b50100d002e0b503000425541e8440c1c00310b100e030240c1951000c031414107030b0000a0140612002c01e6415001e00d10010420950541011481022590440c0c1400c4500703e641d00441109100f40b90242c58004035404150f8800e0340c0c400d40203802841141e40c00c50316400020aa0302c0020b4007140407600442001c4c00f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 906294964 1107 906293857 906293881
    0x50c060f06220b03061008060c090d1e030f0207080c15040306090f1a01030b010b09040b151c0c081906091a090a0603150c030905060a05 60
    0x700b078807500b4400070040400d40c040c1030080c00380c600003440c480540c8810000712802040141900d9540d006490081d80003c54800da000101040380d00200c0c2243c2c6482d140e00d070068200703000007215454017038000c000e94202c500c00d54002102c2000b84034804101c0707180d0310400743e0304480150800b41c9001c102e131103160001409617140110120600c0005604aa0302070b00c074101c0c0400c001c03a510581c2150280901c00102090150401803000164074000f921100c2000307000840c0020b1103400084510410f11000140c02c0d00204a00d1300a040d130001000b2800c0d892181003000b04415680209000360061a501103000c07203072089903810655900c9003001b400040802c2000032a210542070840f01081d13540342c81014180c010a143c00c503a07102d0902146c0c1e0002c4203405200c00e00000e40050208102c0b550241551084142d010960034807095105506003a0300191928080b906621 = true := by decide +kernel

theorem cover : BRFrame.Cov 906115107 906294964 := by
  have h0 := BRFrame.cov_init 906115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 906115107 ≤ n) (h2 : n < 906294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
