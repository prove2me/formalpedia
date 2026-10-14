-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2648
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:10.033051+00:00
-- url     : https://prove2.me/submissions/70700660-141f-40ab-a824-ddd1322af6da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 476079136 ≤ n < 476258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 476080386 1250 476079136 476079179
    0x2090f060a0f0602100f05010f12210507031407020f04020d14090705010e15030c0a020304050406120b060f060d0c05090d060c230301060509030f101a03010213 70
    0x30300c41c0c00200001e200e06910020407564000c2e140d001022034040042c1d0703d04001e1015618a0b18006101048452803c10161640481c40f09803035111441c2c060746118140115141d081d21024064030f03c2e0340d1110080c01c0e024843e90354203003820a984580e40d10307401000c1e0029840708910703918a1050a0a5000d01842c040140f000300300383c40800c04c000d8541e0070558030080c083d00321010900080d60003518110402d4001c2d1884d180310082c060481415001c0038141080e1600002540f83c02507200300f007614040e1000400811920355615000c80704003a03400c3e030880b0201c0002c40024401d282c0108040781070000604803d20301405918010010000c18005c002444010b201c20400303610348090030040f039445103000040038000608040c0040c2a00c20424000e281c0303000000f5a800340e0081904d046400d1818016215010b440000b0f00f040d5041183c1c041d1403084a03299201d1034101d4000404c042c10f94903214128140c450181800d030f11841c1c1d07000402c1c80e0304810411140c00781e940e00110790700c107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 476081636 1250 476080386 476080399
    0x6030f020328030f051c05220b3402070f0501020a050703060c0504030605090f06130305090411041d0a0b060f0f0306041503080a02010f0207030f080a0f0e0f0f010902090f06 76
    0x1140c0050040414642c1350171b42c017584d9804100d94505008030b110100049401400d20103961540c0f07014505100505401e201d640649004103003100d00050903d071303480309059006000e56a00c00c025035039003070392058491200b4401000140340d400465010503403504100a4000c2c1d609640f030301b00c0903181116208003000020080003021803040e114050080741481c0103803500c03a8141240519084000d800b4010300c1c001e036a050700c0045c1e080012148007803410388000c00c140840f1044c400300e40c000ea61100002c4c1e542082d0070740020100598640c031641500d0420400e100304101402940e0084405004c40c6850802c41140340c60350303c001455000900820224581011400381c11140c0003a83c000c4902a83c00700b004500c1c07940a0050301c13a00c1440080844c100412924020030440300501716005203c00200414810405038012121425440e0402d0054450040480756202d000003001521401480300c5001002e00c103004078503090380c00400050494903510003103061120054859030f2b1000713 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 476082886 1250 476081636 476081647
    0xb220803070b070e010306081e0f19050f120d050a1103090616110304030605180a0c080106120f060c030f061e0b0a082202040c080a1b0f0f050d06030f020328030f05 72
    0x88200250700c4004040350000c2c00c145464a0400e00d0910b10254989007a08054ee811540031101000e940604040178000301e0a51144003506c8000c11100700420303600c240020400c0b4500000003007c50148050039036104440e46504002c5910407000e49403898141c0040200f0030101c4c40c0b50300155008540b00e41c60707da0891460321580c0c40d01c001c203081122070340d1006008202c2a082881448000c00c819071344ac840b04802ea5882001c80d600d003c0c8010045503440264103620f51203513200310a60400d60200704189600d44110345528030601483c840c1d0280c02a2000c00c82c03441101c1a81d80c002015180c0c0340031501c0d41031130500c001000a1004000e041789001940150340c460003410004265a06c4010480c24000210410f8403542900041c0c08040e045056071034a43c42015003100184500d081c940c103014900c3c0403a02e52062000c0a20720a0800d1400300900800a001500c900d1007102280c0840c104c540220003040900c400c0050503500a86001340482d0203620000800810383c50a1807030700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 476084136 1250 476082886 476082913
    0xb04051c020906010c031b2105030405030d1a0d0506010f271122060306050f030a1101090506040305011a0a0f03031404090e010516090b220803070b070e010306081e 72
    0x101c12221003908da500c0595660400310300c144d200d11400190500d000c070302c0c1d440c2c0f580359140c2e2481440310103840356940305804901d540010401e2405c1190061812074aa005800c4c42e5503034450130701600306002d481c250001640d000300242c0045050401000386198000c50840c0002003032160541d5904079400c103c1c0d10300b1810100e2180ca0390f01c08691007504814280880201210000d070806405218801d00c0181d01d9600000c5071181d45600c4410148071071100c000480d1124410740c030040d080440401c001c020880d040d08502242607900c1d40f0395034120090304c10403620300111300c6410b001d8605090f09001181c415030305090f64040341003900f8074103940c0e901ca81d4112206411a4a6665136640601040f852000301ca41c0e14460a40f4290b0806810481110560b104400d000c0f003441c42c000e013447e42d05945000c9000700508140e0705036030302c1d80d0712810b069030400012552200010381c01d03884482c80398001d100e0701050b520010001d00d000361800d455620144022999030300c0505c92080300f508c28 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 476085386 1250 476084136 476084177
    0x809031c0503010305070e09030d050601050d09060204031205030606040b070f080408010c020d0f0e090901060306091211010912030b120d17103605010b04051c020906010c03 76
    0x8400c480d6650355a82d0f1660410310704120264020f00b0428001c9424081c0c201000010b5800140340b40ca07000030340792124001a581c511038820118a22400c1940030002d000c01503001e042140e0246595081548000c013007220244002c80c3c010354401c8040c081446103e0880300a0000d4500c280741c50301400b041c41d200c3c401150055401501d6903911b03010400b10081d414080c2150320803443c1400314027880c09400141c150f01100c0800d1b4001c4180000040c8126025042800296005801040f2181090070f029505034500186400030410502900c0c0d801c0805104404200d07400911040cc41040c00100710080d0443c084819800307040402c0042116901b0301c0f880c22070140c0d60300c40811645900300085680e0600500e00f00d0382201d1340340d0030419035000e01c9030581000ba11510040d100e2410550905006101d201300d40c006929000000c100d00b01050300030000d4031421a08242c141d224a41c0105600b08000710003500038243c0c0000c104994090561110050322038200003207100c1c2d114200d800b6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 476086636 1250 476085386 476085433
    0x6210703061404030324050d051002030a1410050901060e06130e09011a030c090408041a0a091203020a03030209040605090c03040308070f090312200f07050a12080903 73
    0xb6030410180c14481050b40511a8909805d0340690b12508030b00120130101e51002c4030720999014228000b20b90040002c18410f04a005401400446d12400c0540f29407000304505407502d1002528000441c1862414000220490348000c000351641c2c1c0c20306804684429030142c020350031603001d014848442c540c043d600000750407110130700009482e04151490a544c03501406900c100c40d00741d9207820b035841c04988001c050708240c8805801d91102c0c07a1202541c4945c3d030004007a0740d11160a01c2032400000010071038402142c1c0d0360088103891741e0500c1058202c611000700982d00162071140044c2c041e801801100e4001000000c5899440c8042007002e4001ca810055481000042008040e00a02090b400840c10b2521640514110700702912800d110701024040d01e00140c41500038a200750042c010500714810310f40044090741c0c64103680d41065111690850041032008900750404050000441e10743c6951104860200d07192180f04e54042250240c00d80110810003080c0803d403002c0c910b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 476087886 1250 476086636 476086661
    0x50117120f19080f010902070503070f0f02030304060201090201020610080318010e04060603091403130b0c100c02100c1d1e03012904021216020114010611010b0303030621070306 78
    0x1c8928284984d03d1881d103058102000443c4180008408108000b0030b45e24038680c00001040503400c18100a9440311400c00005c0d4540b03c0000c001c2444d5a042d000118098800e0702103491030b40301c00960f10190a5240030300002507005000c0d50981c8003203100201d510610604000a110201c0d00c08141074075003503000341000c245c44100c0d0408100d41c00811180c07400244001e14101078031205a900883d02500c078520843d0008034180e04a0b040c2841000b0241d0807901d401c000c0e01c2d50b00100030351110387d0b1450301e581c0305181404048000e40148006552400700d50384540c4004210410800c01d01c070380000e81441c01410324202a150b403402d01c030340b000b0701c004d490000d40640060f80038100441064820140038500610109040c01d42c0340301c010782c0017521000c0c82d600090104e0310881c0141401c4010000c1c00c1990f400004550f50000980c42120340000024060081c200090640c0d070300c0280c0d28907400c858108243e0a08035240000e2003500d2001c1303026201c1c11035a0f0344407a42520100368504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 476089136 1250 476087886 476087897
    0x19051222080f1e120708100b04090618091101050a05040f170d020106031203050402181f140d020405180d02031b0a11100201091a0604050117120f19 65
    0x3c1c0e18400d5036420003c10142142d181900c1c0c02e01d0828200412035002d0810710038002240c0100d1a211224801e4001500d0396034100f0341c58680e5011280042c18082c803807111060b80c01c0394401c00c10500340c0650707014644c03c03400086419402c5801100c007035014071601010407c082c40f02250302116424100001c001c000038400207181b132140c80c9d40c1801002012034003036a140030401c00001700417040041c1c1c080f00701c0c00c00040b141c0c0c90b800420480a000008500b0002903c0308000e4a4007050b600300c213510141c00c86000400703807240b04001042c0241c0d108180c2c00303c01080c4200051800350080c0303070b020340e101810381c4001c03901800d41c519151401e030701100541c00c04511003142451007020902d205140900906040703d854403070340e01c800710461082c4c0c01454030101d850000c50013500a54086503001c40c000c0d1192803007139504a4480001e03141c2e40d104908102c00000e5801a441400c070b01d44500710090080c241701c90b41400500c0d403088600b6800c45500b4014900800910303200300c000c00c107454454 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 476090386 1250 476089136 476089147
    0x1050f03010e0102211003030206071404030501050906010306051e061e100203090103050f0720070b040e01080105061807050307210e0705100e060c070b07050319051222080f 76
    0x59031310905c0c005202c1d448080411404001090740010f01c81e8001046051817203d01d2440c901e19001071040d81c001130619820f01c003c0c00300391000041c04904a0340210030801003500c07454500112006002c0386060519040004200c039840c00b10000070786031000d2400d03420000c07504404200c05034a0000000c0240e00082038030b0900b541c00d4001c1c25801035845030a03900924240f50050402001d005826200000002c40809450010040f08016003c41c0594a459a5803600c903c1d0030300d4402d000c0c498955080c03902103a601d041502c210510091900310050040d60781c800c085903103030401028a4100a402801c00f03500c010400c19141c203140c100b40004c200c400c42120f91600d4038165a2101c0e0023a510882181e070a540d200303110341131046088a506030703603480c4500784525101003034015545855000900208100b400401090580c80482041d080e03003040580a030b94074007400304041c40c01d0604000241c1003007021103841000b0488044401020030311600d844109400001480080510000340c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 476091636 1250 476090386 476090437
    0x80a062a09180605010f050c160b0d0f330b120412090501050d0f0212070e030d03020f040b030c071703070314011211011b0f020f0108090601050f03010e0102 69
    0x400980c4010218000c1c00400d04d0300700001c00e4220100441c5082110201c0c9201e4003e0007071120102030702c96507040b540460740310701c0c0d008103aa00c02e02c40c0da0815450484c3c0e02504003082e010320150302c0f1240c0c1d4440c0344011499180d200202c3c180300750813040188101c000c101400ba6201504e61400354010b10099490149001100720355503400030f070244003010002300000e81ccd0080407141c1c0c40b4030305500401c01562492500001c4d004600ca5000c6140d2904100901c003940600741c074081500450071200115551321040c0e04078480c1c0d030340780e0104503000c00c8180840c0076002d0065800880c281c10326440e00125031500a011000c01c56110072000703000050080790b0f549405100c243c0d41c0c0901c00c800b180e5140c8010407042d56103120b40200f1000c0201d01302035050b0700900e89040440001e543d01813070b007107440c0750046041c040c0c5241244160324075000344055504c541c01e49845401c10781c009141c00d0f4280350400920329026007401e58150740f908100c054014087c0007402001811b842d2031400c0030301002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 476092886 1250 476091636 476091659
    0xa11120318031305011b020d0503031e10030807031b0b04050c01050c0a0b131202030c1002030129161b06050c03070b131a071107080a062a09 62
    0x540050075520034450780e086280c00c04010400c442003402c04110456054142030b8001d400c209020754481e00c3e142c25030040c0032002c002540300b03030106098031518001e2404022121321083c1c0d61400300070110343c02400061f401c08028101c0034003c3c00c00e05440e683c885580d144000004008803041d020300401d2108102d41086950740009003401d02da03081c10009408260740311150840500500403a0f004644500c105c2c035210b214943e0003641290030500904806503407640b1525002400340300d0100241c603407900501c2680d06035004911401c1100c0c400c80700c1c048030302c4246606c1001c9000c080010400c41440d0180088240303120300100600c0c0400304215843e1400654403420500a0030005440402804400c40d489103601441e410200d03201c04886500200316170f030b0010311a04100b42c851018094000b4402d11840c0340d640d911840991010b6202d40310b44551040200c9640260f00c4000083c41a030055408a42207002c081703c1101031502c40c05412901139820070205051540920907440b561 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 476094136 1250 476092886 476092921
    0x70306092f09220f0c21090b040201080a0f0c0e0a050301050c03010e0408070f0f11181503030913050f0c0715090614010905090f0f0706050a111203 65
    0x80c0309039800c0480c0c84012a4062040800f259100c26060700c06880c0c107100c0c0e9001c20080b000c01d28040014581c5020050403440407028001c0c2a8920007a0910041045000d044025984984440d465880d60f90055542240152520f45032544a030b1150301c40302c03807902c541c4007108440ea860072140170100c41404100c01e11a00000d000c2d9043c0f00c1001180d018010131241111604e0300700403500ea0301d41c10310b00c0d101d0086030380c010841142200c0e24024403008c80560444203009060111440440c0003c001404c5030510b03200782d811312110001000e102d41d01640d01004140501a04d02e40000140000d1090030f1442549407950398540c14005200c002415450b4400780c40c035516403401c2481d0f10303030210742641040c1c020311160b224000710003080107580000514001c00d0100704069615074840c6005048c04480c540c01c0c2d4899501000440000011200040d540c1f90024220b030609242c030031103044d40100c82c06414048080c0c000700c4400e40811001ca0b40000f040c45044d124103000c0c840410034080c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 476095386 1250 476094136 476094221
    0x8041502060c09010c03050c01020307080a0605040203090a150608061e0c0717030a0f05040b0a0c020a0c2603040305010c1211030a050a0608030703050904050703050112030807030609 80
    0x1c0400c001c5440300c2c580480703014503c24200720001c0c840514003103c083c400c04070040c0e1326500200c10700c11204d8105140a000d11550703003041c0240344d200c00900040b400700f2a1b00480590000b221200071401568079111036a02180300802c1e0301d500d0b1940b0070b1034107105890301e00f100400320317060342d00650950480581108801c18468544640b640358460151095480ba100f000000008100060035030391200070f100d0035024080c00385150605000c10003820031120403400c282441c8a07490340b03501c04203204d40c03010790140d00b000a1604014450f00a00d80b03000703a00782d031200c0d141c220720000f5104002510082d0300c035100114604500c001d008200031040f02001c00c0007418070800184900700b0038281c0358441032241e800121039a6841026003e0314059004580c603010000e00281072561050003464050001c3c3c5007031041d5100c100c0d0030ed041302c0e424030480f607021344181d001100181c4122812900203186240201c1d0703503a2100d1810007200d440f040802c0c0c0c07040300c680380f44480c00d58211074220200d19 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 476096636 1250 476095386 476095393
    0x5010501050703050c210901350c0d0e10060b07020604061d0a08030414090f0f040305130f0810050405030a0e210610170c0f180408041502 61
    0x90200040c050340500b81e0001c0a00a010500907040300080124011958546140011000d56601c072017965070302065100d80000c0080303440355880200500c5040780003420440b9840150b12040402d0100c0030090044010404100441d119a0720700340916095009a14003801c640c840500f01c620803105264441e101009041c030a00c000b41e641c6e607085c2c804a8201b07042910001140e01940c0a4004a0200302e982c0852104400300711000c0000c0035000b901d80a50380204036400001c10032007d44011030300c0441c0303541c000c400034880fa0f1101c03090540080c40382c1000c608100000c894a42e100c401600480100040320400700030101d402c1100c042e0340c2542c40740422180c14903440f0035032640b00b9882c90b0424001101b00009490b1100003060b15040c155800070f02c900b40b160725107103880743c80645100080c640300c4080410301101f90074882e0111900c080080c0035082c2d02505002483c88107405290344480151802c43d0503850302c900c80c1c0d2090380300b8614266914100014402e01c3d03096000120115070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 476097886 1250 476096636 476096639
    0x13623060a0615030203090133050103020301030f17070b0a0203100e1003021212070501021b031303020f0103061e0303080901060f0e280b210d0e0307081f0e010501 72
    0x18940100c0c03c50fa2468540503903240d80320440203014201e0100701001c0c1c02119400c2807510b0a1050403a0741e1408140712003c08503645d04011010b9000038000030f0000700e081341580b800a240c1c2485561280e81904400d8180385081e140c4d518180400c482d0710500130b070000208000700214008040180c500d41d80800100e0800c8180c22241ca00b490000902914903080c4011040a04120030600350285007161a6a99003d01d4414081d400103405100c560076203100c04412403c022040d10510303540c4030000c0740240d10319000c01210b205825403042c18180e6812001ca40c80443c8000512000307924482d90190078034610340140291310060141406900d4014140b0407400038074a840c003110226454080c480d203034a038003e060740c1062040c01540100913000107036049400d80284034001d400319100a4224140d030000c294585295005042c02d401c10702109201a0041899060200c0301030201e5481c591142d01c03c501d81050750782c030707031303d50304041c480301d21030001c0b5070007100e1084406100074003155 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 476099136 1250 476097886 476097899
    0x120807170f0706050709150e0f030d0c08030c090d141515040506040b0a0305060709080706052205280b13030f06140c040512013623060a06 61
    0x340a26000180743d2030302c0d1004918650b00c98a500382c09030050950341401e0756802c031400f0701407182082042e400744d8541c011080b50703458042604641400182c40300003a1140d02c1d92a191a80d0009044100c04041403055007440c1e221100807070301c00ca120351003091008612480540c600035096609102c2c500840d0100315212011102d80b00030b0541c25600400d8079222400040c0c05400c64164594000000c031100005009000640707a000b46099110030303615603103c2640903200c4002d4020100410f80803c0303000002d9150201e9a03508045603844000c40a80310000114418041113849131440d400034482903102c00100b05a100030503010303500c03c0c500740e51400c51140c2480d5511000e07000c01d04000915084c051207402c41a00701c0c1d40c442050366103140c141d40c249002c0d0060302865019002002080803c00c0c0140b28000030030500b9120b140410501b4480c060a0034541c3c0804026515841c0440d0001f88101c4941d6a06080440c0044405810b00300705524001c4010041c0a10302c1c2400c4042040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 476100386 1250 476099136 476099167
    0x810060e060d03050a0c11040f021e07020102030a0c1109010b0306040b0d0b0a180c080312060321031f08010630020409230604020102010e0106140607060612080717 72
    0x1107603e03081500303504101c0d0074100f0072440c14050740c641003410803441c9c03030724400141d00510358041d101e0164420419006100c02e000d02402400902592041142d034003454002e002030b4003004e1003031580e031140d6400000801c880500a92043d00316400c003005000b070a2400380201da10a10060340c0040365200d440d01c42d102054000b60101105a9641c41850100a000d0841003005504140c640368001d6a5070455603072644803822806920448602141040c0760101328001051b50030251a605021400614032041e0300281c050440c4030b19071100880b918070100641c00003000ca070340000900d2460891030f081840c1d40351412014019114003101065046c00002400b09038046e103000900790071600d01602c810784c0f10b0003070b0103110044841a20024030005a005e128920070f034001c0c89000ca20345089400d88541d4090300c1683d600300c0c07440c0900350401d080a005910300031000421107aa940e811544014950701c001d9848100c009400c03802d100043c40e80300c1c013030038002e00a01c0c40e141010444100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 476101636 1250 476100386 476100397
    0xf14090306010915030203071401080a3c0905070518090615010302040e131a06060409090804030b100e010815010b1c0c0c170406051606060810060e060d0305 69
    0x100c8913a41c4070012034034903440d4807000155602808842030301d03441b0038900c02c40d0710340c1040e07590001d105031000803072460050044581807245d41c0d2500c981c2e0000e818242074030070007148801c40e28528889074000801000c0c0546070f4018025809026018100801d00c54181003402c41c1c1002e40305001c0901c01610740001e034403540704240540c1c03400d43c5451540102c01078450396009100b03c01c0000c040c885008071100d07600d441d192040c3c010100c80811001c502c84e01140456040e039000740c00388010041c520707070f80d04148038040c811040c00385450f840350386072103c40c0c005070b8481c20b0306005510184080b18500f800c0c2409010240014100060380e028404402d070014000d0324031031880400c41d40092100903581c07035035000c00242c0901103080c504100404102188030143d48002401c0300d44020008040b00319803d480281da509403500c42903558400e0300845150342284c1407a501c1d44001074144d828030142d5504080048041100c03031030107904a90b2141c0150050b88103450711000640001c0d0440100ca0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 476102886 1250 476101636 476101649
    0x18061d130605032116110a1508150307180e0d02010c17010e07050903010e100e01111321050607051317150910021810051305040506040906020a0f1409030601 69
    0x90078219240103503440b080441d6058004030a0400800c0004d42c020b103034440c8d001c42da900e00041d0b507030358402c001c107a0400c0d40240e0780640040400b80a20381c80f090701c1d880104101c000c040b030b28903180c80d21a858483e503400c2240050f559040340c0c108060344220b0014402500161042895041c0052003640301006092441801000900b406598030b0a410640e010300c4d03900103450085002c0c075250030240002896402d41075192a40c54040081c2160a980c1825205600007400600b4100d049005034424429062424480a440800500d0411100703104e2421a030791076494480780301c010380000b44079403c000c0c40e40f0072a00014044000010720030906005000000c82d0300d86800c010182040e41410710010390034000124540145d44c002210101c0e40410798000420801e0700a048600e03004d5400100c030880304081040149180c41c0d0040c64000e42e00410002e2170500c2a07403400100c0c0e00c00301103840460040046848002e030031110905015080c1000e2924010b90940081d40b12901406103d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 476104136 1250 476102886 476102917
    0x1508060703090609050607020d111605041515050706051803090f01230909070e01021b01030f0c0804110402180112060506070f060c18061d1306050321 66
    0x10b20512602e43c2042c0500c40d0080b09682035405c0c081c400a40300d02c01042480086030036080701d070740c1d040400104003108004040e4500000d9080c41e0410000e0700b010803840000240e1114081110402c42c4403d01c5c4040180e00c81d01e549420601d0020141c8000501c100409124800c0390a0030f08800b00846803000c03002c44a502c01c10003640e00584401d018020310202440a8404000381548490b00401c002c9200316000b1500790340302c40c0226007030080004980d0050700404480007c5c0d8510459040030110141001729140d4084901740703040b2280800c1e5100020002e0003844180301034032403142030385001501c01707620740a041440950131745030b402941410050000002c0941c6070084d4803283c05444014070075951204941801382c000e0081010070303200c882c40c2c03a5520143d00d0280583e003d414103900307200c1050902d004810381e0f42c20390b00060182c124242680012080d42c2c1d00712a58095002203c000034072a00342001e0516080c0c06170103e03509181154407c1d446146170f40241e404016882812 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 476105386 1250 476104136 476104151
    0xc040b07020d02121002070201030f05160f030f0219030e0d021906060801020c1e010b0a06211b090902090604030b0c07080c0d080708040b0406020f09060c030c011508060703 76
    0x80707a183c1e58540b503140f0660044e600d17003d90340919900201f50303e9000b640d0602030910300c07a11000c200c0324182d0321401c0004080c20f1004406006010301440c085c203504000800b48000c07401d90007a644443d0054060341c0c030f40c045800a00d60540f0402200b0a0110001c0c6119031a80d40d01035a1414043c20086e50303840200380550811059400481c00f0b811100700943d2103100008045a880d242c1d1010840340340030764618684c1d00d06051040b4480381d100141104000c0b131a0000a1f91030703091414010280c030b00d42c40b042c1d68060b6039901a41c042e00e100084000145402040c004240c54007642144152900403c0032a0580d654841070340c4c16680c1280c141c245944940300c180910b0311420728001c00581005c21510a03a02001c2450b040640703e5413501c41e2503503140c036001c40f0390031406c4030024440070301c05002c24081081d550150050080c2d4881079490240796200180282c1c000300407031110b136400002c030100015401c3c06483c0311404071240110300729003040302081c0c490380018440b20030180c0d110f04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 476106636 1250 476105386 476105389
    0x70305091e0105070e060c030306040207020a031e03141206060906040e01120507150c0b090705031204090c0c03120504030201200d0c020c06040e090f1c03050c040b07020d02 76
    0xa4141c0003081658800301c4038441d01441806040c08940342400b1411802c0d0b603c0c454181402110324120740e0601540c61580c0d058200802500f00c240144e800491030a4040000344096100c00d86c0c044540d03500841c03031141c0303180c002c01942c817101901c4030b484030900c801c41c150417885110680168044485540b00c1c0c074000042000c601859100c1c60b4000c00d80c1c000041c100c500c0f0340354550741c1802002516022902c43c4122a0034180025204c40081c0040b29004040780a000059400034201c00c240c0f40255560f03800a8640841c400000700d41c0d0800090801903110306208014804038142081e4480100390341b0060311040e12198182c80060310b032400601058400c4d800000c2900d8440c1c6140c001c4410041000c2561700b107454141046450180e04440701d600001c1c0d45100e03040c005084500d82400d28100c0f040d01c9002401e081030a01c9000c44001c402c0c1e009100607030f03040d4000f2140448261240340024103450026200c080d08031700c100001c0c000e102000048420310703901a01d00d000c40c94040d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 476107886 1250 476106636 476106643
    0x910113f01060f030b01021227060315130e030702061804110406080a09200102031b06040506010f1211190f0501021b061902100204060915051207030509 67
    0x40d92250900114000032920541060881c03490b221142d0b01002401204001681e55110000342048102d405000e200301e107022910f0745540c0000c81c0b203030054620000801141050308141c0c1c04040c3c5620075400d102c924140f076541c04030035401c14001030085025042a0070b40f00d10440d5030280c007490001401000c05c211401d010070f0704600240080001c42282204044607410a0246070001002c24010130041c201c03d00484003000d8201c00d40c0e1081c0d07401f0412550100222185040c15404244101c410746001030004510a0131000c000d0400c600d400d240c4030303041c1f80d016040303aa48030000f4082445a9440d400050307000d540c1c013402150140810100003048840b40120b2240c50300221038021580e011501030f118219030083e022909103043e41160318a14030132001703000d03822000030b103d250000c00b06014244030070000c60050f6050b54004011042c141c0c0c0c081d4100e20b010544440301000070400d51080c9110a071032902d0101c0c1400d40e0034000c0358402c400940701e102055150804102c56010a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 476109136 1250 476107886 476107987
    0x1303050a0c05251d060402130807180c0f0219060e0f0f011817030c1b01020403120507030804030320040f0f09020c060708041703091011 60
    0x70040ba0a0b03c0d509404507001404007140c0100e484071403d000140c0600e00d0f601c41180c0540741002d0300020b64032681404002d4201e403060107000d2060510004020304280300c0d590140803204d540c07100d05038890041006a03802810801c042004030900b0024807a4085151190042d0309101c4030b15031038450510b4009046103203a564501e01542c40c3c0054100740000b0200c20380d003041d600900652a81c14036030040b00c90052400b03401606407403c07450b240d20008000310b50040c6c04140590408804c0c080000c0d00c06001311249902d47e50005081c0203101c5201c0c6019410000d900d401450000b10750303801450844003410050604d5240c10f0080345111100e0320b841541c03054241c15039240d40d518400074039051203600c2003001540d101c12010a640b8014002c0300d440018040c014801621103c204607002c410051040d00e909002d0840e0360710a6541500944c02002680010041d0504071900402221500341c400d0720003c0041044911000100c42584400100e504017840e9000700000484c0122485 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 476110386 1250 476109136 476109143
    0x60403081612030e011407020309060c0328180f09050603070b220b07032304031a060f010e03070b07030219050a0b010f0803040909060b0d0303020915031303050a0c 72
    0x4202c0344061160305520043c03d42c0a480000d004241d446000903082c49000d950100058000300001001400d0403002407810040c4501280c0c540000c08032010741601130008007054800c1203a80020f0129800387c0700051607111080200303405031134600ca0b112a0010762203802c02d455100c0e4005404c940d030500010f0024440c4004981d95029840280300e1405180240c000100c1d10b02d0f400032903c4000c400944030b000760305848a08c0350718000e4420000c1c00400e84062050712a0410000c4001074500401402e0010840303100001401e0110030009024111041141000207481e440503059600040e50802c9580c50b29520350f07030b1106410100c1c11302c0c082c10118403145080907211401c00400041d504d19403402001190a02c0e41c03a1309032032072101031500c2524402c0d031045c0424010040b02c2c0d803201103024403410001034603042c981c011a1400d041b900059003c41c0c0d020682e00240e080180d40c86204800350f010052543c901039035244a001c034407100180401501069818100b40600702c43d0010540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 476111636 1250 476110386 476110403
    0xc0201031b0503180a0b0f06190603060e0606030720070f0305060a0e06040c1a072001030b0307080709090303060b072f030c09060310020d0e0106050a050604030816 72
    0x101c0280504503a1050300c0440c105120b00100c426040c3c00481d2440190364010311080d600d0f00c2d0382d058803521510107070445e940406180e40f4642d41d4141d11003984010a2291408901c0c145008220740a24400a04e024041d1104108101d0761031303031054122111407041640104c41114850101d8640011504400070b0502140e10210522100040c6284a000070b0142400079610126006031a14804e407401490300404503014005201e140d5000c110080c8520502414600701361142114101c8606952102500c081011002540c0c14020103440c0181034008201d41460300e040b150f6150098420301d0a0b8503a644084820940b003030b000300380200102c055164031540d6a040c03105620100000003041118120311203815454003c480044d40a03004020f005026014070170310998101c0140000e1303040c0a1000ba1b050071050300c0c4080c1c04001d0b0580c50015990070286401030854040760085c511546180000b00182d5031014122801d495100340707841e40350448650a06030994489900526070380c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 476112886 1250 476111636 476111681
    0x30a050102090301050106020d14070519060506150a050d0209040b060403050601060f1e0309050a06060f031103010207050618010906050f0a0506090106050409180209160906080c0304030c020103 85
    0x10150064505510b04400811003641d0b52a0700340e90765003410344240040b40c0340c00c20110b00303048140c0103846004e02400548200c042c41e4070031400c80c41c0e42c00f02d048824650359011320811b802c0c411010034038240fa21036800d18080c5250406001402500e101c075401e6500010125400c0d111078003c07a41c0b21002501d099100e984074600a510352400340180070010700e40410304000301e0b2281411000c4412014101103109800c000d040b13014044080707050720248500078004002828512a00000340f0301401d6a0740241c1c158601400100e070b40c6500a44245c4c0103120b8040450350100740d190b040714446c2d9174001c901c154118411f016000342c800117080145070404001c20b01d062440c19071311034001d05104001c0344d9102400c011040d0310a000382c4002800601040c420005c190b44030b18443c10803244018042c00c061340c005034003c03004480e1b441e10118000300310b42c070303007900030440c00080c06160900b4481841e060501041d00d00000f840603040003446402a4156406039204080c0c00b08081c2c4026542d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 476114136 1250 476112886 476112893
    0x9010311061e0f1e040b07060c0302090a080706091e17070f14040e0d02060c090a0929032a010909020d06080d030c230408070314010c030506100c050309030a 69
    0x1a0401d88084d848030050104141100780c0ca1001c49040c1c80ca01c18144e800e00c000c6440e904006c0c109440d0390414590308120300003282d99880076140c02410380100401d41d180c10680d0003842000207034000f03024034400e003802881c00d04102c208031054904c1030904a081481d84841c41e07140591031b501900041a9096002c10380c42d0740d01a0b4844210800e55091080c00c07121403981303540d0b4510f001c02d0710050300100301041084038040024803210000910f4801d03d551a226000111052860b590301c4884645025030307a10508007181010640040340500300c81c00540700034003e0603d0054645903451590608410303d0b80c090b4140d1009800605011902d03405601d012000421550140c11007a1140080c4169042d00c0ba0003142500300710b5540b0300300e5420f24413400d1010418004103000d070000042c00302040564003000220b00441c05818800d00041e0001e19503401c441038240c10b00700b050304280130000c0d95100c20600d0240e01c4054540743c52000d4240c10140d00b507000790344449516004c0d002401091 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 476115386 1250 476114136 476114167
    0x904200414010c031d270411150406123e032202040603050a0507030c0806060f090405160f1802090a03081b010c03051509010311061e 59
    0x165581072034036035804004038006645140d15544000c002584400314100c5d441c0001e541d940e054440580f1002548920b03145201141495010311680400b401c0c01b000284071510305018100036082d01d50000e0303104924044d0f280b80c8640c2c02035005100d00e0048040c018107065005402c580f0030100952101948000b121805205000f801c44000f0250409144200328260441c0c1c050041c401d5250040481001c40404040e40c894081e648295a103100001040c02404140001841038000e0190181180f52282c2d284040d9001000c0b00c1d40014104407a07a22490a40104540211600189641d9529005184c000c503c00d0825a80807602c00c00580e20407190260810b46840d032380c40450101807611201b0407030186011290340481c61041c100302050200e001044046041903003400b1444e28514031509550885103503d001a65802c204030304201516441c0d0b01c1c44104030b4802d1990b501d980c44030404401800049881208000b9a01b0100d0f004880c601c4910300589010079220f40360070b00400403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 476116636 1250 476115386 476115389
    0xd0501090212060405060609010f020f060412080702030c06010311210c01020c03010e0c0d1b0e01050f0102030a0215090a02090103080c010b01081b0a030f02031006120b011409042004 80
    0x1400d0380700003c64000e2615005151044030050202400c20110300011030300d8482143c890001c0d802035100158102006110081c0b21301e000e50000e150b01541050024044032004080d0360864205100c8100680c401152050441b0381284241414082c1c810000d04112600b035414103e19000500d14043c0250200d04100031010903000d0342c14209003030040c1400e0b20715101d03040e2180d030084070903c036407031034000702c078030600d40c010090580b00700c0c0310400d001c00c64006500302d21f043c0b5440000410062405a05260840400384080e44c00c1030079020001c2c1d40c6280101440c84140b07500b0b40020f0081c1002c00c14902c155400914200031035a590400d152030340d0110204d0060765080c120340e00d0b065401401c0442c014000103420f001e184139107044160440d084080e1040c201615184003403000300281c009980144040f4010300140361404074040c05800d0542c07001d81c40242000100907180ea004038131a0781820020001325618030140300041c0c020124621a400c0c252950b20052400429140c003900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 476117886 1250 476116636 476116657
    0x11e0207150c0c0e0406020c0a0b01290a140c01090c0906090c0903060207020604170303090f010c0219020402040506160c092021161209020f010507080d05010902 71
    0x20310341c0c0d18010111012030040001030202e09078928200079240114180c1d541c018015440107041c1004840750030706010780313007006071552400c4000520890041003100003181d481d0a40d00c8914072103034402b070002c07405500c400005014400806542046004049500004904d40200002e0078a86002400c1d14068060410658a4010003103020072080c0705120640c020f5485408001e0720f0355a8401c082d500402040b80c0005040c400095401c8205c10102400c802c0c0030301131502d915028826031b140c04002462038415a04000185040d43d40200b480d4405015096010540080781e00126001c3c0c819580f00c40c0d045080000c2c2c890380810045404160301d0311400c080d01c05107580d5400170701918841c1c80d480050140079841000d0348e80c890703002450107100c1d106048110451001ba81c0d640b5a000305c03452041251000c48103202558070000c096816600b0f00f9041004408640108101607119032226062100004100050010040c25680d4084d001441800f40c1d40c0c4540c5110040c5d000181d000c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 476119136 1250 476117886 476117909
    0x30605011d13020a030227011706090d0f121112040c0b04050307140d02090109020c011d07030b310c12170307050c061303020705032a011e0207 63
    0x2d03004003a440d400c502c040d9002043c0304401c908580810000d08052010340c0f0000c40c08440f5600760084241d03400e4000e01d00c0300c1d11014950414540141003190007000280c09801002c421001c075500100d540c2c0c4c0c1c013045032030880401c240d4141058010890005024503140020405c4040c0854400e0418802c600c00c003074101e503490741c98854440794040e43c042c442d0b16800040c81030104102c074000c041e01944000307203034921180081c0c01248903002c003a084400d205400084800c1e551200f4001d06500500c160300d000403400442c0a102c0e111075090100414a01407a000326480306003c40014000041c8580120841c01e51070551041461010501b143c940b18040000951903da01d20300b040c0040d0401c0c140140d5603003852030107102d58001044203062140a004002002c1c904001e01c81c0f148820205040d04500d0a04000c0d103400b0403075001d01e00c40e901260365200b0035801a9000802049070140304005821810700596030000d107841051005101d014038104401e0b800605101100c0981904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 476120386 1250 476119136 476119141
    0x5010905011d070f030207020a030204020a0207030605240d03030213060f0810120212010608030a11060a1107060c03110f031602060603031204050115030b0103050606040207030f0f0207030605011d 86
    0xa0480030b0030201c8038040840c8481110a030300324020b40040c040c0c288000c0c43e44041c59260ba00040817a045060040d0060340120020300401c45240301d1682c0000d905010845591030400000541502040c3c4081c09102485d4002c010140070307405880c000c00f0b2841c0fa0303213615625580000e181e2182d8820580c002254403011030081000303640d005c019140d0283c4c640800200c5034081c01989040108074040e250b69a96000841c0c940520103484090495600c101030514100b4a082c0342c010003410040820b0701d0810030341e81c0003241d50111082d00703612410100701c2800d509010350090405101d035805401e00010703c0411180310000451180e2000001c0d03d4014284040899856038101d903415090351007084408610444100d5869001e80f0600011a16483c1441c042c0c1c414507841d030048404c83c00c8000103004220003400700c982d004009031030447c03d0403a00d0700c0003003044480e0303181d0905100080c00122213180c03090102c003010b9500410144015607564040f0079038a01150003640680641e11702 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 476121636 1250 476120386 476120429
    0x6060306090b04033506010908010515121603020d1a04080702041b05040603110408070303090f0905130f02120109050601051215010614160305090a120c090b0607060501090501 77
    0x7144038001170090410003580c07813400c8600b0707505035010b000c40d418405400000500d8001c01d000b05480341490203031060710800780400340071441502075000103058100b05021b48200d100c065808044070303011208144601c0841c01e00070b400c4071a0b88a21181e49007070004000511100c40020010540700799000c112108098096150080b40000d100000407001c0000300603c0d84281c201111202080083c01c2c40c0540d03403034086180ae5a10381c411400301d42892410000480c02507070000003000700620070b100e50700c4c00c90300704450109285001000120540002c100350740b550f1100030401c2d08500001c000780d11250a11980c0d42c1c2c07007442142c1c440c10107003180107603d840200d500c08140f0080030b0f40212136420003109442880150802015604050100d400034040e40380c50b59a510f402034850503600c0004106014254804c1d4000b201501699050760300001d0000c18503c0031900181000143c01c075481001840318400d0100180c049810711001250861039540814103c84c8a091541e524403000070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 476122886 1250 476121636 476121677
    0x17092404030e010e0402301f090903030b1306140301020a050306040504060b100314010f05180402280e0a05060904060c090b190815130906060306090b0403 68
    0x21001800601001c0251640d9401201342c0d1050710740080003d82840c1060034800542c5000d115a20003e8030007003018026030840300707042d580294510006c8c2c0041e08507001440d1081c003491165074000341e610740201c1c0a15200f540040d5840c03400806000524081c3c0040301c0103044076005e5203000340000101d040543c60144201c2d240724240b41c598500b1540c4440c00c010041400600944040340c580840000958610810f0005040e13103442c0010001c00700d6038601043c0005802c085c1c24100e81c10b00610859031121104400c20380608448040d9541d24404504021045101c072040940e41c0c1d100c038a8004041034a0300169000c2030701800640d82c0c0c841240d800d641069400c160841070500209012944039000710340e1406590401e401c50301da650802c6181540424400c0002910810a94010981c4150f901d07030451407641014544088180000d0207001001c45070a029a13950410801044802c4c1c000b00010b6820003401c02100401e410701a0101400b00c80c00c4000840c40c013803130f0303000320401c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 476124136 1250 476122886 476122891
    0xc0e010201060f0332031b0d0509060703030b030f1b06040308031906030213050f0906010803030c0c070b0f0909130506060d030c020d03030b190b09010f170924 70
    0x543c4644015107140c4034140040d01080c800c940480d1544101a600000c120740a0380102600004540d51b6000050340c10450100d0105c0990f25040000146141523014041d40c0d40c0c0c0e0000c9845658804e80c1d444d090f0020035020540c0c0b03825029809140509150204c2d0180076580b411030340380e0f0829045400c0084604c2140801000e40a050010682421203081003052017000040e00090b801c1d12038001481d41a840341c05c441c8078030b86a40401c801c480c01c2c07030180b5800c40c000314001c280701d504005086481340001092101112408206234003c0401001280c006000030440030b0b5a41c100c10f05e00c0c40a60b8800004540181781890205e15206180a0142e0405405c1005800030303488400410240740403203001035003040045903001c0c0160761100c841005d4603202e901e00051101000c1c0074840a015018084101e141200804000b0113a5410807105000400d10f41a51401c0603090280c4441c880c0c6407551601e080601c00700803410070000340c40e08051521442002902c1242c100140030308404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 476125386 1250 476124136 476124149
    0xf0102030f070c080c03040f09060b19030c0926010c02070812030a091b03050c06072a03140c0316060c020405040212011802090604060e0c07050703080d0c0e01020106 73
    0x510000640340ca200f400328004191040c001e480ca850401840c00e440d542094200080014503600200201d81035403150b04000c22810203040d05211250507080c0d683d80030440c544050640f60301c507503400d0b644984401c8020b440e2100680b0241c2d2500080e80d001c250810000110a41ca450f00c48078041c1c0c000152070048450f20310051046c4c0720a01a24603203500050308400c051510f0b50140000107000e403040111040c002064003d0341c41c03460904a10f40486c0199040c055141003142c2c0c004607011400817034840c8500c0311505012150b4544a446e03080d101d40c0301074000c65080700c40c0c480036800440c040d54000801c408540e549440c4098003c1110200e1042c2c0000c2a081c4c1924001420141c0015600500050611004d040451143c0b1300b0740c0e0fa4003100d240501d04031421034007103103130242c41c035034000b8403e807030400c4031905044040d00300d620090061100c0b260040b0f0703a40200001081030b54095a80405519145c9403030f1003114014106503244e420105000078207800da60b510520400c4102e40c070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 476126636 1250 476125386 476125411
    0x608101a09040b0c070305130b09040c0905011407020a030812070e01080c0d0c300f0603020609120c06070c060e0108091009050102091018150f080603030c0a03020c030f010203 77
    0x803124074010131030f40310140840c28404144664420324140010b03a800605030b030150180c0e43c41c0058200000c480114400304103001e1600000d20082e6484100d62030310300801180a41c1c0c0e000140001030703291106078001400700c980001c8030040250440c4400d40a101e00381c03100300d03400310b20070300648441c281203c5218a220040c0b00c2400c1d20740c3c8a0f00b18660200440c00c040a010300e1054a42d00f4040c0b000b50350240c2140c03100340c2e281505506100c1c0c0d0320300c0307403111004108182c01d540c00692644104011b561095182e0b58056103031541c1800b582d03600302130040c41c069440c2180d2814070512500c0e84140da01081450b810800d06501400b2003503c500d07481d5028110340c5040f01d050100400140e403068074150340c2400000865191401c40401b8803000752102000f510b800000301d1249921600503198140082942054247c1c02500317800307600c09607003004081940d42c940800d2035800b80051400c4184107803801c07007040c150081481440e0240c01d03010b4402c0701c08020041d078281e102c2034a44908511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 476127886 1250 476126636 476126641
    0xa0c05090c030f0a24061d01031a01030e1005100e060904030c0b0c1b01020d15030305071e05060a0b12011505130608032808060f130608101a09040b 65
    0x84113038019199281000400104128000071117010091203410000104059040450410104007400d80d02032409180502ca85200c4200313840446032040160b5041c1920703001d400c030030b65600780301017501c4842220703080081d450f00d0454000c64007141e20030a00c4c102e0003903001c50998107000c94058803c1c0d4041e03c5a0001e000b0b6a524200c010740020802c1035000030a0010000c0c0c10040000c0a410320014000580c880040521240844410041d0000d50fa85e000381d08100198201c02900e01c400d4000c690107650040d40c02c0c2540c484484100b005140b8001c0204100001103203500040c0c0f06c0d14150340104480760f04840d102d013201c0903000c01245140e00b0110030003075880e01441e0201034103050280451681d9454050603d90b4022201c1e00ca198041c2c044e0300e070b2070700d107090046503481069071400c810a814054003164010000c444024000c0d0484840c41d000100e294010300d0043c20301c0401c5032400c54a44c000c0c40010300c504c411101040703040c10080b206500d0014440d6026541107040c004072034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 476129136 1250 476127886 476127901
    0x6050a0503150103020405060a080f01080f060103030e03010204030f080304030905040b0a170c04140f06030d12020307030e0303090a02090604021905030916171e1c050c0a0c05090c030f 81
    0x1011a082d2a8100340d000c11022a103a1107039030141411400c0d9440c3c90349541040d8460b4000c041058001100b154010321540c80c10040004130f0f40d0440c0d41508104503540080310100340603102e641c2001c2c2426070b0780c4145000304151407004500c2a8001d0391a1002d00d40c07520108401e0f20740e8901e0203640403c4d1030006007c0602d0079070300030324480982e03001c85801008200106041d5585000c0f40384084c0440b00420070782220780b015542e4001000c038007410300f442400e0350180540b02076801c0f1440c042e41c04800100d80c00c2c043c0d8400c000408070007007102e840345080d120665440020800132401504e100c00800d005060500a580c20150114101b45072180000b0046846030002080c0306070303510981a808002c01e2040c2d02000182601c0c1c101c0840341501c50600d980b508000402c260034100364101381e401c1945d408180010302c8601e8590543e05050610400c1741c05014007203400c082401000106000c0241ca450303044c04a40d0191500c1007107a85400004c001030104465400503520240c000a079007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 476130386 1250 476129136 476129161
    0x9120a05030f0304061415041a1801180504031b0f060501140f03150606220b090103050906091c0c2a0f080d0e0a08010e010b0a05031207150618060f06050a0503 70
    0x7008020903081c103009c1c840100182040180c000400d00810700e060060140744018140710101e0000328800b07114a00b01568002d080b0040d0382444002003400481c41d1040044541001461b5504804140403a50310760050440e0344010f005c0d0366100f11001d00d44980b40741000715100960088101c0e42500b5607450005106883c4d10040007800c0c40340100f1140708296000e1a201070150244941c0103403140f6904002408454020340f0810300b0782d01040410059000004944603015260348940d6040740400b18184c845209410700140008140c603001600003412070b1481480055403046041d0169690181008040481c0107001c2940c110200190605000c0c0c00131590b1550050543e610b101c0d40c40c4c5480d42101c0741100403e045944421081c00c4038034000c121072000d004101c0c064891a4180c0315941114031a14000034968207c2d054190702841882e8810402000711107103080303070304031209807003030003003006015004c1d80c124070801c08170b5a184070b0000e9543c143c0a035110645940c440d02e210000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 476131636 1250 476130386 476130401
    0x12020304030507090e0d08040b0703091e0501050402090c12070e1c0605060a0503060108030d110702030114010305160f0311040b0a1d130809120a05030f030406141504 73
    0x1544020480000040d2040001d08010400100009641a0504400e0b070030143d90f04144c004001c601c4040c880031581c00000c10b50012201d00300040e10f03520343d00d44111400c4800c0782d10303203e01e013a500c00802405419007005101ea031003110584010341d502684c00c0000e000395481421340c6241103000844440c09005400c505031801007c0c56184542d0314140c1201d8080003204030740e0542c49509001145c00c0101c40ba00190404074044d241560400b0700ba01d60324054010f0210384039843d59140b000b001034503012070f01c2180d0058000c0c007110030344401d9580c50741c60a202c100c489100c2c02500d5009410a004020240d80440c6000f1190a14648595404154032400654030035900e00c2c07580030907920b2403110b10040c500300030801c04040c500d4607450136840c0001c00201e501003a002072200014030b0705084940c4020112004214006a468042d151a4400c3c00042c00c40c40002000400d248400d4040d61086100e158240130460b0420004542144159035140001180c0c48406041c1d2030300d030f0010407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 476132886 1250 476131636 476131673
    0x9063c1403152b060219030b13020d09051b09131703060315100f050a080c01050c03130815060d0b0105091e0c0a03051b0d0c0c0f050d020d110703 64
    0x491140d50060300400d401d803c000304448031a80003801085080c11381c0100c0300c111605e4101000381c0740141c03020455543e403200602c000c50760700140b0411010804c2e031010106503042011a0003114600c0115140300d03001500052040d132010000510354080684000c407507a80c0108035081d000d00381031010240b1780001c0c200c154180654003a944204281c1c004040c400c00b8400724410800d850302c041200c0b00c0340c451f00401d0241c2e1003241d0034010f51030000340111070700f0340a1a2640e900e800c054481403e60084440b500c9101c0c844110001da0124001001c0011714000079140306161034840c1041140060300c10004c3c0807a8013070004200a1400c4415a903114510300b072114040316080da40d10780c155604841d4403446803004070b460051541d0501c1042d91080191540c1c7c1c3c0d103c0c6007100c0c0c5403014002e0440910003681c44581404030540b03d94021102181e00c0000c0308040009450850b44804241e0180d000501c03940b030442105921441e40020700c007100002130a1180d0544e1203400e0551171202500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 476134136 1250 476132886 476132929
    0x40b0a081b1204120311120a020f071b0f05030c0405070e030d080f0a18061e1a090f01140d02040e0d020a060509030a09063c140315 58
    0x61000c03403004002490034101c0703040d0b1806a40350070b140010700d100e05903045104061800c41d840d03251001e08400ca6040e0400104000003030345d25112088041c1c030a130700c011307a0036410104009042180d07079443c1440703440301c1d81c00c030042490301c0b0480b44155244500c00c41e0b0740f40d1f0282d14440200d05080c0e110039000038144c40c10054110f400d03404a85000425061070700010000010041c07411f481c0202035400c40c04015003888444d40c00606020070100c03080b8017a0900b90351f00c40e03102c0310403545000c4a1100080850a0100940c28000106d45c999495046401500050009402c0030000c01140f0305031984002d1140b201c00b10791091204103121440200d80095840c407124400f00c0c4100042c0714151446d034000c0002c03141c9031403e00241c860140c50b141079a4828000035909640040340c42c010784820345408501c1116a130320400c1c60b00e4040d508013900ea001000701440312503915165000780402d50b03c03003d50042c40004031407618801103800a9071041c00b0303583c1110304d240410701c0011b00744000121 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 476135386 1250 476134136 476134171
    0x15070321021305011701080d1803060f0915060302012001060909060e100e0a121709030a1b0b0a090305070b0a0209040b19030803070908031206010212040b0a08 70
    0x1500c00c0364400301d0142c00262603840c2c00c201941e031240002071040102c00b20b1254075450300803000d03640c6500ca092503040c8417101401040c0f05108139100c40003550455420300c00071200703026400c01000250300940b0700503032400c0c00d610001d000380076110840798107135210420240340b110311005c6810f0b45072841429540f140c000241e4142c040c003d041e061402124002251603640c022285000005610400502d040c00802482d1000c042035200340035030407103940100080c640004644105500c01d0707a0440d41e6840060101412001000c3d09540c0b045031502d8030f9500e00d00142c0814500b031104001d100c0303408a40020350302c1a494200780000c5210341041810205942d0798480003810440c6c440d242181d000c03411000e60314180c0284002460140e80320150902d034440da90840c481f071400080c100d01c1001001c140c0203441511180300074071624003a00d03101d000395130449004c6141560310078018401c003a00100c3c402c0c40780081300c1c22039516810b903614001c90031900b80c4501d040101000c5038885805007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 476136636 1250 476135386 476135447
    0x5010f0f030506040915051503060f01051009050306150310060e0c0d0908160b060603190515100302270d030f030b090f0417160f02120102040f08010605150703 70
    0x2000c280d80c483e06e02c0c011070070b4900b0300101c138154200d00078140d10a60000b410700c40300001017001541514400e542c402c00815035003500382ca0007803090340016010301c240740800c070030041c01003443c4003d68011400d0b40e030402031031001c010a8510314045c1d108184070800203e41d2074500320f030061400c004000c0000c80c41c00c08946440300c1035000400e915101d8200031000c070702080381506141d540702c90111403c078151f04050104445c0054020140c100507640c07000440c0e080c032a400300c920500400100039020242e80008014040c1d04a400380031180001ca0164540d8032001c010706400403e40a0700701c407802002510100d540008480b6814227166440141c030030070340c030b4014150b07125800351107120015081c940380c0f0107081104407850180d4400301f07000040400040c81d4001490540200140581200b40e000241c000405030b208144658030002c4e0000b120403034070700c2a00407108010b00070010181d46806100104c000f543d10707600003581c10405a40040d009488404100a0609050a602302001e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 476137886 1250 476136636 476136653
    0x1d06071b0611010609060f03140a0b1302092a180306100501110a03210f0507180b090112110702030a06060f0f030c0504200d0501030c05010f0f0305060409 68
    0x80040000681040800d06002c400b4011840103241414042040d94074088030f4800518080c08002e181041c0c0c2c8035195000b0380200721580c800b980103914503680c0c1c103060f24001140b080c0040101c2c024240071002072040010003110f440400b1030300311000d880c54031001407911641d00c0360001807495180d1110b5090140ca00300203903440351f014041c16011840c10400050020340c011150700b04150300c11440000060381c403034100c00030480803500c0c1c00e00c032403800410302014224015a05604528000403c0301d8968030650107044800c580b41043e040340c0d201c001c0206075203d40e02640780442c4000255500c012825840421881c00700d0380040e00f0400150b000034200b140c0d2481c19079119031580d01c14051b50f21040e80400041c1100501d40100740e14540d209031310007085201d424800c0350b0300c8503110b1043c0c0c01c1c492441124051145843e5480d02c2d40045080100001e00058812036282c40b80850154043c0310402d114068540380c1c0344140d1701c0041c084001d8000103109a03000f90f22246d50400048058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 476139136 1250 476137886 476137889
    0x1061116050d15182a090c020109151a0607110105301b2a01020405090c1801111b13020703080118060b041401050f030f0906071d06071b 60
    0xd0b1001c51a1500d0341845c0004003000c0c4202c041555041024903425889001c401044403c0c080300460032201d002426801010420302c00f4100c0690305610188805040e40250503044018a00700030840480050101500031550024131705841d405805d4075030760090b005461842710350254030600f4200d0920700055600107a61103000301d0f07190014462982602c10303e11141e85030181d00107041c0454882c074036540d0086040f80f00350040401024099441080d012a00078000282c500031a60804980c40310081d40030303501c035007a40c030100001000b0540c0300702c6043e511403030900000d180030040054207031402250340405940c4942c00c031103584018201800a030110301e0280d00e45151561508003d4490074400499508040d4031b01202031000c401c94009640c00d441b000708601003203030241d10041c2e4030340c495070707081c0c0801410200c100034455000f181420b01c1560070388161402501c551100341c511100911481c20044050081864241420009041114003034500105604c509801c00008403540c1d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 476140386 1250 476139136 476139161
    0x902040b1807021005070c0b1504110a03060e0112060b13110406080c03010803030f1305030d0605031b03031602040b041805060708010612020d0209150301061116050d15 74
    0x840040042c41034040c480802c001e03100c03000038170407407510040040900001c5032008054164a20101d1200c0d061078452881402001e0030070414202c00d1180307040380e43c21080f90303400002e040c142c0205030003040302c214504a0b51a0300c00c0f100303611802c0d901d9001422018211a8201080c40003403000640d103800f440d0745a8a00d400301540e91410b200c0c00402052000b04801444282000100884140081241c0d03000c102e40d090080e0f01d807101003111584890070403025025200101e0981d861804d00d50000b02220000c80c115582c4480c5000700442000c0040c0d1002e915400600030349000b10641f09211841610003400002e40905400000b400c40d509030040c155020328001407402040410017880d44c005805040800030740d858018000d02020029181000c0c06802080e5020101e580d50103980748188000c100c40e4003a40030b098002d8454000348a07000c00190b00414100c4190340c0890381e9400715500d01e040c065514100300502088509403101241c0c0c2640426600c24403008500c981d0300210403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 476141636 1250 476140386 476140429
    0x30705010911041d0a0b0601140307050d0f0902010f230c1b0111071e0e090f2505090403140403050601090507091d04020406081f0e010902010507060902040b 69
    0x101d80c0502c0704031011100340c050000006880c0040c400e1002451400700c0c1c3d405041066540d847c40c0040351108440b40c800f00e1305031b9001c0144002e458119010302501c0c8006101040086541c4500000b6684a034001a02040d11908501c1c5004d2080d9100d0302c1494901d5017128042c40940c0e000d02481c2e00c095205151038004201c1da1011200d8100400b101141c2464510080700e1390816803511500648102000d00050f054504169504081c5140c0105020105140d1915010304029164100c00c0c040c1e000c0c900450301c103266201d0032040090065445540449001810b1030188800e8404c00781043c3e051102d140101c10035a0362481c010009148194040d02003945081000d00603248090544c0c0c0c1400304120b002d0105c41e001c105149040c10000e150550980c40c1e600100c1d0040c01d0941103005d80b400361000c3e490b6081e102140e407044404000c0c90400c100004e4214060803141d1000000b800075104109407008074200f5001b04401900050000428010407000144500d8041040101100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 476142886 1250 476141636 476141663
    0x100f180f03030e0910051f0c080307020a05061b0406180915090b01090e06010518034806031e070f0806100806060d090c1d0a0c020703140307050109 65
    0x105010301d245c00c4801100f0f0008580c0c00d1400048509444001c048060b03000c1f1203050001030701c41d0050400303054020a100b9524140010020345405600c03100f03540034862400454060610058284d1600038140712123402d01d4284075007110074520381113200401040600700469910320910840c82c0e06881e0486180c0da03079140505580540d42c0d01070401d130522040010403c00c815148042a61100c401d180c00e507503424107141000c22010807510401d402d4450100c0007000b400695002c40c03003a02e0600e484090803004030f0303030714400550300384281402c048040358100100d0800c140519040004009405044249600b68040e2100100d90100c0020700400c544140b07150000c071100d411003800d42b072081200c1d42403500509840c402810039030080c00006610001000790798843e40c421780e400441d509030203685240505224080c80c0c18444200b0003c8007051003501e65201d0b05407102c0c0030750042c1540c6451511265143c012103e40110240010004100010b40a100c0d61901394864000e01320441c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 476144136 1250 476142886 476142889
    0xc0312010807030f020111030d1103180f030a0f0519020106061b0b010b0f0d0219021e0a03080606042103030b1203310b0903010b100f180f03030e 64
    0x18410391044034542c0111000b03001040c805440c00d0780c000e0702801e081e0401e07103032500010b01c1d40c86900c580039200380ca880041d103540900c10004600840440c108d54140d078030301c0044a911018403021030622170303108000c0c40c0c3d19a8001d510944504085080181c01d194405040c40240c103040c000c0d0784010703591b0307a200380b01135500000038820b0700b9143e040e40701280325107a5448403505818085c04003d00000b20701007008003518021190402a151003c0d0340310318048001c1151800f40b0751046025024440301440c2400c0c10184101c007a0642400400b40001c1a4409803410b02c0054070752134000800300000b00700209800c6a1001e46800c0d210054840d400790f00700102152030b5401c1d500d210321011240f070a40c2844c0081621140325840306c6500c805500481c103071198287c05030070000a0400c0325400142038215801034620100140c0080c400200d440c400c03c107002e08c14880070004680d18002240c4254801d2158080d09220a420250040e481e0f840b00050303044994002c4001442e41881200103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 476145386 1250 476144136 476144167
    0x306050a0b13050606121f3212030d14010b0903030f0702040f05150a17120d090c1e080a0b15040b0301050114010216050f15220e090705092a0c03 64
    0x1c0c400060001913030001e80ea001e190044044481c01008c00d030548101407241c5e03807600a00e01c20840300d411603644440084541c1e0103031211025001e002e82c0001c00000d00303084900b0450740d24680c0100030318a000300451040c459a0000318060360030641d02c00b5100130040701441818040e415025001840562030810409000c1e0f407030700407011046000b2100c1c0782a84000a106070440c06e00410030351202d22040540b00200240f00000d818400c200c0000520650340381618070303940740d4040f080c003015501d40c4c401c0c0c2c0d1f8071004c02d00c0051110250000080ba0320b45500c24541070f80d600180041035034400c4200181c2525020f82006e08010602e8114000c1c542e01000101018814080390000b807a15000010380d49074549000c1900a10f410548004024408022200c6286628030f1558074035400f00554069000940907050306582c056011648000300042c60760212880200f03621603076960042e0034560311220032420a007452607910f000f0306040111f030113010b54000c41e1001b1038594604000c04a03c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 476146636 1250 476145386 476145389
    0xb03010902282f01020304030503181501031e06050f0118050f04080702010212191709060a0e0c030a05060f1003050d08100905040c0306050a0b13050606121f 69
    0xb40e00c40d12000c1910650810403098900404148460040840150b54000340380c49103889010b0354800030401003050f400c040594003c005490000a821000c141910f40c0c0e410f80c00c60b5400b8050542004100180c00d40d0256503101c0319000c42c420041580c3c0c1c0e03422054860a1701d000006c2c0e40700b500180400030010001c0c15140c10100c0c07052140d810461070041c060300010348003401100f0009090030940e4003c1200405195040d002c06903503050300d07009140210306450304c810001da01c0d2406222800203410360240190300c12000b42c600ca03103640d10584001c0a11074503c0c8158081c895101259550030f00925013414003030406040c461408041c42e0b40c4000009124003a034425418050003c5800007498200120f40c41c01c040a20b500c4292900c8400f518030b9101c107146134102020001000311404d60881120322400045c080c545030f0141c0a0190303842c0d002095000780140904814020302134004079003145026000c00d1400c1000515944020703402c460f0b20005a407a003450800c840c1e4010352020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 476147886 1250 476146636 476146687
    0x1908120a020c030a350f15062205090108251d011409090a03030504030504031211010e012706090209040f0c06090b0f180a0f09050604020c0706050d060b03010902 71
    0x456501e020640300681c140241078100404c186e00005524070300030306d148141d0b41000a0035141c40d1070380380d81c030719400403918000004000071900c5c0000315403d201c15440d06032102d1401034400301c02d02d0842103041001c41e1881c0780022000c0780703002409103c102503080704001c4420005025604181c0545200101c3d1101c29008016407800c101ca00c400100708205002d9052401142e241c4135410115418001d41d000030301714100a0019415041d0031060200c03000300b00000a0004504c00f00440d8200e503190f03801605030020385092506510b031124505000d030f510400000030f0175100c6402040791140200c6044822580d201d407090140882e0b600041c0041c21945801c60295080a042e0070550040c0c2d507030152410408102c40c000119811490150780c0400751a90001c0750780c07a4002d8281c000d06119418900c1d24041c04285541018002c40e00000030390001040301d103280c04c0c811036050380103c0c10a10499a6104003240c004400c0c0010343c003c14034110090780352410380f02100c00b001842426003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 476149136 1250 476147886 476147957
    0x3091b080d27060807030603120306030302061003050d050c120f04050a1e050112020d05090102030a23040222050103030f14090906090c04031707051908120a020c030a 73
    0x2280440403400c1c20b0310540b81c0510342820750351514102980034142076003005060945c03421b800134401d6407550245003181c2c043d074201d601c1030b107130760f1005028001c42c2e000c0a0b0030380e04a8845080781e2806000103150180280b01120204a00120608010b03007040748842c1d1844400a002c200500c0e2549100c8090a0401d0030440790480c410b040780969803803442402e043c0003800032240c040b80e4465054804400441d1030902507860070342c2680d03001358012240406903a00e040409445980b808001d46241c0c44c08091000d41da4a49408000306a40018040030154442e44168886600e0324000e4500851094035020718030744400340040c1050788040010180d0340320034090214560b42d50713030300d568000a043c3d408c0b0241c2c0c0c451504519080c8a29040a01440c0f054140800b00303840f120000c01c8070b28000c106640000c0708682c241d040213030b01c007900030301084414001c14904210b1500103a410840381c0c0b4006140c4451080c01504603000b80c84c0d0827010480301e6042c030320500b903034a102412007030004000303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 476150386 1250 476149136 476149187
    0x102060702030301210b04110a1517180f0d261501120213050a080307170306010309170c010c02010203070527191818020103091b080d 59
    0xc2d600c2c041482500030348604e4400340a40540b425101c824100d0700400d00090601e00790400b1108102c3c1d455406020b02180600010090110305040c040c10100d0380c0c0300c1580a2403a24803c01101010300009000e1450802c1102401410450300d642d030b0100c2c0010303001d1040010320261108803a203500c1748180300205120240c02940500b000e612400c1003400640c0c010315400101c0300500103840d80000184005018803c8410308180b10701100c104880c400340c800c3e103400c012a01c9014509000b02841d141c00103404c8030444820140d94464010b160020304003243d80c40d4104030354840308400c41940c5000843c1c1220941c28000e5803000c3c0302070b00007586141017851001b006d51007861201c0d510941c0c410b0340d00910b980c0d21000c10700c0f29040103005243c3d20912480380d205403440c034801c510b00503090a02c9c000319080c481c02a446002e141c0003034540031640d2500103501800d0700480484025517110900c10307419100b264498044c1c03900500410381601845006485404421320a20000450151 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 476151636 1250 476150386 476150401
    0x10306050f01080711070f031104060620150408030a1d030301061d030304061106070c2001050c0d080603010c02070f1a070609081306081b030702031c09050c010206 72
    0xd40d0800c0e22428a042c10f9603545000007224602602c80c0615924002c0ca8000196041c040c0b194105880c068600003148420b00350402086a0703d51080308085004268082e080e1403c604000212581c0c000681d003030114108014032016008031412140c103403001c0306001e040034140c07203000d201c401041800e4185810044100b5524041441240308000c4504030b01540c1d40410241910444e01c050b04481d2a40e8076075401070721010034442c5400d010b05c510380019014520895809003201c4e00841c408400c8012110309000140250189606004c020045070014607030420103540c1800380c0b036030780031550b0a10710205400d44125074050000c541c0114001e002d00800400580300711076000c1c0c07040981c007501c10031002c0a40100030015004503e0040c41c5024860300d84000c012010b1001c86106900c0e490300c4068a0603c4181e80d010480c0000e803d080321440034200c0199007100f03142c01217a09161503081500e84c1c20301c2402c21b407000c0e50b417107000070703000c101c410000060441400d00103800a03143c10328 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 476152886 1250 476151636 476151649
    0xf0f02070f080306030312090f1c051909150806090a0c0824060a0519030603081219090c050a0801020a0815190b032e03081b0609060103050c01030605 66
    0x1e409400440004040340341942c04200301c03200914585082c0c0b0140c0317805984261281d0310000b801000f40142603400c0704120b550a0400c00303008403074540a04040030903180c1c05140100c280c09109210903c900440d181000b4a010300c0801207641c0d5001c2545051001e0228032a80070b0300c46500242030240c00995660803c00140c0e004802c0c10070078400700f04202c0340310b15207050b4400d2950051000a00c0802944d03000c00141000d255081920741c000764180d030220700311150792001801045040c0490444c0c0d0710001c008075042840b0030010b0a005c048101c9210031941e02400481b000d944201042005040071683c140042c407021008508120780c1c240c002d0841d0b8070060941c4d003100e4280d592502c0581e24500e09565090603030600500c4030342c548107450a03661082d102c0460490488034298060401c0ca41b0401c1804030f1030b840c0000071840c694038140d5542182d12110011658041c0e0112103000c104041d51040d4411300c0201502e5141d41001410480f03c840703c2810175003084000e100c9900d490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 476154136 1250 476152886 476152913
    0x403030507020d0f05060a05220803071817010f06030c051002120a0309060e0604020312181002060106080a050114010e1f0f020708011a0607080d0c030f0f0207 70
    0x103003400c03a40c9200034800030303590140318a0020034201d100000001401000100c1c98071030807054404200c207494203881c81c0700c1413154803086039080c3c0202c421003002072110000385411490354104008060302c0c14a82d01a0308000c0c1d0415804401102d0010354401c0b82401011040c845a00003080968215102c212402c18107006c0e29004540c58241c1c6e10b0614420000114598814500d85da10b401a0510041c040c2c28803040c2903440c5030402c41040b15580001c1500c0340607030307070080050954194038420480307550010a50403c0c8038100380c1c4100341a86070140018145245036018000540c144040504410300180c00c0c0a202c503d044c00600614520741c491a00a26090800c0741510340c010b8002075480041c0c207010a0161003070b10b001040741d50440f040081d113010a03002d175408140c40e90200303800c803170540c036001400c804214140285030070710400820855008079607243c5040307450f80074030040d10054074181000030350311118802c10200a115440d00f417004c0c86003d500d0303c85903841b02c80458404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 476155386 1250 476154136 476154143
    0x117090604060c1e08060a06050309060f180313080f0a1212060302040213180c0c020d051c110105070905010206060f01031d0c040c0206100e36100507050403 69
    0x3c510400c0e0035a801038826250700b410038010000b83c0da0000e500180795032826980280210069040071903000c0c00b480540340310380310344002040142d441c10303905d48a0306005800111034010351038915002c510148010613003030421031205100f4615141815160220726090068160802c0419000240d0002c0e0b03041320600c0149003801494552403008401094180e00017036000d071000039504c40c0400700c0b6200c2011105000030000c1086510300d1020240d45030b004486000900700d060b601c00528181007035406e0140074034102c0b0070400c1c0074412122141122036441000c1500c20500e0081d031002400340d5a4442035515000780490f14000000c0e41c0c1d13000182032640b10701306507105811164031036440317030184c02a4940c5440002041541c0b5944500745203451901440c1415142c850140c0006605801880c011030815400c03454a0020140048094103d070001c200c0700c40307944410b089017110141c01c17190110b02c100d02150300401d5946000041c03141003080364100307400c100d04640c1000946080300e40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 476156636 1250 476155386 476155391
    0x3180f040621150e0129010e06030c07060c050403050c0f0612130804141e03030901081308030f060f0405071b08040e010306050f0f151e0901060e011709060406 70
    0x280703440c03c10703511442c000d0710395842450810050381d0354a05405c80301044440c202c40d031080520030941110b00c400ca401c0802c0c04900035005800403824490b0003141c1c80700012406504080e0340d0745d181c105441920900200040001c5404e0007800b07400d02848254403022585588100070344804500d1038019241c20001c9141c148000844d07240380744e044222000d0740722402c160b49988811080e8040e40f00c2d4008240204805000620300c3c000340010740d58015001402503090150b202d004503400c3c10010600503810400c402c44c6000509407030003440c05050710341c1d001c0c1c0c078502d011400d00003400144000c00e4856410b2909000e041034001c414109072000d402e902c10060000d03410070007101d2145500a645003240d02000105004140e0b1281d0b004540c8400d1404e1980c86443d41c2450405090314003d8150380b030744000a0061030f20300000030782503401c41031820003158020700144403c1c03000d038000d00c003080282034098165a4482d40c3c07032100c00704440c0448a2824600d02666944100a00051000d40e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 476157886 1250 476156636 476156699
    0x140628090219060e0a051305040503160b0105090718060305060303070b010306020408010e1c0f03060e04050d0305130f0f020402120106030204060311211803180f0406 73
    0x60040e0041040c1680103030480d00112000301d607203901c8a00710302c41c20340050501e2030291140d00e0050394803811144002c044844118404401000030039000c3c0c42198248001c01100703201c0015414124841030143e03680325903541c541024070450104c020509400c01000000d80031240351600080d0054540314075002510f42e640401080c0ba501ca6030300e0107484495800d00004c100003407900100144c4034100001c1c421584407689950750354440700e0341801c0900c1585601c00601d845040013031100d4500c0c0ca00451200d58401e0040324080050b18203403000d80100c0e010351446034046c050380750042c40b20741540c90741074107507280c2540342100c4c22801444001d924100505656458054800302000c41c443d500d0750b075135508070243c0254400c1c03080c50046802c0c0a00e01c0c08030344030b00090300c07588490001c41c05501c640385480c240d00084014a01900105030070614920440c041015095418001e4106c011441403141041302080f241441180b107103091000510003881c9d00b11700408041e01052246d20303440c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 476159136 1250 476157886 476157961
    0x2030f040b09014107050706150b1b0c060f09040f020903062715220b15010e060306010c1e120c12031109011202070501020a0c1406 58
    0x504105102500031115a00b0400f00d802020f00720940c0021403420010303004c94641c801520704401107542001240d820301c01e04003c00c016402805800c101c0d140540d122540b100c5c04150f0302d4001c4c4009001003207000c820b402e000402080401e0b000c040884803a41400007014035010180f1501603140c1c0115103901d0001d8565800340c0581301c0011005082e00c5c0117182000c1e003529034124146215a401c1140300548000c1800410a07424800c50140002ca80c1e07900d5070486150000c00304072039900c441540302c07918081115241c00900400d41421080e65034030107080010842c0c6039600469201d45020030a1004980e00306039040d02080e800048840d0344a05150700e0703821488462000703000d0a09a0080020841d8080740c0352580c10f02c902d180b20300100004c90100d044410000e10030760104010801031040b0b43c09060a41c81d280c0e0441c10241c5018100c1e5141426078104c1100480031401d41032415040002203075004a2400f02c40c40280001d00c3d000d01981c100e03081140b1a401c0c4008441d9092990 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 476160386 1250 476159136 476159141
    0x2203050c0f0601032a1d040b010902160f0f05010c030c020c040b0604090b0d1a0a050c130b0f0c0f03070210020613060b0f040513020a0f0b0702060a0215090706090902030f040b0901 79
    0x1406c0c050051003c000b01c4800c241540102254219401901100041200c51440c401e450303c03903c40c0d1200d41140c56040c0e1324482ca042d035540302650101026542140050002d00580100e150390796408110b86899200103887e14207000303e200e00c48c0341800c4203c01c050301c648041d101252010000400c00d20407200200304081d54840e80903103604807180300003e55a0b0110f410700d000785c0c6280010131045c1c0e22214124194054011180e80c0703041403030700c1004000901000b03080741001421555280071411480d4900d4840d0b4802182c0860b00041158400c3d0316143d084011070201c1800034003442c0c940b847d0036516512503030f10018003255440c0486481034072030061a0801a1014108004505011800004049480404038864080c1400c04900d003641c000d15101140c001031840e0b82007100c036034200481500604e2642045115080402d000c800c0c0300f01c020742c00b4040c41c2000d040628105440100700080b190072910b4510300401c140042c030784230595003585c01900005103460b02d44510110501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 476161636 1250 476160386 476160389
    0x3080f0709120609050c04060803070b06030f010c021506240c0c0901060804060b0f060a051606150e0106022b09050303030109060905090c0306060105032203050c0f0601032a 76
    0x400c40721800d105042001c00d91040026a000f10b04607900800c004003000148e440705d0041c01d185400500c01d40000519170a000364001c20028103441750303010350312003031402c403000d40e00080f00513400840b002442042080c0a6500000c05580720400003111801120038800743c04480c1d140581c00042c01214800103200030f601c6003900170306600031541d44000090141c54141d609407440ca141000c803010528114900e0001104081c0071039040c1030724100d090b50903800c500da903000c0039484621040005075981c4602140d05042c810050b1403541021000d13540c0319016000002598882e009405034002d09010305896040d481c1520402841c0d4440100c5020880303a1220350984008000071920b09101d41127030301910f402800c200002e54031540d040d0740e03c2d10701e01250758150f0455004038169511410066a0061440d8020160b0070281d003221075250444042c00d0700010f4012400b00d007501c00c1070040000c001e07079001c001c10341035041d0f4440341005130f4004103200d00c61240036010980801c03003422660 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 476162886 1250 476161636 476161649
    0x90c1908010207240c140d06050904060228020c060a0c0506090d0210021207030905210909060f03151b0c150105010206040b06060d02072405090a03080f0709 69
    0x5403909102c1c5005101c1000320300900f00c40303501341c24002070101c0951140320b64424403031760345400000454106103000d6005048052950b41c6900700440e00703883e4150a203028038802c48005940d40304000050302c141c45420500e4451a003020301c42000c2e154005800300d090502180d5880d510101014144ea103812620001090f5001e14001c2042d000008035685410321855001da44c00c0d0850000090128450320a030804d40c2804540440c2c0414031aa1003041418410011600411000f00c02011200415407080452410010703880074182400f5081c07a4122101307545080c0c034807082c2c0b000240c843d001c0917002c41092108000107414405100d11460710003508003042544e43c8c5921b4051900c0c0d00311030020394040b043c10000003c69500c00a00184555000700c19911740c0c1d1500800c0007100d51200440d1a0b4280d000d100e0306000c5078042c29000c50103081d4000e9021071100c540c0070082518401813208071103410109200000ca5040768810758091052101c11a0769959000151030700b1441d5000701 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 476164136 1250 476162886 476162891
    0x90f03081f142b0506101d07030b0d080d06154e2f070c090f0207021002010c140c070b070b010f0503160302011d06210609090c190801 59
    0x82c80703c00000d400042d01c58012004d542c807560f01c904c400c0c86034070824460744a4140020b0809905c18010b01c101c40e400940070b20380440d010345e51100140780b559500d00241c41543c00080c10b034402c41905d12440c002403000510000d50614066005400040c0b03212100c403605403030b40c0707a9a90200802650000c145048040c0000300094200134502500f80208400b81803450007140445e000d141907101e64510517540035007410b000080041254070740062000f1510602c04100c0414080514014410441220b00300141c0f103c003240108240303e6074605604080da45048004602194802545000e807640781d07582a41d10000900d0141c1351071960b511a251600b00811848204504060032034102d40110a040d508941c40e00c08040c0c49801100200c01542c010040c10401540904050704403444400d04070b01400400c40c01103082c680c030809420480c5550286021840000901c1c006d800032400d4995075174603d041c600450b6070b0001c203100c580c8603904040b04031854410300364090010f030408800a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 476165386 1250 476164136 476164189
    0xf0903020603102607050d15050c0a0e0d02060301120206070203060421090e010303080a020909010f08010c0302070c050603090a17030f0606090a0b0f0d090f03081f14 73
    0x48692052580128205400515901502e40c40161480c01c580c1c0c00c66401351451754502401c000042c0d5100c10111a50802200a05031a40c218440c07036100d43c030f84c054440d0344e0b40d1500000400310b00d21001c04602c90030040182c4400760316090b09480c1900c90307810180c0c10415840c000202c1e2805000740080d818407607201000304108502e0103d40070764555071750300e5101021107641560a9001c6000c0d84000c030034221b0042011174810340e00c00d500000c0007480146400c2804020039000c241c00d81000004500e280005c000007903091190f004001e80c0b501d0b0460408846985104e40600d4a100d13a0344100004030100d00c0743c60082c0710801806a212004107400c1c02030380c507400015041225484030000c00381c0005000c2e410103030101c603010703400140300e16517883c18400880016000091018043e40040c490b0101410a078032800740c00c1405240d40715a00d00c02441d004180540081410121900c21904112a104508071488c15a1038070303058080035525510208468010030440b4a0302c0b400700200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 476166636 1250 476165386 476165401
    0x60f0a09020d0b0a1d040602070506090606010f02030903031c1803030509061003030519090f0b040f05040b060f03090109081206030c0405160c0804030c0e151f0f0903020603 76
    0x30011030010040520911008a081004c801c005200d030f000e090258000002070003145a602c00c1d4400d110b000300500302003a40d158186044c00032074090174154802d00500540390b03040b0025041d100081d1006525000962001c25124016000600b086000b00402c81c0f000d150075802c0035012042d2060512540d4a2906008000e40340c15541900680640c0d40495101c44003444054180d0b6007549406107416081c60082d4101d080620f00b500401800c0100401d4120191321b40b840203011411140e525942421113001400e0265403141d4412498a02e894015880c1c05080d603800522a146082d103d1707554024043c0500403c3c04d00800c64000003410780c44003800140c005018440980481d18202008010302c4111007007900c00c40100c0218916075040c06116194103280107102e100150308213681d80c1c2d500540381e0031a4021002d219650400c0004000403440111a80131003240e8845140804910f50840340c03020b0f2051700d041100d41c400400300c142c00303800c4090041da40640f046949103846103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 476167886 1250 476166636 476166641
    0xf1a0c0102030c071b060905060c010e030c030a0806091b0705030c0d09150807140702030a0b040b01031e03140c01021603030509010606050717031b0406090e0708090601050108060f0a09 81
    0x1100c01d08050500c041c5e010020078141020354400e511140b040d54202002c004503904260702e800207643d00e4158084141c08240003800030b14003c60011a00d51118040c00b0300035003001010305003e075041604005643e007824404c803189401c8000c80590b02e621506200742140304e0700c200980c9601c1810b03a11410141d201c0179020480c1c03079800702c10f18004107219048a241a06990322000100d80050201e040b030101001003101a04c010111107070040e440e40c60b050092402ca03801e580c11644036004009000c0c110900d4092040300380c00c041140000c60750040c0c403401048441440510000c42c441c6020b840c250704841003684000e0904030a1411803a004000d00000c4450008950070401c0000c0c0d120f00500554186d00d900c07000c21420611441e02040d03094100a06038031f110581c0400f542528500f100041019040c1e540d07524164504103682c040d007600002e007424041240510810541003404100d00341502c6c002d107840c1c030050b02d40c20005403d000c00801019481030701d61000050313920866 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 476169136 1250 476167886 476167897
    0xc020f0105090c01030c0f0c020f0d0534080318010c08030406150504060513020904060509130b01050f0603070309230705030d0e061806190e011202040f1a0c0102030c 73
    0x2643c2c04e0001e0408001b00f2201a01c0704040d5038085000340350480c005140c00e4100072071070400901003010130003107610799602d4200c080303c14950450703501180d00d075200c840d030000c019101e040440d000c2d9020700c0c6c0029666244034650300305c068050701600d410201d81c81041400320281c1c01c212102c0d1a0309183c1400710051800d0480306160821402d80081c1d642000c2c000c1804845000301880b00e050144c80b50600a580310445152780035a4400b0086415600c55000300d008a40d00d9005d608402220f2400d03100a10701030b0403c0d440381340e04010501c07044e03a440c07003203a92080051601190103142c0345010241040a0340314030801f400b400e2400b0100d41400500305044410440c129042d00c3c840d82401c0e03030b0707000e88080042c4d0072031820803060300500035040641c0d0720940e024040070f10b0b24200d69855844031040e00c4c600800aa82176905c45019a8000100503046200080440c03401c0e282c940d00c1c2c0e07801b811901c00c0c007081d801c1279402032200c840000d0a0707403114201c1c0030096503645842c112008a03940003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 476170386 1250 476169136 476169139
    0x80f130b09030f1b0d0c050303031311010e0a03020f030703060c05090405010e01050603010b13030f03030b4f051015030603030801060305250e0103060b070809040c020f0105090c 78
    0x5140406000310070002e152074061440c1c50b05544641e03144c00a1045034000030105070340a21200c0300020340b603101040154442c03852081003650342e01484c81d09030b800c004c0c8400f40d58108241d1301d019070b03241d40e6544507413421291704031401c0c0b00c41c00001011a050601c0d0307900103404540381040b40040b494014004010b8040200c03410801aa242c5885000100d07080c00f0f0207400c92000d100500c51030010034001d0042c40d006807840c0c15082c0d13481d075494a00a54500086000a460b2002d61031141030100c0410411222580d800b400900100310701e642c039541d41415401d0441c2030113400a0451701d100c0e206a42c000560106100d1450400d11444e440e1380d051103251003041310b488001012074817038800d200649a142e914154940d00c0c162048020b08800350050700c0001015000d4a0a5116441c5034141c60740343e038940340d038481d40c020005822603446c0d81c1b06110800b0100156000140701808503510110112800a1030740c403024000c9280a107413003d001c00070342c07a00051000d80e10b000100225450030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 476171636 1250 476170386 476170393
    0x4060605040f0e0c0d020a1806031a130308130206070b040506060d0c030b07092303070603020414060a0c0b04031d1c02090402061c021308120403080f130b0903 70
    0x400c40b100000300d43c048102c18080c0c3d0080c81c2c09034420318107490078030106400100001e1200d43c40710744610a01310f5848004000c207070740300010001c0006001150410881255018603e0300d09403100710310080040d140201082103000000b004240000c0c0030a10580e0058601d5444820340c0c5000d40c80485e0a079810344071072040038006030b0240391400d030a401850380324026050302031966032141560400503048805108103180d012030807614941c0035140c0020442d001e42e03c1c80104900703042c24800c450f0441c0c020140104024030090084a0041c450500181d5038070f5070314951440308488100c141d001c014107595540041c402071580c8050408060354035200c211002219150030045603644e4124000030100c1d01140705405803500c050415032183c0040c000314a06403803601300c21410f818000c1301c2d0140e50740c0401e611820441d8178481ca0042c000900007088002a004c4071f2160300d014510004145540004800b02030902440c161141801e404049482c0c0c3e42e19110b01410503002018020301910 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 476172886 1250 476171636 476171651
    0x32309030f24070e011211130f0b070f1709130c080903040f2114100b01030612020904030e030102030915010504110f0f090a0308040603150509130201031404050d1709120c010b090406060504 83
    0x10032900c100c4088541c420701c8000443303803541d58200b804070700c85200c0020170700500400c0040d40f245854441d184446003400600c40444550242c00500c1c0600540004d500a000c1404031013101d4038007400740da40c0130a800c080a00c0c01106880c5800d1440b000500b00110402e4401c81c079980000c40b2241100743e91410302612000d000110200e40c5184120042c0000c00c82c444005424000400c5402034082e192622040c200000800c0c260780c4180d4a01c500b03a404010150f0b042c0d0b010740274007809014100d5090080041450384091680114212400d10580008a141c0c840000104031000c890010f01a200d00700d6490402c45021b0300140b03d11000300f2b06184020560070602400f4801780e8000601203641070710b8a280482d010382c02004124141a0307112a2180c2c4030400c0002c0c2842184140300030003010360081c00040030218083c3c0080c280c0070004041c060408004030700c0c44c00540c84051056200d40d520320340c0d140134081c0002000d0b08080b00302c0a1200741300c2681c1004054900c1900c4c2130001c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 476174136 1250 476172886 476172899
    0x80705060a020a0e100c0c0b1306080411040b1c0b0f06010507021003020901050f070b180a030c08030709090e06060a0b07032309030f24070e011211130f 67
    0xa118030b250000004600e074544482501e0b25400703c0b03060b6017a600c1c100c0c400720310780e031b440040c9108644c01c58005c524003c15800e510004500903a005000c1c00d141c44074081c105543e40c00390141111500346d00c107075113907403900780f036600d03000744440c00254400e00218203401c05041200800e81c068440d01c1d4200f0591000407803a500030003c4039003140d40030740201000070120900300c000b0741003032003100d0411500b0441c40f0418494074014221560203100002d040e81081501281800c44240b0315403040d4001e4100301c40482d800100100030540c000302030513a00e03655100100d51340103e5400c80e6980c3c902d455000902e5860011302d1034460303242a200260095190a030090580c021048001d0000301c8810b0141c2200c10036800e00c5503c2000425003d0829488000003030070328030500010443c683c407910407810150099801c80c0903007041d0310916140c5003480c2c24003c1424481c8100203041c8018820003d940c1600c50380850300219461400940f030f41041181034181c803401748a01180c200e0592804101c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 476175386 1250 476174136 476174141
    0x51603050c0d080307030b0109090c050c070e011a03060f04090b060a0b041401050d020906030702100f060302090a020a0207050a060c05011103070828110c011406010206060d051207080705060a 84
    0xb102c0d04401c1060540c1e0702c20303004801402605c041c1d20304000c0300300307030008400c1e0103030041201240b2103840d00780c1c40d21440d01000b80ba0500d558070000388904040c004100c1e401030120142400e40040002540e40d0b42c0340340114483c0c240d00c400c4c15402c64600f100b030b20280325519082d28010081111341e014250b40d545a000f105001d41c2c01004142c216107540d4040560241e001001c070b83d20b60f0a00035003808891000128650412034035200982c0128004802d805442d03c0380e58200e02e05c0c4502004040e08540104440c0d29004254070019030740003480e030b05020b00070059000244030080205441d951651001041e643c292003044503103600b0f0402d1219a0140e10040d2232144100340d45400d01503580842c500f07a070144203000006000c104404142e00c401c02801001307001c04210f40c3c03046c1d0795520700d076040e0300f11150003464200c03030344903601841010ba03804903060350001400c40303485248008a06203a402c2450704081e515613040c0000f014400c01c80072102070f01c44503004109484140c0c0d03c41440e0404e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 476176636 1250 476175386 476175409
    0x190b130c180c030b03250806090d12180b040206071709010e041a0d21021605010201050f0a1a1309021206040b0402041a030307030309150b210a051603050c 68
    0x141a0080b045000719035a4115000f4100d10724041c6c2444003d035640140d07801c280003500c42140c20f421480c8001302290700a000b09840c00035064040043c4881001c0e03040c4c0d0f00c040b01000904111111000c1000d542d2030382e05990303249400c40380b2400d2000072030440b4030040c0d00c01c104042c0441c0440108502c07524041c414000c0400c001d031481d43d1800b1110007040b03030307920811008031080610700c070074158a803010b2001099000c045030000e0401d141d030440006040304266210504580c140404c20242840b044100d40c3c10107040003007c501c40070203200221017020310b122000d8101c030105071180e844a069410803020300380240d80c92101c44c143d803403089855400498019080c1c41141000c54014209584117003000e46c0709030f4980603078070348480c0028250340c451f4a094002a0302d820305501803002d90042d69100d001c1d050010040324054101107103043c8040e4100000c40c01116040240000c1c080c401200b1641d0f01400340d442e082ca800c00303012002c070603901040d5010310030340c5814491414a41c11603070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 476177886 1250 476176636 476176639
    0x801060e0d050601120501180b060f0a0303020c091012063e030910060303022a030a0f05070503031b0111070f150615050c010e190b130c180c030b 64
    0x103e01d80c2032000002405440c074408403206e641c0c801080d404070075811011184144500c0c5400191b042503010840d2800031086428071507640410204000780d0000f50f1100c0085040e20038200350384d210700980e17029001c08c2e404115035000c2451924104142030340006982e803021030b070700e5013092a81b011604448140144544005c144502045d402c620b01801071076100c81458121480340c40b0901200301910392030341c4200c1c050791007844180c41e407903240d50111140010010103c2c02203244030000176aa2800d0000c0a4003104403400384000f404000e2001c9030161901404403035603500840712500b094104101c100345c0350752a0444813050030034814104c032900c9400410240320f0b03141780d8136440c1c01110703048e44900101eaa01d040008140c1001c401c812036000d80398580310348a00480c05070238256220043d5040460304078106000c0400d00d02d250144a041d0401e041c00c8503940c940c80d003406004041394014025545800f0f00007101440c60360320282540c915101840f40c036095a0094041d60b141c6074105 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 476179136 1250 476177886 476177893
    0x20a2001022b0b18061216141825020303090318030c033715021e03100609150801031509140105060a0608010308031f080d0801060e0d05 60
    0x95500600e501c40c8800302e404000064018100f00003a44c880309070541e41e16680e0b202e6003080400e2404d4201c80d003205100102402d00fa403845444007800911a0040d8170000043d0046e04141d80c80d0509543c01200716084000786a09082070440008050b070f03a1040544802143e80416061005c030540740126103840066046c02555003c1252180c90b0918554051040b4614046903a0b03082100c941c0804410b1005112070510900342c0070361482803490082c107695400c107036000096801c16005075000c254035005855202d811200503082c40121700f00c002c902400b0090054040e20201c040c411540103459030080255030780e0019101030044110f000c0414654401003000c111680040e400180040d44000356008407680c504090f60005e07450300206079510010040d4600308103140c02d0180a01c1e05150165615580d640c8140e40302c010281c0308014404c080c40385480100541d200c01910b07071941039500700c02200100a040c00c20034860100000c0d000d1019680d03a0404140038482642c100000e0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 476180386 1250 476179136 476179177
    0x80405090a021c240b0f0d060e090f061e0a1121061206010302030a12090f0e0a050f0c07030318170d0c020c0603070e0310020a200102 59
    0x2049468080100322240c1c840d02004680c8260090b072900c55201c100184000400e4251201070041041882c001d42c0700340c00f09000c00b405900c0d030b85d80030b5408010b0a008150380e81d00c004916000600802c2c4d20458407415840244402040c0200b010201500380f036044070002e84e07454107540020820029201c010741c0d80c02e00400c4581809400002ca000c5009140c7d030300d00013135085c580c0c0c03101c0c51004c64030305d03040090000e10129141c00e0305004403500c140b800611003541950002506c60049090040c602e61035524091a01c0b4000c1640d08014101e92198480b5140d541c24001e40000080320405000c502e0400000d000e4014640d281c0c0c00b5400041c50705080102a56055008144a003041b80c19050700d0001000040c801200021401c00a9116180c03180c40c4180c025040d1841c2c01420b40c190f41012030a40c00545484041d2035000c0b890746452070b5141061008070b07090148214044d514140006118000e99401c0030b510080c80c1d440325040340f01a14042401d078200c0c010904403030f80410310000e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 476181636 1250 476180386 476180389
    0xe030601030c060f090e070917010507051b100903030b131b03020a020304090501140307060309030804150f0504030305090d180618081b091837050f0d020a080405 71
    0x41341e1032240701c1410502d80c01612050b00b100701040881d000000206150000c0c090b42c50307009940040c1007502c000074095801e08250103005400b90805045101404024000548604006030403400c201d60004000681250600070054542070104900032410318013005418000b034815180c40d60b10b0340c183c091480e68a0326044029621440d130020442c4000c0c000480c43d00501c1c482d150007407010030340c40d003880700c2c081c1c003458104101c6a2028043c0351034074020f180400d401c0409160b00a03400710b404042034031072006480082000600101c0350318513010800c000c058243d0b02c960301500d40c1104440c9121040d410445108441a20000d0a030182d141c1c10042c91340500d2650400749000d0f92401000e54413081418a0680079134002c086802d41c5841e00949400d182009941201d103012a0030301200540a01a03034480300c4075440700d83c03c0050007040306a044881c0c0400c3d00c1c0003030703145491401c00a505009990740344c0310074038103158014a04c8581c141e0b80001100c00486900c0344601c1c0c1000d10302070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 476182886 1250 476181636 476181647
    0x6030c0a150c0b15030609070b220305031201090b12120901020c09040c031518020d03020c040f1407110d030c0512010b03070e06211003120f0e030601030c06 69
    0xc1c1003070500480b40100d000103190f15282c180703e5408203001c060141c00000405103440405072510b60241c10004090040301c403014103c420400340b4400c5010321032040c1d079401c016013132941d101520900000c251a620300c072a0403010742c100c501d40e80040c001c0c000d02c1010040081a2800c4020480c2e000a0240b140d10782d01001404007420140103071240c2070b410002080d2030900c229002c03200c01001d00018010040f43c11000704d43d00c44890710402040d44810b46001c407207038250101a00c2806544002e10800d482004251a004000790060001e5180403042502801d14224540c0503001d603400080c090700d00c9444021001c0c00310301c2c01440b680c00d1601056000301160b078200701c2001010068480c1a01c0e032a0009802844895a182d1356482d15480c020200d0101d400554841d52040090010054030070881d050041c07042c05401e007031501e52031060500000035a1009000e5529131582c03541e010b03040044824040d590b6128000d4045a4000305a03e600c1c090000a00103094030109010152080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 476184136 1250 476182886 476182919
    0x639020d0204110a050703030c02060105010516170412110d0209011a070b0c0c0d021c050c01150e040b010906080303071d09011509080a0c060f021c08010e06030c0a 72
    0x107440054200303e480720981059200302d020f04d01040c03002030b80000305549803081c420543d55500c0a02099414000000c02030300c00c050f041c1c00a403111403510018030140c91072a5110702c580310107032540e82d6611040e20200000c00841680e540700b059251008a05154141c07020700780d8002c08040880e82001c0306000c041c0c001064800d8030410500001d0001101c1030b05490007008221105074945092028061511180d800f21008640100c9001510b04c484546800000c0517241000d64440400c40f0410f4014503501c83c00400c4003464000010b22840700c0d240f568059401001c50019a070388822000003511480d00c900f4005034801c02c0010200d034891510341e900402d8100c2284da08140900020310005000c0c0c00c01e510320307105c400e5500103203600101d01e5002401c0243c064140c000058a8900303545841d0b124090500c5080c0c010482490b201744055482d00c072054503903002c01642100001d100310002d0085207140030030107010841c149400942c0c440500d4004080d403c200f03040480914201900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 476185386 1250 476184136 476184139
    0xb030c0d150305070e041509120f210c030507110c01080613090c051212040306180b0103080405010207060306080613060204080703030201090213020a080c1c060639020d02 75
    0xd0207404800034605020b1800280302c4900000c2c19402d16081100400080180c09030030203162501c12400210740300d00150441510303080410314100c4114042d1045e841c066448a20081411084421443c2c03a034411455190503540811070395907030500c1910301401903002e4101a62100e13100c84180d43c4103082c0700c2c1e0b05c07240107410500c0c1c00341d00700403a00a542d01400308440102201d201804242008101c81c8400003044000b010840f04022442d0a2072060703000151805850303800400444910f0800d810200c2d40c4a001e00d0503030340e52400c02c0b60542d003050140078014000d8800010310b451180c040c80041e01d03208000b400d4a42c688a448090010380100e045503e141c09003c0015255002e00400d00294043c2e000407810540c07a204202d0140344815011350342d580706210070b41d03007603520920070340d844405c0700300f80c3e6992a20318640c0101c503d0440816a5010b050001c0860602d43c403d1003032803405003881c8081d03849400362120300301c02c203c80030f0100403038024109404090b180c03450040803040d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 476186636 1250 476185386 476185421
    0x507020f1e0114070c060509120414060c0a030c11010203040b250212070302010305010e1308070314190806010207061413090903090f0b03010501090b0315090f100b030c0d 75
    0x82c02d1034030b183c21410458203400400c02d610005824049140101c0e640b151410025017900300c502002d401c4a4042c6000b00e48400040082d02501c80e201d603011281400c4139081122058481d9241c0280074040e216001c072041ca0750080c900c006940000151015614440b48103414120540e080f900f080580020304e07496221440c0540f40543c81c2c080700c4c02c80c0c0340b0141c1d010700f403e80d007980005000c1d40e106a100d00e00ba00106020401020004540c0602e515804991155a401c05040032500c5c0d9445682845401c10009040305a56442002d0b221401001da180c041c21659a0300041e078a5000754403420022440c000c4586002c03840040040c401ca40380328000000144c1c803a21300c03030100c49076580d04801040c01c0a80500c0600130b1a03501400501c5038821191440d03060100003007000559110729130f05124040301281108542e020300802040300a001403006151880c1400700d00c00301965080c0e0305201003540803e00d00c4003d411244900040d918079458000d60115120041680d1045e003402b805 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 476187886 1250 476186636 476186651
    0x409020d02130f1802060909040c0b0f09010305010605131a07050f0601092a1202070b0907050f2709011d030409060b030411040e07090e100507020f1e01 67
    0x94658204202e90300a41c100018590719500c1c0e10340894480d03100180c0d0301c884206843c40180c1d56403046590500050750700391300b680c840d8038200c2c0540410340c000e86a0a07001054628003d2242009442a944266414010350740e0300e90003500c0c940f00b1018940f054514484050154941540455450351108564a8a000095200d0b03506000c640d40541095402c0400104a410700e640140c2060000d1004143c1600142e440c1204690100c0074146040c0301c0150344401c903651065040d100290303004003d102651505821081d103c3c041d80c01001e101d8420501103401d14101043d00d20a49240c5540c01740d220000702c1d0044040c044000c00307202c82c1d90340b200c1024107401401c4d040244406c08550080d501c40f0f0070000010b0513140365801000441e503083c401c0001280400011040380b9105072400925082007011050411301d85420145ea502e00702921403425040000d8000c0c102d80c9800400c01050701c802e0002c0361180781084840b10b250340a0800c08411404e82e04884d0b80c486120800090405e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 476189136 1250 476187886 476187889
    0x902030f030c011508060c12060105040302040c050c070e09030702040207080d140f25030b030a0204060b0a1e0f120906150302030d0809030301061107050603010306061d150409020d02 80
    0x1940b20b000b03405800e035100e100000300034010268000142a402c0040d000a01e0311a03052240d50080c1a900e004510900303010541d1381c0d001d04221806141c002d03205115900400c40b015056511181c1d0040851080e13030000240e00c0105075450303028000480240d898001581c013044081d410100d8159104101040945240c0245100d0202c06180154190690746490440320301300b13200080c00c04001c0e104210132490348640099102001c1c650350f06001507980f4851010038901150068000d403ca4039150012a00f8105d000140142c9080782d42d0b504030712521628412200e038415620f5801246001541d102c0c0303c1d00a00100b84140304002c2c0c005403248542d10740000f5180c600c0c0e03048405160400f01401541024841600240d0752401e0408660601c00e88040d80c0b4441403040404014406c881d1004005062101030001c0000800954895841e8204203009240505c1403d0340240804810b035100600510114498051091000400444a024400904203821f012644502401740c42c1c0c005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 476190386 1250 476189136 476189143
    0x2030712060f060e0702070e0603060f1305060a0608070b0c030921011b0f0206090a0b072c0f0d1218090203070c050105130f06150506040b2701120902030f 68
    0x200900c1055031300c2401c1c40e445c00fa08000083c0c02c009540030000f01007103690307200010442c1d0080c3c020a088012603840402c171501c1e2208108000385207000e650107000480d06143c204005031030441040c0c407906a0f0b1015080414845e040900025401c24030000e8800d10300a8030321041080540001482c5188141585084034105810300f05090500b0850000c00e907807128243d0b0a03400140001c081d01c3c20031666840c0d4582503018020b0141d031407000090074041c03003000300b5032480c003910f0544400840b118019180313450098007010700604080620714854600340802212030343e04100d80011003040e0010443d03a030032842c4001c100601200400185000403032005511540c1d076562140700d5510945409820340384080c001c1440301c1c90100e42c02001c0f07209440303855041ca07071140300001c101d00c0c055404503401007240c1c8000c2e84200042400100d0020203001081596801d896680b8501e80135000c030584100419801400900141d8200c002003420ba800050f440e070004003111110102401010f00c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 476191636 1250 476190386 476190389
    0x10905151605030d06080d050304021e041514100323040c0e010801050a050a051b031f030309030c080d2015010f091109010c080315031005040b1302030712060f06 71
    0x20350a51781d00017003043c02400d03c010028861186811480e50500750006901c1c0c4130319020554400208001120447d62a54040c00c05c0c0d0407050248004541d42c0d2001a4001c0382401c0490b010302c801c0e06625440c1440382c4198000290300e6a0100b054515010b0311a005040052084500d40c0c0c0381400401c084201d010903a00030310401001284519120030700605481e4050f009402540c18a414420103070003400c00001c680d220741b940180c60340c2c0c5c0c1c01d000c031000d110252130310494200002d00100505501c5422001500e009a0007140040d90b290380c05540c03141028040000240314412030b012186140031800d600a00540c1120303281c0f002c481040350701d07001c00ea011400031030186400304071140031030080300560210b114049045c2826040007030100100c0580007030941c480040001d61201003032020510080c006002c980300d0600039251000200703420f5800f9241003c1c0140010b0240e4102d0540748a000e9016000d46402403400303c440080381307008603040703402c0d41e2107440c03020250105210713400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 476192886 1250 476191636 476191657
    0xc090a030809010f021c0e012105061903110f040e10150b0708030f100e0a05061e030a080c070b070c03060e12031603090f050a0b0601090515160503 65
    0x41d96941c1c400300140c07004c03410081690540d08503500c1c4900010a4a10030341000a20b402c1501681404c03200403201001c4942c02200f414034107400144c021607141c0c0c01140b00d050f00341c0300c61044400c04c0c40392034150701c45807000800c8608410318110007810220009081a4000b4102250038112500801e007440720702c112068000707607261501035801080c0c68140d4000d107842d806e039030b1501c0c0e42c039141d4040c503110081c2034061105203480422042400314a42c000105448540b800d69820140c00c100c014001c00d4031040d105509004000303c1c13811400d42c0049231504014003c0201c4605a52440c00b6900700321440c1d05140640c0f400041e010001c00000d01409200d0491850402e0440c40c1410840304251341203825a030000060f41e030000301c07400841e40c10a0a44020f10b0460102d00e1045020300070340300300105504549403040080203400500071148500c541413485003a6200c1004642c3c9503854480e0580c06603040307449100d215204070007003100320304411980040c03104039214240b55601c0040f005c1e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 476194136 1250 476192886 476192903
    0xf02011b05060601230f09030f0f060114040e06160203090409050f010c030b130f020421170a0210051302060a0206010801050604090c0501030b300f01050702150c090a03 74
    0xf10f103540e40714110300c2ca000e40103501020f040b603000241c0704c21070140c402d0300c0c50011000182e05079166810000c2c914000c0a0f40101c4001c44810710545458602c01e01c10540c050030401c20302d000f940703030034080d151058407148000e04807583c40305c00b511840805000c8000070744c00204042100781c1c89a000c0d800d00389004200078805000c1b12102c050843c0c1c00859172000301441c3c0b2440440315565100b11000c01281c0100104525100740e000c1c000038815030384840c4e83e882044c0ca03620703c5585011441ca404034060031b105e43c0c1c04032114140880902c40c1c40c14100040c1c000030400a00814140e1200307810150100b184410320905901040035644200c464201585c0440010840782e20b00b40a03190340000b0a5406000f5010f403070391800b00c0c101c80c80c006c99041c181c40b8000e20802d40c0318150448038001030380840d841e48c0c0100024603103404000c081d45001c18052202c0700d080540e014080d182c021311392680100110301159884905110016000da10040420406c1c0141552000da0a102850060115 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 476195386 1250 476194136 476194141
    0x21c0606031a040902100c030504091802040f050f0117121206030f0a02030705061c0911030c0108010b03040b0714030f15010c05070b0d020d1503050106050109080303040f02011b0506 80
    0x401c03a0149403520035612a5013803507140b100585400301707001048020340c28020700c0c8130705505d015103042c007075a08821801440c101014800303e0301c0d908041041402035408200300444040f1035816031b10202d8000a01c100c50300c004100905031200030b04144001c0109403800a034084d4042d80d001ea21842e40490100450740500c0080e00e000c0c04840e00003002d010080541400d140d003c691a0500d910800d4440c2002250000000c07620016051a103902d00208014909082c40c26403810440c00c0c13206030280c0304481900d11b02d0750041c1c41f00d5047e904110400c90840d51959583c1d21066402010141080b0021036443d0f4503940802c00b650142090080c0074a15180111542048c115803250b01810044c1c044000301c04100040360718000d503021155060b90b6901e01d400c90360068458402d032a980646032500e01802e910001903a001030324440c4009006403941d0b540112441000b42c000c022458004201160019100840d1140c0301b80c418108107032800d200d000c0312000100c09007800c0c1ca094009408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 476196636 1250 476195386 476195411
    0x1510031401180b03030c101a12061f1404090f0203060c0c1902060726040f090606090b19170103150b01050f04030b13020901060513120206030a021c060603 68
    0x41c3c43c100d690706900440c1812081182183d580010503882c5800581d901800703c0007060b80b04240d02c400101801c0c1e800001107124400380c2d2210101da00203045490001d00207119214039080d0402c0710b0f080408a00400e00d02401c0000608100300111102440e4001035030060b02d040c008188510201c0e0070301c0341c0703810144a0481c24280c045521201248080c04a0030041e50340034203403800135070000070140f152440c001034102c0031410000b00d00c09480001c603001640704059a0304105890101c1018801d880d540d002c2590b941c17429001d100010181480002513100241120751000c0c052031414055103043c00308070100922007078005803111203501c60301900c81400f5000780142d4487c20b286c21480c042a844208d001e070f02403400018040c0101ca0081115442081d1001c2d51040e001044604203594882000d85140c2c410500009011b41d0310703c0004401c002c0103500c40602ea00a040300e0f20356030f14003102d00c0081d844108240541313000204a114156810303c01c1718060411510001110084c109 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 476197886 1250 476196636 476196641
    0x260f150a0b0405071218050102190306240f051306050415090303120b0105040302090703021b071211190f1d0910020a0516050a140303151003140118 65
    0x2500c1d8007071800c040a101340c280e03000403040040e40c04404000707103480e4220640038400b034031204041c0c9190700200d4400c0306000302030b100f8010843c0d2900d0803c02180e4565401210311558650b503040b038001000c000c0300071800f0344100da00300d00c5980b41c401c3c80c1069aa80c0030505100b141c00c00c20000314041801d00c47d6400b001c0e03056820301e0050810b141464910b50b4020144009040300044040e1204510341059004c0c4094501a5500038800e4086190940c0b0040c000e40103d4902c044048100c04070210038a4042494410f54140c078400303441000c80c9445510640348880382590b000030a01c001e00c581c100700c101c030110281503c00780b031240f202c0c41d10a001f00c0c060b0b042c150820350013903a038007404200c10340040e2003290310180140160719258030817001d881c28000e01030f00c0c01c090200512144100100426000c10075071042c101c01407280717607034030020f070f92030000b240c040b00c241900e01c0960005103010340e500c00402e182880c0c003040d00c1b8083c24841c1c2c1240404c0e880030043c24150001e2517001901070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 476199136 1250 476197886 476197901
    0x312030f0e12090102010905070306020c0d080103050c0906120f01140c0a090512071e0f0605070b040b0402271015091415070809130204260f150a 64
    0x11414816101071620580d01d580030540c0000000c00c0015881d00c4590003900071804e102d403c0070a844185076070342015806940166002c2031170b4017401c41c680c0540c2d4021206a4181c9030040020850110008140010342c00060000c5a1291011162040c1248200700550841d9008000442c0d441e6a581020281400281c8103041d0108140010303d40d0b998418504011144c040380c90756050f010b0031544d0350038207006800142c48036070b0750131fa104001000c1c801c100c1c0850781000072001410f80d0764107080f00d5a0188002c01007801074075030007180c04910085825a04240003c14411030450b11400f010380d21360320400008003100e581c20800410b05410382c4075000904070340e0041c0000380e0a240005040c0c545900901e0161885485449481d0700e900c0c06501b83c2a804a10032951084507090006030350b040244481e10403194040c0d0f11304c010f1028000c2e01d04481d080490203100210902d214500c0c041d800c14500c1e1184540811001c00300010802e80145002418180d079107030408044a60546000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 476200386 1250 476199136 476199161
    0x30c1401091a09210d05070b150604050910050910060801171e030f070309051309020f04020a1b03080402120708060a020a050d05090304230612040813031203 69
    0xb000345010060300101226071401044620503d90004401880c91280150703d44803018458105240b1016802034005d140380750141c0d40184407560f0700b2000d10080c40c0049045508403405010810403410559040c0d500b03c01400622115603403110046054070300c04035030130800360b03400c0d8000f0010f2541112016024004401c10009140551040141c0d40c3c001c8034411034048c0100e86550704480014019038100c00100c040c0c440e074400c06411b0090a503c100d00842c0d21070308a8440740341c91103481c0d01c03564600350f5010b80075894100608007040020f400500301c00d41801440011210015045414411054402c2e19100640e01f85070040c428071100455284d4401da100d080d0038014100002982035004060700300150341da00240c0001c0365076000701c1d48c20642c09410306d01400071300340e000f00281094400800c80d8140750809013a040b8080d03401c2442c00c98003c03004001036103441c9400030210740c1c8035004048081c58446021075030ba0818032a54001d4540f8a5030503951066580e00d1b0281c00b0b0b41404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 476201636 1250 476200386 476200409
    0x81501050c06070507141207140a0215031003080c0102040e160e0d15020a0801060305070309111314090a02011701051e0102011509020c210d09020406030c140109 71
    0x5005511a5900720107083c0d4020b1182c00310701241082005260601d0601001054510050400e5514003007a046079000b1189031400b00d051101010000521040f040d4004080360106030304400400e0180d8400b4000c1c00c2c0d2820004404404110844000c21442c2940b034001640d407890811104103100002d0910071400150106032106264032403111038045070108c032042503148030b41c0703041002d010a103500941d406001140c0300c103090340c010030381ca4100c07041520184803603541c581f0201d04403580201c0041c440d01080c1c41024090400c083d0f500071500a4400000d4003410500070f10f45801011101c0381c4c0d50f0750060118404650703204080c1c4444510882c00008154145400560f900341014801140d0458907031013a2504c0e0f200350003d10041c2016144030000d60380340c440c1d01010b903010754140c111034442c3c5044400743c4018254440c1c40e01070803164007410020740b01d09000142c20790718000c3e40c1c0140c036506c011000c030300201c0c9510005e0001940d0150030a1361880050b260000541c044480f110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 476202886 1250 476201636 476201647
    0xd0e03060703020f040b03150d03030b0f030304060210050c0705070806310602090d02060a020c0f06120f0907081c03050f040302030406050c011503030203030907080609030706020d0e0a0308150105 86
    0x4a020701920156503030513018548035900c08c0c408a6504204040706540b0040e600703508000d00d90190b1008980d6101502c00d441824031003801d05079a8440c5111720301c01039221841c1600131a000da8082604540c102110a00d030004645826180185503080301c4825005941800040341c0031806a10115041c8203141c03181d400e001064a40118904001030601a00004c19580940d81d00c4007000320190700900f00c0e07460742203050000b5a03800786e003a4803a018201d203030441d00e0740d4600003040e1814031030000b211001c07903920b400b40c01c101f00d00050310600f101d100d07190022031107a01c180700803188600c003090a103608030b400c4da500a054134005040241407440c80b00a1202003940482110180d981d141403040c1e40700c410340c3d03825006005410002c0c02d00c42110b54088101503000c0015401410f100080741c080503119548603485103404d0b10041c3c0c1d164001c000200024110740c0281c010803146140c0001c000e041502018200780302030004400007040102001000031007441c0d2a48040821718001e030401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 476204136 1250 476202886 476202907
    0x304060f02070f0902070501091b0501120b090103020d0302120d0c0f1d15040803030f0a14160e060d150807080114060d02030a0807060b030c090f0f07110d0e0306070302 74
    0xc011138051071403082c2e0001444428800d00f50800d507042580113019100080003070552070680c002a02800b07001620341d440c0001c0300685ca0144d048220701c007c4c005042c0ba480d503800c0195050ba640411800d50055000d0300140101950141c081c80300d20b008042500150316030024000603135009482c0501c006444012041b14054101404034001034503407100320300400e42040354900403a4044007107440008200050308000080c81805401c50103001e21891a0701c140c075010f2143d08448a03190460031580c1249460301c1485107003201a4060003661509800e00050010355002d450586452058410100450b50040042c03134024074650000f00f10007a8109001e0880d105d024161600c00d684103051301c4255070302032042403541580400242e5544640d032504101800311040658800d0250380040701c0b4508122040c64400c0427071100d640705503030314614031070503813200500f450003003014070001860040410800a8007488090319020003440e61601010f1400e00014203040400d4010701810100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 476205386 1250 476204136 476204159
    0x3120f18010f02250801112a032d0a0f08010504020c2505120601030c0801020406080619083004050906010f0309150b10080402060a121d0304060f0207 66
    0xa00c0e0403030041000000044403440d05800550b00b003085c00c0d500e000c030311a0035000e0f0b0070014500403041c0d1600c02c14090b850300404103101007280d4010541c1e0001c10213184041b019103150845032814130034404008515201107156608482c04400100f480107545210b10390304502c1050040008076800d5140c0440801440c0c1c90303143d400c0c0c4882415086c03448410070111050750110240001034403412404040302601340e9984401c0c44251089900c0301130200b1031100c18004c84081d10b005407910344060321403405001444032504a4401d502e0748c24480410100e805004403d48481c41d07900e03294031540003804561a4000031443c21180040c200020407050300d03111940d69200d002401c1142c00e00d090028141c02a214000d00104034425240030000403416a91001e00c64903000d0710030304807072a00c0c1d000030384607400162406584280b0600c5282c490601c45c001c07a0f403103235800c8a80800d81034a8000c0038004e84000312030b009242c2c1c10114050020603480410103102c62101d200074203915240c240708114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 476206636 1250 476205386 476205403
    0x5040507061803020301050a2901050f091c050c0f030c0d03051e030a021309091106090d060e0c040b150336010f060f210203120f18010f02 61
    0x52081030b042c1a1030110b10003102000a507000b600901480c07420620103002821020f0078130001580820119001c0d0b0b802c40120090030700c06841d1107281200c00e030070b00381040e04070300c1e003c42d880b1107000000601c106880c42031442c180d00c40c43c0280603400102003000400041c424042e806030780104c0c144042035a80b4031103005010341508006545401c019402c803901c00c101c00740070f03425050000c103008924046034024800404001e900c0002c0c95221178640302621003005016080c01581c869045a600e0000f00400c4400001003102d9000c3d0115500c40c41540e244082680581d0400c0070740c100107007818000d19100920031610380249900035140b603296400003500f64100d42007000c0710b806c0d030440e03240451448141e0150004c800440b440c0c180902802151100c20302c41ba0034100700042403000300501038107807004441d19031403510084103480c18500d029070050764035200d40c0c0080102484400018070f200340d40004215541c40c41c0795101070622110100240c1080000100d1403801540400c800c030723 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 476207886 1250 476206636 476206649
    0x80c0d110907180f031101050a0f0f021f050411040213140102010f141806060607021e180a0b0105030112020d0f08030702030c0601092f040902040306050405060a05040507 75
    0xa8107482d56501295440c0d00c4106084802c0907040d004910348031a0b6500300d007140d12030034140c0306041c032800c0111003901500020300040740350318402c50319440c0070f01c064403c1e862007071040740e02031a40c60611380b10707540d10300c1d08501c4016540c01c00d000511603c0c1c0404040d20324107030350940ca84558407083c1e5400e0302c103c0c442d81d82684440008580240e100390449030105008240600291846400d0300d81c2c56003060711149012020140006100303907001c0380380c80c45281300501d4941000300301c0e02071289402c44141c1e5989885000509a0480d568205034040b6480e80c9580c005080c2ca0020b100004a0749455060f9061040c244010004414141e51200c1240e80c1650340d00000600c0d1b141401c0b4540d1501c60060a245001c010840034070790020280080302840740481c1d6040c0d84e01d120f02c0046074140d05540001c0402c40d15072503000c050918501c80c01150b10b04501d8a00399684a2042c1241c00a800031a030312600e500900050100800c21607070806d00000c0704000f1818aa0344059030303542c00344580c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 476209136 1250 476207886 476207899
    0xc0304030201120e100b091303090b160602031614090603071d0301060e16030e0607030c021908070204110a080612010902031c02060903040602060103110a090e0106080c0d11 76
    0x480c0c80312940e0040e1406000c0b1004403005c4060982e03a07200900b8040e440c3c58000d0a641c00042c03e105106100c60101d2901510350444150070404401d90980c48807080458044079400454009060380c4021032058100c03500411004401240040c034241c01ca01c03000c1e84140b0709014003000b50307440344110b0303800c80400d05004840703144040c9068960700400c000103078136500e82180040c200006404441c40744a0101041c49000501c1a003903049920485140c00c2d0f030b40c000e10010741c200f4042c3d403080c10100041c0c011121894030442102103076a207984d03802c45d801c1d8000300700101141000e0250380d000381003202c549810492244070082029000070311152142c9d001c0c1005100d414020360061120704c1d000f90660b414101742207000f042942c0c4407041d8400500c1407100042c8210404416030302a1402c5901030b0170f2591840c0c82d0754000c00c000c8050385074803101d403040000d4400451f10031903000b5503240300042101881d145405041c20040d8441501409004410f10006100d21450303000c600c5080b03421 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 476210386 1250 476209136 476209157
    0xb1b07031b0213090b0720030f030907031403040602011406102a0c0e15090c0d1b2019060e10050f0a0c14041202030c03100f05010b0c0304030201 64
    0x8443d4aa200c540180040c50b00b100d280602042e0311200b841440e1035128000500030070504039055000030007040c00345420074011180c82400c2e801c015600060300034101c0e4049502e03500c6d00d014040c1503c0b50350170103034400242000601d4080c000c040c4114941000d942080c40c0110104495015100f0301c1c804110250243d64104140d040301140913403211404041d081015103840f401540060084900f4004810300182d940f0b007195407075100c1410040c1c040501c90300d80d280081c10b0364020594880456454030250740207145080700390461a82d407030341e40c030b5181d03108108162071812103407409118a402c40d070207840004a82c0360341130407410b42c80a00080c4030b411801d146403c0c0003c3c12403100d19030b41858284514400300d001c0030ba00a5a842c042001f02e000400c009864011402810490400051208001c900141992000400e0020702a9085000300d030300000d040c1003100f4100c1c1c100c16034601c00d2590b940c155105040c05020058505c5140807028840507542c1e00075844020304101c2001034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 476211636 1250 476210386 476210389
    0x1b030201060b0c0c01030f1b05030c04080d1e022d0106120501060501020f061b091206040602180105040302180c04081506010e1c0204020903030c07030b1b07031b02 72
    0x4544014030b00c041c01d45440d50042d501107515081c128000c24000b0b82414420641940140b24130903640c88180d49826908c900824140c8250b00001d1070385107142020702001440140c00d00c80c0d00c1c00e0b4550340c1c1d41c251101d00c00e02448000a4400305801c000c551005c007610343c41003005414142e01c6800f400403180b0a0f031880c41101d01400c0c2c44d41007507604c0ea0000c80c1090030050150002c1c419101c0036002d45101c0d840c1d503003225a581c0402c031218400920030314100004809a80c004040c0c00302e0103003100528030680403442c1d00c0e00c1002d0310104e94080d40000c220110101c0e48914184500c801d192940c98940b441d000112051129a101c2c1e9010075200042050300d5020001c4400400400e815601d41121100300c0081c41c003002c039138a030701044803410101c140c1e2510803604088615000900c1780c90406540922000f0341203500d031a034043c8030802c4074000c403510421122001b50300c2002280340c035113003941107101d400c880d002e0182d8000000f0301000000941201000400c0c0c84e40745984440b08a4900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 476212886 1250 476211636 476211641
    0x1409010501050d060f08030901110f0c01050715140402030706090605030f0a0e0d0c110d0317041509050303011404020702010f0c23010209010e060c0a02011d04060605030f161b030201 80
    0x5c0c020381c1504c401d07035400225010040042c24406500341c0780c80081940007612302d603d5000315020280d49401c4800140c0040d030190005d040c0c1d05001e51501030325500542e090200f100c825038000050301d00ca03101040110f2404115100213420701c0d14085240f40c1c58800701411501014040219500c24540050603010f156407209414500384000c840c00d8101c2ea1001804011070400181d0748160105042003490406e095803040441e0300d40c0c0c44184c03000c0c0c204900b6465800150048943d44006000441030a030140662800d00340940007550b84c80d49822481c44030040c0101545e0300450051000c200580e0b0032081c1051079000908011402007807500e030041e1384e4810b44075600f0b002a034203048903442d41d40550103481004801c0e221a41c0440c221020410340340a18020006541e11808005006501c1101c0c4d0104d5503220b612420701c03402840d00010706445207a0002da000840220400a40510120800da044010b0040381c09040005250040c0f0081790510140030b84140c0c08440d4003014404d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 476214136 1250 476212886 476212889
    0x3040f060c050c010b0a030c091d0d0e01090f0f0b0c0f011103091608100f0b0a0603092d030f0210050f060f0a08061b040f0b0909011409010501050d06 66
    0x2401c11100316040d2014103590801000d1040b03540c40c3c5001c1c0b8070346003404100241505d030401603001c00d0600d0041210040d101c41c2d0404505031401041028400d80d04100c0150301a1003034865108440840c1c000501640c516404034401921624042188125a01d150820380d0b61390b080140c4e071201a040702d585070010380c440e522695031910803194403c0c0840c4000e540201c108209032103280c41e04142041d101da034a0b012300f03c0c49801046180401035141c0d480511509070511010500000e0b0b90b0000706902e600d03a00801c00300307454209182c100300401c04e0341000d400d032400303070102e141c48055541004600305180007030030300010144030800580208801c50b103191042e0418801840e1220300c1d14134400003964860300440307a807440d0315080c3c80d2540714903043d140e400c0c0c02000250740c2e4071700c08035803d000341c241c02c80c0f5610b04000c085009800348d04210041e203424811243d030b40c60b0381c01c10f00000d03400503404010a21034010940c0030b150b440c600164115a400d00c0c080b52240d0301e08500200600c0f6a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 476215386 1250 476214136 476214143
    0x2007080c060c0706050106030504020f0405060102070e0f0406050709080c0607030e090a0b21250b030103061b03020a0c060c110a0b01030614070c032102030f06030706050406020a0803040f 82
    0x122000c02c050340300101e0003081c12a2003014203001e2070340d0710307201542540d0f82618002c1d4000309860b96208181003507400309610486c1441101c960350f80e20380b02c81d00380360002e403042001c10384a90204421711843c0e005068000301d141c03414042091a014800e900da44030818420320440000680301c041c58400c12010b000440010607111141c03c00300d08010040c80890406806940d9000c0301e0300704100030b82600c101c1800903501400541c07510380403201d206080582c101034903001d1102c2c00301e070740c504e10030145018501c0307031000069940c50b11031000c540000080410007014010810441c00c1b03580320b445565020703031004020840c0950950240c1d100e07604680c91440910071002c3c0d08080c441c8040311503048a004a50821a01c000c0400e0301c100d40900720307052004110145412400240700310150000c3d85001d05500ca01915005038900c240d0b8415201d4114880121081c004545808d1142d00010710407401d00301e01d070030701c7d2400194540c0d44c4084050104000070000034140310840703d905015651 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 476216636 1250 476215386 476215393
    0x190c21021e031c0b150309070909030203120c0301030218131502120c090f13090606060e180103110d030c0b011e08010e10020705010207240c032007080c 67
    0xc1280d2050340d035042810f441050010180d00c0051030b00243c0f080024034135000d40b181c1880503044018540c150301c003a18000240c41481c1d00068005850b02c515030499102c0e42c0555581c0c514450304400c000c4010f00302900d511810001000103030f40304040b2940a58100461002540d1030b0301c580e031000307202ca035005090180c40c2003040d603602e9101d030300814003c101c1c21099241c0c0e4032030441120b650700503110815000b44820182e00300c0741c640100c034000601d83c6081c000c242d1406035075401040e40d00f02d621040c0821652090030b2014600743c00c00008103600f15002421662558031516a0050f5121074140190490b0b0a0302090501c40c1c1143d51403a030300445403c0c03441d60f4500340001d4a2061440c290355602c2861408a0100c04c18003409a0a0503004010716082a9042003240290b02c405000c90305903508001c12070000b2480d541442c143e40200005a140b0380c00f4400070801e4a0144006034100f500d002100e01030300d810007800c0e0031400303103141d8a580c580c41c152400360080e106090901caa18031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 476217886 1250 476216636 476216683
    0x3010e06010303081e01080c04020304022110050a0b090f150607080a020105071e0305220b0603060a020a082a0309030706060501030c12151208190c2102 67
    0x54000107600d00400511440741881c0045c000b030020410701c280035910581c0c0103898000590700c2c264005c2d40d0060b00007010b28026140e40100f0051aa00203001e100041c2c03c80060101500d42c18031920703521025102080c40710b0001c1500140075100010014038514100c0c0002c100c00b0319400d1401429000060a51a6034290340c0c140f1007816004030040c00c00544c2080001002c4520400040c9580d95080c1100d002400701e9807806d802030320006211411351800b0301c04405030a145d601d10100d5040c050f41e00442d40b41040c40c145400d2075801840c5048450040040f98901a4041c151507070004011071207070942034806030088511b00c182240703070120440c08000e008424134040000e03d00c10344a81d13010484180d60308019802c0d41c0000c08a0780204110748110074001301c0d150000c500c050311601c2e400007055155035408036440c41208056507520b1020a100c0c1d4a400c0100814151800070b050020307040086949600401c1800302c1c80941c0b00c0b10903144998950300030005800c41028108c204143da2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 476219136 1250 476217886 476217893
    0xe040b07020322140315041203090206040b0c010b0402181c140717011a010503090c0901180605150307050d0b0d0f021f0509060c0712030c0b01060f020c0f03010e060103 74
    0xc0b01503000350012401c000110824626000500a403814007912003203d15036208d0b115030000010030300700841450780320484403005030307900c1e4010700180c45038041164607210034036102800c40d00800d61940c000c6204111440000e5078058010480810448030801140c0711800344c082088204007000b4110390590111007a00d090101c0d4040c03e80b40701c03440c80c0d44050300d6152031500703903154001040d84605030180c03d0740b401e5128400460340302c91600c0c212004071842c07001280c042d6001341e00140044e2076442c0030202c00f98503401040000e0070300f10341d51602c044d2003010144961202902280c14408006000c19241032644c0211554520080c41400444201d0400c0100b9080d0110100c1c07151181c0910400301c41d00c90b03420009010706940d6400d0a03e031010050010b560b0014440f440745208080c1d0018854a0304805510218480d035a0071342424910318000003c0340741a0032003c24025051285c1803240d60018010407450300894004207089101c5012900510680b00001d0060060030004021b2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 476220386 1250 476219136 476219197
    0xb09060d051e0702010b0d03080402010203130303050301050f2205130b150405130f12110f0a02271b04080613051908030f09030c032b060e040b070203 66
    0x100300c0500c0c00340c0041e07543c01104034202c603407290000340d0040d40c404e507150210384100e0002d684103106004691070000c008101c40102104e65200700c000600000051045060000c10650744103420384201d40d901460354440481c06810f0420701c01c605960340002198a4015880000440d0b00105410260308010782510748040c8140b803024000c0741081c000c2000c105080d03039040b540b9a0001850b42d400d03c2c142d6224a5a980300c1d00d0352101b0081e845c213200b00c842e8414000440c940400c1801000000ca042c414042d400d400707035410345062130003120400241d2904012055010110303454150f6001c80348180d400483c041c0b504a0f400f18410002001001c14401c2c0c1c43c0200240640e080310400c5a520150b0200701946080090070468217002142c040e6404210407030300007403013006403420180c10201e80351942c0c00014040c00c102851804d1035080101241340082c1001308260140300c0c1c50f0501441c041214400b88c070060140e5202d400091402c1c3c401d03c141c0b56611414401c500d919155000350300c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 476221636 1250 476220386 476220421
    0xd032a02060a0e040506010e0d150b0a0609140d0b0a0908070f030507030e04020f0403030e120f0706080108010c090b09011e05091801050f090a061a0c010e160b09060d05 74
    0x145c1c50000410076a602503d13010510a200610f024442c0344ca95443e044a007a20100742e4803140d480303074652034050ba268618070313000c0c0ca481c0d40c540d84118030340042140410300708002180103d80405002c1e010031703002c0010591181d40002c2c08100c1401601e4a00b4842c407a5100280c12005004007807005c142d4400c00a0150074000e50700d044001d2070326410071040f441255400507012200b0842000002e0240301080340b1144000d0480f02181c80f8401c0040c200002502d4000823504000410701c5a01d8001c0750403070240c00014020012281c10b0324014241d2480c0b4000c42030628800b2402c110168825a030110341e1f000c1609a19004029118001e0500d800030040a8421100c00070900d55200204c00c000e0f04840c4028610b072198000c60301031010051015040c009016181d81004c68290f0009441d24070000c20000499511814410800d0840346aa008440300390080b0711044605121101c4900c1035170240412241c1d2000c0b044005841c61107504240000c940c100f00402c41c078142043d00959 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 476222886 1250 476221636 476221639
    0x3070501060b121b2209050f0106140406020613060f0f0203070207060806030c040902030a1403030a0b04201b06090d03060f0b040308090d0f0c0305010b0d032a02060a0e 74
    0x200d96201d440c3d8900c4a00081500c080f00441c051010340b0541042c810641a05c0c10b100002c40806034a444400040e035001710340c0c404070351070014010452a541f000c0c003a0151219020721a0a09017420b00080d140d0030041c10140d06200801d020905003d25640049804100c07400204220307600b2100b07140207500121181805801058000a116802900080e225010003005003103101001c20800c8014241c0b00d40580c1c06100c0d0000b20800188029050b40e00555008000d42c0c6031301d0b001c4904000d580540b0131440c001c904200d02540e540d1b10400c488901c58205185007611441410310800f01c085040e150700b00e45100301818848800c00c08289081c020145070340c1800415120180281064514401e051591202f00810800309030540c000d080703004401400150007031400d880c0c92034103580c86802601d000844a00400401000344038140b5008030540390b25113281e0054401404404503910081400c4803800d0844104206903800345203031a60081c1100c1d200c0048040081031041c0004d042c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 476224136 1250 476222886 476222917
    0x19021801021e07170111070503091f020d11010e010603081201090b0306010b07060209060703030f050901050105030c192c01060e2209021c03030605060a0504060c030203070501060b 79
    0x31114802d00c058594840d8440109441c1c0c1c50403c3c1e0740e00025000741080a2075503030320300e1004450842c00080c10064000d070000c64460410408011500108034540541000c0c1070b40020b80540c0c0209070082139034640e0814801a91a03a08000d0140c0795400b0424941d503c0c1c03039008010480c800c030241030340a81202d4070390456a02c5801e605c1c00c0741d11003280f80d5410b0b0320003401006226031100050184074803a16000d41424032400105100341c01c0740000301e020036111640700c65450350510409601119a10085c0515403400c00840c2c3c4403603011030b80c00e005100d0003800b005000411500400240b000c1e11240364010701c0c80c06103040f0010301001e00c08025007940000102e02d0b100c2d03420354295410041407000355955100c10329000b05040043d12030304944415640000d030303850b450034000102440e400340070078001070702e001011156a074000c80c1c403501c001e000b80255603900c04103803001d8032030a0905030008052810300781d00c0c6000b48940100150f080503804529015584080c2007009201c80d0355 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 476225386 1250 476224136 476224153
    0x331902010513020a030f030507050d0f020c030105060616110603090105090d080907062007031101030e0a0c090213270c0c051018061b17010f050103051902180102 71
    0x2c9110b214108406980b02001c01014000314400c030580400881c841e0900502d00f51040d0b5442e41814202d240300800b00300c041400300b11003a0188503400da4440220020050ba01d050780c0029000d000300309042e004da82c1070f14120001c00c00e000c08080210702d40288915101c0c43c003410858081c2404a509100b180519403802e949180600d1030503005141080240c080e00d420100c0894080203512842c03541c0350711100101c1429082071121f60080c5000d5207841d503040900300005015152590b441c00c0481d880103004178041075080002400303403880c15501581d0703442c2030f6580491a50310303030b04102c0781e460300c02140c9081030070800711031420302910ba00305010f0011180d0094910010310358020b4201e81142034240552419035200074103010f140c48098030f0f416515220b0b2011200e41aa180300002c0f42020807080300d54000c415181e42855840041e2060b43c1403442c1d40d5000c415078031800d4181a210008900d146943c2d0007108203003c0c0125003103442c2c4800480c1012001034070391029015002e4000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 476226636 1250 476225386 476225401
    0x506061c0507050d0602040302100207060f0f1b0503091305060a06050405060a0c0507170102121b0409050402041127030f030417030c01020a020f010b0406053319020105 74
    0x34480d00940c01501070402d0034a03120074001c01c60f540032000c0b180540d0800001c0010303a240c410340c01810b201c5900605c20b641c144035003e803200405a20010070301005a520030005540001e8000006100d03c00400c8918000d1821034903502131080c2159109051070341d00496261644e20840c0309210450302038400680c0c3d08002c1e03c00f44224000e02d40c002e50200400583c045c01340f000d00c40b4480c0b04800312149250384001e50101c0d50490010043c050b50005207201e82200894500e60b0402c40075007071070002d0b02d22402100070602c65803281c0100251964006400d65443d80c1c40004640e4045540a50b21851805003004121582804d5682110103240c0030482d41030009115900100c4400114606814502e88401c0b80c0c500199512452000b00442d008100f020300150a600401d074000300490050750800368252061111502d004603c0d007034040010303544801424055460000d68100040b002c0f0340130800d4000c0d098030343d01a808000a05d242070389500060b01005124540c001c00190b140c400b07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 476227886 1250 476226636 476226679
    0x80618010b09040b040209041a070507020f0a06050703140f0301030c06180e06040f0b18160816120f110a0201110712200a0b0f010603020715050606090301020304050606 74
    0x1c3e0b010b0300101e9003200040c01410041c03a1150000e000301c2a5403911000900d80c514080011039400c400528041040400c50506140082c0c00100407200c00d051070b400c00b00000d220f405000005800c000004101c0700c4034850728400c442c07c2d5051820303400e0380e030740c1c40e0300b002441d11100784030f1070000810345160325015145021485041d02c00750a004082034441c101000060250320f42d0004007640c0e00c00d440e088603a1003019001160700d0551020009181c40b0b504901c40d42e800c00400c90600c0040e1080012445070300b202814a1860780c2005003400d022110490300412211013460101890009000b600440040c050401086c25600a000b4400814046001402020720003061083d5140c42031081e10b00030300c1810203509501806c50348004a460a540c030f40300310060103680b01d8800034280091008800b0141e030241240d0f0030190b107010a40d68800c1c400f00710b10540004407640d5100860b10b26a21802110308050700180255180d05050504d16142d210554001d44141006114601c4440c0c1c2d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 476229136 1250 476227886 476227891
    0x140111041a1c0b0a0e15030c060f0316030633020c0d0206031f0f0e15030615010509040608010212010f0f03060c0e04020a020a050c031b010c0c080618010b09 69
    0x1903002c01c10b88004036040700140070b80e0000a907001030084404100000b860345001c2c8142507184003000e001490038245400c6c41d0844001074000d03c1d04108207201d440e5406d045a0b04100d0b81a801400d4200c9075800b10010003468101d2840d0705118a0542000c050900c2d600c2c4011000d090032002c4540200d905030b82d9025449180b640102e081c0000c40b01500d059000345a200080d50100040400b80100700320002541e44c02c1a15004024141800101c64503486141d00000594550501042901c002030343c1710740c020818403014840c92803d08040e44180251004554041d00511a40d500c800505010390030034070190a8004814000140c03406d00030b81010704032810701403d141e07040e05544400006c3c1c5444c10021050000c1180010410340700e9100606c00d207c0564058520315013980f0f800c6050080d5090755070302c0ba501020b402c0c00e03030552185c2810b441403000d00345004013040341d14004c0203005c1503a000b0040382c01020104500000c0d800300e071000380c1d0030b003c000704000c1039420108907051805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 476230386 1250 476229136 476229157
    0x209010e0a1406180414031303030f0518040f06080d0c021e1810030c0e010e182815051602011a090601030b030607030606030e0105040f060207140111041a 68
    0x9107032011003000100403911760401c0c0100429002c2d03000041c0d082d450360b03100c40030310018818441d00400504d507014210314100c030811b1030064600905031a40c400014503002032580300d56a20084070f0000d50762580180010403400003a2001109114006008280d05100590091100d0495541d07101c2d4a4010b485d1130303240040c144541c880301c0e005c048070003240003045001e65402496010001c258a4600c1e030008149000041501d58102101b410340100041d000a130034807044003c22048510216041c00982c0000002500404280501e0803503011001c0001d0040445100d185500b2107180e006588100000ba0490031b40000301c2000f02d08a6181c0510302c034030900c00c0c0003404c03100c2c81c003034800c0313034011078140740105080c402032000078200074040d1640d6000c00d82d01c250800280e9014010721240400c520003c20040c42c00c0d8450000301e0004010051550b40c0c0002c80d00708000010000c2030103540d414000f000800384055190ba5281d11034024030100c5c07900c80510080000380b860844003401d20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 476231636 1250 476230386 476230399
    0x70c03081e0418020318070902041403010b030a11030a06020c07050a151205060109330f1b03140703090305010b10020a02011422090c0306050325030209010e0a1406 72
    0x301c0f400002500082d00150075440c102c4014617020b00100810005812803480050780c5a140c1100392075182089084503000381d05100c6507001c1c03640c1c0800c60061140d0018044c40140300c0080c0003d040c00d07007174103000b01035910100d42c104080d0400151913040e1031081d1070b0402c0d02900c450302d01c503101c850042000c00080e1900b010707011009540e04440c0d0003520605081110343d887d0000102c6503480d003100b614080c00c084079010a0802d198104410f07a0300039040c0694080740a02d030041820344454041c030801d00000c24010201482481102100f0100100c0680c680803a4540100004c1d03480c4807d9550b5030919800c000c2d00d04d46080c9000e96011781e50010660103410341e0042d0741c01180e64400d8a502a0b00f03210041d11108503d4103a4880c8000d62012003855013000f41c1ca0003100c07e01d800200070586440303820300060300c0c00559100300c41d1001c3c03601d010441440b04c6c1c82405400b25040250080300004c00000c1098818103e1400340c4c841070310a20108090000d2001a1001202d05a80c0802c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 476232886 1250 476231636 476231669
    0x309140402090d1b09090303020a02070b0309120906160c03151a090403030b100e24040509090111131706060f0402070807020d030e2b0611070c03081e04 67
    0x606400c12160080081164600555907031708004003281c40d0460194086500041c0054040d60306018010103003018254150843c1800f441c150340d80e41c203140d1444002c0d000001c6402c000ea8a60054505101441c10303e490390380001d161140c0316002501c011640c014608020880703d07030482c0204410642040c40d110003207400c400821280c6840a84182c003815034400c0680761603100d6442c81c050340e45581e1925560f07880f0100500030601c01b00080840c002004a06460740781c4d61000450f03044642c00c86010350140c030b038604594010441c0e003103880c040c004001a18036208075405181021242154160b1080c02000e540594a41038101d0700030b68410401034090b8920310b402d6001c3d0034640e01401c0c170b1505010f15075002c42c90040c080c010540c04201507048102c3c880c0341c010405940c48114055140b1043c0d1060b092051600d903207540280703000d40300c100c290360403000d038400d42c2c0030b29800288404180350b584c1070840345544002e81d0041c2c082d500130406038000700101e080307504035081c20880c2000d16 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 476234136 1250 476232886 476232893
    0x50406140a0c0b06040f0f230c0d090813060207061407240b040e0328020a020609040f0f0f060b0a35010b0d0b090415270309140402090d 60
    0x60b200030a0298080e0703845c1b02c5140c00101600c540c09620000c0000010550312508140e003181d4059207410100b07038a800c6c100184504a00103a90121900d54404140704000f0f1400c1c519078011054210b8941466100016400390f000078010b0484815441d4880314401c0f0030340c6500c0306d22491030098955002e034080d0182002d911841085e10b00d140d41c400207804000000000c0596030510718906071980b003c070388580e0181c42031b624849a00710704880105501c256890180d10b40c820180701910400000c00e1071000e84e2644e0f04030000700c95a2020030060b2026400900d03000b00003420031700b5003403441e224005c58400028011214210384a440d002464808210019005015550046da01c1480b24080e113132268203200702c45001e005000c0c03546032551880403182e0100c54040c80341a00c240c988400740004520301c0550030741c2c14043c3c008041402d1146150400c034030f10300c44070040307440f2403d0300d143c0301403541c4a450319060710400041c41c2032070342192040009078028800c02179842440030f94440c000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 476235386 1250 476234136 476234153
    0x1e0f0606040902040602010902040b09130b06012d0f0203130e04021309050a140a020d03181e062309011206090207030c060b0a0b0f0c010e030307050406140a0c 70
    0xa8001040286003544442181e02641c00c03030f5200c200940c3d103590b81002146082d00440f510120291000001c0d840e10381845501b50b00921000f17030000c0a088040f0340543d21a0310200c0c51308600780b034411082800000e158442450441401c000501400215107000744040304480c543c14400b40d007a805203040c0014610b03103c0014004a03840402a219810051030034014100d031b5500030310103004414103070306200250007013240b403422840c3c00101d0b02000596444442000f03407a050b20780580c0c9036148080c14800078801c0e4004a10b01c410030114031040c1d000740d207151b03801e071042c43d50341002441030540100d82c08500301d000b00d16802c1d0240800b110f207520900b00207040c3c02d80c0d5034010031200e0307031040d00340e080764410030042d000609005944d1041c000c2038010000c038090706454104003645000724410103402041c036071142c040000100d10300150006d40007110f080501c242542c3e0350781072042d400b41035035002e4400d00c00810320b8030700720450300179800056910050850f180d22622240980c2c44144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 476236636 1250 476235386 476235391
    0x501030b06120f0603061302090c030c0702030604111005190509060708030123010503060a06050f070605240d050c010c0618061d03040f051507020d08121e0f 69
    0x40003002072000d40ca0071000c000b2003902440341403602486504000d4203150900c00300070b103868442480c001c202c1005031102d850303056000115401664aa403030301024040244204400039501d0700c42e1109110a00002c0d51a002d2401c4003203400040d5001840b00680d4207000d942e0b07403020304080500c1746d105824084c1c4010200000020440d40c0742140664070040344d80c0083e0800b000115420100071003013411110741d901015001d00b032403819880c01000041c0c4090302c1d8002c2e4800c206021510f0310020712840141d4080540c88041032025207010515841c01e1002001c40c000c8107601030032001d030305082001340660425045800340492940078801910b4010744550126502076031500d4204001120035106c031006841200d0200e001010103125031284003a02c0350b80d50598200300410098140501e03a00c0045030b1080d24003030345080c8862403014003401450406504020040086000c101e45c0d40b00a00b15001555000c0401e5100d0f060b0213500d00f2000d8503529510042c4001080111910640e601d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 476237886 1250 476236636 476236639
    0x90f010c050601171905031813020409140109050106020709020a2a02010f02031c1d160e2401050d0617070f05030a0203120a050f03100303080901050f010501030b 71
    0x181032400740d0391036140460903071080c14544c040c1300000c41000d2041c80100400d4034118502d1132610035540340d45849201d0105511b645086002d4542d2480c0c941800304041181004811034855644106842c0613000d1030910708401050705d03001088088461284038180ca407540d0040c0405400e125011700254440c00341d03101800f50006660310307a400341140c404500e812106d00031a641003a8400035007092040800d00065410900c0a80300c000440340c04503150b15a4603001003484d8070b82201044280e10f0031020792095014190b0604a0a00800c0c0c96104403848001c51085503561800aa65002c881240b224244030302d45003c060030b9032054000e8611044122400104203568001c0d07080803804034821003000d40c201e4501042010400010100101015406000501d141d640025107a45d0100041404104080386a03103140f445141651903160582c2071880e607a04103001d0704070036912944030440c00600c004001401c58101805041c1c0243c222030303074074030950b420440190b02034110101301a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 476239136 1250 476237886 476237897
    0x2120d09020405150310090b0c070212030c0c12160b210108010b100305010510050f0f07030203041a1204151116050d1b080a031d0609071a090f01 64
    0x10007690300c81c480c45016841031680e81100d0211402403604044034100b010818900e4205050003052240804691240058400c159160070078030005400c1080d140c01c2803020701c8003040c000050030300050030703030200b074030440384541d0300740070300c55015902c0c03880c1142140c460150740410086030500320064130041c190542c0c4207030f03030f0703841004c80d00c2000b40300764415040f5a4550414400d642003c080050001d9854a01070150b581044045003480380000310107420040b00050110710340ca401400c1d50f8517101b04034031584c1c2ea0f40641c100203650350850f0007008a08004400e6150300c058904080381c0c4a134881407410169566030340c0720442808000c60024032a503031640e40381030b018040d1000070f1480f000c1c9010784650222079410300c1c41c40d211481d50544144161503191343c4040340085d1581c3c4103680d0000c04580c0e00c41c060070085002d0003507004141040e4000c01c441203e90b000219141b441908500102c4680b15650220442542d0424030f04d04403115040180108900b81400181102e04041c10507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 476240386 1250 476239136 476239151
    0x6030903090e090a030810030206042c0f010305120301350d0908010c0203090303070f0203120301090c0e060a0c03050f0702090c030103060f020304020a0e06010e031b0a120302120d 79
    0x41c03002c40e40089508400b01c1e00002d107110304068005502c1c0e6007184510130f00f440030030300b03548c003081c080c2c402c138010342c5000030007102c103695002c0021600fa001c2c1041a02c102029040040342c140700544280421205c6004107492680141c00243c1902d040b10b00301c04c07165002e81a03030b00d41400324035617407a05413443c3c20303040d00024a4094100038002c9400f64542e58070030b0040c070f0050701c5800c40d8192200d000071034104212084c2250b03000000d4072026900326a1061100445200081c40c294510342d8080d118240072000203070248166204208404131600c17800c003000758080800c0240d2180340c04c9200410209603404001c68452005044280e00c142c1d009403420209800003a400c4000300d03110980424000018401c004240c09945071010169600754158141580003801d00782d2180a941c00c6082c065002034066880344a0201d448034010f4140c90350301034031030043c108600110740b203203010f8000311030000f0b0801c00090043d200c0d541c00d58080c080d141c690740c130f14000c141c0c044001aa10182c95120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 476241636 1250 476240386 476240399
    0x3010e030c0f1207050d0810030b0403050901020d02010c050a0c030905030102041e080a030e0d110405150a080f122a060618090c040f0e03211f0603090309 68
    0x901404403100001d02c15907400010151808900000b554028002800024002640010390701e01c442c0403400c001410340e4070340645902c001459840944040d030a001030205054200004026003803083e401d54860705115030040e401e0750b4004810000003a0100035200e2000e10882003003400e14800d140405001d0765480020342660001d4000340522182a0080400c0000090164004212440261900700c2c0e0648000e1706504d10a01c0b01e1380078083d864842420003020081000b02c88400a004000300c1c241007102c3c11020310030128a602500401c04082082040003400940c1105403000600c0300c0340e144440e5000c1b58018030b25080e4a04102d0030a0502c00084003500c8101c00320301c500400d0b040c640f010800200000d00b0000560582c09030082c02184407021600c10440c172001e031404218910800b0040307001b8101c03416240d0603408081075454400d104844084012101c14207000600c0e1207001291607113103041d1003002d08049d2000d8080204030b02a4221100180c002e0508010f02ca9550740c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 476242886 1250 476241636 476241643
    0x717070e0f010e070219170c030a0309020f03030423010e030d0807020114091b030c1e2812050c041b18050f010e0604030f0b040b070810031103010e 65
    0x1c0d0031a03041c8125030014448880e441c0c03400e50b40b04100388000d10004c0d980121041005441c0c14020300441c510100d106010610340048980c140c4020040381d90f1000013550040c0100641c90040b4840c26511820b48901c0c6000020f880903141e428600350030511203029921302d0900c48010240c1481604254854981c1e01032051803c404c9141e02d88250902c0c04a0f002821580c201050b1084000760b0024060740b4a000604603480d154220328a566a83c408400249000c5504495945c01042c00c0440307a00000f480380003007400c2c1702c10380d111151b001d1045c42c50075204e8540100222452180c0504200c40c01c100c040309090680203a081d0b619540d8210089026140c10349010200074070300e02c0d40070385403039400b07a840c140243c0b0a501c0d03041c1144c140000140c080590261007070410400403201d003110b95855048600455015400c9500100d15141c00200b80754200d4003a02e03510074510010784007a02071f50003a8031540c210001e55000a08595407110800c901215a5406660310708070719030301c00c0c000c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 476244136 1250 476242886 476242891
    0x506040e10050103060f03030309060f06170c030102030c1e090d080301150c0209010b0d061203030b090f01121205070c091b110d0806030a0b07030204050901080607020717070e 77
    0x91248180c41d2a00051034040c003142548128109441d0581c100609900000f01c081070700d0f41441e010810404500b0f0000281540511440090345090030028200c410f08650001031149482036030040c400d00c1c0700705801c0340003c40b5003c440301001c0000328058404030712010380524001c83c1c5582011701c404042100045000d400701d4a0010000043c07007100c4000c26090151102454044004200c1d80d0100380e14504c18450441584404160a052800982c100f100504601440b5011a0115090081c090411321102500404890000c5420031000460960507a40900103050006800f82e903401e0b012100e454100041080c00d201c1c6000150301130649000402d140c503000310b0700740b42004c40564898041c44c04202882101440790021500c00304038000c00e8012410200250b40d00e00010900b02071110780002e0542c1903600801000310b40650192042d10030550b401c007010380c0c0310700302c1d02d540350002c0e40c040c0003507404103600b08542203100c04c681c0492818042950720450b40d58090380c1484506 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 476245386 1250 476244136 476244149
    0x3020a0c0609081309180308060109030b04060203011d150609060d090b1008032104020f0a180510081902010e060c06160201090c17070e010605090a06030c0509120106050604 76
    0x4603071890813001d01004000d450890400c01c180c5610300091880c20034410802000c0c85614400034081d81e000d210418000d41e00081c0f80340880c41e051800d44020b60090150405e0b0303884180c0144680500c184400d4420341812070070000c2d0b0080b810400c00c0ba608042c41c0943c1c041002c01a014260160b406148695031107811a071002d410552103c00c41ea070141d82206121b544203010f10404c1c50192101c0c40301681c03096103150395544890000c0344030515040780254000b5842e1600080610b112140440c0100701e09408201e60f444081c100b0360781c4280d902c1640d01650184c1c0c4a206d1540000d1103941d411481410816a400840404120303181c0000e144031406400c2203040141c600045890f0650301035240c070003001070349015030302c84c410051a4000c1e05140301d20060202880281007120034050014100c040c081980e58413002030250344102d94150042000080c0055044e02a004044100015844460908541e40c003030203011032290b405060b281d92540030009030b81d00c44c0310080c00074102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 476246636 1250 476245386 476245403
    0x17150d0f11010302090a0902070203070e041b08070e010e090c0301060906030c21141f05060321090607020613080703030815060d05040203100c0906020706021c03020a0c0609 76
    0x18241800c00d070041c920300c1254140741c0104400809a550b103640c00066803c0d00300c0060f01c450380c0d400800d01e0803d40d0341001c41f07008a15402e1200344002d0115040c58a034041e9184c204068940c410161590101d1240004071189900140300b160802003e007940410084201d0307d003004d00100007425aa0790f0303442944119569a403c1c000d000814203080b019000e43c00a003c19181e09524160580c10302c0354028001250086400714180000c4c003007201390102869001140154038980d02e0020501912a54420b10503110b40c1e1291b01c03410907000203682038041c0c4042c10099108284101c82d840300304201c4c3d01200400840c2c0302c403251500c80c0d5002d0b00554005000c014114500a00440c80150910b60744480100d0002040d9550104464080c80b01c40d001142c00d48403403020031f152110b8000110300d0682043d0841001943c09400101150017580c02c0301d103003a0340c600e4181d07140d0b28915940c6011828658044035140d00030b400400005001c0d2405010920407601d03090226100340384100c88044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 476247886 1250 476246636 476246663
    0x90b010f15020c060901030506150c010f060504140a18050708160503070e1f09020d050601020c240304030903140a030311031e150d0303090c06080717150d 68
    0x1c6100d9240c0d41481500080c02c80041c16000104e641c01000c800718109034454002580e65140c03190321a1403842106110798458506200041c0a0801941011105c0e403a00c100052180ba140c06054118100004600560f840b4612280050300da29203e240c0f040000d0000280000c10070403030040100921005040d20180c031081c011032641081e41311600c40c2c0d104134014480d8401840384190840c1c41ca01c1150805400c07602c40605105080c0d00980c00ca52012500641450311500b001d486120243e007650035281528003084150400702d5491504d400655044510f6400c0d10780c015034000340242401d0140c103641c1e60350b50710003050000c10b0824940040380403c2c10103406000e25420148100351450451401044200c9208004440e80300c1a445540c0882c00c1c00d03103440c6040c402000c0207804900594214200500501103000b800c440142d0402c40c009005403142001038002c074103950714070b60100c03010342100000c000041c0c800544640890005602c0d80d03100c91b80c04800350710880ca00031105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 476249136 1250 476247886 476247899
    0x105010e01080708030414010212070501020723070902070204330f0b09040906090507081f021e0c070806150102100c0806100c0c14130c020d080a090b010f 68
    0x3040180e000342d2150340400e005000d004c0d40403050f24107581c03d9983c050100500d250041f407404090240c000c903480b1001403100305101e81900104bc1440c0241120000404403104c08030184404a00c140a203400801c024001d040c3ca45c1c0007406158002400495000181035540c40000e482d103200000790400b0045400d00440b189111030b008186100b50b90300320b10702c1d08406110034072440801d20710503a6908101400c20013198488a46980c02604941c5a2610740d51016924a09024001780c220584170503004038000074001c503030984060010020344080c0c07003501014950401a1032013900d005080b0b001c1101442000030394400c10586030b101c517035542c45070006424001c0340699002d44501b003025a244040e040305085411075000d43e1140030f0691884421602d04011160080072036030014400249042203100503100100125401c544a08501d1040e00840b13840101c4980541c1001209800c042d0103074085517400040f120004c55005105d07030761282e03001c400b40c00011120841502c1070144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 476250386 1250 476249136 476249159
    0x204240206070203030402030307020f03160611010b0307080a060902240901080618010b032e030203011b0c080f070f15050a180210091a07020405060d081209190302010501 75
    0x2d0003500142d03140d4101900440c2d141d1040100180c00b440ca010003011507a00e0412446052180c0401f900c0c001907200e40008010504841c80c03000c2641c28201030510074034001c02c6810864003c0c178010418801c49544520140100307040a0341d2110110007101c0346640b8440000c101015625606a9980d80c0c2c24005000c082c40602100c0c010100c42e00c1694400701e9040741c29040d108100607690301ea0352aa410320450324840030021043d41d06491481c1c6d41031403007101c1501580d108034028044800850041e8502c00d034460300c6040054007600e484004104050000e042045480c0c1426203006090346030241c6130b04201c84c040b54950511621480a9000d500c64141c0040c695031083c04554240d60610903104920400a031058401c20f100c3e042c05400340d41d80600030f00020b90180a000a0701090f407046401c03000c01613006034100b03800182e15242180e01021441c3c0d1000260b41032245a014040103040c00a200014034854032141a0120303903aa880300070740c0c0d1300c0707907002081a46c1020300c0e4000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 476251636 1250 476250386 476250391
    0x71a0a0609020f030f040602090303040602060f13050319170123030105011a2127070608011401030f15031b05150a140d09030305280e010204240206 65
    0xa45441800408590300c3d01c40112034102104010b0903403540c8860030100d0080c0306980032035900d440002400216190007203000da01c5400d451100c1c1d18650744907152000601030b4a580140a0b402c2040100f04000c0c080c0e42040038045280340101100070490385118040380280c000c80c40da10454a582405524000e601d001c14040990081c4029403509013031400c8801584980c2014081c089450304071405407004405120403082d80c107032641d040c1420400c0c1d680f151105030601c800c0b80c03d0203608280d00d000803c0011a104d603940c00c00540e1030325508032042d00366040a5410140c5401d031181074158030b4010f2001c40421a482e1581051031450000c107a40041c80101ca85082d04840030413256803015040410300720f0b0b860101d40d913035180c0c840490310315100403041524240d001c500440c000d1400e07440b13000c4441c03107510100f0181d150707038404001d01c00079461065440705c0c0d000d2007080c3c40c5038a40c1021050111440004d030813391250340c900903d188441616891201840f0b04030b4105034100801078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 476252886 1250 476251636 476251649
    0x908060f012301050901121506080718080a02010e13140105010e0a031208090f060c07021c0b0402010f0e060c010b0a06080c04030209190509100b0f03150a02071a0a06 73
    0x1500040b01800a801805200a030a0500c5265640c0c288120b00710707000001c072928440c80e6000c25680346c480c042c121000913513844000032883c60240e0381b0b4010b495220800c0e1100c80c00284082c0419500445010b0458030b100f0341c100c03041c40c451310b84a0109011380000a8a825031403800340d81044001085400f01000140c422101c44004002003819001003020031115498000707031030364174100f8840c03505503e100644c51030700c903a40c1000029886c490140000301e200301c07220201d00d10f2240d0440e56403044400b000d0000484c40300401c00540c02490816091490380c107011031612480000030f510343c0c01c040c400c00d0032a5103400c034041c200e2505aa001004d4007107401c1142d0241003403008115039000f1404020700a050040203d400010301c201880b100036000381040c0320314900b0041543e100d03481c0b100c0750020030f0f040140001541c5000b480e901c0000f500503009040482c1804010420352601500b069161a030070000c88002c83c40742103c41341454890a55020941480644e1404070f403811741c00700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 476254136 1250 476252886 476252939
    0x4030908160f090e01060302030f0d170412030b01110111030a0e010203010b0d02090103020409060b0c010501150c030305040614040c06110606150a0e0604080d0801080f030702100908060f01 83
    0x1441040030700108030080d43c800c2a00081c0d445078540100b0300400d620f070806036040c0719007032110b0381c1d018000900d102640416902c204404c80319202e1301b030f010582a10024807010000a4411a4500c04e5110801c0d4101c14500103181c00d114007030030790031a1941c0d8084841442c00008002400006014002c0ba058114008519540c5414000041030080c410109480c1c0e40014141e040d0781c0c46501070310094a25008100602543c40509044581c09402004525400c14000040e80159220190003090064491a4071404641d400300d00608004004440d95551410994585540001030601c180e216440d1203603228184000508050400702480c1515031281d000c1015a0b2619860300b84045107452900d07448824043e01600c030300140018507600100046000101c008d40010400a690410380703603c0c41503600c0340d079280d88031008500c0145265000300804001030502140000040c0210b250440000d915040f85034203001c0c09650714034140f6145001030048801400c3c404400c0c14903810310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 476255386 1250 476254136 476254139
    0x15110304080715050c06010f080c03070602030a03090524041a04050a0308270102223008030a09060b0303070507060f030609020d0e01064a0403090816 66
    0x219076032403602d4092540b00000285000c5000c0b4068415644c01210b0a4180c0e04150384458120340e03003240d03601c500b150300c0c42401c80e804601d04020038000d05644150703010750700d00004a5810380c068440034130201c445100f501d02e03866146448909141282d90032100a45a60526080c40c10760742807200303100302c901e0390400284400074038005064082240d01d0f0400040954402940207140b030354a40044030620201002c0d140480c0e010343c003d007054200c11200541411010100c07582c2d104850140400f50168400081c1004000034450040340384a000207034045211035456004075002034a0420500352190f00c18001c0107080d00920280c02e00541c01503007042025210310340c0e68403051180c1400d00c04800410103d492103038004402a0110000a6651b13000e00c4518100919030700095441075403801c400400c1d141e0803c5c58000054050110b1810880c0082c03640900041482007122101c0001d1070b8001c02101c54945001e109500a0b00c54801c0c0c2450180c0032418621201901d40e880c2079070704c60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 476256636 1250 476255386 476255399
    0x70507060608211c110c0609070801050a021201050607082703011b080601030e1905150105090603100e03040504050a021207141e0d11040f06050a0819140115110304 72
    0x2240ca05134422140125410615040030301035403007560079000f403d000755002c2003000040007440504a80e00000204015178407010054101c0c042d0415880c40700b0301040040226281c0040034015050250030381d107141100000d000c2e6118540e28803081043c118542030350080307150070721401e01304411030000004001c46644004000180040c50306061665a54508800c4d120800080c01c54492044501c0703e00030450501c10368031104d0b1480c1c403021040c0d0000104413401d081c0318450180001600501c0380c410314ac2d1448000e40245c2881c00342e0ba22080c80b0005169880c0d0040c640240c644c01300040c0d861404603003480740103000400d0034041c0300c29000b41d04080781003c0200c07125083c0c92500f0f4a00070102485510013881940d40381c004860820402194800e250380050045411500f252142c80355260800d50342070084000c9000030030641c900080744540b6081e440c000c0d002c1540303400600f8106000480d05001820380119a080c4080c00307203004d0b4160001446801410f5400080d130502d881d080d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 476257886 1250 476256636 476256667
    0xb0a1d0a11041b18090c18140105040e04110a090b030c09060a151e0906020d09030309092d05012d030609021801060c15020310060807050706060821 65
    0x100c01000300810224018043c0491307070500000f8155000090203c1e02c0c51ba00f005040041100014241a14134503000a0100c01840340d0269214103844080c10145818501078621700c0043c07040e00e1a40d91504805550740c1c0d82d00c1c000001d40760281001131740c582c40d0b005161408822242e268001e4412074144500799580c0056402214144070b501404000180c00440c0c101d003083c0700090070205841c1a468070340d6000600d174010303684036500311070302c0107a6010100c403104c4551101501003001c0400900c400050380e006030030103450740c801c02c40b200c050030f07080ca5601840600007520400d9540d030060014414408000f0704d001e1013003c81000702c8604521000c02254184002010940c2c0c440b045404c641b81c101c03c40a0312080f409415540c0c0d07a40e40c0c40130305a21400a82102ca074400d40c041c00c481100c1074401d072401090f540d4100010742d410008180c50071000a00741c40e051100c14040c5000044903802a07502500c0e840003c2c100c0180714801111221002900d03055400c0c0b018006610305440d005e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 476258992 1106 476257886 476257931
    0x70e01030f0b06090112110d0f03020105090d0201020c03250f050c01020c12061308040f3017090103060e0903180109050307030b0a1d0a1104 62
    0x3c0040152014090051002e941c003880598030203d0350003a542840240050001a10034542d80ca601d2400300d000442140144e46501c01c11a03254801e000c5000780d0001c40c0000d504180350348a00036140d028000400210078400c0660000c0c801d004a0703201007807600b002170406904e80a060058072000140c4a95015109228882c0124100464415102180c0d1070282c03120340c41e240f1840c240f003603c1300301c19104000d06000209510240c00840d000400c0100d0300d51074442d420750404081100c15082003030406030f8440d000c5010030911b0781e80c142030009e503054042e541c007110070040e40104100c0e0400403049040c0c1007000143e86001000302200004450360744408020b0b0401124221094011250182c0025a0420004e004000c0194102a0100340420042070013072016100c0728a01076039500642c0110400300c02c3c40302407000c81725204015101805000d02c16124001c5a041c203 = true := by decide +kernel

theorem cover : BRFrame.Cov 476079136 476258992 := by
  have h0 := BRFrame.cov_init 476079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 476079136 ≤ n) (h2 : n < 476258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
