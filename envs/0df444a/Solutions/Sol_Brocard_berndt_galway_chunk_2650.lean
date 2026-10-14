-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2650
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:11.859676+00:00
-- url     : https://prove2.me/submissions/85420641-fafb-43c8-90f7-8aa21e620f19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 476438848 ≤ n < 476618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 476440098 1250 476438848 476438863
    0x2003040302131b03090c090f0e0d020d022e020d020c0706020d1409030304050f031501180e010209100f030b030712020a0b03013f12080606070f080309 66
    0x380810544410000b0580042c2521044444800601e8080115468030a2140c942c1c59139000048044840c50451000301074503d415406030290356601d070f0784010341c000300402d03a02c2035041c5e000790000c0054150301905040301c01c011459a05403812488112045213651348240300e03d00c030001a1101e44003c02c80307000f0301600040e15114800d000707020580c50780003c0c410800c074a8076543c04889800d102221360150240c1c88aa80e0507501c188000e104911303009441002c500000740840d4050344100181c05580f4070203a000341c0c00d02c400391100c07001020749809104c2c1c40da40240020b600c0d060340b5101054800360683c00150406c040f605440399076600c00e40001c4010403005003100d0300b80d038450318042c083c0b90415100f2031044150410005181d0495019641203030342c204104e2444008000b19802c41202c0e1645000405200c0f542d820000c1404540303e8050a0181440110b000300c01c034030145c9070140160200c3d1003004180088000100f040115191181d0f100090a45a032a54a405481c1880c0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 476441348 1250 476440098 476440103
    0x130f060e07050418020a030b041e0605090d0503012102040f06060e0a050411040b0315040c0c0506090105010506090607081308030d0f050403080c1e1603031b20030403 73
    0x8105034044100d0000038038a003541c1003103c1c04c2040035520400307040b5200d025807000350080613007501000416004031005034024042d080c000d4443c1003801495074003402ca1602140d030151b8410501c1035100080000404200b03050808a145504005190401181d1a15064504901c5010000440d25540c0049040b1546040c0501c10103031074080c06404048000049070040580034030024403441c060054071401c02101d05218545410100101c0c485d6200805120070100000032080e2180c40d64422456060855a80c03641541000c0c07514504000e070140000000d80c0c1400c00500040d034035003044408241c4201c0c4c01d44d595003014a0200001d020f020480312001c0d4842c600000c50040c048010180c0744100c41c001c00c0090f00a00039001181c009030340280009a2840018501c03685132001002034400d2103010b08000f840e2a4050962644101410024103200030300c80300c2007680501545031040c4061103820000d0030b501000401d4507082e43e12000f109041c041c0c00302d40c0528184100d070301854 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 476442598 1250 476441348 476441351
    0x3020c4e0106050f041103071808030d091406091e0705100e1302040e01061d220e0f06070e150a0309030f08070903081e0d05010302031212130f06 64
    0x8002411034024502c91064901804a02082d607040c3d103001e100f0300b20a540d82d04920b50660300d4108017122507240c0c4e01c80c2030022100d40500400d040c0c100b007024000044c04407c001c030700c1c0456464040a080c4e42090710880a900041c28420321140c00308006520b01d0390204802241010031150526080c20b80d4800f81c0c000340c45004065210754483d03c41c48112b0030580750301500c17000319403084049100e6485164000680107005200c0107105030145840820080815008029404009840c850ba02c4c10140361210300e00900583e02800b0b40507044440e04400054000c0080c46c424440d19548010500800c03c0719a030900b24441d5580b900e03a03d1940007805a03d502c2e0b031107411000c0c004102e00042600170440d11050b050446100c1c00e1141c0c1729010030383d501030a891a503030ba450003980040146882c411403a4a005510408000141848020061002c0782039455401454100030104600340c42c102010088440c001100201c00d641009400805508403c04c1c2e05103050203200101000b020075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 476443848 1250 476442598 476442739
    0xa0b0f090a080303250e091305060a0902011101020c030409020f0c0d02031216050a120b10090504050c070f17040b070305070b220b180f0a03020c 64
    0x40c50008050362195810a0b140403c04031030200e400d0b520707210356100a001a20301010b40d01d00c1e04210151f00d4005200c841e0851119009545407410890100d580d450000c0c0d40e20303400b400f55a070003da002605a04d010003145455058092281c5922030340c0a400d100700d40000701264058481c004aa0041203d0402e445444004580c001e44076030021222010070030301d140206062080040801540c2020303511543c1c43c00e0306058068075030030300c3c1c00e407948010b958131003600c0401c0e142c002000c01c210306076988501c00107041104020440b040a003001001c020305100a40001d41915292103200390080800340300900700f001c240d0042d200704d800000b031103a004140c200c20590080d01500102e403042851991a64403030041c0040070001e26010300300c00d141e850070400450002d400140e00207415480c142c5031004005442850038480c0d100300a0710341c1c811402002459418403892a510008960811030100c201400c02d800c85458210b180400400481512000801d6140c00e403480c038095000c010b04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 476445098 1250 476443848 476443859
    0xb0f0c12070813050a06120b010e0901060f020601080f120c070f030602300606071e080406020f0d0504090c050909010806090d02010506060a0f1206091b020a020a0b0f090a 75
    0xe410038050030a43d2005204007090b94540f104090040e10a595a064040502107615a006d441d900e80e00c281800801008007031a0f450b0260500d010300501d4a42250182220304002e00c2d182c016804201d0359040325860401c10a00412404250110681d0300c50303c5030b0001000038146a5150b10241e4440d038410400400c01510b0740181c0b00690068000189040b004040c1d04a280c03104075850390302d5840580010450701e06080036020150103040c2c1a807103c030f200c182507642c2070742102c8242c4201601103001c00500d40e0400c425030109007880090240d1018000d0045c1482c010340c040c18026030b0b2a80788011026114070191070300c0d90001425034820f540d44203140c54035584191910341d280e005220406a03114014003460340141c03005440c0503e010102c0800b01c424644ca00e9180c010852025920718034401980500380281405010010ba0080085031200984e515119040299000980f040d8007507902e5070a07003030440d049a040603956118054a04025210b85140e065000c0c1400002049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 476446348 1250 476445098 476445113
    0xd0603020406140a06050c030c030c0c030f07030c05040207060e010c0c0311030a05040e09030c0604060f14010b03070e040f1103160c05060106030e160806090c0a0b0f0c1207 76
    0x4a80c0207450800c4200d0f00c03100f000030080c08103a8029000031000404100c018400c0c2d0003024981521402c2d00c0c00c01e415811064115809047d000d115680208040b5030686402e106c1001c0814010b80109031480c80c540d22200312034558400c5a04ca590301007400014070085810507c0ca20750144020880c00d103a10740041c03d90700c1c52840070b50005220640c1852070781030000031503603075000c076880f4941040d03e0601e0107880f0041c02010403905000900c0030001c662420807102c0e0083d4816640481d10b03903c0c0b144194119004c03c0001111510000c004000300365021040f80c0d0006c60ba450f00482d616052404140501069048458a01e1622900086200c6100040c501074161400517080800c680341d403c0358001c10180f0094402d0b000305004208040c02980610401854903040d80c0181c0701049c6d14010000b081ea0020082e40c1004e410042c142c0d200340300070881d01000700d400345a0700d8244403803503c0700d00480650703c2400c600000d43c4000100c040041d480342c1d41089000d299030341c40f986006403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 476447598 1250 476446348 476446361
    0x501021605031c0c1202130302044104030804020f06030a060e0903181c0b0c04030204050a1b0c0f02030319020613082b06030b01080d0201020c0a0f0201140d 69
    0x503c01444201d000000110ba010390b20b5582d400d603032824522401080440d00075442289440740d22801120004010f031242d01411900c0340d450050b80e941001c03080f007444840001e00f000842958100504820103400e805802074100f905440e1415144c0c0c0c40f071000c42c0e454981c9041c9182d0100d0003004209803031107540c210005542c2c82d40042d1404e61602c05005a4074041e10880e034501050b5007084030781d03604100710300e00e004c02622005901c4d0201c40d5222030440c10301c01e580b40084048001014020350074980242a0080381911041000b51401a128001e04d003100d00d040c4204a2082690401d000300c00c0d0269a49940080a0320340e2101c81c60180f028402241d010140580a10800030703200081023420680c0032604020214541041c00302034072a8040005440241428004000e101229062040a000d0f5128000c40b0f0502e5040210451422043c6412034007168010001500310b0b5402040040b20f5603030096104010341180c1c8010f0324041c0b11038040fa1040c1001051100e5a840c10382c0049 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 476448848 1250 476447598 476447617
    0x60303070c0308270612070504150e090c1602060a020114101a03090d2109111327020609030a0506060a0603091e050106081902130212040f050102160503 67
    0x40341140f108009804e485003000e0003459003e4003c0c0f00c50840da90004500c50ba01032401c3c40e1141c9400c2d287c0c07443c00418540c071440440002c45110a00c0d080303082107050b0b0340d000b41e46044070604154103d0303001c03092204408070090040b1004030768540e07814000d410265400d00002415009481c01c00c1928503d48482e10400d40081d524111401150750b1400482c1e01440e0078030f010b001021203038841541c0c412550841017125203d6901e0840c070700c01c400d00c1180026480f41427900c1441880d01c0030451510302c00810032844078940003883e9011450180d0308507100307080b400408060122400000c0319402401d03c06609402400c0703010303040050204000e071285000311845d850032a10f50508034201c03049010002c0401c0210189020134070215200c10621600c180000704825880309440ca04140f45004c964000141440034441185409810f10240c18000c050441c00d082c0c86411040ea00350000d00054248050b601c14001800029012901c4c029101c0d0001d003e150b0f40c0c2d1402940d0703075200d075400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 476450098 1250 476448848 476448877
    0xe0301110412050c0a030201050d020a021618050916121e050304080709050601080609060a05030f030406020c040903020c0d081e03010305010f0e1e1c0503071e0207030b060303070c0308 81
    0x500a00e00d040030404046da80c06070740e1141004c080d048140300075440300402d04203500c507040c40c00f070914105501c61000340150349150340c02c0ba81ca41c000c3c4415144090020201d40c1c0080302e81701c1c00c10394101c00c0401102c1e211541822410b0580c280b100c1c01410388a1f0002030b9072415841c480c1480000030080c0708689001084458450392149510201c81d0309035401e50005d182000407610919217040020340021004044010320b036a5500007038901004032441c1d6150340c1011404000303041d010f000c10f1228420030b44040c003107480c09a80080d118584140e060384198002c00c06141070080c4802500c1600d981c1030301c8904d2811442d4070003505074109200440e8990300308190b111180f1020b025414a400c80300b801401c0c18a0b0005602034984090010f003005071007200b020321048900c0c5036000c1d80458403919100e61328200580010b001c1c60200b00514521494280c0310741000b40d00180d010122900001c00111a40395180081c0c11072140340c0002e40382c801c03000c1e004014400140c0041489070241d006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 476451348 1250 476450098 476450113
    0x1d100e010f0201270206090405040b0a0605060c03040620031201030605010501030b132d0c0207121a06061215040501050307080a08070303020909101805160e030111041205 75
    0x880c2030721220304a441000000c08513040000d10a406401031042c4014030702428425080c01090403148116001d465106030b000070700041c045644a00707006010151580c40c50b2080c402e2441e90340e48502c0c800d42041054468904188400c400c13948140e0011010030340307594800340c403000c90104e8802e02051742e20620341000055030758000c3c8103480c8242d10141c5980c43c0012014030f1800104200150015103c1200150301450600c042030b2503a042030803000098202d40d4410300a151070500d0300041c050b140389401c450301092443c0d0f00000060781c00342d007400d0030783d485601080c1240240300070429901a60818050035034079400005c01c4a01003a03e0400a680c2d94030304140c0d6541061098010580100070040007082c020002000041c0c0a4140545840c0710f40e400328043c03e07022950000260808541400494518192440d192030000c000f8003107405d0032210340f0f0900105d8522082030005c41180b0402c1903c00b900180c0d01c00e005400d505449555440070502a143c83d6541114103002c0d040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 476452598 1250 476451348 476451377
    0x1103270a1503050a0b240d11040311040e150c09130e060703020a0f05030a0207051e010e0c100c05010603060e100e010204030f0807060b0901150e01110c011d100e01 72
    0x114000c82500300804081c58aa1a1b008041c91407180d510302c10b900c0c41e4104440c0d40241c0d158000c0c0c40d00d040044410550720307451410300002c503682d5036901c43e00c2036040c44403078513003010300045035205c1c41240a1b925589031030314802140a8450141010382082d045015015200d00552000201480031403d071192035442c070300114100c4c4a0100c078040420a20512040384510442c05180d00100c64034005140903003d4032440e250410315140c0da4680c10700110340842e04d81c420702a6031210703840c4400503c0803054180010700c0c00034a0b001e11008005610404006010003504504000d581204040141980c9024866181d145c0c0c0081031000c039090010035000038005100b140d040703e4000b0380354032058400380d40d4000240c0c40117409a07080c0d500d80f0000419a950301034030744d00801c44580500d0700d2950b14000a003da81002d041181400000c107140382d815000030171034030b41104013441e01c804101840524520384e054000d00103500300c031940c14000c01050b0030050549041000b40ca1f0700340c6984a00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 476453848 1250 476452598 476452601
    0xb090a08030a0b0105211915050f0102190c080d051801140d0507020a150203040c05090a0e01060b09040e031608090d0b07090e071103270a1503050a 65
    0x9180040045900700005260505140e00192018405141952800c81480d5001b103021404280380c0111445640c1030120054040c40c1081001d40300310000d000851200300b00404d01e01d590701c41e8070b018261604005005030320030301403020001c1180700a4015210181800c40c801d41150040400920443c400d60780c0a600881c20740c0c0030020740441050b00d800519004561260076014480b500400601140380118000d01a445c800c00f01a40240310303100070340c201802600884200441c440b44100144804144404403401c1503e01c19624000280c0b20a0040001001901521601035190901c0071800104000050050b0402254244401c141060700300e0b80300c0c45000080d403140044c80c441080010a5040689010000149101c1140c00c0c0c80e115501340b07000c01c8480c80c1c00500c3c0d2001c01d02c0380348118000c09802c00210300d0140c54490b0301c0c0301d000e41c1c1d07417150700c460040c68840151400c5040c0840a11110302490191031360506580c1d50001c1c2002e14041030070800843d0404e000a911115113 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 476455098 1250 476453848 476453863
    0x70e071b0f0c2310090506070b0f010504060308030610050d020d0b0f03060121081c0f0608070b1206030a081b060105040504111003110415030e070506430b09 69
    0x24202403e145500c00204400f080b1414000070611800c0e42d0000f0315a5525400340000c10300800060310207181221509859480503040a07109500d020310510108100d101500d0b0302010940b43c10381c41c1407407501c1c147d40b240104000c6211080c000500340c2000c0d241508100120441502c3c07107902d0300c0f0624105030702d522090040d010f42c01440b17081c10081129506560f140a401000d52a00c0c10321860034950b1b9804225448600054031558410f82d4604548603e00044c00b00801070401e0504201000807140303e8118614016406a00442d04980d0103009441203039034405d00595503904020540841000b00c071090301d003c1d01581000003201e09050060600c2030703a019050040201c0014100400d818260441708109a682c1041e04074400c04000144060003244003d441001580301d03008041c0c8600818541e4a60030070101000315031101d8042d03c000c50481d40c0544c5580c16510350b03c01000c00c0d1700d050701200749198003403100f241ca04101a14040d40c0103101d10500d6940d40e940303096540d4007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 476456348 1250 476455098 476455139
    0x80c03091203040816030917070b030601050c030c03070f2906091306050108030316140d090f0804091d010b090403180e0a022802070e071b0f0c 63
    0x4408030154500e0700c5100110307071181c0320703500a50405001e82c1c24100044101da0b012070118031400c400303016010340550f00c40208400341009002d540e04040e00034105000103070010341844404110086141e00900581e05191313241c808484d181e170068100845c880c68000710542d02150300320703131651662051101d146c040902445800e01e03983c4516042c0040c0c3c00300184170107804c11304100d48100084140c01200d0003401035200031920b0341004218980070302d1041e07844009100c5020b40000001c001c1c03c0940c0d24503a40300c500007681c01070608007441c19020311080203000d074100140100f002c1e20b0350340c440c1d980000790004450340c42060556150894414030307a50b5500130450390005001910440000307403000c616010001641e0b60b60b02d0190901d440503528242c0064000c00e00041603c1d441400c0140c101e00c900d00d5101d14503034020041c2d00c8100c640506040703040d800c40020b036158025040104010842c4800b10b440e8074660400c549601d00380761003110702e046c000e1000521107080483c400d28020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 476457598 1250 476456348 476456353
    0x7120525050c1c030603050607020c040f020a020c0913170703020c040b2107050a170f07030f080a1b03030b01030b0919090c090c020a060b0603010e07110705040609090201080c0309 79
    0x1036031900c4122400d43c401c3d0040815032103500c0400090802d0014501030711683e0000d05158040408000a0300c0a040b64050b0a520500c54591465070004c1d100c01d0890094614195a4a81481e0343c0c280c0390a600014104050800c1540c0080710030341e0041c58280d0081d404c0d80d402031115030801c0b09507070082c4180c43d44900203000201c04050080680b0001012803402c40f02d81c2c5540e80e01048182d40c09078005d006a005850b001c8113400310030702c850301c0001a10006484e5140c110340d43c441640c0c0f904e0740050008400840d1100c1038a0080800049414920081641146240c1340c024054004003140900085c01c146c0384034064104285554080c03068098051940d01c49500c005000701044042035a060f60040000912103500748a40e015024650740600400030060401034160381c9011301c62402404108010021002100002c0d9008111307880d14048110303290300081d00d00b0000e03410250b4400d1400303d000400c10801d50004050341e2003030b26440a0303951140c82c040b0f110f0000311820303505034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 476458848 1250 476457598 476457613
    0x3030f1b080d0209040905060106180905010501080c0304030302221e320a0e1014061b0a240b040203010503030403170403080c0a0605090c0d020907120525050c 70
    0x143c004d4070b08201d0103880083c1214031a220203151081c02c1e030081001c122020041800b02240749070007809003100010074401c0e5407501c80001d01449005126840f4180080041020144a078044444080918480c1040e4190303240705125100e00314802c00c40089600d0030400c80e20f40d0036a00032000c81c0d0185821004444524246181c52802280e17021414609464042441d549414190000d00004003202e0080d180c608000c40702d180c440d40041c030800754101c105c01c0700d59580b40d048030b4003004041c0414202c9880e030003410340b40c1003060307000615541c880f41c104000290880d07070014001c484994180002071480301480120b00c001e008075505030700f0030070081c070115507000c00b04441ca600e200c2103149015640d4a032452a600440400da41c02e82110014406000b1180196a00084071501425031b981d4014000740189142d010001d0040a003040081c04841c0240401034800d0803525061006203455a41c8400240600300110880f41c100c00ca001c602c00c0c85201034418920383d800040100713 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 476460098 1250 476458848 476458867
    0x105040b060603070210060b03011509030b1b04030212060f0105010e130c02070b03011202100e240d020a0306030b010b04030b070813080c0c040501140607020915090103030f1b08 78
    0x10b50307000400000a41c0306560700400c3d50010707489058000c2111040d201e0303d95042c80b4010000c1c000d07803030221040181030081400411388442403180c0024401525081c01040011200294040c42d40040e510154403285035002c0e00000c12568803e80154803080030503a00c4100540b0031140c20f40702160014542400307012081d06607070100404a01500448400a6030344111111651091f00411900100320b1140380031424003191007102c000075410801d942c802440003184010384014041c00f41210003207420818940201e0854090301303940c0c3c000703540d00e00ba2a040a00640075601c0100c0360f48880d80e000107001401c060596003541e41c06141c241302c50302d404800320703034080c00604103003040b1035800b02035000650004004c04102c079591001c0c041100d906c40c2000120380051340708100c80c9101c00c804c03810565412003140c0c82d00d41d044504102d103450700c0c2440594456031104103904801040004030a040e04549501e0034104550360302ca00440c54900d65000006650400805404050090011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 476461348 1250 476460098 476460109
    0x703030507140a08040f1a030c09040615030e1504051f0b0306040b0f0a0c02031b0304050a09062606060114090301090309050a050414070309030527120105040b06 71
    0x40d0034050035603004268900303121a418460203c0e03080700d159000041c10040b800c0303510140c00050a944040c6d03e241100d001840220f44002003000c4a0f65000042d5002e13603580303c2d031000d0041c00d0301490003c006040c1140250080100c01c2c60314010348901c0c0d060080c04c8000e072544030700c80c680c0500030303210400e94400744080044042409000444d1501e130311602980b001c11015100381c0c01294404441d06040d2106644240050403040f083e6080c0004580740030b030000102d549080009404c41c810300400010f032030031801503405c040c2d803080715201c00080b040305d107402c5002580c484940c6051400103c081c50000e50b541e02c2501a031a4001d040011030540c00b4440e0800703a48100300509241043e1140041d08507001070b0300c12004aa6a66010700c030131304040030914041c050503a41049201e100c1c06485901400c02840c102c2016102d5440c0001c15105809032599a0041c11282400030140080c100e81d5001110a40703015824410b208071112405008460246030440b500a00c07503181d000a100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 476462598 1250 476461348 476461357
    0x60316140d05100c021c1b02100513090603060b0109061e0905030607080106080702070e04110402040512030d142205030f0c06040c1a0d0c09030807030314061207030305 74
    0xb00d142c007a840c030307603800b01c0c200e4000c403c50109254060080124442813414110340c1c000216030400040d19503429494140e4941004d00c2c9804a400710803038120780d84201d03200d20a00c0c2a81d141c0510080c800100c480440e044074040d43c0c407880c03083c0300c21458100112003107007507403159a0000308121080d0024003044800744009010354034002e11220b80381d0000c24170340b0b20203031a4603002800f2040104110385c1d1040042c0c1e0845482d201404246291103042e090b01d1034003400250032115680d1b81e007035060b62603504032401864050104a407075050700030402e03240e8001c420b105801501f03000600c0d240001d03810386123200e42e100060000c8031888001e8103040d504d46a4000300c5075440200041000c001101d07000d00b04032208140102020714040c940489844d4495201350310003941a89890b607542042001d941c02c550075904001081000090220b82c00c4866170b102821305070001854000703069040d00001c0610a0303410000406459590034030900002041c2d04250320340000e942400043d10410041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 476463848 1250 476462598 476462603
    0x1509071d07110102130b0d050703050c220e160e030304050a090b0301090c0801020a0207080a0201020309120a1208180a08040915030209010b03011d091e03070507080105060316140d 79
    0x50038180c2c1560f17803200390021504144404071010402000c1e59056005071139108803545018082c0d4200070302142d031240205151802c48100c00040c09803c80600180703080101000103011496040007840400e591680c0006000020280404800d0b00d0800000711022200f028042c85801480d1042c1c00004200400702a60305d5504d030034100c0c01281c0e0040c015000b81c00e400c8001a03a851154401234503142c00350380310941c550400100390001d82c1e0040141e50019209491070721407030400c00c14003403d044d0304c003e00030180308083c48070782c44040d4440c0c0001d110361100c819403040790101c41c01c103640c0c07210b9042004100c140200300c2402502c0d02c94100a40504100283d408402c0e00c1e6070006a100c68260845242030724007000400041c10810359a40c400e111600d072030049400c00140098036402c44801070b03000a03da80041c00300c490010001c4481c01c64220003510903140e151b13403203503020342010307243d1510034400c0e000c1e08201180b1960b041411904400403020715109981e050114160616006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 476465098 1250 476463848 476463851
    0xa0b1b09120d020d08010509011401120903030b09070206060d26120601020c120604060902061c1d0115120201050f1206190e04060b030309031509071d071101 69
    0x318440d140c1d95801d0482054680c050030499007140002481d082c11601c0100800013038600400640c0c907082c40c0360f819a141000070801070910300005a0381d0040b148022a009843c0640850031305030f00d60b110048031102205c5105041e00c4601d0102e0f039492003900d0b8140e02c180103480c0d87e800502c1000c0304036964151078100300b0582c0f01c640c0c1ea03000940c00040640304000b64240400c6415030303040c04296111203040310105011010303504c11a44d44c1d900244010802e070307560320410003990380b080309841251100b508040d03421410001110098101039000c08100300600e031824005000601881e40400c007403030b0240300c0f8036261083e4442219090344c0164103210701001040710780d00d509002407982c105450380d904010304156040c8402c2c6100d0300050380c2051040c813400e00c00f0328185400035401c1a0031010118191001000290861084100696140c810b410151075410048080284142003800503118900ea44490308902003054a031084002c2c680000007909040c0a90078050310302a02900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 476466348 1250 476465098 476465107
    0x40506060904030f0e1c1a1003050703111815030c042f070f050d09140112020a0e03011b021209010c080d090512040315060806010605070611040617090a0b1b 69
    0x200f2001e801c1c6c0d10400e5404690030720250048013448001c10b5000055a00d2000d20359155880361a11406203020042c03080411252000c07140d900e01e0348000c0755001c0c5001d042c0007801c00406002c0e9091202410501030b0160000c1490300d0700e4030f03105803050743c0a4151081c0d16250807115201485079030300383c4100450000d1040101041c507100c04500224800d42c000c121461100d0000f4060740703010340c400800202d01d50707030054090740d200c0034940c48006407010250702c8128041d403c0d00c40400300040d4541542c82d10580b0b030f803e0f0003013a68001c0400e11580a075041c0509901100e4424416101024045038003001e5074000260058010280c2940a050000b500d1169580341402d042c0d100b4610308a4940c082402e006200d00609028240d00c903200d800c000d03603403034000220f403a640c0501c180c85c01e201010840c81c0520a0341e030841410b540c00101ba140c2d0b02d68980714094a2074404c40034400700d24030050300003040c00c000010049030003600701c80f4440c079035a164070281d584818400307024440c0e40010300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 476467598 1250 476466348 476466379
    0x11a0c06070804031e0f08060616080d060501090b1b03130e07080f04050709050901090804080a060e030c030d05060a15021e070e0a0f150b03040506060904030f0e 71
    0x60140030788596562070b9039a0410b820010b0000c001140708840f00030030007091342806500302400390074040c1c13103040c0040c9544d545000203109024080100209524110f038510401280c40010464000300007420000d82d6251401128600c209000b560b9020700c003002400028000f41902c0d01c084903030602100c0c038204c004003a154080d9069440381e000d0038510014001400c1c1c0000d042a4004801c1e5075151301407070191034481e600d074941d105038140c03540d0f20340c0410b4080d01c082d0801ca401641044119030703180d0341c45040c1a511055101f090754074500d81198428401c4020084900504901d0300441c1405034403904000140070181009610007200c22000400c5054040344100161080c0c0150401c2030900500780d59508807168460350fa500001c00a00c40036040200094100307111010010744500d450341c000c8010886e07400e4112403c0301c2000c00055022640703006602c210700c620140c0c1c40c1c0b0385540041c004100800d460042c041041031500705401c600c982c82440200c0001884a040e940016 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 476468848 1250 476467598 476467603
    0x20a080d1113080706030c1205090c15040e100b0a03020904060e01081005060f030703030c06110301270510060302070611160b010f05030d0c2409030e090609011a0c 72
    0x82c0300e80c0381007600740c40100401c0c98140603c000030807050500307010a06c88084002c4c80220000e0303041c0f12182e0b981d00461001281040350140020000c3e042d401080c400c4818000180c01520409100c0c0c6604c8000500035410403103d2004c50b100c186601c1d051403d109016806508100150f42d000340c5d80300c0d0b001460a580311003c40c020000794020b030204015007003185082c2c80c0010500c0740101a0b2182940e11600c0000380d01040320b0b0545405c200c1100280303042c0010745051002d01014000200c00400c0708800c0404d002c0c180349804001400b608030103c0c01200ba140f0460f0058000e400e001d030108041c90298009008103481040002806801e811442d150b035009121b8400d140c1d142c504c07800080240c084d14450140c80c440c0034001a9500c1c101c000b0383d4600e0b0003030300e80d0200b10038404502b080240146185048400c021117003141c940c0c111541b100109902c080035030004183e400c180b0540d00789010322a00802001e00b96a007283c0c20001a0900c2d8003600c015060684420007003507090640c00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 476470098 1250 476468848 476468857
    0x21030c010c091e03080301120203010902040504030f092c04060b0a15120b1c0311010e030d0c0519030c0c0c140f060a080f04170d1e0903020a080d11 65
    0xc40c0c586070405410006030300f100c2e1a400c0b803101c0c85070544180c144042040403091b40d044510b03901000b090400c452010902525071107400075041414a0103101c00c1603080f1500148408003507880410003aa5020042480108041c0d200300f001c00004401e29031a0701d0305203460380305015034404503140c00d100001c01d00c480d001c2d90200d04c001380034000d0b986400743d0288425a0b1040d4a0b00144543c440d40310000d88038600007261081d07070001e01c007880c80815029103030803441626031400070840b01e158442142d03100e0b44050001c6480e14a0408003684d910b000380d040c4c62150781124075090b404051944254001c1003001c59200a020000034290f000401e8051040054484503c80400d524101820b00aa04030415130a5209a0b810b0010070300941d4410405940200540661101b0340c4803410881c4403422414440700c2d02c0700f40003c1d10b61141c00c0c550040356140f03a54413502c0a01445181c071160440340305242c02801a04540d00b400007140307010000e402803141182d40050b0501d500e84c1c1681c40d5500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 476471348 1250 476470098 476470121
    0xc12030902211615080109051509010b0d14011412011508070f291303060c030911030d05270a0303021615050306060c010e0115140f21030c01 62
    0x11210000d001000c088150900030311300001076024924010354041c0004105002d40080349582e040000c0c01d242c0004001c2405c42e901415051407940c540d044540345500220f00d49491901700103040c0c0035214241c0d038441c100d803030985401c035000c2078080412040c480540c4441d08150340f505462604214100c52070801441060000c2501d14603041c800100715110303034451a141e2100300341c0380800040c010f0b030200c42c100000c84415614032940450b8283c505007a000548803920305001c0842c5107406601c101310140c0210755100782d0016840805a68003103005035003000a005103c0307510382c2038140441038110814a0300091080002101040028816078070542c0142e02c0001c2d80710003030481024446c003a080c07041da565102901a60301500340d120141c00240642d0000034824045d200c00c3d840307840708242e034500a0007400c8000f010a8002081c80c02483e109a071300c0d10302404c840c030b4480c803a101403490150541c14501d440d8148a140324854403281c40c040c1c0410800b89420740401e1158081c00c0d003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 476472598 1250 476471348 476471353
    0xc050a020418020909161206020c03040b070b1b0a120f0504030503011502030f160201020c040f060f06090e07030c02150f0a0501080c0f0f0303040f0320010c1203090221 74
    0xc2d0140100000d8550203091a010b0360040424039103038829540b0104152980300c0200b40c0c903d0740524118009100304400d4080500000c140450600003010040030058000c4000d4402c07500c804900701c40c950700016844000341800c1020380b4002d8054415142c00100050bc0020403229608054054130000c540440c00190300100501000189025400450003d44021401e11422000700d40052007a4080941a8040d1706501c01c21680308200030f0803000c0029005000707501c9656000740c0503100501030703002034a40d560008a24103109000ea841141d004031900740b2140c071543c005500900b0070010080442c05066601d403070403401c80b42403501030880941c2d00050340c5000000d82086500680184100e6080544ac03000503694844040d480300c031007141c4100310701c030f0000c0009141d4031441c0d202c80c44610100400106000d12050340720700c1c644070f50b803050402202c0d41d801192601c401000041c9004c0c03514000c203d4040c4258000d6480c0d80c80a000300f00403590881021800c056451118061035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 476473848 1250 476472598 476472641
    0x1207180b0325180b0906041d16050901020c19030506090c044a011d07060c03080a050a09060f0209041a01020d120b04020708120f0f04030c050a0204 65
    0x20304410110090300066161100c3c1144008520881036031080c4038800e03284002040055150340c1e940111401002c0b0103903120728210b0101d5440700c103480308465406160034052384203080c5a005c3d41c1100c1008805070301401e800900790040007040f401e158103501d080f81c82004c0200024000f004594002c0038454010100100350404000940e4107200010314400100c0c80140c7c0c0341503800300100e0400340003a82d001c83e407410b014000d0114500a0054150030742c00d10300d0415031000503000744400d843c2c0307243c1a100c0c46520307000169042452100024005041440000c01400d60340d40450781116403a540172521b240151269401e0707a031000a02c020702e41d80002c60b03070201d240038820f00710300b2000c1c5d420f0510fa0305c41500020f5101c103803144808003070080c48040a21450b440b503201c0100c1c5103004008645400040c00d102c041a001010007411001151010a5510203400000c9204d900d15007807030b510607582e5940c101c1c0c41d60110682114140700303101160005903502d0003050301c0d4004694044059 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 476475098 1250 476473848 476473891
    0x307120f061202210d111515060d090605010f08100c200a0c0303080f010f03052802090a020d0c0e0d02010e03070e041112031207180b03 60
    0x844040080d104003180c6062020031100c02588210703000e1580440d01c1400030070302020070342480d42d40c050210855009004103000015041a0b921072100c060a04440f200c003004907072224550f406541c2c5034081c000703454400d0881d00e0140c005055840d903407540880d403050b1540d01c807001d83d00e082e001040c000304100024440e07860304202240c40030200c07140c02d00080009040162800e42c90000d4110341c4182011001ca2480c1c0070401b009105a2100f903030000a540e9080003071000300d09554061422100600010b00d01400c00d85650949400a01a100c805410f00c003451030030300e20340017101c8411070b40800c10000d80e0b190045c2070701c900007185000d40da07001c40d59540021a80050210810321140b080b040c00141c8452070010071440e428203001486140c442c0010b440c11616078043c0c005c000b900b1040104009402d00c04800d0b030750050300c01c01c40c0a5000c2d00107644078080e281c0e0ba90080c51220f4009030706544a03108075201140d024254684050320348407a60b1071540100c5180c0c18200510700b120b46c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 476476348 1250 476475098 476475101
    0xb2a0a060b0103020315090c040b07110907090b0406050d06090f0e0c180f04061b03091a0f04171b03120612030409050406020913090c050102010527030906030712 71
    0x101c540c003441c08500d9484c0c061104140034a218810b2801816403a00050b04801407600300c0e0081d000c003d8000c1d84a900d03138607104102ea60031b000b40c0c5018540310004105d519000f10554030554110502c101c0c20142043c4c01221903070414441c6a481c5030b140e9070009240e007094132070440d040460350b5011940c400300c000014034148802c50124068503564208a42082250400716000401318405844a0303e60341480000390074040450213002080010101c80c0c20b805038002c81085200d06c0d91107112030b141906c1000342c1c00d01140c20b0641c2c046054006000200065070001c444220103400c14203148424a2110001007940d80c10380c01c5900000301c4420203c1031121043d44002c04036000c040804c00d80b488103032030340900d11448000300d85410101d0104501501607400c840300251000780b01c028141039040c064034450f8401d86020f25850070200c0c041d44103014551141030260505128140315003241f03407580008162070303509400140106010382d070f1184000d5001c1d03807a9a80c3c50969801c0c08103001c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 476477598 1250 476476348 476476361
    0x723030c1e0a060e071505190807120e0a08220504020405010504030b0a02160b0f07080f0636090609010204290705070f06110312010b2a0a06 62
    0x9158104580d80016101400640b40c020254008404076088008000340f40c581882d940014801d80c00c96070348404280d07440320142040d4024002c010b280007200b41001d0756080426921240062032001202809002903000b4040c400200f404035a501005915030303495582040f1656503070f0845090b030600b2003141203082c840240c001164214541454000083c00c0c8d0320861000a24140020000515040c4140d040d103840448815681c0311400b0340c1e140c41040300c00d003200c4541c08880b00001042c045ea216942c1148581d140010a401a8858004202441074900c41000030b010421181001c02e00070f080380612031950000f8008024200000c0075401c116004003043d180e0380c41480200010120790784420451035800204815110b11030000240900c1654005001482070100000c1e4460102c80040200c070341c156140d05085100d080400d8481c030403042154030050030b1100601020b040341c070003049000002030f071281440c07009007a4030001d60082c034401101c1d82c010010340024400a4000e45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 476478848 1250 476477598 476477623
    0xa030605180f0d03050c0c01180212010b011d0301021c060504050717010605250507030506060d02130b030a120206010305060c0c102c0102042d06050723030c 69
    0x14451203a4400c07485640304802503c003010140c44201040c80216124121800124650005d11030f40071002800104240d002d8002c030302070903265108002111040c441c511103000140d6500c050050071000ca034190258011800e0390556080000784584003982e0044241d50b90406400300e1003500e030400b0402180c0d80100144280080d141002004c03010010380c2c1815101d960030615254054040c445415100015900b4803006c0010b0403082800000580b00c4204c81c1320b14112901e0b552240e0a000c1d4405a03d000203420a44034505000024015004810b01c0800034040701e401c1402601e4841c1e03480612507507000540c1041d8014001d026007440020740c00001c0ca00340c945801042c24006079240c2942c212040e0807507662030410071900c18032849099a400c40424031101600c6151681d00070341c880e00c80d01c00055400d210a00e00110800f020b0314800c0b000300340c01030810b480c08800307651070b50040d01c0413aa00e00490751080c0a03860010926555554964025921400f4070300c0c03240c1c0780c0707000340054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 476480098 1250 476478848 476478853
    0x5010512010e100507020c0d050f010b030309010210023709060305150f0109090608030c07120803040201120608010c170901090b070f02010e070602030a090609051c08090a03060518 79
    0x41000488000808030b0460f00c0d2410002060364a8640032410055046c5185500510015500c0140600001e03c030307180e4201c0070001c110726140401010390728030443d00d0960251b08055110004294168064086e1104c1111140d800308006401c900000229604403046000310164000c01203900400100207400242001c0007641085107910b120405002161031007210014410000d9074440c1e41010000c103044041170004c1e9803203640c0d5a80307942004402d01d40b0751084180c0082c05204446090b402c00d604290340604e142c03515001110610703022200301c20510b44403a0001848007091080c3d540040c8140e6072030a20341012555250300754005001107040740c0c108a0b0f203e0211721582103e40c4c00c29182e04110b85e01904000050f4003420302c415035810940240c0d0340020b491600030000307002954040e034401d80b940c1c1e1621020354072034603240501e981000c5001c021009a6020112201c102c03030003201d4190a000c080d0001072050398068000f10b503425183c0050260120303080e86101c9403031609102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 476481348 1250 476480098 476480111
    0x301050901170307061109010f090e0109051308040902040f05091902090102010915051f03080d110c0d200109080f181e01140a020303060d1401020406030501051201 72
    0x5600d01006016075000e0100400101208035010800c840361158040340c14172082850100c60040d5410803085240481d00c0040707842c0c246446100c00740e00741c6081e0640d1540c240d0038495080014040140784a50300380030110550082941480640024a13003e64090380d00d030300700403100303e03046a59400140103010982c2807100d0007002614142091128040058449152600413405405040300c003030502c0d0204440041075035802c4d001103208200c4c900243c6460f00510445501e0105c1034071024207880c000340301503110300d00c2c0d6030403403181040d0f000015410464481020703400c2c0483d40021300041548150010070401040c0c01140c40540c010000304510081921480c1c1544070300e103c851031514002400c1c1c4e045c0c0b004900682c80f030442c090708218074102d5411502c45403240c550011400b2a1405c0c0c6c00d100c42d850310208031202060960b000e90304503102c0e48140410302522900440700c8001400450300e00c0c5009101510042615075000b081c1545407000b801a002414000048107034102034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 476482598 1250 476481348 476481359
    0x1b0305190c200c120a08070b1308030720120901050919030507061107030c15020f0d181406070201050d02070c030602031f141210090c18020301 63
    0x981a14095550226800c124000304858441c00c1c0d04420b040c0c241075620304400740c0340c0007501c5601894296a0110442101c104d101d6842801c40780c020300f108010013013940000c0c01c01c3d11040e00203c0d03003184429070450030364403448035410803564240040c0c00d01c0d20032800c10502602d9401070008400103810455440074244c0350911401003098148003001582c0303421503c41d1148602c072000d8510300340c20a10380300d103000c980300e00e03840c0701d240c00041d90424407030003071880421190201c0b68010910300c2c03028907155030002c58000c800302090650017030702c4200159000a10030005c50728a03903555240714088888041507242c0c03058020000020340038510304541e80704c1d00222801c02c0d4090800ba600e5030214006640030307101b03080380100030061446002081180c0d40c1c0182d40222600c05a00c40d070107210015803500001d4034401c6032107a44940d01c1200e07260070030201c1c020420408500f542c01100400ca4088144c4a0102e021103034062404000c01c4940001c840d07030203105052640c00e42ca15407400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 476483848 1250 476482598 476482621
    0x2030601091802040603080712052a0a0203010e0d020d030e0d051b0a15060e060901031202030706050f04030305071701090c1b03030e0f070b07110a181b0305 69
    0x5001d05112203a442c44420b08000800c01640c00305680140309104882e101c1c50400c42c25001003804850907601c2280c000c1e0f0107401202950300301a9504c8424001700c0c0743da0001440741081004031360b103a020360044ca4002d41ca081c095400342c07104c144018000e40820041c0280b414002c8091902010314040240c030580001003206540c11040380303407081c0c07240294400e1b261003014549010303181e445895202c100b04150076122031551080b01c2c0c003c12501e0382e03c07940041e00700c17401c80d4980c1d40584510014000a01016410320b0103802c42e20440f4205949591030f08100c0e030701a6900b42c002c40e80311042204140d07040c0901d42d4041658507040101e66a0a070b0080130102c1c042c0212590180c48038003102a0303d00c02c10a5190b69221030344d840b4500e09042c10046e0040c06070320504550790041040d000d03074080300090301e28110743d52820020310f04000c54982e120b2180c6040d00b095404540c0c2e2400040b1b0341c0794200b1507480e4540d41080021140d0150400d4149080c081d1b41d0b010078141440704000c0d880154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 476485098 1250 476483848 476483851
    0x12050309090402030f0706080a050a0615030510050a0905240901170a0602042607060c0809060c0d120b0103090b040b0a0b0a08070501020105101a0c0f030d0b01020d0c020306 76
    0x1e07640e80189807624800a4285078a407040340c18240b00d040800240180d200300018002c1003e51403c100c1e548a040d403400c00c1d1881c5005082c444a1100800d01840d8400e5002c00e80c88900745e0b114821060316580050000030041d031000445545400034403d28458050105000f101904000f40c5907003102d10100f02114414400c20218034851052181e22100a0000500840e44440704540d2282c039800381100c440d0307160402600500c11080070f10f1048100080b0181075445580b100003000000b69600019540540e04c80c0360026024042121508804c204041000403a40c40d9401a101c103400440211500c00c0c1c6490704150400307000c90007040f041a0f04036081500b250036241607a0b40c2250b4040540001040c1c1c0e80c100a60000005039060301042200175140240c1c02480b6946030f85a000c1c0c030755580c6000350201d0107051041002800124001040e450241c5010355107410590301406066400140c401d40610f515007160183c1981c0c1070050503107002c82800c1ca00c0080c4005e40110342d07a601e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 476486348 1250 476485098 476485117
    0x9060105011101090203030a031d010c051803070b04030c030b090312040f020d020d080a02010e0f0d0f0215070c210c0602090411070807060605090c0d0f02041e0609120503 75
    0x6000c40c2d48114003080d00141c07400e07a0041c0890303a680f0b5410000500411034007180421070003003507401860404040c0034284078000b16980d01420990f40292101404000401107589882500d2001a0304000100640000c0d1700404101c0d4441703140d814040c904540c020002c6c000c0f60000c120403030b6019418900f41e90415004005e080115205201142070010f501401035403203000107103020100b0001100074980712006600070b00c04402c42e0041682c4d600a5210060f119130410b8004580803480fa15801000d5000d600c1242d0601402c5101c191200d00152050000560821003140c03e1240341c44000421640c1241003070300d00811800000c0c9640740e41c1c540106401d40005041c003a0741e887c0d82103040d50081a815140d030f103d1640c580100d02c0d5000d1002100d80904082c2d00080518100c46400c0c454419031151500e4941e03107803101c20050210726541e031030a903030a12010641c2105024102c03110100c070740140d48980d05014000d00320307010581c440003210103c00781c200d00160010040c0c955490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 476487598 1250 476486348 476486357
    0xb040f03110109050306040501050403020c030708071e03080d06050f0906010219061d06040213050106080c0f040e13060b0a120f08090301050f10060e0105030708100b13050a0e0906010501 82
    0x14841070049420b04944d41c8801d0f03041c41800c0074802400320650000d03028501c07035000c840034160740d9000c1c19103038011845181c80541010204010482a06482c0300c01c403502a0844403486403680c0c1c0d00d81141d0444060f5a004903600e941c14401800c01d04031080f0110710441e60a1b043d03148c4040000c1d0740f0041104120000c021444110080140310b400030011035020308150212803040c2102582d86030022142680b040704a9044400720b4030151290320f0682d4026a5401c2c4295a0380d034200a0700d6200181c4040c01420801001030214021140540207802018a800c2e51b001c150030444181c41040e0301da01e00c1000001c1040013480c50701c44d5200c500551145601c3c288120608011a07540610441160507500705030030000303018003008460380700741003c43c002a18152984004c60300c004048640a0224208001281510b80a0341c003c3da80310201e244503e40094845164620541101c100c0540d0030400003007c0c0664a8031181c01c10241c02c55280c046003600e01911f45030f0b0b50712010f201d0b490500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 476488848 1250 476487598 476487623
    0x303131e050a090b0f040c0c030f091a041d0105010206010501030e0c0d0303061a0a050f0306190306020408100b0307031e060e060402090a0212060103110904050405030901090b040f03 80
    0x80c405000001403400600840380d85503103c065030050003800102c181310b48a026003601442c0707090701c103440f00865260350f50b942102c0f0554090341d1078564140c1e40c40900001600000e002e00b809508185860340003003000d0384461a020480c808210001113001e82d8840c524014006664002401411240b092802103048141d0024090510300b640f80340d0b64100540c116201c1c24035404d504a0030880e11920200100503280c2800c0841382c2c02100b04400000f442080f4031002d41000e80041c0d41c11100c02040c9144605a044840303c0869065000f158410380100b4104a070010078080500701d01400350703003800060b44030301c0041c1e202c030400d0000030802c20603612150000800480b40801e030950011040203001800d0720031a035100d0044804907c00c0c2007000c0080c503100d80a00035034000c40e070310703244100898a4450040d405412407070754030f072600c400510645d41c096480d40240c0e0f0207a4000c1e805169943c00120004040c4072064200e2410000100020401c864048004c1c000700da40001c84403046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 476490098 1250 476488848 476488889
    0x7062307050a2f030c0105060f060f030619170a140f120307050415110d1b0605061c0c05090c0301030c0311011b140601061d061e120106020c030313 65
    0x1040c0c0c8846a0f841440082076060400a055212500800b001c8401e02440340c200c20421849200b4011102ca643d1000c0c0040b69407410b08150860070b07200c1c98110712030321075280c2c1007d208502180c004d040ca41d500205126083c000694a586100704400c40507015202c0089441d80c0d44070075948480a07010800800241082d100314141c40103040e484040400c00350700f90000602e8402110301ca07001a0003070307517004000f080c01982c514041240900c01c15501020580b031321001018020300341600040f844882807018504c0030f031441c001e240f2690810340207a0908042c80031001c0d0041111440b80d5040005002003420040080c08680d4021210010b80d5020700040342c0301c284040045100b445505082010000c44580c003032080700110302151002d03070340e0ba0f00c1116480e002102c12414141d04120010041c20507400070102e000746861030000700340d1142d03120030507548814443c00266a2100040c002c2507410310180c0d010320011801142800c2410804615800041c81a4501c0811004da5030382c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 476491348 1250 476490098 476490167
    0x81035010605030609070602060a020301051012110a03020706053718030305090d0201050103120c03030914071d06010203181c06020a09060c050d0e0607062307050a 72
    0x1a00c4050b040d04c183c1d0420b07003181075841905000d140054040c81d0300003160041c6030f10a8904231100203248001c020201c0d40306a0300843e003403020500141d03c8216051910720840010322000c0c000381c0c0c0050b03440300107017450011154094a94602461031010800d0380c0e00a103410348900540d0308042d0000480d410244400a1400b0400c0d840d642c26844040024903800d0b42c07040348101e14003425102c4204441e04120700300e40703007404024002200c2c080007200d11032141c183c1c552103030b00c40d080005104031183c40d5580d083c0500c0003c00001e9016420500001e1490403401c02e0f8103a200b50348051a05021001075100d01440d0080104000a180725000c107039103002c01100401c6c10a40410290342c160705141000c1d6003d1740e0424040f66a0741c00004010b84103001c1c8490490300b00c8080c1c042c1248400040302d06520b80443d2690040c400e100510200d4200d105402e03491242e180c0d40b404c4030316446102c643c00700004207542c081c40028401810b001c0d40112865100e050a01e10207000d04504400c1c101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 476492598 1250 476491348 476491361
    0x8060d0b0702030d0b0904020d1b090207080705010b010807170606070b040f03021b010504090b04090c090603030e060c0d2d022506120c09030602030708103501 70
    0x34038080310303002440640d94000c002041c0344101c500082c400c2c0001d105c1400341443c0183c4009400c240c1400321b640c00b107070b01130a03041071044035451030601c9950b950400c40160f800c0005e00f42c4502d400001c09000f0001e00f4490720007940420b003070203403142c9403008019100e502c28103030207141c040022000514550b59134007200d0449a1000d082146401c060602c000c40c2d0310804003c8000d441807040b00a20321381092507903806280b050f940d0341d19282c1000020b0300500180103005800644038400c0e01c0c0003821400a0201500105100052151940c100184240030090810340910760412500045107000700707a5401c00d0a10703040109100c1103441441d02106d04502d01c280d6520352030381d8a0542958041032107903410300901c24003030038410b0400b24000c81114501c0340d14040348130407600405505a5400458207411141050a2079031365030303111364050380c3c422a854000110110304201459924071a0a4041d00342007102d00c07407807070350702c0c1c044d03903d2a02503d40d07042044039401d10f241140c031094006c0c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 476493848 1250 476492598 476492603
    0x24060702060d02070b0603031c0f23040c051507081608030c070614100312260f07030b01081902070611040e07020d0c030f030e0717150906040308060d 66
    0x1581c2c2d07286605051000703402240f8102c2c4d844503014081080b07032400105840c00da80442c401100022400c4194100401c6802d14543c01035480b0742100d0b10008800c0c0802c110880c074120001103910742490284030041c078540010340305070002c0042840e034a00100c1580c40056000c0070b0150340b41c42c030785100040098440402003c3d107500004120035048140043d01140307101740400c0c040e030190380d070150000020883d01c0c15038080604e101003002c20203000306d4203242e040300d040500341c20450003482c1103105001c0501007900c040391070038072050400b003084c0d07103612215a2070100718180c440800201020130140c0805404850380e04c41e1651040a94101d88003254001da00f0802c0041c0d8a1440042c4d0f0403d100780c140304c04038000050050303800130511508100f101d64400280010a030f40c103a031100f4418421404244d40c6240841c424031080001c03c02809450b4a15185c881c2c074000c20500e0020140c501200a03159882402907071000010042e400551500b810101980c031075010640445070140302 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 476495098 1250 476493848 476493859
    0xf081e040312060504050402181305060709050a080303040b04031107170604020a0f08100903031404030206192304030201090c061d040b03030d0e01180c0905070824060702 75
    0x10300c020550464079400501ca0b190400340003055440c0100000c503001201c0281d081043c412400010b081c006010f01d51081d00c460121880049940382c2e645081030031075035100441c11341c01c818005881c050016200a1020310000e52651800b5a50034032108000341005050042e003040c4071080810904c84180030b0508150300c0c1c2d44180392040041c0c0d4a52055806a008201c00007020030480c1d8110704140c191002d02c4020001c2507a000024801060030820950800d41d0b1740c0078210345030360540c1d0001d0245000754010401c60400141801c0d12080382c204c6984450b1410448169002e05501c1c103038211342d00c1c8080c0c40e07007640d201d040c181e02614100d2401003406138030751008034110360450640c06c41048859407040d0047c00e200144421100307082d0f511039259000348140c03440301c01c180c5c01030b091408048002240e0b0090082c0c1c0300e9090f07107640c1011074034189104420b02144141c0c2c41055800052460500803a0402c1900c948000d03909502d600744c24000d130b50107a1156251a02100d103075641c007800c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 476496348 1250 476495098 476495101
    0x302030606040b0112200a02030414090610050711090a020c06090303070f1107120b011509061718120703030515090f0c0708040605250201080a02091813030207150f081e 74
    0x87c025100d80c81402880d011103202d2030004500d0511012440c817540000d440544010400203003550b1030f0700b0281c42120300440242c031038085902d0b000e4045000d40030041700540c503034801108003030408a000f00480b00540c8140100440ea50740b0842c0c20034080014141608802070401035a41007aa29401c0410f600c00d46d00900d80400202c1011107040b01c000d01d15122481341c81200440c1c0c81c501300d1146400290070300c0240c040d08402d03550115002003c0300c0703440031650351000f41c6505140402040050400c400f1940c20141905030140310340c4121303102807001b02c117130800d00042c105600c00b800300c070118840000041c1e08074400504480d84950054003003070300e8541e10b800042c840c0d44850540d041602c0711409680c0c241000240c5031400c40e40c16140e0400581d244218480290082562a40c0c4040702c586071141d2803001d0703181e140c021000200c132405080c4080c20040d103404202d03403104c13501442140b41040386540c01500384101d8500c0d45007410a81c0c41e58004040041000c032504050300c0b81490 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 476497598 1250 476496348 476496367
    0xd0e010e030403120f140a02011b03020c010c0c02030a0f050f06040b04021017060907020a020607061a0901060c12171e07020c030a2a0905010302030606040b011220 72
    0x260048a224403801d540708840503004841c1700340d620b260740c000700c4c199143d104001c0710340d5805450507045902c00000d9480c204601c00180e41120707509000426400106210803da00303010b002c0040c6617506141250000c40c5c1e01103587c1d07842c142c00141004094040c1c5008000052202404000c070311004c81d0502e00782410000f0303d0786004e0383c0413031250301e080c81c840007410301401031900039960031140c500c0d55944003030a002940100070070f84800c60041e100760100699440d4041d10881c0e000b00d6002408150202c0580c50400c2d94000183c801c0011078010005140d1200a0b001c80e40d0b440130405422f060410750554a1540750860206000780748401c02c80d41d401d1100d890603500c12410380500107621590000d03601c844010034a41e80540024036150b0118681c070b03880b0300c03c0048a40410040800702106a88110754a40052441c2c0351070310010002d61904201164000000b110100301c0310110400280240000084a00b0415214400030071704c0e0300c20001e0b1b00001000040075540e114a0030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 476498848 1250 476497598 476497603
    0x250b01080d020d0309050c09060a0503070803030114040b0312090f0409050606090a06080d050306030f0607050c0114130213060807090c03150510050c010b0406060903060b0d15020d0e010e 82
    0x80c1d0394801407040601c03070442944203015505155800c0b03030240240b061101d05002c1401c2e4004c040702d8000704c00301000501030320100041c2c80107045120255499504103802c10b0589952003105500c61402c104181e1000d030b81c0440c91240b02c0d41c0c10000a5616103001022030703e000b200f424410750103450681b080701441000f0403281d1141c00d007103a11103d2603860040c0d2000312140b40c01940f07840d503c6004c407207201a01070f03402190800d074020b0441e8400e9074011089841c016046a00b1000102d000c60f000c1d201c00024003071204000030888a00d14540b6015080c0c01400147c031030040d124405090b089003100220382c0c8150302900ea144103031600b071600e41c1e88090140500d6405040024640088801c0441205801600b55400113006003103450569504944540040b248000e9555a80c030502989030b0392807168000800301034075541c2c1001d2460401404850454601c10b01070403000e030007103002a4024072072500e41d0392681c0d801621080c5203080d000080c441151200025844c0c4003001b105020300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 476500098 1250 476498848 476498863
    0xe03100e101b0c05010e03181c0b0f06010e100201150506160813080d0c0c0e07020c0415230f1002061518330303250b0108 54
    0x6608a603595010101d810088409040b1202000e2000056103205544510382c1039404502880002c1281146001202d0959001d5165030a072034440528140351410101c042d400040035500108140361441d8441c505041d500510b00480c0c0800c0c0303070024882da80140b200400c644c0001e0122440d0300c1302c4d4071000c1c0c02040480c48080072010401c000040d180b5248048400051104c250750b0b000c8141ca0365120074a8000f1440800101001d04001c0740782c4104100b0300003500c01035070301c2848068450a00c5102102c0613003285010003820380400503100d80010307100c12810015207000490303030242050780c4000070442d0803000000e03210f04086550080300c07103154144c00350100e030008161a48003041110401107040356801680266001645c0c1d1406007100005c0840c000e06040034081d02c8080f0480c80e00812180d5031500c81c0300b48059801041c0702c000d01040d0407030300400d004401440c04006541d82c040d02000002022014020241c503001400901c0242a4000e03150040303540c40360039aa444601 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 476501348 1250 476500098 476500121
    0x91401090b0a150501021522080d0510080a120909060f1a030708070c081c05070207050307050607060e0f030403050f011104061d01210b090c0702090106050a0e0310 72
    0x184010403c140b420300c6044811500705070010455011081460441c00d1300060044508070000c07600c14240d0f115074421510814804c01303c1a0b60380c4810b44c040c100b181c5000e098061402016682842644000a400c0408542000b50b1043c015003000e021180a040c903040120010706022002810707d00e5000300704196400d0030209048110034080c4d11a19010441d800400520a06d0129481c80c0c000d41c2038800007401042894501150348810301e0f510300c107422040c0e04080d5628100b0288039418030401c40604030032030180c40424500130004c0c100c2c1c0596080070302801e945050b41c00c038080c1d04201d507100032030401090765160b540d00e0070b00c9601d0354003c00e80f0706031035400c10b60034081031101d020494054801c1c0e500c0c1d005507255594030106c40000400711150500000e89000c030300c2d10796500e81e500c24448840f240841c145100c4003c0c4030108001a180180040342840302034016525460414103440c0c4600d440b41e1204100c000c21200c0c018012501038150150254039044d0000c41c3c0c010620301003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 476502598 1250 476501348 476501351
    0x409111c020a15080c0d02070c03030e120601060e0f0f040c0c0203061807060e01020a1a09010c031112130c060302071109150f010c0803010f030201021c080703091401090b0a 76
    0x159144500200c9000c94000800000c51303400001e000001d0040c05008034200050006003400350b075954841149207903401c181c001c5a81c01d0444246e510f005900b11000901c07103009040f0b2549024005881141d210f44a144204041d0400010310b44400c082c078008500000c03c00d00005961440141503003050b0902680240260b07000500704c502d80c02c0700329003144900b000501009160100071500240c20103907642c11800380617140404640458030089140308180514903031410684401401c45e440030000300241801c0c10024800905218196260704000000c440c0c105d0b91928580710901c69000f00c02440410049030118419601d1341c0940310892241c020440311440d600c0421464000842c0c25408a050355500c035200c0d41800b1034440c048903c1170400c0682136000e682d035030395160000d8201c0000c88404050070019036a04010003859034610002050030034520070300050259800400040505885120500401500072603800c0084040380c000c00c6180440d10303048124040981e403005106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 476503848 1250 476502598 476502619
    0x91810050601183003170a0603150c030e0a15050a0b100305060102160806040314090d080c07051c0f030509100e090f07170c04030203070807230d020409111c02 70
    0xb00f04c030f9144150703034154551422082081400d510291802001c2c40c0140e512000000001180f2613400c040040403004046075101c402e1300c0c018100e40650400304450303840f0000b101d01090741c2084160020a00020200e426510845110044c20f00e02401c2c0341c20800c1d904c81e92010562680c0078501802c3d090382a280040040d2100e000c1046440c0103070b10058100c400030a00107402240f0800074038140c1111181402c0803275000800945456400381c1d21040c0001d00c13044510b806100074000340034101c0e580d405c2c2d0f103c0400003425403030444100a14495664015005043c09141680c80c03501000f400c1400400007448020000090060f003580164a040003151404190501c5144140865621200c4902c40250034520541020309003e824150421010000d078400340311690141080b200200081071920500441643c0303080240c0b446411001440c112540e60000d4110301942c040700c0109600d00c1508207505032041800c2d1a6034810107121110100d0300d4103a0002c2107140c000c80700e50f40c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 476505098 1250 476503848 476503919
    0x304060f030b0409020f10020c0a06050c0f07061e09030203031305040c0212180a05090a0207170307022e09051606080603250902041409181005060118 66
    0x1680c0259100070341c0180340286c2018a410035081c6403031800c0c0d207841143da00301030900100c1c880507480d40100001490006100c103040c00100148070303000c0c840382d00803e84c0340e00c1d080780100380031802480721001105200c1c180c149184640d041320050768006054036525020000d040160351b01a105040c01241000c5d03120003024000b01d0003460121b00011030b646425440481c5e0301108040544099216104410101d11070326400c141a108400c81c920040c0d8446060900c01d05404034154420b1031100304004009280d50301189641001d03881d0360326001e0301c204504484140d01f41a01c43e080d004c13842d085050050000000c2c4440040c90305900c90741c00700f5168042207400040417200d15405511442e848100e40b00c001c8030342c0d1800103c1100d04100d06442e00b00c00c00c141da000b03a00c080010b918001340b05240e840d00100c4907400554181303c2c00010400c055080c0e80b0b6138400000038a4081d603500000c0c0d4030b070b405102821054402d050810556549800008503500c03443c1501070118141920346214 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 476506348 1250 476505098 476505101
    0x120a0b19061520150a14010b032e05060a050f161203180803040303060e1f0b0c060a15120b0108070603060f031104090b0f06090c130504090c080304060f030b04 70
    0x4040383c03c803018148401040c000d40c1c0702d41328050300404590350f0303c288561038400e00039150703070280240100040c1c1d039003800c030080102c1490042c0d0140600306250a01040c02c020307520100c1c119502a07601a440300b4074400b06555a000710409440b00306800600740d0f03080038016208500c02e910074032100300f407158294401c0b000c603010300260510514013089540e0108034448082c0d9400b9210f841c0102703280d031302c54045c0c04982d070041e15444504c03600094a00f05c0000307004841e030040d003509040035042c1980300551641d034000140182c00e890380d582d01c06019410912030214080c0400003418407140c4043e24004864510034811084180110035001c20149d2107801480701302d90016002000240c11515480398403140c40180079070140d50750988100103070710051180e10404221f0400c0c9000e203402400d004890310001d1a501a0641c2040800800300c42d1500020541e01c0984000580c050640703040c0030009210382240d092440046030015500750b1156840c164084a50707402d00013030380500c00707010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 476507598 1250 476506348 476506397
    0x90f080a081515130f060809060a09020105160204060302100f1b2102100510050103051302030d03090503120a0204061101090b0103060902042309010b120a0b190615 72
    0x140d00a402c90122080102103c001d0407203921407015142907283d95074030084803414a40d1100010a40680070031079804000e1160b29072201141d0400d0040d03200ca0b40c0000d00f248074004070320100c02041a541c1c0f055407541c1d031003071000c0c0d41d01074951311141c01d0b0720b0b81c054a200c64903c001000a0500e00d400c1842c2e80c0310700b90200b440d0343e0008584041108050a40d045001954103580c1148203400c4e01c07803618003041c0111400fa0750b16810123000d00c2c2c1410001403c1c3c072001026680103c2c0441c26200068074006120f00041c01c0600e00091000013500e0a00d04601c214006011004070a009020f01059603078020421559552a51541c0c820034404040c240c60700d484025041400d40c2c0d004002140507900700c1d600d5103100400c00102490701c03140245920102c202c16158021440d0104072034058244100c100040d81143e0308103c1003070811519613504a80c0200500040c204404519011030400c0180d0b00350480280510045481d5030070032202060b2000f901000820300144c412481d4145803842 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 476508848 1250 476507598 476507641
    0xf1804061e120f08030c1213020a0803030609011e0306020f0d06080a0b15131503020109120b06061602060d05040b01090903050a032c0106140303090303160204090f080a08 75
    0x18003c507102078803039002d00d0300002c2801c503c6c407204004001c032080f03214100030300c40d0f0101190014600300500511015404e00c0d00030300c0080c0d02c1042842131643c2d54003030b11411a4162504252001a656070325000d05085c0c1d803004080f07500105614102d254a20041c1c4800814017100b0024541c0e1424181e5a51101b010043c0c6810028804a00051820aa40300980300702629a038280100741c0d015808032000c019180d1f0915042e4101441150307480a801002401d02d0080d4000c0388045454031210110041d241510410000a0540b00c122032a03144902d1941c000300b2298660038009254006020210b400f10342d43e03032990b0004140100c4d03e2050481683e0513075035042c14a00d19201c20340c0244006005d04005264a000031100c00000c1048110031154810000c03800b5481e00e0440c030b01503840c042440c0d220382c100384200b075100e45000040d12066900700c2d904c609800e156002141c003c10040d58090681d03080804e912003071050480050036409600d9442800c960360742c07000d600c15a814000c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 476510098 1250 476508848 476508863
    0x21911030c040501060c0b1f151701140402031308221d060405061504080c0f0328170a080103050d08010f050d0201140406081e0103080f1804061e12 65
    0x1a00081f808014034a035200c0113813216928a00000e50901d20030040700d45c4a005a00090b9010301202c96010f030020010102140d0400749550408101d00c90b4240d0b9688401d01542c0d000c0b00182660f040711305c45441e80c5c1c0d040394405a4982410b84001c294100340c80107007280140710340c0c0001c0c01e0f0200304410707401d205100c020504261100d00c200000fa00c0090542039001950b00c441d401c11a078400020002801120000c2011040d1003051000300c4002c1c0002922075007120064003028601c0d280180941103a6070b01280540106203418071001d40400c44448810201045641c901d07504030f0080c0381641e02640c2143c1070a00c06d40300071500c1b25824000e0003c0c403045081d040140e03044c450a0000e565105050011821761741c042e0039403c0f074000d41c4c8000c00058040f030074042c0066001850040c0100d020405003140c0d0b0440c0c8512074148120b5038074680320340c800581c1d980110f0144a0f41c60003140028000d00c0b105c0c0d41e81000700c52035000d1070307114a140200380600098221030b0074849084203911000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 476511348 1250 476510098 476510117
    0xd021207140714010912020d0332060627040501090b0d0201110c0d0c0302010908070b1602060f16290c09030a02090408030f1b030412021911030c04050106 68
    0x296009448500c03003104000d9921755155800007401800e111079484415401480d8010243c813005068490191240e120f04d0300060440f9000103500300381c000b1403042e00c01c014620340c4940c408101203128800203040c41208003031003180104030381011a440545c0032241400640d0300c1d803141c030307007215106c420240d030100c14a0801030040d4007440180e02000034400958801d611102e01142c03403640842811a505421003000340110f40e040355a0101a081950041c02c0359030034401c00f18041d00c034a19007a2a0561030840840071507413a0000c440001a2400c2c034030381c40d00c200400389010061101012981d510382c101c41c1e040d1411500040111400d24801d103504240c58101c0042c04a0780010401500350003800c4854003d81c40d00d240c124042c80c85031042c00d540b890241c43c031600c032040103060858495201c003000600049500280c03070f046038100d0901a00c079088800264644240711013401185480900320300d00f403010900103442c000c07038194291251004502c0030001203800074000c02c008981d42e9013 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 476512598 1250 476511348 476511353
    0x302031e0403021e0a0605010b090337060c1409060f030a0905030f12090a02150a031d07051215011703070618050d020d0e0409170d0212071407 63
    0x3190150000c0c042c1c01940c800580c040005102c0c81c540310034031079950303006000c01d40421401e0f1041c0b90040c820544050300b00410000002c1d2903c03008940072440d0829881100600403904000b156200000011810000340900c1c10320090300e98040540041809a40354460328002441100c0e41043c0040600c0c5c5020007045001025401c007400c1550600e50711007401c40040d070104001e0407120055404545c071505014044050810b00500c0d804550300142e51f0580142c40701040c1d01100c500c143d0306287c8034181888101c0082c14400d00c0d054074440c03c4443e00080c02408100031040d10401c0d119070903580321860240b581c2c4e44441c82401d101014007001000119007a128a100304c02142056a20301041c54980360306030342d400340c140b40303041c004800c42004004081000e041c00034014005404204072004014100c10000e556403402144c0391501a4100052010f1100d820280210003036240c84c402a0341c0e40094000140b45001c0301071241c0407a80543c015100700310b208504c1200f592600401c0d9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 476513848 1250 476512598 476512651
    0x61b08040b0a021006080a290a0c180906050f0105042d120501021305180103030f030e01051008061807120204062d090c0206060603060a0506040f060807030203 70
    0x14091400c50140b580c1c2c03c01040e045008400040503846d0080030700000710b04100c10080c0b810b00802c0700707411148440184020100d134000e6400501020001f0f01c0c21b00850068450019890703007126141203a0501003891041c50f8408000d540c0c081e40c141005045150041d2024411401005c406100340c4062400910a00780100410f01c0069071596840307070340e1260b02940f00c0038441d0031940c694011500184d05841c3d620004010305003202d10091803146091101a03001c1c060001404100c01c004030100c00900030b40100d0b41d2901074800801c1540b0741016040112030042c01074200034000c40010900c2c1d800c61422841d500e49441018005503840c1008200002410315402c9130043e858840001e65032064401d80c03020800b0209111425101c00c0c0950501c500d00d941101402c10700d40249104159400200d01e9844002681c10715941d884003400106103084950219a10040000303000c140e2443c0414404111071064450808030b03191240c05130706a0104440312170760042040802d40100c20768 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 476515098 1250 476513848 476513857
    0x28120201230702090f071b0b04060c18090902030606010314010b0a02070f06020c0a1a091c08041502160605190e0901060215060a140618060a030501061b08040b 70
    0x880360320314001055004c03d964501c11603e40c0c5007042254200a4082c0e040129110210303080c0810103244110f82c0d940718406040a440941400d680d084101c0c4114000c5440c9080c601d04020a803d0241e80c8411140240c00565401c901a014002c0410700740e500a00030309491178420f440a401ea607090a00d241c0c05900074440002c02c41c441c5000c0098000c1c40051884003400180d8082d144040d01c090600800c2031199200100000341103d1000402d008001558202801103c0751070280300301000c104445104141c014003101c100041c00100e540600041c41c002c80850b400f9511081714010380320451060902c200c1c404140104404039221f400000c3c1103082000500385100348600c000041020f031342c426017008026038803041d59010510b088540c074a5008a0885440392801e040a10020054141c3c1c002240a100f01251500401404500c3d16102d00e80c090401070311403020340c0006001d443d01303206100c0826a00818100030040000d49c0380c2e80690070103146885c0c80e2402c28a03551982c030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 476516348 1250 476515098 476515157
    0xf120c031412030a0e1c0206010506090f03010203010602161401051606021201080d0201060b0c0d050a050c06150f010e0d030509010306080f01051501021609110928120201 75
    0x21071074403500071060400035600400d44c60100140000d083d000c010300d81100c200400d1170ba00501c450710510141d00107130f107505545068031400c1d00c502069020541c1019055084d6615500101c008030310180c0c00202c40d800311442031003d0401940d181304c098030840e0103180c0c2c640010030800c4400c80480d00c0020381410507100b0762006107042c03402c40200c20448801e0700000a580c000d0903101d04866424098003000c1c299104505241444800b4110350716910101d842c1c0a002010a040c080940950242c5181d84402c40686026291110b080001106480e0701d142c421400303440940241d511030303907248100c0701c0d000d0090050301c000c68030305030390680042003228109a04c03014041030800041c07043c00d002601c484004034603030510184400d244403258201c1d40c11940102c0d981800c8841c60b041d580200d4207206400603416031000d1a01c170325440303140d004940100d0041d105800d548070000c0c203140006c551f120f05600858586042c10185284a800a8001240014540c0151817010307500c05c200172 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 476517598 1250 476516348 476516353
    0x60609060f07030f1d0f100c08160201020d09030f020415120503070203010c18030b090c1f0e0f0f090c0705120301140306010e0f130203070f0f120c0314 67
    0x1100c0c0d1a51984080401c40014030010803015243d60440b05c403480d40d84044040e80c6081c1e0f1a0000b0480101c02406100c6c400c41c5040c24450703145004540f08410140c026800584d51107584820320042440044200d0040c4114407815000074451100141a20340c80804031450309400d40800000d0805402030345d040b41c1da02680020304c00e11001d040400e2a104201035916034401d40100b40c02c403074000b640c030300c140801c90b6040812141000a00016070741d001c101d82103149c403100d144d18a840c901c00b000c1a00102040c02caa07030241c4018241d1030100c1070558508034803402c40c009110082e540d0003016504103150186d848103c1c90464902c0303038041c0842c40514281300c000e444440c9000f28148900c0398045000005000c148070449842d60000020b03002006694500348580d03c5c2188010000ba005406260101c1c6410710070411245415400070111804144c40d00701a18000011f4816055002c1070b0810020341001c0c21000c20011540060300310207214616201c0035101c0150410410329030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 476518848 1250 476517598 476517607
    0xe1603090501140a0609050c040b030601120615080105030d090b03070c030c060510170102250201110f010510081f050603100f0f0b0103020306031c1205010b030702011b0806060906 79
    0x1200f4074103085101d0009070030085141c40c5040344001c1140d80141004009841c10030003807210b0742042c81106d170860001e00c4c0034403c001161805c50300800b9290084003810018442c04441e2680c0005854141c1d001201038910211200c07400b9654040c6031701c038014010318207000080c80d450203402c03294071860080c1010140070440759100c20440c2c0d0f040361014103000714100c00b84a049952190840030300b4140008510302421942e03481c2411a01c03040c0e802d004501d0f00a45405c6920600032600c22419103412140040c00c004052400b8240440d142010030b48140d600148000c00000c810b280160040b07a02c8024651001540700600700050035650140700b2141041580c00d814450000708000001c400215415011461030a03100444a8141054014000d01c415990040f400010200602c01c2c1040034a090010681d0040481c0042c100c41034034003000022602c041d400114400c24042d40200031412404501000003590304103410b000442030400550340d401c00382c00a0901c0b810040c52607042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 476520098 1250 476518848 476518871
    0x9040608030309070819110607142b020c09010b07112d2704060e0a03030204031a010303050a080c280f0305060f0904020f030a050d090e1603090501 65
    0x355481680c00f846107501035041000410f909012101d8244e04030fa50810b140310607502c4800c0d41c40041c1c5801d0b48a100c1c00903499003006490000041c0c1c201003502510b00d1040e00300740d1081e102e52070303045d00b4002c5c00b01002600d11a501c08280241d0101d401014050a40d00346032503003030700e504810800c851482070200d1203407003a51628035001e40c0c503600414030320090f40324440c41c0101c00c41d0034042c54000d241c03010307400070008140c500e080c0c0c40703683c0300032050b40395612814190060030220f001c1e500c0b14003562000000f856490740081007900e000d4201c15062681035035101d003c03038170240f101a001907418003101130707000e20803410b0310f0b04201d808c2c010074100170441e00c100444042c0c1c05071503a00300c81031100340344085800024001c09018141001c2045107171000202d852034007003020880c031509100002404541c0e42ca041680c0074107019040740c02c02d00e1180781c080e81e15070029407030b0000304200603000a101e142c0d4503152442081d10790322032090300a8888094000e006403100440d120b54880100148 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 476521348 1250 476520098 476520103
    0x30106020d080429100f0608040303022d07020a080703030c080a140a2006011a0903070f151e0207060e030c0907020705040b06122a0304030801050916021209040608 72
    0x8504c0041000f01d100341001240100a401c1d01c1c0e1080c0102e415140c410070490343c01060541c0c2c4280c1600b00940d40d2540c400440110a07450200c42c0040c20303080c01210a03803802c50300544800741c1300750b900351303815600c40c0c2d40a9515440c51000800003440031072294001031f10900903020301c2c3c09905043c0d0b00d01982058513951500f140041c07100007901c0580c04825110001d40e55408441007002400055040c460070450b0109000c1e00b41d462034100080d0540c0689042195000400304070105403400342d152107510620500d80707200c0100141c10003800d14031040c00903902c4442544940c00a0102c0c0d45000815503001c803c07008550350600036012668000d131543c1c01c1c6c880c851003055001d08015800c0c1070070807081325100001c0fa406a441806003101c044c070090b2185030070a101c040d4201101d10362a0310a424181da44000c20303249000442444201600072002c03605031401240c0b58029a614140d0400d107040900d101c4a0040c0d104640d00052809040700801900300c0c06040030810a494400c41071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 476522598 1250 476521348 476521403
    0xb150d06060e06210d0f0203090402030907090e0312010311040b030105070903170c28020d05210309150a0e24070203030f070e06121614030106020d0804 67
    0xb001100e1000801c01c0d02e242000b104403007245101941001441080001d594418408040c1018846040c001541c40c6000300306a03102d401c0d005106543d41e25004104075180c05503441444041c40c01c0c00c3d100c0d150b0301000f1041d5007040303120311030f050711907860358950540c1081408140fa07001b03a6a000c0c131880640702030181a101b042c803622010761851540c41e03e8824044426200d40c4c0158007481800e120203000b0461018890300b00c000782c00320002d08142d4920741c50b91a007000750b0100d03907001d04c44100301000c01c41258424244c00f505100182d064140c0d40b242c80215600180741e00201021224490759038203803904219500c0001840c0c08000c5074107450091402e007105541402d0048040038200d54035549540030b100f910141d821414071024034a00080007130440b8040c803440b80c17114141510760310244d6640c100b0b1140416014105011981410031600311340900042429491118220406d02241d0480c0d049500500b1202013400c030407250039a020300203d5510343c1161240400440307d0314201d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 476523848 1250 476522598 476522609
    0x3030209060d1d06010603200d0e07030f05011b0f0810030b01080c03060c0901050909090a080d0b03010f060e19150602030a17010302010905010c2f030106050a030b150d0606 76
    0xba0044810500e4540c50140145d01200c00c15040429518203042380004140003401c50744542303916a210101010003400130f81c000c8007424890351500105020f00d158070703101160b0007003000300000d01868854500140240d071414002c14035620142c000705120f158042d40c03000d0301c2a1a00070710b40c1c0389d40c3e5600081e00c080e0f12a694961107134015281c41d24051000d03075002001c003001189004c1e91200060054060030444a108200c01c400040c0710000501c4040d80107036103c60065640c02d1900050030007007512511403070183d0f11300038401c02c0c041554402c81d419503c82d0020781300e41d9038505048050010080c1200710116803581c0c4002c29440482c0b124401900b4590099074503664107140c020110b14045803881c00200c0e500d0010030150741c000c0d2210b03054560a01c0e20610b2400c0f80e04004c03001c07020400c00c41c038841e9011202107900c00c01d200e02d548810340c4110024000c071544d440400160604900028180c0700000c80807034035210351a8040c6a03c000c025140307106243d001d0f11004101e40b10783d41700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 476525098 1250 476523848 476523881
    0x3051e0c2209180f021012020a080a06050d0c03110103021314040b06030408070602030411060c0c01140a090b09010e33160f1b080312010f06050703030209060d 70
    0x2d115012150045104a61540a4400641d50541c60b15444004d2065010340554141c4400d4805984182d1003606820b146002c295520015240002c02015080b100000c000d45480004501d40c60140d108403841034026500b075104a0550300e950100e208020300301418140c0c200a110701111070400000000c10700c00e4a5101072034014000d0109403030f000e00065128000410820001416502c00c1c3c0d010207030015401070f104d65681c50105010303141d03112055807111000c113059075448070009404180b102c0030781c5c0d9180d002c00210000b011a000b000d404c080070980e10181480440918006401c3d100c4051601d0006444070301e02242900b103042c001c9420300003485c400341d400c4144400c0c81170900d0412458003440d0400a100541c00c2d45841c1000401c0c01000e1120313182401881c5040100b006840d01c0150f900f80d55403085140c1d00e500807202c4aa242400800004503480c1d8000564101c0b40a0f4841e58a0036115680843c001d501400c81203622580520095100d8000341c403624411100a103030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 476526348 1250 476525098 476525167
    0x71b1413061d01031b0b0a0e030106090212040c060f020c01141b070614040b16030c020405070903060e0a0c0506031305010204060903061d07170f060a0c0f03051e0c 72
    0x45c4140f0607101d0824801030031150b0801007109400c0f203400c94030340040d07914120f400c40d0780352400a1301605040d44600d582e0f50000c6146440c08280c1081e00c1c0c0210320501260103c640d8a1600791070700b2255603c14400b40e00040d510b00090350182c0990351001594030007252070450400a41e000f8029040500c0c4101e5006190600031f082d040644480120b99060b5410306040c60001041302c1f82c86104000b00c65103d004c001c18007058040d6038101d0785140d000700103101600c0c103460001c0c249070386480240c4106040c440c808400c0c2101054079914aa080700d6042000360404090000070b901c080c08841400a2122408022170350a1010b800942401e50304d6511080c5141050019111442480903200b010480d09002d40c40d80015018200e49141c5900340150520004450611080341005042d6015400070030086c4032040d07220004081c07443c4c07030b805501820f4000450440383d045640c60721a203044c203000e414544043d510301c4d03030000c8802c88652905100841034541503e144080d440d0348000301c04d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 476527598 1250 476526348 476526353
    0x605061b1911101701140d050703030201051e0105130e0f10060302101106011401020c0904110414101829011d060306060a0c0b010b071b1413061d0103 66
    0xb0f070703101240e0304034500b81d480199803010600015406205440c1303c201041c88039012511541428040c0c139030801c043d03c5103160741c0e01300680a4001155003520181481c2c44d24a480071154003103074161103001c0c1c034041c101000148420010040c05d40c20204510624219100030142003000c0d0341085245a40881e500740b0390300c10710a40b11050381c0d0090a00207042611a041d40001440d1811500c100740040680155540181d0414212000c5c2079003085442c4100000d00441a05118051506480c100404041c2c85640700840405031156080c1004075201000301003880d40001060341402100080c11240005103541d00c03c49507070200d0380c8660610101d403d81e41e00844d02e0310a03451041e180d000c4042080001611a1000500041c4512000328260700e91a226401070181d00d507104004c01d8686d6110700b9041c07001c0e00b04040841c3c0001c40e6000302c0d5042c20b440c0c0c070354004a0340f440d00c044040020b09000c0007016580b2511640015984d90b000041c10720701d004180000c1040455100501e50460 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 476528848 1250 476527598 476527609
    0x30606060207060503091903051e09100e0a06031a0909010e0c0a26030f1605120f070305160501021605070807080303160912060605040507030605061b1911 68
    0xf5030001040c0201030040010040c000700d20140c0306401c0c0700146c03020061a02c1c0c02d80741c3e4001da400c05c13540e12085503050f501c401c3d086c034010a8484400c4840a403d111607440865643e443d0140c9543c200301064410031007a4000c0e04210038418054001ca01300900c03400200b8079500007140d1224450b034590600402201d001d01400d1182071050314048205400c1200103055520382c001c0341480c0d0324640c0c60b80c880107441842556141c10034043c44030b5540e0006016074001c00e04d050000c0c0d40502400c3c4071070343c6002c246c00c211a0b00c0454140c40600b05401e584007550b054105041042041524502c0800020003e2004108400320582c0c0030450f00000e0038014071305546a0015542680b1082080c801c0500000544e80e1100d235120b101045148542c0f81200c100e8071651000682d0038100701c1080c10409203030455401e440b01698100304c5542c82a400303c095818500c03445801038030402880444072124034400034051885800c440070507603440c1941501c0c04480e18140c03110051038020144501d4030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 476530098 1250 476528848 476528863
    0xc030605040c0c12050a05090604150f02070602060a05040602070611040f051801090b0105070c0b0a034706030f06030601060908030a050904060b0a0903110a0b040b16020a0306060602 80
    0x5510f04480311250310354410751441ca00510403014030101240d40420b56104804503001080040c180c22303204d0341e4806100000b0a1800001c1d00416507000031100c869100040040c00c0b1600e56000b490aa202c480c8000700505c406041611001d40801016020802d2405080d140d81c6155101d165154a40b40f904e5480112681240d44160281241a403075034510f00e40050659108110015007000c02c5070040c0c4062040e0030006052200684001401e1076a00c0c019198403a1261018001204140300b0f00300000841d84640018001c104408120303130360401741c134000155081070390590302c4000360001041500100c6420300c506103042d041003003c2c141481080e0044c0341c81c4c14840d920b1414014503c0d22806051059410048040b817152034542d42d9030010320042400100c52540e80c124100010500d2125000a8407941e1080b008a691800e1080c100c408440405c602141801d04126155850364030080d0204540c10302030a440d005a41e817620310030015403141e003000599501d003880c041e041086e07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 476531348 1250 476530098 476530121
    0x70c0b09062e051504210516121403250c090510061805090c0c012d02070809090907060f020601120b0a0f020d0b031908040b0a030b040c03060504 64
    0x42c0c9042400b21103041005a1094a20495051202400074601c1321528045c5502c18410941805000d20745044650a1038a40d9801002581c0c1448141180b50003494000e200303d41259941844540205192018503c0c251003030b8000d1b41e140609001203000d400035808510404659204c03a140304000d550062200100b228100a00651921024801e0020300a01c070707032400e00041d20301c40c42440140320080c00103450002c01c1142039003800b6070014590f0300105000c109561038401d2a0742240482114800c1c20701c06150711494000e000fa51900194000c003600703d031210300c05c1c031a0040130b580390b1410521604a640042c010070b4600a4001c0080b0b44000300c9206540000d401880b1807030740c0110b007008464010010076525298100b240c4001c2680046500f40c440c8045840d031011002604003200d1200c044040b0384050502e035800804011031140e00a245000810081181034854409000804090308002846140f03c401060641ea21140d00300000703551104127004520f01440f40045004c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 476532598 1250 476531348 476531401
    0x9050111070e1b092d0d050304060c051518060f07051602130f1b022404031116170c0a06080a0221090f0312040b070c0b0906 55
    0xc0c07030102029200300001c0c10381c00c1c9003021080d20b000100c0072401110001a8050441c401700151120407032424134184072031202006103007403640113a15000a8042d007094001d4083c525091804905071001c4c60103640c200c401d40920040a0f00f01d20fa0b08072020b00c41c20807505844142403005941604080d401084141c0d0b91842034280402142e0000507600c0460190254048080040c000155041c24070720060482508103220302848174041e8200b004020f80200c50b44c03981c20390104043e40c8410711840050100d48010103422006c81010040d650010b001c0e00348458409200141c1c0da0800c06400048814110000002c0192400700540e001c03c6440150140c6003075044207000520b1010948143c0003000ac3c804042282c000c1d895040ba0303440c043c804034101c0f400c04c00c41150403059004171402000e84c0940d8410403082c1e0300103c02c40b20307135255881c107400481c1e580e540e40c1c502c90400900601c04005662602e00300160303248040b18010300f50303080103200f54030745070101901c1810b62049461039038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 476533848 1250 476532598 476532613
    0x30c0503010602060f0c071b0321120f1d0a0201020c1008060d03020c0d0615060e010c080a02070b122e03060b040b030a03090e100311060a180609050111 67
    0x4035400304c0c940743c20000050724080c00340c6420621605a0182d0040030302030004034250040c55030840c00d0050101ca04c00d24980b0310f42043c610410082640d94400c10300451401c24901d05129030940c003152500b04007100002c2c007801d0f401c04140902c000242003503041d602c5104180b00b990303010130009908031030403111606920644000100500b42c0500414020802d480a40c020180240b100c40c0c20f01601601c0b1007507591450801c00c018058a0150304007540740000003003295032040c031442c41a11010f8461044055040da1035061582c400b440510460191001c08038503102100e000300170800b40900002041d042c00042043c00501d580c60f10040701b080f0741d82d403082e083c050304400d40441e46c1240b00020401000030124025200c4566a83da140c064613818900709a001030102041d561400358860f101c4d6103284001508142382d00010307180f10007541400603113140c01c0009048004071031230f0010001c40400c02443c0001d03826000003000c0fa06072042070015580c0f01400b8800b0901340401032001c3d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 476535098 1250 476533848 476533859
    0xf050d03050a08090c030f030703080f07081b070f0308060301051825030c060f0219020102101a0a0f05030d05030f0417040803030430020c060d0b0301050406090201030c050301 77
    0x4a100ea82040c034140301d900e030009181d00c501409030b545d03c1038020b0b00352951841981405601c0390b110000860200306003101242c0c48000307010340a84183c2281d200c0e850b1945801041155841080b00402c059100800c0b01a002803190088407500d544a602d49035007600b0200c08140c03d4030001040c80c255600041820794a03000005120300448100e4900c0e000d0030802d01c3c0401304c0c4801190070140440c03000074400a0780c99480031010910002c00e40c240c440014001c404408080c0c10b500010703006902510303461034070305d007158002e4600c50303d01140f40c03030f442e4003500c0400c00c00350099020144403a924042042a800c05000f0031f84a859140b60140c0380d880c0404520180704800b820141040307109030b481d00c1d16100440c085401410441c8101d030b072289450f141058000841d003528074400071004103618200b480300c8909075050310b4260058903004c860070081c84042e41000003243c40c801d45960028401d51428481e050103180505000305500000c3e000250640b4503100c5404100a0108010000b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 476536348 1250 476535098 476535107
    0x2062118030733050c0a020d2615100309020405130b0406090201030905060f0115210c0e0a0e1506130e090a0204020a02151f1205120703090f050d03 65
    0x584004643c807603c2c4103c030140d51204500d20b2000380b4844103281c0b0382407151201c2298050018210180e0890340d50018420046030f045440505121b80c0ca0341995208103403106680320390394000c45400303060601c5017024001800403200c0f040c405001c241e4440c658029801d0500a480d803007150389840450b03103c0c09503103040440c0130050000e0000340c1c2c0c030040c110071688a500001d50a43d0018200c1d4041c2c1081c8100c071541010038403c8000c80300741087ca00d010140145140070b0391301c0726603100c9210380a4404210014020714440031080140d0240c4840c0d0369521814940d0142520202000107850101842c850507003031005514810300b000c0c01307200b001e00300d03866810058480c9504480360741e49540c2c010a2810006403402540a80042801c0380b21550004000c0007440102c0200812a1201d007071060b0640700c0c000500815402c5814180400d01200071105080c0344154102c03446844040280d8880380c00ca44011030026aa840d010010400e5030b22442010b41402c44500d80c820b010f9503130240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 476537598 1250 476536348 476536373
    0xf07050414030109060617010b040b060f09040b060a0f03060e04081605070906030b19050439080105010e070e030d03090f05120a18030c12020621180307 67
    0x1150706040c0203464903161403e40041d060680e002e1428044903444410980c410030300313038407001100d40c41c2c00302e2402546020302400e410200c01801e20303031604000450945040d44907035641c0d03801549501011020391642c800500d015074140e0707110860301c50840001829104070f030f44485412003140301844003140c50901107070a2101c4131041440000d50528040d170502840f54051030900d41740004c008103100158000a1140b00801c8540c5180c01400010800b110070540380038102070184ca051003448580700040e000701d403504500107540485c0c0190002c0c1e40c241513030420142070351103130010000b0f5648900000d13000b0030b060900400103990754000c42e0b0703076400034601502050740b90012141802402d115180b11181c02c0001c3e201c103903803203048600c0c40d40c1c0f00c004000009a8003545901c00c8074a815114000c0d240d004800702c007224640780704280c8001c00841c050740d10440070003115500e034014a0180003484009007500c6018a0840c3e404a15145065010b207100e810420550700044d0008a500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 476538848 1250 476537598 476537609
    0x2070507081b0922140f0106030b01050306040c0b0a170c040e090a0302152706061c05060114060f03040f0b0708070e090c090a060c1106040506030103150f1b02060f070504 75
    0x4050104908007001d001c0301c0d901002005021b40c500c0b03043d40c586c040d006034040d07902070305000c0c0e46a60b8071400e0503500c1008817809040c007110000b007800f40002400050940000900c1d0280c40300300f01e61440342c00184144d40d074000d5600002001c121b5140450a11588004987d0181481c110651000380d254007203014181c105115040010740903d49071884404442d1301e103521400d034110000c1141d550f40d042550964440d0341c5410030b1506101d408010840c3c2c1d0390340300c800751109900c0d0000d00c0d442c045004403c0d039400340c42400315010404062000e18411405801854262940c6040500303107000064049410441010308000541d41c00264030342d006903040c0c40070b84280e13442c25212107060140b2005a64000640ba900158050b40101003c450f140a10f02c6c9102403002e41040100600c036031310419030040000d000400119000501c0c410000e42d52440105114000749011411100010b1501e44105409011001c5460b030401146034003070416900c0110310709050704098458043c0d840750 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 476540098 1250 476538848 476538901
    0x60d060f110703050c0f010b151e0f0403033b010e0307170c06070b010302060706110310150305150d02120712122604020402070507081b09 61
    0x49800804a07030300045401101d107580540310700ea00c3c94000c2c41e82e8482d200700d078898404c007402c01c0c060300010b1182c401102c0c8000c0030110703016002062200140c00c80d11072500100440005029000622030003010035062007014180c0d00c904520340a460b03010400c81034002002209600607140250710000f00407850540130f0450030800a50040354601a0340459070380602440c0000207128601450503030100312500150b46151405405101e014007611001070880300d8807a00401c094105100184001405506e01090900302190062103985c0b043c1c0d041310f03085946a2042011615105070100800e10a107014441418411214100308881a094900c40d003403010041085680300001040f06240072000c0e90b140958070315200700c3d07103000381c001680e800000c4880403503203d101342c4bd20280c411080321021988420000d40c000141d00060040360843e0382002058085503042100100a10401c401803480c0c03141480b4200c100d00c1868410380c059254803080c40300300118890181ca01e004500003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 476541348 1250 476540098 476540111
    0xe0309130b0609120f1027020d080310030614070909140a02031302031b011707080109020f0f03100302120a150c18030b01091413020f060c030a030905010b0603060d06 73
    0x1159805c0c20403080e603c030f140b80308150080d04103100e180c000c403a0300b01d05140100b001b0304a40048002c00810964020340c040c2ca084a00000211190081c40d009030708054000c60440e244e0380d520782140e061904041c2d07052084001c1165081c0e21500301c20250014403c02d20807500180c5006480d040050700d051100b0b42c0200004440d03440559001c010660014216004100014601c00040e05101d9407180041c0d802c41d500b01a16649182d030502500070342d07980f11003507031810114000941041c248881c680c0410004600c20300f101c80055401940c0d034500e00380b102881d500c100035058190101240940d080210301002040340c510740c048841551400c003040301c180005013182c01d03c13000014010181e00c000c4000c4140001139001506860440380108112615001c05603c10542100d001c001002c841c12004e005041924031384001a0010303080d181070a501055032410b40d04030481190019aa540210b018070030b003405503d2101c0d2094842d07038a10700b4038001203940b2003035060024009035240e86 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 476542598 1250 476541348 476541379
    0x16030f020f0102120f03060f2209030c060903021024050105031305010c0804060e160513060f08011a1c03180305011805060f0702030d0c0e040e0309130b0609 69
    0x19410f481c140302c0e1980e42d52041043c0c00c05940384c0094404500801400e062441da03812701036600c100c89891225030341410031900f468100039051a200840070442c00c240d41c040003070344074000d100074944260007800402c982005090704540702034000d00c100c0345014842d00034502c003001c03441007905c9080c81c103960780703607102903500396150a07502c40100343e5840c11908680156011040c140114800c9206101020100c00d6440d036031000c1901d040500513100c0401c01035413412103041c0031400c1422001251140c2c0d01d8000020301101540108140d945522103981d108a801034030340c0e94040121000b0b84090550040c00280b510100e40040c18411100030a5040041c04003110b00115404002404502185111482d240c1d1002c80e08483d18070654001c00e6500b00e0148403540714000075801541841c2c1c46002020280c0b40c059061003d0002254007049591258000c01c01d44081000055546410140600035a14040380301c04124038904000d0904659501048406101c400c543c00b0b4910032004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 476543848 1250 476542598 476542603
    0x20a0902160507090501030b1b040e060d02120d09051f030b06070f060c1e170a061e0608180307030c02010e040f0b09070203040302030c060d0e0a050102030916030f020f0102 76
    0x1d08000e00380703118030344000600c201150004d9060300c0c810404410306e0b460341d0000066840c444520720364501001d01c42805900080c0110640c0f00800030400203081500703401080c02e0a00e2300c440450107411801034074842c00c1e0461003400c02031a080c0c400800da00703a0b0250f00000c2c6003650120404050b02d41d40c042038240c1e94070040d54445504400c000303007841c3c0946004001003010700e002501180010100b40006603007600e00401504894407220a15111148114011480102480080c0317aa0325030118001105081c0ba502111000c0c5511580b542041d401078812400140110905014241e90741c4501ca00442a10030182c0e141c2090000d180c5a03200503100d0800d43d0040941051405100b2a07040450360458086001c090b5800203ca445c0d5182c02c980b03920850001a40603445035070701003014240700c001002c0705000e101001038501e90f807901650410f000113200b950541e401109104420704240074030440030f4458590903408030303e943d54114004003c030740301920410b030a08035011203074000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 476545098 1250 476543848 476543887
    0x61005040305031b07090e0a1203181401050c1e0d0f020f190908030412080c0d020d0909140109091a070203040f05030303070c08030403052b05090604020a0902 70
    0xb14003030301e0f240c0e0681d01c40482030840c0d0b5800f1084c00e10a03418001465041d41c411484001d100c180608107070101178540303100c00c0c018100304400b05031392020341c3c0180001c400d8021003114030600c0c213403200c9a8802200c9095030b0713020707020740c1e240c9400300038207010300e64210620042683e40002064a840c0100b00090041003071014802049000040c1d141300341c0e5111000b04030401088204106401036254110394039011401a10340341d50040100340861070414040d203000d181f00e80c9600d0b192800e0303600401d061500003034101c1c0140e40540d580780c41e2950491034030780140030080030400011015130690382031041c040c82203c072240e44e604400350500c4030712b080410704284001d40c50300e23984c104140b00030b69a40c0107104003c00c1d404d1030100800e1518011045034021030f2a581c0c4d03c2d0724203d2a48802200394006401101400001c02c10102c0c2c1c00004000c05a5000018800e80c01030407960100c0790a5810041440e005174002c0300c200001680c07106c10751400d5440c500350040e12624281c0c035107480f0211 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 476546348 1250 476545098 476545103
    0x1205010b0702122506270522140103140309010507021e0d0321020f040501030b0a0f091a01020a2d02120d02070f0f03020603101805040b0115080610050403 68
    0x1100c20080204c81e6600b500c1040b1201e980da00d51140411400b1340c0c0c2c1c0a804002d82140500c4601c000700064600103100c6205002030080050034800030010b15011149441d00022102c09004010401d002102a00c141001941c03c00f641ca45210100001c280781b0409078000d205191003008042c4104c1c600e601c5190200001e09807000f08200c0b0b0801403c40f12703000400418544054989142c944014000d44a0aa22403c031041c1003a00b03210041d8054500b5103000c03500484880c400081500d0040c3c0e01200501c080200024841202c0385030483d4401d6040e441c0b815984079122000011750038500201221190751820b0f4024140100840c42c581660440a0342c841c11001845124450214071601502c1a42e004c8421041d5241003074410380d0104c0c46941c422014400041002d07042c19030040d5402045840fa62000303d80301c02020320f012889400c008122969a801c001c20001140402800740240300141620140303540001040000028240e03801104450180758160b4059030554000c1c65 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 476547598 1250 476546348 476546383
    0x1031b051c0207060f1e090209040f02010513060804030f0c0809041e020f12060d1a0403050d050112020103110f0d0e0a0b1807060810170a08040b04061205010b070212 73
    0x3100d120101c1d001e04440d60100d0003113502511b007501040c0c950304c107440106a01914650460b6207548038410701c03403070141c1b0903410300004000b015842400c8011010280203d51128407031750400e03040050074500c0c00d10303480f428000d03c10100408034880f803082e103040b41e4040ba0041100c003105209401000c200b0784012044600205030070b5030358020306014006074400004070070896507550080050f407801c401c4010b0710700c110700c545c4100010782c410344c0c455009011741092860500c1084008003143c000741d1200b40c200b200800220110b40c0e0502440882c030360f94000460403c1d000780d111365030341d1091420000300b1a9545007041c03100b00042c401e000003a03410010841c1c0c90700d807000341c038950742c408010354039078a000e101d07000719075203000b940071038003034074100c04441c010505104200720a00c0040800200c0e41c401e03204040700140f050001007000c0c0180c0040aa10b4034070340040074007a80080784a02c3d4040342010018842a10f072001a202001d80481e04100e213544501c0c20a82408580d074000308080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 476548848 1250 476547598 476547611
    0xe01090f06080d021e0c01140a0e0a030807150b031e071208030f09030705060606070201020f0d030e071406071205160c0501110d020c0405090708031801031b051c020706 74
    0xf1500883d600100c0340540c00728185616144402c1a1200400c40300c40d404100e84500007640b14610001606520358181440d5503c030712107100081400f01198803c072003440000580340e0800c214002c030580e00d495040414402c0300c060301c00113074851161822035109118900d1040e00f02420400070385005102c1c451030881c1300e01140c2404446070f40100c030781060100c0c44101151031604000300710380c40503030014041c183c0b580b107550030044140d01a20042c2c0c11071180566101140d1024010186031809548001807004541c8040b2401c0c0049544000b180180225031001191034040840d411168040300b981243e5007220800d0710a8000c1c00e54800e4800e1289244d4001c002c0c0034480081a501c0988882c1c070b003090004001507482840d140f0280060700075481d1490742c1e05154100c0c681103622841500c00d03603501c46061501c0e41d0400c1c42d0b441d103440030940200d480d658061064070300001401d194502c1440103484080d00c184103000e200480c0364440311120304039885507410740310316551280050240307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 476550098 1250 476548848 476548873
    0xc0901030f06261b040b060c03030f09010b030a03020703170c03210f010501120903110d02060109140108030406052b09021e0d02010e031c081006090e01090f0608 71
    0x50700f42c0c500902031465148020000b180000040c003260011850308600c00c8000644e0031300c0003808140074403d402103400d004c031052416080c00514840c1e0004181d0007d0340c40c10780180e900b50344450794000c0c000e8103d46c1d08000801e40c00f00300e9800b501e80120b0010300343c21040e4001d190b94481e086941c4c0d401e000200fa002c91142d21723200700c0d003040d5800240d0640c40e515403080700306460741300f0712803103000c41c084041440d07031400c071504140b081034000d0416031104800c030780809041c140200b5440006030041e100501107100c06228038a02c02203000708040396036041c00341c00c40c1d40344110300030507003031107004a81403075400d004210022040030002000000ea0202400c002c0160001240891140c6044074400040c12a02405649080c4008181d03500300c641940065404c03110072010250940121901960109035490301d48008140b640d030340031044e1600b902c4a10a401050f0049005c0200103241004031401d4503070300ea41586c1003040700041d031030704c640c04941c002c0c02c060340f19107003a01070665850342 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 476551348 1250 476550098 476550119
    0xc01050f1e07050307110a060f0f1503030e28060c1a090c01180314060610031a15071502180406081b011407060f0f140c0901030f06 58
    0x240c000700121050225411144448844044606200084081c400102440d01c2561400e10307240c1c070f100130340c4c151510b20307100c040a480030108030700c22242d100c150031416441c803489200300e0003410b003d00d4081e290444d6001446071144c0c03400640f01d0b0320310241c0c203040380c0000b121071006000049004601140d0b6074802402c84200c00318107440c010180021151680c0e0541440c0340304210201c042c201d210a01001510a811040d811100c1403049400200003e0030f55514451b10f0f609801c0240311a01d41841008191084d080f4031008150030701458104038506500000a14032044400d51401809200010014002d8140182051540b16800445034003141d0003440540301060a55400004200921003039451500c82c8428036807010b4445281c10f40d42d002007d840800503d491200c5004505d202c3c142a00104400d032400c580c1c0d07034828420b0005901ca9a0101552180140030b014422040011800c10091000040c500001030002d0180c3c480c1c0e0189055880d042c80070050319031103040140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 476552598 1250 476551348 476551351
    0x3060a09140a06060f02070312090b0304050304030506090a03081504020f0a0c1101140d020f0f07051014011203200a0501090c08120301091104050a032916050304080c01050f 76
    0x650b01c619010010400500c10740313042505036010740081a40900c0e43da20010143d2803100100c0400c2056040420003113600c100031406140200021621903086040503404c180003e00b014229600c040312030800603410040450703001d40758818180134201e00340040350180c440c030369103020341c0e074400a42000c1c0c4903002080400c115000b01c1090503020034841c01500d1064103952100c820000a00003245960340b04c2c0c004144d0307103590f03d00603030811203511055200d82e0404401141d06411442d100082802c9520401f042e02c0132054040c0e15951520041c100c4002d00d8540150401ca0341554030342104188017800e07088914040300707e03a805651030400c680201181c103412560200211000150824001508003444810101603491a442d0256000082c1204940c541110a060000045507580c0548480007075025060300c80c0001d84c0a03d540303000a000344400034540c4854818000080c40e400381c2c039408401d0a091640d80c9848074101020103009041ca0141951700308800c1001c1030701e076120040d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 476553848 1250 476552598 476552611
    0xe0403030e01110f0706050405070f0b0309060f04030909150e01090204050f1818121b1006140d0204020f070c030311011a060f0d060b0a110303010e0c03060a0914 71
    0x20000041201081c540a2083c4107844c00181c500348001d2000c1a03c80d8800e94201d4480c100b00d84e0b45903a0f400041c400345400d98803208000700702000b0030030603c3e0140304a03688180c42071420f4402e881d0560b405010051113006000020b0703074409001888200c4503000102504c0180054182507a480a1501c060f40c050f02440e07001d00c00010f6101c1042c00d04d01a0440020301c0d6403403290342c994481e60060005400e01080c0d4800384106503000342c44c005000010f000d92000320300c45040c40d40e113900403141307003030300da121804422850b043c01040201060200d500d640e500458040c5016916070000a001e80a00e0a0302044140e0019000c0d0400c00e4806048085034400e45030b80d400258882e09040c00c940340070a00e0000c461040e18203004a1609100074052a035146400d94284080194540d08071003140c1c0112502d40c000007082c21206411104641584d403050005624540c140401482c554030060400c061040d80131000c222a40d80d0710400401402440000700300f020344103500c0c60950340054840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 476555098 1250 476553848 476553851
    0x70f0b3108010c090506030c120405100203070801300602030c0715020703140c0601050f0409060e011d0d0512070918090213020304081621020307020301050a06080a110301060e0403030e01 82
    0x3520706011b4203581c8254106030b10103040200304401840d840f00e00801c02c032040d015080494020203018409507002e20442d980d8100701e50b04244030500c0c02c035181c0000c1d40007241181030005480f040e5869080e506544400d016072071391030300d0290741c0c107030b0181c0100140411000082c0f82c1c0303074068950242c0b0750b0318003942d2107070041409401e500c078451180c0481c40354250801c40c0180910f00f0003862140725130f07a0260000071580c1c2c0c2900c44904985804188003007694440f180c22900b45c8688400d1001d202c01c100143c42c0304204c0041c0070b001d51042c82d0044840400b0700340010449806004032030010034a40c1420142480510300540c01031144ca40103c0c4241c40303002ea5076460700707854800c1c1e91043c0d9000c21002d107071190404641064520311030b4110f0b420350300320403031070503e800c14030000300507201680045465201078070415003134982c01400601d001c1c0c5000d50401944c0d07800544a0382c210382005203420794225840c080f9001d04895048180780c00c204c1e0050004241d419448003500b8800c4800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 476556348 1250 476555098 476555117
    0x80a11120703050f100603020109060e0a0f0b0304050f01020903030409180c1d16080c070f080c030903010b04020711330309010c02010912180306050a0b03070f0b3108010c 75
    0x1c5d00c11180d4901019000074030400e010b10009020350303415205030304001c050340409651502c4c02581403e00c0d402040740d03190084140310822804114901c1540700903c02981003210000100b81d581c02248a09080c00e034549442035805200070101003422a0030009440801d62114040c4900c2c0320601190b42d101458000002d088104034028642d03000364603034a0003001e4031001104417490f0000c1070217540c810360540c20030001404010003402402c00e00b41c061512007000e14109400c6a0105594034022401085a034000541c1c0200b02c001d440030072141824610007583d504800c40701c048542180030941c0e82c01c1c803210154100003441c40340300040020b00503445c100b0340032030990340c80c0f81c0c1c01811402301031a80351415000d0205940d810398805120f9610a42c2c80d205e18040e0f800c02e13220383d018160b41d400c018038641000d03c41200070b0211000318061041c0380c030700380c0080c0d44502080345602c2c41d001c000114080c000500d6481440801000b22040603449a12040c000c040f004031500c0464018503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 476557598 1250 476556348 476556373
    0x8060c030f0c0a031d0d02010614030c1012020a0305040b0604020c0c01030209011206030c030201080c0c10050703020c010e0601090615080c0d020f120a060906080a11120703050f 78
    0x10840703124020aa010316000d0300c4019009240340c21055502040c19164109080c100004142200c0d064803030300300920a01c0c0004a01908445580e000aa5100c030413009072129a00c00040842804130255001d20380c06407003990440d46c5001800614030303210b0001813190300c1c90394503170060750241c0e01601c51019a91034840030003007240308641c0e4100c000c1d017203800c030510f03a5070181e400390001200604012105100c08042c03101212415001160461003900040c0150b580c00140b00e98000341000340d0518215107030400759581c0d80c01d2010541031a0b00c41e00000c0000b0b1090b0103aa60000850740240107034581030610989410382406215041881d00c400050f80000240740c400181c032581d141c031600e0341c4aa01048010358420b0360081ea00f550200542d081003a480c400404d80c1e090354a40a005500b0300b01610402d40b002d0f41e001380404c600b412011710024a000c921603080d5a48000105206070010b404144d8000641c3c5880d101406004800014401c1c00b04901146141c91800d40d4008007915 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 476558848 1250 476557598 476557621
    0x105100e060108040609110a06021b04020c06010b1303060606050a1e0f05210c0a1202071e020301140703020c060a09080702010f0e03030a0306030b061815061b070806 73
    0xc440850005403100f000c0341c041075603035010b10700160080c02241d42c0c00c1c50103c04100e120110b0303845600140e00203048111350340c2e011020148444070847c0c00b545040700b41e0a515907a40c0c41070080d860084000a190440d0f130784a80c1c038200c0210b1b440700d03050140700e5a910029000380c01ca104218081811022141c91060700940c8221380c0420310785070300342041685041114150040e460b8007800e04041c04c440780840e96066800b62080740c03800c170002d554000d1200001c004451020f500c8d0307000b60050110000254510102840005a480701000300e070342035000007030160090920b41d107140c4a444040c4582c4507850b400519201e0005000c079000c50702c905020608603804101c029003040000d215180041d80301e0b00c01c001e03022500d403904800800c6003c0009040d07920030140040800d95518041003000040e0309095406202101c20900c8069165400c084e4904002c110140440b607500c0258200da840f00300740c42407001c0520040303480703102403440c450340e441c0c250280658521580c000a410001c56 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 476560098 1250 476558848 476558851
    0x403081b030a11090406080a03021603110d050a0c0905010f0512070902090a17063106022104060209090f040519141f051308090d050c120105100e 64
    0x51a100350300e507649882881c0000c2c103004030b0030300c6501010001e4070040e580d68000e141c00381100b180605030801180c6806460105181c3e04241c00e1848600104007040180e07404400c0d454055944c034a80c03c1c0302d490041e0804400040c010400500044c0108015400740d00c030310305a0380c044500080c07035912031040000f0008140c0035000158007162051014050503000f400200c1d1000d440d1140307a940fa04008402c9800216050354240d00c440100000c440b011416800c0003403c4000100c29901d01449250b44440c41d0080030f49403540000f9030403018003c1c8022a00420300354941c200090400b490594041c1d480100424400e081000c00704444201c110348103406a644103000f40800c10500d4100a516090104181c078403a0380c2c1c00390080c40810900c10303410010f041d03040d1711030b044c2000d140180403580b002d81080441490307888404005000d40c411038407180780072600026202c0c1d681c079250307250107810f0022540110050703c2c0b003d01105c054000134011b001034040b80003150340300e0002d100d00f10340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 476561348 1250 476560098 476560141
    0x80f03130311010c080f0c0c0609030a030f1812050c04020c100b131e0507030605150706020405100c050609030a09030816020301020f070203070b070b010b0a2303040308 74
    0x56115081000842c201c0e00310390103a8060504440c402410303282c90381c039500000c24001c15a031001513101c840d04024044202c21201c100c030b600741030226040200c0d580b60540780c4018140040004606075117805085003000b0503803070706d841100003500e1b800e004003a6880354504070b0341440754030303070782c264a24060003622021070b851030003041c000e1104130881014191b505103141d004105c0c4185101110130b54007030701d0151102d48013010900c100b05c200a00807950003e0045c410140741100611043e07540103940038a121601c1e081507110f49550030860000d104d80e43c4603a90111038a07030080500794200210540f0180140103071009036491a03901d68483c41440104400503c1c101818400295030001401d80d0358512140400c0700c41c02903004c44d0880c2e01000c031411040802040d00d00071481c0030000303400036080040000b4104100c0b039492103400340040c06151560700011980100381449a50140706148032468440801000c89001300603944c02620241c00003101400004c0e03242000100e400740991 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 476562598 1250 476561348 476561377
    0x1d01030b0c0d0908191206030203060a15050a140a090c021f02070b100801060b070f030503061206010905070e0609011d0a0302061903060e09030306010804020109051801080f03 77
    0xc0d510307185650710ba4040d800c4403000343c0d501c10383c882c04030b20818040c2c6030078040070905440740c186582d40500741d04201200c1800315428180184016140030440641000600f0b03000700714201400c941000c8010380e5040141c010402850020f010700d60140340400309034007540e0000c0c8c41e0351100801c0c0140c17030550386483d026034848000c5403040f451081d094844241c8414006007003622582e80c01e0140c0d0029213442114100300708007440001c000384251002000b001e0200303841c104042d541d070403140c00d070440301905111000c0005a89a11110040842c07403581900342c4061b581c548031032500400c2c050380c84000080c918010300d992400d1400844e11145016115400040700f0141c511464160800302190014442d00340000181c6941d4040c0c0f000d00f13100e160507101c002403070500504585095103e80f600e810b58006111034050044203c83d0418002c1c0303001802650b82d40010f0f200c40b55640e0005402091020b016058100304030001810b80d09400160b44810444803001c640c1e9000c2c1051082a84 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 476563848 1250 476562598 476562601
    0x100608010326120105032a042403030804030806010906050d0e071203031b050403030909050915042306061008090a0c06260c0d0203070e0a08071d01030b 67
    0x1d40200c0000034000289400100403818110003440301c3d045095980c1840f03261000500003031400b88031440b00188030800765070000c400b5603030081c00c046100c498036000b03036035815580082007440354000c00250030541c140b140c5140d481c58000d0040c681282c003980041d541f40d000c20550b40c400c6c03002c002203640ca40d40751820701004d00b0090005000320311001d0b00d0b5100d0003d00064440865072aa102c285c0240c40c00107150f402c3c4805440011030700b0381000104842040244000707074112040c07000782c60544500090603a00c038a2414500744110300300713059070003c51040004000c202c41c1d00403102d20316603405000074800e400e083c5580341025101203a2241c81c0c864a032654520962115074094118411038014010030748481c46140d030300382c10510000b90380d44004800d002030a140c0d1001149000c032030402034a0309640c50100f500920599904868001012600b118810034522043d40c2004142065580d079840150b0b903580c8440c403e0424500f90051600031300d801c5805081d0480f5004450003000c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 476565098 1250 476563848 476563853
    0x708070e0307170d02060c09220204090213050f010e100c0c0302100c1403090a0306020901050717030106120216030e190609051e030d080a140903070b1006080103 71
    0x51810000c2000e8051148510000d0390424014820700c80c03195410203064041c440b50402070074140c1c024810504010104100c12103500c1e121540e55a1062242e80c410f10208581455406407156502c0079010500105188217900d03d5008150700f03c440c02c0b22668128602d070f000640700c404540c00705590100d18866441c141b107000d00c285455084c840c0001064054907940010281520214003074000785507001c11310100010403030030406558055004504200c104030000f400310500c0c0c080140941c0e00441e201040b64011b609880103580d02104074200380d20006404c6105400922a86000030842c04003034105400310710803240c0c5944010008010740b11141c0301910441e44a01d610b541000c8004070020030304020310040c0000e000385075148402a4508402c0044c4250824140341c0000321408050b40d4a9070700189a9046004508200e03215583c0c80c03000500a02d244d080b40980a1000420054a08004402828682d20032251030710182c4038416102c0044d484c0d40250b03000701d094000144003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 476566348 1250 476565098 476565107
    0x40606170a0b03190b06040c020f060c0714010c0c0209061c02060f0403020d0309080c09010503152d0f010f0305030703391202010e030a03021c0c1d0603070807 70
    0x203441c00030341118130306880c0c3c000001080b010f828061314050749000a01510385418002e001d0145202d10041c01540f443c8620305485590103040c542d00c0d10030010b880c2041240302c24281c542c0d01e01100080142c070070541405000142e2440d0100e100c1c1101c0c000042d090b281c5000c85660b0312500c1000031101c03500359428071185034042c00d030401015000f4400040180d46070303038601031000d101b580ca40400034a0014910b04c0c4c00c0ca403049441c0724008400052200c4c1d100000c4200c0108002d5000d018035840d000c8040e0700310b4042c42d500d292102010980e40ca02e0000b205d078080d00a40c1da00b040c8900700d0780d070b4070422000d503007035400002c0c9960020850071001ca44684440b4170b4110301d41e00c840206032041d01c0c0b076515501c80301c070828119aa0034a80c01d010b100404405081042d81c9000070701c040c5e68a0300c401c68482c030039040e0400030306901082c40200021001c0b810159074114001c100804000110040c0492400040181c5000c280112904403030525005481c02041c6540b100740c81070b21004030565 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 476567598 1250 476566348 476566361
    0x122f040606230f090405040f050f0a030806011d1c0b06060310060c052a0103050a0504080313050307060c0503060a08010b0901152601080d2f030f0a0905040606170a 72
    0x149401011301c44000503030303034912030180541d01c10324000d043c100c41807810a05102c40400f006195070402c0e01060007080e0446007a55200600346801c50610300c003980ba02016030b88ca143e00d6900480c51101c003a610850a540182001e401582e51058030369410040282c503200c00c031000090715445800410080d8015804504503a10a03410380303003c01035908102d03101d00c00b803441d400e164034502c5a213840596054405c1c242c0091103003c6c00d11551a0580b81d842c06803001401011813502d40340d810409000c02401a1180d15074041000c1c00b50281c0014001c0550f00183c0300c1c5032086000c0140080c844030144280b15544070f0160421000b80e10380001c000842d0240d196800600c590b0403e081d54070041196040d080000440600e1425414400030510f441552180c0c8400c0c8110985845000c00d0131800c03000b035440100303100b040424082c00849096000e1132030620140c4501043c4078680c44d4014100206403403043d1800c0104036542e41c02100c0300e170f0700b1a01e140e0070000010007048002c0503907000038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 476568848 1250 476567598 476567617
    0x8030f0c03040b0c070e070201090f020f041e0603020f06071a060619180b091c02010e130c1b3507230a020a122f04060623 54
    0x4905299480e1100c90f8940d0154428001c2e541211034103000b01a03001c0f03100c81d00064144000c0208c0603a565490b44450789030701c030281c480d07010201d9090240d65250083d00c4d810143c03d550042c407035001003d50018220b81d01040344148000220112036041280c181c0d03a0701500904e40c8002c0c40a1342090009481c0003911103034000c1010424901c00054120f03483e0620410380e46c803010315101c412030741404920b0700c3d0403c0c03c0c00a0104001856aa121031011000f5a091061b0302c441d55010320058510001003188140c100c0c21640607007800c9892607108486044c40c6032548045104440302c1020500c0d0a4200200225510f2440c20404510719402c1544480781240c290b4845592451002003600500c20031102081c1891401e440c0002d041c59000303010380c025000389602d41c01c80d030000e44001060300800d1001000f40c21240305200c11002030503100401c900c0c1c0301c000c0c4005a0b2552416500c0d601c1114040c1c0d05000c400501680300e000c0328198030203004030298a0900c420309522880c3d0240d80f88 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 476570098 1250 476568848 476568853
    0x3090b010509090a0b06150c0303090c0f13110714060a0f051e0601170a020a0306080c0306040f030c120e10080105090105011107080d0c02031207030c0602030a0e0a05030d06090608030f0c 82
    0x348421042084008d01c0d05461010041d500e1345000205a03182507403241c3da01c0d018458035003040c2f8241c0c50780041642102c1585e01e01245500c481a40034140b8025800060001d141c800c1d0303c01c10090300424298060004d03404180102c1c00b503d84c40206440701a54260f11043c030088541810007140480e5a8104e58145420040c1c481495007520a1a01c00d48201481c0307a03001948026064043c03150354001c00c1c903840034040210113140080d813030392001030001e000d150728410502d0400d07104881c1d00003401e60021030035141220440000f041341202500352400b8540c00c020305840c42d4003d00380039040b84e4000b00818026800d24004681d44440040081d0182c0f20301d85000c01c0e5200306204040c11881e4a0740d44600451042c01014a01400141c040300d40440402601d000701c1d5000b4000414582c001201680e240c560807108402003506030f11075206c5008280381d0384100325010000f030500d00340c1c80105000030f40d251402d40c82258064803070071545174401c0101078240c1c00e030030014060340c00d580c0b400d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 476571348 1250 476570098 476570119
    0x209151b0109030201020318160306110c01060b040e0609190b1507050a0201082410090305101410050a09051f06020a05010f110306040f0f060603090b010509090a0b06 73
    0xc95400c1d503294400450141c5d4000c0108010907520310301050071402c0c0a00100100d00300481d03098407010060002a0040346c860302d00b0000078000300b04030344074043d151008015a503a994103443d856003250240746030940405001c58518602051524003610070a00c1660b10484012a014010f000740500c00341c00c41c000341e0a103116a40c0030806050301c24043c00142810980714800107010a5009100000c240d0304011003020524407442d66408064050700c0500d0218046441500c0000b1942d10080452085201050340201c1681000c141d001c003d40c411445911380324903090031600300313000b6290030111940d4204980102c0f40c00c1903801c1504184440601e0440a41c0029041a16000803025920800341482084000d1045c00e4140c5580d260030484444200800300841c400908120b00c01d5480e0b91001007031034000d034083c40c240420a0010003200e0382c0e514018000c1c00c5212170540d000c141e00c10000825050032942144140e0910010b03141a000e940c0d2540b5203014040c2c04035030000380100c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 476572598 1250 476571348 476571397
    0x5010905010e0f03070b07060b0909010203070c1101020a082b020a05070609060e0f0a05060a05040c12020406090c030c0201240605030a140a0912180b18040501061809020915 76
    0x1740280301c7d442c024240440c405414809002080f10301403d000402da00c1041000401c690204e20b01c0c511641c0190300c02c04250300500103d141c103504800203004c5401c00241022034101444090840d9100000007268140d061440e507012401088902c90100e40204090400600164000c4400c5441080c00040000c500740d030032440c0c41007202d00059182d0144014000307100e400c00110307900034103900051010307140ca42d03074184915031540302e03e007850420613001d0400c41d03480d90400030240041203010822160890b80c0100504460114140903500c0d010502d4502011140d0380805140b150f1103801206103041c0c4200d0307003580000e0000000302d41e90130990601941000c0c01c42d0044401c10000700d03002c000ca01341402c0110400000303000348074284188a001903807101d80c450440d40700b400d03d40d1701c0c0d00d05ea12484c84050321000b1a0b9a00034684070002c05c240d60044200d07145d1860759011242001d890364080c60403417160101c241c0d0700c0300101074082d002020740c6004000c903d107016030125072804241d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 476573848 1250 476572598 476572619
    0x1020c01050a0513080d111e031206041d0601150513060503040f0602070302030a1101140c03150306130308160806040b0103060806180f12250c0e01080705010905010e0f0307 76
    0x66512100144c1c882d024849091001c01008a0031400440c0d00120035040480c050355030f102b206107a49020000303000044203561141e00425503020403424800ca001d1100c0c14080d01c81d1024007036440704199030030604001503c180c003518180424916524440e0303003000c005540d00e820040c002c40d0702c1d840641050000600764009045201d110350001c50b01d50000300e03005045054500d06006850385072642c01e440c0c0c03a4110a0700780d0451459501255243c07669082d012440c4804503071181c01d031043c0000d005c4000d107442c0a00358018002d0703503205d686840e805400d540014130750340b02400041c5010040351292416500c0300d009040141000a140e41d079484119040203000c540128000140d030f038002001810a1100c00d200d2191003020b000303d0525598110b110703001c0c492407180300840480358500815582d210030618103030420000030b842680c0301a007070380000c0c2c2400390b480e1a0042000c0015254003c0e6036843c03d5403416125071608030040d20034840c8001a800110b0b6040c03003a408002480f4901 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 476575098 1250 476573848 476573863
    0x2150f040f05040609020a0e0f15130e060604030f080d021c0c02010e030306060a110703020301060b030a0b0405010e04350901030e03030103030c0b090a060507170601020c01050a051308 81
    0x8203112184540741808020444215505c40d805c2240104803200300c0c03a5001d002d0701e200382001c0310300000407a1160041400080718282d089440d0800180f0480782070714440074002125070800e045012607441c1414445a406513100c020032101d0842410707130000b203000c801743c054003404010040c1403a0b40c0c4850a10841c6400c1000898a9a2524546006a428003926800701c03c2000214a1410010081900ea1080c68050b03800c010508643c40d0300c01800f48180001160001c0081c1b144d0760321070035024a41e80c026196800940d282c02001007541c1054040c1d6030413036114075061036040e5559200c08602c0c00c4c3c1038880c800200c1d00f070103480c8001c2071401c4001e00301800000c94652960040400501121400d200c2c400181d4070600040000a910842059109074000843c2805880c3c2860452500c414190018a0700341000304100c007150b030241820341c1c4400c803284140100d4442d00c2c01640c61348485900310b03000450401894900354000c4008108020380d98408001e005c0d620a415130503d43d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 476576348 1250 476575098 476575109
    0xc03030403030f02370206090603040501020306090a0b010903020105090609030105010e10060503103609060b0105091302031302031c0201110a1b1119030311030903060402150f04 78
    0x41000c0665025410000000340328a1402004c40175140900903020b030321081e241418922080c4509003045407a040e05403031101c80060b0a2a07240e040c5890064041c0d001203d250340186042e00000b600c070102c1e80584403050718103855141500b41913400440325644540c042d41e400c61000c2290214580f824481c0600814600c0e141c16802d0a05d409118421003140e0712072005c01c0000c0c4240b0000c80d04840219003212074104c0e60705c01f0380b40d01d04445010fa200c141030342201c0d42c0320f60640103800c3c0b42c143c202e22000c0d440f9120401c20a101f040064820b801110040b0b6000010380407a124600c003a0f6000b103421210720401e06e0329165407540068a400c002d0009001200740504c0c0c104003403a02401600340c40c41c1041c0c426801c020603904002c1044c466480010207049a00c417a800030720805041d4842c1401c009130141a200072120000c0078060000d1000710001280008102c03140a8048244d81d25404010b01800c480d484540800154401604503068244400c1000c940c940200c3c4009200519 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 476577598 1250 476576348 476576357
    0x80412060e0105060f031209040603050607031a041107140f01090f020901060807170403090f06050918060604031407240e0105033102060a110115080d110c0303040303 73
    0x1000107103082c25208058003180c065002108000b049503004545031a0003aa01c40550b5140d00c06540000c010b00416480038050b401203c06008519038950024840d60f050790003041c00c080c200350184000c480210203030050580060000c400014940c0503410040a94030044a5509003444045802c5440041d002c880c121640c0d0f124030110705101045a00600031030400c5c1c5000d24200d01c0c082e00041804d501001540071042c00182014065000903014120301c2503e801000e0b101d8030054560780c007840c0c1d07a40c8104c600d218410419003000e2030700c0340316410290800381090710356139800084d5890103c0325981801601d00102d252000100d40c014079600741100721407180340300103002e06844440798565041010810801002c00c111b14406650341c103550303080380d65582404402c5c00210081d840025030004001560400d8180d00408503510180e400000f009155a46451403210803070521a070103aa8200c40c0c5410402402024450075030110901503440314000040041d0a55029800450104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 476578848 1250 476577598 476577611
    0x80a0201060e01090e06040305030726040b0a051012020303120708100608010509063006090127020108060a090609050f0112030c11030c03101a0d0b06040908041206 72
    0x40e20098443e00500ea0032800300700032a202031105803038000081028040c00b00000c04228400e2180d0034000c1e0340d80d8040c83d64030b40003220141e901000c10084c1e501b620480340010110300f11071102e00c5618012811031104440c298135106110101c00c110400603603140c0020300030710004004042c81c851240c0a66503900d12945050f40ca421a0454aa0044010042200010300507610313080e243c03d41128049a8a0301d004440c0700117509003044942c941b000c46215420358a0030a500002e20034000d40140009000c54844d070b090b04036040001c0300d54055290315104403940594081c0c1c6d0050307000000600700d070030301d261100301a0013917800ca54031541100d95a4400c00c10502c020402da5400341c00201001090a281601d0013011038030300000140c03440500c42c0d5050a182d5040140e4070069001a042e59000c0561610100c0185100c000c0d44065810b2808040b07498500300d410050841e40c0071a9506513500e0740350602c4010140c00000f01c2d05648104008100b044a031043c41c80868460407012910 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 476580098 1250 476578848 476578859
    0x90c0108161103040e09191a1b0c0c01021c0c020603100503030304050c0f040908031603020415180b0909070327050307030e0a0b0706050a14090a050c190e04020d080a020106 76
    0x3400542180391110810a08511000490050107101c2402c0d070725070381011644800d10274100c0100d221800481101c00003544010040c0702107150500143c0903000d85401038292000020880c41d83c150003c000341c0e50903801e1005184c0032010303641101c40c101a9040746030703c60000c00c0ca10b90041c0d170284c865900c40404030529191003003110303c4112042d0340c140003030303400f544e110900b5001c0640001744072800c4080e88540c4502c00d906403402400c000c005420440103030340e0060240c01a00c02120340d84528444041503c5080d071003285d8548070081d001003d2a0381d1100110010003c5c401540c00240302c10b95842c8400700f05810140c05070780180040c6a50b052a07240262038441082d084074014007900c04100181241801910000c5801500106036642c07000502d000401402050101c107080100600050f40e00000300070034418030a00441c0c00780264070007041950520f0342d52410501210140500c020844500115006032019000380f0b80944142e032100443d4104206400c0140e40d101c0c0c00708034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 476581348 1250 476580098 476580103
    0x403050403140d050703030e0c040c0c060605040c0f0f0314010608010815100510050f1308120c06070309110a03260403020307060c0f08040801050609090c0108161103040e09 76
    0x1e40c1c0d0200b40c02815a0140c1c000080c0140c01103503405401c3c195258001c0403401c406200ba030b907480030300800410038000c10324005080f0080c40c00041c0c42d0180b608401098501b01441500f4229401d504d50080c08840741c44104c0342840c1d05e00801080503160708450316201007090600380038201d0744d11a0031003981025145460403112186810320005c1c42c406115180141c501d10342d0a072941591000400000d006045e50144112000349600c00c00c0010100100d00c00c0c54131020540d4891015114504071a0040c00b42d03074000c0314420031640d000303000800c0009029601020a90b441600900c1040b2010400283c44040960040d1210340107050707003010805011007812000c159003101c3d80d0401d41140c0219640720500d003e00390a001e143d20f10101070000b00d2038400400c1d980300340700303c1d0b813030303031034042e801d001e00700a80d082c601903401000441c3c1c0340540442c50846409040e911110705940f210000c0c0c50310b0106245001c184485583c0c0080301680074030040002c0c000c818044090b81c100880101e2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 476582598 1250 476581348 476581373
    0x80d0201090b0f0f04030503072a0201030b030a030806040c030b18040b0c0703050f0a020304050604240924030b0301060305010e0f1501060c0804050a030506040c05030d0c1e0b0403050403 82
    0x10f001000311810004109120310901e41c1040d00f5140140c0c6a980c1c48409941410318000c52102d242c1040d580c151042c50842040c1c00310034802c0e81c05007d2081c0c034000381039031581c01800060106140200051f09420a54400c0714880c0080c0b60200341c015086c008516494040c00b4015600401d081c104414098041d001769007141c10070318030914140350354900038424004e000401052800001d04001214820000d40300500002425155a07950791965450b00c03801940415058102c00380300e0036207403806415100c089603520b82002c08483d0510714000700e2546140319500030f00d075441481d9042a2024407a41c00503505c00c0e000090510501c1a1207071400b0801c0100d0300181d070000d0408041b44204100c29811038555043c105a107605a00e014100c900454004581001c0ca00c000001400000034000780254000c841101280b034a840c1415203508040da25074011680d038910600c00207088420300d4081d84004400f00ea10494a0354400c820000c06607800e50009001040520922080c0c04000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 476583848 1250 476582598 476582611
    0x3d060507020405010e010501050f1e040e01080c010c08040e0415060b09030712080a0c05190803180a030f05071a13031214041202030d0f02130b040f031b080d0201090b 73
    0x101146c0d803400c00020039030311a0071003601c1030920101e8036075010300003007107246205080380d0460f60701c50f0b131115194140440f00744186e9056100e99441220309501880000b41030070341180e89145801d0070b1010070007100d5000f900485401e110ac004046044425104060190040040356692184071108061500c504e940091462812030b03e80800020038000c1141c00800b40340c00e103440104031506105040c044040a100c0c400c8400c0741c4040c0400c50880020b41c82003d141d0207051114a032402e46c40d03600c2c4c84240000300821607660544250764040e80181c2820b61103030100604401036811916120351041e1900760a40a504400f03804054001c503203440c3d0441e00f80800c00400094201c05c0e007010001900282600048107000c001561003031040340c50b08140d00302d080c0715040e610a607480007903100f6101c000c07044940314800300389010541d080f1021201440560ba0702c80c0c3c215116040c40c1120586005040c0c5011240001c19030014420704240e18143c1d00005020b0445040a121034400208070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 476585098 1250 476583848 476583869
    0x409030e01121a0d1a04030f0f18031b05131505061309021b0a0c050306011d010b031f06030f050a02040302031b0402162102063d06050702040501 64
    0x580307842c00101d0315180e00e1844100e822109403011418905c4854494050301303200c00d0010000c10083c10780100303034007083c10080d643e03025201c3e03000c403000c8888003032101d103096050031862410070120700324500c11201115000300b45100640e5600010f040c031542518100905a202c07503800c1c14440f100d802c4100140419039825241810040380718500810a00410110039408240f903880800003580303c1c40d0340442074003141d800c0146414000048450ba21405100e846a81c00205841009150078100702040f1980d464250342814500d9485070002000b102001c0034109800c0741041640c44520010310850701c0c001002622071140e2000d41b000200b1f180f5200d40104030070801a1000a0f4412504409201c4002e10f00035480026020b8821610041d014002006003c030600a482854075002603500407648011001124140d84584080300c1e000b8206000030501e449420101a4003400380742c1b84039043c401e4100c1207040d044480c02c2c9810070000920041256021030620784145805000d0240700d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 476586348 1250 476585098 476585111
    0x1023060d0b0c07150b0406080f0307110d0b0f09010b01020307120305130204020d0b0102060906150d06060f0b03180601031511120408070312110d09110409030e0112 72
    0x2140c0c0d060990355006101d8610000081c0c50785104078140c48255903c18200810442510604805407841c0c4980034841c0d460701100042c030110004044140d04d0508000d1802c090207038803405c078601e460101d681d41201a000c10840020301d02d01709144070f81d40030358800340d542c01c00f46e18960846050782c0c595810740d8030812084c00400c42c1e21445003c1d2030014517000c03c443e075400c0400900034226a600a4109001080c049100f20442e000b01000200a908684680d079540c228607546001c142e540d8140140d040e03201351081d04001002c0c05150740030b4000420210750315030b08030055808030303403150807032500c040300340300d40160f901c080e80a001c8030000c02040b03a54195250307950790843e4021300071201a42e0b0b4040b4074501c07107603405950318a11402c80341c0c1168a41400e10900540c04054110002100820100c80711b001e58800c500791a00026107044c00d180d41c560400d0002c0003011429140c091006002c142c0da51354500030b40108130310a564140180484a00142c035105091003403400c024140b06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 476587598 1250 476586348 476586361
    0x3071a07022407020f07080d031a0d02060a0c0519020a080d090e1e0c041d01060c0f020d051c0801060509030307020d0c0510050403050c09090d0c11031023 68
    0x2198003600307895816a1208948880701c06a2800b0305c4a50240760a00400600050300100444c0440c502102510203103c40340310034190146a034800004c2580c0148085100c00c05800c00b80c010306010000d500703201c450496552242c51a06540310f000000481e80326202000f1414003a0200e00181148001403580050565000d04440300c3d5004a5a080f030305040040c0b8080420a5411441c144c001004c1181c2d040105441f106680a07019a0458420404505010441070303c0118100c825503540c0003000003540e5500324170380305040c90690348158090003140c04a075080c410107081140c4401085062005544040c00c3e40205070300c000300344007080c0a001c01c6620040308688005604403400708804030245810318904005030401500210401ca0741c0228941000003081600d00a4013200c450040305c1c0100302c05298110740c500456000b500900685c18040d0308550869841806184024900c50003c64039140904d1000e10442d500d501d181850b00c030000f04280d94100118500070300720701d42035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 476588848 1250 476587598 476587633
    0x10f0b0612150406080c040b03152e27150611250609050a05010c23100914060601080f07090503010207080702100314010b070f0503071a0702 62
    0x981c4500510010080090b6034010354070760915090400410812000b5150303802c10f50382d0429050781d24012460064289110314001a680024080c003460050295903020680100100c4c0c5100c001003615002c56480007244111410a000e4801051048102c903800d541d410001404c9140c0e20304c02918001120900329074820420b03003611070a0500d20200101c084002d407801d41c01d4914100d190203001455404400200d9000d4221130f5243d440364140d94888040100441180c8180341c00f051a40c2680340000f40f42d01d00c03070b10300b19003c5244403803803240c501d100034100050040402c8110b07a035810010104168101d01010386110100186098030304440081c3c10203201a00d001050b0f50b101d000103040601c2101c0c880c0103040c01400030b64850200d85403d8042e0780107020204d20079072070011f80c0701015200c1d20038806401c001000f406240c0c0d10b0036000d03400680c046801031b200c549104000d00c02040c400c00003011251b1048480268040c0b0b0381d03202da859204054418001c41d00407512942020220 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 476590098 1250 476588848 476588857
    0x406051b0a0c021216170304180e010f0903021e070b0f07021f230c060406020d0204030c0b03010f0602030319020310053a0f110d0c0806010602010f0b06 67
    0x110b0900c40c40e10441400041c4482d2694503640c110307031240a2055031409902ea60040440d200c19420720704214000034056140d0281d070243d07400030b256507a60001c4036100c0b03401c0110b09001190001807182c0003010a0b02c01d49903001001e60240c0d0001e01076400c1100282d2100800f07501c0300e0050141c490920107041028405c0c5020700014200218428003590342e543c2a8000b542c1c02c145e00c525000d070104401502d03550b070b0140c0d040e20b11013030001c0300407079044070f14200c441c4003400c074024010700d030740d9580c1b028003e42040c04807000c020381c2880b0201c0000d0010b40c07200050003d140d802900d9624240310904825801e4028804540090003849881800351024400b06400240c0244c0c80b60340d28a9002c10358403460f40310380c1c0e01a0303500079803145102000719518149a0044548c0003507841d03d001c503440c40d40103180300500d9030048080301c2c4081071402d01c85422820000300008010700395a1201c11764040c094000f9604ca4000764010425190244951000a03107040000c0c0701032103840000988074040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 476591348 1250 476590098 476590117
    0x903020f0d03140f041410141012030c06060801060603020d06061b0b04021815040b0405010501090e0405120c150108120f16021201091109010305030f0d0f0f050406051b 74
    0x2100000305040185603140c07411003651510407903c1c0c41070b1150b01080a4142c90080c404407100842c040380c0d1014030001d62740141c0758205105402074001e0b9400300c0f1440139421059a02c6a651540403582003400e00804005107d950707030140c1c4403004802c4100440d429903011600388180c07021035407840d180c4001051032541d00007030240d20a540c2d5002245020f001d050800c0290304840d010841282c0340c0c66409207905400356010410041e0391800c0c00102c84c0b00307001d1a80820104541000780108007082d481c0e101d403052042e200c500030341200700700e40d03504101541d40c2d85030003407024034880c002d03001216401800d5a00040c1004c0e806100a01294400c10300c8400d803034100001d0008040d2480982c01c1e4000ba030181181100c4e92514060718000c12003a070084a00080601070420145480044035050780d800001440c504200d90200038003541c002c0c0108490b250310b819001c00200100d100d41403125030b00302404607003032a007441c0540440d07600800d00021052190349a8075400503400a4031580d01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 476592598 1250 476591348 476591371
    0xb011b0b07080c0d020a0503010326030a0b120d050405031011030103110102030c100f0b12060705090a030804030b0106091203090509090a0c03080a020f0f06070c11040903020f0d0314 80
    0x12204a000c0c125803203031301040103600c3e0002030301c192810f1340710340118122030090704854551f103a80100e018081c1c00c448000c3e00c0360101440801c0301101e03140e101d00d45070040184043d90390b2000748142401d01500700b0b4444045440841d04004900341803044104000b940303a010040b000001d81280c150f4001808058105440d1007100c00259008200b02d407859001031048409101d581c0440390064440502001c0410f030030242180310034100891142803076000340029182c1c1c0c0d9207001c0d080302d59800c500030b2070741d000303410410001c00303d1010801040914082d400b20b00407581828400361410003141d00446a07000f650420b240800c0e4801c1042d41642c10440326140907441d032581745890000c50940207400f12882c9140001045620070081020b00c1c810b0302aa1a007024050019480300c041c918940c0803504180000b4002c0c82c0315100b01550b00380700e5181c024043c042e40703010031304841c0030b004210003682c0440720301950b10714200110003034101d09150502052082d040e08034800f04010302421841f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 476593848 1250 476592598 476592601
    0x30403170316050f071b06110f07090504061b0206070f090305030901140d0606020102070c08060c030a02070606151d090702100b131113090203040c05100e0406090b011b0b0708 77
    0x1104c020803140c0c0a500100240414984880924002c01c458460500426031031401410303901c5000c590490084403810140c00640e25048108001c0c01c0d00400032100541e072205180119040e4036a00c22421384564000c1c496407809040c00791003a042c841d46841407011061080000400000848010010070b280c608081c000515020549000305d410040780b0600304031002c11500d5056026042c89801901050100d9030707a988032640313648068558001d110700400c001000c1d49155001440124426500083c0c06a62000a081448000078004000600c030026444a003800001d888076036480444030090681882e0002964841c0e002040c20211900d40f032070b5030007070703500c84801c071f40c240c80700d06001d0003d10303d52910407585500401600a05060100012800550501c2660f10840e0311a0000321034a0604042000554491070f010040100c2c4c0580c500c1c0d07d41380c41c0680d01c01814420000b142e242d125200152884854070300c070b0501c1d0120030034800d010030090f54029400542038103000c96079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 476595098 1250 476593848 476593867
    0x6030c08031815030c0c2e050c0307020a12050919091b0e120a140f060109021305040b040209131a0f06160317040b192307051b03040317031605 63
    0xc0004240f07003001909010200c00031402e285004aa041d40c2d401d007010402360f0f86421000c1d04600040c2c2e5140d0069204010500004400d1a26880d2171912810b000341007802440011f40c10f1080005039407038249100300100300c1c20b526800340d41e011300145850004e64850208008004180315000644900703200f4003140070341c0b1028072140203441c0c1c110001c0d0202d0401d00c2002a910440c0130044803440c807521000141c4020310317100b519590f4482ca25201000e85c5050100b0018000380510300743c2c056070800504003603548500300200b07400d80e2824049082031105984143c2c20390311405a601408031002034042e25511401203a031031080300c0340c011288401d1070404540c1c101644154441500000050006000e00c84000f14411140300900580d02500004500244c4040c1a007180c144440483c541000301d884c440c204e42e2010381e604e4000e040c030b44000c80b5100b21a2010600c42460b070000141030080c4101d1040c0d0750130b5500f4403140b242c0b85090010140c500c00e50310a04500130054003240030103c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 476596348 1250 476595098 476595103
    0x306012309040203010e0402030c090106020712060b19060305160c06021315020124030b0f1906030b060f060708030c0f090409061b02011a01030f06030c08031815030c0c 74
    0x5207000940110744a603140c1c50301400c48201607406078483d106820130f1180500d04621480c2c1605c6181e070241110130710301103041e8554041e080080328660303141d50b0f00494075201c508040701c0100d11000880d200d6483d080010f0104c4001502e01001081c0303010785469404d030003206503040e00398840c20050391450881040ca02d41e05640d0050300a20040c410b95800060313054102c000e0f02111003040d071506040140010300c2604035072000a09004088001501e250813202d0303859401004ca041c85a407002c407840c207001c215400ea800440e0032806240a2000500b828466148000000d070303076940c03800c0000d40391071119000080c6102501c0c0800254030b50005503510603a07007150300107401031010a441e0301c2e081020f002d42c03803802d0442d14074801301c0b582101d1050140000d09e80310603d01010312507440c0011005060040708200700b5549a030b100000007488480e40030002c6c03c1c1c3c68091a220410703810411068400c191142c0c0c85035000351500800d680c03031042182d070003e08140d406944e40c004500c04a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 476597598 1250 476596348 476596357
    0x609050102070803011d04020f010e0a05030d0201020a0e0604052101091b030308061e0d020d0803070504080607030605011e0c050d110f1b150c0303010f14040203060123 74
    0x10840e50001c2500c204010304000510306030792200740d07091842403240c5001d6095030b1084801075401130410700c10441070750061562403d0940007410121906490350301080c0b82c03c04198803500142e5001403401c41c000c2d409200c292101c0421280d4a05c2c00e80307408000380c12019609190b4481815501103543d05810035800610308aa11200d0594003025280e50803c40d01800c0c0310513404210548000340d4603281c043c0e00e80300622001d11445168284507070601000850300710040b600f11000d5018030006c20081d00245110704559583d142e40c0e0387c10b14000e1402c2000140c40c40c2c0500d82044002c1c81181e0304001c00d5500407956241d00505207904c41c0080707030010702110014106004401e4060341300c5602018030326080c0340460450302440702c540360325941d80300c0c0d5841a54201150414111151400c031203504400144200e04038180b202440000b8207592007039202e44e041e0142c1000070403000d00c1c0c60902d00b004031401c0350214103518003000044d2903c614181a0301c00420510700919070702c3d01c0c00c2c05a6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 476598848 1250 476597598 476597603
    0x20a0f02150d060306090c0602210f07050a0804050301230c090f1e030d0c0b0f040201260402030d08010e1504020c01020703120f020408120c1e06060909010203130206070609 76
    0x5010403031307a03030400c400140149441603c0690b003220b00850021300000300622600c0090000780d20f03c50346d00100944a030001c0c06504800700040104c20b0104604001c0c40080c1806401516515031900080500316500c0070640a000d01801c1c91901544104c0304c507085d03006800c2444281d4840f10400000c600001c031340b81c005c1d481031a65048107000300c20720f00c00c0843c40d00181d085904107681110180c0301c4114202004020500100008116980d505460341d040713841810b104441500f05030b8800d0481c184022510034072040301d0200b1042d031a04000031101c440c488e040c105555410f00038040c012880042c00107020240700d401c204016200c55040b00c0c14200e5010086480712480d190050a0360103644001d040c03a8242454941c181c200c0d4030845d41202c0c0f07038100a0506420307082c10900c5682111041034007502528030210240d0b44600400000d205621000d848186400d8040000c000005040344006038130501c00c100d00baa40ca03031034440e1004d404441d12515903489103802c0001d8032415200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 476600098 1250 476598848 476598851
    0x71a0f07031b030c03030605040b0d03030f021317120304020d02010c02031509030a02070b040b16110301060e06040c0206010e01120c090608030c0d031104060e030c0d03050903010606020a0f02150d 86
    0x54418580c1c004c0f00d00589070b21a40c0c05015543d5250300300425142c80e10710a613404600030700c0078000030307020f03a11507000050182e0000d8206204d81c82c1d21309a00c3d0040e444080000e21248165500510520990100c40d0100d2812411801d0580200c0c034403002488000b814010b961081105560b010031802043e01c440200d001e0861034410386c0683c580e002521b40a016220f82800410150140e03000d6605945513620b1050034a040a0702c1507054081c3c0043c02d072110303c03001c1c1d4100c2013034601303005500143c0701c2c02d2103040e100c3c02d01009003c00c480420141c042150020001400380e826108a8141100c030300000021071041d0a05202c2103140c0c9640c08000d03407502d81880091020b00202c05041d51039003241c15554040c6004105030252111000403030031010f4200300030701916028a07124140114098200c8461080d003401060100342000400d50205801083d10380b0a403a0074088c0c180504401d2010341481511a59031a0285898050003482601030b01281041e503070000041d980c1009903981c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 476601348 1250 476600098 476600147
    0x3071704080c07060503011520030708041503021306030b04020c011404031b081c0209030a0303380d0f05060c0a080c092d06040314071a0f0703 63
    0x2450401c9034401c1004490901544100103000f0303003e4410303039040310910400855501d0940c0d800325101242454509000c6058000e9000b100c181000540320992242a441e80d640b0700b05115000104403510102c000c02d40108038010701041664402000ca99440c02c01140d544000750008001e4011602034403215803900c4d52080e00d034008014401d0040303010343c81b01e0944048004980100750329500002d40701303107000c0110001118400b41100c005005406005044c05001c0b40020308202d440c090075000251541c2a0450980021040c4142d0f24010440c805064000380400301142910049891003060854080c0c0140301c00c8807180e0b095154010700303651039071030304500750b01d55a00640082800503000d60000b9105660140c11951502e800800143d40e181c122001c07007180710940d007c8078104440c0500300024940315407020300041d40c400c80c01c0611800d001e022032071401115901521625900c12100800d080b1200c0481e440d818101d18020340d03864a07403d00351040c426000300e40d10001401c48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 476602598 1250 476601348 476601353
    0x100c05032205040c020a080a080613020a0206070f0306050f0d0602070b07120c05030403200f01022b092409200913052e36110603071704 60
    0x1c000c0054940441e4100b040710035a440880c2d640d070015500400380d810400c010a6094000d0301926400403004241c0c0e603185101d43d0400099030000004840968070510a00c522030b07800030a5071807950314928082052624040000d500100c03180552402111290340100c1840980d40444060304d400581c00e2046003001d2000801c2c0c03d110700c135511000d5103021000603600d8444c00849010b25016500d40c92005ea240742614421030310400600d100384503000c0c5080929400380040c010b080c14030020341c2c440501142900c038410026445012820b85441c06c0c6800042190100b0708035088a03950b06045400308020b00d0f00107254508001c0c110100140d210b0f22440701403c0e220701d901c0300a444036500c5450701c04442802540000300248035030046514400c13510a01014a401c1e107503994070b11819501d0407030418040360b00c54440d01e40010360400641080540c20540280d8a0503402c501104400c01da440760380c5079042d5201107a200c0c020002c00b15094a03c18800c841c903410504e9444030301403c003403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 476603848 1250 476602598 476602657
    0x2032203140d170402030a031b02040501231f0503100812090103061d0a02091801030b1b160305090a05061308070807060c0b130c030b040303050a0209100c0503 70
    0x20050100041e00d1050000c3c0d83c902c00d1202c00d0700a5902400414000d01c1c103a80c103551111122009851301d074199448000540e403540070b80707030007004450302d140302e0070403540350100c0340003402d641150140c8040c01c088904080200014500d01c02603140094803600c0f000c080c001c41c01080c0c2d11000c414401c800716030024040110062298a00907241001a555180c40d00050300b000042c8810110910000081001c1120740007002851001020740b80c440c0140d03004100700100a8000780c2d0324842d020100003610710040c0d0986041520748402c41d04203146400d036403080e4422518005e041000124007559980c45440b940c001401004148641380d9007500c400c1001c6000714821400c40d0310a048000a4851000c140e030784c291041c0b90f40715000410291540d03003203c2c0028169440c4403842603424804200807a8902e4081d44c8500343c3c207a85400c043c1401011703100054112503010b8070402000840c1d603680c404140c40b242c0341e4200503244035000c1c01c0860450042c0700300d0903d0080100c40b143d8061300710 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 476605098 1250 476603848 476603863
    0x2003030705011512150c1b110f0409050616030f020c0c010e090108070b090619081005040b0612070e060f0408070801060f0b0c0309030313240203220314 67
    0x140c1028101d40350307413407a6240064090140143c0121512004403c801d90035400002c2c218545081209014031051129000070165a8090300d0007020382c614002c8516200c40d1641c03107581c003128188682d07241030301e40a440302170103000c940d000308507080a822114083e41160601490050045445030400010700d03840c1e0f82e181122034001503030030310460640d00d0f00c081c0140c162841300c0001c00d502ca08001501e0060381c42a5422540080d003442004e078085084a05600d01201960300d0384102d007454502d0204981950f08070612550415020074815161103007074800780414610903200645961070b0955044140402c503c0d000940041d004440300d0310300b002013045034110300c22221042e076985c51090032100f1500030b5422914074440204039020000c0c0141011004400a981c038010803100000e1540d8001ca41d007441110703208104000a2842d07440350403110a40b0035501c482200c40a20080d240e1003203001c0c0303840d40038210905c201c40603190100d10029640c8020ba041940b407864407004c2c4e58000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 476606348 1250 476605098 476605121
    0x24090a090311010c020d030f020906161e03020a122601050a0905150f01140d05010e0f0603100e070807030506010812040b09102109030201060603140103200303070501 73
    0x80d42d020b10602e01005110340c0b0000f1281d0741c05410212003940086000d009189a0384000903000c1c032803034400c3d03070b900c1009220002462a040c4e0a100d8140791030b001c20306403850f14403517001d01c0030300344000700fa008100700c1c24460303000b070794081038101ca01c4060300c040c108400c13009150f6102094094100c40f807480c0040c1030310000c4a88800b002e07511420003040d600100d07061410519904200b1207582481640d000c200881410030000651112505032060340100d40405161921880100035451440c100c803a000211621800041e10701076001c281d85001031100344071201e50350b4491080c010028016180a0490082174070007283d5a810001d03030301c0d00c00b0f014000c6d4030f020340302c09282ca2281d44003c590850782c0e0fa841403410080054204850506455034480911218440d103034a038071003030f02100718028280320000400c940c1ca410b00a003151000c0c0c11460030b06217400802c0304d40b040c00c0b51209045030b601000041d0412100e00390728401d40d091041d110380500c0003042840400c0410f4008541607130 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 476607598 1250 476606348 476606357
    0x50c0604050f062d04020d1e02010905010e06090909030903070306140114210102090409030203191b060e01020d0516030b0604180f150605040806010e040b24090a0903 73
    0xc86031100d800050010024004c0d013600c1d49000058246101096075610500040400441010f15211015107031040c0c0340540d00700c100c40302c544007150b0f002003103000606402c1c07818450751001180480c0c04d512072200c00c0b40c0310384c0a41d0700040c3d41e5181001140c4440c5000f45c1514481503a924000010f8041c1409203508485450000300743e501407000950f6180100403d18901c10345441000460110700000f07150070b81d5020041c03ca0b150325680290b02c040340c031039030065640b0444603409a604b5111918003c00f00300005680820801003005044495a0000400a90004441401da00a2040403690500207082c2801c00c144409104082d002c611020340b4140714146c2010300304401e900c103501541900c47d11110040340850791079800010088a007a00c00146814000780d40d1207100110f41c45030300016800039061241c0c1c40240100b03801000810524522030815a855004c600b4000f4146034036061001c0400e030611024118130f046000c03024103c1d1250307040100b51280501042c140c00c3d03000c41c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 476608848 1250 476607598 476607601
    0xf060c020a080303060d020d0c12030905130606120c03021908010312020105040203030d020306032e150b07020409021306091b02030c060609101a0a091710090201050c0604050f06 78
    0xb00100c01c8911405c0010000d0750522166400c108042c0c4001d5070607500309524903400310704241c041e1160300381c05003e40c1b5200c0003240f0300400c0140101000d13180007100c5040c00b408000f410f4019015080a0095050204040b42e2040d0f0480007030140c070010f0701d1280e403a0130748100030f44e4105400c5e80c140e81c001c2c1e141c010440400304040e03090707403010f45009405500030403a4205040702c65001d9900030700000d054465000078540c0158081124501010307125680a0308508402582d100c3c8107180c4050411141e1142c1c6810b9040136130b07000b1008064001c6890350300c25811542c890000340b50840e609002081640d4560402100900c501200c0750000c014440f402e888090000003651440c0072044014140c950707a800c10322403c5d20028003202142c5440301c0b404a0100d804908080200140040b000d86440d201340006155520380c1d030059207505a28000303911081c00104034030300405400c0b0000301d0320505610040b25280710760414200b541c010081408100b00011034041d000c440a2400c0b240107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 476610098 1250 476608848 476608859
    0x1506020f0307020d210806091b0403080f130914060109030807060b04061a030405062508070c020d140c010801050328060c08101e0e100f060c020a 64
    0x111034540054054541c01030000760014a41071135401142da10581034114200104035820356800c0041c4e0348000800e804008001450400c20822644121003103010483c846400034503007020721407408007904080c00000c0710300ea00780f004401c0711003003d010040b000074240e5845405004000351410035030b000c52074501003132039507100d50404001c0d280c01059236460160140e07100c100900713003105000e0b009900c80781300203500060101350411001d08101c0c129968906454105d0400c100200000c420843d02c0a00765100480c2038160032b014601400c20541d2921400400da07220f2540a10082d0300c4451043d400d0204080614841506400d000868103040190401528500c07002d001d82d41d01988100700d0300400e8a0084441c2c9a02a0a501d5005c44410661200000e65038004110400704043c50113000c01d08040c2540380009102c564110812401031075102002600d061040380f401c141d02c000460600c2c12240340483c0208000d034420a10b441d035401010701544180d50b010303845490307180800241c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 476611348 1250 476610098 476610103
    0x290912060403110c130b030a020a0902040302130203220f0210171b19051e0301051f0c03030509030c07080d03060f0e0402150706050a09061b08160507080d150602 71
    0x1130303000000313220910501949480600138440e54042e251315200c0e4104800140e2a59a01c000107010200c002503600d0342980140a1aa500390340c1400321544100f04000c4000c0c826a4119030103002107600b076000058900f0704a0802a4202010b03500c90b0b64604480e480d076401030f4105050040b8805190301690b038804401ea44007508105a00340c0d5841042440004003640c0100c11a0396550704101d0704121a03808a0510100c68404d04040d003100000180a580b50039520807001c2d40d1030f21080d10031020340f000d000f08454031021004041c1615200400c00c120742c1481551004081801180e1200303643c0e101c0d19039107260480925021915081002ca01c2c0c0c8604145102520000350300b64215031a168248100030141c0e6224550381d200074000da60000340e09004c2e180c020484204042610400b0f400c1c0030341103c485d83e1000180840a400c0d0042660300a90026801401501c035000c4030b4101d20426900f6200f000c400411803080003400d01107000c41540b00c00051503404408244070780c1c4814003030b60f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 476612598 1250 476611348 476611363
    0x2120a050f010221100e0712050a0209090c041805040201090b0c0c010306120209180f070305030702010906031a040b0111030c0115080303011a07051e06190629091206040311 76
    0x2d10799610a0418800201b0307141031241c10680500c1c120b009030960000311130031910141c45145c07500e500064025824a00354148540102003401e24074941807030443c668504070f1081441e48821900d403000a415603000c2c0c004e181c0180324003803480b0b946032540d040164903200c40259150110389807120100300d0100c0140000c42865018050720081e0f181c0040d042c84032080d810194166201e40400510f10342e00500030080203512404c000e41c4c840106100240c000c1c40d1a0b000901014540250312503a0b0340c0074554903003c04802d8400145d1000c0c0c2000495403544400507245113071000160f01000300105500007070700d5006200260301a25222555151248000c4c4254002110240c1150025082402c02410074034800c4003241e4414055503203203421014000c1c580a61a0408410440048003030612910030300040c000c108040740c1003c01c140c508045000401c10340c0710346040390720100d400403803c0f91802c8200801920300560405c460035a10748049070b044001030f0103440100403039a8000b601c0c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 476613848 1250 476612598 476612611
    0x1703090918011127040b0a0303080a0e03071101050703020a021203070302060c120417071a01090c0f021c090e040506061903050a0b06010c0b010803030915040f02120a050f010221 78
    0x41c0c4d841110720400b401e190700910030342540581d0311800e001c81d55840e50362100c0114031945880011303240c218001e008681c011a50401660400c000240010390844264082c078502402c00c83e4480809080c12490401c003444000e4109a5103100c0014000e4000f01410040e071003a422908240d0380c440724940b8600a03094056202ca6a2401050000d11450100300c0540c40b40040309060000030749401c44005110920014000c080d240140114084c078012408a14500d081c945030380740b51140001e545140081d80354200300700740840b00c640795110f0900c42d00209a407000990860a10381001519482d00351210f5200d039624540801c02d4003104000071044903001005801c180340280c4880f18400030007403d00f07040190f8108118002040e41c580d2038080e2820000458913440c0c03150000c1e1801c440c4580001229601400300400551000500403c0c12350655002607800136840c2c20501e85650103000030714a00401c400c1d032070749080540c0a4116070860640d0504202000050300c98146001d0700c25 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 476615098 1250 476613848 476613877
    0x2003010c1e1809051806070c06060518071101090c080c01081f06080a18030201060602241803070203031206011205150d020621160f0917030909180111 66
    0xc0008040036408070390300128117000d0056581c20800080e080c210112a43d1004c50740c8114203405110083c4a03060240c0707010f0715030a0307034199a09100d0300a043c1c020201c404010085110070404403081d081040340560042c001d0003000e40301e80709d19444d1220200041d00150761180010785011303000c40307150740d000040d1607103401242c1081021180e5190003000381342000c0d00e50a40c640c982d1700011106010034001c0d07000040540c10004000c0c02c291100300014100d00114000c4240ca8450409286c1c000707022140c420900400e40b10074034254003440c00080d506000114140e40d1000705006140c0c41000240d80e003854241c145400c00007102c0007990002c114810307100d054205418210848909180011f1070907040114524050030340c03240000f034070b41602c8158018001c8400c0145083c1a0903421800c102e5501207162100800c0030721588681c0780000004170390041d0501080c001c031194007001501c2c03070900380b400c02e4581183c00580d01841c0345640c40c1010003525151080c0c10b4500d003200c81da48 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 476616348 1250 476615098 476615147
    0x4200d06090507030f05010e1203070e010e0f09010b121e04020d240f0e06090c011407230f010608121803101401080703030c2003010c1e 60
    0x1262401801c2201044566206505020001c1580c05242140680c826400400c0004084603818200008049440e0303000c00c007403041c4802160040d04664801d0070078a0000c040c04031207400202903005034410641c02403112800494044c1c0041e00a25004c4440e01020005480d952031140c003401c2c5200341c2c0009541034001050052420207103049166015014403101106482014070410041c0d0501c036060f00d0f80c903a611411079000e40038003401544c440010300841d01c0e1264020b82c1310116440340c0c80c104001801034400c55240d0205480c0d8441e0011100c19405400008103420b041c4501702100b454880d005140c503480c141401888203562180c009000c03078a55001c0d08000355040b0b005921072a8082400e818007a89080010021014881c6801305201c0c1c41c0300f041d800010780c1a0041c00c03450304005418000b107608a40f00400540d4040c0800348030040f141d41e110250001002c000d0380c03550030311520b103030410350009a036510400c10b1004020314003010761007561071801010140049205016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 476617598 1250 476616348 476616353
    0x6090603023007090f0506040314120d1d031305011b0f1214120606090a1502061902091e04060308130f0501030b090f040204060b07030804200d 63
    0x10040c124201039a041003461101d01512040000ba602c204041040d00c10340410031002d0f84190808010546080b030303201c085040001003041841140006007805407000c000702c05910040090480074142c01c80310303a44603030031951000301404044050869118072000c500080c040088225410810302c2c0941440c150714180054403d103c10a541403010744507007a15001151203103c41c840003500c035401c1c1d4000e8032222135010f001d00580000902e01646d041c404088072401311050306402c00c1c82100c0903511148501c0000300030b014913402c148014458162804050303078001274414003520304143c1e035201c642e203030320f0140d4200d016908401d03a01c12202d01c482c0b070300005105c01801c41444080d002051058030307511410119801101030400d100007004040040008406040c0060142440c0612521242c200003802c03050300130740f60003440b0500382d020400715921584038000a1000c849003d841d01454100900a03078008c039001d032100300d4120312540c01101040f2844c0c09401d4001c2c583c4a5110342e94 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 476618705 1107 476617598 476617601
    0x181212100609050108040b0c0702130209010314090c01120e01021b0c0a1802130510030e070801110307050c0c0405040f020316030201050405100306120c03120906090603 74
    0x241e0203002c1c81c5c0e84901d03282c1d00a81c024060380c0c59a240ea1150b003040b4407811720000d40c400807a02e4100c0c0c0d0442c031a0098180c2101c2600c08103c014568078120001c87c0b8122009038503a041080ca2403034942c004c0c0c10a140d448014140014500b8603601c00c1070890748400d02d0315603110b0304091000300c07190081006240030302040d00e001c0e111034a031186864121442001c10941c407a001310784098508515107860b4003d25000384059400006010090010000030304000c406004042000c28a01814022480c65080261842d481e40c4d4a44508540700e1b000f40700e820815004003010b5500130380d41c1d03009680c080c078003c10780c80a40e00c05030700c1010b00d0420b442c42006929418588100007503a00401601c04454080c1d9a10490086c000c0c0b0807402400342c3e41007110902410f0041505109403161007a003a41d11030000c846a030700400405865198140c0f081e40c0c00030b54031070418001d10344603 = true := by decide +kernel

theorem cover : BRFrame.Cov 476438848 476618705 := by
  have h0 := BRFrame.cov_init 476438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 476438848 ≤ n) (h2 : n < 476618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
