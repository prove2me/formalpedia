-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1277
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:07:47.871412+00:00
-- url     : https://prove2.me/submissions/d39e322d-ba6b-4ab5-a081-9e9237745b3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 229496402 ≤ n < 229676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 229497652 1250 229496402 229496419
    0x80a110a08090606180604021602060a05030a05060409080304110f03070314010609110a0509010c020a03150b010f0233070203030108010b0613090e120309160905090c0108151e 77
    0x10141401c0010300a040288900c0b4175440ea2458100030195000603040c000030441c0816117030050300c03468040c0c0042c00d950386640b600e91501c00d901d0821100010101842542040211401b08141070101ca4000c4d40000c504000109840c0200b80780c1040e04079025014800d00340cac00070a1005000340f00c0d52070104200240502c80c4e441302c002c0700b51090032a2940489030300f04070380340a1500660007800001c0c2c0c1030505000800c1103030001051040694000d55440008103111a04010144034413a25900c0908001020a21082c8000cad911031920324940c0c100baa0074540c40ea0140c0040e40c2c079600e950748400303601c000ca00d00a000251207400a01c1928110360901c451291540f5005c020745001100100780880d0a5242003521000380820301c0e0311107410700541a0035501c0100d00b40c02980705041c040010462804885003501141d90756510000007a0b152100340050b041c000724524400417001d181c0611a5215081250114814086041c4c1c0c03045407004242c81023840d00134809a1032030101d92051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 229498902 1250 229497652 229497661
    0x6030a0f0e0a021c05010f0f051e100603020f130308120f010302090c0d0b1201020406111504060903021e0c040b0102060f07120902060f0403050c0a03050607080a110a080906 76
    0xd03030302c0c0c108072402940700001c158005051000c0c100503101ca0303801080042505e0758107882d0720701240c00c241007403102c0a4445041240818080e001040b51846107900b6420a01e002a071a5042d5087c0340a02410550005402a500d40c3c548040d644041c940501e03c8181d036550b86000c81440d0700540040358031070404000207650800207010b6504980e0080c054000c10f40e500344484c003080c0d11003082c034000e06580383c1e10540d0701d0300e80340c40903510490b6040005030b07102d0600300d01034204225001d600c40c1e40d40c42500d8928070002113040403500710b41c2c070000224108409140076818130b4044941c240500c9100017000300040c03000212000502400e84040100349040707001284c40e144222642e4654540c1c55011982c131911800820008040c019000140501d440d40041d110741c0c0301a6099141c03400209050003030103024450f00c003251000303c40c401d40c01c0c0c0ca5541d442e80c4a10006040e17605000309000001c4256034207402c010a0716612103c215655a00e0400103003d5007401d454a84aa204080006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 229500152 1250 229498902 229498931
    0x60305060307030b061507050124150e061810030516030c020604120207081204080c0603011a070503040b0304050a0501060605131e0f0f180c0806060a090506030a0f 72
    0x80e819031390003010400043c1d40c0e0030280682c528501494280d028010850440032417000e114402440e441020644e10300c407000c1e07071107000748103090b0010105081c0403000c03d89125040000c0d1400b413001507030000d0720303480750400c940c01e41c520012400e500064141441031503140c0c56800144211910b4240360760b40b044640048044501520948000d80d104501150103e00002c0d59401141d521388100c40c8480d803900119800c08002c0100701c0d03406600810309015401e8284510340304404151843c904541c036100c041c070501c111010740d880c851000000c2c42003e0100030700484024024101c003180c0e40b403c244c64083da85a060320303016070f880d510340300011480394803910413540000303945900b0301d08460030b06c4059040b000f01c40c00c2d0701c2916418840005120344400c14040000c01711443c0c4031851a01d0482484e0700103907079074000710101d403815040b03a03022504117806d1a0410001c2d03441c0740d111008902c05403142c4400303070041984000013000b007260840154000c1c65001040d90000e1002002e500c403907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 229501402 1250 229500152 229500163
    0x1060f030c060819020d0b030c03010908040b0f04120f05010f05100b0c010209100305011707030c170109150507120501081203071e030501030314180909010e06100603050603 76
    0x41140e031210504000b0309114079040ca41190306010810380c0341c4034040d048401ca83c880807113810400d4980080030350610301801036541c414000e07002401a48250741d03031340800c1d21440c02490403d0001041558421501c501038070083c200d40c1c44030110b00c0304541000d01480000890444066003443d40d0b101030b4070081e001c0e242c0603600440e4480982801c118003000d6a40208103a00c070690350a0244c5242540d410310044100e41041d1030000d0307594182a00034840800704810301c01103901c00e000030000900d04020302d0f0206d4900a0f015030101100d02205809082d05540180140d840300505d2129480704c1e602c642e00544c20f545622440c0042003040070700344c450901c0344001c1608108541015200e4010045500188916002c0000c1c0720442004d039910720400c00b801d00107681c98005008054128901c030310118420078419040c50710f40303160040c03a103000d0294203014001c40c001007112100c00f50030505078000c000c010348150b03142500001030046440d1081c90006402c0c60701040c407a0801040707 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 229502652 1250 229501402 229501409
    0x91e031e021c030209060c10060302030d1b02010518090a14010f050d0f0201021e01020405150f0720030d18050d05060a020702210a03020d020c0d0f02060f0a1101060f 73
    0x610300e850702d051010a0b00207400c0402001e4000204002001001c03a05000354564000070b46000507100b400c3d40103143c50542400481410310051240300110707503000c0c040c2d400c080755092034096515020340440d0401d210310040303850380040850040c00f0f40412250070001c2e0038414200c070025a42e0766850501d5881c00d8a120f801d0f0042510818940810b003110080e03100c40380180111103203114000407040a907010900c0c8401700d42d50102e0240020700c0c040c1a0003101c903c0011045040800b51595480c2078410a00c00820b030718800c401c8452079138210220103980e130b44001c041d00d030080100700020b0300185007403101c000f503c0c541000100e600e20b0440d60700d0202d1a0444014580b07656000480c00c029880040140c5e4051009501085402c20a15004500d00c89803400b41045030034038074020349042c001c18240c01c1950022103010740d55444540c01c0800321303a003240304100c02c80e003e400411100d04c100e00c2030410196001490510198005483c58807290484000300f000c644c1d2030038105c0522043d0300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 229503902 1250 229502652 229502683
    0xe011406010e010804050708060403051b060103031b0f02130c0905030a21030f181a0405031602041d0606100216060503040201120603110f030c1003091e031e02 70
    0x1207200314107511804c1101d1344548034070111a4000e03180d00c14149446c2040350100d000a00005100446440b0400071007119144480288881d506558014010055080c9660715032101d140b002400d101d406207655242c15000b400c4500d4003400050000050181c1c0d02030302d00400c60111000401703050004215a10f650011904c52103440d09842d20007815060003021b1040640340c650381102080640315805006401c0694500450301d00e1500803c18018000c072805404008020080400d00110484011021120b01090300c0a154030003c0c005000915014a0152007030317442800c40d05001980c1d9000c1c0008482140c2164801c890417a0380741d066131050103034418901401c000c4540180e000d542c12910504003000d100100100110454071503600c1592840303082441915075003003000d20401c074802c0a4000e060400d0307c0c24007181c200044480c0313140c20999070b03076203a005211000c00c0081458581001031919404c4500f40103050b445c1841d11040200c00e00340003480901d0001882101580408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 229505152 1250 229503902 229503917
    0x4030e041a030a0b100e01180e01020a0e01030c0203070606030804030308010e04150c12020309100c0e0306010b1b0d0203030603060c03010302030d0c051222060c030210020715020c010e01140601 85
    0x507a80d8a4903070b0700c041c00ca91840c501042000c901140140d686d1400f130110603e00b42d13810400480e4150a4510000c0c0300c039481c0c1d00c10403030403042541c8a4041491400d0a003000f207448903a00408a240d803180e12009814140b500001000704130601c8000c00c1141d00981d80c580050362584259800035805981c01002c0107280c1e20380401d031721599084080422402d0610842500c2214580c0c82a80e000300c0d060070554100f50014444428607218805062040e8900781ea10030741d2450121396180c106004c1c1c3c0c00f855202003100f03051000305810480c040c1e10b24609803000f61260090207584c0380c00a075080d62103401880d0018401c200c0003020360741200e0b002401001c00010f40d0030241d90540e2000826141c3d40203600d08112100c03040c2e0000c0145080c500b0190000200184410001c90801d8010104110000805102007a40090f003100408c100e4040140d43e10018a400c80c0e012548a1401e01c04a00100321000030034810350181d03204644004c003e0148040907446c040418008a898a0204000c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 229506402 1250 229505152 229505173
    0x1e030c04030b040f0b041203060608060310110c1903080609041e1703010f0807050916050f0d110301090b0a0303050a05180a030c0f0b0325120504030e041a03 69
    0x380c2e00700c6800c079002d03104503800d00e40e154540c018086400c450549036450140c04103c040e640c5071060b0030007410107151240c52800e05c48002134807100031a0f400303c1400d071115603c10b000d186140440d1070034030000302255120f002a0800d842d03404003a101c103402003651900015090b04200720300e5031050b40e00c03d14600b5040d405525010030a50152400e690001080c54905002803071000294047d02405035401d0280c1c0c50941d0031443c00e865034012900270248501403068098018401c000c8156036801e1071620b80c1011907159006010b0540c62940b210b081040c00b03071851210b40025410380c0c40c428411700c070b0515010140803110145100c0280020410000d19900c24442c9020f4080d054143c0255984010003800040300544507400075150080c08203410070130140010600b50042a00070400d90071490500c00c89001001c40c050990b1100030103070040a9890303c200c40f40340b20303545081c0c8100200e0501d0700700101882800c40696015529007040403c208607200144103e80c403008004003010402d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 229507652 1250 229506402 229506413
    0x1514070c0e040f02121f0207020906150f040e0609130b04110604180c081015050d060305060a1d03090303091203120a09020103151805180703081e030c0403 68
    0x80c0b0565107183c412001d240180d0740c40d07000c034400d03401010050000c2032400c00c0c42c256840307180250b140b11620400080c1d0060f00ca0300c844036800300046520660b1210100030b110014480d020202d4500d44000402044009540d03c42ca40078280903280014182d5800180031242e4002d58000b51680e240c083c00140000c005a90840040741e015148506150f5100002c6da10f02c103414040d40022910742082402180e07001d07452030341c4020002c10414155142481c40a014101881d03140100000042c801034056400e401080040da4070034100c64441c40d040c000e010040000240300840b02001e03144c900e210920000607900c003810003e0141d4640481001000b0300003142030140803203800144103401804082000062103005242004941c1005a200040448422103031458000c068840d05102d504a400600494080c140000080310749418034080b8560a5040c030714106441001c0e400320401601c2030182100b04003004101601b54001e0001c1861800700326400d01441000b8841000406c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 229508902 1250 229507652 229507679
    0x2030711120a03030203091207020901090b0303121f0915180f021306081609060c060f0606020a15060b1606090501060b0405100c030e281514070c 64
    0x802064600e076000010251414201c0d8404268041307a80441000310b40c00090144d540d01081038440580340c6203d9500103410154103014800c0c1480d070340d05940d1038980f401c100b1a071000301460074031031a41c0342102070004e020f002d854002002100d20300e80040c1840741030180700312501c0011070340750b50a410000c001701140101b50070f00b0f40860716590243e98a03800b6100415003030040012400d065410000080c1243c0070240c5100030700f0849010f504441340c0d100c44020b040d5031081c5414042c01e1080d05140e4050f164102070459000d140460004104c1d40000720245654441c0c40c0c0001d91056002d082000c95846115074040d102c410000d49d41014010070000c070809105910004040702c150325294211542504034020715800054240b100740750080340c100c02c8010354504086540281d543c000c04a94181c2d8505000303072803005a034080403100c00510041d4a41240d0001c0c2955039030040c1c400d1400c840c42c6103101092010040102105002d01117070f0103503070030004540b40c80f460840240401e4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 229510152 1250 229508902 229508933
    0x6030b01020c090403020106170c060f07030e03100605100302030906070806030304180902120f120306040209040207050c01080708070c030822051b0f010c02090604020702030d030f051303020307 85
    0x50041c0301d02d03a4030a9544003e082d020702c0c041c0d40000307020350a0280118400c000c1c68100703001c0390b000603c01d01786a510081103462a0006500e01c68482c0704031710b0181c4040803044202d6604d03008481035040100c1c200e612000464074200c40c9c6003913200310303448103800300d203c240c905600e95081680012641405502c8050300558050210781c503040c1e4a80d22150301c40701800c03640c0d0003103440d001100250f15080144009901400018001c0e0000110711036030703180c4040a041103032000110004e940d6641d680d050b00c104100c040d20035581d60a40d4a8079230b4890004182e03482c04200c0d2030b07010411080c45140214030505250b201e200215803162810385590a004060343d0307444480700f4200100c00301a1030b4980f00a44524000c0ca5103e8442c070910300104007040996016882001016407160303404400c0d04000764054030546040d03141c80010402900c00c2e0207029416100701c8402c0031340e650303250b841040c0c0890801410070880e1204008009a51224a07018005a00a015010214120740a00c0005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 229511402 1250 229510152 229510157
    0x405060a1803110306010506030c030a0b040b120109021c030203040611010207060e030c100225080c0a0f140a080f0c160807030c0504090804120609020409060e0c150406030b01 77
    0x1c5034181d40c07009122410035042100c072440c1c9002d808509041c100302650142604071201420f615081c40c0c0e61080b80801802c40003090703103840e0030308030b241c4695003d040c480c3c00107081d420b94802c0b0403d1450103040c80401c102d004440c1003004085103440212841100756066000c1c61429240c003d044808164200083c074403954200701c1d1400103100d41c41110301500c0c030100959107030380e08640c011f41407903500c07071527402040c0c0104034944508007946800c108200c0b10071403040003040c4d01d08002001d40109040d5484902c641d140e0380c01405181c040705d4082d035200d80386240c9580402540547c6684100100a250b005d00740b0080c084105010060104c40702d01c401225940640183c031121010a10340c440d24a9400c24803081c010b03c241d6040120282034269400e0000c100c0c1561290300f07034071a0f84a6000020700c3c812055003002210740100240755002042070020411904000006080c0c0310000401449104d003a03440c00c0c1440314810549494200e903042c02c0c54504001680542460410381c0e04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 229512652 1250 229511402 229511417
    0x20a02010213080a1212110d0902040e0f0d110f010e030c191a061807121a13020f0409090602090f040513110102070317070b011d160912060509070b07080405060a 71
    0x748400010080d10185c2401200071880f2800ea0041c00f08861040e05070340501e80dc5030000790400007000a200384055500d24129081002d65002e4509000900d04400318650030084c0c4038910400020103801d046d601002954003500e59140b422070030300c40d0884000e0000301220b049603061508110019400717207000d4025080740607240061840781102726042400310740daa8172080b640080c5031007260301540034500e41e03c11140c1010001024803210754170004040740c000403003080d0b1703001003001e544c000e20f2140024001c5142d54a0000c010f5007024140038055582d1801d0001c091406000d868000d107480b071071041e54240c094540d072805110102440b810b5104080380000007075241354103440c0341c01c1204841525810b2520304110a02d0041c2e02241c080e42c1c0c1c0600310021042030b000001d400100c03c868900790058080e0061b2480c0d00320703504c0940443d20360101e200c180803007904041c0c41503c4141c295680030351100ca403440326005600300600f140e24180301c10301c202e042500c0200f0300c0c1300b0542400309 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 229513902 1250 229512652 229512671
    0x10f0e0c0c0c01081e04060917040f09090201030e060903040914010b160c180f05010501080c19020114010308121b04050f0f0405160305060d150b0d06020a02010213080a1212 76
    0x179401d960466036070390740305160014070884410f4036002c070710507031680b510b03145c5071409208440c00240260014903a84540314021607000790b1208051000000c299012850b05036070040d00c030b0f003080c400e03028150708004241d04d840c2c07207401e0407505850420360b090b400c002c082d1414861804451a00b11a80d600507680840c511484400d0a5500a500100442d6030224100da88041d01e80c181d1050307040c03068541c10b00c088030082c0815100c001a01c1440d00c20620f010540c124050b0240718030000020b5001000441484050001464130400e00340c9a8a0b076074440d9103030082c008141c54840050328206000501c49032601498510100c10001c00074603001c03c1607400a011280e081c0d039800e20411054031040c481a07054019698400780c11180c00174420310907210805071442040141c02d826554030381d114929a911a650320010360002411134441c1c180000c080e000b03500400250200d0b103590540003c85800002d194645998094122a101c0500c18002d403110440780d01c074824070f00e8440300b061 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 229515152 1250 229513902 229513951
    0x706060306050a0b040e01020309072c36070504091103010f0c14030402180414011407020f061b030c16120e010318140102070209010f0e0c0c0c0108 65
    0x2e5018040d0f258001031805010700800c012189507191444850b401401040181c03007000c60031004540d41c4601116005d9080721280700751030300714000760403541049002d11608000500010700005000040350358014038540040441c41a14540e03020264014001030040d400d09130011800c0030303c212074602102800100007400e450050052884061f944c51800800e00d9210a9141c240104d07110741c02d00d50308181d0080f8650016410305000b04541c42e002107820071a8800e8010704400300a030080003005442c1074074603030340f000030b981c0080188205501404010b40124400740603a0221010200c01035024444401c076420041205101c0f0100b885010701d6040400d6004045a11500700501c19504120001e8000d03101107449034101890002c0c01200904450b002682c1581c1181c440d4010b0f03140c0548140c0641320341440250401e0621000184c1c960a40044000791048180000d4045e9500c50030703200a0301842c0b00303e013501d034001d005584065000380c0034160480c0410200e16800300422444 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 229516402 1250 229515152 229515161
    0x3021503061f121805071e0909030c050d0801080f030a1b0f14030c0114070e130204180203060a050303090a0303030e03070f030e091b04050f180106020303040605070507170706060306 80
    0x4c00b99180610a103801c104002842840701504000045101118400404007d8803009000f007c2c1800d545400d5002414050000e03880c099a0003003c56841e40c1c06508001c110b0702085c418864680725208004030100300c0402540c40301902c070390b181181040100c100310000401c0190544400b10740b0300051020422818106d0349140c4035030001c0d6030307a04000340144e084480d50b004444210341824180600254270407006040c110040321103e8026200108604c02031046510020705d121480409540b01107250700075520902080f80c500340c0313260755103041c9070b141d10404440642c8a02480c80a00029010307601c10402107040034100ca0804a1940e180b4030f500c06480c4050b030200c0e901c110750440900d001401c450f403000e4182088078140c60100401000c078040c0307000d50b40c0708090200415000f500c1c1e201601c00001d0b60b4031600c0100d540d5600b0701070340702d44c0705807010baa0160034440090b801d58022030444880c07070703403000003d4044544400c01d90507036001224121400c9440f408004003140180c044e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 229517652 1250 229516402 229516421
    0x1e0312051501180b27010c030f11010b04150f090207080f0a0201020c0109030917070f1404020c15040203210a050c032208160311012001020d020403021503061f12 71
    0x10300200e40c96050b8803d01415400381250411481c5240700002950040345500403109ca401c10452103a10355050703a000d003050080a82c2c1062418902103150642d040c240b00c01c81d5180601e050f4590380760306980c4140d10401501804409041000c00805180f40008016011051000604041c0085006400e4441c011382c260001101450709000e00c0d0011000c1c610410040402010f08a151040300000c5902c24420000181c442d4204400c00b51266011265050303118800e844080030291411510708100b954264041c2c441e18108401d1a215142c1084c40400c41051003030822421074012110f60340301c03502000e050f02003030241c581901820b402025907040400340f010100350a000a0501c0c201010240d0700c0341201103007040000c0b40301c00841c0280141c0030300c0e26684250301c41c000300d4a07074802d90a4004c2603601c0041c01c0304c01032800d98090000e8034801c50301e070600080d4500d40f401c4980401c0d182d0583c42000141801d08c25412403407094101c00003424120b8030b9085402150086551140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 229518902 1250 229517652 229517677
    0x606030605040210030b0108150a05180a1820040b0d060b010e030307031209170c030406020c1002030a030f0f02040815060a060f0f0207031e0312051501180b 69
    0x70140000c501c2d01020001003050646820008442c024000900b0218041c03c0b180c88800c1141420700b160700c44141050152401030310f560065400c070100b04200d04030864030b41d40ca462801c0709840729000284680420660800c504c205a8400c80c00704409078040096440c0c2d0260707442101c2d455580700c01d0f000e112f40340c1c003441c0c0c00264070300f1100001d41450710399025075100b50030030444000040d4000d50002103816580b080003840c183e175854100390122071500316030030110000c038004407418000401003080d03e500740e0940c3c0c0307082134000601012005840b1080c1c0035030020300008030070a03c00e50202c0c02e209003005010841124002c1400100da100d500820f8490300445003182e0000c128040f81070b0044015200011041c3c5003180052120901c2c40c0e41c0810440322064000049200704a0480555000718828549009503045034a242c0f081d00c508130045800da45401c0034002440c0b1074148100081c0246c4210174502e00c0c0115004a00384240a1290400c2940410826601402750207184c3c2c0d9030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 229520152 1250 229518902 229518911
    0x1204080a02010507021617010e15100503030918090a02190807050d0507030f050a1a01031b03170d0f0504080a08150d0201210c0519080115140706060306 67
    0x100300c000e00307540000302070f0b03030035036000d20150036891500941880888014004036481d100303042c0303401409030901400c2d000051250310380d00d04e6444681030078180122094900c050000d0381d200180764607405501d5489622612900d4074508001039004902d0f4081c2c0681d050715541d203016800658551000748100d010f18a41d04018412444200b01c400007900045406507604c1283d80c1c0d40551f1010a80001064194102d0a80c0c04010040100411841d84810902403000148554002c040ca091000350350581c01d80140c056040da00b8001c4105aa0b0403080c4c0c01302c80203c1001c0d202c050b5110845082510b41d8070076042040c07160b41d00c0380f24003451180c40324550340c18540900805c00080600405a004181012014190f845200e254031055080c01c141500030110b1218074102101b013003d1000c85400e000c0b4a040d00d6602c1402400303517852801080d036401c040f80004491003202400307800311041c0c1410440c1e08250103a41d0300e440c1201f440d12254a4a4616599801940c42d81d41c401c48a0540300c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 229521402 1250 229520152 229520167
    0xf1c050f040b0406152405030435123103080603030405030105040b01050103150803071b0308030a24061b020a03080a0e011205070c0209100b1210060306030507060f0203120408 77
    0x12002082d40807006140960a50274252199900581741d0015502d000c210800c903400c1944101c403900b17500360350042200c0c1e11030f440b0240340054544100c3c2c03001c140b0b034690701c56221088030184083c248407a01031880040000c040c1c1e401c2c0c4d006400a01402d60520007408001016030b000d00405206611420328034000b0b51501001405551056030600500001000c0034092810008165a019030300044880c00c4191000291000c4a0301070f0005400c0440010420428a0080d00721210b0030b42c102c80c806100b00210030103d05200898064600003415078018003020800e4091840c01c22400281550a5981d8982e00d01a207680b095000b0300215135402400278a40da085400c0100142807900240f20520b84180c0007041d5240c1030800920641c9a04085926030505840d081d002d0003c510b10260340b4030302120520780501044900c2400780b020b4840101e4414840d01446048a0780540145181c0d41840b600340c814401e040e03420340451006000301d070251107101c07260902550084075441d584070074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 229522652 1250 229521402 229521449
    0x60f0103180f05070f05101209060905060916081e12130e0c03070e1002210d291e030d110d0908030301050d030c05030f1c050f040b040615 61
    0x14a640405c124544ca00c070100701d13913100d24103111845859460005659540d0714180801001d4044d406040180b070a000c250400600203000740c01680454101c620381c003d00309149014806a005029103504002040034001c020440303030407845e506200603104130345003101d200301c410b40026506030300b940e40340c0c0c0742005110a1a5001781d0000b0310540c0c042c0c17170744c40c1c46200501103034400c500071401690864001510140300b4000c0300030400711901840c40148049000342c60340d4000041c1a0341040c5400c200b501e007400b0011080740e44841e0030b00001c8440c00c40724100a07540e00f0341d88440781d81c0440b090141c2c0d600d40e0103100b400304500842c4c0302c07401318403035607030007186070200140510091191104003031054160000640b411903100315681141d00000c1d1500710342c400310705003004001d8400402c08140c0703081d080001e0914082e003400940320132242c0c01441000d5603015189030300010400d40204000c150718000311790340240581004510000d81c241d080410000f20380c480001c580607016024601031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 229523902 1250 229522652 229522663
    0x519050108150a061d031204080f150403030b0d0510020a03051e041101050c0f030414010f08010504090c080f010905191106220b040306060f0608060f0103180f05 71
    0xe801c022190250800070120380e81c1c8129009090601071000c0c12403c2c1781180e0003802c280307420003509440f5040c00313140e01c442c03194000340118a9180074113031001200d990300103003045501407a4400900581c680751400e40082051030211034020b05003664030004690200511121038000260050b910f440751400107086907005400d9014500c28808038040b102500c1030080c1d08070740c12441001c000040b540058070a8403031407607140400e004003060030341e4400c004070141c422141c4010b000c03032407440e45600440300c110100e400301000c9043c0d000140214246035014021180c03048803d1064a905c5803482480c2500300040889642c3d1182020720411500f8082ca00900240c524410441e030b01582d54155850508200103005800206030411031703000840c0d422440f40c441c034903103000312900c4200703037541035016000641d0344a0801100081500001c0e88560468a150361a0b58003503d41d80c041141d40b4134240c00590400d0389034000c9078501c244022514410b240b0480d0102c0c01e00c94903141540c10003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 229525152 1250 229523902 229523911
    0x30914010305041a0910141602060c0f2b020a090503060907060e1c12091a0313020d120e0f09060603070507050f190b090a1511040519050108 62
    0x14188800e20002804d44041946884070346500d074400740e0b6032a0026450074010440d03c101c05414500e0041c4402d80d0b44440e0380c0201400301c40021003289210050303a48540c1503032060500310040040003950801c20340500307011903107042146100540b910441b5441d05070710030b40d940000ea00041031442c03183c00c01c0030900100019006000c0358038142071b06540742e01d40d510441041c04614034000c00565180d000388a074070080b04440184014160900712002c0c02400034450100c4c1e84181d02045070408016150120841c1c000114075540c0c854003841c09160300341d04102d800003001700f1500001a1000d4040c48602135076030381e400d0113030748a2040112054031003480340d000d00c074603405016442d11040c0031242e01076110b044c180d6840040c0d140003440d04484000906840c007604064004452200c000070a60314000d0045007903503151b680d0081e894440c058002005030340500e000c0b110781101c941285c007480780752814090805a580002c1076030140c103240e60361140100040c1c00e110560700f001865410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 229526402 1250 229525152 229525157
    0x504061b050304060311040b0d0603051b09070e0414070216090e0d030e0a0b0a0c120b09010302010807022d0105100612020f040b0a090603201909030f03091401 70
    0x18801141c40d4940c9920890042034205504c071888070f0100005201210010070041d0b151030307074403a254011100140700d2400101d5050140341401ca21410340f040c07400300510b000502400c4643c88a40095650001c603800954003c0d4540d501ca1000120101c14148204104d40142c400c0c048404400c050811044c0c008a400c01c3c54603100e41c161060018044031059014180001c180b90100b0040b440e00300754407401070107039038a5810070098444907000005e881280d03444440c0b45d60b800070030700740654050310171498000301180d004101641c0308180142d00000d0700e0041d162600b4840c0354042c4101540000e10301840342d000704d12503038030f1801d10a9562004042c81c00c0203415040010081000040c072208140e040c2c0c01051900300c200528080390010030340401907580d40c0f078480801030051240703482040003003460b2044040d012030030140b40e241c4008040c1805450000003690ba56401100c031040001040690b50003c400104460110b1100600070746a112860313191450000303100980c141c81504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 229527652 1250 229526402 229526447
    0x90509090a05060a02180d03050d110a05070f1401060806060306010806090624060a11101a0607051207081b0a0305090103020705100f0b1807080f04050703080307050406 74
    0x4030b4070116030607030440180300300560340c0d481011110b071450b0580c0c4901944401078021902c2010f40283c0100700311409a6020700c40c8603c07211400c80303140500c06c100c2001c190204420380008056840610119100e071911195007814480c8080c00c648544d04103603110750003402400018581000510b00504010300113101d9860014034031502c407003014108174510714101240d01101c0d0018403249141d408042c0101d078840101d100000c2c0340d0055901d00c0c0c2041d01603103a04503050000390090644104816901d203500820a006003c51903102e00c0c0f0648160040d5440c50b01400441d100420201c1d00036068a82c03520320040310b080a981c2080c0484c1d00a43c03040004400094100f000c4c1c03040080d003401d005840d11170034180581400c100e500d04080007894403981c41100181d0340d1040221100c140c4510410781d021072506c0703a07000b0b41a203103100400c1c46540054140c04020000030750052082082d00e190580d00c0c1da5017000c43d04151418004220041002e210143d130180c0d200c0e5a09019503207494 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 229528902 1250 229527652 229527673
    0x1403030108070e040c090213060f090506160501021605060711150406230a0e21090d02060705060705091008040b0406050601180f060201050601090f060302070f021009050909 76
    0x10360700c4696124550f04801641e00281c180640300c41800003d1144103010343d503039841501c800e5409800c9000e05000b10f18094605054240704d42081030a0344c2000d822145802200030b00428450440b400c01c41c0c607590200304440c0e14800300d46c3c040442e107210300014080e5003001d510261460456080d50151944036010003d90550801001904180c00010006610841c8044c2c0d850360403507a80050b4003814218184a14804c0c66401402080303403000c00e85884036181c000b40749010351080ca10103510142400002400e26002043c01111032008050900d040602d954903803c0c12012201d103400302d4004566203040d4144914807581400d00e030314021007686800c0e1ba03201180c65000d000900300590344d40004659034010b94400032140c1c90f1a160080e041d40d00e00d9035459008803400b0303200042d4202804540f855004418407404c0d544d0002c414107950341003500c110000e4001260940f02070803500544000b6031115529003204000c03654a10f02030b05d0130002440700500b40940103c0055201d205d648 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 229530152 1250 229528902 229528919
    0x627040e1b01120906090c0618050102060103021002030415090e13081207231801030917030403050d020408030309070b1809090f060c03090c03030405060904021b011814030301 77
    0x1651402007402d080403c0000491403070010610345100501c0d180c9440251401e2280781d2560310b045510031342c1c4030901c0c03455445680b403e0948d540310700c3d4090b034480c4005200600d003207242c80b061700ca0244101d03030815503150040d0009801e008424008070750340500c180000d65155200c0d0b54808500098a07a5402c00c50744c51041501c21003a04503402504100850b0740d15101d091085482001006440c2e0203e062001038283c1c2e0703100e11400482e43c00c070081040e21a5029020711014103401130385800fd404034000190070b90b80e1000b0011001c2007403c0040c0b0300490032610180025160b101c000710740703c2c5822244103151400750b401088940106022101000b103154004001c4464240e132410001c1d194000c02c03030b01c1c000840320701807007501903c002c01034000d030010050352040001000f00c55640c2c1c03400c81403584030b201354000c85800480c200315082c1541440d400515103110b12040f0007101c40e0503030258070300312800e01407010041d12a154102d820f111146140c00c40c19200301024500d90351408812 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 229531402 1250 229530152 229530193
    0xc0801050f072007090b0f09150108100801050106051c090c120206040513020a1b02010228060e01050603150610030e0a060c080103121d0f0627040e 65
    0x51804200e00c141e1500414001601803c0251903500101c1e811280ca80c9007900183c40f0f80060503000d000140881d0400349400c114050065149180d403c2d1010b420320700445101c1002030424003400c8200600064100b000d119040c020100d17543c405403074403c00054403646120f8083c10200082c207014010000c0b641f07141c000811910710407448940c2c000c040c404140c8031b005951201c1d901c00c107001c00040070340070960001d000c610526030351203000011191a441c00c1e90407005010b40140c0c880f10f000f440d038169210f00720402c1c40d01141c40e6100c0c803065580780c500fa219440400c0c030f101d945440502c00325040422103400e0903102c0c0034112400b0301e0882d012035558802115540d040603100c4035038920b408800d02c01003500c0c0d0b4000200380001003a09030b010708160001e12003215540703400342c06000050710606002020100407540f0701c00c01241682085408500981e10f07030303800882008500010000360720164401d05e6000381c4c0010284002d0200801c95035400c9c28620160411042000ba88000d0640c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 229532652 1250 229531402 229531411
    0x4030f140703121d150901030f060e060f03061e07030b06210a020f160f0c080604020a05060a1b0305090307060206160315030f0f060504081902071d060d0c0b070c0801050f 75
    0x18640b40ca1b4036200480207030040030240c0168910703191000c254189007840381c031b101e0705080c0c2d18001030174090001e040d0780b100d0407591030808a103d61042490001c64203002c0e600107c1614010500840b288002400e40e44170354030501d88010081000c001d00c40c0d4040c1c0c00c40d40205c807400214100090000d20000074820313010070291400e6143d080004005030019203940030381c0c20150b0344406a84500903c1c0c5e6404081d1002e03880794035032a2000585140c500102d171101c826950342e0091446840072041100410281e0850600c44280040c590580b420405a030060105a00174107032410704a1044070344070b000404c0c440415082034000007401d62111006c2d82201c0e881010743d41403c0460400640103d000c1c83c00030b00003401c0405200c24400c4c0315001c3c0c040701103074040304502100700d080e00703036982e001d01c1c030810001e10020705406200b005100d0806a00c0740016218850b9141c01391b40340e02e03c0f86200e81100864080c0444d41c8020300080403215005082c1c284000c01050820b03210b80203400380e0042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 229533902 1250 229532652 229532689
    0x209040204061701090510030b22050703050f0a0f02040203040203010902130603020109170d0813060603060c0206060a0f060e010c06061d010e150405150306100611010b0604030f140703121d 83
    0x80100307001c0080d2b0340d0a00144000110300d00103000d4146042754551000380310990300e80c0314040400004c2d480118030f618040e40c0c49400c83c500002d495007444080d4000500607603240d5601c3c0710020150300c4041c413071402070726401c000160450840c4000741c00101d4a8120f406410081c4401000004000a03014610301460920031050f41e17518402d50031218102d42c1c02040c5608050b000010404541c200525203003080c2c00780c0d0403640e03aa400b4080d030030056118500c1d103043c0742c20b4108130b01401110184a6050185090780c180d4459032114415280d00d0390210b4011b59650380300400302d1003400d80c000e014101d0651882c0090600d04401c614225032103245612856980303010440340d814036003401c0001d403409419a201032501c02c04000240007a031180307401013011074106140c0d11206100c3d28001010040201b81045e066484000a90052000440e01d5040219074a0348070542003085030021482009044982d0603000c20060842c43e00c10005400e50461260554060781d9100480b100c000101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 229535152 1250 229533902 229533923
    0x231009021e090d1407090501060206060310050a02041d04140d021b0a18150506040308121b130602160323031b010e0f030304080703030906020904020406170109051003 73
    0x100c0003444440c0340b00da0003803d4a201c031001d141d1341c44010440d80100c0307a42681c2040503a0b6a4102603032503503012242c160741504401d803a00294909640899000384110f14014103198480e03811010080d20003080301d0205403044100000c1040343c50b01c65010040300300c0030381084510464042d42e41c1582c0c4615180300351a1080500c0c081c0c5906c00c1d01e500804429000c941d29032a0014428000d188040c1c0d000c4060340c041c2c02c08525420501c08a504a81d40403441e14030317001c1203440440b003211000e0400040030600310080c081221090002d4079148020203144141e051070840d0207032078884030401c08552003e0922003000460340c07580c04d44c0702e813841c0400b52005c11140c4a40d20b5065106100030000c0000007924100c0749040305500c500184640b480c11104819000c9503019900e00040b600202065010844100024460381000b9100c0d031154038054105070045000600380c0e00710381c11020025070030f0203503c1a2030840300300b064010079207401c0400017800d0003181e00d154540f2500015240c14210f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 229536402 1250 229535152 229535167
    0xb09010516030c0b180706050901140d150b04080d03090c12030e06040f0602120c061603020f0f0324011e090e1003050f0114150301231009021e 63
    0x307018018070700380e21031180d05103490010b1149170b148075101035510041c4248030021503005c0c000d10488169080c142c44490401d0404400c3c282a039001000c040b05042d2036070105580a0340800222002e46842542c050f02c4909046103145051040b060b0041010308285492000c24070603c54001a41c43ca419241058041401d050b9104841f55903000c0d000000000c000414034015406207091364015402e0769510f81c0d40c11a080d065004034020300a05400000210388076001c103410020750a440e80c20094182411050024465000480c6810711301200004000c3c51030307180c2031803d240d10840d2103a40950303140360000030001031220072008100c6c03040a03060b005803802941030744010200c022889540d880c000081100502c000d1204803002c1c403540010a01282d03043c0a00d034208100a25410318541c1d8950000d4031f840e40b04004240c0656a9030700c0003041c0900d10409503452582c8450055075814211030144010040d58026409180f0501080001282c42c8110261103108491011780742d006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 229537652 1250 229536402 229536407
    0xc0f090d0204200c070e0c03151305041101080601021606081e1311030d020a03050d020f130312030b1309020a0806041b0e010b120a110406030b04060b0901051603 71
    0x1e030f01c4182c2903c400d4900a10514260070b8006010344c40002e0140c4050a5507030003940025103055401c01483c6109000080420300203880060912900a003050300b61002c1e104204100c0300d0549056030078001d040b6040c003036943c0040c07042d90010300078030042c030300301400061100078240203000700800c001c00800420300d4402640c24200130302c0c824102603181070801218505200300508030454481ca031000c403c2c0300d50320300401c035a440d208240c0c0140c11000714a80d02158582e01c4030400c1c5941940c24004544600541000b1300031940158441005040c15400c01400141c420600102014288078610303010b601e4081549a43c00c41c0c001c0c0105110800c1c2c800107452400325046095103116060400082c411591040f0f003500851180a00600e5115503014282920034052462600300400071b440d120040889229404008a580000c00055003603284032968813660000c4002600d82111481c249032900c1500b00810255400900e04420600040d029000301d40719040c000c405120030005060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 229538902 1250 229537652 229537661
    0x702030408011e0c0302040b041829090a0203010b0406030f0902060307020a150b0a050613081f06081c0c14010903030203011707081e0c030703060c080c0f090d0204 72
    0xa4428024050343e484944800d00300103840848240681c00d04010320f0309680a03100320790a41c0c0518804601e031070b00302600003001d03011400f08a44216610382c240d4014181d400d402c00c2c0b250234608542003003d0490703000c02c24001c401800c0b000c9002e104000403c10310030104225400c6510a0902141448401550600910000e140030390040000002c01c205542c1c0422030210281c8600944040300c0301080400c01183d02a4035400d41000082c54140000c0c58420301400d0300b46200403120244035112400c10b0b0a0005591484003c03600c5038080c10070480300e030b008050180c4028002819074152840c0c00c1f0380171007022082c0d030090100c3c1c01048000e102d4507140c08008a05460000e02800a80b40307030040080d031003440381c09600402c00c00050644a0f0205841e411904058000c0440345400c41881031a1210300044e0700c291b125820001c0700d2030301c0500810008501410001032006140f010140031070304000e0104000d50b00c10410b524025609005446c01d0710010b80c9c6011244141380b020dd001030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 229540152 1250 229538902 229538909
    0x1104061803121e0903020913150c03020c010b01030207020d080f0d0c0e040b01080403121a09010b03090f15070c080f0310170c06180f0907080912030402010203030f07020304 76
    0x800b214844119000e401c4454a00c8540029181e0030010314424012950007816005c000e500905c0d0002084921041d5035480041500501c0c004c2ca00d644001d0380e0740f0444246030080d8020a0700401c2c20442c0c00420b100340080c0b86020700303041d884c0c521198000f407034400c5e012070700601c12607020070005003998088040e90902d006240c81003000c1010980040c26000110340380074401c5080c90303000010755108060142c0686d525845076005a480b107181d44018102940c49004100c204c510040d070305640d5196454000c00041c40c40950b0303030502112490514100a10b6020b881d4020544d040e00f4002c0200d403203a1260310340c43c103e08092140e150030140b81c0700300b0303101e0f0744080f1000c001c1c03052084c007000740b030b00c210b95001081001c011420304c080b0780c50301d84841e0080d40c8075070140400313240d40384003041d032800b60310004003044101c02d440c1c1c000422030302050b1a5000001c001200301310f40310300308220004280c400003000c14110b18156000035564400100148508120701c1c0114107014020015240034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 229541402 1250 229540152 229540163
    0x6050a090803040614010927020105090d0f0614010b04030b0910060303020c01080a060b0702040b0f060406050c0d021b04020c15010924060207050603191104031101031104061803 78
    0x8900f4030f410840042e0603a04940c600c00c0642000015600c0001c1c801e0b1002001c400c459000c1c1000c86100c03950f0401c01d0048181d05105040055007000d0340c0310003407a081c1600c6100b81c030b04070090500f0140220354400e018148005240320040c4070490100050b681101c0c1e0201e190750050340c442c0600360070302680d88100300c1640e0811034040f01b0036030081001d01100c10280d0b00e82e84150b880040e03040c00c4d0b8000c0d00c180c58921208200180250425402c00c0046010107450344a580c7c00b01d02c0440e886034001d502480000311301040100c481d903024011119541424030041049911580c45091a0b90794108018440e61740040c502d07a070715000f80000e49101036411100455980d682c5841c80281514244501c07021243d440c030a0070818586400300c0580303060750300802080c0d0138001401641d0344085d007402502050382e14144071705c0d0100e004100803240701840d069140c43c5145403071460300919000e0b10b4140743c1000000c40341c010103007081d103007101e43d24608090040d0038450612101d84054001402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 229542652 1250 229541402 229541407
    0x70203011803020c03011b0f020111181201020c0606010e0301201305010314040b041b061709060f06090a06081e060906040503270433030b0406050a0908 67
    0xc1c0010700005840d5000d019409503186080c0c1c0c0b200f09400c0307c0c5030390300860440310300700b40320940c0c0d0f4452032000b1149061400001381220000130780322000d410203c00002e0408090740204414100303082010501c1074071500035400c168003034001a0329108000c1c082810407605151140391130f80c00750440e0f048065010800b03402d50729090700d0303c141540201303803490f4104141040060294800c2c4104e040604240c0d078021025255503a800300002c90180050301d154078141c0c403260324004404894401071403680c0322205000350814482c030460a00070b0040726290054010070505281c2e111081d41d1290080742d5000050303680c4440364000348041d401480d454415003120101c11130100300219104c0180504940103a0303211000160740d64000c41c0c004025400034004c0140d04061011888040161580121500b6403114049405c4a038003641c00141c502d2074100030302c001d00380b690030707610610303844044c2c1c1107200d0440d2592513941c1c4c07002e0b000904559031000014a240200e901040e255988811440d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 229543902 1250 229542652 229542671
    0x60f060910090509010b040e0f130b0106050301060201050115020613141506120604020102030d090c1805190528110c0d12141302030a060f021309110405060f07020301 73
    0x1070001180b0301400d4016040d030000442d6862500c0c00b47c80454442603c0e4030350742d540c0c1c7d14500361091405003083d0b00703961010040b00002030054400c80e0203031909540c1c46840c5e6150240c02403c1da42c0690010071042000121507560703e501103411a4490095401c0003c8001a85005242003900086171a0703140a04111160744549000c84c207805880e080b520000c420344000e403800d440f0070007510004c1c0940d004104e02c59014440d504000541802002c2c5071b0080e90b83c0301040c60341d80c2507021014100c590346100304031500900304110380340130403031300c10402c039520b401540031841d4041b459820b059400e440503049001e6469400c0320141024600d220342e181d803029440c09650700e018407102404141440481e07001921a0310541c01c1c107441203072030241c2c0e0f500eaa50091288240382c18042c0c0c0c040c010401004080340c0a0700500c6040c0044140040c0d445880f50780c0c1020b80c0000341c002c4410f43d41450141e624003016001643d040d550100e807180e43d214803501c000344141c4541c7d60000d40550030301c00b524 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 229545152 1250 229543902 229543907
    0xb03070203130509090a0308150301060914160e0d050304051302070c0602150f0415090b06101b08030907090c0201091727030f06010e04031e08060f060910 68
    0x20404242c0304120816a0b9440d84108509128121590740169000e1501c50010038454640e45800001c080c412821502800703001c02d0075200640c200010a0341c50741c5100c40c45210120f0442d60008000d80c13404800042910300030300d61681041c1092291410351388d0300040c08801d00481300184001001e0802400742d020211000e5000220140d07070300c80e08484001800c50006c51601c42e1186080042c0800387d60b9180f860309003140250060f108480d00110012803515688503501c901c5004071604078107490070008000c00c41c048800d100c2e041151449002d407007000c1c01d5640d120700c1c96211050585a60354140e0140c5001720983c84420f03010300708556014880d40660081c00068000c03038402403165020042d5081d240b044014000e09941500d10059069070200140c030416840242622800784d2080c213460729029083e00801030500c10b40042c0420540c2080c000090300c0c00c04501c050b011720101c80c01070301d000c00061240340180c11070a0003641e9542da00c41111074681006010030001003680100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 229546402 1250 229545152 229545157
    0x1080618120403021c05191101030204031112120703120501060e030a020103050c2b05070215010e0619080d08060319110a0b030c19030207030c0b060a0b03070203 71
    0x4003000c1190691081900450701194000600c0071840c5002d02d5030f03092102244400082242d00481e0305c2a07000060b909010360540580602000e8003d02201d045c2401080018900203060603c1040100300003040e000a5045440d012503400031030942100d041410300f5800709801d61503c00c00610b0b041050f402c40004002021003050402c01f0307a0301d035101074a400d18001d41c0d90781c1c035a0104c6403610040d07119400c180da00c02c0c10071425905004411001000c540d6a81600e0388610b4a00c0527007080d0621103103d05644011240f00611071604003101c48443e000301809040600d1078414001803403601c1d5158068101000c001c11981c2c41a038600c001e688070103111083d1400980c401010034114680002c80c2614001355204200b181c00039039a80c0740b0507031b540c0c041043d000031002c4400500d4a00040203140b140101495050740c941d200712812140300000c1d0040b80c18107106120200229034044810010158000c1e805041c645540c0002481c002e00c581c810340280000008100000303501001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 229547652 1250 229546402 229546411
    0xb07030806030705010912030e0a06031406040c0c02130222090e0606100e010908030705010e070609140904080702031b01090501050414091f0b130e150103020d14010806 74
    0xe0340d40154940004068450b0400d00c1140d0004e00d0f14001444a10404685182c6113882401d2030703a84140c2000218100c0304150740203001080c3c1d1800d05030100042100d10940c0560101e8081240060b08000940800b144c044081d0144000248202488105038101c480074960010540342c1840740c0302c0c001e05400076070301654800714104942e82c071182d00c2c0025858040c0d94014044009100d85801c03c031407100c0f4409030b2604101d85040c002440050510082c13012602444c00801c980f2401b4403100e10303140c010781c452003c200000a04100440c401100310020600c02c4841d1042d60f200d40c10049218096014080d506001c1c9000e0042581c4803c074203454404000c1e225416015a0750700152554041c9106142ca10030701b0904c00130151504102c0141d00459010744c05040c0120004001b0350640300f40c2020610540014154860b501f0780c0c0c3d003020060081c40f105200c58075001902800326002884000d040c10307000b25014010394441d402407003c0c0103403050a0746240d030755030340640e964013010f68 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 229548902 1250 229547652 229547657
    0xc10060f03120c03120c090b280503090a030c02010e060c0f0c041401030b180d08190c0e012001090b01090e0c011d0a03080a20031c020f0c0102040b0703 67
    0x8905440c0700d0040f02d502240700c2d01601e0f0701c220b4440c3c148a0320098422102041d041025000300401e40c81401000f801e444040340b410004180ca07840803000d80c01c841000d00405000045c070400c6885d041c001122206542c1c10715000d0040e021134401620305400d288001796100602080800e40c9a10000c0d04402c415171140440d204144c0c40e506110032a405000c61150618400300184041058081491740020a02200380c00303c541c03c542d580d081c901d00084071070004034620248441c40042a0503041c1148990300100038035200800e000e0511700651201c10305000c140e116500c52820344800c1c4807007003011031000380800c410764a07141f00070507024050305684a00d49102184000c07400650044420b5068660300d0b001a0703804525008403034040c0700f450307104684083c04400030701907001800c1e48211580b1460300c1141000b441e103000d8200040c20b00b06541c414003c8a5902c8801c8061900c54910345034010f0303541c1d584800340b190521a020300c1e07054941c000940050011a0f0b24014030302d45000340d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 229550152 1250 229548902 229548923
    0x6031f0504061e05040b0d0611120c040e0108060106050417011b020703032607112503031205090c0f010507170a1205100b030606120405070531020c10060f03 69
    0x407401c00c800c4075681985180c00c480300d1f86030000003a509500001540782c0c002c29103410050f089000410b110750031101e200701300d4000300d030400c2001441c00031140508051000b410080d810001c009016026610401c00068030904464020207000c0d0300041951300f8030417443c60781d12900e10000c1d540d901c2d903100c100c000409031040401e00a000020421482d4406003614074903849210040340c40540e0549241814081c2c004481124000b5040b48040c8603e11a00c2d030080300e01c0c6040281c01000350012078582c4074280800c0185114011804164a640c11100b0401d04000000100d4150094a030014106040044004030018814016146e808602c1c0d40354038000b4004a242c50a0b0b810550312020b0200d0011400e02205034228091944400040c260b5800c0c55280482d526030400261016a56508441404d0105041051014041118a40d0303a0520314103401021200d009030615059002540400c0d1b00545580c2030203c0c4244022449040c000a501c0340001166400c1c14441101c035410346 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 229551402 1250 229550152 229550159
    0x1707080f03060d1202011a0301061815091b090e04050606041505090a0608070609030803040305070f0807060605011d031c0201091a0604150e0a110d0207060504110a030206031f0504061e 81
    0x5001c1d04060341e80040309855140b0a02d80703030000cc3d19800960f411505282e100128885050344502d81760310000400346581000070040103405020542c000910b1101b400040002107103000030083d8128505882c00200c4c81d001e002810180050b541085500580060510210b51050341000c0251104201a640126a02c03101a03c080009200080c4445002d0001801083c040c02c040d040e0303c0d020b9100321080c45040c0e96a0400d5500c43c035400c40c2c480755245014020303541d0042c41a600740701c030304140e098000011400681e07035540d501c480c0c4c1d00201c2d02d4140362030301910030f4000b9280103a12840c6258440070405019212510445069014a1515400d2411281e880e0501002c5030617000220709907440724588540901590703082c0c00032801c03007003054100e451000c1c4001d121743c5014080001d030f182060318000c150000c50440300e07480b0b0b004680040c00540d035100103d85d00031800c01c0000740d043e00b43d900160b00b241c80982c0041c0d4828540000011045c3c8a100c400060000b04040000c4a944 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 229552652 1250 229551402 229551409
    0x4050607020c0108150301020d0c05070507050a18021806030f150105120f070c0507140906041a090403020f010c0806090702070e060f06091c1707080f03060d1202011a 73
    0xc501e800180050000e2000c6805003175441a140035410b0082c0000d40b0700a1408aa64242c03000e8003500342c00100000b1b00d800610406015143c003070601243c00181c00740c80c0415100d0030b103800042c601e601640c00200c0d02079816155004070b080940140c0051344030710300425500b800720302c02c0700d1000560400392900c01d415841401114052054484892625107640204440c0000d006007840c0900582092020214201700300d040300400e100800051246005014000c0051010781102d00a0b8100b10700c20000302404050b00c04201e10640360b01d1001c0d41c86080407850a8090700300849035510b84a254200e082d030111842e80308240c00d80fa0300e6800c1e110400b0890f40c2d84264890104400c20701030200300c44d854099100364100000508440c24482034070700181d0400068001043c40100844200b010000f400000c2206e19204002c21800d20b60103071224200c5104840c80d040302800001700103007103503880d004000b4249400001821440315030010280c02003111840b40d05502da185440d25080380b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 229553902 1250 229552652 229552663
    0xc1410030902030607030504050a050a0506091204030209071b0b090105010e06030d080712021c02031b03040804140411210603010e07090f020405060c01060515040b03040f02030106050d06050405060702 88
    0xc1d0701a0050a035640d592170218000e06029008582a01a018030b010100324108200341c0e007140135201400381d0b402c00c034041310b03c2c00c5001103080f01c03900c10610040000d6611461029440030080c2440c1c14007812410303c41d62405802c100052000c2d40e510240100140150321190581c1c42d01103120809458503800c0641c1c443c0094140d0340010103040028080794420f10303800d6060250300c10090300781b94105503c4540c2043e85403503100752a071f0201c1000300d500240d09401d070700308059001062441c202500ca00b0301380d100d180142030b54808000030318003298076540d0100152002d895090b079114030380d8950030110310044c00c207007050b20b20809021425610341031180c0684c4188240081a0962034a030410021b8070381003c030401080e5080c400000c10b80c07146c40060441201d14030001030300605050400111840120360155200828402030000054a00440303030007503000010f9408030002c41c80064090405a040300340c01c0b8580d451000d042046a80020f4002ea100740150342099603000c00807a42c81 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 229555152 1250 229553902 229553921
    0x906060903030a0c06151d01060f17090307080403060b1f0e0f060909071106010603020301060903060f0917040503100b06161b180f060b0d0c0c0c141003 67
    0x180c204000e030300400d031300038140c1c940c10754800c040102d8005211000c028083c0c01d01d40c0a61026464054018000204200840e01600e12402c0000350007049480c010403800c241180203100e8801c0d0b07804070300103001c1003069824180c2d1000030140c1c0c494417803405c24050450403e00901079a50003441030030b0340d0212104010b80098603600c0d00c03981544072007082144200d141800d9040002048803a2a1b5104ea8052a01c40c00030381d1121031804528010320381c5082c1c01640030a0801d84140010301195520002e402c040380e030001d1020a40301c10b02c00c0400001c2c102e4001c024403181d400444003000030351110160045035011800d1b1089050311000080c1510b058400d00c5038091001c01410142a1401c91401060340c01603190540c1b0340450405414604143e401c10000c0c0e2001d20303401d840c04c030924020340c80008291075043c4551450000d41100a0040c3c1b818200a162207046030500c2c10310940e00036117425007103c6003100550b40d4104448403003141c040d02501803442002d03901091802070042d44240c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 229556402 1250 229555152 229555159
    0x40e0111030a020a03061706010815070815031510060207090b0a05060c03040f030b181b060d0f020f1809040c0909020a080307050c03070503120706020901110d080609060609 76
    0x150381d1102d032048000d510800702c1d03c1c2450b5070341c603001c01d410b842d080a041c20030140000405842d410712508900d00b0b24082c8200021601200c01c00c880c040d400f5100c0381e00700065038038007002042d04900213418402e602440407440c1074158104040b6849124045044071340c540c007551240d546a5030354105803051251015008010f09074100050f0501100429900032450140c0b8241911402c40100302e040652064031188810003d1108994000020700c001030040b01c000d142c0e2080070105800f007501c101a0407480380e0b20102d44d500700600706030051401100b00c072004558594840b004042c82d90410a079940b1424029607075400c00b8105650010b0003140c100140d400454540103105001d8034605508980000d0300240014000b43c0c100094840184030b18082c050300d2400d20127041c07500c00103a1015129501210829441142e400d040b10303c000d07000000503a4511050005a440040520582115100c1c61a1030300100762310080c640e01800007150024040d4841004128880c0501c0c02a50360 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 229557652 1250 229556402 229556407
    0x6040b071b05030f07030c0813051f080f09070915091d1207030918050402191406090d14061602072403060905090f010b06071e0503040e15040e0111 65
    0x180c1040580a041c02c030703111f85803901420b01c2a41e41d03200560009da070b00103a98440a1002d0003940742c18078000d45000d101040600460b000d05200038502c5002614162030349042c007000c244c3c00c03201484482c024024481080c007038200e0300d00344105c05074007a00c40e50b641c207450800c40604403114044205654140c140081030402d0002c0744902013940700980407000d21014500020b0104d45426400480b0b01807100000f903189014018418401900d0000c444800001c00c2c080c000c1510007a4901d11142041c0c40c11921402c110000c290368584c0000050202c0549143c40710505000003007e03407040403403c1414500704000b080999590459018800300c4840f84400448640542c46a144404e4003c0c03402003400c1d50740300703c09c1084407000d442c26074554001d16015802110309015400310a030064078980d00c2c280e0103844850f0100d000d41c81c54042640100d084009004040040d08d010b80320398601d9043e00d060140781b981c1c000a00014090085040546100058034103100d40cae003200030101456131 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 229558902 1250 229557652 229557667
    0x304030303110c0c19030506010e1f030308070c0521091003090f080c01020d0509010e0c0a030206030109020f070b100e07050705101d0703050106060305100b04060813020306040b071b0503 82
    0x302c8002c0c1001110030800300e217040040400c404101c054000c0c040c0c80146d1441d0704001c500304020500c4000ea07001c42034030b081c40c1000001c0c0c3c07101c00540e102172240782c403180007802c03032901c2810110010700422805ea41206d8015407d0240300046c5403246003210720880c29190f541051b800d50f008050050320f0040e10814190100c1c41d20720082c21240082c000042c0350a8101d42e041045880075200703103c181c1c2d0f5a0341140d040382406c0055800b003034811180c4401c01403079540028020300c414042c101c1815004551224000d82c0c000a0b5000d0b035038810f0403006149070401480a400c0d41c40d1207490016580c07a004941a58043c40c03c848926030000040c1150801004881000e0040c1c00c14641303040d1080d40841c070706502c0602000780070350712440c00480e9107490000000c040d00e45c040c0c0100044070402c001044015460000c0724100c0300c1c3d40c249821550b80c1e2407401407a09070300890194050080380c00300020006100384480c0300b041542c4500c402a182c100c8040180305607250001c0040d841000a00b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 229560152 1250 229558902 229558909
    0x5150f100509070302070f050705130204080319020a020303210105180406090309050d080301030506060105040f061103090406030602091f0c0609110307150207050303120604020306040e010204080304030303110c0c 93
    0x1194400c4450130b0142c90103246660703044c11440d62040948940d04105e200748094681003030840c102e01c01410055040a0070100d12035124807801841c801e21050380e4030813034015402800002005a001020751380c0b42d00c40c0000700305c6c2c040481107030000c41c0000000081405d01c2c00b0041003218040544145107955540d50320035008001511701981401882c034400a51780d591710b05444403a80c4100c00e080e4a0313514501d082c52812001410560500c042400180030340c03288aa95401190541e00c2c0003810b01007004c01035415486110100c40c0c00600f014000300070b010158000703004108069403400725a85440302100849040d100ca180009040501c2c418003140a58100f8010705014401c0f01202c0e500401c0002d14000c4258010111751020300e11038043d298050009000601c03090300070714502403558003000301d0700701c4c02024244559030102c04100191542d40c0450750160342c20008540c0c4580303461005650707411520088001038180203e90041c9107070700b001d466503914114001c040101009080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 229561402 1250 229560152 229560169
    0x90e0f2b0c0c05090c070209090a05150411100905030d020a150f0b0612041406040b04060c03020c012406110a03030c02100c0801030c05060a0e010f02070503010905150f1005 76
    0x80d81c5030071038400b0110346541c4545500b409000d484a03180e50f1000c8501c10300c801d01c07100510082c2c1ca90040e045000224001203280c0314038440f0b1906000d010341e114900303d001d00081e10144d0350001441000302d0b0407640c100d90680180c4e5070480440700c80c02d9804504aa41c2d2a9032540200b807003038820b5542004041c5c6400220115041120100c1c4a40d05034020411581128800f04070700c10320784050005121a248140051840703c0e005401d040c581070315001e444042c0504010f010540d54803455644c01c0c841da040c0c0e20184140f0000707100388401980800030106c001d010420f0b81c000d510b040002c40e24043c41210507065150005014541c0103914282c009201e200030300f0341580103143c620480442c2c10720840344800084c0d02c03050055410360400910310350898011700d024090400040d00010382114000b02d032407501346041b40d503c8400403001c905100b81903120380d80660800c021042009400306d035a4286207030300795031008503503610304200d000700c0416100c005003001d20f00000d0045040c160b03007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 229562652 1250 229561402 229561427
    0x60f040b0a151a040305011e06050a030317060f03150106020c061e130b13030605070e01020307170f0c2505060a0311040b0403050a1106030114060304020a090e0f2b 72
    0x904030304207940c5e034680b642520030103030201030300c9200c640150b00585100d204d004003420381a136040e507080307041d5507004d480c581340390785507400194051000401a80d2917150969200c00c02605860300c0000c2c444103410560307002c2c05002d000d405081191022803c1c07403415901315009000c0400d2002c0400024140f07907610003105c03440b40b10403528010451500410080000d8010346072003080040c03460070308400700e41002d4100301c03c201c0a50b03502d40043c0c0e0700209503240c05802285061410201c105061098400d5206024040f0340200b03410011010119140000060280d100c034205050085071990107251070103055444071084c010451014403d600c141490f1303800c489054a840c0c1c6802410480e508564401c81d20340e0721207040001040f40d1030704541882e030401c8d28200c0c11541000c11010b01e42007003032280c0b03010721000b100140c1555a040800002054502c1d01044100c1c403030180287c45022168500310f0a108845180400c0700c40c80200e101541c000300100581007450800c111803c2d5100700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 229563902 1250 229562652 229562699
    0xf020c030c01210f02070311060a141602100c05040e06090903040303050f0f0d050105180405100b0f0613050a0602030a090501050702010e090a0605011704020d060207080c060f040b0a15 81
    0xd518280e109080c17005040080c003070b031910299161500402c0749407041c000e00030804c1074180348c20387d1b030b805030030000741078200900d03880c040088002d51000328545043d0604c0c1c3c0120b0b0342810b0700801280e4000b0014402d0f07841176804040b06540e408280500c0060541d148192039004000400110380301e40043e007501021084807034540002e0790705004e800d80020080b0b5144560300e81c0108824a45000d20041c2d19840c17610030307c942d181076103429403203000600b900e2280580742d21034600716907950501d851074104028040364542e944890a41e401503081c2c01101e000301c48811000c01c4060001041d20184145a624042c030b0a08100c011185a00209800c03414403542c00d5001d01e42da680c461100f4031600c1c01104c00943c0d24549800100744900c1c0385800c0310b41c0240d040600025859012072900b50b150840809a0baa04280c41d05010300c0c0b00d100c3c00745da52800307800c0a00c24104403030350049024600a28500d1500e0f1a404c020604032107480384804443d021940b02000a0705824050f00d1650b403e10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 229565152 1250 229563902 229563911
    0xc190312020304180506150c070b0409140c0f160f06020a082712030c070b01120210090e0402010f110f0705040c08060d030e0303190f020c030c0121 65
    0xa03034400900110944240025030804036050040c40502880d030351128005900038456401c150001c20b1140b44120b82c0c0c40c1c00c01c8000142d2a84c0204208080e40007072154000b030550b50340d03540907018000c244000340466134006040c085448003554078140c13601901070980d454504961850003405d2014608412100106800d00707800c0800c62500c041c00740e20301107031500030040c500311170142074400b1211940440001c0c0d65003e80b5002c80c0010340400c0008107845010b0baa038a9141812149004108000b00b103802000c00200e42d00390286030b00e5032014400e55601c0700444003c44240c4940384030740546c1821b40340c4480020f0240d07120310319585124495013865a00e403003000308030508000359a0a03141041d4040b42d020041c50900f4803c0c8001c2900c01c1c036108105080c00c400040c03801240f000701a04110382e100071644265014002c544101c2440031183d06070b1150850b000e40582c00081c3d6401c05409000020411030401290146444205a55140c0140c4800095110402c505054418803a556 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 229566402 1250 229565152 229565159
    0x20a0206030a0221010b07060e010e0f0304210b070c030c0204050106030c1103130608150907030c120b0f10030906050f041506150c150906060815090c19 67
    0x1000e008602070400008003680e5041403a04039200552801400b50855811400402003101c45a042c0c0300003035441000412130800340e2100314050280500e051586000e440c00440055000100800c22a080c043c0024111705411040041d0484002c1015000c50000da0004903858800d4680450103031203800d0620f0002d4454011600b01c810036081070b00404c0d910b500c242c0c0c0150304004485c2c1071301081001186041e450b1607020a42c50070b144501030034410560040303440d0001e01c086217a141880601400014580070b84010090140d25240c100801c0c5038010290103040c450080e070340000d0010b460a0380f050b41c5d0105208811080c3d492480070180e55044c0c1100080e200c2c001c02d800399080c1035100307682c3e0a060070170804010722071302000e4199183c0b03201000107152140780c16004019030709005503c1e04080c2800764032018005604100e25140003c07440401010b584210141d8080c0011070345070310030034a808010101c0c181c0e10613075254000301c079a141c20301e0305c89007203810090030001000004e5507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 229567652 1250 229566402 229566409
    0x50c060f1309020a17090714030717100501080316150209060301081c08090d12020f0c01060f0602030909010902180d080306030105070309030e10110a05031207050406080a0c020a02 79
    0x4503401c030740b02440d0000ba4030542554042c0041070510640c0c0d103504c0c0356040c0501d10a076141c0716072007940349010550015031400e40d0248041001070041c1c0b013030090607940b00504c041c0c580d61400317031300710b00f4900d81000801c1c540b40003c04d403849183c08404c800b802d100d443d25101c07110141100072000d0700e40c08228000242c0c850101550080001c080148500210b860780c0c81011203141c0c40704020412880c0070401802d600260020b0f44e89014140343e424054030b41040c03000b0b80700e60751116280000009800705003403015403141c0c00f1222412580c110031034490100b00d807a40b140c0c02016501c20304200051000c044070340d004009010341440c420302c100c030b01c400111740c95003003d000c15038104101000704031140c1406e000b52640099145010860801c242e46c0c06010325440448850003000c08005190200b8090580f00f400d0032940c9045a11035900c610304650740c2d90001001030110920f0702c3c0400c44950080d002e640a880d080e450b0801d250f0354806c1681c00920300a0b000c201140705200b0b40780c0c09603c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 229568902 1250 229567652 229567687
    0x4050406060e040b0f0d060b010509270702031305130b040504030c060b040203010b030f040c03051609061703190323010e061008060f010c1a0106080901020403050c060f 74
    0x80700c1d15070000300c1d07048008100441d804804c615004102c910b00401d020307030340d1543d040308055010f02c0020ba40360000c40102c0c0c15000d4000035541004030000704001d1090910307050702d0b612202210344040e030364407188120707101d02407800c16410004605170180800c1c9040300f085d8100304448030700094034045200029013600d0050341c0c203a02003100c07441543c062061038020031a240106070303400d514551605c0724180f003500c001441d0384014401240401c040103c0c0310403003002190001c085600e04041d100035400a0a000d201c1c3e10036861074400001018400003400d02c10741c0312500090360070080000f2405481400f80102d0b00304040c1d40300300c0809641c0505203d103a0800150140603003660401c0d0303540c2d82085004d44010710950300d0401001e004d560010015510000036100301d201c0e12052001603441c0b080c1c0c004010200e00410345c2da040f80d0204420304604031001952000002d456900c4050b00702c0c481c6010140154001e1581d020721420035030300801d0030351855869140f40c40d00b4a5900f00c03040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 229570152 1250 229568902 229568909
    0xc051c05040614040501021005130b0108060105130b090f0718060e0117040c031b090f09120908030306150f07050c030607020114181f050105031501050607150204050406 74
    0x40c801150600c9695807203a6200780f1940c1c82a2824945420700001075034030300706402640c04407521003000810000c0144054208241e11041c1c1d55619610703042850303240c00c0d09006417805200e45520101c82c41c0614025100b101c50064a60445515041104020020b0040c0303003005101c203106580d2031240303001c98404006c110313030760f202410003c00b8070004052134004d96462200c64420400d101c0841d41c504440340480760320a0214090ac1c0e1a242c942000002c0d50780300c0301d0360300e01d0303e00c0210700000142c000004c80c0344200701702c0e42d440607014000d50301a2043d005120041d401400040c5007414801c04141100da40040028248000c2028104455001c640304440030f07004041600780c4c03401e0400074150002c506000a10512000700d4403070207040b400801d40c1d1f9510800c042501035a41080c072107120844040c115030700b2010200c4004402034602840307814002c2c458403290b4a0b540c03c40e81000d074140c8000519546c9420425160200c43d142c451405640c420703403c210009041d9150302c580c0006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 229571402 1250 229570152 229570157
    0x6020705031c050f0a0e0c0f03010b03010c0302130e040305071e060c050903070b0915070f050105010b0c060603010c1403071e030f14161d0a090912020115060c051c 72
    0xd85030030310f1344580d22038029111800560030242d41d01180c0300040703050504440d00703456918070f143d469000640034000c25032610b50907528100c0003c540580c0340c1c00802c2030013065144010695615101040080422203010303000400500103180002e070a00004a4001280141d0111441e00e546030340741120f00402c0302e400410000991040241801d11910000348404a02c9070704098405020074451240060221441480001d40300e040025906000b540c068020b0000c20031983c60300d140395801c0c0d000c1d05c400c50051152030700242191905004403010301c0282e584480d13020340d04a0700900640c001809101c203101207812107440480c22100a40700c4031031281d40103d000e0460304c3c1101c0031134007001c1e501c02183d0030510030014004455004500d20700715500e480410105100c440b944084c1ca000380d090342c40300c0300501c0002c03078a415401007900341c3c0c002c490b0011035906084041c1c0c00c907594a03105001d050810042005414003904400050900620030382e41c140c042e441c0b01c0d00c40c1c00ca074208420301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 229572652 1250 229571402 229571411
    0x705030c1315081501021903021c030603051c020705010806040e0f010b0a0f08030909092806291507020d06020307170106090b03150d0b060102100207080706020705031c 74
    0x400b16844030f1025002400d42c0700340c0c0480514080000d449900300310600c0708032a03540302d6000030180300304466648c40c1c1071088060f101d0640136000034040e00480c1701c00d4400e44581804015104804192054070140580043c48036900c0d02c0015102d410b0b0040540c0d50103030343c0d03c000800081050203084c0407146c401e0000556201d044042240d212000d40010380b00c418040000d01044000208850a01504072040b154030742d41c041d4407070300d068220384200d000321008404c02454602a0003014040c14400c41c400e00c8801140030742d844010150000d9518a402204038141c0c45041407001c45184c1d10305000d469203012a1074020442800d00800e00f112002d50010800000940c48178030001c2c514010207402c030342945031020081c4024024060b00d0029900080822040840d1003e0341007070f41801350110040314054100701d952040110741c500c0c058083e4100300840e03031555100300c4450303c0e03020301c406003002000d40f1410003d40146601f240d040c4010007542c0c51240083e0640400b42942035000316 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 229573902 1250 229572652 229572689
    0x7050418240e03040506040306020c07050a08030306091e070c020f06120f0f0c1b0a1a04030210020c03040e040c0306060e01140402070c0303030e25050405090d080705030c13 76
    0x880b680341042201c41c2e00180001c1c003895554108803001ca940000d005a10782c101007891324141a199440315074424009803000400c000c001c40990311442c403c80c0d00c00117542e6250203003c1c0e150840c401c5188844820400254514000c07180301d0704980c00981807005280749640413492550080380c0d00d44103d903800d010001610a2004450390008285c581a805801d201d545e44543d4011494203081100000300c00315142c0c003040007426440c0381c02071a071550f1900414039121841c06c09403029001030060740309581c00001c0c01d0007142d90a018003002145050720b4151340c20550b20015000b159000001040003010984a014110183c01d039218010f00951500b2040c00000506010b07243c000d5005010b880701051710b030038103002200c1c2c06060106203000d2040380d2500306104908054140c0342c841d0a4140c0c14441568041c3c203031002a107040110740c0380e00c61100d40d5107001e003c04000064050b400104030601c100d01554110003010b0b81142000c07038400c6045a05201a001807000b140e240d0307a0030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 229575152 1250 229573902 229573973
    0x7170a060605060c0a0b18061e1e0c0d020c01022a0a02090a0c12091407050105030105060a030c0c12030c0e3003070807050d0e010f0207050418 63
    0x40000c10b070032100b907850006007200d0f85481c4c014101c4043c0c080454000051018400300480034418903d4000366052850900c0080201c0500790020b140d4a80040000610030368202ca0407100750342c1d10300c807100080d6a820f0380b14109a48900c8407000b03410f40900145000c030609001034160f50f00b202d421404440002141003140c1030035541440800ea128050360380250301c0b40011150021580040401d02d159500006e951441c40c94039896419440c1804020900a810000d422203201c094151f0fa81103a9650044500713000a0003941d5101908201500c2464000c0d44800088c0d600d80c1405d101c507034159181c00030514041010301c00413a03203071405c0d107500650000c01000481740c1140c0040003c1c024030540035800171840c0030900442600642c0c1446031008109440d100d039402400d081d40d9100741d140c040e844415040a00d00415816041030b0f28030340c040c940000720700c98143e0003805105d02e82002c00024100400b20030000c03000480405000c103428043c0445514402c1c6048400d018003072240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 229576402 1250 229575152 229575161
    0x30618151005150f04050415030f140c0103060e2a0703020f070b04060c110a0b0c01060e090a031d0d02060307030213050406050105071106040f0303020d020c100e100207170a06 77
    0x70803074011010400e041013920000142da054640980d000141c0c410140c1000c18584034036000039080701c94110349841080703401c0900f95240c02c404002d032171032903088800643c1503078081e0007030181d692150000580c03040d424002d8425969051220200070762021a036202c859440b003101a80142c0000c001121240810090f41c00103203a4207403030901d004e24205005292681010008290022141c0c0107156599040b6126000e0522440100c3d592000102c174a0b00030140e42c480c02e0b40e18642100020300702d91000c80c03854000c03a0507854550485440d03503800c6101442c0c18603e960320440040400c0096210350000d10b01c505003c1d2401a904c070304c3e0300d40c4122400030a50065202e00c1c108038090216076401030503502c400394880c0209030007034112800101e050086410181c00e5001e0380c00008141a40025520941e04290302500ea0b050314a20900c295204505484804600d8843c4808003e0610380c50001d1046000e00c140d685660711200700170211a6079418071a8164000e505600500285214 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 229577652 1250 229576402 229576429
    0xa0e070206010e040803040303050709080303070c06060e010b071202030d150e090a030f1b05011107020a23010f03090203010603031d030609060609090a05010f060320030618151005 79
    0x400703d541e140c1641c42c8192032200030002010582c41d1030214801c240581125000303860014107a0391030b03180403134008000c2044aca10955203142000c2d070009410209801f424164bc0c4a4145a0302e00703036960320b1f4904111820520142188010000074500007590b101740701f4001410380c074080740c052904811a0300240702034010102900700004000020382c10075604080740e80141410100800105c080e500c042c464164040c00e0342d403c01c44141600c9410100030005180700725050328403140c844000c01c9000e812006500500680d078107040d0350960003031121000e060942e10f030210b0040003070350210b4203403032055108030301084401c0c0b02d40c00c900c80050883c007030011096004010a1410380c90b000d55580c0041d20303580c0103240d4540400c0910609002481400760032038020307c4400d0b01510080001c01b0988420340e8071004a48041c1c0342140c1c009100384510b90002e000b0455a155500d20303003440604907050010a114142c060b240d00b001d2660524804c0e040c0f401c20041e45482d00080c0321800c400c406 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 229578902 1250 229577652 229577669
    0x712021f0215100506070b09070605190806040209120d0f180314030702060a0503010602070f06020d0e040605220507030605100c061103090d09050102030a0c0813050a0e07020601 78
    0x10220350a60358006111000c0120300ca0a46005440b03075a0301071558002500101d412840005080c800c0c89080703000b0318000ea041c50200e4403c00c0d0744a8013200c40d07000e50f40c1e03403030381040c0100602400c581c1704403282604000010401481c06030300300c0010300c4407a4001182209038008a01c4100c2c40d03504002981d01d81c00980c20704020449060898048803916804001d1003000202c4070396000071010000c0d100b0169018059541e00c6072241005440354200740303d03080c018410340d007021400704a420a50004c468481d00240f201c080008829180c01140019203900641e58020000d0f050396009959903100d00254031820240d0741604900068440c01010a0149400c03d182001907460381030410b01601441d01d480d005105451a02c1d60290507a203050110030711000c0148228800301180b50215041c0d10f40349e01c0c00b0955903000681c1c5034040c0200031004103607070010582c01f2076494001003400c0444505c40c035841035240d5000401c00322064120050310302ca500c007000715590301000014050305401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 229580152 1250 229578902 229578949
    0x3050c040b0d020d06031a01081903050d02160501020d0204050906040612020d030c050303070305010521190c03021206061201090506070c02030c10050a030c030513060b01050c071202 80
    0x8011249600c100164208100d40c00a0704413030240441d40210082c5900072420700c031802c1400141ca40d002d0083c003412006014808180d0503d02c6104418071205a15448160074101c090031004020f4000800540900403180c081c0d13000201c00784001c010700f690138440183c0321030600050060181004001030b004030f180004c01d000300c4d00305040030b014a42c1d04503450b0b40d01a48501d800c0360144202e02000b041c511000c0240304c1c0b140e030540c1180d4165203043d107845680c9040f1240c50340c001030170180c101d031158100030328003181d0717400f0701010007a641d00139540d80b0a0300b40d50742e010906030003601c503402c65590440d000b40541c07840e01e105200c181c0145c0b00e000f88003106aa40383c0d00d8407084040c11003001d000250708031000b1900e0900000850040081042c0040c1902c150049c1055001480d030000092070400125021f50207131040303c1c09503441501c0c00d2301c000580da80308002000c181e0400341c14003c0600200f520024100107020103007001181098444085105010012880c04100301c420002d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 229581402 1250 229580152 229580159
    0x90b0102060105150702220b0909061501180302090c0405150a09060305151008070e0319021201110a0306090b0a14010305060a050a030803041a070c061e0c030c03050c04 74
    0xc11040e0041c00c0400c0040682c5c50700f142c800140d00c40005030103031180c0c034090000040003200c154042c500100003034031114003507640d405a090301e60340c0441e4901c0c44100715200080d01c9500c02d142860000c0031022810780306988a4000640c41c030000c95110152450006060242c2d0611082423841d20202c01d03011801c01420b0b00d07024105034a1790090b4001c041c0d0341c00c0040c0903414180e851200340d003400741403008111070401c0c0040244000700c0d0000702280126091800c3c038280001c0380c0c400707052a09001c501012241d800c01c210340b8058404001990740704c160301d0a035051414003c1000e41d0684d200060b00c5840c1c02020000e5480c034050103480740c1c9200e80c0c20405814416100580b041091030001115640c44001800a07001d0b50001138100700520004070410980f90019405079000d5200000011350700e04c0204016107040b40ca00d00000e4250340003a00266180e0444411502d0040200703e400c034640720030724210b80c2400806030002e91a41080c042d410b401d03101d0150424a81042035241908 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 229582652 1250 229581402 229581409
    0xb030304181116050a0c05091b1c0510060e0109150302091810030309050d03020712050c04110d050a06240509090c0403020a0806130f03030e0f07090b0102060105 71
    0x101c031280c00c40d03102d85071181d40c1100e86041084680200c9080e00710b44406480f8184140e41c0d64001404441030701c2c03810070100d15460b0100000748501c2040b00c03814400a40c11201142941101b0240c00c800a180c441803040c090150040d03d205000f03201a002c115480c02d0002000520014922414070007900001c0c0411440228164120f515070b080242c1d4515482c004203540e00e0055400c60300e0550b0a105010b800e45615401102302c030301aa03103810b42162914208400300f401d8000040c0580d02012082201c91084900c046180e4040c1041c0c640408040c03001c9402d6030707805442d0511b82d440018081108070300d14464150490507607a400c0160b142410340380308101746120b446030a03c0411750f054000ca144180c003114026100500701e0f0f480c604100740c41c4002500306010891140b80c801402180602c00021300c58819141d5401c24550070070300d0749890382054100071050f802c0545851000c5074403c42000a00941e05002c00144111031806078913004981003083e005046401c441d004000598 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 229583902 1250 229582652 229582679
    0xb0c0d03090b04021005160803090f1902150f030a051602030703080f100306140106020c0306090a26031305060610120203100f0807080706140318010b180a0b030304 72
    0x96042e244101c5c04040f800d411356070b5000b0140104442003686214134100071b010300188d030040000340200c2d41e1050494038110384940700800b000007220f00751028100545803030104d400c10413a541c080707149041c104040c2c0c500c45a2003255001c8074640c03200f060050f030341c001030008620080d01e4405181003614136580148a00030140840094406d81c1000c50450302018141e03100860384144100203520a0b5038402e1a01c034000d101f01805401404a154032071304001c12010f01c104400c4000d00600c24080d03070b559800c0000030071640036440010300034540b0040d89500850003103803051241441c0d1400352900340c0c40c000005101c14081c18464042402c03040e0025061028144195000368407551220000c060489065000030a2801b12070000950080041400800d451003402a160115250301060f90b0301c080e0006440c088020810004814071412540d00d8000c1c40104004075982808000069261851001d0a070048416106209003030020b4170648140100c20342c0510b0030603240030032209010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 229585152 1250 229583902 229583911
    0x4b050729070c060e0f0f0c0108190f060308120f1501020304050603060d05010903170c03060d02100311030a0e010e0d0c020d0f0219181104060e0114040b0c0d03090b 72
    0x2c0348842440c00c2060741d030880881c03074483c84200c8044115522000d666140c0c0d8404108690252044c2c0d40d007554810303845c0380d100380c504010701c2447c800040441002400d000e020000241e68418001c000916494000c0c4202c0d405040b1302034050a00c0920b031100398101500b1110707034049200c00b030142170340c000c000c0d1011a242215000d8581e40c1d4040482c61010b1071010050982d442c01e1208000c15400020143e00140a5245404241d8903082c400030540703c15142180e1001480e60071400524140b6000c02d64583c0342d26000c13881903d10480ca00c540d800513146c0800160322a251011061024414842c0f441d1000c0024040170ba00f0100c090710b0012400c002038040c0b01015141414004950b12402d14681d000e0b00840d0741c4c845a408004c0160320a0085000010701000d0100c800070140c0101c016500701215001c0c50946450b006aa02d440c4000f1414140584024003a442d03c000300e000e00000c0500d050280d60365030700100380e1818060ba40100c28103245c50002910007103940e80c160142d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 229586402 1250 229585152 229585157
    0x91009121a132d0c0602011b02060702070302060d020c07090e0c01080103120305040f08030c091206061003240b07031403010e01030602090d02190303030605014b05072907 75
    0x42c2950400743c5403050340d50075400340100600050014080341d0551211809402d52180d59540000810040340c075040c040e9002c0b00180d0059400340701503d4044000c01000d90010030052a0514001899003880c02c940e00214549588401d40e03480f074079007031080702036408003460208110342c1556034940d1080c06a40c0050b00b003556500c000313420400070b480880300c0290088401d5889203010075818440c1d030701c0110924003950f000c01c0010241c050000e17090740501402040c803007040040c00303011001400c481d460001d403050721000c11401c03d12045441d00c090216486120f90310344032401c1c0548050501d41003101c10000070001040550038001a040c1503981c01070f005692402c054000030082a0440c1c406980054503403000c8081c1c0c01402d402d4022284030f510700b840103130340c0c580054411401484040c48040c50b40389040520050140090000c14a410243d45407800b00241c5010769844035000032010960005441083c8072070381c13500241c0c25128108990301110350710008294050060000c0d401e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 229587652 1250 229586402 229586453
    0x7050301150e0601141204020f18040b1012050f01140613020d021309090203010f0b030307021908070b0c06100f030803101e0306050c090105091009121a13 68
    0x102030384601052000c20502c2080240c51b00c0382c00f0040c24144405940c04c80c800c141a101040103401c150004140c14ac1e20035054607925a1641c6408901c0400200b521442004481c4082001e00c0b200754800c816038054401032a08580940c1e015003112400f0640c81004c0c1010790070410640d8940401e01c0e00d0710000000581c075040c4102000d0301a005860201130603150580020641d14050780c0600c030114000c4001340303c0d1001441250303088070005034040350581c10030040d4402606040d103000d9628150b04651403003060f44d4096150038450b0503007000f100c820002804180c0700d0b108004a0b900890110201559a80340000f00d480f0110144402003402002100041001000000540c02005940d1800881c8040d0300402c400034034803070004580c0d0034900400308080e24107410603210307001e806031100b6261100280402058a401c818480100300c030781600403411981034441030078900d12588407008020980104164a1640100501d6604181c040c6450100700c02d02c91040031814008120032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 229588902 1250 229587652 229587661
    0x60908030a020c100923150a09050c010c050d03020705030904050a0207030810060c0b040302032a0106080312041e0602160b010b091f1101060f0602060612100b01270807050301150e 79
    0x2810025807d618003c642140c504020802c02990448030866100f030080c2c03007014440e200190743d140080d18000e0247c0d400008005240c9000350b0017401010301940449041a00704400a02692802c4602d10100ba80200b0703c40c0801d41c02c400d203660801e03014070b030782007040d8180b46009002504622001c0c1050300704402040506000307100311440042140c0a0110310300002007049d41c1e400c101ca10181c840d40c41c1103400150442e010065039841210410345000a442d5900d0b007040d505e00c1e602c8d4045580071a250040c00003130180c4010314040d800d60a80c1200540c080c02c0400b4203910503400340c04440810858040f02e035031601c0303901c0c00b000c5861982c966400907041c400c0f01c4045801444444235071030800d004c60b070706900f142d100b01240c446908440342d81d074510341842341710301180345c21402603800312100c00301c000f4082d0085540d000b01850940c000041002c003454101c40c1c000c107250704040031700e5002d0040507024080e2601404095000344143c0b0400007001003a20414412042040d03487e20206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 229590152 1250 229588902 229588973
    0x2707030b040b04091b06020114060d02030f03030f0f160215070905060d0207050705040e120c01320610050a1115010803031f0b0a0c060908030a020c1009 67
    0xd010050b016000700004185450312a4208250710030f01d11060030100360000d8114414015000d00201618144000d0303214241400305e000036000c0100e9060046243c0c82d0000d010420141d44525132f041c1d440101c0d800c221200580040014103110b09011100382c9240704150002030820024180002010056480403011540d090080c0c200e02d0b4800000900b401d80740c1d5482d005040103070f0140040ea900681d070303541000308440024810300300c107420081d241e411982e9505c018040210706a400407403880612440d450350761010b428000700715517500c8510351081d04541c1006900c0a000d45600040d0050400b01624500a0201d14010045003250300f186140d000e20102217454040a10202996150b00243c0d4803900115a0350660300c0058030001c0b10270100c402060101c450041c0304916004c100002254244040041583c034541c65902c00303c00550154025032080d40300c00f10050b03c2d56580d50f00541801e41d00a006001e01c0d050190180100748034541100d02c5142c1c034803409034a0019030305c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 229591402 1250 229590152 229590161
    0x60e0a32030d0c020306091501170c13061502012f042c100e0103110402070c170709020408030a0e030a060606030903080a0c08060103050601091809022707030b04 71
    0xd00d815014180e10910165009142c1d444004c1c070880a03105990f507040740c11691010003110351064072342c4100042018100611100d045601004169035000200c00d000c00d40c01c0034205056070645a41d1082004204021464000951a01d01c024072030030102000c2c06884003d8801e141e101203843e4100e0040100502c0c08a400802202404a00035002494035660422400c3e0b040190390540030b002400d1404c04000303180c2a11041c000203055642551140300342c001c264142c5a400c40e9080141001040380d05a000004104442e5104840d48500708000e00304402a03000100140c0107006c1401511008000da4100304c07510b20302551181030030800246444000880a00002e1906001140682d0300d034200c0107940e4000e45034020f0b15140c51542808036550388580341c00150020004c650780790700c00c1e0415034005005142050241d5180c2440d4400c1540003424224001d59a1041004508101c0c0e00c1c0c0c4084076280241035030088103400611403400000b0b00a0013016900d0040b4031466485501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 229592652 1250 229591402 229591499
    0x10090b0a030605190506060703020a0b13050609010603030908160510030b0d08040e0c091e011412060406050d0f080703142a0303010f0e090f0610060e0a 67
    0x8051000b42040000c07244209250000400d13020f00348800501c0a00701041129102d035499402041d000540d52a1981d110b000a440f20105483c01c0c1c00303180110b60200000303406154440700000c3d4251840c60b0281c48806d8960210301c05800031a1340304010b1641c80901c600f1150b058845e1088003488100c1140100008030032240d120300c0b802c0d078003c00e1140344805802696000d0b84001c100741c83c0c4100c0c240890003410320392035024200e512600380c850802c04032410792403410705004001d0000d02c011403c241d0071105445580f80140d100300b20403840c00e405810010300041e01d00741c100340407a07140c0070803100f00b0980240c191031000803030004051246161100b1841540e0841703450700c0d103050b45100c0000300506a01401050701c1180d0700c0202001c41100c0c1202c04014034414894030b40412503000c604000e00600f0240070f0f0790302041a41406001c80d0344030790001103401108501f4000060030042609403840d0241c041030000384040a0040e464101d505100030800001102030340d20000518070510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 229593902 1250 229592652 229592663
    0x1e031501021c051e0d15031a0402060f070f02030f0d080112050d0f12060e0405100e060a090f12080106090803040308030c07110d0b06040608030f09010302030910060e1e10090b0a03 79
    0x4000c01b04814846100100740c9206244000c88042110354000030054141e402a45c0102c040104203005e102d080010035002d8444d29100303c03901e00c107800182c10203070540c09180c1d10340c119031101c010195010b541c00380942240c509111031a0302546599640380741d02080380b0180640d12441074110b03070203850a46908140c852052080503101d19041a03080825201207580e031050b0082e501030100c140c0111106900428011300543e56070400d5035001c4d0103030a03005d448180000c524480800c040380700750f078407041898071080c0981d4034111004010310380540c00009a50000d001c18030010b051a02280e0b00400f10621494a40516041c0103941c2c1d280c02b103847c0c1d8000c40706c005a204002002d01c50320300c50401118104455551910507545900c905241d000030044100144030a0350700903405503802c080940100c43c0b40c1c2d0010040348089446503003200d51410320103020001058428140303010400c1400c1c4d5800c00f0790030b03c07113415080d8403001e0240052260f10f8900d000324607101d40c4100001990401d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 229595152 1250 229593902 229593911
    0x70215070c03120507200d060509060601080115080a1d010207060c03050115051e0403050604060902040f0c0804030e130606050c070b040b0f1e031501021c051e0d 71
    0x1032600740158070a80c0b00c01c5800d180ca0341901102d060207482580c02c01034010f00d000403108080e0081d4841401e10004aa9015101707080090204a00744190b030300c51503180d07000b420b6904184002520000050340324405800120242ca444554002c0040e5004403010760045140d2002c0e0361041d90b607020080403415650b1011800c1d009004850300690b40c0c61411303441c00c0000303988070f2484d81c0e072490071100321002040d02000703025904010251041c200241d291421410182c81c1d999503030a0070010340c0c1c2554403540310a41c000662409228080452102020410901d0200540506a83c1c0c0c01003000c1e09011081c6188007880c3c6540b200484882009101000415100c03240949950402407540e5510701c100500840c211400c0011101680d195002440c104036040c8841c110a600c06504070810104c91802100300c42010400b644c028600c54401920031440311000a1600e51000310080404402d420b5500b0300713135008011915620340c0460825090082c13681c0c024031500c00c0560745034181c0d240c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 229596402 1250 229595152 229595167
    0x3200604120602091c0b0402012d120b03030a02060906010b040e2a2d070c0e28061403010b10050a0201020918040309060201020a0503011412010501030620030108030708070215 77
    0x3400c1d06c2c203218601c02d0b00d0b1112410441201c28030005480503a40c07400320340300c40314500010f010f0040c8500c101400c030804a01d561034440071a0854001d0101500564040003d00864200500c10103002d414401d0300c140c18645009a06448040040c140b0b81d0b080074074078000c01d6a5244074540944d11114030b000e440d69000c0a040c0858a05a01c0d0511408512600c54640060144108a9034050317000240d0100040c241b45524640340e0b00608101041000e484000c0c003030380303c08180f080101140c040b00042051034030500d143c0048039005010320992428404c9812b070359031000124045541131403c0d94964000c46400d900a11400341d80680c882c0d6114561031246100c200d006116611076070340c04030440e6850074241e00743e000703900000000c20001e000500010103d0085103c1141c0010070027030404902062150071144c013a00151403444e120800c003c40d00d81c00c40320308d54618044898051840d0b140440994990103260002007104100041820039076403a07284050200c6d0840755029910f482c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 229597652 1250 229596402 229596413
    0x408030105010f02010504050c010e0d14010b04051602120a0e0a0801020309010e0307170a140a020a120c0f1b0f090c17010803030604050c1303200604120602091c 71
    0x424464280050329055034030f00303501d00c107002d41030060f60320100034105041c20780015200841d602001c40d4102e11220300d95800700d10304c40300c0b44980c504101e00002e00088001c040c0429210002d000300000d490b000b2034070580030b0380040c07440d00c5181d80c0741d41d003500c800307010508071180380011860507800203440d0004100c205066000b1030103924100d00802001d4240c100039500e81c003030781a0160001f0700380c01803816000b1000c00282005c103442d250040c000d01400c100e4510940000400f2001a032180e0810405c010910703041c40400e03c15400c0000004045a48014400008410081c88006034500540c81101541104000b80c600aa1003507203041d00c80b143e050060040c05049000603000c0e4010840703c4d0300305004681030b20f564201442c919a115010710001c2e000c050100150010200b040d1352082e00b045407200c02451080c0d0842c0b0416030041042c120803000c808449102e008208002c2001c00d0780c48d14502c4d000e56200c0d00150b203441070080011a070345648100740c3d07000c1100700380300000c000c0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 229598902 1250 229597652 229597657
    0x20c010609150e01030804031712150a05120c0607050f06041a100609060315170a0201080a05010602030405010c05030405090112051e0613170a0f1b0210260408 70
    0x20b400c2c01140d80c0e03d03034860a45001520a10015018820800080c0081404104190400510303560035910b092010b0111151003102222481e0403800360010241282c07400040c040020807044492188920100380303400c1e11000740e41d41070f611400c0d0010740801082000d00c40d0340000c000d42815144140303007d0070800300d001c0107241c042d2011141d10700094030104603240c000081d00c010780d0700c1c0a801402d0510650080c8880320501524010349000040c0a68140380c90701da18100840207802002d00031300c00500b20007000b4060348019402c1c20014002d003540081038408894003407a152401014606296080d8402d94204c0c9420031b990710b00104008007150181c445662240046031944000c688149004203040703000702c3c509130412000f0500d1000100d0ba89440310f40039400038a031214207010b205d52583e1000b140d1001080c0901210301802c2d422107020190303490603004604100909600051280304100602c3c001e001d902404654111800f0340828140b00c4081c62080460a00e820840d8594 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 229600152 1250 229598902 229598921
    0x11090405060609010f03080f03190e282d0804230103020a09061404230306010509011505180d050f010f060b030c0a051c1b050906120a020c010609 64
    0x1c3c0ca140d400094126499000d4504507034002c0c0341d440c2412000b40c9000190751000c0c1810300e00c005042c400d01080803040c4910a1004030035001802810403c802504040940f20340302815100743c0c0c0004e80200720021032121454044603400802035502040c48203440e042c40d200504910740c0400c000c5113101e049088010884103060090b8a111828001101070340f003400030050020f007080ba02045454020354a5024a0804840003814141c884041c0c0d00d07502d45000344100403840032150219282814045c0c140503020540d006010f56041840b84100242c06101da0340401000045040d46040d02c410b20b0003030904000c080e20f030041b8503402c106542d9650200030603407551030b0414203618a032042c410402140d0318020b50504540c3ea00800c800c03140c00c04c84111f07060120800100301d030030510b5124851008a1424006040b9402d0351702070740301a082003903110621004104412440e50741805807056070760703c462202d2281c1d56100e4288080d001e003d01c13018041d0b00f00680450940c400350840c9070740 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 229601402 1250 229600152 229600159
    0x5011d06061906050d0b01021e0a1e0302060f0c040504230703020c0d03020d1b110d020102070201080f041a0108030d11180d29040614090712110904050606 68
    0xb511007540c801e020b03400c014030400000c20300c100461a694045038110305ca24100500540f148807901e280403030b4a146080900840341e0b000011241c003003100c95a5640d0200d01ea1030310b90303902d4141c03d50b00a075446001174040d920f0041440001040c003000b290444003d850040d000b40007110320403102145200da54035000761495104000910014883d200f44d90400d201300c0c0003000a182069419070095110105207082c0b00c1d00c40307420b82200d104220081140b640e480c1d444c010200d29100c000e41c20403071800300390021a40104410800340c0e0f8807440b025080124480c40c020b80d521545810604041c80a0580b9960380444d000002c1541c4040060710242c403080390280540200c0d4000f4501c0da1103250440e0040461540d54502d0a0502e0103008400901c681603071000b9910207420764100b0304000000e080b00b10040e508100070400a40600480c0d49a10b102c0107050b414652247c0751182410301504003980e910310b02c01c40600c80f1100c20280c80207000707880090a0b041505200d03440301b10880c0d00a00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 229602652 1250 229601402 229601419
    0x31308070f051b0114090409120e03100b060403030e03011503080315013e0a0503040f092906160602040303090f030c0605032503051603020702091305011d0606 70
    0x1122141c83c02000c030b030030140d64248000e0754009000181c1d4101058040d0400c0d510b105260001710130465600c0d1301c5125481e0a07040501c04030070989090201d0003441485400c0840f01c1e0910348421043d9400d4952508028001ca034007100403a00410b50601e2a44032030422070000001d00140400441c01100100001107413140c1c220011341d1441e442029a01c504003c40c2c070f00507a1040140c480314841090f180750080c4055a502c0034910304030130307814140c034650000101040201c4510010000800c643e04040c810106104030b8594809010956046000410000c4003186c0e0707948002c4801c0315244101e04031304003a031410082e0003504075000442c00324100120105403200031001440413640d114180e40c0c00182040340448098102800d103c2d0244a4032410f80307401030508600340c00342011135500260038601007d40650180c0545c5160060510401c8084003580302d24401c02ea020b9084441c001141c071032890854010002c446408440000c401c0c0400c80341800826210f020742d0302224040b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 229603902 1250 229602652 229602673
    0xa020c0a0f06150e01050d08190e030106090c0206070e060409090c091109061b16060201020d0510050102070501030e070b1201030c0e06100e0a0e07111606090308031308070f05 77
    0x40d6201150144010704d03890100104200d1a040b4030001c0001c3c442c54900b070609442403070445018a400000901041d1001c9101c00740c0c0c202407213014018101d0302024403400404190103034a07a02d000d084401002090450003007a6210842202d0007007510140412070781c0024100000400200d02505500c0c070b080400410030003502100703895081070020407841c6400c06074680781c5081041004002554000e05d1a00c0c1c01c42c0c0c04e074104d503d000305081e400150342e40010203002d00c1110700c001e10000b034480d1000b50500843e6400200c8200b62003085c00c0009510001807441450040e060f445011055000100c44155114880300a412030788142c06204030291600c5a000d170700c000441d4080d0300000c1441c825881c02d8030461800c000c181010b407441464507116650a07001c003108640540c0814645550211260410001500c02081e600104800c4509040d8003e100340410300c4044c00a54011001c107150b03010126080540540c0401c0740c42c0c2d103007114540b40312041100c2d0425140e5010700200d0701d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 229605152 1250 229603902 229603931
    0x7110a1707060f0207050717010f05010b03061207080715022b0f020c090c0927150108010b04090b19290c0705121f05061014120a020c0a0f06 62
    0x4813100d5600071b01405e00142001840207a01c41d86210071140c170b640ba5121948031040c2032103024041e20000020382e94034a4a001481442d944402c0042140d40c8025401c02c2940030100e920b100340e44040c030303c414a01c401001c04038a802e06071280e8250000c80d000072483c42c000c00c0108032845208544881c0441000c84c01e0680c0c43da10351012251300807980e98001582105544020300c400d00d4000c0200760305500400304500b9480d02c100f0345200450750300d0140000390300b180da80180000800d10305a42d2542c1400b01d50384c0070b400359105600d1500d403941d1400c8240d90b9201403100c601400c2c0300d103c0e5611a41c9141000120050448150541855440c03a0140c9000710080700c0c0e041c1450801803034690302c1c003000d0102043c9001c0d031144440c016070446160b04c0c40001443c140d0350721128400b045904200080090201a1129940074881405404800e451071401030303801040050012150030303038071100120007074880c503d191402030180603d0b032010410142800c60419001d09001c1240e180409601f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 229606402 1250 229605152 229605157
    0xc031203010e0a020d060b031005090903071707110607030909060501081501080c0d060e0612150403080c12240411070206030414030c1b01020601030b07110a1707060f02 74
    0x10403001a8800000541001054005000c845c014400000d0aa035884c5041740d00c03038006480c1d03541c11700100c880c100901c0c90701d180c2c43c540050440700590301e030026030707510003146201e10429840c0007500410b07001e00b800b5104c0000009134202510f0b041e0307070f0086460001c0501c10b0f20b00031042090f140c6a0049069485241f41610440010740c0c50b01460f18200e00648200c80010700702403250100304001e07810020a802508020084014aa0040d0800d041005203103d0b00c144886041d60180e90740b00000000c800c0c0700394105070542002c00c2583c6580302001254850050301d900310310458014041441100b000052001509040d0301041002580c10041a81c00d0a071081c07595000520842000d031402c1c100a41d0400d10510020508a0180e410603096410040001e040d0303070801b00304040328101c0034101d414101001d00c040d214070f43c11556498210302018103a02d00700803090081d1181c9030b004003d02206142c100100600301e001400c5049070691040100f1100c440c100b56801600740d449000303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 229607652 1250 229606402 229606409
    0x6020d17040b0f0a0b13090201090b120c0f07050a08121b0d0c0302090a0b12010b030402030a060b040b1f020708120a080702031b0d0305011d01050609060c0f0c03120301 74
    0x19184840c1c2c40c0c403803060810450190616413010381d81c003054541d540e20660702c038003c2d060b440b5010410341c50f60700016241c08119404440300407800c029450703c256081c28040d501c100004000f03500c0300c00246c21544075001d203080c014454402da64605041c04540c801600320140d1010344509a80d80b00011b8818681e048036400c041030a00340628000d04403240c00111034030905103001410138880302d00044500300b450303001103c1d280c000903824001d194140740706c0780904081061039103503040590100f540d07201c0c40c1c0809402190382b050210b240d035885401c400005800240026001041103421404000b400c000b118058446c6000001d403d000203c0c484036500080d0b5400c030304004208105440c07040c0000c0044d0300b140030800844a8035164084203241007500d03803000b0145900c0560b0b01070700302d4506801101400040100d00d080d40d03025181700303078152601070712415104c000245c0031803003e003c1d5100c0560075006155140f54900e07070004404103200d000720221030902108140c1c0e11143d03c0701b0300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 229608902 1250 229607652 229607663
    0x30b07110a08180306040b070206060105040324060302040219031802030601031101091d09071a03060d1403120a1406030717150124020c01020c130608010606020d1704 73
    0x2041003021400d4400034090710103c1d4a903003003039103400b02c00090070600d0450341202c2110180050003549a81041600e500001c00e00301207292a066803110308164010000d0072a1840843c44040b01d4803441d03030492001594003410941d00c8802a5151108140900c02e00c400068540b5a90394020402101445800350f000b80140c0400d03403d41e00c84903425194811110705104500c00002035805000c0700c1d58186c1501d00d004044541402480b19041c11165400102c8611f100640340c06160700f0f001c01c580d0032600885040e6410b1a2520742202154501c459000c0031340008151041183c00700700711031303114082140040103024801c1d60000010300b0160f40e042c2d05a40704e202e0034460000c0d03440c2c8614081c080d1000310740302944525100c1d402d07980c00b6000103841c941c102c4c000041803110445540700e204010700240c2584000480000c2da00d259452903103104044d640d6842d65003032040e6000801401360310009102441d01c0d0b010180d682e01c0c642e040a030000b0180f007502c0d921070030074140080c000c95001303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 229610152 1250 229608902 229608913
    0x50d02060105060d050c0702090c0a0e060a0f031802060a0c0b34031107060902101d060a0509030d030506190e18010b0d030e0102070e0c040302011b0c0906030b0711 72
    0x104c404030300a100050113a50380002c10440030000d0707603514078868860303580f8070281542e9248004005081c400c0c070740c560714016081808031003d00c0350043c924903c84049441c00143e20b290402d8940700d0700d00d0107400030b50041c20000c0d2034201d5070340c0610741c2c200786800b4504807045500c0d006104425281604c62000d2100784c51040341c0299a030b00600804c000d4000d1030080340c190082d03035042c945603108400072a026603403014014114140025000d5a8841504000190400070b002c90403a100300104194801c840000e1001342d00f5000d0019140b14100260032503445541c191006030040c00f0a907041840703103040c004410120341d800d200300003c3e5411100c0c22900354886d0740d81e8140642c0c00b241041242c0d502c4840006880e01c07650010324409000e07549014042102034006401d10206401540c6c030721070b40340c00b00142403003681c044408130383d030a20704001d0303903540b46026015494181e03100400423660410000f42c02d0440e50024416640141110395160716020005d4a283c04400c0a260070354010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 229611402 1250 229610152 229610167
    0x60a02150f090f032812022b0b1e0a0f030501020c010b061e03071106070c0201030c0504140d030309140318040c121d0708030318060106120e28050d0206010506 70
    0xd900795aa080209400e15418090b41070884600b40d8001c00420080541011290495030700b045101d408c003a42d01000170050b41a8040209041000191034107008001030080414142c45c1c03c80004010000c3c0039802007159164a000d81c003035030240010740000c0d0700b002c1c201ca48a141110403030750b000c1e107103e01040d081e21070a10319480e1500002e0012080c018040c92301d00080c3c40c00c0c01014410b4210b940d0b00c4164081e14400507040b203a030b0442c041d0421100344024010001d05241c240300d101400c64000000f4010740c5012006401b100f030008000410010040300300100000150182140f442003000d00390300c00b8402c2c00f040742c0c002c9100e440003c84010748002402c205501099201c015441007842d4604840a1645401c4095010817901c1d0b10000030080e544512040f031080c507a641c00b02900c1d9552402d0002802c10384c1048103145c1c40740c0d44483e116800c0c0d90030400401002c4019910342070a503122003014480600443c404d03281d40c0540c510307140b00144003080d0300e07060359001009079042061 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 229612652 1250 229611402 229611457
    0xe06060301051f140a02160e011505071b030506070e040507050d02090d0b090d091d0403080709030b1003200319050c06040f1a09030606060a02150f090f03 68
    0x44240990f000c0c4250118007045403200c000c020503030715a55130000c001180c5049441c040014407940a070351140e4505005200c1c9031104e0b03003108540794485c6000c984035002814a220030302d2151030f484801d02d0002000004100340491150310402c00d81d1183c65540c0c001703c0910003036600448000e0f001a10802c50f482e5180403076405403c0018011b020826070750013540d03802051035010b40b2030018a5014060321000d1f10740c4605142c1c09000c1d184160b02d802041d4407550602914090002410f209940001540c11841500d08800940d0403054a0300740d0b06040c00e089000e420240002c3d02d881001d240018442128000e8194130040b01900602400b0030400b01c03006486100503084906005000300b02106e5502e000240c40600303500102c2c4c0c0040762801303011a60008a0040307400c04ca0100f80b0001110707540c0415910b92240065444d1581c030403407004120308001001207030345c01d41280314080c0400c020542038654072400c2c01a040f12040c20846880580d24000c17a02d111940701081c021103401c0c0b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 229613902 1250 229612652 229612699
    0x30d0504050a0f05010b040b010504080c09071b0f03080609090601031b0e0108010e010b10050a0309060b130b040f110712020114040f12080103021f2105010e0606030105 74
    0x50007001903070002216070380c07944407444240000352800e03916803010400e107103054491801801c2c1c0c24242145041e04c5c0182c942d482d540d040404038401c00d00040098011401281000c070700e16400300309410b14072031a141c1315008801c2d12100340d0002e0303001000101c070703402c0c445121802684990024080b40c0e10710381e145071a0800e0600100d1007084187c41c001000310f06540401c0c06844c1840001c00d80301e6281054900b159240804940700d503403030203d130000503900a000c5030f224041920340443c0300851070510b10060240e0440558100d1034111007411215540d6021a4003490101c409014126021f0350380c00a07034640d026801042c801c20440c80e000241d042040c441071202c0d40c00042019400e1540c01d9910b6001200c2c252400c44640c00394904002d5044540d201d10400380c02e1000c0710754150b4011815070603030280c0c208075811110951030346c254002c007103441c1704c03a044502c90200f51403428121341c0a04401c0c401c410703100680307001141480c50030406a034166032018041c040314100b110308009508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 229615152 1250 229613902 229613911
    0x60402070f060c122a140307050901090e070c0b010807180506120105040503040807091b110106030203120702090604020a08070804140703290405030a03090501020f030a0e0706050c030d05 82
    0x3005075440307078000301034010b022401c24048601d450000700383c03060a9074405c40800c0b19082181841e41b81105a00400a80c0d811508902d88542c0f5007415400513900000c198200d000c0101106040154695104811a0895104c2c0200c910541d03610070003285c1e80d4815001e01410201600d80b00c40c0300d440710b98441a44110001c08221660f11005a660f01b1601d050390140c8580d00001024444c85c4d10070400d50005005440c1c0820081c0c022110009802042e600628104142041411000c6109401c01005190010244c0781400c8030031180d0141070788401c0081740103030101e4002506501d4588251132420b21291100d043d10f0b503454000319560303103004100b128411400c0581e841103013810807814000d544500b80055190b03050300c0700240400d50703e501a401c008482410840003500220654451482a08000c51a01c58500d080350280c0240740e400d110b00c1801004000e80341440303070403081082e05c01605540595444180c11070380f5214100c501c0c0100d5104105424600b9802c6d400300760310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 229616402 1250 229615152 229615157
    0x10f0f0f0e090108060403110705010804030507030c1208010f09020301030f030806061905030f161205090c1525030c0809062104020a08160314120a08010806060402070f060c 76
    0x80c50500c0042c1c2c0403102138201d0000ca0340080104400c240d00103c990200c1100ca400401c0707510710b8000000c12101001f00300400300b00c004128401094040c10829410590040f10450300e101c101c0001000d4020034400c0355402e06e200c0900040415003842242e040e81d0b006010481a807000d40c4003aa0248030241c1101d401403020806444d000883d40d120501c409460303a10036550381042030008100320001340c04180002d18a18802607002e820400841411340001c4002c41e0607030300c12240b0307400c0c000c040d0030550b04072a00c0901c0041d04204440100000861100380e0a414540c3e0401d00d84902c1103c10020302051b522203038480402c400d0805402a0300c802408103140084845c80c0c1500b00b12051740d2100c1985644041c001145014400000549410001002c00d180054807800c1104402d100140c201001c0c000c104084070814082c070b03001040c0340c000d10b40d940d00a50344000c1c01c00b9424464136485000d160046a03803860280210707440039030070800c00715004140b038541100502c8101401d009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 229617652 1250 229616402 229616417
    0x51504030206120114041103040609061b0804051b060a030207060204031e02040e1c050310030507060c0606080307020d120207030c121104050c07140f011401060e010f0f0f 75
    0x41c2d64490007002a82450702035800c29501d400c1c100e41c0040e152000444c881d60401e040315611040300400c0d40d9001d40c0016011824054505000e0010401d0295440100d400d604020301c0c141e402c19141c80c0124420400c6038810044034608c41c0b80c0d502611552607104030108091241c141c407940142c07000300c2c01507034010f1a040d642d0380e40f0310022011b0081044c4401ca081405e03015460188102c2104211501c0174040310801d0003c943c111200018180040c00004800f040140d44005143c1000e503500c00300f11501c80e5220400900100c15143c011240c860910a0102e05070101100307841c442503015011101006d0595688003140c2e0408040d0740451081d520000301148480e1070307800041131202106905680a4103002690040395001e0a000d1410f01c011b004000e01c511007102d403100d420040c0c0000c40c1c81ca1020041c00d00724040c015540382d40c2441c2c0f0015250b020754410b207040f2002510380440c0c0d400e1040054a00e08030400c82480411003c003070103141c5500940aa80070310103076251240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 229618902 1250 229617652 229617659
    0x30613080c07121203050903040902070807020d0b06270c07030e030a060e0c01030b060322050607080610180603050912071110090e2202090406090c061107051504 71
    0x245841003075804043d21807042402d040a001d0300400601d01050149014851450441c480c03d13070b2881a8441c1d0001250b00041d00c83c140448035003600e40c003503802480c60340c8081c030909001401e00c001351040c034880e020042001400b0101c07040e10103074022425a142c500741da00d03d840c1607070319000058141c4c10f00c00e440e05079001c10395061102c401741503c628400182e503260049900e02c2d1000d024000c906141c40c1201c0c0840569070031042d03a602000000c00e107440c2c10310410305041c4070544200000c0c160301c140028441c400b5000703007041d44284015034141c0c0c12209800300480d825020074814158981c00e03c1d000b441030380d00c43d802076075008218204036414120300000a5045030700070001540c80c842c00700d00500f920701d84071052184202107132800d5450035040c0740100081001c00703014034501e2030b0300b4500d101c0030104100c001409560024080c10b203601d0103040031400303020064011a040260043d010075014081c0e46001d0001074070fa03004140340c070300305011311489074280c00214140b0300003408000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 229620152 1250 229618902 229618927
    0x60b160f020f040509070806100e010302040b011b032106030206160203011806050f0601050304050d30090b18070e0c070204020a1808030711040b1504090b120c03061308 74
    0xd001711203090040002a2421000a0600b0405400303201e4a44041c2d404203e8440c10541090541c1d80495001071450b91900041e0f40481500903117191000d00400400141508070340c0821360b42d02141070000b000302c003021103107045821602000b07501c11020b012108440c1e0091b1041d00c00b0310710240c000140078141a88000840c0100c0c1c004480700b0b5215401c104442e80040107aa0704440c080c20b016003075040c20780d02c00e921942d404030040304100d058844000025600036000ca44100c00880450780c04030406032040280200000c16a44107942c100403c0369203a0714480c0e8030420100b0005480d07034609000c22440c0c50301c00504010160102440305001603541e5100415160805403542c44000c0b030f0700545903ca20401d40d120702c1c669001400b00b000841c802604070b06500c0c81c2110002000c422501c005481700e65102424140194003080c04202000700350f028242c1440300b260b03600541805896030550301c111000070142c01d50400008100140c030100c640d25601d03445901d4880c18090042c141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 229621402 1250 229620152 229620161
    0x2090a090222150206190209040f0e0c090f01140402071202010209090702030306031c11102309030415020307140a030906050a08011a07080d050a060b160f020f04 71
    0x200c2c2c02c1009a0560018188680d0300c5100209144001180310392080f400107902e5540c010581c0f12a00700035500c10310a0174441c0d0403101b820b4002032040080181402070b0b0001401a103c5c0d041d058481c0342e2240b00742d40340802149201c0c80341b541c41c00b603680e8205100790b003090728012200703900580c082c0b14001c0014071b90242e0142e041400d070b00050f22060501c2c04c02c408103070083c0088043d9002003060002e1610086445d402d1030442004502d0190800305088500c1a2020b03003018107401070441e008205840c0350000c10300d9005422440c0400f24500700c0103a110402a44d8084c0c00f80d108100400907000656425010982d560064034141003032504d510804588800790804550403448410707003095002080c182c0604020326000d800c203e0542d601a040310410f010f00c1300102d502c0d51645183d141c5000440e84655032110510703484070503139060980586020b0319000c0760107052440c00b2030b03000215405e89582a00d1540d52000b943c040d070701d0349414a0003501303003603801c0030201d1001c82440e200d9025 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 229622652 1250 229621402 229621417
    0x20a0e270a0b360111161110020c19081905010606141206030109080705070501090b0a080f0907050a0314060c0901050d091b0605030601030b06090a05012006091606031e02090a0902 79
    0x6806d402e4000c0c500e404d0750003451804036184500800644848002ea0000e0313403056224048d6801c0f00d46851103a038000542c0c0c2503500503ca80d12444039150f04540c40c0d16020031a0300c0c4150002d2001c02c0e1558002e0307501c480244c240c1800c44100340b051000080c070004042e600b00c60007400004114090b601c0c1e5000c0b99010b604252082d1340030101c100019644100341d1303002030860004943c00c20403002e400500c880c802074010f00000b00b0030004a4211b050500400c001404000c00d101074055817850111030403c070038004c07a0b1a601801d0b00086504104008980c05004140e540611f0208046890802090b805006a81c12560244070040c04a1200308000c00340030305896454591800c41c0004040c0c810105070140100418084001c585d11750500400589209003462203004050b500d040e14001082044101c03144509400e1228211011807114203080d00e10712481c8500c0d44507030f0180c081d034005810707154440152003250901a84b140d80030b030181d82c00c01080592465540c200c0070069801c00365 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 229623902 1250 229622652 229622677
    0x319050109180f060230070203070804050d03120c030605090f10060f05131205061f0b0705120409060e0f01030506130812010b09010318020a0e270a0b360111 69
    0x50581b0030740282d4640710b0f9032060240c40218540b031095075030805580101d1150030700030340550707000c07008060242511050000060a040010302c0c51300300d004000c0c2025109071070091616030045040c049080b0310f6244180036408000e230165103441f008441440058018504000c414804004013800b407550a10003450010305013850300c00c8a040c180e09100000c0c00300361648180310303045550705814511030011076902504071600d4020b241011400c3c2806074220480e6000001008186081c461b40300c0380035140502080491a5a100c8074403412407401c3c0005000303544900006540740ca22685062202485003055505000c0c0300400002007030400c0e0031040c080b1902265414940d40e152140240740c5a1144242100880540120b80030206c00d0103905c1500e1180030001c3e070050007200e1219500311203803840e05c1802d400b0101c51610b0b110720030710885078a0685004900b450310350104803d06080320511100707075071204861500e6000070710f068190042d501c0c3c0024010001c08000540880a1030341c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 229625152 1250 229623902 229623967
    0x1501050a170103051b041a130b090903040f0605030c18010903120207060e03010c1b080c0d02010e06070e0306150a08030c031305010206240d02060319050109180f0602 73
    0x891030952848030000360345c1e000d02d103804201d6640311664040007841c0c80050b222000c80d2902d02a142020b400d0b00b25107a40c01030044000e202c02c445c000401041111850200078040300d8a40b4000c440600c01600c2290151a06005801040000420002049405050080d01161b5a80d0380d850382c00c07680031064000d0b821182040082d83d4200007011490f4904500811503e405181e02400b04010703090202200701100c0078082c10848880201c92045004004a840425400c2002400381003d0380258102e80074070070109a0780745c091600410f8003440200640f54a03901c040385103c10300d0506211a40c004055180024021420302c0101101c6042e6000303903580f52440984c816140c05582d100a04651204041120b02940002c5c0a00400510030505c85190402e800181c5030700c203c4400690700550000070b00840c0a10100201d8070303003800031810b1000f0382c1c0e074048000480f1810440c113245150070101d10710008110744001c50550b840f4082c010b0401c00704c0141c040c040c10107a40c0c283c4003241c26 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 229626402 1250 229625152 229625173
    0x51302030a15060c0305030c0c011b09061404030b092805060c03010f1715010b250b06010f0923150f0d0902010c050d0305160201051501050a17010305 66
    0x25001d036500e80618240091480b51804000038403420004401508012000c000306511240c1b01084980c1c078140440203102894428071140012203081c1d90100100b1042d035400110540111601c0da8440c454a08881c1410b00c6d603210b1103059070008110501c070740240c2d010040c034103164880fa0300000c0009452005413218518045203851005014a045401c040c0010442400c00c50344810540c1c000000c5141d0400d01c43c09050301d00030101c00841c10416190b0004100c0e1001c3c41d01a0588145419900d956100301f03220903003490807203260141003c182e220000381b03594002c40c03c000d0301c44c4e00d906d00391011302d03a9910282c00c4007101214194010030700b0303107102e0b04600c2e0241400c40c0c2545d00d01702283c5049001c42201c81c2901c142415441810740f61110a001d581c01034054580181e000710949001603540b100041c002c220071152800e41e201ca1f000242c40c1940b05224540c450044113040011490b84000151059000314140704100034000c14400d104600e0901c41500840c03140008110003440c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 229627652 1250 229626402 229626421
    0x70524011508160e01020a0c060e09130201020a030e0a0519173d0203090604140a020112050604020705030703080901060905070c0f1104090807020f01020706120b040605130203 77
    0x450521008202c1d00c50180090b4002076196081d20342028100b0843c10342001005038109801103a0180440e0b204820010f440d50f04402d04945032002217403150026555450300c5c9140401c200c01c0a801603001d0324034007000a0040080b0215400002c06840d142070781c940c00594180c2086d07810300103c4210f1001040382004c01d00206180784415005013991f449a00064400e00c00020740c0c0c4002120440ea4041031051503901802d034800f1421001e554910b000c03010f0682d00c1c001601e0071581c0150025416840c000007080e204892681651100800c4640043e42e0016190281485600c41c1d82003100b00c0014004000418001c0d20940b190310482c038001e0240c40c00c440726a407044c000c450810b810002070301c0d4000c1201203003c0d40320f984c501c404440b60600d006840d03044880103820a01d0450350005100401000e050800d00c2181c014100c9220b0b4801242c44410340d200300e2011644003e0000400c01c210341200d00800f0016000003007542d520000103160f402d00010280c080380e8001709000f582e02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 229628902 1250 229627652 229627679
    0x19060f0305030903151603050a1404051b040c02030901030207020406091433040c0e2815050a1d0d0305030604290f011b0305040609060809030d0207052401 68
    0x14291702c9500704c6498440005805804400c21000400d95100300081150a840c2d102000101c21016038190790716080c0740c03c5540b4402100404103245c03c1202caaa918038207802600b4054440b90f014504140c1d911005402075008800120791060300d030080411030001d81c2c483d20b6451102d8207052605420003401081111040103452000009401400ba41c00c07280c000180b84009016500000c58000d10702003205d1201105090b9940130007108010307921502d49039200d100521031440d400f2400c5a41e4148050512500d40040020400c2800405035035801003d0203403000d20000000d20b481c0e00c1d4800090404a4010001c070302140020040c000d16003000c0c8a2f0b42c001d440e503049a0906200d004030043d100012074103049106500c10744540645034410103a5130410170030488808090000c6190240064009020700d02c0000c1c2d0520002810700d06c51054540a58a80310103140352105d1001ca00c4041c0d400400c040d5124400c581044204208412416180b40102c042c0043e1315414034034000d81a2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 229630152 1250 229628902 229628923
    0x509090102040501020c0603060409021201020a1b0203060424020406020105070f03050709090f021b060f1b030604150810060503071517070e0913020301060e070819060f0305030903 79
    0x140e00c140b000340700b01c0e42c0010b4100803a220490b40e4903140e55138000080d010b0b080c000390082d04052083e01503024204150050006212203466104128188000200401041041c003035416400500820040745400c0c41e00c2400300750400d0191118801d01c060142603a00035486040140e64590400907103561040c840c01c0c543c1640d1a080c030003400c0590300141118618000d0340119079480c0024048203c040c3d0403201c1c816020303060350f10700d0750350068003c0d1180d0701200e4101203001c20100180459164508081110071440403140c250341364141400014200c40c004008808070b494000306a203402040ba9808081200401141c0c07942070000789414441c45031b009100a07506425003c801d59040034000001e0581e407902601030341c2c1e44200c2107506500e2a184541c02030001d806001e0303507201c003c2600b00103034000e40c0288205643c0b2088175100100459a01000942d0500400c06102c5d03a4500c0c40c220071503001c004150340d5200d5a0005200140e40e20849007580300003403840150500b444801100d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 229631402 1250 229630152 229630171
    0x2705060105060406020d0e01020f0a0c1d100306090c09050f0a0c02030a0203041e12030801091107020112020c011d100e010204030c0501080403050d090803091c200f060405070509 78
    0x5144c50304501941c1d480c000c1480400780081500c1000e000e91003001001040104542100c003a6034590808000000c00703405605005070038180180806880c00110b18000c00003040c03c2c04641d443d586501c030040544010840d03203811500360014a0510074010316019503080b10061000c0d06080314140103c510085a441c15504144007002c04d07540c0100c1074508684002690700860440a02106800c1100c3c2c1c001d150105900c401c01414552f1101e9028140c07140e00c0c0e0100030304844007040c80e010b40515000240051040f07034003c6000d1405401074104411035174000710340c148070b80519078040c4614580035a25580044004410380440b401406150f03d0140002c45c60541151941200854140103407030500c564200403d0806100e40c040356200d00000310f0070811440146030035010fa6206941002c0c6500c600403c0000b150009814021000d003640c40d901d0b8401c250205002c5204640031709034000d401004200e90807000309000c0c1c18802c600c900003611080c3e00300000c20021007805810200e6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 229632652 1250 229631402 229631407
    0x1204052b12120902092206020316110f071703130608060f0103060e0a0c09082a0f0108041101200307060e03040602100f1d1522080d270506010506 64
    0x9615500645904010400c4560003142c8003101040000c2c0d4446c40002e1005200104000607070078511080d0b4100b01c090ba49000c414065403d00b69a80c0301ca881c0e030349455401208003041041e03200b4000368100445034050304e0400094210101e010302595000c94085038040c002c00542d45800701c541500d14000342410030031075092401d03c40c040900104080d0115584031500135503d80500750703c0000708001f008032030480074050070b40c1c903407628104003a119181052082c82114a00314440007084001a501c80c0401d03915602d454000b02100c1181c1818020769850700301c0c1ca0240c030500007034081c0b103040c011540e071100f914040003244c681c051402407607001808140f03d034075404222101441440040030409a00d00c03100980184491015000070741c5032a042005021804901e070409020010b8002706295181d00030980c80c041c048800700f0103855003200d440300103624180648075030740c0307003400008002010005135000348011303500003440e04805507a0b40d402c11500b0040540502002c0d1001c2c3d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 229633902 1250 229632652 229632671
    0x216051806040c0e09070e010f08070e150906070b010503100b03030a030b031e0a0c08010b0609091504020f0d050a0908090f030a02040c051201081204052b1212 70
    0x10022101804082c0b055880f040310b941030030720450a07490503440081c40080c2500f450003024200c020104465400b00300001084c44089001c0e1140d1407041c1130b00d444a16a07211108100308584140301d44002182c01d00b4851808161541800340120b50310072203202e10785504140070035152400c40001e48103564100036035088142c030040141d80708040d0030304006c85e016644000090810344104102203c4c07000c0d480b1500012040041e00302caa49015034aa00c041540358100301e401e8860b0304840341e0304040c0400002c180360030801d000c2c0c1c1d840203403009601c0c0da51001d080000e09984c42007003050702d444008101000c00c100c092107025040719808008000686260b0307541081c5010780c4006510401c039100c1c4450141c0c03405d0000700300c51030b4000d1040021226480014002c3d400590811b100ca400f008c00108041000055000071160341c209240d052620744420000040c5030407105a102c0e840e41d00a20300c085403252054200e00348141c00b803400191400c40c008204d68201450f0b030000b24142100301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 229635152 1250 229633902 229633939
    0xb0d02060403080c100c0c0209060405071421040c0e0c16021e0315070306050f1513120302010f0b060310030201030b03010209090a0c140a0e0f0a080d021605 69
    0x540440e940448103544484d030b0114044c0c1005441c02a100400b03013403145040040340c0c0701d120226582c2c400c4901ca0b2050f1944024441140c0d000c88810010400ba40d5582d004440b091000d00700341e09203800b0fa2241d54140342c094240b0b00606403412204080340c41c20910506203c0b0000c2d5a20414030010075007032000700411a4119015441c010340103001074011410b11076000c1a0003041114068221084002c000307900704904101101e410000910345040862107142261038080300410003070401d030004131406a960f881d607002e514001640c2240210000c0d102c0481d0060481c024040d40000440f41c10703141a160a4492540005203d500c0030000c1264041901903a070050300c1d020729001582240c00f80c0803071300920503000c02543c40380f483d400708295800e0681020307540300c40d203503111800704421003005991405201601008039407000100c011a051103520800090401000012025550300b031a9080c05a440b81a40058211480c00b00402c140c050b80b16009100c00d60f1b40f4034420002c3c1e140d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 229636402 1250 229635152 229635157
    0x32d1c0801060c061413021504060212180d06020c0706140d050910021611030111180f120c0f01020d020a1704031a010806060405010f142e02010b0d0206 67
    0x8800038016101400020300c45958042c1135240b517000078540700750400404111002840c80710480c40781e10030503940040d00d001d010a07a412210b0b039070010030f890400750030b0041540e0800b030001024600070035910300056482e25603203403000e4000c079001640c403140480c4c1141400010f410920a010340781000c07050300c0110008071002010012000a0075444640d82641048031002580f90003a0011802064442010090040c41c5100310038240c0c454140f441814240d0303007070911400251200340111514061482c01180d003400380200114817a0040c4000180c1480303490070030485503070020b8030004541c1016201d00c0031400c02400140617020040100a607151300343c120062611120041c0c4041d44010b01d003c0d10091540220f51440500c040503032400240c4003442124564845d0001142007820a442080c1c140c0c0c00b02c81001542038101031f42c950307801140c0a002904401b880200d8a000d04030002d00f0082030984060200506004401c002e094440c07060865201303034014078604005a460008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 229637652 1250 229636402 229636409
    0x3080105010f020f07060201020d061d0609070203250501050601020a0803190204120515010906030803010b0f070f03090f1e0e060a0905101a0c0d0509032d1c0801 71
    0x2c01080141c40542c040781064400074002409100c0c060001c41d030b90b80c043d0082c00c0603802c5560200400759641741143c002310b50310490300c1503007100b4102017416070421007a1540e21842c180102c0340b03408086000e003002120101d6001c1c0403440c1000710802040001c0c094107420800910007402602d18039201c21455110180070400c50034810304010b403402c0c0c02901998020f20303030f040040c080c0500d607042c12a1254010741824a504200c4000810382580b03034410b00c8243c84c2c1010000341180c1c2000324070921075010210224410740207100100000752522440307004e15210355280c0607500c1c580901d40800040300c1c1c20410200d000ca00b00070360344052196880c02240d5102c1100c288588070341c4085010300c240c54102450403801c00b030420142d10200c141c0c8600700d0b01e080365000100760304e00f00b4200d10307402885000400758001c03c00c07440b001c0b807040001c1d01d010000103007500d00c1e40d031100070000101000c0c070716440b5403170b0100a030390f1a0980060000b107069a482c401e2074507400001c014000e01c1d00b86c0501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 229638902 1250 229637652 229637657
    0x11030f060f040608030304050114070903171606050406141e0a05040c051002010e1902060706050c19091707030201171e01140307050f0a06030509010908040b12060307030308010501 79
    0x50800d48160380b150040c2000b01041c1d01aa680c0342040d05006000c0c0664a070f8540305025200041402544140c1d01241200d820440b090703000c0020402c0161075500070219041c6440070340c1500e07004174090f4440c89029a20501001548003403022881804810007003078405109150300506000101c1c40404a5018582520009560b030b9036103484048400c0ca07401c5281c028041c030355100002901584001d9404804104440d214619040030070310740c82202600940001d028000400080c05d1500582d4111011040640c14809901c001010010303402070001c00007602c009003005044070201d11804035840584c040d000352400d54002800070310801c05400485001e240009003d900107406403140c090040460440a51703644030961080454400018401d0241850004881c030700005607000d2424040c04002d80503141940a1b401007074002c00c982819521450b407580081d0400b401400900f0400c1c09454840059028001c008003006100a0203076010103c20300c0807980146005e4110391092 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 229640152 1250 229638902 229638919
    0xc060a0e040e0f01110c1203060d030e0a030501020a0507020a1202090610030f06060e0f0901080d03110d0c1722060b13050f0a0f020405130b180a02030a11030f06 71
    0x42c400b01d840c0409100c1c030038440d94a820103851003c1080001044080c01c580202c480741c01d88404184241d20080c4c8602d0381c0003443d0414400002d0052103143c00580000f0050404a546ca454036420b80c3c1c070a030061300004a00003800000c51030b14445c11006032005404a80e41c041d903a44c04240d0045024281c5841075888035520b081c5103200740c00c03a01100300001001d11800d035540c80c0c041c040c0c0d0300800c00e40f4860350a035240001c00d410503100d16412a241c440c01001500100030050f4024025040e221102d00c00401858000c0c0c40280108007003068199503400707400601d04c441d02442513001e86240c0c038800d20400180c001d00550900070038032982001c0c0006501911000140190b21260703007042d1030178202001c01c000b01904801c024400d040700e18080c40701110708021a012441a13004007075001c41405514041c407091a80710105003030303000e050303828152120300303102075031410803150b01d55101d80000400a00010a00510040d44000d02c0424158142844001060900100118040c0304070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 229641402 1250 229640152 229640171
    0x103020f010c0f0c090f05060f010c17070f0b01050f0307060203030c0a050412050a05060a090f0b060d0c12120e06091201110406030203100609080613060b060c030c0c060a0e04 77
    0xa5101015103030784c0081c01c4002640c1d00c1001c1c0026210341240318003118a01000a0040c1c1000c040c0038024890580d1540c113400000d582e65041000d21054403400d040040c4007900c0000c080c0c01000c40c540d405880c524000d90f14050410494031400c1d4000c6010741c0100c81304110b03454000055a41000c0c03044906611000c0c8000101e425011341d500206a144c00300e1014820b0010101d103a11619005105940981d503e0030519400c2e128404002040c5142100240700420598140550001d000601c500c6102a40351200c002d10903503900102034001c0c441c0b4246003000a8191030f00d001240904003d003c2c00041c50004850340919104903009215a0700c501525080030350042c04002c10300341485498548411006000390003c0f5044c44042e01030080201d001d034000c0091100725080b800040003030f540c5600c0002515074005030100c1c0d00c19124207120f0210341d140350150503400c00403402107845e202c01d070001c6840c00c01c10b641c2090142500300519685690300181c005004c600680c0d001c80c00e89030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 229642652 1250 229641402 229641413
    0xa06050a020c1804060f0204051c050c090f0702060f01140603040204150f06090b0301050d2907120c111b030c0301020a08040c0f060203090d1b0b0408070602060103020f010c 76
    0x100d000301d0703900c685405088885010f18800041c06240549010800c03101c54071440c0080780f155010700c40d0301980481d0600200e1a005515158640c0705d4000c0d1000303d00c140c004505201070941d842112101c681c0b0400c04030a40c1003101560092040c40508003552620601001ca03003031010b003030750007100c00000040954950390442c0141041052000ca200ba54401e814409412607000d51030001300046e000040d501400c40569040c0c84006012075080800741d03a4040c0c0303c1c0c40c40303240014000020106004000500c0001d28810302d0303180c48201c641190445d4150850718580d0405041c00320740140b452020030006500d9a82d0325200002d030401030583c1c5c00080c544007440340e129905600018407030001e140e00a1005028922400071990300b1903c60b0004a00c030f4005010b040c00680c000c0c0b00c01e070294900720708500c42e042e0080700c1149444018154000104101e9000100e80440c000303030411649100f00714000041a540c4050125541507900290440c1c114410042c100038076001c08506014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 229643902 1250 229642652 229642663
    0x1e0c111206010305030301091503080d0915020a030507080a020304050a0206090d0b190c0203040b0f070807150b0a050a03050705040207080910020a020103140403120903030f020c0102090a0f050a06050a02 89
    0x200004200c407020340e5240307400d035983d50090041000c401d061941803503070301140c1f0b04400c0076170f9441100142030000541c5014004d00e031502095840d801510300c00c01144102d44014001441c45030340100f80c41c40e120201500f034140280c084080a4410030410010032008100c041019504a41d00b582d140700c1c0000083e103031841154041c000036a0181441a112082c500d94404118501401c2c40081d0021000383d841c1d000707911803c84140d50070841403104011580051011522614189081440c0c94981c501d049104501011900350394008840b0140740c0140d1001c01003000f100d075841300900310354403d80c40d02000e11a0034080ca4000c901e0b1400c01980500380d82403800042c000c1908034445c1900250380e0704295400740e01003440e01100303100208031150b00798030403901916110105001c0206140040043d25010b508050396014061105d80c1c41e40000c0201440c070740009070300d6080e26820003440004c030f540308005400c0d807004200800c2d140d00385038504a8200341401a1501040f0300180d0824 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 229645152 1250 229643902 229643929
    0x509011b0206061504030c0e0c0d09050307021503150909030405030a0b010608070503070912030e030105010b041403030301151805060a120b031b0f04090803040f02011e0c11 76
    0x1642421030240c10660001e42c02d03124032401c5500581c88240440707000801e02c02c2c1d0001420603034440c40140441004420300c25084a0640840c41c54940707041094000c880c8091021552a000010414258a021154403100d0064440454558107100030412000d855030784c0d4250240042000060845005000f41d038010000070f016204102641d00d01062078240c00d01600d4003003059900440c0070342d40f103801a00c2c40f4091640304c0c4c2d16220b00b4040160304141d00a041181040107009045019032405c3c020f003402000581811030f100c90038654036002200007014420701076801400100b0408041c010707603203e601002d00f0008004d0303400554201110000d0f4009a4100500180a032046540700c0c01402840d00221010400d00107600308150312240341c62060442100c5888a403002443c06003c501305e039201c02480081d041000d40d490042030781085805482c5000d09402038815542c2001c2815400b24101010056690b006ca5000d8a03000d03070480050090f00b010342da03102c4903454200340c0c0c00e1803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 229646402 1250 229645152 229645181
    0xe040b04020705060c1c02071101140d060b0a0905010309050604030c080705010e0a0317130b150406030804030b010f1d100506030f2418060301110d0b010f0918050901 73
    0x1450100803d00086c0d020781801084d952100b0340f02000c1115034400d07610801d601100f102d040c0103c100045441010850000118034420040760003a65100e2080d00024000380d9074050300c8c1c052100000d002e00c60710f5407040c0e042c5400d180402c0300143c00420944d6105900d41040c0c94280c9030740c10901d1030b034015000300900c25813031320f281000790348000100105094400c2e90341e2400303180380404443c03864906031445003480c0704c4540c1c6080040d5a00e141d85502078981e0030343c00324050f9110009002e8454540c07041e0380b01c41c40001c05000b8028a0b50529024210511240d002c4d90702d0308090a05405449004264a0100c100030a001c407070074a1160b401000c005000a49900b083d00c6120b03a11242900da4880c0b00808201000081a04801d0384421841c02040c8600b05c580d151840c458100d00204580da00d035680e600c5114140c050400945019840f514000071690305075800580007407030030014a000d201800b0802c100b0054084059452241e00d41c002003110303150301d1540303805040c038510701100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 229647652 1250 229646402 229646413
    0x204080a050714040b030604121b0803061005030702030f09181503060f2715070507051b0d062408010b0319080a0c0f1a010905090d0e040b04020705 65
    0xa000e0700180500580b2414403410041031498420441200ca05191194043c0c0022002030040b444400b01030510340e0482c10700d2040c00c8200040c80c240c2c007040443c1161200c101000744903003800c104900010007480e50501a145080240002c0c3d668010255443c020600000e1404120340310003264000384c1d0900440096182002d420011901e6941101c10b4000d104020008003080041c2009600078000848210b07285940d0381661210618850303002c41f218401c0041503454600303040d9580f031003130342c655503810740320207151901c54140110a0781b110000c40c10700c80c503a0180c0d41c3d544d1090056a070b01540c0010145a210399050402c0040045400c5003030340796400280d215819001983c2c2904c0440a68050103039a80504141040015008d420340905005050203c1d01545140d5642c50062503c100e608905940d0354402401703200e8030341060740102d00104482d003014050590003200450140442e080da41c0b0703000f850503180d01e00f4184110b0302c030008100c2136141c070b80c11075840702c0d005000e542 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 229648902 1250 229647652 229647673
    0x90317100b040b0301050f010c030f110f0a1415011d0415060305010c03200405060c032502011403130803071b0b010509070512040b062e0206010f03030e060d020408 72
    0x200244c00c24031445005401d0304580752002c4d032040e1066403040e9030503100c52003114500c0310704603046c0b00068203114644c490075480804e03003601000069202d80c07107144183d00d07400402e1882405d000d0980f280c0b1420703003020f000602c4540d0805070740081254a090b19907103150744074100550f013410001d01e40280c41d450070501006200741908400314042c581d48080c4011007000f40c030031004024a03901c1c078101103801d11042c0420310703143d030041c030301c550400040b28100005070980d8041038130045500680240284610011540c1143c0c044042d1060103034201e0662074111b400102403103101c01c00805c404000000956292b00170aa42d148011410381024003101d910b00d0000c9030810280036541c40b03550b808002601301c0c2d00c9101120b98a18101c1c42080160321b03107a0b210000128040c03c584e03440148400000d120b900d206003c0000322048440e10080820070342806410003006800030500800c00380703414000300c1d4112050303c41420060700c40301e659600a0301e4070b40090040e0740201810340a6150f440c2d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 229650152 1250 229648902 229648919
    0x30712060e040c06020f0304080307021e0307090204140603090616030e0d020312090604150507140304050102090109050609061e070b07090f080c0121091407080c04090317100b04 78
    0x114103030f4204e0340860b0240c854041000f0365034016071042d4449035004201c11001400c000d802c1101110300c121111000b405000c000070f040c104030b90807080890b070313004c1010003200200e11201c0c46941d405071036652450a000c02c403940c46100c020b088116034a003030410000c487c1d210740c0c49003040788001c005480c4c00c203031383c40802034803540082041c8240401c100d000c034864403808684207024681c04640c9845d0000c5011034070010f420010b0445043c4100341136820f450b401460003c0d48114459000103942d003035450005040c811180d00484e004100c140300070301842d184c610803158500546004040203d100d81c0d202080340c818204010007c0c0c81a000b1300040315007001d0503038191580c065040c103a80751036509560f52600c0361383d000c500080310f034481c58424220000c181d01c1c402600140119a8a40c16107501d2003581d05c0014042c025444620100941d004c180411450390008545c1402a40c2150706c009100d803240c0c00c942c1c8050005000800d803452052800d69008055084885440b145c0e60440c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 229651402 1250 229650152 229650173
    0x90605180a120b0901110304140f060106091d010e180c03030d090c0605030c040b0906210601030c030203090d0503060118030614011205100c0912050a03170c030712060e04 75
    0x125622458a4040781d80c4d00e506000d441c0313003c1107600c642c5007140c4d201e458240b62414141c0e8080c1c1c660140707103034110b0000414443e960283c0260b45548183e03034076224412540080a6840c0704a44c0b0380800180549610701c00002d40081190701c4141802a6208102e4100380d6080c1e241a858440040d0301c1e5070702142908144561405070031481c0700030360360341d070140c40070700c01222501791450701048148603180030000605041c113800345c02541820340365003401494000a542443c8800741c80010445150b80c540a00800040710345415800c50418880b03565441d41d5200148080c407102000050341030344a815203410450700340d102100000e5403804c1641c0180701003c04007080980e09000411001c0310381e00000a51030f031000041410304514103a0800810500005108100001d80d00143d9018011540c8a040380150060f06100d4924070f0041c0c050705182580494075201c0d40708210310100f9410a0f070b64840550300f80312800541403104a030090074207402100308000e007441800180a8540752 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 229652652 1250 229651402 229651439
    0x60e040b060720010212071509080307090305060907030c090507021204090c03060b0306010206240607030237060203040204060306110a030b040e0a0809030a210e040507090605180a 79
    0x4030f1070b8003c03800380b004a031504050021070b01030403403c1000301c000130300d284e440b00c8100001c0040010707481d00940c0d480400d50300a4490740b0000d0106035040c424801d0502c002500500c0040c01071002d249940c0d03074900b0400e8a84a547c10041d07480000800c1e481c000c0c40140d18016115952540e21911081e0723440007046000c4500d40000d1030a840420290440d030304490152205800403c65070b55030440300704101c410b8040c42c00543c820300303031001e031aa10307004040d2070380502c03a8024000f01034032103600399112070351440d060501701103201e50010340c0400c41c2500d801241e0005c10251ba81d688034000b01e406007038540d00c01000c00e40340c22034412a600100c0080c080e106007642e41485068441d00070003055804c2540e643d500b0f40c01010103007000030f0500c40104034031003001c0d00341c50006026890310500491101001090504c0000d100c0d05096406040c040394041f080710108058105a00020403140c110b00844c000d2000014918508850070110300f0072045004047c8980d0a8a80e1422480c5034403403c2d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 229653902 1250 229652652 229652693
    0x15120605030a1109180f2103040201050708030c1303150c0801050307050f18010617010911090f01051b030406030f2003100e0103030c0b0a0e07060e040b0607 69
    0x40045124507011681c8100c8540180103000341a954004206941c00041d084003500700c4a440c0000c800f070814070498144a621802400b0b50300c100c030790802844126204c3c5092029010002c100050381c1080a48201940107408035440340e4034644201a103200e1200000c11520f9000c20000070845101c11002e11900c88480500034450103d40a0710b50342800e004d183d81c1600309030303418409800c10910440b04004003c12032100080800004181a40300f80c110314001200b140c40c001c2c09405004c001401001d040e02d041004895864440301e0901850245070700c501c0da00b4400c0c1c201c0b41e11480645154003410443d80c6401c00d09501e20a030783e0341c0588135100100b4140b00c50810405541d108003022007505070f01120000c490003101d00c80a030f00061800400b02003540c0c02003900045105a5400385210340c8841c0411403d0341000030b0200170081c8484c16403414044038840034000070420340100c6446042c912072a40e01d0341c0014000d840d0072100c1d15013040c00840c1c01d20a000c0c1c0d0070103440305004030a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 229655152 1250 229653902 229653911
    0x711060c0a0e062704060b03010305010f060b12010915030602030a0606110a080301050603060103060f030506040b060a0819290a1103042a12030f09080f070509101512 73
    0x2006104042c00f6480744c03507003140400007842c10008240754000a41413401030001510035183c500c5007985402c203800550f080e0f90f40e0f82c8110030600f4188900b81c050030f40211400d0400c664005002d82c8040305009450520707407034910b074002e08281022246c000d154043c8040d9207070303d0500340c0b040081045c0d00c00d1500098504007001000d40010408a00700303502b1041c0180703103a086c00d00b40f010b01c0d4000f40c0b080c0d0400d50340f2000041c0e1200c1a0361810041c510440c0544014182418040040c40c2c01070302c0c0317500c101801300d02009003c00004450111461100e00c1880d0006c080c1040400460341112411425032119150043c603802600c1ca02d124000c0000e003041211890000d1015900085030014000c46018181488061a1980c0e040342c0704240140d520345c1c10f4861508088244082e1360403004900e02204c10b802064009920202401b11440180017124003650b150303030349400c1c03840361034000c0785100041401d0703c403a0b507040740140486840e10102d07100c1d001350080003141b40d201c505100501c3d2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 229656402 1250 229655152 229655177
    0xd0e010c080717090f0a03021006050108060f01030506011718071203050a0c050102040801112a07090c020c0406080312090705090402040c050705010c080a0f0e12030711060c0a 77
    0x1403040c8038060364542c0d0f20036406156034914030207101c0c00500802801e11405442d007a11300802c000d0700340b49901c654040d0151101400d926006c0e22003d40049061252600810811b51689203440c041d04009280c0880d881c0c644200599130101c103400703540344120000040101400c141500c40180d074101750200d03030300c1c80d60319058062074001030b08004000030810000d008641c0d200d40e4a100702d075800303400018601a642d9554034212503c00000c3d040c01c420120b80e21030640c68040004242c1c158590880704070b54001d0701c0742500c0d1442e6000320198550b0701c4200c0b503d11882000032aa480102400800844e901d900001d039890b0013424000c0380c4a00c95000040131854041105012120302070111001919907900300006007215041301b1040010602901001c10002d001e00c04138807006441e9085103042000e4090305507898091091169810000c0c4e039820044005080241c00c440c09000f42c1c2c1341c0e00e5104089402c4020480760000f94810b0303005102308070003810002c041c01c130b100751941d1241008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 229657652 1250 229656402 229656407
    0x181c1b05010528050c060a06060f050c060a020d0b030f0703050c1002061504020d0f050709080316150605060309010221011811040b0a0909050604020f2b020d0e010c 72
    0x183c5800c0d0550100003007008641c841c4914094150301825041c010f062107540707080203140c0b035003c0b60310119158841408112840d04500c0800c004080d41c5805841c100d919840f2903594000070b0005842c0590006880004181c503500110008400170207440c10301c0d8904c0f986075503500240c003094545004440c0b4000c2c442c035010300f100318015510b4025240680c0c480c00851808040b00160325006602001403141c10390480c41032490780c0002c0d4000260381c1c20885c034018181003c03504011850f034030030804c5038100807414840c05002039004001e40c06d850f08080d2081c015107030702da01c00c40d0800c00200910003a94010b40290001c0c110105030000001900450422a1542031103006940b042001152800c24140e0304498040d0402039005441c113030351022601b03035580c4101d0420f0001120f0388000d02000c2c01070300482e070b0040d01c00c0380c0942c10314031f0720428426180300c1c0e44060101c0e81d5224404a21003503109440440c1d954244004645036662807542030082c1031201600c114a5180c460305045050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 229658902 1250 229657652 229657657
    0x7050102180d0c0909031b12140c030d0b0f09010f0e1501090509061207080a02090f06060405130906020a0804020f011706061612170a0203010b181c1b050105 69
    0x90b001415141c8042c64140c00400900c2220300590400c81c0c80e01f030201c184011028080b0800f403150365042840c004083d40181100006440d2500401e410011060140000004ea03940c07030035050030015000040c1703000169594800340000c0d4005c4024400091080344039000c403401c0304d0351450950600d94618115188040c0000a140c2c00301d140d01105000303900304070b03a0707841d40404050410a060a820f980081c03808290b80d12202c8140e000418520440c180809001c0d000300100704151880e00b80030000500300d0045010b51800385105090001048102341c00045000c0c1d0841c01c00c5645060300b00000303118174402ca5007039014448087d901d072100c0d4455240020040d80444543e0855201e81c010090b0960200100b0854400081d040da400709802030504000c4142e1034560600d1140c0740808e4100103880181a60406072040c001000340d02d03c0b200403191641d05c1c030848114800d82c58000542c41405160030740f41c600e0a043c10050420054100001c031116444405450b200e5440c0011105407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 229660152 1250 229658902 229658929
    0x1215010f050c19151d12040e0103030c0215160317040203060402040203090c130e010b0907090b07031b06060317090a0306020f1e031b04060f0f030609020705010218 72
    0x150b0121060b20b094290003184841e4240c410620130b101310b031130b0710105802d0303030001c00f100d250701010b081c500c888060041106440118191040500b0146441c0700e80c0c440c54414400602442501c505842c1199030f2450a000051200e1141680710504902407803c1445a08404c40c0418030800030001401d404140051085a000f0010601030365203030f0078440079400107445d1290520805c0d00c40501607482c1c1c010885080c23042c6000060300c45088441e282517030740750030b5510b0003000c468061041081c0e020760040c0c281c1d0812107038180d4591051a0444030000b62903141c1001c80c80c8540c01c2c10400130160454030440c0e00801140c40302001a04899049100e175900e4190300003060101000011060b1700a880c59110a031030a0f81071840f5070100d5040481000e400740412940003007044000381615903c4e2011590600c48142031500705980584901c05608480041c0840c0080854010307100760409070280c01290343c15900c030343d00ba01d0b1043c007039004408890380300d604241d11500759052910388030000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 229661402 1250 229660152 229660177
    0x3170a0c0c0305060714190c061d0105040b0a0608031818040b100603020307052a01021303050706080c07080c120d0c030f0e120c01021323010c0b0604111215010f05 72
    0x3c0d040b8801c000c8c1c03116003030340c24116011607d40e01200528501c199a641e00080d1020020809242524010114131b00082030106400c1c03618805111818000094455100c1a034025540c50b61f6410005603241d2401481106218500002c0008000000b0042c3e4002d0381e0814075460710544642054059001c1242d04000052003800b45000d052400507406000740702003450782441408030f03032040c0c0c2a80c0c054054035042c024002c1c020020010108500d4005041c035103801d20450904000600252007054000b8129a1011800011441c001d02120801c0d05003645910347d507850104251024082c80d002e40e5021910b828103102040c2564021b040a0b0080e110182c0f076001c10100c1d020010350003e01080301559030a00c0040c80c0c00c01544100c0f8041c10341a00d5555407407a01080d58001002440c003900c0c1005011b401520001d046640c038140c2042c8100e501040c528055058124680a9120003070314010380c402c18003040300800010b00001d4002a81c903100703800c040d164107036040d11403500b06160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 229662652 1250 229661402 229661437
    0x60e09060402011b030c06060902031f0f06030203190c020c0315061311040b040b070210020d140c28021008040b0f0a1b0207150903170a0c0c0305060714 67
    0x83c00c18000c84131036140c440d041c03621030661661140002c654264016480316980002480b088520201c0c5c207811410058110800d5181032100c505c14000b03e0344110802c2c55000300c0403030050b00e2405075110300520442c03002c201c5803590b948025a19035075688521f0080c02908404084a0100411030740300319009442000c40c090280c8980004101c0b8101a10007408240808100c040403030300140000c12090450300e45407081c030300401c542c140e0612244025507000042c43c40d2140d8008118030200d03e0885031380ca468410100030030f03050600e007162107450103000e44c140404504c1c1e11010703400103074007e40e00705009d03215442040d514030748280c802425003500c1c0e6001a81665040401c19808003041c0c5d008036003007404080c2c03210020100000400942c201010610100c90940b5080c015501c1900e4110080c901c2e5403120044000b003041c0000a1010002e5900122409090311b070200c00ea00c00300241c2095605c0c1800d54032644181c80703020019503422204440c40b00034100740c0c2da008400020845 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 229663902 1250 229662652 229662677
    0xd0e060907031127040807170705010c0813060e160315050601030e0a060c030603080a0807030b040507052205090f0106020f16060e1306090209030105090a03020d050315040f060e0906040201 83
    0x44c02c2c060041003111140010400b40002074040d451354105905541805070f2602070a15215081d26500c021200030090210200b10902080d203282503900c40c1c10604c005045980442002d0030020b112201c40040b50828000204000500080c4200441700080c20845610f8141c0118203a681e50821b0005991107402c0340030125000c0d92103440030184c9814000f4006a81e0740e117110340364000340c40907030101c0c108804101d101d50b014015900200c00450741001585006400500079000b00782e07100c80e008250f413084092501200c25107a000d4280180301c0301151800031600c08520b4824041c1d0801406401100192140c00041e03030a2900380040ca990b030010b00340f100480e00104080103e96009441c8481c20382c0a004611412000d420b04050240c5d803280c010b82810b003501d20140c660142d50340207414400c0840c0d800303e11003081d8102890040d56035250302000502200008000740c3e44149490711038042603016a2105c821070320324104ca00281d40d241580240c480c042103a011f804240700c4407558 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 229665152 1250 229663902 229663969
    0x60c15060302010f110709050103210807091e0b070602091005030714030604021605013e0c1c05041a1921060f05190f09020d0e0609070311 61
    0x1181710302d10140480c0c6410360366002c4801601e9080e401a01c41c01d0f0340e005c454030714142c8440c10910070522030505800384e090000000308005468030512640c040089201c803c904080580c000c001c5c40d8403107610340c4918407070802c90000e5129030074091140328100882001c06000e0402e40b44101c2c281e85401c40c034401803603d100300d1030384014182c0764403d03401c20046c18021111036240c1c0d0001c1c051400007501c8103a180c041c201d40c103081240c00750302d0100b174082c041c19940d8900440c1c0c1e181c40c440d08020744601e1880b840e18034107050300483c070317044804c0c0454198080d5442009030084490100b40c19250040e1114203044030f2007214080344003000c190300d080701102d001b0301000b20b5074180103801034900031503845281c1c110755103600214a082041d401c00c01043c6014002c0d51982c2c086403114480b61850b000e1042900e07101881030007a60f40e00401c98001040c001d6200b010b003080b001c000e880e4246041c00c001c9440c2c028074007040700c2b075203000703040d14407242400040942c41c8001c5ca03514031100b1800c080b50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 229666402 1250 229665152 229665167
    0xa1d0601050f07060c0c02030f011a04150305030a0201020c16080c0906210a02090a020a0903032303070e100207081f0e03040303051803010510050607061104060c15060302010f 77
    0x442d250301041042d07100091080c4140000403002c1d5440141d00256441050b05001181e04a07560700da0400581c072340141e0004181c07501c0844100c50014028803441d420311600460390740090018080811141405074040d0010491490854180e07035070865425050003071600c40e0b00501100da400581904994102030000c103800000003840c0c003a1401f402041e0201e060203170540701800e604102c030035900314108056280e40000c040d0030b042d0301700a5980c000410074000c5101c0a0b082000003d08100c00350203484140100100d185203986d9685008074001e000072048052060240418810005000d0f20201c1c40c0d0b07042c1c951038000350003005c1e98003941c40005200350080d80e40035580e4045c40341f400c6900700024030080d40319845042e1078017180c00183c00040c3c50038a441c1d009034108020010f11042a00840080d500b0844216403250441e080007001041c4404c3d14004032400010041002900b05038400d850038803810101100401020009096891900c030007404244d14000c00841d00b80035411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 229667652 1250 229666402 229666417
    0x60f0406020a02010615021605030c010e13090501020723060c0a1404051f021005090a2316080c010c050705010e0d0803150a0e160f0201060518060a1d060105 69
    0xc85d080d6103551034013406030290403e01016038400c8a01400030a443d5031150010841200903080c0340d96101c00180a18a98412043c1b0940d241d803210960051240d100d01d0085400000071501e407a95464401030314000050f81840000410300004180c120000daa984581324103410241003003404007007070314241261385442016080030300c40441e80351561030400181c0c0681c891341142c4000c50981c06410500d80b01310306105681840200b1802850005911103001c0e40318030301d401d824244054074032070300c01c0c803068010581c01110031424051556604007002d6504200c00c2d51151216940190740ea440300c060000c000350018203082005600030801c0d140101c1010f00070010318065036680d030585502c01c0316000300751414070802240904019101101425152404415908002211078508501c01020404000400382103c41e03591007904840c0043c100500304c03038803503c403540307034800000021100360740a00d0560400041c110450580c60001242c040d070402440e456030340044405601141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 229668902 1250 229667652 229667657
    0x11100201060512010912050a021b0a090e010605010201050c1305120705030a080a02010501050a03080d050a0f0c0e030d02030307080c0d110a180501030c0e0402030402031005040807030e03060f0406020a 88
    0x72000210782e00c60000a48400c000305000240d8564145408074a0504048140703080000034000402841c0c0c0024581c40100c8a55600451360f02c3c000300041c2c0005c000341c2090030345600340928070300580c00c150020b078180c40e0260000d10240d50b0320401d100103400380b07ca084041160100d006c001508003010780c0e003015500714041d11300350383c0c130780b00800e207428108582211686d0000540c0841d1035420304c100760140000321107000f81c5515645440400f070040c80310405403e40e45802103040000d59a024100d21758a00303100340300500d5480700180c84100d00511481c02070017207500708000070b8800300c1202c4c4a81055114802d1a45450012840c140c02010125200c1942c50040010b10a48140031b00340d02c0c2070903031700ca0005a40c41038042280b140250b20242c10f1500381841444103c0c1c211000ea44000c00c151030068881c1d03600e00009142580b4001c3e0486c0d0f0328541814013041c40022001400741c2030180d15001d83c0000300000703142d07441c50111001507900d002140802c0c00601c961f0000d000c110b080b0b2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 229670152 1250 229668902 229668911
    0xc1b0c05090907060206070905010c030305090c03120705061f060f0c02061611040908030c07030203220e0c040b0403020d0f0c0807060207090b0f0103020f1309090b01090911100201 79
    0x820208080302025501e0b0b0301c090740030103020000140c2c10060554014800d02d8107889441c40c140000e400301e2100034004060588403000103044202c10441c0154901000701111001106081c0500440d8805081903076140102c80005400c00302d410042c240040494440201e12031414070700700d0f1207804c44150340c01044118520403000d0390702d0743d025000c00030001d821810031b02600d00d00440b2445c09a50400d000d103040055038400304080c0001d0707990081911000c181d5030507491500300c1c1103100e800100c04c0341482044000700c0000300c50074550242e4400604190340b541701c07014920301c140100d00c03c8803880c1004010520041c180500e0b0302c41e50b14410310070129041d21690f100310202d05182c0006040340d0000c00c04211060b0304000c02d10080200500402c0070020380760200d90740c905003192840c14950006040b9000702c5c480401c0303074800d0b402219400001b40d00e070154032000d011264001d03600e0048400022030900018410600751981c08041880095a52401d04c18140140c000070000c0d5541d9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 229671402 1250 229670152 229670159
    0x91806020a140706020910030b01120e0f06100e010f080705100509030a2103090b040f0206040b03011715010510110c0307120605130305030703020705070f031202010501090c1b0c 78
    0x10009843c1c03031072041e00056218000d0005008841c0e00002200c010181000d40740381a90742c003c1661000038440100c042080c0038120721152034002507950100d03c6228070700800001d44007100141c01561003001c0c204a550741e0341c2e140c101c0144154094105540c100c00c0c0b0802c031901d40080e01e0085c0441034105682400041c03000a82000120766060341c4000c0310701103900d9103415082e0f2880c5681000c0c1000c000900242e141c4034080000104014245100311a08005554521094400030106943c11a070f480d81c640000012481000c005014144180b5540c0e00700c03003004850f000e05aa4014000c0d01000d11164800c0b9500c4110034012800c41c0980c064085154070103003c028081e281030500ca0715160340390700c5c00034110f407801001c828261060746c09042c00294400d003103070740000e0146409622008517090041c00c0004960125001050501d00002001503c011174088151150020040ca0781c2c0c0d51101e00c2507400b2855080c1c00a04211102d40c0c100e06111080612103020b51144500b250301c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 229672652 1250 229671402 229671437
    0xb032410120506072d0305040602070606080a050c0108070807210507050a09080309060304021026060102210412140102030408070c080109050c060a031506090906091806020a 76
    0x1c619082c0c425810200c100b041c1c0300d800c1204400307100c000700e6005c42000c0041c05151780058004c0c20711000c1503165401300c0c0c1030001a4040e1981d07550082010021190388014481d5580d503900c0c000c440301e002c2c011807880740358050079045200324002d4440c0a92a1b844001c100c91143d00d032042200741caa01c0c4214070100031403d11469120344825210720342d84011281c2d02416000c0b0303903031041c0350507071040007040c4140e00c0d0b200541c3c4c2c2007036044c0c038280c0b10004023580c19101e0484198100c1c030394148051a4441000e05080307498040c240c01e03001c1d61064007081c0903174200301025000310110240e040004100c2044199200100c00c0e008100c248080c90808030220709981c0142c0381998107070004115482031225000c81e010041407500d0003040011450703520103803140920320343d00b0302c500e5002c684503000300e000e5000340720346c442082100c6824617107410001c1c000c0c0701c0a00402e007403549000030101b031440b214400c1c40030142c85001c1513a4064441d07907400000e503224654880801000c0807005001031b8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 229673902 1250 229672652 229672679
    0x140d0c0303030e0106090b06160212160501030b01081b030c1209011a1909020304020a051f030c0f020a02090421020307030f0801121518060e010b032410 67
    0x41c03082d940401c16410580a4500f95520740e044140030a180c40d1041a00b69100c0c0c084464030800c01c0c081103644100c6000062031541c6004044032607010302c580c1580032603000070f28241a110300740c0f4200942c0d80c251b4011906144200c17000c80d000c048400b1300d00c0d8030b00d0a40f4040e42d03100060111052511b54548211042400c042d60410300307507910b8040380c4900781c50405400c201c0441c10748146907040c180f00c4454900c50f645201d0032428580c0000850259141c40030a04042d01010b04400c40011900d101078545241c44008900000c0c50040f82e03000d240d104444400e040c031329650080c001100c05408224480e00040d00840700c85419001881d9011008402c01a4030203c0b5001746440d404c05040c094896440e16803014204101c0400502404c4004108030003919000f040c0e2078030200501c40309034010000102d460b0024281c42030803004001c8140c114450345403604000740038030f05080090540e2021034040c034090203041380341c1c113000003034440b0050360b4024030101040070030b175540d801c1c91031109 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 229675152 1250 229673902 229673909
    0x30c01090c030c0b0307050a0309050c06120f0624130503010606091502010204050d1101020708060a0f060503070b1b0a0b0a0222260304050604080618010b0109140d0c 73
    0x24501003030401c2444840f2200c94014120300c60304d0f610314500708400900da40b05404685040c590303140a082c05001c000c024001c40c1c014040d24556403119107144803e6182c1301100c408c048690200f00094946c10302c1e030201581e6850441064180a0a205800b01141c0090700b0a40e0941110030000840b40d809014400c01000143c450840c554241024141d5074540c1090100035a0b004101c10089501c43d03c0c00c20450f2500203a4030300e8094071540040b82002e07055800040303188965014003000c82c9140c0d00c51260f4400142c0200021a50740e010306485018030720801e2070b001403d1052000900c5802d00c0b282c4014203200954401c80c05964668804000545089900030346c0828000c0d4408040050001c4141030800007500017491b00540b00d060901107000400c0114082c1c4a441140600300191009400010921707601c1d01c0d1140c0b1001d6503060111036000300038a001c00b413440c541d101031040001c03401c01070307489400560400c020003c60714800c0c11007542046400a40d80301054003070720402c019 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 229676258 1106 229675152 229675163
    0x109090314092202192c0306010302010c0c15030213050d050d050a02030c01050910140114062511030c0105090901030605060a0b0a0306061404030b0a0905030c0109 72
    0x6170240300b110800c2500260790715403034a60050310380c0e110b5040d01c542d4007000c0358090700b01c444082200700c10b80790542c000800500140d40704a608a00c2e05004461701d12900d0354030840300e40e20040c0303840c8400c0020341c04542020340d4101400e1403001030104640303100120740c02da1a0903407a49801040c42d000d2240001d04030a866000344141c84410b12100020410341c5080b40c1c01c251a040b1005840c02c28514201c000290310200490007030680e20462802800684404140000341c1e0281c950402c400d020080003144080795988000c1d0f0704c43c412290011440c0703c8105044c608641100c0700c81c180302d41804160070039100c1c00a181e044941242007c2035030707100d5002152390b0101d140c01c5207040c110001404ca25840d0140c014200b100c01c0c2c0d660301d4040700c69020758013806000d9030000519007188800071442d5090f054011041e2309010f0f4040e2464450340001031821540094000c4a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 229496402 229676258 := by
  have h0 := BRFrame.cov_init 229496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 229496402 ≤ n) (h2 : n < 229676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
