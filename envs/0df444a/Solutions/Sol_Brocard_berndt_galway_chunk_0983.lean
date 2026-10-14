-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0983
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:38:42.971977+00:00
-- url     : https://prove2.me/submissions/00a59069-30af-4d9f-ac11-b0871853ef96

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 176618705 ≤ n < 176798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 176619955 1250 176618705 176618711
    0x9020906180a0801060602060403030617070b0904020c0618070f0308070303020706060803120411030318041a0a0e0402031b180c1b01050603060a0605060409020f0d0c3c080604 77
    0x3e41c2d0000f0303003114041d0f0440070050700316004102c18036800d0f005481c01000035080c411240a244003180f602c89009006454113400300040400c100c0d40c0e1901a11140b81d80c1d0f009440305800c140b440003010303500003c101005400380d4240028095542a014011a508031304018500450740e94124000c3d40204421181c05654400c041084082013001d0f080c0302c04241c0c2c6040e0039041c5418075030300030012003070801d1180c2e004101d4200072040081886c0350807801500c0120346420120305409400b04040c010301e81000903078400140e04072000312058080d074026010b032055000084e9600c4940343d14a4042500800d414058901c0c007406c5025450788100031171022414010700c54100b2020500000b07028032541e4603002409801d1606201c0ca0790841c0b070009003008690310705000320b1060f00584c0314404200394003242c0e888001c0320910448600204d000c90402c46181e42c4a400b52100503c0391160307410343d540c5086841c0d4a0710b400d80e00c04400c50f4031a000001d21079003503002c4488080042c001604203031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 176621205 1250 176619955 176619959
    0x3050706111c0e010606050d09140d051e030103020901170a0b0c0405090105060403051203092b120506090a092406080f010c080f061807090f09020906180a 68
    0x10200300a4154030b980385444001041d00314050500f500d4074540c10300d800d40d01d40581000903a4100c41150310f41240380202103010a101d0801080f41011001c4012881c02101050742a1075806802004590030160310041d44c1d243d01c035001c20460109020007500035070b000d001030021640903160088010028011180790041c00e5407203030f0746c42c402074036035010000300490280447c1c074242080b140501416200303603041034070316100e565440903211680d4210001c0080031034900341083c00395510284a0300842803480003074080c0c3c02c1c0400001030440000400c03504090507010054040c89014a400a09034411a280c00129000400784850203d580002c0e604400b052040301040e036803005c08c1d01400000d010761800813840d0408002c1c03000701d0f2503070345049030480a168200b814a504030054124100d515a40e8401041964002c056250f00c05010b880c20003024651212500b0203440101504d400740c113a89140c444141e004100b0000c0c0d000711f081c080101c1c2541c4141d0802d9400303030002d01e42c08001e6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 176622455 1250 176621205 176621231
    0x3081509061c0c0b2113030507020d080f031005010c020f010f09050411030f090a1a04030e0d200402160602030a02040b03040f120503010501020618030f3106020a03050706 75
    0x4941e038004d0102c0000800c240035241c014a400680340d164000c41c200c403d203008200b000c0c80b0f84603078000405000d0049510400c5d502c9800d0003000041d0301445032581c45032400441040d54004803000400300b2076820020890354421019040002d90207401f40d172801130000015107400e0303a803c64010402c00381400000b1a65520b0045020480401e00c50540d02e0911500c400c060850040c12404180d2040c040040010741140a111048000503001506510755180442e000b943c00e00040d50700102c111000800d010141a9411482d28510031400d8594840d20030300c4141d0207020784120b4400c4100302040013040c03d0383c0055501517156500140741c0341e02c0700c21005064100341c0d03043e160800d1040301d035010403060341c0b02c4602546a43c1002811989070400003541c40310010320407104c0e1400e8210018644100b08251109a00c00104181e2120000d1265120490072221489000001c2d20007080c5082003041c0654140c0e4120f90182c00c1d00303130b820f0b02c003504c2b180d00c403d00881d109a551000e0000324 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 176623705 1250 176622455 176622473
    0x1e03120506013b041119090b070809040b0409050102030907080d090e060607050a150609060b030105010f020a0210180b071e0c030204060f030201030b04050601020606120a17030403081509061c 84
    0x17405107803030459140c241042c1904070703ca48110350007081c0b2160500c00d11a696884090b43e040c1c551084c0c42d075503580c0903200464094211540b809070001e043c8a00c500c07c200042d0055407140f61141d00312403400b81e49521791550754124100b54030129900300b80c18010740000f0030706986d1285000d064540703051841d03610186884c000030425945000d80c21810b10541c011801410014a082401440141d0801600588500c018842c42e81484550040c5805c0c550080c8801d00000d40c00401d88d503445440c3e00c1d4090509201d142c6001400140300f000460104108810341e076045030801c041d0000040001281100c0400341c4c8401e5400008018000005944501a80e000303040b0600321004010314500c00502034603821060180701d181020f040022690740007581e00d5005c0012104804110b40c0400300c5404c03c4140e1002071301c0c8800004040410526030b10040d801103100e682c1e41241c42c0d0b18414207861071140d04111550140d4094046451032400303009103210010054440c8050707810b680d03644036007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 176624955 1250 176623705 176623721
    0x36030304030203031f0803090402070201030f09050304050a170a02040902120f07090b03030a020a0605060f03160e0c160305090a090507020c01090b0406050d02071e03120506013b04 79
    0x503407000041100c1c1201c900c8981d05d07402c0346145460b003200c4c10100d04541b01d0007080c03405c0d03000f00d1b804610201036a200e0782095603d8009140d0810034032013503080c40c5450768840e0262602500e03c40c5800180f684140c5409005158102c0144c03000703629030b1f404c1202400c05c1c21026070307209001246414180700b0910048d003840800c407000302000703490507140740142c80040801c2d80c442e0300140045d00001d600400c04616042d03001e0070000d65070780d50000044c03a0601d1b10501681520403503500c4103019040d81d00303041c01d0f40d2156051504907621204001d00c00e200e1600c68240e0000c0d01c00c010350019000304045c0c0300310800100018030041d1038010320011100c04448a10040c0e004030060899541c0009003c0080d1440b03602c07aa16080c18003d02030114480c035604183d043c0c0d400100841030040020b0103902902c07480050040030780490800800c0c504a003440c104d1114900b1000c24010340c080c020103044010486410040740c3c4c906440c40b03200c24070000011a01c1400303001070b00d400340d40342e00c41c80e52 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 176626205 1250 176624955 176624957
    0x4090206041e0303020c0d02090a110f07060212061915120e0c100801062304050307181107030801170106030501051303020601080304050114071401140910053603030403 74
    0xb260703c0d50800a1800f0078642055009400040c18000980c031401d40881c4e00945142c0c002c50b8500c4a030582d09014400c03c51210300301900415440c042202c681c0041215401e180844000d0340c031f5101c204200425400e0030841c0d03100790b020b0f04012200c0810342059006480781007400c0b4a40e188032004c01900c40046010201d500240c10070b0201c0c0c0741c0301449000e100100e00d8504560f60604c80083d04410382d00766106413440100591540c0b8211a500302c0b006440040e0075503206590312014403420864010588140c181021b002000300307001d1800341d80c980c9030960342d4010203910300451212010304055408056540f0b5220220105500b400b0b0a409a02041110307428080c01d418001c3c14003106130404907060300100700c02c2000781e0303108410809030101c2c000980c0c0e07650070320704e0138485489642200403525402d0800014180c0541c00c0c80922502d4030350290f44a2010410011003100c2045130145010241c052424680549403060340003018000b18100c505a03094220003491608102c608030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 176627455 1250 176626205 176626259
    0x6051608090d0b16140a03090c08070905060a060c0f020402030705090a080318030a02091b1c021e0909280608010207020f010f090504151206060302100c0b060409020604 74
    0x12015100990b408680100b0501c2c3c4005122030035050fa4031726100d11800b220826840e8890759040c0700440079000020009801191410f0f41e80c1c01840c400380030102c5000303100c2c040e60200010564095004803204035401400b9030070b00c1304290f0802000750000750042080000070b1054010b9501c48034a075901910340040110740312000081410180b61a01c0c0c0580e004e034200b00903110050f1503042007076810580440350804800d202241c0f040050107481d80c90910b03000c00c0c8901c0301c040005507005000300301d100509140014a000d49075240361080e03a142a4100e1104c800040300c0e0800c50841c030080580281e10401d0b0413610745d0f11482034a01301d401400700344c3d6000882c1003c516080384080803407242030030311190400d4000e8020f04102814070403030340501c0d11628520300c2c4c2c1110000d0f41024015040050702c080e032040c00c08100401160204034001c1180150281002e40901c2c0410b0400760f014140018594810342440b01804580340c04a80100b010f000203c2c42403620300d440d58bd9450f21203500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 176628705 1250 176627455 176627461
    0x3150f090308061302070503042303030a090510050721020c0402181207080d05090303040f0b0a02070b030c09190806040b04060605010311030a02090d12020d021606051608090d0b 78
    0x10040319540030010905104208030302c0040c7c0044107031401c44450050303080c3c0404c0d00a100440d054140d84070103a042c000001c080c050b554000502c14142c5405403007200e8650701e258001c0d00c03035220b580d5002d04001201389032031544c4012a1440d03050302030340384151364800318590302080c1640c2080803030b0100e400b698290150903041c9440c00845102d0400000c040c0c00c1c0c03070030f4036843d142c0c1c0c24142c502c4204000010707808800d4404204540003001407500d280701c0c460b658481c07404950030214581c0010b0140c4840020018245015a4001c10081003014030b864030380c500300880d5030320540c9220b0305002060000a00030000380300c0315110318060030107229980750031b01d044021281e25402290606103040c400c0d80400000d4001d5941c841000d40c40181e98500190001d0400428410000c041c000946a400141d55003c0f07420a0401030b10b408494103035502403800d5190202c84d000c1d100c0024418008414030741c03913131880403000501800341c00d03240c0602c0c10085418181440800d070b84480e8150300f8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 176629955 1250 176628705 176628709
    0x4030e040f020c0613110114040510030609051302010e13090b091f0603080313080d0e01020c010b01080603060403051b030705030a120203100b13092f040308030103150f09030806 78
    0x10312607002c8031841c040c5c00124415528040e07401e0003a5030303c07810840182d110017031151150003160007030700001304401104034001c10010007501c2d090041080d0242008003040031103070007410601000b5816180c0182c10358095040c0840b107410411844281c03611901140d000c81c01544055010701c0d01400540030280c801e25409006900d5240300040d01481d11408001088805040c0c0c2d0f001040c50310f00440c04030762418913041c1402101e0580c400c0f58503061072607591050550080c03101484d42e000900c080001180196003191040b07a5241d003640260000800003481203008200c2c0178005c14424800240607020300d0719503045000100c5090740005030500c40180c00000c1c40350000c0c10440705510314a884451244445580d108060508602245c000c900e0071001e030b6408058400303200200041c3d0007041307200c1c00c00b400e41d20b02240c213003e00c40410030300c0c07450702d5003104c090307a400c00800c1703143d03074a1603031910000049060030711111a65070f0b26031101141e05004420f0424020380d5071480300d007042d0b81 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 176631205 1250 176629955 176629963
    0x90a0c090e071b0201030605060a030903080c0c03041403031318060f0b0a0e150d020304020a05010806031e0109020a0303051c020412021309020402210615030f04030e040f020c 77
    0x84030740150000e0800c034a1541c03107008403a075110035000c910030716801840141c003c3c00742504400d51002d0301007824004c8139030507845003204c42d0183d510304409072140e80c4148c1191190b15a000c06a170420001032019100711214108061409012246000030102c0c2c010465103540e0400f0142403800700700e50514a1080c01440701030003e15000800c1c083c601181110b083c803034060b6071030901c001c2885003c00c4c3c1e9180e481c1c0c43c000c1c0c08041003d41e510f280110044d0000c0d4400c80e003c9110700c0f0041c001040715403044410511420000d0010a034a1400501c008142c0c9107050400c40b0030364a600070480182c46010500008500c06d0325103549401308980109142e01c20981c1c8540b5452050004001c461131101008400765015118500c2c81e4882011900141c015030700041d4100b0b00005004298407501468028100c01d00b0700401c1c150744820f010800c40ca40e0b0400c000307001d42c006101290440c415980616002817081c1060790680100002150a0758040d2251446456011a016148240c140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 176632455 1250 176631205 176631209
    0xc0e090d0f0e13061a0a020709020f0f031503011103041104090b1612020f0406081b07060209011101051f0b030c1b07032a12020a05040b0609090a0c09 66
    0x2003032000401c0381c00c1c540208003081e5201680d1059840d544003041c101666031102026000348031482c0030181803c00e0780105640050b01c10001481240c200051701c150510071b88460840805541d0b2400c4442c00c00302142d0b0b0000b5100702e400742422040c5c1c15243d642442004102c5004000721a01d0b0710b400c2c244500040101c2140a014604200290001171031a22403280d001d18030404240c18208410b00460741c81051107040c0c0c051520001d0759184c0000789501030005c03141c0e960348002c16503a592261010b04c1402003c81102c0103001d21038500042d046801030900c000040c5010006c5680342e4204600b907130410b070355041601c03181d01200c82d00417560044030310241c52a01c08039842c500b081046040c00b80701c0c40100c0305c24040511b402c100400c105029070001550131901441041d4000a031040090340070046010940403846030000b400300c4140b0411881c290020106503540f0700e89800d0001600900e202540e1101040003c004103940e1071007014010013109100052003501e03d04090700c400b000b6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 176633705 1250 176632455 176632457
    0x150d0915050f070e10020c0901031119060f0c020d021008040b070912060e0a0c0f150e010c0308100515030103050105011413090309030b16080a02090d020607020d0c0e090d 75
    0x3001003260302600404204101302c0b0541d0800040141820b041341031407003000c04140d024031850000024441c0c1110200c51446040360030501c03103003000c103048010341354034880c05d800301e40120900c04603103015900481d9a14000b6002c40d030034640ea40c2c0001c408804807001d05010480403011b100038030002c822041d0b807245c014105080001d0404000f03d40c14050098003e1aa548030041d85130b0100b000c2c000c807007802d68404943c104154455a1804680451303004a5821a1541c920810b540784111a442061001a1989190012076480448111000921619017208000400581d944908030036103800c241880d0015102e50561510609442d01a840000c51002105102c645030780c0e00e001c9503110f66401c0c1d900203608069031405071801029a800a00880094020403030030700703d083c0b050103000443d541c6070091942c40e403440000b00e004ac188459040540e501014006080034401043d901d13000030040e614200b81032b6105100382001d40c102150142e108030a014a01208000c1c0c18008801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 176634955 1250 176633705 176633731
    0x1b02011d12090904110a15020f06010e010e07030e060703090c09020a0509060c0f0d030902040b010c0c1502010209060a021606080103110904020112060f082406150d091505 75
    0x800d85001c0c1da4016240807521031880744001c24200010380e5040078900d003000d481c4800d05030342e6174000c81c0c401881050782009400b60f50300d02880b1103030205015060b1050040c0004841c0d0038058441a014002080481819914901c503443c0c04020450345d8070484060358003142c48003a5181500c2400502c1d4001c046040c0180481071019070030105039a030101050358502d4a40b12681d03c458548105020004020301400035011208c9a058204d08840c5000b901c00f40001101e40c1d004443c02150088080c1800c24417100611010448074140079031b40e111403002504080e40340002440c1390340500f4500000d41d001c0303038842c8607a60f4050390b41001402a030400d1051036156480320603440610718450b5105943c0c050000f4110780c024444d1005040540d41c8c108079650b1118044170340c45200f4000c0c1e8007039100d0001030911480f201e414915524001c80c1d084030b040d403510028801680707012201100e41203018040b01c845406a8842c0740c0d041400381d082451800103500031384080b24000307000e8050f1558 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 176636205 1250 176634955 176634973
    0x10f0602100501150509130203010303030b0916020606042f1308031809071b050d02060c07052d0609010506100e1c0201031b02030d0b0102070e0103030804061b02011d 73
    0x1c400e80039414a075014100305d95640f10341000204d141c0c0e00c880000004900c00310000c400c0c0b550580c44489551001d0302c040f8050b455040307044003801618908500103a21100c00104141095000f2211a00303040c0c2c1c0c1001070045c4042e10b030856284000c01d0b4403400c00301080000300224003024007002040180c000e14a4102c0811080d20000390310a030980c0540d16280204504500c41c512044a48804404100c1d450305646030007611440a520701c00010300c944c00208080f04d600344201c980107607000c801003811003003a010101607000b036094000c800b00741816201081c140188401c82c445c110384400090549030000801c000714200c2d080318020040b282c03074251150340724510320000028040c280c4819003007a9200403400340c400320540e40404240e03660502d005540000140041030540041484070304016401242d03940075034171402c03000c000280010000f00340540034050f007080c000e003800f0a031400403030340c005c0010b2040290400140e640d0f40c0d002103480240c29100100110240c080c2508507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 176637455 1250 176636205 176636219
    0xa08241003020703050f04031505010803040f050d02271f12030e0d140102090a050d05060606280e0108061002030d0225030203041a13090b0612010f0602100501 70
    0x20010100c05240d070000d15281854011004e5980300c214810344140e581c0e03260b2900b40c0001d03c60101003004581080d0011802590100a88068900304030072903d40e40d1509041244426251070140c0e0446140401300c03650765076003000800c032107260501040107820304d018200700240c0ca01d52441d40c8444000c1d0300340320b182c004080c21510242c25240c9070603145500c000145810030070140c010400190241404200c50041d005048a404122001d58510f607840781400003078965403000910540003000043c40c80d00d04080580314140c24510315940344000d2030581007881c0c4059003001d0218a80101402c5c0c15a03101500c0c9600c801c0946400041c01725501019540b030203200ac0103813801b80c000c940c14601d1407820800c0c250003100241c01c090500030500b4041e4032940070b03000311490052001040120300420000700c0c3c4602c00b44901e404485460b109010000341200000076501140030800c0200f4450030a09d201c0c040d081c03411441c0502868104003a151503a140761301660b960034034004000b51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 176638705 1250 176637455 176637469
    0xf0a0b070c082805010b030f010c030f060807060522081c111c05070c092f0f031009090605010503060603190b0703060e01080c030c060309100b040f020a0824 69
    0x4045035802d0701c40700f542c0c81d03e03000740500b0b4070340d0000303070035100b06402d0140c0010150440c0c1200d40c0e0b00c0c3c5080003a0700814098000ba07034018082c00030654030030401000114800c1004100f064000d460f03c0a06c1000e0345080074010b1059481045554040d241600c1c1b000c0751400c0f400304802031820482001d21815240340c1c0ca40c0401c4000540f009141d540407000c45006030200d030311003035000300c41013885074490b20618020b003682c2a0004803118a581c0072500c00b12000c2c8248103d5562545580c1028400c1100d041030f9071000f07003c848419044080041d18421030f0013000003031441040c0100741913052005241c07800c43c0040409210390300140b850992800301584e40c4808079006151402107590700392007580944143e03442900241000c100005d4240000306003a0060201102a42c0035840003c0410026000036219203c1540050780c841041c203e0580c031151700d01d0030103400800da400c0e0100b200022600030541d968042010882000701d0201b0484030b0004206180c14481d4113540c0c4a008a8a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 176639955 1250 176638705 176638753
    0x206011203230919030f120306120305030f070f08010308030a061205010203060103050705040b07021311031303020c01020a120305040f0b01081506041b050d02220617010501021b0f0a0b070c08 84
    0x1643c494a10035214440c1d0894404ac100368000c0007003000e414540281580d09c102c0750303040c40c0d8042c580800d550b584101768074514a10f0740d5a0300100c690075a200e2000030780c4007414190700d4554480000a442e000b0030ba00b56a124001d0000581301d161060016003030750710040030b460030490104010300c50a2104015610205d4054540c80041240c00c2c2e100c100030150329528400180000c810052000c2802c0d111110051096081c1c928010720000160f035508800d03240106400e90031501d58010320b1080d0301c40703644903000e101d407141c4080154903601c04c0c00d5400e8110003115040a01e525804210111300c540c2c104a040d641080304800400c02404881c9072154601c2c03c200c000180c010303203850181c05a5486040e049030030fa80d501885d150701a1010842d11500000c600624240c02184610814140c100e03281a0054002480201e0300c00c1004440c0c040032641c072082d0407041080c640c07602a0a00046c206810610795102c0160400b0180c1c515540d00481080d0300011810756405124510507807 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 176641205 1250 176639955 176639963
    0x906050a021203040b06120c061206130e010c0e0a0b07020607031806080711160b0d0906140912070c0501050913050a1d0703030206011203230919030f 66
    0x3031950404001241084201010068003034000b106000911040030841406a80100d1f0382c80c11043d4841501522400181d05241d481322051188400130000080701540c0894024009044201442c141c9001c88100b86401d26a9a544441c1c030049150400c0784840c3c64030045070200f00340c9107000c81034541032140d07130002400b540f80402d401d82014000e45180f0700305d0768685080c1120b141c9a01e0001c1c4070300422200c0340c1c00a09030003a600c142541c081440002d5500e02d0048039030840c02c0100c1a64107078050412410010703a00c28004010440c07603c503400d02c441c89980100e05509141d00f40c203240100880c0380c510303d203030100140400500b001c2d07a40c904540e001e08189440d02e030306e58000b4510003002d1001501540c103003800c0080c2d8140c40c0d4458000000c1040891000021612480340e603182d007400003c016900030001404a90894410400440c0c800c0c0380200c007450881140d402c3c00d01a00141c07031285000450b20009500d0701840c461450302d00301e07040c0b91186e440d42e29081162503a01e500a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 176642455 1250 176641205 176641207
    0x152b0b060c120a02010902120f0d0503130f11041a030705010305010b030f0603030417010906060801020406020703030e1906080415020f07060e0f0610170c0607082803050108010c020d090605 83
    0x50390f42e9000313412a4200075001888a194070100c07075103660f151011040c024510380110310301c820300b0b94014829207000791090300040283c440556640d40d281c00d00c103001507a484032282c544110a517218000c1c005600fa120300310101d0081001c040c1032800c000e681209046c14101001808040c45480581c0d40c4625404904240d984400c408207056110b0354000c00c08100c480041001d040d801500a030304043d210309410040c0c155100c0ca241c1c00c0340503e0150b200183c20803002000800d116691440c04641c0042510041e101d1103e801904000561300c0074000c94020810807042c41021000c6801c00300702c6441c15850300d48101d403403010520500130020415607031083d04007000f00040102c2819050b942d0111080c1342418810b1044e4a5203030300c1081a081d00d9408821030050020850078644140500100c0c02c2c8960340c0c0d1640b910b0b070006241041e140906200d401c1035125a65031031aa642c0c203d4400250550510810a0a6448984500d000d41d84080740124a50fa84002c01d4021600145805 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 176643705 1250 176642455 176642467
    0xc0a0c0305040b07080301230f190e0109050601020607030204060e010f030e060a0b0f010e06030f04020613030f03120e070501030e0708030705072c06152b0b060c12 72
    0x40d5070718016030f0402d40c1c032020003050080070007403240010360680d180c1140030300113191587c5c010103080149900341c6401c036001e83e45c0154142018614000885040a04490990f8039803280071140e1100764840b0361032a4a400600641d96014002c0e04d03003180c0070740790561509051040140400130407103405410015001441400c5c28070985c0702d55008603142040d00c200f0305214000301f004e4403004290302d110303d01d41c81c010300280d80920017100314120302500203411a0f4602c2500a2a508010410390b0440010444080c1410320352800c40c02039485a180c821803200e49090040400c1c2242e00c100c4840351a000307000907403100000c6c06000b01c3d1000d21300407402a0303510300316504003a01c0350301c8003d0501c0003080003001c000c00032526a0036101024a6001d010f1515102180030820204500c0225241c0303402082650800c14040e491240c04038000e0313031070040109024000f01408a0032411072903490b070074124000041d4010174903405012603002e400d00c0034080301c6a03281e607070400044000c50130000319 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 176644955 1250 176643705 176643707
    0x8070e06040f020a2a0b010b0a05070807050a1e0f060507021914101808090102071805191b110a080c0d080115050a111e01091104050c0a0c03 62
    0x101450ba81803820a64540c42e100f40041c03e00c81c0080030074008031524000000c0050600c0c3c055005840e00641c070059641d2070075001180a6100c1c100100c20000204160070100d0030603001003440300d220340001c02e07a11065041c00c0f8040020003074021a2040c00c030780f0140110b41458102c004094004d0b200050603124003406a03e068000742d010504082030a00010901400d005810700080003981035581003241c200014040f9031820780f001a01001ca03e18171804180d255021b0450b5903010300407110700341d40351541420601800c03600c11105548400c1000500790300607118620700503901034203218501130a0703000f04008207482c10340010440140506840c1260400c069003059410100103940e401d10b0001d583d445000ea0034084010400b00000040d0041060a10800c1464075030baa290404102400407035500712641804103c44c4560848181d9003a0034204c03c4c54041d07961400020f104142e441d100b030701c00e00d081c11003d03c520b00d0802046401c0d1440e0089503040c0354140341c0004003141e9850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 176646205 1250 176644955 176644961
    0x180204050d0b06010e09100e060a24020a06021b0c010207060203180301090b0703022208032b0606030e0d090e010e0603030c0616080105090402210708030d090c0501080108070e0604 79
    0x110955010b4101e1051003051f07010807010f4002d40d04549005640c95031810103104046815120310100284101c1800c2c180840f00d1b101d41c545180684140d8209141c02d8a44900381d800c50101c1c0e24401c1008400b010300200204400c0080c00d50030700240001c10700e00100a51207000b1481071141414030a0296151982d0a5126140d001c0c6c0c0078899010078140108020300940080106501c90744464100300098040081080c003103a403c000118980708030820b1400c2018542055100751825801c451421300107075000e148042d201d0340d0360000c0c0c01102040f106250036001c405c02000d01c40e812805115030651590103a06423002c0a01152003600c0701c4000c41d00d5417199260302c0300203018181c14400c41213514100d007020340344070350350b000c0c003590301c84003048010203059500030b6000010034a034400321116060b0b14044c072840e2078160785015685042007403e43d4040142d0405440e51071200004001c1880f103a000509028602074200d9030411600903542c1d00f550142052400b03480c40022050394550b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 176647455 1250 176646205 176646227
    0x60803030c22080303070e04060806040f0b1f12020d0c06171005030d0c1b090e01060f0f090923010506240405040905030f07030801180204050d0b0601 66
    0x4021603960785040400a03105410803903070030304250454040c004007107410081c88020703144044050345c5540c0b6400c000751040c5480c00300c402c4d086900c1c0e20001036041070903c2032034030403400313034418500d44003083c6050704690700010001c000780422520040d0746440b00c0214070040d181407442d0002c0490060002504412840100401d843d02c15100803502f0741d84401d503840801e0001d400300c2203a032100498450300c54114000c3d590580d021050b1800642d210390007114409000702102d01d40d410760003203880c440e00226003140d10303c907847d05001c0c4c0e10001c00f4802c02006011121060f211541000c16800c60a417861040011441c2c59610f200c05000400c450122021031002e103901c2e0003408502d505000e480c003141c06520550050b000c0f0070800c2103203c03413405040b000d810454030b06403d010070800189200300066806201c03c2c440d9200d082c3c080c4004044190080c1c80789959036151103481c0000100440094101a005000c10011600c60031450031009510400c1c000c410368030074004a5500d10301e8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 176648705 1250 176647455 176647469
    0x60c0c0f0b0403120302030c070b0a1d030c06090c03060c030a110313020f0306010b0301150c020d3c1112070b0a0e060304051b0d060f05010e0a0c02060a0f06 69
    0x3200001000110351008104a07031040c4400c415009803107600750101d0208441d25032180808003d40000220103400c9168000512071001980002d000e03110740d400000c0040d00907503548002001c20b80640c0801c03c1c030b80d21060144c0203081c20325161001c03030b0715050040c0443e280c80b0008808a425003007150030000c0d8082070710b1845038407071400c0684205081c1030b03260140c0c000c3c111410405142d00b0041140c40c140c440300c0048501e5640b80c10100d2024240d0b100081c0b04220400100400503a107400743e0000c01030141007902c0040c81a9a4940071490792026400d0030f508549243c0040320042659218855800c40181e038100d03d10700b004120a003000d0010704425001d42600032030f02c41104806440f800c101662913080400c03140d82449124172045d01d010b07007030b0741c0b0208d03110440c1c401d85030780a4160714001e44800c955001d5596110113071003e03046811006511003005004030b055610748a50f01c01888413090040446100000e0746640300900803882c03a5854201105140000e900f000b4001c1c122 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 176649955 1250 176648705 176648729
    0x305040f060c020304090e0d21090b04080909070504180b0a08060a05070f02160302090603030f07060501060e090c090d0302031303050c0a050103060506030a0507090512100c0513060c0c 81
    0x10b10802503c90317101c3e018030300702c052174100b4000390380d84000f03070120101000762191801030411056411409060040d4034400d941c0351602c0c0c1002801840314140620300c01c00900340c4070b1000204103c04000024404410080c05000810114a5521040c0e13121400b026001407000000800b0480300c0c2281d03004100d003403090005101c8001c1095003c18403c06139940e80d603070f04030036105080780c80310f022080400e0400781a10382480589002d40708281c2105000b41220300c0c101070394210310640c0d00007500a5604036565801040180d81010152070710b28001c6950741110701e4505d05403000c41c050700e041070b8060a0341100324000c243c0204100d801c100c2100c10a990010307600d00d0501c3d687d0000318600b038020010100005a594000e000341026200d00a00945c155a918100c03540103207801008481002242e560000d001d407210b03103034500c1c901e2214000c0c1c012109005072210030369190600100420004004418001c06409240000c0d131710a882c020400307a500b801d00005142c2c864000c5062400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 176651205 1250 176649955 176649971
    0x120f090803040b01050a053a03020f1b09040807052a0a1203170901090204060b0406030c0905150705011b0206100b07051c030207120206011d0c0a0305040f06 69
    0x2080c00245200754400c4043d000c0c680c3e00c031801e00c0f001500e01c0c410550042c03581c0410007242045080c5031241c60445001c4044a003c0220041608104080082d00507810055641d502e0340001d0104090b040c1001c80781c400c40362040c80c0441d0018000401c06084504003080348000c110f4144202c000341401c40e130346080e12a20040c901241240c20003502c0b44640050b2000040740e11a0b402190f0b041e907050340303403981c01c0318030b1064920003650003c0405003203558400c0c402005a032a407107010040c1850550054456080060150032034292006030000e00041d05d01c03c0006a65032407600c07225044805079140c9860842c41c200e0702500202c0784009902d2180c8079002c0ea11303980003d03058840c64800501c4558140e50301c0e40c0c080148162003001d0901d81160143c0701a840700d100600010401d02d00d401854100c0079110160050284010b10303006030010401007010250010400c124100141e6407150581000032003403801d0311401803030100b49501d5130700040a1042c1a42c03900c07a0315070403440034412a6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 176652455 1250 176651205 176651213
    0x181e151608101a07080c16150e1309030c0c0303030c080c0702281a0901030506061201091d0105090d0e040c1205070e0d0807050105161b260715140106120f09 69
    0x101d42c1d800b6003c1c402340111800441c0b90301c80e520289180320054070082d800e405520b410000760026000c1038060008282c9002c3c002200501c0100c0110301a680005602c001d60000410014005d0503c4041900c00c0c000040917a40b400301203802d011030003070303c18074005940d0008216611182e20400c0c0740c409022283c000c041502004040081d4240e030f04001a9031401d041100720300a4001d0720120001c407000601c00080345501180082c6c3c0030b480307024004200300e0421401d60700100e540c00e5554000907400e4142c40d42205114801117000c40e030a1101711120040181040c0b081c03494100d038149c5660108400707601070341c82088400c801402c407141500c8282030443d02680103000440351981b07040c0000701c2d4400000301ea0072424407a991a5035201090705c3c8550240001094190b84040301c60203403808900005d0700200c040c2034500e00d0b0355205c4545042044011300080d0b5804070b45c2c0e0810901100502c4860880381c107495903420840342600420744e10f0382c02460761004414603685000c000000780 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 176653705 1250 176652455 176652493
    0x60d0812150a14100212040b03090a080705100c0906020d03150b070b07081003020d080a030f020301090c0e03030f03060909010608030f090405181e151608101a07080c 73
    0x2500c0f082d2510070905102d514220b0391402010004072010384144020301c04501c0800081d500040d107403080b40c10f21081074a0b0480d49034080841103a1503484003040302140c40150140b10101401400e060182c0e6203030090180d2070f58002a070b42c01c10140c2c0ca6804528503074600380d610b00500380c2da150003500c0e820180380c54003050340c1c183c800c40c0100391101e00081c4c10300417500d14141640d502034040480d0600039960202c0c00d07007000d000881410340740c0c180c002021a1a1015500031700d103510740419588000d40c805014031240000c0c250007a081000052500400681140d401000959510310180c0c0e8070750304a401040580c02925983c00b00041145041c24064040e02800b04200c50811050302e0f00500c1c03003500240b44120745000e800500da00104040b400f01c02010f03008641e0705407901104444d2680444190850b44d81d80c00346800b020820710254048c1d00b5541c00011080508803c03818070300c0882610942e80400100c00d01c3c001039500c104040181556039102110b412104112540e03c0303c4824 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 176654955 1250 176653705 176653739
    0x21c0804170a020f0f040209040908040f080a11010e130c03050f0105030c24071b15112523130603030e0609040902060d02070605060d0812150a 63
    0x40d0088050810002600208464120b240e00512440b4005180c00034012891000d0303003c9980300d907003480b50b44110b454038080c40c80c0d5039114210b1550b43da403c03d101c80300600b4154110010b01c0e804000f0780d8001a0010085507904c4809090400b504600c040015a480740d00d40c00c0f907208076041010215010313800d500514014151400712861030b030307291403d0569a80c120442c042c4e00c840c0d16180c2c075516a2130300304e2210341e503444455103d2405006403036500710b529100030180f04202303a416041080c3e00d5070404401c0c010f40300b481c00e15070400c48140c1050355045024034140c09207a01d40b41c0d03c5040c1d06115651f20051405c0c6480d6411482d61071819100d0708502c02540d4050305400d085604000054410780c1c0982c0e50503142c8105120300c110500203550002c0c3c68068001d1f40d03c0c0347c000050395a98002d403080c0c80443d040941d86494034038110080c3d86018000074040e0445284040000351610700350340f14045000750301c00c079550b2443e840018821030f01d01469042208081c0209040a0700d1038000a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 176656205 1250 176654955 176654969
    0x50607120206011406180a08190611070b0420040c030b03060105190b0319050c040603060f030c030f030201150b07050f1b060a02010209130914070e0a09021c0804 71
    0x80c1e030781ca548024441150350001c40c4d00170b03010814042d2458450740d000503000d5001c4c0644100070707150f14400b807802416402e01d62045650064203000c01c40a4007494480c0010303250100d080c4030043d52520520306001e00300900304540b802800c030b40c40c01c01c20a28200b5440c020000e01020703a0004000e4002d080c54407099009001d03400c004921420207100c405008150400444411031030424000d00365000580081d00d2032001010701d1400e80791601807030303018074202d041050796540b411002600721801c070317407003590301401000c804c10100d004103061100301c076000b01d000d000c2480759180490040c250144807203400300c4400c20210b10390b103030000517028681c4074104888041c5240c003122a610211000c0d0b110300d6050351910a01a410000003601c62130702240005410903100c58001604080080305050741140d89503165001c0c000c1e8484000008001400600040d5051030b08aa00b0302c40c0040c101102c4a80320a0301d0030454485c1c4c0050115081c2c46810402c0030320385490805a00d5101d881224 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 176657455 1250 176656205 176656213
    0xa0905040b070c02010801051e0a0305010e07120b0a020d02070204060803030603100506030c010e2407030306090506010f03020f040b03131b08070306050a110a2102090f060904060506071202 83
    0x70038040c080c40742d0f0641c03603070141c4a0041c160710f030508008000703011140049400b28448508003098803001d4281c00650300c1742d000032510241c40d503040d43c680310b411b0313000895601130b601d100c1300401d0b040102c5542022601c44003590b50046940101c0283c882d84500030b400510701000041c6a0101001941c000d202c00c50a403102c0e03020000151003a22020f03240740d5815086821b81003420340c040d007142e01c6a054043d0108016032081100f81c9203040d201e5080040c814000a01c1d102050f605100b000701a0074190350402180c02c00000081414808aa1401c01c0c59400a80503031019047c4003560f00074543d56140564a10f01040c0311020401c116400301d03024000d000c20441d000c04805844020f45003200e000345011803843d10307007401801000c2c4c2808182c41d0b03501e41032034010410742d00800c041241c54980007103180c45035412074039074298019004c01e424030501c00c80e2250340c0d85030f10405541c007007211310715121006200003030000c110760b074011948000b0015000c1d04102c600b0420b00020f018a800361 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 176658705 1250 176657455 176657461
    0x201060603020c100b01110d03090209060a031a101a120901020c061b04030c17070807080a150b0907080405190321090b0108030c10091716020a0905040b 67
    0x1d400340e0040515521682d00801c40a00d4031007030315030141e0390f911030501d000b40c0e0381486804d80d541130400380784004000a03107490442c4190708000f1031040d0000000d80d207a10340d9506d940c0780d80d440340c031994a251040c2c0c000f01000c6007261813843d01c10406000103680c2d01040800c240300c2801d0580c040c50308000e410b11804005106d114062003520320300102c02002d02540d50701c131002d1a60803101403207071904913001400044007080c6100d00070000703080c5008030140520241c010641c03905807240c0c054016984855000e03c4541008144510050b82c04079601e42d4115200100c400945250800160056208000c200c02d1a500146c018042d038016403e403004086d4800ca0510390200c2c0a00c0500810500e21011100110800b5401d0004010540010345c8410a503a0210b9062081e444051076074800b18041c5043d10090090301c4640d12010070400141c149913846c0b042001c0401d07941025000e0100ea50360713002c0901c0c100c5840182e8014040c1034000d80740c402a6000700001e90303040c2c5542d0728030400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 176659955 1250 176658705 176658707
    0x30a0f030b030703120f030f02031617070207120f050f06040311010b2101090218070f0201091205031909030309060b240d0209060d091b0f06050306060408030d090302010606 76
    0x100d0001e603030300400d0b1001140c01402e400e1b51180700d401803c100f0540c0ea851180050400b40c0b0165004410140f583c2c0802c40c03191800910600c86070f40b0400b1017000450520151640004204c000c4480580c00303400950f480b401d00030301c3c00f180d45401030302e2805050b00000101a0104901d0301c50340c400d407101c0000301000c000040c01c0741d02c0c0d11015a008030b80030400d45581e1a4000c41c4000c100c00240010030740d1480c2da40800c607a4881844190741400080c428030800300d400c1701c400340355544140b008006101e2103032180940c400c823241d0100c3c1440800401b18914125052034189001c004000c24000740c034032031800a0080c080080141e03942c501d40003400e038086c60001c019038061240c00c002c1c410050071312103944265611403c1204440355003023204010035101c4070040c010001c81d20b440050255140c3c10880c00c1200841071501128440301014030003540300380c0c090400d44449217480f685070396440002c51880c1c8280c2d00600361611010400d800c000c0c0844d04648900c51196009111842d59464 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 176661205 1250 176659955 176659963
    0xa02070614071806050414041d060402120f1b120a150f0507050901030c092d080102030105030307080c2b09050405060f0d0c05041b0306060c08160c08030a0f030b03 72
    0x500c00000c0040004004c0352000743c001d080d07680402480060081809c2001c103050106007020349415400c02c000304025403034500d10614a2245080142c5603107c28407c00503255158980c4c01e10b4074401a900140c2e151301d44070305c1042c00461144c11911044003604103000411204a07070401e800b8104100c0c0300340807840340111030081c0070948845007409401c500550141490030f504208010701400001a0500400c0040310901e1003000c444c400c6544504c50001014070b1500402c0403a0300410040010f9140001104d06050f00a0405a165981c07554034604284400300a00501a0010021000b90703000c00c0d400103007100e094a8407083c0c203980c1c4d000c0c4016501c04803101540701300305800e040800d003052008003c1651241c17940d40d401079101c0001504440b08944071807252040020f03021040b603010b00c00d4201a00701800d1510302058079070b0700d10b4480d00c69840881c011150301000082007100e1030000078050324814044e2034544500d81801803050000c070203058002410080c0c2c142d41400c000ca = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 176662455 1250 176661205 176661209
    0x2a1d03070e0c0d09050706091e1514040315050610030c0806010309110d0507030210020109170903010e060c130e0402030307110102030d060305060136050a020706140718 74
    0x1e070080070035540d001804a4550010020300d81900e03101c9801c0c0b07001034824486180603018546030f034201542828002002091060311106030156100424083c208492490301f00c01031031454400d03030070180440c22000a0145502c003c00d03148580c1032850344402c060700b02c40e1042c2010764072640070060010307044060381d60300c5134050b021441060114203154482d80108000750300813142208440b20079070119000c21644441950503030000c94050007185018003c00c15018034510080c001900b2a8542400000294042490312800000d0b000c80c3ca40b020b4200c100b451440c80c0640d4210300e00704142c0340c0c0590000403140120499120046030540c030201100f40155005002142040310995070018819030300c6105c0d03811341c4003d0041ea500c0e1110380c001d000280d4401d102800f025490b0410000c90b00d010010400c03008030306060f01e04001d010b4250500c00028910002040070340f03544200724001d1240b440c02a00d0541040c0603035054607a20140701d40500f010341d44101c078031054034061070a074802c07038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 176663705 1250 176662455 176662469
    0x2100e0d0c1b080f060604050906010e0c07020409050610050a09020a021504030c021c050c0103020f1801120f05040b01050105090307090e0c060a0e0406170c01032a1d0307 75
    0x2401c1d0440410401c0390b507010700d040c9a0807860640c1c0d458900c000c0c5441e000001c0703400c2035400b880c104010f41c182401455040b80d54003001f090345504104207031840020040c0303260146040800d1010a5590350b41200302099085801c1d104182001d0540c140d4480e11800340d42c1c02502c000c000025900002e02c00c5402d0000c69501502204114201c0158202d101800c00c3e01040070081b00c10016a89002c1800e50480d40030081d0804a80700d846d0480c103100d141c129030350616206000c1014001d9071801290050410503143c0c07492150540c0043c0c2d08084031301100c00640e0320b003211503840c030141d950040340924002c5071400792070380e6200011511441441e40f103d070981c02400d03080000d150150403407040d480030007060750700c1401b03c01d0201e1665008481c1003000030f0b150009042c101c0c20903200d404d000c0c004840820090282c91a02c075956840600030303d6041696a01c1d010b541954900c0e0311680c503203101e801d12402e0f200b89240c000e090200c0078078040c0c5c2d805810440484079240000d1100c04131000c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 176664955 1250 176663705 176663717
    0x40605011d0d050f0f06091c05070f03090b0f1803010203040807120507021003230403020717030721090b03190e03211806012115060602100e0d 63
    0x410402c1c00805601e0140c200c400344a103840b4040110310901c440a00e6800c3c500017400180f80c150803603031502c0c50411807582d0301d01411000000c5030350301008661843d6005801100c0000f6949400c0b149188682d20002d101c0b0300c042050b02484610800824985481d402062021a40842010300301e200950b4000c200d2082001114002011182d203200c030803116041c0703903060070b4454001c14890701c505c0c482480040d989410b20881c00307158030345d03014104e050903a501003507107441d03607000e035131403469014601c4520507120741700c2a4482d08008032260250311400c94060094400546080c03400c070303550f004000c2160f40c0c101181c4682c1c0346060701e11171500c000200d02c1c050404189940240b80250386650030340003c201c900c0001030300b1801c1403054214030355045072a00c0c2c0701c2038540c0680b40d009020005500082e004104e00d100480320074028000001e00e5102c400318a00c1c018162600759000404c0da242080c200051458000c20707000a120300409040c803407032100c41c0e000c0b61280010108000400d42e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 176666205 1250 176664955 176665007
    0x8070f050408100903050c0102040902120a0902090f150604090c0306050d0c0506160605250302091806180f011517191d1e0a020d030c03020a060501090b04060501 71
    0x6450300511300190003414264034040800246c182a0b074401d4003d002c2182d0000b51080c1c80e40b140c4080c0c160701003802c0c90100581c505035800180f1001d400b81508004c0034a4a001c40c90840c0c1c0e0a101d950b410000601499550f0b69503031400025080c00c290410120b880d0820000d0030f410111515664150b1214541024131304240030049150400100c001821003500049000180e007407003501d0203056920100c803800e000142c40c0c18600301410030b0701c40805006200009150f1100c00803003071030b500410b14852150b501c110102d851501c203184880f5080b25a9004e000c8000305503090541620340d44141c208180020302401e880a410400c40401c59131301083c00030711f00300c01c04400122510620030010940d00300a1a1900a400c0c0300302102595410001d0340d00a111614414001104101c4000e8214110342d0303000030700c8a521000b00541446600c1e1030642c2018402e016a150a562012003002156158a804801032070b4060300180075910f0070f1404240c542c0558458003e0602103019140911 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 176667455 1250 176666205 176666233
    0x61e04080a0c03031e09050709110405120109020d080307020610121101110318190e070804060e06100302010f080c030105010f022b081503190515010608070f050408 72
    0x1403a450b50540c10507603a03074844c6050780e240181c0910302400910010031840d1140c01d106040c01c0703c96101c03840e0a40707400311001880d43c52a00b1358044500807140c0356401c1c0c51020000d400b6045080000b5840700070f81c805102000341100180d40900c0c040d03400c56000c0c0ea10b1800e603240320106402001c0d5244500d40d40305000400f554250b110856041c50f200e520140c18002162454003d049d0b6010301c10a104080c400d142031402d144035002160415112405290130141a5843d070003070183c00410040d88002028000b140d04100c0c0e5590f0341e00100c0c1d050349024442691200440c0c0412800039004041c62140a0700c1031500902403070202d0031041c40c5034030f80300041d651040700e980900150300403500140c54564604d90400414841074000102c040c250040003444c11100a05c03091261040c0c5510115545001582e113400c62404038600001c011a0300340a07180c07800304c041c04170140141703000105075240d20108141c0614102d498000100e00c0184040d50140218082c4000d00d50042d1711f00c03081e03d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 176668705 1250 176667455 176667467
    0x8040206031e040302060108010b0114040306150b0d0c0306060206091b03070b030f061212030114010c050109050a050c1813032606011205070806041a030f061e04080a 73
    0x1003240000721981c1e0001d002040c440c0b84104940944c0503811240040018440038018540440320900e0005c42c154001d0061b0700310b9010340e0101401c200d80d00c212305005210400504005425180c901700d80360f65059800c1405000010355150000303040a02c0002e540f400000c0b40c9002c2c0f45144007810020980507500001e000c01d04c05410361500c600ca400181c07454100c0c00440c0940015280c4e10240d151180a000c0c0c04201104015580d50240080401250310701060340c0c151284860f10162102402c40100d86079181004090595407810180300f04000d00011a0107009120350161811212444200b0810b58071407030902c03150038610700008450740381c414410b034001403107401c0042a80203522826051070031040b050105082948050048a40c0c02c02420700400d0309000003400340d454403030781c0240203c00103030202d40210b44035031140c0d02c1c1440d80721030034110001c09800c4800c1010031040d011340d202001d45480200034030309000101c0d403d103480030780303807085800081c030920b00f6030505011144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 176669955 1250 176668705 176668711
    0x12061406061803100c0503010302031903090e0604150902130f0b121b07050d1803030f050c0a0506070201020d0b0303090607081c050403050703030f0c020706030209040608030a08010e070f0804020603 87
    0x1050040341340b100601603091103480e0b0b40b02e9440e6203403510f03503045206240c5031072940d4240321040d00c400101c0d480001d030b21621010584100810000b49a10340c140494040c12805600307001610001c0343c08907000581c2c3d800b400340781c416902c612406035500d5200c00b8091408d80100c82602d03100300071400c200c0803d40301803500300c0114009101d0310090900d4100540d004501d040701c203504140f040e146903c1d1b2120484414540016003007a29a155690241c16201e121000809110020901072040c940c140032141d80d16402105454842c82d04000c0203000358424030031951000d10340f003203590a500340042512007800c80641180d01d0082161034072441900414124000c48528141243d034604041c019140540e00c6525500c1d16201d01c0d1134080c0641b200f01d540c20040514000c0d000f1030140e8002610000c950040c20b00599804854000c50041e20594000901c684000074005510b603600c1800b19040314807180031030b001901e0b20841104c400240c01da244c1c000170200d4012901501d0300400444d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 176671205 1250 176669955 176669959
    0xc030b1011070905090d14090904031b1205130801090210030b1309030203040302090c12283902030334181a070f050309060301120614060618 62
    0x4a4269101a02416104d04031250210364000280d02c545c1540c200504802c00f8503d00b003ca0304100c05203003c034683c161b00520203401c00405441c0111303502024140d2064054020103242d40140782035501804a503c101a459041d00e030b00200050010300620070200351690003081c485844400030421005480704a40c200e900c0341500480b00b01006c680e00c181c004243c82a000b840d01c072441c42c0100b03d2488001000c4c8500d0403030420407004006044103940d54081004e800700c0c0300100c2880d400440c02418288620f00203803400710b104200c0c403a0200310508041c50344103881c0c40c6070b1600703041c146081c0245074900302580c07060001c0350040c1d9400c041a662070803802c1d000d8141003112240010f070300510a400a000c0340884006030601c503d0070403032902610903441c000102ca051059110b4a501c00c031200902032562081c2a002085010300455224440081c8403503181c3d61205c907601e460400800b0b0403030f4107619144901c0c50f0142c90222584c402c400c0140602d09002c040003100c1017214100301c2a0ba = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 176672455 1250 176671205 176671213
    0x30916211b080d0201050f01050108010e0406050415090c0f0504140a090f0605010e0711010e1f140412030606030506090c13030602031306060b040311120114010b0705010c030b1011 79
    0x7056440b010407070a4900d18595001082c0c504201c07441540443c010303000507041019204c0140004001d8501c402d070000da02540016060ba039608100140703288000e100c040780340c100000300c0700380034280405009840c0c140210450302e40d960810042140c5000203842030b03200c1d5244c00600d40a5190740712400044c0240e080c90081c1510fa92808100c2e48242c00c108180340d060000d1041044d4484141128080c0910081000054596030281d44090041030b02c942c4448108180c071600c0c850b5008584000c008030030518041c00c040c9460a240d220062040c1d000925080c00040c44600c2801507a0148030003030968072541d120070030403a90590288242d2024015000710000000d031080c8000d521a402d0156000010740407450048107480310740d4010003029106000c2800403491800d080b1100b0003003103c850b807150900c001c2e02c5024050418000030350544000000582c4d0130010700a04805108500030851410408000c1c0d04a84002c0c94a5801800740c03150a00424090001a00c1a4200e00c04036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 176673705 1250 176672455 176672459
    0x12070503031b010c090506090f0109080102040801050412020705010e0f031609050106110a020a091d1906230f0907090f0b03010c080c07020d1502030916211b 69
    0x860714590040300c1502c906160300046280541d000e02c0f591140403c24913041d10f59500e003000050f094050b60079814415480a080c00c0c1d0700da03002c1c04400c001061b0880080d074846a0700c0114500030700040314140c5a90120303070701101c1c05a00c00f20740315080c0c0318140c48a442410f060014052130401c1c0c4141644c2604c22005603241c40c120980692004010104000c03031103605005005010300706400105855134409000d120040e551012000c06803201108001900d070501d03909403101100c0b00c1c0405440b406a120b200e1140c04004083c0e0f0940c0d03020b08018020340d981308a007066100729880301224680303224404942c40c400181071544d0803001541c210f800540c2c039040c100c0200d40414411b6060107a860000a48030b0030203000d0300c160001e50341440140e610b0300092800c000d214504000b442603c00d14032030030130000c0e03c1d88246c1000481c0351046440e807421814042d603401d4000e11074a4100442c0d6400150314281103030b1030a1900000c2c40e0640501140c1d550b41c0c000301458011962005000140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 176674955 1250 176673705 176673709
    0x703020d05042103020a0219080912030d06050609090a110c010606121104050d030311161104060509060d0605040c0302030d020304030b0708070516020d0b010f0302040f02070b06120705 81
    0x51680030341d0082c03c89084260501002d01c0895103030b00d02c0344060500620240400f644c011031400c003000205200c0501070902860512454440d079071805910a00200c1d05080e40c80d0008003a2801070f440c1d0320308000b1180c4442c1008001d019110740154004030890005070003014540000703e446d83d08000c814101052002d07411b094035500e0700728000244880c6080d6503030402d680a00ca4407548040c0040d89010308190120301c500d40c51550240034140c0700c0c0c0440300d8540c891801c03030f403001002c602e6001440c6c8151030003121028581003000d11032414030001240900d0005800c500621005140000c2c9a0b4a80d0310000035160043c82a500c03564200f4000000d6101440494a000d01c2c65029598690030741c40d058100d83e1000d0854000c10500000704011030b41c01408a60041740034804036200d540192000422420400c80c004001d2aa01c100000b52800041c040300c058034822a8103000c6403c0d102d01ca58128001e006010300441e1461022032414103120040180401030007058804450321000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 176676205 1250 176674955 176674961
    0x9040603080a0f080a02070218071710031a010e18011404080702180f0c0304061506050d0e01020708030f04020a03050105091516140a030917030702070b210703020d 72
    0x1002401141c09262010140313580500e07202c0c0c0c4120565021802c090b807940200f5180304140264400d44900100030502c3d80303001d041e0407003c00c8045410100c3c070f803818034000043c1c20311603c42110100c1c11401c035500300b964003c0702c05041c0c45640d01045140e179074008070342d205c4044000210055550f5403004000c40d040400c1460711a6000c0c9030081d9035240948180814944920f008104000035442840110b0868110302904104146429601d035101c90034440d005000607000c000c2e00502a120019815400201400700d00304030002c204043d8190f0a0b206082c3c1c031900c200103000e100d082001401180380d80103110342183c000f505010400307480307559582c02c445096a028600f5403003403600c85009014080d0741070707100400d80705014032130b860f80c8006084480e103484a10301e01c40e0b000c40c04c8a50700780302e5841a50303080d40102d000701150301100e48840d8564019128003005003d5104c02180c0d1a19000072108440c00340f0786400154100c038213281c5450710b0041c0070a000c0580820040d40c0102d5280 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 176677455 1250 176676205 176676217
    0x6040e01080607140c0312040809040507090602070f060509041104050307120501060f1503091e0b04060f020f310320090709121e0503041403010b0f060904060308 71
    0x1c002401103041c10240540045580c0703a003003c000d4401c029410000b0320100984004c41660582c039181621180303801030b4240a040d140340d400c00e00e00070401503903541c49102041110096000d030750a40b52940800d003612006406041e010075800c000e50920380c241342d40202901c2c08022481d0b4282925100068100702c070550005040d840e02c5001002803040030300c6a00e00424209080d0740b400c2d440d02c2c14450840501c254107600741580d5000750824003c102d80189600010b0380e4054070008440d241004800360700f80d509071162840e00c1d080d428442c51502c212800c00d0b080500450520b40700300c441c020080f04e0b4006010041f801403006552160b407d8007101d010354131a806c00300314442681c88242c514100080d81c1d921a012070b40a000300141c00c464880c0958555101c600d9008070142458050365940308029140c40b608030f08081c081c4040403001c0c00940700341c20701c40310300703190f4050826090b00d40e0350603469444030007007400c01d0302d625100004004002c0c000e4008541c0d00c1c1c0da51030349002a0401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 176678705 1250 176677455 176677469
    0xb06040f1811010302040f060c060914030a0806090403050f030c16080a0813081e091009060207060207050907030b03011e0c02101802090603100c0201140c03070f080606040e01 77
    0x15401d25010001e05150001e40020203103011802c1a10341a40c054046a01e4440e00d0b0500c503032030070800b042c464503401588080342c10200410301240084e42440e5260300881020340010504000703c0c4071303490071805070b501035a01a40d032a410150140c509062640c00980f1f4051062400c2201350a80801c104003900d8560140054903121180610081e1540900900c1d030032100300c42000c040e0008011303c00b134464600700c04012510400074900441582d12070008119804040c4103e4014900d1b4803449400540b10280d0035070780d4070b694071501669503031300c54003416911154107000110071900c2903201c0b05065100400210b92240700c05050004020300d01042c0070601d441d4085070b1009501003103844a141c4030030710704029140221080011682048400a100c0c200c004003240003030754100b00c0c03484150507844080000059a40c4041c0c000c11590b02007400c4285a140060740a50f40f9600b50380c85800e183c1c84107085064881c000302c6180000605180c0d00901c14000864090545d100c0c09028000d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 176679955 1250 176678705 176678741
    0xc0504120c050405090c010914030304050a1202040c050c03030a052509080607020d0c060209010c022706060a120905070909050609010501081207030c170f03071206120b06040f 77
    0x5180030f0000b80c58004114441c254454800340d40283d90140d4a0000c440b948003041c10548100c03000032b401c3d407080d40d01960b40816a10404a01a03180300044054148221405c0084101c658020740ba80d009800503d8a9500103000085414031590407456002a2a13040c1c04007000d00e0010301070880707295aa0520000303117441020f2000d0034081001680014440c00180950711040300b0003090303056800002000c803500030541c01c400c0d901401c440c0140b00d50080c04140924a03c41002c100e408401206615211105000c98250708113030701100d0b03c1000b1941c5e41070544c0d80140081c0f0146c44001000c0780c80c1c0c03041c981c000445100a110711244d00344118080d003024100611210309490060b001005650414030225002003101000c86040560504007004c4980040c20045074554902800d5514840d00107416184803003001c00030351203800d041d12202d411280013124241200c1440c01001c03201a21403281e100480e44d503898181e031001c00240b0105410002920040665003001046005009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 176681205 1250 176679955 176679959
    0x20c011506020a05010e06060a06031d06010611010b0415030206030714030c07030201060f080a0b09120417010c08010513020702041d01050907080d09090e030d330e0a0c0504120c 78
    0x4d0207000308100104c02c00d0080c911420044006147e1008612031b91051594800840e00da0807100d00300102d19110141c2030702c400b580e48607009040322040500c014030310f500e800b03000c4000c3d01d006d214140e014921301111510b050b096509111079944090000c60901901e44000e150740c0340e404c0300452082d000380942c42d031140034929020342552480d400c041d800210512007400894400100c1080181d0061400701440d214100b40c6401d100c030042d03008940410000300800c0881390203a1070002400300c04000c100030940034004451084080c02400c1c4c3c4001084001800102d450b0003500c046400240002086580c0000c06c01c2c403051844020301e078a9440f0010080115800c0c0912401010220064041040f06d5000203113141c03024020240c01c00d1b52001e0381080f004042007922141c50080d04204980c10f10408000c554264980c80241c1e01811210602d120308400000242219080c0403000f4054942e0700342400a40380305007090040050030b000004000c4542c00d0b10741a1b090103410401d40042c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 176682455 1250 176681205 176681213
    0x12040806062806352215200304050715050d150f08060702061b0417010f0b0409030203090f0d02090c03041208010302031f020c1b040c031e020c011506020a 68
    0x183d00f14030f01d000b61130724002070316070030300d0005a600e5000c81104545902c9084104101120381d610700d0000d440301c140016001051040e6074003030040f9440f055008800512007031811460780c4030458008105030000b0004100c40410034000c00d01042550030320380e080c072800c1e070140c8085400079261405c0e4141d2502c000c002c0022802c1d0f8200251030118081d12061404d0b0101955508015240c03600d000c80ca50300400b4882c0c02e80b41903c0c0501032001d8a24000e070070a50b0700c640078055003004010042d00c2d003241807245182c00d1047c803041980c107130003031070401029804110b54403908050054020100d6503443d80107944800a071841698502c42180e03e0341480e04280304940b2000b09040b003801504030042c409070b42d0000380b0600b180c0881e0140354031229040030001c0640245240035801c0d200da0b040804480c803c140841603c03041c03d41741000302c50302641084068410007204003001903c1054800807010301ca1300100b03004031040700082999007081840344004951503011400503080110801c0c200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 176683705 1250 176682455 176682497
    0xd09020f0103050f0c0f1c0b030d020705030d050c0c0a120302010b040b0f040b010c05100b0102060604060e0f04030509060409091e0b0703091515050312040806062806 73
    0x91002842c00b0003c901c0c0c000c440b46201074000c1c0451208030304c0860310145014906040b9440b0f191032524489038000e0921800001e041c01c080480d2080c010104501010b601c00a45d4200700d600042c01402149841032090350350b82d108010741001400362500e08100e07622803e100300000c00001198000c1c150003420000c4c01c6800d40b10300148503e08000700c11a1703507914400c600c042140104c50004071880080e0043c0d58280f44c20030f0007001805016611507102c5c1442d07219110004082c1c0960303400c0d685407406c203c00c035280c41c020365580c492880d01080c888800ca001c3e041d4010704c00d0900a10704800a00040d00c981c00692102c00c1c69a1614080010044a003100c550a00490840b4540186c841e47d03c501804000804503410590b44114000034000642d220604030b040c403000c10031240c114400407142036200d5001c0e407030080c812050201742d0a04040c040310304407a0410f02426507034440d44104940d0032624000b00b0001450880d5074614038090b40c41020040c0450b4035070141c0140da17103000041c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 176684955 1250 176683705 176683729
    0xd030905100519030506030304050609031f0e250909020d05060f1602160306020a032307020c0d030c080f0408031206010f020708070311150c0a060b0f060a03090303060b0d0902 77
    0x20142007405000f901d1f02d0002c01d86080e0b80c03080750303100d4031990114007182c5001c00301c4081000c3c801c1c08151000503400c1c641d00c062400c5040c04290b030016803070f118038406596491808088603070745005080181035400d078001000c42d131009010b140031f05100d8503040d140070000e8421408070300c1c1d01d0091081202c103002e0486030340300710b50000e0f1071185101e80412410307a5280c440505420340029205a20038860362010004821041035000081d0302203062101c11385080328404058400d00807850081c1c641004c6050b2500d80c10f43e10181a03140907079422509400c0113101502c00355041c003010136a14400c0c0041c110840c400110105945403d2000400448508090f2815500904030030f0007102d82c04900401682e400a82002d40700e00000041984c1c0c42c00c2111a038075441022540d10310720342c004920180ea0034010841840300480070001c110841014052080d840102000315032211406030300407095450007814000baa007513481000e10020782c0903080c8d85848503a642c0320401180740549880e05 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 176686205 1250 176684955 176684957
    0x6030b04030e091308070b0a151403150402060f09060f0304050d02070e0c1e0409060315050903030c090108340305090313051207080d03050a05060d0803060d030905100519 75
    0x40711907103175154100b25108210015003070500c41000207810103041e81111080411058480c48910341e01d00b040b44242864030308891190040460f800b01802503071034010b01440e0000d0100c2d181460aa0018116602042c00e0b16080407080c0825100950a1b202075403045000d0304c00340c00c0d0482c544000908000d1540c110031700040300041030105680881c0151013204680c4000207010103c0c0e290040818001c580c01341000f00d08000002c000c00644c0d0010b2814450002803e019603110740d10785944a010848510040580500030700b041507101c0c2c2c3c1c8264100c0e84aa03d5244c200700c441e8180d0070b41c0110b140c0300343e0180780310300001021558548942e9500443d0f0340041d5061440104006000d45058070480c1d1007600440e00c5892001e0301030191000600c1c40c0c3e0111550700345410030183c042c050842c1c065070182d00d0000000e8403070801d2611500029413000c041442e40c0c0e1101d0402c410046010001d41c100500b80c400400c95444458041a848106480c2d0a4592030050082581c0740c0f01841120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 176687455 1250 176686205 176686231
    0x7290412150908030a110d020c0304051003060e07030b0111060708070f030b0d080c160603050103140d0927091b0611031c0209040c0306090b0103090201090504050a06030b04030e09 79
    0x80343c603420580f501301141038004200010903418581c070074003e507101c00319030030710004000640310000401001250802c4d9001003c0c940c81140070703004c0300c1c003e11640d403141e032070007000481a85c482e9014100308541410001d00350b4059641061901c0d4086408402294120040c003c24a82160290f481030303885140c10b201111800002c00c84240d0450320080c02e5540124a080c00f080c0b0034405440d00b1090001815074642e40c411000b4081c0c00c1c280f205031031814481302c1074014070801040c5141c2e180e00f00d0302d070045521f10742400120307114080220b06080034200144071f4480d00c0da17401640f40190150b0002200c07003459400c07504260007650700400134001480744651100e900802038400b00f070328032000c10000024400c0c00310068800c10301010b40c41442c0c614500b07a955010313072110096a0000f80d0410100c401d5100540880e0f81c1107801070301040c82a0003c128030700d8039800c50dc3c2e020380c1280340423034041d54a603500d40c0b0b41c150564048000c9018900c0100786820300c0da001e1603001c0c240030860 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 176688705 1250 176687455 176687471
    0x4150603050c0f01020f030304030806150c0c0904050f0708010209090f01061b0602160f0b07030e07031415040c0314030901200f0303011508010b0a020729041215 71
    0x81c507a11401004454000d43c14040c088401e68000c0c41101102129032085c4c0c0d54070720703040c64001c10742001144d000d8802c440c004220100e030380d280c00541c0e071182c40b60002410b4281c0c842c400c00081c3d0b04000c00480e468882d180240d00b4501c8140301c030000034407241c1c002580385c0d94500f04011100400a10030b2030400032402c01001445d50101c4800d4030401c2d04010092110824101f410103407240da0384200d40c0d611003244000401c448003000c1c0800c10301030303000d2190584034108101c003511183c000700ca074554000f520a002081000d94900481c0d000c110848a03030308489a014547e100080b102618440b841c94010002e101c4680341f600320300b011013400f65103814203110000c0c2807900300c680401c600d0b8610100c54490480c4c10400da0258001c89802c5070b48035a5981c035017040050f22440d200c0009284040000b561040380400c2e2016841b00f900984881814007101038a40c5040c01e440440c0091401d2100381c011240000900c0585403520b04000402e409080019280303041c91203030b02020381740040d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 176689955 1250 176688705 176688713
    0x409050c01120605040203040c1e080c06091306090b030d0207050a090f09140d170402361f06170a020309010902150904061a2d0a030504150603 63
    0x94003410007401c04072107101420341d0302c800804a80e0480fa4000d44008240802d100030f01006104441d0703c140c0d515100608060750804491070741c400c1d40c110303510072691f50342c0ba4a40280901000c0501801c1e000c00b100700d014102059036502d61080115a644d444603a0302828140080080072116000a0070105e240c60040b80814840303210b14501da07591680c840c850700301980c00100c1001d40000c65001109042d01d40303039454071050f10080c400f08840e81c4070003500398035481f030b01440b580e00101546410b81c925410345040300d414112242d11100c0300194a03500a840509103030080000141c800c0085850040200130380c1c001c1d0b000b980511820303041c01c0440c6030400c0d040c0c60b03000301c1c20701d009a2252030380b02c0360b207001d00000320000354000491400e070108140e04101800c41508112000c0c0003250b915444235070f14883d01c800d00c64506508028400c0046086100f0440300c4e12300710a0400821090801c036502604441c2c0e9200000e501c560500c428801c174600300c101c1076440c0b08820030000b0303d5039036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 176691205 1250 176689955 176689963
    0x50d0b011505090907440402210c0118151103041a09030d08040302060a0513080a0c0b150a06030f18080a020f16090504020310110414040905 62
    0x31a1000320071550860054661190741664050700300a019020a8100404003030315090400350410540c0303506036048910104003150031103c08110b01400c10b14040ca0030400d43c040f80340148140d81100304c9000f1a4101811250884014800700c80035000d161002c130001050b0440052074800428095a404c1c8051304100441c040e144288e400c0007480c20703030245891411805180e11210103040880380780c80311641410010b1180c4a4101c0541d01115032440c001e4510b800d041d1030280040c0d1040000903c14001944680d42014a403c208501036000d6a10610644c1c00b500b044400107810200800400810b40401508642d840040320314042d8190085489089648030380070825840381400005031804d1b90210301b8130080110034207030041d59801e003040301d0f1b80160802030043c8a18029580c0b108408107908401b84130030340e10701c400586440d90b114045c10703014105030381c140122101c4070150000d0b88034024400ca2088501929585040040c4200c0d10b42840c070a8016070505060340300042000c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 176692455 1250 176691205 176691209
    0x2120703050a2901170703060c02031b1b130b030102030a020c1504050d050f090307060507030215070903080f090d03090807060509090412090b07030e04110715020c0c0402040306090b01050d0b01 85
    0xc030303165400600d07210601b4034254403940003030b03c03082c0f402c11400501b030390110040c5104056240403a40101c3c1c0f03051010341e41c0c10503900e1849180c449200780c400c14a445d07100790106007200440410400309000002e802c980c0180c8004000b2903001441a060400901c000c04140c8241c001c0d09030546010386a20742c80b20060707881401003040001e058513005680600382d65a426000d000c5408c07140c1c49440c040d0080d449020180d025100c3c1658084030400781210b005d210311b8003981c2e0112010b1866035052040e4000e040303195040c000a1064038079503107d1880f55411503000b86c1d251404c452510540324102855508004100f11003040003180c2a12a0703801700381c0107580b090801e904014480000c0f10943c040790443d00c0100f4000074018285640440000c0c01c491084030200096516611b211b8154825440020900b581d61003180190b0701841e800b80c10a0b074000d5090341c0300d0300000c8000500700c1e8480c0c4c00894040b90b0f80c143d140140f041c85402980901815106001505d546448070b43d1004414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 176693705 1250 176692455 176692469
    0x3010504230106030c172a0f12062a09030a0b0901090506010b070506010f05010e09100504020c160803030601090e090c1e01020105060105090d0f02120703050a2901 72
    0x40010241c00182544040011500201c0103c00380d92200c404141403c0204d07038804203442101c00e0301d00702c034044060f501c0444200300d48124030b01100c0d80c144400e918010818551044d440060100d8190081c403485104c4c40c20301903041040b04182c3c01c820200c405485120024000c2444014565240012410b01e8140c02c910840841d41c0c450610602400c81044010234031b010350400080e42065010250801c1c510440a07101c082c0c0c0c940d03680380d940240724807a0703500042c540c3e850309189061000e0065000203011000d004c60a4031000441d090780e10480d8200c03140d90081400103044030302d110f4440082d0840c180618a14200040003c11000c080d0044d40000c00d00d11012030110441041912000c40c8003825074144412412442d941a085040c8294055400d010001d04c40e584030320100c89020710020f20200c5800c0d82600c0f8480382c2c1c660090100d800030309510368241045401c01144e002988a00c00400030030000e49884080c2010084041d248588406002074000d40c50200d40c038151105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 176694955 1250 176693705 176693753
    0x20105010b04031b0807030f0c0e1314010f0501120203070b040b040e090f0a080414010f09061107030c03050109020316030b060105070f0b0901061401020a11010302031306020313020a0503010504 85
    0x40713448910b41c400075540c084100d5216680b40041000f4442c035881c131010b8040d000515101d070781d0f5882c0d4402408111903000e02803c0405140001400350820350040c51144c1000040301d0520050b002d04076042a00842000c000b181d0740c2e10114a0200600000307030044200c0b8a00b000d1034416103000c81d010b40d0040c042019140f40009092800c2049040002c002c0002119a004074506107011f050f0320500072141a0b00356024903050039402204211007a24107640c0d9884400d1502e282201e2103580e900260800f80141c101c000003107809042c2c02400b46001c2e00000541400030b104040c500f44000c0701800820a40c7d00080020074a01502c0c03907400442828507070b682d040c603403511805030b0400d00002004034080f502402889101503002006580c0010002c0000000500c01641e58030300c00f680003403031960b109014608551007a0099500302d01c816101907099040fa0750341c48181d8004858070340c02030200d402d500e410f618069010200412091b002005207040507102c20700a601050515110b20309 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 176696205 1250 176694955 176694983
    0x30207030203160b010906050102010b10050a110304092a0c0f02040b040203090106140103140a0c11030301091e020a050a230c0604020306060117070e04060906150f020105010b0403 79
    0x2009100b03e03400e600b601c540390441400c903442c050040746420302407481c4040c94a080420154014410340002c82c00050416040c2d0200030805c80e1194482007400040103140c25901003101c2040000c0e1000d49101e10005c200014202000040401c1c8002d085002c183c3c0201c0110005402100071540c0341e42003000001240b006002042c054180d610352941c200d031002040002040e010340c0003105070703008049821035030b101c58401101502c48a007018040b0090a9012441019050740800e03504c58450520501c0c0e0351855840d5411504242d12a00034140c030b840c82d115003400c0c003a8040601011900c000c5081506966008006004030b95584040c041240c440d03801d1303c000300c800036010049a1204554800218022513140c90080da4224028455240411150b6001310101d00d08040729290000381036694007070846004141d05036850308a80c0d120004581c9030a40e004100142c14480d1180c51150742000300144401600800f0340e046914180040c000700516800b00c034110b9030421300c2608482 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 176697455 1250 176696205 176696207
    0x90b070303111b011a03070612090507030b1311090f1611030d020405211f18060e150f13080f03010f03020a0906050102030f0d0902040c0816110d03020703 68
    0x4400c003c516200d000070681c448441043c150000a0100c2d900c43c083d504c0315040d5400d040c1d60300c2c25809403401041007101c03480c1440701541c4c8a0203190340500c3c100e40c1e00680d02e48410313038509800e51310300540c0820405014184500030081141810042d10008994505010380002c0c0303034030182c0f003400300b44000e1485002c1c8512540c1070310800002c0405903039541c0301d036540305c4002358810311070b250260ad298200a0000e04640ca585a1800f80030006081c0940309012103074400c1e05000c6803060400c2d80d5041c2a00f03440b02c410449150148103481c0010404640d052991038810500802c1036503d5000c010030100242100805070460941229224001194600504503000b4508031301070511380480000b82c0b1107a54890308040301d000342e41107450b150b225142b00f8207841c0c60b4010140564030811802c5900c24034000100341105220400080d0104d940e80003c06450441c07200350005a00c9009102120f06c44482410355041c060802811001c000f501d0141c80f0324080c03560350141507010851708241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 176698705 1250 176697455 176697457
    0x103050a090b0c042105100506060f040806060f09100611030702060705102703050904020c1b040e0106060215042406030303110f03180c060a0c020907090b07030311 72
    0x81d941c00109440503190880d01c4203400d400901c20302c40b070b903000709284a9500e40328504070b04506800802802851001c02000406030101410081d0444010403901c1640700d40803020388007502c0c015000d8102428081c0c1008030300e44d010b0303000b103105100d280140011100880f20b440b0441c3c007241400c1c0a41c03040e13249058210b004004000e5004140050340380d08114000c01c00f00d00240b1402010004d849289003402e0740070030280a004201c1e0004c3c0303203400c0428000c00150244500c000e10140c039004450003110304003100b01200100d61203c1d1600f0b10394924040c05132504150414000300085881d109000750350300300c425000d00d2954114800700d014044103016035000300c80f012582c201c80b1800c0c0c0b00321100070890341c8000e400280c03034501044071705c0303d40c00b044030b40310b00344202c010b0304644a031010940b024480e611220f140307104042540c0003503110300c40a86116905600c4190704100c00e8018043c0501c4010b080c80e00700b1500300340c1400a0810b00080d14440d83e05444e002542e10000c0b85003c540e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 176699955 1250 176698705 176698721
    0xb0901211110020609010608070302090a0e16080606040f0e0a08160507080601030314030123010e03010e0c01080c0705071503060503071511010b090a0e032724090103050a 75
    0x2e51a0700c1c0c040100ca03000510b4034040c20703403a0000c07c1810b5407410019180d0003107000c000c0d4803024540106550040b241c01c00c2c0b0040c0034180a40f0030003e512224080b80c800c1c02d0f4003540c41a08a042003000d1840c2c40c0c401c07100405141e00080c40a580c042c50030a0300c604016074020312050010943c90300c0b98240345400302080d640324040310402074845291690b258004d1204a00260342211040f00450a20040d64100c07200c000c0d41c560018011170000291842060005040054081400106030b80900414060012890141028031500000100303440350051008101a000700540030005d07200007841c800710b41c1001b00785440070f5180c0340c0c224003a00980d44110380c103109050740400c840728030034170000400896494441008140074881030036583c540164903800b0111400081444c912a04500001c141000550345440400d2400f040710742d04d14120b000e02612a407450240c1030130140d4000580300c1c25010040900345401c203040015114604a45041540701e201240c60400c1d43d40008034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 176701205 1250 176699955 176699959
    0x204050d050601030b091207030e03030721110f070e0601140703091805070212090109030501020f031b180d0f060e0c09010512150c040810020a030b09012111 69
    0x14500310038200a5038500c03003800300391009021000840c0300c0000000300100c40c8000c2001c010705141642d1820341b0303240c80503680c09802d4001000710030009a403003138100c940c5402c0307e03a9401d14201c0e00e03000107142904407402104160702810051a0341e400000c0c21300d0841d242c50b004000d46e642c2e0100100c41c40c8110b10b000303215007440800c160b41019001803044050b51a4004c1818560070520185820344800f40c1c0c618000d41c01c00408811078801c040001d000203c4c1c1814490b542c0c503641e030354140c00c981c40945001c4c041c1e0808014000690f0360700c07652841c012a40c00c6894105070325044047c00c112520781d80306d8400d10f0200d02c00f000f00444469910400390300504108210340c0030880b41d0303446207404a0140d10402004001140d039240020038655011034000050425900c80040c40240c2000604540100f001c240310006444108001801c04440b04890141e00c2d60b6210f14081e0a4401080a0394480c10045006100340301034142005c102c004513407c4450142e909090064801101c3c900b115 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 176702455 1250 176701205 176701219
    0x30114030a0804060201050a11090907080702032502130207050d05090a09051303090503062206021905040830070c05060a03090528020108220311010b010c11010c06020405 75
    0x61300c98040d4041485440d1840081c000b03214a0915410944614100c0550106010000c60070a03849801c106a1000950040741d240c0180046066640503425240300c4071038209504c0c0a04500388410404070580030308609500307120055035500d07229a044c201d00420407102003a0008155104403a010042480760020800f80c00c2600407000e2481280304140c0100d09001000076050a000440521a02441d01066029501b000380005d01745460181694455001d10004440c11030540c10407030146002c2e12625995440e04422600f80010aa4050741002071104003014030ba4006204002d00e90402a480d603480000303191040182c504d5411644c0c02c418007103405115540c2550115400a00a034220749032150142c2d03081500008240040601e81c40046000b4010350080020580050030b980120600481c08a200d130302034000034005400042444100c407540810030b02c82d0107045e450a19100308075201548403004213005012403903041001d82d0382607805100c0f06506540c05014001c14038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 176703705 1250 176702455 176702459
    0xf090d031b030f030b010c0309060f0c02030115080d0c0b130204021c0203071107050a090b211b010f090303080919110109060503012115021603140f030114030a0804 72
    0x808014110343c00802080c50481010283e40c00380e80c42c2d11406a141c0d8075000d0711410640c00300c44c07480b00300e0204410311076002c200000607a0300780a140d10010301b50751125101071929406a1a1081c0448202c0c00c0c8031030a540b0f2004218417264080d1b2004d24142e65460000c01807020400922660b00c04c086548068640517416062a40043d030280c1010b540742c0b0314120456049a0306c07441c4074441e540c0d022080c00c404100d141001e03080307103080f000001c00080c582f6500c04900b03880c6a240000350481038002120082c08042c00d03190104c0841000c0ca0701e481c07041801940900040d100703010140a1183e503a0010300b051804220700c0901220000d08401a0652450700b080a1411300140c1d1303000c01e80c0d407400480c806228405a034120303045404100d03010325001d04441c941c2c6060703000a0b15031003016030408001d02c8441c0000c25a00c07001500c492a0007606082c0240215080e0b0004443c1100401c15800d0764518901582d0568000100882d10100040c00191805c00d10201c0140781d48808140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 176704955 1250 176703705 176703707
    0x70b090d120f11011a04050a0605060307050a120209010c02091008010905070305070608191509091b27050901060e04030908010e0307020d1209051201020a02010b060f090d031b03 78
    0x2004801241d541c640c801d8540800400c0b6003a45c00c141030140c1d200341c01d440355042d075140a4120b11b030003000b940c0d00003030760700e450b0004a072842d401100e16001041c400141c003413000340d102d0340f4071030540c900b44000c50412240d000007e1414405031006482003a030300001c44c000c00031600015000303000e6503000b0440c1d4111441d03c0e5417644424401915140544000021014000d86a142c821116080e81c1402d15000f250503500a141500100900000491700030440402e00d00c580120107000e9583d14204070003d11000002a465400207500008507031000d142864070310240d040941860903000c0343d5940d500c0e02c0b0364010030782d5a0202c00600c3d00d400a00083c95002410741090343c82403002440740700e40d4655600d0b5203101d5500000d420442026142000c2101041d100b4a03211152510350a96a42c0704001007440305211404401a5800940ca40140781c091086602c003460030360708141800005080c1e907050340981341e240340c06000d08400c0d01c2c04141c81803001103140c12503841080c1e0f80c0406410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 176706205 1250 176704955 176704967
    0x50103051e091e06100e0a020403080a0306051002010b0102120d09020607031709010507020307021509031e011401030c0b0f0d02030f07081509190f1107030807050c070b090d12 77
    0x241d24401e10103000b142410729140800c00034414040450080d04072464016045030141d0000c0c0247d011507824080400017030f9031200101107a003041c0c0e8010a0490409040103170125001000b10296032500c180214680d0300461541c46050b540d00c0c070b07140c4a00e0302d41c0f40709025000455000354410800105182010780121100d00013000910103000c0a5139150321003400c03100161649400340c2e0052283d40010700d01064444902c080000d06c05080000c11400300307190003440c03140038010719080740d943d8a45100074403807442014000f04070304015501d1916001001e8416000c3c406452400113655031003c0c2c0c1c06e400311f400c2600c03040c10440d540d148c03044029854090a451341c03000680c41001059a8600245009001600040c10300140c2d0b1204820361b00c95013040740d8200401c980302c40c40c0c0d2030018014440ea14a04a015280b00d6071040c06140042c01e03050020559400c0c400184491940204000b40c0e40302901c0c5400e002641d0348200c6400124070000a58004101090b01d0385c4100e01c040e0301c17035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 176707455 1250 176706205 176706223
    0x30405010c091205030706050403090302090f09010e0706050d020c0a120e030105060901210c0803040305071802030c041806030b09010905060601050309030a030915051f06020a0804050103051e09 85
    0x26a030260080e482d80302100510072480d0003e8045d40c402c0c454000810302e44d521403900316101c0d040480ca01c6640c0d5012488030032007180c62204030421002004031030350083c043d0a00c03094403603010f003410310308260018119020b5640d400f40031650104100825100070440440f0403908281000140b11005500802441501711124000e5080078003103460b5040544105058801101d201070b003800e8080390906288260903410b54024520b02d10010307000c101800240091805140581100743c10207915004400960300340043c4140b0400402840c2101c840a80e07081d16819005403200d1030113600d550000d0000c0c0e810240c000c0c19101c050040010341544105080b92150054414941e6600010740310740c0012241c900294008110120105220358070030030303036544541c42400316440000d208808454044800300e2900c0c0c02422451903c02a00c07410000170101440186846002e030b95401d0400d00442c0308550526480e0720200d8900e02d90700805041d034410b4a800c0080900d00580e01c5644c8840319 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 176708705 1250 176707455 176707457
    0x30e101d0d06110721091215110c010b030601080703080706110a0e130603020f060a050408010f0c02210a110c1207090b04020f03040f14030703090f08160608061203030405010c 77
    0x12000031105c03507070001204180b142e0301e8440c2e5034a0303072403d84000d40007000d0010480b49540000036030410b040f06489205940310307240c0103054850340c03042111401c607143d0800f194031a6000da07004010381d410000b64101035987c4110920b40381d285074600140a003042080348045a8000b051050140380d1240078944604c508580382c0b541100c511062504039484c90201079048400c450f400100303414400000e0011a006252942c0741c2075480300b445084891140000f07201d69100c2c44038035241c640c10018005508046007000404880d18448800c661182e243e50800344507078030480c03000c02c220901c9500c0018901401d113124214400803d01d0322464035000d4007642c13034681038081003542024804d036020318081031103083c42c540b40c07900c0e00c1603c002d0081003216040b0440c192607024070b0062000d020240d05c00e80f0356420480c03c0c12040e84c0802983d821201050303020301d05240000a90019480455a15041c0600540c44040c041004440c540b00e400c0014400007082c482007050552061001d0746803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 176709955 1250 176708705 176708723
    0x408010c0e042316020c0406031b08073f050f06012702090a0506040906060e0906030c01030b01020c060703090f0605090d0303050604020d050112030e101d0d061107 72
    0x14000b5aa0303941000e443c000d81001070040c00060000e20001d0190310707006004d004842008903c2c0002906554854008a0340d078034a5500c10700802d8a0b43c1c0b90300c0e000c0d0062501070082c003420020240100d0b56141c2500c2170309003400d003080700c00b00d802407600d40340c0c2188850154132072003850400c26550003407290700e00c0315845034100001d40e05400200d81e40c4046040409611351501414594001c1c4d0011041d06901250384030000500d9590f0400800003440207000125003c0e207010005002c0b1800c4000750b0b80a02602400c00100c0d5402150002c0d08040900300051102102d50040f4500030140a80035041140000e40300c06064000310050112001200f910091a44034441110716018000d0313890381200440b002e4400103070017a04440d50004000d0001814454510044400d5400030381c4890551100308500301c0900d58000c1c402c4414840135906081c03440c0c0340d401c4c01003d40c45410100d80120145e0801080c041d43c420003103841c00c58002105101c0014007400380c0810342d0000b1400c940d1054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 176711205 1250 176709955 176709971
    0xf0506070f030b01212d0b0103020403020f2119050712050d140c010c0c0203061e060d0f050a060b0108070c0804051002240a0b031504110102030408010c0e04 69
    0x4072074001e00003c220181d446022043d0302c008070641204075820136029480d04c4a4444040718070185400c02c54006801c081c03a13001000f040d10300b08a80e000800c03203040600411050001d40c0743c901190920440c29540d85c102425814040d45294041e00210b4072140a0820b822840143c0e000e03911040a02440036240281e54030310301107113a0b170160a170040483d00034440f203042c040d00418210011450701c0407010314181e48141901c7c211140038a104003c6000c4115450035070074104400750f0f2020f07044001150303007401030b4104a900e0b240203000d01c0c802c90080224108200c00c1d001c02e581481e07800b0080780d0429040b0b00e032000180048845503800540b030040010201407042060401064021144a10781030900d4148140040074481d00015440b4010900b41011403044012540c44800c0c002c001181c06c00054050940d0070146005100340e1110071008484080c0d0541c490f08a5840704440100042100060341140100d03440000d0652070b200b45040c049402100c1409440d81c00c84040250139 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 176712455 1250 176711205 176711207
    0x901170c130504091a040212070305060a06080a03020a060209030a150603050d0c0803150a0b0c060f061005040b1e030906010503100c1b060213080715050c0a0308060d0f0506070f 78
    0x644c0c1c0c10809000c5000e02402d040b4502040d02c54a6000380c009460302000010500c4240d25010007a03101316210340c80f4604026900e0140c0c0320349800307005400050000c072105902c00a5032080c0706000035042030380c00500c004040d030701002003030541c981c482c000c8000d46144000300c0d0001c01d81c501c800e65150080e00602c1003c035102c1d0402c1000e0b503a111075000e0542e221413221194170071241243c983c001d000d803c404102d0500140c00340415442140c010700c52803078000300e04400b82c1c1010703005c035000702d141000010002d034015090b601030b50304042045840d030485080d0748054000003d540d00d00304000005100d401c00b40803803454182e60080c0d048412042200041d0b0044500040414000507520100114000648a40c10851a0107450003505201c446962828000c0303582e8840d1209602100d0100588943e818010040b143c2c541003190900901c214860f4070b80e0703040c4c00b0050401c00c107000042c45075501d150305ca5404a40041d14200c0c010441c1c130f0440d60f20981600d509003c100d80360030503c526 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 176713705 1250 176712455 176712461
    0x201021806040b031303050f07060b040e03040b070809040b1903051213060c020d02090a0c0206011505040509130c030605150316091a040c080615030601020c060901170c130504 77
    0x8a60140c80f062540d90f490301800d0390120401000c0302041010002080d46154400c041c0aa182c0103d800003000007684007040304451100c400c01d40b0507082030000f002100d030418250380d001500041c010b079480b18a080000d0080480841680c1d010039030b800341040d028004080c02c8196481401100e0002800c0c56052115001d5000c954444848944040c08054070403540b49080e2032010b86001d6800c2d41c02d42c0040d840a10407110382945a81c4d44000c240b4480d8100545401018041403205440f42d6802c0020800d20450284a008c5c2e000c034808142da00803042038070042c49803c6440f4841e400d440f403418170701800041e0b95803004100d030010403e205103804201014180454070440d800313a03151410180240c1076080740802000b0b4006081e007481d4403180105260721845a865440c2c82c40d101c410450881d580d180088405031041c02000f101d642c0000d40301c004100b08660803900d403201900102c2e031b11110400000841000c0b03109001c007a1400b8000703030071343c202065400707140c45031900244421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 176714955 1250 176713705 176713709
    0x5060a0b06070609030c0b0a02090102120304020a03030c0510051608010512060402220f091a070e01050714031207020d020c060f07050115080309131e0c030f0606020102180604 77
    0x1c00349003045048005029540288051441313820401c03c10342580e2240014000200d0718100c0050f00010003031407035070b070501024282140c81a64903085080c05d8021400281a82c00020144200c2c1075815080c04410010404044000ba81c06c1c0310314503101d68101e01c50000202c102011030b200f140046058070382105003805440909004000740e503180e408001c0c2c4a80201d0860741790703170364185818601c030807075020307520009641e25004146440640f0740402103c0001c00004c0091041c0347c1071250761540b11240e82e500c0c5909281140e2036502c00c5c10003c5c00c07007c824561201900c030000702100201034001c2171622a600c1c1e41c0076a89400300700c0c90140e1700e0703a00c010400f1b0380c8200c0c00c101404e003065554020740115806000005000d10303a05070240d841810f207401502c80d0707034404504d05503186060990000e4005000f5000d100720444d814803100c890202404d00c00031151201c0d400e242040c4298000c0c1020b0140d10002d0064560f40c1d1006030007944140542c0490404040031700d000c2d0f003000021101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 176716205 1250 176714955 176714959
    0x10306060c0209072307030306080c1f0e030c0618010e0a260c03072318220b0106050a120e1f0f0218090a090201080a02160506040602030405060a0b 65
    0x140b10b903200c0300100d504200e451013501d00305080c9414022400d00b44801b521030039120b07440004d4513034100b003a4a450300c01800b0403d40701c0c400a1110071101c1a1500fa580f4013003030389041c103c1c104030400b00004d00301200d03c407003a40c1181001c60200400a0007000360100080c003a210010b41000d1501403001d51106405107903460b041c02c0052560280014000c10f40c094808800d40e00c0c1c143c4202c000900300310300d0390320039603110391031010804580c500500080c0416030121102044c04012580540038100010f002941042e16610301d24250300c41005c2800506038042d907410665a1101806415070f0401410800002c14100c400c00c0d903101d0b607103e6446070306561401400c1c51001d880603251a140365181a0714075680700d83d41c102c5184054006400942200500011708000d410b0921100c034000a100c8107000781081d40d11000750740c0000105d5009916804c015a40d00402840c883c1284441c1d84e00800c2c605c520700801051100715409940a01d01c1403080e10341c0c03600c03807041140a888807115066 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 176717455 1250 176716205 176716219
    0x20030402040c08160e0109090f0509060c04031a070e03060f0702010c11061b0c07080307060b040b1e0d0f0f0507050108040c0501201b0405130804092007030509010306060c02 76
    0x111240c044d58010b05e80e040305260150405071603200705020b4440c0d020302040d500d0344030018404060303070910502d588111207030440c0c0e050520310388412100c01d07200341d0741c00c5404056001007504035200e42d192125003a000380886100c0d00b4005456042c254040310940c00552a10a002139030612401c4a591350700030722030003000280c07104044810300c01244034107828801e0041028800490003400b5403001059900055034440d940781c2050303000e80e008084940e00c030350310b022241185590383c150848545174030300c1403401b422880e00340407450341c1078221000b61208203c10544003c1020401605415a2007002a610690b580f10300641e604581030b14020f104032000501400594800e244900b041c22403081d03a21488d02100c05102e0918081c0303070b0381c2160000e4044540e0000d04180c001e42d40c000411800d0030042c1c030b81c10384514046029032b008010803d600e4a2149041134003100205c961007030880760f49507a590007450f01401c5544410115800309081160016800b4040e48000017a107401074209 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 176718705 1250 176717455 176717491
    0xc011215050f0301240e06010305040302031206150f1b0c01091206180f06060608012d0b040e04060612150c0c080c03130807030f0305030403020120030402040c08 71
    0x20000c02c00002200f070301036598020350301c03512003212450070429880c4141c8404113420401d00218042d00185014181420301e0180000658004100c68001510000c034891b140c646034001040301c55401849410240b000c0340c2c4400520406004001401c010300c0b070b100d100600740100c3d40e155010808000d000c0b4407503100402c9a00d4888242c1c40445100302800140c0e4200001e0780800c5203200d85003983c00b0f40070f811240c810008640f041402800349820950781942c0740c01c08602e0040c40030a0003a41d400c0c4403207e00500700c2c8900c0391000190001036074a6841c0ca03146d00c1da10010500c11075040c2c5840f030078000001802c80304048103480c0f140d000701c0c860026410414090018080f4480c42100704514041c2885c0810501d0016141c0880c42c80040c55491902071a081119240c07500492030580200e20100001031000407607501c6c00b98035090490f181d80d00c90801364014032010751400482032403c6103010601440300001d41c410f5100700c604020f80329020800b152841412074405070000c81000071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 176719955 1250 176718705 176718709
    0x50a150e04140604030c1e02090105130e060c031009090c0b180411360909031201030807060c033614031306050a050712050c030c0c01121505 62
    0x200ca0351050050b1100d071401556070310700d64a80301080f5015400036422544100c204a9402081d0010f6403041e1100b440c80c4c2900c0d000074900010602c0f0f210321890800156000c907018640040e00c40401c03810913a005843c0035150044036500072101e00351100b02415000c6000c4100303120b40c10381070b500b000c6066246820001da110039580422102030005004ca200031055650f60300031244060f030a01c0e41651555240b5002200c502c1c40100d620344038240b002900200140342144032000c5901c11103c1103d540c40d40144942144550307050078400703010880c008401d10041c80020200d03180b00b0401005072400001c0100d00700c03018109003070041c2682095000798452410313003d240307228600900060307070110349e80c40d01004e180403484410290070201d001c21030003442f0314600380148040d0401900d08a1103590081540c4102e88000703140b04217101d00a018144034600b83c07010488a031040382d59461211024540c1c822070560558009400201209450780f40741c00307036407803880f52401400304050901007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 176721205 1250 176719955 176719979
    0xc0d11060a03020c10060e090307050a0f0f0212071a04050102030a0e0307051e13050105100305040309030827220b060f0418060b030420011404090b0301050a15 70
    0x7010820035400b44010b0307650b04001e100c039040c69440c924002900324035090b80b4101d00c6130010300c1d1003269007080c40401c010400205103410b1065002c00802e00c23041d405d1416029185890038007075048000b056030b14003900000600c890950b51003e65840c400e00141c1d40310201407084c0c0c0101130060f081408480d100502842c103421218000070b0036a0170035a00ca201007a10b03940e910b43c3c4102e60303010808000b4018180002c0300d58806594507414041c643c1071002040381a00140743c807404140e80c540000c0c0505d03128140c000095603022062594031011140d041121489544464101c02c000d00140ea1079483e000082c04940c401070202c000101c400c00d90840d00801507100314039004142000780c0300d080d0804000400150a8110703085407008072203000304040720400d800454001c402041403102250144041409420300510740d60b50100401c80120307014160000c51680c801c0c808107012a030000d190300700c2c00700c407003044d4001c1103259200c00d07007135040d100d5080030007070040c80c20a824804104219 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 176722455 1250 176721205 176721217
    0xe0d0e0f03150901020702010e040504020607020d060605030312060906010e0a06110c0424080705010c0803090a1401360b1308040803031e040c090c0e210c0d1106 71
    0x2000e49078440680d004030301542c8001c4500440c075940c0040c0c2c0e40219a0040301340321202d102620100070701d10b030541c040380151086101c0a4482c6286056000030042d0700d40289003d0980a4143d9440b11401c4c08140c111880542c1c0281c03060101c107000941551142004031420b150091141c64094500103003620300405d001c080821a000340e04030307405941c03682c0c000c0c008687c401e04906040450ba42c901c49828030032580020455812004003080b96030380c0300603401c4070b940d001804140d407604c581490914114803070784010000054608080554070701980301190440c280c000d070070307040c0c08181d5140074240020f85101a40084440d85640404c2c81d98000d1540203054102036450003106440f0040c0700d40142d03000c0c1445500000401295028030901008145680d04845044e8100341c2d44028214100d806042e2304107580f08001c5491901c506d0404c03100f0440505200f00c0b005a451020704c2440500071141218032a41700c0d4842d481c2003c8035503921407500405144e048450704410001554091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 176723705 1250 176722455 176722459
    0x60906010f12060b03040b0c0a0903030e04022506110703020a290f070e27040302010617010509060c070804090506030c21060c0901053405030d0e0d0e0f 67
    0x100715202044942441410013030002e110007642c80e8940380c0740c00c8403025001440b0084094040c4240140d07142c000442c030701501e905090041d203000400000c5070087c0038441d840c500010018101034859071040302c080e5001809803206004001802c5200c002920404a0080060340006c0c2c2040200314140345548d191743c0041d9078818080415100c804d0300c4c0009440a103d0948031006205030380781c0010031650420029104e00070040a4841740c542d0841e1140449602c0741460380000c1c04040c400e500110241c040d4803075130503140b650169a180209070440380509280305800104540b4030011050b109000d51010780e4900d014248080352001e0306001d0142070b014031036980718450359940c1c0040c0032144022244081c00c4c40c41510b009520f007490142088918030300c00c001c0d550b07050742d00208035104004541e1902e001c0070481e03031080785d042c002c10102d401c03220100000c0b942003000c048014540c01c0700003c818007544c41c0c0303507043c203440c1e41c640709800000c06d0201045040c5820a103140101c0c0d6440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 176724955 1250 176723705 176723717
    0x603030a0507050304030c030b24010c02091017030a1812021005360f1e0a03080a0206070206011e170307050a0303062c01170307080c0a030306050603060906010f 71
    0x15031365940381f4105098204483c83c011090400c443c108e0086c3c0c2054010501c820814100020040041d1291608a8020b4000c4c2e04100018040295080705500106800c000f00080c0450001003c2e40f03c2d0051212007002500d581c28403d00c403151581608159200c009280441152079400c011526241c2010201440810f015004074004948d00040d003031803510640364540e400074030042d80b4440100d00780b01c0c413644031048083c0851721094104a03010601c40d00e00d0503542e40c0d50001464003001584001c0040340e002500c0101c1d20390115681c1d011740c54680883e402c990b2a01511080f4412101e203511070000360a0040010195510315010340c0d07040c003800d580c1f40007039984440741440e103031000540c042038549004100c0c85003040a01c0100c0303072052a0700754041402c9480d0340340102041c456542c20009200002030401d006000f10b406040d4030082c03050741c44105050840d2110f60440040e00400d1900000041d141441411139200381401041030341156910001940c1404104148000f04a5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 176726205 1250 176724955 176724959
    0x1e09031b070e071706060712031d030c0d020c0108090c010806010905060d0b100c0308061504120b06041104030f02010f09050a060809010c030b01020a080307120c0c03020111030603030a0507050304 86
    0x58510001401105143d69480c0c09100040407211913034009004240036400400594011514290600d00e00f0011440d021506070080130307105804080b04102c5030f045000004029500d0b1100080446803001550280d0715028495401566007420488030311a2907007140e1889092584101d00d140c1d40420141051085c081c1c07a51b0210781d040e008031221000141d55240c112205103840c10915000c515185030151f490342e00395400914000001d001940181c0380b10707a640c1c5a584050b0180d074050301c00515000358040345070a0004c83e581d020b44406000d1842d04003000e030400040d80484080d07035007281d11070050402a500442c0c0c03001da02d40d07480003040b05000002c51550b03110760131607006122680c0d45c20f009003080714045003101c07080d914100600d842c000359152680d8000c100d0002c1c0541101d480b17503d80c0e803812402c6d5411002510440c0c00c144c61300500f01811034000501c5040540298000c0191a03085400e40035a48002d80d0710a600d0380c010301106c11000c1c0b0940042419900c40d905481c00c250f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 176727455 1250 176726205 176726219
    0x6121103070c02040516170405070306110403030f0905010f121d01090203011a0d030c030e03030a080106021507051602060f0d090224030106030506010507050f061e09031b07 76
    0xd04140e541c64001004019244190710f001d00a05402c82d05010750300d481031605807401341454400d40310520006441038000b40900c02c0520000b0000e580281d000d0081c203c0320400b4100b82d034810b020417000709949464082c1c0540c841d0400405498040e1660700150030860b0058400404440c81d0700c007d207483d0b0a21000c0c281c594501010034800d8080003045100c0113104242c03e4681c800000c6a4280d80c54211081c141d6409031400344041d09400d281c13121511506040710840d81500506405201c006405101980d0240c00750341220b401740e00303840e40c6811884200050003401c0d01c003000005d13020b0001d290203150004400068600c0100390a1500c181e2541d054800d03000018481d210340d43e520212000d60810030941d0b414224030300070114a408989083c2845404107000705d41c20541d031100020807990195046641454002c011502c1000900800603900c44046403810740028171031001e40c2c0c42090141c4480c1c0503544200141d810300800011205100400c00e200310480e201c0d00100003500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 176728705 1250 176727455 176727457
    0x20d020d0b0a0606110309010305090322050a0510021c020a020d05070f0b04150c030c060f0509010b0105040305060129030907051516030c061b0201020903060a050c04061211 76
    0x3103841494000071914100c100314085a0342c82d40058180324040da400107000d007021084440c11402400e00140c0d549580e00303001d15601038245116910001d0401000c0b51000c00144141200c000300c86400036640c5800a02010b500070707080300340c0940d01804514185105090010700706c1e072018811141c5051180c0c00085100d031040704150383d15044584c0a0015030000300c5050050700032045820301d05072810700b94102a440c11401881003149010741201010322a8203081e005a42081080c0902d03901c2c242600001d0005840402d00d0358070f4141310160b03950050003034408072600000641448d031b29200c44c0c408062550b038a05010504215043d240c080e800320040d60060f800c403c02000306138104010f0241c00c40c8421040550351070140084101501418174440e20b0550614008540d01c20b2840c02d900603061201107800d1280d54001180b00c116030550181c104054210104c03009a2035404600d421590140e0b0710b1000624200030510180d80030f02c4210210040b03085000411215001c240941 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 176729955 1250 176728705 176728729
    0x803160e03150f0601020c130b0d0206040605030708071d061606050106020a0b010504091205090a030209090a02180402060906030c040503070303050301091505030c010c020103110307110d020105070c0f020d02 91
    0x4040460300500020b60343c000c0c1000e40c440c40a000414011039a030000400e4801c041d46c0d04040c0603121244c0d204c0640308c203d401c9600c4c07a40500035540322510307964040c2464004450b5200003c1780a4001001d0b1480f810f4021403c060040170f076000800c00c0340c1440110341c40160b0580e87d09203403c200ac0e0019174540b150600828403903000e091210440d1030200d0401d076060341b007684a282030034201c4005c54101400c14140507454180030395203491032004504c1c0840d8543c006588490000e080180b400030119030140f18610171070700b40340701c68a048a4422031450503207021307400c080144062500c81c10b2500045030440b400b041018207165484c2d000a1030014a904103d0000d0b6002c00100701c602d82900507562000c02c0c06003211101070400002c250b40d040303440103150411400d105e035841564025030080c18050000b584031130352490415005400145414242e40c1c4510801d52807000e02c601c10303c2114054116540d0309202c81e8510b440f907900c00380351f40341c090b070b0300c805a50030010040e035a003443c01d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 176731205 1250 176729955 176729983
    0x1110301030809090c1312021f030f0e19060209120a030c021f020d050d060b13060f0c03020c01080613410604020a0311040906050a060c0803160e03 65
    0x181d41d90070f007014880c6461018080496800060041c0c0a510000d410b60ba810384148183c3c040c0c82034003d0001500621561030f0001c03105113071803071402e6080c2e415000820308180c900b5042c080685502d800703a50342e28140719010b10207504440a0800594103400908000400a01001555486038109801c10a400390201c01158220310039100714205020206902805000c3c84031411610040185d11080c54121642c100b1800050504194515600c4000501244403825849544c024640c00840c00c803030081d900841c02c20048203105a20406044034402c0e8107501402d08003042100549000c40d01a2546901c5010f48404440c0005188120082d1203c9259809031000030360151102c00890180e240184034600001c0c1c01c14001e030b1541e46500f100003601d0060303898a41e030381c2c11801840c51179850701c5403101c0000e002a08a1441d0007010075a0421603000345d51325541c800a4881505d20360340101144801d10001d4490504400348810072045804d0140d440303040c0500003420000c80342e0300c00c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 176732455 1250 176731205 176731207
    0x1140915280c0b010b0f120a0f24081615140304080a0909110a0c0f02031f05011d010b09030c0a090f1803051204030926010c020a23011103010308 64
    0x80e0a00211440084c01421034559140c07510000c0b28454080d44103003045d000c416a840c0c00070130703030540e510380c003c64200305188010005049905d400d400d4068141440458500c6a0031010075692030201d0010242c00f50801a1890036141203050b503008424804840c0600c16151513902428480d43d00a500c00c5100304480c9a45922461004d4103803281c2d41c0000c0a40c9140c01091904000107508070f854450b2a13041c0081c0c060010320348001e403008143c0000303405002d00d480040c41d01c80e0701e10207801c807030350190340910542e03032076112801801c082603200740451908100100f007140703100002440d0781540074040d600d20b000b00801240405040f41d001000d59550b1700440b0904000510822004214059000d03580e24601d88004103030380100540f41044022120100701098025044200102425050000200f0080b64807159146801b58200c0c043d508041040d007503e0700c045038111a45602407001451100c402201042080e4501c0701240150b5030351040d03080c8d20b0704100141d80254401c40d001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 176733705 1250 176732455 176732477
    0x60305070210060608010b1c11041805040309060813060e070503190209010e100e1e0f040510050c040519050a0b0a05070209040f0204020304110114091528 68
    0x80c60705800d0b081030301400789852414018284d01041c045d044414000c003994a40480794040d40304008510031080341d40e407600703004000c068022005082240d11015070300654042c0d00c1150000e403042100d0081c0010381e1103009015180c05406101c1c1c002203c049450740b9030410780d07100c0c41202c42c5000441004c0e44a400b041203c5c1c034040009501409800b8a818030000150f030209545440600801181407000400a850329580c0c8c68504020032045d402c280c03c1d801c0c40c034a0030750100441020410802c00c1480001c02a8103ca0070b4180038036407000c004c1c115841020762030001810080c3c5017034403510041000180542c1c9044d80e40b103410f1190810740c2544d40c505420800120000e50100c161723483c0031300070305001d150854140da1526405840384100c95440e0305c0d0907018070b01d04501c021f601901c00300c240400d001c1c901c00e03a244d46203002c0e2294161000e490342908038a00a25080e280d0105110700901c020105c2d42c4060403181100b042900854101c0d0440c107549401c05400c0400011103041074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 176734955 1250 176733705 176733707
    0x702040f05041415060402030601020102070c090903080109020c0a03080a1b0210060806090a03030e03190509090105030712020d050106080319080609040c0e04020d02040519060e13170403020a06030507 88
    0x1070441c000412030003c4c000342002c81950324000714010003043c403a035408000110664000e404452132185d00c54403051030b207a01d078140030004001c401c0c0b065000580100000c142a8881d00c04c85521040ca200280300288083e5800c03120002e004040e00b5685840340991b4689405d4403d41e1a035a4102c2d030003401c0300b54030315010304045601692000d12154030100502030004c1020402072005609442c011420001c0800341924600c00d0f00e1510b03084c00300c98030f1038506241d8001d000d0100d03600b00300d62628550342ea400401d40d03240c1f013078010f003150703402503803c140c00626003500246021880380001043c655039850084d0300b10340004400d501100c1044c1525901c0c0d40e4400c9010707502c0002250000c159040946460b0306029050040708180e1201101180540d40e481e000c3c8200c80358011300074821454841045c950715039000c01708908440c10000c0104a00800300c0480d0b21400901040790104410303a1a4146800d40405a8010380e0008003c044003588031515842c02500131501d0118150400081c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 176736205 1250 176734955 176734973
    0x90d030c05030a030c021c0c12090e0a0504060e01092d05010507020c01260a2406090f06020c0607020402030601050706020705010209010f0c0302210f040e0108010531080702040f0504 80
    0x3c41e40060064004480510980203d000700620340c05ca2002d103000c52400a0590750ae0700c29404c04210062524100025129540c014034440c03403003048140040c0a444412034280c3d00420b0004180c10148a80804480d01982d88603100c02e40d01103a100c1c2503030060700c5031030848a00740c0300d440050300101071142895802400301d1100400f0fa451040c1c0000400c4d5540208000141011106e80d49480000f100c04118010310640c600d2004900d400880d903c0c00041c10034000c0d4400c82407110012500082c4040c004119140c4082015006a1078050303590300b004025440180154107010b801c2c07000b44040b55103803020748250783c81a400103a50f01440d01c00900784812080442080154a41000000030760202c1c00c00c5000d8105402084207064401d1861510f004030862481d2071500803d0014000c1501190035040340d0482c8000c1095444060340700b82c1e103205c1201c0c0c0301c0c84400d41000d4442e540240349104c0b4005030180304040e0812034603030700149c01c0d81d0310358400c039460726252000c1c0018400000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 176737455 1250 176736205 176736223
    0x20a0b0d14070c0b0601030e010e0717030a0e0f0105120406060e060603041208061f08150a05060f090103060b1204022b0215120405060108061605090d030c05030a030c02 74
    0xe40d900991800010083c458618410004e2042030140e010484d142d0103a00089180f4640d00000d12005031120b2181d903032030040d40b284441c4a0641d0403c420850004012240c502c8000c0d5101c00543c1d10720410311000d0b96020389500d04000040201d00703003403403070540402d0245118190209400749032808009039030202030702052151030308000348000640c0f28207189400e8446428002c6040d80e543c0d00090071568062910399081c2d0b052100c2c004000c0d4030046161056030341014151402c1141018005101114000d10f50008810031028a9401c480800b520000381c0c14907001c00d180d030311590341420a400095003443c4640a0b2000c0c00118a490003100d54407060354a805a101d440188100002c062814400390241e00788200e29107001c10309070700b01c91620150700c0003144070b41410301c4c0203691134800744180b00e80b130b00070003000c10005004413600c41e0350803a5035650641407603400d5082100344e041204044081c400303134468200000d281403003e040c079200386480014040c210b10001034100303807100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 176738705 1250 176737455 176737481
    0xe1e03040e0112020f0306070e010305090601030506010501080411130617060621011b020a02011d03070306020a030902031209030106120503070323030a050103021c121b020a0b0d 78
    0x6000030300400c10030194035411640300c000d142c0c554001d11300215100d548107402403a0113000301010410301c0340d00811384e041d880c2703000c2ea010000b80c0c0c0d0780308215844013802c3c00001c3c0640c01010040019611030004980c129000300c08103824480300000281052180503072200000c2e440f250101f048000318407000c0b00c1e40040c1f0000c0d045130f141490000e626080240c040780104031050351a03c2241d8025400803400e0146c4d040c20918003440454044d40d1880d0781e0078100e0005032441e5150180c4446c000c02c1c041d00794009030042c0012030942d61001e002c0c1d0042c800340e4041565844600c000359400304110201311003a01c801c0d41d03071004100e0506094070030a4200d9041c1231000e541000c00604000704407411a600740c6000b40034003840307003191866810388072015a00d0403000300511541c10b040c0e91100c0c0c1228800c4900c08041c05a802070404202c441f500054000c403d2620528050b40c052258400d40700244001c100c2d030303004103a0000348174652640140d24061804a1250b100505511a5064401d04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 176739955 1250 176738705 176738707
    0x6031a071b12050903060109020c01050108030703020607051e0703200d02120d0216050705030d031a042427020705030a1b0b0408031905150118090e1e03 67
    0x44842103100380303154480080010720b0407120451410302c02c41c1607035004080102039401550b0750b2580c41d0081e4001a0b03208079036520f000d000090084001044881d400c0e45a00600800c0e540c0388815a026000b42d0a40c14000751b8199000c20501e00034001040164400d446031201d00c0f8008401d004290344120b0f40300003a50126250320602c940005403a8040c03840700405958491401c0c6102002c4c0c0a0150182c07008035440708014100140415540203540b4103508030781c00c40c5032000048050300c95010440c10b0103c2d4511041485041c030b9041000000c2d42150f9402404107002c0c03425034070004560120001c900c41041d4450f0386400ca640c41c0410640c5268158108038050b25801d031244540c2c61400d0a01102035060012103c0700880d00280d5500300892540310714040c144988298000c5542e042d400c100c60b1027051300054988500c0340100040100b800d00e807000340300150343d0010910441400003a0a65001039010311500664510b140c008024200c6c02c000e1010592400350b4004a400c42500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 176741205 1250 176739955 176739977
    0xc0901080a02040e12070507060e15041e08120a02070b0a051b1c0903021903150207060908041502070911121f060e0f030f0a020f0109080106031a07 65
    0x1900084001c02650101e600091304114044020710300000004a0324a514011404000f070010116080c0c045074401e0322442d81403003540040010300c000310401041002c00a00c0103102d0780c0148a082e06100142d019440c41c99500c885405242c100c0745805090703170003000250ba8690740d9041c032181c0005c0142c1e80c440c5050590951002e8214041d94990a4100c1e90300c01b0030030500c1c14200300100d24213144456810f1200355a08000b84150703888d00003a030040c1c0c0f20034811007252800c00c1c41c810459400c00f0a096801782c10544031000b962203040b081c0d541c1c40c0c4075800c20000c140110001c000078640e449120007031801c1041d0190804c0d950764007000310b130352801d0f800f44520001740c4c2c111a8207881d50600d118055469452100e414280441c0600c490300c0c41c0600403401a41106054202c2542203d01aa81c038461400700b61345c0703d041c010143c1d100e07040548010b005040120140544c41014140300380441c1d01d5051060842d481135009949030005403c0000c0c44c80142c20b04142c01486600d844e00311a9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 176742455 1250 176741205 176741219
    0x110901091b03020c46030906050a270b0c0106060305071701060e01090e160306050a06140706060506030906011508090c09060427150203071d030102090904030206090c0901 75
    0x680324030381c50b0105003038840b00103078840c01d03441c0e000c11940368034080101101100d80904045c08282d810440205801d05d002203032080c050010744403520b41c95a0340c02050346001da175403408a02c0c075408011180c81c040b0781c08030311700c4203542c05003580035000b90000440c1c0389000c4d0003e095880c003600300e03814040908417840100741c1d4140001d042d6003242c185410850b2000004980710811030b80000d0051441c0014007002a00d040c0b50340b0341c80159545d09001c210744400c100032030f0070040d216000101d100c440040b005107000201805a40e80140b00000c0c3c00e65542000c50707181d61080f108964030750060001445000c1c003050fc80320800003d841c0100c0186003c0c80075558498415048901c034a25120015560f50307100d4200b40f40d980c040c0f4000b0100d010350340f4070100c012416502d040361044c100d400c0f0001340302554426248a01441d80e20110307042c100703080e610640d2200c4c0c918203406540811090b182c0362100c8041038010f80c070903030003881d240c070381888500d04000c07000c42c0360351140f1b4404d80100101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 176743705 1250 176742455 176742463
    0x70b0a0c0c060b0a0e04060203090705150d1e09030f02010c030203010b070b06040e0304260a031707110607050d0f1103010512030c06070c021206060904030309110901091b03020c 78
    0xa29440000010a18100000104c941c1d1081e4492440880310004003c108012a006140513034030000807549030a0700d0301700300214000d03230b1101449144802e0044911102032034201c0ea06600e07110b0076001900c0021410380c8103544d118007055000c603241c202c000100c130382d09104a28040c01103103021410b55041a2a40825200760078018007440481000b003242d0f5035443d400b0b01403074801c5004981d69255038030104240c04442922010b00440c5010300d40f140d02d880407440d400c0450341665842a01d140c0203520003484140503140c41c04105000c0d400103510740c003c20101e4040d00041e11081c1d00c4045154117403040e9410030480085142c04c120b50745070401002001c0d00d0548908523442507216150300d00c1c051a5020f0209140020b1003040309000c5c6042d00884c03101d441e14001d07564491f10303288448005a03610300580e40c4c0d540200305040010003107446a40100034845c894000c24018a01c3c440c00615508400c2e00180c0d007541da10800d6001085003020301528034040350800f5824085000d40072915 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 176744955 1250 176743705 176743727
    0x4140403090e0f1308030603152715070804030c050313180b0906090c0f13060f080f0f0c071b0501030b01030b0d021302040b1b07061b170c12070b0a0c 66
    0x3917081c0100c04079416907000d215908803503540040d218070780d141403e01c98494541250786500c1c640c2500c09400100900400e4039030750490221180b80c00781c1c584100440c2c5031340004009404011009016800089051005001140354045508819400c014203040880c4042000d4505145464806604e680b035800c64144d1004044030020f0262362440b003103412611a00c00707005d80300000003c01c241d00344003040210054a4050366030f500f01118200c020b03511003034190380003100d07801c4000016103420700300020302d5030104a2400550404400f42c0d101c0c040640e80a80000b4032015440d800c1c44556810303c00d04100743c600b40303420b0000d00c031514086524514482006409185042ea00300341008640c0c04440003402c1243d0b41c070b07036501d40146216056810702c0c90440190b000d45800010024400c1007400b43c2215180040c0d8410315240c2e41300c4154450f0140c285503c40c10030b10184a100005004903c048264066550740d00c950514114841c0302e0000e1814101914184500016581c84030038810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 176746205 1250 176744955 176744963
    0x20405070c0b0718080a0c0311120703060902010302090418050607030c050a030e03070803040804030b011a0406050a021606020a02040e0631050a0c05040e0f0303130204140403090e0f13 81
    0x2080b22262650394000381326801c44c00303139407003410440800c11a003450711100326801080950f03d000300440070005c06c0c043c1c201100015900051301800403850640c40400003500c141001407a0000400101d025502110b01c5d6208915820b080c40c0b0170f01c070080c00f14039441801445c081200c10743e1781c1c00140980c000c403810b4004059075602c1030840060104101e81c11160030000140c1c5038585031610501c00d0b4405c2c0802c641d180302a80c00028000b909821540541080714881800c0a04050085450740c02c8480c1240862140822940d4600072038088403001d40b6170355010b030038004454014082651190010148664400700030400c0098140c444520031140a0224103449128181d60011304403000743c4c058103034012444400200710007035107000101ca50643d001c0c4094000b06402680303410742400c114019800400004544044500000c01000c0c4010b1001a850b9013603448016105004ca8044000c9562000e00303106070340d180e4000741c3d40074401181c10111441c06000c030507804051600020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 176747455 1250 176746205 176746217
    0x31b0e010504080a050303100914161b05010e1912140705010e03130b070308040201180e0906060913050a02130f0e0109020406080c09010e0403020f0307030804020405070c0b07 77
    0x890560310410844000301851003c448202c0341d103060154581c0e0081d10400d81c0c84094181c005000c1059006103803904841041c5d035909940c80c40380400010341d103000d4204c100800284081e000d09505001011141d000382c0000586000600c0700520340303440d00350f440e2076140041c0310060016040c1010342c402064a490000c3c1086c1e84c1c2c0c84802c0c414010080010055402d014801318040c900201500701c1141542e040042503a48460a42c01842105d5003d000126140c0018025500036403010a81d00740c0041498081a603c0025114601081d5148519600030406121b01c520305130b947e01d80c1000c4141600e62400c01142d41d803c1d52100c034010020702030807c041a04200d00425480f0044000341d0090501c141403d4130310041c02055000c0089108078a444001305441c2400500e41c00a01c4014000000c00d03400d100380701c02c6d2201b000b48120214030810070f0403400940d041c0060040755101e40c50310f0102d42058410002030780c000400500801401c04000c0000c42d6002d01a150820460309001c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 176748705 1250 176747455 176747477
    0x30a09050a0f0b07090f030816051002072006090102060a0b010c0f030f0207090b01090302040e01180f06140c0d02030403020c0910080c04050424060e040b01080d031b 73
    0x15080a81495020b06030b030358031010b240e00380314260440d28462800c56540709030345c3ea240d415940c0016242e00010b0110002441264030341c0c40000b03503030075125005204039400301ca0060541d030141d0348440d108840666409200a91203288201120720026040750f009042c881600c000035039500008169144164580c10341d04544e9000d050845c01d900d80002d440054003210303080280c28030080940c40401803090100005081c11240f0890f151641c05030b4800020b02d10307540800c005081c120500038210355a80001c0000d003d0159400c50109218480100c42580c1a00784042140c0c0358105242100d41000200100e01a0402c1110103203036451000580b00e44503414101e01d046400c0040c15085981358003801341c0c606825004e001144c440300d0440f80e6600003c0180b06c1903d800740e5008015406c050310746840340c10403100186841c118a000000c45650f1190400f510303500a840c02d81c1c640084000600c4074950a1014942030307806800c05000424002031441c84544940d00c6200c1004204480 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 176749955 1250 176748705 176748713
    0xa050f09070516080310030b06040e0613080d051006090806011a0c160b030a0f1104090c05120a0b040b010804020a030605090a080d14060109120305091f1806050f030a09 74
    0x50b003080541c0100c0c0e820317101c2c50400c0c070b00000901e013400141d5040c604040013800a00d031a00401c1c140440d04406000309448444002011030080042150802024040442c0368030451141e140709502a042654130f0b58603110026010301c090307820001b030503004075006024240165186501410001c01c03241d03a500d03107a80c0390600b0195903521a04600460300800203c0b01c10540207103009100200d002c00c40312051282440849560000340185000240000c211080d1030707034083c81e0300c00d640b420030500d844088202c4a41c102030444104440c103680f40c40004440c00c091081c08140340080c20040d0f01410190005036444810f440000c15540d21800002c00a917800c0c050a04440d82c803609440d1146455450607002d440c10740705503020b000f5000c000903090740c4500c425208031088410030394109001e80d2001c8460354403003285580c019000903602d00501c00c4241c01015081c485583c1d02843c50304007103166245606507444402000400e0012600512400e02180d40104600030009a07442e01c7c0e2034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 176751205 1250 176749955 176749987
    0x912140c03030c0913023403080c0a0302040e07021c0806090a11040503031204021302160f11090403050d050703060f181107080a0906020d0504030609140f0102090a050f090705 77
    0x11950a040d80041006020551681011a250030450404080082c3c0b24540b49400c940b10340d0025000450070300124ad41c555900d0300920211900c0c0c6005864507464064240d2400320542e00800141d08c0303900c003201000000c2a8460700c41d103040c03802d8440d034142500001e8104401514a0000503a1940c1401d05c0040e028201c0f4014003014054036143d0003242c0d0440c3c01c203441207800747c2c041c1200d0008404080d507144216810042c01c440300c0385007841951030340d41c0701d03030b07000c000880300000c056003546070036520070115922a038882d41e078095076002c3c00310b0010203545025001009040c14071100784109448a036842058900c15001414150603080c2504040c0c04000d12212702250009015800c0c040c070b0500034050301c0301a840c1c0f041c50980d16407040f41c0e80c3d108102e00c0c40000b2014001840011840c1c3c1100b0f030060300544941c07003031405101e0800d0030260300030b030103562980d400140c000395820038500c440020141280e00c00c48840804000c68490a001820001000b00003c2d005030564a001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 176752455 1250 176751205 176751229
    0x10e0a0b0d090c06020f12160b04050c060f0309010b0d0c12170301150906050406080c030601050c0f0c03150103150b060c07080c0a330e03010912140c03030c09 70
    0x90038021081d60f400c4080d46442044c05592518080c9007c00ca495030500340c00c498844442c16032500c5002403d48410215100207001200c680c0580085100c07203544800c054501d00c0c106e116043d07542c0c00c180d041c1d00e007169080318019005080080d4104082996955483c003203916450b0141d4582c0702c5481e000380d1507040010540b0301000084004100002d010104014080e00c0e07403680005c56880701c200b540c1c523005900c12000012410b00005600c0e0307802201440c0c00c900d041c1001403c001405800c941080c1d540e6800a042d2380c03010030040910b01d0200505000309a03403813420040f40d411511101d0004852070400a0400e07201c2440200b240c403403500321021403080304180c8040548404660f40c4039182c9030840c81c45007075030b41d401040040545000c2c808c200240075500c038061090403c50300740c05d10315504850521a0003115500503407002e0290810803845070b041801031440c1c9450280c0070001050744840c50f810240302a04010300000308407034102011342d5805407a081c6030000140155506 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 176753705 1250 176752455 176752463
    0x60a02030a0f0e06040341091809010f0b0d02190f090603120905100309050c061b060702060c04030b0603100c0509030c01030e1203040f0f0804080c010e0a0b0d09 71
    0x407103400c00082001007030050142d4440e644e244030160031411400303036008440602c003001d002d01d01f4039a00c48a25030070321003d4407008201c8190070031106a0008149040051900d110302d0b14180400c04860300078411641d81480d00a0100484003a52000c5078960507c4400280280e482c030312006104100c81d09924010100907a07040441500d03516402c3c082c00d41480104c1e01200c81d60960b54225005a0055007640c4001d071007850100c10100c412005842008400e9503a402900a071310020785951000300880b040c041c07075035400c60984a40e51403030400e00400c3d403c21900808180003100046004440031290407100704016501e0741300000e41092684190b0f0103000d80b8001c40107070030580250240542c40300c1141a240003e118a0066082e20003200184030389030031041c40c208540044a001d550040d000e940c078050b9071102540e4420315000d20080035160a0408242000f0b108c0c1c0c1002010b4410900b860b004174442004000321300070f601c1501404600401c0850707810720040d80c543c0000741030703030300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 176754955 1250 176753705 176753711
    0xc020d020c01081f121b0308070204020d06091506090f0e0c0c0106090203040f050c030a0302060106030e010b040e0304050a060c02030a0201050309011428050405030414030a150c120e060a02030a0f 86
    0x5c1d8061095030380420300b408541d104140704c80c8480c400e03200840802100c3c1c10204013483c02091b40d00f084000e5100351005e1400c02d50300c1c2004a07559410788260003403485090307030b80155181421005071420b06991b01403210702407600d105001c0b0901c01401a42c02c2000000d18580b00c41442e29460b01400168100d07a425078404810001445076a81c2c10785500d6000d0425202e60038078078024192201a40c070005000341e40080d00410104c0c0c841c4e400600700140340000014843c1b003800015050700d80020b143d000355840400c2c180442d01d0b202d400c0000419007030900c9070a11342c2580c0480d8640d040104007906000001c1300060325404203401c5980b40c580700e01c0d801009031800c1030030b0685108524400442c04c683c44a804200b0031824400d050040741c01c00015428180341081c0c803d401150f000c000c80d01402090140c00005040c5c82c20b44600c1202c0290201c0d03500c841280041213064034003140440c0c14185812200d0507040030603081c2d0012070542001d0b90700c0e5106055a4003404040c0d1a43d80030303510f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 176756205 1250 176754955 176754959
    0x1080c1207181a1f0503070306052106010b13030f0305070206160b0114060d09031106010602030301090c0f0f0c060216060203010e09070609150c06020f0705010c020d020c01081f 78
    0x340c0d40c8000d0a4141c0b00e40111103101041c03061002101c8143d001540313100c101c10700055254090400341d940300040d0315020a9032626240441c28881d03006822049044c40517079141440c800070f014807170140066140e482d00340002000d1640400603a40300190031000403428440a040c45103044540c05600130b01015500c0c1d07079000b010034035030752880790648009002000100302c400c410f005080029000801346810001c988032103100901551004809201e400e88051a5240c4180043c9009080b00e4004c0c5840790326102050341170703c906140c4e410412408800310000c2d1074104181100045061034075004054007454488002e10400c6840c0a44500040741842005125002541a1140710000850540750701210640c2c64100c0d02515010a00910b014080007107040049000040545400d00030701c6c8071500c40030101c1e800030600248103040090414140b01090041a0003000302c2e01c001c00d100344805900944920100b14810304000001000c90003240507903408014200154041c42d020076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 176757455 1250 176756205 176756249
    0x1b030306050603150306010803040b0d051009140108010c05090603190b030f160b09030a0206030403050702060310050f03161205070306020c01050118110909090f160602011401080c1207 81
    0x1202811302440792061500220340c0c8030f800f10695085036542101c5034109943c01c203400c4040c2100900322983d00f0040100001d07101e40764011004a00310f4519a101e265041c00581d50070f40e0000c0c0c00c01e0f020300c04200f00c0d076800c6450300001c80707502200f500501040c44035094565006840390b078101c203030300d48124103403002040408601d07124420881d1000568241c1d0303c0e03410f8403446c0203440034240c0c1038014a48034005424100300540d4024881d16000d0300d850603a90000780c080d0000e4401d886c5509002d02c0038001d90038403005107a44518220300500203107440d902201c2d20b440d0640101e4150032080781e00f1300100001004440c025580c0544107540715049010780134002c000c24172640c1140c81c2e04400102100e1245d00c105041d030080644002d180c80d00103020b02200311400381c000c80c0c2034800c002942100d90814007110070380d10380c1603682552251801d80005d003500c1d130f1204619055007182c3d00400c07035000002450f0284084c240c1e0715401a1800088090400c202a0300112900044141140c440307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 176758705 1250 176757455 176757481
    0xc0605181005070909090c03060506030a0b040606090c08060907030b15030118060b04030305030103080f07050d0c02010f030b1c02030f07060201062309040308100513140a0c1b030306050603 83
    0x10f00d06903907503484020f5075504204280c0c0d0000d040a00003554000050010940c10f402c02d541c002130103012182e99031300940d114040a80b04490540380c096846005100850b154040c40c1d6481d0700d603240812440c141880014103000c801340c01c0b41e06041d0b8985403030006403640c0003c000c5d11480302c04215120740e034401d001c481c5690043d2214844918084020820042480996040e00c0c0c06695043c1540e0a66642044e80c0d441a20380a0b405a418802c1e03030000b40c0100218242c1c00c0f0141d6656084a070240700241250081381840c4041c10b051441007143d80d102c9a1043e00c62036410308480012084600220f42012400ca0741c0c0c01c1c660080600105a90342c05401540031160b0000081c54000c550721a04006418407940e86a40070303100401190200c3c0c482d2619641164007880d038001c6156a62002800c043c80ac0181000c002d03840300d51000d2600603018007103520650a0030148112010504010724142403c0d18021402c00c50300501024503200c1e9000350080c00020300415903c1c140701d4074400380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 176759955 1250 176758705 176758711
    0xe0d020a0803130801050106090b03151306060e0f0402030105101d030304080d0807020102030f060103092f011d010e190905040c1e08070b07020103140c091206070c0605181005 77
    0x13a5800d146c0002010b5125a01e014211040c05030b4460540d11807984000115410700350303080e40045600c1800c00030403181d12943e8010010381d120100a02c514101b44074070501c003085045d2044c0c2c4103100402140e00d4114035072858003440d02c0c0890514142094242c880c0707004590b000e400d07100202d4046660720000230031461550503921010035595900404a080c1e120880300c070b04d5068078050120300294026041101c00318428010103260080c05507241d0590781c11145483c80710f001c0039801606558200c40031002ca412420952040312403150000f80002c0c01c00b8685600407400ca400303030b034280703030b442e42c801406010074440500003810642401d4a06c0c528501034040d445444600900075540e0181071001110714540280103028a0b140540d07407642c10074001641415229200d440b4820195001280700c0c0c1508010760f80c5600010092082d0400984e00000c0140d1142043c840440d070000500034070554000004035503a0b585902c503050003840d603030348442c041c400c1c1101c40382005429040284 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 176761205 1250 176759955 176759969
    0x50601080f010b06040302120a0f080a1407050604021c0c030302010204061101021806031812071a04080304170d090f02090601090608011e15050a09090603030e0d020a080313 76
    0x7640a0700c0740015400c03900c44810380756000208120800c014140540d004122048450a5602c0491140c4520102c0051103804403402d070740008001340e845420222403500010180f0506080a805a480941e245005070020b803044010500000065180811440083d9032218161075069a01c2ca000390103504940a900080b80b852808112034202c1442642c10b02511210a400200092801d01c09140e2000c1c0021281032244004081c1e0010204403205858004009055603182d036410818480c2003039841c559a15a5000180004101c0a0b400d6035000b682066082256000070128072110744210b5503480701a50915402900340800505122000c41c000c1d116856540c0d110300c0110780803c443d000d2080072031500e00041c0101d80701d403a0210400c4580000013201a0380700c2c210070344400d890040480004100040f104200b0b60310040d050000c0100c110240616429944c001c0e0400c401c0d08801402103e040948000395a5400e0310722000f885500e040d2551000c3c0100c07232000c02800d60107405 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 176762455 1250 176761205 176761213
    0x602040603111602090405010b0a0303200a0503030c0c070e07080402040522060b18010e04050115060c060b03120301060309050606031504032012030108010f05060102030901030209031905060108 85
    0x5200d03480d25030219600f800c4902202250802c40b503013002160440034109451030341d40c0b203501d451240c480240b03c03030195009031103040c0441c00c101e2182201140354104980c540d001034450f80300054001003600c0d003121032500d030076482c5c40c02c08a5460ad0030302168400010361041c441401820f80e0002c1c101c030301841c000d90701071084c0d68481d190881c041e5540c0c0072011481002a45010100300c072544032441c9000e00400c40d100c40000c41442e01858002a00504a01a64a0144000c2000c01d21442e580c1218021540f038145161002c00b0b00030007031860b0040e0403941c45103005500c81e9000c0c000c0100c62600100b01c2e075100c1d61200300c000c008259000c0115100d21505c80480c1039032030000740040300c40040f0445d20225541d40e590849802003030400180c0b018210b10300c11403e64009219860702d1068001c1d1581c0c4a6250030fa403a800d442c011a0007d08891420040c0071581c2d84c0401110402413003801e015070758001c488086454080444603000c0d00040039011241080300c00300e400c1d4100e4036010121 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 176763705 1250 176762455 176762471
    0x9190608180c040f140406021209010504051903030f050c04080f0f0303070c02060705060906070e040b0906090c04080618011410030f02040b0414010e1e0c1b07030602040603 76
    0x218480c141c41c08101c034041c2d2001a0601c510f182c26040502c1000350b0300303c0440e2805800d801c4840110041c1c0e0704030f400540115003800000c404c01021075226401600030300850825031a526240d64004001600c81e880d05c409620916000350080c407418135007003400304070701d103451600e881454000e802a4007040c010f81518182605002030000300305008030015600e15180c144066034244000b0000b2a0442e609010300d0303000c1641800118030506031480a00b0b51441e02071030041000c01020a0b141c8928607011491200d03880351040194400016150104161140120b84600c0d005640c0000c80174450300040000300e001d0408440740010300c06009000b44180450006d107405411110418501031b002d504202140c61903146012240c00608001251400c920105041c0d446d0348455042c010365600c01004a1080c24a0980c0d000000124400d0720b245404008042040050001c118881012032400c00d840c8981201034400301e02e1074101c6184550f603141c11130194105100e01030100c4d16003004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 176764955 1250 176763705 176763721
    0x3030e0d021b0111060115180902031f060206040b06031903052a1002090a0308070f140f03161b081b04021810020c090a02120108030a0801150509190608 67
    0x105100d80c01c20b03000d0710b0310380e01f8040b245822614002d21081041525003541c0e0001d4441d2008802502c022a000740e920b282420040d208202c42a50000c0c0c040c080080401005501003003030b035003003036001c40394518940700c000000c0d1402080010f1488114070038143c00c010107401800070048040721300740904000f03083c440030454132070b070840b40c12007141c00004000461608a50081018032401402d2120081d1a40c60704800c81e0805842110004024525141031168801070340e110352951000038444100d00001154680c09031a411014070040140400c003001050603a500301480b80388410349440c0d81e1154444d40d210135030129900e019002100044050400d80202c0381781a0403010300110320300700301c418003810f44804000d02007103005a0700b50801683c4d032a8642030240405000150702c650501440e201540030603070203071003076901c1040000c0c10240c200e6a2181114814107440403a0258140252414170801c11403e6020b44964044030058000c588680c2c292125559115060b6075a014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 176766205 1250 176764955 176764967
    0x50c040302010c02060c03070503030a020c0c040b06040501030f0f0e06041208090d050a0216030c080d26062103040f060224100305030d0603051501031e03030e0d021b01 74
    0xc00307400a0074071418600581040c00080940c0706d018030403240b900307425864a9095800658060070182d800044c0c41400f280200604102d0780421101008500c2a100028049105910840d4181511000c1031200111290b100c5000010122000d100d0101442c594a494034002c0710101d454081c0340820716900ea2061036454425103c080050500b05002e15040d1500d810080e40c0c8000c61103080780c0130000000084842d002140301da00155800c50400314810300340116004441c04000e0014000d42110400a0600e1080b64200c4040d01040e180e0501194409030321380300c040c00c2d54007105002c8480c0840040100700b11010b4800220314180c54442c02c03a104c4416003003280d4000c2c8035040789405030110040c0b0541111441c2c0c0c50504081c2d4941d10302e41103401c0401c12010865681d401001800320510110b81082651456103041e98116614401c1d20000000c6048a40b100c410b10101098041e900010105c046281166616008410020747c2c0d00103440b40040b50781c107100307140c1d01a540114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 176767455 1250 176766205 176766209
    0xe030f010b09090d0c02150d0c0f02061f05120c06070803060a090603201c0819090501090b090102010204051c051213060309021906090e012301121b090603050c04 71
    0xa07031040801d540036000c100701f410042801e4001c51004100c140e40049032442040390909454852440c603102e203600190074402d0003048020109002e02e04401c540d550705480c2d100b036400c2106c001e160301410307521213440c094039400080e40020000038184d05101c00035018501c1140e00b19078070383c3c805848415190950300c15110041c4901801c109170581c407501c0c0407900ca004200644424102c0303003800030600820603240000c0d580110001090201c00156410102d520b91241c18180c1e54035143c01c000810042c6a4429040748541c0031034042d12580c400e404a9008050043c00741350f4041d10440350003200300b10188103c4041c890b0741c5010244150003820364100141842c0103404851a00c0c0080e800340105a8040b070707100703844050410f1401c603c0751110014100ba503546050072801d00002e0109494107030041d4441407880b000522101d00800c110f5002418280b03001c8441456140310800a480290781c98920380c2c4203a400b6100e0b40da84011402c0c1200c100c0c0c1c2d01889103482d800c403203414034031030381c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 176768705 1250 176767455 176767457
    0x121403010603020d0e1e010b040501030b0117031e1902012018041109010206070804050714191415040b1207110a0b1806190c0e030f010b09090d 63
    0x920040190a00990141a05038a000004580c10700001c4465041142c41030baa00003000c50071005d03c1c0b00c03050901c29180c0b40c44007600c08000c80d5041d51100d003c038000503c0ba81000c984896960a8001401d000762561004c107a0504459014101d240611a40013512841400e1402d291201c2510707205010f00c0c040e020600f4486070081c2c0c41c1002001c015407041c1701e002e45804041004003402d840f0761156000800e00500c0d426110001d400009041c20f101408081c200082282400080390b4042041c2040b6172110b01e403441504070010102d408203082c2d0754904070b00c18a1000004203a1110310305005001c00844000c4040f07040b400d8544000c0c011401200c0e024181407205c800c04d00011176245070041d09a0600d0410180c060102d14544136441d40100c2d07260310340100340a10150a18004100c2001c3e40014003014580401c2c40d6200c00806207060440d641c5403240015141c1c002c00218803181005401e03a102c1d0501095502d010345103c1c0c03265070084447d80d00081c4030842c042446402c01c051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 176769955 1250 176768705 176768707
    0x40e061b0a02150a0b030106170c040225150b0301091e0f0f05160501030207080a0f09230f060901050406030b0f0904050f0c010e03151b03010e041214 66
    0x500105400d940004816009620442c00502c010003000c8001d28414200c0340d501148140c0510245400c0d1680d036032020702d00c01111049603800700d8001c540d500044a0950f00107885109042060a28203d031540c2031104201c4910101c1c203014541841e8460541d030006e0600011230114103040c01c0703400056002d008400680c21800038448400c2d82960039600070f0004600c50401c2d500c540c400840001c03000c4a056105d03103e00b0f0740b41001141c18200031300c400d00b02181050443e481e20310b028030980b5034000820000140c2400e2840c062030002c0041d08000c0d842400401c4003481246110001044a41c80b400c3c0c00d03c038103502407030140e003142e02c11201a51028105450000c1c2075003c0d20602a46941c8400d402059241c0390700c800b084184100e00440061000080f0640b00c141440e0324246854100094007851003103d13240010304859032000e008a9407404d82e11040319400c0f0b40c02424586011000c000b0000440d005120883d80c022402071814045a002e40201612143c031050706c05094200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 176771205 1250 176769955 176769991
    0x7020c031f0b03010204080703030305010602032506062103021203070f1107120803040b18060c0c01020903030a03140106030606080a2c01060611031309240311040e06 73
    0xc0310070740400c0150001c0040780d103500e64000642660065000f00c1001d502c1484104145507060103003d005103084c0c0003641c58030044521648008820b086c030003d06a2514440e07004201080d800000200801c4001441d04140006c01116100c0803600a030014480d00760102c9112074444d040324000d0343c0d030b51a45243c88140c0f9905903002000101030700d11900501e031001a02c41d040d6481755040c188140c09907035403850b1610f0440804c403009044a0340720030070407000b54064000015244e410030200d95806440d8108041ba00d40644550366045030580004101e07000c1c92501900031140c6109a0025042142e81342c030002c804681c3c0603c034400000f0b601001042d55009191300945041070f401449850750b244000c101c100004011030040803582d9220020021039600a80391301407041903d02071480c2146401400b000d48255005183c0e6456882a20300c004418000090801c01c40541c8294901a80c90610004005031158001d0003039043c0420032200d090003040003803241c3c11a410070847d0803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 176772455 1250 176771205 176771233
    0x120406050916080a1a04050a060e0109080706020309010c0809060601030b0d0f0308011a040b1911070b07020f0a2102040f020414030c010807090b03130b0103110907020c03 75
    0x38021100074012202c10321038070003040e0708280c090258800285003500d003e20b00500d803140c0c004200310850980e1002c1c000000ca003c00d4010140350480c1c030200d102d114840a090040854600042410000003000030421403542c01a5108441890003040400c078100c030191501c0c00704031150040b682240c0c0008036250b02a034010203081c400034003c040001d408c4c0e904c0c0c00107124110000e40c00f00d01400c00400081c180c51054103500907460f6403c504041c174200074117041e4042d8841482403400c0c65019218020301c641a000d00d144081c03800c480f0300301c0c0d84004007045a0b00100e0103070b0244a529000c0c6105080c8201d110040341d1101c21481082c030b03110007005d07030300e064640000c80c2d00545409580c2c0940105001030000b0b4211b0022850450b04840e081510b82900c2c000384905000b0180100213803a074000000d54100c4284458241c2d0369914180310342803440c0030b001c1c014038460300300c2e001006002421104882544098a442145071500c00d0142e9507500315000c01c0ba030503404494040110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 176773705 1250 176772455 176772461
    0x90105030607320a0c060c110d051b1203010f0e0105100f030b10030b090f070906180812030a0b0a0807060c03051303080703021b1318150b0a0902120406 67
    0x9a0300c5000c84074900d04020400d5140340d40511344c18400580f030080040d0030300050380315611421203a402c0c2000b46400248049032601ea00c04102418008089400a00b200c00680d10341840020304d01502c02030b800000d0301440b9a0801e00071318121b03104a0101080c1c500e007421145041c1c4c2d800034040c0c0105503030140c00b142c810b800c082d146c41c20940c81f91300b900d0300350322002d9521520208680b008101c243d20ba0060100c20700000b4001e001e210440b5081c1f118550704441d10a0580c0c0c0f0034513196500181101069112000951100190344103043d640c0100c2a051009540200f00114043c022400c5113800c00484194600440d48507400c000001c00c00f060051609585c1148a4100b941c1403c140c03c1c1803103281d000590043c5d802078000074200c01050341c18044055050f841c080401000d001d07650104002c4100304540b0403065548062440c4070b0703800c049142c01072a0707102012241040400c052040504403e00146010720286140414100303032a000f90f9000036558551880c2c03c0c1e0303c40d1582d20203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 176774955 1250 176773705 176773757
    0x1203020319030b04060b18030a02090f04030c0506010e151801051903051207030f050403030206040201120e010c020d030b04180602031b040303031a0a080307060c20070302090105030607 81
    0x80c583d40c1c0001a4003600e45000b40001020700c5181c0c1c40e2101c0c1c0c3e915007016500710951402e442904851040c0300140d54240019400905c03082e4a0031444e69a45416100262134071405070003403281000004068208110b5980300d0130a0fa561462107880a1050180080c4410240b1031000302e00c000600103420001b43c00c601442101010407595581c2e034488509010014880002120740000c1640900d5006003030500301d00c0661038950303e41071541d100251501c901401c001d0401590700340c66540c581880e0003c21981c03140310000c02a140360b9540180d601c0c01007004000100e402d09681601515041c070030084070003c02078200804521982d54a0025400100501c0c11025147d20302004200013001400141d031103900e0001d5002140c0c1d194003269440d48004501c5109155420b20a00c01d020040d214501d50141011030b8070040c40c0b40a40c0c2c0c8911144c640000c8440e102c0b00554101c2e8002070722802c0f42d0090b48d104420b40d8030381c4107054941a04075140303408941c0174402c400d00340080d2102c0c0c0c61 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 176776205 1250 176774955 176774957
    0x6051e090f1e0615040b1e030c0105040302130c2114100b0f07020604030c0605040905011e0b1c050702070f0b0f09010c060603021003050612010b0913021504080607091203020319 78
    0x91001e00f40400103101c01c1c0e409a0240100e84818200021f50808001e12880c8200034200242414556030005810030f40400d6800d02854076480286d07405401109030303007030f40c0398414085400c01e103034489410018400d0074410610440303100042040030030810311074810b076036101901503c1d00c0d4410039080c1c0c1503400070000300d070007900400c000030110703005245260140c0781564410795224034250f40b4506883c01a0844c018541140002d2050000c00103608000c03100c07141e6080d5112854940c1d00e000310100848140c03020750401d0100401992301144000070758244404850b0010b456011048003409410039540e16020100140790302c80d8001e05071160301911a03c0080303605500c039400700710047c1c0c4100c0b5a401290302e40050042d903181160aa02c04400300c94020000f40b5030350b80002e0640d41000c4c00c240200d503000350b900b10664540d2403a600311910001081691036582d41c041a59500c0200e80701000a011080e0108405902c3d11503850020781590041d0308101840c4034501c0e1054070003101c80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 176777455 1250 176776205 176776211
    0xf01060f020f0f01050603210406120b0307030b01060215010302030703080304050f0d081005010e0906120f0a290112020103020315100903020a0909030c06051e090f1e061504 76
    0x101c21280c200440700035074a0303c10021132541000001d25251a000d802d00300a400c024207105922002c52805480407920305107010780c0d2400e400e041c1d8034010304900c0c91603600360040030030110500c126030311024102c501a6003241c030214464a00004030160070300000350315401c0480d01b003000ca640d0601964215014509032601410404c1200c0c1c9000b003051080408160300d0420001c40e0311003c000040144001c0c00c01e800000c544031700041c0c108070300400c250312403008a555030340c00c050308201d00284466110202e440e81c480c0c4d410042a6291103401c880000200b4000140c9100c40503110030307040701c18219032144801c0d1a58010340c080d4000400061360710112540d15041991524956042d040b0240c4612906608500601c0b4070f62000c0c1d00050040b074104100180001e40c000310030481c45400140c00900c50f2680404060f4501c00304040b9495051460306029820704046400d00300d88030307880c044545804201000301e841001080d09030202d07410031000a9004031100d0804120004010000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 176778705 1250 176777455 176777473
    0xd030f0e0f0603060f15070b090c06030114010c0c0902070305090a090207031d01030213030b0f0a2f07080f0d0b01090b07110301140a020a0810080c13020904020301140906090f01060f02 81
    0x30f406e040d00860001e5030590301c002c0910900d2a0705200c0300c1001c1c802640c559183d5030400304111000c6454644040c100300ca134258030018010141d1441c005015101d106564506030b80c20001c08540014000c5072151808003c009483c44051084418844d49a01c98440800c040600c0300100070042030440d0600d5020411401c00040d1004003070040c51107941c403903000b824100f0f0b0b00d43c1842c030700500301c0340f002d0300d401007089040000001460702c1315804950440b24501407403801d00743c0e00405a000708514070105c1c10702410046100a03211f548500c00c0c0c04c200c40181d640046a1240d82480b070b2811b003070410441540401c1c0900030506003000050008500f03008240c000340018041155649503040e030104000c041c00780e020403004d03002071815190058550800f80226126841c184599100b40da2064400c0743c80051501583c0e2362000c001c200710744a69692556028070980904c0c030a109260202c00a003091500020950165541280c00c0109a0900c1015255100f0340b07003c0d242036119031144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 176779955 1250 176778705 176778739
    0x8011e030b070507050f06060312091f050901181401030225060e070e0907060c03110d0c060609050709090e0a080d200f0f16020d030f0e0f0603060f 65
    0x70703060041449540f034507550583c5003441c42c1080140300a03504142c005509200c076030b540001d113228002c4081400301e941c4140c8100040c80d41035021048841004444110400301a0040060020700c20300303880301d030000d400b008040101070905000301200c50307441e01800c40d1954031031750107400c1c1080f07140103003003150f03201071030101d004903040070112011500d503586452019010700c0321030000e12010a940e950380c10600b0486480d0754031030180c6030030044a003000006040c41000c071041c083c01004151500900c080350001c1449408000a603442c6041c0341000810841c3e51141e40e01ca05000e50711008035604001d00c0710b001c0c0418504601441c410000c542c00440c4c641001002802814400061003a0072002d8208038130b0100d51006058010038000780b000500c1840c100c600682d502182155112403040a8013254107c000303029402110f010065801c05412800b4254410002d0312034061001c43d2000b000002e802000b03241c1d802c8242400401c92904000b07400e0102d401c0010a0590032200c1e01c3c0d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 176781205 1250 176779955 176779973
    0x40b0f1c0504050706120b0901031205090a031514090604060c02011b0504080c0103020a0c0b1e040308070305011e09020706090f0b0711010213030f140304090209090a0c08011e03 78
    0x10700341d90f00e42000000708803c40e04014081080c91440350188582050840010001c00051002400310005007525a01d0148030300d088038481c031002080c0078146500c0e0306000050a05240a80d8a4286440207500803045074003050340c842c0300c083d001003841d642e036603403114040d113140b45001d0259900d502094903001c0c1e02c0e1a908881c2c3c000c6541c0d517501c5603d031503800c52800780444002414184104210710005a0088007c1200ca0f0011081039164a0715101d590a0071441882c490742120110107000402d80d00c00e000900480301950107011903622035541d003960301d4048100310140c200301e40381000b81000030380141c104d0a00030100018580038503283c43c03100d909240c600300c0b01516100c040081413500012040d201da02c148008500f004071105150f03006402e00e000217851100301c41c91910804c03481b0640519174200c1007064076100e9a403441801c01940050035160301c51070320300001509001082c8510101e0183c80d81ea401816442e00010400005d41005d01c40b841d51120360020000c100c800c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 176782455 1250 176781205 176781211
    0x507051f0903020c06070b060d110604091b090b030a09030905030601030809030709050f220203010e06220206071403130e0f01120b01030b07050d0f050103050d05040b0f1c05 76
    0x2410110740d40006140090521001e0340c090343c4600c01c14017044001c12031782c01e001940f080095540325802c803c00d0034044109d00403212850380c001000140480d0f4038440b13030410100310b0100b520910001244a00680717030b4240074020041e40c0301d4140001005c1d01c20f40d400004425006e82440e864141d22a17000c20300f056070036042950580000906c1c4d002504041090f02c0042c001d65008000074100795404440e81200545543d52025007002002184086070019210040d4010002c1091f031290408144d102c42d01120002d2850b05a0030000b0085103070140c4441030587d004284d0f500d00143c2d07a440020803c07548034107020394481803214006410611500c2e60140440c0510120746203044804001d2002c2c0582003402181c0e00c2d9002f4900203006044030a041daa80100d901c0ca103541e69440884940c020352b80424002030030542e2010840c041f650115060ba802102a10f02100c9043c0f000d644501c62072180780a07070340d42080154044100c6002401a03071803400c207180c1c00c00e0301c1d0b107001d003090701c60a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 176783705 1250 176782455 176782513
    0xa08070608090d0e0d02061c05061509060708030a140a060305061005010f0e0411211602061303090906030506090616120f020d091a07031407050705 65
    0x220080c018540c1010710789038481040802800b070f4008085008040d601070840c42800b64030304010340001c540d900f006031070480c1c00c2d00b1108160442e004001c4c501402c03040c2ea4036400360784000322000491420504451a040d009000c052918040d40e0754030280e58402071800b50320a644000081d240140c04000134000d1489250101b0460b0171400c2480c01d050000c1e1814003004052541003040e640c118841981d114418106100025010008100546030400c0340c01001000080c17400761000d100900c00d00c45816400c01c80311290b95a401c0b50703800e10070070702c4104d0250f4403910010300d03d6442100c000c0c040b02d11900d068100ba554809501050750250380007141c00c1d030001d0041014089041060543c001c550100803101d04201c00000791240100d00c6925070542d8459045214280a40c0c0448204d40113a85040051041e1800d2001e603501d000d10288041d0030710302c00450560340c0300380600c092070b513403410041b21a03440311801a00d00e60300c5904115a540a0b0046004051803c480c20000300c0145d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 176784955 1250 176783705 176783713
    0x3090d02060417030c010b0306100302130605090702010c11010c1b03020c03033712020a0201112101060305010503030d0203071b110a05030a050606060a05070609030c1a04030c03080705090a08 84
    0x3045d1400d484100d20320a00030740c812402c000841a5411007141140d03010f844500c41c5ca514551f4081c01350401d0780055810064000074040c00030f0b8154005501401c00b650b0301407148141e48901420784d40b50360207200000d4001a200150700c04081450a02c4d14440d00403140c8566041c80860f0441e00643c03401c4032059134900618460f41019080c2e42c098840c0802a00702101072150090105c0780400850001240d01181100d8070780e0003540840c511024102c8500c4c0c0f80d0f06960110741e0000f00c2c4120200354210a68000224540030380601810380c0c400071302840c00e0101c8001480000c3d04024800000c001a203281d01c00c4c040c1c0995004000c0c80c1c0600719410350460b441d001e0111900c4070380d0000380254404002c420210700e011492940100c2c00312621a82c40b0301c2c1080440e8140a541009040141703400d4000041607044000c60407500e208000810b5020b00340c2401e110402340c1160080e011448040130703040040d21034518194801020300b07000703041c0072688021842040441e00b2101c00e543c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 176786205 1250 176784955 176784967
    0xc1206090506090108030703021e010e060109020a090506130b0904020405060309070501020d0e031005150a06020c0306010501030c08041106041802040306050606030106020d050d02041d1603020a0203090d0206041703 94
    0xf0701c03065060240105c9001140f070f0043c1e95400035503031051a8400042142d00445071802050290810340124021800304c41a5503194840300c0025800b0040d40004141112030000320f50a0600c1541c2c1540c8036284100040340c5400d00741e2403290b0001003150380c0b10303a007004042250341c6c669007c1c41c0650f800c0c10080403c42d0800700003a1405650f0960201880b1400c1d400071240da50000d20030110030030301303100402d080e140c0500110700d4075030400c03184e544420042008202d8a6001807070400454040b0201ca64a0741d9940054040751aa420702900042e5402c00040c040303500c08840380c5d005240035040c01c0c0f0300756545c1851484040f080c04070300d007220b4001030304005006035070180030b0f00064200c1d42180385515000b006507172001d0a00d0500103020700070644c0c3c00c8a80c0c1035410b03900200071440481078070305c007040088072998030100d4507400391110301c01c1c1e20700c4010b1192003a02c400c14565002140790100b81410804803e0301884100da002104210109203c504944140d4014070072a00940d2155 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 176787455 1250 176786205 176786209
    0x3021204050c01230913020d022134020a02041a01140f03010e13020409110108100b03180708030d0207150908030103080705030d0c02160608010506030601030c1206090506 75
    0x1e507102c0343c0300c00b82c1c0b8003083c2501180280f81d130481d201700604807030480c0c84484c1d0554003000b9005410010b180c0301e2010601c020003000505180d8210190a01c1c400040c0c0d9034007441c54101d0461211452500b6282d040c842d0503400154207c002c2884c0c2c900440d45101c401c3c2e800501540c130b1050315482a24076805d806945075801007514615000c141001e94140560080500d545010503c20080c206130054081065210401644290b09070090000d010000107800c0c6a0354000081c1c08030783c002000000001ca4004591004009965561100c0c1d03203140c841150983c40100c0c06400d50495020b258400906068104010b00040380103440160321074499041544100404060b01d140c030504250700741001504034402c50781034a41c40440c890325a0307601c0c1803080c82c601410301011421890111500201c9400081c11a40100002d11002c0080d44504007155040e6080c8503244e041103044c40461103660194112020700049481c00840c40d4030203080000035141658031945e1540e40e01c6080c001c02d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 176788705 1250 176787455 176787467
    0xe0111061008070819060c0c0611031608040210030c11011b0311040602030d110702030d08150d0b0f04020402130603090213020403020d030305040203030c0a03050306040b03060601120c03021204050c01 88
    0x1303001c00f0b005801e000381d800001c24003040b449840104159038848031980c442c1d010300c00f10000765410080030403100d400400c0c60f40d0241d005a5000d074050705200100d4440a01c620b900d5441158041c144602282c1c0e03900742138000d0154125004140706c03a6411010a01000b482003280c401c0c06840800c144d600401b20150403540902016035000508110034401c580c1c00008441c101c101c8010002500440010809160700079000c0081d4940204410344482d0341e4007006440c011100c0120842e1020101d004000c541c0070074a42c024150092200002e025455055180b43c0c40b0b4009040586002042c0c8601c2010030207d0f00b01c0c0011070703030320f0710000c0035814a849020200c1000785011031070541560001804045806401802c141d1036a00107070840d14103006444083c102c4204884605040340b6014010f40c004a40e030700d000307501d40b50039200b061a001540d01c0c0200410385400e04408100e4042401500c09000e1050a1680070440d0030312070030f03030061014440d5009002912010314810001000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 176789955 1250 176788705 176788709
    0x70606150507050a0b0a0204050a08010b1003050115050306030a0b16020601060201060f05061b07091a0303040b0f0a0203090316030201020d030501080c040b0a0f090504140304150e011106100807 85
    0x4000e0280b207100300007240000c041c01c0558102e07070406030175507031750145a02074441d0f600800e4009064400000d40d84005410102e00c4004c01c0780c4010300c0d01c0c40c421080302191b409104000040182c10101043c2d00d001c1ca00943d08170704041c0590301e1044851b10303142c0b1039641c103807003000d00001031a0400414590512405025020340d1000f40121860072202021000550141c94401d401c00644080c0b5807404510520141c0da0940035511400d6450040074005c20001d00307499402054440a049a85000300455041c0d5072100c18450411f03040c50901c078407541040402e042984020004110655000c00c85e5003040f09103400600d1800c1c2c118400281000300310700584050504001c0103200800e80402e0044142406890020f455062140051410070083e0b0042044141101000c221001140c20180c41107014a00c031141c810140100c41d540c2e4440d070700c641001140c030b6007181a1001d1007480540c0b20080b05241840d80b1182098045003001800d4a121a1101000c101000643e07018050400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 176791205 1250 176789955 176789957
    0x1109090d17071b050105070e0402070c260f060403030c1d090712050c0a1404080a02010507020f120d080703090503031915060e011206120b0c04050607060615 69
    0x1411000144050580c0010030394541280418100003425244a9500d40400f00302c1d0084070305074911541031450080c40c00351241000101e04e4855107155042c14000c0700c400e0341e4003010111032907140400c08050320f06240f40c40c801c14601349042468080f010000c4000c0d80714071801805aa0620f0710f40902280d0601e20500c09210121204500b8a41c850681c0c0e20030b02007e0b950342440f995400400c5401c03e004070810b013040340c906030a2100e503c0120020b81841c055588882e01c01002100c6e490840c4d009905c22540c9503030001a2940c01135210344003404400e0f00c050044042401c80d40000399a01100044541c001d074484528503030384035800311030250088482e00b01048042c02c140c0f07582e41c40748802045865001100d00381100c18600b10f900110800d004c0b001030072a42901c40e0001412a03c0c146060f50005503c0e0782c002121514520940040f2851a6821042c5881c59510301007003100080804000700414040005c4a84801c070040001324401e000019500d820689240190a0214840c00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 176792455 1250 176791205 176791213
    0xa0e0a060c0f09030f02150c070f030b060102060405030412030201021b010b210709090c030203120d0e0705060d0e070b0a0306030203150402061c06052d0415060c021c110909 76
    0x4080341c405032110300d41c0c40e0183c4e41e00c1c600840e02c1f003005602c7c0c13003084050b00306840b9198000603030782030200410080d00e108400c1041e41c0c1e01c030000126500c01064501a00e603401c100010010382c442038400c4951288a40009410012580b00990f0340d10040051440c4a9465107045a150718224042c440c206c40e0b0106c07240a0420030505440e0303654014000c1d03a01c42503880c45031a083c030810007050401954020200c84050f082c6281b004c18036040b10681c0a0498146000702851107804203000c402d6500c050070180c200207c04c002c10740030700715400100e8010b000c0c56070046a1303603829000505048415413004170300b0a00c0c40c41898580314030b100c08040d00c14080d0b0140001669000c003180c480d810745140d2200052000c4c040c01c0300070718481d440780d68460310700020f440d41d69041c1d00c483c07000003c0340c045c502192800c0700c080c001501c28400448001000354003042c0081400340601310003e90010304498500a0140b055204019400c4070a8540618007c50b0803168580100c1c09980308442c24090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 176793705 1250 176792455 176792459
    0x1090602030d09030c0b0702011e14040209190e0c1504030507030201210e0109060e1501050618030105040602040801110703120207060212070e0f0109080a08030a0e0a060c0f09 77
    0x25100c0c020107002d041c1654541840005051144c480070644981000562040d4100010040d000300180090400001c1446c0d001c000d001d05180714404920b80341c2c0c5401d502075030303a0340d003005600b01005001c0304034142c045220803044e185d203210f0624115050703c01040c0865034042040107040182d0700040c050300d4104024000101c01007242012258203080407003121064650b54941040388140c0d040600c2c0c680305000c0e4400005400410704240500001c020701c588a202c0c150b191850091320000505c440030041002382840d100500c4204002c00f4600c143c122070344000ba003518419a001ea4281c4d4000c2420f00141000b03100d1074900b0450700300c1880c0b4001407590003800c210480c02c01d1007038095001c901704080c0101a0102c0d174101c0c040712100c81c1940785c40070300605000c81d039160850044030840003e84280d4007500055058a07503070f4000f44504c0310150303a41c12003680000c0a088803a503e80c044c503084400200310001d1110720a501c080381c220b48959000f89a0021301e1504410083d02001c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 176794955 1250 176793705 176793707
    0x6060a020309060315030d03090c0509040b060108040203030c0f030403050f0105060a0306020f130308120a05010b090918060c1c0903140327010213080a0218070903080d050f06010906 80
    0x458494002c107441084d22a41c4011511100b0102c0c0031074070b5054040c19080c440300c20fa042c0d1040445a00c158131031700b4035035181d10034000c042004440007065200a54007003402580141d0100d50301610003411a807900111034901800e0185060041c9541d600c0400d050080000910000042103450381c005c100c503150180006041482911000d86056400280b41e502e1403441c4045542c035202c1290000502a034910b096032880d8095200d40c2c40c156421030205658003142e00070281210843c00040b400c00318010704100001c000501034941880001d030742180b00300b0080c4000c80c82001c00d0303944a84c5a4070201803c80e0030b07024144140c41e5451a006500c0c001a4000180c0c00030003d01241c40d580300d41ea0858236424280c0b215210f0088451200c1c001011a04150020846808882a013001e1141e40e030426a44d29090180020b50112107855401c2298800600b1154851341d5490720044103035407612659803039031003000585441c6869608100d800e8240b00d00b0140c009100380390802182c1d107840c00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 176796205 1250 176794955 176794957
    0x80f0c040b0d0f052a010f030b030606010e04020403050105011e151709030c0a06060f0902030606041202010207180f060501020c030703080a0e03070f0303080c0309070e06012703050606060a0203 85
    0x7001003403070383e00d1000780040c44410054407030741e084801c44189000300813001c2860140e0040c840703280001d000320401c01d1000c1c86130154100c01e24010300109002e40342c080040d2040a460000c00d40c204c0e42c203010000201d0380074003d250082c01d40042038802d004680c8031000b5484455005016250008080c0224555000044004178001030942c41c3c40d60300c980c81660304500c00d0301c0b40840c2c580b0540c00910f06011080d0b00c00821510150324509a01c0d40d20110141a404102d44140c0d1002d0306000401c2468070301c1c90141c28052052041d91032154845a0706400d407511000002041031391a45802401101445007a02801007400142481c800c0100000c0ea40c2c0924000103202c0d1303601144041c1d08500840b0702c03080e0507000409503410213483d50902400e002d81d40c44154009074011001c40d0141400d00100ea00407455240602585403c10348010301c80b00c8094041410803c4280d400240e08040003502d80180c064038000044007855070601d545402000740c0780340c2c85180e003000030b030b402550000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 176797455 1250 176796205 176796229
    0x203030c0904020c010c0908060702010e0c0f0d050d0801031709211f0e06010e070c0b1306020c0f010b010e030703110f06030403050a090605071518050106080f0c040b 73
    0x180596030744205038004500a80103200d0800c00540c00c0600e02c140c0960810111029191144200e501594038202d0480c280e0720003038030240d4590007401840f45d80c2e0511188070800814068141d0002c1d8545680f854680f030781410040c00000c10388801801041004290b40ea074464805010b10706015401001910b106010450a03500340e400480800170848180120b4a800000011203090f10341c2d80c10741d0130041c1094580081c0180101000460020305640b2120b0181c5840c0d03a0f8403e03852029640e1410010303016021680708003480851200165081c00207044800322000503121008411322184d007511a038a1034281403110a141c1c414481c1c0300051400110b036000700c082441c0040c440003184dc203014030b9041c075400440000400041c190010000c0580d0042c590b00c202100355650700c1101c8502900342c0003010030580b50010706003603000d40c00503401070b815124400001c46143e61001d003111180c0c2e1000d07c580c2c20030495060312601c1404a04003100054400f40a0480d1020001e010040d901e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 176798561 1106 176797455 176797471
    0x90b01020717030a0810090501030c03030305090601031104110d0e2112070537020d031806051e01081f0c02100509010b0d08090901080d020303 63
    0x3011025000c00302090245040031160760741203645174006803001b0b84c3c4003034260700801c211003d841014000e5201e400d0742c242c402d1441c076003e029114000c00c81030440c1c00680041020514981d22441c038a81c08a40002d4207005000d40d41c1044d010f40004084018035051403d091503400003840f5211000703020808c400c000c4d1024811030203100b1070421948902a090210700018001c0340075012012140311200000d0389124009004c021800d98540500400c03200c00c0b01c0fa59806211050101c0d07582e107014040852a00c07000310b400119038100800440e9608000781000300070003400b503103014000794442c0030355a4031074010f96113844001c1d0040c0c40c401031401c2e40c0c031080c0039842511021504c54002c2d00403e102c881c120300017000020315241055483e600c020740c203a600c8512044201d4820a140d40e01c0c1c2600b030081c42002c0c00705070000402548042182d0000302c0c0c001080d65880010 = true := by decide +kernel

theorem cover : BRFrame.Cov 176618705 176798561 := by
  have h0 := BRFrame.cov_init 176618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 176618705 ≤ n) (h2 : n < 176798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
