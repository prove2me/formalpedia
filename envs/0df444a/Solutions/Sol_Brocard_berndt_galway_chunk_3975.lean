-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3975
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:13:21.650499+00:00
-- url     : https://prove2.me/submissions/8a98184f-169c-47a5-aa23-6ee9fc2e3730

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 714748201 ≤ n < 714928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 714749451 1250 714748201 714748219
    0x8060a0917130905010b1201080f0d0804020d2a060212180a08070b09031c0e01260106110d0306030302030910020102040302090f10080316060e0a0605070315080111070f2301050105040b 81
    0x2b00a408241c01044650a240040f43e9844500001d030100c006403134003500088215001440321450404003a110290340000c034041e050341c9410503611003c800728a01d50f02e5a08000e1807401d008003012074540c10310000d000300780050302c1c1d4103d00d1a21109400c00850b0940001d0414898501001000010006c500d60300b04459107441004016600010940341070082c00b8100d4003100310050600c64400d0300030300e0150360722f43e5240030090104084081501c418000c0b40725100381a813290140c0d0741a00d8140e0021450800070b481803100c00e1371034800c5601195424000800160740b0010031501804040c010510203080c82100300410104552243c61158020030040010014040d03201005681064000803649e0810300c1103820804040001020540b03410300300030503ea09980034424040500e80c0d1407a6503500c40022a080760003004a5082c452424003100f0000390301030f4107100038a441454090301806201d43c1c030103d0350710322603614041d03030f5119001032200e4182482203008840040340e04040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 714750701 1250 714749451 714749473
    0x1020712020a050103090807170711030a1a1005032407020d12020d090605100608010506070507091d0a0309060e09040b160302091908060a0917130905010b120108 71
    0x8282e0074510495041c152034424080a0082030400d451039542c00a40e040b030601102c3d40d003011180d0143c6030885070f00c41e203d00805d016007000100c034041c5603441419802503409801491048000060010800c0070100c00082029141440001d0801c0941442c800185c20b0403c0c00d001880c03001812001154403442c0c2003138045503c024501d5201110000050b507441c0040001c002800c10000090025030803c401d020b08500b81d0300800742201c0c001da503168034907600c035010400544520340001c0c080350b03c05c0100b80302407001d640c401003a120101541011034203034801100c0c01c1078140d4006402081c2120820030406400000c18240c410040710f8010b164940340d941e6030000000680b09035a2070360301c4007030461301c80d010391b04072144c140b0003c2020010300142c0c04030000d80c0d0320b00c0c082c1d64414003d02020541010590003154003451784007800c8000c0d0080c40b50420760581001c4031880c0007405c0b40f18009105a100d201c0c0c00e01902c150345180b69111000c020140e096001a03206802c99231141844c42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 714751951 1250 714750701 714750709
    0x121113260d021b1c11100801230a03050a03050409151a030618090d0207080307121103130905250e060a03060e010603090b2d070323060102071202 64
    0x949018100e0201c0403480300e01a0114041c9940d044c5964180c801c1040c0050601c03400c0303000102e684000701c461068901d120704084811010078801e80321402c07482d50b80710f4800e683c0010100d910050180a00001d145c0d2911802d01d840410a0290701041000a09204401d802d008a400689081d0f070542c00c041d1403d407240708200d0100800c00c2c0103032000310221300f042d5650074100c54038006003181e41c11503043c0007100c5503c800c10025130340058803412a0010b4074a4004c415904140d8103c041c51a520324816010b03180c01d1180c85045045010400100da1641d01400350000074115039500001d040c544503e00b100c41b07411400594019010240441854540c082c40e52102078805840c0180c03070302485801900641155040071f51403030200c40020407090340c168001520540513501c20140c070740301c0e0301d141c1c0c8614040079108180141241001c4215a80104803180c1200700c1d4900091048115401c4290100202c500e0b0020802c1d410203008156a040001801030702228141c0400e1041641c001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 714753201 1250 714751951 714751963
    0x7080108070312020c090702160e15060322050c1507021509012a060605010c0519030c060c0f0e12060f04050f160501120b01121113260d02 61
    0x20f09000d0700307544120341207100348010404001c0252000c540c60130107800c00781d1a00300900901001c4101b101000901c50480d880050180c0040100a03c1d148010b40510049500c0100000d00c0d1240c0a01c000302880407280c07051801c0740c082c0380500071528415041180c90984c0c040e070045002d006002e60800360b40c034104058050710744110f4055445034100b0058540c02d245015203c40c0d010341220060380c003a040300040008a100c1c03174082004584810064407024440d02000e031407944003000025100214401041103c0d000f400c021084c15220f582e0142611000591600060740420410a46e42e8000d103100030703e00c0c800c0b42c1d130712158031040d030300542c3d2601c009000034030004900e804103007400030610500e00b40d5511101501d1210a4640c201d0303025905500c14180007920000c0f02e0708445603544202802168140d403440712144c02c0001d2007001d0140030700880c0007202d0411076900d9031060068036000a040003148a900c040c0360003560a051410510f0906c059003190300703040802a408146 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 714754451 1250 714753201 714753203
    0x2361c0b0622052d1503010507230717070b010b03070f031a030a080301140411040b030a1b020726070501050c1002040f03110307080d050f0f031509070801080703 71
    0x549039440303003031440c44071362180a80b040c4051418081d41d80d142c10007000c54840c844c038000c2c484102e485603082c50708850b8203e4403400090362440c06ca200b591742550348a040c62920103810b83c2010204d859661040c40da5214120304d01c1c00c0059400f003004142c2e40300d5801010004405401d500e01504040d00c0d100d640000141015a41c000c080f0702501030012400c03201b03401070704540c4000f005141100c0650700078003404141c0343d0a00005413103842c25025011a0708158a03825040c6460810710b404190800b4286407411500ea074565071000b090310048043c003405681c01003650340e01d80a4007020041e4826910f940356241c6078485c0d207824000080c1101110020700e0600e0380c0e8144890101c1c20036503003580c0100050f0000400044a010710302548059038000d2828040000c0c05004041d0b0b65821403081240f00e070014a409406071f4040d002600b401000580d181d8580107144a9025040e40b040b00c0085c00100c00081441030703401d2854015a01c140740341069850340d410a0085e03541c13104c0ca440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 714755701 1250 714754451 714754519
    0x1f180b01090c0212032e03020607030e030a020310020a0e09040f081c050a0c080705030f0115090b0c06040b160801030609030306081b090a02361c0b06 66
    0x8210320801192070381341c22040d0550344909020350150805c0b1251881e03001451002c0c42c81600d40192004280120382e80100b6203480c00c0115601601c0b50130907003ea1035414080e012581300582c400340148004452040d2006a80f44292030000d131108001d8030f00b00f4050310980081200084200711100d02d41500b10240340d40f62070310f80843c50118420b03021f41803c03c9081c441801140c90850304048180313841a01e07a00d80950341c50030101c807507000403101c4140c0d20800b1303001004035140004e80801000040e2074040011502c1341a41c0c4001d61240755454000e502c00c0082105026000c81e003160009201028201c03640f4028400409104040c00041e180940e1918107100701402540075000400042c0281d40d02c2c4a11400e11914403102d00001c0c500540d071a800050600724140300f01c0740c2c0c0100100c0350041c0d00d0600341d80181801010300403442e20071190151006185e494011082d25020010041030400042e450040c0880c00060407090003600c803140d00e0704a2072a181c03100c080301d04e000d507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 714756951 1250 714755701 714755711
    0xe2d010c0c0b13020d15050a02190c08040f0f080601080706020a0305030a140c0306030d09081518061303031118011206030c150912030806060c030c1f180b0109 70
    0x1c42c0f64000100c0f03141c0082d0b012448031020002c100d550040e10342c40642c00b003000c01865070381030b0b000005c3e4440d01d420200c41a90400d5520415030154043c8041140a9000b281c209600c4041c16004003101d50400c030048842201e0400c00c5100030440a4054104400500511b41c034101001c0c2d590202140010103100c408000203180e10580d6100014250502e00e03a07092a080441040310554410b4075454002d01404540c2d140076409030501008a85a0f0b40042410a00c0a40d8403207942c003014140b40640c01c45041041c002180412006c1c0c0030b0302c000300307040700400035501d00541100d00303440360782c031120b1014420350b0001758001c10754440c10002800c0c1500001c50042d403d100070115034000804480904101203200d540005c54000d02000e65115400b0190b201c41042c00708900c0940f00800060b4441c00080150500102400035804035404480c1440301541e0b4840c1460340c241514910081d665815a0880b410350140307035410300302040003101c0c0c90000d413183c564080c030500800c44595154 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 714758201 1250 714756951 714756961
    0x181103031306121803050403030e010806100c1403041e080a080f2b0b120a0803130f0b070c0b0708190b0d0218010302090618190e2d010c0c0b 62
    0x1503001480f50000c08078600401544c81e00d0041c059030410300054000840c400100300c1c81d075014400041c06035000030324a28100d001c100e0211580407042208507000a8016400714100004202900c040c2c0000992540d02c204601c00310403030020580c1c031a102c00e91004110402050483c1d0455042c04040d81101c2d40d20100018405109115606800302e44c4801e180703107100d14840c0d54850300104004880c040000304003058001c0e645d0a1200740605030f1203040002c140074214040d00b914030710740300310216101d5107410b4807034010340102203e004c800300714560071000400401c03030041a401401418502000c0c180740d0010410200c550030b0030030b0303c5130791007041403142c2c0e445171b04040d1105d81c014101606030121f1440c0c855a54420321040b4010711000c5c000c94000d1414604021500c60721509060f42d903560880c0d12100c005100105183c203503580e9064401e502000e010381004000d400e2a00040742e01c000b040c0c25000c0600381d80c02d202d9031740f50941002055038000e44645015811501c00d40558540c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 714759451 1250 714758201 714758237
    0x3190c02060f070b010906050d021c1a0108060405010c08150108040201031d0a02100c0807030309021503040819140f03090f07120b07020109170a12181103031306 71
    0x80c2d41803030114000041941020080003003460b5040e104a607000b884620382d1641030000c0d01c030110900945c0404172420107031400b044550b404100c2030040104e00c1c0442c001210045800400380c10141c51504203d041100b8040c00740107070000110a0328100340a0324140100d401001480c01005041120410108055a11a81240700310800054498100040581e50309a03a605203000132405102e204003083c030480c2c02220551050b60300208800c1c42c207100d66500714000c0c0420030040b039100318110400c0c0c403031600c042c001d5849288122419695810303400700d50b41b48d50f171040519000300242c1b0460201c0c41c440b8002601c81100b120b049154680e100d0404107414443c4201040310b0a220b4441c0c000f880e40c41035014540b482d400b805002d442c3c0c0c3c4806a08134240c80400b40094040800184424404160580103081140862030901d803a070310640c84803400e5400705842400c1048080c082c8200f03000c0e4070392014010714411070055141010002860b28054218420f240910400101030340030344038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 714760701 1250 714759451 714759457
    0x2090c0a0201150f0f050a0b090907051201060e180c0f0a0c12050301050109090209030601061b0c0e0a0f331505040f06020a05070b0a0909180201030b0303190c0206 72
    0x105080f003003448180c0702c40440508000c0c41c40380f0003000c0101c2ca00000d0324205100e051040d10384144c03070030385000340444c1070203070002c00540003000308501007250341c50300354001700190302925440e5145d003944100c9001b003188000804105516042c8140144124584400c0813100d030b0790b1030031912640780d642003e015913100140c040090700e5104101d5090075040ea0040045058560980300c012805466072010012801000d00064250b409500103100150141c001c04000070309460b004000340855588500d140c14080c0c4c0481c0103072184405010640744640250b803145054140c08001035100d0030801c0b00422200f105200380010b460300601c00030710b21052090042d001c2035400c070501c1d1071085c20060465200d0310500b60203d60309240415241d10106000b440180c2140080c2032480c00d1142d07111403544000265000c0c00020080000c11440d00c0c0103c1d0800b82c0c210080c0c28040455000160984c0d03180e54000b03100c1e0700300f00302d07105040007450702840c1e01c01924a800c0ca40c80040d840811410300c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 714761951 1250 714760701 714760721
    0x1f030b06011b0f1a09210f0d0b1e0d080f0705072c06090f090c040603030908070501080c030c1614010e01140106020709150f170d050702090c0a0201 65
    0x141408400c00c0034881e852400540c42807040c640031040800801030750340001d800350b032901d56039009a2114a202c1b040040c5410620801d61090b91402c04003020068480d402900c2c50342c1d9140d00c8442c002c0c9507203012161103814148404440d4500444080014180511803100901d1288007041c401c0380308040c80142c0700c00c2c42c1d00c04115034001d500c9090400c00080507219000700392800d60082c00c000c06244040c035018441c050a01029034540080781c25806400030300c1b030031444c401ca03040e0700815519401100300071402912000d0a00c0d040ca503602c0d0415001c0d0704101d06000c826400e0200810841d001c0b43d80c0490350304542e503103500040c619003024a204030360281000b801c00c0c011010598065200b20b6010030044020410b01c1e0b5140003580c00560240b04400c05030b0055a42000130100c0c4c0c0e045040010b6242c4028844107443c0c48040b0703070304051504010034070000044403401d964010044620109518286035003401c0c0150b001a00380e8030001c0c4803030080d12010481c0200381f0300175040101e41c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 714763201 1250 714761951 714761987
    0x20d0209030102030f180c010e04020a0c0b010b041a12010303050f0f04090614040e031b150c0a110304180207150504050d0906050c0601090914030301060e01081f030b0601 75
    0x64200005084485c140a81e19540c40303081800d24000681030000340038440038010385503405801d02c104100802900480c5402c01804442c0c160700c000210780c680701070b0181c1840e40c40c00c0d84a90411150000f00c45c0000d1038001001c4040082034103a641902c1c546044075414901140e0360410046289610f0140216840c046100031401003410703401ca81000050360165421150080b030f1050800041e02c6140c0005501a0800c00c204031411802c2501a0941d072803941c00c90f00180305c60941e860602c10100c4d034008010f600496420a11342d40150507417804078141004500303140c18141c01c05035042921410742809540021020108092440d0f01d000c2c030682101c0c204424981418000d445643c0920907000042d0160070102d02c0741d006800752034a621940d0010042a801c00c00140000d0a2003442035821020340504040140c600708002c5000c2c0071559100a0080140c2e40050414080501031441e29058261750b2800d1418501c00002102d40100c10b074030040d10358400503240b000b00320106400e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 714764451 1250 714763201 714763207
    0x40203190528060e0c130e0a05030c0319080408040e1008030703270b0405060c030702030f01060501170603060f101505121021030e0603090c030708011a04020d0209030102 75
    0x9696020a02e01c01c0003800303480705000280f4181d0345651034a6070b5016103076204a02005600142c8417960081842003141030807580d1007400782e190b5510b1a00130351901c2d0300f182d0000075403440c00c9080c01d09203c04038031103040984860400e951180343e2800745005421118045400062284e0b000340d08500040030038100762a91401c107414018003001c5141401c03541ca00b0181485a6001c503000e00c640200c4649041c0141003c1c24101080903035800b000d00344143d884280102130145c0e4051200310b418248500c00081c44c0391401c0000b60540020a071071401c6124039404014140d02c010a002c1d5004410f00070000302c50f56002e00c9207806002e25000f4076808c0341050a0304403490b4020f0010884815a048815255a10b003034660030140d6690250a801c51810308038480c00702414000108414801d041c0300710510340781c00110708150011903540c45c1300d9100340c0b210901c40c201400103502508005009200005120108040580700f04000d1400360b81e001581d00c2c1000e503242d041d0780981c0c1d8014003d6603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 714765701 1250 714764451 714764503
    0x8041e0b04030212090625020a1701051537080102070b0606040303021c1b0602281d0f0402070b180a0b0103030f05070c0e0702010b090402031905 64
    0xc4020200c0d0120054410421102d40b802c0400080d00c0030b0b11030040409181c400d040c400e40002880d401039134805540e0003801c0000503030701e551001c006008249580768654000702c00840c00e440001e0040c0c001441c5840700c801d032640300c40103000200032000c860b52020786208104002c450300c0c40805100107124205020a1400d81900100b2110b4020041c2c1c084a40b58101002824481e610000b07000d41d000c8441048490b5400240700520040c90a0803c0072549188488070200c618201c1222180d5002445501803104101c0702c000c80510401d00c0c84402c1c0f0301030b5000e00403180340c1300c00364080780c0c1141084556555469604111110152083d51244090320303181e00d9802094460010700c51040d1515062080f00284801405410004038001d6074a5a2001e0f203224101078000800c1000802c40700000c40c0c00700070711400038440a441504185404e0000a003150204071909101c4c10400c002d11016903000500b030407040d40d01a0004540c288149825032421914010400d8548030f0465400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 714766951 1250 714765701 714765713
    0x28020615120f011d0105090c22110403020909010209011710031a101e090209010c05033c03010311041d0f0c0627041e1a060f030708041e 60
    0x14500e045940c0c1c12513583d80c00d442c5070a080e81c504403443c540c2984540a4000309190880490003840040d540c3c1c90300c101071195030303031040d42d56901440d00070f0f0b00700003420011802c0003042d00d9400700c0203500031420588030400003040d2940c01b000c0034280c42e02c1c0b0004604015145024031006550011500c030140e01280c5201045580c1204c1d44000031011003070002d0400035040030143c071189148140825075040142e001e000350460b0304628100107210384a0f0001a10405c001c091243c039078501c9040003451003076048881100303030040d90040780d0307151a800d0088101100b0b48ac1507a90000075540020300b140003003001032100456040300c508185800d240805000305001010584503000d83d03000c040c0c00ca051020a10400410f004410480b407100008004054075410059200a0001c03c0940402da150059859030500b45048107036600d47d5600c081c1d10810200980030002e80b000f81c2005154401081d07a030000400311010f210304840001d081240d05c2041000c058a050403403110040e640c1850 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 714768201 1250 714766951 714766961
    0xe0a1b05030a140c060405090a09260c0d02070506041a130e090601080105070f0807111b0a050d0f081b030304080d1d0613170a030228020615120f01 65
    0x40c90140100c1a0061007403c1c03940840741a80c030301608e18845e82d160000c02ea00207120380c2e0000e036075108080c501c00500020300780c1c600400c9051500080d840b0301c0c4900020742080c5410070100309652201c41c0410154495400307a50071a003090b0104050019500b030941d500b40306401c2041510940785001252600182d08090f01400060007101c1040c0c0e04c4044450880b00700361070040121300743822040c4074050703c1004095440714052520b0030f51101440354071460034400f401000d06e1004000051003260815465410040c02d00302e42754401480c1545070800003111079a0050f05c0007400048400214984a003201d003510b0b0f000e01108e95030300c2c060500b0072003a0001b400650300c05003000c2200c498104290100d0564506120290a1039110b5903048210b41111030002c45015082c18070040d48650341101520300402c10782c0340940c0d2882c108007003242815004400349070440450203200200e503400a18198000c0c0783e0b1710304003004401140040d582e0201142107000a1048001c0d40f00140819084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 714769451 1250 714768201 714768233
    0x120f0915090609080c1309020103091a01080f191b031208040c0501030912030f1103040c14030f070501050a0e040c12110406080a0504030e0316050a090e0a1b05030a 72
    0x1501e40c01c41d4444c03c115880f0b079203586140d03071b1003c008035000e031000005a101c49065441410002010103103942d0355900f020344050800c0e800c81010004101f0404203204400b0010f40c014080e1102030180c10800b000c0f00c185440c003410300d40841058031840000a09240051900300740d8502d00d4110420b0010b01801084038121003c14402d000011194001d000b8605600da07c40e005949d050170f100b0048006103442402c000540d5128281f0340c0000250000031802079004140c0350303074494241446401c0820220140e1130181c0e002100002c2100030201e401c02c01d940003440c03c070784d6407135143c2011100f000000c01c5080d8840d1601600b001ea66030825016580c584941c05c003440b03250101c282c42102c80c0943d10034900443d10010004000039136661101da8424824101401e105d145d04010030700d0681c4048202001100c04141130000d0710786407002e0001010500401e01000030041c002075142d0002020003040ea41020581e001c41c000701c41400d1014110180454080100d40e06207001c2c11440840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 714770701 1250 714769451 714769457
    0x109020a030c090803180a0f03050109020f1008181204170609120f0d0213080714030601050a050112090b1006091a0a120209031515040603120f09150906 67
    0x6040c40e00d41e030081e031005040364036013405036041450003817160054000790300300540d2008011002160f034200703600b48140510301500002598403014414051205001c4860601c546100181e00203210780c440e0805510034145210300003000402c4c420b003880e02034801c8040c2c030400000300e0041890b980d802c4c13a070864079600307200f01d40c03090b00c501c05003585403200c12007461104902045040c0c0348140c010000c05001591010051030003820f496032030588407c6811100d481c0c1c103c1c0b82d0420005461700c0c10381c0c1440c401240503100301d5241c180040d041b001c0394451141844155560601d0340754080e40a0021540c00810040503031515045d43c50180185004030008210020008240303d00701d4140000d403800091002c2f454803d00a000703032111920f03402203c3c18039400b00310440407500d090000d811100305110819034242031004002c0511a54a00118007440c0380040c2080414400c800300c66000946041c0100c50717140541d400c0700c03407074905e03007240301303403486590a11608551004080e4210f0300b05523 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 714771951 1250 714770701 714770711
    0x5030f0901030b12031b0f010c0206011d13020d06090b010311030d0903260c010603031701050904020109140f0d11091b0f0d020712030608060109111209070e0109020a03 74
    0x8000c00015054250004c10035034814005c4816903240f8298082c9190002000c0740c1e48030f106911070900b5564490341a00050300040010803144400e40040d4240c101c04c070640e4480c43c80e04d17070122200030f0305102001e882040184803410611800368425601650441d0451001c6e40c1c60b070801c4c900d400300700007002d80079119084940c4a0584941240d0043d2580540a01c1da002c86000e141c1c10281c4c0079030412500c444081003d0000301d00e00340300380c200640c0301c1d44401d0b031490b04607070103801c2e0f0240590065003d007070624100030050382c1c020003900941c0c020039400c1441c0303280100411a240800c10107660488441c5105038103000d000540d100d130b042011a49600d25981c0c0084c0c0c9075039a41040f4020f89141c10903c14029642e0070306c80500700b200d00c4039800508041094407001240305d400c3c0d24540100e5980c003400c0c40100c03020311016000d0000c1d000240020441800e030700d41240b04400c101c0030711031203000105046103c140095401030003014500d120558569100a0080d48000310b41c0b800700c0e24007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 714773201 1250 714771951 714771971
    0x1a03060c130314070806090c041515030c1103070c051201090b150315010909030905010503011a1803010e060a0b090f04030807140a0306050301060e040b040807050a05030f090103 78
    0x56421506000d81144400d110700b441c41d555003110803107040440320b10303011301240412101c0d0104100c41c030420300c0e4002044c0c4824102c0034030088031603030180c400c00f07d500b0110034480b060070100540b5007448d00745070008a046900c0021582000d10703620307008450100290b20024002d0405200060394011a201015032040341220f03802c035113074031308010030190050300050083c86001030742416010002d0300f911060100a0280e400c1e9410980211030221364501c1c0d07401c24140d0002088010f1719003800d0661843d4108121100090000300b210f16041900156114005002501026520101a0081c41010311080c503040d2240d4040b83c612800e10300e000341c010340c90b2400540709800380d0030742804c048284e100c64508039503400c0000e094400b44695501e02100c0b45514100170082080c2d00d030380c001045030500040600b940d04a501a003106203a200074440880e24541189410030303808507006a503000700f0714085082a040081c003a001c1e0001007084a09104100020304060600341d8041040002c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 714774451 1250 714773201 714773221
    0x120e070b09131401030308130218040317040305030a020913060906031a1504091a280b0f010f090b0403060204092307050d060308190219151e1a0306 65
    0x1503d56125400301c04001040407900031070074190004c40701c0c6c450106070041500483c44403440d000391544100c1c0c0b820304102c2855400a005c5e91412140ca86105032410251001041800058900d40000d82e00040098643d0b59a9107616031000030741800b4080c840d41c849104004184610054842d01070014038941c02a4101c1000c07480380c0340c00e8081405030740c04441404001d20344284100c0e0420500f0800041101c191007281348500c0c0e040c0c41602e2448071100010301103c0390b07030140c002c1c1d190412a06803a01c0c1d03074030741c80c04200304c0c0d083c42c2000c1010004041154214280e80c01064241030029010003888611b800402c2030310b68a41c01404012407404651030685943e8451150240c0d941e004242d64910910040082840441011403916220340710b598169001508041c200303410140c0360300805030103121140003c503000c88100c00103001d989400c042c0000da50a141c81160703562403119010101d6841c03c000ea0000c4103000c00c428200700c3c0c200c0031596074003031030540f080c0709480c000f0386070b042c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 714775701 1250 714774451 714774461
    0x606030501120c0608150414010302010f050a080c0c031207050a0e0913110a150c05010c0c0201050703030c1e022401050a0e0a020409020c0a061b0f120e070b0913 71
    0x1c0c3c840c4100d12281d1a000c1c0403203409030007900862a4000d0030110b42000d42d1b0320b0081c040c4804008813a60640c1d49144005800710032142500c809000062154446683c0c1080113983d0246e0801141561180c400202a017144184a141d404881d5450f00344080e4541c880094810505c0d035440744200f0210300002c001110804480559440440071640c1e00091030009000c0014200601007220b101c0c0c039050750000300f2002103603581c00155400710703034401d01109004140b41001c640c1407110800580d0380000340188109400a018191a8201c0098a501c14004d811401600c104c6a180029a00b036009495100e9460b0241303a400b40d140482c0b00030600d002c8a14100c3c0c1c070080182401c01d2902c901c440d80d146000b0074a00c4900d03402e12002610710080d000420400d0074400280050761070500c4c3c50001c4800e05048903494101d608214171084c0d0b044410f0b0300c030564160801e414002c40706044a00a0701c0021902112402110400035905071040003402014800311108580e00741c96280c20f6080754 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 714776951 1250 714775701 714775703
    0x204180b10030c15090504021917010803030105060c0304091b02010c0801060504090905070302030d0e180c09010305040f1a1512030f2a060f0112030206180a15060603050112 76
    0x401100e00801c04041007240d613107a01600d9080c2031070080d03680c0c4002012600603c18800c00c4d10803c010038060b441d80650461642103062019802d0740d414103140c550350b4041400ba00d8004c40700040c00c10340604040040d200107207038008040c4516040f000c07000602a42c1e03084903401540c28140c40216090003000303807038140c0311980d441ca07040c03502e85590f91000c3c1801c004107031141c3c003841a0210158805000780f4010345100c1d2a403c0b84405d110040c800840d0701002d11781170381c5508006004403078034218103d5203002024a00410192070318148807442e180b281c40c3c020180402503900028001240c00c40611581440d2044114010010184050400d240074580703034075041080040740448445002d440280c0400180c0c00342c5a00d02d0200c44440c110712001e8000c90b40c060410009200402900c071070240c440580d54070203120043e43e0207956184050040c013207141e0000c03c4204c0b00c3ca03080280da86407980041a5503491485e8540000080c210b80c054000040d00389400820b6410056030304410761 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 714778201 1250 714776951 714776963
    0xa02090907140c100e070807060206070804140312070306050f0607200607050106050307062a0501020c03130504050603060c0d0c030204030f0b0a27020f0303070204180b1003 76
    0x40d999401c007180c00c10b00004100c50901401d000742c260920082110b44006004075070300040800c2c6031215907241c03151983c000c507902d60100d40244040c55020a00c66000205800c140840b9283c41c03401c04c05040040700b28151500c00404c4038002032190850003802900540c5003080019100d8050001140e044000300d0b4020702c2c20015070001400c030340c0c0d0040a010031102030440c82018040020740750340c05203000fa0f8050703440d41c02c01e2280d40390038025000100414244100080503209800c001030f1500c10a0f40030015207440c0050500c0b50a404074ad19480b641d0701501d03592705491654010880540c0245402145007200140312401d0005d4081d00444c0c240710450f0074246184041e03030150000c00703003070410150280400030014610a9540d50068070802c0c00c1c004500d020b6012000303d4030001d11455600748883c1d084880c170850031002e00c004a4056a1090664400002107491445021030080d00306207445040c2c58203084909140c1102403081d001c190700c980700c04015042c0580940405025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 714779451 1250 714778201 714778219
    0x1140a120605031908070809150403060501080d080a0207060b03100e01140417071a012c0412111f0b10050705151f03033219180603060e0a0209 63
    0x7084461000d0610913228074075903440c04890710041481d07820008270703201c4038036804981401040498000c2d58050301a5100610b02d04602403001090740308060038102d4060342c00101001444240e410071844104040c048900706100a001c40f001400050241d10396546000d15030450310b82d11914150003143c1000214462510803952072105070711185c41140da4400e040b03090465640c0003400180201046048140c3c454481002016840c6900c040a07403070303880a0003004005a0b2190001c404040b56103030071080c00794020029072605180500c50304403040c603035150108d010381d96000140c04210a59940080c00800c00c400c2e1568011024001c0241d04071040390484204402a103030341c071100780c00f6000030041d40d032901d401c030203120b0350000c0c3d0001d02c1111402c607098071294070007074103140c400800e11a55109c12041c4c90a07800780f80c100e800415480851400e01300d200310428208540c6068010103219070340c0102800801c0140b2901080200c00c00000310050940e20a40e00f80075000741032205 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 714780701 1250 714779451 714779453
    0xd0e0103060308031b19080a06060c050a031112030a0603030e090c030a09061d010c020105070f080408090303040b120403020111030606030604200a11150115050901140a1206050319 79
    0x905c01640e0f00500e40c210014045200086480a42c0c1c4002ca03055844803840d50500190368021303942c05d170b00401c0501c0b11914001c4000b410001d40c251803182c041c9491803034100c100c2801c90901d46c0101500e1074001010061010403143c0f40e0014086030b1082c0c40e480c070004800c20910040c0301c0110f48040007400284006584045160004000c3c00c1c86808001686c80c02000c0c0b20300c3d0126075000d0080785179514008001d4854091092507004400c9061603500e80354161802496004010b0000748031140104680070b1548041090301c01405400100365110b00002020201d460750071241030b001076080240150403c445182101e004410190101d03145668401c00d0201925031043c900040d01038010f04100750800201c0130b4920b0100a42d54000551110307090300b45442410b0400410002410004114200031000c00c03810451150130510785515211005882c0c1507000c1d2840f4640c030500280741c101c015030220f4950754240316035504006040d121030070300d40c0d14a28011240038a1800169041c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 714781951 1250 714780701 714780721
    0x606130b03030d050a02120f0c0d1a0306010b13060e0609061c0f020c0705040b011710150e030d11070513020c030a080414010c1d040e010e0d0e010306030803 69
    0x20140300e005011a803611511200d400115102260440d105d19030215005d00f2075031322011030642081000310b012129052501c0707445202d01c186070000c0300999807840111794688500d04258044036008040d03038803e60391a08562096170080c0160700c5680002000490f07018010b4080351f680a40161045042969440a005585e8450910b0512800d4110b02600b1904a90302801440c04801e800250700c070b050001c2058a40102500b01a00c02d030701746a00c85440c6c0c0d0f800446806042859070012000340c558803804401901103802441d56103000b50101c27000c403904140c0d0000d081405030111000c0d10680c040440d241501000001c480350003d000421003071400001403144101502001440c22041030070703003869680501e024002140100c81007006000d484a100054015444000d0191420800f401482c0744409003402c07050f210480d071460015283c60303001c85882d001c2c00000300014801101a1940e42500c1c103820341c0041c1c0180c1c007405865219008240860b540310409604640b100031140b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 714783201 1250 714781951 714781961
    0x120a0507060f1806050a020c180a0c140a052502010c15060b1b071e060507081204050109050c060a14160b010e042f040e07080a030e12060613 62
    0x80d04100301c44440d907003c00c0300d01030070b803009040903124156541100345002e07040200c0d40241d41c0c0b08140006c4d004461902244002d40e0101c0042c20000d00007009020940701000c0080c24004c8052001c250200c98031b41081c001d0220f0300364003030024168060440040c085804011000b4002243d2082c1203002460061312000c15481000b800f24802d0b403141c001d2403440d0040341c1080381d42c8114610039450030905000d0b200c06440c081c80c0105508412501c2950780030003d100c2e007010460006040002e001000c81a1140102210900303201c6007840d00300381e8042d10100308140d42c24090346901d401103180c03a50803102e9900d65903c8d4002e03540d080c20b20440075030300210f0b8031002c200c0944c0f480d00c0c0050649512180078210711282c019080c1014201084176859440e00d00c1d038200d038003400740100450504520f0164140031036000c9404c0000003103841c02c043c806d40c0440110320400ea51a0100768000b840301e6070300f030f4040e2028101021440c08540c3e45180c1620300d2034004e82e0080480c03034032000d55045 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 714784451 1250 714783201 714783227
    0x70e0403021b12031c0e03091c050a1509060f0203101202031005041a0108010603020a050f0a030c0b09010212040f15050705100515090c030a0b0d0501050106080402120a050706 77
    0xd0802072160f0f220040d402c5600030f48a0520b5041081d82c84480354255103d025407040c10180214184440300021440c035264080d00502440e158901603c10405d0400412400e20380c09044840886804665103015040241d0120b41817401c009200003000c0310792080d248500c009035403641d600d82c5005c610031006601ca100070303a00340c011145596031444140c060b0b20b01642c41001f1040790400a200d4013042640c06800c0081581d050207070070800746e0b0b64098100b05840302200c80c2c00005d4040f0001940c214440e91008003d60403109001400840500261a00005c2031302915041c03c051550350b04244980e01401d030305028490014802042603581100c540c6480c0d0600c0c6e0320704201500d036140342c00307980d50f00741e602c10b6100d0080110320086001210700740c503000d4072402c4040c02d000d41a40c2c01c42c00010305040c0e41e6070b0744200401c5a81e80b843e440703e44054009008100b070b540c440500030044030f011038040e40500071038596842040000200448030503000009440a00e040100841e001da102d0381e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 714785701 1250 714784451 714784459
    0x90b061201180506010302010908070b0a0806030c0310020d0b04050f0c090105221d0f06013f0e0d09030b0c07060c0807021605090a020d0905030a11070e0403021b 71
    0x1039100303000c40041c401d4440c0c2c41c007480090039958558800180795060359001940550420380c8200f140e04661015507680c1605410101001c4d600c840c0824035020b58845441c0d81440360008129840300e06074000d0412100e10203060107020141380910003510010349040c0c81d159030303240009010801c414040e10459078140740491502d050f051010756842c800320060000c0c5440c0300000c104245070f440c10440780c0120080000d41510300785011941030900140307482d043c07120716041c400001c19110041c0281304044d5900c1041d59440d5103003515240c11a140390390a4a141400c16100858002541b0780d0200a603a02c1c101d0f502d0840e5903890904c58060303c0960340c0803061000701c00060460203610801070140c1d41c0e40f0040d02c0d04c175100074982007004100f18030b8004618000d02440d1030f000c3c0300c140e0052440c400903948203200f0300141c0040250013405800d80c00049103403072055a00ca0940881094184111041c141d12515200c0000c0c1c0706860090150b40840c40c0a00c0441c1612009825050020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 714786951 1250 714785701 714785711
    0x7080a0f020402220f08070e04030c0605061c0c09060b0c0607140d09081804020301060c0222060b03071101050106052a070909020909121611100512060301090b061201 73
    0x409004c16811254000c4615842d00e8001444a1002001440024203124040d030b00b00d414252400380c1002c103500c82c040c100329199170000c2c60320b4441c01ea180e084086500109065030600e800d040b1020b483c140501c19031182402000038114142200b911100004200500441c4d00c072500240d4008109860740d41e4090300c2404001c4208005200d03d1010310701904030150313690100d07808140841400c030304281c8160300c1840184031084d80041d5032413801368143d600014010040310204019544806012642800c2040101d030103001c100286001d191280c03a41c600092145285600b65503003401900b00003541801044950882074a1a60744044c0b000a2580c814843c0342c42c550a18100340c11285806844005002c03c50920114a56001810b0409060a0f1309207001140c4684201c4c3d410014140560940b401448059501c05d0740e401030080c0030101ca5050400040c142d908907c001d58900074015000445c2401c0c1070081d400684d601c0401d4141c6617031510200440c2e65401259044550350311 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 714788201 1250 714786951 714786997
    0x1a0d0902031504030e151b010213080a030f1713030e10180b0306032104080615150c0706050a0c08070c033302071106160507080a0f020402 61
    0x244120050140740701c2c580c403018a45401c1c05410100c403080000e000302d0300b00c4402c2c511026008180e8100c6454408080e20105e0440600f90180c060100720031094003c644000500c5640000d00359007440c0300f41c49031060462016410703141c42c00c8082a0000242d01c840020702d20f048001110004030b80303e400d1000c04288000042000c00d02011344c040d01040c1d41211840d00b410b0808100c038020208810518514036248011a44810084d10b400038040c2001003000800c0c0008001d41c1d001d03000c0a0100e810500d41000700aa0484003074600d00d0090300042019204040001c00b203d10903051000104051380c038090b011a1142c0c4400708074400c0001c2495811300142c0341400030401e0b280103001c3d100e2100c0c01c1d400c00d05140050600640e4081044040703018100040c508444001d000c441c40040c1c0351400703802d04007110b100b0800c40c90790050000880d002e42c00ca0103c2146802070140040310b0003113403600c2805c1e035945643e61024050034212140c07034006141640041c2580740c881050300d070042c0c0d90 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 714789451 1250 714788201 714788203
    0xf080409050a0c0801080a080910030612120806010914010e0a0b0a081e0601140309010204030b0a0c0f1d06030415060b070b0f100e060a05101101060503071a0d090203 73
    0x10b482000410303840c1e80200395415449081c141c00b40124501620404070503603585820f1b407080c0c100d26806180c41c1d100e4150a50700a921080c002d20303040c0e1280800300e003541380501c10201c10240940115030010b0119805512440800059402c00e85000a44103904401595100c0440882c160300c00031144010416004910103802c001c1400c0d22405041e04000b0a51303401c5200c010070034031101404000f00720a5a81c080300881c0d912449010303840e07a0b5103039404001c1c0640300320781000e0700021603103051100b100141d03070001da2218500c0d5660a180481130b402214401d034041c0064074040c001042044c0d00340303096802980c009200d02d003501c011070440305082e4240c0301030794050645407102252100c02c0c801020381c0c0c190f0069480d041c03080e0524203c804811202d5a80c0aa17400d003e042c04005031035034907070429240c05844010440040b01100020050603003400d00e821000550821000080a00700061540e0650301c0444104614101160106071190400f40c110b000250300c0d1110340c005a18 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 714790701 1250 714789451 714789461
    0x1150509011809021c0b09010903020d0c05240a0e010507090b0a03020409090b090706020304230f030a11040f0b0d020d031803030306031e050a0201050a0c1e021503040804030f080409 80
    0xd0b417031495000090942c104841c005800074100a81a4181020070700082e5001c0740c012104012424080000c074003d08005281c03c03c41b81d0300c00b0640803001041c08103000b0003d21113100f03030701e0300074140640201080c0c040c1c2030f50801e44844022030031031b81042c00444084805841c4c0b034500d5290041c01e140e51644100103480c0c010300141c4d0751120704d4080c8000d00000340000c0b0041c10941c0000e620306450b02d03030f9450000103200820000004400180111507403104020340d00c00c80003c0c100d552800e0a03051664100e1240049140324901e480414a20401c081c05004001c8000400c000011800c680a1228030801c0250840410101d414243c001c2085541c40b01e0280d4000d5030001001400d40c64a1418030b07540ca4140340364551600d0f04440007680c0054074280c60307a82840d01e10b46410038100103480d140e92200005006480540f030120148032500018440f6500031250901846800361214a00780703c103440180c5010000c010900218030781e000211540382c403031080d4501c4c00350744914000c00c8403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 714791951 1250 714790701 714790729
    0xe1902040b0a0e19180f0e06010f081b0d0f150906141909111507060f090c090c02031c14150d03081003170a020115050901180902 57
    0x2181c0800c500b0b2160354804003e01d12080252190b08040030119080c00f41c1150500c5164000c074545c440000212440340c1059101e0044c034102804152130300e0b010f46460b06000d020700c5103003580100700004c140c103000840005c8521513080ca0700e404107111090000c07a0096800507280e5469004030070380007030340080340d418005920000010f107118007441c4c200c0548121451103119041c281c0c060143e408003801c050345c0d60800c062000240d03c586860301d001002d80d03c0203011b92040d00607484000700018000200038140c0300307a6040140ca4001c0058074102c0700c0e2000040c22410304054103001900c096440b0305c1448030540100d0341041000a481410f04468141c64a05aa21080c5074103d1065015070107402c9001102e080318031004407000300703c840070385007005810400b01402241024440c40b511a001e16004000c0098240d00c000d1007885660154649000540c603160100300d8038041e540c40d003070a46000900d00da4160340f070700000d26410045401100c1d4415a10054840180d8580500ca1208 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 714793201 1250 714791951 714791969
    0x2010f1d04270c170607082409070c0606350118062a0819060807120b07090b160203030909090d02010c0e03030306090702100507080a0f0c090e190204 66
    0x1c3c03824100350b45507101800503020840c2c1c0c403960611002513000014140d104091030540380b0032002d4190901d2540080900741c83d00180441c0501c00d050354088a42d05140780250010f2012039074031900e2002000c1c4030054214410148010295038a0905580d070201c02030200011403001400c500524401c3c00b5a6011901c5641d00d1007409404403d00465002c1c0e202c1b0020360300b0100118601c00342c5070400040580c204014840711001c0840c2c03841d804400030340448003c1f138500b15202e0b000c4103c00820540195406020301000a40d580c0c8100d00390000c6d294034012450902240c0104400000008035003207074180000c0c441c403919502c80c046803521541c0711000900000a004030f001e421a0003072000c1d002000002e501c07180b42c40c0c50020841e50002010344102e50316598500f0200d04091101c02e00d100101d0800040c0f02c140c940c0140c159000c2c9200410400c640c0884d243e5001c100c901c410f00103004292031040c20011007203846c1c0c0700c0303500501c4032000901d00c181a01c0300d00201e07072050300a070003d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 714794451 1250 714793201 714793223
    0xc0305010c120b27060a080613031e0e0405100510030b0906270c160803040204110a0c12020f0a03020f0c0406030f0f020303091c02010f1d0427 63
    0xc0c90300c24002c181007182c0541d0810341d0804d510118064a640a41c1c400c4195107240000c0307032450b100d81341040d000b005d040f0300741c460340c0c00c00320401000042218003d8002800c07400d82d21880c0c0c0d158140805200c00b0640b136000390600c9000500000e050010003a81c0d200d060761900040c45d80703c0340e07043e98540c9000d550014005500404001d00ba28016020b03500400340704184928024840880040c0071105101c241040d076188a46404940300c2d01c00b00a81100d10000c405080160b64000766001f41d208903030502c25206005c1c3c094409004162001001030419400180440e20841c1403413404015441602c0c003122021084a181811840c07085005a00c05c2c2e81014918100307100c9000c80c0201100c0a1202c00e20f1502c56569801c40d03180d000c0d168601c5812024215034080013141c031003120286c030707810340e0f01c5518250b03061401c410f903016408500603500d1010100d01c0f88a50340001030a00c00e4030f0b410f14040300b0a01001701041c00c1120300300c05e404040342500c8104006c00004c290300c10314540c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 714795701 1250 714794451 714794477
    0x19060b0a17010609030620040e0a0f0c201e0703031b03140c100908031e04020616030c080c1608030903072106090803240a0608040c0305010c 62
    0x803070300014034040c82107030000c0c006110496002c40705100301c0303030051000b0690300c0c820b40102480d1141c290000b0b002d20b8001400203004806659020b00c510a1004100885d8103455622010f0b00d490b01211000180741a0501800d540410f91074900325049008540d402005810000100d40d021a41c80100740e025400c20810180d0024070071400550b842d010348080d02141e030300a081c0041c1054480b04d400c201103030308080b1140800804821890054003404150218280892942c1c416204168408400121400c01002c0102403901441d809004181341054030f0040d030800d0304c1d65800840821508940030380104060001410040302540007410388a40004d00c0801240b05030361042840e508180000c1280d60741c04604a41101e0304240411104403e41e40b08603903a0402c10341c02010b2915044401042c0003044000c2c52155101e2943e40461185400100200038031105000b0350092000c0700a0000501c200305454105204450791000651039503a084d00707580d42c04c0b00040006001c504941 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 714796951 1250 714795701 714795707
    0x902131505040e070501050f0c10060302011403061e04090b0c0415110d0f030204080a03030e0c01031808070f02030312090d1d090408160305040905090f1519060b0a 72
    0xc00c030490b800c01c00d10301a01c40340ca4580c0400e00c17550303040c010041041809510040202c940400300382007500c098841c07040080008003940c1c0003e0780010803400c8a000041151070450f07015040041c11004c00302845100000c42202c500b0081e60860340302c86459001600c60442c4901a03044250aa030b02e0307a0502502c6070800785010700040420441000c6c03103125210200b0146102440c0385011100170802c50429406403159502005142c4600030740341050645c554404409d48840038207071421070004600443c29604000750341c1c0c0209000d02813040000e01100014080d40344a120080c00049087d00060b0841c0c106c29503036040d28480901700198004140b040c0840d02505080406900100c8940d281217001440012802051304902140900924105640318a00100d056600007182031500400c980c10a00c1070300d40c02420f00012030031024020445403411014007004003075504884803041c0a00c00040d01d00c106c101c0032080d907984003203214050396000d4400340b04120b58841c10b0380001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 714798201 1250 714796951 714796991
    0x7021003050f0a020d060b2208010506031b04180b070305090d0c061808030106030b03060105030f0312041b0e0403020d0804050615040f020301080a0c09110a050d090213 74
    0x420035281200300003402da000c000340c40e0421440a40140c4525410400000410854000b0103c0c4840480e950402c00300010000c045284162803a150a42c0e455110070700362901502c08640c15045100b051020002d90340d50b00070460030040021511100074051032030141c0003c0c000b5110b0320580420003000e2905802180e1308000c440b80240041040010024401a10303110002c18054503240700000c001c0c070713240c1020310507600440501d0362569540d0020f4002c001a500c2c10b400380c020900009036038580454030964041149004e54601214007406074103127100140f0845070480c08107082041c100070382c030422024051000d89141203007468280a460550004020b0003000462010000052004203465401544400070303d0302e98900e440018015060040c00c0d0101d0b144044000900018001220300943d40680c0d071030800580c0320110942aa07180580c04800d5a00800452a0340ea1258004050310f407500030000881c10000d5000500901025a00156203034a90080c00c183d1502c1d1030007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 714799451 1250 714798201 714798229
    0x3212a080f031608130825140105150a030b1618060207060311191d031510081b09150303070f02091303090b07080c060c1c020301060c0f020f04110702 66
    0x78261a1701816540d1441c4c1c3d101d1500784400742c812210240c0e076200302182007154040e9001a480c9040340924a5050007072008a81e110b071140507079206a4100d050240c01081a00e07005001042c00c4c3d52800c0003120201e613201401d10400200081600b101303802c078020701c0301501c5281d024108807444c044000301070312801c0b041203078269801c00c041941038aa440d07070601c81c4181e900f4059180d42400d000250410040425141c040c0103084148002c0100502e5480c0701e00b6911780004900e07a124041e4541e04ca4800e035945103c1ca000414402c10b43c41e0030f51405a00044074070900e01804040750109003180c01c401c8084034820340322190071045241540301103510101d0101000305225460714020000030b62485010740395440000c60100740700d0440120750705c10104030f0407039000e4289241c07481e15a44c004070030f01e400011a40c074140c8041c030f80c40c0200d90403a09181d50b912a90b6580342c46400f41c00d24100001c0b40e018509410021254569001e903100e5504140c00700b1752900203600504c4101e801c8101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 714800701 1250 714799451 714799471
    0x7081509010b090114130b04290412050c0d230d09140d02040212070806010c0b011419080d021504020904080c0a0203030403212a080f031608 62
    0x2005002c0e644001c01960b41101e000d10b01074002121181c0c1e02c1045100b0180c0380e51328034441e01008510181d410008104407041e501a40700c0d000002041e603040240400030260323100504000c00c2018504403d580100c0d00d00900c25950003082803800280400c0200750300300d80c0e015507031203514410415400060107140c81c400250a0050424000411603202401030074000151205103c84070307210f4181c481089d540c00f400440d5540310b20b0500c6c020fa41405c84042000442001c00070322194411900c01c201241e10040c04003042e4200551002030070100c4c807249800080d010401c04204001c480340100805c03000c80501041480990f00a04184c4940c01e251003280c0b80105200040e21102c03016644650052015a00c54014402c01c5080c001e020348043d500d4400840c0100503c030400e00540c800045044500680c0351600344259405880301d83c9000c0381030500c02c001c880d900c1610a802000a00c030760003541c5006d450115104803a08291040444011451441030801d44c1040400b0780040c4514 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 714801951 1250 714800701 714800719
    0x11b0c11011716020c040905010b100c020a06030507020f10150f0e01090e0a0c0806071706030c0402030613090f03090e09120a0306231e030a0204050601020c09070815 73
    0x1003042c00d9540098450341d05414141c100001407032091004d0b9048100040040c07090901600b0041d0280c40d100c01707214800c0102050100c0c03294040d02c0d110b1182540640f001c40b80070f180c01002e8000b000020001000c1d4012035000c510140c1041c0800302c0348500008001525406c0e400001c0917080581d00300c00e52070610400e05000364070019424030304452410a001c24030310340001410f030070110ba4a500900040e040c150100713a23020b01250161085629030340c0c04030907035807075405080041025514903070181c0184075800010f040c20740055500c40c90180c05134000c900102c012004940d001c801c296a000e9214603035000b0503074040c149100400c10213140c80d0960500f03070031450310b81c0d040c0544850f0302c5600141c1c02050724080c0c4c2001c4014210800d2041460800e214124440c1d40b40320001c03031144010340c80513003483c1103d880c180400c4d6000340041c400074486509100c01440301a00c024158801c2400c0c961a566550700da280c841da8403960b41d0382103410018401c07602590209141480b4020703003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 714803201 1250 714801951 714801977
    0x90a11010e06030a0608280f0c1e06080a0216020d11031005040b0a020909010b0a0306170d12061508101203050a0201141509040c05120d1112090d05011b0c1101 70
    0x392407110b4103070b0300104804010f8602d450001d10b11191684002481c101c100d452070aca4581440c180f40449070584c5811209545207034841c2d00704c5c0300d108180f18030078100b0122900036060811161a441e4880c5880010781c1e5454030000f890150304c0010352100c682c13030340d040004004c204910140c21200e000b405504210713000d00090120301c01401004605500820305003002c034442c0d0800f03001033050031300320004460604403135a00d590f0f0000305080407408025000058807070502c100300841d0085e550005003000000c2742206d140301d002c0c2c0802d180760303102c00000c1444c50108c40c0f0403200c07c1c802d40303a90303944030b00d00b19000e03003984c1a05246020b420140300802c080102c0503074800d085101d0448030755450b40d03601d140000001c682c41d00503e400004016000344450300c0041e0482140d80306442c5d0886086448806a9440b03282043c04842e41c0c00c180603003885030520810101580d0b10550010505400007580c8416500e861701038071001440c03035001042032100ea07a032104081036080c070303103920241c3c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 714804451 1250 714803201 714803263
    0x9020d1a0319080f0301030308011d10050f01021f05010302210303040f1406070206010501110c030304171f020405090702010c0f0e01030e0601090204030302070608090a11010e06030a0608 82
    0x1e0300b1000039001a480d94100c108100a0f007211603188401d1145900d9584a08004003120024040d403800503140c06442019008144042c1e4880c0e8008240300e55118100428080055100d80300e5a055200340c0000030510303a1000c400e06071030b01241c0800a09903145004004803090454140081809a0482120002004000c403507206410103441642000d06151101ca087d540020741c44060040c02d0510142a5011420324100c49090b40c03080880d403d950499625552654030040e41a44100300c10003500e80281c1d981e40244480c0001e884c0b00481c46d1075270310f101c45030800d91104240d40c0020203129611308050402d402c5402032008000098407014007801c0d0340c60403480a824017405a03003062941c0e02ca50440200f403200402522201e5031350b40080d101940185c00100c015014031070b40498098841c40c0700d40d20078441100101208841134880400d40604080076504011a0105247c20764440f5030045020300f4100703200107005442c1c080a01e00701101c8070b0344d401440c0407010400d40c12480c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 714805701 1250 714804451 714804463
    0x1212041509061d061b0607110c1801050d0218090102130608040b2413020c070501030c08040b04080f180a0506090d1506090c170f0103241509020d1a03 66
    0x9090341c1d90f0756a19401070060b035150f0a00400034045c0c2c81802c04014806034490000f1403000080411540d040600b40104280701d51000d9040d5010400ba40040080d86822803031602a64005052242c00074001995400b403920210381404007a0340008114585050080c81103004101034034203007100b400d20303944603100c0720740142c250803103c007503845a11000818482c2803008110000c0ca044c5607000c1c6034600360040c0d003250704116054010f440d00011154000d01503045461720a9548501c6542c6541d5603105891000d00b0a40b04c94134188440503e04010400030903a10104c00c0414500c0d100400400000080b181c128034056071003800648450f4844140d10521035a02950202d01554081d01d041c0050001d41d2002005504200580503465000040e2210381801c0b0b003119961640c850001300c802034030a1100501501e4280e0100702940c3c0741a85107900c503100344401242d500b40360300136001d0104070b40e081a50215800944554000c4145c4501c44690220001010342c8003c01400252602 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 714806951 1250 714805701 714805757
    0x40309081f020306130c0c0204050a0b06070b18160801050a0b0102030a4b03020301031505040f12021f05060303090d15150e0c070f02121204150906 65
    0x2a000301c0442e007245c0d5095908619054083e030304110302106103800134842881d407042640a58906401f16907511141e000e010311014000d8019881c1040e2642d40850290000b84031200d0540f035200c454458500621802c0f80845030707240380a0b005420441014210f440150032a22540d240108100d4140d8000c81900c004205a040400d0010401642c10611644002065502e10301100308a01c0032401e00241c504020300030107015058025140064080744820302000c0e04000800f500c12004400941000e0791180c400e0160b8010340500796221601248122850030142c1c01170318111035615644003103100041803800c014049401c154001c25103a20407001c9840c050170010301041d080c000720031090044e40960141c01c000340042158001c2061055002b03040059081c14046204c003000d48056807101c5030012603202c03403081c60b68200b1000301200320045400c0e000d1403081e102c0150554001d0b1008040364030016000840c8001c1c0280820352903080b00d024001c1284000d500701c501500340c50024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 714808201 1250 714806951 714807013
    0x30b0414010b0120100f0e0706170c0708071e060e15061e03030406030b01090b040608150f10050c2424060406050a090504020c0a020f150c0604030908 66
    0x130001071039200341440215241c1c000880d00300490403c0300940e50b07221038810b00d070002c1030ba08440c0c0c5801c41110309107002d580c814048440b0101094112004000400016100e12119480c08501d941d58401408400666005042540040344103000c1103014007034421001c2c0001d40f0500110040c0c07481c00a001810190052801d0310440c0102c01117094444928400181201d454503500c090060140420445050000307505440006010703c1030000d0301c2c04d65069440d41003403680c1e500b00c1c403000100000c00003036000940441c0000291640d5040b9444150250b5035541d1301d40c03000403003501c0c040c04001501c104400042c4040d84240f0342040e019085801c1f8184481c070205011500c0c0202040882855440a0000b40004203903800230024651030010f034880301c00386039444003048101d01400d00d43d110700f82c0040b07040d01e0040c644440d40001c0114001c0c030401c24021800640a1260000d1104414075400b58042c00141500aa640030040070420002e0040341c0c02c076448102628040007041100d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 714809451 1250 714808201 714808247
    0x10b0703080406093306060806010f021606030609150e06010f030e03030f0f090f030406141303050706140f04091a09070216060e03210c07030b0414010b01 68
    0x400030660000d096075600203a0f180b40428100455210217407240814880d03030340c1500035209815626014400480c0d42036100c84645550b0100107442c404903012003442140030341507550000464118a030000342c1030300e0b540018881e04100982c0200d070351182d100301d601000b14004010a9034105c0e000c1d03500580a2030910203400c5046c000b036016044428144106000c0801080941440e00100c10710825114030110b446071201c074110b0751643c0b5101e19926258004100038403815000d4924900d0301d60084940f1807500310285c1007400061020b4000312030700c2d04600c40030031019500000160b02c111550900e9840d000407481000c3c428801c51051114030b54407501034035450406691140c0c24800e0141c0260224581010300a4450b007030640070b00300300003822502180080c8904514650140050b0084c0841200e111400c050146111020304021104000f8090400c105021110046110303144040040c14030380340070010304c010314214001d182c4c0b614590045681c3d0008003400000107035448804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 714810701 1250 714809451 714809453
    0x1c020c0a0506040f020a1202030c101b0f050d050325090503160611070320030115031a0c0c0604061d010c091802210c130e0406050c03010b07030804 65
    0x20808803003010103480381c05500200f209101c481500543e2207482100d600c2c1a10f81c5034003802014540f00319020b509940044260013050401050b100c080c1110b60910040350030481c1000f00c0c558075820400c84e88402c41e4082a010004200307c41c210000b900d0519504500e0400c0c50380d0541110082c00c640b1622500d4102e001d0540107a025902400002d825201c600302603410401c080000c0b0301c81c0900040040a880d000c0d40008180c0c40261380d40083c000081403c002d0f070024001c80b40800e055819540c81204064145c00c21032010000c0d1320801419446412900042180d100f005000480041d4200b080c0303c0c4075280811003650044c0d01a9001840070303c181d480c00d01d88a80803d0708a42980b80420428421b6000344111003140d6024030f00c00111001c0100050503406001001c01d060741121908003100c0c10780450050f4000c4100108030704040442e0411110840142c2c01003560311400740c1408180451401120788c07010426699910395450b02c850852548214080602003000c08008a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 714811951 1250 714810701 714810703
    0xa030c0305040e040b061305130b15060403031707051903020715240b0a0906141c0b01110f0d0c02060c06010f081009030e0904080717040f08031c020c 66
    0x10b4054409600000c6061519241c51090303e4415583d032442040001803400004045002d40d51084440c0304290354101c000c0d0b0795090300201d02600c0e0101c039000300c15841030310f0740f00e050140c0001c6009a40c0c844c04035914400a0b00c01100c094040000c0000400c09202c40c103800070841d510500c081e140c0140e80d0442c504041a00780340440d0444461803c016105000401c25524011011180850940f900b0394a1041307096920444500c1c1011458142d010000f042c055841ca10340740148901031450408900c05002c011002e1020a000480d903402c001c0e5129640615800300304550740c4002c005480d00c00d4401c1e5500c6605016a00821410300d045104540300d030020765100580c07180c225402c95858503070441070610207025034500742c800c0310038a40d8503c041d4010b50350010f4158844031040e441c00b80510545800c000d00a4900030790412040300001e92241c0c9030100603110f10301080d11a410103c0094000f58150301c9510310f50300510101c10000c800990b405443c0b06403041c01a43c6122840e661 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 714813201 1250 714811951 714811957
    0x5130210081b2a0708010e070e040b09120304081e03060d06020a020a05030d060329010e060418051b03030403050c0f0a2417090316210905100e01020a030c0305 70
    0x340c2c1d0310f0381101801004080000e921013a507041c1e80c000c0c04482100c482d141e60b11181441100940f038111070124000c99102c0d410103400c0946502a60300c1c2d0004020003100550013920100c800007000130780c0000e80701c00005a0000d11548014041c40e5003094000600ba000003a900608015800a0080c03032260003046506c01c05075000060307a485402c0c0c0b01205000301010b12058032241c1c120044610540040440104261082c2c10807030440e9003442541c920401d0028501d40d0801d660390303c61845400c00304000ca14080c8150020988032203020a21005040314284c1d26003c0c0d0f00503c03080c00080c0e008522404528007c2ea1500051080940001d4000d11117a0242c1841e507400c04130303038180070309180c020541c2580300e1311001c078061802d0501c8034040310101e0b03850555400c14062070381c1500040003131440080c015070060384640b83d04089415812120303140440403400501080100741003822000781c59580c2803c04050603901d210010b52103084007003000b010420340b40f0481003014000d20036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 714814451 1250 714813201 714813247
    0xc050c010305061f02010e06070201231b0301120218090c22110c07050105120103060b010c1203020913020915130f0b0912070302061602060d05130210081b 68
    0x102c5854604d4203031019008006038a014512801190001000280140a030120000c486907417041c003070350280004040ca40c009099541c0031080c4202c10a0180c4080700554040c11000c4480f9a4000341c6204005003146404601d200102400040095200e00410301e0005841e0a8810742c0301840b5241039030080d545941500c881051400c2c105041e10882c0001405000c810740046a034590b0300c441c010740b41400340c603440312240d54000005100040103a00304590030501810700c040544295544c840c0041e4840c0a04c1d0300103076010809004502e401d042c0e40c0e60400300a0700851615000320041040c03100101d05122302500c000070904004841c0c540b1102c014002640b9520395a40c40b05050032003035111001061003044d00c61100d219004011032140122079000b02070b107250481c103002c043c1301c43b40c0f402c074203a07440b030024005160228464020244140680c4103074009030381491040088036440695040304000012040000007400320415450404040d0020f40d224404002e80505080716084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 714815701 1250 714814451 714814489
    0x20702060a03060608070e0907031e0903030f0b0906030706050f1c0501030b01053c030604081e07030906031503050d0e042f0702030c03060c18010c050c01030506 71
    0xc00a071510b5056224500780d90840d45c0d02a400d40314468202c80054080000f158032440041c04200702c0c6004e41d0000c0c0788116001c0325590461802041c51080341c0c0115070560102c1c1d1a8848100e0382c5481d0b220740d0050340c000719038040746414920003080c0e0300d0710b82e40035410a03c0000903000c050b2078107020554540b00000c0d000e0018048110700c100713019000c2032100700c0342010b9900c0003094500d0107480490050500d01c080c1c01440c00b0540c80c00540b031441030b140041c05800501992090344003441800e2080d40a00700742135882c20015a490540070703840d4662000c0c1c020030701034100080c0d8000d003102e045a0003881c011074444210200d04483c904941e00090442c407805c1000c056107034012211910034401100d04221101200d0010031021903403044800b02c1c0180031314088282c014403001342401c68005804ca540c2d0f20380c207802082c40d00100340d4101c480c03184081900c46422a5030f0410b9403c6e0102880d240c4140740090b903070581d0741c1c2000c1030000d041c191110001a00c0f071301d83ca49181c00721a03400d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 714816951 1250 714815701 714815707
    0x1505090f0d0206071407060f0509090c0f0705060603061612020702040f0203040f031103040602070501050d0f0c020601091a0607020d15020a0302090a1a04030b09070b180301050f0f0c0c0102070206 86
    0xc54040c0b01d0420b180817a00c2c15015500f40007918074042c0c2d00c00c84080781541ca80c03901d49840c550802094060080148001764418452000c6890221000d080e0a41c441d800034141030810307104061421a00621a82860b51a00310503012a0f41c010800c000040907030b040940c6600702807002802800304505100b210601c003004000511880103401901c0c103002e03445d10700b0b000090310b95080d243e103c0c40c05120056401550200803a5205100a10000210500c0002c0c2c55961010080640b066050b6540040e4080f42c010f00803a0303100d101340500d8070200313030f0034518099071880032804034018901e0280c0300b017030290940340602c1040050181c0500e1b02d00e00441d503c61400201070000e402c80004140075545010340481c00d070000302104c40b4400409038a56042c10b02c0d6035240c040c040170081c0212040d0141e650009030b00c50914020741040a0039000400058074242c040c142141d4000780546c881701200c10611661a000700549a04035026204042e502c0211404060281c412540000d421076000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 714818201 1250 714816951 714816953
    0x10206060a15050a0e0d3e120a0c03030e272205060103120e0f030c0d05070e01030f15021201030303020a090302210f0a1703040303110d05040506011505090f0d020607 73
    0x307a04a1065407d540841805000c05030403111030504082022200620944059612920f80100340f0b40d180341881d0125501c81200d65906455502261301c102c002c10b403200c41483c0382e4580000d2000b5080381c4036003101041608407805420324003001d031039805843c000d026200c2d0044401c080403250301d50050708803546542e4034500106001a925004c0700010001c0000b0880c0e842c00703902407a082c40e0700070006c0174208490000c00181404130038007114503100301040000c8010360446000d00a41c0560031001d121100381c00d00740007007071001e40e01030300700c5d84100500844400d04444d0a81505e8242c41e00684440021105454a0300b031500007035400140c5501400252200340d48925502e1411020fa904c00451080204c1da20a09240c0040000032000040e40e0f091706043e01465015009160224090025417845007299101e2141c406c0c8444e12201040140712080201c0d9004082c0140c00820085c44441c0090290181e000d08a209141411060342c103682e5005030453303910340081086a4036041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 714819451 1250 714818201 714818213
    0xd091101020708070605031f0f06080403021e06132d05010b0402071212060504090b0907061e030e01152d060801050415081902010206060a15050a0e0d 66
    0x2008419500510600202103220400412107034100e070391a484983c11502c4204c400b1130002900e030701d40c44003440042400521500c0700d444400007002151291115414242402400d000d1380300c0c5640c005030300c501c1c1c0500c1a120000340d05980701c0034088075012284139034900a103480c460100d0309003520b021205d40d4540903c04941103101148690002c10400d992a0140000e030300946001404600c449007004107040d024600c91440170705039850000d041c030340700d100240899400403015550241900204203403070300100310b254082c0960741002c0f90f0440c3c52620281a00c2d010140003c1050703220580000010000d400010100082c10484c45071691220348070ba580d0b0280c2882c40c00d943c040940c88010401030a510751050340e26035910502286c1c2400e060002408840794485001c1c0090940011912401e00c0200f400100d0304446690542142c000289411805000d0902c05d02d01304800308403c041400605256050908107207403284c0a05406880d0609109202d50300844604000d03c10416 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 714820701 1250 714819451 714819473
    0xa020907111e070e0c07020432010b04060c0809120303040302210702061804051005190506031503122805070c03020f0a17010203070201053301050d09 66
    0x4800301c01c80390102e2401d080a075001c071020642240d036400030038040c0080d0400140a40e44a420440701a18100309540440d04884506404046080540a0346402045035850728401d02c94500c0890710254180100000103124a1141200f48820036061071b00f04400c80701951020580104400c20414207807074440e4032a842290b040380140034015200b0315032003810765411416041444c0082c10320815909101d41070340010341e64041815440e07011324480d034440c02101e109903104202c0700c00051a10302400700a0081240c409110051540d0500c19603c50300292503000c0e044042080e940420040400d0030300680f60308200348003100082c031a042c0004041101d49507500000c849004900d040790031516402aa800200b101400310410005440d168485850b5580d00400d40c010301c03a030b03032900044070f420106c0c01a44170365008820802c4140c0c085c41115032000d10051a80c1016a61885400a4101c4619041503460502a515007a40d201c0c41c140c0d0380144600b042080b0074940f50900c071444c0c407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 714821951 1250 714820701 714820727
    0x19050411180108010e04030c14010f0903030b03010207030c06091a010b1305010c120809030c0d110c0a030b040605040821150a080304140402070204090b091504020609120a020907 78
    0x2034000118207165100c0d122a070b04a9081018040f502c0d125540d00b210000904038003074800161b800c6182c81c0303501c005c3c8180002018400320002e044900f52070050103840303103104000d02c00d9105100c1000402e800c030f400c40028552080700080c241d40145041440c0940e45a4041100c11800e00040361a00c140c200625030302101b83c2442d04100d50381d90044480e1207160300300a01030703161414840030360ba005000141d000b44001060b241010480200f55182c841d00c2481400001c000048080d46807605110f280303109042903501c2407405086456074012183e010348010111a51000080c082c890000161000692100290540740000401000600c1e0049d1040f0407502480c80146580b4500b500500c1c0c21180b2000145041501d0074456904943c000b94816030081e408014500050340ca5100703500c820782c031440c0801282c0c10305880c03c0e032030701a05891a1404a042038140000350f900c810030b49225207011244c0b044a111518041e904010990000030342001020040c45007540e04419410200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 714823201 1250 714821951 714821977
    0x30a08130317070804090c1205161e0c03050a0521090d030902150705150f070908070803040b03040201020c0a1811070b0114030a0c08010605091f0519050411 69
    0x254590702150907152080f000010031a9030200020058070b40c032034000d480c1c00302050500c440c060305140500c1c025502c0845410007003806490090a020307800c081c203614411703014a0b503030014040c00c00000c0c003141544040501803041c007043c0183c6940c03241c4215402d13645c0d002104070307030403440080ca60348102065174090690300070044413910781c91080c490400ca690300181000035001e1400c501191541c0940002e4446005641c00c5680800d242e5070114018030201040460700d00d0000001850703800640c109924130340044008000d591000020b503004e50b0500c0306250b079642c58a10060380b400c1e0a01c0c9006070090512000041c0908070700041402c4001c8a090500400300d013628070b045280b140f180000d0034516803d00510400d03401c024103184428026048421071300706501c3c0c242c160f40e45503001001982d12071100b8015402c042e0b404540000c000350710001c9020746000d1780c6209415900032540541c05035141d209400703020441020003048040c02c200000410941c030003480d580b1003082070202c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 714824451 1250 714823201 714823223
    0xa06020c061e060108070e04090c080607020c030607020a2325050d030819111207090e0405030d050709170312010b040312051612081f060f0806030a081303 68
    0x80d6803100450b492203150161350b00b4005070744401c02950307080700c0d00c0c604940107a60340c41c805001500402d4124054205035000701418034002000901d0a00600c2110f4001d40102c0140074070306400186968241d5885000c10f07406030031844940c0074000c1001e038070304d03440e01c101740d4451407207c150480401300000c4a001915400e031601c003032101d00c4250301002000103a17401300145003e03004400307040c5106582c3d1001f19070141e442035040c801d41c00c0080c015a000140340c00340602146c12020340001400665121400e91510761100c54a9004110750003510135210000a8034440c8102c121401030135486100e08021103085061035507903040250242150038400001040c45007400c0180c0c1c1c00c60b98060010410b1075400c10048400e07401100c2000105405042c0f018009402031111810007801c80d61101030314a4281d1ba08410a800040f00d904251100d1030203006040c1d01084081d540c1c0d0160428490680300d49010a14242100030040d02c41c481c0801c05018a45030021500200c90260b000450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 714825701 1250 714824451 714824491
    0x507022409010302070c0b040b030108150f0606070f0c090207150614011d1309020f30030c0a0615080d0507031d030604061e060819050a06020c06 64
    0x303515a4a0025025202030078400014a580f080e0010440c2e58807482c1403500069403002c602c00c0300d402607049203641c10f10100c0148510402007001e45940420701010019908107105584041071000c0c1c8600c1c0107070800150b0b081400b80580020321110343c064118988290744800c0e89009411203031048404080c04040880c200005020311415110900080c0905980c4180151000c1d0002c0c020f0b1600094445081c2c0465914041c03141c0300d000120030042a486101d1040041960800e9080b5205000b88001d132040e13802104100f51601c0c10410f040400d10490818043c5940102c800404c49072081501c03002c20000c0f50f4014044001210f05d00244041e112000035440c6c10890b5107010008601b4070403070b00807070302c0790382c0708184541040085e0190240c1c0d800400d081090840d0199009516000b140201020030345003a0050100013100b08420790514851a032200c0030a907404003044032100b241d005000c0f051040e08c1c07102d42e01020440da20000114010b46514084850392204869000031072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 714826951 1250 714825701 714825739
    0x114071808010e0627101b0201021314010203040e0907050102121215040b100201050f0a0207020901050d03050c0a12080f07120f021b0a020a0506090d0b0403030912050702 75
    0xc0d818941080280450345e455210002c12001c0024195031aa6105420441165802d000032081807028070804501c00d4510710600303902c108400400d07811a031040100d048030746800400101a90f1806d260000fa400c40040104d18600454200e03011540280061286c0141c000810904980c02a000d540309818000c820303203424010390045105100e90f81c000511010001c0200b5140d440c0001d000141398503d0030b0120301c3c0c11b002c0c480c1c401c0c0545e40d26024040d00713007100101c20f58458841c080952030b080c1c00e6804528494410703c540c50050001130955030406020344142c401085c21030044030012203031070504e120b030318401300014408a02c400000c241741d2448844003c0c1f0921081c1c0380c0305a41c001c19501c010080a4007640041c4041c0e0a10540608078018240c0c403145858000040c5031014050040058002045d03101c0343c0700b10700400078100a52540c00e0080030080d084160368a0710b07600e034141900178080340c4038002e0568440b950740001a030341000203840103900070f458200c03146681c000e00e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 714828201 1250 714826951 714826961
    0xa0b04090605010e090705160b04080c01110a0c02090a0617030a08070c0209010537060e061201060507140a0309030b06040605031c09030602191d0918011407180801 72
    0x44c50304440c1d81400102e0303240c0210020031803254a03c00c90000d90300070b92524006c110b800d482c202c8a07043c000030030054080090040c00301c0626540d0540345464200720001d08140d0010100a0141c0c0c0007100142c0700c0b0b04e0030350200c8010080c801c01d0042c0100c551001c02c0e00c0f0386c0000c458801141d020000b0076200e40c810004005415400b50001002e03900700005c003d0144001d4030f00380d00b007031050615003481d0b140c840401d442900c41141032245450a194011f028803200c044010b008410500610000d10000c000076411903041d42040f95031104282070200e03605035850308840c843c0c402c00d010242016405140e1208032406a0495082030b00c5880400c003d6444a106a507410352044000b009041c483da50a00d0000c1114200325641540c0c0c3d5030b0b0101079801510b141480081c92090781c0001e0380d0802c2910145800742d4440300103910142c4005603900700054081600740211240b84c01d4903050950000704411106418a005454000b0000f07001d042030010307203042e9060b079000015000905003c0c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 714829451 1250 714828201 714828227
    0x3020d0203120f190c0302130e0606070b060604360213050f120f1507020f250504090501050604180503090405060301022802070e0f040318050a0b0409060501 69
    0xd455070300d031580035840c070308050042e00e0f1401c84c4442c600058074000e00c912454158501075100540c4810405001c40b1080490380c1c400080714021004200441d40d40030f080721002030f401950051a500e0302004a4111700854000d4490141020341005c5050002000e00c2c215041503884400d5031480031780c0030b10136401b845035882911800d03103000b0b11207460605c4d4100104030b80038225030f003a0199030a0080c41d001880c001e1140c4e503081080034070464080c00714899440300043c0002c00e03201e0101a01c0c1a0307905841390f8850007030701d0a9411a0340002c640606440100030080092001c080c59080140c001e180a03039144c1c3c0b0942c07814100386200c03400c003009c400d0160b410401a500b0b0041000520014040041100d94955404c10290000c41a14200410000041e1408403000e040e00100a842c00086420501190b500c14082141d420800c61125a00071b0380b504c1c10043d07119002010121055294104550010408002143c5050500050422158000e60602c8256520801034481d4118071700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 714830701 1250 714829451 714829477
    0xf0605010f1202010e04110d020c06090c030d030e1c02030a02010b041b03181e0b070810181407020d03060b031608091204150f0816030c140304050a03020d0203 70
    0x420b2030156016641d205003000f009000032800780b0308001c4400300c07039015500d8902104e078042880c100c83c08040100d1a4092851402000c0d4019441e0001750f8440300d1004840415071a07a80900b000390046c07103070f02c1d0007226050700c0015103070001c3c40c041c0d2a03402294039240107601c0d1600c550400c1c940b60107a49140048400507040d1170320505800c402604905014800d07003a80345588600040c0206a102240f0b00c9001c0c4038800040c96140c40911504050010410040c06105000d8440300c1051000c084441110349990f804100d02c007190050040b420703e20150f6503000b01040600307a00803507000304062a42e0313002c00c002501d680041b03203140401c0d107041d9003005100102c8811a4021030700250000048030407140300303214504091013594000c0d0094140b4600c442d5900b02c00740d070440a900b44068440c05c2c1480d161601103144084018000c051404140c0c540c00f2903600035020b16034000001c21104a040e5903403926080040d92001c540a0440040c803c07041003003a10703880030044e1703034001842030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 714831951 1250 714830701 714830729
    0x22030213020f0708041d0a050606090622060e0a290c1024090b01021203060f030a08041e0810110c011a0f12030f070314070f0605010f 59
    0x144503000035042049000310200c0704004500121300d00d240030380000d001d0591642d42c3c2c6030449100d10890640604450140c900f8401889055135503a419920500019200951900303900502c1600048070768000105810419501141140c4d000041224445056035082c00f13860303407243d00b03c240c1101c16030b43c12015080085141141d407030303020003001e422034070000f00e940300a55000680c00f2104400090300c210903154015031200f821101e0301900606224104100014a07100080d46070610b080403103140740c000000180081da1058545100b120028044410401c00d51074240d001e948a80109480312101c0701c2c01448000c5079040c00d5081d034040b04082c0c01c00c4123001e00c07602c000e005940c03d12411040140300d0b1030b03800e1509101d03081104c28110000700f445019130b814040c0002e5228080b40c05605c0710314510441c0103000040750504100201003650302c6040381011500ac54012030302c4901490002100814004a4032400c60200c0c0260401c0117280d0f82c4001c2040b8141c074034440c100d5900445 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 714833201 1250 714831951 714831979
    0x41a0f030a200118090213060f020d08190207080c0111090d03050c030d140712050c090108040804091d010e0604020d0602031e010810060f0b2208060a02220302 70
    0x4602c0300b00c40000d0604007070440c0203601841c0d400038007490704201380aa5010a540c1d584d08100c82d5601c00806131400e00145840c9038140003921550b0000d052401d00003540d0116030003501c405000b080e4046080c80864481680c1c1c6400324050b807204030501d20310340c00c1042c0100c50880700b500b01e03045004014038002c032000d07096030203582c0c94110209058040c0400c0c001c2c2c0c0c0c40b80070903010f05c5404d02125140c044052a001e0409040b550030750341c4144109160804101e40c680150080300c8441009082500d416540d0f4500f8624520594020002403802c00401c04c0000007403100c0c040400c8025002441494043c605540e81c900040728040d40c410400724a03107001c1491780d80116040358410f00303101c6241d1620004039400f00720030391141d0410f91004a100d0860241481201d028200c0401004486850000c2500c29030195806071071018448030100300703810481d100203e0040040905940b502e2900c600d103100213401100c403070324220307560021f044116100d1000610944c0d50040c02010500c0c0c00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 714834451 1250 714833201 714833243
    0x2040806190f0501090b011806050901180f0807030b0a0c0203040614070209070f0f030204180b030a0f110f010e010f0813020901120302010b01081603020711041a0f030a 74
    0x901c1c400c40501da50b14058a02104020b000f01c5010700f0943d2408103482d403400000401c40d0041d08078401161111590502907958090102c490103002440d12048400d2649010000c004150b03004e1205021384c4480010103080100c0c000f0200d034090700380009a6581e90851400b5213005007082070042c2c004200030f0200501403802241100303811030195013010b10703c0c1e01003003001801380c45030004112220348e05960309e54014003c80004085260550400740b0306044240d0b1481c0120b050074080d0b03203507242e14441e078808000591803150014440070728448035007840641c40000100c0c1d10b0040d0070f00441149c195004a600041c0044180c1d91080c0f42e01041c1800c5421480280161084c0c0a002ca800780c0076907513800700c0324040c0040742400c0c0301c00701c0300f481c002c0c2c2100c1d5200368550500c42038600b00049074405100c1c4142503d071509015966241901e8050084c1c000b900f048da81c410302e0403200c0c20310319590440d030303681410040d0703014000004090201a5030f00762211000703109101200d000c4150312384d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 714835701 1250 714834451 714834481
    0x3050a02091003150506100201061406070317131a010302010206070e120109080c1014040305070501060e1611010b240904050f1b041505130b0412021302040806 70
    0x4001940300c4022503da584825401c0f04001d8481c1c0c203940c40d201401a91724203041c6540300b40c9900e00003081402e103002454540e0b81e0464507040d00c01d40c00801e4090625008140e42d5079000c141101c980401e180042800c40030805098040d1008082064001c0d0461980c0c0b02c1141600e4058001308100d950346d00040300d468039550f2209420005402e643d4034000000d0044041841c8030322010b9440d4809d64814529000305e412117035100c181031480f5804481c00c00c40c040ba4105415260243d6203500703e0800078050140365101c2c0203a02c3c3e0a804001c01e0071262441c4442c900166601d503182c04480d64100342c240d4040d03480055106640060240004107010f0503001c43c00c8500c804d00b13043c80d20ba00001030032200c044440c90345424810040242000d4040031498030407044071240c0e82804d0405e00000d0301010305c2e04c1c46606200000440076180c2c3c68403000240184619103103580e80b561580300355400b8011070744089015800e800000c200040082c001d0700d0a490010300202140d40d602c0d60580b600c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 714836951 1250 714835701 714835711
    0x9091e0604200307090f090911040504020d08130807180507080106020601142b141515120d0306060201060b0316030b1309081e03060a0e0c040f15021603050a0209 71
    0x320801c5c00003102d0158440f010020281603400040402150902c813103900e14102c8010300c41d070303d000200001a6204424002510f41202a20f510740b40300b0016101d48101d5500040c48a2181200009201c1a5080d000103031160501092003a03480c0c4000c2034400c04400e01500c800350b0031030300040c400352007e000d40c171504d40c00003420140700e010f40403290100902c000300c3c0040507403000348142050024100007260544096002460f020340700c1d10240c02d00100c041c01c0302942c101c0641c03500c155983d0b00040c0d0000c00032404203991400c50800d00180041a00f845000095400e0000c0046c2e88940101680c0c031489104507100c10810058004400030800c1c4580c4640c0108800107485039801607201d442d0302c461040111303994680c80c45000d43c6c181e091a62403146e02c4a0204100030580d112a650181264800601c000c103c1d114441101003d024a030044c08500c8510800080c01096a0000300d000d16425001c2d00c0b80b50303100c501d400e85100043c1c00b020b800d0b90300c594544030050900b000010380c85 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 714838201 1250 714836951 714836957
    0x51506090a21080f07050c180c07060b041a01080a09020105030a0c020f03030703091e080d3204060510050d0b0601090302100203070302010b0a1d06030309091e0604200307 75
    0x1e049035100f4815400001c4c0c2c060303001c00c02003085020813004000b440d0182c841100c840e40200e1004000710a0074400600400350014041072a80c00c01c03d0a801900c0d01403c003c00030700c110702c5000d50b40a40350b400c0c5000c01d40000c0c0c12202103a00c0030040e20408082c9601039444901d1a518040341401611030300842004601c2100c0a02508641c1803014500840c0107a401144034089810014410f007202004d60104100f0314400da400508a0001c0760f02c1c6010107c0c000c40d000c0914919801402a0039241036411600401490400140c00c1d1901d44281d10803902001151500320103c0340c2602c10740156031b04055011882d6000c078126007503540e4000c005152189a164999005c1010041d441151704050b80c00071941104160b02801001c51a041c00e9602a01c0c851030841c03041d2207408a800200203012011021a100c0d0f2024011141e100002800141460801141031074801000c070203100041ca42072000308180e0720380350080224000c4884070002d0b1104100c640403c50f503101402c88414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 714839451 1250 714838201 714838259
    0xa03081003020a030305030406110901080a0e2a0306010e010311010c060b03120408010b01112505060304050c01020d0e0307060e01020c090114010e041e092301051506090a 75
    0x60340da10418001441c0f00703644241e280d0415141c024190340e0412b0540c21605414403000500381d03071160107143d10080c010300c0414440f1002d419182440080403182006400540c000d0340c081042284848d00618150112000b80c1c7ea14407140c20445020300004210500030000840c03950310640d10500403500a00001600d41c52507c00203280101b0f040034440308202c00704041240400030300c242c07851035500f03023400d0108130000008152281c400c20505a18181c5002010318600042c1d402e40000e800086c0403140e90741441e040c81c1c0d5440000754401030040c410b1700c0031066014410002120741c210054018040030341400402e89480540074692411445010311380c407580c3d075032006c040d402020701020a21040203810001010200c1141400b80258104604020180080805a01c95140000001601200514003900303130034a0940700d400c43c826003030410656004103500c05070090b5440b03d41000e500a070702d414071038240191144680d11502d22101003101400c184100c190300307480a502d01c19 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 714840701 1250 714839451 714839453
    0x90d0b0c0f0403050c010305060d030207090e0c2206080a08090f0112050406050a0605030313090513230c18040b06030f010c0c020307060809100209010513061715030a03081003 77
    0x64070703800aa1050b503666110740d4246629581600c03400da04842c0641d071890008045840180d9149050b20a10021a58030540c1304a00030040c042c0301c0c2e801070020038410600b07044100070401a000c51606c03904a42c5000b800241e044e0000a22001c904c2d4441030781801e0524540801030407000030010b241c14000500084a0110340c41e1141610940c4501800641810309407101d000704ca00682015000b940f0030402d43c81c03079090a1408400300d450080d004a607a9444201c0c1d06d42412000000902802100c0c01004524051098000e480b4900c8402c454850102c441000a4055070842c0a0754214044012a0210fa810403246602000c040e0884051014000c0c4041c01c4903030100a100c00942e4200b4903104510f400d0015000174095850001e80c181049078601c0e4a8030740d00381c4201b80c0c0301e074005840140e5034040d5055401d480c0c0007c810469031a0354040142c035090008101c6510091610006081d0840044800020700d00c00b400a11108100d40e4059401e40b030302928500303036500340c004000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 714841951 1250 714840701 714840727
    0x90308090d020a180608010e031b010914061501030612120e0604080d03061706070c0c0302130617070b1c11030901020406021501030f03080604020d0c0e030d0203090d0b0c 75
    0x710080040544010501046240404c05c441290b08a880c10364108081d213011500000166402c0b0340c81e0350610721000303102c03080507401001d182c400108845007002544903e8000402c10742c1c850b4122a900749141c1fa01d135001141202d540b40106100340d860059500c02003074455006001c4001181044900c0c03454490010304203412903448554031340c6c003601032207110b558540925001007071015441584181d00d00b2045840341401041d00e81000341000020b4240b01080c80034800540e00030300350314200082072a0160240040f03005002d1704400d0040f2840b050035000402030111402070481e941401074403011080d00054015481d00440d840b203440302c865808000056004408a000059482c3d1500201038100040f40501c0f14824040038010008204030a085004c000d50520f000070107941c0b4000081c0090140042e6503c2c0e142c9040e4050090603081400403007907880840450740c4055203900200c0ea00c1c41229030340c07a0017401c1c40c91440000341581c500c2907004482c1c03880040c10116281000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 714843201 1250 714841951 714841969
    0xb0406031e0e0106170106050915150715060510021005131506031b14040b0607081803100c02030f09181504060b04060c1103071a030402090703050601090308090d02 72
    0x302c40140d5542c10200951000c0000162041c5503050090143c907203080005840701e078006100d0006d01d651050a00d4055071940e1030791294000d00316045031202c00505009568a00d100c43e4440340d00d02d01840843ca9160080702c602000c405036004080040800d812180500390151020b0241544043d2240c000745140b506801c03148111100000c0c01480d5003400740300c1c0b00c03a81c034100145c8140c80100740010f030803c840c0041200c030141e5021814a900201041e9144907001c0003504a400105030708044c40b810a48170103035448124100d5600700b94182d50700c4211a00040002c1c0940d000704403030380c50f0155a001510b0356440041c2403080c038480280c6008a0b06d5000c482440000000f100000e00d1072405120308005064a065900e0405080020251001c01d2260740a00f804201000404040d1f038100702d0a005070141030355004102c40c070031800c048a07810a443c101c0c42044500d001a0341503110740302e41c500c00c010595400b1803a83c515120790302c85038400c804ca00d810506400c10000581c40720740d10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 714844451 1250 714843201 714843221
    0x3070c03031b02031e03010b120606040506030405011505031f0b030a020907050c0d050906070209190c0e040b0d0b04081b01020a120e1f110c0703060b01020d08010b0406031e 76
    0x40c664441078140205c1030176200d0040e8900818007400140b044c4040b0000740c400e0110312001c1407403103840301400142c80707005550110354804e030004100b004100042d04000d460f8520784c5103400c0c61503241ca04242c3c80e54040386448403d00e4112006c0c07081404150011358411801074145d40b24001c0940108010003811100f5101040001a8403420440c040091001070400351070f004e410700c1c0c690b100242c0e55200d4040041d115415140c04100d4202c00202203410203084c41c0010020101002c00c003a0006401c2804284210719082005019080280f401d0324150703400601d4400d540d036a030340c81981580200207410110700c03400600d1002d258092005200c28003507a21400814010511024140c1d19034940304c1d40180c10000c1081c0c12075400c0c48120003c2040e50340c0c00f003902150280d24070300c14050240b41101c0f03886820400801d10038194040303005400700303900381c81042590400a0b600e00c0420701ca9200d000f442040104901842680400c400d10110054060700e101c0070070318502500c3c01070203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 714845701 1250 714844451 714844453
    0x1a011d0d0f121803050a06050c0c150a1112180307080c0c09070f0e04050a140a02090103110a0203040b0904020d0c210b0a031e080318060604050c03070c03031b02 71
    0x1250302c1c09402010540a4454410a04078400d045a0700d42e51a0859460b00400158640010407929a10b14065800080c880011140e022903501d0880d4050101514000c0319603140c9100040d4107607034241103a03824012001503040507102c04243c0210551680300241541c0014403c100000b911038004104103a9104028142c1914030003c214040030064801c03010b024008a03054800c0790010100c1141c0d4500701c81c0040c2d6680c41e4050740f4064460014071400c108800807c008005945a010380000042a42c0c200b103e0060a1039500e40c40c4291300075400075078400d00040156044403002042c1ca85000f420150901a80b50000401e5440e40508800411407441017010300500042d04103401d00d9501d034090003900103407000329140c59a6400082d2035001010300302e0b01400304c0c44892103040d560200075030796a440e01414041180c1071a02c1009414012000890018900340c01203078010503895031410300d1030712190815602e20318425803c07400d140d00c0b151064001007201c40c1e81804000260 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 714846951 1250 714845701 714845723
    0x609031e070f091803030504030504050a09050a1a09150d0b010e060306060102070515340507051f0806040b03010513110409120c150603080901031a011d0d0f 69
    0x41d50190342c41d02141c1002c82260320344401d60003400315490b05114019007604000a00b51502e04040f0358502c2560882a041601c0c8100040d030280d42d40c2c0201e1140c60040010481341105c4885144501c40903c034643d40b01c40140c3c00b10f198000c3e20301119411354002070551004010950722411507400036441084c00d13512060401059050610104c0e5001c2024409000e9940c03e00740001c0880068456051014a001c40d0a8401800034030500b6910004148511800b4544140b82d0101503111241114203000c1c6580c0012a07003080010b51150550704055042410b482503812503e0060003030a051780207844001d2510561000e1140c1030144c0040810203e201182c1c4c145034800d50b004039011402079140045c4100400d0541e040180000c8092511040c1c0c12114204600307100d8041c59013502c0c5900d020030000802654074014420750000307032014003c107203107181201210718031054128086101c001c8544804101a55403040b580340041c40781204a13640e40300c0e2188084030001c02c03943c0b01c0c050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 714848201 1250 714846951 714846959
    0xa020c0d080a0f0e1c0e1216061106010b03090115030c14180402090907030c0b090103050106030e07031502130308031f1206090212060412030f0213050609031e07 71
    0x60043d0a90205184402c0c40300b1005007000707580d1241504220b8001000606404402e02e00c551036545640e000103050000c3c5240020700d498030745d0548070b101c02444440b140005032003806018024042200413002e490160318100c4030340c5a0b039000410b58065956100150070124905c0b9449102550240680c01c101c1402c0990108004440b0414035102e00c40342c3c488225800c0d14444125480b50b816124100300343c549104d076500e000319580005042d6a25000f0119404200340040c00b4601030036a0180804e0341d942074103604803a84580e0401054010704c405001041c00300000c0d9100e03d04c440c0c801843d00e400a503000ba03031105039800844910308000309210188124000c50508424500b5007080d840d4600100c0c0303210580354802c000c0c141074079202c0681c00d6585800c1c06800d200ca140b4141e41c020305d41440c101c050384d03c036a0300c40e40120b843c0c443c802038943c400744241c91881000f030b045e20b62128241400c118498001ca007120b0b5040c03040d4081d011030b078044c10446100760a00203005200075410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 714849451 1250 714848201 714848221
    0x80c0607021f0b0d020d020103110414032a09040314040602070504060609080607080a060306060602031323090a02040504230601020d0503011502010b06161109040302060f0a020c0d08 80
    0x140a0449010703040c50b10b108169135603078001031a520390448155102652610050300549101003c440301020f001c11300240040b0200441c1380c149908034192441546d00889841d50083d10601401d8620411042c01c0b02600f4041d019982290081c2082984144000c4a07860305510603000300300160449001000141480c0c05600b001e407080303046c0843c2c13281c1403040403a07960900030b00c1c4a0800c050340300803034482601742e80f05601644c0c0000e001e004654952902a5482d0300030030743c004140b00320080005003405402c603001c02c1c00321401b40510000045000300800c03044003506045c0021713405c010024040e0b69901c0340c2001034400a54681d64000d200075080c2120134020806030554202990801c1c505078080d003101d064801021602d150142400c01c100e00501c65403d095800c4640001c508080848016a000c01588524124080d4498281c1401141c82c000e480080c050381c05030001c40e0140242c151a542c0c030500d480342c01030510002010b090f01c0e1040b003240e040301107603006060155201c4d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 714850701 1250 714849451 714849493
    0x6080109020f09130e030d0c08060a0e06300609100c090b0c0a06050a0209030d0e090f180703030f080a09050a110414190507080c090409080c060702 65
    0x2814403085040c185503140349401071044000c40c2e40b02ea4020301061003c000e1070390002042400c07030000c50740c0326031019603030000900150a03da000f04071035800066051801807109810b840f8116124a400c3d120f44040c0125810050302e0444840c0d182041c8120b60448c0e242c01c0f4103c404039200406a9040c11031980b410400d645100c085940d080100d25440c582e048102c0303000f118401c00c003032541c4040a410441c10085030207401025141440240311220095802820000c03070110281e81d016a2880e0b400d55502031620045600400c40d040012842d40f4480c4c09542d002c0440000002c1203155424140d08181c030381e80048000c07a0b80c44800c48402076000e2602548038884c00f10410480030b503a100c040e40da40c80340c6c00042c920072241007400010b440342e0300b00300f08a8881c030441c072005007040361980812114510b081103450b40340c0390014400c144a101d90074011400c03c00014034040c0c81209002c003800042c581503031185002c110180700e0405c10400d0503c1018030340d0180461180092140c1e95031030f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 714851951 1250 714850701 714850709
    0x16110108010e04030f030f0507080601020106050f09130f0f0302010f1a030a14160920030c0409050421080a06140120190b0a2405010c03030b0910060801 67
    0x100300d000520900c1282050603030096010b081c10640c4c2403043c4021009444206c0c0812011380c101410b1105454110006c903001d40f0098000b40801602c58041c0303c12400380d0f03541c45c1c0d03100c0200d101181050084010501c85c0b0740c060b103450f050f2a003098486244488a084088005070365804a500756584544a0036002600200300040303618001800281e80307a4000d003001d030804010141c0c104040404010011a085000c2000202e442e600c0103080000c002502001907000c2ca0f4410034880748440d03c0480b8458a54510584d0805042c08030f080001c0c44001c2089030316040d4261000303a4002c050341810b030719413041d91314a5035a24000d003606081e80d10541c05001301c600413960112890380c0098442c007100c0e0b459880540f410103400100c0d4070f40340f0719140d00070705014406c00c483c042c030100c80c2c211381c42806210b00034050050740c110541a001420000600c61202d01c0005001c0c540c481c03000302c03603410300903c0c0109145181000040d08c4a0307054070700b00108510743c0e000308070301c42c4c01150b0380c1c1c018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 714853201 1250 714851951 714851957
    0x4090611031e0f0a4a0303070212130807030f02030d0c05030904020d0b06030108061e0105031e01021b070f053709050901020414040c020c040c0c020402161101 70
    0x281020f8104182280c0301808400c580c54032018984d1000c0045030442031550441c850928180c4405501400b4040c00003a8000c210240c14950780380f105d800104803401031290354028100010003081140c12078218049003c1814091000014601010808100607500880913003440315011303c1050702c0d101c0f40c01070350b1060001402ca8400460303401300503208098800d031070150740c80301d244040c0e40041030802c10a560200c0048004640c5000010b00a4894074400205203000745288480100403642445459803680c0440d03942c150055030083c065242d006040000340c20041902c0b2541014007003403070000c00d10362107070904101404400013a040240001e80340900e55400c901c0b00103441c541002c02500e5001446101c00a111000612503402072454a800f000141044040c042c040d50003485102140c0c1541860700340c0303d16091207503100c0782031150000d0980350690f0007031101034041800c40e4070520440380e620380050b07101c42c0018803020403509020504a00f451a040403040b2842c6d01640c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 714854451 1250 714853201 714853261
    0x1020301140f0a0512010209040603052514210f0d090f060e1e12030d1104062111040f0f0b090901062d08040c0618140409061103 57
    0x4280c075080c00010a5600c11799142409030740401d40e20380a80319481d01c43c0c2d00146090400002d001c004205001c0e8201780d04001d0541c05204c070860030140c1c07018081d03034480031154030000d5264508409002c0d150f0103000454009032103000d01c4c0b10300300700b8040140540d0b500500c1c0c1780c0c03895951114461002e041561141c0c406a0308002005081c0b02d00c942c2c035640102c000d0080c041c039038803d009125903c04001094403401036158801c403501c81d0000451b2000300780c03d00c981c40320f4251072102a1400e64925a03100c2c060243d1f034904c07102d1181c0c036030300300c03440302c1a40c52000080410b50741e0f000340b02920500c1d140300071040c5400d5104001000d50762081c0c120550034410307800281e4030901c00703504680c42032400700300c0c540b020310780c4d400071500a103010710080c90641c80d5220b2060700800702c5440746004501c0100c203d0350300c042c286c03941ca00c03c64420340301c8030070407002b44100881d5240314a1096000740002503412025941d40040300d402a2030301031500740100401c5100c1c1c04280121200700000a10110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 714855701 1250 714854451 714854479
    0x717090a0c0b04060c1104020c070609080c010f0e0f04090b100305160305031608090904060921360806061002010c080c0a0e0a0b0a020f0303060d030c02010513080102030114 76
    0x419100c44010425295100c60042c19a12238040d00c0303003c0803c2051b103100380d60f1014090f01c0c401983c49201c0c41401041b2012150798003503940c160304100d03542c9680e1031840d01c0c40c08124a401d2004c401640c46665503088401044040c00424071540080710161406c03425424024581a00f2101c141c03080e0700d00c0365050002600100a44041080d05035a2446074a01c515003d00c40b40211a1000d8000030401e0030070060225070b410020341c0c41e004590841010300d10b0f0544840e5580c0320241400400c0c101980c14124a004443c1e840700e55600e9840c034900c003403184800f00c410780c1c465032119056903c02e0083c0165481c00c00185032190790140001c1003031b142c403c040a0400c400082a01e40c0c01200440e01888590180140c4240e070310005201d03000d966160503c4041e0742d004400c1b604010300c648100302092a400104503405500c00801c0512000c3c0c80350360880748248144000c0341004024020303a00744549070781910300a080070310000f41e240d42c1001c4903000803504081c402c40c480d14080a00304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 714856951 1250 714855701 714855707
    0x19060f0501050a021c030204050f06070f081803030711090916030b060409080a082a120c1903050105030d0305010e0f25080109110c03120717090a0c0b0406 68
    0x601140c03030a003481c0e501c07038801d01c4060b81407004407600280b00704440d01c000c40607a640741d030080064607001c403290303502d4555200501500e80100480180700801e044c1c95840840c41141c05440c059172010b12041d000240d1001080c25030f0440181181d20040b10302622a8501e0705130000e5601c107070900000c1c0444c0404541403806003140f488080d0490b84180d000c5842500c6941142407a50f4101440c1d65440300005401450075504841d00d4020140002c082070a9494a0f68006041c0302448d52407818200080b03003219083d40701602542440c10100710303401c1c601c085610301c41420300403a140095550324103402c1c1410710b2800c031107440070103103880018044c0c3c1144800301c40d0041051031100143d9555030600c80d80d0003103014405c42c8541a0740c002490850307407000005060341e0f5500424070003045188031544003401544606500c81d0824018071002250703082d4410381c044d4503440d0510850b0070008048480010035a074240d0342d030304080ba84d0f0302403002c1c45200c2001404044a098501860800c0003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 714858201 1250 714856951 714856979
    0x120603010b1825050a08011e061202160807050601080109020907030518010f020901140c0a030513030f060203010e241306090f09140d080604020903030d090b1906 71
    0x140400b4810400812540b41d12012a034641801004110110340340500c0c003c0c0080d00101c1128000824450011030300300c0c188440811000760240384524a181840c81c1625900b00d40400d010300c041d400e01110200d20f0301c0d0007a50b45114090801c480d07072121b550400d50308109058114600682c140800d42c0010f0b1107003080396510030842e19001907117445002408801c090600c450650700d40c245060009101041e60003040d294000340c8510000c00b0410b82c814280e03018101c4048000d030829007980010134020300042200003000304000901d06e880303949259611103806400d61b4240e5001c001032000144484049e0340051100760611900003180040c0b000c03040f0310844250151441c0201002d00541c540c01001c054003a1440500500034102c00c28402040002c209a807201c0101040080924011405940703456040e0340c0c2c00b03101c0c0d0b900c13801c0c440654001c82a4175007621040140102c2d60019220b03541c0c1c458400e00a10280f410040c50449810f241c40500c04241c902e0900e04010303441240b111 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 714859451 1250 714858201 714858229
    0x6180b03041a04020301021611010f11032b0e03031509091e010e190209012408040f081603090f0b030112030c0c030b0a06091e0b0420120603010b 64
    0x20142103581d80e04c080f0b80a405000a0700d0440c18902c81c109042085c5044464005802030762904d00d01044040110340c0008002d444100641040040703405d1103041d50103014520390888040300351007040a02e040c0403250155240c5100350030100c28440c040103080700760100380900302d6a18150b0b0506d072401580320170b60500c00844918401340e12180d25a002e400c072202c031410314030036107034100807506c00d160962403d0b4000320b21070004840042400e101818100006075040e441000a441204a094504010241c41a6541e41c4020711940024030407000900010019145c648000ca549241c094131501154000c114030564511083c808a0598001d80e81120785440900500540301d050941d00e0013040c12000d80b4040c040c0d1408801c0c400140003a038080c012001d010065907680c3e40c2d08004580441072281480381404006041025a541140514a2000388009000c80382c00f5440004482c0d80c014440005001041628184802e6901950300c4101a0001d110b002c0070b00000401403407072034103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 714860701 1250 714859451 714859493
    0x601030903020c0f0a12050f100c0c0609080d0c02100b010f0c17130608011707060f081e07030f200f070c0906060c231903020f0706180b0304 62
    0x1074413034103940710514800202a12501c01c94001e02c2c40c01e14075181c00c1c074900210741600c501000480300350034034400c8108290243d0707641d607003641c805d680340360140900503019160100c090003010000c8115111340d040090a98004103407580050a840c0245c80440542c5814444404d003484149a00502c80554640c0d1080051000d9031440100312020f0040544c4900b00c54481280071802e2604400154103a903c00f000f0b4090b4041480001583d40b5030900400002460212469607601d0050340b07c030b5003000c030030b50200200305c48240c60b00004507022280040003075158030f03590405604620449200d500100c81017031041800448516042c0b0850403d40b50301030700042c1d20000c0c0b01c00700020344060040c4a00500c861071346c0f90710042003401400300c25611202c40d85034295151420321580e40410f00048082e003001e400108078906140e25200c0c045e4250300841c44007a0460b4001d1001c0303406450303241c40301d4805c5283c00400384240700154108030119507080051102055040d000e400044000780 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 714861951 1250 714860701 714860719
    0x708030c0f342d05030a0e13061805090309040e06070e030a1106161208010f0504090b0c0f130b0304060e152805071e0203070b0f090c12070e0601030903020c 69
    0x400d001500811503c1c020b0828080803d0000700d00d03a01c8680c111100b20115040c1c0144511079484600300c50070b13880350420700203a039050200300c1203807500b1560740020030009a9003002604c00124082e1640d10054041d5600300d04104148180c200c40b20301c08210080c1c000b003036103c5035a5074410201c4191100c65220b04404521b044071103220fa03111603546640044030a00d06103090351b000d41000000e0142880c0520a1100400c460400d48111810b10360824120714960301c41915640d05540482c1d141d102c5c1100401c94103504070783d00031040c401000110040340d601e103054140b0700e0072901c050401c10141e0b080f010081c20240001d003003141c3c000b04d50203d02c9007421404511540c14041c082030b1140329508210030058182d0f0040070040e581003242c05600201010070340c0072038482c419844020030b40712101c80443d50a41c0c40382c0c0c2441e8482060002c641c0c4003040e074000100848480d04800c921940603141c24810301003200e96140d002034080c20240001030311690040c1d1070303900000309980100546 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 714863201 1250 714861951 714862013
    0x603111e0441030a02012a0f0611280513080303090708060624040e040f1221050702010f05010b07050f0c060708030c0f34 54
    0x258044030010314161800b504144030b40340403000032841110070105400c503025990622540ca411208902203801006410940031541c01910048010b40b02c150307a0184002c0c1d0b4804401e42070901e02071083c0201d1034400e140d90707039140540c123949150f05080d15400c0c0c140200101d8115105490b0443c01d030230140000b801e00103070380485050080a2441c124666070740070026805101000850150005000790b0b2a480e865901c895a10181a03c0c1e03c0d030015111119040807500006441000804031a00145440e07a50311a045005038255819181045c3e55182c04040250008140312610700c036080098030341441501082c20350b412400e01103100d544810015001034401e44c801d03d41d92007401d50411071035840c1c081c000f11301c0d0031a8100326180d00c1010512030000300002440c400c0a08000c105c207151200c070b9540e44110340c1005d00407603180c00081c004082a904840c000d0941c0040902c0424003008044860100c501966105542d0610610300d05a01043c0d000d8850303542a040080452116510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 714864451 1250 714863201 714863257
    0x100210110705030a1d06040e0f090a17090111060405010c12110f0c0a02041d12040503060106270b030f01121a131406090c06031e10051f0306060311 65
    0x80717095020382c4414001004160130030225800782c040d6920b4400e00d0002d0340e640300851307580c242444014101c07038202c000760746038005040c00a2855590614002400020701888945844801d88089409945581c14014450b40c050102800c0c3c40d442d22041c840304005025030134140c400c070203c40189000005a000c600f010030031070202c03900c2e0301a0080018441e014501c400995140c170341c0030142c1c02469804803607043c155003928240c0320014003402d1180d01c1c1c41070030303503041507290030101c1c0c401800c6801c006010000c41012000b8003d03a801e19943e440c1c5101d00d82800401600540c3c04501151294030109606408a2a0091800154641c6d64950703404024201c40340c200c0050104403501c44010b6044408244203000e00080301c01c17508845841b03003c01881e800300b00c40074030507019400240c5030035103201e00302541c2065400801240483e00c480c007107444400c40400102d0f4841010000c51100c42d4548038040051203d841c0c00c10500302c027a81c14000c248915007004207090044020b0b007220302c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 714865701 1250 714864451 714864497
    0xc030c02010507080a1e0203280908030d0204030c06090308070201031a060d09050f060f07030903030209040c05490f090b0901060b0313081305100210110705030a 71
    0xb030030003940c45d221041d4070401010340001c84c840c0038200d0b00d0804001c1419000006480d032010624581d443c03600c528056600103243d14003044070400440503c0000c00900c00c0c402420201c0c081c032009607541c0c0c2541461043c020141d0f108004002c5425010000b142900c3c0a46518079070900e0b02090303010103468881d41780c21100317403403545c0a00c0000e0100c606002c60707885840c0251182c8180c40d084062404050744074401100c075082e9200301280000d4101e8842e0340f10240081c8a400e005092440080c041400c9601e8181080c01003540020350108610054030038001546182021082400e422041141c04a86070707880b501c01d41c0203180e0b01c3d2035507002a400204c800c000e00841013268150078102002d0341b00050710544142d5180c5800881d4040c0c0c03030300440e40302e1032200e010313107801c4034182e503d81c40650300c900c0d4185110012403c0125181d500c41400e9031800c14030343c4c0181b0010f01c102580008071070100d80d41d085015400c0001400156021003030381c0b420030003030402c24140c03103842000c150096 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 714866951 1250 714865701 714865703
    0x14030c070303120b100c06090606030c0801050a0605010e0409030201020d0203100e1503060c0903010915050703110910030b010912080307201b03070315020909060604060c030c02010507 81
    0x1000204421405040000d2124200c902a070346000308004482c01450840c0c0900d1403d507002400200d104040c180503203030105a151042c6000141011141c03900e0048070466081100c03a2500100c0c1040502c40900803141c210f4440002000a1864600080c051103034400c05a40140c0d100c0d8224010706000394107903030300403080c4a0295940c0c5848443c030038002030140503152107000640c01042c640041454040d20b00303100680140350b2500d81e6004a10540c0103804040d6041d0341380e0305064002150240004004080018041094146200080d09490044000070710020003404200400c2e610300c0c401d180c292510341000030b1a006204012075502005820185a07081d0702c0500c541002200c1006510403001559070169024001880c10000180031a4220f0700e41d00140e040c07900642400c41070b20261034000c04481d6103950b20b544007194081c441c030354100300640c0032030341074001d0410400a99010000300d8009140504044000c0d02a04591902500f000101e0104500316400703001122110303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 714868201 1250 714866951 714866953
    0x31c140f06190305100b041401081015150c0204061a030a0c030e0d1706040b060d0506010504081b0301050618041713090213091118370509012114 64
    0xb02d034030301240001a0030280400c6005030328108c88803980110110415060300c01003005014404000c4281300d024003201c9103ca104810401c0d00000c000300d4031440a00b5034103030341d101ea400415550041100f120fa5640c00794000aa0b4440c001510800500860741e100203410f00c00549485246001c0b0018030317541c82614407a10075080c0c0d8400d10341e0048603010040c2c007900900d1070359503240000e20064590070030305160040d405000084803254143c11030780c3c1c001418036000d07003080c2e074810325285002800702800010aa080c00b041070682000e0241e1507000c0c505440314941040c00f480a01600300f0001c0001d06038412041c03c3e8008422400111654624208084540d40e9160300e1103100075408684440d40101510000003442103ca02603450050104002e03181800307600a00861010803044005034403e10800100107181c542107036500103c5141c400e9001c0300580030001080e400c00a4112038800d0558900401400740c001101e2000303155845145940c1e08124580000c1c49031030140d8004203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 714869451 1250 714868201 714868213
    0x1020306220b10110d0e060a0e031c090e0603010c0215070c0b010b0406020105060427051e21030603100b0117012d0e06060a0908031c140f06190305 65
    0x30484d40140c8640700c1c3c0e0604130666500d4410355406130b40e541c804e40c0c21a50068014426840c01c0e90080c114070340141c20280550b62003d000d5030103540c500c08400d00d101c0120b00120424402d101030a1140e5a001009a00070400003e08110203075a62028800c5001d04580383c1000134610b40c4a2550881c089620428014941d611800906015006401944010340c60f0100049292929004001c00e42d00000292120001d40307000c090b80c40641600b00741c0c0c05102e40c159521149440d80044202071a0190107051000100e410b116a400c3c0007610702302400900384140005642e000c02e241a11034001180000c0312000307880140c80340030550803070903075030711002000103019141c41014008011248140c62222602e01039104010800390140382e0003412000c000646508101005095503045030501d20442030303030740d00005c0c40c603072200d1a0000305140351018800798030368a000e0001c8e0000910b03110001450844071540070280002c001c5481034440d403505401a141c00300b01a00510340100923648 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 714870701 1250 714869451 714869479
    0x82503080f0906040f022106090304050406050307140405331c0b180316050c100305040f03201006170708030301060c05330901020306220b 61
    0x4a02501200d10114280040700020042c040200b0f0141c030950b400080f1005041c42e680901c0800c0d601c55030741d9402001140c003a150302c0082004681d104403c900c00542e910350400d028072050f68071540c04113000341d20905c1c0a01c807240c01048200cac00950240c80018199450000120f003012a042e0300b695001030340b00b408d88011195803508450810242c505200e0800743e0b51144800e034441c050040c0110f8602030220f1144401543ca0440f240e06c100300310307401d1014030b00f000200791458500c1110b040c1e00211030f400309130800d00b202d0464644141010000c0d840c042d1146100f2030070031940281048240341408049099100b03803540c84965800448804030070300c610040040046000e00036400c0d20300549132000007000281c1a00341e4420f040914190b921386002620b8541c52000100e03010b0150200c40944990890400c680c0b03402880c0000856469404003d483c9079805418144103034010400c100803910384c03180d500c1c3c04056200e08005510b01c1400540010f21f0300300301c61503108002451a103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 714871951 1250 714870701 714870707
    0x15122d03050705062409041a0708041401060311041806060f0504111812120a030203010e07020c1005070c080a030804170a020a0f02030114010602030301060f02030708030103082503 79
    0x26031880741040b0741c440e484203840465a1180d81716098074000b040328002e400380c00c00c001104c0d0071070301c6503050181c0c10380d40e0006041070900c119060000901d44404010500c1aa110644010f01c24400200507090071a203850794600800314420380282e0302d070141070403121030f80a80d00c409140c00c17000401c442600c2d240d03d01800804c80c80741d9846282059180e18000c0a40e20480e42a40fa0042c0c40c0b00d8019250000d101120b05800f251502c00d009210215490507203a1006081910455030016030301c0d8180310f580c850607c40a401d0004650006c0c1d8450b040d511094014907078000c0c5401c00644481c2c05113429501140c107900010300c5801840c003d64201600030407014040c0380329010b00c6041101d441002c550500491400c0c50041c1d000e0700d40c0d180440c80012580100c0d500140000c5854014070100c0c1201c1ca034283d0200c80180d00001c010041d5951100501481c01d0b206d00c003071031030720600744c803002c04038007040c0805800241e0000c0d4102c08004411041002c1c1104600040f034500c2c281c1c2806 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 714873201 1250 714871951 714871957
    0x31210050109081f11070b040f0b091c0e040e0a0b060a0b160201051b011d06060a06090e07051204030201090b0f010510081f081015122d0305 62
    0x15010690035400403800d4140070075001c600c100010003121107401c601200101070414841c541e03541100402501c00400d00c7c40c40170601c114082e04505140701d405140c180701908000b0500d40d00f0744c01042c040b41002c0701c40743c030207840010245007a400758002400041c0c0241135607001006184508030300082002403d40180307116590448040c0d0071565914540b81c403d2203010040040040140307003000c01580100c01620060500804103000c601802e0042400c654004807544007080b00403015802d01902000302c40d41c8140141da01c000ca00303180560103009034040e40101104851214005414a4072038815241d402040b086c0781030a600307050078041e0091409080c140c540e0700050002606e00d40060b60824102c890240003443c81c4001c441307044455003c090000040c600c50768440385000e004600302c600240101074044d225214640c0c106200b11000ba041c000c3d03031003810071010400380040c0d580c58044160404848101d12a24440c440494441c01c0c0c1e00c1d170b60f00c480b401500010325500c5000303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 714874451 1250 714873201 714873209
    0x402150715060603020906040e13020a030f02030609121206060d02190207050105040605040501031d030f1c0b2b0b0a020403110102061b0705071a030f070c02030601090509031210 78
    0x1081007003c1e21960300f2410307442000031064003e5420481002141c034005080d507445101e600481c81e000e0174a900240143c04540c1c0f0a0b03441220300005201981380c04d000041d003050081c00102421030b03203064205200c0c0111003059004040040010380142c071040d085030040c80c1034840c11541c1e88180b103038004007207044c12200c00051094250208195014404407015150f40781c6500d070400c4d24000046001d040044690f8040140503035007006080c0c004c1016000354a0a101c12940b26013200394900e0b044032a2005100c811814003e001f26652101980441c141e105600c41da08202144c86170054004c03000c980c000e0003c40c05100f003141301c154547c05003003500c2c0304410a45860341c0b5500126692442602c090708a41c000c001d2042801c40c04600401800e0300c1a070564441030740d904c80c0300070441c420400e8104160b800004100308503000644c4a5408003070741c108030394401103a80200fa5501c205000c0d1070b034419946c00c00f2602458081040c2c1c0d580200c0321050350281d10300541c1031984900c00d481 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 714875701 1250 714874451 714874493
    0x80c0d180e01060507060b2d10090f0302010806030312010f05010f080405070621020d05060103060b0705030304030513120302070e150916030e030706051021060504021507 75
    0x40049441c20030100203604840702c0d80c4d15241083d10341d440d01d800415085c40c2d0540d00c0180190b00c0c03035078201a031000c1311491101c10600086031021205102c503070140d0450101c2080102c800c180016581c02c40888103a80c2c0a2810004035612140800d1841c810040200c0c10b0f140044000160200c583c5030701000d0314420380e03c80603909030210080c2c44c0ca0034141e80080450300308803414014280b0952281c0428842c8030102d021400071021260700300d0b03001000c1c042d5096115810400c403540c06000f0380c002081c031400d82030302d099101d03141c5a4881c04042c03c0282080381c000f903000b0a845e2003a81281c0a0448001946456011460040c0d40d40c0344a204010704e1043c1d5400041035120b0040d9013003840e5101408120a50f41c070309101036040901881401d05040d9203d60b9036220020400240001c14442e4000154030300300880c03c2c130020555035000000c0203002d00c01b01c2c1100c4400c503002e4421198054404a01d60316948001507421500d06082410110301041050078400300c0c4140321240c4403114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 714876951 1250 714875701 714875747
    0x2010c0804030c0b1902070302030315060c0a0b0a0902060301060e1807090b0c0a0503041203230909040f050615130c0f0c14010c050c0c18010909080c0d 67
    0x24003603038002000ca5000d008104804902d5021503c03040e03041d0350181c40c500c0c17000c10302c03140b03007031040101d820010701500182e00c084200101200041004117051750b08503080c03824281680110307582d50318140c1d00203017505903100c00724601382e4954001c04810f5900401c1d00d9103070341e1141c8005100504408070244180411f5500c0c441c040c60a1a080c0d001ea41940d440c511600d050821540c1079901c4519024820700c00c4589083c00310b1000c1c4050406440c80f8160007103007a0b0f071030500600c002100f04030059a805407a0b103541c0541078520813151160b5041d1024005580c90b410b11a84074804140302070924020601008600f40095130705008a80b8111800b48989041c85000403c40b1140c075038041c00300340410101c1c0038180c000c91011210f944100048000f41c5000261f03036082d00d102040318404580003050031055000c040c032000e03900c814142c840c12600000c800910062803010710400c1c42d219611041103003403003040411100c42155820844103c0c5002d800010701c1034140410b00941c42c2082 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 714878201 1250 714876951 714876971
    0xe0c0904020f0f01020f03071118090318040f0e01022d0706180c030507090e06060906150f12040b061c0206180315010e010503010b01021e0a02150403030201 69
    0x10540d01454014024088800d03024080c04107400c1e20248140c19442130002e00001301c4000c00040080d40d1150010311034400c0f1880c107101098168140a401030340300740082007004080001036826112103181c441c081820384e18003040007007201c0d021040b82030703080820180054905400410004003651000f405554000c0400c2110039049104d00f00d8010080000a01145040d00100c55506c0c000b0b00111414119a64a4605035003a6000b16400c2e00032801c1080300450500c21071070020300c1e54029204500d000f0002401c3d4a50080109101d500f00c484007001a0840c08184d0300c0c84102501008d40d00c800040c0030700d0340d2440482d0201d0b07900d900d0b00b0004480781060000c91415a10001010410000c01d508025550308050501015204024a100480d03901007200889541c6134002d08200c41d41014031002ca05541600320900980c10b040121219903400541020f0380c2c80f0ce03c07048220802c0c0f414003941044100400a540180060b21030304290110400610031a0301c80d40007085003100d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 714879451 1250 714878201 714878209
    0x90b0721020f07090908090a0f1d070f080414010f020426060a1a1305090105061c030c1a09071503060302010c15061701091e21020c040903030e0c 64
    0x42c0a0384040c241c01c00386040000c2140c0c0d030084441d140c41001c500c1c0c180320780e400205006c5107165111440100c0c984030101b00b00b5030880050460076590007042034451603d5034019000c1da03040000c4d0010403010b20300240a000c902903040d81000c80c1103000344591192101000003940182c05820b00741144280c0280e944030310350401c006015030307a0340504100ea9501e41180020308250354401e0a0601d055100c00503030307031142c6004540390150400060141800c1c200d207030071903800a002c2402240303030840c6611603d880c5042400c40d02d0b458541801e99145030b2810107109202a038118031402c0380c5409110f01b401000c10040140e40e01c40e000301070300308800c11040302903881e1403001038003056480c803020000c2a44c0000040321000d5926010680568174000e807510500041d8181410783d5464080d003080043c6101c2c1ca0000240b800020780b0184d41d15112110944031001e1410443c180800d00c400e03450340244140349944000404c100700f04da006080107406440642000726a90084501c0f035005868 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 714880701 1250 714879451 714879463
    0x7140f0d032106030203030d0f0b0301060501050d0903050919031a0f0105040c03140103030504080c090f070c03090305060a0f0c031a04021c090804050901060c050c0f01090b072102 79
    0xd05603840d03582c80c2158414400310b00350100c440d00742007512010080050b131000c100031714140180c00070000b00000400c114008503088035100c51f10036418654100711580e4008250307807400075081000240641d4a20f8151014882c1004003504650307000d61818403403003941100d1044900038659142d0503001c0b560302120700c483c00c540e421078041402c0014401d03801c083d4444890074845040000749a0020084100108401d03841100000c600003024003c180c0c040c040260702c024150795003089800c0a103600450710000804102c01c00c4071003c00c01e07042c07501c91002c1e8030041d500001a1642c42c01c02d111040701030213810b5038450b002410006421111842481076161800c4045640302201c1302c2c010412020b54011001d0030710304084411104210b0203144031f00104d440c440c40c0c00c550749525210078890340b80c905074000c1c400c0c42840c0b0b09041c08140c000c500c01000b0b560031201e01d0440140040140ca480080360090f070304481008c00d20808002c081d844a00f00110071105c40d0800403400c4401301e940d48 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 714881951 1250 714880701 714880703
    0x703050a0b060a0e0a0b040623040b0d210f0f021f0b100c02040e01050c030c0901200a030306270f0b0d120e0a030f080a0e0307140f0d 59
    0x203841a420a00440c40ca03404103900804010030002e40c69075122148418040c080e1803440103280e4401130401540703468030406008090b518104520220350a55991030b61078002000d40c0210345554102d80345958800d42000d420341d0114407440b800000040710386041d1080302d48000400c219400788001640112440c0c401030420b0781c02404094100c12004440c0e00b402c4900a00160311800ba0145a960381d0081e04014002507940700341c8040c9500401c01038880015800358582d1519090040a400c40d004495100006822080d520103880004035851100721001840b020110200c8200c605008900802102d0195605100c07a13904c8200942500251140c0d51012403000990b01300712810541184141080185001404c0c021110129070f5040115800700c03640c00030b4007000c0070203903089002224000c2d001e0310340f0700e003244c11035840e000a64080c04014292420110b8845a20b5200b154820601c03200541a07501c41595010070816a2085491a901c03602c03482c2420070f12400c181881190781 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 714883201 1250 714881951 714881953
    0x301021611030c090711060115020601050d080c030a080405060610050306310633030b030c0a08071518090506030712051c020d1202030703020403140c0102060603070305 74
    0x211815500c600300405201c07041609802840300540b0165128030400b4401da00300d4407024071003000390031511f0402e08140c020715080340a5800d5040040d9000421606682081c2d42c03ea06414603030825a1050040305c524100c14440040c049041aa10403942409140b1400445800352900c40801000d5041c00c100c0000180302440015224940380d508160b14200c0000e81c080c0c4041c42110800e420180c05954440c1d490721030343d00f00201c11036100c000c000e2002c509101c070740400c881a0910a00d401c10701e00c044c101600c3d1001c03298181d40c10301c500e0380710301c100625496425503200a15a2191018403812100300c018080c00040c0e107014500c200200303421551039407490b500301001d0744000e050191450b60184101c0c1c03c04204050804c050140250080008140509034404416080301000e0709540441d0016a00c4d08196a00403042c410344600c8602d001d86c484e07442d03103c220024011544058151105440700d0311101034042091441030b10f017a405c3c0d80c91a41e501090581d9203079240310081107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 714884451 1250 714883201 714883237
    0x3031107020108040b100302040501080303071716030c2a0302070f060504120309051005121308180301181103010f05010806010308091c051b01020d020d11030409110301030303050105030102 83
    0xf00e40c5903915600c4a01b48030108050f0361a42c004c40c0440b4000d80018210b40c1c400418026002e400140041e6411580380c07025031540f0300030803400c2285155485540a042e200e00070b100849001d244008030f24581840c0300c0000b40c448040e54001d216101c241074000d40500c0901080201031a030090301a25600c0c3c440503c1c0516004100900100c0c1090540403c0340f40c0300003203034541c1c2d034103503d19100d0b0856581903214450250b050007482000741203008031007483d1241c1c0c000145000281c598042c2c2c0c59900e04040d10500c404039000d07121500400d543e0031b4420660b80100107065912914a0300150700030000341e81c0451000381110f030280034180c1c0540c0660f004000107200b00c002843c6102010700000117280c180980031a0111345030703404603000e1300200c09046e00484c1c800203619444009100411180d241694082d4888480c41c03a54001c002c0303000b40e0646844000c0003210024034194404014050803600750f0b01c200c0e00700b80402ca00103414540002075900d814001d070317280c40c9083e4090000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 714885701 1250 714884451 714884453
    0x90d1a09070b090f12060c0304150911010503180d0518092509030602030c04060816050a0e0d080d021201060504030c0b0304030c0b010314010c111510030615030303110702010804 78
    0x14010951071643d65110340c0085071060341c175100744100782c0110618058a920703030810b0301d41200c60000e0f0070f07044002c80b031a211880010500030200303481c071054203013000c0e9507079114928658a0b4038400e4600c1c1d00c0d240b0800c4e60200141790320400400d00f08901e4a000e1154200c0b400400c8581c0c00c2c103413550070054145e01c4180c45d0703c080d074400d0502e41003250706114042d25540ea03201402d81e0011180302030941c0300450100507894108014503840742160b400040b54084010303018001d402071040400400271b0441d9403138039945951014410031500904d1264032480103000d0b81c03000e58841e407079504180301d1a8000180b018018415201640c0d8000c41d4403403031743e041007006400d80d0001132041d010031040e031043e800441d41c420611030203180a500c41079a0b0103102c04c103050075203e0200c1c0c4c06040042d12114403d0030780001c10b00c54003440343c1c2d04960f200703500c030b075078008018080d182c0002d06018034146014003030304541c0f0b80304001c42e0310a8405001c0310460f040708000c140a1210068045200600018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 714886951 1250 714885701 714885709
    0x11030105060f04090f09060e0102071505060a120c0312110601060f05072109140a0b030703090c08212a030c0a0b0103150203010305030d0e03090d1a09070b09 69
    0x401c60054007518a03003880d0703035150044103680c6111003803142e45c1d98903000e21081c01030601550b400c800c07c81c030080d40713482e80035601c40d10340781c074032100c0c1140d125600c1000c61081e540d884c0f104002800c51000103011107006082a018900180c8030032500a0101002040703603501504580803552412000740c0100ea1a2107029144d07040203820355002c100081003d071002690000e4a01003800240101000c0384117842c501428540350b40c1c004200c003022170781e0002c01698031030b9081019240c003032088548a80b280c41d0107402030075072544014800100510081440800040c011400c008055026002c0300c610310301040c124403c403151561080400360b42070a604480c0c42061003514906802c41b441c02400648181c00c1c00303801002110b1b0040c1100040003031113440d030380409000030781400c11891545541da843d0fa50344074400c2207107182a124100c444403d103062003a9540c1c400c0141550f10022502d1910600701484801c000d101c003514080451030582002071034105a500060b000d51070002224208 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 714888201 1250 714886951 714886957
    0x80d05071112030c122a100504120f0804020906040e0f030a02030d1505090f0a0902061201150201151802040b04060c120201020c03070602070f05070311131103010506 73
    0x16241118052018600ca8582c00791140401410354080d544440a00840d242400032032403803001c0c07131202485070004074a10203c8443c0d890390250680000202d0301e0341440c0c2001500082c4414481c900310401003400500308181d40005c0c416521740104c0d00301c0c1030060340d00c207400703407030203504500e1072000a44d807400d15600c01e14420452800300ca00002010050a20b1076208e0240003005800c0402e80c059480068091789001c100700d5548401c201d030514021801c3d0000c0242165000c0210a000c60164082540b1494803141c01518541c1d44600110303010701c1030320080c807465a62480b00c80314001d0307952061140980c0084682e40045000b4542a1482c000443c02c2c80400c241a500700b10000d69032090a00a200505444d12003180046560410802506401488a0669004010400c0ba6550200489060b154085c40060300d581c0c281c14505610088881d0091040c400c0b10404000e202480d583d0002c440022501d0340740c0c86615083e800c061380c10065080307000e24014001400149060009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 714889451 1250 714888201 714888203
    0x40f1701090f05070510020a020d030302031015171e0f220609050705180105090709080f070906080304050d081b190203010f050f060f0406260115080d0507 68
    0xca81e075101921403882000328148211807552001c48208864208082c200300084007900282c51441c0454001c2036050604000042c101b581c0000000c0c9072220001060300500191180d910000b42c0428001d040000d40d00782d460112801d82c0d0004089881d0520610384401c085801003040b030f01e844580030541076000c0c00200740c0c2a040c607401c0140c0c0c0240007840c1401c030f000e80c01c00316604885042503801d181c100c1c2c015a02804071801d60344844000d240c02c4504541050790003205556481508498a60346900441c100b4001c041240c500c25600103148c5054881e540e9007081400d90380c9810316560702ca10f1141075000480c0a034040080356000000c0c0c43c403061810000d200784e001042030175080550045925405652819407281903042c248610000000d42c1d44040005003080d201c0e50501650080800d84111409541d41903503443c2ca0308664020315440e1001c04ca0085548104101015000310354891907103032951b00d4900701e607180481004c4440500103080c0701c00a0a0003111540e01c980c1c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 714890701 1250 714889451 714889453
    0x70b040305090d06050a11070507140102070b03011d0603031c020304020a0909050a0506070c0b061002120f07030e270a0605060418050915070c1104090501020915040f17 74
    0x310b0b030654481d900b040006620031900028035103010100402104d20b840070400303000c24103104000004000203042002d441c040444040c02501642c0101c2c45c000550304140300c0c0c02c2c008000002e080840a0342d44454a2000030131100d0b5030340b4070f028141d1b68001c5103d41c2c1d4142c9080380011114101c03603401160445e001400e2050526100c59a144c140d6042003c1120305900000184d01449410300c8200d400c28614600840358901c2c7d81c45031540d5600191000e03109480054802108900130080d84c035804107180421a1101144200750130107801a0500b070340070660010301c00300300e4a000030201d07106040382628411a214900004011181e0007803041801c107030354002c041116035032080600700410301c41200040c2d4004412125082c0c65020704503551aa1044c0035801003100304c0042d01d6070007142864600802920750410800c1c14a81c18079150f000b030b00d0303c010f81c0305102d410b400030441008190396a00189017503488201c201d1040b03210324005808080014406070000c5102407000c410f441c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 714891951 1250 714890701 714890707
    0x60f030f1c120905030901021e032a2508071a0c0f030f0343050d050c0c060117190812100515160224030108030403061d03070b040305 59
    0x300d00d0b5084401c41c05042d9020342c0040fa00345050340e410400d0308001500000b03140b6200e0204416140d42e4014009201c440d09882e6585c02d52400f4040c6901050340c000c0c504507082c00403e00c0d0858030444082c1d10320b5440c820324002c04180c1c03000c00980d070002c84078414450042c501c11111205050340110131010218003800750f9009195600b000075008640e421f009950303403400d20b40310405410003180c1042d211b8102d00142d2000d1007080d5100c055150b00c95801d5684048201c440840d87c0b441043e10700c000d540d107480c044c0918175110340042c00c04010071408880050742c071007030441014034079003820441c035501c07202e0590b0803112011070300d404031842944075604260030a0030040c264142290311a581290809080041e8608002490f064090483e045803405100d903414080c50014502c2c081c1c007030313070240c0d0b030382031400c1010910f020800e40010415901c95031915030107601c9900c184800d1726601d06208141c2c1c88111510b1401c05400301a400451070012075a580c010b100f00010000e400340807040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 714893201 1250 714891951 714891977
    0x906050109140417041a12130302060a1a060406080f060102031303080913020a021f0606020c010311120403121401050607060e071503060905012c04050a020315060f030f1c 75
    0x1d03900c0600780940700070720151147c02e0014260390600c401003040300744a41c1d80100002080d000b040b015044240b05030b0220302004541c2e510740f03100d031903040d07025000b07140081d00180c150740c00408240502c2044903200f00302d8803410012a80c0f03001d1000800038038182c500c07080000450f03d400400355030001901c0c80a000016494000882e007150800d440503802074400001805410628108030180c2c90f1420043d0504104d0025a60700b0141413260625a40d0800c1141c00d242803000d81310042d085540c00c201d903150a10300108100f00c546032a448442c02d061013552952221610181641c0000d40a43d081011035100c100c080c0031002803040c01d030700610001050502c0185812100140d89880c0428118070b0011440c0c12250160300150002a507803010308413103c0c8000b0020602e0600818002c8a070302c3d036091043c249580d2110081d0b051107201242d4038000300b80102c45102d6041102c0d9030555103003840034503440f4071104c084245260418540050800301c415113052061041c2d02e00440c2e14150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 714894451 1250 714893201 714893219
    0x81507022803080703140a0c200a0b0f04030503070c02010c1a0709062a0203070b07060605040c0c030e13090b040624031205030a1e090605010914041704 67
    0x10207600d030394803041e00c02044424140c015480d19008441c600d000c024035007605c440300d4002c4501800c5612810780b140b60040307903e0f11070b1891403242801ca50280359024030280784195a10301a440071550050700000250440b031540900500c29901600d685242d0340d1030110445641804c0241241448440c050141c040f51000d02c034200e180d203000c002c0300c0c030a0034040c401134454a21a40913030100070004a0b007034031544c007030004c44545000840102507602994400a03050003011f420041d102d1402168541c14850290404000c46206070340411521208100c00c40e501406c0880c0503011484072400340e400d9040c03001d818085145000c60000d005802982c441000d54405d6405959298660110708e510030640010644a0003260041c40c28662455861480c4810410403603c28004040000342c0c003981ea6401104c4040c1c08093b0180d180c04a20314200c00034a003c803420340301d0a00d00320012607200050b1180194010b429043c105080c0d80d59590100300c6550480c842100140501c0700040d0010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 714895701 1250 714894451 714894493
    0xb0a03111603080c0901021902040905100b13060303210e0307030509180105010210110409110d0e0d0e130e1903032706050711030f0d050c030108150702 67
    0x4000e80d00a01d460036040081042c140038040c00c1880070700300607004180c1c1e000600c0b80003600451401d1102c401441c00054000d0025010140c40740c0a1464200210b403030540c40103402800803900035010b000001c108408a030301c28080203001c00c422400d10503046c2d010f060002a802c5582c800460843c048200660950b0030031003003140410000b0824007600c3c90310290380d50701040300304030340c81c1e1541c58500001d540c0c1052103280380c0100c4d40d82c08405c804000c00c1c4126805010384100c01d0001d42905594441254041034200c421145018140c0c803858101085d44400b05199580c2c0300000d401d000c00f000b8080608409107200a03546841c501d00c01c44e800d11403100c08002c0008944c00701d6060742009030030740d01090201d0f80b6080c2442e81418201c48145031105960b90001000a281c0d41c0d102000e0b1010151401e40001c1d030700c000b064990070b20000c1401800103000248091180c2e0f1030703030540c1d40007601003800341304440d8100741d144022407a2886205030340459284111143d101c0d03070200c8000114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 714896951 1250 714895701 714895717
    0x904110415030b1608130c0e0f1f1503020c01022106032118040e060117070f080706080c04032f01050310051908010f0b0418030206010b0a0311 63
    0x500881e010800d200300c1403800396004c40605800c0c0c42c0203251840003410725800502c00c01002d8107411036031b41441592800c4002920404e1048610741c100a4000701084408031010710ba080405030807c1e809906a05094085420049441102e40c02d5000150041c0d00b01c030f80503840710340d824091001132400954400b03c800010305640500f9044c411700317244c01c0c8607100690001d070114120b100400c40900c0000c0307d000c0940c03007604000c0500400c0014000d889554100601803041c10004150f5515035403018500e5031003039003242d483c05d41e1002c418086c0c140920aa118a42102c2c60810403180501030f001d0b8080c94a078001403425440395600b2001c1c070b05240d0b0109859041021300d5032070404403c0020010b47d001d084c128114036143c0c9142100350310740c0c0031b280c0c0921601c009040b129140c039502d28029080d074400a01020940001313200080c0500d0840d42d2045081510644203210240200b41003150117078007906a9a00f4414100c002d41e00040c0400b0425940341c09100390420745038042c100b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 714898201 1250 714896951 714896981
    0x90d08013f0201020d09030812040f02030303041a01090c050301030f0827010e09220203010b1302251a0c040b460c0f02030d0f08160e09041104 63
    0x44100c2c0002454185699040024040720354024404103c240064444090303141c291005199102c1c9811700141100050094041c4800f0080c00704008041002c14455030a400e11642260790f192484c10a64401d0006080400c000704011f20204000780001040b140c010b100d068507060b001c0308400c0f502d502c036001e424469004400124041d41e4040c003501000541142c8038900f0342001c0c560301200901102e05003003190800720998086490a40002647e41c2005012086452420151901a40c0910344c086640300c0c4802c1c812a003c0c0030f0301c100c9a605030704030b41c0307503444c51814203510007503070b0030203060021807103400e00002640c42a12001401400c184140b0220034146130051500310003105101c11100c95140c5080d0201c05062070b0190744800200d240152204409080032038051a4290b0041d4160080c20208a50b45801c00d0301c3d02000a01940e6003103013a80d0300491050b46100700142c220000c4c0040740030072503e00d800001550054000c0d0a00b0701e00c1110b00c00001c007115101c00e002070b40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 714899451 1250 714898201 714898319
    0x3021e0a06080a0507090e010b0a180b07020a09090302060f100f171605060a030906020405090f0106110c010203190e03010501091b090506030a2d090b090d0801 70
    0x101d03c91409125040005402c4c90300403c4d003400c1183c0c0400505008203488101c0204100380c4003441010314202c086082e0841000403501c50090404550003803405034001e1140c000c0003c2d40078900d01c9942001601a40542500e0311410440d046640b8054490454a440d00e10701158504210001e50010f02d00e038070350f02000010f442c0200d402c12501c03c00240e401910342404018545400c4102d0704d002106140004007030310300d4940076009010355003099820a00340001c100451500244480c140e5180e82c654810b01415048802e81d520b074041350960058000303202008a00f41240c0164007901258200000c0ca0701e1540c000c2800c480c0240d0050781002d48a02c02006103100000041d43d0070361161401c00111410a000320b61070f44005401081040c0d500c8020849030a858000b20321032661456000801d4001c007000d02001e00449139055580c4c075203180200388207040c00200004130081d6038494001c01d80c03800d4003441e642c00c00303501407452401e00e4002a8512404110703010010540340804406c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 714900701 1250 714899451 714899461
    0x12020d0c060339140d23060a06050d020703050403050d03050114060408031c0b10020607020d030605090613241806060207090203040305070f0b0f10060903021e0a0608 73
    0x1800b81c09003103102050f1802d010031948440e0300d450b10301c4416809050490311002140e07843d2569100750000b12413140c0c602446501e80481043c41c400c00f40015071508810303500c6010030010300d1328151140c20302041c02001048200300c900c0d0003401ca014082e081c500d052a0342d03922042c2c14246090081000039988000601204c003500202d903035143c10654603681007600304000d0641c1c0b480b80c4032400310704861a440382603003074185070031070b01c490070780074089903038801e807090000c0d50380c40e4191081405800b03030a00944005210b0311409007103071001800941c003601c886060090100c013001404248039140c40007018401300d408925642a44100310000342c0d90301d041d00c004120358030b00c9801e11190782041000c100041d800981541038885c10703900103950352220701e0161110b118118000f0b00500000f05042c1c107011031140140e02c104a83c00d410080c541d80e111138042010350600440e804114403800a001506080a1050407411900740340c81070010a040050b044040507800f144c00260b51100b080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 714901951 1250 714900701 714900731
    0x30605130b090706021b0a1505070605070528271403061015021f050906070c12051b010212010815130201080901021e030a0e150112020d0c0603 63
    0x41c0d102d0303088005814060300b4200001d49401e0b0b4040713510120000c00d0384840701660354800e42402050075445504c0b0700712401c0400f03803043c3c10880056680b03515040000340c115000e4802c6954000d003400306c050071006460076480c0b401d0041e4001d10301704610307040302017880345030b00380f00250340c01d5849a100066450641c0b04c40304c15228109080c0a80c2105003441643d0041042000595070540b04840050245035000c174034100d8882d02459055420380310b81800284198041801141610103550840c0e84424003039941c005030a4000f426141042d50701106107208101402907600c41c0300320100d4030b8120320a0307542681c0004400304005a06440100310003c01004664000c0310300381c01841035460f1154a510300011200400380c14045803000181c1c4191081d411220749401020911801c0a1071009480da0b40d00229078038040700d454002c1c004000c02c800140c00904860382480008141c3c200907c14040044100040380c1112044141c40d00240c140d0703200001070001c9550024242c0207040f284 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 714903201 1250 714901951 714901973
    0x2120f0a03090807120b041e080708030106080c1905090406180c030b0117010302040b1c050a0203100e1f060807140118060e0d020102032502090c0306100e0a03060513 73
    0x20105c030400600001c400210802600c40e80560881c598624400080d801100110303c0050014007154001898608010782c101c05141a55001d55500c0002c0da242c41000c05c0b20300c200031141941c7c14424004072206842030004110860b0040c0002c01c0d5503070f507402612161000c000f05007035480e032110701c0100460340c1803140312428907091a1001d1510600c003400c8030005418040030f4012038030b60800d8900380e10348800c1e000600c1010401c460710401e142c00c0564890041d40340491090081501036418605540115000a400e403c050320f600100d0b00410851901c591313075034050b950b40700d04000645400c1071007080c0041c20103005100b0f400c92400d0004043d05025a82d8854000c0e0f0000c00788229540710700300500d425001c0d40c480f42c0680c2c03c0d0005030300e180644061300c00854508240c0c450400303812801034850314070135648190203480e01d50614000d40011074059420105504201c1042441401a82e11207417001c1d01040805440f0388515040ea0421150284600301180e13040d82005031481d51 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 714904451 1250 714903201 714903209
    0x803070b16051c02030405160306020307022512050712051f06060509040203100314100f0606082e0e150a0e01050402221509060f090302120f0a03090807 67
    0x7600d840b803203440c510810301c2001c3c0f40d040d4069000c00010208401081380440805480344182c007010342c0d81c64104040c0d031017201c8490050050107c8403081c042c0050044140c4880e2110020815061070b11240e00004041421349451049100000d22141110030091905000300701811a0400e81880c1c038890309085101c04803e43d281200800507503520009031a10b003481102c000da92905d030390120850711005900b0203000140d28601c0d40329115400500d400f59066503000034480900031801c00d80803145948109008501104000344c0c840c1c046100c1c260342c1c3c1300074070343c48e4812001402d02c1d40850405030700202c4c507508800c400d00040c041c4024081484180445240c0401030802d642103401d40c2c41841468050f43e00801c10082c221180c40218400b20b10076a480e40d006075603241030005103403030b40d101140031503030550001c1400352064800c000c02d100b0940f80e40008074a076600740300c46102e07103030442000b900650340040c11009041c4401c03e03800d40a982e60602690620048508000e00c40d80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 714905701 1250 714904451 714904457
    0x308090c030303070e0f040c0513060809030d0c1b06091a161202120a020a0305011d040809010c0b1501020706112107020307060306090c0f21060803070b16 68
    0x214000a40d07000000c8030f501c81210702d010485841d200c008685010452031a01d50f1190030003050313400b815030101c054030a40804030f91032070015540341070989106030180c8809401d40c1040002c03040f41c40300c0341c005031000203040ca0030f507903030f03030403070350a5000c0074110401c101c80c1d0766200c0c0704802c00e2002400d44407044065100300a00c0d43d0800c0344030400a54032131602007080c03040443c41d81102e0900382d4140e92203010000d8a50303030103141c4419032400a500066087e008286064000724800003840019022418510070100282e2030f180c032201c0340740d0005c0404034104400c12107c1c60005000f1100c090060564104c0e0a90f00702c000b01c000ba0404036130350029410407002980b4840030107800200c82d4281c059030b403009180801d152442c003a052281b010080c0d014400c03c800011119803680c414800c84034045000c10112541580c226070301c0240844480c00148460096803501c1903401740b200030312482d402c0003c1c0e40c5513144441820754100100a5540b40054010002c0201101e10310384403d0490349 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 714906951 1250 714905701 714905713
    0x80c070302180f16110a0507051f0504091109100806120105060d0821010e07020c030307200a080706050a110a17030c0d1b0f0314130507030816030809 66
    0xd0810b0281c000c000e00c000301000325a6441d0381140c2c000d006400704241e00b9011b0700e11004003401c24a82e90103c6104003400740029502c814504882078100702c0240f4a00e50700d061809290104e4000508080f6408091a010812160415507243d50800c00c03032050342c0d00e03044030502d03010040018258880a411071580d05080c100030300b41d41e800c9441c070310311a4801c4c0b2054681805540a009000924125081d48604c82d000415507030000c0c0411351090003141d01f2135488640400c14140c483c01098001072410800ea00400c44950036540000c19000000d004101c0311070313031003030b1880c44e2074282e51244c00415000240d0440f007940c04405600d9442c4035000a0002000030b540d0004840345005d4810301030b080c040041800303224802c4c100d8540101c07803e810710544100c04000c0c020755448990a1000c1407500c030b0a8039680c0c1c006d004140c03180481c007a41000b81d6030f68000d03104210305101030843c3c89026000c000b2000500d440003034400c440c07801140d80346041075458090b146c400050700c1c800c2664042 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 714908201 1250 714906951 714906961
    0x204030b0919171b0f16171f0f090303020904110403020d021507140705040c020f1b0a09091401140f0a15051008192f07080c07030218 59
    0x1030021621a1145150400e5444c2c4549a2680c0e0064001d44807540c50f000d448814109020300249010000402c0300b0f10300d051a0f501c0003644072402440c41d404102e500030300383d4044010701580341c0c2076a42d800d29101182d84901e1080740c1044031300701c14003200885d80c0407500180d20300303040c8552500382c88600d0031a45068190b070001061400e000d00700a01c58800b8a1022104d04107550583c2c0842c0c0d8000000b0340c4d2540c0c400a43c0d511758840b80201030080b494032202d000c500f8400030704650440520400b4241c0500c5d482110354409045c1210036400c400302010014401c3c1c034a12900004174000c2c400d1801110b416030700300b0f094035070810391100301c4031806052100c165111001990021022100080d00c038800e00003a03440c00030664005a0b006040c800703000c0000e50070941440c81403e121905200e0140e11440321021503c04401e8800060303603009001c0300841403050030844001c00003c803541494403c0d41c4e21030290b400f500d8990303543d400000081045040031607600c80b68078010344540d0f0140c508 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 714909451 1250 714908201 714908213
    0x9050a0b061905091302040303030c092306190203030a1a030607110709090605040c06090f050111010b06030108070e0603030901050d0c0e030d03091e02010c03080702100204030b0919 80
    0x150082c0034142544440312141c0240904100c44050310003030041c3d1400490b0503074000c02034010344010382c04203040c9885c03055a40e215044440503a400c82004500c0c20352100c2614048070101500350390008420001c0c000311002e013030004524014103078003c543d01e24010f0f42c0a400c0e5400299a0440009001c500380a01d0b170b00412002e504c151a8a890100908203c00183c071703000b040d03030003c0c85081c41c003803c0c10248109a0810f901c2103000e00580b056042d03071003c0441d8111414442d085049641c10381c140025031046910b01e04501007000082100e180003400902c05034000c0c0d00c140003941c84a8401c00c034400b003a40c2416400750048002e1410090514006003151140642c0b043c0002c0d40c4221142004e8010040c00300f0021021b800c44a44040b03c2202a004005022059440d51040203182401101600b10b20703007000d5040c2d40c0c1c4c42c40101d00781c0d003d541c950406020402540106101101e002d0304a1001d84021801070302e41040a00b05041a142080458100da01c5980c00481c40c1201043d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 714910701 1250 714909451 714909457
    0xf0c12140105060f040b03010603050403170603030f0904150806061509060f07020118181404120e011709010510090506010e2205010b0a0306050105070510090807020301050403020709050a0b06 84
    0x40d9080c0741e852401340300c5403009114075041100a0b82c40400085041549a44040d00c164402e40700d50b4401040881c00c0003510307a04031852039040d07008009a5032506200c0002d0140200c0191011400202030710600031180c1c1c590f0802c00e2281d000d001000000c1c500f14506281300740d05203480d41d10704110702c00031a11a00c911488601d000100007a44801c692080c8850307124154010b00c503c00c2e45480341e200c0b401200345004202640e9081c080703198650100840240c4c00755a0100c1080320a00f02c08100b52842c60404034040d040c04040250148500c0c0400c01c5a441030a04c000001118504140003140005407a04108011490401000101d036002400100e082908842510810607804a041e41600c0034100c0510030a007044000502d40240e00090104042d01d078800380600c9071036000440e454003a4881c040d1203580072102101300140c0c15031061a5030f034003482031030b8074108198004c00d09407401900c0490041e848024101b003140003034031800342c12054580007840010f03043c2c0001603040c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 714911951 1250 714910701 714910709
    0xf0a0c05210711060a0b040c050906090d050715020f0d0c0f020d080903011a03060a0203060a150309021c12181e03061b1b0c03030509130f0c121401 65
    0x1001d004040b42c4154000d40058504035550400c50701e80e40741905e14038001d098160311040c0604c1c1001e000c406490f008500740c80d44800f001d08901e050a25010411100e4107100800344d5039030003074841c00b04414850300c0c040b404442c141c0c1c009003c281d0003010000d2034107003500c80b04810400e01d210000c00042071003011200b02034040750100c2000006003031050152040c3d90071540d042d880e1402d19544c101081400080610b005c070203840e00da44e544040d8030706a11044580f5580848040300500c01d0341c40e1140c0c44044010030b4500010494055400310b814050320946c00003096800041140801911400c10040c0070031914000300c42402d10300040d809880c3d1070040f200451000d00c40f90001d102d4046580c0e0045421440c00c0c080820b00c400340301c035502485121040082e560f82d0310300c00304c009c000c103070030903916808010b50341c5503071540d02c04481d65040b420010358402c0d428440011055020300440302a890006000030706602240740c080c207000e48034984821402d05041c80d00c02000749858501e0704407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 714913201 1250 714911951 714912007
    0x3031b1206011206170d0206090607020307080f13030804031203060303020c06070303140a05090601060c0f02010806040209120609010f0e0a03110a080316030b0316090209060c03030f0a0c05 83
    0xc0b840c0114510040d042070f400002072012805c4805110b20800280010610304603000da070104d480d000200d0742c640c8422100b46001d0ba0080000c0070014140400400c1d586080d028100d040c1010418101c1c0c101100d680b05480c00c80340460300740306212880e4802c8101c540d0b10b0400700900c03442c6030740107502c0e000310b4a4071318441c0b100840e4030343c00d0500a8020081144501c00c40c03038600d1600302070540c000e21003920480400d1141200104906015040204c20141c028034100c080c3d421507801115a050002c1c46260099000d201380f030301548481c02000c2c1503100b210701030611440c00c100401d0131204203a031442c6441d07043c51103404c50700741c000c60b440e520303540c1503e032401c040c0059201312441d0007400c0100402202c000410880101003120030540312011a0340c0600c0391121440405690b0030184200310901074141600f005511002d0b8010030150382c02805e840d041c01455008682150003c03100903c1a0000c0e00030070008141c280300701c507807a03200d50038220705003030702810805a482c001c1c0c68241c0301e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 714914451 1250 714913201 714913217
    0x80f0105040e1e010e1915020a120912180e040204020d0b060a08061c030512100503011e060b03040f0b130206070320030406020c060d02040503030c03031b120601 71
    0x1040010f208030005110704641c2e001064800440741402003a0312181e04069001e0821100d4492041c1050a950603070081e0140307030200c0c0c407030184074020760101e0442010300c9031400d1a00c14620352802021461805049007039100c04040b10094001105a1701d1148030018411041c442648500c0c061600143c05030350050700d90035201208401403001110080c0d111030040f6101410b00d6011021318402c660549062902c0ca000f0f982044a0314040d80000700030070b00c180201d00090300b121164503801050426161680d65a440100c0e0850b0a815130302d018507074024000040511647c06030400070804140280c0ca10703e001e49800c1c01044028100400c150f0642c030101350301a8105101c0e00c9440d40040442d40e41c0c100314603025100b84d00010720038052941c1c41180c1c2c41201c00102c1601e00701c40030350700600311404661042003010b5120101100c4007641c02c0c440812180c401b000a8494040c80c0c400079070752400d00d118044a03014205403800c54100d4108070405010710700206454000100b8208008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 714915701 1250 714914451 714914471
    0x3041202030106030f0c0305010b0616350408060606041d070201020f040f091406010206070c1506030501050f0109202a0106050f014407020c10080f010504 68
    0x701408140c4d001405280d0501451801e00c0550710031282100d02c10402000070030042c41c2404418010104811007880201144c0004903d512450417488002d18080c03910304545000c11406d21400c01d00454164040030506004140b001c101d0140c00a00444800d41401c2c5444c122488841920041000d01102c4034081403020b4002d4056a154100b005d0040c0d49a135254030b030441d1924860f120744594541000341c044c1400c0f600c036035428042d11044e8042c19071640c0700c44082d614041d407080115600c200840120b050a8614030400c000b440c030400001c5543e080100030811404c00603000191075928149021100c0c0c0784100c10a9044484041c0480c0c036601d4104c40f0f00d0180040a60a040b0201019103100701b408065001c002540c0d412101512446031041c0119040c25801e00000b0894606015010344041c13114107110071a00c9a520581c940d02c031b18071003903001c0c680c243c0d4243c3c0980d121110049c590300d40040c0341e01c4d45d0071042c581200c2c0c5240142a0380c142800600c134860107203030b443c0e803e24 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 714916951 1250 714915701 714915703
    0x3050a06091a04030302070215031509180f0309040518250b191b15090f1202060906070c20060f270301050108030406080a0b1e040615020304120203 65
    0x50306070b26680050309492900b800c0c041d01944c000d2100b02c2c410a010074410500003004410f59004510b410701201e542c0300140c0900407286400f50100d8440e41014144810103441080f40300c02d03540d0800f000d103444004403c1400300703a800c040d0170901507030307840c400304502d401c000220340030142d1101003400048100c0380701d00c04a00340c0ca41c00400d4040000540c18126102824a50410040c5540c8644000b00841e0403900c0d01d1700041802441102200010311803050385810081880b03000c2c05c240000c0702c2e540c0c2c0ea050b09011000d60b4071805a0401002c10400f01028842c03c1d90050446c01c01c0100b120b40c650b2800910043c607000011070050401c00c0c42160f40303032801900c2d060003511302c2c0d8581da581c0940180041d0410020b41c008000c3d4401144425814180075050407142c00800035400c142c00d2400c00d03640864000c0c0120300803a99818645110381d21840c6542c0840c415042c0000d800304440d091105445c0c19400c4100750301140b00e00d0075151a80002107138111800b154000d003074281e04d8800a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 714918201 1250 714916951 714916973
    0x507080a1d0d0308041506050607060b0301151d011508010e330909010608030304150b03010203010f1404140612150705030601180305030306061b06070e0307050a03050a0609 76
    0x6800460b01180002059001461a8000d07030240604048a043c400c80510603a14680151a0080414411038000400a800042461030001c0008c51981d090100100d040700b1340703900c01c9400301e1916084a103030301c08015200b400b6161360010000519400c0b14080c040f13510611590010441180c00100322089641ca820b1000301c0c00d00c1040c0e1214000f080703000074034038803082e200e11a02c10000803889603a0144501811510800d0103142166200d0300d9281c03d0705500050121050b464150004440d5028801107000c0c0c80c10040d121502d50401c024400b0310031502c0841c0e4007440c03802203d1844042c220309650340c427560448216140c084208425420460200d0040248490900900031010740107005184246000e980701d00055a4501d0840000c0d103c1c1e1201074103540042000c82c1d45420800004e00b1107400d008902d40c00764030303218015450a00222510000540d4074641070b081850300b0b016002c024a17003210f240e5140d50454441c03540b69036212200070100340d40c401074030003008010707046 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 714919451 1250 714918201 714918257
    0x1003120e120f070602060112080f0c03040f0303030c05090d0b1302040f0b010212040612092f01080c090109050d0201171602061024230405100507080a 66
    0x3101c00d4a841c0c0421007030351080360209007041c0740240d8001142c1c1d42d2000901c141204c2004c8000585041242c96030400c9601c0161900150a010425001d42c560100000c01c0148081c1c0c81e48480b103407441c14010100d8015448540401c1020030064059a0b10580c02041080e04000031443c151a000300085100403c100002e4005041500c0c0d00c0040e1a9680b003840c80c0082a02030350882103103400300100310300c16030041c0800314400092904110115078004046184294940c540507a48025a00d114441076911301220103800889203005503400840c542e0003540d403048980c00c4c0f40d4540300203003036882e141c00740d180546035400040c025680300300601341000e003a10400b8000d6050a04e6200030364004002e8560152150501081408646110120485130a00c0c4003803800503065890348810340502e2210420000075440960290382c5050584009210000700290365034504000c0c403504010409a9806003c2d00b48480800b050103181101c1c0d90b02c20318a003e9400444844000020703600e0440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 714920701 1250 714919451 714919459
    0x1602120129030106050105090d200a1511010204060e091009050c0406031112070c060609020309070614090d08070c081515040501050a090e01180309060f081003120e 72
    0x4140800c100031401e10304440400c1d8001d01080d038450f8015105403140d0b0b80100d4101142d1080e40021501c039034820400308090051030035030011b02c50b0005803000c0319a000041c030300e80100c109030b904640100c2c80b800b10080c0040298142403408030003420700c460388000d660246510600289912001e00c00e903101500c1c0303c3c001003083c0c3c205a29281540e030400d0040501080c44e140d00702140c85c13510404d031114585d085040d05a65030341c00c0b2049030551b10781c0d8421030b10992900300c0862110400e001951103440c42ca801000f03000e1404100401d031102152000010520812010b01c8603190309060040301c0383c0050041d542d6640c10b142c06400540c8a6102504d03501900b1200424044c4000165000781011040086e5181c0c1480c100021183d007031041640c00b5150f00780400651210740c001c11107188801e40002280c0c0600565072400c2e83c03200004800044030010f0500c911178101902e201440e0040c544200d0710319080750310300c82a5085007c00f81c07100f8211881c4110080c40348115050f0800d002d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 714921951 1250 714920701 714920741
    0xe0d02010b090106050708041202060705010504120e12190f0f030201060303030f020c0705040c050c15100608010b09040f0e01140f060d02090a0b0d0b0103050d031116021201 76
    0x10400034000c16192449910401c005400090424428000c3e20781840e040644d40e80760528000c01d03100b00d00320f0360ba802c98001c00306010000c0458000e03c54684a9800f0b403480080c808040b80c0010588100003070a5441602e8030500b404140100051820703900b02e040c0000d10700c0d00c0c61810051010b902604000f81000c403103115160405a06400010889101c0e84080c04035600503086a03060717002d0103a0000040d40940070400c05803030701d5040500b01907452305040c0d10b04610098824201000c4a50035020180b040c0c081c0400070700400f20542c014540747c5010360155040511150040c815002040d21642d110940b0500d01550b41c3e12100e1440000070003008844403034030b80103010650448070844481d0100c80000d40c14205050780c064150f0340100261600d64031005c030b1400078540c224440340c00501c0f10680100180e61240011301950080c801040540040c00000341070f1150301405462151040c484491500a805a40381426034101d81c1c6401231060b0b12840da004102c40200110080450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 714923201 1250 714921951 714921973
    0xc150c07080f0903010f0e0a030f090b0703090806090106050a1503060e0906090708010c022104050306040f1202010c0c080309010f110a080618060607050a020312090108100f1403010e 80
    0x40c001040011001c4c1d00902540c440003401508950900321010f0301c6400038000c035400a4811640c0d840c1c40711007030804040c0d0a0312000440403a4200140850124540e48001d0101c8002003140d1070307000d01100000d10a0b2424103010612a10491140c4000310401303010b050310503400394200c10003403e1f2550700c0304001d20b0300b075001d180e0b80c100650341008a40036400c4085104001030080601400054009282e00c0310165003150308141c0d0440c16550a1720709000200d0513541c10f101842c010340c05040d080200b03506034100320008031340c00c3c21054203580c54205030342056034010390395604a503042180075403240d90300300d0700b58050080b4110101e055072038645000300814026028103200c1820ba42e403a20b49581d00401d014051211864040480800e0360000f48285003a234020242181f190341590540315060f408289461003603161032001190103d403203041c1e035034441c19481d40075055944002841b8607141c120301c209000741c09190124810000c1c0a111602c4c06d41058013009255011540c0f46207071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 714924451 1250 714923201 714923227
    0x1a1c0f1203020f0d2307022a0301020313031b150209010e0a08160e0c03160c081303061a100f03090803010803030114060406120f060522060b0c150c0708 67
    0x100000101080751601c1c9085c03201540d484540b07215000ca0380041420702c04078203603054101074031900410080d00040d01003109803801c0c00070310301a4880700d604406501144c0380182444d05083c0044080850121521000c5000035202d2182c50b03410210040c0d4039500200100e40780b0105020191b00a0446040024524030000e2110b80780080740c0d06203059103846000c0d6040600c0169400c41c0803030418008100000c0c07c00349000716841c140c1c200715075180d044e03a5070041140c00000d002102d0000750030003002400f40c03034054100012412003011541541030400100c50011401c004400c0040a039007103481540240d1044005903001409aa26903955031481c59803070f4800d01030154449519140030503a42001400d07502654003545880c00711030152007164004203d4640c0ba045c82507240d00b000141900ca80290303850004c1204a2102c4541d0b041c084002503408580c04269070880c100041560000042004200b10302c8450004c081a110200c88078618060b0f13a9002d05280f80020300700d0503500d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 714925701 1250 714924451 714924461
    0x3081810090806060a0f03110d1b0302040b0103020c033901020d0c111e100c020a0c050a1404110409050c0301060906080417090a08011a1c0f1203020f0d 67
    0x642d0350454440b5502c1c00b0600c24070b00700d54803074069556800642400004c40302440748a414101500c1c83c0844c545a407211803004442545024101d048401d003030003076003814007403052131308000e0070103511341400400400d64a22a0b10b07a0707000300c2c00f24040e003850f14810300340113031650054a0070441900c50340c0104c0113000350311200c0d040001c4c41c82d0104140445000749514035803100800094012050041c4400c1c81e003011075081e1300c4441c0541034594038800e0281c45410307152a410fa00034460500c0e42d20b803000c01800f19401903441000000f804001541c0705140742089100241c0e40410495000415001d007405a17400140d501d07400c0108010a4000d5600618100c8105035210300d100c43d690f0206450116050710f000d00782d41c000141100f12180c0d08002080b00b41e802404480e04581e031384881c8c50031140c12000d0a400720008040406603132408003d942040340840d212090300c0c00256131a03120259520070010000812211107001d40c0d8020f5043c1d034041e50038030b41003695a000348907074000185 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 714926951 1250 714925701 714925709
    0x60309030d050a270c050405100303110606060412020a0906031407091e02220e01080d0e030309010e0a0f090f0e0309010e040e0c1201060e18070308181009 68
    0x510b0b0030001001c218075809034455242c500307800c0404514080e2111a150710000100365030001ca41e680005076a1200e00c00c0d2489410381071481250903046182c000c1200320002d030035440990280e0184078980d03036010304844c1100d0b0b88034080d010400152020601c0c60b40c89038001400149400000024040710001c0710124002e80b1303081d07425013a120102e600844480200c04915404900c007142c000b45210350041c600c007801c080001c2ca1345080b80442c1d0391110241d4028907014880b5500400c0040010440c06e4860440c0c0d04200802d84a08400709541c1d0081c1108c0604000c40348852034029240c4002c80c401414210000141054132000f00308040c0188016451246160400740b4500d00c0020007629005c0205a46201000400d141000040c000d1540351505600410b9814a541d5131260780200b40d81e15481c0c00421014580821124a0040101031110f200381d4243c840c0d030b01c41e80c0803840c1c80030340b41c1c00710a0540310344050a00107458242c010b0455006122280740780846c030303040002c1c18112 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 714928057 1106 714926951 714926977
    0x21050304030c081204051c1d06280c021008060f13060902070f05071205060a0c0c0c0303120b01051905071e1b1e09020c0a0206030903 59
    0x1a8060794101c4143e44480c0d0b085041c07504101f0700200c804010b003803070900e101c200b012001214001d4003115200d107c002908259080001807000c203000d1581e40d803825400060fa101500c844400901a4490f001c2000554041480764211501c01c0101401c50480e550200c01480020071540140010141e111032020030286118405810140d000d440c013010389084030304003c1d041081640000844025900010780070805c00126a40c00403c0440006520303464140c08450045d2001001484088c61310b50000a059000d60041c600c4001c081003002000c130141c0041d40e2a2048186000702000e081c408200740c0340c0a1001741a609000303101109000001c414070111002d411002160320a208030101c0d03284640d403c4022014100001c0424681040700c500700503c41c10511070550744640005070100000d00a00000c0b002c141e000e4101034490402200c0282c80c0d40000643c0c1c07410b = true := by decide +kernel

theorem cover : BRFrame.Cov 714748201 714928057 := by
  have h0 := BRFrame.cov_init 714748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 714748201 ≤ n) (h2 : n < 714928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
