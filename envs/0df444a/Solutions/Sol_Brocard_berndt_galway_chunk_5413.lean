-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5413
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:47:21.154622+00:00
-- url     : https://prove2.me/submissions/ecc4c185-a0dd-4afa-83ba-d4e702b4dde3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 973381294 ≤ n < 973561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 973382544 1250 973381294 973381309
    0xc07052e020d02060c0706021204050c040506010215010b0c03070503030c04080c01080405031812011109030c010e0a03120c02060304060c12111b0c030a030203250b010506090a080d020a02 82
    0x80300340d200810188030240c034040d5403110701520b001c03e0100d001c201c0408004454040360b010300b000c0c04009825040501d40076540d1f40c132020006118508080005400e5440014019014031070040c0c0b04045901e41090350181d640b00c5540404a804104210302c0403c3c2d081006501600503030300410742e60b03460607070107600b44031985550904206288080c030011a41c00002d843d032000d0800e201d00019005000044d6540407032a0400c180c0e5424040031050803003840015101c110001c1c1d058510110b0b5030710044a83d05902d0b0706003035104101803401c0c00421002450201d42c041d0074100205220b0085e00002c000341c00880301110000e44a040f40066a80d000c42c181104d2400001d0134042d09089030b011101c80e001d1041c14001e98441022803400c4058108988001a05d001d02507170302041540c03c000f51079600920030140c6900c80719050410100c070a2130360792040c2c1e4000903c2c0034139900b80f4080007440c2e40f00d524002da002d94684008250808180032a5842d04491340092080f442c1d41d02c1440500c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 973383794 1250 973382544 973382629
    0xd0c09050414010b090606180301060305100c02120a022107060f0209040c02011512081c06170a05070b0715050109021b010207020901030b1308190908011a060c0705 72
    0xe85a19002c0c09aa51222000d60304103150084a0341401c0b044c02300401d00503c0c040e4005442072041001c0800d440c142544504404140c581c01e80d007560015010070030217449024842401030340a07540d511030740d014103480380705038920355241c0382d10b044010703100d01050310f40030044182d80c1c50f0300051011032840e00340f01e4402500c0450009002c00150300c2c0c1403540303014003842502d003a0140070200b038080041841c12681031410280b103581030039070f9401c0350714014403290140000c140940140700701d078042e00286504d012039100c0c0c0108a01c42c108413170b960b03090708200811200c58500e8440554400c075a4080c07a8042c1041c0c120040c0c460b034100d010030000c180b00c11a8a102039204129000150b15111259410749400075502000d81d159032080c041c85010b43d100203441c014000c54102482801c1e8003000d041c8c06450754445400a0701e07081720900702d900000d25112180e003541070050003802d051001c0d0000001e50b0050f2800c6681da480070500c19540c40d07045114810703400c4d08e40c41c070000685001d01c8a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 973385044 1250 973383794 973383799
    0x6210c130e04111003060308030c0705010b09040c150c020d14010b04060b070f0201020f1005040b0f0903180109150c17040b03010e060406090c020d03051b07020d0c09050414010b 78
    0x3410103444090465010400305401400107130035182c00703507000e80c100c04029a4481d40303003503407450803030166004d44c0c00a0720110395035420000540e20600e040b00d10503001e50307008480725140b0b80c0380c50100e100c0000c1c907143c0c00e024003007080703070140141e56803581c803000e1070303000314580600c2c04011f1204d1740c2101c0010040350b2107075180060500c0500c469070140c4410302e0380b01d8047e40b200e601d10300060340381c4001d40710303c402284120b09142201d80c1d01d50304004d010700e108980310002600c0e00b10031180303010011100802198024400b2401c503080c0d444000c1860101810b054054a4032010052004520501c00c0c20125500e258110204010102141c00c160a441d40c12420242004c0469040b44030622401500815140108009540d80d50001d0700801815008000e50007003000b01948884007100b8600c0841d291070001006445448160039049581c206000e180a13075580c20400c5031007580c8015290b5405105002c01d40595602c40d40340a240941c00b00c0d80b140c24031074038050030340e1002c034841c90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 973386294 1250 973385044 973385069
    0x604050c07030e0604170d0e0315220206030a0b01090902160b0a0e15150306040c05010f02070312020610060e0307050105030415050f0702010c08011406210c13 70
    0x3010010388800d480c42541d2500d407040d2040d081e280082c019006a400000350102d003903030f10301088074000445210881503078580d03148211109040540700c129084180107035007520000149008244210703c07007054400800d0440900041e008107000d40c000b25015402141d89080c02c4180b50b8010410394020201c00006503d04014a8403d40b8118400c4000900240d001004504800700c9500302c0345102e0503d4044410a0891603621300c0b403544140d031400c18003e000303901d921a509020070f030309214542241804280c14941801101c0008100098100314001d40d800840081e0048800394009121580200f0036030410407205c42d80c02c9480d610010900034004c02d100f00700d4038086240011141c003403d102d6241d680da41003034006e603c00301d00100c03107203841d1500300070880341d500000c98003070358807540208400040d50000355aa0103081c000d0f2002e903100c28102d044c840c0f410400800146400d010840070803400344c02c8003c000c1300241d0b01c89039540000300c3c20181c4010030a42c501c004108012010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 973387544 1250 973386294 973386301
    0x60f1a151c1107080703030204030b07050c0706050a0c2a050612150625060501090b0303071506080d0c12091202040b03030c160306150e070e010e10080f060405 70
    0x2241c0071a03820365618103074546103030001d0340324100280c6a8150f0000550ba5642000345001002544240021202040c0384400319030385610800607181d541d8813500040000a0504206981a401901070001081364440d074800009200c1e10301034140da02060800f5000600d900742e11041d401054009074041d010521101c92441581d0b03c5040e0030031010000008d2032030482011600600c00c0341520070200724042c4040f840d07800064a00c0a695008140400059896a041900f82d800034109580e05610500000002c00ea0610390501c4503a11801c002420a48c0c0f40344103400c1c400500340b0903000c00d1241d18080c042c06203d00a02c0c2d502d412038a41401c1250038078991036011894001d01038090781d594020311410351800c00455407020513030421070f90502c0c0c41300001c0035581b0081c002141c00c40d04148004100000c20904007041d1050590320009550303900200b00d40c01100c000480d070401010400c0c40c2d2003a11546981d0b5480d10844d980d5540c80d241c280322001e80f18501900f03680c040c0303140c002003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 973388794 1250 973387544 973387567
    0x9050106052a070302060307111006050102031e040e04050703050d020705010f0c03030e061503010b04020309030901050d18060f0b0a26070b0c031b01110d09060f1a15 73
    0x149000880180e00d60307210a20510052858000c558100a40281b00081031180c50303504000040c050944802c210780c8026007410a95041e15030902c203d40c003603841030114400c68044180340d20041040c125080e4102030380c07640e005005680660341590b40303030010841402402424820f13400d0200d25400104801441c1400090922101556440800088515a0b01050300c0b80d0000b42d02c1c45c8100045071900e0401c0a60264515031010101d4465842c1000300032a909150003900d11601d23100c2d019500304841c0000558945e80046d94034510300350340d03480b0b0048650300b80e40f0460310329002d420009125403505003034a08450044540c0d41c071601e06204100040d018489100030820568482c40a442d1156440b0030324003085a000340040c20310100e00d0701d19400d00040500fa04600315950540c85450f50f0101c2d9089a0390b440005100c240204040c2a40340314542203d60018400c0c800003a45110300f1100d40b080b034590110440c8608292404901c0500e0501c8180c6c01c615a6008002e1600030000d12 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 973390044 1250 973388794 973388827
    0x1150e13020406022a010e0d0501090c0609080f061302030f01150905131718120a02210a031803150e0f071215110304060e0d092303030d060b03010905010605 69
    0x10f117181040b01180ca40c0040d42c4400c1c46c004c1302d4a901000901012003145070400144241c1d00400c000940c04802c0061424400228615204032180181c02540c990885d500108000414280c0c1c152003000302c5009000024030600002c85000d50400c80118140000042695400fa040e841042c00180c42d020105402603403070760342101c00c001c54590f40c045410400d240d600c80000030360390051407065030010b07000300400d54200c01c0d842294415081014030426a1649405500302c5000d680300585076400a40129045050340d0302004001c10620340e40c1c0d60b5100141003034071841040c291104030003284240100007015561b1304510141c07a8090034500740100241c4e1154020701086918104840005441d0b44451049610040200e0b0780b0315250034180c02400e44441440c08621480040304245d030701c1040c50009482100710002a09640c48084c402d00107203032050325505000c10088552803180c28496100202041200e0f01e49039803428004c40203c9a05901a80074010204040e03245c0c5020f014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 973391294 1250 973390044 973390123
    0x1061115041103010e010902040e0f0601030305130b03070309030e01020d2a38040308070804030e1905030601050301020708040b0f090306043801150e1302040602 71
    0x9185a99600c0c14030381140c0e1010b00d801a015440c0000d00c0c003034a40190031965060340241c500703002020300182226a60b0000c0e006001c00c0703820a000605c0080d1251000300b003000c449011190b825511041c84d03a200390700079148440800d6031070714400101030f00101c600d0504482400078200559001d000034089000c680c100c06114001c1d141007407900c2031621490201c0c9038000b803140b101e02180100310a12a00252031795110300c44101600101101c2030346c000c1d07102d03d9041c2d403041d02607100c0120640d0010b030090700c100c061014000d0070311001d032512050f40580c42da50012500d802c514200905062030b60607040309010ba4010045000402c04c1c0c03c1c01c0b94201d0b0985040d4030b554003482d540180e03103400340d6490035505020740020300003886801e43d202108541c072111030b5000300e802c00c50b0358000b820b5210741c080800c0c9103900040150034544c0b040410f2104050070231404108048002030b80c2006490500c5001e50f9000c10300340000e0b0307410031100701d03070380d60034030440e100d0140540d10200d8114280 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 973392544 1250 973391294 973391323
    0x60f0904050d0f020a1a180606030a02010825020c130522020d06141014010807082d180304180f020f0c07140d020d0f1712010806010611 60
    0x50f51403a040302d1082110303581d9543c00a02d009446001c210180030700c0003040d1081d41e5204501c00c00000d85480114a0345c4c010107000300108440c4034154010b68003a82c000708000c400c45000c408a0300c500c002c032000d000500903e0390144c56400b040c01c1c02c0120310401000c0c11a01e540c40d00d0300701300580d1820410b810300b0708404080c640c03482c481813002900340ba4860340010285030030300304012501c2106081c01070060810b4030090b440c1d036031105071a5036010343c00b06203180041d5658000c101c03010300500c0c003690080070510700000b20b00580c100c00690302176180044035a03138800d5410810054400100c42941000c240c02841c60076103410016a03411070901c2c0c840da0b0040eaa50800c0314802281c0d411145500c0001030419164081c181d4800c0c1c40b0309092250801010034002d2110892410820001e5002e034010b08140e1041c1054440c00c1840303807124011140128086001c1142d4a400c00242100d400b881e41c600940b58103050101c3d01385181a4856414003a211040c2a071030304000c100640d448060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 973393794 1250 973392544 973392557
    0x11b020d0f061b02030a031103070e120304050307060512130830010902430c030206070b0103050c0a240c1202010614091308031f0905060f0904050d 65
    0x754184000100a40d888150003840a410a5601c80d9004000341101c5000c60f1030411106225006c6030b1514402201c0c0000000d03d6842c1c0c0040a107842c4944101007462801200d0400b41c550001c2441c0c1030342600902c01194001c0b0340e6410301030729401803d81c051940310090b58454050784e100030f21030040410302e420708001c0c00300c9008103080c40405d846603a082d07500407403001d5a40b000660700945c0020b8020b01c2c0c0450110b0004040c1d20070421121103444001c1d1001e10324464107120300c4801c116035108440e0040340120010150351b0702e80142c40641d029501c0c2e0030195244d031030306903d401b0116543c2401040340c004104410035008401441c81c50601040e00444090048100d0b91040804c1c070081209601e42e0f128001281d0560003c825190441c41540041d103070380e41006032200086441c444440707211503c0100050361040510b41200c03a201084100b841100700d06488449190041100266100d040003520b2404060810418030305035124002da0801c0c0c0c50b40c58a54a02800503824802c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 973395044 1250 973393794 973393823
    0x40509061201200d050f09060115120911090a0e03070f03020a0c08010f0b030f0d181205010b150310140112060308090a080d050904050406020c060403030b011b020d 72
    0x5080d04488050100305400e110040403c0803d19401d0300414020880b00307140c600055284049042c0913030040d9055402420700780c0c42e0039502c500a0b45203090309801c201100c10300240111807805002d00c803d00c035035550080c200c060010310081900013403886100310304085000403c0d02001c4102e41116420041042d41e15006003000d900c0d080e0081001450002c2109000a407100d043d0f002440c1c8502450040c022411080c0c101507648800090021607034000240c00f40c43e40b4040c008000c04401d03001035203e202c03550384814240001c4034441c15100d6946640b00c04505191900700c60301030040c0d0741951400c0d4180480b03000001070583c0104001781c910300c1c00f0040b01d40c0c003c83c0b44001d407000c019014410207440740382c5000c483c1c01a2034514001c0c603000201280303014000c900701d40b80c0c001a0b82d46600740248401044042d000140c0251035a07942042902c142803c10720005111318002d0720b020450346e440000040c907888040000c6a030b018003041220005a075580302e07050345144c001045000081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 973396294 1250 973395044 973395079
    0x30e032415120105091006060203030a1a0613050a0605040e0610111f05010b2809090c02012306030c040e010b0316081002030115081f080307150204050906 68
    0x41150102d50100040105104180c015004640700b000a2429036000340b00b4424105c013a50124011900960402d000280000105901c600e0a604100920752012440040458000e501102000144584c5090184000c1c107001074420014403031460824a0030b803810481d124002e40c0501854820500c0d068002c00882c03180c07074540810300d9080305503104605030182c540c208103507582d0000c04603400d107000000c41c40310346401e03034503503002c5200000b90040d0002050b1980303008829601050001c1c040001c00c03030070407911862a80b47c00a400014208a2182c10380c85281038103070030039541c3c0d169107003005001e4802050410300c0603000e6a000c9640f60000304c0d0103003d001d243d010f0315058071414402d00b41050078040818204c03281c050a0f981081c0c03000544005910090203203030158261402130201051151036196403204101102da02aa141d886440b07000701c2c01e40c0d00600c00c40d4404036100c0305011040703851003020880007008500c1c261400c00898500740c4001c15503032145406805883e03415 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 973397544 1250 973396294 973396321
    0x106020304060e0112290415080c060c0a170d0e121b211306020604030504050108070c06062601150306150e070201050a0b0607021e04091707030e0324 66
    0x7001a10701b50781040014018400304074000081e44e8812801d100c80c9041102484a461003942d0210026010b0180003005103c56603002c0507410300c00d1302c1020128001700d600f6100c0031282c040c001541039030300c001c51003c0d507041d942e0450410782e6940050700d1181d108003103001203c400b03440d0855004854021140f4460808021a03040c01100d00b83c030440302d1214030b100d4000c0c0f541c02c03c031158180e2002d4940304102c1e40c0c0e480c1254020040750301000203100315030041105c1c5510502902d030102440783c01d903480006a40003a480180b500d81030115060040c03403441590344006402000811501e0140d0800041c01d080ea8880980316503581c0c072807090040003000c0c07400701030440215120080e04004a00078000d140440c0d101c0a01498581d840f0224523103a4110f40519030001d00c603c5040b0f03844812492446000c030300245c0c0c4141d465280c3c80000d0007452821035400150350000752505200e003409800341d840328206c40c0c465082a4000c4c540c400d80184d551581c2c620b04101c2c204070380d44040d01400348 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 973398794 1250 973397544 973397561
    0xa06050303040914070c030804060209151b010c050a02100b030a0203120901080a0b1f031e090506010b030f010603091a0a0c1112040e0406020922050106020304060e0112 74
    0x500001601058210041d0841c2e0380840d0080d051380f805945034a4100c4400c034000c00010000b401c620f0210700440d02e0f5130050b000c106001801d0244902d9446841c2240f0f91184c520f40c1d201d20521140c0444440085c4140c601001c0b050514518051450f00d00944130507000340c900e030380141c0e121110404c03901e0400402000c1030b8040c04036030348001002d0040e000c607085008080e00248050b07002034018403a901840f03080c004040c04a40151514110b076081d5038055400c0c0004150b90f8805d1a030315030344100c1d40b0303a10011842c4000100383d0b0482c14081d040540580010324080c20400c1401036500380c817084e0904460721894005030000031441d1140a05c40710701d01a400700c1c0044020704c4803409a942c444162640191075100d00d040781e5180361500c8003850056000c00b003009003c100080c018a80d4140c0e445840345600510b45641c0340c0015440103201c03400c4680c00ca4000c070903928440040e110701030151400340000c60526142c00002015031517601ca14504001131140c1c0078000c5581c54000146 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 973400044 1250 973398794 973398799
    0x170a1b030b091501150e1320070605130305091009080a0b2707120201030b030307030c0b0a090b133003150b2208060108030d0605040b10080a0605 64
    0x41d506025640640c0c1e03840b00a0b910683d100040c00001d003d000380304030054510301a80701e1a4024210707004204600b07501d1010304841c1622502035031020506601c003508403a6101038215181c8102d801c1c41002c642c8010a15402c401c2e03121220ba0109030000d064641003103080724100c02c0716201080482c1c4460040c0d00035201c5104825041d002c200b222245c4074400d031100c408105000f005101e0500125090100944050700b084000f4820182c085258080722030060402141d8204520b010a16642c851801540090a500750400030440118002e03608680100c0044c0b0400d1400d8440e4000780001414183c040d81030503021204104001009180c011100482014414800d084080d11524403520540000f454100c80300144a0103401c10010340c6c3c004d1035007600f03041c41a264031520081c0c0c100d04a4000e07503071340000600c1c42c40801419002c1c0c0320340c00286448194000c0c908064a0154200b144214100f8000403c56212844040e002c002107181980c4103465510001006210a4200301d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 973401294 1250 973400044 973400063
    0x30f010902031905131101020a0f0803060a1e0602060705070b0f06010c050d0306050a3f050a050d080604021c05040c05030d08010305060906010501021b060d0c0c0507170a1b03 77
    0x5403410001c19030005d40e40103007071a42d08810f401c4012138468a101d003000303004443c4204800302041c900400b855000001030111940e0301e03101d440442c40182e61402e145650701402c0424030229506209040c0c00049074142603050081ca59610410301000034140c100b1a012031000504680c800d10328103403c03d8105c02682c6400c05886402005480c00b0300440d03004102c019000a40d109030a0700e4071200c0d0300c410780310300300c45c0c49000700d60000e02d0315605021400c0d50303d095400300405c1c0d06014241401e4458001403a104122060152055400500c400d1140344181300c1558030309031400100401c0d0700e00b10000521640c451801c070182894075000b00b90944184484004526000009503058074080e20450341c00b5a9001141503a4031424018039005070031284c90203032409034000982c0c180c0d5400408a90604051024030b0084401103807500340004c14800c202024401c045c411000a40b00d16080070042c03941c1000315036510813013044000c05a46000070000103e200b08580280a0b44e40110003c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 973402544 1250 973401294 973401301
    0x406090b15090114012007050909100e010c0f0513080105090307030e0609010c0b0415051302040b01080c09150706050c07020a1409180312010f170102030f010902031905 74
    0x1008030300d6035601c107401518030900204401e04511219000943e0503034031250300340401d0b81c0d4090010345261000389a803007190000724250344e038244458031880c0c2c0c440081049034103064074802034070000d180c010400c3e4907100130012000e9208000080c50407171801c1055032070719200c0d201441c50700ca942c0094103651a003000d0020b4000d001c0010480355010b903440c5008000c5603400c000503441411510350200c0c00c541951000250310342d03491640103020b811204c01060030140b140090720b904035910003c240d03100740482d085140520134000c030201d0a28203400940b8000f0005409440b070b6000952054400e03644400c3d0000c11b620484104030f9101d2000d010720305001140d074416800162040303101c1c1501000108d4842c0b4403203450b18500e000200401140e449a02420315103401c3c2c4c20030000746020410002000c0100311030018020001400c200310054504096551a02c085101c13220090f4010014008842400c00c03015064400c045c00c0180da80c0c0300c130b601082c1c0c00d00000f02e0000e581400d04040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 973403794 1250 973402544 973402561
    0xa06031817040f06053903040303020606011106070e0f030c04020f042105030304080f04030209100626150f091905070305091005060103061a0c0f010c050409050406090b 74
    0x5041218038403c5680e1400d80c480500740c0c2c0500504488080d4500480380c0300d03404c2c464165094144400e64900381e41503603c04142d990450b4013030f802c15005603224409010155a0069034031882c00e201c1030180000341014000100a0950411034038030420500600c50102d07501031141e0003a10400500c215924004450007500c20b8005104044100c906045440001720b41402c1c0d610043c0c4c0d100380034610f59501e030350701d6600a800103d04849022001d010100050301c40380d50340740c0125261840d1140540c074001c8003e0000d0210b20444c1c1004611901d00d1410204024155402070343c40d1403030024003842440880d64070301d003a24945600c5645907050044106514105811040d50001c0510881c1d03146641074054500a98449102c4d50003c4a681890300c4540d02050300800149404542c06982c0d6110254100d250380403040005400681da002120081100038440d00c042c0009120007101080301130a140101d00c81c010f040c640b03400000d41008003c2d4000385020b075004940c1002805c02581 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 973405044 1250 973403794 973403797
    0x60b010e0d0b0f010501021507120f05042a060f0806040e011812050702100309060e01110a0e0d020904020d0507050d08071a0c030c09011713051b0a06031817 69
    0x10711000c1010303c8400491170f54808690214004100780e007960b01a103544104444540711400302c0128150789494200800b8064061140281e01030310701d80100142c01d81d00300c996840c1c001c00d12503140d0041c4208000c1180c001804000d03046d03041c100300d070700c9035a07607000308000c0c00032000100a036500e001c8201264401c070200010429005120b441104100c441d400d0f0303202c0c4138503a80a0740c0090741241140000e4401d4204500407449000d003c182c117030803941100d094440c2c01d0a6029074150100380c0e0311182d5885400c0c4a401101100c0c101328803111a0042007840501410190003030300c6040320141403280c1001080004d00003d00540c1000071241800c8c00d8940220000f2a1800e40f4102803190b0b10819100150142e00c144101c1031031600d13149070300c0c0b440f80c2c84425518144040014107a40205160412034800d6400c0502c5840c81c98061038410308104424078500d403581c04c40c459142054031070351406010380f4080e09000411002c02045142c91891b043c0004208a0b404040da581c0d5114190 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 973406294 1250 973405044 973405051
    0x21903030c0c06020a11041113081b0901030b0a092a1802030f012c0a1a030619090f0506041506060302090f0907180b04050f040b0d060b010e0d0b 64
    0xb00c02c2e80401d07403601e40890300e078200800050183c01d807200042c04185029840300820a1089001ca458410500e0060000601d251302841e100d4000e50880c2c1001c5940800012083e0b074120b034146031325030441e0750b100207021000e040c10142c603940301e0300c80d410451480e2407201150b800d0112000b01042403400ca050847c2640583c1c00321328440c103811504000a4004e0341c9c0036040c0720410b00050703030925001d040c2e05a10154085680c040000d00c5100703607064031841c1c5014050411002c0342c502448070307201c07140742800c182090107648030504101c00c50307400388035101d0610701082d0301049070105418941d0001da01e850000e8040c1c004c8405210811240040c0d406210003000307014083c2582d980016022401040001c80d0000d03094504a01c01d0303d09090103543c4201c031424100d40103a1900306034848100103410842c0315060003d03061102c2c0c0341040e1342e440d84800458090182c145000c011071305040d0700d4074000b01415200d0840d009241c1c010a807030f503038a01e0040c051110150050501065245094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 973407544 1250 973406294 973406303
    0x504090c090504112d101b150612021c031409061e07050708011b030e030d06031b12020a0306050612010e0d0305010b09060304031803050106151b020307050409021903030c 75
    0x754a10007600f04582c01680c0c111a0741c0307540c0e42c1c42e42244851a0010721030306003248c5041200d986100c1c401c4440c0f10300742c0070b4410041c8a152040b41841400080c1221a106603100345030300c0784410010b9402005000c0282c1f6010b03c19407142c030408003264042c0900200c0f8181203e02c1c040031152001c03004054128540210308a4008a070340f01043e90896500002d030b104008d0050071031400584c042d8010441e1141400102c80c54002c0320f442c100c0846400782c00c00c5441604141811054840c240108400f91545841510040205500090345141e65100c01008540c8910001d06150f95000114004040b01c40080c010360130520040c60301c0fa5504019100071074500400440d20200540944500d182c001d04880c2c5561181d8505030382c82c0b51017025001030710358a60004000100c081c0502c50050035070507064100321804442c0540300100360b0486000c41c3c013440e000140075a0b4001080f404807002590001840320040c00400d151080b95499068803c04c5030700000201548002e00f078070340724001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 973408794 1250 973407544 973407619
    0x13090c0603091119091104080a05070e0a02090d12180b0309070b03010305030a0806031207051b09060a0e19020304110405060d1109061f020d0305010504090c09050411 73
    0x884100900e0180340c00c0002d8154402001c00c0c80800d9041d841b4984c5e110000103280c2c10a07a581103403034a008030f2442c0803146500401401c000d494802e105481c1c0000d02000c06600b00a94103011130711070310340103030060082d04079021414840e81c01b81480e055001c03190080400410f4a440c900004ca60042c0d5000d2014070940000051000031a03098a041c0c0307500c4000345150201440044a14010190004e030f414000d055008600c3c4030108028581c20748180043d00b4855001050031002d00f00d00480f55004220f11010043c080c0c0d40c10391620256422424400b0160701c441205100c46060747c0801801544004280014040c0c00040034003041c40840d422b00c880d070340e28814081c048018903001400100f1580e24445140b815514640d8010760180c0101070f580e1b80d41002c0001d86047c00414000b503004000308071a400d81c140110781c0941000d84040c00f2500742682c40c48400002403180340c000a80d07030000303d820042c51141e1604400c0e0001e2200300c2c45060b0b9208440c0314401c02000d40b060369030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 973410044 1250 973408794 973408823
    0x1009051512030406050706050c190e0102010605040e0d08070e0607030207090b03030403030c121704060f0b310905120d2d0e15101e1413090c060309 65
    0x780003040714250b90320740c2d07074060400000380e40d0080504806031904144007420301041400396190740e06941d03002c60b656100403002001720006401c585150700043c0c020f508186185402150010f8410001c003018544615166200d03142142c40c055454441c43d03200e03600256940a02d64001021419031328031a100304165008941095505d114605c4001e02003828280a14046031403606c101302c2c0c2c0b42d80c0741000740d0182c84010380c0b03008a020890b011200503a8400741c1082442240c07013442c043e40c00170350b00042c08660507060f01d16006000d901c00084c1c001d500030860304c80e00d000c5d007040040a62100403101844544c1d400c40c025500204c2e0f8207026140b400315a2180a208220540100708014003071344d41a42210005801500701b07400880d69901c210b144500035a050a146241300d14102d501801c110f07810207040c0c040d124010000c982010b0000759042c0b00c3c1c020690308408402e2000c0741c0111522014440f0200588954075000e811480e030807000080765601034004c2003403544038481c2941a0780 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 973411294 1250 973410044 973410079
    0x1b06060611060c0a0f05160b0703050901200f0c0705060304140624040b0402120c0405131427010204080c09130309150c0b15030f0706080c0310090515 66
    0x1401c45400700080214441500083c014001000c0039a4114200744c000ca607d038550150040042e22400f001030354030803c10014030800c0c030030000145030286d04e148185900d80c59a1055020784650100c80c084001485008030f01d0400001006100150442d5203030300d480e040c1034a25100d0801c103409240141c90008294000c005180300c841283c9801c0050500301e420705101c010b1210401194006030308102c0c0d4210b100341e030400e03a0302c9007000b803000b00e41d50303801c1c2001c1c4105508c4403208900194285184400388640d00031070740340d0010050481c07040d0011041c0452070f0341e10b1590308482d565440010042071350440801c80960080080e5140812031319044280042200700c0d550203000212035510500c500000311884074444903642c0f915045850f101e4450a40a03d000c0d220241c100c3c0c0031802503006814144490466a1401000380010078540040501a03035001841c4441520000000800c0c24410155000151410203020040740c03070a6901b0308001c000184000b40f20380d03441d103501c14140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 973412544 1250 973411294 973411297
    0x110306060a080307120306050607061b0906081f050603040c24051c0b060d050603060f19090305190c03020f03180d06200a110304050906011b06060611060c 68
    0x1984040003c41c900545903d41801d03000c076a8034501c0402d0b4030741c60002134a035241e030302400c0a940559000100c40c21082c040740f0031400309400400031b00000a20412001c0d41043c02035070700c5020007034412074200041d070420007195629008031741c0c0140302205000511015501d8081514070820040054072400c03a4059000d0040c0240000050002c22244c1110542104612601e440e03005010484110800014a05801401e080c45556544004100d01da1504000894201104444003803887c140f0421011403031424424406800e038803140020201885801151071605045503036000c030340300b115002170110001e10015801441400c08010000c0c5002c022a00e1020082c0c07801ca145070350807000d010401e29a0f9200780c41d441c2e60b80020446500070701c1d030081000700a2840d2665144010310019205518110500034558401c4c8824826600c0d0510386642101003403d08807a41d10b05c400020300c404000d4040288020700380b41c400901d041d000110980e840c2030070b00640321240ea425141c82140d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 973413794 1250 973412544 973412549
    0x1701020301151b08040b0a03110403050a0b130206030f070e0103270503090405010e01080d030b0303070308060f1504150305091c0c061113140a050f0f0409110306060a 73
    0x7000301124019100e0181d1404659501030003042500090030b9110200b06170001d070300141c0d80010005500c2499035061043c42c24440c42000118281400c60329020303030700d03007101000801100303045000c108000e242041240300d46a00800f5150390745881c10456003a201c003602c0380c8002c200e88200c082c82c0ca60103402814101c240721845141c6914070b004440f12040e8902d1001d64481c001001f4195a1b0340325402258082c04480382030307080c2549003070581481c000c486400070702014608444000c9655020040300d09941d094a01404285c685d0000110036030701d07020703242d0360003006010130202c07441c005806802150405454415100941c0d8000d40680c2d104031000c05640d000f02c440700c03500310040040345040d41542e1801203514049030b0307640001c89004402c1d9070207040010071000c01c2804503884160143c00b10042c5980c50140000100e0300861860294920074000ba144040064880e000c403002080300007002404240400d044c040962203580030300b5400390040000281c07803400c050580504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 973415044 1250 973413794 973413809
    0xc080603030a0e150903010e061005030303090703081c0e01050420031509011409011a01030204030b1902160305070c0e0402060a08040305190e0a090c020d050d0f060f1701020301 78
    0x1c8045410007000740000d1a00440144d01000f4407a40304103403024464880760020301c03c0100300c5820b018290300c208120300d034440e0748240d20410801101810220b2324604030390380040015250300c002ca0060b400075801e807608890786850140104a90700c070541009005a0140f003100d01d02c0c509184012641d03440d107040240d015809003400c00d8900e4005005150300004590000814181f010301442c07204c50b050750f001d800740e0744031111189401000c820700b00e00c180342401e0442c41c0a03e542d82d44060080000d00d46028175022490807580b6543c0b41d01104d02c4000e003040c446041d146a0316028010b038001080556a2040e80100454140b03c01e540107070103941c001307000504040c22010201e40f420380c001e00440802400f407000c03000e104d140e441400c10303400b0749880f0400e1601c407010502081c0c0904c2e40c0203424450800f030303403546070746e80224110019940341e00d400c507a11298085c0240291610120b41020303145085d40009081c46481010800e89105100ba130f54155940c84681d0300743d000030b0040c2403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 973416294 1250 973415044 973415057
    0x706061e03031b300f0f0504270e0a031202031501030c140a030608070504060522060b04150e0316120303291c0c060c05011407050d15080607031d010e010c080603030a 73
    0x214440c7d200c504106e0049821964040e00c516591890727054458890f5400400c0e40490070344810150440321107101d1002c0c600c070840c00c40c81c0c07400c1c1d29024002880800e43c10b0507611864800c810b03124005000c40740c603400081603a0f9008910740100104100e00c180d0605002c2e20b80d0114140c500780c011202112401000101520700900588840d0018040c00510b91555010009080c47c4028040d00091030000005840d0050503100907100c81e00d1091494883d40ac0b060014440442c451030b54000e880d007001e0b800d041d0b6103203440c0c1030300106101c06078000102c8841d044442c0d240020b00c841d0381c940b00d003a52030b00c00c41c031002d84c0d2015292049602c0103118444104003406120b208580340c5808a020340c0001c183d00980e10300900c0c2e4407a00fa80c5e106c1c00140002103050316481c07a8000c1c1e441c61007a2420a403003041c5003950702c90300d404020300304008160b11546801d0b070402003403240000d1910641d0003081100e5001078540c1c02840701300f0304030001c2003403000050701c24078002c001d48a041c0015140c41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 973417544 1250 973416294 973416299
    0x1a0901031707240606110a080d140906071b08090621040605060103060807141c0b010609330e01140706061e03031b300f0f0504 56
    0x180392040015414078000070050024102089450a0382900048180300020700341c0443c06805054031019003100b8207000600a54900e001000680c1015254114845540701e0034100c00150140858003100c207100300018080c070007099404600e040c0500059181c2c11034031442a450b1108101d82500d0291000a042c801705a107030800c0d400030219403000c0340c441000c564844103141c5a001081d2410f546280d0381c0c000300700680d43c25103d04400f61150030000c0100328580040813110000100040340691106055084003030600c2c0c03102d4a000f81d100d070000c0070359030715000020401e00442c810240030300303824013a0782100b80581002c004040f114801003011640302c0c60094852803442c1c12001d041006101c0340340000c030581e40240c40014031429010411a1500c65000b90880c840400c2ca00c0340e1107400c0b8100002500070520340b405c2031000c0c510b040240c88a0402004005148110210700e81c07045140c00c4c408250488042066440c9481381d8100c9a0001800c80e04914181c030584041042000107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 973418794 1250 973417544 973417553
    0x100905070c06020a03140a1505240708030a0c03140106111e0d14090901060804060603020d08070213090203120f0c03071110170a0902040f05040309091a090103 70
    0x1984205281041c0c6184001c942c1d40030100d81c00760340a00c000a9480e0341c044512561040c416400034200380e410702100300c4485021030255414820136120300f030200300f2100706030b002951340803184d002443d4290b10340b4040d00704488198800c03511440c60620700781c410a00607000384190100f52102c40000e80060f800c1074801d840490f050800920180b0036580b013116088564950803c1410840d0040d0400d808448009443d44ca0700402000c44c9500c10301441c40152034202846045070510b103041200c903112403c02c100209003c0c0c001942040140d0091402e018041000305a001e01c01e0303a5082501c180724a0fa842251101c0100941c543c0000003003210700306142c0d024101c0000c14590046c44d040c401d41c5000c0c035503032040728215155207100795000c0c0e2034544441207581e00360039800c0c00d0360007010b41c0b141301006a10040c41030b083c10b5920101d03581552a03c4c0e203c09040324841004021034180740c100688102c186200303408802e81000f034031203850030301802521b61000003d0200c0d91564216601d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 973420044 1250 973418794 973418801
    0x705152502010e10030606140301150305040f1403071703130b102705090f062403030d150501030b010804061d07032906030a151d150f1009 61
    0x30207a041088001485083d0750311803010000d41d42c6070b0b032000070705246841e2014003580041e034580710220000780010082814074035000124040f85e4070740001d49035518034000c580c021040310050103c141003048541c2c0307110300100811a40f40a1001600d02d8807031001c040300584811142c1c7d0001071071016008000a203032446003904075428820844419460760880c0e840315080c0b02ca2100b40c03e103106044940001148960fa0700440580050900d091201452654815019200b8081c00103c0400064802d80d4072220840c8400700600f5243a940c160100c0001c054256035414070b190190340c00c400a103a6020344508904458180c55490840c1d0341c3e5201e400040489801d030444810050b100c074040402c06105200c0658451102c960200b86600f044402d16a20322b070302c84d054a83c1c10010b2010310382e40080c0745d10405074000e60305c0c4008090040c030903000e410f180ca04101000101c482031581040c01250414010b01e8206421840ba87d51401260900c4801d5070040290001e0407812b1103034421542 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 973421294 1250 973420044 973420117
    0x718090f020f12030a17060a0e16021606050a17070c0305070f02090106120f0c050f0d0e06090f0f0c060405060706060b03040807140f100c0903020d05070515 69
    0xb02043c00101401d0400390460340700c0b81c0d403140020864030220100300a4940345a400c1081991455555801c1c0400381070134880142842d800e003895200f00c0d0f00101e1080148407a070702d0312401e074040c041d55103103000360481e0032000c02c0d0f10100c2c1070034003c04954400d51070744500ca607401e40e45468500b0480d850131354050b0301505055490080344c801000c096112070349058000d2403156500188075040c1d004090840340364040400c81103080000c04450320758802c0590748240c2010b11401c0d6118145159500203010f02c07044c1d140c0d14010481000b00d80207021404018044201088d640f00800ca80c00b810b803030707410000040381d103e9801d210500190619001900c0d16911503c13000409c1c64030703404420125041110102e4400c500081c0b00d07005c11914002c40d2010081e414001c2105441c0150840c0d118240071350910710441d6611110f0f5066481040a03000440d00034014030004e0368241052503c0350a0f0b40601030151482c1404440d030312034a401210303000ba42c50040c0411401110300154074080151 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 973422544 1250 973421294 973421299
    0xf011e0b2d012006010902090612041401200304030302092206050f010203030f0a0e0c090109140601020a03050702040f291011060402101e020718090f020f 68
    0x80301d007001462401c0900c0d410042003144000c01481c4000041c400314a080043d106100440807020090354001002c5054410790303c2d016031508650000710f615401402022001d0600000600050100b17007000000780d03140e83c0c0001c3c00a10ba001036840b0303040c00c516032521414082000000c02082c8a940038200010000340030110344420802c03c1107100001d07520038401e00ea0744050410131460064815440030100b1f001035421443c1c01d50301200440c200170494060b103912038400b21a0b8100601070b45031030b040021300304c40c142e5031940c2d02400180203841030300521405103004281c0329170002400540d030329416610f00c0d241008079802d1002030005041e0044101e80c032043c04080c03101160029505d4241c0000500740d902e00c14a0402035160921580e003824811001c0d80c45c0700e20880800c0903a400303501555800340ca851000c004039486402140643e80001005000c5804942d002c02c54000720f510400c5489542c500a2442c40c0807108141c1004021104c0140458010b003084060030340c0b5031400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 973423794 1250 973422544 973422559
    0x20f06041a0a200a150204080102040608090d0e030a12170a090506060a0b040e10030f080d050f06090a2a020c0301050f06030703021507060204060c050f011e0b 70
    0x103821075030040001208821803281804240102220303406000070f08581c03000e40c90344031901e04200702c0703c0e2600ca82041c00f4007000003810310125500c0050701194010f02051000310355960341d801c401400010244c030660341c940a03007211142c681e40b0805025010420080c09010b04e0801c6980b03001d60240d000c2c144900340803212210300e0b440f0001c0303000c09104048001020803c07a4035407030810305140c0d00422030380c401c0349041401d05c501403d0005403010344070b11a03104940c0f030320380a412080034262540010040050044203008120400002e094141e01d1b1000074003807500d4840078400e0b80702084a6242c1c2107141100025140741e900e80003600ca500300d440780c89002203804000507201940a0041d800075038030010580040b030400344281680700d410038443c030300d40d4244040000d48820140c40080c0c8079080d4024008e0084040204031a0540e80c4084119035444d0780d8413015104811005042d2020300032000401c10040d818060b640561030255010016107031480004c50062158410240c4c200c80d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 973425044 1250 973423794 973423799
    0x140c0a032405010215010b04140414010f030b0f0130050a0c0819020307030209100f080a0c08030c2104081515150301050904141902010f0f0c020f0604 66
    0xa070510303040c211012540825040e810140060f1a14410140c81c5121014480042048042420a45065808407000c0d2083c0c030a60f00006030182c044104200c12542c01c01e80009080110503503542c0440c0d11030400282103a94841180044000901c80c0d0000c000501e8140c036810040c0f0b10310041005038540f04071489164a0312018640501528100c880104106e002e10002004001315134800c80f8986008140da2200d5001c25100e40e000d110007801440c411000c20181640c07100980043c018141600c1d030510303039031601159908041daa080ea0412008540403d0a0030007008031040c0700050001021b48000c070510071441c205180508000d032000501c0042020380050103840200c0754802c0c5500b28030705141401e032030100e004030b040901c00d000314000c00391404070325001d07241150021900020650381707505168480d842d00c5002e42d0b040f40105126048503c0c8185040840c0d14000e985030701c12500045415540464031030040070103e024840100d00601d86040c06960825000e41183c5c240355 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 973426294 1250 973425044 973425071
    0xa0b07030e0603221a150609100e1201091a062409040905010f062c09031c092604030f0f0524070c0c1715100504060504140c0a03 57
    0x9034040480d0340c0d400070780824041d591a170042c10707082129004420303040000c0310005035052080305130240c01442c02c400354a24042c016060b411240101400c840305a150268a203802400d00090448048920b0100924990b2400486d2841104054440903521224208032114070b5504000e08c44c8a0404200700541d40c2c695014081e60306200b480085449003503031200c40140e9074181c01040f00c2660b4880703551248441425201d2050b1380c4142c0300c100c10b4803003050ba542580314110244007901400034100e25890314950100b1080c50158400c0d08052100702c020069001000314042403d0406002c24404a41c0118940e40124461010500c4583d0907550307060810026166185120186001085003200e03603080c869482141490140780390141948c40080f020100d0151200307966005102105c20381081103204c40c0e02440c01c00d804403529200e000c100c41003005002c0c06005506240700016182814007078082850490a075a04045c1e5905074a03600c0c5800c0039014030b04140e2160b2248101c070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 973427544 1250 973426294 973426351
    0xf160611130503010e03030f060105030a2a030b010c0533010e040c080f070312050d0f020c01200a051c02030c0a0f050a09031725020a0b07030e0603 65
    0x4481c0e00030084090b25010816085070f0a03050400742c00d8204008000c5100c1400605560215003424201d480351107030a04a0010490105945081900341240900c4400e040743c005c00400c2880c0e03420302c032100d6241c00460389400d841d0b01c01070023640031041c04803801d0755402840c0c500d146000701c006004100c1690b1440004c40030782c820402c1114107428401404804d2070f01c000030b0584200140403e10f450028075a5484e01c07480044c1c8040035100d90456128072510403a007580513907200602c038550b0b0f066001c100135444840761054662820803c407480f401d00c610804031500d000f46a803030a180034150b090313070940d05c0250740304904030401c40360484080c114030140d401142149140740c1c4491200e00050000005801c42005000c424040315401720362110340c8500741c83c0d000c0015100c3c201e000c2c0703801800d405880a4041b044040141a115074410000800400c5000b103c215606075650101c4c14668459004040c00040541e09940c0507818074100442d08406007040d900d58170500d401ca4220f02 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 973428794 1250 973427544 973427557
    0x21c08150d060b0f030a08120a02070609050f160e01140a05100305010f050a0b0a030b030c0607050f0d0305010e0708060f12030a08010b0a1223010b0c120f160611 71
    0xba0356503480d44000c142080500880111425030080030440d8181d10f07110024001c8118a1200c0d180b582d0008000c03ca407901640e150f81d83c019001c1c41107040603d0aa81c43d08117015008029200c1c7e1410141031040b00e00f2890110f0301c071000302e40866420415035074111901a1086904405c1c080d100080684035078088140300c40c07080c0d600041e035505020341101018019880b0f107108510b4104103002c82c103080000c40b01e14000710300740000d1200d66440880e041c452040f49207a804500400c1c488240640031940315084000346040d501c02010050342941154400e020721031b2207100c407a0000300b01c0c9009210140d0414402040a04400000c000050485044c041d4a0000e6080440e00041030b07900112150302501810001d0350518a9081005002c0e59842d906030f4841a215143e00400c2d40c0354814140c1441d545809090035036850345400d00c0141e0184013112410700c1200c41a1844980f0402078800000000005900d4a2a084201003101c2c0c0d04410a440d02c6030f950b074a030142c5441c81c0d0000c0a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 973430044 1250 973428794 973428803
    0xe0604050a0519150b03070902030115020c030303040f12022a04051e071d03070305031b060411060903010e10151703120c0415020a12021c08150d 64
    0x22150703180460401201c0396983c2c5008003e0034603400042c41c078030015151183e80303a1000440c20b80e5580020b182c00c1c0154044004244000004074115094011580070818141c0890748044120303c1072650302d12044070060482d40114a45ca030014016127000c102e08901e62048541c044a2484180d110481c6402c00803002d661809642150b0b0805000d07150748841028004403441c903200c124554242001020002040714148c1300c900d4030060a0401000b900d130141c1121103558032072400b1036036075000c031320a0760205400301c2d1580501600090494402c039409a8400755891484007444195002075410a5255407100054030144008010407540d0b0201200701145046501c180d01c40590102e406c8000c0b070043e010140c0400395800012101184012b41c00c1103065511410200c0d124021900014420403d895209100a03800290441901c2c0a03a0700c0d4000b19890b035200f070780e580c01c45c014031282e4a4445003010020600078072190390b00c034041c07041244000c0350301c07400604e424050040464 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 973431294 1250 973430044 973430053
    0x6180a150501050c061b0c0f03030402030c1c06023001050f030102070804051009050a060206040308010e010806040b181f110909131a07170c041a07060e060405 70
    0x100008900114000140740c02c0c01d04a16008104039295110b43c001440400d43d071640c400c400048210000441307480c03082c16010364600341e20484086403250b005540591191007218511005468400844515031080c0c01d03c0040c1100c8030398586000c1d40140c1c82d915100941c4019003c82c600000c03e8a048000c0d0b140c05901083d0304003420448003078281850745010703030702c184800da00186e00b110455099950403100591070030060102156545202e40204d904504c441b940002c240341c0020344640194481d0300e503200c031030382c0b07404141c0701400c0248540c550f554400c0021a002c104080c0c140c1d90070031075440c1001c1c2892010608649403400c0100d41080b10380040a000e1f44940461094034448004504210702d0901e00c04000362040401601c454642400300c8034036020400c0f0545501110f03d0003070103006242c98112806413710403044800002101a2000074503041d488508803001e5890303500b058aa0343c401d40303800090070341041c502200c11640d10070030151408001c00046100da8030980050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 973432544 1250 973431294 973431311
    0x10f0c1127070f110c0405090a0c060906090501020a24090b150328031803060c0c1e0b0c0c12041e1509030f0302160314010b0604120b06180a 62
    0x400c3d0000790741c811420410318500b44c0314000000f1410619001c0111030104040d20784081790b600700010100002c2c100c540c50700001410540269101c003c80380951144d43c0416990401aa102c0070003110050802c5901c0c44200c0344054042c601d070400d40242d1100082004440c1d071250000c0a0a480844010309a420940e82c03502c1c0820200d8858462010070300140050711851525400341607000605001d9108802a81e00c04130011030780c0115004070050000781401d942c0500291b0038503000380c0d13100010107001d10201c00c84415035903c072584043c03200080c3c0c0e0380e00300104042d009030b411001c1e176010700100380190350b64500151014111500d003070200c09240c800072071265075017903001090f184c404440c04a075642c0c22101c0c21003200d811113550148160ae07450201d003458082c0140613881000c5001c080180419603030140c000b04400070003045010780080402c00c0c07501a0f482984111008260900002555109079070303048900580841510014100702192600d003c039041e500065039403984 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 973433794 1250 973432544 973432547
    0xa0c02090c13093b280f020d050d1e08041a070507080d06092a030f0b040e060601090f0e0a091b061805040504350f030114010f0c112707 60
    0x3c0c0c115075540c10045c144281c5501d0059030950a1128001d086803503d0007860065448030420f2501c920390020030303038400341034600f8080e0800d0710072507004891001d180003484055004044040c000c40d08481c1c1d00c4c2c050941c071141941001e030000c01d04070801c042801000c0c000740f4500058010381c0304560300414280c5c00c0040c1c00048600d4040300c440c02c0d494244100021030101b50340c05026510a01d008188052101d40c0d00000c0d108141c0130f0307500f103845d081e50100503000c086403290142c002607a90580c4255a1340b81014124001d0003020042680400405e0b220121f50703000301c401e030741309940c600660000307030003640c400041c00e034007c00c00703c1c10503d402960124600c1120024010032501004541800c0d1611540a8404c540850030082d80589040b4085000d43c8150114201001d0045c0d9a481c4608400e140c0e070428401c50400d00d8180101d840c1640c0160b400b0310801d42a81d4540c041d017416030720380a41c801080d0100903040348401c03c1020050459124002c00351304400c44509003070034070a00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 973435044 1250 973433794 973433803
    0x706050f0a0605090406091a090303040302100c1b0f0b100602010c090e07030b040605130f0e1b010507110a0605070312050124140a0c02090c13093b 65
    0x800740755480e14005001c25911004003e4119401c01d1001411048030f00e804003100c4c08084268030218894800c2103880f80b40080150301c40c030701c00d90036104012a0b84a880050f00d00007990711021841c024100c10304d07101d01100302d5410358080c1c005c0c20500e01c0d41d5200da58540d9400d44400c01032400c006024400d403902405094090341d01d900d0324603000d80c60407042120700000a4001410036833268903189840d130b52900058044c0c10002c104100c0b000302c13111408000c001ea03203222010b480c02c2c056080300c008004980312095241c4070700d900d4036001e0400011078459200c1d130821291442401442e02003034641102c80805000e00c0d44641d56524028180a8450b0b1001c030925103450341840e0050190303003118080c50f8103d04090590540d0070440850a4600660b40304500840180101302115400d40c0280e40300fa45500030759003800c1d0754071039000e0170507036204030740b40e440c400001c800d410403a540d5140d1104113024148c3d113040c100e2048244c094801680c801060261a41440c2c0d101c82d8035050510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 973436294 1250 973435044 973435051
    0x1504021e061e1c2705030a0e0303090a08030a0e031903110a0f03051309150b0a03060905040b060a0e010812181008090721110103091520030915100b0706050f 69
    0x38156003107041d62a03686e00c0c0318141101c0c080007001d0007807240645041054440b0743c1401041a01820f450700c881d95a03a40002c0e59503c0042c03080194070240c0c1c10042400b080c030600d544000c1c041000301d0303202514040c1c102580380c029403052454080c041019151031400a03407099894903540d0650407181070201000e41c001d0b8104914005400309441d805c5482141103c1c007450496440c0d43c0d00203420b400a050f03075480305030f200f41800d04001c02c11400445041c800c1034112425000d290b110030350113001ca0340074043d003071503030b070006084003040c21041014020025500c5800c030620304584010440302d03c040980000424600b400f4024a0300050040001a040e840c0000309d211441c48a01951102c05100241500c00c814a540300164400c0e000001d4194002d0808680f22116036441c0004101c1e81052000b4003001c003800240c61881002141d020300942c10081025412a040c0161b030b41030090062400d0720514500002d42c00c01c450058030b003a5000d44000902ca14000c2041030f08400002c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 973437544 1250 973436294 973436351
    0xc051207050d050c12040308043212030c040902031b16120809030904020c010f06061e05031005090907051201090606080c150313051504021e061e1c 65
    0x40c090b0080d0341c41805e6085a100b50185042206070b1070720700340b060203072407800c00c00c2d110006015070075146864001003500c000c0e0901c904864035414451140c903c94017095600108004040000300003442d0305402440c0c00804180484419036682a50002c0039408a40d507054004020041e000910031000303110a002c0c0098100840342e81f40c011010b945034401c3c05000b41c80f0b140c0c08210115545825401107043d44421042000040d440f044050544140c0d0921121041460708168001e948540281d07805075144a0301c14510a00302410030107060b900030038480c034a1040c481c00190750f80e14014030910150b2920000100c25156007880c4040d20031a8202009640c054200c43c002c82d00c51080d41441108900490f54580d01c07841c000e03041c2c4030250000a0143d00c100c0222400500c0c5a2340b0071400f40303100b00d84008100d052a001c02102006d200501079000505004c0100f0b1800c4074148402e4000042d0780312440c001030070a55031404c0d201d029034000303619503c2924080a507480e10403070b030381d40840c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 973438794 1250 973437544 973437547
    0x9150e090a0b010e0d03090323070609050a140d0c170c03010603021c1b0618050d02150c0a0c1203110303040b010303030b0d21080c120103060c051207050d050c 70
    0x10b00004c0c169208200301a400f841c071100001c4281407041c040c010156901130101c07203006401d0384041d1040c0407a48000c2c121801103030400518a03015980781001c80324080d02c0c000203c0d10301060301d90008001c0507030541118400c1290400142070f00303821005801e206000702d802d01002d912583c0b4050b201c1d10414001e81c50b201c414805695143c0910a100840e201a0210701d4642c0c0703001182e20103104094441c0004903000401c800750040001d40b000420403c900010079581c5003000015005034801a401002030607090328440d400b10300401101d0078000855540d80c0e9241d50f02030114140e6031144103800700c041140c400b0194880280014502d61000540c114202900c41d904c80c41b0301888002d040c144d40791008139194581c0346150422036085403148034000249000340c1600c18842910f280007c3d921000140c00f0440300b402d80e5541042e10022a03550b0b0f0071503440500030803004400006205051180e00ba200c1d506c1852a40316074019030301c0d50340b180b000050440c10742d00040c0070407201100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 973440044 1250 973438794 973438811
    0x30712061a120a0905030a170a0c0807030c091a04030203010e0d090e060d061d070b0415030f0213060906020601050d08070b060f060c01060e0c030408160309150e090a 73
    0x941090300e480c00754203540c194943d2660b0031400002d2102120042c41c0b40408034007440320940100007010070800c86110043c041d6128103c50742110810f01c143e074007046240c004201500c0c80b03640b103900102c0d80c900381145584e0711000780d005174899480c051100c4017000142441181020b008121007051004001c044ea40c0d0f004074090460070050044529140060001412684d11301c90048040d40d00410108441207400e0040480740514001c0c0050601c2003001c0003602a0308042150f080750b580c0070b88101011040c240031005000104000c802c03082c1c09000d183d8032503c2521050700100400d807282d42d201d0f0b1034100301074202481640b18500c60700b030001340b08012480040c00c132140581d03c04407180042d41e0300380010702c0d04112a80c2098000c207000c16100084941540f140040c0c41d015815440c840e59456500c600354401210700601c010024000c81182e105981c5906580b188281400d4144544070400c401c01031a0f00d20042d0009106201415000c1c180340080c103402207101c4206002e600c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 973441294 1250 973440044 973440089
    0x150105030a030c03020a06021b01050601020f100b211c050a090605160b010f180b03031914030403030b010f1b230a06020c0d4103071206 60
    0x225400d000d403c0c408407800b500704140c824020450b01381e510400840d00d881340b00300541c5492403014141c0351250f00c3d24011030115070000440c6450002e1400080c0b0001c00204100c0e400b610040f0a050f40100180211104c211a074455106020741040014a011f2000480310b03140801c0000c0804140703d81080300314036440d4403020420036180f00e03042040e0f8452000319034140796103545078087c0c41100407000125820b52a00d1100d030883c1c00b80d0000b016007513001150841124660359074142e05900070040c1482d00c0f020f52181d402c0101190030311200040e440d881d08811035208a0701240001d648a000201e43d68010403a0a2092070501c0c100c0640b114a800407141d5a1005d44040e0525450181c000c2c1d04051800980c6650554a821388401c1102490110081d4000d04202031250240008003041d05102e0480c034008000c004610f94500141a50780e0058001129081e5002e480034210656280c41c00d44003c5004e01001e17580c0c980119102084002102c0c495005032001c83e010700381610005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 973442544 1250 973441294 973441303
    0x121006090303260907050102060907050604050d030c020d062a050711040204050d081c1407030513020a03031d0a080c120123070806030c0d1211070b0a0215010503 71
    0x1a80e01d81804185503001c00094110400d0303107103d441c594030040c0100952141c012416504484007030b002c654150302c503201100e440d001540141c0350001c100340130401c00307494043c3e4440d14460081c10034080c40f002e6900464030b40e41c048501035484980310088088d9014030700541803120040994070181e44944240014050320400310b010b0034204c02c83c02208040e0b9285d45c101c40081c040100030204013071040c5040950b540251080090005d512141420048041d000d800b10760807803140424060341d142141540180000b030099074011180503da000103880703107501100070f1070080d107511500d46070070080c4814000f402d99207580a41810740c81000b45000c00907004c25500f01c1225a0700a03103100d1100170740101f10300a5a0702070140030800300d6001881544110380200300035a03178407245a95600070716603104404143c2c5500442402c1d500b00c04650584c10705c03d065440d92514101c0c0031100e04031185014525008200c81c0f03500001c0c2140600c1c0c040040003d0071818403180c07501507261000180d01d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 973443794 1250 973442544 973442549
    0x2d0f390e0f0609031203011217041d0c130f170a030e040c050d0f02090306090c06160807020a0303030b1e0d02011107080607080402011b05070308090d0b0a0212100609 73
    0x9200103c0c3c403000c01d560900c500003a0301440f5810039280c1d80c5d900780107518400e50410503101700c1408074400c45021044003c0303070161148019803006031a42292103810034034004000d10040320051202c0b20044601d002180002c02746012280540ea0078904200c080f9017540d80c041c00a0390004410340002600081c0c0c60400080031280020941c5201c1420b0362107103d580f00c07242c1140d00e0b200d1907110710440799014110b840429412910faa90b240130341c60303580d80f030303464901c03a48590107000a0031707014045000d903124180310b2002c00703041c610980e01054648c88150011008240c544000c640c2e5401c0c0754014003105d0b10300c2e200c1290300401d800c010424840610102038100007460450f003d2802d400c01400000b010301d4030882c3e0b42460040b0b07008120301d6040da0200d0000726030302c0e400d80d80070010f103c0e01d07101075411401070030b801840c50b640c50080b944560030b001e0f04140c0b407000b000b012a0b29400240d1041440103c0580c0d1200300000400e1960001048105d100d904540140482c83c0d025601406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 973445044 1250 973443794 973443799
    0x1302010c080a02120f0a02010506090c04150e030a060e010b062d0903070f0812030106081305010b0a030309140d0f030503092b02012d0f390e0f 63
    0xa40c2d4450100c201c0c1416560040c05540140000d150380600b59004020301c06c0e40010b9008105945074841007129880065440244c450418003051114540314426008440c078a81010118003402001107401c1c540044401d03504142d44c2c0c80408001102030050180000045402d680350184080c00c800900c41c0528011180e41054418504145541412a001044000c2c1169909507892000040c821b01c1130068091034003440b1700484944a0f0340050f203050b80e13038586603000a0758030741c1c0115071003200c20340e42503e05d9900d41e64032005036100c2c06c3c400e41c05907001e0b42d90320010750300b17150310060003007490000d15004205285018000c5000030400c0340b42c045e854502142e80343c83d44c40701c141c54003003609078010711030a012070803141105447c0061010031323000b81c0091000f281d040710344480740e511450044103401440c4041c0710340300c501503106041001d10600300281c14080c1d008180e070b4802c401202c960340e4101c40544c00c50380d82071802101000700b14030702d444840c415405001c94400d66610b10900d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 973446294 1250 973445044 973445047
    0x30b0f06010e18130b040b2a03060f030a02040501090209120a05121c0f09060506040b092e0b130b0a1202070f0203060c0a03061d0412141309051302010c08 68
    0x60b0081004001d250813941c01c100a0509800d01d42042e200b051003d444c280d01c026030702c000340444000c86076114520040520049421503441d5021702c180ba14081e0013641c0d150151001c5100169074070710038180030308484800107850788e44030070038460004525000104203600800030000010800a0402d040740c4a882e0b40e00d841e0b0903c2000e400b05540030640310142c5a041c604000c04108841d8040d907200ca01811042c485a1502d4040c4401c8a00c58200c00307802c035501400041c0041c2c0465a522003015201002d20342821450b402c803846606079810503142040e000845070504412039500c1c074047c0a4940c0114600503840901501c200c0540451030400c54001c00c6640074000e10368803401c0ca298010b000c2d0f502607d488030358588542c0c08809074a020074035004003c00c607842c09061040e04010700203100e910548440d103e9041601e0301c0c00409040000700c5c41c50400079060a0042c0207400d903801001e08a56040000308000e4030b0b40101442e0f00c82600803400005070703070311485001030103030403010a5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 973447544 1250 973446294 973446301
    0x307030f121b030210141603050606090306010f0509162307020301090c380c19050703050d0f05070f0804051005070203120408030a0324030b0f06010e18 67
    0x41e0b440541e01416900362200b8851150281600841e04200d9862000c1040101c82c110707800c00101c0c450107407600c1c12021402608840e01134040e030b1106400001c002e040c01c0c10200c05d40002890244260401580c00710724840800c901e041c0004450b8014103151490030742c542880328014030a903015065200d900d0003420a254a00c140b010440e9000f0350042c009002e1b00200c0d08009000700c115208010f0005030901c06407503c000342c4080d640d9503d0754541c3c84802101d51642c15401a00254102d08140c01540136942d0350b0340c0b03071130102d402c101d100e6806003074203d01d1030400c10f0800b00d06120000c14491260030009603e0f85c030008440718142d008000b260340014508003010f050055421881d001142005d6075400c068014000c0e04060388201c00322815000302e040d480c44a03000d10300c541e0041c5e41c000d0000d04031180c06030300030303250750043e06006920f801260281601a04c10a50041c0d80c1c0001c240140845454031b91003241d8080e0003070800700c200408801c00f041400b03103140c540006544030540030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 973448794 1250 973447544 973447547
    0x4020a0b042301030605030a080d020c16090c0801050f10030e060703021b0a020d08070501020909011202010f0305070915020c091f15050711041b08010807050307030f12 74
    0xa901030300c050946692100d0701c80c880b030100c08120101e003410040300042c51680940c464040c0c80150b8601401411814500307a5a50b441500b00303002d50008a41c00340a021000003040001c59200b4852907401d86c032084c58000300718221041800944100700981c00107001c070b5112088401441001580c001c10b44007081e0504500030094070b040c401741c070700404080c085403950640203485400a0300d004200880c0340500035996910704840000d40040c4d031241030f00c000c610340d83e001d407400b140580e00240ca0202c642c0005512032400740c00c2090b0760090030801109550f404055456203100318102000a0706009501400000c11441840080656030440c8100544244840c540d0080c0c00341840c032880c100320091000c1c2020b01410030201390000e040020b100c40212454140d4040561500c5141886c561a02da0810f1044504941c0081d00c42465401c0d04040c85c4490300d42c001c9a0750385180d07950400342401c0c01c080540e8801c0d031007540078110500c04609070300f0b141c609960b40701c40d507040e420810600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 973450044 1250 973448794 973448809
    0xa230711030a05152e0504021c05010308040f05040b01020a0b150a0b0a0324050607060608030a030b03060a0e12090111060c071208150d03021608070f0503240402 71
    0x800900a01035001344600306a2030881c0e0038042c4000e030a0b88020340300004081000100e608100c04900d400f030210800290034164010591000501481c8003807001007a0104160313a000e0b402220710b0310300080e082103d82c030700500010203010111001d008288100c4c00003944c80301c50640240807404107402060071901c5083c2c210221100141c160002c07240e6900501d001904501880b4010900308401c5000b49001c046818a4a01c1c0c9070f061075440758201000e00809800000c03040b141655100c401140c44803003040a440b040500380c1e00441d044014a06041c00c058025040708184d908048900041c00d5000c1b030031140ca2000003580f80d03180c0c0440303001240c507144001c42c1000c280c018001400040d000d0500101030580c011002107480c0040300c40101d68102044482000140c0090040d9009241404902064501910455907444000152030400c20403d6000c00100d070f0182004228608012044000500d130490142c200554001281c0444040c940c0e40e500c2c24000800c00a021541d9400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 973451294 1250 973450044 973450063
    0x4053409080714090a050105010f1110020d020a0e120a03030218120615100c02040f0f0c020a03020f1219021014090f1c110a060e030a23071103 63
    0x40c02c598969541c0c0380714031000c01c020700f00c2a005030194000103012210720301640d41202c506a451855030400c1c02421569401110500d000d1030240c645e02c4203207240c00b80064400f440c451840140c1c1c82c6601c0f0805071a201c0d00041d81030240403218848820042c0205040c860660107040141e079441c0034071403036010301c3e42c000d10960f404550803562928140340003404030b1048080039042034032025000d00300000c0100803554000018580c4034200b0041c20306800c04180925030179000b0500c1002d600d050415504c01022144c01a80000c00000c01d0550410400d030035581068041c1c40c411004000d244100d00c1580f10465403032900d6804c2e6045d80784204810094400c01e0f00c0d08200010f141c103250815008252100401c9201e90050b004901c40045aa10b032541042e440d1a017444165901c20703607000c007101e4030b848441e014a0b001c40000c620301e0302131384c2080781205014507a241e24540002d030140c00d0007210707080040300800080b0300c1001c1000071141c1061304801c00c0c17050075886000203441d205401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 973452544 1250 973451294 973451309
    0x2f0a020a060206040b0a0605060702040207050a0203010603080a0f090e06040b0312040b07060606080f061201110d02040f12050709020304062901120b0a0314240604053409 75
    0x4803800240680d011400c213014503ca000c6204031521000a08800da034550302605a010708101302c400010b142071390007001c009100b14140c0d05404820b0300040d003100c255600949460310005451180c1076404080c0c040d414a42c0d003400c00c3e00600301881560103140c005c0c45140103603512124040d49560801202087c1d8a01d42c00c0503544903255071619032190480319081b41c22504140020422074050310b40b0501c5602c2c06c40a01c0322540c0d07410704000040c2c154101301001c65584040e00c0e41520480f20040c03150203041c0a0141c1d0711071034000c8180340940541d00c9401e103102040c2e40c80c8006680800c03140100e4908d1580541c59407140d040540046c00a44040048140b05414000d01000a400c460070f40070400d0300c41c0000380f001c5050500c1035a00092080342c0c00052508184005680c407000340411030301240c2110401e456442180309054502c41202c001d00b090a0200003491502c0d01400c0e07407000e54410a20048400001d12010003600482c41040c050100404040300d103202d600e00f9401024003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 973453794 1250 973452544 973452559
    0x18030308041b1e0306060f050906010e1f02011d06010503030d0e03090a060e2805040518030c03030f010819122c030105130f0f3f2f0a02 60
    0x3c0120a4425409030320049644070f0801030000b411600950044041700c0016212501640e5010011141d03c94001c024680c07008202c8a00c00003100c8140d651403c1c041550000526a48003104448003107c1014402c00b10340c3c8014018011038a020090310384d0780c03d240c003000c20317007201c268010341c1580105444250004004800050f40f0f580c011041c44403150169074000c00f000391207940000050008003000031221030040c041100c0e041c00c1d40410392041241e8900c1040c0700035807500c103041d40e0001054070751607800030041c0441941c40c0341c0d04a0044c800c190043c103084040e00007415203880303407201c042c00a07d02ea5248801c02c074000c004030004841d0190b80c01061481a03040d480f1032201d0840b105000f5032030000025110060401c5034140650000c41c05130030130030250754030f40310100d145608481d610600240f40424147c01091b0048100300c2e1001d40740c144070641c40d048100340000d0415000c01a90701030f1001034414590880b0071540400118980d00c010000c0f465140c8003828800a401c200d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 973455044 1250 973453794 973453829
    0x1a0d322212030f051b0706140703050609010806060d0303052205010204170a110d050a14011e021207030b0307120b060406120c23030a030f18030308041b 67
    0x7119240340e44000151410044820420020011650110b5a0480d4400c171034069603403030f0f4000740c0500f40041c4610400305044241b181c203840640d00684407007000c242c031441840183d1406000007409001c2240080010b860500001400d103440000042c0505556501040440505400c0151114650544142c44c0256890704034001e501510460302e9181c0e0500070003110380c0010818050064205040c282103800050800080c03002d02c4208844510914081307900240f001c0c80c0680025000342c0c00012084001c551001120b00d0310b012080c0b0092040005c0c12031401c0207c461038000c41e4038a80001ca265810002c603140c035605410240c2404502202d0004000c1e03d03280300b034400e68041d030782840342130350310003000d804000e83c20002001909803200c02e01c06c810014044020540c1320400003415000003101103410300080c00d0b002c3d800542801c085010480c1c1226a041d040d540c048070081c40d031455501d0040c000f1001600003001c0742c2c040040058200c00e2030100901501202d41c11050100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 973456294 1250 973455044 973455053
    0x4110409051b131a0706090510060807080606061810020a110f011709010b220c05030907090e121b010b090105310212010f0905150405040c1a0d3222 65
    0x540881489d0340c41070400340c0c0403c5c00300f004200581210500c0004182503103d81c42088155041150122010300c00b82049a042c2e42d20310050402c2400c043d0060112402541041800c03094020580c03070050310004501e0200717990000f01c14840c001d88002c00c1c030755130301c800841e40c4c0036014001299600c20220908180d081c0c0c0c40101121040340311075401c201c04045503800fa039540c0006c03202102c00e6080004100000d550a80100e0154030f2030009444040760f06501084064201003408010103120b101da010340c1035002d21807058141022207031240c96600d0140011450f001c1c101000c4144250100c166010484071400d500021907448010354542c044005a052682d90900c40d0a030104201540002c0c141418401c150140d1480a82007044e004142d040c00003900000d00115034007100030000040c00410030030001481102060300c2996010505c0200d0140c0f181d50003000c0d02ca00d40f081c01c169854914542040f69050b807031181d604203580c0c1341802080000030442da2695074104105040402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 973457544 1250 973456294 973456303
    0xb0414100c02150418060302100c0c0302060712030b030a20220b031b0904020906031009030203090a0501110c0108040c18050a0e031603080604110409051b131a07060905 74
    0x150021101c41c0480c9441a5004046e51001c0c8000380d0400d4040b0b80101c0a140300f401c0300003032030340610450542142d587c2d01203180b03540502000d84828410310308801401d43e2600520446207002c400402441c2c4041d00c1e5070780c520303070341d16420903003a0500c1520b07000607215112082c1c2010020788000c2640d180380302070140a00b550b502514441e000b1000003401708280030b40150240d40d0043c12800042d6655428008410005009075030700d8031800031065019100d034011303901d882d0321903405143c03110550340034400d090410f40c0000341404101d19403143c18560026103009120003d181003100da841703505001c007540c4841c1d04a01c5540000003408502d040321504258028900860200002d000c0c1c2252a074990055100c0b030b034050041036501c1c0000c070f440b074080a900071100900010700350400c444107010390340c01039004005035602d4070304210021803280301207006d0035000f00003503142070402101300030300c9251802080c0c0c1c18802001c0c0a02501c140c4801d8810721b56001c0010054000b143c1001981c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 973458794 1250 973457544 973457549
    0x10e0a0501140603061308030703020702030a14011107080f03130503070809100e0f0f01030b030123071e030f1d0303150604050f01080a0906060b0c01060b0414100c021504 75
    0x2048100b1001c034002e800c000403118032480600807080340d01d82d1b4540d50300700e059001804c440f08040e0284100070241c1e40601031030058512500c034011048644003a20744c01e5604882c1d07080803111090000300045000242110020304484021355a250749040712060035450b1036034090f24503c804070f0001e08204414008100c1c10400301d501d900032940f0603034100d800000b100b03903103500580a8a102c41160814444401143d10141000b00d8880e1400c1d01090850740444401b1900c010344844e5003036526040843c980e00301c406498259035034003160351030381c0a5100a040c01001c0656603590b02001c9000341d0b009485d203045001c03000000072800b00f40241e0343d420035900d0341c46d01c2c0c1141c000e0740c2c01448d02c24102c404588020b07006410381d100100042d189200005c0003140f28940b43c083c900001406882580060150211195141c40d07000b55414212012070300642c01d00f4204202c03d0150800c0c0100b200480241140d0701d0902d4040003000305c0c0c2070851190005c3d04280388507906180c1c2943c0b08040c200303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 973460044 1250 973458794 973458821
    0x603051f06051005090d06061e0603060e060f1009080102030c03010612090213090201030213090615050702010e0d0615060906180e010e100b030412080906160f02010e0a0501 76
    0x70544400c10408a5040c0c03c1640c0c02060f070801c0130744000d0519032075050341c80303025400010303100340e66041c41d494003408080d1a400c401c82284050020640522805c800342c188c02c07014a15500d400b4020810070014a02104d101e25414241400501c5c810300c05c6001a0421000075516424001e001c4e800a41080c000c0602045200502d211004250312541c0c5240303800500c000041c2c000801604002c00207154140e04068081014480303068040e14110014842c000f00003402d01e00d403402040c0c0480308a00120100f190070010780c0d000d40c1c3c0c400d40034007540c00308454008030311000f89002e9000b42a8003955454054080c00002074954008072964125842e584a00000280b02451050043d24601903040c6049042c0c006000b54140f400c4880d0340180d400701c16002903034940e4810600c0d03800448088070f1100301c07031918040165000200c1a0003d8101d4004e00320381c281508420400c05034982e0358010800a0680250924030035000014111881402c3d0354101500e800d00358060000c0004464 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 973461294 1250 973460044 973460051
    0xb0f03090708190605062202030702030706110702010f080405060c1602090411090106051314030f0613150902010f1404050d0c03061d031c020f0a120c0503060319060603051f 76
    0x1c4081c00c14544e00884880e41e10892100e2007d600803140003900003411386130071031009004010000d00d980c07280c4042c0c81100c2c1c407016200c2082e48001004e10340c990700007908001640c02880002000080c0d00c50304001c820788a21788a900c006c480d08011010468042c0d403004030f9805100c240060744070491400c1006580100d80b03681c94040a90341c038880c01c955458103419840f401c01a000c10002045024400202035603c00412003400f00c0c03400c4001e84000a00f02032503880f2008000c02131310780c0c031405000c41030b06000c91507242c1c0000e8036100c03102c41c1000134002ca140381500042c200c0011500a80380c01031068050110324149882c0e0060540801c41d02189400001c3c1c00f4400411103170620741c10240c0c02185400d80d000e440140e28a42103220020280c0c00b070100071054100e26020b01781d915040e41c0e8130b0640c006c07091440426180e0702c0d03841c8410b01c5410400c1c0102510040b9400c846014070b119a03500154032481d0010041c0b0080d8400b403c94001c51015416810241d0105044003082400c1232 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 973462544 1250 973461294 973461301
    0x60f030f0711030409090f0c0807091506050d180b070e010806041a010f110d0e030c04060515130515090109060809060f04060f0507020c190b0f03090708190605 70
    0x82e00c04041c0d4041030959940103200401901140d074101c0c0300c801c2c0c8901041c80b01c2c18819640e40d030205026421980481d0003a00381030051035854810880045403010301d246c0450b18105019201d44294a8002d06403510780008100c16a0301c1401141c42d1076110711600054984000c004042c09400030042c1d000030407038000f01300c0070719041c080d01101c10118100f506001034140e006541342e0000d503040f0014044400a80c0c117030b40c04140141903540303069450362007035912881d0405040c86151420a40310314a400c9017400b40d0703101c5a040c19100710780f480c01640d49861800b869084200560300103548440b400600304501080c04000e40880030007030300c0765000b8685401c0103480300c05084884002d5584a0400109100c08241d00f080c0c01c91301035240001e504040030505000d0f10b10072100c000140c0c0c0580302e0040782d030401801c008080620b03400314400342403c00c1e60f40e01c07040c400c48445900250012020440c40300c400d2000d080205001e03002c440301200412150700500c04845410748025180a000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 973463794 1250 973462544 973462547
    0x3090a0905010e01050904021c05061b070302060a0507050d02040f05120a0302120310030506072001060806160521060a0518060d06240315111c0209060f030f07 70
    0x800741070b21240c0f80c2203503184e07013094148800450000c0c4140d80c815040b19010351483d03080c4020000c1c19002ea8060100c0b45018082c035062100c190102e5541d00b40101f00100c082580458640d4012252800104098039641c00880d06802114074a0758000e01c00a000100403100000c40d00072140c00b580d1248070041b441040c181c4510742c8140c0600580c00060404082400380300095030b0081b0501020010380d41c40ea1074261a03c0811960000441d00200000c10100b800c102c02860462002c0003e00901e8180200d290303d62030003030141019403201a400c002183d0040060f90f40002980102446076210f21214030403209094540c0f5001c0d481076400862a8141422060030f0704040d5814205691100da0610005c108030324001d0b540d4a59414403c40369100d080c10404e542000c4014030341c40030382507042011500c0d0401c08401c1c0e80381c2c80d0039054480c40d10840d0940b404086000c100e5540380c01350060541c00780c07040440d070b203070f0042e000034646041080c80e42c040c501902c0400c4000082c2da0302d2060 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 973465044 1250 973463794 973463801
    0xf0f070501050f0a09090615030b03030a0c0f0c08151e06010c0b0604090c060309020f18160516060204170a2a0503030c0105011a030105010c0b0a0e0d0203090a09 71
    0x400d40061410043c0104400b880c1c3d004181010080c03503c0043d1641d280580700441c1c034250005001080b4048607480400c0c2c0c540150499007000310f000d03610307124442801800c101441800140701c0c5c3c4440300050180f04411041300018940034041d24440071400c1e08407081088111002c903841d04014071104203041010500c40e1080c030040c0c403035206024603911102000440101166403054035284c1581c00240c414180e60000e00c02034401052034181c80c810086e081d0700140c45203000704040205e050100c00382d128039a4001c04101000c0c0303049480700404a509201d9039030903000280c10a50f40400300b210307940c000c00c210380043c212078400392654001a5201c030040390000d41034800d5000101c62441c140d00c0b0b00c820444235840b90908056482c00840e086401a820760380b800d0350340760010460406907480c0c000821001c4c1141740d10759818440040d01044103e5000f40000b203800f1f0000b42e038240e642e0301100082d0340c0a01107401d0207030034040c0207583e544800441d5009841c02040001c0701c81c01e0b4017 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 973466294 1250 973465044 973465049
    0x1008061e060112020d0c020c040623010c030c0c121502120103061104030c0321050c030d0c1b0b010f06030b0f040f180813050d0b04020f030c120f0f07 66
    0x800c0040e944820004480018400254405450f070030002854580c0c0144248040d000c016005440640390035401c000840f10140d00c010100c800712810684d003001100d207040000d8409003082c41040c469810300711286a086100104040c01da0b000105520911510a41509124202041c1040802c8084400f030740141c030030045e9400a50401840001d4840d000702001c2202c0c46c0c1c010b82031640e261112400751159030b0068901c0314a6103100c200c031518664440c4c525178018109249404002582140c0e0ba1158a8246030035035911002e1841c400d102c0c00e902e003d200c581c585030003a1b030641c41c104600310140070b104408802040e00d0001483c18002e01480a40904c018022940130388a40e00707000c05001c105a00441703aaa490042c81224458540c04904407401095815216004030350442e40303819843e0005072265103810007000018440b102819845507054600d5015150a040400d143c07030103241caa00e5001400a10300c09111100040c3c140780105508101c6449019041a4540701c0b40d590 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 973467544 1250 973466294 973466341
    0x4030c081507050a30060626100b0705010906090b070206060102011116110306100f0e0121060f0203090c0a0b090306070807091d0a0c0311090f040212100806 69
    0x1100c5d0100d00030310301a190500d072036540901c02c4048014645070303400c4441d5078002d04045007070008040c4007295019401804d14228050740c040e6810407a0708280780d10082d109460340010002201c0c02040020f40211040d10741c004004c0c00700356218600700c00d03410743c05c0325403000520503000025040e6105000341c240c84242054002d14110440641b800f01d5414001c007501c201d281d2070f100e0601524100300f020302c03c0013081c4840c82c0c2c160420441c422415003d510103030321001614010320103070f02005089015074540808005000c1d06a151020140038094200c24403640301108218486c0c03000702d05810000d10032512090800e442e01c40340240c602070707143c142e5050b5000d64000307030142c0e0203901559004459800c201615070fa50300403000310307880802c104250420200e000d011002034a0300511100c80c219007028001d0300d114688125540c001e400181d4420014040c82e80b201e51074944c110b550100c560007801302103162450101c4104903151082401910400001902001c1100f041c114070080d40d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 973468794 1250 973467544 973467557
    0x91a0901030c171501060203030612061605160203010c0305010512011107060b0a03051c1b020d03030b060d0204080106060225030b06180a061811030109050c04030c081507050a 77
    0x20718a0407203c1800b11a14244207100b410b245502064450321624001c015950040d61381b490590148440c0f0b0ba03804680803031552080080c01542050381480c105c18609604d4003903140c01c0701c00340c211800c641d102c0f00a5019481c1241883d1001d038035070401ea041c0d0b9030642d0704003c541d100c54599802c0710009018000e42c407906000c00000900070b0f401c001e00d129801049c12425507200e4a9181c1025110092152001c5806504a00361900700f41881880e000700f8140340d007201c42d1900840c8000c110880c000f01013503900d40b81c1138400e5481d10299403c0c0d070110301d411034a8985a4001d54004d1840d8003400e00980720310145110050954000b94161948881400003414995610300500070000740c205944110241a0103010342c1110180600c0740484040c0400d496103003c3c016007052541c000d030881c40c80d041440f000800340c041780172681124084400090b1682d00c0001c0303d40240a90f4000410710450054001208000002c84142508100c1d0414807a6202d21100b42c50910a061101c00810302 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 973470044 1250 973468794 973468799
    0xf0105090a030f0512160317060310110c0a05030408070509040c090f3206060310230a030309090b2e021f090312050108031b010605040501091a0901030c 67
    0xd003408609a07449041180c1c481c0c0080c82c612142d5400604142070b60406c41c0400070141070384810b0224a20203032200540190030160042600d800c8021020003002d070715072214401d040b410200301d507800e07480b08090707980d513001c00d240450f100d51151007003600300d00c00c00381c002c03c8030f2510b82e00040c0215031015030b104805181c40780c10300c0076000d03000700c4100c02e0f0b43d20300c442d0003204040d45585c405111020058903101d54054440c00702c040000d8026070042005008000c0002c22075802181920141c1007211501c624000100c5660f440e0301c14066001220400000105500b01320b070002a100c1d00c5409110b210008010301c14503c003140000c13114a4003c190055482d441841a10a24072191055a1000d04080f66801e224a0a00c0c40881c0555440b00c0380c0e03080c140d000d45040c8a03081d03084014401949410700040c1c0d0707400b0381d003946258180860032420f1094800d5200070004c082c040d2003801690b07940d40c07509004047c03d1781c40030101100001c1010b41c81ca00250701d24140ca52182c04640d4160 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 973471294 1250 973470044 973470053
    0x80a050708040f060b03030d1e1e0b0f0a06050a02100c0507030e01022b020c0102030702092d09070906080309010f03020a0309020d0b0402030f0703030212131809020f0105090a03 78
    0x31611401580c10176511144101552014001000241413014021070403800c0c60801c5c008000c1c403142c6c940d0000386004c0e840c800450f11101540144281c05802060320401800060b800c2c00305403100a511144a8400003100768201c00030300701031182c40d0252640028400503d206072580089408002581040002c00085c00307030882d075020200610448110904410b100380c4c101103643c0c00d800800c80380c90050149180d0405c489044000700b0300c087c5007881c200e43d011540008018001c200e030464504491129022552000060000000070481f51400c14004494031100b103409450700c818204a800301e0f9000001045070310703c2c01d069682551341000b55004900a4201d842044200b5407036001c003102695905492007000b80c003032a000115030605204041c90482d1000c3d0f04481c0780c10420041020035004110000038100100c005561843e6108859100c0b8005030001c41050490321b4856100c020154811640c0b184265a44040e0003600001950f01d0701550b10855880144101c041c40000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 973472544 1250 973471294 973471313
    0x20405061c060e19270f0209060105070b0f041e0b04030215010b031602030c010204090204150320090f1002060411010809030912010207241a0a030b10032001080a05070804 75
    0x3484172460030320440180340b005280c0c61202003410f881d402d02407080f50055251205102d034100d58242881d5140c5031460340e801d00e188000400005100341004001070601c486812400e02034081c118181a8000051030b09401c2001c0a541c20f80c0140302d281c10245907079051900190513141c0e5001c01504690b00c0324101512400113005140850105105144151100340080c101420140380d0140e1200d0500300000a42c6070b0700703181d0070105410b149050020810900c0344401264610401c2c42d500e10004000c2101c070014400b50710781164049c2c21982c41c1035404141c00340541e00c152900e9001180362001110741103410b03246000b01d50010846082e141c40d0001710f4a40c0c0403102d00000d8241401c90f1140c0c0102011070b8808024050041c03c01c003150034031840b132401204100003410300d100303510002052007040140001031603c04039101296158a0784a4500000d55120707004401c101740d0300d0300310030041c0218440c06000c61444008502d0ba03113268051130744603031010b548011403583c55480b82c1c4c0c0745 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 973473794 1250 973472544 973472561
    0x30a02070f05060a090b060f0d030c0503090a090504150903121a03060a0b0a0603090b040b1503060702030912010b030a110d122607080c0904020405061c060e19 70
    0x4201e464616100019020710a0501c901c0d0301d20301c006a0740d140360400c81842d60b0010700ea288203c40d25105c0c40c159a03224100c44540c181c040c80c10650300e895500d0083d240d4426482c41c1030303210407491000240300920b504402d105d2407058082e500c5c0d65200805d850261011400020003040b0000700c071900441c00d5901001b100014500c0300310f040300450021909088dc150788943c040341d11980b00242900b05406101d0080003146030402050166882e802aa260003503c01001210700c6404286101c040c080d10003102c0d00002d054507128100018041d50380e03840518001d0256019081d0780081070010700c112500c07103230f000e009030001842c030b07079a010340101c0040d40e0a544007100f841420040790b40003c24000950b09a1180361004100d1001403050110755846084001300900410400701c0e440700240ea00310500b440c680d9100c401c80350001b006801550001d0380c01c80782c0030644130382c82180700c2d02d8118800514070040005503152000d18091090480c1c00030045083c2080d0440500c60f00d62104a5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 973475044 1250 973473794 973473803
    0x90203060604090f05040c1203080417091305090c0105070512071a041b0b04082508011a1201020c1207060b09010321030b210a05060f15040b0105030a0207 68
    0x20385900d03460080c040313401242c10303810b81035610300400c01048000c0022101400300310b104c52040c20f055a03001414400024001864a0318000f030840c1c0e03504e14070060b10310084004001081142d1010722400052004903a4044a881400414025940100100d528082d0010041c040c0e554006000201561001c2d0040b616035100e103d000d10f0303203900728030114042d41c4036494107107681415484e0010481c141c0d8008102c0040100002c12080f10b00003100700441c0c0101810150807050752041803036500f1943d1140409500f1f0076650b440d4228101021105220122505003040c0c400c419942e00b00d00034403518505a40c80440307481d50f15001c0c40b0141028510610001c96114008400326000d130394280e004540081d80001a04010300d1881c0901c641070520b031908003d850b0001d00010710320b1507854005992400321161140296500744583c0040940040231507402c3d083c030700b1007a100ca031ba084403001400306094445400310b01c0c060040103030038001603541c2c1c1e0540d00c8807680300c0d0095104040858 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 973476294 1250 973475044 973475047
    0xc0b160e011430090c130509100213171603020913050a03170a0c08010b072306060a0e010b030c0c030903070603050603010b0a05090c03042406030623010902030606 72
    0x8180707070302d0f00a00712907a01d1007803034820000c1c0908107080a450280800c1c003180c100f90360070b1502c1d464603e10b10203414003001020581f0b0310741007940d0741031120002403822031500000c3d0013840c0103020992003044881703804801903241074002c0c0c5252210320400142080500c0b01000f0070251078031812060700104400180602440503644851400b031010600700c010403030340441b4804803030242203159070203250494240300c4551114001003028405020b02c05684601294810510072440c41d4003502042c100c1403400c191172007240480c0d5920041303898501c102c0c4050b8000c9040740416111074121401c0e803680c0750642d220030030030500c030340c014156080940c0700a002d1011140e80c1002014001c104036240043c8509101c02418291080b0401450207411108410030842c0c680703804444e0300a005026940c0c0b65111407a002030048000f0306030071200d0011402911200c0041c0d1304c010f04407807240da020411054030b80040704600d0107200c403a4404030b07070310001000880f50b96001142c1c065801010f49 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 973477544 1250 973476294 973476307
    0x6030c050d02070b010e0601030911150f03041110110712060e030d0501030b0a0c020307110616080913060e0619180b0a0501050c1209040b100c0b160e0114 68
    0x30400c0ba00701d400d042e520725810f4001000300440070340ca00d030b80040c0227107800c0c04201036940b10b4418080011f140030f405160703042e0a41c44041e00c02d0003500c809140c400410340e524106802d0180314845e0038100c3c00d1182007400103840c00e1707500030b103001c142480501d405080400e01c0c003280c20781e040882c4a030036207059855400d00400c1d000c0a20007003030681100c0c3e000041c594158103100261000041554464624124200540c5a000000c0d030f80ca0310b901020300d40703050700c2000c00f281c001d005100d140c00203002c11304800401c01030b43c1000b80185000c2584d190000303024046004050359802d2140c40d0400240b4408a1a00d013000a200d1300324005202e2400c004036603400078800c10300400800c82c41100d0f1b03500c0d5080f4691610492507001880f0904e4554101006511000e4450008401541d120000005d545801e91580e40041003020b000501010000030713007241c050301003201800d0031901801450f00203043e07170b000104041e15114155aa8800c600d1030140152080744118181c1002a038052088 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 973478794 1250 973477544 973477567
    0x13020a020f01051f031b03080a020312090601030201090303050307020109142a010212160c0e09060703060303090b130503071410020703080904090602070203010c0201061a03010b030106030c05 84
    0x900011485900408034054860a4142107640c0034000e4142c400d51801442030f404409041c034029260456502040a10b0824141d8441c1d51145e200815500002c140c1083d15900400580170262400c1080f041584d00c0c02c1d0001c0d155102404024042006000e00b072001c41d1280000e1030b0b000c03d25000029620710f00303884600c4928415403144440d60302038202420806804c04a542c00c01d4800401e00807241e990b140042d4440e034241c009041207501c0071419990400c039074040c071030b425500210442d0a058480c0314080600d0000c0760306a0052150b1804601c0c101c1c440c1c4194011030b50969940781c2000e041c1007004501368400d2981223100f18007a0303804502d540d0140040b0009114006000c0c00c41c09107182801001da12038040103040d504210410004121030004450520108950010720140706140540c000c0c092030740040d4040d0300e02020544846c0d015440700051b01c90441c0004c0e0098811415481988000d0140c01e512001c00d0004100c100c0c0650007000e00c00205003400341c1002e074141071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 973480044 1250 973478794 973478797
    0xc03040f1b15020705090f01050f1f080106080c0a140913060b0702041118040b011116140409020f0409140d030c080c0c0d08061306090608010b03010504201302 70
    0x701864100c4030102c1400950f4040040780300a21040d81c0010742450f246000d60120f140511880d8091500040c4481c0240eaa2038040744810324190040003c0d894007003002480e40d0300900401001c40d4444000c251124420010750b01c1408642d9250745020b04a15611102c0d50000034010750401c14100b1844081403580c02264080c0c01c7c1c0b030b0751258441c2124010441038840390030b503981d508542000078060890000d500203034174002c26100230500102810048421107110344626505000f050b0304c0380c00903020707030100401b213441a400380c00484a40404200407101441e00c000e501005003002030740503050030342010308940e0082c03000c0441484410700c62170070044c40f0760420000035550340d40d00e190943c000d146581c0041425445a00b4070520ba2059940c0f04044080041401032172400550103030348440c011007005a00c004c003401b0190351500d02101600c0036008040040d400c0204114030790405215192149802801146030840d0004003541c0c001e14880c440c0c0d0300007240c0112414450780500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 973481294 1250 973480044 973480049
    0x11205030d151d060f0103020306030613051218010e120a0b09070e010b0a1211030c130b04090207051b0f12010f090f030e0d020a06050c010603060c05210c03040f1b 72
    0x21401d61140b61150030881c5a02000b00c1e05c0e4107240c41402840540c3d280043c1c403c0d4008580031441c00141c039541002c0b4508a44160224113600c40000c40d01e040410048500ca0301100030780710700c00c140d1092410800c603102e1001c84030581e0742c059803030900412040c40c505900812036005942805071100500d40d01c1c1c2d00b0982100f0541c0b000010340e103d2080d888603a0003000c00b03c02c0810046071065460710501440003604170311035098041858103244a800d400c0707c0091440c13014055032656038482c44006500006001c0c0c03864086d6035001003194250a501c0c4440480003803120007016170300410442001e1071441d003080c107907503510850144c2103500c2c4212014140251581c11100300300345801481c50300c0c8887c00b02d00480c00348000c28016110981824252802400d0203030300d49841000c410700504140e84086c2a2b50b00b824017400c04c80c4d81150041210801e46459642100c4040b1540d02070220107403071601c4040c90420008020a010b0100b00543c04e10030a1102c461701d540e042d00070b40640da540c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 973482544 1250 973481294 973481339
    0x1b150904090606030b0903030103030c0807052409070609080d0f11060a0b130c0e0f0d0507090204140a030302190f060504140106080a080711030c0603090c09011205030d15 75
    0x42409205016501c00c040b940554160007c1d480c42d811a40c00600346541110028400b490209288017041024010007046000186228241e44a80d960244c3c4050069581d03440c14040e002000c40c100d8811848070f0181c0c0e6522008100d0b001e140d102c1101d000900000000c01c0180c55214552a0f0b4800e00601d03004210b0400e011541000a00402030000120075111600d240390840c1641c0309504280130703582ca4001103500003c00740c070003004940b540070b81810050490040c0d075000b040b180500d034054030035101101031003900071071440c1c00d202c06a005408045c015074045480c1501c91000200711700e41e654854a041250001243c2d183e800752042502c084900642e0811440c45810092142c60001c00481e001031680e85219210100b10b80305482c000350502c01066080b1219442c1008404403036000502402c0e030b40e141100090341c651b00c40100b440c3c0f246059400000341c00040a858403412500700d0041e61400d50a0741c0304400500528425402c41c1c12000800070350140605e9140c0c0c480440c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 973483794 1250 973482544 973482551
    0x90102010920030d05310f031b0501140d02030a02090a03140d02010b1e04110f0d32070e0406090e0c040212070c0302010b0604030606080d021b1509040906 68
    0x140b02054204110154902d08209007480179015407070b10b030191480c10185c1d0f0f0300d5240700c26400f40071421042c0c00175048038103c9940907600004101c01c0b0809118000c10507801410b41c81e072920011258092129000340340a407083c004190100d255500458100040000040c035140c0070402040d01c0c444540e2060b581c15805440090002600b0b00550507403d0381031008114074461240016500c444000c10742c1c840c11400c0101d5181a20f807a400060840b0403005603640300c2801d0034950410342d028114580c015424a10103c041c603201c00509076181c030095040247d0401103c0b00e185814030700400e0381c410011245103045040d240d92003100043c03d480b001c003050198204900c203182c580f503035040c42d00070351040016512040c2c4410480d90415014607115252102038103048ac050242c0c03c0000da489007001500100704007641d44680112140a41030710307458580d802c13060303850b1060741c1c210f80713140c07109205904814034065004410281c034484440381059500004a0201c488401007141d03803555 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 973485044 1250 973483794 973483853
    0x150b04050c0306130c02120702040b090a0501080d0201020c0d2a230a17030910060f06120203152106090609010b060712030f020721320901020109 64
    0xa2014440101c0c1c02c2d824028071a62070317216802540d501200ca00e000342e039100401e0000441d95950000510300138001c3c1020440d00340811044003c00080c03050081c14420b070b03041540c840f8018000c0c2c0b43c030040341d00054204c000010a0a8074640d5900307240c0c000149001d00c0a940e50f591409840d071220f070003400c00d2036640280c4413000060081b4155244d506a000004500020348107000d404a0300d1720b5a00404d03202e8444880082c0740900101c624201d260900307c0c04a02d200070555040121041c0744c0d80d8822041d00d01d003c002c100c1c4070560343c2d040301480c40e4903180002d0911804103a070005410b44000080e80b80e082155042150a4560007010b800c8013041c40b80d0304809014180303214108480c514681140d643d9a02043d40c0c0490380c0701c05141e15900c241c4150380306c3d64192030005810000101c401071145002c8141c440c203000690307020407c00c40c9c070748160310b050281c0107400e0b600da0f00005481c07000f00402f40c0000d400c025a26070456413a80e00982c00144604400340d183d540c014490141d416 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 973486294 1250 973485044 973485049
    0x1090b060f1c2405101110020a02010f06050d02090c040b07030203180f030304030303200408011b09050f0d0f05010e15071d10030603020306090c1201090c03150b04050c0306 76
    0x1401c20103c008080c018010840c4200c40e081c40ca00200c540c1290301c100410004482030b80c81c000c8010b0149102c0c041d1188100202d81c50360000d10b00400c46500030030120198640c04401c03074005008442d0030810010203080142850b0261641013116804582c0c1090755038103070411952f10040c411801600041030f01400c69090038840718840d901141c10200b520f8032000880d50764001c610020f0101034a991001c1610700e80300c003080d0380f480c05842d40142e031540c46192440c0070308403000c4485004d199880d005507090b07119003c00d500703403940140443e040340b12100401200310603203c0c040d601500e400d80b106001a009200d003d40c440080f001500084440190781011040c1c02001d420500020800b04c3e150340c0150f0320f03072000240c001c4904ae038540d400030b48120024455908000d40503c10b050900008000004694070004811100300300c0003012500e070182a144010002481d820304101c050000441c06d68892440c400c1c40760f80080c0c4010900002004e42c4c20513111608100f000105000c00750 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 973487544 1250 973486294 973486301
    0x160e0f1602251404050c0306061602060d02041e0810092901060f08070813030e0901030309091a0609040915020307051207170c0f0d02030109020306190e01090b060f1c 73
    0x2007804a1341040689081c4240a000788001000e29100700000551032010303a41420b04299441d8000e0200754490000c0c00298009501030f019800c01c40030034882d1404002040380e003100a0762154000b900240c81d105c0c1c5518040d19250303800700c6810780700b4007504007080755080c3c041218100050410b00030703515145014108544109050f401c000824041241c079039000080c59030480040b40340700d61400b6040c1000c840034000100b0159200500400010905500c90001000e45021403410400481c0e090f440094102401e46159017054003440180744510b0503601640d2038600800580700c843e000100c0c040120ba1049441001061010541c0201e046106100c2e550000490801200a0040143c80c2a0000700200020744040000995009011600c0199101004038140039500d07541c4840c03410000c0d4104654180c020340304640c258500030003072401d41d0110765060309040b0599003816941805031000780841d6402c40d60400c00802034850400040c90035003e06811241c43c2c42c408032440066 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 973488794 1250 973487544 973487579
    0xb0103050c0f0f070c0914060f030a03020a0b060a1706240616050f0a200901031e0c0302120c040e1b010c1401050702160e0f160225 58
    0xe0610600c1264244008201200c1c583c1d9400041a511210f051504604541c001e40200d01c64a04090014171490046c2c401ca5001c2c0c00b007100c041801c0c0c070044061507610050010041c00591040341400302090810403030301d40081c400b900014840f85c46500449049400c0c8001c100254015810024101640f00b1003c2c10b06c1011031008008906600000340706008070848509020312007105141004810850070100c0070b07048040d01c1c1c0000040c24200d6101d2005a030385641c1c14018240c00d80103242000351981030307943c81004031010b5a100032a02da0b001e108094101c90110041d078010015170b80e69503134414601c18182c0109003d85024080c030064505007400500554040e0500c001d0f800300528200b80e14140a103000110101d90381420301d81da104000c002c01065203400240071080703074042001c441c5e0307000303186500c04c14503500c800c1480307170010450b2240310812982c008200400082850301030f0b2641144129020101c43d1404600484110002480300b0509001e0400584d80000d51582d034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 973490044 1250 973488794 973488811
    0x50301020301060c02010e19090b0a0909230304050d080405031911010309020f180105011e02070b0a17010b03070207060806061b070f060c111e04020a210b010305 71
    0xc65142070000384c54241e10290080c140200040c03e00e40c039446420b02403591a415010f96100c0325615003c14004001c041c01840c0252200440440c0102c0c13140100040c042c0d0082c04013900031624030655043e06810300c590940c50004103c006520b0703880760083c10302c050103070050fa1b07500c034509800c241c9841d001c2010764940807004c07000c01c4046801e0b005501c011400a0030301090a00d05440001e400c840e80b100c0746a40b1280050b8001c20700c41034195958141c902c00e0b02c4034a2070045c40202c00c801c20110500b6140180e0102c3c00c20301500c9084070180514010703d0800011142c54100344081c1c81c0d02c01d8008812841c0c010080000740da504112801c000e003e50300b000c240c90300308140850a00e10031081c20b02d040c0052104040340211040103124000c0000d2504080459291403000f880c0b0460900c05481100d003000c8003506030b1078071792140c5801001c054055102420200c0600001e50010040c40e01800440081d01080842c5124044801500f501c0300282100ca4680090103d6102500782c40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 973491294 1250 973490044 973490047
    0x102040609350c031002030412050f04090207021206070f0e12070b070c0b0307080105040506040e06060f0a05040c170a020a0507380a111809130b0c070302010605030102 74
    0x344112804001e94031429691846010300802e0034946501d454003480700f02e1307090311039140800d00c2c5180c19809503004501c07548010006510181d4102d426019a000a5001090810040050704c80584c014004107101800e03070805440c0c10850a814410210740110118440c043e0030311059034080c11002403160b08840403036180b80c4001800b42e0b01d0890740500a04004000740f89801d02c040f028500009105d4000d50342e94918080c0001800702100b84249400385041c17001203807907131810340940484000d001c00181042d6840c00c08020410742cae00da4005070041c40701000400c0d00d444034002e011400c2d05c2500e41d000701500e031802d043c011000c0100000c00d07840c4140504d4160344c1d8400c0440e0b00e1690403070030007076421175014200c0e00003082207454010403041c000d40104494900040c02482001c9800080007100d40b192100143d92159840c10300307180d4242a20f1240c10f103000d4441c44d4104c2120b880c5480103941c0c0780d84446000c0b000340c40814202501040780000c150b0709010301405001c0580095 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 973492544 1250 973491294 973491329
    0xf020c10110f0901110f0303091f0212220204052d01060903080703090801050a0501081b0307060513051005070203100c0f0c031815030b04060506090d230102040609 72
    0x21031072405180c1c0c40f00e040040c1c000700142210000c00000c00d4100000060f60f80ea800d203601615558160707545250060360b1805060f1000021341e20030303141880048207091070f4554a02c0302c0303d00008025000010b02c4c1101281080240c2c50320b205041c0700f810f442041e441d0000180d80c3d24000c1c0d240cc1d082c09080d800802c40180a000e41c00440e1904072540010815101c1042d49002d44a40c40c903604072490303541ca014100400060587c0005049414100960703c1a09840b1401601c11504021031a00359104900802699100740700410100d142c00f03140055040e103c100058400c2803801465000071408104031044d0b250034000355406148020040143d0b201c82d00380501360086444005040c020b44828800525000740c0c90b5000e1000d00101d201102501c58002c0d070481c91001c41500c00207481c1a03ca1081c9040030302c225000e54400614190030600080d0070401d010b0043c2c1c81c21212030700d51114114840c1c2601100921903142c00001603100d504000d0010b14038515a4441a40140d00c007504c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 973493794 1250 973492544 973492567
    0xd0c020723180402031e1b04090b0f19110a0306080601064407020f30090a06080f07031a090a15062a0c060c020102010f020c1011 57
    0x70568107103a00344031034015562400082d061114140e06407800da0708a6419103020007000c2001c3c1c0083c040340007c1d1843c071003030405010480714055002011942407501042d04128845400c55001c440b004110003010101c0c02c0070000c0e10460b0380100310000011500c0344009801d40075140241102c03000a002c0ea43c500100240ba030545014070f020445246c01d20b2144803861040c102c0140299007512180f18015100003484401c01200c0c0c0000501480794100c104141c08070391451a5083c0f9031145c0901005090500b800890202c5132070b20f04841007110907255150000300c40700410054582922501d040d041d03d988028006240c0302c01c00d480c00f40c0c034252900d081504c0300c50303c0364180c0302d160240c0c2d105001900106100701800004040180000400d20707403041c400c0e072403a03162458000380c0d00020001940381c2085400020900c400480302845218072070a8420a0280140300105691850700c520f00200e0b40012007030703a500e42017800c003043c588a142c0141211900008a014540a0003514 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 973495044 1250 973493794 973493809
    0x1020708030a090c03060509100b030303060d141e16121e020a050306012714041709130b040e0a020f06070507150305060306150a09050c0d0c020723 65
    0xe90b505942d518980c0c1440303c0040aa8080c2d507001001b040300c0c0c1080c2540030354032100d5400b41d8078018105544850b00e41400b0003540e0003110701916100d59443c107542d6051000d51104940c2d40d480c07181e00014403a0082104009100030b09990140c9080c2d01c1e03040700d00c0f038014401c1d0130a0400d01a10460040001c1c291034000c008040d00e0a2a07540c003010520014001c013032242e00a650610075280007044d0000000710080c014040501c0381c0340c01414181e40101514025810100d0045008000402050681e402041c02c84018411107140c59030740d10008041042c6c070240360780d5088e030b11030030003075142090710400c0038003060380700207001740c840360760000300c00242a14034103000f0351010481d881044001c2103a4005030a00b803006d2210104c41d880010010a002c61b075091081c41400085191081c080204007c0b002014100064060802a4450107031501401d14440d00200b0400c0c91070030409441006a2040103502800882b4500707190764090355080c810311400c0203461603801403203903107415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 973496294 1250 973495044 973495051
    0x932070302090102010f0e01020301141c06020919031b320307122901030b0c07021c14120406020312070320030f0a0c0c030e060f0d0f060501020102070803 68
    0x503015035101441c4004030b002d002500300100c809402c3c051014860754040d00954140c901490b0380c000f0301c8070f2940800503002050000300644250948910300071800d650002d041184010300301d80c80c20000303050041e5080c4102e44c001d44241100200c9a50300380010100c00c0300038400c5000030b56118948021248040041082281c810b4407590403001207610180a40700061a00711020140401242802c042c002c071901e104030000302038000d0703a00d00030204203002c9060320f07080b5240c58942c0d40c0303400b40891981d04c43c2100b41e81c8071881d005040c5040c05141e5008500074451094490302500f207011044ca06081480c06039181034040c04240003980d07001044d6040c0706081c2d62504015100c50806400900c03402421280302600390001e4403905052000440c06448002a144215910521028105c070740c425010b000140d0341043c0040468403e916403007104000030f004134685280c6118115207a0f20070100710f00566207030b4070706680b00100ca00c100c0006103001c1c0025464000f080d65402514807005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 973497544 1250 973496294 973496297
    0x120902210f07090207060e0a03200a0b0a0f0b090105060a0302070c05030f070303110a0f0f0302150a1a1906051815030604051311131104093207 63
    0x810810424841048800c101220700c1003500c00103600c0d0152540030358004d003420755803641000b0310008400c10000c0c001b00c00030780554911500c800600311011015030212055005449a2a100c4001c5105080001c1c018400c0740c000103801008000008159000640703150301c10f00790706004210030f4a8010031910f9818207898016034562300340c034080803044141e4004e66014031441811500b484400584072045d2402501c48550b0550505407075a502d18a200c4010072000c948000f480008614450070103261b4482d0058624082014151140c988405c81e188040640c443d000e00c1d41321130f0802c0003459040d400307035100c50480b0348441030494003000c1031181c64100600080d80f0324005400f6100005a044000d1080c2580c61114250640540094403003d200794034120120305440f014840c00303600030354040c070342858058011080154484041044203c0f07252a0704e25040c0c00d2402d800144083d069070701c0300049180650310860b01140c106010141c100a01480710303110602040103c5601c192076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 973498794 1250 973497544 973497589
    0x33c0f090309280b09011e02030403030c020103090b1f0b0f070b040c0806040f06050711100e011d0f070e1015110f0106051f0903081e0406090303120902 67
    0x5141d140320500c3c00c0034140d1035000809400402c1090084000b0032440400342d80e0fa4540b40c40400c030b00c0401c215022071000250384100300410000e8080c090040045005040000d0b80912945922500d410226644600c0041540ca4014804080d200b004050075600c401c1c0390a1002d005941c926030b00c90310f540680000030b01d100150030400c80001c0180070b0321010f8251005404d151070800750022281c4002c55040f030403c8000780180303110700e071071700390b21500c04005014201800c0d074010014090030402c0ca4003075403114640c07106003044d05000420603042100614145d110b0031030702420300c00d003900300c0340c10348003c1d0041c81826840c9985140039a031800390b560b40c240048120546030582c111058020340e00811038140900c01040d80400222203066410425050800304110b051383c0304c01c0340440119950b08018400318262070080c141e82c16262500c912558070b405201400c40e00280d000380c0000b10a5182481015401180c0910070705030800c00b84802c901c41c0e40002c0c400642100c8401d1141d10f2b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 973500044 1250 973498794 973498819
    0x2152101061b0201020703230d030902031b060304030f2f010b010e1e03150f06100f0203040b0309070b0418180c0b031504020406090303020f030f0a05033c0f090309 72
    0x303048c40160000c030410307021075500c130100201c05800f40801480587c0300f8060440443d8101d610b095105180c0b200c028801ca240d641e0700d9a007501c0d080000342d168010070206813200700c20844136441c41c50341d0b0b00007007510360f01c0720000484180c252485900e07481e04004410b4030801e085d88500303461b002801001d8400007040326400001ca49425409011802078105031024040c3d80040c8000d030300d02035801a5201f034001c4010300c10584400d2502e20100e0700581c41003004002605401c03001e1030b00b145903407043e2440a59100c60220726a0400e0b001120711102014110280310141d200d414000c0041049030041c0071282c3e01c0e11140f0701d2980c400e1a5007404d001002030307600c1a00d11108035000c40e00400840d00e40e0f8403501d00815180b150302040b000340c828500180700440b0008107551300401c0c0c043e019860840c4d112011141d6800180020390a07400000d08403502500c1009001c0403411120100d40b9402804440440860030142c40e5141090040d42071202202002c021034040c8041962101308544 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 973501294 1250 973500044 973500083
    0x903092112040605030f0603010603021c02010e0a08010617060103031202030c07021e04180807020d030c150f0f020c12030705121009050c0c060402152101061b0201020703 75
    0x71881d000c0840d0100090046421a0400090360290300360b68420740950355100203141c2228481e020195001d41410004460306424030302c0082014410300d0301e00c0d007034180030b00460606213440c6c21440c0f459448840c14404411304902d00d91203a07102d040141480c1d40745880140c24450502c2000451980001c001a414040507044a40c0194050142c60000c2d4202c804082401d0705044228452420455404680c56090b08a103181d6a0416662403030408140d003000034407140d10301c2c101d080c0105201c03001c01250860710f822550b025003010116480c403151078018119111500c0001c03a0920500180c00d4000000421480080000c001da0342c1c0c80d04c69441c181d986019194182440d525107104100c01402d6000d00c80c4200c1e00388101c2445651602902800c00d0301039072015101b00e130721040c00907000d4500030800084c5900ba141001345001200d1f0200d01744055a25044030070b04400c840100070066009109800000501e510916171149990000351100c0e0244005071608030400b00342461603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 973502544 1250 973501294 973501303
    0x1090f0204270c02030a20070305030c0102030a06050d0b070e03010213090917030c0304170d050a1d06160302070809060415090f0b0d0c030b09091509030921 69
    0x304802c40c0480c090b400504150034200100b00d8030980341c182842d5a48070360a000009540e02901c160b21400b0b4401d541c000504400b162405c01c800044c41030041c0080828403d20050401101000c005603907442d191440f0415210945c0c049070065175500500004039004602881d0010001e103418003144043c540024068000c0e241808045501000c1c0081e103428594003401f011441408525084900c1d1904600c0b9404112a400310100c410400600042c3c10360709131801d00c80480760b003607013804803007100a812100e0881c0d000014036a190707044400080c10002d078000044107000100590b00d042d01012a8448000c203013402810b802003503060401c1204029101514806002c00b41c440e5078034a01d5004148004400801003100c138900801e080c8c40b03018141c401d0b640050052440c8c10060518003000f0415000a40109544c4000c9203555544050b241d40c09400c00300006c00c010303008000000101e000242440315194010003d0388190340311444400350b514a20401038243e1403d01c0411400c0c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 973503794 1250 973502544 973502549
    0x912020618101206120201020307080d0908070803010302091b090d02060403020301150e100617040326180307021e01090e0a0519020901121512050319140301090f0204 73
    0x80b02000c1c4400d02140d6110f1000403111075000700a0000c10341e159981000d50a45d0a80640140c00812047c40407621140060403800c2031004009402076440c0c540341410340214100703c8035188000b0040040d407401d110400d821007503442d0010140010110300c03c015105020b410782c01215480040c0f8190764914043e00c00568001d03000780031400d000741ca44000100d0600a40040b0748203c0e01207003c08803005480015506103031922002107001007001454580004c0c000c50400c03280c201540c00b17110407440348440040c801d10380c0d5001410008403600c00c544c0c50b440240234540c003d10038400940e4400c4107814023342450000e2481041c000c1c0100c42030450717a045000034000c9a814455040c00f00d500c100d100d000b009a22415408500503000c040e8450f6115450002c2c4401120460400da2607003c0400680d000e000c140505540700d03201d0494200158060781c00307801c0468082c00307215120710490100a4180340900500c20011405091400b043c06040c071030315940c01c0d41174584220359045601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 973505044 1250 973503794 973503799
    0x1315020f06150405182a210712051507110307030e10050315040507020f150f090604020904080a02030d060b0a090f0803041403071505190912020618 65
    0x100e2801d10310b8008003404034901d080c051071801000480a0f51800d0000d8690340448001c1d1104d8071846640d0805200762400c480c0e0072664281d90020b4568035a85120389041d1020b505a03e01400c2c2072807941040e440da0320245003010a05056000030740040f03011200452034079404403190721880c00480703044280d080c51040a00c0001210700505030440b1104404d118121200613030400903a1085031a400181e900303168841d40420280a14070742a00519031121030780c03040707810200030b000700c4524000e60045d80064151001b010b0000c8420101c40907a070080008000b000381e820f003640030640a2000800c05000064007003043e840c518800c0c01215070488040d503041c083c05840302024000745d481041143c011480c842400182c459844200004480d07085c0f000e10304151a0501c2c559815003400e504c01d91501410f40086078246401044050594607596815141d0714003c8103400d002c003c02c0404001d01080e2071003044406c0c07688900800c0b1503810b0710aa41c0300d50042c0481c0d041c4103511061240e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 973506294 1250 973505044 973505053
    0x1050f150d060906051014010c02134109210f090604030b070f0305011a0c010e0d0203040f0f080606210109031d04051302011404150302070b0603031315020f 69
    0x40b240c1c2c6d500f0a400181d0381c1d114560a100f06503440192009208254000d400502c00590551086000e40c4598000c042c5110a464100090418040b60140c2010002101542500ca410b089440d441c201c590020740480101680d0404080c010288084285181180c000c0010650700840e0303600b0640710040c00c00b40001ea112138030780c6011002e110084030460300141c136020030603201c40d01c2405024102d44071102c070514841d01d12003205d007403039000411351849907484440012060b0400c0103510000c51003507000e1620b43d402c11781203911403456540422000c12443c4010b1042e030102045540d04044221000074200501d00040c1c1440001c3c2c5c03002942c6946490880b07020715070801001c0c000745581620f201e0203916048208000ca03107040c0c8a00352000704040e1480010b500403209a17106040e41e0700041d00309541c401c0884501d90800070381c8000a40c0201e5100c040040b00a80e0680106044010314181503144c110710000f0ba2907881a8201e800760760f1704141100d40203100b840000401c540c1a41c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 973507544 1250 973506294 973506301
    0x20c031303030807031404110405060301090f060b01020705031b0906040e0303040f0311160b0c0a0b0108030d1b0c120905040c0305060901090e490201050f150d06090605 74
    0xf03814010704480c0c00000c00d05140e200d9022004c02001ca5101d80c2d80041c1800301e07124210705010003041d0007000d45130159603035100c0602180200c490300704214454038002c02d19007100c40c00203040018940c40f86020364055042800e4402e11544d1021420206035100782c1c841da1103c0005024000152911501d1f00001061006004080f04503031026402600d4803090362001c4200705a44204800c002440e21480b03482c00d001d42d41e040710080c9a1107010400310b805110082d01c0b46a0743e0304080c0c3c04a2415800054081c025040a021f50013890200482c18500301c0907032440503200b06480c550040c10484112001c40000c0d02450401c3e0250001030b00802007050300a5001c0c0c000c24007903c080d88034680c08000015007002d1805001514607500c030280105103c54240060386d580c840c40c03190400092130600100003940700c52501c0c84120864155060442d6107800a4211100606822291074041003002612401c0b201c08210303000e03095440101d45001824580018a072240c0b006060078104400d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 973508794 1250 973507544 973507547
    0x50117070e010519020f0706050f0a08180712060c05180f041e0e011a060703050c0f03070812060a060929041e0e0601080c072321030f0a020c03130303 66
    0x35181c40386d4000132159000e0300c5500c10b42c0d46000d80074004110100800458400c00d128940698005048043da15420f03c00c01840c1c03410149960003031a1004c41a801c007909004490007054441c030580d003085490460580d0580ca441340c94668210700481000c100e008881e2107a511410320103540705101d00800b10a2646000506000c500c0081150b01b0141003085041c01c01e60412102c0800030001440c042d1181d40607074280e00140700c004000c0c002c032101086411801c0c0001e0401c00e2084a54640d01c01c40780380242000080684440d0217140d4a5000340200c81d08426882d054401c9500c5404001c003e085120055001c6d07a5001c1e29107010100d40003c682d0411640d00c2002d03240112565074180c1c4034030303d0070be024000300c0704180068a46004900c20740e9882c4020401c2c580038084031844100302e441d01c0c54005588000c400b010790b0000c40c40140101e14858188290004005104e1441c14003100c0f540c0c0402c4090b2032410010303800901a810518200202d800c020302002c160100d4950302d090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 973510044 1250 973508794 973508803
    0x906031503010905010507022e0507140301090b120a020307350a0606081c0309080919030209070e03120a020f0d0503040b130807030c020402040b0c010207020406050117070e01051902 80
    0x304c070700141c40742404143e1200003907801007552440c000302704060815020180070240a001d01b0500900201440c0c1c46040d00c0c06200030350203840180300215203502d00e0414031820301c0300680c5250b07082d0410400b48005035004642401201c00d80c1c1c4003132855000c4c10700e03071701d010051075501d00c10812000c0c03000801c42100440c240c140c02c0d0161008008160780d5a040c00d45442c1c3c0801e2403501521020741161103540039520841f06903002c0e42170b4a051106410125105a025094054140c41d003035404004614000c010664815901e28040010000c00c0c40441c1e0b0b00c050303110000c090744c0c0380400d804408501c20000020000861800c540c03047c20514000381803640155415213460000302c001540f00241028900c81c2c00ba8040c03d1103242201da03880c05c5a400801780003c030381c45a000c200005a0740d07998006000c62603000000107076500f01c0d610410044400c1988414103100c1c505107114031400d41880c0d403d500003d04c0c181080d1008505d00102c40b9841100315545003840d0f103c1d031030403880ba400039 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 973511294 1250 973510044 973510051
    0xb06181c051c0207031a130b011403010b030705370303050a2304060324261209062d030402100e0a0b0901030e0318030d090b09060315030109050105 65
    0xb00c030b074a05811a0350700700c1c0c07645801e000c00303054880300402200001d030031100042da02038031a0b072480380c9440c030310383d2a171014071000e80c00b4201c42c0741e044c03401140d0b0380f40a02c40c510800d4001c600600d43e2910b40000325148191200e05034001400c01c2d0749108560703003a40001540240c0c1d18850501107612460040c2c81a01310700c0b03020700051054154951411700083c1030310300070f51868298900382450650300b00d02405d10010380f400700041d03400b051441c445014401e4405001443e00c200301e1b801c1d001c0119050b10f141501c0e8050f99901507014544040741c21001c8070240c000a0310415501e04a0084d50700c0680200c0f02c140e00900740401452143e900c90340003440c02030784203ca00300c08a041261089500320b16202c41c81d6800122114200f00303421203e001001302ca0810704000c1000c01d1488221030070354109128416480c0d24002c0340380ca0314601446030082c503800300c2c100814418207000d030450361030183c1d458141c002c0400001185806a04840100400c00000c1c024415094030f4a0502c1c00f801068 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 973512544 1250 973511294 973511323
    0x70e1c050114010803073804050f12190c1403070b100806090d050315030a061a12151e040c06030b0d030210090201050c03070b15040b06181c05 63
    0x104070044d010045030440c1c0e0300003401c050b03c0100c49181c451581c035001162a8191b4030719008038900704181e01c2e40d03881140210003034240000100f081c0c0b418000d411000061000080102c0725400141c4602041072034000d14000c54580321600d000680d20300800540441d910021a11a0400c000340f500d45100388640e203080700109940b503032595522841070350740542d2030b0000d00380050b03403500c65400366a00111180d1010860040030000c03c0c2802e4101409544594440b070720048861800a14230741000b200380ca130b11190490210400352500c1c907441d00c0d0703201a0096400f023101c00b64104881c178a1240100310b000e008d03003014036080610004903c1064007190800707810380d0491030030395041d100140d01900607003a48000441c0d280024289010103c0c103010f41880018250502080035002440c440c480c000300c51b041c060810f001201a55007014402c6051084003c0c403601d560b01681c07111a000200b28180030054400601c195480202001340804041c000c201802000517050f100070450 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 973513794 1250 973512544 973512581
    0x2030118090201020a020108040521092115040602192102090f0603100b0304080406080c03041220030d060f050414131106030709081006060206070e1c0501 68
    0x98090032065074181c040190240e00b00f00d60b0710300035500070404168003510035020755070390300d80008240c640c000300c0c00071041800102040d6000141080b00c3d00301e509a002447d000c00c40020148103580d02c00c1074120f0701c000c1d1420174001c58200a410b4042c8c0c0e4408100c02442c4030200b014400042600341d040140c000c03050350744c020000c12200706108940040700060010315076041111b050220540c4040d1940c8000a4039820001d0910303040009940518824400c0300e903a1441c0c118010169040600b0844040c00c08005202c00205141910818100c4508081544214400220141626440352090701c0e000c0022a62010f0074541d11403000d40d1240c021601c0100d0f115820320003201c51501d0010440c260b841c0115540010350050b01781030502c101d05040e14042c0c00e00201c0c03220b402c01d845078000300c0c1040801384000c51080c00111158103200208000342c9190100c02507503040b01520050a025040c070480c4443e440e4051303200c001443c0700c00601c1c000300c504e103801c90081c02031141303003004100c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 973515044 1250 973513794 973513829
    0x322080a0507031203021201121a071209030e15040305070b030108060601030902010216030506070f0804170f0715020a0f02010b031c14040b04051c12080709030501050a05040b07030605010c0f08120a020301 90
    0x450f080ac54010045648c400407000e0585210f41c00400d80e0003400e8043c003910f230b0391030340b01c681e55008420605107107000d00c1c1b9240d6246d03140883c41c1c2001038004031180c080603c0107010100300000d03403c3c9d0048003460046001415400185d0402842e1119501d210007942000300901c14000b4680340211000d0b5036401308490b800d0350848880d03000f640c0c020308110840001c1030303202c90800c01420030300c9202c041082c80d02e0030715994008000c0c900409205000d4002c103013480055002031800130b40e6a0640000c1c0162421000002d4880105080a05005034440714a0552510a40280300100e604008096449440d90000e0f012600280314140c8640c4840340c86e403400c240a0429074502951144030003850900c2080c0a9800741401010001088000103002022a00034000d580c000c06003a0f038002100d003040d040080002d04001c00e0390040c90708000b020401a6030001c00f8400603034110910b042c802626160070366403441003030651030090b503040051002d01525980214102e50222040110260 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 973516294 1250 973515044 973515083
    0x4032d020411070629151c14040f031805061207050f0a020102040510021609020c01092a091503020f0d120906020c0904150b120322080a050703120302120112 69
    0x2810007140d06045062152100300340383c4800c0300d030703905800da1f01c00f0550854214070012107004c120b03820b0726140340401c1000145a0003804405440000c606032420460410700498030a1245105215800c040e0710006520300744148162400303204038210050751403181800003800307074001c3e0007042d100d6000194066141d5000140d190108999002d03441209440c1000f40c40094100401a102a54888000c04001107140702c0320070007070441d03180c88111180707000b404002c00f5400781c00040c0c05e0713132a000d10103c100c9110072400044035811602d4020900401009c035180c0028504010301c81d031010303502111502c1c2c1118001c070541c1c0241c1c1c00c6a6001002e041001142101502e0280010f8807018601c0d000364802d420072041307110040c3c50b01d4166a5160405855540450000320030701c04481000c040c8125244001001445220000d2241201d26122243c59448610000b025042c4114140c0050360007901540c2c0c41c801d03411303074280103036a5070802030000c0d00d4103900441d05008402d0352030001c0d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 973517544 1250 973516294 973516309
    0x18020a0b070f02120c100f17012615090a120201051e0c09031002180f03060a02070312050403021b01030207052509060b04032d020411070629 62
    0x1680045508212842603020312011310648032500b600790244002400e11522104c0220030720150a50304e191402e0707030280300245100e0440d40003842d40288500100001c0c2c1c1042c4080d149003400700c1045810740c5c682508a4503141e44041071400c0c0d034818004000034074001050321860b29005012803607801c03241c14412404c1b83d074115800341241c40360402e00524542059115640504a400308a182030b100741c000030b107805c50b25014110034580014401c0b0583c503100c001d5024074070003035a20001e0ba444400000c0d440d183c0c004c0c1944036243e03011421009051050480701d554502d4034600b080281031a00300251a0440490006c2400e00119054003007544079200300c030401c035049406007954060002104001803064620031540c2c00384a407000c100e68025204108c010003400340c502d503903249140342c68402c01f5031208410840c2080001d0100c100891250800d090550444000583c41c85448c00c1418a01580c10301801c814038200c60b0b148103170b40c6020030500020003d131462000b540c4032001c1003100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 973518794 1250 973517544 973517557
    0x31902190f030f02060909090c010927050a0b1513060507121409040e011d03040b0f0c0109060c03051f0b09010302030c0408011103010f06020105060a0501120f18020a0b 74
    0x94090607041011628030300048030b502c2d200428140c506000c0da4000760f850309080c0c43c140c48a410405091a00350b80003d010030080200601709011841c612944caa400c0701c80201c070502d841e0304d440000d49803401c40c1d4000e03030700024001d002107400c0e001001b001c40c464010907204800d01e8003108000c0340050050003507030480340e409800c144101c184c2990071514008054070750b82c0312500904c0f118400c0d41c1c550052401c04041580002241c601c000001c2948100e08001c0d8212a04204001d01c0041d100c1000c691900c0300481e02a6640e0b00c107507070114010310a6400c00303000546840c2101200076450740041d0301515055807400d10b0100300601c45100400307136200792800072004010503461940030340c02555114861208403824545c2d24884142075842003c4000001180040140000741c40c842c54840504014402085030f0716101c804511189028014141803100e009400134480e5400c4c2c219200b004403121041c0a8040000010980031984e208224800c0c00211004906014400c0a8988 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 973520044 1250 973518794 973518809
    0x50703051608120406111f02210907030f0c12030f02060601090506091003110c151f03230d09080f16090209061e07060b1f031a03190219 60
    0x60b007880d11400703507510690400c4400090080d81f40048105c12150b0170550311041c515400340e134805400e4002d9148052008a0a1044400344244002141c000a01600707503603109410307640505450a00203400009644903065410b400b429400030036600200010409000b9000c503862500c83c80c0041d01c03200894081c2e10781009051050100c01d03e03002581001702030182c2000106c2070b1003403001d0b400301e9000c42d90050043c0d100704040e00303000c080084270661060f0b180e0741600c0081d01030034910f0000d001c01d10004d0000f0342c02945582e00207050540098404038540c0482e649a82c1e06d0344c02030004c2405d4401d00895000c0c8600e510309030440031500107404000b0b4100f95500e40d040860a000035004074042c10341100d4140821040408550200100a04032140c030a8682105140508c1524465600240941d00c0a0900c80e01d845204402d1848816941000f1409107019001070400f40040300d60780b5494030503d0310007032a81023f00c0456850038001d03218160030900c11800407020000600c1001c0c1d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 973521294 1250 973520044 973520047
    0x10e01170703020d1116050705060712081e07090510140f0a14030a050a2711120a030c0212300702041a030c01020705010c060905010905070305160812 66
    0x3940544070340d0042041030b107890b20015280e000e4132002c0e107044d0017006006e8000d403401ca00e12410b0003401c11401d001840110340039803900d00103039918640a43c0c104440c100707210685c800705060032100e9481800c00303030480a1074015460115002440c8060512640d406a8468001030418910481d002c0c0700c0980000001440c115a1144d000034036800b5030340200406c50b1442e180424218004000c50054054040110360340c1040709005080300d1030400418541181d000714000820507102140307038095045000030220821101c007007036006003d030403c000c0c00e002e01510b500406800001c80010540280e40d0710124440c1942034540c0c800c0307240340066003050903094518810440c2a480e0b1200c0080317190340ea007084560b50100f02910101181e141c0700341070b95a120b0100f82410488011043d0f424030080410504d00740000c1c00c400e801e108007405d05074440e030414003031103425040706c41c4166000b0f040340d29543d0340781081602c40c3c0e54a41424041150391000295101c8009079801a500d83c0d840c505 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 973522544 1250 973521294 973521301
    0x70605010905060f090408040f03030503090d050909060108070c06060b04081605180403030608100207051606051b03130605030412090e0711190c06030b010203040308090f120a11010e0117 82
    0x2040f18100101b0883d04014100008a8208140c1c1d040c1001948640c480035160f0a00c224030030b0074090f614420000304181400800b2266480c00010307030f04032000303080141304c0781c0300c00608480465010350301810142c00c0440005042ca040e80040c011a240030041c1da1649a8001026060b424144109a4000c40790011030300020758010301c003070700b0a02c03e080004045680d4010503040c88034006441c0c62a03a4003083c1481403140501c0740c0e0040d40c50348011170300d5160800300082e20328090765145241c410030900060952000c10012103001101290040c8103866940d0802042d40d8400c172811070780d22044201360206507001d480d651007607404049200d034882d50ba1850860306001400b00300c40c05803240b0f03a601505c41d6101b122400070f0701c4c014151090402d00340785000d410f4904c403d84950455004100030808255070009036080f050007244c240540010841c002824480041058040c0b806251030b5002046000081072650744020303254103880700c2541e001900c1c3c12107244150300e03142d100007001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 973523794 1250 973522544 973522549
    0x1406010806031e0c0a170718091a01090b030318040c120903080105030105150a05040f0b060a0e04050c0f031807120b01080601080610090207051f02070605010905060f 73
    0x60380d1000700035045a0422400e8400030350504080d5001420725044a00d1030f045a0520348440c101404a40ca60585417000510b1006d030b54860f0781c0304201c5132511845000c500300c03806821210700650010102c41d5a23030f0354040c0180d0142005c1c420a0003052a00c0444407040c01d01000b0f5520840800d5507405100c40c0328010700015008042030001080024000d07240c2c5401039205000c03a05000350b6403103403550304120925085031030160005096016080c103001030742d52448541801c0d038000b96408a084040346400700081c00e46041442c3c0d1020001c0790740150140d0009006400c500c0c1141d040c003458443c801d407a0301c2c034072500302071000c0e01e10b08000140142020214118103c404c09007141c03007032903480900d042e05143d90f81044405a9405004014130301040200602404840015003002c2c01c0507140070204100605c90000e4098020441c0d000f440004d000c0c06420302100c136120100361883d482d15200a500100c01111030528110001c2218081407184034800d0b00e02800380e48840301e02408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 973525044 1250 973523794 973523807
    0x1401060509010c0b010b120702011b050c1c02030705010b09040c03030e0307180209130606020a02100908010614041503020919060b0c03031605030c0f03070509101110140601 76
    0x41d440e040c8002e5550280008000e40e891500900d40c1c2c1170780360b86401c40d440006024040c054001c808682c103014004005401d03c15922080d80643d0030055514a024209241460f21040d0813104c14020b407070100b2400c0e9008001000c10b0781c8039000030001500c1c1c41e01003140105c1d06030f501034140040280c0600c00240280c0d94070055078030042c210340520b0368a0190341190540c54021405040d00414034035500d00b810292150317100c1202c07400b80281d60614000030765583e145840a071064207116902d8002500a03001038010340700450083c8921501d5506210030700c080d000c1e10f6409640342100b00e04280b1000c0c1866000d880d030040441c40705032100c2a15688410071a40609070703141d43c540300025050705400c01402a1012030003e1903c03860860b0707407960382d40b0070110302d4420300804204011031a07110f01300b2030301c0059a40d0742d1583c40303446002d01142c0394003a1120141c0c0207081e0708032198034150888004028030488404440240c41c0c00342111059549040300119a4100e84001c40c40c698000e59 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 973526294 1250 973525044 973525057
    0xc0907020c0405150a091a010c021201060e0417090d02131e061d04031403040c0b070c080c040e030909061c0b070806060c0307030809070b040602010b0907020114010605 74
    0x41101e60704400280000c00320f40050790140308418081e8075200080c20300d2440d00c0c0060044090820958102001c0940c0300c4c000480c0103030401100304060011542c07203021025a0392807440003003180720380315040c0424405007540c2c255141e5400c2d1240f1882961001d0448080c1c1a0242c0010b040c2e0080b9400c2c05100c1030007103080c0d4800d44d100c0500161400c03d07090440301103040048080350141ca00071010310800c40d803c0070402d500c03200c0410040801e4000b0860200000b50104041c0e5903581c6042100403221140c01220b02940b000500e9401c1c000113442002c1603d0302d403016941d4800300300f4200003c075180000c58621540083c4600111442d09154403644140064010110b0700358200d010101c6404000d41180c0307090640c0c0c01d120741c2c030340d0010050354004415214140380050403401c881c3e0300d0007641c50080c204801200001c00d40d0206212003801000a1401c0d00d80300c84d21220068040c1a000300070380d004d0f03030303a4500055425105008811162042e010744044590070801d04441c1507100c3c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 973527544 1250 973526294 973526297
    0x90d0e09152214180303070503191104030503030a0506032d030903010617010b2e0905060309030d0e07030b18160f1401083105060403020a0c090c020c0907 68
    0x103030041110118075014080d01c2a1410601c0c1c100da1401070b80e00000388000c90386a0890303a00c148208000580c000003100d40080d04001140348403060b00342c001010f82f80f1004907504c100008903000041210000146018210140d03052100780d41d00f8050517076805580c1c244010385c00b400d0340400440d00c9812200c2c81c0c02c4601400740d0f46004140c2003c642990510303440700000040c20f0400b540c9190082c82041892541200c113508130040c84810484007030941d00701c80201c454042c01000c0490f020f00007402c0106000341034240c40c1d203444d4100c940c41e904000c0c3c0d9221079a04103100d20704d4680c00450440140c1e5403191112019864080592102c803c40350302c1054175114001a14403c1c00a0031b100c40e001300120116103d0560509901003410543c0300c2082d418880f41c007080c420b03100c44080091000a100600d103003842c40711840c1e0f540390001d0701c5001422500806007844103055000c6605a030190007102e110802c40e9076400c0080440b10b104d8650001070700300a0b002940341ca05405205d4002010703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 973528794 1250 973527544 973527589
    0x50714010e0d0213021c150e0a0c080117210c100b0303190c14071a07050a1403040b030a020c0f0a030203041223011e060b030402040906060b03090d0e0915 68
    0x86c250000440e000c0800601c0c0300040c16004104840e4242d8401d0750141018500744204070540101801c800018028029a6421481c261282d020100100d1600c40908881c1e40c03d0140c2c011445003041c4d200c13140d214040c2c09800c04000860440c2c2c080ca4818000c050000c501d4451030f0074910040310000d00c0d20f00c00300100800440e000c140100000300c14843d101c0c000d406190b20706407202c4071001e0014005081900c060010710701046000c24050210358000c0241e982440705c441d8018250300c00d6401c5002e0030903020040c040c045580ea8054940c120b070810468120b0341286090070b0743d42055000050040e0310030081800b05141d079004d503081d0903108040c1d40810f0041c0c10f60001c201c500e00c110304006a9929211540400722a00d001c1542c00354a010800035241000d810390304038400200007034012a1070752281b108200b100c2e4812001441c07402e25841d00d80c00e040032003541303c0b000c50444400244070202809040e11b403c0c0388030f6018010085401310004071003020b1040c0320820400e400c92034104d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 973530044 1250 973528794 973528837
    0x14061804091202060712230c190c050c0102010203040f0f0501110a020a05120910110a0204020c1b0f0d0f2d020109080a1707080403050714010e0d021302 67
    0x52507860030302c0085801822491910b032000500324100180c8001c0780b0b6092086031452602c1c41042c0c4051901d00d0204018540d858515080941c8a22415400d007080c420b030300c001515a0100c91545000e1003032055402c10300e2110012402e07400f040c0e5010b45092852220480001c8240750f111503814811000401c01007042821245690815640403025030400b50b031080401005000d00400f01d1003c001e07250511001074045004040004009403e01c55030652a50410100708101081030381d00030410356a031700c2840030941d194041c1c0c4010700d06040c2135500c01c0c0c2c11841d0403200d8681d130440250514186044540701c039a990f1000c0001a03403042aa42d000c1e58002c3c10b44168107058a03440c41d084020135920b40b00042460265602c820340c2604401400b100040707442000300c000d1003210300c1c1251100300b20f00f401070030341c131540d40010007610031309034001840301e4003150740512031001b6201c4686d00e250a5050001030307403a0b110000e50001500e0080240001e0a90140c40502d842c550320545121 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 973531294 1250 973530044 973530053
    0x105060a0c0503040b04090e1b010324061e020c060703080403200c0a050f0904060b06040e0a0f0b0303160627060204030b0c040f140112150f1406180409 67
    0x911035040081031700c0c40040c060000000d2405400c1004000a00800b0003c550030060805101040d1040e41019210840090800381e4012905064010490501003841d50348001030080c1c0e100220078220300103410109080240042030191880e8405449540792807200e5900710344400004101700d0501c00c132140a890003003940164101c141cac00d04802881d40342d00b07200130130407014102da0045100c1d0001300e403120303a07685615291036005540130030080340d400c1d810340000b919030103075070400407140c4081d80401070760614035001040d484020140410030304065a05040e204c0c4240c104140407407200c81c211000141c0e8927404016805190b040145030300c42800d0100080c2e030a103400946032507401150500500c140140400d0704010188003007031410b450440c00041c2c03113600c2d100d0f4540000c41c00d03030380801603402110440d00081d080b101c108109002e20b01000c00c1c1e024140103055200604400c04030701d0401c2d101404401d0b650060910b810148030f03042c16a52210203d000540254039180000c0014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 973532544 1250 973531294 973531297
    0x13140d0f3f0518010e031303060b03120d06061e050714070b040e220510090602090d0f050706081506090d020607080a1806051c062106140606030105060a0c0503 70
    0x3000f401040142d035002c6400d5950a41c0c515986501480e002000414054000d00e100311084a17400301707011458a6a440000c0e05081000640006014000417403641d6416550300507429180d103034a4102d10207510b12210a20001c1c0001c403117011600400030000424800c42d1030f8907880103a80101d52403940c58600303944040d086540310003040506c0d01c05000d00940701505221003109a84014180303444281c4800c0d0391046407130b0341c046071144da5084505c14440345404641a111014000003040200f0b0b2034040741c2c400c1401d4060b24075000328000130810034415071803540a03070309110440300000b40f084108081a40030826a0b07501a400850103001629040301525901c0d00543d5456100d03e00c0c00c10240c454007054407d908140180581400344640040a60b88020000c00740130000ca694040d40e01c00410098101c540d071414042c0c0009072140107000d5501c2120700c22081804100350408118018110030380702c10341e002d00c080c03006100c01d05000c0d0141407060603616251040c05e04580720141503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 973533794 1250 973532544 973532551
    0x11030a05100e0c060a17040c030209010312020d0c030f030b030c0a060e210d0815120304081e0604020f0105070b07050a0e2713140d0f3f05 61
    0xa080d25000b041d80384030001d1007400702c03840064400350b1070400c021800503d1280114400340130740f1040b1005c1018400748c0c1d50010051540036000540c696141d040500141d07034140080c070300510501000965992003a6083c03070029505458840c50007e4071501a0f000c1c1800089080e0140700344072000d540796440d0718010000b02030588980d5a060354030000e000b0762107051300e54040030030400f5003c004c51281c00500710658040c1485e026132241c40b04040201c1600c03021a80a07402040d10180d109019800b00040003185c800c074044406031080d408000318402200140e0000b181c100100140260a080805000c42c40c03051403c00e00c0c1864503a00c08203140300a0314407900040c0c020489038a110740111003000e40103000c4403902243c101035260115026410152540041403190114800c510810090411076520510003004e40d0280c0d2216035481c128030503040c2c0041d030f01e04418074540c0e0103110011003144207018a41c03482c1d0101110076140724140c00c50030342e0460350407094650352031103885602e00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 973535044 1250 973533794 973533823
    0x1e150703030e0601080601090209010e0d03030f1802221506080403021e030901030c050d0e100f020a020a1b0509180106080115050415050312030f0106050f0711030a05 73
    0x1211001420020112903904004800e80d61282c1c0c014004032100003516070458154200140e0b44690718801290000108800300c0d4100c0d2a64a0a50405030190040d0380031102d004001c0000764000034010a82010191001e03410031445114802c03450004ca107002e2031039601580106052107620344440c92042d05611001c00100003c050108165040c004d140703c101041d0590340c0342015448240307850b48584121203052590741c0034401e0309140540e003903480b91103c0150400c503513409000b0007904e801c0745540d800d42581c605500c00301100c01510039162481030755402400b0341c0600350340e545404c5500d00c0c0d144000507542100010240d44410500c0e100d1001000480c088117183e1804900307454150b0482450f5904124552030b010350030364001e10460380100e03000700340000c1c1c4d100d081d0110040d58120a405009940032000c092507004001d40c00b0340030403011800941e0380c80c0c004850301c1c0100c0120341c2d0b11030010010000456250b04020f00c0510000342942d9045117690384441c0350001c1c20b800ca02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 973536294 1250 973535044 973535047
    0xc240f070b07020d0507030905040b0d0213021e040807030f080706020403060f1d0c06130e0901151a0706020304061811030c09010806040f0c08011109101701051e15 72
    0x40465414030452004c0e2005040590500c2c802da41c000e01402e40c64011b59014035610001c64882e5658a018850000d40103850709005030f802c81c0041020790301402502000144040c4107441c40308102c02190111501c0c5000f40501c9811540c0305250303102420801d4619410511610000c14818401400150f10850700080d13100c000600c7c1000b5504800a8030840e51401d006100348281c0200340c840c95032804841d420760382d0301315a11000c040740241c0c12001c201d03082941081114141580f040c2084038007403580d52121665003141c4013401030b020703140c0f0021000c144816000241c29401864105102d400049250f21511a0b128204c101c000d20948240b00b1520190405003001e20020740d06200580346030b121981010f00407950b40074050030007807000d2848000c1a0920030301c5444580580039800c000c0c440d020550541403500d810090486224083d07044040305107600500610740142590715801c10140c1c42c01081101e203194176401070510f070300d8003a0495000d07503450409400d600c40c140b0509 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 973537544 1250 973536294 973536301
    0xe031c020109170909011401120501081605090127060305060f040606050d020303070f1a0114090f090d030b0406050a0603060f0b0c0a151b051b0c240f070b 68
    0x21420310621600011a6042007010b00301ca9210030749070031b0545103c00d065400b0030b600303140120f0342400b40e1800895064540000850724104c0890100944100c402091400035180c404020621a00384689072031120305904034050342c2065000d000300388060801c0044d1065682c1c9601c2c1c1012411035200c5d040f0003002040204000483c40780e100603103819600c101c1d45590325804207030b40b8452000d018040300d001c0031401d810441c1d2050520032801d0032803400c00b06542d40f100c8180350504500c0d240c91203111400c00280c0d40c00c03c600003040c40756020b2002404804641d040560007403002c01302c960380140c1c40f40c80c046184c0c2c40300100729000309410352340003440c140703009000b242e580600c0c2c021001c3e900040082c200d112000140201808d5008524441880e072a000424014401602c0c04000b120314000d2201d622504200a00705c040e0500b00e15403210f41c41a4105515a58604860741e80941c9600307003107030240c00a041d2560305841c071078160b91404017102a58210f82d08290001c0b540c1c10040001c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 973538794 1250 973537544 973537553
    0x4121401291905030706120b0603240406030512070c12030905060c0106050312090909010905030d0f06090e010c1407020d020f0102010f1418030c0d0e031c020109 71
    0x2034100c640c0401994a245900c00030701810804070341c0d20309a2091103910724000191041d080004010400207040781e100e01e40e1280050110010010702003841c0386824500d0b82182050011207100d001c011034050788088201c0146007000560321940c0d50090f64621010001840400000d0f2103148004c043d503403103200c54075180c80c1e81d000540121804080540300b0b0800030b40c00c00c06a03c1525411a03807151584582480a40104256407180e40c0c14424901d80080c110144030062443c030500352005500c50741c40c18901d81c00da400301e49004240354010020011680d01c1d41d80f00072104940348002080f403560300c002c80780039030340452100070301c2c5e07555901c618000030340014884042540340c408241c10002c1e60740020300b101e00504006801410489a00f5080745c0c400e600501512509140820504901408200603504110b52142c150081010f41c0d8100e02030000598241100361401010f0895008030203d805003d2813610302c2d014031600f03480100e101d414103821a1851072a41c00052059846c0c1013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 973540044 1250 973538794 973538801
    0x230250318080703080909130501020f0301060311180105090a080105040c05030607180501030f14071701081b0f010216030b090d030903321b240103120504121401 71
    0x80b49482d8048801013001039550020340784c54030b00858020b9502d81c3d541300151081e0082050080081d4400142c0c000301c112488007440c142c1d42c80d035030200300c040080e8815218502c100300d243d424a040070b4680401b0b43d0300c2000100403500014103030240b066500e4070b580f402c1d84c4058800311907001d02c2d1201403210b070408000e03440e48440c1c0751800e000d44179030320103030040c1d00241805154100342d111191403084844580103500401064109100c903072405080050040450b4560074004065038400040d16210016036030382003110b140d2540002210680c10000c203603034250219030550196040741c1106105003a9050300841c09001c00d070f00c0c2850002c0300340e030a0071700c3e0356074010625180080784004640e100740b04200b9482404000c0010740c02c85041456840c04020740500e506c4000503071a00d405418149000080b0000012a070b010a01041c81d0642a205030710700880e0200d65100400c04a50442c101f00c034656003c0c18000e20b030649600305100b140c10090380c107560841d080120029605000d22 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 973541294 1250 973540044 973540049
    0xf060d060b0d0e03121602030f030f06040c090f0b03060d060513050c01020d1b1a07020c131116080c1914060c04090b0303040b0a020c010230250318 65
    0x406903180049041d0540d265117005486440e4030b505010518150700e0003041121004501500b0303031504ca00e40707040c031003400704411289039005600302403184c00490f0052846e407041e10318850168185c1802d1840c1d103143c580004150030361000003407455402144080c03284a0160072181e146213181c00d52814664504880801e04e141103612002c022603146501032403c82c2212074004040c030b144403013030400c20080030079507a0f211102119030003171140c074940001e41c40d1402c0c0000e5442ea0780c426204c0024404645081c0c004030011003040241c41903100000c000c040841d0722451109080c5900f0444135480e052404080019010b80403103000203022010604001400c40030006040e43c3c47d16040c4200e49008502ca1284840c1d00d40706103803015541482038a018052a02c03105447d06035502d0020369400400442d00e016002d0000c895800b5810800c409010501c0101c0d028400d41412078102685c0e8400801e00500c0b01e800b016018043c2c214404c502d00c0c2c0342c000d903680e850708915400c0040c0e5212141d0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 973542544 1250 973541294 973541321
    0x110423270f0610080606130621180201050a0c06020d09022d0f04090218100b03011a161e12030911150903060103060c030f0204140f060d060b0d 63
    0x21001c01c4250b40c1c40340e000c101c290059160213040d43c0c40788030200d8451b0181c0c50703602c15805054030000c80d495501800300341c001c4a10703000541c010380c100c4010f0411100303400030380880c0c0c2c0101d800400140d402800280340300d140a241c030040e81102d980b122005c03a003010382210f071002c2d2180034a40541c0762044410b0039032800400d01c0300ca48101c0c0e182a8100d064481c0c411401007410b44032013101c0d0350700c40c0d000300d25554001d440683c45101c8070b1200844a00308503040702140b00c1800c00030610080100a81e070503900070b4a08090280345031980f00005030080c24000b00d119543c1d915110010304230324a00903804101e10030301e080c0c00c3c2d814541410701d4100036100108061505681d040441c0800c5504007600c0800d4030701c04203000911950300300d01d106491500c1c3e01885514000010030026074040410040740ea41c1c100000f000500407081640301d9440758a4030004110b07060f4985192120b0020b10a29008003420700c2c0141c44030010044c0c4034154803001c05850080f501107407410007806217607081e5501c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 973543794 1250 973542544 973542571
    0xa0203030709061704060905010b040e03030402031902011b150c02030c01050a1a120a021f020d02060103020d060b031c09030c0902040503070e131a07020c0411042327 73
    0x113004000e20740c0c990081029007156160851041484429446280b03802c5018006006900705007548540e01d50041c0e400f02d011744100b5840700000580c8440700305049034145d40346058010b2032049003900400f40c172020344110400034510702030504603200d040c2100841303030041c5d0707103482c00c00c5580350844100424020501c0d04008010026201803030201003019400c440111040f80c946403005e1404c180221700a42180071040040b04121247d107602e05c0c03401103503007121aa02c2400c01d00700e864403001e1000035000518881c5042c001922500070b001e0b000b8028045860b0341904280c2c0c3c00440c80c503031440401084444609005110300c20f0100301c052d0420031403c0d40b40528000219554461921500e11134151100c04651401d0415906151081e049818441061a0a4006c9164000030b80340b4a01520620b0380c1203000d03042c64080d00c0161810035140500701881c1100a21800c0b1000c03010040c008400100303d42e0320366035001505900c98541e124040400380944841ca0080005441390004405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 973545044 1250 973543794 973543817
    0x1207170f1618210c09061806030206030f06040917180102060c0412050a0b04050c09150d1205040506031509090a0807030309031119061b021914030a020303070906 71
    0x1801c1e511011115082d40303d41145040c2106036401100701c0400070a14208103c000440440e00d41001080c0c500d0080010081103201440300110385007444005c1d0000418000240810741084101d035201c0b001a0003c900a0300c55a204108842501c50445901901262001c640da000780d12075001780c8020f00040205040c11f159452032070041d486020201141c0809003000c2000c04d00c00100c02583c0003910400390700307062030b0040d1103140f00360100740159901c00019440701214800c213a2000009000c1c0d05400c001500c1740354403d44403403103c00500004120004540c1c507100c0003540f085000424021903a40100c0400c030b14103c0161a8903c240e00c00000b403000310b040001101c01403545400d0000b5144160300e415102d00c0c0114040030068084c801255105010310300e00c85600a01c150300420482c1602c001c00d9075540750440c590700060340490358100a90180100380c1ca4210b0007150080b4129010880013071841c0e10038682c000040e00003005110402d80c000301044042d10642c01c18040c006c1d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 973546294 1250 973545044 973545077
    0x80a0516081b0603090304050604091b03110d05041e03020c1503010e0106080a0605040e06040b06090c0708090f03010c111002030411240a0203090112050c1207170f16 73
    0x442c0d403241c480c402c100c00030104a0003503082007100d004050107002c0c00d840d195608032500c024003150090140212071350710038151903032007031180b101e01100c03401085003040110303800d15005020080c01183d08804040400a64054440100f6000c51090340205110301c0b8940501010000345422014403110600040c0880301014502506442a038502400543c4c0da42100001401c0c0e1603002036045841c04170340b02481c402c080382041c826801441c07504119101c0b0014840c2040c000c82d140e54040805000c401d0000b1442002090591001002d48001e040400c0000f401c40e4000c55225000c01e004920008602c2414080c0d00d050b018003000450941c5005d0b1246250072071000200c0c2d10610110809086000306005030004200210030b00680398190800701a41d02e50110798403078049503069410340321408140c0039040c4140d45060380d050800400a5a040e2582c4014040005102680b500c0810340161440e00503c00c00f0501440b0085d0300b411482a6601c10308800c0340c008103d108505c0e82d1454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 973547544 1250 973546294 973546333
    0xa050a060e010f1e080702010510050109090902010c0c0b0901090e06130c0c230c03071d1317031b030708013c06020d18140604080a051608 61
    0x107000c0c00c100c03140041403081200d001210b903040101155a800050314a650320024651080d1150b4000300501c0d100c080322048804001d02c5058002200050140807144058001001c81032060511108000341991260044c890540008244c1c0f2340104424001d513034003500b408001d05440350ba4043c01e09001022640b200b100c00000c1c50f4554840001c0c0302e500703120f98148088039801a45e0b40408421310030382d040022403030301c0c440364241c46604007040c2e55143c085500c108540031030013455102091245004058603004200101310001c0710302d194041500039408502c4141d040c2d007806c1c2c1d41d14160502d250168218040024030040600030403031025006140c203419540510100e035503020000c2c486480074102808200c1c086c2500710185405011b800c015401980d019800351800c2c0f008112040f901c02d10641c5412249051164003000640e0031003905925040004d07020358541034680002c40d00d000700c000320807102540812215518191180c20407000b0b401c2210162248220030416560103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 973548794 1250 973547544 973547567
    0x81b03040204020f0702060309060103061d21040515120c030105130e0c030f011a061c0c02010906061805010503120a05130f060804120203120112050a0203060a0b0a050a06 75
    0x82e070380c0080d407031028404000981700d0550b401040c0541d240341c409541e90b203c040a01c812200716080580309141612034800c2845c91950250041034008800b42e40310f5001702500064210030201001301049980703880c0394261030003055042481c4d032145003900c5408401e40080940c0301c003620500050101c0d6682e1322241a918030401000f00e0510000103005040c440004445541031045801d8600801c0040d00131408081000022128141800b03003802118480d441d94040180c03610030404042410baa400300308203052a10000805607002e981310b034101d48880d00141c0d14044502959030b0303600c1e00c5004140c050803003640900f5015605d100381d82c00c03a024015002c1c0500c2070120720006540b5400512074000e000c10090410880e0361140b000c0c080d03501c15101a90006a003102030f440890000044803404100400c1c0260740f0782ca040005a40484040b4048586000c0e8140702c80140e6020401c503800b9090442d4002107032038802c82084444940da510032801040c040000300081600004c0d445607 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 973550044 1250 973548794 973548799
    0x30f0e0a141914031c05092101050703020c0610050f040b040e01050709051008090607200706030f0c0206060a050622180c02060402030606130b12030901081b030402 72
    0x160204010000d28000407020111100610351a000282d1000410303080b618a1030075401d407180741d4001d401c4ea0b40700b070301d2444045d00420f008100c0d4449900b80254241c10440f00c00140c038000038111500d00f82980c01c2075429100003034004c505881410000d0180c40e8100c000d89040349240c5180c032010034a1040d102a000d031040380d0b80c4126040766116500410481c111590081001e40707002030002d05130700703818090315020700d003108001d025a5000304002c07401b40e405d140c01415140d0b80c5005c212000c43c000c206011003449981100603504008010140207014075807400b007041d880302c002c04011038405490380003c41d4450320512815480d03101d008403e8990980f901692607106021803215118210024011704001087c0091001480c1d0700410f0800811107060204800382c1078220303514882a03a01a605130007083c0842d50038603002110b80c8002c0190440460146c00d03190000380b10818144088070140c000260748030701c0390b1303018031110381c80b075134040e5507000e50f00e441c42d240050703804000c100a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 973551294 1250 973550044 973550069
    0x70305151809011107080309070501050319021b0105040c060f05071a0402010e03030301090c140301060f0c1b03051507032009010e0d0f05010509030408030d2016030f0e0a 75
    0x41c0ba2420070341080c0f030134440f8007812940d20301840c5480e04151380100d640c034509008202010071250705c91401c59001c2d07007040c0104542d10009110f804001d600400b5035100c060070400906803080350078000e492040c0c3c081d41d40c00007035a20385103015014040b6007184074200f0500300300f8400050070710b041c0d081159105121604141d030b0380f480141c0301020110440d82e072501c0701000004070391500d82c0204161452a40d1070b2500188070b0410300382d032404203010324030110f621020000c0d04588030b12141c1031003501480d83c0411800450b0f20300f0400c4042d41d0425100d47d008807560465071034040c00303015000744080c0380400c80311080c1500c041c0c41880102150f41a040005905905a88a2500d41c180200028040003004e2910720b02240805d0440710111001e508050008424403404425201121900809107140c001d00d110f0400040000c4802e9030103104480c101d00705296000c5000c0d10240c8441c0140d1107681005003409400310381c1004410040241044c802d06c25034a4409912080310700840e080c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 973552544 1250 973551294 973551301
    0x2120d090e0907050301060b040f0503190201030c1404080106051c03080606130f1517070909090206190c020a080619020a0314040c0f0b0412080903030f120703051518 73
    0x40d04010070307540600c5e0702d90308010340450104201030050085980d81a1900e91041d524000d040c0c4840180c400d0740c842554140400000d54001d4019469181031840c1010903400410a8820b80d9001a040500e103a9541c1409005034100080c10a2804191004070b07a01c90100390340041144600a1201d40912004a08000c0b42e88101681c40054640354204d0504182c440040e0300c560700c0d035220000000342001304412000b900f070b0604c05008224560b101f0304041d041003201009050b64140480e00500100020316102c503080c0d510b03e143c00800e55401e00081500d0041001c06440b43d0065440d50304108140491001032861806110050500258584640d150141c00410307007014a0900056040208800c02040810402c107640e4032801128010351211342000680c02a0b0003550030f404183c4800701c0c04550040090303c41b417103008045a103024888032a141064104515007014801c000c01880601038244c0600360740040482d1b08400e483c03a00b403000a05094648441000585024010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 973553794 1250 973552544 973552561
    0x60304080c031303031d12210706020c010c09050a0b040303120207050a0c0905010605040b0904091e0b0907140d1407210c05271905040501050402120d090e 68
    0x943c0c0395944942907080c00182e032400c1c05000c910f5003103124038040701454515861442e001d00c03030301600c020400041250034100c00306034414110000e121403c1c200140007000020360640014460450a0b0001051940b0188000f07450007655411aa200c0d602d84041406860005416036040ba40c05150815204007064044e0f0002e104c0c0f4080500300d4020001c142c07080c81601e030441d0781100e241060400c4a6a0f86100c1242d40f4003a5010321610f05a08205c80303c414609138004a0700710b070280b01110311802c0702800568808481c000f0841d6120f14001c10440381c8202444100010a41c02056140c0c5071b4002c00010300c00c04d034090000b07007040900340c0c0503810384e2410032001d8040c003980c0c05110141d9000f001014420b0800d0a41140c000150340000708050803ca01c0301c507010742540101c50510712059020308031564008001035040d0078070220003001c0106038003440d80102c0c0641c00000c0c40e4245401030041010f030340ca0101c18540d00071445408525880040a011194040740c400c1040d03c61803034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 973555044 1250 973553794 973553797
    0x62707090f06170708071d1f0903060b04110d09051002040815090f0607080a020d05330609060c0a020d0b10171216021e03100506060304080c03 63
    0x10190108504440106246402540b1040c83c0d8032803080c248000c0d0340351001185c00010460f040000640304048409222203c0c20540042010041c1f1300d820030000744a000b5074040c42c00701100b00041e01440104103011640c4590304034800c00765005e1000440e044400e8940e40328294180c6003041e1740350428018450103000d03040c0090b0400070150342c0e655407804c0c542c0c0e45407050300110f4502018080480d280d1140069018a03424001028003030381d40c4c41d040300340c03140d820092260403003507001c0003010000005445607903c10f07184c180e8080042ca14980011222140083c00c208801102e011008003641e40c41051b1451110115205ea9075001004051420b10300d201c000290419040c00a4004110f05945664445d00c40c074203c3d0724000d980c991942c800203050411948003600030400800c4490940c00040c0340300305030340840c0c815040c0d480c0e01050701c04201e09600060304102002488403890240844c4a070440408411b100f503040440018019100280005025000004011900301000c0c030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 973556294 1250 973555044 973555049
    0xf01052703041a0901050c1b0414040c050d08070519031707020c0f0a050a030b0103060c081b1614150c0403050718110f090117190c112406270709 64
    0xc040d1b0f0080b40381c0c96220310035911180002380c480c032300303040f004c0e07011010361031550340700d9900000c2003018580340c00103012451044120a0700d0464040040c0b00100e81c0411010348400003901c2014504062420010300b045a070a20020002a007030301402a510350019088500490454a10117010341c9980000d5001440d98085500203c082d01c00106000a2008090403617000b03040600400341c03041c00c2111300b01800c035030f1003101d54141c1c0340c410712040310f00d4050700203144210659904a502c5454542c145181c23440142401e40c0310318040306000d003500503260380080d00b82200d207040600b140d80340e0381c030303181c0c00e000d4009248050300d081c508206580c1c2040d0400c10741c144126584041060740020b50343d21000000e8081450000c2c141540400310b15110701c40c0c03500c0c1103860901c0040d1110103003e86230560071501000400c4044824506007030100f5490b285003030115400c2c0d0464420040218000100303d01e1251282c050050200c0c03c27200640e840010900d045540780c0d550b004c0c07098880c40851b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 973557544 1250 973556294 973556317
    0x51809180f07090b040903020622020a03080a090f0b07031812081b060f0411010306080d0c021807020607120f020703050405090a05010b1801020f01052703041a090105 73
    0x240680954840042440c5060f640030b600b052042a891a06000648000c540020300580c42480080c0304400b480c8581c00d00d80c0400000700c4501d00c40b94002034460303943c0e504207640c40940042d040d031400b6017001c11070004041120a01889074645411002c4a0040d02030203010302940d03080010381552000848400351202c9010520720011500b003820180d004104044036568030329480f80040c500020384217115081300e0030340190030303035035550340724018042c002ca6981419254000817031a4074007032010216620f80c6944e060600005030040054071440d2001084001c0c010000340901d80d6804540300383d11054074140028082e440032402401441242828a041840030401c0307c2050703417180080c012180d048035895415180c0c440080c00b110001e124844015200700f05465010803031031080301400740c0c140150703440c490031f01481174207450040314002102c40b020f5a044841c071210141140c80381d2030501c0158203060a140100840800610800031a5a03012038082c56580c41001145d4582c1c914 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 973558794 1250 973557544 973557553
    0x70e010e04090c06140f07061a0a030b060a050427021c060c0305150a0302040e0c1203090306130b24030d08060f061206060706020903070806010501020d05180918 71
    0x201e0901c090400f40600600001400e00c082801500702907009442c0c0c00e131035400a162034040303541d90300801021031009540c103448180f151a0b4483c1e481600034001580101c5c0c00c0c10103072600208002c0d0780c42039a040b440c0f242d807812030080c0180e540380401c07010788800e440f08280300060900015040702401c0c2c1152403a0303550882600200000c68215211588a90314140310549910209214070300710f00700495000443c0020400c094642900700e03907817001200d425204d85a5407800030500c0e42c1c010258821042c1e000090102d840e080400529520040d05140b0103014115035450140c940c00c0500f08011142c1e0044010f4614003601100e5019810000c0455480b81070050000e4140d1100b00c0760b8130300c11030407458980082d041c06401c86001c91507100386420950303209010042c658000100540e86154207214070200e5031020000c060191030b81000600d49585040700092030406402c1a160422000788810260482d0742400f0611051048a00d218540e48480040000c120024503440d0184074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 973560044 1250 973558794 973558811
    0x3020a090f060e0402090406051f030606030c060201060e01090203041e030e04060f060f050d06080111130518220501240e010602061902040308071112010b09070e010e04 74
    0x20349600c0101e44805204080c440355940703030200c010703404003142c02035000b42203a40040e00040c1d40d1381c031140d404602d030701208144980406070081c040050340c10464145a41e50424014002d120700450f0040415200078040d19042062445803002d0620a04107000e402101240c01c01c2038244011080f04481003c0c2615298242030041a00021401e0180110314000000c0b07045458a810031040d20000c2c0c80d02e04000035000b000315203561040b191030b1487c50b918040840d101c03800f80038500c00018440c0034940c684c0d15031500f00004aa140d40702601c035125180341103034918150080c07a68821700130104034111401034203901484907903d407130060040d403902d0f00c2444031000c401843d00c0000c01e00c00785029015141c01c107044401c02d080c001c55001d80e01500000d442c0005510400b03421001c9601c02508003542c0e6514090580c00050301107170303000e40c40c060400460800c80b415045409100c0c000f4081c07040d182c000f14004c1040980002c08011548203210710300c0c0d0064042405030080900208070500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 973561151 1107 973560044 973560059
    0x31707090e1f0f0b04061803023106090c030e0c18060607080a08070e011803020621151c0507060e0a0b0307080a150b040314010603020a 60
    0x182e0503200418034103609480e0308001c0401c06012921541004805810508100c40d41031390110103038130800159840d1520420050414084c20080011350b114804444034890519951a0b081c008009609407099024030285090f40c1d03402c0200c07060410301e2949599810301740d26885000c1000c007020b1f8501d0940400d4208000130000c62815540d0307a65102c0c43d800410341100450600070030403001176042030714040d0300f1009107080d292103842a80e05031280d090300d00020f40901404601d03213401081421003283c06c0c4404010250051424000f4041020200c1070118000e66600480140d11451240d4200301140e111000d081a981004002c540048410480e543d0154040000044440120000b180604000c1c0e0f2200514581941080182d82c0307008c0c4004180601103030300704840d44440007a28142c0380e12440030007102c1c1d003901d00d090242001d40c2020f984410440000640300 = true := by decide +kernel

theorem cover : BRFrame.Cov 973381294 973561151 := by
  have h0 := BRFrame.cov_init 973381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 973381294 ≤ n) (h2 : n < 973561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
