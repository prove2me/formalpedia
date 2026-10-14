-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1367
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:36:31.325281+00:00
-- url     : https://prove2.me/submissions/9c4cb5c6-87d9-4bcb-9ce5-b6dd5f6912d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 245683453 ≤ n < 245863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 245684703 1250 245683453 245683457
    0x60d1704060c2303040302091513061701050c12040c0e0403031a010c0b190f090f0201090e010b0d05071704060608070b040605030c03040804030b0723120610020705040c 74
    0x85000d10500000030301144034001c00140e004450704220203a40d03613a0059000291181d24000e0100e444001c5011802c3c01410001c0c3c41c03894000c2414480703200401140c45000b810450040324141341c0001841818031440100242500b06007010244105154000300216030740b00311140040b50a0640402e0140700314880c1d9400301e03001c1c1000c000e041b02c880c5801c80150500160070390030b000103011400016404000407101e504121441c9080700080d00051114482561400c211141403081c04074140078003034000c2c0c961001190390380c4000b000102c024401d99807105010300c811903000c40260081c075040446482d0014094182e42001d00c5a0700c4141c3d4100d0784c0f269038640c1006100380512400c0001d100c10080c4600305860444c0c054800d2000030300d09282404004000b40402c000081598041c540003821805c0d140307881d5001a05203a14200030b41c0c201c0001e001d4008808980504480715107401450303d2103603840b0f001c140208181c05405000950140300d0b000300342d40d01c8520034411040125 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 245685953 1250 245684703 245684717
    0x3090b0f03160203090d110f090606090906041e0e010c0e0a09091b08010507030509030a0203070b0c041208040603060803040f0306050a1d0304030b13020907050c012306040f050f060d170406 83
    0x70403119400c001f201d1270041e4001820803410369200c4091b69a02101a510000d481c0c4c0c800001800800054803801d03d0020046410740b0501e0f40c652120f0b20000d480d9000b00a00e9110040590f09042d80044003a0322400b400c009101030321146c1c20510f200c0303115074a0160150316010000716500000d40204038180c0d519410000042e915004a40c3c1005081e8041c500e072180b0188001d48034800ca01d0701401952455000c41e5a00110504a50082140d08220001c03a40d0905d006103260b8403c1c415500082d0418001199011011003268100d0300c074825044000c51865076030b180035200042402107610768500f0030710309451042c11360903214840c1c071002e15500c50071494100c41d2104003030103040022104a5103040140c40e01444540c00c209181046a11903914595403409002082200c6843c20940130000400e020310496543c0100c000f10340c1800000d400034071041c01c80b241140c080340f1401031403001c0389580c109a41030400a074080d550b1950300c0701001c1791081240e8001e0740020002050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 245687203 1250 245685953 245685983
    0x30302040b04062a0305030c1b0d0309020a0b04061d0f0409080d0623210304030b04210f030f090605010e0403030e0703050606010f030e0d080403090b0f03160203090d 73
    0x4000500d5104c482905825402d40c10140c900802602004004040c0000300007070491072092007560500d071140b4540100e85100c100e83e0b034000d001e00703580c6030102e024511900e004a0800314071f030300b81c4054801030b43e10908003030050159403200400c4c1c040740ca0b410000e080030207400f584a42c00350340d03282800354105580d1444122500e00403030f1000d81c4145443c041c2d00c01c1580201146400e010603624003140e807c481c108411600c10517500d521a0380c0c0905210001c1c3c000204441545040d10990081c43e40c4401a18a503080b0304900301e01101d243d00050001c2c0014810a000e03910ac03400720450604005a110a2560307414100e50b003c1e003042c01b61520810401c0b0425616004000c1c2c00100d500140c16043d03c2c0d51b46559480002034000c82c14049000c020500c094800e501040c030801d8250304903001900c0c8040b014190184c2980d050b000a032151801041c84514034084a12801045581c5490740d40d809c185400d1f001d444504240841c0030402141e506903031422407030b120043c01411a2200313911 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 245688453 1250 245687203 245687237
    0x30f050306010e1009061b0201140901140d05091e060f0c0d0905030409110408070902092b02010201050a0c090b0c03040b0a09060f03050105060d0504050a080a1d04050f0c07030302040b0406 83
    0x1850449072824091f004000b02c0140d900007240c2071090918140d01e0340340c200460059400d0101c03103241b4010483d001c108a00480c80503002180502c0840c0301703981c59049074038543c605c0000c282d8a02110303540300002040214081c1700e03c490b4482514108a418180044584025914812420f940aa001140a005011042c49500803099011501d42d103040d00e0260300585072100751051354216640410741d0591038a03080420030102c001ca00d41c0b002560851075655118180966069005610704000a070400005205e1170f00d4a20385030300c54030000340c41c1c2031381b0349015440b120782103030140801d100000317100124a002c0d20301c684d4151100d091150a01800074142190300c8007200415007172200401c0b454036581d003101e05000120794080380a81d01c6007000b624084440500030b101001c0002c000c40320a502200504600700030f0350b01c42d0400508641080169030307042d94889800c14410000c03959100e03041d0020b0400620909000d81421342d035240d11003a40e001a40082c002c40c01214101070145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 245689703 1250 245688453 245688467
    0x40c0c0c050a12030819151805040c180207140a030f230c0f0d020717060c03060409020a231203131a0d0501230d030f050306010e100906 60
    0x42600e41c402c50301e24103003409071081141c4401805008900d40802c071040b01c0150340e0b951407003100609000d10603156144200700b910750b11030303e10780100811a10061814a005a500650300a120308000b10304041035852643d00c404207c0c054240d08014840018006256513114520311401810200d0840e0a000c0c01881e1140000710401000340040d00c1d0721800398400c0c1007001d110120050300c95801012461524020003480d038214800c110820300c080341e00050f04c07415030321148084070b540d01007000b042d80d4503a01501d5003030001100303100281c031600300f9074003107504180000c0840c00c859942d1040c4076003090042a005001000c3c3c0c08240780c480c00d0444100030321250020081d840c00c401002c40da403d5210034001d01450b00201001c402a0080e42819a50050074101d000c00c51542d40c2c502d0315103070a1030442d6540410790030400303990b041d10f05860701ca0022901500c42c81006140b8007000c981c60b0780014a40380c144031800070286c0c010380b14071a1610085403a915682c48643c20104040d10003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 245690953 1250 245689703 245689709
    0x130212060910090c090b0c010501211106031302060409020904110307020a0b04060204180e070f030507061b0b01080a0201020105090d0f030e0f010219182303010605040c0c0c 76
    0xc001d501c0c00c0c84000907880c00203034115a55180000740070700d644801121840c000d60b10140ea502c801180c50501c0b4801035104c1d9040354140d5103c00910020141505410b8101c5040948510a0440c100119062000c01180d106c0c101440b100382449203540056a55086600b0208032a54040744120190501c1d10444840402259107103003149400706000303581d00f400c00002400204920045400c00641e901907030302030903400005442c02c00c44d4022900c001c00c651408000a4800c04071300050390f02142401f10140d030f800401800d1020304180d010ba4845000c400d0ba4400342c4081c0814202003500d45100320b020b0000d48002c1e08020030b050000901707507000030348016180d0b04210050403284d60000481d0841480c01c0c2000b080100801240c01e0800790001c4817444254000194a40d5200c240c0715071680f03502c1e2688a414200031006003030000c4080c50700680583c00e0442c002e4108940140e000d03020b05007001400410103a8480d00030a00340c6855040120211303541d000e01c40b00f006005520a009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 245692203 1250 245690953 245690959
    0x105040302130c0311160314030f1303022103061305010605030105221a10181202060717030603070815060105090d0503040b0a1d0d0303020c070513021206 68
    0x9090568000503295052080004100e40c0d0b240d00010410b4065000700303014000c454540d039100c030904a03466410300e180e40b40480009040c80c1c0702c10141050841500e000d01d00900781324089903244207044002aa0501e002e4080d40301e8408400c01405800380360110340700e0b0b0600070a80fa0300301941442200301d0100544100117041000520580c2d605c50305990449808551b5031a44c41c48550704031a1200d04604486c80d040e081a12081000020046070f0a11504c10b81c0c4440d04080c82c0345c8103c85103888104540528100e0200411002c40410000f01c3e0140c001420b842c070300f0442d69508115a00700107039500c0c02c0c0c40007104001c82440c2c14005800145a200064119404115030591081c50700030100c43c14040c0114541110b40ca805c0d840d11001640a42120381c0c80d5128401d060300ca8000d6210030001509541449807411134000c05c00001c2c4001800c40030382401d540c3c2e000c5e0040d4000c1d1010454610510200245039603440c0035041c080742058100507500d6802003040250b1510091680d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 245693453 1250 245692203 245692207
    0x10810050c0702010f03020a030b060301150f020a05071404060e070c051e0c0d110a0b09100f021c0203093003032a0405090a0c033c0f060e0a0b0105 65
    0x2d80d810517030450071090030f031400590f1002161410381c0180442040070340c0043c00400086000043c245443c0541c40403a01d6445125148032000ca0703450351010801003240c2c00182c0f003049699654500184d039928001e0000c5406503c4801c45500b03448105e40000004103049080000d0010074098010327841c5403c840f05003510150016556210054101240242a0200c0000510420008214184100400703a805a503559061194160000c40c14540704d444694003c94107030b4098000444110b2194028061040444c500b8008810390844010194042000706400f1039036928000844070000c07200142107240c0000640411548512008040d580300704140a101000c03d8030804814000d0300b0324205e0b01c210f50408003d640900c1d840550441003040511560301101d4005c0e044000716581c04200107013041c6940800000c000740c1111400407100f604402007070890702260340303c4030441408620604a126103108480300c603481412030144040c00c0c0100280c841c01118050002403074014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 245694703 1250 245693453 245693467
    0x9060f0123010c0809060a080a141003020607050703060e0f1b030715020c0a0b0720010509190e04050703030f0206150603090a1b0612050c090409080d05010810050c 72
    0x1007291805034810350501c4503d400800400042d48116002c0600103044a5152140d003100940500400c0c0c500466032400c1850b2121a480c424074014869407511014100207491034081c014181d00a60090710140503505000c4082102d81c0100d28000030020300901c600300c48240e5850408401414a06000e250080307582c000759000140b54042d503100c08804ac015540144080e440c141400c0e1030160481007000b00000d44418075805898400d0144074002614003040b841c0a0600d080b540c401e502081c4103110300c8101c0c0c240000da0702529083c0b2440b5121482e22810840901c0f0412241102d56900001040c010541d00203203121240116000070710b41d0303042813403400d40f4003484080072a0007010007000042c181401001007210030303900540c0e480c0c440c0000c051100ca00b00c0860080c82d0101d0072181c02151001030074403409100f4503003d40030509044504080101801ca411402d94502000340003840802120f441030500a0440070010172042465490010540e0002050b603155000e00f44807403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 245695953 1250 245694703 245694749
    0x20405070522080705060327010501030314070209040605220b07020115060509090a061e0e100e01030215040312080708070503071706030709020f09090105061306030e120309060f01 79
    0x4c4098400840340d4a8a0366100e180b4004182c442a40540d580116140380d038620740e03010b5002c10f041c0d9002c1d0f55000c0b4020012418803229100f0480000c0d00480c180d400070700411a594001504441e070700c41102d400c034212444c1d4684140300b0030390980c0e4001c000700c20700c0801602481a420050400c02580c51154034094015100d4001c0c44003960080c000c480002d200c10400741d000d40f0103801449524461055101c0d4000741c090580d0103455a03020001c00070845402c0851072080450340007000c0c03000140c0c00c0d0f03428014110040d600b5003000c013000384000320000d80302e68510468001c0c3c030f55800c401c2d4030b441e5800a00c244006050340d41804020030622100a910562102d080e003a100c01e03030f003c262902c0012a01d8040f0581c800c0100714408581c44560132503200007801c40d81011540d442c03060345c950080210341c0c440e4040001e00c004c4402400c204c0b83d4040c0e00444501840c0e00300350b40401103000712032030050303001700c0300c2e880d8a4000d00c2c01c00aa040560200a002d030018986480c1102c2c00d801c12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 245697203 1250 245695953 245695963
    0x1502100504033501080c10030b0a0f0e0a0e120a030e01090209072703030e0f010e03060a02071403181c06231806072007060206180307080a08070c02040507052208 71
    0x409010103860320300c00409c5403610110384000305090a44400000d1780c4d210001070086080e1803060580c0c0c100260704400d035000207100008141c005110030b181130078070202500108483e004090643d5207501400015994225006229402544031000851402900040424000700140440082c1800184080390340031795200640402541c44000030701c00680141c41341c0302c2a0300d00c150705110750402c114074800d594000d070501d544518005600000e40150b0141c59019040050221204810f1a01c815103040e00c1d8905000d4414005031408002d91b4540d4020742e03884040010800a01c80c00a0342d207000f0020109910907601c0c0c4080b402c80c00f149402c2500d403000541034000b0800e141c40e45403101078806000c00014680c080886448595510b4080d40703881d42201c81c01c01458a24107000c0c80ea400110884480c0b40d031081040d4a40003042e4404d07581460040d040b5810040ca2440440c010781b41c82c4a29800360038191103154032a0300c00c0311a9411103480d0f075604410400f206008001000002032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 245698453 1250 245697203 245697229
    0x51c14030306031c05120a020c0714010207060905181905090319030506090402060306030312150109150c03120b060d0b030d03020f090d03110a0605060a1502100504033501080c 77
    0x19681b42e900c0d80846800070340900124070b035190240c441c000410034000c00d18070207a001e0a07000e640010755030b48000e50b55010b051040a0700704d16400d071190343c2202d001c40c0c22940200c04116500580e0b000840b00821980226201911035000142140c00c6826418142041075050f240c10310041c5004404202105400341000f4002c00c4c002c00850100e80c0c1c00d105940032950386640c1c54100f072510760070601813000e00d070540e00c5c04195100e0000c12152042c5200d60040303119609d805810f0780da83e5030201c2d00007200340b111b8541c1c50b0380c07080322001a554160080c0300c00c002e01c480c0416001641e5042508000441d00201d0525104000c8400b01781e403444260340000340d0480d900720080c00c01381400d446144100c00c00e50014080c503a009000c02c0060b41c8041c0c01440d0580b44aa18182c89008cc22803a20300e003580e417070242e4030000c111999102c0941100d0351007842460030039090401520342083d802014505e1000706d040502000f40307a645040015801002c6041c020248503d0301008504001c001034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 245699703 1250 245698453 245698477
    0x12040e0429043c0c1d0117030307140304170a11060601020d090302060d0f1e11070c14010e03010c121512080a0e0a09140a0b030601051c14030306031c05 67
    0x800c040f0140810700345404028510b125400c0000178174044103200d251400d0007171141c00c3c0031807d80c0c0b1f40005000030580f4444c4415848400880c241120b00c031005420003801203521010402841e0640e03031440c03024145480c20794891640c12071183e01c0090508400600741411544030040d94002c49900c0003000080b40d0701130368a00e80c2d40800020703410213004840f21580a032418181008145000c01803210b207401000304003002407031809484680140300b20080074010f1a10203074103100c10141c880201c00e1200050510916004c1c035040482d007901c1404415201050011041229800c030b180520112480c1e243c259540b220706101110200d01d04044003e0400b01011810b0312032940030342105403000400602c646a95541c6401c91805041040c141101c050300d09004200e44141074000d0000055004000d81140da0828003402640c50105801c1c841240c10000c004011401c00ba414007100c44600c40610b54a1500805040c5000110070b2800c44000002111003641035000d011b64140c08804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 245700953 1250 245699703 245699813
    0x18011b0c0804090903050a1701240203070614160504080a06020903070915180216031b0602030a05070e01050c0c090703270c050312040e042904 63
    0x90400d507285000315008420418070f400d50980a040d00000a85034021456560f10216408400329401c2c0036800e2094840c004d003410a10364444882d1442c841413445584100da007449110b41703868003600d01c490f0032107400400c007100703012039a4174002c400d07036031000b15003401c40c513043ca08031403070b0342d00c040c86100503040705e5003c02d02c06040d80d001c4c0700b00c0009081c1900280050411a140245040820b1240c1a21110a0700b50000342d10214004d03144003000350301f0080942500c5440680d01070300c05464080341b541820802800082c1c00b48040c60180c020340100152500d400200505400c0c0c102c40c1c00780c1403020034030503049200300009510104100c281c036550b14030345805d00145c0103000300160f80003040d24102400039000b84005482c0300001d000b04400d0103c150346800307150300e8560004120202007000c2109100380c510180d243c5030403a10602c001c00d45011960001846414007440d105c6d4440f101e2400d002c10b0051341040b0300c02d00c00a6454030300c6461481007176618000611600010440c1d01e03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 245702203 1250 245700953 245700977
    0x902011b050715080f0a0b0f01030b0a1d06210607030b0a0b03092506020309010c1104020c0d0f03140103021002010905030d0b01021902030309091b1218011b 69
    0x205208035402025550003c085003000e160002c0e118140480350007140c0c0b604000000c258070030034028a8510b000261172800c241030410011005045001a020342154140000190000c64a501e04444c41400ca4104159090400421000d0030701c3c8036803050301280360110605001c130040b440c0c580101d128100003c880810744042040401c480e071100d1307000c01c0d0100402c580b41d44007180d2404204026081030550340848041c1041003003450091300d005130710070b1100702160350141c104040b042e03006814000c02103032110000340036a4022664401e040c3c100701c00001d00150041c1c1d1070b2101d01c405c0d060501480400b6070b03141c0c0c401401484040d205100444540e40801d000b035100d00940c0c0d0700075068a90354000e02d1001409018500f028600500c01c41808203000076010202d1401298010043d41c40c01d5918004c2240765000902840504415001003000c21007402005001c0c0c0d40c0703146451140c40c40d00310140700c40001c140034012420390424000e00505603c1000500c0140745504101752110f0b5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 245703453 1250 245702203 245702213
    0xb0903060f0f1f030203100506040b03160611010b03011d072124050702160e09061501050f04080709060b0a090603050c1b0303060405070219030302070807330902011b 73
    0xf4282d1000e5010f0280140110001d82c003508054030400c0103540621400c00b40d00309041c1d54802c502013100050381c00304014040c251088848c038120641140020812206181c0083d086498583d040742d4400c441001d0003035444414032554004101a0b4010005802c52020540c0d441c1f14401e0001e20700720180600c20101c0c15200082c001e0300800400410451400a10181d902d020102d035010030b04211440005020200090052158003204080c1442e512050348840c10300f841600d00c6818000c041c04807071001d82d490b41c06400201b10540003800010301e455200021506c403038024070340d45003003000340c00c10447d0004074000c1220765501e00091540d40d8621400708074001c61b08416a662030403400c1c98a04c02000001d1409480101c504102d984c484020980e031b24041c4441071203d8004c001c0082e40800e010b580501541d5000f95031052414405959800603803511110080caa08906c05180380e114001074090782412880d001d04020404007074001900b066114817003030350994418032030041006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 245704703 1250 245703453 245703511
    0x1503020d05090a060b030d1218021207050f060703081314010608061b090a03030509012115060203030c16020414042901031a040c0b040b0903060f0f 65
    0xc0800200301900300740040e1625088040c405641e07050410010f501140350220320310762807c0301600d85a41030b41e00c80320003c01401c1c210f1038500110382d0412401000da2208603084100811140c00380400b039050608010100070f000d01c409000348818807983c80066000901030b6004014905456803a030f82c01c1c601300d207a0700728007000d5007419404c001f0001110301002035068022500008154042090111800310310b01414006036030169040d4010800309000d000182424141890200d8015000103a030055070100c8e0811562016035824440868030050840300f030281034a440074620f18103104407902d141c1c0c00b4580c141c00c14070003400c0d0301c3c0c000c640e01c0341c1c0528408136100c611510035181909040b04a104982203541c041e890515802610000565041d8141c80e1b10a0741c020180d9a0a402d10301a0100100122003000700d03c540859825040009003000705500700394591b4078a0203406045c1802000f405501c04100e807101840020050500e02c56401b00c45590740c511558207140da00d000c21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 245705953 1250 245704703 245704717
    0xf03110c030d03090b15030d140f13030b130b06042a030606090e160f0302131815080a020613091e1b02060c03060a05090a020a1107030804150302 64
    0x51180c000b102911a806410507110709004805107001559645e02c000780f80b0f000c00500315819004090110406406111040c02c490010b8001c1d03410a490aa070611440d841140308003000306003050100104130240302e9041d400340703281d11003c010400036600c4100812010785114403464452000a1300305400b59600856030000312042c984500c0d0600700a00105810b003d000300040150002060002c403003e1940d0140309c85106500000c42188011100384c50070b80540f01c1016020808020f001404101481c064514842081c8142c421840840100d40c0003880b45070190f4010941005245000300f4205207440e0140c40640c0e41d82c031041c006240c265003036003150182500c1c01c1e81000c0044120300100343c074941d00000420106c6800d90f200000f07544080d0001c40181d10010020303261410ba1300c01796030046405080388500c1c5440e0341c006510502e0440754200321a50200301d81c0555940461900140800d02c0b0103010024215140c9000f00e104d540540d2000c1480070030040c0381144241e04403404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 245707203 1250 245705953 245705959
    0xa110607050a150b010f09060305100305030310060201180c0b0903030f04060306030302120304080d0b060c010c0305160e01082a030c0705060c2502030309040c0c03110a0f03110c 78
    0x40b00e429850900c80c01c86021421403511880c10822100d59402440c0a035002101902ca16007905d24042e011405444c004043c0401c96194040000000d0020400703980200c2d90201c240c1211800c2c264002d0840d8403001d228500909041d004001044514405d03900351050105e969a0700c03e01140441d185102d60211643d0480c0002000500c1d40e61552007030040d680309a00b607807164a00708804404501042c0c034050074441c001c100114980315158042035071901e01400b400d0908a084180070700b15110b80546601181d1940308101c0c0700c0c03499107401c0b13018503031a040c1f130051a2030381c20001300b241c080140354850001d001241a400311224040349040c3c40e004204c001ea0300c2c6843c00140405402540d0100e0700c0d03101e082e0100e012060464240c401c0e02e20038810001c02c034011301c00c21000411408c2c8060340c01d4002040715040356200c500500300b11034460713107540d41714a20a19000b41200c0c070b41000d104071604000d0141e400104400410000d02c1e4041c0382c0017400460200185060403902c03045264 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 245708453 1250 245707203 245707213
    0x20f0a081503070e1504140c03060a0911040609120b0708040312050c4302010e030307261603050c160e1905011805040c12060213050103020c0a11060705 67
    0x540c034940180014458210001e00d07401e03c2c0c41c0c11701800240c0300c0912240c468140100f0009184096540c040d5500c0386000b444442d485660782c444808840c034407612a0300d07081000030107000b0300d07401004200081c241120002c450186640b96130038460006043c000800200601080900d8494040740e604040441b0040105052481c0214105da1103608c495540040c00152060b050762404450001c0300755a03207643c0c2c0072120500c000c81e00b040c590f4a00303e040c042c0c62010088151810809000518402c107200e01040000c03009580c2c4411440c450301444100402611804081001010000a41c1410516103500c0404a440e08000040c03842084515a1100000c1d0140119040c180282c0c0c10080d68040000c142c1c041c9000e4030030074044c43e0201d500c1040900d003000c01c241d1125500600403500c080c0d00507107825442c0140c005806080d1000398010441c1c0e08580c0c04101500000c100c2420704502d801c0c840b00d0442d0711010040006020528034240c5030155848050449892540c080c00f960 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 245709703 1250 245708453 245708459
    0xb010b16060204150806041406012006130611040609030305030c040302060a020a060b19050603071e020d020706030504021c080f070f0519050a080903010615080910020f0a08150307 79
    0x200509501c1c0c0312100051704460100d08036052910441900075600e6038100745da540c4000042d180b0781181c80d002c0ca05240c022000c44558002480618041c511001d1412020403090038050240d468000d80e006a158040000304806031f0031010b400c0850791b00d800d0003078982d5140032003d0085e00560b07001130740100e0002103102c1c0566002c1089030005200e8941001744191031020320416a00d08412482400243e0030144047e01c0c044001e56406501c42c90031040190a110038400001c0f145502e0002507131102c0000c115054040c07240704060302d2503190400807454180c0008101d10b0907044000540034400c613090081c000084101c440a401c80c18500d84c0c0c41034035143c052803411807a44181c0310742c007072100d0924140e00c1a4440000c15a000001401c0050103505e5800381a4032407100941e0565989030002112030000180880e222101c0d1280d404c80e1500c0e681650410315944541c1c030300b042c410460003a88442c2c020588140e0412868018080d50310200d5030040008104032070740e4140f040c0c540c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 245710953 1250 245709703 245709719
    0x30b07080a05090c0d11030309040c090603050106050901121d06070905030118030e01080a0b0306011d1018021c0f091a061e01120504080a1404030b010b16060204 71
    0x1d0003800540410000c559401d14503540340c000d44104130b644207102e0590700b008285152003c07510740800078162031070817600e00000f80072145400100d002041c103d180411a00ea0140f0031640102002e0074000e2404a1180c0028001d0002c40c0103c1589951050302d0525451342c0004456070140310341c112000c03802c041d40082e080c450700d4030802d88690b0030300c05a1441012410800e060081d4036403248030200020000540312100010018200c56685110120b1550b170b0400181d4000e1003a8079040241e45010341d00c4400b4058014540142c140b15030f1000c0140d00a0851080c031000030700c400068036503100008011b40d688441880c10885400c00f61420000c81055202d182c002e48070301c45403058108541c074850780c890021503503181d101052000c041c2840706482c02c4502140700503d032482403c1041e0380d0b150100c0743d00342c03400d842820303001c00c1c1c600155801220140d010b500b18001c40d810305145a80b1907482c1501400790516035003010540110044101030306001c2c00e51310010941d02d8a8551480e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 245712203 1250 245710953 245710967
    0x1050d0e060c1b0f030403081e040b090a06020d090302061c020c010c02011407090e1003140f0d020c060315030a020607150f020715110c0102040e090c060301061205040201020304030b07 81
    0x100900030b040702003800481050000e490382800044002850603c1c7c55071b03c541840350484800000447d204441c0c00d1340d1a850000140040d1502c0180c0c82d4440080c2c0061141142e03503500400c0540d400300b010001140c0c2c02c808504110703503044568903035455000c034000103040d00b114407842ca5a400031034404c04600e4190011b44c0b03054001e5000b00700340030540102c3d02e40314000365036410114220750b000348030b42c07000c00c00583d5105070500045200305541e43e841000c80058804200071641100b00324140380b030b0090101860303a8a05100400000c420729000075024800030380300400158441c40710040c9510309011603030311941c00500e1a511040300d410180031411405140c5442c481c586a00d000c00b4a40134800d85200c00e030030150f0b0201404103120200d000709807441d403a03114002c00780f0190400d80424001080500300440f0140d105040803c01203240c04400c1403d54420003040c0014004a644501440c100411410b00071902e61a40e00050b821441544c05c09491406c3d8102044915600110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 245713453 1250 245712203 245712217
    0x20910020717010b01050706090503070c060c020301110c030901200d0504030605060405040f02061804050c070204060923130f06020c060702010b0609130f090b040209180a0201050d0e060c 82
    0x50400742540b820701d2440c00c0301c2c11005920301040090209101055283d440401c13183d200d241100e14111264440710b4910030194829000101880c4007481142403c0c007846008850641c552030406146d402415282e0140705107081c100722124403c80d03811020284420710005441080d0360322260100c8004084c2e84c828002134500d5070911020422904007441418855030b00950902a420440d600304801c580c84102011545400d81c041100c00d90340c0c0307100700d60045844c648115601ca8180c410311056802c59071194100c5d0340303040c0c02c0403012000010900818004120070410307030364030060801104804d104010b41105950ba401004004a0b54002d07d444660a4115078480e542d03c50308900343c0c0c3c90002d800d0b0b0004420301c580811401d0940740303443c81410203500031070b000844012010844a00000070340e100488841448154140b1810703c2e50480000d405459260710020580d598440c130600d0001d0420000044a41401d45540d000042101c020420b5542d603040117001d20b0f4031504040c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 245714703 1250 245713453 245713469
    0x7050c0601120201090302040903031b030b010314010b04150c060e011a06090307150306081b0a05060f090904060e031206010e010f0e0d02030c130c080606040e0a09060209100207 78
    0x3030004540d4110094220314510b5059441800d0203080d5802e01026042c8164110145502d800d18041c0c1c0540504a40c04200d0050340c0c0050108681c40c001010382e005502644160780350b607001032154800c04000c403416101d01d0901503c1c80c40c1c05000031075802104100c00741c10b03039140007500c3d540702006400a07000e0f0340758901e0030250203261108104081c4100c1f00801c0c1d15911100003000204c0e02e00184000300486400c001036842c0e47d6041c864100036000000d40d01841b010201c070340362031410b070242d400900010f0362024181000181c070618184203a9502c1407040e03106038009401c003d030070341140503603030500015652264080c0d03500301988201981ea4074046242c850030a00e00d94403a400900c0860002d5460148503411041401100729901405030b070917002e90483c0d1007254a9020b484401382d00c5046001545e6810210020302100d4090851841881e003000204540061001c1c80ea8000700030308800103400c0d07054600744000b84120003c15400140141064071401d0300401c1540071940c0750 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 245715953 1250 245714703 245714713
    0x30706050903031c06080f060a060b070c0311030a0614040203010506030c010203041412011e0f091a070908070f05030115050306040b130506010b07110a060212091807050c 75
    0x400080e5941c0c081e0780040c80e00b543c42400180700c8000721501d03880b81081001c3e0b002a120341c4440d0030744d0409001710f00c8401698070580901602814600c01d0f04002e2106040e01d03800c14000f642c401035605094807002d1310b44203848850184079030f010300031820b00e560f10010821280d00c40c40c0104803601011501a031003940f070500051103d090116000340c0180381640a075140c5800c0060694134000141c0d503031500030009245600540f20300340b00e1004130481450362130380d49007462803040090740c1c1d8010204201c1818192030b8800920fa4031001c20000c40d00046072035403a03a410380d0440340890307641c0c80044244a00c40c40003880c034015058020a0300c5042e002071040d050502203a040c184144d110f1140c141c2d01600c0040c0100c2c0302c6414954110701660f282410101c042c0c0c40300c134a000000e03000603d0b4141d0006600c81080b21400396100724510a07100300c0029440c241010f500d500812080303204121000070b0000e4145c0c1c40152104c1c031840703010300c0c1e03261702c0c100300400418075040203050105900c00c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 245717203 1250 245715953 245715959
    0x521041208060d0c15020f0f070305190b0703020f090a090614060c03070314071a22030909050603010b0d060b09090729040801140907170a02060a02030909150307 71
    0x200364614203c0036004401305803400d10b40903014480c0002c04c20090114051440c8441c0f5012082c0588010040060700402d100344c21402e2242c14490707140175104110700740160f044000360b110030441c0c0e03100340c96040041c0c441c03040a0164040b4031071028016407094480740046034a0307100c1c1c4d1252042c0c0b40b080c0454801d514051043c45054456028550201c0c1d00c1400104c0000740700c0c500405100b01c0d1204030f541010002d545000d15410116900c0c405050a04100907407034503000320b402c100e441d0385549410001c4c0320b914094a03422142c010701d64403a1302c50000801c00c1d1001d401280074550080c00c219202c03115801c6c044000c045000c0c0061180b00301e0004900103020000c0c1d10f0003070703502c0a0fa03684600040c3c00c80200e10742c071540b1161010140c09200000b1580402e02c6103c40019600303501d81c1d01441d184440505121003500050151460b00d8610460901e002030120b001380c0d4180c07a6540d4a40c100d07403003a45140500750050f6844a01941001007241074103c00c00084402a01140c10440e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 245718453 1250 245717203 245717209
    0x30807030b0604090c090302060c0d0305060d030509040903021f1b0509090c18060a0e1f090b031b031906080604110d14030d14060916052104120806 65
    0x2500001e040d4022014801406150981d0b8424040080d040c140380300d00c940c0c2c5e42e0208410383c010900440b81500072101d80c003000742e0503010300d036404201216580c541c034000d0358019000340103241d55103004541c0c1d103d17007404040c020011403001052a11455028000e10201c000142400c60a101801c450754820080414001d409880c04107900401080083c3c0d2815242483d43d084039400c584805010000b00c80f9903100c88000303084c03c504507501d00351300700758103414824a88003881642d102c40460001260100d940a40c030401038902038015280e59407201403a5085003800192664803040000060040652a015450015170403481040c001030344d44400032034440301c1c00c07100684008035002ca0600a8a0080f0604000d5840356034005410484410351034510303000b8803041c241d04c540d990f404d41c1810144030f6102d0703807140089401811034034245680000f0410b480010105200c0041b40c12110407118a00c900c0e032480c1c45400c01d0b8070b649000c3c00c03d00c490100301183d0f60045803c1001080a5007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 245719703 1250 245718453 245718461
    0x50c130f05030d0f180f0e13170d1506021501060c03350c03150405040c030f02060717030118050f0c3103060e0f120702220903080703 59
    0x65002030140001c0401400b041d03d0304240104010100135000a02405c42c0700ca100c6044045e19200034140c5001e4109010300d00e8560002d0444140100e4a1952000140070211120756003415080b00680300c0b40c10b41c80c0e12002c2c0c0304c02c4d024502c900594070300119031030343d000600119120b8078141003901c0d03907610541a03503202c0e00781030090005030900160126101c0c0d004120001d000070076912840f010107524084112003c140c0d41503030300030f800000380541d603105010300c525442000c843c03c00507400d0544e05c100a0940904c070050030900211189402e65035040c1c00e40f00d1550704031307250866443c5055081041d60f031090080381940d01a00c180c1e07601110341481346611070720801800c00310355202c069513480740750014610386122807124a0720210440d000b00049140449081803408d60314207600d0308100350b50091030382082503844030038003412070100000e250700b0700d0011a05040e40c409481c004664000c058400000c1c00c140300100041d09040d0360340c00088401d001c1d41c0d8140d400d44954504600b40e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 245720953 1250 245719703 245719709
    0xc090315070507061a09040506090d051305130209130902032811030f100506180c030705090a0504090302030a030b090108030a1103221401050a090308030a0f050c130f 73
    0x64024401080014503540c89036003070001d109084d40c07104128a000414006d0308846c100c61681007030f02800201d01c01000a00305280081c01c000303091500c1c6441c0c40107100c45501c10079208801c659042250380503d6030403111855000340603190038005040010000d03007030001e41280284110300007203120f81044034000300d00d0384980c002d59441d03100c0c030f8645400d444c0345a80115418081da900304203c03c0c808102c2c032075107500710030701c0414103140180030000c1c8600001d00002011003200101b2040c41144000c40e5888100d03410610b17100c0301164007240401c0c0058100641140c5003a00c000107040d00080540001d440641c2c00744100c80404d0305100440e01d013031241050756441401940d2040b03000320310141c0c081701342c081140e0400422500b88415060945041080b0908421003842030030a01002012619021708040d45003a484c0207004103413070b92a20000d882c910001c004190b0a0149402490040b07580c0403040c802c50621010000c50390b40310490700260016182d81c000340030f0024000300f40032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 245722203 1250 245720953 245720957
    0xf030815060a0503040213050115080f070f0f050f04270905030a0c020f03011a01170f040f02030a150b13060803070305030702070f120b01050607020a03141002030c09031507 76
    0x28669890016103075500040c100301d92210184010b4005903116105080c000c200408220305c0d507248000000e40bc40c0e0014041c115415444020005503541100101c000c0780c0c61442c0ca1035004da00b424080300c0314003504107004c504003400500018403e022486200800301440c440403400c91082c0441803c40704071810003001604140064841c40c0d00500d20b960805002400fa044035002c0203002908481c1c031861002030f04509413814280700e5034440440d01108a148000403900d04040761201d04182e0014402840c8040c0c400032181107442c1440009d0030103502c030450074074210200200b840601030106800340500700c0c0101148040c89107000f802d0403905010080e601d4405162000c44481d07000034000c005501c11900005000c426100850000704164240d201c0d07003502901d014000c010040c4c2c4040d100d24818400da07000b41c2e0b1280350183c00c03240c2c005040320481d101c00031214180038400801c9850f4510100400001041540007028010743c21800d0364a5018404598600c8520030359001c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 245723453 1250 245722203 245722207
    0xa0c051206060d0e0a141509060f07141303060b010e06030a0e03071401050a1407020c01120f020406020a021c0b01090c0e0603150114031b030a0204090204030f03081506 74
    0x4140d0074280028280c80940343d0002c180024035107100c0d031034072200000442e00e428501c41c0070981e00005103c2c450703050744909060092401c20035101c6a4804003d840440e0f0301d9140004140c50902a8912000d11038404500a4440e00c00744140c1e4a07001c01c0b8407054940504001031403080d07601c03d0b07142890b1040024161400c68031004180c400500d400604d000f07031031202b001400045a1103c2480c840c08040360008103461809411b114103450345079a0b5001c18100c3c080600040b00c0e0007140925450030b0a203006040e8403810400c4074003910901d185074004610010340421003503800f00f00645814000c1e00d011011000384240b607929203a1159010300349094100c0148900aa10b030803944200401d0b1820010181c00710000541a41c415100340c9aa0303800100798801c0c950b00300301c04405600550408900b14917100e104071481105901c0d06202040c1c00000050b01041b0990545016201c007802c115251a164a05401901c4800790260041401f0a002507000b000b0300000100e0701d0b40140481b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 245724703 1250 245723453 245723461
    0x901290705030d0204030804030611070309030204020c15010f080609210a02010213090f0e06010b0a03090f05030f0a090b03090705060304020339010302090d170d020301030503030a0c0512 82
    0x125250815181264079000c1004008001035441c0064000b07035000b40005695603140d403502034211546400c3d680101282030143c000030a82044000046a40650f405640ca9040003445414100780d8090702d415031290a0011410707144900c910020388490f14100d505907200c085240303948010020b01c03400544d500706403491280390204090f21020b40e140c0009400e00c0c09200c01c0c800003210070b401180c605a03481c84410911300c160300400304e0482c251409810b280d410450082c04600c41c8801c148107043d280c808560420912240e0384281d030f6007003400c1c0d940b5450684000610b9912100f203000018040040103d490303e804800c803406a8103203401008018a081c05100307898100a1050707034035000e0040450b0603407845005280d43c40c001518016848100550a0039021050744001410103206000d08001919140200a1042c0cfc004903416203000040d92041c006200303440b01880c2041c00800000100180040614080e130049101409442c0740410203d5650003240310460f24440103101003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 245725953 1250 245724703 245724779
    0xd0203090a0515040e010b0a2a0201140409050405030702040b030601080a02100e1c0c06090605070b0a020405060c01050108010c08190b01021c0512180a0b060105190804020901 77
    0x1500048620441c04c0956034226001611426405000c4080e00060601c400c20750000071210f0300840e00150302c4a14101c88641d032400d12107500028103000780040183c91455844042d1030003042044020b120343e2900d841c0c80d0f6100d0700415800c80c05542020080700c00c0e440d0211382d56050ba81d240c401840e01c00c0c0150200100009188840070520940388060103140c0c40c1c07221156000c081e5440180301c81061464071055030000b55001400b008600d000c1132140642c403c0481e21f480f07800c420f07109501c0d01d48080400003803082e0740c01598003640c0050603240310103042d00705074101c0f0140380080040002e5044280c801c450212590340c0861007100740110813007686e80c07244200d40f2040c412201e140c400e016003840e4041072903c019000c5400400d804032455806681d040e80108034100e2842400121070741d842d541d0b500c0900c0204181c140c00009062640321b141912a044441c2101809090826002070000c05060702c00707900494840e07002041d00031603151252124900032540c00c0e66540b0080c0340b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 245727203 1250 245725953 245725969
    0x1e0114060402070203100b0414040f0b0703061a22030b010e160503040201120608030a1112090102070e0c13170d0201050f15120a060c0f090807091d0a0302010e0d0203090a05 76
    0x411940990350300d1210b825001e183c016270307204174400c10301020070f6007407818029245d4400070320b60820981400000c0c0024608020101c05000500c2c1205807180c1d45903c80d9803009802003001c040039445100c0000620112440c094120b0715420030803c000e85400d14002c1c804a02d500b01c103400700343c0410114006501c94003100e14115041c880001c0c49603210070340c1030704590008018100042c624020341c16603900900108041c0e446074240c13a4546505040040c0d150707002c2e03114851003030210038006440310000100315002c100302d07003180800140e22081041c1303015100304401d540611410020800440c014400d05014601c1400c540420381d40d4a401401580034441c4082d8010180720701e064403da004002d0129200c0c03141201190800190600900301c0e50030818100401003081001c001510f0041411029070340001808112081800007003076074a24505007d681e2403041401403418140c2c10341c022500001f2072800d440c210400c600c81283d590041e4144103130b01c0155076604100c145402c4003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 245728453 1250 245727203 245727221
    0x905010c080f0c072c090a03180b0f040f06022a1c0809040b031911011b06060602160506160f05071706070f0509121e011406040207020310 61
    0x2d1203141100030340b031640c1030124903071001d90604100c26510304001c0f2200e50f01251043c0c060600d001610b0326a02c0b080d0b407000500e10142c2813010310b034502301c0d00c0c00820780400080c1139002200f81d0340d14000b03030107400541e000e807003000c12100507070802145192005c03502c498603c07002804050402d00d80095041c0c0c001444035055480400e143c0c09225041d01d4070b2044a05500900e4125281d40f016800e00040d10440541c0038131a820840c84201007210f0205080401600800d5800d400b02031000181c40622141c903105c0048044003c03440308100140d001202a02c086030309a444000c2140c00c6000c0c0061140141035100750284000f001d1410f41450510805000d00110036103079245440e041d0030006280c0100080b44000c0e000003201040400040740c000c541e9140c80d4226a0340d0510081480c0503a41c801c901c115212821b500c40c81a04221f00c9000200c0b008030414514407400d1424020400200414000700001000618900d400e10a541003240c02078003400b07540b409021000700903d034182e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 245729703 1250 245728453 245728477
    0x9060809031c020915090f010804021003180215070c0603020301121502090d150612020907030c0e150a1b03050703211e050906010f05010c0302120a0306150905010c08 73
    0x110a005882e9103c0c1d52002d011764902e545c031940c810200c01804250007500340c050b03040c050f40606120061700c60420103020585c0b207180c0001e159240d50b0b070904440c041913038003070760107200d1804001450381401d00501c00e4500c10045405056502c1d1419010b9000c01d110300030503d10501c5002001c140f1025a030552101c02d4a001480e0418080015005140c41001a40c4c41140f03d107100c80340e250540b242d10083c19060003801075800c1c0d982c2c001405030308010482e104242c0c80e01074603988a03001c0c000c0390f00c003020000c20918044104003001c141076007044107042c0c0016444442603203003441825540740ca50780c15544e80c610b010310070345050300c24440070180d40f45030725403049400502e41d02074855000b51120b80e000c450118003042110409590700a0845d03002034010400411200c45420792102c1111401e003424850503502d8103082e800c101040002d106401e20010354441804d506034091001d0f5000160410030801c1900c404488000550043c1c2e8045000120701c0004115003402500b41c0726002c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 245730953 1250 245729703 245729707
    0x106021903050c0604050c090f0105130f0f0f0b1c020a030b070903140d0f0e030a02040b01030b1e0a061d13020714150a14180109050f03070309060809031c02 69
    0x491a0f2130140c0132038003658180c20020030f07000d40345409134000f6042000d000c403c40203541000002041148007400400c04035a41d10b803d44e1050400303801c03020341915824820840c2101c1100c2c1040508880310a81d0b10450600308401c1c8096400840b03c80755980292041c1103850442d0f85144c401880600608140110010000b000800421225054840020107014400040100508070762528002241031003814400011035840005250b000207404840c0801c5039824003005800a250115206400800602508000c00c82c545002a11900103507015048a81c0d81c175403c40d10f00104404403a40c03a81c100703d0511641c58486a0220340705840350005180c14000c0c0d6601d00704410080c200d0070141c100303041601c0c402819203010780c0c0c0021500c0042c007440220451100c1030f40c80040101855040036805940184802d610022850303074803a0491740c5818000c40d50b655260040c10381100011a00e40020868601c00c03a0f070b035802100503038015420b0800030125500701d40707103210541c0c07100c0c0d40c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 245732203 1250 245730953 245730967
    0x80d0c0207080313030c052b08090a091a0105030609040620030a05070206070e01021005040c0905010b12060604050a050f04110d0e190c0b070c08010c031a0306010602190305 76
    0xa0000b405441440054200600e10f10314042d440350140342d002910030325504641c800e0b2980c0e25114580d40003507040c0050f94464903880c290342c840c090164070642003c805940450000119848840841081d10376014003041c1a001116544400c946194201a070500802d00140b1036400040031039500e10b0103d525001c09508a41d8550000ca03248894242c50758140700c29181c051055627082407442c6400e00c6076040c0500040d43d203921001100c6200e507541c0c0e00080074401d6200c400f80c0685441c1d0018005965180004d0030503820034040441900c04040100d002c034505001243c08030795000c0c0c110703c0f209281c00300300160042243d90b00741d04243ca44100e0035900410740007c0c01d613200303041d01c0054207840b00424240b0303085800a10211214204c1c1c0d4280104441e0700b200130880d01c5203864503940c0c980380d1411001c05802e40d48210a59800c02048400a80d010342086110281405818284040c50010555951000c2c440c280140c0c01190044030007007a00e2204441c642e000f804c04501d0200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 245733453 1250 245732203 245732219
    0x816060902031902040b0d0b22050703050c1504030b270124080a05060a0507091d04031704030c12110609160e01061e030e0316021309080d0c0207 64
    0x261102c820700c0d07042c0700c2d800030703c045107071522414001044c15101d2a120400a507202e81d08040054030a5a0f02c10603841c2080780c0c400000e405004196102c8141e8940c55600e1910070768401d800750881e0b218503d02603c000705038840030250b504481d00400c0c60680c41d1a444890111640e45009460300070809690500016000b400381c0c0b4282e0940680041c200d048108051703091200c0f5400c509055001194140c0100d680050781540002040b0b4000650f40c03266001500d1708105039000c9664910240344a1801c030801c2052944910f00a8841190111010005c0c4d490180100c2c1d009020614102d4408041601c4081481e84e0b80c80d5402c08440034000c04951a2030000d003215032207001c4d40b00030351000541e0026814840104550642c042c219410300d60041d1120104152441c03060390881751200a061081c1c010807031188403c3c069076680c40820b217641c4000301c00035a05038012185215500684581442992916600f0400c0c2604111500884a001d0f0000345000c1e411489030000100c0d09003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 245734703 1250 245733453 245733463
    0x130b0d0506060906041104050f010905030f010c021903020a17130e01031e05060708130c061e08010501050a0302090a0302062701080f04140f0d05090411030103081606090203 76
    0x6030040d030040080d0300e400410007443d1200102905c0c0683c2c140b45050490002c80c000b41c4003980c030103da1568103c81c00100486008113070351700c018cd040c450340c5490f11211030103610007200d0700040d9095400c01d44c84160a8210400c1e003220007001a400840750502082d403a01001c1404003102103203526080544400c840f1403220782c0c004c481c8650044004004024161001480410f4020708040c580480c80e204c540d129036004001209204c070700d600054107a02e0401d00715001c940d1100e00a4200c54585000400c000c0110024098880100d01444240343c02605000d04950050b5541031038280200c4044001c1e401040c1030a41001c1d1202000c0300680c0e038100540b000e50910821604109401d0030210f03a80c501d18034840341400240410320001c20750400070103a12030380160720034100c030040f032a090303142c02d80300002451036004190114000540c030000070403440320103c0701403050804a036055150741c8030a100044c2042c20030040301c400784427140c1e0f100340c07114011030380090f00c0681600468101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 245735953 1250 245734703 245734729
    0x5030606010525021306080714060306060c0a0605040f0506060405090706030908121e010b0915180301060608010810060f03020111120304080306100206131e021503010609150509130b 80
    0xa1615040c1c00c3c0407d200c2000310000908031054a02c021281550102c0c2541c40064050b41c0141e1001858107040300b002c0100e0560664401c0e8204007c0c0381900740002120000c150031500d6002e0900407582500e41030242c5c0d03010b0221500a04415864000264000c085060b4202c9400c0c078180301c00003d10212101c964403c20034240c02c07a0700b40d021604c1400c00c140301604040392a4006012500a0351a001221003e1443d211b0041c1d55a000742041e00d0701140003010aa68551b00f8040d0107e002c0383c0c800c0b282c6040340c100c0d82c100c5041000c080310113016150301d4001c444030103104907010000741d8072413907407590011000e07030940d016081d07044000d0040358003c170b40582e00d1a0001040c00001d02707112000240aa0f41440a0709290414800d41e842038110300d80c02500300d000d04020403005180c03031a00888103075401409040c8400c1c2e581c0061005410910031200804c0c100c138400240d540003601c1001c0001880da4900d4641000d060400c101daa00c400c2400002a594501c40a4141c440c001d5070000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 245737203 1250 245735953 245735989
    0x304140402032e0b180a0b040305031204020409080d0903180e06060904110301060e1c082233090620070f090f0c0306050f0d0203010b03030f030702070503060601052502 74
    0x411240c5c0d0184400c00c0d00c0381d8428140c0c00340c10402000414004001c0e17034004003030381c0c0c0d0601c003989482c0000f41c0a48461100034108000c00910484076144540c007003c29284a074989100440c01038040c000d07255030314800c80129911180011329a45401c80003021111401000017070b807448422010b41058000340c000398080750352180014210b1410110000259080000480040070595190803044c0101c0545a01d4000e12515200c2427600c688400406040d0760b00108000d507956098012443d80950440041e03005000080b0945a00c03820340c00061301c18a459000d4400d11b00c021405607840c001d45070020a0042840114540e446260080010440500d0120780710410a20039030440d10900d55030418580760030001c0000303440d45500d00200120807a52403030105041d002290140880c200711552501001500c0641200e4120145002c0c030000e81c22242c4541d2100181030340c8032401d07201d02c0c5c049181480004030310308092180c610310f4040341111302001c0316554081242c03140d01d505407084c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 245738453 1250 245737203 245737237
    0x30c1d091816080f0a17030901090203012c03040806130c030609080703030525120902040525030204080c0f0319060c0e1c0605091204080304140402032e0b 68
    0x201e0f00b20104400d18040c10008081c0100741001d95840144c100c106581141e2190040005070045100f940401ca019401074000d1068807651000d031092106009600554078842d02c1012546050000c1541c040e0b40c0b02d8401402e05443d00d030490758a00118030383c101c41e080307501000440041d515022300000c00344907822254030348480d0700d00542030b100c00030201149480a5099149041d41002c0f40200841f014100901c0000d86210b0380d81c0605410030003c1d401500305001e000700245c0d0410601141d40b07001103c005048131241b002c40c103a120303605c2903405960041512140a02c2c055030b81c02030401004084407211841c238030039502282041c000584809a1390f03011202040e800010341c5d605114101e8903086c02c0d031001e0100306110340c107078100a0011540c40d4002408040b0401404011841e0160216221650743c070545030340f50b0160140c2c4501c10740e40702d44902a42003900a480c043d1869800b4031030051001003c202221500e248006400600080c0004907040d00000809014001c048401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 245739703 1250 245738453 245738459
    0x120408070213022706070f02100201060905090c03070b0705060a02090d0203010e0d0e030d02070e071107270c050304120909090809030f1f0b0a091407030c1d091816 72
    0xc001314200c00c0f02401a0002c21151001036906c64003a540c0d903030304450040301e046070160704a0040c9229080f81141c03034a0441405070248001545c440c20600840c00c0300c07450368403a00045004d018907000100540d02120218808000d89d0300905600c00000e0b00201014026800103429903d04c480480c56542040800c4039800f40e1211010442c6501640117094803010400c0003075598160703204d828020721880e804510300358418001c5410640e00c3c4000c4800c2a5100ca100d041c000e03807a030302441d0619a03046400342042c503090040201402054a40e10300b99512602e03908214a110795642c0d04202c401103001ca1700e4003040c030030780755224041da01300e548650742d9034181881d01e0503040f02e442d402d40c00180c6050445082810441e10401c1c030501c0418580f40c001c02150044640390001c2031018144540000050b0f045400d0078070a9031030360360038802049022802e80e181000402081c640c040a8900710000b070074034090098002d07030349803004101500d0400107107044c0741002e03510f05c81d4020711078010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 245740953 1250 245739703 245739757
    0x60804020901090b06070308040f020d030809070f0e0610020a050106120203071a09101e0804060c1d04090314071415190509150f0a1112040807021302 66
    0x50707030142001200402000704042c00150182c0600800101000b42440c001030030070441040100e566a8042c0090030360070560300e8040d04020013120400c0591040703140005443c0c2d51200404112103400b511500261207250610420404c180c9845040d4031515000782c00042003485198000d00740042904045d007114410541401c2235070740080700c0040d0085c611101d0100e04000c0b52925041183c9540308034903014400c0d1103600c90807030349141c152000304440094a4224240e5072059109007000c10481c074800c0c0041c1c5003103403a14900f01e80b003858500c0500701403c20354016400c250103410401e94051848158130302030340c07100c0d50442c0c4031000038454585080381000280024400010b8a5225150854041511085085014100d191100e0104015200034803900141c03419a20b8000328034a08040c8032840d507001a21160040c40c50407442000c0107042c0802d9584c2d8038480c00a125064980da100d00d1940e421094050b81e2003007140c5034440801540c4c3c402410001d86080b0b20400c0f10848001d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 245742203 1250 245740953 245740969
    0xc07090b0114070210051b07090b1f08010303110c0d050d0807020312040602070f120f0f1b171612091403060f0a0e0304060305011e0b030f15060406080402 68
    0x35151140a0920603c001642c0e2480050100b05491400741c1d2a0b0f1400e0035641d0200c400c1d80d40a22090060707620200c0c0c4d04005400c44400c05000381c5048060701228070a900c10681e480c1303c041c001a50324801400000d10524403501c0c6140b1134022a0303807060407840001c5c0e407201c440e00100d4990744200c0320030180681007803017240c0c4018540091410240c04010390285403500401c01400c03140d00040310302c1000021159228010741280c1c126000702c1b0b00c0c1d20060070055001110030042410340c11012009480340ca41c0100d8240d020343d143d11a0748090b550304904883d044400c0c0385c0f8060510062848441c1130346100c943c60f00a01c1428210700350403034050090b22854220040702c3d0005102001075840000d050780e040103044042501594803c4c0c02c1000511a4803400c00365404002400506954942c12013816034810941008600386c110b4100d60a961051181d106201001c0c000580940d14001500741c2c895020000a040d103a210000038420703903c160000340c0480c01f910140029405c010312 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 245743453 1250 245742203 245742227
    0x20d030c26061e01080a090302120d020310053f030a0c06050c040f0b09010207030c170f03090a1502070803040608010608060f031c090e070c0b0a05010f1701020c07090b01 75
    0x7480002d0070f41d00000e1280c50018240e014094940003860100361080201c034094040755103940342c40d011080c031030f00c001c0c0d4400e03600c81840d00782000e00462103240041d502c2c04030400010700740758085444004a210014200d03440304d08500041e040c60645407080c80145820388482c0d45503e0000b42c589000e20840310090306c0d07002d04c3c100904c0309006860305480c12105503481551604e0b100c041741c100403450083c560700001e00002c0d08840009a03141942507110100d45d005040c2d41d05201c004101981d02e0090b082c1d03c5c0c0c1d0010f0034200800200f510380303401007610b504501c180c41103640c666040324076550196012000040a0000403c907032907018035415041b04044801c03120030030070000000c0e610320141c40c0800080e0b20070010044418002c0020034010490b031012205549404400507180341510304d0f05840c00344240380050740c622020320540307069500d03004c4484c010300d041602d0b80801c2441c01104000340c3d94200410314680008000c01e00041420303003004288135044100050905007008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 245744703 1250 245743453 245743489
    0x3030603060a050f0105210a0c0906051c021c05060709090c020303100e101d040308060109030c090c1718120c0303010e0702150f0a060f030201020d030c2606 69
    0x1d400c4c410600407155807581154000c071000880420b0511504103003101214050a892154980007004c11295034005400c60303410400c2001015a81d1052000041081010b00341086a0071200e10061030300076508140d4800800005003006501c0d601c175807500200356209030110b91110020032000c110b07800b80c1194542c01e0b1001d9421414541c143d0300311a130703a50040003400844c040000d07000100d041c107131800404035100c030120a41e003107031212607001d44240e806a00092182c40040c0345540030300884000c40341e00c18507291155141450103001001c800c0c80d0002017102e141c0392010850030040445003c2c071203e8604650b8480358007a254541010b00d00b44100c04141071180c3c000c1c5c1c007004415241101c98458541e8150394800d0070481c102044800c400b6030b82c8403c04180700024045003400d52085070650410805c10b916a100c40c0000180c921009005074440c03191080b4861194102408207012800c040000b00b21024080d8140082d0760f001c407848400d0b80040005c0b43c94140c2c10041100404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 245745953 1250 245744703 245744711
    0x7051e0703171b121816090e100509010b240703230406050d050c0f070f2f0405060409121b08030a09060e0106051e060d020c03030603060a 61
    0x280da0161401100001c11511401140b000500303400140141c204001882e44180d81d0f1264100290110483c2c180e50111022941e50071000d007081d4000b0340550140586c107070800344d1074a00307554000030301120701072001c0a0103150703e03020881c019401114012200300002040d805185400c0c000c201800454400c0d20005000c444402c1d40b460404440a036500b610384001032101c009008010a40700310020824040001800100744c0d0b880806428000740c5050280565200c91034801040c0c010313082c5c11061414200320b541c0014845010403d44580708000e52440843c0d541d040d42c0d40007400c804c10103c203051644c60041d142c0b40a108481d40030004980401c802801521a4280c4901250007101400b184162500c1d0809444010426840d13000400360352328607000000c00301503d10640211400d900304031001b50420710600412099505c041d25000303008142c03c103480c035400011600990884000c0050303650415550000748800340d040401941e90781440e5040c10700d07200c0300030b055150003450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 245747203 1250 245745953 245745967
    0x120180a060e12010b150403120903031d210102130902040e070309140609150106031b05090418060b0117010b04031704051e010f030b01140703020c030607051e 70
    0x981003005842c040c1c50140b0040504071501e401000000c99403503100d03000c00c10b041419420170005009980c414407004c03144003403008058038006518000100031541c0924101250381c02c044408a82e078000800004800304810449114503400a109034a00c0e500007400b08200350f01c88403c48000c0400703000851800b4a440380c01c000e4810003428020416881e44e8200003448800c0342502c2500791800c003645c0d01c60070720350302d0961b41ea6540d2030700c90950310b074003000061a14009d11680c004c90040341c1040d09481407585003107135143d11003e54144c6c441d6a4252012503550850b45451160340b040740c0000f584e100007800500060300070010300c40a450048018804241d9075816542140da02c40750548440c240082c3d540c1140c01250081a044080c2070701285410b41c20307030354000d120442a01d40d05880c2d1660342088003590059240d407804100c0c812040c0503003803158801402220301038415156601d0007807000909250099620f40001080454881c4281142c10480c2c070a55440d075900900d0501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 245748453 1250 245747203 245747207
    0x80a06080a0201092903010e010302010f0c020f0405040305041a0424050a120908070506070f090510080405010e060708100905010509040f0c080105010605072f120120180a06 76
    0x150190000081441180c4002100008181e285d036504109010346c89607104c0902c1c0180c40070901c0309900082060781d545005d81e0140c1e0310300c02690780150503e101c0c0a01c48007840043c0002400c11010018200000180340c034080ba40e0405000d00c41403516900e61400c00541a82c5165143c8407009003070003001800c035140c0000450b0314940f400d04014091121103040724005100b01c020150000100040c103404204004c02c0c100d1080b070081d21103d92210f04220200c0341d00505000e511341140350f03644660f480301e01402c403c030f0307009102c0c80000c01c04c120b100d50500d050a800303131a01404500d01005001c14000c1a040d41d001825403000108141c1d0f242c0300004a0184001d880500b0f2102c1034111076082c80640308101c0050101c6400030300803565582c2000b08030390300c07900302680c0c101c01c00824540c024020100500011140c00c6405404e21007000801c80007810000740d0000035035907500c4003d40c210038001c0004180e00d42a0306240c9445a800103006101d080c10101440341c0c2840d1428040c0d42d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 245749703 1250 245748453 245748467
    0xe0609120703080a090203030a0e0405100b09150d0f09140609061b07050a030504052419090801060605040315050702101109040f050a0c08010602030304020108060a0312080a06080a0201 81
    0xc2d0145812000354642d8240c0c03034000c00c0e900c0d070003035014080000c42d01c81e83c60300000191290041508c0c104101d5481c50b8111030b800240340503812520108002445107884c05841403107084070b01e220124a4060341c00001c1081302c03908110407c00d103032100010403d001d19000d0f019103074150140908441d203020240c241d203d150040010301c6c040c40c1107012602141041c826248465446030456855011604000c0d00c0c58000b44030303d80c45840e03001c0703003140741e070006144070712200c00400107941c200a000b0640a04480032038050208100d05400005900e01003401808000e114070b40b1820358490650a00d0300841440c42c0c1191541401d00c0c00f0b00c1300343c2da400074408414003607401c80021101c12010740f44150b07110340c2021560003800c00240c114084802d07400703180601c010090030040500c0451080ea180c0e6800d11880002d0b80050000802650040f401540d0004005014044441c0c0300c1c0d441c0e42c2c081ca6180b40010010380c0150800c01c41008078030038840a401c1610040210101541c0002c06d11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 245750953 1250 245749703 245749717
    0x20f0d0b0f0705190207090e030c0327180a0f0203091b0402041502010e0d080105180405010216060207120905060d0e1603080a170105010804080c0a0212010e060912 72
    0x651a00c00002d10b48620a03400e481d03006400c0502038400c050941802507403481c0758090074203100d02d02070120100c2d5000004841a80244002450031300b03840d0340301aa8400030b0700d24000e03419000d1400d06a0341e076907040791076130701c0c0d00c56075480b01c04509107005c0580c200c0d5815002c2900e15803040060115040000403031815407000280c9001e40c490302580406d0107405a540000d4400c049030040300c1c6210307019003005140200800450343c080000c40380c12a007802084c8290f580107030902006101440007030714007903489402240007502c1d00203034200d000c0c1401303c9503500b51442580401e0035010441107040d030f100440614607018080502700b40c009140c522903001e18401c2c003592000c941c0c103280018054410301c07a00c4030003000301065aa04092005034840c13104000010020461856020401d80b401030507500180e50703c0b185581d4950300d1602e103030300c4200c10005902c650083d507001682c40440f200309824452001181454042085a1030440003404042d25034000049165290414500380e90300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 245752203 1250 245750953 245750971
    0x5061f120c0e091810050a0e060c130b0a030204031a2d0a090c0e0702061e0c090105070303020c0d090f08010506031c0903050f0616050901090302190905040b04020f0d0b 74
    0xc01300500c08010f00d8107092059000e05141018104407e140c040d83c4000c0b84a107002c170544030240d4035502007280780c2c82030031410b841041d1404414807030740005001828000025003001850300340c40c0d4580d041c11420003500000d02c469207404224031a6071305094401c1c4c2894800c2606110390060360803008a0070000c3c603c04005030b0b606085c4007445481180d11001b001c48050440460502c00f01c001d40760303c0d048540c01c025001100194003d21381c040307981445400801c107000d0615046900440d82030b40018415020507800707010101c44a039050204940b890a991500342e00149000c0d08501c9961155204d0b102a034074000c10001e181e100414540000151281050191214a070381600c4494198201401904c203a41c2021240c00001607543e0040300848845900c140d0104800c40d40d61103883c014600040f88180104018101915902e0903003c22158040e842038032002e00400b15401200c090302c01d40040000c2c0000e5007808042194200f0f02030381c0000303145025455610381c000001e00b01c401c1e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 245753453 1250 245752203 245752231
    0x204150215150f120d080609131b1809050d031109040902041512031d0f0111120c0a0b0108060c070803060303040b071b06050a0c030305061f120c0e09 66
    0x207440d9200c07220b02c484650018420408482141c03034050785c82c01c850a508011502c08804210a80f80c28001e0f0b910034003c4202c13151014519555220401000d0403201580280505002c28140d81261103280d40780c41c181d50028444d1024200030f480c1811643c104402d140c54107002c3c910142d0b20004482e06110290f0300401e900740140301090003400c0e014800101d07008041030106240c180c40c11001c4200d8042e0f07490902e400c0d0a82ca03210300f4024400849540490100381c4003c95500540054419029003010780d81040140c0111110503406010741201c20703003101020b18104503080184601520f0300e080101050710300304010010512614102a110503008000550140e41c208100c9010303140c2c04400c242c0700c2c6c9541c0703480c03c400c28440c5240302c84c2140e80704000c511b56201c3d100b9200d070b420079696907108259030354030103034024030001e07051903003089100c0200e204101c20381d0787c0c1c000708180c1c42d500d809500c91200c6090048034683e134511001c0103040400100079903a2a10f007a6040200104480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 245754703 1250 245753453 245753491
    0x50c04090b0f0603011e0905070824040c02161410050f0f040306090b060111030307030c030b090906040b010e070e01030507030b121b010503040803010618080601090204150215 77
    0x101540d0400e081d0030783c07241000002269034140c45094101203200d200d04820100e450b4800101903c4085480c00005000c5800048203410b0075a10304250307140040c00200c075100b0365030104040d07591074502c190240c1d1060944103505245c0340750600080c0030000040114481090002d8207508540840c0c804001d00894400341a40b0f4080c120780aaa0302054150b45d03c954038a468009440b02e9071041c4d5040d4400b20014040b540074900701840303030201d20051459a0768a0905400030301a1300413003402c0584d207600d044a0340d114000390b9800303484140000e0480b464240703012900040141c11808400c40c04400b4020b5a58009181c0310303028000f400c000c600341d50380a90440003010318194903030307100e04032a0ba0220f6580000c180c3c0c2d1aa840c0304802020603080000054844d407000b510024403c0e00100b00410100d80302d4158441040e030096400c6854540c1d40590500d042800e81080c039800d68002410000c13281c2c2d050142d02e14502900103002403000003415005504002080f41c240e1203035a042013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 245755953 1250 245754703 245754709
    0x3120c0f040906060309030f030b10082809060b0a0803070b07110604030905010905010e09010308030403030216080d0c0f17070e03070e010518060307030f0f020d0f15050c04090b 78
    0x560094602d44008000d0316a441c2c0d4010003500e0100426400325503048440300990b4840c0c061403030100406044c06a00c4074503280c0031540920300601c8405110a841c042000ba28140d0610310041c0342da40c01c0110b585802c1d410210308480a00810354410600c074817080103000c401005481f40180c100b000e0303542c1e0b84d40e80300c001c0e1000c2d102c03080400803174080c41d400c000070560040031140c15110283d03522800c05449030015100c0315400141d642d805000b00004200083d507110055901a01c280f8015042540e0080103181c0c10211240440c0c80a4002ca40c008805c143c61003003103d80030f8545014669109d03100c00240082c1c441620445501000e03800241805018030781e5010748031405000c0300c0c00c40c0c0e500d800c070411080080c040c9a10840c800155400308040c030000c1e0074010030000300500050ba185940d112003505011804030303022842d4050460160343c80c044a8500c0a0064010344c80302c42481c6000059502440c1c403403140e0b1807901040c131120310882000d03642580d90019000610704422000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 245757203 1250 245755953 245755957
    0xd0305040c261005010b04090207110907120b01030b10080901061e090b030303010311090a1e0b120607091715070f02101b080c0705010c020714010203120c0f 69
    0x160029a0a042c21200d00c11180345044141032000303080c0ea07807926070041c46100750343c400c4c40341000e80101070205000ba4201980180ba5aa100d5600700f400300742100701090900004980c004007003510081e103451810f038540141c000103c004d203000c01c4420703020b4002a80964488494804000b54040082d1101a00b540301c01c0251140e5502000c0c0c2c8591829042c0b01c0140c02c0c050312011500b000303545001c6050010940381a6a401102550001072403400d00000d0500182004800c944520072000c0a1456950300308444130070001c0422041d140c6001d02070504d80110b07108400ea80103200304550680d2100600c020f036014a002850b080000800c0c0c0d9140c030380c141d920716002031001805d0100303241d00813480d8030b4045565000d9400d03c1745000424002c482d9083c406500d40080040d103080c10341d2040e520f9583c484101841035040c402282c03182030844a4900080016910500c1c05001002107403450540000003417001b1460a201d06034586d01e41000600f214866203004140c4030340d85040641 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 245758453 1250 245757203 245757209
    0x60a180e01140601020712020315100e0903040f080d0e1c14030c1603151104090e0105100f03020f0d052815020a0e0907030f0926030105030d0305040c 66
    0x280b0038800200c4101c80c20030410364000b805840b9007000007429a04440320390b80070365002405030600d46006540d0359801e0b84020050100c0044842000c00e11591a9414a0149c51408000c41e2640d040c9400d4070744500c40e507045510f0962040804801113a4400354031010400c0c00c2d40c0071404001c140706145881c00030704200a040191100552f00c3d2400008081c1c0076210b40c90381180d0411940c4e80801c0303e00b4456000141c6454034095590703004401503001391800100414013076241c1665040c2400450714803403001c02003030351640240080407503131120402c00b07030a080d00424880740c03440d800074000000000c146406242ea45100c1400d000d410f1052110903005810329289280314041004040e58200c8811203043c6189900b24201d00308a10944a4403a100c0c2c80d2041d03c55007000c100903048800070201e204040e00e5680d2440c2e80005030145c00c2505104000080300c41031a000840b18640001c10103c80c0b0000c1800100b01a54000441d422102d916040008080c0c885041c00f1581c408290 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 245759703 1250 245758453 245758481
    0x30905070504140901050a0509060411031905061902030105010203120907050a0b0a1103120a1d1213050d0b01060c080c0102030c120f09060105010f091a09030d08060a18 74
    0xd0401600540103400c2544918540c130020045a40c50a130030030300300c0794180c40c1501a80d010600180c00600d0302c0c2240361120324014203c8410054500d0100b80154000d10b040741c2070380004060190708140e072910340903403040e80300056042d5810000000d40e0780c02908680c0c1080c212010114000781011f01c16040502405841e0000c0545c03030701c1c00303040f803940256181e40004800ba03400031a0b280c400b00559545800101000d00c4035216050040060f000c00e401c601d89841200701c203c03441d0035040210b0001542080602a00c0741d0340122215140481680114003604581452400140d900c4141074156002030600700760308680340c20700300b40f140900c4805c408958800010b010522001c40090541146542891604d6984460004a10210a03207002c82c0662050006025660086000004012043ca00005000d99400046881d41c0b0342d010700350116040041d40c00c40d241000e020031000b411a42c100303010541040c40100d0040070240c0b280030301c1e51040c1001d05c640c81c00d240d04000581c0c0000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 245760953 1250 245759703 245759711
    0xd0903030f0509030705100515060c03120411040c020303010b030718030c06080f0c07020a0b090d08031311010503100b072306010f1508010909062904200703030905070504 75
    0x94881e89a882c2c1c071505007031b94503200380081d500c01c4a0240c00703900c0c414504620079813401a070100030b00055404c10703081017000d070000780304014440c000c4140e600c2c826400340b25015210302c0f403507050000f243c0140a030309045400030001480030290680c100c07608080f42d403a0200d5800f94030300b00014000280d420003064207015400004001342c0c005d0744503000e1203d044c0141030310b483e6500440000d11486c41d00a4100c1000502042440458000303815406009007541d00200030650320701c0c1050740708481e4080240c20040f000b0b0309100d01e002d00600501801c0c20900d00c1e500b849a410302c0d0456103440781d21001d401c00290b0408100500c40b501203000b40a00e01803006848403001e003625140300b40070324070f8140704100000542e80c100190001c103a59503500c075400982d00740381d00d00000d460a0107064441c941c540c850243e0010380444502c0100075282907454210324076a00300416103500b0301d00010784511038801c0390181c00070441158005130781418006480032052030054208409584001d03800361074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 245762203 1250 245760953 245760961
    0x723070302073804140f01031503200402090a030605040f1211100b06090918030a050a080c070b1314011811030610170309090106030c081b0d0903030f05 67
    0x280420f110a4019240d10030180f01124910001d403a006921401a54408041942c0a5810212006050100107250200c3d4032500c0d080c60700c4a0600607401260320700300b4841011810005c0840c04d5401140448055140481c40c0c00019203002942c040501042c0d0f840c40070404101016102d054001d1780300290b0710a00c41882d03005800d54a8004910110f4003c0418481640c5001c2c4604881ca01000300040c1c10401050184110710b000104130140c041d113010403000d0009010005841c58120325610b10b5950b604d111001041000b015228041ca200300b44440b4000641d11641180e000d900c0c074039031085462060074070b2084c115018090307101039440c00c0d0640d8000002c64039485441800348150a03000b60302c007014190b0300e000c212032043c04114228028000e001200c4480c0315031241a0b012682040a4400085c0001800ba442100401c1d51554081901c80c1c00201d0250310410010b80210840072080380403507035200e01071419002541e10450281054040e500002a180056000300440c0c0342c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 245763453 1250 245762203 245762249
    0x25030213090f0b090606030a03050f0a030b0a03060b03100615030506010e18061801030c060c051002030703020703030e01090512130e0906072d0e0406090c0c0605072307030207 77
    0x801030703413800603900800300026501e00340014203800d000e85c59603c140c501005885501256041042e00508068a80300c1c3d007101580d40e02c0c1c404002c0d45c065000081d2024240007003600c2c003800c450075081d1907420000e0800404c0d483e00007080524043c0e0801103580e03654400101c2c0c40000c90f120080d8802d80c030051819895240c0e8080307078400c48094907000d408070207544200c1000002403000600c4610761880034081140300740b0314100c106110704112012480208820800e90f00219150310000341c6c0824000c2c18950305009914004902d50020015060345440e4144c60b0400070b4007070007202100080c40048000f000380b15030300078841c1e185102e0b110b00f04421040d8603000103950100c0010130b10f054070740c0c0b401181e600c00c1c003060500e4802800315044540341a10483d4990801c99400395850780001400515806410a00b500a50342d0b500401c04525044040b103001a000030100001000303c01310320f0800c5046408814410b0f40d010344c807000b403842d049141102c55007280e07622590703107460355070420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 245764703 1250 245763453 245763473
    0x30a060303030606020f0309210d020f070909050c0f0109180605030d0801050307031509080301060c060c110a02060306030c04021b0d03050c0a03020a12021305010225030213090f 78
    0x80c0c440e550500c0380c3eaa403098100e80c0c0c2c0c8924240c1e151580c00412070b02480740781c26a050368884021400344032100c011000d51a00b8030118115000140c0c10580c1a14060042403001a000d840084002c000c0501d85031101d40e070b1203002c410664080c4048403101f002980c0203c0c2c2d0a03000b1b244401c00055000c00d03660070f410107807242d441594003d10401590310041c6d03000d81102c5068580140003081340c2c40c510384800d21352801d05121440082d42d181e5440e00400d07811002907000e0300440d15110500c04403450070500300d800740304c019401c01130345403041c424100001c2075060078160102c4944d501d07501c465000900f08180348071030a40c0248009500980c4601d6044241c030040c06241c19030700f0b1503030303a148154103680d0300700d0f0448030001041000d011294025409001000c200d840e08c2c0440030444220501242d0005004056545104c0da04014560341044000f20304c04161080448a03030005244404e03601690000a2003040c0801c0003104035440ca6000907111600b000710003654a9180c03d010005d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 245765953 1250 245764703 245764709
    0x703020a14031501050603130f080301031406090d0509011808010c030903141804050403120e0c0406140307121b120209010e06091501030605030304081e0d020309100311030a06 77
    0x7a004684010328000081d03583c550407140f024000610359030b52500b12074040c2e89001170807264016040aa54086406d940203140614421105100c01c0c2c151170000c1498224010042c001d40d5003d604901000e551000503600c2c51502800c02c0008a07540149140d0944030316040f00580c0c0d0701e480c1d851214198103812914086000e42c960560705c486403202d44144d441109000301141d04a91594001f50034942d0100340c1c41802443c00c461411180702b800b10a403550455030000b1540300181d901098601885480024010881d098104880d0300000c292100407a01c141e020140303c05040c482807168074020740a00305d404894070b201182c0c8862a900316a0312004050740a04900f50000c0390f5440010001d6014440040001c0459598540054244407541c0c0d440c50406845100c00039141c0c8082000d03001420000c000350800030f244806024022815291444070f0360301c0384002c810480e40102c1150703803000042e41c5180941c1069401580649102042280e001000100700545000540c0c13211040e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 245767203 1250 245765953 245765959
    0xd020f0405042a050322060609051005010801140a150801061e05180a05030a0b0a0b090606030106030f060b03070302120123061308030705030a080618010b03090703020a14 75
    0x14281d520322003051241d0b00c5418003004514031015103498134012009582e1240071480707442c01c4c031b01c1618034a590081009030115201a280c0c0710500100c40c07507000e000e0348681c4c20100540c0c81854071000801c01074041c031a002d5600d80d606032425498442e80b007000040c10f900301040109650f40d81004081610901c2a4000103a100c030b0078100e800141c40036140912001c1e640d481c100300d404840040550104454503500074041c2e038000603203841c14040d591640340035041740c1d001ca18001c0c40c80723030030784801103425440ba005d60700c104801c2d80c0e1403c0680e810344103240b40015803001d821442d42c0080466030030100e960f21012040003003035641a001444c07a903494069031666030341d07a00e21962444580c0c1c4076110040254003141a01d07408d04001804d24408070486910800d40d407040080e08540c8011000e950b40e0f0000254004081e40110170130b500a08107440c1102803c04628160094100c11b0050007943d030400804220b00f440300304420f03006941c000b04620310041e505c024a884518a00d044140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 245768453 1250 245767203 245767211
    0x10061d010b0301030c061206091b0e0a030b010e04030302040e16031515030e01180305070c0803040e0708090c0907090807170a020d03020a0605010b13080607021509030d020f040504 79
    0x60920250810b4904883c0e208202d5902c8909008050740e03440b0785261020021542c0f08400659040380c1c0c010403c50304c1040003640106900c1d8540180259400d00c04c5a0090380090350030400580181c5800381111419003004030740703031542e1034101c0203849140d010559400059083c030400c4840a09016101200ea4800304841c03920081c00302d0700e9040030701c0b41c040003101540c0a9403103d402a04021000884c88000003820101d00110104c06a62804190002400868680b0411022011810180140800641c101031601d0b10396041c8000c001e10761713000c22080101060050204200d00d00240000034078011171440c001c000144503291511403030065109002c400542800280005880017000304090303c1d040d017203502808064048240c04400314490503030004003080d80c2d07215032400f8000e900c00a584e6401d5005282c0380f562640c0d000002c0d1a00716109010500f03400040042004800501d0041da942e101205a4114002c2d448496245230001075060600d003070140090040e03640c206c0e0204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 245769703 1250 245768453 245768459
    0xc0d111c080d06141009050f180a0b0312040f090906090203010507030f0518060408180d030f08070512060906041b0203070c06020f1f0204031223030c0702011110061d01 74
    0x21100c0600b0044a010070324019050103a408d2030031541450071070181419104220360783c030060300550103c0d011010030f0794500320100d20345001e2244001d020030424050f0304180c1010300840d840401485002d0340305c1d5a138a18a0704102e840c1c1c00584240d0740040080002d031505180250290048030418400a0700d010f001a0b000301d04c00d03111140c3c00781e5030130040015644036500ca281a600944d80024262170f07100d10537880350b80b544940919544250b0b5030000350400761102400b2018090318180502c0350600221100900700043c81d90b004200315112402a2280b01c0408d001384106885401400d05d119000c00c200381d0004014030750244a00d00b180141655518201d0300e5141d085032000d00c0ea00040090031603e4414155509001e800100051034183d60707590300c21080400010030408100040002c0c0c20b914200c0700101c054146580940b8510b1500720b000780e1480c4165000241803003406054402c045404100382e1004401110041000c26103400e80030b042101c070b00b049085080980e10000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 245770953 1250 245769703 245769709
    0x12030501090501120809031006030f29162102120108030306010507120e101106132105040909050a1214042706060305090c0d111c080d0614 61
    0x1412202e03e403d600c9200040c0d41c0d543c1d40b1700e40c000910540e151194031801c1402d0281d6103d424002c620030250041e940420b4504034528410f4440744144540c1d4000b008000c2c54070412000c0d51010718804c0007100c442076280151154034000951400380d0001200c1003409159940c000e141e0786034400490345460b070fa2580001d81d40d00c412602c0700e00043c0b00344211000582c0c40d40e0800701c00d48250600c80c2c1c10f54039240226100c009031182000004055a445109554041c005d003030b00041c01108105010b00c89807120280a003103007600040441440b00100482c501c12800c0d980036004240301489600e0450801c50350300d4415a04c182d401c142c03800c0381142034a0007032500b05100e04282d20107504003460500c0c08002c0c0140354851b0000602400c141d0540310602d0703c60580500844d4400003441c2c288403100a14102a209459004880b030401100100d524988190f4042c20111100d142102d0750314a040c4181000b0070009104110116040154031242c1d000030003036841e01030030100c0c1c2102c0ba10030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 245772203 1250 245770953 245770961
    0x6020d110316020402030402120a080723070501180503010e07030c06080708060f040f090303050a0c14031f081207030f0512150f030a06060e0708041709030a0206071203050109 77
    0xc5100200c2c8440070000044c20250059503201d070000f4001c03106040842440b074100b5002c1c1d0811580d02000080351010070400c851031004542207050102c40500d11209502d6880496006040c18007110340d0404103082c00034081c450140c0000340090103030900745c2c048a541c03034003240000c860140c008100410040d00c070740805403241c0c80c2a41c4841c1d080e150301c1c061281290000581c2074009854aa202e60480d4040c042c60401d588296400140c0d03241c0319102500311929a28400c5c204808400c003485511032103411ba030381064138030b80d18a001ca40d000c3c14002201000d6405591103020303941c0320340c2c610510348003d082072a000e51502400d900506100326214400e0244003101c01d9000804602c031901003040e2586101409020082620b03a10320000b89800c5601d01d0490302c1e80c0e00c0e05000e022034590718201a8011210307090400040c1040d64802c0440c1001002040d4014400f28081034543d07010005840358036000b034603a80c1d54420071304200071441050034109020a040c0800000d402100c3d02c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 245773453 1250 245772203 245772217
    0xd110714030f040918171b01200c1e07080c040605060403030e0f12010b01091d060108040c0b0a0e190e19020f040b280f260106020d1103 60
    0x200c40d240134107000c44000204003944c0d40c040f8034480c04182a001800b0100b107100304003440e20000d034030b50319402c172a404600e20001ca07800c1303164100b11400c0d2a060811070224041040c840c1d01c503440701a212800c07442e0003000740000c108401001c100d15081c1101042940c142c5007e42c1c00d0750340d03002000b020310040c2e684502c0b806030007800401040021a00c076841d080d0306004014800c0d003490410b10b0001700c07003003001c0d5071038402e0380d42d80c410b98586503800034601002044030240185801d802c640c8082d604410062507241400041e0300010204101ca64881d030142070071409070780d104e114640340101800d0004561900031840100e1000ba1680d82c0780403002180c542da489800e103951080310b03100c01f21ba131455050514079024400844442e84110103030000d412192030030741d00c0c2c0040e0195108201c4248c640041310091031503001e04441e40c400110180c41a041c14101c48519a0518004d000c411942804031062080000803d85581c0441c0045080c22256600140507440d40b0030140ca81c03080c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 245774703 1250 245773453 245773477
    0x902090f0402090711030909072105060d080703110a050c09090313030303110c19020109051806061621020f010c0e1908150613060803030a110d11071403 67
    0x100004440170b200f14441d815255000003501d09089860010401001e4152803400214402c84080841800b60710b6030310102406512041c07006041c00d401240d100012803501a2032100d0001d0308005050090807000c1d040c00c1c014040716410445420a142c0b1400e503680c3c00e520130726426004c90a908000019a0b001000c041e819407002451641e00750020f000c1c2d040b0281c1030042c180600d201a00007442040d09180300c407245e03040e1039003151000414002c001d401292068030049286090300d0440e08443e6840b143c00e58000b6540c0d040d04003810501007810360000e05e4500b0741c0e094400451212804130030109078680844110141c0c45500740c0c00c0c3d9014000d0400040c00080c902c540340c1c640000310011040c00c600000014580300d14415080040349000c800107020100e0600c502c1e23090a8080303401d90380c1a803d0030003c00d418125016140c2c4130242c01d41e08819104c0340700c044d052541c4001c5035890105244204000441c080a034000d81d0002070b0183c9101c88031082820401c2400300885503600601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 245775953 1250 245774703 245774719
    0x1020c090417040b040807151202070203011404080a0305010603021819030501020a0206100f0b031302041b0905031e0c010f05040806130203010c020f0d1409090a0902090f0402 77
    0x60000d000e8010002030081e1a00341da04010800254504001003002e000b001c0c5900341c0d1103050851191410840303521850200754050346071000c1946c00740038030080f56121040581c3c1e03103203a800024094103920020600c0d02e0a0801840204110b100040418900544050202d6230740c50f40700b5012401200d00ea000031034982c90144055142542c0030201070107403000c4c910101c03901ca40712b45003240c0003d0541c1002da40005c0510a0409410442c00020b104010b1030342001801d000200c601800301400c0300641152544009003159100e07002034000c0c214510381c036280080e1040c0001c000100510034540240a408815441c82d10b1034203101000ca1b14010080c0b0200b80c00400464202906400e0f20301000390600c408107401d10140589405250707149000341c0c2400c5140101421207052800010079584404403070392000c2ea010070380030410309245c02c0403110307a00400303100c0d0302070b00c11069078590015402042140c52800740c0d01064ae450700a07141c01000b50b0302c1e044982d09104081d44c02a52000f95 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 245777203 1250 245775953 245775973
    0xf010609050d0503070f0803040209011e0e280501051e31060609050f010305040c06081308040e1f1a030a0605030f1c02070e0619030510021801050301050102 69
    0x1181e00c416400314800c20441c0d05e03100a07611542c0c0e84190254040307602c07150020501041d4a480c210081c09402e40d0403607070240c20152519a40c00401c18883e0121a0031a080002c8155064148000847e480f46503900c0041501140340d070011b25003405014800d4200c00c101449140d050900c00c1c40581c2c026081d032119050515500d00d00d078600390302a501c81c050a850b544191200703070181d100102015222903001a083c002040014100c1d51285410103103410100008243c0200c0c180f4100d4205040c00ca000340c6503002c85000403c038002000d01a07020010740000d0010a0216a80c4a090002c98a0701604041d0305003180d4a0518411841e07604041d410341644281014001c68000311019400191180d860002c00e0030851400407000706900f06002ca4104036007000c000402c02c14081c03001d0a116802c0c1003100c89030080240070140140e0140a001c000f6040003038003d8003030354102c001c071803480d0318452110010358401d01c404404200c0d51105103403594000e20580341038400503006001c0d0462 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 245778453 1250 245777203 245777209
    0x80f0703060b0402071a040c060e010e090603070801060e0a0b010f12050705040f0303260601090611030c01111c09020d0204092607020901080d0c02010f02150a0c080f01060905 77
    0x706118020f42c00703035003081820002103040040700500d031103030030380402c60b4503160034846188000c41d03000c0e8090001260107041c2507a84100c0030854101c08450f2013805849110200e85404829001090715600c1d080740401c04044d00c00c02c1d2841010006014404c030024040110307918001104050041203029080121420658000c2c40e400011481c08600b030550700c030201110148554030981c0802c00e00400e044540b4894111440121010754400710a4282800020006841441a60104215041c0d4142658814001c640000003004002d10081c5d54501041010364050701c03180b5034043d0342c8480203c102000f4091003101503001000306048412a4090002510030440704444018119040f03044403541c0c2090110140e40b400b01e015200c44861060012001041e080040c0c01d500c4041c1310aa80381d8080180c064096080c6048a0f42c0800b0000a074940030100c0e11507640d2201e40307000c0050900c019441a00c1103001913903142c241e038032075140d003845442c800e0003424001207070f40c40c05100c0c0381 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 245779703 1250 245778453 245778461
    0x13080d0918180c03020f150306040f020f0315011209080d0507050c07030503031504050f0408090321070b0c0c2802090406021305061213140a0606030507080f070306 72
    0x900881c04104156080d400014480b848501214000410201403041d4180365400006a0805444000c0390b080c40400e00086800b00401040c80b55490300c181d03000c2512190151101e01042e21760807038481c10540da4900303803c0625010039000590071040780d0041d0259000f580345403504403050074a46a903070390350a0042c29006200c4024083c040060020840d0100001002540920081c503141d003440d824100d980e0f2140380c03003140700c0c81c20b00c028086425005030380c99402937449038090740d60382d1305000401d007013800c00d0f1a0780b05030f41205000d10384a800464010212144150620019680da11080c403809018140c0c510460750f201c02e88031000303220340001800c1d800c4009051000c907030300c266001506447c412a41110302c42d0f0007007101845c0318242e02d541300250800321111030038000d400003202c84a000041140e402c0002022440e13090045900c02010341030500750603140090b080c0d080843c0900344501c400c4171103200d08100050040804645e905080300500c000c0c01250340740d51110b0000e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 245780953 1250 245779703 245779739
    0x170703050c060304080703080c0c0d02060f07020c06220e04050606030d1b020108250507021306151d060d1e1b030e030f03010303110708030405092a0f13080d09 70
    0xb1070f89c10405400c00b80d40c06c200751602a0320550003040039183ca0440b4071202140600910150350102e00540000c5ea070388016540340313091311130580d0021000000b071400c102e1a1036000b81d120101a41c103100c18044007040d001c0c0700710016411a00c5842a96a0403500c2155184040c154800b00240c3d040056100303080c0c080c0c01c401c18160102008040c1190301900552103210b000125000065080c110308000000e03140301082c540d8104211807800705074140540e41c0008082c100412038480006d10310a0540356068460003610254594001c00c601c40014401e20740f0030aaa140001104400c40240e4081c0e042c40c8080ba0390700c9050007145040550217000042d225038481e0005000914000130054090346c001c50003036984080303422000145904101150700200002c1c0c200708418032050b2551010540c019a0701482c0702c0e0000c0000c4000c601007601301280304454407000030185204440741d4090414103c0003a007182c042a070b00d18415584e0400046144007007209400300300030401d400c440c0c0b1458 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 245782203 1250 245780953 245780971
    0x21072102120408150604060b0a0507061512060513120e01031404081207020c0618061204060e07080a021305130b040302030d050f0403090902030a06170703050c06030408070308 77
    0x118034030380c0da01414541054020300c96984c008012082007190100c01a6080310003034400b080709500349540e0a01c42e00c1108194030a000000640d0030030084141c0c001d005041142041c0a070482d2111203000395020040720540d18181010041342c0c80d0b000f41c50002c4d01d015400f0005506500c00d401d410780e400c41c0f0b42160311381450382c1d4042030061141c410420030300c40c610038041240c1c0c0341c8041c0c5403180400c001819020855000040e1100d00d0344901040380c2115050000f09484000e42030002551480380c2e107c02441c4624174410b00042107020b400802041480c10180e8114a44401c840b5948603080180a984a22a010610b01c81e64241d80125000150040b00b58980342c0361342c41c0c0000715042650101d005a100140006c0d200c801c80c41415000504a40b0306041d608141d05d0003042c40d9020b0140c920050b500102140441005038000f0000b003048900704100b6000c20359809898440c684020340c2d5034000d4030500e014034904070301100d04c130f182e0101c140f41c03c04c0e516850807254240000c0586030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 245783453 1250 245782203 245782213
    0x21309050703050a05121303080304063e07110402070c0b1c050f01050102060f100f0b0423010503040f0c0506120403110303090d030f1d21072102 64
    0x40480e40c1801404051402840100240480745c509245045000f1602c3c90940710107000095100420b40300000840382c00c0b280b1207480340c41c0c2d07041c40380003001c6010f44203141c032048505a04607200000d030030703580504500c1c03100f41030100c0043d6800201d01c1003040080c06c1c82060172001c03040e860140d0207000b0040c044c50440b0400c80d1a41b075441102e610002228010f5400400035640400840c0038182d03100402c5003014402c0d51400002030b56032034024008504e107400020000d41071880e00710324039005140b03078141d29601c0d03581c51031440d82641c818014480e03910044260b000c030300d2000841c0e802d076012040c0c1d42c00e461503485845000c44031380940d10807106a030181c003000a06a4461001d07081050111415a130719003031518000d018402008010451030b00700740108840307948049035002580c2c1d42030401040c401924480380d40203001d101c6450744511851044202c03460400500c854403104000e2803100420040d21120042d4000d0000017459041c08101c844041800f00300c003440608001e004035a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 245784703 1250 245783453 245783471
    0x14010801290d0621060509030f0301060c031710031401020301120201110a06140a0b040b010203090105160b07020d0f0c0203100b01050909010b19030203130f020a08010e010c0f1b0213 80
    0x260040c48181e60304c04088003241c5003091120a00c50103401c40c0480c0700079031501ca180c540c102424041407081c2001d00c005241180c5c141030003886208440c0d80340e8000c0440601d403071082965842c0d014001903401229412004014000500c21a81138900041100212400c1c03076004641988d012400c550b480c2c028500b103140080c01d64000c4410003820340c0078203034240c40e2602030501202c0c0d50450301441241002d00100140c1d030080b0031034222000a00c4d100d41d9902d458182c040701c200d06200010a03c2d0240340404c400640d011555504040245d51080906820b51070100c81c11400c690001c0d5041d000300141500b01034103907106051510b01070601a0611403550001000003000341e00074400010300164480c6561003402401034142e1240c1002c600710300b00301d807064000740f1100000410f0300c40320090050079580e81548070310041106000a01c00c540e84030007200e0180540840740d5020483c0c1d1400390001034000c840e400da0b180d02210040c1240030554082209241c01c0400011041d940d80c4485 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 245785953 1250 245784703 245784719
    0xf0901051005190806100c021305100b0705031306080705040902030a0e1f0b04180b0702030c12041e030807030305070905100c0209010e130807081314010801290d06 72
    0x303840064880d241c0101380d1800034240520350403a505007008100c140d0403100c0c01a41e5031240b030007400117070100029003a514405070420400e0176420405e010500480c0134020800000000c000c10308080070715244040e502c00064071103140c1550800e000c104180024449508140c0c042c5030310038000d14020529030240c0a140f410918038038000711030f1005c483c240d005501d03414080c4810016055804021034a6650400c001180103c071000304800c1c1c00c0c1c4082420706100b0021380300303401c15000a850039408102121141d9078050710407400d880031020340041d0800040d20805040340d0700075001c103140c0321659500301d0080c000104240c0500000740b00c045041e456882145080c102c86440c0c44101d0b1240d4010080d05040c142d02ca41407140c1c200c02000085406800040d0006a1080000707803100b00364070b014180c6000d4074080780c007500a2410b00046140f001f419103d9006420780380c004071646c0310071200c083c00d00b2a080b518608031000400300b109080c628000d0035807200c8224001051a00ca0f140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 245787203 1250 245785953 245785987
    0xa0e041103190308090f0706020a030c1a0f0a0b0a050114220801020d0605030601050307050607051002070c03020906030d02061b04031712070302040e04020d02010c021801090b0f0901051005 83
    0x1043c1d000801e41c40030001c03c08000c010f10344040300e0100080110314a89800255a080e081d03800400b006001c2d8032507801c0000c01320310f0180d04d00c00e0704c1030304000e8504403100040c11039040f2641d48040342070102803029814241e00700c8041d030703034181e45e00304401380c00000c3c1280641c050300400c00072901c40c4241d20780e031200541000000d44041320004d40d417241c1500e1108195001d46d00301038072035003014004010564002600800700c600c10b4070920740300c141500301141020409440110114000540354040001c0c0c480c000d810741788200d94a400c185ca4090515a403554045404800341e4005404500341220740c0c1c17081201010696025890183c59a90b000d1902080005004143d5004240041200104194290b03c50103a240071400e1610300003540121420140002e4010105d01075050f0a592082130b6140c04243c010305091180ca41c000a444034020003440758000c01d5180c038680c54014036008101a0041d1801030928046901704420041072290440c006014420104003824402c03050400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 245788453 1250 245787203 245787253
    0x3060d140f01060f120204153807260903010e070e0f0f0f1015020609011104080a110103090506070903020315091c0201020d0e030306040b0a0e041103 66
    0x54225003018503001d909540d42500700c1c00301c4159003901031004204007142080364580499020880ca1500e000c3c040c0301c5100f6400c0111234404903c01c0c00b040c3e42d01c20784078103002c1c00124000448021300740315511060184900c02040003542510350f000d8030031a11444400c16090b880d6007441c04800100003400c441944602117840e400214080040880f01d084040d48007600d408661010b01d001d010701c0f10780c00c0005001140030024900403401c800e44003010900a09460002c0e002c032607101d54006540d6940071a4507884c55803c0040700c40b03d944140007541e044441e640300602a1214556901145081002c0c01504040d5154121000b042040054a0240c25180c4501603603a04500502d41447c2c11840d4100740710f00032405003d08488000381c1d003d00303030581c1615080d130306d010141e040b40a031003040f06240901d0b0600041c81e034144408002540140400c840401c00c0a400e041403000c051010301c19480402075150020b4040380c15802d0f521541e80c8010700f44c4e80d038140510040040b00752404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 245789703 1250 245788453 245788493
    0x1c06020d150e0903030103030f1115040302011b14090d050c060f040e0718060c03091502010e0105180c0114040302040c0306060206060f030c2e050910050a021203060d 73
    0x4000b04081d4188040c0b590f000140030001d145950304649002d1b0440c12030340c00a9080240411034005040e0050040c1c1ea0b610045103009111400d060034024007070b264002c0c00740c4646030307288566405140502080522655451201400c1690040c01c0001c00c81001302d050365540541106215075580c0d400c020119840000016a00c9a04045802485840007445102404000301c0c02c08210a8010300d24802c44156240204804626103012541e2440541c016103d4031070941d80c0908668041d000402e842c1c5507c00200159501c05013460103000a1030445502c0740c01820107800309520440a840035040101e043c81d141556940c0401d0072540714044230340000e03944c1c000134000d00c0d605002c6550486400c48103611040060000207440f40040066240b240d0501312150300c8060380b10f00c28501500d09800c403040e404001840140403540400941c600c1610303440000d849070f80c0108103403030008000754010680c000394030202c140c0f00d61025241030b500281100c0c249d40015601000c806040e4128 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 245790953 1250 245789703 245789741
    0x1b07030c030b070309031205060d140309152811030708030f070302182107030c1a03040302030322080313060b030304030506060402090402070b0f0709141c06020d 71
    0x42c105141000c0c8090000d81c10141040c1c05840400c0c2d12419140f4030305550100080c103074480d5000203200d03d441480051801c94403400000d09000044080d21481c5401d45c0c03001040c08114403c0880c82c400c049282a0000c9525041158000c80130448044010305e410314405d40428070981c84d10b540c006880c119403a140000c10802560072042e5440d0b0041042c2c1400c0d030400c150504022074812002d0045402041201d020072008130000d40800c0781c00d090708003980c01d10781d2207041880c1e8500702030007020820542c1814120a440d19101168800d42e0568040c500315184c508030111140509194411a01c2d03003204040007180e0b0b0600118010110380825000c866080c0c54920151103000c1c5c8014401d400500003040402c2e80410b410b940008201c600595039501000090000d00403480702030618003c29040211143c1003590f920300403406a1034480e2960303900c0c40c208425402003000140c108a04491000e0f52024100c2012001d80c801e80b0050b0502000c448200229440c0044500400c00b44c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 245792203 1250 245790953 245790959
    0xd15030507090b010504030f170904020d0f1103040305030f0603030706061401120c120b0d050f0f0606040c0c020603101e0f090908030408130305030d02030f06010c0b07051b07030c 79
    0x54482c90000c14400c0c28140c0c105484e603100d1281043c40448080c0c004405c554127280720a020b64111007010900600464441c2c40340761544006000c1049140a41c07803810220b078170004100320644e807040768107983c0c4078035581e6000f010214980002d428650544414409000054680d014000c0584003010402c0341e41144500010102c0e050b44900280032031400070705840182d401008917030300b44d40d024404210441c1c20f8021070701218003020040c2043c0200b9862600701880440c008070001e42400403652030b034441804020880e044a050ba0010580340e0a0410050500e0000781d5440201340a9a514240c0da46214100000c040105104a6505d58a092000c004500d00e01030150480c40420030a01c00143d032110303a0b501c00500b002e05007400c0411501c45200d00542100c01555104069a071a000240140c101a42094400a0036007404800043d06d552007080403540d015040040b008654031110f0094855901c00d420031050050703107001100c0c10700ca04009800c001d51003900c00500e101c4c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 245793453 1250 245792203 245792219
    0x40813033011030a0e030a120305010f06090b030106121814070b040b0a11100c0306050109290a020a0b0114010801080312041101050705061503010e030901020a080d15030507 76
    0xc980103502400ba8a03403500211001c004103980c40c0c09918101442c4055801002a260020050f0000c00d0034117003060403201c09900d500158101d480004d42a88844d440d1030050b103140b0094080c010125105000401c0306c24400c150305d840318822140d0005003008607041080c8080e0081074107441d5043c1d8009540360501080004200902d003480295050030300f80700401c4e0092142d43c1c0403d0400200f52181e9a4070342d024000300c05041c1103031900b0440c50f01d4625001d8054405882681c2c00b107400c0c83c50000342d10f800001d1074000c07000140e20b202100000c0c0e9007030101c142c105103041800c40c0f05207a5403200140e000c0150601030f044002c01c0d580031210100005000b000140c2040e00c040e00306201c0087c00320a0610000d030003603841101c02d0044910500100d03080e020340340000c0c205104920500a18030103900c0002d071800740540083c080d80404968842d500d108980718180140d20000c0600c0108031000c02400d1078800045021030780c840602e4407188800c00325001a1681e41140380100603240b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 245794703 1250 245793453 245793533
    0x30f260106110d0e0d02011b0303140601110307120e061815090102070311010201110313020301060f08100f091205031806040812070e1c02091b0304081303 68
    0x1108100081c100360940110003407040e0007a403d0300d0700600d0605c1010045a00550000096809000c1c0c0320000000d6070038001d002e044030024101c03100b08414045100d5520589054000004040c003c5242c541d03244d43d000740321101171854508001c0054461070701941d844c002881030080700f010b1291a00e1a1904011824202810f19072440c481040441950790300490710b07070201da0300005400000b0111f1801070b405041407201102062100008028043c00c00c2a0260201d42c001e400810410b500c440e105d000d00c001e180104401c07030b070007912001c0389500c0c0ea41020005082d044004214440384e070340c03054000b414000c0591301240004c070801c458607a512035500440341c5418010a8103080c251905007051050007205120b000d11a0b001809090041c40300c4241c02c100540003080307244003801d445080301351000040744181d40e01c81c0402e222940480158148849082042e499a1126500c074a840e40c41020f8801c3c64070010340c00080800c61038946101c284940440308503841081098282200c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 245795953 1250 245794703 245794727
    0x150b1f02070509060f010c05190c15020d020c1c17030103021e090105060d090f150609060e0604020703111204150c05100b0312190806030307050a030f260106 69
    0x6041c0f49030070031080350365000c005201c3c1c98003802d000d01c0f500d0407800c1c500d0030034240504900d01c3c0407000704203108000040c0326003411251501c2c030390401c00f01940e90890b00c0e0f0b9041448072006034072004440c412807910b50002c02182042d5082d1402400246d5112090550403034481c3c2d80701d2030701000402c15402c0101040c140300c8582444c5c4a01c03034078001c0020340401070600402d80110b10106221070240001e90214000d140c2040040088130031601d002e900c001c00380c80460084a04105000685580500030391041d546220048000c6a58110601000b0740104001ba42000352032600100f0599052151b0500e9010a0f07426070380c0c490030b120b071100da100785980c12042000207901003807000c600007043c0c02d1071014201d000829011100f000280c50243d844880700030a241c0004d40c00d10900c100f250b003451841c0e217030311000d82681d40c00017016201e006881c4042c099400c02004200028030602110910b1092400e02c00180d41d14005904a01c183e00710302030401100c468018400701d50426290394031307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 245797203 1250 245795953 245795959
    0x80106050705030a03050c0909090601150302040302030c0f04060e070503010305211c0f020a080a0f0e06071103120711120306130209060408030705100c0f0903150b1f020705 76
    0x2a0501e1642d402d59a4032030700f01180109944d540c0465003210b03000781101d8031241c00500340c0303c15040031f1420380e031100c4080c803600e00d104000120080300d050007030007a03604483d00203001d880540005414000720f40b035401400e43c1c5c0543c4e1a4808580710106001c901e0050415648480d00d82d815440d0803803030440c0c0d22050040c0d40588a4420164805807404c981c4c1804045204200c00c0750880c0710381c1c000d400240c0c1081805800401c403485101d911032047c500c210700c18070084c414022076034004802c48050315519078082c1c0282000514240c003075800c840d401d070b2200c003c580c40d00d88100d540680c4a0001d8a541d0001090810030100d100300070414140200c80c443c0c2c001d4558200440051900b030300c0508480d154a801240080465072640305031070091950400f40c81c0d40300c2c001d00d001c546410070a0341103034440d0300c0c01641300b144a10134140c03200103036001d80742c070340000b4216100c20201700b80f05001442030030344030065100c1c0da880e24201c0c1c1c0d13014102d42030440d03000c2c031450f18040d050016075000940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 245798453 1250 245797203 245797207
    0x20a0c050d0c0c060f11010608030702090a050f06060a0207050901030c080d0e031e190803060a08060c03040f02041806020c0d030e030d020708040f030c050a050102012c0a02090c040608010605 84
    0x200d000d07040f126046070740300c3c10300d24241e01d52000152540300340da4401d00380c41d5190400c0000c080502000074001d1501c211124001540d80040c00401c4401c01c0c3c0740040c9800d02400059002d0510340f009203020b910030300403601c20594880001d0030000b0b09820803030fa0b12915481c200405c1008208040c245002d0741807284090b42c113a40400d03502c0a0360707002040c0c0c02e0460310003020a1074050050800c001003039001401c46c04024200740c091644146d44081c054078242d81c1c00a0b4216010600c540202d0000014030314640340c1d03403100c00390040360032001c0c4d030f03c580c1e1032010301150102c0b0a84880c20074880c0e8000358450383c0c1805d403a07040c0002085020249401d010300e4001c001c40210445a09148100d00103881c0c0039242071820359400385802c1a074030709020341d4000c800e200c0c000c62800700b2110b003164000c0543d41c50f140120300380c0d4000c0344210394000c400b00200407411001400070740c82c580502e00f00d401c902020b8000a07000c1000742c2d000307290401e0018040c030249500034062070140a0030f007002c0e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 245799703 1250 245798453 245798477
    0xc080f040f2c0f0703140f011a030907060c1703181b030c06031f0807090f0902010c170904230105220e160602030901030b0a08030403030e040f020a0c050d 68
    0xc01032480052a0f044409030110000310340d64003a601c145015040244508101d01e4200e005c000e088100780034800302a14060441280800c0c0340c0e044038812010880540301c100e190140036140202180800c0304d401d070004d0440e1030009001000f541c81038020510720442540d03060511800d000010003002111a03c040141c0d0f540cbd00c000685408040341074952030350301da403040404241180502d40e00388400361040400142c1c0c0c07400003098030079240d610004214001d031107807006041390400c90b0000e001c40d00b8009040e0115400140d40048030607400039403407030950365000250494609211820141f05840050190041d15114640c0908016145600b025402d22441412161000716040410782c907091102c121040c00e2192403082c400d419181c5807043e48a00b406512600100082800a4a05007540c00366190096008086401c80c0004d503140c682191801c85041d041040103940098a8001d110031049051000305064041071f43d034540c00d2901880c0181c14881908e80150400111107000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 245800953 1250 245799703 245799779
    0x6060307050108100305010e1006080705010e01120f111c0c08130302011512050105060f06090139030210110405010305040201120c2003190c080f040f 66
    0x102050340c60908108800d0780c4c60102c2c0c00e4400c2c03101e0f080100030754203003030f82c40340c14580014a600fa0800310101c01c2c8690342d00c402825942d011580b05140c00101c0300149040654000c0c06c0c80c001c1d101540001281103c0f1b02604842512403d03052418201000900724501100c4001c0d40288480018414403403940d10020040c40103402030540c04441c00200322010806000754000c0c80310b248900349645481d650741c0a03204017013240850660f607039401c0000065840c50107060814003191b00503c070505142c2c078000119101d802200c01c59408140316100d800e002c051a13a8500024003044100000c458082e01d0007d013405209926101c02d0ba0900700c8506000c12000c083c2c0b401c0e11400c0c0b80003e00790380c450004858908040050341b94061908607d1280c03a0341c0820000d903407860100b0043c0304890700c03c400650721311914404e4062038190387d500518071440380c0c032400d02e06405a101700d8140030100c12082a0f0f40e00582c822003d00c007101c40101f0090180c40c0010b28031600e8203440384040321100e007103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 245802203 1250 245800953 245800963
    0xa1205010f180506060d11070b010b03060109080f0d080903040909051605010903080904090206070614040c0b04030b0c0c01110c030d110702031c03151202120f120d180503030414060603 81
    0x141c1106c3da466200c0111009145402e591409400c13600340101940d40303590710b003003a5001351811030002e206940b010455003000520030540031103440003490060700500701260b407400c010700350400d039003c2040b00141190081c010411094068005400851341d074910070103020300c46520031b60501400b100104085a10345007039400c0300200b0346020032600024400154248102100105840d00c0d041509420200326107202d486144590300228459466046240c1140520f10009124010801c0090078480041d00601030150308400082074100a009a0f282c080d00a8100801c40303a101081c2580c1280b2a0b01900080341c01c485030161514043d5004039032070703000350014000c40c85a414111984148aa408900300b525001c20101c0368645403181c4880030824070388264494400c0c0003116030302035000300320b03480100040303c028401001d01c80f84500603604192080300d83c1d9650344a001c02c55411028800312a1480b810146903039181500c0c000d0040303881e400001c41e06602400400603540c8002030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 245803453 1250 245802203 245802217
    0x150714030406020a09030c14040606051e0c0f070308130b03010302130e101a12062a090409030306050102010f0b30070b03160813080a1205010f18050606 67
    0x800580c4e22010f03080d094400c0803941d84000e04825000e14000340780c0790200400640701c0002c43d418070000d41e450300111281d010761028891028043c4840415480081c002040041805800e44803074030200c0010702d00b031480350f60080e05c03030a5000030000203007020741503000301404510401390b0840d4195004500040510011410740d05d41d40c0c5001e802c0c0d08410840503e5180c0b1030b003c01e220a1401004a610154800c10a00e00070070088080240e00c401c0420124820072a2444000b580040d0b10f80b50460701301c3d0204035030383c050b10400800320a900c070760003501d14a50181e100469118030b4000028212244030342130f10a45450010650800d82d104100d40b10074100c2000241c04c1004000c0c04802c1001a89100f12420700c200400001c0815102010314880c0c03204070702c904500207410a06032011070b400c4903003c0048207880c00b49800264180c000d0002c01d141803400590390920f40903080c044079030a801c0b01000c5203a160041002a038180d281c101540d0303141d00203200e03d0a00e038000c2400f0340a071079 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 245804703 1250 245803453 245803463
    0x6030507020616051606020901030c0c1a07050f070506040c080604020102100209030f0102160b060a0305060a0c030905010e1608030c0c041a03030a09140f0d11040e010e1507140304 79
    0x102c1c000c2c01c004c0c826800e450100c04000a0700041620341d2400c90020340c08881d0050200c0d0800d180300641d2030240d2007880e59a42c111020541c1424034001c2c610720300310000d0a6130140241030142c07004410403200a480c01074800c8005000714181401d000304203041d10f6200780c0703466116004001c0141d81c04640c8003214500c140380035031114441c50000b8185a00c0c509070b0b00c6036610101d80d81c3d40d4070b000038800002030390281c0440c540c036844d4001440a01d40203400040d042e0342c02040031407080003503239115100002c410301e800120080c4940e20f650954590124482c001e0780034402d082c4052a41d14021001056404011445d0801c140030305a1150100c80310240700e42c1e514840c1e803d0041d0341541d41d0b503c400004064a50f12049440040c01d08038080c0100444607900c10010300c00c0d03080c00c1c007800d0490080140b0400207880c2590f14206214601c455950300070340c40d5410114030120074000c0e2204030210a0182000d07102c3d110810148220042c0171204108030010481004a000411642c00540003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 245805953 1250 245804703 245804731
    0x50115060e190518180c0a120519060212070203090307030201030b030703081b0d02070b070b070e040f060504050f15090a140c09190e010612060302040203070e0a060305070206 77
    0x1010701102d41149a4000c58104440511801e0110300c00c2d01158810403038022a0394000c0020344002d55140e0300c3d0010300745c22040034101403100b2007a400407003e005100f40200c8400d80d0625541021051407138401710303a055004540714810302c00580240381c0c041e95501c0110f04040003100025682d00044c44041d0505d130b40c503d540607054034107121010141d45c000181ea0794800c0d2081e501003d07a440d031402d1400c4ca019280651f040b061010403c6003c0781c603d45003c07130a1880f191104540f90001508080500c000181202200d0300d69001e0080c0e42c3c41041c0000503031600d48014002910002050030039a5101c00301003001c0c2240709030b03c3c461389243c16146481540d8502c4182c40003001d61910a4030300070100d1007040b000c440003000400c2521000c0d01d441030604000100c0c940648050300840d03100141c1c0b0401840380c113114079015501903820041c042130341d65907074000ca4100c0c0c1c41626600c2c0040c0c40d4012602c034134289603054400502491074100954a08039130003e44661001d8800281c004c18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 245807203 1250 245805953 245805979
    0x3060c0301180f020a020705010f0509150d09020d14151b07030507060207060504020a2403020c1609050403090512060a02070218090a02091612020c070f0909050115060e 74
    0x119521100c3c640078400d004540d07400181e40017943d00e0115104440c0060140410f5800e41c0e80300c0c2040c1c494000c2c0c0600000c001b281d450030001c0881c3c00c40c0c070248010995a0312a8000f6a40300003403404058060b01d81780e0f004480c5009410300788200391084072a5010320b002444a8041040704400701e500221070140d85682c1a482e0481c5d0b80d10900070080c1035240045982c4d8244012540a280114400c4418084c2603958035106402000500324800580d07079030140c6419054000d400602d180b030380e00c40c1074a4400900c000004031054864203e48419541c035401c010070142c0103c007030006030130112030138481903050316603c0f6941d0078020900405140c000c1200c5045441e201e041603a90111502442d18030710b003c143c441d684856864040c2e00c02c1c0028404542e00080ca00d4002e2800541d5603100f001020301e5a082d00065401011031045500c145034002646110840f0040302400f95500c02180c00080b90030240d0075a01c41085c55480205903110821641e41c2054484044103800e64554041d050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 245808453 1250 245807203 245807249
    0x50a090b07110d240e100c09050d0308090c030a08030a020a030b09040f03080609130f0804030512041403060f18010b090a0e011b0c02130204080109080901020c03060c0301 75
    0x114085005810007990425901004890303841d4031041510400d40c2500940c40854280594002503205c040c3d513084115454080003481e041000394450030f040c18109580d45d4000300d82c0c23042020030700354001800b000520011070745c01d0080c0c1c0c880c0340084004040490b03003901c2c5c8801b684030140009401a900003410940319000f5000760b0200380004002d4040d07440c040c20a8079050311020710480019203003800240851420a04c018041d204203034107002058140da60700580207582e21010383d42c1c03020070700000001500070801c58014000000c605d83e21386190800c0d881c44901d5000c0d003107120b504404100f10a811004680a51084c901c0a4601c890004080ca240c010900040d0720b0b0b400c4156030307007042440350b540d400c5006480e0518000b00100080c4020403078540d441c071b006400010ba112090b01026203000c1486081d2603916001c01440d02d90394260013030031240d07001c00460f210a4042050341140d030b0140000d561400c0c0541c0507107000c7c0380032010300955120501610000c0c55070030b244020480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 245809703 1250 245808453 245808473
    0x90a1707080f0a182301090b0405040b03031c06030b09030f092806021f0b060301090c051201030308060909010b030709020c120d0b19030b04060c031b0915050a090b07 73
    0x10200420802c065500c80344445c40c024200014000d0498179000b511400f9441401941c01300e0340070340171050505082c00e04000141c002e80a9540c0e0501c400d000700300d00e0303074542d14100342600040100061382510f9442d0410392548002c100b03009039001841440e55250b0482d0440c0c092807412517601c0342ca1100c00829104111000305002000b405c039100c08120a07400045100c00c08000c14040001c14281c3e0703030201b0a0700d500505031a00904140010040f0500d60f8100c003d17110f20904149007442031041d4004400d0f60241c0c0203400144403481484610b00b003c000180d00402100003e1009a090002180d6141a10302c28038111382c1d400640841c04890920820320800d09182081e07a42e2005080114094070b02030810368443d0300c0d0551421200344007005250100e980c030000c2c403400c0d0395654840800601506110109158450780c8201c5c00b4074194283c5840b40c0300c984c940c502180e00381140c00280c3c04015080b9410300008200e07001086401610311030441c0e1061003044c1d036481c4c441c501140f40c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 245810953 1250 245809703 245809727
    0x50c15070602030a0b0909030f0d0c090308030405010902040510440c0a09020c06010603090c0e04060203090601080c01050405060304150e1005060a0609050402030618090a1707080f0a 80
    0x1c2c40401400010000ca40061240741d00c201c4035691a5111403414540740d12811030407881c141010007000318024400c0c0c014882c1100700782814607225580c1d4903840d801390700444e412a01659034490000031485c0034400c3c05e0f004200798210344c00c564140f054403995152502d000c0da05c00600c00020f94481200d003d20181124540720760820034846034001c4039a07d29028580501c65105080c02040c5480c00380309407003075139003c0001803c1036460160107600410b62030b502035131180419000807498140d00e4010b140150321402c4016a68500048181d09012060304201d403280c1005c121400b03d41e078044203440c00d464040340d8140d940d0b02c99140800348800006841241e680c1041030700a844070740840c20100d1035250003002e0016a45007030030094481e256000304001b041910109021500b8580d0155034880c03400b6024a1600240e0000070040307100032540118554085d200036000c01071441707c041c0f10502c020403c0c0d8144040c569819605000f40c200c07002081c40e01061054289105003006811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 245812203 1250 245810953 245810963
    0xb0a120515010b0d023106080c070503161505070c030e0906150d021204030216080f1207060905120418060302030c062a070906081902060906040b0408010f060b07050c1507 75
    0x300344980c6c0c17485240f0702481040c010945000c001500420810100c405199012014507c0d1a4107003a02d21403a0486003400d540413031070040c1c44031629000d845100c1c00389545031103080386100343d80350040c4001c0c0c9402c2c015001e1002d03031007807080c03070f440d0504201000c885d20700c200e40d120302c05000c085009015041143c0040e0044009100602d5008101c104200346003c01d0f03203140e00c3d143c02d480b9581e0034654004c0006035028411002c0c40c0c11658000d400aa44036010206403996291102860402d28010940413030000140803c130325000010744078100380202800780480e07455600040d03102d0814088031806440001041c44032090700741040703c4d10707240d0040c0031030b181c11824101c41e0b510000e41c000c00d52070314600200401c07403240c00207516030707041000702c1c0d1111210384550038016943c004c403003c990400014800450700c2c400c80c002410252001c2000020480b980403d040e0943e1881e50001170020800c01590001c02d50220307886241c0e84050310954208062180c0a000c148a5008040c3c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 245813453 1250 245812203 245812267
    0x3050d0f0f02250c0302150c010e0115050406080709020c0a050604030f0e0109080604020103201809102405040902030c03101509180b0a120515010b0d02 67
    0x1091090742d6000d08001e8a481441207051000100c00c00e020245503403000d04400d5107110100014a002c08100400643c0d0150300ca08110310030500c0f42c296510b080000c030091351034009480001110458001c000e0004450500aa40c174044580c1d488203901d006080c00c4d241c001808920b950300400000f21140c0d440303022a8500e2030141801401d90100c3e04000c000102c040329040742035171050b00f0300380907101c0d12405401a900d8aa00550041070701801e01840304800001d010b000e04000310240c4000c55048807a41c0c40580000104007040703030010018417034030441c00c0c0c040c050301801c4410035130882003680b03c0d148000c040146c16112070140d680304101c283e0000041100040c0424055405541e60212103600e8a489100e031540030700d03441001c00d00003550104100507201c40400413200c2d80942c3c0c840016481c1d00d00c80428814142a005004410700c080149010000104021000b40b10302d080d4041241d414065042c1241c403c0705600c4c014903030045a042c001c0348481091580d08450742072885 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 245814703 1250 245813453 245813471
    0x27140a05031c030609020403020913050f0f0d080109021620060409090b070908100f240602070902071e030302090409060b01020c031f050711030c06101706010303050d0f 74
    0x1001c40000b0450100000d0811000082c040024029035054940c000e22021160b40d912200701ca0f61202600c05075194400c3c2101203440c80010711020f080340c012940030303003203c2c419100003514081040c1c2c040307090701c1d204000361340c94151a242280c0d441640300c60144200210000380d0f0000c2d0000c022a10f030b2200000800058156240d400b0306d91551054260801d80d90b80c840c03083e41e00d008148a180708a0704034035189417111a17a54003075100d0030840c1d000042c10900100d0001841c00741c0d10310009205500346001d000309a01041504000c06071184150300e80341c8150b840705849402c0c80401400500d0241c1034a0405000c1d4040d2002e5000140c010001c80748241803603009003264010300e44c058014242c09600c0c0d41030100307078240180c42c4802c07807080189200f80c4420042c000105030a0030465114010025454144018840a100700700285110300700703145194404600c5a222110707800c01000c562554800118409045a07010f08101f522003c0e048407800150405060400c1a949401684 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 245815953 1250 245814703 245814733
    0x60501060210110307090302120111070b0612060705090105071e030e040510030c0e1e0f01030501060e01030203150711070b03010906090519020d090b1627140a0503 72
    0x1036080000105000d03c030108003e03e403400c0320f201c1600e000c40026040c240520160030002d050410083d840c5000069a114100506278903411001e800c950300e030400c2041c040c991410740d1002211038004800f4000e507060904010b0a40c0c4602d0369214140720300403807100240454214a850401c202041c807000f1180c09185c01441d0000c04078a544c4594908404505502d8442e01a8001d40758800e0641d00303000e0820f1002124810b00400704003040028040201010309030100140c01801d50300000c0e01154118039025003512400d40010403d24100401080582c2d800100903a141e4254004480d40c2d4a0342101100d0308003c0c0442480175126200c00001d150030400021812107510010410003151605603203020382e00e090316001c8003803075008041040c40125a0040891001003003000814803c0d07555000e00c10402240c9040b801007404246152440d00081304034520016161040b20181d0b1181088440c591580280340b690710b1003000e610500d03100d04080c8009044010700b1149104841c1d029 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 245817203 1250 245815953 245815963
    0x40206120f1006020303061014070507030b011a07080a1815021501050d08070b0c120a020c010b0103052a0409020d020903190201020a02040b010302070c140f0306060307050f0105070605010602 84
    0x4040e1600d60310b180005000d61001c003c0d44d0280c42c00078080d403080741141c2d00481c2c64800354108444d080104000f424001030f800c01c5400c00851286410000c01c0d80b5254540001c40e40c00400314482420800001000078082c80442e1138007450b41c2000140755016003401c000040d0607410407003414100101d20b0224540026a0100325607600f101c10800da078031134080c041c1e250342d000c6004003940c00512015002070103030250642d001c184c1100050034114160901005c9001c152881120b150340010407e541e03440070300400c080381400b802d052205080003000e019441e42100840c0c1101040f05014080d090100c0782210010a0031210554544a82003031581c000d600a4484602c203110310710b450000c500b5440c40d450380b525016005000d11403040d4003400081e100145480d07040683c00c0080c0780000e0340c1c1c0c0790b801c4003501d4003480e074803a01055107003400410b0031044059840ba030300c21400c004030355400282440030381d2000e86144400e0b14044005807246c0c01004c10040031181041c0001c24100e0b40064 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 245818453 1250 245817203 245817211
    0x9080c12090406060201090b0105061c06091e02030f06040b0d0510331a07060e010b0306010605040b0f09030a0212011b0f021504050f07060909050f090d08040206120f 73
    0x203400c000d00f590b00c41060303007200c030b4518004000ba42018010412460000007405101e80d43d41411403800c14900602b104450080e080024699511071008034950f051480122003c02c001c0001c500d54140003020140c0708100a2030700e4461030300da26506400d078848600d6464a182e1207011030324517000c0560700f003014109040010003921074010303205c61042200c84d590804240c0c0341035030501c45401d0291001e01c80c130440501045002c410420300001034034900c108121511180000142007490701c08040c00e045041e40907008001c0c007848244001280401150080441d01601e0359840703880c24042400c00301c6003032005c0c2d84185104121549a1010f41190700400f0007060146119218540300f03880880c5d44201c1c5070010b80c04810800038904508403c560001e0241040b00c402c20030383e288080c0340800581140c0e0002d080703540200414074180c044c26401c4104c0b026810300d249041d2020995440d00c07054080d0802c600340300490306540310071089490342664402461014607011a82c2c003800b92050b5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 245819703 1250 245818453 245818459
    0xf0111011406030f010b0607030e030106170f0106090509120c10110a030606051201051216060f0905032803120204090b10030c140703020f070e10080105150409080c1209 74
    0x840e07182d5601303410301c5000c008460040a1030f05248050310112103c0742d07031810154241d903803008080703807000e1b132a850b41d22450011402410300f101524501c90075200d582d804030704c4c0c8508103000e019000c000070a4441d08058110249030721811642c03542d615241151004040b07043c0741402001074034805000505555005440c01e220143e65003c081f141840744403082d40741d0060f0000180011714020007101c4140d008201219850000e0622078011007600394082404031351002c8184000c076801c606000300801c011009030800c1c444606554400200785811500c1f440b0102580504060044808204604002a0454442d51140010001000d41e070040512a0500346140002c4900c2405280614251a941c030061190808401da0054001c0d60088080d402102000c034034105d4100010740040c415040350308143d0a081110030184981500100c80a034140810003000c0070060f840d102c8000e02c2079400180d5510981003103c0e40340506c0340240403030b0240c8090078110394500000750240385400c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 245820953 1250 245819703 245819713
    0xa02060106091a210c0310050901080a0311160e150603100605030613140f06010f020318060706050708060411040305150903041703030405070f0b090f011101140603 72
    0x1d101c090310208154880c0c1032003550700d5199009468007080c0a024807100346081c1076414080b00c090204100304c11600d0a4403480e020081104000711400d83d20000d18094984044a5062419458482101140280500c19101004110800304126460145418441d0701b00c03a41d40741d410440c2446002e90f030442c4040e00804262055143c80000c80340107140480b0081c03030b102d00c3d204080e1800d81004083c4e40e40400180310403452240240245c1c1540318042040c10314600d80700202081100000e09503e0405c119505040503050700002115503401d0713401d024025000130071001500034800c4081c000c110a041806020b265034002c4592401900304540510200c0b003120741e4444140114400039140380c0c00314100b42c401417400402a03070482d0316601901d16140e00c80300e09025015042a2011990340000104402e11030144a4480685a0f40034031551044c41c09041d0f14031405202041441042c940144400b90b030700401d4405400041c0500910080c1041c50002c0200c00045507400e00038010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 245822203 1250 245820953 245820959
    0xc0602010f0204060e0d02060f070602030a050703090305041205070f0803030708012304200a200304050906090a1506020a03030614100c0809090f070314040b01060320030c0a020601 79
    0x71a00a440030398a0a980702803c07003424504101442003d240140d0700942d003040080c0000903280003d0501d00c4c00380d08090f9580c00c020b541c00044a030700810b16030030145400712020000340e1160440c3c0031a920501d07084198142c5051a60500c5040e5208504107403108000280070b40001c0003030b501c00d800640311038480360380c0c4041401c0100702c0d44040c0008524801c94113840ca19084c0d01a850403014200724120f00000e0204050f081d9020311110790224040400248000144402e1544401441000745050502e400b011824900b40074203001c0c41151030400103295031100c0c0c4d0200406405805010144903070310b0030041e444848400d0180d0000e400c05102003403200109405003032011004e44a80e00f80c0302c80010864540003000340c102d0740304a04214032030f05565a074460a0240c1c2403d03000c103415040800d00075007228030b28200217128001c480e08100100d25288500e074115030842c00c010a00380011412440200311030341c1e840701220790100900c0303020001c960161951000b690211002662 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 245823453 1250 245822203 245822231
    0x190504120813031e2708060709030c0e0a0221150607110103050903040b07030315080c090c0307020f010e0604020117100b0a05120f0a1802010215040f0f0c060201 71
    0x861403001401180c0f040e008109002c030040c03d0751500340c0031450321017510b500c040d100302a48162032494150b080c44400341130000490a00c005c54100186003890b00e4503618513a10b0702c8651640b4801c03070f010b0704c2c44000042c0796000c068044803c4142c42e100c070210010001c0850f942c10b44001e4440ca0b01009d4141801c05440c206030085410b8a030704014400032801c580001140034100040c102c81c4280028040000d110301d403100a026600c1c400d48002c58000c4c09003c8a11118903a580290221380c44040804010b84540b10019084140411600e40d00d030303030720f210984c904600d0003000d0b010b542c41c260b021071807134802084182c0140c2c401d81e641603420801001d0210361000c02d9424070003810b0780080400080c00c107000108018006800c010341051100b904854240c4021900d804400c00600104501d0324500c0c07013800e21140d02510248001e452940000359181c002a6054000412510224080c0002100902ca070305522050500806a2520b84640c1f410028411349015600f07000e203800c0085 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 245824703 1250 245823453 245823481
    0x80607020109150b0f09011710090f030f0905030a0b04060b03030a0f0806041b020d12110a0503060d02030a08190906051219050a06031a0c070b1905041208 68
    0x150001c0114089038450f000d440c00804000c8585070303000e4845890642c0320345035101258024612000e800d44918100b1201c21309044828075580c0307006150029210000d82407441040c65a81c151814901400203803000b90b031140c08035000b5a03450f106021610003044842c00c507440c450b87c0f155070144200340320700080c55560300030800e1107808140d030507890040b001c1c41075000542c0064001d1021034880140404d0420710024041c0c104016008083c8907400c0d540c0103104d00211001500080141c00104040d80d6035a000e0134500508110f40040032070710341d5462a0b65a004280c000301030701e00d00d8030b40e4038080249a04c0111a00d2051410070190804e880c000c400507011117440341c444a14200100205841c4d8400042146521401d0000100344001080c030541c0e21415130400f0004503036096007054440c080036501400741600c658070410a540302c1081c00d03246d6080c4c2c04140c3c2046526008072a141e110442200d81003520720b0f090410040c0210b411050f52000111344855103980c0f07500861284031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 245825953 1250 245824703 245824721
    0x501090504140f09030d05180d1d010f050906031617010f1205011506021f1e09030c0510050a0501061d13060302190305010b0603011802030a140906010806070201 71
    0xb001c2c038000601c540900d0b80800d0f80c84035001045e00e207400b03600b03620f06085500955819180c110f90421031103c00008200f00c0e0001e03003940c07c0c403840b1030321b040e1040880103155201890402081010040200c1d00900079210900c1005040940328a403001c4104488140224200001032060342002440004d44100f0b82c180c1c0c007001c55115103136091204610520302821402c0304e2640d071714040040c010b00c00200c1e190141c03903075902800e259035410302440d11903001114501090782c6800d00403e102415181624103151401d40c002c41d85021509050382e02d2660050040c1c101e01500180030140700490b80194800c0c21207140802c400e90326018111050780d00c2292070440800343e00e442808615084a480304440d092440105602c1c1d100d03030224240c0c1d0007030384004200c1d403800c920900030007000f0b0040c68155042903c940f41158900408000d03410f040c001000b801ea070f40000803d052000d00c1c1c000003541e41d034143c0d210400c0d04100400ba03070355540c240f1441500d030041d0b00105040c5403042c09014a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 245827203 1250 245825953 245825981
    0x5071103030604020711041505010e03071d07030e07062a0302030315030309030d020115050d0c03080d0209060703020c040615050f090a15050d0c02060103021f090f09060501090504 79
    0x110755402d02840000c0d48001c5090700c0c030701c40f1025645819541c60151100000950030564030fa645084000752a12001c21b110f0343c442e4004540500004240c9074501c80c082d40203031040501500c6196042e40245861041c5400b180603d03d030108180d500910800b94002c400c03941c8182e01154100c810300c03440d041c0540100160400c00100e21007140d0044d00104001e0014280c07464100c5480000c0e1402001a0704100940d45805905c42540f041c00c0c220b5005140542c0c4c2c6440d80c6155594003810300c0b0050000030000c1501140802248425505503903080c500503080503034440241c10060f43e940318640d04c01c0c1c41207003001004030742d1001d00e5400c01541c0b202c50311503508218240e1400c0b1400d401c944549070304445100e00001d800f0312446440f52141031191a41c1d9599034461025000303980864070950199800400100f0040e2182d0380c20786540d2004540344074250924000403580c44c0030f03517803103c91840f50201d4041102c10f030741da0222007103810903250303001c6a540e183c05020030361701c402461000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 245828453 1250 245827203 245827207
    0x50709120303060810061412070e09030702031501180b1302091c0b16021506040507110a0602040f080106140402072d06060902270102030c06041101020105071103 71
    0xc100c0c8a40c598004403107100c0d080125846464400c66445d200880d90004252600c0c0c0344100304601d0000c02d00c0700c01c000281c440f00b0403014003880d02c0355640e00c45e1040250308072a42c00001c10311001030041da06099402805c0e0784103d418070344c1d0b800321480280128681078140c0c5410407002401440390174128a00604501c00c900d1269412800942100c406550003d410760b0000551500c1c034a80c0c240d402d0311808182c0c50718105a800444e41341c03101e5001c40195440040501c6001c004c000d911a40a41d08441c00301b4941c0d68500b0440d03190311b49a82c4c00083d840b03505101010000309801074000e48820300c0814061590b9484010f01380c5080c1d2241a082c20b83c900c90003129410a0f8000b050490d015803440d2840c42c06928807210700030882c0307400740c4282d820398144034204240740c085c0c07400603c4411020f41c20802058039400ba24102010426680820350f503145005900900a580c0c606150300c080e10414501400c3c212280841254404d006510f06000102040c3c060214288039003d0880258 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 245829703 1250 245828453 245828459
    0x3020604112707030f0509060915010305120f040b030403020f010e150a09030516060b011205060f10020c181501020a0b0a0b040b0423070801080307030815060703170901050709 77
    0x9082c003025000b00700b05034039613080c070501507014001d450180101c44010003040c81e05120941c1007801d0340e200d04000358110401040403640015894007056041071103160344060311300041401e807046520032140d03c00044200814150045024614500301400034400700d50807021490300d0b03480221011561000c56008035050590a610001c0641d00c2410050f1400382188400d00c00c2c150300700000c47e61680c0b9400c07900300550b4401015001241490700501650a00b1800150006440214940290a070401c655000e074803c002803014088080c0c0601200036103e02034501c41c10307045507108142401628240881e501c005140481180c10600078451a10349402080242c49015a2141d115882c1c002d00541580c883c810043c0000044450001c951800614400340c450000c1c11641331000d24001040000780200448401d541c1c94502102c155603900c442c1c10010b1900501180c00c1070001c1520401c00d904104001000b400c900c504062550b2803814442c00d07517104440705000030b01004030030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 245830953 1250 245829703 245829769
    0x13020316080903040504052e0608130f060f0204090501120314281713030f050f073302030709060e12060405030406140f090d020a03050a0302060411 65
    0x5941c01c07800700d40c280e13442c1607642d200007400c1c1c9609a81c0ca51010b41c01480c42c504110840300700c1e800080300707402c1c03035040c5030700d8080040c2c0070f400001c1c640300c01050b0106801e030411a4854a01252070781c840707400c0080c48014628000250028000d01c110646050004501d8200e1041d17600d8543d076242c3d072414414610416032160f0364114004282a205031802001002000380c41e001844205a039696000608125000258180084d152890801850740d003000030944c84181c15100d00c205003049547c0b610407403060070076440f801038003604100c0e000300c0d450b2040320b208000b10740c5941103c0080c50344015018250f001c03031009550780408980c1000c002c000045c0030f28071071a50940f00030b00a208641d2940c1d4003a04180d0110340172500e640001405000f01c13a007200c0e031204504078000890b0708101e44d0802c0401103200f001035041c802c3d10010395010440d6201c0c04818069684402581c01000031854007941e590300586003240e20700c080403100800780c18002c401c522040b4070102040f0f0508440c0e614 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 245832203 1250 245830953 245830967
    0x306040b09090d032007060911090f010e091207050f061b12040606081b1002191b080a060207060501060c05060604050417130e0c12010b0d022713020316 67
    0x4c80142140500c410701c007002e02d030b170140040600070480801c0c46049450100d0310141a401340c01e2055968a0520a100505014680c19a461418940c3d06600c3d44000300340f40032100400542c14042c001600001c0003408211030610182e070004a50312510391001c00504003241c403014001d15442070280c0c191146520803003d82044c0a4400050341d13545030103980b03090424001a9801ca4070303070044604098100183c4807400f088461000d0a4041c0616041a00d049001c03000600100074101d0411255401603181c1d800514558080706c07030400f414607081c00039400411043d41c001d40b0300400000c0c15030080c00b542150a03480f01c050a8a6914102080004e203005841500c0b0300e02c88510301c140b600341303810081c50808213007114114994507001d240c1e920090002c080d255000c40902040c01c20340c11581f00036055600b02c8004c5511040892181070083c014442d1020351842d0004040b038428030781620002e10001d050354144c1601401e8103503d810307440b0030b50743e41e6403182c407004a00c000544100b02c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 245833453 1250 245832203 245832221
    0x31005071d0d0209040614090d050d0f1b1e090501090611070b03090307020307050607080307080417121807080d0f030902060c060916030b040f080d050a020306040b09090d03 76
    0x2c03510010b142e034000c2215980c048500703e41d039130380c2d580c0c02c16100d500456207a5030041c0380e44028010f00781c80490007081c42c021103100000660f12403a00079a18404c68001002c2e12070606120304002010403c0100071980400c002c401414461780c1d1408214030424862064070070617103c8592032894448200e502140101030f44c01d02c0c0c060104007044070790400009500501c8080019501c41045004250502d40a07601481c425642048508001381c075000c00da03039000102e42410901a6a0750030304800149034403c10b1501d5540c0081c02c0c41084110444080c001c7c420708140d9500c40710f8408807260f884445000e00f07072880d8030045661486510540051040f80e41c03500d0301083c1d80c1580e0f804a6031507000059968105e421420400a11400070010148900595081c181d0001d18646980040704030190001d00140e0300b1440d51820300074190110396030304210754010820781c42c144441d00029081030f0342080c407440c2406010802d5103840800c55018009180280080c444200b00990041945c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 245834703 1250 245833453 245833459
    0x3080a021c090603060506070f110303120c0301090b010f080a02130f08010e1204030c05060904020708030f040c170304152102030f130b040209040c0906080c031005071d 74
    0x7901d04580c0c01121441040100358880680450400d0b6002c0e080d2142034100034000c1c0c00500c200c002281c4d90540d00c81c585034001c0c12480e80311101002290840c4208030200014a104e1018407003004050f900840c12911044820400e181503440115100c1280d601003000080b550f0011a0100c005503000303001c8a1401c42d8001e01060703803114150941150782e0300c52101d91f552026145960f680500801591420507001d00f40742134110350301c64105448a01400740130b81004607143c2c10302e4031380d90f0458540d20b801c022031648034a407039051000c14800c2101e0444140490301b00016582c4821244691142d030144040c506007828800088d8030340c0344000200e001c000122002c0c0341801d140c0100007680f01ea141d0b2001d69640f0b041c001c543d00422014080f03510207040c15103004041080d0549403504194115400710031600c0e00d00b8280000c801d1a000328480902d0728400141c81c01d400291900469029020748041c040f19041820484408844420100720005c01100c0001000003180140d92402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 245835953 1250 245834703 245834713
    0x30304030e030f100504170301030c140102010207080c0a110102030a020703032a050601081b060304030f0306031e02120a050c0d0615141e0a05061804050a020319051003080a02 77
    0x107200949820500040c0c108510360711710921061104104901c0c100801d010502499945180d507800840000b031f02c078051583d900c50b03501428680c401c0d0100c91003590842c02e0b8585820000b090240c030360701240c600700d0383c98034040a8241154008802d642d41c11400d82c0180000c5842d41c3c60951b10940d101d088110031003a030703401c92034410000956885515029030001d110560411a0396403a100710404d0b0b012090780e000322036094960b9001e08517544036506140c02c040c607082450781a00a03016540000701004030b8100e00d50701c0d072030401034900341c614022281082d04140da61080c5448111041c4046c00c542c006401c0c00c03c039420b101108000551240c000029002402c1a40c1e4072500410307040306025112015a02580d85801020034240f0142001800e64494044c40094100e50b02880745a01401000c00c0301c4664a00c101f05401c144000980180424038114100d080254411a000d07004d03220328a208013160440b5109552048904491b4605c0d583d085448003981a0000c410300e034214031078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 245837203 1250 245835953 245835973
    0x9080c010e2805031c0b100806030714060702090402010c0501020a0e0f100f1b02040501080c011b030c02090a180c18020a020a1e050d121b02030304030e03 68
    0x910500d040c80c1030304405005500c065002d00c600303900724031812210361504855101c0104030007000b12000c01e1405450b100c521181255114080c141e400c0d402e641c03114042d405103104030b8000300c0d5144a07140403002c0e03c1211b91508003001071000b825004641001c0c0c24001e40c0c0041c03c01402d140d402c41e0050401c0745240040360740303040c2a42c0c44805a48005a021140c01c0d0381e500309089484100b0b4001c0b60011803800301008c0080c1032000d0010001c0420011310603070520304848070101c080b840d4000c1c10030f006541e160030289541c2c1100c400030500040c1030350301c0c40018840c0044208219030b81a07035000007038085a002c1200140c40500b002d440117645444c0c00d00514152a616880c0ba480380d07000310401441d144c0041065504006840e8085004009024241c0e03800f0aa07200c1c91030380511b2603003968482d20844c0365041080d5030b0040642c498020001300954000610403c1c03800d5403c000c0c800a024003410f00c03000310120001d05c0150f4024408140001d001d00c0029026140143c112244659 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 245838453 1250 245837203 245837227
    0x9010203090913020102060105040b130b010909060605090307091103070c02210a0203011a0a0509040503212d01050105220b090112200705010b04090822030201080a0908 74
    0x207416240080341c10f10800480c030071560180b21f040e004060845040128492100103e0b81040101c4415080715541e400d014000d13070b000f03501d000c0140002c65001c01c075603626004050050390185901c1031203440303243c50025180b46640254013055885100d0a03045454084042c1c0303030b180302180104d070320650000b23042d0180d020b444045450180ca60006210840c5180141800c542c03000c200390a00612144802d4019241c100303109041358004e0f10301300c21966031410315506600810121207124014407001000e216020007070180107a0340410f01485144440960600c10520052424803034035550340104503642c056809426985d80010001a4078241c107415403a04d0407603a0400304054402103111150703940d01400798800c40c2e0400c1010045c0f200100e0307915003081400c0b00342c0d5408403400100d0b030f03003040002c4d00940344800000d2f0050110170820b02e44a40c0c0e81d041000c1442040030803110700ca034160b1004c8103c0301100d4068440c034145403207200d2408090a04120183c40d0f80703004000c00400b640e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 245839703 1250 245838453 245838469
    0xc0d0506241b150403030b0901081e1005090c010f1707051c06030516050a08060103110a030c0e0115030b010c080c03070503030c040801060503030c2d030d0501060e0d170901020309 79
    0x141180855515070f241031703e00541120180d00c800da000d02c1001005002c10803002a21051280d07014441843c0e4041c00100d45242c0705810511401e002c1c10310042c003159400000d00d04103404400d032120400080d6501c41100c0500c15000c2441c1c07185680030110326200d003d100104528150460700c1031400080318820019981550300450b8141c1c400030624280c0300508400c240541012100722032001d1508034229a209018000540802c41e004c507048000da650030381c0c0d80b00455204051860a036174400c1c1003101e1150911849000750105d502900e03681c0d10912401420040c140c58426082c1807980703c07141035420486000c026803000300451008035008201031031081281090140da26800c3c803c220b800c0d510150f105038003962040c40808004140030400c1d004500c00c08452090700c448211030307404441400310801c51135000000350304001c64400e4001c18180c804036110108281c0200081c084c0080680702c02605100c414081d2220039640040240b0840c401403046a0400c884600010850 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 245840953 1250 245839703 245839723
    0xb070e0d030806030705060928030c0902030106030f0c1706190b0d0b010201060f0e1005060a0c02040c08010501050901140910020d020105070f120c0212030c0d0506241b 74
    0x2181c02e4208100b2280303000c200c2e9002801042d6042810810100e0103e0b082d1101008050644440400702c3c0d19080052201880290b0300080b0959007580d44569640080d8028040d210000e070910040e02241700301030080840ca41c1e890f680303036811604a0002c034600d50f5800307403220358071420990703540009001d0700000c840030305151400340da038440021075048100d81e0202811419a414440b00304880402407503a5801c40d141128005203035035908841354210011a004a0b6100d14003107101150035501c440d0520f40300d88256401c106100383c00703500f03030344604013440750a0002e9000c0040180d04d5205103c001c4440d4151801c403801c0c01e00c1600001c0c14201c41c0001b03400180d1007800c65208403982409035540207407680c104040ca44004110007000c158150500da55500e4645000703805980c0b0800040b081031810040d12500c1c1d0620304c15000096100600101e81c0720b0a00300896410701d0104000310520b602d01280440d805c56541c102c4000790006900c10341c140484203a000d440320010310140101c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 245842203 1250 245840953 245840957
    0x402041b0f11060f0c03181501060324061404051e0907080c092806030615020705030307020405130803010b0d18032a0c12111c0b070e0d03 61
    0x4200900070002c002c5615005100240d0f0711100500820400807021180c124010300145036603550f904442c4150500c01c00b000c1a86445080c4000400d08080d22105068800030758080c0312100c00a40da00c1d00c0810940044c1d105024102c1013001600d000b50f00d107031096400750304000d0515949100140b8210030b40d18840b900d80c00c1410b90003075107140040740e40b60f106d821400d01c0c0b2214140b01061300030354018515624002c0a581e020000d1071440c2d55508484140300380e0182c00c040d070300c640300100a814107200d807405200c202220407407001e00202c0c8080030790390b02400171400d0003000d800f04009000e0280800308002450456180828a09001540601500c81b64140e54085d00070680081b10a011882d2440c401005001e600282e80461040035101106561650381150301c421030300038071004800103140240000001407560103074400c20500714001c201c45160340198a040c06040240207168002119038a400c890008070071521040d0031403918035112480405100104078002400e02c000c3e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 245843453 1250 245842203 245842217
    0x9010902010e0613031e060c020a0510020406020604020409020a0510020d0e0a03020f01030f020f160203010e0102030c070b0717040b04050c030d0f051b0307030f080a110706050402041b 81
    0x825075800c900966010001901e0482ca0a904120703900c0c3d4202050200a00c102d1905031a000a1501d070b40c070041403560030080820260b140d01d20003030341d112000c11080700c081c014460121840282c52003510100c6025030003070303d40c0d40c3d216400c100c0148800c801c105c0c3c0c007544640c0d0200d100d45078107102c401e40d140e16130000c004116040001030308000541c18228419051900144016250f101d21064007243c00c1c20007082880786800040084d0080580d04c404141020980d101e5480c601b041c0048001e001b03800030060a0748040c0480e09070b200840d40144456070400203400000d04a0307000c0d9034002154601038101849414030588141000d8600340e820201a030b042c0428407509210101c0c034810110300511404580240c0600b42120410b0b6000c1031100c04100ca8070030266000b10f13051803200038021789556120703514010700707440c00c1584444005524800024802c1d0070f80c1c07290a50820356103005030b08007600703030703680c40c014041c010003c9270081e4503000c5c803071409002c8004007000f44d1103580303a41d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 245844703 1250 245843453 245843471
    0x30f04090203180d170f010b0a0c21020a06050a060b03010303140906030f010503060a1a011b051905060c030402010203070f02180103050d030e06100e0925060e0619030203070905090901 81
    0x170000b44009483d0911034502617004200380e105840444100c100e860602c86000c0c0d2190400c06141e001030344841a0f4280800034100401d90f0118124000d544594010010307a1584652902201c00310f001c3c011481000b0001480800d0241c0d40661369800300203442c0d447c1040c140086034440e041900c1580d140b2400c0001030040b03160500c9015401800040208680425010600340a254440d40c107814080905071503128112194070700041182c011084500c40000d4181030a030041700910700755014051030010841304007411080300e0082e50168015800d06a8a803100140b420107804202d03881600303004001a4256061052402140900081d1501c1c0200c194080c040d10f5801e9451181b9420940402c14010410a14035040d950070031440401640d5405149181400944c146801540f603880c1e658614200084514140c4840342e82e0300b40d4442824062000314000c1d0100d04200c6000214901e19152290340039682c0a010380c60105180c0c0c2d034800100341410300c141c640302640e94541041d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 245845953 1250 245844703 245844737
    0x4080709270c14060c0604050d0801150e06030703180615050d03050d0e0a140307020102010b09011508061903150b0901030b0106050304060212090618030f04090203180d 74
    0xd210a26559480769001c2511580c0310a80c0452500030903120b8410402e4400031520f42805456210108a0031110a81814105159034245011040000400030400400c1003282e5400507109401039850f4a000c2100100411400e0780005003100b08059442d003941744c01003043d604c0107862a01030a0001180b0394030800720300594034a40c00c10350040c880d0003412400607500604987e040210000009180c00008946600308402101c000e805503070058100e0510071070100040c040c0cbd5100b600204540d21081c414130201981c01d00c216040182c0450b13804035044e001d04d210540c041801855070080d1601821100c1070081550070a0b1038050b03805450182d003004610960221b00307400c40301e079205907141d5178500c200c0d803405006080401030040080b80030410783c0d4064550007402002150030341d103446100d15564140844401c80402c400c3c0c070103d140b00d02c0200403103c9204810048924041c1001300710406036102910000c0310f03942c14414503000d100280844038601126940340101c0c081c1a40302 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 245847203 1250 245845953 245845991
    0xa0c060503091c0e060904060807180e0a020904020d050a0803010906031412071704180915110a0c02060c010f0c08090c03031204030c02120627060f040804080709 71
    0x30f03089160650b003036465241c0e030440700a021070b5800701d4200f5a1402c9582c041409071a8907800f000052003103080200320018100c0e0518030811201000700212203000c102d8a980e401c001c40084e4001e900c890109000d030500c0d6509501da03078000d001702d4a101515541d00d40707040d8000da2003c0c007041d950358014010052040c030360b82440030f0030100802105000d0701d2042224440c8500050020303024200511a004070300341030760020300314401e07021500440307030101070080d1040c0b00041f1500c40c000b500b0000018041d00c00c1c4511456044200d506001c0d0903081a103855007424030a991019080c0030001440c5400d01418408050309800494102403002c805400094054486052600880309403050ba0320008107517400e1030841c0501414036141d07414150b40d9480d60103006500080caa0b840c40481c0c4400080241c002e42101807000e441c101c8540c1e240c0e07008002440d555100d50001e101280d080c60a5100070354010b070060015030301c0c01c1e0b502c4001a18203000d0307070710080c00203072500c0c00b0320310044000030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 245848453 1250 245847203 245847223
    0x21c0c110703083c0909060108040f02040e030405041a0414011a2505061b090303040b0901030b0604091a0117060904031202070804090f0b01050d0e0a0c06050309 71
    0x402010140e00315542c1d60150b0040c481604100c090b04e03000f035034842c0701c0c0b29502200e00020000e108072801000d210010664004442a4002c5898030007043c40f95100c0c5800a10441c1c01500880500c0403035400c01000d0120f440a410151209000104d0280d48a2180d003524150817034114154603400c0003800300703a40c5034000001d100a05d00c00108004c2400840951402034101007241da20b4081071542442c04409000c3c0e484502c50800b1b4100c10800300017003207400349000c0103803544030080c0e6511604a40c4100f100c4503816810031b100400c8000c050a010f0103031070b0414180429000204c00c08071706503801907402907041c2e0340c03100710140c0900e90b1400303180d82c2c100003844c1003e1030200c520071480300b001020f04000c0c0654105000501498480c903e0002e0130700380e2070070656840c541410082c0c0c254015010301d15916140043c500420300e03c1d4880e8824040741078580034246204101d9900c014a1450081e8000e801070f00344100015021100e00da003c0c181c10780755141c980c14404141450041e40b07a03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 245849703 1250 245848453 245848487
    0x3090f090504021f05030c07020d080f18031f05060f0409050a0b0708041a150a060207060908010209180a022808070207080c06070302030403050f030403140601060507060f021c0c 78
    0x1c84030742c600e117074010120396101a1113044665104030303920100c1c0c0034030f00c458009080f40c1804202100c3c601001002807440c030705680400314400d0001000c140d101c3e1902c0e1070b0103079646c005181000281c10150419940443c00406a00b9190142404039044c0d61200c0012100e94000c3e807114810004405046900140c403032420404518003a55002500045440c103c0c441918000024002e0710301e0a20072140300d000644601c140790385d520f2000c1e50392030890246502080d410800403601c81c805100750f82e4005001400b42903414800c210140980340041c05009940741c08000220054580105038103824440c07206170340700e092581100512080b80a03180804540255001304040c0e000042c2c20030100400700d80495983c0c030700b840e00b80d145220700e6000a18034012045915840e03800440a80200e9001b628044440500e044a03d900e9880034040e141c041102400084042003081e401400ca103840310320300510b0986613409414000d1031280d824031000d6100c800c50080300354405000700c00f000d030903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 245850953 1250 245849703 245849749
    0x2070806040312020f091801050307060206040b0703020c0f0f06270601180e010612030801080a0c090b0411030907030201121e050403030b0a080304060915051603090f09050402 77
    0x10355401410401001000880f807500459480201d018400844549100003851036509141d0060388016400007486514401d01030014000b802d240080f8256114907800320030707211141e40e8244160020b40260305281d0b00391180c540c00414460007000803451701d22001e00140311624102ca0070088501d09101001d611640032710900040c100c0c00903146064881c81e48201003621011714a040040c08006e80c481d03103c2d800c060000418041d02a07441840c2d600a40d03540f40385070707203600c0003e0387c5420710007000b41003a00d4040c080011582a0744884010300e4010404500300c40c072480d86025640064408001e07980003030600708119030300081c0307145c0c0302400c60205100011483c0310304d54a404114540c0c2031090380320310000d01014800d52041045500041081c40403d883e1070b2210355980190059038041582c1440c0070440b402c0a50351119101010b0303448926042c0c102030900448545100c0443c140403401c5000300d01d44418840f41d10291245010016103840d02e80100408000d00529405040042d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 245852203 1250 245850953 245850961
    0x20a12050d2a030f15030c0306110903030703080c160b0f0105010f1205040204060b0304080301081005060a05010507170c0c01120b09010b03130b070c030f030606080a0c03020f0a0f02070806 83
    0x550103584990a6071814001032240100061030040c10022400e02c1e103001050700041b0406c60145114002e8900841042006c242d000038100182d1251003070080c1d055000380300303480000b403140c0c4038264082000f5181d6030503d6001e07500005000e4020308120340348102c41f002c200c000743e1920b08443c0105000d1901c10707003030300700381502902400c5401981c600e21511180000c0554a468000000038031440030081d59030700e81800e00c80d03407a80080c06481d2840c0601c9010100c40c0c80d05010303240c000c6200a00e01c0d10100d140000540380c9a209803400c89000c551400b020381c0403041400980442e460410160042c101801c0006040e0004403548185951030040c443d00c00b519449000c5042d580e00c0d03246543c1d40e460f10034000442c10400b0178010300314401c0741c0400408503030000100b01c2da18400d40740c0594030402c50905409807003e900840d0005544a000183c0e412071230740207039519180c00d050040c5401d000142c600c0705544904000c44c0070612141e80350f189140d041100100a0a024020700b07a2414 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 245853453 1250 245852203 245852261
    0x1704060216050a06140705031b060c0c03041202121b0f1e060c0f1002072915040213080a020a0f182a030e12040b0910020a12050d 57
    0x881c0034444c1000700304006084161140c1c07049944654000c01140d4a40e604290211090015400b001007a0700410f030100f403080b640c03282580c171f811071084007030740c101402c0c242c020710502c480000c2a03a004a1003901d2500041c018003e01480c0c011845060f044088000c061295031316541d49818081e005031403800d211140c07402500c60040e0740898056684000d401510307450f1420100c4101214002c04607079a040300d1203503008001a80c40760400c500000382d005600800300d48071a02050900f46454000340e00c0c0300b4880584140c5c600024001070512136030303a0544414404603044052a54050103151040d8a04030200500070700b001100b200361301d42480a441e9548076490b1450a0041e15083e40e40c8154441c8111b20110a01c803c0300c41049245401000b000760038400e0990000b402260202210140e600040310251501a902e071840c24011205100307190784003c0c941070850103043c48a10010320100a101c0104400d965550384030b40070b490b0b00504076140c109440f2044a092651226480 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 245854703 1250 245853453 245853469
    0x1e0209130c030f02010509180703060b0a081918081c18030c03050f03090d030c090f0501050d020706060e07020105091615020709051801050a05040c0e040f170406021605 74
    0xf548100300e15107032a0f075840140e42901881c0041c545c084424040300e250307403a407281c0aa10072840c982e42440229611f01e81c40c03005100d2a0841d10014070b22000244807a2061410300004000a94000a031344030403420707110743d425400d1800c0301d034083d0004803800300e500303910070107002c000440108111318000c00da2109410a0b480710020140310840b0204800d0600550030b45000702042e01e84036540b458a012040e8640c0d040100003008240307080e90f8101514030a0241d80162050700e11312229050900e001500c490304000c4844501540820000e0b002072038500402c07006010030426000d060170600000380c03c1d100000d1460f00340e0303070010100c0743c001281c100c0c174a022607000c03000103100304011100c100c1c240b5800344c0205280ca41841c041c00080381e00c540f940f252860650700200615101d00c021242036600560380641080c0d00d5000a12800f10781303a0b199074025200700000b09600b54030340d6803c41010514008502905400700d401c001c00354050000124242c8a5116000118203110004100c0c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 245855953 1250 245854703 245854709
    0x11180106081f03030c1a070e04021806040608070908030a0e04020a020f0d02061f0e04020f0a08150109050708091005060409050f0d031107030207030807030306031e0209130c 76
    0x40d040000c9001442d2007910900d450107410044991140c0b00d04001d410410f40c16401c48109640d17105100c20102a0342c1d0761b40c0502002d60b5480210b800800401001e904002c200c403d4482180c0c00c658542c1c0d80790001000144155110f80c2e02502e400d550240c4500403a070700c01065030700208a0034088960001c040b1001760005c540040c0c8a084111040b4a8010920149403881c401c1c42605c40351142c001804900c5514001c0d00c41c2c4030300304c504500c850000006e1041881c0e40c4030030004540145003c804081701184c0203844a2200f6650303d10036842e21030881d21007403032681c6950040c411440c81d030003419808816800c140220341002e40140350741d400071800d0f050140740e545001c81c10594580e0003615800c0d070407000b150400c401c403070382c050f4507100c01d0200d04020030303d444035219040c02c00c41c0a80d5030700754168004e459003e1464035a110f080d400010210205a55044044009a407405000090f502074100e01c2000300b00342c0c41844541e407009090385212a924010314070006505022213410707 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 245857203 1250 245855953 245855957
    0x15130b19020702030d1706010318140f030307030f1a060306010809010e01060b0c07060206160309030e04020f09010801060503011214122d0708121b041211180106 71
    0x441010615030000034024158003d5250203040107803210107500082402d076050102200e0700242e180c400c0107504441c00b59000b205100410b860718804540c90207081c01010040c0e0040c1c455158121107140d046a10445803030022990311207004030b607405584601c0044081090540002c25100800504030303010003865035040040010001f0200c0d50290026807100f8003010090210785d444d0f11251540340c1102615400320300c141000010010320000783c1c64001c40c101100f4030b1404e45441070031805401100703410340030700a1000381c02e10780ea22248002c0c149024030600864645010b140014100081a071110b000c103c01070005010301d02010400b006004d0340040f03040411640b120065007032420a603121250f401000c680300a1035900c020740b400c00030201c210408101002c545c03415440c3d02800c0c00140c06c40307000340030361000711400300e03413454101821408040c40c09403d00b010301c8540e801500003014000c1c0c3c0c4020341081211500306c003440070700103e9107060042020045038070050014492002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 245858453 1250 245857203 245857231
    0x81606060803030106030b130c2307020a0303120e0c03030409150e010e011e0b0a0f21150501020102090616020a211205070c0515090306040515130b 65
    0x104221003540588000c04200d000c1d039880750b940d9000940105105403d2501034001e60858101c59680c0d0711031100101891b4482d164a00300040c22003580f05209204004c12080411182c80076a60350800400254443d54400d0780740c1c4100008401036800e1003000300415030040400428a40d00070042d030782640e03001e0345e0004075618822042030401640358820f00b403404c844000800c0040c0301f0003a603411384400914844140c00c031080c494000005a10880e5140380b4280003003401c440c850302c251343c0c4e07450b218038040c5a0140c0c00c800c048817212010040d5401990746071100c0011303038181c241a8004080900086007005040b6003c07441d18070404140c0884280800b0040c0f04565801c80c4c0d8602410441750f009440a10342c10b110181316a480c0003e503030710380b00c0c0e24040d50001d10850440d4107440d4010300c3c0070300e103030b00d06003d11013010008180d01603440070501c800c00198804010151055000e24014580d903036416151109000e000b800200051200520f030201040c80000c0c0e10740c0144090030604 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 245859703 1250 245858453 245858497
    0x16050c0102040906080105040201090b040e0f1003060516021c0c06050c13140928052208040509070206010e010b03090304090914010501090e1009020d050102070302060106170408 78
    0x1a0092155811104441d40313410404521000154011481640700381c865082003a25200444d415004500c00c0142c561a0600050f1040c028200c00c280c2040e40811a003200070f40302c1c1d0380e480c2610f904486a030081800800c0641510b5410000c644081c06c0448081d01c1e400b1072004001c14540007041c010386566201c402040300d0341909401c8448a6210b440140320035911208045241c1002080051003030b0140e1000c0703410303800c20561142d402d125034100d8005084041c81140041e100040c0030b03443c071084000c620713001403003480781802440303204004840d034480c00d0400300445204054080811980520018007580341d60003041c40c103560064001c103442e5904c0c9904d4618500c6a0340020301e14074207000128041000041540070b50300c88600c0284807d0381c954844c035040700d85201e41840d850b0b01c00c500008010101303522401c20540060300104000800f038035102e003a03a0200b0011401a41310b00b00400401d5417041000484812880c0901c0082c10282c84440c42c42c0283c0d02164803c08a000f0310f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 245860953 1250 245859703 245859727
    0x6040b04030204110405120a1415390408060f07021e07050a0617061002031605120f0304020a150207060e1201050a06081605030d140d0609020717031605 67
    0x5a401054001d00c3d04a50b0440d0315402501c80d482c0d10720480746044101000c01001030003080205024105d046551650f03990041c1d845106240103410045900741141030b05490002059540d140d00c9a00701207659492600f0304c37162405500030011120000700c02d0a1041140d0f001c101d0760307148481d40603114940304414114909105282d4001e652062000d50000b03902a0081c66850300b2410300001d200043c2c2c0d50030b050001140d60080d490005070000c000710070045800c65a003e1489000d60119070b0f4249040805101681c4144103e02844501200b000214030b009030051001d030244a128504040c46884007170f6030b41c0201c2c0207a2051011440250309207031680d8845004d414184402403007241001005040207040a000d05d00441c000e8503c41c000d80c10301058020203d4001600030010000320300021982041940b805201b011002c02c002880700d00c40d40203500240199401c0183d030f0343c140785401e010352020034900d8012014144200001c24201101800c44902142403881e5294804540c0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 245862203 1250 245860953 245860957
    0x6150503060f01030209150723060417030901060f03080d150b0301050603181902190f0b0c03040b040f14120a020f06091c12030e06070e01050904020c0102120606040b0403020411 78
    0x541c02d00c107030045248e206204100d940c0c00380024403400560307241318000c4a070741e84400085078087c0502101e05c2d5a0950500c0b807500070359011058100001d6000c0d12141c0556500085070f0007510410400b080600c1440d0741c500c90f880510b0200c40481422914000e5030020f03a0005101da588500400f100141340d03d5801a4011031750941e50007036900d881e0650820404082d0512003c0c0e014951081103090110000a044010343d00c040c1506001c651170720b203d00c0180e511a20011001c1c0c0801d01c03000903903600c001c010700090005600d010600e81c5c00e01418034040315491408074800c243e555152121008089660725150360141e569545045201000c900750303214070132a0135004015900e030881002103c811035840709104008100306074040b60030071002e4551200000503190802c0d00450111401003080034030b506018101107041c6113600300020200e0700121001041a500000c400307140c2c8159001065100b40c08417606400c0c2400c1802c1700c0d0050003280030081c0680e90310000c00e01d810a501702 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 245863309 1106 245862203 245862229
    0x1002040b090d0c080706022103070504030b100314030a0206090a0506060910030b010603020c0f070305030a0f0c080a0e1206010e0621010f06150503060f01030209 71
    0xc10848031050041086a03c000042e00c001a401000c2c000c070001001203030081c01d180701440094015120690944c02d442c1d59081007042000b0b60040161420340350804036002c22699400410b10b00343c4101c1d04064508102900200212840080144440011603007030b50130300c1d00e48541c110717554452288000c055401000000700310b418a90300095218803840c49130704005540781c480c0240244281c2240d00000d800165108105004000041c0190310400c010f043d000d165455480e07c2e80907008151080200032400313070345240d03c02c0c803051704c08581201d90709580700c03e00038024000d05201988280660b4110046190803040890400d04880b1480105001c0e075803813500300812900601c1074038a0310b180c10041c44d015a413091149410408110ba40001c0d4281004c2038a60640d00c25080c040400c1800c108005850700c5507003240341015020300b4090b8841c41020001a03ca8042203 = true := by decide +kernel

theorem cover : BRFrame.Cov 245683453 245863309 := by
  have h0 := BRFrame.cov_init 245683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 245683453 ≤ n) (h2 : n < 245863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
