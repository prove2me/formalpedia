-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2646
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:19:49.941331+00:00
-- url     : https://prove2.me/submissions/699be56b-6fc2-4a7d-85a9-85fe9c32c8c7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 475719424 ≤ n < 475899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 475720674 1250 475719424 475719437
    0xd08070c080a030c020c010207120f02010e13020d152601020f0a051c0203061509130519050601030b0609040f150f0914100b0a02101b0e120d 62
    0x2205015203418400240040c00303540d00144414581d5855048850101c5440e0215003008603034000582c0c94003024062203003450202c400c542c012952139240041450300604052180403c604081840d03442a54030080c9034030f0f00001e045030040e5a91240c1192801c011745003a0f5050b007400983d8086d03044850000501c030307035034868400002c5029811580c00d08040e0402c140c0d00da18040014010b40c019603030640e005520080f0035100c4c4e05481c000c40c1c3c411000240300c1c0000c0035909440f429140c01c031040e41e940110803000f80040740d5500d0311030217000380c4c0406032840c448900200703040150f80004104a04241c100350302d00040ea1501740540d486240215008074041d403448100c0c8000b000a2410144124040340c40060482a104408420780751282c40a10648002c516201caa903101071b108442c10700e032004010017090400001074181c3d40c1261054400300061206108207031520313445c0740c2c42520302116002011913044000b403050b004050b2108200d01d12402c0000343c89031030149040050251 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 475721924 1250 475720674 475720681
    0x705090a0608150a0906030c05030d0207060c030e03010c031d0a0c06210c050301170c06040302010c06092003150f0402010804020d120305041103030702101206050915030705120d08 79
    0x20150301d5188084004c0c0c040c00045580703141c2ca41c041c02241c801a40c1803644910007260508005c644900802d1060300140045464080c084904610241040c1e04002035803d41c0f40c8160340c2800343c60400450b03603602050750310301e0014184045444d81400003c0d42d1100c14243e0000741103884c40303c1240d51340c0c286030030103070320b0318104a01862080e1183c05115241c0040c2e110211382020103103040c0e601c0c0840c20b5800580801f611940c9100312022160f01450502c03042005621490291120903c24040882c81e00780b0f82e500d01c005030203800511030b490300002105001c9030400304401703000f45c1714419140d0764608000c0b000d040680380181c0082c1c10440c910300020299180c1c403488054195201c9031910001c411704c00000c0040a081c1c804651300c00044403400d180e40b4000056420040d0020f00040701c441040d4030035074410011a001032001900c51200044964070044107030305c5004108000c5c0098103c070b50815050032066009140310f00707084c488080c1c861740001381d0f0704a02402410b00380072585 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 475723174 1250 475721924 475721941
    0x190c050703021c110613171206090703020f130611160b0c0a0b0f0a06120b070c030e030307140106080604080412020402120a0209031506010c03031808210705090a0608 73
    0x4001340c0307541100d1159106000525070183e000140640c003074803421070081c0105641c1da00510944e5050010001014081a024030f0118002d40c0c000001d402c00500d00380c071081556959400166481200000c1b80d40304005c02c41d000014001d40c0070411000d000383e00c0882103103201003c164040c2950301c49011902c0400b5800c20400d0f40e03040c90700003c07004114a8680300c20000c88a0031542c2605a0b424080005401d25054480b0786800d90b220071140d1850b5520001221046481c0c4c100340c080240d50b0143d24074948040c001010303801d000348000c0044d2103404614900303407803440d44031099960140d81000041501c0724151000c1c3c4412052aaa0003151070000601a02072515014125444030b414000401e00300d600414500e14140c0c1520050102c501d210819460121943c82c0454170782c204850009100341c0c49070000024640150a21020320b480d1604030b6001800c9003039140724008500541c0f1080d00040641c401c5051400605d003824070408514400c0c450712422050118400100c1e0100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 475724424 1250 475723174 475723187
    0xd09060203042604060e0108061305130c081c1107050310050a0f06150f11070603060e010b090f1210051f08061012030c050303190c050703021c 63
    0x2a0021410340d140d05250030121014003441d155080c2c400d416042c004441c00000007600c1c100e0340145c440b02c1040029000540d58070348000c0441e07900c4000c501c040007001e401880740c2c5019803000381d480382030840d05192000840065401951807907208007815007000140300c03603180c0310302c0341444c201e03d5103150002c40c1c1b454424550400fa505002c0d5480415002c44141c1c010f034491000c0e1401400103407a0340e80b42008036140390240d4181908450440000d140c0602100b003600480c600c0c108080690112049090000715044400000d444590403c55016602c1c0b0a602400118503514602015100046c0044130b280c500d40380a94010210000c5000c0c0c10f0003c001103014420041c81146807031001804035050400101718400c84040e8081400800003076070701d11175400300a01e90500341c240441d451904a01c0c0340c040b0f00f00042503a214000130010300242d0300442561035091a22000070f04403100b0350744060104400c000e03040c07001d030340401c0d8000740d804900014003442060f81d10142c40221340c00f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 475725674 1250 475724424 475724441
    0x1a091c06020c010c02070e181e0a060b04020a0c06051b0d05071701080a0f0c0e07020c0108010b04050a0314031908010302011b0b180106050a080a05010b01050c070b161202011a03010615050d 83
    0x105408103049c1c84036034070118181031618410340c4100309070290031003000124041c8100e9840051600002d060000d0389a0b8800f40d00b00180c0481101c0354a0110030303030b610992145000b4060180c6039001d000910390010070340c002c0c01810183d02511581003840c01641c40d2380c200f0025240085607092503040c40000c80000f03014001c00400d98250703107007494000e0340c1e89884100320740c0050441000007a0488100c010346068840081410002a1540d150041000045000120107000c01c100d15100c1111200140c0303404040d5446191003907145000140c03c4a03a0712a59070003c1c0264414400000c0502c1c40a642c412290307516001290050304030640103101603000a40c001d00300400102e40403d0003e0b10020340392140c0c000b40000c031015030045610307004c1c8029464180e4082c070011f0280381d0305880034000c0341c02c80d81c1110741c024a9079140d08000d01c0009040d00d0141c0d55408004044089840c00c1c0300c6030310310030f6000303000c480c1c0740800140701c100120321403c0c200304004c60f080b00b2603c1c00e83c20a21380c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 475726924 1250 475725674 475725703
    0xf0112110105070c030308090f060615180603010e2a1213080f12061f0c2a06030b0904020105160f08030f0117071a091c06020c010c02070e18 62
    0x719440e0f01d4080c102c0b440036217808815115600c848005c2c540c1c0010b07004d100f500054410582840004002e19030b9070000074814882600584100dc15500da07600514000c2445003c4004e40d818080c00081180910303d50b040404d00b00f100c03800080b62000000c03a191100f600c80c00f0840baa550584401c551035045100414451000032803070384d01c0c219a0302514043c2c0620b69102c031680c60303070000c00210016098801c52801078a02410042900a1000c1c5c95014010040c3c41ea00c0340c501c5145401003080d4003613481000041c06000d209259042c0f10318000d8010548078100503003000c5c5c0028005000340d0840e22418030440000500700305007180d001244651048649403241480c80105001100034061100741c0c03040200c01c4a0210800907000084070110060043c512124100340c0410b580305205c0c041d0040700103a2201c1420810445000100c0d0160340010703280d032104640f19082d00c099078902400c540c02840d0901201201c140000c4e0040c1122035071300310148003481510b044c0b81002d1201e09 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 475728174 1250 475726924 475726943
    0xe0322030b1308090901061d01020a231c1d01021b13090f080c06280f0b1e0301061e17010b03030a03060510030522050f071d0f011211010507 62
    0x4030988c12580e0304456201074a84807051400810049a80d11f20310180542004840385421000310021943d00d1140300c401c000391000701205130362004409041c0c8080b480006c006000080a84440031103900c180c45091010304180c0080c1c0585105224018000c0c51152002130600302e20503a9075032000d00380c1517000b560b1003100a820f045c0441c5c40c0e0025011001c0502034080010b4030120b081c0241c86480d2404d5100d940b40c6041d807840440109005422003051039502c0c40c11400f1540e078030316581d06801c110410402c001403400141400c2d501540d200c004403407051000c001e980c5840742c0d6031400307540d4591004100e00400306001790146c69150326a54041c0070004064101b1030b8183c1000c030907031307009a800c101943d044010840854004842c8110f1040da210861280000c030822490600d500800881302045034448000742408500e900c00d240b010f9804610035071b51620880120f0f4011410303180301c4200d41c5400c0c149034042002200003807820a415886052a070b02803000d9510090300201c900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 475729424 1250 475728174 475728179
    0x609090809130509032706072303030601020307143313030504030b09120c01020405010e0a0510080406021207030e1c0f0c030207090e0322030b1308090901 68
    0x110850303002281150280da14201c0c0020120301da030140354020760401d802189003016400010304104660765408091440c6d4401e4480316036180700103485058002c141074824800f80c0c0c540020010b02e10180c00d40a60010b10411003180c0e004001d807140c0541000342140c079040800295402c29088908410b0080f10082407445014031074000034107002c1640700042c3c0d03140c58002d440824074802201c0140042c00c200b03c140000303101c0d0b400c01900481010216480d9514038400380e404c80d0050a00c150440c0e601260401c41503902c122003c20440041e100489040e0501020a982000003207080003848110030108042006030b5044803254002c1898041880c1003000c0000d01901d800141c14000e0701c80e0500d0001c01303a0140c900540d20542c661030b0f004029405810640305c4c4490b01030240c0641c09502c0e00001c0c07400340c0707000d811011407420018564034070a1140d11a590f0340a0080c0315000303858041d0a20000d001c04038130325007111603003a139010903030300d9854900300d00c5c0b180b004596005010074000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 475730674 1250 475729424 475729433
    0xf060312090b161101120c050a170c04060f120e0601060905090f060112140103062f1c1e090c0b0708030f06010203040e071106010e010509150301060909 67
    0x16003220280d07581c0d00503800c1d652068480a8010307140800c2920a600751860006015845074443c800c8041c10070a07000c2090f040c0040c01c4078001e8440c6008590006880c80040741e001c175001021030400e1058044604243c10254114019402000140007641041d401614081e0780301450380b988054061003000c0b1398952240d2103600c28822600071442003540030440d445c040c1c15441c80381d81c5090401c0d40c541d650200448504440107400b8100c142d44400d02d00003e212903140d14040d40c044d400124030007440d882c4500710180650b080c11407004003e41c070031100c0304c0700700d0886a006021000440792244c3c0215068000d1400c81c0050100c1c0f030450441c2c003e01d07101c0f038000d070800b94000e4010030a4665109a040c448c3e11070102c0c000c181810810020306058510701b245504800184116410b2548801d551140087c0a0350f403800818410407072085040030410583c0d026001c089003d103415450600032400c1081c01808084100c00a0100c010460302e0960004005180c904418041d04281d4140f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 475731924 1250 475730674 475730693
    0xf091c030c0605161211090a030b01080c010507020109030f1b0611010608011a01121d070e070e090103020105030a15060509240906070807060c0e0315040507180f0603 73
    0x81c100d40d802c2c1400006800b500b440070000f518400141c64010414090218904c001c05409466642c00380781400b01c1551a2202d8005401a6110340c04d241002d50403c3c0041c1d141c1180380d54814100001000f0020050340d000c80300c5411268403090303101003164a031401203011504070054a409901803e0001100c0768030a1411aa41040d20020041540c40358801800e0341c03a0070f030030400022050503140e200c5502c54141c00103200381c0481d002031084000031031011410710fa001400e280d54030002051261600c01400c2d980c2240b01403e005100004100c08604411070510010341449804000928100070540150445130205011004025100c2c40f02a0994002c040307407d0042404c0007859000c0a400d540040241400380001800e0035422002c02c81c40d6846081f044031200801e1200d2030001d040c601800c3c602103407070740380c5d0f0652001c094241460204a02680255561002c00380000f00340c02090840c1035501c482e651010701d00e0000d9000000d00390486d1044401441e0483c000107011100c038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 475733174 1250 475731924 475731947
    0x60714030903011e0c0e031c0e060a0507150b0a06080403051603080711012c0a0b0c030f090d0c030806032d15072a0b0f01080105011a0f091c03 63
    0x11020014040710113811580b1401c58500e06d60190302c01c5aa010044a03a1407001c0c00e404064605444001280030200d00c0c66000a038404011500205d03804d0100704608880e0b4100d0041504204141c21401e0001503c17400a4400c000600507848045420305124008841b41c0818040e802031040505260052074408102e03090b90014050805200c0e01c00418001d1510b030031442d050020760300300901030004030342409451000d0303603108541d101030001d038409031101c0c800c4c0340b00c001d100e440c0d20b041a824159800002d044512704e40010701780c2c1c442d00da000b207015801542c00d8a400c4106907030700c2d0007080c07a0400740a8900b0404011541082c9070004081c01089090381fa2016906902c1486940c00e10b90388003a1a4400811001038031081d03182c00e00a200030381c07204103200880c3c0854a5488a20300c2000540e1661080f000d040018001070728240100e5006081340c1c40c6580e00c00c1d11107881d03050940552240e078454968001048900b9a840500304011541001303243c140000700762a014168003c0d06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 475734424 1250 475733174 475733231
    0xd051c091d01081905060105120f100c020c040c050706050a0b030f0c031014010b0d020706050f060f0609031b03030408060c030a0f0b0a032916091406071403090301 72
    0x104d52001c0700d040e00c4e00148078481e501c000140007690808081100a07000c01c403421049204124410311118410420f11064001d00c00002a016001c05002420090304084490180d1b04001b2000c10044d071003070440308019001380b000981c5850355101c920162070007203c219494032400030420b08410000c190310510b03400803411210540701100240c419900300300190603041144400400c034034240f40004040c22198000014a003226907a00d00d421604207489a840e0590f4004c2044070a00300b171019a81080011940c1d9070915040310006969181040302070b01c5d00070b01c0c0214807011a00c0c20000c0c0c41c050100582901c0c00c0746044411004036410841d0080ba40c00e0500c4940003445030b091240e500c0300c40c0080d24080007030f415610b60b8031083c060103050070303542411414401110101c0050300d5005145224643c40029244c0900a003064850341160848100b080090b0807a592090101c80b0b0f010b40c80001c949007040080ae9644c114040d01c04070315019400d00e101488881481411160f400001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 475735674 1250 475734424 475734433
    0x1091502010b060f12100e01050607080d1b020f060c03010501031a0904081e0406020a0204090807140c01020d03020405090402220c03050115080f220804030c080c0d051c091d0108 78
    0x803401b0005c07900c0401c1c401c510040030040010b100e00c1c03c0c01001840e040d030152031400d1030511126010307012204495109014920600681000d6507414010250148801801406241002c0131903050178441071050906241e074854030460400c2d80c000002c04000030081041c1c450303290505000c0c0056110946000c640005951084a03110002061320151a05607000b4120703c032580e4203100091056031829039451000f031240d20b000840c1c2e07181034401400a0006455802c12100002e403425292640c1e91007030600520042c03096842e1310180390380c015012110384812000316800c0901480c0010160f807551400c100804442e25011342102c2d049800035005c40c1d00b4030103204011100b250096810984121464011038054000c10b41214116142c54410800c400b03270b140d858141680c4142d008440310401c80c0c0040108100c240302d803450556094904134a5940142d031429113440f545096200360f400c008607030043c041c0c403c0c51600064104d400c82e84484040b0710000d510031550910400285100f0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 475736924 1250 475735674 475735681
    0x312040e0114031b0d060b100903020918060f060a0e0718090b21070f030302011401090903021c120207030309060b010302361f0e0109030201091502010b060f12 70
    0x800103448402003d030507000c089421822010881200d0410200f031b038403292114804140307a500d510502884042d1a200c0d540e40030702d14411b01c1040c2800404406c071002c095040350f0f81d0f140000c2071301580b10076144074604440ea40c070000120914910780000b0603039020202001121504024108c0002034800c0c200b800d580d944008600a403400c00d00c080b5000407504000901c0c50404400458405403101d09951500362284a4840141080d0b8070960041c1e442c0c4095610203040d840409024050f107010611400c1c80588019540c1e600000c01611402800e00c4550711440c0308456035100364520b400150358a1100b41401809881e41c0e40303080e15214035040c024240743d03001c0d100b240c0300200001c440c410361004d00c40c0c42e03a00e84c0c000580620600240b0007440e02550f81c0354441d224684100301900d10a1014481e0700601030030814140c54140070980c0c2c030a001507a08203507400100c61340400c241a0902c0350b24012805410201c0f0710359000380b8040f903511541d2680401030a030f1000380d100106001d54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 475738174 1250 475736924 475736929
    0x60302070213051821180d1709090903040b030103030513030609140105161d0a05040603061d0111091314040c17240c1204050a030e0d0c140312040e0114 67
    0xc0700817074541403201042007040508074151280f541030081c0204442203040680d00e0b26882001c912003c48a510800145e441c01c901d803020540c0d8010140b44010340c2403900308400503203a48010301001d0203000c404114a070391151980002d0010350380c448420300c101d14481c9444491101d0080c590109035080c400050b0b04040844408640b40096550b9203442800d00c10a92002100144160781c1115005401160036140c60181d040110302c5814005110031200b0071022420702c031007001e152240d0400041c500b01704035100c1610542c40702101c041d005812480003500040c842d51100460307030b0600d0010081803245508200003110060f0241125072280000c01507150030130401122000b001181c601d0480c1c260781044280e1218550349070a29000c14034681381c20b01c0104580845040e405031b1450410560310401041c2d109905441e6031103080c000742d8402281c2c0076907010781c904181c00d004440060391360810903400a260300340ea40b103903140d445550204004400b40104681d0450604070710343d02c1d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 475739424 1250 475738174 475738213
    0x804060e0f0120010e0f161a0901080a1d06040b010801090506040f140f010b0102100c0c110301020405040c0305060312040b1207090b0f0703021e070603020702130518 73
    0xc0390583d141034854031881c083d00c240c01c100030040645036584191803507a040c4104005030b603c8404100401114840701c04584174949190454108801821541c2100c0c40890080d144c4400c02401c091001d66a0018020010114040180c610403844071074640849008166680264050401000d05030380780d0303840900380d914080000b081a4014000280410707442c4880c40c10b00361180c00303025025a450701106103007880c810010300c0540d54600000c0d41c15a0104003030140300040c80010321a039450200050304162403014050501410754504111660b802c1d030440303004d004020810020a40b1400000b0000c16088036400c0c00f0344240c49204440c1064030068504655001c1c810314134020032040900042500507001109218900e440458400c0e0890043e10f5001c15407038136142c84820318203000f0702d08040c4282484038114081c000c2c000000e000300f415410340384107080c05a0750301d00510226911507080d64400390b040d4640400d010300703038040700c0710f909800c0c684030115030f0a180646001140b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 475740674 1250 475739424 475739449
    0x2a040608190212012d0e0129010c0213020403060605150304030c1e14010b01080615090d0b010801060303020f0c1804020303090a06180605090607111c0804060e 70
    0x2400454007020014608001c0d51021994110000f0079580c0701e40a80c801e8100c0071080440c2021540390084007214094400c1034040072014009004a08a66516480842e0360a060034003c0c840030540840c60b034000e1841450107913016042d5210040342c4480d10000b50068002160018106100014a490011030b042104085407858a01d5500c480d5000e5810301c815180031540c0316250054032980e14000350104c1c00f698001c4540c5500ca140c10249642140c1c0e042100700c0c18803d800c004d10840b902c40c2021107400c2c421200000d50307150000030026001c0011041c0c001c0551b03008800114400c5030640150040b64826000c035880102005080f40d04c4160781304146402540c07101400c040b48a6540c81a500580098292132800d0991404580b007001c4941010001c642c20742181594003400440070002400f41c4c0c94920304003a281c0c00011440c1c410b0640240c800d040c6040450241d43ea007078002c1c2000a210303107a8079104820741ca40201c1c59040352044401040c804030a002441c03c1a601e00e908 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 475741924 1250 475740674 475740703
    0x70e060324070804020d0803150a1e0501030e07091e0501080304060507080a09050301090609020907090f0915080715090b07020f040903121503140a05061303022a040608 74
    0x703555211022141c81000510582c0d10800e2407041401141c1c6c2880190f006500300083d540703141c8110340601652410a40c480c03a08003010410081d4002400510305080d910246004241e0306c002c0348006140c0001c40d08401490307840c100d05800c03200c4240c031807126400e40b107500a0102c2d81e82c2d000350584a0141d4807541021807803c00c040700c0094082c90041030f102c64a401c00e11030030f0b0b403541d0100382103c101180c2152400e40c2d410f0035006501c3c2071140998030049616000c001141800800d05514541c2c0c41201c01e8283c445401c00313040c2060300d01500107451010201d0f004256031746d11030b00300700304005d1001020030b00302c40021649002c0314003140c010a40180c000d1002840341010303c0014a4051030035020425115807640240d01107000700613003100c40c20007014415055041c40c10071101c3d01002c103200c5900a840020006a010805551010020700c400342200d859080a03414010650203410003c00103080c4a40c040800f40c8548100e010281c03400c001958449104a9498400c000c2220 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 475743174 1250 475741924 475741993
    0x90c050a20070905010e040b15010e040e011803021f0b010906050306010309081801030f0c090e040c080d081f0e01050f0a051305090d020c0d02090a0905070e0603 71
    0x1103102501d0307940450000c054811a0704441da101011411501d0a0b00040445410380052006008480140304e8003d0303040c091226001170782800180c6088403d0500030b004035110221818880c2d030a6000c0031400340b50520070510a9a18540251240010705820154480184078011008403603c42c0202c10311701a100c103240c19080c1034060320107820003450141016124800800020409005400c201c620240d20b8110407841d5400034040d649062500a8102d00d400001c01025a0010084048410103142c0d807203e0b40301c5017800851448150403d0030588100c141c1100c1a84d4400342c20780c4140c542c810403e2151001014690411010b881500c1ca0300302c92400503c144c0c07400740d046485020005110482c491350b10300c0800c000b030f82284403000d40319a44500b000110320b0288400d00d90b485d0103201400c021111100080c440740980e140190241141c00005014000d441d4044541150010101c4003c1642c07012303010410503041326958003a025040c2c8500850340d05800404024540308401d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 475744424 1250 475743174 475743197
    0x101701060f0c0b1f140a080a0c0b0c030f0c0334030e01030e15062e0e040e0f0d0f1119030203040e010303090f05100e040e1c0504090c050a 61
    0x740e44904026064620001250250324200d0150410500040c000071013401910505c3c0f0381000714144040d4022030b4a500701d400000c00181c485108541518a1510015210444100b000d4594042c24000400314840080d425488403c004082c0c100401c0c000d8250721031034900d9000721400356483c103c6006c044590049880041d0240c07503844044003041c580041d5030b01d000306d0a5403400c405081c003d080450607800384070706803c0c60948103e02c4101c0307039040c1080102201a001c040e0003201c11680c100041c800c08058159600e4101048800e0814216410a03804100482e1254100d01111022485811031030042900860f4113000d51810a40900310403505851500c01140c9164411400c6000401020444424418644d4065070013039455446450418000030001007094100c1446008a092914001e1354414001d02c01c0640c00d030b401045511200c005189048104103820014020300da0f9280881a40b041c003800c12a8440003080c019030010314000e44a0784640d40316600002d00300c4109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 475745674 1250 475744424 475744433
    0x40e06010e011b0b090705031906020a02010f050405150f060d02010c020d0f0302100507020a02090103030c060e030c0d0e09070905063006040f060b030112050a02101701060f0c 77
    0x700755194506040415038605074180d4507040303030604101216140b0a0b00180011440f007001000c02404007580100034136548410803891201003100000c0a140d00018000322143c400e4101c03004803c1034503001c0c05981098a41141c5856100b504c62440e60056000205100f200a0032140900c0d0054440c01d92000942c00440b60481403100a03600080c2c0d0994a4000840700ca0807405c2080c000e0f80680102c000c00a40002620b201402d81001c652080c54818096550501020f0460b03a050809900d010124900340025005140745c01095000200c0c180054a2010560143c0d03000281d40e030394500030b101000c0218a28054aa2100184000b1424030240c02c05c81c00402905213080805100100310b080b094500c09009104108510f002d00284001781c00c01d4004d070f035188802202c040c00311300d040018004080c001449810100d50313a1280300c109002d424008042e420703401610413036001280c0340300079000c42034006102c81e0350f02d900b00000404a00c96450401e030084595074420b806803c0341c85 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 475746924 1250 475745674 475745687
    0x61f0b0412120f12181205090a0807180507030e07090c020c0913080912030313020a09090308160504080106030b06010e150f030c0408010507020a200904080f0906180f06040e0601 78
    0x3540b0718550529601000811b20f2045140a8003005644080d40c51144d00e00703000030303d001c65000005c1d60340000c1c03043c40000c0c0ca00c80fa140c8001c10003407000410703645521080380030b00001c0b45800d8441c0101d89020500d400c89800403901070401c1c1d0200e48101c0d00c0c101c117101802070704130783c902194a9050350b00c40010b41c03408010071454000904050181081048031030640e0710075a1805030443c80301030480114149040c07035600412000804115010b219200a00544802441d4200361603022104042260040c000d0b100030340b1004008002064603407500700807443c0140c40942c08160300c044e107107402e890720314050f4030b49247c4080b0481c01e10b00b088030b83c1801070700003510305030243c1802e00000c210300d542403040c588505010750082059000a09100c4900c0c48000e0004c000c0034502d01c0681240d031543d00005401541c400d0038071390f44e2200340700710390211f010754560706030f21a800180141c0a43c02000b2900da00d2102100c3c1200d03000c150000f000054461889800e4959a2500004003950301428 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 475748174 1250 475746924 475746941
    0x3080c1b0a1a0a0306030b09070e0606090607061e0204030b06121f0b061c020307030e0c0a1202150a09061103030f0703090c080d1206090b0102061f0b0412120f12 71
    0x8003c034201b44c50750355031a8401802c840d5650f140d8400c501c00c212480755110143c1d0021801d5454a00d08441030b00410420f110b18000036003116246c0a00084100340c10740306a030901c10100d41191926168030b801206260255402482048141c141308800c0c01c021543c0c2040524400c1da00c0803a480c4084a003010384001100b081c1e01840c148500800c4416980302d40d07808044070000165685460b5602404403251440783c0c0041e68001102000103845001c480b0703040e140a5240f0005018080c40050703031b170040143d004c0304200d40100348190400d4001202e241030301c41603100c0d050840610140c10381d036800102c80400d142606140452056400f135441680000c0c01444d00751806034860354001e10b003580c2d19032040b00244c2e0648003450111410b102c1c4d00c0240c400c0368818003c5080d001c0c0001d40e101c1e805400c019107826003c4441800303020512202d070007400c035800800e85850b030780c40f801005030765101000d9503198601103228043c0da1141700301d40c2d040b038426183c5042c180481d5151400410302340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 475749424 1250 475748174 475748177
    0x1b0d0c17070c0905040b180c04021b0d0f0f08040c060c060b03161d040b0a0c0c1407050112050f041202010b0901090905010e0a080f03060a03080c1b0a1a0a 68
    0x10007609011030740341150762016103a5840081114280b5141c0704126250080c0f8842c03204c0c203043c818061070200410011210801200d016803180000728080e404d04840586445a52080c8045a0340c01a00001c0080e000003c0da111140da80c000d80906940c43e0300d0442300181241141c0d0030600956000348002c10034203000d000001103110721076011900d00300c0200310202036140c01c204e0030006940c0141103201c800c60080c401200328241a40c0b0540500c00141c42e15000340d0700c070a00f01000350f115851985001e50410400a04454240c1d00030f601d07040ca038068280000d48408030004002c5c994040c031801101d00440c44d03056a035998940c00699403c02d81c80e50110354070303601e13841982d42e00d9100c00343c041c000600c0009100a43c0749815421501c0d104510701c65504401420804540c4000507210503081d042c030b2982e900d40d0f94400040480351a40c00050500c48040b800f08091880040e0310301a0920000304c00200e13001c42c100700144920180300304c4560700402c0e8104840304051102424009201b03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 475750674 1250 475749424 475749427
    0x71e03120c12080604060501050705033a050603010506101e110f0714030c0109030b060d0b0405101419020f09040221060a0b0414030a1401021b0d0c17 66
    0xc60380c030b042c0340e16014400e03140020fa546080c00a18500f601c10040140800d08001f4581000c0355669601c03400f80381c0c0c4400320317450046000703c550030100c0503003901e80042000d02d2a80c1c2c014074969500400c400e0301d00c41d0196207808001902410881110103002d005512840321060990003001504054610904200240720208a251040411440300c144050802030318117282000380c0403d035000312881ca28031035484840000d4507070340c1101c0300c4420390f908410300c44a581d03509008141c01b085040310050104071414100070a1000100306402c880c00650300c28051000806451460040107442e00c1034448203000400481035070907030007480c0f289c1d40185003900340f811840c00142260482114513a81c12000100c0c1c0707012b081c0c1090700e00e5115000719001c0c8451030814440c0300d443c3c01503025500300e0f00550070034010b956030100031000181e94001c48401340c1100108000b8081d4129014040710704108109040d03055002089242c00c4c501e0540d604072a821031078a440e200301b50222402c01030f0000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 475751924 1250 475750674 475750697
    0xf1e0405060d0b15030106030e0c030106210807080703092102090601030e1e07051003060605090609030a0b1f060e1c030c0503070803010609080a0203120c010626071e0312 75
    0x13641000355000306042e440000d100a103484100b03003420004809944280d2601074244515042d03000f24054042c1440340024003e07000745403440051040c51006410740b00046921010590300a20410640705002442c40303101d03000510b850040d0140d0741000354000809000200e1031352117540040b0218040d0001c80b0200680c03c03d2030307003c0c807030300000c02052904071302000c0c40b00d81800806200001560300d800c1100d10b1a01c1c030002c00380e0003800e24880c495480002c44e03808584d000c00a0300c0029030400c543c1102d60410240e00d800303281040c49100913005010400103400ca010321005900c0074805400181001c1d411610344254241980c001c401b4000120919400f14108002806a07940301700e212650305d504101002e0204191399010843d140d114101c0c0000588001c901c800b86880c161000340e444440240c1d55034094685504001c005900310070790444490640440c0c4000d40d50000b0031394100d1501c032451121080c800010894182c800010200000340e01800120340707048003440c00042902 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 475753174 1250 475751924 475751959
    0x60a030b040606080606012c1f02330109050a020f040806071b080912100e03040302040c080c031302030102070b070e1503011208030a110f1e0405060d0b 67
    0x3030156429a5041d41c2c0d00418003a10808001080c0c1290003400c05070710301e818203141520048069614840803200e20f0800c11001e4a510701490020031900c02c40000c4d0144910000755118080751040030342c60311401d8ae003660107074240000c0c060107080c62040050b40c1c0c05c041054001d4100038202c1c855699007000f03080711910900000c1c0c030240c240d00e4080c11540c108007000504402c15100c03250720100c6000e0140303001803c1320003200d84911003aa000c2950804080e0f00504008980561401007410100d8000109001200801c1503e10858007000114a00541100e100e40e0807103124045e0407040001c98000066031a8141c5d1040c40100003510b04512030355080d02410042c0c4e03a00d40070944005692a0902c0c154140744003964902507501d09562400100208290602002400420b000404a01c002c0340a8200317040181d460601c0c141d8810700d60b68418000d900c51028403051090300488442140c40002c1100c0440d54000c140c141003207440c0029900400e0f100800720360007480d460080d01300c034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 475754424 1250 475753174 475753193
    0x8070905060a090606121a060a0309020109050319060e19030c06020f0d090506070f210e07030516081609050a150902030714030f0114030304081219050a090905060a03 73
    0x810240d520b00c0381200021b0a150180c9080001900403500440c4d105055602c0300000c0d42d0700c051007031802207080802400140c50000040d0440ca03014000c145880c000e01c0c80c4c2c41c8818215500c211010005680040c0442d030702c583d4002000c140c070b210404a400c000c64451030b403080100d4017512005181c0400c90709150181c1c1c3c810341d0600d0456458826801c1880414001c003a40040c0034188118401038502000f040b81c5c094000d600c0200c0345139240c250f009240e56114000103d65001280d44058581c02c1040e641c404004001010100d4580040b54180001c10080c4044c040c0d1804181c005042449a0300581030040c130f0400c3d81503456807004210450f00010200402c0781200050f903d0030410b03c020280b840c0c5014030b1080060400c20b201d4440600c0c0003080c112035000140554107a080d41c0001e08500c201e034080740031480340c82501e1001042070401804c030304035a1329088828481000302a5214050400710704041484014104480849608020b51100c3c0007410143c081d516503841e5080b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 475755674 1250 475754424 475754429
    0x206091203042310080c0f09031207050d02070b040626040c08061b1c20030f060109121202330a02120106030b041103070c0302100608070905060a0906 66
    0x602e07a05242000c500e4600503001619206562074602c801c0d84e624040c0001d14042c11080c22400e0000e2210310340007509003035915256000b01656140c0c40b0340600c880c0942c100d10030680d40c500851159a181900000d0f4120407502c00c00505802d0a140181c19150590300c0700e21a10b40d40c5c0c4411001c0e03035101c0e48105640c4030318410016015000d051400192034408020300c003014000401401075a180358440c1a5010340040b82c8120f10f040302d07400317000390140100030351009820000c001000b03041c1c82200c01031441044550048c2c161030ba584401150350f1100e0344a07a110540d001c160403001702d030959081110180442c011a403000154040c035801c0720440043c2204408000428441e84110381c2c1d010070303002404104290700304064412181c1003d00d041c0300c0d0070241952100d4280d91915207812403c1c1c2e20900d105016180d1074620400343c00018801c42c11001400380d19110310f484080e6205140644101e840145a01400c00084000400001c0c0419500c0347d41410005100304150203050003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 475756924 1250 475755674 475755689
    0x4060903020a0c08100c0f020309040218030d081501050403020d020d051c03150f08031207021002030c0406081b0405010e1306140913030c0602030c1b061807050d020609120304 77
    0x80d9000005c9103030300300c07081c41702e85104120213a040c13144c9003680017064401000b0304580c0160b81d40b001003c1208240b00700300f515901800750070011722495401004051044804902e6201e194440d2001102d0302d220320300000754042003100c07181c005401d01c0d22500080d140718508860360010008840c450441002d0000c8001a4551248060000c4a0701d9490b00500b240000e1100c0c0c9810111a1902c0b4010095100d15840b80032000a48461080080d40700c1400c8680c0c0440d6a82003262007683c580c1e00500816000c15038107808176403c8500803a10003816080104541c2c242410031004484408543c0c174000c0c2d202003181042e0301c50300c4403442944003e200840c025440b506601c018404070700da00400e1502d01c00c100c0d82209002ca6000000502c1c401e41c00480103a40b070ba08c00c40301c202d460084e08032034621f101c2e5260481045800002d001d600a0049e010320001d41c0c011919801d40d140326034002e82d138200701d042d860075006040880160900000c014203109035419400252843c5030000d81c001007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 475758174 1250 475756924 475756933
    0xa0e0f0d080c010b0909030f03041505090106050a0b0a090905130b10031e0c0b0f071e02040b0402041d0c160507030308060607050d120e0f07030c08010c0804060903020a0c08 76
    0x4040b4001d03c074a40e1000400d9480350154030380b8218441d180d004000d013088941000100290030440c030b445150722181403019080140b41070a8642c0d50003007840707002d940d02a041080340421800001c80c103032601c522007681c0300304819041c04216005000094040c0a13005d030320020510006420000d00d501c5034087c0416000c0c51403940c1020004204284c4444103010b000388440d2011640701c070340d1001a100800312065817200c40038017450b01c1c7e200f03d80b0041d00d0000214000502501c0c6c0c0c4011039504d6008607000e21040454100300300c12849603214841002201070b0241d00351190031483c2691201d035114000d1b0904040070b00c3e0313110310043e020040b42e0603003003a1028002c141e0810041508004240c61441c02d048079641c035540d44203100c103c000c0074443d01d402e44151242098216403002d04400d015200c04000340c0c1c06056454080b40403c0f2140a02e100022400000520450900350140e581d4030f140c039200c5861703610003840307008070640c110f028425501c80451032400d09000181164002070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 475759424 1250 475758174 475758187
    0x20703050c0d17070503071b0f201e040914070314061905090f011104050109091b050a0e0d120e01020606011e0c0b0a02030108160305030a0e0f0d08 65
    0xd0411160030402e03010b00c8007424010314112540120140d000007142801c5a5948601105803450701c003102c092045100e8044402c1d04001d14064180c2c01184541c0912001c03412039810149501e900c0a9640c0e0008000700c811042d01968042120720440c01600024040c0825190f0b040001007000841d03040e80e00c076040c01c101300705098401245920311070700035007803c0c207024402d17035142903001314078804098890b00032410034bc0d8107001d20640101c5400c003c1000683e00f007400022a0024441c032801b1402195000404101c907014003c1107445103c3c82a03541c0e041c1c0318040e500f0742c1180c07002c0010800003204441c2107807114400801018051041410304003a4000c0080654003140031480c1103400907070a100b2181d8106070b00d40c0c1c8102c041018000358a00c401022a81c2d0404000301500040b140424810314110550046050f070f5075104c20f607504600c640c50740e041740702103034440104a0362041083c1d5607100d1040c56460603210004140c80c03100826038001a90101c4002400e0f5071540c4002005c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 475760674 1250 475759424 475759447
    0x6090c0d180305120f0c040902030601030b040c0f021504121110060603050a0b0415061209060203150f1906030209041d1e2d0309090712060f14010309140102070305 72
    0x459481070724091180d203245400c075408681b40c0a50700c28212515004404100c541c1c9c003c0c0c215444015020303200b0405400c2c8031100514541401240c00054064040b0300710408011101c8a4401d68204420807507184041e442181d581c101000c1c000101d0081e1051a907170150140140001070109640c04140360800c104400119005000c10328030691a0410031400300310102c14082c111041401e02440c1881c2c000e804002811641c000200154800000c0002c0040c12107048600071600390f440b5041010b0364418401c00d01900641c1d814103a2101e030040103040c0c4607400138003440c1d1000d04003081400404840300010300c02c41030a0401904244007900710791540e410480f5007200444c004260b00d000040c00c0300000741040c1024074102c00e05164402d12480c04004071495558054003c1c0414540040c00038034244640290800460502c4d1000034070140098005040e01c8070140b11054044c1c0b03200041d0014000c484c0704450221130800d190f0804042032001e44002c3d406600e459503213282c140013 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 475761924 1250 475760674 475760707
    0x31e0f050f0601020a06200c0304091a0303030a0e0313080c040c0216120f02030601080d1b0b0114030f0102031302030c0d051e15240906090c0d180305 66
    0x25400601103070104221060780d00181c0440500d40100b8002003500c030001110505000103405c0006010002811551100d0b001000780b0461302e804104000d1040c501050401028543c040240c0c1076206001241454a15a11018040c100d80c03013220b162418030b20404101c108591b0205c8400c0e00710f801e01a40d581060b000317104110000e0f2020300454a914070325604080014064480c840140da661041080544000c07080020b800400700e03042d03983e41e40d203440da035a0031030f0900c01f00003415040b81d544840c58200800c24055445000141240e00f0007021a0303900742942c0c4056494401d2114000220b1002c0c40210b00a00e51200d41d5007508003980181032600b40e115110b98020340d00c40c404800411004599060040c014114042d69030903a4101d00d4684040400c400341400d480c0018040c942d600422011008a07030030340484014208101040104502212659008544140041e130036014400081c402c00d50f080d0780020740304a01a8050481c504c83c0d44080b030115500040510b0720320111078 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 475763174 1250 475761924 475761931
    0x2130b190323100b030a21090605130b03070e0a081b01020313090b0a0315050601030e03031009021b010e0a170c2d010203130605090a0203120a031e0f05 67
    0x1514070403440e030001d5140d90b64074003503071503c2d8106642d800d4204a40d0f6051102e403519540002c80c211107001c0000300c007032001c8501060500812500c00d0300150b0b0038000c80613500250600e510801c1c940d03241c90004911507100070303c08810021602c0d016000303079a032440c4050151003144018488880c2122803041d88140c02c4264506560040c803001c4035144040b003080003516459080410b4450a08001c01c0114845400003491240c1d03025500c0c845010300d90001c0d1145000340d07010711910b59040010b81d01e0f07110541d4085c6800030400030a100c4884030390010103903c40641c0300108884d0261041600f1611210000703401d50b00a41c0300c000038800103001440703500150003c0d40745400c079403500465a030800f074008071b14050701c1e1014000b004064990601e00c8a83c0c080002c1d50f0300c0c941044198801c05180c07500700c840d1031510700441d03000d0000043c61200d00354090002c001006400450305025040301700c41c042059101d903003600c01800182c061000000800341d0104100c145001310109954008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 475764424 1250 475763174 475763213
    0x402030a0209090a0b01390816050105071b081611031b031e070e0702031b100e010e0d03020f07020d0b040605071d1221070203101802130b1903 63
    0x1f103550314160b070344428012090026812a080c0c142c40a1601c40040e014103150000da024a05288800313002044d041184500c119a5844600c5400c41025070880c07800b071130002d412158280040a09005107480190049000e02124620916003030002460068081a00c2c00c4041a0b84000b030840c6c1030030441100d81c002290200c0304400002030b44070391b0342c050610502100d000010085a1036030300174400c0340d030654181c1d46034450350215810b00d666682c211240320f0007110714001c2c54030744d061410300c948003c4c11082c81c05041c007801c0800d070460281d0403800a00954800800400e00180e03104008000300340d2095001c10100d1505051035130840b800208414280000c61100d02c80401002c000046e007204211030524270003043c048520300d803000c000182c201d849005940c00801000c01400b07042100e01c210210f07000c03520a00c0250f41944c00310310000c051a40310070381400045c0f0707080811262800f0140000500101d01c0c6c5d001404040d6400b5400c000081d012a040c001c0c030090040210341d11136107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 475765674 1250 475764424 475764467
    0x10e1b040225030507021008090f0106060f200d03060f1d04060f020d110c070906080304120326010f0503010203060f1e090a0c02010507020601140402030a0209090a0b01 74
    0x1c424100c40350045054898000c00105100004044c0210207680800d60090401c050051102c000034215020076074650324544a003c00341c81000d03105014a1080c2d441c99519290500c1820801b5215502c01d501d5554a5020b21550b500e4440000c105101404803942c1c0e02003004c500e0b0403141a20140b0581000f5822511400031340140900c1c007400b2600300350f012100085d4584801e00e01d4001780181c1c039801008074107140c9150303070a0301d0031005410088000340956003490345d10424101252403501c13a007400d54001380407c001c10951199191003040c0a4200203032209416000161800030001c0154020442c400040c0710044011717004c0c42c058201540210303e503007800d01c001703540300b8030554000348601d0341988510300e500005212503040c8200079100d64001c2c03c01020040113801c580340400010340c40c01c07000403981e41c40090b4150403200b10210040010000006010280d4001850000030755000c110710001c540358035081520540d100500040c1d071034080000142040f004000c0311404011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 475766924 1250 475765674 475765687
    0x515030a020f121c0e19050f06210108100b09010e0702070b030a0c0306060804020d0f0203070801020d0209090609010308220b0a0e10020d1205220803010609060c32010e1b0402 77
    0x5203401b0141950000c039040c21071350600c200001c1c100d10440c00c1e1845180c0c1840b60300202d0b40c0c0d4100c03400c2e0594100809a8140b404a00c0941080710241c1c101d85074000d5136440100310f83d42a86010982014251064441064442c0e41340d002582c01540d00b0100581c0c2c40c00c0c030801c0903074917220b0500034211502e040a60b030300300750300028207100e0b0802c0d010b803081e040980310004540d420448040104070450003503482d00c51041000d0b000390089680203000700b501c2c4000502900d800141981600c0d80a246581443c008561262001544c420848408150752070042240c81e42c0c40701801110700160382d174808010703052090003041c440805140e415503103d4500c980c2d51039040280c00c030348442d0354040020190f8a00101c0c030b11301c0349a80b4074071801d040440c52200500103005e00440c16501d40d030b03c51001c0340d035492004961a40d02e0f9440900001f1402000660240d1014040000340c0d440c00b507000355030000d070400542103404010707400606500049080310003500c0003048400489086404508111 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 475768174 1250 475766924 475766959
    0x12070809060c07090e1b032d0102090d1119050108010b070f0c06030504050706020d080606220b030a0e0303090c010c02030717010207060515030a020f121c0e 69
    0x991030034030300c141c0d404109030154140030040040101507001013800200b910181003900c4150b0341005c000309800c440040007041c01e000604414034444003485e80d07002030340b04920741c0c1465000381216010355001c000c410486e0f43c6110720410880c0c001e1101c40c181415101c01c100d031030009000c00b02500507036480c00308a507a8114481d281140c2801c1015513440c040ca26040030700500052009000a011400200340c0031b03410750140b8403c51290003200e01f41030700d4070350903641d41014a9030f150000755070070009035040c2400e00180c4a840b419003051101a40021528401403469070400c900402003c0200141042a401208401841c1402443c61410724001d495154071101500c5070610600c0501c140464908001100c02041c9000040b154209d8602c51140030758031140050710345a08003008614409180e290318107803924020020300c06844640d0a00006000d080c41b9070394041010030b8030f152210000e0083c00e504454011081c41040304d5968047d0000980d88801d50150585000344034255 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 475769424 1250 475768174 475768177
    0xf060d080a050d0f060f05120303011e050603161b0803040b09120703031b0806240f0a0e030d0503060604030602090a03120201230624070b040b09120708 67
    0x2590403104181d52440210740585451180e0440620200e14000503076051425582c0204143c40500044a01c81c59070340041003200a20040354044581080004000492000c0c0800e0380701d01c0105010b000d131135030b94800a105900211511f8060080704440c214000d613001e8429400000800d030f080408403210f071580080c0d03001c01040107205a009a01181c0c68000400c41803890403014000c8a0342d501e002d01d0300030060f05840b85402d41000c00f9040c600589030044800910903140074084840c425200c0c0407400780c004400c10121283e400c02c002c0c2e4040300207240002c6c09490b080c4d0b00e41003030003040401454900f945212005040010900070702140759213207000c503012250440409a00c0e00240b80000f500354196900040054075240b8030a014030740c041d00078070340001003002c0c40e000900d1400705200c2c0c1d00c2e00840d02e00341c0c400c025214001d217107a94031031a040c4000c40c040900342041c40d660744030450840c0550b0180c58000c4014100b1182290402c0100b4400084000c0c8605107211640c0e18002c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 475770674 1250 475769424 475769449
    0x906020a0f0e041b1209062a0206070f0e0f030d0509031203060904080a0e0604060f0807030504050d0c06060e0f06150a05030609130f0c0513020c07121a090d080f06 72
    0x401090203c42500003495801c1b13100701d56000401045101d4400c100c01a28205a00705040020010300035034031a50f002040caa441074807281c491042d0400e031072004032562800c801d500d075807002c64200c0b040002c0e00c1c02c0280700b0b10518540c803459a141030450400d840c046008011201c40503082003000003d4a40d80485900954440a10380d110030a400c003c1d54417003160340c2c046800c05800b00c1c00140c0c0c40e50140380d0000044a0f5140c0300b40d0f40d00d50f148100e054803022038010700f15034040380008141c98803c0c07034952001d80c002ca0000a145480d5038503101010f009840821100c02504103210140c03410328000104682c14800f943c3c6440c48800d0b0107422400020081131251101c4000540703080e0b14104040d62460b4401110a41c00d081480c180c1d000881c01d00405000d07054070360700c4000c004040e00c200c4000b15400e00040010900c0c00c0c1c80020307118507400c02240c0368002c0c2c00c0d9900244121605507030048500c08040e00d83c000085c03600401c2c18100809904104030880d007402050307296003031f06801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 475771924 1250 475770674 475770677
    0x80105011701021309020f04150f171b0d150b0705070501020607120c0309120804030e03031303080a020c060a0306080c04050408090f01020f240c0304080d0902040906020a0f0e041b 79
    0x1c982c01c50f09487c0c440b50084d6840801016a04010802c81f42d0f0b10076000388040c0101d07240c00045001c0c034424001d225104031842100710b0044012000f04d40d02200141802d0201c014021491901902d50441c0030940d40e8401c0c3d0406101082c02d0303080090500c2040042c0900b07100610071880e20000082a4980d5604070707400607903842e081c1c6282c00b4400e4007da281a42c1050f091000c0300c000c042d00074460403007264250000341c4802d06860040c5408401c550302e031200321032400010f42c1184c5641e0201e500c0340d00e9034030640c8566110410320792644409011003c045840008582d407600d90300b44d080000b501c4281d485140750808002c00504520141c82a0040581d40f0980c14944400140d1a114582c80c2d003c04170320a594507012000e9092601c0030180843d11030100058407444080b09240c00140c034004c201e280180000901e80c02903910003460540000c202066415058071142c003240d00c1040520002184d0f44181c0203156040314142c101918269402c000c842e12180d814401c800b900f011500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 475773174 1250 475771924 475771927
    0xd03020708040902160213050106020a0308060d0b010e071716030c1701170c0315070f0509040f060806060f03060601270602010b1314070818060108010501170102130902 74
    0x10300707104040301500d0280c015803c0440d07a4070380380c00c2c065900e20020701c0c2c101d01c0707004031701403041480945000e4103048980903001031401154030342d000e807074070342000300416041041e200c80d1902040007550224001e1150031003801e080d05080300001e2108034506492881c102c60801881241428120600f1840c14103140000b0303100328480c0c084429260015902410303610080010414001c1301c1c01007030405a1030800c540d40c00a101040c59141d40120300042c16001c03611000803e9107000310809000c00546e0b103862032410700301ca0300080031a403505800c0d8019950f00c0b03c081c041100308001080d0048000c903070000c40d498107440000d0340c84c2002000303181003080000207840b01104c410b00c0001c80031801c41004281c591030340c0c0020b000300680c0104920400c140341e040c140140c0305100d003151210204010110076a6020310aa420110103000568118007800c10314900c5403042c040c1e28082c1c00480004503495140a60210140015840703a407030310b0348100406403c00844e6002c02085030121a00903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 475774424 1250 475773174 475773187
    0x50d020c0312070207080c041514130f0203040b06030a0b0406020d11042c010807060804150509070f09060815040c0509040f0317040807020415050406030b010312030e0d0302 76
    0x2500714000c030010b0b22181801c200a122006030041034007415121044211184900c440080000b034a01c0c034201c40d85640c007580c00078006800d407030004685110300a0032940024400d541004110740c0c8880700b4529035030f404800d000030412506c80d0203808c044101c008100c3c1c0000d94035500b008000144c0020030700ea07030004034600703c0000307500101550468003e045483d1036881840b880c824010041120a00001c01202907260924000040c10390340c13080f00030140541010303001d450030034000e041134803029030304147c1c4500c00e809030182d03a205804c0c610203000358500c0c00d9000e644056185c0c1100100504006061141000006c2c03030f6072841c1141c010f090607503101c50902c410454070765040307e6007042c0b01c8400c0209021904241d030105611903030310b81c0b1000c400318a1200c9040d20a8400070a2401c003005914050320b071580042008910b2028140d000c07542d104002000c82e1342552088400001c918010028041c88035002d032002000e80c241408000082d000380e980b1000035500c13a00a0680c0414207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 475775674 1250 475774424 475774447
    0x80f0a06330503090a0f060906091211122d070b220c030b0711010e0c01020105090a0b010b070804090c050c0d020120360111010507050d02 61
    0xd40103000828071070100c0078411014070311144074031280c018181c0040c1ea405601c070b403244084910424640003e03088800040d5680c12141400000a5410310741b80c4c05d149000c160304e80300b03010005220b000003000c0c070b0314002400742c50201d0304030b24541150003940c2071712801040742c0700312024000d13610205d003805d001c0c00e5459002071a81120520b1407840c0415603004220009540a0003240c201090b15a40000074122480d041e41c04040240010940c2c001000040c0348410400d40221890034900b0503071920034601401c550310418002034a80c401400c0c0051542c080c411107401103180b0b03021b81941c24080d124a585904180320700300850303030001541e00600c000388040d6005020b8601050183d981580c070000c00369040504011094051030f0b1040c065180140b0400d107003000c4001d00007809408003030407680a03800c64400d640c2c0707414101c508001d801c20810a1401e41c20000c2040c9a41105034400051054803c00803281c10341c1e240c402840251034002040d200d41103001c1c000581d981c0680c0310b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 475776924 1250 475775674 475775681
    0x10b010e040f0912090501091a040b0a0203090d1518120f210617060f150d06060f060e090708041104090f0c051009050a0b160203100b04050f0601080f0a 67
    0x20103407101d13040c0c00b00c0c00219540403149004036a4241e071001412a15440c2100380d000d403280c0d0303401134210204801c1044010240203442d48500e10700650342000b0906002c0341919100000072605250103040d807444c03850207442800c0c20301e41e160703414a91040080d130340c410300c041c4621182c2080c00108801c8000442c4074045c0b001d0089411008041c20440e000c040901a004034041e181c40c2002d44410501c00e00d02c0016041d21a510400f80c03040b464940c96840140b0a015030800358104050b0310981300420340c24062200201012669003803c6460304600070072282c0d04852442c4a10030a000740a000d40c0d05c00300d803d8215401c500400000b8142c1c43c00a8004e002501005011800806070a024031660441c020708131241501c1d070310b0303d540c8120320071074007402107014031540301d01e1000e01409030b0b90501000d001081d1141940140c140480d40020340781801b602a10100e00d5240d00c03010440b818140240307500031098002040c41c0d41018000070300b0f130f0b40008010003e82241350300021140d254a40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 475778174 1250 475776924 475776941
    0x60504030f020613090203010312050a05181f020f071406030a1116051510080d0503040c17060406060605040b0403080d1d0c0a0f0e0105010c060b09010b0703020609010b010e040f 78
    0x1300000b10955940c1d4051000c3d410910080d07691040300d013403103410180100308403040003081c0c5d650f552600755040750001070348400d40c2049400540c0c0c4240e890340301089102110400007150020301549654030f4110340b034030a0a4100580690080d0100f01050701e0ba94156600980d60040200b036909161700c0050181c01240c0304420240e1a249c0c0030018041d02240c0052041404a000d1a80f40d84510110a08504a115940d44c66010416440039103225030081e5800520401c550111243d07280001d00300c28182118400d803d81002c0d060100308881d038802c0c0401400d15040070f03802d0030314040c103004440c01070b48805803800300d00049070800d0001d9540321078030720300c00e0000050140c4213a01c6603d540b5140c0031000c1303019035000348002c078011594140c49000c5480c1c0c194280f455030b00b40307001150820a0301404844184c1c980c0400c1368181c0c1c44600703160281580c045540d88460442c10300900e0104047c0c00070096900d000c0103c0000d99000e1002c0484141c15070340450440b1496130060700034820a03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 475779424 1250 475778174 475778197
    0x80d0f02040f180608074103060a09030801050d0203030c013314040b241908060102120c0f0a080301080f19030c0c0314060103150204060504030f0206 66
    0x250101d05011140b194030181c424461035684444481c00d4004103c0e07205000341070407030b4400b04042000111641e0542d0705c00c5c80300c0c0c4940a0001d00e000c0b4400d0120210303c0240348860070541c0031443c03424100320840d4495000360701401100d00986000d0304d108010b001e001c1c0100310701e250003001d548003041101d0301481c240000300808082c000100d034640c1023204050304040d40d0758144109102c1c3c00400c40d4241d0b40005d085031100540703801044000c2c8455030050303402041300111381c2d1003106c5000100c104d82254008082d03403a0400c580c0111540c0d4500d075010203119040c2c0520446990000e03480281d8000c0b00200c9136034800301e01103145015401c1c0c3e501002da21a009681c42004240300203913048420940c12110b0300c0c04855019922000490055004103a00c0054007001c03038402c158410045010324141402c907a220f45991440803015040400d0640c0701d180108100f003005452011210042c860071070603c0d09020000340180301c0c0d4800642201e107582244801d41d941c0740115000103100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 475780674 1250 475779424 475779427
    0x30602430f050a030f140408031801090b030a0f0f0c0230040807081908030408030411061821030a120609050123010801030201121806050a0f0513050307080d0f02 71
    0x82d1301d030080c4400120030040000807141c88a40144074202c0003960f00345c032640b2020b141004801d0f843c60100340c0c0c4910a003410003a056900003140d044d2003000354020004140e01140100c11501103205031070795171000861940c03070594070f01c00c1c07980d01048428030411000d00f07101598443c01c0c01c4200b40f4051080144480e10001000a02460001018030032911040c0607608214020101d03095022414000504040030070000900010032050046900a100d040d004030303c911148041101500017000914003440d9101c6520f4691600f060449100011640486130151a2520351a00c0b80030741d618550500031810600f62403030303c0030b820001c0070700309080c2c040045c2e41c0d44040c214020f141e00392580440d00d503012100d02e015446880034905890f01a102c0050907200c0741c1055000340301e2105110706184e5611001d400142c41030041a0003a08a2040441d0b822444616030f421580080c0058481468048910700010408820703940c84682091303442c0c0c0c0f03400c0d00e246e012010340510310510b0000c0c2e20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 475781924 1250 475780674 475780693
    0x708030a0f0f18020a09020711060a0203040914041e170d0603290702010b10050a051603180501030b0d03050c07120501090b070f02070905070507020a030602430f05 72
    0x343e40852880c02d00840342e5446565481e5214412841001d402610000ba880b00348011401c0c200700800350a102d51040301c2c5402c0c0e070341c00075604550442e080f03802007645440500052041020900c840e80396103582e00c0d089011556a84007481d1042c010201308000042901d104901165122400075a04815405c840c540150a01e00052414422000086c400b81c4081010248144510390100c04040d010342101040688141c4140e040040d08400f00101001318244400b20303040d1520400d03119032500c2c003010a20f1002203041007010f4000a040500e81240010070381e449018a4141541508000341d8403910a4103041c00d01000c0c0d0809044000044c446200708a8154800c0120341d000b030240301100d4841c0001210f40140e46461700005900c40071041c44825960385c4495001051801c00c20300c0d1407545d0b80844c0344d43c42e5aa0090310120307401f141402d04519001d03410048070b154014450454983d0950500c284c501e25541c0e0011410b00030450000c100d5410003070440141c12400b110a40c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 475783174 1250 475781924 475781951
    0xa0c030b06030a090210051333020a02040b0312120c070f0506090c010f02060402040c110a0804050405010e04021804032d1707020a030e1512011a0708030a0f0f 70
    0x1072601081b1300a5028002c1110b0240c405c000391400e01e0000c0002d10300851030b00b00c28032428020030007000b2426a20a81440882100654001c484665034018203000c0d886070041004480004090324042e80007084000d030700365540005c41d01c0801e81074032120059121203c00140c0b42c06403420007000308001180600a1040028807180b24000117812559480c0341c030001105d00c3c0022000c2c400159010300701090045c6841d0304455007007101850069455085d0784211450710800b10400e0f241c84e40d0004050260b4105802030502401d0080312640c11b6041c04e5009c50b514580002c0d0b00307140c150382c03040441c0070184100000c6840b188074a000c1d461240d802d1754481e900e0024012024041015010245500c12514013014030400c00c507005041150b000f501c007640c00410b295000396001d4120140701e0ba080030b4850181820110110000e002d0f981018413030301c8480701280c110b50b49413409100400020b82180102c03a0311203196180410032900d07081000d03000d001106214107156043c00d40070345030315 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 475784424 1250 475783174 475783181
    0x40203071812020d1e021509090109060f1505040503030307050d201b0a0c030c1809050c0f0d0b011514031501140c06190b0103140a0c030b06030a 64
    0x306140900c1c490181d803140e01c0707a54440062070013500240c11000311070100d1415002c0280f8a5088225404240d16035800165802034003d011014017a010582c002c80c0e0600d2900c4501408200700c0070030001d4100b44042580b2080381c460503a028010b006010191391180307003035600424000c1c08403a283e0402000c05001d9800041c142107600d07141520040c0006250780c0c8100070248194851890141c03c03078508841440d6039a14050980309495205000a4484001c0c00055000e840b0b000051810142010b40c11220007502d00881070030040704d840440ea02040c10209035500300c074500c3c20810000040b4400420200c0c002d0030740030a20000084219030186e01c10080c079003c0c1d6495000c144641b81ca60a1800300359004d21030078100c811802d030554081c070000c1002208141006060a0b007820805180110407203454076020041c80040114222601a2901d000d000b401c05000701c1e640c0d0700d008a8418030040025140da074413080c06041d8103020390301c5603e0902c0b0151909030707070b0729058010f031016 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 475785674 1250 475784424 475784447
    0x18061503010e071b020906011803020d06091101020d090510091502070503100212040f020d1202010609060b091806060c070617100b0d0f11030a05040b0c1908040c030204020307 77
    0x11407090181300f80100112046040601d600800c0d100164642d000119500104500d50820580c604580440540d0f1048030183c0b900d44500c0c1c001c200340c2900d142c140315000485007030b10b06650280b011140e92070340280c01f10080c0e800659100c0c1c002420100204d520310641c1c2d00c0402d40c0c8501095101c405580410442c060b1041641200c035100c41101011049125030030003c02c13910691400301e000a09400d17040c4141500041c82d2880c0381392a515800000170030b0060000150f951004208003043d014041e43c3d00825404500c0c0d8288580400840ca05603444150408900e500e640000c049580304020750f03542e80020004c0381d804c59115a0040c046072440502017108042c0c0c2c00026426030000c803490380950302d200c4602800c01245584120140070200c0c603940c02942c4602002610f8020507000d54480c150300400820785040c903081c6205120000381c420764810700100546007070404101902c01c0c008000b40341c000003565507401c20b40100300c0f10f9000294098000014080c2c4140e219500180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 475786924 1250 475785674 475785677
    0x4030b070c05010c020c0105041202060c1212010608160e01030e0706050703030b030303010803040e041e0c05040b030a02030615030304050604030614090109020315040819030f11070218061503010e07 87
    0x155904e614030a0745c1e1400441c00503400610b041005005113844044d91200440c40a03003540d0600a1520321181420b5840803086080c41c808604008041d140717503050303801000346e400d004141d0b04000804120001c6e92071035100902828407080c0d151644a0380c00500d41c2115902900c031038940390800141198071448099000034200f45c01c034026441c01004490480f5802c100039442d05280000c1c0c100f60f0b00c0010015105025442a83c108144504604034000d510078000c4074040c82c189000c000480d190f591340c80b802607104401110058078000303411078200c1004012203008030bd0640000c0d02c2c2d03108680207580c200c18080780c00020811542c0000c5030004589040c070285039a1040500d088518501011303606a000902d102c81d108045c9801a81044c040c003005403400002460904080c0010640d90000950350305c1c0c001400305492242000981e80301180d13030314013040c1382c0000d495041100050408004080046080399640740c5407030032510000c0c0c0300e054880d0380d00d225a16100108907007410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 475788174 1250 475786924 475786931
    0xa0509070501080907060c0c08010911040c02030306011706130e01050a0b06070506041b030204090b01031205070b0f07020a0c15020d030e0613020a080a110f0f130b030304030b070c0501 81
    0x603042d0b0182c80071134801e9000900401180c1d03e0700900300d4901000030720590b120b180303c40011420f10760078050556214092040d8003050340e01d1700b0601007100c031127600000c11074009100380410741c2c3e0f0061004c0814003010083c50542e480c0d0400042c801fa40b0340031b1000d0303d6841c190f00242030381d0301900301e284202c0c8190b104100411101e018040306220b540f40c0101980c00410019002034220300b0300d00303900c0481e4445400803a480ba40410201c0d0882e80040c2c0700000040c2c01041000605800c0b442d10700024601f2030f040c401160380351600541c0c040c0080540c00030110000342e03074034402c03c800f002e0583c02040400c2106c0d510580d28201915400a510060141182c1070789030710f029006212407418040000c1013240d9520b035403107903130392862881240c1c800f00328500010007c2c4104200c07070005010b40503070004c500c11201080030403410f01441c0307401802c540310003111540c1d40c40041d00c0c0c100f0752180c2c0802c0405801001a003544516040142a51002d00a0080e1307260b004031183c5820b48220000c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 475789424 1250 475788174 475788179
    0x6090903041a0304061d030309070504060f0e060d060204031a0109020f0a030c0e100504170d0c021302041d010602010e010e060114061b010209010912110103020c030706050a050907 79
    0x19403644240c2c0900c0c03801c4480b458881d50382c2101c10000b1680240104e40c0010300c0c0e034005c041c0d030901c20112400c00c80d03e54004424004007030824000d050041c041140e0030440c0900c0c04000b80900c1030304d031042c4075a15070344000007600707525508403a101c00c50f131042c0d086503200e0700c0e842e0505483c40f5611406c2c030602c91007000814106110701c202c0e44506141440c103814101d0a100440117040042041d00c20040031800e0f000040e100c03142010103082d125201d054032541401d84c0c4c42036142451243e0742c103941c0290040d8580383e412000004c03410ba010b480144014038000d803000c0203072107250b0110400d400300301900345500c041681840c0c140ca4565000780800d0034400102030907500c08202c0c60106410180041080b004286600712a10790084c100a04280d00e0581c00d208510a60400311141e940000d40c64401e503a0084502d000b40190a242c0c0c4914401500c801c0b142a0090320f01905241e03000841d8050300e40100203803850582c1c04003003480140b4215441101a02080c0c602072854418203501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 475790674 1250 475789424 475789441
    0x20f1212190809191101030b040f06060e0109030c142d1503041718130b01021507141605030a0f09091118040902030a0b0702070605040501020d030908041d0609 70
    0xb80080020120002d0b44a0b104c140c603000c0c0002030207000c0606044d40c81c0c40b180c200d0b84540c014140c130b0070011032001401c00d140c040054000011515080c2c104000001e0600000324110804d10540b00640494003040c4201c8001c903501c001002802000910141003801c1d2100e02c81041401074041a5040740c0d400801d071035501420301090f80c0080405410800b207040c21101d140141c1075040f0214509120342101030003007400c0c0140b000c446070980381c841007044e06a58042020400264041c0c40d01859840c21880050200b04000074a966540b0b00049442c4991001a0005442604101900d50340c88030403602805451036101d2600218011200000d0100c0541c410941d4072990000883c0c540108043d00d600510b0100d1074041d801a0798060410150300e007000000840c512501d0400300c98241110042c0c0340410a5100c0c00c10007004200900c0284d902141c0c80100d240c9a06000c102010185001d000c180250b40041101c1c4075840100300700c074100d400c0d06501a0b80c044e0b40b00c031361980b10340c0e80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 475791924 1250 475790674 475790683
    0x501020a03051b1501032a050303310801050a0b010503090604061e05070201020307030606020d020c06090d080301170111160807030909051614090307170f010207080d0c0c020f1212190809 82
    0x34141d4160801d100318500194214071032a20b00844080f01c4807000040001103650000799081503306030754642c10032864204510859502c14000d091440c210320f0448001ca55a01e4002c00041145440c0c80c0092600000c040c440c848018103001c00388607a2600101c024000e4008a48400019081220003e0003c1c000308000340f010109a000c2c0029942c0402402034680c000300c0110f070040c0000100e0004a003880b8065406085183c1460352032031070040d0780703600b90307110f16802c2054210100501e141a02c0c1d0449001d02c115880038145459001c40d0900f50f64111080d4400b80c0c0050503d01042104500ca04135031148201da61641185101d004070000c0280c010400031030341560020070f00348004c00c42402030500b0000ca0300304072142243c03811466400ea800c004003c40d0341c120042501c0314403070058084c0c0340340e07402c0f0b80c94140c040c2007441d0001205400d44c450b409000726034610b240030451009000300c0c0c4444003004140d642c0c44814100c0080e40303110340c0c40d240c40090510f501142c0001070204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 475793174 1250 475791924 475791929
    0x1406040602450a05153115050c010606030c0909051b0c1e1e030705121b0f0304090507090810111204030909060501020a03051b1501032a 60
    0x301c8940040720003103100e215036000c40c2c1c61680d11480c1c581d8000384035620b9240d995a0802d8a000c1d141d10b902a00492180d0041d41c0003801c0d032041c19114000340384964100c07000c000c5884450079010216545141502c16214428032086294209400410043c0d01a044003044400540d0b988007081c0e580d0300160229001916403d106035480c0001c19400b001103806411020030b440142c5004042002174090f0241d000c8001c000e041e005504181c1e0350708400300101600300d040002840c81c19059135965529454012210801c0541c00310700300440744190403040c1d40d044481021948058140907030702e43c1d03c0e04603214000003681401e000510f818403454501084a0040d00100088000c00344240083d00c00c000d0220103800080c480c072040d20341410341150056003e42c0f6140403260429600000f610700a4100c1c40c1958040303150600000e62000c2110380b102403d181d1244000d014004650401501001980e41551a9400030050040042c0407100d00349043c05048500905403010301d0b40d4026a2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 475794424 1250 475793174 475793257
    0x140f060607150c021504060f0f02071509060b060c150a02070c1202151b0708061e091204080d02010c0311040608040615061d03010212131406040602 65
    0x500c1ca845085215820010700f601450054031802070034654003c0405004507000c1e24a40e40310140400110307540c0c4100782e120704603080e0552034810300ea01d61500340b2030000703841400039981c5c04810061003080d40c411900d80100230030180d5603002a14115558007505031002c43d500900e20049048400c9034401ca45007603903c100080c100134500a04804001c20301039050381c00c4440d8032805480d103480080100881050a138069030160a03d4005605d070410b1a001000c2e035601c62401c2c441501d885400d80c400015880c01c90400384d03a10104058146100380d401c04031143c0c5d01113004100c0c0600410003400707400a90b0300800180d50056821000c1d2800e02d820784409800821060002c01d11517247c80d41d0107405801c2c00314000d003050b01c440d101402643d000c500020210070400e8441d0103900002c9140e02c0c0114001d40c1000b01a0050070a280006480700d071405c450b0265031000c02040f0300885400c880e9030300564855240c9410000c0296000e018030081c90b03009241440d14031054200b0110b484101c1c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 475795674 1250 475794424 475794443
    0x1509050606040f0315020d090b160804050309120a05010507050304170306060306101116091d06010b090a030f0b1005010c050c06090f060d060611030406140a0504030204140f060607 79
    0x854a685c0c0350600c5040e424034a0503020464041c402d9000d0103844801c92251009020302e29007008a0b07c00040d148461008200c1c454081c0030110700000151801000101da1080a5403c0186c1c0c061900000741001400740d42440704210034550010091841180110300d5200422440d064510451004a542030b501481c00d001051445c200100c2000c00088070342005610701201c2d00c1c20324500a10301c00c5984881c11100c40a01130b00703003c0e000340d28005111144800c000705940310559100c20050081071908180482c028a0966880c0102b1000f51340100140301a41000d0030807400d0828100c0d4100700030700da02c80f4001030700e52143c3c00b40d400850304a800f41c2004401ca400b003001b40c0d400100d0309540100c0c440c048003e6a80c5501c02070091100307035907002503058a002c038064804004216002081e400038401001903079000300010950218080c0000d44c2c4002d241c80680e0207002c1c0b0381000e904030b40f5004410700e803448801466800b4040c07802c0120420368410040010a00c00e101d00180071581 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 475796924 1250 475795674 475795679
    0x806010c08030a050402040207020d0c03020f0f0307290f03011d0f06090c0c01020d140a0507080406090503040909060207031106010614090319030804140c15090406091509050606040f 80
    0x10f194006508184001c0026161018640000301e07051117280c816582c010369008100214a00700c0c42940d500076040c0c071640c031110070b1000000e86501040c400e10004d900d00940000350780416403080400c0110b1290119250301c000d6014001c0c2d0f4109004240214640e848800300030701000200c0d03845000406205010f076a907000c05d10400d0f40000d030031540200020b100c60394030507600b80060300c2c96120111001803082075010610320600b002038801d00708603283c0030610a4450b03105082513480fa03003120012034455214034203545148a66803003040c40d20700c1e020f501400c00403260000c101c110702a6884412845e800500c040c0c50b05820700c0790501040101100900000c6240c002c2e0010310001000e59007000708160780c4864070780403c4070440000e035440c0c1c1000108101e6540500300280040000e20821402d00b012580c2040e6001441d01842ca02003503850242c2c2d00c82d0001c02c05032107030302024010b0200c003003448020059240204a0120300b040c0000e5021708113030302500c04442030742209200b400d2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 475798174 1250 475796924 475796941
    0x18091b03020706140c0a09050402091c030c0c0f090509010b03030d20030a06080f07060e0d061805030a02010b0105030c0f25050703030909140123120c010806010c0803 73
    0x18000603044030015110400032269906a000c11482942105c60f01303591403040a50081224855821aa202d60710622241480f0303102e81103540d599191034011001d03a00d0450800341d40fa5240c4410060600c14030000201c1c1d03003014014444100d4000c400d083c05140c0785d014100d400d90b4903040100e40c00d40d100340b10300080d0750155004051040640512100c1104902c400c0b148280d00071200c03017060a44030101004000810410004e0260040010b0f040071402e0440041c151116000a58803d00451a1001c1801035503402020f103600c00d100030b003802c441a440d2668a1780c1202c24054055482e0401200b802d50041040b00e103d021801050352510091008400444d0000d0340c0450310407450020b840c0320122600c000d0341d000c0303010300e00401103d803861600030f12912490308002401401c0000e4940e95207040015581520580400d045403030180c80c03440410700000e07060781640729000c41c0c0f241029401c082108107038075030280c6e42c0d511b0fa55900401950ba622454000902d180d208100007074546 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 475799424 1250 475798174 475798177
    0x1b060904020d0609020c07061e030b1c0609030f0c02010206040b070203041a0d0b0a05090a0b0105090d060506030d020a121107030f03030b010f080c0403080711060301030318091b0302 80
    0x2400400040c100994024100100d40d1260804401070b5400075040e030b0706d20000c03c840303401001c030f520780428040d00a0140c111500b2620b4454070034035841d013003a03400a513607504030303054411031208248082c13882c1c80c02d09102406100206401040d05108504c6a80e4440c0c1089000329806030010103503600d8079038a104855800804090450006100c0800c0300c000c00354840042c40c15600440e5110403070160301c002159405060700d40f1645c02c07400304011076103c01c440d050340001d104800080c450310b0400162107601c643d40074264030402e5443c1c0b0808120031a40a14002da02c01d504032500080c8003030f8140d0b5920000c11000d0101410700c04082c92030f510500b461800520720b4015204020754950343e45144218201b402c81c04a84c483c5060842c0b564080e0b425005034441c2e2a01c0401414543ca502e0300500c00c500002d00f2003080040c0303640902c10580600c0381403035009801c0650f00e40c2d40c0d040042103407059801c0d004000503602c2000821070800e008136080946a4490b5070444004000160000e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 475800674 1250 475799424 475799437
    0x8010b032104082e050f040204230c04180e1c0314190b010906091401020307020a0f080f0309060405040c0e030a21110604030c03050c06070314091b06 66
    0x1c1010400801c41d600d042c85039120061140082c1c030b003800e119403525031000001c0110300300d00310301c5c2400b00080c4845505080750095015a00010040c403c1d0946c0b455a0f07003804900c1c1c2170500c0d000c0c148441c450100b4018000c44032030705160300c20514052201d1082d0b90325169042d450354040c01c8121460b1031a00c144045480b01e0741400650801c402002c88400c880480c0d0101888151400c0c0450000c0c407406074403806182444d00c1e001c03aa0500e44050072a401c6405004881c20080303480440d580d008000300d490641d001081d00c02044d039185075610080045000e944403501548071040000300b07000003a9808580c1c0200558101420201403100400524020b8020002e00101547c003e03181030000102e090300602420507030540d45601c809051101202080400007586140d4040843c007080442c2c005505245c20510078401e070030100c03841c0c010300c0d280a80900550003070000e0950140c0c440503010241402410712070f51440c000e55216070500000c220480102100c0b16034503c3d10300000c006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 475801924 1250 475800674 475800733
    0x151a040b030a080702040b0d1205071e030807081009090807060e0703151505091906050a0501050403230f0a110a0b18040f2c03070804120201050f0c03120108010b03 72
    0x41c8c80803603499400750502c100240202048000070220280131409240460303000c0f0b0340e5a010442455542d004090050083c482e004000c404000b0a80c207940002d40c10b80107010700c002c01d01084006003041c104580c000882190510719090448800d89000b0403540200c81c0c00c08644408100810105030140c0b810340100e601141c1c2440000c181ca40e506007180f405001c41c6c1485401400b0740c4008141281c0c25a00700504c02c104580d010082aa031140481c0d068030742c840842e60110252580032150085070710b00000281c000c40d01d11000e601400641c09860900440e08170321400050380901c00840341c3c500400c11401404c119044511185035001303d040c500c00f44c00080e90f00c0d8440e140b40112520120f10106611181119801c940c560320110710001d0b4404001d1031501602c0d9460514621a17880b41c030a5001c0d000f80c0c0c02c0c065a01a4ac01e03540c00e0180c440c85a940c4980080700d00d52070740d10803c6051292440c800002c1100101446032102508000e001040451010f003980303140324018070030802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 475803174 1250 475801924 475801939
    0x1f14070206180c130b03120f070204020c01110406020f12160615090e1e0615010f11010213090f060e01060315080d020c031b0901030f151a040b030a080702040b 70
    0x3a5500c1c0c44800d103481340c03201400010384007100300405041581c0c400e549030222209000c040f44c0341c9207540440742011b0f811100141c2d50317007403180d0382805007018004c4100701c1840801c0c0001c0301c40d00829125401321000c020f6440484543c10101410b0086a941e01807074005d40e0b5041c00003c1d11703039000c1842c441c00023003500c45141e52200e12a003981c048541a10f203a40200f41c56603a03040f00002040e02420708a070140c80301c1e14290b40c4581004094170310182c108011202c5207051503010300f9000c1c40505400c0d0003950348402c41c41c2180400e881b944111070845141c1500c3d091200207903c03500d0240c584144903081c4903442c210048014104072000710b6440c03000c14030000b5000504006600f078002040e0090070710741d0482010141030100c40b01402c20a002d240b103040c5501d555151090b0f0649600c103d8414108646003403420383d04000d1596007880d41e250060300c40b4640600810360721204003c813001d000740f1078040181034440b5190035004008000c1409804014682908548590240a4a82d6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 475804424 1250 475803174 475803193
    0xa06080304050603150a0b0d0e060c401406120114031002040e010f051e04020a050909090601080c06040608130203150c0d050105061603030b0f031f1407020618 70
    0x11b41c2400a650005d44184d1000607803440d4000140114030340300014401408c800e24001524500c0781c41102e001c12001003603000f500412001c43c4000642d41c0da030302842004000014402c2d0784100d81903010b03c1c44808000014001d241c0f40410490b40e00c4000c1807a0b00c0316991034031021815070602401c0395603050081040301c2148110034405400104803111404081d540b40410703c144141e89904105e000da101c12181442e6a1480380307107031031500400e803030060ba01d200c002e200302c406003c0d8500b0164800c101c1024030817030240c000b4400341600c41d0b0006449611686100b0010b81d445a8403501022690000c0068420450801d03d13009090003e01a60028158000284041a003c4801d00903c403408200740d03400301118030803103001d40000e45001e46002c1d8040400c00021400711002410035488400100c00c0d5240c901511082e844050100c1f0805d480e1041080e4410510010300712071149045071420341202001000c40c0624016000307804241c803100030451040050200c0e07412a445004c402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 475805674 1250 475804424 475804429
    0x207050312180f0615030307051c05040905090a0204113a0518070807050105031f0b0418050f0f070c1403030a0501150206220507030203100b0102060a0608030405060315 74
    0x4028400043d0029100614040d1140076a00100e00802c6019030b2042c424140051800185201d56004070b00d011301c60329402c0e5504031504c1c807468100b140701d0b0707040106214054100140f00314885100315400d2194600ca1076000743e95015429044410400b030b02460070f107210b00a44044010030105401c4001007580c600311405940c01691840c4004440c0d01080403070010a00c40400a844502d002d0100d0502e0311000070268000076149400d200c154502403001c030070002c81000c1c010300708614130a0319a03a035030301300151b41c0c5c0d13220229800c1070341000006628201103040c280d200d045034030202d080039181e5400865104001f004100d407441c3e8030401c4886181e800b0409140700e40c0082c080421303158100706c0392607030150115080340c045d5405042031101000220391401e4002e404200900070542003420715500d040855030019406004901240d01000040d400041008074203030220340b02e944949440d10212511841070424581040c04188906e103050300055400c141032120802e646c0c84050700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 475806924 1250 475805674 475805683
    0x1522060b07080c0609061b03060d0510060501021e060a020702030a1b140301140705090d1e031b0c06050906040504051906140901093b01050a020705031218 68
    0x10790742e001c00482c00301116642007100c01e0b0700c910140d01078075603410102c0300305501c0d24500c4da51001d10003002c00080d1031903e500c0200308145c2c1d00101107400c2401d081c0110402007003280101e500500804001d541003050a014045c13502726600002c002035610201c0000080d00000c008136814080d03d800c0ba404114015105000080000003070358400389050b440801e05004410040d00903410300d6086120280c200c1c0c4260707401011400d0082d0fa911182000521300f06204500410703076001400d184800b540c60341b001c441054407a0b120400e0080380c600310040e120304406801000b40106550030701009100d400940540d40d0094107140c20680c584000509441084030200100280c0040e000072485050003094003c04240d10219541712401011482c200d90501540400c540c503240d5200030640082c0c0300441c50003060144040302c200d110303000388020503070118400c1c0c10360811001c04c0c404034942c82145ca15682c0f1100840c9000480c10030f6003804640180030200c815040c0d220450707140c00510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 475808174 1250 475806924 475806937
    0x90c0405180603070e0408160c170102041401021606030b150d092d02121c050403111c14010e010e010c031d0604020d24020a081522060b 60
    0xa040c0042d14001042c1860701604d5030003220310121003010310000c1092441100c0c0380340d051f0340551501c00d2640c180400720141a521040c484010700c0341d00c484498066000d002500c5030140654840c0d800f4400481c0e80700a08120036045140c8d00e4005c124150103030707100028000c0c0107096440c05900d40340d080715440d00000c0708041000d45402c1c1c0b0008201801c000302d0344080100b50799a400c0c85c107550625244003651172000740160451001c00c00b40c050300308118411001021980145842c111100411682245c0300c1100e004c810840c902d40c2d10b01e082005181b001100380b054603d07901007a03c4030b8807040a040140d201039544c0e4004081130800a005801c9a1100d0000104072500c002000400f21000440e4403416004148422110340e0f801047d1540c12640465038030071200f495007041c02c00266044803080e100030704414080805030003038000e844908d2582c0c030743c101a580c0c0c80300806104644021025445242c0344417403041c012400b403640032407140c0700c84001405a100d00e1580754560050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 475809424 1250 475808174 475808209
    0xf050322140d0c0b070f030b031e060705040602060f0a0e300301030b010608040812070816020318040f29040e0703051903210603051902010e090c0405 66
    0x12200591070560802030a400742d182842e1800c052000ba45959610881c05040b010810503000301c190043c80c13180c1c021030100c02d0001c055071480b04405031101000c05c0e0340e007210074880c09010b000840b014004d00c19201220625005005c09a0f00c2c0003244424000c002c1000e440507a40300c0e528030b89100b0411000da0240400c0b000804e0700700b240c4c1400700c6544c0c01a00c58540c0441e007040103100044018059070304407126402c00090585840c9891540c03070054038040c50040311000c0402520381d071300c40c410502400505c410500c03000c0041b84202d8580c03185511021011110324400540350078641d000c200000c0c01100001b912440c8141510b10101c078200050903402c03100d0500c7c2d03205141c14481d8503215031082d4000c01101c3d00d1030b80c0c0c0980f6610f0f242400311021000440f04818103004000300c0015905180d0b00300d0641c01c4c2c0d82d0f282402480b844c0003d031400d1042c0c88005041902415488106507016101c1e01e0946540314104a1034600083c524a00040144400107140d01c035000c5030071030140c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 475810674 1250 475809424 475809443
    0x10509010906060c0206030a0b100302090405060414043201050402040b18070309020f060a08071101150504020d180326150603091e0c0405060d030f050322 68
    0x40004112200006800030014039142c0142044803035000050302c18020f0b41070343c0c0b25031242d80740e40342d01c00205000341c01503404c03462040105510f01e0345540100044581142c0400090300c92030180300440303241c1d842107105202e031200480c0200d00c0a0800d0014000800030f11007004d000c9500c8204503d29102c800115070707444100703100451825006100403090151040400c0e12003107107101300c90240143c0010709056071903104c0303002d545541c502c072100c200000d0302e129036490150310010074030700007207079503400007890f0080324040d601040c0100620440340342201400103080c00c0400c0700070740c00805c40041c41da540e1081c0000514910310801001030083c1c40300696000080142d006010b01038214082c0e1030040c4017048101c00d00d444ea1b07412007840030340e51280c0b02c0d60b80c4108145880000611120020300c20031030720461040004080300d0f000b005613010302540e00e6540622814490224000b000b040c800407020420350f10450245610441190024071110032005d80700240101101c0151640707800d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 475811924 1250 475810674 475810679
    0x121b02031023071e0504230118050a0504021b010c0c20030613030e030703150f1e09020a181a011b030e0102070b0c030304060e0d1b03140d0501 63
    0x259201d954494440c411082d014904540c0050907210760060240d2803c1056904056040c421003e032006020f00700c0300ca10100d100d1116036202c0280a2840500007002c012081c40c101c400b2420400440700088d00e0f6030708a81c105401c12019400c0001241a0030b405400c3c480c160560034003c202000f10551940c001c5005241000842004600c41e170344091980e03c400c4441c0c076203000501c01d80c0b00c4082d5004000021152034100d07100300d540c00d40660b0502c600764010040c443c034103034030740034044012000b0414420b00400c04400c8e180155100403628028042c442c00141c220341140c00c50b03032320042c0500e8040340c481d0020a07608102c415819420360b640c0e10b4130b140100c1040b04902091209017448080ca08040e07130501c0c0480c0305400e00808100c01d0030072200300303a4000c2013000080c000075400c4c5c0303480c0c1078180f02c11a40c0ba0822102500d04509008942c90600e00204c0d0909555416503990040b4510000789064202d580900890801c4802001004041d480d54060844000308510215440d403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 475813174 1250 475811924 475811951
    0x204081207030e0d020a090e010b120109030801181104030503120a060803090409171b0106050a0b031f03060e06040b0610020a0b0603120403050a0b0a0603121b020310 73
    0x500e803942500410034200708110101c0c1c0c004a1a40305002c04a545400c40380ea03d03c003041d0010035590018141074200000060504419005a01c85d2541a80c1c1c4540300190306041c10309070303500c05030041d001c80e02c0f1100510482100c580041d0141d080703c140813816503211005810719500541c003d441d503030008154003c0041110440580140381c803d024418103041c40c4550345c1724071a2410342c0e8030036607580140ca000c10100510b200e00210b140303019070791a1200f001c1d41c5001c01031540e144244079441c1a401240a02d80419404152450742d580c041c1541d49500300d0401e0080d101021080d0244402c40020019070107024503158105032002a00c128181458034181c5d040c4081c00c1d0611034640503203581c403a00d44c00503003011103e4003c080e000007600c40e000030900342410032501d14103080c40000c0c0031040c44000901c10400612030341c2a01e085541c5d6100503000c072211400002c0400041140345030380030307204232408118804288003035140328041d680007a1500602c0304101035065111500006d061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 475814424 1250 475813174 475813183
    0x6030f01061e14090d050d0903031206060503040f060b0a03030302040306050906040b0610090f1d090a0c0e1f0e06011b05063402031305100e04050c1c020408 69
    0x70b400c003600c10b40e40d050724040701410000c1c2449182c1c102440201d101c54544c0e90310548050510340040c103489060000107402050800c05010a502084a01003180305907600c9108000465443e540e4071400c44d107071a50740d804884400c031801c3d107005840d00401c4a4640e07403158608019442901c005036203901e5481c0c04030641d41c000b0040c0e07410380c04c45010080810301c46000d55901c180100c40d40042141c101034180d6054441d5040300b820f40c820344002141903044031282103409484c0300c01c1588147e80c4d1210850b6921102d52008021a20385a410018443c0040c0102e4010121540b54080c108040848200d8003a0f1a88010b240c0d6103900280030280d60045003d050900d85001269040005502c0d256031300c660240000e40c2c0a0441c41d032003031040e480100a8002080060289490190f075088000c2d6a904103003041d843c41d503004200000d489c640f1030810740c940c264585039400c041c80c1f500c1c100401010001d01e018540e5100708110b41110232210301d01c061030740214000503180c5040c1552940341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 475815674 1250 475814424 475814447
    0x30f0103200907030f0608030d0e0613030c0213060510020d090f05090402090901060e04082101060c030e1c05071a0304020a1401021002070b0f070926010b06030f0106 73
    0x11048a078000846511121403003035000e041804c02007000280388420b88000d002c0b95100400034080418480b01c03c040c41d82001c03159110450481e100740d02c520044410034241c0f01002004200caa00304000107041c0080d0380d002c40d065041001901c0d540d6600451040b100350b954031001078001192000b1581d0304101c402c400707072490070f03100101c1c40e0070030303001c14400c40d000341c0b02130b104203c035100040044031f003508803402605150100d80d0389801d00b8501f8803038640001016442c0503103044c002002d582032031101c0c5410bd582c96a503586101e101e0740c07001e0703600a0200740103d0708550721240e0340100a074881d506105962144005140b0b80340b920380040a0150007140036901242c08201b0700015a49980c0600c081d640701542c3c03501c200041c240180d10f4a009112001011400419160180140b0070022885000c0c900e40a076a150b0755090304460011482c003585503c0203940e201c010b045004040e441c81d0308007a1034000a5180401c800286803074104658034542c0c150b00703e00500005a102850142c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 475816924 1250 475815674 475815713
    0x15011412070807030f06020c0a08030a05070f080705210910060f0f0509090c13230f42010f030e0d0f030209150d0b01020604020d080a1103030f0103 65
    0x241e509051400d51900740742c3c88050448400110381c00d06101a80c0c2c11034114680c0d0408880c8524038034980f074000c03500704466004080d07203040001190b03c0e006401c1e03a5040e208a07500c0d0358082c0c0d00c0c01d6090f00d5a400200700d07000c404112000c0b400c643d1411001c41c0f80107507000760041101d511030034181ca0503111542c00401c0382c6124503904000114400c0f4225080d0b07142110072410940d50081e1040c500405451510750003c00140344580d4850b0550000700d80d0342803010401c0380038030051090141c000c010f0740c0303810011881030000b80700011400000ca845000e00800c01701071103204510600c401b03000d04030304001042c24a80c104899a000540e44506007040d05041c0400103440c5092504c43c07400c400c0308400d00600c2030504203124440e5044500d0f062008203d602030380381400b00c2d40b9480d0844011501514a041401a0a0340c000640a807103a43e0040c04030001400d83d564031000354000d40354134814070603008490300501400b40f000e5803041c503800c100d13401a985507060031686001184201007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 475818174 1250 475816924 475816933
    0x20d0605041104090c02150109060617040f0206030601050d110322121202160b010302010f031109040207020613120203100204030317041b0e01050f06040501020d080915011412 77
    0x880c0b079100c0c50240d5007141c0a800c8002050040088280c3c10403440c80450029160041d0011941310481c0d440102990401d5440c142146200b03c0d00d00070106055502a14070046c00c19258014501f203070040d640007030185044c1382401d07038801c0c010003038130b01c01484a8603145010080203c50305000120800070301409012550b04100d5885403801c1e99002c0811034100045100b0040d21050302e9011103506603031101403c0707110759460601c219076510a0000b01d000844115800c5052482070103440c282c000c1c1d4100b00c81c6802105030400c4000d601c6900c00b243c0204050020744c0d44204180d0f910030040803060b9901420100b2441010708100302e0f6001109042d105110600c0401e40c000261056422501e10300320080d00c49081c100700c12151150f24030686040401e0118144012104090481d003003641c0c1001100c00810801180e40540d014190040e802103840401c0e0500c00c1d41c0c129040380c80c0000b035842c0804c0051042e118440c00340c1012070301c41c9100000000c5414604500c00d0500c80400242 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 475819424 1250 475818174 475818191
    0xe03030c0a050a09050904050d0e06030c1c0f050c0d0506100c030c020d05010e070501030501050a1a07030e03011a1002010c1e05040e07030501050109090507051b0c1003020d060504 79
    0x11012030159001d510100503002c20524103541c011402080a894010304092040c40c00d40343c07955442c0c0d00c07413201c1d0b000600190287c0c95141404801c0d640201010740e1514201001503c03140b0307404022500361240c907071700c40850724400c40701446198000d0585210b01640c80b2902c111002c2511005800b0354060140030b2409407080e80e01c1084d1041499040ca0300c6041042103000185c180c071008800a4569441c12440403d00d04001414404448088e00c0c2445140e0343c400401c080041644981d001082403000e90409400c0698000c104640c440c0c1465810038609801081c01c4484a121601c0c00d00019000f4200502d02501d01c820912035a200a20041e0303114100100b4005000c4501c41e1648041e128140c096800345050b1005088002108122403400c0e0700002c014100a2003080c2c0131442d03460000c105101c0d03a000341c170b00c12034842d00c1e07842c9041d034112401841c801c059000e5081034002c0585130f0585548081d01c0d141c0444503035502588860301c0450480803a54103510203445a480e0200300c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 475820674 1250 475819424 475819441
    0x121e0c0a0e04020f19031b02070803030403030c110706080f06040b030a080d09020d05011506080f0f040c030f060b0f060a0e060d090218011e0b19030b0406030804090e0303 75
    0x40c07422582060300c003d41c40d250480c264040c0e03801110b811110049207843c1c00841150b240d80101400840c100c200013080243c0001640c4400380e90003a5400e6070002c0000501080c0680c001c0002041701d031a100315007a9401c06580d04080712500f040c0f0025446074240300d80b4540d0007150580105045a00304200304901000950350000c03002c00800c0000d0109109140c100c255009009030754019011810001d401e2800900a0108040a010f0350070508404200c1d64070034000a031280820408585183c5c469002e107183c42c460082003207504100144021001986a008250545100f01e2010441c0c80300481002000d00f01d10150398012842030082c194159845101015502030a03601c0c2951450002201c00180684810181d041490000080c01190512040030b04803500ca00c40488941400c4002e00c001d4001489045100c0100344040300c41280030360b0300c800040910307080c0042c01c1c0f40c41d6008542034801303e910aa441e21004035081144000754018138a20b524040090361071480c12901 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 475821924 1250 475820674 475820687
    0x40c0e15130b09030105010e040c06030509030409021207020d0f09090b040e01180b0609130b130c121401020406090e13061109010f080708011a121e0c0a 67
    0x211a88a080e0810021060400d40421a854188030303424909000c0d4807101c050040d035100b552054000d610303202c00002e048064005c032034040d07580044600038082c60520100c025181c00782a240c0203000400000403d04501d1004210b402481100e007169458642d038064149951f8507031180600c87d1007845640d420798000d158a00344c83d010740d03002920a0700d0b10f0103d0004e007041c45180c8200d40c44d0215440c0941d5034100c5c2d2159081c85010300d08400d40c1d44005112002c0010380d046240c180b01c00510400003100e0310002540000c40200c01c050240142c2c9034145002240d5014892600c00340c003089040c00311010607000301148039002035140c075180010003003d016291003402c80040380c0e400403850052102c42c85240540d0854410300000c2442182801581d00c0702c0e0301d03540402ca80006000c00d480c002c040c00d5206a071507850f442210381c68012078140d41e007407118204018100821410b42c442e00080c2c003081c0200ca00e0b584842d007220114800700881000a00060381c00390092144c1c40318141e02c0321 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 475823174 1250 475821924 475821947
    0x30f060106030e0f030a05071502040312050702030f060f011e0b19050c0d0201020a090801090302070e0628050102010c140307050a0905030a06092102102a090e06040c 73
    0x140001d03c188a484106051030981040c0c0706035400b00140c0c0c060255481006404403601888101c6c400307243c125502c004030701c20740c80001c109503000086420b455008501400c4003d00140503500024000d01c00107042001c2101c0b8141201c8088005010359105014000c1c1002c01c0f912040d08810304007480700140d40100d4002d068071250110240f40d41da40302d0030580311204000401c42d08803081d40038001c1d001c1d4112545000001d401d915000a000e501409020152030f0143c02810403182400346411080d04020401500b18200a1780307400d104175005120003140006500c488a268184000282550300b446050030400074821140c0d0546045a41103a0b006481ca00300a55070350346079501a1000c00544d0302c0940d041c015100e441341480f20f16000005171920035202c0984151340500d403890009400101d0000588c071104106001030340701e84c85514010744010b003c484181c168100c0301079500c1c0e10184500011307038811040040300480700d000d0703400010807181884514004600104a25040c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 475824424 1250 475823174 475823177
    0x30a020603040f0c0b04080105090c041407080a02190504030210020d1d01031b0203090f1e0111102309011b051b06010603091a01050d02190803031503010b030f060106 73
    0x31038a0f504000c01c8070000702c01000c02503d0310391143d0743c5a482034002c0104a6501009000c0e0400c140e246141c14442d50204c40130101c1d100e021915013140031030302020300511003e9125070800015065100c0f9400c1448e04034070300e0f604c41d1754075429803050101c004c200003900c1080d588a8809050400c1d00006040c604624420b0320240c29405c1c2c83c012005403111000d95a00803143c54a0740c1803a0fa400f000920f110b550036261004030b0344019080c4421036112003030b041422240b40351020302543c49040c0c29000341d00f80c0000c0340c1908208000c65800c40c3e510202c0441d802074000c000c504940c0900301003aa00030009030080000d11040d00042000002e5880b40b00d00f008000103605403941c141d440c480c5061005002125a00d61311584040c004080110040d181c42280360031040c801458441c13018141e0302c0180205210401a80c01c1c005a1807402d45605c003000d80c040c1c40819150800c10195200e05441074154041806075424982141d881644650081d007054581c2d03030240b03a00107a9181111180d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 475825674 1250 475824424 475824443
    0x403060f060b16050c091302010e0118050d06020702090c0307110a030e01050a050d0c050901141306210507090f052d210d14030411011d0918010506030a02060304 71
    0x2039140c01c0341405100c0860a510006c69020702c0507012111b007095009900c01e88540300440158801900e1882c151944840c4450b2506014050380c02c20502e00e85040388922409070409001d5800680040d0040302d170b0b10064000402000f01d440e904c2a481101c1c0088400508044062514010b02502042071528184200028405801441102121100010000c041044001084005029a0289400301d001581c1d901079100000480c0c01251128440314600e100d1040ca08407043e079452103a40401a00c003440000c94507000402c034007545114140a9882207001810b00e10b010740812002d4012034080e412200d00000903850303070b084104801c3c0c240d0f82d0261255010a00046021003043c202035182c00c0e100404031028000002d0401c04444039440d044d00e00702d5000380b002124081207038050b0130071003c011030341001d500a001c850140b031001032a429024182c02c011038440002600c42c5500c1c03156100e042d1041c0701080c030840b60000d01c1240903120741001e940000b40c071800080c001900c408103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 475826924 1250 475825674 475825717
    0x506151206060310090212011703040e13050f030f0d0606030b10030f021312060c020d0206161404060203130807060c140f0610080609150a0f06051201020403060f060b 73
    0x3c1c5a81e4018517030644107540d6132052069134030f2482000e1140000505503c038a03d4201200407040d00c003552120b5002c0089503403021484420040503040c19541d900030503040390300880083c0f006241d84061604103d41d10800864a001100c85030742c0150105884c02100e140584d80fa84c01030100c03800b00e0301e400300380d000e01010708400a00c1185114064186501030005882c4000112000541c1c02101c0802958521117001da84403110741c3d0319100181c0080001a280d5543c04e000540e002d0414900440382200c0003035502d00030380c040d801400240e803000c14001a485215464480035102443c09401401e1802c003000d0629015804000c104000a299285d400901001513003544c900c60b0003121024108016507021600e050701032a21140034240c0000c4080400150f152100c0340103510360740c21a034a404900000300541c43c04402103a46549002400c2d0340c2c0c0d003861340e181c5080400010707600c1d851440d003082262125000001c600303040c80c0c010000000e1060585190b507880602c03610b231291 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 475828174 1250 475826924 475826941
    0x1230103090c1707090e0115060804110a06090510030b152110170105070203030a5c07030305090703080d0b01120b030c120703080d05061512060603 65
    0x1100398001e140320141d40452030340d0586000542e44c04480f0009410017119900701030940c2aa034120602038503d02c0d0400080042ca841146010b0b4814020a4000d8030130f0701c10301c0002d900b2410b42d4030207000078808200611a5192440c01540082c07110304080040240c9440443c0f000001c400030b20758000740111341d07003e42d4400159840c566225400070001d25207000100005a4401c5004148a4510071b903194130710700d00140b2505000d908290029411541c0301c8150001401d100d100311050031a2350302d004600305012450a00100071640070020102516541e001285500d0003110300f49050080505e0080444110896042c0d5400d0718020803107596810060745071601d00c1e4002001d004d40016a00840070007640818001002641c1d2134428500c0710009070141d84883c0b440c80d03810307008115170710388078605000c920620f44e00110540d1181d540c1d9031117800d0942c008c1420b5107034503a22075007002600c2c58004035440c50000800c070360311b040202c0110768220a0310000c0c031650080400001149040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 475829424 1250 475828174 475828193
    0x1b0f0418150b0d0924060b0307170c09090f040308061e04020c03090310060302010201050703050c16051906090b0601080f0712020f0c0f070b03011a0708070503040e0106080123010309 80
    0xe0307040503003c244010464a200184050051600c80c0b4038940b140210300d4000c7e0b0022240100700c286d85080c51000d403603c0800380524090000a10103e041004241c55169103441c40c0c41100303107400440701480c043c1806050400e005018074403445030f1022070210b01400440d0391040c035406a0f0010788862228814901d10f201c3c2c03a001c031340d1500c95180120840e200c0d0340c0000096038800e074003c1c13040d034580000035004c2d9070b000d0310320385072407039040c000500ea1604c5045c4450110f070280d02140d600c00d1002c140011242a4601e055546a450710144010b00c840441c1302d035000756007032030520070134504240d0443c80424003030108404c008652102c01d1603240310346c0540380c0042983c000c550b62070381280d0003140d84a084020050039401004400941d40c03405000b500c0c101d400207800b201c4403000b46e20b8205010307440036904403545440ad000392008540708101900140c1215040d42009504050b0007500c03000b03059110750b0644030001650345410710340c003028001c594028200403e1a1220345082c1021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 475830674 1250 475829424 475829441
    0x151a0c0f0a14010c03020a080103120c1e050f07031a090c09010e071d150702011b0503070b0c0c030a031a120102041505160b1b0f0418150b0d 62
    0x94407a41440405001d140507900d501500b1001c001c0050000800c4207400ba400351404000c04a20a0300040021540d4003c0300c000c1ea103403910380b00c1c2c0c410741d00c0e030f443c40940f0850030404e01415081c000b2200801c001080980300c3d880301240249525861071740e0b04a03084401401d0b1102042c90000032960f04c60013080364040c540030013000b001c815030315038140c0026204100c4041c40029421400314014042000c0c60301595032000d00b0290440207640d2f000c051590003568200d04003c48111b108051004000300082c00c10311a001641e0f56440742c3c104030101010190180103c1d8508104007098440c001007101c00703440c0b1509001c02c800007803d04284d080655601015000720408928610b0490103500400a60705204100d0001c1445d425040ba814081c01d20040840400340c6640b0f8003054000802ca54000f500c10f004015070641d0b03824810030b54001814015a00c1c07800b107401c1c0207400f0948000e02040b00c0529040000c4428a00d107030303651110510410407804400501d250000d8204e07080b080d40e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 475831924 1250 475830674 475830703
    0xf060d020d0c0b030a05010509100605030c1201120201020c1801180906240602030405010804080904090c0e1005090c0d0b011b110901060f050418061a0d151a0c 70
    0x1502da030794105280e0b030383d0040b01d256010031300e008004109440e0840051303004080ea04100581541850819185680045c250720300a00040c004001c1003480460007502030050480200d00e0b9070154800613150030f8032400d074140b08150385040042200103069000781100c0107400c000c8040603460120000901341d01e44090144e904202c015140c011804030b030210780380a41c0d40e009038810713a641d0382280c0301d00641c000c3c18009440c1c0c402040100303c1080280c5002080104001126819541c400358bda00c4980d000ca80640340b075204010810a006200600030701e03040c0e94245151034400d2001b5418442d02e03100c174400c0d40da1041d560b04203911403003184200c00c103616030070f191100c580e0408075611104962460b02c00c802d810000b02d1010f106100d003500142d5240c480b85d05060800502483c512018584091605c2e9134405c0015900285074106c40302c1081d020f80f06543e158907074a0300040d907014584202c01d00c000e03d4000c01010f507102401d03000e0189101041a04d51502c0740900d400e00d04859071440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 475833174 1250 475831924 475831943
    0x1110f0307031e1415030105010b0901080604180507080d08060d030c030311131a090f1c32010b060d02070624150c050a02011209060606050c070803030f060d020d 71
    0x18a214104c1c012402400f88010203c041310102c1d04050903942c0c01d00541020781000c0c4240105540161038458100a00030404208200d0031040000f0f070001c42c03003084c0c5055001707480030000f541c82030082c04205446440c020300b1601d046004504580d0200700c0007410040440001340500d84a5481441006001b1301340c40e0380c2d10154180d030964490f85002c3d00a040d42d2940304900172100c20000c031a47e440010b800d880103410361004100702c3c1c1c1240d00c094140102640c4055001032b6240c81106d0f03440c40300702e1599040c0c00d001034030300492002d1224000d201d40c1c074000114080e90340e194150ba4103201c128a026903603000c5490990064042610605c0720f10bc40082c01d802e2088480b6282000d417548982e0501300102c00075070403500c3e8000d000c40a03040f60408110400503501c1003400034074030507842e0001b0540d104295552030440d925503010100007030b800310315458035030b40c103218000041c04604000c40c20350400880507100c1c1c1c8005405c0b10310400030b12081c0e00071074441990081070f150b000400070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 475834424 1250 475833174 475833191
    0x9020319030324050a09021e0a0c0807050102070c0e040c090f0204050604120218041a0a180302070f06090e060402030a15080a15060602030a0c0c09061701110f0307031e 74
    0x140303c0718000740602403190301240310200e04c40e5850b02c00d94152500b20b61100c404120b207808580d2980d1700c60000e2004124040d01038801142c6180020030f40d080c401c400040e558841820320039080400e54010610224120040c000401c40c00355011041d21800e03800010364860f9850348030003c0c4210f50020b50042404071b4006011425510b100659030700a0b15403525000e00421215020401120000c04091075803400b08001c10190007903540c0080f12100008120850340c01c19003152144410403001a40440d0b0240003501c421018480200b21500300202814186408030514880042a160180341d0110002e40e180a40b901f0002c001e030003003684040e10540300d121168440095080c29142d1a00c1c0d800b100b81c1d280e81d24441c8001b00d400070b601450506a0010044400c011003200c10359161102c55030101d0f58008a00c02c0d900180061a10040401445030a0300e0a441d42e082801c0c40b00c0360180541c01105070a20222a03218a4a150008114a101040f0b000c070800384904403105919242c00c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 475835674 1250 475834424 475834481
    0x216030309031a011a0309070306020d1a091003020d02061908070201150f0902070611030c0c190507050913050318120105010506041202030f030c0105060a09090203190303 75
    0x4256406840c000100c1d011203c00740c14502c01c00c2c82100c0040b2009074515005840c29400b542e04100c60030265205540d482d20f074642030b60041ca01a40c44281d50350600c20242c512038201590042058844e00c81c5450300c8000760049000d14803020380610248022841196206c1c4d080390302550601c00304071441551800002c2c03814400f2113081d00598a041821020130241004038403c91704034901d08503545003007030001e0002e034104560840701580c071091090490070548001d9440307840050078081e00e40c03000340a1103140c01a0003545070000c05144004c80302084010030444280e9006482d6856251034107070b03203011880500b000c042c00301d0002060300210402c1d003030007880071034100301d41c01b52894014148031400c0781d0b030038801e01e80e21a000304402c1006044091507101140d0004050703500e401071400701d1034210350120b0a00d0410340d550300d08010380c43c0340044408003d0700303000004100f0140254003099650b480d000001c5001d448040c0082c080520941000000b607880002d410709200f5060030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 475836924 1250 475835674 475835687
    0x909030a02070b121909020d03021b0a0302030703032607020a030f0206090d1107050310050106090e070c08030a02160b040212010e03040302060d1407050d05070903050c1002160303 79
    0x2004014040c202c80050401c68a070309444411042e09281314050729240380d17524245000f0385d0f80c00c1d035141d2100200c8001d613507804035039500140260003910340c01c00c21124080035510032061040c03185104c1d850600258800040a8050329814101024800d0111341c0d0800e06100c08002c18011a611500b00140d065001c61241d9801c0e10a0b21950301040d010311080e611900d00f10f89600659103e91707003601146118a100c00880905601a01e00042d200d0f404241003080304825a107642c0d4464004100440c0e0000081005052040301d070040742c200001e0003001100b1a02d8041d008000110125010000c51781c120744d0303c02c4108141980710f012030b00c1e01114902c02100d069104082c0c81180b84a07095041c094000d50708201d0f005103203043d04560030400135030055401060681d903913543e441f440f11803451495000b0340d03041d01c909071520410005c0a00b51007005204500f0482300307140400009000081a880600089901c204c44070348049040340303400042c3c1100c0c0180c0b0264440001031582111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 475838174 1250 475836924 475836937
    0x90b07061116060f050c070503031b04080f07050306010902090d0809011b03030e060a02040f260f070f050a06080118090209010b0c0c09221b09021b0706081504020405090903 76
    0x44c042c819981e5040c0005406d015030350000d00240c2003080001c122903203608a18a10030810285682466100c44130070740f0300881c0d110740d801720b94880030080c80686820801e041c0102003062041d85090712003030105120404906000305201070118603107415278054190a1a0358400081d0b600d264085824020040c0041d003031484214041c8101085420041e13000300d03002d0340d00c141c4694400501e81074a0750700540c00c40d0300c00130301482070202400080c5c40030b008490104a1540040c280d050600030031001900709a4455841910300c4203041102c95040001181100c2183c103602d10340302e051954200c01f4000240009600070b00d020008a500742c13204000d0140c90030f0700c0e41201c444507040e03018020940019581c80c001040c03241a0040c58122120304081b2107803123080c009001d400d20030289000d900040c1c1080300c0080c0c01007042e042c0c0352030015018180c40c5800006050740c0d4038040014146090280c112106c0441800c2103180549694044030f00824014000648915107640003545940150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 475839424 1250 475838174 475838201
    0x20f030d050a15030b0105011d04060303020601060909150b030402030f0a050d0912151104080601030b04030f02061b0f130b04090506120d0f03090b07110c01090b0706111606 76
    0x440c0c0c03448601c0e8003e02d410180c0e81d1006001300142d08040040d10348a00c500d141d140c4a042c801d1141d01c26403a540540030081d4440d400405241d41000c001400000040e00144401842d1002115070001d21050100486a0400c041d0f40c0c0e82e01c0307500200f41040094980220035101e184c000400304440090441382240c0c587e55410013503501da11010420000100010704041c159403070450400525500407122510345000d0030785031590340c548141c20240d0984c01911285407120400082c95088030500c202068542b0240034945003900117204074801c5002c5a40c50f4040c00300b100c0103010403480803100c2c5810103100b4822a581d803080c03500c2d040d50003030061000c514180030209069080a01241d550b50a45002a10950241860845507004400c1c00c61003056100c2074601c002c82c4003055190301400309035858040812006d1142c130315280d4035030819410050380f40420442c2456100c141c64940354000004240c410700141c004940340070301c20003a10300c003031004041000c020284e40300f041c591304c11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 475840674 1250 475839424 475839431
    0x2071a07030204050a180603050607031a010c0f0f080d1e0605120d0c020a050d050a02030c12030703050f090a1d0f1902030702010908031302090c03010b1207020f030d050a 75
    0x903000c044069000e20712503103412407082c10302440811201d0f41c4200361041d03400da001030301300e6598640c60f02d000026070b42c080100f540d4005600846510000707e00d003e000c00e0030701078410540b95071980842480c0c84030280c244001419940c00700b15508048070b603801c61f007020600074102140c0d007000c1c0d03041d0060440c216251500038005a6820074900d0b90910b500d101c0c0180219a16800c02610f60754581607007280d10840c80b0402050796555142950200340c09038005207030188252051600d0710302c081c044117108403c0c02020a80c612000000c4440041d032503d041615118a440340300c003d8081c20559580c00601e01402040501000d500919a4003481d20b4140e1980c4a580503049040425100407150a07100d200d1110094517a13002541c000e481440001240c6050740c4403590141c0061303554125280c40a10b007032065150840ea06030300310390789004461a55141040081d01840f134480c840c0201250035000031a05402840048181d019141c1600d503180d14055a07100204800c0b030b51808614035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 475841924 1250 475840674 475840681
    0xa120c0306260316030e0411040e10080c0f01020f06151e0603160c02031b030c030102041206180c03030206040309060e010f050c01023609090c0108061302071a 70
    0x5407000c80880d140076420243d480c101e116150b215031640c2e01c6905a050040c071050b4403800b074031240b2806e002e9640548580b0346450500345d85000d030101c007900800c200c0c034604000b40800c0001250320000300b50304591118500c1c0310440141d0410700f6840084005008200411401c2e0309038a01400c8110720880b180781c01e0030040f21920a002c0c1c0c0005c00550400b1007800000d00e490b82c0e100454807100480c6c01c00c4080081d055000034500782c0400e02c0305450510982c03001050342002c20003c801140102e000f54105414807091004491000c02c01400c040d8403007090144000255011801e02c2d904400c0900e001c0361242001b95503540300751b50032800503028001c0002c1c0c56110b100c480071020816940c401e490114503d0845480d00311882c1400503545c01c004103070103e2060101b200c0427070351040c809154a40940398500d01c601400b41c01ca0300070000d240c2000100315010548088085090070710203a0340e1680008500d0301c1128400e04071045200050084c240600908442c40b00d022002480071181c1d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 475843174 1250 475841924 475841969
    0x1801091a030f0a0b06041d07032001020c0d061d0f19020105030414010b040915050601020105011a07050709050414010b0a06050403140309062d0f0f0a120c0306 70
    0x249001d198062070f4000da00501c0006070300f41101030700404000c0c40810b01c90380c0d1311582c4441d030b144140e8822195212a4040003000000403c034250100441c200f170010142010000c4d4440c200f1420b40c9208a5560406108005042c2c0c040c508282c040712204c03091109050005a40790220b02c07110046101d61035514559220111302a20b01300d0741a507810b400e5448179529003100d03490f40750460080c0d5403246045003c0340c54902c10b00320000d0194441e10702442c10441c4d20030071524064429811641400018800e50303078081503103520103d500803020760f509000d003002428507085400030042e25007803805200500c100b1a4000703240c140c0c0c000003040901c0e224000c1001401c046c0c4207560100b0000e000401c0445c50484440c0000c00d118416240307000c480c0000a11107500000303501c81e40f070b8a803185500d40c5505206860052581d100d031028681a60b805840300203019005650720544400118003101510513154800007001005003407040500100003e0060100380c0110548809042c1e942c46031207 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 475844424 1250 475843174 475843183
    0x140303070815240306010306030203060c04180c0804030c050705090a05011412190f0f0609120201020301030203030708030603010f051005010e0301140f0402151218150705091801091a03 81
    0x261035054a100009100b0160f80340c0e400040001c1d05040c1d5030b540020240e00d05000407131003542d400c102c00350740d28100701c2c40d08024040728480103481807070305a043c04495000350b0207541068040c200a03803081611700e030040c40c0c4511900040e41001100303091144d40100c903000207043e82c03080780120380700c0646201880300360b007a4509081310758ac0c482402d201b07280601188075107119006803c018045000c0d034440355202d25204104640c59a074817035181c4244907400d10380b040d444600e88000c1d8659451178001035a41c0c007401c0c401a10011001001c16081e41d82544400d1071244548018000f6180200120048501720310400c4d005c10712401e4241c101d4941132180e02103d584044141c1280e03240d01200d0030a01c0d600500c100d0704004641c200c500b05450042c007900a507104032490764000c0c64a01002c01d40501005201d91403a030142d000b40c840240c2c405541548044140760440c0ca41c22113500240e038040c02e66422003d00b8100800210340e030b1166800c07101c0c07404202d401c0228000a8801499a01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 475845674 1250 475844424 475844449
    0x306060605030402210c120a0804030f0c050d2609130e0d0c02060f03090a0b0c03070212120411040605041a09060105070506040609030e04020a08040309050427140303070815 76
    0x1e9802c441c80a414901d84002c050000c511114210b0b408d8405030b664101d03040c0e000790010359040b140d2180302c40400a10400a030301403c4280c402c003540d80215500c65002030340c1005043d811290002910982140320340680b891510024091420781c0d03201084400100046c810b060194003400b00c01001c514007506c5850007456010700047c1c03070000280503048032500081c207401da543c020303c0840d00100d04c2011803140100c44100e200e03503890800003006807500041040c1815148014000b22000e05400c181e5103a200c0e4020400e600400b103208005401090160007503540b1902d0802c580742a081c611b00c802c82c80e4002a102601d80741c8940b40151030070b018025000b070403036001c2d83c0083c00081e5140c12848078188a401d00000b422624030000381a604400e00c1c1e1000268140104428154044080350080c081660104490240450000d850303800101c8a80f543e03940803149072003046240180102c5c64401e86050303980707074100301d0801411001e00340c03403061a4042c00512000345251150282c0c030f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 475846924 1250 475845674 475845739
    0x50901020a031b06090b01140a06050904050a0b030d050406021203040c05010f050f030109143405091908070906080c04091406040501020a020d0215070e0a0306060605030402 76
    0x24114080e60b0100d03481c1800d8001d04590081e22040ca400280b0301d4007407410700911a071000482c0398141030300e52003485442040d2034070039650f401042001c990080c081700e0040c6c034141d801103500d80d00c4401142c090448840704580500c03c4142550140d603008001d002944c215a007a1400041020303550040c0303000c1514090b00b142d02560703041002d0340c042e40342c401d0401024103110b41804c1114485a205410903800b6600041d2a010045044841020346552010101d018160354081c921000c805143d00c03584000d0803050650320742c001c149d02078401d03908100304c01040c4d0468003154140450008029124102542c07144c01d17004100f1000c41d000b01005d9030b404900410352041d8000c100800307010040000e81d0f001c0c06014020740b40c0782e420f02425224074062000903a84d902240b000a02c1c00c3c40d450140001c46d0021030000700c001c0290703020f480d0041d14510f800f00c288080100080d245100030303403008014038070700080003e00503080300c00740d0b11440c004c40746850901f0020019500d2445010503150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 475848174 1250 475846924 475846933
    0xe03070503010e100e070906140a090507080606031003021504050405070504060c1104060b0a0f0f0518040b1c0317060607151d010f06090f0c0206040b04023d05090102 73
    0x40c039201d05540300d14a018601c104503040265540c103851f040703959640100d44020211030800c04541040d030300040050004410800041c545680f00504816003c1d01c01b138030070000000485d80091030b811201016580040c02e01185a02c440c041c9441036100f07105140c000ca0500c800107401e68010020758048a26640392200c00481642c0d9400d190301c0800703a041c0e4099982d600200e030344000c46020704484080d80e00c8071500303001c0700c0e1800b07010125001c003208200001001006891071106692040304202600e010407032a0409001812244912094011180e02002480107042d0701c20307101422001d100800e6019030301ea40082c007840d440340382c401070000c40a040c10506030000b56400041c0c65180f40e00c1c908010402e0f200c019081d101007000000c0f0355a00e0751020702ca92a01c51152805081c0200c400300041200450082e462700001040944012901000170b800c0d9141c80403039401c01d07108008140301e20a03030701d101d00c0813200c5240ca0791041140c40140c01481703c0d00420458424810580091 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 475849424 1250 475848174 475848193
    0x2609030118021e03070e0c0d1a060f09060f07050601060e010f08041407030203060117060604060f06080c1e03010e07111f09081b0f01050f0121050d0e03070503010e 72
    0x380d00030f084480ea0f03010312500e80001005102650740318000d80c000c030900c0c1c1d503401c000f02c0b0724416501803540640a40140114000e0f440e82ca5800316004004a44d040c55140d000400000d07070240600462403203041030016486081240114160b4140d5071252205400303d0130181c011141c1000c140c282801050314a004a004150108201c514802c80002240c2c1c0058407030b4003090030b000b02079020300c07481c1030403a080d44441d030000d01410340e100000341c600f08445c07840c2122069004107a807040754280066132001c101800301000444900044650441c40c0080e0301d41c0300312540e50700910418604000d00008a90441c0c03050740389080c000c50f900010f081c0340306520300102606441c000d4940c24076607038240300340004480d00c000d400001d070300808003600e20000d400028100310040303520500a9250000304104030314103d41c6181900c1c15950002420300e911001d08013030240e12003000c3c155108100c81c0d003c41d2980020702110000c000d5050b00e8800d941c64060500b030341c50055a80f100ac0c1c00032006d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 475850674 1250 475849424 475849459
    0x17070303020709061a09030f0a030206010602010b03060907060302031009090c03021021050903091201050f012403020a03021605010b0103110a231605030703021204080a0f260903011802 81
    0x246c8481900282030b0b496450411060030300d400110720045016810040040016940a1180174551241034000d0091031070140183c030348490590040d0401c5c95400300110b800c11a81488520152071900b00400c141010343c04c1020241c1e40500c800c906c40e8100072014240d0170300c9500c0725003102038510691601440312941305030191800502c0c0768400c0c03105100d40d00990f03589500c518054118000005500d0416100c4001c54410581040d001001741540c440840e84002030340303011000091400685501480c3c5045003e8031404c40321108841d280b007581b0301440011340c0300c440c400c00709803402c100c0072141c2403050445024032002c441c003080c0080d204040384024084005d900f01d0701d4008403841c0011551035175140143c200400d0340c0660002c0303500400c0540400000304100c1d000020542041c0c940600c407a503400c0741c0d01c030080518041581600420501c1079071889507681d001c0007801010a00319000125412011155100e50b080c040c1d0040060b522880391855103030090481391040818056 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 475851924 1250 475850674 475850677
    0xf0b070c02060a0c0c090e3d020c07060203070812100e0103030e0f010905010e01030504020f120303010627050d0f0c080307031e020312190212040b06090603030415030617070303020709061a 83
    0x1404001c1c1e036004040c3c0223040280c2a4044c8003141c03100060b10317410071108840c030307102d1039400403030540d8404c00c40e601c08141410140e0300704222140c00592141d4450500d02c5c01040c040e8098012503041400100401d03810041c0418030304415181d44e01c00c5041400112070746e0a50b0300c0360700d0101e4800003004615510a4110755803050020b802440d0492a40001c40c92050b0340030762a06240e0004001481690b80c0044102e081442c501250102a4124500b81c82e111030184581c0f4032500840c0b88040420001c0c4004040043d040740c00d180130036a5411718940c40c0e0b400014201c001622a482008401c0700c0400020b41907800d0390300942c00c0c821003032201d410440001e01680c0b4000300300841090740080702d00040502e00181d4220078040d04003440c0202240102808261045410748c0c100a071546001040e1002c88012009144105100f40320560041c10740740c2004240f105100072071000b031038000030400c0403a8826422201c0943d5500342d1002198400c0c0101402c158400b000040040040c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 475853174 1250 475851924 475851973
    0xb450108040b18070807090c1803051506030a02040e070807050301150504050702120d060513090b0a0f0e0a0f0506071706060703052709130f0b070c02060a0c0c090e 72
    0x3c0c2200c124039150381c1810300d031444540c004000306480b119040b800c582d000c040160741b0180c0d030180c0340046046a650584400b10340350701d00d40100d0003600292255504001e003410a98018104005030b5404408035034039201c46004010441c480c9800002e450f00701486503c5a440d051a8004116400c010800018203000b80440d4110710a200d40b14401d0300114006200c42c0200f54000500c05c0d10b0039060004500c000d402d040e282c41d00c0d05124402140c0001d14041d4000741d4000c0000d54a650002c8503c014403184540440350710404840b01c042050743d0205680c045c1c055401c5650030386d1213280864108541c0004040744901800101d28642040c0000d014074501c682000d60401074076078401e145020300500341d1501c01d0500b00307020301113060051103180c01003040101c1c06503518880d1225801e64941000040a02c00707c0d00015592030b10608246101d13a41c0100501c0d90f0b4203c0000081419141510030f540c15461010005043d101b11310034000340c082120050148800c2400d1b1001e009420704 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 475854424 1250 475853174 475853221
    0xb1203070507140105040509011508070e060a0c032c12011b050a021c0309030306091a0609061303050f0f0601060e3007030b060a0f0b450108040b 64
    0x1401b003c2482d82e02c0d44001030180404c80104406904440c60040c241d0350050300c040c1c14070414400000040e10350704111a80038036141030a20107810760b460206c5806a4508000c00003041c150300a640000f24801c5503101040c0403200700d14004045c4102908907035511105061100448007403044141c095005401a00751038010344021011488120043c100000001c0c000a651512007204044e010700c2084042e21150384108034880d01020f110702884a0504007510541c00854204240c1d40da8a0499480c034000c02c1203450160b40c0c1e4904180ea42072a148100c0c164000d04425000140c800500941264815941c0100c2d001c0d2660521a00c80300d55051030400e120b001800b426880c1d10403010103e0040202c000340b44562840c2840102808090b003481c0c0306045040c401c000c500140424101540c1000e50503a540307c41895540c9036540345104160a02007001500d1300c00b00700c201c0380c013110740d030b40030840c1c44400ca5a10004551039030080350f0040104000d103002c01d42c90b404840c650340145045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 475855674 1250 475854424 475854427
    0x50a05090304180f050f06011806091a1306032a090e0a1b050d0608011404030e0a0306090c0f0501031b0f1701120302010b0108150d08070807060b1203070507140105 72
    0x8150011095035006c40740c0b01c0480494405000c802d503800300c3c4000c0300d14100203400c1d52079414010014400e4009108491100d04e010604040b000311260450b201d8400c0b000200030742c00d0340e584000e0068802034101c0e1b450300d0411072002d1000c07006900b07202200f144a90b40c014442e41803d20601d061840900341c2d01c011542d41050401c90a050000c982641c061911056243e46904000006641c800c1c2c100b4070700c03641000800d0203001a4200480e40160342740c18102c42c503910350404078075002c0569001400c0241402d80007400d00a10424401c19140601414450140c4138801902070b81d403041c0500211101311109425136500c540080f11102c491850031609243d02003010382c0f80090281c001e444000507160010302015024400c41c040c110342030030a01802d1034040e010018a0070b000d41c0b000d02404100c5255800c01801e0300884441607804240b40e6201c22090800e07200926802122600238030f0f03140c9140301d1410001040d20700c0181c0c010014030600d4204828000490711003141c03103050010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 475856924 1250 475855674 475855691
    0x2d060d06051201270515061f05030426030417090d06021c060308041514030112020307090b1c050a02040c0215130308010314210d050a0509030418 64
    0xc4042421003540c1402c2e00201e13500d440c4000c02e2038107900b1050980400721449440f2000114042020a6400b00f83c0481c10007558912002c616a440c4039100752166859051400349080e03004800f5500650259180d0314241800000e13130f02c691111100b44024148042c400100000c0420382204041d0305a200d80c141080204000300e8031000150204071981500451000c480c0c101c1000503400918186c80103101c840c3c65920352136036602c0303607005510f6580d041000d401d413014000c0c0459504200d04d20110390740e0b503940d25a144c89621701c20500720300c0381c041c41d20000340b0040d682c000c922040400a04041109101c100c06001282550b0802c407102d00400e045500942c2d103d114030340403078500d40c01405510120b44507106810000030001345034502e10400f98400700358059140744c1500c2c1e004000d40c10040055440b503240810201d40c552005008410802c410f64503d80a4000d41c007071064140706c652510340301303481911821110222035500034401041500d0780b12a94000115500200040280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 475858174 1250 475856924 475856929
    0x309030203010c0314091c18050a0609060206180d12150e04020a06030c020a060504030215161101110f0901050d05090a030801060206041208071206080601052d060d0605 74
    0x600b8983c0600100c0c0d40c8034800c94070241c20403805984054284060140050820154440c4003013401509081000352411003030b10b003a241d0070b24005400010421100d580d45c40c000181402d01c42c4c092640107001c1e0002041e0807412103080e2501070040d03e0040d1118601260080720113009400e03843c1c40b50394460602c00788090380c000c2004c010b4000341d581c82c0102e24060040c8004403006da8810001c152511030107081d02c90b4007154541f0f0082c2d1004010449440700d090403071074003400110041c00800e20301c003441040700710184a215039060a48400c1c241d020309000700750807540381140d01c0968680400400b00703502d8180740104190301050402c0340c1050341030346081c2c044070390440e00b4500c0d550082d01c1c040c051540080041d0b0041c55940700410341c9240980e161f0002011501540e000e010800000c00d81c11805006100e480030582c42080110030b544820655440301c088c842d490049918078030b03420002014224010b61411000c10301040b501d003030f1080c441240c2c000002c50314559903481c004100c0342e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 475859424 1250 475858174 475858181
    0x91a03123a0c09060801030f11181617015009040317070207090212150609010c080a0c0212030a14090312180301020301060804030207050d1509030903020301 69
    0xc400e5241c281080c000801001045900110704402031050800b01046a25480207140f41900d03801a9244c44119945c0341401a602c1c41c0035a441d440104e6204280e84c648200c24218417510390741640e1126082c11000958007010100d04604100014600602020300d2380d26544440c0c2c10b9020071704446110301582e0012516684011980507002d80f0340640f0301c1c8040c181c01c01c540d00070888024907942000d41e40503207103504000061030b00e005e817000001c64041c0207000c2d823402400e00040070b40d51440304208810600608803600c44003101314002420041c2426025a02e40350303c180c5841d810145151118106030308040a500100b0440301030210058480e02240c3d052004101300840e10740d440341c940942018541511000c49000030703c1500c106036400100d051503109415280d5a9600382c03480b03c02c103134000160100d83c0560000000044113036000c5070080c403541c080d60070f40759400d8171441040712607002d081e40601100020f0f0f22010600040b0f9000906135846800c0002045559034082400e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 475860674 1250 475859424 475859497
    0x10504030507150507050a120b060d0b0a090e060402120708070e1e0402030316080f1923030f1e240a15030213030813091a0312 56
    0x7840101d510010030490302861031889051240910440c40d2800004006010301c080c3c1c14100246034010401510880d80b100c0711042024240d40d03a0740101c1c41c44180a40030200341035000d510a0003002405451a2188220310b080920107000c181e1079135000c0000041c4180c41c0c1a113a40540d1030f0025000c0c0c81000030400506140290000034500040c44000081058048055000f241c808010041c0d8010085516841b0411468600c45070785082683c458010038040000344600040c1c03ca140428281c100c1410010795074403107080c4413000003a00c1e291800100e020000043c02e00110300e61400480b40c6d907502100c1d40d07880100442400400104040040d02c01d030158038070060800160542950308081c49280503502054104d04d0b00345106100c01c11500804100b40c0c2c041407403501c040100304150f0086800c01c441c2070311900d80180406c01350003d0700c41c2121107450209010040d144801100c0222580100502612a50084030620551089401f91041b1080d40f0180a400c205442c1c080c11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 475861924 1250 475860674 475860677
    0x1806010e1f1701050118060f030204080a05010212010f030c1404020d0510080c060c100b01020f0d030b010f17130203030c030403030c110603041e02060d0204060c02011d0d020103090f020301050403 86
    0x51a4045800d000b22101a0840c1341041902008082d444401449101c211456490808104100400120003e02070394000707441c64003a000e82d0406001d41500501928a0711181c070783c42d1641d87c0c0704030020307050301c030310005241c0600a24104005c50600400101c403036006030000d40750031031440c11041101e60440304004104888001804030500030000c3c414028819034078030745010104803003541c1c1c1d00c1d481c41115040548038051441164803c0c4607080c2001248002c6446180d01005c001c1d01a00721031000d18009142da5040703004031b500c528500049060f0120700c0c01d2103611921140394019020784000c1e80c1500c010096001c1500c001c100500086019a4034804403014620b000c54a4111064005104071000e20a0202084450510118600e8249440f01e13034000d00e88081040c1d40a02c848480ca12840860001041a049881000140e1003641c400107090024100000c04030216140690440140400a00103500136800f0b0074059004402010b00d0481583c00642507540442d4200c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 475863174 1250 475861924 475861937
    0xa020705010b060a0c060902030a02062d07080906090a0e090a02090603030705071511010614130c021207030302070203160303080705040e0f0c0c01110405010e1806010e1f 75
    0x800c0c0301003803040c8580c549080765018582052180001d00c26000140b0140110790f0311078903c0304540c2c00704020800d26501400c0c4544a0544458403102c03a074141a1a11031108440181c100060346041222003c0740d114007001d0a0041c040140034650b0404069540c100c9110b600100703445100250a07849021080000d000d055941e01c103014035400c0c05040540a40d006006200c002040803c0440c2640c0303103620205c3e0220312002048898106056024180354030706003020542e0045000403801c0d0140540309410000c540320511002c98036407420040058000d64080742a030300340c603001001090302a26016080c400c158001a007046031405030703201c0306002c82e44100105600510004d601841604000b4101441d1181c5c11074450002080ca0740d480c41e10600048242c1a030f030064600382d80040700204000c032081d1079160600c1c1e01c54029180071918074401140d052038401c2a800000320554a00c01894480400640300301d08224007469110740300058601c1d40744401c0b00c02c062440340b40d58890 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 475864424 1250 475863174 475863187
    0xc15040507060f05042103020a06020a080f010509240a0512010501080105060d0f081b100b0906040603030e04150b03070c031209080304110109090e032802060403030b0402040e0a02 79
    0x10f4140d02c000ca01100620070305100800980382030381401003008103141d80d48660441a490101d0a0005241000740340620124443c4140b69000c48030381d100d44144a41003089d6621407080180a5008664200c1c0d1400324201c419610044040c2c42404020041c2000150584038800a03001400300211480e19031355803801003244542c00d000300303500083d09882215100c41c4e01c1c0c4030500c54020b804d80180c2202c1c070000340b179240401500c910710310308410fa0054440305402e442c0640d02070a0040d8410b4411545400400c48501c0c3c2841803404503545902c52201c007441e62010b100142512500150444140c0072001920800060081d0301c0f55000360790b0792070803411901c5c02501c54190500f04001141c80d14100100092502d02181c2d04070713800c0352186194440c1e4000480d02200c094114101450520000d00d820710800405040c0c00281610006e03103202c0105180e040300071403412864010391040e408100400e000780d02c0f150101030040d10240c40c0984402185034220019507030031000c40e90001e6103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 475865674 1250 475864424 475864427
    0x3030612060225082203020901120b060102011a010c050309150318030f030c1e0f0a080f06090c030a14250314072604030503060909061b0c1504050706 66
    0x910f0000ca4920a03840d41d038640c2915080e0b42c5008181c030201c010703620103401d04900100300407000000d40c0e000700251203a686a010310740e20b500c10110116601800000814541d43c010301800540d06642001c9003100d00350980110b80b071380711307100054400380010041003c2d42c0c0c031a55652506040c5020750150f89003000c07600c611010340030510001c8682c00a01003100c48183c0354044a80113aa1842e1302903d4000e42401e154603410762400c0a02d01001c001401504446454081d0010010b1500d0b21885039640d0202d844144004841e640c1d4860403140000d00002e649501950f089980c0220020341c54000c2c2512100c1d0010643e02118040d030800c18509900c0d20103012116000d40d00c0c54140200b002c402c414601d5020041c001d42e0912020b401080b04882c0c14068240402000760201041401c1c503060140195009481d80ca0040c440880001c1c0e461400080942c05090301b6480380e10944440e1400100d0f541014000c041a8080c0022101d5100441d45d1494042c80c0510007600b051403030b0520 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 475866924 1250 475865674 475865707
    0x346030503090613050604080a050c1b100e090f0c07060624030c020607050901020f010612030305160206150d02030a030908010e010c08011a0c03071b0509060d0f030306120602 77
    0x20100d00581304011034002240819455080765000360f440d92180900c2d1070507269800b0f500f01200017486240d6080b95038252401c1180d081200c00d6a040200c824a18022200f0303008a41078144c0200010740411b210900a41505900ca10654003607810310440e80d81e04026541280c4c4819040840c2ca0842e0740c0c400c5225100c580e29501038103081120b87c59200010303458a00040c00d250600c90301048104040e4002c0c481138404c1c1e504070000300116a252140e0b0036021484200c00d400080c07901e00003030355844400c9580301541c00c441c1c0090000355a1100c0c00c0080702e1540081e941c014500500c2e040060301d0800940e40c0c0343d482500d416036020304051041d82111582001880303103a0500480040e0103400c5015a41520840d030700e0701d076a00e510742e180c1040f18403a030401c0090318400042e45009200b00790054800c158956801051365559800400618000a451541c1d0241c8a00c00b41e0000a604100c04a035252180c180459400c0c1d4504035090605581c210944140d900041c00b44014446000f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 475868174 1250 475866924 475866931
    0x203010501060e0d02010807020709090302070911070b010e040314040303030209120d0906050f0c2d03040b0f071406090a03170c0307080a0b0616050c03460305030906 73
    0x42d20410b0f85080d0b40001e0101050400081e0500200300d0114a4441c402e00c4141c0140008140600059a081c41c0003507544507603101c3c08a1062900800c1e41c1080020404c40c1c1ca6181c00401d042c00d10f900344982183c41da500904205d0600c191005079401400b41a0090300040d406520010788482034a41403008003a8041082c001da60400720b803003101181c12481400c00c3e603c103481d120f07403034a5804000e1005032140903a65280341c40b582400c040341c501208540440c51f2819106c0d1014042d211000d10f0b034a0041c0d0040c98101207050084512144415024041c40c902498012030058026030311142810000d40b0003943e242c05c041400014542c11020a4002c2800711251022914040c0c40144040c0805408a0200901d09010a2010072544c10040d40c0c00001004666a00d1010494034003c1003410021211406807a2901943e490081400c010004541c0440014981200c649024460000c02002d00d441b1104146050b44ca1a0aa0603081540f207a200c841d0b6a081c145405850a600203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 475869424 1250 475868174 475868177
    0xa030b040302061315020906091c1401020f09060c0c10031a03030403050606012001050c270901030627080919060c1b05030f01090606050d05120307020a08030c0403020301050106 78
    0x21030700200064603085c10a001303034003180380060301c4444500005d480d600c1086440d0b54441241040e40780d04032000404561060b00c108801c081e0b449440c40310b50300740d01074000010b4902c40d09010b07002003410f21038001c0c20301031502e0095400e989a0080003951081d03001900c000041e60b5508070304118100007103660900c4d00700714001c1d41401d01c0e65464980e1401d004110b1030400018500300c141c241040009032003c040104000d00c454640160f2480c61500000300100c814036411403107056110049012956030400a441400582c1c256294000a80300426419030709416105030100d803284d182540340c446034801d12100da031301c3c11000c040040100b1101c2005844041c2c40c603080003e55000001c000c100d944c0a0001d03c9082d0401c100d5a10310302d51503200c4e03070301402000220030026806610104200d40b041d20308012040e205c030b0502004489844000b4002d500200d41c050420350000c000d1584400d591044500411165407040341c00d41007036903003008040000c5000d0046250a02415001d0b0106 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 475870674 1250 475869424 475869451
    0x20d08071a070e031f0920130e1e0f07061101060605040f0618030605150108010e0136060308270603040204150b03090d180f1e03020a030b04030206 65
    0x4000000340c4880c1001c14003460041c0740049004440c17540e401c9a040c1c55045048030396103898080300c005007184000f5440e40b00c1d54194000b10750b000c90500c5410300401340d405c001c1c0000c003003000c0c140200c5070070607101d4039191040d046040044841000050050509540c481080040580086007555030b29000a01449410320052280b407604016210484a2900d4102d41081c9540307469104801240c0015040504100c02c00503103226030018110803107000e90300c10309940e0b07840348078081c80da40a0140b2000080c0030000903100350200040e6003a05242c01c1606181c1b800d40c0c1e01604111412039104407030a02020601042d8100c404514614517540c0d1080022913070b210b03a000501a100c000e00007032140e9514416048851194600034002c1c05e00c3c1030149941c0c0c242000100e0303031103420204402c0003540c0f903020400340510800d844800c0320b0302841d031413401e54106456440704400d51a200800030b450808000050f13565965114025800733040c4000e01400c2c0307400c0081c1410300040007108440072 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 475871924 1250 475870674 475870697
    0x7090f05120d14090303160b10050102100b0105090307030f030f110d0f0201090b0c180609100503041407180b01020303090705012109110f01080f01050409020d08071a07 74
    0x50208101c4540a42440c20f1460f00d0b85058200070b140c059188410b4161001040c0240d5071116000c41c00720043c043e224011040d6200041a210150580152030044e000060102c0400c1400e41080e8502c0105040c07550500003880302003441c1c1030099200b950252850060101071540244c20381a0082003460030b00030301030b41c06400350f80d9041c40b040c0600070482d22061a41c2894802e50000c4180c5611540340d80882c100180b090100303800c441710504450f03607030900102c0c842c41c020342101e50140000e4a000c1580c44003540030340700c517040204140d0700e08481e50214000303002c062202034098006070752411441c8003413407010412242071820050556008000b8410000c10002d861001c9510905c0d1203894184011400c0034007600302031079507001c542040b4091342004007004203c10711020a031035507050480c0490044942c20070079611095144010001480141007980020031410b00142c00101e01207455500e05d90198040c1d030703060b40e55442aaa0b400502038850030300f960010101d2400c13080104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 475873174 1250 475871924 475871959
    0x30b0d15110a140304030c0602132c04020405040804080718051506031315020c0109060f060308120a060b03090609160b040e100305030f0406020d091a2107090f05 71
    0xf600016034042ca880040f000500301071040445514950f13001a0954548454490300018100380c1c0c0103d4a4040061913213034001440d0607034192210301c05291100701500c4039000d12005200c040c0090310040c00805c070108148504100440c0142242070f558a0500403056500e4203d5402810780424480d14184038007907030707840105890300a6650580c2c490040503e1400c4500d81204c00d403400015800881c0310025044190b10403402c0c98020b55051040c01c2e2030100440441c1c4490000a200d080700348100e182c04210b484220380c0c400038a0000248443d107a4988142c140c00844286425502050801944513814403010400007001c00c0c00c0d0b144241000307407401181c021401840300041103600001c10050591505100650304030013580e948040e42c1014404552150085601502c02c416000403218411344040c0c080360000d1060401c0c0920b234640c00b052301c0d4441c441c040c00e692003000c00f13185d10038036090080d0f00403816034640400440c605613040d02c50b6441da9002c2e0340f141042203080400c84 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 475874424 1250 475873174 475873187
    0x606070b0c0c1612020301050c09090c0a020a06090b04050c0d031407020103110c03070b010e0907140f130b1813030c02010c05060a0b04110c100c030b0d15110a 70
    0xa006032601d1038035540c200400740d01d00b01c0c1005020010b880d0807840050400752400311000c0144c001e40003400160345031045200f8502c242000c3c9a040140e060000704001d02c031801070030041560344140c8086400c0ca071503640c1901c010600c01d50300c8840500901040000400c0340301d14000065a01d041c0c40d101948024015036441c3c0c00380c241d00f00c0000748450071a03200c0d6200659145214613080d444e2240d041130156280c20805088543e0483d007000850f8650712050341500c5180c4e144000e2250f076042603070201110021440868000c003580c80042c11503074401c1c4120f04d0701103d141001614020a0041201c4407410400503119071200b401405401d43c2e548000159030341e01130603c403c108420b0320049810545103080a0400c0c041c140501200d4041ea400c1000644c03c221424400740000f481c44c1035007441040107244143d800a19022842c004a40005104440d103040001b00c400340172003ca4070100c10074904658910482c0490844e90b80030381305a03810f00300701c280804d0508134002000b4028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 475875674 1250 475874424 475874431
    0x150f090605090406030b04111c052512030309050c0d080d112208010606050408101a060f030f100f12060f020a11070b0a022d071d0606070b 61
    0x4202001560400648544d0040f800071a8000c80707a4a1501e800e060181e108a0f80050fa20f200d16510010b00c00c101402c55039802e00f140e017120141a50740c0d12f50740700c10a01070111088880300c0f40600700000700f5410090f505900503003e0389000c070380781d540c0d072078054141500450b0a0348545030102080300072481c1c6209680c903480741c540c1c0014270b81c442c1d4012b070101c078040c1001c1e5096201540c0ba0b54010720404402000454248800032700c01a500d07070000341d49034000d5000d03180282d030046200704000401074210125160b081d040440c1c00403000360124003a54404a500c0e1801100001805241e40100c82c0c00c42c1d000c60b1000300310519508082342c1c40c04085907403080022042050201c0000d102c0350740d0142e405604842021980c801512801034010101c4110300032250040e4200094405818030480e1245200340e405003030744940242101c800220310b00d0400e0010303081e05160201942d410001e40018001101e204a42310f100d0483e40101e240000f0403007401058148040e00008130f108005030b40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 475876924 1250 475875674 475875677
    0x6020102032404060302220f06050f0d0311071203091203020a02090a0b19031e08031807050a0906150215060f0f04050a061a120f040201020304091104150f0906 70
    0x1580d40b90b000500503000903000654845010303148040d10954106081060b99804e440501c072451310342c41c14508581580c45030360b800c41c3c151100c0e08090f1510381d08004c4541e1003400d00c64492140403484900d820000d41041c00e05081000070032082c55004002c0d1001081c0d58003048042c2041d076900251200039020009004445e44000b06440078a00d40240f40300030b501600041000100c1d4506d41d88540316844290381c1c001000041c000c9100c01c03441514215500700c2c00302807440e01c82001c03410701d8403c40740c07002c945c5020381100403032240d803202285001080d0b081e10100302c041c248010100035540c2500c840040d0f520001d8441d0124100449d442d9002800b141c40e24030703001c6d240011516200340030400c25401880e0004000745109583d00040a0303842c0c610b441c420004011000514506c110031600701e00c1180500000c00101144e04416442072043c41560f00340380ea42d04118040c6c54120542450896000c50300380070510741c032420407051005a2400c0c0c48605002403003c3c2070b05209014800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 475878174 1250 475876924 475876981
    0x6120106030f14031905040306050f10050f180a02040305061f03080d0f1401030b1506030a05091608070315111602040e0a03260606030106050309070e0c030906010602010203 76
    0x2002d494140f051700c0c04608426202110200f0f091070042c81948203020481e4000d2400c3c011401c2081e0010120b42b140360410b0540c0e13602030510003000100b07003c5141c140e80c13010050341d41c09019900c1c402003601810706140d0140c1c03038505516186e800c0090080c01c0040c49403101402000e00d0402e07085440031250030044c542d03a55100e152494000d440e1070b65910b4503107414401d0f4410803119625095040724060300100080361195079194106d004004660781d40400b041c00481e00c6446550302181c0c0017500c107021620345d41d1541004101c1c481c001e81c441d0500f5003001d0f0302041808000303844c0c8030300c1112108041021001c2400070803054001c502e07240300d885030001041000c41d1a154882d003622605002202c40089151400a280c04100c51071042803a80481100c0c00b83d50516080d20301a503001000c41341580c0c00c1c03180c100c2d0503410050054140d440386040010340c0c0100c152540f402401481c0c09580d0701d1501c104501d10300382060340801c0c11a0b104200300b000310264804074840c42986102d550 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 475879424 1250 475878174 475878203
    0xf070308060f06041217030606041802071a09010b0102060f0112030210050c0406090b070206070b0a0f110d1b2001021b0303010503191101030e0a050a080306120106030f 74
    0x80d020300b00c030702c0b1003d8100798009004a80807400b141400d9096200d4180d0036929003042254540e1800b090381c0058000c80284418008a5815029550411030502e030050030640251120003d007074441924044000c00e25082c13040c800b0080c040d2143d0444203000402407030400b03054000301aa014410b4400a0f9209001401094400c0c030a0303102800301c0d0700e000c0c400c506104103075030341070b920501c40c810101c0c0310740c0c5000540702c5184080c2d03a0072540081006003007159a40740c090140e000248110b41040c1d40b039982d281126100d00c54000e64071034000b51542c5407510b600b4060119084009422400040107040b1001c5640c0310901d884403203c5046008400c012090300c090187c0114501045001d038620700e003001b000c0c0004003542c12540100d00b11086503d2000e8802c20903000d40402a0103158004500d900b00d5001c5c1e00124184a044000c645400389903403100c6003019010720b41129500000428845146010615403003c05d00720b0307008010007881c581d10000700d0100500007d00c0d100070a00c20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 475880674 1250 475879424 475879429
    0x50708010302121509010203100608040507090513050f0c04141512030c010501140907080c0a050f071b050a0b0f071e02030d05030a1401050627131a0301020f07030806 73
    0x48000307415611490305145c100805454041c3d0012944203844c418019400241d01c3c0c03180b4051406544c0101c0034003402c40c24144903c014000091400480c0403280c40c00e800066400c210f4a050402c1f4400644244e803c10805c000c02d03200c519039440015400d050610906009510380ea400104080324004002d140700c0700120304601458840c20080e500c0c00d0f00004548900d817007098410802292000d40b81c2e41c1d0108140c0e4200c130103440c048a034140030311002c010780303004d07400401d00016412101030030140c02c1e50f5800603085d000e46020f640c00049002c1000340d41407406005c0098a0309020b8641004000300e900101f034000c800020b088044002d105003e24152021180309458026040d0b03140e03110526009407540e40140c0354042c9803461f00300c80e200308180884a0b01c0c162440141401c1c07801c00f0700140d08214031031420f060300a0340d804459041469650401240d0807140700040030030390241c10a45000e0b41c2180300c8045000e41d004101d9003a0100b203a45c1103900040e17140c10700f41d1143d100c4101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 475881924 1250 475880674 475880683
    0x4030312090201031d0303091005070804030f050417030c0616020a240501080714190501050a03060801060816050f010c1b0801020a030b1c1511090306180d020105070801030212 77
    0xa1210565850550001740c011020009510a02c42c100c11a0030b00e5076861066021030300d0440c1c52a0000e8400c3c0042400607100e0b414080d008c0d6824600581020b44444459003820300c81c0801d40e0300b0361300c00903148081a00512a0540c000d9a50031400d0354800170543c0a0742f940d00701c00d0002c203448440c1400701ca503080700307070001c02042c00101750400c00c642c0c603901460b688030300c107000d480483c00e045000002e49240018030310f0000c20781310080001913441c1c180150f901e07810000c00107003815180c3c040401c0c040824810040240a0b203c020b2078180e1089620035448803460b0881406007240c030443c0d00440e40c200c01803032861070b44902e02250340700c031030506004520300340e401071007007540001a03a41d03406503d9004002114011101301600000b01a03100c00400d0300c0f02402400300303281090841040c00241d0000100c10700300800c440c80c2034060000607041800490380d10481d5a480ca02c09021a0400c100742120a08030340001c00090801c140082c4c440e0071705100083c8968000b0403d01c2c2c2900d000d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 475883174 1250 475881924 475881941
    0x5040b07110102100506031c17150f010314070804031e08040b150114090409020a030803010602060108030a020a06020d060b07060b0312090112090201020c060309150c0403031209020103 81
    0x114580d864100c14901201c620715412402030051041a080c40240f20701445018042c4900400604003811000220851504201c001c0018008000b1040211100c98074080c0d01c00d241c42d1a010400e80c60341340070005242001951241018034100b9802c844a2141ca0031f00c0e080001810000440d554038901200c000f0580921068030f0350031202c0031010305401c200c50b240214800c101403155035480b101000c56407004502501d00180c9003640c52003028070207034010186140d011700b01103034481d07003600070810300c110a03482140c0491000004014040d8140046805810703060040c5151101021000f940c3e1400d002c009400e0f141c0c0050481c008507000d60010300100b20302007141c0d840d58110f0031721000816030403d569000740550300f050301d01400000103c900413401616041406845159010000c201d030840890640c421600142d82e1030b500e40c4050362044000708000d05080080c03480b415454480a0130285003501c081c0310520019400249503505e2284a00c03000a100c07000c0e0004034013808910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 475884424 1250 475883174 475883189
    0x2061f050d03080901060b07050c090a0f140405010c0e010804080d1b080403020d02010e0d050c03070209041419030c02040f060e10030611090105040b0d0605060307090305210d0c0504 80
    0x420004240c2c1040f4002e2060003111300030000c055446100344010702c02c00f84024095003150110700c88910b01564501d405c041040000594468191000400c4400d6400324007240c5855204102c200002409500440802440c04841188520303002034910759018000402c0c0d100c0216030025281c9481c1d000885040701c2d001e124904010b00c20340500003200a484c02c1d00103010f250040d0310024014000d50000426000050070b00b04924a0219150381010f101c12100303010401c100d038056030710601c2050245009070584018404040300783c9282c203000c08000c0400d001c140c0d4600c00840d80048403142d81a40646001c0b40b00e800780c0d180300000703044e250440c03800d200c050390501ca01c81c03450710041310550703114601c100f05181202c0190f00e00c0e8010304040600243c0208400d0180000000281c004030f01c2c1918040b4140c3d855400040c4aa082100d240c80080c0e00f106082040c04810000481c3c084c00d001402a1642d0b06420750a02d107100d601d0204411a85808007107003182d208404450040010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 475885674 1250 475884424 475884439
    0x2a0a030e16032a09020f0919060816020d0f0e04060305100c140403080c1207080711010e010e040506150403060c020606220b010507020414010510030c02061f05 70
    0x1a251801d20300c0d901094650906859a4006207448082e42240d00030b00c07104186141071811000002960107003862120810007400526120f461b02d900c00f0b426100c1101121030900e040c5080101201c1c001040000340c0004543c903841c80a4000c10620700c00c000c5e9250810020b00c00f6001554900c4d140401c0540040c84e01030000103012002c1032040684403c08d00030f0007200350320300e4200c0342c0e51b400e0901241549020031040001621850040240008040a5503404482c460060b81c0c150440c000c1a01e01310303000141d4404204000111910100c400d0810841580e0341c000001c103000341c005816402146da03907010594641d100310300446e140103e0139005e9a500d1301c0f4944036000c0c01004001001600c24000402d6140c034281c0402c0d00101644400074080c00590700c3c1038006040412840740c1400801c21800000d030700ca901407080c030040c0f008400c6420354546400d02c0400c04000082d02e0030149028a20038031a540400c8440e00000c0600b42800f11000d0305054902104842d030091703921010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 475886924 1250 475885674 475885693
    0x9010c0201030e0609070e0709061e02070b0a080103170412150b0402040320030705030607031505100c020901090c1409060f07031d09040c03060e0c03010f142a0a030e 73
    0x5000c0040d0f0b00001d5a14201e230322003203426501c1e40168095100402c404204001104155100c034200d091718510498121581c3c405a40311075600505203000000c0d8480d0041c02400306440480003c54002aa02482c05240c41d004500d0011160f00c0100900031010b61802c03d081c0c2a0040070300010b009100b1945c0b5503903413600441024270381922600001280345900c10610f03000c2001812035602401902d0f140d0340e244030840003170440c0c160143d50206000008a0036444c0d0742c2042d0b4030307902036454580103010140100285654141d00ca800c1040c20401c081401c103601202c000200300340504c0300d54403242c0031000039107039000351580b400c100d1601080750400e0550000824084c03040071040114200f261038284140c001040390094000318080b070041000a0382c50307004241c1e181880c0c0503a10310420600009007542d090ba0920040385e92240d07412401c1c036010060550f04414244205840c1c0400c442c02551505802003000355080c0012407480c9509000b0f410100a12951605441030f000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 475888174 1250 475886924 475886941
    0x1204140d0c0c12051509010f0504080319060f050d020a080a111c02010e0f010e0904030f1202090a0501110a080f03010311060306010c1202241f0b09010c0201030e06 72
    0x40d90310405032002d400004000a843d07125042c600b10068120019100c0f40d6200782d500c400308180640b045d4207965803001010040320301f91003800d0046224005250341d0b418109003601e012003c944143d10030515003041049015410381d07250048410076190350443c0411400020309206450344140381d103000e8200365070f0400500141c1890401000c48081d101e111000c140c03030b503014107852002804600c80650000042c58014107004e64440140b40043c01802c095000c5407c1038025501100411140d010b4003100e41e811180907034511062640441c01e0865810004c3c070b40398014811613041c002d00401002810800780545104290070035000c640c3c40320662041c001580c02407106480c0c2c1030f0406185a80e5107041400c4a01940d0142e683c819400b03520b4413405410302130b803090b001c1036104840c240001d4401103010700000c13041084c2d10047c580b9017030f104200c211031a40005900e9101c4540c050056064840075101092001c1c6440354000f6090310040c0d000740074894020500d4851203040003000c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 475889424 1250 475888174 475888187
    0xe190b0409090303110408060c03040609060e010b0405241e0a12030801271505042a05030702100f11070506190605062d07030818121204140d 62
    0x1072007590100419600205c00c91024055409000801e03044580401c011440d01d0028541043c015000011700407242c0d5030340030032180c0810030030603541d45409401c0440c0ca000d00c01da6a1101009541d0320350044603010480001a00241c401d00c83c4224841c5018000e0700f600c10305a501c24041d100e41c452540301c400680103c2803080c0c0031000901c00d00000b0456504000205504807a4000c4400c40c80141b2400100601804144003040041c1e14100044559440c02080039503014030305008080c0700100016a90780000506460a2200c204240468994001003450707080070100b400017601805c81000e50090490051206140c90000c22810b041c0980070503001d010350300810070030343d02a5161004d882640c2042c4280c1d9407214043c421002c2c40307441080d1450684484c0f400c50401180c8416400300c0c540c11070b00040e000500000c08115005103840403500404000c80b004000303007940e0f89801001e501c5411181c603d4400c1405c041003c000c01440940c49441d94001540e84102c80002c005050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 475890674 1250 475889424 475889441
    0x1b0e040605010f0b0403140c0a0617090304061b050f06040602031503010b1c030216092009031009052e0c0e090c070c080d0309150b010e190b0409 64
    0x5203064000100003031403c0e490821203289200960a00b851512004000408041c40c50b90b1340c040c40c002c1c0c220660b2001c10220207801d00c0d0b10354409003c51340350705061041d8010001056a0300400c0280080c5811481e582c400c1c0c030b40ca0320900405c81c118580103090581e0003a010507644107420500042010a4006c3d42c802d4031000258061840c5000826090f202d51200254200014801016803542070750804241c10707004e40110341c980500e406060300070140651119442c41c0d554080c8424088d401074424041a4642c0200c40c14500c1d014002901d4100c0b100c8261203969560201804001f000c4c8070744144604060700c072004103122000c1c040c02c0d809940d0b80c84604240303030940300c41078180940b01001080c0000740050900d903072076550f41341c0c1aa00841060b52041c07101c50001800010821a03520403080c596408a00300407149003000080c1c0100040042107400c02c141045107980c13241c140108010203d0303040d021407648245c034811404440e00160622040010080f43c10503140c1c001c00c81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 475891924 1250 475890674 475890683
    0x6040b130b150f01020d0905060f0f070503130f0311100c02030f06060405160804080c070b0c03070605011a16081308061006020d0f0507051903080a050a110708071b0e04 74
    0x90103c90000481c1c5450440d82007202207111100141b00a0400f0806000f2018000141c645414103041450f0420342100404440e03030f910026070701040119240300b0714010300b800034111162900715510307e021003101a0361075001d0900a440c10110761300c1225003c1503690050103503030645812503030841e100c420442c1e03100e00460500001ca2416417840507420b00c603c90a03aa40440798403155140d2100758010140314a1602c1006404103800030b1083c01400c0c2e0981482c021907a0b6441446c00c0c4e01030713400507440142c244501402c01080ba68a280403141840007981180202c0401840c01d481507016940300c2101c01c040f15103000c500c40c5c82c000f840c1c03405442e039024603400440c3e8490080343d40e1590728a0140008402a01903030b01c15002d6800740c401c40307208005640c0c3c3c0360320f081982c400b40c06104c2000d400207201d880030700110fa030b458400c0710b4215517100c0b0203200c68205038681090074411f800000b404400002010000e00084c2c0c058900601800c016198a40303640f80b654400ca00d13425034041c0d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 475893174 1250 475891924 475891939
    0xb040f140f09030306060a030b19060207030c080616081306050c0c0f010908160f02270603070305032205120a17070c05090a02070614150d0506040b130b15 68
    0x4112050003c1070b41d124040040002d4501148100d003140603040c80c190302c2c0d4010400e4031482120b40d02c84184c0300040d112940c01488a5440c6040008800805a01004c2d640e008034050000c0380085038070f810440070141c2800710142c0c441c0c20b92411042c1195001400c01c4d0314210500c130a4200c00d00050a40e1031044044941402090a0032802c9807804c51004145050801504105002c80301d2501d00c040d011740c000c040301300150f4001c151514a0480f2940440c0c01079030302c0c1c132914800070084a40041c0190000d1181900315610300d42d60b8810f0408080e0700700c464101e03002250101141c100d02400c2f015000000f07582106201070344d2001e031041d041303590056950202c41000420801d54030300b940c20446d100c810b58a440700b40b01083c4005051120301c1e90702003080401203001406942a40900500400001c2c541143c600340c0340181400c600d84078a01d0304000b54081180007030a035070000d811148125503529119020b1500c14240c0c40021710740500700341040f84811240d0928195400140d8014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 475894424 1250 475893174 475893181
    0x3090316150c051213030c06091101030c050a2a140102210c04031101031409150a1a06130e0a06030213060602061b130305060109061a030106030b040f140f 68
    0x43c2c400c0d00940307002c10b0b85814020000b48480d03001030901c6944038000c2c01e14000690a42c2ca41401f6148081d10959400d51810180d644c1542e02d840707062541d410703500d0f00d9420403840c2000207003100c0040d03600c01d0f00c022100d0541e0184410301d8030840c00d1260322003550303150250b900f40030502075000503030f9800c840025503450582c404800d041e0a445030010b00e60f0545400d003540d07075085e44403070307200041410181d5a0001001440781122964003504070b10000f8106102041d04c2a41c2c0c0c1c0307800401c4a203031907007001010300b1500900b0801c0400c120048550a072242c404030903018008499506c1812042580c00c140001ca522540c000c1083c6c80c0243c4102c0c040d04000303407070441514031500c40da80041c0d102200003800403070040c240a104048222a6504e01119102d421a000c1750b00c0d0000e4411750401801000f00300b050380300da1300007040c2006d0740c45a083d601d03012040750b5020500c28001403589500c4000a581c0d10303540141500404401c080100103c04540c0c1d040c0c030030007150a50300b5410200c010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 475895674 1250 475894424 475894427
    0x70c1701060501053a090212011505040b0303070b0106110c2202070f050d03020a0210050108060c0a170708060f04060b180a0f06052805040b03090316150c 68
    0x107100c2680c4060b1a40b6103800c4001c000a500c01202096040e620030101c9810111082d0840007442c903500c0c00000800c0c3c1c0040350040152024000c5510401c0c3d83c9028951003001c02000e1030300044580c111070004100110401207411407058200c000d0030b0101490001c110990844003200d801d1901c003044800c450004400e2140c85031000c0440350311041c07031724031004084559800a200b42c40c480c0d000420b00305115a6058640559040d20201080d00401c910280c81d604024001034034210380340901003545000c0d44c3c60303103070800a007811005030b40001c0c8146019000f400038043c400381d43e02e001045454640c0005183c080c094403014412100e07011041070300c1c941400341100307403050384d1521483e00d0b9020500300e40c1000c41a401f80c2c8c01802c4044005403044003c0c140c4401400180c0b9042d40d80d0950320000042c800c01210b05d20b9038060503500fa41d200a41c040300341c9085c0c076042102c4a580344c846807900c074694003903414801c201c03016041201e01040305001d110f08030300903005000d100f4070307114510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 475896924 1250 475895674 475895681
    0x71701061418030307060f0b1c08090d021f0f080601170a0518030705030a03240b0702010507140706030f18061a0901090b181303180b070c1701 63
    0x1904844100c003401400c45040b0303020005419614000d040701c2c42c041d9155118800d80f104680031880d80c6a642288034148d081c0203240d03110f070300c0c40c405181c044e40609071f42d00380c15406941426130188140007202402c40d11007210b5407003041014a120542003580c0b0000400d6948a10009030010f4108008034010f94000c054000d24000410b000000c2c566a00400c0f400900c00186070a403010024849200c0f075075800e00082281c28000d002469a4500d085005005c0c0c5010424100a01544d815803140d03448400642506440010079025610724203400100c13540e006036040541036000754900d40c2c40061000600008031101601c0510800464280300c008480e0346510315000010190039010014840d0b41c0f14065a8515050451142d01c0e03010200701c0c1c580302600054513050b030b619400220713032070906900f0315510745022506449140c0107200d54048207460300c0040501900d9503c1e0a880c150100c0c10380041c104e03110780d05883d00b13002e0512010509484c410900f6181c1441c45d2010007900601 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 475898174 1250 475896924 475896947
    0xc08010b060c030a0804030e10050409050c09010f031a040e0102030411060c0a0f0804030c08060a0e06150d240f1d0d0c05010e010c1710050a090b03031207170106 71
    0x60103036040401d841c10179545100c000703104034104030381c402d0100440d90b035800100d011200781380c1d242500c03142012540790031520094840b12070700c1c10500c40c80d0000d80e400808070010300c02c5072030003242d01c0c0100c004500c1000076040040d50b101d820310800351309040c0154007940c4a1400f07002a001d0380c2c90064244140741c400c051a48803190025181540424265840c403181544160031240c50540d030703510781250740e0400d07030031080154100000703100046580740151301c09040b900700981345504007a03000e119549034521495003c0d0a07441c040000b4003035000c200114404002508844e50842c0015a400510400645a41e03241c0b901d0303003107560620f04150078880502c030750000700611820700c5000c2d5034110003200c0c02c032440e40d200e4031038040c094428094156585440c0e21960180194455141e100c040001c0001d0b0904241000c00c00c1340e5903d604004040b248035980006500682101003800d40c0300c6c002081480d0351050090182c1258080312407082c2d19085120808680d8884034100c4429440c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 475899280 1106 475898174 475898197
    0x306090b01080f0606101701030303052d0402010507020a031407090c170403030f02070609150e03030f040231150f0f0308070c0e040c08010b06 63
    0x810045014281c000090000c816a004585540741d13401485644200030341c2c00d8000c0340328007610035030b00a0144806100490768483c200a006814103451183c3d0b00c606c885414517200701405070303900300501010346048160301c4e07039001101da5400c451416613001134103a0f0000000346484a020070310f8020301c0090183c8a00c0d1012031710440b0440100101802061610080c0d101c0031100c4040e40035525080000f9802c0003864000024010741100030211b03450134140b4010f2100c401110030408546000605c44942c5400900d5282d0105481c595105c408050100d4014036080d1a0320340c4c054000883c19000000c0321388150402c0440001c05000c1594840c1846000c01c0000d000801410b08094980840c1d0301e0401c0d00324003e9124400074200101c0454208104002400c80e2401825003207410780c2c1038103240c284070006551398840e00d4460741c600001c3c50b0340e0b42407420580f03201d010003 = true := by decide +kernel

theorem cover : BRFrame.Cov 475719424 475899280 := by
  have h0 := BRFrame.cov_init 475719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 475719424 ≤ n) (h2 : n < 475899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
