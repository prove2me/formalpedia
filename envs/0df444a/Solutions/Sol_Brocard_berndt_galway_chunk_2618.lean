-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2618
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:14:44.862092+00:00
-- url     : https://prove2.me/submissions/9d476939-13c7-4c8a-802c-0d288f396545

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 470683453 ≤ n < 470863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 470684703 1250 470683453 470683517
    0x40c051302130504020c010209030601180c0305010605071b05131505090402100503150d03030e12030106050a03020d061205030c1c0801061b061a01030e0304062c0a09020a 75
    0x21090102d468940c00506d000d0481c44005420546000c00090502800f84c0c0201c005c240400001300c3ca009250155421030506424104241c0d8907001c40544240300e41c250062a0b0140035011860b01c90000000030040c14010b0030209540d400c40c6130580c02440f0614050242d0401594001420310b402c03a0520701c81d5501400100080461500c1a10700c0d0b04040c06070b02e8034a0603411010115107a4440000c1e4072800ba07500410071480b1243c4540c203000300c00310a0041c181d41040180a640e8201c02121401c3d155881c005130340b1244500c00740002d00c0250400300298900451041c1403104c0000601541c4804006507a803007084000c240c040094814045000f2a800200400c98580205117444079803401c08010b045801c0c05981c0c4000322400c4454100c0f600044c1d09000700a541d00d84230307454003840440300a502d85410701c000900320302d410303d5070040c8046084c400501400300400d03a5118416014010184071602d421a04000e900400710032000502c0742c0340b0004c0804100f08915000000d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 470685953 1250 470684703 470684737
    0x30c0d05030f03040602091507030807140a120e0105090304030209090105010302130207031707200303010f030b07110f0109031b020d0605090109022d0102120301062303040c051302 79
    0x1c1103a1102600020410350f917080e428014080e0f03e458540c090840007111030301842c2d40e1040fa103005000c07000050061130404c00d0300030b8124240c21030380f022a004a610790404417082d00d09c5164801c05450080781c0d0700c6095003883d0500400c8a0f0000140003605d10855001802c1d6503146840c9003251024407003c1e5010741c0c11208982c0c0b4002503802440414081d2070181c031030a400501030124500c05460f0000050302c0e41c451254105040d21403034000208407005140b4651409249131410011030001070107800000002c08c02c41405580883c1c60ba404103404d40314668044903600e17000340340c0910700350f001c96000790705841100c10146950034600c0d40207045211080e06600c0740e00082c40f000785490070b10b40d42d410075200541e4490310040e0f24600c4480b030802d0b03943d06803041715071401d0718460b2160641d880950008650440304003501d0541c0c5a51418013502c20b805440800b80302e001c081c0c1b0b13440f0490004103000a0040a0814900b520000e551042c0d010075400100f00c2244210140c0301240404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 470687203 1250 470685953 470685967
    0x402010f020f0d0c0f060515090105030102040302061812060c070b16020a1104020d061202100c0507090b0d200301060605090312090a1a1207180e04060e0d030b030c0d0503 75
    0xa00d4031a507045e00070300e50440941010768031401211402c0e254060140104002c03c2c01c5440e0030800c03540500b0302a0025800d0a1440d400300d031081c00b6071848440011132a2000191940b60340c040a607203c80c0303003400c031062803d018a0428040d03004c00c0081e6020300780000001c100e50340c0348840164011640e8000c0100c03080b20b0304c603484080c2e5105903d9034410303020840200e10300c1b1b0702d01521000e481c41c0c0c41c03180d420015030f104002042c0c01c903e40e1003007446841206040424000318103c801c4881d5071001040401304440061031048604100914079100043c44180f420042e074907000c080030095000300b20042c0c4548007038071540140085164950310540044200c2e0003400090301444001074243c42d0442d854001114030040130709442c42c040d050203e0303140c209031030f400d43c4079811074040e044c030b614103103d43e082201105e0b6450203003003071061400f0049801c20403242d00283d5040300101c2500c58444081c04000c01600411407114441d00c1a01040d00140c500b40026410260380031005601d4218 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 470688453 1250 470687203 470687207
    0xa18050f1b0a030608030c0f0c0904030c1b0b0d0203273a0e01021501030506040f02012607021203010e011401050f0d060e09060423030d140402010f020f0d 68
    0xb00008260080645900d800600c001040002c0c04070b10312000c014100c0001d84000301031601e0301c100782042c4181d0190044c08040b03500220480301c1d142c1c0049858800e521801802660501e031640807601420000621a008640a90195001d403207211400700e01c0d4041314541031a03001015581c41010741140192850640600000c00600c01d0a4944000000a002a0f192002845492101c046080c580e8640c00641e810300c405600e001c0f4031800c0c0492541151a4165150402003006050513081d80e020020f40e070281500610036285a54480202d20803620040c7d11b803001503400c0009880b42030b00c0c00c400c0215150969044c2c9245160026450b864482003c03040c08141000f5030510800f003003907065507490100100030600fa02c030b00105969203045010284030500a1101100b03405c003206000020309418940d007095540c2070355210080350401d10300d41c10761044a617514110380c0740002242019565210711481a8000d8841c00103280310282c0c166150710507581c0c1c105450300001041c100c554 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 470689703 1250 470688453 470688457
    0x102180f011403010b031806070905100c290105030c0d060903111203010608060f01022113061d010215010312090e0c030a0b010509060703030f09020a18050f1b 70
    0x40d10500d458500200c01412006040d03100b80c1004031200c50000801c2541c030b9840d09a13090f401960001400c0f03d240c94003000301340211600580e0b01c5568408030f030900c41446100c804002b00e81106180c88a2800c1200c00440002640c2440006103508400000c0318503010800740304059001e418802c08116964424008009443c030403014003580b501c0105050f8000c0000c02c0001c10500c4840e59254104000613140c08002011f40344614120402d8a142da40c1c08a003414222800a94103c9480c0c0000240151030082d804d10328407605c5e01050004800380d01500c516480040e04c07240049841c0c0c02401203840303204182d0f030509403450b032400400c001140c001c04d00700000389600e00391207004d40701c48600e40c00f1a001d0f5034003251420f0100510402c01c600744a404440c40003400c08a10b02000500881c299000d0040301034103041d526441840304951039044078410300e500130115644103031640001c070803031030625484030030080c41c10700060b03118001d00704003d000d000180d41c1181d031401a0342c0181e0707003a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 470690953 1250 470689703 470689729
    0xc090e190902030708011e0b0d02010512061f021f060b0702150d05040605180a15020c03040302030609031c02070206071106090909060612012c070f03080714010218 72
    0xb44c4999240001d00f00c200b8450341450048405010720102504048141500e03412000f4503c51181c1c100e02200507a085811103000c40808000302e072180e52076000040c3c022140404250400d41076081c0c0117807255001c44c0004e000c4400041e60441172040040d500210b8420340911448200300f04128005840c00c1e8034072203040c0d043e06d400d691810340700440201c20f580b415541107541da0345900034000c0101031006a01c80401c0d44400078180e40310551541c02da040459494044010790020f074507100301d0342c00d000711400380d0b4000c1c1c11070f2564107020b01610341e25480708200400c40f0070f00080c00010300045008a0380351540041c02c00d802d0040540b9015240d441c00c0c0307a8254000c604000d00c0340103413622aaa5880380305800f018104518203c014800f032a000c6820710800b41c0d00d0206544180700c51003c1c1084940c407201c00512801c810000542c3ca1700c6500d801035000800900d400004000410005020661046503104441854540041d007030f805017030900c1c50006c0d624180100749041120200c811 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 470692203 1250 470690953 470690959
    0x3090402070c17071805100e070c0209090c03070b0703050301030215070b0412030506030304050d0b0403030e0f0d0314010e0417210609010e07080a020f0f0406030c090e190902 77
    0x7020b0750f070316110544860418040c01c050b8000c10b1040052200c8494041200b55400f0414890340c5805410541c0b004000d020381101c0310844000300300821310070328005400c0c6602914900c801e0074010440d1b0781e60382244d885503100f413003000340119040001e10155404180c0c1a00c41c2400c40c4d08507400c0008402628248100c011030a02150000c1088107080d540114011210100c6000c40000d0080c00e40b900108424020b0340200820401c644803180f001c1c0c9030fa600203400e201c1c991220328007100a0401031305d414013a807082546600e002c00020552010800c220780b0f003000907903c00c000c4080b0780f050902c516060070107608001004a050140100390141c03d80d80e40314503096840c031301c1c9074901c4000c0a11201c00340208081001c039044c00d24241307014050b0b05000f00b016180c80e80d4020a070420040841c40e41d160041140d8464107803110503500c0d20204942c001d9103640e00d82400500900611066400207045c100300022609100308016001e084820045e031003140c80700c200c8002500100400b01e0b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 470693453 1250 470692203 470692223
    0x110708070816021f030b01050c0c220606080702160e0609040c030206030903040603060f030f0201140904050408070b0a0506010f0f050705101b020c03030307260906070f0e030309040207 81
    0x8016600c074401803001024904040044410144e0028110740a18401c141400004c00010111840000f04040d0002c005c0f1919401803034000b03e000815080040700280d042e04121000c00c10700d8111850034070410b0240e08a034951080040c178820400542e21400700001034580104440b030412807400f980c4980902c034880d0141d9940d13808100300740d208a03190501500081010b0106a40c54011000105860342c0c0c40d89925003152607a092081482400a05110150103280c41c17090028058501c0702c40e00074009c000918107820006040e0748000011102c002900000a81c412510701c60240102810b0b0740d82e10101071403000541d16102000000c100b800001d011003000a002000360901c02000b4260101d4020705e080b0800c603003110041b41920554205699040541c0c03400020f0b01c1d0b22980c1c0b446d01070011040c4c08020410100281809101d94003c0010040360110003e503e502500d20b5a40d2140c1400110000700c810400c80a192a810740040240c0041c0d807400340c000d080d00d24040c0401907 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 470694703 1250 470693453 470693497
    0xb0103061a030a05011b1e0503060a03140a150c140c03070c180c02070e07080a0f05040506070816080406091a010303020a0b100308030a0e10020a030f1107080708 71
    0x64548007580504403280c2e034507254010780f506045910b803000c1c4407150803ca41038101021047c8040100d600129080003000700024525235110349107075008642049032100202071454041c0c0c3c8606043d2000e5a080360044c107516008015489080e1240190b5070350500e50029456040003d58800e03540c4400c0c1f0f1006005c207401050501ca221402468564922061031071801060000d44112403640c03015500250401c110130b0703810085040d4444424a402090380ea680c001c12001070140b08917034040c0302d18101c100400c11800081d09401680705440d6201c0d1071381d800c46019000312074800c04000240580010500042454000c50802441186004d00c641d0103098209040c00c000d9100f0740060344a242001c085c0f02000810b42d4001c20b521541c3e03100f8609580718003000307205c00f85c0282c210715034884000035925418803601c1102c0402c403100b50340d1140c41001c014050519804504486d1b860594256a0310800d1003c1b030344442d03401078880f4140f41454441080607008041c0c56014810629401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 470695953 1250 470694703 470694709
    0x806031015080c09040c0902090307030f12030e12070b04020a150f03050c031003020d020109090c11160530060a0212060d03140703171003031103070b0103061a 70
    0x24000392207646900504140380407520351400d80080920307030042c0c04c90350501c40803440c0d01c1041801d4660a480260b580c1e52010b000c28a00031040d80003071301700b201900184003000403032510000110410f50341888141d0644000741e861b08060050003c01d1a002c101d06000a401d0101035030f4000d00041101c4903155850800b185120100c1d103102e400202000c8404186d550103208094201284814003421894184425407168001c3d00001c0d00c03800307400d800c40741160b00c101003801c0a4035201c84c041c007800d14180d0010b014049213a40f044060302070b801d6a1075208511003000812610018003c0c910b0305400303c105041d00800319031801c80e584080469030603c3d4401c00480d401685007a60042e9204445090905c240c500074000b18403601081c03503038174082035005241001c102c044140080d500c502c1d0317140c20380b514508032001c2d01a0020070010401d410f1303080032030001180e02a46482030b6901b404501d6585a1084010041c00702c1d070341e4001403021400035030048400da0343c18192518001140c0c000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 470697203 1250 470695953 470695961
    0xc0b1005042d090201031e053102010804060f0c02010203090d082a041d1005040b222403021219080d0e0109150c020a03020303010b09010c17070c1403030a08060310 72
    0x402c203207840c0c2080c4841042d040500000341c100c9c95040b0f003411114040d81c5a04441c10690290410010202160030700195078032401c040300145400304001e181c0d850317020b030103900122147c84140c01020302d0111101d00512566204840d82080c442c1802141d10002030400b0003441c0e01c12050400b4040071808401003041110940c0410210320b4041c039054000c2c04540f00c560300030342d01172410700c91814000d4480318810015444000351005ca000f46081d002001085804186403800e660544141d000c0c2e00081c014070140d900a960300d5020350700da032040659038000c5041301c0b41300030101140040411910700141400300780050020860391282c840b4642580e88400342682c41c00001c1d0307180201148284100052143e4a0002e4003504507140ca010b502d900051040c1420403070005501811a803241c51138941d03803a0320540d58210f4115174151034007d900941d204460344002107401085643c1e15000c186607101d0001d0045180c64103d030021650a00701400352500b601c00d5800308250815030340a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 470698453 1250 470697203 470697251
    0x20909030301050405061f0c02030f1519050705040311010210050109140702060106020a060e0c1f02060907050604050f18011d0a0e0d0f0c0b1005042d09020103 70
    0x8011078a075410201000100c80010300624403c490060080e0001602c08040384505e452508100640c1c807447c1c00801d0401140f40314030f84150040700380241c1d55610700f0340420f004403102c803080322040d101c44404800b00e440c2603c01e4030100d03034103000030030000d81450746110f211001071050b911410b0300740d2812015554280c0002d600c103600c0304240c1601d080d5002d0200d500c05610300c020426545015030182d2a800b400b0b401600440c1c40d41c011280c14a41000900003d66000c1c140100e4a800d11000c514040041c030780110040c00f98101203810b0f5040012000140c5900401d000c0c0b501d0702d480304200d040f01d00398021640106401707600c86900303446000303014002c00000100841918082004106a0100501042504e0301c1d144183d403c008001900e52098059818900c1070040056001d541e50792640c0340c000d00d0740020808000000390400d40c41421604151010b128480c401c00540541a002c009145100c00780003000742420070403074200d20314140c018100050441182c1c020f00b1642c0071001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 470699703 1250 470698453 470698471
    0x70b0c01110f190804110d050106120311150622180309081015030602030c0403210305090a12030b040b0a09150b0c0a0809040e01020a0e030d020a03120203130209 71
    0x4034000f034808400303040400001043d0f14000946180507174070584480c0218607410302480460302410f042003825030061004d403c443c041e07246070440506e0010304644881c0613000b414052440a507150685c20207030705005d814010060390014644105101c0c171030402d035038624585512110800c2c0000c1e02101c0010b031050081e5100c445823401c00b68214904040ca41461450310702e88500f01c8100c8607661080815668802c402680d030382c035500005142c9000716013020b0f19107807002e40404600c1c040c2007001c0d140c042254500740126a21540c2c1992a0202c440025054148561003901e0b024800e911865080d01c0090000403200b03400c001103115400560402c0040e15916010b01d0110140354420380b0040090001d0741c3e24140c2030510b09503d400c50034000030040c000100c0c092800d9a11600300c48400540d0340000c40d01c41e40301010080100b02d42e0300c5454000d000344002052518800f00b20151380c40d070503841c0c80c0c8035800c0707090b20702009610082410b070168000326034400040c0c0d00c5c254446e026600e10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 470700953 1250 470699703 470699707
    0xa09150903120f0206040818030601060503010801050c090612091207030c06050901020903120702040605090f2e0512120304050303010602010c0516030c020d02030102030903040e0a0608070b0c01110f 87
    0x98609540c00001a2400c9424001d1000440d400c0d0ba500192095016a102c7c6459844011010341d00c0026a20071010381d84c14014036002294003903101003d141240c1c0c610000b07005e95191555510211312030300040303a4110404014040380a00301c1e22a446e002048002103501d1000a00c5003c0119002600101c0000d014800040309204550250350381066038140210f19110700d010001c1e903989071490000d508003101007203090a5607620f034403200003028050032010040c5411005c0d900a100f0842c0d4920020780d095026148610301c504e07030201300841201d0b208448030b08200400072040302000e20b0204a01c11041c1d404114285500914007807813048004548950405001901350386a12464008008050144e02103c0c1e07200003200480a40504140c10840400c0c0046441c400752444c001c0d41541c00003003840301640000004000300c403c0e13030b803005442d6103802075102d040d503005120f10b805a0b80110350a101984140009000100d095400081c4540c009100752030072303030070416101c1e1081e100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 470702203 1250 470700953 470700959
    0x60b0a231807110705190e04050f011508100605011409130c0302070c0b03071d0d050708030a0f050909010306020f1308070311031f0c0507050304080115080f0c01050a091509 76
    0x2c104c6003000e031104995024280c400c030000d5030b1044440c0d00c60f0303000965140303000c1401d1100030701c01b0380c1c60081c01c071009200c004e04038101f914607200f0310302c03555900340300340700f4508090358581c851013007503c10585d00c0031940c040720329002c00c498110400d000d0f0b001149440300000d0343d0b4180b05210406a480c1c0300907854540c1420300302481c102c3d590011468020820030820000c1d4030448501481001054060000c41814082100c900845030010315a1048680105050a000000d016000c803142e0b074010001300740f2141180c0901800707142a0f0000358140040c0001041030f00941b00010a107401d040c2003004640c0c002c000b00a2a0b44042c0d041e0304040300030f0051003000c148542d8400000e4000b0244985c0010403180e010140c104810703d5213541b088088030143c81601110481c9030001c08032501c86407a81030080c001c01e281c407107820250034120b030000754070100480c000c60001031120142c2050042d20006455540c00340030781904200169401140c80070f49078150300c3c800e00c6280d8400d00f140741 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 470703453 1250 470702203 470702237
    0x12020d061814060a120609030e090a06080d0203090604090507270603060b120402010e01020309130f0509011803140913090203060c03060a05060c03130b0304060b0a231807 75
    0xb40a042035000d907901400c107004a40303d100000c1e0001d41d102000207000070701818101d880c90041c0d56241d41c0003500744288054118180c000509482d810000d0354402d00407040d0a99607441034400050b040704003448100008841a0711150307000409041c03d05101c0c00d0102c000251800c42c00004804013422501802069032510a800261402a54051500d40c115507120b40c03448001300001d040010807038550120f81d2091041c0c0c2c0310310001501c4a684100169980000341000c41018502945803900150301c2c0c2005020386009501c1c0301c2034415400c80715031001c50392000128182a00c50508200c1d102003500c40300d00d01c03040513640110008582e8014030400d4205113010302804410841881404050358441d031508080310f0040300c080b5950b0154002090a6010b1802c0d082c01092821f140000d506640000540c81544218800c02200400100f040303891034560281d1420300b560310107115511a400800d00300040c10041020210140044107001507120440381c42c0c000404588403000030003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 470704703 1250 470703453 470703491
    0x30901052511010f0e1b0f01090306050a0b030f0c0f09010e0103030f1e030509160f23030706020d090801020f04050603040f12030b01030609060b0306040c090f080a2112020d0618 78
    0xe80c0481c1c85214481c1c41f040000c0816545001c00b4290903918808a1010000c2c1d5001c00c40803000a0243c3d60003680300c3d014181c071500d0404500b07000f1222a001c0c015140360941391503050391050010540f00d41d007546c40840b0f0300078000e10b0348401c4c442c0700003001617125404900340321103141c541e60100300381c81d02c00360241c180601c50805a0100040f40e200b40101030a00481a003a26004010702a810302000807900204071058002d03178043c0100d00c8003060040c7c0c0801e62301444000e603119004da02c8c0d83e50000ca400c034880c1c000c0040741d202003030100b44550728200d002141c101c0d002d03001001308a035071503e504140c42804094503010a6079108510841d50f01030244400501c4c0d200801c00500c0c0c68101201c3c040d2000500851299035100b40340a85140901031a9000c5d2542c45105010580c542a001e607031072018400940304600f81402c0b1880d80400000f070000500c101c0d0799200a5859145500c0c400f9411880070341c1071180c1c450a003c50445946490105a611203074004144080c403854224002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 470705953 1250 470704703 470704753
    0x9050115080603070e06040609020c012309060609070c080a021605040902010903060c03020f0403121b12080603211c050112030c020f04060803030901052511010f0e 72
    0x402001010002c240d82c022413141d045a04860303207890f441d40c900c1c001030000d008640281d4041d600c082001c0f801000c0550011404281c0040560500c1c95000740c00701b8010070441e05080709900001c00030b42e8a00740307100071903000703003c500b045241e00c28079030b850381520f030800120040140c3c00009030030f035000819229100100011b880c104018030b0290002841862a0300014044039200e000e4540040d2090381111250035480700388030b03102c0340c42c0c0c50702042460140c04c034400082e11013008004220565586049040d60040307045100412034081641c0c0b90300000c0016a15008030204481c2001c0700303540b03030104004118409a40c80c10203400d4045004042c0c10300d40009490070005000451080f0b03002e454403605402c11400c844002e1002a0800e03d05483c890340190400e14001480364000003e10701950000d002880301d40d8aa80201e03510180411901001c80e031071001002485000315030071010603146800108207044070115850650301c610050403029400000c550540d000304440e26111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 470707203 1250 470705953 470705957
    0x9090f0402011d01050703080c0708040806190b0906010c02040b10030c02070e0f010e100506070c091406030304090207030309020301051003032007090e031204031d0114030406090c030c09050115 85
    0x2c03d4000b030000810500407020010248081c820110391540341107803c3e5406e590380483d0040d42c403601d030802c1c203031510007e88201503581c00001600c6000000740c011712980030800743c14000c4903500d40f0011104c500b4451416138010f680c1e40005a40c0d511001218807040b680c0751008614010109402032038148180d1040c09040c542c01c0a00c441c1c00d01150407241140c0340c2c01c00b046060b84a1005551b403440032a4455980b12000282c16400c00804044540c11103151403820070804d047c80f04440c0200508403010790703254000700814414603030303542e003d04a040d000c1d00d4009004ca840398046400c6820542c0d6181c0041c00d903080030820140e01000302000112012402030b0380b001841000c03a6181c0e402c0c003841c2c00054503000ca03c208850304000b9039000701061403a110702c0d41032038140601520f01c2c0c01e0b550205000600a2582e0079401550074002034000b01c2c900602d03543e80c640b102c1000304008281120b00300301c900000000305101d1580e6402800b01201c002802d5494045100b038000a40981041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 470708453 1250 470707203 470707247
    0x180910080c010201020f0a11070806070f08090c0306060103150f08010605030c061321080a03150f050906091b040612061a03040f1b080c1206012103030209090f040201 73
    0xb034210054025901f2115540c18a2160b5618140a00e0305144083d0014029407141c041000181076011103688425006512201d0740398882c030401c0e9444600110320f9a42542c03015021078410351099002015000c00356820300411510b40e01080200c3e407040e80107030309903919640c0c107100c54501800ba06130703407010440e1444d103400c0e010700d195080174516203d18500402156031800400c0c80c0001d0004260b5070203d4025070b20b4004200c054010144511001c4100503054404501c02420803581c100b622401803e0405503034074170b810401e483c0700c0203010704003c0c0e03020002c04502061840290020700305a440340181000440380b0003080341c81035400501c8240d02012030002c1804010201c03600203800030034005803011541441c032069400e4420240c2d40b1000c004000805450115080083c40000c440c407005e00c22500c88003030380c2d40c0b00c00e00400c52100c155200d120515410b10352a5046036110307080250402c07091900240140200b100c00b0f0769035561800420003150b074032003030011030391065102c444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 470709703 1250 470708453 470708467
    0x305040c150509091608060a061b0804081522020d020f040902100f02100c0e010c0303060306020d0911011715030c0a060c1e080708180910080c01020102 67
    0x203450808921811241c030600030034401d10203200741c003190580700c00501005a00d0a007840c0042c40c011550440b140001c000801140b1545421103d440480b907195950008407005180049070b044050035003206e88800802c40003413068001d000751400c1c2c00d01c120641d4020314240c0c000e54102441c0d40c00305400050854940401640e4940300400c0b0550103480c1e061a145074080442c000705100c00010394041450300000307101a170301044c034403640d03030980d13007aa0b03180d13009a51201c00360744003603605c4c00100d19503215103041c952050040c007070310364003d150205480c0c0d41e80d2030b40b00899121980400200e5250648041030119550b4460346aa8081c43c040660030700000c1d00d404007181c007074402448000404410700c1907175402c100c0c0c0d0030203801c0146001c7c0f0081d0707140303409030142c044104215640c0c03101d030075280f104080850103d2031301504420054604070040e40d908150394040040602c0000401d0b40b41c01c0e03a034990140c0d042c8074410742002071080904200007a443c0c00350080c6100e045a004200304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 470710953 1250 470709703 470709713
    0x3050910090b0106031e1e0e03030906040206070312020d05071407020a0902090316180b0102121207110f150c040f12060b120102090a0e013219080d030504 68
    0x50f4115603e6140004442c0c05850a9401c0c00c142020070743c2c0e0250900180000c0d0111304541405a01c002c1034042081c400008107154503404101c1d00c0e481590001c40015000d0b0410400070144541b0910300382940f04807002d141000c98100503018104070744c1c2c030070130400c880e9049607521001c1503000d0850360404c031040d40050f801845c0c6016080405801144403da0f6031000c20500041c0c1c00141751400903203031640a2400081c0c05110b004070a0350070294a86519400401e0040700707031104410061808000030302c0031600c3c40c0007608903020001403007000702c11400180030004071203002c1409014005c0000341e5010b403200c000b5101c044000e00400c4200640c042c0c8044a408941c0100b4801800d401141001002880165840e50b08900c03148a224024413040d1700500c0c50900442d4181d141d551111502d00705200309000c0c10046018001040400100c101d00110715a000d001d203500c0c40c02d0f01c0101080108a01040301d00035400c07081c0c801e10652a040c0103000003451146070810030f0f0710700391710f036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 470712203 1250 470710953 470710973
    0x40b0714070b15041104060c0c0510090303110a0f030e090109060b09041d1906050a0b0d020d06150815010e16110a0b010b0c0f0a05100c0e100305091009 67
    0x1a03034004060a0f810506481d1500b01100d00d240901c5000c0e10303a9625003000e818940e15140450320a0a002d40204262501d1140855030f402c1c16680d0319012401d50381c06a410046105002c207041c4940d005041c005800c15840805142c442d83c4d900c80c03c101340070b0500034501d0060700480f41c0a410004144540d0501c18140c600d01c1d00122408074100d41610300c01c003a60010752a00e00d0450241e0102c01c2c00000b41d45060096282c032071101004290b40381141d00c003c5841860449600010641000025145c102038107021107009510005980400d055021355410940d07000c0700c0280c0045910140300c1c0340b0b00c541c5a0041c01065000d0415203010012000ca40c01d6103840c1205011400e0030046284c6010040030816591180290200b56111b03407020a940d00403840c0e50740203208034602d4040b03414010810b5002c0a0b8400002c25034441083c107136501900c060510502003005041100245644600000010f0b007129100050b20b424401000750401200f032001c0c403041c1d402e10700c10341b00042036049 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 470713453 1250 470712203 470712211
    0x302121503190615060804030f03050c0d020c010b031c0906020c0d020d1e062007030914040f02070809091f0605090a030501020a020f0105101a071406040b0714070b 72
    0x403248031400491500c0f00007004030080c03407203d04030141d10200d820380c2c102094500aa01075241c548903000c1c0380070200c041e2802141c240100c80c8040c4010700001c2403907000b92281065000010136040c00d1000402e150043c48429240342c8008011881140b5410a0090700501602d201a100b042d03c040f010510b0740c07440010003806480c000b041541800451003c00b502120980c642c2400c081080c14450050100000950103000e00341d0614145446020115001e55900d078662040140c40d0a14014183c1d69045040390069100d804c82d0803900350074401030018901c00c500044d02c41240c6014010503030401440c01000e00352001c03500728440030321104941103070818a0074070340d02c95003200420640c0b0200d074401015980041102c3e05490340101b114083d00e95860000c0040384c1d52442d0400010801703120310142484c40c11885454036840800a0000b1400b540c0c0c500006006140718618203d0104c0d0b003a13800409407800d12052540c84460512000c0d03e0b44856410301070661140710344000060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 470714703 1250 470713453 470713483
    0x8010503011a06130f0b04050406090c1b03020f0a150c03021c0203041109011d06040605100c1b0b1309050408030612210d110f03060d08090604060302121503 69
    0x1c90584c0c0e409071381d000040050b1072001d00d40180c441c2d98101c40c0040e40c009000b420f02c510300700300d008190002540726681c070310b80c001e41d1601d444071052010814944000c14040c0c0460250101202240f041040201103862240180f0b94800841c03024210031034220030355450405004010603044482001c0c40f0100301b03500e46500503500c0d10399180910b140c0005042c42030b00708102600000724510786035174180c0e07100c10b448140300d1746a8407041004111115802910760000300d0007070600b009445940c10780b00c0684682446980c10901540e0b5400c0405694080441c0b020001008544c10010382102c030007c00000906100c0360070a0755480409000003131086000b4043c0c80c100400b140130800c099000304c0703c00b440d9001000e8510f01200b00a60111015161540c142070240b4000c500000c12030b659042042c0c2290700710340b10301007042200c000070170741918402024401d0080aa86110040c030040c10503460060b03031890811a189114a002080d04e401d410790344903406841d03140841c40c0c00c619046c038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 470715953 1250 470714703 470714707
    0x170a09030311030a0207053a110f060d0915060b0a0225141c0506090d0206010e040b0c0c0d030603020a0b120406020c1005010e010602120307020c011818050708010503011a06 76
    0x81c141e001c00b41d4103600c1101d0390820780150005140b804545501c40d5000d0120709d09020320074000c0c0403411050101361600081d0030444d00c030b610303000c0b5480010003e1242c40d65000d014490010a0140d8185400c0b02e03010342d5001561942c0c15804201010148122500c40c0d003541e20003008011000d0b42600c00c404c0d03001801c1c941006143c1e81c103005900e46200d580103c094000071800d001e543c1d030300211506152072248205c117050240c00012054100c40c00c401054405581e90f0303440d030310020809000200303102403e0020803c0040203122a4449d80b450350f030300007203251950041050400113544000c80079201000000d0380500d140c012164416000040540d4585500207a02d2600c000d00d44400b88070b03882c100011070099500a2814100c0300a542124185c015003044504103100c241c0e0b44101507031040e42200c9065000c0c90308034002210070b2050440d0680d8131034500c0c1c100c1d40324100310180a0717500c0c0104803040740c0014282e405484150002c2040c106440d4140c40c03860040ca2800b4401c03000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 470717203 1250 470715953 470715979
    0x5070503160e0604110409020307090306050907120f02031903021b04020c0a20150301050f030d170606040504020a030f0507110a03080c07051c02010b0607030807050304170a09030311030a020705 85
    0xc645c0c201c400520100d041107699180c10703a001403040c0c0c001d0200322072640c1480d011a07a040000540001510107680e0140c400411641e21041e01146002040344c2602a03552030400c861440340d0003014480c082d03009032810b14071040340c5404000004c0b81442c070440c410b004144802d00d000449100d40c503440b20505141c503c090402c03400c10703440a07400c0d5601205103542c0c20340c0d2118101c00b80d412a01c00b560b0035078180030307003404240c3c64402030080d1100003414144004060b10180042d0f6420690160829143c9904e590120703080e07905c03462020300480d4079101c040391004140c1c41802e5000303a403403914a1868254001068554404400c080e0402060001085035115a60b040350155a400001c903030b00d002800302000c00002040e0789040165103454003140040c14080d0840c0e204d154103980704083c3c1e80d9150b105955907040540291001a02048820780e0040c00d24020301c1010f801340c035034420b01c43c607514000340302c2440c0100709001a003041c043c0460320341d00081ea10040c0c1d8001c9401c1400c02c0b003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 470718453 1250 470717203 470717231
    0x3060c1b1504082113211e050d05042f060307030c03020c0d0f0f0309120809031201030507141504060c03110d0f08060402030403201905070503160e0604 67
    0x4121901c40311800c0c501403003c901403901060051511411043c5100c0b080c1905210f0384079106040480401d844900043e1060500107603801c10341101d08242c0c0c181204a48094211200bc80b01201c00d034034511034815100001480c007662030440d1940240c503404108004c10f000b8003028019806045c4ca90354091081802034050300c20b44500780048920006141e88014021001351f039a44001ca1100000700403840e10074040e1400b0316030880351000030280c0c03d49080f200e0f03010003482c40c00103000a214038040101c503181078900841c0213000414650b81400b40818148580c1300c075284c81400d0701182c04000e201c14000362421902542052110100b503800d0540b01102c0342a0301c0c03082405090b0740c001810303400c150403020392100c540d60b8181a075906000c3c07004920090b0350103030200f060f01302d4400c1105240450321100d950b042050b00e0101203a02810b11800240440071200c1d0b800c01c800502c52070600b0007480580c003440c0c56400c2e80303280c0740c0410441412006001180215141c911864100d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 470719703 1250 470718453 470718487
    0x114120f0609130b2d01090b010c0818130e010e0606040e10090c27061203120b0a0f03032d090b0f12010b0702040c050a0905010e0a0503060c1b150408 66
    0x241042c0c0456019004691070305e103c00d401d02502d40c03980d00d01403090a06500c640c2c4030300d441950000d00540741c004100d211700b00c02c40340000741d2070b4030030316041c2e5504140c110b5004410760750010500201354000d0000c1613600b031000040515024a2610480005035030000030701d10b00c404841d05002035030440606220070390340f50b1a000303141b10001c2042064520040b2004c03588044030440e400b000100c4c0c95004141d090030b0351074002340c0001e025040001c1111060f900541d1611001411000f520342d580030017030911202d9034000d030003049100c1c82a01d0b028440303900c1c841160b80b1701003a11551078440540a0718800c82c500644411b2240071442c080f204100c00101c40c1c0d44584244500003039a903c0219580503802200201c1c0a1410701c0440d10740d982c09002a15100b9601d80c446a0700d46050100441d0102c4458080651041c2d00400009403a1001c0c85144d00400c40801c0c2e16684050200322078030481030b404148482a03200344001130480307448500c842d0b04280c1c00861503a8030902c01c0d441c0e007400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 470720953 1250 470719703 470719741
    0x91b02012306061b07060201050705030c0a0503090a02031f0b090c07080a02011e05041101020a051c03090b0109020a09080d0210020901051317010e03180409020114120f0609130b 78
    0x1154114800004e0b040c00010100c0c2103c85940c0280300655845c0c1c4110748a0009a462100414041c49413441181c040c1002d1540700914408544c50381b8001e400091400c090301c0b110a001414400c0c0d00041c51085001d0004240019589400e00f42003c0022860078415040d0240c00d003180803465241041c401e401140345d800610f100b220501c01c0010180c0300a0105039022254261001000c41072940085100e808041c1c018000d860410300c0710035101022005088400d04140e03588501900160700146047d0207011300c00c2c40140ca40400c10009040b00380036421a07030482c0c2c084034031000600c1d4006200208400102005a191034902006840034003641e85215400c00c400c0501141040e41c055801d0410300304000240000b920001c4825142c2c400e01418074018072fa815907001c1542442d0b0803680182c0e1040c035146000340105403d10165070882d02e0142c01c078000440901c40c407140f8445c41c9603080300d001c03101f07183d86050505505541e000410001031001240000140407070340151244000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 470722203 1250 470720953 470720977
    0x5040807210f05010b040f050f061207240806010c0c0311041e270218091509100b0901080c0d060e030708030a060806060901090e010b040204091b0201230606 69
    0x501411890004d010300140d02182d4015454403001c21581d00701030082d2401691003040307981a87d00c40400303104007030342034032603000360381c410700300000b401c500e21011007c045002005028045100910001c160003000b07011181000814510785021030140b6000c0c00849520180001240340f4010108018000205100703662034841280c0c0c0c003140045c2e4100c84001500324686120040c030550680c00d200205207000b0f500140d010345903500f001101000c081e0003041a404032031030181c0003da0f21b0020b1404407402c00458000a10020000c4030318051002c0c141c0003101c84034002d42c18114990b42e5150404035151003203041c201c43e5018032589500c040350b044c100d181075a0740c4010318204520198070950301d01e00841e1070b00600060700100820003902170003000300300700340503460122140040c3c0441031a04034155640c05010340c450303403207100600c01080200d00120300d003035002c900042d103600b40303040800c156414018054034612042824484400003000c40ca1450740710000407400d180254000414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 470723453 1250 470722203 470722223
    0xa09020a020a0f0b0a0f1505090a110a0914040507050307034d1e0c0709090c08210306150c0d11070f0e0f0a0905120301150504080721 59
    0x2808013004080744900c00100007441000d800e007400d00101c0f104c0740302d40107420300100c405100610382680d10940000703111101243ca06103c9030882c0b06640909462408a000000200803844414101740304004c006c40f400c1140b4944280c0181241c840101030700c04065681c0201e003c411004500440104403660010319050040700901c4007030a60030515940b0600d040780d03114400d0040c0011100080101200e001c40008007812080c1283c10038402404280030b14400400c070b0303c12600c64078880c40e00a00116501a1501d981c89040c00c6010f0519154105100c0240c06410709000460b83c124400b40e95003003030240d03003201445481c001c1ca600c40285000e0007840b000d0180d4025003130000e41d500e1409613036505581d08811041849503201748200c0d00c103098000b410b00d003080340d125580400b0301c0402141d41e04031071742c43c0740c10161510b02c000d644000110051040f03003445040301c0c22005560800c03a1509003011030507940ca912038030901c038580c200200c810f060380300c00b031240901c081d500c959003407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 470724703 1250 470723453 470723483
    0x50607020304080f07080c010f120203070e04050703020310060e041104171c0c1e08070302011d010b030a081e0d021207030605061605030c0a2001020307020a09020a020a 74
    0x944035032243c840c40c4039074425010f40c110640400700b041d0b4110340c2e40300024903040c0d11440055401d0140c82100c0c07000c1c05102001c04d50010010b000461040e0a5070b503503846440e10041c10041201d1000c2c4c0803104243c414410040035400030f0714040c0c141d0b03d072030030b181001c1c5601c00001000b80c9100c51500a00308004600000d100384c07940030910404401100f035528501c483e002e03c002d01210200fa00c000603a2103013041c4d01040001c0b6410401c001000048014010342e41c803816566402290f003140140e5640b258507440803040d40a00e00907654040092102640000004c0c0d50780900410223482d0030f40000300351a0300592905d031480d0450104030b1450300d61110a806400940000c0c8003030282c05001d50016178880c2c461312030f05040d40d0005003650304202c66800c8165881a46800071030310740c0f1040002d544000b100b0401082510f02c210346030780c000994440800c4120107040045410356000344840780050b0794401c1e00105640d00e0780b10050b200c41c410b0310100e24110a00d000a01f800d903040b2044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 470725953 1250 470724703 470724707
    0x709050c181f1d06030c0a0309020f04060602031b1902010e240a1d150a03060b130f0806040803070c060b19090c0c030e0f0402070204050a020306010807030213031707050607 76
    0x31549a14904801410990384050091314401202d5a0301d0201d030810000c088076000780d000424050000d803441089050f920040b0381100d01642005001d64004a030706406540c00500d020098600030000c9d0501c080c02d004480c660680b1120005d05010489c0c1c002c4000742c444400d000140c040c80c5502014101000701c099207a0352004a41c0000103440081e4101d55050107500d01e0f68105000c2c0240e071030554075003e4451030703402c880d4a2008064480c81e0000d400c144090223880100303014141d1600203840c149145d1610501c80d030096140c0d0704001c0400000c50000000d40e9800540b0742440341c1c80060610b440ca005040c95144103a03c00540004240311600ba600d41c001600c90605013000841d104e0401651803403100c1c10001c001800301146d40c080e0342003580194a000700050700c013609008440e4002416284100c0b8175804c2594044104803180da031151003e42c006032241011854540c00114001808015000213000044c2003102446004e2030030b011214041d40200941d4a0345c1803140c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 470727203 1250 470725953 470725967
    0x13020706090b090c0907210501080601050315040803060607151802040b0916052208010f20072d0606050f010203040b221a0a020709050c181f 62
    0x41e038210b6444400255402d0002440c0141c41900a0a15035070b41d5408000700ca804850070f0311244411a00214001c90400d9809824081e11403000948541e6041c02d06162411003d05610007550114805200100c3d814004030790700b00f40c0030750340c056444c0207905104007003640010f250400302d440d00c002c1154603c01a02c03022035542c0b00315010b2202d4040d44081103240c100558540120264005500d42032501903002080018100854480000704101180c074005200d507200b206035944440c0c1010081080d48500141d03010406015004203040c00f40c604494060f40344000e0881541907900680d41582c40390080900701540103030404180d1500c6e183c0302500c2540f103440d0182049440c007418030340c0040701b640d0540e07840c1545581014006402c880039071204688030b04c0c10100075100400d4a400b80a0380c4212402100c4019680396820302c0000d103054080c0d07010042e400d140001780a03031051440c00311200c091044044205401c0d1020014407101c004100c00f5114940c0c2d03100d00c000c9103800481b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 470728453 1250 470727203 470727221
    0x70302130504060b0a180c111e1203101203020102070609030c02331e1603080a0b1003050915090705010905090f01031707050a150b0406030215070213020706 69
    0x30500c0030504c1301040c07010129003030282c00601c0241c40640c040800e0780e50b200344a16907a5160204800c0c686508107403d14000101b00800d4801d54003079800c41c55000c005407410705010100072481c6290008104200c074001d4016103151146940885051500c01d40603601000d0b04540200b104000900d0040c18002c29490102c3c010108143c01013600c60b400c41c11080030300c25054001d40c502c1382c3d15a01e10705c154001d566040c943e00d1060420b03d0001040c6024149889508003440c02c1d0403500d0901409280004204a80d0b460404103400e02c03507100d56400048130a814117000c00e558540c00b0440d401e0802c0400780300d0303080107185c0030406800800070760b030b500315803003a00d0787d01400d03884e001402100501101c0c46c8005401c0203004100040d02410107602d070802509240b070414089039030300c90078422211415600300d08141240c100c681154811101181c10444081100301d02d180e012030401d180b0303e00717000c02c0b2035408291402951150050101c07961400003085540e0511403411034002c0c64200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 470729703 1250 470728453 470728463
    0x30b0c0d062402070b0406110a0c0306051f05010e0105030c0909160306060503011406032706060120061603060b0d0501260c060d0e0a0c03110102030403080d02030603070302130504 79
    0xb4194000030380c004100b039820703285803003c0c3c01c0ca0241004d01c00c0d01c49200a00c0c0c03070700491042c881e0b4000821000d031030313010241d0300c0740c4004aa6420002c030102c00703a012031060a100049845400c02c0140c1e04552200c4501c0000c5c01c00c152079a842d2081c00380c0c01d0246c1298643c0040010017008501c588824905c880701d05140c07410801c003505d500086401d40000d01070b011040070400c0709a9030600c0c12401542d80042da4403c602e0a007192100c10302410f52549001c0c02d0580d00c9a01031006642e08002e10301499038540003111080551114074a580b16000751410f401c4101c00900304a05610a40040300a0520060003558408840c0880001442d09100b140b03510501c44103d01c410003010310300e03000c10300b10f00c100401c0408070100c1040815030144000200c803030340d0381d404401c80140a00500001c1d038003442090201624505120021143c43c14001e8115001000148001000c000680311007241c4072030010388942c0c803040402e20780011900003952047c8006240b41c0b1040542c0c000c13500c141c1c410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 470730953 1250 470729703 470729759
    0x90501021c020703140c060f07051504110d061107050a1a011505090a030f0813080f1e03070b0405030d0b0609010c1b0b031003030e030c0a030b0c0d06 66
    0xa200788615008041e2024001a004000108003003a02e00460904200741c10081e90307849003045c070001c1c2c0143c0c800c004d42c004102000c500d03001800b40074030008003084242c0c4e144651615140d9a4406050000c0000d107115581a0b1070700800e0103041d80c8410100c414459040340e42c4e0700716007840d80e92a55116001c0b107461413450300d4064500345900d0190b040f0b4003010814488103100b100150780384c0d0402542c0325004500703024000085900f40907075040d51805040855542c600c500c10340b1140450b40d803c8002a90300045189440f803400040b00940300c0c481e01e22820320007007402e104604511a0407070107007518100009100603c080072009140200c00404e04000b0f0b40020024840380340110f4400c940400c03001230340b400220700340c08003051501c00c00500464900387c41d440e400700c00e6042695140c81404000105108040c2c20000340504010102e000703100e800c04800006400e00a2404000c3c1740390090b0000c60003130700d0410103503a25010b1420782842441e4540d0720b480c1c8458088a0f411009001d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 470732203 1250 470730953 470730973
    0x110301020417160e040b0c0c03032814150103062c16020706030b0d0501290904050703020d03020a05100b090a051b130e0f040204050903120a09020a030501050709050102 74
    0x403c000c12080f41d0b0151060303021035482c2e88504840e020001d00d4140504c10420110341c650340140001c611582c3e41141525846205c071075100c20703010a14400c180c6251038141c4035400020540002a88080c1581602200806100049019107111f03442480030302c54100300840c6444001641540100c0003000e50007155841d041149004103100342c801c00560001e041c01d11181c1c1c4a0b030005080702101400007900d45030740c0d03070314282101d41c50051101c2184d07040c16040c1b5a042c1d4080b00c5161490300322410215428141c440d21344551503484024401c40907100e02c641010300900c454069942c106081d0790a90989200320f8024003040b1010300d210790944800604000da0500c101030042205000e912704e50b624040d0510600e51250103d00040901030301d000924900d0f64007018450103031146104135904241c41844107a5101420b24180340d00113008404646c42c09402082d4000ca0950022503118a10b00100e0000092904094119420401007080c1290015800350031280300303908540304898 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 470733453 1250 470732203 470732233
    0x3110109060f0807090e0405010501030309090b0a05060d060f090e0c09150d031b0303020c16060c1b0306050f0f090c0a1e090c020a0302010e15060607110301020417 72
    0x2818040c0c1c502207440c01240c2c07450359100d80d100c2c981c00f082d54100700340e0f8951280c00103420450119000c9529a44600041c0708140d403160621000b4206c006061040c00b41c070b00c002510140084c01210b02a0b07501040c820402503441e0001070041880102018040b92105010f00141c4404c0c100c1c51201e11039095510154204011070350b1107a81d20755490140304406204012000c950582c0c1a020003a02c15200c104091119207104456486a1001a51524500071141c200390031008002d06541c0d403084100101904006480d241680c041203c10402e0303403030420150b408070103400151a99141030108007652507007003072441c080c200b16200e05900e5582c9203e51550b40320040b844a420410050003000409040b440b00300c401c000c1104100700e103e44541a803411620b000f10410010f034030040c4203009054084c4262940141002d000c0c0c491401c41140000e410000506240e0082100040413801d114200f110100c440c04001e00940d542c681d204100b4110030b2910004004c1c2d40030303181d1b0340e0b10501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 470734703 1250 470733453 470733467
    0xc050606031902041e1107020405010b1603050a23070219051005071a0a0c09151b030e1003020a120212280606090e090c090a0e01020d050c04031101 65
    0xc002031840146949a0f501307100281103002c0008107004140c0402c02c038942c070603006441c42015000c0710341d13898071011f00409c803e590060f0310003103520800f00720307140f0310b01c0e0182c803d01031141c2c15080880e9102c000c114122071962a2a800e0451179047c64060402d48407443c0081000780d00031104117070101000c4050600e0340000340701d0641e122548511000b0006c1c041c201a0602e80d0207020000604443c0c2c502110301c0340300c00c03601e41070616030b903100e070f8003034640c0168840f0060143e4034540d940b0858100e03809451805103214007071165000d6081b110070581300760386500380c5d08000b500c0e664015205e0b031800b03800703500102e5507900032800004d00e50006e0191071090701c1e8058403010241c0f0031a00d640324201c5c41e8005509400c00d103c0e030401c081d20011a001d010340d8005202540da00f002140c0b8113003442204085c05451180160003140229003144c1c1e40c105a1600b08a00c0c160010b544c0e840003252034020311910b50600300642c1132408101c00e0302c10b07403005081103d00441c0c1495560603210011107542d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 470735953 1250 470734703 470734723
    0x17160e040b0f10030b04110309060c0316030510080f0606040509010b011e090519090b0a0303020607082a0310050607080f1e0705010e010608211e0a0c05060603 70
    0x1c0711540c0b00c21042460a0b80c802e20311007242c1d04000075a103128001203030550b031410201e8031500300000306105e83c9007000c2140d030742d00040070754500d4110b0170075907501044e44102081c00707420591500041001c407540e24421400030304010049641d010400c110701d540b16402107903500e10a502c3d0100181f40f49d2010300a080501c5016956440d801915841d07084019040409000802c101c80701c0200c0c01c0c0e25144c5419010800140c0350030103240c40d01d0841c500b40c0b6944813200d40908030074502040000d8000440c15008461400c10f105242c0d00e49190041c0c180500c0743c5010011a501c00d0200e80004030801140035a1454042402950700c61050003c0da1190f420001c22480c4100055146902d10b5409003200001c469515040448254040342d419049840107486503599086c41e40003441c000d00c18200100400f10103003101da460824405a810426000505101800103118070303d040380410101002020303c18081c1c131a582c0f040e000b400360740d02e0070044601e0310440d004140c1d01d280010301c840324 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 470737203 1250 470735953 470735959
    0x1f0b100806060a03020c010209040212010f14060d0c032a1206060e10021002071514090c01050f04030507031a0901060803040620070306051501050f030408090117160e040b 75
    0x380000d00f04085000b548400c0c0056150f540c00c0c080c811480e900c070300040140ba640000201155410310f8103100e442800c03640051201064250500c01544410f000c0d1518034078004c8000640e446401420b0380580308440c0381d0b01254010841e2680c0c81f07488404030084000c2150b480a2501c0c00030380c0744904a51850007a40c1c089840c8034035018151a0110020304500c0291060315070001c032442c141020ba0b0458481100c1803d0144000c0400140700d22540714001d1000340700d00d4050234160300381901c0d084841c0c0b400d030412200042c650034a1071140c0407103000f15441b108882a040c0c0c4c9040840050b0400141c40702035900300e2000c5107444405020748001d641c0d03c400950725091410400350703914100b00c1d01d014610401019809820401071040304000d5006410105591822918401030700d402102118140304051080c0071001c02d16100b9a90b210b0741c440b410a903218103079801a600c1e004a0b1064412111131041082031003400c3c5c00b040801042c8580f42e204503252110100400c2e41d038401a6250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 470738453 1250 470737203 470737207
    0x81317070317040f18110703080105060a0504081c390c080312060111030c0a060506030f0f01140a0b09270f0703021201020f1204051f0b10080606 64
    0x1052802c105400d1100100c03942c107182641d507090040c00c801c400d81c4003400c59140d02c05603500881c1c99004280b140c10059000501e0000559030160008006025590044001045000c0e170640500c040381c0181c04002c1c1210818132412160070102e5441d50b120000055418241c4450210100000c2c1c03402404240d407005102e8554022600d03c0145840a6603e414418800501d101d028030007082080f0380050140060b240400c00905404842a40d9581503802008040b560f11004076060020325800301c40480c207510f4200000c2d240803860200302a046c0505034041020780c005610510340f444001e0f03100291903a440c18080201e452081e00d03540c110b00c8001c0040c084c079200b0308482030b000541d08605502c40035000445403500e031003103080341d1650384100020700540c98000d480d66409403042009528103111080340080c940240b105552802050001040c204102404000559040708902590b1007600211842c05016000850741c0100c40d1815034040c3c552007407200d03c1c803804010304114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 470739703 1250 470738453 470738459
    0x150414010e0403050f16020a050306010b1e040902130f090216082d0d0f2703050702040203101805160c0201020c0d03030507020618070e0606130308131707 68
    0xa030041c60001c00071810010100485544001480050304000c0d5000740002a0509980f050060076009a08540d00c80c1d0b0000d030042140c030032103000f22260104071402e0f29080c2403006034003804170b00868104030641c0e40089005048a11088180030880380d441400c11115960b800e102000c0344a207140c800c9204c913420a03000c000c00d44000c01054100060910051000304880c611010004d1042013112a101c0000d0581603400684c05151600d0756002000c000b0740001c0c80e036003054400100314060100b080e040a420078107000e4000e40311aa40c014209540d60319190340d40344001d0013540151a100c280d1001342900c0111103200d4184641d00308501100f010680c44019107010b040240100c7c1184144c01419803140c684603c1c0c0c1e12001d00c21f44010901e0b04109030040c0c24400002c0180f0124100418110b1b58010005200030072100d400c10468004e40702c00020900c0da101d00080404002c1403c02c0000030480c942000b402c01204022803043c0b100e807036100c0741d58107050012100b509940300c50014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 470740953 1250 470739703 470739719
    0xa1505030606090613180b01020601150c0515070c1e0f1707050a06090506070c0b0105061b06091005010f060e100306030b07050901031a01020d0e03011e020315041401 73
    0x1408083c00041109040000c4540da0040c1d5003465000190b40ca904c40e10136800380441800707800020f0000b400500300302d40c18450000c49400006196808000702c504541d01809400e002032501c40d40740d101070105500d41020050207a13150385408540880c0c0c076200305825180d111100940e40755101030350405280c40c98827480c100d00840081c8002581c020450b0b08000b0b00100900f07020b032480740e1404100600c80741095424004000c04600078085004400c0f00000c003a00d01981c1903e504a480301e440d445c50b06180ea40b1f030032195034160220b200d58814022140e10009160b005503811020600850ba2aaa45074a003202c01d446400003041c140d180804092801500d920030800310380c900002c10aa6075284e0b0358584070180c40b103c0201d02d0000b03280810303580c18000c0c901140382e2041d5161041c142c2c41d0000b0742e909001e000480410681900c10303c81030703400f074210000343c024000494141c0039051074558020360090741d80001c440c01202416400e42400c1c02103143c8900d44c8145111181e19185007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 470742203 1250 470740953 470740957
    0x50409121101020c0708161d01030f0c03020a080a0507141509030c03061f0602011109090601021f0222050a0303080c1e0304030809060f01141207140a1505030606 71
    0xe034001d00c1d502031240800202e402c12051004001c180000c061110052200c44200009908840640610004203030040c007000041241143c1d84541038404215140c28454000c13035454000035880500b482d4001420900069a945018010419103412903540c0c10139125090090103a203800c0495469080c0900441002070000180050151440c0a05440009e4108030048404031100c418000f00314251840d6841508050082400200940790b90a0b44409a601900069a204d01c15001c0091500c2e44203112580388500c41c0400310044150007110b540c0603421030092498400e0031810600d07501e10042e242542180d102600c840102429a24210340c0b0102c010248003180900304600d511a0302d50b44460b0322032480030400300b038480c101894010031102024050207083c1c0e201d2814000c42003c420441c0e4112103440c515281e44044c0a408201200c8d4844d80141882c002d01a000580640300026103145090485d40601c0c9030791901c1102801e1441c201c003120020f04180300282c21030400d00c0c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 470743453 1250 470742203 470742227
    0x1140409170a0f0507020102060109050c0702030d0509040f09080409110c031305010e03030304210e0319020418082703030a12110724090516030c05040912 68
    0x201045520345034807000340166002000300040c6400003182c14031998441d02c1d42c40340c00240d10381940f030300a4030340000350f0300c2d00107000350704140e0b40c1c8901240103801032100b1070b0f54980c0c1c05410789840c5c040c521005880ca4001e0388007107001d02e05141320000082018850030a011b03034041125420b02d810074101d20002d100b940010310440104000d00c0c12101c030701304003402d03940c14041590164141400300041282d0020140036020340d01c14010b010005034000002c80e00d040070a120342180004c2c0758012034059491000c0250503000d009115205a6014103410300b125000390740c103001004601020080894050001501c120011700903102c881c80c0c952820b1042d0014041c81a5040c5070312800281140d00c05407005000c1900c540712250450300d40e02400200c092006052404e11a890f16440d00b03103c1405c000c22148603900041c44c40810603a400780042c1d6801030200e8841c0300c0200e4890103080404c1c0800d42c2c204220f80c400252070310701800351002d050b91007408859000c50805003a1020f01c1c10306 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 470744703 1250 470743453 470743459
    0x3080702030c0d05070f0e0c0d0b01050d060608060906030c150d060f06030e060114010c081e0c070303020c100c0201030518010c09050a0909080a0f0c05030a121a090114 74
    0x449903850781c0e5843c606845441d000713502510216140074030003c2803203603070351218030182c1e004020071594114001c281d8510b40141c0f00c000c40c1030780070750004966601c01c2c015017001c1d4070300d000c90105585910200c0700341b00b0881500cac0c5c2c588680b40c0c40d00b01943ca11b80a5212948003071010800f11400003210003800340da010f50000491016140c8410340f608104940102001036039a9240d090403040c2000a02d0042580c13500341141039403141c000801c5410840009032000200180c1c4c5c0003660301c5000185040c00343c00001036164100003203256181c1510744019070051140c5200e03c2c1041c40d000e0110a1076200a403104448034400e0b900550180100804c000c040c001070901582c009002130081140b0303010603544544644d41441c04000383c2400a40068440b20329224074a000503c1901c1120181240c6042c410754000a1950480384517030b101500420500012820ba12800e0b0889248400c211801005001c0e50195540c00101c0e40011540990300070120401084110f019940c00b441e48d040103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 470745953 1250 470744703 470744713
    0xa0f03120605041a13061404020711030a0602040501020d0203030c04090c20061008060c040326040303080601090e04050a0209091222050108090606010f030b100c0c0803130308070203 80
    0x7580043c0031a02c4e0066001c009a042e40c160034280d10b8140d8001c090501c0481c41001528100f500b100c0210741040a0a80203690006454040c840c440009040300c090090459840702a546403420103034106108890141c8100074004d00400e0002c82a03900c942940c81403a41410700d042e10702e10140a0154880040c40307030010450300c6003400381c04800300e9850200b00410f0b281c142a44007208401c1c06034840fa0241e00030030103000d0018641000c88040f00d4002c10030120700da074021403100380703944650520050000009400010141c104076158464007090701c1d21041e0942c0c56519119205088900030256001401c0400040c0340046000e50400f61200403100d8488129007902c40306d074410892509811a07007a203c0d240c0140c0300d08032601510b402c0c60011094100140c0303540c0d8555000c0e104a0502440fa8404800c0600c00e030720010b2040c1c001007000d80c031140003070009403114102843c19a546041b510020405040000490b01c42003e021068454546141c0301d0383c041e80c0080c07030102e0b418060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 470747203 1250 470745953 470745959
    0x7020409020402210c040501021b03070503062a070f060c091703071e080a1d0405180d09050d0f0602070f0c060807030b220603060e0d030e0a0f031206 66
    0x80e603c05030200e9a9010b244482c08540c00380b0303030100d10030000c0c112400ca83d01000700303001d2664041616211040042001041c9866440002c0c2c100081900308940503c03d270810001542c48133076001c418034220035826000c0c039403106c1c9030781c0d4a407184c031001820008608824100140c00c5034082d40e004907103403820f5071140d40c40b002c010140070094160f107100c503807000c55080140080c0c902c1444c42c0306400100b01d0101c9400e66110740e014040c80c2480000d0100302a080003030071004c03805110003d03c000344100114a800c61030030f151190030071074110311441504e620364000c501407254841074400040100c44440b03100d9464061807428100c08547c05a002c1c0900e1001031862810442840e1155070004441d5003016001001800002c00f078404240c1000d03460160b03500c1e9100964071008900d120922580d20340003130703403010300030a82c4000d280526000c44810380c00804240f40600c00c0180c0d80034441e0792180712040c3c2d5951200702c4091b02c2c0c1d1000c80405000640100d90322402009010310124110369 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 470748453 1250 470747203 470747209
    0xf150c0f010f09050c0427080903010c03020721050417070510020106290702011d0d1b1e05010e01091a18030604030e06180a1d0115140702040902 64
    0x1200c1d041c1c244546440f0016203041110a010950040c0801c0d0740030000c4d808000791000745821250940012040051900c009104041c41110080300c0054024003841b8880e5074010000c0d44070110030350364501d000075820400760075100071407130450a5641d0325040504203680690f64000b661008481da1203000070008a40d03c60b030300b0142000c05603800000d0140c0ca0060384410350b48052455106038101119240d00c00c0188805031401d084d02860a1464851004880c0400c07418504070142d00c03010b43c40a075020840303e45107840e078403040c0280c502903840da1540c0c188000c440d040888603000d1030000d420b2000f5445400110001c00d414500048031580d1080c844d420000351424106402000280902c0c1d400c44000c607e0603507050941c002d000501d081e480c02411a0880c810030340c840d0b400040c40351840c03041071401103004007000301f031080712690b114040c18403101ca080c4000216800781000041004526590a201c15000e441d60340c08041e010000342c000d5845040b040768800d81d115030040140e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 470749703 1250 470748453 470748461
    0xc0c0c090108010f0b0109060c0f02040b0603100918050c04090c03122c0d110a08030a0306090c0305040519030311040e060f042d110a0c060b0f150c0f01 67
    0x1ca140c0000007000c00201404205403171003400070138180311040c1d804021050380b00701c5250b1511b0304030504041100c0584000350180000c070f005140e000307a0210a0000c41081d1480c000210341c1e21200421089401100c00700303109565000142044e041004091840e04047c1c1110400c60301c60420f0b6201c07a03071130781c0e282912000c00c001c4080001d11445200c50068494291411090b200040d05002c42544180000c8907580701c2400207000091490300c4a505455001000d00034144242c01d6986400d080c01d0024000d1900740f140780306560a1000211082d4041d2103510f0141f6080301c081c000254043e80c4580100c17024040442c00c1542e07690038a8610744100300544060714000f0b0348410b003409d007602044488680882d216101c0c500c0c000014a010501c0e5071200c18003001c40c0c5007150210b032045280790040000c014004174800703001503411801c43c0d1190030f240510744141c00801000c151901408001d03002881d865401081014091190403032020182c8a60844d5030201c425444401c10001c1c252 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 470750953 1250 470749703 470749709
    0x91501170c0c0f0604061802060a270b120c0909221a04150c020c130908040b030103260a081f03120f030b0607031803060908130611060c0c0c0901 64
    0x26000031081c001004807c2c002d42080100d45100d060921181b9000105180301d018850020f010580d216400c0030300b65a00d00c65001a5a424000d80c1103994414001142d40840000c100415560300001c10a05044080d20b040e00d5026002584550b52003004c81240c5a100100450b100021000034000030300ca51100d0004210010b44440d1600346403802c140c900e5011001c920718281040c40d0a100ae035400103c60039080302c00c035160340700c000654107441d008004030300003d00900400031b0b0110b042d080020086040304d1095030817480002c0aa200c00003401182502030405190401207819414854a1066008000e8090349500b80c028103030b00c4c04203451240d1007101ea0a6000b5801a02c4a4004201d03102c1904d40b4101803150b001101c0c0000c0c50303442000d00040602000142c0d0400300b42164201c1d0b00690b038003210030000360035241007500362070f0001c00c9442200b141e9641c0200705c05118070181400404080c000b81840e4031051900c020342d8200801c2400d01c1d10982900740d01caa91800c3c101030003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 470752203 1250 470750953 470750983
    0xc12060f060e120615060d020f0310050a0f0302060723250f0302060708120f0a0f09020d171e0c0106050d020d140709020304030509091501170c0c 64
    0x5452070010701415841540c000c0710312416203800f00f0200100301041e15075000a5911409035600a4600041c56500079010082c0034103101040780e007110440000290b01507001e91402c00c40c503940e10020450941030034011621082e090f81401c00040c14668090a5014450011299214080a120b42e50f06004107101802c561156002d600512181c000740c0b50920b10001081883da42041000e514100f00d901c4000d0081000240b14428000b506007603c019070000041105507091a0204903403031201560028900c034a004a014030b03030710441c0328410281d0750244c02031540d910940c650f81c7c880e001080d4030b07030362110b4200030350050500b9543c071203801c05c006800207507110301400003110b007100c43c6600158040c0801c44070a00140e0b40704000341c0000381c0e000484071f048960200f81079041a070140d00c01a10940040300b48010950014058101c00ac01942c540180d9502c61140b84070800c07400001d5404500c25029050741c0a40d50034129a1110300c60090074035040380300381594a032550071010042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 470753453 1250 470752203 470752229
    0x10c1101210c0f0810060c0f1a0414060f06010806030a020603091b240d02040306060617100614091203030406060f0801022818060906110604150c1206 66
    0x81080c0c01c0f000910000410b8030f0030324660300d80214480b054801900a8900344503050664208101e0b0300c408012083d0741c0098a58051502c0340030302c490307610342610201c3e4820f03034060081c44203030f1000400500ca404c4c514540b2841d911404019903c001c0050010307a05409024180005a25120000c60140100600030010001c1c080044951070f140140d070a4460b00b50088240c62301021b445501c90804003640345683d40b16060244400244a141c1c4010041400d140d400030310307244c005030b04c010b4408140c44402141d645180700540400380c5405410049040000f1060341100103d01034031090f24080c041b00154440b45108500e16041207c040f00d620751107a60500281910500420050403003c00030350519070003004000c107245c1814184a03040303003213614801c44980b05910106500d1030002c10b90f91005d0320740304001c00c1c4419a00650f404620f640015410101c000205648a19082180a6a000003601800c0050031540307020004101007208071180601c80c501c500801411f590b0403200e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 470754703 1250 470753453 470753471
    0xb0903030d1e110c1b0f01051c0606030212070e030a110a08120307020d020d02150a060e09010504030207050d0b0606030a02040b1603020d0c030509040f0219180e0402010c110121 78
    0x500c0c00c2902e400140e000c05400743c501840c0c1e00c5100083c0c900e081c09081c090f0322826400716918804006109c1c41442e5400d104000405541613401001e9001ea00700c1030007695a42c0036815519031a052000c01d4141d440b148465021030342104102c421100002c140b5011700d0303a2104000c1c50031202c02845016000000700344608103404020783e9610081d01d0001e00b03582d502e00e142c060b4480f2144001132032807040c240c0002d40040300c107901c400003070b00305626006100c0c241034a02c54001c020882d41100035101d4480c6c040307000c1c90502d45c0d02050302d5100207500d03c240e4413032080c0700a641000d00f1b440c407825002c2c04080755051480b0081c0c102102202400d0a40c04885e0500031321b4021000710300801d0100d50b408000c0032030b1348001103a22920342070703502040420110740e8101c0244070310102950421502c4640050481d0f0003402c0310304501d104031038100c005440e01a00020684190740c02070218582813400c000003682c102515550040505100c0c3c480c1070282c482c8018201d083e03500f11100750342c070340e481 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 470755953 1250 470754703 470754727
    0x100c0203030d1a1915110c120102090f0603010f03020d0203240a11130504091403180f030105090604021215180f0601050109090e0c0621010b0903030d1e11 68
    0x2009800d041c134210812014a0400c01c11072400b80d80541340101b003074484040c04400000c009040e42c050026015580340d808000c1d9040c001d4102e445602d115286000e150503507441c000003580e042c0d07443c01ca00c4500842c556800c0110500100d241240c040c0514203a100914840c2002e0188506c80003503068418030703080007848101c0f640404424003410041c03000c04203000030b038149072003071310300c10b82e000500c1c2070b19801c10b41d04420200300c441c2010704c0000360311451101c00c1c4c0f2032288245802d803400e0140699240406d4242e440445100c0e801d64030003000100036240c01c4111000701404a03040e20000698101001620341d002c58142d440f03410180a800d0000034100540e010350710348030000d40301a50500c00002c0980d10300c1d1003448840c54032003402d440c07102004c3c007004c45401c03c010000755880203100002d4070102e44c20328031001c4640303c0e20000264050300d9012150401c60007409545801c2c03014005034010181e503141d403201540131981e11440708039a440b8001e1030740c00030a0030380c1e12035242143d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 470757203 1250 470755953 470755969
    0xf0b010608011d131707052a04060333060626090a030f12050a0905010b150d0c1e120c0221030703020702030d030c0305070e100c0203030d1a 62
    0x2e001c0d0040c81100401089010149000840952110317000d03c1c2c207109550601c1d6039000d4100c2c040d00781e00070a58001e01d041140c2c1c02c0000d501401401048410b003840c810442124018030014200c0c2d01c1d6a00f00c500e519900700c021500807040e845d405500c0d081e081041504844d40d0740c1004000c5035003500c2d0200010140401200031036100c210341d1182e450010380140e190304440c0300040920030760b407207035800303d5014500003910311100300010060341c504080c964018081d0b19005070b4482d4030784000c3c12140d0a1048074130b2081e0a056043e0f52910040070820b6000b0030440103440c0820880c03a254658801703030080031481480d410354035845410215015002202c1052039400d0a542c0070310b1480c03180c225144907071802e88110031001620f0707036034038a400c0d03010748101400258140640c200c2402801d4040d031141400c191503940403c601d0791075000550302d8030072840311305500002040c91102d19030f00c03c180e001c1d0b80a2014080d2030070f1021440300e140558118102c80d5403040c99001002c8564201204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 470758453 1250 470757203 470757239
    0x1b0804200303070209271f060602060c090d06090b0609060913020607050708030c030307140414130b12010c02150f040b1b040303031a120d0c0f0b01060801 68
    0x31a00e40d00c0380880000356030344560fa400a0090320380350000f81c20040100e000b0038a1258401c80d4002c440801864152588480311101c0703848899070040041d900d00511580059400d141c0040c011a100d92180031031a030003c030045c0394030011104411001070030038081c40d0b100d10701c10110544e6a040c100208208090000d00d100d028030151000c006190b03078100c11084800381c05aa0060352000281801030401c84203410a07040c6101c0044c0c00343c100100000103501ca04915503840491840c4400306c03240c1d81c0301d54031076198030400c40400000503240c001e1b190264076843c2000001c01e0410700020841c00e0790007005400d01c60f5590441e914030960144407403182c50b01c4401c00a0036516108141540344c0c8005440580f0030110000051140c54052400059903215074102680302c0340c0d80e00e030050151a10303c0c1101214424003001c41040c1c20010110910b00e100c94000e00101221440115407800c0d4006042d00e08040000c40d101c04680d0071680c0b103001e00381c2a540e00c0ca6640c100418100d044840c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 470759703 1250 470758453 470758493
    0x60e040510050609151206031b01140c0f010603060209010306050a051807112d0a0308040b0705070602040801060602060f010b04090903110d0f02100c02060105131b0804 74
    0x104255031442503000d400340c031070860f072082c3c40e05940750200360000304040100b004100d0005428942802605026200e104128212894000c110300e400c2c7d240c0c2e82c00b034242404540003e0507003030070740c0030080540f003460584005c895030180c07014045402c0d1240d90b032061714110ba0000341003416503454015139000c0c1074251484140103140602190702e040000f11104030300010500401e0415114100d00b019140070304013180c02c080c00900002c0811000d41c00e0700c19900010b42c80302c045c850000b040c1421443e806465900159445850342e00c03000c41d00030002130422070308100300400030b4550710150010b080100d00015810b400c000002c0e19083c40501600816484007004004400c1d11030112016580c1044000c2006409407030181c0d40c10746103501100a80c060382c1544000c0315805a1b42c6000104250700b01c4030b0014400400700111281c001306d002c0160054001071116050a0816048042420760b00141c02101e00d100b000305031072042e83d5000001d2403441803205000b11090002d030120804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 470760953 1250 470759703 470759711
    0x6120605030606041104050a2310020a022107180c020705030a120302040f08100b06031012050c0405070203130b190c060e070803070204140f04081b0d0306060e04 71
    0x220002a503514802441203201300e45602e0840003074412502540d005140140034221616100c82c03000c01620300c06102d0b00900c0751884060b00051030120301001400b82240c000d07200281c44c503001e010600d240c9000500020b0180005100740300c808005e100c00034860048415802000c00c0b04000940d10807003400c8003198001e41c414070082c1c0d404140362031045d50001c1408009038402000341d0280c01a039100b002000d80541001494110100e9408064881e1000070172101407460100202030000760341c0c00c20f80c6240d02c1c40c140304000400e00104c03880c9000310b0840b11617216070700c0050165041107900b0310040c4c2010404c1c0c01540e03007030038810026102d4940041d003003404503448081040030307280005041014121111040c010141d1255101841010039200c4940d11420042d03925848520200c2c022441c02c0403d05001050404a41c0124000c0c1d00044950702c0740c0c3c854001d690804036248002608080072045001d50401c000300a03090301d5100800d900e8034001c2e0151007000c1c21500384e80920b041c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 470762203 1250 470760953 470760959
    0x71809030809121606061503020a030e0706140a03020705030c0a14070501022a12031908090601421101140c0a09030218060f03150a0908091801061206 66
    0x24800954040d40150120700044e11854101031000e8001680103450200c00071504200d07181e450380080092213520f40b410b1042d0301c400540580c2d00c0425118002c009400004c847d4010b204010003060810003926000d0b01304016a19000d0942d030280d00c43d000150b220411803400c1080d01c6684411910030000980030300c600e00070010351550020302003102040383c80807210400c040e13480b80203400c0c52000b61125004d0030212003443c2e560703800000c0380c90768251405000c42d070452052319154071074100300c001307003545034a45900480c00c00500d8521440728441c81d11349600e0091300309000c911629211410b150000902400030b4040e4440c1d080101a69040000001e540e0b90070141e803070b80000303901200b5540e0382c20803601212051080c0d000254003030510070300c07810034511458400740100f4084500c4003500b81504d0400d039403401c40c81d056102200721080001c042d21507642c8450003041c003483d981071510660000082c43d03280070f03010700c4985500c103030014046154007902e000e03804500c02500300101c9007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 470763453 1250 470762203 470762233
    0x7020907021f150b0c010608120715051e0408090a0501050702060a0e0102031309060f080f06010b07030e150307141303080d02040b0427140a0e071809030809 69
    0x140b0944080201911461407441c1d9500c2100590000e0900054840e00d4410241d01e01b80a4400d51248004c03e2290300104003503c60b403401190513596002c1020580c200c0c3c5403181030003509004100d0000500303944812081301445c10709051040b4481c11a86985070000d800300702c425003907900258100b10b014003010300180c40e588101d801380c0d4a541084a005215240102e103944501c01a0100080348a0301c00102c149007a08032605540b50a9940321080380c41e1442030b5a80c0e074841086501c154428401003222224510091040e20300904d04514400000e0000c903003603011181c600094004008200041c140d40261003010443d8615406031514207410203414070444a8000078020700c000007036440252115604882c000e055400b000d40d1107a40d1180307118000000360103030051601c0340c510081e5504070f05104082c078181c1032710991162501d501011340010304d018500b20f12030b0b02c5010004500190b1014031141c2100c0c8904021030306c0501860004c000c25005000c20315258041e110111080d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 470764703 1250 470763453 470763493
    0x30803190e06090c010c110d1505010603140f04210306210503041a040305161805010503060a0e010207020901030c06080906071d04020714071412100905150708010306230c0918010b0702090702 84
    0x348420403c11055161303811c1c10344088030860181030071010200300058842d50150444c4080381c020400c0c2005600e41880a001c803084622401085500304000912160003030080d115440e01d500e610321400c10352203568451404034910885180000221400c001044401820400b4191144d2003484194504000b00313684e810081c0c03c2c2c0b0b2006803515070860324918254190f840040e0010b0a01185581da82406261034165000350000030b4805e0700003c207044e00001c0c1180c0500d00542c1c0e40b00c51020004482c01c07158252038001e0307500940800100c800f02d051100b81d04c25001e050350150400074604a030640c106203488120074001c2c2d100070b44c0c103030805201060840c2e00218420000c11001c415140079070420b58907880c81c1e40d6a40e006414001e440f613001280d6810f03284541810840821400b903440701e194101c495000307108070398800080042c003841d00a4150007a000d0540210000800341090029009030003900d000a8040f030414290b280424003141c00a0382170014040c40720441c40c06414407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 470765953 1250 470764703 470764711
    0x1020d0c051c0c12050a05040b070215060f0a03060c0e03010e0a05060f07170c121528150e2e18030803190e06090c010c110d150501060314 61
    0x1040d0754403c060703a10341c016080103095107a2224108020701c0d20348070136002080190340907141c1c1c0080304002194140001450315000182d5500548241c0d2440100300e42860301c0c0c220310381c128022a0002000661034001d407181d0310309039203a078118089848145401c4800d10380310002207502418401010800106045400c141c91801c910300540c6c1340c0304250b0340c0800020307018608074a07140c00c10585880000141021200203080a082910781610624035050502d00300790744404066215150304202c41310f03200911001031001c4142980d240c1100e112080280708401c089807002039411904c0c0383c26110f00d203040045002d401070351608040280c2440f040d14059500f4000395403d00883d41b0342c07484854008550202c02a0782d00d2400c0c80c015009240044105007145041c00300640131008045041841504240c0003445070b0a00c40c00111411109000141c586191850300c5284603100c0c600a000e2640c01080e0040365010902c0c0c2c014120b40c41640007d040600e400c032481c041506030785002c1d1700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 470767203 1250 470765953 470766007
    0xf140c0108060d0303050c1905040303030b0411040b0c0f0d020a0507050409030504230306010b07060b0301050606190e10021e030406080a0b060d1406030c0414060d0309120501020d0c05 81
    0x4c80d91f02c0200c02c0c2503910a075102e12425078800c80b403542000781c0c040c000303009032846540d00307010f061842c600780402d5071508001c150120000f840b09012013a440c8024011101c44403046031041080b04503011b0400410103024030060300182c034001d0a02c001080150300611050703904000100c05601c000700300d4040c0b400341c5164180c0000c5480f00b132481045100008480044c103032116940d4074034030701550b40e00103202100d072982044000007040c41c06110301882503c0180000d841c1003403546c1c0d608030401d45c1c0d01c0d41e2014005054011034403600c0d200c440d03110504035070300148018140ca4146482c001c130803800e444a154001c010600289071f012964a4000003005800314892001d18001051405800342000301c00b8540307040351000341e030300283c00b038011041502a9035680c01c17500140710030b41d0201c4142400e491462004140542440400906024084e2400c1c0603c035885030b0881748039986642c0c05072020b86d0013107404417995800f072150909680072420030900d0403609008280210480040c0c0b101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 470768453 1250 470767203 470767211
    0x506090f031305091305070806070305070203070317060111150403020f0a05070b030c040b03070807090603202a030d0f05010503100c0201020f13030512030c0d180f140c0108060d0303 80
    0xb2407800c504644481c0c0c5034000c0680e0803441c2c071003031651707507134003084030004000b3341014007060b0300a0000c0112410243c240d0b0341c4400746101e4807544111a039000d080a03040085083c0d540c0e0740e08206010b0241000000c1c01591080c1c10316080084c9010b0742080885e185d90404000d41000620000d003203401c560b080c8180685a035030b503550780a554016a8040c00200400104000c16141c3c03000500344606200e46941c03640a84504085084500a81152a91610031103031a010396151002a155030240c9440802026450b00e072421030442c00404000281d42c80804c007004d600c4400d004040002c80c000c0800c220b598946000241d03500034051812407036958030388803854070354400e40494041d0810100703550f030303500b8404100404108840c1700c1955540079500100e6040810364007101e00560054000c0c509101421040b00d00902086044500c4101820768100006150346243d006082c0188039803101c5840a28410b410514100110390411040c00c08101c0c0340c2e0b41d5100e04907061605890005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 470769703 1250 470768453 470768461
    0xe181e04020415060c0b0106030509150c071b0612090305070b0405011508030a0324171612050d080f0a02131d270703120302070c030506090f03130509 66
    0x1800902410812900c03543d403410303000c0741c0319811581034542d0310300c5506031900c20ba0f031310b00003101100d81c20b8400e41e0303043d00004c4085291051000001d41c00003101d40e41c0038a0300041c0c0e603480c81c01808040042f01103034400b51042201340d0b04240e8059002e901400180811103090b0782c0100103100d1444000c0020310380c1008242400400d500110b1560192481442116280ca060944e42c1d0000700c1090b0020341400c400b030040900d15100144000c5408a00121550410341031194551021407030070754a101d008644020200c002160750f004145030300d403c10203081c8604195003021800c26540080c00006810b02c080c4211101c0e074168803d1006030010f85403005603e01d21207041540e44116955507115040401e07040c0d02050300d41c040c440001d82000190364040c03410391102d0328901c401c0f00c15000340d1820000f05880391000e640741c44051400500d40001640c40058601d400d400541310707030780300f0020490340d40002c204040d050618980154188018040d2171021126540501c034061180d910100b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 470770953 1250 470769703 470769709
    0xf0f140c011514040b15070305130b0405040e0d020601030b061518030613030c120908061e060d0c090c0908060c030a1109100815060a0e181e0402 64
    0x380d0020200900240100b07025040a61140d044034015866105004000c2d02044d151921031150381d40e03405130110040d0b6540b45403181d002e0f0400c0d00181c0c00d1050820000380d0402042d110700010305a51008151254140400e01007150103001000035154080201c0568890b00092194112580326060f0007280d9200780200744002e40032038400c2c2c0c04000129000d85828484044500307039420540c21500a5602c10f84604000d000b401c0016021030382c15400700d004260241c01c1c2410040caa0304001407a240d072000b03101d15110007121a62124030700c0c2c00c00820545140d182e03d0381c100008039004201c00103a0780b81c03900c9a4a036071250310907441c3e0301ca400340b500600036180000201101001c0e1202c40c50712060130400c03580f0458030b51300514a03002075501a40c01100170740343c14031005003401451200c42d03841901d5691000d0005400b40e044500300302d04030f507905402030100da0003d549210513402e02ca010f0214a0001a030710081500342c2c00c0822005020b03003103e100b051041400e1280c079a80700c60000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 470772203 1250 470770953 470770957
    0x30210060306060e1e0c030603150705091002010e0318040f1104031b0b09011209050303090304030501060b040b071506050a0f210309050f0a0b030a1b0f0f14 69
    0x2510a0142400800800d0264503401101241daa080c8015040e80e50300964080c0701c85c804243c01050505400801c41000d42180903640c0003102400f1075400418526241c0c90b203d404880e040300090b000a1480018103107000100d58bc021180020312500c4820078601d6124055001d194418100030206200c4640e169044074080741e403100800c020411540e01d9a104540c01808145e0300201d500032107026a1003960031010480b203000c1880b50800041e5001103410501c40c144510a15460b042100d0124005100460061990030000c42c1c0d9980f8500c0c0c26030a58165a00010320070b002840100007038000391007100c1030b8950101c480000c03680760703040440040c005030300320f00c1c1c1008040c50049404204000e011054500228400c0d201041f460280c074040a00288001c1c00a200340404000340c0c109100064142100202508200c1d42c9a103201640383d001250203c46194541c60a0500e1a81540c600c2010072080d243c50021803940400c0a4a42d18111703000c101007201000e8160424503814003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 470773453 1250 470772203 470772223
    0x306150117270607080c2d0a020d0309080417030408011514030a02010e04022b020301030c12050607050306060f07050c31050705120103030801150302030c12040302 72
    0x20754007950401d50281800c0341c1c1800c401c410500070700d0128141c800000103c99104a40d0383d0f0b5101c6283d0386d40c6a941c4213541005511500e16500e280001300b203889421780240d580005d86110702e4071f500070000d00a140c1030340130300110145440d103030546c1d02141c031000803601031310503240c0c0003820506554009861803082ea0300c0100e00e540f074680c00d401120101120003049a5000101c80d081510403030030181c0300c000c07800e00240840c000c46213070421410541c010304a48041b800e0b96980d1080d042c001c40003500c8a103129610300c82e03030000050080000c4244120098055414030400c07a50f111b688240d0380c1d40001c1c2c4900d003803140210008640c1d980d150f00720342004141c0c00300c80307860380e505142c55992150f106c0840740c4900f000443c0420006800c1c03141c5142d0289100380d1040e00f09a200f8124014600075003072004104040000c0e80454040070085402507220303650b40301c8150b00d0300e40c015041c00c0030b5600c018201401041031001080c464400d0f600d8000140345602401d482e00d240a03850026840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 470774703 1250 470773453 470773487
    0xf1a0607080702120f0f010617100b1311070b07030e030a1101060f0801090b0105041b0804020415030b040b0106033c110901020c0a08030a1d030604080405100e03061501 74
    0x20142c80c40745d040402c0c1034800744560310007404a50b40f1941114810f0154a031ba01d01a41d102c01c1c0c06a0f005215074000400f044005407980740c45044e01e1101e50141c811000c103d020440d00020b50a04102610341441e61081003840c0c208000e00340091803d4880c401e8610050030071000d4403c40036902800e5222070020110580203050031551048518043c01e0243e10580300403650500029003402d16000d80d55145660f40054103000100000c162a2903501820036a00903a0745c068007442012417043c203d01650117010030b00564a454900a503010505030000010541000100c0c41c5008149591022005c031008016440c081c0840b81451244401800e450909042c00e000603241eaa10800820003000281c1c250790140c01e0000602c480c2007414440c0d4007441c1d1042001400151051a80d445a55102d400d00030341c003030301d100009207410001e035005d503003071000050704110b42d00e829480d14540031501e0800ca8035486600c0006515000c0080000c1901d22115001c0c24581e0710403640c40803071900c15 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 470775953 1250 470774703 470774713
    0x70201050c07151e0e1f02190c0513020412021002010923070e010509040602030c0c010905030307030c0c0c06050c0c0603010f0f050315070507080705060a0f1a060708070212 76
    0xc0c0024500c204409480c00301c03129000c040300c8194402e50705221602c0c80070b098100c3c002006840107800601180000003140601c040d03040c103072440e00600036a234601a15280c0f002d981088200028050300221315a045031042104000000300ca0304411440c83e011a94040300c04186d0409074050050340600402d55046540d0030f25020390701030b205204007100030044074045501c400d030f0b5960380c0c202030040903031254690380040c002071207035002140d000500170b5840341041e205c60502c1d42940c0f1800c0d800c98190b0808000c00031055811f02c00e03080403d04501d4003e05201c4036880d50700d040300581c01900c0400400150281150b03c0c1003001484900c4041e028070b64969448000d03c01d049600d0085c01c0c003986400740006003910340006c90322481e441c1c4060700d003020740320080140d031a588040c5013151020380921207000130a030f00344442446548150004200166900c08141c12142c042250000082400244181680700e1405440f440d075445210a9a10031207800020409140d20556028900c20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 470777203 1250 470775953 470775989
    0x40903090e07120c02030c150403110f0d02010b090c0a0c02030717100501080d1b1a04111315060e0a0e1006020d020307030c32010c17040305070201050c07 68
    0x31003c1080e090460b0590108404808010100d807a84500200c0309110391081701100c11000d10942d0b202d402512900340403802c548844481d81c00c000c1190502c80c40741e0418020400f200e502801041c500742421285a261864041c5000304507010711044034041000c403c5180c411910200101c0006d4004242a400c06108103003550342c0d620480d0100074034081c10300c0000901c00700b000034441040c030800c1e120742c444da403112903100e40445100c180170389045d1a04030422000303240203c81d4902950180f200000302d43d51540030b101650301e2082c803c050f92440d05a03030358080b0b01c456100000b0b82d8218038004580040d08000100641142e03044901241c41c00710a000c000800d07292000c003110455004c0d110810f1705032500ba41c4038043c80304040d010880034909000041c040c07186d10148003064524100c0390000c41c000c00580300341c0382100032001c1d139500e081e4081d440350004a03d032040b21450004002038134203654014450302640070001e05000c004151006900c80c02c1c0941c4002d0720445200b18140c1130 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 470778453 1250 470777203 470777207
    0x30f1710063f06031b170d0207150207050312090109060302040b0405150c010e01150504150e18030c0c01170702070e07030207170403022b02040903090e07 68
    0x115100e040041509502400a00d0741c4512111851844042c030b048030b4082c00c2c18100300e66429600c890345405a90308008000a0003601d281e900d64804c040200b90344905011116500560722224129540d00244008501c01d0b4002111300664684032090440207845200030380c17a205c02c58000716454011540c8041070000340c0e10140c12011003d90341c082d4526034030070b8198100d10031406183c801c80410041803009041910003008041e214140c410300c4c10201c9450582100c02ca01c050301103c1e5107900c140c54034039039a54500e002402046500b009065003080f040e41c4031844501c6908cc8000310580000c1e00c40d02c1001c07104c0c2c5121104001e0301c3d035420b001043d00b41ca40f0030b61401a0f01041d0441c28406c0307014601c1c10381510441450300109400d50504510000140340101500704060302008007500240070f40480c2d0740b50f031000021654541d030540c410010f08050304030350b5aa0188000e0b0b040101959003c107038420080c5c05a400140000e1a070908442600701c0740c0201240740a01000d00801035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 470779703 1250 470778453 470778481
    0xb030c0c070501110304060509010504091401050a0b18090601020f03070b0105011805010e0918072301111c05040f1e0503060106020d140c0607020619050f04030f17 72
    0x1400d8803050328811070300c64006686410200b076002c180380d0700a000600100380940010031030719005040060803c1ea032640c000080d036140202a1656424090040105040c224600f0000d03003a260081390070065011050003003a902c44010f58070900180d0041840d59000384401c10f044114003050b02ea60380400c0c140080b03058402e00c5410b000803900c60003c0c10310149a4410016100140c0d604504010a5000c0010600c00909a00c44030003100240d0f0b031369020100030301801010086508240120b4109402080e0038804006a05002d203080b69010b000601049204003501032001c1d09100710561803040740d40c1e00540d01305241c600c11076000440c4030707480682100c84540d590400000047d440d102895182d100a00c0307000701507803250301070080b617a004182000b07114100d2140507081c8000f401c04149090303015140e900c0980c0007a0140960120180040300c509122480700384240d04096039154000d0310300810280800c400d0301084000c0c688103140605482034504480b940d0b505150b4002c800c52 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 470780953 1250 470779703 470779717
    0x1308160204110a081b190210020c0d03111912020702030102040e04052a040c02030702041a1804050a060207030c02180a150e040201050f040902030103110f010e030c0103020c070b030c 80
    0x441c0c10613001482d00c40341074410f110540d403070f003090a0400e16940155900150454400019401140781d03c2c110b590043c40900100d403600030051030002d006000140490b2050043c100d4074800c1000390801d01c59144e039105001c7c81c0c45241c00c0a08072600c0c50907000902424000960550000500241c441e2000d9180350183e070040b0240d07010300a0180440100c0416800e4007081c0d10040680c140e040e103480d0380001d01070380a40c01506e2600742264000740403500404852001910340c49091a401e0400000c1c0b0540002d18440881441c18a600c0715a55074114035001810315400003295000c040c07250808000e015800341036414800c08005c00c00713480c80022202580298500010301d0010155003224900311800d00f010f10700240c40c2d80e00116444e5104802000040344100000139200107240300960003180104903400584518808102c04d6031030b8840141d04208104020303640598020030048a0a4000d01700141e40e07400e06040c25040590315070001e05001404800c200702134524100030816 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 470782203 1250 470780953 470780957
    0x103020103110703120b062803050106020a030504150c1a090c0303091c0c180e07090203010302030607032408010207060b030d020d0c06060b071a010902031308160204110a 75
    0x100d4501032030100c03558000c000002d0001501900914130104a6611100d01c52102407e19494401c3c003540013a4050076100d101640b03800a0000031030847d034184070302809040b051018155404294400074041c0c0140e004400c0c24581d080c0c040c4801034040d2104035001d983c04a01c407044030100e449802004201110300740c1183c015034040f1161407401008503440610001d10b42c103e140f2031600c3e81c1210420f840ca00b1101441340c240c000ca00411504500304940c05613040c041800f641040109092071502e43c402c880d224018001840147d41c04078481c0c2c2d00042074540050354800d044a9503507600b40c20200d400710f40d030b032a1402054045064005200c0781c2d024846c02d01c000b203c0c800c140350307440304100c410b480142c00010712400a140300b0403058440314050303c8042087c0d030300e6684841060340001005ca81c000c054403101ca04207000b107010f032401402c01d80000c50542c904a18104103503c60b5400c021305203040000d07401c0c41003009000c00c0d8819600a80300b008032603481c0703003181c180d43d21540440d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 470783453 1250 470782203 470782211
    0x6061308060f100b040b0f07230c10080121061e0b0904050601060c0c05030111120906101511070b07021305060102150a09020315070f0905031e150903030103020103 72
    0x182402e0124003c0c0103c5101c0c288483c43c0c585005005800f68102d454100d0420804101c0080070840f010110078140340e13074952208520002d00f10306882c141c9800c0807540115966440d680c1e03c44e400003a5203044688420101d950a0b0250300d40d0342500d610200002d0125140040182c032005008511011800d18070800300300c0126400308000340c841080f41c0040160348205d0050106030b110311218400580726109201b80d4940302c1c0700183c2034420f150a02d808226001c540da10f41d502c90904804d030000000380c0940014180304001500c0c4021701d0181e0742c80b84480c900000c2c6054400d12070012000d4613034003503d8440b6140d14584540d0b070f0000c042603218028104810901c80300c06d20039240600300507001414000d0b058a02c010707243e100200303c01240340d0340304185405a04c1c00d200c0c42d0f00f840d0612200381d0355444c107008041d2000e005841940d040100c140c90501a41d10000b80003581502640440e1008080c0441114a00840c656044940b08008801d000703000e94000003440c140c030f1013601d00348 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 470784703 1250 470783453 470783461
    0x1a07020106050319120c08071110081611101805010c020d080402040b13020a03090c12020a050d060605030307150605040c0804110a0819060c0507050a060506061308060f 74
    0x142d95441c925022640030f04025480400a4200d07203004c03a854566040450b01b440c079507151051190001203007a02e408951060850032894110218564113a081c2803504040c2041100c1d283c1c20b4540c960741c002803004003214200d04071410064500d600b2101c281c24003500d4041c590713801c0c0c0312245860407512582042a02c44289002240c101c0000c407130783d568034400303035101d03001c00010b443c05156a030741000d46c02d0360300103031040b89000510341c0e5904d40d10b02003844923461800103100d9009501c840701d018100403031200103955103160201100d0b03044444120000090404000034001644040d40c18400060040c1c03c0003e2080c10422088510f441000741c942d40e642800191002540b1039000074480b800085c000522031204050080c0018002c50052a2a4800c40d8903004040340c80c544450461800320040100f40d0094070307804210340c500107041c00d003260b40e025078442009000900d03e5849000045075511000c054030380b003154800104410598600b2007617200e8200396000c00088907070100117 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 470785953 1250 470784703 470784709
    0x130602190c0212072907020a0311090f0603100e07090501030f03090e01050f01110c1017060418031d060a03050f0f011406181207051311070f0f1a0702010605 69
    0x1075400c0b600032020b0078060381e40010a1744034481c0350800710280e100d002d0118030090f880b040604030107588511413803145d410055013006103103c0010150640c42d6488010096a03813004180a0510b0b0348a0314041900050480340e142826011740129618a28000001040c809030410003140680280c0701d5407081602c44a804a20001c240921500140c812004241c50b5202d80120f448107908082070b07845946a44000a00040c00c800424000850104132904400c180814031030b04840c0803101000911495982030f9a0507810800c054188400505014540c580c1020b46006802d0000d05881d0b40f900e0100018000b41401d590340d07440ca01e801c000044a4032004011703203058a44280b149441e50203c0003c1003800da201001820740c0302e110070302c2050b503601c8409000308003000d09005042801e080034180405c1d448640011010b03a8200311040c20b120b456074040701c005d59081014100401d1446c14588680c428032000184203005c58040d4410240d84054885c1c066001540248030300c540d19410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 470787203 1250 470785953 470785963
    0x4110324030d0503060d17190302090d080906040807120b0f0f0c1c050924070e0907030e0a030e0a06020f0601150201060506160308060103020c06130602190c0212 71
    0xd00d501a030264080d0540e1500a2016680c040e1000f070032031140e114680c0e284000e4961a41045256500100310944910711040320f040c90341e20346150450500442e207001581406200308050600c600006408809807183c0701243d018091050840e900f4076515160250a00350700081a16103076040702c08959412002036240e13016644c2020a10990744550600e050030340d1056214481242c0084920f0214008601600d44035003080c10103401d403040c0025100140229051034510b02c82c00420030403240303580000964603503000503500d140191359036000c1a07000b4038501c00c2015180c81040400010581e008460000108042e510301d00c0e9182d880c1401c0c0d9450b051605000c0140d00100f0040c49a901b4908641200c00d100e48004a00c00e0760741e1021405c1030f400101e210201d01a400380c110b090540090041d50090000e1034114904a050303840030341ca0388000f41210032071a150000100c148070050301692074110b2500c01c000390b0b2104041000c0c107001c080e21001c90003803000400c2041c8680300456 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 470788453 1250 470787203 470787271
    0x7120909050606030c0a08060301240302030f0303060901090e0c0a090f0c1b080c071a0307020c0f0a0603090f1b03060f020a09260307030e011b170f0405041103 70
    0x72011b05080d41c3c100250703085440103100541540d40d8100014610700d1800a50300302c201c44c0d0340415007d071704600605003450782e4002100b45990081092100544031144241c0c1100e40740200001c0e1040702000f000e003040d01c1d07040301c254040040382c80806c401c1c607030b5070006000e21310111b01081030081119080d1070484101007600d440122a044120116141d04020f1220b07840010a84200c81e031183e850701a0700c01c3d9440940345016010041001007a0100120344811800300c82d01c1040c032f0404000038141c03000300d000d49810942c03229051410045249000003d0070b9000302c401c0340f40f005010b8200000042c0303120035501281030206400401c0c00728400c4400c10070f4a541c50075503190800e000741907100003d1003842182507040f030280440080600141210b54801e030b0b50030544a40000004100c0c8100c8090951882c081d43c080300b00145150a00c001c030314102c040352540b940340c0071203010582c2c002c9a00240e0000e00304a60412402107030300c002c520811100054954000c039040007900040e011031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 470789703 1250 470788453 470788471
    0x305040504090f1707051014060d1a07020d0e04090206070b04030507150219210b01020106090f02070501060e010b070b0c1903050403091e17030712090905060603 71
    0x818000c50425402801c040d0b4003801a1001c1151160303138a00180e48030b0401c08a00440214081c0100901407014444c180c070300710418000c10444511000802c04003408040c03260741213070035001c104902c180861f14801020354000095140034640651074002d4500010300203030302c903481d130780491415200b5504a5a0040d040d98141406079444165040f0041c2048d000c1c040240b00c03010000703040c90446a02c0c414103480240c1c403410b13182400e6134280c802011400a002190182c56005010410b2700641442d0031003010070100034080060780104400c1c0c101c80340850421010306c120103804e8000b4158544694020000c40b940d4800300b03103000c0028050701401c03500800c00080481c1c4514062a004030a00210070302d41001a04014203000c496041d500c00300780c540e0100070915401103070314401405041e02e48095155607442d100c0c010403007800340c1200103644400c0707a072080004000b078802c4254441d108120300d41c0d644d4000350a9815074400c101e0460304220000d856800c10718180e80c0661400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 470790953 1250 470789703 470789707
    0x170120090105120a0b04050a0c0203092412040507150c2603091c030e150c160507180b09070c020d06060605090301050c12010509091218030c0a030305 66
    0x10002025969000009035410410203010741d000a41c401c10207640503111501340060a440480c003400f0540e44024040c600700ea182c50b075540f034503d03004070458450034012148200044a2592480641c9008020704c42581002145584c044c0c044540aa40100d0285e07080381e00d25543e40700d02c010b140568002c0c400019440882840004a0099002c2e200000440030380701c0318040d00303800a0b4140c004850642c0580e0140c0c0203031110b030030350004105501e481c42c90203000042402c1003180ea2290040c003441e0880602c00300217210005504240c130101451900040d641400703500b03201ea0b4400c0c1a00805005500700203418403010150300c0b908508074405054a00d181c0d48140d01941c8000e140c003001c0e43c10014440003040041d80ba842990b0180c00291251500d03100e001c0c0c00d15084170001030090703103110b108000d05040c0300d03d07014010b811100c0440346502240c5d5468030090a01c00911511042a040401e0244521145108503d020300f01034089498016042d4200410700c0700314130015002c1482 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 470792203 1250 470790953 470791001
    0x190b0d090b13080a080c0405041506030b2e020a02060d0506100813201305190204050d0f0516030f02010f08041106160c0e0a050c121923011701 63
    0x1d211701c40c2d4000703000c12440341050740d6000842c05039103181d24103110324041c0070301c140702e010b800d40b0640c0202da006840122041c0204071510750342d0449000c801e489075039442da64070a182e10800149038101c0d0f002e805a5140c407e0300251802a1505903810741c8241c414503480e58419208521035803003500e5181c0783e01c5440d2856160404a0340d500b45036020381c002d000f11080a00d40b01c514030800e441c0c1612074000381703519103c8580c50610b04561174890301d540c010082041169140032001040e2500407800e40c41441c11864000d2402844000308020b428000c1030020612900304036865069000f070301c5145400c48541c5003241c4041044400402c03c2d074034110f114400b4200354001e402c0040c20502942c900342469103680d850641715a2060080c00d1a000c100841220706004e001d810a90138043c803400c14102e41ea003250340c8003000f0041c41221001e2124051075100980013030400b00c5c68034400e158aa0000303019910035580c240500348a40c0c03119000c2d0017110740c0c140720780c014900c038141d60300500000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 470793453 1250 470792203 470792207
    0xb0c012316031821050a0903060c09030f080301061202070203031b030d060e060f030f060c030c130801091205040609140301060305030c10060509010311190b0d090b13080a 75
    0x3102141550800d0342e14254004018101a40d83d0003190052182c1841e085402c00103070b03501d4840c041d02d13000300041031001d00a015000310240090380d50102021510002c01181102d444001d94405481050101d03031800900c560900210f043c3c0d08555100752512441c42c804809a204620b8000d4043e030040203e06199000d84040d2502241c0c240140c07840c1c504030314105001d4030415003021142ea071551050002d646088428106d183c00190b010f08140404011615119480200400f4150100000140c18183c20400700c800c48011a02c1c00d9071843d8841e580d107802410f141c242103907003410703c0201141e543e00a0060310200c481c0e42c1c0e40ca054290a244008945003032805e032298041d0f480d040c01000040060000d031024140060092402888510158095400d950b0000b405503141d4001407020418039940e1a16245003500c41038081036440034200100788455000c00180e0a010441c0798500141d47c11030740341c060103034800420765103030030ba4400086514800000d001510420003601c03018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 470794703 1250 470793453 470793481
    0x409111c02090f060a090f05090408030c0f041e0305150603060105010518090a0b01090b0a02070b0a0c0c0311190b04031415040302070e010605030601200f03040b0c0123 74
    0x18002904003284003074000081104c40d0480e00361040800c0101e1024001c4051030407104008040450720700358030b030403da05c03465010312001e000030103d02ca00080051040302880c007181c0040034500650380d420300c8113100c10100c4e4155800100ca107400790b50001c843d007220090000c1d001d170310002d01400da240d2170800151080d521101da200001c04500e1001e07662a0380b0341410a110700d5034080c0200c2c04002c0c031000103003500a10b80203840f00403c01e210b0420f0041e80055028180c91010070b0199444010030070640311040300a600408030200e050010040001080c1102d5507405d06994040003d4488a49042203070b0300d40c0201a1105418002080031500c5d8501401c0c25000c0380c82909c0809044000b030300400d00048078164056444a00100055404010501c1c010100d91a00904508080303000a140300d80840d40c45245e05c4104a034190000030034080000311000782c1d000c81e907172030ba9542c83c6807003e0b801c071034040c0045500c0c0100389201a1445403400c0141305640f4280c500c2c50ba2041000b07160740d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 470795953 1250 470794703 470794717
    0xe1501200106030204020f0d140c0d090f050303180706090b0304060b0105070b161b0203060613020c2e06030c1815060333090525050409111c02 63
    0x41d6490781e6000000d80c5a902c000e001d08501c40c1002542c40d00c8540c001001d0b0f62024801c0415111040d0800c200c0510b048241d9200013603041e00070848040c1400c0070309140f400684040c0050100200303111101c12080e1139155441504401e03620750350b42c1ca40741600c40808520540c5032841040000800055241c0d20054024105040c107a080001644402c01140b0b000c0f9050440000100c0002c0f40791500000704000541c079000350b41104030740719408242c8610703002c0c02c20340c0103200509907201080819015290031089401c1151044070141c445114030150004031800c0d5481c1050410f02c1440c60342c0510015280c02c0b001d2003807283e02d8400034003c034064094110070110b584a0460b4106051070302c110008207816a4045a045403902c0b042d00701c00101c08207500d10450f07491000501c20039201441c000c07110403c20010311603640540400c403114254030940202c19541d620b404c90143c04c000138000b90345541000300715010500d4000342080c42400c04844450280e20711480148109400074850 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 470797203 1250 470795953 470796017
    0x14160503073c1101141308031b0c0115050a08031914070303230f06010507050705090c1315120c05130906090c14251205040e1501 57
    0x12940c90102582c1c154a40040c0e0940040c408000d010400035007401103010803a0307480d580007140e090a1070030140401411030020158100400003480001461042c69900c2c456440075940d40c10600704124000c182000e9920f20081444e400400c0506085c10b80d0f1080d40c803040000c614003445c40301d40c040c24200102100040012078400505200e40c21000f0b0100a4442d85000c506004070705246040d88056803c4091401200c9007004120301c85900540d030003080c00c0c2080b551321300c100c0c10300318242211900580c0d0020b0301c2c0001d1100031801d040041040061104541c205907840f8004450120031200d400400254019039403491028a0340c4103038051450b83c101035140c45071401030206641d20030382c0305520450b51004108906800c500508100d02d643d8a02189003018101c40b90401d4000c640500342d041c8a01080c04205e2010f0381a150400b07070b001008070000c00c000e9600208603910900070b21000c11f50140100d54200104001c00d10200f805858400403104581d040c1403241080741e0100311 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 470798453 1250 470797203 470797277
    0xf0f0a030e060f0f0a121806020f0903160614040602120306132a03090b0c090f0a081605040b010c060f200403120801030206040e0403030f1416050307 66
    0xf07681c01c03100000c192400e800b500103a00da41802d4005801c40140c84c008030010360801c0e9410360100380c40050140c1036a8002401612052507845050a40c01004110383e0144036100b42d41604042e49464001100c2465981c41814003017091041d0041c05030740305080150b4800902d035040990000c018641c0b00300007400c850700b0034403151030b00416900d20441c00182c0000b002004906040140c5145a51901b1820180070840c000c0e40e072031440b410002c6c91103070101800b003038080706550ba003030f00c00c0c528020040a001c03581e51a0000303a521044042a011182c02065600107068181070198105a400586442f20303c2c4010307403500b0300a4150118030b00c43d080c1d43c4040403001d010144c402d0144110000301e005440c0d03402c600d4940801003801c0700c03250a001c1c0c820010001a6229005c66050742e881030382c00800c98542c1d28050340035021346205000483e040c8244e003803101c809100c0c03140c400c403e180c41e2880c2c81090154180c80c2407005407941c800041400303072030300c1101d00c110b00000d600e203481d440c80003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 470799703 1250 470798453 470798467
    0xb04031101030b040c1e090f051c050d020303071218080306032505041409070b070c0803120a0f0c1e090503030a0809060a050702030403030f12050103140f0f0a030e06 73
    0x280c111070300c1e0a140800308100e0210006d2120f007903104000c003800c10307050003040b440c00d10143e1f01d81e0140d2886440c3c0300d51017040801d201c8290340c803080361400b07601108446803002c45980194607600b045840b54009144222921407905090040d680c4035904d010882c48101000c1d21102d10355070008008541520840c0351050f03080d9050410030701c4401d030344290480b1003030401c410482038841c502c01d80c842c9820701105001c003002011802c40100c0b80c403001e42d20fa030389159103001001080641d005220340d00011509100b0707560320a40c650b1103501c10200c00c01c0552201c10408048864074544540014205198401200600c0c0001c0800c0c5903541081407e0fa5501d40000b440c40d40b00d29034180003e81c0050074060a01c03020004160030a90500d8140a1803a01e000c00035900d0041d848003408100c5070030052907515010f0700303603041503100440d4148825030f121704124014203619542022a8864140c0c5616909004106c0c241ca0600d0031024240c0640f45440132545980d190040c154045810003a403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 470800953 1250 470799703 470799709
    0x506162301050a14010e0c03040203120309060712020c060f0907030605090a110a080a2010030b0112110301180b10020f0105060105030c1e0f1606060506040b04031101030b 75
    0x32044641220004202c0d480c10710990400d40e03100b00c210310341c503035a9240140040c5540b0380725a44d00030094803201e51a41c2d50750000a2500703c801e6410300c0002000024801c140101152181c49000d0a44400c94a0202c1c0b500b2182203215582c0904819003210012030343c02c507480746000303070440005012988199101e0311001d045440c240c441c202541d0103640042c3c01c012018041042d81c20f01124048117482c94170720700b107845484840008000c003c20301e0904a424a0130b2819200d4a0300141443c7c000c1581840d024001b020400301c0340303010030089019440c0484103402800a207140240d070310350450346080712041c03070405030348a20b00166440300d881702c1540d10340400103240b108031070380100031103105903030154211080500028100303d0308004100d005c02410003160741e43c0c8030704d9449020b0740c90301800c001c6e210300a444858070a050006020340500c0041f9941c028202e00400c0104501c656440030025280b00c1c40c4101e41035043c00b80320800c04580d50145900301d10806040c0450320054000c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 470802203 1250 470800953 470801003
    0xb060c060105120a0203060a0b031e0604020301060e010f03111c0b160c032007030b0a0903030506030f0d110a0813061d0a09111605061f050616 63
    0x14509658003160040205203071540c46501868540c2014051921884c0c000c01d4407800000d0081c19480c2d2076800c003403801d441c03c100e04000c41500900d90860381c03030f603442c03038645416040c0c4040e4400c0d800c080020401d082e805503080c1c100c071100048085c46515541e103800042006c000504d9210750700c10010808880502c000c0304080740b14051841507458013050316500f0180354210a020005510000c41c006500032603103a06a150120914012256508aa61421000350002480c0780b42141c2401301e4035215403ca050103a1203500d040c0076541d90b0005141c0e480c030707020406141c03a0b4000042401c000f801802c0f21844440f4410555030002c2168550101c194007049506e9241050754004100309a8000f50008001c0c0c0b80c1086205038081c9000000c51140b0540900c1c50690780d20200000031109030022521030015000200040b0503090804980741c52084408000c4c1c02e40300340c43c0d1a00744070181c1c184001c0c1d9000806043c18840c505507841ca0344a68080100c0e4071142d01c80021b5040500192 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 470803453 1250 470802203 470802217
    0xd05010e0a120504060e0f040912020d0e0d11040e21070c080a0b0412020a05061503070e07050307030c0504051c0303060b070519110d030e09100b09010c060b06 70
    0x2007450704860310341000c030090154082810001d00f440103200300799110551150f80541243c81c14000c0040600003002000c81b00c000400c2d0303001030001e0328901500441c00c0300e181011910303001035688126050201e02a031942005101c0700111000724124642580285c4400c049901114162150740715001c40700c0c1c43d4554075008003036000c0341540c1000b15081404003e40942c0707010344403041c11035840b2414400b01400007000c6040c51050807910500c03c10802115a03040422590181071402c0302c03005254511078030301e020b03000b0f2900110b6443e682003032180c0188030907a40c0d40c1c81c41d40c1d10b00d4110006c0c500340580b24100481040700003250780e180c164010b2042e138280c0702900c09000c01d282c0642190081d61011800c08000d0060202140c004a0300184414a00080c01400c202520b010001e140d22200319a90284048000000740340d8070400c42c43d0910015504d00e6240d40711b40701a488002920720442e0052841000414002d501c00c4207007000e1140309039000704400100900103011600244 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 470804703 1250 470803453 470803481
    0xb040302030c100606050304030e1f080118060303050d0b0a031202060702011a03120913091203050c270f041d10020c060f1005190602010c0e0f010c020d0501 69
    0x101d02c03884402c405002e0b5010783c60075000104003580c940900505103000040002d001c0c00b8000040540310b0b00c9400040c09000300068015030383c0c540ca420f000e000000207000d0100b506406090702660050184210340a480d01510341d2810b10040d103001401600380400082d401150741880000000e045030b000c3c000c10125500602564906450020300b141c54120607040d01100c140940951920041641c4c038051294000c0103658550000204421028407000c0003246450082180c1c14400750b002c03001c10901d22546c0610850301c132010000010b01640d5544211094038404050312540c1e40180356003640c00251010300c01e60140f800043c00c4845402c41561540070951104100e10010721201613070a500c01011400c0c0011200d203586e845400070300030720b642c07a141e10200e110b007802c050f2180010100203100550016429942c00c086194030310882001d503080040040c5840e01075000c813000100e02803c601020450b410044980700007a8070180e0700013140003a0840454020f000d208040324840d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 470805953 1250 470804703 470804707
    0x603040816030c110102060c09060c1204090b0102070602030a1d0301091209050103060503071511120d0c0807110604023a0210090e060103050c0f0313060b121e0304030b04030203 78
    0x2400d14100ca820184c84980c11508400308000c16080100d058501c50307603040d82c1c902d0b203420708a800b40f480e2088090041010880114002401580c0c0343c01001a0032400c0e42035540c8240da800742030740d41c2d0051000c0f00317010500c4c1001c10090003942041340c171003420004002264240da5034595010054400102a0015071266402e0006581602480004010503401800c000e8075203614440c5006400c1000d50801844500503a5078000c1000309030301c0901441c1009030b03110b110f0700004006241689084020034034000014142a000b00303208050907102c030015101e19903c41d42082103040d0300342030040180070351b101e011200016400c104440400c05840a45040485004020015a05401c0d000400c000888144191841c0c0c1d440c3c3c6800030b00c02e003004203954076280b620038110f006040380001e071064003000700400d21038618092001c003070107806c0030051f000030f20046c1700060b103646000e0041c80e4400b01c1d4120041a001c0500c00c0b29482d510180c908007900e03550b8280c61404165025001a800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 470807203 1250 470805953 470805977
    0x90d0b01140604060e06131802181c12090902040b030906010b0a0f0309050c12030307030606020c0d150204080105010611011512030e18281406060304081603 69
    0x405448007814842218120700301468001300500d0080d000050074010b520115a807008540c208001c00003034240c500a0000307817a9045c1c1c02c2c40c001d401010380e0061803006001400c4a43c200410485040082900c0c003000130800c45c2c5031841c50b0707981c41d4100c01c1080070071540080e240080d880038002908110a617a03a40342004c0e904d06140050680000b0f07508041003141191098000e0314010505180d400c021503a48c3c40c5080c0b985c200102c0e600100d40180742c090f100c0c0d00e110804402140b02c1d40c07541d1420000a038481d0400c136650006046811781108001003450301041c0e04280a205e200c14825026140c10b440324015070075202c0c00e0b80084007140140d10241400f8000b8040c13031250800c841d030b024940d185494082090f01412150250074132039000b44844454a0b1075904224085004040d00c81508003000c90901010700c010504c0580289405000e090854500a006882e0b0500f90a030241b510b0f00c3c810840c103640040e1045504007020003120448034035070302c04641250300a842d90f03034460b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 470808453 1250 470807203 470807219
    0x604060309170a09150323070807110601210204020c0a0b0c070b040b0703020903010e0c10031119021f050601031b090315090f05030703140a05040515090d0b01 70
    0x7011102c0d41903041d9040c4200c203082603000d00d42c44200c4082a500c0020710040a0040c0d00400380e4840901d240a9103035000c000781c0307240402c0d0394005d5611355115403d568525400301c03000c29210300c1903011600168010070204110441a01080001c248400c3c1c0040f541d60009049921400d40d140c01c542105911000f4010500b00840d80820315651b40380c6828003540d82d60202c00801000200424030010102d58800d21990640d1062407010b4020440000780604441c1e948a14110640c03044502c1c04078042558400d028500ba03511220300aa424908000d80580d482115040000210f100316200e0500301d146008503048951294000003680d400c0110005068410541000d045c0160111740498031507030010b11013040703e070081c051500080d0b031400d01d807001d03104034140030b030a0201592038401030000110040c00031900c2511020b61540c51441c032102180a08680c43c400f090302801704225500780083c0c2000c420700c0b00c500e01890080ba25002032034034200680151180100440144000c0b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 470809703 1250 470808453 470808473
    0x10b0916020607140403080304080708072001020c01020c10140f12010b09010e01120b061b0c030105060d2402040803070224180d0b040b0a0c0315050105180604060309 73
    0x43d641c1d1400101c820800203030500c0c58801e80c0310081443c4000400a000e0002130010f490241d03078010380c0c0701c0c0d48040c1070800e4021408606809201901d140f02080160741c00055529841c20068010b42100d520060070418000c07581000301050108040b41c90a040072402c004088484414000e540c807007542011020a01c9c034141c1103e10440030802800c040d45c2e07001400003880020074a050b0502d00d00c4c600c0440d01a0907548481a00010081a10401d01c564170b01050782c0d456400045074004005441010700786c030720030740c0d8941c1c120040e40ca03d04040386181c810030075111585864135030042d6501d02d0f102d04907400380d400350245405c046000c7c01113103410b805600c06081c945000440c2d080c81a020140580f0502000702007144d401d281030303901d5482d00c0e450402810340100c004c40c0107181c6400c004503185011900841400d1401455000d664040e02c1603085d11582040c060400f181060015201c940c000ba502146049612820711601d60701c040c02440074003803540e00840d10b02021b1401c0f01810f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 470810953 1250 470809703 470809711
    0x90c030604021503090c03160305060f0114010c030e06070c0e060919020904061806030312020403030806090423030c0d0314131b0902130509070804060c02010b09160206 74
    0x3a0004810300002da950584440d40300004079900c584d498659007286807070200c1d003c00c0d080d00750203400030301078035401980c000c1c00850340038109868007aa68444103140908090155004c91490000106144d5102d80e102e0040304d48a800c1c50500d4480d4080010341d09c1c3c002d094201c6d0740000b03006090140e80900a007840c1c000c0720a030380501007400c02c088040340c407900070f010750040b069000c01d01c8007187d038840d081031004140355461603424524081c3c4442c0500b0440c003042d40814480500525a0940b0b8403c880c2244e80603036400c071068651204200c500703040a41b0542e00c0c4060308518010707101d500302000400c0c1c52040c00543d540d98a22100c5c40c00d115181f800c0c58107041c60640c0e050b440c100c40c4000164002c10286400100c0b10092030b010085042d03031602c0c0080f8040e40c01003c18501880c0d401420768600c888102c1c600c207a52481040005c1100b200c510000a40c00c0c00800d0000741260452401052680000300b031040584020426804044a8005960710021030340000941c0501800d07800c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 470812203 1250 470810953 470810959
    0x240103050906010e09070f080607020d020d08060103021315020c01110706020606131b080103020a240c022d0405010812030115090902040314010f0506240403080a08090c 74
    0x106141c94004151112814400e01d070301c00c103600b0005041c1d96010700a50303002c1d04602c003116283c0c60306d43d8022655048129507840c05481441d07102c40201780006011110081d0695481c032284d40c40000442c06034219079404da56100c4094008107205c03446855924234a0146d50003023510350010000103005416081100c8020303080344100344003040d40810180c0d031005054906141c0741c92803140071001804002d16940c40da400c3c04029001866000005a049070300854030007001c01d8440902d00d00f2110f0f4210741d410001c040c55043d00161b4060301c0c402c1d41c42c41c00145860300800c229038100c031041a01c0715240705201100c0641e900e551070a48a480c0c0502022070081440945c8590b0300c0d421840f040c094004101a00342040c440d45114407140300160054505c299190303075a900d00041e220280420241c0c1d00e50a01d489101030242d24800e4502c1100010101407030746051900354000300c0360354004c50303240d890700704400300104885600403d4414800d50b40d20310b4619081801d981003460307d003000e0b88 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 470813453 1250 470812203 470812211
    0x807030e060c190218011e05150a0f0903050607180b0301030c06080406020c0115050414070806060d0b040504080c0709060b18030a050a030315060305090307030807090e240103 77
    0x44040d10018040445103400c030f00e81c03200081607000150004800880103101600998008500c01c001840440c2e0303884000410000c5507a158030030440310703076289040032040060a00980034428400c80c035107407403c0287e08002000644a454180c1008421158840826100ba014020303035580c4103030000042a80c40f40003419941542d5801c01d080030540304c3c000401030344c140498184940da80c1204c0140f0b1000c03000300901101620441486045171207014800e62414500380404050045400d205e00307000c0e0346028060761900100010343c0c1140f907100c1803481e0703900030300c5003c1d407650301c2140e00840c02040840c0c0c607194000e0043e89070260b560440011a410800c1c1000f60703c9015050390081201c42c0c040e0380160f2070b850017003468174810081c01b1b0020b114a40945040c5a0103a2004a6204141800c3d140240d01c402c1d0640a4038416038061615502c00c0040c8800304c0d125000391034000000d0329001011564030800007020410070b640c850722070043c004c0082000000b011001401c0795007030030240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 470814703 1250 470813453 470813467
    0x1b0501021e070b0a0b0612040f02040e030c0c060d0e0714040e150601030f11071a06010f020303060d23011401061b020907050c0d030204080f0c0a18020d06030807030e06 74
    0x201c030009020304030b0202561280800c5d200c2d40d5800301642c1c400c44100d82001024178144c100300031104590b4100764080da2030f08610301000300020040b26030b52426400100004019030060228076400000c030f40340e0161743c81030984100d0009210407001000954541031075000c03020200004c44007100c014802079440400034488020074528038076442142424000b0740020800d403c000074103640440d90400800025194080040c80184103c1c49035044a06504580d101c41c0191248034030040310402683c01400010342038501044010390691140c01001c5070020130f02130564449000240002041e5103951652420200c4c4001040c010310759485d00c2131102c1200c0080c80300030361140710003a00800811000503400c6015030205c926072074101044a003801c41d01c14009009402ca401031450a0040c0c0c0355058500c2e8002841440b0241c2c000c1844011a18140c8480102003a10000c951020380902403208041118418007009502400446a55210524000340070101f5007030000e100300428040700c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 470815953 1250 470814703 470814713
    0x21b070816150302030c040911030411060405181003060c050720130b0109030503130e0f0702120a0c020d0804081e07051c06050a020405100311120402011b0501021e07 73
    0x8102142c0941030051352904c178144410394920442d0425a03a2034185020221050410030085203d41e001d02009c52614101c141041802c3c8501d201d1194070412810140c8001c03a11060026003000200003502030165680d61001c050307514225031540480c8e404200141488400c051080d10751480741040c0030302d002f150000404645141d120143c00654801034860164012101e00000d10340100480b0346504100c0e0722203d095145008d074010450a04011a402441c0350290500a5509070003410a900e81201d4040190f0801d401000c1001107030541c950250f2104100c420000d4080e210035a511820403880c00d00d091a0600042200071180f01f40703401c2010042100815a40d046070340403500c98601c400703003c80c14841c0d0030190440e0b1a0070144000c03085517038000d104658042e1814143c0b0412410160200d408144c0c18180d0000c007006105039240316101201e60041c814180741541c8104804c49010308046500102c40c0d5a500048800703c030b1003291030740c4544006022449140c10706039652 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 470817203 1250 470815953 470815979
    0x71404051f0302070b0c0915040b0a2609010506010f08070c0204020d11040902071e0c0b091f031512021305060301020c0d2a021012021b070816 63
    0x500325030005400c1600c4410300c41d4040303a101035007151405100f41414103150406d5407001c03414600c11048200a04401c2c42414156002c0300c1002d20343c98245401c6500030748500d040d00351075205240c8a40c4008209144044901d4069a00f281c00015145040000500f003401e001500400b44054a800c103ca1254080898504a54145c9025803540c450140798405003000c001802218900414042001070040d07024084403406541840515402800d90755040d02d168000500210210642400400219001401d44e088050820307000d4a14259008000c4000c45078010000380c2c660030606080380d01140913101030b0044101d1a0b035103108a500107405200140c90302040182c480c40041c066035400c0d07043d140006038403800d40c0c40035410b08500400002d01102013045052400440000301000e1381d848590441e8003a020b6103d00d01d211400340d4030002000e00341c2c18034540030041c00350241c00b019002c1c980000a0402018501d0501940d0303420310402420340461421602d00800c9201032602e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 470818453 1250 470817203 470817229
    0x10b030f04110f0d03020a050d03050f01090c09050a03080309120408150a0608061e0c0a0c15060302060c1506030a0b010303270617060f01080135030307140405 70
    0x42c002000ca03560b03008100c811080c010540d034051600701012051503008280c10454910540940f548541c407075270203030212041500c8070030a20503410014020001c0b10f034031a103203401c510f04003080500d1b075402c0056002801c0c0d404c101c4180c200402400000c0c01c04004400e8041c22440901d802d00303060060855a40c00b01100074120085960041030b60601641c3c043c00152481d001510b0041c940800e050901a2040c49540044031000c000103040b1454401514134800880d034410a03008000d4850842c8079132021030900081e6600d22000005aa4510007002c1704000180580040140c442100d01c1549008061501a8100ca4070000000d040f8080081c15264036003440c010928440c0c038040d20020000c4000703400e44103d003e0200300c070794001030710001c484030241c2444d000d551004240b201d0742e40004075142c00700d44120010300181740304580c0340d036220103000200d003071440c142d8070320700c40301c5211000030121900008141301c0d100350700a55080d000b58882810b80c6c6001d180c40040b4241084481d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 470819703 1250 470818453 470818463
    0x16050603070c0213020d09030f0815010807050c0610060f0507020603010909230c09060f0d060b030109060204240804050a17070212010e21180103020f040305060105010305010b030f04 80
    0x800c04204565403101440710304d401c1d404003103440c0c0190091060017009403010075400309900c0005070166a202e090900e01c51400502403140c802085801175a80d1040a4001d5007401014012901145000c0001601c2174250340800c00409240440103002400031704005010010100801ca0140e22181c045038111030100c000000c68424034100349034510482075901000c4000c4449034400c007100040d0142d20079000300c0f4003009648440c41000300c440366812079180c00c040c00300c2140e400b0800b2584880c007596070140c001701e41100c00ea07865034201e078081e800098418891180d0414001c01c41104050300b1221410010340e6420316444079999504a6103009040704003140041000c50303a14015a4105680500404500e104600356940685802e60001e80c0600c5044000783e903048007a00c002070003c1c07180c59400c0c504821103524941103e031050031030f41415020040d00070f5400c45200188021401040038100179410031000609440c07060f40190240113060042c800340a0789090b0007900581c0c45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 470820953 1250 470819703 470819717
    0x150509070f2723061209060f060306191d0f010b04020301080a171b0c030607031107020913051f0513020a05040209150307020a060509070f0b030703020705070603090201021605060307 80
    0x424426030b101540f081c0c002e9041000844d150805010404581e80510f12040680304156140340c0110b041c2c0364100d81c1c0b154140e000f81c001c60307840e4000d8410710704503050300c40001c107085907036184036001c0e000000700c0301c1c0c0d86501000040707041200a00c42c46d00380d441c0813142989154542030089646103001c1d0701c080c203461081c00308120004007960840d4030400d03018007046442c2c00810403c917102d00c01d50b0a0303079020780a800001110141709200e9180100300d201500c50500009409203ca810b078020a104a40041c2c0d105010101e003003003050380c0180e4049204030410b42d11031070101d01911806042200d40c14244d2004074016602c442c201420f45406440060b101c142d40c00000314000e801c60610742c1828400011700c0940703580860000890307802118180080d440c3c0039555540c0710018403400c04817580461041c0610301c0312000a6811402620300507040156507150380303040140540c086030200355607920b54001c41d40c050100081d020544e02400720080e26040c04200d4600c0001d01c00001c00c490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 470822203 1250 470820953 470820989
    0x106120506010501140c0a230703031d0117040f211d0f0a060504080d08010b0d1805010216031101020304050c130f140103020a080304030510150509070f27 68
    0xd22000e03a040740c0c483c2c0b4221880c7c0581400e1480019044c4040c032810304422013603015114200141507003c80c0c1e455a00c034028a4100580d171400700104580e09410403041542c5000340e08512006940503d00800008221900d0b5113029940c0000c1c0c0580c034200c001003034100b444840c1d045070030f0084415a600e0b0810050307c44100184005c0603091000f41d0002202802140440d806400b0340b0503602070104440030329001d400180c501c08800d02c60402d00403c2080310311141c0300d03d46c010300d00d40a0b42a000ca6043c4040369599401c0ea0403a20101e146141c0007801c013000c0c0359100380a892801001d1000b186141000d494464076080004006409007031074906e1002a01c0717440e8410043e024142d14100301140b880701d02c0f0340e007980080c4401e9100300b01c1150003040e1180044121812254414010005400240380d01009044100d414541c2651150780c001903d07101d400b07803144140410343e145a0718402010700540512840030484040b0500325100070700e0f50b010241e481e02512001f60b02007040c1c110f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 470823453 1250 470822203 470822237
    0xe0712030816260901050108191103070b07060b0117160c050c150405040b011704060504020a030f080706110901020c060d02210907060201090c120c0f170106120506010501 75
    0x14034041415070f54599031054a00300c99103458680c051001d0900a1001d039036610031269a45004580840d458006485150006948040c0780381c400c04001e000e50f21300d50b56500c0d0f00e01090300149015504076460394103100d041c0d80d116088006042c0f502c10a2085d9050100080360035001c1d891788482032104440c0c010060100420a094041a004140c00844a0040c80150070341d0860302c1543c0c000c82c200903100742c00d5030044913002c50110342510b0708100c550791034403040007508000d082643c104030841004004035400e004c088800078081e1402f1a81c81540d81741480c00c032191020254842d0700103018090340b6a9000c04c0d03440200c202294200d440d1641100301e07030024403c0307101c610f072a807030003d5064101120300c0e46030314801c610345c005803001d2a94400c416400c0e6204d0341030041c044c03100d41009200882400c41c0303841c6114080c4900101c0c0341d80303c0404504001003038020324200000901e2540402d2024090100a0005c0e502e02c00020506a51420398404041c000d242c1806890a00c3e022211 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 470824703 1250 470823453 470823467
    0x60902030c120706020705122a0d0602120a0b030309210109061e020c06010b0307020a12180b0f0406030203072303010611010209030a081b100e0712030816 68
    0x5000209420982c2104520460340e504652107000058090310100003204c2c035010200c0503140c110000681103010320000e11655864003c0381d41c07801804018503070709454035003556103072800e4030507280160b8900002c1d80200380c11000412060882e0b003000000400303500c0102c00e4401002c2c040d5482801e03a04140042d03003000540d02c203a00788070b61802002d8010300403141c0203011041c1c400300d542070f2003600c9084180242d1203001034500445d404903004019584824009503030000083c81030719000310b6690f1307880385010514a28035000907142403201c032101e0103480f00c040c014100c000700a89000ca510900d601301c0c0c01240f007003c05059003c80080c054a0040088401c00020740200d0b85041d40036903c80b842c581c00c2809182c0002e1507030300b440d616503d0148225a491140100105980292552542c00d250b00042c0003120300c11140d01c04c044c03014020003200e41a040780700f00205111000b2841a85028881d0384025039640070f02c1c2401c0c002c030b5004210641c105c00c1c00501d0f11712005007940c0a660b0f032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 470825953 1250 470824703 470824723
    0x1506041e0f061a0904060605121308271009140609190303020102220501021903030f0f0204090f1b050708121f06140906130503120a0f02060103030c06090203 69
    0x14110030a001c0124206070018400135008807410003641c1d0b107a02044409004140c640750380954040003140741c88000303003034851075944949074203440c1c40d098560b070341c2c00c0110000e91b803d0701450500c105074031890004a810307102580341c544010010f1510142030030617800011043e00900f00014082e107152500f00203007080f030090054202005a80b481c00138002d51100104450552405620000819940308120101c4005030700400340c0401c0c0c2d405201c00721f0217216084061640e03500540c180d0000c0c6000b00071801e07108000c0141ca4603e0b1410000994440d505a0f15025160007013103000d030885c01d95400c1d0102071520b0899151a80e030b281008440c03040c4d001800005509408100014014200e00041014804030000c00c9543e106d00c107550003c0d0503107055016034414400d03507070103003400d002070441035201192101d0200d03030351008241002c20300440c4088100740021080c242d00d4001c50a81100c909a2004050a42c55520002c00c5440d441c980140390076101e00b00c5805540d400c10001d030b01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 470827203 1250 470825953 470825969
    0x180712050901060b070c0e07052b0b09150a0e1b03040c050a09061701060608130c1d042108010b071104050a050a1118060901020703050601081506041e0f06 68
    0x3407501503040c01b1900c1020781c401c00c00054082e6000540c02c034402e1007641c0d02d07014216007080c400d80f40041d01d10503403d03518603004c1500b580c442440c402071303448000082c06010384c0c0147d0140350250344217000504c03580b900054130500c140d1003030001807141c9802ea038490030740f525034454907a11540780001c0b61881541c800b0f40e002c0314516000ca031140b010750081045840f41160712000110860b01c0c242a035103c5d100d10008162450000351006042c140c1c030400c40703031088408514481c0c84045a48001c0001c7d14048010040007040008000e0b500c4819012182d1710390250a0b103002014008015501c14083d0300c041c140d000c9210700c100070040c06541d034040d070000c01c11301980c81c2840701d020080604441e492141340c02d0030150200c1c2580a01104d201140b0741c409100e56080380b80901c0013552040c0380e0300e0704610480340e0010101d0024850140a083c56401074503140f00540350280b1141c0b8090b00240c0305a15040c0500c110a03112a0101e011300d104000c04503540400b91368142c01000c03d6440520 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 470828453 1250 470827203 470827207
    0x3040b150a0914240d02040f09050106080a1b0e06150f0c06040c1706010b03040804080f0a11100f03050709050d110306070509061209010219080402180712050901060b 73
    0x340101803110b180e0311801c065413682034041c28481d000740181c0368000c40a40c1081e40591414050b00f03150708440b680c3c003007244020a85512a59034542101c039280e00180054200d0440413041080586140074146c0d840c10241d103420b4242000400700344405401144540d07240c0000801c0100d0410580f003c21a8216901c2d842d50b404883c1c1c0c54032288201c60440c0c0c10301c83c80c8804500c190301d4841d0400e84190a0000702030682c20007040c0e107000d6201900650704450107120004003044100304000309a1610780107024041d8072481e01c600000340000555105800380c80003840e11503480400010b12000038038002c552074489400035600d14043d030704056004240f00d160382c0c044c000340c0f44070071108907026421110b0a940740d100c00c850742d00400d00120340c003d6040142c0b89020480105a43d0032407100b1000515000e82d008500f8a40910f0450100129050b50100025443c1410fa9001220981c40b0309200601e000d2400410195081c0c102918265465011500181c0254002400f074001500826 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 470829703 1250 470828453 470828471
    0x302160818031005100e060a09020307090f0506161101181514130527040b0a050901060503060a1d06090703120f02280204110301140603040b150a09 65
    0x10005880da07006901a2007003603041c084080d00f501c5014414003428100a40c2c042c03d1012030f4080080c0588010713440300a9500c0406d00042c10b02c0190f005180c41e40b181084146403400c1141886107a910880c80b8800c20f1003414601490b00035981a910390084ca41d9003603052040046c0c40140c4482004030344910000c0e0081440020b11403014a51281600c072500041854200e15441c0d22904021040984500745c2c108258100070140d0001501c0d1221000b5100c80c1c1100313401a0100120703019542c500040050103654542e510806812100b140024040f040c1420003090355084080e05810070340d40d996001450f0b01c8028480d03650140030800c16541242001c0702d0782c80c7c3d122007a000590f1204400141c04124034010b001070b140150103070700030740030b91b40250060460300502240170b06017013002c1150700e0006941d0307441040443c4003800a010307103950401200350f40c00100700075060301828041052101162903081c015074051015441a1010342c0040041916041d8a9100807000ba007080118 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 470830953 1250 470829703 470829727
    0x80a020d0c0f02010e01020c0d140409050a0b040b060703020703020609040b04020c0a0209060d1a041104020c0f0d050f16020d02031c0212071505060a1203020f06100b0a03021608 78
    0x70410102d0b50b500a006580004000390b080384540c00607030318260310031101c4400190107001c030f11050317040103505103040c10380e141e061106840702254580b00f615602e4508034070500d8244903ca41c0e00d8015104507091010560b40030b5030300c00180c0006407107402c0c0420450782580d2150001001c00c14042c0c420764885001c280500d9039203101c402c1c12403240310418000b403a41d040c49043c1601c0300d40c00400c0e4450840c01007100702003018001c2c00a03500081c0506820025031200d00081100c404c200b0000c002030100449001c0c01d219881903684c040003000c002c0c5642a9049a0030780382d42261260180050304100d01c00100c2c11046410029054040c03200702ca40b5108001c56620b40c1c2d401079400750b0740c5440f1900300001a40c441c6100080c10b40344001d04c0d11034101140d034001603000c00c0c05414581d143d43c640d440549521004002100140c0c010b0390722044041c818402d0b250008611403e42107460b00f410041e076200e0040c0207a005c10035901103042c1e00184bd8070054192400d40000189580d440100d001e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 470832203 1250 470830953 470830967
    0x121206050406060c14030f030c0a030b0a08060f090705010c08090d020429060f0d0c02011e0c031406062b0614120c13090302030c030c0f1b0d03080a020d0c 68
    0x1309850010510f0159640710344040121444808140c8a0900e0359560500900580d0445218001056600c8442e01101e40752507060801600c00f88005100700d1401c5c1c0758a4103030074070080244003943c01005040019076040440d80c2146903000005540362a13060004c1044003002c040b01950041c00c20000c082c04101d003140e845401142030015143c0450000e0902c0101d20410710300341c43c40c000421080368400503951100072500301c14800810103890700c40344180b00c540c01419040c105035075000302c2c401550f090f110b0407618030034507003649803a850584c0000e4480d020710304448581b25900800540000c5840d105010401c03004e2000b00031440d1100424040040340c08640c03409440543d0301d000803140d00051600481e24002c0030106040000c4001e04060400b100e41101544020310202805038000e001402807403441400030300015600340d000b5032a101c007584600000c000d501c008008580c403101c54215940f605810800440d86440c9500d000920488003a20101442c25048103055503110349 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 470833453 1250 470832203 470832227
    0x3010b0c0709060b040303030509010e15060f03010603020f04050405030c0a151a13020a02030c030c01020c0d0807080c030726090601091802100e06033112120605040606 74
    0x1219001030700c0e008140c0403529503001c0c4c0144c09000340801c00010340310343c100c0369008444800201d1018a551603c0d4600b0404a850703120b99800c90341002030724103007400a5030724803001f03c1c024000b1914580204507241401034050b8000c648840001e001d11408004803040c20f01404112003030980f007414030041c03007069010900f0243d0b040800e01500242646040c904c04880240588400805503121030001e500c079030400400c3d40401c0c00a100301000a0001d403a289001000250b52101401d0405080031000703014201484105018400134952005a00f6400307003078518410b503651542d1800355912408a1040240122081410f40084680f6000d080c022135000d400c440007662100540b40541d044402e441031942c907001c4d4080701515181e08100b803041414281440c60f9081000403c44552080300e00e1064074581c80a850350300310300341d81c8482e00440e10090141d01c0c02c1e00e50392803110040c46070100c8020003060011400c0c045540341c0c001401003100500400c0180e945041c06002101c0c7c440c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 470834703 1250 470833453 470833477
    0x61c08180d0c060206330f061b060a020f1c0b0d050319050301151b020405010f060e18010e0601020c0301230a180305131d0609090109030e150f03010b 66
    0x20101e0a051145601810288203101c5081e90061a01c0008686c0c0e40420840960001242844181d00d881e024005c00710a400603840099104070702340034600e090b2001c0c1008855601c100101e010b10107940050301c1c10603418207844450340140c0f6001001509100ba01c0b150b1005103240706104002001005109145604400048007403400f0350980f00c500091080c0d05e8031640b01303880d850700c2d42d00c0307614503252a90039044000024003003070300402c08030b642c00d80000040c44044407042c0b0400350000714000c218442120416140c40d215503001c0f007019410b21400601120310b00209280360300034000051010380240003044160402c2c0e24003c031074042e400000c0b489031030b0b010206004501c240200320708511400420060211030b0b0741c0c115610ba01002080820543c8040c000c50b40d2015000311101c0d2910b50109010b0505118040043c2c0340c502406100c2203a144c14031000000f86c200c1c108600305003040701d2503495500e040c03003120400e03c0340107a03085400c0300000011501858410151890507440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 470835953 1250 470834703 470834713
    0x3150102070501020303061504080304060c0c210b190510050a050118170a050d0203030a0f29060d1d160e010e07030618090605061c08180d0c0602 64
    0x5907110020360142c240180c1081001a88900f41500c0c0d0540c29094141d00510345540d403803485056800640158001401c840c1d458410b0001603440c0401901e04050084048080c0b40940d56549404100080285030380400140312a48840000641001105000d002c80d28201440800c81101c44c0034062003a0307003210300420554400c07000d545428036400750401d0b402d400c1441c0503051140c04c1000c480e09120b161003c00004030203022807100301030240c0095480e400c11030f4820701682c054032142c41c149440e10524407030f65860f42c55011040d1102a1041a00d02500d0700031078894420443c002900e5401e00000e6542440005c040c56a0031b4400000d4600c0b041c0c00c0401c3c800300741007500ca0307560800314080052089a201008582d003190450400056a55403150b40b09800c4030f920343d0f19000c10780c0e6400504140b210302e00801b03601250448840a800a0b14110091038401c9080d014251036804195000305a0014600300c4080b04024901f90f40c0c03c0d5545482030301c40e035160103503000501403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 470837203 1250 470835953 470835991
    0x10e030d08010e1003110405040609021507030914100806040623090f240303091806190f03150f110d0c0320090d0816110d030905090a0e01060b03 64
    0x911804c102c26a036010040310500500754040002400300500107841c00ca07503540c00140142c1d01c550309001500b8800780c0f803544811150502914031400380e4403401001103540c00c80701450352100610441c24000342010b0002d5113400b0041402010103401001650141c46113130301c175403880803210b4511f030340e41260100201c0d80e03a0030014200540c156811140654003026406040c10301d0125a424404080d0031a4146104980020140c400189400207160120800d025480c1010300001000754401c0841c11a0603181410507426258140b101800850818112645008141c0c01c03c41e40301240d5441801200682d0ba0300c0d94450b0720050b542440a46032544d60181140240210041c0402040040b01c5401d00b0300b248600550140040c0b83d4000740200b21440001e0f100070180901c00e004000c096107a070310620b007415280750143d0b503013442001510812030002e9032015040e81650400d43e00e1860544420507014090420441440344a509101d404135442c0b007207001951055001d100d4400800b96 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 470838453 1250 470837203 470837221
    0x501050609090c1e0a0c02040c080405060c0c010f060e060a0603090206040506090102030c06011715040b070e06070506040b101d060f0d020a080a050708030f0403030e010e030d08010e 80
    0x82400d03881c64106180c5800156240d50b00d101034656050048058080300c1c41d000368240f0154003014540c00070030149541d00044d0b05180c490550f150507281460181d07401e01d912015580c120046c8800000b680000781104e0443e02034000440350865084144070755a105c0c0d0100685e40011185640141035040e80003454034400d004041800760042c0080c0d20b024100000d22245a028104581c1513100070030a8085001082100500906590314162050710a107459030307081002101c0400e0b1103903000070501000c900a108403d422980e14201042d060f0102d001003040740c0140300019186014210400080c0582007004900c20800c10385641410b50f03c0706c5c203128808020300c12840040c0c585400090f0f0784c0c01c0a5840c0c1001c1034004103004001c00f00c80c0d00041d030f180010307041600c80b034000c44030550800c8000c1019001a244107405181030682c0d440d4050344500451001804204800c481002c01e0f0740a4034107100f1000000d001e83d0410408000c1c00362885d0401c4c0300b0040702034004000111040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 470839703 1250 470838453 470838457
    0x12090a082a01091a180910080d030b13090302070e1005240d05192c1504030c06110307030e0c0102030405060703080c0405181801050c090103021b010e010f05010506 72
    0x10b00e114840004501c0d105a099071540140303040a0100c601d004408100350f6440c0400c0340b00c7c1a040e0410807445041051840c1860020f010a01c141400c0c402c40c0e01281e56090891400d810360700340c00098490309820101c0c503120781c660041c00e90030901d90602c010070880c0149102964800d442080450b1001c88904044079010100c074104004240091486040d0b146c12941e00241044564615104503803480b1044403443d040c440038948081078140c83d1004c01e202c5001e03807c21024081d040f0040c3e0100a0f07101d41030001d0005003080031411443d02048625803008000121030911140c40e0325129102030010007001811800c1d41c4141d03480d0000540c40042100c080d504040c6c242c1d41400340307564094070361160191094084141c10701020440d03494020200c200d940c0542d0740d078202400c21103080c070500b1110304403000059041208001802840f80308461b0051004c0c60010380e1411400304825000c1e0142c2a552015420702041030100315054110a5028100c15000c0020b42d0b61a000c01c5035034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 470840953 1250 470839703 470839709
    0x3021c080a120c17011403070801060609061b020303031317070b15030d020d0e0103021b0c090f100510051b070515030f01150207030b01030602120112020312090a082a0109 75
    0xf00e903500006100c4207071a090b61b0300c0c520101030b08403a1542d450310070700ca0030b50380c1542004c0000307002c10707004014040c0c1c40005080c540302488030004400450740c011a4072441b0046c07078038981003040300d410401c1050800e00d5505500030b010005403100140d1608982c5102d042c2c4040c0ac45001c0c0d00f4142049290201741d180c00c20080c1d0f0000c02829400e40300540e032880341c03101d8141c1415824421341d4072120010070440c07074804000005d0702000c4c05d414108a19107001610042040320660100302c1b107a00314076030240a542c42111440c00f10100900115141e00c81c410803422040d0400c8540e031940d10002401c80e041d42c200300d0304092120307420fa01605640c00101c0380c1564041c0200f00412501364680c1c00c00c081c0880b2481074803003254490b101c00308080c200781e10450f4030743e60006000115003518021030307000d42034045c03113501204810b0700026541d805000c81d5064515001440034070540d04c0c0c4030711200610201d401d80307a0890302c10850302c0c90101d03403a02070b81d50102080311120302c541c07103144040c0c1a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 470842203 1250 470840953 470840987
    0xb0a2706140907031508030f0d151d0636060d0b0c07080f0a0509100503160315230415060207030f08090a0b3103021c080a120c 56
    0x42666400012405002c448030003d010a481c1e10002c06d0700b5a0034001020300e600d20601040d81c03586c03800b5820044842c1c80b40c11051518a000d402d0020060034420540c0b04104000003802c04d0b00c0300780004465044044040c000c810410020026030258041410f503c1001c49034021502d6640e8001d0059050b0034080c000d10f030036070030300015081e00d5040c000f806406018038085400c1c2091108a00695407260781c060021031000300d28135041c1c0c07038076100304425030030389141c801e08505040c4491058104a05101400d068480843c00711001c075501030030000740b11298401038286500303840346050303480815030725000e241044000303015030354040c007060100c4406074001d14642d4030303603164104481500071b030881d801c000c1041400500e42c2c50116500c050403800c00c1341c0e81d403017804241000384040c80c4440d102c54a42d07100d6603158030008031801c0000300ca0f0180e07404081209807080042d5104904070000f4000c41c0042100c980f03580d84124990381d0307000c50410420401080b220203946014103a080504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 470843453 1250 470842203 470842219
    0x301080d080a0e0a0b0f01050607331e140603060601081f14090f16050708040504060e0402090c030405060610020f0d03230c07060b0a270614 62
    0x10540c42800c040b5404405001c0002c1d220f8404400c081c01d091440d0307415a0f20700031140600040c4070103075a880f401080111802860400e055542591a071b00e4492a01001c070f4100110030301c4201005c11443c5414640e400421a001400c400c4c1c5000891300c49082040c5440c000000c14500b0f80e10741500d00803103009000300150780e20b40c4011581305000508401d0001841d0010441d0020303031404030805008540c402803c101d403040c05100f507180d0020228110030000c10284456880540d0b0100d064400d14500103035510010304110817184944d510079900180342c07a000103011009087c415020b24400c07910034144e42c50b1040070b021030340419100034050303400003000b08900345010310544000750824010385110190484059003424101c51505003c203071070b41d1800540e00382a450300955411190031030f40d071034100b1800034126801604001085165110b89440959544511000090010b007100309503040441080c480032a0031610040c082a06041002c54003480d41d0300a56044000a0070460f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 470844703 1250 470843453 470843473
    0x1006090e19060903091502010204030201030b0102061014031f02030405010c0f05090906040b09180d0207030b0414030f03090d1706060711060408100b190b04140f1201050603060a02030108 82
    0x50018070f803c0c0e20403803d201040034005081802e03071811034040452030300010703104da1860002406a41c820910641150458400c008211400d00020301c156864940c0005050455030082460429101103420311007445200340091000160029032180b40304a00070f0201401c081000c0e0b401e02c001080800c0402d00901c1650072034142640c019500410052000c2990b00e00c21010443c4103105172400c1040c0d9150345400c484c42c1404005546200815100400b00185142c41d445410070b0040d000802c02048180a000b24000c01c106444688407443d810036030724102180001daa0390701c2001c640c0041100090100b107520700010740e1500c100c20180c4010b00d0420240d481c4001d01740040113450f84507405201c040b4440384204203203c0501c014980004101c50301c08100b020440c01c18036841448082054140810004041034030210390417001c0a0701e0f5506001c1c0040c15400c1011409030b0011803601c40c2146101054000a015407810b0301518078580b1001140c0080c0d03c800d028400d83d90740703c2040300b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 470845953 1250 470844703 470844713
    0xb010e0a30080a12140f0402120c0f1903061812030506090406091721090d0e09070323070f032703051317060c071a13051006090e19 58
    0x841d8113814103500182c4c003000788010201d01c510545a01ca940e5240204100c11400c05a140d441446000401010180140000211b00401c010320441c01440310001440214a80c1c0c00308402655001c0020300c03021800080b02e4a400c481107805450690490703020886140c041e104280c003540b80030300306441954031500c0d00c03005480100e9003141c0d041c2c000f01c500b248400508024003842c03110000170890030000b41c021500f03220806801000301343c0050f0038103a00581c006610442c40342090b1148200d96803004015030003405400300c0c41c03600b401110b034880b054001a04c2070300d06c92000380c0c651103d6103002c5441181207600300c160603030241c80640004450306800c4810080102e00c00e00d407847c907101440140c014403000d41c2e400040e032450036601714002503405000707007540201132036011420300f42d042d01c845080051401d142e43e03500c00700030040748800b13a8a01004134499000001c96280b0b12601100e0001070202d4400e1080b0903140281103007000c02c0104841f00c02a10050b03040070760f0302490b210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 470847203 1250 470845953 470845967
    0x100305041a040f12081602060603070501082503021b0f2d010207050336040906061707060e010f021510030c08030a030f05090a03030b010e0a30080a 65
    0xc2a224050821043c5000030503941c0c0a40071003c2e2070361003258909040034280c0c03040d902d44c16184155005203040040c42e880000c1d4820407250709182824040d251640c640c240b1050b0903070041d55604031680d20081494041e0001c0181c03400b540c46028014200c4c80d102c64640031000804101034002c2c81c090036403410300074081025040d82c0d284210703042550400850882c0c1c014203049685400101d10324225802c9910b15030240e0798094655041400d4174a00c1d100440d0324201024451556021a00184101070388018040d21207501c040442c000c0601a01c2d0342c2c2d41c03d910451001404080c8040000c3d4400d001c0341c2143c01e000e400074051204032100150f54503000a0035400304c000a0a40000815048100c100042c009100a1940c0314403408000341a14138100400714068101400d05c4000b100c0020244041c6816190001c4c941c80d81070012250a00f00c1896036a03c120341c40c40200b00900300450062a1141c00140d480c166040d0b412060350103100d105003d45020300a1026081c050b010b440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 470848453 1250 470847203 470847211
    0x40201090f1410032d0f060605040303050d060504090321060b1b0a170705010e0c0604030209090a0602040906080c03010b010c26031005100c0c0521011406100305041a 73
    0x10049141c07801412500e5540400c1e04240070711170780c95007000e810f6a201e4401c2c000c460820308400e01c140d60800c4400360540c410391100030f0130440000b40323a58600440da40140c000d03140061051002d200e6a0034011719801160302000240689101741421942c0c4902c40c1e1422507007800d003810304118800c49101420450f0485040450045003003400c0001c8298a14030003842009a08a0b20b400c07480c201a42150a040c1e45406e190340200c85928150f641c0030180d804590341126440440d81e0b50302c8a0078100360007481c00510741400400c01203009081a0000001e89100c0011188005900c0c81014241c6034010b10315070204510115540c08100d18152195004d91000101420708100c455601c026600071512049900502d00c014007084c5040b140d642800700080c40c0598843e112503c52905204440c4143e43c840c01032041a04000000b041d815031181c2c0010f002000440b042e4181d9a0900400b203888510030208403803d1301c1254000c0c4507c5028680242400f13149150301c00154440c4c00c07001e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 470849703 1250 470848453 470848457
    0x106030b0402120a14010e0705040e25210204030f02040513050609010204150513061808030408010e0114090c060a0c0b10030b0a200f130608040201090f1410 69
    0x840b18a02c08802003035140102c01144c000030300391041480c22404040c06803c4814000c1c5014184400c99500509a81c2514170078903038002c05855401058800202c640502d00e294945841c20034070040c1c00c1198070340c46e89884d540d41c00054000d00540300c2213104500008091203100c103160400741c18035038001a842111142c01c4020741302139443da113107440f104541c0c0443c1c6a400250a0021060040305117001c00d255007841410030240301c80b07005c001030141c01010100714503040741c1000c40c42c103042188004d19041040e66512619030718010b010f416100202c45040d800d052020006181040c00c00d80301d0b800750b030b010301760840c882010041140d0040d080e01c0c0401c0705c1c1d0040c910204c0c2010255a0040b92a8101805114034501d819101c941000f0200010a440c0c41a40d0007200340e455446841002c000700c64030381d102840004004580250f42c0200c040c0d54024202190780f5410182240c081c5001343c882e0b001e5156100b40741c00600045000b0f8480801d00995110f6941c00d1401c40011104018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 470850953 1250 470849703 470849707
    0x114040f020d050a0c0807141e03070b0408070f0e04021507030201290a080303220c080f1627050a2004030314040e0c0c0a0b0c0702040b04050f0106030b0402 69
    0x55194036280130100c0c0b4080d0351406000744100710340c00081000400901005ca055030f6000711001c001388039560710030080c0302c00440e80c11079011180d4040c005a005010f58400e807648890701c503580715588001900400042002c0c00b0f03c081265040044614460342d0700034504502600c0195032a4555003280750110155034070340c2803815154000388462503403560044210319030004000c08100c1400035540c0000320715041001804030a090a920108c1e550980c070048403020b40d4145041c0c619000603601102c2c542c0501c01040d00014000310340100001d011400d102089611a041080011002410312140056260307114070250326580280e80d0203541d000f00010b0140c00520328805841c051400c0302100040010180105500120440300d480200d0b491181441d090036a0091582409401e14140240100b004292500c0c20000040707200d6000400c1940341c101103426209076001b03144124880d0341402c00e6214281003134850039109000c3e00c14400e0a907440d200055000b00008031360a5081602 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 470852203 1250 470850953 470850979
    0xe0d18050d0303090302162301020a020310020705060f0708150619050a0f031404240c0215060105030f0105010e0d06051005041d03040315020412030816020114040f02 73
    0x110707540110407501a440c0807a491041e8680207040c61104551070516130521030040c4051104240500c80b1607400c0c0c0c07a02030300c5020940041c0d14016401100039450f2107031903001c0703038045455001341102a202d00221110341d15050040030424008031414000500d44c0d40015442056400c00d5002c011340c05059103140ca182c19040040d404805190740000c1100081c84100142d8007500240f0240d002e031800304224500041c1c80c1c1c0710740402410150030710490b000201040300c0b003516420458500c116081003030003421030340039480d0010076a0207030b9200340c20b1000500d60f501910840788030b010280d0340c4050366800e000042d10381c04804199241c0114460000ea00001c2591040c41d00444002d401541003500d80300400c8160740d115045200e03003441c100b4034580082e0001082da410f0381e500c6118171440c003640004080c020b008980c002114408140c100a062540041d501401000070458404140761103100c2a82070740c15540001809810501c00603002c0b0384141500060700d4401000c207100500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 470853453 1250 470852203 470852209
    0x80d020a080708031b28090f03111503090105070f0f080a0e120705070f0504020405090c160803130506060301053c07020d09050d1106030a0f0501140906040e0d1805 72
    0xc00c1240101c0000e90201b80c0317220303c0c4400070b00e0345080a4907103086200c0c1001203143e001841d0348030080421038003020702c1c0069a510466071003800c2c40120165203a2501641940c041d00c000d88032100850214880250440c1c401c01095510382003940712020540c44071b090701c41c001c188070303040803d090040340d9415404038000300081c040d8a000b00020606103040010128040083d5440380744901d1040004120310384810426990224940d001c1c20707103c001d00021250760354000e1900400c0c4020000c00c00103004429420001c1c0f1034010310071945150b650505241c03c890094501030344004200000010000c043c0035212001e00386800a010181413041d6488011308042c1c42902c0540c1259040b019440c0d0700840060042c1b6040f219015030110f90380342da0258440d800ca10070b000c1e030b00c0000001e0790f01a003900300140c4081c07060000c00042d81d4580000c030000d2482d1022901c9010904041900c0e45800d0250036080002e2002038240b04801c0801941c2c28001d5044207c80f04200c58000502030b6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 470854703 1250 470853453 470853457
    0xb100801020a0c0b01050906280807060816180504020a050d09030807020f010203100626011412011509050402010c0b0c13090c0e01110307020d0c080d020a080708031b 73
    0x407049854441d4503039440c0c0b901890304078051b00705a02030000c1204001090b582c5151461031a03060341e5828035562034000500a150000c3e801106084c81004000280c00f9031144401c1d108400015055250140c4803a0480d400075100304100694050008288203d02d0241c0c0103103e0b0f0b030700a041407480d154081680c08183c924024050b8082100702d020051102d806012031842c1c41299230003180340d40303403110100031924034501502c0c04110a0302070381c1040450700d00d880d88010b0f1f29020001410340c0d480d8480013521202c0175440e40942107070800340b00740410500815004100e524003004055051148140040400130001da042001341005900414211194035000c3e800103004256514485000800042071980c8040c500714a00000c0840d00b0b80d20031180b80214000f460802003051340d604016103540140c490107540700821000789030030050385601c0c11b800c4035100e03815503005c4c0d00c8c002c0c1d0990b200e962015010b02000c0e801c02141000585101c011580000400040315481da02012280c1c165 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 470855953 1250 470854703 470854717
    0x105031317160803010801060b030705070314090405181b15251104180f320304090b0103050403050403061503060615110d02070e040501020f0a17070c0f0b10080102 72
    0xf030b001005100d100e00a00942001e8415003090a2442c02d248034001c050b84140500a0100300c20119140d10f11500207003103c0b8040d800610600041c102100c13080000388007900d114402d48146001c02c0c54404640740390802858005011100c003400808001070b8035403003d0b10800000400108009840c0b00300c0c0c1064589038080c03089515240130800a21040b15801d03010007442041055041c400030f00103841c213103015035200c0360320071360507050705510001074942548103040d80c0303070a0940d506107c41c000050001c460100005003c0485241f0040d02118019100036000a00400083c070201c1c00c160020407050780d1150030344403895503903220700c8115040c942040b10700d4009003d154440075480025000c141c0903a1015000311091804003941e500e07800c0c03089140c003c1198000406001c000e5040d0745042625076140c40da541404036006200d60b440500e640035044640e808901c03641d115100c04107040b9800b803902100001c2ca5298400ca040f8000d10005140030807510109100e10280050110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 470857203 1250 470855953 470855963
    0x40207051b010c020607081605030c0a031419210c050304060b0a080d0309230c090c040f05010c060b13020c07050103110a030c1b050d0806010503131716 67
    0x41154011800c0c007804036001d4140d0420207a41c07848405170365a072040700c407207030382c40240f190303854440002034408241c1d4403001618501001c540185004408114819107511075139450344240700700b1040303c030a40151410750600c001d084040e60a86800b65401c00361003210844907520b0100a401548191003020f030320040001c0012060004000080c0185500006c0032511000d10a040010165581034440000c404150301c0720112014041c0c0e18180d034003c3c1b1160790041d210100f2009100d40d540841000040c080c0300070000156514036460b0545061720007a000009800340303404011103020070784541c10386030b040d42ca40103080c496544500700311207811002000341e100c02e803d5030080d042c40c0c1164092b90606003400e01080e40e00c0c0003242101c0104100d805c001428000c58013044074840070641c00d0243c1074621801d08002d11200060310108100659240c0c0415590361004513503600050f40c0c904c020059031103004000420f25000e004044260084442c12f11141d40c0803141f8261a010094031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 470858453 1250 470857203 470857213
    0xf15070c2303060408031305060a0207030206090a0b0103080306010909050a0e1002040e0c0d230906131a09160605070b0705030106090e100306110d06060905030717010b04020705 78
    0x8020540c0c480800802803116810740041100311020a407a000e00800c014140003000000034545c000d0b1801011880e50400110384080c40c2c016000b10007907000010641c0544103e0700001c0e03400c100000c602000380d600c00007040c840e0f407035560748405a4102414103414050a0080416190724038442c0510400b402c150105413030540c200201c0c100b10344003516143c040c0c0100024005101e0062007150030160414000e5901c07104d00c203208008080240c40c00e16000101d01c00044018400c918250045002e40c0c2911300b030740c4075020500700d038059000005203d1b0310100000301c00d41c081d004605a100b401d6005460382e06030f4840d00242c400c54150070010215001007034510070f00800c018002d9000c102420014515410542c014081d406140b0448070100341e00d0780000d0024070020140401036a1110b41400481800b0b000c1058a401815a0800700e40c6030800014075203108001001c1104e50150140c44060f00b004102e810080708201c0c802040e40d00c070030b01480e040d16248010701082c2d0062000d08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 470859703 1250 470858453 470858459
    0x21003051b03100506031005030105040b1027050711072607050d020607050c03030a081f06211b030204030c0b0f040b07261b01020c0c0f15070c 63
    0x40e81500c1e9192201c50088060041040010703041002038282c0700101c48042d02e81d642d2000010361030b00c1982116806500701401c2c081040341c0d07480c6541c0100084414080407648400340c01084c1004102840d640803440f411621241c05075a00c02c41c0c22100e02e00e46031012440c0c00040b0381c03030201103a02c200c01d602c8001640e114460095842d80e00d80e03906e07075400f0f40529458807000a000100150010344512000112541004803c11010304001d0300513050720b4440e0703c41d400c045c01407a0126504980417a03c1c40507540c542060100040c1980c01a450b600141c002c4401030483c15800a058030000c60b5544a01445005e009041000401300a980169a40e42545400f1030007080550110040d2a000e204030050440100142e400362201e480c0810380b01d0b0982d06016024401c680c003440f45031010203060a420b400d503500100040d200c0441040c00075415625042e00301c0c4500350a164250f0041d8081c0d020034a00380e40d240341200e4006001c0c414141c00e811000c0102d9020072402c545410344d64400b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 470860953 1250 470859703 470859721
    0xb01051905071a010501030b010c051203090a060606020a030e0102010c0c170f0408010902010f0207030803010b0706020904020307120605010e0a0302100e03030d0903080c0c060411060c0d05071704210f02100305 92
    0x26070708c000d1080c6084a003c4034107a031020365603910940c40d00422000400000c0392071204100401d10680c001790140030b441d0365584086d4644041040581c0040c801e650a040c055005005000c0b64464070360741e021181d0999103e00c481440d01076000740c0c200000700090b140b190040340141c4007400300304000048020041c030001d404605d40030032640642d0441c1904102140d504c7c8247c0c0d04642d51290129580c40c0349140c0440207105054003142e000780302005003c085503100412000c2c0103ca2a01003198640740c134010350b680b600b0904003c0e80400120028401800e00344210020070a450403c1c1900c0541c61001078196040304000380e100d559900000030038507a015207680d4000d0440365215192080d0901040d481d82c40061015201c02e40a81040340340c2e0f11600c00b1107048044e0803050341c680c10010440201190b000000035581c0070400c40c040e80d030400c4c20070f080394121400c000003610380c003107110761070a41d510220302c0540c1c02014400304403002d42c0b00c05a0000301c540791030350005001d10b0900c1403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 470862203 1250 470860953 470860961
    0x7150e0904021f0215100e0705070c050909060f09120a0315030618051c0804110a2c1821040909060b100e2d0a03030f0807030b01051905071a01050103 66
    0x2000d5003c00350a400c02080007181402500100c03a07103055982cac0d40042c200300d11001303060743c001600300c00700c0c03002c1090245011030080d000395015080b4144d644c44c1e4201180da242e070003050301c104031803042102a044a001e580714200000701503a204000310b54944840301126a0301c04900e01d001d8600700c55008000e4107004607051100d031030302003604421900c0c030000c2c00e203480200700030a45041090f0302446a9903411000008244400c03900700c0900d84031a6844240c9003551000c170b44d940d0603101060050380c18a11808000006600501884d000365500481c54011803400b0440c6d40c10405c00807038200194015482c485000d000080391a500f024203200c11030219054806c1001000c0d03152071401d55840c0c0c114880c0204007019130100000030700b000034a1910300c44002d07600450f0740d0400820180c001300140141a0755840311641c0391f07250a0154143c03005400090300085d01000080342c140481d00300540c405540d4504141000007075624964404242c0c80e14203410701d000300041041d981d00d800307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 470863309 1106 470862203 470862211
    0x30403080916080c03010e06040213020322031701050402090117071413080f060f070516020d06060503010b0d150b010302130f0302010207150e0904021f0215 69
    0x3d41c2e520800c0702d800500a509114800301c1d402e40101c1c203a8896500178003030314030b0003010031031038402944010110210b81c45c80c0117002490100300c050002c00188252120003210000c19104145200142e1081d84160b00400180b40942d900007079999a1000c99800c5044980743c07a5001c0d2001c581c45081c6101c8030002103a05983e640359161454220740c41c0200703030303500030200a280715100c0e001104d415904443c28400f00300820b100e040240500107a404680209034880d60000721071580501d8180c801700d490700020b101500e828407404025038400c550081c20740c1d88071b039a0898204c958000c4c0301c1e1107954600340d20138680d00170380440d150b0100e0b180c0300410042c0c5a2518174034070149400140c1c014401c50201040000c1c4200c410303804103641c0c3c0c44190400d2409420040d4421000b00103e80001318601c801111071100189140da0200036000750111034508204250149130040c = true := by decide +kernel

theorem cover : BRFrame.Cov 470683453 470863309 := by
  have h0 := BRFrame.cov_init 470683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 470683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 470683453 ≤ n) (h2 : n < 470863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
