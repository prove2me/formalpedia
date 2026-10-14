-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1401
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:47:35.898625+00:00
-- url     : https://prove2.me/submissions/22733c15-84f3-4aa3-a126-9060691b2487

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 251798561 ≤ n < 251978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 251799811 1250 251798561 251798563
    0x60b010201110307210c050a140a090512150f22030203041401051c0912030501030b010e15031005010503070605120f090a060c0201020d050603062401092301090b0309 73
    0x201420b502c05002c0000250703040703a54040c88903079840414045c00e2080c0000b1500103881d0b80c002401c18004140091490b48610560100b5912402041e030b0301c0600c40c5203410144091900300e44040101ea004040c4000b41034118200c04900884107030011101c0740c03610440c07480c3c0000c11503020300a16501ca80705071000c260300005660580f0350324070060880c8900c141c0165014420a080c200f052051405042d40c00e0115904c40240c55008a024071180c0003c103008404403a03007400000e100e50520300c018408a03481d081e00c2544940399504220721900c00d40e00003468030042d1081c003040f2940303400050015003400e202050003899541405410f182e1090b4401001e07402c014012461240d444c8005801080d0410008281d941c01c91020000c0c1e01c0b00d084002d020b0740c0084003400c0300c142800003082c400c0c01c00041d4580711b0086582d2080790210301291000314001520b501904105010030041081c150001c410780c04048900d062250303040280002410050a640c0115a020800e104002010310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 251801061 1250 251799811 251799817
    0xc2301080c0307020c030a05011d210d0f0f06060e0621101d01092a080c0c070b04050f06032202010302071505090f0303102c070507060b01020111 64
    0x3820041c05480741d441c86030480c600300ea40e0a45942c14400d80b20400203003c41940a41c10b88842c841d556540324109107000e6170340f100c816401d4001144684440c5140034486400303000303841c08031075000c01c0e43c49070103005a081e240301c80800c42c0115501c0c4010011030342c01001c0f020b140081516200e0510100400585e030a00d44841041034040f540740000c0ca601891070101c0001c0c0955200c101944e840c500d441041c2c9007001d00469016924294000422241c1035007000c01e5003140c1d100c00c0300c815464180803500318902404035001d45c1c40510040d100c0c114180071503005806034800040c1c035140380100b001505041010b00500070101001400310300f04000c008803086186514140500340780d1440108c009108001000d005070300d1780072188842c2c4440d90021800740040b041101c81d05031103000415124071060701d803803654020041082180c01300207142002e8110300e00d401d103180d44034000c0800c0000b00048a042e0b00203100015071608101440c416800f401c0020302c001c1103417400809803604c2d544 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 251802311 1250 251801061 251801071
    0x8090c300d0c020f0d020414010f050114030c0c01111c05010b03010b0703110307080d0911030106180e010204031a040c080312011202041803092d091509090c230108 72
    0x9135030718042807054070b403c210030140c507a000c0d00811100c0e00e5115400030303200007800780d15143c10ba2014009601d61040b03140c1061071200d0340f035580c5907840d98403003541d69610000a02d8525500c80003450b1442143c007001d4004100640c020111803070180b0b610904032401608000f04542c0e02f400184903104044041e208001c1d41410b10008040c04660124614011500e0040160f1400540c81c2507009058000711880d5102e07104170401582075104150076030380e0f240903c00c80c4000c007000303226100415802a6141d0070701c000006241070345075200e40780004904108002d00d180c49034107000400040044580041042d40d01440c200030310040b400c3c811031410f1140c600403066440140096545951040c2001e000800b03411010031820300e005030081000c2d00c41c3c0000c5000a807200e140c00b103070895a40d0b40da26621182c0c17000642c100b000b001c0081209807503400d5042c440880c0460310800500ca42500301e80144900001d00c2d103010001d4110a900b02103c2018400f1602c113840d0503600115070a0b005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 251803561 1250 251802311 251802319
    0x50d06050a0b0f0c07090504060c0806031506190e01080d08011a04060e0604120b0402030d020d0816020304030c0909050c04020f070605061309081207020705090708090c300d0c02 78
    0xe16130300f494131850003800b0341014540310703d080c051104111150f40300c6111703240381361242022941d0780410146c4410039100e0b5510072110303100015000780b90480b50f00c140c800040f43c1d14400e8586400c0c03d211070780400d070044103c07a0300004100c81c5294100409500424040c0c3c200381911002a030404160b0007a44150f0050100040e02c4c9045540c506081e07030044c0c554022400b54164030b0f42800942454280c0c0d080e4068003e180001c04050f01c0410340103002c01060f11440901e80b2186080e40e10701d08620001000c50205000100c0002c1010003002c0c000e000d40c04000c0b0320303400181051810010130912261140c4e2040003940b60103040e110907612000d8216100203003566900d4040b640843c81184e200f4802450204040300b008901405008180c240b03c80050241e524818140d991b80c000b80203d652100044d400600d005d441491055409a06002500c07203007055500402c2c10a03d040b03000315501c01c00403401165601e007003000380c2501c2c02c05500030400d021a091000d05180d401c031704d0103401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 251804811 1250 251803561 251803567
    0xa060c030207150c030609060f03081e07050a110d120c0c0b0f1209010507020a020d0309050415051e01080c0703020f0318090a051e04050c0a0303050d06050a0b0f 71
    0x55000e0780c15600ea0300d80003001d00c8001c81c101c480010081c00021401c601184c0b0b085000715012605104d544207603001c1035200e07100141191100070079030300407122170105c0000720418035018070380641c06442d405100f1001031a88030107d103032440d110b034082c940481c010390000b0307010300104000c0c400b01c500740c058600381594140f00c9402d001080301c40c0d84e0000708540d1070024a01d4060810360004200107814104d4031900c40e1079041f103081c00e850055500e440180d0040e4101d1014bc580003014012191207810003e4400355200e0226098a001d0080c420082e81081020403103410103141a03450380b0404900841c40d1014900082c15481000d029140d4044001c81c56a04041c000c0000240802d140710850b40c55080c2d100312100c2e508100185c607030080310980b001c143d62007035500582d409070b031295018000b0041c0305203200c0000c0b0401001a10644901508071803240c031024000006580280d1350aaa920301141c0c07540117958640e8003090280e414190100003130240c01c001d07101e54109041c1003d80d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 251806061 1250 251804811 251804831
    0x215090a21201002031c060506190519020601090b01030902150a020a080408030703030c0512040f0606031a0f01050d0309170c12010f27020d1509060e0f0307050a06 72
    0x4940742c805222590000c0e1004040030b00d0360f4000002d810024598086940362103d4101c1301410b50780c00c1e1182d13a420907403e001d50203506610303061411010b0a145485414003c550041c508070041c0c2c0040d81c13001da0041d4005104040c080e01035402e14641c00e0809000c100d500d0741c0071814258200c80a909030721400301e01c4031071b09482403002c9200d05030028030850321140c8603d0030303c0d103030b038014981140800e1510496030180c90080c4c0c103036107404608400c0680e4030390791911145d401c80f50300c5100b00c5400355651401310021f1135075440314a6404024071080f10900c0c1203c400540100180c204030b104003200c0405100007075100c4880781c2500d442c08081d8550803a20880c1c80c1c600710303400703220742c0c2c2c0f00b90303d50f41c1d40006240561086001070710444c81400b00b00070305400f4215040b0444000d03e100b01000b1120f0001d410b141c0c05800c6183d100f40c2071089a689500c00d00800c03203845100c00c5461640f290780f01c082c043d00411440d00f60303030300350800f6515101e0a0780d1015070703e68080200400640c0ca50019039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 251807311 1250 251806061 251806103
    0xe1501120b1216090c05030c03041a04080304150b0604050103020903010b090403020a3e0a090c05070b100e0f04061509091505040c1208070215090a21 66
    0x9950100054542c408118054103802e40341c000d55030820501c071168000000e1146014020851800700f141c8909107151100d0030340868a62000b08207849110864508a03204207001580702e00c82d501601e1b00d59107038100303860f00f010f05401c1c40501c0a03105040422804e01543d83c402160f044590074200140d94070309000103e40500b0401507284d81c002c1440c001c000a0580104103203440a12500c00d2206144111148019091040c10380004185001040d40581208202c50200d2140020044940c003550b0f000801b0030307145c0039415880060004503646040084624545410001103480c1544203401d040e0386400c140402070003251007000c203d010a09101450b0300041c0703881c1d040242c04034103a44800d407900c0500b0000d10221900a46406241060706461280038043c40e4400c103600a0580f405419401c004140c03413040c1d07140d903030800c00c0d24010390b0b510008507203000d40e00a000361104050350406c14500c000d0360098516404002c46440341c0300300d1040071412981d2000103502e2000c4070306064 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 251808561 1250 251807311 251807321
    0xc100f11010203040303060305060c040807030803040510110405191d04020d0f121e0e01030e010e0316050105010b3a020c0601030501060506070302070b0a0311040303180e150112 78
    0x5503940c0d4400410300c41899415000300d0b054074094011a202c903200c101901545108510428099800680d400c0c40095504401183c0084c00f0f10100c0d10095000248001200c10a40c448881980001010810b43c1010f004a90880b81e00a0320501c550b49045010038103200750454240e961341c40c40e00081c0440d0790300c9801340c21341900600308441d988030700d2070007074641841400713403002103607040441d114088030000307140b03010250b01c1c0d070f80c07200f060391400055029141075050101c0c2552110340301d10720100c04001501d20856501c106000b49046070401c42c1c210354040e00100b0403001c00300305078551a48070b000d4607410080c0150900302a3307510703101341e070511200c0704441120b0140001584810054005513030703816a03006a0081040c0350341d410400c90540700348440100582c00c052003c00144c01404081c12040060b41808181ea2500b184114034650180d00f0440200354940e6110400060b080c0c0180701270405c3c13044110050070080100072034588007050b024104400081c420586920765008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 251809811 1250 251808561 251808587
    0xc0c1205070e070f031404050a0f030909090803100803031014010e151e04081005150303160b06030601030f020402090d08030c0d23163e0c100f 63
    0x320310290034451001440c41103604d02c00e01c0041e080c68410390025041101041c0115400001040c446000e9540c06410384100c241c16410700c603040c40c1c001000c0c102400b80328001c07031094000d10307945e2070f113913084560b8a10035421020445c4e1040c01000100c001c0030001c1c0090303c0350050340c580041d030030400403154020b003000c0390f03500601045030f10142c88030260041c0c122103440c09404001c070090000040c2c20ba002da0300c5000c04a03400603294840c01f83d99540143d401103180040040c0d0f403104440031074a15445201704480305030414414005002101c40042d42183c0200c02902c415403454440d50030800c0e0403a0068400c982c00500403c096460764031072441254861511522850700c600b085040d5084125008081810180e242c03184101d80c084041c1c0ca0800310000c4411a11041000507d20002d00700100a00080181107610001c2e142d280c00c2941c50305540911580040b02002c4400701c80ca000741000c19840350802805980d00e00c04500028889460014500f00000702d003120010b00540e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 251811061 1250 251809811 251809829
    0x50a0311030d020d060305190201050306040b04180b0402100207060801091e09060b0f0a03020a0b0313060509011a060a120c0c08070c150908060a05130b07080609070c0c120507 77
    0x13002e40100541e0740208048034066000d450020310200e40c005098100004001d0000b9404c01c0060f215140c0359010405101c030103040010760350000f8030b814451003d11001a070b9107003000720402c070461511710380e20603038107549202900f6210714041d0041c146140c11301940c0c5210307448050109007808d0b01c2e0f0b06012100700415041c400d00c10b403410910020500b10000601501c00850007a1240c241425640200c80d40940003140300b034600340a600c240e4002a2414400140414140020803024040c03280982d49410000440102c0c0300c2c100300003061000500750240074284151a0482c1c1c0203103c4030130160428001059100c0181e5044a41e040800c00086c0106004030f440303030600c59081d1211007030b248100070b21105030403085029500086076205003503003039109a000640800b0250000c680094210b44d070104100e00680d2020083c400858015000072008010400585801d441c20354003c110350070300c400c044a142c3c49042c40c8480500500c00d00c0c0103282c00e031000300721003080b42e50000e000102d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 251812311 1250 251811061 251811067
    0x309021206190c030b01020a121407060506181e15060d06030b010e10030f0c0308040305010b010311090607060e0c03030f0c010507440106030e010513050a0311030d02 73
    0xc1c940c054481c1c400c1048207a110b140140310b2081c0f5000e84100d008884058000741114005a82c417502260041e80c0c10b0010001655060050000000050300881c0e00c15a0b01103034a14046d81031045a0144504003200010030a0038000003030b803003001e00c81e1032032501c04460003550b98602001c01c40040c10074540f60000c0340000d240c914024298041c5058920520503081e050740d85000c40790a01e00c082d221f41801200c0c031001000003600040c01c0103141ca1080840000e41c6e44e41c0d813561600c9400c5a8070660f09070b5141e6928011075a414403070302c080300384420071281c1005840e5004c20003c0c001e55500600340c0d59615954818040c1c00c002c0284044d00003021203036220032104018005402000b14541c0c42c1d0300300004180d039503015900d807505032200060140380700f4140b0703882d10000d000d04841c8940441c9034030710042030401c840348080d030203041c00351400306082c40c01031050381c2100d000800c040200c4656902241c00200701103000d0000e02c1c2c04d032401d81c01459016210a007140f14501504580c58800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 251813561 1250 251812311 251812321
    0x1c02010906050604150510030e0615091b040b0d060510030e060c04122301090305040f050f150f0c0303091f05070f20120301051f0f0309021206 63
    0x15040148030501c00e00e000d1149031180e5051000365202040070b0103110044c98010f01c9075081c121220070f10500d940c0341c04a002003da9468900b0010b00384d5140511403e404100741071414003150294003c50071220035148070801e10242d000360302450107500200742e030000d400f4001d20081d4021201815004005001c031602c5d142c401340c010000d014491903940603080c00107002140e080c041d10704455211801d210301940c0d6070390b8070340441000101d0801102545a41c8001d50030309100301c1c2d510a100762210341c1e5403424406044907040e01607000034454032405124010544480700402007100d19a0300140d00c0380902c111400590041c400740011a00c00841004820710b000101e0040c039080c90101c00301c0c0800d08507014000e0380c2d821902117011440708038016008a00c030381d405c8181380c50039140000d203981e00c4801541c00d0200d0150064500400407006000601d007030301c0812001d900c41405800751180c0342c0000f6004031580001c100c28155589124000d64031001e074111030200002007a01c5443c070349 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 251814811 1250 251813561 251813563
    0x7120c09420f0b030f100e07030504020103180309230a0b07020d081305010305060904050a0f031110020415030915050a15090c020d11070b09040603050d02030705150601201c02 77
    0x21104d00c02c40c102148086142182c180310203001f951401c054600250340e480d1410b90251401400482c1010758030b0005989105417424194420f0b442035880880c142e1a0108400c8207540e015480c5034881550b50f0140c9440c0c2d1001c0c0440f0440d201c902501c0c1c0c6580391400006c91149000401401c03a10000600d0654500e08105001c10303a2070907281080756484007003d00105200441e0024241d500c02c01c121004204000008402640300c2d24000082000500c0c805082600261040300820303000b003000e2220b800741c4000f070b8000100d2850304102200040e100d80f0350824914000310a016a9000801c01c200c0d000e0300080008140d2507004140389036542005002130201c0990764005009102c6144280c0d071041030720b9207000d82058018200d903402c0004100d680d83c458081c0a6116907202d41c0040002c5061145e040c601c2125005182c40d60600c4c1082e500304600090300d00d000040040400c10b881c1e0b0000150180c1c040c2c0030300211000c0c0c2e0a01d2410b49041000d021005001201212454109034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 251816061 1250 251814811 251814817
    0x527010f0624050a09171f090302060c19110a08120403030f0b13020a1803110108090d08070c0305310e06090606090307120c09420f0b 59
    0x200c40c0c0c1000e0308441410908803140d0180c0094074000410f45c1500b0041c00100300c0c5860880c21025007660380c0301038400c4004050f4548034021a0f1101d844208680504d034040c8103080c1d00032401580d43d468600b15215500c4d01149002411080c80030040f400710040208000051103d640303c2d03600703641d59000707440b0780301742c1a0101c40403800070341000c0d10780c44006060f0080d00380036000604601a41c03c1040c840102075000001d1040c200100e041c441d5480d000020070700300046014002500c01000d410000400c81c0c0ea005040300c01991241e84e0340184150700021550f800240c614006201c82c8862400311106d10403108103040048a94aa0b003410040c40d07607000c556044004a0a43c0b441d0b5100c8500b03170454012106140e1242c00032001a4203400c1100051045070300040a81c0e05041d00c640031004600c0741c2c101c060346d01050100091003986014031894a03546260030140c000c812440c186100304800c0c4d22680089107250010181c0d8040744800704401400d020b00808c0c2619843d0030390341603160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 251817311 1250 251816061 251816099
    0x90f0d0519020a17180d260f04060c020d02030a0303060905100501080105100e06030702060411090f040f02130c2703023d0f020f010527010f06 63
    0x1880030881c80700c440d00004a0040c280d03846041248184841291019540c21414030f81c10002920241925075958164000080501c101442803860401000840d2151914090504031410030401c0f6480401d54005680846815103000c1e80c0301d4925201182c0d000111080003074043c07003034000308410107806805c45802d803002c10b8001c000541d00c112000e81c0c2c0000d6841190f01040410006100030709040d01c000d4040c0035076041c0700c140038441e080405c410383e00441f56840103802100a0004009907041e083c0f07140e15007165013110a04082d4044110030b0700280000349803140750300c603a8085464802c284100187d5070750041103404004000585541c0400d102c4115052154118000340c103c0c541b03d12081d290091300b402002d00100390011050403010500d0070300e04c11500402410b2000c0b0201030703458042e140c0c0d01c00c0903900c50040081d1924240031000c060310307418201000041c1c0b80c00c0d0b21403040014810010703100414506200340c0145650041d0040311814010042072864a0f580140d01213 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 251818561 1250 251817311 251817337
    0x3020d031e0806130b1c0503071b0f05040504050c0909010b01080a020703050306090901020c1b0909070b40080d02070501020c060706020d06030605011e140603090f0d05 74
    0x103844035402100c0c040002c50b64140c0c0042e514100c0001340c2540d600007541d5900107441401b28181c1c00f494680414034048040b10513034000202030042203070103040146280f0055040c1407900342416140110300d10350303005480c040c0d41d40b4000036040c01010040310300342c2c52016020094608182401e5030103011080000741c0070034509808191040124402c07185030a400d65030750342c2543c5828040040141d00a81511031540d0207100c171401c01072050100c80c90b07030500c800310148000046414842c030717204010308819060f0441c2001b00950049241101c01910035034489030000015060f85000004e1001100501241c0040c858050340040d5207034001503580d0103048071a0503031071010032a9224202e028031b6005030032400c10307403102c0c0c00e00002078400148591070150a200314001d5401c1180c44592099030406e80304d04c0100201d84004002404255801c61140005814040d0a540d150140c00c0c407240200740000000e541074500307004001d81c945500040d1400b6a21100c4010042d40040c180c548038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 251819811 1250 251818561 251818607
    0x1611030d020316110102030408030f04050109141e061b071410020a020904060e0d08011a070b041b0f03110405010906150309081911060127050603010603020d03 70
    0x8141e0000060302c0f000308052140411220141c2e50702c81d000070900c0446415803005000204a00c0409e0029252000d032441c41c040d00c8510307040005120ba003003580404440750141002c0901d9480d2100e911500c1488850350715180484440411240d1240f002c5079200b031310000405403036003500400d6440071910000c0744107806000070001c00112070110341a05002d6480050280010705007120030326442400b4640004510050349015800c0c4640e6161420000d42d0100042c030150102000d00302d2900f5800f20301d035003009540d550f036503e080405000604040c59591040381440100c000c441c002d81102250038402a0384c03403a2100d658480911051722442c10500081a280c4042c41601d08451801403000030481c09c600040c5c008001c01442035404080030096010208401c3c6a070300505410781d50f940c0001070310703a002c640c104801a00013a02c1080c054040041d0b22190003540400b900c0c2d8050000350795107990000034018299039100a4200e040c0c0c010620030305420007491000ca0310688001c0d41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 251821061 1250 251819811 251819833
    0xa0c020906121b150d151a09011101020903010908030a0f0b01140304060608060c0a02060a1a12190312050604060e0c0d11040b0a02070b0306100c030302161103 70
    0x448101c54000c0151540440007030503c840f00e8582d2160108000340250703000c0c41d1a5202c07040c0651140300b035110242c0e00c0c2d5280341140030b4001281002044a05905039165140100d5281c0c1449102112410410005402c8050803400e6044416030103004000300f2101200f40380140700354008440c0200c006280c41e01c5030010607058015010f13a0b20301652505230002000000400d0b6400180080c1e850039600d940114410b00200f146600400404054507180c2d49010710086c036120008145985040c206510301f03050a06c0e5109045000c0000c50b0b60000201481204d00e05e0816000061811a56042900c27414142c004103510071180c40c04c58140100d9454009004c02e07101c19105d002d01540300500010500d0400742c2c040c1440c0410f1010106218004a040e22091740103608003505101d000240c54541031740401241c0c004004110000703040d45401c0700040c54005000a5010601030301125000c1018480d038119854103120b0717407040d030704c110b2542003246507100d10404241c0280709040c2605 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 251822311 1250 251821061 251821069
    0x100f02070b09010c0b0c0c0a060b040b3003120709051039020301020c0d0e09010b090d080405060703031a03031303170c101a090106121e020a0c020906 66
    0x50811941a141c03070301200c0c505da444600c040d03401804032141c1038040c000784662007814410802c0060042c20045035640d102e0003004200c3e40c0c004907440c4644917840a00441d12408110902c503125034103d0600d51040d40d103401410b40c403030307800390030a0445482c0400c031409800c58040000e039507040d10182e0700200c9055094507104d182d29003001d084903010400c0c4170504450582d084070384241d145100c0100c65580e001c2402d907041300706820000c0c1c0024004445280c0d02c480c01c5550100e00322505035480d45801c20840c958420703000918024079141c01070005000501c0c00320b4000b054013406955892015041c010010a050f09202e0720410a4800d907607140d140c004140c0c1c80c100000032690415500c2c59132400e5000380740010003050752800b400004c0d0108000d00c28000030034010172010511103c504041700d9170354a1151100e104e416000c005008942c0e04c0001c1884607001100000f5011035903000281651102110307140c1c10900000c0c03021f1010340c0c0b1102e69240c0904c01c0c1c6201c075194603100204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 251823561 1250 251822311 251822317
    0x13081908030a0c090b120411060f030c070303020702270901060b16060b030114040b07090e07080612060a2306060703081e041a15010516080405100f02070b 68
    0x1804000301400820410002a0f110f4412003020381421652580c0d02c1d0b062006541001e40046012030180c001c0206102210321802c01180741211074618100903210a03001a00000c1c00b00402100c0c00319031982010701075411910060380090110f004003041d860300f8401c8403454882c1845119084004c1032166034140141400c0d10a4541c20741d051100043d0028500542d00d1800e444082d15103a6640084d1428440c0c00031407403903880c0a10003454503040521030044050a03001c1000a800306c100402e410308507030550040000e15058046407070b454000b8404070400503406426001300010300c41001240c0e4800c00344c40360000006110316400c0003800708403d0080341c40f1754120404200d02d0001134410007825501012040444d11101048030034015400c01c1113500b120200910714140000d090b2840c2c0b06a40302d02c0701c5000c030180c4460003000031700c02d028503100030f00d140380b03030481341002c128209042d00d003d4007003e05200b4050540c0380b80107126018614444016009180020032580b10800031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 251824811 1250 251823561 251823563
    0x1a060108070c02030a120c030908160e06040f1406010f0c0206040302060c16030c140d020a090f090203030c070e0c030421030b031005070315210f08130819 68
    0x9038031195a5040050380e0311107800700e049a050007084408000241d40004d07800c4402416603a6003403007038840ca000b415881c800c0e040b0034400c0d0b1102000030a0026080389001c1610700ca454820800c1d12103001060140c2202d001441722541440c1114411408030001e040c81070800741d035150f00c11901c0c03120a891440c01c60030060740041c41084141302500f0110000d1210b40c0140d0102c0e48083c082c440341203403000d2140c004451180355131000f000f440c040b048001124400072038410885806072390015001b07840c64811202c1b80c607183d10705074400b0360041e401729944a40150541e90f459107454100ca8a49440780104c8440145800208002d03400000036a0311490b40010fa10401c003003141986076160022840400030036440e00000290350714180301c00b0a03020004940495681441813002d410749000544158003035203616010003080c91003812076030390488200780994050401d0b08001d120005803040c06040e40c200001c40502d0a000322080340100d44003d810340340001c103100d100c0d0300c6604044130 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 251826061 1250 251824811 251824817
    0x1090f0906021606060b120f040503070c0e0103020a1403100b0a051903050d030b1c0203070f080f0706050a020a03120f05010e0f010504021602090601181502010e010903140a09031a041a0601 83
    0x2002441c10b42c50b100e03000f84c01c031303012b00e003100d0070032003640d503803980302d801d190004245005040010070443c105800014041e201303074a002460845848003196030340b940380b1044040340b92071302034101c0691683c0940030050a00504604c0b50244034101c04107100301c0fa480b04440510404000c00c18041c400c0c480c1210300ea200500d1303d1101030303818030016048400d5103016031381070190402c0003590354411840c3c1001400c40b14060300001d844d03c24010300f02001c660154040c13050412044035a15800724200115650600300b8003291002030804000a00a00e600200d19514100002c24200140c1c10f140344176666107021418240c1e00c440600050340150400b484582000c501a03000500c1c00c2c690340d40d4030520625020003d110740b1003041000c100c1d00d0f44000c241080144c1d1148013142d080c0502c01e01c00301c80d0f200034001100c3d84e80d401800000310121036a00c0090124816241502c60101240103542199115040c840c2d00300050764120720540b8101d4100e00c1076070100d214003081505d41803280300161 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 251827311 1250 251826061 251826097
    0x130b07052505090f04021809060c0d020d020c030c0d020d0e090a090501050f0618060d03050f04080f030322020d062007060c080c1201090f0906021606060b 68
    0x90300c1c08010341500d49080221900700d44001c5074940b600083d20784900f050600240003400c050051240d2001c00e01c520405c506a420b0030000711140000e20141c200c41880f0095036200d07142c0720010028005e000c050700e640781c000142200041d80000150602e040e210069a40452403440181d944044040403000032801c0750030381c01c030285440002c041e840103985101080c0c81020b07513112402c5840880c0c0e000c01e00c801c040140290303410200c4029000c2c400d140d4500350681030000c00540004140329004003005000a5440b80f40f4030030406441c000c103110f100b20b8900c5501e5008903601e94004454442500c498000a4075208140c40010310000c0d401034a07232a4031011a807504c40240130140c000078020a01013044811850b400c80080104c1070058000003041c00f1407880017403403000040d00119107804240003040081d9403240701c90381101c1903044001950181503a801c4090000342802a165610120700e0442e1138900d4107011110754422070f0100f0400742c0307460502e585400703241038951100180f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 251828561 1250 251827311 251827333
    0xc05040e060103090f02030a0f111c02040b0a170d120204060c0b0702120d06140316060305040317010e1f060c1b0b040602031c0207171e0a05130b0705 66
    0x135441201402d00490114485c0852500428a44202c40c13100701c40001c2c6494107002072001116804039944c44c122403001d060910340301008025050b00c0006403140d641c6502034405aa240550b1800030031002d4007648480c15022099178440441074001c5001c5810030000e284038000c10f100712001c2d6009601c0c1d000da205026128030302c041d4001443d003c02d6201b103d20300002e000e0258050101c0c010040c0c80460f0550610800d03038003200b0f44c11207240c0280d000d42d0411220b0500d102e0342c803064590901d0300044a030340b241021101011200c2982c0d4030b1481400c004540d480302c00020710b2103420502e01003450a04501c0c1e1801c84800d0301d03c101e000107240b1180d0207000900305d0b081c2581e1a64503c140e01c80d09034a031403200116502541c031900146c2d0000510010703141d00307559130104400610008504000040c0ca580e00f80c0380c101e0400004808001a2039041344580030a210300f0600390302c3d030480e15411410809005540290329a9001f450307403403030014402860a0461700c20950000142c8000c10071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 251829811 1250 251828561 251828567
    0x20a0608041502220515071401020403080a030605040c11071406130906030c14031002030c121501020f03180f1807080f010b030f0403110102090a0b04090c05040e0601 73
    0x41c0003100c689501d004207000d000c04038006040141c0e034104440380181d071541140c1020307402d103500550084580d40010461089181e00b990529501b1594880c40c07648011126402481181c0008250701c0d40400c1881c0043d91540c0301c5021f0700c42c00e4034108180ca805400a0701c0c003d42c0f0480b44400b42e480080240300b0403110036103004011030050502800c2c8080464400c007007191641012445594483d0300b0400d03c04844007090040003489192051005440301080d15001c0701152541456000030102c0d001207034040485254040c407881e96052428a004840007141c1d0320300b51036004bc82454217510341c4400101c12281c5401c1c4001c40b18400b1080d1000340a04609440405030b8440039142001e51800c1400540f03501c49c00340b6a84601d5989000c80d8040a8140184c0282c2130703200083c0308011030385080342400d41e003194040c1000c8a03004540c0349503501911840d10340c26040070011400160041c8610094800e0301c0141605000340301113030b0021580da000b43e1003103008204140d0042081303540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 251831061 1250 251829811 251829827
    0xa0c110d0e031e0f0607050c070504050403121406100f1b05030c0a08030f07030603080a030b0a0f0b07110303030f1302041506050304060e010204050307090f0902120d030e0a020a06 79
    0x780c090107a5030180c9240c03541904800102c50f40c03a140f908900220095030405000e0594080c2032030802504003840a181c40350b40c0c41d1180a25070203283c0d03036804581410f000e800d44d1502003410110900c45070f600c400d420b001e62401910242d0081c0761150200c03000c5802101035155001503555042c3e03e550307152a41c1803010641400a07a068041000821009a414011039000d140142c4010342d03a0f080811448520420081104080500e0000d003400001d04500032105024024075000c078514101e000001c02c0740c1c00603401030680c42100b04001400480c800e02038010b82d130003504a003d5a04034501815228801110b1541501da0b0240c0000c404d080140400d0710740c607001500005410010500e1101440c00c40e801007008901c001c03007080100304044c01810b400103100c900942c00c0501c0d00300400d0740c42c85035004094150f40c0f111412054960164000c030031503a0028032410000b41e1805099807100307000384c00b5100090900404840410000840801065020703203020354003407030b0640440b0111 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 251832311 1250 251831061 251831087
    0x140906040305010e0f0c0102030319150906090c032a1202070204020403060b030613051216060612031205010308040311060d05041b1413111309050a0c110d 68
    0x1490a10000c004a842446006070610002005050010300300000c0340ca01107020840504552007041041282101880e0107841150000e202080700d80c480700c0b40818486107030300b081407464640500040c1c00000380c3c01a1410744465203080150702d44080038a003007855680358030b600030a0885183e81d8035521031414040c424240000060400b012a40082e0603030388141d00940341c007070302c0b001c011200d8501400702907080f2001d90742e5651207060581e02e02d9151000326110f8400c00d4000704030901c098142031564050340380e011a0400c82c140d11082d07243c3d104080564107900107450307003442040c039020501c5182e050369000342001307050501d180d885600103010020310582200c0244600501030382c60b80034840c0124803c0810125000d0071190300300300b8030065803102c2c0030500d4840c0c6112907900c400b403249280d1004810081185d01c0300c4141036121748a0803405045c0600c43c00c1c40020104602d91000380202d507060410300003014241e90842c4c1392401b00c500500b05401c540c08040009010b023045201c08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 251833561 1250 251832311 251832319
    0x30c0906011b050114010501030203130201110a0501050109020409060f0f0e0a0603051c030c032c01020408030316021e0334030203090406080706090603020c1e0a0b0105101409 77
    0x2400c03088a1844000300b204401c403010380d1200c1da18403141c0f4401110a015007820320f011811441d1101031031092000450300a0b05000758109000401b00c006d224000d040c6070000003c1c49030b5655090660020351042c82198034540c0b0340100424641d0290040c1801c0b24908010388000c6803c00c0000201824081c0c4015116070362180004001003040c000d0030680001c1710203408141606590250940e240b11000d43c1c20146015207494000750594082d061441745a8450144000c41d902030703a0080c4141c1e009804244800300c01c0041285c2c0e0100c001075441d582c2e03403c3e10808641c1c1491302240c140c486100005070380088c004e1000d116900414000100d40050f0403108001540090113a070300041102034006030400184103405080901890b4000d054800040c02000c4c64620000c05100300e0b40038031030805800180c80303807400ca0100000010030004460780c4144400e000d40e030b00d9031140c41c6981120741c038444400000341c0e8600a1507480c200409519100821001c04840300441d6204480d0b150340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 251834811 1250 251833561 251833577
    0x807050a0e071b0212010f0f0234061b1e05030121020402040602010b120609060609131209061205011a070303090812040b0f16110a02100527030c090601 67
    0x1d60345d00c001c1040601c0b000000043c03801c00e280c1200e01511160f00c0401078040c010403102c200c0e00d445d4000c034586102d0300c151402900c00c035148548000c0c00c0440c0090021802d10178041015413101040d000112400d480394411222201a010803043c0c42225000c0400c0c0c09200421001400c1c942d0900708074502203400041c0400c03a40007404a8110303800c210b0050717546e01c62010181c1041d10760800414011001441c40d86402c152240d5100001011180203050703c001003505041141c0118480c55070004451440942d010002401c01e10036100c2c040028011841e030505c1e840551040030305036900c1c4d02240480f112058401002540201d00407010160f44000741030101d800300002d4691070030340f019020401e082c03034280304091030005000c20f201d10301c00406000701920308030303400300c0341010300d0400e58107015020031050308100e00041c000e908810320001500e50954842d000f0110417103210075109014800880d0342d1524405580d031701e83c05038000c01281c081860000c44456100c1c20514020031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 251836061 1250 251834811 251834813
    0x20d2615040906050a29100c06060608190504030c030f02030c07090b0102120a02030706110f030a0f0501080a050703061104121209060305040b1b040801020705070807050a0e071b 78
    0xc40b440640155012652035050050302c440c2405016000c5500303000c000781100560210515030984901024440c8844c044035855071401402c0464013641c101408200b00c51b59403402070704124040703d030700401a01d500013030240800d4500c9000d004a400d41d907241149000c5035010b440c1922242c0300c88003548030a00460914450070050038000e0104504003113503003a10700002900d40401030245668210040c8015841d590f400420f4919603900301d107010444002d5918003021501c0b0700f41c00c010210f035000040100c003000036081032200301d40c2c140c820001680e84112041e00c0e10f0413140014419040180c0800c04942e25400c0300301d010100c581c82d103203804e5540b01750b00f809840b2550119005c0401411203081c52f40c01c100c4000080c089420280a9440e055584225402009008580a14411034550304e521701110564001d0450349000710366070425410a181c5d6a60548640c041621602002003054101155601c00700c3d000101304140c20b8135080c4040d030316141a1001030b0404c06842c1d01c104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 251837311 1250 251836061 251836069
    0xb0405160f11012a0305190c031404060c080a06180906060510020d08010b0928050303130302040f020c0607051b06160e01080910091502040b0a020d2615 67
    0x380030781d0305001644d000850800e002c5501e9192a0710b02d0401d1501d0b100421400c0920b90b402d400d00030034206e50025003483c2152003a00104000701d60348c0606030b0780310100002c03c4040c0e4025051391907207440f850751582c1c501191005942c8035004019035072400740e007076005c0c6d1141c42c2c1048040501c9880f0101e170968643c40403d080080100b846001030f80064031502c84a9005050b0b0340c05012070070703032440c544a151008100b503030303000c410142d406c03051083c21402c0e0402c085c40c05101624006040d20740c1c610540160403001015804181e105515042c004482803203248200e4040188080151200e540c070040c0941c2c2603040300544040d100c401000c8900b9001081c00702d00e2084400d4019125105000c110007440702c1c520b84d0b2550706100341c490030b20010950000b100411040801d00224901000380350148a1b40c112100c2c00c00d10b070340041400700d160072041c409000401d102e542103541c005440803086910710304400d414952440d1400d242c42d101c00c02c451a0540c02035005900e11301140491004c030b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 251838561 1250 251837311 251837321
    0xc020603070206060907091508060607120504080115050a26030408060f0f0403090b0d021e071b030c15051219061406030a0507090b0415030b0405160f1101 68
    0x1041c01a0005010451580360a440f01070704441c452501c20785007403d1800d44000749071014030300d20501000d030300007c0c500d640d544200d49285901c400c0d180b002403011000900309030004d0090802c13650030620340070780500c00118400119107004100c2c4038000d2410324145403142c03105101c03401403025843d00b800d1008081000304028611240140f00520304090b91f0307084e21710080c24019040b0410400d0001107a80448654156584600721507a42c82c51044801c0092198400884803503134142c040402000000001d44031090240c1008004061840c55220940116000040044604d60703001c0c00700c01c8211221000940380d9017010340c40c0c6440c189040c0304081e403c40780e4503025009500e4445402c0341c2402110024000c83d0350b41c220010b02a00000d0083c00300500500003da51980011042446508917078020f15210788026a0345854800c450392150780204a0404a403c0000d0242d060805d80f107100c1c03084c42a01221810f8515103482190488020200f00081060440c20444068020710030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 251839811 1250 251838561 251838571
    0x110405030303071d06161103030c010614040e1603080702032a03010b0303030c0d02091f0504030b10050a0306050a0f050901060315020705210c01140603100606050a030c0c020603 78
    0x804000407250360480c0c032041c46184110340140745c1488503036440d6282c0d0f900c001c0c11550000000f2982c4c607960340402c1c9940103c4c0e080071069801c0c10740005014000c5100c1c1d8020303071001d441c18880b000505510940d110100d0403c40c0056280f03620405c003155040b1301509020b44002c081d585900840c114111403610444407016042d901501c80515a2409109400724198203401850851070702ea100103543d8007e4041030744030b484c2c00080c030b60310958030002084c440384141d1100303c2c1145001e01c4000e00c1600030703010803120071348040c010900303925003030883d1011503e004181342d40c0c0381d01755035860307014200203000c2c8492183c46000c000210342c4d003401418420300c4907000001c0c0c00f034518248503500101003415040164410400c0070007003400400e41c203010100da2005456041001c281102462240b030350300c02095442c007118980300d001c9405103640202d0044040b942c10000f415418000c6078800c0c451500450ba04201201c0c0b2180250440340c1420314a082c8045201c006030080380d0340f54401c5032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 251841061 1250 251839811 251839817
    0x307090803040e0105041505060d0e0708030c1509060c0a03110d050a150e060d140a0b040f0209010e0603210412050a02091b03010e0c22060206070203071511040503030307 75
    0xf0040c413040c06e05100d290950112032409000c20f80c5094040741581c4500c0010610041e111400e103941c5c24410040f25005101030000c42e581c03015044190358440c20b4100c00600d42d100c803000400c0c540d5000007500c50044000d0346060349030a61102058005011410041e0025441802000325054851040c54462142200c02051100e1a00302e003419001890308101101850b20b000e000c1103403101496581c1c020b07841241c4142c0c89003a80c041a240001440008006011304130400040125030f4201d641d44c50710a550011003640c0711801e44941220849900c1c1d0194404817034070950155010b00902c2c0134014130341541c60152540e001ca01c0001b034000080da40b9910140128045040200c0b060754000e0328207540e24203400184c100d8544a100610404403805c00d02004211100da40600b110300c0411a190749140392a054400a0082c900c5c40c4142d101500406000502c264004821a40d00982c000b081c400d035071400c4d003c1e6400401d410340e5504030141081c000495951002c200071402a03029407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 251842311 1250 251841061 251841089
    0x3181606020d110307020d0609080301061d0609012c10030e060901091e0c1d060f03010b060909040f0206070c0906060207030804062607120f0203060312030709080304 73
    0x28000703890010812182010828504550400440044250ba080580c1147c07184c00007100740c207005000e0b003d14803002d04440000130000409540003500c41590040e02d1040303400110200041000b1130007403e40303140c0819001c00c68000074859111645804400042a00822842010100300480d00e041003a0021070760f13446030038400701001c0001982c000543d000a10180c60107030b42e0620128680c24441c4007500c520000356003003114810120018040d0114101c4038075030301201c0d5240f80d10f4292803081c042c000c620b1084800d802c045c0114070160070042e08580c80c000c810420f015104400800959050014a180c070b80140e4400004040b254040c44000380d1580c20100d6030790440300198441425507200d11000c20010784420f055408035502d0303040c0f030040b4055500300d10030100d036105480344901185008000461b5005a00c1160b080d000400401c4140d0700d80d8086000ca04c0306451480e81541b11807071202002500400440d840741c052329204142c035030381d1000540b464010b80c100840b130307060319 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 251843561 1250 251842311 251842319
    0x17130c09021215010c0305131206020909150f0609010e0d0605040201090807050a03110d0609050319090e13020303131203080903031017120301030f110d03020d05031816 74
    0x14124a0380001e50f4004a4150503014000030740fa21095100c001c1c00c2c0b1001107140714038581200c651318004c0c03210490030603030040076282c504001d40c0100c1c001c621036980030020031042c0c004103110f849600b10250200801c05140000c07c803546d0000c1c504d05041286000c10240746840d180c1d6000f0889202c1d00700407615041510001d4181d1483e81c200120a43c4084c40805c80b5075501c4450204a035000b8200304200c1260401045620703480c105c015001500348000325040040c00001813001041e4250650362007400340008803074800d294800c520102d145000452081c541c0c01c0c0c4680701451009044914102c00059501201001603000030700908400d5070300003d240d0400b0b199684103c01e8006149149441a00034503421030f6800f800d0038004000043e03068551041103100c100320301c0d01c00310644a42e034900d007110003440703040c1044030501050700594000307082140c401d00c0401d5154018000300e034000c00049407140c00013881400c061000e01568048144240300000d066403121b40d104000f1414 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 251844811 1250 251843561 251843587
    0xe010305010c0206190527060103140d27030b0901150905240a081b03010b0d0203070b070204020d09050c04110a09121415010f0603050717130c0902 65
    0x1200301c0c2c08003513411502c104421400b410900e0111259824000541a1104a581c00c2c3d0340d8032a00c5a001c6150a8070540c200980000a903581240e10500501000201d404441615909003ea0100104580350140f14644644e1200709036214007141142072150f48c1d944a40004010584641c0d006035940c4601c50211319480c0c0c02e94015003140e400500903030410a000c0c124490904094400c1c044010501c0d03401aa01d42d101c80c001040010b0868440a18508a101c03402c51003d0f8814072940c40c0921983e4581841e48050080c0f54008014080403072801c041140710354000841207030f00a60801403824071190901c9011041401000185030748880310303040c17104440d0300803001c0c1c448050900020008035800710501c0107a4410002200000059140c4482a6854100d0021040c010007001c3d8003508900d924450403507207040c0103402141d03a00d92040e0700311041610040e001600400303001c101414000c100d0364006140d80c40d51119044a80c88000c901c6620760000000c05800050408018107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 251846061 1250 251844811 251844821
    0xe0a18030507140a020f0907020f031b06011403120a03150b0301030b060409050d0c050a06060e0f100b090f01170403180b0903032a0109030903030f020c1011010b06040e01030501 78
    0x42c1c19030041c07401004d1a00081c045c1b4603d00030040c403456005e000911468030034002c8002c104540d20450b5212220003158520039940200c0b8182d451080c0070002450840145207401e0220740039000d0442240e0f04100031400da030107020071500b41500c40947d00c0d81034884400007001040c0b4406207548950447c50500728083d809008035100d10b0800c10008082000840d0000d403400031800c1150320216a482e1403070070a20138840181060f8504000000d0300500280c4061003081065503102842c0ea03500760200c542801d5016042c0806030a0240c1e1410342404401c1e030a03070080504207880c4823203ca514007410a141158101c1c00210000c07015800c41c210809811f024182c544c4d40682061201004269a40078080803801c40c2c1100050805c02c1c1c4a801012000f1417500d030009000038010781c00c01030200001448105c0001d9003200480301003a101017960400b80c2001060048040c488030421505445088446a03082d561586404080e965400c000c100500c40746603040095855400c0c013a007124 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 251847311 1250 251846061 251846093
    0x507060e09091005070306030204060905060a0b0310060305061305090705010206010609030b19140a020903100603120e0a080102180f0301060e0f13020d05030705060601030b0a0e0a18030507 83
    0x2400042c400c1d01c507008910411040b5031802d0005241da2042000c4001d00020303403000e500700d45041800300c0c04500c0f50300714620400d810b42d507035a0000e94401e800316040c8006c40d100c10741500c03000e0f0f06102203817083e04816000380c070041030040d505140451140803140203a40c035117003541c00b401c810041d42d6014041c280c01811141042c0d44403d02e191200e500000c3d0003071010040c51460400350035214540d52100030380541002052105242040200c0d0003940041c031128420b11900144c4070400f103c9000b902c0969602203607a070710407031050005407148207004403102d0340808070381004644e10f202440908810581c040d41c828115502c903043c808100304094480b0b00a90600d80d051101120002e0110b40140c07164030360303030030f15921408500341d4030717810900007540280f006840c1c405105001000d084104d01440c15100c45132110801501110080010203420000a030404c00004004048081e48241455804070380000845035041c00083c028008a0106101054441c01c3c0200c45546a03600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 251848561 1250 251847311 251847319
    0xf071211031e0115080907080f07090b090c0f070203120c0c011e14070510020409060e1806060f030c04050c030403021209030a0f1103011d0c040b0607081b07030507060e 74
    0x1941070000a482540304058180c082c07012031740c0410420f080c1041800014000c0d00e0a465039242d030007104984804152090110a40c20034445003424508280c1007406620011a860300d059013500300810560810001a03a050007100c0720039440c0d090310340040030086408009000e005002a002408038184001086600c0708400240c07848032f90002d20780e0107601b25000c1d00036145c0c04a4030300640740c4200564100c4071540040b070300040103107080d00803405840c900030007040c07159510140e1484583c0e41a4a01d012548202f01089142c01c050030503143c546401750946118102e140c000c176080c1d0320240d590400c102d8001041005060713050200c101c0740310303100311018980494640020ba5403400220040c00000074100d501b010400a00d2a81110080180084c08109013414000c20246051045507a40e4021300b034003482c1c14034040c80354481c0030200602860500700350762500051a0001d00c0d8034191000640001d46400d0340c100308620003144544000c01e0410305040c0700130005d6444070781c02405 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 251849811 1250 251848561 251848621
    0x41a03060a05010305060303070602040b0a120911040f1119110f1b01030608010f0501080d030e0312060612010e0928151d15010b030f0f07121103 64
    0x195964041c501084940920f804500d40d01c030000060306503c62444024004c9100040c005400802c41001d000c41106039140c2003602c001c05100760003601d55841c001084505604000440c4d03180c0741c0e0100b9208202c40c0400030350040b91b22200d401950002d014072040348081e0300c02c040f5841e0b0041c1020b050840d00c60282886010031229035586180c00000d28041040d20000c100459209600140003012a103009000101a21000c400144020b0081c0b03c0b00e03004180e911800d0500900611039000300440c011854007804902510304000c0181c040f903806801000604682c0b020a000d6501074004600034088038100300781c0701413410002c00281c0044042e44551149030740021401044442e4210001090031000c010102009161013000400303030100e17005080f003102d80001050380310000f4400e0500c0050340c9441100300303540000c070784c6c80074160140e0000500b1603030a40d0907207810441c0b0b400c20014050300004444103998001c81d101004220101c10861140c180000c3e0001c030f00784141d230400d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 251851061 1250 251849811 251849821
    0x13171b0319050c070e04020102030702090103060b01090501140f160b0412030b09040f03030213050a080d020f0c030d0507140a030e031c0f201c0f030e0706030905030909010b041a03 79
    0x1488488074885e882c01040724200103410b59000307000725600c0c603500400c014515a140c0c907058004042e07908200f40051b0f1902804215540180c00c8802d41142c084109410030444415003c030035400307500c001001d48180f40308000090744905a1500591040c43c1d210356218228500400300c0e50141c4045104448010a1002003a03180502d104103e8051801580e0b41d6440c2250050f071094540c060380c2c01c01004080060380c45000b04004101545542c00d41e04912141c451050f992886018884e515410681002038614050002001014491526a1400c50b80c110046040c40e00144055001c144000e40e9014140b0b0144001b201210b030010720401d00308481903004051101e815070300f100b8003584d82905101514048464040c03d5400c90441d40180c03151034005d078500c1c00125484020440800c03059203030500038011400c0450700c40c40148101860800c1c00c0340900044041030340c1e107020401c0500078030744841442c02e0184c10078102159075507191801d80501c1030750300c6494031105001481801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 251852311 1250 251851061 251851063
    0x20d0e06030a05070512180c0102010e121b0304060203130603021903110409061409011a1e09031c0207081f09020301021c050411010813171b0319050c 66
    0x6900b00700c01c0b090005590b540c0390003c0d00c0360b02c03426141100521413941045102094243c039030411040386420743d0440c000c8103005a0a881591710003544235001942c80401c0c800c56400645850b9040444000c014250200924119030080d00402c00603000000d035060b05818001c002d0b0000c000600c2c00310300c2c00200304242079040d09161030b0f00301003649841051044001d6501a1000b170900c55100300503803541e80002030200c01200003041d025020300400050810854800900200282400396107498500090303201c0080310302c00c83e0211440305014201880d00d0402c07040901d42c1d030300250400d503407280d0340b8040e107092100c4d4489000c41d4400e091010454184031101c182d080092100031500098520000340a4007943e4070202102200a00c003a80d9030070b0f00d40010f401103005a42c27480040800d9801111118011a203850f07001649880040c0021071040c2e09000e008070040c0e105040004514030404010700d02002d0448546c400716412030003040a074a140006069402c2040c40d1448800d455 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 251853561 1250 251852311 251852317
    0x20a050a030515071809090b060603010602030a050d061a070204062412020d0c1d010305160c06060803030a020c07050a140607060902211b0604051009030b07020c01020d0e06 76
    0x14950103e20000f18800c0c90107100c807800300409061180d04250340b2901603900400890400f903840000d20320100701c0b14280b03031045a0590304698095407908403440d80c10b03220760f0310013003988804581da420001100c50901c035145c40c1c4140b98a0f441a81e5a20307a00400081d220715420101d00d030700a01d4807003c01e100012031b5010007181c803800c011512202200000c0001e008401c0c0e10041c141c2480c05050b02154805208202403210090050b40c24a002e4011000c45000b00d507220308071014850100440d9014450006500e4403500d404512141c07200070703840c1950415280301d5821500401c0c0005803100520481c0c010f800d040e01e50310300c100d24180c10031604800d10501c480c0550310020303180040c030006411010601e50041c01d0150490302030441c0302040e03040e1a142c608940100798650044000700b0443d031f16440b100800d600d0505003000c0801480910150070a424414803600000000d56034025252051807150050060089448000383c2040d0036040124104251a100030100782d58036015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 251854811 1250 251853561 251853583
    0x2209150e1302030723030d08010b0304060e0a2a09180b1b030c09040b03061e060105091c0b09030a09150c05031b0705040605090a020306031216020a050a0305 69
    0x25906010264000f007418a07080303030440b001000802c1545201d031710030b03490a1045d480d020b40c226402a020140101c4260728207010300c00c0c1c410030030008140454400d07086180d06160460640360380c030b2010350390303002e10070620b0300b40381d04111450170148501c070511074841d40181340e6450180b1080021104612a00300784040003080644032002181c1d5100c41030412200b891018010285c1c0ca00f0701200c0301e0322942200b08205d104608080a90754942004162180201644000d07180c1c5030040b11001da1001d44000d00090401c2810300003000c50b540d498a20a0210f00c0e0b4042c0102060941c1c00c0180039144000c3c00c03100294800c002003600c4950108104d421500c112411113a6506906001c0300e0b40d00b0100b1000d01148030205110748d410340750401c0684003042e0301085a0086c0d94030414001510790360301c5250f40c0310900b40c000901f030071030a07001154010001420784902d170440e480300400a03040b251a00c900f4071f407003200312011810001c81c0ada001c0c0401b103a03400e00c2d0700e2842d0340702c2d0707921590700e11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 251856061 1250 251854811 251854831
    0x9060105191a0a11070314100225060b06070303050a0c0c0510021602060304120206090d021b180108070906050607020a030609031808010e0610030c03030c082209150e 73
    0x3e108029248544180c1e4018011102030b208032541e41d041c424100c1041006401c80d9001c0c400c82030000a8a505c00c44081c40708503009002a5815941040d00840d030310201039804c07585808c91225075540e41710040540300d21a440c0024039081820082c000ca51042d42d42c281401031003880d003408200000723641c003405401d4900141c0d40c2c0303021501c001114a103800f0000d400c0350000c410b2004100300f4809000d0300d01c055508440c600d548080c0556503624502c090100540c0142c0103244101601500e600f802c0d50001d004020140f030083c801407140b2500340e200c01303500e0304002000d20442042d8059080100b00c00c46440b0b00780441c44c0c002880c010780074403004008566905145c0c08050050480404601c0e00003886104a0354400c0458040d2004042021703590280b41c00280f01c885082d0320903001d40707421a50442540d41150307020381e10103034180b8041d2440e543c141304a81d240c1d00d0404110301403014218060604074504001c500c2074550103051407010f5141e80380140f000c1c1205d1010160304c507541c43c1e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 251857311 1250 251856061 251856067
    0xc050702061303080a0309050606030601030804060f0e10030e150105010503060f0f09090105070e0105161e060603081818060616020d110a0b03040510090305040b0309060105191a 78
    0x40140a0b808180d10040c04c00c040483d88000703290300355202c55040b602a000340c2d21540e032640100340d240c2000340001440c1440a20051090728820544000070365070608009107410041000201d170300e0a090079000019032107240c121403001c824030001401000100020403903505100c00a0414080104480d00420b055022810746035118036000898182c042c05500990a0004d4030901a100850304000402c050f00011143e5520900c00c036114408003990480740e40c940341e9100c150144807164441d0001d0141242803000c2003043c07140c1002103204d107101c9070b524021112401c034030444081c6c02601c202c43c0c100c1c0701203c10501d4090583d20000455100365100040d41e40710f170824071040c1020f03402c01d0145091000b000300c0401400144541102c220a000b036454042e4141e03440304440040079901301000d01c40c8440c01c00c0d0007500c0742c24401d041ca1810b0548801c0362090036002111002c1c6142c2c4100300410039030902420418054803080b02581080f41450b02c001c1c0c462441d507613107110b80c070000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 251858561 1250 251857311 251857327
    0x1110a09151e0e0307080f0606060d0605030316050c06090d06050403020313140f03010207030915020c1f031a0a0506091201230f01030b041401110c100e010c05070206 73
    0x15074032142e01c003148184440c10690000c4008000410600f44140a449041c2c000b003a090380000d18a0f0150b080c5200405169507003e09018058001c03c2041c0700d03003901c41102040c9580c090000d0400c81844c3d04108040486a0070414a8024400c0d1090300400040110fa80c06441e05e180c0e2200303240d080800459944c0740c034901240303140302d11140200c10000084012506c0030506065860340c41d021500302c40b01d5110038003010300301d206130035004001c101151020032558020650780c2d880194140180d641c1c2c02d140c400031a104100101c0d0044850501032103d90300160076128012000220108054010301807801017003020540c0d000d001e110b4070001c07904494507601e401d20403c55441c0350001707100300a034480000b80200b00d4210b00c0d42c010740044c800035114900801c5140c0c105e80c1c0040d0304000740e032036648034502191006e00c04010b0554a03a542c4030504815600206180c00d080001408480000380d840800c031003001c00541030603414200440c0615031311506989251360115500350362420b034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 251859811 1250 251858561 251858567
    0x624100c0314210c030f281b110a05100213050a080105093307030b030a030f020d02031c02090319050106090f09020901091805060906040501110a0915 66
    0x2000341e05046078400041c11072000f404103002e0026519442d2070341071281d00c039045402021300003240d003600850201400507116850541e90b001e00750551445408200d014200300d4826144001c044a190580900c1403006965103c007859208140000107840703020307002d076101ea40740c841840c0b80301c3c05a038000c1030500a840c0056408030050100400c8084000d42d00e24606019003004c40d0403050900404a4505802031518000000b480c0c140c01035902d40d0038102004003116602030f0010041560710350030440152003c11007581030302d0103500c03100024416210024034080e020469282150401c0c042c1e00401e00d1841d100d0031186481000c056120490080800d19290301c0c81c40318590403c0c031030000c600344401980b1030742c25122040403d1001074140344560b001d55800d894000e410079280401001f240030140d014001441c0707001400c0f0030341c940f9921031038a008010342d10700080303400120500c020000300744202e9582c50348200a15080c00000030002d80950114403d804c2200080b8006e985803500c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 251861061 1250 251859811 251859827
    0x2040506011704060c08090703120302030a0204051801090e030a0804020409210e1003020c0309010804021f02010501230904140703230c09150609040b030d020624100c03 74
    0x2c4000440001031509041540140c4000700d082008905c04001081d480f850114100060300e8004848400800d0010002c41c02036200401031070f0000c4c4d09110204155030794036280d16000d0030000c03030071269505207000c500c21248a25110f0303285520800c0405038542e04041440d51061301100c000071030f40c0c0d480c2090302a155041d006207600001032541c40340503640000c00c0380507a0000340c4441232283d00003c0c1c00d03005c0340710310150009541e005004461080d80300303078a515445880542108541f90710341b90244501d0182948040141c1d442750010300c03661041000c40702c840c1c2181101d0768a4809100c021030f0a000018002400721402e035400c50000001c1040742c1c400542c0c1c000b170410050141e2040e640c07124410051641418040c1181100e807501e0300c1c1001e140117840460005458982a00800c00d59510400741c07160000c0c1c403001c0361080d5940c18040311181003400d801400741490301003c050424004401e40c1f01c88107100ca00109031644407444a42607034440d41c107000e070a07401d081c1015280d190b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 251862311 1250 251861061 251861087
    0x4091104150e0c120f09010e030a0507030806060708070305030c16141e1f091505100e0405030702010809250603060603050c1e0d1a2b0204050601 64
    0x41c1060765181c500e190984220044580e55007484503141c803001d015012034418110100c001c84d4100c004140001c480c100c1d1990032071642c000000309140d21001040c11130304142d5440780031400201e0301d5011f00d60068050f0754480d07811140e00780303001241e99805996003c1c004020342003040120025105081c0c040031100d806080200c094600020b134030f800b1000b0008985149040e0040c58100c10003440d40342003585009000c48013510000c0e07000510b2450b0341c0a21000c000000740c0320480c245c0458000c03110030449560604001c0b400e450043c558110000c450b07400040c261000c00100300100b40040b0982d5002c990920b080d405a440d9800b05905d0f25500005070184828040b145c12003a007216138800044641c07644084c00003a5442d641941100e03400c81d018040c02c1c00c10000600443c854042c84075030340c882d0341001828030002010001c1228802c0e83c14180394181030340d40f007a907031401ca6502c0c0044845410488203003091103494400d51103c003a8000d00036a116804075040c0d82c061001e0410003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 251863561 1250 251862311 251862319
    0x207270209220603060b0907020a020f03030d0e010b090c07030507081602041802011b030e0f060708030114040b04091212020c19060501080a1a070905040911090106030209010e040911 80
    0x9032101e00034840c01000f80d8402110b40c036103805000d03646030400c0061688500366a0f006485e82c1e5801f1307001c0c4040d4244985c02140c1c54041008007070000003241c4158449400d40e1000000c100460b1000c0c00866440581000c44c501018400900044d5008088400392540400303a15211104001d4070005e0300300443e8021351050a20340c03140c00d206603008a41e428a4000d80e00c440140155880c0d2800220070010042c00185107004000740d5418094080c1001c0c0d500a0491403421000303840c0c901c0c094000b038100309200410a4103030802440e15000b4a298275404403030401075411741e0340d1a050806a403c1007074091121502070820750881c19410740b0020500001583ca0b200c06a10020700403442d903100c1213860b02d1030100041543c40d000220340c00c00503031040310101c03107030703021072400201c04d000032700d203208000107050081030380d44542c055460b10a03c181800040100340c1d00400c204124160016000c052040c061081641e03440000030318900e9082d1400600048503003040d0014507007000000c0c1d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 251864811 1250 251863561 251863609
    0xa030609022206050301080703020f0f09090d02160b12040f12020309010305010f0f03080c0708120318010e032205100519020c030c0f011e0306060207270209 69
    0x82e03a8501c404518020348114076189181c0d00da04003034920b400300780110100c0ba80401010f0006080c83d10344440010710080103407240070034900c00505002d90840e800045500580c081c207111640401440c0c58402c2c04d006d8622001d400c2001a50441c007401d07100840032031840001c1024094290b41c107200b0340f0380100200c80e0142d000c0c68013a5603a44a000042d0019281c00000948200740c485060261541050352141440c990381303806203c0c1c0c1000b0506062801b603c000000c052034100030010700c40b485002280d03240d03d4904142c0c0b5110a1000710240c090741441000460110044101d412000e104032079299094015621a000c0c03103015002540c2000701c0f81138500c0c9554025002d4000d500741c1500300002182c1d1030074200c2e151407407801d807142c0561051152032a50703d0203941c8444441410324103024141c140c2d80403040180c01305038011010a03a1402c09005407941417000c84091f1140340c3d90b00756401c8412100c00312100c00002c0700c03688a60701244610312542c400b0306240c2c0f45241c802c021b000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 251866061 1250 251864811 251864827
    0x15161701090203191401060302071403031303080604090203060f0901060801150906170604111804060c0905030d0c12030b0a090f05070e0f0f03010e030d06050f090402060f0a03060902 80
    0x20351003a00d650485640c045048a00b1030340724001c20015102030245c00300140d2070a82c0640281d080000300b210a11904c1d15419039021341080034500c68414900030310b004408500b8050400b89014090901990408a02d4005a20009a007a4200c0010319012895070f50308c0c000d03240184440d411102c1e5035424120295950203c2c2d421800585d0112413080000c9580c90182000c0701c0c8060010031003e4100c0c0e00098003160b03440c40c914860340c8014190004030007500141c81e5007200304030340407100d4a6880324a450165801120300d000303003206500801d4214031944025000501d400001001550340d14400410f0707034425003103c44400740261400050940307902c410000f9180a41020b540985000e00240446220b000201c00d9641e016260043d145103020500c8603e0340d2202c0150780640d00ca50410503814000c100808038071484407000110b55007000100310703a00500303101041c4100c0d40002800050303605c1d0400c0383c4014001c4034259594101d403900680c0900302c90707403021400354030101d0190 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 251867311 1250 251866061 251866079
    0x6190f020a020703020f010c0b0f060402071a0a050f1e090313171605010801051207051c0b06030114240306040606031406070906050d06030b040c030b070215161701 72
    0x540b4406c030789864002440e03400445903a1100f00010303104100303510210b0112151000c5003070b0132a07000f500141c0343c03c805841300c45d04626a0641c19078120546010000700220a125407900004800d20600c0d46084c0b10446420480b049030b02140b41f00f1030700c004651075100030000c541500c11051502c0e6592a601c0300d024802030794100340702140703004000301103041c0c4442020b42c00980b40140c50f40e1503180d080c0004d105c0c0046014008010718410f42c0000300b12540d41843c10344620f0000c650001c250f0940c0d02c0d007100581009004907000c1d0781442c078000d01d00381030420800d500c0911580134440c0a030144114450b0b080d00084a44e40501444c424003081c015a41c12882c01c1e613009450b0380c008018500c202541e031f140219551070000b000640c041c801280300308028462000c540c0004103000352a03440b200704a66055174202c0e03490304030020810421a048405a074045414006030004500d06000c00c2d68030900140050764603011100c5010540e40900742169800b0f040030b600b090b10f907844140b25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 251868561 1250 251867311 251867323
    0x200c270c0415020d02190201020f01151a03041208040503070803070c1a060a090c0201020c10020408010516080a020912060403030501030b0c0f0f09060910050a0806040e06190f020a02 80
    0x80c0c9004614502d1154a5600015648185400c10b5005024400e64002100f84104040c14101e04500507803440c0500b031442401442008121500b2140c01d1a150000e400312807605181000c0008409204100c00b150880b440050f0510840c00c1000c0c80365602e10303041d4150b204150008000d06004001d00c208140d10400880c0d03080e1048070441602031004c1010500d1420480b592980000203040c148400c032400c5e001492201d07118000503081c0b91810042d03070b0134550070380138000b400b607404601042901000d0203090b40101c610410f18041d01010140182000801400c4100c0c080d0001142401c548803c04000ca50301510001d84c2c0c1c85007014607005010301401e01c000c2d03400500d0003010415003452070301154403101c5080081490103285074240070042e08039880d82940901c040c0603c1c1450740303c07041c01c603030805510b031b5419a95001111014050035000350525018514103241d008440f0740020f41c55400048056489000d4141002c01c0806884500700c068401800031480b201c44540000c3c1c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 251869811 1250 251868561 251868569
    0x3020a08071b0b03010305060a0f02131d0a050c0a030207030203070b250207060f120908031906140618030a0c0807030b0c09091b0403020d0c06200c270c04 68
    0x2c00c2d8580b41d85644641d000c0c00280000361081c0c1020300403c0f03a4215030750240c10b4501c00710300b0143c181240c201604d0380c0b4040c0c0b81d1040340705260240414030303140c3c0030009150b40460442010807842c10449803140a90042c04003036414194001124410300d0b000f0015201840d51003041400d452410100840d455907400151404480440140c0182c0a0002c218141030b541d05988481c0704401c098012580b115031201c0000e21a80c2da50303c00400f14102034015845504000000d0002601d801c8000040f0394890b8005d00c5541206002d09002d50380b0007007215111b01d0000d900e501c2100200000908100074a40c0c01046000640c00c0000d40c241c2c0480c41408581c000c183d00b603030554880210a400d4030480a4082e0700031034010000e00201c1c80c040c072020406d200e074020181043c0d200e42c0892440341c1401410fa6802c01500420010281d1044080309112074003040840404100345001d03944030302d0b041c0781d80d1040401001c86079094446400e122004039a00644061500b40403154403916805401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 251871061 1250 251869811 251869853
    0x5090a140a09061a1516230609070303171e0117070609050a0902250302060609090f15090a06060909020f06070f060b150d0b120a08040e0403020a0807 66
    0x18036011100301c61003582c000d401d8081d08107030305e140300200c141c083c0754084510300ca402132030484041d02003002c203240d0302c842c031110303a941e610140c001031f0542e480c0c2200104149890750183c602480000d611900c2a02c01040e00b80781e2000e1501d5488803c540c810840040078542c1c21400000141507207080030301c005014441c070561f1805901c440c0c0c101e400c1001401415001061080c04000c0c1c001281c0c01003110909802c242110910581056801d00705000802e07001a07111002b44002442d1a4840303907044038481000784813148082001644556130401c125500c051000b000070b82002c824031542c070007a43c1c8400d0800482d03441d4808280200541c4400b640200c02c2068260914149079080b1a00b05403c020f0348403070400e0030355074600134006d9104030940200c4221042103004901e10040c00f9800300503180826034030a107400b407101c6990000084d00c060380c458178a100c08291058100c0302a01e0780c1a4160340e03a691070341002c1c1d28003500c2c0c8400901d082c4000800005000740725421404c07c00030b2003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 251872311 1250 251871061 251871071
    0xc03020405011d0633040503070509091506150c2103041a09030706060b0d0e030307090905042102030d05010b1903021b01060f05030613030905090a140a0906 69
    0x1031030982c00c214004001c1d90312a07080c1000b01c1c00c40c0c0340c240c03204009044000351780b0807000c4031181c1581e8924410070700002540b5010800f07101500e000d0103040d02410040c4c0d40301109141404000741d8a42d02d1045541200c0c0400c404151a9201c6020000c0c00d11005c154a07582e404070034020553303402e8403200c501c2c0c00684000d814100c62080c001140c0c0940c2d04844000040421000c00b440084c0002c0d203026882d1104000000c0012000d014000c02010f600340303d1a00c031001000841c1c00c0e90522000d90303015070410001c200744182c200e8041c1003070350300d590701c000b505555034a44070a45404404841e500c1150800fa040230441d4000010a4524001c980500180c0d07038941411000340140c14000e80113011440121504d644254003070965002051940751241801da172405084900e5900300740000c02c2029000e0000c0d08040000d5a049510005002032075400c64400810164140c000d16210300d142101264403130314103070400841c030181c80c05480300301d003080c40c0001e008085c0703804101d0b40d01b0300b01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 251873561 1250 251872311 251872319
    0xc08030f1c060506030f07021006060f11070e18071e050a0b0a1e180e0a110405060403060c050705010c0305010f17070504020307140f1e1c0203150d0c0302040501 71
    0x18000d00342110030244c6181e00350303140c2824000c605d40009200c0d80451007001c0a00740e41802c50f0044c1c4004090941703400a11000c601c4000704040b400c580c00c800340d03902c00041049035050744600c80381d11511001b034441407910b5414000c1d0510400790301070ba2281104009089c80c2c00340e00068003088681c01c45145031259941c4e900c0369106d010350a1950081000841c0c503290342a040c88a1039260103403403412070701111068004900141040c0c0041882d0980300c1c0400c03402c11f505105401030f00703400402032400d191070a000101d2620031400020010750311403805514050180094501c0d682d48038000b400485c5113110f004005007024421034409820084001460104003c1c0305040c40e40c0c08809001a1800d10007444040e60024290b002084503200c450b200603c10300b000340c008c1c0d040300f903a0300e076881c01405075003403d8464803240010b0a400c104591010303102c051900d800c02c010070140250b01c0f03995102c00300900d40a81e204c1c071504419950403403006c1003004101e02058a108480400050342c072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 251874811 1250 251873561 251873617
    0x90f01020703051203040606181a0d0f1202070f12030801060c0f110a0512030c010501060f0504030b0408090607150f0605030a02011803210e010804080904090c08030f 73
    0x714032014000307800203000480003003021001503502c20301030f040109940d03a40385a0074410405480c08900311603500c00f603d003406020658a0400700704216400303c40703440b85403544840c0c0366685100418040d401c0740050b010300d000344140002854640848003082d941c80144442c4403e0f4140102c0001d03203248000f049243c000c1d0840340040e9000488601c1140ca00d80c0c4a80300300d03441c00e00c0681c0c800b002c0640095180d460110b400010b035940c00240d9101e10344c038070a0b40d09403079042e00b00c0e50900614403050302850340d100c8292001c59801414860031a240ca08110300144201040150810000100c21040c00b8400f00b0720b0282508002c1c04201442884215178100d9065010341c9506800c081e002102540c820072a5a008180d002402003007190f49a41e034080400140310820181c1d0b11400d91080c00d60f030040002c0d00b481e1310a00700180c00e03140554910b0040e100f028840c1e80314551703540c1e506081c05007181e00500588208400c40c0d54680200309421210f4028000c401c0503031010041004003018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 251876061 1250 251874811 251874823
    0x1091b0b030f01090e0a1506090e060f0c0a030912030923190302030904020409050103050f0304060912060b0306010306050a18020603010e072c040e0d08060613030203070902090f0102 80
    0x2c514080040d40d003050a02c0024040390042c801003481840154000b2500314242e6a140054411001034150300e4950641e06580291400d45603a4000c0b004000c1411002100705900465161403960b44542034103099006040046000d00750740d5804210807021901680131510107070040396680300900c503031844906400e4050318a801d8a400009012100402d0121030300755540c401e00540382420300060200702260016848ac2c1010303911903004000b84035041c052030b440c0c0b00503a80a145403504140b0003408401c0e0034440c000344007009000080901056501104200030000e0070750f4520750707590a05202414094503103036842450040d007031500c0c014100d60090304540c098107440c196071a0042000b02c0c100c1c002c0402d001d1003071131415000109004c400e0050703800001aa0b0a00501c2a031041c003007203420420001c0c0781c40d0310050769410a15008000e2961250003202c900b541c501c4c110711280f810041c1070307000942510800f5008600750300b640d00601710701d030403d0300d24614814094004aa40721 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 251877311 1250 251876061 251876071
    0x618040303021e031e06130f051608070e091308030403120e0a1a070e0a09050103060b120c10020f0304090203011d0f011211090403030209031b10030203041401091b0b03 74
    0x1d9101300c1700b40b44881c040c07240d41e0f212030010b184541c0202c001504e1415100321910f0289050303541c50412100d0b0303c0d01e45076690503140740d28003041d40b45000680039080208483c451341c0724013190030016280501810010b90400d6010b036a0507140d040a1038080c10761104203000055043c103002055200721400100b403400300740c1000c481009800590880c180a8001400200801c60341e800c2002840d00c0c1e10a1000081110b968005415031450a100d000c9481500b0744910461589200d1003080c40002554003110b08101c420001c40104c2c000103902e0170004180500d800d000108001402034034170340c0518120340400c981003010100c0010742c84441d5108880c1c0c0d01040c2c0900d4014880d8001d4000300145861081110f6203006800600003407440c04101c5084002070b4001030f0745000c900f001d01130304401c4401d60840e01110030b44500020b0445061522440c00c00d80c0c081300141c180200c409050482d244040d008000e040315500740008540f07000500101d0365907010000040600303105044078420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 251878561 1250 251877311 251877331
    0x110304030905011404090515040e0a051516110c0405180f0f0d080712050408090f1e040c051902030301050a0605120403030f0b03070b1c090215030618040303021e03 72
    0x6d041c5101000144409030051a01c01c00754800d80b01e00da240d0303110380c1c8103240303d00c0020b101341c201038a41249030aa000030181c1c4c0700310004081c0400ca00304c0b80101a03000c10729051900802042c0070905103000ca402d6034160341b007402c203418800380130711034003c40c3c0b4184030090589040c402204540f40c2d40e480d42605403600c40e480901e014507424810710031207411016902d0000b526026100b09002600c809031000d0382d12010020340c025052401c12070114440034140c42100031941c02140c0d014002d030703510130b2040c00b171901d4068009040388200304440c1c0000354032070206891405148000d64a8000b40503203409000c500c64007140d4580140c05503500050f03002202001d40d41d480d503084010b009411000c25110751a48030070b8105607003d00902c0050905001829240c0d503441601c40d000004100306110724601c1d00c424a80980c0352b41700e009450b070070182038003175603502e030784010903500c94009414000510101c8188020140c0c540c0041c544444526540296100d40518041281c48160342c09504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 251879811 1250 251878561 251878567
    0xf110307031a090a0902010c06020a1d040b0d1b050603180c0315060d082109010c0f0221040506030a0b0a0f15120e03040801060f0b0406090e10091103040309050114 72
    0x44c22450300088443c51041c5004d8000c6055540caa40907600300c20031480110308c19902401d405040000c0102040e44211400d010882220010691207681c4610190021a510038085074008640815600408010b800c0c0c1d550307868045a4001e60b100f82c0c01548107140109000382200e4500000c282a81340f0102540c0c064640340c51041052030303010940b003141c4c40c00d418001c0d0301c0003003808041a0040b40803000744100d01d14110016030300f11907107428004180705d21070100f55100d035800a039200210100086000d10b14401003000c0c07619025903400360fa44002d0010030050700680b59000f00c40c54560030342c2c03460390701601c42c035822285501c9400343c02c60000180310703803401203803184601340011500020f0000385151081000750a5071711607009108182e440c2c02e81000002182d0f224000140000482c580c00c003418400d0049c010310061041a030115526000b00b007400701c84d0031001004028400e02005031199903424049160001c0f00d06902140390b02c20f000995500401941548003900c0c142945 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 251881061 1250 251879811 251879821
    0x3030509101e080a11030106021f0606090e0402040f060f03060b0303030c0d021b01060803130e0106020a150e03120103020f010806031e0a1a18030408030712030f110307031a09 77
    0x3c0258004080d40110743d2140004660703031624000035030180001b0742c00740660745050212000e0800b02042081001480c0040c2000582e0380256031005580c00450b41040c291914000500070701921160190424640070001844414121000044134424801030090300000020140c49000450b9034440c0c0d03441c00c10a009102c1c1c1990b0003408481c0c00c0c0d07070072810b0034011075000c0c908540003a040000c007540001044109081d07000a440010100b50308850280d42c14010000d480301c9040b04000c0c07190322101010341804c5040d410110180f001d08c03007200d84400041e500000d07d11820301c8280c2c0544107400c80035206500c10102c2900c00d1070003078010700f40d5031584482038420030b2840d103020616000340740342000003c429402d0361541c62700c0c2c00c220154034202000d819101030080060528164400c0108108010020040d15607180c2c00c400000552049c00c00c0c00d070040d1800b0803505000c80d01e0143c0700000d40c4080300140d070240e42c280d81d003040180d0344a4100f4041c140002c203403942c032400c0300000403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 251882311 1250 251881061 251881067
    0x101e02070f0f021c05070501020c0607050c09040819050901030b0301050906010b030c1b030a0801050a0f031502372d0c0b040302060105040c0c030c110f0a03030509101e 74
    0xe54041c030113001e41c40c03101d500b1101010303000300782001140d070341c1c101c903070204407541e410811101207510071504a49002c5031669003681d07070601500441d0256140d0000070741403042880035950840d40c800d4200c81c0d95075101200410079401498001e011034505030300c89107a818144610f83c410740c4c004004054903420a0380740001030700010444111080700300080810f00b013036044d0104000d41c85800454990014074000f400e07445050700058000c51400c402080030208503501d280c00c6942004042000141301d1000030064850365002c4a090703c1c3d154449101050040c582400d0502d05008003445011400300860b101280305101052042d1102d2190b440711010352201c052064041c18000641040c82d5181003c409003203906902681002004004c41e04041c003851244049910742030000100c2075030033800c90061010068180400b02c80d6641c1c26881d0096641502140100b20b0510300c0c2c0c0e2841e00404a80c0a603103030b18002c021140120784154021411004107140b401103e104802d0100011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 251883561 1250 251882311 251882333
    0x60a1e090809100203040e0903120c070201022b091505040308090604031e06050c071a060406030c0f080705040b030c13060e04150507081512030c101e02070f 69
    0x10344000004011a0a281e550b07603400303503c210355640142d42c5a900d44002c0106c101c500a003044041c2d003040040c89007058003203145030b0b400044494001d45030001800100c0c5040071804450a4000051042d240360100001c500c06e16140107941d00013020352104407422030381c0080e12001e0041101800148002140e034006451002d101402207400c1507603c2c0c13075500c0c01207040c5076400c1c00c0c0c0e00c81c0710301e12051028900807551302411001e039403440c1100c2a9102d91030360034400d55005800c0380c51804280315903141d0300048000d642210807168a19100c1403180e0398070362148150100e501c14000006040e04082c010002524030040c064490003030303844184030748a4880381456550a580c0e4001160132041519402c0c001c40c000c2942043c4038030b4943c0380030211f6001405180c103001003042001914030400030104207405080d100d440b004a0142c0009186000b03025030500345000b41c00d101440250700d076000a800004240c41c464440060100400480c8140748004d4a5140c0200302c18020a038080b0701 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 251884811 1250 251883561 251883563
    0x1401030c022808040603060602070806070c020108220308060310050903031f23040c0512061311211317030712091a06040209130f230702060a1e09 64
    0x1082da400c07442503940c000740343e12a0304000c0c0400c0d0703900000c0c4400c6a04014520142c02e0100003030580f401c0680001d4507001c60914021304000c545c0001808050041c0c10307944801c401422411741809507481d000d02008001c40710103000b4440e80c2d18290184505001d0703940900e510b440910310319100c940d1100041028441c1b8204c40c0a403451001501101904480141c010b502c41e00720074109180d01044240c5004070185000c1007014495120070b01c51010348030303810140c22034868042841010f00203001c0e0a03000c0c80301541e6180441c07c000c61901c1411000c107000810301150000ea40e582441701d60640c11810040c010707460040089030255004c40081d6044021800c1446410401e20071420648031601c0c0d04580525030305081000da855907148044c2c001000700c0d400d41c200745000d00426911409010199603507900c03a003510300c0c000002d9011144c8481e08000605404040300100042c807101500c0c01c1c00140714400005100d00898481d001c401d8405a903140340e0a05860403141c0682084c1c94 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 251886061 1250 251884811 251884873
    0xf0e06030f0a0305040e1b0319061505030901050105040908120402011701150f0f050901030b15030f040b0106031401030209060118090b0906040b01050a050a1107030c1401030c02 78
    0x4503074400c101c010880d000300d0328465600c00740d03a941010741d8604440700c050310440d65030700400807169452403842c0642e0742c40462104114500490700c40c0d8000540f40d40d0b404441080d48010000407102d90140095108408690086c4816603071501030104403011070402910404013030107003040d1107414145450300140145414a600348d4855040708403c4800c0c0d00c080d48900a205c40c0fa0302d5590441c1c03010102c208141481d0311305107002403000d00540304007c602d81c1015035881126007644d40c1e82e1400d080d208a42e0500d56147d00d841c1c00000213881c001d070360599175244000000121a80719019071859190480691105a481c503824845424400b601d00360501405e0307002841c0c451665002c960041041c2c04020910001060a102d0b031210f005d0005c600403400c0c42c00b5034505980000465006101a150035950344078a40e500315071110500c540c140440c00780030000010301c8603074030031002542c0340c1260809251220074010740403504141c9900c405a00314503c039000c080301107a01081d070030503c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 251887311 1250 251886061 251886073
    0x41403040e010b031504050709120c0902070c050a080c0f04020702010507050a051b010e060f090109081b01030c0503061305070e0303040e09060f150d020612070314100f0e0603 77
    0x1164003101c4940980145001040200400120f2006903c4c00800300c5410f8604200034184408000c01d88407582c0546025102d00b85280410403051380e40c0f001c01030090440c2152121120324103a190301010303101e0507105960514002c1510080880c1e01c110311040100410041d508980c14000a0741040c0700c20b80c1070140c05d00485000c40c10621201c0080740c03141028020124160941801c2c3c02c0300125000d04218000842c50031584401d41103c1e44802d042505540b100e101500495103100b181e000400a0300850800c0d101041c1881c1c610884500d0981f800c0c014030040384422906400100c60700d650000030400d00c9890308001d6130025030401210300c0c1c00d100c01c2280d13001180c90355019130b2060a0f041c000004000c4041d20600681780c1001000508074050f09180d146040b4604a1044807446080140204021581d40d181107604a02d400c011816180c9000700f4060003e01004e4480b29011000c8000100700e40c010700220303c156616000f03000c01c000c2c1400303040c006540004085030b425108171 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 251888561 1250 251887311 251887319
    0x3050405040c030f0c050901080a0207020d02064618090204031b0501050901090e0c1605010b1201150e040609020d0803090114071709070e1504060f03020904140304 72
    0x5009002c1402c41a84000c920b50103445006821034a2110f08202000380602007800e141e039000004c01d8103c0d5500b0b00158036040f1071300010794040c024440c020b50290000030003484019000c900928a901c41403c085103404c64cc0c5800c072500d698158441183c840782d0140e04c0e8103d4001c08200b040c07202001d4403d074005458401880c1264042c4c0c20546651030364802d00200c003d6000d44100250000b842c1c828107101130300002030440400d034040e0000551072907000522590a26007a911854800d01c1c0d4120a05145d0400034001d2a002250354003c10401c00d00c04100c00b1305001303440c2d14030305000e42805203a140041c80c000c0d04101030812182c01da2101003560160381c900718543d80460281600554070705260107400c0c00c41d031008104002d44240001040030090300408500c2d81c1072444e82801c041c5584410f5524103064054101c8942c51902000380100211102c8092000c82010b44080292035103c0ca080e2482d0021440000d5208030f00500280008881d82c1c841c1c5a400c1012080700e08203511 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 251889811 1250 251888561 251888569
    0x305100f090e070f031e080c0d09080c180a021c0f0509070914010303080903120a06140103020403080901050c070b0304060b0112021204031b060504050a1b080a020d03050405 76
    0x155124102041e02c981e50307a01d12240038031800d00106030710300c9a00d403c1840d65690146a9507a00380e0420300c6110710680000380500d1108480c0c4c1003000c042500c6031021a8030025208406d00e000702501e81c0305104c121460303801c00f0074892209040c4d0500081d01a81e40700d0416019602402204641c50002d0740030400c010083e000381c02d40c1c240a00404a000d160000920f4500000d5a006070407aa05082c05010016004907005040daa0540b402000607901e0000301841c0d03210b540c15200311611500d08104215070f6a51012040c0d030100c00b4802106c401d00070044060340103500001c0d011920070041818103602070401850b00066a4094070b0b80c00d0342c2c2d0528810709400c1200d00391100c03604c68000c202c0c10746c1d01400041e0b0742000105d0850130042c00a417404442c8000501c020700344025003824403051181c05081802c0958804418052850140742641d01d1703a141140842e09603143e209441d605c0b82c41103d05a00b51000d6200401c1c11016a0302080014070218a054062200400010a054135 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 251891061 1250 251889811 251889839
    0x402030a20030f07080106212403060c0c020306060f01020708151603020f120604020d0c050405211f02070b0702010c09090209010903020904050f01180c0501020705060a030510 77
    0x10100da941e45902c0c0040f5010450b000c0246440200b14800c00184141d50b004201221032142c00040e81e1140b58a05400c100280010410100521045000c0903020b845c52841101030320320410041c4200003581e101034030706054100f402035041d04504001007050034000780c1c21100610500c111244107658829045c1880c004d0344041c400c500030081004041c00c1045070135003110030340d440d0031841c155422014032014010111404145085034010450603503664042c0c0f060042074242c1000345c8500400040d205900c00d1264a009440c03440f62000a02011a06000210815006003020050302d600721316003600c019031040d000541c244101e0020403c10035800d440380c10103800005811140040140048500703070300018401740108008125039030f00c09411802c480d23068581120b15100c500d005401c05840365200030196280658101801c0c5452604260403070050454004a0fa140c1004a88410f040e00880b60414402c111001615100394821617000810b40c1d600c0ca0031a03100c420301d0368070304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 251892311 1250 251891061 251891111
    0xa0504090b03100513030806010905060706020c120f0c070e0c0306060304060e010207060c080f040c1502070503010906090c080102040317070213090c06091d070f0908060112110102010504110402030a 87
    0x8100094050304154014031203a4201209003080402b1a240c600001c80901c24040300808058010a64001d445000c0000d0f0038440541e01003030351a1b000381845031b6004d070410b4029010300d10500c5400034020400600e485d000b00416000540f85a80380010720580f1341c40030b031085911320340c2c822698040c88801c0c805011054400c2c0c4022034103e0412000a220304400742c0780d082e882d0001010701001400c1e4030b01100c2210600161180c0d06104c4040a130708280320766206036019400d011804041180c15405a0b90040c4152a581e4040c1d4942d001e5500b01c1c0600d001c0101400030045070110b6001100001e4200030b0f20050860a0b40300d101a0313280103031408804110790b281c00d41c103401e20007140c0015400000d06602601c0607543c10b40c00b80d10100d0f076030014080714244520081210a442c1c8200e0380c04007e454020301311026540e5a80100000710118403003941e2410044a01780c0d0b40b0340c418098036009940241041d00600200010003009600c003501d407a86031503649a1011418091071100e80d209 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 251893561 1250 251892311 251892331
    0x30402180a020901030e010c0f0e030304050a0b040603062306030a0f1e0e16050913081206031c050702010315050d0302030c0d0806090106031e0203040f0201030b060a0504090b031005 80
    0x110f41032400542911880f0003040d000f6410032003c039406d20303480401d00c80b259804c1d2400f10070003004000800c2c1984540d400150300001410800700e0740f442c2400050084841d40e80c0c0030092a070744d410300c0c40d1880d4181143e0320300580f944224447c2030300d49400a5034000010600008080070315001d480200c5601124a49880d240b490308145402003e20507005001141070140c602c5089a404070b601c0740384a070151512030950000824081480104504000342e40091150b40e0740a1048a10010b01c2040f520b00c0d2180c812040044412150115222074913010350703c0703050400003035500640280c040c9607110700206406850000c0c3c507640b01c00640d8406402074000c0e5644031816951141400c0141556a080c040601c0c140290f45c0c8071641403030304640d81854000b0340007607644551248540182c1c224404540007209000511520502a6080c14800d0328208000500c0c00184a01409600c102c3e8002c6141403004000405164112444c44030b8002d05441c0248040c16131502100c406844d10307440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 251894811 1250 251893561 251893567
    0x203090c120d0935030d0921020d090501030c0c0204240b03060102150c0702040c0e0103050a0525020a0803151201050105030307080d0b0d1511031308030402180a02 72
    0x41d03507000601040a002c280c00c031490002d4500c468801c0128140056018284901026441c44d800c10700a4a0105509080500091590f4140300003440d015401c0c4421a2201c2c40401c4500f41c0005180c03215588582c80d0001d10343d02d010010b40081014020550078817111003814030043c5d0f503500c60080340701c8406449a11445d0034211003141d0304207a4000c0201500c0400a10140d60780000714802c045a6012410241ba0703912221030140d03002c3c41e40025000b504000414072080c1d0002203469000000381e1f03082125a580d041c24005650094034103260b007160300003407007409001508182001c8101c900446001c41920b075034071900b503841210342e41010741d901e00510456107004a458008986e140c0d009100a50500001030349034801e00000810260300054207803001ea01d03e403c00c180840f80204240b2001e8010700f0000b4522034031240282840e8a068502000600e1110a83e4043c5284143e01902c803400e56440c031301140c4c03000d4000e9134010072800161740450013107181c05116400c000d4025071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 251896061 1250 251894811 251894833
    0x1608100b0301020708090603060604080d030c120507200304030506010f090c0906020601060503040c030506090607180806010b0d060806010303020109120c110d0204060911091009030203060a0203090c12 88
    0x108940488580c98466401000204049210041592080344c07040710110f980351691307070000b500c1d4800c0f94400c85241c02484041c03080d0175095844034843d1003c80d11960602c0040341c52a00460350100d4500c00070030002c94001e2410068124154800300030001105e1506440352516480c2071004d0340480515010148280070031412402000545600f906002d900b07a801c1590194481c3c2050185008000000c0009014092030f0075064008503040800d948060522044450302c4010807903c0c1d01c08980c040c40c1680301d005609404104a508c0140a4103040c0d00b0091000c0041c1c1c072003251090070075150710010401d540148651402588a90000240b80710079103021001c500400305070000f404543c44d1800003141c400000c250504208980c9495120601e2000074010080f0342c0014a1180ca443e0b010420004654000c080a0104903802d100e040024041110400c03402e00009405410010214a0b90245600515000000c60064030034184001020541c0e1a0303c0760361131002035020950001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 251897311 1250 251896061 251896093
    0x3060a11094515030a06020409140105030309010c0b090f0f06011e050112022217010e0a030c0b040c031205210907050609130f0606121a01111608 64
    0x10ba42e4a03504503220b81c9012984082004501c01049001c04a500c2100d07440349950603c4810b41041d4410011511207444d107034800010880b034181c01010816080c00811a45800002d546241005030f40d40c8225600c00e603240e44c091440645503200521510032a00c10040050054140c0403501340c005042c558500307082001003140034901d003139009030f03040024003059a00041d0b05440d546954805a5200356001e00c1648403100041064000c00c071700d00300400d4840c1429000c0320840c0002c0000c0c00902225001281c4401900c00000d010550ba0f0140b400003a1440000325442030240780301548140c0e0b0790703d4480e0580c04480720000040c00000c0c00101031241410b4801896020241080882c603001013002e982e1200c0e801441d20a8101141c1c1c1d1645580b034140c2c48150b440c86c4001404007920340e00c0d401e0060320549c003444010881c4c028103015000300601c80d142d0701e0380d2202c540c4100142220015601c10700c029100182038083d614074140e650700901482070043c406a4001c04a040405000b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 251898561 1250 251897311 251897389
    0x1090503010c0f170103030905061b011b0e12030915120112020405010806090d031e111e031005091b0a020c0307050a03080304081605070902070203160503060a1109 72
    0x14130301c2500c90000600100e54800c1c0001c060307030402d841c2c840e9600e00d5441c03007035852a00c18140400644c2031100e030850220314000c01c03450301d80c1e9a440d0241e4050400d800c00c685c081c100c01c1c11226079803042c880301c03481d8542036040c0c4c500c8113808241c0500d4491108016907000c1c009030007101e041001d00c00003404504007882003070f00415035580031b003105003006c00d80340303482d0b4050100303420402da01c0381c8031094442041d0000c20200d400d4a44100030100500c0028001500b14910102d8111004d00c03143e01403521100440b84900c10b000b1a049540c0c0c1080c0400450900140120622188201403001456a000010000c0981c035030001c00d40220120209460a080c80c0c01090191110000800001d800c50041e6a0451b40c0002e907143c94900040055450001c484000b811910420500003008101a402405410300a0302640d1070701c803121600e640045024419582c159000c1000540c44801e00e0340310702c80f030350b000301890381c40c1030b40402c00101910414016000f043c19201d4001d2040390854a00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 251899811 1250 251898561 251898587
    0x6140711030a11150702031b06130608060915280e07030207020f03010e0a06240b03040b010603020f0a0e1302031009060801050702060105010f1211090405070e150901090503010c0f 79
    0x201d4a05405e40e40031980344e05036030b5040c2c542801c4e007200d502da09035900000d03209034044810440a40c0b641e103e0000340324002c1680ca19000e401c0b240045042da122400358110f1106000e441c11142950020031030420402c1d880708030f0500d184103400800d07003101240c10769004013299540503840d94801c0c0100152448440c5e4080d200303a24003400c1034031024010400ca0581380d001840040c0b00342030080e2030050590004284420100242000300e40503900d034015500840c0180500f100c540c0c0c981d442503049104030b82256805100030310440d030b94280308088085076560060400c1c078441e0508496842a6001514464050904503505015201a84c4501002001902c0c001c2c8510709046d200a5152001805400d0420012013400d001030340c0a62146100c40c403102400304010039004251030407582004490314400c606190214004510a150316840c49500521a0b1010007004891040b2540810000c5050182e03206000605035000c0c80f8000c40320360640c841003112054030800400211030014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 251901061 1250 251899811 251899849
    0x40c020f070603110903151e0c07060207110d0303021b07030c0306020901050423040b1207090c020a0f0602041a03010b07020607030507050a050705010f0906140711030a11 75
    0x40d90556000005840811030340a8203000968200741c11010a035403191104c1c00b40c061207041000703505902206661486000011102e9607a00441c8481c50261901a50715100a0b903050028501160460f80100740440c0b00344904a803948404010460500c411107003030700440c0c3c2c0805d00c0c040680803101e503846086a10005000407508650307581600507100d001c00f80c0380c83d5012a5400d03181e401102190040c0ae003c0042142680110001e11814281d01d40594007813404c00c11040ba4908114004c1e456000d260000f904030a420000c80400900491143e43c0851150396038034400709004090050109019040c051380e0b46050040c2d940340c1d698400e05541e20204104010000c02182d102603500440d41100c190b9034031b02d001e0078101c54901440d18054040d00425414504000001410030100d82c001c2e03e03030a042c1c1d081d41000742c0300028140700b5803010810f41c5040b030600c1001003004040051181100219904c01c0038007192420050000c1143c0ca031085101008207031030600c0d0503484034040b0078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 251902311 1250 251901061 251901073
    0x20f0607030b030604060f060302092e06172e0e09060103032a021807030c02010b0d020f030a0803070503090f010623010905060a0906110102070f030c080409020d020405040c02 77
    0x8000c00d40d139110060003c2e103515582c1c0b0355140440e4403034010000440d0014400c0085040004002d085942407100303040c02014000a400300d4038510400802c101c40c42c0b41c803140b2440001414600c207105004141222840e44001d0394014a08507401e03001070a031035840100d00460410140900e101d8024001c07045c076601000c01000000d50110f078490350f1078a4070302c003614810b0508881d424400440200250b000100c00d031004100349950200911503031403580c050000d03c800304000d900300c500310f00d0a80c0d004200081450094204090511807050f0098101d401b21405600c0b0f1140a4009492100000d54000244440c0348130802c8080a40ca4018000300012407400000e0b07003550726410344409500d0b0f0000d01c22902ca0380240d03494802008007404059480c0145400140500c01c51300a10012038542c0c3c50081c2154014400e582d4055440410313496030110035201581d0130320380300004071800d44041002048c405454005092001845400035882d281408100003e4841030150502190720407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 251903561 1250 251902311 251902331
    0x130902040e1207031412010303030e060604110d110405040e0a02100f0504150c0507140117041101050304020303070507080a021f080606130906260303040c0308090111010c020f060703 80
    0x740003261803659160a1504c150b070f4081700141454040c5030304d22181254214000030a242c0c040d00900708450750302080d140caa940328001c0004507032003105841d02c41d140510101040341d0203503010220b59881d007445941055030320400030302503d03607911006040c0e030007031808038045090240c10011400303d1418002100084081d0041c4140183d10550000c4c105540369610402c0c0121200c008494010f001e5592264a8034508244030b4480b0b120300b4005890301d0a05510648000d465901440c0d0203c2d040700d50030000c500445890301b01810aa0f8540000c104005c001801000000020a4aa0701400075401c3e58010861a41c0803034500c5c11282c1041c200700201a940480c1c66070b440041180c2e80d948801d1844004940181243c00c51586a4603186000c10b5003d4589003581d02c2c00c40d0506500903506da40030005451380001d0300e004201c0f201e60081400018410005085244c006151445c480b00d01c0c00c0e285420f60300c081c1c21040151300040300409160742c05006007940b01d60301e424180881f90207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 251904811 1250 251903561 251903593
    0x132102041805060c071212060509090f0601150504090f061707080c0108060d1407080312060907030605030a030503040201050d091a090f150613020a050a0905030c010e130902130902040e 81
    0x4011b9000e0403c060b42144881c0ea100a600010103001c02500e01c140501c2c0c10b907010340d65507414000c0d139a4688200c400029980104140c6012000140ea840c28242458410340402400480500c04401074482402060841003400b81120001e00c900007042140d10702040c260030000d155440d541000b00700d5040020903201d024900d0300c80340c0d2000b4001c1d03c4002100c032040c10143c40f0742011400303000014140c2c4100b803804070102e000740b10840391009643c549910590844149100f0f031034040d040040c5100100b40035002840d846070060500915001e0329034180b40445c1d2403540121290b060400d030003c03035000022015640101da19004080e50011000c04540d11200d26404d042c000140c040003e4841d2514207813100902d484c55010754a0f0355184101500d01d40002c2c01143c0000c80040340001c00d4039000030f000701e4801c411b841d2075040302c80d05410700803d4090440f43c0d0342101c0d280c180b140d00584940c003507400d14290000d40051806070500c10841134803031000126455501c030000489084c4c107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 251906061 1250 251904811 251904833
    0x50415020c090112060b090a09020f030d1713020604150f171914070806090f07080601031a1f03150807051009090e100f02132102041805060c07 63
    0x5500701e005000351340c503440d08502402029080d641c0000040042c01b40107451070300641c028034800c035840581442c0c3e41d4141b50b038038280400d450002840b44a005c10581041082072074010811040d070840d25842500401c50740e40c8241e00000002280c1100c440416910540b00200d81c1600e1030600342450b02d50801a803525000380194180c800200c14610000c41240e000e035080038000c40302015945012070001d40001d02c115001401080e1420000c1c01e81c00f42000603510510640d1540d502079268500114020018402c1e04a540344032420204070382d5035100044001030100808403c0005503486005040d52400c404c1400845285001800101c02c0802e21505486080e03402100402c841d0504441080851b445800c443d86040b200112100c2c0100b500e0b4044000d40200b40072882840340007004a100320140503c4800e101d420921001f070ba5611304e00007500e09002c1c000014103c0360002002c665030314074505a00917403118103604009041c006141c0c400c2800340000d05103102034903903d0101c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 251907311 1250 251906061 251906069
    0x90917090307170d03050f09100513060f0e100204051309060b0a141914090c0415020319140307051e0a0c050c040506150c10020a050415020c0901 64
    0x20601144880340c41d1010451031009090b070000c4200189603401c1c0c2c054940d8049660200004e060200281c80b000750020001c4c020140d920003008200143c4031b03208002d0001900801300703540c108440102040440c000c42c0117441c42e009001a694a003d0811481c1c15081507140c804940180000c01007a6200c4100030020001507002003400942031030300340010a5242e46042d07024110800216490409800d11240c0700f805488000840c607081910380944800c9100345038a10303004d010700a04030b00b0f04081060304604820b0030740741095200c4160395940c1c00c00916140c0140d102003198540b070654050050146002400c112400d100300404003020b902c40284101c040c80000100240c1050703485d950315240064840810341c40d12002e40000300100510501600c80d8030403482c20b088149080c0c401e45001d60b80090551030800041f220b00400c94001219846041c05a000102c6600302c0d10b000600800c181c03659410790b07560408450800300760700182c18508650115074000383c1a1900c40c0300390b0550b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 251908561 1250 251907311 251907353
    0x1050d0515060703050c0d08061003020703020a05060a0e0c04111e0c030301030b0406050a0e0304090914070b030f010602160611031e19050705060f070c1e0b010909 72
    0x107540720721100030285007a101803904034200041d02828164810054854035004106440c10400c0115084a142c1c009440c401e130b2100c400e003610400e041c02580101100340c880d005981610900d621070a0078200100c2e45002c000e41c8030a00d810350764100f0311190000c14000c8074200440820303040104454001c01c5204a850480480031641d6200f0110540da964941c040445e9660740c0c50f89400c015461007507400302c038014103040c00700301a0202402089208032031100154142480c1c041d00e0f2018259150301540c0c0c24400360700600008000344041c00c003416182412654900b0890599050a0030581c051000c6400100840036140740040c0b1000c1212031501c0e2610010aa050401c0c0c21481052100c540c6540c0c0122500400340d004000760031034050300350300c0d404890404403060b9014030440340001c0058000c3c000096405241c402c03440e410400c1454050203411a81e680d503201002c920354080e00c41e400542c0315404101c54060361a01401c046082444609455039685030840e42c020b61032004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 251909811 1250 251908561 251908571
    0x40212040605180304030c0501030e0a020f21070e040317070c0206300103020f040924090c03350703030c143106090b0d020702040e030d050f0601050d 66
    0x80b56801031900d505082c01d07000e8940c5e032039481c540348465081e14412180440e081c440d450000c040040740d003054068000c1c154100d0f400c2c3c1c4104204400001c00044200325280f6981c072081e10b07008200c030300040c110705e52241c0d42d40d080c2400c0140030300081c040444004100002000002031b801200c001c2c0702541541c410b070302d540c2e0810204000c0c44840410b01d104c12600070440b5014503280141034101c0703000340d5043d2403501c400418081a203c40300b00180c0090b0609829400c001041805009004461a0300058500da035607a92074146240d940f043e64000689180100b440ca0302c6003543e410800c500c1c20000e2a040000d0707160005000790b07080603061560300c04003003018a008451009607499050b038cc06598014851342000030303000254950010f5100101c0091503500200c22420070303500c1d5502c40003000e03132421780b0301c41c160f51141c442002100d40a001d901c0040c2c4071800750141520741c40b0055529152040d00b804221350005110007440401c8800b4800d40c0e076082411551803804064010074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 251911061 1250 251909811 251909821
    0x1406030a030311070b281b05070507031a010e0a060e0604092121112508030c0301170c010e041503050708070f0f0617060301180606050f040212040605 66
    0x50300d00520001800c00c03c1d0080400c5540d254003203007002c081c6d81c02d0300b036029000005020982101e61495002c210b01240c000c0303034024140950060300c82d036480341003140c0c0340c1e64403640c9150f0521b004900490351412954014081d10f00039698595001d0300c1d029007000118906090038940e210041c007018012959180d1040c20b00120056260340c2d50810000b860b01c2c02c0c070240005200c040c82a40443d070b1126400e0030001d270080e441c00340a0403418012601c41c181000d450200c0005185480c06110f0008105103130800101e030032020754800c80400319140e440358900300728240c0c0c3c011f10703400e40d12180d000140030034240da810612030f0f544031005880014494445c104a0392401007160405011441542d8000482c40c50020790607060381d401c0144041170035031700d104200d90342a55000741c41c0801d5008085101c0f6a120345d07040c60340414004e001081052940c1c1d03a104103084099000d44505031103c00600c414144000b130301445c4a0250341c11440c0010480c00100e4100d400384c00102039a4584001c02c1e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 251912311 1250 251911061 251911091
    0x3040e01170129131103150108130209070c0b151005160809060915091002190605151e0108010506070b0411030a1205030103031701082104150804061406030a0303 71
    0x104541e1202c04041000c000007400e1746141e034008442000913085e0074406540d545d44039100c0c10307004d01b8060168258500c400d03400c201c0c02d80c0b030080000c410048184009008207919504007030180268007003810320a03000750140108840a2104034042c06800c0250000343c090030b045082c1041d41284003035442e8107000c00002c01505c200c1091a902103d03c0403040c80106020303004111803d030845040b8080d01000409903114654048203d0000c1c1c400201040480c01c1c80e00320300d45c4902d103645940c604007035040002c1c5280f581001e10240c12a180c880c1201300e540c1021030b09000d4402151058208041542d80c01040000184014906880e05820007040d48007040f25050441d405802c250600900130303001040b540017484258001030781c2d500301d201d4a01071401428161501d07040900708101d08011f07034581001040d008000d600707804200c00034484640c101004180d4080396030720b002904042c1026400e843c03a07201d1040300142e0540901c2030503a000070700d850340f69505040100e180076844083e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 251913561 1250 251912311 251912329
    0x60204090c120f0b0312030a060e01080c010207080601150c1403030711070e01061e1713030e0307081f0f050103210e012c0303040e01170129 62
    0xa0091581092101001203820a40041140c194071004108004054031000f094030700c50380700e55802d41c0140301e20403100021314004561081d05a14041895a0344d0001c1c03244043c8240d2182c15945c10a003540a0690380c1804000d0041061030002c0c40203505000955a480c2d000309094421303c20410031240410100b0008102d4126505c810741e5224607004002600c0b00c0c1c0305129541d058098001c01042c004900c4003494140c4003183d5501030456489110103010300300c5603541c1410301410a24505001d109450340e00c0c4540348480c0002c1040e4281d1030302625018108100c544643c01c041001d002c11000000d102e2005403024004038a070000640a80c4003c260043c1d030000100c0c00c0c07200100c14070250080140301c00d401f480340004154001d05040740c00010781c0185c2d6000460340d00b00b104131684e5015101d0041400c2c22044200d281e903070000689164041e9100c91003003d1440010040484141e0341c0402084242000b4890810360083c2141c002192074090b4503400f805a102c010940c503200030b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 251914811 1250 251913561 251913569
    0x10504121a01120210110705060703090b030f07020717060105011119060b010e03070b030a090c090e01090b06010215010b131e0e0c0703051e270f0a0302090a020c0a051506010905040504080a0c060204 87
    0x382562424030020300c010f03f80e01107905d80c0240c40f4155000a8201e4a5484c0203c0c5645880103031500342d00700401181c030b240c050400300170709116081a03950032200c0e11500781c4000b481404c2c0061040440b500240245000b070070080d00c01d0300401020490390100800312988001080c400040c6d4400c185060b0707095080d10740007407404918100c40080d18420544c400f014281c001c4034450010f40c0d5a04c01281e03107080c91a80014041e90000c0104076100c1d40b540905000d0300c10a081e200001d8496081004100021401a0300000d0411042200740c001c40086504801c440b03400d1843e080703568802030034500c959030413000211800030011400700d201c04107452125400c85007031501d107071240c046449070001c82105103202d90f422805101d040d00d80040e44004880d800703850508140e8038500c00400035003061544008034040e1046c10700000d4800e1100e2204541030041d2410b180c107025000402c0901940c209500803441c050910010403842c90030703030310820050715041244441c24a44000a0701450384 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 251916061 1250 251914811 251914829
    0x50709080a0503130b04060c0f1401020d1407110d0e04061a1c05190e0a0c031b080c010c06150f14120309010504121a0112021011070506070309 63
    0x3518070104180031000300032001c40c2101c0e007038226840d5203428140e84121b109400200700c44803243e10000f094001801c00e07543c00b442c80c1da1203070640c0d00e00c1d0074266400b4281401c01690b403500c20401d080b4281c1c0c1d1058000180b0b16100b465929190305113543e880488401e403003408159083c5695950740e42e04050090105035150706030b41441490131820315084402819141d50003041c0721082929a48501d03842400d20304091241d6860850406008081d02c99241d0564000c41d00740d0004900200044002035114024075100c64604101d50808100203403c44030403900075400d034000aa0381300c0303482c1a0769a0058000500600c0807801e0b001c00050329400307459503101a290009035000f4051542e021020182c9800e98001c0044500541300d01c82d40e28000d0200f8014403003409075150040498000c3c0c1d100f8041c24010540b041d0798288140340076070208020340003029844003181820b1030500f080300740030700b40404050b02e9840e03110f480d41158005d1502807040401c03400c083c10710a0100000030103c800d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 251917311 1250 251916061 251916073
    0x120219080402101d010c060e0d0e030712021e010c050609061e0103050304150c14010903170415050705090a080a050c010f0807260712060f03030503040605070908 71
    0x1180584040822502a48920691440e04203001c1c0a8203924000c1500c03201c0d80811103001000544242d0b08000c0c082d05c8055a881030320074020010440b0803001e21881d21220f02c1c1349001c0e8201762402c42036410401055250400da5401a154294005421035010301c43c102c040307a04600403141d00c40b030008064850711a240601400302c83c082039907401095400640800075103a0903266030810f6082c440140305910400003005848808804519020f04625050852040b151900103000800c03188a2901365560b201500c10035401c9040850300c0500c809000d40c2c10314040e2903402c1003441811080e0150391700c500000346124400d408944010000a100c40b03407040d01d40e07888542c2c0e01200c030700803960341c8107102010081758040c02c3c40304140d05c0c4d1950391480555591408598007076050207030713810118050f201c0c0c18042a10022251091020381d271100404800040c440060341e88039800282c40314540502400841d5100085035405030f08408007107516260f010b012185144c0552188005000d03003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 251918561 1250 251917311 251917357
    0xf120903080a0b0102010915090203010e0f0102190e030a02090415061412011b0e1c060b28031b03020904050307061116020f030a0c06030609060801110a1202 69
    0xc41c1060007044401d00420030f00244100580c01c0b2800c5107809480400e1903240014601002d80049210368030140010807104030b2000401c2c17901d540d140390201c1c240d40200d000c080c01c01810000c40c0c011129494202e44181c501000f007901c0b8940494040c4c029074003603000409000842c0310406110420440c02c214040c1d0350302083c03a0b03a49080c04405e10918520080c031409940502410845c0100c0902000700e002e054102522031000e01c0342e0b08da4010b191020710001c2c01894185207503c4900456000c90048000d004109403d84040814100300680e001148040c0741d1068844059030341c0011400008100e0907901d4444882a5000a6129046c607041104102001c0003130045141308a5051255186c0c80e02c0c6014180150b803805000616403603080005403420310004800008060141c40030504d05440d1140c0c42c103007903080b200100707844d01400c0106860030300c500001410703818000c001c40300a2181b0700c1c3c200c1c41946141420004001c035540340c01140c0d541240c4421001490070707014000e80c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 251919811 1250 251918561 251918567
    0xf0703020f0f0313080106060e1e060d061d07020303070f1e030e1b0907030c050c0d08071106090303060105071a040f03120209030a0813030b010807150f080105010f120903 75
    0x40d00130744800504c40305001442080500a40080da802a00c804103007401c0301c3d0070b1101c8414020480c92440c3e40071a008034503615240b000b050101802400869694281801e14117010f90112f620307201505000200995a540482541e401441901d8544a0321200b88000c03074400701c03000c84a00e0024100c0c4002e14080d905980044242c3c144601551440300c0015804d103520300410b40701a13004074805000422062003544207400e500d0b11820028100980000b00ca468840b00c00501c0011400e0801030209558202c45007a020300d65010013000c55181101a0355201e000180106040c410042005000c01409100ca846d0211074030034401c02518040c106101e114000c0700040c0c0202e507450742c400b80465041e00890700070010182c02442c3c0d00405a451204030340c401807a120000c00c07003420110001d22a002c80c10300808600c00201103a80c18290f4004800740d94295071130900c8014486a541e00f500b01b07032100c1c11a842420b1410180d40c6080082d15003044001c070002c00e461601d4092410550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 251921061 1250 251919811 251919817
    0xc160b0c010c020313050906010c0b09060117280519061413030206040201120204090e010209120f0a0b07140307110114010f0308090a08070806180d050f0703020f0f03 73
    0x1500c1002031041107901c03032050740c0300d106811500801001940007840340d41408001c20b5003080f0180740c180041112620740070410501610088840d400100c010025000740d03a00e50820200400003a01c00c17490540c1c083d040c800e42e4244d00b0000c004071640f030300003400403c2c4844000341440b2882c2071401c554501c3d22000900303030b0791214104401e1410210f114107410180b00d40c1490b81c160001c2c080da0b282d070f4005640c02c40d4100005244560208404100320380c0902400c02122100070000d62a0703c0c8007400c0081c0c200a0082d05c0b43c4907408001d0500c5e200c080001c2c107100700c98011003004150f455401d07040310010301c84001c103148082c0000c28000c2c029882194281007214a80c000c012007200c86003646401a0300303106004590518510600200d040d0000a020103540240520201a521100301c0e040884c2540922840c2c1c1204080110181000d54018800114007000d0540d803400450007410900881141d06101c00000c10540100343c001c000c4800300420560403950702022654060f0758942c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 251922311 1250 251921061 251921077
    0xa08070c06090602120a1b02040c0c0201140304020d0209090f010203010e07080f100911160501060618050603040803060d050f0309040c080f040602090117010906170a03140c160b 78
    0x2103900c640020018030129003c0c0d40c040a51803039034540394120031b04498003c81c034465a001109071501c0c0c24016525403141401030289601c0d4401c00c084180005801014074040311140c01004004100042e0f4814103400a0298102d5020f48241c440c1d011081c90482c040c00c954203d503200000114140862301e4034148a040c1c0350b40d07071020b55520328000b02550301e41580e252a00240a001c01e0040044c00d80080f058010500318090070075100300303103540740c2582c00801070704c04c2d03551508244800d6506c44281c40700c45415146105c5103030300d00b2011408500c0000c201a003a45030200210300c1e00e59032510084907181d042021590203a0440304501c4c1c8a601280195104a140c58903024985014010091143d4034061115800b07a541b5140e0130042d5110340d011300e040040041c85030401103e482c0d107a81c040c249208001a2003400c249003081c0c41d607100c1120005c2c541c80000c11100003a803059000d02454001c0001c3c03910703008584c480d5840e08003040c0c103280300407410a00108003000010042c042e54 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 251923561 1250 251922311 251922317
    0x270a0501090e030702010909050717161407051903050d050411012c130e030f07060606030209130f06090f0e0105010f0b040b0a120e0a03030b06090607140a08070c06 72
    0x2040104943c0d9108248009001c030749541d40c00c00100c642a44a030b0351186890a011990320f5a4200d030041004040719407a030250560708482e10221f034460015008807451740040c0d4540b04043c0c896940c0c1d008190350070690014540105003c26202d2002e17500c00607800b0320184031500707040c58040c035074208040354280041c11007101003441160607580c010030801e5000c009030b5445024410f000034100286600c0c203110f40c80d050314940400003000200745c0e024000490755102c400e0f0745003c0c410b40755194800c01c10140184000c0400340d880721114030744040008800200e0640842c0e8030805400c07181c0c0214400e0340703002d40c01e81030b8501a41107107016040c45002007042c0d07a2950781c031203c00d140707500412495035001d100c24458080c540000340182100c90400f40d40004009101e10241c0e04841c520441c5030b00520800b80805030540668014030404a0b0030758105400c0c000070071031034001c1c1c03540904402084080032003094000e00656a540b038002403071681d65810350915007440345440c4030750400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 251924811 1250 251923561 251923571
    0xc12150609010b070809061909060801050604140405060d080f090109090606020a021002070305010c0504080d03110d0f020d022212050a0f0201030b0a081b01031802270a050109 77
    0x1640380c0701c24024180c4880052040c10921240c40d5035142d5003181d003200e40c00600070801e2001d42035140c500c066001585e6661034120301d0070044000c00f021010b900141c0035050501c8113021069914449014592042e1000100790740c40c1d000003801003001c1320011b00035210004425200c540200000c004818003a00e0396079495541c9c2c0c001d002210501d03c20000160403c1c4444001850300d9021017289090b01d10486410035169200c0c1c0c0d00311443d0740610004210005400c0040741024060804031607000d042c200031840b09010808401d115031686c00184580c1d9800000041c00035a045e40d9044c442414115150241303082c0c40030001d0b240006c0361840060280c400160003990280301c00ca0107900c071015080b03041d01560b611119950010703080b41807540701d0450841c40e484401c6003000501641c401440403100902100e1014403039621110f04143c10801e0300d030642200807481050003941503642d02c82c000d1349051145044a075884403000d505040c070003481100c03815500080e068441407001002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 251926061 1250 251924811 251924821
    0x10605010e0307120305070503030f04021f020c060f04080616020c03061b130506030901090b130512071b06050a2a0b0a0b040e0102030a0e0a03020a11030c1215 70
    0xa8440011507216410703803252005004a484015240e00303410310038100a0305050131a5241d9040d5002126450302e8036240d00d080200350710303181804a6002c00714401c01009011020700003900c400101c0600340c021000000d030b440014008000306e0700141000003c0c4d40b41360420413080800318081c0c1c000500148100300705403907140b4020840c0c0d4050260308840d400d4140c01c40d9807550968000701c046456035298584002825100c56004501c51150705000203140001450007030440680a041501da1000e100d050900042001412000054808404907100c1d40c05243c000c000482550415100c0d21030802d00252958004c4064003d41e0030f261600461203480a41c3c20090850309200c2d02d0b0002c3c100c101650204100d400b403550414015500402c00d03003802d10226065400c4640d0303a8201d81c1d400000c2240c91040c40c422444050070f44ca010340078469440e14002d6541080e92405822140e200c81030400e5580c040001d8403401001820700300706510b020303104517100d0720010b180821007103000b00007503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 251927311 1250 251926061 251926067
    0x30c0b0906010819030e0a06032003070f0309111807020d0e010e010f0e09130213021812010e0706050c0c0406051c030302070f0506010512010506240d0903020f01060501 74
    0x2a0580700b0900003406a607000b0b4200420308000a41300b0b90034065984034038480e0307448007488880540b18544002c94130b0041403016404140301d0419030000700d0710600500a13480d50044e10592014014074001c01c030000c44e4140038604201d034014040e44500c2255011460780c401440144c441c40c225001c0e100003004e291303005c0d1051000700040314001600c03104041c000e507006d10414103003440c00e490800b5003107a0707240204040303400540b45807100d2510000c4c45011440d1034080b035a01403810102c2581090700c201500b01c440310084550701d10943d003180081c00c00003000d6000300162a84181240c000607690305000c2c0c41540011480304050140301c040003514105401400d0468802030142c8a0881c0111903500380903008003411010543c00b000708002050b03401d0200c0698038000d10107400e480d4988000c0104690014001120690400301000b40698441107014030101200e41030302c1d62040709041080e8030344100b12803942940e03d800084424150300261129007480c0d604020070070951102c2c015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 251928561 1250 251927311 251927323
    0x6170405060403080c0c010e011d0102120a0905120708030601090909030903080d060f0b0909070c0b1614071401060f0e0c0c0c031213060c0209070f02120403030c0b09 73
    0x340c5a5404000498002403107182410340c41401000a40e0174500da500040342951084801542103079140c1d49026a48411803030b01d01000203441000f14909800c0c0b81034000001d40081143c06a10b945020720024080123105c0c103150124a038030a0395844000341307444402c54205a03551030020340a1900860485200e2280000c440e8245e01e035154413034615070741c0c06a40d07403090100a0b0303a05d0719130701c3c001500c181c0e0808020141002420080e15a110401480810b5100805120070131540b603041b540460070542150303401246410a080c09480401c0d0159020350203050844941c1c10000b4880c0d05000081c1c4114040300481030003840a1581c0303108440c101080c50103043c9905000e5400700e406110b0707030390082c5010720030281940e000c41c00d500c00090030040821485031000c0b0000542849000341d60213140c01512240c2029000000b0b180c010528100c0c00801c0c41c0107000a103040d01d00b40600802111040c1c00d5078101960b0f50765180e00d0000c04804035160f0843c2d803015a0808520702d00c60104107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 251929811 1250 251928561 251928563
    0x303080a0509030313060219111213120305070b0703050f070e01050d2307050309010f1505090601020c04050c0d0b0f030d140f03010f060206060d0c05010f05040f03030801061704 78
    0x3141541c403045a50420285c10100840c0d44560801c895404115803800b145910a52611400c245c1d00b504520141044003035145054003800400200c00104d8072480440140c6c1d811001d60307034440700c091070252010301c142400501560800c2c01044442a13154020620a50200010b0360310394898480590b19080c15811050116909221440c0c42c1c0490f5880a0700c2c0c007045803482c050b01d03694003022034824a01540d005e00000c10020410001035024000e0705200c0c82006010440d18a242014900c07603c490300038207205912140c0031801e581c1c4200b00c6c90f00034500040c010851410803007549111075115040e506065400c10149013807610344001d00c140c0c00d0101401821045514240032104075600c900c1c1d08000b042c080c0039001c048111140a14040c0011068001c611410840c01924200c001040300b0b20566030070001d50001400000b00301c04982c02801c09002486141d40140e0b43e60085400450503014800c0340002415030040c451030413107095485445011107100e408103442c80382254 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 251931061 1250 251929811 251929813
    0xc0c1905060118090206040806060102060708010501020a080f120109020d1a09010e040309080118020901080319050309030c010207060501060f110a11040905010216140129010302070803040b010303080a0509 90
    0x42044075000c0b081c582c0911020f40c0c00141110250380000e00603000341d00042665804041085aa540c040100a4000d8454149010030f507152100017036503070800400c01404e81101040800d000c507a03402c269030814001d030311842c14660b10790301050003e42020b40280e1001d030506032040015220075000d80e440c154050540c0f40c1e20307800e01e2030300d01c82030340c001e40120100540e9180c002441038007846261003110b049403080703c03500510300400031100d006030003d004640003000b04603c404100100e14020700074070f0030010f88035901c10039598214002d10f8503440d1a175000050440800805a215605a500649a0101c400c4680740101e40e900c41c19006400c2c9548540b03c020003045c204580320100c0c00d001000401c0000840d9943c13401ea800c200403104898881940c40010401101c08036002c80340800004c0001e000b00429034031030740a01e0701d0304940304a441c0004400503442a0100e900c038a07040081160359003001c0c5066a00c22109100075070000301000041501020503024007402005020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 251932311 1250 251931061 251931073
    0x10020607032003130c0308120a0b01110309010c41060601050d0f020f19020714011706190605041809120f120c030f0b0604050d080a030e01050c0c1905 66
    0x148207004060380b000aa80903805d0f44000000190714000400080421651940d007038102003078040140c1c3c500a107020b050025240c005441e2a600000750307001e02d002403030400407001e0b540c200a01c0030b1404681642501009440d540c0584550b1103408414608100e00080c035034124680b100e448400644440340068800c10151049040301d400002d220309040800514207400f03040d48a00b40c1c1e00c00000000364000385050070003a0340c0c05202800c0203020300d1041c1c81020404400082c18810691481300c000034000010880685404416002c00d0040c0c1c00400f0785252500b5006e009500148100c10303407403a140d070501d030104013180600d400340c81c2e2202c41a00490610030042e5401d25200b14030701c2c00c2110070151340401c2c580c80c1c000c5007002c0e0441d4070001040110704921300d0a8138903140365a4051a000c00003045152a00c0c001c81c04650380004030961a080c0e940e104a01030454802c61800560802c0c061002c0402040000c000e140030050413101d0310440c10709010003c011020300907040b90485 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 251933561 1250 251932311 251932321
    0x10150f080c09041103010f0609140c09040e0102120702031308070b1e091e030d08060a03030e01110a1109060d0c05010302090a0509010e0103140601180c0e10020607032003 75
    0x41d94280383c10038490149114a0142440402e003100d1500c4002c0c1070460301c038107041080c980740748503200d61a249201244014500458407403018400d6501c0503000e00da454200c40e948940030343c182c5200c3e610078080b0110504210b01c0c020340da41c100c07611686142c0c0901e140001c81c241c00054140c00c68076112822801d010441d001c022440d120307124140d0242c40c00704032601c244c2e5501c401c409107100082100002c1c031941442414902600c5a03000002d00c03680034140035460b40c42018040031a94146000541a5000d100403110031003202480201032141c0d280c044100724000e0b146c41c43e911001d407001c1e11151b50311002c01c0000440c0102c00380ca002e80c985403c0c4a11f52182e0002c1a00100141c80c0a06107907817500805d040038000d90024640070705200060082010f80360541d000104603030004c0002c0d50601d1851044d25801c074903d40300056950b540c00740c0d07990061810b1103562038000c0c04100000c0c41e403000030351200300c2281d40074002031400300340407800391942070b4480d118482c0011040c215951 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 251934811 1250 251933561 251933569
    0x41e030b071d060d1b03060302010e0f011b060b01030506010509090a0b06040f170d020102070201270302120d0807020303072115080304030c090b0d08071410150f080c 73
    0x1d0040d40a00c80303220707100700c030020f4035900d0050095050403480002c032107502c03e40b602800c1c0783c40c444450070141010405c1015030703440007480034084402c07074020021a03c250b0058070b10884002030420f2040a21401405100c040d42c00344402e25400e80313043c0a0b0703940f003100444051086c951065402800c800202e40c000b00303107600054428101804180c54591115640c0010110030307031080e10030510081010395681014004005848140d000940c00d045490f0f0004e45920f0500c0300d011451848841c030a1030382c41c0c60048210040d5006442c0d00350b154202039150b900d44101c1f00c0f204001c02c0540d070210307a4691000081328800d10050382c5102c0000ba01d090311010401071003500b64426902d40c0082c403910784205c10300400800900006554403032543c5040420759049602190141d0f1904405489a407141a80c0b06201039000c503040ba5035446516140190100c254510400c030701c2111058004401c5550207414408041c00000042c01c0c2c0c0c0e04000314008a150181c00c049401c580002c3c081418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 251936061 1250 251934811 251934827
    0x7050d1401050d1211030c030a1409010c08031018020415080411060a0c02030106060e010f05030415180c06020705210703021002071203080f0718030206130305030f041e030b07 77
    0x5140c54140451071009210900d5038107d6228401f0f15080000c40c0840f03250048040f07101010035009950500e446100041d0502402c18806001c184d00000064a681410040350014107018410324901c840c6070064403000b90028040d8045030710400521030942401010f100d4440d40e48100c0d40300207a08280305105050700444010824407440040607001a0350030300a00c1c01030041551741100023000200010308021a6807500c806000c0d0820a200108080b60500440080701000205000a8031400d03000c0140300740070041c001114505002c44d40715408103241d82150000c03074066064543c04441258081c2c5840d49116940e0301540040005041c1071000481d49002d500580320610b0340c0d25102e16020996441c120002007004040090504021650a401c22410328009140180a000441c800f8503e404040d20840700030661035120311000007503502841c2e1001c141c0381c99213641c4030f041409803c00c3c01824046e01d000f0503130000c0c03000c55010007812a42c000c0201c0e0b1140c0c81c0d004069510704 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 251937311 1250 251936061 251936093
    0xf1011030702150705070605070b131106070c0504061703040e0c0c0303130201021c0815040e0304061806020d021b0604150509040f0c0c02012607050d1401050d 70
    0xc0020300048000d6500c8210000307500c40e85001c43c1d59a441a841d04504020591300000c06205d420b004c0f200214002c0200180d001c0b00700920700c00c6407511800c00030000c2d00914a00c2c3e6108030000340c14400c20403200708520842c1e409036010700440707480305071400006404003a40040d5500900003005000e1156481680120720032281c10b02d4943c51040d041d085034401c90ba95208000c04800010455074100013840020580c802801e1103880151401071510f01c01901301000a10300720002690b650b01c55001c48820030841088980d1103070382d4a070207400d0550900d42c80a01000e0010006540c1d8000b1070b0301900c4441c581c2c040c0c8280300d145580707a1440110740c90407a40055003480085000244040c1d40c4810603e0354039015281c5a03501e00b04815144500c41d84445e281c204500c02c50380315004450b00041c1a42420004480075410741c40544101e95108245d0340c201150082c40318031034200c0002c0858900ca0607043c0980c500c12041542441028840c01c3e4000020b03030382d803101040382c00c3c060307403151 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 251938561 1250 251937311 251937313
    0x250c15020d051b07030f0c0909080a12110307020c03060c0c120d0608010f09060b1e0d03050702040c0c020a06020105060136030c0503012f2a030304110f1011 69
    0x1042030b52071518135114581d0411141044680d102d0414094800320101c024244400240702054035660303202071900524400f1424008102c0c02009042c00302d0304800c1c64410703c001307015203901c0e100100944d28802c4411181c0a8002e0801040c2c0100381d02044469205070b450041800d80c402d841c14203425809480302e86000b5990301e502107414403080c080c1d200c0c840041840420290341a08208085840c180541c5101c2c9070040080f05981d01064640b50103030b0011200c09035040d42c10700b03060303c0611401c4002075100703240161461402c1d030000c1d4000c008900940362900403030b49400040e07081b104162403443c085a0a035025109030300c00c00c404088014107100072104643c19807014441c903408650011078100c806084207002c241070910544018910000c403c1d03410700d00c8007102401342d1074402d10701e03048448009682102d826942c81e8007003d9000c0003985519424003c00f1542e100c1d001940c3c1160200f1321040da0038141d18284980d0011620009c000340a050b00d1150141c40707544419801101e0f07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 251939811 1250 251938561 251938597
    0x30304080715030501051804060f0f06090f1b080f06010903080c060a11120105060906040e090607030507030b0105032e09090c060302040b0717250c15020d05 69
    0x820300d8180564001030120905152030340d0101c1102405454058000b103000320344907924698266450242c80d50000c0d04404002000141e02d000b280203403401c000c244010f00d05016000035141203c0c6e00183d810b0050480401c09020b203100d040a13031507200ca501400291059000c01c0c1d1400851100c1ea41020050400e181010740c0c030b0b5a406410317001a900300c03810b500a2000c001c00e00d40c107800f8000b40c402c15402402e00d40580741c490000545018051035001e0036003c40e00074210f44444040b60041d02e03c42d4003461103803804070306603659100c08482010004c0d00b40408540400c1c0680102c58035054161605400c0d0f5030340d400c0c0d4014000d080d110a00c2900c540c0485616080c052041c900e02a02283c480031801d00d5050900e100007080715400f4008041c4100b05c10043c50183d41c09032100a64800042910080d00200c020950701828008003500c1400450460761104040003c01c0114880c0c00b890300030b25610300401a01e403a2903040c840141c2c00c10406e071382189106c0c0c0c005081c0c107800402080d030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 251941061 1250 251939811 251939819
    0xb18010c02090f040c0608161827150303080406052e08060c0c07050d08090913050c0102011b030f090b0f010e180c040b060d15140301020304050c0906030304 69
    0x720b0100036501218816001ca090201388986004900050030081c1000030250410245440300f04061a0040341002004482d00c0f603030481c4944400c00812042c0e0403501c0b114408880440c880d5030291211805030314040701e204440c8201406078045070f0b01611518070903580c0d616450b0291100034001c1300500a4081011070100c00d45490a0302c16000140058400c0d00f494540c1d894400d0107070010b5030100c010b00003482c006000081090035104242c1e0180d50b2142107240c00002401030155040d031000b0203008100d0711f00104506505003600400c100c3d060441804010380c00c0300d900c0c8543d9802125400c0401580c50300a4000d5501004440700010320b41c0d90685a042004000742c958541c90840b80004001d07401e21080500e8201c10b0a400e408429169003400f250344200a89900d0f02894603003002e40300c0c580c3c030344c0300b13443c6500c011100c1448155103550b14403c2034462801141040002140104550b003014030940f44650341c044004e2100a10190803c15151f10007403082ba458441040003003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 251942311 1250 251941061 251941069
    0xb0402070c090605030d0806090c07051608010902040b09090a0201030b03030d0204080607030501060206090303070c0c080a050f2404110a1a0c07151e020c061201030c0f0b18010c02 79
    0x8000b09007001e00020784500b803004060414918480d000100060340b03042c00440d5940c0d040158006050480d10b50340e80b522883d05504080152040030948254043c0c00103240074107400c0b1001c000d20848040207229105d1007000520503007070391111a5940f002c0b600c80300550082d401002000401001c6070300f414003055a013000c1e680560000065500848184840380b40c150144a02500310760018001c075142203011035980c0d0100410315400c0001004840051181000e10400544000000e13100c80c60000d09040e6651240341c0f8a011b118442c0051403001580e4480c5210300e180501c03030b1050032903107843d01d803106c654000458169011048104c00035515014600d1883c258080700c0c4526207480707255005600300380c21a444600c94590400c0c1050070180c0c050420039122401c40724121112119120880c613008503403115030740201c000650300111301740c40d02000307040f01d11400e4034544c4a601c035440d07811403c8080c800c050000005002a4129481103841c10b140d984062601100061041d0001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 251943561 1250 251942311 251942333
    0x21e0c0d141b040b0d081204110907020d020f19020d05150f040b010905040209040308130c30050c09130f0c0501020105180706030e0a060606020c1c150b040207 70
    0x80301d901244a000b03030142e801d0501500307030655012126000c0742c8026440340d401c40e20904005440c206183c00005040100344010241210780140041c061407a20f1080655202a1003003c0405841f40c13080046903000005900c14490800060721400443c10b41d00f03101c40c103002c08200711400d004940c05074240b0810074000501c1510702034005040f60031f007030801600001c0d0680040c4801c5081c04200b0000d42c5405040070f4101d40d141c5004a041d0b614000b05d508031000014000b050b01040280002e40c0c01080d000714035186000c8d0303040010070520413044500080b0b030030740d0003450385c4c001004181c11840c10513402644828000201c1803100320076514008000c092040c00c5a0142d650070041c0301a503824840c25521003208888031740401d4090300100d5403440c3c9441014109a20b819841c400d10400f400604e407102c0c1d0003101170001580b01c0c00080d44441420700300e00d00074540340010381c102400c10003411250b9500104140c60704c1c440c4000440140401c0c51015820a408100d0200090100819 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 251944811 1250 251943561 251943583
    0xc0102071823010612020301120f0f05060115090807031e150203070306090e011e05100e09030901020c0607080d110c0d0e0102060c250f0c080706021e0c0d14 69
    0x5a0b01541c10044080c080385083e481c00c0c1280c07131041c4014000c0440e490804400c05400a644140a00b094507003900709a991007002025801107400000304210784c42d508501d400810f0700c4a0030a2512255007a590710f040b480058600044403e00d20480050841c6040d500e038040e1152120750041d44040c1000e03a0b20030780d49400026a00c0d0030030030500700e69119101020515000078022124444016802e8010f403035080d006250303854010411502c400c0e04036400070409803804880604d41002402e89a41044491740e0241c09103203826071203458007404075104654811800c1d4203001020028070010441000103c84c0c8203000c20071510560810803028030000e8585da05d01a000400500090420b5006801900c800400f441040000c1001c0071001c2d4100001c80401e50000390308d41004e030700e85901d80001500306120b9042c081050740011405000740e4040760210b50480390100c20401c000081104c4250740d903000a18090481e107048103070410304500030321007484001d81d1000c8003820080d00c008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 251946061 1250 251944811 251944871
    0xc120705190e0a020f030a0c020f0106031a010909030f0f02070302090903030406150f05010c0501090218011d0c03070f0e040507030b030105060402040617131709030c030c01020718 79
    0x4410400d949107401070b039900018008080d81400ca40c480c1180c258000513000e03049054656081400040c400c0142c120101c003850024018650307241000c2490019100d441c04103541d01f00008140c8001c140103040c076090b8556900700f28090841c03c00c440c0e41d805401c2c07075802c5015141002000d070359160704c001e000394041405180e4900301403070013004a0b0444040e80f41030b150482000c01400400107549004c0303803404e08020100088610b0028010001408c000f540300b0000d9050201c03406000707140038180c07030070036041908220007048100c4640394104c801d03907041941000021051031080c0b0401700d0316141410040d03510b0300b40c000014207884040f240e41000998541168490b03207002d010b00c5030080c0c000e440440c60706045c540300400c040d0701c0d4410070108100c85404501c0c110b403920f0407240415042240c1d04801b0410020000b6160702082a580c400e100384403030304074285004220100b03001016002130040610707141558560a23481208d2106180ea02c00c03442070081c11b40440f079140ea00b5440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 251947311 1250 251946061 251946109
    0x105070c03140f03190b040b03060601050c030c010606090807090209060f0a1e020102031e16050919030b073c030209030f010c020d050304032a02030a0f140c030c120705 74
    0xa917404049076001c42c8401d200f18108050030199440c08504140c12036028a0041da03540813294804d4079600c600780818000b503107412000141c0d07951214850341551600001ea4040503a078a02100503405103203500c0b680320200304110004916a8001081039400c60700300743c1c0240880200441046000c00606030140c1d40000070800140952a00c081e90407003400c181d5074250600c070b0310340c2641c4ea4282404c4428410001000070f041d80d900c0413254407000c089e10308041e60644034540798010140a940140102e034490034a411500c0f50a020001014501c008100010100c082c1c03d8583c04c012080400a1560070020280c1c0c130f40302840602d070011030920000c1070000c51080024904007030504203c0c1000818001d0000080d400044500d05a42c02107880d050b0f13844a51650260180156009606100c3e0350802c030b003000311038910380321024060f8420410403a94580056124084201545e51582008488103038600c1c20643d10103151380910101c034074644d01c0b2800319031307203082251070222080805 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 251948561 1250 251947311 251947351
    0x1309021305040903081602121207020a050607120606080702030a0810320409021e1504060f0201060f0b040909060b12070905130b0112020117010f170105070c03140f03 73
    0x300e541b040c00211034401007040b81008480040b45006a1000002c410380800c007040c0340d14420440304805a800101fa10414240030364050300041c482c0d03060b403441d18209040001e51500440203144680c84a07005145080b179608802c0310380309001003441812015842004c40e00340312a01202c030301d10250803054210b244031003411842d5415040c455601c11800e2600718001611004002d911810301030300c180a01c00482c000150341010565880415014040340004e00b160340403425181c4c03c01d4540082041c55114000390084c0344640c010021066001c02041060b0340656204885040c018070000444500c082e0005028000300c00440d40e20354050682484007a80c288101d50300010841070328107001101ba6100042450140f20b41442003d0b1419001305590049102e004102c80d000c1031000e980d83c40d0700140c01207441e1030041c580c00c010002890040c501051050b58090202c90701e99102c640b015a03011541d0b00e400e5108041d56080c1400f0440d103c5a5010265000e11480d101c6d005401c00c0c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 251949811 1250 251948561 251948581
    0x30b0403021f0b010e03070f1a07080d050406051005030607050d060803121906050f0f03190c1505030405070b16050a2319080c010e150901050c130902130504090308 72
    0xa041561187d003265800300401c2e01300341c42c0300c0c0403247c006c000c142005040811401e5503028141c2d01030050600010000c02d020781950149110300d104010400654440007030406581c4028060141c05600c64400305d40705034000c42c0034017825250280d0220342d154442e0012030840d080600c00e051610b40d160140b200c0c10580136440300c1c070014000c00401c070742454a00051510300607019058048d91541000c155151418007442500c81e19001c12000c01802c54584050348015521425002c80140000f050b101ca128608a0f405142c10900030a074080c100b07400f800c450303441b801e4400f15280f0300001c280c0009405000d02d4102c2401002545640c1035401e1150fa94174004149070340d400c0d0031041c081380044071411107103d080e035042200c5075214045150480c1c010030790001491124400e8010410798040443e80161003034001800078070542d12030f41002c4a45002e0485009000c034001c076400d100c103404981c040d181c508009030341c103005166a4070100e822a0413002c07054001500c0ca000f0030040a0f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 251951061 1250 251949811 251949827
    0x70e0105060313060f02091206071202160b06241e0a021902041e02030a3c14090a11030d09050108040206040906060f0807020610030b0403021f0b01 65
    0xa42a01d1451440c64410100114400400001881c05503514541030300c04100c0c0d8183c40340c450000e00300488801c448a015944c6d03200490740301c80050000040c070801a101d074001d442c4413900c001050b280500081c3d50b055a040c0c4014200d0360013906450001105e4a9088200b010080d0700d501d1300c5540d600113018024800f0a88004850091070030040040106e40c0080c21245450064443c0000c01d156840054050081183d1000f104224210080c00c0c1d1a0140c0c0113500038800588100302020640054240050041c900360f09200807042d42c03252001040320502e500526482c00004c0e0740b0000070384240509405803000c01941d401800c22a081010051391110001c0c4100e004200b408a030880060840582c0d0040c10304001182010904544030101624082c0525480c24400c0c039445400040c50b00d5174a40c0c401c3d00080a00c0d001c00c1c550b40c004a80c81d0700500c1d0b0117849035034140c2036484020092303101070030460440c41032900c00740b114a40d42012020300e030481d13107000c2182da8039440018801d074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 251952311 1250 251951061 251951069
    0x6051801061d010e060a0810060503011a030705090405120a080702160b030a020d0902130209150405090106030c0e090c0d0f271a0703050130030e15040305070e01 71
    0x8070314075074440900c035004200b41144c030084041d12160342d81c00045a4131000702c0d07000300301c0d0b48500603040b8070820490308180b050365020360080042854803440011961411036146d0b400d60088007041c892800c009040e03035072040c0110100d071a0301c0164000c4040561007481680c00040f031110a018546c0d40c1440524004020003400a03115800c01808240502c0090641c1c2e95550340081c0d1140320030125007010303002a8004003520300ba1070100c0301c160041e503ca00700301489280311200191402096405823410f8070000f6110b003030340c0ea0802105034018001e481083c002d01107403240c01106691070740380c0c00d1710560705038900c01c1e1100d40642c2d80805580e03001c049140c4842c1001021100f201c000309a240184040038201403001030203080c40860208403020312050f40c2070300810030050325015080720341256217810100d11a9413401481c04c1d60000724081c082041c00c1c0104659003c81d00c110720748500d41300d00030181020001d00415520f0280d105610071900ca422140b020490a00f04030b0000b8010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 251953561 1250 251952311 251952329
    0xc0604060501051e1c020301060e011509030506060d020a031e060c0504031a181501050307051005070215040909060b040b040c090303030905030d0e1c26060d0605180106 74
    0x1020406040b9007200380d00392205400342c10034505d18110402e98880b00c0c00c01d65000740c000c200060b1101c00d50039081c102401401e1140c000180c00305134283c455900001140c2c0c003c000340000d42c07668010851840c0d050328069901031030214010000c00d00d0300881440844040b0400c0003200f220b0310381007096941402c00ea0b000d2103014842007020031000d4008144102c2e0b0000d028815550f0640000b19803003041034807542a00c162030000d0540810312011a041c0d0703004800300c9800d04c2d0f4030030401c1480d04101010380000303034003440a03c0040c1010304040c40140310301c90410b420b081e200c0c400d84045420302c1806540b00d60300c2d42d02603007641c1410302c03801d849110251018080344540000c068481c928501c001010180d41c2c24241050000900a5030041050414240502a040c01e6000e5480220301d0741c000041c41880794070009640940c103003183c0c00000c031002c0d01c19030210400d070f40381e81a8003d01e8179030454460f07500d40c0c00007100c610034144201c034111440002c041035a0103103400c6441640004140d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 251954811 1250 251953561 251953579
    0x30905070611100203090a06020c070303081f060302090102010603050d0f03050f040c0b03040c030b010e06120601061b050102090d030c0b0108030c102301030302010204090b041116080f0c060406050105 88
    0x22503402150318440500070203c0560350b91624009146042030101d40681003c1c408210000d4124022511f0000c49002e0740c0c9680f03a80c1c0744e030f030340e8100c654003040c95900c041e802907002080480d000340c01404103a071050000284207070340c80d140d040c140b03100603600c00000f4042450500b40329800d44103060300408042030441062030107a8413000054040e01940000c40000300c0020f0400128440350400f845d8401d08000c01c2c3d581da80c62010300036070260360b154490009081554184440000d80c0c50480e1119030700c02a40c0c1381100c400c0d60145100c8501515555002c0020b01600d48511100c1110305200369a541c821420078103002e040050180c001803015081000314805240c800121a101c408519600107810300c039420b800d03040c2c008410320305c1442c3ca1402c0000000d041c0c06501620441d0303e555014031108009500b008100d44070900500034008041c000304480b1039070080e40d01c00040c800d4194500e00381d404aa41c114541010010351403541c420030400c01000198003485004100690390002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 251956061 1250 251954811 251954837
    0xd03020f090108130807080a030c020a0507030b0c221505031006030518060708040302240c13050307030c05040f050105060d151a130b070b040b060604150309050706 72
    0x280703104520546042058040c0422800d0090b003440400041c0d00220581e6503c1440c508818242c000484503004a232400783c440c2040d500200b03003605010b43c8107020f4440e4605660390307520800b90182070b03207110030401d000402d041d1040c0d1881444070300826010306020361402d4a0454150402544a8104002401030026035481d411040c000c1d50881d040108050340d8918001d000c0a540e02c80c15520b1f4400c1c881489429600052040e0142d4000d500783c41d9807218481512642c150003c90b50a040240000058503142c2c4980207020035101d101ca030640b180e80d40c4c1700000c0c0b81064076082a1003503505cad24010041450700344103840e821904414240304c0d541c54900050b503503000701d0f0b0103100300710b407548030041ea203042c61030700c1c0c030701628034080b1103450504810000b071340540200050b20314035001c540002c03c200282809440c1124ce10051406445d555551004240722000d8039003500110207100204401c42000342c4014294416580000e07074444500b403080c42d00c0d4280d80600180052441c0c001c0f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 251957311 1250 251956061 251956087
    0x60f09090b070c020f04091104061a091c0b01030803390d06150e040e0a080703110744030901030c020a1b0305071d01141206070306080d0302 62
    0x66804846803e02d07405000b0180013150440e807445088642c002d190480e83c004010814010490803442030710100b04503610780e40072152a959030306004c3c002002c14000c1010134502403065442c1d013002000380d210b000c04640d031204154402a00202c0301c10750301000300586000c54032a100d0031080740204c0d9518800082401c140c00b0886c10700001c1c2c1d040c500150304240c2c034031b45e9003020006080c04203403041c4109903482c4c020402c9011007074140c429800c0039000c0c94050030000b0300030340f000c0d00000401c0c50220319680541c0c500e90003147d058254011040002000880c80012400105051504203481c010b042d00303556040010031030408190404004d02c0300504000810707244010002c1c200040c40d2102ea002c142d1820164a078001c09042e02420083d68511008810f0003c883c40b600446202d541c0711100d1500160742c1007182181d4190380b0004101002441d00b40c1c101002d000303031070754200c0c18030195403030f0414038211019404a40c4914003080016404c21010200101d685001c44c14161103500032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 251958561 1250 251957311 251957333
    0xf09090d020d0224040807150c11030403080306010c02030f0106080c0109090e060117070f0306200f1204060f05070914010203040b07121107060c05010c0503010e06010c060e030d060f0909 82
    0x302c240d000d444c01c005002c212409040350649600b02d2201c100c140320081c07142000d03080308a00fa1001800c07000e40505502000003d54094980c4901d800342155100401114925200d04060b42d0520403500c00a0102d5002e11510740900401400f400c41c0c50554000500a541c0580c007100085160000703000b400c001c08280d0700e042d00c1030001c81440c1d019841c80514034100c0300b600085140610704400204000c000d03031004502907034084480e01400180d88052102e030003003da5880c0e001c8400c01040c6ca213411200101944030348140c0c00003441030406009102110005c40d424004200c800d1000c2c010900080507501084100348010b41c1b5090400d400c0d40500e00801070000c04840903008602100c40c001d8600c4071544d40fa01040b1200c156580100070800d8130280e07000e5459510b000910a48107100d0340450b4180c1300b980c2d11440e0603072114001103c0c400c000e1401a254982d42c0c0350004220003043c00140842e02c8200d0001c0780403418045611f9209070300b41d01481070180341200c407000060368079600d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 251959811 1250 251958561 251958613
    0x6180b0f0c030c090f0111070b040503010507020c030a031b1a0a1a03030f30040606050d080a0f12020c0a02090604090317150310051f060504050d020f09090d020d02 72
    0x84a5645800c20700147e5031040611030350103140c0110207011a0550f10b130b201030011110110001e005544a0350b405984030706080c00c4103a00b40c1c1001025070b0100303000e04408200204002252002c4000580b6811020388160103403c00600d0200c0c1886402c082e1409500e104070010010480301d6010440065582c0c89884034000d61240c0101d001f103107841c0c1c4100003080014890181590580d1101d0703110780f80382000c490440d64180761003030124031400c02c40d44a922040e804910f035440d180800c20291000305001c0402d02c20810703841c160810714030841c00074200c8003021400401d1111964410815015002012180214a040c0c50500070036402a2110718500c800d60504915485a8109009114810003070540602c61055101c40340382c01980481e100b4081c0d00c5030b19116030541c42c15403050780d01e20310071359001a00c00c1c8014890792401c8005441528801000003400c130b450030020610784402210b80c40c140b40c020b0290340307010384d40501c030340a50035210b440a040808100224401041c18981c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 251961061 1250 251959811 251959819
    0x50d0e0d022805010e01150806010f0e0c0d0608011a012307020a0e070906030b0d03020d0509030a1b05101407060b0d0803040b1512060c0706180b0f0c030c09 69
    0x2c0c0e011000c0b810300249001c241c100000b40281c8071821040e5002e0b0031004642c0514100324000002d0804022a41038107171914050941c060a1a0058a215003080034102900d0701c402002030b071890a00c00d01c101c900500002002050170001e40c030384004154075407a030b920305100c52403070350301f55422a0201c2081c0300040305c0d203000e031581c1c51400813400b0b0b035103990030807045807000c0c0e02804299a007010394030302100d0440e5014009200381200b0320123561103100780100964403071403625400d24080c8000d000b2126002d4200c0d4002c03002174403aa840b580302015031486103d60813409018504119031085543c40c01410b004800c1c0704242c1c00090144030300903000d0301b0203696a101c6112544c4c1c00c10402c5520b504403074095100d0402d801e103148010415280b00b409850b03c00c0c0d051805050001c80d4080800a14010b400246d449400b80c80207540003c00c11164190b603028211184003009511001050180c1207490461a002c408040860000340610000d40030620030009541c00201c00c6841c1c1000a503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 251962311 1250 251961061 251961103
    0x105040903030204050a0f03050c0d030c15110f070605100305150702011104030602090a060f0203070b090c27060411030105010302130806190b0d030f11030f0a050d0e0d02 75
    0x10500b107000340515045a5440b04004000292440c1034070704010641e4061000d031460000c0e0002000003140c454000140410f208a100802040e4030030343d1441c050100a0001c29084ca1044100d581035103e4840c00701040c10118400d801d020407441040d5000440100c00e003800303425515800da4900d04080720484a0145d0000110742074030030741040c6a0b0300c4a40c08542d071074a4480c40c01e003020750004185507004403540f140005209104030130980e204680d42c0c000e14a03158064542c0024040c0c01048407031288502c0c040340500c0e4440c4010b60103940590b8090350038200d071511300344001040103042184141d04240d050704030500840c0c00c0364110340007428010303941c40218400a013006840d91245645000c0e944c00c0015220022180e4411010f000d407081105405c21420022100140300010700051003d80494200c42c0c0201d03003044080c40d40008582c10520305a000e96000c0d40039104e03141c0040c00100340c1d9081211240181700c034065002020b01071084018800030764034040d02410f40070500e111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 251963561 1250 251962311 251962313
    0x16120f170c0601090b0301050601090b160807080a0e01140306010206240d1103070905041a040807050303010603090c09140c16050609150c0a080f04060e0a050a02040c02070e01050409 80
    0x18411501011551010b071015507a4918406001700785844c8901e01035403c1c039001444561080442d01e0564480d000e28030705161081180101c2030040c110212440c040c00c000f8400490b51070340141c4036049040e50364460f4042c003040010000b420803161607a04003014000c0c0001c40e0b0700420810380c030040f4a84103102401c0b1042500d002e850a000041c0d4019003244000010711404284000000f10203800b01c03030655607109040300440d8412a0f020b007250300c0300821100803a00e080c810a070018000c1111034286012521070380d0440d4400e0b4401c001080d5a0b44038081080150000d000050851080420858040d000d60b08032035540100301d910315000c0002c0ca0fa0b550740040c40c40040298001c0d08540c914500895055a9000110071440d03044c201d0fa40011101d00107901180c20314190355440c1181d45d2036038103d40020880144c8100c4055448081d0203092620400c42102118011310003032120500034010302049a02d0040300c4011504000d40a00207600c1a8941504450050b00d001a1540107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 251964811 1250 251963561 251963603
    0xd020607051207140c0703030f0e0a09020904110c06091506090402040b0112020403030806030f01020c0a0b060f0d060b01121b050d0f050f18030403023001060816120f 73
    0x10700c1d11403424100b404290841d280a00103190b5080e88d119451318050404002c000741d420360340c03011060364410942c2205202c4004c080d00504483c0402810224922140e5081c504150300081030081196010070104241c03801c2c00c214110170f003d058032003c807250030280c001c107048641c0204003a000726141d249078104c9034070401c0004051424098115115078881c1b80040c5500c0e02510202d1003486a5000840402418802c40320802011401040144815622010200030042084d51b00c002c1c816811a616180d0313150881495101300c90010710105250000742207015019039922000f46000100018086066206007006085080c29030300c0380702d01480ca81c00341030000000380c034132824a0144251000c528200c1d03401a442c18001034020b80c004511203a5a00641c80040d51060156501003284809403c0759030340320551861b07001803201d299195500791707505a8400c03d413075844818114803081012072440043c1c0f105650500c0407440f01d41300c10380e81d000c0d200c0002d0201c486000f414840044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 251966061 1250 251964811 251964827
    0x150f090e180a1502042606070f02030c030418050a0902090a0e010b1009151e080405010207060c0203040f0e16030b18040b0a06150828060e06030d020607051207 70
    0x60f01c102c0d4400e109036410750160194201d4424075100d08007660031800d40c40740c03076102d4a00c9150000028061503540c1c1c030b411141e28410503800c0b003e5000812080ca940d074820300040014009200c00240c4000040e00d5150850710010599062035260803000001a40ca000440d03400a820729001b0070b40e091200507081c01800307190720580d881903008241922403030708100d04000f211004034610541c041800e80030b0384c0d210060200c40d06000380b822480b842c41030140b07a216401078041c400050510705a60b59040441d051070801001681c4040740801481c0680c94029000e4210220310360380da41002510707403040c50352980000081c9070316004201039a40320710052000c1c1c400b00c0050b4211f2400d09091080030306c1c20030f49199940e10f083c41d0020a034000c0da9140001e031300392a543c65036699034801c2101442d206402e40e12200c01c0031448840721042c0c6882c01000050034483c03000c1542810f0007003c251500140340134010075034201004004615401000342e649200d1440072040d900d40e2203142c11a000d030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 251967311 1250 251966061 251966063
    0x1d0307092712020601120309030615120c080715140307210b040f060602150612120d0e01150b07060213030f15050606090d1704150f090e180a 62
    0xc15001c030040c0601003442c0040304890381c00e03001c0d2030380c07640c8440c914140ea0404c0480603002c1805480c0400010341d5940c08600e4003c440843c0d400310b151241303449182421034100682d101d0403403a0b4244251801030140500400303070b4028400c4000c00750384001d4a03811846d03480031501d030004400900305c20b01071688120030380c0e003034510700301100c4500c1411801802d40c25941e0380514a40745900180380924031428084d282c01d0f030000c0160039417486113150807101c014440398224602080c4c4001d070003803c20104903d810060b8003140c4503062100392000710b40081d6848000c580c144500348600e03808080f00704080e950802441e03540d411481c2032800103482141d0b04030400d54200c550000c1800100d005030b10781e0030b12440c5440a40402c295179074040d42c00c207565442d40314900b000841e040c0d14081e01b103080e40c188031f6000540750f08001d01d01070800350071990040c01403000c4042c0c00c44100f070344503020040640950074001500340c10030014200804004280d401151420190110303180b500f00801c030112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 251968561 1250 251967311 251967371
    0x1020d1409010612020609101206090e0f161205010b060d020304062306010c0c3303020a0903170d060303050910020a120813211d030709 60
    0x115040d100c129490403021115904a540390103400301c0d50a100500d40d01d00c0704e800501c400c0c106100c01d41045000418002c800040c41103003001c600000035140210b0008010342c03400050614021544141020100b00004c0016003000a07400400d182d070380306080c251403002c0400c804428251a00c00c0c0100004600b0940c040030204803005101040c0d0004e51146210741d0b41400581c1040d201c03906010b4942d086200d1250b00704000501030b5200d10840d06805000c0c4213200c903332681e914640311510b188581d000d403071a6951468107004150244038a03206240c60710b0110700c0e00c000d40100030b00f4481d135400010f21f08140c40303a4554442072040141c49644241e640c0c10001243c0d00c0c41c000d0860307030003a501c1a00800781c0c07805840403503001007040e450041d00100042041c814200b01110452402428224500701e20001c060105444180c140a441c9200310482011601038101401150b0080c1c2c00305201c030000c4016030441d4401243d208110303a41c0d60070110300003481030444c3c112900003200d40220 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 251969811 1250 251968561 251968571
    0x90f04150e0c0a050111100213031e121107051c06021603030606021b09040203031908040c050d050312100b07050c040f050705120a0204230102010c1e050c01020d 71
    0x40800860452040001200c00c9020340750355130f005481c01c01c10300c1c40c414000d401c00c03407924101c4000d54008121b800108240404120744035500c0252003110b21512481c40c4519000f0f100070803030b410002d140072000b0703810314241b03210039031143c50364400c0c16010302c0e4010410802e4809903a802c00c46c10004007580304a0039500c03525000710003c69414040010b8000030f003424800240ca600214542980c0392540400c9259200503c050060b025800f0300100c2e018817013000600c0c10300022010066501c40240d41c2d6a482c0d0030642842d81c9421155004240f00d4a140900c0000054002044580710140c80500d00c00554440e1041d000b590340396404058454070008448041100206614528103400c440821100c8880c900b0041144c0044a1000100754204580c8440484111003190b1083d000c0300094507160b2036070100d292118004490103090400800c0100c850340c2c080c01540a000c080386008032a200741203020807041c042e0b034440041802000210070351000d07020340440792207039500300044c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 251971061 1250 251969811 251969831
    0x31050106030b0a1e090b06040306020f070311060f01090f0b03060c070b150603010b0c010b030d20060402010e060703022103070f0203030403090308030a0f050109020a0f0c02090f0415 80
    0x741080418040c403a4054500104c0c1c1c1d40c0d611080d0301001c0c4a8070031110780e40307424030094000030407000000b03d500540c14040000055498002000d2030600c3c040e4081e02c079a0107103809043e4540000c5180c8141d0800020801d101001e0035000741103501141d004642c1580384000c02009001103008140c05014042c10090707801210801403130310507c0703079003800c5403969002c40000c1c40c851000b0001d940000104010031401660501411100000342c0001540340700d1100083d1401c0c2044a0310360200b4007181010341c155046050002c61503080c00050050743c40e06500003410b1003001d03820b5610070140400c1007000d0510030046440020080305800648810318002c240c0d29800c11202d61000030310350450720407401d2012066900880c0d041d202c0c03d4010703095581e1180c15420040c03042011558a0299039400c003620700a8500038401000c0050b40e4024040c0000e100003041d443d860180010741c00c049005071190b120140e400100100c0040d00398841c3c0c504101d010b92040d43c0f0000b020b00b444207480c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 251972311 1250 251971061 251971067
    0xd05010c020c030c03120913150f06050319020f0f07050307020a120b01050d170a0906030b0406030f02060304050c061b0706090605070b0603030c0f21030631050106 72
    0x900e050126022203001250000c1010f0b5529030840c00e030340c1c15402102c2d0140d103460700040036000040c40103140c00018080903c1d10421035480190003111502200b0041091400c01c0007000301620b00e80c5041e501d1460307c2070042c005080840d03141c6083e16400190a0280c0d50761109943c204400702e07040f5a038419003400c22507902e8000704410380c030881130907400181d0304082804a03030b560b590051400c2e11980c40c10040014146504009640e00b024840042c4090855100102002d1405450f20500c0a00703202c8014100c4512100c0780f4042c92034150240085916217260303501c03460341200d141d07990b55582e10b0014180f07415074172000d40240c800304038a20000f084000070352070345401d00111003210340d9a00b400c803800b500038132600d0701044003000050040349010120540c4400d01074210303807520010540c214a0403840e841c0c1000c5541082d107003007da94176006198411b8408500081c1d003142000b400144044804900320f28260714860030752800300c00494000402150780480030480e940e5202406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 251973561 1250 251972311 251972321
    0x122410080105120102090a1502101803020115061b1505010f18020414100e03191e02180a060b07060504020f090415090206070b01030c1a0f07030813020d0501 69
    0x1d41c41a00c3c0700c505806000c00510a031402500000c04980860b0302d050594802200c80c031381d440c6c0460180b06a401c2c1c1034840360080000312841d00c10b1308102000c2c0e07402c001b406c4641c43d42c8054183d609044040100950041e0031802248181c030740d50010f2805840c0c0b00c650b450455a4040d0190b0400d0000120421103100302402c445400c4001d9a202035100303100d0080303104d18020140135121032062041142040021030310f8400082c01c00710003a200d2040024900101040c9a80000020402a0041041c9c2c0f04101031900440510542d8070318042d8001142c0401d41c2603541450500b800000714048016000500200030440641d640c40038181840c1c0e02800e012503082c1d018490200f000d40040c10f02c1100144650380140c041d091800c014a0204040c01000707030180c1e445441801080d02080300055424003d610591558090515007941c0c80604001ca03076210940400c00e0004140c41d040c007100711241e0310b5161428900d41d558000e00c5110021001d8000b035049510000c020041110540c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 251974811 1250 251973561 251973569
    0x50d050c03062407080c150a0213080106051008070215090c090603061e0601230315010c0503250f030314130206390109171224100801 59
    0x10400e000800d21042d0983c074000080c0503031003072001c00000c004183e03000e0203040e0001010040c2d825405c40f501b031654034628280c9150311401d42c0002c401d8107c08250308020002e0410500a0147c50f00d06400038403440104003088080c042c9660014240c588248401c107100040710403040c280d8100003d00c01c4d03480b43d604640c50b009061800102e00c1915000030400d11843d406018121341e1031800c41c0c00c0005180252985050040808445a180c25007040b04110b0140d402e210076100e02c0e15143c882d0000b44600c0d40241440301020410020540c00f10846030300211044400f222070001d01d1044403003c0030042d018002480c600c40220426515401c807001000d012059051152980901c4055141049000a6201d4000c0000a0024540c0c610f5402c3d046201e0880910040238141500c05058428031000007595491050500304580a20048000d8202d6400305050502c407409441580c0c0c0007078000c0f003e041d0b01c201e08031003001a0000c25211004090f10300c40005402d454041d20003402802 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 251976061 1250 251974811 251974819
    0x10201090506070f2d0c02031606080f01050402070f1b0f0e0f09030307020705090a0b0405040c0e070503070f3f06051c02060f090d0b06010201050f070807050901050d050c0306 77
    0x2242e102400c034004a604e03140840745c0000c420342000009680030742036032104a1701409801410b42c061141207540c0801045680c0fa8140c083c5072026141c400c0c108140c01061190380706204240125110814004d001d07035011101003240c8020041000c01302400d0b50119010560b40c9001144400381c02d0590343c041d001441485007a515002d10140e02c0380821510300c40141e0010408106607d404088250454055130340010b41c1801e81003c82c090b100103c0d800c0c1c81421200700104000350b00000103960000d23072854030b282113080c6024010403001c1e6031144581040404203962034082c07000e401c003811b5102091521000ca801580e50074011003c4044c1400401e03240150010b10760030005c622511502041e40c0c8189551500d90030002c1c20380101c0440c602d501c00a000107815030700c070352440400980c003032404a421f900e050341c002820b441005001c135501c0d40c07d437414010841d40040084c2d8105025042081d114005100100c59030301030032244948160a1009111f04c020401c802076000b880259 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 251977311 1250 251976061 251976077
    0x5130902031b09060d1502030103031e08040b010512010f0e06011a04030215032706041205070b06010e0613090504170406050901120204050303070506240a0311010201090506070f 78
    0x1a0100040d0401c0800d0b490308a201c000c0040e9a600d8520540c402c094442c8407180302c058404031442040ba0003d070822401f0401c1000304d103600e003140030906100b004640c41d181e034041c60541c0d42c0b40740003030042c4241fa000b0300300b06d040d00c002030b20f080d0002200404846000c100000c0114600b5540c2c0da0280704640101904c140c4007031041d607000007110260380e00904103815200c000001030500303a000510030301c5400c406001c09004615007140c2c101c0d58200c15002846142424107004902060a42c0790314140b142c108014400108074456051303110809007054100d0524030000301e0300a00c204402010241300990010039040c01d1a030100d4040c90042c0c900101c600340c03a8800c1d00303d61045008001c0480c00910030900a58072900da41c800c0d07a103407400003508040d610402320745107030004401112680c04c0002000301c4030a0140d00c92440c6292003084009110ba903801160b08050240009030581d0060102e40065034000d411075142130b40e010f41107412600d0101002030807160b088074440c1c0010031003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 251978417 1106 251977311 251977333
    0x25020d050109030212040510080903210108071d1b0f0a02011b09060e041a03070f090c0e0a0b07050f0303070306091103010305070b0d060513090203 65
    0xd000105041a903032402904244032210300d80c03400d0906000c01c100c1c569498141659049860400802c651286208203017180310b5684558000d100620900d003000742c4c42071745a8101d54560041c2ca410310340f2550201035a1840c0082d000c503094261001c145840694003060900c0010340081c5458040361049031541904030251408c0580d6503400c4070101424031240c032060b520402d141c806010388c14803102405008401d52024010355841c00e4a4000244140300d07081700303100050889504a5036032410380810002400b9080075103003801d2002640c1401003080540085008040f51021428030110f03007066001244190740f648110ba00c074000515043c0000c40c0a8102a0b40101e2010b0509030000cac10344511204008410f6410801000414404503042c0b0075a0380c40e580060395945984d07000c8018040340e0b000144c2c42a000010715104001c03580c440000c0900c2982590041907039 = true := by decide +kernel

theorem cover : BRFrame.Cov 251798561 251978417 := by
  have h0 := BRFrame.cov_init 251798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 251798561 ≤ n) (h2 : n < 251978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
