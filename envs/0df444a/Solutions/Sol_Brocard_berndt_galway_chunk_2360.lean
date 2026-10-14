-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2360
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:49.196185+00:00
-- url     : https://prove2.me/submissions/c4bfda56-165d-46e8-a348-1fcdd2702073

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 424280575 ≤ n < 424460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 424281825 1250 424280575 424280579
    0xc0e06091012020708031e06010219081e120a1d060a09020609060a0201240303050307140409022b0507121104090e060a0c0509010906030b03030702060c0303090d0c0c 73
    0xc65141610035803840302c0d40c1c0c0a002c10000150f40402442c0558036400005201c3c1325494480c0c8588540184402c7c11588052080390f10040c0841e0a003105940011074990785145400007003840e10b07880c88000f24007410010743c1a103000ea5908031a800380c21030250a002c40d0742880191032170f079080503820211070f0700118089078008500da8007941c0900c0c40945928103000036080051155000104604d0141c0d440300103101c10714080c0d45018030780003002111706800d6811520010058000102504140000c1c0f41034001a04903640641e0010220741800399030f20080710102c035940c01183d02100710a00e42c0300020444545c105e0040350300c50f02c015a1583c14400d88000440084c1041c6d0340d40e10348050003004080340c0641c06001b41d51550149400034a01410140301a9040700c0c0610080b404002c000d014417941303a80d0000740d0000b1100a8a00410390700340d84000203055120b01000294040e030000354010b04500040061b601c01c4003c1000d8500822004009031400c004405000b00b682600c8070b02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 424283075 1250 424281825 424281827
    0x3030507090e070e0904060e03030c070b0108070b0904020c0106030203120901080109020f0a051c0c05070b06030604120f02071814010e04021305150a030819030b06070b1e01090c0e060910 82
    0x221b900174003901001c1000a22022401d00f1503206803030407600e088000504405014084200b9401000e17840000c1c0080ea203001c100b00b28a010740414030b40b046400250800011100b504543c02658004040e60720455403c1d41544941c0d2160880f80e01103200d007400011084128403d48068031031540d80b40d40340000351001103a41381c0c030805d4050040400740800161807120361098042c12840340d10350a940782d03180c1c10248640074004200c544070b42d0164040000180075401000300c11021400d040107030000c000816401c05a554000d490b8114030702d10342d48082040d5400c40607044604200d501c00030f036241d40144641400845000e500001078001c03a8060342c003143e000301e5000550858941c10070322104000384c5030000d5513000f40e07240c00020454501c3c2c4114940c2c1800c11300340d241410014900003801180c0d039400b5550002c1c00103468000040c0056400d4505841008185035106d80f40c0e60b12004204003c05803010454000740d801c3d021003800d414200c00312164850020980c005610304050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 424284325 1250 424283075 424283089
    0x170601080603210702010e27060d080c1b09010e010e0414011508010605010c021f02010908121f32180f061507110f0d03030507090e070e 60
    0x4064240c42501d411034180c2c295a4510950102c00c3d182542d501c00341e600004068451118101d4490f521285100c5134018000c819009108100a14514507560ba0320018000d100440006444100000b130b030503e01e51000b0a980d0a060034011303031941e014900c00705200300c24a00740030b000060400d4400512880041214055006200d0b10040007208581c520710340c207441908900c0400b0500d110300a010b424005e0083c0f4000c1e0030203191800c0c180c1c47c5a0005004220f070743c4c0e6041e9030b0804418049040900c01c1d086000c9080d040168a55516100c0842061107003048800310082d0002a081041182c4900c011204030350040b01e0a01030920444800c14501c41d010001c03103503072400164020140e1b107404448840b85030707042c04003c12602d480244802d5442c40141100d01c1600540780a4041c1d40091051350461500450140d102d11510700c007144041940050143c0e0082942040c5002c00d545500210701c40d800c4c0740c0d00c0c00812661401500103241d030a88100c0e0104411180c40c0c0f61a08043c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 424285575 1250 424284325 424284331
    0x40308070615080604020102010e0d02100e07090c050c070506191101060e0a15082b171003031e05030106110a0804060306060219050a0609150f0c020c0117060108 71
    0x400080d0030b038188003030301d1042c8200d0f0f405600c00d50000c5003048190740c5c087c420418807550850250500b0040e1910081d104c0c61110340d601c5030140d903805010718001c010425480036048180d02000070f14590100542981c001340380390300380c80c0314407200440c5074140501a100b152442603410141114480030698500714070151080456586180004540d0800503545029000f0160700003808c0402c0d400c031016801c6c95400c0001c183d8061289a08a041d01800d2141940a045485464284010700484800703407541c1c446e651225843d800d00c560302560410324401c030b901c82c0d11000001007134542c0d40c00c42d45100c440c03520f004c140b090004010081c0201a009680c0703804905485403c403055541140b0b68019400101c0001d075030360781c188820b80e01084402141303550446100480f501e00d0b5a81640d42c004600700500035529607200108100a02e0b0001181a15180d8140202410b101a04d4001c00748502414010f00c51304080e4040780d40950741e020305448c00030f080307a007859131440700541c1d050700c001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 424286825 1250 424285575 424285583
    0x80306040b0a090b131506050c070e090c0906030a0f1101020a021504050a0f15030b04320105010504050303040909030e1c0b010b0309030d0e0c100c021801050604030807 74
    0x703200d541116515180281c01400710420005180000c500c180b0007060001990541600d00c1d080720f215040c500e8410100803603d0a28080d5541d0340c140d02c449040149a07408650504500c40c00c4c403040036004120351203014010b1b10661080e0361140708241e90b03000840b0000c0c0111044c1e804c4500031407881102443c90000600440e50006034650110b40c01140e00d02a110b80e0402c0820b042c0803900c2c0954605000308501c1241c0b0305110300300459000c4995030000003000b450f130740d007054003001e44483e0010075075038801120720742d00c8410b50255104a1240d0307404d0700c0c03460020080041010340c06002550b060704c4000e0300440c201400d0162078001844010419018462a281900c8d41781ea100707000c0440321001d032464605c00610134900850407140c1a008003050000501c20451451000805d030340042c0c0b00c800d0080b64007000c0c1c0c20ba450511701101c400319084212400c091116503040804000440e1080d0341c60101d400503c1001d4400303000a006580d4028400c00080010070600ca0141c0349d06402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 424288075 1250 424286825 424286831
    0xc0a0f0f1b0b041e0b0f0901060f030308181c0e030115120b0618040605100302060d020c1006060807050703110109061e0506012f010609051b040503070308030604 71
    0x30a0901946510450210360704610722040000b00622000c04c3d03961800158000002c0c10441e5036103d500c0d03000100060200d01400001410030704003500400024005030742503402e550b4032402c000740855800c41c1d9000304200c4208400060041c00581100c8c2c00c406408400701c0750300041400c403240388a4411548e419900e5121045101c00c008520500a05491012040c0c000141c58094070303000c0300502540c0720700c0f580280903010084c10401242d00a6010800080aa507052000b820a40035500041d40103070004c11649034141455004000d0103181d141160224030070318540509894550003180002909000810f0382c040c003807005440001e109040540034042800344039801c40d000c0e503005552250b00e0300c0c0c00e5201000f041c1507180e00512460002d114a2418400182c03900003075000d40203511064070105903039450a52280322103810301d100240880f030766400390103001d49000c0d6103c2c1420007910401b280c80401e07890841c0c08803040900613105840c03941d2a014020740004106980281e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 424289325 1250 424288075 424288097
    0x1203020c10022109010c08010b070302011b020c120a020a1a1c05010504050a0203041208071803140c0102060f01060e13020304060c09050f0a0b0901030902030a080a03050c0a0f0f 78
    0x86002806055030003004503910f010700c00c1008000c18401034280000350b49406d1484a100d64402c01a6040d03c5492481c0d40d03459506203000c9004060810b540d4564555180d100d17051164081103080c5808401c40c1c0d8004542c11080c8050b8a4174004100258445c1c40180e0400c1407032403691660300422404d03607038141042680b520251589180342094500c46a480006004514062042d2a08004e500c2c03403c60451800e035031201c1110040005020910600c0400503058610416800b500900310284c1d1840035036a91400780c000f550400d07c84007181c091900d498060394400034519114803110400c58440781d1a020080d18044860002183c0268012000c401c4505440c001503004900c280340c0002c511803152401030086c0c440b0303004075108124081050781250780b84602e079000c4d5581c08019a03940c0b001240140c00811019000a4041c0900041c0b0803c0c07081039400b0f020405c80548042c400e42d6030f41ea24100c69403080c071454001107040d200c000c1b54000c2c401d18403000030700381a00b480c21000f4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 424290575 1250 424289325 424289353
    0x7080318121501060203030f0703180b04060b040f1a010e010f03110906030408120c0a0203070215160c030303050a090c120c031704060207050901051c15020a0c02090f01031203020c 79
    0x50b401d800000159000009120b000143c0a00d03036680010546030401c442d0b00c0010030280e01561800c0040e0141c00c108010800703000b0981c0c4418200b40d0024820000040798406801c050425407500a4150801c088107100d654002c2c0500003060130141d490040c2c004245005500601c40151102c503c4103080c420040f140c0c649800071030107140074030491030321001044102da02d12407009002c0c40307182d03d040c000e040e0900d4001056a1000b0380c1120001c5000c0500800d940e0707240184000007005207105101c00c4280a0702455420560f0700a980c00c0c40550f07030b1062281c042c6e90161000400209514408009000c0000d455a02c1d0900c2446004415a030340e45a51000c0f000c0140d146031040b80010307003000219010007a04004010542c0c400301298504400160044c0340070072120400a18505c01d01e04100b0001d110340000e925010301151a02c02c5c5800c000c02400f0010b404034000c900c48400304080c01c3c00049100d04076a4400400342c80004c1c0020100c000e504000d4488015200303c0791400400d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 424291825 1250 424290575 424290613
    0xc090312090f030d2c180603060c0f0f07290709050d05062a070302010203010302121b060f090d0506041b140f300708031812 55
    0x880320321032565103824010040241d40324482d107400b4420380c0039a9684614541000f0280000c1c000803020594900d112050701500c0081c03003030800e42c00002d18a126154024001910f40074407010303000c4902c4c564131402584058401d001e21050980801e1280714003150b02170b8010b00740c092180c415000a0b030041d84190100d421554005161101780300f04000c0d503554807204080c004c0500b140d1040102c001a107407203840d01c5001d80720030500a046106000c107000c40c182103002142c142d001c841c1e0b40304290b00f4024002c0d0403c0c00101d204100c200041e0300e25401c0000c039501410b181c0102003040712400c0c01007080507800003140e0000351405121101c1c00d5903400681d03003038050203040544480c5c0b80c1442e00024410081140440c41c04020310244000121078040c000300c21001c0e1101103402c03003000b000844181c8100c100003040d03003800c0e0658043e840b404038410840401003040781c400c1c0c0d407200c0345142c0364006c00d064400c2c0d044542401050b0303441d003585514060f4001d14290384031080041448004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 424293075 1250 424291825 424291843
    0x1090504050a0f0506040b130510050d0c080c011e08150307090f050903031308090303070b0c0c010c08090d08062709190b060103020a03290102010f021e030c0903 71
    0x901a6a5034040c0c8205059004131a0f00c000111010000600340c80c000522160000d8000600107503a000092080e200e00314112015250041045c1c02e044480e1500e4444040c5034020081c090040440041882d409011281cad1181c0030b03950200c0c010115090201d0b0304180051407c51109101001030956071801c1c006200034011102005c201e03100796500c00b02c19150080e00e4402c495004000700901c500d04090714220865104140320b070754290f038100203440c500603c48090f01c0c211540f0240003554401500038019012030344003d102c50150030340180c841c400101c50808150704503c550080c102d102d01c2001d54884402000c01c805401d40303210b002d10701e15040c0f0769000385c0d11218007400b102003800c004101d40351600c210346800405060361082e600d1100544164181600400c6401d103c5004c2c2d00640180100c80125408111021401d90450035603031500c140954600071180051003424002c940440302c0b01c030f501807058800e01007443e98a5000a10b4405042e000780b1070540d1680d02403144481d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 424294325 1250 424293075 424293091
    0x30901060b0a080103060506040f2f0c0606011d030601063501050420040e0117030a0210020d18080319020301210305040e0f01030b090c09040303150b13030512030405070e060109050405 81
    0x3910a00c82c0c8010411000f03180d001100700c840074860503214cd070001407001c0e409a82840e103071b107241c1da0b25654800c101e0000d03105035505004880001c00d8141e031101daa000151a130511a0300242c40141c01d005a66200c0c3c0301da91111071071800184002d080c650001c0c005558080540d482c148800c15072100142c100d82c01c100359000b0781000420580c0c140d4006035200074080720165152005104029640b00302c640300e80400300303401050100c0d2001e060781c06131003806160303002c2c2071074041c40e03141074410341c1e00840c1d48420740801d01050f020006114802d030f90581e0445400c4030522000c3d40c1040d0700e02c0706035003c120104441000301003114640034042c1030040d10fa10f841c1e5403c0754114648120380e800e0041c404000795000701c45140d00c96a40158540d04150103050000301450f0b842d414403200c40042d00208101c2d64005000100d41041c5a511030480307003d0f00580e84008a04043c9030750900c41920094030782c3c0d00c101d00134801c0411b40c60b9429041201410500c00b004d54400208040e5082110303194 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 424295575 1250 424294325 424294361
    0x1092706020406140f0414010c05010905010506120d0e060f0c0d0905040b010e09060d0c0f06020a0c1401140f16060c0e1504210215030901060b0a080103060506040f 72
    0x20f46500724840801116025000e00d0903d90307045583d85050246104600001a411441a101d030340580d1b003928407240c00c880284000c80711414050702800c4c0a0720b100b401140450501c10f40601c0c0440c002c601088640d803002200380c140010488940c020161032803078810200000104c80f0b008100f41c404084054030340702c03000c6103001c0800088400f4000e27030700d0500c200201c0b55103150762980d007481c2d4860703000c071507902c6000307454204030014a0440d007002c0b02c04600d00c600030a001c0d80000c0d00b02e1100380705405001d4080c0c2ca80e0950a0007c5070840e6643c0400e00c54542c120b4144150800b41c4105180303000361a081403032084e070310000b00c0440003081e560503aa90090000752135116150600b09141900c2407140d0b600a003a840080340b2462203014103a100d031004c0300c0c2480c04001c1c11504000d400078003401c2c45030851281c1650720382c03042c0c1e0070954961a0240000d21070b59840d0940700c2c1c1607044e480b0440c05a113541c0328200684401001c59500c540c7c2c1d50380c03116201109204142d4600c40c018050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 424296825 1250 424295575 424295579
    0x509040b0a0f0e0a15060f020f030c10051012080c031204240c0504140312030f0f0a05130b07020f0a03090f0b04030512070203031b1006060e0108010927060204 70
    0x2006683c0090003000c00c00741440e21440341886104000c0c0200c030020b02c2c20030f450141e0290100c0c00c0a010010100e07940c040021810806000050411050000403008010075103812a020004200d5846406801c05c035921041000c00c04a80c042c1c4a82524030b02a41c0c41c04051940b0002c45200440c2c0031a0803c1e9244030009a082901d0384641416031300400400440c0c00d20100609075020b00d11404410000f0f1002c1d143c0d00c1d440c24400d846039403900070703032107078a0b400c10014000792900c0c100c9544120320761810000d2075916281c00b41c14008c45e607102c41c000c0355a03087d490302c807030441d0000e0820f01036100380140415030070703420072103521000d00a5603100409400d22040c4491900c00340d00031038030030b0760a01041c0041080480c2c8000088007504540381c3e80d00e51840401d065006149924100803807010300c0021804000c41c2031102e541c4103280030001540c40c2c000569100019141e200d0000303141a0041c0710020907036100c208010615481c2d1300451011155040c100c0924100450300c1503004541 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 424298075 1250 424296825 424296839
    0x7050a050106180902010804230106090b18041101051321050712021507030315060302090307090627020d2903060106140d020d090f150b0f010509040b0a0f 68
    0xc0321100e43c0000ca0b040c0828566500028144c1d00041c00203024100c1001048100b04020b5040b8a0f00618001c0207100403966100c52074028400004100d001e17111024940d0030301c80306150766910030380d0720a1048484c07840704c500446203a0044524041090342d1802d0208180700c03e015158500801d0108074540c2040b1442e225090041c2c86e40b0070b003031034004210200010fa50341c00c443d5141c242070005440d00c5010a04040b405060401926201103105c0f0601060f8294950014418140158112101c156a541d070703010807a085403003181d005011812000d1011455110a1801445000d2001d41000c503483c140c40200e8040705541482e00000c100c200141c5503c0e1045221440c0701140900b903150314164018244034200040b01d01e400d48000f03a15410309409a040c1c8400060444c810810b40c08689090b1100200203c0241c401c03103800c01d40e8a078911044c4c0031341c1210382d10180c600040c0c1d8841d50015191a0800501c00764499205c440000711619040d00300701c020844d0a40d407030083d13894012 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 424299325 1250 424298075 424298099
    0x909010606050a0804233906071109010303080403022b0e0d02030d030b15030903070b1003051e0613050c0d02030106050d0503131e06080c07120305070e01030b0a030b0c07050a050106 80
    0x300c2003105481c454a0946040d00b030740060001c854040d1816903580d0001e01e0704180303000c214007034654805c080bc8008418954000d050511440c829022200710401c4090283c2c18903807102da000d24011340100e0b03c403052600c42d010707d540f69000689150391400490703000a050641851041e80025500d0700c001c507442c81c000030368032203051003952090300d503083c00d041c416100d1040c440d001d408510bc11000c030301044c02904810000719000404c1c0c900c0440900d03280004c0528001060800707110b0f001c04200d10800d81030f480341c10294408000c24001c40200d05220180c1240c6400ba039065503a0b0b03400190503210000c4a007031040c03040d0b01465903028007203045a00185140c1140d147d000c0030400b0b18980000020088054581138281808155203402e1410558807401c1001000c1401111030000101d425030055070150180f61035132104440b201004504540034285015404040c2101c2000482ea42140304e40c2c0085910030307000d00d083c4640d00ca5500c0c00023009000c603556999080b08102000105c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 424300575 1250 424299325 424299373
    0x10e1c0c0203070501030e0f01060b0712030b01020604060c020f01020f0c06390d022701020d020a170f070c0e010b09030c0405220b060909010606050a080423 69
    0x10804262040068000c03d96444050080c903041c1a0340e8819011005400c001d03050320a0138802c024000c998603070f101e8040a8100e400100c8003024044158000a80203014108488a041c1d009050594a81d03d409010308031807191401580a00748021441400c05e00040054028010080c0d680d520242c0c601440c03ca40104004148109201c040c60030000341100d8258545010f0803101300c5c0a42c01034075010901c144400c0322483e91000034551018441d200030100b03100d207c800b001007818401001aa00c81c42070301c03044801608210170120000700e0701000303160389483d000030103810411401850126a41b001900ba200081d01d030f40200300c00c5090f18003103809041380400207803c0082d1030001c05c2e681d941c10002076110b03e80700c0c0300040304402007400008075001121030070200100e940c05c055441140c19180e0500807580040000d655410500588044400700da42d030b1031074228007800458070702d04040c00448494414603003507660200c810110065960009003d08000840201c1e5003240820749 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 424301825 1250 424300575 424300577
    0x1218010c05091f020601060302070317010e04111507022115090115051806220f05010801150302150c0304060e19050f04020d0b04090b0115031a0f03030705010e1c 71
    0x10f98807030151aa404070b049811104941000368039258240380c01c0d40c4040f40d0301c84480505014400003c0d8103107642c130300300d400b40d8003800741403005242c80800d010310340c000c3e60360544010760f013040f0038001428141c11040241c41d060410042c1d19041c0040d40342080c142c949605004060481407056000c020700c0355080d8058105d100079911481e141c08114481040c00008100c3c540300c0300090503545840c07203410a02540742c08100e04032580d4500354402041ca8031004540107207054008122004140300b5410910a0034058100305c0c1d20310750811074001041c00302400088000d01001c0a0381d007007003001d880a098036469000d0310b0074101041c440e100b0460341d03d061312103210700030030403030f945680300d810020718015071b400f60355510017002d034401400c0d8440c0f07c0b0760440e281868041c14008260b480394103803152815100c80d102c8480c84210155082c0300080700ca080740c103d8503800c4c0c0b40740c50b0000a000c170304080c00317503400d0241c9501d03181d00f103e80001f02c590003900402d10400d64101020070001003c1c141d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 424303075 1250 424301825 424301869
    0x602010b010f270602010f11070f0602030c0d09050606011b121d0d05030c071e05010e010e210f010c081302030312011202150c031218010c0509 63
    0x40400001c00c000c08541c181801c1c40032040311003200107803c0805041c8140141680e10101350b0f00d410080c000c0a07209440201d032413800d00a6413006840710704442c009504140d409500c80b245880e84030081d0300c090070f180512002080a07421208072405003104160052029104038074001001500032460003140008040745024600c0001d05e600800001700c407035900d02681d02c0355507a408854040c0c2e59100d0203500c0715210032a040cc0040020007404195242e10a0b00d03180766454500003a81080d880e514446000c58140510265216078569a045d450501d8504058043d0b100483e01000101400d4208202941c0f450300814608024223001610180001c100c00490032200502c01e01016014406141e4041008810365a040080c1c49801c03981d84040c0c000b65035281103861410344100822406100301c91620003011b800007060b20284207598000c0c503d004d400c5135261003544001032020000174500c1c491450085801d20901d07054641c0340e250310f6a00c1c20404c00300009100464500c1002c2c5107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 424304325 1250 424303075 424303091
    0x13060311121513240515070302160806161404091503080a0504060806030c090f040f061104080c0307120b100815010512060c041a091003050709060201 66
    0x150410480718400c1590088039803603100d10509001203400d0040403540981d10450a5108061a5210752070f182ca1410345400e01c520078054552240142c0c0c82825440602010030031070f405070050040c0f41d01842841500c00a02890140c52580001c07a001606aa4031600c10001903400b02c0310703103903c241d4217802e01da801046260950025441240180c0c0703407481d1224413207005500c500c400c0d400510790100ea000c3d01c50a000d00c0c01231254100d03105020025103000701085003818085074130a24510040d0103c0002ea80c4d06a460038030000c05082100c1e020f040d5011440071030042e200f200101c1080007025903032980362024807807400d0006d40d10709100703810901080050300202d015000c4025400b115000045d910f85000d40c007000001e0380420002e00402071240c0e405410b29580d83e05071242102c02e1041480612805681c403242102c0d1190b005900b00400d101c5030740301c3c0c940785003880305404d84e0914203109240070910741200280d42c04042511102481100e5800200c00e9024090701e10007045401c1b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 424305575 1250 424304325 424304351
    0x207050c0a050f060c030d02030a020a0f08010b030c2a060105040b0118141306240c110f0a03080c010b0103051602061f030501090b012405042c0c130603 67
    0x3078611100d130320502c07000881140f88582801038071840900003000315101c0c03500380c0380107010b580400300c1a000206400402850180074003211810b90303292401c0941103603926850001c041d07200c00f9034054600c2d04071144004c031410410380a0641c8902e9009480d440d413400c414882501d03070004056042c01040000b100003060003010039821a4000540082604144004100240e0304e124581041608001000c10b0344109014603812681200e60000c005c0d40d1050811200f01c1c0b07040308005c00a1031001c0c540e4020f80f43c21b4840000c4240001d01c030324011603aa40d5260119070100f40003000c965101c2a498016681500c11f084e0f126500c55480030030341c0703029030b8003c0d142d400003440202001003400d100302c48294094405000742d9800b1000304020155810440b0b51010300344a81880b020700c4a020a061400c90300c0c41034000401501c0b41170038242850f08041d10404000705094080035030b60403030000e400d81884c00500820500840d00c0d5100c40d42148407103400c003603412050a0608081d4003c10f1030b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 424306825 1250 424305575 424305589
    0x9051605070f080721020705120d0807091d0603070f05010c0b040317040302030309061501091a0c030a051c0219030e0f0d031d0109020a060c05010b0d060207050c0a05 73
    0x119030040701c45034030300d50718900f5164034040d213400904001d00d51807a11500e520885251181094560210f03031100e907072502080001c0700300e03100310300e52508024a40d03807000303001d0f540407900000a030500364000c41d1230740d2038140c880351034803401c001c8420041e05100302410144407040c09042444081d00d111400c1000283c042d01004e45c0c0101414003040020301414440c84000041d12401c0d14100028106800c0003560391b00b0031340b9046010300922001c5100e0000084840407185010b1712010101e5150807841c00c5046401803d1200d003840400c058ac0c6400402e00c010000c404440d180d56485074040c100c82100c01150b0640301700040d1041204000403001d20220f02c04080162801184100140541c01c2c2001c80b400010910392117805088211079800d50001c68203d040c0d1a00c2c42801810115010301b80c81d507500019401c103050400610281c0c0c071a8201161060180d4008164000c5c50008103010780c0c0142c0041d52080da0101d6600c04000091049590004d41203441340c00403400d007000a204 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 424308075 1250 424306825 424306837
    0x11070203060f0a0e01021803010506012f01091415090d020c040b0f030607050417010b060d1d1b04050108030309070b0d1e09020301060b0a020d030209010c02030a060609051605 77
    0x1401c2d90300c005403203807040e42c121a01c00b52130f40780207540306d10003000000380707559424501a200b54200000206c840d403081da4851801d615202c19201c0500441414800368200c2440511241d507c0c0c01000000c211050074560787d1140741b5000704183e0320711520f0b43c00c10303150140607100d950300158940452140e00189035007204030b00301d50004014410034002440c0710401d82e2102e403d4042d01c0200100f07160007601902c100e8260850703014660382c41407400c81c2226240034001e40e2248080c02669100742d460341c09404021000072244541c803a1080341c440c600001481c001c0548009007900c614241010702805006081c060001c5d030540c2480401e09407203002c83d0013010200e41000c0703914015403040b40c0007004400340c81505020840d00503154640505401c100503070081d030171b014002440341d40c80400c07100c0c0320725a80d001d840700344510141240694032084004c0d0400501c0e68080c40940d406100301e0480318412100016128500320740401960b41c000d108454058540304050171440e003180840318 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 424309325 1250 424308075 424308091
    0x9013b151213060504050c0405010501091a0306240301083a02011104060c051504020105030a0b0d21020607020708030412051006080a06061406070f110907050d1107020306 75
    0x115079030324540c4900400326402c2d4041d19550401080c40f06025000c40c00d86a0390350250340c1406943e172200019142c881c4184580d003000c0701c00e04900c0f40c200c140f400240d6040ba400400c408400c0c44a005444da000111b81c6580e01d8981000004104003a81040945c2c1011481e0040030b9103296091140bc20000300e0504541000d000c1049814100b03100394809240759440b6800c403a21a512483d00a10960514008a40900c2005503c4010240703442406100765416500c00e0300d55520401740c0f101400c0c41014003a0802c0300c01d100200000c441c817524165200402000444907080c0b804001c2ca41301c00940410b0554001e5001800303110804411241907074401209160649400d1914900c3c140e4540d02044030b00340b45c0381001c5040c2c0c9010401020184c0102d00501110391074a07a015034080950200c1580580304020120026a10b5031150034218020520180341c0c0014401040c0780c8181103c41340002040040d02001c0340401d0b124030303015000800d40d0541403c201d070f1302281d502c00001d84190 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 424310575 1250 424309325 424309357
    0x8130617070c02030a0b010602240f01050d1104020304082505101a1e03070e090604031d040c2001110304030309050f1c0305090109110609013b15 64
    0x22003992010460035005c0c6501014184042da9200e600079107074103c0340c004030380d000d000610044c500000105501c3c01010a501c1008483c1d1912041003007030710010204540176108128540c2c0d5998030307880075520075406000c0c1103a850a01d0715240748920000b0805c601304148110705100440c2c80010517108030b0105071800a1001c042841002810010030070166119804207c01c82d0781115420709018020401d03021228080d4842030601c410150031122103285034090400503010901c5291002e07070040b03154007818101e1420002040540310340b400607a0216910005401c0090748507904000010080802003010207642000740311144006040a401c0640314001c41052210520140e912164044d046407005038101100400e180c0303003031600c14042403500000644481c1e060140790911680701071000e00414500d800c02090380c018004145c10010240c01d48d90441c0b000840c481c03100b103010310301c1c280035100300030001c507484844040540c000ca50744040ca181c140403120940743c03501902652a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 424311825 1250 424310575 424310597
    0xa090312090f0f051f0e060a03060e1609090905060406020f0c061501091215090302071e090608010b0109150c02131409060903070308060307030206070813061707 71
    0x45841c0388060700002c019a0420000081c0d41d03000000c018210745058a908400588403003051901601240249000c103040700911545881e1400c01440190300e1420300090160f207403194141c03070541c04c440001800c5a4849000d075001d400c90040001491241300501403010320396906600c0c3e140140000781071a4000c503810f1010500728064416000141e001c40d13a0034074104000e4051804141c2900d4080ba107104008903504070308290202c1096008103c0005110501850030018021400281d00718051018045a81066191028568a0103181d0707500303c01e00b0f01114108640c0241d0112000c0da140281140d1540d802039686812188807006262550740d1082c000c0c0c88804401100941c0314041150504540015521042c80158050042030041d502c050070240d5070581074900000070307131082c41424006440780900c00d500c03607800381c292100340345da0740d004c00c40941040c14101d03020500811014034000201d603410005205515104000c48400c2081840d2000301620390000c100c402241 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 424313075 1250 424311825 424311827
    0xa1505160f0b0423030f07030e2b051c080103080d0906090308040b18100903110f0106181104060509031f020301090c030516111519050c0a090312 64
    0x605090b00030b00488824036203450544820000110000440300004080360015580002901c002044103c44549011441c0d1015030701e841913183c42d9a03020004010040c105100320b00b07401c0000d484241c40b2524003416140c0a402c5c01c030585201c1802e180b40c4d03501100e00b541e001e0f0007141100d8100c0c00003030340c40701118000d0780074100c00000070b00074505003580d0400b0154003034a0707a81b2950040c0c4d00315a00e9120440045003080a0f10724450050340507001e0400380c20803940c00700c100d6600c00d040c01c0843c0b213a03408039941465000e12041d00e080e551000e040094080040b40c008450040720070400c032014503009481c07200d0145001d98010844040380003402d5071030410450b003c0000000303540411406116001c000380d803090054010041c1808041906075001c1d008260051104411100d02c0041d00e880885000003040c14955007445a503003000b449030f41d001038850127510741c080742e1300d40d40000040b004195180a841c0300c1d0711403403c019000605502040c0642960361041c00d0091848411074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 424314325 1250 424313075 424313093
    0x10b2d060c070f030212010c12020306180112142b03180c0302040c0207050a0510090b030a06060207060c02033c06061e10081b07110a150516 62
    0xd0103842e2080070400314500d280c0e55904401c9034400c446940348003419401c003500360b07489604840085444c00a00030b07140c0700c5540240d5841000581082c820b101e07207000310a4040001c0c0d024090440411400406021402e2145d80c4961082c0c0c0080ca2410f401d52480c01d02c1d02040c501c3c041040044440010075039203e83c02209001e00100c81e44510900c1c607017481c2c5e00d1120b10b44002c9101c4d07860400359500903030000c00c80000b141c500800c50222035241c0030030700000030180f680c0401004a0710303c1c0030641580307030000787d4020101300700f001852600700354000e8035210068000ba000d0140d407102c000016600017a001e80c1c4902c50081842e00311b190004d03000c0340b02e0000d42c0145464a0415454541e000000072642d128010480e200100301d460010141c03400c0b48106035180d080703c0b40105035900d96000300301d09504442c079030124800c04859410002820781041d517003100d54203d2500368140c035160080c1900b0180c80d07402600c50f000360412401401341d10641400f40c801c07840c02801c078414480200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 424315575 1250 424314325 424314337
    0x90a270207050a110d170d0c0801080322050406120c050904120f02011b02030a02060f09120a09090504060b09070f020304060c0c030215030709060908150402060c1c02010b2d06 77
    0x201b003ca0000fa20000040302c60b0300b0092102200e14035080c640d4070304910442c4600c0c122034080c4081c0d45440800341d1080c02407041c1c04010403504100c04000102900c483c0f0a4400170308002d680e01c581c4800521b002450100564071013403080c3c0542081c000810240154240e48080600308514100c10000069000d00941d0000d40502c2446c43c8400b40c4481d004402403d406c02c0707030307070959500d581d40c80e4840208880650700701c4010780c00002401003003003245006001d0110941014030b8100c0e07a0f00300e00015a07008880031540e2a80b40c50380301045003032101c6640d8122101c1d050010740e140c10703044000d64a006078840c11742041141003101040c00314842c000780146070041c02d038104514a500206001b64420744d941800150395410001e4014450400c42d42030b645824041c0c203c032503032107000f41a8554064000d982c842070800180a42a400f0065101c1240002d40c0000002180100c00303421074403110703d158040c1014104188140740074000c0e00308038100c4450010354070b4005002041190140d2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 424316825 1250 424315575 424315583
    0x20918010b1c0b131d010905030304020613090c03020a08061e130f051510050a0c03120608010c02160501110a23240115050d0b06090a270207050a110d 66
    0x11425003104c0754203402c403a00d8800c0d4440d034000030201d021034250072100a01c201a2080d04244080b800501d030010003401c01919403e0440d030142d44444003030080b41c220400310710100350b0010300d9050903900304038080c0d88090215800c9480418840081a039100d03440d9805200d90214941d2284010b806c0e0700c0f40c148860900c100304210315007904070112001901081c02d1042068840d070b040d000c0d200d10f08881415a2a580700d220340c0c911550162418401902c890740e86c0c5455210100f8507407130910980c4106c00c02031707004250b11103c1d003000a841031560f4000310b042116400c503210300304000140003d40325078031035104000e6130380010142c550701d514829501c80d00d00031070103c0b211007034207070500341c01883c0c1070b20000c45580d90f200314214028000200d00300110340c05101c2000301c048280d02c424400e10010f00214170305400a0300148a6a000e40c00a44007010041103040c41c005544988402110401030210324199154075040d1f81c4070f4000400030010280c2c004000304544401c2e440e0b8044941c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 424318075 1250 424316825 424316839
    0x50108070e030f12070c05060403050a061808030702150c041505030c1b06041403030402100309110a0b0a091502030906180a03030801090b0d0b060f1f0201020918010b1c0b 75
    0x428500101300c0d9101240075200d0700326540307000c2a60320300001110112a4004018260f01d80550784081c040d00c4624400d9800c5243c52484030003143c141d0004510841503540900804c2c00440790000207000054070407241c40d00d0602050061450052000c40f404403135003407403500d9a955040285440c400c0c1040c3c442e100c0d07030702c2000041c294070001c1d5590003644141d400070b040d00d054420035680d0303000c00c9401a40c06400490f1003511030740290b03c07e180c054050b0b2a0840e8411602c00441c04100440e4004072140d43d0000d001000c1c15400300e182d4014003800041840803001802c00290f890007a40e481e14172981000440d17860341d0302c01200418582c0c4c4083c01c0503101350398a090160141d031003446001d21090810b140e0f0340007031401e0105901c03107a0f48801503190b191110b4084c4104207411603411030704684591129803a0349003003600d4480000c10303030780003607610400c1d00d0622011000500e40c20010294040043c400442c100341540d500e0041e05250b1007200010010003005042504844d40c0c00040b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 424319325 1250 424318075 424318093
    0x7050a030905160b040f08030a1e0215190c0212041509090903090906060c050d030509010e01060806071b050607050306060d1b080105060708030606090307030b010f031b050108070e030f 81
    0x1002c10140049175081024406c0d2a40d554145544034481d1510a80009001000741d45142003ca010032a80c400380340304031290034000c21140000c48405890480d081080102202104082d41c082c0040301c14441c4060055190a50801c0805d4012802444030022003060203852061041d030000300100303803141003400010303510f044c0903082c2549800f80503455810540d01050a130300564240d044644c0c0030000b0540001c0d054000c0f001018003501001941d522420300d00d00e050024001d07200a4030390a000f40407582450b10000d828020740d00d80a1442e00780b00420300d0003152000c00c0f040c1d844905420156502d68504000521902c80c03200b40020a61600700c242c00c8a600b061340c041240710003915007941690300e030b100b0000140100c41c03004016030780400000d00a400c044003d00322002002d0200d03200542c40c1d90b070f144c0c4285000d800030900701c1c1d5405400c2040c00b803404c1c0380521003504030764802400d170b0038080000c00c0490b00801060500c0310300130020f01a910b0800c5038807580194641919444c007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 424320575 1250 424319325 424319339
    0x10c0623010f08070f030201050d1e09150c08071706032b0305060f0a180603140609010b040c0e0f03072318060a0501140906040902120a0507050a03090516 68
    0x842c040c00b03181507504c14010046400104007110b034081e250161100b90600c514011188003901102010300b50b201e10007890102c8119082c014004450310030811112202840200413085580d0800240200003200092001d4aa0420020000801a03103c1a00540d13505004640340c65041c81c15041c1240121040151a0328410300c0000082d01ea5501405180c44180030051741011030b017103143d400300360244d040000c2d0403000042c1412a00c900300c042401c0c1d680c2d8945060380c16144000303035610382156003040442c00c000e101d40080060226020464400003d6008080c581400c030454041d0380c00da5000305481c0d50410103080185050080351112255100c2c3c1000c4100b050000240510141405060035000380184140300c2c0d03034098211000189054011609004410050300400d20700300803074041501d501c0000e00c003500700103c0159031003135010880d0b600c0c141e0041040b804145084180a901c03070f070100c21100301e12890715000c50116818100141040704802224112102e500000500340c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 424321825 1250 424320575 424320599
    0x71e05010e030d0c1e1e0201180308090d144005030c0a0b030c07022106060f030610031506091d060c0c0a02010f030b03011a0906010e010c062301 64
    0x9511079031140058004210303d44460413150100d517002c103600d610004280c10048142c1c1032080a03a2001180b4101071984101e00ea40c51100281c0001f000001000281d00c020007204828126600e804e500d60f500201405e1460701424200050352003101c0704103031a508001c0c405441500c0c2c0c00c0305240b0405980f040e2001c2d124100e03c1094000d01510340c640d5070741c3c07920000c10030803204085492407440d0f44856a0743c405074400482260321035a20b00d020b00d1081d548505441403040450002c2ca9242050810005c0d030041d01c040da548280e0041d810409903060b500c903410101c07039201a06080070061012840040c002d0f80c0c01c40c950b024500185512a4a1a4000300d00c0002065003039403102c0c2c403040d008420910a054451515a0200c114440154070034203d000000e1658a4001910591140087e094450983c07100c07901c00710b0301214040d149000c000458000d13800342403c42c006040400080c0c8280f034a5000640707c03698941504500f441860303506014440c0305207121103150f84a030340c0342c408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 424323075 1250 424321825 424321841
    0xa09020a0501050c03090d02010c1703010503070b04080a1209080f010f050c07033e0a050d0201200706060e0c190305040305070227010b0d05060402071e05010e030d 72
    0x100310000d0300005025401401141c0d007039075201001d1440e001303800c0c060211080b00f0a4080b030401922581c0240401c000010481000e1104408944c0d43c0d4540002c052805086410140720002d0030001080340060000321500003d0780551800307502d0b8904442a58500c0556104041d40d0044904288040606520a05001074003140402c000c4c1c0324100d102c1864012101c0040104031440721840c180000101e443e001c031180c0711103c0c0b201c2001c1c200184039005a11808a205500865292003001010b00c0001e44e40d0312948001c00c0365403071820350581070910081d1000c1403920006583d605000c8243c000308060310086590f0313180c6e401c0c0514880b10703d40c041207400d21501c03460341034202c0312842405072a00031501076440c281440b407141c0800a0420b5048040c50036200c3d1140c48100d089070b42d404c0d240c002c0c0a901c0c030041d201c4441a10302400d070750f8010040361084e4070400443c0005081960071180c400c241407a00c081d203030103034034000e03004018841c09a249440049224411050b4580100d02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 424324325 1250 424323075 424323079
    0x717010603021503270f0a0b070e090f0a0c0c050a1a130b0402042f09030d0e03060a11040b040b1902011e02130f03050a0302060f1005010c03090504050a0902 69
    0x200f60f0f445491a1205804140d440c045600403601c101c1c1904104000303640380c01c113544030590f0101541c85100500d4151005801c541c005252801c021031039400c03001038183d080d819540e211603490060038807000c000b00140b034900d8107a030b6030241070103040c4640c6c000c0802c42d40c0181161600350090800303601d83c10000440c04521408500001e45035600303031001560240c1d201c00ca80b1500d48444d82080060100015041d5016a0890411041d8814030341c4001c40803049614090ba51407042091500f01001d00410340c0070b003c0004103800858800003082c503808902103100042040c3c09c03884041081c032440d486290100c602190128600700e0700300c02041c160310503d904084001c0003c2090b403e99510340006080359a444c0130260b20041ea9800400d00b000f4990500200c6540307604032240350000d81c2c2c000352020b0f0f1240d001902095010400a5041411040c285c2000e04d01140d00101f090402d001c2c0b0350400c921020640c080600400d5100060003008206000500d05100001e00401c04400180c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 424325575 1250 424324325 424324339
    0x1e09040501020405190803030106140f0a0306030501050703060e0f0405030712050a091d04150b150702030105060a050a181503050f0105070806060d09050304050904080c01140720071701060302 84
    0x40050040b44003d5170444400801641c21a8a866419102480000d161a6011100704501c0d580b940c0320900402c003014090310005816030642c207022b0708485000700050181850804148035409000340d196038070001c9601d020610360b0b501e1a120b400c6004609000341040c51108400c0411608003015101c4034050f40d880c0340e0107030380c6c0d010103464480c0c1d400d105100b8810b00707002103000319881b171030fa002e10605080030200d006503002c030120b00c6040062941260b11900071440307008500d401c1c05042d400130011140c0701102801c0c000040c0d502d000a02c1680f824412143e100c80c0151450b411034806040221502c9180d40d56a0800301c2c5c0310011b100620b507581d442d017000a0a000e0145580074000c4001409032418041b4104181008000c072020985192000f4003000456075a40721415204900c00c0310034540f01c40225144c0b5081d01c08013528114a10400000c00c0070080c4c2c03046042d005035451440140380040329181c01420074840d5009824007201041c1d1204400805400c1001183d109032002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 424326825 1250 424325575 424325599
    0xf080a0e0a0618050a23070e060609010207030b1504110403030e0603070c21080f010b09060c010e0604060212070e010e1e0a08030c0c040203060f01080c2203020406231e09040501020405 81
    0x200c0d00c50003203008d040300000c1d001c4041441c2d81041005008a0101030040340d01e81134403a240c0c1c001c0d03084101c1e81e04034046a85120502182081d002d120f10b104000111281050f007160ba01400c45d031540704100780142000300000d00d226202d503140d00c2a0981009454541604a900c0b50b01d03000e2a0031840c00c0814072240200d000d42d05100020740c12900e000d41c90504164282c410032000e070f800f10400b00555929114a214205420f000340740c0200d04c6401d006a95100c2002c109583c418000c24034001e02c140c0440341c0d4010390f00a110b02030f009401700e0fa82c01e00d503404010448504c4110a8403681c01010030340010031040320000007892a03ea5450490b890741c1901e030100800da00c030072236090781c0040011006000e40c0d4033804040f0f8110003540100360601411000c082c01c002c445104544d080c90320035108000b07509082c80f541010b881c043c801c10b60201008000140003000d481e1200e4042d400d056220103800324480c44c82c41c40701f000240340b600c180c1081c3c24210b000c1e401070300485110300c0341c103088 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 424328075 1250 424326825 424326893
    0xe072c0a02030601140a0f0f05040f0b031e01030b010b070f05030a081504091a0406111602040b042906090d1505090303090607050d0b0a060f080a0e0a0618050a 70
    0x686d0301c0360718a5036982070056000d2804540c01608421808280903046c000402c20600c11030210010308030041c100c03512460b00e0000c0c0b400d0300440360122100c6842400044c0040345284e48204e0540b0002e015255581c040d03481c008941600340900641756010104481c0c1d1450740c000c603c02d000701800c4980701d80030b145d00c908200454000500040610740c1c00c44007031003482c045488407684a40200c600044000e00c0c11000c84556104103080b0f003c8c4508441c0403411480c007403046004841065404108489604013406030400380b4440e07a0302c01001054001c01983d80301000c072128107001610060034050246003a1100d07010601e01e15005508240000c0c0800c007000041d01d11401c4580c004190b01c0e2580301050724190321065a40c00e8003a00c614520b00d1a8654292031402030403155510141800600001080050060412100c0da41890159403080e031002500e4442c1580040340055007000604500348d840c118007170002c0180c0181c0c0c580401b800b0428800c1c0c40c618500a42c2100700b0404000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 424329325 1250 424328075 424328077
    0x160e1807060c0303090203150c0a030606020d050405060d060803040f18020f3f07020c0a0308040501050c0c0a090e0d02120315011803060b0102100e072c0a0203060114 73
    0x3a400060504a002d90110384a07402c2810007900180646001050380f0001d04c5581804486d240d1410303100007142010b031941445800d00030f11032407014042c0054003c000600303e102d2445001d200314004075644100030300541c0318a00400000084070b90740c645d140c41018088680d44907100590520390030884100c00503008a5020411100c40149820b55100b20006101007005e0165070ba04c040f04440403206d2400c00c48450013050a54483d8110310b88072800030310303180500a206000b025840c0040000421120039101a00c2c82402c0c1191a403a42c081d4480c5000340d41c61416070702c00240350002403203a400794005480d2046450030380780304000612050342e0303904000c801c01c0c4d2071180030000100440c0c1d103400f403c400c8910524040e400307202c6030103030030004842a401c282e44165440910a0b01581c04000c002c03130200c6502018021550500090398440320244942074060382144030304482d0003005107c0071011041801c0215103402d20341802c00003074104035030490102e040d00d1860107801c0c40d204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 424330575 1250 424329325 424329329
    0x518070902041415120108011b0f0c02040e15040f021906080a05040c050603070908071d181905030a031401050919020f0a020c0a09060305120a02160e1807 68
    0x4400c040d5140c0d01181800800c44c0710000c1144529003c0c8040d00702d0080e4210180d000708840b20020601440512443c05c0d141100741200c0305000c04080c8034001c142e04144000da4403501107500251801c2241c1e0007908003484210418074290010080004004680b031107016640c0c000d540042c24900c0320a40361043c800f550140201040d40000000d4085500f508404d9115120b07445103051a40d0310004180c0e544c1003a1a400080350188400f0b105d007040030001c240007044c080c54000b01d91074003200d51400401006e010500d80f20341d041d03c02000440e0400c200d1800c40710b81340c0c10750080c08541c01d00c2c070344030741110400100003070415043c204219524126641600c01c010303c004029103801e08039904101c62900311425103602400160700c94000c500140411a0003900508010703003032002008480c003819000040d041380303407000c28008628009900f990b4080c4590110380d0f20703a119007050b0314118102400f0f003040c08a1183c0814104100400540290411750140020078003d01080b41c03510514 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 424331825 1250 424330575 424330589
    0x10204330315150309020a03081207021c0804050c0604060903060b030303100902090f041a0a05031c1107050d2001031407051605070f1a04081203040510051807090204 73
    0x25905205260119402200c04843c1381800241d0920590100325000c48a0f401074860380700100e03000080106044034240d014051744003520070305510418562501c540d800098003084222400501000b00c1080790305c10320071004081030749442d40c4000041450317116010484000d03042c0003060b04c05040002c1982c1c090004d016841c242c007030502d09181c009400a402e0b0303d5015100011604040c0c40b01d11401041410700c0500604103e01d0314140410480240e1003180268000040d00c030074a10b60006041440d9560304c0e1a8005a02c1943d49500e07042041e00100e6101c002c407000350b4108101c84903460404100c800c8000d5200344030000540031154142d41044500b60500c0000c6c004a103d84010b0001d0401403654020407007194807010302d8071400b070b00484d0310492910790030b100303840100c03841c0388038401d11240c041e26141c1020307201a01c4485171b0401500b84000400494108001444a202c0c54540420b0400841c034044031800c003224004111811203005290010507049014022a0143c52007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 424333075 1250 424331825 424331861
    0x424020105090c0907023901020304050d060b030a05010e101805070620011404051207110904030c080c012c121308030705010c1805130903020102043303 67
    0x70504c003903041d00034070050840c02001e01c0c000c810744509051114030440c909551848001040b6a8070011041605150643d803042c002003200b56142c0044e081110391002012034400c1500340070074600a0040701c001d1555081541905c0f00000000300c0d0122403060703803014020214040100150060308600c058400d0b0003404d0144180d41c010b00710010400440706031b80c80569034028505007180c0c01c030400502c03004007940910052200405c440d0710003126100841e482e08610780c1e1128080703a40340301c0c0c05008002c241c00240074103000c0d5400741d0001e90050315403560352400c81405c90080c5140c09000072030200c0030090088100180003101030341140e000c0107020350421019401820f812040000354031404030301d00400c60000c24405080c41e640305000109a00340c02a00107800400001034008501b5000c1004004607074484140c803903c040105800101c0700c82c141000c034003911607a00071400e00124500d440014000d4040c1e0000d04642c1d6100e000000101c00038110141e501150140422841c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 424334325 1250 424333075 424333093
    0x130902070b0a0612020f0a150903050f0c280f0b130602010507050904090809060a23120103021e03240a022a1609050403030b01090e1902040b042402010509 68
    0x2000341c00b000061b01c2c01003141c82c1140c0c0d0344014035010b10318452880c0014204500070400c00c90204203201c0105503510141c000c1280c80030120b9a000b00d082129a440e00c14400803244400d04032100102506d004100c800c0c1c1f0799151000c6ca84e00e5407184d541810482510031000074980d01c10701c03419000300d48590381d0900c1d0010714005c04c8080c1030102d8080d266154100205440d9654200040141e00c8454840040c0380305204040360a20b020400c06002003241005842d48050101442d941921340c100c4103001203600031442c7d059080701c82d11400b50907200c1c040001a800408440208400a081c3c0c40c055050380c46403001e000340e009405c3c55058400c0c1d280110b400c41c1a8036204045202803200c21102000400400030300c028480d60b008140481c1e50b14140310074968540540404050282820b8030003910b00401c84499020013420342c2c2c4c001003650039408100c0c5c0e194048030020f142111120380c0315a1103140c903a800b140c203160070100240c1d0305000000707079034010b000746882503900101819001d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 424335575 1250 424334325 424334329
    0xa0210121b1d1f0306050d0606080f03120106050c0f2a0a080d200303011d010501050a12020d0e0f010b04061203050f07030e03010912020d1119030203130902070b0a061202 75
    0xf14144040004c3c10746520002c2450303115042142580e9001c1d80c4040782003072402c5660f03810000316150200d000c2e0402c12101c9001109200c5050468040c1c3c03505582d640c40c10340381c15003000c0e0f40710680c000754041c03401c00701c1740c0c0601803020f02401c455100107101d145103000200040d00002c0d101d50300c52070300815101c0c1d80d00e030301400e003c9900034002c8081c0b03004526805942401c42e41700340c1002c280044100886400c154140b04654017605082c02c2151a02c00c6818001c0e00002400c0000c440c40e5400144c48200c11846801480a20800b10700b01c0349080000c06903d8041c011035901d075801989080d00c0000d0542c0d44004e407011058058031070500c1c1110030810003049034002e40080e0f05200400c2600c0045440c24840d4955507030003945543d0000b1509070000382488144405141000704040030340411640204081c0701c04100088042d0507560a880c0136803e50190007401480a11422400190001d2640041070f500d4451070903200700755078200340c807800c4031032500038a0510340002e031341e0034018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 424336825 1250 424335575 424335619
    0x6060207050f0103061d010305010b0103050601050d0c0509060f12060a05010512070e151e190c150510150305010b1615050c070212010501080a0210121b1d 68
    0x92001803401144460300d40d00125142c0403d40389100c40e07400c101b801001800f00a1203225030a800910b8240a18103103400001c00e00e004104405024650b24400e41860324050740403903020600242230203803259141c0e001c1d910b4070f1704840d09404011070344000159251a005540c201500d005840d42414041040500510508020481428811495034070803c5545110098030758404001385259103004011002040f0040c42c141c0c595042070038004101d990001c413445000c041280d20b01130f0300c040130743e0074100c030160246011802d40628050a0003034101c80112107a0549202c402214000c0000923403c42c101d800911801080c1803083c0a4040c00140c180c500c05040f40c0200d005031020010440c2d00300460303005540c4c8190140c070000700348046081c48015050080801d1008000c2036240800d010788440c621300d0001c0c8a0301101c6083c83c40c442c000d403942c040c1010700420800a4100408035500e0882d072604110001c680b0070800560407a05451101c4201c8601030700440d49804038001d03035012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 424338075 1250 424336825 424336849
    0xc030406110c1306051c020907030b0303070b0403030501031209030b1816080102271005070201090f060801090f0b012001090b04150e0a11060714030304050f100606020705 75
    0x10b030040c110412415611600541c007500c920002c0003e0407407070700b003c1002203803207240c0e080b8100f200d158201026903a28000540d000001c0d040100d03901e22400f00090a600c51711000031300f40c00c404000c0c441072560540c0014181d9120705400750b5942401c01069a42c0306461000820036541500000c1510680d91680212911004100c8590020700304600b0000d0041e40c00180c000e03980803512228868201c13011480c5c0c0c904519030f101c0054841800300320341040240080b000d000d40002e1400441e48100c00c9a0f000f480d50041e09110f458507524002d000500c20310400151743e0918810614440d9a031180009561058503002012a104043c0b18100c4a05c0a20309035995030398021000460300303559507240b24600c202c409031000c604a26140c001c88000091f030300b000d03502c60000c803c0010384102c02d0121002040f103035291103243d6031800e00c0c81428012540c4201c1e02000c410f220401c50001000c18164400c0da080e104503415103910981220142d00c11200140c0c0300b108100840d06081c409458 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 424339325 1250 424338075 424338107
    0x115110a060c0e0d03031406040b01020304030f03090b18131802010e120d03020705011109030a0b040222021801020c0319050f01052703031b0a021e01090b0c0c030406 73
    0x403c070700480002101c0c80310821042c0c001c00c0d00e622030b03010306220103410b040d44004100ca041050000c5000000e50781e0180b13010080100d1900c02441d81414000c2d80140000c046000e12280c1c0c9044010300603140394404006075000706800040f0381c06640340c902806c00720907440450108034200540044405000e02c14115410040d80c12542c60107003001e20404654254075200966100d6280c0350141c00c60300360750b6072005030301c2c414041d0f1840e0380d8002c940c031080203400c8110402e0740c2d191070001403021071038000c1c1c1c1030303000d00511000c4050005d55000390642c1203113800e50ba841032104d20016038440b0380c0e8010302075054200c8945050f81401d41a00c40c4940b502a104540603640c0301c080c803a0031210142d44420806990300400540a07020340f00c0001c40b013685c6000303181107040c4003c40460899204e91b01280030780021401c1a84284200040302d061418035070b40140c4400031004060007000514000d440d40b80d060000100c2c0103c409044880640d03400004515251800004996066118450f15 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 424340575 1250 424339325 424339337
    0x1e060902091609050d0c180e03070b04060e12030c0d060801090302030408072106110c15060f0301020304050615030a0510060603060909050d0e0406120b0115110a060c 73
    0x5621400780341d03881010200030b148000c1006000141040115600c0300384985000580380c00003440c0100700e0000c07035051005101889416404c0d1720041e14018210a09170710000c40d40f0414401240c010501590040b075003081b141c8003100300c06480d442c621030045c034846410000f08400103071410080803908081078000600310384070000507083d40c4160005400507440820184445203060022034010030940c0001415500e0074032454801d4041d250001d400740d540d03110141100002d000c11501c190009009641d44d41c01c3e040d58040804a00752380650141c1c05401980d02d03281014400c40c0d0041d03821900500c0b0a646101050407100d00c002d130565010300402c04805e0015104020020020384031001c04512203080032402001ca0790f650703004540b294100550030011031404600b00070031803914940003200885500c0414007920042e4000d11045801c124001e051011010825041e603020781c5009402c51140e000031a007415031114840d406420015541c00000c61642c0400c8261581d41401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 424341825 1250 424340575 424340591
    0x70e0a0c0c32010606080c0a09030803070c051c0201200d050402030a0c0603020c06070c020612090106120309050f04050106170417030f1b04230607060c0f0201050705071e06 76
    0x2c804a072800b5605251680d12643c06109154000650720341c080041071580c0d040c0032401030014502c4020b8803000e055940004040f45501d80720744034098016402008456a682c01d054041301c0c074455080140c030040d481c0c1400455848850468055500a4048114200030040d94164010074002c2c0c001c0382c1c1846000700344400110120081002030041d501d006031119100d9960908121004180c2810849a580c0700801640c4000503600c4070a40b030a07204541d0340e241f0030154011302194210150120f50b03034001c8810107604c50341031016211b041d101180240e500c0c005001c1036031804c1c000c250100e400055981d03d00440a40300d503500c20300403102c50f00c84440752440707582d0552047c0c03199160681a8000c128040b4100e507002c401041760344070082c0c5424a00030f10581180a281c8044101101d000034031700e15035491005030b6504980041e01017258907d407000240045003408a624055424040040c1c1e61030702540507a41c4154020458216011044404942080c1005401c80e0341654074220 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 424343075 1250 424341825 424341893
    0xc13060504090302070303030b060909040308040f060509101401050307210f060b1e0f0d02040e070905100e1312031d030406020f030304020f040506060d020c070e0a0c0c 74
    0x25030112070f02a03005405400c0c00c40c00c00a0590316002d2030b41c5d000d103008000842042e1039021440742d1003501440e10010300c1e1a41e10f000101f0f6600f500340075088a0506003440181c40011070020002c43d000b41c1d080020303504803003842c070203441309215050740341e001040100041888806003898503022240c017045203007200c2c2d0701c3c0e001c401c2040f81c2c01e85020b030395040e2280d81402c00240d14502c55185000480180000c000007401841c0d40b0781c0490702401c4400d8200d01103440716007002c103401c1e4449080e40c0c00317591580300d59001407030110352420600008080005080c2001da001d90301a03010842d9100c0345800d991500020388051842210405a80d4512004046507000d5003041c5441008040d6940d6890038400a1804c2d102d00a0840290010002c4c0001079454043d40b240005e81910082102c0c4d0303407000001d1003401000c95549160b0300010702140020320100780032080c0d94405d5201203594503900300d8603046641c1c024920011411a410450201c0c4a10641801303a114406000c042102c030080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 424344325 1250 424343075 424343081
    0xd1202070e0a020a031a0f12070302031e0c01090605070b0c12090a0c06030c20011107080a020d05030103030f08060303040b1c0609110d0207030c0218040c080f0c13060504 75
    0x1d02c1c01400c55021403100034099050140041e51403241c008004001d01c4a0001500c001201403264801c142c1050030200c0c589043c00003000a40e002000d684070181c003106e19600c20b2031101619031040c0152000094550700400484055030515610f071414400c0581d1604e0b202c12000d49800c2008809000b81c0400c1c0051841c164401c805980c064030094116140c40d008110464000000741814000e80c040708550110040035175880c1d484600b4950f03080242e030785005140822902500320070009241050100c070f01c00400410400c2c3c0d08a402c0e44a808408440a010a0000038000741c1201041d080082c030500c401900b04900505032850b203551841145016070200c11000c1800300d041a00420b200140c0c41840010024000c044c84140c0d1103017051034162044000d2419859808503800c0240f5101d081c0c0310342c2c459400340c410503003c08041402c004440381118112600c4a104d6404640c0328400305440c581002140010304030b0b810a40c0400143c0350100c5d0003208026074071200001c0b40d40d9240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 424345575 1250 424344325 424344331
    0x1030503070311071404020d02070c0e0103050601050301051303030504051c0201090506060d0c0e100b0f0c011b1d0112050403110f0c03030306040b0103020d062d050d1202070e 77
    0x6004654425152501612040001d03480b116140c110010402c818059401ca00c1c40301101260016074400305100841c00038000c03c0c40140582c0029070012400042000015040c1e80c010340071039242e60b030303264205800d8130b102310742c282c4e045040660342c0c02c0002e0203a005a900140306106940c3c0c180102100b4105074400710a03040010703034580503410305103d0180841a040361003030b100002c0720b550f81d44840c00f0600e00d178803844c000c08076400d00007148070412942000c041c1001200e08c0d9a035900603003800c89582c0010418001035480e2820202d1070500c00315480c4c4643c06980c549400347d80c00010f01c8001c0180c000d07101d07810302c09441104079070001e2503c03c03a84107601c6a2551070006040c050030b50310b0b08002500500041d0301c40b00035442c3c290760000075658460802c40b804a00c03420f0b4100100c02038002c4040d010a85030800c040859200204032800000c911452640d000802501000514040343c52045541115000c04044007103001000410500781440c0120b40000da510404002901011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 424346825 1250 424345575 424345583
    0x905010c031506030e060402190e0c0403140318191205031b030307140318100b010e0607020a0e04053a050c0309100315300309030314120103 62
    0x24481c81c0302500d0b0030610b00d8002d002245010402c1a2403805116901c81e409000680b252080c4010f80c40c0c20038048051001034808106002e41e20306041c440c8244903001800212034002440b030440d041c0381e20010170b4a082004050544413241c501e40248412040c0c030900643d40300319040700100e40101e203542d14115040c030400c01103548042880d030460f044001c040d03100c1c016030810014450803d0380104c0d00a0401e130b22525060f40c0740ca071882141e0500c115081608075a01a645142d8100100307503109810181c004c0e00c3d0f0340421210401004450701c42c402c0020751000709940d0a0111031710740d280c038560280c41502100d4021888201e148d4103a01d0383c015648035100000003100300c002c41910501c0d680f400303a0520700d0a01c01c02401c1180c690040c0340080340540e0340700318070445582c440c1c0c000c100c0c0040b4205002140e2900c407600ca25040040c6212800c10b0200400c00360141c030004100c4850168140e6102540c450442c1d4088407900b5031450000104841445682d8000c5c6002c044107008501c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 424348075 1250 424346825 424346831
    0x8070c021314060406090207080d0e1c21051b030a09170d1404020d0b04030c0b0c040807050604051c080f03010f030203010b0306090c0f040e060a05060112110f09040905010c03 77
    0x3d203041000369130560b040001c07800c1c010b004480000c1c2c9005d00b81c43c4ca4030031194001c1800704003801214904034400c0c604247e00c4003010648a03400d1b4202c984000008040c0451041c2c407124822680b09480701030320306640700310001c511940440195406140c014031860801703d1074841684400b858054283d02510414500142050300a2503a101d02100144030f140c00074140d00d0190009900388070305e03c1e00030342208115400101054030403206403440591040140e0118100070011406c0e030780050182e00320502c10940b010895183c40000e82c0c085940003002060b0807002d1906c1d0401d41294030b0000c4401040520900d4090300600f4041d6004e0282c0544214205155004040c00c2d210410b04442c0683c0040742400700b0840003040300301c2015015201e50510302101408640203020f201c5502000e4060038041c07103103034030b0302e0f40200d80512003d0380d40c3c01c000c1c0c1c076601402c000c0b10b004d801c000c140b20004003c0600452030a0f80075207030f2481d00030000201030301b06407100307401e403280b0401c0b250000f59 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 424349325 1250 424348075 424348081
    0x60b01031b141b01060e1003020d06090204091a0603120325180303030906110309280b04050d08060604083319150303091e120b04020102150708070c021314 68
    0x121b42c03183d560f12122006814040794a103070007003550040228000b070036040d1140f50180641d21107410900c20560b01c4000d80c044030b5000308507001e03403080645a4503c607020f1450ba410940c4032440a490166030406070700443c4003100b081c101d65543c400880042403060312321144003400424076070304005500a407404070310740c89103280c2541100d62031301c0e280880c03400a205025603d10b00040a030002c1c41007400442c038604101104507007491210100818100000040004000d0007161404051381c168a030800180c64a100300034a90045005040159000d0050116801c0c414800c1505040d02d035001002d448100400002c4850300466680c00312070001194000800140d02c84d00380e06044580440074040d045580c014005072a80c40341900000c00104901c0e015450001070340000c000c0c078a4100403131107071450f00b0040e00c24212000d0340076005586620030129040844a4410300441d512101a5520080280c44200e80341d441039800940c8860380b0080070900f0b10515105040001410442d85 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 424350575 1250 424349325 424349339
    0x305060a05011a16020a050a240804021305070c020d05010c020c190302061b0f0a063b0a1b0f1401050f1b0703060504060b01031b141b0106 61
    0x240e041c3d01c4000c220050f0105440d4848480041d2035101800015001211040e80002240c200c080d800c07965010020a5000801030350a008039100f400010300d818844e843c00c0700c2c0c00d0303e20020480740a90810700c80200c02192104550141c0e900c0fa0f482c1c10107640182064001c07801540c01301500312080d80d91f541084030002e80400045800b03100071240040d01d041e06840860341c00d03d191000074090b81022440c52101c1c0b01d02045230003071848040481d100d1061902c07005903280c0c0071290648440b4900101c00c101108080e505c503821105100c0ca044281d46240b144d105050003204260513513010328806280040c030810790f0709010540340d6080142541c100341242c498181c01d07610010441103401c0c101c03c0241d8000081d200d0501c402a038440d00ca0710210380210741920609a88201402441c5c1c010040011039031125000341e0040004000082c83e202c0154129440881c81419292000d684c0c20102c80c403c4903102015a1020b0000e03040c02580c0b806604901c90300c44401c072003030351035200903c404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 424351825 1250 424350575 424350581
    0x90c08010b1b062706100b0a030209130b15130e040809092a1e031f0b0d0515090619120f060c180501050708220e100b1207030e03040305060a 62
    0x141c040d83c019017058200929401d0400035280f01d010400500883c020301c025010b981525146031000e0540c0d4803c181c83c41039072006068150040303114005d02401c003090300c454007003901c0490300e1110030350621500384041b0104140f001071044502e10780c06c00c00c01546441d00074120380100400444140c588182190100c1c02c21280d200000d0440424003c0c0c42031450190508445148041001590798070f03a1b4a0443d100c100d0300c0d5072586400e00c034003000a254080030f03005010300d0f40303814002c1215450724000200400ea0024009600c5041c203004504540f824849460104034400402c003103241e0344207205101c003001724106440000120b52100c051101070700420120b00524984000385042511541443c0c00395406040e0400c07034007140e64405c2017040f000301c9200c0308200c444030001d01c40703030f0528002074103045c080d5032801910306000c55101c40c0c01040d48026254245003082c14101d01980c03042601400030021410140c6030344001254a0043c00100302440c065405801c0350301d00703a4110419 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 424353075 1250 424351825 424351891
    0x206010603090c1712030c041e060e130b030d020a0b06030106061d0a1a03180316110d020405010830070204020d0b040216020109090c08010b1b06 64
    0x740750034220700c0c2c400a00740000c01c0d0709403902442c504018200b48884149080802c450b1000c09138000030030b0000064040010704100d401c6160011840c801e0501c00000f20304191040001241c54184c2d40f041c20301d49865039031012100800c1c0050509a05000280740110011a55000d81c0001448400303025282d004150300a40a9000b8040146000c0c40200301440c00c4001a000400700f00d9031210580e100072060000b442c144605190003c60000380740c1240d4020740e01108200345480e1011404c1d05d011003512004c074088283c81416011584807442d0400c40440362030362080c4601401c03401a5a01d01c9002d010340030a000400001d000403100e4103111040741d070350600c0138404000300800d2281d2502101c28044d8140e9000d81c49194402100300a0300d1000301042c1c0c420b002141603400c03030380400d00300b4400c6d90007640d409080c0c80d641c40c0d887c02248d0032801114001412400180400006d001c01851a030600000c00000c5c0c20041e29040d052010903150010b000072408000038004000954040c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 424354325 1250 424353075 424353077
    0x181c0f1407020607150221010501110604030905040b03120301080703150212060d0201052701120e060a0c11060106031505030c030a061d06010f0807060c0809040b0409200102060106 79
    0x490581c0e542c0005003a03000d180c8004003a0320080125100c02c101ca9015120700c0070304060070b000c010380e6040101c0c9201c0c0090003820b0015074829240d0b800c1c944005007250040e90143c950300f1139241000c080c0000b82c00d0354080c0a81512500c0320710001d05c0d0610005500901d83c500180c03c1c62420351074031054240c4044500c4a60364018410360300714a0300300c8181c81e081401110004120882c2c1d100603a0f450113000c004140c070b28a4032580507515030a03503100c44d100c01c0c8260703910f81010301185043c10803504080c20003130b0b41d9405500050390b8900390b58031140581400d814040301c105c1103004110314203c1c003600b060300040e858889046159040304805400b1780340840203041041420400f003680d52840e400d002e4030094450b81221158079100d00c0d880100b051782c01c240c2c2c0c82580c5941403003410b4121445458074038400d9440000d2854883c801c021b00f00d07030384504940d15145d803a500f0440540b03070700000654055560483d880000c6d90101c008000303441805218059845004000380c205801644080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 424355575 1250 424354325 424354327
    0x90106020f1b0d150923190201090e3c0a0908041508090d180e0a0f021605060106230706021e0d0606020a0803181c0f14 53
    0x25000440100d00410008910722a0742d1a041e050400111040042103000d8100081d41c2041400032656422286580c5d000d02652a02d00c1100c10001006035140b01c407007a40c9411032070141e048180e08446840c4800c4c0145007111080e51500c600104104042d165a1701c6031561100020358800349144032402403040c4050307031040030503062201182c0300c401032000281e00d54131966842084220020f4902030030400c46012800c000d4803401400380ea2065620010f0340c0f140d1600308181c01e1290031030013406440c850aa0303d4517072070000c440b11440703000f401d041040307a140c000e01e0040768402c2c40541481611056080c1d461076039800c060307007041e506030800301c00c11170354034801102000071041416030345190316840f81ea81c44840c1811070003400ba0601d4030302141c10032540c165203840818081c2004c001010001c01200742c1d00d11050781e6a031000c40c0c00174441501030000aa00f03804003055030001418482c15103060550421071480e5486d01100340308049062110084403450740700004d41c0162007004046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 424356825 1250 424355575 424355593
    0xf0105010804080f0901021c0e01080a0c0c170c0a080318070f120201020f01020a0e030708010c0c0204050a0e0f100f060b18180426090906120a170909010602 69
    0x2e1500c0f03218564484500900005d1544043d900c01c102c1c504d503202103202c200102da0b02c1190005c0c13040000f280414001060000400c0902d0f9052050403400074043e1911168200d2036030790581c107089018140d42205c8400d102e1002101024420058924031a5031416901e2412460b045640e580e03006180355640e21030682441040046003134a03041c3e075602c921021408005200403843c000424150074003039400451000901034001c80480c00001084040d02c00c0551070b010700074200c94a4000c003e00065800c40103d0150030036a01a94119540c4800811013084540745071789010f900a0340004140d0246510076030403c0e861103007080c1d95550100a004161404222000e00e0043c0d40f84c2d4070750964001c603800d03419900c0041005903005110980407180c941420b10f0600c0c200d000681c8181081c1007401628100d020740d007180c00c0b486004003c07050f03503218013003030092190341c92903016404e1141d20040f00100310344145c4030000c0880308a0140da20a01d02042c480d0000040e400081903511220701 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 424358075 1250 424356825 424356833
    0x10c050d020604151b050c0102071e054c02031303030510121403090910060306063209150309010b010903080a050f04090204080d03060e22080c150f0105010804 70
    0xc040e414003a945001507c2e103000f89000c9009108a0b00c004103840103e0302d0100501c0040603158288a0217038056492003d0124650300701c150401d1610760501d10328042e00c0404528109034050031600300614100d1206044400804036800fda6420a0300764203510403504042c0d03d0302501d45c0c400f4095907240c2d05245030203040e10480e0349001009000861001c503081031410204240c0d46000c500502d619002d05040d103806020399418001e4000090400c000401e00a0045030416102c0018458484052034000390b0035258225188030000c40c1c040c10019044036a459040c00344190f60b00e524111755a04091207014215881988a01c0c103203c50180c00300003040c0034100b81c4082d0200c604155076556802d1a0b842214030533900140200e81c80400c011400750000940360103040c442c0c1d14200560f648400c8140d00070326040300e100d0329940b828102014001d010744500200c440c810340320f450130810005e44480c108400c0f0310741402c0c0c14403c94100b01051321400c840c240101000e0030109014205525 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 424359325 1250 424358075 424358111
    0xf060307080d030b031501060c1506060807030f0f060f08060f0c0708160c03032115060302221e1509060e0d0209090102030a0606090509060906010c050d02060415 71
    0xb902d9024142ea80e00c081006480901c10441491007011b0301d408a5030311048040c04200295400f90754103e10320014290008513442428180c0380c1c640c03541100c2d6540c0d80c90031409014041300d01b22041b0f03140e0341c90546c103204030b001c1d003030140c904a2300341c1c1c0384142019051898000003d081084801c18803003031103a000c60301002c8a0301c42c0c0c0c00c0a11a0750340d00c6a400410302000c495600107106050014002044c55404a900000f40782c582d8451103000444442e41001d85d02186140754031294510b00070091980a54014415940c20011b100310506482018281134001640110350450204055504950041c0b4401d1f015100d0080907040f000780c2000001c010b0001c501a150034011108148046a516210013500040d8010038541061404807001e074043d400580382c0d4507003d8244070010540c14010a5110143e50700500300300030b1650f0348030400c0095a006010726051022070012040443c10501064a18280c3c68008002c641014a002e0700fa048000e014032011904e400c00000c0718100d000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 424360575 1250 424359325 424359343
    0x10b01081303030506180f160206041101050d0f02160c0e07120f061809050105010b0403050a08160f080319060302090f070201240510080f0c0a05090406030303050f06030708 76
    0x2c0f5000a555039803c4c003082c001032840100c0144200010100086036080c090902e10685204e04445068044004180e0b038507802a14000c203080d18070704404c901540b24030040c1c9101c0307180f1100410802d03c42e40c4417004070f90054510244482880d095201484580c20b8040c00800418161880d01e180050000700500c4103221284241034036924852480c0040741c00940282100c07080169000c0c00d000d20140c002c0140d036800f20b8680d401e2400000d2028031510035a0308a0350080046d20000c0e10300e030b0b20440315030300c004c5c40000d408a1700d510701004a14858000c9134a24031568120343c0d80c0c2401c000c001c2480c540b84110030607980c20301c0024001a241c0740199908131070384c0480c003851500e42140c143e0250980800ca001605d0303c2103014500700c0a00d02841048660a6513508c114100d81c1d1002c03030719020308588401e000d07101000071400c41c5801c500140f61010381450081d00301080d2a00040c2507c3c000d03801503000030745580620100010b000007068010100720000c0010500d0502c0441d101d03a807032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 424361825 1250 424360575 424360577
    0xf0d111e01210b042c0c01050a110f0303070504180204230301090816020a14010c1b0504050f0702010f0c0815010e090403032313020609060c0601080f010b01081303 72
    0x342038452001049401206520f140108240107110309484c2420101a80c0c181030500002c600e409110100404144411001c2040e035400e85004840081942d0840ea66048074940b0f120340800c3e002c10100501c09140101010b5482c80d87d220301c1c21200b40000650156000c075090b03c1000200310124003400302410780320380b41841c0b20030351014400090040c0014207001e8240500024000d01807403880e0011300da1607108450041015440700e118140340c40e00300001c58040b0310551600b10102c0c041c07105a49020183d40501d04002d0707100d402003000d0b41d505030f881c24001c4003030b4130a1144281d0203002d460118280d16500300a10308442d03000078280d0202801200c03018242c400302c05d400789d114078000d901c1054041c082113140e043c2450000c00900c0050a52080c00202c1d5840c1542c0d25528034070301c0c1c000d44031945100c074081041d40030480701d81d0084106d41e5001008000e2084480c0301441401c0c002c000d4200600030301020403000d035003940d09100005040240760320030400782d0b480c2c890f0394103101509 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 424363075 1250 424361825 424361867
    0xa08160806040c020328121401030f170c0a031409011e020304090207110f1207091a100e09060414010902030405030412080a090f06020c0f0f0d111e01 66
    0xd003800d901710700c41d03008540e80c41403181c00c0d02c0301c1d0140000905124000e841e0303105001503103820f0180040f11007800719200100900310041000c1109000761840c1310740030740e01140c010301e096000c40c1c902d80c0c000c040355647c03900b000801000f495080320114104032500e00030741e450180d0160000340350002100e4103001d00c544514071400518400c006440141140745811503403a4007505000740c88504500120707115160325840040b0313a040166041900ca00001c00400440b03041c0604040031b09240003440c051100c0210000d01240c1c1c1e20500000c8802080d12082c44c099042810b01c080c00d4002019580101d080c5882c46407500c031003240e0b050443e84070745001a101e0300c80f807a055056110b0340e48000000c0380090b82c1c10080c045074031700802c00b101c400d40300c3c07012455a880310210401040c1c4100400b6802030b101b10200c44c1001d44012807001300080031200c0801141001036180403200c0c2c002d0701d0038401c12940000c18102400016070f5104504001c94114035200c0c0000c24001c01d40110282001c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 424364325 1250 424363075 424363091
    0x105031620030d090c080304080703030c051f1401051002030a11031908010e0603010b0d120311041508060a03020d0f050f0106060c05100902151c0608030a0816080604 73
    0x1d0030040d14654a080710a4035511040c0102201c040c04000109a45d030b40020600041c0d4910000111800c60384810f019103e403500e141c0317040d0740090300444269540d000e10040d1081c03095500d04038000c0d03e00c15000000300c00b0050040c4444c41101600128041d680d9210541d620079000000e4400c00358a40c503105020004c42d904903030550003042e400302d0507603540401680f9841e41003480701e07041c1c6200c150301e20078550321441094241d50020000c20341045440c0d21880106910108618120b89030b400d001c030f40500082c0c02100503903c55800032000b000d03ca03060b15019035000c082d02e500500121000c42c14030b811030b00000ca21001040e4010280307200c014114042140901c04841c1000c4403200821440ea50340038094910250600c0455060280c0301c5c4d40c0001034814860a141203401070100480a605a121400c3d6a8000c4090600c420319215030102e60340c1442c000e480c003400701070020b036480d1140c0003006464100043c040210001e41d18804646080d0701420056101000700d4012800300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 424365575 1250 424364325 424364357
    0x601030b06100c051e150408041421030307030b0103060b0a1b060213051203030403080c03090705190e010e0112020103020d09050613050f0c01020a060b060408060a0f050601050316 79
    0x3010660003811402501e012402040d207100381c11188641c5c400a4908050760450403552200b001c8800401d10b4505000601c6040e41a400001c0d04d00c0c40a0003034006511000428940c003c2254125091940004100111250b00d409003c07c401420f0805005940c02e1001c0300c0410b010750010201045050f0850303040c0d00b102240f5076101103402c8682159155240700704500d140c07540c1c0c00340e2400f400c5000300701440c03940700000312440340360160b03103003009626240f035405825400585405014480ca0301b0108540d03441880f807501c54455030307000750600c0d460000300407141c00050b1300000c494003001004002d00420044048561030b030902c4c00590362820020306d503000b0701c504e2002420510403030f01080341c9500240f0f00d40122300c2c092811603c0346004800b03035990b01c050040752940140c02100c46070001403019000302a00601c010800c5007080c0c1c8441d0500d26140c008c0700e464140c543c440100c2c0518414034800e0940100d003c0c030340f991135443c1c420254910f4102c020100d00400044a100308400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 424366825 1250 424365575 424365587
    0x40b061606060314030c060c03090a02010f0e12010204140103060b0d0f1401030f14070f0b030a1b02030a1b08031306060b0a0c110418021012050a0c0f020601030b0610 73
    0x1d56881410001c07011341400310306580380c01907824604c1034407035075001c200c4091041060b6032298000030018240d0807650f9004490704d900741d60152051065440d1410301ca03030396100b46540c0309907400c0001600c03035140c0208250300d5201c05222a051628101080c405000f9103400c450100400c0080410b00e0302d18450b45a0041402180c01003000c03409000110402038450050100540610089501501c1c5020200d8a850251081a5921000c5882004100d8400c1c001c2c550103a9040d80018202c0500f200340c111103040c0100a10040c1c00000e01110725a401c0504c4911001622101242180701540c41d40e40c0c074031010300a028017800c213804070420807841c0d82080016008288281d0344030b203a039120142c80961013440844410b103050381c140f440307400d09104d0410040c42025817001583d1040d000d00c00840c5250030300300d041000c0c91080e00c204c0182409158000c0801000000303222181c81c00090640c0d04048030001150406001040491003604c883c507007100088892940345c40c2e680c2402d40c0e0b1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 424368075 1250 424366825 424366829
    0x314060607140708010c08040210090f061101020d0513030807141606020910020105061201050906061009030b0c0441030c13060f17100f1107060501090b040b06160606 73
    0x17582001c1e80121078540c07041c00e450241d8404d4a0320300300c40b410080240e80c00b0300f8600a018241c5041b050412000340f042c644030007181d811600041c5040b040c0e1000704141c1c4c4003102d50045410005006200f0980d01600039688500d05142c52076181c0000382e5600d442e0311547d10a00103803490754074a036050151581c112600d200e0024882c40001d000524041c0c00303800c00302c41d000e00ca4402451000221507043c05510310a01240c009020103550700420450008102d122000030050140000303c0017895010080f40a0001000320fa0f844925000c4040d072051a07204041c48040f030032180c246145403600440e142e01506000c0e502511041030400f00346821501d0349034a078030009506800c0c0094000764051000e81c0c1d952503001030b4143c0c60340b103000c0300010156100c0109a02c6568400440c00c2a0b900c42c1800035590800404c03841e409010340e04140d08407100c240e0701503076104010032542400388160000103109607414043d001d04200055001d00840803040d040301a2581c10b43c003004142d84c05040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 424369325 1250 424368075 424368089
    0x30806130f15060e0f09040f0b010605030f070504081b150d060807080f030406050c0a0804030b150406050d02060331060c090509010b09010905100f03140606071407 72
    0x84440e1981e8030050400c08242e030040088900000c1a0740e40f282c4407482000a01804008142024074144011820b0042c802e46148030201001c8000820000b0b5081c02840c3c40e0795500d4403401d00c050144030609000e4600b00602c4070420040241c0400403074001e030300c4888160a40e81c8019040046a01c401d003c10441804e10750001d07441d4203442003903000105842001c1d04403106191034085c80ca99600c86010001c07404d82c010700003040203e00c9003004140310511001a5a0740e2101c0341c0d503040d469001758004445641e0040c0c2040803a17618541c138060301101c11034062010a2606010607032650301c0b1140a4004c8400100144030002d45038100100700f154000006540d2100058858080303c80301421030300b05007407680960840340324000340b00540d0402410029580d00c0c2c060000c5440d4856400305043c0580c6000c0040c07250340b0038003c2c81c54800c5e01e8039445007069015000400712664446010495680385c0c0503c01e550b103841d030685290a5000810702c440400b1003404500d0b0410f45d502480d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 424370575 1250 424369325 424369331
    0x9090f041505010f08070803040b0f0d0204150c02040e06040b07030e07050a031a0a060e0c090d060f2f3103050a0309060201091214040315020304050c1203040303080613 74
    0x201c0c04180c00c130718011146100d00743ca0760740d0344949030284c0340c1c07007184140603100c00f06100081d0704c900c4210080a004c52100c100516243e9180d240f4031211902d80c000d071020a200301849015070401c0e0003005010350b101c01c060407441c5040c0e030b55610b80d040d014080c40105580c43c440250500030410048001e050000c250f001842d80e28034000d23103640b02c06071420340250342e0700c8042090700d40310780144000c1da05415082c0352a6600d0504485031a081040c2c2d45610203500341440010ad9003074842c8480c62503020001151910002e40700b020035170303104070303190600883c6181c0b044031102d40803041e9454065140b00c04402c00183d4802c074003410009241480440c0c0c00c210000003003200010b02c0c0d0142510980303645582c2c540c0c03040c0681c200c48040c1d001500400b0301c0305034151000e100d0250145c800201d00765240c2405c0d141d4540d8040406480c4040c00724550000901043c82000c01241d00713040c074101c44000211164009858072070040d0f10009081c0118000407400980d210004040032080b01e030010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 424371825 1250 424370575 424370579
    0x30d030c0c1a010617040f0b0403030207241127040b06030a1e14180f07170705030c06040b0c011425050f2a010c020303010e010b09090f04150501 64
    0x40d050030903082c401c010214800e001c04441c505c412590641c0310756006600c01e410000745440c1d16090b050000d004608266080110500144842c0300d54903419204a059a2890341c1c000408000c03a55607027048000124240b10450740150003050000304030302034506003c61000b004001c50041e1001801381c581c81031010040005212065002ca191141040782c6441600200c003124000c4880e0b900d500d1182904400020310800c20503111040c203048070320225181000c0c0c01c40031900348440c54003d500c5100c0310400e6050140d2003045042d0180c10304030003a060300c19440000032104d204d1841a07040c2d080f004200307818007480a500002c2541200c141515030392a0a94007486140550380c040700c0c070000042c101904142c4600c05840ba00010700180c2072030620540309000b0102800304c609030080d00f0611004030b03820707030a02400c1c0510200b5001907480794108103410b003030040e0581000c21010403c0c03140c0030f001d5880703a01258000c0030700503100803180c4960400c05220707008001c15641e124142800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 424373075 1250 424371825 424371863
    0x50405010b031005101706120106060509090114010e120709021809070201060303051606090c091d0309060f07080d0905060901110c031902071e090515030d030c0c 71
    0xc510070f0400d040710419040c0c035001003088411029660400281301c0c081c00080c0402108492600140c0091a02a4a410048003282520320b0f80c2c00a1700050400301d04240141042120706000d04a142103403000f04011000080c501d01081c64224403804400940d483d0040c01408500c028040b400c805654070441c43c405001c03803a0004001500808044000820552040c40381a094a9060352043c0c6000c0910014040c402c410b00025603206030344d040c80e0300c006100b1076505401001c1104001c10502c0c4085100032080010800c9086d0b540c00030042400a55200341c00c541c0c0310700740340e44003a84400349070500d0600c03401522541080c00c3e2030040c0c0c0a061007400504580b140038042c0081c0701c1d014100d80011514081d2003045d000c16801444030b04a01004804031044d00c4100307204641500d681d4401085049140414001d000801d05d8400d00541100340078a542c040d501c004180e0944e01500003182c0e0f5030321000440c00415a82d0b401d01004903100c4c103a1854119004821094144d0650807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 424374325 1250 424373075 424373077
    0x70b07020a05010c0b010612020c03070f14120306060304060209130618110412050c030a0f0303150503100f110403030203130609080a11060f21010801052a04050405010b 74
    0x2400da100d5114010001440c3d8415402c0603400c542c4507601d21a540d00c1d21105907005030042441001035074081c000601c006c5c00400103015200e01420300c9040604190410700a0160802030800a03070308000f040c010207851220481350801010703121141d5035a101d0818100a0046900c1c041d0700884600c84040510500d070880c005940f0a00705492000c0084200b40b000c40d01081d40c0c0c41c0d0070490500041004518902c0404032a84c016001d03101010100c000083c2000020b14080f1800445662840700307066042c450360980301e040e030f02d20020b810300380000a036481c0c4124000c0c050341c503201d20b500120503d8542040c20301d40d40c082c10083d103da40303a10b0083c4d180d42000300c0c1c403054111503840026203244641301410032600a00050112608640c440c0d00d441c19002e000e550b0401030801280201881e94002089030715290b501d080c80c0311004003902440040181c4c0303c08011b80c100803c2c0300c0c220314a100c0d469000070154000e101c9040705003801c14501e0049902060703000345000000204085180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 424375575 1250 424374325 424374337
    0x807020301021b0c0a0f05010f1b0c0608180a021f3f020f19140403060b0906010212031f120605010e13030c110f0a030c0501201914070b 60
    0x40b0440050786d210103054880521610905000501b686042030081e80903040c40880e48c20000705406240c030040d220307030501c41d444ea449140000d10b0b810030080700119200122406c041184084d0109205503000100c40d8654800541c1c00c0c59001b40800704010f0103103058505800f0800020000a4103107150031103030108401c8101040c0c1c01c2307011404a00e8189200320350414610018540c100425040c0566030348030388807145410312050302c031042002c0d0414405400254447c4d480800d0001448062103109030010301000d06640c0715001200742203001200352a0310000c0b00780c0403603000e1001d480381c920201150740480c1041090403941820b0203400d400040c16034440b0000002d183d03d031403401403055032000c00b015000035003111842000507100010480403d400504100c221705202c00018a0b44290f90310032a030f01c0355401c60410030303540c01804854030a0407060680761018520f00c43d60707403501500f0441011041c180c9142004011100c103207004503004600480781d030181c48114484540c1e0200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 424376825 1250 424375575 424375579
    0x106020c030f0109080a0305180106032006030f0105130908030c040906080706080106080a06080f060a1a06070b130f050a030207050901210c080d02070306060801050106020a0807020301021b0c 84
    0xb801c07528a0300c0c414001c002519500000507850311600c40812002403c01420b002e420544e110a018123010b002d01846c1d004e5401a408007120f040e000c03503201b018441c046100d42c040d00092040002020800581034112803007900c1041d2000d03045619040281040c3d400208200c00100c1840108007101014006407400008104150798840307500c02d940c1c1e015440341d000041d0f82030b00180840e40c0f083d031041c0d80041401074040b5115466210b003509101511103c040e5a901601c08c012100301b0601500a000104800c2c1e0b55004140c0340101d00e440c400c43c1390280207108080d0120b038100300d0010b002103000c0e4025440407104161031600c141c9802d80c00400341d0051103010404149407401d040420704031000e0300401c40e60101d0b9054103841d03c8550fa00c0c2515040d9110f4400190034106101040002c00d05502030140705040d45800d20464a4507001041c10342c1c94000144504c41c2c000500300b04050f0409102600d881c803d00c0000d000e48903c501d160784594044060407030701c0d40002800000c05c0c0c42 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 424378075 1250 424376825 424376833
    0x301031106090d0602070c0b03040602070512031303030e242d070309050c130e0f010e190f0203010c0329030c0d0203160605040501020d0903050703170d050106020c03 73
    0x100384200100740c0aa00c80c0c1c26401040b00c421000010b0b42d0b9801803160382e1003030030541e45c0240d4450314004940c00c215003e442c400d4000828a040003000d000b81e0a0003e01c1010060550401c074009909030300300c41a00400741540d4500303d85e808802040a03040c08840200014031007010f01c0341c04d002c860002d81c1d8000302240d041c040220040024410001c00e800703980011b010517942c80004501500c8504c1d000d603143d000b610000c0d141c9854078a0302550341454104086010842903480340c1c5014460007098a00364580301040c0b0b0700c3ca00204401c603140780c550004203120710135424100c0c15051002d41c02980742d8a8014158250740d0103802c8855660702c00134204480c2001615031141c0411210101581900305074210f011030300d4050302480507907001800f116080c00c40d082503004021803c1c1c02c91008500007240411030740da1304026038030b5005c51504c0c12040651840c0d0300d24cd0390300e20b41c4c00000d0580c0201080c0c4e640070040ba20959101c034500000038045565aa0b1010f034032558191100303030082c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 424379325 1250 424378075 424378103
    0xb040305071220010c2111060c07060209130e07141f1b0605090a02031603080d0c031806090201110d02030f090612090f06071409220f02030103 63
    0x62010080c040311070304598220741401140c0107001007250281a40ba0500c07034070007100400b0961140e6484803910703945048500800031b1060140c0481100d5a28041d00d034000703400c000c90094001c041d2040580c0c4800050317100c040030000608200c54007100a0000751800c09400382c0c01200040400c2220b00e145c1d080d034026000b1000f40002869013400c240c2d10243c6c038240c02002544111850300782802c00300349070f41c02e02d00c65030784070829684191040d0744540d001042d80420f40c42c082c007000507080301c5400c41180f040d00d10b580b21714641c011105100707000c5030f0342c10303041c248103010760041c1e6610150090305a08800c1c680c50304000621250405030300290004201803840b0900048a008000d0981c00940c100010131405120a91000c803107150403907014008008400100c006880c0124095005041000c0507021044c0c5011001044801008100d03401c00e54031800c618216004060166100c0714501d94640c0e50513560284c4c14004206586080158401c4005660246068a100d5a0000d075081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 424380575 1250 424379325 424379339
    0x2a02060d2a0203181909151401090905061302030702100c05040506220801090302100f090209071803050303180709020a020c0d150c110c1909110c01060b04030507 71
    0x5a4140072180140c0e00030440040302c00c0d5100c000118800b001003604601c0308800e00500948402d42e8080c00070251194884402440d40e24600c0c0c0140252a001882010585000820240d1244110010f265440d0302140310341d141c8108521461002110556407400c05860081d501c5007041c2ca40d0382000e203006407414901c1e02c101e003100c0483d680209000c1c10300a0810300341d204900b0500392502402c045801c0014141c1081c012140d40304c0c06038016200b5500c5045030a0f05803400c800040309594a8038a1010050766a00340790354003c0e029103420b200701d856084000000341d4a03a00003400d00d100100070403007000811003c00400c24888c10650340403176a2061944203034055019031a01603004108100d050b4142040400347e124001c001e209142402a503807402214114405030b00080c40c41141103ca2900401018071002000d81e20080e407005000c0d00340c0030105d800d004080101c0e0f100e0a03142c1820f204641520b40e0345965000070031495984018400459010344000c80f02d40c054071000040c85 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 424381825 1250 424380575 424380641
    0xe01030506030d0203270a09020306011413030602071a09010c0e01080114060c030708030f071e081b0d0e0f060106020601060203030402011803050a140115062a02060d 73
    0xf6030155001036086c201c020901304082e4402c1441d22000b240b9420b000d81e015515001c400005107000840103a580c03c05400040081550081003421724800300006503000a000c4914402c8a0b0441001078840c00700b80b0f03101109811110204498040301c3e410301c555440190700000450303c1503143d141070807910b81d005590154091080001e40c0001c1c01d0064464206640182450602e10301034a24203002591020b0341500140c884071140307440f1500f00004107801c520703400400e4850405003050b042d40d441e00280288002008107200e100c00000e504004442203051380e0840306045018030081110386d0340c8075501c0190003017001741442864000900f850000ca10746051f0380b0365a0155145540d81e400640b040700b0b91f080051080b011184000010034810700c11807408034418440c8081140e851440b190079900e0081000c071350201010702c1040120707044101e83d06082c045028506510741c95450007415005136940180d04a00c00055110178030071148d0001681003c1c4100007a2030705130710000d079012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 424383075 1250 424381825 424381843
    0x20d0b09010b031615090b03070504091109030d0309020406080f03030f1006090614070614090c042706060323070905010308070803090705060d0204050f0315040807080f0a0e0103050603 81
    0x82900c04c1006001c40342100d0509080c0e0195030400d50f490f1035994400890700e030710449600380001c20104081c001303404940901082c2203030ba03140c1141003580b4000007988031f41d00541c0d40320170305075601150400c54503160401c00040102c0d100b643c052000030011301f43c50b035001700e4601c5610321110700000c540f500101400c0c4103458243c2d941c840030740e00340641601c441414003483c558030320041c40900c0000f0214081c2c003004111b40c801e0391f0164101601102e00d403480d4104d10621940c101160428001603103101c40508281c1010790000702c81c6035003800b10041c0130030b80019018007101c0300802c0c1c0e4000360b01c54854184101d41c084900072555240035600710750003800020207040341000039401080242e0007641d0001d030403105403280103503641d0008440d80e003c4208112443d8010074200312a140c04100e1041c001004d070f01038000205014081030b60130000a00041c1a1003001c140842480324500580b110204d804818981c0c600003010081c1000b4108070803940000e042030300166440c140885c000403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 424384325 1250 424383075 424383103
    0x21818010b0705010216060902010210062d1802070b010f05030d03020304020301020c0a0b010f1a0301050418081206040e0c09160c0b0a021801080106140a0507020d0b09010b03 77
    0x11090342007201c0076003668840001038a1a6400380250140401300d540c0c4500518850407002480c00303054800a0b0030b080c114450f5040e09440e24038204402e0341040ba055428411003040304001100ba25500044900c49801884c0481d0303401005089048696000380130765401081c1c90741c0d16030390390040c0140c5000e042c06039527016000201c10b581510b0081d00030b550001d100030000343c2007107403601041d460a110000c003a2a00b0fa003a600402002421440d55000b03009403101c3c1c0d4031081c2001034414114030042c4201401a0754034074070300006211514900c0c2c240d035800a826aa1944d4485c010701c200c603020f907001da108500d4002c540c0360001c80041c032501094000741c0002955034501e03c2d950495412001000148001100b0b040c002884032641184240b08500300181c454000741c1d400a403100303a401070342d8140300000e40140500c1d41c210100700c0358610810506951400b0b8414121820302440038000e402c07840b40109481002a9040d80746d00c0f40c40104c0c0200b05c1e10300348038105980ea4103c14a054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 424385575 1250 424384325 424384369
    0xb041a0c1011160605192309010e1c021b1003090c09090308090c0108071b03020c1005120604050709030b0c3c0403030807110c0307090218 61
    0x9a00785100b5040604091450380c00e403400c2c000426a10035100f801c490003102e4aa64400401c0450140200d03ca0b0f1b0060845204108503100c10703a0003034040c114007505419101051002410003d425040906207441800c00d0700c1d0800f6100600c00c0e09440402e0205015002e07031100503001c2000d42d00307100d0044100901c4542c120014110640003001107103c29036400610380d4000c250b501841c007405030352620a50340c2c0c0340d1034a44100510b0414a02440d00c40c100038044041c0500f140e40301c0c9006d01400e4111020b10001d421918069191440c0d5000c05d98004510164451600d81c1181c01382032820f9000c05c408185035585400c1000300e40f01202e41740e01007819118148081103c508600c2d03481000004040d18142d4003002c00c0311000441802d03140c441d200d081650308004c014002054145240d41c5103d4101400c5a4000d414a00010f120104200011010f055420010001445604005001e0701c10135034440c0b2018011350310210803a502400400c01c407942c40c2c2081c00d12140c0c907011a034049 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 424386825 1250 424385575 424385593
    0x80604051b0a09030203060c0d0e060402010e1201060f0e160311180d051516021c030b0103200309280204110d110720030705041d070b041a0c 62
    0x241500e40c002c99040d104003c211480800140c40800080b40100c101c021440c0c0c482c041000080d00396403031650002a1500004144070050b43c004640c110030540c1118030041044e0100c0119004003580c1c0d00410030030302d07910f000090400003050040d000c0c143c8036200c1c4a0901c0354000c2542910504120300000c7c000801845031803505a448044440400400802000c80a03881d01f030b140140c0640601003500700c41c028003142d1401c01041072201c03501400030308001050061800800d03445007120001741601c500040d810350b88030303038442d10101ca4081141500704180e803001c10255041140c4c525401d20980888039451410641c03e01d03110701c1942e982d900481d1076030342804003030240d104401118007002c3c0891903030060a40103040c514000011580c1c1c9903946030800c1d14400b103131410704010007910b803401c01400e603e0210301d25081d01e20944011404216501d210ba50b0a10907034441d1183d4010791001080c1320741c11900800403103046441e4084c405040154104451045c0484403806500c20103078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 424388075 1250 424386825 424386871
    0x3030f041e1709010f1b020d0c120b0f0106030603080304080a090810020a09061d040b06040b0d14150612090703060903050a02161a07060b0a060f08060405 68
    0x140c020100560554201d01c10000e640c1c6503440500000380720700390003010900c945596440314000c4c0c0d0b00089440c1ca155048112064441020340d8040068007880101803183d013405282c1030340f08028190050f03240b00d908450b08020710401c1042d03580ca042910110000130320944280a41001c0c2d0f0303000180c003031843d00c9554a500740c43e030202d918001485207209000611031000d100c0442038024115015a89101d0800014200c03511354010380280181006000540208400e00390701540c01520002442d010050000c0c903640101d03841071004440c00115031032041e2654014000104243ca442c0b4210380340e011415441e8503c45c030b0b6054000a05000c0111030b400c15888941d08506000107032100c00340c4a07103541042d00d146010940c00b0500010b0106001c5a0410407482000003401440e450541400050b030090f020785d4001c3c11722414042059020320000380d002c1013024200804900401d40c0e0b03464040c01d920700c03d0b9900808502c043c0009821414140030383d40c0301c2d8000c5904051100300760381c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 424389325 1250 424388075 424388093
    0x2d070905090c040e030403260703230a0e030106150206040b1008070306061503090201020c010e01090506030901050103031706030d031802120f211204020d0c0e0103120203030f04 78
    0x25510051140c01001d074550744891164213040b0703425402441e551130440c1401c05001c807a030101684050720ba06451441c1d0100002505d4160394545898100d180000b01c62104826006044a202440c0064001d03072a0b81c201c2e01848541400758020f208640c0d80e007900c2d01d078080c0c5698514016811030000200040c2d40c44220a40c81a02c2d01078440480d61100e52035131402d03699800460340301c0d40d692414000241d4909441240031070503c1c05100d24012540000c2d2100304085049043c0248030014072541e038050041040a000003500c25601ca1070800403a41c0a882c00380700580100e1591000402410a060241ca2203144050001e018010640e80f0850090941d0340703003200b20340040d0f021f090041e03035107110031018007843d10700038000b070102c2c014014102018090f42c3c00b06002e407888401c133309103481c0d03081e101001c005500c080f02e00d607183d0001c6100006140e1005081d000014030100d00c00a0fa14003543c1039034050500e0105200f80102c0907a81c9110a41da02e07030f2a031101f6400100003c2a082c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 424390575 1250 424389325 424389331
    0x70306060e0306150a0801092d0215030a3801080c04050d060b0303120709080d17060301020714070f0911030613020d2a02060118090807080c2d070905 66
    0x150030174440690700c1290500315048208110742152401e00c0d480d610340000d00200d0144604000030603000040d5600050825407042601c0c1140c4002200280010203142e000400816000031442f4200040800c180c81950180c08d082c0010310132580b44060552013042c04501c1001461070451505061204004140c040c2540c1158040e1312003000081946080c4043c080010941c92004440d007401100680072034031a030040000f5901025002c00010740c4038250402d01ca25100055903683c070341c0c0d40800c1c068030413100041c00342c82c9590404550004001085c900301c54400d20315484143c0c6a101c1141a01c0712010303105002141407012603e02c0c40c0608041d4104404031100502e8049041c0d1200c06440c6018001d004141c0d002c000005030703e4610124810300c000902c00f07800c0d01d41c182528810300e01040070b100540d450340c6904100070442c41c1c2d002c480240f03820620070b0392101c4007481c401e81e40d00030600c400d019450f801c5106810b02210301400f02d0402c20010083e194560a049003000144001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 424391825 1250 424390575 424390579
    0xf1205010f0606080603010b1203090904020f12030a0305060303070c06052b0e010608010b06190210020d050106200d140f0406020f1203060f01210e0105070306060e030615 75
    0x240d800e499107803024450b100080105407614541ca2620030200b508440600365102d00604c10414614030b400c0000c0200c6007103080850b803051f007540703442c00450101c0c10403020403a0007810400103002031850000c00307846003005c5980c0c00d02003955070300140f507140d0081380401805034506a0701440303403d02072000380210701c620103103c008148800c4070800010503c0d41c22201190741e01c04d03400342c039a4428003d450140c005140240494900c800115200c0e11034103481c403800540c25044034060510a104025200c110460155201e0784e030304524030000e01080c4256004200c0c0f6116620510321003410044800e841840070740310a02d64018142d40a41107980340c003031680b03800c00c42e618003502c12001810190025500800003e03944030800c0e0300d4070403403c4250850000c14000c10040d540c40204080f94480d0a18200c00ba8540011003c00f968007030001a10925042c0507051440c0c0b101544990301c228280d0ba41400042d44d2a401900d200f0030f01c80945800d904490001081c0540c500c450110207800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 424393075 1250 424391825 424391831
    0x30a090302030d050a0f1107080906070305040305121305010e030703031b0f05061e3106020307030c02060606070c0b0f0c0f0d090e090606040903020c221103010f120501 74
    0x210403c1c0080350022038185200d45d03a104c0e503029100341c0381d01c981e9000007200c0740c1080c60440799440d80080e0340184444e040c03044400141003806c00d4482d500b41e9005650040c01c80700170f240608002000e84e00a010000c1e4108040d68001402d50310030311221406241c081c014044480c11520110780d8071070046201059041902121400111800d00d0300500c540120050300c945c0c00c2800e403985015495122030307414110350405208030103a092402006400000108150740404803500c100b108a4071280506810710220812000d940c240d00030110504940c0d080d0390351036a5010030000c060182034809800340d007440c2001d01001403000e0040a00d1040003544c68102040e010195240103181c80c546100345c2c02c482c56075001e458204604001500d40c8201003541464403181483e540c4400626841c4a16103490b8400107250003406242c004050140000c0c1c0f21010941e031444030305200c4160300440f90701d0b0141040800c541c8500752070503683c41c1e003412048245801da42c001092144081038074295a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 424394325 1250 424393075 424393087
    0x423011406040501050a0e210312250c1a010b130639060507121107111014040b120a0e1c022509140907090e07030b090307150b06030a09030203 63
    0x795014441232150b8004001755038404601012400c070f0308d00038000040a6100c079540c011240211071000c2103010782484c040c44071103031a0610128440d40c0605801001d4501400130481030040b1008143e09840320b8010442c80b07980d82c1c2c00301c46115450394039821442034000030410b005d8450602103690b944480444038002c0c016140c45084401c151401c00218001d1030510b656007030740e03025240c0d0001a0310a0300c0e0402501d0303121501801d0307550070101c0c840c88441c40c904003150b0144040500ca070004030b003540d8071552240a0b4042c1980201a1025a07005520000384840070502480e80041c0b0b101d800f501400b11419003201240a841034604158001d141a0302a0602c21a01c00d045112015440c034504a1a2003541400c03140107000b40c46581c0301060411211a40028180c0102d4107060b0380003481a0850300a1400c010840c0c00082112400e4014008019000400780c85e880c0e0040d0385541e02c0b9040c01c5011700403603681d0785105070840320920010300001e00550040b0215402401030f41d20703000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 424395575 1250 424394325 424394359
    0x6011209080904020c0c010809060f0c090301020c1c1205010815180f0c0111010c0917010605120c01080c0a230712020a12110705040207020423011406040501050a0e 72
    0x40c01216040c8041d506c055010f440d59a0710403400e58004d21000040c5c1590701704280407030046078004000c1003040400003111040d68030258126010300400380c0644841009003480d080741c1010721200000081c100301c5615104460300d1103030a0482e81c0003002410b000c540303d0b41c49a040c4100401c03641424146855031108500d090118840701c05544d40078140d9015030b18000f500842e00344900303540d942e14003003e4007a000e4006190b80c042e2640d46d03405c02e070441100b10f4018090040341d00b145400c00175840108090307160002d4a10840d4809894400300350b550400c4001c5d2134024152401f00040c1c400684030140034a0b42d0414241c4a20001c03040d00e0001d01d91170f881180c010030511000164030401915042c400b80400c84442c048003403a203042c103000c80841ca2036840b461802490300c1540e000904008664031a80034000601c1e5610f50202c0d502100c601d201c116001c01d10610001624242c50340c00d0030302d0180c04403019100140c40c8c0f0343c10720215040894040f862a00030b160000880000341d0016 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 424396825 1250 424395575 424395577
    0x9060e0d0302031b2815110c0a150e03091302070c152007053007080a1103030a0c03030e0705030628060f030b0405150c04031103060601120908090402 66
    0x8440c4040041000e1520f14250652600110148a40b1052186042000181340d921783c0040e10004440214107d04082c1c405402403103000b0601c503451041b0801c0c0401c0100c89910402c040004040c00c0001d0600c07205c0f005e03124480c841c801e660100401c515451900950741c05000d8840c00b4813803284505031a2020190200e180002d4a80460305074910300081c982d24140310303415101d5a0020700440d8ac41c100104080028140348043c000320702008140e10001010b0604134102081d40c215034104d80d44051840d2a0b9101000c1510b40d4031800101003080d0600000329145002256035040c4901403a841c110b004201711a552400750089903800101c0d40d0f0304200860080c11100c4131140612482904403000f034000040e40c102850614404003e9001c0c054035400403641c10108001d80f6955030b2401038141034403450749030b50100980c410704c202810103902900a0301d1192040da91300350008020180c0d01c0400300c0300540002c1d0b4140280003000d0060f001034024500c9034030b0b130321300b800c8010300040e0a03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 424398075 1250 424396825 424396867
    0x90b0a03020d020f12060109030b010603090f1b0509010f030528060501090c0315080c04020a09081f0c1d01120605060301230d11010f0c0803160e0109060e0d030203 72
    0x1200304c0810580d80b00c04200042640101003405e20018451a41c3c0e22003100d540d0512504090599401c4040180080c0c40c0c81400003e81c400c031100d6004051200c0c00c5401c803102d0044a0041700e0390f000209094803c28044400d980d00f260080c200c0084900d030742c9200300084101100e000c1c00120f0100000f0382d8600406010303001d105004038213100b14481c010100d605004902180310400a82040701c101302007410125003905542c0580d43d405040710981e00d8107540e6204907110322541008188080d1200201c002c0e00c1c80b0503100b4031540c40c07a500100d900c903420b2119038040361000c17840e8030003940c001c0040da0482601000c010a01907520000180c00390000d91020440f050300701860f01d41107504860b050b4110404070742140d40345410b900c3d000412050100b0180c180042c03404029282405a92410311306503001d454a6030342d01e003100c201d54a030310440e0074a502244103c2c54041d515030141440c103095540f01d07655040b54510480401040303019080d400da05600042084084866001540d041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 424399325 1250 424398075 424398097
    0x62013050102010c180e07200609011107020f0d0212010f0203040213150e0c0909070e0108090105070c0807060f061d0a02090604171e0c03060105030c01090b0a03020d02 74
    0x2600d280200180c02e48141000000401002034448040a021445400f09440141c00a64495030b40d0346003d6440540c40c50f00c0c001b04243c29520300494800000d44135104403042002071011440320385914900f405801002548058090842c2099050818148841c540003d09152242802000c4a800c450340f1014000501c1e40000c100802c4d410000c00300e02070748101000070061643c0b40e081d43d09144416000342840c561101011468000c2d0a0080c5c90043c0c00040445c021030921b418080c029050307030310707000703000c0303680e460001e0a80c40041c4036451041d440368942e800b14a045503621451944068002c64030656a8240e40d201103d0038420080504101010320b2080c1d00010304001052000900b0107051034010030103401d01c2d4552605640840703085030600001021000301c5541000d1300d030009120b010501003c500e1400c0340003d242c1020070350540980d41c403a62104203040d201c81c1c013030250f03501240302828100400400b0000030402c0c050585401404c0ca604c411002003642e1008840325 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 424400575 1250 424399325 424399357
    0xa021006080a110d03090b0f0403080301060503010e130c12030306031a0117160603020702040e0a06022d070b0601091224020c0a12020322090b09040507030620 70
    0x404200843d54446581c80040701c030440b010010303a4000b01004e006010300c4049110100d2100060440c3e0307010340c2e001e5030340185059220f60b12200f00400d650000d10400f008a408040880c80b00c41e0f010345c078000c1c40c64002400c000c0090900c111884082d01e800c0e0201c2c20075a0728080000401e80c9074100e000d0030140e0480c0e042840d450044c0100003188180200c00752504110709c00f036440c40b40900f091086a2050402680f12101c2d40001070003064508032808031750007070450070700400c207a9900070f044010004862a06810320341220b01e0003207601000041d030b4584100440b101007061401c0c0c0b503a001d403051400104607511444203c0d081d01e40035104680010707980c404102d412240c28170348441c2611204086050032842030a1660352045418082c0c00d401800541902e45882403003120900c40180c0a010701d81c04030140d039442c10038114440c50081900d8140d098031325250281c1c0c0c2c10300507608100140344007030942d216a0001d10080101230701102d0f0341601840c0c203440301005041d81c545429902 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 424401825 1250 424400575 424400593
    0xd0e030c0d110a0b06012001060321080f0a060503100506010909090b1915060e090603070509190f11031b040b040605130b07050a0501111804020a02100608 68
    0x410301d00420241d4050a005000b4000d084440000520b04001c60f0881d05090082d00c17071800694100d110b90004615040d000542c03040710076015000350b800c03a4819601d030030010380c00c00b0704169a03900c0300400e5400940f45001082aa02c4e400e400240c008882e0b00d4006101540c900c0000d1a08a55022070b4410355204d9081107215a00403030701c01e000303252700714090042c14003e540d01d404038140145411101d001090516440500c80d030700c514059411103140d6158991601005000b00c505280c0700b600c10031403140040e045040c0412000100c4030050584e9000b40c0303414000240c001e0207a806802c0940d5511060306405c940c901600c2845c414064125950f030800c84180690768040c000030495100c81081b01b0844842040121401c40d1014a0583c1e100e12052a0724400c2c640154040b454010000c18084188272010a5034600700d03201d03500801030000344207840151030103102c2a441000e515440510141e0800790004d00c801003240c8103841c10968140408001c407801d5821a9000d90f022000d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 424403075 1250 424401825 424401847
    0x301050717010f0f03020d0c050a0b04030203071e03020607061104031401051003020906100905060c031210080304090513020406030602090f0f06090f060d020a031a0121020f0d0e03 79
    0xc034054604411030b06101c0d4103003824625104c2d0b00d031200a011b50305c1c81001505005101c1e500c0005401e0003410520000c0e502c100007411600305000aa10900942000003070440c843c119080140824010880180c1c0c51a020003a141d04104c030185c440c40d4481c40301e44000319440340100040c520425290494002c036410b01d034211500108124000480d25209002584c1c4140d142c544c0014200e82010888183d640100c9580000745c0c0180d80241010844180500010003d00168170300e5010500709540c0e500402641c1d024203208542c4140c0040200340983d041980042e85e000610241110f20301000380d0100d0121031140d401030b50351503404a90510189003800406022510490710590031401010000e0041c0c8603001c2254800c07a2400507a00d256140d01781910040700c40070008548903080782c8800f4014000084592004001c000b241840070740c02416008000500200081c00c2c890344400640c000758403109480c654101301744901c03c80c41266024119603c10814059512150a120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 424404325 1250 424403075 424403117
    0x907091e0c05030906040813030209040506040210080f040201030c0905060310060306090902010e040e07031202060a06060c0b04060c1b030e09070306150806010e060a030e10051905060f03010507 85
    0x1d0000c08001c001c00c02d010f204d80000442c650450340048500340d5440d001e00b2113030341401306540003d420402a104020a219020801500c114001e850700d840c0c2d0f1040d003008039030000d0126417541d0f620032080003140155100340d104922001440c01e1072000c01da1103500240c3e00b44c00880f0b6640e23861540305e00602c011a0b040c02071000608045c401408000c2060b40040c140104418103240226610007104242d84c50401c4800300641d080540200d09c5003980310000c1d1075400444440700301da0304020b00000c445105504611000380c2001e142030603601c440da03d950142c60760101c0042001501090400c84000415103904154400d4844c203500004043c28400900c4004043c8028903180042c200142410304074000c89044151828200f56a00e000041c0c0b100204220b619070815408112182100d4041e40080c2c1410507600441d803160a2542c0c01406461080340d299005410585d49024803c080d81c0220b5008140284088a1005054040b80c00c440c8102d84002c0040e40400029480b078079200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 424405575 1250 424404325 424404341
    0x21030d1407141c240303051201050102060606030c180a08010e0115050609090c0403080316080f04051902010c02030a0506060901060f0c0803180a05010c030b01031a090907091e 77
    0x241405041100f1141d0000102d40802c9903101059124a100200c00d6504200d1120f00c1c030f1100d00f40c180e074980700d00b030060007a041030b4114154540501c0011545600016080b44a540020074040c51640e4403164030645d41c02441400e070340c0240c082030f290b19075545d0303a25410207041d845000040c2030020761085401e50b070300041c950f403920812003c1409551a003070129480b00d101529602c0e4075441c0c800404040d8400c03584003030440d4001009004242112100d0b200030b03c0101d41c1c8000c8140c42c1c05502189961083d94006d042d07074012888003412440361040020002d005040804101d0841d4000c241003c410311011034403030304100108807546ca0a00c0440f80234202d14540200b800001d21700150110365407590203025001c010001901500154990450b50300b408825503850780c0c224940780e400b81c8500c0d0811400309040c080c2c280e101c0d5100c0d100d9108240c0c0e01c903900d18040301000051140303540380a01400c0c543d000d11480820099050b00842d28041c6404124480038518400c2d00e000310f500c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 424406825 1250 424405575 424405607
    0x9180c0108040503040614040807030614070206100e1b070809030708150c0d230a05220f0201020a0804140f10020d080606040f06020a061a21030d1407 66
    0x60400d01003c01e00000554003502c0203400c0120201c8155988212503009603800600280302c0c0702004010041c86400040104c0304003880e0808941703800d01c09076180d003411106d1a5429001800410040041100c0c0d00e81041c5030403d41603100c3c6101d00450a03a43c04800199840b02d4000b03102822418104080402002582c0c00340a484040c0b40030440042006007a40314524800700c0c1038141141258000103040d816100040e032071103078600400d859030104a807000800c42c079003000078401c4010344a10000b1400c144003582d543d960346a071031804c2c16010340b02c02c0c0c1c11480f4660225000444c04002400036020400c440d880484961b420415502c0b07010a100740544d008400705c1c90238980000f03614605203043c2c00d00c610716036140750200311240580c0d40714030b02c0c071200604000356142d004111184550700074801400a40c0c00a019140c443c0c0e41c0074603154005908070f882e101d4850a08501c2201c8403110350540340303041c0b208414281554881d03800040000411010300140d0742d0416042140c595031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 424408075 1250 424406825 424406837
    0x2090315010810140703050403021509060403020c04020a02120c0312041a07050703091401020f010c030f050109090b0714090d110405100806010b0705120c0304060908011104140f09180c01 82
    0x441c00d89481c3c005006040c5c01c0c00d040d00d41c008602014002e001c4854043d20220001e0810f181c80199159200b0058074150054050340c12511482d0800d402182e00b41c90140e002090304d03d260006080541d40310081241c902d01051012404010b0820a03e60041d800303403000c213102103181010f25201c9800078013880148542001480b0019030044440c0301210250450f035581c1c46004c00041c0e041c14501d5140f02c0055180c501c140e600b00380c02d0703888a40300d10072599041005a80b105c206101322707a1141000351008050300000341010f0f103e4034981c110302890305002403d0420324404a500581568001c42d0590b80280200d440350070f0501c00c095102483c0c807004000d052510045940b0781d80e060103100010000042c489060000c1000b0080e00a05010005e030b90360403096117047e0302c0303800502401c0c0019181250001d8820014087c034480c030000b91014034503003482c0c4406100000c0c0a814a40e0b00200c6d803200f200d845a5034010708a1089036040d00c48071010310400303106428188c140c40c0e080d042c410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 424409325 1250 424408075 424408091
    0x3050d0c02090f0901020904050c0c0f240601021608010c1b0b07051b030c0a1e0c0b0315120706030f110405060304050109020d0311070e060102031c02090315010810 72
    0x6600d2201c550094081400b0212540780ca01002d401ba101c0c0c04002500300342400103100340d0500c00001407484280c01c005803004010401c241e0341d21840240044000c1d82611200450941c401c0c184158000c070341401214202035203c2040c110f10b5441c1c2d848003809035518404041d410b40c024624042d4403a10446113243c00c2c6540d660a444018060800010020041040702c40018030a451503013104103e03003140c0e20b407066101c0c01c0303540d440c2d612811216402da01c02c0f159a0030312124144d480480e0300c6585000d00c242410030001d0300e0b070802840c4c0100b9460540c080301c41a120000f0054040d44480d0140c00654180403010741a280340d4442c27100301515017101030040c81026420f0303405036a011142169680c841d1304005015110441c1c0182d440341103132644008050f003000e007800da201d220308150340300e20340d607101800f41045c0d04840301c0b405a00100440ac13400b194514415039044e0041c0e0b00141401800000b2030324000c0f19421038642c03c80b140c0018400036508001c940045440040c09000d189 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 424410575 1250 424409325 424409329
    0x180209100f181a06160201180e0105041d07090b18012409050d0308150a0b030103050c0612061c0602030c0c12040f06140904090b06040b03061b1318020403050d0c02 72
    0x88940034000800030060300c17010301160310421100c20003024070605805070541b540c4805000c0c800030321455220309e140050381100312040c0140c0d0300c04240392501030801e0619000d05040034000740c884080e800515640d0322203c00e0310740d11059011b040c1444040b146094884600381d040d0b08041da190b0240420b00b0801c00c5030340e48120103003654035850300e448403003600c602401c40c00b880712444c1903070742c4050150004140050041c01440c101da0050b011a03450b00025014804903110b0751a5081070280014005038150402d03804200740403001d00a100d911a0064650720b080f60801d682100c0c2c00c510001d10b0f03400e2400b0030484100c0091412441500d49890000f5a5102d40c13940d01c503420038041d2086016140c4040d000544885150140050140c03a0305880c1c0f1190341c81c8104c0300c0500c1760b46041304100b05070074009141c3c0d1241100040f003d01114640250000e103801120640d2120300307155001058104001084602e5403000794400f50300c0e207003145401801c21480340c96032400c00c41110005000340e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 424411825 1250 424410575 424410577
    0x1080f100902090a0801020a080601021603150c0c050a050c0109230405040213060e06040f090201090303051303140a06050906130609060e030307080a0c0201180209100f181a06 77
    0x11880e403400160f88140c804041071901030304d40e014500c03a510214805c4480c0b50041c1d0701c0d5100300802d909071200b41300700c458003481980381c6000162149403024180d01c200100c2d0f51101811060030304281090400070b03503580e4504000540f0407501a0800c2c032080c00e2950b0414014405030030351070300c1c0300c1d0558290322202d03804450302c809d1544590f89a02c007107010341d02d58040603081d40380302180500c211600d4462801100b0401e03540700d0f0041d40b501e00b02c0307200340106214804090390705958011010b86503071001c6400d50022107210801c11100e40e400800525283e9203c80c240b0a480c004d0b0919902c00e082401c22244020206140c64000c00204443d20001c095404690782d840880024018010f041c504010242c9a04003446440000148105a60007440d21481013141e5a004e020280480360202c0c2030729040b5001e03124000040e0403c50040c6411801a680119104003241030300f942c80d80d0504803841c0541c009140307070800c030000c0414820140079049586001d1075507682d180c0c001c180030400c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 424413075 1250 424411825 424411829
    0x60c0c040f0c0530181e150c0409020a080405010b0607030207061407080d1a01090503030a140c0d0c05010b1005030103060c02070504020307030b040e010606170702010f0f090201080f10 81
    0x483c030601d03100c003c1c0004540101c003040d104402d504c0d400030304e417425844081e81d07071082d0601c6103441498040200c1d200224800600408102d0213043e0030680c8041c840d0641c1c00103008a6521001800041806000f9101800c120a1560b940c0e00c11414107042c03950864100c0c04e40a40640c0e010400000480d4000800504966151402c1e07001846007a100c56454000c085008181d00d0f0000391684007420207400c4080152031002403c0c3c0300d07040c81801550844050f203c2c6a0b0075070028030540e440d40d40284035461114032200499840c041e59030701c100f42010344075540c64011402c00c140080074008244101c2c50421400d4441c081d41d000704d1074028125010501c07000708041e40300c18040050034130034080359005100c090419901d906025202a000d068440e01150041d890403a1161001c10140622012500c41e038481d040d840d4500003198201c007000502200640d0b40360212000345030b21034814480580a80780c400581122144001800180054840d0041d42001d105214070a0b001c1c803034400c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 424414325 1250 424413075 424413097
    0x2220f120503070b040609120f090b0702010e131d0604020607150905061006110102090a090902180408030402100f02060f151201060e1b070818060c0c040f0c05 70
    0x4030030305a880c0103840c1d8443e8150050402100f07a042c030041107065041550070f41d00c608445191494803000440745c0d009000398a2001403154582000300c5003007070004110b145c1c011314010441848060201d0384000558410b0002180d03280310251a40d51100044034000740084060074250030320781c00103400c1d80a0110050010080728442583c10301403580880f8a49500a041d5034542c603100442c0380d6180720034890701d4003041e10408800e01d00b900610803240d803900f00a00c9051540d040402110050040403812030b00700442c401c048610b50341140240f03116074802c07004507517645441d2041c0b0804210f0306e81403e013401201040000d0090700810030340d40c07084000c0160341c50b81d43d810040300307255581d11003113640090b4605120101e210f019086041980c0281c000c42081d512041c4913020f903851304600e043e142400c1444803070002000000240349201c41403521940c20b4a44200042032507200c50141d400a9000c8541c4449a0030700b406110426415204200084545048090000d104441e0020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 424415575 1250 424414325 424414349
    0xe03120621010c0e03010c09030308012d09090201020c010503072313030b0618090307060207080f0c010b010e04020a05251a0f0f07211e02220f 63
    0x202088604405030041d401001c002445204810b200c00350503480384905440c0694245186100240e004034055011a0f9059540c000c1e143c0c80c0406030241c110f01d0008c0e500042c1010500b40c0d00f0080d42009032406024500c03400074060f0300c1c1e4400079143c5840d02541505110042c0304014629400032035000c000240088050108070000c1e101113840d200f40e051400161902c0c440110070b1007882041644240d0307054903210705c40c803000840c620480500b1100700c0c0c00b0303900402c034450000308560060689980701d080220b0038503255440e14440350b04017001070780042c0e64840c2842465a0f10550320f803040c1105036411880c140341c20200820714411801c2c8842800700254904800d070003a4003e0101440e08000d449d988101c81c164020001e8000752860424200001e010803001100c00340064052545c6803544044440145105526500082154003000f43d4403181c6031000303c00072171003041c3d03000340040041e900c8084102c158803000314000007864843c1c40c0a024003c0014229034030094600e511000c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 424416825 1250 424415575 424415599
    0x903090608060d0204020406020703110d05120f0d05041406070305060901090b03030706060b0301080601080705030d0807020109050a03090609061e0813061103151905040e0a050105090c040e031206 86
    0x41000c0f054104030080d046840007800103180c5501050031000c0d2489007640404000100b420001c042180a074003030695000340403500c00641c0100020301031030748010a0a420400f982d1500c008032002143c05030350403112850720480c80042401740691000640c00c04104a040c84000b196086905003e119000c954662024480c1d0381c0c10402e0361003050744960103000c81501c445c620300040d0400e1040072264442e4500118904202054490a481000d0000c1c81d0002c100407040b20240006001181503541e030344881d00104d5000e103c43c50015000351034907503a00e032500c94018907011807a031080003004290159041c9500740c50701110b11201143c581400140c503509040261500c1500004260038901800107010b000804080c610400b00c2c42c100c214040d982c1800d021415007500742c0303c940380b90240002d010515041c0d118400d86284042156000030b0903035642421500155520201c56103d03000b541d0083c600384c0100203441e1030171400b543c240000294080340c80f58018040074407400c00b403044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 424418075 1250 424416825 424416829
    0x30711100302040b190906080f0606070206040909110f01020c03060f071808071406090904021302160308220c060807020c041a09010509091e0a0b0103030f090504090309060806 77
    0x10303038001d01548030513140d5412126410007003000c21540000c0200702e9141001400074001c0401038425030340204441103a6540c00104180c45d03201e102b0899120304c00b404045200080742c451080d5441c85a070081122000101c10020b41c013915410381d504540c011b041c17401441c0c07000b1030040e8200000000b10b12440c1c40d9160282c03510161808800c0c005120700d50300090b40000041c010f002c41c0d00c5c0846002e0760a01c20002e000c86803054000594014403c40301003801800c10040b200020300e1086401400d0508141080558852100040d400102c80c403007841001a03640c8000c1c111503454040f01000e06071071f80e031501d00d100068032401c411b11840300d0000d61300714028040400108001001040902141e86030a8020342101d150070303006401d010004510342c100060394034024400200100b090b0048000b10014034101c1c0c5941451038051501400000f514611400d40030f180b02ea00c60320341c014144180100700b0082c6a101610660401c0340f2100400e80044011003914018a0010322982d40c01d40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 424419325 1250 424418075 424418077
    0x3f12151518150406080c040b0414030a050105151e0f0607110d0b0106020c0d030519030204091505030624010804110a0801020310080102040305060a0216050f030318030711100302 78
    0x50398002e42494010800b40d1001801003040e82c51548400d0003646400f106007000d03010b40d00454082c02070170003091241809032a50030406543c000c0c00c54900003003655582d400d403541500c0a0261203000705001e0706901e0240301001e40b9103040304600c0d4100300c03050001000324410303100240c00b840c000605002440384083e81130b01080805000301085030708518000c00c2d05c2a0903c42c14006008004c040086481c02c45040e442c0c00b0303090f6039002d0500e0984201c488035a50344068120615508000006000303800e402490071718019038002ca03040c1d502c0d0400341030502c0d00c0140044d1890a0b040780410701020304103e0511400401c1c44c000f116a0303150300c1c00d1100303c92240c40c01c90b441070017100300061040054004510951010303954030b0700c9540d0742c22060300383e00a0340401003054028400041c84004c20b40c1c05000c0045d1203049459020001d6210349080c403240c5124070146c0c3c2c1000007001003100340c1140622580c51112b00445ca000c540d0384403c0c4200d103042809034458150045c890500a120750 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 424420575 1250 424419325 424419367
    0x2060907091d030a0804020108060906101805040f02040e010803030106170403210903140c03030a0513140a06060f0302090f06120f060f0a0504053f121515 68
    0x50103c0707503103d0311480044c0400c0b1044400300d00164000d80000c1850a1220146002d200054100f1011442020301502c1071104080181c1720060300300030014560f51035003d00078104814400040e07649041c4421205201d005030000c03e031650040004011040d80031480f0489019500059440768a4901e01103c1090558010320400c2c0c8d000c0b200014036403095400610f84d5071107511403500600520403800590301a0210381840d41e0428000140b0441482e00619441040e014946120540d15621111501044004070080c3e07031050751003c040020500c592009800712000840c041451a0b0000d07100c07800050071b02c0700400c450000305130b25490b543d005401010014084e15000803541540f03690718101190407c40400303480011591920ba07d1198a01840e00200501260100c0e100807640c2c51440300e6403468440f44030741686081020310000b0040190b62130480a80d100106000305a80000140440c4551080c07507025240582d0b034951060b241401520f035071511480e01e40e9490310005a42 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 424421825 1250 424420575 424420631
    0xa150e0f090303010b0f1804050a1406010905010509090411090906040b060409080a0309050a0b010b07030e04050f0f04080c160503010524010e040b040c0908060a0207030e0d02130f0605030d0206090709 88
    0x20806101c80080d60b60880c42050bc88518101c00d2540e865004642c091040c4c490180416030402c40c035015070818202c1580d11030b010398856515680200d021800c86c50301101e6001316904218288010050261951a0806411941400707244c3c40760f10351800502c280c0010704107040d5078034864020031038140964034003550456540c0140b50707034a0707503140c60317a44c445582180060650044044146400d1089501039a00002290313920364813040c440c0b03a5042c01500968044100b48038202540504002600d5208050440071424919050501d801d4501c080c1140c0c203074507815944c83d2041841c021402d0303c80142440c04140600352000860014014206c50a4020b410079807004034443d0480101e5080b03d0042d81107690554035200c020342207015401005000504000c1d82840510385807011000349800103141d0101c0d6001000b41d8400c46002031100e40900d5201c0c4810001403074103118001c92a00d050011300b00074540002156110038060082d044095940d448084103224802e060f10104400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 424423075 1250 424421825 424421831
    0xf01080d0206012d06030b0f190b07021305040501020a110f1b0103090c1715040b010b09220606090503010e070504022508030402130902090406050a150e0f090303010b0f1804 76
    0x341c0d1802806007441f201501d0145000080010603400c0c05583e440c03202102c7d0602104043c10071110405a50000b01c040e42e201d1800c03580469040e107540300340c5002c1c61241000503926107030351101030702034404083d81409035040318101c04614900428594a840c102218005030b00c0360650041e00103182600001e45000740c01d84010070340308188207000411100b0f00c011600600060003445074041c5c02180c0040003c4107020040042c0c0d2002400f402c04250f0084c601010762081188940c81c3d800c50100382040b803034458004119094220b002d1780c000d0842a0028801c0080d2080001e0740c87c5018482c0d00e000351703400140300002400000f040c0c2d1240321040400700d207503421801c0600b034640003642c0c01c1c2c0c460141100301003510b0302a4464411032039406810405150303903548072003000b00300c01032401a45a4440d00380500c0581c912110502038041c800e40e035100b50802c112221200c0d03a00400e01c0305964000c00c010312104402400b603c11781e10801030300d02e90b075818400005400101034a25280c000d41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 424424325 1250 424423075 424423079
    0x1b0307080708060a0b0d020d03030f110c031806030705090108040c08030703080f070914061605011b03050f07020c131b03020406020d091404020d180303050f01080d0206012d 76
    0x443c2c05402002c1c0c000b000d00002c4510020811080103400d8029404140f84880c207002901039006800109400c000010b0064180c040f400a603500c04445108160400240c400d03900c40b65820310318482c03c040c3d50040c10362900307800140c5148030f80000c05041c0020100020104107806d14008054888082500d440c0e003203501d0044e013610010f84400b00850760500c00210040c2c0706186040846005811800c904000300050040b1540503c00d100c40b00c4110b8241c81012503403d00841c02d020740455800500100c803201c0040c210740e00900ba803c20311401c01d09100c8407950010388a92501021115126200c2502038110000c0400c10044140400c40d80103134500b980d01903024004032541d40e025035600300c041310b100301c5031160180901c0c1141c0c0302d0342d05c649802d41001d0f40903001c2c81d000d0107800141103031185464080003500c80c404400017500c900401c1548400c0d40b481d01c1c0180410320003081d5140d60003902070348454050003800a80c0300c3d83c18012320b03203045085a00300000501201214042d0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 424425575 1250 424424325 424424339
    0x6040b1507050114011406250c0609060e04060807060e010c060c03090c05030a1709150c01091a1006080a06150824030c1201141302040b0406081b03070807 68
    0x3201030041c100184d0010000000c240100c103d40b8501103800400d001d2174104d502c503051071481002035a0f5004da0720980701c64400100301c0c4030b0040140420b0b4960003a0b40b450007400074001901c0101c0f481c0128140101040000e00015030282a80c8060600b004400065030048542504070f4001070708840c1080c07840100d09800d944055040c0303000d80522031000d0745a106241d540c51841e6801008540303c059900c08901d403030005080d80840041c200019241000b5603400d0781e4100010540150b59a980420104292042c211440c82403401070f2050310b14006112034900c0d50284a4402440300d030000007000c0c1c404560080c070140000024a4030340d14070303000b4003c0541c0c0c01290703c401d56000c210104001400840b0381d050460340010020600c4105030410f05c032041d01c035807142c0e040701d641b544100390840d800204468414512815122030304107090040206031041e160a450040c2e14011040c40542004540b00d9403800a00700c54540890828020130b00d403946591140f0154010030101223109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 424426825 1250 424425575 424425581
    0x5040b1f03020f1303030912050a11011101090b0a0c0c080d0f0902040204080c040c0315120507080607050c010f020304020d060b12060903090f03010b03030301180b09130303050702070302060306040b15070501 91
    0x17072030099a0b5164516190070081c00004249000a040c5901030040d40300040d400c911000d00c030b03080615080c1034184001c441503023942c140c0b00b800c0340d08880c05c00c10044d14040c40c0c032507845918124540200008020385428042e4030030381c0c41144449403988a10801c0048941000c40c2441c5d020704115541d6030340760003140d00c1e0040750441c14032480c00d24241020342031090081c008403e201101285482c2d01d80200111182084ca104580900403c240055040c03401d00c03013203105040c11380706c00391b540c2c0021104600310340881e460000d40c18814800d100158841d0084100f62941c80000020100c44150000344188291200181030f44141404c206d0400408009801249400e0304c000d2405003500f4105820380c4c54274201d450b00740e0300c140010892010000c0300e00341c1780318030070800007185140000400c41800301120010020396a03d24a107082660500ca01548550030b4409402a1410341d4001b568500c0b019001c1c038031513a15001c030022035a50340040d940070200c0381d41b20301c0d98584a516100b406 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 424428075 1250 424426825 424426829
    0x406030501180e100b031903020105070207060503011d06010c060509071d061f0908070305070e0108061501110c0409060506180c03040605040c1d0f0105040b1f03020f13 74
    0x341084103540e0480560500805a5180f8070402030010200300e031079500000d00903555020352610982200484c241e64541510030407500a5001103041c0c0b41c0340038086c1c58280a503008a0400c02d0400040000c00d80c80008804500d0b802c1e0054003040d1100b0380100c1c1c05011014001d422180740000b8001c030000001603000464210402c566000c24a1185d804115141128000e800000020140e104121641c0740310406104d0707410300703031003490300d4480d8989015050342084900e0b40c41200700340200d1028010140c01001a80020703c52854800c15803041500c18241d1103045c411002c03503c130170700300e03082c8584a00b00c00041d008100c158400c0c01c00101805094500b40e0140f01035034084401d0300c45502100e88904c00309944641f6603121561030200074032000b4025128040507500201d01d0403080210055040721400c3c2c8130301c1c1820701c00380c20182c2000c10703407000e0310440ca8409061401d4860b000124901c0400014010007600c0b1310070203601038490681c000a22810000d070301c03241d0f42c0025040ca01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 424429325 1250 424428075 424428089
    0x601060206060a03020f0405070504032f0a031119090c021f0c1b020d021809100b1005130503190b070e0a1412030316030b0f0105040611070305030406030501 69
    0x100740d458440902c4854803082c00082d4120108814500044c240b80d00001d03003180c954607001d403034035aa80d1180c0e001a81549415041c04c0d48420311078801c000010380d00240500c0855603074907000e19680d80c4281031509011024042d07a0200f91005a04000e0130501e00103002e4428140322a000300350300251620030542c50f1800302d90710110a406268014403030000000322035200e6001d805180c00d41000c407840d01e00c2d0103c0e07111803140c207883e006032210204165100c50f1200c01841c141464802d240c01c028000358020080c0e0310b8580045465622612404181d0b8800e0600c1641c1d407140b655a00c2480c0169001540c040c81000c500440c2040c0072000b03048001d02901c0c00f40f000da143c000e01290070202d0100602c0e84480f41d414240001c00d139400c081da440060040100c00d03032080c0f07141c100741560011608a102440c00d9403803524039a8041c01100081c3c0030865041401c2180c080001c3d24070f0013540216010404a45030284c01c00404004a801440d004021a030326155604802401350400740500303e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 424430575 1250 424429325 424429333
    0xf150c0c0510020a02030a14070507090b09150a0605070f050613211e050705160503161a0705150103051006090216060b01120218150307050a0318080a0206010602 71
    0xd50791046900c20b4500304490340d8055447c04403103441c1201c03003180800305003c11a100300f000700005941004a20001d100c001d101041c4400c54904101240c0f1005141007511034000401c0b540a99a04022409641450410750b450311050b0070992030110f00c54030b0080030361140e24180600710300130074200d0703417400d100d409680d04101030708c4030340c183c985c030008000d1000c1100e0212034402d208107a0580542c86185141c698101300064607040c0c588090000c9640402581c0c40041c070071400c0910100f0040e003240701d0380c59401c0c0d14108400030040403150100168203804200307201004018411001c0c01102c40352400d00da540c4900301284c42e00d50703440d2045d900701e19015000074155501d0081d150040c3c000101c5801084860b212103002c0d00742d035401c031030410094050302c59000039140b003c6c00602280015a018031000c4030f0a001c00903628260796001044c046c0100f14403ea48a03048a403894001d18000c25100000044200c64a441c600010b05030200400c0c65981d40d80d000842e90304036402c81e802c035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 424431825 1250 424430575 424430593
    0xb09180c060705070e06040212070c02030f07050a0b0c010b030318010801050a030308070807050c0a060204030c0803040b040b0f0712120605060a02030f0913090c030314090d0f150c0c05 81
    0xc800c03403140c1c02005003d80c210035000c10404614508241c2d01c100d01134800352800502d501d9030381c0c1000c01141c0c00d00104603d410a01d00b582010480d2582c10803450000b445181e0809d0009007604c0030700c0c899a0f1034120300040801c0090801c0d0001107a030403010781142d86070b14600503101c0e811401e540459002841c00d10000030541380c0307030004208880e00f64a4a107522384480008440160f8014000010300c501000400f0000790100203044010307000321030058a6500b14034100c5003c000341c0d804216240e1052000f803141200c2c1e10119411a03084030700950f0b89520715001d031581380c01160383c0982038440d80d1001641094000c120040c400410040420889440d00204010750040e0b4011600580c41480210f0042600390002d0a050400800a682c1801f0098840040da650000101c13440d0a10040420405802c40f00889607040c0c00d0481d58204407541c1e011501080207410003410b5503040307001041c10b101d02c00b041e0700210503401e00240049007002a000d84a0103010300f00300c0b0544905800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 424433075 1250 424431825 424431829
    0xa1b020303010315050118020304050106050a0b4602010e0615090f04031d010e06040f1706090c0d0f151b020c0616150e1605041b0f030b09180c 63
    0x141c5d6058405ca81c0d924071012020b045e810000750401041142c03950b595800204c3c4940c0c0780c24003540103100100780340e43d5071080c2078185013202681c0c020507510241c5410b00c0c0c02c0c008000e141e00b40108505400c508030303d07032041d582c103d0141c4440d5161207003501031602805040c0c0700c055440c4214600941d091030361512004e000d295070100031100a4006a40d0000b407110708480652000603000052411801c480079020010b0b08590003a03002000410540d0307410802d80752002040118035241401a04062600408141e29039081070840c0d0721540d54007412074100309082c1d801d20701040d0004079a001114882d40340c0300041c20f204460301401c1103011740380301c0d0307440c800500d40c084d140000d0480c60a0032800c800000d01080700c0f48040324951040e14101d60708642d030303200380802d03649010300604910102e051600e10b0f540494002c40d00590911503a580c03440c0c0700341e40c42e80c1010018500399481c030501d9002100140541c0c6240c980c8000783c202402182c40c41903024001124100007619030031810201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 424434325 1250 424433075 424433081
    0x50a1b091a10030e01021209030310081c030c1e020a110a0b09040e0a12090e010b091f12060603020913021e07050a02060d05100b18090a1b020303010315 67
    0x620580d1110b2003903042d620080c465003212045130800000035042a4014080c14480c820846e80c0100c181d1002c420090310900284c8403500a1070f6920281c40201040002c60604491030310f501d5090585501c1111407441c419103459507951a00b4005000c2d0362441000203440c0c414804050b80d000782c1c40c6005904a1900c6c40984049411003e225480c060040d070620019100c403850807001c4c0c0c0140e1114201158200744a2511001e00b1740c0c0f464071060416000e00804201a017000380e88080501c0700d6041341d10b800074908111f605082d81c85018001c80141240d070102c296100402483c140034001815a4068000d03241d20b0300100d81040100c02c256030707410124090a40c1d9528030790700d0034031044c055100b04030003082e2480c000c1c400d0340c1d00781d00d03160080380f85a40b11600030070040341c1e11420072410b40250b140000240507402c040c0752608140903001008260340640700d921070189400442c502c2003040e403001201000748910107591200b94600070307490ba00309100070f4400c0503081d01c51004070000c0744 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 424435575 1250 424434325 424434371
    0x6080a0501090b0f0f0f0c27041407120b030102070507060810090b130b0d05030a0f080a151707090213060e0d020306360102040501020708030a080106030c0e130b131b0c050a1b09 78
    0xa0b03601d02c9480b8cd0340314508040c00c0c60310030b4960155030030000340b000720701c050241c800a032074652944112800c00300c1c24203ca41d005588035044e12442d024881c40d0998404500c208e40c0082c90901141204020000540c0350f149841d00500d0307440002015020150030110074503000109454114040d9180084a000d0f10301c078180e210644400e03540c0c203200c42c040300c80241702250b8840046404494451206008a0b40042c1460b03818a60706101044800c1d401088181c0e0f43c00203841e84a6801d154ac2d0100382c0d1500f02501c5250079100c402054001d5020308104c22048000c007803011016502e0b17425405000354000e001e980e0041c01074607130200312102c00104903101340b07141382c0e6201070a07860500700301e0040c113079078203204204010321080c007c0e036540e1a0f0940d031451080210004440107080204404000c200000c00380d42814018103c02c00714418140240000403400c19020211040c5009030505a82c80d00c0200b41001d00d03009241d800c0300c00c100000603a04c2a042c10810b80c0f203186e0b60018104489 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 424436825 1250 424435575 424435577
    0x601230702150d24080309010909020307020f0a140d0203070f08030a020706150e070e13020912070e04031404081e0106080a0501090b0f0f0f0c27041407 67
    0x400580c0010709040b2801c007410900b03440c6080c10414001a00f80c241d038134039200e04010340d07038200580303052035201c2e010070f00100800c2004510b07024124002801e01c50540c45110300c11640400054400342c028419095209004010346021030054505498204500d5911208500c07032070a250564078000000c652403650014080c2030440300c1562092441c1d803000f008201d0032a0244001c0c800190180904201d03604e4284440180c14140b4164040e00341c00281044204010341c2406407894552802c20340301180481e1000d40d9071040a0003040c0a803883c400d82d0038040c40340f001e00089440c050b05030180154800e07580c0340e0304904e54030059901b0303000e54040c4020b590000845040700c0d14000001041202e000000452426a83d01da05401c1c146150130030f5529075118814001000002c030481903000d424458802080e00340303000c47c0d8101c40d500030a207045500c01c1c5804220030418140c00c0c0d500d42d40c1501d00c00e01031a42c0c0352000c480302620301c00040b4021400d100f80702180920484e6050301ca0001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 424438075 1250 424436825 424436827
    0x503010c17090c150a021005060a0504150f120606090c052a01060b0a120606020705010503070c23010f050402030613020a0f0905072a0b1518060123 65
    0x5901c2008407400140107400386110b05850304040b6100d0780c1400c1d00c5a58a0410a42c80780804c140280c1071684442481d07041c18541030403c03250380c2e5051800c0083d20410350340050b8949540c03a0308900081a0f801c04020301104113000030b602c220700007079000017500c1070a0900c00c059403002d6020988007095507120100f241030012608240e03540130a40c0100c0c01c04d60700440f00314610000c02d03007191020780007000200c9001412440440d081840015510118081007060a180c01f600a440e09414040da40c100b000000110345940c2c403419007035040640014400c1d4003c11455640007410403d0303400c4a00e29400c200240003101c402d031052912564001d4043c05050b9655140d103505581240002c03603200e0015500403908580d0100540d01a00044034001010300f002c180150140c44011401d0781070716520f0320151090700c200025140e85660100860626440b1310207900c0d003640ea651003854100618480121540001906283c041c2c0c1c003e0702c900100700521001540e42c42076800c910400c101d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 424439325 1250 424438075 424438097
    0x24060712121a0d0510110c010b01080903040b090a0b16030e0d0f080c16030b06030c060c12070606090207030e090c1303120e0909071e21020303091003090b010503010c 73
    0x82900c1d5030b03003c852003601500e0300700d02c1080b003000448461581d60a5070413004a0840c1c2e405400340b048145040c401d0030920110b10309800c100703a42c0c0c417642c01020300e002800302d4140081c0e15250b100340007134412242c0d4180c80e402d40c107903e0a5004101003090340081c1a40d00e86100ca420400d010400194001145428841d000e031030794809a03204004000c1107100d00031300c1c0344648222070794000166218198107601402c0500401d0324104544425500c20203041000e030304400b02c00515081c007019141c1c8202d13241c49050130100d0080083d98414060320340001440e608160f0301407059400d41d4412030f0041c01c00c1d1191010060740b8092007a44201d0140c642c10309001180c80784104e12003014003071078210366403010071000c6000c00c442910410481da20110b030074885d0006008007948040d01c01d11405120600d410440b01243c1d2140c160840311f40c03000e410801c01d41d1070a10450703040d40030181041d429000c4416000b00100040041941c0d110380070000400c003442c0c18001c2c01d40619413541c030180162 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 424440575 1250 424439325 424439329
    0x51c0605011d01020c04020412060506090702031206011206031b060f122007080703020d081303451202010f2006010e150a060824060712121a 62
    0x15400b41146040d84205145803141395214001007010300b0170407a400e0f04040d0145440340076120003034030b1036201d013881004011000c0c0d400400d032000418403003881c10850716607500589101115a1040380e40a0500c0404802c2c800621020300035003003c5024102d444c0d0395403008130b40f100503034402000000c607101c0100c801c4001c1a00308510342c44601d00c00d00c90060b250482c00130903a1200c4002c40e01c00101095150a04d0b405000000303040e0181d062828592500e8000502d407007145440003028046120302180c41c00c4440c05040340003610045011080c10340d07290100f44844140f80c1c0c440c100311030313444011650b05102d00d0f12015841d4185c48030302c10380400c1324040d1042469041500f42401440d00170845400702000454000c02d203040d1440414244000340b03000c83c003081301c41c00380a0814030034100300081e031080195500c03407072802441d43c007a03021703190200c41d0000d0680b0807980240e02061601c00d1101450707a10042d0003098407150703207046c00d441e600400c0e6104500321410345146944103000c0380c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 424441825 1250 424440575 424440617
    0x241404110a0501053112170c19030203090a2d030507060c08121905090c0a030b060a08010e0309030f0616050f0d02070c03060c050c060c0a020a0209010303051c060501 73
    0x740d902c281c2d050700900650750f1320b060845d00390340400e01c1035040b5820042803266442c60007050200300d661243c6880604491186d50300704044800c2c02d01c0d0711001e8480f06140c801c4c000d40d410402c00402c450300155030340344c8008007401c00052140680a084020107a40c0c002c0f000e14108803a40b10010340217482c80c102013074503014071034001560f017810108110360b032410a10090512078501e0442800441024040040c11254001c2c0110030702d500c0510030000b80d070343e0350815404032a401007140c0c0085d616540460b483c8541a444070b1010f40c04d014450103000d43c08030240c1301e10704c0300780c00701c035108200c4008540d40c81c1c8050310105201040f280502c000d06215800504004401041c0145408100080442264460b10050f90b036266001814002c208143c02075001a04540c502a418041c150540945900010305224540300d03000031210f284034002d02889210030f800505c2c1045941c0d6a040103826170b030024a804103ca041d96081c00c0800c2420300c55102942e0060f0b5a00750310f505140201c03080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 424443075 1250 424441825 424441867
    0xc062a030903080f0a020c0a0e04060c09080d030b0301050c090a060804030c080a02010504050f010c14031902040308130f140103021c180308010b090904241404110a050105 75
    0xc000a070703003010012820403c000c192030100d0401300b0740c0c0c40d401c0310802800d02c02c80c2d040b103520404001504000b007040404065401c160458130014540b600e01c013090ba0060303902e1740011820b000f059260110b0b00d40607401000000d00070f42c020f01c090f83d00c0304504080c0e48140c0c071202d0b0740440180342c02e01c8294452801c01c0e9005100f8100191410041c0d1a8100d081e0031024407100140e4440040104005007880040b0741c100c10039000f40082051765001a207100700400b1810b811500100001da5101e440e940580414654074004564943d00c9003065503580d40505683c2000003281880090b03c000e0b6001144200ea080603094080e840109004501a6004035040300c0c1200030500d0401700c00c04544217524040644c21850441c2c910342d890f02404900c0164020800d56005000d026aa40c840c8401d1951040c0c2c082c0400704261400002503911130164040d0141c6d1030f24203c10740420792041d02c80740e4010b900400228502602c0e210801c00700f0301c2c090003102d0018205004050081142a80e0425 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 424444325 1250 424443075 424443077
    0x80702010f1b3c030f050103050618030306010903021e04050709090609111b03040b04030b0f0c030912130308070510111312030903060203130c062a03 66
    0x3812811001524040e11075800700b0303860100c440c0c040800840d8000ea110103448190b060109071601042120400c0d54030204440750598010100c070340016840381d80100e11180e45040100a2035071070b810b12683c1c5880440c0e00b02c03008505001a148020070000540e0300c6440d050f0b4508014500350390070f1080443e0030008030103400b100c0c04524100c50703541d809143d208440315600c0041d040c0c0f6000340c200a0b02e241e81d0080c6070380303441c2080307038400801c0400890329503030206008000300c0c44955800350700d544504c0e031202e01c0c0400081004400c001e011010b02e4000d41100c2d201c54050303204d40d190199184826a2000b140758031103440840c0c4400c21501401d10f000b4002d6070140915541c1c1c0f207901c121f501109040b1090303044214500c00159642c410584003d060f82041e90500c0d480d4505200f20200b43d014a65501c0e411624050400d84a0070070540030f1940120195100d0800300c84856190389400310444404450200215640f0b21400a0581820b070803000d0918403030002c01211002e00040740190 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 424445575 1250 424444325 424444331
    0x151207030b060f120615042912030f0c0105150a0b0304020108060a0807090e010e07030f0807060b06040303020312160c170f0c0a05061323161d06040204050303030708070201 76
    0xb0314400c606225182c89140c590120020011502080104403070807004211400c8c416040c0403103400705001041070701c0c4182a9003200e80f900481508520354090320044000c21a000624010301200641000d0b0140180c8111108003102100400c90902881e00801281060034000600558030991125800240107840c132002507807921000c40c1400200d4104400b150340707514403030f02c20300300c244210010351920750f010b8010b2a00f5659400301030b260320180540203401c042909414407410307521510381400014880ca540310f41d203160103522508400300c2c4462001a50b40022030254520903203d1844005950781e0008420303580d5240d1907119a807010390300002041c010031200700c004400824009200e40d0040c51100d40c5131030158034080d40105094440320004000300000340e01c0901c5030a4941040c107074075405105a83e1054070b4101d968070909811100b4000009207800212050001c4105090a080c46a9103003c184016840b8500c80c4640591040000903d110301c10980d0030340201d9984008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 424446825 1250 424445575 424445599
    0x70e010c0c090e01060e0105040b0a12060b100c02010f03060b09060a0302090d080408070f06020d05031e040303050a0c0203072a030b04060b0913050a02010e03070509151207030b060f 80
    0x30421035000303143d5586641e5403881c0620003441407640503401003100b04d0b0280141549240815091030092003a20101482031200e40d082010541100200c03a50180c034001610081080050030301002c0307441603010400700c418101d9090300c24010a000d4070040414076180840117420301ca05980902d01078030805a0a001c0001d160f90f918090204c10f90085c920346868070b0030703c1d6049041041e50781c04a54041da032050100301e191340100d040e095005036800e03c5510b03a902c221480c0d44c400c00711901040ca00303030b011040100305074059000c1800745d601c58800300b1909a074036070240da8a00c651300028240018500351501040e030306079040135181038283c000001c80b40d45c9035908001c0a409075000c0701d03800e40b070728400000c90030202c040c540d2000740360080c54034448264a5107900d60403103130000390401940b1200341a084d20704010000080c00090a05041d078a40004803c0001c48a8008548030300079017868844140780c00100c1d0400c0e02d8006090100d19218082000103078204ca00e00550013810404036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 424448075 1250 424446825 424446839
    0x1090e0a021c0605040c08070206130c05090a1b18031b0803030403050d050a060e04060b2101050604230c0313020a030f0312060812092b0c0e070e010c0c 67
    0x303038400080d807049020481ca401c080400c0706031b9121207100c42c1000901c20400556a500007103175a004185520390340030b03d0b8102e040288608829030003045d0020180010300890a41c41d80c0440300250005031400360300c0c00ba0110840e10f01a100030580f01003d070203030080c800719814121080d1a50720a0781c0410510b995000d86d00e045030411a001d038003061020030341808207800c1d401b45942c0407440710010400107040058003c52070300c014102900740341d81c40c1c5c58145261103a11074140074540d001c01010031010710115032406070404070b80302800f441c10802030340c0754950714103644400500b20712804c501c1c56860b4148511160002000f148280144111402c09622450215406540502d0700306d0f210310740724200600805c0800c40340c91101460003504001c20344001c00d40742c2c242004000440c4d501c000103400030700d60050072854003400c104000c0325620b200034450140340806202c2c1d0900060b946d82d6140d40d407200070b01194044041580000d114040b58869201c03020402d2180f0803c0c03000a0721130134 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 424449325 1250 424448075 424448107
    0x31e01030507030b0705040e040818210c030a02060a121b050d0b010216050f01090306060b031605070f031b060e060601021e03071707050303070309031d01090e0a02 72
    0x80241c41c1a0014501481400103070f0318000d52007111400c1042ca01460080868401640180b000d050340c20042414242000198404030340c0800c010b1002d80c220358040c02c0458000b4080506040a128668002640b400c000c01c40941d03c41d00200341e9810001e01c00c400b650404024500d583d502552040a0700005e074040c240624003007180d5480d0364480d000100e030041114000c2c036041c0d0641d0b00401258900740e4996240d8019560203950035120190040d005907071801654100a041604050000c58840303c501c2c0a503101d44400c03c140034210140200949062240241c040c01c032840038102c030400300c5d002c0c070b5101c4100388046a4054075182a81c541900720340d1038805070320344ca40050b81489900c1d03904100b031142d03006110300914030005044000303136a207120b181c42c001e0001840c00307800e42640d01401d00f55003240d41c014060f41c7d9a860650780c02001010418000c8001c1a240072400c12141c43c4040c408010000607151454100e050070300d031030802070f401864004800e408210b0010754000d400b03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 424450575 1250 424449325 424449329
    0xa030b0109140703090b060111030903010509150627070c05010f0c08070e06180f03030c21040e040f050c0307030606050306060102060705030f0a111c0e01020a1202031e01 75
    0x9002441c0d114122500c4142c0702c01034609001c26050040035004074150b20300c0c060b001802420240510190b021080c0d0941c040c110300a541540f0304010051084c001160303804801102d0603499503196030f09010413407054400c40c83c10178001112003040e00005202910303141c1003800ea0520f0951400f1940e0b400d429503403c0f9252007403640e11550303000074036504030040e260425082c0c1803010541481d40040740d414001c440b140c1c40102a071880604880d00c50031000c0c0300808001e401d480d6a440c0d00c0c08981c1d6101d59540301e008901c2c9454031080c101058101c00e46003500d610b201003948584658403507107407111007010192040d009901d0550a10b9404201d400002c5104500119425140c081010304109006108a055420000c10421110340c007030100c0f40d2001007683c0e01485a291500d1075001011481c0b00700a5a84001400e41030f07250400fa100086001050f0080c009856a10101420b034000c802c00b040108007404c0ca00d001c2040b05070065944200c103400700c80115180d04000c06002002a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 424451825 1250 424450575 424450589
    0x1031101122d0605100804171b070f03020604030209040201030b30010209010c1407050d060e010e0708070b0711030604060b011403060102070b0a05130b09030106061d09060a030b01 79
    0x40800c1c110011002d04407110300e03240d0290402600d8504004121038110b440010410810160006010840240d5103000e03105191001c05464070318212555554110400e401e18a83c415007800242e4240001051801e07241d0141c4240d0600e4656807e018800c01c000e481203040c5516030440481c0c075203d00c041ca40340368400700c0342800c4074000c81c5101c2681c803048a41400a50740100301401d4981d03000400700c085d2960101c10405907810011080c0c0c101f0299801c820340c00844030002074140213640d0031803018010340e240204400010400c3e02aa00d4100744203450b40b40d0090442000b5a81450700030b071403010300070440c00481c801400000ad0030004100da007210300550320b0f240005196801801000c401050650349443d50a1100010b0740d1200144582c078490400055a054400c2c424425900e20040c150b6914076006c0d02c9807030248080d0002000503009602c1c190002501e580720b1035103800c440c1311a4414000c090b942500f40804c611004bc4441c0d04507050a50000002e14001c03040340c000c0c511 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 424453075 1250 424451825 424451861
    0x1215090510110d0c1b0809031509150711060c030a0b0307030b04110604030807080f09040212150402070b010e060a080a0b01090b15031302130903111e060103110112 72
    0x8a00609000c5809808054040007109100410a17441e078040e6880103030780100f6105d4a0700040d4002030310b440c06030314000c05042c4011082c00648000054040e107020700c1301c00082141c2e500d280b0100c4410841c940740299540c00034000c24030018a4200441d006443c01e600801d000d1458000b00c0d01d03040c1294011100b0394551001c0000f070001c0f00c401d441c540079003160085e14051860b200da00d068000d80d0409400f44100180b001104030401e01100d0740d0f442e014000359200c00305000703216400082121401001e140001320f41c2d0b11483c00703208544070181d204200d0040c0303034202089003801d208010031340d40e000021110080368802c020010744200607c100001e537039541c1860412000d503a00680c18501454481808410240f06c0e0021380764004203103103021510514900001c0d030f04800d615681c640c0346103400038490515502040110203c400c0e001180c4e0389102d100d20314200404610302450450f04094014800945441c00d001d03290801450301a411003102c208410031900e8a240700340100345 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 424454325 1250 424453075 424453087
    0x180c03031b0606010309031e02070306060b030f0f070f0e0f30030f07020f04061809050606120613030527010e090606030a090804030f0b07020601121509051011 70
    0x4040142e00e51010080c40c2c1441080000d560140c48a08103d2a100c0d11302500704c0d645602c5071023004602d005580001045c480a96100e002003081d600c15240c110755509494001346a4088132003030b4901400c565550380c0d080182e01d4508844540480603800e80c46462041a60213980c1c80040c40501d941051031000c101c500244164503a91040100c2003140e60824070071004600c0240050b01e25a940540300d03059400d0542c00090014201d50308100b10043c80303624601950384495021b0f06050307110394201d80ca81e884150800503c500e42110790102e503440440010f40803940c4407140501d151113401c1039420229200d061341000040740304582d842d6035013000142095039100542c4200e002c8191220312550400801060562200411145105498100110400040c1003c035070085420102001e103d01003483e00c083c91520541e007480040c498400046480070750200c0d500c0d0003950102c8240700032881d00b400d20001d048021815242c9019110b011074400089000b907140c850709000c2c1c040d507602 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 424455575 1250 424454325 424454377
    0x6070c0b133216050303041401200706020c011b0321050406090c0b0705120318150f0c0f0301050f0a120b06040501060509030703020609150a05030118090209180c0303 73
    0x4110f5185016070915140e040050b518003004850a4074800990076043c4841c0c4c80040e0385c01d42c110f841b0711194000c0d5a1004104401c080780c800140e54543c0d0a5400c4101547c1c01181e43c1022005071041c00c4140d1080301001901078003107902c403600d00d590856082d5054255010440d42d04890a0b9000b03500c9001e918101b203450440840600008001b5a04200042c0c1710296603450400c500c0b0390b2581c000004c01c0440c811025880003004101040b9000229110f8500001761400e958024101c440c500100d000009540262500310b00d2a900c40c60641e8640010000d81403046c18113150080c940b4030380894460f0307201210f403d07058091103c0c2d0002d810410240700031903205a0100c800c000f014000301d5042c0e0740100b840007c41e0380450f880b903150f41a043c006000103c111014280246000078420503107a040400340d030488a00091401351940d044000b40103460141c407009504c11446000592183e1540811503044600d1400322038181c040400483c3c42d40d40b040303c0748001c40c016912464881 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 424456825 1250 424455575 424455583
    0x2704170408101407020a2003032701020a02060a050f2701020f0303070f050d0212010f030303180b040f0c080706030209040b120d08151f0206070c0b1332 67
    0x140300c3e01d042640103490100c0c002525001e0b4844000c00c074129681d420510700c800c400c0c501400f1a402420b0b03903941c2500384c8401c90b030442e803828030540701c2c03a040128050a60000c01c3e0180e8068014088510f0201c1c0b22600300c07581d602c10a46403011250522990242e8444562030007900015468050750000e0460000ba1174036124141680340d9520070410091410b82c0500180d0507200305091660f124400051218082c0c00f80005ea212011008000001d00b0700c680d0740f4110032640a03407410450100103503e0403040c048004000b070164882080440e00140304011261011402008040c0d07400b912041e01c641008604d0b032001d0000394020400041d10300c0d0038071440b03c41c81030807203c201080100002490310352481a03842410311690500140c032042403a0f50a418441005003c052130f2003070050622140200c5181c0c05005102e840c0009010785c0c00354401542d40758000d51180d00e0b0fa601c1040d00b9481100f6108115542e6900a0000c20219415020304c1140e01088034900440544406034600d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 424458075 1250 424456825 424456841
    0xc05030405150c0405040f0b0907020d12060b0a08040204090c081612150903052503030c11060402040c0507051509061b030606091503091b270417040810 67
    0x1844600188010090400f0403581101d900307540204448500c80301802c000c019010001d604083d25104205450358089034412110302191104d900425000440c03074100d9440f4012040402810800100254000ca0840340c1c00b42c0300420104400000e0756905210b0002913005403003d03401403c00000010b035400b88003001e844c25511400c107194458584001229009440c0800e8699602e0203e0500d4818421031700e08080a000d003802d644001c4292001054900c90183d001030f10b0041c20754041d80c803940301d092816004400070b20143e02c0c1c2e40c080000500c104401601801010011350340050028042005602c0801c44401114a070400030070b0705201000f081c40d01070b00002c03200700001c0b0514400f43c0703422200544070540c48806050204a880385100d42c01c10041b0740210421145050004800d01000c3c08030303c0311703000c49440401340310720140103543d1440900f1100401701400b00c3c03070004460340640542c3ca2a50094401c0d10380d0540c6500a800400160b00041c500c1a00c06186001d5121 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 424459325 1250 424458075 424458103
    0x140108010e0d0e0d021503010f030b0c0703020a24060b07021c0b0c0f040e010b2a070905190e0708070806041a090a060e010f060803070b0c031305010c05030405 70
    0x544090b4901c80101611102d6800c180318500d146203100940d120010301d44c07041384090020075a80d58517055109440010707407004507810750744000003032001e89494042e00c1c1100c0d410b4000f800000318990791046115800001e051400c03120204860307001c542d601070070740104007000000d6920106801442940c3d080000e59000c1f207ca1403942000152400d030031168410008890180c4480c602110303603503148541d910041035402140c0020511420f000e0003040940c884841c142160401e4090240103114a15104800d039000803070b04000f0402641c100e07503070200103040c24111003481d220801d0100c0c0d5a003000d03c141030b40252014013142500b080700401501400c4000e203a50b02e05540c49040088420228040440f160008944d002c102040991345a5034040024071060071955607040c0201111500301d84c0c0b49040010000b102080030084031030054210ba441001c0b9550070340449800d6002410080d4850040e101e110003084081c820340344280210b40e580c591384c4c100b44c201946411b100d0702103e2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 424460431 1106 424459325 424459333
    0x303030c12090b060607020414070519080c040303140c0114060315090c0103180f0302060106081f06110a1a040303110a0503011e0306140108010e 64
    0x400e4840d99410901034221201030059a0038118068103158940001c20b032a81450f1000304002d41c005000452010104c4c4440c181c0a402101c0c04000240f021845039100801d00b46078100950f1a441d03c00000d003410010703511140710f00d01c001402d02074154000310803803144805550a15944100070042098502811151034108898103807003402000f07031015107000d84550380360190581b0b500030300c50954590019002010412005502c0c0303886450b55200065010982940c040d20036800b804680d454070300040d01101021b81109440c03029840c0d0a4001c00c51070300a101169041d00c2d00e0038a081c0407001540c102807501a01a1215040d0032107114105082a100c500891281c2d404010700050900340d1800c501600c58044001141080100118800e03012441e040d402420026002155a651f401d005c07240f02420003a41030103068010081c42c1700030b101d0082001d08d808094 = true := by decide +kernel

theorem cover : BRFrame.Cov 424280575 424460431 := by
  have h0 := BRFrame.cov_init 424280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 424280575 ≤ n) (h2 : n < 424460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
