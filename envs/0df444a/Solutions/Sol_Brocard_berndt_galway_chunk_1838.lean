-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1838
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:51:31.164661+00:00
-- url     : https://prove2.me/submissions/9b528e46-75a4-4351-9644-84f25b36b2cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 330395683 ≤ n < 330575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 330396933 1250 330395683 330395687
    0x110a02030d0e031e060105120703051213030c060815040903140c0c0415050405061e0402030709090504030801060305162a02030a0b040501050133030b0d050606100f 72
    0xd0400200c800b40310b20542100e0160707406102400d4080f0104070011030244c400400030340e0316038007886511b00803a02c07180d10302032503d404101a010707290007800400c032483c85018280b01c50303030080f00540107a1266080c044000b518811100c4001d01d840c0e561060f503400d040e0b000128514140c0b01c40d034400c51511802200280d04100c004207003140f0702d1165a1982d4ac81d165060a0040d048240c66009180001d4146084030328180c200a490054504110070354451081c0f100d0000c008060b40d408035a04206104a0b24058000310750240b954685804d8080d5190300000a5903001c0d40c007103000c07400396001405940da061103240d500c15402d08080e00d403c070202c070000c0c00401c100c0d02da008604405144080074603030700c1581c03600e1aa0f07000d0200d544003c1c0721b052120792800d064070101d80d07950900000181e1900f90105007460845a003400b508030321015444c4000d185051028241031544171001d1300c0596545944170311442d4004e6024000c2e80c64200f04102c603c024098001c030030700401070b1201c00d88603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 330398183 1250 330396933 330396943
    0x718061401081b04050a080601030c1409180a0b070e1504050f0f0a08121207021b0607151104030201090b070b0f041704090c0809010c0806100e0a03080a110a0203 71
    0x3c10140d2160a10305880c0d02c488074107104c0ca81003280c0056107400001442800024101c0c1202e009940c3c0c20305054861510b41700c1e03400b82c02032843e40000040007141c1444400403024060203641011140c180e0b217203607075464020104480e0340f00410080d08059405051a58400404081f400c3c40549010705041c001010000a2490305000714074510f01207000e42c0301c2c0f0303490b01e016240c080101d51208035203088081c40c9034001540d50143c10a8140070030040f03400050380d800347c08042501d25900c0650141403200342e4000c2c1c1410343c2e02245001c00700601c803045100e00310074a8030380c0095a40c0c4a0a40c0009030810300a03034030620080e00c0403c500030105035080c0d07040f5040960440745030400d84850030b0090004074412100d404030000000c000409840d65400030103030402c2c1e500c806e20123988921000c1d00326142c034959140810b441000165444c505503100d00041101400c044908081d0000440c0510b902c03501304603076640700015443c00594019590040480b01d2800502c202d0410380d0200e0340351 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 330399433 1250 330398183 330398191
    0xf0b09010303080109020708040902070503090a060e13020c03190e010306230d1a0c03040303110903121b12030103050705061305040b04020d05040b011518150302040305071806140108 80
    0x5e10350109a003420030004a00302c400906942d001035403125520b041c619203980c80007190510405541d0000100d95001e00564044135000401070541c10501540f600040e501c0703c03141241c81d0100700440f0014018007001111f01c28132a030307105c00010212000240888032150018a0480400300d10400c100d006c030f80350062820410381c2c2d03032101d20b102031401e4200d80821102185a000d074010402840684e61409988034501941e0280010a030006084032148100d80405805030800000f0300d6991403600014985004000b50102c5220a004952810058660325072220342400100400034401e0421811002d00000c5814914204c09205101701d41c5090388141d500a54440c05581804d03034542e41540c00d4404440014011071400e41b90201c420303078090168002e198140c030702c1d0048251081c00194a17074240b01c10400c8942e410814100c0710560906040c0c820940c00300004000101c0600c4400d000708070103101d20034076003000004071054503107613001030741e100080c0c000019003130b80e21000e59500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 330400683 1250 330399433 330399449
    0xc05060109061a0a053705161419030c0516081e010207060e060405060708150909030f0a050301080615010c0b040c1a0a030e01140402060a03140a0f0b090103030801 72
    0x10b01d41000300140d5041c020b0311000d220302ca90b49400080d1880b002c4040a00c0b000e01b85060100107400c190050360f040c01800062040d01c0c40c011038240004124103e03200461540504840b0444180c40152040080c1e0315000c500081c00382000d9810400d042007021880c5030251200c0744070070700b00000d490340e40750501020110119400b100a15001e001e50485003000d41040c000e0248445684106a503110b06a03404c580302c2c0708040c001074400b4032601c0300c00c2c050311039087c9288114544034100b0078400780c081e00c3d0b0061030008000c204940240d074002010180c0480e22030b143c41c2c2d0704d80b4030504d042c9000100312280009080411074103036a401800b104959034008914006605c95090904614200b41c001c100d2541030200d10846c5070b024032001c0e00212840760740174400100c10465a60903a800c540300e040c003c00c403070004140103281c4030018040c1c5d100a0701d0f00191704540b0040c076403101c1d0010b8640d100d10316076030720141c4551022802003c00b8100141c9005a02d5455940c0080c1100e10510403220 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 330401933 1250 330400683 330400687
    0x1d0a02060a1202120114100f0914060f070b0919020105070b150a140f010306080307030e010512011d010608100b030a021608030f0906040b0a020a1e0c05060109061a 72
    0x8904a8a0380c1621321312507003405209055a140d002110000c10b0742c9480700d106105038000c0030540c40c4225001542e0803015643c0e6140c0e07500d40740148690000000606031b00c420180003c68007800040060208a806a005600c05090070031000d030420303600d043e101140826943c04000540d0300b0504441c10705a21203001a41c80e0789401081c44ac0a07210302e900b60380145540800204140025505000464115240c00c0d10703502400c01542159a14444ca11140d0020701001002c80d00440b251071582c0c0e410b042c464500b400180050300508c209070450300305402050120565400e11320b0042c0e024006034141100365041c03c0d16030f08190310951082c0780b200107000000030243c065940554035075040201c414880c2c0303485882c101505400c221000810504e0403000102d0f1b4a400141840c055904042d540244c0d40b91108020040d5100b410b0300010f01040790100d442c800300080810b048461144d032044003007180303403034610305080041c0c0c0300d0002d40342426420f020744018846410f030361a8250081d00d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 330403183 1250 330401933 330401957
    0x70f020103060810051618120606030f06020403150e032205030706050d23040305220311040b0103020306010f0507020d14060106030e01090c180b03030309011d0a02060a 74
    0x1c015004a80007140b00d80140e808610000c040c5800c900e000e0b1182c03200780c03815441c04090484003000040450361490219440c10410405e4824060680c640100c0000c10389540765190410070042d58103040310080d50000d401c1043c00900e55005404007643d42040c01041103040c0010fa4034010b102d2210700d40c0043c600460301040030091207100800000c0c2c150790400740d07503617005456074000240c91031182e810300001e201800c3e55180380401d201d800f210360103d0b549558608545540125810b074002d0000c4001000a00a10503004001107100d0500b100a585119090209903443d20440c00d040c107005000744001e981e0018018407188100e86841503c0302e034076000242d01040020760251400360280031b5003409480c007040d46070680708152000d000a100051a55007261130054001e052045042414072500310310500601840840c00000304040c10003800180c115030042d24081076607075469480d40c0b400788203051494901c841101c06090001012740104085220f00d0040c0420840c101c1e80d10303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 330404433 1250 330403183 330403187
    0x3080307021e030405030c06041a0a0e04090f1104060b041202031203010e10060903120509030102070c0e0601110705060406050c0f1b0a1509051002030d090c0e01080d05070f0201 78
    0x100038410310b003100d1030700030394080000352680d0003030040a020740146400600117041800413101220404c00c10030075a05c100510344c00d86034001107400d0040044840d503041c21541c036401400c0d4458083d00c010041c044c041d00d41803003180020000c45000c0e6080c03031020171083d03030100160b80c110340c1d4200740031804800c0761001900340b54400c2da030a501080c02000210340308488846180c800c08202480c0485c40d03803110b130162101d07901c6100040c800400c144184503070b0703449103020380403101000c0c00141c20a6010b50f03404001c80b150703070070001e10b0f440d805040100075a4003812083d001c04102010300143c40c1440c01040d6144114000d903401d2140004098200007c10007001c552140e0041c00d480c000341e104101c2006460300e40b01114403500101ca0049808810200300d95078940380d40e04c82c46409171816041c44130550460246100b580000e0100c0400032026004480e0a5449000c2d0650b01074281105518207030410382048469901007610f00802c03540080c2201c01c8140c210003223100780d0b0754900c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 330405683 1250 330404433 330404443
    0xf0e0411070b25050f0315130e0f06010b250f1a0411010f080613021306050309010e06040510020705210d1a01020d12110316020c090403090308030702 66
    0x1440b0700041c2e000c000b0b0765404516a8a00350a0381d0100c00b8940e40030100c1201c45008280e11a1030001040010540e4410654104950a02c0141c214040c07401c503030322041c04a407140048540290400f21181000b0344080c400e25000d8411600758604000b03101d100d0300702c68048525404c0750603200d00702c1c0d041480741541044615552100c0100205682c01c007a400d80ca02060b0384c2180e05800c0b032a95085e4544c010600c1e0305440b020755444028965907481040207a0365804a1400a1f90b801c00c18540c544011082040151480f034550f90381e40e0415038462400c40d940e4610312101a0054020b000000d0300200e04031180509140c00561240d00c071b4104641005080021407101c0c2e100c0c801c84440780100c0b00701a0516010719042007001c0110740c0e11803580760703031140384842c0140c0115100d4010304c0c0c0181d90482c08150b0300780340054541031149481107642d0050703e50942d0201c084060320004d03a4108040030012100b501ca002070350a05603030280c4121f100d400018074101000c40080d800710f108202d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 330406933 1250 330405683 330405697
    0x71701020d06031203050703021e03040f0210020a020f090708011e090501030b180d02121b0601030b010e09070803030408090111100b100309020f12070e07020d0306060f0e0411 77
    0x20000b950792031410070b07140303955040090b002c1780c140b0000480d020300901c00d481b101400d21904020680a0080c024070683c4024000c40d002c40003c0019400b680311600c0140880881e0340003004d2494041c010021401c007545001c07445015404100144941c0c09181181120519002d01c40811164048c400d0b85032141c0e003020580c10b00c0e100c00081803090500d2483d00900314018442c052203003d12901c3d03158907440784210096402000140100003001c4000d21b000c4544004800f01805071084050400800307038404d50f08184050010320503c0707a24829685c0000480300201600d42c64400105d4036400001c101910801021903c4500c590091200285501410082d00c0e00301d503034080e20000400c07010f00640d0058400d54200c0c03400b02d00a210700390180b90018100e29850040c002000024410072034100d00398000d0743d4000030800a03c1469500aa03480c1e0041d0403000400d42005045800d0f640c40b2204120060312030807100b503004002881540b4040e04c0110b01000c8002c002c8256106540c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 330408183 1250 330406933 330406957
    0x1d0717100b130f0515040212010b16140d02010509070305060106080c0c1509012702130b090937021302040b0406020a120305040213090c031505061503070207170102 72
    0xc00480060a00f55101c0b6215507000c034084484400900f040c00304078050303030038520910752000c801484082c1014019000043d000e19003060b03910010f0369000c09030003802c404000d280e032203404244d5080c0d40a00a08d48d110300504000d0010900c0e40c0c641980e00c030010711402044c00300d034401040107201c480e42240e852415840c1181d01c0901800d95070400400d0464080f1425440d0888581c1c250a40c03905603c03507200e810407144c0d02c030300081d000c1180100581c90441101592400129100e88030248240d10856a0b20058801c0d407840040464490b2030300c82a0340100ea0003000d400b00342030180c1854000c1180c040d58031184001d10400880024411a000580003041c080307800102c0982c0000d141050724862028604401c4913000d05406440003500c00071341c811000159151a18140d9201c5515140940034004403d0754a0f21003002943c0100003001e0f000e03840700c04004081c100240c1404000c400b040c1664510b1400080003901c4080c1405085807508175000d21119944003501611a558060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 330409433 1250 330408183 330408191
    0x3040803043c03020c091023030d0f0e0303070b0106080a0b0a080c1306080601030f030c0803010e06090601111b030a08040f080f0f0c01050f0d1d0717100b13 69
    0xe92060320704103041071001c800500c03640350345d09030504254561900030000009880304160030400110075142010301e004084105049420845950030800300340c0640c859100c86181c0d602103140207041d40c4640000328000e5104010340c1000618000304641110480d00e0b080503141c50340e28000010b807043c50002940001d41c0e5901103802c03075002c120215101d504a136180c01661820442c0000e50380e07144202d10040e00030400400c04070300c14041c0504a1031080c613001071504076980c0c1e406100d800c280c00076440b0344010410030040d402c08800c8175070011070908003215900c911a40f2a43d43d082d000f10004040c241c00c1e486d030301182e1070400030b0030302e05a07000710102d4403180c4a005106510259101e03018452041340044024001c0108088140d81c130359102514840c00d028005444540c803155078842d4074503041000001003e95442940a0b02c41700d03000c5c558101a40b41d40b09032508506801c01c00d550b0f00403050303013426500009110b00c0000314003c0b000c0780c41c8100b000004c2800121000d00c600c86814 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 330410683 1250 330409433 330409523
    0xf0c0308151f0201050a1d0a1209080d020601060908060402030604022b050307050115060e10110105090c01090815010e070e09090f060c0a051812010204080c0a0b0304080304 76
    0x10341001b84903040e640c4d02009841846940c5588524407078030b40304c0d80c541160700c0c800045600501407210941140c04c011521541d1050521301d0403a850920000582090006024041d448107482000b0b141c0980100414186600001d03201c0070082c1000f84540e254082d241c0b6804511816640c8039030340107005003038500c6541001034483c0e118820071101940b8210700c02442c1c4209418007401e5518070b560302c2c8404904101030029420f100c190541c00d201180030b05c80c202110074000c3c02e216545010280507642214000945884d8254104108540007840f101180071800c00e0604e0444281d803c0440f40703522802c00c00c0c0c522083d04080c035508540c880040000c644000941190b140b41c5803811500665510303880c2440c20300030030001800285080111070441d09803e40850650100144021443d0a103545503070300720783c065403040105800050f011502860542480402005851035003071452030640c0d00c6081c28400280024610450164040c400e1134420161100b40584c100100d658124 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 330411933 1250 330410683 330410687
    0x9010c030311040e1f08060c03040204200d06080304050105090f040b030a0b0103150507080601030b012a05060903090d0206070503090613090b0d03080a180b0c0405010f0c0308151f 79
    0x703c11100c410541c11192080609019284809400c1b83e4035900070b41020703101c0c1d1f00d0700b244990002d07000740d9010751111040000c01600381c0c9810100500000d585a0350034034445900c094035a07990002d501c6400521003000a070340c0080803a204150200d661401071a00310000400800a5102850b0544600d00b143d1003000342c201c08140c180c038014030962040e1031a010fa501d06442c8215445800240202c0120345194001e402120401c0b0781410b114200c41464050110384650500900d9238591320700c0d6565081c44800d104d0f4640241800003d1442e2250001c080b450482c11410024010600003035001c09200f01403041c0e440c10740700108842c0d41c8600c00341040e40c2070059806038000242c03801d00701c08000d01d0300d82c0c42209210752585504071299210195040103003038842c0038a0180681c0740400d00040c06400000340318640f031811890b2568100400180158000c200742d00c20320400085041c04a40c0103800d03917030b0010824a1000700040c1d5840420b00304240d09581e40c0c0a41105500c140380c981e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 330413183 1250 330411933 330411959
    0x10c230105190506131a090906070e0f0a1203090810020a0909200306011407061401050303031b0a0903050a03022113030618020a030308010e0f090309010c03031104 72
    0x3641c03070500b925440d5501d511040031200103030741465108040c000c01c0b40448140717400c0343d4a450000d10081d8501c45100c0c000c81d10302c0741d04899851081d0407038010850b03025040420a2a4035405132081031010b144000450350310b54041c0100203600b800303482c0c5002094404c2c20000050000c59007035607c40302030802032038040d41001300b0203800320b541c0b00004600d4015611500c40070f407a00042e0707070041c03107414000d10344d281d40003400c1c641c10002c69500d001ca21a20740710017000e500e40f20700f50000b4801040c0c103010040003010380259110390010001e0080c80382480516201a4082d2880f003940d6400d040400e40f4907113a280d100030483e00512040380c0602d500407980300b040340c410300341c0c0d84a00701d014824042c080c0726580c015542800017074000c0c4013080702c61748076040b06a141d800c80b00340b1003074640005a00014a50040740003d52007030041c003020301a00050b41d045040da4180364100d0900b4040241c0342d00800c80814100803022808009041c403a400008800c0d0050320860758403915029500696 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 330414433 1250 330413183 330413191
    0x1b0c0112050601081308040915050306010f03030c110d1401020a091a04060e0301090f0807060c08060913020f0603270a05030f070807120e010e01031a010c230105 71
    0x82200c0d0054000280c0550103500d205072816074541c2116900c906804060146840b41660028000e00c40419480100e00c20030704101070002e40c87d00028a400304041c5050320580084078021100e41c02000045e03004a07816003155404070003401100c100e5404580703c602414400b4003c11001000141258819401418402003903500c000b03da54944411503480b0401054620001e60104030403c04540304200224180344d0040000c1000f076107a0301e5803c0ba10003070712001d0311a208006040303010030140d4451a055001071b0b0804459902d417500000c0c24801e8000c0c60000700100c20540041103507201d07011120300540c01030686807241084060a00344407010100b4840c01203011001d030455540c0054101851903003d0000c5103030008102c00480580c0040c0c00c100c4210500b80407000c00a03844078102d034164070140d9160f020441c6900d000405030350741125540e05261803e030440d21140c1840f42d040d140201c081c02e00c10092207041ca000c007080c00050780070039208159180341002c412010f402060003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 330415683 1250 330414433 330414437
    0x2c04020d02070203010e06190e0c0d11091608040809120604111203040f0b0903030f1c06090212070305090a02032a011403070305040f06020c01060e130f15021b0c01 72
    0x10794046c00c1c1c055550300000d690004001d282c0943d074100c03c8201d500404900d502d82030a440c02c7c3c00150b004100c0c64107001c1d41c12155005030324415107050412284c615845007070900032070100030003c600603100300005400541441c00000d0941a69228204240e0b91203045004444691601d400d0005220400c180c1062107203030030090100c510b82c1c00005840030f41d08955054000c061401c800c0e940951701c00c80e0420340501003481000c0d1035020060180500024a0340ca407040304d0440d041202c00c5a400d608000c1201e80305220705180070380d440b0015a031000031030900040c65182d8281c2c042c07034076035900c900031340c54070840380000d02e40038110340d410100703240348001075620442001c01522a04241440d1241c80304080c000a1406442500b149808c18003900e9000c42c00e031441d888000030b0340c5c030901c8101802e81d100c0c80304009020110035415400341c00954020300750005c55440c18007043c0610310203811442030b45100c00300c1b007013580e0445110034883d0b400b029802c0680c284082d01c8105035a0480c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 330416933 1250 330415683 330415691
    0x106050607021503060109030b28050c1c020f0d140603060c1215091f08030c0709200c0703050607030510030f03031d01200a2c04020d0207020301 64
    0x809040140603074814980c014400a05400c1c190210340850304020241410889030f00304c0007010584240c051409506102868542080401c074041201c80750007800d541c11600c0c18040001e43c50010f4107171901c0c1c03c0300040c40310400d5041804180640190040640024800601078402c0407441c0c4c030800003161405d002580a40e00c0c1d40c209921140304642500c0d18a6040151005407103100d000c0e00da0004100103150090312407003010920042c000c81b8ac000d2060741b10a5841502200390086400615490004624007104500020b407120010b00c03034600c026403110070032058940040c10012807500c0c0a480c8030303102d0078040100c43c0d581840344026501c2c1e008103008900c03041d00c24096688a902228000c2028a15503a218040f950705141f050701050358a200d040640800644003d00340710300300e4000309000342080d00c11a014080c00b1021440614100094191150804221107042003072030224150007600900c010b100f1010010003580c060b20000c2d00c0c91025426901521159000b03038000c00c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 330418183 1250 330416933 330416939
    0xd1e090209090a0206070b09011404060204050306060f1f0c120203091302070b04080d1b020c01270b0913020a020d080906100306180203070b031f0f05040c05040b12090106 75
    0x3c1d2074000c07400001e50449810030400d0b000c100604c40c0d4a401c2085200001601d640100c4440300d611800d8030304a030400c5e00000c00b080a4582000142d4001a040310010314480c02000003070741060000100900c2070b80d50000a1b11030500031a01034042c02c2c0c014006d00801d640c0b48100944950040602510800c050b00c81200720150074804d44102e00d500080200642d01c9036150f43c40c0a0300701412048200f520780c2c01d000c40390517121610081c40b42d019001044056a8403002600c9600000c000d00c0d01c080c1c60861034009a0801c09c40c2104440c200c8003076654a4483d003001c50f58100401240b915084c0c0001030f92040c00c1d9002032403801181142d0b80b509843c1e2980703440315840c2c00090720b00c1c038110a1244002e0002c10669485a81c44032444400301d00b80072440d03404070b41400382da54410b0190480110410013150390001101031081028800c3d90f6095040c01190356600e0071600803203001d1a640c001d510382c0d00e401203040328041c082c0c0550080c1c03149400400094054000c417444862542010000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 330419433 1250 330418183 330418201
    0x10801052503090804031b0e0703020901120903140a05090a06050c060601032d020403021207030b1503100204090c0e030313140a090c11061b0703050d1e090209 70
    0x841c00a00641d002150300800c4504078060a055001a41d40c508204400000101140c0f030282c0410785c03010311164200d00d000301c60841030100034007480030305004101c40c0c02a03a91045920511000811001910300c0860400f02d0b01c1580b000707000a01001e001850301c4c55550404040c5c4502e00c0c4c2211410030300c0b0f44401e402c9502d400b4403054060258803039808030707521b98007a41050840d004210b00740c1e80882c0d4000861200f0300c1c10402140c001d80e9001900340290f003800d03119104400403007030042414628540c0c4480103008000c2c501025903008a10040c1540e90501c281150203032050820354690341c88000c2c5000a005000c4c42402003001048003a0540c1030100555100105011600100c40c1c5810741c0c0410108030058076540c041c0c1c882034085004c8ac1ba51003028040f8004d41d030f03249001e4441c3c500862034100054126400b602220311001d4200349648101d4400544c5032500766104c20700801001c000d86802045029500c201840b618403101c01b035400240301d030b4001c031003048190301c5445107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 330420683 1250 330419433 330419461
    0x9060b221812050c0c0a120501050a02040e071d030105010e06091807090f1103010602012004050306150621071706030c0411070510060314191217040b01080105 70
    0x100000402440c00c0009402034024100440c135050545c3c51468005000075607021140d0009100c442e04200c1c400103000d400d10840760700c20090300d002c601d001d0411403003c40c3c8000c020490010000041c482c5e10008011000001034031001400a00095843c0d1001c0e158a000c120343c550300441e1501c0004d8440c4403180c08900030400944090803882c0e0500100c14040c10782e40e01c0080105803500c14040300c00c48010000c500a12a540c000a4914500c54082502c0c070b2044609000d500c2040c00140215036010401325017200203020a00c081088003c04220280110400107504841c0000c154060840409905200701043c2d42e51880c030508240260852503c141c50840c0c16500403a002c00043c1059401200c00d10415500d1509000301c540c1c4151402600011756122592071780401c00401500f450598580c10303440300a44060403100f0000010910702d140e0261806500c901c012684034003850022180c0b0394600c0c02003540b45800d0804003102c07902072140740410340c6040000b0f01e10003a0480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 330421933 1250 330420683 330420731
    0x31b06120b100e031e030309010c020a0b0105010813050f0f060702010c020717071a070c0e01050303070201030f020f040608160906170a1103070c02030705040612020409060b22 77
    0x1003011054160750008888180d084a5101d1309803040c3c0f407901080302c03c41501440041001001582e070b074500500b00380c3c01c1da00368150b4040ac3d54088401c941c002090708603500c1c1035403c28600900c440d030b04d0400340700c06a45401c5000c0d0450003580c010b20622a4045104620310f01001c003103d0003a159000f0403030072a03808040035001078008130001d0001400e41c28407048080590002c0390324130754441d1450320b65000b1141124072003070702c00200300080102d03c01000b001070034103540881e085c0d03140001094407446192002410903a0724841d66014040303540c10b485981102c00c500c03903241c68807101301421051042d680c0141e102d0500302e0348068a40701d1070703090007900c002e503880e0096118403201d000e40c5054007a111017011604c1d07003144548541c640c000366206842030b0ba40e0b044884030a005160400203c1c0e0003da0041d1f007084418002050696407001c5e4240d81036400080721040ca00b418001004240b40305580607050340d4200c841c480728110010035042c1312060801503940303030044034120440401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 330423183 1250 330421933 330421939
    0x60b0111100906020c032d03040b060105310314060702030712090503010c0804022d0d030210020a05042c04020904060e0d020105100b04031106030402030304031b06120b 74
    0x322201c42055590828000daa1150f400942464080011182076420041c80c6000c106a08014030b6000003442100000700040402420314505054844600d2010010201c5040c00070001c2c06809444441803102c0b02450708005160228a4801c000c03800b070001440140c07003000f04030b04070103284940402c2d44e5000d030380d941d0029450305000b95900248401051a200c040c0100700c480040e15840070b006000595151359291001031400c2e01c108000021328000216003010f11110151100006a954002080f0129035013403084142c1e180807031810511b41c03034005942d80003040009040e41c101015205945030ba00706060402004107006141603506085040380000c8000410003608042100f2900f01d4010b101c040f40c91081202c03801d243c120340700c40100050b9518010010400070420440000d04590031441e89054910385030100c07112205030006c0e05c9020004040307011540c00f041181c0003540d20444019205c0c115a4800414030103621410b008200152004010030174030b4810303024000b40c02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 330424433 1250 330423183 330423193
    0x1030f020f04030f080409050405100c031b08090a0507080705031c0206150411070f03030605010207050105041a04080706020106080114010501051b0c040e01020415050c10020903011107030c060b0111 87
    0x50b22080d0a00e58107841c00c1d118410104804101c087c1d02c0e014913446580150014908400004110011186241a217800301860882600c4526201e60102805c000c9075140604841c0ca84040d118107142002100400d01e02c512040001c142401084100c200c840c11819258401c1e540400180090541d00112005030407000000340d030045400340e401100b8401030000205000d6412a40c2c0c0d50740d100e43c601350b605e84a09a58a001c045d8140078000c040c000c00e20192511501d03103c000782c401e0050307019549940584480d11407501c26450203450080414004440c10300d60340d100040d000744a94059840d0075420250b41159078080ba01116040b920706079101d42c0360440300032032203041a580580c00c07940c6014045044016989501521103405191000107039a24a080b41c168021a58011900248582407284400c0b40d00e003ca4101580c80c0325410150792074a803a00081c0c01480c24031551400c02001050140070706500c0140148183e104450410607000d140e4015194003d20f60700c540700702d03844 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 330425683 1250 330424433 330424439
    0x406031e0f020901030b1b090a0e040510050c0703020105070203090a050f030a0c140a090b18100302060a1e030504050c0f01091a030601090e040b0f041505041101030f020f04 76
    0x10380010400d280075140c80c034420300550340001d00d426802c1c0c4c81680c07684401400d01140301d1410001c1258142042520303450041c20b00c0204108461b075102c3d0090340c00441c00010103000301070044404c0703c880400c0400840c03038610f14424481e003240d031040d00150f00e00b0b03001800c0c1d60300000c00c0b80c01c100c20041c101100540ba01d420407035080195017180350503006600c40702000807401a440800383c040c10712525540d0043e81f05000040b055980000e0b04542405403040c000d0b110080c40f440301040c0180580740603515030303044841e819071692000750044400240c40c461035030300500b000002010502503100360790198608506480c0280d902420940204000800f580342c03a0101d221508018180514556941c1c0d00c110b0701038440341c511100f041d4000003044215a030000d007100140c0102081150b49040070703264a1061003005042601c80c403c0200814184009140031210400321010f0600c15407805150621460b00c0504c0b907a4041f90510f00140e51a01e06030080e01e41c4040c0c8103c5403410545 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 330426933 1250 330425683 330425723
    0x13021b0f0f120306060705011b020f031c0e0a1a04060608060402010e010518030102030406230403050f09010e0316050405100513020912030708030702210d0e100f0e0c040603 76
    0x203c05004154048401c10401000490031b0041380f0100340511120f81ea4441d10301c601a041450201e481c0003950000c01051040000400b007400d0a0b0191700800030799034850982052a014200401034459200000d0003100c4000e25401c081c440c0348070f41400c0c0725003075407401515a1007005950090201e110101e0180941d4800d9010b0042040b0341c00703c0c8041010450086401c80e4400da806980d415102e00603c01440b132181002c04200c1c1e0000603040e00c5d80b4003514010064002e100780c2007200980014030841680c4a19190004070000a060b0f800d0882c18402400300b1516a220761400350381800c0000c0c40d000c1c0c1d08021401210780207400212001201803401000b5808400c480382d10040caa01105504a800c0002e000309500c80c1a40c55513904240e0070103481d1644a5001441c0252448040d60a040058098a080c00004100881c1c14a2444802800c01c001940c0360030355941740c00001505d089080d0401d002e070f0613030007082e502262824014001500d80030302024103040c030b40c5202c000e4416 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 330428183 1250 330426933 330426937
    0x1050a0b1602010f02100911040c02150a0c05040b03010e04050d08010b2d040f0314060c0904150506130e0c07050703030f050c0303070914042913021b0f0f12 69
    0x544501c15034003030000c00591b1004944c0d403801305a0761045101654420b82c2441c1c410f0302c40000050000b031950504940005520b204010300400c55035846034001c6100c58054401d07180030300340c405602034417580c40c1c4001404a400c202c4d810f51740340c0320f160400c1c0304a9004010240c162042d00c11a20324160080c01914000d00068140c0c8040c9030000840041d907424400c041c00103041850143c410705451428941c405912000c8071000fa0341107481401200c68505040b00c0c4000c2c4195400b04002034070007a14541c000d0aa0301c101d42161000a5141840ca0041883c10903513100068200003030700c4e0781207000e006000b4240f00901c2544106402d0001ca40110364079980c440345880d0040c83c110140e444942150010313208540810350515046c00440d0740074504042d951020340e402c2002d820540c210380d0b81d240e00340801c221201e010380c00300c0e142600c1d003010015004d89040030a41d030314241007003c20700c014040c007114078650040381b0000b103060f5004103816142d649500010212288c4030755203130f8259 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 330429433 1250 330428183 330428207
    0xf03042f0d020d02060d090308090105070f0c031206032a050d1b210b070e031e010e011a0922020103180b0414070609031a040c080304030b01050a0b160201 68
    0x1007000e10074080f0050361a94000c01c041010b154000ca00b0018134507018080005c040d28801441e414a401c002800d030b4000c00c01c2010029500d032143d0028403d040586c1e113000c0810039002002d0400c0c2010041c005103481c02c0d0b600711400ca0207a1b8580850000e40003418581d8042d8030307800341c80c4c042e200001c500807a0000009190098400742060740d140c03c1c3d10740c1507840440e24400c201241501d14107018401c0c05442d440038241c204000a4110703000003a032151210003074000c0b25203d11048803d50303802580b00340011640a4000c00600c8443c81515041c1c2c01402c01807446441410006840100c01c11007640140c000345100400d03240090340103601403c1c1c41c0343e20b00289071144420502161125105602680c01900b083c204d035180d6074106824040190806000c3c406603c00820000722445041c407003080f0007a241003069107503441e140d5030901803684581590300c0b0109011060040d50131500d41200c20840d40072007683c0e900d03081c0401a0194200501c40000c01450140155010b01042500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 330430683 1250 330429433 330429439
    0x30d09030504150c0c050a050303030a0e010605030a03020304090b030d09300b0a05070f0504050d0503070b010f060306090c050a0e0a05120a060506061813020f0f03042f0d02 76
    0x40c039840d10807070f01c5680c2440c110032000a00f8808101c0c05c0c071525071032810181000391103426000d41088042641d9220142040c2240c0b03645650340300e6800001e6100c5c0e801b810008041d9045040c903800c2c000d40c2c0c1d82060280584503850510380102034500040c030309911500c1c5884419400d03107041c958403200b018201d48480300d680c12000a0401d03241742d0035400d101500c62201d0a2680c14a00d401c02c007156001084030742031040d114507420034a9003000584003105c0007261031001603070b101c0c605076045000c0c0440091414080d0800402c1240c6e0048400040d140b00381c3c2c041100320303a04c501620607a0541e04445e004200c0810103c10040e00c110700c00d190b46c480c0035140c0c194080d91000403580841107420145910f40003a03614804108580c02141d1f00315900700ea401d401c105104d1107841c20302c62101c4480344500c0c0d10310041c0c50340c85819010b0301c2e200413030540080d84403106c41d651040701da0700450b41200c0c0c03510b9140071030f041c50415900304412542c3c1c940700d8021040034402070000000000905982c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 330431933 1250 330430683 330430687
    0x206070501020910090806070e0a0b0c011b030203041403090901090507031b0206011508010509070c0f0506040b040309060c05100f061e092a050f0702210706020f030d090305 76
    0x29503104e00300b40070340d400f80c103944141615107815100d60406402411601c100104201889616682c150200060f43c42c1007048a41d00c014110321980180803000300214000f1102e218200810b4065001c0c51049004000c00c01c0503c0031842c20580f40d214401015902a0003000180403070381060b8031a55000280d400e002419076009401d001d10b0b01028a6082c006074050310040c032501c0000059500d0199141c00c020180c3d505042c001000404020000c01c104401b186840040c8040d01c040d80c844250403805985603414103081504408104030360590128422000006032a0311a981c046141034004000c1c01d90400402d0705030007d07103134807920f0b004200d132186c0b000b194211380740e503c60350783d9450503000070292440c0441240580c1d81c018410681485080d42d418a50b14a0000c16000e0040f10702c0c006580300c05054604c1681d001c0d980c4043d40050301c140c0c40f0702c01300f001002e09001303c85c3c000044801b42d5130380c1c000481e84c1e4840c104100042d40c0040c01201d5411381e154108188143c0301e420064 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 330433183 1250 330431933 330431947
    0x301032f030f01060609080a02010e090703180c0501080f0906070c030908010e250b0a031107060c02030a0210020a02121309151806030206070816081b100903020a020607050102 77
    0x240350500c1c981c142242a559004c041010a401c6403105000344603030b50241c040030a903500040e1175040001c0540e030003013240c140002c00d590311a5203d240307008840c0200a1034900381c2d042012146001e801500c1c0450345050110b03401c410b042e203915100e110010020a81640d43c4042201c906482140881c18000c2e42e1a021900d0307203080c02408002c0c0da0300001003101c0d68209503076035160f0040c0101502c2200b034023801406854032490403134000300010b041c013050b0200040710103040f0b0702c101e40000d44905e140511411034280d010004012105140d0f00301c030712410031301c80c494003248107005409003d603112008812007410068094a40c11036801620751703900303644080341000c0d01c02403110b0036041040d0400c14005034080483c181c008601441c2d01300000c0d4103550100304244200032010f013180707c1c08107010300b0f2040c1611203a070040c0c0e40040075a403590040301d4080346200c01243c008850313010f10a0120301401092040926a60f0198010140b4102c241c00b409400d82c00441d0075249035408001903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 330434433 1250 330433183 330433189
    0x10605040203070f1b02092703132303100c030e010603050d0f0201020406020303152d01090806060609091f0b040f0608101e051c0203070602030301032f 67
    0x14601c1900503465100602e181078900900b11008500075064031700b8030a00010251712001c1840b80d02002c1e09404024204100b01502d40000200e000700b9010f103c00507421901038030324800c1004845605480b40420441716038103904d00d032a40c0300c41d1501580304901d24010450240c00c41080d11007603003000a140d021000711a820f658041c1c00a4400b80e2204004006466114036001c465034120f20085040a061260003500c910014102512008800c0e00084840c0d4039106c40803000c2111032503132500c90707072004941e0b441a12600085408035121b880f0002d400403010a8492050000070300592034454200c080010500e005025000b02590f0508800440d0f0103650200001c2c10051080c0d94989160440001c00301d18280c00100410022406110f041041303990310030250b4100c13030001c41c84501d008411010751403059101550080112550040b65002d613185200114001c0d400e9070306a584801c0140c0c2d89100a220081c1038440150302000408443c00c0100c840307035182260101244520400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 330435683 1250 330434433 330434437
    0x231c050103052407020a02010e010e090702010f051e19060f0605120a060303020619020d1d07050405010e0f0903040e180601080105011a0c030f0309030a11030f03010302040e0106050402 81
    0x4881d568020141c8540400740484043e91079036040c1501c11840c54400f01c000c0d210b920f9080000d05000503904001041d0b801401e00746d06019000d0f003465101c2c50820740c020701a003400d003040581c45192201246081400d400d4002c40000c1000d840d80254680c00040c40440045002c80132141d070361814041071f00203500429200900c010342d20140c50340104840b5141043c0064004000c0c6441d0070020000217801043c8103500000c000d03801c06481c40003180080180c8158000402d01a02c0c10700c500c801702114207904a0b917010702108442503d5251018042210300078010f503c14980d128000401d009161600306030300507001e0741522704150303481042420b4070b1000d680540080080204010041408200780da0041c0303480d100911070b5524143c025540b9270580505048401800114205c0b010010011100c610f2400e42c1c580e55645804401d654482d00001072400000d0390850740b410f03c01c0710000030713640e0341d0007082c6420345164a96420407004040c003c0700f001055494441c0040d0326542c0d840 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 330436933 1250 330435683 330435689
    0xf0615030c130f06270302060903150711241315020d050402040e0d0e0d02060c0a0819020105090706030e0a020a090515120a020103050618010f060f231c0501 69
    0x3c4019642442d40c003a003c0041c0403c44200b00c0003e40e800842c11004a4002c000c80750107035070042e40d0711140c80100341001641d031040720100704850103010000303601c403e0032440b65a0780001d071a0805508404441034195800060a1b8440e00c0408541a2101601b645503031a01c13519040b071584500003001d800f60b8218800f4013036115500c2d0200402d500302400750004c200326080c0174000d03c81114402401c50140200340c42d0150540064440c11901c1e11000c65046500c100d0031a240030340d891030004815402035a4075401141c0302075500380b01500501409000d09140c0001d01005410204101e004141041003050360744181c409030405602c9074003107100030304030f1210080b0341c0c0d1404048182400040205180c060840b0f0350951030308030004503000f180594246800708880e26400001912004e4146401444204101c0001030034078802c0d8100045071401e0302c1d0072180b601e0601080c1c0f000c00c24040c202144d000f5a1060801110341c0a008010300540d011034090740d80c03248480e0008444c4260 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 330438183 1250 330436933 330436949
    0x109120605011502031c02180a0e09010c020304080705010f0507061a0a050607021503130c0b0901091a1c060807080f010f0903120b01050f030f040b0f0615030c13 71
    0x500c080c00f50a940042c41c03940900045140c54950054000c031040710000c14610654081400c201000d85203042c6002600d00906050303800e0380f034030038094010000340d95a854640c6001d5981a40340e0001c41aa0111203161000c0c2100b58501401560510044016001081710810210000509911503543e840b4811084102d5031000702c03041c0300581c2020b070440752080800384402001640c60321444402c002e4040300140d102e803200c41c068211500c400b80c0060008100000125400d12044050285000300f42e0315010441d60b50041d004c01004d00342e40302c01640d0030402c4400404450851303000c6071540c00c1d51001a03041c0d92011101d00305269a00070821a03004100002100042400380d85000d65841c2c1e820488a180750b44e025050039120a2050303013180e280e60100405a002d01c0960b040c3d0703071101404560b0392400c9555240003080440b4220350020715080424210340641811903c254009881400841021010382c2040c0d0001400c41841c1c40e0104401010404443c0c1c84500901c904 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 330439433 1250 330438183 330438191
    0x906050609010501110705010e030a06180b0f04021c0f0212030c1e07030318030606240309082a102013090c050d05040c1412031801091206 61
    0x1404005880d0410f900850403c0382c82d02907401e100b0707004130b4013070202d51090034040380304210780780402d04186150381c01070400b0f0300c2c0c8100f0100c1d00d99080311400055224004110a654820440e41c010410640b006500000c1d2401d440c01e00c0c4092250600c1d40074050b500011403030089900080b0041d61045200055400200d001c080b40c1c0e03004c00451420a0507031003c1011281d0a0050640d1048070344008ac042150001e11800c400c3d01940e0050060745d088042404460b0b00ca994442d04100b0b5540300c2400c00c005410305070080703446441900a030350f610110340c0d03103006184c440b83c03091080d100340e170607252020400318091506401c001d080b02500c00c00340c011a800003001031980c601d8440040b0000a4a0100110b040500300440d80406a83e4040c4002815007a03581c000c607100e0013643c038124030703040c030300710601c414070048012081c100c9000c102c0304640e00401000340000ca0314000c16090741540140000c66800f01d900006e501c00324010300d804400d844e9610108134502d40c0206040d0307075071665 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 330440683 1250 330439433 330439441
    0x200a0c152403021c0317150a0608070e121006080a020a1e0b25051b031603120516030c0302010c14220b070302061006182106090605 58
    0x503107101c007108210350a40340403540340b80d0340101d107003442d50701603840c80c5020b5041e6601c10940540a50403030071740301808000307540c0f41030080d010001444242c1c062042d10b00c80e00c0003070020300c0f034100345210398a035548111201002000307020042443d183c1c0c500c2c247c0a1125401d1001c8840d01c80c04004081e080e000700000a00d60040c0a034080c1c0c240c100d07400142c40c0418002c10800e05000c0d001c111b070441d28040755241201a880a140070380b04448124002080700ea507414800c0c00601144c1d4509004040c50004104200f0141e5440f158008544a8112440c0030008141f4264041ca44103409041c12840c00c9078034070840d85890900c89048001c9010007000d6004c1c5903091060081d031064605140c4d28108440004bc00c0c0c030301a014203a0403011000e504034140c840468011001015070303082c0306131100440c4c42d0203034441104135102200b0f8034241d10000786092103568400b0f4001c1080380614099414040a00250000c1030307c030f049180098803202d00001d20030310540000e1405020005201d040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 330441933 1250 330440683 330440711
    0x4b060f03100f0503030f070804091b0807020105070c02040f0b0303040f031101030501050108060906041407090603050a0b0d1403130909150b09181c02071503200a0c15 73
    0x10300741c0001000081e0b000080c88240c9000040b5000711520412150f00c2d00c00501d031000c281d115580110407131505000d0500040b00e11000c003811240025101c910055423081401c90807110115000400180c40c007070858050704043e4031016070700c101c100c0c0110b0359950090100780b07191700980c4840070801e8029020000d000403640309200c3c41c6024a41032265524160000b004084040c141034030544501e40880c0319079403a1341c054040e0a422100301c207500e04c2d158070064808800b9110b1b41c400310303080000103810311070117200b040c034038030b1004101c115001450385440840c042000341540c0a03110030091098400f8007a4a0100180700071280840c2c101640e1030100001044a4881151103007010308500c5d1954565502d144d00075030a030f1110600200031104940340c685103040c88110300241c0c1fa0100f400075400f1400308195400b0743c812441c080c0d900002202100c0c4070300c90002010f110202c071306440d40060b00007042001e291345040c002c4c01031642c4405140803504d01e80251010b550780000107940e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 330443183 1250 330441933 330441961
    0x160c0e06030f0a080304140307060f1d070305100c0216030c09060b03060a3012080c040609181d0c0901120206090405061507050c4b060f03 61
    0x2a40340b40034010002c0b0740d684000d12030001810050030001a6602040102801c2064600d0140c100000f440300c80207580b0341c940101038140d504031840000105d060382030030b8002001c0b02200c0e4070030001e0504003d140101b9000381420a4080d045002e2405d94183c003c3c090b0788a0360146010344110007610b4a009035150465040390300c02049a43c05108020304c940e108500441140e001d6112018549524407042060070701400c0c240c0c020fa4484c0031407505002413956074044550458884c0000c5841c0d08100d291a80101d00c40e0318002500c400051004642b280c0341000341a0501c4008148501c1c076660500d1151000c55540280b0b07800402e0301c8103280f0f80000b0150050451201c041c01c843d590f900400c8261140e000c0d6180200c0d1510046412900d410165201100c050560b0320b80340c0000f450110380700c1c4140c03131a452103008090081d11300c0c441d48507141c0441c000035030a50306611400286d094811001460005003080b550402c002c155102c0b03030002c280141c510602d0f90b03500e24021061980b04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 330444433 1250 330443183 330443203
    0x70503090916170c18030c0301110309070503030306030d0315050a030f061109010f1b06050c03040c0b0f030609070c050304090c03062418080a0f050d0309020f0105160c0e0603 77
    0x449180030a0155140b289400c8642e520040c0241012600c402000701c1d1401f10034241079901986441410032446618102542c0109a45400e4440407540d032020559a4042540c0c0030f41d040e0858518000518000d52108503000d8401c481018030541d030f04002001c40400d0351041d0703101114035501c1e40400095100320040c031558610200e0409a4400000300718150340a540c1080c0441c2c02800c008076018182070800d41039009906105601c0c100b130072214950410b58048514680d00b50000c035500d1550015140d89a01d6210503e0031642c2d00001c1261214014141d081809807511407880803e01c284010005001000408030309942024001003c45507298001d0b01c0070b040301d00000500d00350164011b0040040342c0b805c5d03000c1c0d41c203034505041c45c2c3c10141e003ca0350314800c803034200040025020120420034051825221022f80c2c0a100391305072180c442c0c0c000e40c484000c2c86c41c14010340c0900c3c0039120100c00c26450072803146003959039042c000c40079007090344000c8503001049801c0c8ce0810250b921 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 330445683 1250 330444433 330444467
    0xa06050a1b05040b07170c031903020f03040602160b090c015d140105061206130e151501020a050d120f0f0b01030506030f030f070503090916 62
    0x20708803181e4401809401180112400300c100010b0003400c2c04403801c401805c140594080582d204c48103294603540c0d070700c80070490544400149000071002c0c080d2080d03a6031080b07503010781f900d150b8641e6a032400a51051040f2000c10f01e8500ca00c0340402c80703808040b840749109000601e041d81041300050034400007000307100c1d5110716281d440512507200c603000540b0180c544240011100c40c4420224000300260030004201c2d0010740310700510006500b0440c600e0090000c44c5185988560070300c000c0d4402c2540c4040c401d0700603804203206050503030842e230711482241c00c0000d001d0044000a0b040c2a0300b01e2051740e03601030348405e01581c000015521076900000340010005d880300d07a0307600c80e150100040d81030706125198002e0607541945410103c40000c80131402c0201902400030f40005061110000c0c1c00285001e000801d5400c00044031039443d05078200441c1401c002d201c4a849552101400720b8190005120204036511030000c1c0c1c40c02010701005c010040041200020500ca40c81420215 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 330446933 1250 330445683 330445721
    0x40b011e170c04230d081201031b050d14160e060a0e040f2405040501150621020708090411040e0a090b01060503060406030c260109020102030405060d0e0a06050a 71
    0x4404c0c1c80400c2e40362103004024a0b04e008a00345a0001094005c95500251074803100080300c2d040c451954000e181130b05e05c540003640d03003102c42c0080c0c14442c009034095282c203c6101010040030480049034660400350391003c4800384007080c210749110100c0d940c040d9100b414880309101031440d1449180010745108034001c9e000d4a440d0315160201e0300034040144c60300400448134600c05520001c070b041c811159100501180c140340c03801c2c42c0284009482d1810007912250003240722032081c082c1401c00491005103400b005420104d0b08005c0d0701c1880103c8900c1e20801c504403076034546004100000113100c0703019445620b4215101d41200d00203100300380641c5000ca06c02c0014100c0160300e419a1254609141c9030f035175540c00310b00100b0742c0350030141c2801540d5800050b10507211240001c1b0000008109101d1800440b145090b118032080003800b603042804184002d007001401b0b00f0100c800c0344000320300d48004403029814280350803001d03141603072100b04106c1409241e000b62a48490340d104209 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 330448183 1250 330446933 330446939
    0xa08040b03150312040914102105061302030606012f030c15010f140a1a0c060a0c30050919031d09040201090e071808060f010b1305040b011e170c04 65
    0x208c1c2c41102405400c26160075000b482c03400700d5400b890802902c0c0c1c05011207410342001c40e032845424030020000c130301c00e10030800000d449501c60442c1e400700e0203403d13424411030900030302c03c5c101d011480070f40c03c41c4d58070051105403007000c0c1c00c0140038580480181009100d504210748111800c01c07a40003604070f4500b1554006154840907402d0049800300c0e004414070a80440c1000c0300d80c8135075200100b452141c10244040b04445034400840000d09486156601c0c01c0c03081e0171050078000341e4074030141c00311080500e10703c8070342ea170005540400d5000c240c5206034603040f06030003e0005210160002405441040128401e2509851981c081110001c001346050303030001b001c8400c0b60250002d900030b04c0700071902c014020501155200d214226584000e910740100c180d4802c0c04070340c504004030040d07000090010100f0225480d0755090620400b140b428081880054071b074895200d4100302c0c590900040f9400c40443c02248428217030355410001c03a490009440302100a04810701c0300c13034200020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 330449433 1250 330448183 330448201
    0x807080c0d0f0f05010614010e0105040918020603010b031f1809080f18100305010510050705100501121407050105070204090f0b07120507020a08040b03150312040914 73
    0x100490610881d0003003001c1034640342420903030740c052400034440119102024108141034020009640f03001c0008642d146650004481122501d0801804181c0400c018840030501e0b40001c0240380081c55001613201040c2d001c24803036070099110005a013400b200b03204440107144e03040c0204554101c5805085030400b28810031495164660302c009990324040c100400405034140c6c0c659190500741c45071035110381d2082c5c1012411911015100300c05025007600d142e8080d114007416901e002c0c0440a20901c265070a80350303503100308416200d41c031030b0400d01c0c12004101d00515018081034080c00d0003020847c03402155061030318291900c0707500024028030640e64450140d818250f0125000314426140e800d1503080c80000b4a0301510600460007044552a04024088600e412009041040f66140740c0202d84403043ca20000f86000b0040004018152032000559007020340d04140b01103031880080000d1030b108203c600303e007440d407001c80c082107900f89511800c13503405041e81c1d003c030640c43c1800c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 330450683 1250 330449433 330449443
    0x3081b040b0d0209031e01060602060f011a0d021204062f0a050f0708030702060402130605011b030215100f060e06030705070c092c010b1e15031f080708 67
    0x340318060ba01003580d451319542007202e1300c10344500c21014407012500007501030103400340d4003460700503100707040120f07589082e030403d0141201c282428059002c40b110700210042c0d03001341d582d4460942c0034001d21100140a07281680140e100d9940001c07d0b40041540c003802807a160300c0780500543c0c00341544210382001c1c0031031f81d80118174a00580d5840c2c99842e00a20380c05401c001804080010040003529500010900d00590003260003080c00b148a4203c0001c2d81c0843c0995800078070240c810b65001e045200110042c20b05c6401601da00c0d440822034a903110740212004021040c2c0c82c038040010000c4e0250541c090501440c04010002140010030000e10025040308108940010080103024490414201400302c428061140d402000c514000c10b0020f21162801c48030b2681945000d850144164a40a540902140d203052450003686c0704003088020b00c0e5801008210f404a83c01c010358005602c140c0c0f488104000311b070384a1300801c0103261981c001e0405540801d109100c00440010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 330451933 1250 330450683 330450697
    0x9010203060a09180f0804091b09060503220c03120513030f02030a080a0801050a0506090f0405041b12110a03020102150718080f062809060608030703081b040b 70
    0x10200340d0b16600c3d4a010001100084042c05c0c84814040c03520820042500806c102d1300601020301420038546a0005020740c400c4560700407410f41e4004000480c02207000e182d0009030709103004545004010000f515071a80c2c070003250103c40017003052080001031000b5600043c000c0c54030320300703046210520825000d842e001c06803283c0482c1d0540b004550b0200300000b90130754030100d03240e100c401c038000c060301d030103028081c09206604409012a4a080043c140c0c1c02910000300508610b0300d4000c103020007880c0280c404d94025000e8058003c0080c071255450008088204054554210342c2c1031000038420710081c030b9440780492010400240c0e03800242401d0210102c3e003003c06503220300d02c1c143da8100140d100f101c641c02c543c01001030075074804107a410f81105000300769182941c55210b500022214516244da400d2500c0f903548907001c8040d40030219541c45554009812034031140c55034590f401c210001c80c0010031100400a0a81c0b4440e00c144103804000821820b19061130f407c0465030007100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 330453183 1250 330451933 330451949
    0x7050c030703080a0906020c0a030e010c150f06150903061d0601150e2e0e01120209010225050a06030903020a0212011e020c0c0f060703032018040509010203060a 71
    0x300031802c6400d00d548038544486c0d201c00d01715603039400c40c0706c81c43c1c850f0241e4806401148100c0300c08a1694016480540740c80c2e4003080d00e22040403030484960060840000f0000d003d80d540002140310b00d90390f101e1101e009425107030882c0b407a2039442c10105903502e01c484111060300d0340400401d80b45c40055104c8c15038620024000c08079010000c1100c102221443e1161f108001d03078081908441d0f12038140c0346480c1c140451082c8600c8180007a555080044541400030b91642628407042c04280d001d40040c480503c142d42010000b407080c441c41d5528501040c1310724807001030400039841e0256a81c00182000e05061106003000d85020351502900540039009149220065100344000e44c4501450800380c5c1e1510710401421007524000e401000b40318586100c0c80602441c2440c2246400000c00360081000d440d00160385d4044002e080c20020042800700f100e0210102a17085001074503803101180d44001000c3c0000e0200300640340d0242c00504240d1040082c82a2070b143c40d222078042d10090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 330454433 1250 330453183 330453197
    0x10f1d010b072103050103060b01050a020a02090c070b09010b04180b0703110d090506071b0213020f041203020c0a062d14180a05010e0102070e06030102070204020f0d0507050c030703 80
    0x2d8141154071880f05003030003034000061800245501d030540e0005d41a00e005030010407804900d40015103261181000140140e804134141d00c00510b030201c0841e9100100206a5003011029039078858540d50507240925244d4503020380e2041402c20348910b910140064560520f406c000b43c41c1d4641914000e0702060030552600c41c03605500842e00120341d80745104410412100700036041c49a2508401e07207a80001a00740700a200080119a0458682e01c1d00100032440244018960000070340c845030242c0d07482c220510002902183c184421351256000e500a0f0140c04042030821101031026001038041c000480b1410103042c881c030f0401c00100000c211001610b5141d21803d6030766403008020346814140014100341d0780b07806000341480d08403003580c92003540c40d06c038130042d68266406008c1d28010707444180b0401900841280c459040a001b03000145071040580100741030b03a114041da068140790000300400140c01038071500703910100718030340780381172001d00c00455480c2d10452001500300140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 330455683 1250 330454433 330454447
    0xc09070f0309170f071401020c0c0f0a090e0a05070614070303090c08071d060f15070609080d140709140d020a05090a05161b030804050c0a060206010f1d010b 69
    0x8440300303c08601d04a81c1c2d143c1d840b44216995440c1940c8400000c0b14035a04820101c00c6004c01402a2140c070000c540c050513490074a0380170300241c15000d8410740d90005907420001440c400f14811100308034901005000c800721241007252902e07002d50f2001341000a030300c00100148075054280e07020a94545008148589182860109900c89400607411130048113000106c048440b400780f00d0014005501440e15540c81c002c01c821800140281134000030004500000c4481c0e103401003082d10301c64203002501ca101c5450300c02c8103030072002109007110b985500c05000c00324602d0b01c66620a0702468402500e5041550406001c2c0800c24054080c401d0017000b0000c541d2090b07040c201400001e4442e40c42458180c10400107840c0549150400000c074003030121a40d8030840e040d20101c0d021007141d0342d00c208266000c803a443d600600c1520540501c400d000c0981d5a1419200c0040c04181d00402d0350794104907440014180c581e0014030418221f011010707028130003201060464042404250b04d0300340c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 330456933 1250 330455683 330455693
    0x203060601120e0d0503240a0308130b030f0a0f050613110d0f0b010f05071109270c040c09051809030403020a0305071a0f09041a040e010504050c09070f0309 69
    0x943e01d800ea0a090185031003684043d40d01201452144402164540c0040c1082d01c0d00c09082c050b12980c15080419100300b4004140040c00074003020028110310301c0c41d10f9031010b000c5501c1e0000c1d1809180d0b0154141407000c0d91307140f030241c005113940c03103c001c1001d400c00c180014400130302c06600c0d5900030340b80c001c1d079484c6480884c161000d00068810900144001e442e040c0d008110035101c0a01180c0c0c806202c0e45618072550a0380c0341d0742e40c0000f40d5400c08003020204494186c004040b541e4000c0055000510002c146c0c00030044000c014000380750030003991007044155031440340b04400308071070000e04124030341d40c0c8400c20078684850600500c2940340d03900c0d01c5081d4403403038001035001180480c00004000c0c0014030541100c142400c52080c8503040b807815440b52251110100000c8020700895403035150039400841040a1454204840c14000c00810b0a44e0744440821506964400401051181c14020004910300456880b046450a050003400c0400708220000030140c0d2100161b0401c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 330458183 1250 330456933 330456941
    0x1103091b061b0708060115080103080c0a0804091506020319031d060702030d0b0406062001060918031412041403070602030115180302090601031e0504030804120903020306060112 78
    0x207503019540300601d208901800ea440c8202d100e01d81d100d12a0b170000040d103004075030340941030840e155110017440c0d10f5512a00081c2d040000d19103218028180e4140005610500600c01000d880001040c03d402c644500c0080140e50f9002c0b4083d50400c22060000d0104081c0e1824092024100001c030980c503440d505030001e02c3c413840211144103038014002203c1e00040907242a15243c4814403200d86090148003d4811f1031103071101240d031511145140781c0d10240c03181014a06a000060460341c0c4007408001d41d4070700c000c0c0c04090a144030481060651100c0f010000c40c1d6070040c01840e160076061a204a80c200410140041c040d0003010410401d007801100d002c40d0f0000425516540c45442c0c180020208811140110340c02c0101034000003000754070603040740d070000e00c904065911403005502800075460714121000c0341a0654009000b40e10409004038044d540c0e00c119464a442e14100d00811600240d003800082d03582000103036800503145600070780030301e0000980c2403256a8540030b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 330459433 1250 330458183 330458197
    0x601020c011b080a2a0804051215190609090f0f020d060903020d0e1906030506010c0c03060b03150f0a0903121b082a0a05040503030f03040201031103091b06 69
    0x500c40011041000369000140700c0400d01c2c541d01e808120801e4400e503100101100031700510000741400100954a40300810f42403460313002c41510000011690b140d03605000c1181c840107143c40130403000c00c60301c07224481d410281400070001c004001e034039114202403440c100401000e50074121441021512804040040d8541c0402c081c001003a0b6440c0203920b40e50301024a100140d4a00f240002619186c203403802c62108202c09070300d449007000412006080020b01c85810f0048040410380040d5a1900d00d41c02507015280c00a41030600b0003c0604010300c001400020700140c20504c0180c003032030b00d052a0071401100c4001449201031170140c80c440301d1a414154480d26001101e80303808080300070804007140b0741d55210025030b04d203040f0502c035210440c080d0160044403805100c240303101c400241a15296410321500f017a070340c0d500003481c55002e419020960751011041c4030455800d80038444983d0f040e03401c210306510304040003aa56145018001400b040c070f40002c41416103c0303804032500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 330460683 1250 330459433 330459443
    0x2150a20070804180b13050c3408030109050c0703170a0f06030809030c01081e061809100b0607110409030903120f020616022d07120201170601020c011b 67
    0x1819505011300002011000b540d14090300d0816203460044005105031485000803070030882c02c0542070f843c02d03220016005d07041c100a00710800811410000030a90313524842c411203030140e4940c1050310590540d0000b074102000c0c9101840846e0000781c226802da04014800d805604c5691790720604603024100314400180581c3c40c0601c044148001c0300c00600441c581a4100d8150320581c90044400d07000c00c403000710103040030085504415840041260b0010b03c01440c4200e40300e044554400294410380b0300b03060907030240c0c41d000408400383c094581d0320402114198288035098031248a44d103802d00503503200e00c3d52802c4210800d801914101c02550f0070a01032080059801701c007030104d1107000008405807080700c0010f040c80740303410b81c106528580303a800380c04000010a00140c50303800040b40320089491030303814503c1c02c02c0c00300200c0009181e071b207080403114100c0780005021003c01c511485140c4440b00200402e50b600003078441c000741e00a290070510700e01d038908490b41f4113a6101c1c0c0100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 330461933 1250 330460683 330460709
    0x90e04050c130f0504080c0c18160c050f0f0616050304060b010309120302090a050405041e081210030212010c0e27090706081006081b04080d02150a20070804 69
    0xc14024824081e184c01010708003280d52211200c410409089d404444842030140711f140060300401c0b040100316079881c50350802d0382d16091995100e50411540808a42c0c10741c0c007040388128050001c0000300e4001c4807440320514203501f00b010041161100400182419032a61000e8100ea4803d6010820392a08009541a1150038000003000b81d8031494080d40704424024ac04a01e0f45000e219407030003560b000d0801d58010395041050201550300401c1503d00c8041400040c440d0714002e40014070800c4501d5040e100117080d0310400c11540b110851050090b81f4242d62a2416900040c008a00410444181030009062070150000048007036800c4045190741d014041ea504c00010148242c400d942c8800322a560b8012003400b082155129610003c0e0880011a44129a00000b50491071501c1c1f41c06190035100c442c1075141250403142c0c0310040c2d200c0c20041c00d00e003001204080d00400003003400d1003207002c942d24031148244130503c041c4d001d10300010800200302004049400600803858081e03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 330463183 1250 330461933 330461941
    0x11180105300411040b030a0611041a0409050c0319092f03060603010912050a0e0d050307020102120405011d04060e010618050312030103030e0a051f090e04050c130f05 73
    0x4418a0410b07581190305203082101e01d641840c241c01000303400103000e0000c21041126840c0d2401404d41800240c40b10f40c0c00f00301c040b071418001c0261081c11351290218a6503240b91039050380031150f0003028140c1042d070510031b1102a201510303038450750811a4102280c2c0e400795003001000780504540d52440720001c10414a01c1c1c41c800004840101030807010f6480e540d4a00701450b00761144500000e2550441c00c5455000901402c0646600903140c030f00014030454480c0410131440139810144c509600120b4090110340c2c5c10046100d0008918207400d0900b1b14120000c0d0107040d009249944035000030b0605412903c1d80c0c0d00401c020b005c0e100c40420765596030b4401610014500440394240990864080b4a41c1000240c0e030600512046580d032a5a1941d202103901c901407035000c641c0198180400206940e03130034020380c403101c02e01240948010f240310000d8401c0c4030300d6002c0c0b1241a48a030400021171408a14108610f0040d5000990501014010b0703009024403002c4003e0145840180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 330464433 1250 330463183 330463267
    0x7090b130509091903080a0e070303030207110409051b120105070f020f060906070c02040e01050403030515090f0109051e010b04031a060306070f03110f090411180105 73
    0x510304582007500ca00e000c036100d103214140c03214803100d10152100c2c801124600060701c182c001070340c07040d6404000913440c09810002800c09207a40d0059000035000b240301c04c1400402070500110f640704950422500d511940c8854071200501c405c0c40c4032442c40c60001849890300710020f000510f0321402001245401103014054034141c0000d00014481d061200c0906803001404d81d000d126003000030a040d82c0c8848007290601040c03802242c10035102c1c07000079181402402094011442528040303824030f004244000c80031700400401e4803620002084c0a503840d410000541521401b61001c1102c1d5a404c2e84a10103010206640078401141800001d0a2200c50b0107013050324405d0400c2c200120301041c1c00460f18001395206903041d0415804140d04030301440e605101c0c503007141800300e524800e1b400035800b0340d0041c034074243d0242000280010a85040d108914501203204461420140b1401000c4050808200181d040c441c00007640d160048000e900c4034001100020309214103d60070142d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 330465683 1250 330464433 330464467
    0x207090c030209090c12010509040c030605060f0405091b03070501080f0a02160c030312020322150e01020d0608030705030703140412050c100201051b030c0909010b190c170307090b 79
    0x41e00d40446d5168001081d40d01e000005d250085400c004550031450440c2c55607002000041d00c40703036014100d1a00441c16031500e000715442041504060200341504c1503980402030105195a4480e4000013028885070381c10110135900a0240d071060b440a545454415009115202c00c01e10b0301c0ca02005003804114520f6203100070382c1c3c842d07038031507a0740443d044040c801c2c4d004c103440350f01044541d0190310426002c41100a86201d000d0450b510024040d10010030844021001d070002c140d40000d60040031405902a680c01441c82e4001186842010b40b2440e0f264010001d008040200403402040c0b80c4541c0803d480240048000801a01055141640d41c0d01140d4003202d00072504401c02401080c0103200b8a4400c1c0e600c0314134001035a004004003034880d88020955640980c082c4030b040e030369071140d54145010b044030b9200c4541c0e861444800d846510003454004c010410f0312091000040d01c1d103580c881e144821480c0241e1240c0b03580c13609403007030002c503081171031203a4001c1555100354240102c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 330466933 1250 330465683 330465697
    0x1020f0a030f05040f0602031b030a090b060a0308040605070f0b0f010603140610030e0102041a070b0a02030c0d020a030f050c45030a0506010f090507030b010207090c030209090c 78
    0x3400c0210000708504401a0f4400721405801001c5842d084408600c540d002954880c4030702144004800c0c00440701c02c059003040da00864443c2d55403815800700480b030110107802050440e4250001d510f151b944002502c114007a007010080049461400c04c1480c0307844050041d840045112140303844640141891400d201d610b00190410208202c1c04400c01c0040b8040d80c0058084c00682c2001310042d40a48910b0003c00d090790b500300300015040c42d0503103c1c581c0b1a20b07801c00b050741d1841e0350708280c2501709000e41603080e61031041091108158180086a0102130a4100541c441c03031003880540c000c1c0302d242c0c00740914504140400c0754401480004040c2241d0b030000070201170605403403898514020890286600078000000a0441d0001407140c140c5140101203c28811095039a5420101c0a03071010700781001ca10170a00c440c8109000f0701e54000054901082000f1280000035036400e81481007030003180d41d40910800041c800c1c3c04440800d400a0644040c0d810b2511168001341d00c010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 330468183 1250 330466933 330466937
    0x70b071110020c010506100513030303150803030405010c1115150a08030307181205030403020603060f030a03050316141b07091e0f05010b0409050a06150e01030e06061503090106030501020f0a 84
    0x201c0c40103800c502070f05c159049d110031200e04403ca9421698143c0040072050100e010300109220002a0b814040005502c920b04c100c1c0041421a00404094080d1102c940d00100c00c0c0c001c044040c80f444491256903500160441158058043d00390110341d9600c1c060f08408018000002005503c58005100407088c00d2010044000f881d0b44241075a18940d20010013440c5400801c002c00162070010084d5402c004010107040051401070300180c42d043d8042411030100300040100009131000500d0011040d2190502d034140348404c45030281a84500c1c07500e1187e403d0120188003294008006102c0506a54001000000540003018040300e1110802903c0f16040c00e000a10307460740d0f409058100d0786c01d80044c03030a041c1041d05d85005404001c1c010403d00c5d580361400507d104040c407020088140c55110702500c1c50400000605507020101341c029a940020140300007510b800020030700301c14aa0781c241b900c03601d030048080d000d410310b94000b811960020400420b213100c120020a1040001d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 330469433 1250 330468183 330468199
    0x1104030302150106050f090d02060d09150f0501051807030b03010c091a0406020a0f0305120a0e010f29040b1003021b0a03020d052a01061802070b071110020c010506 72
    0x35800803942c603c21401b400707055110a00c070321440c0d82401c440e0104010300c001e01341414200c9401d0310408a440101d41900c00305a88034148511040c0c41c4142090080b0848040c0403942c146408601c1220303a041d082442e604d070107400240702034420742c054071b04044020024445070070003050003454903c49010701e011414200000948042145c41114103d62440c0c010300201c06280d00c4000e80d101585d1800d0701444401c0010300103017084c41945038030800700300c1000201400c002445030308480e488183c403140c4e0740c0b8041254400d642c003501c94000036a0522a0752481d0520300001ca8090900c4030034640d008023909122060a54047d000752130070b110090910700c1d000d030070643d415544010740513010b00940c2009180c0b00c040c42c450001414441000901d80d540c0341006000074460f070710314244010650350360f01c006114014000c2110034080010100640c10310b82c2c66100c2d82d81d50301e0007429580510a0344080c80c80c2241044c030600034071103002c00017103443d85015007400c0d001e40b41c22501d175072082d459 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 330470683 1250 330469433 330469439
    0x140c04090f0905071e0f08070303030e0606090619080703060b010f1701030f060e10200418090311030f030906060d05100e030c07080a0b0106030209150d11040303021501 74
    0x140d8419202e1041c2c1000040c4400c82c40d001c2c0d03000e9800d01c0c00c4006122450801c2c00441c4505481c0810401403030260024031450f40345045c020201e96200071000300640040042c05142e90340c0841184d0000c4007151139030040e901503021405042d0007a40a03403d90700070f40400100380710715507005400c0d01c1e100780c942e90184201200d0844491240006440c5500f420070018408500c0110b0640320440c03003000c0004800d90810340c03481c074010045014400654803907041c40e6091072051120b405d00740c550700340306e410f190504403911085004203d41c038200079070740e441c804141803145240068a0740c460081e240d0312401c1250341140c2e540201c1d0205000d205000204000d410000301107030a060b0444094020b40c4445140380000d031155182100051209228100581005001d05c8000f05140c000422141c0d19519008906010582c0000c00781841402403440b9915203c4000c0b04480040301c03469994106464480004d100903100400900360105001c0200350b000600c050304854840c0c0402c000e41e030703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 330471933 1250 330470683 330470711
    0x1e080105040e0106060210020c010204030c0837031107030803040b01080c0a05060d0c02010b1201091703070e270408090405090a021c02010c060f050609150d0f0303140c0409 76
    0x400e40c03244c45d005070f00088070518102e1030766000d04150301040001611301552a101c01c03684940c540c0118055803c03404e56114048200102c1c00b100d980b800311200e1406031001440400c2c800744220203020b006490100143d04401446400c8c007566100724600d07220706080c20140102d510900030b0140c00d1148020104072854072905a03c00c64000402007450290340f503070200054200800001c05542d00d4150811941d03940c5040072404941d203c00000341e055103801c201407500b01440f00c4031000b010400038080750950088d100c18003020b050b035880150300b104008100b501800c1192036107000c00200103210030404154020866000c0488081c092601e41e0046582c5952060100a5200001c0e8941801e214504410b19030101d0050400010300c0e039290302c0303020030b0700d00c020141d85043d5502c100708049850b20b029041d0300b100142c0b40d88280801d24402090b80c9000946025144400307e942500404d4403940121040da9410401505181050480740c1841d801a0241e1a0071034100a85140d40035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 330473183 1250 330471933 330471941
    0x607051219050313030e0607020a0303080a0f05060307030212031c060e070305270120040603060608011203050904020d09030309020a12080906030702120703020c09010902030c0a0f1e080105040e01 86
    0x104104813494403c4103960603100b42840c00c0f0004d801000500001c3c2c09607480c42032010007140a0b444010b00d07071424414040451701d00000c005225858142800016140018010306072a41560084028440b0aa2142c514040d000c404c02d004a040502c902c85203100d43c10400c01c44002c03805a210304c2d101c0380c40580a5407002c99911070017800100e0901844460300d8915503042446200000d0704031442c0d1841c02944401c880d0320354003130000082c100407403945441030764003c1881d460058503a50400b00c00740514451000040c0802c0000b0034410040d981d01d504481580d0a8003e08100030405860040c01400070044160310400701c5003c0000c0d00240596070002c4203600404091510f030030181082510740021380903404500c030f5445d11000003188080203208150003500109030320072a010400124200c160000d0144900500c18010380705280700c01e582038003c8a0038544804503005030202c59400311481c0b444d40320321440702e41c04002b680104240c0e0688030203840903c1000300c42d200303103030a80e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 330474433 1250 330473183 330473191
    0x5100e01180b03150a09020d0902030f0609102703121407053009061614041203120c17090d05030708130b04080c10050108060c070206070512190503 65
    0x4040c00b04000750707400c0070104c060104401e006200ea20140e48600102080343c000340820110940d64800b2241940b404003d030141c4401d0304002000740b0724060305040d458229141800c0e03802a00d030011424001f030300081c40310129650708003001000313019090052816000500344840f280c540203c08051007040040a4800ea038030381c503a6484c2c0300b0600700134811243c000c05104044000700c0700c00c1c0603001a200140740a00550f41c0200400e090641000000501c0140d81406000485800d10101000001034408440d140ba40c40403c001a07814181c0e200310031820741c1d05100303150618248006400540c3c450b1003034202001c448441c2d41d811009076540c086c40030010040340041c400251303120320406146a026400c0e0310a07a01840480d55100d820880907181152803120100c1d01c0b414400e0204000f42d4600440300c0c090046500d010101c40c0c031600041c100000b0320400250000641d04d4001c11a0305165110b412114002c200342e44802103500491400d141c580074000c16032120a00c6a8240e03409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 330475683 1250 330474433 330474449
    0x5070810050126091c050a0e0402030a0b0909010203070917070b090a0b040b042c0a0216020a0305060f0c0a080a09021201020316110a030903080c0705100e0118 70
    0x140c0e09001c01907500060f43c3c0f8074038001c280a0f200301e10b001d0102e01202801180408002d04002c402e04104040c3d0382d8107816050708110b01400f5076102c040d40100c0710401e502c400d640040c0d40c1e0701c96980c070002a00001d00000d401c18020b10500543c94015402148214607075034958140641303d105085070300300301c1d0100301065403241a0a200004041c1c00419030018001e2500030b505641d0f44002e111600164070940012802007010005060b010170a07045c04947d1368946a001031103144100111840a000c055903154089805d142880403968180101e54000700b9142c84290b40786440c580c1c80300100c4000d01030030b5540e008200300d9200d00081e80c40324002c2d40c44404d1140c0d25480120001c000001c6e090341e2080c200244911a000300f0b200541c000c0140c1450300108400c118000b03404d2403154082c0300002e501c5003d521000c0707640040e000043e00d83c4150369035550444d41210515020503a0041c65112810800110035039400401c001442c86013a2540c40d020303901d8150070700900c0781500c00c0b042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 330476933 1250 330475683 330475711
    0x60f0e09040c170c090a05090c0307150206073015080609010609050609070c03140a050c0f0304080a020d1b292818300c050111100f02030703050708 65
    0xc2103501391f041a40d004060000b107819000310007000a00c0c1104035803110340c100d2401032000304030b03a0781031061a50196a50415201100d09028919168070804c400c035240c3c185044900602d0070700e40d070850301c4100460801000f05648554446880c1e102c2610311315229880c00a000581c46024058035219010081203001150740b41601603d10b0144464101c007000003e59554480c28262800340020341d030141d46083d10740302003060540c81e18030b030404450047c0c1c1c0103002c204401c410000c0c5500d00191306035118100710005141c0b47c0ca034601010103c0201000b141404510315203c54403110301d490f80c6900318044114a588007440d24810701d046032411008020071001441c0e1001c0a03070411200516049107203030015480001840c0007900441c29100140003a151200400d00d544400c03400c0303200440f1039044640c4e680c07460105191150720f0601c074540703540d964504020b100f80c08800003800418003100c030005182800030b40c03088034075002281c50000491842442225168858840d210080e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 330478183 1250 330476933 330476941
    0x509040c11071706130308190609050c09090702150a1104080703080a02120c03090d050c090403201516050f030405070612021207030b12010e030c0f16060f0e09040c170c09 75
    0x20b82c812215840403601e10b846480002d10700cad1951007214401d20650ba030746a00d8900c80070800c040c51201414840c115800b00754a50280000e45a03000d0304441c0c00c410006000c0328a10070071080e801990b00c141d1031030041840000a1028182c010170100740a58261100020400800c403281c0c0181060404560b02c103205109690030609140003e550080b13040f100e19a810900140005e9002c4400710300040c1c0b0790103c0010610604840c005a40c8004041c08016446000d10f2405210081140700810050000b031580036018204640f02502100040c0e40c0e2460541043c50b5910024812800051100850840150500d100b40d80b502801c2900080b126103480380124050080304002c160f0220882903c0840800240301d00c80000700628003540d266076840b00000d0902e08001078040b041e800c0486080c0c07000c0306500d1604192100342c1030004200e048044100c1d00221500800340e0840f0300c100078003051100b8a040d02d4200c0d48a0003940c0401003040019540340c04486d120b103134020850402003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 330479433 1250 330478183 330478201
    0xd0c0605040303110705100b010f021903180e01060216030201170606390a030c080a0507080307081f0602070b031e0f040c12030509040c11071706130308 67
    0x3268001d4080e00d0301180d03926003880030b09031507400310074201e40990245075a902c42d01298011107200a009003003810050303003003c80c01f9490308186105510240704144988007014000c2040c00c0c0083d90200902980d036031241244d800b6040280500700140c45524545a07050200c115040207807541a51040034400150300240c0d548100030f000303103900c010180206403c01d00c20280d20200800644041c2005101c00003402811024810411b00a504031001c40000b10360050804c1c2c68096006032450745d200890001104d1901426030010418034000081c403941c40e501c0310025008410040511000c0409a0158082140d0f540305440c0507810440d01049031101503c05558440000c120440700c4000300000505158012038144080b032408205200a010b0124807103400780c5040c4044a148000b81e44014006019002100e44944e480b00030206e130141c484c5000c5242e003560701d003c40341c1803074444030f007804c1445400c660002c1c01d10800c0c3c0080d5070414a6071b42501c2c0d1a170162201506902c40c1408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 330480683 1250 330479433 330479441
    0xc090c07141c0c0303060f0302030a03050304080904020d0605031e1c02010e060103050106030c0e06030304030611070203010c08160201060506090d031b0f060b0105280e060403230d0c06 81
    0x3480107401100e445140c4040d41d0000c480c03151989954083c402c00702c82c540502242c55a0704a001d4912000e0300074001a200010445190354150804684079079541c609224107204412020340c02c07500104841c0c0000c110b94000500340c07082103041e1003617210b0b13030004007080e03000280d09003905600c07a259000114040c090062001e0410f0300c00400d1130200c28982d14940781e0281d0045581c3c1e907680f101002030140614007003000d441120b5100d4030318100180000e60303d00441c00b02500d070b9941d94040c07030030100c104400c0700d802c2d56019000b0700098101c0d02d40904100000c03242007a0f0301031030000000703400b803061040d44103640d8010082c03030400c0b80110078801c000514000c1281444032400351040d00c1c45c3c000f0420080703103116214101e210055882c0820070344004021032030602c6000d00684000c26180e54040c00c000000d41100440c40421083c1240c00100e600980c0da00a0300008000c0144401010340301801461100e040c1a02901c1228407a59980075001c44400990b03110a80d600040441e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 330481933 1250 330480683 330480713
    0xc08070f090305011a0a0b1e0306210109020102010e280305120a0912030b0f01030f0f061d0609061f050f2109010203070e0d05010219020f0c090c07 65
    0x2410041c903540300d80e9420700711440c18150303840c1466206065030031450410388042c060001c44145504140503180d064046442400c1c4504110300044000340007500c95111200042561031000d205000114004a0082c071210303005900650070704610a030020400a07001e1110149040b4003680a280e200b01f20340942400d0380224100310f420081342c1012180d40401e940208130140f400584118a86001c003500c54542d44000289070038000803125603994407500e002e0501007030030003107031100002c06c840c0010407214010006a42c40c101000c600d0000d00c8030b03100e00c00c400340c07400b5405c0c540f2101c08114001300c049643e0340c1d2000c0d002c0c1d0210a50f82d030b480f903c5112107140382449030030300c1201c030640c000f85d4200403028802018140c10341c402903100c4459141c0c100d0b00c0e4070001c40c80e500340740038001e00d03504000d0301c400e0140c1d4a03020342d4001c000c000d5045488103148070031207280500311207400035156900f81c0e07000205881740100394040c903d01000c4036401640041c260a28001c4256911044526801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 330483183 1250 330481933 330481937
    0x5041202010e03030d0c110613170a0201060314010f0609023901140703050f06010203040b07110a0905010f080d0e0111150103060203010f060c050a08130b160210030c08070f 76
    0x7000700080b84215000300500c81b416615a9411028440d42e042d18080c001030603c21911024030018004c1100200c03000c401340301802e4115601e428002c0240c0c050002640010141d00100d403130386101d102d0641c0f0060308048000350a001450752100100240c9c001c1d485c4031b4142001202d10440c00101a03004c2240050107451481c141900b524039107401c45004ca200041d1100b031040403c0921a414442c290303210940c003441640d2402c00000003035690141e070048810348440040c07258113101c41407503119100003009042a1b859034888508102a10083c0b180040b40701d000d48020030421004280d09100156503560421039040c03c030011205404841808005405061130545042011450b514040c50007400056501c0d45044049808110250303c624204041e0707051020001b4001301d201c020b0742d80c0007035805031500c51585485041c007500f5848405003600009882040c4058804c078806214000c4039400308100c01c1075029810b0b04c0041c0e03a06030008010b400001d44241c001d00309100840000c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 330484433 1250 330483183 330483187
    0x31b120a30020409050f0f01050f031e0319050403050a02060906070203010207050c030d0306080a080703020f0f0f070e041a0c0d090f060c1b11010e1c0b0705041202010e0303 76
    0x700d0248040c0c400e000e20070104580000d0140000009805440d401040e5800030001c0791800001d00d0b03e03042d106001d440c2c0306607400d00603548581d404006203400a80c0c240100110307229120340056a941c80700c181c40005181c1c60811001042c041c2050320122070b0002c02500729004d140e03003004040e6021120300750303001030140036250258400348041d08101f40310b40d005100819141040601e0400881e800c3c60405003801800e10414501251a51080c0d41c4601010340310f200e18a810713400d180c07194201c2c01d40da102e154078928042030001120764800400005884000d500c1d15030708400f80c4411103001d800420a04005041900044400c60388160001d56007401d046840302c403078040c4c03030350000103481648145126205010882c0305100c00304c0d00908141d60302d4a42c7c3e0502004039011414003902455000084c140141d000d0030102106d03400c0200342e1143c200707841860041e10280c10134145d8002c841e01d40000c1209004a04680c00d41301801402c0000c08001c2c0d0044801c803c0140c03555400d4082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 330485683 1250 330484433 330484487
    0x302120109051915091a161d0d12050307110303070e060702030a0c0b090f03062809050d0309060f0506060405060708090a080a12020102030c09010305091e031b120a 72
    0x2407441030045d03040c40340a2050703686040381909101e68030042c10100c03080070712801485a07180c1020922021084a140214082c11402c00160b01150345c480083d0072482440a50301c2500d5000000f940f0401d0b05031103090f80104083d4a0703690700d000464100011906004141c00c003403070444090415188020f0898100100f07554a0b107401c0c00203075002410034900450030744010f00c0e1060782c040c81ca000590041480f2700d820b0a2a00c81c25180d80380c100b0b14410314094070f075001a03860308036089041e00a0f048030105951594000c004010040d41a6201407414468074144a040c1c040c0c0c6008010041c5090b00f01030910301005160b6210150480e841e500811840980f5103d515800c0014a05130703002c1c002515150520780d2300414000c0d801d0003164810010010450280000d80344180030a00c0d0028542d92011310462500c07039941444a01118a10b1782c440c20500004000c01d4079880c108210300050520840c00380da41c07d54895601040d5500340589030245204d80d200c42600503c0f0301000b6000c0342 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 330486933 1250 330485683 330485723
    0xc1c1b0f14011d0c031e070603020313060c0c031b39080109050106050a120f141f2301030816080c060a050705090603060918150103021201090519 64
    0x500280d0f0b592154016084130241460b0500029903d802c450060400c0d030615480340c0d540b070b042c1c6170003154181175000c00462804c0c121900c3d985d5010f58029001c1141c00d11500000d407000803c1401207000503000b40d11040700c0400c904c0e074a60281d501070500400042040030301e8046000501c41e920000c0016044010340701407464010f80100a04000010145820f040250070340f5800c1d04400e02078150b482040008282042160030810b4000034440d0082d1200c0c5042d00110940000b881038a20868001c2c0000c8800f2994003502e40480380e0080168049141042d44d004601c080b1042840b0080700041012505090090030b090b9801c0c0c0d101850012a545d44a400c0c1d04400c0c16007000794403010811060a034a03100c4d50750411070508000e0304024803000042d0651100901031400317046c82c200800d0489038608009261001c01d1300655882e20741c01c90395104510024441a44500c1544406081541040c41140c6d45503070468094516451011240c42814000d150202ea03010b0300304c544820506 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 330488183 1250 330486933 330486971
    0x6040314090301090c091d070306201b2107030e0d020603100603060602030412080d1d0a03090b0316080414100b0103051806011a0c1c1b0f1401 63
    0x54805e062980b9940d05200107401201e00f40d1841011901031030f101820010300014a5030201c951008020422038031541119400c81c260040d040a00c2e0707004154001d00c5102c5029924100c0b07016000c440544d0349078504404a07003107a0309004ac0061081029802003407103501c02441d01c100c044e10b003400c2c545190b80410001da00c121001c040340092650280032440e4580600c10050003c1c0c4021418182003950035040381c22103500003031145100003a8452251080e800070108201d94941c00200400c8060400e0b4503611951001c0b000101c8411005c1a00e10180060324040c140c0c803a040460615170080c1643d20b144042c10581c0c0d03400d09400c02d03400d08082085110050100b03000d001c40c04ca400040007400b651300c09000c881707440c040c0e20110172210600254646c1181d600702019200703450b40050703076006803250f0103080107907005454001550040d81940403268440a03526507800e4900c403800d4082500040b00b0040440702112a403102180c42070300c2d0045842c0705040001051114002080710300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 330489433 1250 330488183 330488201
    0x30f0306130504081b15071d061204170c0a0c0515031b130512010506010e090c030a1e02160201110d0e06031f030503040509010b040806040314090301 66
    0x1500000800000381001c010389a1100001d000074011410281d039514450701601d02c4010001e855400200300400c0c0c2041201c0080d0309219002c281c0d0304042800030114580e0411892062010065140080c24102c0440e800c48200c00c0038070f80582c0f5255503401031044001c10301c84080c0320601210340020000e020604c036051142d03140f1080ba07480d00040c010050701d07094070709100d40000d004015050701001010013103821401e202c41e648403030301503080719080d91682115801003d400c031440c2d0003c0d4158840b50084600b40c03204e0004070402010089100d804950551080d841400460400c00b01c1b030708101c040303d83e2074801c0401d0041c020010812600b0044d41d00070f8442d00c030b540450540d42c20081c90b841120b42d00002d00b51032861030324080c009403042c01c030b440c0c05483c0020028403440d1300c06d60301180100d000392981d0291692824503a40c4c80d00a40200307441258036200009002121000f12001c42c2e0000c00508000d60395908c05031403c1c0b102d0006d01c3c0700c1d00390800c150031060703900b84214a14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 330490683 1250 330489433 330489457
    0xc150a2322030506010905040201024201090b0d020a0b0c01140405030d050609070f14040504151a070f020d0f0605130b0907030c0b030c04030c060f0e030c0618060c03 73
    0x81c103196003000c500e818810390000002074901702c14000036036401b10781c40c0c3c4038029110340301042c1854441400c010111640c061003841c9050882c2800043c4100c8255049503541141071010a011b8410000007134402c2e840250b2104c5151020816000b15402620340c00900100000305c1c000301c0b8003640701404040340c044540340c02c001040201d85421344906600204256000303130040c81c1c003260141070446c00000300340c248440d10031140010300031141140d026020180041c07042580f0400060300c0751089019a4000b1440d00e0240d401004803070301500d41080d040200c0c58064401d070380a012449501540580e10462100f105501085003406030600418840c1c0c041050100c0307a00302a41500006400d1914540120b0001c2012a034841c5115054035118034840b545c0707881e125609520340c0328170751000b0a2210943d400003201d0360800d020403281c0741c2d103440740601814554105502e5104c040c0e40380d40d000c0d0080c0081d00f03403501a025a60746803e405402c040c9800081010070b803460704180c110481c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 330491933 1250 330490683 330490747
    0x509010617090a03200a02132a02280606081605040216020130140c1315020102040e100923040f060b0d050c150a23 51
    0x82116144155950000d407200207841043d0555600401202c001c0741c131102144030140002c1c50110b01403003840d503820f500034420307403074101d40480da500644060644e1056600010700d80b010741e0140b0440c1c07506408810750281050380f017200c0106d4150946442c0043d1200100810302e000130700d007071007038001501c0c02c1c40083c0b00c80c80b2440401c0324111307810703082940280e0051102003412241c100c05507003116424205422003150031005044042411841404054080c0070503000c02a000c0e40445485070441d540a0030b10703034400e410140745208641140003041c0c60003034108202005414055040004c5200152400740d40700231f916130041d020b44030b0441c00c080405040080d040c242c410254592440c4250403080040e00b20070051151000308041d200005000390001013007104d52229081ca040200403501109030b40c2002c9a481039007003c040d0003000303a03803c0c45504400c240c09541024129588014403891252171190041c02442080341007003030144a0948282024800c0c1d0a100041440b414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 330493183 1250 330491933 330491957
    0x1d04061b1707020d170601020102160f120305060f10051b06010e06150315130203071106070908250306020c0a1104150e04020f06040602010e0106091119030605090106 73
    0xe065618042c11070300942d4081c1104819940d00000301c00852900d00e00c1c551041d945610060780680300c1c1c200c605d94801000307608002044030038402e41c28168000c0355500718144400c50103a00f15582980c00c0d56110380848000c1e2801d1038528a4203c0c00030340c41c035095090207680c2200900c0d00031034884036441038100c00010f22207c82c034070b2049130380090111290b030248800c1013090620f9200c045c0500403a030000810b060340701c3c5c803080804000340b08400011540d911300303500002d111401c12450300803140500001b2502c02882130744d16100703850089014008104801d003050305441c204078048000c02c206140c0010205020344003070039500076100090141c040b9280703400760000746820540c600c214038041a4078110707003000304400c00350381d415500c40c4007603166400000c1e12400340715052540b2140000d1f000c11250381c1034100340e0010103901c00070b021a070b84901445080d61541540d442645d4000d2002241202c80e84507598040c443c14100054495110741c0070483d82c841c00d8210700c001c100c002c5004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 330494433 1250 330493183 330493217
    0x6030a152301140703090303050a09050312070203060f100510030b04140603070e01060e04020c10050114040e07031227031a011e03081305040501121a011d04061b 71
    0x43d91600100700000d8039140d2103660280104516000103410800089071a20205001e59a240b018000050403208400d40c4610b1042065000e45402c034000d002d4080070801c4008181e9503603001d081c407422403994050900e028090200801144041016121840866192144d109072800025141145c01c40e0307240807428503140c003d807a2300807802c203281400100600c2c2e9004846010f00c60f000c5070056a19007030400803e01e07001003082078040c01c1b45000000600c22030081181c000d116410390b000d000c45c0703c0509829498562520028203144030040300e9480c0c962040410b0007418040184494201d0035801d040d848001e00380c0c0046455094101c040c283ea5003616800a005005441740c41034811414110854001c82a2000034112403011030320807031812014101c2d5024000251007044107681d12a8810610840a041551602001d003640300c200c0c00c40e02ea00c1412303511401d4403d101038004480450510744010804d4075a1030380d4501d1840100c61114030004001e44503a58904084840880 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 330495683 1250 330494433 330494447
    0x130204090608030f0a0c14150109060b0f0d200f12060405061e21060115020303090a0b0a06170303060906041e0e070803040f08011a06030a152301 64
    0x800c100e00e900c24058a51021a40405c5a5120b001464140001c410602c0d009009072401c040d0508a4001d1f510246682410b11010f039040300c44220091020580c0c1d9401881540b240a9480004410030000080e980f075050b0031071480740445042202900410780321080f20740e041112078450343c4100203030309080f07121010083d41c0c0040d1b0403502003115041c89000118800c400400c60904c845040b185940b0076590030342d06440b100316864007881d80c07024002d100740c4c45000900620110901000b417100310184004183c92040780e856008082c9045240c03a0f52124001c02020000d00f592100303c0400d00034070540480340030800c2c1100464403801c0c440c082004851000f00410b00a81c03408801020154500846089040c00104005103019042c80c2e4181005966081038000344400a80041c20800c0c1e81038480443d8030030700080191403a80c80070388400f01c5a0310b41d4a80d100d581400811000031842d030200c5040080e018a42507080e981e9401621501c03880d88201c00c50300c19647c120b00582d40c0100c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 330496933 1250 330495683 330495689
    0xa0b2d01060e0a12020108131e021201060308120901061a0301031a0402030d030b030c04060f1a121617070e13020301051806030f0604060507030b040b1806010e1302040906 75
    0x144141c3c2c80c030309180c181000064200ca01078100400903000c1008525042503440170103030020425001541c0424010740d00a2007044120300801404181d801072036810700c2403105503a88200090f2600c8980600310a51807005000d140480d5620b40c400190108030400b06020300c0c3e02080304a440398034604110000903008402e0b1846522401c0400c0016900480d240741e101c800b90500080e42402c400c0424500f8a0b49840c0c02d80140c03a01c0408140c2280360051641180c4101034004910260b40c80c1c4030350603014000880307290b0301515021500701042c4c03004081100300c2c01d01d406890b210010b00c403480140819101c1402080800301c0617060781c1040520618010500c0e034081d0b25552500012450380c12a80c10000541d01e10f03000807421580e002e005080d28005554101c4034141003a040020080c182a02c020300801d2a10341eaa00706410240107082440f24024a074980103170303160222003060b25000781042c2c100041007101e86010750320f0b14031090701049802401616113017803194140844045070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 330498183 1250 330496933 330496939
    0x90c08010503010b0a03060507110717010c11060402060307050f0d0b1f0203040504020903010612030206060306100e07081807080a020906092a1c0b01030501170a0b2d01060e 76
    0x1d4130700242ca604062204603a030041c0001215900e0401c05c8401d413181c1480c0714041d010390400015090040d402c51444621624001c1100641007541580c00c180c1c01d0f0403c01194000c100040c025246c0880655406003860801e24a0046403e0f4100c1490340003007411011540c1d0b60000c400141408a0b0316400e598104115281656034064041e50701d004034490540302e00e40001e41680142c8080d0040f10041041040300b02030303950203181c003944035842200e100307010740310306c5000406035254120124111a2810315401d043e40b60b9500403a82d8840061a115852009680000040d1810071100c0d0017400c6e024040c01d600400b0707104206070340001a00451241ca00c2c002440b002041407800b64001030340101c50301820081b1034500001078001c9088458a5460b07074400b140c0e50b224190042c03900c040d0240c1e13081040b681c0720a480c00c0c0400001c80f40c12442c0d40200040d60020701050003803a0012801300e4007440f92311100b0501548000445c51801d9551010801000450303003003014803070700706811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 330499433 1250 330498183 330498191
    0x70f0606090903090540092406030c09050a2901020f2b0903051f1503110616120c031b12030c05070b0c13080c240f04090c0801050301 59
    0x24246000611071200300300020710f00703000078040101c00c00c006c41c203400035603049081c004c0703900b01d051807000c52100c1a06141c4e1032610b41c02c2e815400115109580c1620780c0803030860100c03402c102110004260080041000c81c0c7c0c0ca2100c0c030b0162180e0403640c2c400c1d803546030030400075003c4a00022304154500d101a003ca81c0061552408154103100c0d400402c2d10600b444881802c1032101241c03035a0f220350020f4454003420002c0a8052a0201c0707004920160325400c0c0511104110806011303000e501c0090403c1c41d104c1a0030b030079490104c00030300c8495024144500e4900083e15450b841841059a500104456041560815401840c0d03405068040002841c10520135102e9814003185454106c0400d9910b000228103240580250345209400c01034012003880d060080c08010391003149100350140414500003000f100005248040d03010250100301440359545c0c020480e2003010940500e1001e084c03003102c24501c04007000c3c000070442a140800d102449220140a001060304198060303414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 330500683 1250 330499433 330499459
    0x18090804231221180f0d12030f0b0306090606091b0c010b0405010501170615040b0a030605190302210a0503030403020106090b0114030412050c010903051e0705070308070f06060909030905 82
    0x6243c04146019130683d003095601030f0480015240c5030540d040240151041828a0321240e03059000c55010541641d08108041c140800c0590701c420807100f44170160b1209000031607608021a805030003081c0d45407010355103040c03903036288141d811407607070003150f6950342e05407983c5450a030050381d00521007800c0240070010300d92a0f1201003880202014094103a111083c0491070710b090849000301a2444082c0d220b18641c1c1c0c000340501090303c2154031424000d0880a205001c00c040401200e9005200ca000c018800310741c501501d0031035880c640079000d01e05503074000c40d0090000314440c1e4820760001440307904108a090444280810346410420b07110444030302820700e071f811280c025400003da1548400300301c40c12900d41c801c60303003801e5055080c00d09501c10560400702a01892110040b0440d0b221341c010394442e0381e4011494050080d030300143c42000031545207001420840c4c09250741800c0042c9548070740f0140d4080f540074000c82982e481400741031560100da180c0103803000311803814140c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 330501933 1250 330500683 330500707
    0x917040e0103030e0d020a081f0c050d0b0301020705060403111b09070e030c270108030f040b03090102120114012d030b0315010f18090804231221 64
    0xc0140402400d0014440708110b00e80e4a050815031441ea0007000245d00b0750321201d01da91035082011420701207400e044a83c109600703841c0103514441060381eaa19003400340c02c46524014013890b08026425540c01c10207040420020711103d842507019032111514001103040342071410f8402e090b4455902c003464840340a40d62000c03803541d04601c4c2c1349451455401c007000041d04006004e01c98550044100911414101c0500c0c010b081201c03010211005170f03a41d85035802d8403803064060160014801300b00034041e6180d80c40180d5003000e04c040c001420145c6a5540245c05102030b0001c1c55040c10107141c0d84000d40c1e000c29403a140d5074000d4007440c441024618048103200c045202e42080c1501c48681c50000d8400700500c10441890340d00760313804c03540c2d59a000b0850803594029851840030b1242e02c81d040e5060307400f500d0b810690200d140d5242901d80180c403031200301903915600000c468120381c9641c542d1f03045000780945040c04e014001040d400070f4100d520311801854a0a080c41c24014545855 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 330503183 1250 330501933 330501959
    0x20d03051b0c01140420030a050a0204091e0303020d060b0901200102070222200a1d13050a1d120919170607030e030d0c03110c01091704 60
    0x808101da034507890b84161003046000d448102c0045008540080401050000c0900382c1c43d000201e12a0700b81030b03188040c1c00c0c1501d0340c11080000c0e11030390100b4054001400c15501280c0d505004401c1640b030041c0506045070703900d252940070b400090f0003291403055480d00c5d200c2c87c0010010001c0b80d0707240a05410000e04610340001850040e45500030f4440d42d141703420340403501c440e64000d00706084140300f01814144003100b4200c01880360320705130465454155100583d190f140b80303201d070340e402c1003a031800c21108516010342e845060600c0b031006080070f84807904100e03d104042e41000c0703414505260f03050211084480301b81c413840c150b144101d080c0380c00403d050b01400e40c00b000865071400448049018241d0240050781c040390039401c0001c804448400d0042c40c090b2900550707a5584400d00704805072416128400304c2d58104001600d5801e0b29a0b0003000902c10905010071140b0900c844181a90480410650f0303a0b51114941410080c0c03407440076000304800100c0c03606160a05820807042c4c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 330504433 1250 330503183 330503221
    0xb0f01051305150d110d0807110105070816020d0b0f0901110918090703020a1d0a020a08010e1f080115050a060e010f03020c0706120c031b05070201140a0206010501020d0305 76
    0x1d580d0a1070f44900740100c4010070140c601c1c001d08031b6528003c03d0f14050a0a900012060307502d100c060141d40c41540c07040c821682c0c41900603030b80a04081c017a4041a421410203c001ca90004007111741c200020b25202c5400d20554100480d109140b90496003d030941d0051803184558500420080429681e03440041030312842024508030341e0381c2c400640b24034010003904060341c410007400d00000c4c03600802081100c200803d5010b50060b0f01e801d08004168080c84902c0008580308100600900c41e84a542c5940301d58941004036940b8101140c8200d03d80881d007003643d06946410b14a03484400740100c000003008162144002641b80c40401050601602c240b2810001c01c60041038841d44030380c05840c41540d08038140c980040e0348600140c110f107020441c0c50b50f082c1c107101e0ba00b107126000344141d00115462144c1010b80b48010441100e469200c01000c81c180194082d000890301312a001802e003441480c1c000341f10f80d504002c00649003450b801c0301441011300f01020818003480c17241b007040c06 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 330505683 1250 330504433 330504439
    0xc01050415030f09050a020111030304020a030b0402030c090a0614090105030d08062d0a0909020d0b06040f0501030c05010809281a090d14040f0e130b0f0105130515 72
    0x34103a03007808101c0c0034102e0300e561140140c0c10280070106002005c00c4a02d400c44c0300b629414480319510700c0a548071f00040740c020754800c1d46000108045140c0b0100164800e00c0103064401c2d9007582000120180c0007aa1000000c030754400061001c0004281020385038036040b19580c0c1a907241800203940e8002e5080d01c40c04020340708000c951181c6502401d00c1c0d01861407240e80c1440306040070212007540454100600c03072141d0010000792942540302da00021500681140742c030020300d8840c40c0030610098591a0810b40d1107031020201b030303514402e844c0614480c00e2400449442c1500060030b0140141c0303440016000080149131405030816920105a40080161081c140c18280200c2c40558035424080301c0302200d04209910902040030095036a00f03032a0901c4100e40c8040c031000c41d0045011300d800344200c0c800180903414041010300d52003d000c24040c1a09800ea640c1c940e82000181c4000c40c3d540708400062040c1d1a00c1d0f9018600ea40405c00100003928107180051341c0c500e107200da802c0c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 330506933 1250 330505683 330505709
    0x9160810020c070503070e0a050a02070f021e0d1a070f17070c080a02030d0e011a1320040e0901020304020d0206070311160611150106050c0f120315030c010504 70
    0x82c80e03100902860004250080c281d800507079480355030301544c000c101c403903e00d410300d0800060f250f088180b003030301e45c201c1e00001c15000c0901c00354240844940e26030103000d04500b0b101001c0d103960307942d00c0201d20b400d4466514402c0c0000d050b20303000c4c819840a0b105200b80b201000d0b202901c250b01c802c039124440107402c404c041640b603281041d0b03580b1003040e1000e000c5040000b42100c525030004000c042002e040c150420100c07908062446c225000504041006105036004180c246415805040340c102c08040004041341d007590340c1040d94031200703415890040003003401c00084005680303ea50002c00700b0b00035403640c03070f090340064021143c2c01c800078417518002c0f45080500d0b1243c80300148400d40c80040321120b40e041003560b0240b400d188034103030000b1346400700c0341c0c4102e601040b03a810011903408004880d90034040f040d10702c1c0d041a40070494500c55000b4007404000c0401034045900000740f074090342c030b00707002640082045148400c940607a0041c0c0c403204060740d03c207003114202d540ca498116 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 330508183 1250 330506933 330506947
    0xb0403030801150e090c1c0203180a0210030c020316030c0201020607091d2701050108210a03050415060b0702120c09040605062404060822030c0602120403080916081002 74
    0x70f2074078040c4038090a000351f54010401d05010865004500800600000104420740d00409655601003004000e400c4580c024118680034040d0300805101d1499005480c20001c0312614215506040d040036030010f0350340c4900e45c0135541c05205c413a800102510340144524144500420044900c02c04401543c8107070001580450711011110946c0c04007580b5602c2d00e00c0102c80c0103010b04001c2c02007260f54041ca0003400f401000900601007030741c080c85929410042c0c5201c05034003c0000500a440100801c0040d85030900c10748180340161540301852515074440c0c0c014069034020308001c82c9101c0c1d00044c40340703c89585488404c4c0d8481d42c450004503843d903400c000720301080140c81030389540c0d04000030f1800050107606c0203403040c3d41099980d5030070381d0b48494001012081c1d9010002c090001c130445040840c2c0701f8a407000c071442c001c40000d407508480d4a40c841c04901c00f25015800030700c05000340104010140400085d440d52510002d000b0381c140b03000d03141c40700082070303047d14003950014004c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 330509433 1250 330508183 330508201
    0xe010302040321020c0d03080406050c07050f010f06050609030a200604080102071109010608010b0a030204180e010b010302091509132901091d070909060b0403030801150e09 76
    0x11800b4507803100010001ea00e2814800210054140300c20001d40030b00103800c0034070305050120486064061b81c845009031079a0b212640244405050900d01d03078000c01c43d40004c11010490790f48038003150000007400601c03049140d002c455080d000f80d4130a290421084065a400080c000750942d00310101101c1003c5c9980301a40d01e506c10300180d0380001c0003041c00544c2c01019800b901c22503001d210034902010320541080002c190034014a80444d00440060000c03441400107490f1440250034010300d0b058413014081c1c2d2000601c003044140f103880d00030100315400e003801444254482070a05500b0030132100005110740100d066664602c440200d541c0344180e8400c84000981d041164042004051030b20768000566030407502002d0002500e84100c19035407103043d0340c0044a0711082c4408d801c03c05c195024110480c05017020701004050080403601c00468810340005003001845241c3d00c0d407035440c1c05011510142e103d0040ea4404072032141802c0d422440080904030210340d12504d40e6114101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 330510683 1250 330509433 330509437
    0x50303070f2d030b03070f0815010b0f0f0702060403060b1c05030a0c02030718090b1e04020405151806030f030903120715090b0402152701170c031b070804060e010302 73
    0x8415414442d0380f000040c00e01c47d4400f000140c400317035010340e08480110042d0b00c0380c0550030310072070780e6420f4104107d410549402c80541000305181d22482d01e4003a0036000130741c294106420903122103941d04490415442d010b0f002052001800001101c2800d494848544a01034000f0400c280030016103080700315501441244003400b28000001c0003145c50340240ea00410175030508990008507000440d15a21018800c0c0f02000441d18444c10f007942c9503802d110103403601600c03c000c400c0700d1900c0e41c2801c2c2c0e200c2011189034041c48800a020785484020107190002c8151103020a400c00c114000e9030351070118007030420b5003154150766a588881d24210018a40006620341c490340342810707000c00c111240d000300307000314001c4030304194010302a44440090311032606000c42c0031240078140c54042400e0b4601e8108204141404000100c82641003207014a0032524a0300300040002000041d0700c020035010f5803514a01801070504c0342968403000c00d407003980615400e00c240000c040030aa032090701 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 330511933 1250 330510683 330510701
    0x11040c110f010b030f160306021804090308070212070209041101110d0f1e05030a1a13051909020108010306150f1e050103020a2118050303070f2d03 65
    0x12940200c01a5100700e00900d0690b0380b1901c2802030316a1194158000200e03445c01082c8900d6164101d89180e4680001350f10140001c040540341010b2070000d9502c0c2d22510307019078000d40314101c00346800200207017840f81083d00c0800720107043c080440582c44100403150300c164801044250105c0c0300380103954040070610984202c0c810300303044000f080d500143c0790119a401e510340001c45d804041107910072010108036540003d6052000a001d2003040c0c21240341240042c40343e07901d030030390030303020800c034121001175040455290000d22110714044032404035204422030b01040044032981c0001c2c02c41da41880080c1400d0303110341000c0b030036800c0e03000300740c0c000c2000900c0c43e501103a45d448841d064001041e001003001c8040700002646500070b00071658808203c1d9103016000170405148014408140c01818940795038440d0000c2c040a28103171003840700d01450045841e407402d840010050250081100100f101742e040078201c00040111100c0e81305400c00d42c070f1051209c43c031070480050840c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 330513183 1250 330511933 330511967
    0x30a0c050c060c0d0e0604230d0c0603021b010e030306010807110a0c0503010c1106010b1605070f05030f070e07030b1f0801090c020303041205030601050d06031a07020a11040c 77
    0x18443c002140000b900d4040e0f0601500e50b800c0161401c4200212400f6a01c914000c81d0002d001c00da094a404140350080c2c40802400c01a4264054958103034002240d001280403990000e0900300c0c403807811280003d100032a10003807010741c1c202c2007a2501c9000252400341844805004038103054021010112042000e000322091484c0c00d0030810300401192140c140203500c0c003e030a032181d900c034540c2c4c44c1040652000802d050b0f46041544a40790703001000c603005280150703986500090051044000038105e006031442150f0901d0300f05030401881c06e00002c820b61003a4802c000011040245650180d51400e0004a0344c80d06404a81c10706050341803c0101030415031380324000c942000005059070442c11003004034000c240d4043c2da40e03100036200a821183c8020a00c0c003064499001123501c80c2045c03401d1030500102c045c01d4810740d150f50300700321440d0100b000354144030b0500c0b110382940304180744018154005103807100d144078054590002d0203552210f8081341e9150191070f800e07481c58006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 330514433 1250 330513183 330513187
    0x90b0715050c0c0316030e040513110102010204090e0f070e100302040b060d0f1b17060d03180305010902011e05090f011b05010203100b0f121017030c061008030a0c050c06 75
    0x41c0c0c01c01084141c07001180426003161f80032103203051610900d48121032200103c4a40103043c3c0390b0344e03000072440c5071150440d0340800006c00c44a8036406540540701c030617002451683c01110440e030130301007181c011a054021590400100c1030852624138201c81d015074000451100c0900482c1d12032180081001205040c0110f201c0510f40c0307984103400c0c440b0807a2452818840844049805100038a061400e400001000c10f4107071074500d900c00c041c141702e414480d04506110010b44500241a8819641c1c0c1c0d65a208880c1036503040380002e1169060020314a0702046001800740c8a03005010b000c034040e00b0340050200e042d0b401070007100044c058404804412048518056010b540102c40c6404a03610400000840300c0411051311540090034420600700110031011501000c0014128084030107000300020744e00c5031500440ca01160800c0c05180d0329000050200d16160014041101110500008200c5201c2c040142c8606002d00d107000e180091650400710700c0c0c800f030048410760107900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 330515683 1250 330514433 330514447
    0x90f02160b040317070c29070c03031505010f030f140c040f05040b1809070308041205010b010906050d0e0c12150901050708040611160b0601090b0715050c0c03 70
    0x980868a116074404e680c0e21059010722901c0542c80c2e130302a5035603000b1800040d503000005420700d0000d105245d115880c614010394011b4240440c40c400e55000000c507042000d04001e042d414040d801842c195590344142e65490700c000248a10100404d41e001c15541e808060743c41045034001c0045841c90f442c0d500220304150001c1590780d4458851100601c001d0340002a03241031070302412484001c010400b08042616451400c01503400504880c414000d41e280440001c40500203000a8000c08070600051080c17841c105084030071480c600780c10300c0740e800010042d00798400b04444540c1070400d00401c11000400c5010b14128140c2c030700c15841803141802c008010400648d40e4a12081d205d0035064540742c4205050881e40281c0d181c0002038042d00000d1b010845035000103504020300400c991501c2c000303100210481c034000c401200c0a0902d4018041c640d070f8400311800c080c10190a04600d4412543e6038861800c50007007031036400d85c7e201c80005107940e5000e41a21a02142d41c0141d80d51140e0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 330516933 1250 330515683 330515693
    0x301061b030c1703060a05010908030a03020c0304081005040204050f040f080f04180207062324060304060c02010606050c03120c040b07030306030b0c0301120b06040e0304030b06100513090f0216 85
    0x311012030140e201b0320030010786c540c803402500c011201c842002e5441c200108504801952010b19a90a0b03807104010024410354204903240803c00c0c146000902070070248100010f689001d010150401300c4c61080c84080f07820503407141c4086a01c07600789684e8020740403d0101d11700030fa03804500e007004225001440b41203e6001052902c0c0f1440701004069141c588140304814008028650043e00788009941d2707256030540800c240140640509410007403d000908561046404513420741d191540158100d4090180314080c160340e00b0468208034001d1101c80e520702441208078184106a00403c58004070303c8119400303010782c1d048142c1d681d04241005401f0b001c6520003180c401802c68005001d00d0083c02c02c0d0b034103884541c19145011151500c540948200c05030040350301c00da803403403844480c2d10b00300000c100843c03068403540114a400c108004880c4d110709640014800104881c840d1590703440d244400f95a4a164000740248140038008024011030501e201400d400178034103001c5c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 330518183 1250 330516933 330516937
    0x219110d0f0b251407060c0c0203070603230a0b0603011e05041506050a09090501090c030608010212180709110c1b0306060402071505070e03120301061b030c17 70
    0xd020701400d0710300e03454031903a10300141c061215480a90394000032043c0400e20484030440701c0c0e90404082403c10844d604d6000c05c80e12000d015030082807003038121104505040c00188002c0c00a8201003140b003c100b00219a0360b01404c40d0410035200d0302c000642c00d49400c2c1d101d030344144800307481903450350313158a51100300303003500c805242e013581e11860006264074290040782498011007021080340c44c82d00106440d00e0700a2558481407001d002408034142c031107445840d0081007010750100f0310300034240001e42102e13125000a0b81d18bd0041200f0300100c000702c20410380006180c1c40d4603441c11714001525040002d1500905000e5040001c5111790580d480043d0441d443e4810076a4000c1d0480604290900c010065080d01030b000340001502c24a041c0c0d0141c0401400791140c0c60200c2103100803042101d208403400d80220301c1c014170900441c1000c110000c0307040c084151031413655041c40409030645100200707a10049035901010410184140b0035002c1c0030b6032101d54082500c0c00c2c80303042c051503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 330519433 1250 330518183 330518213
    0xb0f070c0905040510150603020703021906020d0f18080c030d0c0903030e030c0102151909050105010e011e050906041b08061207060504150c021507031205070219110d 73
    0x103106071410300c60300d17801902c100c0390601c0d010709203c038846261031015800b03900410381c00c3d800e5024120141480045005207500c0003803040c000180e444c00b244650600301ea00e03000891105030328205090103010f20b80c88100d00d10a402600e0183c440328010003061540c82640161100a03050180d462506a0407204400942e0b1003501d0700803950030f1420034542c2c1e03840c0c00aa864010b030300514080c0c4600b8525070065801010620071401020510030f20361007500d0040c2021075181c1c2d91a001082001c9442d80424054030842c0b1640000384c100070004d42c1074800b640075040c0310340702500100f82d00c0d5496501221031000940041042800c80e008080c25101d01221841d000e01905001025454400300d200000e5440f030f502c41c03500300b6080c000a20001c203ca049414280065000802c015aa400700292562100090010303958507051074003e100104007410440b141d420a0244106507402061402e282541d0900480c415061401c14282c010155400b55410401104100b13081c015203680c03800b03031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 330520683 1250 330519433 330519443
    0x103050c120c040c0207170f060a06030203030a030b040b0a08060a0501051002030a2f070f050307031101030f0b060c07090518060609042402180108100b0f070c090504 73
    0x41000c40c001400407110400030348032410b820194060350145010f42c0039100c14165403044407001c548820041182c6001c2c0003047e00e580c0d10403007070040b000034100001c981c4214402c030240400e51440e40131039664050310710001c0505481b11001801911250f00c07204003204002d000c02c4c0c0790b80d52480d1940c2c554105803811079185013071100104040c2450900c03200b20310000d074021450980b00d00c00444520042120319494401c440c101e484200010400503440d60001c000500300d254a00708070580140140d51105020f80c1100030208081070040243d03542449007030901181301c01180451400410b5007200d0350354000c40c085040403560300001a854103880714a901003010b511000403148010805291100c0c09070b006400249280c2041d861403500144240381c1c2d05a43d02c502c1040c03810000a6105c0384490329070102d140035a40c105881a014419000e08001c601030500c10407109510b01207000d0501c81c840000b50000e4805070304003c031146c49802c1641d00301c4464981507220050981aa010b0314 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 330521933 1250 330520683 330520693
    0x20702091006050d1a04020309010209120c03070603110c0a050105070f03050408030604090f0c0602060f0a091208061c052b020615130c020a0303110a0210090606031208010305 77
    0x1003000e621080c14140c0b00280c40711800c1100200c103450203810640d80300700215000ba060050903448038005107006299000000da01c0d102c80206102c0c030540d030110761120a074092940e0900c151008550002540e0b014a40820721040c10b0035024003a00c0780402100c0d5901c06c44400e1f00500106512032800707038200f90307161084c4e804100340c114181c8000f03a0740580608000c00119401e484e10b540400045841045400800c00c941c0d01d401d007070083d0030741c42000540c01150030016400d0180050707e41c0700d011102d00700032340903294136018036280f01c00c001d1000380311020b40426010740e580700c1d00c0360000e403503100712204d0401c0c18034005448554190303c2c01e1000300034a411900d18a442100284034800d00d80c01005550b9400c184c004d20540d14180ca240c0140c248001c403500364070103018003000003413940c00901200082e460000c0440d017140200e5000304409100044031300341d0208203504401c032407a4022234004030900b810401003645601c02428450400b000605032600846000e0480c3d0080c81954 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 330523183 1250 330521933 330521941
    0x13060807050a0219050111030f01050906040212060411040f17010c020d02100f0f050103030f14040f030803041401060e090111030709050402180310020c0705030a0506010312111002070209 82
    0x80c1e0203005400702c82003d43c10102240c00c1942502d062a04020301070800031a141d4002003c0d80120350094907026031110224005200f682400940703160420800c4d00c04616154100e003200303803030b04000384c0507a110b640c480c501d00f69032005141c03e44026151b80c103104a01940d2311490343e6950200b20981030599420503d4034499140007140955121340395401400c9002c01c6640c1e2540146003503d001c411060350b446902603001403601c54035019500c81d0f180d200c0080714400b409820300d07410110403002d41c0f204001c1840071200070300c240c2e0201d0707070712085141d01ca880d545481140c40701d85c03e55464041d031805500244c0110403000c40d90041420744000c00c88400c503134488015502c4100c1d8442c02083c0541020021810554000e00001c1040b95003144c400c18000002810b11111080304c0108a0300800c084401501c148894402850100e0040c00340c0415540c0e802d444440501c0060000400c0d0b040b02c65506000306540c044800521065621111804200d00c000750031040c0103900800d0054005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 330524433 1250 330523183 330523187
    0xa03020a0315120b19090c060e09040804150309120c120207080d08070e03010924050402030703060b01091505040609141f0c0605040605061005030c0304020112060b13060807 76
    0x9042510900303d0f50341d155580036120941c1014002c0e01d8100c0b8080302844c010a00f00c43c5110300e050b1144a09400303840107151400060800b4400601035210f0b10300d2209100001d613144040f50122080600509407415124006a000f40010140601340904003042c0010460340306518200c1c0e24840c50702e0b005015000d61089036148214003034049182d00a2020800c1d85000390006a400841c80c0b9003040310180e4180400d09652001c0001c5130700e0500f1800c18565044981400e8003590b0290404202c20324190b00081c0e5103160b03910001d4041955901c603174890380d205004400c05420150940580e650084070020103991203842030b180002d185c18801b15030300b40c440380300145200000340f13a02c1484c2d04a00d8401034000032400f0350f4040c070442c444c2103000280113009561041e401481c0c0042c81d0f1400320144032604241d042602c007000b40420400022903180030550742c00039028a8240138020466499030010409174104811428012411584815503840b0b42401d41c0c110790390303040e0940c07500181 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 330525683 1250 330524433 330524471
    0x132090312070c060c0c0305011a01020d170c07081204050c090a020c1f20090f0301060b030109050604090b250e030d0503090102160804080105092109010c05030a03020a03 75
    0x10003824507483e6801008020320031000941541e001c1c0d040054540e0743c941d55142150b0f1550307880f419070759040d8000500c568051003445c528040300d081c0030b20b07111803c8a04990300c3c040204401c03083e5102003211818485101309484207070b03041121030754150820b4101165590f01000a01e4411604074000405130f440ba402594110300107900201040d0316440030003e004c420707007200101e00a80c0d40540c101e2007078800400d0048103215140300e0350750311002c8062002011030340741164000d078101002001201d1028080f02e0450341c1e41100080e258407500b0000b0003604030002c010301070200410500103550400c01914055200640c050075003546001c40540c0c845403001d0340b0b0ba07450f070401d143d04280c050161000f590702a2140c00018034103201014104c90102c0140010744486401041c2445881001d106868200013075000510b42120b14254540007141000c0311400845004200006d1310b9006056511303045510105590b01d481d50180c00400035044001e0410009041c800072254100d00010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 330526933 1250 330525683 330525697
    0xa0f0b01031101141b16060906020c0301020301060f2a2409020604141314040b010b03160e1f030209040606110d05160803010306060608010816050132090312 69
    0x3e8130300b00700c8a00c045050303c400380c50217500c150040e500ca501d005940c072603200010385000c0d119045100d003404002494603a0403088070780240c0c4100f00500c04990400380b00c1b141001e0070700e05820300108140b0400010307080d000e244d03001c45072102241c0013000020800c4c0800c1c0084003100000301e0b11807030403001c169002a00003035001201040705006840e078841d003e4956000c050003044401c00e050f141002100e60000b40614204400d82c20b00c000c101074141454010000940c0075400c50911413054205486201210414070020a000582c580c403816a8410301c034018140c0c03503010060400005d0069803200703124501ca03038038014001c22140d016440b8280882d41c024001e04c203691940034103440517032100001010840d9080c0905002034403001c004c6010710b2103108003140d042e02d41030000d07000c070300c042e04803072820740200959080c2244041280c200b1141c0910b41140011072513080815000722a41c0350100805250003410342034983c20005005800c816000c503090010b2100301d0400c1802814 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 330528183 1250 330526933 330526967
    0xe0a03080f060d08070b040b0c0406090506031009022b0603030e040f0b060f071a010e04030c060e10020702120303190b03010b04050726060307170a0f0b01031101 71
    0x1101044400750610415603000c0c0010306a1080702d10381e5203800003a90880f6900b11500c078048001c200400c42624030340e40c0c100d0040194142840d040280223080130700d5034083c080c000c2c0400710000b04401c0180030700400620000008643e04c0d120058100500202c0f02c1e040808828810b005104140d020b1250408a80d01580e17040580800d2200b044007034211903501d1400140c403000014440c0e620314008000030300740a001103640303c007070345054001400b00e50f01040c84154120010018030b20700c5450282c0c0941d1503c2c01291310307001c07841e0400080c814401d40000c541b14a07101c8032080d0f400c603030042445074022203e820400d0510b1030050780e01d01c800c45001140000000c82130a05147c6a0413241403100000c0c00441d0603079504001ca8211403048410100007681c00c000309040c40c0d2014880c034100d0251b88580c00c401e18011001c280d5496141c85112a6400f0344031008041400038000c0c80c00c01035001c0c418604100c842d040980d1085030138001a40c2d4400c0000494580750f006614a8000c14000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 330529433 1250 330528183 330528197
    0x3020f030a090504020705100c091404060e060d020315090706030509011109010c050a020402030a06030b070c0320070e01030302030a0f0e03070605070213060905090120030402040e07030b0703050a0e0a03 89
    0x80f50034480039401220b01240d040c03045000c0c0c3c522003819400b03246915429075890750000c515042e540c02d0010703003005080303028915120061064007070154030780d0740c0060705440081240c461440400d1806444804007030305028503000340502c400c804100c1808840325590305105c50b84400d00018200c0c0c00c0800d034020201c00c1041101030f954020301314540324500890640e400b0441c030380c0206041e6402110344020099640750140b0070040d090324443d40102d040d18040900f502c1a69014200041403003113a884640300340155442c500d0208500405840b000c001603806581d2494003a50f25000403441d000030a103a5001030f2a400c0c400c0143c5032400b84000c0061140380d180c038109484640c44244103a0700034414880d070300c041d90141d000306002001400800140e03031600c00710450841c0c1724840c480e456a072031a0740c0e40100e0304112061741d402940484002038071040800001c1e00e84065030740300510344101d140c100306000e038160307001038440c12035081d06104903180522401e07102c0c014600b00401040780 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 330530683 1250 330529433 330529439
    0x7080702190f150914090c07060216140105130303020f1c0f050618010902070602041511010612150c091a25261605010b030c01171302030a0f05010903020f030a09 71
    0x103e0b06c0d200360410b5250442600e006403130b84440301645d0240c00c20001c10521054500100119071055034041106000204158108024413005c800341c001405000c02d90040703080221103204004652644040400000900c5015288080500703031718028040c0040c9850009103182c14988000b070701c0c2c0c8401141540d500d82c2003600c0b1b42c000b90814501543c810f9030070f00c800f044103040d92151071040f61080d12a08000c180d204059401e491458004c100040c4400014030300240480a13034410150107104081f85080440404454910041c1e102c0c41e28060010880d0130700c00001d40c004c14106841c8100100f119100c4800c0c9111240150b000800051210302c3c00e001041d4030001008400031900d00807842c101c201036070440c84603180c2d5001e03107144e5500d00b40c603100ca1030104030110510a081c00c0500114540003d1440d01020040c921004041180588421503405210101070b06e1791109551214604c181842c600a00c0350003002c030050f1080c00e94100c2d02c98800400d80313040185541d149010142 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 330531933 1250 330530683 330530689
    0x10b0c0a03030c0504230306150d0201120e1510060e06180f09010603020a090f05010f1b0f0b091902031e070b0415180501020307080702190f150914 65
    0x180800003001002801c0c000440d1b1090414100441520513088101d0100388a600305030500c400a040e28a0300c04068290140f035131940000d5208558090a002c3c003031143d00581e800c0907044458645580d8001c01200c2488260f9841c0c107075001e82c900c2c07174038021000e0704c4d0407040d12423502142c0c07001d61007041400303140e1046150402c140080c66014001045001099010074800002038200c40b010940100307408d41690f038000c4000c0003e2001640042c20b291801002034100001c80d2946410080081050801d0890150000b40155408035103103409440d00d045c000000e500c21b58070320080f4020100c000c031405c2800c864a00c007807900140504409202c071050542444115a001c46090048040000702c40c40389601034402021a00d5207a0511400564014000c0e105802200004003072410140140e0341d000096038000c0d82d0210b102c1766a140b5030300002d2034020040b100240c0c813000708907020070100340c039000ea18200d965005651880215030355050301e8004180c024110807011a1007422010f00d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 330533183 1250 330531933 330531941
    0x2060112020609031c0e041b03090311100204030b06030d0e0603090a0506040b01091112070e06190903060b010e090a0f15060207150f05030708180304060306050405010b0c0a0303 78
    0x252009000610b0030f03983c0e2000c01c4c00c2403030311700d42400070585001240c00f9032038015204043c3c0d0b4400715000c01c0320f044400d014245c800c1d0001000e000f00359481d03400d031080502504c05815001c01c994201c80c8640802040c060195106000071240c00d804640465841d05002800344054038040e1030f0403031960305500c01c1c03000f20b42004014001c2e62154003c0c440210300103105242c080c50003518252a150705040031074007540c03261104c690320782c041040b8503001c14000680442c1c01110500c0e042aa80040d400001c0719405000d40c0304210b00c541034080d030240780c1c0100c10f500c2241d104100074081c230070b049401500d40e600047c0d0041c0d00b201c411000200600f003554001c80303d4801c40c10000401d0f0648140d2201d00d100b56070420005a800001d003408050080308400c40c035040c4618204c5501e4040120040c0103010240140e001d101079807000c944841e00000510700004040d2040307a40f1503641c0e0200a0140040d4803d4130300883c45c103c008158890604101c5080906640040c603450300107940c00c078014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 330534433 1250 330533183 330533219
    0x4060c090b0313051006060521070503040f03140a03020c010b030309060d02030a110715140c0d0e0703140c01110a0203061308091314060109050a17010f02040602030c12030601020601 80
    0x64050002e1548641c6400d100c0d08014002c6948d420382c0744c5101d082c00d1090b0112004043c900c04282070704001802c1c0d03200040325406980421269180c580c140703000d42d101508007051035182507022500d140d50319403684c00741c0501d1090700024009d003d038920a060b200d100700002207800800c2040f640d020051150001c580107032200000045040c0e4243c01082e05822011003112204c120b45049910504980a9a1044641c91507050582d080c2400307140c41920030100c150a89a447d0050345043c0c0c9010720164008603004034441d500d0644d09102140c80e000f10311003090106800f4483c00e03000410026110900f9039001d0000c06d038644410030345904103200c030101240c0c0c3c640c003000720480c180c1310f8140744000a80d81c1d50300898116400c0d0840c69003414001c1c240760400103004010013440da0f030800d144045030110900d140c0d0501d48654801c2c003605104107002100380c00020001113150303000004010041d5a01d055520403886055030603018441074650b5030059000100600c40001184519015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 330535683 1250 330534433 330534443
    0x20a020304050904141203010e181c083405090a03120302190e0d1509060e1c022b090302100f080a0902031002090307030b010e04060c090b0313 63
    0x400e40c0d82d2000400304030b011101192080c800680f01c00034a00e00b08098104902010f21981c00c1d90706040c6403d0034404c006000f1880703a5600c2910030803401041c05490701a1307402004800c04640380301405003120a0503120f0302000340b11144e1801d209568101200000d41d5010441c03121000d4bd01000c960581095040303d903c02d0812030000001425543d020808101c0b0351800358079011216110458040d22941000500195048a100b1075450810800646500c48041200d1036400b26908004086a0a00408107403034038625078041940040c0c103100076070030b01e08142440322180c802203842e507149000d4050b90404100035807141d80000030810076100554500010000d03038a800007401582e00180c5040031917030414264607a03e51020700c055200d1810b8405202800c540d40c00f2941d01c2640c0c4440c066902c0c2c2c0814142c07003540d41440351100030364210340c118078035586407201444130340025a412111b440c0b400c42c070782641500400401044603112065542555210030707070841030301012142220 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 330536933 1250 330535683 330535687
    0x303070209090f0a200d120f0e18010e0c070209040b0702100f0c0201051b0a0c020d0f030503091504110123030a150503070b0427020a030e0d080702060a020a0203 71
    0x10703010350070411600c0c110f004600002040140080b550360500000d201e05026102c3c8142d20070100701e043c0710107000b0341c040e440d0039203001c0c85c4007101f19440284502c4d00c03035010f00072b0440d24001c0418021b031241602c0100111320055247c44c403400b0510300c640381c402900301c048400043d000c2102140d00942c0503030a170042c0c82e050081c0081c0002144c6620307a010325103a130f41e0550b40b40c22a5091207541da0100070b4003a0804240d2603144594030074020300b4000000c21071481142411510390030070840ca000d5100704400394000c0f492074060065002102d008001c0d100e2095480c119000c1440407501480e04421a900c02050b1307072004640060001280c12103041c1480c0c00301c185841e00e0002144506061a00050802d40701c6040404045c0290f00103031080d40140030034040c42d80203c0807642117610a907040d101002c04800d250348070304012001c0d52040b601c04039008074a41d4054101410f1403a141b4141c40c80c030100c41c901a036414500307492800050307000c0000114884200d9009202090450040383c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 330538183 1250 330536933 330536953
    0x4060f060c2402030408030717060a141302120106120203010b0a08060103090f0c0611010905030406110f0607023d0e010902191d070509040f0e19020307050a05030307020909 76
    0x20b010799005072400c46002d00c2c000700b0030042e41ea02c0261040702140c00c02d25980781c0d09150300041c44004183c01100c8000c0d650400046155940991150f281c0b500da00c3c00395180c4004007003d640158007403089601081c01503290040c0d00865200301c0c2d06981002c0c01050524800d8442150401e034000d1045040c19610f032200c10109100042444a0074450400045200e040c1000140b65012200160704c007a810b00306550002a000710546d419140c0034a021454280a0b20a081c501101004900c2c2c1c540104401e015040364040f405000700d40080000e805001c0c006068a007485280c80c428006284c2d840c0340e1240c442440e50000300b20703080048008030f50040c158001170403081c1840240c0d2a5086915410440c00010031000100042c1095017200070341341520f0041c20a00c50500d070188100d0361085d246840006644c0a50001c101520480f015408030320070005007071041490980c440d114030a400606444c1c600c0d40c0030142c0e100034010314145032882d401e010b44004040c0105d040750180507256 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 330539433 1250 330538183 330538253
    0xc11030a030510120501090507060215130203070e0a0e061e15010908030a080a0c02030403020901030f030309200114030712020d0f0c05031503010606050406111c02070504060f060c 79
    0x1180c0f019014400009588007e40703452860a90720340d00010a6400507070100354080e02c1550781c642c0c0500c20461085c1c200c1e100748002420300300c064012000b494080da09201030002c8507403084003440208003c0b0f40d0140c07520b101c1c9841400103c000464542402c0c00015100d00c19104c1c480305520040c1080350282d03032507681140c2582c206822210000301c0c0807040041a002c43d024460200d605400a103203040e0958010445140e01408090b000440300074403041054072a074080c1000c95000f44d8100e0038412803111140265082d07600d0030703001404201301540c0f0300400c0c0302104d004403507680b0b92603015005086408040c0d0081c0f03a007100c0c0c45a83d0070080a03407400c2d501440c40d0303540c1c4035551160780b45418030b00300740e102142007101c40c02030780b5204092000d140c100341290181c0300c0fa070030181101c0c5041c140052400445500e1010780e1107401c00000007a54000070440306445084805000c030a031079001d0f6418607145481802c0001d003484950002241d82c0560359601460b040c83d1038201d1540300084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 330540683 1250 330539433 330539459
    0x130f141204090b0a050a0b070212100c03060501020c010914040c051204030207180c0504060509030109060905061618170708070303080610020616030209031905010f0c11030a030510 79
    0x11042c2d1a26031072000d0306071500004c09000380a0032262000f403a81010700c3d0002c203000c2d00c1d20090007140c90310303086d600c4030504100540e84218050b8050040c800c0b804002006810140f16550140c414122a01882d6016500340c1d0300b62002020a404409110b900b00409000400c444605104042000c1d40d4074520325600740c3c1c0701c3c601030380007000074a00c0c01742c40340b400380b15483c10228000d00c1d08500d004069071200484045603224a07100341c9540b140c5000a005200c00c040081219181015400800c8404103555100e04407185201d640c3d1403690006a035000e0750340f580c103031891003000d005028880b601c403003c5550303a94500458264684900c041454203d150304254080b070035110811085103001c2071203070040686403000e004507040c0007120900683c0716000c00713024590007080d0072010740c90030000750218495a118480c04c0401034100385000b411100034044041c0d0402648101e41400341e202003511409410003940341c8000040700b140102000f5114090011010800040001007444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 330541933 1250 330540683 330540689
    0x40308030708011502120319090501060512010e1e0f150912090906010c171809100803030a0504061b050d0e01051e040809091608130f141204 62
    0x5829a2810104006460058160301c050360003404403070503070300590340403d1111410403005195030322610349030720800c2c10440c480d0012110501d0040c104007804015000300048903003c0c3c0d044080031208442150030f03600340d034204500903440640c3c0b149080c00f4110000b482c001025044e40e81c0e10700c0c90406d16003000c620420b0340303115110903000d102c8041d1051040e44100c01c10803100d14a490b0b030f00030101d105030034014600c505000c00b65213001c0602c1004081c0c2d241d0016510a069540d944456214500d1419400c149002d0021140011210a41c0745071070b4081e500c41c1001503082da6035002d01d03072000d018010801c9909685612101c00050741011450301403041680329a62602030343d0050380229000c0c811032000981c140400e00001a81c440500ba00401d401e014455195039213041441142c1704011805070402c000108201200042c1081c103800540c542c0d0b10020742c1d8980b0510351906142d1450068041050507641c000064822602e00aa600c81070003aa14000c440c107188507810b81041e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 330543183 1250 330541933 330541943
    0xa020402070b07181d0a091416090903021203070207030215030f100608070e04150906050907090302010807081312020d020c09010b09040c090b0c070906090209101d04020403 76
    0xc42403028a540000402c02c4c40c02c13040000c0e040d014070300070501c40e540d080f405070a11a00f0880c2c02044040c85503400586140b504001091180c140e50301c041540d0f900248030f11030015445e0724000c102d04d02580030b070030080c07a0181d008110080700c50360406940d03803020700213400754412001c0000c01a200c16154a600d142c250003003648034640445000d4017414000d0180c111201c002c0800d00c80303c1c0c0c2215809421240d5490901500013510021030000c000b00d080030000505004000a030360a103d030081015594107658001c096200e0000c00e503001c0409005c020b02182400001900e01403007610340c030764007030304000e2000b180c1922070f00c607140044402c54059006801040c03856034203c0c0c04200901171800305481c012203540c900039030740c14140034403c001d51180f0740710020181520b00c41c2e0b030380f00098014194601d989800340d21909030355640038854600890f040480000301c00b18540300f030b1050402c0280c84108001d40020b811109c00c0c00d2450151000041140721500300c1c0c0390b510103000518411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 330544433 1250 330543183 330543203
    0xc030b28031a1e060114030702010f0510060314010303020d08060f060a020f060123040e030903071401170118050603030c01020a1214010f030303020903070302040905010f0b040605030c010e030a02040207 89
    0x2441c500803c400c1c1459000c03449203d16030501c405070b6404039410a407211a4503806480b0348902900324003510059412400c01420082444402145c0c241c81a04031000d54808001c500807050074009005000d00c0041d015801c00300c581811103000300201984040006c6c546600c500314240010841e412480360040145d0020300b030391100c1d960401c2000e001d00440301208502c00c0c4030744540041c101710120f0441c0199150010500d0908003001640e046420003820303101140c1d210007001004101c480300c854001542006144508c1403541001c6040e035001c00c0d0550b0095410050030302c06000301408007501803104101944e1010400c0c4003800d109685a580c256117a0303005000c41040d0340000c240e0040c60103061004104884860740d0360011a90305050140c2c440508400003130801074240d10103504182000000320800c007065000f0303040c521a8900400091160a013400101c889600907a501684030300088107456010342d00140448900504461035810b6550204003030b0b800c01d860483c4d4241c0c00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 330545683 1250 330544433 330544441
    0x30507090902180a03060203040c0b1801050706060302090705030403020607030527070305060a0204232107050307120614010303122705030403151109010c140609100c030b28031a 78
    0x881c50410f00140010b22449040c10008100056030000d81ccd61340c58144600010a072040010b250081c800441d001426000c0901c1e00003006001a4800c540490050184d000003800340d80c00303031140318002d44584411002c1e8400140301026036070106090042c05104e03a420010000f01d08003c403920030800914007584807460080c405c2c10040340180c9442d51400920b4101010f6103550600c559610f005120401602ca0f070000b007281010415003085800d402810030100c8c030350b105c410621a000344646000c10241e4440003e040c0d001c00207000c0100011000ea64141104803603030410314443c0380724480f50502c01e0745d00f0b442804a800c40c000c119281d400220f03040040c403282195034281403107001030501441c00c0001091045110303000711181030041c80160001032140000d1030001904011048a080d414003c4a555440d15042d54a40046041c075640d140041d01c41d0103001215000501500d1013402101204649610808001960701d030780b0303a20010205008a0352500307800e40c3c0035031610b95818 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 330546933 1250 330545683 330545693
    0x30603031315140f160213090305340b1009090c080601050d0b01090c09030f0b040501060f0b040b0f090315010e070302030c27030a21030507090902180a0306020304 72
    0xd10a400202c4402c090040d00300b5040010111841d950389294200c010174450310001d0305921101c03905400140c50701684c00c08164000004103114020404880d8034000044420840c8011002d01c1c0c82a41140c0c00406000a46071a0300b142c001004014040c0d41a84030b0360000121644c800060b1001c0640e00802c2110000500c099809000c0a9840101a4565494008408c501841108401350f5200c682c101d003a071091002038080c643c04024441164840d0a03c10b4500e04282c4096a240d441c04a0000e8070100c682c103540211280741c007005051501d42000e1070343c10381202e20b045c1c0755a60208004030b40c0750740502c41214080d03482d59280c7d034554100381e178181080c03d00a0001d02454410018031026101d4902900c500f501e814104006a03000030107100305094444500300e8141c0305031203083e420040c40e0716408099104006c030102100c50000d0088040c0c6006480b10004161301c03101c00e000c0305a443d0010102c404c0e203248a0001c0c00410400304402c80c1c0305a04c140c44441d0701005004c2045 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 330548183 1250 330546933 330546947
    0x10f03061521020a050a1412040b09010501090e1005100e070804030e030604031d04140a0608010506030c010930030f020c0307050f060d060302120109050d0503011505030603031315 79
    0x50b5540d201141071403041c0e080684940300c0c2c030101074140400001e0707951501c04a142200c1303000c010760402030300c0c2e8280b503d0800301d6010156001d45a40d400d003000869081068407440da400f0496500804154507280c0e5404003c1201400002c0c560400e110085400040b034030340035000d540280c0c1e802529203040c0c10300802591003100002d10a420540521012135030000d815a074488100c0d0a212107410f40d1000a8001c044d2900200707109075240040102818544d031001c1c0c00c58950500a0160340d954100700b640320602005864041500d0341811300640300c2d404000e508210f00e40312442c0307584145030605604d0511480e421000a880001c0710707001554140820f0018050580007041414103201c0058009545120028041c007c01718407440e080034190800c0c0700a50f00134102c40c100440510340035019017205c12054466101c4d9038504d0306103038410340440e03040340c2d07140c0600da25901741c1c40401c4840340d0029103840d60520043c012401060a800203650051425640c001118403905002070000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 330549433 1250 330548183 330548237
    0x6050706060815040210020d09030b070e030f011b02032118011104030c06050c1e01020708041503050117030a0309030c02120a0507170c100908060f0a06050a0311010f030615 76
    0x190030003008c14604a40003d802400daa921001004940d901c01d10b0444040c0d9002c00c607580c0c1482001082000d085040d41306061003078055039002032500e90243c0c10784c0c4d00c0c03107100c140701c8201200311404030000851000320341d0000b162004850f0040001e02d8205d09440c28891611511700001404204110840640000514903818002d06000007000c0150311041c0f506c2c40f09880c8580d020071188801030a44c1154a096030140c000c1d80c4580d1540042c0c95050b1005032400d000c00e1901e000850000744c1c0c44040e00403a10b0b2840110325004988000310f01400c0000003c070309203c004040900169502507815007003040282c0280980c04080c1401032910341c01d6804250101b012101d0000c11003c041011b5001500644686201e1001064110b40b00701441c1c0c0414540e0244805100500051a017414080d14075484140035840d111000c00c900842d03103200040c4440300d0903020083c01c1d405000513041850841c00c001600d01d585240d402440312030240f1400004600000b0066402d1440e09400302c0c2c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 330550683 1250 330549433 330549437
    0x90204090f09050c040506010e130504151806090807200a091109010327030906090501020c0f100c08040f030516030c0620070b040603180201050406050706060815040210 74
    0x1200b000c1d6100c0b99222501c011400b4002d039114400034074103074010a480403030510090b0041680054071418030004000a50b01190303d10100100702d460005180101c0041700c11500d2404004800c2c0c2d0303140d80040071055000c403815101880141e010a00100c0440032000110b601424020724050400c912030a40c1d41290320000d1801e2080151601600190381050350203085c00101f040207500d20b10940e0341c920310311444000240c0310326801c05a100c0d031800c00303c8001783c40d04000c1580303400c010f9071241461007030240c200107440e03040807441c90160f0301814064014102800700409603126419264050f402c804c841e0241c02c1d400f0010044200b042501d14150150700600550842e65003055003100c0d8400c507000c010380400c007200e10139804055420408594822941c12503076844503205103030020311408001c6403401900e00c80b07507440f64400600e6240e05a68580c41c084c203100d010783c1d050700140340c2a80c0060796180081146001048203035045102c01d685c1403071034a820710410001c00419940842 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 330551933 1250 330550683 330550691
    0x1e040c1409100b0f07050318010809060f07051b070e1b1e0307020f0a0308011703031009021b010212040c05061602010e010c050a0b040c14130906020f04090204090f 72
    0x807220003020300b507040d20481043c0d00d41e1030704490080c030f42e00d01407850081c1090000040024092003c0900c5d8101e030542a2216500f6540380c0080740e490302000c60f40d0a00c00c54911000a104034494001072241c080d220303030f4211034039a00a9000c0c2c40e2641c0d5400160001050000f44100000c0348003102c040080b210b0501c2d4030740b040c8144001d00c0e090032117008030003403680800071901c030500078402c07410101140c80441c0d000000d14100240415800c0c41041000d00b0b001001081d50040481182e00c0340d07000b481c00c222100e1624004c81f0095000b2000800b001e088031400840c0c101382030000301402c850607004050603080900300207220781d8480c0e20961061508001c034410000c00b0b000048445502400d281d2440c13034000c40180d51803040d642000344507008213400c3c0410000d000c0b21841c0141e014a032604003894468180fa404450644980c03a803010300d14084011015492300081c0c0c42600c2618094101041c41005031215046038203d0f1060780d17004202800005850b00c01c01c08219003a4400f40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 330553183 1250 330551933 330551941
    0x31a07021e0c061305091f060c0816030e060d050a0b030115060c0309030b16080603010203090a020d06230a0b1008040807020d08030c210411091e040c1409 68
    0x10703a4810441201e075010380e1012540484651130ba218040062201800308002e62524500b604001c1000011407440e0310388251002c103499102c2e00203c2589039110040c14600340950044241159003850308404000016542d90f940e03407551006400e40e884000004039003800c1c4007006006a59456010074040c2c0e1401102401c03112660b60340000b02c039014140340b440342001e030404641d0403508e5007000c0c0a10052768240b19400a1014000d61844c0c5955601e00b19502d40074105070a030300c000c2d500c1e03100c1544400d0588001d450a140f4a050040c0701d00c40009007882184600c10510802000c42d00d41003c1c0702041000304000d5000d0502c03e41e50464032030f03411320034010000e401c616025102400300341001c515030741103448041c41c00508940000281d5240e240a040c5a0134503403000704218442c1098010340b80c811950a15410300a503440080502c291034060300740010700d40014251105855440300100051400e0700c65070303000da405644849038041c20000298841d1078400c4445001e081410100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 330554433 1250 330553183 330553243
    0x901051f1b020a0b0307080a0e070b09130903031d0a0804060302071112030d0f0603080301030611070b0f04120f08061909050c0c011512020d030306031a0702 69
    0x241010180c185422244056200d006030000704440c000d40200468401094241030a000f035480303904195144141513407601c954005907a042c850f81d100650040400b031291014000c040c1980d0040a020591001c200c4030000c0195041c1050035008260344030150780340402c41004050303c02c80050000c01c005100c5680c0c40900780316a10401007059404a40c040400c942207148070281072000f08100ca0300102601042c0d180d900007120851024503205003030758a0310481c00b482049940003680c060950707103142c031044003601c8800181c0140790401c01201c0001102c00c21114010485a0003181d002e180600e0400c0ba0f4401c100054400d000c030b003c2000d65442c5d8440446540141c0070341d40b41408142100c449403802001342c0288070382c02d0030641041004201c1d80c000e401a4850000203000e0300e0600e1100541455141c014204048914115070000d07040c0000c1400d4094868030300090415074030744400c0d1044c041110381003502100c403000d002c54035a04204040d0309031080f00c20224000040781c06 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 330555683 1250 330554433 330554479
    0x30607020a0209061f030606020c0a0f0e07031503030e0423070f140c0f010b0603090d0305090709020313050601050a050604030204050406021308070f06080403120e011e0b090105 78
    0x9100d00d000f0000925103071608001c0000000c0f074031040440d01c1c04101c4026020f8a01802160010f10514100940500c0d100402404480300e81c0c40170400d01d801d14010180000004060303a00340b54032201c031091030003885240c0f580218003946e1605100d041c01d4040000381d80c281d940c80113440560003000e03d0b0b00f0540c000710507000a12400c02c1e00d2420402031080e6105011131040c060b00041c0410703100003803a8003080029211410500800000200504000c8a80401d40c0c0300f04140d4440004041c90354040da101c2034214030202d003121242071b9203980700c0003170344c4c41210074129000c07103001104100081000007a0161a04803106c803142030928001c103216014a21000c1d100e90b48170004641130041550468920754a0190720440640c0c4030364109680d142a44109204c0c00b02c1c0007400a03810b845800340d58040c5605680c0c103c4440d1f01100042c0c0a01308544481c6240e561b1680740145c0003108440240b0a182d01c00e10120b0058140020088104c505a010138002d8080d01203860b05d154075010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 330556933 1250 330555683 330555703
    0x160815011e12150606181a0906160206032403010e0c060a030605030706020c10090b1b0c0a0e0105030c03010203010e040f030c080f0403060c0f021e031309060e0603060702 75
    0x4410480c50b03a05081200d840c2c0c401000b80b0345460a0030100d6110f03440728a10016585040e24031210700d54910b02200d500c600d00075509840c05060100b00c2c001c1c80e102c4010550418a400354850800c02600042c0c091783c010fa5a0307042c81545403048000103062641500c2c61940110000c01c0b03803014400d0340c9900c52006c51002c600c128400103500704014025070009014080250271159500c0c4c40c0e10700603603100307842d0302658803a1000808a503012441580c01405540d0040c901a0038034000708510340344c0300d480b124841141d0203000d800d0303442522140910f00007490350500d00c00da503514000c1032501304002d944809020340d0041005000c40a0007000c0b583d0000c0e4032010280d00e042c26810121800d0042c0700b40244800d0001900f01c01d681e49580c040c00c241c034000c00c0100280041d0343ca0588020604030302400158004052540b0a0100c00100c42620314000c1c05a0f864104810230b2206c1020554200c98000c0b95a18814040c091a101102d81e2140c401d030001c0c8001d09261a0281d50b80d01504 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 330558183 1250 330556933 330556949
    0xb150c0d050912070806090c031903080601140d05190212011a04030b0408071b1413021603051e07020a03060b041409030c06060907120e160815011e 65
    0x880307148540f1100351240a01560506880c1555218800780b81c5600041d50154080d02c13501e5401c001e1803902080c42840e8081d0304480d4042c10f0215a030980e0358100040c030584c14040c18041e8440e041c81c9082c020600b0007007a2000040c0ca241c0074501010300d051640000d68007900c11b101341401142c61520407410364907140c1c000d030180c11200105280710310564000424140510060100300b20314040940001c034858a210056106031100515800001e03204800d90724030b0002100b005818030000e902e0200c13000c040c0140c1303044030305003010910700404801100000c0300043e00103070b115042c040198800c4050520307680b41a81540015094201d94000581590b40c4c41c030b0341a00540d11644a04a594050380d000100c2d0f00c1c00082c480e44035041100886224003c20001980c80e151104626210340d48a0b1204c418807a140e031280c0d07001748400e01345500c01e403103044101001090460390440080282e4070080c003a59248401614482c08181c3c404505240c1400b16030740700c060702c0e500c000180d5442c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 330559433 1250 330558183 330558187
    0x5011d2805010e161403030306010509010c0f060509160b0408060103080a0324090509070602030313020a0b071b060f0215090a0614090c15070620030a0b150c0d05 71
    0x1418407a0041c5040030b105000c500c100f0300d0840307003a84010900c0040300c6002e00c0782040e6100020505460b84411a413440c00210300308610300003580034050030b001c51806052403040d1142d1070707941d143c00c40b007080d17580440982c40607082d02d036102c462020300c07805007010001c034600301442c1c0504a503442c6c0c018000204002d0000c1410301303403140702c1e0344100c20609040d05e400c00440c0d10074140490052707480c09000e04c071500740800224080c1000450104444c8264000e6103550340d44035084148084054049900c990240000280d40c420a805000594040c01c0700c13100c11101c4840c100c00580031984407505101c0c100503038101c41600800c6403000c010100030005441d6444a050780d0030304ca0798040081000345418002c10408030f814031032601c101c0b044021261011890000c0140b01015014141a011410844007000403c035400241172001d480116140140704080c03262841c0d0005c03610a44002c0d0760b11400180c40c40d0900301d12000780e5050481501c0c0003d05c480b030a4640ca1600c10480c01c0c0400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 330560683 1250 330559433 330559513
    0x90334120203070c090203040213051009021305041b080f0c0a0c06060b0703031a0d11240307030b180603100c09051002060402040b09090d0c0206090d05011d 69
    0x3442100c0003c3e51200940e031280d900c51941c0c4000350000d84041c1d014443c060064041c0300d5036840360601400410424102a40c80c0c20001e0000c0d40c4419421040c020038100700003040c1c1c0301d85c0900707050405048000d1202c1202114002e060050081402403109504414450102e22020480d960b0450170300e400c00c2d980d4118103103140031700b100341e0000c1076400c00080c502c01855495030003403120007403000c40d40024810f4a0104401000342d0200035103a0310700e000c8090f076180b5044a090303103042141c01c0905038640c0462849620ba400840314900469159072103a503013807800c1c103110005400b44031581c50031814030501103541e4880ea0780702480001e0f5908103401c01c5e01c1c010383d0640000d2400401200440132001c1c0700a40342c80080e1802c81c00340f81072849240707092401294451050080b003004100d220200101203d5414040c4002d0b0f80081c0104a07860158990310b0f4128a4075014800108000e03c0c0c080c01c540080c1120750440710f0f03507040b040e1044035000320303c5903410303400740303c8009440700400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 330561933 1250 330560683 330560687
    0x60d03022424061206010e0a0602100606091503021c110c0c03012304020409050d0f030509070311010c290f0a050903041202030c0a151d01020705011b0b09033412 71
    0x400541f03281d034800118940001d00c0b560010381d10688030882101800790540d140f00070b441c0d81c4002d0150b071b2036038416988514203441c802e40c00340c25800002000c0b00480442a6400c0045a08942c2c0d445044180002c0e80060080704000d03254500c04150000c001603030304084407011103001c0d00e0f001c0c031100c0580d801007025076603690002c042c1a500113056610040c5241400380c0302c250388030750210100b03040c280050905500803030548110303078000400700440800000110350390b4030320020403aa40021401d00101b01d40c000142a840207101c1d160100c2c0e0b13400c10503040c14640c030f001001c4002c500c0c00c000070004040004000c3d54100d40100c5d44070701912502d8400a410034600c164603a82204401800048110540d140e00c07522071003944860418040746440514030100c42c0003030b0740c00b6a11180b4108a00e51080310b1401c3e00040c2c503020380c0f8403003010f550381154005065800c5a015800481c0b406017490038079024840d0806002a1034014040c2c1c0000d8414901c3d0052000d0321707880a14054a036054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 330563183 1250 330561933 330561947
    0x20105030a29010e150301060f020319020703110603041515050301020f0414120d120603152903100507201b04090b060d0302242406120601 61
    0x4485000d0103a0b1041c20301d801d40c601d415001d4a00186a030380e6070580070b0801c41200b4030004590f2a20500c1d507801c5c0710065504104603607925045100802c90b03480d601c402c20400c0d003c021410750140031038900e1030404101908c0d04410175031007554200184800505c2d01e101c8500c0015480720049090201d035820288003100641c03220f900755000040c840c07610310382c20b0002c02c25503180c10458002c060108050000381c00c001c258441c81c56005043e407880d1540130f406408010380784944003181d50f07034603699010b41c280030381d401e034402254843c810601c00140740401e90400f4094890061030b1400e08000007560b0301c141c040e14220040ea64808210840e1003001082c0b041c800507101303088000d070099602541c0700c1080c20302804504007e0801903a51500b40180140c0c140c100030150303081d4443d2820840100c021040803000d40c4290740b2424490444502040c0000e214510010000c0c0707041300c1c0342448518003046600c0c080e0a940300942142c2c0c0d4050a0700c00b403001c48403e950076580c5c1c1a0041c0e481c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 330564433 1250 330563183 330563201
    0x40503060403210c110d080105010c030305060f36090304030f020604032a090213210b010602100e0a0308010b0d0209090103080304060c1805150403120c0c0b09030a020105030a 77
    0x40d0800004600c03240e00b005c07520310114895800c5840700101c100003116010003e0207850b0000340e07424044000b00b4420b4010030f070404002070103060500c540704d00140d803014440c1d6200014140d020301c503036140a019039025281040402c00c1d4042c80c0303040b070740e4242c0303e10441c04000c0a0040e188040b0003552100801d440c0074613401724040c52050f94806040c4009149058a4070401030301c2000840d105045009844040d140c03130160580e041e0501090118840400340400602000c84007504003180e8102c01040c020001900607011001c040d440480c00c0c0c0344101c501c0d1013568004d4900d100029840a0000c1c1181d010320456502d0306802c0705454080d20030407141581c004441800030090180c81402540501d108000801601845c500c09840d443c0110003480ca40d10017251b010040d9052504c1031180104240072203602e41034480c0d03a0807160106030707842d10300040d80c040489020804800b01000c0548442c1c0900c0703003007002881c0000c1d0b5800c5000780080c100100400802c0c16548540c01c0a40c103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 330565683 1250 330564433 330564497
    0xc0705062b0213151e0320120103060e030c0a0b07120b0a0e06060f071406090307050709090807020409030e090a09030507020405130b01080c04050705040503060403 72
    0x900d03020a4400c89426070500d070a684551121803810424004600c02ca8401c070410151a4407458542030f070415507000680050418080040c14a4443d9151140e0703019521100c2c0d01c000031549602240310500c00806a81b40da00d20008205550581004812007130440703911490108001042209441c15030055140c0082a445030b00e1603001080340d41040300b41329450980c0c5031030190f0b803401490410750300d4040c0910341050f8068814401c3d0007a41c150b8681c00800030b04210301c1c0032000174242100742d10030181503c07000642d824001d22014240180c0b90080801d07801942401c0c990740310188c60314024070802c0030032131b6a10101c20801c18414140e81a05400410810001c940e5090190061841d5000d4602c074270390403c00500d607050103108280c0d0762501580d40c1030034444994203100c008c1ca0058a24040410790200c284000360714003605a0290179140b001d0440910010300f80300940314090032010510a0a00c028401610006002a8001d4040c0303000a151101038060400c0e415050806103d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 330566933 1250 330565683 330565687
    0x9020609040c17011503140c070f290a06141e010e040203010e19060b160212060403020d180317130e0a0213080102090114030a0b090403080a0c0e060a050c070506 71
    0x2510802c81c4050540d0040507881c180700c4104426240f00010400311061035204230140010004030340b40440c55524184510840803101d0040f100010b100c0d0844d6042140e0100350504000074100c4074000d0b40300400090a503494040d610b400081c80c91203d0458240c1c240c1001a940010780c0c1c881d03511100b6004015004540e0f82d611841810b140031000c4a03031018110080046c0303507658040c1d00c1100b0450714900c15040c1800c09207051907135455090700c405da0744082a00c0360349015400030310140740211310a030020b1192600840c0c0c09081c0070101040b80014464031802000801c03018540c002068030040e000c07568400302e00e841c400000400c0d800400280589504000b07201e5030310b60041143d80000c48141d40131300e039111845800c0c7d10440b00d140e8006034945500148a891354030181d900880801004180c107080e010104240c1d1508503400ea00182d000b00900c440f42d5400e101d00c4001c03e00030301c2e04080c00d0140c000843da07548902016035081143c000769100e22000d05000500c040c01d0001c240b15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 330568183 1250 330566933 330566939
    0x180c030c1e0f0307110703120f02160914100f0501051b010e010e0c0a0803040902071e08030f0c0705060c030709090e0604020301060b0408060408090a151e0309020609040c1701 77
    0xa00c05400071180301c00864204602c2007481700300000da000449500841c03020b41203242d0041240e1407020250240c0c20362203139481c60410006201e40000103130000040000b01d48114060a403245e40014041c403403c0e0010315001c0c403910400940c910152102030078299501e201110350005104c9103a42c0066047d4a084011000740780190840c201040c0341804481d0301100c44420022200c10701e00c074030512a1702c10402040051001c0c2c000c0c2c40d049000e0500380707040001180c08074100c50a400c40440380d0a000104000d104005a0301e482e41148651103c5d900301080782e03a41a030307101c80241c140d40e9080c002000107501c0b148a100140043e0528510600443d00c1050b0001c1da6002c0c1518100d11079420410702003500c0c0032410550382191307039100051205072035540f140202ca03408942e005401c242e4a80300494602094003400320350200c0342c0d4500c180b039141e010070003040c40402c002c3c080400d420019541b015030340720816a4000700044900080740442e042d41500c14102150040340c148070148000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 330569433 1250 330568183 330568207
    0x1906140405210d171305030708040617070e0102190c180204090506010206060d110114180f1c150912020604060e01330e090705180c030c1e 61
    0x102c4803500124044074000c03089501c0a4552070454203543c41c00141a9000440500140c403201c81120300a605032807400070152034410a42d8042c0e00064040b0b104d449418410070220011690301c5081c2d49420b519890403100003d4407080007110502921500c03213010b009105100c019807009040d5205c03034090391840444c481010b5040740c42a42091490000003800c694004240184a8a801090b541d80c3ca001c0f96181c5a410b4100c6d0340c4d450400c10405640180301c9a17040040401c25401000e814a103d140c070108161111018501c1d802200300b4101120002044d003074030401036a0101004095020080f00040100000400642207110a0303256440030f079004550b10307000703074020081400851000c2e045503080c1e410703811240e1058502c0152460000442e1741512445404040020082903070b1000003441220003038401c0019071b0040c1c4010409854200c2e06241e140c040305070b079440729280c4040c0315480b9020061686040340c0c40040d42040c50041c0c00d070030503181c0d88000c8000340c07525805020703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 330570683 1250 330569433 330569479
    0xc060f07090e06041d071a030f061002010f0c0c110a08030d0b0310091b0f0807140303090a0b0a11060606090d0c0b0304030504090c080402030c04020d06030203060112111906140405 79
    0x5e103503213440098242104147e0300200301ca209203504010700b0003603110f1500748170418840000307043c01c5540e80c031400489050301d03009510105000d40e440305443c9116003856013001010f50060b5214000420080022040102c00c1d101112070f4404005202d0395050042410f00010052203c44103284c403040904002071551070f000f21201054400074815102c01c001c126100700b034000c00041c1d070b000711003c01c00140003000d501d46226015050f1f90400e811840851403c14071a00802848600420400d01541d03120700120612b003141001007110303017014804034a16220300b4401d030303008544640148090100a4030307104014071001d0003c2d996440c260a005080d500180603030492141001400e6500500c42c061060140d60010064510304241008000080d40000c80341d0400300d80754103001015075003d0102c14000d048148500c1a0045946025825610340c182c105100721540039001c3c1041201011100645600f818a422040305911070126030307018070b82c00141c0c400c44481d90040d0319821041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 330571933 1250 330570683 330570689
    0x1b06050a05070c03090519030206120405060a150513020708040f0f050a0501020d08150d0602131a030f100b0a03020c010c09060c2301050c0c060f07090e06041d07 71
    0x10200941d03160080100c03140383e00034501400140c0221000c0c010b0b46040301d0105034110000c1e0b02503420a40e20b90114070243c1103500c480c1c10070032040c000c0000788a003d00100d50b02503800b000811600f071581d5441c4291000a004260040702c1d9480a00f0768181194112034129403c66125a00c03695a00120f60309000140201401100d16190006071400d10607955016544160090150615010700480d1558030050054814113503500c00c0808d1901d032950424021801844096074403105032100302c00b104026801241d1100034844410044840141036030340200540c1c1e01009952903050311823501105607000000a2030001400c991419010303801400c50503915002406100241041541c4810452185a0204912040400006034440c3c464030011240c90304600c1070070035405025085910840d43c2100e031200c0000c05000b17103901081000c1d0b0001200d8541091803a2402c801000c50017603204084107515003102140c0e05564a8002900520308201e4080840051a031031550f2001244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 330573183 1250 330571933 330571951
    0x203150115030222081b012c0d02101d030f0a03080c070203010513021216060f051909050307080307020310050711060702030d0e06010b070f02060403060e030403020f010305090604030e011b0605 85
    0x2400c10b040ca03500891890b480c450a604440c5103860507103038642503232540901040d501c00300382c0d41c003540141e982e920b0709a00c50081c2d542c2c0d171045100c04e011200c43d1000b0b003015144254050041d040e10903034000b8140000d40d5051a01c0840ca0303c900b0b464029600814800a40c10b50038402044104403003149000c5619008a400700e241542c4400865180c0c2d05400c10005c20a00324001408170f01d0190010071111840c2d4035001d86405856103807254440300700041e141c00106008010070091600304049000b80a115000c2c6245c0142940007030740d60810311000c1d089843d01e038800119528001d5003941d030300020401c02c1c1e0780c0b60300e02070034029103c1c0d12424540b02c40a1500002c0d9410900c0015064107aa1000461b5850202c454130360102c0018000c0080381e01c604104400b00024005018180341e074003103030b4000d6807960708500c100a0101c1030452900e04051500003001082a0001a0a5001a00341c2400b100010202e00100e5804441d803041d01178850442c42d10381c0820400340d0020f44600103003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 330574433 1250 330573183 330573223
    0x30809011b021e0105040e010e0105011404060e0d14030c0604060c1103030402061317010912050a0804061509140f010503070506030106030b0d060c030504020315011503022208 77
    0x100030348060040d00d044043d400018440028544212282c040c20a0072014103105003800e40c2d841d40d0b90f1042d00d00b40c00c184050100240100100d5070440764542500a624903218140b40c10060010036084c0084903451045092401003000c1c0001c0f007440201c18402c84040d26a10409038220a0b920041038408480310f9107001d40c41c120182c451586600d55924803c00386242d0785a90b001c0044a8010291030110b8503410400051000c5250341c4024031043e0700b500225150005041c02d000200e20303840440c4c2030000030040040c0d4558040d03291a0310940c040c100245a8824611018000c49140c002c000d410b80341c017500b001481840c9206500c5076a810150242507a00d500c249a01e4036542d1180513000202400148503c44c002c2e000b1040050740079040c21016801c0e9111182070714030001c0c01c40c000c02e80d0361003404190b040c24420403408110084034466554034002c0e0600c08040b80016110405501080c1c0d110311241e80e9102151000c400c2e080450700c540c41d412003686403017011007011912100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 330575539 1106 330574433 330574457
    0xe03060c04032003012f03070e0415050616051605010c02011b0f0311061005010e04330e0f06031e0c030d030f1d0601050f13050103080901 61
    0x9065024412240c03a502104c50710701a1b08400040808200304200390315412092544030704c00282c5000421160000e021f046c000d01039040b241e400307080000c41c0c1c0010046100d0408030716025400359546620803401c9600120403d104950114035641095009507014000c505000c05038280c029407601d00c0f6035500c005040c40110210046100030b10b40c58030004081040950001c030203441c9400e0141400006032408801595851103076440343d00d10f81e4881204c41d030145200305078154a2581d4200350aa2024488a80c0a040e000c0b00c1c13900001007001c800e900500303003d010090050404d0b81b0000380f00b109001d6092008481038031600e44481c1168404200d20707405d125190341c0c00201c000c0d62030b0305903050313038480521409450000800c101c0080301c0420090f04541088a000400205140204080300c01041408840601d004000018401620000c01148400740d880b0940c0640d = true := by decide +kernel

theorem cover : BRFrame.Cov 330395683 330575539 := by
  have h0 := BRFrame.cov_init 330395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 330395683 ≤ n) (h2 : n < 330575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
